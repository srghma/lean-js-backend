module

public import LakeJs.Subst
public import LakeJs.ExternEval1
public import LakeJs.ExternEval2
public import LakeJs.ExternEvalMisc

@[expose] public section

/-!
# The evaluator: what a `Term` *means*

This module is the operational semantics of `LakeJs.Expr`, and nothing else.  There is no
optimiser here: a `Term` is the language the front end produces, and what this file says
is how one **runs**.

The semantics is a call-by-value small step relation, `Step` on terms and `StepT` on the
tails of a block, whose central rule is **β**:

```
Step (.ap (.lam b) a) (b.subst0 a)      -- when `a` is a value
```

with the other rules doing the same thing for the other binders and eliminators:

| term                                        | steps to                                 |
| :------------------------------------------ | :--------------------------------------- |
| `(fun x => b) v`                             | `b[x := v]`                               |
| `let x = v; b`                               | `b[x := v]`                               |
| `if true then t else e`                      | `t`                                       |
| `force (delay e)`                            | `e`                                       |
| `(ctor 0 args).j`                            | `args[j]`                                 |
| `tag (ctor i args)`                          | `i`                                       |
| `case (ctor i args) of …`                    | the branch for `i`                        |
| `block (ret t)`                              | `t`                                       |
| `label l(ps) = body; rest` (shared tail)     | `rest` with every jump to `l` replaced    |
| `label l(ps) = body; rest` (loop)            | the same, a jump re-entering the loop     |

## One rule for both kinds of label

A label is bound by `Tail.label`, and it reduces by **substituting the label away**
(`Tail.lsubst0`): every jump to it in the rest of the block becomes the block it names,
with the arguments of the jump bound in front of it.  The two kinds of label differ only
in *what* is substituted.

* A **shared tail** (`self = false`) is replaced by its body, which cannot jump to it.
* A **loop** (`self = true`) is replaced by `Tail.loopEntry body`: the loop again, entered
  with the arguments of the jump.  So a loop needs no unrolling rule of its own —
  re-entering it *is* jumping to it — and a loop that never answers shows up as an
  infinite reduction sequence, which is the honest statement: a self-label is the one
  construct of this language that can fail to terminate, and no termination theorem is
  claimed for it.

## Where the relation lives

`Step` relates terms, and a term holds no labels at all, so nothing has to be said about
free jumps.  `StepT` relates the tails of a block in the **empty** label context: a tail
that jumps out of the block being run is a part of a program, not a program, and in the
empty label context `Tail.jmp` has no target to name.

## Call by value, and the price of a control transfer

Every rule that substitutes asks first that what it substitutes is an answer: `Step.beta`
asks `Value a` and `StepT.letV` asks `Value e`.  A jump does not substitute its arguments
at all: `Tail.lsubst` binds every argument with a `let` in front of the block
(`Tail.letSpine`), so a control transfer can neither duplicate a computation nor delay
one.

## What is proved

* The answers are described by `Value`, and the ones the language cannot run any further
  because they reach out of it — a reference to a top-level declaration, a variable, a
  constant of the host platform — are `Neutral`.  A closed term over the empty
  signature whose externs all have a meaning has no neutral subterm, and then `Value`
  means what it should: a literal, a delayed value, a lambda, or a **constructor of one
  of the schemas applied to values**.
* `canonical_prim`, `canonical_fn`, `canonical_lazy`, `canonical_bool` and
  `canonical_oneCtor` are the canonical-forms lemmas that say so: what an answer of each
  shape of type can be.
* `DeltaRedex.steps`: **a δ-redex takes a step** — a function of the runtime applied to
  as many literals as it takes is never stuck.
* `quickAp_steps`, `quickAp_steps_of_steps`, `not_neutral_quickAp`, `step_quickAp_inv`:
  **hash-consing is erasure** — `lean_sharecommon_quick` answers its argument, at every
  type, and an application of it is never an answer
  (`SHARECOMMON_EMULATION.md`, option A).
* The examples at the end of the file are proofs that `lean_nat_add 1 2` runs to `3`,
  that `lean_float_sin 1.0` runs to the sine of `1.0`, and that a function of the runtime
  waiting for a further argument is an answer.

The progress theorem — *every* closed term is an answer or takes a step, with no shape
left out — is `Term.progress`, in `LakeJs.Progress`.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

variable {Sg : Sig}

/-! ## Reading a spine, and choosing a branch -/

/-- The `j`-th term of a spine, at the type the list of types gives it. -/
def Spine.get? {Γ : Ctx} :
    ∀ {σs : List Ty} {τ : Ty}, Spine Sg Γ σs → (j : Nat) → σs[j]? = some τ →
      Term Sg Γ τ
  | _ :: _, _, .cons t _, 0, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      exact h ▸ t
  | _ :: _, _, .cons _ rest, j + 1, h => rest.get? j (by simpa using h)

/-- The branch a dispatch takes for tag `i`: the branch that tests it, the default branch
    if none does — and, when the dispatch is exhaustive and so has no default branch, the
    branch the coverage proof `hcov` says is there. -/
def Alts.select {Γ : Ctx} {τ : Ty} :
    ∀ {tags : List Nat} {full : Bool}, Alts Sg Γ τ tags full → (i : Nat) →
      (hcov : full = true → i ∈ tags) → Term Sg Γ τ
  | _, _, .deflt t, _, _ => t
  | _, _, .nilFull, _, hcov => absurd (hcov rfl) (by simp)
  | _, _, .cons tag t rest, i, hcov =>
      if h : tag = i then t
      else
        rest.select i (fun hf => by
          have hmem := hcov hf
          rcases List.mem_cons.mp hmem with heq | hrest
          · exact absurd heq.symm h
          · exact hrest)

/-- The same, for the branches of a dispatch inside a block. -/
def AltsT.select {Γ : Ctx} {Ω : LCtx} {τ : Ty} :
    ∀ {tags : List Nat} {full : Bool}, AltsT Sg Γ Ω τ tags full → (i : Nat) →
      (hcov : full = true → i ∈ tags) → Tail Sg Γ Ω τ
  | _, _, .deflt b, _, _ => b
  | _, _, .nilFull, _, hcov => absurd (hcov rfl) (by simp)
  | _, _, .cons tag b rest, i, hcov =>
      if h : tag = i then b
      else
        rest.select i (fun hf => by
          have hmem := hcov hf
          rcases List.mem_cons.mp hmem with heq | hrest
          · exact absurd heq.symm h
          · exact hrest)

/-! ## δ: running a function of the runtime

`Term.extern` is a *curried* term, so a function of the runtime applied to all of its
arguments is a tower of `Term.ap`s over it.  When every one of those arguments is a
literal, the whole tower is a **δ-redex** and steps in one go to the literal of
`e.eval …` — the catalogue's meaning of the entry at those values, which is a **total**
function, so there is no side condition and no way for the evaluator to stop in front of
a saturated call.  Nothing partial is a redex: `lean_nat_add 1` is a function still
waiting for its second argument, and it is an answer. -/

/-- A term the evaluator can run because it is a function of the runtime applied to as
    many literals as it takes — or because it is `lean_sharecommon_quick` applied to
    anything, which is the identity. -/
inductive DeltaRedex {Γ : Ctx} : ∀ {τ : Ty}, Term Sg Γ τ → Prop
  /-- A constant of the runtime.  (`LeanInitPureExternLazy` is empty today, so this
      constructor has no instance; see `(‡)` in `LakeJs.LeanInitPureExterns`.) -/
  | const {p : LeanPrimTy} (e : LeanInitPureExternLazy p) :
      DeltaRedex (Term.extern (Sg := Sg) (Γ := Γ) (.const e))
  /-- A one-argument function of the runtime, applied to a literal. -/
  | prim1 {a b : LeanPrimTy} (e : LeanInitPureExtern1OnlyPrim a b) (l : LeanPrimLit a) :
      DeltaRedex (Term.ap (Sg := Sg) (Γ := Γ) (.extern (.prim1 e)) (.lit l))
  /-- A two-argument function of the runtime, applied to two literals. -/
  | prim2 {a b c : LeanPrimTy} (e : LeanInitPureExtern2OnlyPrim a b c) (l1 : LeanPrimLit a)
      (l2 : LeanPrimLit b) :
      DeltaRedex (Term.ap (Sg := Sg) (Γ := Γ)
        (.ap (.extern (.prim2 e)) (.lit l1)) (.lit l2))
  /-- A three-argument function of the runtime, applied to three literals. -/
  | prim3 {a b c d : LeanPrimTy} (e : LeanInitPureExtern3OnlyPrim a b c d)
      (l1 : LeanPrimLit a) (l2 : LeanPrimLit b) (l3 : LeanPrimLit c) :
      DeltaRedex (Term.ap (Sg := Sg) (Γ := Γ)
        (.ap (.ap (.extern (.prim3 e)) (.lit l1)) (.lit l2)) (.lit l3))
  /-- A five-argument function of the runtime, applied to five literals. -/
  | prim5 {a b c d e' f : LeanPrimTy} (e : LeanInitPureExtern5 a b c d e' f)
      (l1 : LeanPrimLit a) (l2 : LeanPrimLit b) (l3 : LeanPrimLit c) (l4 : LeanPrimLit d)
      (l5 : LeanPrimLit e') :
      DeltaRedex (Term.ap (Sg := Sg) (Γ := Γ)
        (.ap (.ap (.ap (.ap (.extern (.prim5 e)) (.lit l1)) (.lit l2)) (.lit l3)) (.lit l4))
        (.lit l5))
  /-- **Hash-consing is the identity on values.**  `lean_sharecommon_quick` answers a
      value equal to its argument — it only replaces subterms by copies already in the
      runtime's table, which is invisible to this language — so it is a redex at *every*
      type, not only at the terminal ones the `eval` tables speak about.  See
      `SHARECOMMON_EMULATION.md`.

      Unlike the other five, this one does not ask that its argument is an answer.  It
      cannot: `Neutral` asks that a term is *not* a δ-redex, so `DeltaRedex` occurs
      negatively in it and cannot be defined together with `Value`.  Nothing is lost by
      firing early, because the rule keeps the argument exactly as it is — the argument
      is then evaluated where it stands, rather than under the identity. -/
  | quick {τ : Ty} {t : Term Sg Γ τ} :
      DeltaRedex (Term.ap (Sg := Sg) (Γ := Γ)
        (.extern (.poly1 (.lean_sharecommon_quick τ))) t)

/-! ## Values, and where the language stops -/

mutual

/-- A **neutral** term: one the language cannot run, because what it is waiting for is
    outside the language.  A variable, a reference to a top-level declaration, a function
    the runtime implements, and every eliminator applied to one of those. -/
inductive Neutral {Γ : Ctx} : ∀ {τ : Ty}, Term Sg Γ τ → Prop
  | var {τ : Ty} (v : Γ ∋ τ) : Neutral (.var v)
  | global {τ : Ty} (r : GlobalRef Sg.decls τ) : Neutral (.global r)
  | extern {σs : List Ty} {τ : Ty} (e : Externs σs τ)
      (h : ¬ DeltaRedex (Term.extern (Sg := Sg) (Γ := Γ) e)) :
      Neutral (.extern e)
  | ap {σ τ : Ty} {f : Term Sg Γ (σ ⇒ τ)} {a : Term Sg Γ σ} :
      Neutral f → Value a → ¬ DeltaRedex (.ap f a) → Neutral (.ap f a)
  | proj {σ τ : Ty} {e : Term Sg Γ σ} (i j : Nat) (hOne : σ.numCtors? = some 1)
      (h : σ.fieldTy? i j = some τ) : Neutral e → Neutral (.proj e i j hOne h)
  | tagOf {σ : Ty} {e : Term Sg Γ σ} (h : σ.isTagged = true) :
      Neutral e → Neutral (.tagOf e h)
  | caseTag {σ τ : Ty} {tags : List Nat} {full : Bool} {e : Term Sg Γ σ}
      {alts : Alts Sg Γ τ tags full} (h : σ.caseOkAlts full tags = true) :
      Neutral e → Neutral (.caseTag e alts h)
  | ite {τ : Ty} {c : Term Sg Γ (.prim .bool)} {t e : Term Sg Γ τ} :
      Neutral c → Neutral (.ite c t e)
  | lazyForce {τ : Ty} {e : Term Sg Γ (.lazy τ)} : Neutral e → Neutral (.lazyForce e)
  /-- A block whose tail waits for something outside the language.  A block that
      *answers* is not neutral: `Step.blockRet` runs it. -/
  | block {τ : Ty} {b : Tail Sg Γ [] τ} : TailNeutral b → Neutral (.block b)

/-- A tail the evaluator cannot run: its head — the condition of a branch, the scrutinee
    of a dispatch — is waiting for something outside the language.  Every other shape of
    tail either answers (`Tail.ret`, which the enclosing block returns) or steps. -/
inductive TailNeutral {Γ : Ctx} : ∀ {τ : Ty}, Tail Sg Γ [] τ → Prop
  | iteT {τ : Ty} {c : Term Sg Γ (.prim .bool)} {t e : Tail Sg Γ [] τ} :
      Neutral c → TailNeutral (.iteT c t e)
  | caseT {σ τ : Ty} {tags : List Nat} {full : Bool} {e : Term Sg Γ σ}
      {alts : AltsT Sg Γ [] τ tags full} (h : σ.caseOkAlts full tags = true) :
      Neutral e → TailNeutral (.caseT e alts h)

/-- An **answer**: a term the evaluator is done with. -/
inductive Value {Γ : Ctx} : ∀ {τ : Ty}, Term Sg Γ τ → Prop
  /-- A function. -/
  | lam {σ τ : Ty} (b : Term Sg (σ :: Γ) τ) : Value (.lam b)
  /-- A constant of a terminal type. -/
  | lit {p : LeanPrimTy} (l : LeanPrimLit p) : Value (.lit l)
  /-- A delayed value: what is inside is *not* run. -/
  | lazyMk {τ : Ty} (e : Term Sg Γ τ) : Value (.lazyMk e)
  /-- A constructor of one of the schemas, applied to answers.  A **boolean** is the
      one type that has a layout and a literal both, and the literal is the answer:
      `Step.ctorBool` turns a constructor of `Ty.bool` into `true` or `false`, so a
      constructor at that type is not an answer. -/
  | ctor {τ : Ty} (i : Nat) (fs : Layout.FieldLayout) (h : τ.ctorFields? i = some fs)
      (hb : τ ≠ Ty.bool) {args : Spine Sg Γ fs} :
      SpineValue args → Value (.ctor i fs h args)
  /-- A term the language cannot run any further. -/
  | neutral {τ : Ty} {t : Term Sg Γ τ} : Neutral t → Value t

/-- Every term of a spine is an answer. -/
inductive SpineValue {Γ : Ctx} : ∀ {σs : List Ty}, Spine Sg Γ σs → Prop
  | nil : SpineValue .nil
  | cons {σ : Ty} {σs : List Ty} {t : Term Sg Γ σ} {rest : Spine Sg Γ σs} :
      Value t → SpineValue rest → SpineValue (.cons t rest)

end

/-! ## The step relation -/

mutual

/-- One step of call-by-value evaluation. -/
inductive Step {Γ : Ctx} : ∀ {τ : Ty}, Term Sg Γ τ → Term Sg Γ τ → Prop
  /-- **β**. -/
  | beta {σ τ : Ty} {b : Term Sg (σ :: Γ) τ} {a : Term Sg Γ σ} :
      Value a → Step (.ap (.lam b) a) (b.subst0 a)
  /-- **δ**: a constant of the runtime is its value, delayed.  (No instance today:
      `LeanInitPureExternLazy` is empty, see `(‡)` in `LakeJs.LeanInitPureExterns`.) -/
  | deltaConst {p : LeanPrimTy} (e : LeanInitPureExternLazy p) :
      Step (Term.extern (.const e)) (.lazyMk (.lit (LeanPrimLit.ofVal p e.eval)))
  /-- **δ**: a one-argument function of the runtime, run on a literal. -/
  | deltaPrim1 {a b : LeanPrimTy} (e : LeanInitPureExtern1OnlyPrim a b) (l : LeanPrimLit a) :
      Step (Term.ap (.extern (.prim1 e)) (.lit l)) (.lit (LeanPrimLit.ofVal b (e.eval l.val)))
  /-- **δ**: a two-argument function of the runtime, run on two literals. -/
  | deltaPrim2 {a b c : LeanPrimTy} (e : LeanInitPureExtern2OnlyPrim a b c)
      (l1 : LeanPrimLit a) (l2 : LeanPrimLit b) :
      Step (Term.ap (.ap (.extern (.prim2 e)) (.lit l1)) (.lit l2))
        (.lit (LeanPrimLit.ofVal c (e.eval l1.val l2.val)))
  /-- **δ**: a three-argument function of the runtime, run on three literals. -/
  | deltaPrim3 {a b c d : LeanPrimTy} (e : LeanInitPureExtern3OnlyPrim a b c d)
      (l1 : LeanPrimLit a) (l2 : LeanPrimLit b) (l3 : LeanPrimLit c) :
      Step (Term.ap (.ap (.ap (.extern (.prim3 e)) (.lit l1)) (.lit l2)) (.lit l3))
        (.lit (LeanPrimLit.ofVal d (e.eval l1.val l2.val l3.val)))
  /-- **δ**: a five-argument function of the runtime, run on five literals. -/
  | deltaPrim5 {a b c d e' f : LeanPrimTy} (e : LeanInitPureExtern5 a b c d e' f)
      (l1 : LeanPrimLit a) (l2 : LeanPrimLit b) (l3 : LeanPrimLit c) (l4 : LeanPrimLit d)
      (l5 : LeanPrimLit e') :
      Step (Term.ap (.ap (.ap (.ap (.ap (.extern (.prim5 e)) (.lit l1)) (.lit l2))
        (.lit l3)) (.lit l4)) (.lit l5))
        (.lit (LeanPrimLit.ofVal f (e.eval l1.val l2.val l3.val l4.val l5.val)))
  /-- **δ at every type**: `lean_sharecommon_quick` is the identity on values.  Sharing
      is a property of the runtime's representation, not of the value, so the term it
      answers with is the term it was given.  See `SHARECOMMON_EMULATION.md`. -/
  | quick {τ : Ty} {t : Term Sg Γ τ} :
      Step (Term.ap (.extern (.poly1 (.lean_sharecommon_quick τ))) t) t
  /-- Run the function of an application first. -/
  | apFun {σ τ : Ty} {f f' : Term Sg Γ (σ ⇒ τ)} {a : Term Sg Γ σ} :
      Step f f' → Step (.ap f a) (.ap f' a)
  /-- Then its argument. -/
  | apArg {σ τ : Ty} {f : Term Sg Γ (σ ⇒ τ)} {a a' : Term Sg Γ σ} :
      Value f → Step a a' → Step (.ap f a) (.ap f a')
  /-- A `let` of an answer is a substitution. -/
  | letV {σ τ : Ty} {e : Term Sg Γ σ} {b : Term Sg (σ :: Γ) τ} :
      Value e → Step (.letE e b) (b.subst0 e)
  /-- Run what a `let` binds first. -/
  | letStep {σ τ : Ty} {e e' : Term Sg Γ σ} {b : Term Sg (σ :: Γ) τ} :
      Step e e' → Step (.letE e b) (.letE e' b)
  /-- `if true`. -/
  | iteTrue {τ : Ty} {t e : Term Sg Γ τ} :
      Step (.ite (.lit (.bool true)) t e) t
  /-- `if false`. -/
  | iteFalse {τ : Ty} {t e : Term Sg Γ τ} :
      Step (.ite (.lit (.bool false)) t e) e
  /-- Run the condition first. -/
  | iteCond {τ : Ty} {c c' : Term Sg Γ (.prim .bool)} {t e : Term Sg Γ τ} :
      Step c c' → Step (.ite c t e) (.ite c' t e)
  /-- Running a delayed value gives what was delayed.  **Unmemoised**: forcing the same
      delay twice runs what it delays twice, exactly as `() => …` does in the target. -/
  | force {τ : Ty} {e : Term Sg Γ τ} : Step (.lazyForce (.lazyMk e)) e
  /-- Run what is being forced first. -/
  | forceStep {τ : Ty} {e e' : Term Sg Γ (.lazy τ)} :
      Step e e' → Step (.lazyForce e) (.lazyForce e')
  /-- Reading a field of a constructor gives the field.  The type has one constructor
      (`hOne`), so the constructor the value carries is the one the projection reads. -/
  | projCtor {σ τ : Ty} {fs : Layout.FieldLayout} {args : Spine Sg Γ fs} {i j : Nat}
      {hc : σ.ctorFields? i = some fs} {hOne : σ.numCtors? = some 1}
      {h : σ.fieldTy? i j = some τ} (hg : fs[j]? = some τ) :
      Step (.proj (.ctor i fs hc args) i j hOne h) (args.get? j hg)
  /-- Run the value a field is read of first. -/
  | projStep {σ τ : Ty} {e e' : Term Sg Γ σ} {i j : Nat}
      {hOne : σ.numCtors? = some 1} {h : σ.fieldTy? i j = some τ} :
      Step e e' → Step (.proj e i j hOne h) (.proj e' i j hOne h)
  /-- The tag of a constructor is its number. -/
  | tagOfCtor {σ : Ty} {fs : Layout.FieldLayout} {args : Spine Sg Γ fs} {i : Nat}
      {hc : σ.ctorFields? i = some fs} {h : σ.isTagged = true} :
      Step (.tagOf (.ctor i fs hc args) h) (.lit (.nat i))
  /-- A boolean *is* the two-constructor sum, so it has a tag: `false` is `0`. -/
  | tagOfBool {b : Bool} {h : Ty.bool.isTagged = true} :
      Step (.tagOf (.lit (.bool b)) h) (.lit (.nat (if b then 1 else 0)))
  /-- Run the value whose tag is read first. -/
  | tagOfStep {σ : Ty} {e e' : Term Sg Γ σ} {h : σ.isTagged = true} :
      Step e e' → Step (.tagOf e h) (.tagOf e' h)
  /-- A dispatch on a constructor takes the branch for its tag. -/
  | caseCtor {σ τ : Ty} {tags : List Nat} {full : Bool} {fs : Layout.FieldLayout}
      {args : Spine Sg Γ fs} {i : Nat} {hc : σ.ctorFields? i = some fs}
      {alts : Alts Sg Γ τ tags full} {h : σ.caseOkAlts full tags = true} :
      Step (.caseTag (.ctor i fs hc args) alts h)
        (alts.select i (Ty.mem_of_caseOkAlts h hc))
  /-- A dispatch on a boolean takes the branch for `0` or for `1`. -/
  | caseBool {τ : Ty} {tags : List Nat} {full : Bool} {b : Bool}
      {alts : Alts Sg Γ τ tags full} {h : Ty.bool.caseOkAlts full tags = true} :
      Step (.caseTag (.lit (.bool b)) alts h)
        (alts.select (if b then 1 else 0)
          (Ty.mem_of_caseOkAlts h (Ty.bool_ctorFields b)))
  /-- Run the scrutinee first. -/
  | caseStep {σ τ : Ty} {tags : List Nat} {full : Bool} {e e' : Term Sg Γ σ}
      {alts : Alts Sg Γ τ tags full} {h : σ.caseOkAlts full tags = true} :
      Step e e' → Step (.caseTag e alts h) (.caseTag e' alts h)
  /-- A constructor of `Ty.bool` is a boolean literal: the two-constructor field-less
      sum *is* the boolean, and `false`/`true` are its constructors `0`/`1`. -/
  | ctorBool {i : Nat} {fs : Layout.FieldLayout} {h : Ty.bool.ctorFields? i = some fs}
      {args : Spine Sg Γ fs} :
      Step (.ctor i fs h args) (.lit (.bool (decide (i = 1))))
  /-- Run the fields of a constructor. -/
  | ctorStep {τ : Ty} {i : Nat} {fs : Layout.FieldLayout} {h : τ.ctorFields? i = some fs}
      {args args' : Spine Sg Γ fs} :
      SpineStep args args' → Step (.ctor i fs h args) (.ctor i fs h args')
  /-- **Answer with the answer of the block.**  A block whose tail is `ret` is the term
      that tail answers with; this is the one rule that leaves the block grammar. -/
  | blockRet {τ : Ty} {t : Term Sg Γ τ} : Step (.block (.ret t)) t
  /-- Run the tail of a block. -/
  | blockStep {τ : Ty} {b b' : Tail Sg Γ [] τ} : StepT b b' → Step (.block b) (.block b')

/-- One step of the tail of a block, in the **empty** label context: there is nothing to
    jump out to, so a `Tail.jmp` has no target here and every other shape either answers
    or steps. -/
inductive StepT {Γ : Ctx} : ∀ {τ : Ty}, Tail Sg Γ [] τ → Tail Sg Γ [] τ → Prop
  /-- Run the term a block answers with. -/
  | retStep {τ : Ty} {t t' : Term Sg Γ τ} : Step t t' → StepT (.ret t) (.ret t')
  /-- A `let` of an answer is a substitution. -/
  | letV {σ τ : Ty} {e : Term Sg Γ σ} {b : Tail Sg (σ :: Γ) [] τ} :
      Value e → StepT (.letT e b) (b.subst0 e)
  /-- Run what a `let` binds first. -/
  | letStep {σ τ : Ty} {e e' : Term Sg Γ σ} {b : Tail Sg (σ :: Γ) [] τ} :
      Step e e' → StepT (.letT e b) (.letT e' b)
  /-- `if true`. -/
  | iteTrue {τ : Ty} {t e : Tail Sg Γ [] τ} :
      StepT (.iteT (.lit (.bool true)) t e) t
  /-- `if false`. -/
  | iteFalse {τ : Ty} {t e : Tail Sg Γ [] τ} :
      StepT (.iteT (.lit (.bool false)) t e) e
  /-- Run the condition first. -/
  | iteCond {τ : Ty} {c c' : Term Sg Γ (.prim .bool)} {t e : Tail Sg Γ [] τ} :
      Step c c' → StepT (.iteT c t e) (.iteT c' t e)
  /-- A dispatch on a constructor takes the branch for its tag. -/
  | caseCtor {σ τ : Ty} {tags : List Nat} {full : Bool} {fs : Layout.FieldLayout}
      {args : Spine Sg Γ fs} {i : Nat} {hc : σ.ctorFields? i = some fs}
      {alts : AltsT Sg Γ [] τ tags full} {h : σ.caseOkAlts full tags = true} :
      StepT (.caseT (.ctor i fs hc args) alts h)
        (alts.select i (Ty.mem_of_caseOkAlts h hc))
  /-- A dispatch on a boolean takes the branch for `0` or for `1`. -/
  | caseBool {τ : Ty} {tags : List Nat} {full : Bool} {b : Bool}
      {alts : AltsT Sg Γ [] τ tags full} {h : Ty.bool.caseOkAlts full tags = true} :
      StepT (.caseT (.lit (.bool b)) alts h)
        (alts.select (if b then 1 else 0)
          (Ty.mem_of_caseOkAlts h (Ty.bool_ctorFields b)))
  /-- Run the scrutinee first. -/
  | caseStep {σ τ : Ty} {tags : List Nat} {full : Bool} {e e' : Term Sg Γ σ}
      {alts : AltsT Sg Γ [] τ tags full} {h : σ.caseOkAlts full tags = true} :
      Step e e' → StepT (.caseT e alts h) (.caseT e' alts h)
  /-- **A shared tail is inlined at its jumps.**  This is the β rule of the label
      context: the rest of the block, with every jump to the label just bound replaced by
      the block it names, the arguments of the jump bound in front of it by
      `Tail.letSpine` rather than substituted into it. -/
  | labelJoin {ps : List Ty} {τ : Ty} {body : Tail Sg (ps ++ Γ) [] τ}
      {rest : Tail Sg Γ [ps] τ} :
      StepT (.label false body rest) (rest.lsubst0 body)
  /-- **A loop is re-entered at its jumps.**  The same rule, with the loop itself
      substituted for the label (`Tail.loopEntry`): a jump to a self-label runs the loop
      again with the arguments of the jump.  This is the one rule of the language that
      can repeat work. -/
  | labelLoop {ps : List Ty} {τ : Ty} {body : Tail Sg (ps ++ Γ) [ps] τ}
      {rest : Tail Sg Γ [ps] τ} :
      StepT (.label true body rest) (rest.lsubst0 (Tail.loopEntry body))

/-- One step inside a spine, from the left. -/
inductive SpineStep {Γ : Ctx} :
    ∀ {σs : List Ty}, Spine Sg Γ σs → Spine Sg Γ σs → Prop
  | head {σ : Ty} {σs : List Ty} {t t' : Term Sg Γ σ} {rest : Spine Sg Γ σs} :
      Step t t' → SpineStep (.cons t rest) (.cons t' rest)
  | tail {σ : Ty} {σs : List Ty} {t : Term Sg Γ σ} {rest rest' : Spine Sg Γ σs} :
      Value t → SpineStep rest rest' → SpineStep (.cons t rest) (.cons t rest')

end

/-- Zero or more steps. -/
inductive Steps {Γ : Ctx} {τ : Ty} : Term Sg Γ τ → Term Sg Γ τ → Prop
  | refl {t} : Steps t t
  | tail {t u v} : Steps t u → Step u v → Steps t v

/-! ## Canonical forms

What an answer of each shape of type can be.  These are what the progress proof runs
on, and together they are the statement that an answer is a literal, a lambda, a delayed
value or a constructor of one of the schemas — unless it is neutral, i.e. unless it is
waiting for something outside the language. -/

/-- A function type has no layout, so nothing can be built at one. -/
theorem isTagged_fn (σ τ : Ty) : (σ ⇒ τ).isTagged = false := rfl

/-- An answer of function type is a lambda or neutral. -/
theorem canonical_fn {Γ : Ctx} {σ τ : Ty} {t : Term Sg Γ (σ ⇒ τ)} :
    Value t → (∃ b : Term Sg (σ :: Γ) τ, t = .lam b) ∨ Neutral t := by
  intro hv
  cases hv with
  | lam b => exact Or.inl ⟨b, rfl⟩
  | ctor i fs h _ _ => exact absurd h (by simp [Ty.ctorFields?, Ty.layout?])
  | neutral hn => exact Or.inr hn

/-- An answer of a delayed type is a delay or neutral. -/
theorem canonical_lazy {Γ : Ctx} {τ : Ty} {t : Term Sg Γ (.lazy τ)} :
    Value t → (∃ e : Term Sg Γ τ, t = .lazyMk e) ∨ Neutral t := by
  intro hv
  cases hv with
  | lazyMk e => exact Or.inl ⟨e, rfl⟩
  | ctor i fs h _ _ => exact absurd h (by simp [Ty.ctorFields?, Ty.layout?])
  | neutral hn => exact Or.inr hn

/-- An answer of a terminal type is a literal or neutral. -/
theorem canonical_prim {Γ : Ctx} {p : LeanPrimTy} {t : Term Sg Γ (.prim p)} :
    Value t → (∃ l : LeanPrimLit p, t = .lit l) ∨ Neutral t := by
  intro hv
  cases hv with
  | lit l => exact Or.inl ⟨l, rfl⟩
  | ctor i fs h hb _ =>
      exact absurd h (by cases p <;> first
        | exact absurd rfl hb
        | simp [Ty.ctorFields?, Ty.layout?])
  | neutral hn => exact Or.inr hn

/-- An answer of a **boolean** type is `true`, `false`, or neutral: a boolean is the
    two-constructor field-less sum, and `Term.ctor` can build one. -/
theorem canonical_bool {Γ : Ctx} {t : Term Sg Γ Ty.bool} :
    Value t → (∃ b : Bool, t = .lit (.bool b)) ∨ Neutral t := by
  intro hv
  rcases canonical_prim hv with ⟨l, rfl⟩ | hn
  · cases l with
    | bool b => exact Or.inl ⟨b, rfl⟩
  · exact Or.inr hn

/-- **An answer of a type with exactly one constructor is that constructor, or neutral.**
    This is the canonical-forms lemma `Term.proj` rests on: a record is built one way, so
    reading a field of one is never stuck. -/
theorem canonical_oneCtor {Γ : Ctx} {σ : Ty} {t : Term Sg Γ σ}
    (hOne : σ.numCtors? = some 1) (hv : Value t) :
    (∃ (fs : Layout.FieldLayout) (h : σ.ctorFields? 0 = some fs)
      (args : Spine Sg Γ fs), t = .ctor 0 fs h args ∧ SpineValue args) ∨ Neutral t := by
  cases hv with
  | lam b => exact absurd hOne (by simp [Ty.numCtors?, Ty.layout?])
  | lazyMk e => exact absurd hOne (by simp [Ty.numCtors?, Ty.layout?])
  | lit l =>
      exact absurd hOne (by
        cases l <;> simp [Ty.numCtors?, Ty.layout?])
  | ctor i fs h hb hsv =>
      have hi : i = 0 := Ty.eq_zero_of_ctorFields?_of_numCtors?_one hOne h
      subst hi
      exact Or.inl ⟨fs, h, _, rfl, hsv⟩
  | neutral hn => exact Or.inr hn

/-- **A δ-redex takes a step**: a function of the runtime applied to as many literals as
    it takes is never stuck. -/
theorem DeltaRedex.steps {Γ : Ctx} {τ : Ty} {t : Term Sg Γ τ}
    (h : DeltaRedex t) : ∃ t' : Term Sg Γ τ, Step t t' := by
  cases h with
  | const e => exact ⟨_, .deltaConst e⟩
  | prim1 e l => exact ⟨_, .deltaPrim1 e l⟩
  | prim2 e l1 l2 => exact ⟨_, .deltaPrim2 e l1 l2⟩
  | prim3 e l1 l2 l3 => exact ⟨_, .deltaPrim3 e l1 l2 l3⟩
  | prim5 e l1 l2 l3 l4 l5 => exact ⟨_, .deltaPrim5 e l1 l2 l3 l4 l5⟩
  | quick => exact ⟨_, .quick⟩

/-! ## A saturated call of the runtime always runs

Since every entry of the terminal families denotes a **total** function of the values of
its arguments (`LakeJs.ExternEval1`, `LakeJs.ExternEval2`, `LakeJs.ExternEvalMisc`), the
δ-rules carry no side condition, and a function of the runtime applied to as many
literals as it takes is never an answer: it runs. -/

/-- A one-argument function of the runtime, on a literal, runs. -/
theorem steps_prim1 {Γ : Ctx} {a b : LeanPrimTy}
    (e : LeanInitPureExtern1OnlyPrim a b) (l : LeanPrimLit a) :
    ∃ t' : Term Sg Γ (.prim b), Step (Term.ap (.extern (.prim1 e)) (.lit l)) t' :=
  (DeltaRedex.prim1 e l).steps

/-- A two-argument one, on two literals, runs. -/
theorem steps_prim2 {Γ : Ctx} {a b c : LeanPrimTy}
    (e : LeanInitPureExtern2OnlyPrim a b c) (l1 : LeanPrimLit a) (l2 : LeanPrimLit b) :
    ∃ t' : Term Sg Γ (.prim c),
      Step (Term.ap (.ap (.extern (.prim2 e)) (.lit l1)) (.lit l2)) t' :=
  (DeltaRedex.prim2 e l1 l2).steps

/-- A three-argument one, on three literals, runs. -/
theorem steps_prim3 {Γ : Ctx} {a b c d : LeanPrimTy}
    (e : LeanInitPureExtern3OnlyPrim a b c d) (l1 : LeanPrimLit a) (l2 : LeanPrimLit b)
    (l3 : LeanPrimLit c) :
    ∃ t' : Term Sg Γ (.prim d),
      Step (Term.ap (.ap (.ap (.extern (.prim3 e)) (.lit l1)) (.lit l2)) (.lit l3)) t' :=
  (DeltaRedex.prim3 e l1 l2 l3).steps

/-! ## Hash-consing is erasure

The one `ShareCommon` entry the catalogue keeps, `lean_sharecommon_quick`, is the
identity on values (`SHARECOMMON_EMULATION.md`, option A).  Three facts say that the
evaluator treats it as one: an application of it is never stuck, it answers exactly its
argument, and it cannot delay or change what its argument answers. -/

/-- The term `lean_sharecommon_quick t`. -/
abbrev quickAp {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ) : Term Sg Γ τ :=
  .ap (.extern (.poly1 (.lean_sharecommon_quick τ))) t

/-- Reductions compose. -/
theorem Steps.trans {Γ : Ctx} {τ : Ty} {t u v : Term Sg Γ τ}
    (h1 : Steps t u) (h2 : Steps u v) : Steps t v := by
  induction h2 with
  | refl => exact h1
  | tail _ s ih => exact .tail ih s

/-- **`lean_sharecommon_quick` is erased**: the application reduces to its argument. -/
theorem quickAp_steps {Γ : Ctx} {τ : Ty} {t : Term Sg Γ τ} :
    Steps (quickAp t) t :=
  .tail .refl .quick

/-- **Erasure is observationally sound**: whatever the argument reduces to, the
    application reduces to as well — in particular to the same answer. -/
theorem quickAp_steps_of_steps {Γ : Ctx} {τ : Ty} {t u : Term Sg Γ τ}
    (h : Steps t u) : Steps (quickAp t) u :=
  quickAp_steps.trans h

/-- **The evaluator never stops in front of it**: an application of
    `lean_sharecommon_quick` is not neutral, so it is an answer at no type. -/
theorem not_neutral_quickAp {Γ : Ctx} {τ : Ty} {t : Term Sg Γ τ} :
    ¬ Neutral (Sg := Sg) (quickAp t) := by
  intro h
  cases h with
  | ap _ _ hnd => exact hnd .quick

/-- **Nothing else can happen at that head**: a step of `lean_sharecommon_quick t` either
    erases the application, or is a step of the argument under it.  With the previous
    theorem this is the whole content of erasure: the application answers what the
    argument answers, by whichever order the two rules are taken. -/
theorem step_quickAp_inv {Γ : Ctx} {τ : Ty} {t s : Term Sg Γ τ}
    (h : Step (quickAp t) s) :
    s = t ∨ ∃ t' : Term Sg Γ τ, s = quickAp t' ∧ Step t t' := by
  cases h with
  | quick => exact Or.inl rfl
  | apArg _ hs => exact Or.inr ⟨_, rfl, hs⟩
  | apFun hs => cases hs

/-! ## The evaluator really does run the functions of the runtime

Three examples, each a proof rather than a test: the term on the left steps to the
literal on the right, and `rfl` is what checks that the catalogue's meaning of the entry
at those values is that literal. -/

section Examples

/-- The empty signature: these examples mention no top-level declaration. -/
private def sigNone : Sig := ⟨[], rfl⟩

/-- `lean_nat_add 1 2` runs to `3`. -/
example :
    Step (Sg := sigNone) (Γ := [])
      (.ap (.ap (.extern (.prim2 .lean_nat_add)) (.lit (.nat 1))) (.lit (.nat 2)))
      (.lit (.nat 3)) :=
  .deltaPrim2 .lean_nat_add (.nat 1) (.nat 2)

/-- `lean_float_sin 1.0` runs to the sine of `1.0`. -/
example :
    Step (Sg := sigNone) (Γ := [])
      (.ap (.extern (.prim1 .sin)) (.lit (.float 1.0)))
      (.lit (.float (Float.sin 1.0))) :=
  .deltaPrim1 .sin (.float 1.0)

/-- `lean_string_append "ab" "c"` runs to `"abc"`. -/
example :
    Step (Sg := sigNone) (Γ := [])
      (.ap (.ap (.extern (.prim2 .lean_string_append)) (.lit (.string "ab")))
        (.lit (.string "c")))
      (.lit (.string ("ab" ++ "c"))) :=
  .deltaPrim2 .lean_string_append (.string "ab") (.string "c")

/-- `lean_sharecommon_quick 3` runs to `3`: sharing a value is the value. -/
example :
    Step (Sg := sigNone) (Γ := [])
      (.ap (.extern (.poly1 (.lean_sharecommon_quick (.prim .nat)))) (.lit (.nat 3)))
      (.lit (.nat 3)) :=
  .quick

/-! ### What a jump does with its arguments

Two examples of the rule that keeps a control transfer call-by-value: **every** argument
is bound by a `let` in front of the block, so it is run once, before the block, whatever
it is. -/

/-- `Term.sharedTail` jumps with literals, and inlining its label binds each of them in
    front of the block it names, once per jump. -/
example :
    Step (Sg := sigNone) (Γ := [Ty.bool]) Term.sharedTail
      (.block (.iteT (♯0)
        (.letT (.lit (.nat 1)) (.ret (♯0)))
        (.letT (.lit (.nat 2)) (.ret (♯0))))) :=
  .blockStep .labelJoin

/-- A jump whose argument is a computation: `lean_nat_add 1 2`. -/
private def jumpComputed : Term sigNone [] Ty.nat :=
  .block
    (.label (ps := [Ty.nat]) false (.ret (♯0))
      (.jmp .head (.cons (Term.callExtern (.prim2 .lean_nat_add)
        (.cons (.lit (.nat 1)) (.cons (.lit (.nat 2)) .nil))) .nil)))

/-- Inlining that label **binds** the argument rather than copying it into the block: the
    computation is run once, where the jump stood. -/
example :
    Step (Sg := sigNone) (Γ := []) jumpComputed
      (.block (.letT (Term.callExtern (.prim2 .lean_nat_add)
        (.cons (.lit (.nat 1)) (.cons (.lit (.nat 2)) .nil))) (.ret (♯0)))) :=
  .blockStep .labelJoin

/-! ### A loop is a label jumped to from its own body

`Term.tco01` is the `Tco01` snapshot by hand.  Its block is one self-label, entered by a
jump; the step below is the one that substitutes the loop for the label, after which the
jump that entered it has become the loop, run on the argument. -/

/-- The loop of `Term.tco01`, entered: the block steps, and what it steps to is again a
    block with the same label. -/
example :
    ∃ u : Term sigNone [Ty.nat] Ty.nat,
      Step (Sg := sigNone) (Γ := [Ty.nat])
        (.block (Tail.label (ps := [Ty.nat]) true
          (.iteT (Term.callExtern (.prim2 .lean_nat_dec_eq)
              (.cons (♯0) (.cons (.lit (.nat 0)) .nil)))
            (.ret (♯0))
            (.jmp .head (.cons (Term.callExtern (.prim2 .lean_nat_sub)
              (.cons (♯0) (.cons (.lit (.nat 1)) .nil))) .nil)))
          (.jmp .head (.cons (♯0) .nil)))) u :=
  ⟨_, .blockStep .labelLoop⟩

/-- **A shared tail that continues an enclosing loop runs too.**  `Term.sharedTailInLoop`
    is the program the two-construct grammar could not express: a label bound inside a
    loop's body whose block jumps back to the loop.  Its block steps, by substituting the
    loop for its own label. -/
example :
    ∃ u : Term sigNone [Ty.nat] Ty.nat,
      Step (Sg := sigNone) (Γ := [Ty.nat]) Term.sharedTailInLoop u :=
  ⟨_, .blockStep .labelLoop⟩

/-- A function of the runtime that is still waiting for an argument is an answer: only a
    *saturated* application is a δ-redex. -/
example : ¬ DeltaRedex (Sg := sigNone) (Γ := [])
    (.extern (.prim2 .lean_nat_add)) := by
  intro h; cases h

end Examples

end LakeJs.Expr

end
