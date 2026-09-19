module

public import LakeJs.Expr
public import LakeJs.ExternDen
public import LakeJs.Lex

@[expose] public section

set_option autoImplicit false

/-!
# The evaluator: what a `Term` *means*, and why running one stops

This module is the semantics of `LakeJs.Expr`, and nothing else.  There is no optimiser
here: a `Term` is the language the front end produces, and what this file says is how one
**runs**.

The semantics is **denotational**: a term of type `τ` evaluates to an inhabitant of the
Lean type `Ty.den τ` (`LakeJs.Den`).

```
Term.eval : Term Sg Γ Ρ τ → GEnv Sg.decls → Env Γ → REnv Ρ → τ.den
```

and, for a closed term,

```
Term.evalClosed (t : Term Sg [] [] τ) : τ.den
```

* it takes **no fuel**;
* it answers in `τ.den`, not in `Option` or an error monad — it never gets stuck, so
  there is no progress theorem to prove and no neutral term to characterise;
* it is neither `partial` nor `unsafe`, and it uses no `sorry` and no extra axiom.

That is the totality obligation of the plan, discharged **by construction**: the Lean
kernel accepts `Term.eval` only because the definition is a structural recursion on the
term, so the fact that running a term stops is the fact that the definition elaborates.
A pleasant consequence is that terms also reduce *in the kernel*, so a check of what a
term computes is `by rfl`.

## How the object language's recursion is run, and why it stops

`Term.fix ps k measure body stuck` evaluates to the curried function that

1. evaluates `measure` in the environment of its own arguments, giving a `Lex.NatVec k` —
   the **bound** this activation runs under;
2. runs `body` with a self-reference which, at a call with arguments `bs`, evaluates the
   measure again and
   * recurses with the new value as the bound, if it is lexicographically **strictly
     smaller** than the current one,
   * and answers `stuck` if it is not.

That is `LakeJs.Lex.guardedFix`, and it terminates because the bound only ever descends in
a well-founded order.  It is *not* run by `WellFounded.fix`: `LakeJs.Lex.LexRun` is built
from `Nat.rec` and structural recursion on the number of components, so the kernel
computes it and a check of what a term evaluates to is still `by rfl`.

A `Term.selfCall` inside `body` can invoke nothing but that self-reference: the recursion
environment holds a plain Lean function `Env ps → τ.den`, so the bound is not a value the
term can see, name, replace or raise.  This is the sealed measure of the plan — and,
unlike a counted rank, a *wrong* measure cannot make the term compute a wrong function: it
can only make a call answer `stuck`, which is observable.

A tail recursion and a non-tail recursion are the same construct here: `body` may call
`selfCall` in any position, because the self entry is an ordinary Lean function.

## Where the old small-step semantics went

The previous version of this module was a call-by-value small-step relation (`Step`,
`StepT`) whose central rule was β, together with a `Value`/`Neutral` characterisation, a
progress theorem, a logical relation and a strong-normalisation proof for a *certified*
fragment of the grammar — because the grammar of the time had a loop, and a loop can
diverge.  The grammar has no loop any more (`Tail.join` cannot jump back to itself, and
`Term.fix` carries its measure), so none of that machinery is needed: an ordinary Lean
function is the evaluator, and its existence is the normalisation theorem.  See
`LakeJs.Totality` for the statements, and `LakeJs.CertGen` for what became of the
certificates.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty
open LakeJs.Layout (FieldLayout)

/-! ## Environments -/

/-- A runtime environment: one value per entry of the variable context. -/
inductive Env : Ctx → Type where
  /-- The empty environment. -/
  | nil : Env []
  /-- One more value. -/
  | cons : ∀ {τ Γ}, τ.den → Env Γ → Env (τ :: Γ)

/-- Look a variable up in an environment. -/
def Env.get : ∀ {Γ : Ctx} {τ : Ty}, Env Γ → Γ ∋ τ → τ.den
  | _, _, .cons v _, .head => v
  | _, _, .cons _ e, .tail x => e.get x

/-- Concatenate environments, matching `List.append` on their contexts. -/
def Env.append : ∀ {Γ Δ : Ctx}, Env Γ → Env Δ → Env (Γ ++ Δ)
  | [], _, .nil, e => e
  | _ :: _, _, .cons v vs, e => .cons v (vs.append e)

/-- The environment that gives every entry of `Γ` its canonical inhabitant. -/
def Env.dflt : (Γ : Ctx) → Env Γ
  | [] => .nil
  | τ :: Γ => .cons τ.dflt (Env.dflt Γ)

/-- Read an environment out of a list of runtime trees, using the canonical inhabitant
    where the list is too short.  This is how an alternative of a `case` binds the fields
    of the constructor it matched. -/
def Env.ofData : (Γ : Ctx) → List Data → Env Γ
  | [], _ => .nil
  | τ :: Γ, [] => .cons τ.dflt (Env.ofData Γ [])
  | τ :: Γ, d :: ds => .cons (τ.ofData d) (Env.ofData Γ ds)

/-- Write an environment out as a list of runtime trees: the fields of a constructor. -/
def Env.toData : ∀ {Γ : Ctx}, Env Γ → List Data
  | [], _ => []
  | _ :: _, .cons v vs => Ty.toData _ v :: vs.toData

/-- Turn a function of an environment into a curried function of its values. -/
def Env.curry {τ : Ty} : (ps : Ctx) → (Env ps → τ.den) → (Ty.arrows ps τ).den
  | [], f => f .nil
  | _ :: ps, f => fun a => Env.curry ps (fun args => f (.cons a args))

/-- Apply a curried function to an environment of arguments. -/
def Env.apply {τ : Ty} : ∀ {ps : Ctx}, (Ty.arrows ps τ).den → Env ps → τ.den
  | [], f, .nil => f
  | _ :: _, f, .cons a args => Env.apply (f a) args

/-- `Env.curry` and `Env.apply` are inverse: currying loses nothing. -/
theorem Env.apply_curry {τ : Ty} : ∀ {ps : Ctx} (f : Env ps → τ.den) (args : Env ps),
    Env.apply (Env.curry ps f) args = f args
  | [], _, .nil => rfl
  | _ :: _, f, .cons a args => Env.apply_curry (fun rest => f (.cons a rest)) args

/-- The values of the module's top-level declarations. -/
inductive GEnv : List GlobalDecl → Type where
  /-- No declarations. -/
  | nil : GEnv []
  /-- One more declaration, with its value. -/
  | cons : ∀ {g : GlobalDecl} {ds : List GlobalDecl}, g.ty.den → GEnv ds → GEnv (g :: ds)

/-- Look a global up. -/
def GEnv.get : ∀ {ds : List GlobalDecl} {τ : Ty}, GEnv ds → GlobalRef ds τ → τ.den
  | _, _, .cons v _, .here => v
  | _, _, .cons _ e, .there x => e.get x

/-- The meanings of the join points in scope: each is a function of its arguments
    answering the type the block answers with. -/
inductive LEnv (τ : Ty) : LCtx → Type where
  /-- No join points. -/
  | nil : LEnv τ []
  /-- One more join point. -/
  | cons : ∀ {ps Ω}, (Env ps → τ.den) → LEnv τ Ω → LEnv τ (ps :: Ω)

/-- Look up a join point. -/
def LEnv.get : ∀ {τ : Ty} {Ω : LCtx} {ps : List Ty}, LEnv τ Ω → Ω ∋ₗ ps →
    (Env ps → τ.den)
  | _, _, _, .cons f _, .head => f
  | _, _, _, .cons _ e, .tail x => e.get x

/-- The meanings of the recursions in scope.  An entry is a plain Lean function,
    so a term can call it and can do nothing else with it — in particular it cannot
    inspect the measure that produced it, or ask for another one. -/
inductive REnv : RCtx → Type where
  /-- No recursions. -/
  | nil : REnv []
  /-- One more recursion. -/
  | cons : ∀ {r : RSig} {Ρ}, (Env r.ps → r.ret.den) → REnv Ρ → REnv (r :: Ρ)

/-- Look up a recursion. -/
def REnv.get : ∀ {Ρ : RCtx} {r : RSig}, REnv Ρ → Ρ ∋ᵣ r → (Env r.ps → r.ret.den)
  | _, _, .cons f _, .head => f
  | _, _, .cons _ e, .tail x => e.get x

/-- Read the value of a `k`-component measure out of the environment its spine evaluates
    to: a `LakeJs.Lex.NatVec`, which is what the guard compares. -/
def Env.toNatVec : (k : Nat) → Env (Ty.nats k) → Lex.NatVec k
  | 0, _ => .nil
  | k + 1, .cons a as => .cons (show Nat from a) (Env.toNatVec k as)

/-! ## The evaluator -/

mutual

/-- Evaluate a term in an environment of globals, locals and recursions. -/
def Term.eval {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {τ : Ty} (t : Term Sg Γ Ρ τ)
    (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ) : τ.den :=
  match t with
  | .var x => γ.get x
  | .lam b => fun a => b.eval δ (.cons a γ) ρ
  | .ap f a => (f.eval δ γ ρ) (a.eval δ γ ρ)
  | .lit l => l.val
  | .global r => δ.get r
  | .extern e => e.den
  | .lazyMk e => fun _ => e.eval δ γ ρ
  | .lazyForce e => (e.eval δ γ ρ) ()
  | .letE e b => b.eval δ (.cons (e.eval δ γ ρ) γ) ρ
  | .ite c a b => if cond (c.eval δ γ ρ) true false then a.eval δ γ ρ else b.eval δ γ ρ
  | .ctor (τ := σ) i _ _ s => σ.buildVal i (s.eval δ γ ρ).toData
  | .proj (σ := σ) (τ := τ') e _ j _ _ =>
      τ'.ofData ((σ.fieldsOfVal (e.eval δ γ ρ)).getD j .opaque)
  | .tagOf (σ := σ) e _ => σ.tagOfVal (e.eval δ γ ρ)
  | .structSize (σ := σ) e => Data.size (σ.toData (e.eval δ γ ρ))
  | .caseTag (σ := σ) (τ := τ') scrut alts _ =>
      let v := scrut.eval δ γ ρ
      match alts.eval (σ.tagOfVal v) (σ.fieldsOfVal v) δ γ ρ with
      | some r => r
      | none => τ'.dflt
  | .block b => b.eval δ γ .nil ρ
  | .fix ps k measure body stuck =>
      Env.curry ps fun args =>
        Lex.guardedFix
          (fun as => Env.toNatVec k (measure.eval δ (as.append γ) ρ))
          (fun as => stuck.eval δ (as.append γ) ρ)
          (fun g as => body.eval δ (as.append γ) (.cons g ρ))
          args
  | .selfCall r s => ρ.get r (s.eval δ γ ρ)

/-- Evaluate a spine of arguments into an environment. -/
def Spine.eval {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {σs : List Ty} (s : Spine Sg Γ Ρ σs)
    (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ) : Env σs :=
  match s with
  | .nil => .nil
  | .cons a rest => .cons (a.eval δ γ ρ) (rest.eval δ γ ρ)

/-- Find the branch for a tag and run it with the constructor's fields bound.  `none`
    means the dispatch has no branch for that tag, which the grammar rules out: a
    dispatch either has a default branch or is exhaustive. -/
def Alts.eval {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {σ τ : Ty} {tags : List Nat} {full : Bool}
    (alts : Alts Sg Γ Ρ σ τ tags full) (tag : Nat) (fs : List Data)
    (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ) : Option τ.den :=
  match alts with
  | .deflt e => some (e.eval δ γ ρ)
  | .nilFull => none
  | .cons t fields _ body rest =>
      if t = tag then some (body.eval δ ((Env.ofData fields fs).append γ) ρ)
      else rest.eval tag fs δ γ ρ

/-- Evaluate a block. -/
def Tail.eval {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {τ : Ty} (b : Tail Sg Γ Ω Ρ τ)
    (δ : GEnv Sg.decls) (γ : Env Γ) (lenv : LEnv τ Ω) (ρ : REnv Ρ) : τ.den :=
  match b with
  | .ret e => e.eval δ γ ρ
  | .jmp l s => lenv.get l (s.eval δ γ ρ)
  | .letT e rest => rest.eval δ (.cons (e.eval δ γ ρ) γ) lenv ρ
  | .iteT c t e =>
      if cond (c.eval δ γ ρ) true false then t.eval δ γ lenv ρ else e.eval δ γ lenv ρ
  | .caseT (σ := σ) scrut alts _ =>
      let v := scrut.eval δ γ ρ
      match alts.eval (σ.tagOfVal v) (σ.fieldsOfVal v) δ γ lenv ρ with
      | some r => r
      | none => τ.dflt
  | .join ps body rest =>
      rest.eval δ γ
        (.cons (fun (args : Env ps) => body.eval δ (args.append γ) lenv ρ) lenv) ρ

/-- Find the branch for a tag in tail position. -/
def AltsT.eval {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {σ τ : Ty} {tags : List Nat}
    {full : Bool} (alts : AltsT Sg Γ Ω Ρ σ τ tags full) (tag : Nat) (fs : List Data)
    (δ : GEnv Sg.decls) (γ : Env Γ) (lenv : LEnv τ Ω) (ρ : REnv Ρ) : Option τ.den :=
  match alts with
  | .deflt b => some (b.eval δ γ lenv ρ)
  | .nilFull => none
  | .cons t fields _ body rest =>
      if t = tag then
        some (body.eval δ ((Env.ofData fields fs).append γ) lenv ρ)
      else rest.eval tag fs δ γ lenv ρ

end

/-- **The value of a measure** at an argument list: the spine evaluated, read as a
    lexicographic vector.  This is the only thing the guard compares. -/
def Term.measureVal {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {ps : List Ty} {k : Nat}
    (measure : Spine Sg (ps ++ Γ) Ρ (Ty.nats k))
    (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ) (as : Env ps) : Lex.NatVec k :=
  Env.toNatVec k (measure.eval δ (as.append γ) ρ)

/-- **The meaning of a recursion**, as a function of its arguments: the body run with a
    self-reference that answers the recursion at `bs` when the measure of `bs` is
    lexicographically smaller than the measure of the arguments of the activation the call
    is made from, and `stuck` when it is not.  This is exactly what `Term.eval` does in the
    `fix` case (`Term.eval_fix` below is `rfl`). -/
def Term.fixFun {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {ps : List Ty} {τ : Ty} {k : Nat}
    (measure : Spine Sg (ps ++ Γ) Ρ (Ty.nats k))
    (body : Term Sg (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ)
    (stuck : Term Sg (ps ++ Γ) Ρ τ)
    (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ) : Env ps → τ.den :=
  Lex.guardedFix (Term.measureVal measure δ γ ρ)
    (fun as => stuck.eval δ (as.append γ) ρ)
    (fun g as => body.eval δ (as.append γ) (.cons g ρ))

/-- Run a closed term.  No fuel, no `Option`: the answer is a Lean value. -/
def Term.evalClosed {Sg : Sig} {τ : Ty} (t : Term Sg [] [] τ) (δ : GEnv Sg.decls) : τ.den :=
  t.eval δ .nil .nil

/-- Run a term of a module with no declarations. -/
def Term.run {τ : Ty} (t : Term ⟨[], by decide⟩ [] [] τ) : τ.den :=
  t.eval .nil .nil .nil

/-! ### Running a closed term at a concrete type

`Ty.den` is a function, so Lean's elaborator will not look through it when it searches
for a numeral's `OfNat` instance.  These wrappers do the looking: each is the identity,
and each states the concrete Lean type of the answer. -/

/-- Run a closed unary function on `Nat`s. -/
def Term.runNat1 (t : Term ⟨[], by decide⟩ [] [] (.nat ⇒ .nat)) (n : Nat) : Nat :=
  t.run n

/-- Run a closed binary function on `Nat`s. -/
def Term.runNat2 (t : Term ⟨[], by decide⟩ [] [] (.nat ⇒ .nat ⇒ .nat)) (m n : Nat) :
    Nat := t.run m n

/-- Run a closed predicate on `Nat`s. -/
def Term.runNatBool (t : Term ⟨[], by decide⟩ [] [] (.nat ⇒ .bool)) (n : Nat) : Bool :=
  t.run n

/-- Run a closed unary function on `Int`s. -/
def Term.runInt1 (t : Term ⟨[], by decide⟩ [] [] (.int ⇒ .int)) (i : Int) : Int :=
  t.run i

/-! ## The equations of the recursion, as propositions -/

section Equations

variable {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {ps : List Ty} {τ : Ty}

variable {k : Nat}

@[simp] theorem Term.eval_fix (measure : Spine Sg (ps ++ Γ) Ρ (Ty.nats k))
    (body : Term Sg (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ) (stuck : Term Sg (ps ++ Γ) Ρ τ)
    (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ) :
    (Term.fix ps k measure body stuck).eval δ γ ρ =
      Env.curry ps (Term.fixFun measure body stuck δ γ ρ) := rfl

/-- Applying a recursion to a full argument list. -/
theorem Term.apply_eval_fix (measure : Spine Sg (ps ++ Γ) Ρ (Ty.nats k))
    (body : Term Sg (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ) (stuck : Term Sg (ps ++ Γ) Ρ τ)
    (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ) (args : Env ps) :
    Env.apply ((Term.fix ps k measure body stuck).eval δ γ ρ) args =
      Term.fixFun measure body stuck δ γ ρ args := by
  rw [Term.eval_fix, Env.apply_curry]

/-- **One unrolling.**  The recursion runs its body once, with a self-reference that is
    the recursion itself at every *strictly smaller* measure and `stuck` everywhere else.
    This is the equation every faithfulness proof uses, and the only one there is: no fuel
    and no iteration count occurs in it. -/
theorem Term.fixFun_unfold (measure : Spine Sg (ps ++ Γ) Ρ (Ty.nats k))
    (body : Term Sg (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ) (stuck : Term Sg (ps ++ Γ) Ρ τ)
    (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ) (args : Env ps) :
    Term.fixFun measure body stuck δ γ ρ args =
      body.eval δ (args.append γ)
        (.cons (fun bs =>
            if (Term.measureVal measure δ γ ρ bs).lt (Term.measureVal measure δ γ ρ args)
            then Term.fixFun measure body stuck δ γ ρ bs
            else stuck.eval δ (bs.append γ) ρ) ρ) :=
  Lex.guardedFix_unfold _ _ _ args

/-- **A self call that does not descend answers `stuck`.**  This is the failure mode of a
    mistranslated measure: an observable value, not a wrong one and not a hang. -/
theorem Term.fixFun_stuck_of_not_lt (measure : Spine Sg (ps ++ Γ) Ρ (Ty.nats k))
    (body : Term Sg (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ) (stuck : Term Sg (ps ++ Γ) Ρ τ)
    (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ) (args bs : Env ps)
    (h : ¬ Lex.NatVec.Lt (Term.measureVal measure δ γ ρ bs)
            (Term.measureVal measure δ γ ρ args)) :
    (if (Term.measureVal measure δ γ ρ bs).lt (Term.measureVal measure δ γ ρ args)
     then Term.fixFun measure body stuck δ γ ρ bs
     else stuck.eval δ (bs.append γ) ρ) = stuck.eval δ (bs.append γ) ρ := by
  rw [(Lex.NatVec.lt_eq_false_iff _ _).mpr h]
  rfl

end Equations

end LakeJs.Expr

end
