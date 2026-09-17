module

public import LakeJs.Usage

@[expose] public section

/-!
# Building a term that cannot bind a name for nothing

`LakeJs/Usage.lean` states the discipline — a variable a function binds is read, a `let`
shares its value with two readers or keeps work out of a binder, a join point is jumped
to and never named as a value — and proves that the check refuses each violation.  This
file is the other half: an **interface for building terms in which a violation cannot be
written down**.

`WfTermAt Sg Γ m τ` is a term together with the proof that it passes the check, with `m`
the mask saying which variables of `Γ` are join points, and `WfTerm Sg Γ τ` is the case
of a context with no join point in it — the type a whole declaration has.  Every
constructor of `Term` has a counterpart here, and the counterparts of the *binders* ask
for the discipline as an argument:

| builder | what it asks for |
| :-- | :-- |
| `WfTermAt.lamN` | `Usage.paramsUsed ps.length b`: the body reads every parameter |
| `WfTermAt.lamProd` | the same, of a body that is a spine |
| `WfTermAt.letE` | `Usage.sharesOk (occ 0 b) (occUnder 0 b)`: two readers, or one under a binder |
| `WfTermAt.loop` | `Usage.paramsUsedBody σs.length body`: every slot is read |
| `WfTermAt.joinPoint` | the body reads every parameter, and the rest jumps to it |
| `WfTermAt.jump` | the target is a join point of the context |
| `WfTermAt.var` | the variable is **not** a join point |

Each condition is a decidable `Bool`, so it is written `by decide` at a closed term and
discharged from the context otherwise; it is never a proof obligation about the
*meaning* of the term, only about its shape.  Nothing else is needed: the remaining
builders (`apN`, `ite`, `ctor`, …) take well-formed parts and answer with a well-formed
whole, because `Term.usesOk` at those nodes is exactly the conjunction over the parts.

So `Term.const = ƛ ƛ ♯1` — the function that ignores its parameter, which
`Usage.Term.not_usesOk_lamN_of_unusedParam` refuses — has no counterpart here: the
argument `WfTermAt.lamN` asks for is `false`, and there is nothing to pass.  The examples
at the end of the file pin that down.
-/

namespace LakeJs.Usage

open LakeJs
open LakeJs.Ty
open LakeJs.Expr

/-! ## The four subtypes -/

/-- A term that passes the usage discipline, against the mask `m` of the join points of
    its context. -/
def WfTermAt (Sg : Sig) (Γ : Ctx) (m : JMask) (τ : Ty) : Type :=
  { t : Term Sg Γ τ // Term.usesOk m t = true }

/-- A spine all of whose terms pass the discipline. -/
def WfSpineAt (Sg : Sig) (Γ : Ctx) (m : JMask) (σs : List Ty) : Type :=
  { s : Spine Sg Γ σs // Spine.usesOk m s = true }

/-- Branches of a case all of which pass the discipline. -/
def WfAltsAt (Sg : Sig) (Γ : Ctx) (m : JMask) (τ : Ty) (tags : List Nat) : Type :=
  { a : Alts Sg Γ τ tags // Alts.usesOk m a = true }

/-- A loop block that passes the discipline. -/
def WfBodyAt (Sg : Sig) (Γ : Ctx) (m : JMask) (σs : List Ty) (τ : Ty) : Type :=
  { b : Body Sg Γ σs τ // Body.usesOk m b = true }

namespace WfTermAt

variable {Sg : Sig} {Γ : Ctx} {m : JMask}

/-! ## The leaves -/

/-- A variable — which may not be a join point: naming one is the one thing a join point
    is never allowed to do. -/
def var {τ : Ty} (v : Γ ∋ τ) (h : m.isJoin v.index = false := by decide) :
    WfTermAt Sg Γ m τ :=
  ⟨.var v, by simp [Term.usesOk, h]⟩

/-- A literal. -/
def lit {p : LeanPrimTy} (l : Lit p) : WfTermAt Sg Γ m (.prim p) :=
  ⟨.lit l, rfl⟩

/-- A reference to a declaration of the module's signature. -/
def global {τ : Ty} (r : GlobalRef Sg τ) : WfTermAt Sg Γ m τ :=
  ⟨.global r, rfl⟩

/-- A function the runtime implements. -/
def extern {σs : List Ty} {τ : Ty} (e : Externs σs τ) : WfTermAt Sg Γ m (.fn σs τ) :=
  ⟨.extern e, rfl⟩

/-! ## The binders, each with its condition -/

/-- A lambda **whose body reads every parameter**.  This is the builder that makes a
    function ignoring an argument unwritable. -/
def lamN {ps : List Ty} {ret : Ty}
    (b : WfTermAt Sg (ps.reverse ++ Γ) (JMask.pushPlain ps.length m) ret)
    (h : paramsUsed ps.length b.1 = true := by decide) :
    WfTermAt Sg Γ m (.fn ps ret) :=
  ⟨.lamN b.1, by simp [Term.usesOk, h, b.2]⟩

/-- A lambda answering with several values at once, whose body reads every parameter. -/
def lamProd {ps : List Ty} {r1 : Ty} {rs : List Ty}
    (rets : WfSpineAt Sg (ps.reverse ++ Γ) (JMask.pushPlain ps.length m) (r1 :: rs))
    (h : paramsUsedSpine ps.length rets.1 = true := by decide) :
    WfTermAt Sg Γ m (.fn_returnsProd ps r1 rs) :=
  ⟨.lamProd rets.1, by simp [Term.usesOk, h, rets.2]⟩

/-- A `let` **that shares something**: its variable is read twice or more, or its single
    reader sits under a binder, where the binding is what keeps the work out. -/
def letE {σ τ : Ty} (e : WfTermAt Sg Γ m σ) (b : WfTermAt Sg (σ :: Γ) (false :: m) τ)
    (h : sharesOk (Term.occ 0 b.1) (Term.occUnder 0 b.1) = true := by decide) :
    WfTermAt Sg Γ m τ :=
  ⟨.letE e.1 b.1, by simp [Term.usesOk, h, e.2, b.2]⟩

/-- A loop **every slot of which the block reads** — the value a jump hands a slot not
    counting as a read of it, since that value goes when the slot goes. -/
def loop {σs : List Ty} {τ : Ty} (init : WfSpineAt Sg Γ m σs)
    (body : WfBodyAt Sg (σs.reverse ++ Γ) (JMask.pushPlain σs.length m) σs τ)
    (h : paramsUsedBody σs.length body.1 = true := by decide) :
    WfTermAt Sg Γ m τ :=
  ⟨.loop init.1 body.1, by simp [Term.usesOk, h, init.2, body.2]⟩

/-- A join point: its body reads every parameter, and the rest of the term **jumps to
    it** at least once.  That the name is never used as a value is not a condition here
    — it is `WfTermAt.var`, which refuses a join point, and `WfTermAt.jump`, which is the
    only builder that names one. -/
def joinPoint {ps : List Ty} {σ τ : Ty}
    (body : WfTermAt Sg (ps.reverse ++ Γ) (JMask.pushPlain ps.length m) σ)
    (rest : WfTermAt Sg (.fn ps σ :: Γ) (true :: m) τ)
    (hp : paramsUsed ps.length body.1 = true := by decide)
    (hj : 1 ≤ Term.occ 0 rest.1 := by decide) :
    WfTermAt Sg Γ m τ :=
  ⟨.joinPoint body.1 rest.1, by simp [Term.usesOk, hp, hj, body.2, rest.2]⟩

/-- A jump — **to a join point**, which is what the mask says. -/
def jump {ps : List Ty} {σ : Ty} (v : Γ ∋ (.fn ps σ)) (args : WfSpineAt Sg Γ m ps)
    (h : m.isJoin v.index = true := by decide) : WfTermAt Sg Γ m σ :=
  ⟨.jump v args.1, by simp [Term.usesOk, h, args.2]⟩

/-! ## The nodes that bind nothing

At these the discipline is the conjunction over the parts, so there is no condition to
ask for: well-formed parts make a well-formed whole. -/

/-- An application. -/
def apN {ps : List Ty} {ret : Ty} (f : WfTermAt Sg Γ m (.fn ps ret))
    (args : WfSpineAt Sg Γ m ps) : WfTermAt Sg Γ m ret :=
  ⟨.apN f.1 args.1, by simp [Term.usesOk, f.2, args.2]⟩

/-- A call of a function answering with several values at once. -/
def callProd {ps : List Ty} {r1 : Ty} {rs : List Ty}
    (f : WfTermAt Sg Γ m (.fn_returnsProd ps r1 rs)) (args : WfSpineAt Sg Γ m ps)
    (i : Fin (rs.length + 1)) : WfTermAt Sg Γ m ((r1 :: rs).get i) :=
  ⟨.callProd f.1 args.1 i, by simp [Term.usesOk, f.2, args.2]⟩

/-- An operation that is JavaScript's rather than Lean's. -/
def jsOp {σs : List Ty} {τ : Ty} (op : JsOp σs τ) (args : WfSpineAt Sg Γ m σs) :
    WfTermAt Sg Γ m τ :=
  ⟨.jsOp op args.1, by simp [Term.usesOk, args.2]⟩

/-- Delay a value. -/
def lazyMk {τ : Ty} (e : WfTermAt Sg Γ m τ) : WfTermAt Sg Γ m (.lazy τ) :=
  ⟨.lazyMk e.1, by simp [Term.usesOk, e.2]⟩

/-- Run a delayed value. -/
def lazyForce {τ : Ty} (e : WfTermAt Sg Γ m (.lazy τ)) : WfTermAt Sg Γ m τ :=
  ⟨.lazyForce e.1, by simp [Term.usesOk, e.2]⟩

/-- A conditional. -/
def ite {τ : Ty} (c : WfTermAt Sg Γ m (.prim .bool)) (t u : WfTermAt Sg Γ m τ) :
    WfTermAt Sg Γ m τ :=
  ⟨.ite c.1 t.1 u.1, by simp [Term.usesOk, c.2, t.2, u.2]⟩

/-- A tagged value. -/
def ctor {τ : Ty} (i : Nat) (fields : Layout.FieldLayout)
    (h : τ.ctorFields? i = some fields) (args : WfSpineAt Sg Γ m fields) :
    WfTermAt Sg Γ m τ :=
  ⟨.ctor i fields h args.1, by simp [Term.usesOk, args.2]⟩

/-- A field of a tagged value. -/
def proj {σ τ : Ty} (e : WfTermAt Sg Γ m σ) (i j : Nat) (h : σ.fieldTy? i j = some τ) :
    WfTermAt Sg Γ m τ :=
  ⟨.proj e.1 i j h, by simp [Term.usesOk, e.2]⟩

/-- The runtime tag of a value. -/
def tagOf {σ : Ty} (e : WfTermAt Sg Γ m σ) (h : σ.isTagged = true) :
    WfTermAt Sg Γ m (.prim .nat) :=
  ⟨.tagOf e.1 h, by simp [Term.usesOk, e.2]⟩

/-- A dispatch on the tag of a value. -/
def caseTag {σ τ : Ty} {tags : List Nat} (s : WfTermAt Sg Γ m σ)
    (alts : WfAltsAt Sg Γ m τ tags) (h : σ.caseOk tags = true) : WfTermAt Sg Γ m τ :=
  ⟨.caseTag s.1 alts.1 h, by simp [Term.usesOk, s.2, alts.2]⟩

end WfTermAt

namespace WfSpineAt

variable {Sg : Sig} {Γ : Ctx} {m : JMask}

/-- The empty spine. -/
def nil : WfSpineAt Sg Γ m [] := ⟨.nil, rfl⟩

/-- One more argument. -/
def cons {σ : Ty} {σs : List Ty} (t : WfTermAt Sg Γ m σ) (rest : WfSpineAt Sg Γ m σs) :
    WfSpineAt Sg Γ m (σ :: σs) :=
  ⟨.cons t.1 rest.1, by simp [Spine.usesOk, t.2, rest.2]⟩

end WfSpineAt

namespace WfAltsAt

variable {Sg : Sig} {Γ : Ctx} {m : JMask}

/-- The default branch, which every case has. -/
def deflt {τ : Ty} (t : WfTermAt Sg Γ m τ) : WfAltsAt Sg Γ m τ [] :=
  ⟨.deflt t.1, by simp [Alts.usesOk, t.2]⟩

/-- One more branch, keyed by a tag. -/
def cons {τ : Ty} {tags : List Nat} (tag : Nat) (t : WfTermAt Sg Γ m τ)
    (rest : WfAltsAt Sg Γ m τ tags) : WfAltsAt Sg Γ m τ (tag :: tags) :=
  ⟨.cons tag t.1 rest.1, by simp [Alts.usesOk, t.2, rest.2]⟩

end WfAltsAt

namespace WfBodyAt

variable {Sg : Sig} {Γ : Ctx} {m : JMask}

/-- Leave the loop with this value. -/
def ret {σs : List Ty} {τ : Ty} (t : WfTermAt Sg Γ m τ) : WfBodyAt Sg Γ m σs τ :=
  ⟨.ret t.1, by simp [Body.usesOk, t.2]⟩

/-- Go round the loop again. -/
def cont {σs : List Ty} {τ : Ty} (args : WfSpineAt Sg Γ m σs) : WfBodyAt Sg Γ m σs τ :=
  ⟨.cont args.1, by simp [Body.usesOk, args.2]⟩

/-- A `let` of a block, under the same sharing condition as `WfTermAt.letE`. -/
def letB {σ : Ty} {σs : List Ty} {τ : Ty} (e : WfTermAt Sg Γ m σ)
    (b : WfBodyAt Sg (σ :: Γ) (false :: m) σs τ)
    (h : sharesOk (Body.occ 0 b.1) (Body.occUnder 0 b.1) = true := by decide) :
    WfBodyAt Sg Γ m σs τ :=
  ⟨.letB e.1 b.1, by simp [Body.usesOk, h, e.2, b.2]⟩

/-- A conditional whose arms are blocks. -/
def iteB {σs : List Ty} {τ : Ty} (c : WfTermAt Sg Γ m (.prim .bool))
    (t u : WfBodyAt Sg Γ m σs τ) : WfBodyAt Sg Γ m σs τ :=
  ⟨.iteB c.1 t.1 u.1, by simp [Body.usesOk, c.2, t.2, u.2]⟩

/-- A join point of a loop block, under the same conditions as `WfTermAt.joinPoint`. -/
def joinPointB {ps : List Ty} {σ : Ty} {σs : List Ty} {τ : Ty}
    (body : WfTermAt Sg (ps.reverse ++ Γ) (JMask.pushPlain ps.length m) σ)
    (rest : WfBodyAt Sg (.fn ps σ :: Γ) (true :: m) σs τ)
    (hp : paramsUsed ps.length body.1 = true := by decide)
    (hj : 1 ≤ Body.occ 0 rest.1 := by decide) :
    WfBodyAt Sg Γ m σs τ :=
  ⟨.joinPointB body.1 rest.1, by simp [Body.usesOk, hp, hj, body.2, rest.2]⟩

end WfBodyAt

/-! ## A whole declaration

A declaration is written in a context with no join point in it, so its mask is all
`false`. -/

/-- The mask of a context none of whose variables is a join point. -/
def plainMask (Γ : Ctx) : JMask := List.replicate Γ.length false

/-- A closed, well-formed term of a declaration. -/
def WfTermIn (Sg : Sig) (Γ : Ctx) (τ : Ty) : Type := WfTermAt Sg Γ (plainMask Γ) τ

/-- What was built through the interface is a term the check accepts — the two
    statements of the discipline agree. -/
theorem WfTermIn.usesOk {Sg : Sig} {Γ : Ctx} {τ : Ty} (t : WfTermIn Sg Γ τ) :
    Term.usesOk (List.replicate Γ.length false) t.1 = true := t.2

/-! ## Examples: what can be built, and what cannot

The identity function is built; the constant function is not, because the argument its
builder asks for is `false`. -/

/-- `(v0) => v0`, built through the interface. -/
def idWf : WfTermIn [] [] (Ty.nat ⇒ Ty.nat) :=
  WfTermAt.lamN (ps := [Ty.nat]) (WfTermAt.var .head rfl) rfl

example : idWf.1 = Term.id := rfl

/-- **The constant function cannot be built**: `WfTermAt.lamN` asks for
    `paramsUsed 1 ♯1`, and that is `false`, so there is no such argument to give. -/
example :
    paramsUsed (Sg := []) (Γ := [Ty.nat].reverse ++ [Ty.nat])
      1 (♯1 : Term [] _ Ty.nat) = false := rfl

/-- The join point of `LakeJs.Usage.joinExample`, built through the interface: the
    conditions — the body reads its parameter, and the rest jumps to it — are discharged
    by `decide`, and the term is the one written by hand. -/
def joinWf : WfTermIn [] [] Ty.nat :=
  WfTermAt.joinPoint (ps := [Ty.nat]) (σ := Ty.nat)
    (WfTermAt.apN (WfTermAt.extern .lean_nat_add)
      (WfSpineAt.cons (WfTermAt.var .head) (WfSpineAt.cons (WfTermAt.var .head)
        WfSpineAt.nil)))
    (WfTermAt.ite (WfTermAt.lit (.bool true))
      (WfTermAt.jump .head (WfSpineAt.cons (WfTermAt.lit (.nat 1)) WfSpineAt.nil))
      (WfTermAt.jump .head (WfSpineAt.cons (WfTermAt.lit (.nat 2)) WfSpineAt.nil)))

example : joinWf.1 = joinExample := rfl

/-- **A join point that nothing jumps to cannot be built**: the condition
    `1 ≤ Term.occ 0 rest` fails, as `Usage.Term.not_usesOk_joinPoint_of_noJump` says it
    must. -/
example : ¬ (1 ≤ Term.occ (Sg := []) (Γ := [Ty.fn [Ty.nat] Ty.nat]) 0
    (.lit (.nat 0) : Term [] _ Ty.nat)) := by decide

/-- **A join point named as a value cannot be built**: `WfTermAt.var` asks that the
    variable is not a join point, and under the mask a join point put there it is. -/
example : JMask.isJoin (true :: []) 0 = true := rfl

/-- A `let` read twice is built; one read once, out in the open, is not. -/
def sharedLetWf : WfTermIn [] [] Ty.nat :=
  WfTermAt.letE (WfTermAt.lit (.nat 2))
    (WfTermAt.apN (WfTermAt.extern .lean_nat_add)
      (WfSpineAt.cons (WfTermAt.var .head)
        (WfSpineAt.cons (WfTermAt.var .head) WfSpineAt.nil)))

example : Term.usesOkDecl sharedLetWf.1 = true := by decide +kernel

/-- The same `let` with a single reader: the condition `WfTermAt.letE` asks for is
    `false`, so the term is unwritable through the interface — and `LakeJs.LinearLet` is
    the pass that turns such a binding into the term that *is* writable. -/
example :
    sharesOk (Term.occ (Sg := []) (Γ := [Ty.nat]) 0 (♯0 : Term [] [Ty.nat] Ty.nat))
      (Term.occUnder 0 (♯0 : Term [] [Ty.nat] Ty.nat)) = false := rfl

/-! ## What the interface guarantees against the compiler's own check

`LakeJs.Compile` refuses a declaration whose term has a `Term.declIssues` to report.
The theorem below is that a term the discipline accepts has none, so a term built
through this interface is one the compiler cannot refuse. -/

/-- A binder all of whose variables are read has no unread one to report. -/
theorem unreadParams_eq_nil {Sg : Sig} {Γ : Ctx} {τ : Ty} {n : Nat} {b : Term Sg Γ τ}
    (h : paramsUsed n b = true) : unreadParams n b = [] := by
  simp [paramsUsed] at h
  simp [unreadParams, List.filter_eq_nil_iff]
  intro k hk
  exact h k hk

/-- The same, for a loop whose every slot is read. -/
theorem unreadParamsBody_eq_nil {Sg : Sig} {Γ : Ctx} {σs : List Ty} {τ : Ty} {n : Nat}
    {b : Body Sg Γ σs τ} (h : paramsUsedBody n b = true) : unreadParamsBody n b = [] := by
  simp [paramsUsedBody] at h
  simp [unreadParamsBody, List.filter_eq_nil_iff]
  intro k hk
  exact h k hk

mutual

/-- **A term the discipline accepts has nothing for the compiler to refuse**: every
    message `Term.issues` would report is one of the conditions `Term.usesOk` checks, so
    a term that passes the check has none.  (`strict := false` is the tier the compiler
    enforces: an unread *function parameter* is reported through
    `Term.paramNotes` instead, since the arity of a function is part of its type.) -/
theorem Term.issues_eq_nil_of_usesOk {Sg : Sig} :
    ∀ {Γ : Ctx} {τ : Ty} (m : JMask) (t : Term Sg Γ τ),
      Term.usesOk m t = true → Term.issues false m t = []
  | _, _, m, .var v, h => by
      simp [Term.usesOk] at h; simp [Term.issues, h]
  | _, _, _, .lit _, _ => rfl
  | _, _, _, .global _, _ => rfl
  | _, _, _, .extern _, _ => rfl
  | _, _, m, .lamN b, h => by
      simp [Term.usesOk] at h
      simp [Term.issues, Term.issues_eq_nil_of_usesOk _ b h.2]
  | _, _, m, .lamProd rets, h => by
      simp [Term.usesOk] at h
      simp [Term.issues, Spine.issues_eq_nil_of_usesOk _ rets h.2]
  | _, _, m, .apN f args, h => by
      simp [Term.usesOk] at h
      simp [Term.issues, Term.issues_eq_nil_of_usesOk _ f h.1,
        Spine.issues_eq_nil_of_usesOk _ args h.2]
  | _, _, m, .callProd f args _, h => by
      simp [Term.usesOk] at h
      simp [Term.issues, Term.issues_eq_nil_of_usesOk _ f h.1,
        Spine.issues_eq_nil_of_usesOk _ args h.2]
  | _, _, m, .jsOp _ args, h => by
      simp [Term.usesOk] at h
      simp [Term.issues, Spine.issues_eq_nil_of_usesOk _ args h]
  | _, _, m, .lazyMk e, h => by
      simp [Term.usesOk] at h
      simp [Term.issues, Term.issues_eq_nil_of_usesOk _ e h]
  | _, _, m, .lazyForce e, h => by
      simp [Term.usesOk] at h
      simp [Term.issues, Term.issues_eq_nil_of_usesOk _ e h]
  | _, _, m, .letE e b, h => by
      simp [Term.usesOk] at h
      simp [Term.issues, h.1.1, Term.issues_eq_nil_of_usesOk _ e h.1.2,
        Term.issues_eq_nil_of_usesOk _ b h.2]
  | _, _, m, .ite c t u, h => by
      simp [Term.usesOk] at h
      simp [Term.issues, Term.issues_eq_nil_of_usesOk _ c h.1.1,
        Term.issues_eq_nil_of_usesOk _ t h.1.2, Term.issues_eq_nil_of_usesOk _ u h.2]
  | _, _, m, .ctor _ _ _ args, h => by
      simp [Term.usesOk] at h
      simp [Term.issues, Spine.issues_eq_nil_of_usesOk _ args h]
  | _, _, m, .proj e _ _ _, h => by
      simp [Term.usesOk] at h
      simp [Term.issues, Term.issues_eq_nil_of_usesOk _ e h]
  | _, _, m, .tagOf e _, h => by
      simp [Term.usesOk] at h
      simp [Term.issues, Term.issues_eq_nil_of_usesOk _ e h]
  | _, _, m, .caseTag s alts _, h => by
      simp [Term.usesOk] at h
      simp [Term.issues, Term.issues_eq_nil_of_usesOk _ s h.1,
        Alts.issues_eq_nil_of_usesOk _ alts h.2]
  | _, _, m, .loop init body, h => by
      simp [Term.usesOk] at h
      simp [Term.issues, unreadParamsBody_eq_nil h.1.1, paramMsgs,
        Spine.issues_eq_nil_of_usesOk _ init h.1.2,
        Body.issues_eq_nil_of_usesOk _ body h.2]
  | _, _, m, .joinPoint body rest, h => by
      simp [Term.usesOk] at h
      simp [Term.issues, unreadParams_eq_nil h.1.1.1, paramMsgs,
        Term.issues_eq_nil_of_usesOk _ body h.1.2,
        Term.issues_eq_nil_of_usesOk _ rest h.2]
      omega
  | _, _, m, .jump v args, h => by
      simp [Term.usesOk] at h
      simp [Term.issues, h.1, Spine.issues_eq_nil_of_usesOk _ args h.2]

/-- `Term.issues_eq_nil_of_usesOk`, over a spine. -/
theorem Spine.issues_eq_nil_of_usesOk {Sg : Sig} :
    ∀ {Γ : Ctx} {σs : List Ty} (m : JMask) (s : Spine Sg Γ σs),
      Spine.usesOk m s = true → Spine.issues false m s = []
  | _, _, _, .nil, _ => rfl
  | _, _, m, .cons t rest, h => by
      simp [Spine.usesOk] at h
      simp [Spine.issues, Term.issues_eq_nil_of_usesOk _ t h.1,
        Spine.issues_eq_nil_of_usesOk _ rest h.2]

/-- `Term.issues_eq_nil_of_usesOk`, over the branches of a case. -/
theorem Alts.issues_eq_nil_of_usesOk {Sg : Sig} :
    ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat} (m : JMask) (a : Alts Sg Γ τ tags),
      Alts.usesOk m a = true → Alts.issues false m a = []
  | _, _, _, m, .deflt t, h => by
      simp [Alts.usesOk] at h
      simp [Alts.issues, Term.issues_eq_nil_of_usesOk _ t h]
  | _, _, _, m, .cons _ t rest, h => by
      simp [Alts.usesOk] at h
      simp [Alts.issues, Term.issues_eq_nil_of_usesOk _ t h.1,
        Alts.issues_eq_nil_of_usesOk _ rest h.2]

/-- `Term.issues_eq_nil_of_usesOk`, over a loop block. -/
theorem Body.issues_eq_nil_of_usesOk {Sg : Sig} :
    ∀ {Γ : Ctx} {σs : List Ty} {τ : Ty} (m : JMask) (b : Body Sg Γ σs τ),
      Body.usesOk m b = true → Body.issues false m b = []
  | _, _, _, m, .ret t, h => by
      simp [Body.usesOk] at h
      simp [Body.issues, Term.issues_eq_nil_of_usesOk _ t h]
  | _, _, _, m, .cont args, h => by
      simp [Body.usesOk] at h
      simp [Body.issues, Spine.issues_eq_nil_of_usesOk _ args h]
  | _, _, _, m, .letB e b, h => by
      simp [Body.usesOk] at h
      simp [Body.issues, h.1.1, Term.issues_eq_nil_of_usesOk _ e h.1.2,
        Body.issues_eq_nil_of_usesOk _ b h.2]
  | _, _, _, m, .iteB c t u, h => by
      simp [Body.usesOk] at h
      simp [Body.issues, Term.issues_eq_nil_of_usesOk _ c h.1.1,
        Body.issues_eq_nil_of_usesOk _ t h.1.2, Body.issues_eq_nil_of_usesOk _ u h.2]
  | _, _, _, m, .joinPointB body rest, h => by
      simp [Body.usesOk] at h
      simp [Body.issues, unreadParams_eq_nil h.1.1.1, paramMsgs,
        Term.issues_eq_nil_of_usesOk _ body h.1.2,
        Body.issues_eq_nil_of_usesOk _ rest h.2]
      omega

end

/-- A term built through this interface is one `LakeJs.Compile` accepts. -/
theorem WfTermIn.usesOkDecl {Sg : Sig} {Γ : Ctx} {τ : Ty} (t : WfTermIn Sg Γ τ) :
    Term.usesOkDecl t.1 = true := by
  have h := Term.issues_eq_nil_of_usesOk (plainMask Γ) t.1 t.2
  unfold plainMask at h
  simp [Term.usesOkDecl, Term.declIssues, h]

end LakeJs.Usage
