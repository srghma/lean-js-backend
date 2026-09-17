import LakeJs.Scalarise
import LakeJs.Usage

/-!
# The `let` that shares nothing: inlining a binding with a single reader

A `let` earns its name by *sharing*: the value is computed once and read from several
places.  A binding whose variable is read **once** shares nothing — the value belongs
where it is read — and one that is read not at all is dead.  That is the rule
`LakeJs.Usage` states of a well-formed term, and this file is the pass that makes the
terms the backend emits keep to it.

## What is rewritten, and what is not

`let x = e; b` becomes `b` with `e` in place of `x` when all three of these hold:

* **`x` is read exactly once** (`LakeJs.Usage.Term.occ`, which counts *syntactic*
  occurrences, a jump target included).  Read twice, moving the value would compute it
  twice; read once, nothing is duplicated.
* **the read is not under a binder** (`LakeJs.Usage.Term.occUnder`).  A read inside a
  lambda, a loop body, the body of a join point or a thunk happens once *per call, per
  iteration, per jump, per force*, so moving the value there turns one computation into
  many: the binding is what keeps the work outside, and it stays.
* **the value can be printed where an expression is expected** (`exprSafe`).  A `case`,
  a loop, a join point or a nested `let` in an expression position is something
  `LakeJs.EmitJs` can only print by wrapping it in an immediately-invoked arrow, which
  is a closure the module did not have before, so such a value stays where it is.  A
  lambda and a thunk are *arrow functions*, whose bodies are printed as blocks, so what
  is inside one does not matter; a conditional is a ternary, so it is an expression when
  its condition and both its answers are.

Everything else is left alone, so the pass never duplicates work and never duplicates
code.

The same rule applies to `Body.letB`, the binding of a loop block.

## Where it sits

The substitution itself is `LakeJs.Scalarise.mapTerm` with
`LakeJs.Scalarise.substHead` — the same machinery the constructor-inlining rule uses —
so the result is a term of the same signature, context and type, by construction.  The
pass is a rule of `LakeJs.Reduce.Step` (`Step.letLinearInline`, and `BodyStep` for a
block), and `LakeJs.Reduce.Term.lineariseLets_chain` proves that what it produces is
reachable from what it was given.
-/

namespace LakeJs.LinearLet

open LakeJs
open LakeJs.Ty
open LakeJs.Expr
open LakeJs.Scalarise (Env mapTerm mapSpine mapAlts mapBody substHead)

/-! ## Values that print as expressions -/

mutual

/-- Can this term be printed where JavaScript expects an **expression**, without
    `LakeJs.EmitJs` wrapping it in an immediately-invoked arrow?  A lambda and a thunk
    are arrow functions, so their bodies are blocks and anything may be inside them; a
    conditional is a ternary; a `let`, a `case`, a loop and a join point need
    statements. -/
def exprSafe {Sg : Sig} : ∀ {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → Bool
  | _, _, .var _ => true
  | _, _, .lit _ => true
  | _, _, .global _ => true
  | _, _, .extern _ => true
  | _, _, .lamN _ => true
  | _, _, .lamProd _ => true
  | _, _, .lazyMk _ => true
  | _, _, .apN f args => exprSafe f && exprSafeSpine args
  | _, _, .callProd f args _ => exprSafe f && exprSafeSpine args
  | _, _, .jsOp _ args => exprSafeSpine args
  | _, _, .lazyForce e => exprSafe e
  | _, _, .ite c t u => exprSafe c && exprSafe t && exprSafe u
  | _, _, .ctor _ _ _ args => exprSafeSpine args
  | _, _, .proj e _ _ _ => exprSafe e
  | _, _, .tagOf e _ => exprSafe e
  | _, _, .jump _ args => exprSafeSpine args
  | _, _, .letE _ _ => false
  | _, _, .caseTag _ _ _ => false
  | _, _, .loop _ _ => false
  | _, _, .joinPoint _ _ => false

/-- `exprSafe`, on every term of a spine. -/
def exprSafeSpine {Sg : Sig} : ∀ {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → Bool
  | _, _, .nil => true
  | _, _, .cons t rest => exprSafe t && exprSafeSpine rest

end

/-! ## The rule -/

/-- May the value of this `let` be moved to the one place that reads it?  The variable is
    read exactly once, that read is not under a binder, and the value is one that prints
    as an expression. -/
def movable {Sg : Sig} {Γ : Ctx} {σ τ : Ty} (e : Term Sg Γ σ) (b : Term Sg (σ :: Γ) τ) :
    Bool :=
  Usage.Term.occ 0 b == 1 && Usage.Term.occUnder 0 b == 0 && exprSafe e

/-- `movable`, for the `let` of a loop block. -/
def movableB {Sg : Sig} {Γ : Ctx} {σ : Ty} {σs : List Ty} {τ : Ty} (e : Term Sg Γ σ)
    (b : Body Sg (σ :: Γ) σs τ) : Bool :=
  Usage.Body.occ 0 b == 1 && Usage.Body.occUnder 0 b == 0 && exprSafe e

/-- The rule itself, as a function of the already rewritten parts, so that it can be
    named and reasoned about (`LakeJs.Reduce.Step.letLinearInline`): a `let` whose
    variable has a single reader is that reader, with the value in it. -/
def inlineLinearLet {Sg : Sig} {Γ : Ctx} {σ τ : Ty} (e : Term Sg Γ σ)
    (b : Term Sg (σ :: Γ) τ) : Term Sg Γ τ :=
  if movable e b then
    match mapTerm (substHead e) b with
    | some b' => b'
    | none => .letE e b
  else .letE e b

/-- `inlineLinearLet`, for the `let` of a loop block. -/
def inlineLinearLetB {Sg : Sig} {Γ : Ctx} {σ : Ty} {σs : List Ty} {τ : Ty}
    (e : Term Sg Γ σ) (b : Body Sg (σ :: Γ) σs τ) : Body Sg Γ σs τ :=
  if movableB e b then
    match mapBody (substHead e) b with
    | some b' => b'
    | none => .letB e b
  else .letB e b

/-! ## The pass -/

mutual

/-- Move the value of every `let` with a single reader to that reader, everywhere in a
    term. -/
def Term.lineariseLets {Sg : Sig} : ∀ {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → Term Sg Γ τ
  | _, _, .letE e b => inlineLinearLet (Term.lineariseLets e) (Term.lineariseLets b)
  | _, _, .lamN b => .lamN (Term.lineariseLets b)
  | _, _, .apN f args => .apN (Term.lineariseLets f) (Spine.lineariseLets args)
  | _, _, .lamProd rets => .lamProd (Spine.lineariseLets rets)
  | _, _, .callProd f args i => .callProd (Term.lineariseLets f) (Spine.lineariseLets args) i
  | _, _, .jsOp op args => .jsOp op (Spine.lineariseLets args)
  | _, _, .lazyMk t => .lazyMk (Term.lineariseLets t)
  | _, _, .lazyForce t => .lazyForce (Term.lineariseLets t)
  | _, _, .ite c t u =>
      .ite (Term.lineariseLets c) (Term.lineariseLets t) (Term.lineariseLets u)
  | _, _, .ctor i fs h args => .ctor i fs h (Spine.lineariseLets args)
  | _, _, .proj v i j h => .proj (Term.lineariseLets v) i j h
  | _, _, .tagOf v h => .tagOf (Term.lineariseLets v) h
  | _, _, .caseTag s alts h =>
      .caseTag (Term.lineariseLets s) (Alts.lineariseLets alts) h
  | _, _, .loop init body => .loop (Spine.lineariseLets init) (Body.lineariseLets body)
  | _, _, .joinPoint body rest =>
      .joinPoint (Term.lineariseLets body) (Term.lineariseLets rest)
  | _, _, .jump v args => .jump v (Spine.lineariseLets args)
  | _, _, t => t

/-- `Term.lineariseLets`, on every term of a spine. -/
def Spine.lineariseLets {Sg : Sig} :
    ∀ {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → Spine Sg Γ σs
  | _, _, .nil => .nil
  | _, _, .cons t rest => .cons (Term.lineariseLets t) (Spine.lineariseLets rest)

/-- `Term.lineariseLets`, on every branch of a case. -/
def Alts.lineariseLets {Sg : Sig} :
    ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat}, Alts Sg Γ τ tags → Alts Sg Γ τ tags
  | _, _, _, .deflt t => .deflt (Term.lineariseLets t)
  | _, _, _, .cons tag t rest => .cons tag (Term.lineariseLets t) (Alts.lineariseLets rest)

/-- `Term.lineariseLets`, inside a loop block. -/
def Body.lineariseLets {Sg : Sig} :
    ∀ {Γ : Ctx} {σs : List Ty} {τ : Ty}, Body Sg Γ σs τ → Body Sg Γ σs τ
  | _, _, _, .ret t => .ret (Term.lineariseLets t)
  | _, _, _, .cont args => .cont (Spine.lineariseLets args)
  | _, _, _, .letB e b => inlineLinearLetB (Term.lineariseLets e) (Body.lineariseLets b)
  | _, _, _, .iteB c t u =>
      .iteB (Term.lineariseLets c) (Body.lineariseLets t) (Body.lineariseLets u)
  | _, _, _, .joinPointB body rest =>
      .joinPointB (Term.lineariseLets body) (Body.lineariseLets rest)

end

/-! ## Worked examples

Two of them: a `let` that shares nothing, which goes, and one whose single reader is
under a lambda, which stays. -/

/-- `let x = 1 + 2; x + 5` — the binding shares nothing. -/
def sharesNothing : Term [] [] Ty.nat :=
  .letE (.apN (.extern .lean_nat_add) (.cons (.lit (.nat 1)) (.cons (.lit (.nat 2)) .nil)))
    (.apN (.extern .lean_nat_add) (.cons (♯0) (.cons (.lit (.nat 5)) .nil)))

/-- The compiler refuses it … -/
example : Usage.Term.usesOkDecl sharesNothing = false := by decide +kernel

/-- … and the pass is what makes it acceptable: `(1 + 2) + 5`. -/
example : Usage.Term.usesOkDecl (Term.lineariseLets sharesNothing) = true := by
  decide +kernel

/-- `let x = 1 + 2; fun y => x + y` — read once, but inside a lambda, so the binding is
    what keeps the addition out of the closure and it stays. -/
def readUnderLambda : Term [] [] (Ty.fn [Ty.nat] Ty.nat) :=
  .letE (.apN (.extern .lean_nat_add) (.cons (.lit (.nat 1)) (.cons (.lit (.nat 2)) .nil)))
    (.lamN (params := [Ty.nat])
      (.apN (.extern .lean_nat_add) (.cons (♯1) (.cons (♯0) .nil))))

example : Usage.Term.usesOkDecl readUnderLambda = true := by decide +kernel

end LakeJs.LinearLet
