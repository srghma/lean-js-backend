module

public import LakeJs.SN

@[expose] public section

/-!
# The fragment the evaluator is total on

`LakeJs.Diverge` shows that no evaluator of the *whole* language is total: a `Tail.label`
with `self = true` is the one construct that repeats work, and a loop whose body jumps
back at once never answers.  `Term.simple` is the decidable check that a term stays out
of that, and of the rest of the block grammar, which the totality proof does not cover:

* **no `Term.block`** — a loop is a label of a block, and that is the essential reason;
  a label of either kind is also inlined at its jumps (`StepT.labelJoin`,
  `StepT.labelLoop`), which duplicates the block, and the reducibility argument of
  `LakeJs.Reducibility` is not carried through that duplication here;
* **a field read answers with a value type**, i.e. a `Term.proj` whose result type is
  neither a function type nor a delayed one (`Ty.ground`).  Reading a field takes a term
  out from under a constructor, and the logical relation would have to hold of the
  fields of every constructor to say anything about a function read out of a record;
  that is what `USAGE_INDEX_ASSESSMENT.md`-style hereditary reducibility would buy and
  what is left out here.  Reading a `Nat`, a `String`, an array or another record out of
  a record is inside the fragment; reading a *function* out of one is not.

Everything else — variables, functions, applications, literals, globals, the whole
catalogue of runtime functions, delayed values, `let`, `if`, constructors, tag tests and
dispatches — is inside it.
-/

namespace LakeJs

open LakeJs.Ty

/-- A **value type**: one that is not a function type and not a delayed one.  An answer
    at such a type is a literal or a constructor, and the evaluator needs nothing more of
    it than that it runs out of steps. -/
def Ty.ground : Ty → Bool
  | .fn _ _ => false
  | .primCovariant (.lazy _) => false
  | _ => true

/-- A terminal type is a value type. -/
theorem Ty.ground_prim (p : LeanPrimTy) : (Ty.prim p).ground = true := rfl

/-- **A type with a constructor is a value type**: a function type and a delayed type
    have no layout, so nothing can be built at one. -/
theorem Ty.ground_of_ctorFields? {τ : Ty} {i : Nat} {fs : Layout.FieldLayout}
    (h : τ.ctorFields? i = some fs) : τ.ground = true := by
  cases τ with
  | fn _ _ => exact absurd h (by simp [Ty.ctorFields?, Ty.layout?])
  | primCovariant c =>
      cases c with
      | lazy _ => exact absurd h (by simp [Ty.ctorFields?, Ty.layout?])
      | _ => rfl
  | _ => rfl

namespace Expr

open LakeJs
open LakeJs.Ty

variable {Sg : Sig}

mutual

/-- **Is this term inside the fragment the evaluator is total on?**  See the header. -/
def Term.simple {Sg : Sig} : ∀ {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → Bool
  | _, _, .var _ => true
  | _, _, .lam b => b.simple
  | _, _, .ap f a => f.simple && a.simple
  | _, _, .lit _ => true
  | _, _, .global _ => true
  | _, _, .extern _ => true
  | _, _, .lazyMk e => e.simple
  | _, _, .lazyForce e => e.simple
  | _, _, .letE e b => e.simple && b.simple
  | _, _, .ite c t e => c.simple && t.simple && e.simple
  | _, _, .ctor _ _ _ args => args.simple
  | _, _, .proj (τ := τ) e _ _ _ _ => τ.ground && e.simple
  | _, _, .tagOf e _ => e.simple
  | _, _, .caseTag e alts _ => e.simple && alts.simple
  | _, _, .block _ => false

/-- Is every term of this spine inside the fragment? -/
def Spine.simple {Sg : Sig} : ∀ {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → Bool
  | _, _, .nil => true
  | _, _, .cons t rest => t.simple && rest.simple

/-- Is every branch of this dispatch inside the fragment? -/
def Alts.simple {Sg : Sig} : ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat} {full : Bool},
    Alts Sg Γ τ tags full → Bool
  | _, _, _, _, .deflt t => t.simple
  | _, _, _, _, .nilFull => true
  | _, _, _, _, .cons _ t rest => t.simple && rest.simple

end

end Expr

end LakeJs

end
