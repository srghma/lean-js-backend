module

public import LakeJs.SN

@[expose] public section

set_option autoImplicit false

/-!
# The fragment the evaluator is total on — which is now the whole language

This module used to carve out `Term.simple`, a decidable check that a term stays out of
the two places the totality proof of the time did not reach: the block grammar (because a
label could be a loop, and a loop can diverge) and a field read whose result is a
function (because the logical relation was not hereditary).  Only inside that fragment was
the evaluator known to answer.

Both restrictions are gone.

* **The block grammar is safe.**  The one label is `Tail.join`, whose body is typed in
  the outer label context, so a block is a finite nest of join points and repeats no work.
  Repeating work is `Term.fix`, which carries its rank.
* **There is no logical relation to be hereditary.**  `Term.eval` is a Lean function into
  `Ty.den τ`, so a field read is `Ty.ofData` and nothing has to be proved about what it
  answers.

So the fragment is the whole language, and `Term.simple` is the constant `true` — which
is why it is not defined here any more.  What is kept is the notion of a **value type**,
`Ty.ground`, which the emitter still uses to tell a type whose values are data from one
whose values are code, together with the fact that every type with a constructor is one.
-/

namespace LakeJs

open LakeJs.Ty

/-- A **value type**: one that is not a function type and not a delayed one.  A value of
    such a type is data — a scalar, a constructor value, a sequence — and can be written
    into a runtime tree; `Ty.storable` is the sharper form of the same idea, and this is
    the shallow test the emitter uses. -/
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

/-- **Every term is inside the fragment**: the evaluator answers for all of them, blocks
    and recursions included.  This is the statement `Term.simple` used to approximate. -/
theorem Term.eval_defined {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {τ : Ty} (t : Term Sg Γ Ρ τ)
    (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ) : ∃ v : τ.den, t.eval δ γ ρ = v :=
  ⟨t.eval δ γ ρ, rfl⟩

end Expr

end LakeJs

end
