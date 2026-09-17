import LakeJs.Reduce

/-!
# One sweep of the simplifier is not a fixed point

`LakeJs/Reduce.lean` exists so that questions about the optimiser can be *asked*; two of
the ones it names are answered elsewhere (`LakeJs/ReduceCycle.lean`: the relation does
not terminate; `LakeJs/ReduceConfluence.lean`: it is not confluent).  This file answers
the third: **is the simplifier idempotent?**

`LakeJs.Simp.Term.simp` is one bottom-up sweep, and `LakeJs.Simp.Term.simpAll`, which
the backend runs, is two of them.  The second sweep is not there by superstition: a rule
can only see the redex another rule makes.  The term below is the case the comment on
`Term.simpAll` describes —

```
let c = 0; if (n === c) then 0 else n - 1
```

— where the copy rule puts the literal `0` in the test, and only *then* is the test a
guard the `else` branch can be sharpened by: the truncating `Nat` subtraction becomes
the plain one, because a branch taken when `n ≠ 0` cannot truncate `n - 1`.  The first
sweep does the copy, the second does the sharpening, so

```
Term.simp (Term.simp t) ≠ Term.simp t
```

and one sweep is not idempotent.  That is a fact about the *function*: it says that the
number of sweeps the backend runs is part of what it computes, not an optimisation of
it.
-/

namespace LakeJs.SimpFixpoint

open LakeJs
open LakeJs.Ty
open LakeJs.Layout (FieldLayout ObjLayout)
open LakeJs.Expr
open LakeJs.Lookup
open LakeJs.Rename
open LakeJs.Reduce

/-! ## The example -/

/-- The signature of the example: empty, since it mentions no top-level declaration. -/
abbrev fxSig : Sig := []

/-- The context: one `Nat` in scope, the `n` the test reads. -/
abbrev fxCtx : Ctx := [Ty.nat]

/-- `n === c`, where `c` is the variable the `let` binds and `n` the one in scope. -/
def fxCond : Term fxSig (Ty.nat :: fxCtx) (.prim .bool) :=
  .apN (.extern .lean_nat_beq) (.cons (.var (.tail .head)) (.cons (.var .head) .nil))

/-- `n - 1`, the truncating subtraction, under the binder of the `let`. -/
def fxElse : Term fxSig (Ty.nat :: fxCtx) Ty.nat :=
  .apN (.extern .lean_nat_sub)
    (.cons (.var (.tail .head)) (.cons (.lit (.nat 1)) .nil))

/-- `let c = 0; if (n === c) then 0 else n - 1`. -/
def fxTerm : Term fxSig fxCtx Ty.nat :=
  .letE (.lit (.nat 0)) (.ite fxCond (.lit (.nat 0)) fxElse)

/-- After one sweep: the copy rule has put the literal in the test, so the test is now a
    guard — and the `else` branch still holds the truncating subtraction. -/
def fxOnce : Term fxSig fxCtx Ty.nat :=
  .ite (.apN (.extern .lean_nat_beq)
          (.cons (.var .head) (.cons (.lit (.nat 0)) .nil)))
    (.lit (.nat 0))
    (.apN (.extern .lean_nat_sub) (.cons (.var .head) (.cons (.lit (.nat 1)) .nil)))

/-- After two: the guard has sharpened the branch, and the subtraction is the plain
    one. -/
def fxTwice : Term fxSig fxCtx Ty.nat :=
  .ite (.apN (.extern .lean_nat_beq)
          (.cons (.var .head) (.cons (.lit (.nat 0)) .nil)))
    (.lit (.nat 0))
    (.jsOp .natSubExact (.cons (.var .head) (.cons (.lit (.nat 1)) .nil)))

theorem fxTerm_simp : LakeJs.Simp.Term.simp fxTerm = fxOnce := by
  with_unfolding_all rfl

theorem fxOnce_simp : LakeJs.Simp.Term.simp fxOnce = fxTwice := by
  with_unfolding_all rfl

/-! ## They are different terms -/

/-- Is the `else` branch of this conditional one of the operations that are
    JavaScript's rather than Lean's?  It is what tells the two sweeps apart: the plain
    subtraction the guard introduces is a `Term.jsOp`, the truncating one a call of the
    extern `lean_nat_sub`. -/
def elseIsJsOp {Sg : Sig} {Γ : Ctx} {τ : Ty} : Term Sg Γ τ → Bool
  | .ite _ _ (.jsOp _ _) => true
  | _ => false

theorem fxOnce_ne_fxTwice : fxOnce ≠ fxTwice :=
  fun h => absurd (congrArg elseIsJsOp h) (by with_unfolding_all decide)

/-! ## So one sweep is not idempotent -/

/-- **One sweep of the simplifier is not a fixed point.**  The copy rule of the first
    sweep makes the redex the guard rule of the second sweep fires on. -/
theorem simp_not_idempotent :
    ∃ (Sg : Sig) (Γ : Ctx) (τ : Ty) (t : Term Sg Γ τ),
      LakeJs.Simp.Term.simp (LakeJs.Simp.Term.simp t) ≠ LakeJs.Simp.Term.simp t := by
  refine ⟨fxSig, fxCtx, Ty.nat, fxTerm, ?_⟩
  rw [fxTerm_simp, fxOnce_simp]
  exact fun h => fxOnce_ne_fxTwice h.symm

/-- The two sweeps the backend runs *are* a fixed point of this term, which is why two
    is the number in `Term.simpAll`: the guard rule has nothing left to see. -/
theorem fxTerm_simpAll_fixed :
    LakeJs.Simp.Term.simpAll (LakeJs.Simp.Term.simpAll fxTerm)
      = LakeJs.Simp.Term.simpAll fxTerm := by
  with_unfolding_all rfl

end LakeJs.SimpFixpoint
