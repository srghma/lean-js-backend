import LakeJs.Reduce

/-!
# The relation has a cycle: `Step` is not a terminating rewrite system

`LakeJs/Reduce.lean` writes the optimiser down as a relation, so that questions like
"is it confluent?" and "is it idempotent?" can be *asked*.  This file answers the first
of the questions that come before those: **does every reduction end?**  It does not.

The guard rule `iteGuard` says that the `else` branch of a test against `0` may be
rewritten by `Term.assumeNonZero`, which turns a truncating `n - 1` into the plain one
for the variable the test has just shown is not zero.  Where the branch holds no such
subtraction, `Term.assumeNonZero` gives the branch back unchanged — and the rule then
relates the term to *itself*:

```
if (n === 0) then 0 else 0   —→   if (n === 0) then 0 else 0
```

So `Step` is reflexive at that term, no element of the relation is accessible from it,
and the relation is not well-founded.  Nothing here is a defect of the *function*: the
simplifier applies each rule once in a bottom-up sweep, so it always stops.  It is a
statement about the relation, and it is what makes "the normal form of a term" the wrong
phrase to reach for when reasoning about `Step`: a term that steps to itself has none.
-/

namespace LakeJs.ReduceCycle

open LakeJs
open LakeJs.Ty
open LakeJs.Layout (FieldLayout ObjLayout)
open LakeJs.Expr
open LakeJs.Lookup
open LakeJs.Rename
open LakeJs.Reduce

/-- The signature and the table the example is written against: both empty, since the
    example mentions no top-level declaration. -/
abbrev exSig : Sig := []

/-- The empty table of inlinable declarations. -/
def exTbl : Inline.Table exSig := {}

/-- The context of the example: one `Nat` in scope, the `n` the test reads. -/
abbrev exCtx : Ctx := [Ty.nat]

/-- The test `n === 0`, which `nonZeroGuard?` recognises. -/
def exGuard : Term exSig exCtx (.prim .bool) :=
  .apN (.extern .lean_nat_beq) (.cons (.var .head) (.cons (.lit (.nat 0)) .nil))

/-- `if (n === 0) then 0 else 0`: a guarded test whose branches hold no subtraction for
    the guard to sharpen. -/
def exTerm : Term exSig exCtx Ty.nat :=
  .ite exGuard (.lit (.nat 0)) (.lit (.nat 0))

/-- The test is a guard: it tests the variable at index `0` against zero. -/
theorem exGuard_isGuard : LakeJs.Simp.nonZeroGuard? exGuard = some 0 := rfl

/-- Sharpening the `else` branch leaves it alone, there being nothing in it to sharpen. -/
theorem exElse_assumeNonZero :
    LakeJs.Simp.Term.assumeNonZero (Sg := exSig) (Γ := exCtx) 0 (.lit (.nat 0))
      = .lit (.nat 0) := rfl

/-- **The cycle.**  The guard rule rewrites `exTerm` to `exTerm`. -/
theorem exTerm_step_self : Step exTbl exTerm exTerm := by
  have h : Step exTbl exTerm
      (.ite exGuard (.lit (.nat 0))
        (LakeJs.Simp.Term.assumeNonZero 0 (.lit (.nat 0)))) :=
    .iteGuard exGuard_isGuard
  simpa [exTerm, exElse_assumeNonZero] using h

/-- A relation with a self-loop leaves the element it loops at inaccessible. -/
theorem not_acc_of_self {α : Sort u} {R : α → α → Prop} {x : α} (h : R x x) :
    ¬ Acc R x := by
  intro hx
  induction hx with
  | intro y _ ih => exact ih y h h

/-- **`Step` is not well-founded**, so it is not a terminating rewrite system and a term
    need not have a normal form: `exTerm` steps to itself for ever. -/
theorem step_not_wellFounded :
    ¬ WellFounded (fun a b : Term exSig exCtx Ty.nat => Step exTbl b a) :=
  fun h =>
    not_acc_of_self (R := fun a b : Term exSig exCtx Ty.nat => Step exTbl b a)
      exTerm_step_self (h.apply exTerm)

/-- The same fact stated as the relation's own irreflexivity failing: there is a term
    the relation relates to itself. -/
theorem step_not_irreflexive :
    ∃ (Sg : Sig) (tbl : Inline.Table Sg) (Γ : Ctx) (τ : Ty) (t : Term Sg Γ τ),
      Step tbl t t :=
  ⟨exSig, exTbl, exCtx, Ty.nat, exTerm, exTerm_step_self⟩

end LakeJs.ReduceCycle
