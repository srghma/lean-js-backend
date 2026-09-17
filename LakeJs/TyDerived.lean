import LakeJs.TyDerive

/-!
# The generic types, derived from Lean's own declarations

`Option α` and `Prod α β` are **not** constructors of `Ty`: the first is an ordinary
non-recursive tagged union and the second an ordinary one-constructor record, so the
backend needs no special case for either, and `LakeJs.Ty` offers them as the
abbreviations `Ty.option` and `Ty.prod`.

Those two abbreviations are written by hand, so they *could* disagree with what the
backend reads off Lean's real `Option` and `Prod` — a constructor added, a field
reordered, a field made a proof.  This module derives the same two functions from the
declarations themselves with `derive_ty`, and checks that the hand-written ones agree
with them.  The check is `rfl`, so it is made whenever this module is built.
-/

open LakeJs LakeJs.Ty

namespace LakeJs.TyDerived

/-- `Option α`, read off Lean's `Option`: constructor `0` (`none`) carries nothing and
    constructor `1` (`some`) carries the value. -/
derive_ty Option as optionOfDecl

/-- `Prod α β`, read off Lean's `Prod`: one constructor with two fields.  (`Ty.fn`
    already takes a *list* of parameters, so a product is never needed to pass several
    arguments — only to return several results.) -/
derive_ty Prod as prodOfDecl

/-- The hand-written `Ty.option` is what the backend reads off `Option`. -/
theorem option_eq_optionOfDecl : Ty.option = optionOfDecl := rfl

/-- The hand-written `Ty.prod` is what the backend reads off `Prod`. -/
theorem prod_eq_prodOfDecl : Ty.prod = prodOfDecl := rfl

/-- `Except ε α` needs no special case either: it is the tagged union whose `error`
    carries an `ε` and whose `ok` carries an `α`. -/
derive_ty Except as exceptOfDecl

example : exceptOfDecl .nat .string = Ty.taggedUnion [[.nat], [.string]] := rfl

end LakeJs.TyDerived
