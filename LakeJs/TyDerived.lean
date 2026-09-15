module

public import LakeJs.TyDerive
public meta import LakeJs.TyDerive

open LakeJs.TyDerive

@[expose] public section

/-!
# The derived generic types

`Option α` and `Prod α β` are **not** constructors of `Ty`: the first is an ordinary
non-recursive tagged union and the second an ordinary one-constructor record, so the
backend needs no special case for either.  Rather than writing those two schemas out
by hand — and risking a copy that disagrees with Lean's actual declarations — they are
generated from `Option` and `Prod` themselves by `derive_ty` (see `LakeJs.TyDerive`).

What is generated is what the elaborator reads off the declaration: the type's short
name, one constructor per constructor in declaration order, its short name as the
runtime tag, and the declared binder name of each field.  So `Ty.option`'s payload
field is called `val` because `Option.some`'s parameter is called `val`, and
`Ty.prod`'s fields are `fst`/`snd` for the same reason.
-/

/-- `Option α`, as the non-recursive tagged union it is:
    `{ tag: "none" } | { tag: "some", _val: … }`. -/
derive_ty Option as Ty.option

/-- `Prod α β`, as the one-constructor record it is: `{ _fst: …, _snd: … }`.  (`Ty.fn`
    already takes a *list* of parameters, so a product is never needed to pass several
    arguments — only to return several results.) -/
derive_ty Prod as Ty.prod

end
