import LakeJs.FromLcnf
import LakeJs.TySchema

/-!
# `lean_…_schema% T` — the `Ty` the backend models a real Lean type by

The backend already reads a Lean type: `LakeJs.FromLcnf.toTy` is what turns the type of
every binder of a compiled declaration into a `LakeJs.Ty`, and it is the only such
translation there is.  This module puts that one function behind term elaborators, so
that a schema can be read off a declaration *while elaborating Lean source* — and,
because it is the same function, the schema printed here is by construction the one the
compiled code is checked against, with no second translation to drift from it.

| elaborator                        | produces                    |
| :-------------------------------- | :-------------------------- |
| `lean_ty% T`                       | `Ty`                         |
| `lean_enum_schema% T`              | `LeanEnumSchema`             |
| `lean_record_schema% T`            | `LeanRecordSchema`           |
| `lean_tagged_union_schema% T`      | `LeanTaggedUnionSchema`      |
| `lean_rec_tagged_union_schema% T`  | `LeanTaggedUnionSchema`   |
| `lean_rec_object_schema% T`        | `LeanRecordSchema`        |
| `lean_rec_alias_schema% T`         | `RTy`         |
| `lean_mutual_rec_family% T`        | `LeanMutualRecFamily`        |

There is no `Ty` argument to any of those names: `Ty` *is* the type language, so the
payload of `Ty.record` is a `List Ty` and the payload of `Ty.recAlias` is an
`Ty.RTy` — see `LakeJs.TySchema`.

Each of the seven shape elaborators **checks** that the type really has that shape, so
`lean_enum_schema% Option` is an error naming the shape `Option` actually has, not a
silently different schema.  The counting conditions — an enum has at least three
constructors, a record at least two fields, a tagged union at least two constructors of
which one carries a field — are conditions of the *schema types* themselves
(`LakeJs.Schema`), so a schema that fails one of them cannot be built at all rather than
being built and then rejected.  `lean_ty% T` accepts any shape, and checks the whole
type with `Ty.wf`.

The argument is a *type*, not only a name, so a parameterised declaration may be read at
an instantiation: `lean_ty% (Except Nat String)` is a `taggedUnion`, and
`lean_ty% (Array (Option Nat))` is an array.  A declaration with parameters left open —
`Option` rather than `Option Nat` — is not a type but a family of them, and is what
`derive_ty` (`LakeJs.TyDerive`) handles.

## What is supported, and what is refused

Whatever `LakeJs.FromLcnf` supports, which is what the backend compiles:

* a parameterised declaration is modelled **at its instantiation**, and a mutual block
  as a family, so every type is a finite tree;
* a field that carries nothing at run time — a proof, a type, a `Unit` — is dropped, and
  a declaration left with one constructor carrying one field is a **newtype**, whose
  wrapper is erased: `structure Wrapper where x : Nat` *is* `Ty.nat`, and
  `structure Rose where kids : Array Rose` is `Ty.recAlias (.array (.self 0))`;
* an indexed family, a recursive declaration nested inside another one's body, and a
  declaration with no constructors are refused with a message saying why.
-/

open Lean Elab Term Meta

namespace LakeJs.TyMeta

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

open LakeJs.Ty

/-! ## Quoting a `Ty` back into syntax

The elaborators compute a `Ty` and then have to *return* it, so each shape is rendered
as the term that builds it.  The rendering uses the abbreviations of `LakeJs.Ty`
(`Ty.array`, `Ty.nat`, …), so what a `lean_ty%` elaborates to is also what one would
write by hand. -/

/-- A `LeanPrimTy`, as syntax.  Every constructor but `bitvec` is named by its own
    `pretty`, which is the constructor's name. -/
def primSyn : LeanPrimTy → MetaM Term
  | .bitvec n _ => `(LeanPrimTy.bitvec $(quote n))
  | p => return mkIdent (`LakeJs.LeanPrimTy ++ Name.mkSimple p.pretty)

/-- An `Int`, as syntax: `quote` covers the non-negative ones. -/
def intSyn (i : Int) : MetaM Term :=
  if i < 0 then do `(-$(quote i.natAbs)) else `($(quote i.natAbs))

mutual

/-- A closed type, as syntax. -/
partial def tySyn : Ty → MetaM Term
  | .prim p => do `(Ty.prim $(← primSyn p))
  | .typeParam => `(Ty.typeParam)
  | .fnTy s => tyFnSyn s
  | .primCovariant s => tyCovSyn s
  | .enum e => do `(Ty.enum $(← enumSchemaSyn e))
  | .record fs => do `(Ty.record $(← tyA2Syn fs))
  | .taggedUnion l => do `(Ty.taggedUnion $(← tyTUSyn l))
  | .recTaggedUnion ⟨l⟩ => do `(Ty.recTaggedUnion ⟨$(← rtyTUSyn l)⟩)
  | .recObject ⟨fs⟩ => do `(Ty.recObject ⟨$(← rtyA2Syn fs)⟩)
  | .recAlias ⟨b⟩ => do `(Ty.recAlias ⟨$(← rtySyn b)⟩)
  | .mutualRecursiveFamily f => do `(Ty.mutualRecursiveFamily $(← familySyn f))

/-- A function type, over closed types. -/
partial def tyFnSyn : TyFn Ty → MetaM Term
  | .fn ps r => do `(Ty.fn $(← tyListSyn ps) $(← tySyn r))
  | .fn_returnsProd ps r rs => do
      `(Ty.fn_returnsProd $(← tyListSyn ps) $(← tySyn r) $(← tyListSyn rs))

/-- An invariant type former, over closed types. -/
partial def tyCovSyn : LeanPrimTyCovariant Ty → MetaM Term
  | .array a => do `(Ty.array $(← tySyn a))
  | .list a => do `(Ty.list $(← tySyn a))
  | .task a => do `(Ty.task $(← tySyn a))
  | .promise a => do `(Ty.promise $(← tySyn a))
  | .thunk a => do `(Ty.thunk $(← tySyn a))
  | .lazy a => do `(Ty.lazy $(← tySyn a))

/-- A list of closed types, as a list literal. -/
partial def tyListSyn (ts : List Ty) : MetaM Term := do
  let ts ← ts.toArray.mapM tySyn
  `([$ts,*])

/-- The constructors of a closed layout, as a list of list literals. -/
partial def tyCtorsSyn (l : List (List Ty)) : MetaM Term := do
  let l ← l.toArray.mapM tyListSyn
  `([$l,*])

/-- The fields of a record of closed types. -/
partial def tyA2Syn (fs : LeanRecordSchema Ty) : MetaM Term := do
  `(⟨$(← tySyn fs.fst), $(← tySyn fs.snd), $(← tyListSyn fs.rest)⟩)

/-- The fields of a constructor of closed types that has at least one. -/
partial def tyNESyn (f : NonEmptyList Ty) : MetaM Term := do
  `(⟨$(← tySyn f.head), $(← tyListSyn f.tail)⟩)

/-- The constructors of a tagged union of closed types. -/
partial def tyTUSyn : LeanTaggedUnionSchema Ty → MetaM Term
  | .payloadFirst f n r => do
      `(LeanTaggedUnionSchema.payloadFirst $(← tyNESyn f) $(← tyListSyn n)
          $(← tyCtorsSyn r))
  | .skip rest => do `(LeanTaggedUnionSchema.skip $(← tyCPSyn rest))

/-- The constructors of closed types that follow a field-less one. -/
partial def tyCPSyn : CtorsWithPayload Ty → MetaM Term
  | .here f r => do `(CtorsWithPayload.here $(← tyNESyn f) $(← tyCtorsSyn r))
  | .skip rest => do `(CtorsWithPayload.skip $(← tyCPSyn rest))

/-- A type inside a recursive declaration, as syntax. -/
partial def rtySyn : RTy → MetaM Term
  | .self i => do `(RTy.self $(quote i))
  | .prim p => do `(RTy.prim $(← primSyn p))
  | .typeParam => `(RTy.typeParam)
  | .fnTy s => rtyFnSyn s
  | .primCovariant s => rtyCovSyn s
  | .enum e => do `(RTy.enum $(← enumSchemaSyn e))
  | .record fs => do `(RTy.record $(← rtyA2Syn fs))
  | .taggedUnion l => do `(RTy.taggedUnion $(← rtyTUSyn l))
  | .recTaggedUnion ⟨l⟩ => do `(RTy.recTaggedUnion ⟨$(← rtyTUSyn l)⟩)
  | .recObject ⟨fs⟩ => do `(RTy.recObject ⟨$(← rtyA2Syn fs)⟩)
  | .recAlias ⟨b⟩ => do `(RTy.recAlias ⟨$(← rtySyn b)⟩)
  | .mutualRecursiveFamily f => do `(RTy.mutualRecursiveFamily $(← familySyn f))

/-- A function type, over types that may mention `.self`. -/
partial def rtyFnSyn : TyFn RTy → MetaM Term
  | .fn ps r => do `(RTy.fn $(← rtyListSyn ps) $(← rtySyn r))
  | .fn_returnsProd ps r rs => do
      `(RTy.fn_returnsProd $(← rtyListSyn ps) $(← rtySyn r) $(← rtyListSyn rs))

/-- An invariant type former, over types that may mention `.self`. -/
partial def rtyCovSyn : LeanPrimTyCovariant RTy → MetaM Term
  | .array a => do `(RTy.array $(← rtySyn a))
  | .list a => do `(RTy.list $(← rtySyn a))
  | .task a => do `(RTy.task $(← rtySyn a))
  | .promise a => do `(RTy.promise $(← rtySyn a))
  | .thunk a => do `(RTy.thunk $(← rtySyn a))
  | .lazy a => do `(RTy.lazy $(← rtySyn a))

/-- A list of types that may mention `.self`, as a list literal. -/
partial def rtyListSyn (ts : List RTy) : MetaM Term := do
  let ts ← ts.toArray.mapM rtySyn
  `([$ts,*])

/-- The constructors of a layout, as a list of list literals. -/
partial def rtyCtorsSyn (l : List (List RTy)) : MetaM Term := do
  let l ← l.toArray.mapM rtyListSyn
  `([$l,*])

/-- The fields of a record. -/
partial def rtyA2Syn (fs : LeanRecordSchema RTy) : MetaM Term := do
  `(⟨$(← rtySyn fs.fst), $(← rtySyn fs.snd), $(← rtyListSyn fs.rest)⟩)

/-- The fields of a constructor that has at least one. -/
partial def rtyNESyn (f : NonEmptyList RTy) : MetaM Term := do
  `(⟨$(← rtySyn f.head), $(← rtyListSyn f.tail)⟩)

/-- The constructors of a tagged union. -/
partial def rtyTUSyn : LeanTaggedUnionSchema RTy → MetaM Term
  | .payloadFirst f n r => do
      `(LeanTaggedUnionSchema.payloadFirst $(← rtyNESyn f) $(← rtyListSyn n)
          $(← rtyCtorsSyn r))
  | .skip rest => do `(LeanTaggedUnionSchema.skip $(← rtyCPSyn rest))

/-- The constructors that follow a field-less one. -/
partial def rtyCPSyn : CtorsWithPayload RTy → MetaM Term
  | .here f r => do `(CtorsWithPayload.here $(← rtyNESyn f) $(← rtyCtorsSyn r))
  | .skip rest => do `(CtorsWithPayload.skip $(← rtyCPSyn rest))

/-- One member of a mutual family, as syntax. -/
partial def famMemberSyn : FamMember → MetaM Term
  | .ctors l => do `(LeanFamMemberSchema.ctors $(← rtyTUSyn l))
  | .record fs => do `(LeanFamMemberSchema.record $(← rtyA2Syn fs))
  | .alias b => do `(LeanFamMemberSchema.alias $(← rtySyn b))

/-- The members of a mutual family, as a list literal. -/
partial def famMembersSyn (ms : List FamMember) : MetaM Term := do
  let ms ← ms.toArray.mapM famMemberSyn
  `([$ms,*])

/-- A mutual family, as syntax. -/
partial def familySyn : LeanMutualRecFamily RTy → MetaM Term
  | .selectedThenMore before current next after => do
      `(LeanMutualRecFamily.selectedThenMore $(← famMembersSyn before)
          $(← famMemberSyn current) $(← famMemberSyn next) $(← famMembersSyn after))
  | .selectedLast first before current => do
      `(LeanMutualRecFamily.selectedLast $(← famMemberSyn first)
          $(← famMembersSyn before) $(← famMemberSyn current))

/-- A `LeanEnumSchema`, as syntax. -/
partial def enumSchemaSyn (e : LeanEnumSchema) : MetaM Term := do
  `(⟨$(quote e.extraConstructors), $(← intSyn e.shift)⟩)

end

/-! ## Reading the type -/

/-- The `Ty` the backend models a Lean type by, or an error explaining why it models
    none. -/
def tyOfExpr (e : Expr) : MetaM Ty := do
  match LakeJs.FromLcnf.toTy (← getEnv) e with
  | .ok τ => return τ
  | .error msg => throwError "`{e}` is not a type the backend models: {msg}"

/-- The `Ty` the backend models the Lean type written as `t` by. -/
def tyOfSyntax (t : Term) : TermElabM Ty := do
  tyOfExpr (← instantiateMVars (← elabType t))

/-- The name of the shape a type has, for the error message of an elaborator that
    wanted a different one. -/
def shapeName : Ty → String
  | .prim p => "the primitive type " ++ p.pretty
  | .typeParam => "a type parameter"
  | .fnTy _ => "a function type"
  | .primCovariant (.array _) => "an array"
  | .primCovariant (.list _) => "a list"
  | .primCovariant (.task _) => "a task"
  | .primCovariant (.promise _) => "a promise"
  | .primCovariant (.thunk _) => "a thunk"
  | .primCovariant (.lazy _) => "a lazy value"
  | .enum _ => "an enum"
  | .record _ => "a record"
  | .taggedUnion _ => "a tagged union"
  | .recTaggedUnion _ => "a recursive tagged union"
  | .recObject _ => "a recursive record"
  | .recAlias _ => "a recursive newtype (an alias)"
  | .mutualRecursiveFamily _ => "a member of a mutual family"

/-- Fail unless the payload read off `τ` is one the backend can produce. -/
def checkOk (τ : Ty) (ok : Bool) : TermElabM Unit := do
  unless ok do
    throwError "the type read off `{τ.pretty}` is not one the backend can produce; \
      see `LakeJs.TySchema` for the conditions a recursive shape has to meet"

/-! ## The elaborators -/

/-- `lean_ty% T` — the `Ty` the backend models the Lean type `T` by. -/
elab "lean_ty% " t:term : term => do
  let τ ← tyOfSyntax t
  checkOk τ (Ty.wf τ)
  elabTerm (← tySyn τ) none

/-- `lean_enum_schema% T` — the `LeanEnumSchema` of a type whose constructors all have
    no fields. -/
elab "lean_enum_schema% " t:term : term => do
  let τ ← tyOfSyntax t
  let some s := τ.enumSchema?
    | throwError "`{t}` is {shapeName τ}, not an enum"
  checkOk τ (Ty.wf τ)
  elabTerm (← enumSchemaSyn s) none

/-- `lean_record_schema% T` — the `LeanRecordSchema` of a non-recursive declaration with
    one constructor and at least two fields. -/
elab "lean_record_schema% " t:term : term => do
  let τ ← tyOfSyntax t
  let some fs := τ.recordSchema?
    | throwError "`{t}` is {shapeName τ}, not a record (a one-field declaration is a \
        newtype, and is erased into its field)"
  checkOk τ (Ty.wf τ)
  elabTerm (← tyA2Syn fs) none

/-- `lean_tagged_union_schema% T` — the `LeanTaggedUnionSchema` of a non-recursive
    `inductive` with fields. -/
elab "lean_tagged_union_schema% " t:term : term => do
  let τ ← tyOfSyntax t
  let some l := τ.taggedUnionSchema?
    | throwError "`{t}` is {shapeName τ}, not a non-recursive tagged union"
  checkOk τ (Ty.wf τ)
  elabTerm (← tyTUSyn l) none

/-- `lean_rec_tagged_union_schema% T` — the `LeanTaggedUnionSchema` of a recursive
    `inductive` with at least two constructors. -/
elab "lean_rec_tagged_union_schema% " t:term : term => do
  let τ ← tyOfSyntax t
  let some l := τ.recTaggedUnionSchema?
    | throwError "`{t}` is {shapeName τ}, not a recursive tagged union"
  checkOk τ (Ty.wf τ)
  elabTerm (← (do `(⟨$(← rtyTUSyn l.ctors)⟩))) none

/-- `lean_rec_object_schema% T` — the `LeanRecordSchema` of a recursive declaration
    with one constructor and at least two fields. -/
elab "lean_rec_object_schema% " t:term : term => do
  let τ ← tyOfSyntax t
  let some fs := τ.recObjectSchema?
    | throwError "`{t}` is {shapeName τ}, not a recursive record (a one-field one is a \
        newtype: it is erased, and becomes a `Ty.recAlias`)"
  checkOk τ (Ty.wf τ)
  elabTerm (← (do `(⟨$(← rtyA2Syn fs.fields)⟩))) none

/-- `lean_rec_alias_schema% T` — the `RTy` of a recursive newtype. -/
elab "lean_rec_alias_schema% " t:term : term => do
  let τ ← tyOfSyntax t
  let some b := τ.recAliasSchema?
    | throwError "`{t}` is {shapeName τ}, not a recursive newtype (one constructor, \
        carrying one runtime field, which mentions the declaration itself)"
  checkOk τ (Ty.wf τ)
  elabTerm (← (do `(⟨$(← rtySyn b.body)⟩))) none

/-- `lean_mutual_rec_family% T` — the `LeanMutualRecFamily` of a genuinely mutual block,
    pointing at the member `T`. -/
elab "lean_mutual_rec_family% " t:term : term => do
  let τ ← tyOfSyntax t
  let some f := τ.mutualRecFamily?
    | throwError "`{t}` is {shapeName τ}, not a member of a genuinely mutual block (a \
        block of at least two declarations that each reach the other)"
  checkOk τ (Ty.wf τ)
  elabTerm (← familySyn f) none

end LakeJs.TyMeta
