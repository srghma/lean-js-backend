module

public import LakeJs.Ty
public meta import LakeJs.Ty
public import Lean.Elab.Term
public meta import Lean.Elab.Term
public meta import Lean.Elab.Term.TermElabM
public meta import Lean.Meta.Basic
public meta import Lean.Parser.Extra

public section
@[expose] section

/-!
# `lean_…_schema% T` — reading a schema off a real Lean declaration

One elaborator per shape of `Ty`:

| elaborator                       | produces                     |
| :------------------------------- | :--------------------------- |
| `lean_enum_schema% T`            | `LeanEnumSchema`             |
| `lean_record_schema% T`          | `LeanRecordSchema Ty`        |
| `lean_tagged_union_schema% T`    | `LeanTaggedUnionSchema Ty`   |
| `lean_rec_tagged_union_schema% T`| `LeanRecTaggedUnionSchema Ty`|
| `lean_rec_object_schema% T`      | `LeanRecObjectSchema Ty`     |
| `lean_mutual_rec_family% T`      | `LeanMutualRecFamily Ty`     |
| `lean_ty% T`                     | `Ty`                         |

Each of the first six *checks* that `T` really has that shape and fails with an
explanation otherwise, so `lean_enum_schema% Option` is an error, not a silently
different schema.  `lean_ty% T` classifies `T` and picks the right one; it is also
what translates the field types, so a record field of a user-defined type expands
into that type's schema in place.

## What is supported

A declaration is translatable when

* it takes no parameters and no indices (`List α` is not a *type*, it is a family —
  the built-in `Ty.list` covers it);
* it is not a unit type (one constructor, no fields) and not void (no constructors),
  since neither has a runtime representation;
* every field type is a primitive (`PrimTy`), a built-in container of a translatable
  type (`Array`, `List`, `Option`, `Prod`, `Thunk`, `Task`), a non-dependent function
  of translatable types, or another translatable declaration.

Anything else is reported as an error rather than approximated.

## Tags

The runtime tag of a constructor is its short name (`"nil"`, `"cons"`); inside a
mutual family it is `"Type.ctor"`, since tags must be distinct across the whole
block.
-/

open Lean Elab Term Meta
open NonEmpty.String

namespace LakeJs.TyMeta

/-! ## Small helpers -/

/-- The last component of a name, as a string. -/
meta def shortName (n : Name) : String :=
  match n with
  | .str _ s => s
  | _        => n.toString

/-- Syntax for a `NonEmptyString` literal. -/
meta def nesSyn (s : String) : MetaM Term := `(NonEmptyString.mk $(quote s) (by decide))

/-- Syntax for a `Ty` abbreviation of a `PrimTy`, e.g. `"nat"` ↦ `Ty.nat`. -/
meta def tyIdent (s : String) : Term := mkIdent ((Name.mkSimple "Ty").str s)

/-- The name of field `i` of a constructor: its binder name when the declaration gives
    one (a `structure` always does), and the positional `_1`, `_2`, … otherwise. -/
meta def fieldName (i : Nat) (n : Name) : String :=
  let s := shortName n
  if n.hasMacroScopes || s.isEmpty || s == "_" then "_" ++ toString (i + 1) else s

/-- The runtime tag of a constructor. -/
meta def ctorTag (inFamily : Bool) (typeName ctorName : Name) : String :=
  if inFamily then shortName typeName ++ "." ++ shortName ctorName else shortName ctorName

/-- The `PrimTy` that a nullary constant denotes, if any. -/
meta def primOfConst? (c : Name) : Option String :=
  match c with
  | ``Bool => some "bool"
  | ``Nat => some "nat"
  | ``Int => some "int"
  | ``UInt8 => some "uint8"
  | ``UInt16 => some "uint16"
  | ``UInt32 => some "uint32"
  | ``UInt64 => some "uint64"
  | ``USize => some "usize"
  | ``Int8 => some "int8"
  | ``Int16 => some "int16"
  | ``Int32 => some "int32"
  | ``Int64 => some "int64"
  | ``ISize => some "isize"
  | ``Char => some "char"
  | ``String => some "string"
  | ``ByteArray => some "byteArray"
  | ``FloatArray => some "floatArray"
  | ``Float => some "float"
  | ``Float32 => some "float32"
  | ``Substring => some "substring"
  | ``String.Pos => some "stringPos"
  | ``Lean.Name => some "name"
  | ``Ordering => some "ordering"
  | _ => none

/-- Does `e` mention any of `names`? -/
meta def mentionsAny (names : List Name) (e : Expr) : Bool :=
  e.find? (fun s => match s with
    | .const c _ => names.contains c
    | _          => false) |>.isSome

/-- The constructors of an inductive, with their fields `(name, type)`. -/
meta def ctorFields (ctorName : Name) : MetaM (List (String × Expr)) := do
  let cv ← getConstInfoCtor ctorName
  forallTelescopeReducing cv.type fun args _ => do
    let fields := args.toList.drop cv.numParams
    fields.zipIdx.mapM fun (fv, i) => do
      let decl ← fv.fvarId!.getDecl
      return (fieldName i decl.userName, ← instantiateMVars decl.type)

/-- Reject declarations this translation cannot describe. -/
meta def checkTranslatable (n : Name) : MetaM InductiveVal := do
  let iv ← getConstInfoInduct n
  if iv.numParams != 0 then
    throwError "'{n}' takes {iv.numParams} parameter(s); only parameterless types are \
      translatable (the built-in `Ty.array`/`Ty.list`/`Ty.option` cover the generic \
      containers)"
  if iv.numIndices != 0 then
    throwError "'{n}' is an indexed family, which has no JavaScript representation"
  if iv.ctors.isEmpty then
    throwError "'{n}' is a void type: it has no values, so it has no representation"
  return iv

/-! ## Classification -/

/-- Which of the six shapes a declaration has. -/
meta inductive SchemaKind where
  | enum | record | taggedUnion | recTaggedUnion | recObject | mutualFamily
  deriving DecidableEq, Repr, Inhabited

/-- The members of the block that member `i` mentions. -/
meta def blockTargets (block : List Name) (n : Name) : MetaM (List Name) := do
  let iv ← getConstInfoInduct n
  let mut out : List Name := []
  for c in iv.ctors do
    for (_, t) in ← ctorFields c do
      for m in block do
        if mentionsAny [m] t && !out.contains m then
          out := m :: out
  return out

/-- Is the "mentions" graph of `block` strongly connected? -/
meta def blockStronglyConnected (block : List Name) : MetaM Bool := do
  let mut edges : List (Name × List Name) := []
  for n in block do
    edges := (n, ← blockTargets block n) :: edges
  let targets (n : Name) : List Name := (edges.find? (·.1 == n)).elim [] (·.2)
  let rec reach (fuel : Nat) (acc : List Name) : List Name :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      let next := acc.foldl (fun a n => (targets n).foldl (fun a m =>
        if a.contains m then a else m :: a) a) acc
      if next.length == acc.length then acc else reach fuel next
  return block.all fun i => (block.all fun j => (reach block.length [i]).contains j)

/-- Classify a declaration. -/
meta def classify (n : Name) : MetaM SchemaKind := do
  let iv ← checkTranslatable n
  let block := iv.all
  if block.length ≥ 2 then
    if ← blockStronglyConnected block then
      return .mutualFamily
  -- a non-mutual declaration (or a member of a "fake mutual" block)
  let mut selfRec := false
  let mut anyField := false
  for c in iv.ctors do
    for (_, t) in ← ctorFields c do
      anyField := true
      if mentionsAny [n] t then selfRec := true
  match iv.ctors with
  | [] => throwError "'{n}' is a void type"
  | [_] =>
      if !anyField then
        throwError "'{n}' is a unit type: it carries no information and is erased"
      return if selfRec then .recObject else .record
  | _ =>
      if !anyField then return .enum
      return if selfRec then .recTaggedUnion else .taggedUnion

/-! ## Translating types -/

mutual

/-- The `Ty` of a Lean type expression. -/
meta partial def tyOfExpr (visiting : List Name) (e₀ : Expr) : MetaM Term := do
  let e ← whnf e₀
  if e.isForall then
    return ← forallTelescopeReducing e fun args body => do
      if body.hasLooseBVars then
        throwError "dependent function type '{e}' has no JavaScript representation"
      let params ← args.mapM fun a => do tyOfExpr visiting (← inferType a)
      let ret ← tyOfExpr visiting body
      `(Ty.fn [$params,*] $ret)
  let args := e.getAppArgs
  match e.getAppFn with
  | .const c _ =>
    match c, args with
    | ``Array, #[a]   => do `(Ty.array $(← tyOfExpr visiting a))
    | ``List, #[a]    => do `(Ty.list $(← tyOfExpr visiting a))
    | ``Thunk, #[a]   => do `(Ty.thunk $(← tyOfExpr visiting a))
    | ``Task, #[a]    => do `(Ty.task $(← tyOfExpr visiting a))
    | ``Option, #[a]  => do `(Ty.option $(← tyOfExpr visiting a))
    | ``Prod, #[a, b] => do `(Ty.prod $(← tyOfExpr visiting a) $(← tyOfExpr visiting b))
    | ``BitVec, #[n]  => do
        let some w := (← whnf n).rawNatLit? | throwError "'BitVec {n}' has a non-literal width"
        if w == 0 then throwError "`BitVec 0` is a unit type and is erased"
        `(Ty.bitvec $(quote w))
    | _, #[] =>
        match primOfConst? c with
        | some s => return tyIdent s
        | none   => tyOfDecl visiting c
    | _, _ => throwError "'{e}' is an applied type; only parameterless declarations and \
        the built-in containers are translatable"
  | .fvar fid =>
    -- A free variable of sort type is a *type parameter* standing for a `Ty`
    -- argument; this is how `LakeJs.TyDerive` translates `Option`/`Prod`, whose
    -- parameters it has introduced as local constants named after the arguments of
    -- the definition being generated.
    let decl ← fid.getDecl
    if args.isEmpty && decl.type.isSort then
      return mkIdent decl.userName
    else
      throwError "'{e}' is not a translatable type"
  | _ => throwError "'{e}' is not a translatable type"

/-- The `Ty` of a user-defined declaration: its schema, wrapped in the matching
    constructor. -/
meta partial def tyOfDecl (visiting : List Name) (n : Name) : MetaM Term := do
  if visiting.contains n then
    throwError "'{n}' refers to itself through a position this translation does not \
      support (only direct occurrences, and occurrences under `Array`/`List`/`Option`/\
      `Thunk`/`Task`, are understood)"
  match ← classify n with
  | .enum            => do `(Ty.enum $(← enumSchemaSyn n))
  | .record          => do `(Ty.record $(← recordSchemaSyn visiting n))
  | .taggedUnion     => do `(Ty.taggedUnion $(← taggedUnionSchemaSyn visiting n))
  | .recTaggedUnion  => do `(Ty.recTaggedUnion $(← recTaggedUnionSchemaSyn visiting n))
  | .recObject       => do `(Ty.recObject $(← recObjectSchemaSyn visiting n))
  | .mutualFamily    => do `(Ty.mutualRecursiveFamily $(← mutualFamilySchemaSyn visiting n))

/-- A `FieldRow` of ordinary (non-recursive) fields. -/
meta partial def fieldRowSyn (visiting : List Name) : List (String × Expr) → MetaM Term
  | [] => `(FieldRow.nil)
  | (nm, t) :: rest => do
      `(FieldRow.cons $(← nesSyn nm) $(← tyOfExpr visiting t) $(← fieldRowSyn visiting rest))

/-- The `LeanEnumSchema` of a field-less, non-recursive, non-mutual `inductive`. -/
meta partial def enumSchemaSyn (n : Name) : MetaM Term := do
  if (← classify n) != .enum then
    throwError "'{n}' is not a plain enum (a non-mutual, non-recursive `inductive` \
      with at least two field-less constructors)"
  let iv ← getConstInfoInduct n
  let tags := iv.ctors.map (fun c => ctorTag false n c)
  match tags with
  | t1 :: t2 :: rest => do
      let restSyn ← rest.toArray.mapM nesSyn
      `(({ name := $(← nesSyn (shortName n))
         , ctor1 := $(← nesSyn t1), ctor2 := $(← nesSyn t2)
         , ctorRest := [$restSyn,*] } : LeanEnumSchema))
  | _ => throwError "'{n}' has fewer than two constructors"

/-- The `LeanRecordSchema` of a one-constructor, non-recursive declaration. -/
meta partial def recordSchemaSyn (visiting : List Name) (n : Name) : MetaM Term := do
  if (← classify n) != .record then
    throwError "'{n}' is not a plain record (a non-mutual, non-recursive declaration \
      with exactly one constructor and at least one field)"
  let iv ← getConstInfoInduct n
  let some c := iv.ctors.head? | throwError "'{n}' has no constructor"
  let fields ← ctorFields c
  `(({ name := $(← nesSyn (shortName n))
     , fields := $(← fieldRowSyn (n :: visiting) fields) } : LeanRecordSchema Ty))

/-- A `CtorRow` of non-recursive constructors. -/
meta partial def ctorRowSyn (visiting : List Name) (tyName : Name) :
    List Name → MetaM Term
  | [] => `(CtorRow.nil)
  | c :: rest => do
      let fields ← ctorFields c
      `(CtorRow.cons $(← nesSyn (ctorTag false tyName c))
          $(← fieldRowSyn visiting fields) $(← ctorRowSyn visiting tyName rest))

/-- The `LeanTaggedUnionSchema` of a non-recursive `inductive` with fields. -/
meta partial def taggedUnionSchemaSyn (visiting : List Name) (n : Name) : MetaM Term := do
  if (← classify n) != .taggedUnion then
    throwError "'{n}' is not a non-recursive tagged union (≥ 2 constructors, at least \
      one with a field, no recursion, no mutual block)"
  let iv ← getConstInfoInduct n
  `(({ name := $(← nesSyn (shortName n))
     , ctors := $(← ctorRowSyn (n :: visiting) n iv.ctors) } : LeanTaggedUnionSchema Ty))

/-- The `SelfTy` of a field of a recursive declaration named `self`. -/
meta partial def selfTyOfExpr (visiting : List Name) (self : Name) (e₀ : Expr) : MetaM Term := do
  let e ← whnf e₀
  if !mentionsAny [self] e then
    return ← `(SelfTy.ty $(← tyOfExpr visiting e))
  if e.isConstOf self then
    return ← `(SelfTy.self)
  if e.isForall then
    return ← forallTelescopeReducing e fun args body => do
      if body.hasLooseBVars then
        throwError "dependent function type '{e}' has no JavaScript representation"
      for a in args do
        if mentionsAny [self] (← inferType a) then
          throwError "'{self}' occurs in a parameter of the function type '{e}': that is \
            a negative occurrence, which has no representation"
      let params ← args.mapM fun a => do tyOfExpr visiting (← inferType a)
      `(SelfTy.fn [$params,*] $(← selfTyOfExpr visiting self body))
  match e.getAppFn, e.getAppArgs with
  | .const ``Array _, #[a]   => do `(SelfTy.array $(← selfTyOfExpr visiting self a))
  | .const ``List _, #[a]    => do `(SelfTy.list $(← selfTyOfExpr visiting self a))
  | .const ``Option _, #[a]  => do `(SelfTy.option $(← selfTyOfExpr visiting self a))
  | .const ``Thunk _, #[a]   => do `(SelfTy.thunk $(← selfTyOfExpr visiting self a))
  | .const ``Task _, #[a]    => do `(SelfTy.task $(← selfTyOfExpr visiting self a))
  | .const ``Prod _, #[a, b] => do
      `(SelfTy.prod $(← selfTyOfExpr visiting self a) $(← selfTyOfExpr visiting self b))
  | _, _ => throwError "'{self}' occurs in '{e}' in a position this translation does not \
      understand (supported: a direct occurrence, and occurrences under \
      `Array`/`List`/`Option`/`Thunk`/`Task`/`Prod`, and the result of a function)"

/-- A `SelfFieldRow`. -/
meta partial def selfFieldRowSyn (visiting : List Name) (self : Name) :
    List (String × Expr) → MetaM Term
  | [] => `(SelfFieldRow.nil)
  | (nm, t) :: rest => do
      `(SelfFieldRow.cons $(← nesSyn nm) $(← selfTyOfExpr visiting self t)
          $(← selfFieldRowSyn visiting self rest))

/-- A `RecCtorRow`. -/
meta partial def recCtorRowSyn (visiting : List Name) (self : Name) : List Name → MetaM Term
  | [] => `(RecCtorRow.nil)
  | c :: rest => do
      `(RecCtorRow.cons $(← nesSyn (ctorTag false self c))
          $(← selfFieldRowSyn visiting self (← ctorFields c))
          $(← recCtorRowSyn visiting self rest))

/-- The `LeanRecTaggedUnionSchema` of a non-mutual recursive `inductive`. -/
meta partial def recTaggedUnionSchemaSyn (visiting : List Name) (n : Name) : MetaM Term := do
  if (← classify n) != .recTaggedUnion then
    throwError "'{n}' is not a non-mutual recursive tagged union"
  let iv ← getConstInfoInduct n
  `(({ name := $(← nesSyn (shortName n))
     , ctors := $(← recCtorRowSyn (n :: visiting) n iv.ctors)
     } : LeanRecTaggedUnionSchema Ty))

/-- The `LeanRecObjectSchema` of a non-mutual recursive one-constructor declaration. -/
meta partial def recObjectSchemaSyn (visiting : List Name) (n : Name) : MetaM Term := do
  if (← classify n) != .recObject then
    throwError "'{n}' is not a non-mutual recursive record"
  let iv ← getConstInfoInduct n
  let some c := iv.ctors.head? | throwError "'{n}' has no constructor"
  `(({ name := $(← nesSyn (shortName n))
     , fields := $(← selfFieldRowSyn (n :: visiting) n (← ctorFields c))
     } : LeanRecObjectSchema Ty))

/-- The `FamTy` of a field of a member of the mutual block `block`.  This mirrors
    `selfTyOfExpr`: a field of a family member may use the family anywhere a field of
    a non-mutual recursive declaration may use *itself*. -/
meta partial def famTyOfExpr (visiting : List Name) (block : List Name) (e₀ : Expr) :
    MetaM Term := do
  let e ← whnf e₀
  let memberIdx? (x : Expr) : Option Nat :=
    match x.getAppFn with
    | .const c _ => if x.getAppArgs.isEmpty then block.idxOf? c else none
    | _ => none
  if !mentionsAny block e then
    return ← `(FamTy.ty $(← tyOfExpr visiting e))
  if let some i := memberIdx? e then
    return ← `(FamTy.memberRef $(quote i))
  if e.isForall then
    return ← forallTelescopeReducing e fun args body => do
      if body.hasLooseBVars then
        throwError "dependent function type '{e}' has no JavaScript representation"
      for a in args do
        if mentionsAny block (← inferType a) then
          throwError "a member of the mutual block occurs in a parameter of the \
            function type '{e}': that is a negative occurrence, which has no \
            representation"
      let params ← args.mapM fun a => do tyOfExpr visiting (← inferType a)
      `(FamTy.fn [$params,*] $(← famTyOfExpr visiting block body))
  match e.getAppFn, e.getAppArgs with
  | .const ``Array _, #[a]   => do `(FamTy.array $(← famTyOfExpr visiting block a))
  | .const ``List _, #[a]    => do `(FamTy.list $(← famTyOfExpr visiting block a))
  | .const ``Option _, #[a]  => do `(FamTy.option $(← famTyOfExpr visiting block a))
  | .const ``Thunk _, #[a]   => do `(FamTy.thunk $(← famTyOfExpr visiting block a))
  | .const ``Task _, #[a]    => do `(FamTy.task $(← famTyOfExpr visiting block a))
  | .const ``Prod _, #[a, b] => do
      `(FamTy.prod $(← famTyOfExpr visiting block a) $(← famTyOfExpr visiting block b))
  | _, _ => throwError "a member of the mutual block occurs in '{e}' in a position this \
      translation does not understand (supported: a direct occurrence, and occurrences \
      under `Array`/`List`/`Option`/`Thunk`/`Task`/`Prod`, and the result of a function)"

/-- A `FamFieldRow`: each field carries a `FamTy`, so an ordinary field carries its
    `Ty` and a field using the family carries the shape of that use. -/
meta partial def famFieldRowSyn (visiting : List Name) (block : List Name) :
    List (String × Expr) → MetaM Term
  | [] => `(FamFieldRow.nil)
  | (nm, t) :: rest => do
      `(FamFieldRow.cons $(← nesSyn nm) $(← famTyOfExpr visiting block t)
          $(← famFieldRowSyn visiting block rest))

/-- A `FamCtorRow`. -/
meta partial def famCtorRowSyn (visiting : List Name) (block : List Name) (tyName : Name) :
    List Name → MetaM Term
  | [] => `(FamCtorRow.nil)
  | c :: rest => do
      `(FamCtorRow.cons $(← nesSyn (ctorTag true tyName c))
          $(← famFieldRowSyn visiting block (← ctorFields c))
          $(← famCtorRowSyn visiting block tyName rest))

/-- A `FamMemberRow`. -/
meta partial def famMemberRowSyn (visiting : List Name) (block : List Name) :
    List Name → MetaM Term
  | [] => `(FamMemberRow.nil)
  | m :: rest => do
      let iv ← checkTranslatable m
      `(FamMemberRow.cons $(← nesSyn (shortName m))
          $(← famCtorRowSyn visiting block m iv.ctors)
          $(← famMemberRowSyn visiting block rest))

/-- The `LeanMutualRecFamily` of a genuinely mutual block, pointing at the member
    `n`. -/
meta partial def mutualFamilySchemaSyn (visiting : List Name) (n : Name) : MetaM Term := do
  if (← classify n) != .mutualFamily then
    throwError "'{n}' is not a member of a genuinely mutual block (a block of ≥ 2 \
      declarations whose reference graph is strongly connected); the non-mutual \
      shapes have their own schemas"
  let iv ← getConstInfoInduct n
  let block := iv.all
  let some idx := block.idxOf? n | throwError "'{n}' is not a member of its own block"
  let visiting := block ++ visiting
  `(({ name := $(← nesSyn (shortName (block.head!)))
     , member := $(quote idx)
     , members := $(← famMemberRowSyn visiting block block)
     } : LeanMutualRecFamily Ty))

end

/-! ## The elaborators -/

/-- `lean_enum_schema% T` — the `LeanEnumSchema` of a field-less `inductive`. -/
elab "lean_enum_schema% " id:ident : term => do
  elabTerm (← enumSchemaSyn (← resolveGlobalConstNoOverload id)) none

/-- `lean_record_schema% T` — the `LeanRecordSchema Ty` of a non-recursive
    one-constructor declaration. -/
elab "lean_record_schema% " id:ident : term => do
  elabTerm (← recordSchemaSyn [] (← resolveGlobalConstNoOverload id)) none

/-- `lean_tagged_union_schema% T` — the `LeanTaggedUnionSchema Ty` of a non-recursive
    `inductive` with fields. -/
elab "lean_tagged_union_schema% " id:ident : term => do
  elabTerm (← taggedUnionSchemaSyn [] (← resolveGlobalConstNoOverload id)) none

/-- `lean_rec_tagged_union_schema% T` — the `LeanRecTaggedUnionSchema Ty` of a
    non-mutual recursive `inductive`. -/
elab "lean_rec_tagged_union_schema% " id:ident : term => do
  elabTerm (← recTaggedUnionSchemaSyn [] (← resolveGlobalConstNoOverload id)) none

/-- `lean_rec_object_schema% T` — the `LeanRecObjectSchema Ty` of a non-mutual
    recursive one-constructor declaration. -/
elab "lean_rec_object_schema% " id:ident : term => do
  elabTerm (← recObjectSchemaSyn [] (← resolveGlobalConstNoOverload id)) none

/-- `lean_mutual_rec_family% T` — the `LeanMutualRecFamily Ty` of a genuinely mutual
    block, pointing at member `T`. -/
elab "lean_mutual_rec_family% " id:ident : term => do
  elabTerm (← mutualFamilySchemaSyn [] (← resolveGlobalConstNoOverload id)) none

/-- `lean_ty% T` — the `Ty` of any translatable Lean declaration. -/
elab "lean_ty% " id:ident : term => do
  elabTerm (← tyOfDecl [] (← resolveGlobalConstNoOverload id)) none

end LakeJs.TyMeta

end
end
