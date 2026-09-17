import LakeJs.Ty
import LakeJs.TyPretty

/-!
# The surface syntax of `Term`: its abstract form, and how it is written down

`LakeJs.Expr.Term` is intrinsically scoped, typed and linked, which is what makes it a
good *internal* language and a bad one to type: a variable is a de Bruijn index, a
global is an index into the module signature, and three of its constructors carry a
proof.  Writing one by hand means counting binders.

This module defines the language one *writes* instead — the text inside `[LEAN| … ]` —
as an ordinary, untyped, first-order syntax tree:

* `RawTy` is a type as it is written, with the two layers of the type language
  (`Ty` and `Ty.RTy`) collapsed into one; `RawTy.toTy` and `RawTy.toRTy` are the two
  readings of it, and `Surface.ofTy` is the way back.
* `STerm`, `SSpine`, `SAlts` and `SBody` mirror the four inductives of `Term` one
  constructor at a time, with *names* where the term has indices and nothing where the
  term has a proof.
* `SEmbed` is a whole embedded fragment: the type it is written at, the signature it is
  written against, the context it is written in, and the code.

`LakeJs.SurfaceParse` reads the text into these trees, `LakeJs.TermElab` turns a tree
into a `Term` (the elaborator), and `LakeJs.TermDeelab` turns a `Term` back into one
(the delaborator).  The printer here is the one the delaborator's output goes through,
so what it prints is exactly what the parser reads.
-/

namespace LakeJs.Surface

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

open LakeJs
open LakeJs.Ty

/-! ## Types as they are written

One tree for both layers.  `RawTy.self` is only meaningful inside a recursive
declaration, and `RawTy.famCtors`/`RawTy.famAlias` only as members of a
`RawTy.family`; the two readings below are what rule the other placements out. -/

/-- A type as it is written in the surface syntax. -/
inductive RawTy where
  /-- A terminal type, by the name `LeanPrimTy.pretty` gives it (`nat`, `string`, …),
      or `typeParam`. -/
  | prim (name : String)
  /-- `(bitvec n)`. -/
  | bitvec (n : Nat)
  /-- `(self i)`: an occurrence of the recursive declaration being written. -/
  | self (i : Nat)
  /-- `(fn [σ, …] τ)`. -/
  | fn (params : List RawTy) (ret : RawTy)
  /-- `(fnProd [σ, …] [τ₁, …])`: a function answering with several values. -/
  | fnProd (params : List RawTy) (rets : List RawTy)
  /-- `(array τ)`. -/
  | array (t : RawTy)
  /-- `(list τ)`. -/
  | list (t : RawTy)
  /-- `(task τ)`. -/
  | task (t : RawTy)
  /-- `(promise τ)`. -/
  | promise (t : RawTy)
  /-- `(thunk τ)`. -/
  | thunk (t : RawTy)
  /-- `(lazy τ)`. -/
  | lazy (t : RawTy)
  /-- `(enum n shift)`. -/
  | enum (n : Nat) (shift : Int)
  /-- `(record [τ, …])`. -/
  | record (fields : List RawTy)
  /-- `(union [[τ, …], …])`. -/
  | union (ctors : List (List RawTy))
  /-- `(recUnion [[τ, …], …])`. -/
  | recUnion (ctors : List (List RawTy))
  /-- `(recObject [τ, …])`. -/
  | recObject (fields : List RawTy)
  /-- `(recAlias τ)`. -/
  | recAlias (t : RawTy)
  /-- `(family i [m, …])`, whose members are `famCtors`/`famAlias` nodes. -/
  | family (members : List RawTy) (i : Nat)
  /-- `(famCtors [[τ, …], …])`: a member of a family that has constructors. -/
  | famCtors (ctors : List (List RawTy))
  /-- `(famAlias τ)`: a member of a family that is a newtype. -/
  | famAlias (t : RawTy)

instance : Inhabited RawTy := ⟨.prim "nat"⟩

/-! ### Printing a written type -/

mutual

/-- A written type, as the text the parser reads back. -/
def RawTy.print : RawTy → String
  | .prim n => n
  | .bitvec n => "(bitvec " ++ toString n ++ ")"
  | .self i => "(self " ++ toString i ++ ")"
  | .fn ps r => "(fn [" ++ RawTy.printList ps ++ "] " ++ RawTy.print r ++ ")"
  | .fnProd ps rs =>
      "(fnProd [" ++ RawTy.printList ps ++ "] [" ++ RawTy.printList rs ++ "])"
  | .array t => "(array " ++ RawTy.print t ++ ")"
  | .list t => "(list " ++ RawTy.print t ++ ")"
  | .task t => "(task " ++ RawTy.print t ++ ")"
  | .promise t => "(promise " ++ RawTy.print t ++ ")"
  | .thunk t => "(thunk " ++ RawTy.print t ++ ")"
  | .lazy t => "(lazy " ++ RawTy.print t ++ ")"
  | .enum n s => "(enum " ++ toString n ++ " " ++ toString s ++ ")"
  | .record fs => "(record [" ++ RawTy.printList fs ++ "])"
  | .union cs => "(union [" ++ RawTy.printCtors cs ++ "])"
  | .recUnion cs => "(recUnion [" ++ RawTy.printCtors cs ++ "])"
  | .recObject fs => "(recObject [" ++ RawTy.printList fs ++ "])"
  | .recAlias t => "(recAlias " ++ RawTy.print t ++ ")"
  | .family ms i => "(family " ++ toString i ++ " [" ++ RawTy.printList ms ++ "])"
  | .famCtors cs => "(famCtors [" ++ RawTy.printCtors cs ++ "])"
  | .famAlias t => "(famAlias " ++ RawTy.print t ++ ")"

/-- Written types, separated by commas. -/
def RawTy.printList : List RawTy → String
  | [] => ""
  | [t] => RawTy.print t
  | t :: ts => RawTy.print t ++ ", " ++ RawTy.printList ts

/-- The constructors of a layout, each a bracketed list of field types. -/
def RawTy.printCtors : List (List RawTy) → String
  | [] => ""
  | [c] => "[" ++ RawTy.printList c ++ "]"
  | c :: cs => "[" ++ RawTy.printList c ++ "], " ++ RawTy.printCtors cs

end

/-! ### Reading a written type as a `Ty` or as a `Ty.RTy` -/

/-- The terminal type a name denotes.  The names are the ones `LeanPrimTy.pretty`
    prints, so a printed type reads back. -/
def primOfName? : String → Option LeanPrimTy
  | "bool" => some .bool
  | "nat" => some .nat
  | "int" => some .int
  | "uint8" => some .uint8
  | "uint16" => some .uint16
  | "uint32" => some .uint32
  | "uint64" => some .uint64
  | "usize" => some .usize
  | "int8" => some .int8
  | "int16" => some .int16
  | "int32" => some .int32
  | "int64" => some .int64
  | "isize" => some .isize
  | "char" => some .char
  | "string" => some .string
  | "byteArray" => some .byteArray
  | "name" => some .name
  | "stringPos" => some .stringPos
  | "substring" => some .substring
  | "stringSlice" => some .stringSlice
  | "float" => some .float
  | "float32" => some .float32
  | "floatArray" => some .floatArray
  | "childProcess" => some .childProcess
  | "shareCommonObject" => some .shareCommonObject
  | "shareCommonState" => some .shareCommonState
  | _ => none

/-- Why a written `enum` may be refused. -/
def enumCountError : String :=
  "an `enum` has at least three constructors: a sum of two field-less constructors is \
   `bool`, one of a single constructor is a unit type, and one of none has no values"

/-- Why a written `record` may be refused. -/
def recordFieldsError : String :=
  "a `record` has at least two fields: a one-field declaration is a newtype, whose \
   wrapper is erased into its field, and a field-less one is a unit type"

/-- Why a written sum may be refused. -/
def unionCtorsError : String :=
  "a tagged union has at least two constructors, at least one of which carries a \
   field: with no field anywhere it is an `enum` or a `bool`"

/-- Why a written `family` may be refused. -/
def familyError : String :=
  "a `family` has at least two members, and the member it selects has to be one of them"

mutual

/-- A written type, read as a closed type.  `self` is refused here: it is only
    meaningful inside a recursive declaration. -/
def RawTy.toTy : RawTy → Except String Ty
  | .prim "typeParam" => .ok .typeParam
  | .prim n =>
      match primOfName? n with
      | some p => .ok (.prim p)
      | none => .error s!"unknown type `{n}`"
  | .bitvec n =>
      if h : 0 < n then .ok (.prim (.bitvec n h))
      else .error "`bitvec 0` is a unit type, which has no representation"
  | .self i => .error s!"`(self {i})` may only appear inside a recursive declaration"
  | .fn ps r => do .ok (.fn (← RawTy.toTys ps) (← RawTy.toTy r))
  | .fnProd ps rs => do
      match ← RawTy.toTys rs with
      | [] => .error "`fnProd` must answer with at least one value"
      | r1 :: rest => .ok (.fn_returnsProd (← RawTy.toTys ps) r1 rest)
  | .array t => do .ok (.array (← RawTy.toTy t))
  | .list t => do .ok (.list (← RawTy.toTy t))
  | .task t => do .ok (.task (← RawTy.toTy t))
  | .promise t => do .ok (.promise (← RawTy.toTy t))
  | .thunk t => do .ok (.thunk (← RawTy.toTy t))
  | .lazy t => do .ok (.lazy (← RawTy.toTy t))
  | .enum n s =>
      match LeanEnumSchema.ofCount? n s with
      | some e => .ok (.enum e)
      | none => .error enumCountError
  | .record fs => do
      match LeanRecordSchema.ofList? (← RawTy.toTys fs) with
      | some r => .ok (.record r)
      | none => .error recordFieldsError
  | .union cs => do
      match LeanTaggedUnionSchema.ofList? (← RawTy.toTyCtors cs) with
      | some tu => .ok (.taggedUnion tu)
      | none => .error unionCtorsError
  | .recUnion cs => do
      match LeanTaggedUnionSchema.ofList? (← RawTy.toRTyCtors cs) with
      | some tu => .ok (.recTaggedUnion ⟨tu⟩)
      | none => .error unionCtorsError
  | .recObject fs => do
      match LeanRecordSchema.ofList? (← RawTy.toRTys fs) with
      | some r => .ok (.recObject ⟨r⟩)
      | none => .error recordFieldsError
  | .recAlias t => do .ok (.recAlias ⟨← RawTy.toRTy t⟩)
  | .family ms i => do
      match LeanMutualRecFamily.ofMembers? (← RawTy.toFams ms) i with
      | some f => .ok (.mutualRecursiveFamily f)
      | none => .error familyError
  | .famCtors _ => .error "`famCtors` is only a member of a `family`"
  | .famAlias _ => .error "`famAlias` is only a member of a `family`"

/-- `RawTy.toTy`, on a list. -/
def RawTy.toTys : List RawTy → Except String (List Ty)
  | [] => .ok []
  | t :: ts => do .ok ((← RawTy.toTy t) :: (← RawTy.toTys ts))

/-- `RawTy.toTy`, on the constructors of a layout. -/
def RawTy.toTyCtors : List (List RawTy) → Except String (List (List Ty))
  | [] => .ok []
  | c :: cs => do .ok ((← RawTy.toTys c) :: (← RawTy.toTyCtors cs))

/-- A written type, read as a type inside a recursive declaration. -/
def RawTy.toRTy : RawTy → Except String RTy
  | .prim "typeParam" => .ok .typeParam
  | .prim n =>
      match primOfName? n with
      | some p => .ok (.prim p)
      | none => .error s!"unknown type `{n}`"
  | .bitvec n =>
      if h : 0 < n then .ok (.prim (.bitvec n h))
      else .error "`bitvec 0` is a unit type, which has no representation"
  | .self i => .ok (.self i)
  | .fn ps r => do .ok (.fn (← RawTy.toRTys ps) (← RawTy.toRTy r))
  | .fnProd ps rs => do
      match ← RawTy.toRTys rs with
      | [] => .error "`fnProd` must answer with at least one value"
      | r1 :: rest => .ok (.fn_returnsProd (← RawTy.toRTys ps) r1 rest)
  | .array t => do .ok (.array (← RawTy.toRTy t))
  | .list t => do .ok (.list (← RawTy.toRTy t))
  | .task t => do .ok (.task (← RawTy.toRTy t))
  | .promise t => do .ok (.promise (← RawTy.toRTy t))
  | .thunk t => do .ok (.thunk (← RawTy.toRTy t))
  | .lazy t => do .ok (.lazy (← RawTy.toRTy t))
  | .enum n s =>
      match LeanEnumSchema.ofCount? n s with
      | some e => .ok (.enum e)
      | none => .error enumCountError
  | .record fs => do
      match LeanRecordSchema.ofList? (← RawTy.toRTys fs) with
      | some r => .ok (.record r)
      | none => .error recordFieldsError
  | .union cs => do
      match LeanTaggedUnionSchema.ofList? (← RawTy.toRTyCtors cs) with
      | some tu => .ok (.taggedUnion tu)
      | none => .error unionCtorsError
  | .recUnion cs => do
      match LeanTaggedUnionSchema.ofList? (← RawTy.toRTyCtors cs) with
      | some tu => .ok (.recTaggedUnion ⟨tu⟩)
      | none => .error unionCtorsError
  | .recObject fs => do
      match LeanRecordSchema.ofList? (← RawTy.toRTys fs) with
      | some r => .ok (.recObject ⟨r⟩)
      | none => .error recordFieldsError
  | .recAlias t => do .ok (.recAlias ⟨← RawTy.toRTy t⟩)
  | .family ms i => do
      match LeanMutualRecFamily.ofMembers? (← RawTy.toFams ms) i with
      | some f => .ok (.mutualRecursiveFamily f)
      | none => .error familyError
  | .famCtors _ => .error "`famCtors` is only a member of a `family`"
  | .famAlias _ => .error "`famAlias` is only a member of a `family`"

/-- `RawTy.toRTy`, on a list. -/
def RawTy.toRTys : List RawTy → Except String (List RTy)
  | [] => .ok []
  | t :: ts => do .ok ((← RawTy.toRTy t) :: (← RawTy.toRTys ts))

/-- `RawTy.toRTy`, on the constructors of a layout. -/
def RawTy.toRTyCtors : List (List RawTy) → Except String (List (List RTy))
  | [] => .ok []
  | c :: cs => do .ok ((← RawTy.toRTys c) :: (← RawTy.toRTyCtors cs))

/-- A written member of a mutual family.  A member written with a single constructor
    carrying a single field is a newtype member, and one with a single constructor
    carrying several is a record member. -/
def RawTy.toFam : RawTy → Except String FamMember
  | .famCtors cs => do
      match ← RawTy.toRTyCtors cs with
      | [[f]] => .ok (.alias f)
      | [fs] =>
          match LeanRecordSchema.ofList? fs with
          | some r => .ok (.record r)
          | none => .error recordFieldsError
      | l =>
          match LeanTaggedUnionSchema.ofList? l with
          | some tu => .ok (.ctors tu)
          | none => .error unionCtorsError
  | .famAlias t => do .ok (.alias (← RawTy.toRTy t))
  | _ => .error "a member of a `family` is a `famCtors` or a `famAlias`"

/-- `RawTy.toFam`, on a list. -/
def RawTy.toFams : List RawTy → Except String (List FamMember)
  | [] => .ok []
  | m :: ms => do .ok ((← RawTy.toFam m) :: (← RawTy.toFams ms))

end

/-! ### Writing a type down -/

/-- A terminal type as a written type. -/
def ofPrim : LeanPrimTy → RawTy
  | .bitvec n _ => .bitvec n
  | p => .prim p.pretty

mutual

/-- A closed type, as it is written. -/
def ofTy : Ty → RawTy
  | .prim p => ofPrim p
  | .typeParam => .prim "typeParam"
  | .fn ps r => .fn (ofTys ps) (ofTy r)
  | .fn_returnsProd ps r1 rs => .fnProd (ofTys ps) (ofTy r1 :: ofTys rs)
  | .array t => .array (ofTy t)
  | .list t => .list (ofTy t)
  | .task t => .task (ofTy t)
  | .promise t => .promise (ofTy t)
  | .thunk t => .thunk (ofTy t)
  | .lazy t => .lazy (ofTy t)
  | .enum e => .enum e.nOfConstructors e.shift
  | .record fs => .record (ofTyA2 fs)
  | .taggedUnion cs => .union (ofTyTU cs)
  | .recTaggedUnion ⟨cs⟩ => .recUnion (ofRTyTU cs)
  | .recObject ⟨fs⟩ => .recObject (ofRTyA2 fs)
  | .recAlias ⟨t⟩ => .recAlias (ofRTy t)
  | .mutualRecursiveFamily f => ofFamily f

/-- `ofTy`, on a list. -/
def ofTys : List Ty → List RawTy
  | [] => []
  | t :: ts => ofTy t :: ofTys ts

/-- `ofTy`, on the constructors of a layout. -/
def ofTyCtors : List (List Ty) → List (List RawTy)
  | [] => []
  | c :: cs => ofTys c :: ofTyCtors cs

/-- `ofTy`, on the fields of a record. -/
def ofTyA2 : LeanRecordSchema Ty → List RawTy
  | ⟨a, b, rest⟩ => ofTy a :: ofTy b :: ofTys rest

/-- `ofTy`, on the fields of a constructor that has at least one. -/
def ofTyNE : NonEmptyList Ty → List RawTy
  | ⟨a, as⟩ => ofTy a :: ofTys as

/-- `ofTy`, on the constructors of a tagged union. -/
def ofTyTU : LeanTaggedUnionSchema Ty → List (List RawTy)
  | .payloadFirst f n r => ofTyNE f :: ofTys n :: ofTyCtors r
  | .skip rest => [] :: ofTyCP rest

/-- `ofTy`, on the constructors that follow a field-less one. -/
def ofTyCP : CtorsWithPayload Ty → List (List RawTy)
  | .here f r => ofTyNE f :: ofTyCtors r
  | .skip rest => [] :: ofTyCP rest

/-- A type inside a recursive declaration, as it is written. -/
def ofRTy : RTy → RawTy
  | .self i => .self i
  | .prim p => ofPrim p
  | .typeParam => .prim "typeParam"
  | .fn ps r => .fn (ofRTys ps) (ofRTy r)
  | .fn_returnsProd ps r1 rs => .fnProd (ofRTys ps) (ofRTy r1 :: ofRTys rs)
  | .array t => .array (ofRTy t)
  | .list t => .list (ofRTy t)
  | .task t => .task (ofRTy t)
  | .promise t => .promise (ofRTy t)
  | .thunk t => .thunk (ofRTy t)
  | .lazy t => .lazy (ofRTy t)
  | .enum e => .enum e.nOfConstructors e.shift
  | .record fs => .record (ofRTyA2 fs)
  | .taggedUnion cs => .union (ofRTyTU cs)
  | .recTaggedUnion ⟨cs⟩ => .recUnion (ofRTyTU cs)
  | .recObject ⟨fs⟩ => .recObject (ofRTyA2 fs)
  | .recAlias ⟨t⟩ => .recAlias (ofRTy t)
  | .mutualRecursiveFamily f => ofFamily f

/-- `ofRTy`, on a list. -/
def ofRTys : List RTy → List RawTy
  | [] => []
  | t :: ts => ofRTy t :: ofRTys ts

/-- `ofRTy`, on the constructors of a layout. -/
def ofRTyCtors : List (List RTy) → List (List RawTy)
  | [] => []
  | c :: cs => ofRTys c :: ofRTyCtors cs

/-- `ofRTy`, on the fields of a record. -/
def ofRTyA2 : LeanRecordSchema RTy → List RawTy
  | ⟨a, b, rest⟩ => ofRTy a :: ofRTy b :: ofRTys rest

/-- `ofRTy`, on the fields of a constructor that has at least one. -/
def ofRTyNE : NonEmptyList RTy → List RawTy
  | ⟨a, as⟩ => ofRTy a :: ofRTys as

/-- `ofRTy`, on the constructors of a tagged union. -/
def ofRTyTU : LeanTaggedUnionSchema RTy → List (List RawTy)
  | .payloadFirst f n r => ofRTyNE f :: ofRTys n :: ofRTyCtors r
  | .skip rest => [] :: ofRTyCP rest

/-- `ofRTy`, on the constructors that follow a field-less one. -/
def ofRTyCP : CtorsWithPayload RTy → List (List RawTy)
  | .here f r => ofRTyNE f :: ofRTyCtors r
  | .skip rest => [] :: ofRTyCP rest

/-- A member of a mutual family, as it is written: every member is written as its
    constructors, so a record member is one constructor and a newtype member is one
    constructor of one field. -/
def ofFam : FamMember → RawTy
  | .ctors cs => .famCtors (ofRTyTU cs)
  | .record fs => .famCtors [ofRTyA2 fs]
  | .alias t => .famAlias (ofRTy t)

/-- `ofFam`, on a list. -/
def ofFams : List FamMember → List RawTy
  | [] => []
  | m :: ms => ofFam m :: ofFams ms

/-- A mutual family, as it is written: its members and the number of the one this type
    is. -/
def ofFamily : LeanMutualRecFamily RTy → RawTy
  | .selectedThenMore before current next after =>
      .family (ofFams before ++ ofFam current :: ofFam next :: ofFams after)
        (ofFams before).length
  | .selectedLast first before current =>
      .family (ofFam first :: (ofFams before ++ [ofFam current]))
        ((ofFams before).length + 1)

end

/-- A closed type, as the text the parser reads back. -/
def tyText (t : Ty) : String := (ofTy t).print

/-! ## Terms as they are written -/

/-- A constant of a terminal type, as it is written.  A floating point number is
    written as the bits of its representation, so that the text is exact. -/
inductive SLit where
  | bool (b : Bool)
  | nat (n : Nat)
  | int (i : Int)
  /-- `(lit bitvec w v)`: `v`, at `w` bits. -/
  | bitvec (w : Nat) (v : Nat)
  | uint8 (n : Nat)
  | uint16 (n : Nat)
  | uint32 (n : Nat)
  | uint64 (n : Nat)
  | usize (n : Nat)
  | int8 (i : Int)
  | int16 (i : Int)
  | int32 (i : Int)
  | int64 (i : Int)
  | isize (i : Int)
  | char (c : Char)
  | string (s : String)
  | byteArray (bs : List Nat)
  | name (n : String)
  | stringPos (p : Nat)
  | substring (s : String) (startPos stopPos : Nat)
  | stringSlice (s : String) (startPos stopPos : Nat)
  /-- The bits of a `Float`. -/
  | float (bits : UInt64)
  /-- The bits of a `Float32`. -/
  | float32 (bits : UInt32)
  /-- The bits of each element of a `FloatArray`. -/
  | floatArray (bits : List UInt64)
  deriving Inhabited

/-- An operation that is JavaScript's rather than Lean's, as it is written. -/
inductive SOp where
  | cast (from_ to_ : Ty)
  | boolAnd
  | boolOr
  | boolNot
  | boolBEq
  | charBEq
  | natSubExact
  | toStr (t : Ty)
  deriving Inhabited

/-- A binder: the name it introduces and the type it has. -/
abbrev SParam := String × Ty

mutual

/-- A term as it is written: `Term`, with names for its indices and nothing for its
    proofs. -/
inductive STerm where
  /-- A name: a variable of the context, or a declaration of the signature. -/
  | var (name : String)
  /-- `(lit …)`. -/
  | lit (l : SLit)
  /-- `(fn [x : σ, …] body)`. -/
  | lam (params : List SParam) (body : STerm)
  /-- `(app f a …)`. -/
  | app (f : STerm) (args : SSpine)
  /-- `(prodFn [x : σ, …] r₁ …)`. -/
  | lamProd (params : List SParam) (rets : SSpine)
  /-- `(callProd i f a …)`. -/
  | callProd (i : Nat) (f : STerm) (args : SSpine)
  /-- `(extern lean_nat_add τ …)`, the type arguments being a polymorphic extern's. -/
  | extern (name : String) (tyArgs : List Ty)
  /-- `(op … a …)`. -/
  | op (o : SOp) (args : SSpine)
  /-- `(let x : σ = e body)`. -/
  | letE (name : String) (ty : Ty) (val : STerm) (body : STerm)
  /-- `(if c t e)`. -/
  | ite (c t e : STerm)
  /-- `(ctor i : τ a …)`. -/
  | ctor (i : Nat) (ty : Ty) (args : SSpine)
  /-- `(proj i j e)`. -/
  | proj (i j : Nat) (e : STerm)
  /-- `(tagOf e)`. -/
  | tagOf (e : STerm)
  /-- `(lazy e)`: a function of no arguments answering with `e`. -/
  | lazyMk (e : STerm)
  /-- `(force e)`: call one. -/
  | lazyForce (e : STerm)
  /-- `(case scrut (tag n e) … (default e))`. -/
  | caseTag (scrut : STerm) (alts : SAlts)
  /-- `(loop [x : σ = e, …] body)`. -/
  | loop (slots : List SParam) (inits : SSpine) (body : SBody)
  /-- `(join j [x : σ, …] : τ body rest)`. -/
  | joinPoint (name : String) (params : List SParam) (ret : Ty) (body : STerm) (rest : STerm)
  /-- `(jump j a …)`. -/
  | jump (name : String) (args : SSpine)

/-- A written list of terms. -/
inductive SSpine where
  | nil
  | cons (t : STerm) (rest : SSpine)

/-- The written branches of a case. -/
inductive SAlts where
  | deflt (t : STerm)
  | cons (tag : Nat) (t : STerm) (rest : SAlts)

/-- A written loop body. -/
inductive SBody where
  | ret (t : STerm)
  | cont (args : SSpine)
  | letB (name : String) (ty : Ty) (val : STerm) (body : SBody)
  | iteB (c : STerm) (t e : SBody)
  /-- `(joinB j [x : σ, …] : τ body rest)`: a join point bound inside a loop block. -/
  | joinPointB (name : String) (params : List SParam) (ret : Ty) (body : STerm)
      (rest : SBody)

end

/-- A whole embedded fragment: what `[LEAN| … ]` holds. -/
structure SEmbed where
  /-- The type the code is written at, where it is written down. -/
  sig : Option Ty := none
  /-- The signature the code is written against: the top-level declarations it may
      name, in the order the signature declares them. -/
  glob : List SParam := []
  /-- The context the code is written in: de Bruijn index 0 first. -/
  vars : List SParam := []
  /-- The code. -/
  code : STerm

/-! ### Printing a written term -/

/-- `n` spaces. -/
def pad (n : Nat) : String := String.join (List.replicate n " ")

/-- A string, in double quotes, with the four characters that would end it or confuse a
    reader escaped. -/
def quoteString (s : String) : String :=
  let esc := s.toList.foldl (init := "") fun acc c =>
    acc ++
      (if c == '"' then "\\\""
       else if c == '\\' then "\\\\"
       else if c == '\n' then "\\n"
       else if c == '\t' then "\\t"
       else if c == '\r' then "\\r"
       else String.singleton c)
  "\"" ++ esc ++ "\""

/-- A character, in single quotes, escaped as a string is. -/
def quoteChar (c : Char) : String :=
  let body :=
    if c == '\'' then "\\'"
    else if c == '\\' then "\\\\"
    else if c == '\n' then "\\n"
    else if c == '\t' then "\\t"
    else if c == '\r' then "\\r"
    else String.singleton c
  "'" ++ body ++ "'"

/-- A list of natural numbers, in brackets. -/
def printNats (ns : List Nat) : String :=
  "[" ++ String.intercalate ", " (ns.map toString) ++ "]"

/-- A constant, as it is written. -/
def SLit.print : SLit → String
  | .bool b => "bool " ++ toString b
  | .nat n => "nat " ++ toString n
  | .int i => "int " ++ toString i
  | .bitvec w v => "bitvec " ++ toString w ++ " " ++ toString v
  | .uint8 n => "uint8 " ++ toString n
  | .uint16 n => "uint16 " ++ toString n
  | .uint32 n => "uint32 " ++ toString n
  | .uint64 n => "uint64 " ++ toString n
  | .usize n => "usize " ++ toString n
  | .int8 i => "int8 " ++ toString i
  | .int16 i => "int16 " ++ toString i
  | .int32 i => "int32 " ++ toString i
  | .int64 i => "int64 " ++ toString i
  | .isize i => "isize " ++ toString i
  | .char c => "char " ++ quoteChar c
  | .string s => "string " ++ quoteString s
  | .byteArray bs => "byteArray " ++ printNats bs
  | .name n => "name " ++ quoteString n
  | .stringPos p => "stringPos " ++ toString p
  | .substring s a b =>
      "substring " ++ quoteString s ++ " " ++ toString a ++ " " ++ toString b
  | .stringSlice s a b =>
      "stringSlice " ++ quoteString s ++ " " ++ toString a ++ " " ++ toString b
  | .float bits => "float " ++ toString bits.toNat
  | .float32 bits => "float32 " ++ toString bits.toNat
  | .floatArray bs => "floatArray " ++ printNats (bs.map (·.toNat))

/-- An operation that is JavaScript's rather than Lean's, as it is written. -/
def SOp.print : SOp → String
  | .cast a b => "cast " ++ tyText a ++ " " ++ tyText b
  | .boolAnd => "boolAnd"
  | .boolOr => "boolOr"
  | .boolNot => "boolNot"
  | .boolBEq => "boolBEq"
  | .charBEq => "charBEq"
  | .natSubExact => "natSubExact"
  | .toStr t => "toStr " ++ tyText t

/-- A list of binders, as it is written: `[x : nat, y : bool]`. -/
def printParams (ps : List SParam) : String :=
  "[" ++ String.intercalate ", " (ps.map fun (n, t) => n ++ " : " ++ tyText t) ++ "]"

mutual

/-- A written term, as the lines of an indented s-expression. -/
def STerm.printLines (ind : Nat) : STerm → List String
  | .var n => [pad ind ++ n]
  | .lit l => [pad ind ++ "(lit " ++ l.print ++ ")"]
  | .extern n [] => [pad ind ++ "(extern " ++ n ++ ")"]
  | .extern n ts =>
      [pad ind ++ "(extern " ++ n ++ " "
        ++ String.intercalate " " (ts.map tyText) ++ ")"]
  | .lam ps b =>
      (pad ind ++ "(fn " ++ printParams ps) :: STerm.printLines (ind + 2) b
        ++ [pad ind ++ ")"]
  | .app f args =>
      (pad ind ++ "(app") :: STerm.printLines (ind + 2) f
        ++ SSpine.printLines (ind + 2) args ++ [pad ind ++ ")"]
  | .lamProd ps rets =>
      (pad ind ++ "(prodFn " ++ printParams ps) :: SSpine.printLines (ind + 2) rets
        ++ [pad ind ++ ")"]
  | .callProd i f args =>
      (pad ind ++ "(callProd " ++ toString i) :: STerm.printLines (ind + 2) f
        ++ SSpine.printLines (ind + 2) args ++ [pad ind ++ ")"]
  | .op o args =>
      (pad ind ++ "(op " ++ o.print) :: SSpine.printLines (ind + 2) args
        ++ [pad ind ++ ")"]
  | .letE n t v b =>
      (pad ind ++ "(let " ++ n ++ " : " ++ tyText t ++ " =")
        :: STerm.printLines (ind + 2) v ++ STerm.printLines (ind + 2) b
        ++ [pad ind ++ ")"]
  | .ite c t e =>
      (pad ind ++ "(if") :: STerm.printLines (ind + 2) c
        ++ STerm.printLines (ind + 2) t ++ STerm.printLines (ind + 2) e
        ++ [pad ind ++ ")"]
  | .ctor i t args =>
      (pad ind ++ "(ctor " ++ toString i ++ " : " ++ tyText t)
        :: SSpine.printLines (ind + 2) args ++ [pad ind ++ ")"]
  | .proj i j e =>
      (pad ind ++ "(proj " ++ toString i ++ " " ++ toString j)
        :: STerm.printLines (ind + 2) e ++ [pad ind ++ ")"]
  | .tagOf e =>
      (pad ind ++ "(tagOf") :: STerm.printLines (ind + 2) e ++ [pad ind ++ ")"]
  | .lazyMk e =>
      (pad ind ++ "(lazy") :: STerm.printLines (ind + 2) e ++ [pad ind ++ ")"]
  | .lazyForce e =>
      (pad ind ++ "(force") :: STerm.printLines (ind + 2) e ++ [pad ind ++ ")"]
  | .caseTag s alts =>
      (pad ind ++ "(case") :: STerm.printLines (ind + 2) s
        ++ SAlts.printLines (ind + 2) alts ++ [pad ind ++ ")"]
  | .loop slots inits body =>
      (pad ind ++ "(loop " ++ printParams slots) :: SSpine.printLines (ind + 2) inits
        ++ SBody.printLines (ind + 2) body ++ [pad ind ++ ")"]
  | .joinPoint n ps ret body rest =>
      (pad ind ++ "(join " ++ n ++ " " ++ printParams ps ++ " : " ++ tyText ret)
        :: STerm.printLines (ind + 2) body ++ STerm.printLines (ind + 2) rest
        ++ [pad ind ++ ")"]
  | .jump n args =>
      (pad ind ++ "(jump " ++ n) :: SSpine.printLines (ind + 2) args ++ [pad ind ++ ")"]

/-- The terms of a written spine, one after another. -/
def SSpine.printLines (ind : Nat) : SSpine → List String
  | .nil => []
  | .cons t rest => STerm.printLines ind t ++ SSpine.printLines ind rest

/-- The written branches of a case. -/
def SAlts.printLines (ind : Nat) : SAlts → List String
  | .deflt t =>
      (pad ind ++ "(default") :: STerm.printLines (ind + 2) t ++ [pad ind ++ ")"]
  | .cons tag t rest =>
      ((pad ind ++ "(tag " ++ toString tag) :: STerm.printLines (ind + 2) t
        ++ [pad ind ++ ")"]) ++ SAlts.printLines ind rest

/-- A written loop body. -/
def SBody.printLines (ind : Nat) : SBody → List String
  | .ret t => (pad ind ++ "(ret") :: STerm.printLines (ind + 2) t ++ [pad ind ++ ")"]
  | .cont args =>
      (pad ind ++ "(cont") :: SSpine.printLines (ind + 2) args ++ [pad ind ++ ")"]
  | .letB n t v b =>
      (pad ind ++ "(letB " ++ n ++ " : " ++ tyText t ++ " =")
        :: STerm.printLines (ind + 2) v ++ SBody.printLines (ind + 2) b
        ++ [pad ind ++ ")"]
  | .iteB c t e =>
      (pad ind ++ "(ifB") :: STerm.printLines (ind + 2) c
        ++ SBody.printLines (ind + 2) t ++ SBody.printLines (ind + 2) e
        ++ [pad ind ++ ")"]
  | .joinPointB n ps ret body rest =>
      (pad ind ++ "(joinB " ++ n ++ " " ++ printParams ps ++ " : " ++ tyText ret)
        :: STerm.printLines (ind + 2) body ++ SBody.printLines (ind + 2) rest
        ++ [pad ind ++ ")"]

end

/-- A written term, as one string. -/
def STerm.print (t : STerm) : String := String.intercalate "\n" (t.printLines 0)

/-- The binders of a header section, as they are written. -/
def printDecls (ps : List SParam) : String :=
  String.intercalate ", " (ps.map fun (n, t) => n ++ " : " ++ tyText t)

/-- A whole fragment, as the text between `[LEAN|` and `]`. -/
def SEmbed.print (e : SEmbed) : String :=
  let sigLine := match e.sig with
    | none => "sig"
    | some t => "sig " ++ tyText t
  String.intercalate "\n"
    [ sigLine
    , "|glob " ++ printDecls e.glob
    , "|vars " ++ printDecls e.vars
    , "|" ] ++ "\n" ++ e.code.print

end LakeJs.Surface
