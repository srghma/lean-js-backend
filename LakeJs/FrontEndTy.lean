import Lean

/-!
# The fragment of `Ty` the front end produces

`STy` is the part of `LakeJs.Ty` the front end builds: the terminal types the snapshots
use, the curried function type over them, arrays, `Option`, products, and the layout of a
user-defined type.  It is not a second type language — every `STy` is rendered as the
`LakeJs.Ty` it stands for, both as Lean source (`STy.source`, `STy.rsource`) and as
`LakeJs.TyPretty` prints it (`STy.pretty`).

It lives in its own module so that `LakeJs.FrontEndPrimExterns` — the generated table of
the scalar functions of the runtime, which is stated in terms of `STy` — can be read
before the front end itself.
-/

namespace LakeJs.FrontEnd

open Lean

/-- A fixed-width scalar type.  `USize` is `UInt64` and `ISize` is `Int64`, so neither has
    an entry of its own: they are the same type of the language. -/
inductive SScalar where
  /-- `UInt8`. -/
  | uint8
  /-- `UInt16`. -/
  | uint16
  /-- `UInt32`. -/
  | uint32
  /-- `UInt64`, which is also `USize`. -/
  | uint64
  /-- `Int8`. -/
  | int8
  /-- `Int16`. -/
  | int16
  /-- `Int32`. -/
  | int32
  /-- `Int64`, which is also `ISize`. -/
  | int64
  /-- `Float`. -/
  | float
  /-- `Float32`. -/
  | float32
  deriving BEq, Inhabited, Repr, DecidableEq

namespace SScalar

/-- The constructor of `LakeJs.LeanPrimTy` this scalar is, which is also how
    `LakeJs.TyPretty` prints it. -/
def name : SScalar → String
  | .uint8 => "uint8" | .uint16 => "uint16" | .uint32 => "uint32" | .uint64 => "uint64"
  | .int8 => "int8" | .int16 => "int16" | .int32 => "int32" | .int64 => "int64"
  | .float => "float" | .float32 => "float32"

/-- The Lean type whose values this scalar holds. -/
def leanName : SScalar → Name
  | .uint8 => ``UInt8 | .uint16 => ``UInt16 | .uint32 => ``UInt32 | .uint64 => ``UInt64
  | .int8 => ``Int8 | .int16 => ``Int16 | .int32 => ``Int32 | .int64 => ``Int64
  | .float => ``Float | .float32 => ``Float32

/-- Is this a scalar whose values are whole numbers, so that a literal of it is written
    as the number it is? -/
def isIntegral : SScalar → Bool
  | .float | .float32 => false
  | _ => true

/-- The scalar a Lean type is, if it is one.  `USize` and `ISize` are the 64-bit ones. -/
def ofLeanName? (n : Name) : Option SScalar :=
  if n == ``UInt8 then some .uint8
  else if n == ``UInt16 then some .uint16
  else if n == ``UInt32 then some .uint32
  else if n == ``UInt64 then some .uint64
  else if n == ``USize then some .uint64
  else if n == ``Int8 then some .int8
  else if n == ``Int16 then some .int16
  else if n == ``Int32 then some .int32
  else if n == ``Int64 then some .int64
  else if n == ``ISize then some .int64
  else if n == ``Float then some .float
  else if n == ``Float32 then some .float32
  else none

/-- The value `n` of this scalar, as Lean source: a literal of the Lean type it holds. -/
def litSource (s : SScalar) (n : Nat) : String :=
  match s with
  | .float => "(Float.ofNat " ++ toString n ++ ")"
  | .float32 => "(Float32.ofNat " ++ toString n ++ ")"
  | _ => "(" ++ toString n ++ " : " ++ toString s.leanName ++ ")"

end SScalar

/-- The types this front end can translate: the terminal types the snapshots use, and the
    curried function type built from them. -/
inductive STy where
  /-- `Nat`. -/
  | nat
  /-- `Bool`. -/
  | bool
  /-- `Int`. -/
  | int
  /-- `String`. -/
  | string
  /-- `Char`. -/
  | char
  /-- A fixed-width scalar: `UInt32`, `Int8`, `Float`, … -/
  | scalar (s : SScalar)
  /-- A curried function. -/
  | fn (a b : STy)
  /-- `Array α`. -/
  | array (a : STy)
  /-- `Option α`: a tagged union, `none` at tag `0` and `some` at tag `1`. -/
  | option (a : STy)
  /-- `α × β`: a record of two fields. -/
  | prod (a b : STy)
  /-- A user-defined type with a layout: the `Ty` it is, as Lean source, as the `RTy` it
      is inside a recursive declaration, and as `LakeJs.TyPretty` prints it, together
      with the field types of each of its constructors, in tag order, under the name of
      the Lean constructor. -/
  | data (src rsrc pp : String) (ctors : List (Name × List STy))
  /-- An occurrence of the recursive type being described.  It appears only in the field
      list of a `data`, where reading a field replaces it by the type itself. -/
  | selfRef
  deriving BEq, Inhabited, Repr

namespace STy

/-- The type as Lean source, i.e. as a `LakeJs.Ty`. -/
def source : STy → String
  | .nat => "Ty.nat"
  | .bool => "Ty.bool"
  | .int => "Ty.int"
  | .string => "Ty.string"
  | .char => "Ty.char"
  | .scalar s => "(Ty.prim ." ++ s.name ++ ")"
  | .fn a b => "(Ty.fn " ++ a.source ++ " " ++ b.source ++ ")"
  | .array a => "(Ty.array " ++ a.source ++ ")"
  | .option a => "(Ty.option " ++ a.source ++ ")"
  | .prod a b => "(Ty.prod " ++ a.source ++ " " ++ b.source ++ ")"
  | .data src _ _ _ => src
  | .selfRef => "Ty.nat"  -- unreachable: a self reference is replaced where it is read

/-- The type as Lean source for a type **inside** a recursive declaration, an `RTy`. -/
def rsource : STy → String
  | .nat => "(RTy.prim .nat)"
  | .bool => "(RTy.prim .bool)"
  | .int => "(RTy.prim .int)"
  | .string => "(RTy.prim .string)"
  | .char => "(RTy.prim .char)"
  | .scalar s => "(RTy.prim ." ++ s.name ++ ")"
  | .fn a b => "(RTy.fn " ++ a.rsource ++ " " ++ b.rsource ++ ")"
  | .array a => "(RTy.array " ++ a.rsource ++ ")"
  | .option a => "(RTy.taggedUnion (.skip (.here ⟨" ++ a.rsource ++ ", []⟩ [])))"
  | .prod a b => "(RTy.record ⟨" ++ a.rsource ++ ", " ++ b.rsource ++ ", []⟩)"
  | .data _ rsrc _ _ => rsrc
  | .selfRef => "(RTy.self 0)"

/-- The type as `LakeJs.TyPretty` prints it. -/
def pretty : STy → String
  | .nat => "nat"
  | .bool => "bool"
  | .int => "int"
  | .string => "string"
  | .char => "char"
  | .scalar s => s.name
  | .fn a b => "(fn " ++ a.pretty ++ " " ++ b.pretty ++ ")"
  | .array a => "(array " ++ a.pretty ++ ")"
  -- `Ty.option α` is the tagged union with a field-less constructor and then `α`
  | .option a => "(taggedUnion ()|(" ++ a.pretty ++ "))"
  -- `Ty.prod α β` is the two-field record
  | .prod a b => "(record " ++ a.pretty ++ " " ++ b.pretty ++ ")"
  | .data _ _ pp _ => pp
  | .selfRef => "self#0"

/-- The constructors of a type that has a layout: the tag and the field types of each,
    in the order the layout lists them. -/
def ctors : STy → List (Nat × List STy)
  | .option a => [(0, []), (1, [a])]
  | .prod a b => [(0, [a, b])]
  | .data src rsrc pp cs =>
      cs.zipIdx.map fun (c, i) =>
        (i, c.2.map fun f => if f == .selfRef then .data src rsrc pp cs else f)
  | _ => []

/-- `σ₁ ⇒ ⋯ ⇒ σₙ ⇒ τ`. -/
def arrows (ps : List STy) (τ : STy) : STy := ps.foldr STy.fn τ

end STy

/-- Space separated, the way `Ty.prettyList` prints a list of types. -/
def prettyTyList (ts : List STy) : String :=
  String.intercalate " " (ts.map STy.pretty)

end LakeJs.FrontEnd
