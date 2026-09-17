module
prelude
public import LakeJs.LeanPrimTy
public import Init.Data.String.Slice
@[expose] public section
namespace LakeJs

/-- A constant of a terminal type: one constructor per constructor of `LeanPrimTy`,
    holding the Lean value itself rather than a rendering of it, and indexed by the
    terminal type it is a constant *of*.  So a literal is a constant of the Lean type
    model, and turning it into JavaScript source is the printer's business alone
    (`LakeJs.EmitJs.litExpr`).
    Three constructors of `LeanPrimTy` are missing here, on purpose: `.childProcess`,
    `.shareCommonObject` and `.shareCommonState` are run-time handles, and a handle has
    no constant — `Lit .childProcess` is an empty type, which is the right statement.
    `Float` and `Float32` are held as the Lean floats they are.  That is why
    `LakeJs.FloatDecide` exists: a fact about them is settled by `float_decide`, a
    `native_decide` that first checks the goal really is about floating point. -/
inductive LeanPrimLit : LeanPrimTy → Type
  | bool   : Bool → LeanPrimLit .bool
  | nat    : Nat → LeanPrimLit .nat
  | int    : Int → LeanPrimLit .int
  | bitvec : ∀ {n : Nat} {h_positive : 0 < n}, BitVec n → LeanPrimLit (.bitvec n h_positive)
  | uint8  : UInt8 → LeanPrimLit .uint8
  | uint16 : UInt16 → LeanPrimLit .uint16
  | uint32 : UInt32 → LeanPrimLit .uint32
  | uint64 : UInt64 → LeanPrimLit .uint64
  | usize  : USize → LeanPrimLit .usize
  | int8   : Int8 → LeanPrimLit .int8
  | int16  : Int16 → LeanPrimLit .int16
  | int32  : Int32 → LeanPrimLit .int32
  | int64  : Int64 → LeanPrimLit .int64
  | isize  : ISize → LeanPrimLit .isize
  | char   : Char → LeanPrimLit .char
  | string : String → LeanPrimLit .string
  | stringPos : Nat → LeanPrimLit .stringPos
  | substring : Substring → LeanPrimLit .substring
  | stringSlice : String.Slice → LeanPrimLit .stringSlice
  | float  : Float → LeanPrimLit .float
  | float32 : Float32 → LeanPrimLit .float32
