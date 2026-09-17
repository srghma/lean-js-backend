module

public import Init.Prelude
public import Init.Data.ToString.Basic

@[expose] public section

namespace LakeJs

/-!
# `LeanPrimTy`: the terminal (leaf) types

These are exactly the types of the compiler's type language that

* contain **no** other type — they are leaves of a `Ty`, and
* are **built in** — the backend knows their JavaScript representation directly,
  without consulting a user-written schema.

They used to be constructors of `Ty` itself.  Splitting them off means

* a backend that only has to decide "how is a scalar represented?" pattern-matches on
  `LeanPrimTy`, a small type with no recursion and no indexed families, and can `deriving
  DecidableEq`/`Repr` freely;
* `Ty` is left with just the six *compound* shapes plus the handful of type
  constructors (`fn`, `array`, `list`, `task`, `promise`, `thunk`) and one
  `Ty.prim` leaf, so a traversal over the tree structure of a type has a dozen cases
  instead of forty;
* the "how is this rendered in JS?" configuration (`number` vs `bigint`, …) is a
  function `LeanPrimTy → …` — see `LakeJs.Config` — rather than a function on `Ty` with
  unreachable cases.

`Ty` re-exports every one of them as an abbreviation (`Ty.nat` is `Ty.prim .nat`), so
existing code that writes `.nat`, `.uint32`, `.bitvec 32`, … is unaffected.

Note that there is **no** `unit` and **no** `void`: a type with one value carries no
information and is erased before it reaches `LeanPrimTy`, and a type with no values has no
runtime representation at all.  This is also why `bitvec n` requires `0 < n`:
`BitVec 0` is a unit type.
-/

/-- A terminal type: a leaf of a `Ty`, with a built-in LEAN TYPE!!! representation

(not javascript!
The term deals only with lean type model,
then lean type model is optimized,
AND ONLY THEN (maybe optimized again and) printed into javascript). -/
inductive LeanPrimTy where
  /-- In JS: `boolean`. -/
  | bool      : LeanPrimTy
  /-- In JS: configurable (`number` or `bigint`). -/
  | nat       : LeanPrimTy
  /-- In JS: configurable (`number` or `bigint`). -/
  | int       : LeanPrimTy
  /-- IF `n` is less THEN 32 then nonconfigurable (`number`), ELSE configurable
      (`number` or `bigint`).  `BitVec 0` has a single value, i.e. it is a unit type,
      so `n` must be positive — the proof is an auto-param, so `.bitvec 32` just
      works. -/
  | bitvec    : (n : Nat) → (h_pos : 0 < n := by decide) → LeanPrimTy
  /-- In JS: `number`. -/
  | uint8     : LeanPrimTy
  /-- In JS: `number`. -/
  | uint16    : LeanPrimTy
  /-- In JS: `number`. -/
  | uint32    : LeanPrimTy
  /-- In JS: configurable (`number` or `bigint`). -/
  | uint64    : LeanPrimTy
  /-- In JS: configurable (`number` or `bigint`). -/
  | usize     : LeanPrimTy
  /-- In JS: `number`. -/
  | int8      : LeanPrimTy
  /-- In JS: `number`. -/
  | int16     : LeanPrimTy
  /-- In JS: `number`. -/
  | int32     : LeanPrimTy
  /-- In JS: configurable (`number` or `bigint`). -/
  | int64     : LeanPrimTy
  /-- In JS: configurable (`number` or `bigint`). -/
  | isize     : LeanPrimTy
  /-- In JS: `string`. -/
  | char      : LeanPrimTy
  /-- In JS: `string`. -/
  | string    : LeanPrimTy
  /-- In JS: `Uint8Array` / `ArrayBuffer`. -/
  | byteArray : LeanPrimTy
  /-- A `Lean.Name`. In JS: `string`. -/
  | name      : LeanPrimTy
  /-- A position in a string — like `.uint32`, but strictly non-negative. -/
  | stringPos : LeanPrimTy
  /-- In JS: `{ str: string, startPos: number, stopPos: number }`. -/
  | substring : LeanPrimTy
  /-- `.substring` or `.string`? -/
  | stringSlice : LeanPrimTy
  /-- In JS: `number` (IEEE 754 64-bit). -/
  | float     : LeanPrimTy
  /-- In JS: `number` (IEEE 754 32-bit, `Math.fround`). -/
  | float32   : LeanPrimTy
  /-- In JS: `Float64Array`. -/
  | floatArray : LeanPrimTy
  /-- In JS (node only): a `ChildProcess` handle. -/
  | childProcess : LeanPrimTy
  /-- In JS: `object` / `any`. -/
  | shareCommonObject : LeanPrimTy
  /-- In JS: a `Map` / cache object. -/
  | shareCommonState  : LeanPrimTy
  deriving Repr, DecidableEq, Inhabited

namespace LeanPrimTy

/-- A one-word rendering, for debugging and error messages. -/
def pretty : LeanPrimTy → String
  | .bitvec n _ => "(bitvec " ++ toString n ++ ")"
  | .bool => "bool" | .nat => "nat" | .int => "int"
  | .uint8 => "uint8" | .uint16 => "uint16" | .uint32 => "uint32" | .uint64 => "uint64"
  | .usize => "usize"
  | .int8 => "int8" | .int16 => "int16" | .int32 => "int32" | .int64 => "int64"
  | .isize => "isize"
  | .char => "char" | .string => "string" | .byteArray => "byteArray" | .name => "name"
  | .stringPos => "stringPos" | .substring => "substring" | .stringSlice => "stringSlice"
  | .float => "float" | .float32 => "float32" | .floatArray => "floatArray"
  | .childProcess => "childProcess"
  | .shareCommonObject => "shareCommonObject" | .shareCommonState => "shareCommonState"

instance : ToString LeanPrimTy where
  toString := pretty

/-- Is the JavaScript representation of this type configurable (`number` vs
    `bigint`)?  A bit vector of fewer than 32 bits always fits in a `number`. -/
def isNumberConfigurable : LeanPrimTy → Bool
  | .nat | .int | .uint64 | .usize | .int64 | .isize => true
  | .bitvec n _ => 32 ≤ n
  | _ => false

end LeanPrimTy

end LakeJs

end
