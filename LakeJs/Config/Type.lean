module

public import Lean.Data.Name
public import LakeJs.LeanPrimTy

@[expose] public section

/-!
# The configuration: how each Lean type is represented in JavaScript

| Lean | JavaScript | knob |
| --- | --- | --- |
| `Nat` | a number or a `BigInt` | `natRepr` |
| `Int` | a number or a `BigInt` | `intRepr` |
| `USize` | a number or a `BigInt` | `usizeRepr` |
| `UInt64` | a number or a `BigInt` | `uint64Repr` |
| `Int64` | a number or a `BigInt` | `int64Repr` |
| `ISize` | a number or a `BigInt` | `isizeRepr` |
| `BitVec n`, `n ≥ 53` | a number or a `BigInt` | `bitvecRepr` |
| `BitVec n`, `n < 53` | always a number | — |
| `UInt8/16/32`, `Int8/16/32` | always a number | — |
| `Float`, `Float32` | always a number | — |
| `String.Pos.Raw` | always a number (a UTF-8 byte offset) | — |
| `Char` | always a one-character string | — |
| `Bool` | always a JavaScript boolean | — |
| `String` | always a JavaScript string | — |
| `Array α` | always a JavaScript array | — |

`reprOfPrim` below answers the question for *every* constructor of `LeanPrimTy`, with
no catch-all case, so a terminal type added to the language has to be given a
representation here before this module builds; `knobOfPrim?` says which knob decides
it, and `#guard`s at the end of the module tie both to
`LeanPrimTy.isNumberConfigurable`, so the three cannot drift apart.

## The runtime prelude is one module per knob

The externs are implemented in JavaScript, in `runtime/`, and *which* implementation a
compiled module imports depends on the configuration.  Rather than one whole prelude
per configuration — which would be one file per combination of the knobs — the prelude
is split by knob:

* `lean_runtime_non_configurable.mjs` holds every function whose answer is of a type no
  knob decides (a `Bool`, a `String`, an array, a fixed-width type below 64 bits);
* `lean_runtime_<knob>_num.mjs` and `lean_runtime_<knob>_bigint.mjs` hold the functions
  that answer with the type that knob decides.

`RuntimeGroup` is that split, `runtimeGroupOf` says which module a runtime name comes
from, and `preludeFileOf` names the file.
-/

namespace LakeJs.Config

open Lean

/-- How a numeric Lean type is represented: as a JavaScript number, or as a
    `BigInt`. -/
inductive JsNumRepr where
  /-- A JavaScript number (a double): fast, exact only below `2^53`. -/
  | num
  /-- A JavaScript `BigInt`: exact at every size, and a different JavaScript type —
      a `BigInt` is never `===` to a number and mixing the two throws. -/
  | bigint
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Whether to prefer a dedicated JS TypedArray or a standard generic `Array<T>`. -/
inductive ArrayTypedOrGeneric where
  /-- Use a typed array (e.g. `Uint8Array`, `Float64Array`). -/
  | typedArray
  /-- Use a generic JavaScript `Array<T>`. -/
  | genericArray
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Strategy for modeling `Array UInt64` in JS. -/
inductive ArrayUint64Repr where
  /-- JavaScript `BigUint64Array`. Elements are JS `bigint`. -/
  | bigUint64Array
  /-- Generic JS array (`Array<bigint>` or `Array<number>` per `uint64Repr`). -/
  | genericArray
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Strategy for modeling `Array Int64` in JS. -/
inductive ArrayInt64Repr where
  /-- JavaScript `BigInt64Array`. Elements are JS `bigint`. -/
  | bigInt64Array
  /-- Generic JS array (`Array<bigint>` or `Array<number>` per `int64Repr`). -/
  | genericArray
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Strategy for modeling `Array (BitVec n)` in JS. -/
inductive ArrayBitVecRepr where
  /--
  Rounds up non-power-of-two widths to the smallest fitting typed array:
  - 1..8   => `Uint8Array`
  - 9..16  => `Uint16Array`
  - 17..32 => `Uint32Array`
  - 33..64 => `BigUint64Array` (if `bitvecRepr = .bigint`)
  - > 64   => generic `Array<T>`
  -/
  | roundUpToSmallestTypedArray
  /-- Only exact powers of 2 (8, 16, 32, 64) use typed arrays; odd widths stay generic. -/
  | exactTypedArrayOnly
  /-- All `BitVec` arrays are generic `Array<T>`. -/
  | genericArray
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Strategy for modeling `Array Bool` in JS. -/
inductive ArrayBoolRepr where
  /-- Standard JS `Array<boolean>`. -/
  | genericArray
  /-- Byte buffer `Uint8Array` (stores `0` or `1` per byte; cache/SIMD friendly). -/
  | uint8Array
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Strategy for modeling `Array Char` in JS. -/
inductive ArrayCharRepr where
  /-- `Array<string>` where each element is a 1-character string. -/
  | genericArray
  /-- `Uint32Array` representing Unicode scalar code points directly. -/
  | uint32Array
  deriving Repr, DecidableEq, BEq, Inhabited

/-- The configuration of the backend: every representation decision, in one record.
    The default is the one described at the top of this module. -/
structure JsConfig where
  /-- How `Nat` is represented. -/
  natRepr : JsNumRepr := .bigint
  /-- How `Int` is represented. -/
  intRepr : JsNumRepr := .bigint
  /-- How `USize` is represented. -/
  usizeRepr : JsNumRepr := .bigint
  /-- How `UInt64` is represented. -/
  uint64Repr : JsNumRepr := .bigint
  /-- How `Int64` is represented. -/
  int64Repr : JsNumRepr := .bigint
  /-- How `ISize` is represented. -/
  isizeRepr : JsNumRepr := .bigint
  /-- How a bit vector of `n > 53` bits is represented.  A narrower one fits in a
      number exactly and is one whatever this says. -/
  bitvec53Repr : JsNumRepr := .bigint

  /- --- Array Representations --- -/
  /-- How fixed-width 8/16/32-bit integer arrays are modeled. -/
  arrayFixedIntRepr : ArrayTypedOrGeneric := .typedArray
  /-- How `Array UInt64` is modeled. -/
  arrayUint64Repr   : ArrayUint64Repr := .bigUint64Array
  /-- How `Array Int64` is modeled. -/
  arrayInt64Repr    : ArrayInt64Repr := .bigInt64Array
  /-- How `Array (BitVec n)` is modeled (including 1..7, 9..15, etc.). -/
  arrayBitVecRepr   : ArrayBitVecRepr := .roundUpToSmallestTypedArray
  /-- How `Array Float` and `Array Float32` are modeled. -/
  arrayFloatRepr    : ArrayTypedOrGeneric := .typedArray
  /-- How `Array Bool` is modeled. -/
  arrayBoolRepr     : ArrayBoolRepr := .genericArray
  /-- How `Array Char` is modeled. -/
  arrayCharRepr     : ArrayCharRepr := .genericArray
  deriving Repr, DecidableEq, Inhabited


namespace JsConfig

/-- The default configuration: a `BigInt` everywhere a knob allows one, which is the
    representation that keeps Lean's semantics exactly. -/
def default : JsConfig := {}

/-- Everything that can be a number is a number, `List` is a JavaScript array,
    constructors are positional arrays: the representation
    `purescript-backend-optimizer` uses, and the one the `SnapshotsPBO` outputs were
    written against. -/
def presetPBO : JsConfig where
  natRepr := .num
  intRepr := .num
  usizeRepr := .num
  uint64Repr := .num
  int64Repr := .num
  isizeRepr := .num
  bitvecRepr := .num

/-- The representation that keeps Lean's semantics exactly: `BigInt` everywhere an
    unbounded or 64-bit integer can appear.  This is what the backend did before it was
    configurable. -/
def presetFaithful : JsConfig where
  natRepr := .bigint
  intRepr := .bigint
  usizeRepr := .bigint
  uint64Repr := .bigint
  int64Repr := .bigint
  isizeRepr := .bigint
  bitvecRepr := .bigint




end JsConfig


end LakeJs.Config
