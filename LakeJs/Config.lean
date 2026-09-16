module

public import Lean.Data.Name

@[expose] public section

open Lean

namespace LakeJs.Config

/-!
| Lean | JavaScript | knob |
| --- | --- | --- |
| `Nat` | a number (default) or a `BigInt` | `natRepr` |
| `Int` | a number (default) or a `BigInt` | `intRepr` |
| `UInt8/16/32`, `Int8/16/32` | always a number | — |
| `USize` | a `BigInt` (default) or a number | `usizeRepr` |
| `UInt64` | a `BigInt` (default) or a number | `uint64Repr` |
| `Int64` | a `BigInt` (default) or a number | `int64Repr` |
| `Float`, `Float32` | always a number | — |
| `Char` | always a string | — |
| `Bool` | always a JavaScript boolean | — |
| `String` | always a JavaScript string | — |
| `Array α` | always a JavaScript array | — |
-/


/-- How a numeric Lean type is represented: as a JavaScript number, or as a
    `BigInt`. -/
inductive JsNumRepr where
  /-- A JavaScript number (a double): fast, exact only below `2^53`. -/
  | num
  /-- A JavaScript `BigInt`: exact at every size, and a different JavaScript type —
      a `BigInt` is never `===` to a number and mixing the two throws. -/
  | bigint
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
  deriving Repr, DecidableEq, Inhabited

namespace JsConfig

/-- The default configuration: numbers for `Nat` and `Int`, `BigInt` for the 64-bit
    types, strings for `Char`, tagged objects with positional fields, constructor
    chains for `List`, and the totality guards on. -/
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

/-- The representation that keeps Lean's semantics exactly: `BigInt` everywhere an
    unbounded integer can appear, every totality guard emitted, `Char` as its code
    point.  This is what the backend did before it was configurable. -/
def presetFaithful : JsConfig where
  natRepr := .bigint
  intRepr := .bigint
  usizeRepr := .bigint
  uint64Repr := .bigint
  int64Repr := .bigint

/-- How a numeric Lean *type* is represented, or `none` if it is not one of the
    numeric types the backend knows.  `Float` and `Float32` are numbers, and the
    small fixed-width types are numbers whatever the configuration says. -/
def numReprOf? (cfg : JsConfig) (typeName : Name) : Option JsNumRepr :=
  match typeName with
  | ``Nat => some cfg.natRepr
  | ``Int => some cfg.intRepr
  | ``USize => some cfg.usizeRepr
  | ``UInt64 => some cfg.uint64Repr
  | ``Int64 => some cfg.int64Repr
  | ``UInt8 | ``UInt16 | ``UInt32 | ``Int8 | ``Int16 | ``Int32 => some .num
  | ``Float | ``Float32 => some .num
  | _ => none

/-- How a numeric representation is spelled on the command line. -/
def reprName : JsNumRepr → String
  | .num => "num"
  | .bigint => "bigint"

/-- The configuration in one line, as the command line spells it.  This is what the
    header of a generated `-Expr.txt` says, so a tree can be traced back to the
    settings that produced it. -/
def describe (cfg : JsConfig) : String :=
  String.intercalate " "
    [ "nat=" ++ reprName cfg.natRepr, "int=" ++ reprName cfg.intRepr,
      "usize=" ++ reprName cfg.usizeRepr, "uint64=" ++ reprName cfg.uint64Repr,
      "int64=" ++ reprName cfg.int64Repr,
      ]

end JsConfig

end LakeJs.Config
