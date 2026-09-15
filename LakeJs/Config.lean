module

public import Lean.Data.Name

@[expose] public section

/-!
# The configuration of the JavaScript backend

Every decision about *how a Lean value looks in JavaScript* that has more than one
defensible answer lives here, in one record, rather than being hard-wired in the
translation or the renderer.  The rest of the backend takes a `JsConfig` as an
explicit argument of the pure functions it is made of — there is no reader monad and
no global state, so the generated file is a function of the `.olean` files and of this
record.

## The table

| Lean | JavaScript | knob |
| --- | --- | --- |
| `Nat` | a number (default) or a `BigInt` | `natRepr` |
| `Int` | a number (default) or a `BigInt` | `intRepr` |
| `UInt8/16/32`, `Int8/16/32` | always a number | — |
| `USize` | a `BigInt` (default) or a number | `usizeRepr` |
| `UInt64` | a `BigInt` (default) or a number | `uint64Repr` |
| `Int64` | a `BigInt` (default) or a number | `int64Repr` |
| `Float`, `Float32` | always a number | — |
| `Char` | always a string (default) or its code point | `charRepr` |
| `Bool` | always a JavaScript boolean | — |
| `String` | always a JavaScript string | — |
| `Array α` | always a JavaScript array | — |
| a constructor | `{tag: "cons", _1, _2}`, `["cons", a, b]` or `{tag: 1, …}` | `ctorRepr` |
| a field | `_1`, `_2` or the declared field name | `fieldNaming` |
| an enum-like inductive | a tagged value (default) or a small integer | `enumRepr` |
| `List α` | a constructor chain (default) or a JavaScript array | `listRepr` |
| `Option α` | **always** a constructor object | — |
| a `PUnit`-like structure, a unit type | always erased, or `undefined` | — |
| a one-field structure | always unwrapped | — |
| a type, a proof, `IO.RealWorld` | always erased | — |

The entries with no knob are not oversights: they are the representations for which
there is no second sensible choice, and `Option` is forced to a tagged object because
`some none` and `none` would otherwise be the same JavaScript value.

## What is lossy

* `JsNumRepr.num` for `USize`, `UInt64` and `Int64` cannot hold the values above
  `2^53` exactly.  It is offered because most programs never reach them and numbers
  are much faster than `BigInt`s; the default for those three types is therefore
  `bigint`.
* `Float32` arithmetic is *not* rounded to single precision after each step: no
  `Math.fround` is emitted.  A `Float32` is a JavaScript number, i.e. a double.
* With `natSubGuard := false` a `Nat` subtraction that would underflow produces a
  negative number instead of `0`, and with `divModZeroGuard := false` a division or
  modulo by zero produces `Infinity`/`NaN` (or throws, for a `BigInt`) instead of
  Lean's `0`.  Both knobs are **on** by default, because a total Lean function has to
  keep computing what Lean computes; they can be turned off (`--no-nat-sub-guard`,
  `--no-divmod-guard`) by a program that is known never to underflow or divide by
  zero.  The guard is never emitted where the operands rule the case out — a literal
  non-zero divisor, a subtraction of `0` — so straight-line arithmetic pays nothing
  for it.

## Totality knobs that are not knobs

* Array indexing through a `Fin` or a proof argument is *trusted*: `a[i]` with no
  check, because the Lean side has already proved the index in range.
* Array indexing through a `!` operation (`a[i]!`, `Array.get!`) always emits the
  bounds check, because there is no proof to trust.
-/

namespace Lean.Compiler.JS

/-- How a numeric Lean type is represented: as a JavaScript number, or as a
    `BigInt`. -/
inductive JsNumRepr where
  /-- A JavaScript number (a double): fast, exact only below `2^53`. -/
  | num
  /-- A JavaScript `BigInt`: exact at every size, and a different JavaScript type —
      a `BigInt` is never `===` to a number and mixing the two throws. -/
  | bigint
  deriving Repr, DecidableEq, BEq, Inhabited

/-- How a compiled Lean constructor is represented. -/
inductive JsCtorRepr where
  /-- `{tag: "cons", _1: a, _2: b}` — the default. -/
  | taggedObject
  /-- `["cons", a, b]`: the tag first, then the fields. -/
  | positionalArray
  /-- `{tag: 1, _1: a, _2: b}`: the tag is the constructor's index. -/
  | taggedInt
  deriving Repr, DecidableEq, BEq, Inhabited

/-- How the fields of a constructor are named. -/
inductive JsFieldNaming where
  /-- `_1`, `_2`, … — the default, and the only choice for a constructor whose fields
      are anonymous. -/
  | positional
  /-- The declared field names of the structure, falling back on `_i` for a field
      with no name. -/
  | declared
  deriving Repr, DecidableEq, BEq, Inhabited

/-- How an inductive all of whose constructors are nullary is represented. -/
inductive JsEnumRepr where
  /-- Like any other constructor: a tagged value.  The default. -/
  | tagged
  /-- The constructor's index, as a plain small integer. -/
  | smallInt
  deriving Repr, DecidableEq, BEq, Inhabited

/-- How a `List` is represented. -/
inductive JsListRepr where
  /-- A chain of constructor values, like any other inductive.  The default. -/
  | ctorChain
  /-- A JavaScript array: `nil` is `[]` and `cons a as` is `[a, ...as]`. -/
  | jsArray
  deriving Repr, DecidableEq, BEq, Inhabited

/-- How a `Char` is represented. -/
inductive JsCharRepr where
  /-- A one-character JavaScript string.  The default. -/
  | jsString
  /-- The code point, as a number or a `BigInt` (following `natRepr`).  This is what
      Lean's own compiler does, and it is the only representation in which
      `Char.toNat` of a *computed* character can be compiled, since the object
      language has no `codePointAt` node. -/
  | codePoint
  deriving Repr, DecidableEq, BEq, Inhabited

/-- The configuration of the backend: every representation decision, in one record.
    The default is the one described at the top of this module. -/
structure JsConfig where
  /-- How `Nat` is represented. -/
  natRepr : JsNumRepr := .num
  /-- How `Int` is represented. -/
  intRepr : JsNumRepr := .num
  /-- How `USize` is represented. -/
  usizeRepr : JsNumRepr := .bigint
  /-- How `UInt64` is represented. -/
  uint64Repr : JsNumRepr := .bigint
  /-- How `Int64` is represented. -/
  int64Repr : JsNumRepr := .bigint
  /-- How `Char` is represented. -/
  charRepr : JsCharRepr := .jsString
  /-- How a constructor value is built. -/
  ctorRepr : JsCtorRepr := .taggedObject
  /-- How the fields of a constructor are named. -/
  fieldNaming : JsFieldNaming := .positional
  /-- How an enum-like inductive is represented. -/
  enumRepr : JsEnumRepr := .tagged
  /-- How a `List` is represented. -/
  listRepr : JsListRepr := .ctorChain
  /-- Emit the truncation guard of `Nat` subtraction (`a < b ? 0 : a - b`)? -/
  natSubGuard : Bool := true
  /-- Emit Lean's `divisor = 0 ? 0 : …` guard on division and modulo? -/
  divModZeroGuard : Bool := true
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
  ctorRepr := .positionalArray
  listRepr := .jsArray

/-- The representation that keeps Lean's semantics exactly: `BigInt` everywhere an
    unbounded integer can appear, every totality guard emitted, `Char` as its code
    point.  This is what the backend did before it was configurable. -/
def presetFaithful : JsConfig where
  natRepr := .bigint
  intRepr := .bigint
  usizeRepr := .bigint
  uint64Repr := .bigint
  int64Repr := .bigint
  charRepr := .codePoint
  natSubGuard := true
  divModZeroGuard := true

/-- The last component of a name, `Int32.add ↦ "add"`. -/
def lastPart (declName : Name) : String :=
  match declName with
  | .str _ s => s
  | _ => ""

/-- The name of the type a `Int32.add`-style constant belongs to, `Int32.add ↦
    `Int32`. -/
def typeOfConst (declName : Name) : Name :=
  match declName with
  | .str p _ => p
  | _ => .anonymous

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
  | ``Char => some (match cfg.charRepr with
      | .codePoint => cfg.natRepr
      | .jsString => cfg.natRepr)
  | _ => none

/-- Is this Lean numeric type compiled to a `BigInt`? -/
def isBigIntType (cfg : JsConfig) (typeName : Name) : Bool :=
  cfg.numReprOf? typeName == some .bigint

/-- The representation of a fixed-width type of `bits` bits (signed or not), read off
    the configuration.  Everything below 64 bits is a number. -/
def fixedWidthRepr (cfg : JsConfig) (bits : Nat) (signed : Bool) : JsNumRepr :=
  if bits < 64 then .num
  else if signed then cfg.int64Repr else cfg.uint64Repr

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
      "char=" ++ (match cfg.charRepr with | .jsString => "string" | .codePoint => "codepoint"),
      "ctor=" ++ (match cfg.ctorRepr with
        | .taggedObject => "object" | .positionalArray => "array" | .taggedInt => "int"),
      "fields=" ++ (match cfg.fieldNaming with
        | .positional => "positional" | .declared => "declared"),
      "enum=" ++ (match cfg.enumRepr with | .tagged => "tagged" | .smallInt => "int"),
      "list=" ++ (match cfg.listRepr with | .ctorChain => "chain" | .jsArray => "array"),
      "nat-sub-guard=" ++ toString cfg.natSubGuard,
      "divmod-guard=" ++ toString cfg.divModZeroGuard ]

/-- `Nat` and `Int` in the same representation?  Several primitives (`Int.ofNat`,
    comparisons between the two) are the identity exactly then. -/
def natIntAgree (cfg : JsConfig) : Bool := cfg.natRepr == cfg.intRepr

end JsConfig

/-! ## The defaults, pinned -/

section Guards

open JsConfig

private def dflt : JsConfig := JsConfig.default

/-- `Nat` and `Int` are numbers by default. -/
example : dflt.natRepr = .num := by decide
example : dflt.intRepr = .num := by decide

/-- The possibly-64-bit types are `BigInt`s by default. -/
example : dflt.usizeRepr = .bigint := by decide
example : dflt.uint64Repr = .bigint := by decide
example : dflt.int64Repr = .bigint := by decide

/-- The totality guards are on by default: a translation of total Lean code has to
    compute what Lean computes, including at `x / 0` and at an underflowing `Nat`
    subtraction.  Where the operands make the guard unnecessary it is not emitted
    (see `LakeJs.JsPrims`), so the cost is only paid where it is needed. -/
example : dflt.natSubGuard = true := by decide
example : dflt.divModZeroGuard = true := by decide

#guard dflt.numReprOf? ``Nat == some .num
#guard dflt.numReprOf? ``Int == some .num
#guard dflt.numReprOf? ``UInt8 == some .num
#guard dflt.numReprOf? ``UInt16 == some .num
#guard dflt.numReprOf? ``UInt32 == some .num
#guard dflt.numReprOf? ``Int8 == some .num
#guard dflt.numReprOf? ``Int16 == some .num
#guard dflt.numReprOf? ``Int32 == some .num
#guard dflt.numReprOf? ``UInt64 == some .bigint
#guard dflt.numReprOf? ``USize == some .bigint
#guard dflt.numReprOf? ``Int64 == some .bigint
#guard dflt.numReprOf? ``Float == some .num
#guard dflt.numReprOf? ``Float32 == some .num
#guard dflt.numReprOf? ``String == none
#guard dflt.isBigIntType ``UInt64 == true
#guard dflt.isBigIntType ``Nat == false
#guard dflt.fixedWidthRepr 8 false == .num
#guard dflt.fixedWidthRepr 32 true == .num
#guard dflt.fixedWidthRepr 64 false == .bigint
#guard dflt.fixedWidthRepr 64 true == .bigint
#guard JsConfig.presetPBO.fixedWidthRepr 64 false == .num
#guard JsConfig.presetFaithful.numReprOf? ``Nat == some .bigint
#guard JsConfig.presetFaithful.natSubGuard == true
#guard JsConfig.presetPBO.listRepr == .jsArray
#guard JsConfig.presetPBO.ctorRepr == .positionalArray
#guard dflt.listRepr == .ctorChain
#guard dflt.ctorRepr == .taggedObject
#guard dflt.fieldNaming == .positional
#guard dflt.enumRepr == .tagged
#guard dflt.charRepr == .jsString
#guard dflt.describe ==
  "nat=num int=num usize=bigint uint64=bigint int64=bigint char=string ctor=object \
fields=positional enum=tagged list=chain nat-sub-guard=true divmod-guard=true"
#guard JsConfig.typeOfConst ``Int32.add == ``Int32
#guard JsConfig.lastPart ``Int32.add == "add"

end Guards

end Lean.Compiler.JS

end
