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
| `BitVec n`, `n ≥ 32` | a number or a `BigInt` | `bitvecRepr` |
| `BitVec n`, `n < 32` | always a number | — |
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
  /-- How a bit vector of `n ≥ 32` bits is represented.  A narrower one fits in a
      number exactly and is one whatever this says. -/
  bitvecRepr : JsNumRepr := .bigint
  deriving Repr, DecidableEq, Inhabited

/-- Which knob decides a terminal type, named as the command line spells it; `none`
    where the type has one representation only.  Every constructor of `LeanPrimTy` is
    listed: there is no catch-all, so a new terminal type must be classified here. -/
def knobOfPrim? : LeanPrimTy → Option String
  | .nat => some "nat"
  | .int => some "int"
  | .usize => some "usize"
  | .uint64 => some "uint64"
  | .int64 => some "int64"
  | .isize => some "isize"
  | .bitvec n _ => if 32 ≤ n then some "bitvec" else none
  | .bool | .uint8 | .uint16 | .uint32 | .int8 | .int16 | .int32 => none
  | .char | .string | .byteArray | .name => none
  | .stringPos | .substring | .stringSlice => none
  | .float | .float32 | .floatArray => none
  | .childProcess | .shareCommonObject | .shareCommonState => none

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
  | ``ISize => some cfg.isizeRepr
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
      "isize=" ++ reprName cfg.isizeRepr,
      "bitvec=" ++ reprName cfg.bitvecRepr,
      ]

/-- How a *terminal* type is represented.  This is the question the printer asks, and it
    has an answer for every leaf of a `Ty`: the types that are not numeric at all, and
    the numeric ones that always fit in a `number`, answer `.num`.  A bit vector of
    `n ≥ 32` bits follows `bitvecRepr`, a narrower one is a `number`, exactly as
    `LeanPrimTy.isNumberConfigurable` says.  There is no catch-all case: a terminal
    type added to `LeanPrimTy` must be given a representation here. -/
def reprOfPrim (cfg : JsConfig) : LeanPrimTy → JsNumRepr
  | .nat => cfg.natRepr
  | .int => cfg.intRepr
  | .usize => cfg.usizeRepr
  | .uint64 => cfg.uint64Repr
  | .int64 => cfg.int64Repr
  | .isize => cfg.isizeRepr
  | .bitvec n _ => if 32 ≤ n then cfg.bitvecRepr else .num
  | .bool | .uint8 | .uint16 | .uint32 | .int8 | .int16 | .int32 => .num
  | .char | .string | .byteArray | .name => .num
  | .stringPos | .substring | .stringSlice => .num
  | .float | .float32 | .floatArray => .num
  | .childProcess | .shareCommonObject | .shareCommonState => .num

/-- How a knob is set, by the name the command line spells it with. -/
def reprOfKnob? (cfg : JsConfig) : String → Option JsNumRepr
  | "nat" => some cfg.natRepr
  | "int" => some cfg.intRepr
  | "usize" => some cfg.usizeRepr
  | "uint64" => some cfg.uint64Repr
  | "int64" => some cfg.int64Repr
  | "isize" => some cfg.isizeRepr
  | "bitvec" => some cfg.bitvecRepr
  | _ => none

/-- Is every configurable type represented the same way?  The runtime prelude is one
    module per knob, so a mixed configuration has a prelude; what it does *not* yet
    have is the conversions between the two representations that a value crossing from
    one knob's type to another's would need (`Nat.toInt` prints as its argument exactly
    when the two agree), so a mixed configuration is still refused. -/
def isUniform (cfg : JsConfig) : Bool :=
  [cfg.intRepr, cfg.usizeRepr, cfg.uint64Repr, cfg.int64Repr, cfg.isizeRepr,
    cfg.bitvecRepr].all (· == cfg.natRepr)

/-- The representation a uniform configuration gives every configurable type. -/
def uniformRepr (cfg : JsConfig) : JsNumRepr := cfg.natRepr

/-- The configuration a preset name denotes, as the command line spells it. -/
def ofPresetName? : String → Option JsConfig
  | "pbo" => some presetPBO
  | "faithful" => some presetFaithful
  | _ => none

end JsConfig

/-! ## Which runtime module a name comes from -/

/-- One module of the runtime prelude: the part no knob changes, or the part a
    particular knob decides. -/
inductive RuntimeGroup where
  /-- `lean_runtime_non_configurable.mjs`. -/
  | nonConfigurable
  /-- The functions that answer with a `Nat`. -/
  | nat
  /-- The functions that answer with an `Int`. -/
  | int
  /-- The functions that answer with a `USize`. -/
  | usize
  /-- The functions that answer with a `UInt64`. -/
  | uint64
  /-- The functions that answer with an `Int64`. -/
  | int64
  /-- The functions that answer with an `ISize`. -/
  | isize
  deriving Repr, DecidableEq, BEq, Inhabited

namespace RuntimeGroup

/-- The knob this group follows, by the name the command line spells it with;
    `none` for the part no knob changes. -/
def knob? : RuntimeGroup → Option String
  | .nonConfigurable => none
  | .nat => some "nat"
  | .int => some "int"
  | .usize => some "usize"
  | .uint64 => some "uint64"
  | .int64 => some "int64"
  | .isize => some "isize"

/-- Every group, so that a check can run over all of them. -/
def all : List RuntimeGroup :=
  [.nonConfigurable, .nat, .int, .usize, .uint64, .int64, .isize]

end RuntimeGroup

/-- The names `lean_runtime_nat_*.mjs` exports: the functions that answer with a
    `Nat`. -/
def natRuntimeNames : List String :=
  [ "$lean_nat_gcd", "$lean_nat_div", "$lean_nat_mod", "$lean_nat_mod_core",
    "$lean_nat_sub", "$lean_nat_land", "$lean_nat_lor", "$lean_nat_lxor",
    "$lean_nat_shiftl", "$lean_nat_shiftr", "$lean_string_utf8_byte_size" ]

/-- The names `lean_runtime_int_*.mjs` exports. -/
def intRuntimeNames : List String :=
  [ "$lean_int_ediv", "$lean_int_div", "$lean_int_neg", "Int_not" ]

/-- The names `lean_runtime_usize_*.mjs` exports.  `UInt64.toUSize` answers with a
    `USize`, so it is here rather than with the `UInt64` operations. -/
def usizeRuntimeNames : List String :=
  [ "$lean_usize_of_nat", "$lean_uint64_to_usize", "$lean_usize_div",
    "$lean_usize_neg", "$lean_usize_add", "$lean_usize_sub", "$lean_usize_mul",
    "$lean_usize_land", "$lean_usize_lor", "$lean_usize_xor",
    "$lean_usize_complement", "$lean_usize_shift_left", "$lean_usize_shift_right" ]

/-- The names `lean_runtime_uint64_*.mjs` exports.  A hash is a `UInt64`, so the two
    hashing functions are here. -/
def uint64RuntimeNames : List String :=
  [ "$lean_uint64_of_nat", "$lean_uint64_div", "$lean_uint64_neg",
    "$lean_uint64_add", "$lean_uint64_sub", "$lean_uint64_mul",
    "$lean_uint64_land", "$lean_uint64_lor", "$lean_uint64_xor",
    "$lean_uint64_complement", "$lean_uint64_shift_left",
    "$lean_uint64_shift_right", "$lean_string_hash", "instHashableString",
    "instHashableNat" ]

/-- The names `lean_runtime_int64_*.mjs` exports. -/
def int64RuntimeNames : List String :=
  [ "$lean_int64_of_nat", "$lean_int64_div", "$lean_int64_neg", "$lean_int64_add",
    "$lean_int64_sub", "$lean_int64_mul", "$lean_int64_land", "$lean_int64_lor",
    "$lean_int64_xor", "$lean_int64_complement", "$lean_int64_shift_left",
    "$lean_int64_shift_right" ]

/-- The names `lean_runtime_isize_*.mjs` exports. -/
def isizeRuntimeNames : List String :=
  [ "$lean_isize_of_nat", "$lean_isize_div", "$lean_isize_neg", "$lean_isize_add",
    "$lean_isize_sub", "$lean_isize_mul", "$lean_isize_land", "$lean_isize_lor",
    "$lean_isize_xor", "$lean_isize_complement", "$lean_isize_shift_left",
    "$lean_isize_shift_right" ]

/-- Which module of the prelude a runtime name comes from.  A name that answers with a
    type no knob decides — and that is most of them: the strings, the arrays, the
    lists, the fixed-width types below 64 bits and the library declarations the
    optimiser leaves free — is in the part no configuration changes. -/
def runtimeGroupOf (name : String) : RuntimeGroup :=
  if natRuntimeNames.contains name then .nat
  else if intRuntimeNames.contains name then .int
  else if usizeRuntimeNames.contains name then .usize
  else if uint64RuntimeNames.contains name then .uint64
  else if int64RuntimeNames.contains name then .int64
  else if isizeRuntimeNames.contains name then .isize
  else .nonConfigurable

namespace JsConfig

/-- How the type a runtime module answers with is represented under this
    configuration. -/
def reprOfGroup (cfg : JsConfig) : RuntimeGroup → JsNumRepr
  | .nonConfigurable => .num
  | .nat => cfg.natRepr
  | .int => cfg.intRepr
  | .usize => cfg.usizeRepr
  | .uint64 => cfg.uint64Repr
  | .int64 => cfg.int64Repr
  | .isize => cfg.isizeRepr

/-- The file of the runtime prelude a module of the split lives in. -/
def preludeFileOf (cfg : JsConfig) (g : RuntimeGroup) : String :=
  match g.knob? with
  | none => "lean_runtime_non_configurable.mjs"
  | some knob => "lean_runtime_" ++ knob ++ "_" ++ reprName (cfg.reprOfGroup g) ++ ".mjs"

/-- The file of the runtime prelude a runtime name is imported from. -/
def preludeFileOfName (cfg : JsConfig) (name : String) : String :=
  cfg.preludeFileOf (runtimeGroupOf name)

end JsConfig

/-! ## The three answers agree

`LeanPrimTy.isNumberConfigurable` says which terminal types have a choice of
representation, `knobOfPrim?` says which knob makes it, and `reprOfPrim` makes it.  The
checks below are what keeps them the same statement. -/

/-- Every terminal type that has a knob is one `isNumberConfigurable` calls
    configurable, and every one without a knob is represented the same way by both
    presets. -/
def prims : List LeanPrimTy :=
  [ .bool, .nat, .int, .bitvec 1, .bitvec 31, .bitvec 32, .bitvec 64, .uint8, .uint16,
    .uint32, .uint64, .usize, .int8, .int16, .int32, .int64, .isize, .char, .string,
    .byteArray, .name, .stringPos, .substring, .stringSlice, .float, .float32,
    .floatArray, .childProcess, .shareCommonObject, .shareCommonState ]

/-- A terminal type has a knob exactly when `LeanPrimTy.isNumberConfigurable` calls its
    representation configurable. -/
theorem knob_iff_configurable :
    prims.all (fun p => (knobOfPrim? p).isSome == p.isNumberConfigurable) = true := by
  decide

/-- The knob a terminal type has is one the configuration knows, and it is the one that
    decides that type's representation; a type with no knob is represented the same way
    by both presets. -/
theorem knob_decides_repr :
    prims.all (fun p =>
      match knobOfPrim? p with
      | none => JsConfig.presetPBO.reprOfPrim p == JsConfig.presetFaithful.reprOfPrim p
      | some knob =>
          (JsConfig.presetFaithful.reprOfKnob? knob
              == some (JsConfig.presetFaithful.reprOfPrim p))
            && (JsConfig.presetPBO.reprOfKnob? knob
              == some (JsConfig.presetPBO.reprOfPrim p))) = true := by
  decide

/-- Both presets are uniform, and a configuration that mixes the two representations is
    not. -/
theorem presets_uniform :
    JsConfig.presetPBO.isUniform && JsConfig.presetFaithful.isUniform
      && !({ natRepr := .num, intRepr := .bigint : JsConfig }.isUniform) = true := by
  decide

/-- Every group of the split has a file of its own, and the non-configurable part is the
    only one whose file does not depend on the configuration. -/
theorem prelude_file_configurable :
    RuntimeGroup.all.all (fun g =>
      (JsConfig.presetPBO.preludeFileOf g == JsConfig.presetFaithful.preludeFileOf g)
        == (g == RuntimeGroup.nonConfigurable)) = true := by
  decide

end LakeJs.Config
