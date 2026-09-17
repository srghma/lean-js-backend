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
