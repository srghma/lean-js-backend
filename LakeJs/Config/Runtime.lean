
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
  /-- The functions that answer with a `BitVec w`. -/
  | bitvec
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
  | .bitvec => some "bitvec"

/-- Every group, so that a check can run over all of them. -/
def all : List RuntimeGroup :=
  [.nonConfigurable, .nat, .int, .usize, .uint64, .int64, .isize, .bitvec]

end RuntimeGroup

/-- The names `lean_runtime_nat_*.mjs` exports: the functions that answer with a
    `Nat`. -/
def natRuntimeNames : List String :=
  [ "$lean_nat_gcd", "$lean_nat_div", "$lean_nat_mod", "$lean_nat_mod_core",
    "$lean_nat_sub", "$lean_nat_land", "$lean_nat_lor", "$lean_nat_lxor",
    "$lean_nat_shiftl", "$lean_nat_shiftr", "$lean_string_utf8_byte_size",
    "BitVec_toNat" ]

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

/-- The names `lean_runtime_bitvec_*.mjs` exports: the functions that answer with a
    `BitVec w`.  A bit vector narrower than 32 bits is a number whatever the
    configuration says, but the same function serves every width — the width is an
    argument — so the whole catalogue follows `bitvecRepr`.  `BitVec.toNat` answers
    with a `Nat` and is with the `Nat` functions instead; the three decidable
    comparisons answer with a `Bool` and read their arguments in whichever
    representation they are given, so they are in the part no knob changes. -/
def bitvecRuntimeNames : List String :=
  [ "BitVec_ofNat", "BitVec_add", "BitVec_sub", "BitVec_mul", "BitVec_neg",
    "BitVec_udiv", "BitVec_umod", "BitVec_and", "BitVec_or", "BitVec_xor",
    "BitVec_not", "BitVec_shiftLeft", "BitVec_ushiftRight", "BitVec_sshiftRight",
    "$lean_uint64_to_bitvec", "$lean_usize_to_bitvec" ]

/-- The names one group of the split holds, which is what the module of the prelude
    that stands for it — one file per representation — must export, and nothing else.
    The part no knob changes is open-ended (every library declaration the optimiser
    leaves free lands there), so it claims no list. -/
def RuntimeGroup.names : RuntimeGroup → List String
  | .nonConfigurable => []
  | .nat => natRuntimeNames
  | .int => intRuntimeNames
  | .usize => usizeRuntimeNames
  | .uint64 => uint64RuntimeNames
  | .int64 => int64RuntimeNames
  | .isize => isizeRuntimeNames
  | .bitvec => bitvecRuntimeNames

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
  else if bitvecRuntimeNames.contains name then .bitvec
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
  | .bitvec => cfg.bitvecRepr

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
  [ .bool, .nat, .int, .bitvec 1, .bitvec 31, .bitvec 32, .bitvec 53, .bitvec 54,
    .bitvec 64, .uint8, .uint16,
    .uint32, .uint64, .usize, .int8, .int16, .int32, .int64, .isize, .char, .string,
    .byteArray, .name, .stringPos, .substring, .stringSlice, .float, .float32,
    .floatArray, .childProcess, .shareCommonObject, .shareCommonState ]

/-- Can a value of this terminal type be an *integer* outside the range a JavaScript
    number holds exactly, `|v| ≤ 2^53 - 1`?  `Nat` and `Int` are unbounded, the four
    64-bit types reach past it, and so does a bit vector of more than 53 bits;
    everything else — the fixed-width types up to 32 bits, a `Char`, a string offset —
    stays inside it, and a `Float` is a double, so it *is* a JavaScript number and
    nothing about it is rounded.  There is no catch-all case here either: a terminal
    type added to the language has to answer this question too, and
    `exceeding_types_have_a_knob` below is what the answer is for. -/
def exceedsExactIntegers : LeanPrimTy → Bool
  | .nat | .int => true
  | .uint64 | .usize | .int64 | .isize => true
  | .bitvec n _ => 53 < n
  | .bool | .uint8 | .uint16 | .uint32 | .int8 | .int16 | .int32 => false
  | .char | .string | .byteArray | .name => false
  | .stringPos | .substring | .stringSlice => false
  | .float | .float32 | .floatArray => false
  | .childProcess | .shareCommonObject | .shareCommonState => false

/-- The configuration is *complete*: every terminal type that can hold an integer a
    JavaScript number cannot hold exactly has a knob, so there is no type whose values
    are silently rounded with no way to ask for the exact representation.  (The
    converse does not hold, and deliberately: a bit vector of 32 to 53 bits fits in a
    number exactly and is still given the knob, so that the whole `BitVec` catalogue of
    the runtime prelude follows one representation.) -/
theorem exceeding_types_have_a_knob :
    prims.all (fun p => !exceedsExactIntegers p || (knobOfPrim? p).isSome) = true := by
  decide

/-- The same, at every width a bit vector can have rather than at the few `prims`
    lists: a bit vector wide enough to hold an integer a number cannot, is one
    `bitvecRepr` decides. -/
theorem bitvec_exceeding_has_knob {n : Nat} (h : 0 < n)
    (hx : exceedsExactIntegers (.bitvec n h) = true) :
    (knobOfPrim? (.bitvec n h)).isSome = true := by
  simp only [exceedsExactIntegers, decide_eq_true_eq] at hx
  simp only [knobOfPrim?]
  rw [if_pos (by omega)]
  rfl

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

/-- A name a group claims is a name `runtimeGroupOf` puts back in that group: the
    lists of the split do not overlap. -/
theorem group_names_classified :
    RuntimeGroup.all.all (fun g => g.names.all (fun n => runtimeGroupOf n == g)) = true := by
  decide
