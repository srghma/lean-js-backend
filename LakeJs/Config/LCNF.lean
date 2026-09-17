
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

