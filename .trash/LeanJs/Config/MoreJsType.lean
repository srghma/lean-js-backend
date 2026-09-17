/-- Lower a scalar `LeanPrimTy` to `MoreJsTy` based on the configuration. -/
def lowerScalarPrim (cfg : JsConfig) (prim : LeanPrimTy) : MoreJsTy :=
  match prim with
  | .bool      => .bool
  | .nat       => match cfg.natRepr with
    | .bigint => .nat
    | .num    => .uint53
  | .int       => match cfg.intRepr with
    | .bigint => .int
    | .num    => .int53
  | .bitvec n hPos =>
    if h : n <= 53 then
      .bitvec_small n h hPos
    else
      match cfg.bitvecRepr with
      | .bigint => .bitvec_big n (by omega)
      | .num    => .uint53
  | .uint8     => .uint8
  | .uint16    => .uint16
  | .uint32    => .uint32
  | .uint64    => match cfg.uint64Repr with
    | .bigint => .nat
    | .num    => .uint53
  | .int8      => .int8
  | .int16     => .int16
  | .int32     => .int32
  | .int64     => match cfg.int64Repr with
    | .bigint => .int
    | .num    => .int53
  | .float     => .float
  | .float32   => .float32
  | .char      => .string
  | .string    => .string
  | .stringPos => .uint32
  | .substring => .substring
  | .stringSlice => .stringSlice
  | .childProcess => .childProcess
  | .shareCommonObject => .shareCommonObject
  | .shareCommonState  => .shareCommonState

/-- Lowers `LeanPrimTyCovariant.array prim` into the optimized `MoreJsTy`. -/
def lowerArrayPrim (cfg : JsConfig) (prim : LeanPrimTy) : MoreJsTy :=
  match prim with
  -- 1. Booleans
  | .bool =>
    match cfg.arrayBoolRepr with
    | .genericArray => .genericArray .bool
    | .uint8Array   => .uint8Array

  -- 2. Nat and Int (configured separately!)
  | .nat =>
    match cfg.natRepr with
    | .bigint => .genericArray .nat
    | .num    => .genericArray .uint53

  | .int =>
    match cfg.intRepr with
    | .bigint => .genericArray .int
    | .num    => .genericArray .int53

  -- 3. BitVectors (supports 1..7, 9..15, 17..31, 33..63 packing)
  | .bitvec n hPos =>
    let genericBitVec : MoreJsTy :=
      if h : n <= 53 then
        .genericArray (.bitvec_small n h hPos)
      else
        match cfg.bitvecRepr with
        | .bigint => .genericArray (.bitvec_big n (by omega))
        | .num    => .genericArray .uint53

    match cfg.arrayBitVecRepr with
    | .genericArray => genericBitVec

    | .exactTypedArrayOnly =>
      if n == 8 then .uint8Array
      else if n == 16 then .uint16Array
      else if n == 32 then .uint32Array
      else if n == 64 then
        match cfg.bitvecRepr with
        | .bigint => .bigUint64Array
        | .num    => genericBitVec
      else genericBitVec

    | .roundUpToSmallestTypedArray =>
      if n <= 8 then
        .uint8Array           -- BitVec 1..8 fits in Uint8
      else if n <= 16 then
        .uint16Array          -- BitVec 9..16 fits in Uint16
      else if n <= 32 then
        .uint32Array          -- BitVec 17..32 fits in Uint32
      else if n <= 64 then
        match cfg.bitvecRepr with
        | .bigint => .bigUint64Array -- BitVec 33..64 fits in BigUint64Array
        | .num    => genericBitVec
      else
        genericBitVec

  -- 4. Fixed-Width 8/16/32-bit Integers
  | .uint8 =>
    match cfg.arrayFixedIntRepr with
    | .typedArray   => .uint8Array
    | .genericArray => .genericArray (lowerScalarPrim cfg .uint8)
  | .uint16 =>
    match cfg.arrayFixedIntRepr with
    | .typedArray   => .uint16Array
    | .genericArray => .genericArray (lowerScalarPrim cfg .uint16)
  | .uint32 =>
    match cfg.arrayFixedIntRepr with
    | .typedArray   => .uint32Array
    | .genericArray => .genericArray (lowerScalarPrim cfg .uint32)
  | .int8 =>
    match cfg.arrayFixedIntRepr with
    | .typedArray   => .int8Array
    | .genericArray => .genericArray (lowerScalarPrim cfg .int8)
  | .int16 =>
    match cfg.arrayFixedIntRepr with
    | .typedArray   => .int16Array
    | .genericArray => .genericArray (lowerScalarPrim cfg .int16)
  | .int32 =>
    match cfg.arrayFixedIntRepr with
    | .typedArray   => .int32Array
    | .genericArray => .genericArray (lowerScalarPrim cfg .int32)

  -- 5. 64-bit Integers (separate configs for UInt64 and Int64)
  | .uint64 =>
    match cfg.arrayUint64Repr with
    | .bigUint64Array => .bigUint64Array
    | .genericArray   =>
      match cfg.uint64Repr with
      | .bigint => .genericArray .nat
      | .num    => .genericArray .uint53

  | .int64 =>
    match cfg.arrayInt64Repr with
    | .bigInt64Array => .bigInt64Array
    | .genericArray  =>
      match cfg.int64Repr with
      | .bigint => .genericArray .int
      | .num    => .genericArray .int53

  -- 6. Floating-point numbers
  | .float =>
    match cfg.arrayFloatRepr with
    | .typedArray   => .float64Array
    | .genericArray => .genericArray .float
  | .float32 =>
    match cfg.arrayFloatRepr with
    | .typedArray   => .float32Array
    | .genericArray => .genericArray .float32

  -- 7. Characters
  | .char =>
    match cfg.arrayCharRepr with
    | .genericArray => .genericArray .string
    | .uint32Array  => .uint32Array

  -- 8. String index positions
  | .stringPos =>
    match cfg.arrayFixedIntRepr with
    | .typedArray   => .uint32Array
    | .genericArray => .genericArray .uint32

  -- 9. Reference / Composite types (always generic Array<T>)
  | other => .genericArray (lowerScalarPrim cfg other)
