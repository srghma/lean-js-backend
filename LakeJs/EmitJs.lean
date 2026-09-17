import MiniAST
import LakeJs.Expr
import LakeJs.ExternsMeta
import LakeJs.Rename
import LakeJs.Config

/-!
# Printing a `Term` as JavaScript

The whole of the JavaScript the backend emits is built here, as a `MiniProgram` of
`MiniAST`, and printed by `MiniAST.printProgram`.  Nothing in this file can emit a
recursive JavaScript function: a `Term` has no recursive node to translate, so the only
repetition it can print is the `while` loop of `Term.loop`.

Names are chosen from the *depth* of the binder — the variable bound in a context of
length `k` is `v{k}` — which is deterministic, needs no gensym counter, and cannot
shadow, since two binders in the same scope chain always sit at different depths.

A loop is the whole body of the function it belongs to, so the loop's own condition is
the constant `true` and the block is left with a `return`: no exit flag and no result
variable are printed.

```js
const test = (v0) => {
  let v1 = v0;
  while (true) {
    if (v1 === 0) { return v1; }
    v1 = v1 - 1;
    continue;
  }
};
```
-/

namespace LakeJs.EmitJs

open LakeJs
open LakeJs.Ty
open LakeJs.Layout (FieldLayout ObjLayout)
open LakeJs.Expr
open LakeJs.Rename

open Language.JavaScript
open Language.JavaScript.MiniAST
open LakeJs.Config (JsConfig JsNumRepr RuntimeGroup runtimeGroupOf)

/-- A non-empty JavaScript identifier from a string that the backend built. -/
def ident (s : String) : NEString := NEString.ofString! (if s.isEmpty then "_" else s)

/-- `e` as an identifier expression. -/
def var (s : String) : MiniExpr := .ident (ident s)

/-- The JavaScript name of the variable bound in a context of length `depth`. -/
def depthName (depth : Nat) : String := "v" ++ toString depth

/-- The JavaScript name of field number `j` of a constructor: fields are positional,
    and they are numbered from one. -/
def fieldName (j : Nat) : String := "_" ++ toString (j + 1)

/-- The name the runtime prelude binds an extern under. -/
def externName {σs : List Ty} {τ : Ty} (e : Externs σs τ) : String := "$" ++ e.cName

/-- A number literal. -/
def num (n : Nat) : MiniExpr := .number (JSNumber.ofNat n)

/-- An integer literal, negative ones included. -/
def intLit (i : Int) : MiniExpr :=
  if i < 0 then .unary .minus (num i.natAbs) else num i.toNat

/-- A literal at a numeric representation: `48` where the type is a JavaScript number,
    `48n` where it is a `BigInt`. -/
def numAt : JsNumRepr → Nat → MiniExpr
  | .num, n => num n
  | .bigint, n => .number (.bigint .decimal n)

/-- A possibly negative literal at a numeric representation. -/
def intLitAt (r : JsNumRepr) (i : Int) : MiniExpr :=
  if i < 0 then .unary .minus (numAt r i.natAbs) else numAt r i.toNat

/-- The tag of a value of `Ty.enum n shift`, which is the value itself less the shift:
    nothing at all when the shift is zero, which is the ordinary case. -/
def unshift (shift : Int) (e : MiniExpr) : MiniExpr :=
  if shift == 0 then e
  else if shift < 0 then .binary e .plus (num shift.natAbs)
  else .binary e .minus (num shift.toNat)

/-- `Math.max(0, e)`, for the truncated subtraction of `Nat`. -/
def mathMax0 (e : MiniExpr) : MiniExpr :=
  .call (.dot (var "Math") (ident "max")) [num 0, e]

/-- An object literal with these fields, in this order. -/
def objectOf (fields : List (String × MiniExpr)) : MiniExpr :=
  .object (fields.map fun (k, v) => MiniProperty.keyValue (.ident (ident k)) v)

/-- The digits of `n`, as a decimal string. -/
def decimalOfNat (n : Nat) : String := toString n

/-- The *exact* decimal value of `m * 2 ^ (-e)`, with `e` binary places after the point.
    Multiplying by `5 ^ e` turns the binary fraction into a decimal one, which is exact
    because `2 ^ (-e) * 5 ^ e = 10 ^ (-e)`; the point then goes `e` digits from the
    right. -/
def decimalOfBinaryFraction (m : Nat) (e : Nat) : String :=
  if e == 0 then decimalOfNat m
  else
    let digits : List Char := (decimalOfNat (m * 5 ^ e)).toList
    let pad : Nat := if digits.length ≤ e then e + 1 - digits.length else 0
    let padded : List Char := List.replicate pad '0' ++ digits
    let cut := padded.length - e
    let whole := String.ofList (padded.take cut)
    let fracDigits := (padded.drop cut).reverse.dropWhile (· == '0')
    let frac := String.ofList fracDigits.reverse
    if frac.isEmpty then whole else whole ++ "." ++ frac

/-- The exact decimal rendering of the IEEE 754 binary64 number whose bits are `bits`,
    without its sign: a binary floating point number is a finite decimal, so no digit is
    invented and none is lost, and JavaScript reads the rendering back as the same
    number.  `none` is an infinity or a NaN, which have no decimal rendering. -/
def decimalOfFloatBits (bits : UInt64) : Option String :=
  let expo := (bits >>> 52).toNat &&& 0x7ff
  let mant := bits.toNat &&& 0xfffffffffffff
  if expo == 0x7ff then none            -- an infinity or a NaN
  else if expo == 0 then
    -- subnormal: 0.mant × 2 ^ (-1022), that is mant × 2 ^ (-1074)
    some (decimalOfBinaryFraction mant 1074)
  else
    -- normal: 1.mant × 2 ^ (expo - 1023), that is (2 ^ 52 + mant) × 2 ^ (expo - 1075)
    let m := 2 ^ 52 + mant
    if expo ≥ 1075 then some (decimalOfNat (m * 2 ^ (expo - 1075)))
    else some (decimalOfBinaryFraction m (1075 - expo))

/-- A `Float`, as the JavaScript expression denoting exactly it. -/
def floatExpr (f : Float) : MiniExpr :=
  if f.isNaN then var "NaN"
  else if f.isInf then (if f < 0 then .unary .minus (var "Infinity") else var "Infinity")
  else
    match decimalOfFloatBits f.abs.toBits with
    | some s =>
        let e := .ident (NEString.ofString! s)
        -- a negative zero is `-0`, which JavaScript distinguishes from `0`
        if f < 0 || (f == 0 && (1.0 / f) < 0) then .unary .minus e else e
    | none => var "NaN"

-- the rendering is the exact value of the double, so JavaScript reads it back unchanged
#guard decimalOfFloatBits (1.0 : Float).toBits == some "1"
#guard decimalOfFloatBits (1.5 : Float).toBits == some "1.5"
#guard decimalOfFloatBits (0.0 : Float).toBits == some "0"
#guard decimalOfFloatBits (1024.0 : Float).toBits == some "1024"
#guard decimalOfFloatBits (0.1 : Float).toBits ==
  some "0.1000000000000000055511151231257827021181583404541015625"
#guard (decimalOfFloatBits (1.0 / 0.0 : Float).toBits).isNone

/-- A literal.  Every terminal type of `LeanPrimTy` that has constants has a case here;
    the three that have none (`.childProcess`, `.shareCommonObject`,
    `.shareCommonState`) have no `Lit` constructor, so there is nothing to print. -/
def litExpr (cfg : JsConfig) : ∀ {p : LeanPrimTy}, Lit p → MiniExpr
  | _, .bool b => if b then .true_ else .false_
  | _, .nat n => numAt (cfg.reprOfPrim .nat) n
  | _, .int i => intLitAt (cfg.reprOfPrim .int) i
  | _, .bitvec (n := n) (h := h) v => numAt (cfg.reprOfPrim (.bitvec n h)) v.toNat
  | _, .uint8 v => num v.toNat
  | _, .uint16 v => num v.toNat
  | _, .uint32 v => num v.toNat
  | _, .uint64 v => numAt (cfg.reprOfPrim .uint64) v.toNat
  | _, .usize v => numAt (cfg.reprOfPrim .usize) v.toNat
  | _, .int8 v => intLit v.toInt
  | _, .int16 v => intLit v.toInt
  | _, .int32 v => intLit v.toInt
  | _, .int64 v => intLitAt (cfg.reprOfPrim .int64) v.toInt
  | _, .isize v => intLitAt (cfg.reprOfPrim .isize) v.toInt
  | _, .char c => .string (String.singleton c)
  | _, .string s => .string s
  | _, .byteArray bs => .array (bs.toList.map fun b => .elem (num b.toNat))
  | _, .name n => .string (toString n)
  | _, .stringPos p => num p
  | _, .substring s a b => objectOf [("str", .string s), ("startPos", num a), ("stopPos", num b)]
  | _, .stringSlice s a b => objectOf [("str", .string s), ("startPos", num a), ("stopPos", num b)]
  | _, .float f => floatExpr f
  | _, .float32 f => floatExpr f.toFloat
  | _, .floatArray fs => .array (fs.toList.map fun f => .elem (floatExpr f))

/-- `Math.trunc(e)`, for the integer division of `Nat` and `Int`. -/
def mathTrunc (e : MiniExpr) : MiniExpr :=
  .call (.dot (var "Math") (ident "trunc")) [e]

/-- `Math.abs(e)`. -/
def mathAbs (e : MiniExpr) : MiniExpr :=
  .call (.dot (var "Math") (ident "abs")) [e]

/-! ## The externs JavaScript has an operator for

An extern is a *Lean* function, and the general way to run one is to call the runtime
function of that name.  For arithmetic, comparison and the handful of string and array
operations below, JavaScript has an operator that does exactly the same thing, and
calling out to the runtime for `a + b` would be absurd — so `inlineExtern?` gives the
operator form of those, and the extern prints as the operator wherever it is *saturated*
(`externCall?`) and as a lambda over the operator wherever it is used as a value
(`externValue`).  An extern with an operator form is therefore never imported from the
runtime prelude.

Everything else — `lean_nat_gcd`, `lean_string_utf8_next`, the hashing and the tasks —
has no operator and prints as the call it is.  The table below is deliberately
conservative: an extern is here only when the JavaScript operator agrees with Lean on
*every* input the representation can hold, which is why `lean_string_dec_lt` (JavaScript
compares UTF-16 code units) and the wrapping fixed-width arithmetic are absent. -/

/-- `BigInt(e)`: the length of a string or an array is a JavaScript number, and has to
    be converted where `Nat` is a `BigInt`. -/
def toBigInt (e : MiniExpr) : MiniExpr := .call (var "BigInt") [e]

/-- The length of a string or an array, as a value of a `Nat` at representation `r`. -/
def lengthAt (r : JsNumRepr) (e : MiniExpr) : MiniExpr :=
  let len := .dot e (ident "length")
  match r with
  | .num => len
  | .bigint => toBigInt len

/-- `some e` where the representation is `.num`, and `none` where it is `.bigint`: the
    operator form of this extern is only right over JavaScript numbers, so over `BigInt`s
    the extern is called instead. -/
def numOnly (r : JsNumRepr) (e : MiniExpr) : Option MiniExpr :=
  match r with
  | .num => some e
  | .bigint => none

/-- Is this terminal type held as an integer — a value the two representations spell
    differently, a number or a `BigInt`?  A cast between two such types has to convert
    where the configuration represents them differently; a cast that touches anything
    else (a string, a character, a float, a function, an array) is a reinterpretation
    and prints as its argument. -/
def isIntegralPrim : LeanPrimTy → Bool
  | .nat | .int | .usize | .uint64 | .int64 | .isize | .bitvec _ _ => true
  | .uint8 | .uint16 | .uint32 | .int8 | .int16 | .int32 => true
  | .stringPos => true
  | _ => false

/-- A cast from `σ` to `τ`.  The two types are the same value in Lean's model, but a
    `Nat` may be a `BigInt` while the `UInt8` it is read as is always a number, and the
    two are different JavaScript types, so a cast that crosses representations is a
    conversion and not nothing. -/
def castExpr (cfg : JsConfig) : Ty → Ty → MiniExpr → MiniExpr
  | .prim p, .prim q, e =>
      if isIntegralPrim p && isIntegralPrim q then
        match cfg.reprOfPrim p, cfg.reprOfPrim q with
        | .bigint, .num => .call (var "Number") [e]
        | .num, .bigint => toBigInt e
        | _, _ => e
      else e
  | _, _, e => e

/-- The natural number a JavaScript literal denotes, be it a number or a `BigInt`. -/
def natOfLit? : MiniExpr → Option Nat
  | .number (.decimal m e) => if 0 ≤ e then some (m * 10 ^ e.toNat) else none
  | .number (.radix _ v) => some v
  | .number (.bigint _ v) => some v
  | _ => none

/-- `UInt8.ofNat`, `UInt16.ofNat` or `UInt32.ofNat` of a *literal*: the constant taken
    into `w` bits.  The answer is always a JavaScript number, so this is one place where
    a `Nat` written as a `BigInt` becomes a number at compile time rather than at run
    time.  Where the argument is not a literal there is nothing to compute here and the
    runtime function is called. -/
def ofNatLitU (w : Nat) (a : MiniExpr) : Option MiniExpr :=
  (natOfLit? a).map fun n => num (n % 2 ^ w)

/-- `Int8.ofNat`, `Int16.ofNat` or `Int32.ofNat` of a literal: the constant taken into
    `w` bits, read as a signed number. -/
def ofNatLitS (w : Nat) (a : MiniExpr) : Option MiniExpr :=
  (natOfLit? a).map fun n =>
    let m : Nat := 2 ^ w
    let r : Nat := n % m
    intLit (if m / 2 ≤ r then (r : Int) - (m : Int) else (r : Int))

/-- Is this expression safe to mention twice — a name or a literal, which has no
    subexpression to evaluate and hence no work to repeat and no effect to repeat? -/
def isAtomic : MiniExpr → Bool
  | .ident _ => true
  | .number _ => true
  | .unary .minus e => isAtomic e
  | _ => false

/-- Is this expression the literal zero of the representation `r`? -/
def isZeroLit : MiniExpr → Bool
  | .number (.decimal 0 _) => true
  | .number (.radix _ 0) => true
  | .number (.bigint _ 0) => true
  | _ => false

/-- Is this expression a numeric literal other than zero? -/
def isNonZeroLit : MiniExpr → Bool
  | .number _ => true
  | .unary .minus (.number _) => true
  | _ => false

/-- `e`, guarded by `b ≠ 0`: Lean answers zero when the divisor is zero, JavaScript
    answers `NaN` or `Infinity` (and a `BigInt` division throws), so an operator form of
    a division is only the Lean function inside this guard.  The guard is dropped where
    the divisor is a literal that is not zero, and the operator form is refused
    altogether — the extern is then called — where mentioning the divisor twice would
    repeat work. -/
def divGuard (atZero : MiniExpr) (b : MiniExpr) (e : MiniExpr) : Option MiniExpr :=
  if isZeroLit b then some atZero
  else if isNonZeroLit b then some e
  else if isAtomic b then some (.ternary (.binary b .strictNeq (num 0)) e atZero)
  else none

/-- The JavaScript operator form of an extern, applied to the arguments the runtime
    function takes, or `none` when the extern has none and has to be called.

    The answer depends on the configuration, because an operator that is exactly the
    Lean function over JavaScript numbers need not be one over `BigInt`s: `Math.max` and
    `Math.trunc` reject a `BigInt` outright, and `a / 0n` throws where `a / 0` is
    `Infinity`.  Where the operator is not right, this answers `none` and the extern
    prints as the call of the runtime function it is, which the prelude of *that*
    representation implements. -/
def inlineExtern? (cfg : JsConfig) :
    ∀ {σs : List Ty} {τ : Ty}, Externs σs τ → List MiniExpr → Option MiniExpr
  -- `a + b`
  | _, _, .lean_nat_add, [a, b] => some (.binary a .plus b)
  | _, _, .lean_int_add, [a, b] => some (.binary a .plus b)
  | _, _, .lean_float_add, [a, b] => some (.binary a .plus b)
  | _, _, .lean_float32_add, [a, b] => some (.binary a .plus b)
  -- `UInt8`, `UInt16` and `UInt32` wrap, which the JavaScript operator does not, so
  -- their arithmetic is the call of the runtime function that wraps
  -- the 64-bit types wrap too, at either representation
  | _, _, .lean_string_append, [a, b] => some (.binary a .plus b)
  | _, _, .lean_string_append_defs, [a, b] => some (.binary a .plus b)
  -- `a - b`; `Nat` truncates at zero, and no other type here does
  | _, _, .lean_nat_sub, [a, b] =>
      numOnly (cfg.reprOfPrim .nat) (mathMax0 (.binary a .minus b))
  | _, _, .lean_nat_pred, [a] =>
      numOnly (cfg.reprOfPrim .nat) (mathMax0 (.binary a .minus (num 1)))
  | _, _, .lean_int_sub, [a, b] => some (.binary a .minus b)
  | _, _, .lean_float_sub, [a, b] => some (.binary a .minus b)
  | _, _, .lean_float32_sub, [a, b] => some (.binary a .minus b)
  -- `a * b`
  | _, _, .lean_nat_mul, [a, b] => some (.binary a .times b)
  | _, _, .lean_int_mul, [a, b] => some (.binary a .times b)
  | _, _, .lean_float_mul, [a, b] => some (.binary a .times b)
  | _, _, .lean_float32_mul, [a, b] => some (.binary a .times b)
  -- division: the integer ones truncate towards zero, the floating ones do not
  | _, _, .lean_nat_div, [a, b] =>
      (numOnly (cfg.reprOfPrim .nat) (mathTrunc (.binary a .divide b))).bind fun e =>
        divGuard (num 0) b e
  | _, _, .lean_int_div, [a, b] =>
      (numOnly (cfg.reprOfPrim .int) (mathTrunc (.binary a .divide b))).bind fun e =>
        divGuard (num 0) b e
  | _, _, .lean_float_div, [a, b] => some (.binary a .divide b)
  | _, _, .lean_float32_div, [a, b] => some (.binary a .divide b)
  -- `a % b`, on the two types whose remainder JavaScript agrees with
  -- `n % 0` is `n` in Lean and `NaN` in JavaScript, so the remainder is guarded too,
  -- and the value the guard answers with is the dividend rather than zero
  | _, _, .lean_nat_mod, [a, b] =>
      (numOnly (cfg.reprOfPrim .nat) (.binary a .mod b)).bind fun e =>
        if isAtomic a then divGuard a b e else none
  | _, _, .lean_nat_mod_core, [a, b] =>
      (numOnly (cfg.reprOfPrim .nat) (.binary a .mod b)).bind fun e =>
        if isAtomic a then divGuard a b e else none
  -- `a < b`
  | _, _, .lean_nat_dec_lt, [a, b] => some (.binary a .lt b)
  | _, _, .lean_int_dec_lt, [a, b] => some (.binary a .lt b)
  | _, _, .lean_uint8_dec_lt, [a, b] => some (.binary a .lt b)
  | _, _, .lean_uint16_dec_lt, [a, b] => some (.binary a .lt b)
  | _, _, .lean_uint32_dec_lt, [a, b] => some (.binary a .lt b)
  | _, _, .lean_uint64_dec_lt, [a, b] => some (.binary a .lt b)
  | _, _, .lean_usize_dec_lt, [a, b] => some (.binary a .lt b)
  | _, _, .lean_float_lt, [a, b] => some (.binary a .lt b)
  | _, _, .lean_float_decLt, [a, b] => some (.binary a .lt b)
  | _, _, .lean_float32_lt, [a, b] => some (.binary a .lt b)
  | _, _, .lean_float32_decLt, [a, b] => some (.binary a .lt b)
  -- `a <= b`
  | _, _, .lean_nat_dec_le, [a, b] => some (.binary a .le b)
  | _, _, .lean_nat_ble, [a, b] => some (.binary a .le b)
  | _, _, .lean_int_dec_le, [a, b] => some (.binary a .le b)
  | _, _, .lean_uint8_dec_le, [a, b] => some (.binary a .le b)
  | _, _, .lean_uint16_dec_le, [a, b] => some (.binary a .le b)
  | _, _, .lean_uint32_dec_le, [a, b] => some (.binary a .le b)
  | _, _, .lean_uint64_dec_le, [a, b] => some (.binary a .le b)
  | _, _, .lean_usize_dec_le, [a, b] => some (.binary a .le b)
  | _, _, .lean_float_le, [a, b] => some (.binary a .le b)
  | _, _, .lean_float_decLe, [a, b] => some (.binary a .le b)
  | _, _, .lean_float32_le, [a, b] => some (.binary a .le b)
  | _, _, .lean_float32_decLe, [a, b] => some (.binary a .le b)
  -- `a === b`
  | _, _, .lean_nat_dec_eq, [a, b] => some (.binary a .strictEq b)
  | _, _, .lean_nat_beq, [a, b] => some (.binary a .strictEq b)
  | _, _, .lean_int_dec_eq, [a, b] => some (.binary a .strictEq b)
  | _, _, .lean_uint8_dec_eq, [a, b] => some (.binary a .strictEq b)
  | _, _, .lean_uint16_dec_eq, [a, b] => some (.binary a .strictEq b)
  | _, _, .lean_uint32_dec_eq, [a, b] => some (.binary a .strictEq b)
  | _, _, .lean_uint64_dec_eq, [a, b] => some (.binary a .strictEq b)
  | _, _, .lean_usize_dec_eq, [a, b] => some (.binary a .strictEq b)
  | _, _, .lean_string_dec_eq, [a, b] => some (.binary a .strictEq b)
  | _, _, .lean_float_beq, [a, b] => some (.binary a .strictEq b)
  | _, _, .lean_float32_beq, [a, b] => some (.binary a .strictEq b)
  -- `ofNat` of a literal, at a width that is always a JavaScript number: the constant
  -- itself, so that a module whose types no knob can change prints the same text at
  -- either configuration
  | _, _, .lean_uint8_of_nat, [a] => ofNatLitU 8 a
  | _, _, .lean_uint16_of_nat, [a] => ofNatLitU 16 a
  | _, _, .lean_uint32_of_nat, [a] => ofNatLitU 32 a
  | _, _, .lean_int8_of_nat, [a] => ofNatLitS 8 a
  | _, _, .lean_int16_of_nat, [a] => ofNatLitS 16 a
  | _, _, .lean_int32_of_nat, [a] => ofNatLitS 32 a
  -- `Int.ofNat`, which is the identity on the JavaScript value as long as the two types
  -- are represented the same way
  | _, _, .lean_nat_to_int, [a] =>
      if cfg.reprOfPrim .nat == cfg.reprOfPrim .int then some a else none
  -- `Int.toNat`, which truncates a negative integer to zero
  | _, _, .lean_int_to_nat, [a] => numOnly (cfg.reprOfPrim .int) (mathMax0 a)
  -- `Int.natAbs`
  | _, _, .lean_nat_abs, [a] => numOnly (cfg.reprOfPrim .int) (mathAbs a)
  -- strings and arrays; a `length` is a JavaScript number whatever `Nat` is
  | _, _, .lean_string_length, [a] => some (lengthAt (cfg.reprOfPrim .nat) a)
  | _, _, .lean_string_length_def, [a] => some (lengthAt (cfg.reprOfPrim .nat) a)
  | _, _, .lean_array_get_size _, [a] => some (lengthAt (cfg.reprOfPrim .nat) a)
  | _, _, .lean_array_push _, [a, x] => some (.array [.elem (.spread a), .elem x])
  | _, _, .lean_array_fget _, [a, i] => some (.index a i)
  | _, _, .lean_array_fget_borrowed _, [a, i] => some (.index a i)
  | _, _, .lean_array_get _, [a, i] => some (.index a i)
  | _, _, .lean_array_get_borrowed _, [a, i] => some (.index a i)
  -- the capacity an empty array is asked for is a hint, and JavaScript has none
  | _, _, .lean_empty_array_with_capacity _, [_] => some (.array [])
  | _, _, .lean_array_mk_empty _, [_] => some (.array [])
  | _, _, _, _ => none

/-- Does this extern print as a JavaScript operator rather than as a call of the runtime
    function?  Such an extern is never imported from the prelude. -/
def hasInlineForm (cfg : JsConfig) {σs : List Ty} {τ : Ty} (e : Externs σs τ) : Bool :=
  (inlineExtern? cfg e ((List.range e.arity).map fun i => var (depthName i))).isSome

/-- The de Bruijn index of a variable, as a number. -/
abbrev varIndex {Γ : Ctx} {τ : Ty} (v : Γ ∋ τ) : Nat := v.index

/-- The wrapper of an extern used as a *value* rather than called:
    `(x0, x1) => $lean_nat_gcd(x0, x1)`, or `(x0, x1) => x0 + x1` where the extern has an
    operator form.  An extern is typed `.fn σs τ`, and a `Ty.fn` is uncurried, so the
    wrapper takes all of its arguments at once — exactly the arguments the runtime
    function takes. -/
def externValue (cfg : JsConfig) (depth : Nat) {σs : List Ty} {τ : Ty} (e : Externs σs τ) : MiniExpr :=
  let names := (List.range e.arity).map fun i => depthName (depth + i)
  let args := names.map var
  .arrow (names.map fun nm => MiniParam.plain (.ident (ident nm)))
    (.expr (match inlineExtern? cfg e args with
      | some body => body
      | none => .call (var (externName e)) args))

/-- Does this term read loop slot `k`?  The slot is the variable at depth `base + k`,
    which is de Bruijn index `depth - 1 - (base + k)` of a term read in a context of
    length `depth`. -/
def readsSlot (depth base k : Nat) {Sg : Sig} {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ) : Bool :=
  Term.readsIndexAt (depth - 1 - (base + k)) 0 t

/-- Is this term the loop slot `j` itself, so that assigning it would assign a variable
    to itself? -/
def isSlot (depth base j : Nat) {Sg : Sig} {Γ : Ctx} {τ : Ty} : Term Sg Γ τ → Bool
  | .var v => depth - 1 - v.index == base + j
  | _ => false

/-- For each argument of a `Body.cont`, in order: whether it has to be computed into a
    temporary before the slots are assigned, and whether the assignment is a self
    assignment that may be dropped altogether.

    The slots are assigned in order, so argument `j` needs a temporary exactly when it
    reads a slot `k < j`, whose assignment would otherwise have overwritten the value it
    means to read.  An argument that reads only slots it does not precede — a literal, a
    `const` of the body, its own slot — is assigned directly. -/
partial def contSlotInfo (depth base : Nat) :
    ∀ {Sg : Sig} {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → Nat → List (Bool × Bool)
  | _, _, _, .nil, _ => []
  | _, _, _, .cons t rest, j =>
      ((List.range j).any (fun k => readsSlot depth base k t), isSlot depth base j t) ::
        contSlotInfo depth base rest (j + 1)

mutual

/-- A term in expression position.  `depth` is the length of the context, so the binder
    `i` de Bruijn steps out is the one at depth `depth - 1 - i`. -/
partial def exprOf (cfg : JsConfig) (depth : Nat) : ∀ {Sg : Sig} {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → MiniExpr
  | _, _, _, .var v => var (depthName (depth - 1 - varIndex v))
  | _, _, _, .lamN (params := ps) b =>
      let n := ps.length
      let names := (List.range n).map (fun i => MiniParam.plain (.ident (ident (depthName (depth + i)))))
      .arrow names (arrowBody cfg (depth + n) b)
  | _, _, _, t@(.apN f args) =>
      match externCall? cfg depth t [] with
      | some e => e
      | none => .call (exprOf cfg depth f) (spineOf cfg depth args)
  | _, _, _, .lamProd (params := ps) rets =>
      let n := ps.length
      let names := (List.range n).map (fun i => MiniParam.plain (.ident (ident (depthName (depth + i)))))
      let vals := spineOf cfg (depth + n) rets
      .arrow names (.block [.return_ (some (.array (vals.map MiniArrayElement.elem)))])
  | _, _, _, .callProd f args i => .index (.call (exprOf cfg depth f) (spineOf cfg depth args)) (num i.val)
  | _, _, _, .lit l => litExpr cfg l
  | _, _, _, .global r => var r.name
  | _, _, _, .extern e => externValue cfg depth e
  | _, _, _, .jsOp op args => jsOpExpr cfg depth op args
  | _, _, _, .lazyMk e => .arrow [] (arrowBody cfg depth e)
  | _, _, _, .lazyForce e => .call (exprOf cfg depth e) []
  -- a constructor of an enum carries nothing, so the value *is* its number, shifted:
  -- `.enum 3 (-1)` (an `Ordering`) prints as `-1`, `0`, `1`
  | _, _, .enum es, .ctor i _ _ _ => intLit (Int.ofNat i + es.shift)
  | _, _, _, .ctor i _ _ args => ctorExpr i (spineOf cfg depth args)
  | _, _, _, .proj e _ j _ => .dot (exprOf cfg depth e) (ident (fieldName j))
  -- and its tag is the value itself, shifted back
  | _, _, _, .tagOf (σ := .enum es) e _ => unshift es.shift (exprOf cfg depth e)
  | _, _, _, .tagOf e _ => .dot (exprOf cfg depth e) (ident "tag")
  | _, _, _, t@(.letE ..) => iife (stmtsOf cfg depth t)
  | _, _, _, t@(.caseTag ..) => iife (stmtsOf cfg depth t)
  | _, _, _, t@(.loop ..) => iife (stmtsOf cfg depth t)
  | _, _, _, t@(.joinPoint ..) => iife (stmtsOf cfg depth t)
  -- a join point is a local function that never escapes, so a jump is an ordinary call
  | _, _, _, .jump v args =>
      .call (var (depthName (depth - 1 - varIndex v))) (spineOf cfg depth args)
  | _, _, _, .ite c t e => .ternary (exprOf cfg depth c) (exprOf cfg depth t) (exprOf cfg depth e)

/-- A call whose head is an extern, printed as the JavaScript operator of that extern
    (`a + b`) where it has one, and otherwise as **one** call of the runtime function
    (`$lean_nat_gcd(a, b)`).  It answers `none` when the head is not an extern, or when
    the extern does not get exactly the arguments the runtime function takes — the
    curried wrapper of `externValue` handles that case instead. -/
partial def externCall? (cfg : JsConfig) (depth : Nat) :
    ∀ {Sg : Sig} {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → List MiniExpr → Option MiniExpr
  | _, _, _, .extern e, args =>
      if args.length == e.arity then
        match inlineExtern? cfg e args with
        | some body => some body
        | none => some (.call (var (externName e)) args)
      else none
  | _, _, _, .apN f args, acc => externCall? cfg depth f (spineOf cfg depth args ++ acc)
  | _, _, _, _, _ => none

/-- One of the operations that are JavaScript’s rather than Lean’s (`JsOp`), applied to
    exactly the arguments its type gives it. -/
partial def jsOpExpr (cfg : JsConfig) (depth : Nat) :
    ∀ {Sg : Sig} {Γ : Ctx} {σs : List Ty} {τ : Ty}, JsOp σs τ → Spine Sg Γ σs → MiniExpr
  -- a cast is a reinterpretation, and prints as its argument alone, except where the
  -- two types are represented differently: crossing between a number and a `BigInt` is
  -- a conversion, because they are two JavaScript types
  | _, _, _, _, .cast σ τ, .cons a .nil => castExpr cfg σ τ (exprOf cfg depth a)
  | _, _, _, _, .boolAnd, .cons a (.cons b .nil) =>
      .binary (exprOf cfg depth a) .and (exprOf cfg depth b)
  | _, _, _, _, .boolOr, .cons a (.cons b .nil) =>
      .binary (exprOf cfg depth a) .or (exprOf cfg depth b)
  | _, _, _, _, .boolNot, .cons a .nil => .unary .not (exprOf cfg depth a)
  | _, _, _, _, .boolBEq, .cons a (.cons b .nil) =>
      .binary (exprOf cfg depth a) .strictEq (exprOf cfg depth b)
  | _, _, _, _, .charBEq, .cons a (.cons b .nil) =>
      .binary (exprOf cfg depth a) .strictEq (exprOf cfg depth b)
  | _, _, _, _, .natSubExact, .cons a (.cons b .nil) =>
      .binary (exprOf cfg depth a) .minus (exprOf cfg depth b)
  | _, _, _, _, .toStr _, .cons a .nil => .call (var "String") [exprOf cfg depth a]

/-- The body of an arrow function: an expression when the term is one, a block when it
    needs statements. -/
partial def arrowBody (cfg : JsConfig) (depth : Nat) :
    ∀ {Sg : Sig} {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → MiniArrowBody
  | _, _, _, .letE e b => .block (stmtsOf cfg depth (.letE e b))
  | _, _, _, .caseTag s alts h => .block (stmtsOf cfg depth (.caseTag s alts h))
  | _, _, _, .loop init body => .block (stmtsOf cfg depth (.loop init body))
  | _, _, _, .ite c t e => .block (stmtsOf cfg depth (.ite c t e))
  | _, _, _, t => .expr (exprOf cfg depth t)

/-- `(() => { … })()`, for a block in expression position. -/
partial def iife (body : List MiniStatement) : MiniExpr :=
  .call (.arrow [] (.block body)) []

/-- The arguments of a call, in order. -/
partial def spineOf (cfg : JsConfig) (depth : Nat) :
    ∀ {Sg : Sig} {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → List MiniExpr
  | _, _, _, .nil => []
  | _, _, _, .cons t rest => exprOf cfg depth t :: spineOf cfg depth rest

/-- `{ tag: i, _1: …, _2: … }`: a value of constructor number `i` holding these
    fields, which are named by their position. -/
partial def ctorExpr (i : Nat) (vals : List MiniExpr) : MiniExpr :=
  .object (.keyValue (.ident (ident "tag")) (num i) ::
    vals.zipIdx.map fun (v, j) => MiniProperty.keyValue (.ident (ident (fieldName j))) v)

/-- A term in tail position: a block of statements ending in a `return`. -/
partial def stmtsOf (cfg : JsConfig) (depth : Nat) :
    ∀ {Sg : Sig} {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → List MiniStatement
  | _, _, _, .letE e b =>
      .decl .const ⟨⟨.ident (ident (depthName depth)), some (exprOf cfg depth e)⟩, []⟩ ::
        stmtsOf cfg (depth + 1) b
  | _, _, _, .ite c t e =>
      [.if_ (exprOf cfg depth c) (.block (stmtsOf cfg depth t)) (some (.block (stmtsOf cfg depth e)))]
  | _, _, _, .caseTag s alts _ =>
      let sc := exprOf cfg depth s
      altStmts cfg depth sc alts
  | _, _, _, .loop init body =>
      let n := spineLen init
      let inits := spineOf cfg depth init
      let decls := (List.range n).map fun i =>
        (⟨.ident (ident (depthName (depth + i))), inits[i]?⟩ : MiniDeclarator)
      -- the loop is in tail position of the function (or of the arrow an expression
      -- position wraps it in), so a `Body.ret` is a `return` of that function: no exit
      -- flag and no result variable are needed
      let declStmt : MiniStatement :=
        match decls with
        | [] => .empty
        | d :: ds => .decl .let_ ⟨d, ds⟩
      [ declStmt
      , .while_ .true_ (.block (bodyStmts cfg (depth + n) depth n body)) ]
  -- `const j = (v₀, …) => { … };` in front of the block the join point is in scope in:
  -- the parameters shadow the name inside the arrow, which is harmless, since a join
  -- point is never in scope in its own body
  | _, _, _, .joinPoint (params := ps) body rest =>
      let n := ps.length
      let names := (List.range n).map
        (fun i => MiniParam.plain (.ident (ident (depthName (depth + i)))))
      .decl .const ⟨⟨.ident (ident (depthName depth)),
          some (.arrow names (arrowBody cfg (depth + n) body))⟩, []⟩ ::
        stmtsOf cfg (depth + 1) rest
  | _, _, _, t => [.return_ (some (exprOf cfg depth t))]

/-- The branches of a case, as a chain of `if`s on the tag. -/
partial def altStmts (cfg : JsConfig) (depth : Nat) (sc : MiniExpr) :
    ∀ {Sg : Sig} {Γ : Ctx} {τ : Ty} {tags : List Nat}, Alts Sg Γ τ tags → List MiniStatement
  | _, _, _, _, .deflt t => stmtsOf cfg depth t
  | _, _, _, _, .cons tag t rest =>
      .if_ (.binary (.dot sc (ident "tag")) .strictEq (num tag))
          (.block (stmtsOf cfg depth t)) none ::
        altStmts cfg depth sc rest

/-- The body of a loop.  `base` is the context length the loop variables start at, and
    `n` is how many of them there are. -/
partial def bodyStmts (cfg : JsConfig) (depth : Nat) (base : Nat) (n : Nat) :
    ∀ {Sg : Sig} {Γ : Ctx} {σs : List Ty} {τ : Ty}, Body Sg Γ σs τ → List MiniStatement
  | _, _, _, _, .ret t => [ .return_ (some (exprOf cfg depth t)) ]
  | _, _, _, _, .cont args =>
      let vals := spineOf cfg depth args
      let info := contSlotInfo depth base args 0
      -- The slots are assigned in order, so only an argument that reads a slot assigned
      -- before it has to be computed into a temporary first; an argument that is the
      -- slot itself is not assigned at all.
      let tmps := (List.range n).map fun i => "t$" ++ toString base ++ "$" ++ toString i
      let tmpDecls : List MiniStatement :=
        (List.range n).filterMap fun i =>
          match vals[i]?, info[i]? with
          | some v, some (true, _) => some (.decl .const ⟨⟨.ident (ident tmps[i]!), some v⟩, []⟩)
          | _, _ => none
      let assigns : List MiniStatement :=
        (List.range n).filterMap fun i =>
          match vals[i]?, info[i]? with
          | _, some (_, true) => none
          | some _, some (true, _) =>
              some (.expr (.assign (var (depthName (base + i))) .assign (var tmps[i]!)))
          | some v, _ => some (.expr (.assign (var (depthName (base + i))) .assign v))
          | _, _ => none
      tmpDecls ++ assigns ++ [.continue_ none]
  | _, _, _, _, .letB e b =>
      .decl .const ⟨⟨.ident (ident (depthName depth)), some (exprOf cfg depth e)⟩, []⟩ ::
        bodyStmts cfg (depth + 1) base n b
  | _, _, _, _, .iteB c t e =>
      [ .if_ (exprOf cfg depth c)
          (.block (bodyStmts cfg depth base n t))
          (some (.block (bodyStmts cfg depth base n e))) ]
  -- a join point of a loop block prints exactly as one of a term does: a local arrow
  -- that is only ever called, in front of the rest of the block
  | _, _, _, _, .joinPointB (params := ps) body rest =>
      let k := ps.length
      let names := (List.range k).map
        (fun i => MiniParam.plain (.ident (ident (depthName (depth + i)))))
      .decl .const ⟨⟨.ident (ident (depthName depth)),
          some (.arrow names (arrowBody cfg (depth + k) body))⟩, []⟩ ::
        bodyStmts cfg (depth + 1) base n rest

/-- How many values a spine holds. -/
partial def spineLen : ∀ {Sg : Sig} {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → Nat
  | _, _, _, .nil => 0
  | _, _, _, .cons _ rest => spineLen rest + 1

end

/-- One compiled top-level declaration: its JavaScript name and its value.  The value is
    a term of the signature `Sg`, which is the signature the whole module is emitted
    against, so a declaration can only mention names that signature declares. -/
structure JsDecl (Sg : Sig) where
  /-- The name the declaration is bound to, and exported under. -/
  name : String
  /-- Whether the module exports it. -/
  exported : Bool := true
  /-- Its value, as a closed term. -/
  value : Σ τ : Ty, Term Sg [] τ

/-! ## The externs a module uses

An extern prints as a call of the runtime function of that name, so the emitted module
has to *import* those functions: they are the only free names in it.  The set of them is
read off the terms, so a module imports exactly what it calls. -/

mutual

/-- The runtime names a term calls, in the order they occur. -/
partial def externsOfTerm (cfg : JsConfig) : ∀ {Sg : Sig} {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → List String
  | _, _, _, .var _ => []
  | _, _, _, .lit _ => []
  | _, _, _, .global _ => []
  -- an extern with an operator form prints as the operator, wherever it occurs, so the
  -- module does not import it
  | _, _, _, .extern e => if hasInlineForm cfg e then [] else [externName e]
  | _, _, _, .lamN b => externsOfTerm cfg b
  | _, _, _, .apN f args => externsOfTerm cfg f ++ externsOfSpine cfg args
  | _, _, _, .lamProd rets => externsOfSpine cfg rets
  | _, _, _, .callProd f args _ => externsOfTerm cfg f ++ externsOfSpine cfg args
  | _, _, _, .jsOp _ args => externsOfSpine cfg args
  | _, _, _, .lazyMk e | _, _, _, .lazyForce e => externsOfTerm cfg e
  | _, _, _, .letE e b => externsOfTerm cfg e ++ externsOfTerm cfg b
  | _, _, _, .ite c t e => externsOfTerm cfg c ++ externsOfTerm cfg t ++ externsOfTerm cfg e
  | _, _, _, .ctor _ _ _ args => externsOfSpine cfg args
  | _, _, _, .proj e _ _ _ => externsOfTerm cfg e
  | _, _, _, .tagOf e _ => externsOfTerm cfg e
  | _, _, _, .caseTag s alts _ => externsOfTerm cfg s ++ externsOfAlts cfg alts
  | _, _, _, .loop init body => externsOfSpine cfg init ++ externsOfBody cfg body
  | _, _, _, .joinPoint body rest => externsOfTerm cfg body ++ externsOfTerm cfg rest
  | _, _, _, .jump _ args => externsOfSpine cfg args

/-- The runtime names a spine calls. -/
partial def externsOfSpine (cfg : JsConfig) : ∀ {Sg : Sig} {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → List String
  | _, _, _, .nil => []
  | _, _, _, .cons t rest => externsOfTerm cfg t ++ externsOfSpine cfg rest

/-- The runtime names the branches of a case call. -/
partial def externsOfAlts (cfg : JsConfig) :
    ∀ {Sg : Sig} {Γ : Ctx} {τ : Ty} {tags : List Nat}, Alts Sg Γ τ tags → List String
  | _, _, _, _, .deflt t => externsOfTerm cfg t
  | _, _, _, _, .cons _ t rest => externsOfTerm cfg t ++ externsOfAlts cfg rest

/-- The runtime names a loop body calls. -/
partial def externsOfBody (cfg : JsConfig) :
    ∀ {Sg : Sig} {Γ : Ctx} {σs : List Ty} {τ : Ty}, Body Sg Γ σs τ → List String
  | _, _, _, _, .ret t => externsOfTerm cfg t
  | _, _, _, _, .cont args => externsOfSpine cfg args
  | _, _, _, _, .letB e b => externsOfTerm cfg e ++ externsOfBody cfg b
  | _, _, _, _, .iteB c t e => externsOfTerm cfg c ++ externsOfBody cfg t ++ externsOfBody cfg e
  | _, _, _, _, .joinPointB body rest => externsOfTerm cfg body ++ externsOfBody cfg rest

end

mutual

/-- The names of the *global* declarations a term mentions, in the order they occur.
    A global the emitted module does not bind itself is a free name of the module, and
    has to be imported like an extern is. -/
partial def globalsOfTerm : ∀ {Sg : Sig} {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → List String
  | _, _, _, .var _ => []
  | _, _, _, .lit _ => []
  | _, _, _, .global r => [r.name]
  | _, _, _, .extern _ => []
  | _, _, _, .lamN b => globalsOfTerm b
  | _, _, _, .apN f args => globalsOfTerm f ++ globalsOfSpine args
  | _, _, _, .lamProd rets => globalsOfSpine rets
  | _, _, _, .callProd f args _ => globalsOfTerm f ++ globalsOfSpine args
  | _, _, _, .jsOp _ args => globalsOfSpine args
  | _, _, _, .lazyMk e | _, _, _, .lazyForce e => globalsOfTerm e
  | _, _, _, .letE e b => globalsOfTerm e ++ globalsOfTerm b
  | _, _, _, .ite c t e => globalsOfTerm c ++ globalsOfTerm t ++ globalsOfTerm e
  | _, _, _, .ctor _ _ _ args => globalsOfSpine args
  | _, _, _, .proj e _ _ _ => globalsOfTerm e
  | _, _, _, .tagOf e _ => globalsOfTerm e
  | _, _, _, .caseTag s alts _ => globalsOfTerm s ++ globalsOfAlts alts
  | _, _, _, .loop init body => globalsOfSpine init ++ globalsOfBody body
  | _, _, _, .joinPoint body rest => globalsOfTerm body ++ globalsOfTerm rest
  | _, _, _, .jump _ args => globalsOfSpine args

/-- The globals a spine mentions. -/
partial def globalsOfSpine : ∀ {Sg : Sig} {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → List String
  | _, _, _, .nil => []
  | _, _, _, .cons t rest => globalsOfTerm t ++ globalsOfSpine rest

/-- The globals the branches of a case mention. -/
partial def globalsOfAlts :
    ∀ {Sg : Sig} {Γ : Ctx} {τ : Ty} {tags : List Nat}, Alts Sg Γ τ tags → List String
  | _, _, _, _, .deflt t => globalsOfTerm t
  | _, _, _, _, .cons _ t rest => globalsOfTerm t ++ globalsOfAlts rest

/-- The globals a loop body mentions. -/
partial def globalsOfBody :
    ∀ {Sg : Sig} {Γ : Ctx} {σs : List Ty} {τ : Ty}, Body Sg Γ σs τ → List String
  | _, _, _, _, .ret t => globalsOfTerm t
  | _, _, _, _, .cont args => globalsOfSpine args
  | _, _, _, _, .letB e b => globalsOfTerm e ++ globalsOfBody b
  | _, _, _, _, .iteB c t e => globalsOfTerm c ++ globalsOfBody t ++ globalsOfBody e
  | _, _, _, _, .joinPointB body rest => globalsOfTerm body ++ globalsOfBody rest

end

/-- `const <name> = <value>;` -/
def declStatement (cfg : JsConfig) {Sg : Sig} (d : JsDecl Sg) : MiniStatement :=
  .decl .const ⟨⟨.ident (ident d.name), some (exprOf cfg 0 d.value.2)⟩, []⟩

/-- Where a module of the runtime prelude sits, seen from a compiled module `depth`
    directories below the package root: `SnapshotsMy/GcdEntry.js` is at depth 1 and
    imports `../runtime/lean_runtime_nat_num.mjs`.  The prelude is split by knob
    (`LakeJs.Config`), so *which* file a name comes from depends both on the name and
    on the configuration. -/
def preludePathOf (cfg : JsConfig) (g : RuntimeGroup) (depth : Nat) : String :=
  (String.join (List.replicate depth "../")) ++ "runtime/" ++ cfg.preludeFileOf g

/-- The names this module imports from one module of the prelude, in order. -/
def namesOfGroup (names : List String) (g : RuntimeGroup) : List String :=
  names.filter fun n => runtimeGroupOf n == g

/-- `import { $lean_nat_gcd, … } from "…/runtime/lean_runtime_nat_num.mjs";` — one such
    import per module of the prelude the compiled module actually calls into, in the
    order `RuntimeGroup.all` lists them, and nothing at all for a module that calls no
    extern. -/
def preludeImport (cfg : JsConfig) (names : List String) (depth : Nat) : List MiniModuleItem :=
  RuntimeGroup.all.flatMap fun g =>
    let gnames := namesOfGroup names g
    if gnames.isEmpty then []
    else
      let specs := gnames.map fun n => ({ name := ident n, alias_ := none } : Specifier)
      [ .importDecl (.clause (MiniImportClause.mk! none none (some specs)
          (NEString.ofString! (preludePathOf cfg g depth)))) ]

/-- A whole compiled module: the import of the runtime functions it calls, then one item
    per declaration — an exported one written as `export const <name> = …;` at its
    definition site rather than collected into a trailing `export { … }` list. -/
def program (cfg : JsConfig) {Sg : Sig} (ds : List (JsDecl Sg)) (depth : Nat := 1) : MiniProgram :=
  let bound := ds.map (·.name)
  let externs := ds.flatMap fun d => externsOfTerm cfg d.value.2
  let free := (ds.flatMap fun d => globalsOfTerm d.value.2).filter fun n => !bound.contains n
  let imported := (externs ++ free).eraseDups.mergeSort (· ≤ ·)
  { items := preludeImport cfg imported depth ++ ds.map fun d =>
      if d.exported then MiniModuleItem.exportDecl (.decl (declStatement cfg d))
      else MiniModuleItem.stmt (declStatement cfg d) }

/-- The text of a compiled module. -/
def render (cfg : JsConfig) {Sg : Sig} (ds : List (JsDecl Sg)) (depth : Nat := 1) : String :=
  printProgram (program cfg ds depth)

end LakeJs.EmitJs
