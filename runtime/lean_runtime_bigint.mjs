// The runtime prelude of the Lean-to-JavaScript backend, for the `faithful`
// configuration.
//
// `runtime/lean_runtime.mjs` beside this file is the same prelude for the `pbo`
// configuration, where every numeric type is a JavaScript number.  Here the
// configurable types are `BigInt`s instead:
//
//   Nat, Int, USize, UInt64, Int64, ISize   a BigInt, exact at every size
//   UInt8/16/32, Int8/16/32                 a number (they always fit exactly)
//   String.Pos.Raw                          a number (a UTF-8 byte offset)
//   Char                                    a one-character JS string
//   String                                  a JS string
//   Array α                                 a JS array, used persistently
//
// A compiled module imports the externs it calls from the prelude its configuration
// names, so the two files never meet in one program: a `BigInt` is never `===` to a
// number, and mixing the two in an arithmetic operator throws.
//
// Everything whose behaviour does not depend on how a `Nat` is represented — the
// string, array and list operations, and the library declarations the optimiser
// leaves free — is re-exported from `lean_runtime.mjs` rather than written twice.
// Everything that does answer with, or take, a `Nat`-like value is defined here.

import {
  $lean_array_fset,
  $lean_array_mk,
  $lean_array_to_list,
  $lean_array_uget,
  $lean_array_uset,
  $lean_mk_array,
  $lean_string_append,
  $lean_string_hash,
  $lean_string_memcmp,
  $lean_string_mk,
  $lean_string_pos_raw_at_end,
  $lean_string_pos_raw_get,
  $lean_string_pos_raw_next,
  $lean_string_push,
  $lean_uint64_shift_right,
  $lean_uint64_xor,
  _private_Init_Data_Array_Basic_0_Array_foldrMUnsafe_fold,
  Array_append,
  Array_back_,
  Array_mkEmpty,
  Function_const,
  Id_instMonad,
  instBEqOfDecidableEq,
  instHashableString,
  List_reverse,
  Repr_addAppParen,
  String_quote,
  String_Slice_Pos_nextn,
  String_Slice_toString,
} from "./lean_runtime.mjs";

export {
  $lean_array_fset,
  $lean_array_mk,
  $lean_array_to_list,
  $lean_array_uget,
  $lean_array_uset,
  $lean_mk_array,
  $lean_string_append,
  $lean_string_hash,
  $lean_string_memcmp,
  $lean_string_mk,
  $lean_string_pos_raw_at_end,
  $lean_string_pos_raw_get,
  $lean_string_pos_raw_next,
  $lean_string_push,
  $lean_uint64_shift_right,
  $lean_uint64_xor,
  _private_Init_Data_Array_Basic_0_Array_foldrMUnsafe_fold,
  Array_append,
  Array_back_,
  Array_mkEmpty,
  Function_const,
  Id_instMonad,
  instBEqOfDecidableEq,
  instHashableString,
  List_reverse,
  Repr_addAppParen,
  String_quote,
  String_Slice_Pos_nextn,
  String_Slice_toString,
};

/** `x` taken modulo `2^64`. */
const U64 = (x) => BigInt.asUintN(64, BigInt(x));

/** `x` taken modulo `2^64` and read as a signed 64-bit value. */
const S64 = (x) => BigInt.asIntN(64, BigInt(x));

/** `x` taken modulo `2^w`, for a `w`-bit value held in a JavaScript number. */
const wrapU = (w, x) => {
  const m = 2 ** w;
  const r = Number(x) % m;
  return r < 0 ? r + m : r;
};

/** `x` taken modulo `2^w` and read as a signed `w`-bit number. */
const wrapS = (w, x) => {
  const m = 2 ** w;
  const r = wrapU(w, x);
  return r >= m / 2 ? r - m : r;
};

/* -------------------------------------------------------------- Nat and friends */

/** `Nat.gcd`. */
export const $lean_nat_gcd = (a, b) => {
  let x = a < 0n ? -a : a;
  let y = b < 0n ? -b : b;
  while (y !== 0n) {
    const t = x % y;
    x = y;
    y = t;
  }
  return x;
};

/** `Nat.div`: rounds down, and `n / 0` is `0`. */
export const $lean_nat_div = (a, b) => (b === 0n ? 0n : a / b);

/** `Int.ediv`, which is what `/` on `Int` is: the remainder is never negative. */
export const $lean_int_ediv = (a, b) => {
  if (b === 0n) return 0n;
  const q = a / b; // BigInt division truncates towards zero
  const r = a - q * b;
  return r < 0n ? (b > 0n ? q - 1n : q + 1n) : q;
};

/** `Int.neg`. */
export const $lean_int_neg = (a) => -a;

/** `Nat.reprFast`. */
export const Nat_reprFast = (n) => String(n);

/** `instHashableNat`. */
export const instHashableNat = (n) => U64(n);

/** `String.utf8ByteSize`; a `Nat`, hence a `BigInt`. */
export const $lean_string_utf8_byte_size = (s) => {
  let n = 0n;
  for (const ch of s) {
    const cp = ch.codePointAt(0);
    n += cp < 0x80 ? 1n : cp < 0x800 ? 2n : cp < 0x10000 ? 3n : 4n;
  }
  return n;
};

/* ------------------------------------------------------------------- fixed width */

/** `UInt64.ofNat`. */
export const $lean_uint64_of_nat = (n) => U64(n);

/** `USize.ofNat`. */
export const $lean_usize_of_nat = (n) => U64(n);

/** `UInt64.toUSize`: both are 64 bits wide here, so nothing is cut. */
export const $lean_uint64_to_usize = (a) => U64(a);

/** `USize.land`. */
export const $lean_usize_land = (a, b) => U64(a) & U64(b);

/** Unsigned division: rounds down, and `a / 0` is `0`. */
const udivN = (a, b) => (b === 0 ? 0 : Math.floor(a / b));
const udivB = (a, b) => (b === 0n ? 0n : a / b);

/** Signed division: truncates towards zero, wraps, and `a / 0` is `0`. */
const sdivN = (w, a, b) => (b === 0 ? 0 : wrapS(w, Math.trunc(a / b)));
const sdivB = (a, b) => (b === 0n ? 0n : S64(a / b));

/** `UInt8.div`. */
export const $lean_uint8_div = (a, b) => udivN(a, b);
/** `UInt16.div`. */
export const $lean_uint16_div = (a, b) => udivN(a, b);
/** `UInt32.div`. */
export const $lean_uint32_div = (a, b) => udivN(a, b);
/** `UInt64.div`. */
export const $lean_uint64_div = (a, b) => udivB(a, b);
/** `USize.div`. */
export const $lean_usize_div = (a, b) => udivB(a, b);

/** `Int8.div`. */
export const $lean_int8_div = (a, b) => sdivN(8, a, b);
/** `Int16.div`. */
export const $lean_int16_div = (a, b) => sdivN(16, a, b);
/** `Int32.div`. */
export const $lean_int32_div = (a, b) => sdivN(32, a, b);
/** `Int64.div`. */
export const $lean_int64_div = (a, b) => sdivB(a, b);
/** `ISize.div`. */
export const $lean_isize_div = (a, b) => sdivB(a, b);

/** `UInt8.neg`. */
export const $lean_uint8_neg = (a) => wrapU(8, -a);
/** `UInt16.neg`. */
export const $lean_uint16_neg = (a) => wrapU(16, -a);
/** `UInt32.neg`. */
export const $lean_uint32_neg = (a) => wrapU(32, -a);
/** `UInt64.neg`. */
export const $lean_uint64_neg = (a) => U64(-a);
/** `USize.neg`. */
export const $lean_usize_neg = (a) => U64(-a);

/** `Int8.neg`. */
export const $lean_int8_neg = (a) => wrapS(8, -a);
/** `Int16.neg`. */
export const $lean_int16_neg = (a) => wrapS(16, -a);
/** `Int32.neg`. */
export const $lean_int32_neg = (a) => wrapS(32, -a);
/** `Int64.neg`. */
export const $lean_int64_neg = (a) => S64(-a);
/** `ISize.neg`. */
export const $lean_isize_neg = (a) => S64(-a);

/** `Int8.ofNat`. */
export const $lean_int8_of_nat = (n) => wrapS(8, n);
/** `Int16.ofNat`. */
export const $lean_int16_of_nat = (n) => wrapS(16, n);
/** `Int32.ofNat`. */
export const $lean_int32_of_nat = (n) => wrapS(32, n);
/** `Int64.ofNat`. */
export const $lean_int64_of_nat = (n) => S64(n);
/** `ISize.ofNat`. */
export const $lean_isize_of_nat = (n) => S64(n);

/* ------------------------------------------------------------------- equalities */

/** `Int.instDecidableEq`. */
export const Int_instDecidableEq = (a, b) => a === b;
/** `instDecidableEqUSize`. */
export const instDecidableEqUSize = (a, b) => a === b;
/** `instDecidableEqUInt8`. */
export const instDecidableEqUInt8 = (a, b) => a === b;
/** `instDecidableEqUInt16`. */
export const instDecidableEqUInt16 = (a, b) => a === b;
/** `instDecidableEqUInt32`. */
export const instDecidableEqUInt32 = (a, b) => a === b;
/** `instDecidableEqUInt64`. */
export const instDecidableEqUInt64 = (a, b) => a === b;
/** `instDecidableEqInt8`. */
export const instDecidableEqInt8 = (a, b) => a === b;
/** `instDecidableEqInt16`. */
export const instDecidableEqInt16 = (a, b) => a === b;
/** `instDecidableEqInt32`. */
export const instDecidableEqInt32 = (a, b) => a === b;
/** `instDecidableEqInt64`. */
export const instDecidableEqInt64 = (a, b) => a === b;
/** `instDecidableEqISize`. */
export const instDecidableEqISize = (a, b) => a === b;

/* --------------------------------------------- the wrapping fixed-width arithmetic */

/** `UInt8.add`. */
export const $lean_uint8_add = (a, b) => wrapU(8, a + b);
/** `UInt16.add`. */
export const $lean_uint16_add = (a, b) => wrapU(16, a + b);
/** `UInt32.add`. */
export const $lean_uint32_add = (a, b) => wrapU(32, a + b);
/** `UInt64.add`. */
export const $lean_uint64_add = (a, b) => U64(a + b);
/** `USize.add`. */
export const $lean_usize_add = (a, b) => U64(a + b);

/** `UInt8.sub`. */
export const $lean_uint8_sub = (a, b) => wrapU(8, a - b);
/** `UInt16.sub`. */
export const $lean_uint16_sub = (a, b) => wrapU(16, a - b);
/** `UInt32.sub`. */
export const $lean_uint32_sub = (a, b) => wrapU(32, a - b);
/** `UInt64.sub`. */
export const $lean_uint64_sub = (a, b) => U64(a - b);
/** `USize.sub`. */
export const $lean_usize_sub = (a, b) => U64(a - b);

/** `UInt8.mul`. */
export const $lean_uint8_mul = (a, b) => wrapU(8, a * b);
/** `UInt16.mul`. */
export const $lean_uint16_mul = (a, b) => wrapU(16, a * b);
/** `UInt32.mul`. */
export const $lean_uint32_mul = (a, b) => wrapU(32, a * b);
/** `UInt64.mul`. */
export const $lean_uint64_mul = (a, b) => U64(a * b);
/** `USize.mul`. */
export const $lean_usize_mul = (a, b) => U64(a * b);

/** `Int.div`, which truncates towards zero; `a / 0` is `0`. */
export const $lean_int_div = (a, b) => (b === 0n ? 0n : a / b);

/** `Nat.mod`; `n % 0` is `n`. */
export const $lean_nat_mod = (a, b) => (b === 0n ? a : a % b);
/** `Nat.modCore`. */
export const $lean_nat_mod_core = (a, b) => (b === 0n ? a : a % b);

/* ------------------------------------------- the signed 64-bit wrapping arithmetic */

/** `Int64.add`. */
export const $lean_int64_add = (a, b) => S64(a + b);
/** `ISize.add`. */
export const $lean_isize_add = (a, b) => S64(a + b);
/** `Int64.sub`. */
export const $lean_int64_sub = (a, b) => S64(a - b);
/** `ISize.sub`. */
export const $lean_isize_sub = (a, b) => S64(a - b);
/** `Int64.mul`. */
export const $lean_int64_mul = (a, b) => S64(a * b);
/** `ISize.mul`. */
export const $lean_isize_mul = (a, b) => S64(a * b);

/** `Int64.decLt`. */
export const $lean_int64_dec_lt = (a, b) => a < b;
/** `Int64.decLe`. */
export const $lean_int64_dec_le = (a, b) => a <= b;
/** `ISize.decLt`. */
export const $lean_isize_dec_lt = (a, b) => a < b;
/** `ISize.decLe`. */
export const $lean_isize_dec_le = (a, b) => a <= b;

/* ---------------------------------------------------------- the bitwise operations
 *
 * Lean takes the shift distance of a 64-bit type modulo 64 (`BitVec.smod` for the
 * signed ones, so a negative distance counts from the top); `Nat` has no width, so
 * its shifts and bitwise operations are exact at every size.
 */

/** The shift distance Lean uses at 64 bits: the argument taken modulo 64. */
const shift64 = (b) => ((b % 64n) + 64n) % 64n;

/** `Nat.sub`, which truncates at zero. */
export const $lean_nat_sub = (a, b) => (a >= b ? a - b : 0n);

/** `UInt64.land`. */
export const $lean_uint64_land = (a, b) => U64(a & b);
/** `UInt64.lor`. */
export const $lean_uint64_lor = (a, b) => U64(a | b);
/** `UInt64.complement`. */
export const $lean_uint64_complement = (a) => U64(~a);
/** `UInt64.shiftLeft`. */
export const $lean_uint64_shift_left = (a, b) => U64(a << shift64(b));

/** `USize.lor`. */
export const $lean_usize_lor = (a, b) => U64(a | b);
/** `USize.xor`. */
export const $lean_usize_xor = (a, b) => U64(a ^ b);
/** `USize.complement`. */
export const $lean_usize_complement = (a) => U64(~a);
/** `USize.shiftLeft`. */
export const $lean_usize_shift_left = (a, b) => U64(a << shift64(b));
/** `USize.shiftRight`; the value is unsigned, so the shift brings in zeros. */
export const $lean_usize_shift_right = (a, b) => U64(a >> shift64(b));

/** `Int64.land`, on the two's complement. */
export const $lean_int64_land = (a, b) => S64(a & b);
/** `Int64.lor`. */
export const $lean_int64_lor = (a, b) => S64(a | b);
/** `Int64.xor`. */
export const $lean_int64_xor = (a, b) => S64(a ^ b);
/** `Int64.complement`. */
export const $lean_int64_complement = (a) => S64(~a);
/** `Int64.shiftLeft`. */
export const $lean_int64_shift_left = (a, b) => S64(a << shift64(b));
/** `Int64.shiftRight`, which is arithmetic: the sign bit is carried in. */
export const $lean_int64_shift_right = (a, b) => S64(a >> shift64(b));

/** `ISize.land`. */
export const $lean_isize_land = (a, b) => S64(a & b);
/** `ISize.lor`. */
export const $lean_isize_lor = (a, b) => S64(a | b);
/** `ISize.xor`. */
export const $lean_isize_xor = (a, b) => S64(a ^ b);
/** `ISize.complement`. */
export const $lean_isize_complement = (a) => S64(~a);
/** `ISize.shiftLeft`. */
export const $lean_isize_shift_left = (a, b) => S64(a << shift64(b));
/** `ISize.shiftRight`, arithmetic. */
export const $lean_isize_shift_right = (a, b) => S64(a >> shift64(b));

/** `Nat.land`. */
export const $lean_nat_land = (a, b) => a & b;
/** `Nat.lor`. */
export const $lean_nat_lor = (a, b) => a | b;
/** `Nat.xor`. */
export const $lean_nat_lxor = (a, b) => a ^ b;
/** `Nat.shiftLeft`, which does not wrap: a `Nat` has no width. */
export const $lean_nat_shiftl = (a, b) => a << b;
/** `Nat.shiftRight`. */
export const $lean_nat_shiftr = (a, b) => a >> b;

/** `Int.not`, the complement of an unbounded integer: `~~~a` is `-a - 1`. */
export const Int_not = (a) => -a - 1n;
