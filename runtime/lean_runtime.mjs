// The runtime prelude of the Lean-to-JavaScript backend.
//
// A compiled module calls a Lean `@[extern]` function by the name the catalogue
// (`LakeJs/Externs.lean`) gives it, prefixed with `$`, and imports it from this file:
//
//     import { $lean_nat_gcd } from "../runtime/lean_runtime.mjs";
//     export const gcd2 = (v0, v1) => $lean_nat_gcd(v0, v1);
//
// so an emitted module has no free names at all and runs under `node` as it stands.
// Only the externs the generated corpus actually uses are implemented here; adding one
// is adding an export whose name is the catalogue's.
//
// Representation (the `presetPBO` choice: a `Nat` is a JS `number`):
//
//   Nat, Int, USize, StringPos  a JS number (a `String.Pos.Raw` is a UTF-8 byte offset)
//   UInt64                      a BigInt, always masked to 64 bits
//   Char                        a one-character JS string
//   String                      a JS string
//   Array α                     a JS array, used persistently: a write copies
//
// Every function here is pure: it never mutates an argument, which is what lets the
// compiler treat a `Term` as a value.

const U64 = (x) => BigInt.asUintN(64, typeof x === "bigint" ? x : BigInt(x));

/* -------------------------------------------------------------- Nat and friends */

/** `Nat.gcd`. */
export const $lean_nat_gcd = (a, b) => {
  let x = a < 0 ? -a : a;
  let y = b < 0 ? -b : b;
  while (y !== 0) {
    const t = x % y;
    x = y;
    y = t;
  }
  return x;
};

/* ------------------------------------------------------------------- fixed width */

/** `UInt64.ofNat`. */
export const $lean_uint64_of_nat = (n) => U64(n);

/** `USize.ofNat`. */
export const $lean_usize_of_nat = (n) => Number(n);

/** `UInt64.xor`. */
export const $lean_uint64_xor = (a, b) => U64(U64(a) ^ U64(b));

/** `UInt64.shiftRight`; the shift is taken modulo 64, as Lean's is. */
export const $lean_uint64_shift_right = (a, b) => U64(U64(a) >> (U64(b) & 63n));

/**
 * `UInt64.toUSize`.  A `USize` is a JS number here, so the value is cut to the 53 bits
 * a number holds exactly — the *low* bits, which are the ones a hash bucket is masked
 * out of.
 */
export const $lean_uint64_to_usize = (a) => Number(U64(a) & 0x1fffffffffffffn);

/** `USize.land`, over the full width, via BigInt. */
export const $lean_usize_land = (a, b) => Number(BigInt(a) & BigInt(b));

/* ------------------------------------------------------------------------ arrays */

/** `Array.replicate`. */
export const $lean_mk_array = (n, v) => new Array(Number(n)).fill(v);

/** `Array.uget`. */
export const $lean_array_uget = (a, i) => a[Number(i)];

/** `Array.uset`: persistent, so it answers with a copy. */
export const $lean_array_uset = (a, i, v) => {
  const out = a.slice();
  out[Number(i)] = v;
  return out;
};

/** `Array.set`: persistent, so it answers with a copy. */
export const $lean_array_fset = (a, i, v) => {
  const out = a.slice();
  out[Number(i)] = v;
  return out;
};

/* ----------------------------------------------------------------------- strings */

const encoder = new TextEncoder();

/** How many UTF-8 bytes a code point takes. */
const cpBytes = (cp) => (cp < 0x80 ? 1 : cp < 0x800 ? 2 : cp < 0x10000 ? 3 : 4);

/** `String.utf8ByteSize`. */
export const $lean_string_utf8_byte_size = (s) => {
  let n = 0;
  for (const ch of s) n += cpBytes(ch.codePointAt(0));
  return n;
};

/** The character whose UTF-8 encoding begins at byte `pos`, and its byte length. */
const charAtByte = (s, pos) => {
  let at = 0;
  for (const ch of s) {
    const w = cpBytes(ch.codePointAt(0));
    if (at === pos) return [ch, w];
    at += w;
  }
  return [undefined, 1];
};

/** `String.Pos.Raw.get`; past the end, Lean answers `(default : Char)`, i.e. `'A'`. */
export const $lean_string_pos_raw_get = (s, pos) => {
  const [ch] = charAtByte(s, pos);
  return ch === undefined ? "A" : ch;
};

/** `String.Pos.Raw.next`. */
export const $lean_string_pos_raw_next = (s, pos) => {
  const [, w] = charAtByte(s, pos);
  return pos + w;
};

/** `String.Pos.Raw.atEnd`. */
export const $lean_string_pos_raw_at_end = (s, pos) =>
  pos >= $lean_string_utf8_byte_size(s);

/** `String.append`. */
export const $lean_string_append = (a, b) => a + b;

/**
 * `String.Slice.Pattern.Internal.memcmpStr`: are the `len` bytes of `lhs` at `lstart`
 * the same as the `len` bytes of `rhs` at `rstart`?
 */
export const $lean_string_memcmp = (lhs, rhs, lstart, rstart, len) => {
  const l = encoder.encode(lhs);
  const r = encoder.encode(rhs);
  for (let i = 0; i < len; i++) {
    if (l[lstart + i] !== r[rstart + i]) return false;
  }
  return true;
};

/**
 * `String.hash`.  Lean's own hash is not specified by the language, and nothing in a
 * compiled program may depend on its value — only on its being a function of the
 * string.  This is FNV-1a over the UTF-8 bytes, taken to 64 bits.
 */
export const $lean_string_hash = (s) => {
  let h = 0xcbf29ce484222325n;
  for (const b of encoder.encode(s)) {
    h = U64((h ^ BigInt(b)) * 0x100000001b3n);
  }
  return h;
};

/* ==================================================================================
 * Lean library declarations
 *
 * A compiled module only contains the declarations of the Lean module it was compiled
 * from; a declaration of the standard library that survives the optimiser is left as a
 * free name, and imported from here in exactly the same way an extern is.  The
 * definitions below follow the calling convention the backend uses for a Lean
 * declaration: type arguments and proofs are erased, a class with a single method is
 * unboxed into that method, a constructor is `{ tag, _1, _2, … }`, and an `Option` is
 * `{ tag: 0 }` for `none` and `{ tag: 1, _1: x }` for `some x`.
 * ================================================================================== */

/** `Function.const`, with its type arguments erased: `const a` ignores its argument. */
export const Function_const = (a, _b) => a;

/** `Int.instDecidableEq`; an `Int` is a JS number here. */
export const Int_instDecidableEq = (a, b) => a === b;

/** `instDecidableEqUSize`. */
export const instDecidableEqUSize = (a, b) => a === b;

/** `instBEqOfDecidableEq`: a `BEq` is its one method, and so is a `DecidableEq`. */
export const instBEqOfDecidableEq = (decEq) => decEq;

/** `instHashableString`: a `Hashable` is its one method. */
export const instHashableString = (s) => $lean_string_hash(s);

/** `instHashableNat`. */
export const instHashableNat = (n) => U64(n);

/** `Nat.reprFast`. */
export const Nat_reprFast = (n) => String(n);

/** `String.quote`. */
export const String_quote = (s) => {
  let out = '"';
  for (const ch of s) {
    out +=
      ch === "\\" ? "\\\\"
      : ch === '"' ? '\\"'
      : ch === "\n" ? "\\n"
      : ch === "\t" ? "\\t"
      : ch === "\r" ? "\\r"
      : ch;
  }
  return out + '"';
};

/** `Repr.addAppParen`: parenthesise a `Std.Format` when the context binds tighter. */
export const Repr_addAppParen = (f, prec) =>
  prec >= 1024
    ? { tag: 5, _1: { tag: 5, _1: { tag: 3, _1: "(" }, _2: f }, _2: { tag: 3, _1: ")" } }
    : f;

/** `List.reverse`; a `List` is `{ tag: 0 }` / `{ tag: 1, _1: head, _2: tail }`. */
export const List_reverse = (xs) => {
  let out = { tag: 0 };
  let cur = xs;
  while (cur.tag === 1) {
    out = { tag: 1, _1: cur._1, _2: out };
    cur = cur._2;
  }
  return out;
};

/** `Array.mkEmpty`: the capacity is a hint, and a JS array needs none. */
export const Array_mkEmpty = (_capacity) => [];

/** `Array.append`. */
export const Array_append = (a, b) => a.concat(b);

/** `Array.back?`. */
export const Array_back_ = (a) =>
  a.length === 0 ? { tag: 0 } : { tag: 1, _1: a[a.length - 1] };

/**
 * `Id.instMonad`.  The only monadic function of the corpus that takes a `Monad` and is
 * not compiled into the module is `Array.foldrMUnsafe.fold` below, which is only ever
 * handed this instance; the marker is what it checks for.
 */
export const Id_instMonad = { id: true };

/**
 * `Array.foldrMUnsafe.fold`: fold `f` over `as[stop … i)` from the right.  Only the
 * identity monad is supported — in it a monadic value *is* the value, so there is
 * nothing to bind.
 */
export const _private_Init_Data_Array_Basic_0_Array_foldrMUnsafe_fold = (
  monad,
  f,
  as,
  i,
  stop,
  b,
) => {
  if (monad !== Id_instMonad) {
    throw new Error("lean_runtime: Array.foldrMUnsafe.fold only supports Id");
  }
  let acc = b;
  let k = Number(i);
  const end = Number(stop);
  while (k > end) {
    k -= 1;
    acc = f(as[k], acc);
  }
  return acc;
};

/* ------------------------------------------------------- String.Slice
 *
 * A `String.Slice` is `{ tag: 0, _1: string, _2: startByte, _3: endByte }`, and a
 * position in it is a UTF-8 byte offset into `_1`.
 */

/** `String.Slice.Pos.nextn`: advance `n` characters. */
export const String_Slice_Pos_nextn = (slice, pos, n) => {
  let p = pos;
  for (let k = 0; k < n; k++) {
    if (p >= slice._3) return slice._3;
    p = $lean_string_pos_raw_next(slice._1, p);
  }
  return p > slice._3 ? slice._3 : p;
};

/** `String.Slice.toString`: the characters between the two byte offsets. */
export const String_Slice_toString = (slice) => {
  let out = "";
  let at = 0;
  for (const ch of slice._1) {
    const w = cpBytes(ch.codePointAt(0));
    if (at >= slice._2 && at < slice._3) out += ch;
    at += w;
  }
  return out;
};

/* ------------------------------------------------- List and Array conversions
 *
 * Lean declares `Array α` as a structure holding a `List α`; the backend represents it
 * as a JavaScript array instead, so `Array.mk` and `Array.toList` are conversions.
 */

/** `Array.mk`: a JavaScript array out of a `List`. */
export const $lean_array_mk = (xs) => {
  const out = [];
  let cur = xs;
  while (cur.tag === 1) {
    out.push(cur._1);
    cur = cur._2;
  }
  return out;
};

/** `Array.toList`. */
export const $lean_array_to_list = (a) => {
  let out = { tag: 0 };
  for (let i = a.length - 1; i >= 0; i--) out = { tag: 1, _1: a[i], _2: out };
  return out;
};

/** `String.mk`: a string out of a `List Char`. */
export const $lean_string_mk = (chars) => $lean_array_mk(chars).join("");

/** `String.push`: a `Char` is a one-character string here. */
export const $lean_string_push = (s, c) => s + c;

/* ================================================================================
 * Integer division, negation and equality
 *
 * The functions below are the `@[extern]`s of Lean's division, negation and
 * `DecidableEq` on the integer types.  This prelude is the one the `pbo`
 * configuration uses, so `Nat`, `Int`, `USize`, `UInt64`, `Int64` and `ISize` are
 * JavaScript numbers here; a 64-bit value beyond `2^53` is therefore rounded, which
 * is the trade-off that configuration makes.  Wrapping at 64 bits still goes through
 * `BigInt`, so the wrap itself is exact.
 *
 * Lean's semantics, which these follow:
 *
 *   - division by zero answers zero, at every integer type;
 *   - a fixed-width division truncates towards zero and wraps (`Int8.div (-128) (-1)`
 *     is `-128`);
 *   - `Int./` is `Int.ediv`: the remainder is never negative;
 *   - `Nat./` rounds down.
 * ================================================================================ */

/** `x` taken modulo `2^w`, for `w ≤ 32`. */
const wrapU = (w, x) => {
  const m = 2 ** w;
  const r = x % m;
  return r < 0 ? r + m : r;
};

/** `x` taken modulo `2^w` and read as a signed `w`-bit value, for `w ≤ 32`. */
const wrapS = (w, x) => {
  const m = 2 ** w;
  const r = wrapU(w, x);
  return r >= m / 2 ? r - m : r;
};

/** `x` taken modulo `2^64`, exactly, and then back to a number. */
const wrapU64 = (x) => Number(BigInt.asUintN(64, BigInt(x)));

/** `x` taken modulo `2^64` and read as a signed 64-bit value. */
const wrapS64 = (x) => Number(BigInt.asIntN(64, BigInt(x)));

/** Unsigned division at `w ≤ 32` bits: rounds down, and `a / 0` is `0`. */
const udiv = (a, b) => (b === 0 ? 0 : Math.floor(a / b));

/** Unsigned division at 64 bits, computed exactly. */
const udiv64 = (a, b) => (b === 0 ? 0 : wrapU64(BigInt(a) / BigInt(b)));

/** Signed division at `w ≤ 32` bits: truncates towards zero, wraps, and `a / 0` is `0`. */
const sdiv = (w, a, b) => (b === 0 ? 0 : wrapS(w, Math.trunc(a / b)));

/** Signed division at 64 bits, computed exactly. */
const sdiv64 = (a, b) => (b === 0 ? 0 : wrapS64(BigInt(a) / BigInt(b)));

/** `Nat.div`: rounds down, and `n / 0` is `0`. */
export const $lean_nat_div = (a, b) => (b === 0 ? 0 : Math.floor(a / b));

/** `Int.ediv`, which is what `/` on `Int` is: the remainder is never negative. */
export const $lean_int_ediv = (a, b) => {
  if (b === 0) return 0;
  const q = Math.trunc(a / b);
  const r = a - q * b;
  return r < 0 ? (b > 0 ? q - 1 : q + 1) : q;
};

/** `Int.neg`. */
export const $lean_int_neg = (a) => -a;

/** `UInt8.div`. */
export const $lean_uint8_div = (a, b) => udiv(a, b);
/** `UInt16.div`. */
export const $lean_uint16_div = (a, b) => udiv(a, b);
/** `UInt32.div`. */
export const $lean_uint32_div = (a, b) => udiv(a, b);
/** `UInt64.div`. */
export const $lean_uint64_div = (a, b) => udiv64(a, b);
/** `USize.div`. */
export const $lean_usize_div = (a, b) => udiv64(a, b);

/** `Int8.div`. */
export const $lean_int8_div = (a, b) => sdiv(8, a, b);
/** `Int16.div`. */
export const $lean_int16_div = (a, b) => sdiv(16, a, b);
/** `Int32.div`. */
export const $lean_int32_div = (a, b) => sdiv(32, a, b);
/** `Int64.div`. */
export const $lean_int64_div = (a, b) => sdiv64(a, b);
/** `ISize.div`. */
export const $lean_isize_div = (a, b) => sdiv64(a, b);

/** `UInt8.neg`. */
export const $lean_uint8_neg = (a) => wrapU(8, -a);
/** `UInt16.neg`. */
export const $lean_uint16_neg = (a) => wrapU(16, -a);
/** `UInt32.neg`. */
export const $lean_uint32_neg = (a) => wrapU(32, -a);
/** `UInt64.neg`. */
export const $lean_uint64_neg = (a) => wrapU64(-BigInt(a));
/** `USize.neg`. */
export const $lean_usize_neg = (a) => wrapU64(-BigInt(a));

/** `Int8.neg`. */
export const $lean_int8_neg = (a) => wrapS(8, -a);
/** `Int16.neg`. */
export const $lean_int16_neg = (a) => wrapS(16, -a);
/** `Int32.neg`. */
export const $lean_int32_neg = (a) => wrapS(32, -a);
/** `Int64.neg`. */
export const $lean_int64_neg = (a) => wrapS64(-BigInt(a));
/** `ISize.neg`. */
export const $lean_isize_neg = (a) => wrapS64(-BigInt(a));

/** `Int8.ofNat`. */
export const $lean_int8_of_nat = (n) => wrapS(8, n);
/** `Int16.ofNat`. */
export const $lean_int16_of_nat = (n) => wrapS(16, n);
/** `Int32.ofNat`. */
export const $lean_int32_of_nat = (n) => wrapS(32, n);
/** `Int64.ofNat`. */
export const $lean_int64_of_nat = (n) => wrapS64(n);
/** `ISize.ofNat`. */
export const $lean_isize_of_nat = (n) => wrapS64(n);

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

/* --------------------------------------------- the wrapping fixed-width arithmetic
 *
 * Addition, subtraction and multiplication of the unsigned fixed-width types wrap,
 * which the JavaScript operator does not, so the printer never writes these as
 * operators: they are calls of the functions below.
 */

/** `UInt8.add`. */
export const $lean_uint8_add = (a, b) => wrapU(8, a + b);
/** `UInt16.add`. */
export const $lean_uint16_add = (a, b) => wrapU(16, a + b);
/** `UInt32.add`. */
export const $lean_uint32_add = (a, b) => wrapU(32, a + b);
/** `UInt64.add`. */
export const $lean_uint64_add = (a, b) => wrapU64(BigInt(a) + BigInt(b));
/** `USize.add`. */
export const $lean_usize_add = (a, b) => wrapU64(BigInt(a) + BigInt(b));

/** `UInt8.sub`. */
export const $lean_uint8_sub = (a, b) => wrapU(8, a - b);
/** `UInt16.sub`. */
export const $lean_uint16_sub = (a, b) => wrapU(16, a - b);
/** `UInt32.sub`. */
export const $lean_uint32_sub = (a, b) => wrapU(32, a - b);
/** `UInt64.sub`. */
export const $lean_uint64_sub = (a, b) => wrapU64(BigInt(a) - BigInt(b));
/** `USize.sub`. */
export const $lean_usize_sub = (a, b) => wrapU64(BigInt(a) - BigInt(b));

/** `UInt8.mul`. */
export const $lean_uint8_mul = (a, b) => wrapU(8, a * b);
/** `UInt16.mul`. */
export const $lean_uint16_mul = (a, b) => wrapU(16, a * b);
/** `UInt32.mul`. */
export const $lean_uint32_mul = (a, b) => wrapU(32, a * b);
/** `UInt64.mul`. */
export const $lean_uint64_mul = (a, b) => wrapU64(BigInt(a) * BigInt(b));
/** `USize.mul`. */
export const $lean_usize_mul = (a, b) => wrapU64(BigInt(a) * BigInt(b));

/** `Int.div`, which truncates towards zero; `a / 0` is `0`. */
export const $lean_int_div = (a, b) => (b === 0 ? 0 : Math.trunc(a / b));

/** `Nat.mod`; `n % 0` is `n`. */
export const $lean_nat_mod = (a, b) => (b === 0 ? a : a % b);
/** `Nat.modCore`. */
export const $lean_nat_mod_core = (a, b) => (b === 0 ? a : a % b);

/* ------------------------------------------- the signed 64-bit wrapping arithmetic
 *
 * `Int64` and `ISize` wrap at 64 bits exactly as the unsigned types do, and the
 * JavaScript operator does not wrap, so these are calls rather than operators.  The
 * work is done over `BigInt`, which is exact at 64 bits, and the answer is read back
 * as a number, which is how this prelude represents the type.
 */

/** `Int64.add`. */
export const $lean_int64_add = (a, b) => wrapS64(BigInt(a) + BigInt(b));
/** `ISize.add`. */
export const $lean_isize_add = (a, b) => wrapS64(BigInt(a) + BigInt(b));
/** `Int64.sub`. */
export const $lean_int64_sub = (a, b) => wrapS64(BigInt(a) - BigInt(b));
/** `ISize.sub`. */
export const $lean_isize_sub = (a, b) => wrapS64(BigInt(a) - BigInt(b));
/** `Int64.mul`. */
export const $lean_int64_mul = (a, b) => wrapS64(BigInt(a) * BigInt(b));
/** `ISize.mul`. */
export const $lean_isize_mul = (a, b) => wrapS64(BigInt(a) * BigInt(b));

/** `Int64.decLt`. */
export const $lean_int64_dec_lt = (a, b) => a < b;
/** `Int64.decLe`. */
export const $lean_int64_dec_le = (a, b) => a <= b;
/** `ISize.decLt`. */
export const $lean_isize_dec_lt = (a, b) => a < b;
/** `ISize.decLe`. */
export const $lean_isize_dec_le = (a, b) => a <= b;

/* --------------------------------------------------- the bitwise operations
 *
 * Lean takes the shift distance of a 64-bit type modulo 64 (`BitVec.smod` for the
 * signed ones, so a negative distance counts from the top), and `Nat`'s shifts and
 * bitwise operations are exact at every size.  Everything here is computed over
 * `BigInt` and read back the way this prelude represents the type.
 */

/** The shift distance Lean uses at 64 bits: the argument taken modulo 64. */
const shift64 = (b) => ((BigInt(b) % 64n) + 64n) % 64n;

/** `UInt64.land`. */
export const $lean_uint64_land = (a, b) => wrapU64(BigInt(a) & BigInt(b));
/** `UInt64.lor`. */
export const $lean_uint64_lor = (a, b) => wrapU64(BigInt(a) | BigInt(b));
/** `UInt64.complement`. */
export const $lean_uint64_complement = (a) => wrapU64(~BigInt(a));
/** `UInt64.shiftLeft`. */
export const $lean_uint64_shift_left = (a, b) => wrapU64(BigInt(a) << shift64(b));

/** `USize.lor`. */
export const $lean_usize_lor = (a, b) => wrapU64(BigInt(a) | BigInt(b));
/** `USize.xor`. */
export const $lean_usize_xor = (a, b) => wrapU64(BigInt(a) ^ BigInt(b));
/** `USize.complement`. */
export const $lean_usize_complement = (a) => wrapU64(~BigInt(a));
/** `USize.shiftLeft`. */
export const $lean_usize_shift_left = (a, b) => wrapU64(BigInt(a) << shift64(b));
/** `USize.shiftRight`; the value is unsigned, so the shift brings in zeros. */
export const $lean_usize_shift_right = (a, b) => wrapU64(BigInt(a) >> shift64(b));

/** `Int64.land`, on the two's complement. */
export const $lean_int64_land = (a, b) => wrapS64(BigInt(a) & BigInt(b));
/** `Int64.lor`. */
export const $lean_int64_lor = (a, b) => wrapS64(BigInt(a) | BigInt(b));
/** `Int64.xor`. */
export const $lean_int64_xor = (a, b) => wrapS64(BigInt(a) ^ BigInt(b));
/** `Int64.complement`. */
export const $lean_int64_complement = (a) => wrapS64(~BigInt(a));
/** `Int64.shiftLeft`. */
export const $lean_int64_shift_left = (a, b) => wrapS64(BigInt(a) << shift64(b));
/** `Int64.shiftRight`, which is arithmetic: the sign bit is carried in. */
export const $lean_int64_shift_right = (a, b) => wrapS64(BigInt(a) >> shift64(b));

/** `ISize.land`. */
export const $lean_isize_land = (a, b) => wrapS64(BigInt(a) & BigInt(b));
/** `ISize.lor`. */
export const $lean_isize_lor = (a, b) => wrapS64(BigInt(a) | BigInt(b));
/** `ISize.xor`. */
export const $lean_isize_xor = (a, b) => wrapS64(BigInt(a) ^ BigInt(b));
/** `ISize.complement`. */
export const $lean_isize_complement = (a) => wrapS64(~BigInt(a));
/** `ISize.shiftLeft`. */
export const $lean_isize_shift_left = (a, b) => wrapS64(BigInt(a) << shift64(b));
/** `ISize.shiftRight`, arithmetic. */
export const $lean_isize_shift_right = (a, b) => wrapS64(BigInt(a) >> shift64(b));

/** `Nat.land`. */
export const $lean_nat_land = (a, b) => Number(BigInt(a) & BigInt(b));
/** `Nat.lor`. */
export const $lean_nat_lor = (a, b) => Number(BigInt(a) | BigInt(b));
/** `Nat.xor`. */
export const $lean_nat_lxor = (a, b) => Number(BigInt(a) ^ BigInt(b));
/** `Nat.shiftLeft`, which does not wrap: a `Nat` has no width. */
export const $lean_nat_shiftl = (a, b) => Number(BigInt(a) << BigInt(b));
/** `Nat.shiftRight`. */
export const $lean_nat_shiftr = (a, b) => Number(BigInt(a) >> BigInt(b));

/** `Int.not`, the complement of an unbounded integer: `~~~a` is `-a - 1`. */
export const Int_not = (a) => -a - 1;
