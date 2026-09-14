// UInt8, UInt16, UInt32, Int8, Int16, Int32 are always representable exactly as a
// JS Number (max magnitude 2^32 < Number.MAX_SAFE_INTEGER = 2^53 - 1), so there is
// only one output mode for these — no BigInt needed, ever. This is the
// "PrimOpIntUnitNonConfigurable" file: not affected by natRepr/intRepr/usizeRepr/
// uint64Repr/int64Repr configuration.
//
// Two things make this correct without BigInt:
// 1. JS's `&`, `|`, `^`, `~` operate on the ToInt32 bit pattern of their operands.
//    For AND/OR/XOR/NOT specifically, if both operands are already the correct
//    (sign-extended, for signed types) 32-bit representation of the value, the
//    32-bit-wide result IS already the correct answer at any narrower width w < 32:
//    bit i (i >= w-1) of the result only depends on bit i of each operand, and for
//    i >= w-1 those bits are just copies of the sign bit — so the upper bits come
//    out correctly sign-extended "for free". No masking needed for signed types.
// 2. `<<` and `>>` shift counts are automatically taken mod 32 by the JS spec, and
//    `<<`/`>>`/`~` on Int32 already produce a correctly wrapped, correctly signed
//    32-bit result — so Int32 needs zero special-casing at all.
// For unsigned types (UInt8/16/32) we mask to width after ops that can produce bits
// outside it (shiftLeft, complement), and for UInt32 specifically we need `>>> 0`
// after `&`/`|`/`^`/`~`/`<<` to turn the signed-int32 JS result back into the
// unsigned Number range [0, 2^32).

// ---------------- TestUInt8 ----------------

export const TestUInt8$land = (a) => (b) => (a & b) & 0xff;
export const TestUInt8$lor = (a) => (b) => (a | b) & 0xff;
export const TestUInt8$shiftLeft = (a) => (b) => (a << (((b % 8) + 8) % 8)) & 0xff;
export const TestUInt8$shiftRight = (a) => (b) => a >>> (((b % 8) + 8) % 8);
export const TestUInt8$xor = (a) => (b) => (a ^ b) & 0xff;
export const TestUInt8$complement = (a) => (~a) & 0xff;

// ---------------- TestUInt16 ----------------

export const TestUInt16$land = (a) => (b) => (a & b) & 0xffff;
export const TestUInt16$lor = (a) => (b) => (a | b) & 0xffff;
export const TestUInt16$shiftLeft = (a) => (b) => (a << (((b % 16) + 16) % 16)) & 0xffff;
export const TestUInt16$shiftRight = (a) => (b) => a >>> (((b % 16) + 16) % 16);
export const TestUInt16$xor = (a) => (b) => (a ^ b) & 0xffff;
export const TestUInt16$complement = (a) => (~a) & 0xffff;

// ---------------- TestUInt32 ----------------
// Native `&`/`|`/`^`/`~`/`<<` return a *signed* int32; `>>> 0` reinterprets that
// bit pattern as the unsigned Number JS side expects. `>>>` (logical shift) already
// returns an unsigned result on its own.

export const TestUInt32$land = (a) => (b) => (a & b) >>> 0;
export const TestUInt32$lor = (a) => (b) => (a | b) >>> 0;
export const TestUInt32$shiftLeft = (a) => (b) => (a << b) >>> 0; // shift count auto-mod-32
export const TestUInt32$shiftRight = (a) => (b) => a >>> b; // auto-mod-32, logical
export const TestUInt32$xor = (a) => (b) => (a ^ b) >>> 0;
export const TestUInt32$complement = (a) => (~a) >>> 0;

// ---------------- TestInt8 ----------------
// land/lor/xor/complement need no masking (see note above). shiftLeft needs
// masking + re-sign-extension since JS's native shift is 32-bit, not 8-bit.
// shiftRight needs no masking: arithmetic `>>` on an already-correctly-sign-
// extended int32 automatically performs the correct 8-bit arithmetic shift.

export const TestInt8$land = (a) => (b) => a & b;
export const TestInt8$lor = (a) => (b) => a | b;
export const TestInt8$shiftLeft = (a) => (b) => {
  const amt = ((b % 8) + 8) % 8;
  const r = ((a & 0xff) << amt) & 0xff;
  return r >= 128 ? r - 256 : r;
};
export const TestInt8$shiftRight = (a) => (b) => a >> (((b % 8) + 8) % 8);
export const TestInt8$xor = (a) => (b) => a ^ b;
export const TestInt8$complement = (a) => ~a;

// ---------------- TestInt16 ----------------

export const TestInt16$land = (a) => (b) => a & b;
export const TestInt16$lor = (a) => (b) => a | b;
export const TestInt16$shiftLeft = (a) => (b) => {
  const amt = ((b % 16) + 16) % 16;
  const r = ((a & 0xffff) << amt) & 0xffff;
  return r >= 32768 ? r - 65536 : r;
};
export const TestInt16$shiftRight = (a) => (b) => a >> (((b % 16) + 16) % 16);
export const TestInt16$xor = (a) => (b) => a ^ b;
export const TestInt16$complement = (a) => ~a;

// ---------------- TestInt32 ----------------
// Fully native: JS's `&`/`|`/`^`/`~`/`<<`/`>>` already operate at exactly 32 bits
// with automatic mod-32 shift counts, so these need nothing extra at all.

export const TestInt32$land = (a) => (b) => a & b;
export const TestInt32$lor = (a) => (b) => a | b;
export const TestInt32$shiftLeft = (a) => (b) => a << b;
export const TestInt32$shiftRight = (a) => (b) => a >> b;
export const TestInt32$xor = (a) => (b) => a ^ b;
export const TestInt32$complement = (a) => ~a;
