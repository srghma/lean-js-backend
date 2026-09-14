// UInt8, UInt16, UInt32, Int8, Int16, Int32 are always representable exactly as a
// JS Number (max magnitude 2^32 < Number.MAX_SAFE_INTEGER = 2^53 - 1), so there is
// only one output mode for these — no BigInt needed, ever. This is the
// "PrimOpIntNonConfigurable" file: not affected by natRepr/intRepr/usizeRepr/
// uint64Repr/int64Repr configuration.
//
// Wrapping and representation rules:
// - Comparisons (==, !=, <, >, <=, >=) work directly on JS Numbers when both operands
//   are in the correct representation range.
// - UInt8 / UInt16 wrap arithmetic via `& 0xff` / `& 0xffff`.
// - UInt32 wraps arithmetic via `>>> 0`.
// - Int8 / Int16 wrap and sign-extend via `((x << 24) >> 24)` / `((x << 16) >> 16)`.
// - Int32 wraps via `| 0`, matching native 32-bit signed integer semantics.

// ---------------- TestUInt8 ----------------

export const TestUInt8$add = (a) => (b) => (a + b) & 0xff;
export const TestUInt8$sub = (a) => (b) => (a - b) & 0xff;
export const TestUInt8$eq = (a) => (b) => a === b;
export const TestUInt8$ne = (a) => (b) => a !== b;
export const TestUInt8$lt = (a) => (b) => a < b;
export const TestUInt8$gt = (a) => (b) => a > b;
export const TestUInt8$le = (a) => (b) => a <= b;
export const TestUInt8$ge = (a) => (b) => a >= b;
export const TestUInt8$mul = (a) => (b) => (a * b) & 0xff;
export const TestUInt8$div = (a) => (b) => (b !== 0 ? Math.floor(a / b) : 0);
export const TestUInt8$neg = (a) => (-a) & 0xff;

// ---------------- TestUInt16 ----------------

export const TestUInt16$add = (a) => (b) => (a + b) & 0xffff;
export const TestUInt16$sub = (a) => (b) => (a - b) & 0xffff;
export const TestUInt16$eq = (a) => (b) => a === b;
export const TestUInt16$ne = (a) => (b) => a !== b;
export const TestUInt16$lt = (a) => (b) => a < b;
export const TestUInt16$gt = (a) => (b) => a > b;
export const TestUInt16$le = (a) => (b) => a <= b;
export const TestUInt16$ge = (a) => (b) => a >= b;
export const TestUInt16$mul = (a) => (b) => (a * b) & 0xffff;
export const TestUInt16$div = (a) => (b) => (b !== 0 ? Math.floor(a / b) : 0);
export const TestUInt16$neg = (a) => (-a) & 0xffff;

// ---------------- TestUInt32 ----------------

export const TestUInt32$add = (a) => (b) => (a + b) >>> 0;
export const TestUInt32$sub = (a) => (b) => (a - b) >>> 0;
export const TestUInt32$eq = (a) => (b) => a === b;
export const TestUInt32$ne = (a) => (b) => a !== b;
export const TestUInt32$lt = (a) => (b) => a < b;
export const TestUInt32$gt = (a) => (b) => a > b;
export const TestUInt32$le = (a) => (b) => a <= b;
export const TestUInt32$ge = (a) => (b) => a >= b;
export const TestUInt32$mul = (a) => (b) => Math.imul(a, b) >>> 0;
export const TestUInt32$div = (a) => (b) => (b !== 0 ? Math.floor(a / b) : 0);
export const TestUInt32$neg = (a) => (-a) >>> 0;

// ---------------- TestInt8 ----------------

export const TestInt8$add = (a) => (b) => ((a + b) << 24) >> 24;
export const TestInt8$sub = (a) => (b) => ((a - b) << 24) >> 24;
export const TestInt8$eq = (a) => (b) => a === b;
export const TestInt8$ne = (a) => (b) => a !== b;
export const TestInt8$lt = (a) => (b) => a < b;
export const TestInt8$gt = (a) => (b) => a > b;
export const TestInt8$le = (a) => (b) => a <= b;
export const TestInt8$ge = (a) => (b) => a >= b;
export const TestInt8$mul = (a) => (b) => ((a * b) << 24) >> 24;
export const TestInt8$div = (a) => (b) =>
  (((b > 0 ? Math.floor(a / b) : b < 0 ? -Math.floor(a / -b) : 0) << 24) >> 24);
export const TestInt8$neg = (a) => (-a << 24) >> 24;

// ---------------- TestInt16 ----------------

export const TestInt16$add = (a) => (b) => ((a + b) << 16) >> 16;
export const TestInt16$sub = (a) => (b) => ((a - b) << 16) >> 16;
export const TestInt16$eq = (a) => (b) => a === b;
export const TestInt16$ne = (a) => (b) => a !== b;
export const TestInt16$lt = (a) => (b) => a < b;
export const TestInt16$gt = (a) => (b) => a > b;
export const TestInt16$le = (a) => (b) => a <= b;
export const TestInt16$ge = (a) => (b) => a >= b;
export const TestInt16$mul = (a) => (b) => ((a * b) << 16) >> 16;
export const TestInt16$div = (a) => (b) =>
  (((b > 0 ? Math.floor(a / b) : b < 0 ? -Math.floor(a / -b) : 0) << 16) >> 16);
export const TestInt16$neg = (a) => (-a << 16) >> 16;

// ---------------- TestInt32 ----------------

export const TestInt32$add = (a) => (b) => (a + b) | 0;
export const TestInt32$sub = (a) => (b) => (a - b) | 0;
export const TestInt32$eq = (a) => (b) => a === b;
export const TestInt32$ne = (a) => (b) => a !== b;
export const TestInt32$lt = (a) => (b) => a < b;
export const TestInt32$gt = (a) => (b) => a > b;
export const TestInt32$le = (a) => (b) => a <= b;
export const TestInt32$ge = (a) => (b) => a >= b;
export const TestInt32$mul = (a) => (b) => (a * b) | 0;
export const TestInt32$div = (a) => (b) =>
  b > 0 ? Math.floor(a / b) : b < 0 ? -Math.floor(a / -b) : 0;
export const TestInt32$neg = (a) => -a;
