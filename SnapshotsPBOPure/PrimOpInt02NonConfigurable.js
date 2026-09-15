// UInt8, UInt16, UInt32, Int8, Int16, Int32 are always representable exactly as a
// JS Number (max magnitude 2^32 < Number.MAX_SAFE_INTEGER = 2^53 - 1), so there is
// only one output mode for these — no BigInt needed, ever. This is the
// "PrimOpIntNonConfigurable" file: not affected by natRepr/intRepr/usizeRepr/
// uint64Repr/int64Repr configuration.
//
// In `PrimOpInt02`, `intValues` is marked `@[inline]` and evaluated at compile time,
// so all static applications of primitive operations in `test1`–`test11` are fully
// inlined and computed.

// ---------------- TestUInt8 ----------------

export const TestUInt8$intValues = (op) => [
  op(1)(1),
  op(1)(2),
  op(2)(1),
  op(1)(254),
  op(255)(2),
  op(255)(255),
];

export const TestUInt8$test1 = [2, 3, 3, 255, 1, 254];
export const TestUInt8$test2 = [0, 255, 1, 3, 253, 0];
export const TestUInt8$test3 = [true, false, false, false, false, true];
export const TestUInt8$test4 = [false, true, true, true, true, false];
export const TestUInt8$test5 = [false, true, false, true, false, false];
export const TestUInt8$test6 = [false, false, true, false, true, false];
export const TestUInt8$test7 = [true, true, false, true, false, true];
export const TestUInt8$test8 = [true, false, true, false, true, true];
export const TestUInt8$test9 = [1, 2, 2, 254, 254, 1];
export const TestUInt8$test10 = [1, 0, 2, 0, 127, 1];
export const TestUInt8$test11 = [255, 1];

// ---------------- TestUInt16 ----------------

export const TestUInt16$intValues = (op) => [
  op(1)(1),
  op(1)(2),
  op(2)(1),
  op(1)(65534),
  op(65535)(2),
  op(65535)(65535),
];

export const TestUInt16$test1 = [2, 3, 3, 65535, 1, 65534];
export const TestUInt16$test2 = [0, 65535, 1, 3, 65533, 0];
export const TestUInt16$test3 = [true, false, false, false, false, true];
export const TestUInt16$test4 = [false, true, true, true, true, false];
export const TestUInt16$test5 = [false, true, false, true, false, false];
export const TestUInt16$test6 = [false, false, true, false, true, false];
export const TestUInt16$test7 = [true, true, false, true, false, true];
export const TestUInt16$test8 = [true, false, true, false, true, true];
export const TestUInt16$test9 = [1, 2, 2, 65534, 65534, 1];
export const TestUInt16$test10 = [1, 0, 2, 0, 32767, 1];
export const TestUInt16$test11 = [65535, 1];

// ---------------- TestUInt32 ----------------

export const TestUInt32$intValues = (op) => [
  op(1)(1),
  op(1)(2),
  op(2)(1),
  op(1)(4294967294),
  op(4294967295)(2),
  op(4294967295)(4294967295),
];

export const TestUInt32$test1 = [2, 3, 3, 4294967295, 1, 4294967294];
export const TestUInt32$test2 = [0, 4294967295, 1, 3, 4294967293, 0];
export const TestUInt32$test3 = [true, false, false, false, false, true];
export const TestUInt32$test4 = [false, true, true, true, true, false];
export const TestUInt32$test5 = [false, true, false, true, false, false];
export const TestUInt32$test6 = [false, false, true, false, true, false];
export const TestUInt32$test7 = [true, true, false, true, false, true];
export const TestUInt32$test8 = [true, false, true, false, true, true];
export const TestUInt32$test9 = [1, 2, 2, 4294967294, 4294967294, 1];
export const TestUInt32$test10 = [1, 0, 2, 0, 2147483647, 1];
export const TestUInt32$test11 = [4294967295, 1];

// ---------------- TestInt8 ----------------

export const TestInt8$intValues = (op) => [
  op(1)(1),
  op(1)(2),
  op(2)(1),
  op(1)(-2),
  op(-1)(2),
  op(-1)(-1),
];

export const TestInt8$test1 = [2, 3, 3, -1, 1, -2];
export const TestInt8$test2 = [0, -1, 1, 3, -3, 0];
export const TestInt8$test3 = [true, false, false, false, false, true];
export const TestInt8$test4 = [false, true, true, true, true, false];
export const TestInt8$test5 = [false, true, false, false, true, false];
export const TestInt8$test6 = [false, false, true, true, false, false];
export const TestInt8$test7 = [true, true, false, false, true, true];
export const TestInt8$test8 = [true, false, true, true, false, true];
export const TestInt8$test9 = [1, 2, 2, -2, -2, 1];
export const TestInt8$test10 = [1, 0, 2, 0, -1, 1];
export const TestInt8$test11 = [-1, 1];

// ---------------- TestInt16 ----------------

export const TestInt16$intValues = (op) => [
  op(1)(1),
  op(1)(2),
  op(2)(1),
  op(1)(-2),
  op(-1)(2),
  op(-1)(-1),
];

export const TestInt16$test1 = [2, 3, 3, -1, 1, -2];
export const TestInt16$test2 = [0, -1, 1, 3, -3, 0];
export const TestInt16$test3 = [true, false, false, false, false, true];
export const TestInt16$test4 = [false, true, true, true, true, false];
export const TestInt16$test5 = [false, true, false, false, true, false];
export const TestInt16$test6 = [false, false, true, true, false, false];
export const TestInt16$test7 = [true, true, false, false, true, true];
export const TestInt16$test8 = [true, false, true, true, false, true];
export const TestInt16$test9 = [1, 2, 2, -2, -2, 1];
export const TestInt16$test10 = [1, 0, 2, 0, -1, 1];
export const TestInt16$test11 = [-1, 1];

// ---------------- TestInt32 ----------------

export const TestInt32$intValues = (op) => [
  op(1)(1),
  op(1)(2),
  op(2)(1),
  op(1)(-2),
  op(-1)(2),
  op(-1)(-1),
];

export const TestInt32$test1 = [2, 3, 3, -1, 1, -2];
export const TestInt32$test2 = [0, -1, 1, 3, -3, 0];
export const TestInt32$test3 = [true, false, false, false, false, true];
export const TestInt32$test4 = [false, true, true, true, true, false];
export const TestInt32$test5 = [false, true, false, false, true, false];
export const TestInt32$test6 = [false, false, true, true, false, false];
export const TestInt32$test7 = [true, true, false, false, true, true];
export const TestInt32$test8 = [true, false, true, true, false, true];
export const TestInt32$test9 = [1, 2, 2, -2, -2, 1];
export const TestInt32$test10 = [1, 0, 2, 0, -1, 1];
export const TestInt32$test11 = [-1, 1];
