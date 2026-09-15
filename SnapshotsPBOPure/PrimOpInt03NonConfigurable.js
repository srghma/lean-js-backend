// UInt8, UInt16, UInt32, Int8, Int16, Int32 are always representable exactly as a
// JS Number (max magnitude 2^32 < Number.MAX_SAFE_INTEGER = 2^53 - 1), so there is
// only one output mode for these — no BigInt needed, ever.
//
// In `PrimOpInt03`, static constants in `test1`–`test3` are inlined and computed
// with wrapping, and `test4` preserves the non-constant expression.

// ---------------- TestUInt8 ----------------

export const TestUInt8$test1 = 144; // (200 + 200) & 0xff
export const TestUInt8$test2 = 106; // (50 - 200) & 0xff
export const TestUInt8$test3 = 144; // (20 * 20) & 0xff
export const TestUInt8$test4 = (a) => (a + 144) & 0xff;

// ---------------- TestUInt16 ----------------

export const TestUInt16$test1 = 34464; // (50000 + 50000) & 0xffff
export const TestUInt16$test2 = 25536; // (10000 - 50000) & 0xffff
export const TestUInt16$test3 = 16960; // (1000 * 1000) & 0xffff
export const TestUInt16$test4 = (a) => (a + 34464) & 0xffff;

// ---------------- TestUInt32 ----------------

export const TestUInt32$test1 = 1705032704; // (3000000000 + 3000000000) >>> 0
export const TestUInt32$test2 = 2294967296; // (1000000000 - 3000000000) >>> 0
export const TestUInt32$test3 = 2690588672; // Math.imul(2000000000, 2000000000) >>> 0
export const TestUInt32$test4 = /* #__PURE__ */ (a) => (a + 1705032704) >>> 0;

// ---------------- TestInt8 ----------------

export const TestInt8$test1 = -56;  // ((100 + 100) << 24) >> 24
export const TestInt8$test2 = 56;   // ((-100 - 100) << 24) >> 24
export const TestInt8$test3 = -112; // ((20 * 20) << 24) >> 24
export const TestInt8$test4 = /* #__PURE__ */ (a) => ((a - 56) << 24) >> 24;

// ---------------- TestInt16 ----------------

export const TestInt16$test1 = -25536; // ((20000 + 20000) << 16) >> 16
export const TestInt16$test2 = 25536;  // ((-20000 - 20000) << 16) >> 16
export const TestInt16$test3 = 16960;  // ((1000 * 1000) << 16) >> 16
export const TestInt16$test4 = /* #__PURE__ */ (a) => ((a - 25536) << 16) >> 16;

// ---------------- TestInt32 ----------------

export const TestInt32$test1 = -294967296;  // (2000000000 + 2000000000) | 0
export const TestInt32$test2 = 294967296;   // (-2000000000 - 2000000000) | 0
export const TestInt32$test3 = -1604378624; // Math.imul(2000000000, 2000000000) | 0
export const TestInt32$test4 = /* #__PURE__ */ (a) => (a - 294967296) | 0;
