import {
  Int_instDecidableEq,
  instDecidableEqISize,
  instDecidableEqInt64,
  instDecidableEqUInt64,
  instDecidableEqUSize,
} from "../runtime/lean_runtime_non_configurable.mjs";
import { $lean_nat_div } from "../runtime/lean_runtime_nat_bigint.mjs";
import {
  $lean_int_ediv,
  $lean_int_neg,
} from "../runtime/lean_runtime_int_bigint.mjs";
import {
  $lean_usize_div,
  $lean_usize_neg,
} from "../runtime/lean_runtime_usize_bigint.mjs";
import {
  $lean_uint64_div,
  $lean_uint64_neg,
} from "../runtime/lean_runtime_uint64_bigint.mjs";
import {
  $lean_int64_div,
  $lean_int64_neg,
  $lean_int64_of_nat,
} from "../runtime/lean_runtime_int64_bigint.mjs";
import {
  $lean_isize_div,
  $lean_isize_neg,
  $lean_isize_of_nat,
} from "../runtime/lean_runtime_isize_bigint.mjs";
export const TestUSize_divNoInline = (v0, v1) => $lean_usize_div(v0, v1);
export const TestUSize_test3m2_shouldBeTrue = (() => {
  const v0 = $lean_usize_neg(2n);
  const v1 = $lean_usize_div(3n, v0);
  const v2 = TestUSize_divNoInline(3n, v0);
  const v3 = instDecidableEqUSize(v1, v2);
  if (v3) {
    return instDecidableEqUSize(v1, 0n);
  } else {
    return v3;
  }
})();
export const TestUSize_test3_2_shouldBeTrue = (() => {
  const v0 = $lean_usize_div(3n, 2n);
  const v1 = TestUSize_divNoInline(3n, 2n);
  const v2 = instDecidableEqUSize(v0, v1);
  if (v2) {
    return instDecidableEqUSize(v0, 1n);
  } else {
    return v2;
  }
})();
export const TestUSize_test1_0_shouldBeTrue = (() => {
  const v0 = $lean_usize_div(1n, 0n);
  const v1 = TestUSize_divNoInline(1n, 0n);
  const v2 = instDecidableEqUSize(v0, v1);
  if (v2) {
    return instDecidableEqUSize(v0, 0n);
  } else {
    return v2;
  }
})();
export const TestUInt64_divNoInline = (v0, v1) => $lean_uint64_div(v0, v1);
export const TestUInt64_test3m2_shouldBeTrue = (() => {
  const v0 = $lean_uint64_neg(2n);
  const v1 = $lean_uint64_div(3n, v0);
  const v2 = TestUInt64_divNoInline(3n, v0);
  const v3 = instDecidableEqUInt64(v1, v2);
  if (v3) {
    return instDecidableEqUInt64(v1, 0n);
  } else {
    return v3;
  }
})();
export const TestUInt64_test3_2_shouldBeTrue = (() => {
  const v0 = TestUInt64_divNoInline(3n, 2n);
  const v1 = instDecidableEqUInt64(1n, v0);
  if (v1) {
    return instDecidableEqUInt64(1n, 1n);
  } else {
    return v1;
  }
})();
export const TestUInt64_test1_0_shouldBeTrue = (() => {
  const v0 = TestUInt64_divNoInline(1n, 0n);
  const v1 = instDecidableEqUInt64(0n, v0);
  if (v1) {
    return instDecidableEqUInt64(0n, 0n);
  } else {
    return v1;
  }
})();
export const TestNat_divNoInline = (v0, v1) => $lean_nat_div(v0, v1);
export const TestNat_test3_2_shouldBeTrue = (() => {
  const v0 = TestNat_divNoInline(3n, 2n);
  const v1 = 1n === v0;
  if (v1) {
    return 1n === 1n;
  } else {
    return v1;
  }
})();
export const TestNat_test1_0_shouldBeTrue = (() => {
  const v0 = TestNat_divNoInline(1n, 0n);
  const v1 = 0n === v0;
  if (v1) {
    return 0n === 0n;
  } else {
    return v1;
  }
})();
export const TestInt64_divNoInline = (v0, v1) => $lean_int64_div(v0, v1);
export const TestInt64_test3m2_shouldBeTrue = (() => {
  const v0 = $lean_int64_of_nat(3n);
  const v1 = $lean_int64_of_nat(2n);
  const v2 = $lean_int64_neg(v1);
  const v3 = $lean_int64_div(v0, v2);
  const v4 = TestInt64_divNoInline(v0, v2);
  const v5 = instDecidableEqInt64(v3, v4);
  if (v5) {
    const v6 = $lean_int64_of_nat(1n);
    const v7 = $lean_int64_neg(v6);
    return instDecidableEqInt64(v3, v7);
  } else {
    return v5;
  }
})();
export const TestInt64_test3_2_shouldBeTrue = (() => {
  const v0 = $lean_int64_of_nat(3n);
  const v1 = $lean_int64_of_nat(2n);
  const v2 = $lean_int64_div(v0, v1);
  const v3 = TestInt64_divNoInline(v0, v1);
  const v4 = instDecidableEqInt64(v2, v3);
  if (v4) {
    const v5 = $lean_int64_of_nat(1n);
    return instDecidableEqInt64(v2, v5);
  } else {
    return v4;
  }
})();
export const TestInt64_test1_0_shouldBeTrue = (() => {
  const v0 = $lean_int64_of_nat(1n);
  const v1 = $lean_int64_of_nat(0n);
  const v2 = $lean_int64_div(v0, v1);
  const v3 = TestInt64_divNoInline(v0, v1);
  const v4 = instDecidableEqInt64(v2, v3);
  if (v4) {
    return instDecidableEqInt64(v2, v1);
  } else {
    return v4;
  }
})();
export const TestInt_divNoInline = (v0, v1) => $lean_int_ediv(v0, v1);
export const TestInt_test3m2_shouldBeTrue = (() => {
  const v0 = $lean_int_neg(2n);
  const v1 = $lean_int_ediv(3n, v0);
  const v2 = TestInt_divNoInline(3n, v0);
  const v3 = Int_instDecidableEq(v1, v2);
  if (v3) {
    const v4 = $lean_int_neg(1n);
    return Int_instDecidableEq(v1, v4);
  } else {
    return v3;
  }
})();
export const TestInt_test3_2_shouldBeTrue = (() => {
  const v0 = $lean_int_ediv(3n, 2n);
  const v1 = TestInt_divNoInline(3n, 2n);
  const v2 = Int_instDecidableEq(v0, v1);
  if (v2) {
    return Int_instDecidableEq(v0, 1n);
  } else {
    return v2;
  }
})();
export const TestInt_test1_0_shouldBeTrue = (() => {
  const v0 = $lean_int_ediv(1n, 0n);
  const v1 = TestInt_divNoInline(1n, 0n);
  const v2 = Int_instDecidableEq(v0, v1);
  if (v2) {
    return Int_instDecidableEq(v0, 0n);
  } else {
    return v2;
  }
})();
export const TestISize_divNoInline = (v0, v1) => $lean_isize_div(v0, v1);
export const TestISize_test3m2_shouldBeTrue = (() => {
  const v0 = $lean_isize_of_nat(3n);
  const v1 = $lean_isize_of_nat(2n);
  const v2 = $lean_isize_neg(v1);
  const v3 = $lean_isize_div(v0, v2);
  const v4 = TestISize_divNoInline(v0, v2);
  const v5 = instDecidableEqISize(v3, v4);
  if (v5) {
    const v6 = $lean_isize_of_nat(1n);
    const v7 = $lean_isize_neg(v6);
    return instDecidableEqISize(v3, v7);
  } else {
    return v5;
  }
})();
export const TestISize_test3_2_shouldBeTrue = (() => {
  const v0 = $lean_isize_of_nat(3n);
  const v1 = $lean_isize_of_nat(2n);
  const v2 = $lean_isize_div(v0, v1);
  const v3 = TestISize_divNoInline(v0, v1);
  const v4 = instDecidableEqISize(v2, v3);
  if (v4) {
    const v5 = $lean_isize_of_nat(1n);
    return instDecidableEqISize(v2, v5);
  } else {
    return v4;
  }
})();
export const TestISize_test1_0_shouldBeTrue = (() => {
  const v0 = $lean_isize_of_nat(1n);
  const v1 = $lean_isize_of_nat(0n);
  const v2 = $lean_isize_div(v0, v1);
  const v3 = TestISize_divNoInline(v0, v1);
  const v4 = instDecidableEqISize(v2, v3);
  if (v4) {
    return instDecidableEqISize(v2, v1);
  } else {
    return v4;
  }
})();
export const test = (v0, v1, v2, v3, v4, v5) => {
  const v6 = v1(v3, v4);
  const v7 = v2(v3, v4);
  const v8 = v0(v6, v7);
  if (v8) {
    return v0(v6, v5);
  } else {
    return v8;
  }
};
