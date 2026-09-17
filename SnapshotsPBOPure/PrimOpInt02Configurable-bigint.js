import {
  $lean_int64_add,
  $lean_int64_dec_le,
  $lean_int64_dec_lt,
  $lean_int64_div,
  $lean_int64_mul,
  $lean_int64_neg,
  $lean_int64_of_nat,
  $lean_int64_sub,
  $lean_int_ediv,
  $lean_int_neg,
  $lean_isize_add,
  $lean_isize_dec_le,
  $lean_isize_dec_lt,
  $lean_isize_div,
  $lean_isize_mul,
  $lean_isize_neg,
  $lean_isize_of_nat,
  $lean_isize_sub,
  $lean_uint64_add,
  $lean_uint64_div,
  $lean_uint64_mul,
  $lean_uint64_neg,
  $lean_uint64_shift_left,
  $lean_uint64_shift_right,
  $lean_uint64_sub,
  $lean_usize_add,
  $lean_usize_div,
  $lean_usize_mul,
  $lean_usize_neg,
  $lean_usize_sub,
  Int_instDecidableEq,
  instDecidableEqISize,
  instDecidableEqInt64,
  instDecidableEqUInt64,
  instDecidableEqUSize,
} from "../runtime/lean_runtime_bigint.mjs";
export const TestUSize_test9 = (() => {
  const v0 = $lean_usize_mul(1n, 1n);
  const v1 = $lean_usize_mul(1n, 2n);
  const v2 = $lean_usize_mul(2n, 1n);
  const v3 = $lean_usize_neg(2n);
  const v4 = $lean_usize_mul(1n, v3);
  const v5 = $lean_usize_neg(1n);
  const v6 = $lean_usize_mul(v5, 2n);
  const v7 = $lean_usize_mul(v5, v5);
  const v8 = [];
  const v9 = [...v8, v0];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v4];
  const v13 = [...v12, v6];
  return [...v13, v7];
})();
export const TestUSize_test8 = (() => {
  const v0 = (v0, v1) => {
    const v2 = v1 <= v0;
    return v2;
  };
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = $lean_usize_neg(2n);
  const v5 = v0(1n, v4);
  const v6 = $lean_usize_neg(1n);
  const v7 = v0(v6, 2n);
  const v8 = v0(v6, v6);
  const v9 = [];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v3];
  const v13 = [...v12, v5];
  const v14 = [...v13, v7];
  return [...v14, v8];
})();
export const TestUSize_test7 = (() => {
  const v0 = (v0, v1) => {
    const v2 = v0 <= v1;
    return v2;
  };
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = $lean_usize_neg(2n);
  const v5 = v0(1n, v4);
  const v6 = $lean_usize_neg(1n);
  const v7 = v0(v6, 2n);
  const v8 = v0(v6, v6);
  const v9 = [];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v3];
  const v13 = [...v12, v5];
  const v14 = [...v13, v7];
  return [...v14, v8];
})();
export const TestUSize_test6 = (() => {
  const v0 = (v0, v1) => {
    const v2 = v1 < v0;
    return v2;
  };
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = $lean_usize_neg(2n);
  const v5 = v0(1n, v4);
  const v6 = $lean_usize_neg(1n);
  const v7 = v0(v6, 2n);
  const v8 = v0(v6, v6);
  const v9 = [];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v3];
  const v13 = [...v12, v5];
  const v14 = [...v13, v7];
  return [...v14, v8];
})();
export const TestUSize_test5 = (() => {
  const v0 = (v0, v1) => {
    const v2 = v0 < v1;
    return v2;
  };
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = $lean_usize_neg(2n);
  const v5 = v0(1n, v4);
  const v6 = $lean_usize_neg(1n);
  const v7 = v0(v6, 2n);
  const v8 = v0(v6, v6);
  const v9 = [];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v3];
  const v13 = [...v12, v5];
  const v14 = [...v13, v7];
  return [...v14, v8];
})();
export const TestUSize_test4 = (() => {
  const v0 = (v0, v1) => {
    const v2 = instDecidableEqUSize(v0, v1);
    if (v2) {
      return false;
    } else {
      return true;
    }
  };
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = $lean_usize_neg(2n);
  const v5 = v0(1n, v4);
  const v6 = $lean_usize_neg(1n);
  const v7 = v0(v6, 2n);
  const v8 = v0(v6, v6);
  const v9 = [];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v3];
  const v13 = [...v12, v5];
  const v14 = [...v13, v7];
  return [...v14, v8];
})();
export const TestUSize_test3 = (() => {
  const v0 = (v0, v1) => {
    const v2 = instDecidableEqUSize(v0, v1);
    return v2;
  };
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = $lean_usize_neg(2n);
  const v5 = v0(1n, v4);
  const v6 = $lean_usize_neg(1n);
  const v7 = v0(v6, 2n);
  const v8 = v0(v6, v6);
  const v9 = [];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v3];
  const v13 = [...v12, v5];
  const v14 = [...v13, v7];
  return [...v14, v8];
})();
export const TestUSize_test2 = (() => {
  const v0 = $lean_usize_sub(1n, 1n);
  const v1 = $lean_usize_sub(1n, 2n);
  const v2 = $lean_usize_sub(2n, 1n);
  const v3 = $lean_usize_neg(2n);
  const v4 = $lean_usize_sub(1n, v3);
  const v5 = $lean_usize_neg(1n);
  const v6 = $lean_usize_sub(v5, 2n);
  const v7 = $lean_usize_sub(v5, v5);
  const v8 = [];
  const v9 = [...v8, v0];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v4];
  const v13 = [...v12, v6];
  return [...v13, v7];
})();
export const TestUSize_test11 = (() => {
  const v0 = $lean_usize_neg(1n);
  const v1 = $lean_usize_neg(v0);
  const v2 = [];
  const v3 = [...v2, v0];
  return [...v3, v1];
})();
export const TestUSize_test10 = (() => {
  const v0 = $lean_usize_div(1n, 1n);
  const v1 = $lean_usize_div(1n, 2n);
  const v2 = $lean_usize_div(2n, 1n);
  const v3 = $lean_usize_neg(2n);
  const v4 = $lean_usize_div(1n, v3);
  const v5 = $lean_usize_neg(1n);
  const v6 = $lean_usize_div(v5, 2n);
  const v7 = $lean_usize_div(v5, v5);
  const v8 = [];
  const v9 = [...v8, v0];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v4];
  const v13 = [...v12, v6];
  return [...v13, v7];
})();
export const TestUSize_test1 = (() => {
  const v0 = $lean_usize_add(1n, 1n);
  const v1 = $lean_usize_add(1n, 2n);
  const v2 = $lean_usize_add(2n, 1n);
  const v3 = $lean_usize_neg(2n);
  const v4 = $lean_usize_add(1n, v3);
  const v5 = $lean_usize_neg(1n);
  const v6 = $lean_usize_add(v5, 2n);
  const v7 = $lean_usize_add(v5, v5);
  const v8 = [];
  const v9 = [...v8, v0];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v4];
  const v13 = [...v12, v6];
  return [...v13, v7];
})();
export const TestUSize_intValues = (v0) => {
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = $lean_usize_neg(2n);
  const v5 = v0(1n, v4);
  const v6 = $lean_usize_neg(1n);
  const v7 = v0(v6, 2n);
  const v8 = v0(v6, v6);
  const v9 = [];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v3];
  const v13 = [...v12, v5];
  const v14 = [...v13, v7];
  return [...v14, v8];
};
export const TestUInt64_test9 = (() => {
  const v0 = $lean_uint64_neg(2n);
  const v1 = $lean_uint64_neg(1n);
  const v2 = $lean_uint64_shift_left(v1, 1n);
  const v3 = $lean_uint64_mul(v1, v1);
  const v4 = [];
  const v5 = [...v4, 1n];
  const v6 = [...v5, 2n];
  const v7 = [...v6, 2n];
  const v8 = [...v7, v0];
  const v9 = [...v8, v2];
  return [...v9, v3];
})();
export const TestUInt64_test8 = (() => {
  const v0 = (v0, v1) => {
    const v2 = v1 <= v0;
    return v2;
  };
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = $lean_uint64_neg(2n);
  const v5 = v0(1n, v4);
  const v6 = $lean_uint64_neg(1n);
  const v7 = v0(v6, 2n);
  const v8 = v0(v6, v6);
  const v9 = [];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v3];
  const v13 = [...v12, v5];
  const v14 = [...v13, v7];
  return [...v14, v8];
})();
export const TestUInt64_test7 = (() => {
  const v0 = (v0, v1) => {
    const v2 = v0 <= v1;
    return v2;
  };
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = $lean_uint64_neg(2n);
  const v5 = v0(1n, v4);
  const v6 = $lean_uint64_neg(1n);
  const v7 = v0(v6, 2n);
  const v8 = v0(v6, v6);
  const v9 = [];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v3];
  const v13 = [...v12, v5];
  const v14 = [...v13, v7];
  return [...v14, v8];
})();
export const TestUInt64_test6 = (() => {
  const v0 = (v0, v1) => {
    const v2 = v1 < v0;
    return v2;
  };
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = $lean_uint64_neg(2n);
  const v5 = v0(1n, v4);
  const v6 = $lean_uint64_neg(1n);
  const v7 = v0(v6, 2n);
  const v8 = v0(v6, v6);
  const v9 = [];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v3];
  const v13 = [...v12, v5];
  const v14 = [...v13, v7];
  return [...v14, v8];
})();
export const TestUInt64_test5 = (() => {
  const v0 = (v0, v1) => {
    const v2 = v0 < v1;
    return v2;
  };
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = $lean_uint64_neg(2n);
  const v5 = v0(1n, v4);
  const v6 = $lean_uint64_neg(1n);
  const v7 = v0(v6, 2n);
  const v8 = v0(v6, v6);
  const v9 = [];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v3];
  const v13 = [...v12, v5];
  const v14 = [...v13, v7];
  return [...v14, v8];
})();
export const TestUInt64_test4 = (() => {
  const v0 = (v0, v1) => {
    const v2 = instDecidableEqUInt64(v0, v1);
    if (v2) {
      return false;
    } else {
      return true;
    }
  };
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = $lean_uint64_neg(2n);
  const v5 = v0(1n, v4);
  const v6 = $lean_uint64_neg(1n);
  const v7 = v0(v6, 2n);
  const v8 = v0(v6, v6);
  const v9 = [];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v3];
  const v13 = [...v12, v5];
  const v14 = [...v13, v7];
  return [...v14, v8];
})();
export const TestUInt64_test3 = (() => {
  const v0 = (v0, v1) => {
    const v2 = instDecidableEqUInt64(v0, v1);
    return v2;
  };
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = $lean_uint64_neg(2n);
  const v5 = v0(1n, v4);
  const v6 = $lean_uint64_neg(1n);
  const v7 = v0(v6, 2n);
  const v8 = v0(v6, v6);
  const v9 = [];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v3];
  const v13 = [...v12, v5];
  const v14 = [...v13, v7];
  return [...v14, v8];
})();
export const TestUInt64_test2 = (() => {
  const v0 = $lean_uint64_neg(2n);
  const v1 = $lean_uint64_sub(1n, v0);
  const v2 = $lean_uint64_neg(1n);
  const v3 = $lean_uint64_sub(v2, 2n);
  const v4 = $lean_uint64_sub(v2, v2);
  const v5 = [];
  const v6 = [...v5, 0n];
  const v7 = [...v6, 18446744073709551615n];
  const v8 = [...v7, 1n];
  const v9 = [...v8, v1];
  const v10 = [...v9, v3];
  return [...v10, v4];
})();
export const TestUInt64_test11 = (() => {
  const v0 = $lean_uint64_neg(1n);
  const v1 = $lean_uint64_neg(v0);
  const v2 = [];
  const v3 = [...v2, v0];
  return [...v3, v1];
})();
export const TestUInt64_test10 = (() => {
  const v0 = $lean_uint64_neg(2n);
  const v1 = $lean_uint64_div(1n, v0);
  const v2 = $lean_uint64_neg(1n);
  const v3 = $lean_uint64_shift_right(v2, 1n);
  const v4 = $lean_uint64_div(v2, v2);
  const v5 = [];
  const v6 = [...v5, 1n];
  const v7 = [...v6, 0n];
  const v8 = [...v7, 2n];
  const v9 = [...v8, v1];
  const v10 = [...v9, v3];
  return [...v10, v4];
})();
export const TestUInt64_test1 = (() => {
  const v0 = $lean_uint64_neg(2n);
  const v1 = $lean_uint64_add(1n, v0);
  const v2 = $lean_uint64_neg(1n);
  const v3 = $lean_uint64_add(v2, 2n);
  const v4 = $lean_uint64_add(v2, v2);
  const v5 = [];
  const v6 = [...v5, 2n];
  const v7 = [...v6, 3n];
  const v8 = [...v7, 3n];
  const v9 = [...v8, v1];
  const v10 = [...v9, v3];
  return [...v10, v4];
})();
export const TestUInt64_intValues = (v0) => {
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = $lean_uint64_neg(2n);
  const v5 = v0(1n, v4);
  const v6 = $lean_uint64_neg(1n);
  const v7 = v0(v6, 2n);
  const v8 = v0(v6, v6);
  const v9 = [];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v3];
  const v13 = [...v12, v5];
  const v14 = [...v13, v7];
  return [...v14, v8];
};
export const TestNat_test9 = (() => {
  const v0 = [];
  const v1 = [...v0, 1n];
  const v2 = [...v1, 2n];
  const v3 = [...v2, 2n];
  const v4 = [...v3, 0n];
  const v5 = [...v4, 0n];
  return [...v5, 0n];
})();
export const TestNat_test8 = (() => {
  const v0 = (v0, v1) => {
    const v2 = v1 <= v0;
    return v2;
  };
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = v0(1n, 0n);
  const v5 = v0(0n, 2n);
  const v6 = v0(0n, 0n);
  const v7 = [];
  const v8 = [...v7, v1];
  const v9 = [...v8, v2];
  const v10 = [...v9, v3];
  const v11 = [...v10, v4];
  const v12 = [...v11, v5];
  return [...v12, v6];
})();
export const TestNat_test7 = (() => {
  const v0 = (v0, v1) => {
    const v2 = v0 <= v1;
    return v2;
  };
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = v0(1n, 0n);
  const v5 = v0(0n, 2n);
  const v6 = v0(0n, 0n);
  const v7 = [];
  const v8 = [...v7, v1];
  const v9 = [...v8, v2];
  const v10 = [...v9, v3];
  const v11 = [...v10, v4];
  const v12 = [...v11, v5];
  return [...v12, v6];
})();
export const TestNat_test6 = (() => {
  const v0 = (v0, v1) => {
    const v2 = v1 < v0;
    return v2;
  };
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = v0(1n, 0n);
  const v5 = v0(0n, 2n);
  const v6 = v0(0n, 0n);
  const v7 = [];
  const v8 = [...v7, v1];
  const v9 = [...v8, v2];
  const v10 = [...v9, v3];
  const v11 = [...v10, v4];
  const v12 = [...v11, v5];
  return [...v12, v6];
})();
export const TestNat_test5 = (() => {
  const v0 = (v0, v1) => {
    const v2 = v0 < v1;
    return v2;
  };
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = v0(1n, 0n);
  const v5 = v0(0n, 2n);
  const v6 = v0(0n, 0n);
  const v7 = [];
  const v8 = [...v7, v1];
  const v9 = [...v8, v2];
  const v10 = [...v9, v3];
  const v11 = [...v10, v4];
  const v12 = [...v11, v5];
  return [...v12, v6];
})();
export const TestNat_test4 = (() => {
  const v0 = (v0, v1) => {
    const v2 = v0 === v1;
    if (v2) {
      return false;
    } else {
      return true;
    }
  };
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = v0(1n, 0n);
  const v5 = v0(0n, 2n);
  const v6 = v0(0n, 0n);
  const v7 = [];
  const v8 = [...v7, v1];
  const v9 = [...v8, v2];
  const v10 = [...v9, v3];
  const v11 = [...v10, v4];
  const v12 = [...v11, v5];
  return [...v12, v6];
})();
export const TestNat_test3 = (() => {
  const v0 = (v0, v1) => {
    const v2 = v0 === v1;
    return v2;
  };
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = v0(1n, 0n);
  const v5 = v0(0n, 2n);
  const v6 = v0(0n, 0n);
  const v7 = [];
  const v8 = [...v7, v1];
  const v9 = [...v8, v2];
  const v10 = [...v9, v3];
  const v11 = [...v10, v4];
  const v12 = [...v11, v5];
  return [...v12, v6];
})();
export const TestNat_test2 = (() => {
  const v0 = [];
  const v1 = [...v0, 0n];
  const v2 = [...v1, 0n];
  const v3 = [...v2, 1n];
  const v4 = [...v3, 1n];
  const v5 = [...v4, 0n];
  return [...v5, 0n];
})();
export const TestNat_test10 = (() => {
  const v0 = [];
  const v1 = [...v0, 1n];
  const v2 = [...v1, 0n];
  const v3 = [...v2, 2n];
  const v4 = [...v3, 0n];
  const v5 = [...v4, 0n];
  return [...v5, 0n];
})();
export const TestNat_test1 = (() => {
  const v0 = [];
  const v1 = [...v0, 2n];
  const v2 = [...v1, 3n];
  const v3 = [...v2, 3n];
  const v4 = [...v3, 1n];
  const v5 = [...v4, 2n];
  return [...v5, 0n];
})();
export const TestNat_intValues = (v0) => {
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = v0(1n, 0n);
  const v5 = v0(0n, 2n);
  const v6 = v0(0n, 0n);
  const v7 = [];
  const v8 = [...v7, v1];
  const v9 = [...v8, v2];
  const v10 = [...v9, v3];
  const v11 = [...v10, v4];
  const v12 = [...v11, v5];
  return [...v12, v6];
};
export const TestInt64_test9 = (() => {
  const v0 = $lean_int64_of_nat(1n);
  const v1 = $lean_int64_mul(v0, v0);
  const v2 = $lean_int64_of_nat(2n);
  const v3 = $lean_int64_mul(v0, v2);
  const v4 = $lean_int64_mul(v2, v0);
  const v5 = $lean_int64_neg(v2);
  const v6 = $lean_int64_mul(v0, v5);
  const v7 = $lean_int64_neg(v0);
  const v8 = $lean_int64_mul(v7, v2);
  const v9 = $lean_int64_mul(v7, v7);
  const v10 = [];
  const v11 = [...v10, v1];
  const v12 = [...v11, v3];
  const v13 = [...v12, v4];
  const v14 = [...v13, v6];
  const v15 = [...v14, v8];
  return [...v15, v9];
})();
export const TestInt64_test8 = (() => {
  const v0 = (v0, v1) => {
    const v2 = $lean_int64_dec_le(v1, v0);
    return v2;
  };
  const v1 = $lean_int64_of_nat(1n);
  const v2 = v0(v1, v1);
  const v3 = $lean_int64_of_nat(2n);
  const v4 = v0(v1, v3);
  const v5 = v0(v3, v1);
  const v6 = $lean_int64_neg(v3);
  const v7 = v0(v1, v6);
  const v8 = $lean_int64_neg(v1);
  const v9 = v0(v8, v3);
  const v10 = v0(v8, v8);
  const v11 = [];
  const v12 = [...v11, v2];
  const v13 = [...v12, v4];
  const v14 = [...v13, v5];
  const v15 = [...v14, v7];
  const v16 = [...v15, v9];
  return [...v16, v10];
})();
export const TestInt64_test7 = (() => {
  const v0 = (v0, v1) => {
    const v2 = $lean_int64_dec_le(v0, v1);
    return v2;
  };
  const v1 = $lean_int64_of_nat(1n);
  const v2 = v0(v1, v1);
  const v3 = $lean_int64_of_nat(2n);
  const v4 = v0(v1, v3);
  const v5 = v0(v3, v1);
  const v6 = $lean_int64_neg(v3);
  const v7 = v0(v1, v6);
  const v8 = $lean_int64_neg(v1);
  const v9 = v0(v8, v3);
  const v10 = v0(v8, v8);
  const v11 = [];
  const v12 = [...v11, v2];
  const v13 = [...v12, v4];
  const v14 = [...v13, v5];
  const v15 = [...v14, v7];
  const v16 = [...v15, v9];
  return [...v16, v10];
})();
export const TestInt64_test6 = (() => {
  const v0 = (v0, v1) => {
    const v2 = $lean_int64_dec_lt(v1, v0);
    return v2;
  };
  const v1 = $lean_int64_of_nat(1n);
  const v2 = v0(v1, v1);
  const v3 = $lean_int64_of_nat(2n);
  const v4 = v0(v1, v3);
  const v5 = v0(v3, v1);
  const v6 = $lean_int64_neg(v3);
  const v7 = v0(v1, v6);
  const v8 = $lean_int64_neg(v1);
  const v9 = v0(v8, v3);
  const v10 = v0(v8, v8);
  const v11 = [];
  const v12 = [...v11, v2];
  const v13 = [...v12, v4];
  const v14 = [...v13, v5];
  const v15 = [...v14, v7];
  const v16 = [...v15, v9];
  return [...v16, v10];
})();
export const TestInt64_test5 = (() => {
  const v0 = (v0, v1) => {
    const v2 = $lean_int64_dec_lt(v0, v1);
    return v2;
  };
  const v1 = $lean_int64_of_nat(1n);
  const v2 = v0(v1, v1);
  const v3 = $lean_int64_of_nat(2n);
  const v4 = v0(v1, v3);
  const v5 = v0(v3, v1);
  const v6 = $lean_int64_neg(v3);
  const v7 = v0(v1, v6);
  const v8 = $lean_int64_neg(v1);
  const v9 = v0(v8, v3);
  const v10 = v0(v8, v8);
  const v11 = [];
  const v12 = [...v11, v2];
  const v13 = [...v12, v4];
  const v14 = [...v13, v5];
  const v15 = [...v14, v7];
  const v16 = [...v15, v9];
  return [...v16, v10];
})();
export const TestInt64_test4 = (() => {
  const v0 = (v0, v1) => {
    const v2 = instDecidableEqInt64(v0, v1);
    if (v2) {
      return false;
    } else {
      return true;
    }
  };
  const v1 = $lean_int64_of_nat(1n);
  const v2 = v0(v1, v1);
  const v3 = $lean_int64_of_nat(2n);
  const v4 = v0(v1, v3);
  const v5 = v0(v3, v1);
  const v6 = $lean_int64_neg(v3);
  const v7 = v0(v1, v6);
  const v8 = $lean_int64_neg(v1);
  const v9 = v0(v8, v3);
  const v10 = v0(v8, v8);
  const v11 = [];
  const v12 = [...v11, v2];
  const v13 = [...v12, v4];
  const v14 = [...v13, v5];
  const v15 = [...v14, v7];
  const v16 = [...v15, v9];
  return [...v16, v10];
})();
export const TestInt64_test3 = (() => {
  const v0 = (v0, v1) => {
    const v2 = instDecidableEqInt64(v0, v1);
    return v2;
  };
  const v1 = $lean_int64_of_nat(1n);
  const v2 = v0(v1, v1);
  const v3 = $lean_int64_of_nat(2n);
  const v4 = v0(v1, v3);
  const v5 = v0(v3, v1);
  const v6 = $lean_int64_neg(v3);
  const v7 = v0(v1, v6);
  const v8 = $lean_int64_neg(v1);
  const v9 = v0(v8, v3);
  const v10 = v0(v8, v8);
  const v11 = [];
  const v12 = [...v11, v2];
  const v13 = [...v12, v4];
  const v14 = [...v13, v5];
  const v15 = [...v14, v7];
  const v16 = [...v15, v9];
  return [...v16, v10];
})();
export const TestInt64_test2 = (() => {
  const v0 = $lean_int64_of_nat(1n);
  const v1 = $lean_int64_sub(v0, v0);
  const v2 = $lean_int64_of_nat(2n);
  const v3 = $lean_int64_sub(v0, v2);
  const v4 = $lean_int64_sub(v2, v0);
  const v5 = $lean_int64_neg(v2);
  const v6 = $lean_int64_sub(v0, v5);
  const v7 = $lean_int64_neg(v0);
  const v8 = $lean_int64_sub(v7, v2);
  const v9 = $lean_int64_sub(v7, v7);
  const v10 = [];
  const v11 = [...v10, v1];
  const v12 = [...v11, v3];
  const v13 = [...v12, v4];
  const v14 = [...v13, v6];
  const v15 = [...v14, v8];
  return [...v15, v9];
})();
export const TestInt64_test11 = (() => {
  const v0 = $lean_int64_of_nat(1n);
  const v1 = $lean_int64_neg(v0);
  const v2 = $lean_int64_neg(v1);
  const v3 = [];
  const v4 = [...v3, v1];
  return [...v4, v2];
})();
export const TestInt64_test10 = (() => {
  const v0 = $lean_int64_of_nat(1n);
  const v1 = $lean_int64_div(v0, v0);
  const v2 = $lean_int64_of_nat(2n);
  const v3 = $lean_int64_div(v0, v2);
  const v4 = $lean_int64_div(v2, v0);
  const v5 = $lean_int64_neg(v2);
  const v6 = $lean_int64_div(v0, v5);
  const v7 = $lean_int64_neg(v0);
  const v8 = $lean_int64_div(v7, v2);
  const v9 = $lean_int64_div(v7, v7);
  const v10 = [];
  const v11 = [...v10, v1];
  const v12 = [...v11, v3];
  const v13 = [...v12, v4];
  const v14 = [...v13, v6];
  const v15 = [...v14, v8];
  return [...v15, v9];
})();
export const TestInt64_test1 = (() => {
  const v0 = $lean_int64_of_nat(1n);
  const v1 = $lean_int64_add(v0, v0);
  const v2 = $lean_int64_of_nat(2n);
  const v3 = $lean_int64_add(v0, v2);
  const v4 = $lean_int64_add(v2, v0);
  const v5 = $lean_int64_neg(v2);
  const v6 = $lean_int64_add(v0, v5);
  const v7 = $lean_int64_neg(v0);
  const v8 = $lean_int64_add(v7, v2);
  const v9 = $lean_int64_add(v7, v7);
  const v10 = [];
  const v11 = [...v10, v1];
  const v12 = [...v11, v3];
  const v13 = [...v12, v4];
  const v14 = [...v13, v6];
  const v15 = [...v14, v8];
  return [...v15, v9];
})();
export const TestInt64_intValues = (v0) => {
  const v1 = $lean_int64_of_nat(1n);
  const v2 = v0(v1, v1);
  const v3 = $lean_int64_of_nat(2n);
  const v4 = v0(v1, v3);
  const v5 = v0(v3, v1);
  const v6 = $lean_int64_neg(v3);
  const v7 = v0(v1, v6);
  const v8 = $lean_int64_neg(v1);
  const v9 = v0(v8, v3);
  const v10 = v0(v8, v8);
  const v11 = [];
  const v12 = [...v11, v2];
  const v13 = [...v12, v4];
  const v14 = [...v13, v5];
  const v15 = [...v14, v7];
  const v16 = [...v15, v9];
  return [...v16, v10];
};
export const TestInt_test9 = (() => {
  const v0 = 1n * 1n;
  const v1 = 1n * 2n;
  const v2 = 2n * 1n;
  const v3 = $lean_int_neg(2n);
  const v4 = 1n * v3;
  const v5 = $lean_int_neg(1n);
  const v6 = v5 * 2n;
  const v7 = v5 * v5;
  const v8 = [];
  const v9 = [...v8, v0];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v4];
  const v13 = [...v12, v6];
  return [...v13, v7];
})();
export const TestInt_test8 = (() => {
  const v0 = (v0, v1) => {
    const v2 = v1 <= v0;
    return v2;
  };
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = $lean_int_neg(2n);
  const v5 = v0(1n, v4);
  const v6 = $lean_int_neg(1n);
  const v7 = v0(v6, 2n);
  const v8 = v0(v6, v6);
  const v9 = [];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v3];
  const v13 = [...v12, v5];
  const v14 = [...v13, v7];
  return [...v14, v8];
})();
export const TestInt_test7 = (() => {
  const v0 = (v0, v1) => {
    const v2 = v0 <= v1;
    return v2;
  };
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = $lean_int_neg(2n);
  const v5 = v0(1n, v4);
  const v6 = $lean_int_neg(1n);
  const v7 = v0(v6, 2n);
  const v8 = v0(v6, v6);
  const v9 = [];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v3];
  const v13 = [...v12, v5];
  const v14 = [...v13, v7];
  return [...v14, v8];
})();
export const TestInt_test6 = (() => {
  const v0 = (v0, v1) => {
    const v2 = v1 < v0;
    return v2;
  };
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = $lean_int_neg(2n);
  const v5 = v0(1n, v4);
  const v6 = $lean_int_neg(1n);
  const v7 = v0(v6, 2n);
  const v8 = v0(v6, v6);
  const v9 = [];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v3];
  const v13 = [...v12, v5];
  const v14 = [...v13, v7];
  return [...v14, v8];
})();
export const TestInt_test5 = (() => {
  const v0 = (v0, v1) => {
    const v2 = v0 < v1;
    return v2;
  };
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = $lean_int_neg(2n);
  const v5 = v0(1n, v4);
  const v6 = $lean_int_neg(1n);
  const v7 = v0(v6, 2n);
  const v8 = v0(v6, v6);
  const v9 = [];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v3];
  const v13 = [...v12, v5];
  const v14 = [...v13, v7];
  return [...v14, v8];
})();
export const TestInt_test4 = (() => {
  const v0 = (v0, v1) => {
    const v2 = Int_instDecidableEq(v0, v1);
    if (v2) {
      return false;
    } else {
      return true;
    }
  };
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = $lean_int_neg(2n);
  const v5 = v0(1n, v4);
  const v6 = $lean_int_neg(1n);
  const v7 = v0(v6, 2n);
  const v8 = v0(v6, v6);
  const v9 = [];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v3];
  const v13 = [...v12, v5];
  const v14 = [...v13, v7];
  return [...v14, v8];
})();
export const TestInt_test3 = (() => {
  const v0 = (v0, v1) => {
    const v2 = Int_instDecidableEq(v0, v1);
    return v2;
  };
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = $lean_int_neg(2n);
  const v5 = v0(1n, v4);
  const v6 = $lean_int_neg(1n);
  const v7 = v0(v6, 2n);
  const v8 = v0(v6, v6);
  const v9 = [];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v3];
  const v13 = [...v12, v5];
  const v14 = [...v13, v7];
  return [...v14, v8];
})();
export const TestInt_test2 = (() => {
  const v0 = 1n - 1n;
  const v1 = 1n - 2n;
  const v2 = 2n - 1n;
  const v3 = $lean_int_neg(2n);
  const v4 = 1n - v3;
  const v5 = $lean_int_neg(1n);
  const v6 = v5 - 2n;
  const v7 = v5 - v5;
  const v8 = [];
  const v9 = [...v8, v0];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v4];
  const v13 = [...v12, v6];
  return [...v13, v7];
})();
export const TestInt_test11 = (() => {
  const v0 = $lean_int_neg(1n);
  const v1 = $lean_int_neg(v0);
  const v2 = [];
  const v3 = [...v2, v0];
  return [...v3, v1];
})();
export const TestInt_test10 = (() => {
  const v0 = $lean_int_ediv(1n, 1n);
  const v1 = $lean_int_ediv(1n, 2n);
  const v2 = $lean_int_ediv(2n, 1n);
  const v3 = $lean_int_neg(2n);
  const v4 = $lean_int_ediv(1n, v3);
  const v5 = $lean_int_neg(1n);
  const v6 = $lean_int_ediv(v5, 2n);
  const v7 = $lean_int_ediv(v5, v5);
  const v8 = [];
  const v9 = [...v8, v0];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v4];
  const v13 = [...v12, v6];
  return [...v13, v7];
})();
export const TestInt_test1 = (() => {
  const v0 = 1n + 1n;
  const v1 = 1n + 2n;
  const v2 = 2n + 1n;
  const v3 = $lean_int_neg(2n);
  const v4 = 1n + v3;
  const v5 = $lean_int_neg(1n);
  const v6 = v5 + 2n;
  const v7 = v5 + v5;
  const v8 = [];
  const v9 = [...v8, v0];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v4];
  const v13 = [...v12, v6];
  return [...v13, v7];
})();
export const TestInt_intValues = (v0) => {
  const v1 = v0(1n, 1n);
  const v2 = v0(1n, 2n);
  const v3 = v0(2n, 1n);
  const v4 = $lean_int_neg(2n);
  const v5 = v0(1n, v4);
  const v6 = $lean_int_neg(1n);
  const v7 = v0(v6, 2n);
  const v8 = v0(v6, v6);
  const v9 = [];
  const v10 = [...v9, v1];
  const v11 = [...v10, v2];
  const v12 = [...v11, v3];
  const v13 = [...v12, v5];
  const v14 = [...v13, v7];
  return [...v14, v8];
};
export const TestISize_test9 = (() => {
  const v0 = $lean_isize_of_nat(1n);
  const v1 = $lean_isize_mul(v0, v0);
  const v2 = $lean_isize_of_nat(2n);
  const v3 = $lean_isize_mul(v0, v2);
  const v4 = $lean_isize_mul(v2, v0);
  const v5 = $lean_isize_neg(v2);
  const v6 = $lean_isize_mul(v0, v5);
  const v7 = $lean_isize_neg(v0);
  const v8 = $lean_isize_mul(v7, v2);
  const v9 = $lean_isize_mul(v7, v7);
  const v10 = [];
  const v11 = [...v10, v1];
  const v12 = [...v11, v3];
  const v13 = [...v12, v4];
  const v14 = [...v13, v6];
  const v15 = [...v14, v8];
  return [...v15, v9];
})();
export const TestISize_test8 = (() => {
  const v0 = (v0, v1) => {
    const v2 = $lean_isize_dec_le(v1, v0);
    return v2;
  };
  const v1 = $lean_isize_of_nat(1n);
  const v2 = v0(v1, v1);
  const v3 = $lean_isize_of_nat(2n);
  const v4 = v0(v1, v3);
  const v5 = v0(v3, v1);
  const v6 = $lean_isize_neg(v3);
  const v7 = v0(v1, v6);
  const v8 = $lean_isize_neg(v1);
  const v9 = v0(v8, v3);
  const v10 = v0(v8, v8);
  const v11 = [];
  const v12 = [...v11, v2];
  const v13 = [...v12, v4];
  const v14 = [...v13, v5];
  const v15 = [...v14, v7];
  const v16 = [...v15, v9];
  return [...v16, v10];
})();
export const TestISize_test7 = (() => {
  const v0 = (v0, v1) => {
    const v2 = $lean_isize_dec_le(v0, v1);
    return v2;
  };
  const v1 = $lean_isize_of_nat(1n);
  const v2 = v0(v1, v1);
  const v3 = $lean_isize_of_nat(2n);
  const v4 = v0(v1, v3);
  const v5 = v0(v3, v1);
  const v6 = $lean_isize_neg(v3);
  const v7 = v0(v1, v6);
  const v8 = $lean_isize_neg(v1);
  const v9 = v0(v8, v3);
  const v10 = v0(v8, v8);
  const v11 = [];
  const v12 = [...v11, v2];
  const v13 = [...v12, v4];
  const v14 = [...v13, v5];
  const v15 = [...v14, v7];
  const v16 = [...v15, v9];
  return [...v16, v10];
})();
export const TestISize_test6 = (() => {
  const v0 = (v0, v1) => {
    const v2 = $lean_isize_dec_lt(v1, v0);
    return v2;
  };
  const v1 = $lean_isize_of_nat(1n);
  const v2 = v0(v1, v1);
  const v3 = $lean_isize_of_nat(2n);
  const v4 = v0(v1, v3);
  const v5 = v0(v3, v1);
  const v6 = $lean_isize_neg(v3);
  const v7 = v0(v1, v6);
  const v8 = $lean_isize_neg(v1);
  const v9 = v0(v8, v3);
  const v10 = v0(v8, v8);
  const v11 = [];
  const v12 = [...v11, v2];
  const v13 = [...v12, v4];
  const v14 = [...v13, v5];
  const v15 = [...v14, v7];
  const v16 = [...v15, v9];
  return [...v16, v10];
})();
export const TestISize_test5 = (() => {
  const v0 = (v0, v1) => {
    const v2 = $lean_isize_dec_lt(v0, v1);
    return v2;
  };
  const v1 = $lean_isize_of_nat(1n);
  const v2 = v0(v1, v1);
  const v3 = $lean_isize_of_nat(2n);
  const v4 = v0(v1, v3);
  const v5 = v0(v3, v1);
  const v6 = $lean_isize_neg(v3);
  const v7 = v0(v1, v6);
  const v8 = $lean_isize_neg(v1);
  const v9 = v0(v8, v3);
  const v10 = v0(v8, v8);
  const v11 = [];
  const v12 = [...v11, v2];
  const v13 = [...v12, v4];
  const v14 = [...v13, v5];
  const v15 = [...v14, v7];
  const v16 = [...v15, v9];
  return [...v16, v10];
})();
export const TestISize_test4 = (() => {
  const v0 = (v0, v1) => {
    const v2 = instDecidableEqISize(v0, v1);
    if (v2) {
      return false;
    } else {
      return true;
    }
  };
  const v1 = $lean_isize_of_nat(1n);
  const v2 = v0(v1, v1);
  const v3 = $lean_isize_of_nat(2n);
  const v4 = v0(v1, v3);
  const v5 = v0(v3, v1);
  const v6 = $lean_isize_neg(v3);
  const v7 = v0(v1, v6);
  const v8 = $lean_isize_neg(v1);
  const v9 = v0(v8, v3);
  const v10 = v0(v8, v8);
  const v11 = [];
  const v12 = [...v11, v2];
  const v13 = [...v12, v4];
  const v14 = [...v13, v5];
  const v15 = [...v14, v7];
  const v16 = [...v15, v9];
  return [...v16, v10];
})();
export const TestISize_test3 = (() => {
  const v0 = (v0, v1) => {
    const v2 = instDecidableEqISize(v0, v1);
    return v2;
  };
  const v1 = $lean_isize_of_nat(1n);
  const v2 = v0(v1, v1);
  const v3 = $lean_isize_of_nat(2n);
  const v4 = v0(v1, v3);
  const v5 = v0(v3, v1);
  const v6 = $lean_isize_neg(v3);
  const v7 = v0(v1, v6);
  const v8 = $lean_isize_neg(v1);
  const v9 = v0(v8, v3);
  const v10 = v0(v8, v8);
  const v11 = [];
  const v12 = [...v11, v2];
  const v13 = [...v12, v4];
  const v14 = [...v13, v5];
  const v15 = [...v14, v7];
  const v16 = [...v15, v9];
  return [...v16, v10];
})();
export const TestISize_test2 = (() => {
  const v0 = $lean_isize_of_nat(1n);
  const v1 = $lean_isize_sub(v0, v0);
  const v2 = $lean_isize_of_nat(2n);
  const v3 = $lean_isize_sub(v0, v2);
  const v4 = $lean_isize_sub(v2, v0);
  const v5 = $lean_isize_neg(v2);
  const v6 = $lean_isize_sub(v0, v5);
  const v7 = $lean_isize_neg(v0);
  const v8 = $lean_isize_sub(v7, v2);
  const v9 = $lean_isize_sub(v7, v7);
  const v10 = [];
  const v11 = [...v10, v1];
  const v12 = [...v11, v3];
  const v13 = [...v12, v4];
  const v14 = [...v13, v6];
  const v15 = [...v14, v8];
  return [...v15, v9];
})();
export const TestISize_test11 = (() => {
  const v0 = $lean_isize_of_nat(1n);
  const v1 = $lean_isize_neg(v0);
  const v2 = $lean_isize_neg(v1);
  const v3 = [];
  const v4 = [...v3, v1];
  return [...v4, v2];
})();
export const TestISize_test10 = (() => {
  const v0 = $lean_isize_of_nat(1n);
  const v1 = $lean_isize_div(v0, v0);
  const v2 = $lean_isize_of_nat(2n);
  const v3 = $lean_isize_div(v0, v2);
  const v4 = $lean_isize_div(v2, v0);
  const v5 = $lean_isize_neg(v2);
  const v6 = $lean_isize_div(v0, v5);
  const v7 = $lean_isize_neg(v0);
  const v8 = $lean_isize_div(v7, v2);
  const v9 = $lean_isize_div(v7, v7);
  const v10 = [];
  const v11 = [...v10, v1];
  const v12 = [...v11, v3];
  const v13 = [...v12, v4];
  const v14 = [...v13, v6];
  const v15 = [...v14, v8];
  return [...v15, v9];
})();
export const TestISize_test1 = (() => {
  const v0 = $lean_isize_of_nat(1n);
  const v1 = $lean_isize_add(v0, v0);
  const v2 = $lean_isize_of_nat(2n);
  const v3 = $lean_isize_add(v0, v2);
  const v4 = $lean_isize_add(v2, v0);
  const v5 = $lean_isize_neg(v2);
  const v6 = $lean_isize_add(v0, v5);
  const v7 = $lean_isize_neg(v0);
  const v8 = $lean_isize_add(v7, v2);
  const v9 = $lean_isize_add(v7, v7);
  const v10 = [];
  const v11 = [...v10, v1];
  const v12 = [...v11, v3];
  const v13 = [...v12, v4];
  const v14 = [...v13, v6];
  const v15 = [...v14, v8];
  return [...v15, v9];
})();
export const TestISize_intValues = (v0) => {
  const v1 = $lean_isize_of_nat(1n);
  const v2 = v0(v1, v1);
  const v3 = $lean_isize_of_nat(2n);
  const v4 = v0(v1, v3);
  const v5 = v0(v3, v1);
  const v6 = $lean_isize_neg(v3);
  const v7 = v0(v1, v6);
  const v8 = $lean_isize_neg(v1);
  const v9 = v0(v8, v3);
  const v10 = v0(v8, v8);
  const v11 = [];
  const v12 = [...v11, v2];
  const v13 = [...v12, v4];
  const v14 = [...v13, v5];
  const v15 = [...v14, v7];
  const v16 = [...v15, v9];
  return [...v16, v10];
};
