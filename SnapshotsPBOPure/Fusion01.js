import {
  $lean_array_mk,
  $lean_array_uget,
  $lean_string_memcmp,
  Id_instMonad,
  Nat_reprFast,
  String_Slice_Pos_nextn,
  String_Slice_toString,
  _private_Init_Data_Array_Basic_0_Array_foldrMUnsafe_fold,
  instDecidableEqUSize,
} from "../runtime/lean_runtime_non_configurable.mjs";
import {
  $lean_string_utf8_byte_size,
} from "../runtime/lean_runtime_nat_num.mjs";
import {
  $lean_usize_of_nat,
  $lean_usize_sub,
} from "../runtime/lean_runtime_usize_num.mjs";
const _private_Init_Data_Array_Basic_0_Array_foldrMUnsafe_fold__at__test_spec_0 = (
  v0,
  v1,
  v2,
  v3,
) => {
  let v4 = v0, v5 = v1, v6 = v2, v7 = v3;
  while (true) {
    const v8 = (v8, v9) => {
      const v10 = $lean_string_utf8_byte_size(v8);
      const v11 = $lean_string_utf8_byte_size("1");
      const v12 = v11 <= v10;
      if (v12) {
        const v13 = $lean_string_memcmp(v8, "1", 0, 0, v11);
        if (v13) {
          const v14 = { tag: 0, _1: v8, _2: 0, _3: v10 };
          const v15 = String_Slice_Pos_nextn(v14, 0, 1);
          const v16 = { tag: 0, _1: v8, _2: v15, _3: v10 };
          const v17 = String_Slice_toString(v16);
          const v18 = "2" + v17;
          const v19 = v18 === "wat";
          if (v19) {
            return v9;
          } else {
            const v20 = v18 + "1";
            return { tag: 1, _1: v20, _2: v9 };
          }
        } else {
          return v9;
        }
      } else {
        return v9;
      }
    };
    const v9 = instDecidableEqUSize(v5, v6);
    if (v9) {
      return v7;
    } else {
      const v10 = $lean_usize_sub(v5, 1);
      const v11 = $lean_array_uget(v4, v10);
      const v12 = v11 + 1;
      if (v12 < 0) {
        const v13 = -1 - v12;
        const v14 = v13 + 1;
        const v15 = Nat_reprFast(v14);
        const v16 = "-" + v15;
        const v17 = v8(v16, v7);
        v5 = v10;
        v7 = v17;
        continue;
      } else {
        const v13 = Nat_reprFast(v12);
        const v14 = v8(v13, v7);
        v5 = v10;
        v7 = v14;
        continue;
      }
    }
  }
};
export const toArray = (v0) => {
  const v1 = (v1, v2) => ({ tag: 1, _1: v1, _2: v2 });
  const v2 = { tag: 0 };
  const v3 = v0(v1, v2);
  return $lean_array_mk(v3);
};
export const test = (v0) => {
  const v1 = { tag: 0 };
  const v2 = v0.length;
  const v3 = 0 < v2;
  if (v3) {
    const v4 = $lean_usize_of_nat(v2);
    const v5 = _private_Init_Data_Array_Basic_0_Array_foldrMUnsafe_fold__at__test_spec_0(
      v0,
      v4,
      0,
      v1,
    );
    return $lean_array_mk(v5);
  } else {
    return $lean_array_mk(v1);
  }
};
export const overArray = (v0, v1) => {
  const v2 = (v2, v3) => {
    const v4 = (v4, v5) => v2(v4, v5);
    const v5 = v1.length;
    const v6 = 0 < v5;
    if (v6) {
      const v7 = $lean_usize_of_nat(v5);
      return _private_Init_Data_Array_Basic_0_Array_foldrMUnsafe_fold(
        Id_instMonad,
        v4,
        v1,
        v7,
        0,
        v3,
      );
    } else {
      return v3;
    }
  };
  const v3 = (v3, v4) => ({ tag: 1, _1: v3, _2: v4 });
  const v4 = v0(v2);
  const v5 = { tag: 0 };
  const v6 = v4(v3, v5);
  return $lean_array_mk(v6);
};
export const mapF = (v0, v1) => (v2, v3) => {
  const v4 = (v4, v5) => {
    const v6 = v0(v4);
    return v2(v6, v5);
  };
  return v1(v4, v3);
};
export const fromArray = (v0) => (v1, v2) => {
  const v3 = (v3, v4) => v1(v3, v4);
  const v4 = v0.length;
  const v5 = v4 <= v4;
  if (v5) {
    const v6 = 0 < v4;
    if (v6) {
      const v7 = $lean_usize_of_nat(v4);
      return _private_Init_Data_Array_Basic_0_Array_foldrMUnsafe_fold(
        Id_instMonad,
        v3,
        v0,
        v7,
        0,
        v2,
      );
    } else {
      return v2;
    }
  } else {
    const v6 = 0 < v4;
    if (v6) {
      const v7 = $lean_usize_of_nat(v4);
      return _private_Init_Data_Array_Basic_0_Array_foldrMUnsafe_fold(
        Id_instMonad,
        v3,
        v0,
        v7,
        0,
        v2,
      );
    } else {
      return v2;
    }
  }
};
export const filterMapF = (v0, v1) => (v2, v3) => {
  const v4 = (v4, v5) => {
    const v6 = v0(v4);
    if (v6.tag === 0) {
      return v5;
    } else {
      const v7 = v6._1;
      return v2(v7, v5);
    }
  };
  return v1(v4, v3);
};
export const filterF = (v0, v1) => (v2, v3) => {
  const v4 = (v4, v5) => {
    const v6 = v0(v4);
    if (v6) {
      return v2(v4, v5);
    } else {
      return v5;
    }
  };
  return v1(v4, v3);
};
export const dropPrefix1 = (v0) => {
  const v1 = $lean_string_utf8_byte_size(v0);
  const v2 = $lean_string_utf8_byte_size("1");
  const v3 = v2 <= v1;
  if (v3) {
    const v4 = $lean_string_memcmp(v0, "1", 0, 0, v2);
    if (v4) {
      const v5 = { tag: 0, _1: v0, _2: 0, _3: v1 };
      const v6 = String_Slice_Pos_nextn(v5, 0, 1);
      const v7 = { tag: 0, _1: v0, _2: v6, _3: v1 };
      const v8 = String_Slice_toString(v7);
      return { tag: 1, _1: v8 };
    } else {
      return { tag: 0 };
    }
  } else {
    return { tag: 0 };
  }
};
