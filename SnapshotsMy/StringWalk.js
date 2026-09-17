import {
  $lean_string_pos_raw_at_end,
  $lean_string_pos_raw_get,
  $lean_string_pos_raw_next,
  $lean_string_push,
  $lean_string_utf8_byte_size,
} from "../runtime/lean_runtime.mjs";
const _private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0 = (
  v0,
  v1,
  v2,
) => {
  let v3 = v0, v4 = v1._1, v5 = v1._2, v6 = v2;
  while (true) {
    const v7 = v3._2;
    const v8 = v6 < v7;
    if (v8) {
      const v9 = $lean_string_utf8_byte_size(v5);
      const v10 = v4 + v9;
      const v11 = $lean_string_push(v5, "x");
      const v12 = v3._3;
      const v13 = v6 + v12;
      v4 = v10;
      v5 = v11;
      v6 = v13;
      continue;
    } else {
      return { tag: 0, _1: v4, _2: v5 };
    }
  }
};
export const test4_go = (v0, v1, v2) => {
  let v3 = v0, v4 = v1, v5 = v2;
  while (true) {
    const v6 = v3.length;
    const v7 = v4 < v6;
    if (v7) {
      const v8 = v4 + 1;
      const v9 = v5 + v4;
      v4 = v8;
      v5 = v9;
      continue;
    } else {
      return v5;
    }
  }
};
export const test2_go = (v0, v1, v2) => {
  let v3 = v0, v4 = v1, v5 = v2;
  while (true) {
    const v6 = $lean_string_pos_raw_at_end(v3, v5);
    if (v6) {
      return v5;
    } else {
      const v7 = $lean_string_pos_raw_get(v3, v5);
      const v8 = v7 === v4;
      if (v8) {
        return v5;
      } else {
        const v9 = $lean_string_pos_raw_next(v3, v5);
        v5 = v9;
        continue;
      }
    }
  }
};
export const test1_go = (v0, v1, v2, v3) => {
  let v4 = v0, v5 = v1, v6 = v2, v7 = v3;
  while (true) {
    const v8 = $lean_string_pos_raw_at_end(v4, v6);
    if (v8) {
      return v7;
    } else {
      const v9 = $lean_string_pos_raw_next(v4, v6);
      const v10 = $lean_string_pos_raw_get(v4, v6);
      const v11 = v10 === v5;
      if (v11) {
        const v12 = v7 + 1;
        v6 = v9;
        v7 = v12;
        continue;
      } else {
        v6 = v9;
        continue;
      }
    }
  }
};
export const test4 = (v0) => test4_go(v0, 0, 0);
export const test3 = (v0, v1) => {
  const v2 = { tag: 0, _1: 0, _2: v1, _3: 1 };
  const v3 = { tag: 0, _1: 0, _2: v0 };
  const v4 = _private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0(
    v2,
    v3,
    0,
  );
  return v4._1;
};
export const test2 = (v0, v1) => test2_go(v0, v1, 0);
export const test1 = (v0, v1) => test1_go(v0, v1, 0, 0);
