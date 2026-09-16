const _private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0 = (
  v0,
  v1,
  v2,
) => {
  let v3 = v0, v4 = v1, v5 = v2, c$3 = true, r$3;
  while (c$3) {
    const v6 = v3._2;
    const v7 = v5 < v6;
    if (v7) {
      const v8 = v4._1;
      const v9 = v4._2;
      const v10 = $lean_string_utf8_byte_size(v9);
      const v11 = v8 + v10;
      const v12 = 120;
      const v13 = v9 + v12;
      const v14 = { tag: 0, _1: v11, _2: v13 };
      const v15 = v3._3;
      const v16 = v5 + v15;
      const t$3$0 = v3;
      const t$3$1 = v14;
      const t$3$2 = v16;
      v3 = t$3$0;
      v4 = t$3$1;
      v5 = t$3$2;
      continue;
    } else {
      c$3 = false;
      r$3 = v4;
      continue;
    }
  }
  return r$3;
};
const test4_go = (v0, v1, v2) => {
  let v3 = v0, v4 = v1, v5 = v2, c$3 = true, r$3;
  while (c$3) {
    const v6 = v3.length;
    const v7 = v4 < v6;
    if (v7) {
      const v8 = 1;
      const v9 = v4 + v8;
      const v10 = v5 + v4;
      const t$3$0 = v3;
      const t$3$1 = v9;
      const t$3$2 = v10;
      v3 = t$3$0;
      v4 = t$3$1;
      v5 = t$3$2;
      continue;
    } else {
      c$3 = false;
      r$3 = v5;
      continue;
    }
  }
  return r$3;
};
const test2_go = (v0, v1, v2) => {
  let v3 = v0, v4 = v1, v5 = v2, c$3 = true, r$3;
  while (c$3) {
    const v6 = $lean_string_pos_raw_at_end(v3, v5);
    if (v6) {
      c$3 = false;
      r$3 = v5;
      continue;
    } else {
      const v7 = $lean_string_pos_raw_get(v3, v5);
      const v8 = v7 === v4;
      const v9 = v8;
      if (v9) {
        c$3 = false;
        r$3 = v5;
        continue;
      } else {
        const v10 = $lean_string_pos_raw_next(v3, v5);
        const t$3$0 = v3;
        const t$3$1 = v4;
        const t$3$2 = v10;
        v3 = t$3$0;
        v4 = t$3$1;
        v5 = t$3$2;
        continue;
      }
    }
  }
  return r$3;
};
const test1_go = (v0, v1, v2, v3) => {
  let v4 = v0, v5 = v1, v6 = v2, v7 = v3, c$4 = true, r$4;
  while (c$4) {
    const v8 = $lean_string_pos_raw_at_end(v4, v6);
    if (v8) {
      c$4 = false;
      r$4 = v7;
      continue;
    } else {
      const v9 = $lean_string_pos_raw_next(v4, v6);
      const v10 = $lean_string_pos_raw_get(v4, v6);
      const v11 = v10 === v5;
      const v12 = v11;
      if (v12) {
        const v13 = 1;
        const v14 = v7 + v13;
        const t$4$0 = v4;
        const t$4$1 = v5;
        const t$4$2 = v9;
        const t$4$3 = v14;
        v4 = t$4$0;
        v5 = t$4$1;
        v6 = t$4$2;
        v7 = t$4$3;
        continue;
      } else {
        const t$4$0 = v4;
        const t$4$1 = v5;
        const t$4$2 = v9;
        const t$4$3 = v7;
        v4 = t$4$0;
        v5 = t$4$1;
        v6 = t$4$2;
        v7 = t$4$3;
        continue;
      }
    }
  }
  return r$4;
};
const test4 = (v0) => {
  const v1 = 0;
  return test4_go(v0, v1, v1);
};
const test3 = (v0, v1) => {
  const v2 = 0;
  const v3 = 1;
  const v4 = { tag: 0, _1: v2, _2: v1, _3: v3 };
  const v5 = { tag: 0, _1: v2, _2: v0 };
  const v6 = _private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0(
    v4,
    v5,
    v2,
  );
  const v7 = v6._1;
  const v8 = v6._2;
  return v7;
};
const test2 = (v0, v1) => {
  const v2 = 0;
  const v3 = v2;
  return test2_go(v0, v1, v3);
};
const test1 = (v0, v1) => {
  const v2 = 0;
  const v3 = v2;
  return test1_go(v0, v1, v3, v2);
};
export { test4_go, test2_go, test1_go, test4, test3, test2, test1 };
