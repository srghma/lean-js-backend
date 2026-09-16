const _private_Init_Data_Array_Basic_0_Array_foldrMUnsafe_fold__at__test_spec_0 = (
  v0,
  v1,
  v2,
  v3,
) => {
  let v4 = v0, v5 = v1, v6 = v2, v7 = v3, c$4 = true, r$4;
  while (c$4) {
    const v8 = (v8, v9) => {
      const v10 = "1";
      const v11 = $lean_string_utf8_byte_size(v8);
      const v12 = $lean_string_utf8_byte_size(v10);
      const v13 = v12 <= v11;
      if (v13) {
        const v14 = 0;
        const v15 = v12;
        const v16 = v14;
        const v17 = $lean_string_memcmp(v8, v10, v16, v16, v15);
        if (v17) {
          const v18 = 1;
          const v19 = v16;
          const v20 = v11;
          const v21 = v20;
          const v22 = { tag: 0, _1: v8, _2: v19, _3: v21 };
          const v23 = v16;
          const v24 = String_Slice_Pos_nextn(v22, v23, v18);
          const v25 = v24;
          const v26 = v25;
          const v27 = v26;
          const v28 = v27;
          const v29 = { tag: 0, _1: v8, _2: v28, _3: v21 };
          const v30 = String_Slice_toString(v29);
          const v31 = "2";
          const v32 = v31 + v30;
          const v33 = "wat";
          const v34 = v32 === v33;
          const v35 = v34;
          if (v35) {
            return v9;
          } else {
            const v36 = v32 + v10;
            return { tag: 1, _1: v36, _2: v9 };
          }
        } else {
          return v9;
        }
      } else {
        return v9;
      }
    };
    const v9 = instDecidableEqUSize(v5, v6);
    const v10 = v9;
    if (v10) {
      c$4 = false;
      r$4 = v7;
      continue;
    } else {
      const v11 = 1;
      const v12 = v5 - v11;
      const v13 = $lean_array_uget(v4, v12);
      const v14 = 1;
      const v15 = v14;
      const v16 = v13 + v15;
      if (v16 < 0) {
        const v17 = -1 - v16;
        const v18 = "-";
        const v19 = v17 + 1;
        const v20 = Nat_reprFast(v19);
        const v21 = $lean_string_append(v18, v20);
        const v22 = v8(v21, v7);
        const t$4$0 = v4;
        const t$4$1 = v12;
        const t$4$2 = v6;
        const t$4$3 = v22;
        v4 = t$4$0;
        v5 = t$4$1;
        v6 = t$4$2;
        v7 = t$4$3;
        continue;
      } else {
        const v17 = v16;
        const v18 = Nat_reprFast(v17);
        const v19 = v8(v18, v7);
        const t$4$0 = v4;
        const t$4$1 = v12;
        const t$4$2 = v6;
        const t$4$3 = v19;
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
const toArray = (v0) => {
  const v1 = (v1, v2) => ({ tag: 1, _1: v1, _2: v2 });
  const v2 = v0;
  const v3 = { tag: 0 };
  return v2(v1, v3);
};
const test = (v0) => {
  const v1 = { tag: 0 };
  const v2 = v0.length;
  const v3 = 0;
  const v4 = v3 < v2;
  if (v4) {
    const v5 = $lean_usize_of_nat(v2);
    const v6 = 0;
    return _private_Init_Data_Array_Basic_0_Array_foldrMUnsafe_fold__at__test_spec_0(
      v0,
      v5,
      v6,
      v1,
    );
  } else {
    return v1;
  }
};
const overArray = (v0, v1) => {
  const v2 = (v2, v3) => {
    const v4 = (v4, v5) => v2(v4, v5);
    const v5 = v1.length;
    const v6 = 0;
    const v7 = Id_instMonad;
    const v8 = v6 < v5;
    if (v8) {
      const v9 = $lean_usize_of_nat(v5);
      const v10 = 0;
      return _private_Init_Data_Array_Basic_0_Array_foldrMUnsafe_fold(
        v7,
        v4,
        v1,
        v9,
        v10,
        v3,
      );
    } else {
      return v3;
    }
  };
  const v3 = (v3, v4) => ({ tag: 1, _1: v3, _2: v4 });
  const v4 = v2;
  const v5 = v0(v4);
  const v6 = v5;
  const v7 = { tag: 0 };
  return v6(v3, v7);
};
const mapF = (v0, v1) => (v2, v3) => {
  const v4 = (v4, v5) => {
    const v6 = v0(v4);
    return v2(v6, v5);
  };
  const v5 = v1;
  return v5(v4, v3);
};
const fromArray = (v0) => (v1, v2) => {
  const v3 = (v3, v4) => v1(v3, v4);
  const v4 = v0.length;
  const v5 = 0;
  const v6 = Id_instMonad;
  const v7 = v4 <= v4;
  if (v7) {
    const v8 = v5 < v4;
    if (v8) {
      const v9 = $lean_usize_of_nat(v4);
      const v10 = 0;
      return _private_Init_Data_Array_Basic_0_Array_foldrMUnsafe_fold(
        v6,
        v3,
        v0,
        v9,
        v10,
        v2,
      );
    } else {
      return v2;
    }
  } else {
    const v8 = v5 < v4;
    if (v8) {
      const v9 = $lean_usize_of_nat(v4);
      const v10 = 0;
      return _private_Init_Data_Array_Basic_0_Array_foldrMUnsafe_fold(
        v6,
        v3,
        v0,
        v9,
        v10,
        v2,
      );
    } else {
      return v2;
    }
  }
};
const filterMapF = (v0, v1) => (v2, v3) => {
  const v4 = (v4, v5) => {
    const v6 = v0(v4);
    if (v6.tag === 0) {
      return v5;
    } else {
      const v7 = v6._1;
      return v2(v7, v5);
    }
  };
  const v5 = v1;
  return v5(v4, v3);
};
const filterF = (v0, v1) => (v2, v3) => {
  const v4 = (v4, v5) => {
    const v6 = v0(v4);
    if (v6) {
      return v2(v4, v5);
    } else {
      return v5;
    }
  };
  const v5 = v1;
  return v5(v4, v3);
};
const dropPrefix1 = (v0) => {
  const v1 = "1";
  const v2 = $lean_string_utf8_byte_size(v0);
  const v3 = $lean_string_utf8_byte_size(v1);
  const v4 = v3 <= v2;
  if (v4) {
    const v5 = 0;
    const v6 = v3;
    const v7 = v5;
    const v8 = $lean_string_memcmp(v0, v1, v7, v7, v6);
    if (v8) {
      const v9 = 1;
      const v10 = v7;
      const v11 = v2;
      const v12 = v11;
      const v13 = { tag: 0, _1: v0, _2: v10, _3: v12 };
      const v14 = v7;
      const v15 = String_Slice_Pos_nextn(v13, v14, v9);
      const v16 = v15;
      const v17 = v16;
      const v18 = v17;
      const v19 = v18;
      const v20 = { tag: 0, _1: v0, _2: v19, _3: v12 };
      const v21 = String_Slice_toString(v20);
      return { tag: 1, _1: v21 };
    } else {
      return { tag: 0 };
    }
  } else {
    return { tag: 0 };
  }
};
export {
  toArray,
  test,
  overArray,
  mapF,
  fromArray,
  filterMapF,
  filterF,
  dropPrefix1,
};
