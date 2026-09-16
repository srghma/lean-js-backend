const Std_DHashMap_Internal_AssocList_foldlM__at___private_Std_Data_DHashMap_Internal_Defs_0_Std_DHashMap_Internal_Raw__expand_go__at__Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_1_spec_2_spec_5 = (
  v0,
  v1,
) => {
  let v2 = v0, v3 = v1, c$2 = true, r$2;
  while (c$2) {
    if (v3.tag === 0) {
      c$2 = false;
      r$2 = v2;
      continue;
    } else {
      const v4 = v3._1;
      const v5 = v3._2;
      const v6 = v3._3;
      const v7 = v2;
      const v8 = v7.length;
      const v9 = $lean_uint64_of_nat(v4);
      const v10 = 32;
      const v11 = $lean_uint64_shift_right(v9, v10);
      const v12 = $lean_uint64_xor(v9, v11);
      const v13 = 16;
      const v14 = $lean_uint64_shift_right(v12, v13);
      const v15 = $lean_uint64_xor(v12, v14);
      const v16 = $lean_uint64_to_usize(v15);
      const v17 = $lean_usize_of_nat(v8);
      const v18 = 1;
      const v19 = v17 - v18;
      const v20 = $lean_usize_land(v16, v19);
      const v21 = $lean_array_uget(v7, v20);
      const v22 = { tag: 1, _1: v4, _2: v5, _3: v21 };
      const v23 = $lean_array_uset(v7, v20, v22);
      const v24 = v23;
      const t$2$0 = v24;
      const t$2$1 = v6;
      v2 = t$2$0;
      v3 = t$2$1;
      continue;
    }
  }
  return r$2;
};
const Std_DHashMap_Internal_AssocList_foldlM__at___private_Std_Data_DHashMap_Internal_Defs_0_Std_DHashMap_Internal_Raw__expand_go__at__Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_3_spec_4_spec_6 = (
  v0,
  v1,
) => {
  let v2 = v0, v3 = v1, c$2 = true, r$2;
  while (c$2) {
    if (v3.tag === 0) {
      c$2 = false;
      r$2 = v2;
      continue;
    } else {
      const v4 = v3._1;
      const v5 = v3._2;
      const v6 = v3._3;
      const v7 = v2;
      const v8 = v7.length;
      const v9 = $lean_string_hash(v4);
      const v10 = 32;
      const v11 = $lean_uint64_shift_right(v9, v10);
      const v12 = $lean_uint64_xor(v9, v11);
      const v13 = 16;
      const v14 = $lean_uint64_shift_right(v12, v13);
      const v15 = $lean_uint64_xor(v12, v14);
      const v16 = $lean_uint64_to_usize(v15);
      const v17 = $lean_usize_of_nat(v8);
      const v18 = 1;
      const v19 = v17 - v18;
      const v20 = $lean_usize_land(v16, v19);
      const v21 = $lean_array_uget(v7, v20);
      const v22 = { tag: 1, _1: v4, _2: v5, _3: v21 };
      const v23 = $lean_array_uset(v7, v20, v22);
      const v24 = v23;
      const t$2$0 = v24;
      const t$2$1 = v6;
      v2 = t$2$0;
      v3 = t$2$1;
      continue;
    }
  }
  return r$2;
};
const _private_Std_Data_DHashMap_Internal_Defs_0_Std_DHashMap_Internal_Raw__expand_go__at__Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_1_spec_2 = (
  v0,
  v1,
  v2,
) => {
  let v3 = v0, v4 = v1, v5 = v2, c$3 = true, r$3;
  while (c$3) {
    const v6 = v4.length;
    const v7 = v3 < v6;
    if (v7) {
      const v8 = v4[v3];
      const v9 = { tag: 0 };
      const v10 = $lean_array_fset(v4, v3, v9);
      const v11 = Std_DHashMap_Internal_AssocList_foldlM__at___private_Std_Data_DHashMap_Internal_Defs_0_Std_DHashMap_Internal_Raw__expand_go__at__Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_1_spec_2_spec_5(
        v5,
        v8,
      );
      const v12 = 1;
      const v13 = v3 + v12;
      const t$3$0 = v13;
      const t$3$1 = v10;
      const t$3$2 = v11;
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
const _private_Std_Data_DHashMap_Internal_Defs_0_Std_DHashMap_Internal_Raw__expand_go__at__Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_3_spec_4 = (
  v0,
  v1,
  v2,
) => {
  let v3 = v0, v4 = v1, v5 = v2, c$3 = true, r$3;
  while (c$3) {
    const v6 = v4.length;
    const v7 = v3 < v6;
    if (v7) {
      const v8 = v4[v3];
      const v9 = { tag: 0 };
      const v10 = $lean_array_fset(v4, v3, v9);
      const v11 = Std_DHashMap_Internal_AssocList_foldlM__at___private_Std_Data_DHashMap_Internal_Defs_0_Std_DHashMap_Internal_Raw__expand_go__at__Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_3_spec_4_spec_6(
        v5,
        v8,
      );
      const v12 = 1;
      const v13 = v3 + v12;
      const t$3$0 = v13;
      const t$3$1 = v10;
      const t$3$2 = v11;
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
const Std_DHashMap_Internal_AssocList_contains__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_0 = (
  v0,
  v1,
) => {
  let v2 = v0, v3 = v1, c$2 = true, r$2;
  while (c$2) {
    if (v3.tag === 0) {
      const v4 = false;
      c$2 = false;
      r$2 = v4;
      continue;
    } else {
      const v4 = v3._1;
      const v5 = v3._2;
      const v6 = v3._3;
      const v7 = v4 === v2;
      const v8 = v7;
      if (v8) {
        c$2 = false;
        r$2 = v8;
        continue;
      } else {
        const t$2$0 = v2;
        const t$2$1 = v6;
        v2 = t$2$0;
        v3 = t$2$1;
        continue;
      }
    }
  }
  return r$2;
};
const Std_DHashMap_Internal_AssocList_replace__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_2 = (
  v0,
  v1,
  v2,
) => {
  if (v2.tag === 0) {
    return v2;
  } else {
    const v3 = v2._1;
    const v4 = v2._2;
    const v5 = v2._3;
    const v6 = v3 === v0;
    const v7 = v6;
    if (v7) {
      return { tag: 1, _1: v0, _2: v1, _3: v5 };
    } else {
      const v8 = Std_DHashMap_Internal_AssocList_replace__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_2(
        v0,
        v1,
        v5,
      );
      return { tag: 1, _1: v3, _2: v4, _3: v8 };
    }
  }
};
const Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_1 = (
  v0,
) => {
  const v1 = v0;
  const v2 = v1.length;
  const v3 = 2;
  const v4 = v2 * v3;
  const v5 = 0;
  const v6 = { tag: 0 };
  const v7 = $lean_mk_array(v4, v6);
  const v8 = v7;
  return _private_Std_Data_DHashMap_Internal_Defs_0_Std_DHashMap_Internal_Raw__expand_go__at__Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_1_spec_2(
    v5,
    v1,
    v8,
  );
};
const Std_DHashMap_Internal_AssocList_replace__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_4 = (
  v0,
  v1,
  v2,
) => {
  if (v2.tag === 0) {
    return v2;
  } else {
    const v3 = v2._1;
    const v4 = v2._2;
    const v5 = v2._3;
    const v6 = v3 === v0;
    const v7 = v6;
    if (v7) {
      return { tag: 1, _1: v0, _2: v1, _3: v5 };
    } else {
      const v8 = Std_DHashMap_Internal_AssocList_replace__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_4(
        v0,
        v1,
        v5,
      );
      return { tag: 1, _1: v3, _2: v4, _3: v8 };
    }
  }
};
const Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_3 = (
  v0,
) => {
  const v1 = v0;
  const v2 = v1.length;
  const v3 = 2;
  const v4 = v2 * v3;
  const v5 = 0;
  const v6 = { tag: 0 };
  const v7 = $lean_mk_array(v4, v6);
  const v8 = v7;
  return _private_Std_Data_DHashMap_Internal_Defs_0_Std_DHashMap_Internal_Raw__expand_go__at__Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_3_spec_4(
    v5,
    v1,
    v8,
  );
};
const Std_DHashMap_Internal_AssocList_getD__at__Std_DHashMap_Internal_Raw__Const_getD__at__test1_spec_0_spec_0 = (
  v0,
  v1,
  v2,
) => {
  let v3 = v0, v4 = v1, v5 = v2, c$3 = true, r$3;
  while (c$3) {
    if (v5.tag === 0) {
      c$3 = false;
      r$3 = v4;
      continue;
    } else {
      const v6 = v5._1;
      const v7 = v5._2;
      const v8 = v5._3;
      const v9 = v6 === v3;
      const v10 = v9;
      if (v10) {
        c$3 = false;
        r$3 = v7;
        continue;
      } else {
        const t$3$0 = v3;
        const t$3$1 = v4;
        const t$3$2 = v8;
        v3 = t$3$0;
        v4 = t$3$1;
        v5 = t$3$2;
        continue;
      }
    }
  }
  return r$3;
};
const Std_DHashMap_Internal_AssocList_foldrM__at__test6_spec_1 = (v0, v1) => {
  if (v1.tag === 0) {
    return v0;
  } else {
    const v2 = v1._1;
    const v3 = v1._2;
    const v4 = v1._3;
    const v5 = Std_DHashMap_Internal_AssocList_foldrM__at__test6_spec_1(v0, v4);
    const v6 = { tag: 0, _1: v2, _2: v3 };
    return { tag: 1, _1: v6, _2: v5 };
  }
};
const Std_DHashMap_Internal_AssocList_erase__at__Std_DHashMap_Internal_Raw__erase__at__test5_spec_0_spec_0 = (
  v0,
  v1,
) => {
  if (v1.tag === 0) {
    return v1;
  } else {
    const v2 = v1._1;
    const v3 = v1._2;
    const v4 = v1._3;
    const v5 = v2 === v0;
    const v6 = v5;
    if (v6) {
      return v4;
    } else {
      const v7 = Std_DHashMap_Internal_AssocList_erase__at__Std_DHashMap_Internal_Raw__erase__at__test5_spec_0_spec_0(
        v0,
        v4,
      );
      return { tag: 1, _1: v2, _2: v3, _3: v7 };
    }
  }
};
const Std_DHashMap_Internal_AssocList_contains__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_2 = (
  v0,
  v1,
) => {
  let v2 = v0, v3 = v1, c$2 = true, r$2;
  while (c$2) {
    if (v3.tag === 0) {
      const v4 = false;
      c$2 = false;
      r$2 = v4;
      continue;
    } else {
      const v4 = v3._1;
      const v5 = v3._2;
      const v6 = v3._3;
      const v7 = v4 === v2;
      const v8 = v7;
      if (v8) {
        c$2 = false;
        r$2 = v8;
        continue;
      } else {
        const t$2$0 = v2;
        const t$2$1 = v6;
        v2 = t$2$0;
        v3 = t$2$1;
        continue;
      }
    }
  }
  return r$2;
};
const Std_DHashMap_Internal_Raw__insertIfNew__at__test3_spec_0 = (
  v0,
  v1,
  v2,
) => {
  const v3 = v0;
  const v4 = v3._1;
  const v5 = v3._2;
  const v6 = v5.length;
  const v7 = $lean_string_hash(v1);
  const v8 = 32;
  const v9 = $lean_uint64_shift_right(v7, v8);
  const v10 = $lean_uint64_xor(v7, v9);
  const v11 = 16;
  const v12 = $lean_uint64_shift_right(v10, v11);
  const v13 = $lean_uint64_xor(v10, v12);
  const v14 = $lean_uint64_to_usize(v13);
  const v15 = $lean_usize_of_nat(v6);
  const v16 = 1;
  const v17 = v15 - v16;
  const v18 = $lean_usize_land(v14, v17);
  const v19 = $lean_array_uget(v5, v18);
  const v20 = Std_DHashMap_Internal_AssocList_contains__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_2(
    v1,
    v19,
  );
  if (v20) {
    return v3;
  } else {
    const v21 = 1;
    const v22 = v4 + v21;
    const v23 = { tag: 1, _1: v1, _2: v2, _3: v19 };
    const v24 = $lean_array_uset(v5, v18, v23);
    const v25 = 4;
    const v26 = v22 * v25;
    const v27 = 3;
    const v28 = Math.trunc(v26 / v27);
    const v29 = v24.length;
    const v30 = v28 <= v29;
    if (v30) {
      return { tag: 0, _1: v22, _2: v24 };
    } else {
      const v31 = v24;
      const v32 = Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_3(
        v31,
      );
      const v33 = v32;
      return { tag: 0, _1: v22, _2: v33 };
    }
  }
};
const Std_DHashMap_Internal_Raw__insert__at__test2_spec_0 = (v0, v1, v2) => {
  const v3 = v0;
  const v4 = v3._1;
  const v5 = v3._2;
  const v6 = v5.length;
  const v7 = $lean_uint64_of_nat(v1);
  const v8 = 32;
  const v9 = $lean_uint64_shift_right(v7, v8);
  const v10 = $lean_uint64_xor(v7, v9);
  const v11 = 16;
  const v12 = $lean_uint64_shift_right(v10, v11);
  const v13 = $lean_uint64_xor(v10, v12);
  const v14 = $lean_uint64_to_usize(v13);
  const v15 = $lean_usize_of_nat(v6);
  const v16 = 1;
  const v17 = v15 - v16;
  const v18 = $lean_usize_land(v14, v17);
  const v19 = $lean_array_uget(v5, v18);
  const v20 = Std_DHashMap_Internal_AssocList_contains__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_0(
    v1,
    v19,
  );
  if (v20) {
    const v21 = { tag: 0 };
    const v22 = $lean_array_uset(v5, v18, v21);
    const v23 = Std_DHashMap_Internal_AssocList_replace__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_2(
      v1,
      v2,
      v19,
    );
    const v24 = $lean_array_uset(v22, v18, v23);
    return { tag: 0, _1: v4, _2: v24 };
  } else {
    const v21 = 1;
    const v22 = v4 + v21;
    const v23 = { tag: 1, _1: v1, _2: v2, _3: v19 };
    const v24 = $lean_array_uset(v5, v18, v23);
    const v25 = 4;
    const v26 = v22 * v25;
    const v27 = 3;
    const v28 = Math.trunc(v26 / v27);
    const v29 = v24.length;
    const v30 = v28 <= v29;
    if (v30) {
      return { tag: 0, _1: v22, _2: v24 };
    } else {
      const v31 = v24;
      const v32 = Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_1(
        v31,
      );
      const v33 = v32;
      return { tag: 0, _1: v22, _2: v33 };
    }
  }
};
const Std_DHashMap_Internal_AssocList_get___at__Std_DHashMap_Internal_Raw__Const_get___at__test2_spec_2_spec_5 = (
  v0,
  v1,
) => {
  let v2 = v0, v3 = v1, c$2 = true, r$2;
  while (c$2) {
    if (v3.tag === 0) {
      const v4 = { tag: 0 };
      c$2 = false;
      r$2 = v4;
      continue;
    } else {
      const v4 = v3._1;
      const v5 = v3._2;
      const v6 = v3._3;
      const v7 = v4 === v2;
      const v8 = v7;
      if (v8) {
        const v9 = { tag: 1, _1: v5 };
        c$2 = false;
        r$2 = v9;
        continue;
      } else {
        const t$2$0 = v2;
        const t$2$1 = v6;
        v2 = t$2$0;
        v3 = t$2$1;
        continue;
      }
    }
  }
  return r$2;
};
const Std_DHashMap_Internal_Raw__insert__at__test1_spec_1 = (v0, v1, v2) => {
  const v3 = v0;
  const v4 = v3._1;
  const v5 = v3._2;
  const v6 = v5.length;
  const v7 = $lean_string_hash(v1);
  const v8 = 32;
  const v9 = $lean_uint64_shift_right(v7, v8);
  const v10 = $lean_uint64_xor(v7, v9);
  const v11 = 16;
  const v12 = $lean_uint64_shift_right(v10, v11);
  const v13 = $lean_uint64_xor(v10, v12);
  const v14 = $lean_uint64_to_usize(v13);
  const v15 = $lean_usize_of_nat(v6);
  const v16 = 1;
  const v17 = v15 - v16;
  const v18 = $lean_usize_land(v14, v17);
  const v19 = $lean_array_uget(v5, v18);
  const v20 = Std_DHashMap_Internal_AssocList_contains__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_2(
    v1,
    v19,
  );
  if (v20) {
    const v21 = { tag: 0 };
    const v22 = $lean_array_uset(v5, v18, v21);
    const v23 = Std_DHashMap_Internal_AssocList_replace__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_4(
      v1,
      v2,
      v19,
    );
    const v24 = $lean_array_uset(v22, v18, v23);
    return { tag: 0, _1: v4, _2: v24 };
  } else {
    const v21 = 1;
    const v22 = v4 + v21;
    const v23 = { tag: 1, _1: v1, _2: v2, _3: v19 };
    const v24 = $lean_array_uset(v5, v18, v23);
    const v25 = 4;
    const v26 = v22 * v25;
    const v27 = 3;
    const v28 = Math.trunc(v26 / v27);
    const v29 = v24.length;
    const v30 = v28 <= v29;
    if (v30) {
      return { tag: 0, _1: v22, _2: v24 };
    } else {
      const v31 = v24;
      const v32 = Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_3(
        v31,
      );
      const v33 = v32;
      return { tag: 0, _1: v22, _2: v33 };
    }
  }
};
const List_forIn__loop__at__test7_spec_0 = (v0, v1, v2, v3, v4) => {
  let v5 = v0, v6 = v1, v7 = v2, v8 = v3, v9 = v4, c$5 = true, r$5;
  while (c$5) {
    if (v8.tag === 0) {
      c$5 = false;
      r$5 = v9;
      continue;
    } else {
      const v10 = v8._1;
      const v11 = v8._2;
      const v12 = v10.length;
      const v13 = v9;
      const v14 = v13;
      const v15 = v14;
      const v16 = Std_DHashMap_Internal_Raw__insert__at__test1_spec_1(
        v15,
        v10,
        v12,
      );
      const v17 = v16;
      const v18 = v17;
      const v19 = v18;
      const t$5$0 = v5;
      const t$5$1 = v6;
      const t$5$2 = v7;
      const t$5$3 = v11;
      const t$5$4 = v19;
      v5 = t$5$0;
      v6 = t$5$1;
      v7 = t$5$2;
      v8 = t$5$3;
      v9 = t$5$4;
      continue;
    }
  }
  return r$5;
};
const Std_DHashMap_Internal_Raw__Const_getD__at__test1_spec_0 = (
  v0,
  v1,
  v2,
) => {
  const v3 = v0;
  const v4 = v3._1;
  const v5 = v3._2;
  const v6 = v5.length;
  const v7 = $lean_string_hash(v1);
  const v8 = 32;
  const v9 = $lean_uint64_shift_right(v7, v8);
  const v10 = $lean_uint64_xor(v7, v9);
  const v11 = 16;
  const v12 = $lean_uint64_shift_right(v10, v11);
  const v13 = $lean_uint64_xor(v10, v12);
  const v14 = $lean_uint64_to_usize(v13);
  const v15 = $lean_usize_of_nat(v6);
  const v16 = 1;
  const v17 = v15 - v16;
  const v18 = $lean_usize_land(v14, v17);
  const v19 = $lean_array_uget(v5, v18);
  return Std_DHashMap_Internal_AssocList_getD__at__Std_DHashMap_Internal_Raw__Const_getD__at__test1_spec_0_spec_0(
    v1,
    v2,
    v19,
  );
};
const _private_Init_Data_Array_Basic_0_Array_foldrMUnsafe_fold__at__test6_spec_2 = (
  v0,
  v1,
  v2,
  v3,
) => {
  let v4 = v0, v5 = v1, v6 = v2, v7 = v3, c$4 = true, r$4;
  while (c$4) {
    const v8 = instDecidableEqUSize(v5, v6);
    const v9 = v8;
    if (v9) {
      c$4 = false;
      r$4 = v7;
      continue;
    } else {
      const v10 = 1;
      const v11 = v5 - v10;
      const v12 = $lean_array_uget(v4, v11);
      const v13 = Std_DHashMap_Internal_AssocList_foldrM__at__test6_spec_1(
        v7,
        v12,
      );
      const t$4$0 = v4;
      const t$4$1 = v11;
      const t$4$2 = v6;
      const t$4$3 = v13;
      v4 = t$4$0;
      v5 = t$4$1;
      v6 = t$4$2;
      v7 = t$4$3;
      continue;
    }
  }
  return r$4;
};
const List_mapTR_loop__at__test6_spec_0 = (v0, v1) => {
  let v2 = v0, v3 = v1, c$2 = true, r$2;
  while (c$2) {
    if (v2.tag === 0) {
      const v4 = List_reverse(v3);
      c$2 = false;
      r$2 = v4;
      continue;
    } else {
      const v4 = v2._1;
      const v5 = v2._2;
      const v6 = v4._1;
      const v7 = { tag: 1, _1: v6, _2: v3 };
      const t$2$0 = v5;
      const t$2$1 = v7;
      v2 = t$2$0;
      v3 = t$2$1;
      continue;
    }
  }
  return r$2;
};
const Std_DHashMap_Internal_Raw__erase__at__test5_spec_0 = (v0, v1) => {
  const v2 = v0;
  const v3 = v2._1;
  const v4 = v2._2;
  const v5 = v4.length;
  const v6 = $lean_string_hash(v1);
  const v7 = 32;
  const v8 = $lean_uint64_shift_right(v6, v7);
  const v9 = $lean_uint64_xor(v6, v8);
  const v10 = 16;
  const v11 = $lean_uint64_shift_right(v9, v10);
  const v12 = $lean_uint64_xor(v9, v11);
  const v13 = $lean_uint64_to_usize(v12);
  const v14 = $lean_usize_of_nat(v5);
  const v15 = 1;
  const v16 = v14 - v15;
  const v17 = $lean_usize_land(v13, v16);
  const v18 = $lean_array_uget(v4, v17);
  const v19 = Std_DHashMap_Internal_AssocList_contains__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_2(
    v1,
    v18,
  );
  if (v19) {
    const v20 = { tag: 0 };
    const v21 = $lean_array_uset(v4, v17, v20);
    const v22 = 1;
    const v23 = Math.max(0, v3 - v22);
    const v24 = Std_DHashMap_Internal_AssocList_erase__at__Std_DHashMap_Internal_Raw__erase__at__test5_spec_0_spec_0(
      v1,
      v18,
    );
    const v25 = $lean_array_uset(v21, v17, v24);
    return { tag: 0, _1: v23, _2: v25 };
  } else {
    return v2;
  }
};
const List_forIn__loop__at__test4_spec_0 = (v0, v1, v2, v3, v4) => {
  let v5 = v0, v6 = v1, v7 = v2, v8 = v3, v9 = v4, c$5 = true, r$5;
  while (c$5) {
    if (v8.tag === 0) {
      c$5 = false;
      r$5 = v9;
      continue;
    } else {
      const v10 = v8._1;
      const v11 = v8._2;
      const v12 = 1;
      const v13 = v9;
      const v14 = v13;
      const v15 = v14;
      const v16 = Std_DHashMap_Internal_Raw__insert__at__test1_spec_1(
        v15,
        v10,
        v12,
      );
      const v17 = v16;
      const v18 = v17;
      const v19 = v18;
      const t$5$0 = v5;
      const t$5$1 = v6;
      const t$5$2 = v7;
      const t$5$3 = v11;
      const t$5$4 = v19;
      v5 = t$5$0;
      v6 = t$5$1;
      v7 = t$5$2;
      v8 = t$5$3;
      v9 = t$5$4;
      continue;
    }
  }
  return r$5;
};
const List_forIn__loop__at__test4_spec_1 = (v0, v1, v2, v3, v4) => {
  let v5 = v0, v6 = v1, v7 = v2, v8 = v3, v9 = v4, c$5 = true, r$5;
  while (c$5) {
    if (v8.tag === 0) {
      c$5 = false;
      r$5 = v9;
      continue;
    } else {
      const v10 = v8._1;
      const v11 = v8._2;
      const v12 = "!";
      const v13 = v10 + v12;
      const v14 = v9;
      const v15 = { tag: 0 };
      const v16 = v14;
      const v17 = v16;
      const v18 = v17;
      const v19 = Std_DHashMap_Internal_Raw__insertIfNew__at__test3_spec_0(
        v18,
        v13,
        v15,
      );
      const v20 = v19;
      const v21 = v20;
      const v22 = v21;
      const v23 = v22;
      const t$5$0 = v5;
      const t$5$1 = v6;
      const t$5$2 = v7;
      const t$5$3 = v11;
      const t$5$4 = v23;
      v5 = t$5$0;
      v6 = t$5$1;
      v7 = t$5$2;
      v8 = t$5$3;
      v9 = t$5$4;
      continue;
    }
  }
  return r$5;
};
const Std_DHashMap_Internal_Raw__contains__at__test3_spec_2 = (v0, v1) => {
  const v2 = v0;
  const v3 = v2._1;
  const v4 = v2._2;
  const v5 = v4.length;
  const v6 = $lean_string_hash(v1);
  const v7 = 32;
  const v8 = $lean_uint64_shift_right(v6, v7);
  const v9 = $lean_uint64_xor(v6, v8);
  const v10 = 16;
  const v11 = $lean_uint64_shift_right(v9, v10);
  const v12 = $lean_uint64_xor(v9, v11);
  const v13 = $lean_uint64_to_usize(v12);
  const v14 = $lean_usize_of_nat(v5);
  const v15 = 1;
  const v16 = v14 - v15;
  const v17 = $lean_usize_land(v13, v16);
  const v18 = $lean_array_uget(v4, v17);
  return Std_DHashMap_Internal_AssocList_contains__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_2(
    v1,
    v18,
  );
};
const List_forIn__loop__at__test3_spec_1 = (v0, v1, v2, v3, v4) => {
  let v5 = v0, v6 = v1, v7 = v2, v8 = v3, v9 = v4, c$5 = true, r$5;
  while (c$5) {
    if (v8.tag === 0) {
      c$5 = false;
      r$5 = v9;
      continue;
    } else {
      const v10 = v8._1;
      const v11 = v8._2;
      const v12 = v9;
      const v13 = { tag: 0 };
      const v14 = v12;
      const v15 = v14;
      const v16 = v15;
      const v17 = Std_DHashMap_Internal_Raw__insertIfNew__at__test3_spec_0(
        v16,
        v10,
        v13,
      );
      const v18 = v17;
      const v19 = v18;
      const v20 = v19;
      const v21 = v20;
      const t$5$0 = v5;
      const t$5$1 = v6;
      const t$5$2 = v7;
      const t$5$3 = v11;
      const t$5$4 = v21;
      v5 = t$5$0;
      v6 = t$5$1;
      v7 = t$5$2;
      v8 = t$5$3;
      v9 = t$5$4;
      continue;
    }
  }
  return r$5;
};
const List_forIn__loop__at__test2_spec_1 = (v0, v1, v2, v3, v4) => {
  let v5 = v0, v6 = v1, v7 = v2, v8 = v3, v9 = v4, c$5 = true, r$5;
  while (c$5) {
    if (v8.tag === 0) {
      c$5 = false;
      r$5 = v9;
      continue;
    } else {
      const v10 = v8._1;
      const v11 = v8._2;
      const v12 = v10 * v10;
      const v13 = v9;
      const v14 = v13;
      const v15 = v14;
      const v16 = Std_DHashMap_Internal_Raw__insert__at__test2_spec_0(
        v15,
        v10,
        v12,
      );
      const v17 = v16;
      const v18 = v17;
      const v19 = v18;
      const t$5$0 = v5;
      const t$5$1 = v6;
      const t$5$2 = v7;
      const t$5$3 = v11;
      const t$5$4 = v19;
      v5 = t$5$0;
      v6 = t$5$1;
      v7 = t$5$2;
      v8 = t$5$3;
      v9 = t$5$4;
      continue;
    }
  }
  return r$5;
};
const Std_DHashMap_Internal_Raw__Const_get___at__test2_spec_2 = (v0, v1) => {
  const v2 = v0;
  const v3 = v2._1;
  const v4 = v2._2;
  const v5 = v4.length;
  const v6 = $lean_uint64_of_nat(v1);
  const v7 = 32;
  const v8 = $lean_uint64_shift_right(v6, v7);
  const v9 = $lean_uint64_xor(v6, v8);
  const v10 = 16;
  const v11 = $lean_uint64_shift_right(v9, v10);
  const v12 = $lean_uint64_xor(v9, v11);
  const v13 = $lean_uint64_to_usize(v12);
  const v14 = $lean_usize_of_nat(v5);
  const v15 = 1;
  const v16 = v14 - v15;
  const v17 = $lean_usize_land(v13, v16);
  const v18 = $lean_array_uget(v4, v17);
  return Std_DHashMap_Internal_AssocList_get___at__Std_DHashMap_Internal_Raw__Const_get___at__test2_spec_2_spec_5(
    v1,
    v18,
  );
};
const List_forIn__loop__at__test1_spec_2 = (v0, v1, v2, v3, v4) => {
  let v5 = v0, v6 = v1, v7 = v2, v8 = v3, v9 = v4, c$5 = true, r$5;
  while (c$5) {
    if (v8.tag === 0) {
      c$5 = false;
      r$5 = v9;
      continue;
    } else {
      const v10 = v8._1;
      const v11 = v8._2;
      const v12 = 0;
      const v13 = v9;
      const v14 = v13;
      const v15 = v14;
      const v16 = Std_DHashMap_Internal_Raw__Const_getD__at__test1_spec_0(
        v15,
        v10,
        v12,
      );
      const v17 = 1;
      const v18 = v16 + v17;
      const v19 = Std_DHashMap_Internal_Raw__insert__at__test1_spec_1(
        v15,
        v10,
        v18,
      );
      const v20 = v19;
      const v21 = v20;
      const v22 = v21;
      const t$5$0 = v5;
      const t$5$1 = v6;
      const t$5$2 = v7;
      const t$5$3 = v11;
      const t$5$4 = v22;
      v5 = t$5$0;
      v6 = t$5$1;
      v7 = t$5$2;
      v8 = t$5$3;
      v9 = t$5$4;
      continue;
    }
  }
  return r$5;
};
const test7 = (v0, v1) => {
  const v2 = instHashableString;
  const v3 = (v3, v4) => v3 === v4;
  const v4 = instBEqOfDecidableEq(v3);
  const v5 = 0;
  const v6 = 16;
  const v7 = { tag: 0 };
  const v8 = $lean_mk_array(v6, v7);
  const v9 = { tag: 0, _1: v5, _2: v8 };
  const v10 = v9;
  const v11 = v10;
  const v12 = List_forIn__loop__at__test7_spec_0(v4, v2, v0, v0, v11);
  const v13 = v12;
  const v14 = v13;
  const v15 = v14;
  return Std_DHashMap_Internal_Raw__Const_getD__at__test1_spec_0(v15, v1, v5);
};
const test6 = (v0) => {
  const v1 = instHashableString;
  const v2 = (v2, v3) => v2 === v3;
  const v3 = instBEqOfDecidableEq(v2);
  const v4 = 0;
  const v5 = 16;
  const v6 = { tag: 0 };
  const v7 = $lean_mk_array(v5, v6);
  const v8 = { tag: 0, _1: v4, _2: v7 };
  const v9 = v8;
  const v10 = v9;
  const v11 = List_forIn__loop__at__test4_spec_0(v3, v1, v0, v0, v10);
  const v12 = v11;
  const v13 = v12;
  const v14 = { tag: 0 };
  const v15 = v13._2;
  const v16 = v15.length;
  const v17 = v4 < v16;
  if (v17) {
    const v18 = $lean_usize_of_nat(v16);
    const v19 = 0;
    const v20 = _private_Init_Data_Array_Basic_0_Array_foldrMUnsafe_fold__at__test6_spec_2(
      v15,
      v18,
      v19,
      v14,
    );
    const v21 = v20;
    const v22 = { tag: 0 };
    return List_mapTR_loop__at__test6_spec_0(v21, v22);
  } else {
    const v18 = v14;
    const v19 = { tag: 0 };
    return List_mapTR_loop__at__test6_spec_0(v18, v19);
  }
};
const test5 = (v0) => {
  const v1 = instHashableString;
  const v2 = (v2, v3) => v2 === v3;
  const v3 = instBEqOfDecidableEq(v2);
  const v4 = 0;
  const v5 = 16;
  const v6 = { tag: 0 };
  const v7 = $lean_mk_array(v5, v6);
  const v8 = { tag: 0, _1: v4, _2: v7 };
  const v9 = v8;
  const v10 = v9;
  const v11 = List_forIn__loop__at__test4_spec_0(v3, v1, v0, v0, v10);
  const v12 = "a";
  const v13 = v11;
  const v14 = v13;
  const v15 = v14;
  const v16 = Std_DHashMap_Internal_Raw__erase__at__test5_spec_0(v15, v12);
  const v17 = v16;
  const v18 = "b";
  const v19 = Std_DHashMap_Internal_Raw__erase__at__test5_spec_0(v15, v18);
  const v20 = v19;
  const v21 = v17._1;
  const v22 = 100;
  const v23 = v21 * v22;
  const v24 = v20._1;
  return v23 + v24;
};
const test4 = (v0) => {
  const v1 = instHashableString;
  const v2 = (v2, v3) => v2 === v3;
  const v3 = instBEqOfDecidableEq(v2);
  const v4 = 0;
  const v5 = 16;
  const v6 = { tag: 0 };
  const v7 = $lean_mk_array(v5, v6);
  const v8 = { tag: 0, _1: v4, _2: v7 };
  const v9 = v8;
  const v10 = v9;
  const v11 = List_forIn__loop__at__test4_spec_0(v3, v1, v0, v0, v10);
  const v12 = { tag: 0 };
  const v13 = $lean_mk_array(v5, v12);
  const v14 = { tag: 0, _1: v4, _2: v13 };
  const v15 = v14;
  const v16 = v15;
  const v17 = v16;
  const v18 = List_forIn__loop__at__test4_spec_1(v3, v1, v0, v0, v17);
  const v19 = v11;
  const v20 = v19;
  const v21 = v20._1;
  const v22 = v18;
  const v23 = v22;
  const v24 = v23;
  const v25 = v24._1;
  return v21 + v25;
};
const test3 = (v0) => {
  const v1 = instHashableString;
  const v2 = (v2, v3) => v2 === v3;
  const v3 = instBEqOfDecidableEq(v2);
  const v4 = 0;
  const v5 = 16;
  const v6 = { tag: 0 };
  const v7 = $lean_mk_array(v5, v6);
  const v8 = { tag: 0, _1: v4, _2: v7 };
  const v9 = v8;
  const v10 = v9;
  const v11 = v10;
  const v12 = List_forIn__loop__at__test3_spec_1(v3, v1, v0, v0, v11);
  const v13 = v12;
  const v14 = v13;
  const v15 = v14;
  const v16 = v15._1;
  const v17 = "a";
  const v18 = v15;
  const v19 = Std_DHashMap_Internal_Raw__contains__at__test3_spec_2(v18, v17);
  if (v19) {
    const v20 = 1;
    return v16 + v20;
  } else {
    return v16;
  }
};
const test2 = (v0) => {
  const v1 = instHashableNat;
  const v2 = (v2, v3) => v2 === v3;
  const v3 = instBEqOfDecidableEq(v2);
  const v4 = 0;
  const v5 = 16;
  const v6 = { tag: 0 };
  const v7 = $lean_mk_array(v5, v6);
  const v8 = { tag: 0, _1: v4, _2: v7 };
  const v9 = v8;
  const v10 = v9;
  const v11 = List_forIn__loop__at__test2_spec_1(v3, v1, v0, v0, v10);
  const v12 = 3;
  const v13 = v11;
  const v14 = v13;
  const v15 = v14;
  return Std_DHashMap_Internal_Raw__Const_get___at__test2_spec_2(v15, v12);
};
const test1 = (v0) => {
  const v1 = instHashableString;
  const v2 = (v2, v3) => v2 === v3;
  const v3 = instBEqOfDecidableEq(v2);
  const v4 = 0;
  const v5 = 16;
  const v6 = { tag: 0 };
  const v7 = $lean_mk_array(v5, v6);
  const v8 = { tag: 0, _1: v4, _2: v7 };
  const v9 = v8;
  const v10 = v9;
  const v11 = List_forIn__loop__at__test1_spec_2(v3, v1, v0, v0, v10);
  const v12 = v11;
  const v13 = v12;
  return v13._1;
};
export { test7, test6, test5, test4, test3, test2, test1 };
