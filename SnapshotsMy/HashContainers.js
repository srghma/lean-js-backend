import {
  $lean_array_fset,
  $lean_array_uget,
  $lean_array_uset,
  $lean_mk_array,
  $lean_string_hash,
  $lean_uint64_of_nat,
  $lean_uint64_shift_right,
  $lean_uint64_to_usize,
  $lean_uint64_xor,
  $lean_usize_land,
  $lean_usize_of_nat,
  $lean_usize_sub,
  List_reverse,
  instBEqOfDecidableEq,
  instDecidableEqUSize,
  instHashableNat,
  instHashableString,
} from "../runtime/lean_runtime.mjs";
const Std_DHashMap_Internal_AssocList_foldlM__at___private_Std_Data_DHashMap_Internal_Defs_0_Std_DHashMap_Internal_Raw__expand_go__at__Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_1_spec_2_spec_5 = (
  v0,
  v1,
) => {
  let v2 = v0, v3 = v1;
  while (true) {
    if (v3.tag === 0) {
      return v2;
    } else {
      const v4 = v3._1;
      const v5 = v3._2;
      const v6 = v3._3;
      const v7 = v2.length;
      const v8 = $lean_uint64_of_nat(v4);
      const v9 = $lean_uint64_shift_right(v8, 32);
      const v10 = $lean_uint64_xor(v8, v9);
      const v11 = $lean_uint64_shift_right(v10, 16);
      const v12 = $lean_uint64_xor(v10, v11);
      const v13 = $lean_uint64_to_usize(v12);
      const v14 = $lean_usize_of_nat(v7);
      const v15 = $lean_usize_sub(v14, 1);
      const v16 = $lean_usize_land(v13, v15);
      const v17 = $lean_array_uget(v2, v16);
      const v18 = { tag: 1, _1: v4, _2: v5, _3: v17 };
      const v19 = $lean_array_uset(v2, v16, v18);
      v2 = v19;
      v3 = v6;
      continue;
    }
  }
};
const Std_DHashMap_Internal_AssocList_foldlM__at___private_Std_Data_DHashMap_Internal_Defs_0_Std_DHashMap_Internal_Raw__expand_go__at__Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_3_spec_4_spec_6 = (
  v0,
  v1,
) => {
  let v2 = v0, v3 = v1;
  while (true) {
    if (v3.tag === 0) {
      return v2;
    } else {
      const v4 = v3._1;
      const v5 = v3._2;
      const v6 = v3._3;
      const v7 = v2.length;
      const v8 = $lean_string_hash(v4);
      const v9 = $lean_uint64_shift_right(v8, 32);
      const v10 = $lean_uint64_xor(v8, v9);
      const v11 = $lean_uint64_shift_right(v10, 16);
      const v12 = $lean_uint64_xor(v10, v11);
      const v13 = $lean_uint64_to_usize(v12);
      const v14 = $lean_usize_of_nat(v7);
      const v15 = $lean_usize_sub(v14, 1);
      const v16 = $lean_usize_land(v13, v15);
      const v17 = $lean_array_uget(v2, v16);
      const v18 = { tag: 1, _1: v4, _2: v5, _3: v17 };
      const v19 = $lean_array_uset(v2, v16, v18);
      v2 = v19;
      v3 = v6;
      continue;
    }
  }
};
const _private_Std_Data_DHashMap_Internal_Defs_0_Std_DHashMap_Internal_Raw__expand_go__at__Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_1_spec_2 = (
  v0,
  v1,
  v2,
) => {
  let v3 = v0, v4 = v1, v5 = v2;
  while (true) {
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
      const v12 = v3 + 1;
      v3 = v12;
      v4 = v10;
      v5 = v11;
      continue;
    } else {
      return v5;
    }
  }
};
const _private_Std_Data_DHashMap_Internal_Defs_0_Std_DHashMap_Internal_Raw__expand_go__at__Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_3_spec_4 = (
  v0,
  v1,
  v2,
) => {
  let v3 = v0, v4 = v1, v5 = v2;
  while (true) {
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
      const v12 = v3 + 1;
      v3 = v12;
      v4 = v10;
      v5 = v11;
      continue;
    } else {
      return v5;
    }
  }
};
const Std_DHashMap_Internal_AssocList_contains__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_0 = (
  v0,
  v1,
) => {
  let v2 = v0, v3 = v1;
  while (true) {
    if (v3.tag === 0) {
      return false;
    } else {
      const v4 = v3._1;
      const v5 = v3._3;
      const v6 = v4 === v2;
      if (v6) {
        return v6;
      } else {
        v3 = v5;
        continue;
      }
    }
  }
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
    if (v6) {
      return { tag: 1, _1: v0, _2: v1, _3: v5 };
    } else {
      const v7 = Std_DHashMap_Internal_AssocList_replace__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_2(
        v0,
        v1,
        v5,
      );
      return { tag: 1, _1: v3, _2: v4, _3: v7 };
    }
  }
};
const Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_1 = (
  v0,
) => {
  const v1 = v0.length;
  const v2 = v1 * 2;
  const v3 = { tag: 0 };
  const v4 = $lean_mk_array(v2, v3);
  return _private_Std_Data_DHashMap_Internal_Defs_0_Std_DHashMap_Internal_Raw__expand_go__at__Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_1_spec_2(
    0,
    v0,
    v4,
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
    if (v6) {
      return { tag: 1, _1: v0, _2: v1, _3: v5 };
    } else {
      const v7 = Std_DHashMap_Internal_AssocList_replace__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_4(
        v0,
        v1,
        v5,
      );
      return { tag: 1, _1: v3, _2: v4, _3: v7 };
    }
  }
};
const Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_3 = (
  v0,
) => {
  const v1 = v0.length;
  const v2 = v1 * 2;
  const v3 = { tag: 0 };
  const v4 = $lean_mk_array(v2, v3);
  return _private_Std_Data_DHashMap_Internal_Defs_0_Std_DHashMap_Internal_Raw__expand_go__at__Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_3_spec_4(
    0,
    v0,
    v4,
  );
};
const Std_DHashMap_Internal_AssocList_getD__at__Std_DHashMap_Internal_Raw__Const_getD__at__test1_spec_0_spec_0 = (
  v0,
  v1,
  v2,
) => {
  let v3 = v0, v4 = v1, v5 = v2;
  while (true) {
    if (v5.tag === 0) {
      return v4;
    } else {
      const v6 = v5._1;
      const v7 = v5._2;
      const v8 = v5._3;
      const v9 = v6 === v3;
      if (v9) {
        return v7;
      } else {
        v5 = v8;
        continue;
      }
    }
  }
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
    if (v5) {
      return v4;
    } else {
      const v6 = Std_DHashMap_Internal_AssocList_erase__at__Std_DHashMap_Internal_Raw__erase__at__test5_spec_0_spec_0(
        v0,
        v4,
      );
      return { tag: 1, _1: v2, _2: v3, _3: v6 };
    }
  }
};
const Std_DHashMap_Internal_AssocList_contains__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_2 = (
  v0,
  v1,
) => {
  let v2 = v0, v3 = v1;
  while (true) {
    if (v3.tag === 0) {
      return false;
    } else {
      const v4 = v3._1;
      const v5 = v3._3;
      const v6 = v4 === v2;
      if (v6) {
        return v6;
      } else {
        v3 = v5;
        continue;
      }
    }
  }
};
const Std_DHashMap_Internal_Raw__insertIfNew__at__test3_spec_0 = (
  v0,
  v1,
  v2,
) => {
  const v3 = v0._1;
  const v4 = v0._2;
  const v5 = v4.length;
  const v6 = $lean_string_hash(v1);
  const v7 = $lean_uint64_shift_right(v6, 32);
  const v8 = $lean_uint64_xor(v6, v7);
  const v9 = $lean_uint64_shift_right(v8, 16);
  const v10 = $lean_uint64_xor(v8, v9);
  const v11 = $lean_uint64_to_usize(v10);
  const v12 = $lean_usize_of_nat(v5);
  const v13 = $lean_usize_sub(v12, 1);
  const v14 = $lean_usize_land(v11, v13);
  const v15 = $lean_array_uget(v4, v14);
  const v16 = Std_DHashMap_Internal_AssocList_contains__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_2(
    v1,
    v15,
  );
  if (v16) {
    return v0;
  } else {
    const v17 = v3 + 1;
    const v18 = { tag: 1, _1: v1, _2: v2, _3: v15 };
    const v19 = $lean_array_uset(v4, v14, v18);
    const v20 = v17 * 4;
    const v21 = Math.trunc(v20 / 3);
    const v22 = v19.length;
    const v23 = v21 <= v22;
    if (v23) {
      return { tag: 0, _1: v17, _2: v19 };
    } else {
      const v24 = Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_3(
        v19,
      );
      return { tag: 0, _1: v17, _2: v24 };
    }
  }
};
const Std_DHashMap_Internal_Raw__insert__at__test2_spec_0 = (v0, v1, v2) => {
  const v3 = v0._1;
  const v4 = v0._2;
  const v5 = v4.length;
  const v6 = $lean_uint64_of_nat(v1);
  const v7 = $lean_uint64_shift_right(v6, 32);
  const v8 = $lean_uint64_xor(v6, v7);
  const v9 = $lean_uint64_shift_right(v8, 16);
  const v10 = $lean_uint64_xor(v8, v9);
  const v11 = $lean_uint64_to_usize(v10);
  const v12 = $lean_usize_of_nat(v5);
  const v13 = $lean_usize_sub(v12, 1);
  const v14 = $lean_usize_land(v11, v13);
  const v15 = $lean_array_uget(v4, v14);
  const v16 = Std_DHashMap_Internal_AssocList_contains__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_0(
    v1,
    v15,
  );
  if (v16) {
    const v17 = { tag: 0 };
    const v18 = $lean_array_uset(v4, v14, v17);
    const v19 = Std_DHashMap_Internal_AssocList_replace__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_2(
      v1,
      v2,
      v15,
    );
    const v20 = $lean_array_uset(v18, v14, v19);
    return { tag: 0, _1: v3, _2: v20 };
  } else {
    const v17 = v3 + 1;
    const v18 = { tag: 1, _1: v1, _2: v2, _3: v15 };
    const v19 = $lean_array_uset(v4, v14, v18);
    const v20 = v17 * 4;
    const v21 = Math.trunc(v20 / 3);
    const v22 = v19.length;
    const v23 = v21 <= v22;
    if (v23) {
      return { tag: 0, _1: v17, _2: v19 };
    } else {
      const v24 = Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test2_spec_0_spec_1(
        v19,
      );
      return { tag: 0, _1: v17, _2: v24 };
    }
  }
};
const Std_DHashMap_Internal_AssocList_get___at__Std_DHashMap_Internal_Raw__Const_get___at__test2_spec_2_spec_5 = (
  v0,
  v1,
) => {
  let v2 = v0, v3 = v1;
  while (true) {
    if (v3.tag === 0) {
      return { tag: 0 };
    } else {
      const v4 = v3._1;
      const v5 = v3._2;
      const v6 = v3._3;
      const v7 = v4 === v2;
      if (v7) {
        return { tag: 1, _1: v5 };
      } else {
        v3 = v6;
        continue;
      }
    }
  }
};
const Std_DHashMap_Internal_Raw__insert__at__test1_spec_1 = (v0, v1, v2) => {
  const v3 = v0._1;
  const v4 = v0._2;
  const v5 = v4.length;
  const v6 = $lean_string_hash(v1);
  const v7 = $lean_uint64_shift_right(v6, 32);
  const v8 = $lean_uint64_xor(v6, v7);
  const v9 = $lean_uint64_shift_right(v8, 16);
  const v10 = $lean_uint64_xor(v8, v9);
  const v11 = $lean_uint64_to_usize(v10);
  const v12 = $lean_usize_of_nat(v5);
  const v13 = $lean_usize_sub(v12, 1);
  const v14 = $lean_usize_land(v11, v13);
  const v15 = $lean_array_uget(v4, v14);
  const v16 = Std_DHashMap_Internal_AssocList_contains__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_2(
    v1,
    v15,
  );
  if (v16) {
    const v17 = { tag: 0 };
    const v18 = $lean_array_uset(v4, v14, v17);
    const v19 = Std_DHashMap_Internal_AssocList_replace__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_4(
      v1,
      v2,
      v15,
    );
    const v20 = $lean_array_uset(v18, v14, v19);
    return { tag: 0, _1: v3, _2: v20 };
  } else {
    const v17 = v3 + 1;
    const v18 = { tag: 1, _1: v1, _2: v2, _3: v15 };
    const v19 = $lean_array_uset(v4, v14, v18);
    const v20 = v17 * 4;
    const v21 = Math.trunc(v20 / 3);
    const v22 = v19.length;
    const v23 = v21 <= v22;
    if (v23) {
      return { tag: 0, _1: v17, _2: v19 };
    } else {
      const v24 = Std_DHashMap_Internal_Raw__expand__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_3(
        v19,
      );
      return { tag: 0, _1: v17, _2: v24 };
    }
  }
};
const List_forIn__loop__at__test7_spec_0 = (v0, v1, v2, v3, v4) => {
  let v5 = v0, v6 = v1, v7 = v2, v8 = v3, v9 = v4;
  while (true) {
    if (v8.tag === 0) {
      return v9;
    } else {
      const v10 = v8._1;
      const v11 = v8._2;
      const v12 = v10.length;
      const v13 = Std_DHashMap_Internal_Raw__insert__at__test1_spec_1(
        v9,
        v10,
        v12,
      );
      v8 = v11;
      v9 = v13;
      continue;
    }
  }
};
const Std_DHashMap_Internal_Raw__Const_getD__at__test1_spec_0 = (
  v0,
  v1,
  v2,
) => {
  const v3 = v0._2;
  const v4 = v3.length;
  const v5 = $lean_string_hash(v1);
  const v6 = $lean_uint64_shift_right(v5, 32);
  const v7 = $lean_uint64_xor(v5, v6);
  const v8 = $lean_uint64_shift_right(v7, 16);
  const v9 = $lean_uint64_xor(v7, v8);
  const v10 = $lean_uint64_to_usize(v9);
  const v11 = $lean_usize_of_nat(v4);
  const v12 = $lean_usize_sub(v11, 1);
  const v13 = $lean_usize_land(v10, v12);
  const v14 = $lean_array_uget(v3, v13);
  return Std_DHashMap_Internal_AssocList_getD__at__Std_DHashMap_Internal_Raw__Const_getD__at__test1_spec_0_spec_0(
    v1,
    v2,
    v14,
  );
};
const _private_Init_Data_Array_Basic_0_Array_foldrMUnsafe_fold__at__test6_spec_2 = (
  v0,
  v1,
  v2,
  v3,
) => {
  let v4 = v0, v5 = v1, v6 = v2, v7 = v3;
  while (true) {
    const v8 = instDecidableEqUSize(v5, v6);
    if (v8) {
      return v7;
    } else {
      const v9 = $lean_usize_sub(v5, 1);
      const v10 = $lean_array_uget(v4, v9);
      const v11 = Std_DHashMap_Internal_AssocList_foldrM__at__test6_spec_1(
        v7,
        v10,
      );
      v5 = v9;
      v7 = v11;
      continue;
    }
  }
};
const List_mapTR_loop__at__test6_spec_0 = (v0, v1) => {
  let v2 = v0, v3 = v1;
  while (true) {
    if (v2.tag === 0) {
      const v4 = List_reverse(v3);
      return v4;
    } else {
      const v4 = v2._1;
      const v5 = v2._2;
      const v6 = v4._1;
      v2 = v5;
      v3 = { tag: 1, _1: v6, _2: v3 };
      continue;
    }
  }
};
const Std_DHashMap_Internal_Raw__erase__at__test5_spec_0 = (v0, v1) => {
  const v2 = v0._1;
  const v3 = v0._2;
  const v4 = v3.length;
  const v5 = $lean_string_hash(v1);
  const v6 = $lean_uint64_shift_right(v5, 32);
  const v7 = $lean_uint64_xor(v5, v6);
  const v8 = $lean_uint64_shift_right(v7, 16);
  const v9 = $lean_uint64_xor(v7, v8);
  const v10 = $lean_uint64_to_usize(v9);
  const v11 = $lean_usize_of_nat(v4);
  const v12 = $lean_usize_sub(v11, 1);
  const v13 = $lean_usize_land(v10, v12);
  const v14 = $lean_array_uget(v3, v13);
  const v15 = Std_DHashMap_Internal_AssocList_contains__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_2(
    v1,
    v14,
  );
  if (v15) {
    const v16 = { tag: 0 };
    const v17 = $lean_array_uset(v3, v13, v16);
    const v18 = Math.max(0, v2 - 1);
    const v19 = Std_DHashMap_Internal_AssocList_erase__at__Std_DHashMap_Internal_Raw__erase__at__test5_spec_0_spec_0(
      v1,
      v14,
    );
    const v20 = $lean_array_uset(v17, v13, v19);
    return { tag: 0, _1: v18, _2: v20 };
  } else {
    return v0;
  }
};
const List_forIn__loop__at__test4_spec_0 = (v0, v1, v2, v3, v4) => {
  let v5 = v0, v6 = v1, v7 = v2, v8 = v3, v9 = v4;
  while (true) {
    if (v8.tag === 0) {
      return v9;
    } else {
      const v10 = v8._1;
      const v11 = v8._2;
      const v12 = Std_DHashMap_Internal_Raw__insert__at__test1_spec_1(
        v9,
        v10,
        1,
      );
      v8 = v11;
      v9 = v12;
      continue;
    }
  }
};
const List_forIn__loop__at__test4_spec_1 = (v0, v1, v2, v3, v4) => {
  let v5 = v0, v6 = v1, v7 = v2, v8 = v3, v9 = v4;
  while (true) {
    if (v8.tag === 0) {
      return v9;
    } else {
      const v10 = v8._1;
      const v11 = v8._2;
      const v12 = v10 + "!";
      const v13 = 0;
      const v14 = Std_DHashMap_Internal_Raw__insertIfNew__at__test3_spec_0(
        v9,
        v12,
        v13,
      );
      v8 = v11;
      v9 = v14;
      continue;
    }
  }
};
const Std_DHashMap_Internal_Raw__contains__at__test3_spec_2 = (v0, v1) => {
  const v2 = v0._2;
  const v3 = v2.length;
  const v4 = $lean_string_hash(v1);
  const v5 = $lean_uint64_shift_right(v4, 32);
  const v6 = $lean_uint64_xor(v4, v5);
  const v7 = $lean_uint64_shift_right(v6, 16);
  const v8 = $lean_uint64_xor(v6, v7);
  const v9 = $lean_uint64_to_usize(v8);
  const v10 = $lean_usize_of_nat(v3);
  const v11 = $lean_usize_sub(v10, 1);
  const v12 = $lean_usize_land(v9, v11);
  const v13 = $lean_array_uget(v2, v12);
  return Std_DHashMap_Internal_AssocList_contains__at__Std_DHashMap_Internal_Raw__insert__at__test1_spec_1_spec_2(
    v1,
    v13,
  );
};
const List_forIn__loop__at__test3_spec_1 = (v0, v1, v2, v3, v4) => {
  let v5 = v0, v6 = v1, v7 = v2, v8 = v3, v9 = v4;
  while (true) {
    if (v8.tag === 0) {
      return v9;
    } else {
      const v10 = v8._1;
      const v11 = v8._2;
      const v12 = 0;
      const v13 = Std_DHashMap_Internal_Raw__insertIfNew__at__test3_spec_0(
        v9,
        v10,
        v12,
      );
      v8 = v11;
      v9 = v13;
      continue;
    }
  }
};
const List_forIn__loop__at__test2_spec_1 = (v0, v1, v2, v3, v4) => {
  let v5 = v0, v6 = v1, v7 = v2, v8 = v3, v9 = v4;
  while (true) {
    if (v8.tag === 0) {
      return v9;
    } else {
      const v10 = v8._1;
      const v11 = v8._2;
      const v12 = v10 * v10;
      const v13 = Std_DHashMap_Internal_Raw__insert__at__test2_spec_0(
        v9,
        v10,
        v12,
      );
      v8 = v11;
      v9 = v13;
      continue;
    }
  }
};
const Std_DHashMap_Internal_Raw__Const_get___at__test2_spec_2 = (v0, v1) => {
  const v2 = v0._2;
  const v3 = v2.length;
  const v4 = $lean_uint64_of_nat(v1);
  const v5 = $lean_uint64_shift_right(v4, 32);
  const v6 = $lean_uint64_xor(v4, v5);
  const v7 = $lean_uint64_shift_right(v6, 16);
  const v8 = $lean_uint64_xor(v6, v7);
  const v9 = $lean_uint64_to_usize(v8);
  const v10 = $lean_usize_of_nat(v3);
  const v11 = $lean_usize_sub(v10, 1);
  const v12 = $lean_usize_land(v9, v11);
  const v13 = $lean_array_uget(v2, v12);
  return Std_DHashMap_Internal_AssocList_get___at__Std_DHashMap_Internal_Raw__Const_get___at__test2_spec_2_spec_5(
    v1,
    v13,
  );
};
const List_forIn__loop__at__test1_spec_2 = (v0, v1, v2, v3, v4) => {
  let v5 = v0, v6 = v1, v7 = v2, v8 = v3, v9 = v4;
  while (true) {
    if (v8.tag === 0) {
      return v9;
    } else {
      const v10 = v8._1;
      const v11 = v8._2;
      const v12 = Std_DHashMap_Internal_Raw__Const_getD__at__test1_spec_0(
        v9,
        v10,
        0,
      );
      const v13 = v12 + 1;
      const v14 = Std_DHashMap_Internal_Raw__insert__at__test1_spec_1(
        v9,
        v10,
        v13,
      );
      v8 = v11;
      v9 = v14;
      continue;
    }
  }
};
export const test7 = (v0, v1) => {
  const v2 = instBEqOfDecidableEq((v2, v3) => v2 === v3);
  const v3 = { tag: 0 };
  const v4 = $lean_mk_array(16, v3);
  const v5 = { tag: 0, _1: 0, _2: v4 };
  const v6 = List_forIn__loop__at__test7_spec_0(
    v2,
    instHashableString,
    v0,
    v0,
    v5,
  );
  return Std_DHashMap_Internal_Raw__Const_getD__at__test1_spec_0(v6, v1, 0);
};
export const test6 = (v0) => {
  const v1 = instBEqOfDecidableEq((v1, v2) => v1 === v2);
  const v2 = { tag: 0 };
  const v3 = $lean_mk_array(16, v2);
  const v4 = { tag: 0, _1: 0, _2: v3 };
  const v5 = List_forIn__loop__at__test4_spec_0(
    v1,
    instHashableString,
    v0,
    v0,
    v4,
  );
  const v6 = { tag: 0 };
  const v7 = v5._2;
  const v8 = v7.length;
  const v9 = 0 < v8;
  if (v9) {
    const v10 = $lean_usize_of_nat(v8);
    const v11 = _private_Init_Data_Array_Basic_0_Array_foldrMUnsafe_fold__at__test6_spec_2(
      v7,
      v10,
      0,
      v6,
    );
    const v12 = { tag: 0 };
    return List_mapTR_loop__at__test6_spec_0(v11, v12);
  } else {
    const v10 = { tag: 0 };
    return List_mapTR_loop__at__test6_spec_0(v6, v10);
  }
};
export const test5 = (v0) => {
  const v1 = instBEqOfDecidableEq((v1, v2) => v1 === v2);
  const v2 = { tag: 0 };
  const v3 = $lean_mk_array(16, v2);
  const v4 = { tag: 0, _1: 0, _2: v3 };
  const v5 = List_forIn__loop__at__test4_spec_0(
    v1,
    instHashableString,
    v0,
    v0,
    v4,
  );
  const v6 = Std_DHashMap_Internal_Raw__erase__at__test5_spec_0(v5, "a");
  const v7 = Std_DHashMap_Internal_Raw__erase__at__test5_spec_0(v5, "b");
  const v8 = v6._1;
  const v9 = v8 * 100;
  const v10 = v7._1;
  return v9 + v10;
};
export const test4 = (v0) => {
  const v1 = instBEqOfDecidableEq((v1, v2) => v1 === v2);
  const v2 = { tag: 0 };
  const v3 = $lean_mk_array(16, v2);
  const v4 = { tag: 0, _1: 0, _2: v3 };
  const v5 = List_forIn__loop__at__test4_spec_0(
    v1,
    instHashableString,
    v0,
    v0,
    v4,
  );
  const v6 = { tag: 0 };
  const v7 = $lean_mk_array(16, v6);
  const v8 = { tag: 0, _1: 0, _2: v7 };
  const v9 = List_forIn__loop__at__test4_spec_1(
    v1,
    instHashableString,
    v0,
    v0,
    v8,
  );
  const v10 = v5._1;
  const v11 = v9._1;
  return v10 + v11;
};
export const test3 = (v0) => {
  const v1 = instBEqOfDecidableEq((v1, v2) => v1 === v2);
  const v2 = { tag: 0 };
  const v3 = $lean_mk_array(16, v2);
  const v4 = { tag: 0, _1: 0, _2: v3 };
  const v5 = List_forIn__loop__at__test3_spec_1(
    v1,
    instHashableString,
    v0,
    v0,
    v4,
  );
  const v6 = v5._1;
  const v7 = Std_DHashMap_Internal_Raw__contains__at__test3_spec_2(v5, "a");
  if (v7) {
    return v6 + 1;
  } else {
    return v6;
  }
};
export const test2 = (v0) => {
  const v1 = instBEqOfDecidableEq((v1, v2) => v1 === v2);
  const v2 = { tag: 0 };
  const v3 = $lean_mk_array(16, v2);
  const v4 = { tag: 0, _1: 0, _2: v3 };
  const v5 = List_forIn__loop__at__test2_spec_1(
    v1,
    instHashableNat,
    v0,
    v0,
    v4,
  );
  return Std_DHashMap_Internal_Raw__Const_get___at__test2_spec_2(v5, 3);
};
export const test1 = (v0) => {
  const v1 = instBEqOfDecidableEq((v1, v2) => v1 === v2);
  const v2 = { tag: 0 };
  const v3 = $lean_mk_array(16, v2);
  const v4 = { tag: 0, _1: 0, _2: v3 };
  const v5 = List_forIn__loop__at__test1_spec_2(
    v1,
    instHashableString,
    v0,
    v0,
    v4,
  );
  return v5._1;
};
