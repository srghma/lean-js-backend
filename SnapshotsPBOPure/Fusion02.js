import {
  $lean_string_memcmp,
  Nat_reprFast,
  String_Slice_Pos_nextn,
  String_Slice_toString,
} from "../runtime/lean_runtime_non_configurable.mjs";
import {
  $lean_string_utf8_byte_size,
} from "../runtime/lean_runtime_nat_num.mjs";
export const toArrayLoop = (v0, v1, v2) => {
  let v3 = v0, v4 = v1, v5 = v2;
  while (true) {
    const v6 = v3._2;
    const v7 = v6(v4);
    if (v7.tag === 0) {
      return v5;
    } else {
      const v8 = v7._1;
      const v9 = v8._1;
      const v10 = v8._2;
      const v11 = [...v5, v10];
      v4 = v9;
      v5 = v11;
      continue;
    }
  }
};
export const toArray = (v0) => {
  const v1 = v0._1;
  const v2 = [];
  let v3 = v0, v4 = v1, v5 = v2;
  while (true) {
    const v6 = v3._2;
    const v7 = v6(v4);
    if (v7.tag === 0) {
      return v5;
    } else {
      const v8 = v7._1;
      const v9 = v8._1;
      const v10 = v8._2;
      const v11 = [...v5, v10];
      v4 = v9;
      v5 = v11;
      continue;
    }
  }
};
export const overArray = (v0, v1) => {
  const v2 = (v2) => {
    const v3 = v1.length;
    const v4 = v2 < v3;
    if (v4) {
      const v5 = v2 + 1;
      const v6 = v1[v2];
      const v7 = { tag: 0, _1: v5, _2: v6 };
      return { tag: 1, _1: v7 };
    } else {
      return { tag: 0 };
    }
  };
  const v3 = (v3) => {
    const v4 = v1.length;
    return Math.max(0, v4 - v3);
  };
  const v4 = { tag: 0, _1: 0, _2: v2, _3: v3 };
  const v5 = v0(v4);
  const v6 = v5._1;
  const v7 = [];
  let v8 = v5, v9 = v6, v10 = v7;
  while (true) {
    const v11 = v8._2;
    const v12 = v11(v9);
    if (v12.tag === 0) {
      return v10;
    } else {
      const v13 = v12._1;
      const v14 = v13._1;
      const v15 = v13._2;
      const v16 = [...v10, v15];
      v9 = v14;
      v10 = v16;
      continue;
    }
  }
};
export const mapU = (v0, v1) => {
  const v2 = (v2) => {
    const v3 = v1._2;
    const v4 = v3(v2);
    if (v4.tag === 0) {
      return { tag: 0 };
    } else {
      const v5 = v4._1;
      const v6 = v5._1;
      const v7 = v5._2;
      const v8 = v0(v7);
      const v9 = { tag: 0, _1: v6, _2: v8 };
      return { tag: 1, _1: v9 };
    }
  };
  const v3 = v1._1;
  const v4 = v1._3;
  return { tag: 0, _1: v3, _2: v2, _3: v4 };
};
export const fromArray = (v0) => {
  const v1 = (v1) => {
    const v2 = v0.length;
    const v3 = v1 < v2;
    if (v3) {
      const v4 = v1 + 1;
      const v5 = v0[v1];
      const v6 = { tag: 0, _1: v4, _2: v5 };
      return { tag: 1, _1: v6 };
    } else {
      return { tag: 0 };
    }
  };
  const v2 = (v2) => {
    const v3 = v0.length;
    return Math.max(0, v3 - v2);
  };
  return { tag: 0, _1: 0, _2: v1, _3: v2 };
};
export const filterU = (v0, v1) => {
  const v2 = (v2) => {
    const v3 = v0(v2);
    if (v3) {
      return { tag: 1, _1: v2 };
    } else {
      return { tag: 0 };
    }
  };
  const v3 = v1._1;
  const v4 = (v4) => {
    let v5 = v1, v6 = v2, v7 = v4;
    while (true) {
      const v8 = v5._2;
      const v9 = v8(v7);
      if (v9.tag === 0) {
        return { tag: 0 };
      } else {
        const v10 = v9._1;
        const v11 = v10._1;
        const v12 = v10._2;
        const v13 = v6(v12);
        if (v13.tag === 0) {
          v7 = v11;
          continue;
        } else {
          const v14 = v13._1;
          return { tag: 1, _1: { tag: 0, _1: v11, _2: v14 } };
        }
      }
    }
  };
  const v5 = v1._3;
  return { tag: 0, _1: v3, _2: v4, _3: v5 };
};
export const filterMapU = (v0, v1) => {
  const v2 = v1._1;
  const v3 = (v3) => {
    let v4 = v1, v5 = v0, v6 = v3;
    while (true) {
      const v7 = v4._2;
      const v8 = v7(v6);
      if (v8.tag === 0) {
        return { tag: 0 };
      } else {
        const v9 = v8._1;
        const v10 = v9._1;
        const v11 = v9._2;
        const v12 = v5(v11);
        if (v12.tag === 0) {
          v6 = v10;
          continue;
        } else {
          const v13 = v12._1;
          return { tag: 1, _1: { tag: 0, _1: v10, _2: v13 } };
        }
      }
    }
  };
  const v4 = v1._3;
  return { tag: 0, _1: v2, _2: v3, _3: v4 };
};
export const filterMapStep = (v0, v1, v2) => {
  let v3 = v0, v4 = v1, v5 = v2;
  while (true) {
    const v6 = v3._2;
    const v7 = v6(v5);
    if (v7.tag === 0) {
      return { tag: 0 };
    } else {
      const v8 = v7._1;
      const v9 = v8._1;
      const v10 = v8._2;
      const v11 = v4(v10);
      if (v11.tag === 0) {
        v5 = v9;
        continue;
      } else {
        const v12 = v11._1;
        return { tag: 1, _1: { tag: 0, _1: v9, _2: v12 } };
      }
    }
  }
};
export const test = (v0) => {
  const v1 = (v1) => {
    const v2 = v0.length;
    return Math.max(0, v2 - v1);
  };
  const v2 = (v2) => {
    const v3 = v0.length;
    const v4 = v2 < v3;
    if (v4) {
      const v5 = v2 + 1;
      const v6 = v0[v2];
      const v7 = v6 + 1;
      if (v7 < 0) {
        const v8 = -1 - v7;
        const v9 = v8 + 1;
        const v10 = Nat_reprFast(v9);
        const v11 = "-" + v10;
        const v12 = { tag: 0, _1: v5, _2: v11 };
        return { tag: 1, _1: v12 };
      } else {
        const v8 = Nat_reprFast(v7);
        const v9 = { tag: 0, _1: v5, _2: v8 };
        return { tag: 1, _1: v9 };
      }
    } else {
      return { tag: 0 };
    }
  };
  const v3 = (v3) => {
    const v4 = v3 === "wat";
    if (v4) {
      return { tag: 0 };
    } else {
      return { tag: 1, _1: v3 };
    }
  };
  const v4 = (v4) => {
    const v5 = $lean_string_utf8_byte_size(v4);
    const v6 = $lean_string_utf8_byte_size("1");
    const v7 = v6 <= v5;
    if (v7) {
      const v8 = $lean_string_memcmp(v4, "1", 0, 0, v6);
      if (v8) {
        const v9 = { tag: 0, _1: v4, _2: 0, _3: v5 };
        const v10 = String_Slice_Pos_nextn(v9, 0, 1);
        const v11 = { tag: 0, _1: v4, _2: v10, _3: v5 };
        const v12 = String_Slice_toString(v11);
        return { tag: 1, _1: v12 };
      } else {
        return { tag: 0 };
      }
    } else {
      return { tag: 0 };
    }
  };
  const v5 = { tag: 0, _1: 0, _2: v2, _3: v1 };
  const v6 = (v6) => {
    const v7 = filterMapStep(v5, v4, v6);
    if (v7.tag === 0) {
      return v7;
    } else {
      const v8 = v7._1;
      const v9 = v8._1;
      const v10 = v8._2;
      const v11 = "2" + v10;
      const v12 = { tag: 0, _1: v9, _2: v11 };
      return { tag: 1, _1: v12 };
    }
  };
  const v7 = { tag: 0, _1: 0, _2: v6, _3: v1 };
  const v8 = (v8) => {
    const v9 = filterMapStep(v7, v3, v8);
    if (v9.tag === 0) {
      return v9;
    } else {
      const v10 = v9._1;
      const v11 = v10._1;
      const v12 = v10._2;
      const v13 = v12 + "1";
      const v14 = { tag: 0, _1: v11, _2: v13 };
      return { tag: 1, _1: v14 };
    }
  };
  const v9 = { tag: 0, _1: 0, _2: v8, _3: v1 };
  const v10 = [];
  return toArrayLoop(v9, 0, v10);
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
