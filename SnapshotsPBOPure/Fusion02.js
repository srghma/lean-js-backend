const toArrayLoop = (v0, v1, v2) => {
  let v3 = v0, v4 = v1, v5 = v2, c$3 = true, r$3;
  while (c$3) {
    const v6 = v3._2;
    const v7 = v6(v4);
    if (v7.tag === 0) {
      c$3 = false;
      r$3 = v5;
      continue;
    } else {
      const v8 = v7._1;
      const v9 = v8._1;
      const v10 = v8._2;
      const v11 = [...v5, v10];
      const t$3$0 = v3;
      const t$3$1 = v9;
      const t$3$2 = v11;
      v3 = t$3$0;
      v4 = t$3$1;
      v5 = t$3$2;
      continue;
    }
  }
  return r$3;
};
const toArray = (v0) => {
  const v1 = v0._1;
  const v2 = 0;
  const v3 = Array_mkEmpty(v2);
  return toArrayLoop(v0, v1, v3);
};
const test = (v0) => {
  const v1 = (v1) => {
    const v2 = v0.length;
    return Math.max(0, v2 - v1);
  };
  const v2 = (v2) => {
    const v3 = v0.length;
    const v4 = v2 < v3;
    if (v4) {
      const v5 = 1;
      const v6 = v2 + v5;
      const v7 = v0[v2];
      const v8 = v5;
      const v9 = v7 + v8;
      if (v9 < 0) {
        const v10 = -1 - v9;
        const v11 = "-";
        const v12 = v10 + 1;
        const v13 = Nat_reprFast(v12);
        const v14 = $lean_string_append(v11, v13);
        const v15 = v14;
        const v16 = { tag: 0, _1: v6, _2: v15 };
        return { tag: 1, _1: v16 };
      } else {
        const v10 = v9;
        const v11 = Nat_reprFast(v10);
        const v12 = v11;
        const v13 = { tag: 0, _1: v6, _2: v12 };
        return { tag: 1, _1: v13 };
      }
    } else {
      return { tag: 0 };
    }
  };
  const v3 = (v3) => {
    const v4 = "wat";
    const v5 = v3 === v4;
    const v6 = v5;
    if (v6) {
      return { tag: 0 };
    } else {
      return { tag: 1, _1: v3 };
    }
  };
  const v4 = 0;
  const v5 = (v5) => {
    const v6 = "1";
    const v7 = $lean_string_utf8_byte_size(v5);
    const v8 = $lean_string_utf8_byte_size(v6);
    const v9 = v8 <= v7;
    if (v9) {
      const v10 = v8;
      const v11 = v4;
      const v12 = $lean_string_memcmp(v5, v6, v11, v11, v10);
      if (v12) {
        const v13 = 1;
        const v14 = v11;
        const v15 = v7;
        const v16 = v15;
        const v17 = { tag: 0, _1: v5, _2: v14, _3: v16 };
        const v18 = v11;
        const v19 = String_Slice_Pos_nextn(v17, v18, v13);
        const v20 = v19;
        const v21 = v20;
        const v22 = v21;
        const v23 = v22;
        const v24 = { tag: 0, _1: v5, _2: v23, _3: v16 };
        const v25 = String_Slice_toString(v24);
        return { tag: 1, _1: v25 };
      } else {
        return { tag: 0 };
      }
    } else {
      return { tag: 0 };
    }
  };
  const v6 = { tag: 0, _1: v4, _2: v2, _3: v1 };
  const v7 = (v7) => {
    const v8 = filterMapStep(v6, v5, v7);
    if (v8.tag === 0) {
      return v8;
    } else {
      const v9 = v8._1;
      const v10 = v9._1;
      const v11 = v9._2;
      const v12 = "2";
      const v13 = v12 + v11;
      const v14 = { tag: 0, _1: v10, _2: v13 };
      return { tag: 1, _1: v14 };
    }
  };
  const v8 = { tag: 0, _1: v4, _2: v7, _3: v1 };
  const v9 = (v9) => {
    const v10 = filterMapStep(v8, v3, v9);
    if (v10.tag === 0) {
      return v10;
    } else {
      const v11 = v10._1;
      const v12 = v11._1;
      const v13 = v11._2;
      const v14 = "1";
      const v15 = v13 + v14;
      const v16 = { tag: 0, _1: v12, _2: v15 };
      return { tag: 1, _1: v16 };
    }
  };
  const v10 = { tag: 0, _1: v4, _2: v9, _3: v1 };
  const v11 = Array_mkEmpty(v4);
  return toArrayLoop(v10, v4, v11);
};
const overArray = (v0, v1) => {
  const v2 = (v2) => {
    const v3 = v1.length;
    const v4 = v2 < v3;
    if (v4) {
      const v5 = 1;
      const v6 = v2 + v5;
      const v7 = v1[v2];
      const v8 = { tag: 0, _1: v6, _2: v7 };
      return { tag: 1, _1: v8 };
    } else {
      return { tag: 0 };
    }
  };
  const v3 = (v3) => {
    const v4 = v1.length;
    return Math.max(0, v4 - v3);
  };
  const v4 = 0;
  const v5 = { tag: 0, _1: v4, _2: v2, _3: v3 };
  const v6 = v0(v5);
  const v7 = v6._1;
  const v8 = Array_mkEmpty(v4);
  return toArrayLoop(v6, v7, v8);
};
const mapU = (v0, v1) => {
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
const fromArray = (v0) => {
  const v1 = (v1) => {
    const v2 = v0.length;
    const v3 = v1 < v2;
    if (v3) {
      const v4 = 1;
      const v5 = v1 + v4;
      const v6 = v0[v1];
      const v7 = { tag: 0, _1: v5, _2: v6 };
      return { tag: 1, _1: v7 };
    } else {
      return { tag: 0 };
    }
  };
  const v2 = (v2) => {
    const v3 = v0.length;
    return Math.max(0, v3 - v2);
  };
  const v3 = 0;
  return { tag: 0, _1: v3, _2: v1, _3: v2 };
};
const filterU = (v0, v1) => {
  const v2 = (v2) => {
    const v3 = v0(v2);
    if (v3) {
      return { tag: 1, _1: v2 };
    } else {
      return { tag: 0 };
    }
  };
  const v3 = v1._1;
  const v4 = filterMapStep(v1, v2);
  const v5 = v1._3;
  return { tag: 0, _1: v3, _2: v4, _3: v5 };
};
const filterMapU = (v0, v1) => {
  const v2 = v1._1;
  const v3 = filterMapStep(v1, v0);
  const v4 = v1._3;
  return { tag: 0, _1: v2, _2: v3, _3: v4 };
};
const filterMapStep = (v0, v1, v2) => {
  let v3 = v0, v4 = v1, v5 = v2, c$3 = true, r$3;
  while (c$3) {
    const v6 = v3._2;
    const v7 = v6(v5);
    if (v7.tag === 0) {
      const v8 = { tag: 0 };
      c$3 = false;
      r$3 = v8;
      continue;
    } else {
      const v8 = v7._1;
      const v9 = v8._1;
      const v10 = v8._2;
      const v11 = v4(v10);
      if (v11.tag === 0) {
        const t$3$0 = v3;
        const t$3$1 = v4;
        const t$3$2 = v9;
        v3 = t$3$0;
        v4 = t$3$1;
        v5 = t$3$2;
        continue;
      } else {
        const v12 = v11._1;
        const v13 = { tag: 0, _1: v9, _2: v12 };
        const v14 = { tag: 1, _1: v13 };
        c$3 = false;
        r$3 = v14;
        continue;
      }
    }
  }
  return r$3;
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
  toArrayLoop,
  toArray,
  test,
  overArray,
  mapU,
  fromArray,
  filterU,
  filterMapU,
  filterMapStep,
  dropPrefix1,
};
