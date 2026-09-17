const _spec$testEven = (v0, v1) => {
  let v2 = v0, v3 = v1._1, v4 = v1._2;
  while (true) {
    if (v2 === 0) {
      return { tag: 0, _1: v3, _2: v4 };
    } else {
      const v5 = v2 - 1;
      const v6 = v4 + 1;
      const v7 = v3 + 2;
      if (v5 === 0) {
        return { tag: 0, _1: v6, _2: v7 };
      } else {
        const v8 = v5 - 1;
        const v9 = v7 + 3;
        const v10 = v6 + 4;
        v2 = v8;
        v3 = v9;
        v4 = v10;
        continue;
      }
    }
  }
};
export const testEven = _spec$testEven;
export const testOdd = (v0, v1) => {
  if (v0 === 0) {
    return v1;
  } else {
    const v2 = v0 - 1;
    const v3 = v1._1;
    const v4 = v1._2;
    const v5 = v4 + 3;
    const v6 = v3 + 4;
    const v7 = { tag: 0, _1: v5, _2: v6 };
    return _spec$testEven(v2, v7);
  }
};
export const test5 = (v0) => {
  const v1 = (v1) => {
    const v2 = v0._1;
    return v2 + v1;
  };
  const v2 = (v2) => {
    const v3 = v0._2;
    return v3 + v2;
  };
  return { tag: 0, _1: v1, _2: v2 };
};
export const test4 = (v0) => {
  const v1 = (v1) => {
    const v2 = v0._1;
    return v2 + v1;
  };
  const v2 = (v2) => {
    const v3 = v0._2;
    return v3 + v2;
  };
  return { tag: 0, _1: v1, _2: v2 };
};
export const test3 = (v0) => (v1) => {
  const v2 = v0._1;
  return v2 + v1;
};
export const test2 = (v0, v1) => {
  const v2 = v0._1;
  return v2 + v1;
};
export const test1 = (v0, v1) => {
  const v2 = v0._1;
  return v2 + v1;
};
