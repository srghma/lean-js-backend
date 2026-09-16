const _mut$testEven = (v0, v1, v2) => {
  let v3 = v0, v4 = v1, v5 = v2, c$3 = true, r$3;
  while (c$3) {
    if (v3 === 0) {
      if (v4 === 0) {
        c$3 = false;
        r$3 = v5;
        continue;
      } else {
        const v6 = Math.max(0, v4 - 1);
        const v7 = v5._1;
        const v8 = v5._2;
        const v9 = 1;
        const v10 = v9;
        const v11 = v8 + v10;
        const v12 = 2;
        const v13 = v12;
        const v14 = v7 + v13;
        const v15 = { tag: 0, _1: v11, _2: v14 };
        const t$3$0 = 1;
        const t$3$1 = v6;
        const t$3$2 = v15;
        v3 = t$3$0;
        v4 = t$3$1;
        v5 = t$3$2;
        continue;
      }
    } else {
      if (v4 === 0) {
        c$3 = false;
        r$3 = v5;
        continue;
      } else {
        const v6 = Math.max(0, v4 - 1);
        const v7 = v5._1;
        const v8 = v5._2;
        const v9 = 3;
        const v10 = v9;
        const v11 = v8 + v10;
        const v12 = 4;
        const v13 = v12;
        const v14 = v7 + v13;
        const v15 = { tag: 0, _1: v11, _2: v14 };
        const t$3$0 = 0;
        const t$3$1 = v6;
        const t$3$2 = v15;
        v3 = t$3$0;
        v4 = t$3$1;
        v5 = t$3$2;
        continue;
      }
    }
  }
  return r$3;
};
const testEven = (v0, v1) => _mut$testEven(0, v0, v1);
const testOdd = (v0, v1) => _mut$testEven(1, v0, v1);
const test5 = (v0) => {
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
const test4 = (v0) => {
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
const test3 = (v0) => (v1) => {
  const v2 = v0._1;
  return v2 + v1;
};
const test2 = (v0, v1) => {
  const v2 = v0._1;
  return v2 + v1;
};
const test1 = (v0, v1) => {
  const v2 = v0._1;
  return v2 + v1;
};
export { testEven, testOdd, test5, test4, test3, test2, test1 };
