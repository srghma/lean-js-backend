export const span_go = (v0, v1, v2) => {
  let v3 = v0, v4 = v1, v5 = v2;
  while (true) {
    const v6 = v4.length;
    const v7 = v5 < v6;
    if (v7) {
      const v8 = v4[v5];
      const v9 = v3(v8);
      if (v9) {
        const v10 = v5 + 1;
        v5 = v10;
        continue;
      } else {
        return { tag: 1, _1: v5 };
      }
    } else {
      return { tag: 0 };
    }
  }
};
export const span = (v0, v1) => span_go(v0, v1, 0);
