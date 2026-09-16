const span_go = (v0, v1, v2) => {
  let v3 = v0, v4 = v1, v5 = v2, c$3 = true, r$3;
  while (c$3) {
    const v6 = v4.length;
    const v7 = v5 < v6;
    if (v7) {
      const v8 = v4[v5];
      const v9 = v3(v8);
      if (v9) {
        const v10 = 1;
        const v11 = v5 + v10;
        const t$3$0 = v3;
        const t$3$1 = v4;
        const t$3$2 = v11;
        v3 = t$3$0;
        v4 = t$3$1;
        v5 = t$3$2;
        continue;
      } else {
        const v10 = { tag: 1, _1: v5 };
        c$3 = false;
        r$3 = v10;
        continue;
      }
    } else {
      const v8 = { tag: 0 };
      c$3 = false;
      r$3 = v8;
      continue;
    }
  }
  return r$3;
};
const span = (v0, v1) => {
  const v2 = 0;
  return span_go(v0, v1, v2);
};
export { span_go, span };
