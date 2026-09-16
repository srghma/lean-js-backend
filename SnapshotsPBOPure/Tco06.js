const _mut$f = (v0, v1, v2, v3) => {
  let v4 = v0, v5 = v1, v6 = v2, v7 = v3, c$4 = true, r$4;
  while (c$4) {
    if (v4 === 0) {
      if (v5 === 0) {
        const v8 = v6 + v7;
        c$4 = false;
        r$4 = v8;
        continue;
      } else {
        const v8 = Math.max(0, v5 - 1);
        const v9 = v6 + v7;
        const t$4$0 = 1;
        const t$4$1 = v8;
        const t$4$2 = v9;
        const t$4$3 = 0;
        v4 = t$4$0;
        v5 = t$4$1;
        v6 = t$4$2;
        v7 = t$4$3;
        continue;
      }
    } else {
      if (v5 === 0) {
        c$4 = false;
        r$4 = v6;
        continue;
      } else {
        const v8 = Math.max(0, v5 - 1);
        const v9 = 1;
        const v10 = v9;
        const v11 = v6 + v10;
        const t$4$0 = 0;
        const t$4$1 = v8;
        const t$4$2 = v6;
        const t$4$3 = v11;
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
const f = (v0, v1, v2) => _mut$f(0, v0, v1, v2);
const g = (v0, v1) => _mut$f(1, v0, v1, 0);
export { f, g };
