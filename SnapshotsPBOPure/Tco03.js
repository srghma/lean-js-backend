const _mut$go = (v0, v1) => {
  let v2 = v0, v3 = v1, c$2 = true, r$2;
  while (c$2) {
    if (v2 === 0) {
      const v4 = 0;
      const v5 = v3 === v4;
      if (v5) {
        c$2 = false;
        r$2 = v3;
        continue;
      } else {
        const v6 = 100;
        const v7 = v3 <= v6;
        if (v7) {
          const v8 = 1;
          const v9 = Math.max(0, v3 - v8);
          const t$2$0 = 0;
          const t$2$1 = v9;
          v2 = t$2$0;
          v3 = t$2$1;
          continue;
        } else {
          const v8 = 1;
          const v9 = Math.max(0, v3 - v8);
          const t$2$0 = 1;
          const t$2$1 = v9;
          v2 = t$2$0;
          v3 = t$2$1;
          continue;
        }
      }
    } else {
      const v4 = 100;
      const v5 = v3 === v4;
      if (v5) {
        const v6 = 1;
        const v7 = Math.max(0, v3 - v6);
        const t$2$0 = 0;
        const t$2$1 = v7;
        v2 = t$2$0;
        v3 = t$2$1;
        continue;
      } else {
        const v6 = 900;
        const v7 = v3 === v6;
        if (v7) {
          const v8 = 42;
          c$2 = false;
          r$2 = v8;
          continue;
        } else {
          const v8 = 1;
          const v9 = Math.max(0, v3 - v8);
          const t$2$0 = 1;
          const t$2$1 = v9;
          v2 = t$2$0;
          v3 = t$2$1;
          continue;
        }
      }
    }
  }
  return r$2;
};
const go = (v0) => _mut$go(0, v0);
const k = (v0) => _mut$go(1, v0);
export { go, k };
