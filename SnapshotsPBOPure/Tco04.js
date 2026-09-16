const _mut$test1 = (v0, v1) => {
  let v2 = v0, v3 = v1, c$2 = true, r$2;
  while (c$2) {
    if (v2 === 0) {
      const v4 = 1;
      const v5 = v4;
      const v6 = Int_instDecidableEq(v3, v5);
      if (v6) {
        c$2 = false;
        r$2 = v3;
        continue;
      } else {
        const v7 = v3 - v5;
        const t$2$0 = 1;
        const t$2$1 = v7;
        v2 = t$2$0;
        v3 = t$2$1;
        continue;
      }
    } else {
      const v4 = 2;
      const v5 = v4;
      const v6 = Int_instDecidableEq(v3, v5);
      if (v6) {
        c$2 = false;
        r$2 = v3;
        continue;
      } else {
        const v7 = v3 - v5;
        const t$2$0 = 0;
        const t$2$1 = v7;
        v2 = t$2$0;
        v3 = t$2$1;
        continue;
      }
    }
  }
  return r$2;
};
const test1 = (v0) => _mut$test1(0, v0);
const test2 = (v0) => _mut$test1(1, v0);
export { test1, test2 };
