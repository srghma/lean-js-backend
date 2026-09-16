const _mut$test3 = (v0, v1, v2, v3) => {
  let v4 = v0, v5 = v1, v6 = v2, v7 = v3, c$4 = true, r$4;
  while (c$4) {
    if (v4 === 0) {
      if (v5 === 0) {
        c$4 = false;
        r$4 = v6;
        continue;
      } else {
        const v8 = Math.max(0, v5 - 1);
        const v9 = 1;
        const v10 = v6 + v9;
        const v11 = 2;
        const t$4$0 = 1;
        const t$4$1 = v8;
        const t$4$2 = v10;
        const t$4$3 = v11;
        v4 = t$4$0;
        v5 = t$4$1;
        v6 = t$4$2;
        v7 = t$4$3;
        continue;
      }
    } else {
      if (v4 === 1) {
        if (v5 === 0) {
          c$4 = false;
          r$4 = v6;
          continue;
        } else {
          const v8 = Math.max(0, v5 - 1);
          const v9 = v6 + v7;
          const t$4$0 = 2;
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
          const v9 = 3;
          const v10 = v6 + v9;
          const t$4$0 = 0;
          const t$4$1 = v8;
          const t$4$2 = v10;
          const t$4$3 = 0;
          v4 = t$4$0;
          v5 = t$4$1;
          v6 = t$4$2;
          v7 = t$4$3;
          continue;
        }
      }
    }
  }
  return r$4;
};
const test3 = (v0, v1) => _mut$test3(0, v0, v1, 0);
const test4 = (v0, v1, v2) => _mut$test3(1, v0, v1, v2);
const test5 = (v0, v1) => _mut$test3(2, v0, v1, 0);
const _mut$test1 = (v0, v1) => {
  let v2 = v0, v3 = v1, c$2 = true, r$2;
  while (c$2) {
    if (v2 === 0) {
      if (v3 === 0) {
        const v4 = true;
        c$2 = false;
        r$2 = v4;
        continue;
      } else {
        const v4 = Math.max(0, v3 - 1);
        const t$2$0 = 1;
        const t$2$1 = v4;
        v2 = t$2$0;
        v3 = t$2$1;
        continue;
      }
    } else {
      if (v3 === 0) {
        const v4 = false;
        c$2 = false;
        r$2 = v4;
        continue;
      } else {
        const v4 = Math.max(0, v3 - 1);
        const t$2$0 = 0;
        const t$2$1 = v4;
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
export { test3, test4, test5, test1, test2 };
