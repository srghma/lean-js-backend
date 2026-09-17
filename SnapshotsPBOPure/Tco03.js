const _mut$go = (v0, v1) => {
  let v2 = v0, v3 = v1;
  while (true) {
    if (v2 === 0) {
      const v4 = v3 === 0;
      if (v4) {
        return v3;
      } else {
        const v5 = v3 <= 100;
        if (v5) {
          const v6 = v3 - 1;
          v2 = 0;
          v3 = v6;
          continue;
        } else {
          const v6 = v3 - 1;
          v2 = 1;
          v3 = v6;
          continue;
        }
      }
    } else {
      const v4 = v3 === 100;
      if (v4) {
        const v5 = Math.max(0, v3 - 1);
        v2 = 0;
        v3 = v5;
        continue;
      } else {
        const v5 = v3 === 900;
        if (v5) {
          return 42;
        } else {
          const v6 = Math.max(0, v3 - 1);
          v2 = 1;
          v3 = v6;
          continue;
        }
      }
    }
  }
};
export const go = (v0) => _mut$go(0, v0);
export const k = (v0) => _mut$go(1, v0);
