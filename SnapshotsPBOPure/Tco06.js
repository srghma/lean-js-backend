const _spec$f = (v0, v1, v2) => {
  let v3 = v0, v4 = v1, v5 = v2;
  while (true) {
    if (v3 === 0) {
      const v6 = v4 + v5;
      return v6;
    } else {
      const v6 = v3 - 1;
      const v7 = v4 + v5;
      if (v6 === 0) {
        return v7;
      } else {
        const v8 = v6 - 1;
        const v9 = v7 + 1;
        v3 = v8;
        v4 = v7;
        v5 = v9;
        continue;
      }
    }
  }
};
export const f = _spec$f;
export const g = (v0, v1) => {
  if (v0 === 0) {
    return v1;
  } else {
    const v2 = v0 - 1;
    const v3 = v1 + 1;
    return _spec$f(v2, v1, v3);
  }
};
