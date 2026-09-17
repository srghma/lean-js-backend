const _spec$test3 = (v0, v1, v2) => {
  let v3 = v0, v4 = v1, v5 = v2;
  while (true) {
    if (v3 === 0) {
      return v4;
    } else {
      const v6 = v3 - 1;
      const v7 = v4 + 1;
      if (v6 === 0) {
        return v7;
      } else {
        const v8 = v6 - 1;
        const v9 = v7 + 2;
        if (v8 === 0) {
          return v9;
        } else {
          const v10 = v8 - 1;
          const v11 = v9 + 3;
          v3 = v10;
          v4 = v11;
          v5 = 2;
          continue;
        }
      }
    }
  }
};
export const test3 = (v0, v1) => _spec$test3(v0, v1, 0);
export const test4 = (v0, v1, v2) => {
  if (v0 === 0) {
    return v1;
  } else {
    const v3 = v0 - 1;
    const v4 = v1 + v2;
    if (v3 === 0) {
      return v4;
    } else {
      const v5 = v3 - 1;
      const v6 = v4 + 3;
      return _spec$test3(v5, v6, v2);
    }
  }
};
export const test5 = (v0, v1) => {
  if (v0 === 0) {
    return v1;
  } else {
    const v2 = v0 - 1;
    const v3 = v1 + 3;
    return _spec$test3(v2, v3, 0);
  }
};
const _spec$test1 = (v0) => {
  let v1 = v0;
  while (true) {
    if (v1 === 0) {
      return true;
    } else {
      const v2 = v1 - 1;
      if (v2 === 0) {
        return false;
      } else {
        const v3 = v2 - 1;
        v1 = v3;
        continue;
      }
    }
  }
};
export const test1 = _spec$test1;
export const test2 = (v0) => {
  if (v0 === 0) {
    return false;
  } else {
    const v1 = v0 - 1;
    return _spec$test1(v1);
  }
};
