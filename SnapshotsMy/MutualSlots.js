const _spec$walkNat = (v0, v1, v2) => {
  let v3 = v0, v4 = v1, v5 = v2;
  while (true) {
    if (v3 === 0) {
      return v4;
    } else {
      const v6 = v3 - 1;
      const v7 = v4 === 0;
      if (v7) {
        if (v6 === 0) {
          const v8 = "".length;
          return v8;
        } else {
          const v8 = v6 - 1;
          const v9 = "".length;
          const v10 = v9 + 1;
          v3 = v8;
          v4 = v10;
          v5 = "";
          continue;
        }
      } else {
        if (v6 === 0) {
          const v8 = "xy".length;
          return v8;
        } else {
          const v8 = v6 - 1;
          const v9 = "xy".length;
          const v10 = v9 + 1;
          v3 = v8;
          v4 = v10;
          v5 = "xy";
          continue;
        }
      }
    }
  }
};
export const walkNat = (v0, v1) => _spec$walkNat(v0, v1, "");
export const walkStr = (v0, v1) => {
  if (v0 === 0) {
    return v1.length;
  } else {
    const v2 = v0 - 1;
    const v3 = v1.length;
    const v4 = v3 + 1;
    return _spec$walkNat(v2, v4, v1);
  }
};
