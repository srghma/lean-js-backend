export const small = (v0) => {
  if (v0 === 0) {
    return 10;
  } else {
    const v1 = v0 - 1;
    if (v1 === 0) {
      return 20;
    } else {
      return 30;
    }
  }
};
export const test = (v0) => {
  const v1 = v0 < 3;
  if (v1) {
    const v2 = small(v0);
    return v2 + v0;
  } else {
    return 0;
  }
};
export const headOf = (v0) => v0._1;
