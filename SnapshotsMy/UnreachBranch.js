const test = (v0) => {
  const v1 = 3;
  const v2 = v0 < v1;
  if (v2) {
    const v3 = small(v0);
    return v3 + v0;
  } else {
    return 0;
  }
};
const small = (v0) => {
  if (v0 === 0) {
    return 10;
  } else {
    const v1 = Math.max(0, v0 - 1);
    if (v1 === 0) {
      return 20;
    } else {
      const v2 = Math.max(0, v1 - 1);
      return 30;
    }
  }
};
const headOf = (v0) => {
  const v1 = v0._1;
  const v2 = v0._2;
  return v1;
};
export { test, small, headOf };
