export const test = (v0) => {
  let v1 = v0;
  while (true) {
    if (v1 === 0) {
      return v1;
    } else {
      const v2 = v1 - 1;
      v1 = v2;
      continue;
    }
  }
};
