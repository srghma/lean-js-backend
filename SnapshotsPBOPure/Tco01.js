const test = (v0) => {
  let v1 = v0, c$1 = true, r$1;
  while (c$1) {
    if (v1 === 0) {
      c$1 = false;
      r$1 = v1;
      continue;
    } else {
      const v2 = Math.max(0, v1 - 1);
      const t$1$0 = v2;
      v1 = t$1$0;
      continue;
    }
  }
  return r$1;
};
export { test };
