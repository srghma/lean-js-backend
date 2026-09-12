const test3 = () => {
  const count = { value: 0 };
  return {
    _1: count,
    _2: n => () => {
      const $0 = count.value;
      count.value = $0 + n | 0;
    }
  };
};
const test2 = () => {
  let count = 0;
  return n => () => {
    count = count + n | 0;
  };
};
const test1 = hi => () => {
  let count = 0;
  let continue_ = true;
  while (continue_) {
    const n = count;
    if (n < hi) {
      count = n + 1 | 0;
    } else {
      continue_ = false;
    }
  }
  return count;
};
export { test1, test2, test3 };
