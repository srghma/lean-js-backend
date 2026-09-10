const test2 = f => g => x => {
  const fx = f(x);
  const gx = g(x);
  return fx + gx + fx + gx;
};
const test1 = f => g => x => f(x) + g(x);
export {test1, test2};
