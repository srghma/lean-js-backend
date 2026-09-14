const test1 = 1;
const counter = {
  value: 1,
};
const test2 = (random) => {
  const n = random();
  const m = random();
  return (n + m) | 0;
};
export { counter, test1, test2 };
