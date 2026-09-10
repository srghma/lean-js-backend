const test2 = random => {
  const n = random();
  const m = random();
  return n + m | 0;
};
const counter = { value: 1 };
const test1 = 1;
export { counter, test1, test2 };
