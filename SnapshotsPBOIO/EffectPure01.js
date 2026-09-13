const test1 = () => 1;
const test2 = (a) => {
  const $0 = (a + 1) | 0;
  return () => $0;
};
export { test1, test2 };
