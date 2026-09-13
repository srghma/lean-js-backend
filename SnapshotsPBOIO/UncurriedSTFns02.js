const test1 = () => 12;
const test2 = (random) => () => {
  const n = random();
  return console.log(n.toString());
};
export { test1, test2 };
