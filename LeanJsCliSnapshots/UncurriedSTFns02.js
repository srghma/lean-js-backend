const test2 = random => () => {
  const n = random();
  return console.log(n.toString());
};
const test1 = () => 12;
export {test1, test2};
