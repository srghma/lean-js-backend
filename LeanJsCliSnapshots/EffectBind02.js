const test = random => () => {
  const a = random();
  const b = random();
  return a + b | 0;
};
export {test};
