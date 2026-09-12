const test = x => () => {
  const x_3 = x();
  const x_5 = x();
  return x_3 + x_5;
};

export {test};
