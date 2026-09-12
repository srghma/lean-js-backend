function test$__lam__0(x) {
  const x_3 = x();
  const x_5 = x();
  return x_3 + x_5;
}

const test = x => () => test$__lam__0(x);
export {test};
