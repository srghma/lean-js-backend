const test1 = f => a => b => {
  const $0 = f(a);
  if ($0 && f(b) ? $0 : true) { return $0; }
  return f();
};
export { test1 };
