const test1 = () => v => {
  if (v === 1) { return 1; }
  if (v === 2) { return 2; }
  if (v === 3) { return 3; }
  throw new Error('UNREACHABLE');
};
export { test1 };
