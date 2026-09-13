const test1 = (k) => () => k()();
const test2 = (k) => k();
export { test1, test2 };
