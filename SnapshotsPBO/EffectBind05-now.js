const test2 = (x, y) => x()(y);
const test1 = x => () => x()();
export {test1, test2};
