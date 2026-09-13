// @fails Binding demanded before initialized
import * as $runtime from "../runtime.js";
const test1$lazy = /* #__PURE__ */ $runtime.binding(() => ({
  foo: test1$lazy().bar,
  bar: 42,
}));
const test2$lazy = /* #__PURE__ */ $runtime.binding(() => ({
  baz: test1$lazy().bar,
}));
const test1 = /* #__PURE__ */ test1$lazy();
const test2 = /* #__PURE__ */ test2$lazy();
const test3 = (n) => {
  if (n < 100) {
    return n;
  }
  return test1$lazy().bar;
};
export { test1, test2, test3 };
