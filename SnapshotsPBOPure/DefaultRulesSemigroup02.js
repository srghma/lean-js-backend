const appendR = ra => rb => ({bar: [...ra.bar, ...rb.bar], foo: ra.foo + rb.foo});
const test4 = {bar: ["hello", "World!"], foo: "hello, World!"};
const test3 = /* #__PURE__ */ appendR({foo: "hello", bar: ["hello"]});
const test2 = a => b => ({bar: [...a.bar, ...b.bar], foo: a.foo + b.foo});
const test1 = appendR;
export {appendR, test1, test2, test3, test4};
