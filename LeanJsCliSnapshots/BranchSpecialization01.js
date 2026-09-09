const $TestEnum$foo = "foo";
const $TestEnum$bar = "bar";
const $TestEnum$baz = "baz";
const $TestEnum$qux = "qux";
const instBEqTestEnum = {
  beq: x => y => {
    if (x === "foo") { return y === "foo"; }
    if (x === "bar") { return y === "bar"; }
    if (x === "baz") { return y === "baz"; }
    return x === "qux" && y === "qux";
  }
};
const test1 = a => a === "baz";
const test2 = a => a === "baz";
export { $TestEnum$bar, $TestEnum$baz, $TestEnum$foo, $TestEnum$qux, instBEqTestEnum, test1, test2 };
