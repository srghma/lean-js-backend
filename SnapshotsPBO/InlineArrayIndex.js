// @inline export testArrayIndex never
import * as Assert from "../Assert/index.js";
const assertEqual = /* #__PURE__ */ Assert.assertEqual({
  eq: x => y => {
    if (x.tag === "none") { return y.tag === "none"; }
    return x.tag === "some" && y.tag === "some" && x._1 === y._1;
  }
})({
  show: v => {
    if (v.tag === "some") { return "(Just " + v._1.toString() + ")"; }
    if (v.tag === "none") { return "Nothing"; }
    throw new Error('UNREACHABLE');
  }
});
const testArrayIndex = arr => ix => {
  if (ix >= 0 && ix < arr.length) { return $Option$some(arr[ix]); }
  return $Option$none;
};
const main = /* #__PURE__ */ (() => {
  const array = [1, 2, 3];
  const $0 = assertEqual("index -1")({ expected: $Option$none, actual: testArrayIndex(array)(-1) });
  return () => {
    $0();
    assertEqual("index 0")({ expected: $Option$some(1), actual: testArrayIndex(array)(0) })();
    assertEqual("index 1")({ expected: $Option$some(2), actual: testArrayIndex(array)(1) })();
    assertEqual("index 2")({ expected: $Option$some(3), actual: testArrayIndex(array)(2) })();
    return assertEqual("index 3")({ expected: $Option$none, actual: testArrayIndex(array)(3) })();
  };
})();
export {assertEqual, main, testArrayIndex};
