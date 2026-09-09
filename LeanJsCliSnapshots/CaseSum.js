const $SumType = (tag, _1) => ({ tag, _1 });
const L = value0 => $SumType("L", value0);
const R = value0 => $SumType("R", value0);
const test1 = v => {
  if (v.tag === "L") {
    if (v._1 === 1) { return "1"; }
    if (v._1 === 2) { return "2"; }
    return "3";
  }
  if (v.tag === "R") { return "4"; }
  throw new Error('UNREACHABLE');
};
export { $SumType, L, R, test1 };
