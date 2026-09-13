const $SumType$L = value0 => ({ tag: "L", _1: value0 });
const $SumType$R = value0 => ({ tag: "R", _1: value0 });
const test1 = v => {
  if (v.tag === "L") {
    if (v._1 === 1) { return "1"; }
    if (v._1 === 2) { return "2"; }
    return "3";
  }
  if (v.tag === "R") { return "4"; }
  throw new Error('UNREACHABLE');
};
export {$SumType$L, $SumType$R, test1};
