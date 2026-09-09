const $Expr$add = value0 => value1 => ({ tag: "add", _1: value0, _2: value1 });
const $Expr$mul = value0 => value1 => ({ tag: "mul", _1: value0, _2: value1 });
const $Expr$succ = value0 => ({ tag: "succ", _1: value0 });
const $Expr$zero = { tag: "zero" };
const renderExpr = v => {
  if (v.tag === "add") { return "Add(" + renderExpr(v._1) + " " + renderExpr(v._2) + ")"; }
  if (v.tag === "mul") { return "Mul(" + renderExpr(v._1) + " " + renderExpr(v._2) + ")"; }
  if (v.tag === "succ") { return "Succ(" + renderExpr(v._1) + ")"; }
  if (v.tag === "zero") { return "Zero"; }
  throw new Error('UNREACHABLE');
}
const instToStringExpr = {
  toString: renderExpr
};
const test1 = v => {
  if (v.tag === "add") {
    if (v._2.tag === "zero") {
      if (v._1.tag === "zero") { return "e1"; }
      if (v._1.tag === "succ") { return "e3: " + renderExpr(v._1._1) + " " + renderExpr(v._2); }
      return "e6: " + renderExpr(v._1);
    }
    if (v._1.tag === "succ") { return "e3: " + renderExpr(v._1._1) + " " + renderExpr(v._2); }
    return "e7: " + renderExpr(v);
  }
  if (v.tag === "mul") {
    if (v._1.tag === "zero") { return "e2: " + renderExpr(v._2); }
    if (v._2.tag === "zero") { return "e4: " + renderExpr(v._1); }
    if (v._1.tag === "add") { return "e5: " + renderExpr(v._1._1) + " " + renderExpr(v._1._2) + " " + renderExpr(v._2); }
  }
  return "e7: " + renderExpr(v);
};
export { $Expr$add, $Expr$mul, $Expr$succ, $Expr$zero, instToStringExpr, test1 };
