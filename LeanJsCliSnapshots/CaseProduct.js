const test1 = v => {
  if (v._1 === 1) {
    if (v._3 === 3 && v._2 === 2) { return "1"; }
    if (v._2 === 4) { return "2"; }
    return "catch";
  }
  if (v._2 === 4) { return "2"; }
  if (v._1 === 4 && v._2 === 5 && v._3 === 6) { return "3"; }
  return "catch";
};
export {test1};
