const test5 = v => {
  if (v.tag === "some" && v._1.tag === "ok") { return v._1._1; }
  if (v.tag === "some" && v._1.tag === "error" && v._1._1 === 2) { return 4; }
  return 5;
};
const test4 = v => v1 => {
  if (v.a === 1) {
    if (v1.d === 1) { return 1; }
    if (v1.d === 2) { return 2; }
    if (v1.d === 3) { return 3; }
    if (v1.d === 4) { return 4; }
    if (v1.d === 5) { return 5; }
    return (11 + v.c | 0) + v1.f | 0;
  }
  if (v1.d === 2) { return 2; }
  if (v1.d === 3) { return 3; }
  if (v.a === 2) {
    if (v1.d === 1) { return 6; }
    if (v1.d === 4) {
      if (v.c === v1.e) { return 7; }
      if (v.c < v1.e) { return 8; }
      if (v.c > v1.e) { return 9; }
    }
    return (11 + v.c | 0) + v1.f | 0;
  }
  if (v1.d === 4) {
    if (v.c === v1.e) { return 7; }
    if (v.c < v1.e) { return 8; }
    if (v.c > v1.e) { return 9; }
    return (11 + v.c | 0) + v1.f | 0;
  }
  if (v.b === 2 && v1.d === 1 && v1.f === 10) { return 10; }
  return (11 + v.c | 0) + v1.f | 0;
};
const test3 = v => {
  if (v._1 === v._2) { return v._1; }
  if (v._3 === v._2) { return v._1; }
  if (v._1 === v._3) { return v._3; }
  return v._2;
};
const test2 = v => {
  if (v < 1) { return v; }
  if (v > 1) { return v; }
  if (v === 1) { return 1; }
  return 0;
};
const test1 = v => {
  if (v < 1) { return "n: " + v; }
  if (v > 1 && v < 100) { return "1 < x < 100: " + v; }
  if (v > 1 && v < 50) { return "1 < x < 50: " + v; }
  return "catch";
};
export {test1, test2, test3, test4, test5};
