const $Column$zero = {tag: "zero"};
const $Column$one = value0 => ({tag: "one", _1: value0});
const $Column$two = value0 => value1 => ({tag: "one", _1: value0, _2: value1});
const testPBAN = v => v1 => {
  if (v.tag === "one") {
    if (v1.tag === "one") {
      if (v._1 === 1) {
        if (v1._1 === 1) { return 1; }
        return 4;
      }
      if (v._1 === 2 && v1._1 === 2) { return 2; }
    }
    return 4;
  }
  if (v.tag === "two" && v1.tag === "two") { return 3; }
  return 4;
};
const testPBA = v => v1 => {
  if (v1.tag === "one") {
    if (v.tag === "one") {
      if (v._1 === 1) {
        if (v1._1 === 1) { return 1; }
        return 4;
      }
      if (v._1 === 2 && v1._1 === 2) { return 2; }
    }
    return 4;
  }
  if (v.tag === "two" && v._1 === 1 && v1.tag === "two") { return 3; }
  return 4;
};
const testPB = v => v1 => {
  if (v.tag === "one") {
    if (v._1 === 1 && v1.tag === "one") {
      if (v1._1 === 1) { return 1; }
      return 4;
    }
    if (v1.tag === "zero") { return 3; }
    return 4;
  }
  if (v.tag === "two" && v._1 === 2 && v._2 === 3 && v1.tag === "two") {
    if (v1._1 === 2 && v1._2 === 3) { return 2; }
    return 4;
  }
  if (v1.tag === "zero") { return 3; }
  return 4;
};
const testP = v => v1 => v2 => {
  if (v1 === 2) {
    if (v === 1) {
      if (v2 === 1) { return 1; }
      if (v2 === 2) { return 2; }
      if (v2 === 3) { return 3; }
      if (v2 === 4) { return 4; }
      return 5;
    }
    if (v2 === 3) { return 3; }
    return 5;
  }
  if (v === 1 && v2 === 4) { return 4; }
  return 5;
};
export {$Column$one, $Column$two, $Column$zero, testP, testPB, testPBA, testPBAN};
