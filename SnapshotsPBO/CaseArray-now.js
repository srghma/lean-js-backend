function test1(x) {
  const x_2 = x.length;
  if (x_2 === 0) {
    return "0";
  }
  if (x_2 === 1) {
    if (x[0] === 1) {
      return "1";
    }
    return "any1";
  }
  if (x_2 === 2) {
    if (x[1] === 2) {
      return "2";
    }
    return "catch";
  }
  if (x_2 === 3) {
    return "3";
  }
  return "catch";
}

export {test1};
