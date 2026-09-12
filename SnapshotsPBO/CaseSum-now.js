function test1(x) {
  if (x.tag === "SumType$L") {
    const x_2 = x._1;
    if (x_2 === 1) {
      return "1";
    }
    if (x_2 === 2) {
      return "2";
    }
    return "3";
  }
  return "4";
}

export {test1};
