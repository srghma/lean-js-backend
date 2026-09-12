function test4(x) {
  if (x.tag === "List$nil") {
    return "empty";
  }
  if (x._2.tag === "List$nil") {
    return "one " + String(x._1);
  }
  return "many";
}

function test3(x) {
  if (x.tag === "Shape$dot") {
    return 0;
  }
  if (x.tag === "Shape$circle") {
    return x._1;
  }
  return x._1 + x._2;
}

function test2(x, y) {
  if (x.tag === "Shape$dot") {
    return y;
  }
  if (x.tag === "Shape$circle") {
    return x._1 + y;
  }
  return x._1 + x._2 + y;
}

function test1(x, y) {
  if (x === 0) {
    return y;
  }
  if (x === 1) {
    return y + 1;
  }
  return y + 2;
}

export {test1, test2, test3, test4};
