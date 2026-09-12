function test5(x) {
  if (x.tag === "Option$some") {
    const x_4 = x._1;
    if (x_4.tag === "Except$error") {
      if (x_4._1 === 2) {
        return 4;
      }
      return 5;
    }
    return x_4._1;
  }
  return 5;
}

function test4(x, y) {
  const x_15 = x._1;
  const x_17 = x._3;
  const j_22 = x_18 => {
    return 11 + x_17 + x_18;
  };
  if (x_15 === 1) {
    const x_49 = y._1;
    if (x_49 === 1) {
      return 1;
    }
    if (x_49 === 2) {
      return 2;
    }
    if (x_49 === 3) {
      return 3;
    }
    if (x_49 === 4) {
      return 4;
    }
    if (x_49 === 5) {
      return 5;
    }
    return j_22(y._3);
  }
  if (x_15 === 2) {
    const x_39 = y._1;
    if (x_39 === 2) {
      return 2;
    }
    if (x_39 === 3) {
      return 3;
    }
    if (x_39 === 1) {
      return 6;
    }
    if (x_39 === 4) {
      if (x_17 === y._2) {
        return 7;
      }
      if (x_17 < y._2) {
        return 8;
      }
      return 9;
    }
    return j_22(y._3);
  }
  const x_27 = y._1;
  const x_29 = y._3;
  if (x_27 === 2) {
    return 2;
  }
  if (x_27 === 3) {
    return 3;
  }
  if (x_27 === 4) {
    if (x_17 === y._2) {
      return 7;
    }
    if (x_17 < y._2) {
      return 8;
    }
    return 9;
  }
  if (x_27 === 1 && x_29 === 10) {
    if (x._2 === 2) {
      return 10;
    }
    return j_22(10);
  }
  return j_22(x_29);
}

function test3(x) {
  const x_2 = x._1;
  const x_3 = x._2;
  const x_4 = x._3;
  if (x_2 === x_3) {
    return x_2;
  }
  if (x_4 === x_3) {
    return x_2;
  }
  if (x_2 === x_4) {
    return x_4;
  }
  return x_3;
}

function test2(x) {
  if (x < 1) {
    return x;
  }
  if (x > 1) {
    return x;
  }
  if (x === 1) {
    return 1;
  }
  return 0;
}

function test1(x_1) {
  if (x_1 < 1) {
    if (x_1 < 0) {
      return "n: -" + String(-x_1 > 1 ? -x_1 : 1);
    }
    return "n: " + String(x_1);
  }
  const x_22 = x_1 > 1;
  if (!!x_22 && x_1 < 100) {
    if (x_1 < 0) {
      return "1 < x < 100: -" + String(-x_1 > 1 ? -x_1 : 1);
    }
    return "1 < x < 100: " + String(x_1);
  }
  return "catch";
}

export {test1, test2, test3, test4, test5};
