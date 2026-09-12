function testPBAN(x, y) {
  if (x.tag === "Column$one") {
    const x_5 = x._1;
    if (x_5 === 1) {
      if (y.tag === "Column$one" && y._1 === 1) {
        return 1;
      }
      return 4;
    }
    if (x_5 === 2 && y.tag === "Column$one" && y._1 === 2) {
      return 2;
    }
    return 4;
  }
  if (x.tag === "Column$two" && y.tag === "Column$two") {
    return 3;
  }
  return 4;
}

function testPBA(x, y) {
  if (x.tag === "Column$one") {
    const x_5 = x._1;
    if (x_5 === 1) {
      if (y.tag === "Column$one" && y._1 === 1) {
        return 1;
      }
      return 4;
    }
    if (x_5 === 2 && y.tag === "Column$one" && y._1 === 2) {
      return 2;
    }
    return 4;
  }
  if (x.tag === "Column$two" && x._1 === 1 && y.tag === "Column$two") {
    return 3;
  }
  return 4;
}

function testPB(x, y) {
  if (x.tag === "Column$one") {
    if (x._1 === 1 && y.tag === "Column$one") {
      if (y._1 === 1) {
        return 1;
      }
      return 4;
    }
    if (y.tag === "Column$zero") {
      return 3;
    }
    return 4;
  }
  if (x.tag === "Column$two" && x._1 === 2 && x._2 === 3 && y.tag === "Column$two") {
    if (y._1 === 2 && y._2 === 3) {
      return 2;
    }
    return 4;
  }
  if (y.tag === "Column$zero") {
    return 3;
  }
  return 4;
}

function testP(x, y, z) {
  if (x === 1) {
    if (y === 2) {
      if (z === 1) {
        return 1;
      }
      if (z === 2) {
        return 2;
      }
      if (z === 3) {
        return 3;
      }
      if (z === 4) {
        return 4;
      }
      return 5;
    }
    if (z === 4) {
      return 4;
    }
    return 5;
  }
  if (y === 2 && z === 3) {
    return 3;
  }
  return 5;
}

export {testP, testPB, testPBA, testPBAN};
