function test1(x, y, z) {
  if (y) {
    if (x) {
      if (z) {
        return 4;
      }
      return 3;
    }
    return 2;
  }
  if (z) {
    return 1;
  }
  return 3;
}

export {test1};
