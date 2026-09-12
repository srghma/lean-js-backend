function lean_nat_gcd(a, b) {
  while (b != 0) {
    const t = b;
    b = a % b;
    a = t;
  }
  return a;
}

function test4(x, y, z) {
  while (x !== 0) {
    x = x > 1 ? x - 1 : 0;
    y = y + 1;
    z = z + 2;
  }
  return y + z;
}

function test3(x, y, z) {
  while (x !== 0) {
    x = x > 1 ? x - 1 : 0;
    const t = lean_nat_gcd(z, y + 7);
    z = lean_nat_gcd(y, z + 3);
    y = t;
  }
  return y * 1000 + z;
}

function test2(x, y, z, w) {
  while (x !== 0) {
    x = x > 1 ? x - 1 : 0;
    const t = z;
    z = w;
    w = y + 1;
    y = t;
  }
  return y * 100 + z * 10 + w;
}

function test1(x, y, z) {
  while (x !== 0) {
    if (z === 0) {
      return y;
    }
    x = x > 1 ? x - 1 : 0;
    const t = z;
    z = z > 0 ? y % z : y;
    y = t;
  }
  return y;
}

export {test1, test2, test3, test4};
