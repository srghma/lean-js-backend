// A copy of an array, which is what an update works on when the array it is given
// is the one a whole program shares (the `#[]` a function starts from is evaluated
// once, while the module is loaded).
function _arrClone(a) { return a.slice(); }

function Array$mapMUnsafe$map(x, y, z) {
  z = _arrClone(z);
  while (y < x) {
    const t = y + 1;
    z[y] = z[y] + 1;
    y = t;
  }
  return z;
}

function Array$mapMUnsafe$map$spec_2(x, y, z, w) {
  w = _arrClone(w);
  while (z < y) {
    const x_9 = x(w[z]);
    const t = z + 1;
    w[z] = x_9;
    z = t;
  }
  return w;
}

function Array$foldlMUnsafe$fold(x, y, z, w, a) {
  if (z === w) {
    return a;
  }
  const x_12 = y[z];
  const x_13 = x(x_12);
  if (x_13) {
    return Array$foldlMUnsafe$fold(x, y, z + 1, w, [...a, x_12]);
  }
  return Array$foldlMUnsafe$fold(x, y, z + 1, w, a);
}

function Array$foldlMUnsafe$fold$spec_2(x, y, z, w) {
  if (y === z) {
    return w;
  }
  const x_11 = x[y];
  if (x_11 > 4) {
    return Array$foldlMUnsafe$fold$spec_2(x, y + 1, z, [...w, x_11]);
  }
  return Array$foldlMUnsafe$fold$spec_2(x, y + 1, z, w);
}

function Array$mapMUnsafe$map$spec_3(x, y, z) {
  z = _arrClone(z);
  while (y < x) {
    const t = y + 1;
    z[y] = z[y] * 2;
    y = t;
  }
  return z;
}

function test5(x) {
  const x_3 = x.length;
  const x_4 = [];
  const x_5 = x_3 > 0;
  if (x_5) {
    const s = Array$foldlMUnsafe$fold$spec_2(x, 0, x_3, x_4);
    if (x_3 <= x_3) {
      return s;
    }
    return s;
  }
  return x_4;
}

const test4 = x => Array$mapMUnsafe$map(x.length, 0, x);

function test3(x) {
  const x_4 = Array$mapMUnsafe$map$spec_3(x.length, 0, x);
  const x_6 = x_4.length;
  const x_7 = [];
  const x_8 = x_6 > 0;
  if (x_8) {
    const s = ({ _1: x_4, _2: Array$foldlMUnsafe$fold$spec_2(x_4, 0, x_6, x_7) });
    if (x_6 <= x_6) {
      return s;
    }
    return s;
  }
  return ({ _1: x_4, _2: x_7 });
}

function test2(x, y, z) {
  const x_6 = Array$mapMUnsafe$map$spec_2(y, x.length, 0, x);
  const x_8 = x_6.length;
  const x_9 = [];
  const x_10 = x_8 > 0;
  if (x_10) {
    const s = Array$foldlMUnsafe$fold(z, x_6, 0, x_8, x_9);
    if (x_8 <= x_8) {
      return s;
    }
    return s;
  }
  return x_9;
}

function test1(x) {
  const x_4 = Array$mapMUnsafe$map$spec_3(x.length, 0, x);
  const x_6 = x_4.length;
  const x_7 = [];
  const x_8 = x_6 > 0;
  if (x_8) {
    const s = Array$foldlMUnsafe$fold$spec_2(x_4, 0, x_6, x_7);
    if (x_6 <= x_6) {
      return s;
    }
    return s;
  }
  return x_7;
}

export {test1, test2, test3, test4, test5};
