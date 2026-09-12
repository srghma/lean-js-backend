// `a.pop`, on an array nothing else holds. As in Lean, popping an empty array
// answers with the empty array.
function _arrPop(a) { a.pop(); return a; }

// `a.swap i j`, on an array nothing else holds.
function _arrSwap(a, i, j) { const t = a[i]; a[i] = a[j]; a[j] = t; return a; }

// A copy of an array, which is what an update works on when the array it is given
// is the one a whole program shares (the `#[]` a function starts from is evaluated
// once, while the module is loaded).
function _arrClone(a) { return a.slice(); }

function lean_array_set(a, i, v) {
  const b = a.slice();
  b[i] = v;
  return b;
}

const test2$__closed__0 = new Array(8).fill(0);

function buildRec(x, y) {
  while (x !== 0) {
    const x_6 = x > 1 ? x - 1 : 0;
    x = x_6;
    y.push(x_6);
  }
  return y;
}

function Std$Legacy$Range$forIn_u39_$loop(x, y, z, w) {
  while (w < y) {
    z = _arrSwap(z, w, (x > w ? x - w : 0) > 1 ? (x > w ? x - w : 0) - 1 : 0);
    w = w + 1;
  }
  return z;
}

function Std$Legacy$Range$forIn_u39_$loop$spec_2(x, y, z) {
  while (z < x) {
    y.push(z);
    z = z + 1;
  }
  return y;
}

function Std$Legacy$Range$forIn_u39_$loop$spec_3(x, y, z) {
  y = _arrClone(y);
  while (z < x) {
    y[z] = 2 * (z < y.length ? y[z] : 0);
    z = z + 1;
  }
  return y;
}

function List$forIn_u39_$loop(x, y) {
  while (x.tag !== "List$nil") {
    const x_7 = x._1 % 8;
    x = x._2;
    y[x_7] = (x_7 < y.length ? y[x_7] : 0) + 1;
  }
  return y;
}

function Std$Legacy$Range$forIn_u39_$loop$spec_4(x, y, z) {
  while (z < x) {
    y.push(z * z);
    z = z + 1;
  }
  return y;
}

const test6 = x => buildRec(x, []);

function test5(x) {
  const x_7 = Number.isSafeInteger(x) ? Math.floor(x / 2) : Number(BigInt(x) >> 1n);
  return _arrPop(Std$Legacy$Range$forIn_u39_$loop(x, x_7, Std$Legacy$Range$forIn_u39_$loop$spec_2(x, [], 0), 0));
}

function test4(x) {
  const x_3 = new Array(3).fill(x);
  return ({ _1: x_3, _2: lean_array_set(x_3, 0, 7) });
}

function test3(x) {
  const x_3 = x.length;
  return Std$Legacy$Range$forIn_u39_$loop$spec_3(x_3, x, 0);
}

const test2 = x => List$forIn_u39_$loop(x, _arrClone(test2$__closed__0));
const test1 = x => Std$Legacy$Range$forIn_u39_$loop$spec_4(x, [], 0);
export {test1, test2, test3, test4, test5, test6};
