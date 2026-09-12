// `Option.none`, where the analysis found that an `Option` need not be an object: a
// symbol, so that no Lean value — `undefined` and `null` included — is equal to it.
const _none = Symbol("none");

function clampSum(x, y, z, w) {
  if (z === 0) {
    return w;
  }
  const x_9 = z > 1 ? z - 1 : 0;
  const j_13 = x_10 => {
    return clampSum(x, y, x_9, w + x_10);
  };
  if (x_9 < x) {
    return j_13(x);
  }
  if (y < x_9) {
    return j_13(y);
  }
  return j_13(x_9);
}

function sumOpt(x) {
  if (x === _none) {
    return 0;
  }
  return x._1 + x._2;
}

function bigger(x) {
  const x_2 = x._1;
  const x_3 = x._2;
  if (x_2 < x_3) {
    return x;
  }
  return ({ _1: x_3, _2: x_2 });
}

function dist(x, y) {
  if (x < y) {
    return y > x ? y - x : 0;
  }
  return x > y ? x - y : 0;
}

function Std$Legacy$Range$forIn_u39_$loop(x, y, z) {
  while (z < x) {
    y = Std$Legacy$Range$forIn_u39_$loop$spec_2(z, y, 0);
    z = z + 1;
  }
  return y;
}

function Std$Legacy$Range$forIn_u39_$loop$spec_2(x, y, z) {
  while (z < x) {
    y = y + z;
    z = z + 1;
  }
  return y;
}

function test6(x) {
  const x_3 = x % 3;
  const x_6 = x % 7 + 3;
  return clampSum(x_3, x_6, x, 0);
}

const test5 = (x, y) => sumOpt(({ _1: x, _2: y })) + 0;
const test4 = (x, y) => bigger(({ _1: x, _2: y }));

function test3(x, y) {
  const x_6 = x + 1;
  return dist(x, y) + dist(y, x_6);
}

const test2 = x => Std$Legacy$Range$forIn_u39_$loop(x, 0, 0);
const test1 = x => Std$Legacy$Range$forIn_u39_$loop$spec_2(x, 0, 0);
export {test1, test2, test3, test4, test5, test6};
