function lean_array_set(a, i, v) {
  const b = a.slice();
  b[i] = v;
  return b;
}

function lean_array_swap(a, i, j) {
  const b = a.slice();
  const t = b[i];
  b[i] = b[j];
  b[j] = t;
  return b;
}

const test5$__closed__0 = ({ _1: 0, _2: 4, _3: 1 });

function Std$Legacy$Range$forIn_u39_$loop(x, y, z) {
  while (z < x._2) {
    const x_18 = y._1;
    y = ({ _1: lean_array_set(x_18, z, z + 1), _2: y._2 + (z < x_18.length ? x_18[z] : 0) });
    z = z + x._3;
  }
  return y;
}

const test5 = x => Std$Legacy$Range$forIn_u39_$loop(test5$__closed__0, ({ _1: new Array(4).fill(x), _2: 0 }), 0)._2;

function test4(x) {
  const x_6 = new Array(3).fill(x + 7);
  return ({ _1: lean_array_set(x_6, 0, 99), _2: x_6.length > 0 ? x_6[0] : 0 });
}

function test3(x) {
  const x_6 = [x + 1];
  return (x_6.length > 0 ? x_6[0] : 0) + [...x_6, 5].length;
}

function test2(x) {
  const x_12 = [x + 1, x + 2, x + 3];
  return (x_12.length > 0 ? x_12[0] : 0) * 10 + (lean_array_swap(x_12, 0, 2).length > 0 ? lean_array_swap(x_12, 0, 2)[0] : 0);
}

function test1(x) {
  const x_6 = new Array(3).fill(x + 7);
  return (x_6.length > 0 ? x_6[0] : 0) + (lean_array_set(x_6, 0, 99).length > 1 ? lean_array_set(x_6, 0, 99)[1] : 0);
}

export {test1, test2, test3, test4, test5};
