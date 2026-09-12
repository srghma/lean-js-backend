// `a ++ b`, on an array nothing else holds: the entries of `b` are pushed onto `a`
// one after another, so the append takes as long as `b` rather than as long as
// both. `b` is only read, and is left as it was. How many entries to take is read
// off `b` first, so that `a ++ a` — where the two are one array — appends the
// entries it had rather than the ones it is growing.
function _arrAppend(a, b) {
  const n = b.length;
  let i = 0;
  while (i < n) {
    a.push(b[i]);
    i = i + 1;
  }
  return a;
}

// A copy of an array, which is what an update works on when the array it is given
// is the one a whole program shares (the `#[]` a function starts from is evaluated
// once, while the module is loaded).
function _arrClone(a) { return a.slice(); }

const test3$__closed__0 = new Array(3).fill(0);

function Std$Legacy$Range$forIn_u39_$loop(x, y, z) {
  while (z < x) {
    y = _arrAppend(y, [z, z * z]);
    z = z + 1;
  }
  return y;
}

function List$forIn_u39_$loop(x, y) {
  while (x.tag !== "List$nil") {
    const t = x._2;
    y = _arrAppend(y, x._1);
    x = t;
  }
  return y;
}

const test5 = x => Std$Legacy$Range$forIn_u39_$loop(x, [], 0);
const test4 = x => [1, 2, ...x];

function test3(x) {
  const x_2 = _arrClone(test3$__closed__0);
  return ({ _1: x_2, _2: [...x_2, ...x] });
}

const test2 = (x, y) => [...x, ...y];
const test1 = x => List$forIn_u39_$loop(x, []);
export {test1, test2, test3, test4, test5};
