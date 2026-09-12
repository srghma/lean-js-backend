const _c$List$nil = { tag: "List$nil" };
const _c$Option$none = { tag: "Option$none" };
const _c$Std$DHashMap$Internal$AssocList$nil = { tag: "Std$DHashMap$Internal$AssocList$nil" };

// `m[k]?`.
function _mapGetOpt(m, k) {
  return m.has(k) ? ({ tag: "Option$some", _1: m.get(k) }) : _c$Option$none;
}

// The number of entries of a container of string keys whose size the program asks
// for. It is kept in a *symbol* property, which `Object.keys` does not list and a
// `k in m` on a string key never finds, so the entries of the container are still
// exactly its string properties.
const _objN = Symbol("size");

// An empty container of string keys that keeps the number of its entries.
function _objNew() { const m = Object.create(null); m[_objN] = 0; return m; }

// `m.insert k v` on a container of string keys that keeps the number of its entries.
function _objnSet(m, k, v) {
  if (!(k in m)) {
    m[_objN] = m[_objN] + 1;
  }
  m[k] = v;
  return m;
}

// `m.erase k` on a container of string keys that keeps the number of its entries.
function _objnErase(m, k) {
  if (k in m) {
    delete m[k];
    m[_objN] = m[_objN] - 1;
  }
  return m;
}

// `m.getD k fallback` on a container of string keys.
function _objGetD(m, k, d) { return k in m ? m[k] : d; }

// `a.set i v`, on an array nothing else holds.
function _arrSet(a, i, v) { a[i] = v; return a; }

// A copy of an array, which is what an update works on when the array it is given
// is the one a whole program shares (the `#[]` a function starts from is evaluated
// once, while the module is loaded).
function _arrClone(a) { return a.slice(); }

function lean_array_fset(a, i, v) {
  const b = a.slice();
  b[i] = v;
  return b;
}

function lean_array_uset(a, i, v) {
  const b = a.slice();
  b[i] = v;
  return b;
}

function lean_string_hash(s) {
  let h = 2166136261;
  let i = 0;
  while (i < s.length) {
    h = Math.imul(h ^ s.charCodeAt(i), 16777619);
    i = i + 1;
  }
  return BigInt(h >>> 0);
}

function lean_string_length(s) {
  let n = 0;
  let i = 0;
  while (i < s.length) {
    const c = s.charCodeAt(i);
    if (c >= 55296 && c < 56320 && i + 1 < s.length && s.charCodeAt(i + 1) >= 56320 && s.charCodeAt(i + 1) < 57344) {
      i = i + 2;
    } else {
      i = i + 1;
    }
    n = n + 1;
  }
  return n;
}

const test1$__closed__0 = new Array(16).fill(_c$Std$DHashMap$Internal$AssocList$nil);
const test1$__closed__1 = ({ _1: 0, _2: test1$__closed__0 });

function Std$DHashMap$Internal$AssocList$foldlM(x, y) {
  x = _arrClone(x);
  while (y.tag !== "Std$DHashMap$Internal$AssocList$nil") {
    const x_22 = y._1;
    const x_26 = lean_string_hash(x_22);
    const x_29 = x_26 ^ x_26 >> 32n;
    const x_37 = Number((x_29 ^ x_29 >> 16n) & 9007199254740991n & BigInt(x.length > 1 ? x.length - 1 : 0));
    x[x_37] = ({ tag: "Std$DHashMap$Internal$AssocList$cons", _1: x_22, _2: y._2, _3: x[x_37] });
    y = y._3;
  }
  return x;
}

function Std$DHashMap$Internal$Raw_u8320_$expand$go(x, y, z) {
  while (x < y.length) {
    const t = x + 1;
    const t_4 = lean_array_fset(y, x, _c$Std$DHashMap$Internal$AssocList$nil);
    z = Std$DHashMap$Internal$AssocList$foldlM(z, y[x]);
    x = t;
    y = t_4;
  }
  return z;
}

function Std$DHashMap$Internal$AssocList$replace(x, y) {
  if (y.tag === "Std$DHashMap$Internal$AssocList$nil") {
    return y;
  }
  const x_10 = y._1;
  const x_12 = y._3;
  if (x_10 === x) {
    return ({ tag: "Std$DHashMap$Internal$AssocList$cons", _1: x, _2: 1, _3: x_12 });
  }
  return ({ tag: "Std$DHashMap$Internal$AssocList$cons", _1: x_10, _2: y._2, _3: Std$DHashMap$Internal$AssocList$replace(x, x_12) });
}

function Std$DHashMap$Internal$AssocList$contains(x, y) {
  while (y.tag !== "Std$DHashMap$Internal$AssocList$nil") {
    const x_6 = y._1 === x;
    if (x_6) {
      return x_6;
    }
    y = y._3;
  }
  return 0;
}

const Std$DHashMap$Internal$Raw_u8320_$expand = x => Std$DHashMap$Internal$Raw_u8320_$expand$go(0, x, new Array(x.length * 2).fill(_c$Std$DHashMap$Internal$AssocList$nil));

function Std$DHashMap$Internal$Raw_u8320_$insert(x, y) {
  const x_37 = x._1;
  const x_38 = x._2;
  const x_40 = lean_string_hash(y);
  const x_43 = x_40 ^ x_40 >> 32n;
  const x_51 = Number((x_43 ^ x_43 >> 16n) & 9007199254740991n & BigInt(x_38.length > 1 ? x_38.length - 1 : 0));
  const x_52 = x_38[x_51];
  if (Std$DHashMap$Internal$AssocList$contains(y, x_52)) {
    return ({ _1: x_37, _2: _arrSet(lean_array_uset(x_38, x_51, _c$Std$DHashMap$Internal$AssocList$nil), x_51, Std$DHashMap$Internal$AssocList$replace(y, x_52)) });
  }
  const x_55 = x_37 + 1;
  const x_57 = lean_array_uset(x_38, x_51, ({ tag: "Std$DHashMap$Internal$AssocList$cons", _1: y, _2: 1, _3: x_52 }));
  if (Math.floor(x_55 * 4 / 3) <= x_57.length) {
    return ({ _1: x_55, _2: x_57 });
  }
  return ({ _1: x_55, _2: Std$DHashMap$Internal$Raw_u8320_$expand(x_57) });
}

function List$reverseAux$__redArg(x, y) {
  while (x.tag !== "List$nil") {
    y = ({ tag: "List$cons", _1: x._1, _2: y });
    x = x._2;
  }
  return y;
}

function Std$DHashMap$Internal$AssocList$foldrM(x, y) {
  if (y.tag === "Std$DHashMap$Internal$AssocList$nil") {
    return x;
  }
  return ({ tag: "List$cons", _1: ({ _1: y._1, _2: y._2 }), _2: Std$DHashMap$Internal$AssocList$foldrM(x, y._3) });
}

function List$forIn_u39_$loop(x, y) {
  while (x.tag !== "List$nil") {
    const x_3 = x._1;
    x = x._2;
    y[x_3] = lean_string_length(x_3);
  }
  return y;
}

function List$forIn_u39_$loop$spec_2(x, y) {
  while (x.tag !== "List$nil") {
    const t = x._2;
    y = Std$DHashMap$Internal$Raw_u8320_$insert(y, x._1);
    x = t;
  }
  return y;
}

function List$mapTR$loop(x, y) {
  while (x.tag !== "List$nil") {
    y = ({ tag: "List$cons", _1: x._1._1, _2: y });
    x = x._2;
  }
  return List$reverseAux$__redArg(y, _c$List$nil);
}

function Array$foldrMUnsafe$fold(x, y, z, w) {
  while (y !== z) {
    const x_7 = y > 1 ? y - 1 : 0;
    y = x_7;
    w = Std$DHashMap$Internal$AssocList$foldrM(w, x[x_7]);
  }
  return w;
}

function List$forIn_u39_$loop$spec_3(x, y) {
  while (x.tag !== "List$nil") {
    const t = x._2;
    y = _objnSet(y, x._1, 1);
    x = t;
  }
  return y;
}

function List$forIn_u39_$loop$spec_4(x, y) {
  while (x.tag !== "List$nil") {
    const t = x._2;
    y = y.add(x._1 + "!");
    x = t;
  }
  return y;
}

function List$forIn_u39_$loop$spec_5(x, y) {
  while (x.tag !== "List$nil") {
    const t = x._2;
    y = _objnSet(y, x._1, 1);
    x = t;
  }
  return y;
}

function List$forIn_u39_$loop$spec_6(x, y) {
  while (x.tag !== "List$nil") {
    const t = x._2;
    y = y.add(x._1);
    x = t;
  }
  return y;
}

function List$forIn_u39_$loop$spec_7(x, y) {
  while (x.tag !== "List$nil") {
    const x_3 = x._1;
    x = x._2;
    y = y.set(x_3, x_3 * x_3);
  }
  return y;
}

function List$forIn_u39_$loop$spec_8(x, y) {
  while (x.tag !== "List$nil") {
    const x_3 = x._1;
    x = x._2;
    y = _objnSet(y, x_3, _objGetD(y, x_3, 0) + 1);
  }
  return y;
}

const test7 = (x, y) => _objGetD(List$forIn_u39_$loop(x, Object.create(null)), y, 0);

function test6(x) {
  const x_9 = List$forIn_u39_$loop$spec_2(x, test1$__closed__1)._2;
  const x_10 = _c$List$nil;
  const x_11 = x_9.length;
  if (x_11 > 0) {
    return List$mapTR$loop(Array$foldrMUnsafe$fold(x_9, x_11, 0, x_10), _c$List$nil);
  }
  return List$mapTR$loop(x_10, _c$List$nil);
}

function test5(x) {
  const x_3 = List$forIn_u39_$loop$spec_3(x, _objNew());
  return _objnErase(Object.assign(Object.create(null), x_3), "a")[_objN] * 100 + _objnErase(Object.assign(Object.create(null), x_3), "b")[_objN];
}

const test4 = x => List$forIn_u39_$loop$spec_5(x, _objNew())[_objN] + List$forIn_u39_$loop$spec_4(x, new Set()).size;

function test3(x) {
  const x_3 = List$forIn_u39_$loop$spec_6(x, new Set());
  const x_4 = x_3.size;
  if (x_3.has("a")) {
    return x_4 + 1;
  }
  return x_4;
}

const test2 = x => _mapGetOpt(List$forIn_u39_$loop$spec_7(x, new Map()), 3);
const test1 = x => List$forIn_u39_$loop$spec_8(x, _objNew())[_objN];
export {test1, test2, test3, test4, test5, test6, test7};
