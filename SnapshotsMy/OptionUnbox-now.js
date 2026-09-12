const _c$Option$none = { tag: "Option$none" };

// `Option.none`, where the analysis found that an `Option` need not be an object: a
// symbol, so that no Lean value — `undefined` and `null` included — is equal to it.
const _none = Symbol("none");

// Application of a value that is not statically known to be a function of the
// right arity: apply one argument at a time.
function _app(f, args) { let r = f; for (const a of args) { r = r(a); } return r; }

// One step of a partial application: the arguments collected so far, followed by
// the ones this call adds. `_pap` hands it the first three, so calling what `_pap`
// answers with is calling this with the rest. An argument that carries nothing is
// not passed, so a call with no arguments is a call with one such argument.
function _papApply(fn, arity, args, ...more) {
  if (more.length === 0) {
    more = [undefined];
  }
  const all = args.concat(more);
  if (all.length < arity) {
    return _pap(fn, arity, all);
  }
  const r = fn(...all.slice(0, arity));
  return all.length === arity ? r : _app(r, all.slice(arity));
}

// Partial application: collect arguments until `arity` of them are available.
function _pap(fn, arity, args) { return _papApply.bind(null, fn, arity, args); }

function lean_string_hash(s) {
  let h = 2166136261;
  let i = 0;
  while (i < s.length) {
    h = Math.imul(h ^ s.charCodeAt(i), 16777619);
    i = i + 1;
  }
  return BigInt(h >>> 0);
}

function Std$DHashMap$Internal$AssocList$get_u63_(x, y) {
  while (y.tag !== "Std$DHashMap$Internal$AssocList$nil") {
    if (y._1 === x) {
      return y._2;
    }
    y = y._3;
  }
  return _none;
}

function Std$DHashMap$Internal$Raw_u8320_$Const$get_u63_(x, y) {
  const x_3 = x._2;
  const x_5 = lean_string_hash(y);
  const x_8 = x_5 ^ x_5 >> 32n;
  return Std$DHashMap$Internal$AssocList$get_u63_(y, x_3[Number((x_8 ^ x_8 >> 16n) & 9007199254740991n & BigInt(x_3.length > 1 ? x_3.length - 1 : 0))]);
}

const firstBig$__lam__0$__boxed = (x, y) => x < y;

function List$find_u63_$__redArg(x, y) {
  while (y.tag !== "List$nil") {
    const x_4 = y._1;
    const x_6 = x(x_4);
    if (x_6) {
      return x_4;
    }
    y = y._2;
  }
  return _none;
}

function test6(x, y) {
  const x_3 = [({ tag: "Option$some", _1: x }), _c$Option$none];
  if (y < x_3.length) {
    const x_7 = x_3[y];
    if (x_7.tag === "Option$none") {
      return 1;
    }
    return x_7._1;
  }
  return 2;
}

const test5 = x => [({ tag: "Option$some", _1: x }), _c$Option$none];

function test4(x) {
  if (x) {
    return "0";
  }
  return "none";
}

function test3(x, y) {
  const x_3 = Std$DHashMap$Internal$Raw_u8320_$Const$get_u63_(x, y);
  if (x_3 === _none) {
    return 0;
  }
  return x_3;
}

function test2(x, y) {
  const x_3 = List$find_u63_$__redArg(_pap(firstBig$__lam__0$__boxed, 2, [y]), x);
  if (x_3 === _none) {
    return "none";
  }
  return "found " + String(x_3);
}

function test1(x, y) {
  const x_3 = List$find_u63_$__redArg(_pap(firstBig$__lam__0$__boxed, 2, [y]), x);
  if (x_3 === _none) {
    return 0;
  }
  return x_3;
}

export {test1, test2, test3, test4, test5, test6};
