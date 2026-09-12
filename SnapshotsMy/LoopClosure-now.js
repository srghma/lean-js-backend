const _c$List$nil = { tag: "List$nil" };

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

function List$mapTR$loop(x, y, z) {
  while (y.tag !== "List$nil") {
    z = ({ tag: "List$cons", _1: y._1 + x, _2: z });
    y = y._2;
  }
  return List$reverseAux$__redArg(z, _c$List$nil);
}

function List$reverseAux$__redArg(x, y) {
  while (x.tag !== "List$nil") {
    y = ({ tag: "List$cons", _1: x._1, _2: y });
    x = x._2;
  }
  return y;
}

function apply3(x) {
  const x_3 = x(1);
  const x_5 = x(2);
  const x_8 = x(3);
  return x_3 + x_5 + x_8;
}

const Std$Legacy$Range$forIn_u39_$loop = (x, y) => y + x;

function List$mapTR$loop$spec_2(x, y, z) {
  while (y.tag !== "List$nil") {
    const t = y._2;
    z = ({ tag: "List$cons", _1: List$mapTR$loop(x, y._1, _c$List$nil), _2: z });
    y = t;
  }
  return List$reverseAux$__redArg(z, _c$List$nil);
}

function Std$Legacy$Range$forIn_u39_$loop$spec_2(x, y, z, w) {
  const c = _pap(Std$Legacy$Range$forIn_u39_$loop, 2, [x]);
  while (w < y) {
    z = z + apply3(c);
    w = w + 1;
  }
  return z;
}

const test2 = (x, y) => List$mapTR$loop$spec_2(x, y, _c$List$nil);
const test1 = (x, y) => Std$Legacy$Range$forIn_u39_$loop$spec_2(x, y, 0, 0);
export {test1, test2};
