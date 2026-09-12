const _c$List$nil = { tag: "List$nil" };

// The command line arguments as a Lean `Array String`, which a JavaScript array of
// strings already is. For a `main` that takes them and only turns them into an array.
// As in a compiled Lean program, the name of the program itself is not included.
function _argvArray() {
  return typeof process === "undefined" ? [] : process.argv.slice(2);
}

// The command line arguments as a Lean `List String`, for a `main` that takes them.
function _argv() {
  const a = _argvArray();
  let l = _c$List$nil;
  let i = a.length - 1;
  while (i >= 0) {
    l = ({ tag: "List$cons", _1: a[i], _2: l });
    i = i - 1;
  }
  return l;
}

function String$intercalate$go(x, y, z) {
  while (z.tag !== "List$nil") {
    x = x + y + z._1;
    z = z._2;
  }
  return x;
}

function List$lengthTRAux$__redArg(x, y) {
  while (x.tag !== "List$nil") {
    x = x._2;
    y = y + 1;
  }
  return y;
}

function String$intercalate(x, y) {
  if (y.tag === "List$nil") {
    return "";
  }
  return String$intercalate$go(y._1, x, y._2);
}

function main(x) {
  console.log(String(List$lengthTRAux$__redArg(x, 0)) + ": " + String$intercalate(", ", x));
  const x_11 = List$lengthTRAux$__redArg(x, 0);
  if (x_11 <= 125) {
    return x_11 >>> 0;
  }
  return 125;
}

const _res = main(_argv());
if (typeof process !== "undefined" && typeof _res === "number") { process.exitCode = _res; }
