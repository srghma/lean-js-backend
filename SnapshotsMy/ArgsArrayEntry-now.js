// The command line arguments as a Lean `Array String`, which a JavaScript array of
// strings already is. For a `main` that takes them and only turns them into an array.
// As in a compiled Lean program, the name of the program itself is not included.
function _argvArray() {
  return typeof process === "undefined" ? [] : process.argv.slice(2);
}

function Array$forIn_u39_Unsafe$loop(x, y, z) {
  while (z < y) {
    console.log(x[z]);
    z = z + 1;
  }
  return null;
}

function main(x) {
  const x_4 = x.length;
  console.log(String(x_4) + " argument(s)");
  const x_12 = Array$forIn_u39_Unsafe$loop(x, x.length, 0);
  if (x_4 <= 125) {
    return x_4 >>> 0;
  }
  return 125;
}

const _res = main(_argvArray());
if (typeof process !== "undefined" && typeof _res === "number") { process.exitCode = _res; }
