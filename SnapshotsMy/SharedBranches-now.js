const test5 = x => x.length === 0;
const test4 = (x, y) => x.length === 0 ? x : String.fromCodePoint(y) + x.slice(x.codePointAt(0) > 65535 ? 2 : 1);
const test3 = x => x.length === 0 ? 65 : x.codePointAt(0);

function test2(x, y) {
  const s = "[" + String(y * y + 1);
  if (x.tag === "List$nil") {
    return s + "]";
  }
  return s + ", " + x._1 + "]";
}

function test1(x, y, z) {
  const s = z + " (error code: " + String(y);
  if (x.tag === "Option$none") {
    return s + ")";
  }
  return s + ")\n  file: " + x._1;
}

export {test1, test2, test3, test4, test5};
