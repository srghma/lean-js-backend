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

const test7 = (x, y) => Number.isSafeInteger(lean_string_length(x) > y ? lean_string_length(x) - y : 0) ? Math.floor((lean_string_length(x) > y ? lean_string_length(x) - y : 0) / 2) : Number(BigInt(lean_string_length(x) > y ? lean_string_length(x) - y : 0) >> 1n);
const test6 = x => x.length <= 2147483647 ? x.length & 7 : Number(BigInt(x.length) & 7n);
const test5 = x => Number.isSafeInteger(x) ? Math.floor(x / 2) : Number(BigInt(x) >> 1n);
const test4 = x => Math.floor(lean_string_length(x) / 3);
const test3 = x => Math.floor(x.length / 2);
const test2 = (x, y) => (x.length + y.length) * 3;
const test1 = x => Math.floor(x.length / 2);
export {test1, test2, test3, test4, test5, test6, test7};
