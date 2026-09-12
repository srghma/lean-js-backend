// The one `TextEncoder` of the program: it holds no state between calls, so a fresh
// one at each call would only be an allocation.
const _enc = new TextEncoder();

// The one `TextDecoder` of the program; like `_enc`, it holds no state between
// calls (nothing here decodes a stream).
const _dec = new TextDecoder();

// The UTF-8 bytes of a string, remembering the last two strings asked for: a Lean
// string position is a byte offset into this encoding, so a loop over a string asks
// for the encoding of the same string at every step. The array is shared and only
// ever read; a primitive whose bytes reach the program encodes a fresh one.
let _u8k0 = null;
let _u8v0 = null;
let _u8k1 = null;
let _u8v1 = null;
function _utf8(s) {
  if (s === _u8k0) {
    return _u8v0;
  }
  if (s === _u8k1) {
    const k = _u8k0;
    const v = _u8v0;
    _u8k0 = _u8k1;
    _u8v0 = _u8v1;
    _u8k1 = k;
    _u8v1 = v;
    return _u8v0;
  }
  _u8k1 = _u8k0;
  _u8v1 = _u8v0;
  _u8k0 = s;
  _u8v0 = _enc.encode(s);
  return _u8v0;
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

function lean_string_utf8_get(s, p) {
  const b = _utf8(s);
  if (p >= b.length) {
    return 65;
  }
  if (b[p] < 128) {
    return b[p];
  }
  const n = b[p] < 224 ? 2 : b[p] < 240 ? 3 : 4;
  return _dec.decode(b.subarray(p, p + n)).codePointAt(0);
}

function lean_string_utf8_next(s, p) {
  const b = _utf8(s);
  if (p >= b.length) {
    return p + 1;
  }
  return p + (b[p] < 128 ? 1 : b[p] < 224 ? 2 : b[p] < 240 ? 3 : 4);
}

function test4$go(x, y, z) {
  const u = lean_string_length(x);
  while (y < u) {
    z = z + y;
    y = y + 1;
  }
  return z;
}

function Std$Legacy$Range$forIn_u39_$loop(x_26, x_2, x_3) {
  while (x_3 < x_26) {
    const x_17 = x_2._2;
    x_2 = ({ _1: x_2._1 + _utf8(x_17).length, _2: x_17 + "x" });
    x_3 = x_3 + 1;
  }
  return x_2;
}

function test2$go(x, y, z) {
  const u = _utf8(x);
  while (!(z >= u.length)) {
    if (lean_string_utf8_get(x, z) === y) {
      return z;
    }
    z = lean_string_utf8_next(x, z);
  }
  return z;
}

function test1$go(x, y, z, w) {
  const u = _utf8(x);
  while (!(z >= u.length)) {
    const x_6 = lean_string_utf8_next(x, z);
    if (lean_string_utf8_get(x, z) === y) {
      z = x_6;
      w = w + 1;
      continue;
    }
    z = x_6;
  }
  return w;
}

const test4 = x => test4$go(x, 0, 0);
const test3 = (x, y) => Std$Legacy$Range$forIn_u39_$loop(y, ({ _1: 0, _2: x }), 0)._1;
const test2 = (x, y) => test2$go(x, y, 0);
const test1 = (x, y) => test1$go(x, y, 0, 0);
export {test1, test2, test3, test4};
