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

// `Option.none`, where the analysis found that an `Option` need not be an object: a
// symbol, so that no Lean value — `undefined` and `null` included — is equal to it.
const _none = Symbol("none");

function lean_string_utf8_get_fast(s, p) {
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

const test5 = 104;
const test4 = "total (3, ok)";

function String$Slice$Pos$get_u63_(x) {
  const x_4 = x._2;
  if ((x._3 > x_4 ? x._3 - x_4 : 0) === 0) {
    return _none;
  }
  return lean_string_utf8_get_fast(x._1, x_4 + 0);
}

function describe(x, y, z) {
  const s = x + " (" + String(y);
  if (z === _none) {
    return s + ")";
  }
  return s + ", " + z + ")";
}

function test6(x) {
  const x_5 = String$Slice$Pos$get_u63_(({ _1: x, _2: 0, _3: _utf8(x).length }));
  if (x_5 === _none) {
    return 65;
  }
  return x_5;
}

const test3 = (x, y) => x + " (" + String(y) + ")";
const test2 = (x, y) => describe("count", x, y);
const test1 = x => "count (" + String(x) + ")";
export {test1, test2, test3, test4, test5, test6};
