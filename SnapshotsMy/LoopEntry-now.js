const _c$List$nil = { tag: "List$nil" };

const messages = ({
  tag: "List$cons",
  _1: "one",
  _2: ({ tag: "List$cons", _1: "two", _2: ({ tag: "List$cons", _1: "three", _2: _c$List$nil }) })
});

function List$forIn_u39_$loop(x) {
  while (x.tag !== "List$nil") {
    console.log(x._1);
    x = x._2;
  }
  return null;
}

let _v$main$__closed__0 = undefined, _i$main$__closed__0 = false;
function main$__closed__0() {
  if (!_i$main$__closed__0) { _i$main$__closed__0 = true; _v$main$__closed__0 = (() => {
    return countUp$__redArg(5, 0);
  })(); }
  return _v$main$__closed__0;
}

function printAll() {
  List$forIn_u39_$loop(messages);
  return null;
}

let _v$main$__closed__1 = undefined, _i$main$__closed__1 = false;
function main$__closed__1() {
  if (!_i$main$__closed__1) { _i$main$__closed__1 = true; _v$main$__closed__1 = (() => {
    return String(main$__closed__0());
  })(); }
  return _v$main$__closed__1;
}

function List$forIn_u39_$loop$spec_2(x) {
  while (x.tag !== "List$nil") {
    console.log(x._1 + "!");
    x = x._2;
  }
  return null;
}

function countUp$__redArg(x, y) {
  while (x !== 0) {
    x = x > 1 ? x - 1 : 0;
    y = y + 2;
  }
  return y;
}

function main() {
  printAll();
  console.log(main$__closed__1());
  List$forIn_u39_$loop$spec_2(messages);
  return null;
}

main();
