function test1(x) {
  if (x === 1) {
    return 1;
  }
  if (x === 2) {
    return 2;
  }
  if (x === 3) {
    return 3;
  }
  if (x < 0) {
    throw new Error("PANIC at test1 LeanJsCliSnapshots.CasePartial:5:9: mypanic -" + String(-x > 1 ? -x : 1));
  }
  throw new Error("PANIC at test1 LeanJsCliSnapshots.CasePartial:5:9: mypanic " + String(x));
}

export {test1};
