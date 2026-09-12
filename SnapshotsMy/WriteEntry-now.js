function lean_st_ref_set(ref, a) {
  ref.value = a;
}

function lean_st_ref_take(ref) {
  const old = ref.value;
  ref.value = undefined;
  return old;
}

function literalRun() {
  console.log("one\ntwo\nthree");
  return null;
}

function aroundAnAction(x) {
  console.log("before");
  const x_5 = lean_st_ref_take(x);
  lean_st_ref_set(x, x_5 + 1);
  const x_9 = x.value;
  console.log(String(x_9) + "\n" + "after");
  return null;
}

function interleaved() {
  console.log("out 1");
  console.error("err 1");
  console.log("out 2");
  return null;
}

function main() {
  literalRun();
  interleaved();
  const x_5 = ({ value: 41 });
  aroundAnAction(x_5);
  console.log("nonewline!");
  return null;
}

main();
