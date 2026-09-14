const test1 = (cond) => () => {
  while (cond.value) {
    console.log("foo");
    console.log("bar");
  }
};
const test2 = (cond) => () => {
  while (cond.value) {
    console.log("foo");
  }
  while (cond.value) {
    console.log("bar");
  }
};
const test3 = (cond, ref) => () => {
  while (cond.value) {
    const a = ref.value;
    if (a < 10) {
      console.log("foo");
    }
  }
};
const test4 = (cond, ref) => () => {
  while (cond.value) {
    const a = ref.value;
    if (a < 10) {
      console.log("foo");
    } else {
      console.log("wat");
    }
  }
};
export { test1, test2, test3, test4 };
