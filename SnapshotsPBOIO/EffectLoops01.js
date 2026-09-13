const test4 = arr => () => {
  for (const a of arr) {
    if (a < 10) {
      console.log(a.toString());
    } else {
      console.log("wat");
    }
  }
};
const test3 = arr => () => {
  for (const a of arr) {
    if (a < 10) { console.log(a.toString()); }
  }
};
const test2 = k => {
  const $0 = k(42);
  return () => {
    for (const a of $0) {
      console.log(a.toString());
    }
    for (const $1 of $0) {
      console.log($1.toString());
    }
    for (const $2 of $0) {
      console.log("wat");
    }
  };
};
const test1 = k => {
  const $0 = k(42);
  return () => {
    for (const a of $0) {
      const $1 = a.toString();
      console.log($1);
      console.log($1);
    }
  };
};
export {test1, test2, test3, test4};
