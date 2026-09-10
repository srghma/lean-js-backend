const test4 = lo => hi => () => {
  for (let a = lo; a < hi; a++) {
    if (a < 10) {
      console.log(a.toString());
    } else {
      console.log("wat");
    }
  }
};
const test3 = lo => hi => () => {
  for (let a = lo; a < hi; a++) {
    if (a < 10) {
      console.log(a.toString());
    }
  }
};
const test2 = lo => hi => {
  const $0 = lo + 1 | 0;
  const $1 = hi + 1 | 0;
  return () => {
    for (let a = $0; a < $1; a++) {
      console.log(a.toString());
    }
    for (let $2 = $0; $2 < $1; $2++) {
      console.log($2.toString());
    }
    for (let $3 = $0; $3 < $1; $3++) {
      console.log("wat");
    }
  };
};
const test1 = lo => hi => {
  const $0 = lo + 1 | 0;
  const $1 = hi + 1 | 0;
  return () => {
    for (let a = $0; a < $1; a++) {
      console.log(a.toString());
      console.log(a.toString());
    }
  };
};
export { test1, test2, test3, test4 };