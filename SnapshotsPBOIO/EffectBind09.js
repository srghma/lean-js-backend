const when$p = bool => k => {
  if (bool) { return k(); }
  return () => {};
};
const test1 = bool => {
  return () => {
    if (bool) { console.log("1") }
    if (bool) { console.log("2") }
    if (bool) { console.log("3") }
  };
};
export {test1, when$p};
