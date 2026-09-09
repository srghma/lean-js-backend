
const test5 = mb => {
  if (mb.tag === "some") { return Data$dMaybe.$Maybe("some", mb._1); }
  return Data$dMaybe.Nothing;
};
const test4 = mb => {
  if (mb.tag === "some") { return Data$dMaybe.$Maybe("some", 42); }
  return Data$dMaybe.Nothing;
};
const test3 = mb => {
  if (mb.tag === "some") { return Data$dMaybe.$Maybe("some", 42); }
  return Data$dMaybe.Nothing;
};
const test2 = mb => {
  if (mb.tag === "some") { return Data$dMaybe.$Maybe("some", undefined); }
  return Data$dMaybe.Nothing;
};
const test1 = mb => {
  if (mb.tag === "some") { return Data$dMaybe.$Maybe("some", (mb._1)); }
  return Data$dMaybe.Nothing;
};
export {test1, test2, test3, test4, test5};
