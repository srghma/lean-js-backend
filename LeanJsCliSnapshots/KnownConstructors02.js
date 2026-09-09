const test = a => {
  if (a.tag === "Left") { return a._1; }
  if (a.tag === "Right") { return a._1; }
  throw new Error('UNREACHABLE');
};
export { test };
