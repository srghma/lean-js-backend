// @inline Data.Maybe.maybe arity=3
// @inline Data.Maybe.maybe' arity=3
const test5 = a => g => z => {
  const $0 = g(1);
  if (z.tag === "none") { return a + 1 | 0; }
  if (z.tag === "some") { return $0(z._1); }
  throw new Error('UNREACHABLE');
};
const test4 = f => g => z => {
  const $0 = g(1);
  if (z.tag === "none") { return f(); }
  if (z.tag === "some") { return $0(z._1); }
  throw new Error('UNREACHABLE');
};
const test3 = f => z => {
  if (z.tag === "none") { return f(); }
  if (z.tag === "some") { return 1 + z._1 | 0; }
  throw new Error('UNREACHABLE');
};
const test2 = f => g => z => {
  const $0 = f();
  const $1 = g(1);
  if (z.tag === "none") { return $0; }
  if (z.tag === "some") { return $1(z._1); }
  throw new Error('UNREACHABLE');
};
const test1 = f => z => {
  const $0 = f();
  if (z.tag === "none") { return $0; }
  if (z.tag === "some") { return 1 + z._1 | 0; }
  throw new Error('UNREACHABLE');
};
export {test1, test2, test3, test4, test5};
