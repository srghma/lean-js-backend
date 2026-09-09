const identity = x => x;
const fold = dictFoldable => dictMonoid => dictFoldable.foldMap(dictMonoid)(identity);
const test = v1 => {
  if (v1.tag === "Nothing") { return ""; }
  if (v1.tag === "Just") { return v1._1; }
  throw new Error('UNREACHABLE');
};
export { fold, identity, test };
