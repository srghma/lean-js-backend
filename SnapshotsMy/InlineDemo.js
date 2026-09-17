export const useScale = (v0) => {
  const v1 = v0 * 2;
  const v2 = v0 + 1;
  const v3 = v2 * 2;
  return v1 + v3;
};
export const triple = (v0) => v0 * 3;
export const useTriple = (v0) => {
  const v1 = triple(v0);
  const v2 = v0 + 1;
  const v3 = triple(v2);
  return v1 + v3;
};
export const foo = (v0, v1) => {
  const v2 = v0 * v1;
  return v2 + v0;
};
export const bar = 3;
