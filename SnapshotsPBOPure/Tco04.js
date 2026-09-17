import {
  Int_instDecidableEq,
} from "../runtime/lean_runtime_non_configurable.mjs";
const _spec$test1 = (v0) => {
  let v1 = v0;
  while (true) {
    const v2 = Int_instDecidableEq(v1, 1);
    if (v2) {
      return v1;
    } else {
      const v3 = v1 - 1;
      const v4 = Int_instDecidableEq(v3, 2);
      if (v4) {
        return v3;
      } else {
        const v5 = v3 - 2;
        v1 = v5;
        continue;
      }
    }
  }
};
export const test1 = _spec$test1;
export const test2 = (v0) => {
  const v1 = Int_instDecidableEq(v0, 2);
  if (v1) {
    return v0;
  } else {
    const v2 = v0 - 2;
    return _spec$test1(v2);
  }
};
