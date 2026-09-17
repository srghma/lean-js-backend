import { Function_const } from "../runtime/lean_runtime_non_configurable.mjs";
export const mapExprF = (v0, v1) => {
  if (v1.tag === 0) {
    const v2 = v1._1;
    return { tag: 0, _1: v2 };
  } else {
    if (v1.tag === 1) {
      const v2 = v1._1;
      const v3 = v1._2;
      const v4 = v0(v2);
      const v5 = v0(v3);
      return { tag: 1, _1: v4, _2: v5 };
    } else {
      const v2 = v1._1;
      const v3 = v1._2;
      const v4 = v0(v2);
      const v5 = v0(v3);
      return { tag: 2, _1: v4, _2: v5 };
    }
  }
};
export const instFunctorExprF_map = mapExprF;
export const instFunctorExprF_mapConst = (v0, v1) => {
  const v2 = (v2) => Function_const(v0, v2);
  return mapExprF(v2, v1);
};
export const eval$ = (v0) => {
  if (v0.tag === 0) {
    return v0._1;
  } else {
    if (v0.tag === 1) {
      const v1 = v0._1;
      const v2 = v0._2;
      return v1 + v2;
    } else {
      const v1 = v0._1;
      const v2 = v0._2;
      return v1 * v2;
    }
  }
};
export const bump = (v0) => {
  if (v0.tag === 0) {
    const v1 = v0._1;
    const v2 = v1 + 1;
    return { tag: 0, _1: v2 };
  } else {
    return v0;
  }
};
export const test2 = (v0) => {
  const v1 = (v1) => {
    const v2 = bump(v1);
    return eval$(v2);
  };
  return cata(v1, v0);
};
export const test1 = (v0) => cata(eval$, v0);
export const cataMap = (v0, v1) => {
  if (v1.tag === 0) {
    const v2 = v1._1;
    return { tag: 0, _1: v2 };
  } else {
    if (v1.tag === 1) {
      const v2 = v1._1;
      const v3 = v1._2;
      const v4 = cata(v0, v2);
      const v5 = cata(v0, v3);
      return { tag: 1, _1: v4, _2: v5 };
    } else {
      const v2 = v1._1;
      const v3 = v1._2;
      const v4 = cata(v0, v2);
      const v5 = cata(v0, v3);
      return { tag: 2, _1: v4, _2: v5 };
    }
  }
};
export const cata = (v0, v1) => {
  const v2 = cataMap(v0, v1);
  return v0(v2);
};
