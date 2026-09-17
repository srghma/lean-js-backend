import { Repr_addAppParen, String_quote } from "../runtime/lean_runtime.mjs";
const traverseFun1D__at__rewriteBottomUpM__at__rewriteBottomUp_spec_0_spec_0 = (
  v0,
  v1,
) => {
  if (v0.tag === 0) {
    const v2 = v0._1;
    const v3 = v0._2;
    const v4 = v1(v3);
    return { tag: 0, _1: v2, _2: v4 };
  } else {
    const v2 = v0._1;
    const v3 = v0._2;
    const v4 = v1(v2);
    const v5 = v1(v3);
    return { tag: 1, _1: v4, _2: v5 };
  }
};
const rewriteBottomUpM__at__rewriteBottomUp_spec_0 = (v0, v1) => {
  const v2 = (v2) => rewriteBottomUpM__at__rewriteBottomUp_spec_0(v0, v2);
  const v3 = traverseFun1D__at__rewriteBottomUpM__at__rewriteBottomUp_spec_0_spec_0(
    v1,
    v2,
  );
  return v0(v3);
};
export const instReprFun_repr = (v0, v1) => {
  if (v0.tag === 0) {
    const v2 = v0._1;
    const v3 = v0._2;
    const v4 = (v4) => {
      const v5 = { tag: 3, _1: "Fun.Abs" };
      const v6 = { tag: 1 };
      const v7 = { tag: 5, _1: v5, _2: v6 };
      const v8 = String_quote(v2);
      const v9 = { tag: 3, _1: v8 };
      const v10 = { tag: 5, _1: v7, _2: v9 };
      const v11 = { tag: 5, _1: v10, _2: v6 };
      const v12 = instReprFun_repr(v3, 1024);
      const v13 = { tag: 5, _1: v11, _2: v12 };
      const v14 = { tag: 4, _1: v4, _2: v13 };
      const v15 = 0;
      const v16 = { tag: 6, _1: v14, _2: v15 };
      return Repr_addAppParen(v16, v1);
    };
    const v5 = 1024 <= v1;
    if (v5) {
      return v4(1);
    } else {
      return v4(2);
    }
  } else {
    const v2 = v0._1;
    const v3 = v0._2;
    const v4 = (v4) => {
      const v5 = { tag: 3, _1: "Fun.App" };
      const v6 = { tag: 1 };
      const v7 = { tag: 5, _1: v5, _2: v6 };
      const v8 = instReprFun_repr(v2, 1024);
      const v9 = { tag: 5, _1: v7, _2: v8 };
      const v10 = { tag: 5, _1: v9, _2: v6 };
      const v11 = instReprFun_repr(v3, 1024);
      const v12 = { tag: 5, _1: v10, _2: v11 };
      const v13 = { tag: 4, _1: v4, _2: v12 };
      const v14 = 0;
      const v15 = { tag: 6, _1: v13, _2: v14 };
      return Repr_addAppParen(v15, v1);
    };
    const v5 = 1024 <= v1;
    if (v5) {
      return v4(1);
    } else {
      return v4(2);
    }
  }
};
export const instDecidableEqFun_decEq = (v0, v1) => {
  if (v0.tag === 0) {
    const v2 = v0._1;
    const v3 = v0._2;
    if (v1.tag === 0) {
      const v4 = v1._1;
      const v5 = v1._2;
      const v6 = v2 === v4;
      if (v6) {
        const v7 = instDecidableEqFun_decEq(v3, v5);
        if (v7) {
          return true;
        } else {
          return false;
        }
      } else {
        return false;
      }
    } else {
      return false;
    }
  } else {
    const v2 = v0._1;
    const v3 = v0._2;
    if (v1.tag === 0) {
      return false;
    } else {
      const v4 = v1._1;
      const v5 = v1._2;
      const v6 = instDecidableEqFun_decEq(v2, v4);
      if (v6) {
        const v7 = instDecidableEqFun_decEq(v3, v5);
        if (v7) {
          return true;
        } else {
          return false;
        }
      } else {
        return false;
      }
    }
  }
};
export const Fun_size = (v0) => {
  if (v0.tag === 0) {
    const v1 = v0._2;
    const v2 = Fun_size(v1);
    return v2 + 1;
  } else {
    const v1 = v0._1;
    const v2 = v0._2;
    const v3 = Fun_size(v1);
    const v4 = Fun_size(v2);
    const v5 = v3 + v4;
    return v5 + 1;
  }
};
export const traverseFun1D = (v0, v1, v2, v3, v4, v5, v6) => {
  const v7 = (v7, v8) => ({ tag: 1, _1: v7, _2: v8 });
  if (v5.tag === 0) {
    const v8 = v5._1;
    const v9 = v5._2;
    const v10 = (v10) => ({ tag: 0, _1: v8, _2: v10 });
    const v11 = v0._1;
    const v12 = v6(v9);
    return v11(v10, v12);
  } else {
    const v8 = v5._1;
    const v9 = v5._2;
    const v10 = (v10) => v6(v9);
    const v11 = v0._1;
    const v12 = v6(v8);
    const v13 = v11(v7, v12);
    return v2(v13, v10);
  }
};
export const traverseFun1 = (v0, v1, v2, v3, v4, v5, v6) => {
  const v7 = (v7, v8) => ({ tag: 1, _1: v7, _2: v8 });
  if (v6.tag === 0) {
    const v8 = v6._1;
    const v9 = v6._2;
    const v10 = (v10) => ({ tag: 0, _1: v8, _2: v10 });
    const v11 = v0._1;
    const v12 = v5(v9);
    return v11(v10, v12);
  } else {
    const v8 = v6._1;
    const v9 = v6._2;
    const v10 = (v10) => v5(v9);
    const v11 = v0._1;
    const v12 = v5(v8);
    const v13 = v11(v7, v12);
    return v2(v13, v10);
  }
};
export const rewriteBottomUpM = (v0, v1, v2, v3) => {
  const v4 = (v4) => rewriteBottomUpM(v0, v1, v2, v4);
  const v5 = (v5) => v2(v5);
  const v6 = traverseFun1D(v0._1, v0._2, v0._3, v0._4, v0._5, v3, v4);
  return v1(v6, v5);
};
export const rewriteBottomUp = (v0, v1) => {
  const v2 = (v2) => v0(v2);
  return rewriteBottomUpM__at__rewriteBottomUp_spec_0(v2, v1);
};
export const instReprFun_reprPrec = instReprFun_repr;
export const instDecidableEqFun = instDecidableEqFun_decEq;
