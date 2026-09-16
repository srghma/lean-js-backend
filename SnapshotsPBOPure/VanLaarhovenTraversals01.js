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
const instReprFun_repr = (v0, v1) => {
  if (v0.tag === 0) {
    const v2 = v0._1;
    const v3 = v0._2;
    const v4 = 1024;
    const v5 = v4 <= v1;
    if (v5) {
      const v6 = 1;
      const v7 = v6;
      const v8 = v7;
      const v9 = "Fun.Abs";
      const v10 = { tag: 3, _1: v9 };
      const v11 = { tag: 1 };
      const v12 = { tag: 5, _1: v10, _2: v11 };
      const v13 = String_quote(v2);
      const v14 = { tag: 3, _1: v13 };
      const v15 = { tag: 5, _1: v12, _2: v14 };
      const v16 = { tag: 5, _1: v15, _2: v11 };
      const v17 = instReprFun_repr(v3, v4);
      const v18 = { tag: 5, _1: v16, _2: v17 };
      const v19 = { tag: 4, _1: v8, _2: v18 };
      const v20 = { tag: 0 };
      const v21 = { tag: 6, _1: v19, _2: v20 };
      return Repr_addAppParen(v21, v1);
    } else {
      const v6 = 2;
      const v7 = v6;
      const v8 = v7;
      const v9 = "Fun.Abs";
      const v10 = { tag: 3, _1: v9 };
      const v11 = { tag: 1 };
      const v12 = { tag: 5, _1: v10, _2: v11 };
      const v13 = String_quote(v2);
      const v14 = { tag: 3, _1: v13 };
      const v15 = { tag: 5, _1: v12, _2: v14 };
      const v16 = { tag: 5, _1: v15, _2: v11 };
      const v17 = instReprFun_repr(v3, v4);
      const v18 = { tag: 5, _1: v16, _2: v17 };
      const v19 = { tag: 4, _1: v8, _2: v18 };
      const v20 = { tag: 0 };
      const v21 = { tag: 6, _1: v19, _2: v20 };
      return Repr_addAppParen(v21, v1);
    }
  } else {
    const v2 = v0._1;
    const v3 = v0._2;
    const v4 = 1024;
    const v5 = v4 <= v1;
    if (v5) {
      const v6 = 1;
      const v7 = v6;
      const v8 = v7;
      const v9 = "Fun.App";
      const v10 = { tag: 3, _1: v9 };
      const v11 = { tag: 1 };
      const v12 = { tag: 5, _1: v10, _2: v11 };
      const v13 = instReprFun_repr(v2, v4);
      const v14 = { tag: 5, _1: v12, _2: v13 };
      const v15 = { tag: 5, _1: v14, _2: v11 };
      const v16 = instReprFun_repr(v3, v4);
      const v17 = { tag: 5, _1: v15, _2: v16 };
      const v18 = { tag: 4, _1: v8, _2: v17 };
      const v19 = { tag: 0 };
      const v20 = { tag: 6, _1: v18, _2: v19 };
      return Repr_addAppParen(v20, v1);
    } else {
      const v6 = 2;
      const v7 = v6;
      const v8 = v7;
      const v9 = "Fun.App";
      const v10 = { tag: 3, _1: v9 };
      const v11 = { tag: 1 };
      const v12 = { tag: 5, _1: v10, _2: v11 };
      const v13 = instReprFun_repr(v2, v4);
      const v14 = { tag: 5, _1: v12, _2: v13 };
      const v15 = { tag: 5, _1: v14, _2: v11 };
      const v16 = instReprFun_repr(v3, v4);
      const v17 = { tag: 5, _1: v15, _2: v16 };
      const v18 = { tag: 4, _1: v8, _2: v17 };
      const v19 = { tag: 0 };
      const v20 = { tag: 6, _1: v18, _2: v19 };
      return Repr_addAppParen(v20, v1);
    }
  }
};
const instDecidableEqFun_decEq = (v0, v1) => {
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
      const v4 = v1._1;
      const v5 = v1._2;
      return false;
    }
  } else {
    const v2 = v0._1;
    const v3 = v0._2;
    if (v1.tag === 0) {
      const v4 = v1._1;
      const v5 = v1._2;
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
const Fun_size = (v0) => {
  if (v0.tag === 0) {
    const v1 = v0._1;
    const v2 = v0._2;
    const v3 = Fun_size(v2);
    const v4 = 1;
    return v3 + v4;
  } else {
    const v1 = v0._1;
    const v2 = v0._2;
    const v3 = Fun_size(v1);
    const v4 = Fun_size(v2);
    const v5 = v3 + v4;
    const v6 = 1;
    return v5 + v6;
  }
};
const traverseFun1D = (v0, v1, v2, v3, v4, v5, v6) => {
  const v7 = (v7, v8) => ({ tag: 1, _1: v7, _2: v8 });
  const v8 = v0;
  const v9 = v2;
  if (v5.tag === 0) {
    const v10 = v5._1;
    const v11 = v5._2;
    const v12 = (v12) => ({ tag: 0, _1: v10, _2: v12 });
    const v13 = v8._1;
    const v14 = v6(v11);
    return v13(v12, v14);
  } else {
    const v10 = v5._1;
    const v11 = v5._2;
    const v12 = (v12) => v6(v11);
    const v13 = v9;
    const v14 = v8._1;
    const v15 = v6(v10);
    const v16 = v14(v7, v15);
    return v13(v16, v12);
  }
};
const traverseFun1 = (v0, v1, v2, v3, v4, v5, v6) => {
  const v7 = (v7, v8) => ({ tag: 1, _1: v7, _2: v8 });
  const v8 = v0;
  const v9 = v2;
  if (v6.tag === 0) {
    const v10 = v6._1;
    const v11 = v6._2;
    const v12 = (v12) => ({ tag: 0, _1: v10, _2: v12 });
    const v13 = v8._1;
    const v14 = v5(v11);
    return v13(v12, v14);
  } else {
    const v10 = v6._1;
    const v11 = v6._2;
    const v12 = (v12) => v5(v11);
    const v13 = v9;
    const v14 = v8._1;
    const v15 = v5(v10);
    const v16 = v14(v7, v15);
    return v13(v16, v12);
  }
};
const rewriteBottomUpM = (v0, v1, v2, v3) => {
  const v4 = (v4) => rewriteBottomUpM(v0, v1, v2, v4);
  const v5 = (v5) => v2(v5);
  const v6 = v1;
  const v7 = v6;
  const v8 = v0;
  const v9 = traverseFun1D(v8._1, v8._2, v8._3, v8._4, v8._5, v3, v4);
  return v7(v9, v5);
};
const rewriteBottomUp = (v0, v1) => {
  const v2 = (v2) => v0(v2);
  return rewriteBottomUpM__at__rewriteBottomUp_spec_0(v2, v1);
};
const instReprFun_reprPrec = instReprFun_repr;
const instDecidableEqFun = instDecidableEqFun_decEq;
export {
  instReprFun_repr,
  instDecidableEqFun_decEq,
  Fun_size,
  traverseFun1D,
  traverseFun1,
  rewriteBottomUpM,
  rewriteBottomUp,
  instReprFun_reprPrec,
  instDecidableEqFun,
};
