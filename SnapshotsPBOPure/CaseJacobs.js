const test1 = (v0) => {
  if (v0.tag === 0) {
    const v1 = v0._1;
    const v2 = v0._2;
    if (v1.tag === 3) {
      if (v2.tag === 3) {
        return "e1";
      } else {
        const v3 = v0;
        const v4 = "e7: ";
        const v5 = renderExpr(v3);
        return v4 + v5;
      }
    } else {
      if (v1.tag === 2) {
        const v3 = v1._1;
        const v4 = "e3: ";
        const v5 = renderExpr(v3);
        const v6 = v4 + v5;
        const v7 = " ";
        const v8 = v6 + v7;
        const v9 = renderExpr(v2);
        return v8 + v9;
      } else {
        if (v2.tag === 3) {
          const v3 = "e6: ";
          const v4 = renderExpr(v1);
          return v3 + v4;
        } else {
          const v3 = v0;
          const v4 = "e7: ";
          const v5 = renderExpr(v3);
          return v4 + v5;
        }
      }
    }
  } else {
    if (v0.tag === 1) {
      const v1 = v0._1;
      const v2 = v0._2;
      if (v1.tag === 3) {
        const v3 = "e2: ";
        const v4 = renderExpr(v2);
        return v3 + v4;
      } else {
        if (v1.tag === 0) {
          const v3 = v1._1;
          const v4 = v1._2;
          if (v2.tag === 3) {
            const v5 = v1;
            const v6 = "e4: ";
            const v7 = renderExpr(v5);
            return v6 + v7;
          } else {
            const v5 = "e5: ";
            const v6 = renderExpr(v3);
            const v7 = v5 + v6;
            const v8 = " ";
            const v9 = v7 + v8;
            const v10 = renderExpr(v4);
            const v11 = v9 + v10;
            const v12 = v11 + v8;
            const v13 = renderExpr(v2);
            return v12 + v13;
          }
        } else {
          if (v2.tag === 3) {
            const v3 = v1;
            const v4 = "e4: ";
            const v5 = renderExpr(v3);
            return v4 + v5;
          } else {
            const v3 = v0;
            const v4 = "e7: ";
            const v5 = renderExpr(v3);
            return v4 + v5;
          }
        }
      }
    } else {
      const v1 = v0;
      const v2 = "e7: ";
      const v3 = renderExpr(v1);
      return v2 + v3;
    }
  }
};
const renderExpr = (v0) => {
  if (v0.tag === 0) {
    const v1 = v0._1;
    const v2 = v0._2;
    const v3 = "Add(";
    const v4 = renderExpr(v1);
    const v5 = v3 + v4;
    const v6 = " ";
    const v7 = v5 + v6;
    const v8 = renderExpr(v2);
    const v9 = v7 + v8;
    const v10 = ")";
    return v9 + v10;
  } else {
    if (v0.tag === 1) {
      const v1 = v0._1;
      const v2 = v0._2;
      const v3 = "Mul(";
      const v4 = renderExpr(v1);
      const v5 = v3 + v4;
      const v6 = " ";
      const v7 = v5 + v6;
      const v8 = renderExpr(v2);
      const v9 = v7 + v8;
      const v10 = ")";
      return v9 + v10;
    } else {
      if (v0.tag === 2) {
        const v1 = v0._1;
        const v2 = "Succ(";
        const v3 = renderExpr(v1);
        const v4 = v2 + v3;
        const v5 = ")";
        return v4 + v5;
      } else {
        return "Zero";
      }
    }
  }
};
const instToStringExpr_toString = renderExpr;
export { test1, renderExpr, instToStringExpr_toString };
