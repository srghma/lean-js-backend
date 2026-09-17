export const renderExpr = (v0) => {
  if (v0.tag === 0) {
    const v1 = v0._1;
    const v2 = v0._2;
    const v3 = renderExpr(v1);
    const v4 = "Add(" + v3;
    const v5 = v4 + " ";
    const v6 = renderExpr(v2);
    const v7 = v5 + v6;
    return v7 + ")";
  } else {
    if (v0.tag === 1) {
      const v1 = v0._1;
      const v2 = v0._2;
      const v3 = renderExpr(v1);
      const v4 = "Mul(" + v3;
      const v5 = v4 + " ";
      const v6 = renderExpr(v2);
      const v7 = v5 + v6;
      return v7 + ")";
    } else {
      if (v0.tag === 2) {
        const v1 = v0._1;
        const v2 = renderExpr(v1);
        const v3 = "Succ(" + v2;
        return v3 + ")";
      } else {
        return "Zero";
      }
    }
  }
};
export const test1 = (v0) => {
  if (v0.tag === 0) {
    const v1 = v0._1;
    const v2 = v0._2;
    if (v1.tag === 3) {
      if (v2.tag === 3) {
        return "e1";
      } else {
        const v3 = renderExpr(v0);
        return "e7: " + v3;
      }
    } else {
      if (v1.tag === 2) {
        const v3 = v1._1;
        const v4 = renderExpr(v3);
        const v5 = "e3: " + v4;
        const v6 = v5 + " ";
        const v7 = renderExpr(v2);
        return v6 + v7;
      } else {
        if (v2.tag === 3) {
          const v3 = renderExpr(v1);
          return "e6: " + v3;
        } else {
          const v3 = renderExpr(v0);
          return "e7: " + v3;
        }
      }
    }
  } else {
    if (v0.tag === 1) {
      const v1 = v0._1;
      const v2 = v0._2;
      if (v1.tag === 3) {
        const v3 = renderExpr(v2);
        return "e2: " + v3;
      } else {
        if (v1.tag === 0) {
          const v3 = v1._1;
          const v4 = v1._2;
          if (v2.tag === 3) {
            const v5 = renderExpr(v1);
            return "e4: " + v5;
          } else {
            const v5 = renderExpr(v3);
            const v6 = "e5: " + v5;
            const v7 = v6 + " ";
            const v8 = renderExpr(v4);
            const v9 = v7 + v8;
            const v10 = v9 + " ";
            const v11 = renderExpr(v2);
            return v10 + v11;
          }
        } else {
          if (v2.tag === 3) {
            const v3 = renderExpr(v1);
            return "e4: " + v3;
          } else {
            const v3 = renderExpr(v0);
            return "e7: " + v3;
          }
        }
      }
    } else {
      const v1 = renderExpr(v0);
      return "e7: " + v1;
    }
  }
};
export const instToStringExpr_toString = renderExpr;
