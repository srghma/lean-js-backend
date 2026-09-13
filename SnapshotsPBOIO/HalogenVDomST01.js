const diffWithKeyAndIxE = (o1, as, fk, f1, f2, f3) => {
  const o2 = {};
  const $0 = as.length;
  for (let i = 0; i < $0; i++) {
    const a = as[i];
    const k = fk(a);
    if (Object.hasOwn(o1, k)) {
      const v2 = f1(k, i, o1[k], a);
      o2[k] = v2;
      continue;
    }
    const v2 = f3(k, i, a);
    o2[k] = v2;
  }
  for (const k of Object.keys(o1)) {
    if (Object.hasOwn(o2, k)) { continue; }
    f2(k, o1[k]);
  }
  return o2;
};
const diffWithIxE = (a1, a2, f1, f2, f3) => {
  const a3 = [];
  const l1 = a1.length;
  const l2 = a2.length;
  const $0 = l1 < l2 ? l2 : l1;
  for (let i = 0; i < $0; i++) {
    if (i < l1) {
      if (i < l2) {
        const v3 = f1(i, a1[i], a2[i]);
        a3.push(v3);
        continue;
      }
      f2(i, a1[i]);
      continue;
    }
    if (i < l2) {
      const v3 = f3(i, a2[i]);
      a3.push(v3);
    }
  }
  return a3;
};
export {diffWithIxE, diffWithKeyAndIxE};
