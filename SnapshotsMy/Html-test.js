const _private_SnapshotsMy_Html_0_p = (v0) => {
  const v1 = [];
  const v2 = v0(v1);
  const v3 = v2._2;
  return { tag: 0, _1: "p", _2: v3 };
};
const _private_SnapshotsMy_Html_0_h2 = (v0) => {
  const v1 = [];
  const v2 = v0(v1);
  const v3 = v2._2;
  return { tag: 0, _1: "h2", _2: v3 };
};
const _private_SnapshotsMy_Html_0_article = (v0) => {
  const v1 = [];
  const v2 = v0(v1);
  const v3 = v2._2;
  return { tag: 0, _1: "article", _2: v3 };
};
const _private_SnapshotsMy_Html_0_section_ = (v0) => {
  const v1 = [];
  const v2 = v0(v1);
  const v3 = v2._2;
  return { tag: 0, _1: "section", _2: v3 };
};
const _private_SnapshotsMy_Html_0_h1 = (v0) => {
  const v1 = [];
  const v2 = v0(v1);
  const v3 = v2._2;
  return { tag: 0, _1: "h1", _2: v3 };
};
export const test = (v0) => {
  const v1 = (v1) => {
    const v2 = (v2) => {
      const v3 = 0;
      const v4 = "Posts for " + v0;
      const v5 = { tag: 1, _1: v4 };
      const v6 = [...v2, v5];
      return { tag: 0, _1: v3, _2: v6 };
    };
    const v3 = _private_SnapshotsMy_Html_0_h1(v2);
    const v4 = [...v1, v3];
    const v5 = 0;
    const v6 = (v6) => {
      const v7 = (v7) => {
        const v8 = { tag: 1, _1: "The first post" };
        const v9 = [...v7, v8];
        return { tag: 0, _1: v5, _2: v9 };
      };
      const v8 = _private_SnapshotsMy_Html_0_h2(v7);
      const v9 = [...v6, v8];
      const v10 = (v10) => {
        const v11 = { tag: 1, _1: "This is the first post." };
        const v12 = [...v10, v11];
        const v13 = { tag: 1, _1: "Not much else to say." };
        const v14 = [...v12, v13];
        return { tag: 0, _1: v5, _2: v14 };
      };
      const v11 = _private_SnapshotsMy_Html_0_p(v10);
      const v12 = [...v9, v11];
      return { tag: 0, _1: v5, _2: v12 };
    };
    const v7 = _private_SnapshotsMy_Html_0_article(v6);
    const v8 = [...v4, v7];
    return { tag: 0, _1: v5, _2: v8 };
  };
  return _private_SnapshotsMy_Html_0_section_(v1);
};
