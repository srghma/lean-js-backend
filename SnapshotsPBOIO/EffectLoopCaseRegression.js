const test = eff => () => {
  const res = eff();
  if (res.tag === "none") { return; }
  if (res.tag === "some") {
    for (const a of res._1) {
      console.log(a);
    }
    return;
  }
  throw new Error('UNREACHABLE');
};
export {test};
