const test2 = x => () => {
  const j_6 = x_3 => {
    console.log("Done");
    return null;
  };
  const x_7 = x();
  if (x_7 > 100) {
    console.log("Too hot");
    return j_6();
  }
  if (x_7 < 20) {
    console.log("Too cold");
    return j_6();
  }
  console.log("Just right");
  return j_6();
};

const test1 = x => () => {
  const x_3 = x();
  if (x_3 > 100) {
    console.log("Too hot");
    return null;
  }
  if (x_3 < 20) {
    console.log("Too cold");
    return null;
  }
  console.log("Just right");
  return null;
};

export {test1, test2};
