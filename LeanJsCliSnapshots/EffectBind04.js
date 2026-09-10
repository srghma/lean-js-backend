const test2 = random => () => {
  const n = random();
  if (n > 100) {
    console.log("Too hot");
  } else if (n < 20) {
    console.log("Too cold");
  } else {
    console.log("Just right");
  }
  return console.log("Done");
};
const test1 = random => () => {
  const n = random();
  if (n > 100) { return console.log("Too hot"); }
  if (n < 20) { return console.log("Too cold"); }
  return console.log("Just right");
};
export {test1, test2};
