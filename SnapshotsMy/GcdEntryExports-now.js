function lean_nat_gcd(a, b) {
  while (b != 0) {
    const t = b;
    b = a % b;
    a = t;
  }
  return a;
}

const run = 6;

function main() {
  console.log("6");
  return null;
}

const gcd2 = (x, y) => lean_nat_gcd(x, y);
const Nat$gcd = lean_nat_gcd;
export {Nat$gcd, gcd2, run, main};
