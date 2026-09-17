// Time the *generated* module, so the numbers track the compiler rather than a copy of
// its output pasted into a benchmark.
//
// It compares `SnapshotsPBOPure/CaptureDerefRegression01.js` — the loop the backend
// emits for the mutually tail-recursive `testEven`/`testOdd` — against the
// shape MUTUAL_LOOP_PERF.md calls the expected output: the 2-cycle unrolled into one
// specialised loop with the accumulator scalarised.  Both are checked to agree before
// either is timed.
//
// Run: node scripts/bench-generated.mjs

import { testEven } from "../SnapshotsPBOPure/CaptureDerefRegression01.js";

// the shape of §0 of MUTUAL_LOOP_PERF.md: tag specialised away, accumulator scalarised
const expected = (n, b_1, b_2) => {
  while (true) {
    if (n === 0) return { _1: b_1, _2: b_2 };
    const next_b_1 = (b_2 + 1) | 0;
    const next_b_2 = (b_1 + 2) | 0;
    const next_n = n - 1;
    if (next_n === 0) return { _1: next_b_1, _2: next_b_2 };
    b_1 = (next_b_2 + 3) | 0;
    b_2 = (next_b_1 + 4) | 0;
    n = next_n - 1;
  }
};

const N = 1000;
const ITERS = 20000;

// they must compute the same thing before any of it is worth timing
for (const n of [0, 1, 2, 3, 10, 101, 1000]) {
  const a = testEven(n, { tag: 0, _1: 0, _2: 0 });
  const b = expected(n, 0, 0);
  if (a._1 !== b._1 || a._2 !== b._2) {
    console.error(`disagreement at n = ${n}: ${JSON.stringify(a)} vs ${JSON.stringify(b)}`);
    process.exit(1);
  }
}

const time = (label, f) => {
  for (let i = 0; i < 2000; i++) f(); // warm up
  const t0 = process.hrtime.bigint();
  let acc = 0;
  for (let i = 0; i < ITERS; i++) acc = (acc + f()) | 0;
  const t1 = process.hrtime.bigint();
  console.log(`${label.padEnd(34)} ${(Number(t1 - t0) / 1e6).toFixed(0)} ms  (checksum ${acc})`);
};

console.log(`n = ${N}, ${ITERS} iterations, ${process.version}`);
time("generated (specialised loop)", () => testEven(N, { tag: 0, _1: 0, _2: 0 })._1);
time("expected (unrolled, scalarised)", () => expected(N, 0, 0)._1);
