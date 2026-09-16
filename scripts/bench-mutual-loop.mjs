// Benchmark for the CaptureDerefRegression01 mutual tail-recursion question.
//
// Variants:
//   A   : purescript-backend-optimizer shape - curried, unboxed scalar
//         accumulators, mutual pair unrolled into one specialised loop.
//   B   : what this backend emits today - one merged dispatch loop with a
//         member tag, and a boxed { tag, _1, _2 } rebuilt every iteration.
//   B1  : merged dispatch loop, but the Box2 accumulator scalarised.
//   B2  : boxed accumulator, but the member tag specialised away (unrolled).
//
// Run: node scripts/bench-mutual-loop.mjs

// --- A ---------------------------------------------------------------
const testEven_A = (n) => (b_1, b_2) => {
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
const testOdd_A = (n) => (b_1, b_2) => {
  if (n === 0) return { _1: b_1, _2: b_2 };
  return testEven_A(n - 1)((b_2 + 3) | 0, (b_1 + 4) | 0);
};

// --- B (current output, verbatim modulo names) -----------------------
const _mut$testEven_B = (v0, v1, v2) => {
  let v3 = v0, v4 = v1, v5 = v2, c$3 = true, r$3;
  while (c$3) {
    if (v3 === 0) {
      if (v4 === 0) { c$3 = false; r$3 = v5; continue; }
      else {
        const v6 = Math.max(0, v4 - 1);
        const v7 = v5._1;
        const v8 = v5._2;
        const v9 = 1;
        const v10 = v9;
        const v11 = v8 + v10;
        const v12 = 2;
        const v13 = v12;
        const v14 = v7 + v13;
        const v15 = { tag: 0, _1: v11, _2: v14 };
        const t$3$0 = 1, t$3$1 = v6, t$3$2 = v15;
        v3 = t$3$0; v4 = t$3$1; v5 = t$3$2;
        continue;
      }
    } else {
      if (v4 === 0) { c$3 = false; r$3 = v5; continue; }
      else {
        const v6 = Math.max(0, v4 - 1);
        const v7 = v5._1;
        const v8 = v5._2;
        const v9 = 3;
        const v10 = v9;
        const v11 = v8 + v10;
        const v12 = 4;
        const v13 = v12;
        const v14 = v7 + v13;
        const v15 = { tag: 0, _1: v11, _2: v14 };
        const t$3$0 = 0, t$3$1 = v6, t$3$2 = v15;
        v3 = t$3$0; v4 = t$3$1; v5 = t$3$2;
        continue;
      }
    }
  }
  return r$3;
};
const testEven_B = (v0, v1) => _mut$testEven_B(0, v0, v1);
const testOdd_B = (v0, v1) => _mut$testEven_B(1, v0, v1);

// --- B1: merged dispatch loop, scalarised accumulator ----------------
const _mut$testEven_B1 = (t, n, b1, b2) => {
  let v3 = t, v4 = n, v5 = b1, v6 = b2, c = true, r1, r2;
  while (c) {
    if (v3 === 0) {
      if (v4 === 0) { c = false; r1 = v5; r2 = v6; continue; }
      else {
        const n1 = Math.max(0, v4 - 1);
        const x = (v6 + 1) | 0, y = (v5 + 2) | 0;
        v3 = 1; v4 = n1; v5 = x; v6 = y;
        continue;
      }
    } else {
      if (v4 === 0) { c = false; r1 = v5; r2 = v6; continue; }
      else {
        const n1 = Math.max(0, v4 - 1);
        const x = (v6 + 3) | 0, y = (v5 + 4) | 0;
        v3 = 0; v4 = n1; v5 = x; v6 = y;
        continue;
      }
    }
  }
  return { _1: r1, _2: r2 };
};
const testEven_B1 = (n, b) => _mut$testEven_B1(0, n, b._1, b._2);
const testOdd_B1 = (n, b) => _mut$testEven_B1(1, n, b._1, b._2);

// --- B2: boxed accumulator, tag specialised away (unrolled) ----------
const testEven_B2 = (n, b) => {
  let v4 = n, v5 = b;
  while (true) {
    if (v4 === 0) return v5;
    {
      const n1 = Math.max(0, v4 - 1);
      const x = (v5._2 + 1) | 0, y = (v5._1 + 2) | 0;
      const b1 = { tag: 0, _1: x, _2: y };
      if (n1 === 0) return b1;
      const n2 = Math.max(0, n1 - 1);
      v5 = { tag: 0, _1: (b1._2 + 3) | 0, _2: (b1._1 + 4) | 0 };
      v4 = n2;
    }
  }
};
const testOdd_B2 = (n, b) => {
  if (n === 0) return b;
  return testEven_B2(Math.max(0, n - 1), { tag: 0, _1: (b._2 + 3) | 0, _2: (b._1 + 4) | 0 });
};

// --- harness ---------------------------------------------------------
const N = Number(process.argv[2] ?? 1000);
const ITERS = Number(process.argv[3] ?? 20000);

const runs = {
  A: () => { const r = testEven_A(N)(10, 20); const s = testOdd_A(N)(10, 20); return r._1 + r._2 + s._1 + s._2; },
  B: () => { const r = testEven_B(N, { tag: 0, _1: 10, _2: 20 }); const s = testOdd_B(N, { tag: 0, _1: 10, _2: 20 }); return r._1 + r._2 + s._1 + s._2; },
  B1: () => { const r = testEven_B1(N, { _1: 10, _2: 20 }); const s = testOdd_B1(N, { _1: 10, _2: 20 }); return r._1 + r._2 + s._1 + s._2; },
  B2: () => { const r = testEven_B2(N, { tag: 0, _1: 10, _2: 20 }); const s = testOdd_B2(N, { tag: 0, _1: 10, _2: 20 }); return r._1 + r._2 + s._1 + s._2; },
};

// agreement check
const vals = Object.entries(runs).map(([k, f]) => [k, f()]);
console.log('results (must all agree):', JSON.stringify(Object.fromEntries(vals)));

const time = (f) => {
  for (let i = 0; i < 2000; i++) f();              // warm up
  const t0 = process.hrtime.bigint();
  let acc = 0;
  for (let i = 0; i < ITERS; i++) acc += f();
  const t1 = process.hrtime.bigint();
  return { ms: Number(t1 - t0) / 1e6, acc };
};

console.log(`N=${N} iters=${ITERS}`);
for (const round of [1, 2, 3]) {
  const line = Object.entries(runs).map(([k, f]) => `${k}=${time(f).ms.toFixed(1)}ms`).join('  ');
  console.log(`round ${round}: ${line}`);
}
