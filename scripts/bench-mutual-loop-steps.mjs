// Finer breakdown of the gap between the current merged-dispatch loop and the
// purescript-backend-optimizer shape, for CaptureDerefRegression01.
//
// Each step adds one transformation on top of the previous one:
//   S0  current output (tag dispatch, boxed accumulator, flag-driven exit,
//       Math.max for Nat predecessor)
//   S1  + scalarise the Box2 accumulator (no per-iteration allocation)
//   S2  + return directly instead of `c$ = false; r$ = …; continue`
//   S3  + `n - 1` instead of `Math.max(0, n - 1)` (guarded by `n === 0` above)
//   S4  + specialise the member tag away (unroll the 2-cycle)
//   S5  = S4 with the entry points curried, i.e. the expected output
//
// Run: node scripts/bench-mutual-loop-steps.mjs [N] [iters]

// S0 -------------------------------------------------------------------
const mS0 = (v0, v1, v2) => {
  let v3 = v0, v4 = v1, v5 = v2, c = true, r;
  while (c) {
    if (v3 === 0) {
      if (v4 === 0) { c = false; r = v5; continue; }
      else {
        const v6 = Math.max(0, v4 - 1);
        const v7 = v5._1, v8 = v5._2;
        const v11 = v8 + 1, v14 = v7 + 2;
        const v15 = { tag: 0, _1: v11, _2: v14 };
        v3 = 1; v4 = v6; v5 = v15; continue;
      }
    } else {
      if (v4 === 0) { c = false; r = v5; continue; }
      else {
        const v6 = Math.max(0, v4 - 1);
        const v7 = v5._1, v8 = v5._2;
        const v11 = v8 + 3, v14 = v7 + 4;
        const v15 = { tag: 0, _1: v11, _2: v14 };
        v3 = 0; v4 = v6; v5 = v15; continue;
      }
    }
  }
  return r;
};
const evenS0 = (n, b) => mS0(0, n, b), oddS0 = (n, b) => mS0(1, n, b);

// S1 -------------------------------------------------------------------
const mS1 = (t, n, b1, b2) => {
  let v3 = t, v4 = n, v5 = b1, v6 = b2, c = true, r1, r2;
  while (c) {
    if (v3 === 0) {
      if (v4 === 0) { c = false; r1 = v5; r2 = v6; continue; }
      else { const n1 = Math.max(0, v4 - 1), x = (v6 + 1) | 0, y = (v5 + 2) | 0; v3 = 1; v4 = n1; v5 = x; v6 = y; continue; }
    } else {
      if (v4 === 0) { c = false; r1 = v5; r2 = v6; continue; }
      else { const n1 = Math.max(0, v4 - 1), x = (v6 + 3) | 0, y = (v5 + 4) | 0; v3 = 0; v4 = n1; v5 = x; v6 = y; continue; }
    }
  }
  return { _1: r1, _2: r2 };
};
const evenS1 = (n, b) => mS1(0, n, b._1, b._2), oddS1 = (n, b) => mS1(1, n, b._1, b._2);

// S2 -------------------------------------------------------------------
const mS2 = (t, n, b1, b2) => {
  let v3 = t, v4 = n, v5 = b1, v6 = b2;
  while (true) {
    if (v3 === 0) {
      if (v4 === 0) return { _1: v5, _2: v6 };
      const n1 = Math.max(0, v4 - 1), x = (v6 + 1) | 0, y = (v5 + 2) | 0; v3 = 1; v4 = n1; v5 = x; v6 = y;
    } else {
      if (v4 === 0) return { _1: v5, _2: v6 };
      const n1 = Math.max(0, v4 - 1), x = (v6 + 3) | 0, y = (v5 + 4) | 0; v3 = 0; v4 = n1; v5 = x; v6 = y;
    }
  }
};
const evenS2 = (n, b) => mS2(0, n, b._1, b._2), oddS2 = (n, b) => mS2(1, n, b._1, b._2);

// S3 -------------------------------------------------------------------
const mS3 = (t, n, b1, b2) => {
  let v3 = t, v4 = n, v5 = b1, v6 = b2;
  while (true) {
    if (v3 === 0) {
      if (v4 === 0) return { _1: v5, _2: v6 };
      const n1 = v4 - 1, x = (v6 + 1) | 0, y = (v5 + 2) | 0; v3 = 1; v4 = n1; v5 = x; v6 = y;
    } else {
      if (v4 === 0) return { _1: v5, _2: v6 };
      const n1 = v4 - 1, x = (v6 + 3) | 0, y = (v5 + 4) | 0; v3 = 0; v4 = n1; v5 = x; v6 = y;
    }
  }
};
const evenS3 = (n, b) => mS3(0, n, b._1, b._2), oddS3 = (n, b) => mS3(1, n, b._1, b._2);

// S4 -------------------------------------------------------------------
const evenS4 = (n, b_1, b_2) => {
  while (true) {
    if (n === 0) return { _1: b_1, _2: b_2 };
    const nb1 = (b_2 + 1) | 0, nb2 = (b_1 + 2) | 0, nn = n - 1;
    if (nn === 0) return { _1: nb1, _2: nb2 };
    b_1 = (nb2 + 3) | 0; b_2 = (nb1 + 4) | 0; n = nn - 1;
  }
};
const oddS4 = (n, b_1, b_2) => {
  if (n === 0) return { _1: b_1, _2: b_2 };
  return evenS4(n - 1, (b_2 + 3) | 0, (b_1 + 4) | 0);
};

// S5 (expected output) --------------------------------------------------
const evenS5 = (n) => (b_1, b_2) => {
  while (true) {
    if (n === 0) return { _1: b_1, _2: b_2 };
    const nb1 = (b_2 + 1) | 0, nb2 = (b_1 + 2) | 0, nn = n - 1;
    if (nn === 0) return { _1: nb1, _2: nb2 };
    b_1 = (nb2 + 3) | 0; b_2 = (nb1 + 4) | 0; n = nn - 1;
  }
};
const oddS5 = (n) => (b_1, b_2) => {
  if (n === 0) return { _1: b_1, _2: b_2 };
  return evenS5(n - 1)((b_2 + 3) | 0, (b_1 + 4) | 0);
};

const N = Number(process.argv[2] ?? 1000);
const ITERS = Number(process.argv[3] ?? 20000);
const boxed = () => ({ tag: 0, _1: 10, _2: 20 });

const runs = {
  S0: () => { const r = evenS0(N, boxed()), s = oddS0(N, boxed()); return r._1 + r._2 + s._1 + s._2; },
  S1: () => { const r = evenS1(N, boxed()), s = oddS1(N, boxed()); return r._1 + r._2 + s._1 + s._2; },
  S2: () => { const r = evenS2(N, boxed()), s = oddS2(N, boxed()); return r._1 + r._2 + s._1 + s._2; },
  S3: () => { const r = evenS3(N, boxed()), s = oddS3(N, boxed()); return r._1 + r._2 + s._1 + s._2; },
  S4: () => { const r = evenS4(N, 10, 20), s = oddS4(N, 10, 20); return r._1 + r._2 + s._1 + s._2; },
  S5: () => { const r = evenS5(N)(10, 20), s = oddS5(N)(10, 20); return r._1 + r._2 + s._1 + s._2; },
};

console.log('results (must all agree):', JSON.stringify(Object.fromEntries(Object.entries(runs).map(([k, f]) => [k, f()]))));
const time = (f) => { for (let i = 0; i < 2000; i++) f(); const t0 = process.hrtime.bigint(); let a = 0; for (let i = 0; i < ITERS; i++) a += f(); return Number(process.hrtime.bigint() - t0) / 1e6; };
console.log(`N=${N} iters=${ITERS}`);
for (const round of [1, 2, 3])
  console.log(`round ${round}: ` + Object.entries(runs).map(([k, f]) => `${k}=${time(f).toFixed(1)}ms`).join('  '));
