// Where the merged dispatch loop wins: a mutual group whose next member is
// data-dependent, so the cycle cannot be unrolled into one member's loop.
//
//   f n a = if n = 0 then a else (if a % 3 = 0 then g else h) (n-1) (a+1)
//   g n a = if n = 0 then a else f (n-1) (a+2)
//   h n a = if n = 0 then a else (if a % 5 = 0 then f else g) (n-1) (a+3)
//
// "calls": each member is its own JS function and tail calls its successor,
//          i.e. what you get if you only self-TCO each member (the fallback
//          when unrolling is not applicable).
// "merged": the merged dispatch loop this backend emits.
//
// Run: node scripts/bench-mutual-loop-robust.mjs [N] [iters]

// --- mutual calls ------------------------------------------------------
const f_c = (n, a) => n === 0 ? a : (a % 3 === 0 ? g_c(n - 1, a + 1) : h_c(n - 1, a + 1));
const g_c = (n, a) => n === 0 ? a : f_c(n - 1, a + 2);
const h_c = (n, a) => n === 0 ? a : (a % 5 === 0 ? f_c(n - 1, a + 3) : g_c(n - 1, a + 3));

// --- merged dispatch loop ---------------------------------------------
const mut = (t, n, a) => {
  let vt = t, vn = n, va = a;
  while (true) {
    if (vn === 0) return va;
    if (vt === 0) { const nt = (va % 3 === 0) ? 1 : 2; vt = nt; vn = vn - 1; va = va + 1; }
    else if (vt === 1) { vt = 0; vn = vn - 1; va = va + 2; }
    else { const nt = (va % 5 === 0) ? 0 : 1; vt = nt; vn = vn - 1; va = va + 3; }
  }
};
const f_m = (n, a) => mut(0, n, a);

const N = Number(process.argv[2] ?? 1000);
const ITERS = Number(process.argv[3] ?? 20000);

console.log('agreement:', f_c(N, 0), f_m(N, 0));

const time = (f) => { for (let i = 0; i < 2000; i++) f(); const t0 = process.hrtime.bigint(); let s = 0; for (let i = 0; i < ITERS; i++) s += f(); return Number(process.hrtime.bigint() - t0) / 1e6; };
console.log(`N=${N} iters=${ITERS}`);
for (const r of [1, 2, 3])
  console.log(`round ${r}: calls=${time(() => f_c(N, 0)).toFixed(1)}ms  merged=${time(() => f_m(N, 0)).toFixed(1)}ms`);

// --- stack behaviour ---------------------------------------------------
for (const depth of [100000, 1000000]) {
  let outCalls;
  try { outCalls = String(f_c(depth, 0)); } catch (e) { outCalls = e.constructor.name + ': ' + e.message; }
  let outMerged;
  try { outMerged = String(f_m(depth, 0)); } catch (e) { outMerged = e.constructor.name + ': ' + e.message; }
  console.log(`depth ${depth}: calls -> ${outCalls} | merged -> ${outMerged}`);
}
