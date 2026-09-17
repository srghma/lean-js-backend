// The check the Node suites of the `PrimOp*Configurable` snapshots run.
//
// `scripts/expectations/<Module>.json` holds what Lean answers for every export of
// `SnapshotsPBOPure/<Module>.lean` — a constant as it stands, a function at the
// arguments `scripts/gen-primop-expectations.py` lists — and this compares the
// generated JavaScript against it.  The expectations are written by Lean itself
// (`scripts/regen-primop-expectations.sh`), so nothing here is a hand-copied answer.
//
// The two representations are held to different standards, deliberately:
//
// * under `--config=faithful` (`<Module>-bigint.js`) every value is a `BigInt`, which
//   is exact at every size, so **every** answer must be Lean's;
// * under `--config=pbo` (`<Module>-num.js`) a `Nat`, an `Int`, a `USize`, a `UInt64`,
//   an `Int64` and an `ISize` are JavaScript numbers, which hold an integer exactly
//   only up to `2^53 - 1`.  Every answer inside that range must be Lean's, unless the
//   *computation* passed through a value outside it, which these snapshots do on
//   purpose (`-1 : UInt64` is `2^64 - 1`).  Those two kinds of answer are named rather
//   than asserted: `inexact` is how many answers do not fit, and `divergent` lists the
//   exports that fit but are reached through one that does not — and each of those is
//   asserted to *disagree* with Lean, so the list cannot go stale.  That is the cost of
//   the representation, and the point of having both.
import assert from "node:assert/strict";
import test from "node:test";
import { readFileSync } from "node:fs";

const EXACT = 2n ** 53n - 1n;

/** The rendering of a JavaScript answer, in the shape `Render` gives it in Lean. */
export const render = (v) => {
  if (Array.isArray(v)) return "[" + v.map(render).join(",") + "]";
  if (typeof v === "bigint") return v.toString();
  if (typeof v === "boolean") return String(v);
  if (typeof v === "number") {
    return Number.isInteger(v) ? BigInt(v).toString() : String(v);
  }
  return String(v);
};

/** The items of an expected answer: one, or the elements of an array. */
const items = (expected) =>
  expected.startsWith("[")
    ? expected
        .slice(1, -1)
        .split(",")
        .filter((s) => s.length > 0)
    : [expected];

/** Is every item of this expected answer one a JavaScript number holds exactly? */
const exactlyRepresentable = (expected) =>
  items(expected).every((s) => {
    if (s === "true" || s === "false") return true;
    const n = BigInt(s);
    return (n < 0n ? -n : n) <= EXACT;
  });

/** Is the answer a number, or a list of numbers and booleans? */
const isNumeric = (v) =>
  Array.isArray(v)
    ? v.every(isNumeric)
    : typeof v === "number" || typeof v === "bigint" || typeof v === "boolean";

/**
 * Check one generated module against the expectations of its Lean source.
 *
 * @param {object} mod the imported generated module
 * @param {string} name the name of the snapshot module
 * @param {"num"|"bigint"} repr how the numeric types are represented
 * @param {{inexact: number, divergent?: string[]}} budget what this representation
 *   cannot hold: how many answers are outside the exact range, and which exports are
 *   computed through one
 */
export const checkModule = (mod, name, repr, budget) => {
  const spec = JSON.parse(
    readFileSync(new URL(`expectations/${name}.json`, import.meta.url), "utf8"),
  );
  const lit = (s) => (repr === "bigint" ? BigInt(s) : Number(s));
  const divergent = new Set(budget.divergent ?? []);
  let inexact = 0;

  const checkOne = (key, expected, answer) => {
    const fits = repr === "bigint" || exactlyRepresentable(expected);
    if (repr === "num" && !fits) inexact += 1;
    test(key, () => {
      assert.notEqual(answer, undefined, `${key} is not exported`);
      if (divergent.has(key)) {
        // recorded as a divergence of the `num` representation: the answer fits, but
        // the way to it does not, so it must differ from Lean's — if it no longer
        // does, the entry belongs in neither list
        assert.notEqual(render(answer), expected);
      } else if (fits) {
        assert.equal(render(answer), expected);
      } else {
        assert.equal(isNumeric(answer), true);
      }
    });
  };

  for (const c of spec.calls) {
    const key = `${c.fn}(${c.args.join(", ")})`;
    const fn = mod[c.fn];
    checkOne(key, c.expected, typeof fn === "function" ? fn(...c.args.map(lit)) : undefined);
  }

  for (const v of spec.values) checkOne(v.name, v.expected, mod[v.name]);

  test(`${name}-${repr}: what the representation cannot hold`, () => {
    assert.equal(inexact, budget.inexact);
    if (repr === "bigint") assert.equal(divergent.size, 0);
  });
};
