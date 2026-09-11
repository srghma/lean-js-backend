import { run, bench, summary } from 'mitata';

// Prevent Dead-Code Elimination
let SINK = null;
function blackhole(val) {
  SINK = val;
}

// =============================================================================
// Non-Recursive Variant Implementations
// =============================================================================

// 1. Object + String Tag
export const V1 = {
  add: (a, b) => ({ tag: "add", _1: a, _2: b }),
  mul: (a, b) => ({ tag: "mul", _1: a, _2: b }),
  succ: a => ({ tag: "succ", _1: a }),
  zero: { tag: "zero" },
  eval: v => {
    if (v.tag === "add") return v._1 + v._2;
    if (v.tag === "mul") return v._1 * v._2;
    if (v.tag === "succ") return v._1 + 1;
    return 0;
  }
};

// 2. Object + Int Tag
export const V2 = {
  add: (a, b) => ({ tag: 0, _1: a, _2: b }),
  mul: (a, b) => ({ tag: 1, _1: a, _2: b }),
  succ: a => ({ tag: 2, _1: a, _2: 0 }),
  zero: { tag: 3, _1: 0, _2: 0 },
  eval: v => {
    switch (v.tag) {
      case 0: return v._1 + v._2;
      case 1: return v._1 * v._2;
      case 2: return v._1 + 1;
      default: return 0;
    }
  }
};

// 3. Array + String Tag
export const V3 = {
  add: (a, b) => ["add", a, b],
  mul: (a, b) => ["mul", a, b],
  succ: a => ["succ", a],
  zero: ["zero"],
  eval: v => {
    const t = v[0];
    if (t === "add") return v[1] + v[2];
    if (t === "mul") return v[1] * v[2];
    if (t === "succ") return v[1] + 1;
    return 0;
  }
};

// 4. Array + Int Tag (ReScript / OCaml style)
export const V4 = {
  add: (a, b) => [0, a, b],
  mul: (a, b) => [1, a, b],
  succ: a => [2, a],
  zero: 3, // unboxed integer leaf
  eval: v => {
    if (typeof v === "number") return 0;
    switch (v[0]) {
      case 0: return v[1] + v[2];
      case 1: return v[1] * v[2];
      default: return v[1] + 1;
    }
  }
};

// 6. Monomorphic Single Class
class NodeClass {
  constructor(tag, a, b) {
    this.tag = tag;
    this._1 = a;
    this._2 = b;
  }
}
const zeroNode = new NodeClass(3, 0, 0);

export const V6 = {
  add: (a, b) => new NodeClass(0, a, b),
  mul: (a, b) => new NodeClass(1, a, b),
  succ: a => new NodeClass(2, a, 0),
  zero: zeroNode,
  eval: v => {
    switch (v.tag) {
      case 0: return v._1 + v._2;
      case 1: return v._1 * v._2;
      case 2: return v._1 + 1;
      default: return 0;
    }
  }
};

// 8. Modern PureScript (ES6 Subclasses + instanceof)
class Expr { }
class PS_Add extends Expr { constructor(a, b) { super(); this.v0 = a; this.v1 = b; } }
class PS_Mul extends Expr { constructor(a, b) { super(); this.v0 = a; this.v1 = b; } }
class PS_Succ extends Expr { constructor(a) { super(); this.v0 = a; } }
class PS_Zero extends Expr { }
const psZero = new PS_Zero();

export const V8 = {
  add: (a, b) => new PS_Add(a, b),
  mul: (a, b) => new PS_Mul(a, b),
  succ: a => new PS_Succ(a),
  zero: psZero,
  eval: v => {
    if (v instanceof PS_Add) return v.v0 + v.v1;
    if (v instanceof PS_Mul) return v.v0 * v.v1;
    if (v instanceof PS_Succ) return v.v0 + 1;
    return 0;
  }
};

// =============================================================================
// 9. ZERO ALLOCATION: Unboxed Stack/Registers Passing (Tag + Fields as arguments)
// =============================================================================
export const V9 = {
  // Evaluator directly accepts (tag, _1, _2) on the stack
  eval: (tag, a, b) => {
    switch (tag) {
      case 0: return a + b;
      case 1: return a * b;
      case 2: return a + 1;
      default: return 0;
    }
  },
  // Dispatch helpers (simulating passing constructor values without boxing)
  add: (fn, a, b) => fn(0, a, b),
  mul: (fn, a, b) => fn(1, a, b),
  succ: (fn, a) => fn(2, a, void 0),
  zero: (fn) => fn(3, void 0, void 0)
};

// =============================================================================
// Benchmarks
// =============================================================================

// Scenario A: Pipe / Process 1,000,000 expressions in a tight loop
// Simulates parsing or evaluating a stream of non-recursive ADT values
const N = 500_000;

summary(() => {
  bench('9. Zero-Alloc (Stack / void 0)', () => {
    let sum = 0;
    for (let i = 0; i < N; i++) {
      const kind = i & 3;
      if (kind === 0) sum += V9.eval(0, i, 42);
      else if (kind === 1) sum += V9.eval(1, i, 2);
      else if (kind === 2) sum += V9.eval(2, i, void 0);
      else sum += V9.eval(3, void 0, void 0);
    }
    blackhole(sum);
  });

  bench('2. Object + Int Tag', () => {
    let sum = 0;
    for (let i = 0; i < N; i++) {
      const kind = i & 3;
      const v = (kind === 0) ? V2.add(i, 42)
        : (kind === 1) ? V2.mul(i, 2)
          : (kind === 2) ? V2.succ(i)
            : V2.zero;
      sum += V2.eval(v);
    }
    blackhole(sum);
  });

  bench('6. Uniform Class Instance', () => {
    let sum = 0;
    for (let i = 0; i < N; i++) {
      const kind = i & 3;
      const v = (kind === 0) ? V6.add(i, 42)
        : (kind === 1) ? V6.mul(i, 2)
          : (kind === 2) ? V6.succ(i)
            : V6.zero;
      sum += V6.eval(v);
    }
    blackhole(sum);
  });

  bench('1. Object + String Tag', () => {
    let sum = 0;
    for (let i = 0; i < N; i++) {
      const kind = i & 3;
      const v = (kind === 0) ? V1.add(i, 42)
        : (kind === 1) ? V1.mul(i, 2)
          : (kind === 2) ? V1.succ(i)
            : V1.zero;
      sum += V1.eval(v);
    }
    blackhole(sum);
  });

  bench('4. [tag: Int] (ReScript)', () => {
    let sum = 0;
    for (let i = 0; i < N; i++) {
      const kind = i & 3;
      const v = (kind === 0) ? V4.add(i, 42)
        : (kind === 1) ? V4.mul(i, 2)
          : (kind === 2) ? V4.succ(i)
            : V4.zero;
      sum += V4.eval(v);
    }
    blackhole(sum);
  });

  bench('8. PureScript ES6 (instanceof)', () => {
    let sum = 0;
    for (let i = 0; i < N; i++) {
      const kind = i & 3;
      const v = (kind === 0) ? V8.add(i, 42)
        : (kind === 1) ? V8.mul(i, 2)
          : (kind === 2) ? V8.succ(i)
            : V8.zero;
      sum += V8.eval(v);
    }
  });
});

await run();
