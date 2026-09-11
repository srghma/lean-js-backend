import { run, bench, summary } from 'mitata';
import * as Impls from './bench_recursive_impl.mjs';

function generateTree(api, depth) {
  if (depth <= 0) return api.zero;
  if (depth % 2 === 0) return api.add(generateTree(api, depth - 1), generateTree(api, depth - 2));
  return api.succ(generateTree(api, depth - 1));
}

// -----------------------------------------------------------------------------
// Pre-generate static trees for pure traversal & rendering
// -----------------------------------------------------------------------------
const TRAVERSAL_DEPTH = 20; // ~40,000 nodes
const RENDER_DEPTH = 12;    // ~400 nodes

const trees = {};
for (const [key, api] of Object.entries(Impls)) {
  if (api.reset) api.reset();
  trees[key] = generateTree(api, TRAVERSAL_DEPTH);
}

const renderTrees = {};
for (const [key, api] of Object.entries(Impls)) {
  if (api.reset) api.reset();
  renderTrees[key] = generateTree(api, RENDER_DEPTH);
}

// =============================================================================
// Benchmark 1: Pure Traversal / Match Speed
// =============================================================================
summary(() => {
  bench('V1: Object + String Tag', () => Impls.V1.count(trees.V1));
  bench('V2: Object + Int Tag', () => Impls.V2.count(trees.V2));
  bench('V2: Object + Int Tag (without_empty_fields)', () => Impls.V2_without_empty_fields.count(trees.V2_without_empty_fields));
  bench('V3: Array + String Tag', () => Impls.V3.count(trees.V3));
  bench('V4: [tag: Int] (ReScript)', () => Impls.V4.count(trees.V4));
  bench('V5: Flat TypedArrays', () => Impls.V5.count(trees.V5));
  bench('V6: Uniform Class', () => Impls.V6.count(trees.V6));
  bench('V7: PureScript ES5 (inst)', () => Impls.V7.count(trees.V7));
  bench('V8: PureScript ES6 (inst)', () => Impls.V8.count(trees.V8));
});

// =============================================================================
// Benchmark 2: String Rendering Throughput
// =============================================================================
summary(() => {
  bench('V1: Object + String Tag', () => Impls.V1.render(renderTrees.V1));
  bench('V2: Object + Int Tag', () => Impls.V2.render(renderTrees.V2));
  bench('V2: Object + Int Tag (without_empty_fields)', () => Impls.V2_without_empty_fields.render(renderTrees.V2_without_empty_fields));
  bench('V3: Array + String Tag', () => Impls.V3.render(renderTrees.V3));
  bench('V4: [tag: Int] (ReScript)', () => Impls.V4.render(renderTrees.V4));
  bench('V5: Flat TypedArrays', () => Impls.V5.render(renderTrees.V5));
  bench('V6: Uniform Class', () => Impls.V6.render(renderTrees.V6));
  bench('V7: PureScript ES5 (inst)', () => Impls.V7.render(renderTrees.V7));
  bench('V8: PureScript ES6 (inst)', () => Impls.V8.render(renderTrees.V8));
});

// =============================================================================
// Benchmark 3: Construction & Allocation Speed
// =============================================================================
const CONSTRUCT_DEPTH = 16;

summary(() => {
  bench('V1: Object + String Tag', () => generateTree(Impls.V1, CONSTRUCT_DEPTH));
  bench('V2: Object + Int Tag', () => generateTree(Impls.V2, CONSTRUCT_DEPTH));
  bench('V2: Object + Int Tag (without_empty_fields)', () => generateTree(Impls.V2_without_empty_fields, CONSTRUCT_DEPTH));
  bench('V3: Array + String Tag', () => generateTree(Impls.V3, CONSTRUCT_DEPTH));
  bench('V4: [tag: Int] (ReScript)', () => generateTree(Impls.V4, CONSTRUCT_DEPTH));
  bench('V5: Flat TypedArrays', () => { Impls.V5.reset(); generateTree(Impls.V5, CONSTRUCT_DEPTH); });
  bench('V6: Uniform Class', () => generateTree(Impls.V6, CONSTRUCT_DEPTH));
  bench('V7: PureScript ES5 (inst)', () => generateTree(Impls.V7, CONSTRUCT_DEPTH));
  bench('V8: PureScript ES6 (inst)', () => generateTree(Impls.V8, CONSTRUCT_DEPTH));
});

await run();
