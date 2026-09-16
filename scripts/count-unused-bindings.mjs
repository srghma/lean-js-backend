// Count, in the generated JavaScript of the snapshot corpus, how many bindings are
// never mentioned again: arrow-function parameters and `const` bindings.
//
// The count is a LOWER BOUND.  Names are of the form `vN` and two sibling scopes of one
// declaration can reuse the same `N`, so a name that is unused in one scope but used in
// a sibling scope is counted here as used.  It is also purely lexical: a name mentioned
// only inside a branch that never runs counts as used.
//
// Usage: node scripts/count-unused-bindings.mjs [dir ...]

import { readdirSync, readFileSync, statSync } from 'node:fs';
import { join } from 'node:path';

const dirs = process.argv.slice(2);
if (dirs.length === 0) dirs.push('SnapshotsPBOPure', 'SnapshotsMy');

function files(dir) {
  const out = [];
  for (const e of readdirSync(dir)) {
    const p = join(dir, e);
    if (statSync(p).isDirectory()) out.push(...files(p));
    else if (e.endsWith('.js') && !e.endsWith('.expected.js')) out.push(p);
  }
  return out;
}

// Split a module into top-level declarations: a line starting with `const ` at column 0
// opens one, and the next such line (or the `export` line) closes it.
function decls(src) {
  const lines = src.split('\n');
  const out = [];
  let cur = null;
  for (const line of lines) {
    if (/^const /.test(line)) {
      if (cur) out.push(cur);
      cur = { name: /^const ([A-Za-z0-9_$]+)/.exec(line)[1], text: line };
    } else if (/^export /.test(line)) {
      if (cur) out.push(cur);
      cur = null;
    } else if (cur) {
      cur.text += '\n' + line;
    }
  }
  if (cur) out.push(cur);
  return out;
}

let totals = { params: 0, unusedParams: 0, consts: 0, unusedConsts: 0 };
const offenders = [];

for (const dir of dirs) {
  for (const file of files(dir)) {
    const src = readFileSync(file, 'utf8');
    for (const d of decls(src)) {
      const binds = new Map(); // name -> number of binding occurrences
      const kind = new Map(); // name -> 'param' | 'const'
      // parameters of every arrow function
      for (const m of d.text.matchAll(/\(([^()]*)\)\s*=>/g)) {
        for (const raw of m[1].split(',')) {
          const p = raw.trim();
          if (!p) continue;
          binds.set(p, (binds.get(p) ?? 0) + 1);
          if (!kind.has(p)) kind.set(p, 'param');
        }
      }
      // `const x = ...` and `let x = ...` inside the declaration
      for (const m of d.text.matchAll(/(?:^|\n)\s+(?:const|let) ([A-Za-z0-9_$]+)\s*=/g)) {
        const p = m[1];
        binds.set(p, (binds.get(p) ?? 0) + 1);
        if (!kind.has(p)) kind.set(p, 'const');
      }
      for (const [name, nbinds] of binds) {
        const esc = name.replace(/[$]/g, '\\$');
        const uses = [...d.text.matchAll(new RegExp(`(?<![A-Za-z0-9_$])${esc}(?![A-Za-z0-9_$])`, 'g'))].length;
        const isParam = kind.get(name) === 'param';
        if (isParam) totals.params += nbinds; else totals.consts += nbinds;
        if (uses <= nbinds) {
          if (isParam) totals.unusedParams += nbinds; else totals.unusedConsts += nbinds;
          offenders.push(`${file}: ${d.name}: ${kind.get(name)} ${name}`);
        }
      }
    }
  }
}

console.log(`parameters:     ${totals.params} bound, ${totals.unusedParams} never mentioned again`);
console.log(`const bindings: ${totals.consts} bound, ${totals.unusedConsts} never mentioned again`);
console.log('');
for (const o of offenders) console.log(o);
