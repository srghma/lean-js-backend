// Every name a generated module imports from the runtime prelude must be exported by
// the module of the prelude it is imported from.  A missing one is a `SyntaxError` at
// load time, which this reports as a list rather than as the first failure.
//
// The prelude is split by knob — `lean_runtime_non_configurable.mjs` and one module per
// configurable type and representation — so a generated module has one import per part
// of it that the module calls into, and every one of them is checked.
//
// Every `.js` file in the snapshot directories is read, not only the ones
// `scripts/snapshot-files.txt` drives, so a generated module that calls a runtime
// function nothing has implemented yet is caught wherever it sits.
//
//     node scripts/check-prelude-imports.mjs
import { readFileSync, globSync } from "node:fs";
import { resolve, dirname } from "node:path";
import { pathToFileURL } from "node:url";

const files = globSync("Snapshots*/*.js")
  .filter((f) => !f.endsWith(".test.js"))
  .sort();

let missing = 0;
for (const file of files) {
  const src = readFileSync(file, "utf8");
  for (const m of src.matchAll(/^import \{([^}]*)\} from "([^"]+)";/gms)) {
    const names = m[1]
      .split(",")
      .map((s) => s.trim())
      .filter(Boolean);
    // the specifier is relative to the generated module, not to this script
    const prelude = pathToFileURL(resolve(dirname(file), m[2])).href;
    const mod = await import(prelude);
    for (const name of names) {
      if (!(name in mod)) {
        console.error(`${file}: ${m[2]} does not export ${name}`);
        missing += 1;
      }
    }
  }
}

if (missing !== 0) {
  console.error(`=> ${missing} imported name(s) the prelude does not have`);
  process.exit(1);
}
console.log(`=> every name the ${files.length} generated modules import exists`);
