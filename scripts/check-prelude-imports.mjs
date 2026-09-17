// Every name a generated module imports from its runtime prelude must be exported by
// that prelude.  A missing one is a `SyntaxError` at load time, which this reports as a
// list rather than as the first failure.
//
//     node scripts/check-prelude-imports.mjs
import { readFileSync } from "node:fs";
import { resolve, dirname } from "node:path";
import { pathToFileURL } from "node:url";

const files = readFileSync("scripts/snapshot-files.txt", "utf8")
  .trim()
  .split("\n")
  .map((line) => line.split(" ")[0])
  .filter(Boolean);

let missing = 0;
for (const file of files) {
  const src = readFileSync(file, "utf8");
  const m = src.match(/^import \{([^}]*)\} from "([^"]+)";/ms);
  if (!m) continue; // the module calls no extern
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

if (missing !== 0) {
  console.error(`=> ${missing} imported name(s) the prelude does not have`);
  process.exit(1);
}
console.log(`=> every name the ${files.length} generated modules import exists`);
