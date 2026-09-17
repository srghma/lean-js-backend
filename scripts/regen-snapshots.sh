#!/usr/bin/env bash
# Regenerate the JavaScript of the snapshot modules that `scripts/snapshot-files.txt`
# lists, with the `lean-to-js-backend` executable of this package.
#
# A line of that file is one generated `.js` file, and the *name* says which
# configuration generates it — nothing else has to be written down:
#
#   <Module>-num.js      `<Module>.lean` at `--config=pbo`      (numbers)
#   <Module>-bigint.js   `<Module>.lean` at `--config=faithful` (BigInts)
#   <Module>.js          `<Module>.lean` at the default configuration
#
# so `XxxConfigurable.lean` has a `XxxConfigurable-num.js` and a
# `XxxConfigurable-bigint.js`, and `XxxNonConfigurable.lean` — whose types no knob can
# change — has a single `XxxNonConfigurable.js`.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build lean-to-js-backend >/dev/null
while read -r js; do
  [ -z "$js" ] && continue
  base="${js%.js}"
  flags=()
  case "$base" in
    *-num) base="${base%-num}"; flags=("--config=pbo") ;;
    *-bigint) base="${base%-bigint}"; flags=("--config=faithful") ;;
  esac
  echo "=> $js"
  lake env ./.lake/build/bin/lean-to-js-backend "${flags[@]}" "$base.lean"
done < scripts/snapshot-files.txt

# The programs of single declarations, which `scripts/snapshot-decls.txt` lists as
#
#   <path/to/Module.lean> <declaration>
#
# Each one is that declaration, everything it calls and everything they call, down to
# the functions the runtime implements — the closure `#lean_to_lean_term` prints — and
# is written to `<Module>-<declaration>.js` beside `<Module>-<declaration>-Program.txt`.
while read -r src decl; do
  [ -z "$src" ] && continue
  echo "=> ${src%.lean}-$decl.js"
  lake env ./.lake/build/bin/lean-to-js-backend "--decl=$decl" "$src"
done < scripts/snapshot-decls.txt
