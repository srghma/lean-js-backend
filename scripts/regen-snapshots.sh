#!/usr/bin/env bash
# Regenerate the JavaScript of the snapshot modules that `scripts/snapshot-files.txt`
# lists, with the `lean-to-js-backend` executable of this package.
#
# A line of that file is the generated `.js` file, optionally followed by the name of
# the configuration it is generated with (`pbo` or `faithful`).  A configured module is
# named after its configuration — `<Module>-num.js` and `<Module>-bigint.js` — so the
# Lean source of such a line is its name with the suffix removed.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build lean-to-js-backend >/dev/null
while read -r js cfg; do
  [ -z "$js" ] && continue
  base="${js%.js}"
  flags=()
  case "$cfg" in
    "") ;;
    pbo) base="${base%-num}"; flags=("--config=pbo") ;;
    faithful) base="${base%-bigint}"; flags=("--config=faithful") ;;
    *) echo "unknown configuration '$cfg' for $js" >&2; exit 1 ;;
  esac
  echo "=> $js"
  lake env ./.lake/build/bin/lean-to-js-backend "${flags[@]}" "$base.lean"
done < scripts/snapshot-files.txt
