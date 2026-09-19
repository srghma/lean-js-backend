#!/usr/bin/env bash
# Translate *every* module of the snapshot libraries — not just the corpus of
# `scripts/corpus-modules.txt` — and check that not one declaration is reported as
# `not translated:`.
#
# Nothing is written: each module is translated in `--check` mode and only the verdict is
# read.  A declaration the front end declines has to be declined either
#
#   * by the totality gate (`partial`, `unsafe`, `IO`, a partial fixpoint), or
#   * as outside the language (not a program of `LakeJs.Ty` at all),
#
# with the reason named.  `was not translated` — a declaration that *is* a program of the
# language and that the front end failed on anyway — is a gap in the front end, and this
# script exits non-zero if a single one appears.
set -euo pipefail
cd "$(dirname "$0")/.."

lake build lean-to-js-backend SnapshotsPBOPure SnapshotsMy SnapshotsPBOIO \
  SnapshotsPBOPartial >/dev/null

log=$(mktemp)
trap 'rm -f "$log"' EXIT

mods=()
while read -r src; do
  mods+=("$src")
done < <(ls SnapshotsPBOPure/*.lean SnapshotsMy/*.lean SnapshotsPBOIO/*.lean \
         SnapshotsPBOPartial/*.lean \
         | grep -v 'Program\.lean$' | grep -v 'Check\.lean$')

echo "sweeping ${#mods[@]} modules"
# `--no-check` skips the elaboration of the generated source: this sweep is about the
# translation verdict, and `scripts/regen-corpus-programs.sh` is what elaborates.
lake env ./.lake/build/bin/lean-to-js-backend --check --no-check "${mods[@]}" \
  > "$log" 2>&1 || true

if grep -n "was not translated" "$log"; then
  echo "FAIL: a declaration of the language was not translated" >&2
  exit 1
fi
grep -c ": ok (" "$log" | sed 's/^/modules translated: /'
echo "OK: no declaration is reported as \`not translated\`"
