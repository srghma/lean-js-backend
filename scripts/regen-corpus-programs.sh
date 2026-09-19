#!/usr/bin/env bash
# Regenerate `<Module>Program.lean` for every module of `scripts/corpus-modules.txt`, and
# check that not one of them reports a declaration as `not translated:`.
#
# The header of a generated program keeps three things apart:
#
#   refused by the totality gate:  `partial`, `unsafe`, `IO`, a partial fixpoint — a
#                                  declaration the backend is meant to refuse;
#   outside the language:          a declaration that is not a program of `LakeJs.Ty`
#                                  at all (a `Repr`, a `Sort`-valued motive, a hash
#                                  container, a type with no values, a polymorphic
#                                  declaration no call instantiates);
#   not translated:                a declaration that *is* a program of the language
#                                  and that the front end failed on anyway.
#
# Only the third is a gap in the front end, and it must stay empty; this script exits
# non-zero if any appears.
set -euo pipefail
cd "$(dirname "$0")/.."

# the driver reads a module out of its `.olean`, so the modules of the corpus have to be
# built first — they are not default targets.  Only the sources are built here: a
# `<Module>Program.lean` of the previous run may well not compile against a changed
# grammar, and it is about to be overwritten anyway.
lake build lean-to-js-backend >/dev/null
while read -r src; do
  [ -z "$src" ] && continue
  lake build "$(echo "${src%.lean}" | tr '/' '.')" >/dev/null
done < scripts/corpus-modules.txt

while read -r src; do
  [ -z "$src" ] && continue
  echo "=> $src"
  lake env ./.lake/build/bin/lean-to-js-backend "$src"
done < scripts/corpus-modules.txt

echo
if rg -n "^-- not translated:" --glob '*Program.lean' .; then
  echo "FAIL: a generated program reports a declaration as \`not translated:\`" >&2
  exit 1
fi
echo "OK: no generated program reports \`not translated:\`"

# the run also wrote `<Module>AutoCheck.lean` for every declaration whose arguments and
# result the generator can sample: building the snapshot libraries runs those differential
# checks, which is what turns a measure the front end read wrongly — a recursion that gets
# stuck instead of descending — into a red build
echo
echo "=> building the snapshot libraries, which runs the generated differential checks"
lake build SnapshotsPBOPure SnapshotsMy SnapshotsPBOPartial
echo "OK: every generated differential check passes"
