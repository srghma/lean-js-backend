#!/usr/bin/env bash
# Regenerate `scripts/expectations/<Module>.json`: what Lean answers for every export of
# the `PrimOp*Configurable` snapshots.
#
# The Lean programs that print them are themselves generated, by
# `scripts/gen-primop-expectations.py`; the snapshots declare the same names, so there
# is one program per module rather than one for all of them.  The Node suites of the
# generated JavaScript read the JSON, so re-run this after changing a snapshot.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build SnapshotsPBOPure >/dev/null
for module in \
  PrimOpInt01Configurable \
  PrimOpInt02Configurable \
  PrimOpInt03Configurable \
  PrimOpIntBit01Configurable \
  PrimOpIntBit02Configurable; do
  echo "=> scripts/expectations/$module.json"
  lake env lean --run "scripts/expectations/$module.lean" \
    > "scripts/expectations/$module.json"
done
