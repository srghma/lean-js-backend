#!/usr/bin/env bash
# Generates .lean.out.expected for all es6 test files by compiling to native and running.
set -euo pipefail

export LEAN_BIN="${LEAN_BIN:-lean}"
export LEANC_BIN="${LEANC_BIN:-leanc}"
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

export TMPDIR="$(mktemp -d)"
trap 'rm -rf "$TMPDIR"' EXIT

FILES=("$@")
if [ ${#FILES[@]} -eq 0 ]; then
  FILES=("$DIR"/*.lean)
fi

printf '%s\0' "${FILES[@]}" | xargs -0 -n1 -P "$(nproc)" bash -c '
  set -euo pipefail
  lean_file="$1"
  [[ "$lean_file" == *"_tmp_test.lean"* ]] && exit 0

  name="$(basename "$lean_file" .lean)"
  c_file="$TMPDIR/${name}.c"
  bin_file="$TMPDIR/${name}"
  expected_file="${lean_file}.out.expected"

  if ! "$LEAN_BIN" -c "$c_file" "$lean_file" 2>/dev/null; then
    echo "  $name ... SKIP (lean -c failed)"
    exit 0
  fi

  if ! "$LEANC_BIN" -o "$bin_file" "$c_file" 2>/dev/null; then
    echo "  $name ... SKIP (leanc link failed)"
    exit 0
  fi

  if "$bin_file" >"$expected_file" 2>&1; then
    echo "  $name ... OK"
  else
    echo "  $name ... FAILED (exit $?)"
    exit 1
  fi
' bash
