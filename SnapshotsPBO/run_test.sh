source_init "$1"

echo "Compiling to JS"
run_before "$1"

lean -A "$1.js" -Dcompiler.postponeCompile=false -Djavascript.extern_path="$(dirname "${BASH_SOURCE[0]}")/../../src/Init/System/IO.js" "${TEST_LEAN_ARGS[@]}" "$1" || fail "Failed to compile $1 to $1.js"

CAPTURED="$1.js"

override=1
if [[ $override -eq 1 ]]; then
  cp "$1.js" "$1.js.expected"
else
  if [[ -f "$1.js.expected" ]]; then
    $DIFF -- "$1.js.expected" "$1.js" || fail "Unexpected JS output"
  else
    fail "Missing $1.js.expected"
  fi
fi

# Only run node execution if there's a .out.expected file
if [[ -f "$1.out.expected" ]]; then
  echo "Running with Node"
  # Runner script location (alongside run_test.sh)
  RUNNER_JS="$(dirname "${BASH_SOURCE[0]}")/runner.js"
  node "$1.js" > "$1.js.out" || fail "Failed to run $1.js with Node"
  CAPTURED="$1.js.out"
  $DIFF -- "$1.out.expected" "$1.js.out" || fail "JS node output does not match expected output"
fi

run_after "$1"
exit 0
