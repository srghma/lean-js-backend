source_init "$1"
run_before "$1"
maybe_use_lean_header_snapshot "$1"

# Ensure LakeJs oleans exist in stage1 lib directory
if [[ -n "$BUILD_DIR" && -n "$SRC_DIR" ]]; then
  LAKEJS_LIB="${BUILD_DIR}/lib/lean/LakeJs"
  mkdir -p "$LAKEJS_LIB/JsImplOfKnownExternFunctions/Init"
  if [[ ! -f "$LAKEJS_LIB/Js.olean" || "$SRC_DIR/LakeJs/Js.lean" -nt "$LAKEJS_LIB/Js.olean" ]]; then
    lean -R "$SRC_DIR" -o "$LAKEJS_LIB/Js.olean" "$SRC_DIR/LakeJs/Js.lean"
  fi
  if [[ ! -f "$LAKEJS_LIB/Render.olean" || "$SRC_DIR/LakeJs/Render.lean" -nt "$LAKEJS_LIB/Render.olean" ]]; then
    lean -R "$SRC_DIR" -o "$LAKEJS_LIB/Render.olean" "$SRC_DIR/LakeJs/Render.lean"
  fi
  if [[ ! -f "$LAKEJS_LIB/Optimizer.olean" || "$SRC_DIR/LakeJs/Optimizer.lean" -nt "$LAKEJS_LIB/Optimizer.olean" ]]; then
    lean -R "$SRC_DIR" -o "$LAKEJS_LIB/Optimizer.olean" "$SRC_DIR/LakeJs/Optimizer.lean"
  fi
  if [[ ! -f "$LAKEJS_LIB/JsImplOfKnownExternFunctions/Init/Prelude.olean" || "$SRC_DIR/LakeJs/JsImplOfKnownExternFunctions/Init/Prelude.lean" -nt "$LAKEJS_LIB/JsImplOfKnownExternFunctions/Init/Prelude.olean" ]]; then
    lean -R "$SRC_DIR" -o "$LAKEJS_LIB/JsImplOfKnownExternFunctions/Init/Prelude.olean" "$SRC_DIR/LakeJs/JsImplOfKnownExternFunctions/Init/Prelude.lean"
  fi
fi

# `--root` to infer same private names as in the server
# Elab.inServer to allow for arbitrary `#eval`
# compiler.postponeCompile for immediate trace output
capture_only "$1" \
  lean --root=.. -DprintMessageEndPos=true -Dlinter.all=false -DElab.inServer=true -Dcompiler.postponeCompile=false "${TEST_LEAN_ARGS[@]}" "$1"
normalize_mvar_suffixes
normalize_reference_urls
normalize_measurements
check_out_file
check_exit_is_success

run_after "$1"
