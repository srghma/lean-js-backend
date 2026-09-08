import Init.System.IO

@[extern "js_extern_inlined_test_add", js_extern_inlined Lean.Compiler.JS.Impl.natAdd]
opaque jsExternInlinedTestAdd : Nat → Nat → Nat

def inc : Nat → Nat :=
  jsExternInlinedTestAdd 1

def main : IO Unit := do
  IO.println (jsExternInlinedTestAdd 20 22)
  IO.println (inc 41)
