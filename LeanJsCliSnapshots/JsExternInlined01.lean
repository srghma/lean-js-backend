@[extern "js_extern_inlined_test_add", js_extern_inlined Lean.Compiler.JS.Impl.natAdd]
opaque jsExternInlinedTestAdd : Nat → Nat → Nat

def inc : Nat → Nat :=
  jsExternInlinedTestAdd 1
