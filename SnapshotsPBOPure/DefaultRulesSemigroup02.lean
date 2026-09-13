structure R where
  foo : String
  bar : Array String
deriving Repr

-- since appendR is not marked with @[inline] - it will not be inlined by JS optimizer,
-- but /* #__PURE__ */ still will be added
def appendR (a b : R) : R :=
  { foo := a.foo ++ b.foo, bar := a.bar ++ b.bar }

def test1 : R → R → R := appendR
def test2 (a b : R) : R := appendR a b -- TODO: not sure, maybe output should just `const test2 = appendR` too?
def test3 : R → R := appendR { foo := "hello", bar := #["hello"] }
def test4 : R := appendR { foo := "hello", bar := #["hello"] } { foo := ", World!", bar := #["World!"] }
