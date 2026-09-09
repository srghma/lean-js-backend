structure R where
  foo : String
  bar : List String
deriving Repr

def appendR (a b : R) : R :=
  { foo := a.foo ++ b.foo, bar := a.bar ++ b.bar }

def test1 : R → R → R := appendR
def test2 (a b : R) : R := appendR a b
def test3 : R → R := appendR { foo := "hello", bar := ["hello"] }
def test4 : R := appendR { foo := "hello", bar := ["hello"] } { foo := ", World!", bar := ["World!"] }
