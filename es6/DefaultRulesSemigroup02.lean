prelude
import Init.System.IO
import Init.Data.String.Basic
import Init.Data.List.Basic

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

def main : IO Unit := do
  let r1 := { foo := "a", bar := ["b"] : R }
  let r2 := { foo := "c", bar := ["d"] : R }
  IO.println (repr (test1 r1 r2))
  IO.println (repr (test2 r1 r2))
  IO.println (repr (test3 r1))
  IO.println (repr (test4))
