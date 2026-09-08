prelude
import Init.System.IO

structure Input where
  bar : String

structure Output where
  foo : Int
  bar : String
deriving Repr

def test (a : Input) : Output :=
  { foo := 42, bar := a.bar }

def main : IO Unit := do
  IO.println (repr (test { bar := "hi" }))
