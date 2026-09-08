prelude
import Init.System.IO

inductive TestEnum where
  | foo
  | bar
  | baz
  | qux
deriving BEq

def test1 (a : TestEnum) : Bool := .baz == a
def test2 (a : TestEnum) : Bool := a == .baz

def main : IO Unit := do
  IO.println (test1 .baz)
  IO.println (test2 .foo)
