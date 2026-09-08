prelude
import Init.System.IO

inductive Test where | Foo | Bar | Baz | Qux
deriving Repr

def main : IO Unit := do
  IO.println (repr Test.Foo)
  IO.println (repr Test.Bar)
  IO.println (repr Test.Baz)
  IO.println (repr Test.Qux)
