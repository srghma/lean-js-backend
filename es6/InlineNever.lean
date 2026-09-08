prelude
import Init.System.IO

@[noinline]
def foo : String := "foo"

def test : String := foo

def main : IO Unit := do
  IO.println test
