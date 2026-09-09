prelude
import Init.System.IO
import Init.Data.String.Basic
import Init.Data.Option.Basic

def foldString : Option String → String
  | some a => a
  | none   => ""

def test : Option String → String := foldString

def main : IO Unit := do
  IO.println (repr (test (some "a")))
  IO.println (repr (test none))
