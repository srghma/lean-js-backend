prelude
import Init.System.IO
import Init.Data.String.Basic

inductive Test where | Foo | Bar | Baz | Qux

def fromString : String → Option Test
  | "foo" => some Test.Foo
  | "bar" => some Test.Bar
  | "baz" => some Test.Baz
  | "qux" => some Test.Qux
  | _ => none

def test (a : String) : Int :=
  match fromString a with
  | some Test.Foo => 1
  | some Test.Bar => 2
  | some Test.Baz => 3
  | some Test.Qux => 4
  | none => 0

def main : IO Unit := do
  IO.println (test "foo")
  IO.println (test "bar")
  IO.println (test "baz")
  IO.println (test "qux")
  IO.println (test "wat")
