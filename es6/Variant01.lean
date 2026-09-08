prelude
import Init.System.IO
import Init.Data.String.Basic
import Init.Data.Int.Basic
import Init.Data.Bool

inductive Variant where
  | foo : Int → Variant
  | bar : Bool → Variant
  | baz : String → Variant

def test1 : Variant → String
  | Variant.foo i => toString i
  | Variant.bar b => toString b
  | Variant.baz s => s

def main : IO Unit := do
  IO.println (test1 (Variant.foo 42))
  IO.println (test1 (Variant.bar true))
  IO.println (test1 (Variant.baz "hi"))
