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
