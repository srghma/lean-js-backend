prelude
import Init.System.IO
import Init.Data.Int.Basic

structure MyEffect (α : Type) where
  val : IO α

instance : Monad MyEffect where
  pure a := { val := pure a }
  bind x k := { val := do
    let a ← x.val
    (k a).val
  }

def test : MyEffect Int := do
  let a ← ({ val := pure 1 } : MyEffect Int)
  let b ← ({ val := pure 1 } : MyEffect Int)
  pure (a + b)

def main : IO Unit := do
  IO.println 2
