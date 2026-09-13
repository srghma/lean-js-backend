structure MyEffect (α : Type) where
  val : IO α

instance : Monad MyEffect where
  pure a := { val := pure a }
  bind x k := { val := do
    let a ← x.val
    (k a).val
  }

def test (random : MyEffect Int) : MyEffect Int := do
  let a ← random
  let b ← random
  pure (a + b)
