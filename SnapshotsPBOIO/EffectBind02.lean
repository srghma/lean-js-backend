private def MyEffect (α : Type) := IO α

private instance : Monad MyEffect := inferInstanceAs (Monad IO)

def test (random : MyEffect Int) : MyEffect Int := do
  let a ← random
  let b ← random
  pure (a + b)
