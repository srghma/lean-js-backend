import Init.System.IO
import Init.Data.Int.Basic

def MyEffect (α : Type) := IO α

instance : Monad MyEffect := inferInstanceAs (Monad IO)

def test (random : Unit → MyEffect Int) : MyEffect Int := do
  let a ← random ()
  let b ← random ()
  pure (a + b)
