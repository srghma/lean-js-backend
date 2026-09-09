def test1 : Int := Id.run (pure 1)
def test2 (random : Unit → IO Int) : IO Int := do
  let n ← random ()
  let m ← random ()
  pure (n + m)
