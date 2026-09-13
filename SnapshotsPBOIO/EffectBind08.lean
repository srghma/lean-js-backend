def test : IO Int := do
  let a ← (pure 12 : IO Int)
  pure (a + 1)
