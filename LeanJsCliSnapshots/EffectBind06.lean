def test (random : Unit → IO Int) : IO Int := do
  let x ← random ()
  let n ← do
    let x ← random ()
    let y ← random ()
    pure (x + y)
  let m ← random ()
  pure (x + n - m)
