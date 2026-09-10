def test (eff : IO (Option (Array String))) : IO Unit := do
  let res ← eff
  match res with
  | none => pure ()
  | some as =>
    for a in as do
      println! a
