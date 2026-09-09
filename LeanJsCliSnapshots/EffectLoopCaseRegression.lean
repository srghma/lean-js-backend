def test (eff : Unit → IO (Option (List String))) : IO Unit := do
  let res ← eff ()
  match res with
  | none => pure ()
