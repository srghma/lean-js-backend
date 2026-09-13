def test1 {α β : Type} (f : α → β) (as : Array α) : IO Unit := do
  let ref ← IO.mkRef #[]
  for a in as do
    let bs ← ref.get
    ref.set (bs.push (f a))
