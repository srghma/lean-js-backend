def test1 : IO Unit := IO.println 12

def test2 (random : Unit → IO Int) : IO Unit := do
  let log := fun (n : Int) => IO.println n
  let n ← random ()
  log n
