def when' (bool : Bool) (k : Unit → IO Unit) : IO Unit :=
  if bool then k () else pure ()

def test1 (bool : Bool) : IO Unit := do
