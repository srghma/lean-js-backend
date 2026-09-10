def MyId (α : Type) := Unit → α

instance : Monad MyId where
  pure a := fun _ => a
  bind x k := k (x ())

-- #print instMonadMyId

def test1 (k : Unit → IO Unit) : IO Unit := do
  let _ ← pure ()
  k ()

def test2 {α : Type} (k : Unit → MyId α) : MyId α := do
  let _ ← pure ()
  k ()
