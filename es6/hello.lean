def hello (x : Nat) : Nat :=
  let y := 1
  x + y

def main : IO Unit := do
  IO.println (hello 5)
