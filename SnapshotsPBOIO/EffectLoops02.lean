def test1 (lo hi : Nat) : IO Unit := do
  for a in [lo + 1 : hi + 1] do
    IO.println a
    IO.println a

def test2 (lo hi : Nat) : IO Unit := do
  for a in [lo + 1 : hi + 1] do
    IO.println a
  for a in [lo + 1 : hi + 1] do
    IO.println a
  for _ in [lo + 1 : hi + 1] do
    IO.println "wat"

def test3 (lo hi : Nat) : IO Unit := do
  for a in [lo : hi] do
    if a < 10 then
      IO.println a

def test4 (lo hi : Nat) : IO Unit := do
  for a in [lo : hi] do
    if a < 10 then
      IO.println a
    else
      IO.println "wat"
