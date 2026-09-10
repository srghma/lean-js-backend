def test1 (cond : IO.Ref Bool) : IO Unit := do
  while (← cond.get) do
    IO.println "foo"
    IO.println "bar"

def test2 (cond : IO.Ref Bool) : IO Unit := do
  while (← cond.get) do
    IO.println "foo"
  while (← cond.get) do
    IO.println "bar"

def test3 (cond : IO.Ref Bool) (ref : IO.Ref Int) : IO Unit := do
  while (← cond.get) do
    let a ← ref.get
    if a < 10 then
      IO.println "foo"

def test4 (cond : IO.Ref Bool) (ref : IO.Ref Int) : IO Unit := do
  while (← cond.get) do
    let a ← ref.get
    if a < 10 then
      IO.println "foo"
    else
      IO.println "wat"
