partial def whileE (cond : IO Bool) (m : IO Unit) : IO Unit := do
  let c ← cond
  if c then
    m
    whileE cond m
  else
    pure ()

def test1 (cond : IO.Ref Bool) (ref : IO.Ref Int) : IO Unit :=
  whileE (cond.get) do
    let val ← ref.get
    ref.set (val + 1)
    let val2 ← ref.get
    ref.set (val2 + 2)

def test2 (cond : IO.Ref Bool) (ref : IO.Ref Int) : IO Unit := do
  whileE (cond.get) do
    let val ← ref.get
    ref.set (val + 1)
  whileE (cond.get) do
    let val ← ref.get
    ref.set (val + 2)

def test3 (cond : IO.Ref Bool) (ref : IO.Ref Int) : IO Unit :=
  whileE (cond.get) do
    let a ← ref.get
    if a < 10 then
      ref.set (a + 1)

def test4 (cond : IO.Ref Bool) (ref : IO.Ref Int) : IO Unit :=
  whileE (cond.get) do
    let a ← ref.get
    if a < 10 then
      ref.set (a + 1)
    else
      ref.set (a + 2)
