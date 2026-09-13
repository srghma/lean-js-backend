def test1 (ref : IO.Ref Int) (k : Int → Array Int) : IO Unit := do
  for a in k 42 do
    let val ← ref.get
    ref.set (val + a)
    let val2 ← ref.get
    ref.set (val2 + a)

def test2 (ref : IO.Ref Int) (k : Int → Array Int) : IO Unit := do
  for a in k 42 do
    let val ← ref.get
    ref.set (val + a)
  for a in k 42 do
    let val ← ref.get
    ref.set (val + a)
  for _ in k 42 do
    let val ← ref.get
    ref.set (val + 1)

def test3 (ref : IO.Ref Int) (arr : Array Int) : IO Unit := do
  for a in arr do
    if a < 10 then
      let val ← ref.get
      ref.set (val + a)

def test4 (ref : IO.Ref Int) (arr : Array Int) : IO Unit := do
  for a in arr do
    let val ← ref.get
    if a < 10 then
      ref.set (val + a)
    else
      ref.set (val + 1)
