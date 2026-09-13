def test1 (hi : Int) : IO Int := do
  let count ← IO.mkRef 0
  let continue_ ← IO.mkRef true
  while (← continue_.get) do
    let n ← count.get
    if n < hi then
      count.set (n + 1)
    else
      continue_.set false
  count.get

def test2 : IO (Int → IO Unit) := do
  let count ← IO.mkRef 0
  pure fun n => count.modify (· + n)

def test3 : IO (IO.Ref Int × (Int → IO Unit)) := do
  let count ← IO.mkRef 0
  pure (count, fun n => count.modify (· + n))
