def test (f : IO.Ref Int → IO.Ref Int) : IO Unit := do
  let ref ← IO.mkRef 0
  let wat := f ref
  let v1 ← wat.get
  wat.set (v1 + 1)
  let v2 ← ref.get
  ref.set (v2 + 1)
