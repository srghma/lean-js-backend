-- will use mutating property, bc `let` + `export` = `const`
initialize counter : IO.Ref Nat ← IO.mkRef 0

def test1 : Int :=
  unsafe (unsafeBaseIO (pure 1))

def test2 (random : BaseIO Int) : Int := unsafe (unsafeBaseIO (do
  let n ← random
  let m ← random
  pure (n + m)))
