-- @js_export: test1, test2, test3
def test1 : Int := Id.run (pure 1)
def test2 : Int := Id.run (pure (1 + 2))
def test3 : Int := Id.run do
  let n := 1
  let m := 2
  pure (n + m)
