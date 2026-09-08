def test1 (x : String) : String → String :=
  let y := x ++ "!"
  fun z => y ++ z


def main : IO Unit := do
  IO.println (test1 "hello" "world")
