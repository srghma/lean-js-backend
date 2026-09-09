def test1 (x y : Int) : String :=
  match x, y with
  | 1, 1 => "1.1"
  | 1, 2 => "1.2"
  | 1, 3 => "1.3"
  | _, 4 => "_.4"
  | 1, 5 => "1.5"
  | _, 2 => "_.2"
  | _, _ => "_._"


def main : IO Unit := do
  IO.println (test1 1 1)
  IO.println (test1 1 2)
  IO.println (test1 2 4)
  IO.println (test1 2 2)
