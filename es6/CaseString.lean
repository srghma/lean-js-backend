def test1 (x : String) : String :=
  match x with
  | "foo" => "1"
  | "bar" => "2"
  | "" => "3"
  | _ => "catch"


def main : IO Unit := do
  IO.println (test1 "foo")
  IO.println (test1 "bar")
  IO.println (test1 "wat")
