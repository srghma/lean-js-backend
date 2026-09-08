structure NewTypeInt where
  val : Nat

def test1 (v : NewTypeInt) : String :=
  match v.val with
  | 1 => "1"
  | 2 => "2"
  | 3 => "3"
  | _ => "catch"

def test2 : NewTypeInt → String
  | ⟨1⟩ => "1"
  | ⟨2⟩ => "2"
  | ⟨3⟩ => "3"
  | _ => "catch"


def main : IO Unit := do
  IO.println (test1 (.mk 42))
  IO.println (test2 (.mk 42))
