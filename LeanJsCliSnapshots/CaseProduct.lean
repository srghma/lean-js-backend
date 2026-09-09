structure Product3 where
  a : Nat
  b : Nat
  c : Nat

def test1 (v : Product3) : String :=
  match v with
  | ⟨1, 2, 3⟩ => "1"
  | ⟨_, 4, _⟩ => "2"
  | ⟨4, 5, 6⟩ => "3"
  | _ => "catch"


def main : IO Unit := do
  IO.println (test1 (.mk 1 2 3))
