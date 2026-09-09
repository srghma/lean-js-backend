prelude
import Init.System.IO

partial def test (n : Nat) : Nat :=
  let k (wat : Bool) : Nat :=
    let j (i : Nat) (_ : Unit) : Nat := test i
    if wat then j (n - 1) ()
    else n
  if n == 0 then k false
  else k true

def main : IO Unit := do
  IO.println (test 10)
