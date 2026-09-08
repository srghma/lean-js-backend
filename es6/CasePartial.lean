prelude
import Init.System.IO
import Init.Data.Int.Basic

def test1Opt : Int → Option Int
  | 1 => some 1
  | 2 => some 2
  | 3 => some 3
  | _ => none

def main : IO Unit := do
  IO.println (repr (test1Opt 1))
  IO.println (repr (test1Opt 3))
  IO.println (repr (test1Opt 9))
