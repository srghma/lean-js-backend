prelude
import Init.System.IO
import Init.Data.Int.Basic
import Init.Data.String.Basic

def test1 (f g : Int → String) : Int → String := fun x => f x ++ g x
def test2 (f g : Int → String) : Int → String := fun x => f x ++ g x ++ f x ++ g x

def main : IO Unit := do
  let f := fun (i : Int) => "f" ++ toString i
  let g := fun (i : Int) => "g" ++ toString i
  IO.println (test1 f g 42)
  IO.println (test2 f g 42)
