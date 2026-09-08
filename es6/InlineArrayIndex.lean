prelude
import Init.System.IO
import Init.Data.Array.Basic
import Init.Data.Option.Basic

def testArrayIndex {α : Type} (arr : Array α) (ix : Int) : Option α :=
  if ix < 0 then
    none
  else if h : ix.toNat < arr.size then
    some (getElem arr ix.toNat h)
  else
    none

def main : IO Unit := do
  let array := #[ 1, 2, 3 ]
  IO.println (repr (testArrayIndex array (-1)))
  IO.println (repr (testArrayIndex array 0))
  IO.println (repr (testArrayIndex array 1))
  IO.println (repr (testArrayIndex array 2))
  IO.println (repr (testArrayIndex array 3))
