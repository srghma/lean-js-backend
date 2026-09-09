import Init.Data.Array.Basic
import Init.Data.Option.Basic

def testArrayIndex {α : Type} (arr : Array α) (ix : Int) : Option α :=
  if ix < 0 then
    none
  else if h : ix.toNat < arr.size then
    some (getElem arr ix.toNat h)
  else
    none
