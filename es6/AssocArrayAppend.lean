prelude
import Init.System.IO
import Init.Data.Array.Basic
import Init.Data.Int.Basic

def test1 (arr : Array String) : Array String :=
  let x := #["a"]
  let y := #["b"]
  let z := #["c"]
  let w := #["d"]
  x ++ (y ++ (arr ++ (arr ++ (arr ++ (arr ++ z))))) ++ w

def test2 (arr : Array String) : Array String :=
  let x := #["a"]
  let y := #["b"]
  let z := #["c"]
  let w := #["d"]
  x ++ (y ++ arr ++ arr ++ arr ++ arr ++ z) ++ w

def test3 (arr : Array String) : Array String :=
  let x := #["a"]
  let y := #["b"]
  let z := #["c"]
  let w := #["d"]
  let e := #["e"]
  let f := #["f"]
  let g := #["g"]
  x ++ (y ++ (arr ++ (arr ++ (arr ++ (arr ++ z))))) ++ w ++ (e ++ arr ++ arr ++ arr ++ arr ++ f) ++ g

def printArray (arr : Array String) : IO Unit := do
  IO.print "#["
  let mut first := true
  for a in arr do
    if !first then IO.print ", "
    IO.print "\""
    IO.print a
    IO.print "\""
    first := false
  IO.println "]"

def main : IO Unit := do
  let arr := #["xy"]
  printArray (test1 arr)
  printArray (test2 arr)
  printArray (test3 arr)
