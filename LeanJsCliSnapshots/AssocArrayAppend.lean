prelude
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
