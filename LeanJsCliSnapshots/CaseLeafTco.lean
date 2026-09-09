import Init.Data.Array.Basic
import Init.Data.Int.Basic

partial def test1 (b : Bool) (arr : Array Int) : Array Int :=
  let head? := arr[0]?
  let last? := if arr.isEmpty then none else arr[arr.size - 1]?
  match head?, last? with
  | some 1, some 2 => arr
  | none, some y => arr.push y
  | none, none => arr
  | some x, none => arr.push x
  | some x, some y =>
    if b then
      #[]
    else
      test1 b (#[ y, x, 3, y, 5, 6, 7, 8, 9, 10, x, 12, 13, 14, 15, 16, 17 ] ++ arr)
