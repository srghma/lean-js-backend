prelude
import Init.System.IO
import Init.Data.Array.Basic
import Init.Data.Int.Basic

def span (p : Int → Bool) (arr : Array Int) : Option Nat :=
  let rec go (i : Nat) : Option Nat :=
    if h : i < arr.size then
      let x := arr[i]
      if p x then go (i + 1) else some i
    else
      none
  go 0

def main : IO Unit := do
  let res1 := span (fun x => x < 10) #[1, 2, 11, 3]
  match res1 with
  | some i => IO.println s!"some {i}"
  | none => IO.println "none"
  let res2 := span (fun x => x < 10) #[1, 2, 3]
  match res2 with
  | some i => IO.println s!"some {i}"
  | none => IO.println "none"
