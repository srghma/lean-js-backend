import Init.System.IO
import Init.Data.Array.Basic
import Init.Data.Int.Basic
import Init.Data.String.Basic
import Init.Data.String.TakeDrop

structure Fold (α : Type) where
  fold : ∀ {ρ : Type}, (α → ρ → ρ) → ρ → ρ

def mapF {α β : Type} (f : α → β) (ma : Fold α) : Fold β :=
  { fold := fun cons nil => ma.fold (fun a as => cons (f a) as) nil }

def filterMapF {α β : Type} (f : α → Option β) (ma : Fold α) : Fold β :=
  { fold := fun cons nil => ma.fold (fun a as => match f a with | some b => cons b as | none => as) nil }

def filterF {α : Type} (p : α → Bool) (ma : Fold α) : Fold α :=
  filterMapF (fun a => if p a then some a else none) ma

def fromArray {α : Type} (arr : Array α) : Fold α :=
  { fold := fun {ρ} cons nil =>
    let rec loop (i : Nat) (acc : ρ) : ρ :=
      if h : i < arr.size then
        loop (i + 1) (cons arr[i] acc)
      else
        acc
    loop 0 nil
  }

def toArray' {α : Type} (ma : Fold α) : Array α :=
  let l := ma.fold (fun a as => a :: as) []
  l.reverse.toArray

def test (arr : Array Int) : Array String :=
  let f := fromArray arr
  let f := mapF (fun x => x + 1) f
  let f := mapF toString f
  let f := filterMapF (fun s => if s.startsWith "1" then some (s.drop 1).copy else none) f
  let f := mapF (fun s => "2" ++ s) f
  let f := filterF (fun s => s != "wat") f
  let f := mapF (fun s => s ++ "1") f
  toArray' f

def printArray (arr : Array String) : IO Unit := do
  IO.print "#["
  let mut first := true
  for a in arr do
    if !first then IO.print ", "
    IO.print "\""
    IO.print a
    IO.print "\""
    first := false
