prelude
import Init.System.IO
import Init.Data.Array.Basic
import Init.Data.Int.Basic
import Init.Data.String.Basic
import Init.Data.String.TakeDrop

structure Unfold (α : Type) where
  σ : Type
  s : σ
  step : σ → ∀ {ρ : Type}, (Unit → ρ) → (σ → α → ρ) → ρ

def mapU {α β : Type} (f : α → β) (u : Unfold α) : Unfold β :=
  { σ := u.σ, s := u.s, step := fun s {_ρ} nothing just => u.step s nothing (fun s' a => just s' (f a)) }

def stepToOption (u : Unfold α) (s : u.σ) : Option (u.σ × α) :=
  u.step s (fun _ => none) (fun s' a => some (s', a))

partial def filterMapU {α β : Type} (f : α → Option β) (u : Unfold α) : Unfold β :=
  let rec step' (s : u.σ) : Option (u.σ × β) :=
    match stepToOption u s with
    | none => none
    | some (s', a) =>
      match f a with
      | none => step' s'
      | some b => some (s', b)
  { σ := u.σ, s := u.s, step := fun s {_ρ} nothing just =>
    match step' s with
    | none => nothing ()
    | some (s', b) => just s' b
  }

def filterU {α : Type} (p : α → Bool) (u : Unfold α) : Unfold α :=
  filterMapU (fun a => if p a then some a else none) u

def fromArray {α : Type} (arr : Array α) : Unfold α :=
  { σ := Nat, s := 0, step := fun i {ρ} nothing just =>
    if h : i < arr.size then
      just (i + 1) arr[i]
    else
      nothing ()
  }

partial def toArray {α : Type} (u : Unfold α) : Array α :=
  let rec loop (s : u.σ) (acc : List α) : List α :=
    match stepToOption u s with
    | none => acc
    | some (s', a) => loop s' (a :: acc)
  (loop u.s []).reverse.toArray

def test (arr : Array Int) : Array String :=
  let u := fromArray arr
  let u := mapU (fun x => x + 1) u
  let u := mapU toString u
  let u := filterMapU (fun s => if s.startsWith "1" then some (s.drop 1).copy else none) u
  let u := mapU (fun s => "2" ++ s) u
  let u := filterU (fun s => s != "wat") u
  let u := mapU (fun s => s ++ "1") u
  toArray u

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
  let arr := #[9, 10, 11, 12, 19, 20]
  printArray (test arr)
