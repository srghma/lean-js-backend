prelude
import Init.System.IO
import Init.Data.Int.Basic
import Init.Data.String.Basic
import Init.Data.Option.Basic
import Init.Data.ToString.Basic

def test1 : Option Int → Option String
  | some i => some (toString i)
  | none   => none

def test2 {α : Type} : Option α → Option Unit
  | some _ => some ()
  | none   => none

def test3 {α : Type} : Option α → Option Int
  | some _ => some 42
  | none   => none

def test4 {α : Type} : Option α → Option Int
  | some _ => some 42
  | none   => none

def test5 {α : Type} : Option α → Option α
  | some a => some a
  | none   => none

def main : IO Unit := do
  IO.println (repr (test1 (some 42)))
  IO.println (repr (test1 none))
  IO.println (repr (test2 (some 42)))
  IO.println (repr (test2 (none : Option Int)))
  IO.println (repr (test3 (some "hi")))
  IO.println (repr (test3 (none : Option String)))
  IO.println (repr (test4 (some "hi")))
  IO.println (repr (test5 (some 42)))
  IO.println (repr (test5 (none : Option Int)))
