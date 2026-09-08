prelude
import Init.System.IO
import Init.Data.Option.Basic
import Init.Data.Int.Basic
import Init.Data.ToString.Basic

def preview_left {α β : Type} : Except α β → Option α
  | Except.error a => some a
  | Except.ok _ => none

def preview_left_right {α β γ : Type} : Except (Except α β) γ → Option β
  | Except.error (Except.ok b) => some b
  | _ => none

def test1 : Except Int Int → Option Int := preview_left
def test2 (a : Except Int Int) := preview_left a
def test3 : Except (Except Int Int) Int → Option Int := preview_left_right
def test4 (a : Except (Except Int Int) Int) := preview_left_right a

def main : IO Unit := do
  IO.println (repr (test1 (Except.error 1)))
  IO.println (repr (test1 (Except.ok 2 : Except Int Int)))
  IO.println (repr (test3 (Except.error (Except.ok 2))))
  IO.println (repr (test3 (Except.error (Except.error 1))))
