prelude
import Init.System.IO
import Init.Data.Int.Basic

def divNoInline (a b : Int) : Int := a / b

def main : IO Unit := do
  IO.println (divNoInline 1 0)
  IO.println (divNoInline 3 2)
  IO.println (divNoInline 3 (-2))
