prelude
import Init.System.IO
import Init.Data.Int.Basic
import Init.Data.Float
import Init.Data.String

def prec1 (f : Unit → Bool) (_a _b : Unit) : Bool :=
  let x := if f () then f () else false
  let y := if x then f () else true
  if y then f () else f ()

def prec2_1 (a : Float) : Float := a + (a + (a + a))
def prec2_2 (a : Float) : Float := ((a + a) + a) + a
def prec2_3 (a : Float) : Float := a + (a + (a - a))
def prec2_4 (a : Float) : Float := ((a - a) + a) + a
def prec2_5 (a : Float) : Float := (a - a) + (a + a)

def sharedElse (a b c : Bool) : Int :=
  if a then
    if b then 1 else if c then 2 else 3
  else if c then
    2
  else
    3

def main : IO Unit := do
  IO.println (prec1 (fun _ => true) () ())
  IO.println (prec2_1 1.5)
  IO.println (prec2_2 1.5)
  IO.println (prec2_3 1.5)
  IO.println (prec2_4 1.5)
  IO.println (prec2_5 1.5)
  IO.println (sharedElse true false true)
  IO.println (sharedElse false false false)
