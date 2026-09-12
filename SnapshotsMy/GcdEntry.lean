-- @js_export: Nat.gcd, gcd2, run, main
prelude
import Init.Data.Nat.Gcd
import Init.System.IO

/-!
A snapshot input for the `OnlyEntry` kind of output: the generated file runs `main`
at the end, exactly as a compiled Lean program does. `main` has one of the types
Lake accepts for an entry point (`IO Unit`), so the file that comes out prints the
result of `run`.
-/

def gcd2 (a b : Nat) : Nat := Nat.gcd a b

def run : Nat := gcd2 48 18

def main : IO Unit := IO.println run
