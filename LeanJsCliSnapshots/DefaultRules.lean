prelude
import Init.System.IO
import Init.Data.Option.Basic
import Init.Data.String
import Init.Data.Int.Basic

structure R where
  foo : Int
  bar : String
  baz : Bool
deriving BEq, Repr

def eqTest1 : Bool :=
  let r1 : R := { foo := 42, bar := "hello", baz := false }
  r1 == r1

def eqTest2 : Bool :=
  let r1 : R := { foo := 42, bar := "hello", baz := false }
  let r2 : R := { foo := 43, bar := "hello", baz := false }
  r1 == r2

def eqTest3 : Bool :=
  let r1 : R := { foo := 42, bar := "hello", baz := false }
  let r2 : R := { foo := 43, bar := "hello", baz := false }
  r1 != r2

def functionAppend (f g : Int → String) (x : Int) : String :=
  f x ++ g x

def functionAppend4 (f g : Int → String) (x : Int) : String :=
  f x ++ g x ++ f x ++ g x

def maybeShow (x : Option Int) : Option String :=
  x.map toString

def maybeConst (x : Option String) : Option Int :=
  x.map (fun _ => 42)

def pipeDemo (g : Unit → String) (f : String → String) : String :=
  () |> g |> f

def main : IO Unit := do
  IO.println eqTest1
  IO.println eqTest2
  IO.println eqTest3
  IO.println (12 != (12 : Int))
  IO.println (12 != (13 : Int))
  IO.println (functionAppend (fun x => s!"a{x}") (fun x => s!"b{x}") 7)
  IO.println (functionAppend4 (fun x => s!"a{x}") (fun x => s!"b{x}") 7)
  IO.println ((maybeShow (some 42)).getD "none")
  IO.println (toString ((maybeConst (some "x")).getD 0))
  IO.println (pipeDemo (fun _ => "ok") (fun s => s ++ "!"))
