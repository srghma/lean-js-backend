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
