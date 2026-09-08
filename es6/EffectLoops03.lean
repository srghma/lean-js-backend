prelude
import Init.System.IO
import Init.Data.Int.Basic

partial def whileE (cond : IO Bool) (f : IO Unit) : IO Unit := do
  let c ← cond
  if c then
    f
    whileE cond f
  else
    pure ()

def test1 (cond : IO.Ref Bool) : IO Unit :=
  whileE cond.get do
    IO.println "foo"
    IO.println "bar"

def test2 (cond : IO.Ref Bool) : IO Unit := do
  whileE cond.get do
    IO.println "foo"
  whileE cond.get do
    IO.println "bar"

def test3 (cond : IO.Ref Bool) (ref : IO.Ref Int) : IO Unit :=
  whileE cond.get do
    let a ← ref.get
    if a < 10 then
      IO.println "foo"
    else
      pure ()

def test4 (cond : IO.Ref Bool) (ref : IO.Ref Int) : IO Unit :=
  whileE cond.get do
    let a ← ref.get
    if a < 10 then
      IO.println "foo"
    else
      IO.println "wat"

def main : IO Unit := do
  let cond ← IO.mkRef true
  let ref ← IO.mkRef 0
  
  -- Simple test with false
  cond.set false
  test1 cond
  test2 cond
  test3 cond ref
  test4 cond ref
  
  -- Test with one iteration
  cond.set true
  let random := do
    let c ← cond.get
    if c then cond.set false
    pure c
  whileE random (IO.println "once")
