import Init.System.IO
import Init.Data.Int.Basic

partial def whileE (cond : IO Bool) (f : IO Unit) : IO Unit := do
  let c ← cond
  if c then
    f
    whileE cond f
  else
    pure ()

def test1 (hi : Int) : IO Int := do
  let count ← IO.mkRef 0
  let keepRunning ← IO.mkRef true
  whileE keepRunning.get do
    let n ← count.get
    if n < hi then
      count.set (n + 1)
    else
      keepRunning.set false
  count.get

def test2 : IO (Int → IO Unit) := do
  let count ← IO.mkRef 0
  pure fun n => do
    let val ← count.get
    count.set (val + n)

def test3 : IO (IO.Ref Int × (Int → IO Unit)) := do
  let count ← IO.mkRef 0
  pure (count, fun n => do
    let val ← count.get
    count.set (val + n))
