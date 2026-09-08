import Init.System.IO
import Init.Data.Range

def test1 (ref : IO.Ref Int) (lo hi : Nat) : IO Unit := do
  for a in [lo + 1 : hi + 1] do
    let val ← ref.get
    ref.set (val + a)
    let val2 ← ref.get
    ref.set (val2 + a)

def test2 (ref : IO.Ref Int) (lo hi : Nat) : IO Unit := do
  for a in [lo + 1 : hi + 1] do
    let val ← ref.get
    ref.set (val + a)
  for a in [lo + 1 : hi + 1] do
    let val ← ref.get
    ref.set (val + a)
  for _ in [lo + 1 : hi + 1] do
    let val ← ref.get
    ref.set (val + 1)

def test3 (ref : IO.Ref Int) (lo hi : Nat) : IO Unit := do
  for a in [lo : hi] do
    if a < 10 then
      let val ← ref.get
      ref.set (val + a)

def test4 (ref : IO.Ref Int) (lo hi : Nat) : IO Unit := do
  for a in [lo : hi] do
    let val ← ref.get
    if a < 10 then
      ref.set (val + a)
    else
      ref.set (val + 1)

def main : IO Unit := do
  let total := Id.run do
    let mut acc := 0
    for a in [1:3] do
      acc := acc + a
      acc := acc + a
    for a in [1:3] do
      acc := acc + a
    for a in [1:3] do
      acc := acc + a
    for _ in [1:3] do
      acc := acc + 1
    for a in [0:20] do
      if a < 10 then
        acc := acc + a
    for a in [0:20] do
      acc := acc + if a < 10 then a else 1
    acc
  IO.println total
