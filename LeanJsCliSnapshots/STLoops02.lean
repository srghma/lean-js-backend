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
