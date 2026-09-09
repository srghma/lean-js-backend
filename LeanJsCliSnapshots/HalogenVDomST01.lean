import Init.System.IO
import Init.Data.Array.Basic
import Init.Data.String.Basic

structure Merged where
  a : String
  b : Int
  deriving Repr

structure Result where
  ix : Int
  a : String
  b : Int
  deriving Repr

def diffWithIxE {b c d : Type} [Inhabited b] [Inhabited c]
  (a1 : Array b)
  (a2 : Array c)
  (f1 : Int → b → c → IO d)
  (f2 : Int → b → IO Unit)
  (f3 : Int → c → IO d) : IO (Array d) := do
  let mut a3 := #[]
  let l1 := a1.size
  let l2 := a2.size
  let l3 := if l1 < l2 then l2 else l1
  for i in List.range l3 do
    if i < l1 then
      if i < l2 then
        let v1 := a1[i]!
        let v2 := a2[i]!
        let v3 ← f1 i v1 v2
        a3 := a3.push v3
      else
        let v1 := a1[i]!
        f2 i v1
    else if i < l2 then
      let v2 := a2[i]!
      let v3 ← f3 i v2
      a3 := a3.push v3
  pure a3

def diffWithKeyAndIxE {a b c d : Type} [Inhabited b]
  (o1 : List (String × a))
  (as : Array b)
  (fk : b → String)
  (f1 : String → Int → a → b → IO c)
  (f2 : String → a → IO d)
  (f3 : String → Int → b → IO c) : IO (List (String × c)) := do
  let mut o2 : List (String × c) := []
  for i in List.range as.size do
    let a := as[i]!
    let k := fk a
    match o1.find? (fun (k', _) => k' == k) with
    | some (_, v1) =>
      let v2 ← f1 k i v1 a
      o2 := (k, v2) :: o2
    | none =>
      let v2 ← f3 k i a
      o2 := (k, v2) :: o2

  for (k, v1) in o1 do
    if o2.find? (fun (k', _) => k' == k) |>.isNone then
      let _ ← f2 k v1

  pure o2.reverse
