prelude
import Init.System.IO
import Init.Data.Array.Basic
import Init.Data.String.Basic

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

structure Merged where
  a : String
  b : Int
  deriving Repr

structure Result where
  ix : Int
  a : String
  b : Int
  deriving Repr

def main : IO Unit := do
  let result ← diffWithIxE
    #[ "1", "2", "3" ]
    #[ 1, 2 ]
    (fun ix a b => do
        pure ({ ix := ix, a := a, b := b } : Result)
    )
    (fun _ _ => pure ())
    (fun ix b => pure ({ ix := ix, a := "", b := b } : Result))

  IO.println (repr (#[({ a := "1", b := 1 } : Merged), { a := "2", b := 2 }]))
  IO.println (repr (#[] : Array Int))
  IO.println (repr (#["3"] : Array String))
  IO.println (repr result)
