def test1 (f : Unit → Bool) (a b : Unit) : Bool :=
  let x := if f a then f b else false
  let y := if x then f a else true
  if y then f a else f ()
