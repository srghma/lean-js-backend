def test1 (f : Unit → Bool) (a b : Unit) : Bool :=
  -- since `f a` is pure function - it will be cached by optimizer, so `f a` calls will be optimized to single call
  let x := if f a then f b else false
  let y := if x then f a else true
  if y then f a else f ()
