def test1Opt : Int → Option Int
  | 1 => some 1
  | 2 => some 2
  | 3 => some 3
  | _ => none
