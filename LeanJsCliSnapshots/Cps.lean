def cpsResult (s : Int) : Int × Unit :=
  let res1 := s
  let s := res1 + 1
  let res2 := s
  let s := res2 + 1
  (s, ())
