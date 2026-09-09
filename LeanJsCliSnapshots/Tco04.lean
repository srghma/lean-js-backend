mutual
  partial def test1 (n : Int) : Int :=
    if n == 1 then n else test2 (n - 1)

  partial def test2 (m : Int) : Int :=
    if m == 2 then m else test1 (m - 2)
end
