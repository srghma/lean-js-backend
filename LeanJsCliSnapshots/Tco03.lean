partial def test (n : Int) : Int :=
  let rec go (n : Int) : Int :=
    let rec k (m : Int) : Int :=
      if m == 100 then go (m - 1)
      else if m == 900 then 42
      else k (m - 1)
    if n == 0 then n
    else if n <= 100 then go (n - 1)
    else k (n - 1)
  go n
