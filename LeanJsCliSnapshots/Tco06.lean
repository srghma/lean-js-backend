import Init.Data.Int.Basic

mutual
  partial def f (a b : Int) : Int := g (a + b)
  partial def g (a : Int) : Int := f a (a + 1)
end
