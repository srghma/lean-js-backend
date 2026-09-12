2. how can we improve ObjProps to not have duplicate keys? Does it make sense to restrict it?

3.

inductive EffectOp : Nat → Finset NEString → Type where
  | call (fn : NEString) (args : ExprVec n g k) : EffectOp n g
  -- e.g., console.log, mutation, etc.

inductive Stmt : Nat → Finset NEString → Type where
  | effect (eff : EffectOp n g)                  : Stmt n g  -- only allow side effects here
  | ret    (e : Expr n g)                        : Stmt n g
  | ifElse (c : BExpr n g) (thn els : Block n g) : Stmt n g
