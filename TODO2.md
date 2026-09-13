2. how can we improve ObjProps to not have duplicate keys? Does it make sense to restrict it?

3.

inductive EffectOp : Nat → Finset NEString → Type where
  | call (fn : NEString) (args : ExprVec n g k) : EffectOp n g
  -- e.g., console.log, mutation, etc.

inductive Stmt : Nat → Finset NEString → Type where
  | effect (eff : EffectOp n g)                  : Stmt n g  -- only allow side effects here
  | ret    (e : Expr n g)                        : Stmt n g
  | ifElse (c : BExpr n g) (thn els : Block n g) : Stmt n g

4. prove `Expr.cse_idempotent`:

A formal proof requires proving a characterisation invariant on the output—specifically, proving that `Expr.cseTop` leaves behind no repeated subterms that meet the candidate threshold, meaning a subsequent pass finds no candidates to rewrite.
