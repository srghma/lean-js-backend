module

public import Lean.Attributes
public import Lean.EnvExtension
public import Lean.Environment
public import Lean.Data.Name
public import Lean.Meta.Eval
public meta import Lean.Parser.Extra
public meta import Init.Data.ToString.Name

-- Stmt is code that doesnt have return (bc it is not inside of function) or break or continue (bc it is not inside of while or for statement)
-- 1st Bool true if inside of function (allows return)
-- 2nd Bool true if inside of while or for (allows break and continue)
-- 3d Nat is N of let debrujin indexes
-- 4th Nat is N of const debrujin indexes
inductive Stmt : Bool -> Bool -> Nat → Type where
  | return_    (e : Expr n)                                                          : Stmt n -- return
  | let    (val : Expr n) (k : Stmt (n+1))                                           : Stmt n -- let l#0 = expr
  | const  (val : Expr n) (k : Stmt (n+1))                                           : Stmt n -- const c#0 = expr
  | assign                                                                                    -- only can assign to the let, checked by let debrujin indexes
  | seq    (e : Expr n) (k : Stmt n)                                                 : Stmt n -- what is this?
  | ifElse (cond : BExpr n) (t e : Stmt n) (k : Stmt n)                             : Stmt n  -- should render using ? : if simple
  -- TODO: replace with while and for and forArray for forObject
  # | loop   (m : Nat) (stateNames : Array String)
  #           (state0 : ExprList n)
  #           (cond : BExpr (n+m)) (body : Stmt (n+m))
  #           (k : Stmt (n+m))                                                         : Stmt n
  | continue   (newState : ExprList n)                                                   : Stmt n
  | break_                                                                              : Stmt n
  deriving Repr, BEq, Inhabited

inductive InlinableFunc : Nat → Type where
  | mk (paramNames : Array String) (paramOwn : Array Ownership) (body : Stmt n) (returns : Option (Expr n)) : InlinableFunc n
  deriving Repr, BEq, Inhabited

def throwNewError (msg : String) : Expr n :=
  .call (.unsafeGlobal "throw") (.cons (.new (.unsafeGlobal "Error") (.cons (.str msg) .nil)) .nil)

def plus (a b : Expr n)   := Expr.binop .plus a b
def minus (a b : Expr n)  := Expr.binop .minus a b
def times (a b : Expr n)  := Expr.binop .times a b
def divide (a b : Expr n) := Expr.binop .divide a b
def mod (a b : Expr n)    := Expr.binop .mod a b
def pow (a b : Expr n)    := Expr.call (.prop (.unsafeGlobal "Math") "pow") (.cons a (.cons b .nil))

instance : Add (Expr n) where add := plus
instance : Sub (Expr n) where sub := minus
instance : Mul (Expr n) where mul := times
instance : Div (Expr n) where div := divide
instance : Mod (Expr n) where mod := mod
instance : Pow (Expr n) (Expr n) where pow := pow
