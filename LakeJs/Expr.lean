module

public import Lean.Attributes
public import Lean.EnvExtension
public import Lean.Environment
public import Lean.Data.Name
public import Lean.Meta.Eval
public meta import Lean.Parser.Extra
public meta import Init.Data.ToString.Name

public import LakeJs.LeanEnum.Schema
public meta import LakeJs.LeanEnum.Schema
public import LakeJs.LeanEnum.SchemaMeta
public meta import LakeJs.LeanEnum.SchemaMeta

public section

/- Smart constructor -/

-- def LeanEnumSchema.mkEnum (schema : LeanEnumSchema) (ctorName : String)
--     (fields : Vector (Expr n) (schema.ctorNumFields ctorName))
--     (hValid : schema.hasCtor ctorName = true := by decide) :
--     LeanEnum schema ctorName n :=
--   ⟨fields, hValid⟩

/- Operators that always evaluate to a boolean value.
   Note: While JS allows `&&` and `||` on arbitrary types (evaluating to the operand value),
   we restrict them at the compiler/type level to boolean operands, guaranteeing a boolean result. -/
inductive JSBinOpReturnBoolTakesExpr where
  | eq          -- ==   (Loose equality)
  | strictEq    -- ===  (Strict equality)
  | neq         -- !=   (Loose inequality)
  | strictNeq   -- !==  (Strict inequality)
  | lt          -- <    (Less than)
  | le          -- <=   (Less than or equal)
  | gt          -- >    (Greater than)
  | ge          -- >=   (Greater than or equal)
  | in_         -- in   (Property existence check)
  | instanceOf  -- instanceof (Prototype chain check)
  deriving Repr, BEq, Inhabited

/- Operators that evaluate to non-boolean values (numbers, strings, bitfields, etc.) -/
inductive JSBinOpReturnNotBoolTakesExpr where
  | plus        -- +    (Numeric addition or string concatenation)
  | minus       -- -    (Numeric subtraction)
  | times       -- *    (Numeric multiplication)
  | divide      -- /    (Numeric division)
  | mod         -- %    (Numeric remainder)
  | bitAnd      -- &    (Bitwise AND: 32-bit integer)
  | bitOr       -- |    (Bitwise OR: 32-bit integer)
  | bitXor      -- ^    (Bitwise XOR: 32-bit integer)
  | lsh         -- <<   (Bitwise left shift: 32-bit signed integer)
  | rsh         -- >>   (Bitwise sign-propagating right shift: 32-bit signed integer)
  | ursh        -- >>>  (Bitwise zero-fill right shift: 32-bit unsigned integer)
  deriving Repr, BEq, Inhabited

/- Unary operators returning non-boolean -/
inductive JSUnaryOpReturnNotBoolTakesExpr where
  | plus        -- +      (Unary plus: converts operand to number)
  | minus       -- -      (Unary negation: negates number)
  | tilde       -- ~      (Bitwise NOT: inverts 32-bit integer bits)
  | typeof      -- typeof (Returns string type identifier)
  | void        -- void   (Evaluates operand and returns undefined)
  | incr        -- ++     (Pre/post increment)
  | decr        -- --     (Pre/post decrement)
  deriving Repr, BEq, Inhabited

mutual
  -- same as List (String × Expr n)
  inductive ObjectPropsExprList : Nat → Type where
    | nil : ObjectPropsExprList n
    | cons (prop : String) (val : Expr n) (tail : ObjectPropsExprList n) : ObjectPropsExprList n
    deriving Repr, BEq, Inhabited

  -- same as List (Expr n)
  inductive ExprList : Nat → Type where
    | nil : ExprList n
    | cons (head : Expr n) (tail : ExprList n) : ExprList n
    deriving Repr, BEq, Inhabited

  inductive BExpr : Nat → Type where
    | tt                                                         : BExpr n
    | ff                                                         : BExpr n
    | truthy      (e : Expr n)                                   : BExpr n -- will be printed with !!(expr)
    | not         (c : BExpr n)                                  : BExpr n -- !
    | delete      (c : Expr n)                                   : BExpr n -- delete x
    | and         (c d : BExpr n)                                : BExpr n -- &&
    | or          (c d : BExpr n)                                : BExpr n -- ||
    | binop       (op : JSBinOpReturnBoolTakesExpr) (a b : Expr n) : BExpr n
    -- | leanGeneratedEnumIsTag (obj : LeanEnum n) (inductiveFieldName : String) : BExpr n
    deriving Repr, BEq, Inhabited

  inductive Expr : Nat → Type where
    | var         (i : Fin n)                                    : Expr n
    | unsafeGlobal (name : String)                               : Expr n
    | bexpr       (b : BExpr n)                                  : Expr n
    | num         (val : Nat)                                    : Expr n
    | numLit      (val : String)                                 : Expr n
    | str         (val : String)                                 : Expr n
    | obj         (props : ObjectPropsExprList n)                : Expr n
    | arr         (elems : List (Expr n))                           : Expr n
    | call        (fn : Expr n) (args : ExprList n)              : Expr n
    | prop        (obj : Expr n) (name : String)                 : Expr n
    | index       (obj idx : Expr n)                             : Expr n
    | unary       (op : JSUnaryOpReturnNotBoolTakesExpr) (a : Expr n)     : Expr n
    | binop       (op : JSBinOpReturnNotBoolTakesExpr) (a b : Expr n)     : Expr n
    | cond        (c : BExpr n) (t e : Expr n)                   : Expr n
    | new         (cls : Expr n) (args : ExprList n)             : Expr n
    | arrowExpr   (params : Nat) (body : Expr (n + params))      : Expr n -- TODO: what is this?
    -- | leanGeneratedEnumGetField (obj : LeanExpr n) (idx : Nat)       : Expr n
    deriving Repr, BEq, Inhabited
end

def ObjectPropsExprList.toList : ObjectPropsExprList n → List (String × Expr n)
  | .nil => []
  | .cons p v tail => (p, v) :: tail.toList

def ObjectPropsExprList.ofList : List (String × Expr n) → ObjectPropsExprList n
  | [] => .nil
  | (p, v) :: tail => .cons p v (ofList tail)

def ExprList.toList : ExprList n → List (Expr n)
  | .nil => []
  | .cons h t => h :: t.toList

def ExprList.ofList : List (Expr n) → ExprList n
  | [] => .nil
  | x :: xs => .cons x (ofList xs)
