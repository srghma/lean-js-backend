module

public import Lean.Attributes
public import Lean.EnvExtension
public import Lean.Environment
public import Lean.Data.Name
public import Lean.Meta.Eval
public meta import Lean.Parser.Extra
public meta import Init.Data.ToString.Name

public section


/-! ### 1. Schema Definitions -/

structure LeanEnumCtorSchema where
  name      : String
  numFields : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

structure LeanEnumSchema where
  typeName : String
  ctors    : List LeanEnumCtorSchema
  deriving Repr, BEq, DecidableEq, Inhabited

namespace LeanEnumSchema

/-- Returns the number of fields for a constructor in the schema, defaulting to 0 if not found. -/
def ctorNumFields (schema : LeanEnumSchema) (ctorName : String) : Option Nat :=
  schema.ctors.find? (·.name == ctorName) >>= (some ·.numFields)

/-- Validates that a constructor name belongs to the schema. -/
def hasCtor (schema : LeanEnumSchema) (ctorName : String) : Prop :=
  schema.ctors.any (·.name == ctorName)

end LeanEnumSchema

/- Smart constructor -/
def LeanEnumSchema.mkEnum (schema : LeanEnumSchema) (ctorName : String) {n : Nat}
    (fields : Vector (Expr n) (schema.ctorNumFields ctorName))
    (hValid : schema.hasCtor ctorName = true := by decide) :
    LeanEnum schema ctorName n :=
  ⟨fields, hValid⟩

/-! ### 4. Metaprogramming / Elaborator -/


/-- Inspects an inductive type in Lean's environment and generates a `LeanEnumSchema`. -/
open Lean Meta Elab Term in
def extractEnumSchema (typeName : Name) : MetaM LeanEnumSchema := do
  let env ← getEnv
  let some (.inductInfo indVal) := env.find? typeName
    | throwError "'{typeName}' is not an inductive type"
  let mut ctors : List CtorSchema := []
  for ctorName in indVal.ctors do
    let some (.ctorInfo ctorVal) := env.find? ctorName
      | throwError "Constructor '{ctorName}' not found"
    let shortName := match ctorName with
      | .str _ s => s
      | _ => ctorName.toString
    -- `numFields` accounts for the constructor fields after stripping type params
    ctors := ctors ++ [{ name := shortName, numFields := ctorVal.numFields }]
  return { typeName := typeName.toString, ctors := ctors }

/--
`lean_schema% <type>` resolves an inductive type in the environment and expands
into a literal `LeanEnumSchema` at compile time.
-/
elab "lean_schema% " id:ident : term => do
  let typeName ← resolveGlobalConstNoOverload id
  let schema ← extractEnumSchema typeName
  let ctorSyntax ← schema.ctors.mapM fun c =>
    `(CtorSchema.mk $(quote c.name) $(quote c.numFields))
  let ctorsList ← `([ $[$ctorSyntax],* ])
  let term ← `(LeanEnumSchema.mk $(quote schema.typeName) $ctorsList)
  elabTerm term none

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

  inductive ExprList : Nat → Type where
    | nil : ExprList n
    | cons (head : Expr n) (tail : ExprList n) : ExprList n
    deriving Repr, BEq, Inhabited

  /- Dedicated object representing Lean-generated enum/inductive representations -/
  structure LeanEnum : Nat -> Type where
    | mk
      (type : String) -- E.g. "List"
      (inductiveFieldName : String) -- e.g. "cons"
      (fields : ExprList n) : LeanEnum n -- e.g. TODO
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
    | leanGeneratedEnumIsTag (obj : LeanEnum n) (inductiveFieldName : String) : BExpr n
    deriving Repr, BEq, Inhabited

  inductive Expr : Nat → Type where
    | var         (i : Fin n)                                    : Expr n
    | unsafeGlobal (name : String)                               : Expr n
    | bexpr       (b : BExpr n)                                  : Expr n
    | num         (val : Nat)                                    : Expr n
    | numLit      (val : String)                                 : Expr n
    | str         (val : String)                                 : Expr n
    | obj         (props : ObjectPropsExprList n)                : Expr n
    | arr         (elems : ExprList n)                           : Expr n
    | call        (fn : Expr n) (args : ExprList n)              : Expr n
    | prop        (obj : Expr n) (name : String)                 : Expr n
    | index       (obj idx : Expr n)                             : Expr n
    | unary       (op : JSUnaryOpReturnNotBoolTakesExpr) (a : Expr n)     : Expr n
    | binop       (op : JSBinOpReturnNotBoolTakesExpr) (a b : Expr n)     : Expr n
    | cond        (c : BExpr n) (t e : Expr n)                   : Expr n
    | new         (cls : Expr n) (args : ExprList n)             : Expr n
    | arrowExpr   (params : Nat) (body : Expr (n + params))      : Expr n -- TODO: what is this?
    | leanGeneratedEnumGetField (obj : LeanExpr n) (idx : Nat)       : Expr n
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
