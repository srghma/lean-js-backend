import Init.Data.Int.Basic
import Init.Data.Float
import Init.Data.String

inductive Expr where
  | add (a : Expr) (b : Expr)
  | mul (a : Expr) (b : Expr)
  | succ (a : Expr)
  | zero
deriving Repr

inductive Column where
  | zero
  | one (n : Int)
  | two (a : Int) (b : Int)
deriving Repr

structure Product3 where
  a : Int
  b : Int
  c : Int
deriving Repr

def renderExpr : Expr → String
  | .add a b => "Add(" ++ renderExpr a ++ " " ++ renderExpr b ++ ")"
  | .mul a b => "Mul(" ++ renderExpr a ++ " " ++ renderExpr b ++ ")"
  | .succ a => "Succ(" ++ renderExpr a ++ ")"
  | .zero => "Zero"

def caseJacobs : Expr → String
  | .add .zero .zero => "e1"
  | .mul .zero x => "e2: " ++ renderExpr x
  | .add (.succ x) y => "e3: " ++ renderExpr x ++ " " ++ renderExpr y
  | .mul x .zero => "e4: " ++ renderExpr x
  | .mul (.add x y) z => "e5: " ++ renderExpr x ++ " " ++ renderExpr y ++ " " ++ renderExpr z
  | .add x .zero => "e6: " ++ renderExpr x
  | x => "e7: " ++ renderExpr x

def caseBoolean : Bool → String
  | true => "1"
  | false => "2"

def caseChar : Char → String
  | 'a' => "1"
  | 'b' => "2"
  | 'c' => "3"
  | _ => "catch"

def caseInt : Int → String
  | 1 => "1"
  | 2 => "2"
  | 3 => "3"
  | _ => "catch"

def caseNumber (x : Float) : String :=
  if x == 1.0 then "1"
  else if x == 2.0 then "2"
  else if x == 3.0 then "3"
  else "catch"

def caseGrafting : Bool → Bool → Bool → Int
  | _, false, true => 1
  | false, true, _ => 2
  | _, _, false => 3
  | _, _, true => 4

def caseHeuristicP : Int → Int → Int → Int
  | 1, 2, 1 => 1
  | 1, 2, 2 => 2
  | _, 2, 3 => 3
  | 1, _, 4 => 4
  | _, _, _ => 5

def caseHeuristicPB : Column → Column → Int
  | .one 1, .one 1 => 1
  | .two 2 3, .two 2 3 => 2
  | _, .zero => 3
  | _, _ => 4

def caseHeuristicPBA : Column → Column → Int
  | .one 1, .one 1 => 1
  | .one 2, .one 2 => 2
  | .two 1 _, .two _ _ => 3
  | _, _ => 4

def caseHeuristicPBAN : Column → Column → Int
  | .one 1, .one 1 => 1
  | .one 2, .one 2 => 2
  | .two _ _, .two _ _ => 3
  | _, _ => 4

def caseNamed1 (x : Int) : String :=
  match x with
  | 1 => "111"
  | 2 => "2"
  | n => "any: " ++ toString n ++ toString n ++ toString n

def caseNamed2 (x : Product3) : String :=
  match x with
  | ⟨1, a, b⟩ => toString a ++ toString b ++ "1"
  | ⟨a, 1, b⟩ => toString a ++ toString b ++ "1"
  | ⟨a, b, 1⟩ => toString a ++ toString b ++ "1"
  | ⟨a, b, c⟩ => toString a ++ toString a ++ toString b ++ toString b ++ toString c ++ toString c
