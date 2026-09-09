
module

prelude
public import Init.Prelude
public import Init.Coe
public import Init.Data.Repr
public import Init.Data.Vector
public import Lean.Attributes
public import Lean.EnvExtension
public import Lean.Environment
public import Lean.Data.Name
public import Lean.Meta.Eval
public meta import Lean.Parser.Extra
public meta import Init.Data.ToString.Name

public section

-- 1. Declare the syntax categories
declare_syntax_cat js_expr
declare_syntax_cat js_bexpr

-- 2. Grammar for js_expr
syntax "#" num : js_expr                        -- Arguments: #0, #1
syntax "#" num "." ident : js_expr              -- Arg + property: #0.length
syntax num : js_expr                            -- Literals: 64, 0xFF
syntax str : js_expr                            -- String literals
syntax ident : js_expr                          -- Identifiers: Error, Uint8Array
syntax "(" js_expr ")" : js_expr                -- Parentheses
syntax "[" (js_expr,*)? "]" : js_expr            -- Array literal: [], [a, b]
declare_syntax_cat js_prop_init
syntax ident ":" js_expr : js_prop_init
syntax "{" (js_prop_init,*)? "}" : js_expr
syntax js_expr "[" js_expr "]" : js_expr        -- Bracket access
syntax js_expr "." ident : js_expr              -- Member dot access
syntax js_expr "()" : js_expr
syntax js_expr "(" ")" : js_expr
syntax js_expr "(" (js_expr,*)? ")" : js_expr   -- Function calls
syntax "new " ident "(" (js_expr,*)? ")" : js_expr   -- New expression: new Foo(args)
syntax "new " ident "()" "." ident "(" (js_expr,*)? ")" : js_expr
syntax "new " ident "()" "." ident "(" (js_expr,*)? ")" "." ident : js_expr
syntax "throw " js_expr : js_expr

syntax js_expr "[" js_expr "]" " = " js_expr : js_expr
syntax js_expr "." ident " = " js_expr : js_expr
syntax ident " = " js_expr : js_expr

-- Unary operators
syntax "!" js_expr : js_expr
syntax "-" js_expr : js_expr
syntax "~" js_expr : js_expr

-- Binary and Ternary operators with precedence
syntax:30 js_expr " || " js_expr : js_expr
syntax:35 js_expr " && " js_expr : js_expr
syntax:40 js_expr " == " js_expr : js_expr
syntax:40 js_expr " === " js_expr : js_expr
syntax:40 js_expr " != " js_expr : js_expr
syntax:40 js_expr " !== " js_expr : js_expr
syntax:45 js_expr " <= " js_expr : js_expr
syntax:45 js_expr " < " js_expr : js_expr
syntax:45 js_expr " > " js_expr : js_expr
syntax:45 js_expr " >= " js_expr : js_expr
syntax:50 js_expr " | " js_expr : js_expr
syntax:55 js_expr " ^ " js_expr : js_expr
syntax:60 js_expr " & " js_expr : js_expr
syntax:65 js_expr " << " js_expr : js_expr
syntax:65 js_expr " >> " js_expr : js_expr
syntax:65 js_expr " >>> " js_expr : js_expr
syntax:70 js_expr " + " js_expr : js_expr
syntax:70 js_expr " - " js_expr : js_expr
syntax:80 js_expr " * " js_expr : js_expr
syntax:80 js_expr " / " js_expr : js_expr
syntax:80 js_expr " % " js_expr : js_expr
syntax:20 js_expr " ? " js_expr " : " js_expr : js_expr

syntax "(" (ident,*)? ")" " => " js_expr : js_expr
syntax ident " => " js_expr : js_expr

syntax "isTag" "(" js_expr "," Lean.Parser.nameLit ")" : js_expr
syntax "isTag" "(" js_expr "," ident ")" : js_expr
syntax "getField" "(" js_expr "," num ")" : js_expr
syntax "mkObject" "(" Lean.Parser.nameLit ("," js_expr)* ")" : js_expr
syntax "mkObject" "(" ident ("," js_expr)* ")" : js_expr

-- Top-level syntax
syntax "[JS_EXPR|" js_expr "]" : term
syntax "[JS_EXPR" "(" num ")" "|" js_expr "]" : term

end Lean.Compiler.JS

open Lean.Compiler.JS

namespace Lean.Compiler.JS

public meta partial def getMaxArg (stx : Syntax) : Nat :=
  match stx with
  | .node _ k args =>
    if k == `Lean.Compiler.JS.«js_expr#_» || k == `«js_expr#_» then
      if h : args.size > 1 then
        match args[1].isNatLit? with
        | some n => n + 1
        | none => 0
      else 0
    else if k == `Lean.Compiler.JS.«js_expr#_._» || k == `«js_expr#_._» then
      if h : args.size > 1 then
        match args[1].isNatLit? with
        | some n => n + 1
        | none => 0
      else 0
    else
      args.foldl (fun m a => max m (getMaxArg a)) 0
  | _ => 0

mutual
  public meta partial def elabExprWithScope (stx : TSyntax `js_expr) (scope : List String) : MacroM (TSyntax `term) := do
    match stx with
    | `(js_expr| #$n:num) => `(Expr.var ⟨$n, by decide⟩)
    | `(js_expr| #$n:num . $p:ident) => `(Expr.prop (Expr.var ⟨$n, by decide⟩) $(quote p.getId.toString))
    | `(js_expr| $n:num) => `(Expr.num $n)
    | `(js_expr| $s:str) => `(Expr.str $s)
    | `(js_expr| ($e)) => elabExprWithScope e scope
    | `(js_expr| $id:ident) =>
      let name := id.getId.toString
      if name == "true" then
        `(Expr.bool true)
      else if name == "false" then
        `(Expr.bool false)
      else match scope.findIdx? (· == name) with
      | some idx => `(Expr.var ⟨$(quote idx), by decide⟩)
      | none => `(Expr.global $(quote name))
    | `(js_expr| [ $[$elems:js_expr],* ]) => do
      let elTerms ← elems.mapM (elabExprWithScope · scope)
      let listTerm ← elTerms.foldrM (fun e acc => `(ExprList.cons $e $acc)) (← `(ExprList.nil))
      `(Expr.arr $listTerm)
    | `(js_expr| { $[$inits:js_prop_init],* }) => do
      let terms ← inits.mapM fun init => match init with
        | `(js_prop_init| $p:ident : $v:js_expr) => do
          let v' ← elabExprWithScope v scope
          pure (p.getId.toString, v')
        | _ => Macro.throwError s!"unsupported prop init: {init}"
      let listTerm ← terms.foldrM
        (fun (p, v) acc => `(PropExprList.cons $(quote p) $v $acc))
        (← `(PropExprList.nil))
      `(Expr.obj $listTerm)
    | `(js_expr| $obj:js_expr [ $idx:js_expr ]) => do
      let o ← elabExprWithScope obj scope
      let i ← elabExprWithScope idx scope
      `(Expr.index $o $i)
    | `(js_expr| $obj:js_expr . $id:ident) => do
      let o ← elabExprWithScope obj scope
      `(Expr.prop $o $(quote id.getId.toString))
    | `(js_expr| $fn:js_expr ()) | `(js_expr| $fn:js_expr ( )) => do
      let f ← elabExprWithScope fn scope
      `(Expr.call $f ExprList.nil)
    | `(js_expr| $fn:js_expr ( $[$args:js_expr],* )) => do
      let f ← elabExprWithScope fn scope
      let argTerms ← args.mapM (elabExprWithScope · scope)
      let listTerm ← argTerms.foldrM (fun a acc => `(ExprList.cons $a $acc)) (← `(ExprList.nil))
      `(Expr.call $f $listTerm)
    | `(js_expr| new $cls:ident ( $[$args:js_expr],* )) => do
      let argTerms ← args.mapM (elabExprWithScope · scope)
      let listTerm ← argTerms.foldrM (fun a acc => `(ExprList.cons $a $acc)) (← `(ExprList.nil))
      `(Expr.new (Expr.global $(quote cls.getId.toString)) $listTerm)
    | `(js_expr| new $cls:ident () . $m:ident ( $[$args:js_expr],* )) => do
      let argTerms ← args.mapM (elabExprWithScope · scope)
      let listTerm ← argTerms.foldrM (fun a acc => `(ExprList.cons $a $acc)) (← `(ExprList.nil))
      `(Expr.call (Expr.prop (Expr.new (Expr.global $(quote cls.getId.toString)) ExprList.nil) $(quote m.getId.toString)) $listTerm)
    | `(js_expr| new $cls:ident () . $m:ident ( $[$args:js_expr],* ) . $prop:ident) => do
      let argTerms ← args.mapM (elabExprWithScope · scope)
      let listTerm ← argTerms.foldrM (fun a acc => `(ExprList.cons $a $acc)) (← `(ExprList.nil))
      let c ← `(Expr.call (Expr.prop (Expr.new (Expr.global $(quote cls.getId.toString)) ExprList.nil) $(quote m.getId.toString)) $listTerm)
      `(Expr.prop $c $(quote prop.getId.toString))
    | `(js_expr| throw $e) => do
      let e' ← elabExprWithScope e scope
      `(Expr.call (Expr.global "throw") (ExprList.cons $e' ExprList.nil))
    | `(js_expr| $obj:js_expr [ $idx:js_expr ] = $val:js_expr) => do
      let o ← elabExprWithScope obj scope
      let i ← elabExprWithScope idx scope
      let v ← elabExprWithScope val scope
      `(Expr.assign (Expr.index $o $i) $v)
    | `(js_expr| $obj:js_expr . $p:ident = $val:js_expr) => do
      let o ← elabExprWithScope obj scope
      let v ← elabExprWithScope val scope
      `(Expr.assign (Expr.prop $o $(quote p.getId.toString)) $v)
    | `(js_expr| $x:ident = $val:js_expr) => do
      let name := x.getId.toString
      let v ← elabExprWithScope val scope
      match scope.findIdx? (· == name) with
      | some idx => `(Expr.assign (Expr.var ⟨$(quote idx), by decide⟩) $v)
      | none => `(Expr.assign (Expr.global $(quote name)) $v)
    | `(js_expr| ! $a) => do
      let a' ← elabExprWithScope a scope
      `(Expr.unary .not $a')
    | `(js_expr| - $a) => do
      let a' ← elabExprWithScope a scope
      `(Expr.unary .minus $a')
    | `(js_expr| ~ $a) => do
      let a' ← elabExprWithScope a scope
      `(Expr.unary .tilde $a')
    | `(js_expr| $a || $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(Expr.binop .or $a' $b')
    | `(js_expr| $a && $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(Expr.binop .and $a' $b')
    | `(js_expr| $a != $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(Expr.binop .neq $a' $b')
    | `(js_expr| $a !== $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(Expr.binop .strictNeq $a' $b')
    | `(js_expr| $a == $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(Expr.binop .eq $a' $b')
    | `(js_expr| $a === $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(Expr.binop .strictEq $a' $b')
    | `(js_expr| $a <= $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(Expr.binop .le $a' $b')
    | `(js_expr| $a < $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(Expr.binop .lt $a' $b')
    | `(js_expr| $a >= $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(Expr.binop .ge $a' $b')
    | `(js_expr| $a > $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(Expr.binop .gt $a' $b')
    | `(js_expr| $a | $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(Expr.binop .bitOr $a' $b')
    | `(js_expr| $a ^ $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(Expr.binop .bitXor $a' $b')
    | `(js_expr| $a & $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(Expr.binop .bitAnd $a' $b')
    | `(js_expr| $a << $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(Expr.binop .lsh $a' $b')
    | `(js_expr| $a >> $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(Expr.binop .rsh $a' $b')
    | `(js_expr| $a >>> $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(Expr.binop .ursh $a' $b')
    | `(js_expr| $a + $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(Expr.binop .plus $a' $b')
    | `(js_expr| $a - $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(Expr.binop .minus $a' $b')
    | `(js_expr| $a * $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(Expr.binop .times $a' $b')
    | `(js_expr| $a / $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(Expr.binop .divide $a' $b')
    | `(js_expr| $a % $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(Expr.binop .mod $a' $b')
    | `(js_expr| $c ? $t : $e) => do
      let c' ← elabBExprWithScope c scope
      let t' ← elabExprWithScope t scope
      let e' ← elabExprWithScope e scope
      `(Expr.cond $c' $t' $e')
    | `(js_expr| ( $[$params:ident],* ) => $body:js_expr) => do
      let pNames := params.toList.map (·.getId.toString)
      let body' ← elabExprWithScope body (scope ++ pNames)
      `(Expr.arrowExpr $(quote pNames.length) $body')
    | `(js_expr| $p:ident => $body:js_expr) => do
      let body' ← elabExprWithScope body (scope ++ [p.getId.toString])
      `(Expr.arrowExpr 1 $body')
    | `(js_expr| isTag($obj:js_expr, $tag:name)) => do
      let o ← elabExprWithScope obj scope
      `(Expr.leanGeneratedEnumIsTag $o $(quote tag.getName))
    | `(js_expr| isTag($obj:js_expr, $tag:ident)) => do
      let o ← elabExprWithScope obj scope
      `(Expr.leanGeneratedEnumIsTag $o $(quote tag.getId))
    | `(js_expr| getField($obj:js_expr, $idx:num)) => do
      let o ← elabExprWithScope obj scope
      `(Expr.leanGeneratedEnumGetField $o $(quote idx.getNat))
    | `(js_expr| mkObject($tag:name $[, $fields:js_expr]*)) => do
      let fTerms ← fields.mapM (elabExprWithScope · scope)
      let listTerm ← fTerms.foldrM (fun f acc => `(ExprList.cons $f $acc)) (← `(ExprList.nil))
      `(Expr.leanGeneratedEnumMk $(quote tag.getName) $listTerm)
    | `(js_expr| mkObject($tag:ident $[, $fields:js_expr]*)) => do
      let fTerms ← fields.mapM (elabExprWithScope · scope)
      let listTerm ← fTerms.foldrM (fun f acc => `(ExprList.cons $f $acc)) (← `(ExprList.nil))
      `(Expr.leanGeneratedEnumMk $(quote tag.getId) $listTerm)
    | _ => Macro.throwError s!"unsupported js_expr: {stx}"

  public meta partial def elabBExprWithScope (stx : TSyntax `js_expr) (scope : List String) : MacroM (TSyntax `term) := do
    match stx with
    | `(js_expr| ($e)) => elabBExprWithScope e scope
    | `(js_expr| ! $a) => do
      let a' ← elabBExprWithScope a scope
      `(BExpr.not $a')
    | `(js_expr| $a && $b) => do
      let a' ← elabBExprWithScope a scope; let b' ← elabBExprWithScope b scope
      `(BExpr.and $a' $b')
    | `(js_expr| $a || $b) => do
      let a' ← elabBExprWithScope a scope; let b' ← elabBExprWithScope b scope
      `(BExpr.or $a' $b')
    | `(js_expr| $a < $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(BExpr.lt $a' $b')
    | `(js_expr| $a <= $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(BExpr.le $a' $b')
    | `(js_expr| $a > $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(BExpr.lt $b' $a')
    | `(js_expr| $a >= $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(BExpr.le $b' $a')
    | `(js_expr| $a == $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(BExpr.eq $a' $b')
    | `(js_expr| $a === $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(BExpr.strictEq $a' $b')
    | `(js_expr| $a != $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(BExpr.not (BExpr.eq $a' $b'))
    | `(js_expr| $a !== $b) => do
      let a' ← elabExprWithScope a scope; let b' ← elabExprWithScope b scope
      `(BExpr.not (BExpr.strictEq $a' $b'))
    | other => do
      let e' ← elabExprWithScope other scope
      `(BExpr.truthy $e')
end
