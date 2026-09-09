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

public def mangleString (s : String) : String :=
  s.foldl (fun res c =>
    if c.isAlphanum then
      res.push c
    else if c == '.' then
      res.push '$'
    else if c == '_' then
      res ++ "__"
    else
      res ++ s!"_u{c.toNat.toUInt32.toNat}_"
  ) ""

public def mangleName (n : Name) : String :=
  mangleString n.toString

declare_syntax_cat js_stmt
declare_syntax_cat js_state_init
declare_syntax_cat js_state_step

-- State assignment items for loops: a := val
syntax ident " := " js_expr : js_state_init
syntax ident " := " js_expr : js_state_step

-- Grammar for js_stmt
syntax "const " ident " = " js_expr (";")? : js_stmt
syntax "let " ident " = " js_expr (";")? : js_stmt
syntax "return " js_expr (";")? : js_stmt
syntax "if " "(" js_expr ")" "{" js_stmt* "}" ("else" "{" js_stmt* "}")? : js_stmt
syntax "if " "(" js_expr ")" "{" js_stmt* "}" "else " js_stmt : js_stmt
syntax "if " "(" js_expr ")" js_stmt : js_stmt
syntax "while " "(" js_expr ")" "{" js_stmt* "}" : js_stmt
syntax "loop " "(" (js_state_init,*)? ")" "{" js_stmt* "}" : js_stmt
syntax "continue " "(" (js_state_step,*)? ")" (";")? : js_stmt
syntax "continue" (";")? : js_stmt
syntax "break" (";")? : js_stmt
syntax js_expr (";")? : js_stmt

syntax "[JS_STMT|" js_stmt "]" : term
syntax "[JS_FUNC|" "inputs" "(" (ident,*)? ")" "|" "returns" "=" js_expr:51 "|" js_stmt* "]" : term
syntax "[JS_FUNC|" "inputs" "(" (ident,*)? ")" "|" js_stmt* "]" : term

public meta partial def elabStmtsWithScope (stmts : List (TSyntax `js_stmt)) (scope : List String) (retOpt : Option (TSyntax `js_expr)) : MacroM (TSyntax `term) := do
  match stmts with
  | [] =>
    match retOpt with
    | some ret =>
      let ret' ← elabExprWithScope ret scope
      `(Stmt.ret $ret')
    | none => `(Stmt.break_)
  | s :: rest =>
    match s with
    | `(js_stmt| const $x:ident = $val:js_expr $[;]? )
    | `(js_stmt| let $x:ident = $val:js_expr $[;]? ) => do
      let val' ← elabExprWithScope val scope
      let rest' ← elabStmtsWithScope rest (scope ++ [x.getId.toString]) retOpt
      `(Stmt.letIn $val' $rest')
    | `(js_stmt| return $val:js_expr $[;]? ) => do
      let val' ← elabExprWithScope val scope
      `(Stmt.ret $val')
    | `(js_stmt| if ($cond:js_expr) { $[$thenB:js_stmt]* } else { $[$elseB:js_stmt]* } ) => do
      let c' ← elabBExprWithScope cond scope
      let t' ← elabStmtsWithScope thenB.toList scope none
      let e' ← elabStmtsWithScope elseB.toList scope none
      let rest' ← elabStmtsWithScope rest scope retOpt
      `(Stmt.ifElse $c' $t' $e' $rest')
    | `(js_stmt| if ($cond:js_expr) { $[$thenB:js_stmt]* } else $elseS:js_stmt ) => do
      let c' ← elabBExprWithScope cond scope
      let t' ← elabStmtsWithScope thenB.toList scope none
      let e' ← elabStmtsWithScope [elseS] scope none
      let rest' ← elabStmtsWithScope rest scope retOpt
      `(Stmt.ifElse $c' $t' $e' $rest')
    | `(js_stmt| if ($cond:js_expr) { $[$thenB:js_stmt]* } ) => do
      let c' ← elabBExprWithScope cond scope
      let t' ← elabStmtsWithScope thenB.toList scope none
      let e' ← `(Stmt.break_)
      let rest' ← elabStmtsWithScope rest scope retOpt
      `(Stmt.ifElse $c' $t' $e' $rest')
    | `(js_stmt| if ($cond:js_expr) $thenS:js_stmt ) => do
      let c' ← elabBExprWithScope cond scope
      let t' ← elabStmtsWithScope [thenS] scope none
      let e' ← `(Stmt.break_)
      let rest' ← elabStmtsWithScope rest scope retOpt
      `(Stmt.ifElse $c' $t' $e' $rest')
    | `(js_stmt| while ($cond:js_expr) { $[$body:js_stmt]* } ) => do
      let c' ← elabBExprWithScope cond scope
      let body' ← elabStmtsWithScope body.toList scope none
      let rest' ← elabStmtsWithScope rest scope retOpt
      `(Stmt.loop 0 #[] ExprList.nil $c' $body' $rest')
    | `(js_stmt| loop ( $[$stateNames:ident := $stateInits:js_expr],* ) { $[$body:js_stmt]* } ) => do
      let m := stateNames.size
      let sNames := stateNames.toList.map (·.getId.toString)
      let initTerms ← stateInits.mapM (elabExprWithScope · scope)
      let initList ← initTerms.foldrM (fun i acc => `(ExprList.cons $i $acc)) (← `(ExprList.nil))
      let loopScope := scope ++ sNames
      let body' ← elabStmtsWithScope body.toList loopScope none
      let rest' ← elabStmtsWithScope rest loopScope retOpt
      let sNamesQuote := quote (stateNames.map (·.getId.toString))
      `(Stmt.loop $(quote m) $sNamesQuote $initList BExpr.tt $body' $rest')
    | `(js_stmt| continue ( $[$stepNames:ident := $stepExprs:js_expr],* ) $[;]? ) => do
      let stepTerms ← stepExprs.mapM (elabExprWithScope · scope)
      let stepList ← stepTerms.foldrM (fun s acc => `(ExprList.cons $s $acc)) (← `(ExprList.nil))
      `(Stmt.continue $stepList)
    | `(js_stmt| continue $[;]? ) => `(Stmt.continue ExprList.nil)
    | `(js_stmt| break $[;]? ) => `(Stmt.break_)
    | `(js_stmt| $e:js_expr $[;]? ) => do
      let e' ← elabExprWithScope e scope
      let rest' ← elabStmtsWithScope rest scope retOpt
      `(Stmt.seq $e' $rest')
    | _ => Macro.throwError s!"unsupported js_stmt: {s}"

macro "[JS|" body:js_expr "]" : term => `([JS_EXPR| $body])
macro "[JS|" "(" n:num ")" "|" body:js_expr "]" : term => `([JS_EXPR ($n) | $body])

macro_rules
  | `([JS_EXPR| $body:js_expr ]) => do
    let maxN := getMaxArg body.raw
    let bodyTerm ← elabExprWithScope body []
    `(($bodyTerm : Expr $(quote maxN)))
  | `([JS_EXPR ( $n:num ) | $body:js_expr ]) => do
    let bodyTerm ← elabExprWithScope body []
    `(($bodyTerm : Expr $n))
  | `([JS_EXPR_WITH_NAMED_ARGS ( $[$args:ident],* ) | $body:js_expr ]) => do
    let scope := args.toList.map (·.getId.toString)
    let bodyTerm ← elabExprWithScope body scope
    `(($bodyTerm : Expr $(quote scope.length)))
  | `([JS_STMT| $s:js_stmt ]) => do
    elabStmtsWithScope [s] [] none
  | `([JS_FUNC| inputs ( $[$params:ident],* ) | returns = $ret:js_expr | $[$stmts:js_stmt]* ]) => do
    let paramNames := params.toList.map (·.getId.toString)
    let body ← elabStmtsWithScope stmts.toList paramNames (some ret)
    let ret' ← elabExprWithScope ret paramNames
    let pNamesQuote := quote (params.map (·.getId.toString))
    let owns ← params.mapM (fun _ => `(Ownership.owned))
    let n := quote params.size
    `(((InlinableFunc.mk $pNamesQuote #[$[$owns],*] $body (some $ret')) : InlinableFunc $n))
  | `([JS_FUNC| inputs ( $[$params:ident],* ) | $[$stmts:js_stmt]* ]) => do
    let paramNames := params.toList.map (·.getId.toString)
    let body ← elabStmtsWithScope stmts.toList paramNames none
    let pNamesQuote := quote (params.map (·.getId.toString))
    let owns ← params.mapM (fun _ => `(Ownership.owned))
    let n := quote params.size
    `(((InlinableFunc.mk $pNamesQuote #[$[$owns],*] $body none) : InlinableFunc $n))
