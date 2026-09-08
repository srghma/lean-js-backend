/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Init.Prelude
public import Init.Data.Repr
public import LakeJs.Js

public section

namespace Lean.Compiler.JS

public def indentLines (s : String) : String :=
  let lines := (s.split (· == '\n')).toList
  String.intercalate "\n" (lines.map fun l => if l.isEmpty then "" else "  " ++ l)

mutual
  public partial def renderExpr {n : Nat} (e : Expr n) (env : Array String := #[]) : String :=
    match e with
    | .var i =>
      if i.val < env.size then env[i.val]! else s!"#${i.val}"
    | .global name => name
    | .num val => s!"{val}"
    | .numLit val => val
    | .str val => s!"\"{val}\""
    | .bool val => if val then "true" else "false"
    | .obj props =>
      let pairs := props.toList.map fun (p, v) => s!"{p}: {renderExpr v env}"
      "({ " ++ ", ".intercalate pairs ++ " })"
    | .arr elems =>
      "[" ++ ", ".intercalate (elems.toList.map (renderExpr · env)) ++ "]"
    | .call fn args =>
      if fn == Expr.global "throw" then
        match args.toList with
        | [arg] => s!"throw {renderExpr arg env}"
        | _ => s!"throw {renderExpr fn env}"
      else
        s!"{renderExpr fn env}({", ".intercalate (args.toList.map (renderExpr · env))})"
    | .prop obj name =>
      s!"{renderExpr obj env}.{name}"
    | .index obj idx =>
      s!"{renderExpr obj env}[{renderExpr idx env}]"
    | .unary op a =>
      let opStr := match op with
        | .not => "!" | .minus => "-" | .tilde => "~" | .typeof => "typeof " | _ => ""
      s!"{opStr}{renderExpr a env}"
    | .binop op a b =>
      let opStr := match op with
        | .plus => "+" | .minus => "-" | .times => "*" | .divide => "/" | .mod => "%"
        | .eq => "==" | .strictEq => "===" | .neq => "!=" | .strictNeq => "!=="
        | .le => "<=" | .lt => "<" | .gt => ">" | .ge => ">="
        | .and => "&&" | .or => "||"
        | .bitAnd => "&" | .bitOr => "|" | .bitXor => "^"
        | .lsh => "<<" | .rsh => ">>" | .ursh => ">>>"
        | _ => "=="
      s!"({renderExpr a env} {opStr} {renderExpr b env})"
    | .cond c t e =>
      s!"({renderBExpr c env} ? {renderExpr t env} : {renderExpr e env})"
    | .new cls args =>
      s!"new {renderExpr cls env}({", ".intercalate (args.toList.map (renderExpr · env))})"
    | .assign lhs rhs =>
      s!"{renderExpr lhs env} = {renderExpr rhs env}"
    | .arrowExpr params body =>
      let freshParams := (List.range params).map (fun i => s!"_p{i}")
      let env' := env ++ freshParams.toArray
      let pStr := ", ".intercalate freshParams
      s!"(({pStr}) => {renderExpr body env'})"
    | .leanGeneratedEnumIsTag obj tag =>
      s!"({renderExpr obj env}.tag === \"{mangleName tag}\")"
    | .leanGeneratedEnumGetField obj idx =>
      s!"{renderExpr obj env}._{idx + 1}"
    | .leanGeneratedEnumMk tag fields =>
      if fields.toList.isEmpty then
        s!"(\{ tag: \"{mangleName tag}\" })"
      else
        let fieldStrs := fields.toList.mapIdx fun i f => s!"_{i + 1}: {renderExpr f env}"
        s!"(\{ tag: \"{mangleName tag}\", {", ".intercalate fieldStrs} })"

  public partial def renderBExpr {n : Nat} (b : BExpr n) (env : Array String := #[]) : String :=
    match b with
    | .tt => "true"
    | .ff => "false"
    | .truthy e => renderExpr e env
    | .lt a b => s!"({renderExpr a env} < {renderExpr b env})"
    | .le a b => s!"({renderExpr a env} <= {renderExpr b env})"
    | .eq a b => s!"({renderExpr a env} == {renderExpr b env})"
    | .strictEq a b => s!"({renderExpr a env} === {renderExpr b env})"
    | .not c => s!"!{renderBExpr c env}"
    | .and c d => s!"({renderBExpr c env} && {renderBExpr d env})"
    | .or c d => s!"({renderBExpr c env} || {renderBExpr d env})"
end

mutual
  public partial def renderStmt {n : Nat} (st : Stmt n) (env : Array String := #[]) : String :=
    match st with
    | .ret e => s!"return {renderExpr e env};"
    | .letIn val k =>
      let varName := s!"_v{env.size}"
      let initStr := s!"const {varName} = {renderExpr val env};"
      let kStr := renderStmt k (env.push varName)
      s!"{initStr}\n{kStr}"
    | .letClosure f captures k =>
      let varName := s!"_v{env.size}"
      let fStr := renderInlinableFunc f
      let capStrs := captures.toList.map (renderExpr · env)
      let initStr := s!"const {varName} = {fStr}({", ".intercalate capStrs});"
      let kStr := renderStmt k (env.push varName)
      s!"{initStr}\n{kStr}"
    | .seq e k =>
      let eStr := s!"{renderExpr e env};"
      let kStr := renderStmt k env
      if kStr.isEmpty || kStr == "break;" then eStr else s!"{eStr}\n{kStr}"
    | .ifElse cond t e k =>
      let tStr := renderStmt t env
      let eStr := renderStmt e env
      let kStr := renderStmt k env
      let ifBlock :=
        if eStr.isEmpty || eStr == "break;" then
          s!"if ({renderBExpr cond env}) \{\n{indentLines tStr}\n}"
        else
          s!"if ({renderBExpr cond env}) \{\n{indentLines tStr}\n} else \{\n{indentLines eStr}\n}"
      if kStr.isEmpty || kStr == "break;" then ifBlock else s!"{ifBlock}\n{kStr}"
    | .loop m stateNames state0 cond body k =>
      let inits := (List.range m).map fun i =>
        let sName := if i < stateNames.size then stateNames[i]! else s!"_s{i}"
        let initVal := if i < state0.toList.length then renderExpr state0.toList[i]! env else "undefined"
        s!"let {sName} = {initVal};"
      let loopScope := env ++ stateNames
      let condStr := renderBExpr cond loopScope
      let bodyStr := renderStmt body loopScope
      let kStr := renderStmt k loopScope
      let initsStr := String.intercalate "\n" inits
      let loopStr :=
        if cond == BExpr.tt then
          s!"while (true) \{\n{indentLines bodyStr}\n}"
        else
          s!"while ({condStr}) \{\n{indentLines bodyStr}\n}"
      if kStr.isEmpty || kStr == "break;" then
        s!"{initsStr}\n{loopStr}"
      else
        s!"{initsStr}\n{loopStr}\n{kStr}"
    | .continue newState =>
      if newState.toList.isEmpty then
        "continue;"
      else
        let stepStrs := newState.toList.map (renderExpr · env)
        s!"continue ({", ".intercalate stepStrs});"
    | .break_ => "break;"

  public partial def renderInlinableFunc {n : Nat} (f : InlinableFunc n) : String :=
    match f with
    | .mk paramNames _ body returnsOpt =>
      let env := paramNames
      let paramsStr := String.intercalate ", " env.toList
      let bodyStr := renderStmt body env
      let retStr := match returnsOpt with
        | some r => s!"\n  return {renderExpr r env};"
        | none => ""
      s!"(({paramsStr}) => \{\n{indentLines bodyStr}{retStr}\n})"
end

public def renderJs {n : Nat} (e : Expr n) (env : Array String := #[]) : String :=
  renderExpr e env

end Lean.Compiler.JS

