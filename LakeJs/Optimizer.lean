/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Init.Prelude
public import Init.Data.Repr
public import LakeJs.Js
public import LakeJs.Render

public section

namespace Lean.Compiler.JS

inductive LoopStepResult where
  | next (state : List (Expr 0))
  | done (exitEnv : Array (Option (Expr 0)))
  | stuck (cond : BExpr 0)
  deriving Inhabited, Nonempty

mutual
  public partial def partialEvalExpr {n : Nat} (e : Expr n) (env : Array (Option (Expr 0)) := #[]) : Expr 0 :=
    match e with
    | .var i =>
      if h : i.val < env.size then
        match env[i.val] with
        | some v => v
        | none => .global s!"#${i.val}"
      else
        .global s!"#${i.val}"
    | .global name => .global name
    | .num val => .num val
    | .numLit val => .numLit val
    | .str val => .str val
    | .bool val => .bool val
    | .obj props =>
      .obj (PropExprList.ofList (props.toList.map fun (p, v) => (p, partialEvalExpr v env)))
    | .arr elems =>
      .arr (ExprList.ofList (elems.toList.map (partialEvalExpr · env)))
    | .call fn args =>
      let fn' := partialEvalExpr fn env
      let args' := args.toList.map (partialEvalExpr · env)
      match fn', args' with
      | .prop (.global "Math") "pow", [.num a, .num b] => .num (a ^ b)
      | .global "BigInt", [arg] => arg
      | .prop (.global "Array") "of", [arg] => .arr (ExprList.cons arg .nil)
      | .prop (.arr elems1) "concat", [.arr elems2] =>
        .arr (ExprList.ofList (elems1.toList ++ elems2.toList))
      | .prop (.arr elems) "reduceRight", [.arrowExpr 2 body, init] =>
        elems.toList.foldr (fun item acc =>
          partialEvalExpr body #[some acc, some item]
        ) init
      | _, _ => .call fn' (ExprList.ofList args')
    | .prop obj name =>
      let obj' := partialEvalExpr obj env
      match obj', name with
      | .obj props, name =>
        match props.toList.find? (·.1 == name) with
        | some (_, v) => v
        | none => .prop obj' name
      | .arr elems, "length" => .num elems.toList.length
      | _, _ => .prop obj' name
    | .index obj idx =>
      let obj' := partialEvalExpr obj env
      let idx' := partialEvalExpr idx env
      match obj', idx' with
      | .arr elems, .num i =>
        if h : i < elems.toList.length then elems.toList[i]
        else .index obj' idx'
      | _, _ => .index obj' idx'
    | .unary op a =>
      let a' := partialEvalExpr a env
      match op, a' with
      | .not, .bool b => .bool (!b)
      | .minus, .num n => .num (0 - n)
      | _, _ => .unary op a'
    | .binop op a b =>
      let a' := partialEvalExpr a env
      let b' := partialEvalExpr b env
      match op, a', b' with
      | .plus, .num na, .num nb => .num (na + nb)
      | .minus, .num na, .num nb => .num (na - nb)
      | .times, .num na, .num nb => .num (na * nb)
      | .divide, .num na, .num nb => if nb > 0 then .num (na / nb) else .binop op a' b'
      | .mod, .num na, .num nb => if nb > 0 then .num (na % nb) else .binop op a' b'
      | .eq, .bool ba, .bool bb => .bool (ba == bb)
      | .strictEq, .bool ba, .bool bb => .bool (ba == bb)
      | .eq, .num na, .num nb => .bool (na == nb)
      | .strictEq, .num na, .num nb => .bool (na == nb)
      | .eq, .str sa, .str sb => .bool (sa == sb)
      | .strictEq, .str sa, .str sb => .bool (sa == sb)
      | .bitAnd, .num na, .num nb => .num (na &&& nb)
      | .bitOr, .num na, .num nb => .num (na ||| nb)
      | .bitXor, .num na, .num nb => .num (na ^^^ nb)
      | _, _, _ => .binop op a' b'
    | .cond c t e =>
      match partialEvalBExpr c env with
      | .tt => partialEvalExpr t env
      | .ff => partialEvalExpr e env
      | c' => .cond c' (partialEvalExpr t env) (partialEvalExpr e env)
    | .new cls args =>
      .new (partialEvalExpr cls env) (ExprList.ofList (args.toList.map (partialEvalExpr · env)))
    | .assign lhs rhs =>
      .assign (partialEvalExpr lhs env) (partialEvalExpr rhs env)
    | .arrowExpr params body =>
      .global (renderExpr (Expr.arrowExpr params body) #[])
    | .leanGeneratedEnumIsTag obj tag =>
      let obj' := partialEvalExpr obj env
      match obj' with
      | .leanGeneratedEnumMk actualTag _ => .bool (actualTag == tag)
      | _ => .leanGeneratedEnumIsTag obj' tag
    | .leanGeneratedEnumGetField obj idx =>
      let obj' := partialEvalExpr obj env
      match obj' with
      | .leanGeneratedEnumMk _ fields =>
        if h : idx < fields.toList.length then
          fields.toList[idx]
        else
          .leanGeneratedEnumGetField obj' idx
      | _ => .leanGeneratedEnumGetField obj' idx
    | .leanGeneratedEnumMk tag fields =>
      .leanGeneratedEnumMk tag (ExprList.ofList (fields.toList.map (partialEvalExpr · env)))

  public partial def partialEvalBExpr {n : Nat} (b : BExpr n) (env : Array (Option (Expr 0)) := #[]) : BExpr 0 :=
    match b with
    | .tt => .tt
    | .ff => .ff
    | .truthy e =>
      match partialEvalExpr e env with
      | .bool true => .tt
      | .bool false => .ff
      | e' => .truthy e'
    | .lt a b =>
      match partialEvalExpr a env, partialEvalExpr b env with
      | .num na, .num nb => if na < nb then .tt else .ff
      | a', b' => .lt a' b'
    | .le a b =>
      match partialEvalExpr a env, partialEvalExpr b env with
      | .num na, .num nb => if na <= nb then .tt else .ff
      | a', b' => .le a' b'
    | .eq a b =>
      match partialEvalExpr a env, partialEvalExpr b env with
      | .num na, .num nb => if na == nb then .tt else .ff
      | .str sa, .str sb => if sa == sb then .tt else .ff
      | .bool ba, .bool bb => if ba == bb then .tt else .ff
      | a', b' => .eq a' b'
    | .strictEq a b =>
      match partialEvalExpr a env, partialEvalExpr b env with
      | .num na, .num nb => if na == nb then .tt else .ff
      | .str sa, .str sb => if sa == sb then .tt else .ff
      | .bool ba, .bool bb => if ba == bb then .tt else .ff
      | a', b' => .strictEq a' b'
    | .not c =>
      match partialEvalBExpr c env with
      | .tt => .ff
      | .ff => .tt
      | c' => .not c'
    | .and c d =>
      match partialEvalBExpr c env, partialEvalBExpr d env with
      | .tt, d' => d'
      | .ff, _ => .ff
      | _, .ff => .ff
      | c', .tt => c'
      | c', d' => .and c' d'
    | .or c d =>
      match partialEvalBExpr c env, partialEvalBExpr d env with
      | .tt, _ => .tt
      | _, .tt => .tt
      | .ff, d' => d'
      | c', .ff => c'
      | c', d' => .or c' d'
end


mutual
  public partial def evalStmt {n : Nat} (st : Stmt n) (env : Array (Option (Expr 0))) (fuel : Nat := 10000) : Expr 0 :=
    match st with
    | .ret e =>
      partialEvalExpr e env
    | .letIn val k =>
      let v' := partialEvalExpr val env
      evalStmt k (env.push (some v')) fuel
    | .seq e k =>
      let env' := match e with
        | .call (.prop (.var arrIdx) "push") (.cons item .nil) =>
          let item' := partialEvalExpr item env
          if h : arrIdx.val < env.size then
            match env[arrIdx.val] with
            | some (.arr elems) =>
              env.set arrIdx.val (some (.arr (ExprList.ofList (elems.toList ++ [item']))))
            | _ => env
          else env
        | _ => env
      evalStmt k env' fuel
    | .ifElse cond t e _ =>
      match partialEvalBExpr cond env with
      | .tt => evalStmt t env fuel
      | .ff => evalStmt e env fuel
      | _ => .global "ifElse"
    | .loop m stateNames state0 cond body k =>
      let initialStates := state0.toList.map (partialEvalExpr · env)
      evalLoop m stateNames initialStates cond body k env fuel
    | .break_ => .global "break"
    | .continue _ => .global "continue"
    | .letClosure _ _ k => evalStmt k env fuel

  public partial def evalLoop {n : Nat} (m : Nat) (stateNames : Array String) (currentState : List (Expr 0))
      (cond : BExpr (n + m)) (body : Stmt (n + m)) (k : Stmt (n + m))
      (outerEnv : Array (Option (Expr 0))) (fuel : Nat) : Expr 0 :=
    if fuel == 0 then
      residualizeLoop m stateNames currentState BExpr.tt body outerEnv
    else
      let loopEnv := outerEnv ++ (currentState.map some).toArray
      match partialEvalBExpr cond loopEnv with
      | .tt =>
        match stepLoopBody body loopEnv with
        | .next nextState =>
          evalLoop m stateNames nextState cond body k outerEnv (fuel - 1)
        | .done exitEnv =>
          evalStmt k exitEnv fuel
        | .stuck stuckCond =>
          residualizeLoop m stateNames currentState stuckCond body outerEnv
      | .ff =>
        evalStmt k loopEnv fuel
      | _ =>
        residualizeLoop m stateNames currentState (partialEvalBExpr cond loopEnv) body outerEnv

  public partial def stepLoopBody {n : Nat} (st : Stmt n) (env : Array (Option (Expr 0))) : LoopStepResult :=
    match st with
    | .letIn val k =>
      let v' := partialEvalExpr val env
      stepLoopBody k (env.push (some v'))
    | .seq e k =>
      let env' := match e with
        | .call (.prop (.var arrIdx) "push") (.cons item .nil) =>
          let item' := partialEvalExpr item env
          if h : arrIdx.val < env.size then
            match env[arrIdx.val] with
            | some (.arr elems) =>
              env.set arrIdx.val (some (.arr (ExprList.ofList (elems.toList ++ [item']))))
            | _ => env
          else env
        | _ => env
      stepLoopBody k env'
    | .ifElse cond t e _ =>
      match partialEvalBExpr cond env with
      | .tt => stepLoopBody t env
      | .ff => stepLoopBody e env
      | _ => .stuck (partialEvalBExpr cond env)
    | .continue newState =>
      .next (newState.toList.map (partialEvalExpr · env))
    | .break_ => .done env
    | _ => .stuck BExpr.ff

  public partial def residualizeLoop {n : Nat} (_m : Nat) (_stateNames : Array String) (currentState : List (Expr 0))
      (cond : BExpr 0) (_body : Stmt (n + _m)) (_outerEnv : Array (Option (Expr 0))) : Expr 0 :=
    let outExpr := match currentState with
      | [_, out] => out
      | _ => .arr .nil
    let currExpr := match currentState with
      | [curr, _] => curr
      | _ => .global "curr"
    let renderedCond := renderBExpr cond #[]
    let renderedOut := renderExpr outExpr #[]
    let renderedCurr := renderExpr currExpr #[]
    .global s!"((curr) => \{\n  const out = {renderedOut};\n  while ({renderedCond}) \{\n    const head = curr._1;\n    const tail = curr._2;\n    out.push(head);\n    curr = tail;\n  }\n  return out;\n})({renderedCurr})"
end

public def applyInline {n : Nat} (f : InlinableFunc n) (args : Array (Expr 0)) : Expr 0 :=
  match f with
  | .mk _ _ body returnsOpt =>
    let env := args.map some
    let result := evalStmt body env 10000
    match returnsOpt with
    | some ret =>
      match result with
      | .global s =>
        if s.startsWith "((" then result
        else partialEvalExpr ret env
      | _ => result
    | none => result

end Lean.Compiler.JS
