/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jules
-/
module

prelude
public import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.EmitUtil
import Lean.Compiler.NameMangling
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.ExportAttr
import Lean.Compiler.ModPkgExt
import Lean.Compiler.LCNF.Internalize
import Lean.Compiler.InitAttr
import Lean.Compiler.LCNF.Types
import Lean.Compiler.JsExternInlinedAttr
import Lean.Util.Path
import Lean.Elab.Eval
import Lean.Elab.Term
import Lean.Meta.Eval

namespace Lean.Compiler.LCNF

register_builtin_option javascript.extern_path : String := {
  defValue := ""
  descr := "path to external JS file to import externs from"
}

namespace EmitEs6

open _root_.Lean.Compiler.JS

mutual
  inductive JsExpr where
    | ident (name : String)
    | litNum (value : String)
    | litBigNum (value : String)
    | litStr (value : String)
    | litBool (value : Bool)
    | null
    | litArr (elems : Array JsExpr)
    | object (fields : Array (String × JsExpr))
    | call (fn : JsExpr) (args : Array JsExpr)
    | prop (obj : JsExpr) (field : String)
    | index (obj : JsExpr) (index : JsExpr)
    | unary (op : String) (arg : JsExpr)
    | binary (lhs : JsExpr) (op : String) (rhs : JsExpr)
    | cond (cond : JsExpr) (thenExpr : JsExpr) (elseExpr : JsExpr)
    | arrow (params : Array String) (body : Array JsStmt)
    | arrowEffectful (params : Array String) (body : Array JsStmt)
    | paren (expr : JsExpr)
    | new (name : String) (args : Array JsExpr)
    deriving Inhabited, BEq

  inductive JsStmt where
    | const (name : String) (value : JsExpr)
    | assign (lhs : JsExpr) (rhs : JsExpr)
    | return (value : JsExpr)
    | continue
    | throw (value : JsExpr)
    | ifElse (cond : JsExpr) (thenBranch : Array JsStmt) (elseBranch : Array JsStmt)
    | whileTrue (body : Array JsStmt)
    | block (body : Array JsStmt)
    | new (name : String) (args : Array JsExpr)
    deriving Inhabited, BEq
end

structure JsDecl where
  exportName : String
  value : JsExpr

structure JsModule where
  modName : Name := .anonymous
  imports : Array (String × Array String) := #[]
  externImports : Array (String × Array String) := #[]
  externExports : Array String := #[]
  decls : Array JsDecl := #[]

structure State (pu : Purity) where
  mainModName : Name := .anonymous
  currentDecl? : Option (Decl pu) := none
  joinPoints : FVarIdMap (FunDecl pu) := {}
  knownBools : FVarIdMap Bool := {}
  usedDecls : NameMap NameSet := {}
  localImpureDecls : Std.HashMap Name (Decl .impure) := {}
  usedExterns : Std.HashMap Name (Std.HashSet String) := {}
  localExterns : Std.HashSet String := {}

abbrev EmitM (pu : Purity) := StateRefT (State pu) CompilerM

def mangleString (s : String) : String :=
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
def stripRedArgSuffix (s : String) : String :=
  if s.endsWith "$__redArg" then
    (s.dropEnd 9).toString
  else if s.endsWith "__redArg" then
    (s.dropEnd 8).toString
  else
    s

def isInlinedPrimitive (name : String) : Bool :=
  let s := stripRedArgSuffix name
  s == "Nat$add" || s == "lean_nat_add" || s == "Nat$mul" || s == "lean_nat_mul" || s == "Nat$div" || s == "lean_nat_div" || s == "Nat$pow" || s == "lean_nat_pow" ||
  s == "Nat$decEq" || s == "lean_nat_dec_eq" || s == "Nat$beq" || s == "Nat$decLt" || s == "lean_nat_dec_lt" || s == "Nat$blt" ||
  s == "Nat$decLe" || s == "lean_nat_dec_le" || s == "Nat$ble" || s == "Nat$reprFast" ||
  s == "Int$ofNat" || s == "Int$negSucc" || s == "Int$add" || s == "lean_int_add" || s == "Int$sub" || s == "lean_int_sub" ||
  s == "Int$mul" || s == "lean_int_mul" || s == "Int$neg" || s == "lean_int_neg" || s == "Int$decEq" || s == "lean_int_dec_eq" || s == "Int$decLt" || s == "lean_int_dec_lt" ||
  s == "Int$decLe" || s == "lean_int_dec_le" || s == "Char$ofNat" || s == "Char$toNat" ||
  s == "USize$add" || s == "USize$sub" || s == "UInt32$add" || s == "Int$instInhabited" ||
  s == "String$append" || s == "String$Internal$append" || s == "lean_string_append" || s == "String$push" || s == "lean_string_push" ||
  s == "Array$size" || s == "Array$empty" || s == "Array$mkEmpty" || s == "Array$push" || s == "Array$append" ||
  s == "Array$get" || s == "Array$uget" || s == "Array$getInternalBorrowed" || s == "Array$getInternal" || s == "Array$ugetBorrowed" ||
  s == "String$utf8ByteSize" || s == "lean_string_utf8_byte_size"

def recordExternUse (modName : Name) (jsName : String) : EmitM pu Unit := do
  unless isInlinedPrimitive jsName do
    modify fun s =>
      let names := (s.usedExterns.getD modName {}).insert jsName
      { s with usedExterns := s.usedExterns.insert modName names }

def isLikelyImpureName (_n : Name) : Bool :=
  false


def toJsName (n : Name) (isRef : Bool := false) : EmitM pu String := do
  if n.isAnonymous then
    return ""
  else
    let n := if isBoxedName n then n.getPrefix else n
    let env ← getEnv
    if isRef then
      let s ← get
      if let some idx := env.getModuleIdxFor? n then
        let nMod := env.allImportedModuleNames[idx]!
        let sMod := nMod.toString
        let isStd := sMod == "Init" || sMod.startsWith "Init." ||
                     sMod == "Std" || sMod.startsWith "Std." ||
                     sMod == "Lean" || sMod.startsWith "Lean." ||
                     sMod == "Lake" || sMod.startsWith "Lake."
        if nMod != s.mainModName && !isStd then
          modify fun s => { s with usedDecls := s.usedDecls.insert nMod (s.usedDecls.find? nMod |>.getD {} |>.insert n) }
        else if nMod != s.mainModName && isStd then
          let hasExtern := (getExternNameFor env `javascript n).isSome || (getExternNameFor env `all n).isSome
          if !hasExtern then
            let jsName := mangleString n.toString
            recordExternUse nMod jsName
    let recordExtern (extName : String) : EmitM pu String := do
      if isRef then
        let mainModName := (← get).mainModName
        let modName :=
          match env.getModuleIdxFor? n with
          | some idx => env.allImportedModuleNames[idx]!
          | none => mainModName
        recordExternUse modName extName
      return extName
    if let some s := getExternNameFor env `javascript n then
      return ← recordExtern s
    if let some s := getExternNameFor env `all n then
      return ← recordExtern s
    match getExportNameFor? env n with
    | some (.str .anonymous s) => return s
    | some _                   => throwError "invalid export name '{n}'"
    | none                     => return mangleString n.toString

def getRelativePath (fromMod toMod : Name) : String := Id.run do
  let fromParts := fromMod.components
  let toParts := toMod.components
  let commonPrefixLen := (fromParts.zip toParts).takeWhile (fun (a, b) => a == b) |>.length
  let numUps := fromParts.length - 1 - commonPrefixLen
  let mut res := ""
  for _ in [:numUps] do
    res := res ++ "../"
  if res == "" then
    res := "./"
  let mut first := true
  for i in [commonPrefixLen:toParts.length] do
    if !first then res := res ++ "/"
    res := res ++ mangleString toParts[i]!.toString
    first := false
  return res ++ ".js"

def isClosedName (name : Name) : Bool :=
  name.isStr && name.getString!.contains "_closed_"

def isClosedJsName (name : String) : Bool :=
  name.contains "_closed_"

def isBoxedName (name : Name) : Bool :=
  name.toString.contains "_boxed_const_"

def isBoxedConstJsName (name : String) : Bool :=
  name.contains "_boxed_const_"

def isLikelyImpureJsName (_name : String) : Bool :=
  false


def isRuntimeParamType (type : Expr) : Bool :=
  let type := type.headBeta
  let _ := dbgTrace s!"isRuntimeParamType: {type}" fun _ => ()
  if type.isAppOf ``lcErased || type.isAppOf ``lcAny || type.isAppOf ``lcVoid || maybeTypeFormerType type || isPredicateType type then
    false
  else
    match type.getAppFn with
    | .const n .. =>
      let s := n.toString
      !(s == "PUnit" || s == "Unit" || s == "Lean.PUnit" || s == "Lean.Unit" ||
        s == "Void" || s == "Lean.Void" || s.endsWith ".Void" ||
        s.contains "RealWorld" || s == "lcAny" || s == "lcVoid")
    | _ => true

partial def getRuntimeArrowArity (type : Expr) : Nat :=
  match type.headBeta with
  | .forallE _ d b _ =>
    let rest := getRuntimeArrowArity b
    if isRuntimeParamType d then rest + 1 else rest
  | _ => 0

partial def isEffectResultType (type : Expr) : Bool :=
  match type.headBeta with
  | .forallE _ _ b _ => isEffectResultType b
  | t =>
    match t.getAppFn with
    | .const ``EStateM.Result .. => true
    | .const n .. =>
        let s := n.toString
        s == "Real" || s.endsWith "RealWorld" || s.contains "RealWorld" || s.contains "IO" || s.contains "ST"
    | _ => false

def getVisibleRuntimeArrowArity (type : Expr) : Nat :=
  let arity := getRuntimeArrowArity type
  if isEffectResultType type && arity > 0 then
    arity - 1
  else
    arity

def getVisibleRuntimeParams (type : Expr) (params : Array (Param .impure)) : Array (Param .impure) :=
  let params := params.filter fun p => isRuntimeParamType p.type
  if isEffectResultType type && !params.isEmpty then
    params.pop
  else
    params

partial def getArity (n : Name) : EmitM pu Nat := do
  if let some decl ← getLocalImpureDecl? n then
    return decl.params.size
  else if let some sig ← getImpureSignature? n then
    return sig.params.size
  else
    let env ← getEnv
    if let some cinfo := env.find? n then
      return cinfo.type.getForallArity
    else
      if n.getString! == "_redArg" then
        getArity n.getPrefix
      else
        if let some ty ← try some <$> liftM (LCNF.getType { name := n }) catch _ => pure none then
          return getVisibleRuntimeArrowArity ty
        else
          return 0

def getLCtx : EmitM pu LCtx := do
  let s ← liftM (get : CompilerM LCNF.CompilerM.State)
  return s.lctx

def getVarName (fvarId : FVarId) : EmitM pu String := do
  return mangleString fvarId.name.toString

def isRedundantArg (a : Arg pu) : EmitM pu Bool := do
  match a with
  | .erased | .type .. => return true
  | .fvar fvarId =>
    let type ← try
      liftM <| LCNF.getType fvarId
    catch _ =>
      return false
    return !isRuntimeParamType type

def filterRedundantArgs (args : Array (Arg .impure)) : EmitM .impure (Array (Arg .impure)) :=
  args.filterM fun a => do return !(← isRedundantArg a)

def getKnownBoolArg? (a : Arg pu) : EmitM pu (Option Bool) := do
  match a with
  | .fvar fvarId => return (← get).knownBools.get? fvarId
  | .erased | .type .. => return none

def getKnownBool? (v : LetValue pu) : EmitM pu (Option Bool) := do
  match v with
  | .const declName .. =>
    if declName == ``Bool.true then
      return some true
    else if declName == ``Bool.false then
      return some false
    else
      return none
  | .ctor info _ _ =>
    if info.name == ``Bool.true then
      return some true
    else if info.name == ``Bool.false then
      return some false
    else
      return none
  | .fvar fvarId #[] =>
    return (← get).knownBools.get? fvarId
  | .box _ fvarId _ | .unbox fvarId _ | .reset _ fvarId _ =>
    return (← get).knownBools.get? fvarId
  | .isShared .. =>
    return some true
  | _ =>
    return none

def getInlinedOp? (s : String) : Option String :=
  let s := stripRedArgSuffix s
  if s.endsWith "$add" || s == "lean_nat_add" || s == "lean_int_add" || s == "lean_float_add" || s == "lean_usize_add" || s == "lean_uint32_add" || s == "String$append" || s == "lean_string_append" || s == "String$Internal$append" then some "+"
  else if s.endsWith "$sub" || s == "lean_nat_sub" || s == "lean_int_sub" || s == "lean_float_sub" || s == "lean_usize_sub" then some "-"
  else if s.endsWith "$mul" || s == "lean_nat_mul" || s == "lean_int_mul" || s == "lean_float_mul" then some "*"
  else if s.endsWith "$decEq" || s.endsWith "$beq" || s == "lean_nat_dec_eq" || s == "lean_int_dec_eq" || s == "lean_float_dec_eq" then some "==="
  else if s.endsWith "$decLt" || s.endsWith "$blt" || s.endsWith "$decidableLT" || s.endsWith "$lt" || s == "lean_nat_dec_lt" || s == "lean_int_dec_lt" || s == "lean_float_dec_lt" then some "<"
  else if s.endsWith "$decLe" || s.endsWith "$ble" || s.endsWith "$decidableLE" || s.endsWith "$decLE" || s.endsWith "$le" || s == "lean_nat_dec_le" || s == "lean_int_dec_le" || s == "lean_float_dec_le" then some "<="
  else if s == "Int$neg" || s == "Float$neg" || s == "lean_int_neg" || s == "lean_float_neg" then some "-"
  else if s == "not" || s == "Bool$not" then some "!"
  else if s == "String" then some "String"
  else if s == "String$utf8ByteSize" || s == "lean_string_utf8_byte_size" then some "String_utf8ByteSize"
  else none

def mkJsString (s : String) : String :=
  let s := s.foldl (fun acc c =>
    if c == '\\' then acc ++ "\\\\"
    else if c == '\"' then acc ++ "\\\""
    else if c == '\n' then acc ++ "\\n"
    else if c == '\r' then acc ++ "\\r"
    else if c == '\t' then acc ++ "\\t"
    else acc.push c) ""
  "\"" ++ s ++ "\""

def containsName (names : List String) (name : String) : Bool :=
  names.any (· == name)

def insertName (names : List String) (name : String) : List String :=
  if containsName names name then names else name :: names

def eraseName (names : List String) (name : String) : List String :=
  names.filter (· != name)

def unionNames (xs ys : List String) : List String :=
  ys.foldl insertName xs

def ifElseStmt (cond : JsExpr) (thenBranch : Array JsStmt) (elseBranch : Array JsStmt := #[]) : JsStmt :=
  JsStmt.ifElse cond thenBranch elseBranch

def eraseNames (substs : List (String × JsExpr)) (names : Array String) : List (String × JsExpr) :=
  names.foldl (init := substs) fun substs name => substs.filter (·.1 != name)

def lookupSubst? (substs : List (String × JsExpr)) (name : String) : Option JsExpr :=
  substs.findSome? fun (name', value) =>
    if name' == name then some value else none

def eraseAllName (names : List String) (name : String) : List String :=
  names.filter (· != name)

def countName (names : List String) (name : String) : Nat :=
  names.foldl (init := 0) fun count name' => if name' == name then count + 1 else count

partial def isInlineAliasExpr : JsExpr → Bool
  | .ident .. | .litNum .. | .litBigNum .. | .litStr .. | .litBool .. | .null => true
  | .litArr elems => elems.all isInlineAliasExpr
  | .call (.ident "BigInt") #[arg] => isInlineAliasExpr arg
  | .prop obj _ => isInlineAliasExpr obj
  | .index obj idx => isInlineAliasExpr obj && isInlineAliasExpr idx
  | .paren expr => isInlineAliasExpr expr
  | _ => false

def isComplementaryCond (lhs rhs : JsExpr) : Bool :=
  match lhs, rhs with
  | .unary "!" lhs, rhs => lhs == rhs
  | lhs, .unary "!" rhs => lhs == rhs
  | _, _ => false

def isScalarType (type : Expr) : Bool :=
  type == ImpureType.float || type == ImpureType.float32 || type == ImpureType.uint8 ||
  type == ImpureType.uint16 || type == ImpureType.uint32 || type == ImpureType.uint64 ||
  type == ImpureType.usize

mutual
  partial def exprUses : JsExpr → List String
    | JsExpr.ident name => [name]
    | JsExpr.litNum .. | JsExpr.litBigNum .. | JsExpr.litStr .. | JsExpr.litBool .. | JsExpr.null => []
    | JsExpr.litArr elems => elems.foldl (fun used elem => unionNames used (exprUses elem)) []
    | JsExpr.object fields =>
      fields.foldl (fun used (_, value) => unionNames used (exprUses value)) []
    | JsExpr.call fn args =>
      args.foldl (fun used arg => unionNames used (exprUses arg)) (exprUses fn)
    | JsExpr.prop obj _ => exprUses obj
    | JsExpr.index obj idx => unionNames (exprUses obj) (exprUses idx)
    | JsExpr.unary _ arg => exprUses arg
    | JsExpr.binary lhs _ rhs => unionNames (exprUses lhs) (exprUses rhs)
    | JsExpr.cond cond thenExpr elseExpr =>
      unionNames (exprUses cond) (unionNames (exprUses thenExpr) (exprUses elseExpr))
    | JsExpr.arrow params body =>
      params.foldl (fun used param => eraseName used param) (stmtsUses body)
    | JsExpr.arrowEffectful params body =>
      params.foldl (fun used param => eraseName used param) (stmtsUses body)
    | JsExpr.paren expr => exprUses expr
    | JsExpr.new _ args => args.foldl (fun used arg => unionNames used (exprUses arg)) []

  partial def stmtUses : JsStmt → List String
    | JsStmt.const _ value => exprUses value
    | JsStmt.assign lhs rhs => unionNames (exprUses lhs) (exprUses rhs)
    | JsStmt.return value => exprUses value
    | JsStmt.continue => []
    | JsStmt.throw value => exprUses value
    | JsStmt.ifElse cond thenBranch elseBranch =>
      unionNames (exprUses cond) (unionNames (stmtsUses thenBranch) (stmtsUses elseBranch))
    | JsStmt.whileTrue body => stmtsUses body
    | JsStmt.block body => stmtsUses body
    | JsStmt.new _ args => args.foldl (fun used arg => unionNames used (exprUses arg)) []

  partial def stmtsUses (stmts : Array JsStmt) : List String :=
    stmts.foldl (fun used stmt => unionNames used (stmtUses stmt)) []

  partial def exprWrites : JsExpr → List String
    | JsExpr.ident name => [name]
    | JsExpr.prop obj _ => exprWrites obj
    | JsExpr.index obj _ => exprWrites obj
    | _ => []

  partial def stmtWrites : JsStmt → List String
    | JsStmt.const name _ => [name]
    | JsStmt.assign lhs _ => exprWrites lhs
    | JsStmt.ifElse _ thenBranch elseBranch => unionNames (stmtsWrites thenBranch) (stmtsWrites elseBranch)
    | JsStmt.whileTrue body => stmtsWrites body
    | JsStmt.block body => stmtsWrites body
    | JsStmt.new .. => []
    | _ => []

  partial def stmtsWrites (stmts : Array JsStmt) : List String :=
    stmts.foldl (fun written stmt => unionNames written (stmtWrites stmt)) []
end

mutual
  partial def exprUseCounts : JsExpr → List String
    | JsExpr.ident name => [name]
    | JsExpr.litNum .. | JsExpr.litBigNum .. | JsExpr.litStr .. | JsExpr.litBool .. | JsExpr.null => []
    | JsExpr.litArr elems => elems.foldl (init := []) fun used elem => used ++ exprUseCounts elem
    | JsExpr.object fields =>
      fields.foldl (init := []) fun used (_, value) => used ++ exprUseCounts value
    | JsExpr.call fn args =>
      args.foldl (init := exprUseCounts fn) fun used arg => used ++ exprUseCounts arg
    | JsExpr.prop obj _ => exprUseCounts obj
    | JsExpr.index obj idx => exprUseCounts obj ++ exprUseCounts idx
    | JsExpr.unary _ arg => exprUseCounts arg
    | JsExpr.binary lhs _ rhs => exprUseCounts lhs ++ exprUseCounts rhs
    | JsExpr.cond cond thenExpr elseExpr =>
      exprUseCounts cond ++ exprUseCounts thenExpr ++ exprUseCounts elseExpr
    | JsExpr.arrow params body =>
      params.foldl (init := stmtsUseCounts body) fun used param => eraseAllName used param
    | JsExpr.arrowEffectful params body =>
      params.foldl (init := stmtsUseCounts body) fun used param => eraseAllName used param
    | JsExpr.paren expr => exprUseCounts expr
    | JsExpr.new _ args => args.foldl (init := []) fun used arg => used ++ exprUseCounts arg

  partial def stmtUseCounts : JsStmt → List String
    | JsStmt.const _ value => exprUseCounts value
    | JsStmt.assign lhs rhs => exprUseCounts lhs ++ exprUseCounts rhs
    | JsStmt.return value => exprUseCounts value
    | JsStmt.continue => []
    | JsStmt.throw value => exprUseCounts value
    | JsStmt.ifElse cond thenBranch elseBranch =>
      exprUseCounts cond ++ stmtsUseCounts thenBranch ++ stmtsUseCounts elseBranch
    | JsStmt.whileTrue body => stmtsUseCounts body
    | JsStmt.block body => stmtsUseCounts body
    | JsStmt.new _ args => args.foldl (fun used arg => used ++ exprUseCounts arg) []

  partial def stmtsUseCounts (stmts : Array JsStmt) : List String :=
    stmts.foldl (init := []) fun used stmt => used ++ stmtUseCounts stmt
end

mutual
  partial def constThunkBodyExpr? : Array JsStmt → Option JsExpr
    | #[JsStmt.return expr] =>
      if isPureExpr expr then some expr else none
    | _ => none

  partial def isPureBuiltinCall : JsExpr → Array JsExpr → Bool
    | .ident "BigInt", #[arg] => isPureExpr arg
    | _, _ => false

  partial def isPureExpr : JsExpr → Bool
    | JsExpr.ident .. | JsExpr.litNum .. | JsExpr.litBigNum .. | JsExpr.litStr .. | JsExpr.litBool .. | JsExpr.null => true
    | JsExpr.litArr elems => elems.all isPureExpr
    | JsExpr.object fields => fields.all (fun (_, value) => isPureExpr value)
    | JsExpr.call fn args => isPureBuiltinCall fn args
    | JsExpr.prop obj _ => isPureExpr obj
    | JsExpr.index obj idx => isPureExpr obj && isPureExpr idx
    | JsExpr.unary _ arg => isPureExpr arg
    | JsExpr.binary lhs _ rhs => isPureExpr lhs && isPureExpr rhs
    | JsExpr.cond cond thenExpr elseExpr => isPureExpr cond && isPureExpr thenExpr && isPureExpr elseExpr
    | JsExpr.arrow _ body => isPureStmts body
    | JsExpr.arrowEffectful .. => false
    | JsExpr.paren expr => isPureExpr expr
    | JsExpr.new .. => false

  partial def isPureStmt : JsStmt → Bool
    | JsStmt.const _ value => isPureExpr value
    | JsStmt.assign .. | JsStmt.return .. | JsStmt.continue | JsStmt.throw .. => false
    | JsStmt.ifElse cond thenBranch elseBranch =>
      isPureExpr cond && isPureStmts thenBranch && isPureStmts elseBranch
    | JsStmt.whileTrue .. => false
    | JsStmt.block body => isPureStmts body
    | JsStmt.new .. => false

  partial def isPureStmts (stmts : Array JsStmt) : Bool :=
    stmts.all isPureStmt
end

mutual
  partial def substituteExpr (substs : List (String × JsExpr)) : JsExpr → JsExpr
    | JsExpr.ident name =>
      match lookupSubst? substs name with
      | some value => value
      | none => JsExpr.ident name
    | JsExpr.litArr elems => JsExpr.litArr (elems.map (substituteExpr substs))
    | JsExpr.object fields =>
      JsExpr.object <| fields.map fun (name, value) => (name, substituteExpr substs value)
    | JsExpr.call fn args => JsExpr.call (substituteExpr substs fn) (args.map (substituteExpr substs))
    | JsExpr.prop obj field => JsExpr.prop (substituteExpr substs obj) field
    | JsExpr.index obj idx => JsExpr.index (substituteExpr substs obj) (substituteExpr substs idx)
    | JsExpr.unary op arg => JsExpr.unary op (substituteExpr substs arg)
    | JsExpr.binary lhs op rhs => JsExpr.binary (substituteExpr substs lhs) op (substituteExpr substs rhs)
    | JsExpr.cond cond thenExpr elseExpr =>
      JsExpr.cond (substituteExpr substs cond) (substituteExpr substs thenExpr) (substituteExpr substs elseExpr)
    | JsExpr.arrow params body =>
      JsExpr.arrow params (substituteStmts (eraseNames substs params) body)
    | JsExpr.arrowEffectful params body =>
      JsExpr.arrowEffectful params (substituteStmts (eraseNames substs params) body)
    | JsExpr.paren expr => JsExpr.paren (substituteExpr substs expr)
    | JsExpr.new name args => JsExpr.new name (args.map (substituteExpr substs))
    | expr => expr

  partial def substituteStmt (substs : List (String × JsExpr)) : JsStmt → JsStmt
    | JsStmt.const name value => JsStmt.const name (substituteExpr substs value)
    | JsStmt.assign lhs rhs => JsStmt.assign (substituteExpr substs lhs) (substituteExpr substs rhs)
    | JsStmt.return value => JsStmt.return (substituteExpr substs value)
    | JsStmt.continue => JsStmt.continue
    | JsStmt.throw value => JsStmt.throw (substituteExpr substs value)
    | JsStmt.ifElse cond thenBranch elseBranch =>
      JsStmt.ifElse (substituteExpr substs cond) (substituteStmts substs thenBranch) (substituteStmts substs elseBranch)
    | JsStmt.whileTrue body => JsStmt.whileTrue (substituteStmts substs body)
    | JsStmt.block body => JsStmt.block (substituteStmts substs body)
    | JsStmt.new name args => JsStmt.new name (args.map (substituteExpr substs))

  partial def substituteStmts (substs : List (String × JsExpr)) (stmts : Array JsStmt) : Array JsStmt :=
    let rec loop (i : Nat) (substs : List (String × JsExpr)) (acc : Array JsStmt) : Array JsStmt :=
      if _h : i < stmts.size then
        let stmt := stmts[i]!
        match stmt with
        | JsStmt.const name value =>
          let stmt := JsStmt.const name (substituteExpr substs value)
          loop (i + 1) (substs.filter (·.1 != name)) (acc.push stmt)
        | stmt =>
          loop (i + 1) substs (acc.push (substituteStmt substs stmt))
      else
        acc
    loop 0 substs #[]
end

partial def stmtsToExpr? : Array JsStmt → Option JsExpr
  | #[] => none
  | stmts =>
    let rec loop (i : Nat) (expr : JsExpr) : Option JsExpr :=
      if _h : i < stmts.size - 1 then
        let idx := stmts.size - 2 - i
        match stmts[idx]! with
        | JsStmt.const name value =>
          let useCount := countName (exprUseCounts expr) name
          if useCount == 0 && isPureExpr value then
            loop (i + 1) expr
          else if useCount == 1 then
            loop (i + 1) (substituteExpr [(name, value)] expr)
          else
            none
        | _ =>
          none
      else
        some expr
    match stmts.back? with
    | some (JsStmt.return expr) => loop 0 expr
    | _ => none

/-- Fold `String.fromCodePoint(Number(litNum n))` → the single-char string literal.
    Only for code points that fit in a Unicode scalar value (≤ 0x10FFFF). -/
def foldStringPush (s : String) (codeStr : String) : Option JsExpr :=
  match codeStr.toNat? with
  | some n =>
    if n < 1114112 then -- Unicode scalar values
      some <| JsExpr.litStr (s.push (Char.ofNat n))
    else none
  | none => none

def quoteCharLiteral (codeStr : String) : Option String :=
  match codeStr.toNat? with
  | some n =>
    if n < 1114112 then
      let c := Char.ofNat n
      let body :=
        if c == '\\' then "\\\\"
        else if c == '\'' then "\\'"
        else if c == '\n' then "\\n"
        else if c == '\r' then "\\r"
        else if c == '\t' then "\\t"
        else if c == '\x00' then "\\x00"
        else String.singleton c
      some s!"'{body}'"
    else
      none
  | none => none

/-- True iff every char in `s` has code point < 128 (ASCII). -/
def isAsciiStr (s : String) : Bool :=
  s.foldl (fun ok c => ok && (c.val < 128)) true

mutual
  partial def simplifyLengthComparison? (lhs : JsExpr) (op : String) (rhs : JsExpr) : Option JsExpr :=
    match lhs, rhs with
    | .prop obj "length", .litNum _ =>
      return .binary (.prop obj "length") op rhs
    | .litNum _, .prop obj "length" =>
      return .binary lhs op (.prop obj "length")
    | _, _ =>
      none

  partial def foldBinary? (lhs : JsExpr) (op : String) (rhs : JsExpr) : Option JsExpr :=
    match lhs, op, rhs with
    | .litBool lhs, "&&", .litBool rhs => some (.litBool (lhs && rhs))
    | .litBool lhs, "||", .litBool rhs => some (.litBool (lhs || rhs))
    | .litBool lhs, "===", .litBool rhs => some (.litBool (lhs == rhs))
    | .litBool lhs, "!==", .litBool rhs => some (.litBool (lhs != rhs))
    | .litStr lhs, "===", .litStr rhs => some (.litBool (lhs == rhs))
    | .litStr lhs, "!==", .litStr rhs => some (.litBool (lhs != rhs))
    | .litNum lhs, "===", .litNum rhs => some (.litBool (lhs == rhs))
    | .litNum lhs, "!==", .litNum rhs => some (.litBool (lhs != rhs))
    | .litBigNum lhs, "===", .litBigNum rhs => some (.litBool (lhs == rhs))
    | .litBigNum lhs, "!==", .litBigNum rhs => some (.litBool (lhs != rhs))
    | .litStr lhs, "+", .litStr rhs => some (.litStr (lhs ++ rhs))
    | _, _ , _ => none

  partial def optimizeExpr : JsExpr → JsExpr
    | JsExpr.litArr elems => JsExpr.litArr (elems.map optimizeExpr)
    | JsExpr.object fields => JsExpr.object <| fields.map fun (name, value) => (name, optimizeExpr value)
    | JsExpr.call fn args =>
      let fn := optimizeExpr fn
      let args := args.map optimizeExpr
      match fn, args with
      | JsExpr.ident "Int_ofNat", #[JsExpr.litBigNum value] => JsExpr.litNum value
      | JsExpr.ident "Int_ofNat", #[JsExpr.litNum value] => JsExpr.litNum value
      | JsExpr.ident "Int_ofNat", #[JsExpr.call (.ident "BigInt") #[arg]] => arg
      -- String(litNum n) => "n"  (Nat.reprFast / Int.repr on known literal)
      | JsExpr.ident "String", #[JsExpr.litNum value] => JsExpr.litStr value
      | JsExpr.ident "String", #[JsExpr.litBigNum value] => JsExpr.litStr value
      -- Array_mkEmpty(_) => []
      | JsExpr.ident "Array_mkEmpty", #[_] => JsExpr.litArr #[]
      | JsExpr.ident "Array_mkEmpty", #[] => JsExpr.litArr #[]
      -- Array_push([...elems], elem) => [...elems, elem]
      | JsExpr.ident "Array_push", #[JsExpr.litArr elems, elem] => JsExpr.litArr (elems.push elem)
      -- String_push(s, litNum n) => s + char
      | JsExpr.ident "String_push", #[s, JsExpr.litNum codeStr] =>
        match foldStringPush "" codeStr with
        | some (JsExpr.litStr char) => JsExpr.binary s "+" (JsExpr.litStr char)
        | _ => JsExpr.call fn args
      | JsExpr.litStr s, #[] => JsExpr.litStr s
      | JsExpr.litNum s, #[] => JsExpr.litNum s
      | JsExpr.litBigNum s, #[] => JsExpr.litBigNum s
      | JsExpr.litBool b, #[] => JsExpr.litBool b
      | JsExpr.null, #[] => JsExpr.null
      | JsExpr.litArr elems, #[] => JsExpr.litArr elems
      | JsExpr.object fields, #[] => JsExpr.object fields
      -- String_Internal_length(litStr s) => s.length  [ASCII only for correctness]
      | JsExpr.ident "String_Internal_length", #[JsExpr.litStr s] =>
        if isAsciiStr s then JsExpr.litNum (toString s.length)
        else JsExpr.call fn args
      | JsExpr.ident "String$Internal$length", #[JsExpr.litStr s] =>
        if isAsciiStr s then JsExpr.litNum (toString s.length)
        else JsExpr.call fn args
      | JsExpr.ident "Char$quote", #[JsExpr.litNum codeStr] =>
        match quoteCharLiteral codeStr with
        | some s => JsExpr.litStr s
        | none => JsExpr.call fn args
      | JsExpr.paren (JsExpr.arrow #[] body), #[] =>
        match constThunkBodyExpr? body with
        | some expr => optimizeExpr expr
        | none => JsExpr.call fn args
      | JsExpr.arrow #[] body, #[] =>
        match constThunkBodyExpr? body with
        | some expr => optimizeExpr expr
        | none => JsExpr.call fn args
      | _, _ => JsExpr.call fn args
    | JsExpr.prop obj field => JsExpr.prop (optimizeExpr obj) field
    | JsExpr.index obj idx =>
      let obj := optimizeExpr obj
      let idx := optimizeExpr idx
      match idx with
      | JsExpr.litBigNum value =>
        JsExpr.index obj (JsExpr.litNum value)
      | _ => JsExpr.index obj idx
    | JsExpr.unary op arg =>
      let arg := optimizeExpr arg
      match op, arg with
      | "!", JsExpr.litBool value => JsExpr.litBool (!value)
      | _, _ => JsExpr.unary op arg
    | JsExpr.binary lhs op rhs =>
      let lhs := optimizeExpr lhs
      let rhs := optimizeExpr rhs
      match foldBinary? lhs op rhs with
      | some expr => expr
      | none =>
        if let some expr := simplifyLengthComparison? lhs op rhs then
          expr
        else
          match lhs, op, rhs with
          | JsExpr.litBool true, "&&", rhs => rhs
          | JsExpr.litBool false, "&&", _ => JsExpr.litBool false
          | JsExpr.litBool false, "||", rhs => rhs
          | JsExpr.litBool true, "||", _ => JsExpr.litBool true
          | _, _, _ => JsExpr.binary lhs op rhs
    | JsExpr.cond cond thenExpr elseExpr =>
      let cond := optimizeExpr cond
      let thenExpr := optimizeExpr thenExpr
      let elseExpr := optimizeExpr elseExpr
      if thenExpr == elseExpr then
        thenExpr
      else
        match cond, thenExpr, elseExpr with
        | JsExpr.litBool true, thenExpr, _ => thenExpr
        | JsExpr.litBool false, _, elseExpr => elseExpr
        | _, JsExpr.litBool true, JsExpr.litBool false => cond
        | _, JsExpr.litBool false, JsExpr.litBool true => JsExpr.unary "!" cond |> optimizeExpr
        | _, _, _ => JsExpr.cond cond thenExpr elseExpr
    | JsExpr.arrow params body => JsExpr.arrow params body
    | JsExpr.arrowEffectful params body => JsExpr.arrowEffectful params body
    | JsExpr.paren expr => optimizeExpr expr
    | expr => expr

  partial def mkCondExpr? (cond : JsExpr) (thenBranch : Array JsStmt) (elseBranch : Array JsStmt) : Option JsStmt :=
    match stmtsToExpr? thenBranch, stmtsToExpr? elseBranch with
    | some thenExpr, some elseExpr =>
      some <| JsStmt.return <| optimizeExpr <| JsExpr.cond cond thenExpr elseExpr
    | _, _ =>
      none

  partial def simplifyBranchByTruth (cond : JsExpr) (isTrue : Bool) (branch : Array JsStmt) : Array JsStmt :=
    match branch with
    | #[JsStmt.ifElse innerCond innerThen innerElse] =>
      if innerCond == cond then
        if isTrue then innerThen else innerElse
      else if isComplementaryCond innerCond cond then
        if isTrue then innerElse else innerThen
      else
        branch
    | _ => branch

  partial def mkIfChain (cond : JsExpr) (thenBranch : Array JsStmt) (elseBranch : Array JsStmt := #[]) : Array JsStmt :=
    let cond := optimizeExpr cond
    let thenBranch := optimizeStmts thenBranch |> simplifyBranchByTruth cond true |> optimizeStmts
    let elseBranch := optimizeStmts elseBranch |> simplifyBranchByTruth cond false |> optimizeStmts
    match cond with
    | JsExpr.unary "!" inner => mkIfChain inner elseBranch thenBranch
    | JsExpr.litBool true => thenBranch
    | JsExpr.litBool false => elseBranch
    | _ =>
      if let some stmt := mkCondExpr? cond thenBranch elseBranch then
        #[stmt]
      else
        #[JsStmt.ifElse cond thenBranch elseBranch]

  partial def simplifyStmt : JsStmt → Array JsStmt
    | JsStmt.const name value => #[JsStmt.const name (optimizeExpr value)]
    | JsStmt.assign lhs rhs =>
      let lhs := optimizeExpr lhs
      let rhs := optimizeExpr rhs
      if lhs == rhs then
        #[]
      else
        #[JsStmt.assign lhs rhs]
    | JsStmt.return value => #[JsStmt.return (optimizeExpr value)]
    | JsStmt.continue => #[JsStmt.continue]
    | JsStmt.throw value => #[JsStmt.throw (optimizeExpr value)]
    | JsStmt.ifElse cond thenBranch elseBranch => mkIfChain cond thenBranch elseBranch
    | JsStmt.whileTrue body => #[JsStmt.whileTrue (optimizeStmts body)]
    | JsStmt.block body =>
      let body := optimizeStmts body
      if body.isEmpty then #[] else #[JsStmt.block body]
    | JsStmt.new name args => #[JsStmt.new name (args.map optimizeExpr)]

  partial def optimizeStmts (stmts : Array JsStmt) : Array JsStmt :=
    let stmts := stmts.foldl (fun acc stmt => acc ++ simplifyStmt stmt) #[]
    let rec loop (i : Nat) (used : List String) (acc : Array JsStmt) : Array JsStmt :=
      if _h : i < stmts.size then
        let idx := stmts.size - 1 - i
        let stmt := stmts[idx]!
        match stmt with
        | JsStmt.const name value =>
          let useCount := countName used name
          let used := eraseAllName used name
          if useCount == 0 && isPureExpr value then
            loop (i + 1) (exprUseCounts value ++ used) acc
          else if isPureExpr value && isInlineAliasExpr value && (exprUses value).all (fun v => !(stmtsWrites acc).contains v) then
            let acc := substituteStmts [(name, value)] acc
            loop (i + 1) (exprUseCounts value ++ used) acc
          else if useCount == 1 && isPureExpr value && (exprUses value).all (fun v => !(stmtsWrites acc).contains v) then
            let acc := substituteStmts [(name, value)] acc
            loop (i + 1) (exprUseCounts value ++ used) acc
          else
            loop (i + 1) (exprUseCounts value ++ used) (Array.push acc stmt)
        | _ =>
          loop (i + 1) (stmtUseCounts stmt ++ used) (Array.push acc stmt)
      else
        acc.reverse
    loop 0 [] #[]
end

def mkArgExpr (a : Arg .impure) : EmitM .impure JsExpr := do
  match a with
  | .fvar fvarId => return JsExpr.ident (← getVarName fvarId)
  | .erased | .type .. => return JsExpr.null

def mkArgsExprs (args : Array (Arg .impure)) : EmitM .impure (Array JsExpr) := do
  let args ← filterRedundantArgs args
  args.mapM mkArgExpr

def mkCtorExpr (ctorName : Name) (args : Array JsExpr) : EmitM .impure JsExpr := do
  if ctorName == ``Bool.true then
    return JsExpr.litBool true
  else if ctorName == ``Bool.false then
    return JsExpr.litBool false
  else
    let tag ← toJsName ctorName
    let mut fields := #[("tag", JsExpr.litStr tag)]
    for i in [:args.size] do
      fields := fields.push (s!"_{i+1}", args[i]!)
    return JsExpr.object fields

def mkClosureFromSupplied (arity : Nat) (supplied : Array JsExpr) (k : Array JsExpr → JsExpr) : JsExpr :=
  if supplied.size >= arity then
    k supplied
  else
    let missing := arity - supplied.size
    let params := Array.range missing |>.map fun i => s!"x_{i+1}"
    let allArgs := supplied ++ params.map JsExpr.ident
    JsExpr.arrow params #[JsStmt.return (k allArgs)]

def mkDynamicClosureFromLength (fnExpr : JsExpr) (supplied : Array JsExpr) : JsExpr :=
  let diff := JsExpr.binary (JsExpr.prop fnExpr "length") "-" (JsExpr.litNum (toString supplied.size))
  let mkArrow (params : Array String) : JsExpr :=
    let extra := params.map JsExpr.ident
    JsExpr.arrow params #[JsStmt.return (JsExpr.call fnExpr (supplied ++ extra))]
  -- diff === 0: all supplied args cover the function arity; wrap in zero-arg thunk
  -- so the result is still a callable closure (e.g. for use as `cond` in whileE)
  JsExpr.cond (JsExpr.binary diff "===" (JsExpr.litNum "0")) (mkArrow #[])
    (JsExpr.cond (JsExpr.binary diff "===" (JsExpr.litNum "1")) (mkArrow #["x_1"])
      (JsExpr.cond (JsExpr.binary diff "===" (JsExpr.litNum "2")) (mkArrow #["x_1", "x_2"]) (mkArrow #["x_1", "x_2", "x_3"])))

def mkResultClosureFromSupplied (resultType : Expr) (supplied : Array JsExpr) (k : Array JsExpr → JsExpr) : JsExpr :=
  let resultArity := getRuntimeArrowArity resultType
  if isEffectResultType resultType && resultArity == 1 then
    JsExpr.arrowEffectful #[] #[JsStmt.return (k supplied)]
  else
    mkClosureFromSupplied resultArity supplied k

def getRuntimeArity (n : Name) : EmitM .impure Nat := do
  if n == (← get).mainModName ++ `main then return 1
  if let some decl ← getLocalImpureDecl? n then
    return decl.params.foldl (init := 0) fun acc p => if isRuntimeParamType p.type then acc + 1 else acc
  else if let some sig ← getImpureSignature? n then
    return sig.params.foldl (init := 0) fun acc p => if isRuntimeParamType p.type then acc + 1 else acc
  else if let some ty ← try some <$> liftM (LCNF.getType { name := n }) catch _ => pure none then
    return getVisibleRuntimeArrowArity ty
  else
    return ← getArity n

def getKnownFVarArity? (fvarId : FVarId) : EmitM .impure (Option Nat) := do
  if let some decl ← liftM <| findFunDecl? (pu := .impure) fvarId then
    return some <| decl.params.foldl (init := 0) fun acc p => if isRuntimeParamType p.type then acc + 1 else acc
  else
    try
      let type ← liftM <| LCNF.getType fvarId
      return some <| getRuntimeArrowArity type
    catch _ =>
      return none

partial def toEmitJsExpr (e : JsInlineExpr) (args : Array JsExpr) : JsExpr :=
  match e with
  | .identifier name => .ident name
  | .arg idx => args[idx]!
  | .num val => .litNum s!"{val}"
  | .numLit val => .litNum val
  | .str val => .litStr val
  | .array elems => .litArr (elems.map (toEmitJsExpr · args))
  | .call fn fnArgs => .call (toEmitJsExpr fn args) (fnArgs.map (toEmitJsExpr · args))
  | .prop obj name => .prop (toEmitJsExpr obj args) name
  | .bracketAccess obj idx => .index (toEmitJsExpr obj args) (toEmitJsExpr idx args)
  | .unary op arg => .unary op (toEmitJsExpr arg args)
  | .binary op lhs rhs =>
    let opStr := match op with
      | .add => "+"
      | .sub => "-"
      | .mul => "*"
      | .div => "/"
      | .mod => "%"
      | .pow => "**"
      | .eq => "==="
      | .le => "<="
      | .lt => "<"
      | .gt => ">"
      | .bitAnd => "&"
      | .rightShift => ">>>"
    .binary (toEmitJsExpr lhs args) opStr (toEmitJsExpr rhs args)
  | .cond c t e => .cond (toEmitJsExpr c args) (toEmitJsExpr t args) (toEmitJsExpr e args)
  | .new name newArgs => .new name (newArgs.map (toEmitJsExpr · args))

def elabJsExpr (stx : Syntax) : EmitM .impure JsInlineExpr := do
  -- Fast path: if the stored syntax is a plain ident, try the hardcoded builtin table first
  if stx.isIdent then
    if let some e := _root_.Lean.Compiler.resolveBuiltinJsExternInlined? stx.getId then
      return e
  -- General path: elaborate the term and evaluate it to a JsInlineExpr value
  try
    let expr ← liftM (m := MetaM) <| Term.TermElabM.run' <| Term.elabTerm stx (some (mkConst ``Lean.Compiler.JS.JsInlineExpr))
    liftM (m := MetaM) <| evalJsInlineExpr expr
  catch e =>
    throwErrorAt stx s!"invalid `js_extern_inlined` term: {← e.toMessageData.toString}"

def mkCallLikeExpr (fnName : Name) (rawArgs : Array (Arg .impure)) : EmitM .impure JsExpr := do
  let args ← mkArgsExprs rawArgs
  if let some jsStx := getJsExternInlined? (← getEnv) fnName then
    let jsExpr ← elabJsExpr jsStx
    let arity ← getRuntimeArity fnName
    return mkClosureFromSupplied arity args fun allArgs => toEmitJsExpr jsExpr allArgs
  let mkUnaryLambda (k : JsExpr → JsExpr) : JsExpr :=
    JsExpr.arrow #["x_1"] #[JsStmt.return (k (JsExpr.ident "x_1"))]
  let mkBinaryLambda (k : JsExpr → JsExpr → JsExpr) : JsExpr :=
    JsExpr.arrow #["x_1", "x_2"] #[JsStmt.return (k (JsExpr.ident "x_1") (JsExpr.ident "x_2"))]
  let mkNamedCall (name : String) : EmitM .impure JsExpr := do
    let expr := JsExpr.ident name
    let arity ← getRuntimeArity fnName
    if args.isEmpty then
      match getInlinedOp? name with
      | some "String" => return mkUnaryLambda fun x => JsExpr.call (JsExpr.ident "String") #[x]
      | some "!" => return mkUnaryLambda fun x => JsExpr.unary "!" x
      | some "-" =>
        if arity == 1 then
          return mkUnaryLambda fun x => JsExpr.unary "-" x
        else if arity == 2 then
          return mkBinaryLambda fun x y => JsExpr.binary x "-" y
      | some "+" =>
        if arity == 2 then
          return mkBinaryLambda fun x y => JsExpr.binary x "+" y
      | some "*" =>
        if arity == 2 then
          return mkBinaryLambda fun x y => JsExpr.binary x "*" y
      | some "===" =>
        if arity == 2 then
          return mkBinaryLambda fun x y => JsExpr.binary x "===" y
      | some "<" =>
        if arity == 2 then
          return mkBinaryLambda fun x y => JsExpr.binary x "<" y
      | some "<=" =>
        if arity == 2 then
          return mkBinaryLambda fun x y => JsExpr.binary x "<=" y
      | _ => pure ()
    if arity == 0 && !isClosedName fnName then
      return JsExpr.call expr #[]
    else if !args.isEmpty && args.size < arity then
      return mkDynamicClosureFromLength expr args
    else if !args.isEmpty then
      return JsExpr.call expr args
    else
      return expr
  let jsName ← toJsName fnName (isRef := true)
  let jsNameBase := stripRedArgSuffix jsName
  if jsNameBase == "Nat$add" || jsNameBase == "lean_nat_add" || jsNameBase == "Int$add" || jsNameBase == "lean_int_add" || jsNameBase == "Float$add" ||
      jsNameBase == "String$append" || jsNameBase == "lean_string_append" || jsNameBase == "String$Internal$append" || jsNameBase == "USize$add" then
    if args.size == 2 then return JsExpr.binary args[0]! "+" args[1]!
    else if args.size < 2 then return mkClosureFromSupplied 2 args fun allArgs => JsExpr.binary allArgs[0]! "+" allArgs[1]!
    else return ← mkNamedCall jsName
  else if jsNameBase == "Nat$mul" || jsNameBase == "lean_nat_mul" || jsNameBase == "Int$mul" || jsNameBase == "lean_int_mul" || jsNameBase == "Float$mul" then
    if args.size == 2 then return JsExpr.binary args[0]! "*" args[1]!
    else if args.size < 2 then return mkClosureFromSupplied 2 args fun allArgs => JsExpr.binary allArgs[0]! "*" allArgs[1]!
    else return ← mkNamedCall jsName
  else if jsNameBase == "Int$sub" || jsNameBase == "lean_int_sub" || jsNameBase == "Float$sub" || jsNameBase == "USize$sub" then
    if args.size == 2 then return JsExpr.binary args[0]! "-" args[1]!
    else if args.size < 2 then return mkClosureFromSupplied 2 args fun allArgs => JsExpr.binary allArgs[0]! "-" allArgs[1]!
    else return ← mkNamedCall jsName
  else if jsNameBase == "Nat$sub" || jsNameBase == "lean_nat_sub" then
    if args.size == 2 then return JsExpr.call (JsExpr.prop (JsExpr.ident "Math") "max") #[JsExpr.litNum "0", JsExpr.binary args[0]! "-" args[1]!]
    else if args.size < 2 then return mkClosureFromSupplied 2 args fun allArgs => JsExpr.call (JsExpr.prop (JsExpr.ident "Math") "max") #[JsExpr.litNum "0", JsExpr.binary allArgs[0]! "-" allArgs[1]!]
    else return ← mkNamedCall jsName
  else if jsNameBase == "Nat$div" || jsNameBase == "lean_nat_div" then
    if args.size == 2 then return JsExpr.cond (JsExpr.binary args[1]! "===" (JsExpr.litNum "0")) (JsExpr.litNum "0") (JsExpr.call (JsExpr.prop (JsExpr.ident "Math") "trunc") #[JsExpr.binary args[0]! "/" args[1]!])
    else if args.size < 2 then return mkClosureFromSupplied 2 args fun allArgs => JsExpr.cond (JsExpr.binary allArgs[1]! "===" (JsExpr.litNum "0")) (JsExpr.litNum "0") (JsExpr.call (JsExpr.prop (JsExpr.ident "Math") "trunc") #[JsExpr.binary allArgs[0]! "/" allArgs[1]!])
    else return ← mkNamedCall jsName
  else if jsNameBase == "Nat$pow" || jsNameBase == "lean_nat_pow" then
    if args.size == 2 then return JsExpr.call (JsExpr.prop (JsExpr.ident "Math") "pow") args
    else if args.size < 2 then return mkClosureFromSupplied 2 args fun allArgs => JsExpr.call (JsExpr.prop (JsExpr.ident "Math") "pow") allArgs
    else return ← mkNamedCall jsName
  else if jsNameBase == "Nat$decEq" || jsNameBase == "lean_nat_dec_eq" || jsNameBase == "Nat$beq" || jsNameBase == "Int$decEq" || jsNameBase == "lean_int_dec_eq" || jsNameBase == "Bool$beq" then
    if args.size == 2 then return JsExpr.binary args[0]! "===" args[1]!
    else if args.size < 2 then return mkClosureFromSupplied 2 args fun allArgs => JsExpr.binary allArgs[0]! "===" allArgs[1]!
    else return ← mkNamedCall jsName
  else if jsNameBase == "Nat$decLt" || jsNameBase == "lean_nat_dec_lt" || jsNameBase == "Nat$blt" || jsNameBase == "Int$decLt" || jsNameBase == "lean_int_dec_lt" then
    if args.size == 2 then return JsExpr.binary args[0]! "<" args[1]!
    else if args.size < 2 then return mkClosureFromSupplied 2 args fun allArgs => JsExpr.binary allArgs[0]! "<" allArgs[1]!
    else return ← mkNamedCall jsName
  else if jsNameBase == "Nat$decLe" || jsNameBase == "lean_nat_dec_le" || jsNameBase == "Nat$ble" || jsNameBase == "Int$decLe" || jsNameBase == "lean_int_dec_le" then
    if args.size == 2 then return JsExpr.binary args[0]! "<=" args[1]!
    else if args.size < 2 then return mkClosureFromSupplied 2 args fun allArgs => JsExpr.binary allArgs[0]! "<=" allArgs[1]!
    else return ← mkNamedCall jsName
  else if jsNameBase == "String$push" || jsNameBase == "lean_string_push" then
    if args.size == 2 then return JsExpr.binary args[0]! "+" (JsExpr.call (JsExpr.prop (JsExpr.ident "String") "fromCodePoint") #[args[1]!])
    else if args.size < 2 then return mkClosureFromSupplied 2 args fun allArgs => JsExpr.binary allArgs[0]! "+" (JsExpr.call (JsExpr.prop (JsExpr.ident "String") "fromCodePoint") #[allArgs[1]!])
    else return ← mkNamedCall jsName
  else if jsNameBase == "Nat$reprFast" || jsNameBase == "Int$repr" then
    if args.size == 1 then return JsExpr.call (JsExpr.ident "String") args
    else if args.isEmpty then return JsExpr.arrow #["x_1"] #[JsStmt.return (JsExpr.call (JsExpr.ident "String") #[JsExpr.ident "x_1"])]
    else return ← mkNamedCall jsName
  else if jsNameBase == "Int$ofNat" || jsNameBase == "lean_nat_to_int" || jsNameBase == "USize$ofNat" || jsNameBase == "USize$toNat" || jsNameBase == "UInt32$ofNat" then
    if args.size == 1 then return args[0]!
    else if args.isEmpty then return JsExpr.arrow #["x_1"] #[JsStmt.return (JsExpr.ident "x_1")]
    else return ← mkNamedCall jsName
  else if jsNameBase == "Int$negSucc" then
    if args.size == 1 then return JsExpr.unary "-" (JsExpr.binary args[0]! "+" (JsExpr.litNum "1"))
    else if args.isEmpty then return JsExpr.arrow #["x_1"] #[JsStmt.return (JsExpr.unary "-" (JsExpr.binary (JsExpr.ident "x_1") "+" (JsExpr.litNum "1")))]
    else return ← mkNamedCall jsName
  else if jsNameBase == "Int$neg" || jsNameBase == "lean_int_neg" then
    if args.size == 1 then return JsExpr.unary "-" args[0]!
    else if args.isEmpty then return JsExpr.arrow #["x_1"] #[JsStmt.return (JsExpr.unary "-" (JsExpr.ident "x_1"))]
    else return ← mkNamedCall jsName
  else if jsNameBase == "Char$ofNat" then
    if args.size == 1 then return JsExpr.call (JsExpr.prop (JsExpr.ident "String") "fromCodePoint") args
    else if args.isEmpty then return JsExpr.arrow #["x_1"] #[JsStmt.return (JsExpr.call (JsExpr.prop (JsExpr.ident "String") "fromCodePoint") #[JsExpr.ident "x_1"])]
    else return ← mkNamedCall jsName
  else if jsNameBase == "Char$toNat" then
    if args.size == 1 then return JsExpr.call (JsExpr.prop args[0]! "codePointAt") #[JsExpr.litNum "0"]
    else if args.isEmpty then return JsExpr.arrow #["x_1"] #[JsStmt.return (JsExpr.call (JsExpr.prop (JsExpr.ident "x_1") "codePointAt") #[JsExpr.litNum "0"])]
    else return ← mkNamedCall jsName
  else if jsNameBase == "UInt32$add" then
    if args.size == 2 then return JsExpr.binary (JsExpr.binary args[0]! "+" args[1]!) ">>>" (JsExpr.litNum "0")
    else if args.size < 2 then return mkClosureFromSupplied 2 args fun allArgs => JsExpr.binary (JsExpr.binary allArgs[0]! "+" allArgs[1]!) ">>>" (JsExpr.litNum "0")
    else return ← mkNamedCall jsName
  else if jsNameBase == "Int$instInhabited" then
    return JsExpr.object #[("default", JsExpr.litNum "0")]
  else if jsNameBase.endsWith "Array_size" || jsNameBase.endsWith "Array$size" ||
      jsNameBase.endsWith "String_Internal_length" || jsNameBase.endsWith "String$Internal$length" then
    if args.size == 1 then
      return JsExpr.prop args[0]! "length"
    else if args.size < 1 then
      return mkClosureFromSupplied 1 args fun allArgs => JsExpr.prop allArgs[0]! "length"
    else
      return ← mkNamedCall jsName
  else if jsNameBase.endsWith "Array_get" || jsNameBase.endsWith "Array$get" ||
      jsNameBase.endsWith "Array_uget" || jsNameBase.endsWith "Array$uget" ||
      jsNameBase.endsWith "Array_getInternalBorrowed" || jsNameBase.endsWith "Array$getInternalBorrowed" ||
      jsNameBase.endsWith "Array_getInternal" || jsNameBase.endsWith "Array$getInternal" ||
      jsNameBase.endsWith "Array_ugetBorrowed" || jsNameBase.endsWith "Array$ugetBorrowed" then
    if args.size == 2 then
      return JsExpr.index args[0]! args[1]!
    else if args.size < 2 then
      return mkClosureFromSupplied 2 args fun allArgs => JsExpr.index allArgs[0]! allArgs[1]!
    else
      return ← mkNamedCall jsName
  else if jsNameBase.endsWith "Array_push" || jsNameBase.endsWith "Array$push" then
    if args.size == 2 then
      return JsExpr.litArr #[JsExpr.unary "..." args[0]!, args[1]!]
    else if args.size < 2 then
      return mkClosureFromSupplied 2 args fun allArgs =>
        JsExpr.litArr #[JsExpr.unary "..." allArgs[0]!, allArgs[1]!]
    else
      return ← mkNamedCall jsName
  else if jsNameBase.endsWith "Array_append" || jsNameBase.endsWith "Array$append" then
    if args.size == 2 then
      return JsExpr.litArr #[JsExpr.unary "..." args[0]!, JsExpr.unary "..." args[1]!]
    else if args.size < 2 then
      return mkClosureFromSupplied 2 args fun allArgs =>
        JsExpr.litArr #[JsExpr.unary "..." allArgs[0]!, JsExpr.unary "..." allArgs[1]!]
    else
      return ← mkNamedCall jsName
  else if jsNameBase.endsWith "Array$empty" || jsNameBase.endsWith "Array$mkEmpty" then
    return JsExpr.litArr #[]
  else if jsNameBase.endsWith "Int$ofNat" || jsNameBase.endsWith "Float$ofNat" || jsNameBase.endsWith "Float$ofInt" ||
          jsNameBase.endsWith "USize$ofNat" || jsNameBase.endsWith "USize$toNat" || jsNameBase.endsWith "UInt8$ofNat" || jsNameBase.endsWith "UInt16$ofNat" ||
          jsNameBase.endsWith "UInt32$ofNat" || jsNameBase.endsWith "UInt64$ofNat" then
    if args.size == 1 then return args[0]!
    else if args.isEmpty then return JsExpr.arrow #["x_1"] #[JsStmt.return (JsExpr.ident "x_1")]
    else return ← mkNamedCall jsName
  else if jsNameBase.endsWith "Array$mk" then
    if args.size == 1 then return JsExpr.call (JsExpr.ident jsName) args
    else if args.isEmpty then return JsExpr.arrow #["x_1"] #[JsStmt.return (JsExpr.call (JsExpr.ident jsName) #[JsExpr.ident "x_1"])]
    else return ← mkNamedCall jsName
  else if jsNameBase == "IO$getStdout" || jsNameBase == "IO$getStderr" || jsNameBase == "IO$getStdin" then
    if args.isEmpty then return JsExpr.call (JsExpr.ident jsName) #[]
    else if args.size == 1 then return JsExpr.call (JsExpr.ident jsName) #[args[0]!]
    else return ← mkNamedCall jsName
  else if jsNameBase.endsWith "Nat$sub" || jsNameBase.endsWith "Int$sub" || jsNameBase.endsWith "Float$sub" then
    if args.size == 2 then
      if jsNameBase.endsWith "Nat$sub" then
        return JsExpr.call (JsExpr.ident "Nat$sub") #[args[0]!, args[1]!]
      else
        return JsExpr.binary args[0]! "-" args[1]!
    else return ← mkNamedCall jsName
  else if jsNameBase.endsWith "String$push" then
    if args.size == 2 then
      return JsExpr.binary args[0]! "+" (JsExpr.call (JsExpr.prop (JsExpr.ident "String") "fromCodePoint") #[args[1]!])
    else return ← mkNamedCall jsName
  else if jsNameBase.endsWith "Float$toString" || jsNameBase.endsWith "Nat$reprFast" || jsNameBase.endsWith "Int$repr" then
    if args.size == 1 then
      if jsNameBase.endsWith "Float$toString" then
        return JsExpr.call (JsExpr.prop args[0]! "toFixed") #[JsExpr.litNum "6"]
      else
        return JsExpr.call (JsExpr.ident "String") args
    else if args.size < 1 then
      if jsNameBase.endsWith "Float$toString" then
        return mkClosureFromSupplied 1 args fun allArgs =>
          JsExpr.call (JsExpr.prop allArgs[0]! "toFixed") #[JsExpr.litNum "6"]
      else
        return mkClosureFromSupplied 1 args fun allArgs => JsExpr.call (JsExpr.ident "String") allArgs
    else return ← mkNamedCall jsName
  else if jsNameBase.endsWith "Nat$add" || jsNameBase.endsWith "Int$add" || jsNameBase.endsWith "Float$add" ||
      jsNameBase.endsWith "String$append" || jsNameBase.endsWith "String$Internal$append" then
    if args.size == 2 then
      return JsExpr.binary args[0]! "+" args[1]!
    else return ← mkNamedCall jsName
  else if jsNameBase.endsWith "Nat$mul" || jsNameBase.endsWith "Int$mul" || jsNameBase.endsWith "Float$mul" then
    if args.size == 2 then
      return JsExpr.binary args[0]! "*" args[1]!
    else return ← mkNamedCall jsName
  else if jsNameBase.endsWith "Float$div" then
    if args.size == 2 then
      return JsExpr.binary args[0]! "/" args[1]!
    else return ← mkNamedCall jsName
  else if jsNameBase.endsWith "Nat$div" then
    if args.size == 2 then
      return JsExpr.cond (JsExpr.binary args[1]! "===" (JsExpr.litNum "0")) (JsExpr.litNum "0") (JsExpr.call (JsExpr.prop (JsExpr.ident "Math") "trunc") #[JsExpr.binary args[0]! "/" args[1]!])
    else return ← mkNamedCall jsName
  else if jsNameBase.endsWith "Nat$mod" then
    if args.size == 2 then
      return JsExpr.cond (JsExpr.binary args[1]! "===" (JsExpr.litNum "0")) args[0]! (JsExpr.binary args[0]! "%" args[1]!)
    else return ← mkNamedCall jsName
  else if jsNameBase.endsWith "Int$negSucc" then
    if args.size == 1 then
      return JsExpr.unary "-" (JsExpr.binary args[0]! "+" (JsExpr.litNum "1"))
    else return ← mkNamedCall jsName
  else if jsNameBase.endsWith "Char$ofNat" then
    if args.size == 1 then
      return JsExpr.call (JsExpr.prop (JsExpr.ident "String") "fromCodePoint") #[args[0]!]
    else return ← mkNamedCall jsName
  else if jsNameBase.endsWith "Char$toNat" then
    if args.size == 1 then
      return JsExpr.call (JsExpr.prop args[0]! "codePointAt") #[JsExpr.litNum "0"]
    else return ← mkNamedCall jsName
  else if jsNameBase.endsWith "Char$quote" then
    if args.size == 1 then
      return optimizeExpr <| JsExpr.call (JsExpr.ident jsName) #[args[0]!]
    else
      return ← mkNamedCall jsName
  else if jsNameBase.endsWith "decEq" || jsNameBase.endsWith "beq" then
    if args.size == 2 then
      return JsExpr.binary args[0]! "===" args[1]!
    else return ← mkNamedCall jsName
  else if jsNameBase.endsWith "decLt" || jsNameBase.endsWith "blt" || jsNameBase.endsWith "decidableLT" || jsNameBase.endsWith "lt" then
    if args.size == 2 then
      return JsExpr.binary args[0]! "<" args[1]!
    else return ← mkNamedCall jsName
  else if jsNameBase.endsWith "decLe" || jsNameBase.endsWith "ble" || jsNameBase.endsWith "decidableLE" || jsNameBase.endsWith "decLE" || jsNameBase.endsWith "le" then
    if args.size == 2 then
      return JsExpr.binary args[0]! "<=" args[1]!
    else return ← mkNamedCall jsName
  else if jsName == "Int$neg" || jsName == "Float$neg" then
    if args.size == 1 then
      return JsExpr.unary "-" args[0]!
    else return ← mkNamedCall jsName
  else if jsName == "not" || jsName == "Bool$not" then
    if args.size == 1 then
      return JsExpr.unary "!" args[0]!
    else return ← mkNamedCall jsName
  else if jsName.endsWith "Bool$true" then
    return JsExpr.litBool true
  else if jsName.endsWith "Bool$false" then
    return JsExpr.litBool false
  else
    return ← mkNamedCall jsName

partial def mkLetValueExpr (v : LetValue .impure) (resultType? : Option Expr := none) : EmitM .impure JsExpr := do
  let expr ← match v with
    | .lit (.nat n) => pure <| JsExpr.litNum (toString n)
    | .lit (.str s) => pure <| JsExpr.litStr s
    | .lit (.uint8 n) => pure <| JsExpr.litNum (toString n)
    | .lit (.uint16 n) => pure <| JsExpr.litNum (toString n)
    | .lit (.uint32 n) => pure <| JsExpr.litNum (toString n)
    | .lit (.uint64 n) => pure <| JsExpr.litNum (toString n)
    | .lit (.usize n) => pure <| JsExpr.litNum (toString n)
    | .const declName _ fnArgs _ => mkCallLikeExpr declName fnArgs
    | .fvar fvarId fnArgs =>
      let args ← mkArgsExprs fnArgs
      if !fnArgs.isEmpty then
        let expr := JsExpr.ident (← getVarName fvarId)
        if let some resultType := resultType? then
          let resultArity := getRuntimeArrowArity resultType
          if resultArity > 0 then
            pure <| mkResultClosureFromSupplied resultType #[] fun restArgs => JsExpr.call expr (args ++ restArgs)
          else if let some arity ← getKnownFVarArity? fvarId then
            if args.size < arity then
              pure <| mkDynamicClosureFromLength expr args
            else
              pure <| JsExpr.call expr args
          else
            pure <| JsExpr.call expr args
        else if let some arity ← getKnownFVarArity? fvarId then
          if args.size < arity then
            pure <| mkDynamicClosureFromLength expr args
          else
            pure <| JsExpr.call expr args
        else
          pure <| JsExpr.call expr args
      else
        if let some letDecl ← liftM <| findLetDecl? (pu := .impure) fvarId then
          match letDecl.value with
          | .const declName _ #[] _ =>
            if (← getArity declName) == 0 && !isClosedName declName then
              pure <| JsExpr.call (JsExpr.ident (← toJsName declName)) #[]
            else
              pure <| JsExpr.ident (← getVarName fvarId)
          | _ =>
            pure <| JsExpr.ident (← getVarName fvarId)
        else
          pure <| JsExpr.ident (← getVarName fvarId)
    | .fap fn fnArgs _ | .pap fn fnArgs _ =>
      mkCallLikeExpr fn fnArgs
    | .ctor info ctorArgs _ =>
      let args ← (← filterRedundantArgs ctorArgs).mapM mkArgExpr
      let tag ← toJsName info.name
      if isScalarType (mkConst info.name) then
        pure <| JsExpr.litNum (toString info.cidx)
      else
        let mut fields := #[("tag", JsExpr.litStr tag)]
        for i in [:args.size] do
          fields := fields.push (s!"_{i+1}", args[i]!)
        pure <| JsExpr.object fields
    | .proj _ i fvarId ..
    | .oproj i fvarId ..
    | .uproj i fvarId .. =>
      pure <| JsExpr.prop (JsExpr.ident (← getVarName fvarId)) s!"_{i+1}"
    | .sproj i offset fvarId .. =>
      pure <| JsExpr.prop (JsExpr.ident (← getVarName fvarId)) s!"_{i + offset + 1}"
    | .reuse _ info _ reuseArgs _ =>
      let args ← (← filterRedundantArgs reuseArgs).mapM mkArgExpr
      let tag ← toJsName info.name
      let mut fields := #[("tag", JsExpr.litStr tag)]
      for i in [:args.size] do
        fields := fields.push (s!"_{i+1}", args[i]!)
      pure <| JsExpr.object fields
    | .isShared .. =>
      pure <| JsExpr.litBool true
    | .box _ fvarId _ | .unbox fvarId _ | .reset _ fvarId _ =>
      pure <| JsExpr.ident (← getVarName fvarId)
    | .erased =>
      pure <| JsExpr.null
  return expr

def mkBlock (body : Array JsStmt) : Array JsStmt :=
  body

partial def mkTailRecursiveJump? (decl : LetDecl .impure) (k : Code .impure) : EmitM .impure (Option (Array JsStmt)) := do
  let some currentDecl := (← get).currentDecl? | return none
  match k, decl.value with
  | .return fvarId, .const declName _ args _
  | .return fvarId, .fap declName args _ =>
    if fvarId == decl.fvarId && declName == currentDecl.name then
      let args ← filterRedundantArgs args
      let params := currentDecl.params.filter fun (p : Param .impure) => isRuntimeParamType p.type
      let mut stmts := #[]
      for i in [:args.size] do
        stmts := stmts.push <| JsStmt.const s!"_tmp_{i}" (← mkArgExpr args[i]!)
      for i in [:args.size] do
        stmts := stmts.push <| JsStmt.assign (JsExpr.ident (← getVarName params[i]!.fvarId)) (JsExpr.ident s!"_tmp_{i}")
      stmts := stmts.push JsStmt.continue
      return some stmts
    else
      return none
  | _, _ =>
    return none

mutual
partial def mkCode (code : Code .impure) : EmitM .impure (Array JsStmt) := do
    match code with
    | .let decl k =>
      modifyLCtx fun lctx => lctx.addLetDecl decl
      let oldKnown := (← get).knownBools
      if let some b ← getKnownBool? decl.value then
        modify fun s => { s with knownBools := s.knownBools.insert decl.fvarId b }
      if let some stmts ← mkTailRecursiveJump? decl k then
        modify fun s => { s with knownBools := oldKnown }
        return optimizeStmts stmts
      let stmt := JsStmt.const (← getVarName decl.fvarId) (← mkLetValueExpr decl.value (some decl.type))
      let rest ← mkCode k
      modify fun s => { s with knownBools := oldKnown }
      return #[stmt] ++ rest
    | .return fvarId =>
      return #[JsStmt.return (JsExpr.ident (← getVarName fvarId))]
    | .cases c =>
      mkCases c
    | .jmp fvarId args => do
      let s ← get
      match s.joinPoints.get? fvarId with
      | some decl =>
        let oldLCtx ← getLCtx
        let oldKnownBools := (← get).knownBools
        for p in decl.params do
          modifyLCtx fun lctx => lctx.addParam p
        let mut bindings := #[]
        for i in [:args.size] do
          let name ← getVarName decl.params[i]!.fvarId
          bindings := bindings.push <| JsStmt.const name (← mkArgExpr args[i]!)
          if let some b ← getKnownBoolArg? args[i]! then
            modify fun s => { s with knownBools := s.knownBools.insert decl.params[i]!.fvarId b }
        let body ← mkCode decl.value
        modify fun s => { s with knownBools := oldKnownBools }
        modifyLCtx fun _ => oldLCtx
        let body := optimizeStmts (bindings ++ body)
        if bindings.isEmpty then
          return body
        else
          return optimizeStmts <| #[JsStmt.block body]
      | none =>
        return #[JsStmt.return (JsExpr.call (JsExpr.ident (← getVarName fvarId)) (← mkArgsExprs args))]
    | .jp decl k => do
      modifyLCtx fun lctx => lctx.addFunDecl decl
      modify fun s => { s with joinPoints := s.joinPoints.insert decl.fvarId decl }
      mkCode k
    | .fun decl k _ => do
      modifyLCtx fun lctx => lctx.addFunDecl decl
      let oldLCtx ← getLCtx
      for p in decl.params do
        modifyLCtx fun lctx => lctx.addParam p
      let params := decl.params.filter fun p => isRuntimeParamType p.type
      let paramNames ← params.mapM fun p => getVarName p.fvarId
      let valueBody ← mkCode decl.value
      let value :=
        if isEffectResultType decl.type then
          JsExpr.arrowEffectful paramNames valueBody
        else
          JsExpr.arrow paramNames valueBody
      modifyLCtx fun _ => oldLCtx
      let funStmt := JsStmt.const (← getVarName decl.fvarId) value
      let rest ← mkCode k
      return optimizeStmts <| #[funStmt] ++ rest
    | .oset f i y k _ =>
      let stmt := JsStmt.assign (JsExpr.prop (JsExpr.ident (← getVarName f)) s!"_{i+1}") (← mkArgExpr y)
      return optimizeStmts <| #[stmt] ++ (← mkCode k)
    | .uset f i y k _ =>
      let stmt := JsStmt.assign (JsExpr.prop (JsExpr.ident (← getVarName f)) s!"_{i+1}") (JsExpr.ident (← getVarName y))
      return optimizeStmts <| #[stmt] ++ (← mkCode k)
    | .sset f i offset y _ k _ =>
      let stmt := JsStmt.assign (JsExpr.prop (JsExpr.ident (← getVarName f)) s!"_{i + offset + 1}") (JsExpr.ident (← getVarName y))
      return optimizeStmts <| #[stmt] ++ (← mkCode k)
    | .setTag fvarId cidx k _ =>
      let stmt := JsStmt.assign (JsExpr.prop (JsExpr.ident (← getVarName fvarId)) "tag") (JsExpr.litNum (toString cidx))
      return optimizeStmts <| #[stmt] ++ (← mkCode k)
    | .inc _ _ _ _ k _ | .dec _ _ _ _ k _ | .del _ k _ =>
      mkCode k
    | .unreach _ =>
      return #[JsStmt.throw (JsExpr.litStr "unreachable")]

  partial def mkCases (c : Cases .impure) : EmitM .impure (Array JsStmt) := do
    let discr := JsExpr.ident (← getVarName c.discr)
    let knownBool? := (← get).knownBools.get? c.discr
    let discrType ← liftM <| LCNF.getType c.discr
    let isBool := c.typeName == ``Bool || c.alts.any fun alt => match alt with
      | .ctorAlt i .. => i.name == ``Bool.true || i.name == ``Bool.false
      | _ => false
    let discrTag :=
      if isScalarType discrType then
        discr
      else
        JsExpr.prop discr "tag"
    if let some b := knownBool? then
      for alt in c.alts do
        match alt with
        | .ctorAlt i k _ =>
          if (i.name == ``Bool.true && b) || (i.name == ``Bool.false && !b) then
            return optimizeStmts <| mkBlock (← mkCode k)
        | .default k =>
          return optimizeStmts <| mkBlock (← mkCode k)
        | _ => pure ()
      return #[]
    else if isBool then
      let mut currentElse : Array JsStmt := #[]
      for i in [:c.alts.size] do
        let alt := c.alts[c.alts.size - 1 - i]!
        match alt with
        | .ctorAlt info k _ =>
          let cond :=
            if info.name == ``Bool.true then discr
            else JsExpr.unary "!" discr
          currentElse := mkIfChain cond (mkBlock (← mkCode k)) currentElse
        | .alt _ params k _ =>
          let oldLCtx ← getLCtx
          for p in params do
            modifyLCtx fun lctx => lctx.addParam p
          let body ← mkCode k
          modifyLCtx fun _ => oldLCtx
          currentElse := mkBlock body
        | .default k =>
          currentElse := mkBlock (← mkCode k)
      return optimizeStmts currentElse
    else
      let mut currentElse : Array JsStmt := #[]
      for i in [:c.alts.size] do
        let alt := c.alts[c.alts.size - 1 - i]!
        match alt with
        | .ctorAlt info k _ =>
          let cond ←
            if isScalarType discrType then
              pure <| JsExpr.binary discrTag "===" (JsExpr.litNum (toString info.cidx))
            else do
              let tag ← toJsName info.name
              pure <| JsExpr.binary discrTag "===" (JsExpr.litStr tag)
          currentElse := mkIfChain cond (mkBlock (← mkCode k)) currentElse
        | .alt ctor params k _ =>
          let oldLCtx ← getLCtx
          for p in params do
            modifyLCtx fun lctx => lctx.addParam p
          let params := params.filter fun (p : Param .impure) => isRuntimeParamType p.type
          let mut body := #[]
          for i in [:params.size] do
            body := body.push <| JsStmt.const (← getVarName params[i]!.fvarId) (JsExpr.prop discr s!"_{i+1}")
          body := body ++ (← mkCode k)
          modifyLCtx fun _ => oldLCtx
          let tag ← toJsName ctor
          let cond := JsExpr.binary discrTag "===" (JsExpr.litStr tag)
          currentElse := mkIfChain cond (mkBlock body) currentElse
        | .default k =>
          currentElse := mkBlock (← mkCode k)
      return optimizeStmts currentElse
end

partial def hasTailRecursiveCall (name : Name) (code : Code .impure) : Bool :=
  match code with
  | .let decl k =>
    match k with
    | .return fvarId =>
      if fvarId == decl.fvarId then
        match decl.value with
        | .const n .. | .fap n .. => n == name
        | _ => false
      else false
    | _ => hasTailRecursiveCall name k
  | .jp decl k | .fun decl k _ => hasTailRecursiveCall name decl.value || hasTailRecursiveCall name k
  | .cases c => c.alts.any fun alt => hasTailRecursiveCall name alt.getCode
  | .oset _ _ _ k .. | .uset _ _ _ k .. | .sset _ _ _ _ _ k .. | .setTag _ _ k ..
  | .inc _ _ _ _ k .. | .dec _ _ _ _ k .. | .del _ k .. => hasTailRecursiveCall name k
  | .return .. | .jmp .. | .unreach .. => false

def mkDecl? (decl : Decl .impure) : EmitM .impure (Option JsDecl) := do
  match decl.value with
  | .code code =>
    let oldLCtx ← getLCtx
    let oldDecl := (← get).currentDecl?
    modify fun s => { s with currentDecl? := some decl, knownBools := {}, joinPoints := {} }
    for p in decl.params do
      modifyLCtx fun lctx => lctx.addParam p
    let exportName ← toJsName decl.name
    let isRecursive := hasTailRecursiveCall decl.name code
    let params := decl.params.filter fun p => isRuntimeParamType p.type
    let paramNames ← params.mapM fun p => do
      let name ← getVarName p.fvarId
      return s!"/* {p.type} */ {name}"
    let body ← mkCode code
    let body := if isRecursive then #[JsStmt.whileTrue body] else body
      let value :=
        if params.isEmpty && isClosedName decl.name then
          match stmtsToExpr? body with
          | some expr => expr
          | none => JsExpr.call (JsExpr.paren (JsExpr.arrow #[] body)) #[]
      else if isEffectResultType decl.type then
        JsExpr.arrowEffectful paramNames body
      else
        JsExpr.arrow paramNames body
    modify fun s => { s with currentDecl? := oldDecl }
    modifyLCtx fun _ => oldLCtx
    return some { exportName, value }
  | .extern _ =>
    -- Externs are handled by mkModule to generate imports/re-exports
    return none

partial def isAtomicExpr : JsExpr → Bool
  | JsExpr.ident .. | JsExpr.litNum .. | JsExpr.litBigNum .. | JsExpr.litStr .. | JsExpr.litBool .. | JsExpr.null => true
  | JsExpr.litArr elems => elems.all isAtomicExpr
  | JsExpr.prop obj _ => isAtomicExpr obj
  | JsExpr.index obj idx => isAtomicExpr obj && isAtomicExpr idx
  | _ => false

partial def isInlinePrimitiveExpr : JsExpr → Bool
  | JsExpr.litNum .. | JsExpr.litBigNum .. | JsExpr.litStr .. | JsExpr.litBool .. | JsExpr.null => true
  | JsExpr.litArr elems => elems.all isInlinePrimitiveExpr
  | _ => false

def substituteDecls (substs : List (String × JsExpr)) (decls : Array JsDecl) : Array JsDecl :=
  decls.map fun decl => { decl with value := optimizeExpr (substituteExpr substs decl.value) }

mutual
  partial def rewriteNullaryValueCallsExpr (names : List String) : JsExpr → JsExpr
    | .call (.ident name) #[] =>
      if containsName names name then .ident name else .call (.ident name) #[]
    | .call fn args =>
      .call (rewriteNullaryValueCallsExpr names fn) (args.map (rewriteNullaryValueCallsExpr names))
    | .object fields =>
      .object <| fields.map fun (name, value) => (name, rewriteNullaryValueCallsExpr names value)
    | .prop obj field =>
      .prop (rewriteNullaryValueCallsExpr names obj) field
    | .index obj idx =>
      .index (rewriteNullaryValueCallsExpr names obj) (rewriteNullaryValueCallsExpr names idx)
    | .unary op arg =>
      .unary op (rewriteNullaryValueCallsExpr names arg)
    | .binary lhs op rhs =>
      .binary (rewriteNullaryValueCallsExpr names lhs) op (rewriteNullaryValueCallsExpr names rhs)
    | .cond cond thenExpr elseExpr =>
      .cond (rewriteNullaryValueCallsExpr names cond) (rewriteNullaryValueCallsExpr names thenExpr)
        (rewriteNullaryValueCallsExpr names elseExpr)
    | .arrow params body =>
      .arrow params (rewriteNullaryValueCallsStmts names body)
    | .arrowEffectful params body =>
      .arrowEffectful params (rewriteNullaryValueCallsStmts names body)
    | .paren expr =>
      .paren (rewriteNullaryValueCallsExpr names expr)
    | expr => expr

  partial def rewriteNullaryValueCallsStmt (names : List String) : JsStmt → JsStmt
    | .const name value => .const name (rewriteNullaryValueCallsExpr names value)
    | .assign lhs rhs => .assign (rewriteNullaryValueCallsExpr names lhs) (rewriteNullaryValueCallsExpr names rhs)
    | .return value => .return (rewriteNullaryValueCallsExpr names value)
    | .continue => .continue
    | .throw value => .throw (rewriteNullaryValueCallsExpr names value)
    | .ifElse cond thenBranch elseBranch =>
      .ifElse (rewriteNullaryValueCallsExpr names cond) (rewriteNullaryValueCallsStmts names thenBranch)
        (rewriteNullaryValueCallsStmts names elseBranch)
    | .whileTrue body => .whileTrue (rewriteNullaryValueCallsStmts names body)
    | .block body => .block (rewriteNullaryValueCallsStmts names body)
    | .new name args => .new name (args.map (rewriteNullaryValueCallsExpr names))

  partial def rewriteNullaryValueCallsStmts (names : List String) (stmts : Array JsStmt) : Array JsStmt :=
    stmts.map (rewriteNullaryValueCallsStmt names)
end

def rewriteNullaryValueCallsDecls (names : List String) (decls : Array JsDecl) : Array JsDecl :=
  decls.map fun decl => { decl with value := optimizeExpr (rewriteNullaryValueCallsExpr names decl.value) }

def foldNullaryWrapperDecls (decls : Array JsDecl) : Array JsDecl := Id.run do
  let mut wrappers : List String := []
  let mut wrapperTargets : List (String × String) := []
  let mut byName : Std.HashMap String JsExpr := {}
  let mut useCounts : Std.HashMap String Nat := {}
  for decl in decls do
    byName := byName.insert decl.exportName decl.value
  for decl in decls do
    for name in exprUseCounts decl.value do
      useCounts := useCounts.insert name (useCounts.getD name 0 + 1)
  let mut out := #[]
  for decl in decls do
    let mut decl := decl
    match decl.value with
    | .arrow #[] #[.return (.ident target)] =>
      if let some value := byName.get? target then
        wrappers := decl.exportName :: wrappers
        wrapperTargets := (decl.exportName, target) :: wrapperTargets
        decl := { decl with value }
    | _ => pure ()
    out := out.push decl
  let decls := out
  let decls := rewriteNullaryValueCallsDecls wrappers decls
  decls.filter fun decl =>
    !(isClosedJsName decl.exportName && wrapperTargets.any fun (_, target) =>
      target == decl.exportName && useCounts.getD target 0 == 1)

partial def optimizeDecls (decls : Array JsDecl) : Array JsDecl :=
  let decls := foldNullaryWrapperDecls decls
  let decls := decls.map fun decl => { decl with value := optimizeExpr decl.value }
  let (_, _, acc) :=
    decls.reverse.foldl
      (init := (([] : List (String × JsExpr)), ([] : List String), (#[] : Array JsDecl)))
      fun (substs, used, acc) decl =>
        let value := optimizeExpr (substituteExpr substs decl.value)
        let useCount := countName used decl.exportName
        let used := eraseAllName used decl.exportName
        let inlineAlways :=
          isClosedJsName decl.exportName && isInlinePrimitiveExpr value
        let inlineIfCheap :=
          isClosedJsName decl.exportName && isPureExpr value && (isInlineAliasExpr value || useCount == 1)
        if inlineAlways || inlineIfCheap then
          let substs := (decl.exportName, value) :: substs
          let acc := substituteDecls [(decl.exportName, value)] acc
          (substs, exprUseCounts value ++ used, acc)
        else
          (substs, exprUseCounts value ++ used, Array.push acc { exportName := decl.exportName, value })
  acc.reverse

def mkModule (decls : Array (Decl .impure)) : EmitM .impure JsModule := do
  let mut out := #[]
  let mut seen : Std.HashSet String := {}
  for decl in decls do
    let jsName ← toJsName decl.name
    if seen.contains jsName then
      continue
    if let some jsDecl ← mkDecl? decl then
      seen := seen.insert jsName
      out := out.push jsDecl
    else if let .extern _ := decl.value then
      let jsNameBase := stripRedArgSuffix jsName
      let hasJsExternInlined := (getJsExternInlined? (← getEnv) decl.name).isSome
      unless isInlinedPrimitive jsNameBase || hasJsExternInlined do
        let mainModName := (← get).mainModName
        recordExternUse mainModName jsNameBase
        modify fun s => { s with localExterns := s.localExterns.insert jsNameBase }
        seen := seen.insert jsName

  let s ← get

  let mut imports := #[]
  for (nMod, names) in s.usedDecls.toArray.qsort (·.1.toString < ·.1.toString) do
    let sMod := nMod.toString
    let isStd := sMod == "Std" || sMod.startsWith "Std." ||
                 sMod == "Lean" || sMod.startsWith "Lean." ||
                 sMod == "Lake" || sMod.startsWith "Lake."
    if isStd then continue

    let mut importNames := #[]
    for n in names.toArray.qsort (·.toString < ·.toString) do
      importNames := importNames.push (← toJsName n)
    imports := imports.push (getRelativePath s.mainModName nMod, importNames)

  let resolveExternImportPath (modName : Name) : EmitM .impure (Option String) := do
    let srcSearchPath ← liftM (m := IO) Lean.getSrcSearchPath
    let path? ← liftM (m := IO) <| srcSearchPath.findModuleWithExt "external.js" modName
    match path? with
    | some path => return some (System.FilePath.normalize path).toString
    | none =>
      return (← liftM (m := IO) <| srcSearchPath.findModuleWithExt "js" modName).map (fun path => (System.FilePath.normalize path).toString)

  let mut externImports := #[]
  let mut unresolvedExterns := #[]
  for (modName, names) in s.usedExterns.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    let names := names.toArray.qsort (· < ·)
    if let some path ← resolveExternImportPath modName then
      externImports := externImports.push (path, names)
    else
      unresolvedExterns := unresolvedExterns ++ names

  let opts ← getOptions
  let s_path := javascript.extern_path.get opts
  if !unresolvedExterns.isEmpty then
    if s_path.isEmpty then
      throwError "missing JS extern import path for: {Format.joinSep (unresolvedExterns.toList.map format) ", "}"
    externImports := externImports.push (s_path, unresolvedExterns.qsort (· < ·))

  return {
    modName := s.mainModName,
    decls := optimizeDecls out,
    imports,
    externImports,
    externExports := s.localExterns.toArray.qsort (· < ·)
  }

def isCallLikeExpr : JsExpr → Bool
  | JsExpr.call .. | JsExpr.paren .. => true
  | _ => false

def binaryPrecedence (op : String) : Nat :=
  if op == "*" || op == "/" || op == "%" then 70
  else if op == "+" || op == "-" then 60
  else if op == "<" || op == "<=" || op == ">" || op == ">=" then 50
  else if op == "===" || op == "!==" then 45
  else if op == "&&" then 40
  else if op == "||" then 35
  else 30

def exprPrecedence : JsExpr → Nat
  | JsExpr.arrow .. | JsExpr.arrowEffectful .. => 10
  | JsExpr.cond .. => 20
  | JsExpr.binary _ op _ => binaryPrecedence op
  | JsExpr.unary .. => 80
  | JsExpr.call .. | JsExpr.prop .. | JsExpr.index .. | JsExpr.new .. => 90
  | JsExpr.paren .. => 100
  | _ => 100

partial def stripBlockWrappers (body : Array JsStmt) : Array JsStmt :=
  match body with
  | #[JsStmt.block inner] => stripBlockWrappers inner
  | _ => body

mutual

  partial def isNonCallableValueExpr : JsExpr → Bool
    | JsExpr.litNum .. | JsExpr.litBigNum .. | JsExpr.litStr .. | JsExpr.litBool .. | JsExpr.null => true
    | JsExpr.litArr .. | JsExpr.object .. => true
    | JsExpr.paren expr => isNonCallableValueExpr expr
    | _ => false

  partial def renderExprPrec (ctxPrec : Nat) : JsExpr → String
    | JsExpr.ident name => name
    | JsExpr.litNum value => value
    | JsExpr.litBigNum value => value
    | JsExpr.litStr value => mkJsString value
    | JsExpr.litBool true => "true"
    | JsExpr.litBool false => "false"
    | JsExpr.null => "null"
    | JsExpr.litArr elems =>
      "[" ++ ", ".intercalate (elems.map (renderExprPrec 0)).toList ++ "]"
    | JsExpr.object fields =>
      let fields := fields.map fun (name, value) => s!"{name}: {renderExprPrec 0 value}"
      "{ " ++ ", ".intercalate fields.toList ++ " }"
    | JsExpr.call fn args =>
      if args.isEmpty && isNonCallableValueExpr fn then
        renderExprPrec ctxPrec fn
      else
        let prec := exprPrecedence (.call fn args)
        let fn := renderExprPrec prec fn
        let args := ", ".intercalate <| (args.map (renderExprPrec 0)).toList
        let out := fn ++ "(" ++ args ++ ")"
        if prec < ctxPrec then "(" ++ out ++ ")" else out
    | JsExpr.prop obj field =>
      let prec := exprPrecedence (.prop obj field)
      let obj := renderExprPrec prec obj
      let out := obj ++ "." ++ field
      if prec < ctxPrec then "(" ++ out ++ ")" else out
    | JsExpr.index obj idx =>
      let prec := exprPrecedence (.index obj idx)
      let obj := renderExprPrec prec obj
      let idx := renderExprPrec 0 idx
      let out := obj ++ "[" ++ idx ++ "]"
      if prec < ctxPrec then "(" ++ out ++ ")" else out
    | JsExpr.unary op arg =>
      let prec := exprPrecedence (.unary op arg)
      let arg :=
        match arg with
        | JsExpr.unary .. => renderExprPrec (prec + 1) arg
        | _ => renderExprPrec prec arg
      let out := op ++ arg
      if prec < ctxPrec then "(" ++ out ++ ")" else out
    | JsExpr.binary lhs op rhs =>
      let prec := binaryPrecedence op
      let lhs := renderExprPrec prec lhs
      let rhs := renderExprPrec (prec + 1) rhs
      let out := lhs ++ s!" {op} " ++ rhs
      if prec < ctxPrec then "(" ++ out ++ ")" else out
    | JsExpr.cond cond thenExpr elseExpr =>
      let prec := exprPrecedence (.cond cond thenExpr elseExpr)
      let cond := renderExprPrec prec cond
      let thenExpr := renderExprPrec 0 thenExpr
      let elseExpr := renderExprPrec 0 elseExpr
      let out := cond ++ s!" ? {thenExpr} : {elseExpr}"
      if prec < ctxPrec then "(" ++ out ++ ")" else out
    | JsExpr.new name args =>
      let out := "new " ++ name ++ "(" ++ ", ".intercalate (args.map (renderExprPrec 0)).toList ++ ")"
      if exprPrecedence (.new name args) < ctxPrec then "(" ++ out ++ ")" else out
    | JsExpr.arrow params body =>
      let body := stripBlockWrappers body
      let out :=
        if let some expr := stmtsToExpr? body then
          let expr := match expr with
            | JsExpr.object .. => "(" ++ renderExpr expr ++ ")"
            | _ => renderExpr expr
          "(" ++ ", ".intercalate params.toList ++ ") => " ++ expr
        else
          "(" ++ ", ".intercalate params.toList ++ ") => " ++ renderBlock 0 body
      if exprPrecedence (.arrow params body) < ctxPrec then "(" ++ out ++ ")" else out
    | JsExpr.arrowEffectful params body =>
      let body := stripBlockWrappers body
      let paramsStr := ", ".intercalate params.toList
      let paramsStr := if paramsStr.isEmpty then "/* world */" else paramsStr ++ ", /* world */"
      let out :=
        if let some expr := stmtsToExpr? body then
          let expr := match expr with
            | JsExpr.object .. => "(" ++ renderExpr expr ++ ")"
            | _ => renderExpr expr
          "(" ++ paramsStr ++ ") => " ++ expr
        else
          "(" ++ paramsStr ++ ") => " ++ renderBlock 0 body
      if exprPrecedence (.arrowEffectful #[] body) < ctxPrec then "(" ++ out ++ ")" else out
    | JsExpr.paren expr =>
      "(" ++ renderExprPrec 0 expr ++ ")"

  partial def renderExpr : JsExpr → String :=
    renderExprPrec 0

  partial def renderIndent (n : Nat) : String :=
    String.join <| (List.replicate n "  ")

  partial def renderBlock (indent : Nat) (body : Array JsStmt) : String :=
    let body := stripBlockWrappers body
    "{\n" ++ renderStmts (indent + 1) body ++ renderIndent indent ++ "}"

  partial def renderStmt (indent : Nat) : JsStmt → String
    | JsStmt.const name value =>
      renderIndent indent ++ s!"const {name} = {renderExpr value};\n"
    | JsStmt.assign lhs rhs =>
      renderIndent indent ++ s!"{renderExpr lhs} = {renderExpr rhs};\n"
    | JsStmt.return value =>
      renderIndent indent ++ s!"return {renderExpr value};\n"
    | JsStmt.continue =>
      renderIndent indent ++ "continue;\n"
    | JsStmt.throw value =>
      renderIndent indent ++ s!"throw {renderExpr value};\n"
    | JsStmt.ifElse cond thenBranch elseBranch =>
      let head := renderIndent indent ++ s!"if ({renderExpr cond}) " ++ renderBlock indent thenBranch
      if elseBranch.isEmpty then
        head ++ "\n"
      else if elseBranch.size == 1 then
        match elseBranch[0]! with
        | JsStmt.ifElse cond thenBranch elseBranch =>
          head ++ " else " ++ (renderStmt indent (JsStmt.ifElse cond thenBranch elseBranch)).trimAsciiStart.toString
        | _ =>
          head ++ " else " ++ renderBlock indent elseBranch ++ "\n"
      else
        head ++ " else " ++ renderBlock indent elseBranch ++ "\n"
    | JsStmt.whileTrue body =>
      renderIndent indent ++ "while (true) " ++ renderBlock indent body ++ "\n"
    | JsStmt.block body =>
      renderIndent indent ++ renderBlock indent body ++ "\n"
    | JsStmt.new name args =>
      renderIndent indent ++ s!"new {name}(" ++ ", ".intercalate (args.map (renderExprPrec 0)).toList ++ ");\n"

  partial def renderStmts (indent : Nat) (stmts : Array JsStmt) : String :=
    String.join <| (stmts.map (renderStmt indent)).toList
end

def renderDecl (decl : JsDecl) : String :=
  s!"export const {decl.exportName} = {renderExpr decl.value};\n"

def renderModule (m : JsModule) : String := Id.run do
  let hasContent := !m.imports.isEmpty || !m.externImports.isEmpty || !m.decls.isEmpty || m.modName == `Main
  -- Return empty string for modules with no effective content (e.g. pure re-export umbrella modules)
  if !hasContent then return ""
  let mut res := "// Generated by Lean ES6 emitter\n"
  for (path, names) in m.imports do
    let namesStr := ", ".intercalate (names.toList.map (fun n => s!"{n} as {n}"))
    res := res ++ "import { " ++ namesStr ++ " } from \"" ++ path ++ "\";\n"
  for (path, names) in m.externImports do
    let namesStr := ", ".intercalate names.toList
    res := res ++ "import { " ++ namesStr ++ " } from \"" ++ path ++ "\";\n"
  if !m.externExports.isEmpty then
    let names := ", ".intercalate m.externExports.toList
    res := res ++ "export { " ++ names ++ " };\n"
  for decl in m.decls do
    res := res ++ renderDecl decl
  if m.decls.any (fun d => d.exportName == "main") then
    res := res ++ "\nmain();\n"
  return res

end EmitEs6

public def emitEs6' (modName : Name) (decls : Array (Decl .impure)) : CompilerM String := do
  let mut localImpureDecls : Std.HashMap Name (Decl .impure) := {}
  for decl in decls do
    localImpureDecls := localImpureDecls.insert decl.name decl
  let (module, _) ← (EmitEs6.mkModule decls).run { mainModName := modName, localImpureDecls }
  return EmitEs6.renderModule module

public def emitEs6 (modName : Name) : CoreM String := do
  let declNames ← getLocalImpureDecls
  let (localDecls, _) ← collectUsedDecls declNames
  (emitEs6' modName localDecls).run (phase := .impure)

end Lean.Compiler.LCNF
