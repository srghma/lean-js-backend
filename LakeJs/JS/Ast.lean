/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license with some modifications.
-/
module Lean.JS

/-!
# JavaScript AST

This module defines the Abstract Syntax Tree (AST) for the JavaScript language,
translated from the `language-javascript` Haskell library.
-/

inductive JSAst where
  | program (stmts : Array JSStatement)
  | module_ (items : Array JSModuleItem)
  | statement (s : JSStatement)
  | expression (e : JSExpression)
  | literal (e : JSExpression)
  deriving Repr, BEq

inductive JSModuleItem where
  | importDeclaration (decl : JSImportDeclaration)
  | exportDeclaration (decl : JSExportDeclaration)
  | statement (s : JSStatement)
  deriving Repr, BEq

inductive JSImportDeclaration where
  | declaration (clause : JSImportClause) (from : JSFromClause) (semi : JSSemi)
  | bare (moduleName : String) (semi : JSSemi)
  deriving Repr, BEq

inductive JSImportClause where
  | default (ident : JSIdent)
  | nameSpace (ns : JSImportNameSpace)
  | named (named : JSImportsNamed)
  | defaultNameSpace (default : JSIdent) (ns : JSImportNameSpace)
  | defaultNamed (default : JSIdent) (named : JSImportsNamed)
  deriving Repr, BEq

inductive JSFromClause where
  | from (moduleName : String)
  deriving Repr, BEq

inductive JSImportNameSpace where
  | nameSpace (ident : JSIdent)
  deriving Repr, BEq

inductive JSImportsNamed where
  | named (specifiers : Array JSImportSpecifier)
  deriving Repr, BEq

inductive JSImportSpecifier where
  | specifier (ident : JSIdent)
  | specifierAs (ident : JSIdent) (as : JSIdent)
  deriving Repr, BEq

inductive JSExportDeclaration where
  | from (clause : JSExportClause) (from : JSFromClause) (semi : JSSemi)
  | locals (clause : JSExportClause) (semi : JSSemi)
  | export (stmt : JSStatement) (semi : JSSemi)
  deriving Repr, BEq

inductive JSExportClause where
  | clause (specifiers : Array JSExportSpecifier)
  deriving Repr, BEq

inductive JSExportSpecifier where
  | specifier (ident : JSIdent)
  | specifierAs (ident1 : JSIdent) (ident2 : JSIdent)
  deriving Repr, BEq

inductive JSStatement where
  | block (stmts : Array JSStatement) (semi : JSSemi)
  | break (ident : JSIdent) (semi : JSSemi)
  | let (decl : Array JSExpression) (semi : JSSemi)
  | class (name : JSIdent) (heritage : JSClassHeritage) (body : Array JSClassElement) (semi : JSSemi)
  | constant (decl : Array JSExpression) (semi : JSSemi)
  | continue (ident : JSIdent) (semi : JSSemi)
  | doWhile (stmt : JSStatement) (expr : JSExpression) (semi : JSSemi)
  | for (expr1 : Array JSExpression) (expr2 : Array JSExpression) (expr3 : Array JSExpression) (stmt : JSStatement)
  | forIn (expr1 : Array JSExpression) (op : JSBinOp) (expr2 : JSExpression) (stmt : JSStatement)
  | forVar (varDecl : Array JSExpression) (expr2 : Array JSExpression) (expr3 : Array JSExpression) (stmt : JSStatement)
  | forVarIn (varDecl : Array JSExpression) (expr1 : JSExpression) (op : JSBinOp) (expr2 : JSExpression) (stmt : JSStatement)
  | forLet (varDecl : Array JSExpression) (expr2 : Array JSExpression) (expr3 : Array JSExpression) (stmt : JSStatement)
  | forLetIn (varDecl : Array JSExpression) (expr1 : JSExpression) (op : JSBinOp) (expr2 : JSExpression) (stmt : JSStatement)
  | forLetOf (varDecl : Array JSExpression) (expr1 : JSExpression) (op : JSBinOp) (expr2 : JSExpression) (stmt : JSStatement)
  | forConst (varDecl : Array JSExpression) (expr2 : Array JSExpression) (expr3 : Array JSExpression) (stmt : JSStatement)
  | forConstIn (varDecl : Array JSExpression) (expr1 : JSExpression) (op : JSBinOp) (expr2 : JSExpression) (stmt : JSStatement)
  | forConstOf (varDecl : Array JSExpression) (expr1 : JSExpression) (op : JSBinOp) (expr2 : JSExpression) (stmt : JSStatement)
  | forOf (expr1 : Array JSExpression) (op : JSBinOp) (expr2 : JSExpression) (stmt : JSStatement)
  | forVarOf (varDecl : Array JSExpression) (expr1 : JSExpression) (op : JSBinOp) (expr2 : JSExpression) (stmt : JSStatement)
  | asyncFunction (name : JSIdent) (params : Array JSExpression) (block : JSBlock) (semi : JSSemi)
  | function (name : JSIdent) (params : Array JSExpression) (block : JSBlock) (semi : JSSemi)
  | generator (name : JSIdent) (params : Array JSExpression) (block : JSBlock) (semi : JSSemi)
  | if (expr : JSExpression) (stmt : JSStatement)
  | ifElse (expr : JSExpression) (stmt1 : JSStatement) (stmt2 : JSStatement)
  | labelled (ident : JSIdent) (stmt : JSStatement)
  | emptyStatement
  | expressionStatement (expr : JSExpression) (semi : JSSemi)
  | assignStatement (lhs : JSExpression) (op : JSAssignOp) (rhs : JSExpression) (semi : JSSemi)
  | methodCall (expr : JSExpression) (args : Array JSExpression) (semi : JSSemi)
  | return (expr? : Option JSExpression) (semi : JSSemi)
  | switch (expr : JSExpression) (parts : Array JSSwitchParts) (semi : JSSemi)
  | throw (expr : JSExpression) (semi : JSSemi)
  | try (block : JSBlock) (catches : Array JSTryCatch) (finally : JSTryFinally)
  | variable (decl : Array JSExpression) (semi : JSSemi)
  | while (expr : JSExpression) (stmt : JSStatement)
  | with (expr : JSExpression) (stmt : JSStatement) (semi : JSSemi)
  deriving Repr, BEq

inductive JSExpression where
  | identifier (name : String)
  | decimal (value : String)
  | literal (value : String)
  | hexInteger (value : String)
  | octal (value : String)
  | stringLiteral (value : String)
  | regEx (value : String)
  | arrayLiteral (elems : Array JSArrayElement)
  | assignExpression (lhs : JSExpression) (op : JSAssignOp) (rhs : JSExpression)
  | awaitExpression (expr : JSExpression)
  | callExpression (expr : JSExpression) (args : Array JSExpression)
  | callExpressionDot (expr : JSExpression) (expr2 : JSExpression)
  | callExpressionSquare (expr : JSExpression) (index : JSExpression)
  | classExpression (name : JSIdent) (heritage : JSClassHeritage) (body : Array JSClassElement)
  | commaExpression (lhs : JSExpression) (rhs : JSExpression)
  | expressionBinary (lhs : JSExpression) (op : JSBinOp) (rhs : JSExpression)
  | expressionParen (expr : JSExpression)
  | expressionPostfix (expr : JSExpression) (op : JSUnaryOp)
  | expressionTernary (cond : JSExpression) (trueVal : JSExpression) (falseVal : JSExpression)
  | arrowExpression (params : JSArrowParameterList) (body : JSStatement)
  | functionExpression (name : JSIdent) (params : Array JSExpression) (block : JSBlock)
  | generatorExpression (name : JSIdent) (params : Array JSExpression) (block : JSBlock)
  | memberDot (obj : JSExpression) (prop : JSExpression)
  | memberExpression (expr : JSExpression) (args : Array JSExpression)
  | memberNew (expr : JSExpression) (args : Array JSExpression)
  | memberSquare (obj : JSExpression) (index : JSExpression)
  | newExpression (expr : JSExpression)
  | objectLiteral (props : Array JSObjectProperty)
  | spreadExpression (expr : JSExpression)
  | templateLiteral (tag? : Option JSExpression) (head : String) (parts : Array JSTemplatePart)
  | unaryExpression (op : JSUnaryOp) (expr : JSExpression)
  | varInitExpression (ident : JSExpression) (init : JSVarInitializer)
  | yieldExpression (expr? : Option JSExpression)
  | yieldFromExpression (expr : JSExpression)
  deriving Repr, BEq

inductive JSArrowParameterList where
  | unparenthesized (ident : JSIdent)
  | parenthesized (params : Array JSExpression)
  deriving Repr, BEq

inductive JSBinOp where
  | and | bitAnd | bitOr | bitXor | divide | eq | ge | gt | in | instanceOf | le | lsh | lt | minus | mod | neq | of | or | plus | rsh | strictEq | strictNeq | times | ursh
  deriving Repr, BEq

inductive JSUnaryOp where
  | decr | delete | incr | minus | not | plus | tilde | typeof | void
  deriving Repr, BEq

inductive JSSemi where
  | semi
  | auto
  deriving Repr, BEq

inductive JSAssignOp where
  | assign | timesAssign | divideAssign | modAssign | plusAssign | minusAssign | lshAssign | rshAssign | urshAssign | bwAndAssign | bwXorAssign | bwOrAssign
  deriving Repr, BEq

inductive JSTryCatch where
  | catch (ident : JSExpression) (block : JSBlock)
  | catchIf (ident : JSExpression) (expr : JSExpression) (block : JSBlock)
  deriving Repr, BEq

inductive JSTryFinally where
  | finally (block : JSBlock)
  | noFinally
  deriving Repr, BEq

inductive JSBlock where
  | block (stmts : Array JSStatement)
  deriving Repr, BEq

inductive JSSwitchParts where
  | case (expr : JSExpression) (stmts : Array JSStatement)
  | default (stmts : Array JSStatement)
  deriving Repr, BEq

inductive JSVarInitializer where
  | init (expr : JSExpression)
  | none
  deriving Repr, BEq

inductive JSObjectProperty where
  | propValue (name : JSPropertyName) (value : Array JSExpression)
  | propIdentRef (name : String)
  | propMethod (method : JSMethodDefinition)
  deriving Repr, BEq

inductive JSMethodDefinition where
  | method (name : JSPropertyName) (params : Array JSExpression) (block : JSBlock)
  | generatorMethod (name : JSPropertyName) (params : Array JSExpression) (block : JSBlock)
  | accessorMethod (acc : JSAccessor) (name : JSPropertyName) (params : Array JSExpression) (block : JSBlock)
  deriving Repr, BEq

inductive JSPropertyName where
  | ident (name : String)
  | string (value : String)
  | number (value : String)
  | computed (expr : JSExpression)
  deriving Repr, BEq

inductive JSAccessor where
  | get
  | set
  deriving Repr, BEq

inductive JSIdent where
  | name (n : String)
  | none
  deriving Repr, BEq

inductive JSArrayElement where
  | element (expr : JSExpression)
  | comma
  deriving Repr, BEq

inductive JSTemplatePart where
  | part (expr : JSExpression) (suffix : String)
  deriving Repr, BEq

inductive JSClassHeritage where
  | extends (expr : JSExpression)
  | none
  deriving Repr, BEq

inductive JSClassElement where
  | instanceMethod (method : JSMethodDefinition)
  | staticMethod (method : JSMethodDefinition)
  | semi
  deriving Repr, BEq
