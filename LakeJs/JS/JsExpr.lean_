/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license with some modifications.
-/

/-!
# Minimal JavaScript Expression AST

This module defines a minimal AST for JavaScript expressions used in `js_extern_inlined` attributes.
-/

namespace Lean.JS

inductive JsExpr where
  | identifier (name : String)
  | arg (idx : Nat)
  | num (val : Nat)
  | numLit (val : String)
  | str (val : String)
  | call (fn : JsExpr) (args : Array JsExpr)
  | prop (obj : JsExpr) (name : String)
  | bracketAccess (obj : JsExpr) (idx : JsExpr)
  | binary (op : JsBinOp) (lhs : JsExpr) (rhs : JsExpr)
  | cond (cond : JsExpr) (thenExpr : JsExpr) (elseExpr : JsExpr)
  | new (name : String) (args? : Option (Array JsExpr))
  | arrayLiteral (elems : Array JsExpr)
  deriving Repr, BEq

inductive JsBinOp where
  | add | sub | mul | div | mod | pow | eq | le | lt | gt | bitAnd | rightShift
  deriving Repr, BEq

/-- Environment extension to store inlined JS expressions for declarations. -/
structure JsExternInlinedExt : PersistentEnvExtension (Name × JsExpr) (Name × JsExpr) (List Name × NameMap JsExpr) where
  addEntry (asyncDecl := _) env decl val :=
    env.addEntry (asyncDecl := decl) decl val
  getState env := env.getState (asyncDecl := _)
  getParam env decl := env.getState (asyncDecl := _).getParam decl

def registerJsExternInlinedExt : IO Unit :=
  registerPersistentEnvExtension jsExternInlinedExt

end Lean.JS

namespace JS

open Lean.JS

def throwError (e : JsExpr) : JsExpr :=
  .call (.identifier "throwError") #[e]

def newError (msg : String) : JsExpr :=
  .call (.new "Error" none) #[.str msg]

def add a b := .binary .add a b
def sub a b := .binary .sub a b
def mul a b := .binary .mul a b
def div a b := .binary .div a b
def mod a b := .binary .mod a b
def pow a b := .binary .pow a b
def eq a b := .binary .eq a b
def le a b := .binary .le a b
def lt a b := .binary .lt a b
def gt a b := .binary .gt a b
def bitAnd a b := .binary .bitAnd a b
def rightShift a b := .binary .rightShift a b

def arg n := .arg n
def num n := .num n
def numLit s := .numLit s
def prop obj p := .prop obj p
def bracketAccess obj idx := .bracketAccess obj idx
def call fn args := .call fn args
def new name args? := .new name args?
def newArray elems := .call (.new "Array" none) #[elems]

end JS
