/-
# `LakeJs.Program` — waiting for the front end

This module printed the whole program one Lean declaration is: it read the declaration's
LCNF, followed every call with a body, and printed the resulting `Term`s.  It is kept
here verbatim, but **commented out**, because everything it is built on —
`LakeJs.Compile`, `LakeJs.Config`, `LakeJs.FromLcnf`, `LakeJs.ExternTable` — is currently
an empty file: the translation from `Lean.Compiler.LCNF` into `Term` has not been written
against the present shape of `Term` (curried functions, one block/label grammar for loops
and shared tails, no `JsOp`).  Nothing is deleted, so restoring it is a matter of restoring those
modules and adjusting the names this file uses.

import LakeJs.Compile

/-!
# `#lean_to_lean_term`: the whole program a single Lean function is

`LakeJs.Compile.compileModule` compiles a **module**: the declarations it declares, and
the declarations *of the same module* that they call.  Everything else is an import — a
name the emitted JavaScript calls but does not define — and a declaration of the module
that cannot be compiled (a `partial def` Lean derived, say) refuses the whole module.

That is the wrong unit when what is wanted is the program *one function* is.  This file
compiles the **closure of a declaration** instead:

* the roots are that one declaration;
* a declaration it reaches belongs to the program whenever the backend can read a body
  for it, whatever module that body came from — so a call of a helper in another module
  is followed, not left as an import;
* a call the runtime implements (`Array.push`, `String.append`, … — the catalogue of
  `LakeJs.Externs`) stops the walk: those are primitives, and the term calls them as
  `(extern lean_array_push)`;
* nothing else of the declaration's module is looked at, so a `deriving Repr` instance
  beside it — which is `partial`, and which `compileModule` therefore refuses — does not
  stop the function it is not called from.

`#lean_to_lean_term f` prints that program:

1. **the types** it mentions, each as the Lean type it comes from and the `LakeJs.Ty`
   the backend models it by — a recursive `inductive` is a `recTaggedUnion`, a
   `structure` a `record`, `Array α` an `array`, and so on;
2. **the declarations**, callees before callers, each as its name, its type and its term
   (`LakeJs.TermPretty`), as the translation produced it — before the optimiser runs.

A declaration whose result is a class instance is *unboxed* by the translation, here as
anywhere else: it is not one declaration building a record of fields but one declaration
per field, named `inst$field`, and those are what the program holds.

```
#lean_to_lean_term test
#lean_to_lean_term (config := faithful) test   -- `Nat` as a `BigInt`
```
-/

namespace LakeJs.Program

open Lean Lean.Compiler.LCNF
open LakeJs
open LakeJs.Compile
open LakeJs.FromLcnf (toTy)

/-- Does this declaration belong to the program, rather than being a name it calls?

    It does when the backend can read a Lean body for it: a declaration the runtime
    implements (the extern catalogue) and one whose LCNF body is `@[extern]` are
    primitives, and a name with no LCNF declaration at all — an `opaque`, a constructor,
    a type — is not a declaration of the program either. -/
def belongsToProgram (n : Name) : CoreM Bool := do
  if (LakeJs.ExternTable.externFor? n Ty.typeParam Ty.typeParam).isSome then
    return false
  match ← getBaseDecl? n with
  | some d =>
      match d.value with
      | .code _ => return true
      | .extern _ => return false
  | none => return false

/-- The program the closure of `root` is: `root` is what it exports, and everything it
    calls that has a body is part of it.

    No *module* is being compiled here, so the totality gate is given none: a declaration
    Lean itself marks `partial`, or that specialises one, is refused wherever it came
    from, and a library function that is proved total but implemented by an `unsafe`
    loop or by `@[extern]` is read as the primitive it is.  A declaration of the file the
    command is run in has no module of its own yet, which the gate reads as local, so a
    `partial def` written beside the root is still refused. -/
def declSpec (root : Name) : ProgramSpec where
  label := root
  roots := #[root]
  own := belongsToProgram
  totalityMods := #[]
  refusalHeader := s!"the program of `{root}` cannot be compiled to JavaScript"

/-! ## The types a program mentions -/

/-- Is this a type worth naming on its own?  A scalar and a type parameter are not: they
    are written the same wherever they appear. -/
def isCompoundTy : Ty → Bool
  | .prim _ => false
  | .typeParam => false
  | _ => true

/-- The name a private declaration was written under: `_private.SnapshotsMy.Html.0.Html`
    is `Html`. -/
def userName (n : Name) : Name := (privateToUserName? n).getD n

/-- The same expression as it is *read*: a private name is written as the name it was
    declared under, a universe level is dropped — neither says anything about the values
    the type describes — and the local standing for a type argument, which has only a
    generated name, is written `_`. -/
def forReading (e : Expr) : Expr :=
  e.replace fun s =>
    match s with
    | .const c _ => some (.const (userName c) [])
    | .fvar _ | .mvar _ => some (.const (Name.mkSimple "_") [])
    | _ => none

/-- Does this type end in a `Sort` once its parameters are taken?  That is what makes a
    `def` a name for a type — `abbrev HtmlM := StateM (Array Html) Unit` is one. -/
def resultIsSort : Expr → Bool
  | .forallE _ _ b _ => resultIsSort b
  | .sort _ => true
  | _ => false

/-- Does this expression *name* a type?  An `inductive` does, and so does a `def` whose
    result is a `Sort`; an arrow and a `let` do not, and neither does an ordinary
    function applied to its arguments. -/
def headNamesAType (env : Environment) (e : Expr) : Bool :=
  match e.getAppFn.constName? with
  | some c => match env.find? c with
    | some (.inductInfo _) => true
    | some (.defnInfo di) => resultIsSort di.type
    | _ => false
  | none => false

/-- Every type the backend models that appears anywhere inside `e`, as the Lean
    expression it is written as and the `Ty` it is modelled by.  A type is collected
    *and* its arguments are walked, so `Array Html` contributes both itself and `Html`. -/
partial def collectTys (env : Environment) (e : Expr) (acc : Array (Expr × Ty)) :
    Array (Expr × Ty) :=
  let acc :=
    if !e.hasLooseBVars && headNamesAType env e then
      match toTy env e with
      | .ok t => if isCompoundTy t then acc.push (e, t) else acc
      | .error _ => acc
    else acc
  match e with
  | .app f a => collectTys env a (collectTys env f acc)
  | .forallE _ d b _ => collectTys env b (collectTys env d acc)
  | .lam _ d b _ => collectTys env b (collectTys env d acc)
  | .letE _ t v b _ => collectTys env b (collectTys env v (collectTys env t acc))
  | .mdata _ b => collectTys env b acc
  | .proj _ _ b => collectTys env b acc
  | _ => acc

/-- The types of a program: what its declarations take, what they answer with, and
    everything inside those.  Each entry is the Lean type and the `Ty` the backend
    models it by, in the order they were met, without repeats.

    Both the type the declaration was *written* with and the one LCNF kept are walked:
    the first is where a name like `HtmlM` still stands, the second is where the type it
    abbreviates — the pair a `StateM` step answers with, the array it carries — shows
    up. -/
def programTys (env : Environment) (names : Array Name) : CoreM (Array (String × String)) := do
  let mut found : Array (Expr × Ty) := #[]
  for n in names do
    if let some ci := env.find? n then
      found := collectTys env ci.type found
    match ← getBaseDecl? n with
    | none => pure ()
    | some d =>
      found := collectTys env d.type found
      for p in d.params do
        found := collectTys env p.type found
  let mut out : Array (String × String) := #[]
  for (e, t) in found do
    let row := (toString (forReading e), Ty.pretty t)
    unless out.contains row do
      out := out.push row
  return out

/-! ## Rendering -/

/-- `s` padded with spaces to `n` characters. -/
private def padTo (n : Nat) (s : String) : String :=
  s ++ String.join (List.replicate (n - s.length) " ")

/-- The program of `root`, as text.  `res` is what the compiler made of its closure and
    `names` the declarations that closure held. -/
def render (cfg : LakeJs.Config.JsConfig) (root : Name) (tys : Array (String × String))
    (res : LakeJs.Compile.Result) : String :=
  let width := tys.foldl (init := 0) fun w (n, _) => max w n.length
  let typeLines :=
    if tys.isEmpty then "-- (it mentions no type of its own)\n"
    else String.join (tys.toList.map fun (n, t) => s!"{padTo width n} : {t}\n")
  let declBlocks := String.join (res.exprDecls.toList.map fun d =>
    let from_ := String.intercalate ", " (d.source.map fun n => s!"`{userName n}`")
    s!"-- from {from_}\n{d.name} : {d.ty}\n{d.term}\n\n")
  let failures :=
    if res.failures.isEmpty then ""
    else "\n-- what could not be translated\n"
      ++ String.join (res.failures.toList.map fun (n, why) => s!"-- `{n}`: {why}\n")
  s!"-- the program of `{userName root}`  [{cfg.describe}]\n\
     -- Its declarations are the ones it calls, and the ones they call, down to the\n\
     -- functions the runtime implements; the terms are as the translation produced\n\
     -- them, before the optimiser ran.\n\n\
     -- the types it mentions, and how the backend models them\n\
     {typeLines}\n\
     -- {res.compiled.size} declarations, callees before callers\n\n\
     {declBlocks}" ++ failures

/-- The whole program of `root`, as text: its types and the term of every declaration it
    needs. -/
def programOf (root : Name) (cfg : LakeJs.Config.JsConfig := .presetPBO) : CoreM String := do
  let env ← getEnv
  unless (env.find? root).isSome do
    throwError s!"there is no declaration called `{root}`"
  unless ← belongsToProgram root do
    throwError s!"`{root}` has no body the backend can read: it is a primitive of the \
      runtime, an `opaque`, or not a function at all"
  let res ← compileSpec (declSpec root) (preludeDepth := 1) (cfg := cfg)
  let tys ← programTys env res.compiled
  return render cfg root tys res

/-- The JavaScript of the program of `root`: the same closure, optimised and printed. -/
def javascriptOf (root : Name) (cfg : LakeJs.Config.JsConfig := .presetPBO) :
    CoreM String := do
  let res ← compileSpec (declSpec root) (preludeDepth := 1) (cfg := cfg)
  return res.js

/-! ## The commands -/

open Lean.Elab Lean.Elab.Command in
/-- The configuration a command was given, if it named one. -/
private def cfgOf (preset? : Option Syntax) : CommandElabM LakeJs.Config.JsConfig := do
  match preset? with
  | none => return .presetPBO
  | some s =>
    let name := s.getId.toString
    match LakeJs.Config.JsConfig.ofPresetName? name with
    | some c => return c
    | none => throwErrorAt s s!"unknown configuration `{name}`: use `pbo` or `faithful`"

open Lean.Elab Lean.Elab.Command in
/-- `#lean_to_lean_term f` prints the whole program of `f`: the types it mentions, and
    the term of `f` and of every declaration it needs, callees first. -/
elab "#lean_to_lean_term" cfg?:("(" &"config" ":=" ident ")")? f:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo f
  let cfg ← cfgOf (cfg?.map fun s => s.raw[3])
  logInfo (← liftCoreM <| programOf n cfg)

-- open Lean.Elab Lean.Elab.Command in
-- /-- `#lean_to_lean_js f` prints the JavaScript of the program of `f`: the same closure
--     of declarations, optimised and emitted. -/
-- elab "#lean_to_lean_js" cfg?:("(" &"config" ":=" ident ")")? f:ident : command => do
--   let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo f
--   let cfg ← cfgOf (cfg?.map fun s => s.raw[3])
--   logInfo (← liftCoreM <| javascriptOf n cfg)

end LakeJs.Program

-/
