/-
Print the type LCNF stored for every `let` of a declaration's `saveBase` body.

    lake env lean --run scripts/dump-let-types.lean <Module.Name> <Decl.Name>
-/
import Lean
import Lean.Compiler.LCNF

open Lean Lean.Compiler.LCNF

partial def walk (code : Code) : MetaM Unit := do
  match code with
  | .let decl k => do
      IO.println s!"let {decl.fvarId.name} : {← Meta.ppExpr decl.type}"
      walk k
  | .jp decl k | .fun decl k => do walk decl.value; walk k
  | .cases c => do
      IO.println s!"cases on {c.discr.name} : {← Meta.ppExpr c.resultType}"
      for alt in c.alts do
        match alt with
        | .default k => walk k
        | .alt _ ps k => do
            for p in ps do
              IO.println s!"  alt param {p.fvarId.name} : {← Meta.ppExpr p.type}"
            walk k
  | _ => pure ()

def main (args : List String) : IO Unit := do
  let [mod, decl] := args | throw (IO.userError "usage: <Module> <Decl>")
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := mod.toName }] {} (trustLevel := 1024)
  let act : MetaM Unit := do
    let some d ← getBaseDecl? decl.toName | IO.println "no body"
    for p in d.params do
      IO.println s!"param {p.fvarId.name} : {← Meta.ppExpr p.type}"
    match d.value with
    | .code c => walk c
    | _ => IO.println "extern"
  let _ ← (act.run' {}).toIO { fileName := "dump", fileMap := default } { env }
