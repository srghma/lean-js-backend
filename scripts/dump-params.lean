/-
Print the LCNF `saveBase` parameter types of one declaration, plus the arguments of each
call in its body.  Used to check which binders the backend drops.

    lake env lean --run scripts/dump-params.lean <Module.Name> <Decl.Name>
-/
import Lean
import Lean.Compiler.LCNF

open Lean Lean.Compiler.LCNF

partial def showCode (code : Code) : CoreM Unit := do
  match code with
  | .let d k =>
      match d.value with
      | .const n _ args =>
          IO.println s!"  call {n} args = {args.toList.map (fun a => match a with
            | .erased => "erased" | .type e => s!"type {e}" | .fvar f => s!"fvar {f.name}")}"
      | _ => pure ()
      showCode k
  | .fun d k | .jp d k => do showCode d.value; showCode k
  | .cases c => for a in c.alts do showCode a.getCode
  | _ => pure ()

def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let mod := args[0]!.toName
  let decl := args[1]!.toName
  let env ← Lean.importModules #[{ module := mod }] {} (trustLevel := 1024) (loadExts := true)
  let act : CoreM Unit := do
    let some d ← getDeclAt? decl .base | IO.println "no base decl"
    for p in d.params do
      IO.println s!"param {p.fvarId.name} : {p.type}"
    IO.println s!"type: {d.type}"
    match d.value with
    | .code c => showCode c
    | _ => pure ()
  let (_, _) ← act.toIO { fileName := "dump", fileMap := default } { env }
  return ()
