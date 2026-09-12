/-
Print, for a set of declarations and their transitive dependencies, what Lean stored for them
at the `saveBase` LCNF phase.

Usage:

    lake env lean --run scripts/dump-lcnf-saveBase.lean [--out <file>] <Module.Name> [<Decl.Name> ...]

With no declaration names, every declaration of the module that has an IR body is used as a root.
-/
import Lean
import Lean.Compiler.LCNF

open Lean Lean.Compiler.LCNF

/-- Declarations of `mod` that have an IR body, in name order. -/
def moduleDeclsWithIR (env : Environment) (mod : Name) : Array Name := Id.run do
  let some idx := env.getModuleIdx? mod | return #[]
  let mut ns := #[]
  for (n, _) in env.constants.toList do
    if env.getModuleIdxFor? n == some idx then
      if let some (.fdecl ..) := Lean.IR.findEnvDecl env n then
        ns := ns.push n
  return ns.qsort Name.lt

partial def collectUsedDecls (code : Code) (s : NameSet := {}) : NameSet :=
  match code with
  | .let decl k => collectUsedDecls k <| collectLetValue decl.value s
  | .jp decl k | .fun decl k => collectUsedDecls decl.value <| collectUsedDecls k s
  | .cases c =>
    c.alts.foldl (init := s) fun s alt =>
      match alt with
      | .default k => collectUsedDecls k s
      | .alt _ _ k => collectUsedDecls k s
  | _ => s
where
  collectLetValue (e : LetValue) (s : NameSet) : NameSet :=
    match e with
    | .const declName .. => s.insert declName
    | _ => s

def getDeclUsed (d : Decl) : NameSet :=
  match d.value with
  | .code c => collectUsedDecls c {}
  | _ => {}

def dumpString (env : Environment) (names : Array Name) : IO String := do
  let act : CoreM String := do
    let mut todo := names.toList
    let mut seen : NameSet := {}
    let mut declMap : Std.HashMap Name Decl := {}

    while !todo.isEmpty do
      let n := todo.head!
      todo := todo.tail!
      if seen.contains n then continue
      seen := seen.insert n
      if let some d ← getBaseDecl? n then
        declMap := declMap.insert n d
        let used := getDeclUsed d
        for c in used do
          if !seen.contains c && (← getBaseDecl? c).isSome then
            todo := c :: todo

    let mut out := ""
    for n in names do
      out := out ++ s!"════ 🎯 {n}\n"
      match declMap[n]? with
      | some d => out := out ++ s!"{← ppDecl' d}\n\n"
      | none   => out := out ++ "-- LCNF (saveBase): not stored\n\n"

    let depNames := (seen.filter (!names.contains ·)).toArray.qsort Name.lt
    for dep in depNames do
      out := out ++ s!"════ 📦 {dep}\n"
      match declMap[dep]? with
      | some d => out := out ++ s!"{← ppDecl' d}\n\n"
      | none   => out := out ++ "-- LCNF (saveBase): not stored\n\n"

    return out

  let (res, _) ← act.toIO { fileName := "dump-lcnf-saveBase", fileMap := default } { env }
  return res

def main (args : List String) : IO Unit := do
  let (outPath?, args) :=
    match args with
    | "--out" :: p :: rest => (some (System.FilePath.mk p), rest)
    | _ => (none, args)
  let some mod := args.head? | throw (IO.userError "usage: dump-lcnf-saveBase.lean [--out <file>] <Module> [<Decl> ...]")
  let mod := mod.toName
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := mod }] {} (trustLevel := 1024)
  let names :=
    if args.tail.isEmpty then moduleDeclsWithIR env mod
    else (args.tail.map String.toName).toArray
  let s ← dumpString env names
  if let some p := outPath? then
    IO.FS.writeFile p s
  else
    IO.print s
