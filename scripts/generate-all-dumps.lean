import Lean
import Lean.Compiler.LCNF
import Lean.Compiler.ClosedTermCache
import LakeJs.Compile

open Lean Lean.Compiler.LCNF LakeJs LakeJs.Config

set_option linter.unusedVariables false

def moduleDefs (env : Environment) (mod : Name) : Array Name := Id.run do
  let some idx := env.getModuleIdx? mod | return #[]
  let mut ns := #[]
  for (n, cinfo) in env.constants.toList do
    if env.getModuleIdxFor? n == some idx then
      if let .defnInfo _ := cinfo then
        if (Lean.IR.findEnvDecl env n).isSome && !n.isInternal && !Lean.isPrivateName n then
          let s := n.toString
          if !s.contains "._sizeOf" && !s.contains ".sizeOf_spec" && !s.contains ".noConfusion" && !s.contains ".casesOn" && !s.contains ".recOn" && !s.contains ".ctorElim" && !s.contains ".ctorIdx" && !s.contains ".toCtorIdx" && !s.contains ".elim" && !s.contains ".match_" then
            ns := ns.push n
  return ns.qsort Name.lt

def moduleDeclsWithIR (env : Environment) (mod : Name) : Array Name := Id.run do
  let some idx := env.getModuleIdx? mod | return #[]
  let mut ns := #[]
  for (n, _) in env.constants.toList do
    if env.getModuleIdxFor? n == some idx then
      if let some (.fdecl ..) := Lean.IR.findEnvDecl env n then
        ns := ns.push n
  return ns.qsort Name.lt

def parseJsExportHeader (filePath : System.FilePath) : IO (Option (Array Name)) := do
  let content ← IO.FS.readFile filePath
  for line in content.splitOn "\n" do
    let trimmed := line.trimAscii.toString
    if trimmed.startsWith "--" && trimmed.contains "@js_export:" then
      let parts := trimmed.splitOn "@js_export:"
      if parts.length >= 2 then
        let rawNames := parts[1]!.splitOn "," |>.map (fun s => s.trimAscii.toString) |>.filter (!·.isEmpty)
        let names := rawNames.map (·.toName) |>.toArray
        return some names
  return none

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

def populateClosedCache (mod : Name) : CoreM Unit := do
  let env ← getEnv
  for (name, decl) in (monoExt.getState env).toArray do
    if name.toString.contains "_closed" then
      if let .code c := decl.value then
        let expr := c.toExpr
        modifyEnv fun env => cacheClosedTermName env expr name
  if let some modIdx := env.getModuleIdx? mod then
    for decl in monoExt.getModuleEntries env modIdx do
      if decl.name.toString.contains "_closed" then
        if let .code c := decl.value then
          let expr := c.toExpr
          modifyEnv fun env => cacheClosedTermName env expr decl.name

def getResultDecl (d : Decl) : CoreM (Array Decl) := do
  if isClosedTermName (← getEnv) d.name then
    let norm ← CompilerM.run (phase := .mono) <| normalizeFVarIds d
    return #[norm]
  else
    let pm ← getPassManager
    let mut afterSaveMono := false
    let mut postPasses : Array Pass := #[]
    for pass in pm.monoPassesNoLambda do
      if afterSaveMono then
        postPasses := postPasses.push pass
      else if pass.name == `saveMono then
        afterSaveMono := true

    let decls ← CompilerM.run (phase := .mono) do
      let mut decls := #[d]
      for pass in postPasses do
        decls ← withPhase pass.phase <| pass.run decls
      return decls

    decls.mapM fun decl => do
      CompilerM.run (phase := .mono) <| normalizeFVarIds decl

def makeDumpIr (env : Environment) (mod : Name) (names : Array Name) (oleanData : JsOleanData) : CoreM String := do
  let mut out := ""
  let depNames := (oleanData.decls.toList.map (·.1)).toArray.filter (!names.contains ·) |>.qsort Name.lt
  let allNames := names.map (true, ·) ++ depNames.map (false, ·)

  for (isRequested, n) in allNames do
    let emoji := if isRequested then "🎯" else "📦"
    out := out ++ s!"════ {emoji} {n}\n"
    let env ← getEnv
    if isRequested && (env.find? n).isNone then
      out := out ++ s!"❌ ⚠️ Name '{n}' is not present in environment!\n"
    match Lean.IR.findEnvDecl (← getEnv) n with
    | some d => out := out ++ s!"-- IR (what the backend reads)\n{format d}\n"
    | none   => out := out ++ "-- IR: not stored\n"
    out := out ++ "-- JsOleanData\n"
    let mut foundAny := false
    if let some declInfo := oleanData.decls[n]? then
      foundAny := true
      out := out ++ s!"decl.resultIsBool: {declInfo.resultIsBool}\n"
      out := out ++ s!"decl.externSym?: {repr declInfo.externSym?}\n"
      out := out ++ s!"decl.hashKeyType?: {repr declInfo.hashKeyType?}\n"
    if let some ctorInfo := oleanData.ctors[n]? then
      foundAny := true
      out := out ++ s!"ctor.induct: {ctorInfo.induct}\n"
      out := out ++ s!"ctor.cidx: {ctorInfo.cidx}\n"
      out := out ++ s!"ctor.numFields: {ctorInfo.numFields}\n"
    if let some inductInfo := oleanData.inducts[n]? then
      foundAny := true
      out := out ++ s!"induct.isEnum: {inductInfo.isEnum}\n"
      out := out ++ s!"induct.ctors: {repr inductInfo.ctors}\n"
    if n == OutputContent.entryName then
      foundAny := true
      out := out ++ s!"entry: {repr oleanData.entry}\n"
    if !foundAny then
      out := out ++ "not stored in JsOleanData\n"
    out := out ++ "\n"

  out := out ++ "════ JsOleanData summary\n"
  out := out ++ s!"modules: {repr oleanData.modules}\n"
  out := out ++ s!"entry: {repr oleanData.entry}\n"
  let declNames := (oleanData.decls.toList.map (·.1)).toArray.qsort Name.lt
  out := out ++ s!"decls ({declNames.size}): {repr declNames.toList}\n"
  let ctorNames := (oleanData.ctors.toList.map (·.1)).toArray.qsort Name.lt
  out := out ++ s!"ctors ({ctorNames.size}): {repr ctorNames.toList}\n"
  let inductNames := (oleanData.inducts.toList.map (·.1)).toArray.qsort Name.lt
  out := out ++ s!"inducts ({inductNames.size}): {repr inductNames.toList}\n"
  return out

def makeDumpLcnfSaveBase (names : Array Name) : CoreM String := do
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

def makeDumpLcnfSaveMono (names : Array Name) : CoreM String := do
  let mut todo := names.toList
  let mut seen : NameSet := {}
  let mut declMap : Std.HashMap Name Decl := {}

  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if let some d ← getMonoDecl? n then
      declMap := declMap.insert n d
      let used := getDeclUsed d
      for c in used do
        if !seen.contains c && (← getMonoDecl? c).isSome then
          todo := c :: todo

  let mut out := ""
  for n in names do
    out := out ++ s!"════ 🎯 {n}\n"
    match declMap[n]? with
    | some d => out := out ++ s!"{← ppDecl' d}\n\n"
    | none   => out := out ++ "-- LCNF (saveMono): not stored\n\n"

  let depNames := (seen.filter (!names.contains ·)).toArray.qsort Name.lt
  for dep in depNames do
    out := out ++ s!"════ 📦 {dep}\n"
    match declMap[dep]? with
    | some d => out := out ++ s!"{← ppDecl' d}\n\n"
    | none   => out := out ++ "-- LCNF (saveMono): not stored\n\n"

  return out

def makeDumpLcnfSaveResult (mod : Name) (names : Array Name) : CoreM String := do
  populateClosedCache mod
  let mut todo := names.toList
  let mut seen : NameSet := {}
  let mut declMap : Std.HashMap Name Decl := {}

  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if let some d ← getMonoDecl? n then
      let resDecls ← getResultDecl d
      for r in resDecls do
        declMap := declMap.insert r.name r
        if r.name != n then
          seen := seen.insert r.name
        let used := getDeclUsed r
        for c in used do
          if !seen.contains c && (← getMonoDecl? c).isSome then
            todo := c :: todo

  let mut out := ""
  for n in names do
    out := out ++ s!"════ 🎯 {n}\n"
    match declMap[n]? with
    | some d => out := out ++ s!"{← ppDecl' d}\n\n"
    | none   => out := out ++ "-- LCNF (result): not stored\n\n"

  let depNames := (seen.filter (!names.contains ·)).toArray.qsort Name.lt
  for dep in depNames do
    out := out ++ s!"════ 📦 {dep}\n"
    match declMap[dep]? with
    | some d => out := out ++ s!"{← ppDecl' d}\n\n"
    | none   => out := out ++ "-- LCNF (result): not stored\n\n"

  return out

def makeDumpArrayOwn (modName : String) (olean : JsOleanData) (roots : Array Name) : String :=
  let oleanHash := nativeHashContainers olean roots
  s!"=== {modName}\n" ++ (arrayOwnReport oleanHash roots (arrayMkIsFresh := true))

def makeDumpHashRepr (modName : String) (olean : JsOleanData) (roots : Array Name) : String :=
  s!"=== {modName}\n" ++ (hashReprReport olean roots)

def makeDumpIoAbi (modName : String) (olean : JsOleanData) : String :=
  match estAbiUnsupported? olean with
  | none => s!"{modName}: throws\n"
  | some why => s!"{modName}: objects — {why}\n"

def makeDumpOptionRepr (modName : String) (olean : JsOleanData) (content : OutputContent) (roots : Array Name) : String :=
  let frozen := (frozenParamDecls olean content).push OutputContent.entryName
  s!"=== {modName}\n" ++ (optionReprReport olean roots frozen)

def makeDumpParamPlan (olean : JsOleanData) (content : OutputContent) (names : Array Name) : String := Id.run do
  let (plans, vals, frozenSet) := paramArgValues olean (frozenParamDecls olean content)
  let mut out := ""
  for n in names do
    out := out ++ s!"════ {n}\n"
    if (olean.decl? n).isNone then
      out := out ++ s!"❌ ⚠️ Name '{n}' is not present in extracted declarations!\n"
    match olean.decl? n with
    | some d => out := out ++ s!"-- IR\n{format d}\n"
    | none => out := out ++ "-- IR: not in the extracted data\n"
    match plans[n]? with
    | some plan => out := out ++ s!"-- plan: {repr plan}\n"
    | none => out := out ++ "-- plan: every parameter kept\n"
    out := out ++ s!"-- frozen: {frozenSet.contains n}\n"
    out := out ++ s!"-- values: {(vals[n]?).getD #[] |>.toList.map fun
      | .bot => "bot"
      | .ctorVal c => s!"ctor {c}"
      | .numVal n => s!"num {n}"
      | .strVal s => s!"str {s}"
      | .top => "top"}\n"
    out := out ++ "-- callers:\n"
    for (m, info) in olean.decls.toList do
      if let .fdecl _ ps _ body _ := info.ir then
        let scan := scanParamCallsBody olean m (nullaryCtorVars olean {} body) (litVars {} body)
          (paramPositions ps) {} body
        for site in scan.sites do
          if site.callee == n then
            let srcs := site.args.toList.map fun
              | .bot => "erased"
              | .ctorVal c => s!"ctor {c}"
              | .numVal n => s!"num {n}"
              | .strVal s => s!"str {s}"
              | .param f i => s!"param {f} #{i}"
              | .top => "?"
            out := out ++ s!"   from {m}: {srcs}\n"
        if scan.frozen.contains n then
          out := out ++ s!"   frozen by {m}\n"
    out := out ++ "\n"
  return out

def makeDumpSplitPlan (olean : JsOleanData) (content : OutputContent) (names : Array Name) : String := Id.run do
  let frozen := frozenParamDecls olean content
  let plans := computeSplitPlans olean frozen
  let mut out := "════ split plans\n"
  for (n, plan) in plans.toList do
    out := out ++ s!"{n}: {repr plan}\n"
  let olean' := scalarReplace olean frozen
  let paramPlans := computeParamPlans olean' frozen
  for n in names do
    out := out ++ s!"════ {n} before\n"
    match olean.decl? n with
    | some d => out := out ++ toString (format d) ++ "\n"
    | none => out := out ++ "  (no compiled code)\n"
    out := out ++ s!"════ {n} after\n"
    match olean'.decl? n with
    | some d => out := out ++ toString (format d) ++ "\n"
    | none => out := out ++ "  (no compiled code)\n"
    match paramPlans[n]? with
    | some p => out := out ++ s!"════ {n} parameter plan: {repr p}\n"
    | none => out := out ++ s!"════ {n} parameter plan: (every parameter kept)\n"
  return out

def allTxtFilesExist (dir : System.FilePath) (baseName : String) : IO Bool := do
  let scripts := #[
    "dump-ir",
    "dump-lcnf-saveBase",
    "dump-lcnf-saveMono",
    "dump-lcnf-saveResult",
    "dump-array-own",
    "dump-hash-repr",
    "dump-io-abi",
    "dump-option-repr",
    "dump-param-plan",
    "dump-split-plan"
  ]
  for s in scripts do
    if !(← (dir / s!"{baseName}-{s}.txt").pathExists) then
      return false
  return true

def processModule (dir : System.FilePath) (baseName : String) (mod : Name) (names : Array Name) (content : OutputContent) (env : Environment) : IO Unit := do
  let oleanData := JsOleanData.ofEnvironment env #[mod] #[content]
  let roots := content.roots.push ioErrorToStringName

  -- 1. dump-ir
  let actIr := makeDumpIr env mod names oleanData
  let (sIr, _) ← actIr.toIO { fileName := "dump-ir", fileMap := default } { env }
  IO.FS.writeFile (dir / s!"{baseName}-dump-ir.txt") sIr

  -- 2. dump-lcnf-saveBase
  let actBase := makeDumpLcnfSaveBase names
  let (sBase, _) ← actBase.toIO { fileName := "dump-lcnf-saveBase", fileMap := default } { env }
  IO.FS.writeFile (dir / s!"{baseName}-dump-lcnf-saveBase.txt") sBase

  -- 3. dump-lcnf-saveMono
  let actMono := makeDumpLcnfSaveMono names
  let (sMono, _) ← actMono.toIO { fileName := "dump-lcnf-saveMono", fileMap := default } { env }
  IO.FS.writeFile (dir / s!"{baseName}-dump-lcnf-saveMono.txt") sMono

  -- 4. dump-lcnf-saveResult
  let actResult := makeDumpLcnfSaveResult mod names
  let (sResult, _) ← actResult.toIO { fileName := "dump-lcnf-saveResult", fileMap := default } { env }
  IO.FS.writeFile (dir / s!"{baseName}-dump-lcnf-saveResult.txt") sResult

  -- 5. dump-array-own
  let sArrayOwn := makeDumpArrayOwn baseName oleanData roots
  IO.FS.writeFile (dir / s!"{baseName}-dump-array-own.txt") sArrayOwn

  -- 6. dump-hash-repr
  let sHash := makeDumpHashRepr baseName oleanData roots
  IO.FS.writeFile (dir / s!"{baseName}-dump-hash-repr.txt") sHash

  -- 7. dump-io-abi
  let sAbi := makeDumpIoAbi baseName oleanData
  IO.FS.writeFile (dir / s!"{baseName}-dump-io-abi.txt") sAbi

  -- 8. dump-option-repr
  let sOpt := makeDumpOptionRepr baseName oleanData content roots
  IO.FS.writeFile (dir / s!"{baseName}-dump-option-repr.txt") sOpt

  -- 9. dump-param-plan
  let sParam := makeDumpParamPlan oleanData content names
  IO.FS.writeFile (dir / s!"{baseName}-dump-param-plan.txt") sParam

  -- 10. dump-split-plan
  let sSplit := makeDumpSplitPlan oleanData content names
  IO.FS.writeFile (dir / s!"{baseName}-dump-split-plan.txt") sSplit
  IO.println s!"  ✓ {baseName}"

def processOne (dir : System.FilePath) (baseName : String) (force : Bool := false) : IO Unit := do
  if !force && (← allTxtFilesExist dir baseName) then
    IO.println s!"  ↷ {baseName} (already generated, skipping)"
    return
  let p := dir / s!"{baseName}.lean"
  let mod := if dir == "LeanJsCliSnapshots" then (`LeanJsCliSnapshots).str baseName else (`LeanJsCliSnapshots2).str baseName
  let headerNames? ← parseJsExportHeader p
  try
    let env ← Lean.importModules #[{ module := mod }] {} (trustLevel := 1024)
    let names := match headerNames? with
      | some names => names
      | none => moduleDefs env mod
    let content : OutputContent :=
      if names == #[OutputContent.entryName] then .onlyEntry
      else if h : 0 < names.size then
        .onlyExports ⟨names[0], names.extract 1 names.size⟩
      else .onlyEntry
    processModule dir baseName mod names content env
  catch e =>
    let errMsg := s!"❌ ⚠️ Failed to load module {mod}: {e}\n"
    IO.FS.writeFile (dir / s!"{baseName}-dump-ir.txt") errMsg
    IO.FS.writeFile (dir / s!"{baseName}-dump-lcnf-saveBase.txt") errMsg
    IO.FS.writeFile (dir / s!"{baseName}-dump-lcnf-saveMono.txt") errMsg
    IO.FS.writeFile (dir / s!"{baseName}-dump-lcnf-saveResult.txt") errMsg
    IO.FS.writeFile (dir / s!"{baseName}-dump-array-own.txt") errMsg
    IO.FS.writeFile (dir / s!"{baseName}-dump-hash-repr.txt") errMsg
    IO.FS.writeFile (dir / s!"{baseName}-dump-io-abi.txt") errMsg
    IO.FS.writeFile (dir / s!"{baseName}-dump-option-repr.txt") errMsg
    IO.FS.writeFile (dir / s!"{baseName}-dump-param-plan.txt") errMsg
    IO.FS.writeFile (dir / s!"{baseName}-dump-split-plan.txt") errMsg
    IO.println s!"  ✗ {baseName}: {e}"

def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let force := args.contains "--force"
  let cleanArgs := args.filter (· != "--force")
  match cleanArgs with
  | [dirStr, baseName] =>
    processOne dirStr baseName force
  | _ =>
    -- Process LeanJsCliSnapshots
    let dir1 : System.FilePath := "LeanJsCliSnapshots"
    IO.println s!"Processing {dir1}..."
    let entries1 ← dir1.readDir
    for entry in entries1 do
      let p := entry.path
      if p.extension == some "lean" then
        let baseName := p.fileStem.getD ""
        processOne dir1 baseName force

    -- Process LeanJsCliSnapshots2
    let dir2 : System.FilePath := "LeanJsCliSnapshots2"
    IO.println s!"Processing {dir2}..."
    let entries2 ← dir2.readDir
    for entry in entries2 do
      let p := entry.path
      if p.extension == some "lean" then
        let baseName := p.fileStem.getD ""
        processOne dir2 baseName force

    IO.println "All dumps generated successfully!"
