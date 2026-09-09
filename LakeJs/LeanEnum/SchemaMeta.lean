module

public import LakeJs.LeanEnum.Basic
public meta import LakeJs.LeanEnum.Basic
public import Lean.Elab.Term
public meta import Lean.Elab.Term.TermElabM
public import Lean.Attributes
public import Lean.EnvExtension
public import Lean.Environment
public import Lean.Data.Name
public meta import Lean.Meta.Eval
public meta import Lean.Parser.Extra
public meta import Init.Data.ToString.Name

public section
@[expose] section

/-! # Metaprogramming / Elaborators for `LeanEnum` -/

open Lean in
/-- Inspects an inductive type in Lean's environment and generates a `LeanEnumSchema`. -/
public meta def extractEnumSchema (typeName : Name) : MetaM LeanEnumSchema := do
  let env ← getEnv
  let some (.inductInfo indVal) := env.find? typeName
    | throwError "'{typeName}' is not an inductive type"
  let typeNameStr := typeName.toString
  if h_type : typeNameStr != "" then
    let mut ctors : List LeanEnumCtorSchema := []
    for ctorName in indVal.ctors do
      let some (.ctorInfo ctorVal) := env.find? ctorName
        | throwError "Constructor '{ctorName}' not found"
      let shortName := match ctorName with
        | .str _ s => s
        | _ => ctorName.toString
      if h_name : shortName != "" then
        ctors := ctors ++ [{
          name      := shortName,
          h_name_ne := h_name,
          numFields := ctorVal.numFields
        }]
      else
        throwError "Constructor '{ctorName}' has an empty name"
    if h_ctors : ctors.length > 1 then
      -- The duplicate-name check uses the linear-time (hash-set) implementation and
      -- is turned into the `CtorNamesNodup` proof by `ctorNamesNodupFast_iff`.
      if h_nodup : ctorNamesNodupFast ctors = true then
        return {
          typeName            := typeNameStr,
          h_typeName_ne       := h_type,
          ctors               := ctors,
          h_ctors_more_than_1 := h_ctors,
          h_ctors_nodup       := (ctorNamesNodupFast_iff ctors).mp h_nodup
        }
      else
        throwError "Inductive type '{typeName}' has duplicate constructor names"
    else
      throwError "Inductive type '{typeName}' has {ctors.length} constructor(s), but LeanEnumSchema requires more than 1"
  else
    throwError "Type name is empty"

open Lean Meta Elab Term in
/--
`lean_schema% <type>` resolves an inductive type in the environment and expands
into a literal `LeanEnumSchema` at compile time.
-/
elab "lean_schema% " id:ident : term => do
  let typeName ← resolveGlobalConstNoOverload id
  let schema ← extractEnumSchema typeName
  let ctorSyntax ← schema.ctors.toArray.mapM fun (c : LeanEnumCtorSchema) =>
    `(LeanEnumCtorSchema.mk $(quote c.name) (by decide) $(quote c.numFields))
  let ctorsList ← `([ $[$ctorSyntax],* ])
  let term ← `(LeanEnumSchema.mk $(quote schema.typeName) (by decide) $ctorsList
    (by decide) (by decide))
  elabTerm term none
