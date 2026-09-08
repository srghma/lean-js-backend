module

public import Lean.Elab.Term
public meta import Lean.Elab.Term.TermElabM
public import Lean.Attributes
public import Lean.EnvExtension
public import Lean.Environment
public import Lean.Data.Name
public import Lean.Meta.Eval
public meta import Lean.Parser.Extra
public meta import Init.Data.ToString.Name

public section

/-! ### 1. Schema Definitions -/

structure LeanEnumCtorSchema where
  name      : String
  numFields : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

structure LeanEnumSchema where
  typeName : String
  ctors    : List LeanEnumCtorSchema
  deriving Repr, BEq, DecidableEq, Inhabited

namespace LeanEnumSchema

/-- Returns the number of fields for a constructor in the schema, defaulting to 0 if not found. -/
def ctorNumFields (schema : LeanEnumSchema) (ctorName : String) : Option Nat :=
  schema.ctors.find? (·.name == ctorName) >>= (some ·.numFields)

/-- Validates that a constructor name belongs to the schema. -/
def hasCtor (schema : LeanEnumSchema) (ctorName : String) : Prop :=
  schema.ctors.any (·.name == ctorName)

end LeanEnumSchema

/-! ### 4. Metaprogramming / Elaborator -/

open Lean in
/-- Inspects an inductive type in Lean's environment and generates a `LeanEnumSchema`. -/
public meta def extractEnumSchema (typeName : Name) : MetaM LeanEnumSchema := do
  let env ← getEnv
  let some (.inductInfo indVal) := env.find? typeName
    | throwError "'{typeName}' is not an inductive type"
  let mut ctors : List LeanEnumCtorSchema := []
  for ctorName in indVal.ctors do
    let some (.ctorInfo ctorVal) := env.find? ctorName
      | throwError "Constructor '{ctorName}' not found"
    let shortName := match ctorName with
      | .str _ s => s
      | _ => ctorName.toString
    -- `numFields` accounts for the constructor fields after stripping type params
    ctors := ctors ++ [{ name := shortName, numFields := ctorVal.numFields }]
  return { typeName := typeName.toString, ctors := ctors }

open Lean Meta Elab Term in
/--
`lean_schema% <type>` resolves an inductive type in the environment and expands
into a literal `LeanEnumSchema` at compile time.
-/
elab "lean_schema% " id:ident : term => do
  let typeName ← resolveGlobalConstNoOverload id
  let schema ← extractEnumSchema typeName
  let ctorSyntax ← schema.ctors.toArray.mapM fun (c : LeanEnumCtorSchema) =>
    `(LeanEnumCtorSchema.mk $(quote c.name) $(quote c.numFields))
  let ctorsList ← `([ $[$ctorSyntax],* ])
  let term ← `(LeanEnumSchema.mk $(quote schema.typeName) $ctorsList)
  elabTerm term none

-- 1. Create schemas at compile time
def listSchema   : LeanEnumSchema := lean_schema% List
def optionSchema : LeanEnumSchema := lean_schema% Option

-- def arraySchema   : LeanEnumSchema := lean_schema% Array -- DONT USE IT, for js we have special
-- #print arraySchema
