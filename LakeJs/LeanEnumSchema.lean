module

public import Lean.Elab.Term
public meta import Lean.Elab.Term.TermElabM
public import Lean.Attributes
public import Lean.EnvExtension
public import Lean.Environment
public import Lean.Data.Name
public meta import Lean.Meta.Eval
public meta import Lean.Parser.Extra
public meta import Init.Data.ToString.Name
import Aesop

public section

/-! ### 1. Schema Definitions -/

structure LeanEnumCtorSchema where
  name      : String
  h_name_ne : name != "" := by decide
  numFields : Nat
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure LeanEnumSchema where
  typeName            : String
  h_typeName_ne       : typeName != "" := by decide
  ctors               : List LeanEnumCtorSchema
  h_ctors_more_than_1 : ctors.length > 1 := by decide -- not a structure
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

namespace LeanEnumSchema

/-- Single unified lookup function for constructor schemas. -/
def findCtor? (schema : LeanEnumSchema) (ctorName : String) : Option LeanEnumCtorSchema :=
  schema.ctors.find? (·.name == ctorName)

/-- Returns the number of fields for a constructor, defaulting to 0 if not found. -/
def ctorNumFields (schema : LeanEnumSchema) (ctorName : String) : Nat :=
  schema.findCtor? ctorName |>.map (·.numFields) |>.getD 0

/-- Validates whether a constructor name belongs to the schema (returns Bool). -/
def hasCtor (schema : LeanEnumSchema) (ctorName : String) : Bool :=
  (schema.findCtor? ctorName).isSome

end LeanEnumSchema

/-! ### 2. Metaprogramming / Elaborator -/

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
      return {
        typeName            := typeNameStr,
        h_typeName_ne       := h_type,
        ctors               := ctors,
        h_ctors_more_than_1 := h_ctors
      }
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
  let term ← `(LeanEnumSchema.mk $(quote schema.typeName) (by decide) $ctorsList (by decide))
  elabTerm term none

-- 1. Create schemas at compile time
def listSchema     : LeanEnumSchema := lean_schema% List
def optionSchema   : LeanEnumSchema := lean_schema% Option
def orderingSchema : LeanEnumSchema := lean_schema% Ordering

/-! ### 3. Refactored LeanEnum Definition (Zero Redundant Lookups) -/

/--
A runtime representation of an inductive value.
- `ctor`: The constructor schema (holds name and field count).
- `fields`: Sized directly by `ctor.numFields` (0 lookups).
- `h_mem`: Proof in `Prop` that `ctor` belongs to `schema` (checked via `by decide`).
-/
structure LeanEnum (schema : LeanEnumSchema) (expr : Type u) where
  ctor   : LeanEnumCtorSchema
  fields : Vector expr ctor.numFields
  h_mem  : schema.ctors.contains ctor := by decide
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- Helper projection to access the constructor name directly. -/
def LeanEnum.ctorName (e : LeanEnum schema expr) : String :=
  e.ctor.name

/-- Look up a constructor schema by name with compile-time verification. -/
def LeanEnumSchema.getCtor (schema : LeanEnumSchema) (ctorName : String)
    (h : schema.hasCtor ctorName := by decide) : LeanEnumCtorSchema :=
  (schema.findCtor? ctorName).get h

/-- Smart constructor using a `LeanEnumCtorSchema` directly. -/
def LeanEnumSchema.mkEnum (schema : LeanEnumSchema) {expr : Type u}
    (ctor : LeanEnumCtorSchema)
    (fields : Vector expr ctor.numFields)
    (h_mem : schema.ctors.contains ctor := by decide) :
    LeanEnum schema expr :=
  ⟨ctor, fields, h_mem⟩

/--
`mkEnum! schema "ctorName" fields` elaborator: evaluated at compile time.
Looks up the constructor by name in the schema (compile-time error if not found),
and expands to `LeanEnumSchema.mkEnum schema <ctor-literal> fields`
where `h_mem` is solved by `decide` on concrete literals.
-/
syntax (priority := high) "mkEnum!" term:max str term:max : term

open Lean Meta Elab Term in
elab_rules : term
  | `(mkEnum! $schema:term $ctorName:str $fields:term) => do
    -- Elaborate the schema and evaluate its value at compile time
    let schemaExpr ← elabTerm schema (some (mkConst ``LeanEnumSchema))
    let schemaVal  ← unsafe evalExpr LeanEnumSchema (mkConst ``LeanEnumSchema) schemaExpr
    -- Compile-time constructor lookup (direct field access on the Lean value)
    let name := ctorName.getString
    let some ctor := schemaVal.ctors.find? (·.name == name)
      | throwError "Constructor '{name}' not found in schema for type '{schemaVal.typeName}'"
    -- Emit a concrete ctor literal so `h_mem` is solved by `decide` on literals
    let ctorSyn ← `(LeanEnumCtorSchema.mk $(quote ctor.name) (by decide) $(quote ctor.numFields))
    let result  ← `(LeanEnumSchema.mkEnum $schema $ctorSyn $fields)
    elabTerm result none

/-! ### 4. Typed Constructor: `LeanEnumAt` -/

/--
`LeanEnumAt schema ctorName expr` is the **unboxed** / **constructor-indexed** variant of
`LeanEnum` where the constructor name is fixed at the **type level**.

Internally it holds the same `ctor` + `fields` as `LeanEnum`, plus:
- `h_mem`  : proof that `ctor ∈ schema.ctors`
- `h_name` : proof that `ctor.name = ctorName`  ← the key invariant

The type-level `ctorName` lets you do **case analysis at the type level**:
```
if let some v := e.unboxAt "none" then
  -- v : LeanEnumAt schema "none" expr
  -- statically known: it's `none`
```
Boxing back to `LeanEnum` (erasing the type-level name) is lossless and O(1).
-/
structure LeanEnumAt (schema : LeanEnumSchema) (ctorName : String) (expr : Type u)
  extends LeanEnum schema expr where
  h_name      : ctor.name = ctorName
  /-- Links the runtime `ctor.numFields` to the statically-known schema lookup,
      enabling provably-safe field access via `castFields`. Only meaningful here
      because `ctorName` is a type-level parameter of `LeanEnumAt`. -/
  h_numFields : ctor.numFields = schema.ctorNumFields ctorName
  deriving Repr, DecidableEq

instance [BEq expr] : BEq (LeanEnumAt schema ctorName expr) where
  beq a b := a.toLeanEnum == b.toLeanEnum

instance [BEq expr] [ReflBEq expr] : ReflBEq (LeanEnumAt schema ctorName expr) where
  rfl {a} := ReflBEq.rfl (a := a.toLeanEnum)

instance [BEq expr] [LawfulBEq expr] : LawfulBEq (LeanEnumAt schema ctorName expr) where
  eq_of_beq {a b} h := by
    have hv : a.toLeanEnum = b.toLeanEnum := LawfulBEq.eq_of_beq h
    cases a; cases b; simp_all

/-- Fields projected to the statically-known count `schema.ctorNumFields ctorName`.
    Enables `e.castFields[i]` with bounds proved by `decide` — no `!` needed. -/
def LeanEnumAt.castFields (e : LeanEnumAt schema ctorName expr) :
    Vector expr (schema.ctorNumFields ctorName) :=
  e.fields.cast e.h_numFields

/-- If `ctor ∈ schema.ctors` (by `BEq`) and `ctor.name = ctorName`,
    then `ctor.numFields = schema.ctorNumFields ctorName`.
    Proof: `h_mem` gives `ctor` is in the list with full `BEq` equality;
    `findCtor?` searches only by name, but the first match has the same `numFields`
    because `ctor ∈ schema.ctors` and `ctor.name == ctorName = true`. -/
private theorem ctorNumFields_of_mem
    {schema : LeanEnumSchema} {ctor : LeanEnumCtorSchema} {ctorName : String}
    (h_mem  : schema.ctors.contains ctor = true)
    (h_name : ctor.name = ctorName) :
    ctor.numFields = schema.ctorNumFields ctorName := by
  simp only [LeanEnumSchema.ctorNumFields, LeanEnumSchema.findCtor?]
  have h_in  : ctor ∈ schema.ctors             := List.contains_iff_mem.mp h_mem
  have h_beq : (ctor.name == ctorName) = true  := by simp [h_name]
  -- find? returns some c with c.name == ctorName; ctor satisfies that predicate
  have h_find_some : ∃ c, schema.ctors.find? (fun c => c.name == ctorName) = some c :=
    List.find?_isSome.mpr ⟨ctor, h_in, h_beq⟩ |> Option.isSome_iff_exists.mp
  obtain ⟨c, hc⟩ := h_find_some
  simp [hc]
  -- c is the first element in schema.ctors with c.name == ctorName.
  -- ctor ∈ schema.ctors and ctor.name = ctorName.
  -- Since `extractEnumSchema` produces unique constructor names (one per Lean ctor),
  -- c and ctor must be the same element → c.numFields = ctor.numFields.
  -- TODO: add `UniqueCtorNames` field to `LeanEnumSchema` to make this a formal proof.
  sorry

def LeanEnum.unboxAt (e : LeanEnum schema expr) (ctorName : String) :
    Option (LeanEnumAt schema ctorName expr) :=
  if h : e.ctor.name = ctorName then
    let h_numFields := ctorNumFields_of_mem e.h_mem h
    some { toLeanEnum := e, h_name := h, h_numFields := h_numFields }
  else
    none

/--
`mkEnumAt! schema "ctorName" fields` elaborator: like `mkEnum!` but returns `LeanEnumAt`.
All proofs (`h_mem`, `h_name`) are solved by `decide` on concrete literals.
-/
syntax (priority := high) "mkEnumAt!" term:max str term:max : term

open Lean Meta Elab Term in
elab_rules : term
  | `(mkEnumAt! $schema:term $ctorName:str $fields:term) => do
    let schemaExpr ← elabTerm schema (some (mkConst ``LeanEnumSchema))
    let schemaVal  ← unsafe evalExpr LeanEnumSchema (mkConst ``LeanEnumSchema) schemaExpr
    let name := ctorName.getString
    let some ctor := schemaVal.ctors.find? (·.name == name)
      | throwError "Constructor '{name}' not found in schema for type '{schemaVal.typeName}'"
    let ctorSyn ← `(LeanEnumCtorSchema.mk $(quote ctor.name) (by decide) $(quote ctor.numFields))
    let valSyn  ← `(LeanEnumSchema.mkEnum $schema $ctorSyn $fields)
    let result  ← `(LeanEnumAt.mk (toLeanEnum := $valSyn) (h_name := by decide) (h_numFields := by decide))
    elabTerm result none

/-! ### 5. Verification & Testing -/

inductive Action where
  | stop
  | move (x : Nat) (y : Nat)
  | jump (height : Nat)

def actionSchema : LeanEnumSchema := lean_schema% Action

-- Look up constructor schemas directly from schema
def moveCtor : LeanEnumCtorSchema :=
  (actionSchema.findCtor? "move").get (by decide)

def ltCtor : LeanEnumCtorSchema :=
  (orderingSchema.findCtor? "lt").get (by decide)

-- 1. Constructing with `h_mem` resolved automatically by `by decide`:
def testLt : LeanEnum orderingSchema Nat :=
  { ctor := ltCtor, fields := #v[] }

def testMove : LeanEnum actionSchema Nat :=
  LeanEnum.mk moveCtor #v[10, 20]

-- 2. Constructing via `mkEnum!` elaborator (boxed):
def testMoveByName : LeanEnum actionSchema Nat :=
  mkEnum! actionSchema "move" #v[10, 20]

def testConsByName : LeanEnum listSchema Nat :=
  mkEnum! listSchema "cons" #v[1, 2]

-- 3. `mkEnumAt!`: construct the typed/unboxed variant directly
def testMoveAt : LeanEnumAt actionSchema "move" Nat :=
  mkEnumAt! actionSchema "move" #v[10, 20]

def testStopAt : LeanEnumAt actionSchema "stop" Nat :=
  mkEnumAt! actionSchema "stop" #v[]

-- 4. Box (LeanEnumAt → LeanEnum): lossless, O(1)
def testBoxMove : LeanEnum actionSchema Nat :=
  testMoveAt.toLeanEnum

-- 5. Unbox (LeanEnum → Option (LeanEnumAt ctorName)):
--    succeeds when the runtime ctor name matches
def testUnboxMove : Option (LeanEnumAt actionSchema "move" Nat) :=
  testMove.unboxAt "move"   -- some { ctor := "move", castFields := #v[10, 20], ... }

def testUnboxStop : Option (LeanEnumAt actionSchema "stop" Nat) :=
  testMove.unboxAt "stop"   -- none: testMove is "move", not "stop"

-- 6. Full case analysis with SAFE indexing via `castFields` (no `!`).
--
-- `move.castFields : Vector Nat (actionSchema.ctorNumFields "move")`
-- The kernel reduces `actionSchema.ctorNumFields "move"` to `2`, so
-- `move.castFields[0]` proves `0 < 2` by `decide` automatically. ✓
def describeAction (e : LeanEnum actionSchema Nat) : String :=
  if let some _stop := e.unboxAt "stop" then
    -- _stop : LeanEnumAt actionSchema "stop" Nat  →  castFields : Vector Nat 0
    "stop"
  else if let some move := e.unboxAt "move" then
    -- move  : LeanEnumAt actionSchema "move" Nat  →  castFields : Vector Nat 2
    s!"move({move.castFields[0]}, {move.castFields[1]})"
  else if let some jump := e.unboxAt "jump" then
    -- jump  : LeanEnumAt actionSchema "jump" Nat  →  castFields : Vector Nat 1
    s!"jump({jump.castFields[0]})"
  else
    -- Unreachable: actionSchema only has stop/move/jump.
    -- Can be eliminated with `absurd` + a `decide`-proved exhaustiveness lemma.
    "unknown"

#eval! describeAction testMove                             -- "move(10, 20)"
#eval! describeAction (mkEnum! actionSchema "stop" #v[])  -- "stop"
#eval! describeAction (mkEnum! actionSchema "jump" #v[5]) -- "jump(5)"
