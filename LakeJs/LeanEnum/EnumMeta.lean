module

public import LakeJs.LeanEnum.Schema
public meta import LakeJs.LeanEnum.Schema
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
    let result  ← `(LeanEnumAt.mk (toLeanEnum := $valSyn) (h_name := by decide))
    elabTerm result none

/-! ### `match_enum`: pattern matching on a `LeanEnum` by constructor name

```
match_enum e with
  | "stop" => "stop"
  | "move" f => s!"move({f[0]}, {f[1]})"
  | "jump" f => s!"jump({f[0]})"
```

The schema is read off the type of the scrutinee at elaboration time, so:

* a constructor name that is not in the schema is a **compile-time error**;
* a repeated constructor name is a **compile-time error**;
* if the alternatives do not cover every constructor of the schema, that is a
  **compile-time error** too (add `| _ => ...` for an explicit catch-all);
* the fields binder gets type `Vector expr k` with `k` the **literal** field count
  taken from the schema, so `f[0]` is bounds-checked by `decide` -- no `!`, and
  `f[2]` on a two-field constructor is rejected at compile time;
* the fields binder may be dropped when the branch ignores the fields.

When the alternatives are exhaustive there is no fallback value to invent: the
expansion ends in `(LeanEnum.exhaustive_of_cover ...).elim`, i.e. a proof that the
remaining case cannot happen. -/

/-- One alternative of `match_enum`: `| "ctorName" fields => body`.
    The fields binder may be omitted when the branch does not use the fields. -/
syntax matchEnumAlt := atomic(" | " str) (ident)? " => " term
/-- Catch-all alternative of `match_enum`: `| _ => body`. -/
syntax matchEnumElse := " | " "_" " => " term

syntax (name := matchEnumSyntax) "match_enum " term " with"
  (ppLine matchEnumAlt)* (ppLine matchEnumElse)? : term

open Lean Meta Elab Term in
elab_rules : term <= expectedType?
  | `(match_enum $scrut with $alts:matchEnumAlt* $[$els?:matchEnumElse]?) => do
    -- 1. Elaborate the scrutinee and read its schema off its type.
    let eExpr ← instantiateMVars (← elabTerm scrut none)
    let eType ← whnf (← instantiateMVars (← inferType eExpr))
    let some schemaExpr := (do
        guard (eType.getAppFn.constName? == some ``LeanEnum)
        eType.getAppArgs[0]?)
      | throwError "`match_enum` expects a scrutinee of type `LeanEnum schema expr`, got{indentExpr eType}"
    let schemaVal ← unsafe evalExpr LeanEnumSchema (mkConst ``LeanEnumSchema) schemaExpr
    let enumSyn ← exprToSyntax eExpr

    -- 2. Check the alternatives against the schema.
    let mut names   : Array String := #[]
    let mut numFieldss : Array Nat := #[]
    let mut binders : Array (Option Ident) := #[]
    let mut bodies  : Array Term := #[]
    for alt in alts do
      let `(matchEnumAlt| | $nameStx:str $[$b?:ident]? => $body) := alt
        | throwErrorAt alt "ill-formed `match_enum` alternative"
      let name := nameStx.getString
      if names.contains name then
        throwErrorAt nameStx "duplicate `match_enum` alternative for constructor '{name}'"
      let some ctor := schemaVal.ctors.find? (·.name == name)
        | throwErrorAt nameStx
            "constructor '{name}' is not in the schema for type '{schemaVal.typeName}'"
      names   := names.push name
      numFieldss := numFieldss.push ctor.numFields
      binders := binders.push b?
      bodies  := bodies.push body
    if els?.isNone then
      let missing := (schemaVal.ctors.filter (fun c => !names.contains c.name)).map (·.name)
      unless missing.isEmpty do
        throwError "`match_enum` is not exhaustive for type '{schemaVal.typeName}': missing constructor(s) {missing}. Add them, or a catch-all `| _ => ...`."

    -- 3. The last branch: either the user's catch-all, or a proof that this case
    --    is unreachable, built from the recorded `unboxAt ... = none` equations.
    let hyps : Array Ident :=
      (Array.range names.size).map fun i => mkIdent (Name.mkSimple s!"h_match_enum_{i}")
    let fallback : Term ←
      match els? with
      | some els =>
        match els with
        | `(matchEnumElse| | _ => $body) => pure body
        | _ => throwErrorAt els "ill-formed `match_enum` catch-all"
      | none =>
        let nameLits : Array Term := names.map fun n => quote n
        let namesSyn ← `([$[$nameLits],*])
        let mut prf ← `(LeanEnum.noneAtAll_nil $enumSyn)
        for h in hyps.reverse do
          prf ← `(LeanEnum.noneAtAll_cons $h $prf)
        `((LeanEnum.exhaustive_of_cover $enumSyn $namesSyn (by decide) $prf).elim)
    let mut result : Term := fallback

    -- 4. Wrap the branches around it, innermost (last alternative) first.
    for i in [0:names.size] do
      let j     := names.size - 1 - i
      let hName := hyps[j]!
      let tmp   := mkIdent (Name.mkSimple s!"__match_enum_at_{j}")
      let nameLit : Term := quote names[j]!
      let numFields : Term := quote numFieldss[j]!
      let branch ←
        match binders[j]! with
        | some f =>
          -- `castFields` has the schema-level field count; re-cast it to the literal
          -- one so that `f[0]` is bounds-checked by `decide`.
          `(let $f:ident : Vector _ $numFields :=
              Vector.cast (by decide) (LeanEnumAt.castFields $tmp)
            $(bodies[j]!))
        | none => pure bodies[j]!
      result ←
        `(match $hName:ident : LeanEnum.unboxAt $enumSyn $nameLit with
          | some $tmp:ident => $branch
          | none => $result)

    elabTerm result expectedType?

-- Schemas created at compile time from real Lean inductive types.
def listSchema     : LeanEnumSchema := lean_schema% List
def optionSchema   : LeanEnumSchema := lean_schema% Option
def orderingSchema : LeanEnumSchema := lean_schema% Ordering
