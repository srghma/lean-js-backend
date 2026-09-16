module

public import LakeJs.Compile
public import LakeJs.Config
public import LakeJs.EmitJs
public import LakeJs.Expr
public import LakeJs.ExternTable
public import LakeJs.ExternsMeta
public import LakeJs.FloatDecide
public import LakeJs.FloatDecideTests
public import LakeJs.FromLcnf
public import LakeJs.Layout
public import LakeJs.LeanImpureExtern
public import LakeJs.LeanPrimTy
public import LakeJs.LeanPureExtern
public import LakeJs.Lookup
public import LakeJs.Simp
public import LakeJs.TermTotal
public import LakeJs.Totality
public import LakeJs.Ty

def main (args : List String) : IO Unit := do
  let args := args.toArray

-- prelude
--
-- public import LakeJs.LeanEnum.Schema
-- public meta import LakeJs.LeanEnum.Schema
-- public import LakeJs.LeanEnum.SchemaMeta
-- public meta import LakeJs.LeanEnum.SchemaMeta

-- public import LakeJs.LeanEnum.Enum
-- public meta import LakeJs.LeanEnum.Enum
-- public import LakeJs.LeanEnum.EnumMeta
-- public meta import LakeJs.LeanEnum.EnumMeta
-- public import LakeJs.LeanEnum.EnumDemo

/-!
# `LeanEnum`: schema-driven runtime representation of Lean inductive types

Root module re-exporting the three parts:

* `LakeJs.LeanEnum.Basic` — schemas, `LeanEnum`, `LeanEnumAt`, `unboxAt`
  and the proofs tying them together (in particular `ctorNumFields_of_mem` and the
  exhaustiveness principle `LeanEnum.exhaustive`),
* `LakeJs.LeanEnum.Meta` — the compile-time elaborators `lean_schema%`,
  `mkEnum!`, `mkEnumAt!` and `match_enum` (pattern matching on a `LeanEnum` by
  constructor name, with exhaustiveness checked against the schema at compile time),
* `LakeJs.LeanEnum.Demo` — worked example (`Action`) with a total, safe,
  `match`-based eliminator whose fallback branch is proved unreachable, both spelled
  out by hand (`describeAction`) and written with `match_enum` (`describeActionMatch`).
-/
