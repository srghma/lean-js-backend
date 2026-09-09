module

prelude

public import LakeJs.LeanEnum.Schema
public meta import LakeJs.LeanEnum.Schema
public import LakeJs.LeanEnum.SchemaMeta
public meta import LakeJs.LeanEnum.SchemaMeta
public import LakeJs.LeanEnum.Enum
public meta import LakeJs.LeanEnum.Enum
public import LakeJs.LeanEnum.EnumMeta
public meta import LakeJs.LeanEnum.EnumMeta
public import LakeJs.LeanEnum.EnumDemo

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
