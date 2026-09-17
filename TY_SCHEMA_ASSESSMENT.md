# The seven shapes of `Ty`, and what is now a condition of writing one

This file used to argue that the payloads of `Ty`'s seven declaration shapes should stay
plain aliases, with the counting conditions written out separately as decidable
predicates in two tiers (`.ok` / `.strict`, `Ty.wf` / `Ty.wfStrict`) and checked at the
boundary.  **That design is gone.**  The payloads are now *types of their own*, in
`LakeJs/Schema.lean`, whose inhabitants are exactly the schemas that mean something, and
the two-tier split has been replaced by one `Ty.wf` that checks only what is left over —
the conditions about `self` that a payload type cannot see.

## What `LakeJs/Schema.lean` is

Every schema is parameterised by the type it holds, so the same schema types serve `Ty`,
`Ty.RTy` and any other type language added later:

| shape                      | payload                             | what is impossible to write                       |
| :------------------------- | :---------------------------------- | :------------------------------------------------ |
| `Ty.enum`                  | `LeanEnumSchema`                    | fewer than three constructors                      |
| `Ty.record`                | `LeanRecordSchema α`                | fewer than two fields                              |
| `Ty.taggedUnion`           | `LeanTaggedUnionSchema α`           | fewer than two constructors; no constructor with a field |
| `Ty.recTaggedUnion`        | `LeanTaggedUnionSchema α`        | as `taggedUnion`                                   |
| `Ty.recObject`             | `LeanRecordSchema α`             | as `record`                                        |
| `Ty.recAlias`              | `α`              | —                                                  |
| `Ty.mutualRecursiveFamily` | `LeanMutualRecFamily α`             | fewer than two members; a member number out of range |
| the invariant prims        | `LeanPrimTyInvariant α`             | —                                                  |
| the function space         | `TyFn α`                            | —                                                  |

The conditions are **structural**, not proof-carrying: nothing here is a `Subtype` and
nothing asks the translation for a `by decide`.

* `LeanRecordSchema α` is a structure with two fields and a list, so "at least two" is
  the shape of the data.
* `LeanEnumSchema` carries `extraConstructors : Nat` and the shift, and
  `nOfConstructors = extraConstructors + 3`.  Zero constructors is `Empty`, one is
  `Unit`, two is `Bool` — the first two the backend has no type for and refuses
  (`LakeJs.FromLcnf` says so with a message), and the third is modelled as `Ty.bool`.
* `LeanTaggedUnionSchema α` is an inductive that *marks* the first constructor carrying
  a field (`payloadFirst`), so "at least two constructors, at least one of them with a
  field" is again the shape of the data, and the marking is canonical: `toList` and
  `ofList?` round-trip (`toList_ofList?`), so there is exactly one schema per layout.
* `LeanMutualRecFamily α` is a zipper over the members — the members before the selected
  one, the selected one, and the members after — so the member number is in range by
  construction and there are always at least two members (`two_le_members`,
  `memberIdx_lt`).

Because the payloads are ordinary types, they carry the usual API — `toList`, `ofList?`,
`map`, `length` — and the round-trip lemmas that say `ofList?` is the inverse of
`toList` where it answers at all.  `Ty` and `Ty.RTy` are then defined *in terms of* them,
so a degenerate declaration shape is not something `Ty.wf` rejects: it is something that
does not typecheck.

## What is left for `Ty.wf`

Two families of conditions cannot be expressed by the payload type, because they are
about the *contents* of the payload rather than its shape:

1. **A recursive shape mentions itself.**  `Ty.recAlias ⟨.prim .nat⟩`, but it is not a recursive declaration; `Ty.not_wf_recAlias_noSelf`
   is the statement that `Ty.wf` refuses it.  The same goes for `recObject` and
   `recTaggedUnion`.
2. **A recursive declaration has values.**  `inductive Bad | mk : Bad → Bad` reads as
   `Ty.recAlias ⟨.self 0⟩`, the equation `T = T`, which no value satisfies.
   `Ty.not_wf_selfLoop` is the statement that `Ty.wf` refuses it, and
   `Ty.not_wf_recObject_selfField` the same for a record one of whose fields is the
   record itself.  What *is* accepted is a self-reference behind a shape that can be
   empty or can stop: `Ty.wf_recAlias_array` (`T = Array T`) and
   `Ty.wf_recTaggedUnion_tree`.

These are computed by `Ty.RTy.inhabWith`, a fixed-point over the members in scope, and by
`Ty.FamMember.hasSelf`; `Ty.wf` runs them at every node of a whole type, and `WfTy` is
the subtype of types that pass.  There is no second tier: strong connectivity of a
`mutual` block is part of `LeanMutualRecFamily.wf`, so a `mutual` block whose members
ignore each other is not read as a family.

## The remaining scoping mistake

`RTy.self` still takes a `Nat` rather than a `Fin` of the number of members in scope, so
`.self 3` inside a `recObject` is writable and rejected rather than unwritable.  Indexing
the inner layer by the number of members in scope (`RTy n` with `self : Fin n → RTy n`)
would remove it by construction.  It is a wide change — `Ty`, `Layout`, `Expr`,
`FromLcnf` and everything that pattern-matches on `RTy` — and it is the one item of this
assessment still outstanding.
