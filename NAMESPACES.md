# Namespaces in `LakeJs`

One rule, and it holds of every file in `LakeJs/`:

> every declaration of `LakeJs/X.lean` is named `LakeJs.X` or `LakeJs.X.…`

Nothing in the backend is declared at the root any more, and no two files share a
namespace.

## The ordinary case

A module that owns a batch of functions opens its own namespace and closes it at the
bottom:

```lean
namespace LakeJs.Simp
…
end LakeJs.Simp
```

so `Term.simp` is `LakeJs.Simp.Term.simp`, `LakeJs.Inline.Table` is the inliner's table,
and so on.  A consumer writes `open LakeJs.Simp` and then `Term.simp` as before.

## A file named after the type it defines

`Ty.lean` defines the type `Ty`, `LeanPrimTy.lean` defines `LeanPrimTy`, `Externs.lean`
defines `Externs`.  For those the file's namespace *is* the type: the type is
`LakeJs.Ty`, and everything else the file declares lives under it —

| declaration            | full name                |
| :--------------------- | :----------------------- |
| the closed type        | `LakeJs.Ty`              |
| the recursive layer    | `LakeJs.Ty.RTy`          |
| the shared formers     | `LakeJs.Ty.Shape`        |
| a member of a family   | `LakeJs.Ty.FamMember`    |
| structural equality    | `LakeJs.Ty.beq`          |
| `.nat`, `.fn`, …       | `LakeJs.Ty.nat`, …       |

which keeps `Ty.beq`, `RTy.self`, `Ty.nat` reading exactly as they did, and avoids the
`LakeJs.Ty.Ty` a blind wrapping would have produced.

## A file that extends another file's type

`Layout.lean`, `TyPretty.lean`, `Rename.lean`, `TermTotal.lean` and `ExternsMeta.lean`
add an API to a type defined elsewhere.  Their declarations still live in their own
namespace — `LakeJs.Layout.Ty.layout?`, `LakeJs.TyPretty.Ty.pretty` — and each file ends
with an `export` block that puts the same declarations under the namespace of the type
they are about:

```lean
namespace LakeJs.Ty
export LakeJs.Layout.Ty (layout? aliasUnfold? isAlias …)
end LakeJs.Ty
```

so `τ.layout?` and `τ.pretty` keep working at every use site, while the file the
definition lives in is still visible in its name.

## Consumers

A module that uses the type language opens what it needs:

```lean
open LakeJs                -- Ty, LeanPrimTy, Externs, …
open LakeJs.Ty             -- RTy, Shape, FamMember, and the `Ty` API
open LakeJs.Expr           -- Term, Sig, Ctx, Var, Alts, Body, Spine, …
open LakeJs.Layout (FieldLayout ObjLayout)
```

Note that `open LakeJs.Ty` has to be the *whole* namespace rather than a selective
`open LakeJs.Ty (RTy)`: a name reached through a selective open is not resolved through
the `export` aliases above, so `RTy.hasSelf` would not be found.
