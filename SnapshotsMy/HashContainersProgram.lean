-- SnapshotsMy.HashContainers: the module as a Program of the one grammar of `LakeJs.Expr`.
-- 🎯 a public entry point of the module; 📦 a declaration the translation pulled in.
-- Every term below is a `Term`, so it is terminating by construction: the one way it
-- repeats work is `Term.fix`, whose measure it descends on at every self call.
-- refused by the totality gate: `_private.Init.Data.Array.Basic.0.Array.foldrMUnsafe.fold._at_.test6.spec_2` (reached from `test6`): it is a specialization of the `unsafe def` `_private.Init.Data.Array.Basic.0.Array.foldrMUnsafe.fold`, which Lean did not prove terminating; the backend cannot turn it into a loop
-- outside the language: `test1`: `Std.DHashMap.Internal.AssocList.nil` builds a value of a type that is not one the front end translates
-- outside the language: `test2`: `Std.DHashMap.Internal.AssocList.nil` builds a value of a type that is not one the front end translates
-- outside the language: `test3`: `Std.DHashMap.Internal.AssocList.nil` builds a value of a type that is not one the front end translates
-- outside the language: `test4`: `Std.DHashMap.Internal.AssocList.nil` builds a value of a type that is not one the front end translates
-- outside the language: `test5`: `Std.DHashMap.Internal.AssocList.nil` builds a value of a type that is not one the front end translates
-- outside the language: `test6`: `Std.DHashMap.Internal.AssocList.nil` builds a value of a type that is not one the front end translates
-- outside the language: `test7`: `Std.DHashMap.Internal.AssocList.nil` builds a value of a type that is not one the front end translates
--
--
-- ── the same program as Lean source ────────────────────────────────────
-- The trees above are this program printed in the notation of `LakeJs.ExprPretty`;
-- copy one into a `[LEAN|...]` elaboration if you want to read it there.

import LakeJs

open LakeJs LakeJs.Ty LakeJs.Expr LakeJs.Expr.Ops

namespace ProgramSnapshotsMyHashContainers

/-- The signature of the whole module. -/
def moduleSig : Sig := ⟨[], by decide⟩

/-- The module as a telescope: every body is written against the declarations before it, so the call graph is acyclic by construction.  It is built one declaration at a time, above, so that no single elaboration sees the whole telescope at once. -/
def program : Program moduleSig.decls :=
  Program.nil

end ProgramSnapshotsMyHashContainers
