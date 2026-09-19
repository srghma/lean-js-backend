-- SnapshotsPBOPure.VanLaarhovenTraversals01: the module as a Program of the one grammar of `LakeJs.Expr`.
-- 🎯 a public entry point of the module; 📦 a declaration the translation pulled in.
-- Every term below is a `Term`, so it is terminating by construction: the one way it
-- repeats work is `Term.fix`, whose measure it descends on at every self call.
-- outside the language: `instDecidableEqFun`: the parameter `x.1` of `instDecidableEqFun` has type `Fun`, which the front end does not translate (every constructor of `Fun` mentions `Fun`, so it has no values, and every type of the language has a canonical value)
-- outside the language: `instReprFun`: the result type of `instReprFun`, `Repr Fun`, is not one the front end translates
-- outside the language: `rewriteBottomUp`: the parameter `k` of `rewriteBottomUp` has type `Fun →
--   Fun`, which the front end does not translate
-- outside the language: `rewriteBottomUpM`: the parameter `m` of `rewriteBottomUpM` has type `Type →
--   Type`, which the front end does not translate
-- outside the language: `traverseFun1`: the parameter `f` of `traverseFun1` has type `Type → Type`, which the front end does not translate
-- outside the language: `traverseFun1D`: the parameter `f` of `traverseFun1D` has type `Type →
--   Type`, which the front end does not translate
-- outside the language: `Fun.ctorElim`: the parameter `motive` of `Fun.ctorElim` has type `Fun →
--   Sort u`, which the front end does not translate
-- outside the language: `Fun.ctorIdx`: the parameter `x` of `Fun.ctorIdx` has type `Fun`, which the front end does not translate (every constructor of `Fun` mentions `Fun`, so it has no values, and every type of the language has a canonical value)
-- outside the language: `Fun.size`: the parameter `x.1` of `Fun.size` has type `Fun`, which the front end does not translate (every constructor of `Fun` mentions `Fun`, so it has no values, and every type of the language has a canonical value)
-- outside the language: `instDecidableEqFun.decEq`: the parameter `x.1` of `instDecidableEqFun.decEq` has type `Fun`, which the front end does not translate (every constructor of `Fun` mentions `Fun`, so it has no values, and every type of the language has a canonical value)
-- outside the language: `instReprFun.repr`: the parameter `x.1` of `instReprFun.repr` has type `Fun`, which the front end does not translate (every constructor of `Fun` mentions `Fun`, so it has no values, and every type of the language has a canonical value)
-- outside the language: `Fun.Abs.elim`: the parameter `motive` of `Fun.Abs.elim` has type `Fun →
--   Sort u`, which the front end does not translate
-- outside the language: `Fun.App.elim`: the parameter `motive` of `Fun.App.elim` has type `Fun →
--   Sort u`, which the front end does not translate
--
--
-- ── the same program as Lean source ────────────────────────────────────
-- The trees above are this program printed in the notation of `LakeJs.ExprPretty`;
-- copy one into a `[LEAN|...]` elaboration if you want to read it there.

import LakeJs

open LakeJs LakeJs.Ty LakeJs.Expr LakeJs.Expr.Ops

namespace ProgramSnapshotsPBOPureVanLaarhovenTraversals01

/-- The signature of the whole module. -/
def moduleSig : Sig := ⟨[], by decide⟩

/-- The module as a telescope: every body is written against the declarations before it, so the call graph is acyclic by construction.  It is built one declaration at a time, above, so that no single elaboration sees the whole telescope at once. -/
def program : Program moduleSig.decls :=
  Program.nil

end ProgramSnapshotsPBOPureVanLaarhovenTraversals01
