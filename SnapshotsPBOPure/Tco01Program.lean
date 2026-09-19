-- SnapshotsPBOPure.Tco01: the module as a Program of the one grammar of `LakeJs.Expr`.
-- 🎯 a public entry point of the module; 📦 a declaration the translation pulled in.
-- Every term below is a `Term`, so it is terminating by construction: the one way it
-- repeats work is `Term.fix`, whose measure it descends on at every self call.
--
-- ════ 🎯 test : (fn nat nat)
--      measure: structural recursion, on the argument Lean recorded (position 0); 1 component: [ ♯0 ]
-- fix (nat) measure [ ♯0 ] body {
--   if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then ♯0 else let ♯ := self0⟨↓⟩(((extern⟨nat nat ⇒ nat⟩ ⬝ ♯0) ⬝ 1#));
--   ♯0
-- } stuck { 0# }
--
--
-- ── the same program as Lean source ────────────────────────────────────
-- The trees above are this program printed in the notation of `LakeJs.ExprPretty`;
-- copy one into a `[LEAN|...]` elaboration if you want to read it there.

import LakeJs

open LakeJs LakeJs.Ty LakeJs.Expr LakeJs.Expr.Ops

namespace ProgramSnapshotsPBOPureTco01

/-- `test`, as a declaration of the module. -/
def d_test : GlobalDecl := ⟨"test", (Ty.fn Ty.nat Ty.nat)⟩

/-- The signature `test` is written against. -/
def sig_test : Sig := ⟨[], by decide⟩

/-- The body of the recursion of `test`. -/
def bd_test : Term sig_test ([Ty.nat] ++ []) [⟨[Ty.nat], Ty.nat⟩] Ty.nat :=
  (Term.ite (natEq (♯0) (Term.natL 0)) (♯0) (Term.letE (Term.selfCall .head (.cons (natSub (♯0) (Term.natL 1)) .nil)) (♯0)))

/-- The body of `test`. -/
def tm_test : Term sig_test [] [] (Ty.fn Ty.nat Ty.nat) :=
  Term.fix [Ty.nat] 1 (.cons (♯0) .nil) bd_test (Term.natL 0)

/-- The module up to and including `test`. -/
def prog_test : Program (d_test :: sig_test.decls) :=
  .cons d_test sig_test.h_names_unique tm_test Program.nil

/-- The signature of the whole module. -/
def moduleSig : Sig := ⟨[d_test], by decide⟩

/-- The module as a telescope: every body is written against the declarations before it, so the call graph is acyclic by construction.  It is built one declaration at a time, above, so that no single elaboration sees the whole telescope at once. -/
def program : Program moduleSig.decls :=
  prog_test

end ProgramSnapshotsPBOPureTco01
