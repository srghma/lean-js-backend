-- SnapshotsMy.Tco07: the module as a Program of the one grammar of `LakeJs.Expr`.
-- 🎯 a public entry point of the module; 📦 a declaration the translation pulled in.
-- Every term below is a `Term`, so it is terminating by construction: the one way it
-- repeats work is `Term.fix`, whose measure it descends on at every self call.
--
-- ════ 🎯 boom : (fn nat nat)
--      measure: well-founded recursion, `termination_by` transcribed verbatim; 1 component: [ ♯0 ]
-- fix (nat) measure [ ♯0 ] body {
--   let ♯ := 1#;
--   let ♯ := ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯1) ⬝ ♯0);
--   if ♯0 then let ♯ := 0#;
--   ♯0 else let ♯ := 3#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯0) ⬝ ♯3);
--   let ♯ := self0⟨↓⟩(♯0);
--   ♯0
-- } stuck { 0# }
--
--
-- ── the same program as Lean source ────────────────────────────────────
-- The trees above are this program printed in the notation of `LakeJs.ExprPretty`;
-- copy one into a `[LEAN|...]` elaboration if you want to read it there.

import LakeJs

open LakeJs LakeJs.Ty LakeJs.Expr LakeJs.Expr.Ops

namespace ProgramSnapshotsMyTco07

/-- `boom`, as a declaration of the module. -/
def d_boom : GlobalDecl := ⟨"boom", (Ty.fn Ty.nat Ty.nat)⟩

/-- The signature `boom` is written against. -/
def sig_boom : Sig := ⟨[], by decide⟩

/-- The body of the recursion of `boom`. -/
def bd_boom : Term sig_boom ([Ty.nat] ++ []) [⟨[Ty.nat], Ty.nat⟩] Ty.nat :=
  (Term.letE (Term.natL 1) (Term.letE (natEq (♯1) (♯0)) (Term.ite (♯0) (Term.letE (Term.natL 0) (♯0)) (Term.letE (Term.natL 3) (Term.letE (natMul (♯0) (♯3)) (Term.letE (Term.selfCall .head (.cons (♯0) .nil)) (♯0)))))))

/-- The body of `boom`. -/
def tm_boom : Term sig_boom [] [] (Ty.fn Ty.nat Ty.nat) :=
  Term.fix [Ty.nat] 1 (.cons (♯0) .nil) bd_boom (Term.natL 0)

/-- The module up to and including `boom`. -/
def prog_boom : Program (d_boom :: sig_boom.decls) :=
  .cons d_boom sig_boom.h_names_unique tm_boom Program.nil

/-- The signature of the whole module. -/
def moduleSig : Sig := ⟨[d_boom], by decide⟩

/-- The module as a telescope: every body is written against the declarations before it, so the call graph is acyclic by construction.  It is built one declaration at a time, above, so that no single elaboration sees the whole telescope at once. -/
def program : Program moduleSig.decls :=
  prog_boom

end ProgramSnapshotsMyTco07
