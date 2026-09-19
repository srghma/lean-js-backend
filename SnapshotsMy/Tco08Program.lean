-- SnapshotsMy.Tco08: the module as a Program of the one grammar of `LakeJs.Expr`.
-- 🎯 a public entry point of the module; 📦 a declaration the translation pulled in.
-- Every term below is a `Term`, so it is terminating by construction: the one way it
-- repeats work is `Term.fix`, whose measure it descends on at every self call.
--
-- ════ 🎯 ack : (fn nat (fn nat nat))
--      measure: well-founded recursion, `termination_by` transcribed verbatim; 2 components: [ ♯0, ♯1 ]
-- fix (nat nat) measure [ ♯0, ♯1 ] body {
--   if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then let ♯ := 1#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ ♯0);
--   ♯0 else if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯1) ⬝ 0#) then let ♯ := 1#;
--   let ♯ := self0⟨↓⟩(((extern⟨nat nat ⇒ nat⟩ ⬝ ♯1) ⬝ 1#), ♯0);
--   ♯0 else let ♯ := 1#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯1) ⬝ 1#)) ⬝ ♯0);
--   let ♯ := self0⟨↓⟩(♯0, ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯3) ⬝ 1#));
--   let ♯ := self0⟨↓⟩(((extern⟨nat nat ⇒ nat⟩ ⬝ ♯3) ⬝ 1#), ♯0);
--   ♯0
-- } stuck { 0# }
--
-- ════ 🎯 ack999 : nat
-- let ♯ := 999#;
-- let ♯ := 1#;
-- let ♯ := ((@ack ⬝ ♯1) ⬝ ♯0);
-- ♯0
--
--
-- ── the same program as Lean source ────────────────────────────────────
-- The trees above are this program printed in the notation of `LakeJs.ExprPretty`;
-- copy one into a `[LEAN|...]` elaboration if you want to read it there.

import LakeJs

open LakeJs LakeJs.Ty LakeJs.Expr LakeJs.Expr.Ops

namespace ProgramSnapshotsMyTco08

/-- `ack`, as a declaration of the module. -/
def d_ack : GlobalDecl := ⟨"ack", (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat))⟩

/-- The signature `ack` is written against. -/
def sig_ack : Sig := ⟨[], by decide⟩

/-- The body of the recursion of `ack`. -/
def bd_ack : Term sig_ack ([Ty.nat, Ty.nat] ++ []) [⟨[Ty.nat, Ty.nat], Ty.nat⟩] Ty.nat :=
  (Term.ite (natEq (♯0) (Term.natL 0)) (Term.letE (Term.natL 1) (Term.letE (natAdd (♯2) (♯0)) (♯0))) (Term.ite (natEq (♯1) (Term.natL 0)) (Term.letE (Term.natL 1) (Term.letE (Term.selfCall .head (.cons (natSub (♯1) (Term.natL 1)) (.cons (♯0) .nil))) (♯0))) (Term.letE (Term.natL 1) (Term.letE (natAdd (natSub (♯1) (Term.natL 1)) (♯0)) (Term.letE (Term.selfCall .head (.cons (♯0) (.cons (natSub (♯3) (Term.natL 1)) .nil))) (Term.letE (Term.selfCall .head (.cons (natSub (♯3) (Term.natL 1)) (.cons (♯0) .nil))) (♯0)))))))

/-- The body of `ack`. -/
def tm_ack : Term sig_ack [] [] (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat)) :=
  Term.fix [Ty.nat, Ty.nat] 2 (.cons (♯0) (.cons (♯1) .nil)) bd_ack (Term.natL 0)

/-- The module up to and including `ack`. -/
def prog_ack : Program (d_ack :: sig_ack.decls) :=
  .cons d_ack sig_ack.h_names_unique tm_ack Program.nil

/-- `ack999`, as a declaration of the module. -/
def d_ack999 : GlobalDecl := ⟨"ack999", Ty.nat⟩

/-- The signature `ack999` is written against. -/
def sig_ack999 : Sig := ⟨[d_ack], by decide⟩

/-- The body of `ack999`. -/
def tm_ack999 : Term sig_ack999 [] [] Ty.nat :=
  (Term.letE (Term.natL 999) (Term.letE (Term.natL 1) (Term.letE (Term.ap (Term.ap (Term.global .here) (♯1)) (♯0)) (♯0))))

/-- The module up to and including `ack999`. -/
def prog_ack999 : Program (d_ack999 :: sig_ack999.decls) :=
  .cons d_ack999 sig_ack999.h_names_unique tm_ack999 prog_ack

/-- The signature of the whole module. -/
def moduleSig : Sig := ⟨[d_ack999, d_ack], by decide⟩

/-- The module as a telescope: every body is written against the declarations before it, so the call graph is acyclic by construction.  It is built one declaration at a time, above, so that no single elaboration sees the whole telescope at once. -/
def program : Program moduleSig.decls :=
  prog_ack999

end ProgramSnapshotsMyTco08
