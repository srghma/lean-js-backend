-- RankFlakiness.AckOpaqueArg: the module as a Program of the one grammar of `LakeJs.Expr`.
-- 🎯 a public entry point of the module; 📦 a declaration the translation pulled in.
-- Every term below is a `Term`, so it is terminating by construction: the one way it
-- repeats work is `Term.fix`, whose measure it descends on at every self call.
--
-- ════ 🎯 ackOpaque : (fn nat (fn nat nat))
--      measure: well-founded recursion, `termination_by` transcribed verbatim; 2 components: [ ♯0, ♯1 ]
-- fix (nat nat) measure [ ♯0, ♯1 ] body {
--   if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then let ♯ := 1#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ ♯0);
--   ♯0 else if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯1) ⬝ 0#) then let ♯ := 1#;
--   let ♯ := self0⟨↓⟩(((extern⟨nat nat ⇒ nat⟩ ⬝ ♯1) ⬝ 1#), ♯0);
--   ♯0 else let ♯ := 2#;
--   let ♯ := 1#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ 1#)) ⬝ ♯0);
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ ♯0);
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯0) ⬝ ♯1);
--   let ♯ := self0⟨↓⟩(♯0, ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯6) ⬝ 1#));
--   let ♯ := self0⟨↓⟩(((extern⟨nat nat ⇒ nat⟩ ⬝ ♯6) ⬝ 1#), ♯0);
--   ♯0
-- } stuck { 0# }
--
--
-- ── the same program as Lean source ────────────────────────────────────
-- The trees above are this program printed in the notation of `LakeJs.ExprPretty`;
-- copy one into a `[LEAN|...]` elaboration if you want to read it there.

import LakeJs

open LakeJs LakeJs.Ty LakeJs.Expr LakeJs.Expr.Ops

namespace ProgramRankFlakinessAckOpaqueArg

/-- `ackOpaque`, as a declaration of the module. -/
def d_ackOpaque : GlobalDecl := ⟨"ackOpaque", (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat))⟩

/-- The signature `ackOpaque` is written against. -/
def sig_ackOpaque : Sig := ⟨[], by decide⟩

/-- The body of `ackOpaque`. -/
def tm_ackOpaque : Term sig_ackOpaque [] [] (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat)) :=
  (Term.fix [Ty.nat, Ty.nat] 2 (.cons (♯0) (.cons (♯1) .nil)) (Term.ite (natEq (♯0) (Term.natL 0)) (Term.letE (Term.natL 1) (Term.letE (natAdd (♯2) (♯0)) (♯0))) (Term.ite (natEq (♯1) (Term.natL 0)) (Term.letE (Term.natL 1) (Term.letE (Term.selfCall .head (.cons (natSub (♯1) (Term.natL 1)) (.cons (♯0) .nil))) (♯0))) (Term.letE (Term.natL 2) (Term.letE (Term.natL 1) (Term.letE (natAdd (natSub (♯2) (Term.natL 1)) (♯0)) (Term.letE (natMul (♯2) (♯0)) (Term.letE (natSub (♯0) (♯1)) (Term.letE (Term.selfCall .head (.cons (♯0) (.cons (natSub (♯6) (Term.natL 1)) .nil))) (Term.letE (Term.selfCall .head (.cons (natSub (♯6) (Term.natL 1)) (.cons (♯0) .nil))) (♯0)))))))))) (Term.natL 0))

/-- The module up to and including `ackOpaque`. -/
def prog_ackOpaque : Program (d_ackOpaque :: sig_ackOpaque.decls) :=
  .cons d_ackOpaque sig_ackOpaque.h_names_unique tm_ackOpaque Program.nil

/-- The signature of the whole module. -/
def moduleSig : Sig := ⟨[d_ackOpaque], by decide⟩

/-- The module as a telescope: every body is written against the declarations before it, so the call graph is acyclic by construction.  It is built one declaration at a time, above, so that no single elaboration sees the whole telescope at once. -/
def program : Program moduleSig.decls :=
  prog_ackOpaque

end ProgramRankFlakinessAckOpaqueArg
