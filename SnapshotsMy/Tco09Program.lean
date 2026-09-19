-- SnapshotsMy.Tco09: the module as a Program of the one grammar of `LakeJs.Expr`.
-- 🎯 a public entry point of the module; 📦 a declaration the translation pulled in.
-- Every term below is a `Term`, so it is terminating by construction: the one way it
-- repeats work is `Term.fix`, whose measure it descends on at every self call.
--
-- ════ 🎯 ackRev : (fn nat (fn nat nat))
--      measure: well-founded recursion, `termination_by` transcribed verbatim; 2 components: [ ♯1, ♯0 ]
-- fix (nat nat) measure [ ♯1, ♯0 ] body {
--   if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯1) ⬝ 0#) then let ♯ := 1#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯1) ⬝ ♯0);
--   ♯0 else if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then let ♯ := 1#;
--   let ♯ := self0⟨↓⟩(♯0, ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ 1#));
--   ♯0 else let ♯ := 1#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ 1#)) ⬝ ♯0);
--   let ♯ := self0⟨↓⟩(((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ 1#), ♯0);
--   let ♯ := self0⟨↓⟩(♯0, ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯4) ⬝ 1#));
--   ♯0
-- } stuck { 0# }
--
-- ════ 🎯 diagonal : (fn nat (fn nat nat))
--      measure: well-founded recursion, `termination_by` transcribed verbatim; 2 components: [ ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯0) ⬝ ♯1), ♯0 ]
-- fix (nat nat) measure [ ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯0) ⬝ ♯1), ♯0 ] body {
--   if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯1) ⬝ 0#) then let ♯ := 0#;
--   ♯0 else let ♯ := 0#;
--   let ♯ := self0⟨↓⟩(((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ 1#), ♯0);
--   let ♯ := 1#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯1) ⬝ ♯0);
--   ♯0 else let ♯ := 1#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ ♯0);
--   let ♯ := self0⟨↓⟩(((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ 1#), ♯0);
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯0) ⬝ ♯2);
--   ♯0
-- } stuck { 0# }
--
-- ════ 🎯 hyper : (fn nat (fn nat (fn nat nat)))
--      measure: well-founded recursion, `termination_by` transcribed verbatim; 2 components: [ ♯0, ♯2 ]
-- fix (nat nat nat) measure [ ♯0, ♯2 ] body {
--   if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then let ♯ := 1#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯3) ⬝ ♯0);
--   ♯0 else if ((extern⟨nat nat ⇒ bool⟩ ⬝ ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯0) ⬝ 1#)) ⬝ 0#) then if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯2) ⬝ 0#) then ♯1 else let ♯ := 1#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯1) ⬝ 1#)) ⬝ ♯0);
--   let ♯ := self0⟨↓⟩(♯0, ♯3, ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯4) ⬝ 1#));
--   let ♯ := self0⟨↓⟩(((extern⟨nat nat ⇒ nat⟩ ⬝ ♯3) ⬝ 1#), ♯4, ♯0);
--   ♯0 else if ((extern⟨nat nat ⇒ bool⟩ ⬝ ((extern⟨nat nat ⇒ nat⟩ ⬝ ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯0) ⬝ 1#)) ⬝ 1#)) ⬝ 0#) then if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯2) ⬝ 0#) then let ♯ := 0#;
--   ♯0 else let ♯ := 1#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯1) ⬝ 1#)) ⬝ ♯0);
--   let ♯ := self0⟨↓⟩(♯0, ♯3, ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯4) ⬝ 1#));
--   let ♯ := self0⟨↓⟩(((extern⟨nat nat ⇒ nat⟩ ⬝ ♯3) ⬝ 1#), ♯4, ♯0);
--   ♯0 else if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯2) ⬝ 0#) then let ♯ := 1#;
--   ♯0 else let ♯ := 1#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯1) ⬝ 1#)) ⬝ ♯0);
--   let ♯ := self0⟨↓⟩(♯0, ♯3, ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯4) ⬝ 1#));
--   let ♯ := self0⟨↓⟩(((extern⟨nat nat ⇒ nat⟩ ⬝ ♯3) ⬝ 1#), ♯4, ♯0);
--   ♯0
-- } stuck { 0# }
--
-- ════ 🎯 Mc91.M : (fn nat nat)
--      measure: well-founded recursion, `termination_by` transcribed verbatim; 1 component: [ ((extern⟨nat nat ⇒ nat⟩ ⬝ 101#) ⬝ ♯0) ]
-- fix (nat) measure [ ((extern⟨nat nat ⇒ nat⟩ ⬝ 101#) ⬝ ♯0) ] body {
--   let ♯ := 100#;
--   let ♯ := ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ ♯1);
--   if ♯0 then let ♯ := 10#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯3) ⬝ ♯0);
--   let ♯ := ♯0;
--   ♯0 else let ♯ := 11#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯3) ⬝ ♯0);
--   let ♯ := self0⟨↓⟩(♯0);
--   let ♯ := ♯0;
--   let ♯ := self0⟨↓⟩(♯0);
--   let ♯ := ♯0;
--   let ♯ := ♯0;
--   ♯0
-- } stuck { 0# }
--
-- ════ 🎯 Mc91 : (fn nat nat)
-- ƛ let ♯ := (@Mc91.M ⬝ ♯0);
-- let ♯ := ♯0;
-- ♯0
--
--
-- ── the same program as Lean source ────────────────────────────────────
-- The trees above are this program printed in the notation of `LakeJs.ExprPretty`;
-- copy one into a `[LEAN|...]` elaboration if you want to read it there.

import LakeJs

open LakeJs LakeJs.Ty LakeJs.Expr LakeJs.Expr.Ops

namespace ProgramSnapshotsMyTco09

/-- `ackRev`, as a declaration of the module. -/
def d_ackRev : GlobalDecl := ⟨"ackRev", (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat))⟩

/-- The signature `ackRev` is written against. -/
def sig_ackRev : Sig := ⟨[], by decide⟩

/-- The body of the recursion of `ackRev`. -/
def bd_ackRev : Term sig_ackRev ([Ty.nat, Ty.nat] ++ []) [⟨[Ty.nat, Ty.nat], Ty.nat⟩] Ty.nat :=
  (Term.ite (natEq (♯1) (Term.natL 0)) (Term.letE (Term.natL 1) (Term.letE (natAdd (♯1) (♯0)) (♯0))) (Term.ite (natEq (♯0) (Term.natL 0)) (Term.letE (Term.natL 1) (Term.letE (Term.selfCall .head (.cons (♯0) (.cons (natSub (♯2) (Term.natL 1)) .nil))) (♯0))) (Term.letE (Term.natL 1) (Term.letE (natAdd (natSub (♯2) (Term.natL 1)) (♯0)) (Term.letE (Term.selfCall .head (.cons (natSub (♯2) (Term.natL 1)) (.cons (♯0) .nil))) (Term.letE (Term.selfCall .head (.cons (♯0) (.cons (natSub (♯4) (Term.natL 1)) .nil))) (♯0)))))))

/-- The body of `ackRev`. -/
def tm_ackRev : Term sig_ackRev [] [] (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat)) :=
  Term.fix [Ty.nat, Ty.nat] 2 (.cons (♯1) (.cons (♯0) .nil)) bd_ackRev (Term.natL 0)

/-- The module up to and including `ackRev`. -/
def prog_ackRev : Program (d_ackRev :: sig_ackRev.decls) :=
  .cons d_ackRev sig_ackRev.h_names_unique tm_ackRev Program.nil

/-- `diagonal`, as a declaration of the module. -/
def d_diagonal : GlobalDecl := ⟨"diagonal", (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat))⟩

/-- The signature `diagonal` is written against. -/
def sig_diagonal : Sig := ⟨[d_ackRev], by decide⟩

/-- The body of the recursion of `diagonal`. -/
def bd_diagonal : Term sig_diagonal ([Ty.nat, Ty.nat] ++ []) [⟨[Ty.nat, Ty.nat], Ty.nat⟩] Ty.nat :=
  (Term.ite (natEq (♯0) (Term.natL 0)) (Term.ite (natEq (♯1) (Term.natL 0)) (Term.letE (Term.natL 0) (♯0)) (Term.letE (Term.natL 0) (Term.letE (Term.selfCall .head (.cons (natSub (♯2) (Term.natL 1)) (.cons (♯0) .nil))) (Term.letE (Term.natL 1) (Term.letE (natAdd (♯1) (♯0)) (♯0)))))) (Term.letE (Term.natL 1) (Term.letE (natAdd (♯2) (♯0)) (Term.letE (Term.selfCall .head (.cons (natSub (♯2) (Term.natL 1)) (.cons (♯0) .nil))) (Term.letE (natAdd (♯0) (♯2)) (♯0))))))

/-- The body of `diagonal`. -/
def tm_diagonal : Term sig_diagonal [] [] (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat)) :=
  Term.fix [Ty.nat, Ty.nat] 2 (.cons (natAdd (♯0) (♯1)) (.cons (♯0) .nil)) bd_diagonal (Term.natL 0)

/-- The module up to and including `diagonal`. -/
def prog_diagonal : Program (d_diagonal :: sig_diagonal.decls) :=
  .cons d_diagonal sig_diagonal.h_names_unique tm_diagonal prog_ackRev

/-- `hyper`, as a declaration of the module. -/
def d_hyper : GlobalDecl := ⟨"hyper", (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat)))⟩

/-- The signature `hyper` is written against. -/
def sig_hyper : Sig := ⟨[d_diagonal, d_ackRev], by decide⟩

/-- The body of the recursion of `hyper`. -/
def bd_hyper : Term sig_hyper ([Ty.nat, Ty.nat, Ty.nat] ++ []) [⟨[Ty.nat, Ty.nat, Ty.nat], Ty.nat⟩] Ty.nat :=
  (Term.ite (natEq (♯0) (Term.natL 0)) (Term.letE (Term.natL 1) (Term.letE (natAdd (♯3) (♯0)) (♯0))) (Term.ite (natEq (natSub (♯0) (Term.natL 1)) (Term.natL 0)) (Term.ite (natEq (♯2) (Term.natL 0)) (♯1) (Term.letE (Term.natL 1) (Term.letE (natAdd (natSub (♯1) (Term.natL 1)) (♯0)) (Term.letE (Term.selfCall .head (.cons (♯0) (.cons (♯3) (.cons (natSub (♯4) (Term.natL 1)) .nil)))) (Term.letE (Term.selfCall .head (.cons (natSub (♯3) (Term.natL 1)) (.cons (♯4) (.cons (♯0) .nil)))) (♯0)))))) (Term.ite (natEq (natSub (natSub (♯0) (Term.natL 1)) (Term.natL 1)) (Term.natL 0)) (Term.ite (natEq (♯2) (Term.natL 0)) (Term.letE (Term.natL 0) (♯0)) (Term.letE (Term.natL 1) (Term.letE (natAdd (natSub (♯1) (Term.natL 1)) (♯0)) (Term.letE (Term.selfCall .head (.cons (♯0) (.cons (♯3) (.cons (natSub (♯4) (Term.natL 1)) .nil)))) (Term.letE (Term.selfCall .head (.cons (natSub (♯3) (Term.natL 1)) (.cons (♯4) (.cons (♯0) .nil)))) (♯0)))))) (Term.ite (natEq (♯2) (Term.natL 0)) (Term.letE (Term.natL 1) (♯0)) (Term.letE (Term.natL 1) (Term.letE (natAdd (natSub (♯1) (Term.natL 1)) (♯0)) (Term.letE (Term.selfCall .head (.cons (♯0) (.cons (♯3) (.cons (natSub (♯4) (Term.natL 1)) .nil)))) (Term.letE (Term.selfCall .head (.cons (natSub (♯3) (Term.natL 1)) (.cons (♯4) (.cons (♯0) .nil)))) (♯0)))))))))

/-- The body of `hyper`. -/
def tm_hyper : Term sig_hyper [] [] (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat))) :=
  Term.fix [Ty.nat, Ty.nat, Ty.nat] 2 (.cons (♯0) (.cons (♯2) .nil)) bd_hyper (Term.natL 0)

/-- The module up to and including `hyper`. -/
def prog_hyper : Program (d_hyper :: sig_hyper.decls) :=
  .cons d_hyper sig_hyper.h_names_unique tm_hyper prog_diagonal

/-- `Mc91.M`, as a declaration of the module. -/
def d_Mc91_M : GlobalDecl := ⟨"Mc91.M", (Ty.fn Ty.nat Ty.nat)⟩

/-- The signature `Mc91.M` is written against. -/
def sig_Mc91_M : Sig := ⟨[d_hyper, d_diagonal, d_ackRev], by decide⟩

/-- The body of the recursion of `Mc91.M`. -/
def bd_Mc91_M : Term sig_Mc91_M ([Ty.nat] ++ []) [⟨[Ty.nat], Ty.nat⟩] Ty.nat :=
  (Term.letE (Term.natL 100) (Term.letE (natLt (♯0) (♯1)) (Term.ite (♯0) (Term.letE (Term.natL 10) (Term.letE (natSub (♯3) (♯0)) (Term.letE (♯0) (♯0)))) (Term.letE (Term.natL 11) (Term.letE (natAdd (♯3) (♯0)) (Term.letE (Term.selfCall .head (.cons (♯0) .nil)) (Term.letE (♯0) (Term.letE (Term.selfCall .head (.cons (♯0) .nil)) (Term.letE (♯0) (Term.letE (♯0) (♯0)))))))))))

/-- The body of `Mc91.M`. -/
def tm_Mc91_M : Term sig_Mc91_M [] [] (Ty.fn Ty.nat Ty.nat) :=
  Term.fix [Ty.nat] 1 (.cons (natSub (Term.natL 101) (♯0)) .nil) bd_Mc91_M (Term.natL 0)

/-- The module up to and including `Mc91.M`. -/
def prog_Mc91_M : Program (d_Mc91_M :: sig_Mc91_M.decls) :=
  .cons d_Mc91_M sig_Mc91_M.h_names_unique tm_Mc91_M prog_hyper

/-- `Mc91`, as a declaration of the module. -/
def d_Mc91 : GlobalDecl := ⟨"Mc91", (Ty.fn Ty.nat Ty.nat)⟩

/-- The signature `Mc91` is written against. -/
def sig_Mc91 : Sig := ⟨[d_Mc91_M, d_hyper, d_diagonal, d_ackRev], by decide⟩

/-- The body of `Mc91`. -/
def tm_Mc91 : Term sig_Mc91 [] [] (Ty.fn Ty.nat Ty.nat) :=
  (Term.lam (Term.letE (Term.ap (Term.global .here) (♯0)) (Term.letE (♯0) (♯0))))

/-- The module up to and including `Mc91`. -/
def prog_Mc91 : Program (d_Mc91 :: sig_Mc91.decls) :=
  .cons d_Mc91 sig_Mc91.h_names_unique tm_Mc91 prog_Mc91_M

/-- The signature of the whole module. -/
def moduleSig : Sig := ⟨[d_Mc91, d_Mc91_M, d_hyper, d_diagonal, d_ackRev], by decide⟩

/-- The module as a telescope: every body is written against the declarations before it, so the call graph is acyclic by construction.  It is built one declaration at a time, above, so that no single elaboration sees the whole telescope at once. -/
def program : Program moduleSig.decls :=
  prog_Mc91

end ProgramSnapshotsMyTco09
