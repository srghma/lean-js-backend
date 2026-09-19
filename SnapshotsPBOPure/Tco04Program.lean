-- SnapshotsPBOPure.Tco04: the module as a Program of the one grammar of `LakeJs.Expr`.
-- 🎯 a public entry point of the module; 📦 a declaration the translation pulled in.
-- Every term below is a `Term`, so it is terminating by construction: the one way it
-- repeats work is `Term.fix`, whose measure it descends on at every self call.
--
-- ════ 📦 test1 & test2 (clique) : (fn nat (fn int (fn int int)))
--      measure: mutual clique of 2 members; 2 components: [ if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then (extern⟨int ⇒ nat⟩ ⬝ ♯1) else (extern⟨int ⇒ nat⟩ ⬝ ♯2), ((extern⟨nat nat ⇒ nat⟩ ⬝ 1#) ⬝ ♯0) ] — the measure of the member the tag selects, then its phase
-- fix (nat int int) measure [ if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then (extern⟨int ⇒ nat⟩ ⬝ ♯1) else (extern⟨int ⇒ nat⟩ ⬝ ♯2), ((extern⟨nat nat ⇒ nat⟩ ⬝ 1#) ⬝ ♯0) ] body {
--   if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then let ♯ := 1#;
--   let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--   let ♯ := ((extern⟨int int ⇒ bool⟩ ⬝ ♯3) ⬝ ♯0);
--   if ♯0 then ♯4 else let ♯ := ((extern⟨int int ⇒ int⟩ ⬝ ♯4) ⬝ ♯1);
--   let ♯ := self0⟨↓⟩(1#, 0i, ♯0);
--   ♯0 else let ♯ := 2#;
--   let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--   let ♯ := ((extern⟨int int ⇒ bool⟩ ⬝ ♯4) ⬝ ♯0);
--   if ♯0 then ♯5 else let ♯ := ((extern⟨int int ⇒ int⟩ ⬝ ♯5) ⬝ ♯1);
--   let ♯ := self0⟨↓⟩(0#, ♯0, 0i);
--   ♯0
-- } stuck { 0i }
--
-- ════ 🎯 test1 : (fn int int)
-- ƛ (((@test1 & test2 (clique) ⬝ 0#) ⬝ ♯0) ⬝ 0i)
--
-- ════ 🎯 test2 : (fn int int)
-- ƛ (((@test1 & test2 (clique) ⬝ 1#) ⬝ 0i) ⬝ ♯0)
--
--
-- ── the same program as Lean source ────────────────────────────────────
-- The trees above are this program printed in the notation of `LakeJs.ExprPretty`;
-- copy one into a `[LEAN|...]` elaboration if you want to read it there.

import LakeJs

open LakeJs LakeJs.Ty LakeJs.Expr LakeJs.Expr.Ops

namespace ProgramSnapshotsPBOPureTco04

/-- `test1 & test2 (clique)`, as a declaration of the module. -/
def d_test1___test2__clique_ : GlobalDecl := ⟨"test1 & test2 (clique)", (Ty.fn Ty.nat (Ty.fn Ty.int (Ty.fn Ty.int Ty.int)))⟩

/-- The signature `test1 & test2 (clique)` is written against. -/
def sig_test1___test2__clique_ : Sig := ⟨[], by decide⟩

/-- The body of the recursion of `test1 & test2 (clique)`. -/
def bd_test1___test2__clique_ : Term sig_test1___test2__clique_ ([Ty.nat, Ty.int, Ty.int] ++ []) [⟨[Ty.nat, Ty.int, Ty.int], Ty.int⟩] Ty.int :=
  (Term.ite (natEq (♯0) (Term.natL 0)) (Term.letE (Term.natL 1) (Term.letE (natToInt (♯0)) (Term.letE (intEq (♯3) (♯0)) (Term.ite (♯0) (♯4) (Term.letE (intSub (♯4) (♯1)) (Term.letE (Term.selfCall .head (.cons (Term.natL 1) (.cons (Term.intL (0)) (.cons (♯0) .nil)))) (♯0))))))) (Term.letE (Term.natL 2) (Term.letE (natToInt (♯0)) (Term.letE (intEq (♯4) (♯0)) (Term.ite (♯0) (♯5) (Term.letE (intSub (♯5) (♯1)) (Term.letE (Term.selfCall .head (.cons (Term.natL 0) (.cons (♯0) (.cons (Term.intL (0)) .nil)))) (♯0))))))))

/-- The body of `test1 & test2 (clique)`. -/
def tm_test1___test2__clique_ : Term sig_test1___test2__clique_ [] [] (Ty.fn Ty.nat (Ty.fn Ty.int (Ty.fn Ty.int Ty.int))) :=
  Term.fix [Ty.nat, Ty.int, Ty.int] 2 (.cons (Term.ite (natEq (♯0) (Term.natL 0)) (intToNat (♯1)) (intToNat (♯2))) (.cons (natSub (Term.natL 1) (♯0)) .nil)) bd_test1___test2__clique_ (Term.intL (0))

/-- The module up to and including `test1 & test2 (clique)`. -/
def prog_test1___test2__clique_ : Program (d_test1___test2__clique_ :: sig_test1___test2__clique_.decls) :=
  .cons d_test1___test2__clique_ sig_test1___test2__clique_.h_names_unique tm_test1___test2__clique_ Program.nil

/-- `test1`, as a declaration of the module. -/
def d_test1 : GlobalDecl := ⟨"test1", (Ty.fn Ty.int Ty.int)⟩

/-- The signature `test1` is written against. -/
def sig_test1 : Sig := ⟨[d_test1___test2__clique_], by decide⟩

/-- The body of `test1`. -/
def tm_test1 : Term sig_test1 [] [] (Ty.fn Ty.int Ty.int) :=
  (Term.lam (Term.ap (Term.ap (Term.ap (Term.global .here) (Term.natL 0)) (♯0)) (Term.intL (0))))

/-- The module up to and including `test1`. -/
def prog_test1 : Program (d_test1 :: sig_test1.decls) :=
  .cons d_test1 sig_test1.h_names_unique tm_test1 prog_test1___test2__clique_

/-- `test2`, as a declaration of the module. -/
def d_test2 : GlobalDecl := ⟨"test2", (Ty.fn Ty.int Ty.int)⟩

/-- The signature `test2` is written against. -/
def sig_test2 : Sig := ⟨[d_test1, d_test1___test2__clique_], by decide⟩

/-- The body of `test2`. -/
def tm_test2 : Term sig_test2 [] [] (Ty.fn Ty.int Ty.int) :=
  (Term.lam (Term.ap (Term.ap (Term.ap (Term.global (.there .here)) (Term.natL 1)) (Term.intL (0))) (♯0)))

/-- The module up to and including `test2`. -/
def prog_test2 : Program (d_test2 :: sig_test2.decls) :=
  .cons d_test2 sig_test2.h_names_unique tm_test2 prog_test1

/-- The signature of the whole module. -/
def moduleSig : Sig := ⟨[d_test2, d_test1, d_test1___test2__clique_], by decide⟩

/-- The module as a telescope: every body is written against the declarations before it, so the call graph is acyclic by construction.  It is built one declaration at a time, above, so that no single elaboration sees the whole telescope at once. -/
def program : Program moduleSig.decls :=
  prog_test2

end ProgramSnapshotsPBOPureTco04
