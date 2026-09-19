-- SnapshotsMy.MutualTail: the module as a Program of the one grammar of `LakeJs.Expr`.
-- 🎯 a public entry point of the module; 📦 a declaration the translation pulled in.
-- Every term below is a `Term`, so it is terminating by construction: the one way it
-- repeats work is `Term.fix`, whose measure it descends on at every self call.
--
-- ════ 📦 test1 & test2 (clique) : (fn nat (fn nat (fn nat bool)))
--      measure: mutual clique of 2 members; 2 components: [ if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then ♯1 else ♯2, ((extern⟨nat nat ⇒ nat⟩ ⬝ 1#) ⬝ ♯0) ] — the measure of the member the tag selects, then its phase
-- fix (nat nat nat) measure [ if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then ♯1 else ♯2, ((extern⟨nat nat ⇒ nat⟩ ⬝ 1#) ⬝ ♯0) ] body {
--   if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯1) ⬝ 0#) then let ♯ := true;
--   ♯0 else let ♯ := self0⟨↓⟩(1#, 0#, ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯1) ⬝ 1#));
--   ♯0 else if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯2) ⬝ 0#) then let ♯ := false;
--   ♯0 else let ♯ := self0⟨↓⟩(0#, ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ 1#), 0#);
--   ♯0
-- } stuck { false }
--
-- ════ 📦 test3 & test4 & test5 (clique) : (fn nat (fn nat (fn nat (fn nat (fn nat (fn nat (fn nat (fn nat nat))))))))
--      measure: mutual clique of 3 members; 2 components: [ if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then ♯1 else if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 1#) then ♯3 else ♯6, ((extern⟨nat nat ⇒ nat⟩ ⬝ 2#) ⬝ ♯0) ] — the measure of the member the tag selects, then its phase
-- fix (nat nat nat nat nat nat nat nat) measure [ if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then ♯1 else if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 1#) then ♯3 else ♯6, ((extern⟨nat nat ⇒ nat⟩ ⬝ 2#) ⬝ ♯0) ] body {
--   if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯1) ⬝ 0#) then ♯2 else let ♯ := 1#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯3) ⬝ ♯0);
--   let ♯ := 2#;
--   let ♯ := self0⟨↓⟩(1#, 0#, 0#, ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯4) ⬝ 1#), ♯1, ♯0, 0#, 0#);
--   ♯0 else if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 1#) then if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯3) ⬝ 0#) then ♯4 else let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯4) ⬝ ♯5);
--   let ♯ := self0⟨↓⟩(2#, 0#, 0#, 0#, 0#, 0#, ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯4) ⬝ 1#), ♯0);
--   ♯0 else if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯6) ⬝ 0#) then ♯7 else let ♯ := 3#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯8) ⬝ ♯0);
--   let ♯ := self0⟨↓⟩(0#, ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯8) ⬝ 1#), ♯0, 0#, 0#, 0#, 0#, 0#);
--   ♯0
-- } stuck { 0# }
--
-- ════ 🎯 test1 : (fn nat bool)
-- ƛ (((@test1 & test2 (clique) ⬝ 0#) ⬝ ♯0) ⬝ 0#)
--
-- ════ 🎯 test2 : (fn nat bool)
-- ƛ (((@test1 & test2 (clique) ⬝ 1#) ⬝ 0#) ⬝ ♯0)
--
-- ════ 🎯 test3 : (fn nat (fn nat nat))
-- ƛ ƛ ((((((((@test3 & test4 & test5 (clique) ⬝ 0#) ⬝ ♯1) ⬝ ♯0) ⬝ 0#) ⬝ 0#) ⬝ 0#) ⬝ 0#) ⬝ 0#)
--
-- ════ 🎯 test4 : (fn nat (fn nat (fn nat nat)))
-- ƛ ƛ ƛ ((((((((@test3 & test4 & test5 (clique) ⬝ 1#) ⬝ 0#) ⬝ 0#) ⬝ ♯2) ⬝ ♯1) ⬝ ♯0) ⬝ 0#) ⬝ 0#)
--
-- ════ 🎯 test5 : (fn nat (fn nat nat))
-- ƛ ƛ ((((((((@test3 & test4 & test5 (clique) ⬝ 2#) ⬝ 0#) ⬝ 0#) ⬝ 0#) ⬝ 0#) ⬝ 0#) ⬝ ♯1) ⬝ ♯0)
--
--
-- ── the same program as Lean source ────────────────────────────────────
-- The trees above are this program printed in the notation of `LakeJs.ExprPretty`;
-- copy one into a `[LEAN|...]` elaboration if you want to read it there.

import LakeJs

open LakeJs LakeJs.Ty LakeJs.Expr LakeJs.Expr.Ops

namespace ProgramSnapshotsMyMutualTail

/-- `test1 & test2 (clique)`, as a declaration of the module. -/
def d_test1___test2__clique_ : GlobalDecl := ⟨"test1 & test2 (clique)", (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.bool)))⟩

/-- The signature `test1 & test2 (clique)` is written against. -/
def sig_test1___test2__clique_ : Sig := ⟨[], by decide⟩

/-- The body of the recursion of `test1 & test2 (clique)`. -/
def bd_test1___test2__clique_ : Term sig_test1___test2__clique_ ([Ty.nat, Ty.nat, Ty.nat] ++ []) [⟨[Ty.nat, Ty.nat, Ty.nat], Ty.bool⟩] Ty.bool :=
  (Term.ite (natEq (♯0) (Term.natL 0)) (Term.ite (natEq (♯1) (Term.natL 0)) (Term.letE (Term.boolL true) (♯0)) (Term.letE (Term.selfCall .head (.cons (Term.natL 1) (.cons (Term.natL 0) (.cons (natSub (♯1) (Term.natL 1)) .nil)))) (♯0))) (Term.ite (natEq (♯2) (Term.natL 0)) (Term.letE (Term.boolL false) (♯0)) (Term.letE (Term.selfCall .head (.cons (Term.natL 0) (.cons (natSub (♯2) (Term.natL 1)) (.cons (Term.natL 0) .nil)))) (♯0))))

/-- The body of `test1 & test2 (clique)`. -/
def tm_test1___test2__clique_ : Term sig_test1___test2__clique_ [] [] (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.bool))) :=
  Term.fix [Ty.nat, Ty.nat, Ty.nat] 2 (.cons (Term.ite (natEq (♯0) (Term.natL 0)) (♯1) (♯2)) (.cons (natSub (Term.natL 1) (♯0)) .nil)) bd_test1___test2__clique_ (Term.boolL false)

/-- The module up to and including `test1 & test2 (clique)`. -/
def prog_test1___test2__clique_ : Program (d_test1___test2__clique_ :: sig_test1___test2__clique_.decls) :=
  .cons d_test1___test2__clique_ sig_test1___test2__clique_.h_names_unique tm_test1___test2__clique_ Program.nil

/-- `test3 & test4 & test5 (clique)`, as a declaration of the module. -/
def d_test3___test4___test5__clique_ : GlobalDecl := ⟨"test3 & test4 & test5 (clique)", (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat))))))))⟩

/-- The signature `test3 & test4 & test5 (clique)` is written against. -/
def sig_test3___test4___test5__clique_ : Sig := ⟨[d_test1___test2__clique_], by decide⟩

/-- The body of the recursion of `test3 & test4 & test5 (clique)`. -/
def bd_test3___test4___test5__clique_ : Term sig_test3___test4___test5__clique_ ([Ty.nat, Ty.nat, Ty.nat, Ty.nat, Ty.nat, Ty.nat, Ty.nat, Ty.nat] ++ []) [⟨[Ty.nat, Ty.nat, Ty.nat, Ty.nat, Ty.nat, Ty.nat, Ty.nat, Ty.nat], Ty.nat⟩] Ty.nat :=
  (Term.ite (natEq (♯0) (Term.natL 0)) (Term.ite (natEq (♯1) (Term.natL 0)) (♯2) (Term.letE (Term.natL 1) (Term.letE (natAdd (♯3) (♯0)) (Term.letE (Term.natL 2) (Term.letE (Term.selfCall .head (.cons (Term.natL 1) (.cons (Term.natL 0) (.cons (Term.natL 0) (.cons (natSub (♯4) (Term.natL 1)) (.cons (♯1) (.cons (♯0) (.cons (Term.natL 0) (.cons (Term.natL 0) .nil))))))))) (♯0)))))) (Term.ite (natEq (♯0) (Term.natL 1)) (Term.ite (natEq (♯3) (Term.natL 0)) (♯4) (Term.letE (natAdd (♯4) (♯5)) (Term.letE (Term.selfCall .head (.cons (Term.natL 2) (.cons (Term.natL 0) (.cons (Term.natL 0) (.cons (Term.natL 0) (.cons (Term.natL 0) (.cons (Term.natL 0) (.cons (natSub (♯4) (Term.natL 1)) (.cons (♯0) .nil))))))))) (♯0)))) (Term.ite (natEq (♯6) (Term.natL 0)) (♯7) (Term.letE (Term.natL 3) (Term.letE (natAdd (♯8) (♯0)) (Term.letE (Term.selfCall .head (.cons (Term.natL 0) (.cons (natSub (♯8) (Term.natL 1)) (.cons (♯0) (.cons (Term.natL 0) (.cons (Term.natL 0) (.cons (Term.natL 0) (.cons (Term.natL 0) (.cons (Term.natL 0) .nil))))))))) (♯0)))))))

/-- The body of `test3 & test4 & test5 (clique)`. -/
def tm_test3___test4___test5__clique_ : Term sig_test3___test4___test5__clique_ [] [] (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat)))))))) :=
  Term.fix [Ty.nat, Ty.nat, Ty.nat, Ty.nat, Ty.nat, Ty.nat, Ty.nat, Ty.nat] 2 (.cons (Term.ite (natEq (♯0) (Term.natL 0)) (♯1) (Term.ite (natEq (♯0) (Term.natL 1)) (♯3) (♯6))) (.cons (natSub (Term.natL 2) (♯0)) .nil)) bd_test3___test4___test5__clique_ (Term.natL 0)

/-- The module up to and including `test3 & test4 & test5 (clique)`. -/
def prog_test3___test4___test5__clique_ : Program (d_test3___test4___test5__clique_ :: sig_test3___test4___test5__clique_.decls) :=
  .cons d_test3___test4___test5__clique_ sig_test3___test4___test5__clique_.h_names_unique tm_test3___test4___test5__clique_ prog_test1___test2__clique_

/-- `test1`, as a declaration of the module. -/
def d_test1 : GlobalDecl := ⟨"test1", (Ty.fn Ty.nat Ty.bool)⟩

/-- The signature `test1` is written against. -/
def sig_test1 : Sig := ⟨[d_test3___test4___test5__clique_, d_test1___test2__clique_], by decide⟩

/-- The body of `test1`. -/
def tm_test1 : Term sig_test1 [] [] (Ty.fn Ty.nat Ty.bool) :=
  (Term.lam (Term.ap (Term.ap (Term.ap (Term.global (.there .here)) (Term.natL 0)) (♯0)) (Term.natL 0)))

/-- The module up to and including `test1`. -/
def prog_test1 : Program (d_test1 :: sig_test1.decls) :=
  .cons d_test1 sig_test1.h_names_unique tm_test1 prog_test3___test4___test5__clique_

/-- `test2`, as a declaration of the module. -/
def d_test2 : GlobalDecl := ⟨"test2", (Ty.fn Ty.nat Ty.bool)⟩

/-- The signature `test2` is written against. -/
def sig_test2 : Sig := ⟨[d_test1, d_test3___test4___test5__clique_, d_test1___test2__clique_], by decide⟩

/-- The body of `test2`. -/
def tm_test2 : Term sig_test2 [] [] (Ty.fn Ty.nat Ty.bool) :=
  (Term.lam (Term.ap (Term.ap (Term.ap (Term.global (.there (.there .here))) (Term.natL 1)) (Term.natL 0)) (♯0)))

/-- The module up to and including `test2`. -/
def prog_test2 : Program (d_test2 :: sig_test2.decls) :=
  .cons d_test2 sig_test2.h_names_unique tm_test2 prog_test1

/-- `test3`, as a declaration of the module. -/
def d_test3 : GlobalDecl := ⟨"test3", (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat))⟩

/-- The signature `test3` is written against. -/
def sig_test3 : Sig := ⟨[d_test2, d_test1, d_test3___test4___test5__clique_, d_test1___test2__clique_], by decide⟩

/-- The body of `test3`. -/
def tm_test3 : Term sig_test3 [] [] (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat)) :=
  (Term.lam (Term.lam (Term.ap (Term.ap (Term.ap (Term.ap (Term.ap (Term.ap (Term.ap (Term.ap (Term.global (.there (.there .here))) (Term.natL 0)) (♯1)) (♯0)) (Term.natL 0)) (Term.natL 0)) (Term.natL 0)) (Term.natL 0)) (Term.natL 0))))

/-- The module up to and including `test3`. -/
def prog_test3 : Program (d_test3 :: sig_test3.decls) :=
  .cons d_test3 sig_test3.h_names_unique tm_test3 prog_test2

/-- `test4`, as a declaration of the module. -/
def d_test4 : GlobalDecl := ⟨"test4", (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat)))⟩

/-- The signature `test4` is written against. -/
def sig_test4 : Sig := ⟨[d_test3, d_test2, d_test1, d_test3___test4___test5__clique_, d_test1___test2__clique_], by decide⟩

/-- The body of `test4`. -/
def tm_test4 : Term sig_test4 [] [] (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat))) :=
  (Term.lam (Term.lam (Term.lam (Term.ap (Term.ap (Term.ap (Term.ap (Term.ap (Term.ap (Term.ap (Term.ap (Term.global (.there (.there (.there .here)))) (Term.natL 1)) (Term.natL 0)) (Term.natL 0)) (♯2)) (♯1)) (♯0)) (Term.natL 0)) (Term.natL 0)))))

/-- The module up to and including `test4`. -/
def prog_test4 : Program (d_test4 :: sig_test4.decls) :=
  .cons d_test4 sig_test4.h_names_unique tm_test4 prog_test3

/-- `test5`, as a declaration of the module. -/
def d_test5 : GlobalDecl := ⟨"test5", (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat))⟩

/-- The signature `test5` is written against. -/
def sig_test5 : Sig := ⟨[d_test4, d_test3, d_test2, d_test1, d_test3___test4___test5__clique_, d_test1___test2__clique_], by decide⟩

/-- The body of `test5`. -/
def tm_test5 : Term sig_test5 [] [] (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat)) :=
  (Term.lam (Term.lam (Term.ap (Term.ap (Term.ap (Term.ap (Term.ap (Term.ap (Term.ap (Term.ap (Term.global (.there (.there (.there (.there .here))))) (Term.natL 2)) (Term.natL 0)) (Term.natL 0)) (Term.natL 0)) (Term.natL 0)) (Term.natL 0)) (♯1)) (♯0))))

/-- The module up to and including `test5`. -/
def prog_test5 : Program (d_test5 :: sig_test5.decls) :=
  .cons d_test5 sig_test5.h_names_unique tm_test5 prog_test4

/-- The signature of the whole module. -/
def moduleSig : Sig := ⟨[d_test5, d_test4, d_test3, d_test2, d_test1, d_test3___test4___test5__clique_, d_test1___test2__clique_], by decide⟩

/-- The module as a telescope: every body is written against the declarations before it, so the call graph is acyclic by construction.  It is built one declaration at a time, above, so that no single elaboration sees the whole telescope at once. -/
def program : Program moduleSig.decls :=
  prog_test5

end ProgramSnapshotsMyMutualTail
