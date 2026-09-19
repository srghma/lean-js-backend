-- SnapshotsPBOPure.CaptureDerefRegression01: the module as a Program of the one grammar of `LakeJs.Expr`.
-- 🎯 a public entry point of the module; 📦 a declaration the translation pulled in.
-- Every term below is a `Term`, so it is terminating by construction: the one way it
-- repeats work is `Term.fix`, whose measure it descends on at every self call.
--
-- ════ 🎯 test1 : (fn (record int int) (fn int int))
-- ƛ ƛ let ♯ := proj0.0(♯1);
-- let ♯ := ((extern⟨int int ⇒ int⟩ ⬝ ♯0) ⬝ ♯1);
-- ♯0
--
-- ════ 🎯 test2 : (fn (record int int) (fn int int))
-- ƛ ƛ let ♯ := proj0.0(♯1);
-- let ♯ := ((extern⟨int int ⇒ int⟩ ⬝ ♯0) ⬝ ♯1);
-- ♯0
--
-- ════ 🎯 test3 : (fn (record int int) (fn int int))
-- ƛ let ♯ := ƛ let ♯ := proj0.0(♯1);
-- let ♯ := ((extern⟨int int ⇒ int⟩ ⬝ ♯0) ⬝ ♯1);
-- ♯0;
-- let ♯ := ♯0;
-- ♯0
--
-- ════ 🎯 test4 : (fn (record int int) (record (fn int int) (fn int int)))
-- ƛ let ♯ := ƛ let ♯ := proj0.0(♯1);
-- let ♯ := ((extern⟨int int ⇒ int⟩ ⬝ ♯0) ⬝ ♯1);
-- ♯0;
-- let ♯ := ƛ let ♯ := proj0.1(♯2);
-- let ♯ := ((extern⟨int int ⇒ int⟩ ⬝ ♯0) ⬝ ♯1);
-- ♯0;
-- let ♯ := ctor0((fn int int) (fn int int))(♯1, ♯0);
-- ♯0
--
-- ════ 🎯 test5 : (fn (record int int) (record (fn int int) (fn int int)))
-- ƛ let ♯ := ƛ let ♯ := proj0.0(♯1);
-- let ♯ := ((extern⟨int int ⇒ int⟩ ⬝ ♯0) ⬝ ♯1);
-- ♯0;
-- let ♯ := ƛ let ♯ := proj0.1(♯2);
-- let ♯ := ((extern⟨int int ⇒ int⟩ ⬝ ♯0) ⬝ ♯1);
-- ♯0;
-- let ♯ := ctor0((fn int int) (fn int int))(♯1, ♯0);
-- ♯0
--
-- ════ 📦 testEven & testOdd (clique) : (fn nat (fn nat (fn (record int int) (fn nat (fn (record int int) (record int int))))))
--      measure: mutual clique of 2 members; 2 components: [ if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then ♯1 else ♯3, ((extern⟨nat nat ⇒ nat⟩ ⬝ 1#) ⬝ ♯0) ] — the measure of the member the tag selects, then its phase
-- fix (nat nat (record int int) nat (record int int)) measure [ if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then ♯1 else ♯3, ((extern⟨nat nat ⇒ nat⟩ ⬝ 1#) ⬝ ♯0) ] body {
--   if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯1) ⬝ 0#) then ♯2 else case ♯2 of
--     | 0(int int) => let ♯ := 1#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := ((extern⟨int int ⇒ int⟩ ⬝ ♯3) ⬝ ♯0);
--       let ♯ := 2#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := ((extern⟨int int ⇒ int⟩ ⬝ ♯5) ⬝ ♯0);
--       let ♯ := ctor0(int int)(♯3, ♯0);
--       let ♯ := self0⟨↓⟩(1#, 0#, ctor0(int int)(0i, 0i), ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯10) ⬝ 1#), ♯0);
--       ♯0
--  else if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯3) ⬝ 0#) then ♯4 else case ♯4 of
--     | 0(int int) => let ♯ := 3#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := ((extern⟨int int ⇒ int⟩ ⬝ ♯3) ⬝ ♯0);
--       let ♯ := 4#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := ((extern⟨int int ⇒ int⟩ ⬝ ♯5) ⬝ ♯0);
--       let ♯ := ctor0(int int)(♯3, ♯0);
--       let ♯ := self0⟨↓⟩(0#, ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯12) ⬝ 1#), ♯0, 0#, ctor0(int int)(0i, 0i));
--       ♯0
--
-- } stuck { ctor0(int int)(0i, 0i) }
--
-- ════ 🎯 testEven : (fn nat (fn (record int int) (record int int)))
-- ƛ ƛ (((((@testEven & testOdd (clique) ⬝ 0#) ⬝ ♯1) ⬝ ♯0) ⬝ 0#) ⬝ ctor0(int int)(0i, 0i))
--
-- ════ 🎯 testOdd : (fn nat (fn (record int int) (record int int)))
-- ƛ ƛ (((((@testEven & testOdd (clique) ⬝ 1#) ⬝ 0#) ⬝ ctor0(int int)(0i, 0i)) ⬝ ♯1) ⬝ ♯0)
--
--
-- ── the same program as Lean source ────────────────────────────────────
-- The trees above are this program printed in the notation of `LakeJs.ExprPretty`;
-- copy one into a `[LEAN|...]` elaboration if you want to read it there.

import LakeJs

open LakeJs LakeJs.Ty LakeJs.Expr LakeJs.Expr.Ops

namespace ProgramSnapshotsPBOPureCaptureDerefRegression01

/-- `test1`, as a declaration of the module. -/
def d_test1 : GlobalDecl := ⟨"test1", (Ty.fn (Ty.prod Ty.int Ty.int) (Ty.fn Ty.int Ty.int))⟩

/-- The signature `test1` is written against. -/
def sig_test1 : Sig := ⟨[], by decide⟩

/-- The body of `test1`. -/
def tm_test1 : Term sig_test1 [] [] (Ty.fn (Ty.prod Ty.int Ty.int) (Ty.fn Ty.int Ty.int)) :=
  (Term.lam (Term.lam (Term.letE (Term.proj (♯1) 0 0 (by rfl) (by rfl)) (Term.letE (intAdd (♯0) (♯1)) (♯0)))))

/-- The module up to and including `test1`. -/
def prog_test1 : Program (d_test1 :: sig_test1.decls) :=
  .cons d_test1 sig_test1.h_names_unique tm_test1 Program.nil

/-- `test2`, as a declaration of the module. -/
def d_test2 : GlobalDecl := ⟨"test2", (Ty.fn (Ty.prod Ty.int Ty.int) (Ty.fn Ty.int Ty.int))⟩

/-- The signature `test2` is written against. -/
def sig_test2 : Sig := ⟨[d_test1], by decide⟩

/-- The body of `test2`. -/
def tm_test2 : Term sig_test2 [] [] (Ty.fn (Ty.prod Ty.int Ty.int) (Ty.fn Ty.int Ty.int)) :=
  (Term.lam (Term.lam (Term.letE (Term.proj (♯1) 0 0 (by rfl) (by rfl)) (Term.letE (intAdd (♯0) (♯1)) (♯0)))))

/-- The module up to and including `test2`. -/
def prog_test2 : Program (d_test2 :: sig_test2.decls) :=
  .cons d_test2 sig_test2.h_names_unique tm_test2 prog_test1

/-- `test3`, as a declaration of the module. -/
def d_test3 : GlobalDecl := ⟨"test3", (Ty.fn (Ty.prod Ty.int Ty.int) (Ty.fn Ty.int Ty.int))⟩

/-- The signature `test3` is written against. -/
def sig_test3 : Sig := ⟨[d_test2, d_test1], by decide⟩

/-- The body of `test3`. -/
def tm_test3 : Term sig_test3 [] [] (Ty.fn (Ty.prod Ty.int Ty.int) (Ty.fn Ty.int Ty.int)) :=
  (Term.lam (Term.letE (Term.lam (Term.letE (Term.proj (♯1) 0 0 (by rfl) (by rfl)) (Term.letE (intAdd (♯0) (♯1)) (♯0)))) (Term.letE (♯0) (♯0))))

/-- The module up to and including `test3`. -/
def prog_test3 : Program (d_test3 :: sig_test3.decls) :=
  .cons d_test3 sig_test3.h_names_unique tm_test3 prog_test2

/-- `test4`, as a declaration of the module. -/
def d_test4 : GlobalDecl := ⟨"test4", (Ty.fn (Ty.prod Ty.int Ty.int) (Ty.record ⟨(Ty.fn Ty.int Ty.int), (Ty.fn Ty.int Ty.int), []⟩))⟩

/-- The signature `test4` is written against. -/
def sig_test4 : Sig := ⟨[d_test3, d_test2, d_test1], by decide⟩

/-- The body of `test4`. -/
def tm_test4 : Term sig_test4 [] [] (Ty.fn (Ty.prod Ty.int Ty.int) (Ty.record ⟨(Ty.fn Ty.int Ty.int), (Ty.fn Ty.int Ty.int), []⟩)) :=
  (Term.lam (Term.letE (Term.lam (Term.letE (Term.proj (♯1) 0 0 (by rfl) (by rfl)) (Term.letE (intAdd (♯0) (♯1)) (♯0)))) (Term.letE (Term.lam (Term.letE (Term.proj (♯2) 0 1 (by rfl) (by rfl)) (Term.letE (intAdd (♯0) (♯1)) (♯0)))) (Term.letE (Term.ctor (τ := (Ty.record ⟨(Ty.fn Ty.int Ty.int), (Ty.fn Ty.int Ty.int), []⟩)) 0 [(Ty.fn Ty.int Ty.int), (Ty.fn Ty.int Ty.int)] (by rfl) (.cons (♯1) (.cons (♯0) .nil))) (♯0)))))

/-- The module up to and including `test4`. -/
def prog_test4 : Program (d_test4 :: sig_test4.decls) :=
  .cons d_test4 sig_test4.h_names_unique tm_test4 prog_test3

/-- `test5`, as a declaration of the module. -/
def d_test5 : GlobalDecl := ⟨"test5", (Ty.fn (Ty.record ⟨Ty.int, Ty.int, []⟩) (Ty.record ⟨(Ty.fn Ty.int Ty.int), (Ty.fn Ty.int Ty.int), []⟩))⟩

/-- The signature `test5` is written against. -/
def sig_test5 : Sig := ⟨[d_test4, d_test3, d_test2, d_test1], by decide⟩

/-- The body of `test5`. -/
def tm_test5 : Term sig_test5 [] [] (Ty.fn (Ty.record ⟨Ty.int, Ty.int, []⟩) (Ty.record ⟨(Ty.fn Ty.int Ty.int), (Ty.fn Ty.int Ty.int), []⟩)) :=
  (Term.lam (Term.letE (Term.lam (Term.letE (Term.proj (♯1) 0 0 (by rfl) (by rfl)) (Term.letE (intAdd (♯0) (♯1)) (♯0)))) (Term.letE (Term.lam (Term.letE (Term.proj (♯2) 0 1 (by rfl) (by rfl)) (Term.letE (intAdd (♯0) (♯1)) (♯0)))) (Term.letE (Term.ctor (τ := (Ty.record ⟨(Ty.fn Ty.int Ty.int), (Ty.fn Ty.int Ty.int), []⟩)) 0 [(Ty.fn Ty.int Ty.int), (Ty.fn Ty.int Ty.int)] (by rfl) (.cons (♯1) (.cons (♯0) .nil))) (♯0)))))

/-- The module up to and including `test5`. -/
def prog_test5 : Program (d_test5 :: sig_test5.decls) :=
  .cons d_test5 sig_test5.h_names_unique tm_test5 prog_test4

/-- `testEven & testOdd (clique)`, as a declaration of the module. -/
def d_testEven___testOdd__clique_ : GlobalDecl := ⟨"testEven & testOdd (clique)", (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn (Ty.record ⟨Ty.int, Ty.int, []⟩) (Ty.fn Ty.nat (Ty.fn (Ty.record ⟨Ty.int, Ty.int, []⟩) (Ty.record ⟨Ty.int, Ty.int, []⟩))))))⟩

/-- The signature `testEven & testOdd (clique)` is written against. -/
def sig_testEven___testOdd__clique_ : Sig := ⟨[d_test5, d_test4, d_test3, d_test2, d_test1], by decide⟩

/-- The body of the recursion of `testEven & testOdd (clique)`. -/
def bd_testEven___testOdd__clique_ : Term sig_testEven___testOdd__clique_ ([Ty.nat, Ty.nat, (Ty.record ⟨Ty.int, Ty.int, []⟩), Ty.nat, (Ty.record ⟨Ty.int, Ty.int, []⟩)] ++ []) [⟨[Ty.nat, Ty.nat, (Ty.record ⟨Ty.int, Ty.int, []⟩), Ty.nat, (Ty.record ⟨Ty.int, Ty.int, []⟩)], (Ty.record ⟨Ty.int, Ty.int, []⟩)⟩] (Ty.record ⟨Ty.int, Ty.int, []⟩) :=
  (Term.ite (natEq (♯0) (Term.natL 0)) (Term.ite (natEq (♯1) (Term.natL 0)) (♯2) (Term.caseTag (♯2) (Alts.cons 0 [Ty.int, Ty.int] (by rfl) (Term.letE (Term.natL 1) (Term.letE (natToInt (♯0)) (Term.letE (intAdd (♯3) (♯0)) (Term.letE (Term.natL 2) (Term.letE (natToInt (♯0)) (Term.letE (intAdd (♯5) (♯0)) (Term.letE (Term.ctor (τ := (Ty.record ⟨Ty.int, Ty.int, []⟩)) 0 [Ty.int, Ty.int] (by rfl) (.cons (♯3) (.cons (♯0) .nil))) (Term.letE (Term.selfCall .head (.cons (Term.natL 1) (.cons (Term.natL 0) (.cons (Term.ctor (τ := (Ty.record ⟨Ty.int, Ty.int, []⟩)) 0 [Ty.int, Ty.int] (by rfl) (.cons (Term.intL (0)) (.cons (Term.intL (0)) .nil))) (.cons (natSub (♯10) (Term.natL 1)) (.cons (♯0) .nil)))))) (♯0))))))))) Alts.nilFull) (by rfl))) (Term.ite (natEq (♯3) (Term.natL 0)) (♯4) (Term.caseTag (♯4) (Alts.cons 0 [Ty.int, Ty.int] (by rfl) (Term.letE (Term.natL 3) (Term.letE (natToInt (♯0)) (Term.letE (intAdd (♯3) (♯0)) (Term.letE (Term.natL 4) (Term.letE (natToInt (♯0)) (Term.letE (intAdd (♯5) (♯0)) (Term.letE (Term.ctor (τ := (Ty.record ⟨Ty.int, Ty.int, []⟩)) 0 [Ty.int, Ty.int] (by rfl) (.cons (♯3) (.cons (♯0) .nil))) (Term.letE (Term.selfCall .head (.cons (Term.natL 0) (.cons (natSub (♯12) (Term.natL 1)) (.cons (♯0) (.cons (Term.natL 0) (.cons (Term.ctor (τ := (Ty.record ⟨Ty.int, Ty.int, []⟩)) 0 [Ty.int, Ty.int] (by rfl) (.cons (Term.intL (0)) (.cons (Term.intL (0)) .nil))) .nil)))))) (♯0))))))))) Alts.nilFull) (by rfl))))

/-- The body of `testEven & testOdd (clique)`. -/
def tm_testEven___testOdd__clique_ : Term sig_testEven___testOdd__clique_ [] [] (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn (Ty.record ⟨Ty.int, Ty.int, []⟩) (Ty.fn Ty.nat (Ty.fn (Ty.record ⟨Ty.int, Ty.int, []⟩) (Ty.record ⟨Ty.int, Ty.int, []⟩)))))) :=
  Term.fix [Ty.nat, Ty.nat, (Ty.record ⟨Ty.int, Ty.int, []⟩), Ty.nat, (Ty.record ⟨Ty.int, Ty.int, []⟩)] 2 (.cons (Term.ite (natEq (♯0) (Term.natL 0)) (♯1) (♯3)) (.cons (natSub (Term.natL 1) (♯0)) .nil)) bd_testEven___testOdd__clique_ (Term.ctor (τ := (Ty.record ⟨Ty.int, Ty.int, []⟩)) 0 [Ty.int, Ty.int] (by rfl) (.cons (Term.intL (0)) (.cons (Term.intL (0)) .nil)))

/-- The module up to and including `testEven & testOdd (clique)`. -/
def prog_testEven___testOdd__clique_ : Program (d_testEven___testOdd__clique_ :: sig_testEven___testOdd__clique_.decls) :=
  .cons d_testEven___testOdd__clique_ sig_testEven___testOdd__clique_.h_names_unique tm_testEven___testOdd__clique_ prog_test5

/-- `testEven`, as a declaration of the module. -/
def d_testEven : GlobalDecl := ⟨"testEven", (Ty.fn Ty.nat (Ty.fn (Ty.record ⟨Ty.int, Ty.int, []⟩) (Ty.record ⟨Ty.int, Ty.int, []⟩)))⟩

/-- The signature `testEven` is written against. -/
def sig_testEven : Sig := ⟨[d_testEven___testOdd__clique_, d_test5, d_test4, d_test3, d_test2, d_test1], by decide⟩

/-- The body of `testEven`. -/
def tm_testEven : Term sig_testEven [] [] (Ty.fn Ty.nat (Ty.fn (Ty.record ⟨Ty.int, Ty.int, []⟩) (Ty.record ⟨Ty.int, Ty.int, []⟩))) :=
  (Term.lam (Term.lam (Term.ap (Term.ap (Term.ap (Term.ap (Term.ap (Term.global .here) (Term.natL 0)) (♯1)) (♯0)) (Term.natL 0)) (Term.ctor (τ := (Ty.record ⟨Ty.int, Ty.int, []⟩)) 0 [Ty.int, Ty.int] (by rfl) (.cons (Term.intL (0)) (.cons (Term.intL (0)) .nil))))))

/-- The module up to and including `testEven`. -/
def prog_testEven : Program (d_testEven :: sig_testEven.decls) :=
  .cons d_testEven sig_testEven.h_names_unique tm_testEven prog_testEven___testOdd__clique_

/-- `testOdd`, as a declaration of the module. -/
def d_testOdd : GlobalDecl := ⟨"testOdd", (Ty.fn Ty.nat (Ty.fn (Ty.record ⟨Ty.int, Ty.int, []⟩) (Ty.record ⟨Ty.int, Ty.int, []⟩)))⟩

/-- The signature `testOdd` is written against. -/
def sig_testOdd : Sig := ⟨[d_testEven, d_testEven___testOdd__clique_, d_test5, d_test4, d_test3, d_test2, d_test1], by decide⟩

/-- The body of `testOdd`. -/
def tm_testOdd : Term sig_testOdd [] [] (Ty.fn Ty.nat (Ty.fn (Ty.record ⟨Ty.int, Ty.int, []⟩) (Ty.record ⟨Ty.int, Ty.int, []⟩))) :=
  (Term.lam (Term.lam (Term.ap (Term.ap (Term.ap (Term.ap (Term.ap (Term.global (.there .here)) (Term.natL 1)) (Term.natL 0)) (Term.ctor (τ := (Ty.record ⟨Ty.int, Ty.int, []⟩)) 0 [Ty.int, Ty.int] (by rfl) (.cons (Term.intL (0)) (.cons (Term.intL (0)) .nil)))) (♯1)) (♯0))))

/-- The module up to and including `testOdd`. -/
def prog_testOdd : Program (d_testOdd :: sig_testOdd.decls) :=
  .cons d_testOdd sig_testOdd.h_names_unique tm_testOdd prog_testEven

/-- The signature of the whole module. -/
def moduleSig : Sig := ⟨[d_testOdd, d_testEven, d_testEven___testOdd__clique_, d_test5, d_test4, d_test3, d_test2, d_test1], by decide⟩

/-- The module as a telescope: every body is written against the declarations before it, so the call graph is acyclic by construction.  It is built one declaration at a time, above, so that no single elaboration sees the whole telescope at once. -/
def program : Program moduleSig.decls :=
  prog_testOdd

end ProgramSnapshotsPBOPureCaptureDerefRegression01
