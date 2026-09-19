-- SnapshotsMy.AssignSteps: the module as a Program of the one grammar of `LakeJs.Expr`.
-- 🎯 a public entry point of the module; 📦 a declaration the translation pulled in.
-- Every term below is a `Term`, so it is terminating by construction: the one way it
-- repeats work is `Term.fix`, whose measure it descends on at every self call.
--
-- ════ 🎯 test1 : (fn nat (fn nat (fn nat nat)))
--      measure: structural recursion, on the argument Lean recorded (position 0); 1 component: [ ♯0 ]
-- fix (nat nat nat) measure [ ♯0 ] body {
--   if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then ♯1 else let ♯ := 0#;
--   let ♯ := ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯3) ⬝ ♯0);
--   let ♯ := ♯0;
--   if ♯0 then ♯4 else let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯4) ⬝ ♯5);
--   let ♯ := self0⟨↓⟩(((extern⟨nat nat ⇒ nat⟩ ⬝ ♯4) ⬝ 1#), ♯6, ♯0);
--   ♯0
-- } stuck { 0# }
--
-- ════ 🎯 test2 : (fn nat (fn nat (fn nat (fn nat nat))))
--      measure: structural recursion, on the argument Lean recorded (position 0); 1 component: [ ♯0 ]
-- fix (nat nat nat nat) measure [ ♯0 ] body {
--   if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then let ♯ := 100#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ ♯0);
--   let ♯ := 10#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯5) ⬝ ♯0);
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ ♯0);
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯0) ⬝ ♯8);
--   ♯0 else let ♯ := 1#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ ♯0);
--   let ♯ := self0⟨↓⟩(((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ 1#), ♯4, ♯5, ♯0);
--   ♯0
-- } stuck { 0# }
--
-- ════ 🎯 test4 : (fn nat (fn nat (fn nat nat)))
--      measure: structural recursion, on the argument Lean recorded (position 0); 1 component: [ ♯0 ]
-- fix (nat nat nat) measure [ ♯0 ] body {
--   if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯1) ⬝ ♯2);
--   ♯0 else let ♯ := 1#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ ♯0);
--   let ♯ := 2#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯5) ⬝ ♯0);
--   let ♯ := self0⟨↓⟩(((extern⟨nat nat ⇒ nat⟩ ⬝ ♯4) ⬝ 1#), ♯2, ♯0);
--   ♯0
-- } stuck { 0# }
--
-- ════ 📦 Nat.gcd : (fn nat (fn nat nat))
--      measure: well-founded recursion, `termination_by` transcribed verbatim; 1 component: [ ♯0 ]
-- fix (nat nat) measure [ ♯0 ] body {
--   let ♯ := 0#;
--   let ♯ := ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯1) ⬝ ♯0);
--   if ♯0 then ♯3 else let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯3) ⬝ ♯2);
--   let ♯ := self0⟨↓⟩(♯0, ♯3);
--   ♯0
-- } stuck { 0# }
--
-- ════ 🎯 test3 : (fn nat (fn nat (fn nat nat)))
--      measure: structural recursion, on the argument Lean recorded (position 0); 1 component: [ ♯0 ]
-- fix (nat nat nat) measure [ ♯0 ] body {
--   if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then let ♯ := 1000#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ ♯0);
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯0) ⬝ ♯4);
--   ♯0 else let ♯ := 7#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ ♯0);
--   let ♯ := ((@Nat.gcd ⬝ ♯4) ⬝ ♯0);
--   let ♯ := 3#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯6) ⬝ ♯0);
--   let ♯ := ((@Nat.gcd ⬝ ♯6) ⬝ ♯0);
--   let ♯ := self0⟨↓⟩(((extern⟨nat nat ⇒ nat⟩ ⬝ ♯6) ⬝ 1#), ♯3, ♯0);
--   ♯0
-- } stuck { 0# }
--
--
-- ── the same program as Lean source ────────────────────────────────────
-- The trees above are this program printed in the notation of `LakeJs.ExprPretty`;
-- copy one into a `[LEAN|...]` elaboration if you want to read it there.

import LakeJs

open LakeJs LakeJs.Ty LakeJs.Expr LakeJs.Expr.Ops

namespace ProgramSnapshotsMyAssignSteps

/-- `test1`, as a declaration of the module. -/
def d_test1 : GlobalDecl := ⟨"test1", (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat)))⟩

/-- The signature `test1` is written against. -/
def sig_test1 : Sig := ⟨[], by decide⟩

/-- The body of the recursion of `test1`. -/
def bd_test1 : Term sig_test1 ([Ty.nat, Ty.nat, Ty.nat] ++ []) [⟨[Ty.nat, Ty.nat, Ty.nat], Ty.nat⟩] Ty.nat :=
  (Term.ite (natEq (♯0) (Term.natL 0)) (♯1) (Term.letE (Term.natL 0) (Term.letE (natEq (♯3) (♯0)) (Term.letE (♯0) (Term.ite (♯0) (♯4) (Term.letE (natMod (♯4) (♯5)) (Term.letE (Term.selfCall .head (.cons (natSub (♯4) (Term.natL 1)) (.cons (♯6) (.cons (♯0) .nil)))) (♯0))))))))

/-- The body of `test1`. -/
def tm_test1 : Term sig_test1 [] [] (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat))) :=
  Term.fix [Ty.nat, Ty.nat, Ty.nat] 1 (.cons (♯0) .nil) bd_test1 (Term.natL 0)

/-- The module up to and including `test1`. -/
def prog_test1 : Program (d_test1 :: sig_test1.decls) :=
  .cons d_test1 sig_test1.h_names_unique tm_test1 Program.nil

/-- `test2`, as a declaration of the module. -/
def d_test2 : GlobalDecl := ⟨"test2", (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat))))⟩

/-- The signature `test2` is written against. -/
def sig_test2 : Sig := ⟨[d_test1], by decide⟩

/-- The body of the recursion of `test2`. -/
def bd_test2 : Term sig_test2 ([Ty.nat, Ty.nat, Ty.nat, Ty.nat] ++ []) [⟨[Ty.nat, Ty.nat, Ty.nat, Ty.nat], Ty.nat⟩] Ty.nat :=
  (Term.ite (natEq (♯0) (Term.natL 0)) (Term.letE (Term.natL 100) (Term.letE (natMul (♯2) (♯0)) (Term.letE (Term.natL 10) (Term.letE (natMul (♯5) (♯0)) (Term.letE (natAdd (♯2) (♯0)) (Term.letE (natAdd (♯0) (♯8)) (♯0))))))) (Term.letE (Term.natL 1) (Term.letE (natAdd (♯2) (♯0)) (Term.letE (Term.selfCall .head (.cons (natSub (♯2) (Term.natL 1)) (.cons (♯4) (.cons (♯5) (.cons (♯0) .nil))))) (♯0)))))

/-- The body of `test2`. -/
def tm_test2 : Term sig_test2 [] [] (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat)))) :=
  Term.fix [Ty.nat, Ty.nat, Ty.nat, Ty.nat] 1 (.cons (♯0) .nil) bd_test2 (Term.natL 0)

/-- The module up to and including `test2`. -/
def prog_test2 : Program (d_test2 :: sig_test2.decls) :=
  .cons d_test2 sig_test2.h_names_unique tm_test2 prog_test1

/-- `test4`, as a declaration of the module. -/
def d_test4 : GlobalDecl := ⟨"test4", (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat)))⟩

/-- The signature `test4` is written against. -/
def sig_test4 : Sig := ⟨[d_test2, d_test1], by decide⟩

/-- The body of the recursion of `test4`. -/
def bd_test4 : Term sig_test4 ([Ty.nat, Ty.nat, Ty.nat] ++ []) [⟨[Ty.nat, Ty.nat, Ty.nat], Ty.nat⟩] Ty.nat :=
  (Term.ite (natEq (♯0) (Term.natL 0)) (Term.letE (natAdd (♯1) (♯2)) (♯0)) (Term.letE (Term.natL 1) (Term.letE (natAdd (♯2) (♯0)) (Term.letE (Term.natL 2) (Term.letE (natAdd (♯5) (♯0)) (Term.letE (Term.selfCall .head (.cons (natSub (♯4) (Term.natL 1)) (.cons (♯2) (.cons (♯0) .nil)))) (♯0)))))))

/-- The body of `test4`. -/
def tm_test4 : Term sig_test4 [] [] (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat))) :=
  Term.fix [Ty.nat, Ty.nat, Ty.nat] 1 (.cons (♯0) .nil) bd_test4 (Term.natL 0)

/-- The module up to and including `test4`. -/
def prog_test4 : Program (d_test4 :: sig_test4.decls) :=
  .cons d_test4 sig_test4.h_names_unique tm_test4 prog_test2

/-- `Nat.gcd`, as a declaration of the module. -/
def d_Nat_gcd : GlobalDecl := ⟨"Nat.gcd", (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat))⟩

/-- The signature `Nat.gcd` is written against. -/
def sig_Nat_gcd : Sig := ⟨[d_test4, d_test2, d_test1], by decide⟩

/-- The body of the recursion of `Nat.gcd`. -/
def bd_Nat_gcd : Term sig_Nat_gcd ([Ty.nat, Ty.nat] ++ []) [⟨[Ty.nat, Ty.nat], Ty.nat⟩] Ty.nat :=
  (Term.letE (Term.natL 0) (Term.letE (natEq (♯1) (♯0)) (Term.ite (♯0) (♯3) (Term.letE (natMod (♯3) (♯2)) (Term.letE (Term.selfCall .head (.cons (♯0) (.cons (♯3) .nil))) (♯0))))))

/-- The body of `Nat.gcd`. -/
def tm_Nat_gcd : Term sig_Nat_gcd [] [] (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat)) :=
  Term.fix [Ty.nat, Ty.nat] 1 (.cons (♯0) .nil) bd_Nat_gcd (Term.natL 0)

/-- The module up to and including `Nat.gcd`. -/
def prog_Nat_gcd : Program (d_Nat_gcd :: sig_Nat_gcd.decls) :=
  .cons d_Nat_gcd sig_Nat_gcd.h_names_unique tm_Nat_gcd prog_test4

/-- `test3`, as a declaration of the module. -/
def d_test3 : GlobalDecl := ⟨"test3", (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat)))⟩

/-- The signature `test3` is written against. -/
def sig_test3 : Sig := ⟨[d_Nat_gcd, d_test4, d_test2, d_test1], by decide⟩

/-- The body of the recursion of `test3`. -/
def bd_test3 : Term sig_test3 ([Ty.nat, Ty.nat, Ty.nat] ++ []) [⟨[Ty.nat, Ty.nat, Ty.nat], Ty.nat⟩] Ty.nat :=
  (Term.ite (natEq (♯0) (Term.natL 0)) (Term.letE (Term.natL 1000) (Term.letE (natMul (♯2) (♯0)) (Term.letE (natAdd (♯0) (♯4)) (♯0)))) (Term.letE (Term.natL 7) (Term.letE (natAdd (♯2) (♯0)) (Term.letE (Term.ap (Term.ap (Term.global .here) (♯4)) (♯0)) (Term.letE (Term.natL 3) (Term.letE (natAdd (♯6) (♯0)) (Term.letE (Term.ap (Term.ap (Term.global .here) (♯6)) (♯0)) (Term.letE (Term.selfCall .head (.cons (natSub (♯6) (Term.natL 1)) (.cons (♯3) (.cons (♯0) .nil)))) (♯0)))))))))

/-- The body of `test3`. -/
def tm_test3 : Term sig_test3 [] [] (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat))) :=
  Term.fix [Ty.nat, Ty.nat, Ty.nat] 1 (.cons (♯0) .nil) bd_test3 (Term.natL 0)

/-- The module up to and including `test3`. -/
def prog_test3 : Program (d_test3 :: sig_test3.decls) :=
  .cons d_test3 sig_test3.h_names_unique tm_test3 prog_Nat_gcd

/-- The signature of the whole module. -/
def moduleSig : Sig := ⟨[d_test3, d_Nat_gcd, d_test4, d_test2, d_test1], by decide⟩

/-- The module as a telescope: every body is written against the declarations before it, so the call graph is acyclic by construction.  It is built one declaration at a time, above, so that no single elaboration sees the whole telescope at once. -/
def program : Program moduleSig.decls :=
  prog_test3

end ProgramSnapshotsMyAssignSteps
