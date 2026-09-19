-- SnapshotsPBOPure.CaseLeafTco: the module as a Program of the one grammar of `LakeJs.Expr`.
-- 🎯 a public entry point of the module; 📦 a declaration the translation pulled in.
-- Every term below is a `Term`, so it is terminating by construction: the one way it
-- repeats work is `Term.fix`, whose measure it descends on at every self call.
--
-- ════ 📦 Array.back? @ Int : (fn (array int) (taggedUnion ()|(int)))
-- ƛ let ♯ := (extern⟨(array int) ⇒ nat⟩ ⬝ ♯0);
-- let ♯ := 1#;
-- let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯1) ⬝ ♯0);
-- let ♯ := ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ ♯2);
-- if ♯0 then let ♯ := ((extern⟨(array int) nat ⇒ int⟩ ⬝ ♯4) ⬝ ♯1);
-- let ♯ := ctor1(int)(♯0);
-- ♯0 else let ♯ := ctor0()();
-- ♯0
--
-- ════ 📦 LakeJs.CoreModels.arrayAppendFrom @ Int : (fn (array int) (fn (array int) (fn nat (array int))))
--      measure: well-founded recursion, `termination_by` transcribed verbatim; 1 component: [ ((extern⟨nat nat ⇒ nat⟩ ⬝ (extern⟨(array int) ⇒ nat⟩ ⬝ ♯1)) ⬝ ♯2) ]
-- fix ((array int) (array int) nat) measure [ ((extern⟨nat nat ⇒ nat⟩ ⬝ (extern⟨(array int) ⇒ nat⟩ ⬝ ♯1)) ⬝ ♯2) ] body {
--   let ♯ := (extern⟨(array int) ⇒ nat⟩ ⬝ ♯1);
--   let ♯ := ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯3) ⬝ ♯0);
--   if ♯0 then let ♯ := ((extern⟨(array int) nat ⇒ int⟩ ⬝ ♯3) ⬝ ♯4);
--   let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯3) ⬝ ♯0);
--   let ♯ := 1#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯7) ⬝ ♯0);
--   let ♯ := self0⟨↓⟩(♯2, ♯7, ♯0);
--   ♯0 else ♯2
-- } stuck { (extern⟨nat ⇒ (array int)⟩ ⬝ 0#) }
--
-- ════ 📦 Array.append @ Int : (fn (array int) (fn (array int) (array int)))
-- ƛ ƛ let ♯ := 0#;
-- let ♯ := (((@LakeJs.CoreModels.arrayAppendFrom @ Int ⬝ ♯2) ⬝ ♯1) ⬝ ♯0);
-- ♯0
--
-- ════ 🎯 test1Fuel : (fn nat (fn bool (fn (array int) (array int))))
--      measure: structural recursion, on the argument Lean recorded (position 0); 1 component: [ ♯0 ]
-- fix (nat bool (array int)) measure [ ♯0 ] body {
--   if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then ♯2 else let ♯ := 0#;
--   let ♯ := (extern⟨(array int) ⇒ nat⟩ ⬝ ♯3);
--   let ♯ := ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯1) ⬝ ♯0);
--   if ♯0 then let ♯ := ((extern⟨(array int) nat ⇒ int⟩ ⬝ ♯5) ⬝ ♯2);
--   let ♯ := 1#;
--   let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--   let ♯ := ((extern⟨int int ⇒ bool⟩ ⬝ ♯2) ⬝ ♯0);
--   if ♯0 then let ♯ := (@Array.back? @ Int ⬝ ♯9);
--   case ♯0 of
--     | 0() => let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯10) ⬝ ♯2);
--       ♯0
--     | 1(int) => let ♯ := 2#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := ((extern⟨int int ⇒ bool⟩ ⬝ ♯2) ⬝ ♯0);
--       if ♯0 then ♯14 else if ♯13 then let ♯ := 0#;
--       let ♯ := (extern⟨nat ⇒ (array int)⟩ ⬝ ♯0);
--       ♯0 else let ♯ := 3#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := 5#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := 6#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := 7#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := 8#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := 9#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := 10#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := 12#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := 13#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := 14#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := 15#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := 16#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := 17#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := (extern⟨nat ⇒ (array int)⟩ ⬝ ♯1);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯30);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯34);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯27);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯33);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯27);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯26);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯25);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯24);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯23);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯22);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯43);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯22);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯21);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯20);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯19);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯18);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯17);
--       let ♯ := ((@Array.append @ Int ⬝ ♯0) ⬝ ♯58);
--       let ♯ := self0⟨↓⟩(((extern⟨nat nat ⇒ nat⟩ ⬝ ♯57) ⬝ 1#), ♯58, ♯0);
--       ♯0
--  else let ♯ := (@Array.back? @ Int ⬝ ♯9);
--   case ♯0 of
--     | 0() => let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯10) ⬝ ♯4);
--       ♯0
--     | 1(int) => if ♯10 then let ♯ := 0#;
--       let ♯ := (extern⟨nat ⇒ (array int)⟩ ⬝ ♯0);
--       ♯0 else let ♯ := 3#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := 5#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := 6#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := 7#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := 8#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := 9#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := 10#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := 12#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := 13#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := 14#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := 15#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := 16#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := 17#;
--       let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--       let ♯ := (extern⟨nat ⇒ (array int)⟩ ⬝ ♯1);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯27);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯33);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯27);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯30);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯27);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯26);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯25);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯24);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯23);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯22);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯42);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯22);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯21);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯20);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯19);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯18);
--       let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯0) ⬝ ♯17);
--       let ♯ := ((@Array.append @ Int ⬝ ♯0) ⬝ ♯55);
--       let ♯ := self0⟨↓⟩(((extern⟨nat nat ⇒ nat⟩ ⬝ ♯54) ⬝ 1#), ♯55, ♯0);
--       ♯0
--  else let ♯ := (@Array.back? @ Int ⬝ ♯5);
--   case ♯0 of
--     | 0() => ♯6
--     | 1(int) => let ♯ := ((extern⟨(array int) int ⇒ (array int)⟩ ⬝ ♯7) ⬝ ♯0);
--       ♯0
--
-- } stuck { (extern⟨nat ⇒ (array int)⟩ ⬝ 0#) }
--
-- ════ 🎯 test1FuelCalled : (fn bool (fn (array int) (array int)))
-- ƛ ƛ let ♯ := 1000000#;
-- let ♯ := (((@test1Fuel ⬝ ♯0) ⬝ ♯2) ⬝ ♯1);
-- ♯0
--
--
-- ── the same program as Lean source ────────────────────────────────────
-- The trees above are this program printed in the notation of `LakeJs.ExprPretty`;
-- copy one into a `[LEAN|...]` elaboration if you want to read it there.

import LakeJs

open LakeJs LakeJs.Ty LakeJs.Expr LakeJs.Expr.Ops

namespace ProgramSnapshotsPBOPureCaseLeafTco

/-- `Array.back? @ Int`, as a declaration of the module. -/
def d_Array_back____Int : GlobalDecl := ⟨"Array.back? @ Int", (Ty.fn (Ty.array Ty.int) (Ty.option Ty.int))⟩

/-- The signature `Array.back? @ Int` is written against. -/
def sig_Array_back____Int : Sig := ⟨[], by decide⟩

/-- The body of `Array.back? @ Int`. -/
def tm_Array_back____Int : Term sig_Array_back____Int [] [] (Ty.fn (Ty.array Ty.int) (Ty.option Ty.int)) :=
  (Term.lam (Term.letE (arrLen (♯0)) (Term.letE (Term.natL 1) (Term.letE (natSub (♯1) (♯0)) (Term.letE (natLt (♯0) (♯2)) (Term.ite (♯0) (Term.letE (arrGet (♯4) (♯1)) (Term.letE (Term.ctor (τ := (Ty.option Ty.int)) 1 [Ty.int] (by rfl) (.cons (♯0) .nil)) (♯0))) (Term.letE (Term.ctor (τ := (Ty.option Ty.int)) 0 [] (by rfl) .nil) (♯0))))))))

/-- The module up to and including `Array.back? @ Int`. -/
def prog_Array_back____Int : Program (d_Array_back____Int :: sig_Array_back____Int.decls) :=
  .cons d_Array_back____Int sig_Array_back____Int.h_names_unique tm_Array_back____Int Program.nil

/-- `LakeJs.CoreModels.arrayAppendFrom @ Int`, as a declaration of the module. -/
def d_LakeJs_CoreModels_arrayAppendFrom___Int : GlobalDecl := ⟨"LakeJs.CoreModels.arrayAppendFrom @ Int", (Ty.fn (Ty.array Ty.int) (Ty.fn (Ty.array Ty.int) (Ty.fn Ty.nat (Ty.array Ty.int))))⟩

/-- The signature `LakeJs.CoreModels.arrayAppendFrom @ Int` is written against. -/
def sig_LakeJs_CoreModels_arrayAppendFrom___Int : Sig := ⟨[d_Array_back____Int], by decide⟩

/-- The body of the recursion of `LakeJs.CoreModels.arrayAppendFrom @ Int`. -/
def bd_LakeJs_CoreModels_arrayAppendFrom___Int : Term sig_LakeJs_CoreModels_arrayAppendFrom___Int ([(Ty.array Ty.int), (Ty.array Ty.int), Ty.nat] ++ []) [⟨[(Ty.array Ty.int), (Ty.array Ty.int), Ty.nat], (Ty.array Ty.int)⟩] (Ty.array Ty.int) :=
  (Term.letE (arrLen (♯1)) (Term.letE (natLt (♯3) (♯0)) (Term.ite (♯0) (Term.letE (arrGet (♯3) (♯4)) (Term.letE (arrPush (♯3) (♯0)) (Term.letE (Term.natL 1) (Term.letE (natAdd (♯7) (♯0)) (Term.letE (Term.selfCall .head (.cons (♯2) (.cons (♯7) (.cons (♯0) .nil)))) (♯0)))))) (♯2))))

/-- The body of `LakeJs.CoreModels.arrayAppendFrom @ Int`. -/
def tm_LakeJs_CoreModels_arrayAppendFrom___Int : Term sig_LakeJs_CoreModels_arrayAppendFrom___Int [] [] (Ty.fn (Ty.array Ty.int) (Ty.fn (Ty.array Ty.int) (Ty.fn Ty.nat (Ty.array Ty.int)))) :=
  Term.fix [(Ty.array Ty.int), (Ty.array Ty.int), Ty.nat] 1 (.cons (natSub (arrLen (♯1)) (♯2)) .nil) bd_LakeJs_CoreModels_arrayAppendFrom___Int ((arrEmpty (α := Ty.int)) (Term.natL 0))

/-- The module up to and including `LakeJs.CoreModels.arrayAppendFrom @ Int`. -/
def prog_LakeJs_CoreModels_arrayAppendFrom___Int : Program (d_LakeJs_CoreModels_arrayAppendFrom___Int :: sig_LakeJs_CoreModels_arrayAppendFrom___Int.decls) :=
  .cons d_LakeJs_CoreModels_arrayAppendFrom___Int sig_LakeJs_CoreModels_arrayAppendFrom___Int.h_names_unique tm_LakeJs_CoreModels_arrayAppendFrom___Int prog_Array_back____Int

/-- `Array.append @ Int`, as a declaration of the module. -/
def d_Array_append___Int : GlobalDecl := ⟨"Array.append @ Int", (Ty.fn (Ty.array Ty.int) (Ty.fn (Ty.array Ty.int) (Ty.array Ty.int)))⟩

/-- The signature `Array.append @ Int` is written against. -/
def sig_Array_append___Int : Sig := ⟨[d_LakeJs_CoreModels_arrayAppendFrom___Int, d_Array_back____Int], by decide⟩

/-- The body of `Array.append @ Int`. -/
def tm_Array_append___Int : Term sig_Array_append___Int [] [] (Ty.fn (Ty.array Ty.int) (Ty.fn (Ty.array Ty.int) (Ty.array Ty.int))) :=
  (Term.lam (Term.lam (Term.letE (Term.natL 0) (Term.letE (Term.ap (Term.ap (Term.ap (Term.global .here) (♯2)) (♯1)) (♯0)) (♯0)))))

/-- The module up to and including `Array.append @ Int`. -/
def prog_Array_append___Int : Program (d_Array_append___Int :: sig_Array_append___Int.decls) :=
  .cons d_Array_append___Int sig_Array_append___Int.h_names_unique tm_Array_append___Int prog_LakeJs_CoreModels_arrayAppendFrom___Int

/-- `test1Fuel`, as a declaration of the module. -/
def d_test1Fuel : GlobalDecl := ⟨"test1Fuel", (Ty.fn Ty.nat (Ty.fn Ty.bool (Ty.fn (Ty.array Ty.int) (Ty.array Ty.int))))⟩

/-- The signature `test1Fuel` is written against. -/
def sig_test1Fuel : Sig := ⟨[d_Array_append___Int, d_LakeJs_CoreModels_arrayAppendFrom___Int, d_Array_back____Int], by decide⟩

/-- The body of the recursion of `test1Fuel`. -/
def bd_test1Fuel : Term sig_test1Fuel ([Ty.nat, Ty.bool, (Ty.array Ty.int)] ++ []) [⟨[Ty.nat, Ty.bool, (Ty.array Ty.int)], (Ty.array Ty.int)⟩] (Ty.array Ty.int) :=
  (Term.ite (natEq (♯0) (Term.natL 0)) (♯2) (Term.letE (Term.natL 0) (Term.letE (arrLen (♯3)) (Term.letE (natLt (♯1) (♯0)) (Term.ite (♯0) (Term.letE (arrGet (♯5) (♯2)) (Term.letE (Term.natL 1) (Term.letE (natToInt (♯0)) (Term.letE (intEq (♯2) (♯0)) (Term.ite (♯0) (Term.letE (Term.ap (Term.global (.there (.there .here))) (♯9)) (Term.caseTag (♯0) (Alts.cons 0 [] (by rfl) (Term.letE (arrPush (♯10) (♯2)) (♯0)) (Alts.cons 1 [Ty.int] (by rfl) (Term.letE (Term.natL 2) (Term.letE (natToInt (♯0)) (Term.letE (intEq (♯2) (♯0)) (Term.ite (♯0) (♯14) (Term.ite (♯13) (Term.letE (Term.natL 0) (Term.letE ((arrEmpty (α := Ty.int)) (♯0)) (♯0))) (Term.letE (Term.natL 3) (Term.letE (natToInt (♯0)) (Term.letE (Term.natL 5) (Term.letE (natToInt (♯0)) (Term.letE (Term.natL 6) (Term.letE (natToInt (♯0)) (Term.letE (Term.natL 7) (Term.letE (natToInt (♯0)) (Term.letE (Term.natL 8) (Term.letE (natToInt (♯0)) (Term.letE (Term.natL 9) (Term.letE (natToInt (♯0)) (Term.letE (Term.natL 10) (Term.letE (natToInt (♯0)) (Term.letE (Term.natL 12) (Term.letE (natToInt (♯0)) (Term.letE (Term.natL 13) (Term.letE (natToInt (♯0)) (Term.letE (Term.natL 14) (Term.letE (natToInt (♯0)) (Term.letE (Term.natL 15) (Term.letE (natToInt (♯0)) (Term.letE (Term.natL 16) (Term.letE (natToInt (♯0)) (Term.letE (Term.natL 17) (Term.letE (natToInt (♯0)) (Term.letE ((arrEmpty (α := Ty.int)) (♯1)) (Term.letE (arrPush (♯0) (♯30)) (Term.letE (arrPush (♯0) (♯34)) (Term.letE (arrPush (♯0) (♯27)) (Term.letE (arrPush (♯0) (♯33)) (Term.letE (arrPush (♯0) (♯27)) (Term.letE (arrPush (♯0) (♯26)) (Term.letE (arrPush (♯0) (♯25)) (Term.letE (arrPush (♯0) (♯24)) (Term.letE (arrPush (♯0) (♯23)) (Term.letE (arrPush (♯0) (♯22)) (Term.letE (arrPush (♯0) (♯43)) (Term.letE (arrPush (♯0) (♯22)) (Term.letE (arrPush (♯0) (♯21)) (Term.letE (arrPush (♯0) (♯20)) (Term.letE (arrPush (♯0) (♯19)) (Term.letE (arrPush (♯0) (♯18)) (Term.letE (arrPush (♯0) (♯17)) (Term.letE (Term.ap (Term.ap (Term.global .here) (♯0)) (♯58)) (Term.letE (Term.selfCall .head (.cons (natSub (♯57) (Term.natL 1)) (.cons (♯58) (.cons (♯0) .nil)))) (♯0)))))))))))))))))))))))))))))))))))))))))))))))))))) Alts.nilFull)) (by rfl))) (Term.letE (Term.ap (Term.global (.there (.there .here))) (♯9)) (Term.caseTag (♯0) (Alts.cons 0 [] (by rfl) (Term.letE (arrPush (♯10) (♯4)) (♯0)) (Alts.cons 1 [Ty.int] (by rfl) (Term.ite (♯10) (Term.letE (Term.natL 0) (Term.letE ((arrEmpty (α := Ty.int)) (♯0)) (♯0))) (Term.letE (Term.natL 3) (Term.letE (natToInt (♯0)) (Term.letE (Term.natL 5) (Term.letE (natToInt (♯0)) (Term.letE (Term.natL 6) (Term.letE (natToInt (♯0)) (Term.letE (Term.natL 7) (Term.letE (natToInt (♯0)) (Term.letE (Term.natL 8) (Term.letE (natToInt (♯0)) (Term.letE (Term.natL 9) (Term.letE (natToInt (♯0)) (Term.letE (Term.natL 10) (Term.letE (natToInt (♯0)) (Term.letE (Term.natL 12) (Term.letE (natToInt (♯0)) (Term.letE (Term.natL 13) (Term.letE (natToInt (♯0)) (Term.letE (Term.natL 14) (Term.letE (natToInt (♯0)) (Term.letE (Term.natL 15) (Term.letE (natToInt (♯0)) (Term.letE (Term.natL 16) (Term.letE (natToInt (♯0)) (Term.letE (Term.natL 17) (Term.letE (natToInt (♯0)) (Term.letE ((arrEmpty (α := Ty.int)) (♯1)) (Term.letE (arrPush (♯0) (♯27)) (Term.letE (arrPush (♯0) (♯33)) (Term.letE (arrPush (♯0) (♯27)) (Term.letE (arrPush (♯0) (♯30)) (Term.letE (arrPush (♯0) (♯27)) (Term.letE (arrPush (♯0) (♯26)) (Term.letE (arrPush (♯0) (♯25)) (Term.letE (arrPush (♯0) (♯24)) (Term.letE (arrPush (♯0) (♯23)) (Term.letE (arrPush (♯0) (♯22)) (Term.letE (arrPush (♯0) (♯42)) (Term.letE (arrPush (♯0) (♯22)) (Term.letE (arrPush (♯0) (♯21)) (Term.letE (arrPush (♯0) (♯20)) (Term.letE (arrPush (♯0) (♯19)) (Term.letE (arrPush (♯0) (♯18)) (Term.letE (arrPush (♯0) (♯17)) (Term.letE (Term.ap (Term.ap (Term.global .here) (♯0)) (♯55)) (Term.letE (Term.selfCall .head (.cons (natSub (♯54) (Term.natL 1)) (.cons (♯55) (.cons (♯0) .nil)))) (♯0)))))))))))))))))))))))))))))))))))))))))))))))) Alts.nilFull)) (by rfl)))))))) (Term.letE (Term.ap (Term.global (.there (.there .here))) (♯5)) (Term.caseTag (♯0) (Alts.cons 0 [] (by rfl) (♯6) (Alts.cons 1 [Ty.int] (by rfl) (Term.letE (arrPush (♯7) (♯0)) (♯0)) Alts.nilFull)) (by rfl))))))))

/-- The body of `test1Fuel`. -/
def tm_test1Fuel : Term sig_test1Fuel [] [] (Ty.fn Ty.nat (Ty.fn Ty.bool (Ty.fn (Ty.array Ty.int) (Ty.array Ty.int)))) :=
  Term.fix [Ty.nat, Ty.bool, (Ty.array Ty.int)] 1 (.cons (♯0) .nil) bd_test1Fuel ((arrEmpty (α := Ty.int)) (Term.natL 0))

/-- The module up to and including `test1Fuel`. -/
def prog_test1Fuel : Program (d_test1Fuel :: sig_test1Fuel.decls) :=
  .cons d_test1Fuel sig_test1Fuel.h_names_unique tm_test1Fuel prog_Array_append___Int

/-- `test1FuelCalled`, as a declaration of the module. -/
def d_test1FuelCalled : GlobalDecl := ⟨"test1FuelCalled", (Ty.fn Ty.bool (Ty.fn (Ty.array Ty.int) (Ty.array Ty.int)))⟩

/-- The signature `test1FuelCalled` is written against. -/
def sig_test1FuelCalled : Sig := ⟨[d_test1Fuel, d_Array_append___Int, d_LakeJs_CoreModels_arrayAppendFrom___Int, d_Array_back____Int], by decide⟩

/-- The body of `test1FuelCalled`. -/
def tm_test1FuelCalled : Term sig_test1FuelCalled [] [] (Ty.fn Ty.bool (Ty.fn (Ty.array Ty.int) (Ty.array Ty.int))) :=
  (Term.lam (Term.lam (Term.letE (Term.natL 1000000) (Term.letE (Term.ap (Term.ap (Term.ap (Term.global .here) (♯0)) (♯2)) (♯1)) (♯0)))))

/-- The module up to and including `test1FuelCalled`. -/
def prog_test1FuelCalled : Program (d_test1FuelCalled :: sig_test1FuelCalled.decls) :=
  .cons d_test1FuelCalled sig_test1FuelCalled.h_names_unique tm_test1FuelCalled prog_test1Fuel

/-- The signature of the whole module. -/
def moduleSig : Sig := ⟨[d_test1FuelCalled, d_test1Fuel, d_Array_append___Int, d_LakeJs_CoreModels_arrayAppendFrom___Int, d_Array_back____Int], by decide⟩

/-- The module as a telescope: every body is written against the declarations before it, so the call graph is acyclic by construction.  It is built one declaration at a time, above, so that no single elaboration sees the whole telescope at once. -/
def program : Program moduleSig.decls :=
  prog_test1FuelCalled

end ProgramSnapshotsPBOPureCaseLeafTco
