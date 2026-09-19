-- SnapshotsMy.StringWalk: the module as a Program of the one grammar of `LakeJs.Expr`.
-- 🎯 a public entry point of the module; 📦 a declaration the translation pulled in.
-- Every term below is a `Term`, so it is terminating by construction: the one way it
-- repeats work is `Term.fix`, whose measure it descends on at every self call.
--
-- ════ 🎯 test4.go : (fn string (fn nat (fn nat nat)))
--      measure: well-founded recursion, `termination_by` transcribed verbatim; 1 component: [ ((extern⟨nat nat ⇒ nat⟩ ⬝ (extern⟨string ⇒ nat⟩ ⬝ ♯0)) ⬝ ♯1) ]
-- fix (string nat nat) measure [ ((extern⟨nat nat ⇒ nat⟩ ⬝ (extern⟨string ⇒ nat⟩ ⬝ ♯0)) ⬝ ♯1) ] body {
--   let ♯ := (extern⟨string ⇒ nat⟩ ⬝ ♯0);
--   let ♯ := ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯2) ⬝ ♯0);
--   if ♯0 then let ♯ := 1#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯4) ⬝ ♯0);
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯6) ⬝ ♯5);
--   let ♯ := self0⟨↓⟩(♯5, ♯1, ♯0);
--   ♯0 else ♯4
-- } stuck { 0# }
--
-- ════ 📦 _private.Init.Data.Range.Basic.0.Std.Legacy.Range.forIn'.loop._at_.test3.spec_0 : (fn (record nat nat nat) (fn (record nat string) (fn nat (record nat string))))
--      measure: well-founded recursion, `termination_by` transcribed verbatim; 1 component: [ ((extern⟨nat nat ⇒ nat⟩ ⬝ proj0.1(♯0)) ⬝ ♯2) ]
-- fix ((record nat nat nat) (record nat string) nat) measure [ ((extern⟨nat nat ⇒ nat⟩ ⬝ proj0.1(♯0)) ⬝ ♯2) ] body {
--   let ♯ := proj0.1(♯0);
--   let ♯ := ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯3) ⬝ ♯0);
--   if ♯0 then let ♯ := proj0.0(♯3);
--   let ♯ := proj0.1(♯4);
--   let ♯ := (extern⟨string ⇒ nat⟩ ⬝ ♯0);
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ ♯0);
--   let ♯ := 'x';
--   let ♯ := ((extern⟨string char ⇒ string⟩ ⬝ ♯3) ⬝ ♯0);
--   let ♯ := ctor0(nat string)(♯2, ♯0);
--   let ♯ := proj0.2(♯9);
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯12) ⬝ ♯0);
--   let ♯ := self0⟨↓⟩(♯11, ♯2, ♯0);
--   ♯0 else ♯3
-- } stuck { ctor0(nat string)(0#, "") }
--
-- ════ 📦 String.Pos.Raw.atEnd : (fn string (fn nat bool))
-- ƛ ƛ let ♯ := (extern⟨string ⇒ nat⟩ ⬝ ♯1);
-- let ♯ := ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ ♯1);
-- let ♯ := ♯0;
-- ♯0
--
-- ════ 📦 String.Pos.Raw.next : (fn string (fn nat nat))
-- ƛ ƛ let ♯ := "";
-- let ♯ := ♯1;
-- let ♯ := ((extern⟨string nat ⇒ char⟩ ⬝ ♯3) ⬝ ♯0);
-- let ♯ := ((extern⟨string char ⇒ string⟩ ⬝ ♯2) ⬝ ♯0);
-- let ♯ := (extern⟨string ⇒ nat⟩ ⬝ ♯0);
-- let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯5) ⬝ ♯0);
-- ♯0
--
-- ════ 📦 instDecidableEqChar : (fn char (fn char bool))
-- ƛ ƛ let ♯ := "";
-- let ♯ := ((extern⟨string char ⇒ string⟩ ⬝ ♯0) ⬝ ♯2);
-- let ♯ := ((extern⟨string char ⇒ string⟩ ⬝ ♯1) ⬝ ♯2);
-- let ♯ := ((extern⟨string string ⇒ bool⟩ ⬝ ♯1) ⬝ ♯0);
-- let ♯ := ♯0;
-- ♯0
--
-- ════ 🎯 test3 : (fn string (fn nat nat))
-- ƛ ƛ let ♯ := 0#;
-- let ♯ := 1#;
-- let ♯ := ctor0(nat nat nat)(♯1, ♯2, ♯0);
-- let ♯ := ctor0(nat string)(♯2, ♯4);
-- let ♯ := (((@_private.Init.Data.Range.Basic.0.Std.Legacy.Range.forIn'.loop._at_.test3.spec_0 ⬝ ♯1) ⬝ ♯0) ⬝ ♯3);
-- case ♯0 of
--   | 0(nat string) => ♯0
--
--
-- ════ 🎯 test4 : (fn string nat)
-- ƛ let ♯ := 0#;
-- let ♯ := (((@test4.go ⬝ ♯1) ⬝ ♯0) ⬝ ♯0);
-- ♯0
--
-- ════ 🎯 test1.go : (fn string (fn char (fn nat (fn nat nat))))
--      measure: well-founded recursion, `termination_by` transcribed verbatim; 1 component: [ ((extern⟨nat nat ⇒ nat⟩ ⬝ (extern⟨string ⇒ nat⟩ ⬝ ♯0)) ⬝ ♯2) ]
-- fix (string char nat nat) measure [ ((extern⟨nat nat ⇒ nat⟩ ⬝ (extern⟨string ⇒ nat⟩ ⬝ ♯0)) ⬝ ♯2) ] body {
--   let ♯ := ((@String.Pos.Raw.atEnd ⬝ ♯0) ⬝ ♯2);
--   if ♯0 then ♯4 else let ♯ := ((@String.Pos.Raw.next ⬝ ♯1) ⬝ ♯3);
--   let ♯ := ((extern⟨string nat ⇒ char⟩ ⬝ ♯2) ⬝ ♯4);
--   let ♯ := ((@instDecidableEqChar ⬝ ♯0) ⬝ ♯4);
--   let ♯ := ♯0;
--   if ♯0 then let ♯ := 1#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯9) ⬝ ♯0);
--   let ♯ := self0⟨↓⟩(♯7, ♯8, ♯5, ♯0);
--   ♯0 else let ♯ := self0⟨↓⟩(♯5, ♯6, ♯3, ♯8);
--   ♯0
-- } stuck { 0# }
--
-- ════ 🎯 test2.go : (fn string (fn char (fn nat nat)))
--      measure: well-founded recursion, `termination_by` transcribed verbatim; 1 component: [ ((extern⟨nat nat ⇒ nat⟩ ⬝ (extern⟨string ⇒ nat⟩ ⬝ ♯0)) ⬝ ♯2) ]
-- fix (string char nat) measure [ ((extern⟨nat nat ⇒ nat⟩ ⬝ (extern⟨string ⇒ nat⟩ ⬝ ♯0)) ⬝ ♯2) ] body {
--   let ♯ := ((@String.Pos.Raw.atEnd ⬝ ♯0) ⬝ ♯2);
--   if ♯0 then ♯3 else let ♯ := ((extern⟨string nat ⇒ char⟩ ⬝ ♯1) ⬝ ♯3);
--   let ♯ := ((@instDecidableEqChar ⬝ ♯0) ⬝ ♯3);
--   let ♯ := ♯0;
--   if ♯0 then ♯6 else let ♯ := ((@String.Pos.Raw.next ⬝ ♯4) ⬝ ♯6);
--   let ♯ := self0⟨↓⟩(♯5, ♯6, ♯0);
--   ♯0
-- } stuck { 0# }
--
-- ════ 🎯 test1 : (fn string (fn char nat))
-- ƛ ƛ let ♯ := 0#;
-- let ♯ := ♯0;
-- let ♯ := ((((@test1.go ⬝ ♯3) ⬝ ♯2) ⬝ ♯0) ⬝ ♯1);
-- ♯0
--
-- ════ 🎯 test2 : (fn string (fn char nat))
-- ƛ ƛ let ♯ := 0#;
-- let ♯ := ♯0;
-- let ♯ := (((@test2.go ⬝ ♯3) ⬝ ♯2) ⬝ ♯0);
-- ♯0
--
--
-- ── the same program as Lean source ────────────────────────────────────
-- The trees above are this program printed in the notation of `LakeJs.ExprPretty`;
-- copy one into a `[LEAN|...]` elaboration if you want to read it there.

import LakeJs

open LakeJs LakeJs.Ty LakeJs.Expr LakeJs.Expr.Ops

namespace ProgramSnapshotsMyStringWalk

/-- `test4.go`, as a declaration of the module. -/
def d_test4_go : GlobalDecl := ⟨"test4.go", (Ty.fn Ty.string (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat)))⟩

/-- The signature `test4.go` is written against. -/
def sig_test4_go : Sig := ⟨[], by decide⟩

/-- The body of the recursion of `test4.go`. -/
def bd_test4_go : Term sig_test4_go ([Ty.string, Ty.nat, Ty.nat] ++ []) [⟨[Ty.string, Ty.nat, Ty.nat], Ty.nat⟩] Ty.nat :=
  (Term.letE (strLength (♯0)) (Term.letE (natLt (♯2) (♯0)) (Term.ite (♯0) (Term.letE (Term.natL 1) (Term.letE (natAdd (♯4) (♯0)) (Term.letE (natAdd (♯6) (♯5)) (Term.letE (Term.selfCall .head (.cons (♯5) (.cons (♯1) (.cons (♯0) .nil)))) (♯0))))) (♯4))))

/-- The body of `test4.go`. -/
def tm_test4_go : Term sig_test4_go [] [] (Ty.fn Ty.string (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat))) :=
  Term.fix [Ty.string, Ty.nat, Ty.nat] 1 (.cons (natSub (strLength (♯0)) (♯1)) .nil) bd_test4_go (Term.natL 0)

/-- The module up to and including `test4.go`. -/
def prog_test4_go : Program (d_test4_go :: sig_test4_go.decls) :=
  .cons d_test4_go sig_test4_go.h_names_unique tm_test4_go Program.nil

/-- `_private.Init.Data.Range.Basic.0.Std.Legacy.Range.forIn'.loop._at_.test3.spec_0`, as a declaration of the module. -/
def d__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0 : GlobalDecl := ⟨"_private.Init.Data.Range.Basic.0.Std.Legacy.Range.forIn'.loop._at_.test3.spec_0", (Ty.fn (Ty.record ⟨Ty.nat, Ty.nat, [Ty.nat]⟩) (Ty.fn (Ty.record ⟨Ty.nat, Ty.string, []⟩) (Ty.fn Ty.nat (Ty.record ⟨Ty.nat, Ty.string, []⟩))))⟩

/-- The signature `_private.Init.Data.Range.Basic.0.Std.Legacy.Range.forIn'.loop._at_.test3.spec_0` is written against. -/
def sig__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0 : Sig := ⟨[d_test4_go], by decide⟩

/-- The body of the recursion of `_private.Init.Data.Range.Basic.0.Std.Legacy.Range.forIn'.loop._at_.test3.spec_0`. -/
def bd__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0 : Term sig__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0 ([(Ty.record ⟨Ty.nat, Ty.nat, [Ty.nat]⟩), (Ty.record ⟨Ty.nat, Ty.string, []⟩), Ty.nat] ++ []) [⟨[(Ty.record ⟨Ty.nat, Ty.nat, [Ty.nat]⟩), (Ty.record ⟨Ty.nat, Ty.string, []⟩), Ty.nat], (Ty.record ⟨Ty.nat, Ty.string, []⟩)⟩] (Ty.record ⟨Ty.nat, Ty.string, []⟩) :=
  (Term.letE (Term.proj (♯0) 0 1 (by rfl) (by rfl)) (Term.letE (natLt (♯3) (♯0)) (Term.ite (♯0) (Term.letE (Term.proj (♯3) 0 0 (by rfl) (by rfl)) (Term.letE (Term.proj (♯4) 0 1 (by rfl) (by rfl)) (Term.letE (strUtf8ByteSize (♯0)) (Term.letE (natAdd (♯2) (♯0)) (Term.letE (Term.lit (.char (Char.ofNat 120))) (Term.letE (strPush (♯3) (♯0)) (Term.letE (Term.ctor (τ := (Ty.record ⟨Ty.nat, Ty.string, []⟩)) 0 [Ty.nat, Ty.string] (by rfl) (.cons (♯2) (.cons (♯0) .nil))) (Term.letE (Term.proj (♯9) 0 2 (by rfl) (by rfl)) (Term.letE (natAdd (♯12) (♯0)) (Term.letE (Term.selfCall .head (.cons (♯11) (.cons (♯2) (.cons (♯0) .nil)))) (♯0))))))))))) (♯3))))

/-- The body of `_private.Init.Data.Range.Basic.0.Std.Legacy.Range.forIn'.loop._at_.test3.spec_0`. -/
def tm__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0 : Term sig__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0 [] [] (Ty.fn (Ty.record ⟨Ty.nat, Ty.nat, [Ty.nat]⟩) (Ty.fn (Ty.record ⟨Ty.nat, Ty.string, []⟩) (Ty.fn Ty.nat (Ty.record ⟨Ty.nat, Ty.string, []⟩)))) :=
  Term.fix [(Ty.record ⟨Ty.nat, Ty.nat, [Ty.nat]⟩), (Ty.record ⟨Ty.nat, Ty.string, []⟩), Ty.nat] 1 (.cons (natSub (Term.proj (♯0) 0 1 (by rfl) (by rfl)) (♯2)) .nil) bd__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0 (Term.ctor (τ := (Ty.record ⟨Ty.nat, Ty.string, []⟩)) 0 [Ty.nat, Ty.string] (by rfl) (.cons (Term.natL 0) (.cons (Term.strL "") .nil)))

/-- The module up to and including `_private.Init.Data.Range.Basic.0.Std.Legacy.Range.forIn'.loop._at_.test3.spec_0`. -/
def prog__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0 : Program (d__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0 :: sig__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0.decls) :=
  .cons d__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0 sig__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0.h_names_unique tm__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0 prog_test4_go

/-- `String.Pos.Raw.atEnd`, as a declaration of the module. -/
def d_String_Pos_Raw_atEnd : GlobalDecl := ⟨"String.Pos.Raw.atEnd", (Ty.fn Ty.string (Ty.fn Ty.nat Ty.bool))⟩

/-- The signature `String.Pos.Raw.atEnd` is written against. -/
def sig_String_Pos_Raw_atEnd : Sig := ⟨[d__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0, d_test4_go], by decide⟩

/-- The body of `String.Pos.Raw.atEnd`. -/
def tm_String_Pos_Raw_atEnd : Term sig_String_Pos_Raw_atEnd [] [] (Ty.fn Ty.string (Ty.fn Ty.nat Ty.bool)) :=
  (Term.lam (Term.lam (Term.letE (strUtf8ByteSize (♯1)) (Term.letE (natLe (♯0) (♯1)) (Term.letE (♯0) (♯0))))))

/-- The module up to and including `String.Pos.Raw.atEnd`. -/
def prog_String_Pos_Raw_atEnd : Program (d_String_Pos_Raw_atEnd :: sig_String_Pos_Raw_atEnd.decls) :=
  .cons d_String_Pos_Raw_atEnd sig_String_Pos_Raw_atEnd.h_names_unique tm_String_Pos_Raw_atEnd prog__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0

/-- `String.Pos.Raw.next`, as a declaration of the module. -/
def d_String_Pos_Raw_next : GlobalDecl := ⟨"String.Pos.Raw.next", (Ty.fn Ty.string (Ty.fn Ty.nat Ty.nat))⟩

/-- The signature `String.Pos.Raw.next` is written against. -/
def sig_String_Pos_Raw_next : Sig := ⟨[d_String_Pos_Raw_atEnd, d__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0, d_test4_go], by decide⟩

/-- The body of `String.Pos.Raw.next`. -/
def tm_String_Pos_Raw_next : Term sig_String_Pos_Raw_next [] [] (Ty.fn Ty.string (Ty.fn Ty.nat Ty.nat)) :=
  (Term.lam (Term.lam (Term.letE (Term.strL "") (Term.letE (♯1) (Term.letE (strCharAt (♯3) (♯0)) (Term.letE (strPush (♯2) (♯0)) (Term.letE (strUtf8ByteSize (♯0)) (Term.letE (natAdd (♯5) (♯0)) (♯0)))))))))

/-- The module up to and including `String.Pos.Raw.next`. -/
def prog_String_Pos_Raw_next : Program (d_String_Pos_Raw_next :: sig_String_Pos_Raw_next.decls) :=
  .cons d_String_Pos_Raw_next sig_String_Pos_Raw_next.h_names_unique tm_String_Pos_Raw_next prog_String_Pos_Raw_atEnd

/-- `instDecidableEqChar`, as a declaration of the module. -/
def d_instDecidableEqChar : GlobalDecl := ⟨"instDecidableEqChar", (Ty.fn Ty.char (Ty.fn Ty.char Ty.bool))⟩

/-- The signature `instDecidableEqChar` is written against. -/
def sig_instDecidableEqChar : Sig := ⟨[d_String_Pos_Raw_next, d_String_Pos_Raw_atEnd, d__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0, d_test4_go], by decide⟩

/-- The body of `instDecidableEqChar`. -/
def tm_instDecidableEqChar : Term sig_instDecidableEqChar [] [] (Ty.fn Ty.char (Ty.fn Ty.char Ty.bool)) :=
  (Term.lam (Term.lam (Term.letE (Term.strL "") (Term.letE (strPush (♯0) (♯2)) (Term.letE (strPush (♯1) (♯2)) (Term.letE (strEq (♯1) (♯0)) (Term.letE (♯0) (♯0))))))))

/-- The module up to and including `instDecidableEqChar`. -/
def prog_instDecidableEqChar : Program (d_instDecidableEqChar :: sig_instDecidableEqChar.decls) :=
  .cons d_instDecidableEqChar sig_instDecidableEqChar.h_names_unique tm_instDecidableEqChar prog_String_Pos_Raw_next

/-- `test3`, as a declaration of the module. -/
def d_test3 : GlobalDecl := ⟨"test3", (Ty.fn Ty.string (Ty.fn Ty.nat Ty.nat))⟩

/-- The signature `test3` is written against. -/
def sig_test3 : Sig := ⟨[d_instDecidableEqChar, d_String_Pos_Raw_next, d_String_Pos_Raw_atEnd, d__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0, d_test4_go], by decide⟩

/-- The body of `test3`. -/
def tm_test3 : Term sig_test3 [] [] (Ty.fn Ty.string (Ty.fn Ty.nat Ty.nat)) :=
  (Term.lam (Term.lam (Term.letE (Term.natL 0) (Term.letE (Term.natL 1) (Term.letE (Term.ctor (τ := (Ty.record ⟨Ty.nat, Ty.nat, [Ty.nat]⟩)) 0 [Ty.nat, Ty.nat, Ty.nat] (by rfl) (.cons (♯1) (.cons (♯2) (.cons (♯0) .nil)))) (Term.letE (Term.ctor (τ := (Ty.record ⟨Ty.nat, Ty.string, []⟩)) 0 [Ty.nat, Ty.string] (by rfl) (.cons (♯2) (.cons (♯4) .nil))) (Term.letE (Term.ap (Term.ap (Term.ap (Term.global (.there (.there (.there .here)))) (♯1)) (♯0)) (♯3)) (Term.caseTag (♯0) (Alts.cons 0 [Ty.nat, Ty.string] (by rfl) (♯0) Alts.nilFull) (by rfl)))))))))

/-- The module up to and including `test3`. -/
def prog_test3 : Program (d_test3 :: sig_test3.decls) :=
  .cons d_test3 sig_test3.h_names_unique tm_test3 prog_instDecidableEqChar

/-- `test4`, as a declaration of the module. -/
def d_test4 : GlobalDecl := ⟨"test4", (Ty.fn Ty.string Ty.nat)⟩

/-- The signature `test4` is written against. -/
def sig_test4 : Sig := ⟨[d_test3, d_instDecidableEqChar, d_String_Pos_Raw_next, d_String_Pos_Raw_atEnd, d__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0, d_test4_go], by decide⟩

/-- The body of `test4`. -/
def tm_test4 : Term sig_test4 [] [] (Ty.fn Ty.string Ty.nat) :=
  (Term.lam (Term.letE (Term.natL 0) (Term.letE (Term.ap (Term.ap (Term.ap (Term.global (.there (.there (.there (.there (.there .here)))))) (♯1)) (♯0)) (♯0)) (♯0))))

/-- The module up to and including `test4`. -/
def prog_test4 : Program (d_test4 :: sig_test4.decls) :=
  .cons d_test4 sig_test4.h_names_unique tm_test4 prog_test3

/-- `test1.go`, as a declaration of the module. -/
def d_test1_go : GlobalDecl := ⟨"test1.go", (Ty.fn Ty.string (Ty.fn Ty.char (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat))))⟩

/-- The signature `test1.go` is written against. -/
def sig_test1_go : Sig := ⟨[d_test4, d_test3, d_instDecidableEqChar, d_String_Pos_Raw_next, d_String_Pos_Raw_atEnd, d__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0, d_test4_go], by decide⟩

/-- The body of the recursion of `test1.go`. -/
def bd_test1_go : Term sig_test1_go ([Ty.string, Ty.char, Ty.nat, Ty.nat] ++ []) [⟨[Ty.string, Ty.char, Ty.nat, Ty.nat], Ty.nat⟩] Ty.nat :=
  (Term.letE (Term.ap (Term.ap (Term.global (.there (.there (.there (.there .here))))) (♯0)) (♯2)) (Term.ite (♯0) (♯4) (Term.letE (Term.ap (Term.ap (Term.global (.there (.there (.there .here)))) (♯1)) (♯3)) (Term.letE (strCharAt (♯2) (♯4)) (Term.letE (Term.ap (Term.ap (Term.global (.there (.there .here))) (♯0)) (♯4)) (Term.letE (♯0) (Term.ite (♯0) (Term.letE (Term.natL 1) (Term.letE (natAdd (♯9) (♯0)) (Term.letE (Term.selfCall .head (.cons (♯7) (.cons (♯8) (.cons (♯5) (.cons (♯0) .nil))))) (♯0)))) (Term.letE (Term.selfCall .head (.cons (♯5) (.cons (♯6) (.cons (♯3) (.cons (♯8) .nil))))) (♯0)))))))))

/-- The body of `test1.go`. -/
def tm_test1_go : Term sig_test1_go [] [] (Ty.fn Ty.string (Ty.fn Ty.char (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat)))) :=
  Term.fix [Ty.string, Ty.char, Ty.nat, Ty.nat] 1 (.cons (natSub (strUtf8ByteSize (♯0)) (♯2)) .nil) bd_test1_go (Term.natL 0)

/-- The module up to and including `test1.go`. -/
def prog_test1_go : Program (d_test1_go :: sig_test1_go.decls) :=
  .cons d_test1_go sig_test1_go.h_names_unique tm_test1_go prog_test4

/-- `test2.go`, as a declaration of the module. -/
def d_test2_go : GlobalDecl := ⟨"test2.go", (Ty.fn Ty.string (Ty.fn Ty.char (Ty.fn Ty.nat Ty.nat)))⟩

/-- The signature `test2.go` is written against. -/
def sig_test2_go : Sig := ⟨[d_test1_go, d_test4, d_test3, d_instDecidableEqChar, d_String_Pos_Raw_next, d_String_Pos_Raw_atEnd, d__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0, d_test4_go], by decide⟩

/-- The body of the recursion of `test2.go`. -/
def bd_test2_go : Term sig_test2_go ([Ty.string, Ty.char, Ty.nat] ++ []) [⟨[Ty.string, Ty.char, Ty.nat], Ty.nat⟩] Ty.nat :=
  (Term.letE (Term.ap (Term.ap (Term.global (.there (.there (.there (.there (.there .here)))))) (♯0)) (♯2)) (Term.ite (♯0) (♯3) (Term.letE (strCharAt (♯1) (♯3)) (Term.letE (Term.ap (Term.ap (Term.global (.there (.there (.there .here)))) (♯0)) (♯3)) (Term.letE (♯0) (Term.ite (♯0) (♯6) (Term.letE (Term.ap (Term.ap (Term.global (.there (.there (.there (.there .here))))) (♯4)) (♯6)) (Term.letE (Term.selfCall .head (.cons (♯5) (.cons (♯6) (.cons (♯0) .nil)))) (♯0)))))))))

/-- The body of `test2.go`. -/
def tm_test2_go : Term sig_test2_go [] [] (Ty.fn Ty.string (Ty.fn Ty.char (Ty.fn Ty.nat Ty.nat))) :=
  Term.fix [Ty.string, Ty.char, Ty.nat] 1 (.cons (natSub (strUtf8ByteSize (♯0)) (♯2)) .nil) bd_test2_go (Term.natL 0)

/-- The module up to and including `test2.go`. -/
def prog_test2_go : Program (d_test2_go :: sig_test2_go.decls) :=
  .cons d_test2_go sig_test2_go.h_names_unique tm_test2_go prog_test1_go

/-- `test1`, as a declaration of the module. -/
def d_test1 : GlobalDecl := ⟨"test1", (Ty.fn Ty.string (Ty.fn Ty.char Ty.nat))⟩

/-- The signature `test1` is written against. -/
def sig_test1 : Sig := ⟨[d_test2_go, d_test1_go, d_test4, d_test3, d_instDecidableEqChar, d_String_Pos_Raw_next, d_String_Pos_Raw_atEnd, d__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0, d_test4_go], by decide⟩

/-- The body of `test1`. -/
def tm_test1 : Term sig_test1 [] [] (Ty.fn Ty.string (Ty.fn Ty.char Ty.nat)) :=
  (Term.lam (Term.lam (Term.letE (Term.natL 0) (Term.letE (♯0) (Term.letE (Term.ap (Term.ap (Term.ap (Term.ap (Term.global (.there .here)) (♯3)) (♯2)) (♯0)) (♯1)) (♯0))))))

/-- The module up to and including `test1`. -/
def prog_test1 : Program (d_test1 :: sig_test1.decls) :=
  .cons d_test1 sig_test1.h_names_unique tm_test1 prog_test2_go

/-- `test2`, as a declaration of the module. -/
def d_test2 : GlobalDecl := ⟨"test2", (Ty.fn Ty.string (Ty.fn Ty.char Ty.nat))⟩

/-- The signature `test2` is written against. -/
def sig_test2 : Sig := ⟨[d_test1, d_test2_go, d_test1_go, d_test4, d_test3, d_instDecidableEqChar, d_String_Pos_Raw_next, d_String_Pos_Raw_atEnd, d__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0, d_test4_go], by decide⟩

/-- The body of `test2`. -/
def tm_test2 : Term sig_test2 [] [] (Ty.fn Ty.string (Ty.fn Ty.char Ty.nat)) :=
  (Term.lam (Term.lam (Term.letE (Term.natL 0) (Term.letE (♯0) (Term.letE (Term.ap (Term.ap (Term.ap (Term.global (.there .here)) (♯3)) (♯2)) (♯0)) (♯0))))))

/-- The module up to and including `test2`. -/
def prog_test2 : Program (d_test2 :: sig_test2.decls) :=
  .cons d_test2 sig_test2.h_names_unique tm_test2 prog_test1

/-- The signature of the whole module. -/
def moduleSig : Sig := ⟨[d_test2, d_test1, d_test2_go, d_test1_go, d_test4, d_test3, d_instDecidableEqChar, d_String_Pos_Raw_next, d_String_Pos_Raw_atEnd, d__private_Init_Data_Range_Basic_0_Std_Legacy_Range_forIn__loop__at__test3_spec_0, d_test4_go], by decide⟩

/-- The module as a telescope: every body is written against the declarations before it, so the call graph is acyclic by construction.  It is built one declaration at a time, above, so that no single elaboration sees the whole telescope at once. -/
def program : Program moduleSig.decls :=
  prog_test2

end ProgramSnapshotsMyStringWalk
