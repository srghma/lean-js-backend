-- SnapshotsMy.GcdEntry: the module as a Program of the one grammar of `LakeJs.Expr`.
-- 🎯 a public entry point of the module; 📦 a declaration the translation pulled in.
-- Every term below is a `Term`, so it is terminating by construction: the one way it
-- repeats work is `Term.fix`, whose measure it descends on at every self call.
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
-- ════ 🎯 gcd2 : (fn nat (fn nat nat))
-- ƛ ƛ let ♯ := ((@Nat.gcd ⬝ ♯1) ⬝ ♯0);
-- ♯0
--
-- ════ 🎯 run : nat
-- let ♯ := 48#;
-- let ♯ := 18#;
-- let ♯ := ((@Nat.gcd ⬝ ♯1) ⬝ ♯0);
-- ♯0
--
--
-- ── the same program as Lean source ────────────────────────────────────
-- The trees above are this program printed in the notation of `LakeJs.ExprPretty`;
-- copy one into a `[LEAN|...]` elaboration if you want to read it there.

import LakeJs

open LakeJs LakeJs.Ty LakeJs.Expr LakeJs.Expr.Ops

namespace ProgramSnapshotsMyGcdEntry

/-- `Nat.gcd`, as a declaration of the module. -/
def d_Nat_gcd : GlobalDecl := ⟨"Nat.gcd", (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat))⟩

/-- The signature `Nat.gcd` is written against. -/
def sig_Nat_gcd : Sig := ⟨[], by decide⟩

/-- The body of the recursion of `Nat.gcd`. -/
def bd_Nat_gcd : Term sig_Nat_gcd ([Ty.nat, Ty.nat] ++ []) [⟨[Ty.nat, Ty.nat], Ty.nat⟩] Ty.nat :=
  (Term.letE (Term.natL 0) (Term.letE (natEq (♯1) (♯0)) (Term.ite (♯0) (♯3) (Term.letE (natMod (♯3) (♯2)) (Term.letE (Term.selfCall .head (.cons (♯0) (.cons (♯3) .nil))) (♯0))))))

/-- The body of `Nat.gcd`. -/
def tm_Nat_gcd : Term sig_Nat_gcd [] [] (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat)) :=
  Term.fix [Ty.nat, Ty.nat] 1 (.cons (♯0) .nil) bd_Nat_gcd (Term.natL 0)

/-- The module up to and including `Nat.gcd`. -/
def prog_Nat_gcd : Program (d_Nat_gcd :: sig_Nat_gcd.decls) :=
  .cons d_Nat_gcd sig_Nat_gcd.h_names_unique tm_Nat_gcd Program.nil

/-- `gcd2`, as a declaration of the module. -/
def d_gcd2 : GlobalDecl := ⟨"gcd2", (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat))⟩

/-- The signature `gcd2` is written against. -/
def sig_gcd2 : Sig := ⟨[d_Nat_gcd], by decide⟩

/-- The body of `gcd2`. -/
def tm_gcd2 : Term sig_gcd2 [] [] (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat)) :=
  (Term.lam (Term.lam (Term.letE (Term.ap (Term.ap (Term.global .here) (♯1)) (♯0)) (♯0))))

/-- The module up to and including `gcd2`. -/
def prog_gcd2 : Program (d_gcd2 :: sig_gcd2.decls) :=
  .cons d_gcd2 sig_gcd2.h_names_unique tm_gcd2 prog_Nat_gcd

/-- `run`, as a declaration of the module. -/
def d_run : GlobalDecl := ⟨"run", Ty.nat⟩

/-- The signature `run` is written against. -/
def sig_run : Sig := ⟨[d_gcd2, d_Nat_gcd], by decide⟩

/-- The body of `run`. -/
def tm_run : Term sig_run [] [] Ty.nat :=
  (Term.letE (Term.natL 48) (Term.letE (Term.natL 18) (Term.letE (Term.ap (Term.ap (Term.global (.there .here)) (♯1)) (♯0)) (♯0))))

/-- The module up to and including `run`. -/
def prog_run : Program (d_run :: sig_run.decls) :=
  .cons d_run sig_run.h_names_unique tm_run prog_gcd2

/-- The signature of the whole module. -/
def moduleSig : Sig := ⟨[d_run, d_gcd2, d_Nat_gcd], by decide⟩

/-- The module as a telescope: every body is written against the declarations before it, so the call graph is acyclic by construction.  It is built one declaration at a time, above, so that no single elaboration sees the whole telescope at once. -/
def program : Program moduleSig.decls :=
  prog_run

end ProgramSnapshotsMyGcdEntry
