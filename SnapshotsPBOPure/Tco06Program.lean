-- SnapshotsPBOPure.Tco06: the module as a Program of the one grammar of `LakeJs.Expr`.
-- 🎯 a public entry point of the module; 📦 a declaration the translation pulled in.
-- Every term below is a `Term`, so it is terminating by construction: the one way it
-- repeats work is `Term.fix`, whose measure it descends on at every self call.
--
-- ════ 📦 f & g (clique) : (fn nat (fn nat (fn int (fn int (fn nat (fn int int))))))
--      measure: mutual clique of 2 members; 2 components: [ if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then ♯1 else ♯4, ((extern⟨nat nat ⇒ nat⟩ ⬝ 1#) ⬝ ♯0) ] — the measure of the member the tag selects, then its phase
-- fix (nat nat int int nat int) measure [ if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then ♯1 else ♯4, ((extern⟨nat nat ⇒ nat⟩ ⬝ 1#) ⬝ ♯0) ] body {
--   if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯1) ⬝ 0#) then let ♯ := ((extern⟨int int ⇒ int⟩ ⬝ ♯2) ⬝ ♯3);
--   ♯0 else let ♯ := ((extern⟨int int ⇒ int⟩ ⬝ ♯2) ⬝ ♯3);
--   let ♯ := self0⟨↓⟩(1#, 0#, 0i, 0i, ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ 1#), ♯0);
--   ♯0 else if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯4) ⬝ 0#) then ♯5 else let ♯ := 1#;
--   let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--   let ♯ := ((extern⟨int int ⇒ int⟩ ⬝ ♯7) ⬝ ♯0);
--   let ♯ := self0⟨↓⟩(0#, ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯7) ⬝ 1#), ♯8, ♯0, 0#, 0i);
--   ♯0
-- } stuck { 0i }
--
-- ════ 🎯 f : (fn nat (fn int (fn int int)))
-- ƛ ƛ ƛ ((((((@f & g (clique) ⬝ 0#) ⬝ ♯2) ⬝ ♯1) ⬝ ♯0) ⬝ 0#) ⬝ 0i)
--
-- ════ 🎯 g : (fn nat (fn int int))
-- ƛ ƛ ((((((@f & g (clique) ⬝ 1#) ⬝ 0#) ⬝ 0i) ⬝ 0i) ⬝ ♯1) ⬝ ♯0)
--
--
-- ── the same program as Lean source ────────────────────────────────────
-- The trees above are this program printed in the notation of `LakeJs.ExprPretty`;
-- copy one into a `[LEAN|...]` elaboration if you want to read it there.

import LakeJs

open LakeJs LakeJs.Ty LakeJs.Expr LakeJs.Expr.Ops

namespace ProgramSnapshotsPBOPureTco06

/-- `f & g (clique)`, as a declaration of the module. -/
def d_f___g__clique_ : GlobalDecl := ⟨"f & g (clique)", (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.int (Ty.fn Ty.int (Ty.fn Ty.nat (Ty.fn Ty.int Ty.int))))))⟩

/-- The signature `f & g (clique)` is written against. -/
def sig_f___g__clique_ : Sig := ⟨[], by decide⟩

/-- The body of the recursion of `f & g (clique)`. -/
def bd_f___g__clique_ : Term sig_f___g__clique_ ([Ty.nat, Ty.nat, Ty.int, Ty.int, Ty.nat, Ty.int] ++ []) [⟨[Ty.nat, Ty.nat, Ty.int, Ty.int, Ty.nat, Ty.int], Ty.int⟩] Ty.int :=
  (Term.ite (natEq (♯0) (Term.natL 0)) (Term.ite (natEq (♯1) (Term.natL 0)) (Term.letE (intAdd (♯2) (♯3)) (♯0)) (Term.letE (intAdd (♯2) (♯3)) (Term.letE (Term.selfCall .head (.cons (Term.natL 1) (.cons (Term.natL 0) (.cons (Term.intL (0)) (.cons (Term.intL (0)) (.cons (natSub (♯2) (Term.natL 1)) (.cons (♯0) .nil))))))) (♯0)))) (Term.ite (natEq (♯4) (Term.natL 0)) (♯5) (Term.letE (Term.natL 1) (Term.letE (natToInt (♯0)) (Term.letE (intAdd (♯7) (♯0)) (Term.letE (Term.selfCall .head (.cons (Term.natL 0) (.cons (natSub (♯7) (Term.natL 1)) (.cons (♯8) (.cons (♯0) (.cons (Term.natL 0) (.cons (Term.intL (0)) .nil))))))) (♯0)))))))

/-- The body of `f & g (clique)`. -/
def tm_f___g__clique_ : Term sig_f___g__clique_ [] [] (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.int (Ty.fn Ty.int (Ty.fn Ty.nat (Ty.fn Ty.int Ty.int)))))) :=
  Term.fix [Ty.nat, Ty.nat, Ty.int, Ty.int, Ty.nat, Ty.int] 2 (.cons (Term.ite (natEq (♯0) (Term.natL 0)) (♯1) (♯4)) (.cons (natSub (Term.natL 1) (♯0)) .nil)) bd_f___g__clique_ (Term.intL (0))

/-- The module up to and including `f & g (clique)`. -/
def prog_f___g__clique_ : Program (d_f___g__clique_ :: sig_f___g__clique_.decls) :=
  .cons d_f___g__clique_ sig_f___g__clique_.h_names_unique tm_f___g__clique_ Program.nil

/-- `f`, as a declaration of the module. -/
def d_f : GlobalDecl := ⟨"f", (Ty.fn Ty.nat (Ty.fn Ty.int (Ty.fn Ty.int Ty.int)))⟩

/-- The signature `f` is written against. -/
def sig_f : Sig := ⟨[d_f___g__clique_], by decide⟩

/-- The body of `f`. -/
def tm_f : Term sig_f [] [] (Ty.fn Ty.nat (Ty.fn Ty.int (Ty.fn Ty.int Ty.int))) :=
  (Term.lam (Term.lam (Term.lam (Term.ap (Term.ap (Term.ap (Term.ap (Term.ap (Term.ap (Term.global .here) (Term.natL 0)) (♯2)) (♯1)) (♯0)) (Term.natL 0)) (Term.intL (0))))))

/-- The module up to and including `f`. -/
def prog_f : Program (d_f :: sig_f.decls) :=
  .cons d_f sig_f.h_names_unique tm_f prog_f___g__clique_

/-- `g`, as a declaration of the module. -/
def d_g : GlobalDecl := ⟨"g", (Ty.fn Ty.nat (Ty.fn Ty.int Ty.int))⟩

/-- The signature `g` is written against. -/
def sig_g : Sig := ⟨[d_f, d_f___g__clique_], by decide⟩

/-- The body of `g`. -/
def tm_g : Term sig_g [] [] (Ty.fn Ty.nat (Ty.fn Ty.int Ty.int)) :=
  (Term.lam (Term.lam (Term.ap (Term.ap (Term.ap (Term.ap (Term.ap (Term.ap (Term.global (.there .here)) (Term.natL 1)) (Term.natL 0)) (Term.intL (0))) (Term.intL (0))) (♯1)) (♯0))))

/-- The module up to and including `g`. -/
def prog_g : Program (d_g :: sig_g.decls) :=
  .cons d_g sig_g.h_names_unique tm_g prog_f

/-- The signature of the whole module. -/
def moduleSig : Sig := ⟨[d_g, d_f, d_f___g__clique_], by decide⟩

/-- The module as a telescope: every body is written against the declarations before it, so the call graph is acyclic by construction.  It is built one declaration at a time, above, so that no single elaboration sees the whole telescope at once. -/
def program : Program moduleSig.decls :=
  prog_g

end ProgramSnapshotsPBOPureTco06
