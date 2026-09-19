-- SnapshotsPBOPure.Tco03: the module as a Program of the one grammar of `LakeJs.Expr`.
-- 🎯 a public entry point of the module; 📦 a declaration the translation pulled in.
-- Every term below is a `Term`, so it is terminating by construction: the one way it
-- repeats work is `Term.fix`, whose measure it descends on at every self call.
--
-- ════ 📦 go & k (clique) : (fn nat (fn nat (fn nat nat)))
--      measure: mutual clique of 2 members; 2 components: [ if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then ♯1 else ♯2, ((extern⟨nat nat ⇒ nat⟩ ⬝ 1#) ⬝ ♯0) ] — the measure of the member the tag selects, then its phase
-- fix (nat nat nat) measure [ if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then ♯1 else ♯2, ((extern⟨nat nat ⇒ nat⟩ ⬝ 1#) ⬝ ♯0) ] body {
--   if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then let ♯ := 0#;
--   let ♯ := ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯2) ⬝ ♯0);
--   if ♯0 then ♯3 else let ♯ := 100#;
--   let ♯ := ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯4) ⬝ ♯0);
--   if ♯0 then let ♯ := 1#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯6) ⬝ ♯0);
--   let ♯ := self0⟨↓⟩(0#, ♯0, 0#);
--   ♯0 else let ♯ := 1#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯6) ⬝ ♯0);
--   let ♯ := self0⟨↓⟩(1#, 0#, ♯0);
--   ♯0 else let ♯ := 100#;
--   let ♯ := ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯3) ⬝ ♯0);
--   if ♯0 then let ♯ := 1#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯5) ⬝ ♯0);
--   let ♯ := self0⟨↓⟩(0#, ♯0, 0#);
--   ♯0 else let ♯ := 900#;
--   let ♯ := ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯5) ⬝ ♯0);
--   if ♯0 then let ♯ := 42#;
--   ♯0 else let ♯ := 1#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯7) ⬝ ♯0);
--   let ♯ := self0⟨↓⟩(1#, 0#, ♯0);
--   ♯0
-- } stuck { 0# }
--
-- ════ 🎯 go : (fn nat nat)
-- ƛ (((@go & k (clique) ⬝ 0#) ⬝ ♯0) ⬝ 0#)
--
-- ════ 🎯 k : (fn nat nat)
-- ƛ (((@go & k (clique) ⬝ 1#) ⬝ 0#) ⬝ ♯0)
--
--
-- ── the same program as Lean source ────────────────────────────────────
-- The trees above are this program printed in the notation of `LakeJs.ExprPretty`;
-- copy one into a `[LEAN|...]` elaboration if you want to read it there.

import LakeJs

open LakeJs LakeJs.Ty LakeJs.Expr LakeJs.Expr.Ops

namespace ProgramSnapshotsPBOPureTco03

/-- `go & k (clique)`, as a declaration of the module. -/
def d_go___k__clique_ : GlobalDecl := ⟨"go & k (clique)", (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat)))⟩

/-- The signature `go & k (clique)` is written against. -/
def sig_go___k__clique_ : Sig := ⟨[], by decide⟩

/-- The body of the recursion of `go & k (clique)`. -/
def bd_go___k__clique_ : Term sig_go___k__clique_ ([Ty.nat, Ty.nat, Ty.nat] ++ []) [⟨[Ty.nat, Ty.nat, Ty.nat], Ty.nat⟩] Ty.nat :=
  (Term.ite (natEq (♯0) (Term.natL 0)) (Term.letE (Term.natL 0) (Term.letE (natEq (♯2) (♯0)) (Term.ite (♯0) (♯3) (Term.letE (Term.natL 100) (Term.letE (natLe (♯4) (♯0)) (Term.ite (♯0) (Term.letE (Term.natL 1) (Term.letE (natSub (♯6) (♯0)) (Term.letE (Term.selfCall .head (.cons (Term.natL 0) (.cons (♯0) (.cons (Term.natL 0) .nil)))) (♯0)))) (Term.letE (Term.natL 1) (Term.letE (natSub (♯6) (♯0)) (Term.letE (Term.selfCall .head (.cons (Term.natL 1) (.cons (Term.natL 0) (.cons (♯0) .nil)))) (♯0)))))))))) (Term.letE (Term.natL 100) (Term.letE (natEq (♯3) (♯0)) (Term.ite (♯0) (Term.letE (Term.natL 1) (Term.letE (natSub (♯5) (♯0)) (Term.letE (Term.selfCall .head (.cons (Term.natL 0) (.cons (♯0) (.cons (Term.natL 0) .nil)))) (♯0)))) (Term.letE (Term.natL 900) (Term.letE (natEq (♯5) (♯0)) (Term.ite (♯0) (Term.letE (Term.natL 42) (♯0)) (Term.letE (Term.natL 1) (Term.letE (natSub (♯7) (♯0)) (Term.letE (Term.selfCall .head (.cons (Term.natL 1) (.cons (Term.natL 0) (.cons (♯0) .nil)))) (♯0)))))))))))

/-- The body of `go & k (clique)`. -/
def tm_go___k__clique_ : Term sig_go___k__clique_ [] [] (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat))) :=
  Term.fix [Ty.nat, Ty.nat, Ty.nat] 2 (.cons (Term.ite (natEq (♯0) (Term.natL 0)) (♯1) (♯2)) (.cons (natSub (Term.natL 1) (♯0)) .nil)) bd_go___k__clique_ (Term.natL 0)

/-- The module up to and including `go & k (clique)`. -/
def prog_go___k__clique_ : Program (d_go___k__clique_ :: sig_go___k__clique_.decls) :=
  .cons d_go___k__clique_ sig_go___k__clique_.h_names_unique tm_go___k__clique_ Program.nil

/-- `go`, as a declaration of the module. -/
def d_go : GlobalDecl := ⟨"go", (Ty.fn Ty.nat Ty.nat)⟩

/-- The signature `go` is written against. -/
def sig_go : Sig := ⟨[d_go___k__clique_], by decide⟩

/-- The body of `go`. -/
def tm_go : Term sig_go [] [] (Ty.fn Ty.nat Ty.nat) :=
  (Term.lam (Term.ap (Term.ap (Term.ap (Term.global .here) (Term.natL 0)) (♯0)) (Term.natL 0)))

/-- The module up to and including `go`. -/
def prog_go : Program (d_go :: sig_go.decls) :=
  .cons d_go sig_go.h_names_unique tm_go prog_go___k__clique_

/-- `k`, as a declaration of the module. -/
def d_k : GlobalDecl := ⟨"k", (Ty.fn Ty.nat Ty.nat)⟩

/-- The signature `k` is written against. -/
def sig_k : Sig := ⟨[d_go, d_go___k__clique_], by decide⟩

/-- The body of `k`. -/
def tm_k : Term sig_k [] [] (Ty.fn Ty.nat Ty.nat) :=
  (Term.lam (Term.ap (Term.ap (Term.ap (Term.global (.there .here)) (Term.natL 1)) (Term.natL 0)) (♯0)))

/-- The module up to and including `k`. -/
def prog_k : Program (d_k :: sig_k.decls) :=
  .cons d_k sig_k.h_names_unique tm_k prog_go

/-- The signature of the whole module. -/
def moduleSig : Sig := ⟨[d_k, d_go, d_go___k__clique_], by decide⟩

/-- The module as a telescope: every body is written against the declarations before it, so the call graph is acyclic by construction.  It is built one declaration at a time, above, so that no single elaboration sees the whole telescope at once. -/
def program : Program moduleSig.decls :=
  prog_k

end ProgramSnapshotsPBOPureTco03
