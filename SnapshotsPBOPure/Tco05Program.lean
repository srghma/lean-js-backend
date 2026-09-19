-- SnapshotsPBOPure.Tco05: the module as a Program of the one grammar of `LakeJs.Expr`.
-- 🎯 a public entry point of the module; 📦 a declaration the translation pulled in.
-- Every term below is a `Term`, so it is terminating by construction: the one way it
-- repeats work is `Term.fix`, whose measure it descends on at every self call.
--
-- ════ 🎯 span.go : (fn (fn int bool) (fn (array int) (fn nat (taggedUnion ()|(nat)))))
--      measure: well-founded recursion, `termination_by` transcribed verbatim; 1 component: [ ((extern⟨nat nat ⇒ nat⟩ ⬝ (extern⟨(array int) ⇒ nat⟩ ⬝ ♯1)) ⬝ ♯2) ]
-- fix ((fn int bool) (array int) nat) measure [ ((extern⟨nat nat ⇒ nat⟩ ⬝ (extern⟨(array int) ⇒ nat⟩ ⬝ ♯1)) ⬝ ♯2) ] body {
--   let ♯ := (extern⟨(array int) ⇒ nat⟩ ⬝ ♯1);
--   let ♯ := ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯3) ⬝ ♯0);
--   if ♯0 then let ♯ := ((extern⟨(array int) nat ⇒ int⟩ ⬝ ♯3) ⬝ ♯4);
--   let ♯ := (♯3 ⬝ ♯0);
--   if ♯0 then let ♯ := 1#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯7) ⬝ ♯0);
--   let ♯ := self0⟨↓⟩(♯6, ♯7, ♯0);
--   ♯0 else let ♯ := ctor1(nat)(♯6);
--   ♯0 else let ♯ := ctor0()();
--   ♯0
-- } stuck { ctor0()() }
--
-- ════ 🎯 span : (fn (fn int bool) (fn (array int) (taggedUnion ()|(nat))))
-- ƛ ƛ let ♯ := 0#;
-- let ♯ := (((@span.go ⬝ ♯2) ⬝ ♯1) ⬝ ♯0);
-- ♯0
--
--
-- ── the same program as Lean source ────────────────────────────────────
-- The trees above are this program printed in the notation of `LakeJs.ExprPretty`;
-- copy one into a `[LEAN|...]` elaboration if you want to read it there.

import LakeJs

open LakeJs LakeJs.Ty LakeJs.Expr LakeJs.Expr.Ops

namespace ProgramSnapshotsPBOPureTco05

/-- `span.go`, as a declaration of the module. -/
def d_span_go : GlobalDecl := ⟨"span.go", (Ty.fn (Ty.fn Ty.int Ty.bool) (Ty.fn (Ty.array Ty.int) (Ty.fn Ty.nat (Ty.option Ty.nat))))⟩

/-- The signature `span.go` is written against. -/
def sig_span_go : Sig := ⟨[], by decide⟩

/-- The body of the recursion of `span.go`. -/
def bd_span_go : Term sig_span_go ([(Ty.fn Ty.int Ty.bool), (Ty.array Ty.int), Ty.nat] ++ []) [⟨[(Ty.fn Ty.int Ty.bool), (Ty.array Ty.int), Ty.nat], (Ty.option Ty.nat)⟩] (Ty.option Ty.nat) :=
  (Term.letE (arrLen (♯1)) (Term.letE (natLt (♯3) (♯0)) (Term.ite (♯0) (Term.letE (arrGet (♯3) (♯4)) (Term.letE (Term.ap (♯3) (♯0)) (Term.ite (♯0) (Term.letE (Term.natL 1) (Term.letE (natAdd (♯7) (♯0)) (Term.letE (Term.selfCall .head (.cons (♯6) (.cons (♯7) (.cons (♯0) .nil)))) (♯0)))) (Term.letE (Term.ctor (τ := (Ty.option Ty.nat)) 1 [Ty.nat] (by rfl) (.cons (♯6) .nil)) (♯0))))) (Term.letE (Term.ctor (τ := (Ty.option Ty.nat)) 0 [] (by rfl) .nil) (♯0)))))

/-- The body of `span.go`. -/
def tm_span_go : Term sig_span_go [] [] (Ty.fn (Ty.fn Ty.int Ty.bool) (Ty.fn (Ty.array Ty.int) (Ty.fn Ty.nat (Ty.option Ty.nat)))) :=
  Term.fix [(Ty.fn Ty.int Ty.bool), (Ty.array Ty.int), Ty.nat] 1 (.cons (natSub (arrLen (♯1)) (♯2)) .nil) bd_span_go (Term.ctor (τ := (Ty.option Ty.nat)) 0 [] (by rfl) .nil)

/-- The module up to and including `span.go`. -/
def prog_span_go : Program (d_span_go :: sig_span_go.decls) :=
  .cons d_span_go sig_span_go.h_names_unique tm_span_go Program.nil

/-- `span`, as a declaration of the module. -/
def d_span : GlobalDecl := ⟨"span", (Ty.fn (Ty.fn Ty.int Ty.bool) (Ty.fn (Ty.array Ty.int) (Ty.option Ty.nat)))⟩

/-- The signature `span` is written against. -/
def sig_span : Sig := ⟨[d_span_go], by decide⟩

/-- The body of `span`. -/
def tm_span : Term sig_span [] [] (Ty.fn (Ty.fn Ty.int Ty.bool) (Ty.fn (Ty.array Ty.int) (Ty.option Ty.nat))) :=
  (Term.lam (Term.lam (Term.letE (Term.natL 0) (Term.letE (Term.ap (Term.ap (Term.ap (Term.global .here) (♯2)) (♯1)) (♯0)) (♯0)))))

/-- The module up to and including `span`. -/
def prog_span : Program (d_span :: sig_span.decls) :=
  .cons d_span sig_span.h_names_unique tm_span prog_span_go

/-- The signature of the whole module. -/
def moduleSig : Sig := ⟨[d_span, d_span_go], by decide⟩

/-- The module as a telescope: every body is written against the declarations before it, so the call graph is acyclic by construction.  It is built one declaration at a time, above, so that no single elaboration sees the whole telescope at once. -/
def program : Program moduleSig.decls :=
  prog_span

end ProgramSnapshotsPBOPureTco05
