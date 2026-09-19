-- SnapshotsMy.MutualSlots: the module as a Program of the one grammar of `LakeJs.Expr`.
-- 🎯 a public entry point of the module; 📦 a declaration the translation pulled in.
-- Every term below is a `Term`, so it is terminating by construction: the one way it
-- repeats work is `Term.fix`, whose measure it descends on at every self call.
--
-- ════ 📦 walkStr & walkNat (clique) : (fn nat (fn nat (fn string (fn nat (fn nat nat)))))
--      measure: mutual clique of 2 members; 2 components: [ if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then ♯1 else ♯3, ((extern⟨nat nat ⇒ nat⟩ ⬝ 1#) ⬝ ♯0) ] — the measure of the member the tag selects, then its phase
-- fix (nat nat string nat nat) measure [ if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then ♯1 else ♯3, ((extern⟨nat nat ⇒ nat⟩ ⬝ 1#) ⬝ ♯0) ] body {
--   if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯1) ⬝ 0#) then let ♯ := (extern⟨string ⇒ nat⟩ ⬝ ♯2);
--   ♯0 else let ♯ := (extern⟨string ⇒ nat⟩ ⬝ ♯2);
--   let ♯ := 1#;
--   let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯1) ⬝ ♯0);
--   let ♯ := self0⟨↓⟩(1#, 0#, "", ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯4) ⬝ 1#), ♯0);
--   ♯0 else if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯3) ⬝ 0#) then ♯4 else let ♯ := 0#;
--   let ♯ := ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯5) ⬝ ♯0);
--   let ♯ := ♯0;
--   if ♯0 then let ♯ := "";
--   let ♯ := self0⟨↓⟩(0#, ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯7) ⬝ 1#), ♯0, 0#, 0#);
--   ♯0 else let ♯ := "xy";
--   let ♯ := self0⟨↓⟩(0#, ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯7) ⬝ 1#), ♯0, 0#, 0#);
--   ♯0
-- } stuck { 0# }
--
-- ════ 🎯 walkStr : (fn nat (fn string nat))
-- ƛ ƛ (((((@walkStr & walkNat (clique) ⬝ 0#) ⬝ ♯1) ⬝ ♯0) ⬝ 0#) ⬝ 0#)
--
-- ════ 🎯 walkNat : (fn nat (fn nat nat))
-- ƛ ƛ (((((@walkStr & walkNat (clique) ⬝ 1#) ⬝ 0#) ⬝ "") ⬝ ♯1) ⬝ ♯0)
--
--
-- ── the same program as Lean source ────────────────────────────────────
-- The trees above are this program printed in the notation of `LakeJs.ExprPretty`;
-- copy one into a `[LEAN|...]` elaboration if you want to read it there.

import LakeJs

open LakeJs LakeJs.Ty LakeJs.Expr LakeJs.Expr.Ops

namespace ProgramSnapshotsMyMutualSlots

/-- `walkStr & walkNat (clique)`, as a declaration of the module. -/
def d_walkStr___walkNat__clique_ : GlobalDecl := ⟨"walkStr & walkNat (clique)", (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.string (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat)))))⟩

/-- The signature `walkStr & walkNat (clique)` is written against. -/
def sig_walkStr___walkNat__clique_ : Sig := ⟨[], by decide⟩

/-- The body of the recursion of `walkStr & walkNat (clique)`. -/
def bd_walkStr___walkNat__clique_ : Term sig_walkStr___walkNat__clique_ ([Ty.nat, Ty.nat, Ty.string, Ty.nat, Ty.nat] ++ []) [⟨[Ty.nat, Ty.nat, Ty.string, Ty.nat, Ty.nat], Ty.nat⟩] Ty.nat :=
  (Term.ite (natEq (♯0) (Term.natL 0)) (Term.ite (natEq (♯1) (Term.natL 0)) (Term.letE (strLength (♯2)) (♯0)) (Term.letE (strLength (♯2)) (Term.letE (Term.natL 1) (Term.letE (natAdd (♯1) (♯0)) (Term.letE (Term.selfCall .head (.cons (Term.natL 1) (.cons (Term.natL 0) (.cons (Term.strL "") (.cons (natSub (♯4) (Term.natL 1)) (.cons (♯0) .nil)))))) (♯0)))))) (Term.ite (natEq (♯3) (Term.natL 0)) (♯4) (Term.letE (Term.natL 0) (Term.letE (natEq (♯5) (♯0)) (Term.letE (♯0) (Term.ite (♯0) (Term.letE (Term.strL "") (Term.letE (Term.selfCall .head (.cons (Term.natL 0) (.cons (natSub (♯7) (Term.natL 1)) (.cons (♯0) (.cons (Term.natL 0) (.cons (Term.natL 0) .nil)))))) (♯0))) (Term.letE (Term.strL "xy") (Term.letE (Term.selfCall .head (.cons (Term.natL 0) (.cons (natSub (♯7) (Term.natL 1)) (.cons (♯0) (.cons (Term.natL 0) (.cons (Term.natL 0) .nil)))))) (♯0)))))))))

/-- The body of `walkStr & walkNat (clique)`. -/
def tm_walkStr___walkNat__clique_ : Term sig_walkStr___walkNat__clique_ [] [] (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.string (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat))))) :=
  Term.fix [Ty.nat, Ty.nat, Ty.string, Ty.nat, Ty.nat] 2 (.cons (Term.ite (natEq (♯0) (Term.natL 0)) (♯1) (♯3)) (.cons (natSub (Term.natL 1) (♯0)) .nil)) bd_walkStr___walkNat__clique_ (Term.natL 0)

/-- The module up to and including `walkStr & walkNat (clique)`. -/
def prog_walkStr___walkNat__clique_ : Program (d_walkStr___walkNat__clique_ :: sig_walkStr___walkNat__clique_.decls) :=
  .cons d_walkStr___walkNat__clique_ sig_walkStr___walkNat__clique_.h_names_unique tm_walkStr___walkNat__clique_ Program.nil

/-- `walkStr`, as a declaration of the module. -/
def d_walkStr : GlobalDecl := ⟨"walkStr", (Ty.fn Ty.nat (Ty.fn Ty.string Ty.nat))⟩

/-- The signature `walkStr` is written against. -/
def sig_walkStr : Sig := ⟨[d_walkStr___walkNat__clique_], by decide⟩

/-- The body of `walkStr`. -/
def tm_walkStr : Term sig_walkStr [] [] (Ty.fn Ty.nat (Ty.fn Ty.string Ty.nat)) :=
  (Term.lam (Term.lam (Term.ap (Term.ap (Term.ap (Term.ap (Term.ap (Term.global .here) (Term.natL 0)) (♯1)) (♯0)) (Term.natL 0)) (Term.natL 0))))

/-- The module up to and including `walkStr`. -/
def prog_walkStr : Program (d_walkStr :: sig_walkStr.decls) :=
  .cons d_walkStr sig_walkStr.h_names_unique tm_walkStr prog_walkStr___walkNat__clique_

/-- `walkNat`, as a declaration of the module. -/
def d_walkNat : GlobalDecl := ⟨"walkNat", (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat))⟩

/-- The signature `walkNat` is written against. -/
def sig_walkNat : Sig := ⟨[d_walkStr, d_walkStr___walkNat__clique_], by decide⟩

/-- The body of `walkNat`. -/
def tm_walkNat : Term sig_walkNat [] [] (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat)) :=
  (Term.lam (Term.lam (Term.ap (Term.ap (Term.ap (Term.ap (Term.ap (Term.global (.there .here)) (Term.natL 1)) (Term.natL 0)) (Term.strL "")) (♯1)) (♯0))))

/-- The module up to and including `walkNat`. -/
def prog_walkNat : Program (d_walkNat :: sig_walkNat.decls) :=
  .cons d_walkNat sig_walkNat.h_names_unique tm_walkNat prog_walkStr

/-- The signature of the whole module. -/
def moduleSig : Sig := ⟨[d_walkNat, d_walkStr, d_walkStr___walkNat__clique_], by decide⟩

/-- The module as a telescope: every body is written against the declarations before it, so the call graph is acyclic by construction.  It is built one declaration at a time, above, so that no single elaboration sees the whole telescope at once. -/
def program : Program moduleSig.decls :=
  prog_walkNat

end ProgramSnapshotsMyMutualSlots
