-- SnapshotsPBOPure.RecursionSchemes01: the module as a Program of the one grammar of `LakeJs.Expr`.
-- 🎯 a public entry point of the module; 📦 a declaration the translation pulled in.
-- Every term below is a `Term`, so it is terminating by construction: the one way it
-- repeats work is `Term.fix`, whose measure it descends on at every self call.
-- outside the language: `instFunctorExprF`: the result type of `instFunctorExprF`, `Functor ExprF`, is not one the front end translates
-- outside the language: `mapExprF`: `mapExprF` is polymorphic, and the type language is monomorphic: it is compiled once per instantiation a caller uses, and this module has no call of it the front end could read one off
-- outside the language: `ExprF.ctorElim`: `ExprF.ctorElim` is polymorphic, and the type language is monomorphic: it is compiled once per instantiation a caller uses, and this module has no call of it the front end could read one off
-- outside the language: `ExprF.ctorIdx`: `ExprF.ctorIdx` is polymorphic, and the type language is monomorphic: it is compiled once per instantiation a caller uses, and this module has no call of it the front end could read one off
-- outside the language: `ExprF.Add.elim`: `ExprF.Add.elim` is polymorphic, and the type language is monomorphic: it is compiled once per instantiation a caller uses, and this module has no call of it the front end could read one off
-- outside the language: `ExprF.Lit.elim`: `ExprF.Lit.elim` is polymorphic, and the type language is monomorphic: it is compiled once per instantiation a caller uses, and this module has no call of it the front end could read one off
-- outside the language: `ExprF.Mul.elim`: `ExprF.Mul.elim` is polymorphic, and the type language is monomorphic: it is compiled once per instantiation a caller uses, and this module has no call of it the front end could read one off
--
-- ════ 🎯 bump : (fn (taggedUnion (int)|(int int)|(int int)) (taggedUnion (int)|(int int)|(int int)))
-- ƛ case ♯0 of
--   | 0(int) => let ♯ := 1#;
--     let ♯ := (extern⟨nat ⇒ int⟩ ⬝ ♯0);
--     let ♯ := ((extern⟨int int ⇒ int⟩ ⬝ ♯2) ⬝ ♯0);
--     let ♯ := ctor0(int)(♯0);
--     ♯0
--   | _ => ♯0
--
--
-- ════ 🎯 eval : (fn (taggedUnion (int)|(int int)|(int int)) int)
-- ƛ case ♯0 of
--   | 0(int) => ♯0
--   | 1(int int) => let ♯ := ((extern⟨int int ⇒ int⟩ ⬝ ♯0) ⬝ ♯1);
--     ♯0
--   | 2(int int) => let ♯ := ((extern⟨int int ⇒ int⟩ ⬝ ♯0) ⬝ ♯1);
--     ♯0
--
--
-- ════ 📦 cata @ Int & cataMap @ Int (clique) : (fn nat (fn (fn (taggedUnion (int)|(int int)|(int int)) int) (fn (recTaggedUnion (int)|(self#0 self#0)|(self#0 self#0)) (fn (fn (taggedUnion (int)|(int int)|(int int)) int) (fn (recTaggedUnion (int)|(self#0 self#0)|(self#0 self#0)) (taggedUnion (int)|((taggedUnion (int)|(int int)|(int int)))))))))
--      measure: mutual clique of 2 members; 2 components: [ if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then size(♯2) else size(♯4), ((extern⟨nat nat ⇒ nat⟩ ⬝ 1#) ⬝ ♯0) ] — the measure of the member the tag selects, then its phase
-- fix (nat (fn (taggedUnion (int)|(int int)|(int int)) int) (recTaggedUnion (int)|(self#0 self#0)|(self#0 self#0)) (fn (taggedUnion (int)|(int int)|(int int)) int) (recTaggedUnion (int)|(self#0 self#0)|(self#0 self#0))) measure [ if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then size(♯2) else size(♯4), ((extern⟨nat nat ⇒ nat⟩ ⬝ 1#) ⬝ ♯0) ] body {
--   if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then ctor0(int)(let ♯ := case self0⟨↓⟩(1#, ƛ 0i, ctor0(int)(0i), ♯1, ♯2) of
--     | 1((taggedUnion (int)|(int int)|(int int))) => ♯0
--     | _ => ctor0(int)(0i)
-- ;
--   let ♯ := (♯2 ⬝ ♯0);
--   ♯0) else ctor1((taggedUnion (int)|(int int)|(int int)))(case ♯4 of
--     | 0(int) => let ♯ := ctor0(int)(♯0);
--       ♯0
--     | 1((recTaggedUnion (int)|(self#0 self#0)|(self#0 self#0)) (recTaggedUnion (int)|(self#0 self#0)|(self#0 self#0))) => let ♯ := case self0⟨↓⟩(0#, ♯5, ♯0, ƛ 0i, ctor0(int)(0i)) of
--         | 0(int) => ♯0
--         | _ => 0i
-- ;
--       let ♯ := case self0⟨↓⟩(0#, ♯6, ♯2, ƛ 0i, ctor0(int)(0i)) of
--         | 0(int) => ♯0
--         | _ => 0i
-- ;
--       let ♯ := ctor1(int int)(♯1, ♯0);
--       ♯0
--     | 2((recTaggedUnion (int)|(self#0 self#0)|(self#0 self#0)) (recTaggedUnion (int)|(self#0 self#0)|(self#0 self#0))) => let ♯ := case self0⟨↓⟩(0#, ♯5, ♯0, ƛ 0i, ctor0(int)(0i)) of
--         | 0(int) => ♯0
--         | _ => 0i
-- ;
--       let ♯ := case self0⟨↓⟩(0#, ♯6, ♯2, ƛ 0i, ctor0(int)(0i)) of
--         | 0(int) => ♯0
--         | _ => 0i
-- ;
--       let ♯ := ctor2(int int)(♯1, ♯0);
--       ♯0
-- )
-- } stuck { ctor0(int)(0i) }
--
-- ════ 🎯 cata @ Int : (fn (fn (taggedUnion (int)|(int int)|(int int)) int) (fn (recTaggedUnion (int)|(self#0 self#0)|(self#0 self#0)) int))
-- ƛ ƛ case (((((@cata @ Int & cataMap @ Int (clique) ⬝ 0#) ⬝ ♯1) ⬝ ♯0) ⬝ ƛ 0i) ⬝ ctor0(int)(0i)) of
--   | 0(int) => ♯0
--   | _ => 0i
--
--
-- ════ 🎯 cataMap @ Int : (fn (fn (taggedUnion (int)|(int int)|(int int)) int) (fn (recTaggedUnion (int)|(self#0 self#0)|(self#0 self#0)) (taggedUnion (int)|(int int)|(int int))))
-- ƛ ƛ case (((((@cata @ Int & cataMap @ Int (clique) ⬝ 1#) ⬝ ƛ 0i) ⬝ ctor0(int)(0i)) ⬝ ♯1) ⬝ ♯0) of
--   | 1((taggedUnion (int)|(int int)|(int int))) => ♯0
--   | _ => ctor0(int)(0i)
--
--
-- ════ 🎯 test1 : (fn (recTaggedUnion (int)|(self#0 self#0)|(self#0 self#0)) int)
-- ƛ let ♯ := @eval;
-- let ♯ := ((@cata @ Int ⬝ ♯0) ⬝ ♯1);
-- ♯0
--
-- ════ 🎯 test2 : (fn (recTaggedUnion (int)|(self#0 self#0)|(self#0 self#0)) int)
-- ƛ let ♯ := ƛ let ♯ := (@bump ⬝ ♯0);
-- let ♯ := (@eval ⬝ ♯0);
-- ♯0;
-- let ♯ := ((@cata @ Int ⬝ ♯0) ⬝ ♯1);
-- ♯0
--
--
-- ── the same program as Lean source ────────────────────────────────────
-- The trees above are this program printed in the notation of `LakeJs.ExprPretty`;
-- copy one into a `[LEAN|...]` elaboration if you want to read it there.

import LakeJs

open LakeJs LakeJs.Ty LakeJs.Expr LakeJs.Expr.Ops

namespace ProgramSnapshotsPBOPureRecursionSchemes01

/-- `bump`, as a declaration of the module. -/
def d_bump : GlobalDecl := ⟨"bump", (Ty.fn (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]])) (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]])))⟩

/-- The signature `bump` is written against. -/
def sig_bump : Sig := ⟨[], by decide⟩

/-- The body of `bump`. -/
def tm_bump : Term sig_bump [] [] (Ty.fn (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]])) (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]]))) :=
  (Term.lam (Term.caseTag (♯0) (Alts.cons 0 [Ty.int] (by rfl) (Term.letE (Term.natL 1) (Term.letE (natToInt (♯0)) (Term.letE (intAdd (♯2) (♯0)) (Term.letE (Term.ctor (τ := (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]]))) 0 [Ty.int] (by rfl) (.cons (♯0) .nil)) (♯0))))) (Alts.deflt (♯0))) (by rfl)))

/-- The module up to and including `bump`. -/
def prog_bump : Program (d_bump :: sig_bump.decls) :=
  .cons d_bump sig_bump.h_names_unique tm_bump Program.nil

/-- `eval`, as a declaration of the module. -/
def d_eval : GlobalDecl := ⟨"eval", (Ty.fn (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]])) Ty.int)⟩

/-- The signature `eval` is written against. -/
def sig_eval : Sig := ⟨[d_bump], by decide⟩

/-- The body of `eval`. -/
def tm_eval : Term sig_eval [] [] (Ty.fn (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]])) Ty.int) :=
  (Term.lam (Term.caseTag (♯0) (Alts.cons 0 [Ty.int] (by rfl) (♯0) (Alts.cons 1 [Ty.int, Ty.int] (by rfl) (Term.letE (intAdd (♯0) (♯1)) (♯0)) (Alts.cons 2 [Ty.int, Ty.int] (by rfl) (Term.letE (intMul (♯0) (♯1)) (♯0)) Alts.nilFull))) (by rfl)))

/-- The module up to and including `eval`. -/
def prog_eval : Program (d_eval :: sig_eval.decls) :=
  .cons d_eval sig_eval.h_names_unique tm_eval prog_bump

/-- `cata @ Int & cataMap @ Int (clique)`, as a declaration of the module. -/
def d_cata___Int___cataMap___Int__clique_ : GlobalDecl := ⟨"cata @ Int & cataMap @ Int (clique)", (Ty.fn Ty.nat (Ty.fn (Ty.fn (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]])) Ty.int) (Ty.fn (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]])) (Ty.fn (Ty.fn (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]])) Ty.int) (Ty.fn (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]])) (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [(Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]]))] [])))))))⟩

/-- The signature `cata @ Int & cataMap @ Int (clique)` is written against. -/
def sig_cata___Int___cataMap___Int__clique_ : Sig := ⟨[d_eval, d_bump], by decide⟩

/-- The body of the recursion of `cata @ Int & cataMap @ Int (clique)`. -/
def bd_cata___Int___cataMap___Int__clique_ : Term sig_cata___Int___cataMap___Int__clique_ ([Ty.nat, (Ty.fn (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]])) Ty.int), (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]])), (Ty.fn (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]])) Ty.int), (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]]))] ++ []) [⟨[Ty.nat, (Ty.fn (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]])) Ty.int), (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]])), (Ty.fn (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]])) Ty.int), (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]]))], (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [(Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]]))] []))⟩] (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [(Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]]))] [])) :=
  (Term.ite (natEq (♯0) (Term.natL 0)) (Term.ctor (τ := (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [(Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]]))] []))) 0 [Ty.int] (by rfl) (.cons (Term.letE (Term.caseTag (Term.selfCall .head (.cons (Term.natL 1) (.cons (Term.lam (Term.intL (0))) (.cons (Term.ctor (τ := (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]]))) 0 [Ty.int] (by rfl) (.cons (Term.intL (0)) .nil)) (.cons (♯1) (.cons (♯2) .nil)))))) (Alts.cons 1 [(Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]]))] (by rfl) (♯0) (Alts.deflt (Term.ctor (τ := (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]]))) 0 [Ty.int] (by rfl) (.cons (Term.intL (0)) .nil)))) (by rfl)) (Term.letE (Term.ap (♯2) (♯0)) (♯0))) .nil)) (Term.ctor (τ := (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [(Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]]))] []))) 1 [(Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]]))] (by rfl) (.cons (Term.caseTag (♯4) (Alts.cons 0 [Ty.int] (by rfl) (Term.letE (Term.ctor (τ := (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]]))) 0 [Ty.int] (by rfl) (.cons (♯0) .nil)) (♯0)) (Alts.cons 1 [(Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]])), (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]]))] (by rfl) (Term.letE (Term.caseTag (Term.selfCall .head (.cons (Term.natL 0) (.cons (♯5) (.cons (♯0) (.cons (Term.lam (Term.intL (0))) (.cons (Term.ctor (τ := (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]]))) 0 [Ty.int] (by rfl) (.cons (Term.intL (0)) .nil)) .nil)))))) (Alts.cons 0 [Ty.int] (by rfl) (♯0) (Alts.deflt (Term.intL (0)))) (by rfl)) (Term.letE (Term.caseTag (Term.selfCall .head (.cons (Term.natL 0) (.cons (♯6) (.cons (♯2) (.cons (Term.lam (Term.intL (0))) (.cons (Term.ctor (τ := (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]]))) 0 [Ty.int] (by rfl) (.cons (Term.intL (0)) .nil)) .nil)))))) (Alts.cons 0 [Ty.int] (by rfl) (♯0) (Alts.deflt (Term.intL (0)))) (by rfl)) (Term.letE (Term.ctor (τ := (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]]))) 1 [Ty.int, Ty.int] (by rfl) (.cons (♯1) (.cons (♯0) .nil))) (♯0)))) (Alts.cons 2 [(Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]])), (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]]))] (by rfl) (Term.letE (Term.caseTag (Term.selfCall .head (.cons (Term.natL 0) (.cons (♯5) (.cons (♯0) (.cons (Term.lam (Term.intL (0))) (.cons (Term.ctor (τ := (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]]))) 0 [Ty.int] (by rfl) (.cons (Term.intL (0)) .nil)) .nil)))))) (Alts.cons 0 [Ty.int] (by rfl) (♯0) (Alts.deflt (Term.intL (0)))) (by rfl)) (Term.letE (Term.caseTag (Term.selfCall .head (.cons (Term.natL 0) (.cons (♯6) (.cons (♯2) (.cons (Term.lam (Term.intL (0))) (.cons (Term.ctor (τ := (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]]))) 0 [Ty.int] (by rfl) (.cons (Term.intL (0)) .nil)) .nil)))))) (Alts.cons 0 [Ty.int] (by rfl) (♯0) (Alts.deflt (Term.intL (0)))) (by rfl)) (Term.letE (Term.ctor (τ := (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]]))) 2 [Ty.int, Ty.int] (by rfl) (.cons (♯1) (.cons (♯0) .nil))) (♯0)))) Alts.nilFull))) (by rfl)) .nil)))

/-- The body of `cata @ Int & cataMap @ Int (clique)`. -/
def tm_cata___Int___cataMap___Int__clique_ : Term sig_cata___Int___cataMap___Int__clique_ [] [] (Ty.fn Ty.nat (Ty.fn (Ty.fn (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]])) Ty.int) (Ty.fn (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]])) (Ty.fn (Ty.fn (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]])) Ty.int) (Ty.fn (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]])) (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [(Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]]))] []))))))) :=
  Term.fix [Ty.nat, (Ty.fn (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]])) Ty.int), (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]])), (Ty.fn (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]])) Ty.int), (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]]))] 2 (.cons (Term.ite (natEq (♯0) (Term.natL 0)) (Term.structSize (♯2)) (Term.structSize (♯4))) (.cons (natSub (Term.natL 1) (♯0)) .nil)) bd_cata___Int___cataMap___Int__clique_ (Term.ctor (τ := (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [(Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]]))] []))) 0 [Ty.int] (by rfl) (.cons (Term.intL (0)) .nil))

/-- The module up to and including `cata @ Int & cataMap @ Int (clique)`. -/
def prog_cata___Int___cataMap___Int__clique_ : Program (d_cata___Int___cataMap___Int__clique_ :: sig_cata___Int___cataMap___Int__clique_.decls) :=
  .cons d_cata___Int___cataMap___Int__clique_ sig_cata___Int___cataMap___Int__clique_.h_names_unique tm_cata___Int___cataMap___Int__clique_ prog_eval

/-- `cata @ Int`, as a declaration of the module. -/
def d_cata___Int : GlobalDecl := ⟨"cata @ Int", (Ty.fn (Ty.fn (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]])) Ty.int) (Ty.fn (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]])) Ty.int))⟩

/-- The signature `cata @ Int` is written against. -/
def sig_cata___Int : Sig := ⟨[d_cata___Int___cataMap___Int__clique_, d_eval, d_bump], by decide⟩

/-- The body of `cata @ Int`. -/
def tm_cata___Int : Term sig_cata___Int [] [] (Ty.fn (Ty.fn (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]])) Ty.int) (Ty.fn (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]])) Ty.int)) :=
  (Term.lam (Term.lam (Term.caseTag (Term.ap (Term.ap (Term.ap (Term.ap (Term.ap (Term.global .here) (Term.natL 0)) (♯1)) (♯0)) (Term.lam (Term.intL (0)))) (Term.ctor (τ := (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]]))) 0 [Ty.int] (by rfl) (.cons (Term.intL (0)) .nil))) (Alts.cons 0 [Ty.int] (by rfl) (♯0) (Alts.deflt (Term.intL (0)))) (by rfl))))

/-- The module up to and including `cata @ Int`. -/
def prog_cata___Int : Program (d_cata___Int :: sig_cata___Int.decls) :=
  .cons d_cata___Int sig_cata___Int.h_names_unique tm_cata___Int prog_cata___Int___cataMap___Int__clique_

/-- `cataMap @ Int`, as a declaration of the module. -/
def d_cataMap___Int : GlobalDecl := ⟨"cataMap @ Int", (Ty.fn (Ty.fn (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]])) Ty.int) (Ty.fn (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]])) (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]]))))⟩

/-- The signature `cataMap @ Int` is written against. -/
def sig_cataMap___Int : Sig := ⟨[d_cata___Int, d_cata___Int___cataMap___Int__clique_, d_eval, d_bump], by decide⟩

/-- The body of `cataMap @ Int`. -/
def tm_cataMap___Int : Term sig_cataMap___Int [] [] (Ty.fn (Ty.fn (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]])) Ty.int) (Ty.fn (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]])) (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]])))) :=
  (Term.lam (Term.lam (Term.caseTag (Term.ap (Term.ap (Term.ap (Term.ap (Term.ap (Term.global (.there .here)) (Term.natL 1)) (Term.lam (Term.intL (0)))) (Term.ctor (τ := (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]]))) 0 [Ty.int] (by rfl) (.cons (Term.intL (0)) .nil))) (♯1)) (♯0)) (Alts.cons 1 [(Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]]))] (by rfl) (♯0) (Alts.deflt (Term.ctor (τ := (Ty.taggedUnion (.payloadFirst ⟨Ty.int, []⟩ [Ty.int, Ty.int] [[Ty.int, Ty.int]]))) 0 [Ty.int] (by rfl) (.cons (Term.intL (0)) .nil)))) (by rfl))))

/-- The module up to and including `cataMap @ Int`. -/
def prog_cataMap___Int : Program (d_cataMap___Int :: sig_cataMap___Int.decls) :=
  .cons d_cataMap___Int sig_cataMap___Int.h_names_unique tm_cataMap___Int prog_cata___Int

/-- `test1`, as a declaration of the module. -/
def d_test1 : GlobalDecl := ⟨"test1", (Ty.fn (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]])) Ty.int)⟩

/-- The signature `test1` is written against. -/
def sig_test1 : Sig := ⟨[d_cataMap___Int, d_cata___Int, d_cata___Int___cataMap___Int__clique_, d_eval, d_bump], by decide⟩

/-- The body of `test1`. -/
def tm_test1 : Term sig_test1 [] [] (Ty.fn (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]])) Ty.int) :=
  (Term.lam (Term.letE (Term.global (.there (.there (.there .here)))) (Term.letE (Term.ap (Term.ap (Term.global (.there .here)) (♯0)) (♯1)) (♯0))))

/-- The module up to and including `test1`. -/
def prog_test1 : Program (d_test1 :: sig_test1.decls) :=
  .cons d_test1 sig_test1.h_names_unique tm_test1 prog_cataMap___Int

/-- `test2`, as a declaration of the module. -/
def d_test2 : GlobalDecl := ⟨"test2", (Ty.fn (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]])) Ty.int)⟩

/-- The signature `test2` is written against. -/
def sig_test2 : Sig := ⟨[d_test1, d_cataMap___Int, d_cata___Int, d_cata___Int___cataMap___Int__clique_, d_eval, d_bump], by decide⟩

/-- The body of `test2`. -/
def tm_test2 : Term sig_test2 [] [] (Ty.fn (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.prim .int), []⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0), (RTy.self 0)]])) Ty.int) :=
  (Term.lam (Term.letE (Term.lam (Term.letE (Term.ap (Term.global (.there (.there (.there (.there (.there .here)))))) (♯0)) (Term.letE (Term.ap (Term.global (.there (.there (.there (.there .here))))) (♯0)) (♯0)))) (Term.letE (Term.ap (Term.ap (Term.global (.there (.there .here))) (♯0)) (♯1)) (♯0))))

/-- The module up to and including `test2`. -/
def prog_test2 : Program (d_test2 :: sig_test2.decls) :=
  .cons d_test2 sig_test2.h_names_unique tm_test2 prog_test1

/-- The signature of the whole module. -/
def moduleSig : Sig := ⟨[d_test2, d_test1, d_cataMap___Int, d_cata___Int, d_cata___Int___cataMap___Int__clique_, d_eval, d_bump], by decide⟩

/-- The module as a telescope: every body is written against the declarations before it, so the call graph is acyclic by construction.  It is built one declaration at a time, above, so that no single elaboration sees the whole telescope at once. -/
def program : Program moduleSig.decls :=
  prog_test2

end ProgramSnapshotsPBOPureRecursionSchemes01
