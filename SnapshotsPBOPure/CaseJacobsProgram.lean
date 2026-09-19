-- SnapshotsPBOPure.CaseJacobs: the module as a Program of the one grammar of `LakeJs.Expr`.
-- 🎯 a public entry point of the module; 📦 a declaration the translation pulled in.
-- Every term below is a `Term`, so it is terminating by construction: the one way it
-- repeats work is `Term.fix`, whose measure it descends on at every self call.
-- outside the language: `Expr.ctorElim`: the parameter `motive` of `Expr.ctorElim` has type `Expr →
--   Sort u`, which the front end does not translate
-- outside the language: `Expr.add.elim`: the parameter `motive` of `Expr.add.elim` has type `Expr →
--   Sort u`, which the front end does not translate
-- outside the language: `Expr.mul.elim`: the parameter `motive` of `Expr.mul.elim` has type `Expr →
--   Sort u`, which the front end does not translate
-- outside the language: `Expr.succ.elim`: the parameter `motive` of `Expr.succ.elim` has type `Expr →
--   Sort u`, which the front end does not translate
-- outside the language: `Expr.zero.elim`: the parameter `motive` of `Expr.zero.elim` has type `Expr →
--   Sort u`, which the front end does not translate
--
-- ════ 🎯 renderExpr : (fn (recTaggedUnion (self#0 self#0)|(self#0 self#0)|(self#0)|()) string)
--      measure: structural recursion, on the argument Lean recorded (position 0); 1 component: [ size(♯0) ]
-- fix ((recTaggedUnion (self#0 self#0)|(self#0 self#0)|(self#0)|())) measure [ size(♯0) ] body {
--   case ♯0 of
--     | 0((recTaggedUnion (self#0 self#0)|(self#0 self#0)|(self#0)|()) (recTaggedUnion (self#0 self#0)|(self#0 self#0)|(self#0)|())) => let ♯ := "Add(";
--       let ♯ := self0⟨↓⟩(♯1);
--       let ♯ := ((extern⟨string string ⇒ string⟩ ⬝ ♯1) ⬝ ♯0);
--       let ♯ := " ";
--       let ♯ := ((extern⟨string string ⇒ string⟩ ⬝ ♯1) ⬝ ♯0);
--       let ♯ := self0⟨↓⟩(♯6);
--       let ♯ := ((extern⟨string string ⇒ string⟩ ⬝ ♯1) ⬝ ♯0);
--       let ♯ := ")";
--       let ♯ := ((extern⟨string string ⇒ string⟩ ⬝ ♯1) ⬝ ♯0);
--       ♯0
--     | 1((recTaggedUnion (self#0 self#0)|(self#0 self#0)|(self#0)|()) (recTaggedUnion (self#0 self#0)|(self#0 self#0)|(self#0)|())) => let ♯ := "Mul(";
--       let ♯ := self0⟨↓⟩(♯1);
--       let ♯ := ((extern⟨string string ⇒ string⟩ ⬝ ♯1) ⬝ ♯0);
--       let ♯ := " ";
--       let ♯ := ((extern⟨string string ⇒ string⟩ ⬝ ♯1) ⬝ ♯0);
--       let ♯ := self0⟨↓⟩(♯6);
--       let ♯ := ((extern⟨string string ⇒ string⟩ ⬝ ♯1) ⬝ ♯0);
--       let ♯ := ")";
--       let ♯ := ((extern⟨string string ⇒ string⟩ ⬝ ♯1) ⬝ ♯0);
--       ♯0
--     | 2((recTaggedUnion (self#0 self#0)|(self#0 self#0)|(self#0)|())) => let ♯ := "Succ(";
--       let ♯ := self0⟨↓⟩(♯1);
--       let ♯ := ((extern⟨string string ⇒ string⟩ ⬝ ♯1) ⬝ ♯0);
--       let ♯ := ")";
--       let ♯ := ((extern⟨string string ⇒ string⟩ ⬝ ♯1) ⬝ ♯0);
--       ♯0
--     | 3() => let ♯ := "Zero";
--       ♯0
--
-- } stuck { "" }
--
-- ════ 🎯 Expr.ctorIdx : (fn (recTaggedUnion (self#0 self#0)|(self#0 self#0)|(self#0)|()) nat)
-- ƛ case ♯0 of
--   | 0((recTaggedUnion (self#0 self#0)|(self#0 self#0)|(self#0)|()) (recTaggedUnion (self#0 self#0)|(self#0 self#0)|(self#0)|())) => let ♯ := 0#;
--     ♯0
--   | 1((recTaggedUnion (self#0 self#0)|(self#0 self#0)|(self#0)|()) (recTaggedUnion (self#0 self#0)|(self#0 self#0)|(self#0)|())) => let ♯ := 1#;
--     ♯0
--   | 2((recTaggedUnion (self#0 self#0)|(self#0 self#0)|(self#0)|())) => let ♯ := 2#;
--     ♯0
--   | 3() => let ♯ := 3#;
--     ♯0
--
--
-- ════ 🎯 instToStringExpr : (fn (recTaggedUnion (self#0 self#0)|(self#0 self#0)|(self#0)|()) string)
-- let ♯ := ƛ let ♯ := (@renderExpr ⬝ ♯0);
-- ♯0;
-- let ♯ := ♯0;
-- ♯0
--
-- ════ 🎯 test1 : (fn (recTaggedUnion (self#0 self#0)|(self#0 self#0)|(self#0)|()) string)
-- ƛ case ♯0 of
--   | 0((recTaggedUnion (self#0 self#0)|(self#0 self#0)|(self#0)|()) (recTaggedUnion (self#0 self#0)|(self#0 self#0)|(self#0)|())) => case ♯0 of
--       | 3() => case ♯1 of
--           | 3() => let ♯ := "e1";
--             ♯0
--           | _ => let ♯ := "e7: ";
--             let ♯ := (@renderExpr ⬝ ♯3);
--             let ♯ := ((extern⟨string string ⇒ string⟩ ⬝ ♯1) ⬝ ♯0);
--             ♯0
--
--       | 2((recTaggedUnion (self#0 self#0)|(self#0 self#0)|(self#0)|())) => let ♯ := "e3: ";
--         let ♯ := (@renderExpr ⬝ ♯1);
--         let ♯ := ((extern⟨string string ⇒ string⟩ ⬝ ♯1) ⬝ ♯0);
--         let ♯ := " ";
--         let ♯ := ((extern⟨string string ⇒ string⟩ ⬝ ♯1) ⬝ ♯0);
--         let ♯ := (@renderExpr ⬝ ♯7);
--         let ♯ := ((extern⟨string string ⇒ string⟩ ⬝ ♯1) ⬝ ♯0);
--         ♯0
--       | _ => case ♯1 of
--           | 3() => let ♯ := "e6: ";
--             let ♯ := (@renderExpr ⬝ ♯1);
--             let ♯ := ((extern⟨string string ⇒ string⟩ ⬝ ♯1) ⬝ ♯0);
--             ♯0
--           | _ => let ♯ := "e7: ";
--             let ♯ := (@renderExpr ⬝ ♯3);
--             let ♯ := ((extern⟨string string ⇒ string⟩ ⬝ ♯1) ⬝ ♯0);
--             ♯0
--
--
--   | 1((recTaggedUnion (self#0 self#0)|(self#0 self#0)|(self#0)|()) (recTaggedUnion (self#0 self#0)|(self#0 self#0)|(self#0)|())) => case ♯0 of
--       | 3() => let ♯ := "e2: ";
--         let ♯ := (@renderExpr ⬝ ♯2);
--         let ♯ := ((extern⟨string string ⇒ string⟩ ⬝ ♯1) ⬝ ♯0);
--         ♯0
--       | 0((recTaggedUnion (self#0 self#0)|(self#0 self#0)|(self#0)|()) (recTaggedUnion (self#0 self#0)|(self#0 self#0)|(self#0)|())) => case ♯3 of
--           | 3() => let ♯ := "e4: ";
--             let ♯ := (@renderExpr ⬝ ♯3);
--             let ♯ := ((extern⟨string string ⇒ string⟩ ⬝ ♯1) ⬝ ♯0);
--             ♯0
--           | _ => let ♯ := "e5: ";
--             let ♯ := (@renderExpr ⬝ ♯1);
--             let ♯ := ((extern⟨string string ⇒ string⟩ ⬝ ♯1) ⬝ ♯0);
--             let ♯ := " ";
--             let ♯ := ((extern⟨string string ⇒ string⟩ ⬝ ♯1) ⬝ ♯0);
--             let ♯ := (@renderExpr ⬝ ♯6);
--             let ♯ := ((extern⟨string string ⇒ string⟩ ⬝ ♯1) ⬝ ♯0);
--             let ♯ := ((extern⟨string string ⇒ string⟩ ⬝ ♯0) ⬝ ♯3);
--             let ♯ := (@renderExpr ⬝ ♯11);
--             let ♯ := ((extern⟨string string ⇒ string⟩ ⬝ ♯1) ⬝ ♯0);
--             ♯0
--
--       | _ => case ♯1 of
--           | 3() => let ♯ := "e4: ";
--             let ♯ := (@renderExpr ⬝ ♯1);
--             let ♯ := ((extern⟨string string ⇒ string⟩ ⬝ ♯1) ⬝ ♯0);
--             ♯0
--           | _ => let ♯ := "e7: ";
--             let ♯ := (@renderExpr ⬝ ♯3);
--             let ♯ := ((extern⟨string string ⇒ string⟩ ⬝ ♯1) ⬝ ♯0);
--             ♯0
--
--
--   | _ => let ♯ := "e7: ";
--     let ♯ := (@renderExpr ⬝ ♯1);
--     let ♯ := ((extern⟨string string ⇒ string⟩ ⬝ ♯1) ⬝ ♯0);
--     ♯0
--
--
--
-- ── the same program as Lean source ────────────────────────────────────
-- The trees above are this program printed in the notation of `LakeJs.ExprPretty`;
-- copy one into a `[LEAN|...]` elaboration if you want to read it there.

import LakeJs

open LakeJs LakeJs.Ty LakeJs.Expr LakeJs.Expr.Ops

namespace ProgramSnapshotsPBOPureCaseJacobs

/-- `renderExpr`, as a declaration of the module. -/
def d_renderExpr : GlobalDecl := ⟨"renderExpr", (Ty.fn (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []])) Ty.string)⟩

/-- The signature `renderExpr` is written against. -/
def sig_renderExpr : Sig := ⟨[], by decide⟩

/-- The body of the recursion of `renderExpr`. -/
def bd_renderExpr : Term sig_renderExpr ([(Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []]))] ++ []) [⟨[(Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []]))], Ty.string⟩] Ty.string :=
  (Term.caseTag (♯0) (Alts.cons 0 [(Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []])), (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []]))] (by rfl) (Term.letE (Term.strL "Add(") (Term.letE (Term.selfCall .head (.cons (♯1) .nil)) (Term.letE (strAppend (♯1) (♯0)) (Term.letE (Term.strL " ") (Term.letE (strAppend (♯1) (♯0)) (Term.letE (Term.selfCall .head (.cons (♯6) .nil)) (Term.letE (strAppend (♯1) (♯0)) (Term.letE (Term.strL ")") (Term.letE (strAppend (♯1) (♯0)) (♯0)))))))))) (Alts.cons 1 [(Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []])), (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []]))] (by rfl) (Term.letE (Term.strL "Mul(") (Term.letE (Term.selfCall .head (.cons (♯1) .nil)) (Term.letE (strAppend (♯1) (♯0)) (Term.letE (Term.strL " ") (Term.letE (strAppend (♯1) (♯0)) (Term.letE (Term.selfCall .head (.cons (♯6) .nil)) (Term.letE (strAppend (♯1) (♯0)) (Term.letE (Term.strL ")") (Term.letE (strAppend (♯1) (♯0)) (♯0)))))))))) (Alts.cons 2 [(Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []]))] (by rfl) (Term.letE (Term.strL "Succ(") (Term.letE (Term.selfCall .head (.cons (♯1) .nil)) (Term.letE (strAppend (♯1) (♯0)) (Term.letE (Term.strL ")") (Term.letE (strAppend (♯1) (♯0)) (♯0)))))) (Alts.cons 3 [] (by rfl) (Term.letE (Term.strL "Zero") (♯0)) Alts.nilFull)))) (by rfl))

/-- The body of `renderExpr`. -/
def tm_renderExpr : Term sig_renderExpr [] [] (Ty.fn (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []])) Ty.string) :=
  Term.fix [(Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []]))] 1 (.cons (Term.structSize (♯0)) .nil) bd_renderExpr (Term.strL "")

/-- The module up to and including `renderExpr`. -/
def prog_renderExpr : Program (d_renderExpr :: sig_renderExpr.decls) :=
  .cons d_renderExpr sig_renderExpr.h_names_unique tm_renderExpr Program.nil

/-- `Expr.ctorIdx`, as a declaration of the module. -/
def d_Expr_ctorIdx : GlobalDecl := ⟨"Expr.ctorIdx", (Ty.fn (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []])) Ty.nat)⟩

/-- The signature `Expr.ctorIdx` is written against. -/
def sig_Expr_ctorIdx : Sig := ⟨[d_renderExpr], by decide⟩

/-- The body of `Expr.ctorIdx`. -/
def tm_Expr_ctorIdx : Term sig_Expr_ctorIdx [] [] (Ty.fn (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []])) Ty.nat) :=
  (Term.lam (Term.caseTag (♯0) (Alts.cons 0 [(Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []])), (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []]))] (by rfl) (Term.letE (Term.natL 0) (♯0)) (Alts.cons 1 [(Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []])), (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []]))] (by rfl) (Term.letE (Term.natL 1) (♯0)) (Alts.cons 2 [(Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []]))] (by rfl) (Term.letE (Term.natL 2) (♯0)) (Alts.cons 3 [] (by rfl) (Term.letE (Term.natL 3) (♯0)) Alts.nilFull)))) (by rfl)))

/-- The module up to and including `Expr.ctorIdx`. -/
def prog_Expr_ctorIdx : Program (d_Expr_ctorIdx :: sig_Expr_ctorIdx.decls) :=
  .cons d_Expr_ctorIdx sig_Expr_ctorIdx.h_names_unique tm_Expr_ctorIdx prog_renderExpr

/-- `instToStringExpr`, as a declaration of the module. -/
def d_instToStringExpr : GlobalDecl := ⟨"instToStringExpr", (Ty.fn (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []])) Ty.string)⟩

/-- The signature `instToStringExpr` is written against. -/
def sig_instToStringExpr : Sig := ⟨[d_Expr_ctorIdx, d_renderExpr], by decide⟩

/-- The body of `instToStringExpr`. -/
def tm_instToStringExpr : Term sig_instToStringExpr [] [] (Ty.fn (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []])) Ty.string) :=
  (Term.letE (Term.lam (Term.letE (Term.ap (Term.global (.there .here)) (♯0)) (♯0))) (Term.letE (♯0) (♯0)))

/-- The module up to and including `instToStringExpr`. -/
def prog_instToStringExpr : Program (d_instToStringExpr :: sig_instToStringExpr.decls) :=
  .cons d_instToStringExpr sig_instToStringExpr.h_names_unique tm_instToStringExpr prog_Expr_ctorIdx

/-- `test1`, as a declaration of the module. -/
def d_test1 : GlobalDecl := ⟨"test1", (Ty.fn (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []])) Ty.string)⟩

/-- The signature `test1` is written against. -/
def sig_test1 : Sig := ⟨[d_instToStringExpr, d_Expr_ctorIdx, d_renderExpr], by decide⟩

/-- The body of `test1`. -/
def tm_test1 : Term sig_test1 [] [] (Ty.fn (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []])) Ty.string) :=
  (Term.lam (Term.caseTag (♯0) (Alts.cons 0 [(Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []])), (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []]))] (by rfl) (Term.caseTag (♯0) (Alts.cons 3 [] (by rfl) (Term.caseTag (♯1) (Alts.cons 3 [] (by rfl) (Term.letE (Term.strL "e1") (♯0)) (Alts.deflt (Term.letE (Term.strL "e7: ") (Term.letE (Term.ap (Term.global (.there (.there .here))) (♯3)) (Term.letE (strAppend (♯1) (♯0)) (♯0)))))) (by rfl)) (Alts.cons 2 [(Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []]))] (by rfl) (Term.letE (Term.strL "e3: ") (Term.letE (Term.ap (Term.global (.there (.there .here))) (♯1)) (Term.letE (strAppend (♯1) (♯0)) (Term.letE (Term.strL " ") (Term.letE (strAppend (♯1) (♯0)) (Term.letE (Term.ap (Term.global (.there (.there .here))) (♯7)) (Term.letE (strAppend (♯1) (♯0)) (♯0)))))))) (Alts.deflt (Term.caseTag (♯1) (Alts.cons 3 [] (by rfl) (Term.letE (Term.strL "e6: ") (Term.letE (Term.ap (Term.global (.there (.there .here))) (♯1)) (Term.letE (strAppend (♯1) (♯0)) (♯0)))) (Alts.deflt (Term.letE (Term.strL "e7: ") (Term.letE (Term.ap (Term.global (.there (.there .here))) (♯3)) (Term.letE (strAppend (♯1) (♯0)) (♯0)))))) (by rfl))))) (by rfl)) (Alts.cons 1 [(Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []])), (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []]))] (by rfl) (Term.caseTag (♯0) (Alts.cons 3 [] (by rfl) (Term.letE (Term.strL "e2: ") (Term.letE (Term.ap (Term.global (.there (.there .here))) (♯2)) (Term.letE (strAppend (♯1) (♯0)) (♯0)))) (Alts.cons 0 [(Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []])), (Ty.recTaggedUnion (.payloadFirst ⟨(RTy.self 0), [(RTy.self 0)]⟩ [(RTy.self 0), (RTy.self 0)] [[(RTy.self 0)], []]))] (by rfl) (Term.caseTag (♯3) (Alts.cons 3 [] (by rfl) (Term.letE (Term.strL "e4: ") (Term.letE (Term.ap (Term.global (.there (.there .here))) (♯3)) (Term.letE (strAppend (♯1) (♯0)) (♯0)))) (Alts.deflt (Term.letE (Term.strL "e5: ") (Term.letE (Term.ap (Term.global (.there (.there .here))) (♯1)) (Term.letE (strAppend (♯1) (♯0)) (Term.letE (Term.strL " ") (Term.letE (strAppend (♯1) (♯0)) (Term.letE (Term.ap (Term.global (.there (.there .here))) (♯6)) (Term.letE (strAppend (♯1) (♯0)) (Term.letE (strAppend (♯0) (♯3)) (Term.letE (Term.ap (Term.global (.there (.there .here))) (♯11)) (Term.letE (strAppend (♯1) (♯0)) (♯0))))))))))))) (by rfl)) (Alts.deflt (Term.caseTag (♯1) (Alts.cons 3 [] (by rfl) (Term.letE (Term.strL "e4: ") (Term.letE (Term.ap (Term.global (.there (.there .here))) (♯1)) (Term.letE (strAppend (♯1) (♯0)) (♯0)))) (Alts.deflt (Term.letE (Term.strL "e7: ") (Term.letE (Term.ap (Term.global (.there (.there .here))) (♯3)) (Term.letE (strAppend (♯1) (♯0)) (♯0)))))) (by rfl))))) (by rfl)) (Alts.deflt (Term.letE (Term.strL "e7: ") (Term.letE (Term.ap (Term.global (.there (.there .here))) (♯1)) (Term.letE (strAppend (♯1) (♯0)) (♯0))))))) (by rfl)))

/-- The module up to and including `test1`. -/
def prog_test1 : Program (d_test1 :: sig_test1.decls) :=
  .cons d_test1 sig_test1.h_names_unique tm_test1 prog_instToStringExpr

/-- The signature of the whole module. -/
def moduleSig : Sig := ⟨[d_test1, d_instToStringExpr, d_Expr_ctorIdx, d_renderExpr], by decide⟩

/-- The module as a telescope: every body is written against the declarations before it, so the call graph is acyclic by construction.  It is built one declaration at a time, above, so that no single elaboration sees the whole telescope at once. -/
def program : Program moduleSig.decls :=
  prog_test1

end ProgramSnapshotsPBOPureCaseJacobs
