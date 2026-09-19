-- SnapshotsMy.LoopEntry: the module as a Program of the one grammar of `LakeJs.Expr`.
-- 🎯 a public entry point of the module; 📦 a declaration the translation pulled in.
-- Every term below is a `Term`, so it is terminating by construction: the one way it
-- repeats work is `Term.fix`, whose measure it descends on at every self call.
-- refused by the totality gate: `main`: its type is an IO type; the backend compiles pure functions only
-- refused by the totality gate: `printAll`: its type is an IO type; the backend compiles pure functions only
--
-- ════ 🎯 countUp : (fn string (fn nat (fn nat (fn nat nat))))
--      measure: structural recursion, on the argument Lean recorded (position 2); 1 component: [ ♯2 ]
-- fix (string nat nat nat) measure [ ♯2 ] body {
--   if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯2) ⬝ 0#) then ♯3 else let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯3) ⬝ ♯1);
--   let ♯ := self0⟨↓⟩(♯1, ♯2, ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯3) ⬝ 1#), ♯0);
--   ♯0
-- } stuck { 0# }
--
-- ════ 🎯 messages : (recTaggedUnion ()|(string self#0))
-- let ♯ := "one";
-- let ♯ := "two";
-- let ♯ := "three";
-- let ♯ := ctor0()();
-- let ♯ := ctor1(string (recTaggedUnion ()|(string self#0)))(♯1, ♯0);
-- let ♯ := ctor1(string (recTaggedUnion ()|(string self#0)))(♯3, ♯0);
-- let ♯ := ctor1(string (recTaggedUnion ()|(string self#0)))(♯5, ♯0);
-- ♯0
--
--
-- ── the same program as Lean source ────────────────────────────────────
-- The trees above are this program printed in the notation of `LakeJs.ExprPretty`;
-- copy one into a `[LEAN|...]` elaboration if you want to read it there.

import LakeJs

open LakeJs LakeJs.Ty LakeJs.Expr LakeJs.Expr.Ops

namespace ProgramSnapshotsMyLoopEntry

/-- `countUp`, as a declaration of the module. -/
def d_countUp : GlobalDecl := ⟨"countUp", (Ty.fn Ty.string (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat))))⟩

/-- The signature `countUp` is written against. -/
def sig_countUp : Sig := ⟨[], by decide⟩

/-- The body of the recursion of `countUp`. -/
def bd_countUp : Term sig_countUp ([Ty.string, Ty.nat, Ty.nat, Ty.nat] ++ []) [⟨[Ty.string, Ty.nat, Ty.nat, Ty.nat], Ty.nat⟩] Ty.nat :=
  (Term.ite (natEq (♯2) (Term.natL 0)) (♯3) (Term.letE (natAdd (♯3) (♯1)) (Term.letE (Term.selfCall .head (.cons (♯1) (.cons (♯2) (.cons (natSub (♯3) (Term.natL 1)) (.cons (♯0) .nil))))) (♯0))))

/-- The body of `countUp`. -/
def tm_countUp : Term sig_countUp [] [] (Ty.fn Ty.string (Ty.fn Ty.nat (Ty.fn Ty.nat (Ty.fn Ty.nat Ty.nat)))) :=
  Term.fix [Ty.string, Ty.nat, Ty.nat, Ty.nat] 1 (.cons (♯2) .nil) bd_countUp (Term.natL 0)

/-- The module up to and including `countUp`. -/
def prog_countUp : Program (d_countUp :: sig_countUp.decls) :=
  .cons d_countUp sig_countUp.h_names_unique tm_countUp Program.nil

/-- `messages`, as a declaration of the module. -/
def d_messages : GlobalDecl := ⟨"messages", (Ty.recTaggedUnion (.skip (.here ⟨(RTy.prim .string), [(RTy.self 0)]⟩ [])))⟩

/-- The signature `messages` is written against. -/
def sig_messages : Sig := ⟨[d_countUp], by decide⟩

/-- The body of `messages`. -/
def tm_messages : Term sig_messages [] [] (Ty.recTaggedUnion (.skip (.here ⟨(RTy.prim .string), [(RTy.self 0)]⟩ []))) :=
  (Term.letE (Term.strL "one") (Term.letE (Term.strL "two") (Term.letE (Term.strL "three") (Term.letE (Term.ctor (τ := (Ty.recTaggedUnion (.skip (.here ⟨(RTy.prim .string), [(RTy.self 0)]⟩ [])))) 0 [] (by rfl) .nil) (Term.letE (Term.ctor (τ := (Ty.recTaggedUnion (.skip (.here ⟨(RTy.prim .string), [(RTy.self 0)]⟩ [])))) 1 [Ty.string, (Ty.recTaggedUnion (.skip (.here ⟨(RTy.prim .string), [(RTy.self 0)]⟩ [])))] (by rfl) (.cons (♯1) (.cons (♯0) .nil))) (Term.letE (Term.ctor (τ := (Ty.recTaggedUnion (.skip (.here ⟨(RTy.prim .string), [(RTy.self 0)]⟩ [])))) 1 [Ty.string, (Ty.recTaggedUnion (.skip (.here ⟨(RTy.prim .string), [(RTy.self 0)]⟩ [])))] (by rfl) (.cons (♯3) (.cons (♯0) .nil))) (Term.letE (Term.ctor (τ := (Ty.recTaggedUnion (.skip (.here ⟨(RTy.prim .string), [(RTy.self 0)]⟩ [])))) 1 [Ty.string, (Ty.recTaggedUnion (.skip (.here ⟨(RTy.prim .string), [(RTy.self 0)]⟩ [])))] (by rfl) (.cons (♯5) (.cons (♯0) .nil))) (♯0))))))))

/-- The module up to and including `messages`. -/
def prog_messages : Program (d_messages :: sig_messages.decls) :=
  .cons d_messages sig_messages.h_names_unique tm_messages prog_countUp

/-- The signature of the whole module. -/
def moduleSig : Sig := ⟨[d_messages, d_countUp], by decide⟩

/-- The module as a telescope: every body is written against the declarations before it, so the call graph is acyclic by construction.  It is built one declaration at a time, above, so that no single elaboration sees the whole telescope at once. -/
def program : Program moduleSig.decls :=
  prog_messages

end ProgramSnapshotsMyLoopEntry
