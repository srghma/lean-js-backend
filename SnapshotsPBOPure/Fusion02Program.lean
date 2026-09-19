-- SnapshotsPBOPure.Fusion02: the module as a Program of the one grammar of `LakeJs.Expr`.
-- 🎯 a public entry point of the module; 📦 a declaration the translation pulled in.
-- Every term below is a `Term`, so it is terminating by construction: the one way it
-- repeats work is `Term.fix`, whose measure it descends on at every self call.
-- outside the language: `filterMapStep`: `filterMapStep` is polymorphic, and the type language is monomorphic: it is compiled once per instantiation a caller uses, and this module has no call of it the front end could read one off
-- outside the language: `filterMapU`: `filterMapU` is polymorphic, and the type language is monomorphic: it is compiled once per instantiation a caller uses, and this module has no call of it the front end could read one off
-- outside the language: `filterU`: `filterU` is polymorphic, and the type language is monomorphic: it is compiled once per instantiation a caller uses, and this module has no call of it the front end could read one off
-- outside the language: `fromArray`: `fromArray` is polymorphic, and the type language is monomorphic: it is compiled once per instantiation a caller uses, and this module has no call of it the front end could read one off
-- outside the language: `mapU`: `mapU` is polymorphic, and the type language is monomorphic: it is compiled once per instantiation a caller uses, and this module has no call of it the front end could read one off
-- outside the language: `overArray`: `overArray` is polymorphic, and the type language is monomorphic: it is compiled once per instantiation a caller uses, and this module has no call of it the front end could read one off
-- outside the language: `test`: the local function `_f.4` answers with `Option
--   (lcAny × String)`, which the front end does not translate
-- outside the language: `toArray`: `toArray` is polymorphic, and the type language is monomorphic: it is compiled once per instantiation a caller uses, and this module has no call of it the front end could read one off
-- outside the language: `toArrayLoop`: `toArrayLoop` is polymorphic, and the type language is monomorphic: it is compiled once per instantiation a caller uses, and this module has no call of it the front end could read one off
-- outside the language: `String.Slice.Pos.nextn`: the parameter `p` of `String.Slice.Pos.nextn` has type `String.Slice.Pos
--   lcAny`, which the front end does not translate
-- outside the language: `dropPrefix1`: it calls `String.Slice.Pos.nextn`, which is outside the language
--
-- ════ 📦 String.Slice.toString : (fn (record string nat nat) string)
-- ƛ let ♯ := proj0.0(♯0);
-- let ♯ := proj0.1(♯1);
-- let ♯ := proj0.2(♯2);
-- let ♯ := (((extern⟨string nat nat ⇒ string⟩ ⬝ ♯2) ⬝ ♯1) ⬝ ♯0);
-- ♯0
--
--
-- ── the same program as Lean source ────────────────────────────────────
-- The trees above are this program printed in the notation of `LakeJs.ExprPretty`;
-- copy one into a `[LEAN|...]` elaboration if you want to read it there.

import LakeJs

open LakeJs LakeJs.Ty LakeJs.Expr LakeJs.Expr.Ops

namespace ProgramSnapshotsPBOPureFusion02

/-- `String.Slice.toString`, as a declaration of the module. -/
def d_String_Slice_toString : GlobalDecl := ⟨"String.Slice.toString", (Ty.fn (Ty.record ⟨Ty.string, Ty.nat, [Ty.nat]⟩) Ty.string)⟩

/-- The signature `String.Slice.toString` is written against. -/
def sig_String_Slice_toString : Sig := ⟨[], by decide⟩

/-- The body of `String.Slice.toString`. -/
def tm_String_Slice_toString : Term sig_String_Slice_toString [] [] (Ty.fn (Ty.record ⟨Ty.string, Ty.nat, [Ty.nat]⟩) Ty.string) :=
  (Term.lam (Term.letE (Term.proj (♯0) 0 0 (by rfl) (by rfl)) (Term.letE (Term.proj (♯1) 0 1 (by rfl) (by rfl)) (Term.letE (Term.proj (♯2) 0 2 (by rfl) (by rfl)) (Term.letE (strExtract (♯2) (♯1) (♯0)) (♯0))))))

/-- The module up to and including `String.Slice.toString`. -/
def prog_String_Slice_toString : Program (d_String_Slice_toString :: sig_String_Slice_toString.decls) :=
  .cons d_String_Slice_toString sig_String_Slice_toString.h_names_unique tm_String_Slice_toString Program.nil

/-- The signature of the whole module. -/
def moduleSig : Sig := ⟨[d_String_Slice_toString], by decide⟩

/-- The module as a telescope: every body is written against the declarations before it, so the call graph is acyclic by construction.  It is built one declaration at a time, above, so that no single elaboration sees the whole telescope at once. -/
def program : Program moduleSig.decls :=
  prog_String_Slice_toString

end ProgramSnapshotsPBOPureFusion02
