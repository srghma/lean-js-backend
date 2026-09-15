module

public import LakeJs.SourceToTy
public import LakeJs.TyMeta
public meta import LakeJs.TyMeta
public import LakeJs.TyPretty
meta import Lean

open NonEmpty.String

@[expose] public section

/-!
# A generator of Lean declarations, and the differential test it feeds

`LakeJs.SourceAgreement` checks by hand that the metaprogram `lean_ty%` and the
model translation `SrcDecl.toTy` agree on a handful of real declarations.  This
module does the same thing at volume: `gen_agreement n seed` *generates* `n`
pseudo-random Lean `inductive` declarations, elaborates them, runs `lean_ty%` on each,
writes the same declaration out as a `SrcDecl`, and emits an `example … := by decide`
comparing the two results.

So the answer to "generator, or a function?" is both, with different jobs:

* the **function** `SrcDecl.toTy` carries the theorems (`toTy_isOk_iff_supported`,
  `toTy_class`); a generator could never prove them, since it only samples;
* the **generator** tests the part no theorem can reach — the `MetaM` program that
  reads schemas out of the environment.  A disagreement here is a bug in
  `LakeJs.TyMeta`, and the test is a compile error.

The generated declarations are non-mutual, with two or three constructors, the first
of which never mentions the declared type (so the declaration is well-founded) and
the second of which always carries a field (so the declaration is never a field-less
enum, whose rendering the kernel cannot evaluate: `String.intercalate` does not
reduce).  Fields are drawn from `Int`, `String`, `Bool`, `Self`, `Array Self`,
`Option Self`, `Int × Self`, `Unit` and `Array Unit`, which exercises the direct,
guarded, nested and product occurrences, and the erasure of unit-like fields and of
containers over them.
-/

namespace LakeJs.SourceRandom

/-- The pretty-printed translation, as in `LakeJs.SourceExamples`. -/
def rendered (r : Except Source.Reject Ty) : Option String := r.toOption.map Ty.pretty

end LakeJs.SourceRandom

namespace LakeJs.SourceRandom

open Lean Elab Command

meta section

/-- One step of a linear congruential generator; the test inputs have to be
    reproducible, so no `IO.rand`. -/
def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

/-- The Lean source text of field type `code`, inside declaration `self`. -/
def leanTyOf (self : String) : Nat → String
  | 0 => "Int"
  | 1 => "String"
  | 2 => "Bool"
  | 3 => self
  | 4 => "Array " ++ self
  | 5 => "Option " ++ self
  | 6 => "Int × " ++ self
  | 7 => "Unit"
  | _ => "Array Unit"

/-- The `RawTy` source text of field type `code`. -/
def srcTyOf : Nat → String
  | 0 => ".ext .int"
  | 1 => ".ext .string"
  | 2 => ".ext .bool"
  | 3 => ".ref 0"
  | 4 => ".array (.ref 0)"
  | 5 => ".option (.ref 0)"
  | 6 => ".prod (.ext .int) (.ref 0)"
  | 7 => ".unitLike"
  | _ => ".array .unitLike"

/-- A field type that does not mention the declared type; `Unit` and `Array Unit` are
    included, so the generated tests exercise erasure too. -/
def nonSelfCode (k : Nat) : Nat :=
  match k % 5 with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 7
  | _ => 8

/-- Fields of one constructor: `(name, code)` pairs.  `selfOk = false` restricts the
    codes to those that do not mention the declared type. -/
def genFields (selfOk : Bool) (atLeastOne : Bool) (seed : Nat) :
    Nat × List (String × Nat) :=
  let s1 := lcg seed
  let count := (if atLeastOne then 1 else 0) + s1 % (if atLeastOne then 2 else 3)
  let rec go (n : Nat) (s : Nat) (acc : List (String × Nat)) : Nat × List (String × Nat) :=
    match n with
    | 0 => (s, acc.reverse)
    | k + 1 =>
        let s' := lcg s
        -- the *first* field of a constructor that must have one is never unit-like,
        -- so that constructor still carries a field after erasure (a declaration all
        -- of whose constructors are field-less is an enum, whose rendering the kernel
        -- cannot evaluate)
        let code :=
          if atLeastOne && k + 1 == count then (if selfOk then s' % 7 else s' % 3)
          else if selfOk then s' % 9 else nonSelfCode s'
        go k s' (("f" ++ toString k, code) :: acc)
  go count s1 []

/-- One generated declaration: its constructors, each with its fields. -/
def genDecl (seed : Nat) : Nat × List (String × List (String × Nat)) :=
  let s1 := lcg seed
  let nCtors := 2 + s1 % 2
  let rec go (i : Nat) (s : Nat) (acc : List (String × List (String × Nat))) :=
    match i with
    | 0 => (s, acc.reverse)
    | k + 1 =>
        let idx := nCtors - (k + 1)
        -- the first constructor is a base constructor; the second always has a field
        let (s', fields) := genFields (selfOk := idx != 0) (atLeastOne := idx == 1) s
        go k s' ((("c" ++ toString idx), fields) :: acc)
  go nCtors s1 []

/-- The Lean source text of one generated declaration, its `Ty`, its `SrcDecl` and the
    `example` comparing the two. -/
def declText (i : Nat) (ctors : List (String × List (String × Nat))) : String :=
  let name := "Gen" ++ toString i
  let ctorText := String.intercalate "\n"
    (ctors.map fun (tag, fields) =>
      "  | " ++ tag ++
        String.join (fields.map fun (fn, code) => " (" ++ fn ++ " : " ++ leanTyOf name code ++ ")"))
  let srcCtors := String.intercalate "\n           , "
    (ctors.map fun (tag, fields) =>
      "{ tag := nes!\"" ++ tag ++ "\", fields := [" ++
        String.intercalate ", "
          (fields.map fun (fn, code) => "(nes!\"" ++ fn ++ "\", " ++ srcTyOf code ++ ")") ++ "] }")
  "inductive " ++ name ++ " where\n" ++ ctorText ++ "\n\n" ++
  "def ty" ++ name ++ " : Ty := lean_ty% " ++ name ++ "\n\n" ++
  "def src" ++ name ++ " : LakeJs.Source.RawDecl :=\n" ++
  "  { block := [{ name := nes!\"" ++ name ++ "\"\n" ++
  "              , ctors := [ " ++ srcCtors ++ " ] }]\n" ++
  "    member := 0 }\n\n" ++
  "example : rendered (LakeJs.Source.RawDecl.toTy src" ++ name ++ ")"
    ++ " = some (Ty.pretty ty" ++ name ++ ") := by decide\n"

/-- Parse and elaborate one command. -/
def runText (text : String) : CommandElabM Unit := do
  let env ← getEnv
  match Parser.runParserCategory env `command text with
  | .error e => throwError "generated command does not parse: {e}\n{text}"
  | .ok stx  => elabCommand stx

/--
`gen_agreement n seed` generates `n` pseudo-random `inductive` declarations and, for
each, checks that `lean_ty%` and `SrcDecl.toTy` produce the same type.  Each check is
an `example … := by decide`, so a disagreement is a build error.
-/
elab "gen_agreement " n:num " seed " s:num : command => do
  let count := n.getNat
  let mut seed := s.getNat
  for i in [0:count] do
    let (seed', ctors) := genDecl seed
    seed := seed'
    let text := declText i ctors
    for piece in text.splitOn "\n\n" do
      if !piece.trimAscii.isEmpty then
        runText piece

end

end LakeJs.SourceRandom

section

open NonEmpty.String
open LakeJs.SourceRandom

namespace LakeJs.SourceRandomTests

open LakeJs.SourceRandom

/-! ## The generated test suite

Twenty generated declarations, on which the metaprogram and the model agree.  Change
the seed to get a different twenty. -/

gen_agreement 20 seed 20250915

/-- The generated declarations really are there: the last one translates, and its two
    translations are the ones compared above. -/
example : (rendered (LakeJs.Source.RawDecl.toTy srcGen19)).isSome = true := by decide
example : (LakeJs.Source.RawDecl.classify srcGen19).isSome = true := by decide

end LakeJs.SourceRandomTests

end

end
