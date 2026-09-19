module

public import LakeJs.Expr
public import LakeJs.TyPretty

@[expose] public section

set_option autoImplicit false

/-!
# Printing a `Term`

Item 12 of `TERM_ONE_GRAMMAR_ASSESSMENT.md`'s phase 4: the test run writes, per module, a
`-Expr.txt` holding the `Term` tree of each declaration, with 🎯 on the module's public
entry points and 📦 on the private declarations they pulled in.  `LakeJs.Examples.Dump`
produces that file for the worked examples; this module is the printer it uses.

The notation is the one the examples are written in:

| written | means |
| :-- | :-- |
| `♯n` | the local variable at de Bruijn index `n` |
| `@name` | a module-level declaration (`Term.global`) |
| `ƛ e` | `Term.lam` |
| `(f ⬝ a)` | `Term.ap` |
| `5#` | a literal |
| `extern⟨σ…⟩` | `Term.extern` — a call of the runtime |
| `fix (σ…) measure [ … ] body { … } stuck { … }` | `Term.fix` |
| `self⟨↓⟩(…)` | `Term.selfCall`; the descent marker has nothing after it, because there is nothing a term may say about the measure |
| `join(σ…) { … } in { … }` | `Tail.join` |
| `jmp ℓn (…)` | `Tail.jmp` |

A `Term.extern` prints its argument and result types rather than the runtime's name for
it: the catalogue of `LakeJs.Externs` is indexed by type, and the table that maps an entry
to its C name is the emitter's, not the grammar's.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty
open LakeJs.Layout (FieldLayout)

/-- Print a literal. -/
def litPretty : ∀ {p : LeanPrimTy}, LeanPrimLit p → String
  | _, .bool b => if b then "true" else "false"
  | _, .nat n => toString n ++ "#"
  | _, .int i => toString i ++ "i"
  | _, .bitvec v => toString v
  | _, .uint8 v => toString v ++ "u8"
  | _, .uint16 v => toString v ++ "u16"
  | _, .uint32 v => toString v ++ "u32"
  | _, .uint64 v => toString v ++ "u64"
  | _, .usize v => toString v ++ "usize"
  | _, .int8 v => toString v ++ "i8"
  | _, .int16 v => toString v ++ "i16"
  | _, .int32 v => toString v ++ "i32"
  | _, .int64 v => toString v ++ "i64"
  | _, .isize v => toString v ++ "isize"
  | _, .char c => "'" ++ toString c ++ "'"
  | _, .string s => "\"" ++ s ++ "\""
  | _, .stringPos n => "pos" ++ toString n
  | _, .substring _ => "substring"
  | _, .stringSlice _ => "slice"
  | _, .float f => toString f
  | _, .float32 f => toString f

/-- Print the signature of a call of the runtime: an extern is identified by the types it
    takes and the type it answers with. -/
def externPretty {σs : List Ty} {τ : Ty} (_e : Externs σs τ) : String :=
  "extern⟨" ++ Ty.prettyList σs ++ " ⇒ " ++ τ.pretty ++ "⟩"

/-- `n` spaces. -/
def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

mutual

/-- Print a term at the given indentation. -/
def Term.pretty {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {τ : Ty} (t : Term Sg Γ Ρ τ) (ind : Nat) :
    String :=
  match t with
  | .var x => "♯" ++ toString x.index
  | .lam b => "ƛ " ++ b.pretty ind
  | .ap f a => "(" ++ f.pretty ind ++ " ⬝ " ++ a.pretty ind ++ ")"
  | .lit l => litPretty l
  | .global r => "@" ++ r.name
  | .extern e => externPretty e
  | .lazyMk e => "lazy { " ++ e.pretty ind ++ " }"
  | .lazyForce e => "force " ++ e.pretty ind
  | .letE e b => "let ♯ := " ++ e.pretty ind ++ ";\n" ++ spaces ind ++ b.pretty ind
  | .ite c a b =>
      "if " ++ c.pretty ind ++ " then " ++ a.pretty ind ++ " else " ++ b.pretty ind
  | .ctor i fields _ s =>
      "ctor" ++ toString i ++ "(" ++ Ty.prettyList fields ++ ")(" ++ s.pretty ind ++ ")"
  | .proj e i j _ _ =>
      "proj" ++ toString i ++ "." ++ toString j ++ "(" ++ e.pretty ind ++ ")"
  | .tagOf e _ => "tag(" ++ e.pretty ind ++ ")"
  | .structSize e => "size(" ++ e.pretty ind ++ ")"
  | .caseTag scrut alts _ =>
      "case " ++ scrut.pretty ind ++ " of\n" ++ alts.pretty (ind + 2)
  | .block b => "block {\n" ++ spaces (ind + 2) ++ b.pretty (ind + 2) ++ "\n" ++
      spaces ind ++ "}"
  | .fix ps _ measure body stuck =>
      "fix (" ++ Ty.prettyList ps ++ ")" ++
        " measure [ " ++ measure.pretty (ind + 2) ++ " ] body {\n" ++
        spaces (ind + 2) ++ body.pretty (ind + 2) ++ "\n" ++
        spaces ind ++ "} stuck { " ++ stuck.pretty (ind + 2) ++ " }"
  | .selfCall r s => "self" ++ toString r.index ++ "⟨↓⟩(" ++ s.pretty ind ++ ")"

/-- Print a spine of arguments, comma separated. -/
def Spine.pretty {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {σs : List Ty} (s : Spine Sg Γ Ρ σs)
    (ind : Nat) : String :=
  match s with
  | .nil => ""
  | .cons a .nil => a.pretty ind
  | .cons a rest => a.pretty ind ++ ", " ++ rest.pretty ind

/-- Print the alternatives of a `case`, one per line. -/
def Alts.pretty {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {σ τ : Ty} {tags : List Nat} {full : Bool}
    (alts : Alts Sg Γ Ρ σ τ tags full) (ind : Nat) : String :=
  match alts with
  | .deflt e => spaces ind ++ "| _ => " ++ e.pretty (ind + 2) ++ "\n"
  | .nilFull => ""
  | .cons tag fields _ body rest =>
      spaces ind ++ "| " ++ toString tag ++ "(" ++ Ty.prettyList fields ++ ") => " ++
        body.pretty (ind + 2) ++ "\n" ++ rest.pretty ind

/-- Print a block body. -/
def Tail.pretty {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {τ : Ty} (b : Tail Sg Γ Ω Ρ τ)
    (ind : Nat) : String :=
  match b with
  | .ret e => "ret " ++ e.pretty ind
  | .jmp l s => "jmp ℓ" ++ toString l.index ++ "(" ++ s.pretty ind ++ ")"
  | .letT e rest => "let ♯ := " ++ e.pretty ind ++ ";\n" ++ spaces ind ++ rest.pretty ind
  | .iteT c t e =>
      "if " ++ c.pretty ind ++ " then " ++ t.pretty ind ++ " else " ++ e.pretty ind
  | .caseT scrut alts _ =>
      "case " ++ scrut.pretty ind ++ " of\n" ++ alts.pretty (ind + 2)
  | .join ps body rest =>
      "join(" ++ Ty.prettyList ps ++ ") {\n" ++
        spaces (ind + 2) ++ body.pretty (ind + 2) ++ "\n" ++
        spaces ind ++ "} in {\n" ++
        spaces (ind + 2) ++ rest.pretty (ind + 2) ++ "\n" ++ spaces ind ++ "}"

/-- Print the alternatives of a `case` in tail position. -/
def AltsT.pretty {Sg : Sig} {Γ : Ctx} {Ω : LCtx} {Ρ : RCtx} {σ τ : Ty} {tags : List Nat}
    {full : Bool} (alts : AltsT Sg Γ Ω Ρ σ τ tags full) (ind : Nat) : String :=
  match alts with
  | .deflt b => spaces ind ++ "| _ => " ++ b.pretty (ind + 2) ++ "\n"
  | .nilFull => ""
  | .cons tag fields _ body rest =>
      spaces ind ++ "| " ++ toString tag ++ "(" ++ Ty.prettyList fields ++ ") => " ++
        body.pretty (ind + 2) ++ "\n" ++ rest.pretty ind

end

/-- One entry of a `-Expr.txt`: the marker, the name, the type and the tree.  `target`
    marks a public entry point (🎯); the others are the private declarations the
    translation pulled in (📦). -/
def prettyEntry {Sg : Sig} {Γ : Ctx} {Ρ : RCtx} {τ : Ty}
    (target : Bool) (name : String) (t : Term Sg Γ Ρ τ) : String :=
  let marker := if target then "🎯" else "📦"
  "════ " ++ marker ++ " " ++ name ++ " : " ++ τ.pretty ++ "\n" ++ t.pretty 0 ++ "\n"

end LakeJs.Expr

end
