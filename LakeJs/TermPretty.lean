import LakeJs.Expr
import LakeJs.TyPretty
import LakeJs.ExternsMeta

/-!
# Printing a `Term`

The JavaScript a module compiles to is what the backend is *for*, but it is not what the
backend reasons about: the optimiser rewrites `Term`s, and a `Term` is invisible in the
`.js` file — a rewrite that fired and a rewrite that did not fire can print alike.  This
file writes a `Term` down as an indented s-expression, so that the input of the optimiser
can be read beside its output.

The rendering is complete and unambiguous:

* every binding form names the types it binds (`(lamN [nat nat] …)`), so the de Bruijn
  index of a variable can be resolved by counting binders out from its occurrence;
* a variable prints as its index *and* its type (`(var 0 : nat)`);
* a reference to a top-level declaration prints as the name the signature gives it, and
  an extern as the runtime name it is called by, so the two cannot be confused;
* the tag and the field of a constructor, a projection and a case branch are the numbers
  the term holds, not names the printer invents.

`LakeJs.Compile` writes the rendering of the terms **before** the optimiser runs into
`<Module>-Expr.txt`, beside the `.js` file that holds the terms after it.
-/

namespace LakeJs.TermPretty

open LakeJs
open LakeJs.Ty
open LakeJs.Layout (FieldLayout ObjLayout)
open LakeJs.Expr

/-- `n` spaces. -/
def pad (n : Nat) : String := String.join (List.replicate n " ")

/-- A literal, as the Lean constant it is. -/
def Lit.pretty : ∀ {p : LeanPrimTy}, Lit p → String
  | _, .bool b => toString b
  | _, .nat n => toString n
  | _, .int i => toString i
  | _, .bitvec (n := n) v => toString v.toNat ++ "#" ++ toString n
  | _, .uint8 v => toString v.toNat ++ "u8"
  | _, .uint16 v => toString v.toNat ++ "u16"
  | _, .uint32 v => toString v.toNat ++ "u32"
  | _, .uint64 v => toString v.toNat ++ "u64"
  | _, .usize v => toString v.toNat ++ "usize"
  | _, .int8 v => toString v.toInt ++ "i8"
  | _, .int16 v => toString v.toInt ++ "i16"
  | _, .int32 v => toString v.toInt ++ "i32"
  | _, .int64 v => toString v.toInt ++ "i64"
  | _, .isize v => toString v.toInt ++ "isize"
  | _, .char c => "'" ++ String.singleton c ++ "'"
  | _, .string s => s.quote
  | _, .byteArray bs => "bytes" ++ toString (bs.toList.map (·.toNat))
  | _, .name n => "`" ++ toString n
  | _, .stringPos p => "pos " ++ toString p
  | _, .substring s a b => "substring " ++ s.quote ++ " " ++ toString a ++ " " ++ toString b
  | _, .stringSlice s a b => "slice " ++ s.quote ++ " " ++ toString a ++ " " ++ toString b
  | _, .float f => toString f
  | _, .float32 f => toString f
  | _, .floatArray fs => "floats" ++ toString (fs.toList.map toString)

/-- The name of an operation that is JavaScript’s rather than Lean’s, with the type it
    is used at where it has one. -/
def JsOp.pretty : ∀ {σs : List Ty} {τ : Ty}, JsOp σs τ → String
  | _, _, .cast σ τ => "cast " ++ Ty.pretty σ ++ " → " ++ Ty.pretty τ
  | _, _, .boolAnd => "boolAnd"
  | _, _, .boolOr => "boolOr"
  | _, _, .boolNot => "boolNot"
  | _, _, .boolBEq => "boolBEq"
  | _, _, .charBEq => "charBEq"
  | _, _, .natSubExact => "natSubExact"
  | _, _, .toStr τ => "toStr " ++ Ty.pretty τ

/-- A list of types, as the printer writes the binders of a term. -/
def tyList (σs : List Ty) : String := "[" ++ Ty.prettyList σs ++ "]"

mutual

/-- A term, as the lines of an indented s-expression: the head of a node on its own
    line, its children indented two spaces below it. -/
def Term.ppLines {Sg : Sig} : ∀ {Γ : Ctx} {τ : Ty}, Nat → Term Sg Γ τ → List String
  | _, τ, i, .var v => [pad i ++ "(var " ++ toString v.index ++ " : " ++ Ty.pretty τ ++ ")"]
  | _, _, i, .lit l => [pad i ++ "(lit " ++ Lit.pretty l ++ ")"]
  | _, _, i, .global r => [pad i ++ "(global " ++ r.name ++ ")"]
  | _, _, i, .extern e => [pad i ++ "(extern " ++ e.cName ++ ")"]
  | _, _, i, .lamN (params := ps) b =>
      (pad i ++ "(lamN " ++ tyList ps) :: Term.ppLines (i + 2) b ++ [pad i ++ ")"]
  | _, _, i, .apN f args =>
      (pad i ++ "(apN") :: Term.ppLines (i + 2) f ++ Spine.ppLines (i + 2) args
        ++ [pad i ++ ")"]
  | _, _, i, .lamProd (params := ps) rets =>
      (pad i ++ "(lamProd " ++ tyList ps) :: Spine.ppLines (i + 2) rets ++ [pad i ++ ")"]
  | _, _, i, .callProd f args j =>
      (pad i ++ "(callProd #" ++ toString j.val) :: Term.ppLines (i + 2) f
        ++ Spine.ppLines (i + 2) args ++ [pad i ++ ")"]
  | _, _, i, .jsOp op args =>
      (pad i ++ "(jsOp " ++ JsOp.pretty op) :: Spine.ppLines (i + 2) args
        ++ [pad i ++ ")"]
  | _, _, i, .letE (σ := σ) e b =>
      (pad i ++ "(letE : " ++ Ty.pretty σ) :: Term.ppLines (i + 2) e
        ++ Term.ppLines (i + 2) b ++ [pad i ++ ")"]
  | _, _, i, .ite c t u =>
      (pad i ++ "(ite") :: Term.ppLines (i + 2) c ++ Term.ppLines (i + 2) t
        ++ Term.ppLines (i + 2) u ++ [pad i ++ ")"]
  | _, τ, i, .ctor j _ _ args =>
      (pad i ++ "(ctor " ++ toString j ++ " : " ++ Ty.pretty τ) :: Spine.ppLines (i + 2) args
        ++ [pad i ++ ")"]
  | _, τ, i, .proj e j k _ =>
      (pad i ++ "(proj " ++ toString j ++ " " ++ toString k ++ " : " ++ Ty.pretty τ)
        :: Term.ppLines (i + 2) e ++ [pad i ++ ")"]
  | _, _, i, .tagOf e _ =>
      (pad i ++ "(tagOf") :: Term.ppLines (i + 2) e ++ [pad i ++ ")"]
  | _, _, i, .lazyMk e =>
      (pad i ++ "(lazy") :: Term.ppLines (i + 2) e ++ [pad i ++ ")"]
  | _, _, i, .lazyForce e =>
      (pad i ++ "(force") :: Term.ppLines (i + 2) e ++ [pad i ++ ")"]
  | _, _, i, .caseTag s alts _ =>
      (pad i ++ "(caseTag") :: Term.ppLines (i + 2) s ++ Alts.ppLines (i + 2) alts
        ++ [pad i ++ ")"]
  | _, _, i, .loop (σs := σs) init body =>
      (pad i ++ "(loop " ++ tyList σs) :: Spine.ppLines (i + 2) init
        ++ Body.ppLines (i + 2) body ++ [pad i ++ ")"]
  | _, _, i, .joinPoint (params := ps) body rest =>
      (pad i ++ "(joinPoint " ++ tyList ps) :: Term.ppLines (i + 2) body
        ++ Term.ppLines (i + 2) rest ++ [pad i ++ ")"]
  | _, _, i, .jump v args =>
      (pad i ++ "(jump " ++ toString v.index) :: Spine.ppLines (i + 2) args
        ++ [pad i ++ ")"]

/-- `Term.ppLines`, on every term of a spine. -/
def Spine.ppLines {Sg : Sig} :
    ∀ {Γ : Ctx} {σs : List Ty}, Nat → Spine Sg Γ σs → List String
  | _, _, _, .nil => []
  | _, _, i, .cons t rest => Term.ppLines i t ++ Spine.ppLines i rest

/-- `Term.ppLines`, on every branch of a case. -/
def Alts.ppLines {Sg : Sig} :
    ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat}, Nat → Alts Sg Γ τ tags → List String
  | _, _, _, i, .deflt t => (pad i ++ "(default") :: Term.ppLines (i + 2) t ++ [pad i ++ ")"]
  | _, _, _, i, .cons tag t rest =>
      (pad i ++ "(tag " ++ toString tag) :: Term.ppLines (i + 2) t ++ [pad i ++ ")"]
        ++ Alts.ppLines i rest

/-- `Term.ppLines`, inside a loop body. -/
def Body.ppLines {Sg : Sig} :
    ∀ {Γ : Ctx} {σs : List Ty} {τ : Ty}, Nat → Body Sg Γ σs τ → List String
  | _, _, _, i, .ret t => (pad i ++ "(ret") :: Term.ppLines (i + 2) t ++ [pad i ++ ")"]
  | _, _, _, i, .cont args =>
      (pad i ++ "(cont") :: Spine.ppLines (i + 2) args ++ [pad i ++ ")"]
  | _, _, _, i, .letB (σ := σ) e b =>
      (pad i ++ "(letB : " ++ Ty.pretty σ) :: Term.ppLines (i + 2) e
        ++ Body.ppLines (i + 2) b ++ [pad i ++ ")"]
  | _, _, _, i, .iteB c t u =>
      (pad i ++ "(iteB") :: Term.ppLines (i + 2) c ++ Body.ppLines (i + 2) t
        ++ Body.ppLines (i + 2) u ++ [pad i ++ ")"]
  | _, _, _, i, .joinPointB (params := ps) body rest =>
      (pad i ++ "(joinPointB " ++ tyList ps) :: Term.ppLines (i + 2) body
        ++ Body.ppLines (i + 2) rest ++ [pad i ++ ")"]

end

/-- A term, as one string. -/
def Term.pretty {Sg : Sig} {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ) : String :=
  String.intercalate "\n" (Term.ppLines 0 t)

end LakeJs.TermPretty
