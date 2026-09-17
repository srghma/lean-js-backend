import LakeJs.Expr
import LakeJs.ExternsMeta
import LakeJs.Surface
import LakeJs.SurfaceParse

/-!
# Writing a `Term` down: the delaborator

`LakeJs.TermElab` reads a `[LEAN| … ]` fragment and builds a `Term`.  This module is the
other direction: it takes a `Term` — with its de Bruijn indices, its signature indices
and its proofs — and writes the fragment that builds it again.

Two decisions make the output read back:

* **a name is its depth.**  The slot a binder introduces when the context has length `L`
  is called `v<L>`, whatever binder introduces it, so a name never has to be invented,
  never collides with a name in scope, and the `vars` section of the header can be
  written down from the context alone.
* **nothing is dropped.**  The type of every binder, the type arguments of a polymorphic
  extern (`Externs.tyArgs`), the tag of a constructor and the index of a projection are
  all written out, and a floating point constant is written as the bits of its
  representation, so the text is exact rather than rounded.

The proofs a `Term` carries are *not* written: they are recomputed by `rfl` when the
fragment is read, which is possible exactly because they are proofs of decidable facts
about the types that are written.
-/

namespace LakeJs.TermDeelab

open LakeJs
open LakeJs.Ty
open LakeJs.Expr
open LakeJs.Surface

/-- The name of the context slot whose index is `idx`, in a context of length `len`:
    the depth of the slot, counted from the outermost. -/
def nameAt (len idx : Nat) : String := "v" ++ toString (len - 1 - idx)

/-- The binders a list of parameter types introduces, in the order the parameters are
    written, when the context they extend has length `base`. -/
def paramNames (base : Nat) : List Ty → List SParam
  | [] => []
  | t :: ts => ("v" ++ toString base, t) :: paramNames (base + 1) ts

/-- The header's `vars` section: one binder per slot of the context, index 0 first. -/
def ctxDecls (Γ : Ctx) : List SParam :=
  let len := Γ.length
  let rec go (i : Nat) : List Ty → List SParam
    | [] => []
    | t :: ts => (nameAt len i, t) :: go (i + 1) ts
  go 0 Γ

/-- The header's `glob` section: one binder per declaration of the signature. -/
def sigDecls (Sg : Sig) : List SParam := Sg.map fun g => (g.name, g.ty)

/-- A constant, as it is written. -/
def litOf : ∀ {p : LeanPrimTy}, Lit p → SLit
  | _, .bool b => .bool b
  | _, .nat n => .nat n
  | _, .int i => .int i
  | _, .bitvec (n := n) v => .bitvec n v.toNat
  | _, .uint8 v => .uint8 v.toNat
  | _, .uint16 v => .uint16 v.toNat
  | _, .uint32 v => .uint32 v.toNat
  | _, .uint64 v => .uint64 v.toNat
  | _, .usize v => .usize v.toNat
  | _, .int8 v => .int8 v.toInt
  | _, .int16 v => .int16 v.toInt
  | _, .int32 v => .int32 v.toInt
  | _, .int64 v => .int64 v.toInt
  | _, .isize v => .isize v.toInt
  | _, .char c => .char c
  | _, .string s => .string s
  | _, .byteArray bs => .byteArray (bs.toList.map (·.toNat))
  | _, .name n => .name n.toString
  | _, .stringPos p => .stringPos p
  | _, .substring s a b => .substring s a b
  | _, .stringSlice s a b => .stringSlice s a b
  | _, .float f => .float f.toBits
  | _, .float32 f => .float32 f.toBits
  | _, .floatArray fs => .floatArray (fs.toList.map (·.toBits))

/-- An operation that is JavaScript's rather than Lean's, as it is written. -/
def opOf : ∀ {σs : List Ty} {τ : Ty}, JsOp σs τ → SOp
  | _, _, .cast σ τ => .cast σ τ
  | _, _, .boolAnd => .boolAnd
  | _, _, .boolOr => .boolOr
  | _, _, .boolNot => .boolNot
  | _, _, .boolBEq => .boolBEq
  | _, _, .charBEq => .charBEq
  | _, _, .natSubExact => .natSubExact
  | _, _, .toStr τ => .toStr τ

mutual

/-- A term, as it is written. -/
def termOf {Sg : Sig} : ∀ {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → STerm
  | Γ, _, .var v => .var (nameAt Γ.length v.index)
  | _, _, .lit l => .lit (litOf l)
  | _, _, .global r => .var r.name
  | _, _, .extern e => .extern e.cName e.tyArgs
  | Γ, _, .lamN (params := ps) b => .lam (paramNames Γ.length ps) (termOf b)
  | _, _, .apN f args => .app (termOf f) (spineOf args)
  | Γ, _, .lamProd (params := ps) rets => .lamProd (paramNames Γ.length ps) (spineOf rets)
  | _, _, .callProd f args i => .callProd i.val (termOf f) (spineOf args)
  | _, _, .jsOp op args => .op (opOf op) (spineOf args)
  | _, _, .lazyMk e => .lazyMk (termOf e)
  | _, _, .lazyForce e => .lazyForce (termOf e)
  | Γ, _, .letE (σ := σ) e b => .letE ("v" ++ toString Γ.length) σ (termOf e) (termOf b)
  | _, _, .ite c t e => .ite (termOf c) (termOf t) (termOf e)
  | _, τ, .ctor i _ _ args => .ctor i τ (spineOf args)
  | _, _, .proj e i j _ => .proj i j (termOf e)
  | _, _, .tagOf e _ => .tagOf (termOf e)
  | _, _, .caseTag s alts _ => .caseTag (termOf s) (altsOf alts)
  | Γ, _, .loop (σs := σs) init body =>
      .loop (paramNames Γ.length σs) (spineOf init) (bodyOf body)
  | Γ, _, .joinPoint (params := ps) (σ := σ) body rest =>
      .joinPoint ("v" ++ toString Γ.length) (paramNames Γ.length ps) σ
        (termOf body) (termOf rest)
  | Γ, _, .jump v args => .jump (nameAt Γ.length v.index) (spineOf args)

/-- A spine, as it is written. -/
def spineOf {Sg : Sig} : ∀ {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → SSpine
  | _, _, .nil => .nil
  | _, _, .cons t rest => .cons (termOf t) (spineOf rest)

/-- The branches of a case, as they are written. -/
def altsOf {Sg : Sig} :
    ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat}, Alts Sg Γ τ tags → SAlts
  | _, _, _, .deflt t => .deflt (termOf t)
  | _, _, _, .cons tag t rest => .cons tag (termOf t) (altsOf rest)

/-- A loop body, as it is written. -/
def bodyOf {Sg : Sig} :
    ∀ {Γ : Ctx} {σs : List Ty} {τ : Ty}, Body Sg Γ σs τ → SBody
  | _, _, _, .ret t => .ret (termOf t)
  | _, _, _, .cont args => .cont (spineOf args)
  | Γ, _, _, .letB (σ := σ) e b =>
      .letB ("v" ++ toString Γ.length) σ (termOf e) (bodyOf b)
  | _, _, _, .iteB c t e => .iteB (termOf c) (bodyOf t) (bodyOf e)
  | Γ, _, _, .joinPointB (params := ps) (σ := σ) body rest =>
      .joinPointB ("v" ++ toString Γ.length) (paramNames Γ.length ps) σ
        (termOf body) (bodyOf rest)

end

/-- A term, as the whole fragment that builds it again: its type, the signature it is
    written against, the context it is written in, and the code. -/
def embedOf {Sg : Sig} {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ) : SEmbed :=
  { sig := some τ, glob := sigDecls Sg, vars := ctxDecls Γ, code := termOf t }

end LakeJs.TermDeelab

namespace LakeJs.Expr.Term

open LakeJs.Expr
open LakeJs.Surface

/-- The text of the `[LEAN| … ]` fragment that builds this term: the delaborator. -/
def deelab {Sg : Sig} {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ) : String :=
  (LakeJs.TermDeelab.embedOf t).print

/-- The delaborated term, brackets and all, as it would be written in a Lean file. -/
def deelabEmbed {Sg : Sig} {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ) : String :=
  "[LEAN|\n" ++ t.deelab ++ "\n]"

/-- Does the delaborated term read back as itself?  The text this term delaborates to
    is parsed again and printed again, and the two texts must agree: the parser of
    `LakeJs.SurfaceParse` accepts everything the delaborator writes, and reads it as the
    tree that was written.  (The step from the tree to a `Term` is Lean's own
    elaboration, which `LakeJs.TermSyntaxSpec` checks with `rfl` instead.) -/
def roundTrips {Sg : Sig} {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ) : Bool :=
  let s := t.deelab
  match LakeJs.Surface.parseEmbed s with
  | .ok e => e.print == s
  | .error _ => false

end LakeJs.Expr.Term
