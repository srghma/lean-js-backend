module

public import LakeJs.Expr

@[expose] public section

/-!
# Looking things up while building a `Term`

Building a `Term` while reading someone else's intermediate representation needs a
*proof* that two types agree — `Term.apN` only accepts arguments whose types are the
parameter list of the function, and `Term.var` only accepts an index whose type is the
one the context has there.

`Ty` has a `DecidableEq` instance, so that proof is just `if h : σ = τ then …`: there
is no partial "equality where it can be had" any more, and nothing is refused because
two types could not be compared.
-/

namespace LakeJs.Lookup

open LakeJs
open LakeJs.Expr

/-- Look a name up in a signature, at a type that must agree with the declared one. -/
def GlobalRef.find? : (Sg : Sig) → (name : String) → (τ : Ty) → Option (GlobalRef Sg τ)
  | [], _, _ => none
  | g :: Sg, nm, τ =>
    if g.name == nm then
      if h : g.ty = τ then some (h ▸ GlobalRef.here)
      else (GlobalRef.find? Sg nm τ).map .there
    else
      (GlobalRef.find? Sg nm τ).map .there

/-- Move a term to an equal type. -/
def Term.coerce? {Sg : Sig} {Γ : Ctx} {τ : Ty} (σ : Ty) (t : Term Sg Γ τ) :
    Option (Term Sg Γ σ) :=
  if h : τ = σ then some (h ▸ t) else none

/-- The variable `i` steps from the front of the context, if it has type `τ` there. -/
def Var.at? : (Γ : Ctx) → (i : Nat) → (τ : Ty) → Option (Γ ∋ τ)
  | [], _, _ => none
  | σ :: _, 0, τ => if h : σ = τ then some (h ▸ Var.head) else none
  | _ :: Γ, i + 1, τ => (Var.at? Γ i τ).map Var.tail

/-- The type the context has `i` steps from its front. -/
def Ctx.get? : (Γ : Ctx) → (i : Nat) → Option Ty
  | [], _ => none
  | σ :: _, 0 => some σ
  | _ :: Γ, i + 1 => Ctx.get? Γ i

/-- A term of an unknown type: what the translation of a sub-expression answers with. -/
abbrev SomeTerm (Sg : Sig) (Γ : Ctx) := Σ τ : Ty, Term Sg Γ τ

/-- Assemble a spine of the given types out of terms whose types are not yet known to
    match, coercing each one. -/
def Spine.ofList? {Sg : Sig} {Γ : Ctx} :
    (σs : List Ty) → List (SomeTerm Sg Γ) → Option (Spine Sg Γ σs)
  | [], [] => some .nil
  | σ :: σs, t :: ts =>
      match Term.coerce? σ t.2, Spine.ofList? σs ts with
      | some t', some rest => some (.cons t' rest)
      | _, _ => none
  | _, _ => none

end LakeJs.Lookup

end
