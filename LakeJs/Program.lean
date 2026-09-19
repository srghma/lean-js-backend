module

public import LakeJs.CertGen

@[expose] public section

set_option autoImplicit false

/-!
# A whole module: a telescope of declarations

A `Term` is written against a `Sig`, the list of top-level names it may call, and a
`GlobalRef` is an index into that list.  This module is the other half: the **values** of
those declarations, and the structure that supplies them.

A `Program` is a telescope.  Each declaration's body is a closed term written against the
signature of the declarations that come **before** it, so:

* the call graph of a program is **acyclic by construction** — a declaration cannot call
  itself or anything later, because the index it would need does not exist;
* `Program.env` therefore builds the `GEnv` by a plain structural recursion, evaluating
  each body in the environment of its predecessors, with nothing to tie off;
* and `Program.run` runs a term of the whole signature against it, with no fuel.

Recursion is deliberately not here: it is `Term.fix`, inside a body, with its rank.  A
*mutual* clique of top-level Lean functions — `Tco03`'s `go`/`k`, `Tco04`'s
`test1`/`test2` — is therefore not a cycle between two declarations of a program but a
single `Term.fix` whose argument list carries a tag saying which member of the clique is
running, sharing one rank.  `LakeJs.Examples.WellFounded` builds exactly that.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

/-- **A program**: declarations in dependency order, each body closed and written against
    the signature of the declarations before it. -/
inductive Program : List GlobalDecl → Type where
  /-- The empty program. -/
  | nil : Program []
  /-- One more declaration, whose body may call the ones already declared. -/
  | cons : ∀ {ds : List GlobalDecl} (g : GlobalDecl) (h : declNamesUnique ds = true),
      Term ⟨ds, h⟩ [] [] g.ty → Program ds → Program (g :: ds)

/-- **The values of a program's declarations.**  Each body is run in the environment its
    predecessors built; there is no fixpoint to take, because there is no cycle. -/
def Program.env : ∀ {ds : List GlobalDecl}, Program ds → GEnv ds
  | _, .nil => .nil
  | _, .cons _ _ body rest => .cons (body.evalClosed rest.env) rest.env

/-- Running the body of the newest declaration: the equation of `Program.env`. -/
@[simp] theorem Program.env_cons {ds : List GlobalDecl} (g : GlobalDecl)
    (h : declNamesUnique ds = true) (body : Term ⟨ds, h⟩ [] [] g.ty) (rest : Program ds) :
    (Program.cons g h body rest).env = .cons (body.evalClosed rest.env) rest.env := rfl

/-- **Run a closed term against a program.**  This is the top-level entry point of the
    library: a module, a term of its signature, and a value — no fuel, no `Option`. -/
def Program.run {Sg : Sig} {τ : Ty} (p : Program Sg.decls) (t : Term Sg [] [] τ) : τ.den :=
  t.evalClosed p.env

/-- **Every program runs.**  Totality at the level of a whole module. -/
theorem Program.total {Sg : Sig} {τ : Ty} (p : Program Sg.decls) (t : Term Sg [] [] τ) :
    ∃ v : τ.den, p.run t = v :=
  ⟨p.run t, rfl⟩

/-! ## A worked module

Two declarations: `zero`, a constant, and `succOfZero`, which calls it.  The second is
written against the signature that declares the first, which is what makes the call
legal — and what makes a call in the other direction unwritable. -/

/-- The declaration `zero : Nat`. -/
def declZero : GlobalDecl := ⟨"zero", Ty.nat⟩

/-- The declaration `succOfZero : Nat`. -/
def declSucc : GlobalDecl := ⟨"succOfZero", Ty.nat⟩

/-- The signature of the worked module. -/
def demoSig : Sig := ⟨[declSucc, declZero], by decide⟩

/-- The worked module itself: `zero = 0`, and `succOfZero = zero + 1`. -/
def demoProgram : Program demoSig.decls :=
  .cons declSucc (by decide)
    (Term.callExtern (.prim2 .lean_nat_add)
      (.cons (.global .here) (.cons (Term.natL 1) .nil)))
    (.cons declZero (by decide) (Term.natL 0) .nil)

/-- The value of the second declaration, computed by the kernel from the whole module. -/
example : (show Nat from
    demoProgram.run (Sg := demoSig) (τ := Ty.nat) (.global .here)) = 1 := rfl

/-- And the value of the first. -/
example : (show Nat from
    demoProgram.run (Sg := demoSig) (τ := Ty.nat) (.global (.there .here))) = 0 := rfl

end LakeJs.Expr

end
