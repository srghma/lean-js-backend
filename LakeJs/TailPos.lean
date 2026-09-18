module

public import LakeJs.Subst

@[expose] public section

set_option autoImplicit false

/-!
# A jump belongs in tail position — and now it can stand nowhere else

A label exists so that a block shared by several paths is written — and emitted — **once**:
the target is a labelled block, and a jump to it is a `break`/`continue` of that label.
Two things have to hold for that to be possible.

* **A jump may not escape into a closure.**  A `Term` has no label context at all, so a
  jump cannot occur inside one — in particular not under a `Term.lam` or a
  `Term.lazyMk`, which is what matters, since a label of the target is function-local.
* **A jump may only stand where the block it is in answers**, i.e. in *tail position*.
  A jump is a `Tail.jmp`, and every position of a `Tail` is a tail position of the
  enclosing `Term.block`: the constructors of `Tail` end a block (`ret`, `jmp`) or
  continue it with the rest of the block as their last component (`letT`, `iteT`,
  `caseT`, `label`).  There is no shape of the grammar in which something happens
  *after* a jump.

This module used to hold `Term.tailOk`, a decidable check for the second condition, which
the old two-construct grammar (`Term.joinPoint` plus `Term.loop`) needed because a
`Term.jump` could stand in the argument of an application or in what a `let` binds.  With
the block/label unification of `TERM_DESIGN_ASSESSMENT.md` §3 the check has no work left
to do: the terms it refused are no longer terms.  What is left here is the statement of
that, and the examples it used to refuse and accept, now read as "does not typecheck" and
"typechecks".
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

variable {Sg : Sig}

/-! ## The discipline, as facts about the grammar -/

/-- **There is nothing to jump to out of a block.**  The tail of a `Term.block` is
    written in the empty label context, and that context has no label — so a jump out of
    the block being run cannot be written, and the evaluator of `LakeJs.Reduce` never
    meets one. -/
theorem LVar.not_mem_nil {ps : List Ty} (l : ([] : LCtx) ∋ₗ ps) : False := nomatch l

/-- **A jump never comes back.**  Reducing a label replaces a jump to it by the block it
    names — with the arguments bound in front (`Tail.letSpine`) and *nothing after it*,
    because a `Tail.jmp` has no continuation to keep.  That is the whole content of
    "a jump stands in tail position", and here it is an equation that holds by
    computation. -/
theorem Tail.lsubst0_jmp_head {Γ : Ctx} {Ω : LCtx} {ps : List Ty} {τ : Ty}
    (args : Spine Sg Γ ps) (body : Tail Sg (ps ++ Γ) Ω τ) :
    (Tail.jmp (Ω := ps :: Ω) .head args).lsubst0 body = Tail.letSpine args body := rfl

/-- **A jump to another label is left where it is.**  Reducing the innermost label does
    not touch a jump that targets one further out; it only drops that label from the
    context. -/
theorem Tail.lsubst0_jmp_tail {Γ : Ctx} {Ω : LCtx} {ps qs : List Ty} {τ : Ty}
    (l : Ω ∋ₗ qs) (args : Spine Sg Γ qs) (body : Tail Sg (ps ++ Γ) Ω τ) :
    (Tail.jmp (Ω := ps :: Ω) (.tail l) args).lsubst0 body
      = Tail.letSpine args (Tail.jmp l (Spine.vars qs)) := rfl

/-! ## What the old check refused, and what it accepted

Each example below is the counterpart of one of the terms `Term.tailOk` was written for.
The two it refused are not terms of the language any more — the commented lines do not
elaborate — and the ones it accepted are written out and typecheck. -/

section Examples

/-- The empty signature. -/
private def sigNone : Sig := ⟨[], rfl⟩

-- **A jump in the argument of an application** was the term the old check existed to
-- refuse: a `break` hands no value to the function waiting for one.  It cannot be
-- written now, because `Term.ap` takes `Term`s and a jump is not one — there is no
-- `Term` constructor for a jump at all:
--
-- private def jumpInArg : Term sigNone [] Ty.nat :=
--   .block (.label (ps := [Ty.nat]) false (.ret (♯0))
--     (.ret (.ap (.ap (.extern (.prim2 .lean_nat_add))
--       (.jmp .head (.cons (.lit (.nat 1)) .nil))) (.lit (.nat 2)))))
--
-- **A jump in what a `let` binds** is refused for the same reason: `Tail.letT` binds a
-- `Term`, and a jump is a `Tail`:
--
-- private def jumpInLet : Term sigNone [] Ty.nat :=
--   .block (.label (ps := [Ty.nat]) false (.ret (♯0))
--     (.letT (.jmp .head (.cons (.lit (.nat 1)) .nil))
--       (.ret (.ap (.ap (.extern (.prim2 .lean_nat_add)) (♯0)) (♯0)))))

/-- A jump in the **body** of a `let` — the tail of the block — is a term: this is the
    shape the old check accepted. -/
private def jumpInLetBody : Term sigNone [] Ty.nat :=
  .block
    (.label (ps := [Ty.nat]) false (.ret (♯0))
      (.letT (.lit (.nat 1)) (.jmp .head (.cons (♯0) .nil))))

/-- A jump out of a **loop** to a label bound outside it is a term too: a labelled block
    may be left from inside a loop, and the two labels are the same construct. -/
private def jumpFromLoop : Term sigNone [] Ty.nat :=
  .block
    (.label (ps := [Ty.nat]) false (.ret (♯0))
      (.label (ps := [Ty.nat]) true
        (.jmp (.tail .head) (.cons (♯0) .nil))
        (.jmp .head (.cons (.lit (.nat 0)) .nil))))

/-- And the shared tail of `Term.sharedTail` — a label jumped to from both arms of a
    branch — is the ordinary case. -/
example : Term sigNone [Ty.bool] Ty.nat := Term.sharedTail

end Examples

end LakeJs.Expr

end
