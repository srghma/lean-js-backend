module

public import LakeJs.Reduce

@[expose] public section

/-!
# Progress: a closed term is an answer, or it runs

`LakeJs.Reduce` says how a `Term` runs.  This module says that it *does* run: a closed
term — one in the empty variable context — is either an answer (`Value`, which includes
the `Neutral` terms that wait for something outside the language, such as a top-level
declaration of the signature) or it takes a `Step`.  `Tail.progress` is the same statement
for the tail of a block, in the empty label context: it answers the block, waits for
something outside the language, or steps.

`Term.progress` is that theorem, and it leaves **no shape of the language out**.  Three
things make it true.

* **Every function of the runtime the language can mention has a total meaning.**  The
  δ-rules of `Step` carry no side condition `eval? … = some r`: `eval` is a total
  function for each of the four terminal families of the catalogue, so a saturated
  application of one to literals is *always* a redex.  The entries that denoted no
  function of their arguments' values are commented out of
  `LakeJs.LeanInitPureExterns` rather than left to make the evaluator stick.
* **`Term` is intrinsically typed**, so a call is never stuck for the reason a call is
  stuck in an untyped language: `Term.ap` asks for a function of type `σ ⇒ τ` and an
  argument of type `σ`, and `Term.extern` is typed by the catalogue entry it names, so
  `lean_int_add` applied to a `Float` is not a *term*, and no evaluator has to answer for
  it.  `externTy_int_add` below is the positive half of that statement — the type of the
  entry, spelled out — and the line under it is the ill-typed application, which does not
  compile and is therefore kept as a comment.
* **A field read is sound by construction.**  `Term.proj` carries `hOne`, the evidence
  that the type it reads a field of has exactly *one* constructor, so the constructor the
  value carries is the constructor the projection speaks about.  This is what used to be
  missing: `(none).1` at `Option Nat` was a closed, well-typed term that no rule applied
  to.  It is not a term any more (see `Stuck` at the end of the file), and `Term.proj`
  needs no exclusion from the theorem.
-/

namespace LakeJs.Expr

open LakeJs
open LakeJs.Ty

variable {Sg : Sig}

/-! ## Canonical forms at a tagged type -/

/-- Only a boolean is a terminal type with a layout: `Nat` is not an object, and `n._1`
    is not a thing to emit. -/
theorem isTagged_prim {p : LeanPrimTy} (h : (Ty.prim p).isTagged = true) : p = .bool := by
  cases p <;> simp_all [Ty.isTagged, Ty.layout?]

/-- A case dispatches on a value of an object type, and the only terminal object type is
    the boolean. -/
theorem caseOk_prim {p : LeanPrimTy} {full : Bool} {tags : List Nat}
    (h : (Ty.prim p).caseOkAlts full tags = true) : p = .bool := by
  cases full <;>
    cases p <;>
      simp_all [Ty.caseOkAlts, Ty.caseOk, Ty.caseOkFull, Ty.numCtors?, Ty.layout?]

/-! ## Reading a field of a one-constructor type -/

/-- A field is a field of a constructor the type has. -/
theorem ctorFields?_of_fieldTy? {σ τ : Ty} {i j : Nat} (h : σ.fieldTy? i j = some τ) :
    ∃ fs, σ.ctorFields? i = some fs := by
  cases hc : σ.ctorFields? i with
  | none => rw [Ty.fieldTy?, hc] at h; exact absurd h (by simp)
  | some fs => exact ⟨fs, rfl⟩

/-- …and it is the field of that constructor's layout. -/
theorem getElem?_of_fieldTy? {σ τ : Ty} {i j : Nat} {fs : Layout.FieldLayout}
    (hc : σ.ctorFields? i = some fs) (h : σ.fieldTy? i j = some τ) : fs[j]? = some τ := by
  rw [Ty.fieldTy?, hc] at h; exact h

/-! ## The shapes the evaluator has to decide

Each of these is the whole of one case of the progress proof: what to do with an
application, a constructor, a field read, a tag test and a dispatch once the subterm the
evaluator descends into is known to be an answer. -/

/-- An application of an answer to an answer is an answer or steps: the function is a
    lambda (β), or it is a function of the runtime saturated by literals (δ), or it is
    waiting for something outside the language and the application is neutral. -/
theorem value_or_step_ap {σ τ : Ty} {f : Term Sg [] (σ ⇒ τ)} {a : Term Sg [] σ}
    (hvf : Value f) (hva : Value a) :
    Value (Term.ap f a) ∨ ∃ t' : Term Sg [] τ, Step (Term.ap f a) t' := by
  rcases canonical_fn hvf with ⟨b, rfl⟩ | hnf
  · exact Or.inr ⟨_, .beta hva⟩
  · by_cases hd : DeltaRedex (Term.ap f a)
    · exact Or.inr hd.steps
    · exact Or.inl (.neutral (.ap hnf hva hd))

/-- A constructor of answers is an answer — unless it is built at the boolean type, in
    which case it steps to the literal `true` or `false`. -/
theorem value_or_step_ctor {τ : Ty} {i : Nat} {fs : Layout.FieldLayout}
    {h : τ.ctorFields? i = some fs} {args : Spine Sg [] fs} (hsv : SpineValue args) :
    Value (Term.ctor i fs h args) ∨
      ∃ t' : Term Sg [] τ, Step (Term.ctor i fs h args) t' := by
  by_cases hb : τ = Ty.bool
  · subst hb; exact Or.inr ⟨_, .ctorBool⟩
  · exact Or.inl (.ctor i fs h hb hsv)

/-- **Reading a field of an answer is never stuck.**  The type has one constructor, so an
    answer at it is that constructor applied to answers — and the field is one of them —
    or it is neutral, and then so is the read. -/
theorem value_or_step_proj {σ τ : Ty} {e : Term Sg [] σ} {i j : Nat}
    {hOne : σ.numCtors? = some 1} {h : σ.fieldTy? i j = some τ} (hv : Value e) :
    Value (Term.proj e i j hOne h) ∨
      ∃ t' : Term Sg [] τ, Step (Term.proj e i j hOne h) t' := by
  obtain ⟨fs', hc'⟩ := ctorFields?_of_fieldTy? h
  have hi : i = 0 := Ty.eq_zero_of_ctorFields?_of_numCtors?_one hOne hc'
  subst hi
  rcases canonical_oneCtor hOne hv with ⟨fs, hc, args, rfl, _⟩ | hn
  · have hfs : fs' = fs := by rw [hc'] at hc; exact Option.some.inj hc
    subst hfs
    exact Or.inr ⟨_, .projCtor (getElem?_of_fieldTy? hc' h)⟩
  · exact Or.inl (.neutral (.proj 0 j hOne h hn))

/-- The tag of an answer: a constructor answers with its number, a boolean with `0` or
    `1`, and there is nothing else at a type with a layout but a neutral term. -/
theorem value_or_step_tagOf {σ : Ty} {e : Term Sg [] σ} (h : σ.isTagged = true)
    (hv : Value e) :
    Value (Term.tagOf e h) ∨ ∃ t' : Term Sg [] (.prim .nat), Step (Term.tagOf e h) t' := by
  cases hv with
  | lam b => simp [Ty.isTagged, Ty.layout?] at h
  | lazyMk e => simp [Ty.isTagged, Ty.layout?] at h
  | lit l =>
      cases isTagged_prim h
      cases l with
      | bool b => exact Or.inr ⟨_, .tagOfBool⟩
  | ctor i fs hc hb hsv => exact Or.inr ⟨_, .tagOfCtor⟩
  | neutral hn => exact Or.inl (.neutral (.tagOf h hn))

/-- A dispatch on an answer: a constructor takes the branch for its tag, a boolean the
    branch for `0` or `1`, and a neutral scrutinee leaves the dispatch neutral. -/
theorem value_or_step_caseTag {σ τ : Ty} {tags : List Nat} {full : Bool}
    {e : Term Sg [] σ} {alts : Alts Sg [] τ tags full}
    (h : σ.caseOkAlts full tags = true) (hv : Value e) :
    Value (Term.caseTag e alts h) ∨
      ∃ t' : Term Sg [] τ, Step (Term.caseTag e alts h) t' := by
  cases hv with
  | lam b =>
      simp [Ty.caseOkAlts, Ty.caseOk, Ty.caseOkFull, Ty.numCtors?, Ty.layout?] at h
  | lazyMk e =>
      simp [Ty.caseOkAlts, Ty.caseOk, Ty.caseOkFull, Ty.numCtors?, Ty.layout?] at h
  | lit l =>
      cases caseOk_prim h
      cases l with
      | bool b => exact Or.inr ⟨_, .caseBool⟩
  | ctor i fs hc hb hsv => exact Or.inr ⟨_, .caseCtor⟩
  | neutral hn => exact Or.inl (.neutral (.caseTag h hn))

/-- A function of the runtime on its own is an answer unless the evaluator can run it
    where it stands — which, since `LeanInitPureExternLazy` is empty, it cannot. -/
theorem value_or_step_extern {σs : List Ty} {τ : Ty} (e : Externs σs τ) :
    Value (Term.extern (Sg := Sg) (Γ := []) e) ∨
      ∃ t' : Term Sg [] (Ty.arrows σs τ), Step (Term.extern e) t' := by
  by_cases hd : DeltaRedex (Sg := Sg) (Γ := []) (Term.extern e)
  · exact Or.inr hd.steps
  · exact Or.inl (.neutral (.extern e hd))

/-! ## Progress -/

mutual

/-- **Progress.**  A closed term is an answer or takes a step: the evaluator is never
    stuck on it.  Since `Value` includes the neutral terms, "answer" here means *the
    evaluator has nothing left to do*: it has reached a literal, a function, a delayed
    value, a constructor of answers, or a term waiting for something the language does
    not contain, such as a declaration of the signature. -/
theorem Term.progress : ∀ {τ : Ty} (t : Term Sg [] τ),
    Value t ∨ ∃ t' : Term Sg [] τ, Step t t'
  | _, .var v => nomatch v
  | _, .global r => Or.inl (.neutral (.global r))
  | _, .lit l => Or.inl (.lit l)
  | _, .lam b => Or.inl (.lam b)
  | _, .lazyMk e => Or.inl (.lazyMk e)
  | _, .extern e => value_or_step_extern e
  | _, .block b => by
      rcases b.progress with ⟨t, rfl⟩ | hn | ⟨b', hs⟩
      · exact Or.inr ⟨_, .blockRet⟩
      · exact Or.inl (.neutral (.block hn))
      · exact Or.inr ⟨_, .blockStep hs⟩
  | _, .ap f a => by
      rcases f.progress with hvf | ⟨f', hsf⟩
      · rcases a.progress with hva | ⟨a', hsa⟩
        · exact value_or_step_ap hvf hva
        · exact Or.inr ⟨_, .apArg hvf hsa⟩
      · exact Or.inr ⟨_, .apFun hsf⟩
  | _, .letE e _ => by
      rcases e.progress with hv | ⟨e', hs⟩
      · exact Or.inr ⟨_, .letV hv⟩
      · exact Or.inr ⟨_, .letStep hs⟩
  | _, .ite c _ _ => by
      rcases c.progress with hv | ⟨c', hs⟩
      · rcases canonical_prim hv with ⟨l, rfl⟩ | hn
        · cases l with
          | bool b =>
              cases b
              · exact Or.inr ⟨_, .iteFalse⟩
              · exact Or.inr ⟨_, .iteTrue⟩
        · exact Or.inl (.neutral (.ite hn))
      · exact Or.inr ⟨_, .iteCond hs⟩
  | _, .lazyForce e => by
      rcases e.progress with hv | ⟨e', hs⟩
      · rcases canonical_lazy hv with ⟨e0, rfl⟩ | hn
        · exact Or.inr ⟨_, .force⟩
        · exact Or.inl (.neutral (.lazyForce hn))
      · exact Or.inr ⟨_, .forceStep hs⟩
  | _, .ctor _ _ _ args => by
      rcases args.progress with hsv | ⟨args', hss⟩
      · exact value_or_step_ctor hsv
      · exact Or.inr ⟨_, .ctorStep hss⟩
  | _, .proj e _ _ _ _ => by
      rcases e.progress with hv | ⟨e', hs⟩
      · exact value_or_step_proj hv
      · exact Or.inr ⟨_, .projStep hs⟩
  | _, .tagOf e h => by
      rcases e.progress with hv | ⟨e', hs⟩
      · exact value_or_step_tagOf h hv
      · exact Or.inr ⟨_, .tagOfStep hs⟩
  | _, .caseTag e _ h => by
      rcases e.progress with hv | ⟨e', hs⟩
      · exact value_or_step_caseTag h hv
      · exact Or.inr ⟨_, .caseStep hs⟩

/-- **Progress for the tail of a block.**  A closed tail is one of three things: an
    answer of the block (`Tail.ret`, which `Step.blockRet` hands back), a tail waiting for
    something outside the language, or a tail that steps.  A `Tail.jmp` is none of them —
    in the empty label context there is nothing to jump to. -/
theorem Tail.progress : ∀ {τ : Ty} (b : Tail Sg [] [] τ),
    (∃ t : Term Sg [] τ, b = .ret t) ∨ TailNeutral b ∨ ∃ b' : Tail Sg [] [] τ, StepT b b'
  | _, .ret t => Or.inl ⟨t, rfl⟩
  | _, .jmp l _ => nomatch l
  | _, .letT e _ => by
      rcases e.progress with hv | ⟨e', hs⟩
      · exact Or.inr (Or.inr ⟨_, .letV hv⟩)
      · exact Or.inr (Or.inr ⟨_, .letStep hs⟩)
  | _, .iteT c _ _ => by
      rcases c.progress with hv | ⟨c', hs⟩
      · rcases canonical_prim hv with ⟨l, rfl⟩ | hn
        · cases l with
          | bool b =>
              cases b
              · exact Or.inr (Or.inr ⟨_, .iteFalse⟩)
              · exact Or.inr (Or.inr ⟨_, .iteTrue⟩)
        · exact Or.inr (Or.inl (.iteT hn))
      · exact Or.inr (Or.inr ⟨_, .iteCond hs⟩)
  | _, .caseT e _ h => by
      rcases e.progress with hv | ⟨e', hs⟩
      · cases hv with
        | lam b =>
            simp [Ty.caseOkAlts, Ty.caseOk, Ty.caseOkFull, Ty.numCtors?, Ty.layout?] at h
        | lazyMk e =>
            simp [Ty.caseOkAlts, Ty.caseOk, Ty.caseOkFull, Ty.numCtors?, Ty.layout?] at h
        | lit l =>
            cases caseOk_prim h
            cases l with
            | bool b => exact Or.inr (Or.inr ⟨_, .caseBool⟩)
        | ctor i fs hc hb hsv => exact Or.inr (Or.inr ⟨_, .caseCtor⟩)
        | neutral hn => exact Or.inr (Or.inl (.caseT h hn))
      · exact Or.inr (Or.inr ⟨_, .caseStep hs⟩)
  | _, .label (self := self) _ _ => by
      cases self
      · exact Or.inr (Or.inr ⟨_, .labelJoin⟩)
      · exact Or.inr (Or.inr ⟨_, .labelLoop⟩)

/-- **Progress for a spine**: either every term of it is an answer, or the leftmost one
    that is not takes a step. -/
theorem Spine.progress : ∀ {σs : List Ty} (args : Spine Sg [] σs),
    SpineValue args ∨ ∃ args' : Spine Sg [] σs, SpineStep args args'
  | _, .nil => Or.inl .nil
  | _, .cons t rest => by
      rcases t.progress with hv | ⟨t', hs⟩
      · rcases rest.progress with hsv | ⟨rest', hss⟩
        · exact Or.inl (.cons hv hsv)
        · exact Or.inr ⟨_, .tail hv hss⟩
      · exact Or.inr ⟨_, .head hs⟩

end

/-! ## The projection that used to be stuck

`Option Nat` has the layout `[[], [.nat]]`: constructor `0` (`none`) carries nothing and
constructor `1` (`some`) carries a `Nat`.  Before `Term.proj` carried `hOne`, the term
`(none).1` — build `none`, read field `0` of constructor `1` out of it — was closed and
well-typed, and it was neither an answer nor a redex.  The theorems that proved so are
kept below, **commented out**: they no longer elaborate, because the term they are about
is no longer a term.  `Option Nat` has two constructors, so `hOne` cannot be discharged
at it, and that is exactly the repair (`PROJ_SOUNDNESS.md`, option C). -/

section Stuck

/-- The empty signature. -/
def sigNone : Sig := ⟨[], rfl⟩

/-- `none`, at `Option Nat`. -/
def noneTerm : Term sigNone [] (Ty.option .nat) :=
  .ctor 0 [] rfl .nil

/-- **`Option Nat` has two constructors**, so `Term.proj` may not read a field of one:
    the `hOne` premise is unprovable at it. -/
theorem numCtors_option_nat : (Ty.option .nat).numCtors? = some 2 := rfl

/-- A **record** has one constructor, and a field of one *is* readable. -/
theorem numCtors_prod_nat : (Ty.prod .nat .nat).numCtors? = some 1 := rfl

/-- The pair `(1, 2)`. -/
def pairTerm : Term sigNone [] (Ty.prod .nat .nat) :=
  .ctor 0 [.nat, .nat] rfl (.cons (.lit (.nat 1)) (.cons (.lit (.nat 2)) .nil))

/-- Reading the first component of a pair: the projection the repair keeps. -/
def fstOfPair : Term sigNone [] Ty.nat :=
  .proj pairTerm 0 0 rfl rfl

/-- …and it runs: a field read of a one-constructor type is never stuck. -/
example : ∃ t' : Term sigNone [] Ty.nat,
    Step (.proj (σ := Ty.prod .nat .nat) pairTerm 0 0 rfl rfl) t' :=
  ⟨_, .projCtor (fs := [Ty.nat, Ty.nat]) (j := 0) rfl⟩

-- The term that used to be stuck, and the proofs about it.  `badProj` does not
-- elaborate any more — `Term.proj` now asks for `(Ty.option .nat).numCtors? = some 1`,
-- and `numCtors_option_nat` says it is `some 2` — so the whole section is kept as a
-- record of what was repaired rather than as live code.
--
-- /-- `(none).1` — field `0` of constructor `1` (`some`) of a value built with
--     constructor `0` (`none`). -/
-- def badProj : Term sigNone [] Ty.nat :=
--   .proj noneTerm 1 0 rfl
--
-- theorem badProj_not_value : ¬ Value badProj :=
--   fun hv => not_neutral_ctor (neutral_of_value_proj hv)
--
-- theorem badProj_not_step : ¬ ∃ t' : Term sigNone [] Ty.nat, Step badProj t' := by
--   rintro ⟨t', hs⟩
--   cases hs with
--   | projStep hsi => cases hsi with
--     | ctorStep hss => cases hss
--
-- theorem badProj_stuck :
--     ¬ (Value badProj ∨ ∃ t' : Term sigNone [] Ty.nat, Step badProj t') := by
--   rintro (hv | hs)
--   · exact badProj_not_value hv
--   · exact badProj_not_step hs

/-- A constructor is never *neutral*: it is built here, it waits for nothing. -/
theorem not_neutral_ctor {Γ : Ctx} {τ : Ty} {i : Nat} {fs : Layout.FieldLayout}
    {hc : τ.ctorFields? i = some fs} {args : Spine Sg Γ fs} :
    ¬ Neutral (Term.ctor i fs hc args) := by
  intro h; cases h

/-- An answer that reads a field is neutral in what it reads it out of: there is no
    other way for a `Term.proj` to be an answer. -/
theorem neutral_of_value_proj {Γ : Ctx} {σ τ : Ty} {e : Term Sg Γ σ}
    {i j : Nat} {hOne : σ.numCtors? = some 1} {h : σ.fieldTy? i j = some τ}
    (hv : Value (Term.proj e i j hOne h)) : Neutral e := by
  cases hv with
  | neutral hn => cases hn with
    | proj _ _ _ _ hin => exact hin

end Stuck

/-! ## Being intrinsically typed is what keeps an application from going wrong

The catalogue indexes each entry by the types of its arguments and of its result, and
`Term.extern` is typed by the entry, so the type of a function of the runtime is not a
matter of convention: `lean_int_add` **is** a term of type `int ⇒ int ⇒ int`, and
`Term.ap` will take nothing but an `int` for its argument. -/

/-- `lean_int_add` is a curried function of two integers, and that is its type as a
    term. -/
def externTy_int_add : Term sigNone [] (Ty.int ⇒ Ty.int ⇒ Ty.int) :=
  .extern (.prim2 .lean_int_add)

/-- Applied to two integer literals, it is a redex, so it runs. -/
example :
    Step (Sg := sigNone) (Γ := [])
      (.ap (.ap (.extern (.prim2 .lean_int_add)) (.lit (.int 2))) (.lit (.int 3)))
      (.lit (.int 5)) :=
  .deltaPrim2 .lean_int_add (.int 2) (.int 3)

-- Applied to a **float**, it is not a term: the line below does not elaborate —
-- "application type mismatch: `LeanPrimLit.float 1.0` has type `LeanPrimLit
-- LeanPrimTy.float` but is expected to have type `LeanPrimLit LeanPrimTy.int`".  There
-- is nothing for the evaluator to get stuck on, because the ill-typed application
-- cannot be written down.
--
-- example : Term sigNone [] Ty.int :=
--   .ap (.ap (.extern (.prim2 .lean_int_add)) (.lit (.float 1.0))) (.lit (.int 3))

end LakeJs.Expr

end
