module

public import LakeJs.Descends
public import LakeJs.DescentVC
public import LakeJs.Examples.Structural
public import LakeJs.Examples.WellFounded
public import LakeJs.Examples.Ackermann

@[expose] public section

set_option autoImplicit false

/-!
# The verification condition, discharged on the worked examples

`LakeJs.Descends` states, once and generically, what it takes for a recursion to never
reach its `stuck` branch: `Term.Descends`, *the body consults its self-reference only at
arguments of strictly smaller measure*.  This file discharges that condition on the worked
examples — a structural recursion on a number (`sumTo`), a structural recursion over data
(`sumList`), a recursion whose body is a block of join points, a lexicographic one
(Ackermann), a merged mutual clique (`testEven` / `testOdd`) and a well-founded one
(`Nat.gcd`) — reads off the consequences in each case,
and shows the condition is not vacuous by **refuting** it twice: for `Tco07.boom`, whose
erased proof made a non-descending branch reachable, and for the recursion that calls
itself at the same argument.

Four of them go through the rule calculus of `LakeJs.DescentVC`
(`gcdBody_descends_by_rules`, `ackBody_descends_by_rules`, `sumListBody_descends_by_rules`
and `joinCountBody_descends`), where the derivation is structural — one rule per node,
including the rules for dispatch and for blocks — and the only goals left over are the
arithmetic ones.

What is worth noticing is the shape of the last theorem of each section.
`sumToTerm_implements` and `ackTerm_implements`, in the files these terms come from, are
proved by an *induction*: the hypothesis of `Term.fix_implements` is an induction step,
and the proof supplies the descent of the measure at each call while simultaneously
rewriting with the Lean function's equations.  Here the two halves are separated:

1. `…_descends` — a property of the term alone, with the Lean function nowhere in it;
2. `…_body_equation` — the body, run with the Lean function as its self-reference, *is*
   the Lean function: a one-step check against `f`'s own equation lemmas, with no
   induction and no measure in it;
3. `Term.fix_implements_of_equation` — the generic theorem, which combines them.

That is the decomposition translation validation (step 7 of
`TERM_RANK_FLAKINESS_AND_ALTERNATIVES.md` §8) needs, because both halves are mechanical:
(1) is an arithmetic obligation per self call, and (2) is `simp [f]`.
-/

namespace LakeJs.Expr.Examples

open LakeJs
open LakeJs.Ty
open LakeJs.Expr.Ops

variable {Sg : Sig}

/-- Every binary arithmetic or comparison operation of `LakeJs.Expr.Ops` is an extern
    applied to two subterms, so this is the rule for all of them at once. -/
theorem natCmpIndep {Ρ : RCtx} {ps : List Ty} {τ : Ty} {δ : GEnv Sg.decls} {ρ : REnv Ρ}
    {S : Env ps → Prop} {Γ' : Ctx} {Φ : Env Γ' → (Env ps → τ.den) → Prop}
    {σ₁ σ₂ σ : Ty} {e : Externs [σ₁, σ₂] σ}
    (a : Term Sg Γ' (⟨ps, τ⟩ :: Ρ) σ₁) (b : Term Sg Γ' (⟨ps, τ⟩ :: Ρ) σ₂)
    (ha : Term.SelfIndepOn δ ρ S Φ a := by
      first | exact Term.selfIndepOn_var _ | exact Term.selfIndepOn_lit _)
    (hb : Term.SelfIndepOn δ ρ S Φ b := by
      first | exact Term.selfIndepOn_var _ | exact Term.selfIndepOn_lit _) :
    Term.SelfIndepOn δ ρ S Φ (.ap (.ap (.extern e) a) b) :=
  Term.selfIndepOn_ap (Term.selfIndepOn_ap (Term.selfIndepOn_extern _) ha) hb

/-! ## 1. A structural recursion: `sumTo` -/

/-- **The verification condition for `sumTo`.**  Its one self call is at `n - 1` under the
    test `n = 0`, so it descends on the measure `n`. -/
theorem sumToBody_descends (δ : GEnv Sg.decls) :
    Term.Descends (Sg := Sg) (Γ := []) (Ρ := []) (ps := [Ty.nat]) (τ := Ty.nat)
      (Term.measure1 sumToMeasure) sumToBody δ .nil .nil := by
  refine Term.descends_of_measure1 (Γ := []) (ps := [Ty.nat]) sumToMeasure sumToBody
    δ .nil .nil
    (fun as => as.get .head) (fun as => ?_) (fun as g₁ g₂ hg => ?_)
  · cases as with
    | cons _ _ => rfl
  · match as with
    | .cons n .nil =>
      cases (n : Nat) with
      | zero => rfl
      | succ k =>
        show (k + 1) + g₁ (.cons (k : Nat) .nil) = (k + 1) + g₂ (.cons (k : Nat) .nil)
        rw [hg (.cons (k : Nat) .nil) (by exact Nat.lt_succ_self k)]

/-- **The `stuck` branch of `sumTo` is unreachable**: replacing it by any other term —
    here, one answering `99` instead of `0` — changes no value the recursion computes. -/
theorem sumToTerm_stuck_irrelevant (δ : GEnv Sg.decls) (args : Env [Ty.nat]) :
    Term.fixFun (Sg := Sg) (Γ := []) (ps := [Ty.nat])
        (Term.measure1 sumToMeasure) sumToBody (Term.natL 0) δ .nil .nil args
      = Term.fixFun (Sg := Sg) (Γ := []) (ps := [Ty.nat])
        (Term.measure1 sumToMeasure) sumToBody (Term.natL 99) δ .nil .nil args :=
  Term.fix_stuck_irrelevant _ _ _ _ δ .nil .nil (sumToBody_descends δ) args

/-- **The unrolling equation of `sumTo`**, with no guard and no `stuck`: the recursion is
    its body run with itself. -/
theorem sumToTerm_unfold (δ : GEnv Sg.decls) (args : Env [Ty.nat]) :
    Term.fixFun (Sg := Sg) (Γ := []) (ps := [Ty.nat])
        (Term.measure1 sumToMeasure) sumToBody (Term.natL 0) δ .nil .nil args
      = sumToBody.eval δ (args.append .nil)
          (.cons (Term.fixFun (Sg := Sg) (Γ := []) (ps := [Ty.nat])
            (Term.measure1 sumToMeasure) sumToBody (Term.natL 0) δ .nil .nil) .nil) :=
  Term.fixFun_unfold_of_descends _ _ _ δ .nil .nil (sumToBody_descends δ) args

/-- **The body is `sumTo`'s equation.**  No induction and no measure: the body, run with
    the Lean function itself as the self-reference, answers what the Lean function
    answers. -/
theorem sumToBody_equation (δ : GEnv Sg.decls) (as : Env [Ty.nat]) :
    sumToBody.eval (Sg := Sg) δ (as.append .nil) (.cons sumToFun .nil) = sumToFun as := by
  match as with
  | .cons n .nil =>
    cases (n : Nat) with
    | zero => rfl
    | succ k =>
      show (k + 1) + sumToFun (.cons (k : Nat) .nil) = sumTo (k + 1)
      show (k + 1) + sumTo k = sumTo (k + 1)
      simp [sumTo]

/-- **Faithfulness, assembled from the two halves** rather than proved by induction: the
    term is `sumTo`.  Compare `sumToTerm_implements`, which does it in one induction. -/
theorem sumToTerm_implements_of_equation (δ : GEnv Sg.decls) :
    (sumToTerm (Sg := Sg)).Implements δ sumToFun :=
  Term.fix_implements_of_equation (Sg := Sg) (ps := [Ty.nat]) (τ := Ty.nat) (k := 1)
    (Term.measure1 sumToMeasure) sumToBody (Term.natL 0) δ sumToFun
    (sumToBody_descends δ) (sumToBody_equation δ)

/-! ## 2. A lexicographic recursion: Ackermann -/

/-- The measure of the Ackermann term, as a function of the arguments. -/
theorem ackTerm_measureVal (δ : GEnv Sg.decls) (as : Env [Ty.nat, Ty.nat]) :
    Term.measureVal (Sg := Sg) (Γ := []) (ps := [Ty.nat, Ty.nat]) (k := 2)
      (.cons (♯0) (.cons (♯1) .nil)) δ .nil .nil as
      = ackMeasure as := by
  match as with
  | .cons _ (.cons _ .nil) => rfl

/-- **The verification condition for Ackermann.**  Its three self calls descend on
    `[m, n]`: `(m, n - 1)` keeps the head and descends in the tail, and the two calls at
    `m - 1` descend in the head whatever their second argument is — including the
    *nested* one, whose second argument is itself a self call. -/
theorem ackBody_descends (δ : GEnv Sg.decls) :
    Term.Descends (Sg := Sg) (Γ := []) (Ρ := []) (ps := [Ty.nat, Ty.nat]) (τ := Ty.nat)
      (k := 2) (.cons (♯0) (.cons (♯1) .nil)) ackBody δ .nil .nil := by
  intro as g₁ g₂ hg
  simp only [ackTerm_measureVal δ] at hg
  match as with
  | .cons m (.cons n .nil) =>
    cases (m : Nat) with
    | zero => rfl
    | succ k =>
      cases (n : Nat) with
      | zero =>
        have hdrop : Lex.NatVec.Lt (ackMeasure (.cons (k : Nat) (.cons (1 : Nat) .nil)))
            (ackMeasure (.cons (k + 1 : Nat) (.cons (0 : Nat) .nil))) :=
          Lex.NatVec.Lt.head (Nat.lt_succ_self k)
        show g₁ (.cons (k : Nat) (.cons (1 : Nat) .nil))
            = g₂ (.cons (k : Nat) (.cons (1 : Nat) .nil))
        exact hg (.cons (k : Nat) (.cons (1 : Nat) .nil)) hdrop
      | succ i =>
        have htail : Lex.NatVec.Lt
            (ackMeasure (.cons (k + 1 : Nat) (.cons (i : Nat) .nil)))
            (ackMeasure (.cons (k + 1 : Nat) (.cons (i + 1 : Nat) .nil))) :=
          Lex.NatVec.Lt.tail (Lex.NatVec.Lt.head (Nat.lt_succ_self i))
        have hinner : g₁ (.cons (k + 1 : Nat) (.cons (i : Nat) .nil))
            = g₂ (.cons (k + 1 : Nat) (.cons (i : Nat) .nil)) :=
          hg (.cons (k + 1 : Nat) (.cons (i : Nat) .nil)) htail
        show g₁ (.cons (k : Nat)
              (.cons (g₁ (.cons (k + 1 : Nat) (.cons (i : Nat) .nil))) .nil))
            = g₂ (.cons (k : Nat)
              (.cons (g₂ (.cons (k + 1 : Nat) (.cons (i : Nat) .nil))) .nil))
        rw [hinner]
        exact hg _ (Lex.NatVec.Lt.head (Nat.lt_succ_self k))

/-- **The `stuck` branch of Ackermann is unreachable.** -/
theorem ackTerm_stuck_irrelevant (δ : GEnv Sg.decls) (args : Env [Ty.nat, Ty.nat]) :
    Term.fixFun (Sg := Sg) (Γ := []) (ps := [Ty.nat, Ty.nat]) (k := 2)
        (.cons (♯0) (.cons (♯1) .nil)) ackBody (Term.natL 0) δ .nil .nil args
      = Term.fixFun (Sg := Sg) (Γ := []) (ps := [Ty.nat, Ty.nat]) (k := 2)
        (.cons (♯0) (.cons (♯1) .nil)) ackBody (Term.natL 7) δ .nil .nil args :=
  Term.fix_stuck_irrelevant _ _ _ _ δ .nil .nil (ackBody_descends δ) args

/-- **The body is `ack`'s equation**: run with `ack` as its self-reference, the body
    answers `ack`.  This is the three equation lemmas of `ack` and nothing else. -/
theorem ackBody_equation (δ : GEnv Sg.decls) (as : Env [Ty.nat, Ty.nat]) :
    ackBody.eval (Sg := Sg) δ (as.append .nil) (.cons ackFun .nil) = ackFun as := by
  match as with
  | .cons m (.cons n .nil) =>
    cases (m : Nat) with
    | zero =>
      show (show Nat from n) + 1 = ack 0 n
      rw [ack_zero]
    | succ k =>
      cases (n : Nat) with
      | zero =>
        show ackFun (.cons (k : Nat) (.cons (1 : Nat) .nil)) = ack (k + 1) 0
        show ack k 1 = ack (k + 1) 0
        rw [ack_succ_zero]
      | succ i =>
        show ackFun (.cons (k : Nat)
              (.cons (ackFun (.cons (k + 1 : Nat) (.cons (i : Nat) .nil))) .nil))
            = ack (k + 1) (i + 1)
        show ack k (ack (k + 1) i) = ack (k + 1) (i + 1)
        rw [ack_succ_succ]

/-- **Faithfulness of Ackermann, assembled from the two halves.**  Compare
    `ackTerm_implements`, whose single induction interleaves them. -/
theorem ackTerm_implements_of_equation (δ : GEnv Sg.decls) :
    (ackTerm (Sg := Sg)).Implements δ ackFun :=
  Term.fix_implements_of_equation (Sg := Sg) (ps := [Ty.nat, Ty.nat]) (τ := Ty.nat)
    (k := 2) (.cons (♯0) (.cons (♯1) .nil)) ackBody (Term.natL 0) δ ackFun
    (ackBody_descends δ) (ackBody_equation δ)

/-! ### Ackermann by the rule calculus, including the nested call

The interesting case for a *structural* derivation is the nested call
`ack m (ack (m + 1) n)`: the argument of one self call is another self call.  The calculus
handles it without any analysis — the spine rule checks the inner call like any other
subterm, and the outer call's obligation is about the measure of its arguments, whose
first component does not mention the inner call at all. -/

/-- Ackermann's verification condition, assembled from the rules.  Three self calls, three
    arithmetic obligations, and nothing else. -/
theorem ackBody_descends_by_rules (δ : GEnv Sg.decls) :
    Term.Descends (Sg := Sg) (Γ := []) (Ρ := []) (ps := [Ty.nat, Ty.nat]) (τ := Ty.nat)
      (k := 2) (.cons (♯0) (.cons (♯1) .nil)) ackBody δ .nil .nil := by
  refine Term.descends_of_selfIndepOn (Γ := []) (ps := [Ty.nat, Ty.nat]) (τ := Ty.nat)
    (k := 2) (.cons (♯0) (.cons (♯1) .nil)) ackBody δ .nil .nil (fun as => ?_)
  refine Term.selfIndepOn_ite (natCmpIndep _ _) (natCmpIndep _ _) ?_
  refine Term.selfIndepOn_ite (natCmpIndep _ _) ?_ ?_
  · -- `self (m - 1) 1`, under `m ≠ 0` and `n = 0`
    refine Term.selfIndepOn_selfCall
      (Spine.selfIndepOn_cons (natCmpIndep _ _)
        (Spine.selfIndepOn_cons (Term.selfIndepOn_lit _) Spine.selfIndepOn_nil)) ?_
    rintro γ' g ⟨⟨rfl, hc1⟩, _⟩
    match as with
    | .cons m (.cons n .nil) =>
      have hm : (show Nat from m) ≠ 0 := of_decide_eq_false hc1
      refine Lex.NatVec.Lt.head ?_
      show (show Nat from m) - 1 < (show Nat from m)
      omega
  · -- `self (m - 1) (self m (n - 1))`, under `m ≠ 0` and `n ≠ 0`
    refine Term.selfIndepOn_selfCall
      (Spine.selfIndepOn_cons (natCmpIndep _ _)
        (Spine.selfIndepOn_cons ?_ Spine.selfIndepOn_nil)) ?_
    · -- the *inner* call, checked like any other subterm
      refine Term.selfIndepOn_selfCall
        (Spine.selfIndepOn_cons (Term.selfIndepOn_var _)
          (Spine.selfIndepOn_cons (natCmpIndep _ _) Spine.selfIndepOn_nil)) ?_
      rintro γ' g ⟨⟨rfl, _⟩, hc2⟩
      match as with
      | .cons m (.cons n .nil) =>
        have hn : (show Nat from n) ≠ 0 := of_decide_eq_false hc2
        refine Lex.NatVec.Lt.tail (Lex.NatVec.Lt.head ?_)
        show (show Nat from n) - 1 < (show Nat from n)
        omega
    · rintro γ' g ⟨⟨rfl, hc1⟩, _⟩
      match as with
      | .cons m (.cons n .nil) =>
        have hm : (show Nat from m) ≠ 0 := of_decide_eq_false hc1
        -- the second argument is the inner self call; the obligation never looks at it
        refine Lex.NatVec.Lt.head ?_
        show (show Nat from m) - 1 < (show Nat from m)
        omega

/-! ## 2b. A structural recursion over data: `sumList`

The measure of a structural recursion is `Term.structSize`, the size of the recursion
subject's runtime tree, and the obligation is that a field of a constructor is smaller
than the value it is a field of.  That is `Data.size_lt_of_mem`, and it is the only thing
this verification condition needs — no `+ 1`, and nothing about how many iterations the
recursion takes. -/

/-- **The verification condition for `sumList`.**  The call is on the *tail* bound by the
    `x :: xs` branch, whose runtime tree is a strict sub-tree of the scrutinee's. -/
theorem sumListBody_descends (δ : GEnv Sg.decls) :
    Term.Descends (Sg := Sg) (Γ := []) (Ρ := []) (ps := [natList]) (τ := Ty.nat)
      (Term.structMeasure (♯0)) sumListBody δ .nil .nil := by
  refine Term.descends_of_measure1 (Γ := []) (ps := [natList]) (.structSize (♯0))
    sumListBody δ .nil .nil
    (fun as => Data.size (natList.toData (as.get .head))) (fun as => ?_)
    (fun as g₁ g₂ hg => ?_)
  · match as with
    | .cons _ .nil => rfl
  · match as with
    | .cons xs .nil =>
      match (xs : List Nat) with
      | [] => rfl
      | x :: rest =>
        have hsize : Data.size (natList.toData (show List Nat from rest))
            < Data.size (natList.toData (show List Nat from x :: rest)) := by
          show Data.size (.seq (rest.map Ty.nat.toData))
              < Data.size (.seq ((x :: rest).map Ty.nat.toData))
          simp only [List.map_cons, Data.size_seq, Data.sizeList]
          have : Data.size (Ty.nat.toData x) = 1 := rfl
          omega
        have hr : (show List Nat from
            natList.ofData (Data.seq (List.map Ty.nat.toData rest))) = rest :=
          Ty.ofData_toData natList (by rfl) rest
        show (show Nat from Ty.nat.ofData (Ty.nat.toData x))
              + g₁ (.cons (show List Nat from
                  natList.ofData (Data.seq (List.map Ty.nat.toData rest))) .nil)
            = (show Nat from Ty.nat.ofData (Ty.nat.toData x))
              + g₂ (.cons (show List Nat from
                  natList.ofData (Data.seq (List.map Ty.nat.toData rest))) .nil)
        rw [hr, hg (.cons (show List Nat from rest) .nil) hsize]

/-- The Lean function `sumList`, as a function of an argument environment. -/
def sumListFun (as : Env [natList]) : Ty.nat.den := sumList (as.get .head)

/-- **The body is `sumList`'s equation.** -/
theorem sumListBody_equation (δ : GEnv Sg.decls) (as : Env [natList]) :
    sumListBody.eval (Sg := Sg) δ (as.append .nil) (.cons sumListFun .nil)
      = sumListFun as := by
  match as with
  | .cons xs .nil =>
    match (xs : List Nat) with
    | [] => rfl
    | x :: rest =>
      have hr : (show List Nat from
          natList.ofData (Data.seq (List.map Ty.nat.toData rest))) = rest :=
        Ty.ofData_toData natList (by rfl) rest
      show (show Nat from Ty.nat.ofData (Ty.nat.toData x))
            + sumListFun (.cons (show List Nat from
                natList.ofData (Data.seq (List.map Ty.nat.toData rest))) .nil)
          = sumList (x :: rest)
      rw [hr]
      show x + sumList rest = sumList (x :: rest)
      simp [sumList]

/-- **Faithfulness of `sumList`**: the structural recursion over data computes the Lean
    function, assembled from its verification condition and its equation. -/
theorem sumListTerm_implements (δ : GEnv Sg.decls) :
    (sumListTerm (Sg := Sg)).Implements δ sumListFun :=
  Term.fix_implements_of_equation (Sg := Sg) (ps := [natList]) (τ := Ty.nat) (k := 1)
    (Term.structMeasure (♯0)) sumListBody (Term.natL 0) δ sumListFun
    (sumListBody_descends δ) (sumListBody_equation δ)

/-! ### `sumList` by the rule calculus, through the dispatch rules

The same condition again, this time assembled from `LakeJs.DescentVC`'s rules — including
the ones for `caseTag` and `Alts`, whose path condition carries the matched tag and the
fields the branch bound.  That is what turns "the call is on the tail" into an arithmetic
fact about the scrutinee. -/

/-- `sumList`'s verification condition, derived by the rules. -/
theorem sumListBody_descends_by_rules (δ : GEnv Sg.decls) :
    Term.Descends (Sg := Sg) (Γ := []) (Ρ := []) (ps := [natList]) (τ := Ty.nat)
      (Term.structMeasure (♯0)) sumListBody δ .nil .nil := by
  refine Term.descends_of_selfIndepOn (Γ := []) (ps := [natList]) (τ := Ty.nat) (k := 1)
    (Term.structMeasure (♯0)) sumListBody δ .nil .nil (fun as => ?_)
  refine Term.selfIndepOn_caseTag (Term.selfIndepOn_var _) ?_
  refine Alts.selfIndepOn_cons (Term.selfIndepOn_lit _) ?_
  refine Alts.selfIndepOn_cons ?_ Alts.selfIndepOn_nilFull
  refine Term.selfIndepOn_ap
    (Term.selfIndepOn_ap (Term.selfIndepOn_extern _) (Term.selfIndepOn_var _)) ?_
  refine Term.selfIndepOn_selfCall
    (Spine.selfIndepOn_cons (Term.selfIndepOn_var _) Spine.selfIndepOn_nil) ?_
  rintro γ'' g ⟨γ', fs, ⟨rfl, htag, rfl⟩, rfl⟩
  match as with
  | .cons xs .nil =>
    match hxs : (xs : List Nat) with
    | [] =>
      -- the `[]` scrutinee has tag `0`, so this branch is not the one that matched
      have h10 : (1 : Nat) = 0 := htag
      exact absurd h10 (by decide)
    | x :: rest =>
      have hr : (show List Nat from
          natList.ofData (Data.seq (List.map Ty.nat.toData rest))) = rest :=
        Ty.ofData_toData natList (by rfl) rest
      show Lex.NatVec.Lt
        (Lex.NatVec.cons
          (Data.size (natList.toData (show List Nat from
            natList.ofData (Data.seq (List.map Ty.nat.toData rest))))) .nil)
        (Lex.NatVec.cons (Data.size (natList.toData (show List Nat from x :: rest))) .nil)
      rw [hr]
      refine (Lex.NatVec.lt_one_iff _ _).mpr ?_
      show Data.size (.seq (rest.map Ty.nat.toData))
          < Data.size (.seq ((x :: rest).map Ty.nat.toData))
      simp only [List.map_cons, Data.size_seq, Data.sizeList]
      have hx1 : Data.size (Ty.nat.toData x) = 1 := rfl
      omega

/-! ## 2c. A recursion whose body is a block of join points

The front end emits join points wherever two paths share a tail, so the calculus has to
reach inside `Term.block`.  This is the smallest recursion of that shape: both arms of the
test jump to the same join point, and one of them jumps with the value of a self call. -/

/-- `fun n => block { join k(x) { x };
                      if n = 0 then k(0) else k(self (n - 1)) }`. -/
def joinCountBody : Term Sg [Ty.nat] [⟨[Ty.nat], Ty.nat⟩] Ty.nat :=
  .block
    (.join [Ty.nat] (.ret (♯0))
      (.iteT (natEq (♯0) (Term.natL 0))
        (.jmp .head (.cons (Term.natL 0) .nil))
        (.jmp .head
          (.cons (.selfCall .head (.cons (natSub (♯0) (Term.natL 1)) .nil)) .nil))))

/-- The recursion, measured by its argument. -/
def joinCountTerm : Term Sg [] [] (.nat ⇒ .nat) :=
  .fix [Ty.nat] 1 (Term.measure1 (♯0)) joinCountBody (Term.natL 7)

example : Term.runNat1 (joinCountTerm (Sg := ⟨[], by decide⟩)) 0 = 0 := rfl
example : Term.runNat1 (joinCountTerm (Sg := ⟨[], by decide⟩)) 5 = 0 := rfl

/-- **Its verification condition, through the block rules.**  `block`, `join`, `iteT` and
    `jmp` are all discharged structurally; the one goal left is `n - 1 < n` under
    `n ≠ 0`. -/
theorem joinCountBody_descends (δ : GEnv Sg.decls) :
    Term.Descends (Sg := Sg) (Γ := []) (Ρ := []) (ps := [Ty.nat]) (τ := Ty.nat) (k := 1)
      (Term.measure1 (♯0)) joinCountBody δ .nil .nil := by
  refine Term.descends_of_selfIndepOn (Γ := []) (ps := [Ty.nat]) (τ := Ty.nat) (k := 1)
    (Term.measure1 (♯0)) joinCountBody δ .nil .nil (fun as => ?_)
  refine Term.selfIndepOn_block ?_
  refine Tail.selfIndepOn_join (Tail.selfIndepOn_ret (Term.selfIndepOn_var _)) ?_
  refine Tail.selfIndepOn_iteT (natCmpIndep _ _)
    (Tail.selfIndepOn_jmp _
      (Spine.selfIndepOn_cons (Term.selfIndepOn_lit _) Spine.selfIndepOn_nil)) ?_
  refine Tail.selfIndepOn_jmp _ (Spine.selfIndepOn_cons ?_ Spine.selfIndepOn_nil)
  refine Term.selfIndepOn_selfCall
    (Spine.selfIndepOn_cons (natCmpIndep _ _) Spine.selfIndepOn_nil) ?_
  rintro γ' g ⟨rfl, hc⟩
  match as with
  | .cons n .nil =>
    have h0 : decide ((show Nat from n) = 0) = false := hc
    have hn : (show Nat from n) ≠ 0 := of_decide_eq_false h0
    show Lex.NatVec.Lt (Lex.NatVec.cons ((show Nat from n) - 1) .nil)
      (Lex.NatVec.cons (show Nat from n) .nil)
    exact (Lex.NatVec.lt_one_iff _ _).mpr (by omega)

/-- The Lean function it computes: the constant `0`. -/
def joinCountFun (_ : Env [Ty.nat]) : Ty.nat.den := (0 : Nat)

/-- The body is that function's equation. -/
theorem joinCountBody_equation (δ : GEnv Sg.decls) (as : Env [Ty.nat]) :
    joinCountBody.eval (Sg := Sg) δ (as.append .nil) (.cons joinCountFun .nil)
      = joinCountFun as := by
  match as with
  | .cons n .nil =>
    cases (n : Nat) with
    | zero => rfl
    | succ _ => rfl

/-- **Faithfulness**, from the two halves — with a `stuck` branch of `7` that is never
    reached. -/
theorem joinCountTerm_implements (δ : GEnv Sg.decls) :
    (joinCountTerm (Sg := Sg)).Implements δ joinCountFun :=
  Term.fix_implements_of_equation (Sg := Sg) (ps := [Ty.nat]) (τ := Ty.nat) (k := 1)
    (Term.measure1 (♯0)) joinCountBody (Term.natL 7) δ joinCountFun
    (joinCountBody_descends δ) (joinCountBody_equation δ)

/-! ## 3. A merged mutual clique: `testEven` / `testOdd` -/

/-- **The verification condition for the merged parity clique.**  The one self call flips
    the member tag and descends on the shared measure `n`, which is what makes a clique
    representable as a single recursion. -/
theorem parityBody_descends (δ : GEnv Sg.decls) :
    Term.Descends (Sg := Sg) (Γ := []) (Ρ := []) (ps := [Ty.nat, Ty.nat]) (τ := Ty.bool)
      (Term.measure1 (♯1)) parityBody δ .nil .nil := by
  refine Term.descends_of_measure1 (Γ := []) (ps := [Ty.nat, Ty.nat]) (♯1) parityBody
    δ .nil .nil (fun as => as.get (.tail .head)) (fun as => ?_) (fun as g₁ g₂ hg => ?_)
  · match as with
    | .cons _ (.cons _ .nil) => rfl
  · match as with
    | .cons tag (.cons n .nil) =>
      cases (n : Nat) with
      | zero => rfl
      | succ k =>
        show g₁ (.cons (1 - tag : Nat) (.cons (k : Nat) .nil))
            = g₂ (.cons (1 - tag : Nat) (.cons (k : Nat) .nil))
        exact hg (.cons (1 - tag : Nat) (.cons (k : Nat) .nil)) (Nat.lt_succ_self k)

/-- **The `stuck` branch of the clique is unreachable**, at either member. -/
theorem parityMerged_stuck_irrelevant (δ : GEnv Sg.decls) (args : Env [Ty.nat, Ty.nat]) :
    Term.fixFun (Sg := Sg) (Γ := []) (ps := [Ty.nat, Ty.nat])
        (Term.measure1 (♯1)) parityBody (Term.boolL false) δ .nil .nil args
      = Term.fixFun (Sg := Sg) (Γ := []) (ps := [Ty.nat, Ty.nat])
        (Term.measure1 (♯1)) parityBody (Term.boolL true) δ .nil .nil args :=
  Term.fix_stuck_irrelevant _ _ _ _ δ .nil .nil (parityBody_descends δ) args

/-! ## 4. A well-founded recursion that is not structural: `Nat.gcd` -/

/-- **The verification condition for `gcd`.**  The call is at `(y % x, x)` under the test
    `x = 0`, and `y % x < x` there — the obligation Lean's own `decreasing_by` discharges,
    and the only thing this proof has to know. -/
theorem gcdBody_descends (δ : GEnv Sg.decls) :
    Term.Descends (Sg := Sg) (Γ := []) (Ρ := []) (ps := [Ty.nat, Ty.nat]) (τ := Ty.nat)
      (Term.measure1 (♯0)) gcdBody δ .nil .nil := by
  refine Term.descends_of_measure1 (Γ := []) (ps := [Ty.nat, Ty.nat]) (♯0) gcdBody
    δ .nil .nil (fun as => as.get .head) (fun as => ?_) (fun as g₁ g₂ hg => ?_)
  · match as with
    | .cons _ (.cons _ .nil) => rfl
  · match as with
    | .cons x (.cons y .nil) =>
      cases (x : Nat) with
      | zero => rfl
      | succ j =>
        show g₁ (.cons ((y : Nat) % (j + 1)) (.cons (j + 1 : Nat) .nil))
            = g₂ (.cons ((y : Nat) % (j + 1)) (.cons (j + 1 : Nat) .nil))
        exact hg (.cons ((y : Nat) % (j + 1)) (.cons (j + 1 : Nat) .nil))
          (Nat.mod_lt _ (Nat.succ_pos j))

/-- **The body is `Nat.gcd`'s equation** — `Nat.gcd_rec`, and nothing else. -/
theorem gcdBody_equation (δ : GEnv Sg.decls) (as : Env [Ty.nat, Ty.nat]) :
    gcdBody.eval (Sg := Sg) δ (as.append .nil) (.cons gcdFun .nil) = gcdFun as := by
  match as with
  | .cons x (.cons y .nil) =>
    cases (x : Nat) with
    | zero =>
      show (y : Nat) = gcdFun (.cons (0 : Nat) (.cons y .nil))
      simp [gcdFun, Env.get]
    | succ j =>
      show gcdFun (.cons ((y : Nat) % (j + 1)) (.cons (j + 1 : Nat) .nil))
          = gcdFun (.cons (j + 1 : Nat) (.cons y .nil))
      show Nat.gcd ((y : Nat) % (j + 1)) (j + 1) = Nat.gcd (j + 1) y
      exact (Nat.gcd_rec (j + 1) y).symm

/-- **Faithfulness of `gcd`, assembled from the two halves.** -/
theorem gcdTerm_implements_of_equation (δ : GEnv Sg.decls) :
    (gcdTerm (Sg := Sg)).Implements δ gcdFun :=
  Term.fix_implements_of_equation (Sg := Sg) (ps := [Ty.nat, Ty.nat]) (τ := Ty.nat)
    (k := 1) (Term.measure1 (♯0)) gcdBody (Term.natL 0) δ gcdFun
    (gcdBody_descends δ) (gcdBody_equation δ)

/-! ### The same condition, derived by the rule calculus

`gcdBody_descends` above is a hand proof: it destructures the arguments and runs the
evaluator.  `LakeJs.DescentVC` turns that into a structural derivation — one rule per node
of the body — whose *only* leftover goal is the arithmetic one, `y % x < x` under the path
condition `x ≠ 0`.  That leftover is exactly the obligation Lean's `decreasing_by`
discharges, which is the point of the exercise: the calculus asks the front end for
nothing that Lean has not already proved. -/

/-- The verification condition for `gcd` again, this time assembled from the rules of
    `LakeJs.DescentVC` rather than proved by hand. -/
theorem gcdBody_descends_by_rules (δ : GEnv Sg.decls) :
    Term.Descends (Sg := Sg) (Γ := []) (Ρ := []) (ps := [Ty.nat, Ty.nat]) (τ := Ty.nat)
      (Term.measure1 (♯0)) gcdBody δ .nil .nil := by
  refine Term.descends_of_selfIndepOn (Γ := []) (ps := [Ty.nat, Ty.nat]) (τ := Ty.nat)
    (k := 1) (Term.measure1 (♯0)) gcdBody δ .nil .nil (fun as => ?_)
  refine Term.selfIndepOn_ite ?_ (Term.selfIndepOn_var _) ?_
  · exact Term.selfIndepOn_ap
      (Term.selfIndepOn_ap (Term.selfIndepOn_extern _) (Term.selfIndepOn_var _))
      (Term.selfIndepOn_lit _)
  · refine Term.selfIndepOn_selfCall ?_ ?_
    · exact Spine.selfIndepOn_cons
        (Term.selfIndepOn_ap
          (Term.selfIndepOn_ap (Term.selfIndepOn_extern _) (Term.selfIndepOn_var _))
          (Term.selfIndepOn_var _))
        (Spine.selfIndepOn_cons (Term.selfIndepOn_var _) Spine.selfIndepOn_nil)
    · -- the one arithmetic obligation the calculus leaves
      rintro γ' g ⟨rfl, hc⟩
      match as with
      | .cons x (.cons y .nil) =>
        have h0 : decide ((show Nat from x) = 0) = false := hc
        have hx : (show Nat from x) ≠ 0 := of_decide_eq_false h0
        show Lex.NatVec.Lt
          (Lex.NatVec.cons ((show Nat from y) % (show Nat from x)) .nil)
          (Lex.NatVec.cons (show Nat from x) .nil)
        exact (Lex.NatVec.lt_one_iff _ _).mpr (Nat.mod_lt _ (Nat.pos_of_ne_zero hx))

/-! ## 5. `Tco07.boom`: the function a checked design must refuse

Lean accepts `boom` because the erased proof `h : Safe n` rules out every input but `1`,
so the call `boom (3 * n)` is dead code.  After erasure that branch is *reachable*, and it
does not descend: `Descends` is therefore **false** for the translated body, and it is
proved false below.

This is exactly the trade `TERM_RANK_FLAKINESS_AND_ALTERNATIVES.md` §5.4 names.  What the
guarded semantics gives is that the failure is not a wrong answer: the call answers
`stuck` (`boomTerm_at_two`), and `boomTerm` still agrees with Lean's `boom` at the one
input Lean's `boom` accepts (`boomTerm_at_one`). -/

/-- **`Descends` is false for the erased `boom`.**  At `n = 2` the body calls itself at
    `6`, which does not descend, so two self-references agreeing below `2` still give the
    body different answers. -/
theorem boomBody_not_descends (δ : GEnv Sg.decls) :
    ¬ Term.Descends (Sg := Sg) (Γ := []) (Ρ := []) (ps := [Ty.nat]) (τ := Ty.nat) (k := 1)
      (Term.measure1 (♯0)) boomBody δ .nil .nil := by
  intro h
  have hagree : ∀ bs : Env [Ty.nat],
      Lex.NatVec.Lt
          (Term.measureVal (Sg := Sg) (Γ := []) (ps := [Ty.nat]) (k := 1)
            (Term.measure1 (♯0)) δ .nil .nil bs)
          (Term.measureVal (Sg := Sg) (Γ := []) (ps := [Ty.nat]) (k := 1)
            (Term.measure1 (♯0)) δ .nil .nil (.cons (2 : Nat) .nil)) →
      (fun _ : Env [Ty.nat] => (0 : Nat)) bs
        = (fun bs : Env [Ty.nat] => if bs.get .head < 2 then (0 : Nat) else 1) bs := by
    intro bs hbs
    match bs with
    | .cons b .nil =>
      have hb : Lex.NatVec.Lt (Lex.NatVec.cons (show Nat from b) .nil)
          (Lex.NatVec.cons (2 : Nat) .nil) := hbs
      have hlt : (show Nat from b) < 2 := (Lex.NatVec.lt_one_iff _ _).mp hb
      show (0 : Nat) = if (show Nat from b) < 2 then (0 : Nat) else 1
      rw [if_pos hlt]
  have key := h (.cons (2 : Nat) .nil) (fun _ => (0 : Nat))
    (fun bs => if bs.get .head < 2 then (0 : Nat) else 1) hagree
  have h01 : (0 : Nat) = 1 := key
  exact absurd h01 (by decide)

/-! ## 6. The condition has teeth: a recursion that does **not** descend

`spinTerm` is the recursion whose body calls itself at the *same* argument — what used to
be the divergent term of the language.  Its `stuck` branch is reached, so `Descends` must
fail for it, and it does: two self-references that agree at every strictly smaller
argument still give different answers to the body, because the body asks about the current
one. -/

/-- The body of `spinTerm`: a single self call at the unchanged argument. -/
def spinBody : Term Sg [Ty.nat] [⟨[Ty.nat], Ty.nat⟩] Ty.nat :=
  .selfCall .head (.cons (♯0) .nil)

/-- `spinTerm` is that body, measured by its argument. -/
theorem spinTerm_eq : spinTerm (Sg := Sg)
    = .fix [Ty.nat] 1 (.cons (♯0) .nil) spinBody (Term.natL 7) := rfl

/-- **`Descends` fails for the spinning recursion** — which is why its `stuck` branch is
    reached.  The two self-references below agree on every argument of smaller measure and
    disagree on the answer, so the body is not independent of what happens at the current
    measure. -/
theorem spinBody_not_descends (δ : GEnv Sg.decls) :
    ¬ Term.Descends (Sg := Sg) (Γ := []) (Ρ := []) (ps := [Ty.nat]) (τ := Ty.nat) (k := 1)
      (.cons (♯0) .nil) spinBody δ .nil .nil := by
  intro h
  -- two self-references that agree at every smaller argument …
  have hagree : ∀ bs : Env [Ty.nat],
      Lex.NatVec.Lt
          (Term.measureVal (Sg := Sg) (Γ := []) (ps := [Ty.nat]) (k := 1)
            (.cons (♯0) .nil) δ .nil .nil bs)
          (Term.measureVal (Sg := Sg) (Γ := []) (ps := [Ty.nat]) (k := 1)
            (.cons (♯0) .nil) δ .nil .nil (.cons (5 : Nat) .nil)) →
      (fun _ : Env [Ty.nat] => (0 : Nat)) bs
        = (fun bs : Env [Ty.nat] => if bs.get .head < 5 then (0 : Nat) else 1) bs := by
    intro bs hbs
    match bs with
    | .cons b .nil =>
      have hb : Lex.NatVec.Lt (Lex.NatVec.cons (show Nat from b) .nil)
          (Lex.NatVec.cons (5 : Nat) .nil) := hbs
      have hlt : (show Nat from b) < 5 := (Lex.NatVec.lt_one_iff _ _).mp hb
      show (0 : Nat) = if (show Nat from b) < 5 then (0 : Nat) else 1
      rw [if_pos hlt]
  -- … but disagree on the answer the body gives, because the body asks at `5` itself
  have key := h (.cons (5 : Nat) .nil) (fun _ => (0 : Nat))
    (fun bs => if bs.get .head < 5 then (0 : Nat) else 1) hagree
  have h01 : (0 : Nat) = 1 := key
  exact absurd h01 (by decide)

/-- And so it gets stuck: at every input, `spinTerm` answers its `stuck` value. -/
example : Term.runNat1 (spinTerm (Sg := ⟨[], by decide⟩)) 5 = 7 := rfl

end LakeJs.Expr.Examples

end
