import LakeJs.Simp
import LakeJs.Inline
import LakeJs.Scalarise
import LakeJs.DeadSlot
import LakeJs.Contify

/-!
# The optimiser as a relation

`LakeJs/Simp.lean` is the optimiser as a *function*: it takes a term and gives back a
better one.  That is what the backend runs, but it is not something one can state a
property of — "is the optimiser confluent?", "is it idempotent?", "does rule A commute
with rule B?" are all questions about the **individual rewrites**, and a function that
applies all of them at once in one bottom-up sweep has none of them written down.

So the rewrites are written down here, as an inductive relation:

```
t —→[tbl] t'   means   t' is t with one rewrite of the optimiser applied somewhere inside it
```

`Step` has one constructor per *rule* — the projection of a constructor application, the
dead `let`, the copy, the eta-contraction, the guarded `Nat` predecessor, and the two
rules of the inliner — and one per *position* a rewrite may be made in, which is what
makes the relation a congruence.  Its reflexive-transitive closure `Chain` is "reduces
to", written `—↠[tbl]`.

`tbl` is the table of declarations a call of which may be inlined
(`LakeJs.Inline.Table`), and it is what the rules `delta` and `deltaLit` read: unfolding a
call is justified by the *definition* of the callee, and a `Sig` records only names and
types, so the definitions have to be given.  Every other rule ignores it, which is why the
relation is one relation rather than two.

The relation and the functions are then tied together: `Term.simp_chain` (and its three
companions for spines, branches and loop blocks) proves

```
t —↠[tbl] Term.simp t
```

and `Term.inlineCalls_chain`, with the same three companions, proves

```
t —↠[tbl] LakeJs.Inline.Term.inlineCalls tbl t
```

that is: **every term the optimiser produces is reachable from the input by the rules of
this relation.**  The function is an *implementation* of the relation — a particular
strategy for applying the rules, bottom up, once each — rather than a separate thing that
happens to agree with it, and a property proved of `Step` is therefore a property of what
the backend actually emits.

Two things this file deliberately does not claim.

* Nothing here says that `Step` is confluent — and `LakeJs/ReduceConfluence.lean` proves
  that it is not, not even locally: a wrapper `fun (x0, x1) => add2(x0, x1)` around an
  inlinable declaration eta-contracts to `add2` and delta-expands to
  `fun (x0, x1) => x0 + x1`, which eta-contracts to the extern, and those two normal
  forms are different terms (`step_not_locallyConfluent`, `step_not_confluent`).  The
  two are the same *function*, so the emitted module is right whichever it prints; what
  fails is that the answer does not depend on the order the rules fire in, which is why
  the backend fixes an order rather than chasing the relation to a normal form.
* `LakeJs/Specialise.lean` is not part of the relation.  It does not rewrite one term
  into another: it takes the *bodies of a whole group* of declarations and builds one
  loop that the members enter, so what it relates is a module, not a term.
  `LakeJs/Scalarise.lean`, on the other hand, *is* part of it (`letCtorInline`,
  `scalariseSlot`): splitting a loop slot into its fields changes the slots the loop
  carries, but the slots of a loop are not part of the type of the term the loop is, so
  such a rewrite is still an endorelation on `Term Sg Γ τ`.

Everything in `Step` is type-preserving by construction: both sides of every constructor
are terms of the same `Term Sg Γ τ`, so "the optimiser cannot produce an ill-typed
program" is not a theorem here but a property of the statement.
-/

namespace LakeJs.Reduce

open LakeJs
open LakeJs.Ty
open LakeJs.Layout (FieldLayout ObjLayout)
open LakeJs.Expr
open LakeJs.Lookup
open LakeJs.Rename
open LakeJs.Simp
open LakeJs.Inline
open LakeJs.Scalarise

open LakeJs.Simp

/-! ## One rewrite -/

mutual

/-- `Step tbl t t'`: `t'` is `t` with one rewrite of the optimiser applied, either at the
    root (the first group of constructors, one per rule) or inside one of its
    subterms (the second group, one per position). -/
inductive Step {Sg : Sig} (tbl : Inline.Table Sg) :
    {Γ : Ctx} → {τ : Ty} → Term Sg Γ τ → Term Sg Γ τ → Prop
  /-- Reading a field of a value built right here is the field itself. -/
  | projOfCtor {Γ : Ctx} {σ τ : Ty} {e : Term Sg Γ σ} {i j : Nat}
      {h : σ.fieldTy? i j = some τ} {t : Term Sg Γ τ} :
      projOfCtor? e i j = some t → Step tbl (.proj e i j h) t
  /-- The `else` of a test against `0` knows the value is not zero, so the truncating
      subtraction in it is the plain one. -/
  | iteGuard {Γ : Ctx} {τ : Ty} {c : Term Sg Γ (.prim .bool)} {t u : Term Sg Γ τ}
      {i : Nat} :
      nonZeroGuard? c = some i → Step tbl (.ite c t u) (.ite c t (Term.assumeNonZero i u))
  /-- `let x = e; cast x` is `cast e`: a cast is not a value, it is the record that the
      value was read at another type. -/
  | letCast {Γ : Ctx} {σ τ : Ty} {e : Term Sg Γ σ} {b : Term Sg (σ :: Γ) τ}
      {rebuild : Term Sg Γ σ → Term Sg Γ τ} :
      castOfHead? b = some rebuild → Step tbl (.letE e b) (rebuild e)
  /-- A `let` whose value is a test against `0` teaches the branch it guards the same
      thing `iteGuard` does. -/
  | letGuard {Γ : Ctx} {σ τ : Ty} {e : Term Sg Γ σ} {b : Term Sg (σ :: Γ) τ} {i : Nat} :
      nonZeroGuard? e = some i →
      Step tbl (.letE e b) (.letE e (Term.guardNonZero 0 (i + 1) b))
  /-- `let x = e; x` is `e`. -/
  | letId {Γ : Ctx} {σ : Ty} {e : Term Sg Γ σ} : Step tbl (.letE e (.var .head)) e
  /-- `let x = e; b` is `b` when `b` never reads `x`.  Every term is a pure, total
      value, so a binding nobody reads can go. -/
  | letDead {Γ : Ctx} {σ τ : Ty} {e : Term Sg Γ σ} {b : Term Sg (σ :: Γ) τ}
      {b' : Term Sg Γ τ} :
      Term.strengthen? b = some b' → Step tbl (.letE e b) b'
  /-- `let x = y; b`, `let x = 1; b`, `let x = f; b`: the bound value is a copy of
      something that is already a value, so it goes where the variable was. -/
  | letCopy {Γ : Ctx} {σ τ : Ty} {e : Term Sg Γ σ} {b : Term Sg (σ :: Γ) τ}
      {r : Ren Sg (σ :: Γ) Γ} {b' : Term Sg Γ τ} :
      copyOfValue? e = some r → Term.rename? r b = some b' → Step tbl (.letE e b) b'
  /-- A lambda whose body applies a context-independent head to its own parameters in
      order is that head. -/
  | eta {Γ : Ctx} {ps : List Ty} {ret : Ty} {b : Term Sg (ps.reverse ++ Γ) ret}
      {t : Term Sg Γ (.fn ps ret)} :
      etaTarget? (ps := ps) b = some t → Step tbl (.lamN b) t
  /-- A saturated call of a declaration of the table is that declaration's body, with
      the arguments of the call in place of its parameters
      (`LakeJs.Inline.betaGlobal?`).  This is the one rule that reads the table: it is
      the *definition* of the callee that justifies the rewrite, and a `Sig` records only
      names and types, so the definitions have to be given. -/
  | delta {Γ : Ctx} {ps : List Ty} {ret : Ty} {r : GlobalRef Sg (.fn ps ret)}
      {args : Spine Sg Γ ps} {t : Term Sg Γ ret} :
      LakeJs.Inline.betaGlobal? tbl r args = some t →
        Step tbl (.apN (.global r) args) t
  /-- A reference to a declaration of the table whose body is a literal is that
      literal. -/
  | deltaLit {Γ : Ctx} {τ : Ty} {r : GlobalRef Sg τ} {t : Term Sg Γ τ} :
      LakeJs.Inline.litGlobal? tbl r = some t → Step tbl (.global r) t
  /-- A `let` of a constructor application that nothing needs whole goes to its uses:
      `LakeJs.Scalarise.mapTerm` puts the application at each of them, where it is a
      field read that `projOfCtor` then turns into the field itself, so the object is
      never built at all. -/
  | letCtorInline {Γ : Ctx} {σ τ : Ty} {v : Term Sg Γ σ} {b : Term Sg (σ :: Γ) τ}
      {b' : Term Sg Γ τ} :
      Scalarise.mapTerm (Scalarise.substHead v) b = some b' → Step tbl (.letE v b) b'
  /-- A loop slot whose value the body only takes apart and builds again becomes one slot
      per field (`LakeJs.Scalarise.scalariseSlot?`).  The loop that comes out carries
      *different slots* from the one that went in — and is a term of the same type, since
      the slots of a loop are not part of the type of the term the loop is, which is what
      lets this pass be a rule of the same relation as the rest. -/
  | scalariseSlot {Γ : Ctx} {σs : List Ty} {τ : Ty} {init : Spine Sg Γ σs}
      {body : Body Sg (σs.reverse ++ Γ) σs τ} {p : Nat} {t : Term Sg Γ τ} :
      Scalarise.scalariseSlot? init body p = some t → Step tbl (.loop init body) t
  /-- A loop slot no iteration reads is dropped (`LakeJs.DeadSlot.dropSlot?`): the loop
      starts with one value fewer and hands one value fewer round, and — as with
      `scalariseSlot` — the slots of a loop are not part of the type of the term the loop
      is, so the smaller loop is a term of the same type. -/
  | dropDeadSlot {Γ : Ctx} {σs : List Ty} {τ : Ty} {init : Spine Sg Γ σs}
      {body : Body Sg (σs.reverse ++ Γ) σs τ} {p : Nat} {t : Term Sg Γ τ} :
      DeadSlot.dropSlot? init body p = some t → Step tbl (.loop init body) t
  /-- A `let` of a lambda that is only ever *called* — never used as a value, never
      called from under a binder — is a join point (`LakeJs.Contify.contifiable`): the
      same body, bound by `Term.joinPoint`, and every call of it in the rest turned into
      a `Term.jump`.  Both sides bind the same body and run it on the same arguments at
      the same places; what changes is that the term now *says* the name never escapes,
      which is what `LakeJs.Usage` asks of a join point. -/
  | contify {Γ : Ctx} {ps : List Ty} {ret τ : Ty} {body : Term Sg (ps.reverse ++ Γ) ret}
      {b : Term Sg (.fn ps ret :: Γ) τ} :
      Contify.contifiable body b = true →
        Step tbl (.letE (.lamN body) b) (.joinPoint body (Contify.toJumps 0 b))
  -- the positions: a rewrite inside a subterm is a rewrite of the term
  | projArg {Γ : Ctx} {σ τ : Ty} {e e' : Term Sg Γ σ} {i j : Nat}
      {h : σ.fieldTy? i j = some τ} :
      Step tbl e e' → Step tbl (.proj e i j h) (.proj e' i j h)
  | tagOfArg {Γ : Ctx} {σ : Ty} {e e' : Term Sg Γ σ} {h : σ.isTagged = true} :
      Step tbl e e' → Step tbl (.tagOf e h) (.tagOf e' h)
  | lazyMkBody {Γ : Ctx} {τ : Ty} {e e' : Term Sg Γ τ} :
      Step tbl e e' → Step tbl (.lazyMk e) (.lazyMk e')
  | lazyForceArg {Γ : Ctx} {τ : Ty} {e e' : Term Sg Γ (.lazy τ)} :
      Step tbl e e' → Step tbl (.lazyForce e) (.lazyForce e')
  | iteCond {Γ : Ctx} {τ : Ty} {c c' : Term Sg Γ (.prim .bool)} {t u : Term Sg Γ τ} :
      Step tbl c c' → Step tbl (.ite c t u) (.ite c' t u)
  | iteThen {Γ : Ctx} {τ : Ty} {c : Term Sg Γ (.prim .bool)} {t t' u : Term Sg Γ τ} :
      Step tbl t t' → Step tbl (.ite c t u) (.ite c t' u)
  | iteElse {Γ : Ctx} {τ : Ty} {c : Term Sg Γ (.prim .bool)} {t u u' : Term Sg Γ τ} :
      Step tbl u u' → Step tbl (.ite c t u) (.ite c t u')
  | letVal {Γ : Ctx} {σ τ : Ty} {e e' : Term Sg Γ σ} {b : Term Sg (σ :: Γ) τ} :
      Step tbl e e' → Step tbl (.letE e b) (.letE e' b)
  | letBody {Γ : Ctx} {σ τ : Ty} {e : Term Sg Γ σ} {b b' : Term Sg (σ :: Γ) τ} :
      Step tbl b b' → Step tbl (.letE e b) (.letE e b')
  | lamBody {Γ : Ctx} {ps : List Ty} {ret : Ty} {b b' : Term Sg (ps.reverse ++ Γ) ret} :
      Step tbl b b' → Step tbl (.lamN (params := ps) b) (.lamN b')
  | apFun {Γ : Ctx} {ps : List Ty} {ret : Ty} {f f' : Term Sg Γ (.fn ps ret)}
      {args : Spine Sg Γ ps} :
      Step tbl f f' → Step tbl (.apN f args) (.apN f' args)
  | apArgs {Γ : Ctx} {ps : List Ty} {ret : Ty} {f : Term Sg Γ (.fn ps ret)}
      {args args' : Spine Sg Γ ps} :
      SpineStep tbl args args' → Step tbl (.apN (ret := ret) f args) (.apN f args')
  | lamProdRets {Γ : Ctx} {ps : List Ty} {r1 : Ty} {rs : List Ty}
      {rets rets' : Spine Sg (ps.reverse ++ Γ) (r1 :: rs)} :
      SpineStep tbl rets rets' →
      Step tbl (.lamProd (params := ps) rets) (.lamProd rets')
  | callProdFun {Γ : Ctx} {ps : List Ty} {r1 : Ty} {rs : List Ty}
      {f f' : Term Sg Γ (.fn_returnsProd ps r1 rs)} {args : Spine Sg Γ ps}
      {i : Fin (rs.length + 1)} :
      Step tbl f f' → Step tbl (.callProd f args i) (.callProd f' args i)
  | callProdArgs {Γ : Ctx} {ps : List Ty} {r1 : Ty} {rs : List Ty}
      {f : Term Sg Γ (.fn_returnsProd ps r1 rs)} {args args' : Spine Sg Γ ps}
      {i : Fin (rs.length + 1)} :
      SpineStep tbl args args' → Step tbl (.callProd f args i) (.callProd f args' i)
  | jsOpArgs {Γ : Ctx} {σs : List Ty} {τ : Ty} {op : JsOp σs τ}
      {args args' : Spine Sg Γ σs} :
      SpineStep tbl args args' → Step tbl (.jsOp op args) (.jsOp op args')
  | ctorArgs {Γ : Ctx} {τ : Ty} {i : Nat} {fs : FieldLayout}
      {h : τ.ctorFields? i = some fs} {args args' : Spine Sg Γ fs} :
      SpineStep tbl args args' → Step tbl (.ctor i fs h args) (.ctor i fs h args')
  | caseScrut {Γ : Ctx} {σ τ : Ty} {tags : List Nat} {s s' : Term Sg Γ σ}
      {alts : Alts Sg Γ τ tags} {h : σ.caseOk tags = true} :
      Step tbl s s' → Step tbl (.caseTag s alts h) (.caseTag s' alts h)
  | caseAlts {Γ : Ctx} {σ τ : Ty} {tags : List Nat} {s : Term Sg Γ σ}
      {alts alts' : Alts Sg Γ τ tags} {h : σ.caseOk tags = true} :
      AltsStep tbl alts alts' → Step tbl (.caseTag s alts h) (.caseTag s alts' h)
  | loopInit {Γ : Ctx} {σs : List Ty} {τ : Ty} {init init' : Spine Sg Γ σs}
      {body : Body Sg (σs.reverse ++ Γ) σs τ} :
      SpineStep tbl init init' → Step tbl (.loop init body) (.loop init' body)
  | loopBody {Γ : Ctx} {σs : List Ty} {τ : Ty} {init : Spine Sg Γ σs}
      {body body' : Body Sg (σs.reverse ++ Γ) σs τ} :
      BodyStep tbl body body' → Step tbl (.loop init body) (.loop init body')
  | joinBody {Γ : Ctx} {ps : List Ty} {σ τ : Ty}
      {body body' : Term Sg (ps.reverse ++ Γ) σ} {rest : Term Sg (.fn ps σ :: Γ) τ} :
      Step tbl body body' → Step tbl (.joinPoint body rest) (.joinPoint body' rest)
  | joinRest {Γ : Ctx} {ps : List Ty} {σ τ : Ty}
      {body : Term Sg (ps.reverse ++ Γ) σ} {rest rest' : Term Sg (.fn ps σ :: Γ) τ} :
      Step tbl rest rest' → Step tbl (.joinPoint body rest) (.joinPoint body rest')
  | jumpArgs {Γ : Ctx} {ps : List Ty} {σ : Ty} {v : Γ ∋ (.fn ps σ)}
      {args args' : Spine Sg Γ ps} :
      SpineStep tbl args args' → Step tbl (.jump v args) (.jump v args')

/-- A rewrite inside one argument of a spine. -/
inductive SpineStep {Sg : Sig} (tbl : Inline.Table Sg) : {Γ : Ctx} → {σs : List Ty} →
    Spine Sg Γ σs → Spine Sg Γ σs → Prop
  | head {Γ : Ctx} {σ : Ty} {σs : List Ty} {t t' : Term Sg Γ σ} {rest : Spine Sg Γ σs} :
      Step tbl t t' → SpineStep tbl (.cons t rest) (.cons t' rest)
  | tail {Γ : Ctx} {σ : Ty} {σs : List Ty} {t : Term Sg Γ σ}
      {rest rest' : Spine Sg Γ σs} :
      SpineStep tbl rest rest' → SpineStep tbl (.cons t rest) (.cons t rest')

/-- A rewrite inside one branch of a case. -/
inductive AltsStep {Sg : Sig} (tbl : Inline.Table Sg) :
    {Γ : Ctx} → {τ : Ty} → {tags : List Nat} → Alts Sg Γ τ tags → Alts Sg Γ τ tags → Prop
  | deflt {Γ : Ctx} {τ : Ty} {t t' : Term Sg Γ τ} :
      Step tbl t t' → AltsStep tbl (.deflt t) (.deflt t')
  | head {Γ : Ctx} {τ : Ty} {tags : List Nat} {tag : Nat} {t t' : Term Sg Γ τ}
      {rest : Alts Sg Γ τ tags} :
      Step tbl t t' → AltsStep tbl (.cons tag t rest) (.cons tag t' rest)
  | tail {Γ : Ctx} {τ : Ty} {tags : List Nat} {tag : Nat} {t : Term Sg Γ τ}
      {rest rest' : Alts Sg Γ τ tags} :
      AltsStep tbl rest rest' → AltsStep tbl (.cons tag t rest) (.cons tag t rest')

/-- A rewrite in a loop block: the rules of the `let` of a block, and the positions. -/
inductive BodyStep {Sg : Sig} (tbl : Inline.Table Sg) :
    {Γ : Ctx} → {σs : List Ty} → {τ : Ty} → Body Sg Γ σs τ → Body Sg Γ σs τ → Prop
  /-- The block's `let` of a test against `0` teaches the rest of the block that the
      value it tests is not zero. -/
  | letGuard {Γ : Ctx} {σ : Ty} {σs : List Ty} {τ : Ty} {e : Term Sg Γ σ}
      {b : Body Sg (σ :: Γ) σs τ} {i : Nat} :
      nonZeroGuard? e = some i →
      BodyStep tbl (.letB e b) (.letB e (Body.guardNonZero 0 (i + 1) b))
  /-- A block's `let` that the rest of the block never reads. -/
  | letDead {Γ : Ctx} {σ : Ty} {σs : List Ty} {τ : Ty} {e : Term Sg Γ σ}
      {b : Body Sg (σ :: Γ) σs τ} {b' : Body Sg Γ σs τ} :
      Body.strengthen? b = some b' → BodyStep tbl (.letB e b) b'
  /-- A block's `let` of a constructor application that nothing needs whole, which goes
      to its uses exactly as `Step.letCtorInline` does. -/
  | letCtorInline {Γ : Ctx} {σ : Ty} {σs : List Ty} {τ : Ty} {v : Term Sg Γ σ}
      {b : Body Sg (σ :: Γ) σs τ} {b' : Body Sg Γ σs τ} :
      Scalarise.mapBody (Scalarise.substHead v) b = some b' →
        BodyStep tbl (.letB v b) b'
  /-- A block's `let` of a copy. -/
  | letCopy {Γ : Ctx} {σ : Ty} {σs : List Ty} {τ : Ty} {e : Term Sg Γ σ}
      {b : Body Sg (σ :: Γ) σs τ} {r : Ren Sg (σ :: Γ) Γ} {b' : Body Sg Γ σs τ} :
      copyOfValue? e = some r → Body.rename? r b = some b' → BodyStep tbl (.letB e b) b'
  /-- The guarded predecessor, in a block. -/
  | iteGuard {Γ : Ctx} {σs : List Ty} {τ : Ty} {c : Term Sg Γ (.prim .bool)}
      {t u : Body Sg Γ σs τ} {i : Nat} :
      nonZeroGuard? c = some i →
      BodyStep tbl (.iteB c t u) (.iteB c t (Body.assumeNonZero i u))
  -- the positions
  | retTerm {Γ : Ctx} {σs : List Ty} {τ : Ty} {t t' : Term Sg Γ τ} :
      Step tbl t t' → BodyStep tbl (σs := σs) (.ret t) (.ret t')
  | contArgs {Γ : Ctx} {σs : List Ty} {τ : Ty} {args args' : Spine Sg Γ σs} :
      SpineStep tbl args args' → BodyStep tbl (τ := τ) (.cont args) (.cont args')
  | letBVal {Γ : Ctx} {σ : Ty} {σs : List Ty} {τ : Ty} {e e' : Term Sg Γ σ}
      {b : Body Sg (σ :: Γ) σs τ} :
      Step tbl e e' → BodyStep tbl (.letB e b) (.letB e' b)
  | letBBody {Γ : Ctx} {σ : Ty} {σs : List Ty} {τ : Ty} {e : Term Sg Γ σ}
      {b b' : Body Sg (σ :: Γ) σs τ} :
      BodyStep tbl b b' → BodyStep tbl (.letB e b) (.letB e b')
  | iteBCond {Γ : Ctx} {σs : List Ty} {τ : Ty} {c c' : Term Sg Γ (.prim .bool)}
      {t u : Body Sg Γ σs τ} :
      Step tbl c c' → BodyStep tbl (.iteB c t u) (.iteB c' t u)
  | iteBThen {Γ : Ctx} {σs : List Ty} {τ : Ty} {c : Term Sg Γ (.prim .bool)}
      {t t' u : Body Sg Γ σs τ} :
      BodyStep tbl t t' → BodyStep tbl (.iteB c t u) (.iteB c t' u)
  | iteBElse {Γ : Ctx} {σs : List Ty} {τ : Ty} {c : Term Sg Γ (.prim .bool)}
      {t u u' : Body Sg Γ σs τ} :
      BodyStep tbl u u' → BodyStep tbl (.iteB c t u) (.iteB c t u')
  /-- The block's `let` of a lambda that is only ever called is a join point of the
      block (`LakeJs.Contify.contifiableB`): `Step.contify`, one layer in. -/
  | contifyB {Γ : Ctx} {ps : List Ty} {ret : Ty} {σs : List Ty} {τ : Ty}
      {body : Term Sg (ps.reverse ++ Γ) ret} {b : Body Sg (.fn ps ret :: Γ) σs τ} :
      Contify.contifiableB body b = true →
        BodyStep tbl (.letB (.lamN body) b) (.joinPointB body (Contify.toJumpsBody 0 b))
  | joinBBody {Γ : Ctx} {ps : List Ty} {σ : Ty} {σs : List Ty} {τ : Ty}
      {body body' : Term Sg (ps.reverse ++ Γ) σ} {rest : Body Sg (.fn ps σ :: Γ) σs τ} :
      Step tbl body body' →
        BodyStep tbl (.joinPointB body rest) (.joinPointB body' rest)
  | joinBRest {Γ : Ctx} {ps : List Ty} {σ : Ty} {σs : List Ty} {τ : Ty}
      {body : Term Sg (ps.reverse ++ Γ) σ} {rest rest' : Body Sg (.fn ps σ :: Γ) σs τ} :
      BodyStep tbl rest rest' →
        BodyStep tbl (.joinPointB body rest) (.joinPointB body rest')

end

/-- `t —→[tbl] t'`: one rewrite of the optimiser, where `tbl` is the table of
    declarations a call of which may be inlined (`LakeJs.Inline.Table`). -/
scoped notation:40 t:41 " —→[" tbl "] " t':41 => Step tbl t t'

/-! ## Reducing to -/

/-- The reflexive-transitive closure of a relation: `a` reduces to `b` in zero or more
    steps. -/
inductive Chain {α : Sort u} (R : α → α → Prop) : α → α → Prop
  /-- No rewrite at all. -/
  | refl {a : α} : Chain R a a
  /-- One rewrite, then the rest. -/
  | head {a b c : α} : R a b → Chain R b c → Chain R a c

/-- `t —↠[tbl] t'`: zero or more rewrites of the optimiser. -/
scoped notation:20 t:21 " —↠[" tbl "] " t':21 => Chain (Step tbl) t t'

namespace Chain

/-- One rewrite is a reduction. -/
theorem single {α : Sort u} {R : α → α → Prop} {a b : α} (h : R a b) : Chain R a b :=
  .head h .refl

/-- Reductions compose. -/
theorem trans {α : Sort u} {R : α → α → Prop} {a b c : α}
    (h₁ : Chain R a b) (h₂ : Chain R b c) : Chain R a c := by
  induction h₁ with
  | refl => exact h₂
  | head hab _ ih => exact .head hab (ih h₂)

/-- A reduction followed by one more rewrite. -/
theorem tail {α : Sort u} {R : α → α → Prop} {a b c : α}
    (h₁ : Chain R a b) (h₂ : R b c) : Chain R a c :=
  h₁.trans (single h₂)

/-- A reduction inside a position is a reduction: `f` carries every rewrite over. -/
theorem congr {α : Sort u} {β : Sort v} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ {a b : α}, R a b → S (f a) (f b)) {a b : α}
    (h : Chain R a b) : Chain S (f a) (f b) := by
  induction h with
  | refl => exact .refl
  | head hab _ ih => exact .head (hf hab) ih

end Chain

/-! ## Reducing inside a position

One lemma per position of the language: a reduction of a subterm is a reduction of the
term.  Each is `Chain.congr` of the corresponding constructor of `Step`. -/

namespace Chain

variable {Sg : Sig} {tbl : Inline.Table Sg}

theorem projArg {Γ : Ctx} {σ τ : Ty} {e e' : Term Sg Γ σ} {i j : Nat}
    {h : σ.fieldTy? i j = some τ} (hc : e —↠[tbl] e') :
    (Term.proj e i j h) —↠[tbl] (Term.proj e' i j h) :=
  Chain.congr (fun x => Term.proj x i j h) (fun hs => .projArg hs) hc

theorem tagOfArg {Γ : Ctx} {σ : Ty} {e e' : Term Sg Γ σ} {h : σ.isTagged = true}
    (hc : e —↠[tbl] e') : (Term.tagOf e h) —↠[tbl] (Term.tagOf e' h) :=
  Chain.congr (fun x => Term.tagOf x h) (fun hs => .tagOfArg hs) hc

theorem lazyMkBody {Γ : Ctx} {τ : Ty} {e e' : Term Sg Γ τ}
    (hc : e —↠[tbl] e') : (Term.lazyMk e) —↠[tbl] (Term.lazyMk e') :=
  Chain.congr (fun x => Term.lazyMk x) (fun hs => .lazyMkBody hs) hc

theorem lazyForceArg {Γ : Ctx} {τ : Ty} {e e' : Term Sg Γ (.lazy τ)}
    (hc : e —↠[tbl] e') : (Term.lazyForce e) —↠[tbl] (Term.lazyForce e') :=
  Chain.congr (fun x => Term.lazyForce x) (fun hs => .lazyForceArg hs) hc

theorem iteCond {Γ : Ctx} {τ : Ty} {c c' : Term Sg Γ (.prim .bool)} {t u : Term Sg Γ τ}
    (hc : c —↠[tbl] c') : (Term.ite c t u) —↠[tbl] (Term.ite c' t u) :=
  Chain.congr (fun x => Term.ite x t u) (fun hs => .iteCond hs) hc

theorem iteThen {Γ : Ctx} {τ : Ty} {c : Term Sg Γ (.prim .bool)} {t t' u : Term Sg Γ τ}
    (hc : t —↠[tbl] t') : (Term.ite c t u) —↠[tbl] (Term.ite c t' u) :=
  Chain.congr (fun x => Term.ite c x u) (fun hs => .iteThen hs) hc

theorem iteElse {Γ : Ctx} {τ : Ty} {c : Term Sg Γ (.prim .bool)} {t u u' : Term Sg Γ τ}
    (hc : u —↠[tbl] u') : (Term.ite c t u) —↠[tbl] (Term.ite c t u') :=
  Chain.congr (fun x => Term.ite c t x) (fun hs => .iteElse hs) hc

theorem letVal {Γ : Ctx} {σ τ : Ty} {e e' : Term Sg Γ σ} {b : Term Sg (σ :: Γ) τ}
    (hc : e —↠[tbl] e') : (Term.letE e b) —↠[tbl] (Term.letE e' b) :=
  Chain.congr (fun x => Term.letE x b) (fun hs => .letVal hs) hc

theorem letBody {Γ : Ctx} {σ τ : Ty} {e : Term Sg Γ σ} {b b' : Term Sg (σ :: Γ) τ}
    (hc : b —↠[tbl] b') : (Term.letE e b) —↠[tbl] (Term.letE e b') :=
  Chain.congr (fun x => Term.letE e x) (fun hs => .letBody hs) hc

theorem lamBody {Γ : Ctx} {ps : List Ty} {ret : Ty} {b b' : Term Sg (ps.reverse ++ Γ) ret}
    (hc : b —↠[tbl] b') : (Term.lamN (params := ps) b) —↠[tbl] (Term.lamN b') :=
  Chain.congr (fun x => Term.lamN (params := ps) x) (fun hs => .lamBody hs) hc

theorem apFun {Γ : Ctx} {ps : List Ty} {ret : Ty} {f f' : Term Sg Γ (.fn ps ret)}
    {args : Spine Sg Γ ps} (hc : f —↠[tbl] f') :
    (Term.apN f args) —↠[tbl] (Term.apN f' args) :=
  Chain.congr (fun x => Term.apN x args) (fun hs => .apFun hs) hc

theorem apArgs {Γ : Ctx} {ps : List Ty} {ret : Ty} {f : Term Sg Γ (.fn ps ret)}
    {args args' : Spine Sg Γ ps} (hc : Chain (SpineStep tbl) args args') :
    (Term.apN f args) —↠[tbl] (Term.apN f args') :=
  Chain.congr (fun x => Term.apN f x) (fun hs => .apArgs hs) hc

theorem lamProdRets {Γ : Ctx} {ps : List Ty} {r1 : Ty} {rs : List Ty}
    {rets rets' : Spine Sg (ps.reverse ++ Γ) (r1 :: rs)}
    (hc : Chain (SpineStep tbl) rets rets') :
    (Term.lamProd (params := ps) rets) —↠[tbl] (Term.lamProd rets') :=
  Chain.congr (fun x => Term.lamProd (params := ps) x) (fun hs => .lamProdRets hs) hc

theorem callProdFun {Γ : Ctx} {ps : List Ty} {r1 : Ty} {rs : List Ty}
    {f f' : Term Sg Γ (.fn_returnsProd ps r1 rs)} {args : Spine Sg Γ ps}
    {i : Fin (rs.length + 1)} (hc : f —↠[tbl] f') :
    (Term.callProd f args i) —↠[tbl] (Term.callProd f' args i) :=
  Chain.congr (fun x => Term.callProd x args i) (fun hs => .callProdFun hs) hc

theorem callProdArgs {Γ : Ctx} {ps : List Ty} {r1 : Ty} {rs : List Ty}
    {f : Term Sg Γ (.fn_returnsProd ps r1 rs)} {args args' : Spine Sg Γ ps}
    {i : Fin (rs.length + 1)} (hc : Chain (SpineStep tbl) args args') :
    (Term.callProd f args i) —↠[tbl] (Term.callProd f args' i) :=
  Chain.congr (fun x => Term.callProd f x i) (fun hs => .callProdArgs hs) hc

theorem jsOpArgs {Γ : Ctx} {σs : List Ty} {τ : Ty} {op : JsOp σs τ}
    {args args' : Spine Sg Γ σs} (hc : Chain (SpineStep tbl) args args') :
    (Term.jsOp op args) —↠[tbl] (Term.jsOp op args') :=
  Chain.congr (fun x => Term.jsOp op x) (fun hs => .jsOpArgs hs) hc

theorem ctorArgs {Γ : Ctx} {τ : Ty} {i : Nat} {fs : FieldLayout}
    {h : τ.ctorFields? i = some fs} {args args' : Spine Sg Γ fs}
    (hc : Chain (SpineStep tbl) args args') :
    (Term.ctor i fs h args) —↠[tbl] (Term.ctor i fs h args') :=
  Chain.congr (fun x => Term.ctor i fs h x) (fun hs => .ctorArgs hs) hc

theorem caseScrut {Γ : Ctx} {σ τ : Ty} {tags : List Nat} {s s' : Term Sg Γ σ}
    {alts : Alts Sg Γ τ tags} {h : σ.caseOk tags = true} (hc : s —↠[tbl] s') :
    (Term.caseTag s alts h) —↠[tbl] (Term.caseTag s' alts h) :=
  Chain.congr (fun x => Term.caseTag x alts h) (fun hs => .caseScrut hs) hc

theorem caseAlts {Γ : Ctx} {σ τ : Ty} {tags : List Nat} {s : Term Sg Γ σ}
    {alts alts' : Alts Sg Γ τ tags} {h : σ.caseOk tags = true}
    (hc : Chain (AltsStep tbl) alts alts') :
    (Term.caseTag s alts h) —↠[tbl] (Term.caseTag s alts' h) :=
  Chain.congr (fun x => Term.caseTag s x h) (fun hs => .caseAlts hs) hc

theorem loopInit {Γ : Ctx} {σs : List Ty} {τ : Ty} {init init' : Spine Sg Γ σs}
    {body : Body Sg (σs.reverse ++ Γ) σs τ} (hc : Chain (SpineStep tbl) init init') :
    (Term.loop init body) —↠[tbl] (Term.loop init' body) :=
  Chain.congr (fun x => Term.loop x body) (fun hs => .loopInit hs) hc

theorem loopBody {Γ : Ctx} {σs : List Ty} {τ : Ty} {init : Spine Sg Γ σs}
    {body body' : Body Sg (σs.reverse ++ Γ) σs τ} (hc : Chain (BodyStep tbl) body body') :
    (Term.loop init body) —↠[tbl] (Term.loop init body') :=
  Chain.congr (fun x => Term.loop init x) (fun hs => .loopBody hs) hc

theorem joinBody {Γ : Ctx} {ps : List Ty} {σ τ : Ty} {body body' : Term Sg (ps.reverse ++ Γ) σ}
    {rest : Term Sg (.fn ps σ :: Γ) τ} (hc : body —↠[tbl] body') :
    (Term.joinPoint body rest) —↠[tbl] (Term.joinPoint body' rest) :=
  Chain.congr (fun x => Term.joinPoint x rest) (fun hs => .joinBody hs) hc

theorem joinRest {Γ : Ctx} {ps : List Ty} {σ τ : Ty} {body : Term Sg (ps.reverse ++ Γ) σ}
    {rest rest' : Term Sg (.fn ps σ :: Γ) τ} (hc : rest —↠[tbl] rest') :
    (Term.joinPoint body rest) —↠[tbl] (Term.joinPoint body rest') :=
  Chain.congr (fun x => Term.joinPoint body x) (fun hs => .joinRest hs) hc

theorem jumpArgs {Γ : Ctx} {ps : List Ty} {σ : Ty} {v : Γ ∋ (.fn ps σ)}
    {args args' : Spine Sg Γ ps} (hc : Chain (SpineStep tbl) args args') :
    (Term.jump v args) —↠[tbl] (Term.jump v args') :=
  Chain.congr (fun x => Term.jump v x) (fun hs => .jumpArgs hs) hc

theorem spineHead {Γ : Ctx} {σ : Ty} {σs : List Ty} {t t' : Term Sg Γ σ}
    {rest : Spine Sg Γ σs} (hc : t —↠[tbl] t') :
    Chain (SpineStep tbl) (Spine.cons t rest) (Spine.cons t' rest) :=
  Chain.congr (fun x => Spine.cons x rest) (fun hs => .head hs) hc

theorem spineTail {Γ : Ctx} {σ : Ty} {σs : List Ty} {t : Term Sg Γ σ}
    {rest rest' : Spine Sg Γ σs} (hc : Chain (SpineStep tbl) rest rest') :
    Chain (SpineStep tbl) (Spine.cons t rest) (Spine.cons t rest') :=
  Chain.congr (fun x => Spine.cons t x) (fun hs => .tail hs) hc

theorem altsDeflt {Γ : Ctx} {τ : Ty} {t t' : Term Sg Γ τ} (hc : t —↠[tbl] t') :
    Chain (AltsStep tbl) (Alts.deflt t) (Alts.deflt t') :=
  Chain.congr (fun x => Alts.deflt x) (fun hs => .deflt hs) hc

theorem altsHead {Γ : Ctx} {τ : Ty} {tags : List Nat} {tag : Nat} {t t' : Term Sg Γ τ}
    {rest : Alts Sg Γ τ tags} (hc : t —↠[tbl] t') :
    Chain (AltsStep tbl) (Alts.cons tag t rest) (Alts.cons tag t' rest) :=
  Chain.congr (fun x => Alts.cons tag x rest) (fun hs => .head hs) hc

theorem altsTail {Γ : Ctx} {τ : Ty} {tags : List Nat} {tag : Nat} {t : Term Sg Γ τ}
    {rest rest' : Alts Sg Γ τ tags} (hc : Chain (AltsStep tbl) rest rest') :
    Chain (AltsStep tbl) (Alts.cons tag t rest) (Alts.cons tag t rest') :=
  Chain.congr (fun x => Alts.cons tag t x) (fun hs => .tail hs) hc

theorem retTerm {Γ : Ctx} {σs : List Ty} {τ : Ty} {t t' : Term Sg Γ τ} (hc : t —↠[tbl] t') :
    Chain (BodyStep tbl) (Body.ret (σs := σs) t) (Body.ret t') :=
  Chain.congr (fun x => Body.ret (σs := σs) x) (fun hs => .retTerm hs) hc

theorem contArgs {Γ : Ctx} {σs : List Ty} {τ : Ty} {args args' : Spine Sg Γ σs}
    (hc : Chain (SpineStep tbl) args args') :
    Chain (BodyStep tbl) (Body.cont (τ := τ) args) (Body.cont args') :=
  Chain.congr (fun x => Body.cont (τ := τ) x) (fun hs => .contArgs hs) hc

theorem letBVal {Γ : Ctx} {σ : Ty} {σs : List Ty} {τ : Ty} {e e' : Term Sg Γ σ}
    {b : Body Sg (σ :: Γ) σs τ} (hc : e —↠[tbl] e') :
    Chain (BodyStep tbl) (Body.letB e b) (Body.letB e' b) :=
  Chain.congr (fun x => Body.letB x b) (fun hs => .letBVal hs) hc

theorem letBBody {Γ : Ctx} {σ : Ty} {σs : List Ty} {τ : Ty} {e : Term Sg Γ σ}
    {b b' : Body Sg (σ :: Γ) σs τ} (hc : Chain (BodyStep tbl) b b') :
    Chain (BodyStep tbl) (Body.letB e b) (Body.letB e b') :=
  Chain.congr (fun x => Body.letB e x) (fun hs => .letBBody hs) hc

theorem joinBBody {Γ : Ctx} {ps : List Ty} {σ : Ty} {σs : List Ty} {τ : Ty}
    {body body' : Term Sg (ps.reverse ++ Γ) σ} {rest : Body Sg (.fn ps σ :: Γ) σs τ}
    (hc : body —↠[tbl] body') :
    Chain (BodyStep tbl) (Body.joinPointB body rest) (Body.joinPointB body' rest) :=
  Chain.congr (fun x => Body.joinPointB x rest) (fun hs => .joinBBody hs) hc

theorem joinBRest {Γ : Ctx} {ps : List Ty} {σ : Ty} {σs : List Ty} {τ : Ty}
    {body : Term Sg (ps.reverse ++ Γ) σ} {rest rest' : Body Sg (.fn ps σ :: Γ) σs τ}
    (hc : Chain (BodyStep tbl) rest rest') :
    Chain (BodyStep tbl) (Body.joinPointB body rest) (Body.joinPointB body rest') :=
  Chain.congr (fun x => Body.joinPointB body x) (fun hs => .joinBRest hs) hc

theorem iteBCond {Γ : Ctx} {σs : List Ty} {τ : Ty} {c c' : Term Sg Γ (.prim .bool)}
    {t u : Body Sg Γ σs τ} (hc : c —↠[tbl] c') :
    Chain (BodyStep tbl) (Body.iteB c t u) (Body.iteB c' t u) :=
  Chain.congr (fun x => Body.iteB x t u) (fun hs => .iteBCond hs) hc

theorem iteBThen {Γ : Ctx} {σs : List Ty} {τ : Ty} {c : Term Sg Γ (.prim .bool)}
    {t t' u : Body Sg Γ σs τ} (hc : Chain (BodyStep tbl) t t') :
    Chain (BodyStep tbl) (Body.iteB c t u) (Body.iteB c t' u) :=
  Chain.congr (fun x => Body.iteB c x u) (fun hs => .iteBThen hs) hc

theorem iteBElse {Γ : Ctx} {σs : List Ty} {τ : Ty} {c : Term Sg Γ (.prim .bool)}
    {t u u' : Body Sg Γ σs τ} (hc : Chain (BodyStep tbl) u u') :
    Chain (BodyStep tbl) (Body.iteB c t u) (Body.iteB c t u') :=
  Chain.congr (fun x => Body.iteB c t x) (fun hs => .iteBElse hs) hc

end Chain

/-! ## The optimiser is a strategy for these rules

The function `LakeJs.Simp.Term.simp` walks a term bottom up and applies each rule where
it matches.  The theorems below say that everything it does is a reduction of the
relation above: the function is one *strategy* for the rules, not a second optimiser that
has to be kept in step with them by hand. -/

/-! ### The rules of each binding form

`LakeJs.Simp` collects the rules of each binding form into one function of the already
simplified parts (`simpProj`, `simpIte`, `simpLetE`, `simpLamN`, `simpLetB`, `simpIteB`).
Each of these lemmas says the same thing about one of them: whatever the function picks,
it is reachable from the rebuilt term by the rules. -/

theorem simpProj_chain {Sg : Sig} {tbl : Inline.Table Sg}
    {Γ : Ctx} {σ τ : Ty} {e' : Term Sg Γ σ} {i j : Nat}
    {h : σ.fieldTy? i j = some τ} {t0 : Term Sg Γ τ}
    (base : t0 —↠[tbl] Term.proj e' i j h) : t0 —↠[tbl] simpProj e' i j h := by
  unfold simpProj
  split
  · next heq => exact base.tail (.projOfCtor heq)
  · exact base

theorem simpIte_chain {Sg : Sig} {tbl : Inline.Table Sg}
    {Γ : Ctx} {τ : Ty} {c' : Term Sg Γ (.prim .bool)}
    {t' u' t0 : Term Sg Γ τ} (base : t0 —↠[tbl] Term.ite c' t' u') :
    t0 —↠[tbl] simpIte c' t' u' := by
  unfold simpIte
  split
  · next heq => exact base.tail (.iteGuard heq)
  · exact base

theorem simpLamN_chain {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx} {ps : List Ty} {ret : Ty}
    {b' : Term Sg (ps.reverse ++ Γ) ret} {t0 : Term Sg Γ (.fn ps ret)}
    (base : t0 —↠[tbl] Term.lamN b') : t0 —↠[tbl] simpLamN b' := by
  unfold simpLamN
  split
  · next heq => exact base.tail (.eta heq)
  · exact base

/-- The guard a bound value establishes is one rewrite. -/
theorem guardedBody_chain {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx} {σ τ : Ty} {e' : Term Sg Γ σ}
    {b0 : Term Sg (σ :: Γ) τ} {t0 : Term Sg Γ τ} (base : t0 —↠[tbl] Term.letE e' b0) :
    t0 —↠[tbl] Term.letE e' (guardedBody e' b0) := by
  unfold guardedBody
  split
  · next heq => exact base.tail (.letGuard heq)
  · exact base

/-- The rules a `let` is rewritten by once its guard has been applied. -/
theorem simpLetBody_chain {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx} {σ τ : Ty} {e' : Term Sg Γ σ}
    {b' : Term Sg (σ :: Γ) τ} {t0 : Term Sg Γ τ} (base : t0 —↠[tbl] Term.letE e' b') :
    t0 —↠[tbl] simpLetBody e' b' := by
  unfold simpLetBody
  split
  · exact base.tail .letId
  · split
    · next heq => exact base.tail (.letDead heq)
    · split
      · next heqc =>
        split
        · next heqr => exact base.tail (.letCopy heqc heqr)
        · exact base
      · exact base

theorem simpLetE_chain {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx} {σ τ : Ty} {e' : Term Sg Γ σ}
    {b0 : Term Sg (σ :: Γ) τ} {t0 : Term Sg Γ τ} (base : t0 —↠[tbl] Term.letE e' b0) :
    t0 —↠[tbl] simpLetE e' b0 := by
  unfold simpLetE
  split
  · next heq => exact base.tail (.letCast heq)
  · exact simpLetBody_chain (guardedBody_chain base)

theorem simpIteB_chain {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx} {σs : List Ty} {τ : Ty}
    {c' : Term Sg Γ (.prim .bool)} {t' u' t0 : Body Sg Γ σs τ}
    (base : Chain (BodyStep tbl) t0 (Body.iteB c' t' u')) :
    Chain (BodyStep tbl) t0 (simpIteB c' t' u') := by
  unfold simpIteB
  split
  · next heq => exact base.tail (.iteGuard heq)
  · exact base

/-- `guardedBody_chain`, for a loop block. -/
theorem guardedBodyB_chain {Sg : Sig} {tbl : Inline.Table Sg}
    {Γ : Ctx} {σ : Ty} {σs : List Ty} {τ : Ty}
    {e' : Term Sg Γ σ} {b0 : Body Sg (σ :: Γ) σs τ} {t0 : Body Sg Γ σs τ}
    (base : Chain (BodyStep tbl) t0 (Body.letB e' b0)) :
    Chain (BodyStep tbl) t0 (Body.letB e' (guardedBodyB e' b0)) := by
  unfold guardedBodyB
  split
  · next heq => exact base.tail (.letGuard heq)
  · exact base

/-- The rules a block's `let` is rewritten by once its guard has been applied. -/
theorem simpLetBBody_chain {Sg : Sig} {tbl : Inline.Table Sg}
    {Γ : Ctx} {σ : Ty} {σs : List Ty} {τ : Ty}
    {e' : Term Sg Γ σ} {b' : Body Sg (σ :: Γ) σs τ} {t0 : Body Sg Γ σs τ}
    (base : Chain (BodyStep tbl) t0 (Body.letB e' b')) :
    Chain (BodyStep tbl) t0 (simpLetBBody e' b') := by
  unfold simpLetBBody
  split
  · next heq => exact base.tail (.letDead heq)
  · split
    · next heqc =>
      split
      · next heqr => exact base.tail (.letCopy heqc heqr)
      · exact base
    · exact base

theorem simpLetB_chain {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx} {σ : Ty} {σs : List Ty} {τ : Ty}
    {e' : Term Sg Γ σ} {b0 : Body Sg (σ :: Γ) σs τ} {t0 : Body Sg Γ σs τ}
    (base : Chain (BodyStep tbl) t0 (Body.letB e' b0)) :
    Chain (BodyStep tbl) t0 (simpLetB e' b0) :=
  simpLetBBody_chain (guardedBodyB_chain base)

/-! ### The bottom-up walk -/

mutual

/-- Every term the optimiser produces is reachable from the term it was given by the
    rules of `Step`: the function is a *strategy* for the relation. -/
theorem Term.simp_chain {Sg : Sig} {tbl : Inline.Table Sg} : ∀ {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ),
    t —↠[tbl] Term.simp t
  | _, _, .var _ => .refl
  | _, _, .lit _ => .refl
  | _, _, .global _ => .refl
  | _, _, .extern _ => .refl
  | _, _, .proj e _ _ _ => simpProj_chain (Chain.projArg (Term.simp_chain e))
  | _, _, .tagOf e _ => Chain.tagOfArg (Term.simp_chain e)
  | _, _, .lazyMk e => Chain.lazyMkBody (Term.simp_chain e)
  | _, _, .lazyForce e => Chain.lazyForceArg (Term.simp_chain e)
  | _, _, .ite c t u =>
      simpIte_chain
        (((Chain.iteCond (Term.simp_chain c)).trans
          (Chain.iteThen (Term.simp_chain t))).trans (Chain.iteElse (Term.simp_chain u)))
  | _, _, .letE e b =>
      simpLetE_chain
        ((Chain.letVal (Term.simp_chain e)).trans (Chain.letBody (Term.simp_chain b)))
  | _, _, .lamN b => simpLamN_chain (Chain.lamBody (Term.simp_chain b))
  | _, _, .apN f args =>
      (Chain.apFun (Term.simp_chain f)).trans (Chain.apArgs (Spine.simp_chain args))
  | _, _, .lamProd rets => Chain.lamProdRets (Spine.simp_chain rets)
  | _, _, .callProd f args _ =>
      (Chain.callProdFun (Term.simp_chain f)).trans
        (Chain.callProdArgs (Spine.simp_chain args))
  | _, _, .jsOp _ args => Chain.jsOpArgs (Spine.simp_chain args)
  | _, _, .ctor _ _ _ args => Chain.ctorArgs (Spine.simp_chain args)
  | _, _, .caseTag s alts _ =>
      (Chain.caseScrut (Term.simp_chain s)).trans (Chain.caseAlts (Alts.simp_chain alts))
  | _, _, .loop init body =>
      (Chain.loopInit (Spine.simp_chain init)).trans (Chain.loopBody (Body.simp_chain body))
  | _, _, .joinPoint body rest =>
      (Chain.joinBody (Term.simp_chain body)).trans (Chain.joinRest (Term.simp_chain rest))
  | _, _, .jump _ args => Chain.jumpArgs (Spine.simp_chain args)

/-- `Term.simp_chain`, for the arguments of a spine. -/
theorem Spine.simp_chain {Sg : Sig} {tbl : Inline.Table Sg}
    : ∀ {Γ : Ctx} {σs : List Ty} (s : Spine Sg Γ σs),
    Chain (SpineStep tbl) s (Spine.simp s)
  | _, _, .nil => .refl
  | _, _, .cons t rest =>
      (Chain.spineHead (Term.simp_chain t)).trans (Chain.spineTail (Spine.simp_chain rest))

/-- `Term.simp_chain`, for the branches of a case. -/
theorem Alts.simp_chain {Sg : Sig} {tbl : Inline.Table Sg} :
    ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat} (a : Alts Sg Γ τ tags),
      Chain (AltsStep tbl) a (Alts.simp a)
  | _, _, _, .deflt t => Chain.altsDeflt (Term.simp_chain t)
  | _, _, _, .cons _ t rest =>
      (Chain.altsHead (Term.simp_chain t)).trans (Chain.altsTail (Alts.simp_chain rest))

/-- `Term.simp_chain`, for a loop block. -/
theorem Body.simp_chain {Sg : Sig} {tbl : Inline.Table Sg} :
    ∀ {Γ : Ctx} {σs : List Ty} {τ : Ty} (b : Body Sg Γ σs τ),
      Chain (BodyStep tbl) b (Body.simp b)
  | _, _, _, .ret t => Chain.retTerm (Term.simp_chain t)
  | _, _, _, .cont args => Chain.contArgs (Spine.simp_chain args)
  | _, _, _, .letB e b =>
      simpLetB_chain
        ((Chain.letBVal (Term.simp_chain e)).trans (Chain.letBBody (Body.simp_chain b)))
  | _, _, _, .iteB c t u =>
      simpIteB_chain
        (((Chain.iteBCond (Term.simp_chain c)).trans
          (Chain.iteBThen (Body.simp_chain t))).trans (Chain.iteBElse (Body.simp_chain u)))
  | _, _, _, .joinPointB body rest =>
      (Chain.joinBBody (Term.simp_chain body)).trans
        (Chain.joinBRest (Body.simp_chain rest))

end

/-- The optimiser as the backend runs it — two passes — is a reduction as well. -/
theorem Term.simpAll_chain {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ) :
    t —↠[tbl] Term.simpAll t :=
  (Term.simp_chain t).trans (Term.simp_chain (Term.simp t))

/-! ## The inliner is a strategy for these rules too

`LakeJs.Inline` walks a term bottom up and rewrites a call of a declaration of `tbl` into
that declaration's body.  The theorems below say the same thing of it as `simp_chain` says
of the simplifier: everything it does is a reduction of `Step tbl`. -/

/-- The rule of a reference to a declaration. -/
theorem inlineGlobal_chain {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx} {τ : Ty}
    {r : GlobalRef Sg τ} {t0 : Term Sg Γ τ} (base : t0 —↠[tbl] Term.global r) :
    t0 —↠[tbl] LakeJs.Inline.inlineGlobal tbl r := by
  unfold LakeJs.Inline.inlineGlobal
  split
  · next heq => exact base.tail (.deltaLit heq)
  · exact base

/-- The rule of an application. -/
theorem inlineApN_chain {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx}
    {ps : List Ty} {ret : Ty} {f' : Term Sg Γ (.fn ps ret)} {args' : Spine Sg Γ ps}
    {t0 : Term Sg Γ ret} (base : t0 —↠[tbl] Term.apN f' args') :
    t0 —↠[tbl] LakeJs.Inline.inlineApN tbl f' args' := by
  unfold LakeJs.Inline.inlineApN
  split
  · split
    · next heq => exact base.tail (.delta heq)
    · exact base
  · exact base

mutual

/-- Every term the inliner produces is reachable from the term it was given by the rules
    of `Step tbl`, `delta` and `deltaLit` among them. -/
theorem Term.inlineCalls_chain {Sg : Sig} {tbl : Inline.Table Sg} :
    ∀ {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ),
      t —↠[tbl] LakeJs.Inline.Term.inlineCalls tbl t
  | _, _, .var _ => .refl
  | _, _, .lit _ => .refl
  | _, _, .global _ => inlineGlobal_chain .refl
  | _, _, .extern _ => .refl
  | _, _, .proj e _ _ _ => Chain.projArg (Term.inlineCalls_chain e)
  | _, _, .tagOf e _ => Chain.tagOfArg (Term.inlineCalls_chain e)
  | _, _, .lazyMk e => Chain.lazyMkBody (Term.inlineCalls_chain e)
  | _, _, .lazyForce e => Chain.lazyForceArg (Term.inlineCalls_chain e)
  | _, _, .ite c t u =>
      ((Chain.iteCond (Term.inlineCalls_chain c)).trans
        (Chain.iteThen (Term.inlineCalls_chain t))).trans
          (Chain.iteElse (Term.inlineCalls_chain u))
  | _, _, .letE e b =>
      (Chain.letVal (Term.inlineCalls_chain e)).trans
        (Chain.letBody (Term.inlineCalls_chain b))
  | _, _, .lamN b => Chain.lamBody (Term.inlineCalls_chain b)
  | _, _, .apN f args =>
      inlineApN_chain
        ((Chain.apFun (Term.inlineCalls_chain f)).trans
          (Chain.apArgs (Spine.inlineCalls_chain args)))
  | _, _, .lamProd rets => Chain.lamProdRets (Spine.inlineCalls_chain rets)
  | _, _, .callProd f args _ =>
      (Chain.callProdFun (Term.inlineCalls_chain f)).trans
        (Chain.callProdArgs (Spine.inlineCalls_chain args))
  | _, _, .jsOp _ args => Chain.jsOpArgs (Spine.inlineCalls_chain args)
  | _, _, .ctor _ _ _ args => Chain.ctorArgs (Spine.inlineCalls_chain args)
  | _, _, .caseTag s alts _ =>
      (Chain.caseScrut (Term.inlineCalls_chain s)).trans
        (Chain.caseAlts (Alts.inlineCalls_chain alts))
  | _, _, .loop init body =>
      (Chain.loopInit (Spine.inlineCalls_chain init)).trans
        (Chain.loopBody (Body.inlineCalls_chain body))
  | _, _, .joinPoint body rest =>
      (Chain.joinBody (Term.inlineCalls_chain body)).trans
        (Chain.joinRest (Term.inlineCalls_chain rest))
  | _, _, .jump _ args => Chain.jumpArgs (Spine.inlineCalls_chain args)

/-- `Term.inlineCalls_chain`, for the arguments of a spine. -/
theorem Spine.inlineCalls_chain {Sg : Sig} {tbl : Inline.Table Sg} :
    ∀ {Γ : Ctx} {σs : List Ty} (s : Spine Sg Γ σs),
      Chain (SpineStep tbl) s (LakeJs.Inline.Spine.inlineCalls tbl s)
  | _, _, .nil => .refl
  | _, _, .cons t rest =>
      (Chain.spineHead (Term.inlineCalls_chain t)).trans
        (Chain.spineTail (Spine.inlineCalls_chain rest))

/-- `Term.inlineCalls_chain`, for the branches of a case. -/
theorem Alts.inlineCalls_chain {Sg : Sig} {tbl : Inline.Table Sg} :
    ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat} (a : Alts Sg Γ τ tags),
      Chain (AltsStep tbl) a (LakeJs.Inline.Alts.inlineCalls tbl a)
  | _, _, _, .deflt t => Chain.altsDeflt (Term.inlineCalls_chain t)
  | _, _, _, .cons _ t rest =>
      (Chain.altsHead (Term.inlineCalls_chain t)).trans
        (Chain.altsTail (Alts.inlineCalls_chain rest))

/-- `Term.inlineCalls_chain`, for a loop block. -/
theorem Body.inlineCalls_chain {Sg : Sig} {tbl : Inline.Table Sg} :
    ∀ {Γ : Ctx} {σs : List Ty} {τ : Ty} (b : Body Sg Γ σs τ),
      Chain (BodyStep tbl) b (LakeJs.Inline.Body.inlineCalls tbl b)
  | _, _, _, .ret t => Chain.retTerm (Term.inlineCalls_chain t)
  | _, _, _, .cont args => Chain.contArgs (Spine.inlineCalls_chain args)
  | _, _, _, .letB e b =>
      (Chain.letBVal (Term.inlineCalls_chain e)).trans
        (Chain.letBBody (Body.inlineCalls_chain b))
  | _, _, _, .iteB c t u =>
      ((Chain.iteBCond (Term.inlineCalls_chain c)).trans
        (Chain.iteBThen (Body.inlineCalls_chain t))).trans
          (Chain.iteBElse (Body.inlineCalls_chain u))
  | _, _, _, .joinPointB body rest =>
      (Chain.joinBBody (Term.inlineCalls_chain body)).trans
        (Chain.joinBRest (Body.inlineCalls_chain rest))

end

/-! ## The scalariser is a strategy for these rules too

`LakeJs.Scalarise` does two things: it moves a constructor application nothing needs
whole to the places that read its fields, and it gives a loop one slot per field of a
slot the body only takes apart and builds again.  Both are rules of `Step`, so the whole
pass is again a reduction — which is what the two theorems below say. -/

/-- The rule of a `let` the constructor inliner rewrites. -/
theorem inlineLet_chain {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx} {σ τ : Ty}
    {v' : Term Sg Γ σ} {b' : Term Sg (σ :: Γ) τ} {t0 : Term Sg Γ τ}
    (base : t0 —↠[tbl] Term.letE v' b') :
    t0 —↠[tbl] Scalarise.inlineLet v' b' := by
  unfold Scalarise.inlineLet
  split
  · split
    · exact base
    · split
      · next heq => exact base.tail (.letCtorInline heq)
      · exact base
  · exact base

/-- The rule of a block’s `let` the constructor inliner rewrites. -/
theorem inlineLetB_chain {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx} {σ : Ty}
    {σs : List Ty} {τ : Ty} {v' : Term Sg Γ σ} {b' : Body Sg (σ :: Γ) σs τ}
    {t0 : Body Sg Γ σs τ} (base : Chain (BodyStep tbl) t0 (Body.letB v' b')) :
    Chain (BodyStep tbl) t0 (Scalarise.inlineLetB v' b') := by
  unfold Scalarise.inlineLetB
  split
  · split
    · exact base
    · split
      · next heq => exact base.tail (.letCtorInline heq)
      · exact base
  · exact base

mutual

/-- Every term the constructor inliner produces is reachable from the term it was given
    by the rules of `Step tbl`. -/
theorem Term.inlineCtors_chain {Sg : Sig} {tbl : Inline.Table Sg} :
    ∀ {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ), t —↠[tbl] Scalarise.inlineTerm t
  | _, _, .var _ => .refl
  | _, _, .lit _ => .refl
  | _, _, .global _ => .refl
  | _, _, .extern _ => .refl
  | _, _, .proj e _ _ _ => Chain.projArg (Term.inlineCtors_chain e)
  | _, _, .tagOf e _ => Chain.tagOfArg (Term.inlineCtors_chain e)
  | _, _, .lazyMk e => Chain.lazyMkBody (Term.inlineCtors_chain e)
  | _, _, .lazyForce e => Chain.lazyForceArg (Term.inlineCtors_chain e)
  | _, _, .ite c t u =>
      ((Chain.iteCond (Term.inlineCtors_chain c)).trans
        (Chain.iteThen (Term.inlineCtors_chain t))).trans
          (Chain.iteElse (Term.inlineCtors_chain u))
  | _, _, .letE e b =>
      inlineLet_chain
        ((Chain.letVal (Term.inlineCtors_chain e)).trans
          (Chain.letBody (Term.inlineCtors_chain b)))
  | _, _, .lamN b => Chain.lamBody (Term.inlineCtors_chain b)
  | _, _, .apN f args =>
      (Chain.apFun (Term.inlineCtors_chain f)).trans
        (Chain.apArgs (Spine.inlineCtors_chain args))
  | _, _, .lamProd rets => Chain.lamProdRets (Spine.inlineCtors_chain rets)
  | _, _, .callProd f args _ =>
      (Chain.callProdFun (Term.inlineCtors_chain f)).trans
        (Chain.callProdArgs (Spine.inlineCtors_chain args))
  | _, _, .jsOp _ args => Chain.jsOpArgs (Spine.inlineCtors_chain args)
  | _, _, .ctor _ _ _ args => Chain.ctorArgs (Spine.inlineCtors_chain args)
  | _, _, .caseTag s alts _ =>
      (Chain.caseScrut (Term.inlineCtors_chain s)).trans
        (Chain.caseAlts (Alts.inlineCtors_chain alts))
  | _, _, .loop init body =>
      (Chain.loopInit (Spine.inlineCtors_chain init)).trans
        (Chain.loopBody (Body.inlineCtors_chain body))
  | _, _, .joinPoint body rest =>
      (Chain.joinBody (Term.inlineCtors_chain body)).trans
        (Chain.joinRest (Term.inlineCtors_chain rest))
  | _, _, .jump _ args => Chain.jumpArgs (Spine.inlineCtors_chain args)

/-- `Term.inlineCtors_chain`, for the arguments of a spine. -/
theorem Spine.inlineCtors_chain {Sg : Sig} {tbl : Inline.Table Sg} :
    ∀ {Γ : Ctx} {σs : List Ty} (s : Spine Sg Γ σs),
      Chain (SpineStep tbl) s (Scalarise.inlineSpine s)
  | _, _, .nil => .refl
  | _, _, .cons t rest =>
      (Chain.spineHead (Term.inlineCtors_chain t)).trans
        (Chain.spineTail (Spine.inlineCtors_chain rest))

/-- `Term.inlineCtors_chain`, for the branches of a case. -/
theorem Alts.inlineCtors_chain {Sg : Sig} {tbl : Inline.Table Sg} :
    ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat} (a : Alts Sg Γ τ tags),
      Chain (AltsStep tbl) a (Scalarise.inlineAlts a)
  | _, _, _, .deflt t => Chain.altsDeflt (Term.inlineCtors_chain t)
  | _, _, _, .cons _ t rest =>
      (Chain.altsHead (Term.inlineCtors_chain t)).trans
        (Chain.altsTail (Alts.inlineCtors_chain rest))

/-- `Term.inlineCtors_chain`, for a loop block. -/
theorem Body.inlineCtors_chain {Sg : Sig} {tbl : Inline.Table Sg} :
    ∀ {Γ : Ctx} {σs : List Ty} {τ : Ty} (b : Body Sg Γ σs τ),
      Chain (BodyStep tbl) b (Scalarise.inlineBody b)
  | _, _, _, .ret t => Chain.retTerm (Term.inlineCtors_chain t)
  | _, _, _, .cont args => Chain.contArgs (Spine.inlineCtors_chain args)
  | _, _, _, .letB e b =>
      inlineLetB_chain
        ((Chain.letBVal (Term.inlineCtors_chain e)).trans
          (Chain.letBBody (Body.inlineCtors_chain b)))
  | _, _, _, .iteB c t u =>
      ((Chain.iteBCond (Term.inlineCtors_chain c)).trans
        (Chain.iteBThen (Body.inlineCtors_chain t))).trans
          (Chain.iteBElse (Body.inlineCtors_chain u))
  | _, _, _, .joinPointB body rest =>
      (Chain.joinBBody (Term.inlineCtors_chain body)).trans
        (Chain.joinBRest (Body.inlineCtors_chain rest))

end

/-- Scalarising one slot is one rewrite. -/
theorem scalariseAt_step {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx} {τ : Ty}
    {t t' : Term Sg Γ τ} {p : Nat} (h : Scalarise.scalariseAt? t p = some t') :
    t —→[tbl] t' := by
  unfold Scalarise.scalariseAt? at h
  split at h
  · exact .scalariseSlot h
  · exact absurd h (by simp)

/-- Scalarising the first slot that can be is one rewrite. -/
theorem scalariseFrom_step {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx} {τ : Ty} :
    ∀ (n p : Nat) {t t' : Term Sg Γ τ}, Scalarise.scalariseFrom? n p t = some t' →
      t —→[tbl] t'
  | 0, _, _, _, h => absurd h (by simp [Scalarise.scalariseFrom?])
  | n + 1, p, t, t', h => by
      rw [Scalarise.scalariseFrom?] at h
      split at h
      · next heq =>
        rw [Option.some.injEq] at h
        exact h ▸ scalariseAt_step heq
      · exact scalariseFrom_step n (p + 1) h

/-- Every loop the scalariser produces is reachable from the loop it was given. -/
theorem scalariseLoopGo_chain {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx} {τ : Ty} :
    ∀ (f : Nat) (t : Term Sg Γ τ), t —↠[tbl] Scalarise.scalariseLoopGo f t
  | 0, t => by rw [Scalarise.scalariseLoopGo]; exact .refl
  | f + 1, t => by
      rw [Scalarise.scalariseLoopGo]
      split
      · next heq =>
        exact .head (scalariseFrom_step (tbl := tbl) _ _ heq) (scalariseLoopGo_chain f _)
      · exact .refl

/-- `scalariseLoopGo_chain`, with the budget the pass runs with. -/
theorem scalariseLoop_chain {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx} {τ : Ty}
    (t : Term Sg Γ τ) : t —↠[tbl] Scalarise.scalariseLoop t :=
  scalariseLoopGo_chain _ t

/-- The loops of a compiled declaration, scalarised. -/
theorem scalariseLoops_chain {Sg : Sig} {tbl : Inline.Table Sg} :
    ∀ {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ), t —↠[tbl] Scalarise.scalariseLoops t
  | _, _, .lamN b => Chain.lamBody (scalariseLoops_chain b)
  | _, _, .loop init body => scalariseLoop_chain (.loop init body)
  | _, _, .var _ => .refl
  | _, _, .lit _ => .refl
  | _, _, .global _ => .refl
  | _, _, .extern _ => .refl
  | _, _, .proj .. => .refl
  | _, _, .tagOf .. => .refl
  | _, _, .lazyMk .. => .refl
  | _, _, .lazyForce .. => .refl
  | _, _, .ite .. => .refl
  | _, _, .letE .. => .refl
  | _, _, .apN .. => .refl
  | _, _, .lamProd .. => .refl
  | _, _, .callProd .. => .refl
  | _, _, .jsOp .. => .refl
  | _, _, .ctor .. => .refl
  | _, _, .caseTag .. => .refl
  | _, _, .joinPoint .. => .refl
  | _, _, .jump .. => .refl

/-- The whole scalarising pass is a reduction of the rules. -/
theorem Term.scalarise_chain {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx} {τ : Ty}
    (t : Term Sg Γ τ) : t —↠[tbl] Scalarise.scalarise t :=
  (Term.inlineCtors_chain t).trans (scalariseLoops_chain (Scalarise.inlineTerm t))

/-- Simplify, inline, simplify — the first three passes of the pipeline — is a reduction
    of the rules.  `LakeJs/OptimiseChain.lean` says it of the whole of
    `LakeJs.Compile.optimise`, the scalariser included. -/
theorem Term.simp_inline_simp_chain {Sg : Sig} {tbl : Inline.Table Sg} {Γ : Ctx}
    {τ : Ty} (t : Term Sg Γ τ) :
    t —↠[tbl] Term.simpAll (LakeJs.Inline.Term.inlineCalls tbl (Term.simpAll t)) :=
  ((Term.simpAll_chain t).trans
    (Term.inlineCalls_chain (Term.simpAll t))).trans
      (Term.simpAll_chain (LakeJs.Inline.Term.inlineCalls tbl (Term.simpAll t)))

end LakeJs.Reduce
