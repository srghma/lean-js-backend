import LakeJs.Usage

/-!
# Contification: a local function that is only ever called is a join point

The translation binds the shared tail of a branch as a local function — `Term.letE` of a
`Term.lamN`, whose uses are calls of it.  That is what a **join point** is, and the
language has a form for it (`Term.joinPoint`, `Term.jump`) whose whole content is the
discipline `LakeJs.Usage` states of it: the name is jumped to and never used as a value,
so nothing ever captures it and it needs no closure.  This pass is what recognises one.

`let f = fun … => body; rest` becomes `joinPoint body rest'`, with every call of `f` in
`rest` turned into a jump, when

* `f` is called **at least once**, and every occurrence of it in `rest` is the *head of
  an application* (`onlyJumped`) — a use of `f` as a value would escape, which is exactly
  what a join point may not do.  A call is saturated by construction: the head of a
  `Term.apN` has type `.fn params ret` and its spine is typed by `params`, so a call of
  `f` gives it every argument it has;
* no occurrence is **under a binder** (`LakeJs.Usage.Term.occUnder`) — a jump from inside
  a lambda, a loop body or a thunk would be a call made after the block the join point
  belongs to has been left, which is a closure rather than a jump;
* the body reads every parameter, which is what the discipline asks of a join point (of a
  function it does not, since a function's arity is part of its type).

Nothing about the emitted JavaScript changes: `LakeJs.EmitJs` prints a join point as the
same `const f = (…) => { … };` and a jump as the same call.  What changes is what the
term *says*: the local function is marked as one that never escapes, and the checks of
`LakeJs.Usage` then hold the backend to it.

The rewrite is `LakeJs.Reduce.Step.contify`, and `LakeJs.Reduce.Term.contify_chain` says
the pass only ever fires it.
-/

namespace LakeJs.Contify

open LakeJs
open LakeJs.Ty
open LakeJs.Expr

/-! ## Is the variable only ever called? -/

mutual

/-- Is every occurrence of de Bruijn index `i` the head of an application, or the target
    of a jump?  Anywhere else it is a use of the value itself, which a join point may not
    have. -/
def onlyJumped {Sg : Sig} (i : Nat) : ∀ {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → Bool
  | _, _, .var v => v.index != i
  | _, _, .lit _ => true
  | _, _, .global _ => true
  | _, _, .extern _ => true
  | _, _, .apN f args =>
      (match f with
        | .var _ => true
        | f => onlyJumped i f) && onlyJumpedSpine i args
  | _, _, .lamN (params := ps) b => onlyJumped (i + ps.length) b
  | _, _, .lamProd (params := ps) rets => onlyJumpedSpine (i + ps.length) rets
  | _, _, .callProd f args _ => onlyJumped i f && onlyJumpedSpine i args
  | _, _, .jsOp _ args => onlyJumpedSpine i args
  | _, _, .lazyMk e | _, _, .lazyForce e => onlyJumped i e
  | _, _, .letE e b => onlyJumped i e && onlyJumped (i + 1) b
  | _, _, .ite c t u => onlyJumped i c && onlyJumped i t && onlyJumped i u
  | _, _, .ctor _ _ _ args => onlyJumpedSpine i args
  | _, _, .proj e _ _ _ => onlyJumped i e
  | _, _, .tagOf e _ => onlyJumped i e
  | _, _, .caseTag s alts _ => onlyJumped i s && onlyJumpedAlts i alts
  | _, _, .loop (σs := σs) init body =>
      onlyJumpedSpine i init && onlyJumpedBody (i + σs.length) body
  | _, _, .joinPoint (params := ps) body rest =>
      onlyJumped (i + ps.length) body && onlyJumped (i + 1) rest
  | _, _, .jump _ args => onlyJumpedSpine i args

/-- `onlyJumped`, over a spine. -/
def onlyJumpedSpine {Sg : Sig} (i : Nat) :
    ∀ {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → Bool
  | _, _, .nil => true
  | _, _, .cons t rest => onlyJumped i t && onlyJumpedSpine i rest

/-- `onlyJumped`, over the branches of a case. -/
def onlyJumpedAlts {Sg : Sig} (i : Nat) :
    ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat}, Alts Sg Γ τ tags → Bool
  | _, _, _, .deflt t => onlyJumped i t
  | _, _, _, .cons _ t rest => onlyJumped i t && onlyJumpedAlts i rest

/-- `onlyJumped`, over a loop block. -/
def onlyJumpedBody {Sg : Sig} (i : Nat) :
    ∀ {Γ : Ctx} {σs : List Ty} {τ : Ty}, Body Sg Γ σs τ → Bool
  | _, _, _, .ret t => onlyJumped i t
  | _, _, _, .cont args => onlyJumpedSpine i args
  | _, _, _, .letB e b => onlyJumped i e && onlyJumpedBody (i + 1) b
  | _, _, _, .iteB c t u => onlyJumped i c && onlyJumpedBody i t && onlyJumpedBody i u
  | _, _, _, .joinPointB (params := ps) body rest =>
      onlyJumped (i + ps.length) body && onlyJumpedBody (i + 1) rest

end

/-! ## Turning the calls into jumps -/

mutual

/-- Every call of de Bruijn index `i`, as a jump to it.  A call of anything else, and
    every other term, is left as it is. -/
def toJumps {Sg : Sig} (i : Nat) : ∀ {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → Term Sg Γ τ
  | _, _, .apN f args =>
      match f with
      | .var v => if v.index == i then .jump v (toJumpsSpine i args)
                  else .apN (.var v) (toJumpsSpine i args)
      | f => .apN (toJumps i f) (toJumpsSpine i args)
  | _, _, .lamN (params := ps) b => .lamN (toJumps (i + ps.length) b)
  | _, _, .lamProd (params := ps) rets => .lamProd (toJumpsSpine (i + ps.length) rets)
  | _, _, .callProd f args j => .callProd (toJumps i f) (toJumpsSpine i args) j
  | _, _, .jsOp op args => .jsOp op (toJumpsSpine i args)
  | _, _, .lazyMk e => .lazyMk (toJumps i e)
  | _, _, .lazyForce e => .lazyForce (toJumps i e)
  | _, _, .letE e b => .letE (toJumps i e) (toJumps (i + 1) b)
  | _, _, .ite c t u => .ite (toJumps i c) (toJumps i t) (toJumps i u)
  | _, _, .ctor k fs h args => .ctor k fs h (toJumpsSpine i args)
  | _, _, .proj e k j h => .proj (toJumps i e) k j h
  | _, _, .tagOf e h => .tagOf (toJumps i e) h
  | _, _, .caseTag s alts h => .caseTag (toJumps i s) (toJumpsAlts i alts) h
  | _, _, .loop (σs := σs) init body =>
      .loop (toJumpsSpine i init) (toJumpsBody (i + σs.length) body)
  | _, _, .joinPoint (params := ps) body rest =>
      .joinPoint (toJumps (i + ps.length) body) (toJumps (i + 1) rest)
  | _, _, .jump v args => .jump v (toJumpsSpine i args)
  | _, _, t => t

/-- `toJumps`, over a spine. -/
def toJumpsSpine {Sg : Sig} (i : Nat) :
    ∀ {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → Spine Sg Γ σs
  | _, _, .nil => .nil
  | _, _, .cons t rest => .cons (toJumps i t) (toJumpsSpine i rest)

/-- `toJumps`, over the branches of a case. -/
def toJumpsAlts {Sg : Sig} (i : Nat) :
    ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat}, Alts Sg Γ τ tags → Alts Sg Γ τ tags
  | _, _, _, .deflt t => .deflt (toJumps i t)
  | _, _, _, .cons tag t rest => .cons tag (toJumps i t) (toJumpsAlts i rest)

/-- `toJumps`, over a loop block. -/
def toJumpsBody {Sg : Sig} (i : Nat) :
    ∀ {Γ : Ctx} {σs : List Ty} {τ : Ty}, Body Sg Γ σs τ → Body Sg Γ σs τ
  | _, _, _, .ret t => .ret (toJumps i t)
  | _, _, _, .cont args => .cont (toJumpsSpine i args)
  | _, _, _, .letB e b => .letB (toJumps i e) (toJumpsBody (i + 1) b)
  | _, _, _, .iteB c t u => .iteB (toJumps i c) (toJumpsBody i t) (toJumpsBody i u)
  | _, _, _, .joinPointB (params := ps) body rest =>
      .joinPointB (toJumps (i + ps.length) body) (toJumpsBody (i + 1) rest)

end

/-! ## The rule -/

/-- May this `let` of a lambda be read as a join point?  It is called at least once,
    every occurrence of it is a call rather than a value, no occurrence is under a
    binder, and its body reads every parameter. -/
def contifiable {Sg : Sig} {Γ : Ctx} {ps : List Ty} {ret τ : Ty}
    (body : Term Sg (ps.reverse ++ Γ) ret) (b : Term Sg (.fn ps ret :: Γ) τ) : Bool :=
  1 ≤ Usage.Term.occ 0 b && Usage.Term.occUnder 0 b == 0 && onlyJumped 0 b &&
    Usage.paramsUsed ps.length body

/-- May this `letB` of a lambda be read as a join point of the block?  The conditions
    are those of `contifiable`, read over the block the binding is in front of. -/
def contifiableB {Sg : Sig} {Γ : Ctx} {ps : List Ty} {ret : Ty} {σs : List Ty} {τ : Ty}
    (body : Term Sg (ps.reverse ++ Γ) ret) (b : Body Sg (.fn ps ret :: Γ) σs τ) : Bool :=
  1 ≤ Usage.Body.occ 0 b && Usage.Body.occUnder 0 b == 0 && onlyJumpedBody 0 b &&
    Usage.paramsUsed ps.length body

/-- The rule itself, as a function of the already rewritten parts, so that it can be
    named and reasoned about (`LakeJs.Reduce.Step.contify`). -/
def contifyLet {Sg : Sig} {Γ : Ctx} {σ τ : Ty} (e : Term Sg Γ σ)
    (b : Term Sg (σ :: Γ) τ) : Term Sg Γ τ :=
  match e with
  | .lamN (params := ps) body =>
      if contifiable body b then .joinPoint body (toJumps 0 b) else .letE (.lamN body) b
  | e => .letE e b

/-- `contifyLet`, for a `let` of a loop block: the same rule, producing a
    `Body.joinPointB`. -/
def contifyLetB {Sg : Sig} {Γ : Ctx} {σ τ : Ty} {σs : List Ty} (e : Term Sg Γ σ)
    (b : Body Sg (σ :: Γ) σs τ) : Body Sg Γ σs τ :=
  match e with
  | .lamN (params := ps) body =>
      if contifiableB body b then .joinPointB body (toJumpsBody 0 b)
      else .letB (.lamN body) b
  | e => .letB e b

/-! ## The pass -/

mutual

/-- Read every local function that is only ever called as the join point it is. -/
def Term.contify {Sg : Sig} : ∀ {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → Term Sg Γ τ
  | _, _, .letE e b => contifyLet (Term.contify e) (Term.contify b)
  | _, _, .lamN b => .lamN (Term.contify b)
  | _, _, .apN f args => .apN (Term.contify f) (Spine.contify args)
  | _, _, .lamProd rets => .lamProd (Spine.contify rets)
  | _, _, .callProd f args i => .callProd (Term.contify f) (Spine.contify args) i
  | _, _, .jsOp op args => .jsOp op (Spine.contify args)
  | _, _, .lazyMk t => .lazyMk (Term.contify t)
  | _, _, .lazyForce t => .lazyForce (Term.contify t)
  | _, _, .ite c t u => .ite (Term.contify c) (Term.contify t) (Term.contify u)
  | _, _, .ctor i fs h args => .ctor i fs h (Spine.contify args)
  | _, _, .proj v i j h => .proj (Term.contify v) i j h
  | _, _, .tagOf v h => .tagOf (Term.contify v) h
  | _, _, .caseTag s alts h => .caseTag (Term.contify s) (Alts.contify alts) h
  | _, _, .loop init body => .loop (Spine.contify init) (Body.contify body)
  | _, _, .joinPoint body rest => .joinPoint (Term.contify body) (Term.contify rest)
  | _, _, .jump v args => .jump v (Spine.contify args)
  | _, _, t => t

/-- `Term.contify`, on every term of a spine. -/
def Spine.contify {Sg : Sig} : ∀ {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → Spine Sg Γ σs
  | _, _, .nil => .nil
  | _, _, .cons t rest => .cons (Term.contify t) (Spine.contify rest)

/-- `Term.contify`, on every branch of a case. -/
def Alts.contify {Sg : Sig} :
    ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat}, Alts Sg Γ τ tags → Alts Sg Γ τ tags
  | _, _, _, .deflt t => .deflt (Term.contify t)
  | _, _, _, .cons tag t rest => .cons tag (Term.contify t) (Alts.contify rest)

/-- `Term.contify`, inside a loop block: a local function bound by `Body.letB` and only
    ever called becomes a `Body.joinPointB`, exactly as one bound by `Term.letE` becomes
    a `Term.joinPoint`. -/
def Body.contify {Sg : Sig} :
    ∀ {Γ : Ctx} {σs : List Ty} {τ : Ty}, Body Sg Γ σs τ → Body Sg Γ σs τ
  | _, _, _, .ret t => .ret (Term.contify t)
  | _, _, _, .cont args => .cont (Spine.contify args)
  | _, _, _, .letB e b => contifyLetB (Term.contify e) (Body.contify b)
  | _, _, _, .iteB c t u => .iteB (Term.contify c) (Body.contify t) (Body.contify u)
  | _, _, _, .joinPointB body rest =>
      .joinPointB (Term.contify body) (Body.contify rest)

end

/-! ## How many join points a term has

What the pass produced, as a number: `LakeJs.Compile` prints it for a module, and
`scripts/count-join-points.lean` sums it over the corpus. -/

mutual

/-- The number of join points a term binds, those of its loop blocks included. -/
def Term.joinCount {Sg : Sig} : ∀ {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → Nat
  | _, _, .joinPoint body rest => Term.joinCount body + Term.joinCount rest + 1
  | _, _, .letE e b => Term.joinCount e + Term.joinCount b
  | _, _, .lamN b => Term.joinCount b
  | _, _, .apN f args => Term.joinCount f + Spine.joinCount args
  | _, _, .lamProd rets => Spine.joinCount rets
  | _, _, .callProd f args _ => Term.joinCount f + Spine.joinCount args
  | _, _, .jsOp _ args => Spine.joinCount args
  | _, _, .lazyMk t | _, _, .lazyForce t => Term.joinCount t
  | _, _, .ite c t u => Term.joinCount c + Term.joinCount t + Term.joinCount u
  | _, _, .ctor _ _ _ args => Spine.joinCount args
  | _, _, .proj v _ _ _ => Term.joinCount v
  | _, _, .tagOf v _ => Term.joinCount v
  | _, _, .caseTag s alts _ => Term.joinCount s + Alts.joinCount alts
  | _, _, .loop init body => Spine.joinCount init + Body.joinCount body
  | _, _, .jump _ args => Spine.joinCount args
  | _, _, _ => 0

/-- `Term.joinCount`, summed over a spine. -/
def Spine.joinCount {Sg : Sig} : ∀ {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → Nat
  | _, _, .nil => 0
  | _, _, .cons t rest => Term.joinCount t + Spine.joinCount rest

/-- `Term.joinCount`, summed over the branches of a case. -/
def Alts.joinCount {Sg : Sig} :
    ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat}, Alts Sg Γ τ tags → Nat
  | _, _, _, .deflt t => Term.joinCount t
  | _, _, _, .cons _ t rest => Term.joinCount t + Alts.joinCount rest

/-- `Term.joinCount`, summed over a loop block. -/
def Body.joinCount {Sg : Sig} :
    ∀ {Γ : Ctx} {σs : List Ty} {τ : Ty}, Body Sg Γ σs τ → Nat
  | _, _, _, .ret t => Term.joinCount t
  | _, _, _, .cont args => Spine.joinCount args
  | _, _, _, .letB e b => Term.joinCount e + Body.joinCount b
  | _, _, _, .iteB c t u => Term.joinCount c + Body.joinCount t + Body.joinCount u
  | _, _, _, .joinPointB body rest =>
      Term.joinCount body + Body.joinCount rest + 1

end

/-! ## Worked examples

A local function of a term, and one of a loop block: each is called twice, from two arms
of a conditional, so each is a join point and the pass says so. -/

/-- `let f = (n) => n + n; if (true) f(1) else f(2)`: a local function that never
    escapes. -/
def letOfLambdaExample : Term [] [] Ty.nat :=
  .letE (.lamN (params := [Ty.nat])
      (.apN (.extern .lean_nat_add) (.cons (♯0) (.cons (♯0) .nil))))
    (.ite (.lit (.bool true))
      (.apN (♯0) (.cons (.lit (.nat 1)) .nil))
      (.apN (♯0) (.cons (.lit (.nat 2)) .nil)))

/-- The pass reads it as a join point … -/
example : Term.joinCount (Term.contify letOfLambdaExample) = 1 := by decide +kernel

/-- … and the result keeps to the discipline `LakeJs.Usage` states of one. -/
example : Usage.Term.usesOk [] (Term.contify letOfLambdaExample) = true := by
  decide +kernel

/-- The same local function bound *inside a loop block*, which until `Body.joinPointB`
    existed had to stay a `let` of a lambda. -/
def loopLetOfLambdaExample : Term [] [] Ty.nat :=
  .loop (σs := [Ty.nat]) (.cons (.lit (.nat 3)) .nil)
    (.letB (.lamN (params := [Ty.nat])
        (.apN (.extern .lean_nat_add) (.cons (♯0) (.cons (♯1) .nil))))
      (.iteB (.lit (.bool true))
        (.ret (.apN (♯0) (.cons (.lit (.nat 1)) .nil)))
        (.ret (.apN (♯0) (.cons (.lit (.nat 2)) .nil)))))

/-- It becomes a `Body.joinPointB` … -/
example : Term.joinCount (Term.contify loopLetOfLambdaExample) = 1 := by decide +kernel

/-- … and the block keeps to the discipline, which as a `let` read twice it also did:
    what is new is that the term now says the name never escapes. -/
example : Usage.Term.usesOk [] (Term.contify loopLetOfLambdaExample) = true := by
  decide +kernel

end LakeJs.Contify
