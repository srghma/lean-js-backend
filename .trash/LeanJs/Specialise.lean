import LakeJs.FromLcnf
import LakeJs.Scalarise

/-!
# Specialising the member tag of a merged dispatch loop

A mutually tail-recursive group is compiled into one function holding a `while` loop
whose first slot is the *tag* of the member that is currently running
(`LakeJs.Compile.transGroup`).  Every iteration then re-tests that tag:

```js
while (true) { if (v3 === 0) { …; v3 = 1; continue; } else { …; v3 = 0; continue; } }
```

When each jump inside the group names a member that is **statically known** — which is
the usual case, since a tail call names the function it calls — the tag is a
compile-time value and the test is waste.  This pass removes it, by *unrolling the
cycle*: the loop belongs to one member (the owner), and a jump to another member is
replaced by that member's body, spliced in with the arguments bound in front of it, up
to the jump that comes back round to the owner, which is the `continue` of the one
remaining loop.

```js
const _spec$testEven = (n, b1, b2) => {
  while (true) {
    …testEven's body…                 // jumps to testOdd:
    …testOdd's body, inlined…         // jumps back to testEven:
    n = …; b1 = …; b2 = …; continue;
  }
};
```

A member that is not the owner enters the loop by running its own body once — and the
bodies of the members between it and the owner — and then calling the owner's function,
which is a jump, not a recursion, so the stack stays constant exactly as it did before.

The conditions, checked in order and all of them conservative:

* every `Body.cont` of every member supplies a **literal** tag (`tagsOfBody`);
* each member therefore has one successor, and the successor map is a **single cycle**
  through all the members (`isSingleCycle`) — this is what makes the unrolling
  terminate, and makes each member's body appear once along each path;
* the cycle is short (`maxCycleLength`) and the unrolled function stays under a node
  budget (`sizeBudget`), since a member with several jumps duplicates the bodies that
  follow it.

Anything else keeps the merged dispatch loop, which stays the general case.

Everything here is a total, type-preserving rebuild: a body is moved into another
context by `LakeJs.Scalarise.mapTerm`, the substitution that answers `none` rather than
producing something ill-typed, so a specialised loop is well-scoped and well-typed by
construction, and a failure anywhere is just `none` and the merged loop.
-/

namespace LakeJs.Specialise

open LakeJs
open LakeJs.Ty
open LakeJs.Layout (FieldLayout ObjLayout)
open LakeJs.Expr
open LakeJs.Lookup
open LakeJs.Rename

/-! ## Reading the transition graph off the bodies -/

/-- The tags the jumps of a member's body name, or `none` if one of them is not a
    literal — that is a jump whose target is not statically known, and the group is then
    left as a dispatch loop. -/
def tagsOfBody {Sg : Sig} {Γ : Ctx} {slotTys : List Ty} {τ : Ty} :
    Body Sg Γ (Ty.nat :: slotTys) τ → Option (List Nat)
  | .ret _ => some []
  | .cont (.cons t _) => (LakeJs.Simp.natLit? t).map ([·])
  | .letB _ b => tagsOfBody b
  | .iteB _ t u => do
      let a ← tagsOfBody t
      let b ← tagsOfBody u
      pure (a ++ b)
  -- the body of a join point is a term, so it holds no jump round the loop
  | .joinPointB _ rest => tagsOfBody rest

/-- The one member a member jumps to, if all its jumps agree and it has at least one.
    A member that never jumps is no part of a cycle. -/
def uniqueSucc? (tags : List Nat) : Option Nat :=
  match tags with
  | [] => none
  | t :: rest => if rest.all (· == t) then some t else none

/-- Is `succ` — the successor of member `i`, at position `i` — a single cycle through
    every member?  Starting at the owner and following it must visit each member once
    and come back. -/
def isSingleCycle (succ : List Nat) : Bool := Id.run do
  let k := succ.length
  if k == 0 then return false
  if !succ.all (· < k) then return false
  let mut seen : Array Bool := Array.replicate k false
  let mut cur := 0
  for _ in [0:k] do
    if seen[cur]! then return false
    seen := seen.set! cur true
    cur := succ[cur]!
  return cur == 0 && seen.all id

/-- The successor of each member, when the whole group's transitions are statically
    known and form a single cycle; `none` otherwise. -/
def cycleOf? {Sg : Sig} {Γ : Ctx} {slotTys : List Ty} {τ : Ty}
    (bodies : List (Body Sg Γ (Ty.nat :: slotTys) τ)) : Option (List Nat) := do
  let tags ← bodies.mapM tagsOfBody
  let succ ← tags.mapM uniqueSucc?
  if isSingleCycle succ then some succ else none

/-! ## Rebuilding a member's body with its tag known -/

/-- What the variables of a member's body become once the member it belongs to, and the
    values of the argument slots, are known: the argument slots are the variables the
    caller has just bound for them (the first `slots` of the context, in the same order
    the loop had them), the tag slot is the literal tag of the member, and nothing else
    of the merged loop's context is in scope. -/
def memberEnv {Sg : Sig} (Δ : Ctx) (slots : Nat) (tag : Nat) : LakeJs.Scalarise.Env Sg Δ :=
  fun i =>
    if i < slots then LakeJs.Scalarise.varAtIndex? Δ i
    else if i == slots then some ⟨Ty.nat, .lit (.nat tag)⟩
    else none

/-- `let x₀ = a₀; … let x_{n-1} = a_{n-1};` in front of a block: the arguments of a jump,
    bound so that the body spliced in for that jump can read them as its argument slots.
    The continuation is given the context the bindings leave, whose first `n` variables
    are those values, most recently bound last. -/
partial def letSpine {Sg : Sig} {slots : List Ty} {τ : Ty} :
    {Δ : Ctx} → {σs : List Ty} → Spine Sg Δ σs →
      ((Δ' : Ctx) → Option (Body Sg Δ' slots τ)) → Option (Body Sg Δ slots τ)
  | Δ, _, .nil, k => k Δ
  | _, _, .cons (σ := σ) a rest, k => do
      let rest' ← Spine.rename? (LakeJs.Scalarise.shiftRen σ) rest
      let b ← letSpine rest' k
      pure (.letB a b)

/-- Rebuild the body of a member of the group with its tag known, in a loop whose slots
    are the argument slots alone.

    * a jump back to the owner is what the caller says it is (`onOwner`): the `continue`
      of the specialised loop, or a call of the function that owns it;
    * a jump to any other member binds its arguments and splices that member's body in,
      with its own tag known — the unrolling, which `fuel` bounds. -/
partial def specBody {Sg : Sig} {Γb : Ctx} {slotTys : List Ty} {τ : Ty}
    (bodies : Array (Body Sg Γb (Ty.nat :: slotTys) τ))
    (owner : Nat)
    (onOwner : {Δ : Ctx} → Spine Sg Δ slotTys → Body Sg Δ slotTys τ)
    (fuel : Nat) :
    {Γ : Ctx} → {Δ : Ctx} → LakeJs.Scalarise.Env Sg Δ → Body Sg Γ (Ty.nat :: slotTys) τ →
      Option (Body Sg Δ slotTys τ)
  | _, _, e, .ret t => (LakeJs.Scalarise.mapTerm e t).map .ret
  | _, _, e, .letB (σ := σ) v b => do
      let v' ← LakeJs.Scalarise.mapTerm e v
      let b' ← specBody bodies owner onOwner fuel (LakeJs.Scalarise.Env.liftList [σ] e) b
      pure (.letB v' b')
  | _, _, e, .iteB c t u => do
      let c' ← LakeJs.Scalarise.mapTerm e c
      let t' ← specBody bodies owner onOwner fuel e t
      let u' ← specBody bodies owner onOwner fuel e u
      pure (.iteB c' t' u')
  | _, _, e, .joinPointB (params := ps) (σ := σ) body rest => do
      let body' ← LakeJs.Scalarise.mapTerm (LakeJs.Scalarise.Env.liftList ps.reverse e) body
      let rest' ← specBody bodies owner onOwner fuel
        (LakeJs.Scalarise.Env.liftList [Ty.fn ps σ] e) rest
      pure (.joinPointB body' rest')
  | _, _, e, .cont (.cons tagT rest) => do
      let j ← LakeJs.Simp.natLit? tagT
      let rest' ← LakeJs.Scalarise.mapSpine e rest
      if j == owner then
        pure (onOwner rest')
      else
        if fuel == 0 then none
        else do
          let b ← bodies[j]?
          letSpine rest' fun Δ' =>
            specBody bodies owner onOwner (fuel - 1)
              (memberEnv Δ' slotTys.length j) b

/-- The body of the specialised loop: the owner's body, with every jump to another
    member unrolled and the jump that comes back round left as the one `continue`.
    `Δ` is the context the loop body is read in — the loop slots in front of the
    function's parameters. -/
def loopBody? {Sg : Sig} {Γb : Ctx} {slotTys : List Ty} {τ : Ty} (Δ : Ctx)
    (bodies : Array (Body Sg Γb (Ty.nat :: slotTys) τ)) (owner : Nat) :
    Option (Body Sg Δ slotTys τ) := do
  let b ← bodies[owner]?
  specBody bodies owner (fun sp => .cont sp) bodies.size
    (memberEnv Δ slotTys.length owner) b

/-- How a member that does not own the loop is entered: run its body once — and the
    bodies of the members between it and the owner — and then call the owner's function.
    That call is the last thing the member does and is made once per entry, not once per
    iteration, so the loop still runs in constant stack. -/
def enterTerm? {Sg : Sig} {Γb : Ctx} {slotTys : List Ty} {τ : Ty} {Γw : Ctx}
    (bodies : Array (Body Sg Γb (Ty.nat :: slotTys) τ)) (owner : Nat)
    (ownerRef : GlobalRef Sg (.fn slotTys τ)) (j : Nat) (args : Spine Sg Γw slotTys) :
    Option (Term Sg Γw τ) :=
  let call : {Δ : Ctx} → Spine Sg Δ slotTys → Body Sg Δ slotTys τ := fun sp =>
    .ret (.apN (.global ownerRef) sp)
  if j == owner then
    some (.apN (.global ownerRef) args)
  else do
    let b ← bodies[j]?
    let body ← letSpine args fun Δ' =>
      specBody bodies owner call bodies.size (memberEnv Δ' slotTys.length j) b
    LakeJs.FromLcnf.bodyToTerm? body

/-! ## The budget -/

mutual

/-- How many nodes a term has: the size the unrolling is budgeted against. -/
def termSize {Sg : Sig} : {Γ : Ctx} → {τ : Ty} → Term Sg Γ τ → Nat
  | _, _, .var _ | _, _, .lit _ | _, _, .global _ | _, _, .extern _ => 1
  | _, _, .lamN b => termSize b + 1
  | _, _, .apN f args => termSize f + spineSize args + 1
  | _, _, .lamProd rets => spineSize rets + 1
  | _, _, .callProd f args _ => termSize f + spineSize args + 1
  | _, _, .jsOp _ args => spineSize args + 1
  | _, _, .lazyMk e | _, _, .lazyForce e => termSize e + 1
  | _, _, .letE v b => termSize v + termSize b + 1
  | _, _, .ite c t u => termSize c + termSize t + termSize u + 1
  | _, _, .ctor _ _ _ args => spineSize args + 1
  | _, _, .proj v _ _ _ => termSize v + 1
  | _, _, .tagOf v _ => termSize v + 1
  | _, _, .caseTag s alts _ => termSize s + altsSize alts + 1
  | _, _, .loop init body => spineSize init + bodySize body + 1
  | _, _, .joinPoint body rest => termSize body + termSize rest + 1
  | _, _, .jump _ args => spineSize args + 1

/-- `termSize`, summed over a spine. -/
def spineSize {Sg : Sig} : {Γ : Ctx} → {σs : List Ty} → Spine Sg Γ σs → Nat
  | _, _, .nil => 0
  | _, _, .cons t rest => termSize t + spineSize rest

/-- `termSize`, summed over the branches of a case. -/
def altsSize {Sg : Sig} :
    {Γ : Ctx} → {τ : Ty} → {tags : List Nat} → Alts Sg Γ τ tags → Nat
  | _, _, _, .deflt t => termSize t
  | _, _, _, .cons _ t rest => termSize t + altsSize rest

/-- `termSize`, over a loop body. -/
def bodySize {Sg : Sig} : {Γ : Ctx} → {σs : List Ty} → {τ : Ty} → Body Sg Γ σs τ → Nat
  | _, _, _, .ret t => termSize t + 1
  | _, _, _, .cont args => spineSize args + 1
  | _, _, _, .letB v b => termSize v + bodySize b + 1
  | _, _, _, .iteB c t u => termSize c + bodySize t + bodySize u + 1
  | _, _, _, .joinPointB body rest => termSize body + bodySize rest + 1

end

/-- The longest cycle that is unrolled.  A `k`-cycle puts each member's body into the
    owner's loop once per path, so `k` is capped as well as the size. -/
def maxCycleLength : Nat := 3

/-- The most nodes a specialised function may have.  Beyond it the group keeps its
    dispatch loop: a member with several jumps duplicates everything that follows it,
    and a big loop body is worse for the instruction cache than one tag test. -/
def sizeBudget : Nat := 800

end LakeJs.Specialise
