import LakeJs.Lookup
import LakeJs.Rename
import LakeJs.Layout

/-!
# Scalarising a loop accumulator

A loop variable whose type is a record — a type with one constructor — costs an
allocation per iteration when the body takes it apart and builds a new one:

```js
const v7 = v5._1, v8 = v5._2;
const v15 = { tag: 0, _1: v8 + 1, _2: v7 + 2 };   // allocated every iteration
v5 = v15;
```

This pass gives the loop **one slot per field** instead of one slot for the value, so
the fields travel round the loop as scalars and the object is built only where the loop
answers:

```js
let v5 = b._1, v6 = b._2;
…
v5 = v6 + 1; v6 = v5old + 2;
…
return { tag: 0, _1: v5, _2: v6 };
```

How it is done, and why it stays well-typed: the loop variable is *substituted* by the
constructor applied to the new field slots. That alone is already correct — it is the
same value — and it is `LakeJs.Simp.projOfCtor?` that makes it fast: a `._1` of a value
built right there is the field itself, so every projection inside the body collapses to
a slot, and the only constructor applications left are the ones the body's answers need.
The jump round the loop is the one place that needs more than a substitution: its
argument for the slot is replaced by one projection per field, which the same rule then
collapses when the argument was a constructor application, which is exactly the case the
allocation came from.

The pass refuses — and leaves the loop boxed — when the value is used *whole* anywhere
but in an answer, since then the allocation would only move, which is the "re-boxing
trap" the snapshot's own comment names.
-/

namespace LakeJs.Scalarise

open LakeJs
open LakeJs.Ty
open LakeJs.Layout (FieldLayout ObjLayout)
open LakeJs.Expr
open LakeJs.Lookup
open LakeJs.Rename

/-- The variable `i` steps out of `Γ`, as a term of the type the context gives it. -/
def varAtIndex? {Sg : Sig} (Γ : Ctx) (i : Nat) : Option (SomeTerm Sg Γ) :=
  match Ctx.get? Γ i with
  | none => none
  | some τ => (Var.at? Γ i τ).map fun v => ⟨τ, .var v⟩

/-- The renaming that carries a term under one more binder. -/
def shiftRen {Sg : Sig} {Γ : Ctx} (σ : Ty) : Ren Sg Γ (σ :: Γ) where
  map v := some (.var (.tail v))

/-- Carry a term under one binder. -/
def weaken1? {Sg : Sig} {Γ : Ctx} {τ : Ty} (σ : Ty) (t : Term Sg Γ τ) :
    Option (Term Sg (σ :: Γ) τ) :=
  Term.rename? (shiftRen σ) t

/-- Carry a term under a whole list of binders. -/
def weakenList? {Sg : Sig} {Γ : Ctx} {τ : Ty} :
    (l : Ctx) → Term Sg Γ τ → Option (Term Sg (l ++ Γ) τ)
  | [], t => some t
  | σ :: l, t => (weakenList? l t).bind (weaken1? σ)

/-- What the variables of the term being rebuilt become: a term of the *new* context,
    which need not be a variable. -/
abbrev Env (Sg : Sig) (Δ : Ctx) := Nat → Option (SomeTerm Sg Δ)

/-- Carry an environment under a list of binders: the new binders stand for themselves
    and everything else is weakened past them. -/
def Env.liftList {Sg : Sig} {Δ : Ctx} (l : Ctx) (e : Env Sg Δ) : Env Sg (l ++ Δ) :=
  fun i =>
    if i < l.length then varAtIndex? (l ++ Δ) i
    else (e (i - l.length)).bind fun t => (weakenList? l t.2).map fun t' => ⟨t.1, t'⟩

mutual

/-- Rebuild a term in another context, replacing every variable by what the environment
    gives for it.  `none` when a variable has no image, or has one of the wrong type. -/
def mapTerm {Sg : Sig} {Δ : Ctx} (e : Env Sg Δ) :
    {Γ : Ctx} → {τ : Ty} → Term Sg Γ τ → Option (Term Sg Δ τ)
  | _, _, .var v => (e v.index).bind fun t => Term.coerce? _ t.2
  | _, _, .lit l => some (.lit l)
  | _, _, .global g => some (.global g)
  | _, _, .extern x => some (.extern x)
  | _, _, .lamN (params := ps) b => (mapTerm (Env.liftList ps.reverse e) b).map .lamN
  | _, _, .apN f args => do
      let f' ← mapTerm e f
      let args' ← mapSpine e args
      pure (.apN f' args')
  | _, _, .lamProd (params := ps) rets =>
      (mapSpine (Env.liftList ps.reverse e) rets).map .lamProd
  | _, _, .callProd f args i => do
      let f' ← mapTerm e f
      let args' ← mapSpine e args
      pure (.callProd f' args' i)
  | _, _, .jsOp op args => (mapSpine e args).map (.jsOp op)
  | _, _, .lazyMk t => (mapTerm e t).map .lazyMk
  | _, _, .lazyForce t => (mapTerm e t).map .lazyForce
  | _, _, .letE (σ := σ) v b => do
      let v' ← mapTerm e v
      let b' ← mapTerm (Env.liftList [σ] e) b
      pure (.letE v' b')
  | _, _, .ite c t u => do
      let c' ← mapTerm e c
      let t' ← mapTerm e t
      let u' ← mapTerm e u
      pure (.ite c' t' u')
  | _, _, .ctor i fs h args => (mapSpine e args).map (.ctor i fs h)
  | _, _, .proj v i j h => (mapTerm e v).map (.proj · i j h)
  | _, _, .tagOf v h => (mapTerm e v).map (.tagOf · h)
  | _, _, .caseTag s alts h => do
      let s' ← mapTerm e s
      let alts' ← mapAlts e alts
      pure (.caseTag s' alts' h)
  | _, _, .loop (σs := σs) init body => do
      let init' ← mapSpine e init
      let body' ← mapBody (Env.liftList σs.reverse e) body
      pure (.loop init' body')
  | _, _, .joinPoint (params := ps) (σ := σ) body rest => do
      let body' ← mapTerm (Env.liftList ps.reverse e) body
      let rest' ← mapTerm (Env.liftList [Ty.fn ps σ] e) rest
      pure (.joinPoint body' rest')
  | _, _, .jump (params := ps) (σ := σ) v args => do
      let f ← (e v.index).bind fun t => Term.coerce? (Ty.fn ps σ) t.2
      let args' ← mapSpine e args
      -- the target stays a join point when it is still a variable, and becomes the call
      -- a jump abbreviates when the environment replaced it by a term
      pure <| match f with
        | .var w => .jump w args'
        | f => .apN f args'

/-- `mapTerm`, on every term of a spine. -/
def mapSpine {Sg : Sig} {Δ : Ctx} (e : Env Sg Δ) :
    {Γ : Ctx} → {σs : List Ty} → Spine Sg Γ σs → Option (Spine Sg Δ σs)
  | _, _, .nil => some .nil
  | _, _, .cons t rest => do
      let t' ← mapTerm e t
      let rest' ← mapSpine e rest
      pure (.cons t' rest')

/-- `mapTerm`, on every branch of a case. -/
def mapAlts {Sg : Sig} {Δ : Ctx} (e : Env Sg Δ) :
    {Γ : Ctx} → {τ : Ty} → {tags : List Nat} → Alts Sg Γ τ tags → Option (Alts Sg Δ τ tags)
  | _, _, _, .deflt t => (mapTerm e t).map .deflt
  | _, _, _, .cons tag t rest => do
      let t' ← mapTerm e t
      let rest' ← mapAlts e rest
      pure (.cons tag t' rest')

/-- `mapTerm`, inside a loop body whose slots are unchanged. -/
def mapBody {Sg : Sig} {Δ : Ctx} (e : Env Sg Δ) :
    {Γ : Ctx} → {σs : List Ty} → {τ : Ty} → Body Sg Γ σs τ → Option (Body Sg Δ σs τ)
  | _, _, _, .ret t => (mapTerm e t).map .ret
  | _, _, _, .cont args => (mapSpine e args).map .cont
  | _, _, _, .letB (σ := σ) v b => do
      let v' ← mapTerm e v
      let b' ← mapBody (Env.liftList [σ] e) b
      pure (.letB v' b')
  | _, _, _, .iteB c t u => do
      let c' ← mapTerm e c
      let t' ← mapBody e t
      let u' ← mapBody e u
      pure (.iteB c' t' u')
  | _, _, _, .joinPointB (params := ps) (σ := σ) body rest => do
      let body' ← mapTerm (Env.liftList ps.reverse e) body
      let rest' ← mapBody (Env.liftList [Ty.fn ps σ] e) rest
      pure (.joinPointB body' rest')

end

/-- The terms of a spine, each at its own type. -/
def spineList {Sg : Sig} {Γ : Ctx} : {σs : List Ty} → Spine Sg Γ σs → List (SomeTerm Sg Γ)
  | _, .nil => []
  | _, .cons t rest => ⟨_, t⟩ :: spineList rest

/-- One projection per field of constructor `0` of `τp`, read off `a`.  Where `a` is a
    constructor application these collapse to its arguments, which is what makes the
    jump round a scalarised loop allocate nothing. -/
def projList {Sg : Sig} {Γ : Ctx} (a : Term Sg Γ τp) (fs : FieldLayout) :
    Option (List (SomeTerm Sg Γ)) :=
  (List.range fs.length).mapM fun j =>
    match h : τp.fieldTy? 0 j with
    | some _ => some (⟨_, Term.proj a 0 j h⟩ : SomeTerm Sg Γ)
    | none => none

/-- Replace element `p` of a list by the elements of `fs`. -/
def spliceAt (l : List Ty) (p : Nat) (fs : List Ty) : List Ty :=
  l.take p ++ fs ++ l.drop (p + 1)

/-! ## Is the slot worth scalarising, and safe to scalarise? -/

mutual

/-- Does the variable at de Bruijn index `i` occur somewhere other than as the value a
    `._j` is read out of?  Such a use needs the whole object, so scalarising would only
    move the allocation rather than remove it. -/
def usedWhole {Sg : Sig} (i : Nat) :
    {Γ : Ctx} → {τ : Ty} → Term Sg Γ τ → Bool
  | _, _, .var v => v.index == i
  | _, _, .lit _ | _, _, .global _ | _, _, .extern _ => false
  -- `x._j` is the good use: it needs the field, not the object, whichever variable `x`
  -- is — and a variable other than `i` is no use of `i` at all
  | _, _, .proj (.var _) _ _ _ => false
  | _, _, .proj v _ _ _ => usedWhole i v
  | _, _, .lamN (params := ps) b => usedWhole (i + ps.length) b
  | _, _, .apN f args => usedWhole i f || usedWholeSpine i args
  | _, _, .lamProd (params := ps) rets => usedWholeSpine (i + ps.length) rets
  | _, _, .callProd f args _ => usedWhole i f || usedWholeSpine i args
  | _, _, .jsOp _ args => usedWholeSpine i args
  | _, _, .lazyMk t | _, _, .lazyForce t => usedWhole i t
  | _, _, .letE v b => usedWhole i v || usedWhole (i + 1) b
  | _, _, .ite c t u => usedWhole i c || usedWhole i t || usedWhole i u
  | _, _, .ctor _ _ _ args => usedWholeSpine i args
  | _, _, .tagOf v _ => usedWhole i v
  | _, _, .caseTag s alts _ => usedWhole i s || usedWholeAlts i alts
  | _, _, .loop (σs := σs) init body =>
      usedWholeSpine i init || usedWholeBody (i + σs.length) body
  | _, _, .joinPoint (params := ps) body rest =>
      usedWhole (i + ps.length) body || usedWhole (i + 1) rest
  | _, _, .jump v args => v.index == i || usedWholeSpine i args

/-- `usedWhole`, on every term of a spine. -/
def usedWholeSpine {Sg : Sig} (i : Nat) :
    {Γ : Ctx} → {σs : List Ty} → Spine Sg Γ σs → Bool
  | _, _, .nil => false
  | _, _, .cons t rest => usedWhole i t || usedWholeSpine i rest

/-- `usedWhole`, on every branch of a case. -/
def usedWholeAlts {Sg : Sig} (i : Nat) :
    {Γ : Ctx} → {τ : Ty} → {tags : List Nat} → Alts Sg Γ τ tags → Bool
  | _, _, _, .deflt t => usedWhole i t
  | _, _, _, .cons _ t rest => usedWhole i t || usedWholeAlts i rest

/-- `usedWhole`, inside a loop body.  A `Body.ret` is ignored: an answer may hold the
    value whole, since it is then built once, where the loop leaves. -/
def usedWholeBody {Sg : Sig} (i : Nat) :
    {Γ : Ctx} → {σs : List Ty} → {τ : Ty} → Body Sg Γ σs τ → Bool
  | _, _, _, .ret _ => false
  | _, _, _, .cont args => usedWholeSpine i args
  | _, _, _, .letB v b => usedWhole i v || usedWholeBody (i + 1) b
  | _, _, _, .iteB c t u => usedWhole i c || usedWholeBody i t || usedWholeBody i u
  | _, _, _, .joinPointB (params := ps) body rest =>
      usedWhole (i + ps.length) body || usedWholeBody (i + 1) rest

/-- `usedWhole`, inside a loop body, counting the answers too. -/
def usedWholeBodyAll {Sg : Sig} (i : Nat) :
    {Γ : Ctx} → {σs : List Ty} → {τ : Ty} → Body Sg Γ σs τ → Bool
  | _, _, _, .ret t => usedWhole i t
  | _, _, _, .cont args => usedWholeSpine i args
  | _, _, _, .letB v b => usedWhole i v || usedWholeBodyAll (i + 1) b
  | _, _, _, .iteB c t u =>
      usedWhole i c || usedWholeBodyAll i t || usedWholeBodyAll i u
  | _, _, _, .joinPointB (params := ps) body rest =>
      usedWhole (i + ps.length) body || usedWholeBodyAll (i + 1) rest

/-- `usedWhole` in the places of a loop body that are *not* where the block ends: a
    whole use in an answer or in a jump happens once, at the end of the block, so a
    value moved there is built once; anywhere else it may be built again. -/
def usedWholeOffTail {Sg : Sig} (i : Nat) :
    {Γ : Ctx} → {σs : List Ty} → {τ : Ty} → Body Sg Γ σs τ → Bool
  | _, _, _, .ret _ => false
  | _, _, _, .cont _ => false
  | _, _, _, .letB v b => usedWhole i v || usedWholeOffTail (i + 1) b
  | _, _, _, .iteB c t u =>
      usedWhole i c || usedWholeOffTail i t || usedWholeOffTail i u
  | _, _, _, .joinPointB (params := ps) body rest =>
      usedWhole (i + ps.length) body || usedWholeOffTail (i + 1) rest

end

mutual

/-- How many times the variable at de Bruijn index `i` is needed *whole*.  A read
    *under a binder* — inside a lambda, or inside a nested loop — may happen any number
    of times, so it counts as many: substituting a value there could turn one allocation
    into one per call or per iteration.  A field read `x._j` counts for nothing: a
    constructor application substituted there is not built, since
    `LakeJs.Simp.projOfCtor?` reads the field straight out of it. -/
def occCount {Sg : Sig} (i : Nat) : {Γ : Ctx} → {τ : Ty} → Term Sg Γ τ → Nat
  | _, _, .var v => if v.index == i then 1 else 0
  | _, _, .lit _ | _, _, .global _ | _, _, .extern _ => 0
  | _, _, .lamN (params := ps) b => if occCount (i + ps.length) b == 0 then 0 else 2
  | _, _, .lamProd (params := ps) rets =>
      if occCountSpine (i + ps.length) rets == 0 then 0 else 2
  | _, _, .apN f args => occCount i f + occCountSpine i args
  | _, _, .callProd f args _ => occCount i f + occCountSpine i args
  | _, _, .jsOp _ args => occCountSpine i args
  -- a delayed value may be run more than once, so a use inside one is not a single use
  | _, _, .lazyMk t => if occCount i t == 0 then 0 else 2
  | _, _, .lazyForce t => occCount i t
  | _, _, .letE v b => occCount i v + occCount (i + 1) b
  | _, _, .ite c t u => occCount i c + max (occCount i t) (occCount i u)
  | _, _, .ctor _ _ _ args => occCountSpine i args
  | _, _, .proj (.var _) _ _ _ => 0
  | _, _, .proj v _ _ _ => occCount i v
  | _, _, .tagOf v _ => occCount i v
  | _, _, .caseTag s alts _ => occCount i s + occCountAlts i alts
  | _, _, .loop (σs := σs) init body =>
      occCountSpine i init + (if occCountBody (i + σs.length) body == 0 then 0 else 2)
  -- the body of a join point runs once per jump, so a read in it counts as many
  | _, _, .joinPoint (params := ps) body rest =>
      (if occCount (i + ps.length) body == 0 then 0 else 2) + occCount (i + 1) rest
  | _, _, .jump v args => (if v.index == i then 1 else 0) + occCountSpine i args

/-- `occCount`, on every term of a spine. -/
def occCountSpine {Sg : Sig} (i : Nat) :
    {Γ : Ctx} → {σs : List Ty} → Spine Sg Γ σs → Nat
  | _, _, .nil => 0
  | _, _, .cons t rest => occCount i t + occCountSpine i rest

/-- `occCount`, on every branch of a case: only one branch runs, so it is the largest
    of them. -/
def occCountAlts {Sg : Sig} (i : Nat) :
    {Γ : Ctx} → {τ : Ty} → {tags : List Nat} → Alts Sg Γ τ tags → Nat
  | _, _, _, .deflt t => occCount i t
  | _, _, _, .cons _ t rest => max (occCount i t) (occCountAlts i rest)

/-- `occCount`, inside a loop body. -/
def occCountBody {Sg : Sig} (i : Nat) :
    {Γ : Ctx} → {σs : List Ty} → {τ : Ty} → Body Sg Γ σs τ → Nat
  | _, _, _, .ret t => occCount i t
  | _, _, _, .cont args => occCountSpine i args
  | _, _, _, .letB v b => occCount i v + occCountBody (i + 1) b
  | _, _, _, .iteB c t u => occCount i c + max (occCountBody i t) (occCountBody i u)
  -- the body of a join point runs once per jump, so a read in it counts as many
  | _, _, _, .joinPointB (params := ps) body rest =>
      (if occCount (i + ps.length) body == 0 then 0 else 2) + occCountBody (i + 1) rest

end

/-- The environment that replaces the most recently bound variable by a term of the
    enclosing context and shifts everything else down: what inlining a `let` needs. -/
def substHead {Sg : Sig} {Γ : Ctx} {σ : Ty} (v : Term Sg Γ σ) : Env Sg Γ :=
  fun i => if i == 0 then some ⟨σ, v⟩ else varAtIndex? Γ (i - 1)

/-! ## Inlining a constructor nobody needs whole

The translation names every intermediate value, so the object a loop rebuilds arrives
here as `let x = { tag: 0, _1: a, _2: b }; … x._1 …`.  Where *every* use of such a
binding is a field read, the constructor application goes to the use sites, where
`LakeJs.Simp.projOfCtor?` turns each of them into the field itself and the object is
never built.  That is what makes the jump round a loop hand the fields over rather than
an object, which is the shape `scalariseSlot?` needs.
-/

/-- The rule this pass has, as a function of the *already rewritten* parts, so that it
    can be named and reasoned about (`LakeJs.Reduce`, `Step.letCtorInline`): a `let` of a
    constructor application that nothing needs whole goes to its uses, where every use is
    a field read that `LakeJs.Simp.projOfCtor?` then turns into the field itself. -/
def inlineLet {Sg : Sig} {Γ : Ctx} {σ τ : Ty} (v' : Term Sg Γ σ)
    (b' : Term Sg (σ :: Γ) τ) : Term Sg Γ τ :=
  match v' with
  | .ctor .. =>
      -- nothing needs the object whole, so every use of it collapses to a field
      if usedWhole 0 b' then .letE v' b'
      else
        match mapTerm (substHead v') b' with
        | some b'' => b''
        | none => .letE v' b'
  | _ => .letE v' b'

/-- `inlineLet`, for the `let` of a loop block: the object may also stay where it is
    built when its one use is where the block ends — an answer, or the jump round the
    loop, which is where a scalarised loop wants the fields handed over. -/
def inlineLetB {Sg : Sig} {Γ : Ctx} {σ : Ty} {σs : List Ty} {τ : Ty} (v' : Term Sg Γ σ)
    (b' : Body Sg (σ :: Γ) σs τ) : Body Sg Γ σs τ :=
  match v' with
  | .ctor .. =>
      if usedWholeBodyAll 0 b' && !(!usedWholeOffTail 0 b' && occCountBody 0 b' ≤ 1) then
        .letB v' b'
      else
        match mapBody (substHead v') b' with
        | some b'' => b''
        | none => .letB v' b'
  | _ => .letB v' b'

mutual

/-- Inline the constructor applications a term binds and only ever reads fields of. -/
def inlineTerm {Sg : Sig} : {Γ : Ctx} → {τ : Ty} → Term Sg Γ τ → Term Sg Γ τ
  | _, _, .letE v b => inlineLet (inlineTerm v) (inlineTerm b)
  | _, _, .lamN b => .lamN (inlineTerm b)
  | _, _, .apN f args => .apN (inlineTerm f) (inlineSpine args)
  | _, _, .lamProd rets => .lamProd (inlineSpine rets)
  | _, _, .callProd f args i => .callProd (inlineTerm f) (inlineSpine args) i
  | _, _, .jsOp op args => .jsOp op (inlineSpine args)
  | _, _, .lazyMk t => .lazyMk (inlineTerm t)
  | _, _, .lazyForce t => .lazyForce (inlineTerm t)
  | _, _, .ite c t u => .ite (inlineTerm c) (inlineTerm t) (inlineTerm u)
  | _, _, .ctor i fs h args => .ctor i fs h (inlineSpine args)
  | _, _, .proj v i j h => .proj (inlineTerm v) i j h
  | _, _, .tagOf v h => .tagOf (inlineTerm v) h
  | _, _, .caseTag s alts h => .caseTag (inlineTerm s) (inlineAlts alts) h
  | _, _, .loop init body => .loop (inlineSpine init) (inlineBody body)
  | _, _, .joinPoint body rest => .joinPoint (inlineTerm body) (inlineTerm rest)
  | _, _, .jump v args => .jump v (inlineSpine args)
  | _, _, t => t

/-- `inlineTerm`, on every term of a spine. -/
def inlineSpine {Sg : Sig} : {Γ : Ctx} → {σs : List Ty} → Spine Sg Γ σs → Spine Sg Γ σs
  | _, _, .nil => .nil
  | _, _, .cons t rest => .cons (inlineTerm t) (inlineSpine rest)

/-- `inlineTerm`, on every branch of a case. -/
def inlineAlts {Sg : Sig} :
    {Γ : Ctx} → {τ : Ty} → {tags : List Nat} → Alts Sg Γ τ tags → Alts Sg Γ τ tags
  | _, _, _, .deflt t => .deflt (inlineTerm t)
  | _, _, _, .cons tag t rest => .cons tag (inlineTerm t) (inlineAlts rest)

/-- `inlineTerm`, inside a loop body. -/
def inlineBody {Sg : Sig} :
    {Γ : Ctx} → {σs : List Ty} → {τ : Ty} → Body Sg Γ σs τ → Body Sg Γ σs τ
  | _, _, _, .ret t => .ret (inlineTerm t)
  | _, _, _, .cont args => .cont (inlineSpine args)
  | _, _, _, .letB v b => inlineLetB (inlineTerm v) (inlineBody b)
  | _, _, _, .iteB c t u => .iteB (inlineTerm c) (inlineBody t) (inlineBody u)
  | _, _, _, .joinPointB body rest =>
      .joinPointB (inlineTerm body) (inlineBody rest)

end

/-- Is the argument this jump gives slot `p` a constructor application — the object the
    loop rebuilds every time round?  That is the waste the pass exists to remove, so a
    loop with no such jump is left alone. -/
def rebuildsSlot {Sg : Sig} (p : Nat) :
    {Γ : Ctx} → {σs : List Ty} → {τ : Ty} → Body Sg Γ σs τ → Bool
  | _, _, _, .ret _ => false
  | _, _, _, .cont args =>
      match (spineList args)[p]? with
      | some ⟨_, .ctor 0 _ _ _⟩ => true
      | _ => false
  | _, _, _, .letB _ b => rebuildsSlot p b
  | _, _, _, .iteB _ t u => rebuildsSlot p t || rebuildsSlot p u
  | _, _, _, .joinPointB _ rest => rebuildsSlot p rest

/-- A jump inside the *whole* body reads the slot variable at an index that depends on
    how many binders it sits under, which `usedWholeBody` already tracks; this is the
    index the slot has at the top of the body. -/
def slotIndex (n p : Nat) : Nat := n - 1 - p

mutual

/-- Rebuild a loop body against the *new* slot list, expanding the argument each jump
    gives slot `p` into one argument per field. -/
def mapBodySplit {Sg : Sig} {Δ : Ctx} (e : Env Sg Δ) (p : Nat) (τp : Ty)
    (fs : FieldLayout) (σs' : List Ty) :
    {Γ : Ctx} → {σs : List Ty} → {τ : Ty} → Body Sg Γ σs τ → Option (Body Sg Δ σs' τ)
  | _, _, _, .ret t => (mapTerm e t).map .ret
  | _, _, _, .cont args => do
      let ts ← (spineList args).mapM fun t => (mapTerm e t.2).map fun t' => (⟨t.1, t'⟩ : SomeTerm Sg Δ)
      let a ← ts[p]?
      let a' ← Term.coerce? τp a.2
      let fields ← projList a' fs
      let spliced := ts.take p ++ fields ++ ts.drop (p + 1)
      (Spine.ofList? σs' spliced).map .cont
  | _, _, _, .letB (σ := σ) v b => do
      let v' ← mapTerm e v
      let b' ← mapBodySplit (Env.liftList [σ] e) p τp fs σs' b
      pure (.letB v' b')
  | _, _, _, .iteB c t u => do
      let c' ← mapTerm e c
      let t' ← mapBodySplit e p τp fs σs' t
      let u' ← mapBodySplit e p τp fs σs' u
      pure (.iteB c' t' u')
  | _, _, _, .joinPointB (params := ps) (σ := σ) body rest => do
      let body' ← mapTerm (Env.liftList ps.reverse e) body
      let rest' ← mapBodySplit (Env.liftList [Ty.fn ps σ] e) p τp fs σs' rest
      pure (.joinPointB body' rest')

end

/-- Scalarise slot `p` of this loop, when its type is a record whose value the body
    takes apart and rebuilds.  `none` leaves the loop as it is. -/
def scalariseSlot? {Sg : Sig} {Γ : Ctx} {τ : Ty} {σs : List Ty}
    (init : Spine Sg Γ σs) (body : Body Sg (σs.reverse ++ Γ) σs τ) (p : Nat) :
    Option (Term Sg Γ τ) := do
  let τp ← σs[p]?
  guard (τp.numCtors? == some 1)
  match h : τp.ctorFields? 0 with
  | none => none
  | some fs =>
    guard (fs.length ≥ 1)
    -- the body must rebuild the value, and never need it whole except in an answer
    guard (rebuildsSlot p body)
    guard (!usedWholeBody (slotIndex σs.length p) body)
    let k := fs.length
    let σs' := spliceAt σs p fs
    let n := σs.length
    let n' := σs'.length
    let Γn : Ctx := σs'.reverse ++ Γ
    -- the loop variable becomes the constructor applied to its new field slots
    let fieldVars ← (List.range k).mapM fun j => varAtIndex? (Sg := Sg) Γn (n' - 1 - (p + j))
    let fieldSpine ← Spine.ofList? fs fieldVars
    let boxed : Term Sg Γn τp := .ctor 0 fs h fieldSpine
    let env : Env Sg Γn := fun i =>
      if i < n then
        let s := n - 1 - i
        if s == p then some ⟨τp, boxed⟩
        else
          let s' := if s < p then s else s + k - 1
          varAtIndex? Γn (n' - 1 - s')
      else varAtIndex? Γn (i - n + n')
    let body' ← mapBodySplit env p τp fs σs' body
    -- the loop starts with the fields of the value it used to start with
    let its := spineList init
    let a ← its[p]?
    let a' ← Term.coerce? τp a.2
    let fields ← projList a' fs
    let init' ← Spine.ofList? σs' (its.take p ++ fields ++ its.drop (p + 1))
    pure (.loop init' body')

/-- Scalarise slot `p` of this term, when it is a loop and the slot can be. -/
def scalariseAt? {Sg : Sig} {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ) (p : Nat) :
    Option (Term Sg Γ τ) :=
  match t with
  | .loop init body => scalariseSlot? init body p
  | _ => none

/-- How many slots this term has, if it is a loop. -/
def slotCount {Sg : Sig} {Γ : Ctx} {τ : Ty} : Term Sg Γ τ → Nat
  | .loop (σs := σs) _ _ => σs.length
  | _ => 0

/-- The result of scalarising the first slot, from `p` on, that can be scalarised; `n` is
    how many slots are left to try. -/
def scalariseFrom? {Sg : Sig} {Γ : Ctx} {τ : Ty} :
    Nat → Nat → Term Sg Γ τ → Option (Term Sg Γ τ)
  | 0, _, _ => none
  | n + 1, p, t =>
    match scalariseAt? t p with
    | some t' => some t'
    | none => scalariseFrom? n (p + 1) t

/-- How many times a loop may be split before the pass gives up.  Splitting a slot into
    its fields makes the loop *wider*, and the pass then starts again at the first slot,
    so there is no structural measure to recurse on — but there is no need for one
    either: a loop of a compiled declaration has a handful of slots, and this bound is
    far above what any of them reaches.  Counting the splits rather than declaring the
    function `partial` is what gives it equations, and therefore what lets
    `LakeJs.Reduce` prove that what it produces is reachable by the rules. -/
def splitBudget : Nat := 64

/-- Scalarise every slot of this loop that can be, restarting at the first slot after
    each split, at most `splitBudget` times. -/
def scalariseLoopGo {Sg : Sig} {Γ : Ctx} {τ : Ty} : Nat → Term Sg Γ τ → Term Sg Γ τ
  | 0, t => t
  | f + 1, t =>
    match scalariseFrom? (slotCount t) 0 t with
    | some t' => scalariseLoopGo f t'
    | none => t

/-- Scalarise every slot of this loop that can be, left to right. -/
def scalariseLoop {Sg : Sig} {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ) : Term Sg Γ τ :=
  scalariseLoopGo splitBudget t

/-- Scalarise the loops a compiled declaration is made of: its body, and the body of
    each of its parameters' lambdas. -/
def scalariseLoops {Sg : Sig} {Γ : Ctx} {τ : Ty} : Term Sg Γ τ → Term Sg Γ τ
  | .lamN b => .lamN (scalariseLoops b)
  | t@(.loop ..) => scalariseLoop t
  | t => t

/-- The whole pass: inline the constructors nothing needs whole, then scalarise the
    loop slots that has made scalarisable. -/
def scalarise {Sg : Sig} {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ) : Term Sg Γ τ :=
  scalariseLoops (inlineTerm t)

end LakeJs.Scalarise
