module

public import LakeJs.Expr

@[expose] public section

/-!
# The usage discipline: no variable is bound for nothing

`Term` is intrinsically scoped and intrinsically typed, so a free variable and an
ill-typed application are already unrepresentable.  What its *type* cannot say is how
often a bound variable is read, and a binder that binds a name nothing reads — or one
whose name is read once, where the binder is waste rather than sharing — is exactly the
JavaScript a backend should not emit.  This file is that condition, as a `Bool` the
compiler can check and a subtype `WfTerm` a well-behaved term inhabits.

The rules are:

* **A variable a function binds is read at least once.**  A `Term.lamN`, a
  `Term.lamProd`, a `Term.loop` and the body of a `Term.joinPoint` all bind a whole list
  of variables at once; every one of them has to occur in the body.  A parameter nothing
  reads belongs to the calling convention of a function that does not need it.
* **A variable a `let` binds is read at least twice — or its one read is under a
  binder.**  Read twice, the `let` shares a value.  Read once, it shares nothing: the
  value belongs where it is read, and `LakeJs.LinearLet` is the pass that moves it
  there.  Read not at all, the `let` is dead, and `LakeJs.Simp` drops it.  The one
  exception is a single read that sits **under a binder** — inside a lambda, a loop
  body, the body of a join point or a thunk — because such a read happens once per
  call, per iteration, per jump or per force: there the binding is what keeps the work
  out of the loop or the closure, so it stays.  `Term.occUnder` counts exactly those
  reads, and the condition is `Usage.sharesOk`.
* **A join point is jumped to, and nothing else.**  The name a `Term.joinPoint` binds
  may appear only as the target of a `Term.jump`, and has to appear at least once.  That
  is what separates a join point from a `let` of a lambda: it never escapes, so it needs
  no closure, and it is never dead.

`Term.usesOk` is the full discipline, and `Term.usesOkDecl` the part the compiler
*enforces*: the parameters of a function are its calling convention, so an unread one is
reported rather than refused — see "The discipline of a whole declaration" below.  Two
passes establish the rest of it, `LakeJs.LinearLet` (the `let` with one reader) and
`LakeJs.DeadSlot` (the loop slot nothing reads), and `LakeJs.Compile` refuses a module
whose optimised terms still break it.

`Term.occ i t` counts the occurrences of de Bruijn index `i` in `t`, a *jump* to it
included, and `Term.usesOk` is the check itself.  The mask it carries says, for each
variable of the context, whether a join point bound it: that is how "used as a value"
and "used as a jump target" are told apart without a second context.
-/

namespace LakeJs.Usage

open LakeJs
open LakeJs.Expr

/-! ## Counting the occurrences of a variable -/

mutual

/-- How many times de Bruijn index `i` of the term's own context occurs in the term.
    The target of a `Term.jump` counts as an occurrence, so one function counts both the
    reads of an ordinary variable and the jumps to a join point. -/
def Term.occ {Sg : Sig} (i : Nat) : ∀ {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → Nat
  | _, _, .var v => if v.index == i then 1 else 0
  | _, _, .lit _ => 0
  | _, _, .global _ => 0
  | _, _, .extern _ => 0
  | _, _, .lamN (params := ps) b => Term.occ (i + ps.length) b
  | _, _, .apN f args => Term.occ i f + Spine.occ i args
  | _, _, .lamProd (params := ps) rets => Spine.occ (i + ps.length) rets
  | _, _, .callProd f args _ => Term.occ i f + Spine.occ i args
  | _, _, .jsOp _ args => Spine.occ i args
  | _, _, .lazyMk e | _, _, .lazyForce e => Term.occ i e
  | _, _, .letE e b => Term.occ i e + Term.occ (i + 1) b
  | _, _, .ite c t e => Term.occ i c + Term.occ i t + Term.occ i e
  | _, _, .ctor _ _ _ args => Spine.occ i args
  | _, _, .proj e _ _ _ => Term.occ i e
  | _, _, .tagOf e _ => Term.occ i e
  | _, _, .caseTag s alts _ => Term.occ i s + Alts.occ i alts
  | _, _, .loop (σs := σs) init body => Spine.occ i init + Body.occ (i + σs.length) body
  | _, _, .joinPoint (params := ps) body rest =>
      Term.occ (i + ps.length) body + Term.occ (i + 1) rest
  | _, _, .jump v args => (if v.index == i then 1 else 0) + Spine.occ i args

/-- `Term.occ`, summed over a spine. -/
def Spine.occ {Sg : Sig} (i : Nat) : ∀ {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → Nat
  | _, _, .nil => 0
  | _, _, .cons t rest => Term.occ i t + Spine.occ i rest

/-- `Term.occ`, summed over the branches of a case. -/
def Alts.occ {Sg : Sig} (i : Nat) :
    ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat}, Alts Sg Γ τ tags → Nat
  | _, _, _, .deflt t => Term.occ i t
  | _, _, _, .cons _ t rest => Term.occ i t + Alts.occ i rest

/-- `Term.occ`, summed over a loop block. -/
def Body.occ {Sg : Sig} (i : Nat) :
    ∀ {Γ : Ctx} {σs : List Ty} {τ : Ty}, Body Sg Γ σs τ → Nat
  | _, _, _, .ret t => Term.occ i t
  | _, _, _, .cont args => Spine.occ i args
  | _, _, _, .letB e b => Term.occ i e + Body.occ (i + 1) b
  | _, _, _, .iteB c t e => Term.occ i c + Body.occ i t + Body.occ i e
  | _, _, _, .joinPointB (params := ps) body rest =>
      Term.occ (i + ps.length) body + Body.occ (i + 1) rest

end

/-! ## Reads that sit under a binder -/

mutual

/-- How many occurrences of de Bruijn index `i` sit **under a binder**: in the body of a
    lambda, of a loop, of a join point, or inside a thunk.  Such a read happens once per
    call, per iteration, per jump or per force, so a `let` read only there is what keeps
    the work outside — which is why it is the one `let` with a single reader that the
    discipline allows. -/
def Term.occUnder {Sg : Sig} (i : Nat) : ∀ {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → Nat
  | _, _, .var _ => 0
  | _, _, .lit _ => 0
  | _, _, .global _ => 0
  | _, _, .extern _ => 0
  | _, _, .lamN (params := ps) b => Term.occ (i + ps.length) b
  | _, _, .lamProd (params := ps) rets => Spine.occ (i + ps.length) rets
  | _, _, .apN f args => Term.occUnder i f + Spine.occUnder i args
  | _, _, .callProd f args _ => Term.occUnder i f + Spine.occUnder i args
  | _, _, .jsOp _ args => Spine.occUnder i args
  | _, _, .lazyMk e => Term.occ i e
  | _, _, .lazyForce e => Term.occUnder i e
  | _, _, .letE e b => Term.occUnder i e + Term.occUnder (i + 1) b
  | _, _, .ite c t u => Term.occUnder i c + Term.occUnder i t + Term.occUnder i u
  | _, _, .ctor _ _ _ args => Spine.occUnder i args
  | _, _, .proj e _ _ _ => Term.occUnder i e
  | _, _, .tagOf e _ => Term.occUnder i e
  | _, _, .caseTag s alts _ => Term.occUnder i s + Alts.occUnder i alts
  | _, _, .loop (σs := σs) init body =>
      Spine.occUnder i init + Body.occ (i + σs.length) body
  | _, _, .joinPoint (params := ps) body rest =>
      Term.occ (i + ps.length) body + Term.occUnder (i + 1) rest
  | _, _, .jump _ args => Spine.occUnder i args

/-- `Term.occUnder`, summed over a spine. -/
def Spine.occUnder {Sg : Sig} (i : Nat) :
    ∀ {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → Nat
  | _, _, .nil => 0
  | _, _, .cons t rest => Term.occUnder i t + Spine.occUnder i rest

/-- `Term.occUnder`, summed over the branches of a case. -/
def Alts.occUnder {Sg : Sig} (i : Nat) :
    ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat}, Alts Sg Γ τ tags → Nat
  | _, _, _, .deflt t => Term.occUnder i t
  | _, _, _, .cons _ t rest => Term.occUnder i t + Alts.occUnder i rest

/-- `Term.occUnder`, summed over a loop block. -/
def Body.occUnder {Sg : Sig} (i : Nat) :
    ∀ {Γ : Ctx} {σs : List Ty} {τ : Ty}, Body Sg Γ σs τ → Nat
  | _, _, _, .ret t => Term.occUnder i t
  | _, _, _, .cont args => Spine.occUnder i args
  | _, _, _, .letB e b => Term.occUnder i e + Body.occUnder (i + 1) b
  | _, _, _, .iteB c t u => Term.occUnder i c + Body.occUnder i t + Body.occUnder i u
  | _, _, _, .joinPointB (params := ps) body rest =>
      Term.occ (i + ps.length) body + Body.occUnder (i + 1) rest

end

/-- Is a binding of `n` readers, `u` of them under a binder, one that shares something?
    It shares a value where two or more readers read it, and it keeps work out of a
    lambda or a loop where its single reader is under a binder. -/
def sharesOk (n u : Nat) : Bool := decide (2 ≤ n) || (n == 1 && u == 1)

/-! ## Is every binder of a list read? -/

/-- Are all `n` variables a binder just bound read in the term?  A binder that binds a
    list puts its parameters at de Bruijn indices `0 … n-1` of its body. -/
def paramsUsed {Sg : Sig} {Γ : Ctx} {τ : Ty} (n : Nat) (b : Term Sg Γ τ) : Bool :=
  (List.range n).all fun k => Term.occ k b != 0

/-- `paramsUsed`, for a binder whose body is a spine (`Term.lamProd`). -/
def paramsUsedSpine {Sg : Sig} {Γ : Ctx} {σs : List Ty} (n : Nat) (s : Spine Sg Γ σs) :
    Bool :=
  (List.range n).all fun k => Spine.occ k s != 0

/-! ### Reading a loop slot, as against handing it round

Every `Body.cont` of a block gives a value to *every* slot, so a slot that no iteration
reads still occurs once per jump — as the value it hands itself.  `Body.occSlotAt` is
`Body.occ` with that one argument of each jump left out, so a slot only carries itself is
a slot nothing reads, which is what `LakeJs.DeadSlot` drops and what the rule below
refuses. -/

mutual

/-- The occurrences of de Bruijn index `i` in a block, **not** counting the value each
    jump round the loop gives to slot `p`. -/
def Body.occSlotAt {Sg : Sig} (p : Nat) (i : Nat) :
    ∀ {Γ : Ctx} {σs : List Ty} {τ : Ty}, Body Sg Γ σs τ → Nat
  | _, _, _, .ret t => Term.occ i t
  | _, _, _, .cont args => Spine.occSkipAt p i args
  | _, _, _, .letB e b => Term.occ i e + Body.occSlotAt p (i + 1) b
  | _, _, _, .iteB c t u =>
      Term.occ i c + Body.occSlotAt p i t + Body.occSlotAt p i u
  | _, _, _, .joinPointB (params := ps) body rest =>
      Term.occ (i + ps.length) body + Body.occSlotAt p (i + 1) rest

/-- `Spine.occ`, with the `p`-th term of the spine left out. -/
def Spine.occSkipAt {Sg : Sig} (p : Nat) (i : Nat) :
    ∀ {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → Nat
  | _, _, .nil => 0
  | _, _, .cons t rest =>
      match p with
      | 0 => Spine.occ i rest
      | p + 1 => Term.occ i t + Spine.occSkipAt p i rest

end

/-- `paramsUsed`, for a binder whose body is a loop block (`Term.loop`).  Slot `p` of `n`
    is de Bruijn index `n - 1 - p` of the block, and the value the block hands *that*
    slot round the loop is not a read of it. -/
def paramsUsedBody {Sg : Sig} {Γ : Ctx} {σs : List Ty} {τ : Ty} (n : Nat)
    (b : Body Sg Γ σs τ) : Bool :=
  (List.range n).all fun k => Body.occSlotAt (n - 1 - k) k b != 0

/-! ## Which variables are join points

A mask runs parallel to the context: `true` at a variable a `Term.joinPoint` bound,
`false` at every other.  It is what tells a use of a join point as a value — which is
refused — from a jump to it, which is the only thing a join point is for. -/

/-- For each variable of the context, innermost first: was it bound by a join point? -/
abbrev JMask := List Bool

/-- Is the variable at de Bruijn index `i` a join point? -/
def JMask.isJoin (m : JMask) (i : Nat) : Bool := (m[i]?).getD false

/-- The mask under a binder that binds `n` ordinary variables. -/
def JMask.pushPlain (n : Nat) (m : JMask) : JMask := List.replicate n false ++ m

/-! ## The check -/

mutual

/-- Is every binder of this term read as often as it has to be, and is every join point
    of it used only as a jump target?  `m` says which variables of the context are join
    points. -/
def Term.usesOk {Sg : Sig} (m : JMask) : ∀ {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → Bool
  -- a join point is not a value: naming one anywhere but in a jump is refused
  | _, _, .var v => !m.isJoin v.index
  | _, _, .lit _ => true
  | _, _, .global _ => true
  | _, _, .extern _ => true
  | _, _, .lamN (params := ps) b =>
      paramsUsed ps.length b && Term.usesOk (JMask.pushPlain ps.length m) b
  | _, _, .apN f args => Term.usesOk m f && Spine.usesOk m args
  | _, _, .lamProd (params := ps) rets =>
      paramsUsedSpine ps.length rets && Spine.usesOk (JMask.pushPlain ps.length m) rets
  | _, _, .callProd f args _ => Term.usesOk m f && Spine.usesOk m args
  | _, _, .jsOp _ args => Spine.usesOk m args
  | _, _, .lazyMk e | _, _, .lazyForce e => Term.usesOk m e
  -- a `let` read once is not sharing anything, and one read not at all is dead
  | _, _, .letE e b =>
      sharesOk (Term.occ 0 b) (Term.occUnder 0 b) && Term.usesOk m e &&
        Term.usesOk (false :: m) b
  | _, _, .ite c t e => Term.usesOk m c && Term.usesOk m t && Term.usesOk m e
  | _, _, .ctor _ _ _ args => Spine.usesOk m args
  | _, _, .proj e _ _ _ => Term.usesOk m e
  | _, _, .tagOf e _ => Term.usesOk m e
  | _, _, .caseTag s alts _ => Term.usesOk m s && Alts.usesOk m alts
  | _, _, .loop (σs := σs) init body =>
      paramsUsedBody σs.length body && Spine.usesOk m init &&
        Body.usesOk (JMask.pushPlain σs.length m) body
  -- a join point has to be jumped to, and its own parameters read, like a function's
  | _, _, .joinPoint (params := ps) body rest =>
      paramsUsed ps.length body && decide (1 ≤ Term.occ 0 rest) &&
        Term.usesOk (JMask.pushPlain ps.length m) body && Term.usesOk (true :: m) rest
  -- and a jump goes to a join point, not to any other function the context holds
  | _, _, .jump v args => m.isJoin v.index && Spine.usesOk m args

/-- `Term.usesOk`, on every term of a spine. -/
def Spine.usesOk {Sg : Sig} (m : JMask) :
    ∀ {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → Bool
  | _, _, .nil => true
  | _, _, .cons t rest => Term.usesOk m t && Spine.usesOk m rest

/-- `Term.usesOk`, on every branch of a case. -/
def Alts.usesOk {Sg : Sig} (m : JMask) :
    ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat}, Alts Sg Γ τ tags → Bool
  | _, _, _, .deflt t => Term.usesOk m t
  | _, _, _, .cons _ t rest => Term.usesOk m t && Alts.usesOk m rest

/-- `Term.usesOk`, inside a loop block. -/
def Body.usesOk {Sg : Sig} (m : JMask) :
    ∀ {Γ : Ctx} {σs : List Ty} {τ : Ty}, Body Sg Γ σs τ → Bool
  | _, _, _, .ret t => Term.usesOk m t
  | _, _, _, .cont args => Spine.usesOk m args
  | _, _, _, .letB e b =>
      sharesOk (Body.occ 0 b) (Body.occUnder 0 b) && Term.usesOk m e &&
        Body.usesOk (false :: m) b
  | _, _, _, .iteB c t e => Term.usesOk m c && Body.usesOk m t && Body.usesOk m e
  -- a join point of a loop block, under the same rule as `Term.joinPoint`
  | _, _, _, .joinPointB (params := ps) body rest =>
      paramsUsed ps.length body && decide (1 ≤ Body.occ 0 rest) &&
        Term.usesOk (JMask.pushPlain ps.length m) body && Body.usesOk (true :: m) rest

end

/-- A term of the language that binds no name for nothing: every variable a function
    binds is read, every `let` shares its value with at least two readers, and every
    join point is jumped to and never used as a value. -/
def WfTerm (Sg : Sig) (Γ : Ctx) (τ : Ty) : Type :=
  { t : Term Sg Γ τ // Term.usesOk (List.replicate Γ.length false) t = true }

/-! ## Diagnosing a term the discipline refuses

`Term.usesOk` answers `false` and says nothing about why.  `Term.issues` runs the same
rules and collects one message per violation, which is what the compiler reports when it
refuses a declaration. -/

/-- The parameters of a binder that binds `n` variables at once and are never read. -/
def unreadParams {Sg : Sig} {G : Ctx} {t : Ty} (n : Nat) (b : Term Sg G t) : List Nat :=
  (List.range n).filter fun k => Term.occ k b == 0

/-- `unreadParams`, for a binder whose body is a spine (`Term.lamProd`). -/
def unreadParamsSpine {Sg : Sig} {G : Ctx} {ss : List Ty} (n : Nat) (s : Spine Sg G ss) :
    List Nat :=
  (List.range n).filter fun k => Spine.occ k s == 0

/-- `unreadParams`, for a binder whose body is a loop block (`Term.loop`). -/
def unreadParamsBody {Sg : Sig} {G : Ctx} {ss : List Ty} {t : Ty} (n : Nat)
    (b : Body Sg G ss t) : List Nat :=
  (List.range n).filter fun k => Body.occSlotAt (n - 1 - k) k b == 0

/-- One message per parameter of a binder that nothing reads. -/
def paramMsgs (what : String) (ks : List Nat) : List String :=
  ks.map fun k => s!"{what} never reads the variable it binds at position {k}"

mutual

/-- Every reason `Term.usesOk` refuses this term, innermost binder last.  `strict` says
    whether the parameters of a **function** are checked too: they are part of its type,
    hence of the calling convention its callers keep to, so the compiler reports an
    unread one rather than refusing it — see `Term.declIssues`. -/
def Term.issues {Sg : Sig} (strict : Bool) (m : JMask) :
    ∀ {Γ : Ctx} {τ : Ty}, Term Sg Γ τ → List String
  | _, _, .var v =>
      if m.isJoin v.index then
        [s!"the join point at index {v.index} is named as a value rather than jumped to"]
      else []
  | _, _, .lit _ => []
  | _, _, .global _ => []
  | _, _, .extern _ => []
  | _, _, .lamN (params := ps) b =>
      (if strict then paramMsgs "a function" (unreadParams ps.length b) else []) ++
        Term.issues strict (JMask.pushPlain ps.length m) b
  | _, _, .apN f args => Term.issues strict m f ++ Spine.issues strict m args
  | _, _, .lamProd (params := ps) rets =>
      (if strict then paramMsgs "a function" (unreadParamsSpine ps.length rets)
        else []) ++
        Spine.issues strict (JMask.pushPlain ps.length m) rets
  | _, _, .callProd f args _ => Term.issues strict m f ++ Spine.issues strict m args
  | _, _, .jsOp _ args => Spine.issues strict m args
  | _, _, .lazyMk e | _, _, .lazyForce e => Term.issues strict m e
  | _, _, .letE e b =>
      (if sharesOk (Term.occ 0 b) (Term.occUnder 0 b) then [] else
        [s!"a `let` is read {Term.occ 0 b} time(s), none of them under a binder, so it \
          shares nothing"]) ++
        Term.issues strict m e ++ Term.issues strict (false :: m) b
  | _, _, .ite c t e =>
      Term.issues strict m c ++ Term.issues strict m t ++ Term.issues strict m e
  | _, _, .ctor _ _ _ args => Spine.issues strict m args
  | _, _, .proj e _ _ _ => Term.issues strict m e
  | _, _, .tagOf e _ => Term.issues strict m e
  | _, _, .caseTag s alts _ => Term.issues strict m s ++ Alts.issues strict m alts
  | _, _, .loop (σs := σs) init body =>
      paramMsgs "a loop" (unreadParamsBody σs.length body) ++
        Spine.issues strict m init ++
        Body.issues strict (JMask.pushPlain σs.length m) body
  | _, _, .joinPoint (params := ps) body rest =>
      paramMsgs "a join point" (unreadParams ps.length body) ++
        (if Term.occ 0 rest = 0 then ["a join point is never jumped to"] else []) ++
        Term.issues strict (JMask.pushPlain ps.length m) body ++
        Term.issues strict (true :: m) rest
  | _, _, .jump v args =>
      (if m.isJoin v.index then []
        else [s!"a jump goes to index {v.index}, which is not a join point"]) ++
        Spine.issues strict m args

/-- `Term.issues`, on every term of a spine. -/
def Spine.issues {Sg : Sig} (strict : Bool) (m : JMask) :
    ∀ {Γ : Ctx} {σs : List Ty}, Spine Sg Γ σs → List String
  | _, _, .nil => []
  | _, _, .cons t rest => Term.issues strict m t ++ Spine.issues strict m rest

/-- `Term.issues`, on every branch of a case. -/
def Alts.issues {Sg : Sig} (strict : Bool) (m : JMask) :
    ∀ {Γ : Ctx} {τ : Ty} {tags : List Nat}, Alts Sg Γ τ tags → List String
  | _, _, _, .deflt t => Term.issues strict m t
  | _, _, _, .cons _ t rest => Term.issues strict m t ++ Alts.issues strict m rest

/-- `Term.issues`, inside a loop block. -/
def Body.issues {Sg : Sig} (strict : Bool) (m : JMask) :
    ∀ {Γ : Ctx} {σs : List Ty} {τ : Ty}, Body Sg Γ σs τ → List String
  | _, _, _, .ret t => Term.issues strict m t
  | _, _, _, .cont args => Spine.issues strict m args
  | _, _, _, .letB e b =>
      (if sharesOk (Body.occ 0 b) (Body.occUnder 0 b) then [] else
        [s!"a `let` of a loop block is read {Body.occ 0 b} time(s), none of them under a \
          binder, so it shares nothing"]) ++
        Term.issues strict m e ++ Body.issues strict (false :: m) b
  | _, _, _, .iteB c t e =>
      Term.issues strict m c ++ Body.issues strict m t ++ Body.issues strict m e
  | _, _, _, .joinPointB (params := ps) body rest =>
      paramMsgs "a join point" (unreadParams ps.length body) ++
        (if Body.occ 0 rest = 0 then ["a join point of a loop block is never jumped to"]
          else []) ++
        Term.issues strict (JMask.pushPlain ps.length m) body ++
        Body.issues strict (true :: m) rest

end

/-! ## The discipline of a whole declaration

The parameters of a function are its **calling convention**, and the arity is part of
the type `.fn params ret` the function has: a declaration the module exports is called
from outside with that many arguments, and a lambda handed to a higher-order function is
called by *it* with that many.  Dropping a parameter nothing reads would therefore change
a type, which is not something an optimiser of one module may do — so an unread function
parameter is **reported** (`LakeJs.Compile.Result.unusedParams`) rather than refused.

Every other binder is one the *backend itself* chose: the slots of a `Term.loop` and the
parameters of a `Term.joinPoint` belong to no type, so the compiler refuses one that
nothing reads, as it refuses a `let` that shares nothing and a join point that is never
jumped to.  `Term.usesOkDecl` is that discipline, and `Term.declIssues` its diagnosis. -/

/-- The reasons a declaration's term fails the discipline the compiler enforces: the
    parameters of a function are its calling convention, so they are not checked; a loop
    slot, a join point and a `let` are. -/
def Term.declIssues {Sg : Sig} {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ) : List String :=
  Term.issues false (List.replicate Γ.length false) t

/-- Does a declaration's term meet the discipline the compiler enforces? -/
def Term.usesOkDecl {Sg : Sig} {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ) : Bool :=
  (Term.declIssues t).isEmpty

/-- Every unread *function* parameter of a declaration: what the compiler reports rather
    than refuses. -/
def Term.paramNotes {Sg : Sig} {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ) : List String :=
  (Term.issues true (List.replicate Γ.length false) t).filter fun s =>
    !(Term.declIssues t).contains s

/-! ## What the discipline refuses -/

/-- **A function whose body ignores one of its parameters is refused.** -/
theorem Term.not_usesOk_lamN_of_unusedParam {Sg : Sig} {Γ : Ctx} {ps : List Ty} {ret : Ty}
    {b : Term Sg (ps.reverse ++ Γ) ret} (m : JMask) {k : Nat} (hk : k < ps.length)
    (h : Term.occ k b = 0) : Term.usesOk m (.lamN (params := ps) b) = false := by
  have : paramsUsed ps.length b = false := by
    simp [paramsUsed]
    exact ⟨k, hk, h⟩
  simp [Term.usesOk, this]

/-- **A `let` nothing reads is refused.** -/
theorem Term.not_usesOk_letE_of_dead {Sg : Sig} {Γ : Ctx} {σ τ : Ty}
    {e : Term Sg Γ σ} {b : Term Sg (σ :: Γ) τ} (m : JMask) (h : Term.occ 0 b = 0) :
    Term.usesOk m (.letE e b) = false := by
  simp [Term.usesOk, sharesOk, h]

/-- **A `let` read once, where that read is not under a binder, is refused**: read twice
    it shares a value, read once out in the open the value belongs where it is read. -/
theorem Term.not_usesOk_letE_of_readOnce {Sg : Sig} {Γ : Ctx} {σ τ : Ty}
    {e : Term Sg Γ σ} {b : Term Sg (σ :: Γ) τ} (m : JMask) (h : Term.occ 0 b = 1)
    (hu : Term.occUnder 0 b = 0) : Term.usesOk m (.letE e b) = false := by
  simp [Term.usesOk, sharesOk, h, hu]

/-- **A join point nothing jumps to is refused.** -/
theorem Term.not_usesOk_joinPoint_of_noJump {Sg : Sig} {Γ : Ctx} {ps : List Ty} {σ τ : Ty}
    {body : Term Sg (ps.reverse ++ Γ) σ} {rest : Term Sg (.fn ps σ :: Γ) τ} (m : JMask)
    (h : Term.occ 0 rest = 0) : Term.usesOk m (.joinPoint body rest) = false := by
  simp [Term.usesOk]
  omega

/-- **A join point of a loop block that nothing jumps to is refused.** -/
theorem Body.not_usesOk_joinPointB_of_noJump {Sg : Sig} {Γ : Ctx} {ps : List Ty}
    {σ τ : Ty} {σs : List Ty} {body : Term Sg (ps.reverse ++ Γ) σ}
    {rest : Body Sg (.fn ps σ :: Γ) σs τ} (m : JMask) (h : Body.occ 0 rest = 0) :
    Body.usesOk m (.joinPointB body rest) = false := by
  simp [Body.usesOk]
  omega

/-- **A join point used as a value is refused**: naming one anywhere but as the target of
    a jump would make it escape, and a join point that escapes is a closure. -/
theorem Term.not_usesOk_var_of_join {Sg : Sig} {Γ : Ctx} {τ : Ty} {v : Γ ∋ τ} (m : JMask)
    (h : m.isJoin v.index = true) : Term.usesOk (Sg := Sg) m (.var v) = false := by
  simp [Term.usesOk, h]

/-- **A jump to a variable that is not a join point is refused.** -/
theorem Term.not_usesOk_jump_of_notJoin {Sg : Sig} {Γ : Ctx} {ps : List Ty} {σ : Ty}
    {v : Γ ∋ (.fn ps σ)} {args : Spine Sg Γ ps} (m : JMask)
    (h : m.isJoin v.index = false) : Term.usesOk m (.jump v args) = false := by
  simp [Term.usesOk, h]

/-! ## Examples

`Term.id` is the smallest term the discipline accepts, and `Term.const` the smallest one
it refuses: `ƛ ƛ ♯1` binds a variable its body never names. -/

example {Sg : Sig} {τ : Ty} : Term.usesOk [] (Term.id (Sg := Sg) (τ := τ)) = true := rfl

example {Sg : Sig} {τ1 τ2 : Ty} :
    Term.usesOk [] (Term.const (Sg := Sg) (τ1 := τ1) (τ2 := τ2)) = false := rfl

/-- A join point of one parameter, jumped to from both arms of a conditional: the
    shared tail that a join point exists for. -/
def joinExample : Term [] [] Ty.nat :=
  .joinPoint (params := [Ty.nat]) (σ := Ty.nat)
    (.apN (.extern .lean_nat_add) (.cons (♯0) (.cons (♯0) .nil)))
    (.ite (.lit (.bool true))
      (.jump .head (.cons (.lit (.nat 1)) .nil))
      (.jump .head (.cons (.lit (.nat 2)) .nil)))

example : Term.usesOk [] joinExample = true := by decide +kernel

/-- The same join point, named as a value rather than jumped to: refused. -/
def escapingJoinExample : Term [] [] (Ty.fn [Ty.nat] Ty.nat) :=
  .joinPoint (params := [Ty.nat]) (σ := Ty.nat)
    (.apN (.extern .lean_nat_add) (.cons (♯0) (.cons (♯0) .nil)))
    (♯0)

example : Term.usesOk [] escapingJoinExample = false := by decide +kernel

end LakeJs.Usage
