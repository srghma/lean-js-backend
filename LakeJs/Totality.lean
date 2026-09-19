import Lean
import Lean.Compiler.LCNF

/-!
# Refusing what the backend must not compile

The target of this backend is JavaScript whose only repetition is a `while`/`for` loop.
A loop is a faithful translation of a Lean function *only* if the function is total: a
`partial def` may never come back, and neither may an `unsafe` one, so there is no
number of iterations that is the right one to print.  A declaration that does IO is out
for a different reason — the language the backend compiles is pure.

So the compiler starts by refusing:

* a **`partial def`** of a module being compiled, and any of its `where` / `let rec`
  helpers or specializations — Lean did not prove it terminating;
* an **`unsafe def`** of a module being compiled, for the same reason;
* a declaration whose type is an **IO** type (`IO`, `EIO`, `BaseIO`, `ST`, `EST`,
  `EStateM`) — an impure entry point;
* a declaration with **no body to read**: an `opaque`, or one implemented by `@[extern]`
  in C rather than in Lean.

Two refinements matter in practice.

*Dependencies of other modules.*  Lean's own library implements several *proved total*
functions by an `unsafe` loop — `Array.mapM` is `Array.mapMUnsafe.map` — and hands the
backend a specialization of that loop.  Refusing every `unsafe` LCNF declaration would
therefore refuse `(a.map f)`, whose source is total.  What is refused outside the
modules being compiled is a declaration whose *origin* Lean itself marks `partial`:
that one really can diverge.

*Where the blame goes.*  A rejection names the declaration that caused it and the root
that reached it, so the message points at the user's `def` rather than at a compiler
generated helper twelve calls down.
-/

namespace LakeJs.Totality

open Lean Lean.Compiler.LCNF

/-- Why one declaration was refused. -/
structure Rejection where
  /-- The declaration that is not compilable. -/
  name : Name
  /-- The root declaration whose call graph reached it, when it is not the root itself. -/
  via : Option Name := none
  /-- What is wrong with it, in one sentence. -/
  reason : String
  deriving Repr, Inhabited

/-- The message the compiler prints for a rejection. -/
def Rejection.message (r : Rejection) : String :=
  let at_ := match r.via with
    | some v => s!" (reached from `{v}`)"
    | none => ""
  s!"`{r.name}`{at_}: {r.reason}"

/-- Where a compiler-generated specialization comes from: `A._at_.B.spec_0` is a
    specialization of `A`, and a name with no `_at_` component is its own origin. -/
def specializationOrigin (n : Name) : Name :=
  let cs := n.components
  match cs.findIdx? (· == `_at_) with
  | some i => (cs.take i).foldl (· ++ ·) Name.anonymous
  | none => n

/-- Where the recursion of `n` is recorded.  A compiler-generated specialization of a
    library loop — `Std.Legacy.Range.forIn'.loop._at_.test1.spec_0` — has no
    `ConstantInfo` and no equation info of its own: what says how it recurses is the
    record Lean kept for the declaration it was specialized from. -/
def recInfoSource (env : Environment) (n : Name) : Name :=
  if (env.find? n).isSome then n else specializationOrigin n

/-- The head constant of a type, after all its parameters. -/
private def resultHead (type : Expr) : Option Name :=
  match type with
  | .forallE _ _ body _ => resultHead body
  | e => e.getAppFn.constName?

/-- The monads whose values are not pure. -/
private def ioHeads : List Name :=
  [``IO, ``EIO, ``BaseIO, ``ST, ``EST, ``EStateM, ``IO.Ref, ``ST.Ref]

/-- Does this type describe a computation in an IO-like monad? -/
def isIOType (type : Expr) : Bool :=
  match resultHead type with
  | some n => ioHeads.contains n
  | none => false

/-- Is `n` a declaration of one of the modules being compiled? -/
def isLocalTo (env : Environment) (moduleIdxs : Array Nat) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => moduleIdxs.contains idx.toNat
  | none => true -- declared in the current file rather than imported

/-- What is wrong with `n`, if anything.  `local?` says whether `n` belongs to a module
    being compiled, which is what decides how an `unsafe` implementation is read. -/
def classify (env : Environment) (local? : Bool) (n : Name) : Option String :=
  match env.find? n with
  | none =>
    -- A helper the compiler generated for itself, such as a specialization of a
    -- library loop: it has no `ConstantInfo` of its own, so it is judged by the
    -- declaration it was generated from.
    let origin := specializationOrigin n
    if origin == n then none
    else
      match env.find? origin with
      | some (.defnInfo ov) =>
        if ov.safety == .partial then
          some s!"it is a specialization of the `partial def` `{origin}`"
        else if ov.safety == .unsafe then
          some s!"it is a specialization of the `unsafe def` `{origin}`, which Lean did \
                  not prove terminating; the backend cannot turn it into a loop"
        else none
      | _ => none
  | some ci =>
    if isIOType ci.type then
      some "its type is an IO type; the backend compiles pure functions only"
    else
      match ci with
      | .defnInfo dv =>
        match dv.safety with
        | .partial =>
          some "it is a `partial def`, so Lean did not prove it terminating; \
                the backend cannot turn it into a loop"
        | .unsafe =>
          -- An `unsafe def` is one of the four kinds of definition `Term` cannot
          -- represent, wherever it was written: Lean did not prove it terminating, so
          -- there is no number of iterations a loop could be given.  Lean's own total
          -- functions that are *implemented* by an `unsafe` loop are reached through
          -- `coreModelOf?`, which compiles the definition the source gives them instead.
          some "it is an `unsafe def`, so Lean did not prove it terminating; \
                the backend cannot turn it into a loop"
        | .safe => none
      | .opaqueInfo _ =>
        -- A `partial def` is stored as an `opaque` constant with an `unsafe`
        -- implementation beside it; that is the shape to refuse.
        if env.contains (n ++ `_unsafe_rec) then
          some "it is a `partial def`, so Lean did not prove it terminating; \
                the backend cannot turn it into a loop"
        else if local? then
          some "it is `opaque`, so there is no body to compile"
        else
          -- An `opaque` of the standard library is a primitive of the runtime, such as
          -- `String.hash`: it has no Lean body because it is implemented by the
          -- platform, not because it might not terminate.
          none
      | .axiomInfo _ =>
        some "it is an axiom, so there is no body to compile"
      | _ => none

/-! ## Which kind of recursion Lean used

Lean's reference manual lists six kinds of recursive definition.  `Term` can represent the
first two and only those, so the front end classifies a declaration **positively**: it
looks for the evidence that Lean elaborated it structurally or by well-founded recursion,
and refuses anything else rather than assuming it is fine.

* structural recursion leaves a `Lean.Elab.Structural.EqnInfo`, which also records
  `recArgPos`, the argument the recursion is on — the one `Term.structRank` measures;
* well-founded recursion leaves a `Lean.Elab.WF.EqnInfo`, whose `termination_by` measure
  the front end transcribes as the measure;
* a partial fixpoint leaves a `Lean.Elab.PartialFixpoint.EqnInfo`, and is refused;
* `partial` and `unsafe` are refused by `classify` above;
* an inductive or coinductive fixpoint is a `Prop`-valued declaration with no compilable
  body, so it never reaches a `Term` at all.
-/

/-- How Lean elaborated a declaration's recursion, when the backend can represent it. -/
inductive RecKind where
  /-- Not recursive: no fixpoint of any sort. -/
  | nonRecursive
  /-- Structurally recursive on argument `recArgPos`, in the mutual clique `clique`. -/
  | structural (recArgPos : Nat) (clique : Array Name)
  /-- Recursive over a well-founded relation, in the mutual clique `clique`. -/
  | wellFounded (clique : Array Name)
  deriving Repr, Inhabited

/-- The kind of recursion Lean used for `n`, or the reason the backend refuses it.  This
    is a **whitelist**: a strategy that is not one of the two admitted ones has no branch
    that accepts it. -/
def recKind? (env : Environment) (n : Name) : Except String RecKind :=
  if let some info := Lean.Elab.Structural.eqnInfoExt.find? env n then
    .ok (.structural info.recArgPos info.declNames)
  else if let some info := Lean.Elab.WF.eqnInfoExt.find? env n then
    .ok (.wellFounded info.declNames)
  else if (Lean.Elab.PartialFixpoint.eqnInfoExt.find? env n).isSome then
    .error "it is defined as a partial fixpoint (`partial_fixpoint`); the backend \
            represents structural and well-founded recursion only"
  else
    .ok .nonRecursive

/-! ## The core functions whose Lean body is read from a model

A few of Lean's own total functions carry `@[extern]`, so the compiled module stores no
LCNF body for them. `LakeJs.CoreModels` writes those bodies out as ordinary Lean
definitions, with the termination proof Lean's own source gives them, and this table says
which model stands in for which name. A function reached through it is compiled exactly
like a function of the module being compiled — the `@[extern]` implementation is the only
thing that is ignored. -/

/-- The Lean-source model of a core function that is implemented by `@[extern]`. -/
def coreModelOf? (n : Name) : Option Name :=
  if n == ``Nat.gcd then some `LakeJs.CoreModels.natGcd
  else if n == ``Array.append then some `LakeJs.CoreModels.arrayAppend
  else if n == ``String.Pos.Raw.atEnd then some `LakeJs.CoreModels.posAtEnd
  else if n == ``String.Pos.Raw.next then some `LakeJs.CoreModels.posNext
  else if n == ``instDecidableEqChar then some `LakeJs.CoreModels.charEq
  else if n == ``String.ofList then some `LakeJs.CoreModels.stringOfList
  else if n == ``Array.toList then some `LakeJs.CoreModels.arrayToList
  else none

/-- The declaration whose body stands for `n`: `n` itself, unless a model stands in. -/
def resolveModel (n : Name) : Name := (coreModelOf? n).getD n

/-- The rejection `recKind?` produces, if any. -/
def classifyRecursion (env : Environment) (n : Name) : Option String :=
  match recKind? env n with
  | .ok _ => none
  | .error reason => some reason

/-- The declarations a piece of LCNF code calls. -/
partial def usedDecls (code : Code) (s : NameSet := {}) : NameSet :=
  match code with
  | .let decl k => usedDecls k (letValueDecls decl.value s)
  | .jp decl k | .fun decl k => usedDecls decl.value (usedDecls k s)
  | .cases c =>
    c.alts.foldl (init := s) fun s alt =>
      match alt with
      | .default k => usedDecls k s
      | .alt _ _ k => usedDecls k s
  | _ => s
where
  letValueDecls (e : LetValue) (s : NameSet) : NameSet :=
    match e with
    | .const declName .. => s.insert declName
    | _ => s

/-- Walk the call graph of `roots` through the `saveBase` LCNF phase and collect every
    reason the modules cannot be compiled.  An empty array means the backend may go
    ahead. -/
def check (moduleIdxs : Array Nat) (roots : Array Name) : CoreM (Array Rejection) := do
  let env ← getEnv
  let mut rejections : Array Rejection := #[]
  let mut seen : NameSet := {}
  let mut todo : List (Name × Option Name) := roots.toList.map (·, none)
  while !todo.isEmpty do
    let (n, via) := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let local? := isLocalTo env moduleIdxs n
    if let some reason := classify env local? n <|> classifyRecursion env (resolveModel n) then
      rejections := rejections.push { name := n, via := via, reason := reason }
      continue
    match ← getBaseDecl? (resolveModel n) with
    | none =>
      if (env.find? n).isNone then
        rejections := rejections.push
          { name := n, via := via
            reason := "no declaration of this name was found in the compiled modules" }
    | some d =>
      match d.value with
      | .extern _ =>
        -- Outside the modules being compiled, an `@[extern]` declaration is a runtime
        -- primitive; inside them it is a body the backend cannot read.
        if local? then
          rejections := rejections.push
            { name := n, via := via
              reason := "it is implemented by `@[extern]`, so there is no Lean body to compile" }
      | .code c =>
        for callee in usedDecls c do
          if !seen.contains callee then
            todo := (callee, some (via.getD n)) :: todo
  return rejections

end LakeJs.Totality
