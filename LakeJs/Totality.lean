module

public import Lean
public import Lean.Compiler.LCNF

@[expose] public section

namespace LakeJs.Totality

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

/-- The head constant of a type, after all its parameters. -/
def resultHead (type : Expr) : Option Name :=
  match type with
  | .forallE _ _ body _ => resultHead body
  | e => e.getAppFn.constName?

/-- The monads whose values are not pure. -/
def ioHeads : List Name :=
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
          if local? then
            some "it is an `unsafe def`, so Lean did not prove it terminating; \
                  the backend cannot turn it into a loop"
          else
            -- Lean's own total functions are sometimes implemented by an `unsafe`
            -- loop; the declaration the user wrote does have a termination proof.
            let origin := specializationOrigin n
            match env.find? origin with
            | some (.defnInfo ov) =>
              if ov.safety == .partial then
                some s!"it is a specialization of the `partial def` `{origin}`"
              else none
            | _ => none
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
    if let some reason := classify env local? n then
      rejections := rejections.push { name := n, via := via, reason := reason }
      continue
    match ← getBaseDecl? n with
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
