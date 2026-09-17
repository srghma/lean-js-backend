import LakeJs.FromLcnf
import LakeJs.Scalarise
import LakeJs.Specialise
import LakeJs.Inline
import LakeJs.TermPretty

/-!
# The driver: an `.olean` in, a `.js` file out

`compileModule` is the whole pipeline:

1. import the module, so that what Lean stored for it is available;
2. refuse it if it must not be compiled (`LakeJs.Totality`) — a `partial def`, an
   `unsafe def`, an IO entry point or a body Lean never proved terminating stops the
   compilation with an error naming the declaration;
3. read the `saveBase` LCNF phase of every declaration of the module, and of every
   declaration of theirs that they call;
4. work out the **signature** of the module — every top-level name the emitted
   JavaScript binds or imports, with its type — because a `Term` can only refer to a
   declaration of the signature it is written against;
5. translate each declaration into a `Term` (`LakeJs.FromLcnf`), turning a
   tail-recursive declaration into a `Term.loop`, unboxing each class instance into one
   declaration per field, and simplifying the result (`LakeJs.Simp`);
6. print it with `MiniAST` (`LakeJs.EmitJs`).
-/

namespace LakeJs.Compile

open LakeJs
open LakeJs.Ty
open LakeJs.Layout (FieldLayout ObjLayout)
open LakeJs.Expr
open LakeJs.Lookup
open LakeJs.Rename
open LakeJs.Simp
open LakeJs.Inline
open LakeJs.Scalarise
open LakeJs.Specialise
open LakeJs.EmitJs
open LakeJs.FromLcnf
open LakeJs.TermPretty

/-- Everything the backend does to a translated declaration before it is printed:
    simplify, inline the calls of the declarations of `tbl` (`LakeJs.Inline`), simplify
    what inlining exposed, scalarise the accumulators of its loops, and simplify again —
    the last pass is what collapses the projections scalarising leaves behind.  Every
    one of them is a function `Term Sg Γ τ → Term Sg Γ τ`, so none of it can produce a
    program that is not well-typed. -/
def optimise {Sg : Sig} {τ : Ty} (tbl : LakeJs.Inline.Table Sg) (t : Term Sg [] τ) :
    Term Sg [] τ :=
  let t1 := LakeJs.Simp.Term.simpAll t
  let t2 :=
    if tbl.isEmpty then t1
    else LakeJs.Simp.Term.simpAll (LakeJs.Inline.Term.inlineCalls tbl t1)
  LakeJs.Simp.Term.simpAll (LakeJs.Scalarise.scalarise t2)

/-- What a translated declaration is put through before it is printed.  The driver runs
    the translation twice: once with `optimised`, whose result is the emitted JavaScript,
    and once with `unoptimised`, whose result is the term `<Module>-Expr.txt` holds. -/
abbrev Post (Sg : Sig) := (τ : Ty) → Term Sg [] τ → Term Sg [] τ

/-- The term as the translation produced it. -/
def unoptimised {Sg : Sig} : Post Sg := fun _ t => t

/-- The term the optimiser produces, with `tbl` the declarations a call of which may be
    inlined. -/
def optimised {Sg : Sig} (tbl : LakeJs.Inline.Table Sg) : Post Sg := fun _ t => optimise tbl t

/-- How big a declaration's body may be for the backend to inline a call of it where
    Lean itself said nothing about the declaration.  A declaration Lean marked
    `@[inline]` is inlined whatever its size. -/
def inlineSizeLimit : Nat := 24

open Lean Lean.Compiler.LCNF
open LakeJs.FromLcnf
open LakeJs.EmitJs

/-- Does this block end in a call to one of `targets` that is its own answer?  That,
    and only that, is what becomes the `continue` of a loop. -/
partial def hasTailCallTo (targets : Name → Bool) : Code → Bool
  | .let d k =>
      (match d.value, k with
       | .const n _ _, .return r => targets n && r == d.fvarId
       | _, _ => false) || hasTailCallTo targets k
  | .fun _ k => hasTailCallTo targets k
  | .jp d k => hasTailCallTo targets d.value || hasTailCallTo targets k
  | .cases c => c.alts.any fun a =>
      match a with
      | .alt _ _ k => hasTailCallTo targets k
      | .default k => hasTailCallTo targets k
  | _ => false

/-- Does this block tail-call the declaration it belongs to? -/
def hasTailSelfCall (self : Name) (code : Code) : Bool :=
  hasTailCallTo (· == self) code

/-- Every declaration a block calls. -/
partial def calledDecls (code : Code) : NameSet := LakeJs.Totality.usedDecls code {}

/-! ## What a block mentions

The signature of the module has to be known before anything is translated, so the names
a block mentions — every constant it calls, whether or not the module declares it — are
collected first. -/

/-- Every constant a `LetValue` mentions. -/
def constsOfValue : LetValue → NameSet → NameSet
  | .const n _ _, s => s.insert n
  | _, s => s

/-- Every constant a block mentions. -/
partial def constsOfCode (code : Code) (s : NameSet) : NameSet :=
  match code with
  | .let d k => constsOfCode k (constsOfValue d.value s)
  | .fun d k | .jp d k => constsOfCode k (constsOfCode d.value s)
  | .cases c => c.alts.foldl (init := s) fun s a => constsOfCode a.getCode s
  | _ => s

/-! ## The free variables of a block, and the bindings it does not need

Unboxing an instance means keeping one field of the value a declaration builds and
throwing the rest of its body away.  What is left is a block full of bindings nothing
reads any more, so they are dropped here rather than printed. -/

/-- Every free variable an argument mentions. -/
def usedOfArg : Arg → Std.HashSet FVarId → Std.HashSet FVarId
  | .fvar f, s => s.insert f
  | _, s => s

/-- Every free variable a `LetValue` mentions. -/
def usedOfValue : LetValue → Std.HashSet FVarId → Std.HashSet FVarId
  | .proj _ _ f, s => s.insert f
  | .fvar f args, s => args.foldl (init := s.insert f) fun s a => usedOfArg a s
  | .const _ _ args, s => args.foldl (init := s) fun s a => usedOfArg a s
  | _, s => s

/-- Every free variable a block mentions. -/
partial def usedOfCode (code : Code) (s : Std.HashSet FVarId) : Std.HashSet FVarId :=
  match code with
  | .let d k => usedOfCode k (usedOfValue d.value s)
  | .fun d k | .jp d k => usedOfCode k (usedOfCode d.value s)
  | .jmp f args => args.foldl (init := s.insert f) fun s a => usedOfArg a s
  | .cases c => c.alts.foldl (init := s.insert c.discr) fun s a => usedOfCode a.getCode s
  | .return f => s.insert f
  | .unreach _ => s

/-- Drop the bindings of a block that nothing downstream reads.  Everything the source
    language can express is pure, so a binding nobody reads can go. -/
partial def dropDeadLets (code : Code) : Code :=
  match code with
  | .let d k =>
      let k' := dropDeadLets k
      if (usedOfCode k' {}).contains d.fvarId then .let d k' else k'
  | .fun d k =>
      let k' := dropDeadLets k
      if (usedOfCode k' {}).contains d.fvarId then .fun d k' else k'
  | c => c

/-- The block that answers with the `i`-th field of the value this one builds.  It is
    the same block, returning the field the constructor was given instead of the
    constructor's result; `none` when the block does not end in a constructor
    application, which is when the instance has to be built and projected instead. -/
partial def instFieldCode? (binds : Std.HashMap FVarId LetValue) (i : Nat) : Code → Option Code
  | .let d k => (instFieldCode? (binds.insert d.fvarId d.value) i k).map (Code.let d)
  | .fun d k => (instFieldCode? binds i k).map (Code.fun d)
  | .return x =>
      match binds[x]? with
      | some (.const _ _ args) =>
          match (args.toList.filter (!isErasedArgForm ·))[i]? with
          | some (.fvar f) => some (.return f)
          | _ => none
      | _ => none
  | _ => none

/-! ## Class instances

A declaration whose result is a class is not a record in the output: it is one
declaration per field.  What the fields are is read off the class's structure. -/

/-- Strip `n` leading `∀` binders off a type expression, without touching a local
    context: what is left may mention the binders, which the backend reads as opaque
    runtime values anyway. -/
def stripForall : Nat → Expr → Expr
  | 0, e => e
  | n + 1, .forallE _ _ b _ => stripForall n b
  | _, e => e

/-- The fields a value of this type is unboxed into, if it is a class the backend
    unboxes: a structure class with at least one field that survives to run time.

    Only the *class* is read off the type given here; the fields are read off the class's
    own constructor, which is a closed declaration, so this works on an LCNF type whose
    free variables belong to a declaration's parameters rather than to any local
    context. -/
def instPlanOfType? (ty : Expr) : MetaM (Option InstPlan) := do
  let env ← getEnv
  let ret := ty.getAppFn
  let some cls := ret.constName? | return none
  if !Lean.isClass env cls then return none
  if !Lean.isStructure env cls then return none
  let ctor := Lean.getStructureCtor env cls
  let fieldNames := Lean.getStructureFields env cls
  let some ctorInfo := env.find? ctor.name | return none
  let fields ← Meta.forallTelescopeReducing ctorInfo.type fun bs _ => do
    let fs := bs.toList.drop ctor.numParams
    let mut out : List (String × Ty) := []
    for f in fs, nm in fieldNames.toList do
      let fty ← Meta.inferType f
      -- a proof or a type carries nothing at run time, and LCNF has already dropped it
      if (← Meta.isProp fty) || fty.isSort then continue
      let some t := (toTy env (← instantiateMVars fty)).toOption | continue
      out := out ++ [(nm.toString, t)]
    return out
  if fields.isEmpty then return none
  return some { fields := fields }

/-- The fields the *result* of this declaration is unboxed into. -/
def instPlanOfDecl? (d : Decl) : MetaM (Option InstPlan) := do
  let ret := stripForall d.params.size d.type
  instPlanOfType? ret

/-- How each parameter of a declaration is passed: on its own, or as the fields of an
    instance. -/
def paramPlanOfDecl (d : Decl) : MetaM (List (Option InstPlan)) :=
  d.params.toList.mapM fun p => instPlanOfType? p.type

/-! ## Parameters

A parameter whose type is an unboxed class is several parameters — one per field — so
the list of parameters the JavaScript function takes is not the list of parameters the
Lean declaration has. -/

/-- The parameters the emitted function takes, and where each Lean parameter went.
    `base` is the depth the first parameter sits at. -/
def expandParams (base : Nat) :
    List (Option InstPlan) → List Param → List (Option Ty) →
      List Ty × List (FVarId × Binding)
  | _, [], _ => ([], [])
  | plans, p :: ps, ptys =>
    -- a dropped parameter has no type, and no JavaScript parameter either
    let pty := (ptys.headD none).getD (.enum 1 (shift := 0))
    let rest := ptys.tail
    let plan := plans.headD none
    let plans' := plans.tail
    if isErasedParam p then
      -- a type or a proof: no JavaScript parameter at all
      let (tys, bs) := expandParams base plans' ps rest
      (tys, (p.fvarId, .erased) :: bs)
    else
    match plan with
    | none =>
      let (tys, bs) := expandParams (base + 1) plans' ps rest
      (pty :: tys, (p.fvarId, .one base) :: bs)
    | some ip =>
      let k := ip.size
      let (tys, bs) := expandParams (base + k) plans' ps rest
      (ip.tys ++ tys, (p.fvarId, .split ip ((List.range k).map (base + ·))) :: bs)

/-- The `Ty` of each parameter, in order, with `none` for a parameter that is dropped —
    a type or a proof — so that the list stays parallel to the LCNF parameters. -/
def paramTys (env : Environment) (ps : List Param) : Except String (List (Option Ty)) :=
  ps.mapM fun p => if isErasedParam p then pure none else do return some (← toTy env p.type)

/-- How many parameters of a declaration survive to run time: the arrows its `Ty`
    has. -/
def runtimeParamCount (ps : List Param) : Nat := (ps.filter (!isErasedParam ·)).length

/-! ## Mutually recursive groups

A group of declarations that call one another is compiled into **one** JavaScript
function with a dispatch loop, and one wrapper per member that enters it:

```js
const _mut$test1 = (v0, v1) => { let … while (c) { if (tag === 0) { … } else { … } } };
const test1 = (v0) => _mut$test1(0, v0);
const test2 = (v0) => _mut$test1(1, v0);
```

The loop's variables are the tag of the member that is running and one slot per
argument — as many slots as the widest member has parameters.  A tail call to *any*
member of the group is then a `Body.cont` of that one loop: it assigns the new tag and
the new arguments and goes round again, so a mutually tail-recursive group runs in
constant JavaScript stack, exactly as a self tail-recursive one does.  A call that is
not in tail position still goes through the member's wrapper, which re-enters the loop.
-/

/-- One member of a merged group. -/
structure Member where
  /-- The Lean declaration. -/
  name : Name
  /-- Its LCNF parameters that survive to run time, needed to map them onto the loop's
      argument slots. -/
  params : List Param
  /-- The parameters that were dropped: types and proofs, which are no argument. -/
  erasedParams : List FVarId
  /-- The type of each surviving parameter. -/
  ptys : List Ty
  /-- What it answers with. -/
  ret : Ty
  /-- Its body. -/
  code : Code

/-- The type two members give the same *result*.  Where they agree it is that type;
    where they do not, the merged loop answers with a value it only passes on, which is
    what `Ty.typeParam` is, and each member’s wrapper reads the answer at its own type.
    The argument slots are no longer unified like this: `groupSlotAlloc` gives a
    parameter a slot of its own rather than widening one. -/
def unifyTy (a b : Ty) : Ty :=
  if a = b then a else Ty.typeParam

/-- The name of the merged function of a group, built from the name its first member
    was given. -/
def mergedName (firstBase : String) : String := "_mut$" ++ firstBase

/-- The name of the *specialised* function of a group whose tag is statically known
    (`LakeJs.Specialise`): the loop of the member the group is named after, with the
    other members unrolled into it.  It is a different name from `mergedName` because
    it is a different function — it has no tag parameter — and a group gets one or the
    other, never both. -/
def specName (firstBase : String) : String := "_spec$" ++ firstBase

/-- The dispatch of the merged loop: test the tag against each member in turn, the last
    member being the `else`. -/
def dispatch {Sg : Sig} {Γ : Ctx} {σs : List Ty} {τ : Ty} (tagTerm : Term Sg Γ Ty.nat) :
    Nat → Body Sg Γ σs τ → List (Body Sg Γ σs τ) → Body Sg Γ σs τ
  | _, b, [] => b
  | i, b, b' :: rest =>
      let test : Term Sg Γ (.prim .bool) :=
        .callExtern .lean_nat_dec_eq (.cons tagTerm (.cons (.lit (.nat i)) .nil))
      .iteB test b (dispatch tagTerm (i + 1) b' rest)

/-- Read one member of a group off its LCNF declaration. -/
def toMember (env : Environment) (d : Decl) : Except String Member := do
  let code ← match d.value with
    | .code c => pure c
    | .extern _ => throw s!"`{d.name}` is implemented by `@[extern]`, so there is nothing to compile"
  let allPs := d.params.toList
  let ps := allPs.filter (!isErasedParam ·)
  if ps.isEmpty then
    throw s!"`{d.name}` has no parameters, so it cannot be a member of a dispatch loop"
  let ptys ← ps.mapM fun p => toTy env p.type
  let declTy ← toTy env d.type
  return { name := d.name, params := ps,
           erasedParams := (allPs.filter isErasedParam).map (·.fvarId), ptys := ptys,
           ret := stripArrows ps.length declTy, code := code }

/-- The first slot of type `t` that this member is not already using, if there is one. -/
def freeSlot? (tys : List Ty) (used : List Nat) (t : Ty) : Option Nat :=
  let rec go : Nat → List Ty → Option Nat
    | _, [] => none
    | k, u :: rest => if u == t && !used.contains k then some k else go (k + 1) rest
  go 0 tys

/-- Where each parameter of each member of a group is held in the merged loop: the types
    of the argument slots, and, per member, the slot of each of its parameters.

    A slot is shared by two members only where they *agree* on its type, so no slot is
    ever widened to `Ty.typeParam` and every slot holds values of one type — which is
    what lets a JavaScript engine keep the loop variable unboxed.  A parameter whose type
    no free slot has gets a slot of its own.  Members that agree pointwise, which is the
    ordinary case and every case in the corpus, therefore get exactly the layout they had
    before: parameter `k` is slot `k`, and there are as many slots as the widest member
    has parameters. -/
def groupSlotAlloc (mems : List Member) : List Ty × List (List Nat) :=
  let rec member : List Ty → List Nat → List Ty → List Ty × List Nat
    | tys, used, [] => (tys, used)
    | tys, used, t :: rest =>
      match freeSlot? tys used t with
      | some k => member tys (used ++ [k]) rest
      | none => member (tys ++ [t]) (used ++ [tys.length]) rest
  let rec go : List Ty → List Member → List Ty × List (List Nat)
    | tys, [] => (tys, [])
    | tys, m :: rest =>
      let (tys, used) := member tys [] m.ptys
      let (tys, outs) := go tys rest
      (tys, used :: outs)
  go [] mems

/-- The argument slots of the merged function of a group, one type per slot. -/
def groupSlotTys (mems : List Member) : List Ty := (groupSlotAlloc mems).1

/-- What the merged function of a group answers with. -/
def groupRet (mems : List Member) : Ty :=
  match mems with
  | [] => Ty.typeParam
  | m :: rest => rest.foldl (fun t m' => unifyTy t m'.ret) m.ret

/-- The type of the merged function of a group: the tag of the member that is running,
    then the argument slots. -/
def groupTypes (mems : List Member) : List Ty × Ty :=
  (Ty.nat :: groupSlotTys mems, groupRet mems)

/-- The value of every argument slot of a merged loop, for a member that holds its `k`-th
    parameter in slot `idxs[k]`: the slots the member has no parameter for get none. -/
def slotValues {Sg : Sig} {Γ : Ctx} (idxs : List Nat) (args : List (SomeTerm Sg Γ))
    (slots : Nat) : List (Option (SomeTerm Sg Γ)) :=
  (List.range slots).map fun j =>
    match idxs.idxOf? j with
    | some k => args[k]?
    | none => none

/-- Translate a mutually recursive group into the merged function and the wrapper of
    each member.  A tail call inside the group becomes a `continue` of the one loop. -/
def transGroup {Sg : Sig} (post : Post Sg) (c : Ctx') (ds : List Decl) :
    Except String (JsDecl Sg × List (Name × JsDecl Sg)) := do
  let mems ← ds.mapM (toMember c.env)
  let (slotTys, argSlots) := groupSlotAlloc mems
  let slots := slotTys.length
  let ret : Ty := groupRet mems
  let σs : List Ty := Ty.nat :: slotTys
  let Γlam : Ctx := σs.reverse ++ []
  let Γbody : Ctx := σs.reverse ++ Γlam
  let gmap : Std.HashMap Name Nat :=
    mems.zipIdx.foldl (init := {}) fun m (mem, i) => m.insert mem.name i
  let slotsOf : Std.HashMap Name (List Nat) :=
    (mems.zip argSlots).foldl (init := {}) fun m (mem, idxs) => m.insert mem.name idxs
  let gc : Ctx' :=
    { c with self := none, group := gmap, groupSlots := slots, groupArgSlots := slotsOf }
  let bodies : List (Body Sg Γbody σs ret) ← (mems.zip argSlots).mapM fun (mem, idxs) => do
    -- each parameter of the member is the slot `groupSlotAlloc` gave it
    let vm : VarMap := mem.params.zipIdx.foldl (init := {}) fun m (p, i) =>
      m.insert p.fvarId (.one (slots + 2 + (idxs[i]?.getD i)))
    let vm : VarMap := mem.erasedParams.foldl (init := vm) fun m f => m.insert f .erased
    transBody gc Γbody vm {} σs ret mem.code
  -- Is the tag a compile-time value?  Then the dispatch is waste: the cycle is unrolled
  -- and the loop belongs to one member, which the others enter (`LakeJs.Specialise`).
  let spec? : Option (JsDecl Sg × List (Name × JsDecl Sg)) := do
    let succ ← LakeJs.Specialise.cycleOf? bodies
    guard (succ.length ≤ LakeJs.Specialise.maxCycleLength)
    let barr := bodies.toArray
    let Γlam' : Ctx := slotTys.reverse ++ []
    let Γbody' : Ctx := slotTys.reverse ++ Γlam'
    let lbody ← LakeJs.Specialise.loopBody? Γbody' barr 0
    let initTerms ← (List.range slotTys.length).mapM fun i =>
      (varAtDepth (Sg := Sg) Γlam' i).toOption
    let init ← mkSpine? (Γ := Γlam') slotTys initTerms
    let sname := specName (c.js (mems.head?.map (·.name) |>.getD Name.anonymous))
    let specTerm : Term Sg [] (.fn slotTys ret) :=
      post _ (Term.lamN (Term.loop init lbody))
    guard (LakeJs.Specialise.termSize specTerm ≤ LakeJs.Specialise.sizeBudget)
    let ownerRef ← GlobalRef.find? Sg sname (.fn slotTys ret)
    let wrappers ← (mems.zip argSlots).zipIdx.mapM fun ((mem, idxs), i) => do
      let Γw : Ctx := mem.ptys.reverse ++ []
      let argTerms ← (List.range mem.ptys.length).mapM fun j =>
        (varAtDepth (Sg := Sg) Γw j).toOption
      let args : Spine Sg Γw slotTys := mkSpineSomePad slotTys (slotValues idxs argTerms slots)
      let t ← LakeJs.Specialise.enterTerm? barr 0 ownerRef i args
      let bodyW : Term Sg Γw mem.ret := coerce mem.ret ⟨ret, t⟩
      pure (mem.name,
        ({ name := c.js mem.name,
           value := ⟨_, post _
             (Term.lamN bodyW : Term Sg [] (.fn mem.ptys mem.ret))⟩ } : JsDecl Sg))
    pure (({ name := sname, exported := false, value := ⟨_, specTerm⟩ } : JsDecl Sg), wrappers)
  if let some r := spec? then
    return r
  let tagVar ← varAtDepth Γbody (slots + 1)
  let body ← match bodies with
    | [] => throw "a merged dispatch loop must have at least one member"
    | b :: bs => pure (dispatch (coerce Ty.nat tagVar) 0 b bs)
  let initTerms ← (List.range σs.length).mapM fun i => varAtDepth (Sg := Sg) Γlam i
  let init ← mkSpine (Γ := Γlam) σs initTerms
  let mname := mergedName (c.js (mems.head?.map (·.name) |>.getD Name.anonymous))
  let merged : JsDecl Sg :=
    { name := mname, exported := false,
      value := ⟨_, post _ (Term.lamN (Term.loop init body) : Term Sg [] (.fn σs ret))⟩ }
  let wrappers ← (mems.zip argSlots).zipIdx.mapM fun ((mem, idxs), i) => do
    let Γw : Ctx := mem.ptys.reverse ++ []
    let tagArg : SomeTerm Sg Γw := ⟨Ty.nat, .lit (.nat i)⟩
    let argTerms ← (List.range mem.ptys.length).mapM fun j => varAtDepth (Sg := Sg) Γw j
    let mergedRef ← globalTerm (Sg := Sg) (Γ := Γw) mname (.fn σs ret)
    let call : Term Sg Γw ret :=
      .apN mergedRef (mkSpineSomePad σs (some tagArg :: slotValues idxs argTerms slots))
    let bodyW : Term Sg Γw mem.ret := coerce mem.ret ⟨ret, call⟩
    return (mem.name,
      ({ name := c.js mem.name,
         value := ⟨_, post _ (Term.lamN bodyW : Term Sg [] (.fn mem.ptys mem.ret))⟩ } : JsDecl Sg))
  return (merged, wrappers)

/-- Everything reachable from the successors of `start` in the call graph. -/
partial def reachGo (edges : Std.HashMap Name (List Name)) : List Name → NameSet → NameSet
  | [], acc => acc
  | n :: rest, acc =>
      if acc.contains n then reachGo edges rest acc
      else reachGo edges ((edges[n]?.getD []) ++ rest) (acc.insert n)

/-- What `start` calls, directly or through others.  `start` itself is in the answer
    exactly when it is part of a cycle. -/
def reachableFrom (edges : Std.HashMap Name (List Name)) (start : Name) : NameSet :=
  reachGo edges (edges[start]?.getD []) {}

/-- The body of a declaration, as a term of the emitted function: its parameters become
    the parameters of a `Term.lamN`, and a self tail call becomes the `continue` of a
    `Term.loop`.  `code` is the block to translate, which is the declaration's own body
    unless a field of an unboxed instance is being kept. -/
def transBodyOf {Sg : Sig} (c : Ctx') (d : Decl) (code : Code) (ret : Ty) :
    Except String (Σ τ : Ty, Term Sg [] τ) := do
  let ps := d.params.toList
  let ptys ← paramTys c.env ps
  let plans := c.paramPlan[d.name]?.getD []
  let (etys, binds) := expandParams 0 plans ps ptys
  let n := etys.length
  if n == 0 then
    let body ← transBody { c with self := none } [] {} {} [] ret code
    match bodyToTerm? body with
    | some t => return ⟨ret, t⟩
    | none => throw s!"`{d.name}` has no parameters, so it cannot be a loop"
  else if hasTailSelfCall d.name code then
    -- the parameters of the lambda, then a mutable copy of each as a loop variable
    let Γlam : Ctx := etys.reverse ++ []
    let Γbody : Ctx := etys.reverse ++ Γlam
    let vm : VarMap := binds.foldl (init := {}) fun m (f, b) =>
      m.insert f (shiftBinding n b)
    let body ← transBody { c with self := some d.name, selfArity := n } Γbody vm {} etys ret code
    let initTerms : List (SomeTerm Sg Γlam) ←
      (List.range n).mapM fun i => varAtDepth Γlam i
    let init ← mkSpine (Γ := Γlam) etys initTerms
    return ⟨_, (.lamN (Term.loop init body) : Term Sg [] (.fn etys ret))⟩
  else
    let Γlam : Ctx := etys.reverse ++ []
    let vm : VarMap := binds.foldl (init := {}) fun m (f, b) => m.insert f b
    let body ← transBody { c with self := none } Γlam vm {} [] ret code
    match bodyToTerm? body with
    | some t => return ⟨_, (.lamN t : Term Sg [] (.fn etys ret))⟩
    | none => throw s!"`{d.name}` continues a loop it is not in"
where
  /-- Inside the loop, the loop variables sit `n` binders above the parameters. -/
  shiftBinding (n : Nat) : Binding → Binding
    | .erased => .erased
    | .one d => .one (d + n)
    | .split p ds => .split p (ds.map (· + n))
    | .instGlobal b p => .instGlobal b p

/-- The LCNF body of a declaration. -/
def declCode (d : Decl) : Except String Code :=
  match d.value with
  | .code c => .ok c
  | .extern _ => .error s!"`{d.name}` is implemented by `@[extern]`, so there is nothing to compile"

/-- The result type of a declaration, after its parameters. -/
def declRet (env : Environment) (d : Decl) : Except String Ty := do
  let declTy ← toTy env d.type
  return stripArrows (runtimeParamCount d.params.toList) declTy

/-- Translate one ordinary declaration. -/
def transDecl {Sg : Sig} (post : Post Sg) (c : Ctx') (d : Decl) :
    Except String (JsDecl Sg) := do
  let code ← declCode d
  let ret ← declRet c.env d
  let v ← transBodyOf c d code ret
  return { name := c.js d.name, value := ⟨v.1, post v.1 v.2⟩ }

/-- Translate a declaration whose result is a class instance: one declaration per field.
    Where the body ends in the constructor of the class, each field keeps only what it
    needs; where it does not, the instance is built once under a private name and the
    fields read it. -/
def transInstDecl {Sg : Sig} (post : Post Sg) (c : Ctx') (d : Decl) (plan : InstPlan) :
    Except String (List (JsDecl Sg)) := do
  let code ← declCode d
  let boxName := c.js d.name ++ "$box"
  let mut out : List (JsDecl Sg) := []
  let mut needBox := false
  for ((fname, fty), i) in plan.fields.zipIdx do
    match instFieldCode? {} i code with
    | some fcode =>
        let v ← transBodyOf c d (dropDeadLets fcode) fty
        out := out ++ [{ name := instFieldName (c.js d.name) fname,
                         value := ⟨v.1, post v.1 v.2⟩ }]
    | none =>
        needBox := true
        let ps := d.params.toList
        let ptys ← paramTys c.env ps
        let plans := c.paramPlan[d.name]?.getD []
        let (etys, _) := expandParams 0 plans ps ptys
        let Γlam : Ctx := etys.reverse ++ []
        let instTy : Ty := plan.boxedTy
        let boxTy : Ty := if etys.isEmpty then instTy else .fn etys instTy
        let boxRef ← globalTerm (Sg := Sg) (Γ := Γlam) boxName boxTy
        let inst : Term Sg Γlam instTy ←
          if etys.isEmpty then
            pure (coerce instTy ⟨boxTy, boxRef⟩)
          else do
            let args ← (List.range etys.length).mapM fun j => varAtDepth (Sg := Sg) Γlam j
            pure (.apN (coerce (.fn etys instTy) ⟨boxTy, boxRef⟩) (← mkSpine etys args))
        let field : Term Sg Γlam fty ← unboxInstField plan ⟨instTy, inst⟩ i fty
        let value : Σ τ : Ty, Term Sg [] τ :=
          if h : etys.isEmpty then
            ⟨fty, by rw [List.isEmpty_iff] at h; subst h; exact field⟩
          else
            ⟨_, (.lamN field : Term Sg [] (.fn etys fty))⟩
        out := out ++ [{ name := instFieldName (c.js d.name) fname, value := value }]
  if needBox then
    let ret ← declRet c.env d
    let v ← transBodyOf c d code ret
    out := { name := boxName, exported := false, value := ⟨v.1, post v.1 v.2⟩ } :: out
  return out

/-- The declarations Lean derives for a type rather than the user writing them: the
    eliminators, the `casesOn`/`recOn` family, the `match_` auxiliaries, and the
    equation lemmas.  They are not part of the compiled module. -/
def isCompilerGenerated (n : Name) : Bool :=
  let cs := n.components.map Name.toString
  let derived :=
    ["elim", "ctorElim", "ctorIdx", "toCtorIdx", "casesOn", "recOn", "rec", "below",
     "brecOn", "ibelow", "binductionOn", "noConfusion", "noConfusionType", "sizeOf",
     "eq_def", "injEq"]
  cs.any (fun c =>
    derived.contains c
      || c.startsWith "match_" || c.startsWith "proof_" || c.startsWith "_sizeOf"
      || c.startsWith "eq_" || c.startsWith "sizeOf_")

/-- The declarations of `mod` that have a compiled body, in name order, with the
    compiler-generated ones left out. -/
def moduleDecls (env : Environment) (mod : Name) : Array Name := Id.run do
  let some idx := env.getModuleIdx? mod | return #[]
  let mut ns := #[]
  for (n, ci) in env.constants.toList do
    if env.getModuleIdxFor? n == some idx then
      let isValue := match ci with
        | .defnInfo _ => true
        -- a `partial def` is an `opaque` constant with an implementation beside it
        | .opaqueInfo _ => true
        | _ => false
      if isValue then
        if (Lean.IR.findEnvDecl env n).isSome && !n.isInternal then
          if !isCompilerGenerated n then
            ns := ns.push n
  return ns.qsort Name.lt

/-- What a module compiles to: the text of the `.js` file, or the reasons it was
    refused. -/
structure Result where
  /-- The text of the JavaScript module. -/
  js : String := ""
  /-- The declarations that could not be compiled, and why. -/
  failures : Array (Name × String) := #[]
  /-- The declarations that were compiled. -/
  compiled : Array Name := #[]
  /-- The declarations whose term still holds a `let` its body never reads.  The
      dead-`let` rule of `LakeJs.Simp` removes those, so this is empty — the test run
      asserts it, which is the extrinsic form of "no unused binding". -/
  deadLets : Array String := #[]
  /-- The declarations that ignore one of their parameters, and which parameters those
      are.  A parameter belongs to the type of the function, hence to its calling
      convention, so it cannot be dropped the way a dead `let` can: this is reported,
      not refused. -/
  unusedParams : Array (String × List Nat) := #[]
  /-- The terms of the module as the translation produced them, before the optimiser
      ran, rendered by `LakeJs.TermPretty`: what `<Module>-Expr.txt` holds. -/
  exprs : String := ""

/-- The first of `base`, `base$1`, `base$2`, … all of whose names (`binds`) are still
    free.  A declaration binds more than one name when it is an instance the backend
    unboxes, or the first member of a merged group, so a base is only free when every
    name built from it is. -/
partial def freshName (used : Std.HashSet String) (binds : String → List String)
    (base : String) (i : Nat) : String :=
  let cand := if i == 0 then base else base ++ "$" ++ toString i
  if (binds cand).all fun s => !used.contains s then cand
  else freshName used binds base (i + 1)

/-- Lift a translation that may fail into `CoreM`. -/
def ofExcept' {α : Type} : Except String α → CoreM α
  | .ok a => pure a
  | .error e => throwError e

/-- The type of an imported declaration, as the signature records it. -/
def importedTy (env : Environment) (n : Name) : CoreM Ty := do
  match ← getBaseDecl? n with
  | some d =>
      let ps := d.params.toList
      let ptys ← ofExcept' (paramTys env ps)
      let declTy ← ofExcept' (toTy env d.type)
      let ret := stripArrows (runtimeParamCount ps) declTy
      let etys := (ps.zip ptys).filterMap fun (p, t) => if isErasedParam p then none else t
      return if etys.isEmpty then ret else .fn etys ret
  | none =>
    match env.find? n with
    | some ci => return (toTy env ci.type).toOption.getD Ty.typeParam
    | none => return Ty.typeParam

/-- The declarations of a module in an order that puts a callee before its caller: a
    depth-first walk of the call graph, pushing a declaration once everything it calls has
    been pushed.  A cycle is broken where it is found — the members of a mutually
    recursive group are translated as one unit anyway.  This is the order the driver
    *translates* in, so that the body a call site may inline is already translated and
    already optimised; the order the declarations are *printed* in is unchanged. -/
partial def topoVisit (edges : Std.HashMap Name (List Name)) (n : Name)
    (st : NameSet × Array Name) : NameSet × Array Name :=
  if st.1.contains n then st
  else
    let st := (edges[n]?.getD []).foldl (init := (st.1.insert n, st.2))
      fun st m => topoVisit edges m st
    (st.1, st.2.push n)

/-- `topoVisit`, from every declaration of the module. -/
def topoOrder (edges : Std.HashMap Name (List Name)) (ns : List Name) : Array Name :=
  (ns.foldl (init := (({} : NameSet), (#[] : Array Name)))
    fun st n => topoVisit edges n st).2

/-- Is a call of this declaration inlined at its call sites?  Lean's own `@[inline]`
    and `@[macro_inline]` say yes and `@[noinline]` says no; where Lean said nothing, a
    body small enough to cost less copied than called is inlined too.  Only a declaration
    whose body is a lambda over its parameters qualifies, since a saturated call is the
    only call the pass rewrites, and one that mentions its own name never does: expanding
    it would put the call back. -/
def inlinableDecl {Sg : Sig} (env : Environment) (n : Name) (jd : JsDecl Sg) : Bool :=
  !Lean.Compiler.hasNoInlineAttribute env n
    && LakeJs.Inline.isLambda jd.value
    && (Lean.Compiler.hasInlineAttribute env n
        || Lean.Compiler.hasMacroInlineAttribute env n
        || LakeJs.Inline.worthInlining inlineSizeLimit jd.value)
    && !(LakeJs.EmitJs.globalsOfTerm jd.value.2).contains jd.name

/-- The names an emitted module needs: the ones it exports, and — transitively — the
    ones a needed declaration mentions. -/
partial def reachableNames {Sg : Sig} (decls : List (JsDecl Sg)) (acc : List String) :
    List String :=
  let acc' := (acc ++ (decls.filter fun d => acc.contains d.name).flatMap
    fun d => LakeJs.EmitJs.globalsOfTerm d.value.2).eraseDups
  if acc'.length == acc.length then acc else reachableNames decls acc'

/-- Drop the declarations the module neither exports nor uses.  Inlining a call is what
    makes those appear: a private declaration whose every call site took a copy of its
    body is a binding nothing reads any more, and the module is smaller without it. -/
def dropUnusedDecls {Sg : Sig} (decls : List (JsDecl Sg)) : List (JsDecl Sg) :=
  let exported := (decls.filter (·.exported)).map (·.name)
  if exported.isEmpty then decls
  else
    let live := reachableNames decls exported
    decls.filter fun d => live.contains d.name

/-- The first declaration of `rest` all of whose dependencies are already out of `rest`,
    i.e. the first one that can be emitted next without mentioning a name the module has
    not bound yet.  A declaration may mention itself: that is a loop, not a dependency. -/
def readyDecl? {Sg : Sig} (rest : List (JsDecl Sg)) : Option (JsDecl Sg) :=
  rest.find? fun d =>
    (LakeJs.EmitJs.globalsOfTerm d.value.2).all fun n =>
      n == d.name || !(rest.any fun e => e.name == n)

/-- `decls` in an order in which a declaration comes after the declarations it mentions,
    keeping the order they were in wherever that is already so. -/
def orderDeclsAux {Sg : Sig} : Nat → List (JsDecl Sg) → List (JsDecl Sg)
  | _, [] => []
  | 0, rest => rest
  | fuel + 1, d0 :: ds =>
      let d := (readyDecl? (d0 :: ds)).getD d0
      d :: orderDeclsAux fuel ((d0 :: ds).filter fun e => e.name != d.name)

/-- The declarations of a module in dependency order: a declaration is emitted after
    every declaration it mentions.

    `const` in JavaScript is not hoisted, so a declaration whose value is computed as the
    module loads — a Lean constant rather than a function — throws if it runs before a
    declaration it calls has been initialised.  Only a cycle cannot be ordered, and the
    declarations of one keep the order they had: a cycle is made of functions, which are
    only read when they are called, by which time the whole module has loaded. -/
def orderDecls {Sg : Sig} (decls : List (JsDecl Sg)) : List (JsDecl Sg) :=
  orderDeclsAux decls.length decls

/-- The terms of a module as `<Module>-Expr.txt` holds them: one block per declaration,
    with its JavaScript name, its type, and the term itself. -/
def renderExprs (cfg : LakeJs.Config.JsConfig) {Sg : Sig} (mod : Name)
    (decls : List (JsDecl Sg)) : String :=
  let header :=
    s!"-- {mod}  [{cfg.describe}]\n\
       -- The terms of this module as the translation produced them, *before* the\n\
       -- optimiser ran; the `.js` file beside this one holds what the optimiser made of\n\
       -- them.  The rendering is `LakeJs.TermPretty`: a variable is the de Bruijn index\n\
       -- of the binder it belongs to, and every binding form names the types it binds.\n\n"
  header ++ String.join (decls.map fun d =>
    s!"{d.name} : {Ty.pretty d.value.1}\n" ++ LakeJs.TermPretty.Term.pretty d.value.2 ++ "\n\n")

/-- Compile one module: the declarations it declares, and the declarations of the same
    module that they call. -/
def compileModule (mod : Name) (preludeDepth : Nat := 1)
    (cfg : LakeJs.Config.JsConfig := .presetPBO) : CoreM Result := do
  unless cfg.isUniform do
    throwError "this configuration mixes JavaScript numbers and `BigInt`s, and there is \
      no runtime prelude for it: every configurable type has to have the same \
      representation"
  let env ← getEnv
  let some idx := env.getModuleIdx? mod
    | throwError s!"module `{mod}` was not imported"
  let roots := moduleDecls env mod
  -- 1. the totality gate
  let rejections ← LakeJs.Totality.check #[idx.toNat] roots
  if !rejections.isEmpty then
    let msgs := rejections.map (·.message)
    throwError ("this module cannot be compiled to JavaScript:\n  "
      ++ String.intercalate "\n  " msgs.toList)
  -- 2. every declaration of the module that is reachable from a root
  let mut order : Array Name := #[]
  let mut seen : NameSet := {}
  let mut todo := roots.toList
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if env.getModuleIdxFor? n != some idx then continue
    match ← getBaseDecl? n with
    | none => pure ()
    | some d =>
      order := order.push n
      match d.value with
      | .code c => todo := todo ++ (calledDecls c).toList
      | .extern _ => pure ()
  -- 3. the declarations themselves, and the call graph between them
  let inModule : NameSet := order.foldl (init := {}) fun s n => s.insert n
  let mut declOf : Std.HashMap Name Decl := {}
  let mut edges : Std.HashMap Name (List Name) := {}
  let mut mentioned : NameSet := {}
  for n in order do
    match ← getBaseDecl? n with
    | none => pure ()
    | some d =>
      declOf := declOf.insert n d
      let called := match d.value with
        | .code cd => (calledDecls cd).toList.filter inModule.contains
        | .extern _ => []
      edges := edges.insert n called
      match d.value with
      | .code cd => mentioned := constsOfCode cd mentioned
      | .extern _ => pure ()
  -- the mutually recursive group of each declaration: the ones it calls that call it
  -- back.  A group of two or more becomes one merged dispatch loop.
  let reach : Std.HashMap Name NameSet :=
    order.foldl (init := {}) fun m n => m.insert n (reachableFrom edges n)
  let groupOf (n : Name) : List Name :=
    let rn := (reach[n]?).getD {}
    order.toList.filter fun m =>
      m == n || (rn.contains m && ((reach[m]?).getD {}).contains n)
  let isMergedGroup (grp : List Name) : Bool :=
    grp.length ≥ 2 && grp.any fun m =>
      match declOf[m]? with
      | some d => match d.value with
        | .code cd => hasTailCallTo (fun x => grp.contains x) cd
        | .extern _ => false
      | none => false
  -- 4. which declarations are class instances, and which parameters are instances
  let mut instOf : Std.HashMap Name InstPlan := {}
  let mut paramPlan : Std.HashMap Name (List (Option InstPlan)) := {}
  for n in order do
    let some d := declOf[n]? | continue
    if isMergedGroup (groupOf n) then continue
    if let some plan ← Meta.MetaM.run' (instPlanOfDecl? d) then
      instOf := instOf.insert n plan
    let plans ← Meta.MetaM.run' (paramPlanOfDecl d)
    if plans.any (·.isSome) then
      paramPlan := paramPlan.insert n plans
  -- 4b. one JavaScript name per declaration.  `jsName` is only a *base*: two Lean names
  -- can spell alike once the characters JavaScript does not allow are replaced, and the
  -- constants an instance is unboxed into (`inst_field`) can spell like a declaration of
  -- their own.  Every name the module binds is therefore handed out here, and a name
  -- already taken gets a `$1`, `$2`, … so that no two declarations share one.
  let mut used : Std.HashSet String := {}
  let mut nameOf : Std.HashMap Name String := {}
  for n in order do
    let some _ := declOf[n]? | continue
    let grp := groupOf n
    let isHead := isMergedGroup grp && grp.head? == some n
    let binds (base : String) : List String :=
      base :: (match instOf[n]? with
               | some plan => (base ++ "$box") :: plan.fields.map fun f => instFieldName base f.1
               | none => [])
            ++ (if isHead then [mergedName base, specName base] else [])
    let base := freshName used binds (jsName n) 0
    for b in binds base do
      used := used.insert b
    nameOf := nameOf.insert n base
  for n in mentioned do
    if inModule.contains n then continue
    if nameOf.contains n then continue
    let base := freshName used (fun b => [b]) (jsName n) 0
    used := used.insert base
    nameOf := nameOf.insert n base
  let nm (n : Name) : String := nameOf[n]?.getD (jsName n)
  -- 5. the signature: every name the emitted module binds or imports
  let mut sig : Sig := []
  for n in order do
    let some d := declOf[n]? | continue
    let ps := d.params.toList
    let ptys ← ofExcept' (paramTys env ps)
    let declTy ← ofExcept' (toTy env d.type)
    let ret := stripArrows (runtimeParamCount ps) declTy
    let plans := paramPlan[n]?.getD []
    let (etys, _) := expandParams 0 plans ps ptys
    let fnTy (r : Ty) : Ty := if etys.isEmpty then r else .fn etys r
    match instOf[n]? with
    | some plan =>
        sig := sig ++ [{ name := nm n ++ "$box", ty := fnTy plan.boxedTy }]
        for (f, fty) in plan.fields do
          sig := sig ++ [{ name := instFieldName (nm n) f, ty := fnTy fty }]
    | none =>
        sig := sig ++ [{ name := nm n, ty := fnTy ret }]
    -- the wrapper of a merged group keeps the member's own parameters
    let grp := groupOf n
    if isMergedGroup grp then
      let mems := grp.filterMap fun m => declOf[m]?
      match mems.mapM (toMember env) with
      | .ok ms =>
          let (σs, gret) := groupTypes ms
          let rep := ms.head?.map (·.name) |>.getD Name.anonymous
          -- the merged loop is *one* declaration for the whole group, so it is declared
          -- once, when the member it is named after comes round — not once per member.
          -- Both shapes it can take are declared, since which one the group gets is only
          -- known once its members are translated; the one it does not get is a name the
          -- emitted module never mentions, and an unmentioned name is not printed.
          if rep == n then
            sig := sig ++ [{ name := mergedName (nm rep), ty := .fn σs gret }]
            sig := sig ++ [{ name := specName (nm rep), ty := .fn (groupSlotTys ms) gret }]
      | .error _ => pure ()
  for n in mentioned do
    if inModule.contains n then continue
    sig := sig ++ [{ name := nm n, ty := ← importedTy env n }]
  -- the names a signature declares must be unique: two entries under one name would be
  -- two JavaScript bindings of the same identifier, and reading the name back out of the
  -- signature could pick either one's type.  Every name here comes from `freshName`, so
  -- this holds; it is checked rather than assumed.
  unless Sig.namesUnique sig do
    throwError s!"the module signature declares a name twice: \
{(Sig.names sig).filter fun s => (Sig.names sig).count s > 1}"
  -- 6. translate, in dependency order (callees first).  A declaration is translated as
  -- a *unit*: on its own, or — for a merged tail-recursive group — together with the
  -- other members of its group, which share one loop.
  let Sg : Sig := sig
  let c : Ctx' := { env := env, self := none, compiled := seen,
                    instOf := instOf, paramPlan := paramPlan, jsNames := nameOf }
  let mut units : Array (List Name × List (JsDecl Sg)) := #[]
  -- the same units, translated again without the optimiser: what `<Module>-Expr.txt`
  -- holds, keyed by the same member list so that a unit dropped below is dropped here
  let mut rawUnits : Array (List Name × List (JsDecl Sg)) := #[]
  let mut failures : Array (Name × String) := #[]
  let mut failed : NameSet := {}
  let mut emitted : NameSet := {}
  -- the declarations a call of which is inlined, filled in as they are translated: the
  -- order is callees first, so a call site always finds the callee's finished term
  let mut inlineTable : LakeJs.Inline.Table Sg := []
  -- callees first, so that the term a call site inlines is the callee's finished one
  for n in topoOrder edges order.toList do
    if emitted.contains n then continue
    let some d := declOf[n]? | continue
    let grp := groupOf n
    let post : Post Sg := optimised inlineTable
    let merged? : Option (JsDecl Sg × List (Name × JsDecl Sg)) :=
      if isMergedGroup grp then
        match transGroup post c (grp.filterMap fun m => declOf[m]?) with
        | .ok r => some r
        | .error _ => none
      else
        none
    let rawDecls : List (JsDecl Sg) :=
      if isMergedGroup grp then
        match transGroup unoptimised c (grp.filterMap fun m => declOf[m]?) with
        | .ok (m, ws) => m :: ws.map (·.2)
        | .error _ => []
      else
        match instOf[n]? with
        | some plan => (transInstDecl unoptimised c d plan).toOption.getD []
        | none =>
          match transDecl unoptimised c d with
          | .ok jd => [jd]
          | .error _ => []
    match merged? with
    | some (mergedDecl, wrappers) =>
        let mems := wrappers.map (·.1)
        let jds := mergedDecl :: wrappers.map fun (m, jd) => { jd with exported := roots.contains m }
        units := units.push (mems, jds)
        rawUnits := rawUnits.push (mems, rawDecls)
        for m in mems do
          emitted := emitted.insert m
    | none =>
      emitted := emitted.insert n
      match instOf[n]? with
      | some plan =>
          match transInstDecl post c d plan with
          | .ok jds =>
              units := units.push ([n],
                jds.map fun jd => { jd with exported := jd.exported && roots.contains n })
              rawUnits := rawUnits.push ([n], rawDecls)
          | .error e =>
              failures := failures.push (n, e)
              failed := failed.insert n
      | none =>
        match transDecl post c d with
        | .ok jd =>
            let jd : JsDecl Sg := { jd with exported := roots.contains n }
            units := units.push ([n], [jd])
            rawUnits := rawUnits.push ([n], rawDecls)
            if inlinableDecl env n jd then
              inlineTable := (jd.name, jd.value) :: inlineTable
        | .error e =>
            failures := failures.push (n, e)
            failed := failed.insert n
  -- 7. a declaration that calls one the translation could not handle is dropped too:
  -- the emitted module never mentions a name of its own that it does not bind.
  let mut live := units
  let mut changed := true
  while changed do
    changed := false
    let mut keep : Array (List Name × List (JsDecl Sg)) := #[]
    for u in live do
      let bad := u.1.flatMap fun m => (edges[m]?.getD []).filter failed.contains
      if bad.isEmpty then
        keep := keep.push u
      else
        changed := true
        for m in u.1 do
          if !failed.contains m then
            failed := failed.insert m
            let names := String.intercalate ", " (bad.eraseDups.map (s!"`{·}`"))
            failures := failures.push (m, s!"it calls {names}, which could not be translated")
    live := keep
  -- the declarations are printed in the order they always were — the caller before the
  -- callee it was translated after
  let emitIdx (ns : List Name) : Nat :=
    (order.toList.reverse.findIdx? fun m => ns.contains m).getD 0
  let ordered := live.qsort fun u v => emitIdx u.1 < emitIdx v.1
  let liveKeys : List (List Name) := ordered.toList.map (·.1)
  -- 8. a declaration nothing exports and nothing calls is not printed: inlining a call
  -- is what leaves those behind.
  let decls : List (JsDecl Sg) := orderDecls (dropUnusedDecls (ordered.toList.flatMap (·.2)))
  let rawDecls : List (JsDecl Sg) :=
    (rawUnits.toList.filter fun u => liveKeys.contains u.1).flatMap (·.2)
  let compiled : Array Name := ordered.flatMap fun u => u.1.toArray
  let deadLets : Array String :=
    (decls.filter fun d => !Term.noUnusedLet d.value.2).toArray.map (·.name)
  let unusedParams : Array (String × List Nat) :=
    (decls.filterMap fun d =>
      let ps := Term.unusedParams d.value.2
      if ps.isEmpty then none else some (d.name, ps)).toArray
  return { js := render cfg decls preludeDepth, failures := failures, compiled := compiled,
           deadLets := deadLets, unusedParams := unusedParams,
           exprs := renderExprs cfg mod rawDecls }

end LakeJs.Compile
