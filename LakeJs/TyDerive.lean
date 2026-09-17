import LakeJs.TyMeta

/-!
# `derive_ty T as Ty.foo` — the `Ty` of a *parameterised* declaration

`lean_ty%` needs a type: `lean_ty% (Option Nat)` is a `Ty`, because `Option Nat` is a
type.  `Option` on its own is not a type but a family of them, so what it has is not a
`Ty` but a **function** from `Ty` to `Ty`, one argument per type parameter:

```lean
derive_ty Option as Ty.optionOfDecl   -- def Ty.optionOfDecl : Ty → Ty
derive_ty Prod   as Ty.prodOfDecl     -- def Ty.prodOfDecl   : Ty → Ty → Ty
```

The body is read off the real Lean declaration by the one translation the backend uses
(`LakeJs.FromLcnf.toTy`, behind `LakeJs.TyMeta`), so a derived function cannot drift
from what the compiler does with the same declaration.

## How a parameter is found

The declaration is read **twice**, at two instantiations of its parameters.

* Once with every parameter instantiated at a type the translation models as
  `Ty.typeParam` — the type of a value whose Lean type the caller chooses.  This run
  says *where* the parameters went: `Option` is `taggedUnion [[], [typeParam]]`.
* Once with parameter `i` instantiated at the `i`-th **probe** type, a built-in scalar
  whose `Ty` is a single leaf and which is different for each parameter.  This run says
  *which* parameter went where: `Option` is `taggedUnion [[], [float32]]`.

Walking the two results together gives the body: a position that is `Ty.typeParam` in
the first run and the `i`-th probe in the second is the argument `αᵢ`, a position that
is `Ty.typeParam` in both is a genuine `Ty.typeParam`, and anything else is the same in
both and is copied.  A scalar the declaration mentions *itself* is not a parameter
position — the first run has that scalar there too — so a probe can never be mistaken
for one, whatever types the declaration uses.

If the two runs disagree in shape, the declaration is one whose *shape* depends on what
its parameters are instantiated at (a `Ty` has no room for that), and `derive_ty`
refuses it with an error rather than generating one of the two shapes.

## What is supported

Everything `lean_ty%` supports, and in addition a recursive parameterised declaration —
`MyList α` inside `MyList α` is `RTy.self 0`, as `LakeJs.FromLcnf` reads it.  Every
parameter has to be a *type* parameter: a value parameter (`n : Nat`, as in
`Vector α n`) makes an indexed family, which has no JavaScript representation.
-/

open Lean Elab Command Term Meta Lean.Compiler.LCNF

namespace LakeJs.TyDerive

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

open LakeJs.Ty
open LakeJs.TyMeta

/-! ## The generated function's arguments -/

/-- The name of the `Ty` argument standing for type parameter `i`. -/
def paramName (i : Nat) : Name := Name.mkSimple ("a" ++ toString i)

/-- The identifier of the `Ty` argument standing for type parameter `i`. -/
def paramIdent (i : Nat) : Ident := mkIdent (paramName i)

/-- The types parameter `i` is read at, and the leaf each of them is modelled by: a
    built-in scalar, so that the leaf is a single node, and all different, so that the
    parameters can be told apart. -/
def probes : List (Name × LeanPrimTy) :=
  [ (``Float32, .float32), (``ISize, .isize), (``Int8, .int8), (``Int16, .int16)
  , (``UInt8, .uint8), (``UInt16, .uint16), (``USize, .usize), (``Int64, .int64)
  , (``UInt64, .uint64), (``Int32, .int32), (``UInt32, .uint32), (``Char, .char)
  , (``Float, .float), (``ByteArray, .byteArray), (``FloatArray, .floatArray)
  , (``String, .string), (``Bool, .bool), (``Int, .int), (``Nat, .nat) ]

/-- Which parameter this leaf is the probe of, among the first `k` probes. -/
def probeIdx? (k : Nat) (p : LeanPrimTy) : Option Nat :=
  (probes.take k).findIdx? (fun q => q.2 == p)

/-! ## Reading the two runs together -/

/-- The error for a declaration whose shape depends on its type arguments: the two runs
    disagree, so there is no one `Ty` to generate. -/
def mismatch (self : Name) (a b : String) : MetaM Term :=
  throwError "the shape of `{self}` depends on what its type parameters are \
    instantiated at (`{a}` at one instantiation, `{b}` at another), and a `Ty` has no \
    room for that"

mutual

/-- The body of the generated function: the two runs walked together, with a parameter
    position rendered as the argument that stands for it. -/
partial def substTy (self : Name) (k : Nat) : Ty → Ty → MetaM Term
  | .typeParam, .typeParam => `(Ty.typeParam)
  | .typeParam, .prim p =>
      match probeIdx? k p with
      | some i => return paramIdent i
      | none => throwError "`{self}` is modelled by the scalar `{p.pretty}` where one \
          of its type parameters was expected"
  | .prim p, .prim q =>
      if p == q then do `(Ty.prim $(← primSyn p))
      else mismatch self (Ty.pretty (.prim p)) (Ty.pretty (.prim q))
  | .fnTy s, .fnTy t => substFn self k s t
  | .primCovariant s, .primCovariant t => substInv self k s t
  | .enum e, .enum e' =>
      if e == e' then tySyn (.enum e)
      else mismatch self (Ty.pretty (.enum e)) (Ty.pretty (.enum e'))
  | .record a, .record b => do `(Ty.record $(← substA2 self k a b))
  | .taggedUnion a, .taggedUnion b => do `(Ty.taggedUnion $(← substTU self k a b))
  | .recTaggedUnion ⟨a⟩, .recTaggedUnion ⟨b⟩ => do
      `(Ty.recTaggedUnion ⟨$(← substRTU self k a b)⟩)
  | .recObject ⟨a⟩, .recObject ⟨b⟩ => do `(Ty.recObject ⟨$(← substRA2 self k a b)⟩)
  | .recAlias ⟨a⟩, .recAlias ⟨b⟩ => do `(Ty.recAlias ⟨$(← substRTy self k a b)⟩)
  | .mutualRecursiveFamily f, .mutualRecursiveFamily g => do
      `(Ty.mutualRecursiveFamily $(← substFamily self k f g))
  | a, b => mismatch self (Ty.pretty a) (Ty.pretty b)

/-- `substTy`, on a function type. -/
partial def substFn (self : Name) (k : Nat) : TyFn Ty → TyFn Ty → MetaM Term
  | .fn ps r, .fn qs s => do `(Ty.fn $(← substList self k ps qs) $(← substTy self k r s))
  | .fn_returnsProd ps r rs, .fn_returnsProd qs s ss => do
      `(Ty.fn_returnsProd $(← substList self k ps qs) $(← substTy self k r s)
          $(← substList self k rs ss))
  | a, b => mismatch self (Ty.pretty (.fnTy a)) (Ty.pretty (.fnTy b))

/-- `substTy`, on an invariant type former. -/
partial def substInv (self : Name) (k : Nat) :
    LeanPrimTyCovariant Ty → LeanPrimTyCovariant Ty → MetaM Term
  | .array a, .array b => do `(Ty.array $(← substTy self k a b))
  | .list a, .list b => do `(Ty.list $(← substTy self k a b))
  | .task a, .task b => do `(Ty.task $(← substTy self k a b))
  | .promise a, .promise b => do `(Ty.promise $(← substTy self k a b))
  | .thunk a, .thunk b => do `(Ty.thunk $(← substTy self k a b))
  | .lazy a, .lazy b => do `(Ty.lazy $(← substTy self k a b))
  | a, b =>
      mismatch self (Ty.pretty (.primCovariant a)) (Ty.pretty (.primCovariant b))

/-- `substTy`, on a list of types. -/
partial def substList (self : Name) (k : Nat) :
    List Ty → List Ty → MetaM Term
  | as, bs =>
      if as.length != bs.length then
        mismatch self s!"{as.length} types" s!"{bs.length} types"
      else do
        let ts ← (as.zip bs).toArray.mapM fun (a, b) => substTy self k a b
        `([$ts,*])

/-- `substTy`, on the constructors of a layout. -/
partial def substCtors (self : Name) (k : Nat) :
    List (List Ty) → List (List Ty) → MetaM Term
  | as, bs =>
      if as.length != bs.length then
        mismatch self s!"{as.length} constructors" s!"{bs.length} constructors"
      else do
        let l ← (as.zip bs).toArray.mapM fun (a, b) => substList self k a b
        `([$l,*])

/-- `substTy`, on the fields of a record. -/
partial def substA2 (self : Name) (k : Nat) :
    LeanRecordSchema Ty → LeanRecordSchema Ty → MetaM Term
  | ⟨a1, a2, as⟩, ⟨b1, b2, bs⟩ => do
      `(⟨$(← substTy self k a1 b1), $(← substTy self k a2 b2),
         $(← substList self k as bs)⟩)

/-- `substTy`, on the fields of a constructor that has at least one. -/
partial def substNE (self : Name) (k : Nat) :
    NonEmptyList Ty → NonEmptyList Ty → MetaM Term
  | ⟨a, as⟩, ⟨b, bs⟩ => do
      `(⟨$(← substTy self k a b), $(← substList self k as bs)⟩)

/-- `substTy`, on the constructors of a tagged union. -/
partial def substTU (self : Name) (k : Nat) :
    LeanTaggedUnionSchema Ty → LeanTaggedUnionSchema Ty → MetaM Term
  | .payloadFirst f n r, .payloadFirst g m s => do
      `(LeanTaggedUnionSchema.payloadFirst $(← substNE self k f g)
          $(← substList self k n m) $(← substCtors self k r s))
  | .skip a, .skip b => do `(LeanTaggedUnionSchema.skip $(← substCP self k a b))
  | a, b =>
      mismatch self (Ty.pretty (.taggedUnion a)) (Ty.pretty (.taggedUnion b))

/-- `substTy`, on the constructors that follow a field-less one. -/
partial def substCP (self : Name) (k : Nat) :
    CtorsWithPayload Ty → CtorsWithPayload Ty → MetaM Term
  | .here f r, .here g s => do
      `(CtorsWithPayload.here $(← substNE self k f g) $(← substCtors self k r s))
  | .skip a, .skip b => do `(CtorsWithPayload.skip $(← substCP self k a b))
  | _, _ =>
      mismatch self "a sum whose first constructor carries fields"
        "a sum whose first constructor carries none"

/-- `substTy`, on a type inside a recursive declaration. -/
partial def substRTy (self : Name) (k : Nat) : RTy → RTy → MetaM Term
  | .self i, .self j =>
      if i == j then do `(RTy.self $(quote i))
      else mismatch self (RTy.pretty (.self i)) (RTy.pretty (.self j))
  | .typeParam, .typeParam => `(RTy.typeParam)
  -- the argument stands for a *closed* type, so inside a recursive declaration it is
  -- read one layer down (`Ty.toRTy`)
  | .typeParam, .prim p =>
      match probeIdx? k p with
      | some i => `(Ty.toRTy $(paramIdent i))
      | none => throwError "`{self}` is modelled by the scalar `{p.pretty}` where one \
          of its type parameters was expected"
  | .prim p, .prim q =>
      if p == q then do `(RTy.prim $(← primSyn p))
      else mismatch self (RTy.pretty (.prim p)) (RTy.pretty (.prim q))
  | .fnTy s, .fnTy t => substRFn self k s t
  | .primCovariant s, .primCovariant t => substRInv self k s t
  | .enum e, .enum e' =>
      if e == e' then rtySyn (.enum e)
      else mismatch self (RTy.pretty (.enum e)) (RTy.pretty (.enum e'))
  | .record a, .record b => do `(RTy.record $(← substRA2 self k a b))
  | .taggedUnion a, .taggedUnion b => do `(RTy.taggedUnion $(← substRTU self k a b))
  | .recTaggedUnion ⟨a⟩, .recTaggedUnion ⟨b⟩ => do
      `(RTy.recTaggedUnion ⟨$(← substRTU self k a b)⟩)
  | .recObject ⟨a⟩, .recObject ⟨b⟩ => do `(RTy.recObject ⟨$(← substRA2 self k a b)⟩)
  | .recAlias ⟨a⟩, .recAlias ⟨b⟩ => do `(RTy.recAlias ⟨$(← substRTy self k a b)⟩)
  | .mutualRecursiveFamily f, .mutualRecursiveFamily g => do
      `(RTy.mutualRecursiveFamily $(← substFamily self k f g))
  | a, b => mismatch self (RTy.pretty a) (RTy.pretty b)

/-- `substRTy`, on a function type. -/
partial def substRFn (self : Name) (k : Nat) : TyFn RTy → TyFn RTy → MetaM Term
  | .fn ps r, .fn qs s => do
      `(RTy.fn $(← substRList self k ps qs) $(← substRTy self k r s))
  | .fn_returnsProd ps r rs, .fn_returnsProd qs s ss => do
      `(RTy.fn_returnsProd $(← substRList self k ps qs) $(← substRTy self k r s)
          $(← substRList self k rs ss))
  | a, b => mismatch self (RTy.pretty (.fnTy a)) (RTy.pretty (.fnTy b))

/-- `substRTy`, on an invariant type former. -/
partial def substRInv (self : Name) (k : Nat) :
    LeanPrimTyCovariant RTy → LeanPrimTyCovariant RTy → MetaM Term
  | .array a, .array b => do `(RTy.array $(← substRTy self k a b))
  | .list a, .list b => do `(RTy.list $(← substRTy self k a b))
  | .task a, .task b => do `(RTy.task $(← substRTy self k a b))
  | .promise a, .promise b => do `(RTy.promise $(← substRTy self k a b))
  | .thunk a, .thunk b => do `(RTy.thunk $(← substRTy self k a b))
  | .lazy a, .lazy b => do `(RTy.lazy $(← substRTy self k a b))
  | a, b =>
      mismatch self (RTy.pretty (.primCovariant a)) (RTy.pretty (.primCovariant b))

/-- `substRTy`, on a list of types. -/
partial def substRList (self : Name) (k : Nat) :
    List RTy → List RTy → MetaM Term
  | as, bs =>
      if as.length != bs.length then
        mismatch self s!"{as.length} types" s!"{bs.length} types"
      else do
        let ts ← (as.zip bs).toArray.mapM fun (a, b) => substRTy self k a b
        `([$ts,*])

/-- `substRTy`, on the constructors of a layout. -/
partial def substRCtors (self : Name) (k : Nat) :
    List (List RTy) → List (List RTy) → MetaM Term
  | as, bs =>
      if as.length != bs.length then
        mismatch self s!"{as.length} constructors" s!"{bs.length} constructors"
      else do
        let l ← (as.zip bs).toArray.mapM fun (a, b) => substRList self k a b
        `([$l,*])

/-- `substRTy`, on the fields of a record. -/
partial def substRA2 (self : Name) (k : Nat) :
    LeanRecordSchema RTy → LeanRecordSchema RTy → MetaM Term
  | ⟨a1, a2, as⟩, ⟨b1, b2, bs⟩ => do
      `(⟨$(← substRTy self k a1 b1), $(← substRTy self k a2 b2),
         $(← substRList self k as bs)⟩)

/-- `substRTy`, on the fields of a constructor that has at least one. -/
partial def substRNE (self : Name) (k : Nat) :
    NonEmptyList RTy → NonEmptyList RTy → MetaM Term
  | ⟨a, as⟩, ⟨b, bs⟩ => do
      `(⟨$(← substRTy self k a b), $(← substRList self k as bs)⟩)

/-- `substRTy`, on the constructors of a tagged union. -/
partial def substRTU (self : Name) (k : Nat) :
    LeanTaggedUnionSchema RTy → LeanTaggedUnionSchema RTy → MetaM Term
  | .payloadFirst f n r, .payloadFirst g m s => do
      `(LeanTaggedUnionSchema.payloadFirst $(← substRNE self k f g)
          $(← substRList self k n m) $(← substRCtors self k r s))
  | .skip a, .skip b => do `(LeanTaggedUnionSchema.skip $(← substRCP self k a b))
  | a, b =>
      mismatch self (RTy.pretty (.taggedUnion a)) (RTy.pretty (.taggedUnion b))

/-- `substRTy`, on the constructors that follow a field-less one. -/
partial def substRCP (self : Name) (k : Nat) :
    CtorsWithPayload RTy → CtorsWithPayload RTy → MetaM Term
  | .here f r, .here g s => do
      `(CtorsWithPayload.here $(← substRNE self k f g) $(← substRCtors self k r s))
  | .skip a, .skip b => do `(CtorsWithPayload.skip $(← substRCP self k a b))
  | _, _ =>
      mismatch self "a sum whose first constructor carries fields"
        "a sum whose first constructor carries none"

/-- `substRTy`, on one member of a mutual family. -/
partial def substMember (self : Name) (k : Nat) : FamMember → FamMember → MetaM Term
  | .ctors a, .ctors b => do `(LeanFamMemberSchema.ctors $(← substRTU self k a b))
  | .record a, .record b => do `(LeanFamMemberSchema.record $(← substRA2 self k a b))
  | .alias a, .alias b => do `(LeanFamMemberSchema.alias $(← substRTy self k a b))
  | _, _ =>
      mismatch self "a member of one shape" "a member of another"

/-- `substRTy`, on the members of a mutual family. -/
partial def substMembers (self : Name) (k : Nat) :
    List FamMember → List FamMember → MetaM Term
  | as, bs =>
      if as.length != bs.length then
        mismatch self s!"a family of {as.length} members"
          s!"a family of {bs.length} members"
      else do
        let ms ← (as.zip bs).toArray.mapM fun (a, b) => substMember self k a b
        `([$ms,*])

/-- `substRTy`, on a whole mutual family. -/
partial def substFamily (self : Name) (k : Nat) :
    LeanMutualRecFamily RTy → LeanMutualRecFamily RTy → MetaM Term
  | .selectedThenMore b1 c1 n1 a1, .selectedThenMore b2 c2 n2 a2 => do
      `(LeanMutualRecFamily.selectedThenMore $(← substMembers self k b1 b2)
          $(← substMember self k c1 c2) $(← substMember self k n1 n2)
          $(← substMembers self k a1 a2))
  | .selectedLast f1 b1 c1, .selectedLast f2 b2 c2 => do
      `(LeanMutualRecFamily.selectedLast $(← substMember self k f1 f2)
          $(← substMembers self k b1 b2) $(← substMember self k c1 c2))
  | _, _ =>
      mismatch self "a family selecting one member" "a family selecting another"

end

/-! ## Reading the declaration -/

/-- Fail unless the first `k` binders of a declaration's type are type parameters. -/
def checkTypeParams (self : Name) (k : Nat) (ty : Expr) : MetaM Unit := do
  let rec go : Nat → Expr → MetaM Unit
    | 0, _ => pure ()
    | n + 1, .forallE _ d b _ => do
        unless (← whnf d).isSort do
          throwError "parameter #{k - n} of `{self}` is a value parameter of type \
            `{d}`, not a type parameter; such a declaration is an indexed family and \
            has no JavaScript representation"
        go n b
    | n, e => throwError "`{self}` has fewer binders than its {n} remaining declared \
        parameters (its type is `{e}`)"
  go k ty

/-- The declaration, applied to `k` arguments. -/
def applied (self : Name) (lvls : List Level) (args : List Expr) : Expr :=
  mkAppN (.const self lvls) args.toArray

/-- How many `Ty` arguments the generated function takes, and its body. -/
def deriveTyBody (self : Name) : MetaM (Nat × Term) := do
  let iv ← getConstInfoInduct self
  if iv.numIndices != 0 then
    throwError "`{self}` is an indexed family, which has no JavaScript representation"
  let k := iv.numParams
  checkTypeParams self k iv.type
  if probes.length < k then
    throwError "`{self}` takes {k} type parameters, more than the {probes.length} \
      probe types `derive_ty` can tell apart"
  let lvls := iv.levelParams.map fun _ => Level.zero
  let anys := (List.range k).map fun _ => Expr.const ``lcAny []
  let probeArgs := (probes.take k).map fun p => Expr.const p.1 []
  let base ← tyOfExpr (applied self lvls anys)
  let probed ← tyOfExpr (applied self lvls probeArgs)
  unless Ty.wf probed do
    throwError "the type read off `{self}` is not one the backend can produce \
      (`{probed.pretty}`); see `LakeJs.TySchema` for the conditions each shape has to \
      meet"
  return (k, ← substTy self k base probed)

/-- `Ty → Ty → … → Ty`, with `n` arguments. -/
def arityTySyn : Nat → MetaM Term
  | 0 => `(Ty)
  | n + 1 => do `(Ty → $(← arityTySyn n))

/-- The `def` that `derive_ty` generates. -/
def deriveTyCmd (doc : Option (TSyntax ``Lean.Parser.Command.docComment))
    (declName self : Name) : MetaM (TSyntax `command) := do
  let (k, body) ← deriveTyBody self
  let sig ← arityTySyn k
  let binders := (Array.range k).map paramIdent
  let val ← if binders.isEmpty then pure body else `(fun $binders* => $body)
  let id := mkIdent declName
  match doc with
  | some d => `(command| $d:docComment def $id:ident : $sig := $val)
  | none => `(command| def $id:ident : $sig := $val)

/-- `Ty.` followed by the declaration's short name with a lower-case initial: the
    default target name, so `derive_ty Option` defines `Ty.option`. -/
def defaultTargetName (self : Name) : Name :=
  let s := match self with
    | .str _ s => s
    | n => n.toString
  let s := match s.toList with
    | c :: cs => String.ofList (c.toLower :: cs)
    | [] => s
  (Name.mkSimple "Ty").str s

/-! ## The command -/

/--
`derive_ty T` defines `Ty.t` — a `Ty`, or a function from `Ty` to `Ty` with one argument
per type parameter of `T` — by reading the real Lean declaration `T` with the
translation the backend itself uses.  `derive_ty T as Ty.foo` chooses the name.
-/
syntax (docComment)? "derive_ty " ident (" as " ident)? : command

elab_rules : command
  | `(command| $[$doc:docComment]? derive_ty $id:ident) => do
      let cmd ← liftTermElabM do
        let self ← resolveGlobalConstNoOverload id
        deriveTyCmd doc (defaultTargetName self) self
      elabCommand cmd
  | `(command| $[$doc:docComment]? derive_ty $id:ident as $tgt:ident) => do
      let cmd ← liftTermElabM do
        let self ← resolveGlobalConstNoOverload id
        deriveTyCmd doc tgt.getId self
      elabCommand cmd

end LakeJs.TyDerive
