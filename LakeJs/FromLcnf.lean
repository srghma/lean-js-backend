import Lean
import Lean.Compiler.LCNF
import LakeJs.Lookup
import LakeJs.TyPretty
import LakeJs.Simp
import LakeJs.EmitJs
import LakeJs.ExternTable
import LakeJs.Totality

/-!
# From what the `.olean` stores to a `Term`

The backend reads the **`saveBase` LCNF phase** out of the `.olean` files — not
`Lean.IR`, and not `saveMono`.  Both of those have already thrown the types away: by
then a `Nat`, a `UInt32`, a `Char` and a one-field structure all look alike, and the
choice of JavaScript representation, which is what an optimiser wants to work against,
can no longer be made.  `base` still carries the LCNF type of every binder, so this
translation can build a *typed* `Term`.

What the translation does, in one paragraph.  A declaration's parameters become the
parameters of a `Term.lamN`.  If the declaration calls itself, the whole body becomes a
`Term.loop` whose loop variables are copies of those parameters, and a self-call in tail
position becomes `Body.cont` — that, and only that, is how recursion survives into the
output, which is why the output only ever contains `while`.  A self-call that is *not*
in tail position is refused, with a message saying so, rather than being turned into a
recursive JavaScript function.

A *mutually* tail-recursive group is compiled the same way, into a single loop shared by
all of its members (`LakeJs.Compile.transGroup` assembles it): the loop's first variable
is the tag of the member that is running and the rest are the argument slots, and
`Ctx'.group` is what tells this translation that a tail call to another member of the
group is a `Body.cont` of that shared loop rather than a JavaScript call.

Join points are inlined at their jumps (LCNF join points are not recursive, so this
terminates), because a jump in the middle of a join point may be the tail call of the
enclosing loop, and a JavaScript function call could not be one.

## Three things every reference goes through

* a call of a function Lean implements with `@[extern]` becomes `Term.extern`, which
  carries the catalogue entry (`LakeJs.Externs`) and therefore the *type* of the runtime
  function, rather than a bare name;
* the few operations that are not Lean functions at all — a reinterpretation of a value
  at another type, `Bool.and`, and the rest of `JsOp` — become `Term.jsOp`, which is
  indexed by the types of its arguments in the same way, so it too is applied to exactly
  the arguments it takes;  a constant like `instDecidableEqString` used as a *value* is
  eta-expanded into `(v0, v1) => v0 === v1` rather than printed as a call of no
  arguments;
* anything else becomes `Term.global`, an index into the module's signature: the name
  must be one the module declares or imports, and it is used at the type the signature
  gives it.

## Instances are unboxed

A class instance is not a record at run time.  A declaration of the module whose result
is a class with fields `f₁ … f_k` is emitted as `k` declarations, `inst_f₁ … inst_f_k`
(`LakeJs.Compile`), and this translation resolves a *projection* of it straight to the
field it names.  A parameter whose type is such a class is likewise split into one
parameter per field, so a function that depends on an instance it cannot see takes the
instance's fields as ordinary arguments.  Where a whole instance is genuinely needed as
one value — it is handed to a function of another module — the fields are packed back
into a record on the spot.
-/

namespace LakeJs.FromLcnf

open LakeJs
open LakeJs.Ty
open LakeJs.Layout (FieldLayout ObjLayout)
open LakeJs.Expr
open LakeJs.Lookup
open LakeJs.Rename
open LakeJs.Simp
open LakeJs.EmitJs
open LakeJs.ExternTable
open LakeJs.Totality

open Lean Lean.Compiler.LCNF
open LakeJs.EmitJs

/-- Is this LCNF type the type of a value that carries *nothing* at run time — a type
    argument or a proof?  Such a binder is **dropped**: it is not given a `Ty` and no
    parameter, argument or `let` is emitted for it, which is why `Ty` has no erased
    type and `Term` no erased literal. -/
def isErasedLcnfTy : Expr → Bool
  | .sort _ => true
  | .mdata _ e => isErasedLcnfTy e
  -- a *type family* (`Nat → Type`) is as much a compile-time value as a type is
  | .forallE _ _ b _ => isErasedLcnfTy b
  | e => e.getAppFn.constName? == some ``lcErased

/-- Is this LCNF parameter dropped? -/
def isErasedParam (p : Param) : Bool := isErasedLcnfTy p.type

/-- Is this LCNF argument dropped? -/
def isErasedArgForm : Arg → Bool
  | .type _ => true
  | .erased => true
  | .fvar _ => false

/-! ## Types

Every Lean type a compiled declaration mentions is modelled, or the declaration is
refused: there is no longer an "unmodelled type" to fall back on.  That means this
translation has to do two things the old one did not.

* **A parameterised declaration is modelled at its instantiation.**  `Except Nat String`
  is read by instantiating `Except`'s constructors with `Nat` and `String` and turning
  the result into a `Ty.taggedUnion [[.nat], [.string]]`.  `Option Nat` and
  `Except Nat String` are therefore different types, and each is a finite tree.
* **A mutual block is modelled as a family.**  The bodies of *all* the members are read
  at once, and `RTy.self i` inside them is member `i`, so a member never points outside
  its family.

The shape a declaration gets is the shape it has: no field, one field, several fields,
one constructor or several, recursive or not — see `LakeJs.Ty`.  A single-constructor
declaration with a single runtime field is a **newtype**: the wrapper is erased, and its
`Ty` is the field's own `Ty`.

Two things are still refused rather than guessed: an inductive *family* with indices,
and a recursive declaration that occurs inside another recursive declaration's body
(the type language has one `.self` binder per recursive shape, and the inner one
shadows the outer).  A value whose Lean type is a **type parameter** of the enclosing
declaration is `Ty.typeParam` — parametric, and provably impossible to take apart.
-/

/-- The runtime tag of a constructor: its position in its type's declaration order. -/
def ctorIdx (env : Environment) (n : Name) : Nat :=
  match env.find? n with
  | some (.ctorInfo ci) => ci.cidx
  | _ => 0

/-- Strip `n` leading `∀` binders off a type, whatever is under them. -/
def stripForalls : Nat → Expr → Expr
  | 0, e => e
  | k + 1, .forallE _ _ b _ => stripForalls k b
  | _, e => e

/-- Drop every remaining `∀` binder: `∀ x y, P` becomes `P`. -/
partial def resultOfForalls : Expr → Expr
  | .forallE _ _ b _ => resultOfForalls b
  | .mdata _ e => resultOfForalls e
  | e => e

/-- Is this LCNF type the type of a **proof**?  A proof carries nothing at run time, so
    the field or parameter it fills is dropped — exactly as LCNF drops it, which is what
    keeps the field numbers of a layout and the argument numbers of a constructor
    application the same.

    The test is the one that can be made without elaborating: the head constant's own
    type, with the arguments the occurrence gives it stripped off, ends in `Prop`.  That
    covers `n < 3`, `a = b`, `xs ≠ []`, `p ∧ q` and every other proposition a field can
    have; a head that is not a constant is not a proposition here. -/
partial def isPropTyIn (env : Environment) (binders : Array Expr) (e : Expr) : Bool :=
  match e with
  | .forallE _ a b _ => isPropTyIn env (binders.push a) b
  | .mdata _ e => isPropTyIn env binders e
  | e =>
    let e := e.headBeta
    match e.getAppFn with
    | .const c _ =>
      (match env.find? c with
       | none => false
       | some info =>
         match resultOfForalls (stripForalls e.getAppNumArgs info.type) with
         | .sort .zero => true
         | _ => false)
    | .bvar i =>
      -- the field's type is a *parameter* applied to arguments, as in `Subtype`'s
      -- `property : p val`: it is a proof exactly when that parameter is a predicate
      (match binders[binders.size - 1 - i]? with
       | some t => resultOfForalls t == Expr.sort .zero
       | none => false)
    | .lam .. => isPropTyIn env binders e.headBeta
    | _ => false

/-- `isPropTyIn`, outside any binder. -/
def isPropTy (env : Environment) (e : Expr) : Bool := isPropTyIn env #[] e

/-- Is this parameter or field dropped — a type, a proof, or a value LCNF has already
    erased? -/
def isErasedFieldTy (env : Environment) (e : Expr) : Bool :=
  isErasedLcnfTy e || isPropTy env e

/-- Is a binder of this type a **compile-time** thing — a type, a type family or a
    proof?  Such a binder carries nothing at run time, so the field or parameter it
    stands for is dropped.

    This is the test for a *kernel* type, where an erased binder still has its original
    type.  It deliberately does **not** treat `lcErased` as compile-time: a binder whose
    type the translation could not read still holds a runtime value, of the type the
    caller chooses (`Ty.typeParam`) — the `State` field of
    `structure Unfold where State : Type; seed : State; …` is dropped, and `seed`,
    whose type is that field, is not. -/
def isTypeOrProofTy (env : Environment) (binders : Array Expr) (e : Expr) : Bool :=
  let rec isSortLike : Expr → Bool
    | .sort _ => true
    | .mdata _ e => isSortLike e
    | .forallE _ _ b _ => isSortLike b
    | _ => false
  isSortLike e || isPropTyIn env binders e

/-- How many fields of this constructor survive to run time: the ones that are neither
    a type nor a proof.  It is the number of arguments LCNF passes to the constructor,
    and the number of entries the layout of its type has for it. -/
def runtimeFieldCount (env : Environment) (ci : ConstructorVal) : Nat :=
  let rec skip : Nat → Expr → Array Expr → Expr × Array Expr
    | 0, e, bs => (e, bs)
    | k + 1, .forallE _ a b _, bs => skip k b (bs.push a)
    | _, e, bs => (e, bs)
  let (t, bs) := skip ci.numParams ci.type #[]
  let rec go : Nat → Expr → Array Expr → Nat → Nat
    | 0, _, _, acc => acc
    | k + 1, .forallE _ a b _, bs, acc =>
        go k b (bs.push a) (if isTypeOrProofTy env bs a then acc else acc + 1)
    | _, _, _, acc => acc
  go ci.numFields t bs 0

/-- Does the backend give this declaration a representation of its own, rather than
    reading one off its constructors?  `toRTyAppIn` answers these names with a `Ty` that
    owes nothing to how Lean declares them — an `Array` is a JavaScript array and not the
    `List` its one field holds — so none of them may be treated as a newtype, however
    their declaration is shaped. -/
def hasPrimitiveLayout (n : Name) : Bool :=
  n == ``Nat || n == ``Int || n == ``Bool || n == ``String || n == ``Char ||
  n == ``Float || n == ``Float32 ||
  n == ``UInt8 || n == ``UInt16 || n == ``UInt32 || n == ``UInt64 || n == ``USize ||
  n == ``Int8 || n == ``Int16 || n == ``Int32 || n == ``Int64 || n == ``ISize ||
  n == ``ByteArray || n == ``FloatArray ||
  n == ``Ordering || n == ``Unit || n == ``PUnit || n == ``Decidable ||
  n == ``Array || n == ``List

/-- Is this constructor a *conversion* rather than a constructor of a layout?  The
    backend represents an `Array` as a JavaScript array and a `String` as a JavaScript
    string, so building one out of the `List` Lean declares it to hold is work the
    runtime does — `Array.mk` is `lean_array_mk`, not a tag and a field. -/
def isConversionCtor (n : Name) : Bool :=
  n == ``Array.mk || n == ``String.mk || n == ``ByteArray.mk || n == ``FloatArray.mk

/-- Is this declaration a **newtype** — one constructor with one runtime field?  Such a
    declaration has no wrapper at run time: its `Ty` is the field's own `Ty`, building
    one is its field and reading its field is the value itself. -/
def isNewtypeInduct (env : Environment) (n : Name) : Bool :=
  if hasPrimitiveLayout n then false else
  match env.find? n with
  | some (.inductInfo iv) =>
    iv.all.length == 1 && !iv.isUnsafe &&
      (match iv.ctors with
       | [cn] =>
         (match env.find? cn with
          | some (.ctorInfo ci) => runtimeFieldCount env ci == 1
          | _ => false)
       | _ => false)
  | _ => false

/-- Where the `i`-th field of a single-constructor declaration sits in its layout.
    LCNF numbers the fields of a projection as the declaration does — the types and
    proofs among them included — and a layout numbers only the fields that survive to
    run time, so `structure Unfold where State : Type; seed : State; …` has its `seed`
    at declaration index 1 and at layout index 0.  `none` if the field itself carries
    nothing, and so has no layout entry at all. -/
def runtimeFieldIndex (env : Environment) (sname : Name) (i : Nat) : Option Nat :=
  match env.find? sname with
  | some (.inductInfo iv) =>
    match iv.ctors with
    | [cn] =>
      match env.find? cn with
      | some (.ctorInfo ci) =>
        let rec skip : Nat → Expr → Array Expr → Expr × Array Expr
          | 0, e, bs => (e, bs)
          | k + 1, .forallE _ a b _, bs => skip k b (bs.push a)
          | _, e, bs => (e, bs)
        let (t, bs) := skip ci.numParams ci.type #[]
        let rec go : Nat → Expr → Array Expr → Nat → Nat → Option Nat
          | 0, _, _, _, _ => none
          | k + 1, .forallE _ a b _, bs, here, seen =>
            let erased := isTypeOrProofTy env bs a
            if here == i then (if erased then none else some seen)
            else go k b (bs.push a) (here + 1) (if erased then seen else seen + 1)
          | _, _, _, _, _ => none
        go ci.numFields t bs 0 0
      | _ => none
    | _ => none
  | _ => none

/-- Is this constructor the constructor of a newtype? -/
def isNewtypeCtor (env : Environment) (cn : Name) : Bool :=
  match env.find? cn with
  | some (.ctorInfo ci) => isNewtypeInduct env ci.induct
  | _ => false

/-- The recursive declaration whose body is being read: its members, in declaration
    order (one member unless it is a mutual block), and the type arguments they are
    instantiated at.  An occurrence of member `i` inside the body is `RTy.self i`. -/
structure SelfScope where
  /-- The members of the declaration, in declaration order. -/
  members : List Name
  /-- The type arguments the family is instantiated at. -/
  args : Array Expr

/-- The position of a name among the members of a scope. -/
def SelfScope.idxOf? (sc : SelfScope) (n : Name) : Option Nat :=
  sc.members.idxOf? n

/-- Instantiate the first `k` `∀` binders of a type with the arguments given. -/
def instParams : Nat → Array Expr → Expr → Except String Expr
  | 0, _, e => .ok e
  | k + 1, args, .forallE _ _ b _ =>
    match args[0]? with
    | some a => instParams k (args.extract 1 args.size) (b.instantiate1 a)
    | none => .error "a type constructor is applied to fewer arguments than it takes"
  | _, _, _ => .error "a type constructor has fewer parameters than it is applied to"

/-- How deep a type may be expanded before the translation gives up.  Expansion only
    ever descends into the *fields* of a declaration, and a recursive occurrence is
    `RTy.self`, so ordinary types are nowhere near this; a type whose expansion does not
    stop (a non-uniformly recursive one) is refused instead of looping. -/
def tyFuel : Nat := 64

mutual

/-- The `RTy` of an LCNF type, inside the recursive declaration `self` — or outside any,
    when `self` is `none`, in which case no `RTy.self` is produced. -/
partial def toRTyIn (env : Environment) (self : Option SelfScope) (blocked : List Name)
    (fuel : Nat) (e : Expr) : Except String RTy := do
  if fuel == 0 then
    throw "a type is too deeply nested for the backend to read"
  match e with
  | .forallE _ a b _ =>
      -- a binder that carries nothing at run time is no JavaScript parameter, so it is
      -- no parameter of the function type either
      if isTypeOrProofTy env #[] a then
        toRTyIn env self blocked fuel (b.instantiate1 (.const ``lcAny []))
      else
        let a' ← toRTyIn env self blocked fuel a
        let b' ← toRTyIn env self blocked fuel
          (b.instantiate1 (.const ``lcAny []))
        return .fn [a'] b'
  | .mdata _ e => toRTyIn env self blocked fuel e
  | .app .. =>
      -- a type-level application: beta-reduce it, and read a head that is a type
      -- variable as one
      let e' := e.headBeta
      if e' != e then toRTyIn env self blocked (fuel - 1) e'
      else if !e.getAppFn.isConst then return .typeParam
      else toRTyAppIn env self blocked fuel e
  | .lam .. => return .typeParam
  | .bvar _ | .fvar _ | .mvar _ =>
      -- a type variable: the value has a type the *caller* chooses, so the compiled
      -- code can only pass it on
      return .typeParam
  | .sort _ => throw "a type used as a value is erased, so it has no runtime type"
  | e => toRTyAppIn env self blocked fuel e

/-- The `RTy` of a type whose head is a constant, applied to arguments. -/
partial def toRTyAppIn (env : Environment) (self : Option SelfScope) (blocked : List Name)
    (fuel : Nat) (e : Expr) : Except String RTy := do
  if fuel == 0 then
    throw "a type is too deeply nested for the backend to read"
  let args := e.getAppArgs
  match e.getAppFn.constName? with
  | none => return .typeParam
  | some n =>
      match n with
      | ``Nat => return .prim .nat
      | ``Int => return .prim .int
      | ``Bool => return .prim .bool
      | ``String => return .prim .string
      | ``Char => return .prim .char
      | ``Float => return .prim .float
      | ``Float32 => return .prim .float32
      | ``UInt8 => return .prim .uint8
      | ``UInt16 => return .prim .uint16
      | ``UInt32 => return .prim .uint32
      | ``UInt64 => return .prim .uint64
      | ``USize => return .prim .usize
      | ``Int8 => return .prim .int8
      | ``Int16 => return .prim .int16
      | ``Int32 => return .prim .int32
      | ``Int64 => return .prim .int64
      | ``ISize => return .prim .isize
      | ``ByteArray => return .prim .byteArray
      | ``FloatArray => return .prim .floatArray
      -- `Ordering` is built and matched as data (`Ordering.lt`, …): three
      -- constructors, none with a field
      | ``Ordering => return .enum 3 (shift := -1)
      -- `Unit` has one value, which is `{ tag: 0 }`: a one-constructor enum
      | ``Unit | ``PUnit => return .enum 1 (shift := 0)
      -- both constructors of `Decidable` carry nothing but a proof, so a `Decidable` is
      -- the boolean it decides — which is also how a `cases` on one is compiled
      | ``Decidable => return .prim .bool
      | ``lcErased | ``lcAny => return .typeParam
      | ``Array => match args[0]? with
        | some α => return .array (← toRTyIn env self blocked fuel α)
        | none => throw "`Array` without an element type"
      | ``List => match args[0]? with
        | some α => return .list (← toRTyIn env self blocked fuel α)
        | none => throw "`List` without an element type"
      | ``Thunk => match args[0]? with
        | some α => return .thunk (← toRTyIn env self blocked fuel α)
        | none => throw "`Thunk` without a value type"
      | ``Task => match args[0]? with
        | some α => return .task (← toRTyIn env self blocked fuel α)
        | none => throw "`Task` without a value type"
      | _ => toDeclRTy env self blocked fuel n args

/-- The `RTy` of a declaration applied to type arguments: an occurrence of the recursive
    declaration being read, the shape of an inductive read off its constructors, or the
    unfolding of a type synonym. -/
partial def toDeclRTy (env : Environment) (self : Option SelfScope) (blocked : List Name)
    (fuel : Nat) (n : Name) (args : Array Expr) : Except String RTy := do
  if fuel == 0 then
    throw "a type is too deeply nested for the backend to read"
  match self with
  | some sc =>
    match sc.idxOf? n with
    | some i =>
        if sc.args.size ≤ args.size && sc.args == args.extract 0 sc.args.size then
          return .self i
        else
          throw s!"`{n}` occurs inside itself at other type arguments, \
            which the backend does not model"
    | none => pure ()
  | none => pure ()
  if blocked.contains n then
    throw s!"`{n}` occurs inside a recursive declaration nested in it, which the \
      backend does not model"
  match env.find? n with
  | some (.inductInfo iv) => toInductiveRTy env self blocked fuel iv args
  | some (.defnInfo dv) =>
      -- a type synonym: unfold it and read what it stands for
      if (resultOfForalls dv.type).isSort then
        toRTyIn env self blocked (fuel - 1) (dv.value.beta args)
      else
        throw s!"`{n}` is not a type the backend models"
  | _ => throw s!"`{n}` is not a type the backend models"

/-- The shape of an inductive declaration, read off its constructors at the type
    arguments it is applied to. -/
partial def toInductiveRTy (env : Environment) (self : Option SelfScope)
    (blocked : List Name) (fuel : Nat) (iv : InductiveVal) (args : Array Expr) :
    Except String RTy := do
  if iv.isUnsafe then
    throw s!"`{iv.name}` is an unsafe inductive"
  if iv.numIndices != 0 then
    throw s!"`{iv.name}` is an indexed family, whose layout depends on its indices"
  if (resultOfForalls iv.type) == .sort .zero then
    throw s!"`{iv.name}` is a proposition, which carries nothing at run time"
  if iv.ctors.isEmpty then
    throw s!"`{iv.name}` has no constructors, so it has no values at run time"
  if args.size < iv.numParams then
    throw s!"`{iv.name}` is applied to fewer type arguments than it takes"
  let params := args.extract 0 iv.numParams
  if iv.all.length > 1 then
    -- a mutual block: every member is read at once, and `.self i` is member `i`
    let sc : SelfScope := { members := iv.all, args := params }
    let blocked' := blocked ++ (match self with | some s => s.members | none => [])
    let ms ← iv.all.mapM fun m => do
      match env.find? m with
      | some (.inductInfo miv) => do
          if miv.ctors.isEmpty then
            throw s!"`{miv.name}` has no constructors, so it has no values at run time"
          let l ← miv.ctors.mapM fun cn =>
            ctorFieldsRTy env (some sc) blocked' (fuel - 1) cn params
          match l with
          | [[f]] => return FamMember.alias f
          | _ => return FamMember.ctors l
      | _ => throw s!"`{m}` is a member of a mutual block the backend cannot read"
    match iv.all.idxOf? iv.name with
    | some i => return .mutualRecursiveFamily ms i
    | none => throw s!"`{iv.name}` is not a member of its own mutual block"
  else
    -- a recursive declaration opens a `.self` scope; a non-recursive one is read in the
    -- scope it is used in, so an `Option Tree` inside `Tree` keeps pointing at `Tree`
    let sc : Option SelfScope :=
      if iv.isRec then some { members := [iv.name], args := params } else self
    -- a recursive declaration opens a *new* `.self` scope, so the one it is nested in
    -- becomes unreachable: the type language has one `.self` binder per recursive
    -- shape, and the inner one shadows the outer.  An occurrence of the outer one is
    -- refused where it happens, which is rare; nesting itself is not.
    let blocked' :=
      if iv.isRec then blocked ++ (match self with | some s => s.members | none => [])
      else blocked
    let l ← iv.ctors.mapM fun cn => ctorFieldsRTy env sc blocked' (fuel - 1) cn params
    let recursive := iv.isRec && l.any fun fs => fs.any RTy.hasSelf
    if recursive then
      match l with
      | [[f]] => return .recAlias f
      | [fs] => return .recObject fs
      | _ => return .recTaggedUnion l
    else
      match l with
      | [[f]] => return f                         -- a newtype: the wrapper is erased
      | [fs] => return (if fs.isEmpty then .enum 1 (shift := 0) else .record fs)
      -- a declaration with no constructors at all has no values, and is refused above
      | [] => throw s!"`{iv.name}` has no constructors, so it has no values at run time"
      | c :: cs =>
        if (c :: cs).all (·.isEmpty) then
          return .enum (c :: cs).length (by simp) 0
        else return .taggedUnion (c :: cs)

/-- The types of the runtime fields of one constructor, in declaration order, with the
    type parameters instantiated and the fields that carry nothing at run time dropped —
    exactly the fields LCNF passes to the constructor. -/
partial def ctorFieldsRTy (env : Environment) (self : Option SelfScope)
    (blocked : List Name) (fuel : Nat) (cn : Name) (params : Array Expr) :
    Except String (List RTy) := do
  match env.find? cn with
  | some (.ctorInfo ci) => do
      let t ← instParams ci.numParams params ci.type
      go ci.numFields t []
  | _ => throw s!"`{cn}` is not a constructor"
where
  /-- Collect the next `k` binder types, dropping the ones that carry nothing. -/
  go : Nat → Expr → List RTy → Except String (List RTy)
    | 0, _, acc => .ok acc.reverse
    | k + 1, .forallE _ a b _, acc =>
        let b' := b.instantiate1 (.const ``lcAny [])
        if isTypeOrProofTy env #[] a then go k b' acc
        else do
          let t ← toRTyIn env self blocked fuel a
          go k b' (t :: acc)
    | _, _, _ => .error s!"`{cn}` has fewer fields than its declaration says"

end

/-- The `Ty` of an LCNF type: a closed type, mentioning no recursive declaration it is
    not part of. -/
def toTy (env : Environment) (e : Expr) : Except String Ty := do
  let r ← toRTyIn env none [] tyFuel e
  match LakeJs.Layout.instRTy (fun _ => none) r with
  | some t => return t
  | none => throw "a type escapes the recursive declaration it belongs to"

/-- Strip `n` parameters off a function type, to find what it answers with. -/
def stripArrows : Nat → Ty → Ty
  | 0, ty => ty
  | n + 1, .fn _ ret => stripArrows n ret
  | _, ty => ty


/-! ## The operations a call is translated into directly

A call of one of the declarations below is not a call of anything the module declares:
it is the operation itself, applied to the arguments of the call.  Almost every one of
them is a Lean function the runtime implements, and so a row of the catalogue
`LakeJs.Externs` — `Nat.add` is `lean_nat_add`, and `LakeJs.EmitJs` decides whether that
prints as `a + b` or as a call of the runtime function.  The handful that are *not*
`@[extern]` functions are the `JsOp` of `LakeJs.Expr`. -/

/-- An operation a call becomes directly: a Lean function of the extern catalogue, or one
    of the few operations that are not Lean functions. -/
inductive DirectOp : List Ty → Ty → Type where
  /-- A function Lean implements with `@[extern]`. -/
  | ext : ∀ {σs : List Ty} {τ : Ty}, Externs σs τ → DirectOp σs τ
  /-- An operation that is JavaScript’s rather than Lean’s. -/
  | js : ∀ {σs : List Ty} {τ : Ty}, JsOp σs τ → DirectOp σs τ

/-- The operation applied to exactly the arguments its type asks for. -/
def DirectOp.apply {Sg : Sig} {Γ : Ctx} {σs : List Ty} {τ : Ty} :
    DirectOp σs τ → Spine Sg Γ σs → Term Sg Γ τ
  | .ext e, args => .callExtern e args
  | .js o, args => .jsOp o args

/-- An operation together with the types it is applied at. -/
structure SomeDirect where
  /-- The types of its arguments. -/
  {σs : List Ty}
  /-- What it answers with. -/
  {τ : Ty}
  /-- The operation. -/
  op : DirectOp σs τ

/-- The Lean declarations a call becomes an operation of, and which operation — at the
    types of the call it is looking at, since both `Externs` and `JsOp` carry them.

    A name that is missing here is not missing from the backend: a call of any other
    `@[extern]` function is recognised further down (`externFor?`) and printed as a call
    of the runtime function.  What this table adds is the *shape*: the operation is
    applied to the arguments of the call at once, and is eta-expanded where the call
    gives it none. -/
def directFor (n : Name) (argTys : List Ty) (ret : Ty) : Option SomeDirect :=
  let arg (i : Nat) : Ty := argTys[i]?.getD Ty.typeParam
  let elemOf : Ty → Ty := fun t => match t with | .array α => α | _ => Ty.typeParam
  match n with
  | ``Nat.add => some ⟨.ext .lean_nat_add⟩
  | ``Nat.mul => some ⟨.ext .lean_nat_mul⟩
  | ``Nat.sub => some ⟨.ext .lean_nat_sub⟩
  | ``Nat.div => some ⟨.ext .lean_nat_div⟩
  | ``Nat.mod => some ⟨.ext .lean_nat_mod⟩
  | ``Nat.pred => some ⟨.ext .lean_nat_pred⟩
  | ``Nat.beq => some ⟨.ext .lean_nat_beq⟩
  | ``Nat.decEq | ``instDecidableEqNat => some ⟨.ext .lean_nat_dec_eq⟩
  | ``Nat.ble => some ⟨.ext .lean_nat_ble⟩
  | ``Nat.decLe => some ⟨.ext .lean_nat_dec_le⟩
  -- Lean implements `Nat.blt` with the runtime function of `Nat.decLt`
  | ``Nat.blt | ``Nat.decLt => some ⟨.ext .lean_nat_dec_lt⟩
  | ``Int.add => some ⟨.ext .lean_int_add⟩
  | ``Int.sub => some ⟨.ext .lean_int_sub⟩
  | ``Int.mul => some ⟨.ext .lean_int_mul⟩
  | ``Int.neg => some ⟨.ext .lean_int_neg⟩
  | ``Int.decEq => some ⟨.ext .lean_int_dec_eq⟩
  | ``Int.decLt => some ⟨.ext .lean_int_dec_lt⟩
  | ``Int.decLe => some ⟨.ext .lean_int_dec_le⟩
  -- `Int.ofNat` is `lean_nat_to_int`, which is the identity on the value: a `Nat` and a
  -- non-negative `Int` have the same JavaScript representation.  Recording it as the
  -- reinterpretation it is keeps it out of the way of the optimiser, which may then
  -- substitute the value it reads through it
  | ``Int.ofNat => some ⟨.js (.cast Ty.nat Ty.int)⟩
  | ``Int.toNat => some ⟨.ext .lean_int_to_nat⟩
  | ``Int.natAbs => some ⟨.ext .lean_nat_abs⟩
  -- `Bool.and`, `Bool.or` and `Bool.not` are Lean functions, but not `@[extern]` ones
  | ``Bool.and => some ⟨.js .boolAnd⟩
  | ``Bool.or => some ⟨.js .boolOr⟩
  | ``Bool.not => some ⟨.js .boolNot⟩
  | ``String.append => some ⟨.ext .lean_string_append⟩
  -- `String.push` is *not* string concatenation: its second argument is a `Char`, which
  -- is not a `String`, so it goes to the extern `lean_string_push` instead
  | ``String.length => some ⟨.ext .lean_string_length⟩
  | ``String.decEq | ``instDecidableEqString => some ⟨.ext .lean_string_dec_eq⟩
  -- Lean decides `Bool` and `Char` equality by a match rather than with a runtime
  -- function, and both are `===` on the representation the backend gives them
  | ``instDecidableEqBool => some ⟨.js .boolBEq⟩
  | ``instDecidableEqChar => some ⟨.js .charBEq⟩
  | ``Array.size => some ⟨.ext (.lean_array_get_size (elemOf (arg 0)))⟩
  | ``Array.push => some ⟨.ext (.lean_array_push (elemOf (arg 0)))⟩
  | ``Array.getInternal => some ⟨.ext (.lean_array_fget (elemOf (arg 0)))⟩
  | ``Array.mkEmpty | ``Array.emptyWithCapacity =>
      some ⟨.ext (.lean_empty_array_with_capacity
        (match ret with | .array α => α | _ => Ty.typeParam))⟩
  | ``UInt8.add => some ⟨.ext .lean_uint8_add⟩
  | ``UInt16.add => some ⟨.ext .lean_uint16_add⟩
  | ``UInt32.add => some ⟨.ext .lean_uint32_add⟩
  | ``UInt64.add => some ⟨.ext .lean_uint64_add⟩
  | ``USize.add => some ⟨.ext .lean_usize_add⟩
  | ``UInt8.sub => some ⟨.ext .lean_uint8_sub⟩
  | ``UInt16.sub => some ⟨.ext .lean_uint16_sub⟩
  | ``UInt32.sub => some ⟨.ext .lean_uint32_sub⟩
  | ``UInt64.sub => some ⟨.ext .lean_uint64_sub⟩
  | ``USize.sub => some ⟨.ext .lean_usize_sub⟩
  | ``UInt32.mul => some ⟨.ext .lean_uint32_mul⟩
  | ``UInt64.mul => some ⟨.ext .lean_uint64_mul⟩
  | ``UInt32.decEq => some ⟨.ext .lean_uint32_dec_eq⟩
  | ``UInt64.decEq => some ⟨.ext .lean_uint64_dec_eq⟩
  | ``Float.add => some ⟨.ext .lean_float_add⟩
  | ``Float.sub => some ⟨.ext .lean_float_sub⟩
  | ``Float.mul => some ⟨.ext .lean_float_mul⟩
  | ``Float.div => some ⟨.ext .lean_float_div⟩
  | ``Float.decLt => some ⟨.ext .lean_float_decLt⟩
  | ``Float.decLe => some ⟨.ext .lean_float_decLe⟩
  -- deciding a proposition and reading the answer as a boolean costs nothing at run time
  | ``Decidable.decide => some ⟨.js (.cast (arg 0) ret)⟩
  | ``toString => some ⟨.js (.toStr (arg 0))⟩
  | _ => none

/-! ## Class instances

A class instance is unboxed: a declaration whose result is a class with fields
`f₁ … f_k` becomes `k` declarations, and a parameter of such a class becomes `k`
parameters.  `InstPlan` is what the translation needs to know about one of them. -/

/-- The fields a class instance is unboxed into. -/
structure InstPlan where
  /-- The name and type of each runtime field, in the order the constructor has them.
      The name is the *class field's* name, which is what the constant the field is
      unboxed into is called (`instToStringExpr_toString`); it is not a name in the
      emitted data, which is positional. -/
  fields : List (String × Ty)
  deriving Inhabited

/-- How many values an unboxed instance is. -/
def InstPlan.size (p : InstPlan) : Nat := p.fields.length

/-- The types of the fields, in order. -/
def InstPlan.tys (p : InstPlan) : List Ty := p.fields.map (·.2)

/-- The type of the instance as **one** value, where it has to be passed as one: a
    record of its fields.  A class with a single field is a newtype, so that type is the
    field's own type — there is no wrapper at run time. -/
def InstPlan.boxedTy (p : InstPlan) : Ty :=
  match p.tys with
  | [t] => t
  | ts => .record ts

/-- The JavaScript name the `i`-th field of instance `base` is bound to. -/
def instFieldName (base : String) (field : String) : String := base ++ "_" ++ field

/-! ## The translation state -/

/-- What the translation of one declaration needs to know. -/
structure Ctx' where
  /-- The environment the `.olean` files were read into. -/
  env : Environment
  /-- The declaration being compiled, when it may call itself. -/
  self : Option Name
  /-- How many parameters it has. -/
  selfArity : Nat := 0
  /-- The mutually recursive group being compiled into **one** dispatch loop: every
      member of the group, with the tag that selects it inside the loop.  A tail call
      to any of them is a `Body.cont` of that loop, so a mutually tail-recursive group
      costs no JavaScript stack at all. -/
  group : Std.HashMap Name Nat := {}
  /-- How many argument slots the merged loop has.  Loop variable `0` is the tag and
      loop variable `j + 1` is slot `j`. -/
  groupSlots : Nat := 0
  /-- Which slot each parameter of each member is held in (`LakeJs.Compile`,
      `groupSlotAlloc`): parameter `k` of member `m` is slot `groupArgSlots[m][k]`.  Two
      members share a slot only where they agree on its type, so no slot is widened; a
      group whose members agree pointwise — the ordinary case — has parameter `k` in slot
      `k`, as it always did. -/
  groupArgSlots : Std.HashMap Name (List Nat) := {}
  /-- The declarations of this module, which are referred to by name. -/
  compiled : NameSet := {}
  /-- The declarations of this module that are class instances, and the fields they are
      unboxed into. -/
  instOf : Std.HashMap Name InstPlan := {}
  /-- Which declarations of this module have had a parameter split into the fields of an
      instance, and how. -/
  paramPlan : Std.HashMap Name (List (Option InstPlan)) := {}
  /-- The JavaScript name each declaration was given, where it is not `jsName` of it:
      `LakeJs.Compile` hands out one name per declaration, so that two Lean names that
      `jsName` spells alike — and a name that clashes with the constant an instance is
      unboxed into — stay two names in the output. -/
  jsNames : Std.HashMap Name String := {}

/-- Where a local binder is.  A binder of a class type is *several* binders — one per
    field of the instance — and a local that is just a nullary instance of the module is
    no binder at all, since its fields are top-level declarations. -/
inductive Binding where
  /-- One binder, at this absolute depth. -/
  | one (depth : Nat)
  /-- A binder that was dropped: it stood for a type or a proof, which carries nothing
      at run time, so there is no JavaScript variable for it and every argument
      position that uses it is dropped too. -/
  | erased
  /-- An instance split into one binder per field, at these absolute depths. -/
  | split (plan : InstPlan) (depths : List Nat)
  /-- A nullary instance of this module: its fields are the declarations
      `base_f₁ … base_f_k`. -/
  | instGlobal (base : String) (plan : InstPlan)
  deriving Inhabited

/-- Where each local binder is. -/
abbrev VarMap := Std.HashMap FVarId Binding

/-- The join points in scope, to be inlined at their jumps. -/
abbrev JpMap := Std.HashMap FVarId (Array Param × Code)

/-- How many jumps to this join point a block holds.  A join point with one jump is
    better inlined — that is what LCNF's own join points are for — but one with several
    is duplicated once per jump, so it is bound as a local function instead, and its
    jumps become calls of it.  A join point that *continues the enclosing loop* cannot be
    a function, and is inlined whatever this says (`LakeJs.FromLcnf.transBody`). -/
partial def jumpCount (f : FVarId) : Code → Nat
  | .let _ k => jumpCount f k
  | .fun d k | .jp d k => jumpCount f d.value + jumpCount f k
  | .jmp g _ => if g == f then 1 else 0
  | .cases cs => cs.alts.foldl (init := 0) fun n a => n + jumpCount f a.getCode
  | .return _ | .unreach _ => 0

/-- How big a block is, counted in LCNF nodes.  Binding a join point as a function costs
    a closure at run time and a name in the output, so it is only worth it for a body
    that is more than a couple of operations; a small one is cheaper duplicated. -/
partial def codeSize : Code → Nat
  | .let _ k => codeSize k + 1
  | .fun d k | .jp d k => codeSize d.value + codeSize k + 1
  | .jmp _ _ => 1
  | .cases cs => cs.alts.foldl (init := 1) fun n a => n + codeSize a.getCode
  | .return _ | .unreach _ => 1

/-- The smallest join-point body that is worth binding as a function rather than
    duplicating at each of its jumps. -/
def jpShareSize : Nat := 6

/-- Does this `let` value call the declaration being compiled, or a member of its mutual
    group? -/
def letValueMentionsLoop (self : Option Name) (group : Std.HashMap Name Nat) :
    LetValue → Bool
  | .const n _ _ => self == some n || group.contains n
  | _ => false

/-- Does this block call the declaration being compiled, or a member of its mutual group
    — directly, or through a join point it jumps to?  Such a block must **not** become a
    local function: a tail call to the declaration being compiled is the `continue` of
    its loop, and a closure cannot continue a loop it is not in, so the call would become
    a recursive call and grow the stack. -/
partial def mentionsLoopCall (self : Option Name) (group : Std.HashMap Name Nat)
    (jps : JpMap) : Code → Bool
  | .let d k =>
      letValueMentionsLoop self group d.value || mentionsLoopCall self group jps k
  | .fun d k | .jp d k =>
      mentionsLoopCall self group jps d.value || mentionsLoopCall self group jps k
  | .jmp f _ =>
      match jps[f]? with
      | some (_, body) => mentionsLoopCall self group jps body
      | none => false
  | .cases cs => cs.alts.any fun a => mentionsLoopCall self group jps a.getCode
  | .return _ | .unreach _ => false

/-! ## Branches Lean marked unreachable

Every expression the backend emits is a *value*, so there is nothing to put in a branch
Lean proved impossible — no `throw`, no `undefined`.  Such a branch is therefore
**dropped** before the dispatch is built: the tag it tests is never tested, and control
reaches a sibling branch instead.  That is faithful precisely because the branch cannot
be taken, and it keeps every term pure and reorderable. -/

/-- Is this block unreachable — does every path through it end in `.unreach`?  A
    binding in front of an unreachable block is dead, and a `cases` all of whose
    branches are unreachable is itself unreachable; a jump is unreachable when the join
    point it goes to is. -/
partial def codeIsUnreach (jps : JpMap) : Code → Bool
  | .unreach _ => true
  | .let _ k | .fun _ k => codeIsUnreach jps k
  | .jp d k => codeIsUnreach (jps.insert d.fvarId (d.params, d.value)) k
  | .cases cs => cs.alts.all fun a => codeIsUnreach jps a.getCode
  | .jmp f _ =>
      match jps[f]? with
      | some (_, body) => codeIsUnreach jps body
      | none => false
  | .return _ => false

/-- The alternatives worth compiling: the ones that are not unreachable.  If they all
    are, the list is left alone, and the declaration is refused when the first of them
    is translated — a function that can never answer is not a value either. -/
def liveAlts (jps : JpMap) (alts : List Alt) : List Alt :=
  let live := alts.filter fun a => !codeIsUnreach jps a.getCode
  if live.isEmpty then alts else live

/-- A term of some type in context `Γ`. -/
abbrev Res (Sg : Sig) (Γ : Ctx) := Except String (SomeTerm Sg Γ)

/-- The term of the variable at absolute depth `d`. -/
def varAtDepth {Sg : Sig} (Γ : Ctx) (d : Nat) : Except String (SomeTerm Sg Γ) :=
  let len := Γ.length
  if d < len then
    let i := len - 1 - d
    match Ctx.get? Γ i with
    | none => .error s!"variable at depth {d} is out of scope"
    | some τ =>
      match Var.at? Γ i τ with
      | some v => .ok ⟨τ, .var v⟩
      | none => .error s!"variable at depth {d} has a type the backend cannot compare"
  else
    .error s!"variable at depth {d} is out of scope (context has {len})"

/-- Read a term at another type.  Where the two types are known to agree, the term is
    unchanged; where they are not — the LCNF type was a user-defined type, a proof or an
    erased value, all of which `Ty` sees as one opaque runtime value — the term is
    wrapped in `JsOp.cast`, which prints as the term itself.  Nothing is inserted into
    the output either way; what changes is only which `Ty` the backend ascribes. -/
def coerce {Sg : Sig} (σ : Ty) {Γ : Ctx} (t : SomeTerm Sg Γ) : Term Sg Γ σ :=
  match σ, t with
  -- LCNF spells a character by its code point, and the backend spells it by the
  -- one-character string it is at run time: `'x'` is `"x"`, not `120`
  | .prim .char, ⟨_, .lit (.nat n)⟩ => .lit (.char (Char.ofNat n))
  | σ, t =>
    match Term.coerce? σ t.2 with
    | some t' => t'
    | none => .jsOp (.cast t.1 σ) (.cons t.2 .nil)

/-- A natural number literal, read at the type the LCNF `let` gives it.  LCNF holds the
    constants of every integral type as a natural number, so this is where a `UInt8`
    constant becomes a literal *of* `UInt8` rather than a `Nat` cast to it: the two are
    the same value in Lean, but a `Nat` may be a `BigInt` while a `UInt8` is always a
    number, and a literal knows which one it has to print as. -/
def natLitAt {Sg : Sig} {Γ : Ctx} (ty : Ty) (n : Nat) : SomeTerm Sg Γ :=
  match ty with
  | .prim .int => ⟨Ty.int, .lit (.int (Int.ofNat n))⟩
  -- LCNF spells a character by its code point; the backend spells it by the
  -- one-character string it is at run time, so `'x'` prints as `"x"` and not `120`
  | .prim .char => ⟨Ty.char, .lit (.char (Char.ofNat n))⟩
  | .prim .uint8 => ⟨Ty.uint8, .lit (.uint8 (UInt8.ofNat n))⟩
  | .prim .uint16 => ⟨Ty.uint16, .lit (.uint16 (UInt16.ofNat n))⟩
  | .prim .uint32 => ⟨Ty.uint32, .lit (.uint32 (UInt32.ofNat n))⟩
  | .prim .uint64 => ⟨Ty.uint64, .lit (.uint64 (UInt64.ofNat n))⟩
  | .prim .usize => ⟨Ty.usize, .lit (.usize (USize.ofNat n))⟩
  | .prim .int8 => ⟨Ty.int8, .lit (.int8 (Int8.ofNat n))⟩
  | .prim .int16 => ⟨Ty.int16, .lit (.int16 (Int16.ofNat n))⟩
  | .prim .int32 => ⟨Ty.int32, .lit (.int32 (Int32.ofNat n))⟩
  | .prim .int64 => ⟨Ty.int64, .lit (.int64 (Int64.ofNat n))⟩
  | .prim .isize => ⟨Ty.isize, .lit (.isize (ISize.ofNat n))⟩
  | .prim (.bitvec w h) => ⟨Ty.bitvec w h, .lit (.bitvec (BitVec.ofNat w n))⟩
  | .prim .stringPos => ⟨Ty.stringPos, .lit (.stringPos n)⟩
  | _ => ⟨Ty.nat, .lit (.nat n)⟩

/-- Build a spine of the given types, reading each argument at the type its parameter
    has.  There is no value to invent for a missing argument — nothing is erased into
    an `undefined` any more — so a call with too few arguments has no spine. -/
def mkSpine? {Sg : Sig} {Γ : Ctx} :
    (σs : List Ty) → List (SomeTerm Sg Γ) → Option (Spine Sg Γ σs)
  | [], _ => some .nil
  | σ :: σs, t :: ts => (mkSpine? σs ts).map (Spine.cons (coerce σ t))
  | _ :: _, [] => none

/-- `mkSpine?`, with the failure reported. -/
def mkSpine {Sg : Sig} {Γ : Ctx} (σs : List Ty) (ts : List (SomeTerm Sg Γ)) :
    Except String (Spine Sg Γ σs) :=
  match mkSpine? σs ts with
  | some sp => .ok sp
  | none => .error s!"a call is given fewer arguments ({ts.length}) than the function takes ({σs.length})"

/-- The value that fills an argument slot of a merged dispatch loop that the member
    entering the loop does not have: the members of a group need not all use every slot,
    and a slot a member does not use is never read by it.

    It is the *empty* value of the slot’s own type — `0`, `""`, `false`, `[]` — rather
    than a `0` at whatever type the slot has, so that a slot keeps holding values of one
    JavaScript type and an engine can keep it unboxed.  Each of them is a pure, total
    value, so the term stays pure and reorderable; nothing is thrown and nothing is
    `undefined`. -/
def padValue {Sg : Sig} {Γ : Ctx} : (σ : Ty) → Term Sg Γ σ
  | .prim .string => .lit (.string "")
  | .prim .bool => .lit (.bool false)
  | .prim .char => .lit (.char ' ')
  | .prim .float => .lit (.float 0.0)
  | .prim .float32 => .lit (.float32 0.0)
  | .array α => .callExtern (.lean_empty_array_with_capacity α) (.cons (.lit (.nat 0)) .nil)
  | σ => coerce σ ⟨Ty.nat, .lit (.nat 0)⟩

/-- A spine of the given types, with the slots no argument was given for filled by
    `fill`, which is told the position it is filling.  This is what a jump into a merged
    dispatch loop uses: the member being entered need not have an argument for every
    slot of the loop. -/
def mkSpineFill {Sg : Sig} {Γ : Ctx} (fill : Nat → Except String (SomeTerm Sg Γ)) :
    (σs : List Ty) → Nat → List (SomeTerm Sg Γ) → Except String (Spine Sg Γ σs)
  | [], _, _ => .ok .nil
  | σ :: σs, j, [] => do
      let t ← fill j
      return .cons (coerce σ t) (← mkSpineFill fill σs (j + 1) [])
  | σ :: σs, j, t :: ts =>
      return .cons (coerce σ t) (← mkSpineFill fill σs (j + 1) ts)

/-- A spine of the given types from a value *per position*, the positions that have none
    being filled by `fill`.  This is what a jump into a merged dispatch loop uses: the
    member being entered has an argument for its own slots and for no others. -/
def mkSpineSome {Sg : Sig} {Γ : Ctx} (fill : Nat → Except String (SomeTerm Sg Γ)) :
    (σs : List Ty) → Nat → List (Option (SomeTerm Sg Γ)) → Except String (Spine Sg Γ σs)
  | [], _, _ => .ok .nil
  | σ :: σs, j, ts => do
      let t ← match ts.head?.join with
        | some t => pure t
        | none => fill j
      return .cons (coerce σ t) (← mkSpineSome fill σs (j + 1) ts.tail)

/-- A spine of the given types from a value *per position*, the positions that have none
    being filled by `padValue`.  This is what the wrapper of a member of a merged group
    uses: it passes its own arguments in its own slots, and the slots it has no argument
    for are never read. -/
def mkSpineSomePad {Sg : Sig} {Γ : Ctx} :
    (σs : List Ty) → List (Option (SomeTerm Sg Γ)) → Spine Sg Γ σs
  | [], _ => .nil
  | σ :: σs, ts =>
      let t : Term Sg Γ σ :=
        match ts.head?.join with
        | some t => coerce σ t
        | none => padValue σ
      .cons t (mkSpineSomePad σs ts.tail)

/-- A spine of the given types, with the slots no argument was given for filled by
    `padValue`.  This is only for the argument slots of a merged dispatch loop. -/
def mkSpinePad {Sg : Sig} {Γ : Ctx} :
    (σs : List Ty) → List (SomeTerm Sg Γ) → Spine Sg Γ σs
  | [], _ => .nil
  | σ :: σs, [] => .cons (padValue σ) (mkSpinePad σs [])
  | σ :: σs, t :: ts => .cons (coerce σ t) (mkSpinePad σs ts)

/-- A spine of arguments whose types are read off the arguments themselves. -/
def spineOfTerms {Sg : Sig} {Γ : Ctx} :
    List (SomeTerm Sg Γ) → Σ σs : List Ty, Spine Sg Γ σs
  | [] => ⟨[], .nil⟩
  | t :: ts =>
    let rest := spineOfTerms ts
    ⟨t.1 :: rest.1, .cons t.2 rest.2⟩

/-! ### Reading and building values

The data operations of `Term` (`Term.ctor`, `Term.proj`, `Term.tagOf`, `Term.caseTag`)
ask for the evidence that the type involved really has that constructor, that field or
those tags — evidence a `Ty` provides through its layout (`LakeJs.Layout`).  They are
now the *only* data operations there are: the unchecked ones are gone, and so is the
`Ty.dynamic` they lived at, so the smart constructors below either build a checked
operation or **refuse** the declaration.

There is one case in which a type has no layout and the access is still right: a
**newtype**, whose single constructor and single field are erased.  Building it is the
field itself and reading its field is the value itself — no `{ tag: 0, _1: … }` is
emitted for it, and nothing is read out of one. -/

/-- Field `j` of constructor `i` of `s`.  When the type of `s` has a layout with that
    field, this is the *checked* `Term.proj`, and the type of the result is the type the
    layout gives the field.  When it has no layout at all, the only access that can be
    right is field `0` of constructor `0` — the field of an erased newtype — which is
    the value itself, read at the type the wrapper stood for. -/
def projAt {Sg : Sig} {Γ : Ctx} (s : SomeTerm Sg Γ) (i j : Nat) :
    Except String (SomeTerm Sg Γ) :=
  match h : s.1.fieldTy? i j with
  | some fty => .ok ⟨fty, .proj s.2 i j h⟩
  | none =>
    if s.1.isTagged then
      .error s!"a value of type `{s.1}` has no field {j} of constructor {i}"
    else if i == 0 && j == 0 then
      match s.1.aliasUnfold? with
      | some u => .ok ⟨u, coerce u s⟩
      | none => .ok s
    else
      .error s!"a value of type `{s.1}` has no field {j} of constructor {i}"

/-- Field `j` of constructor `i` of `s`, read at the type `ty`. -/
def projAtTy {Sg : Sig} {Γ : Ctx} (ty : Ty) (s : SomeTerm Sg Γ) (i j : Nat) :
    Except String (Term Sg Γ ty) := do
  return coerce ty (← projAt s i j)

/-- The runtime tag of `s`: the checked `Term.tagOf`.  A value whose type has no
    constructors has no tag, and a dispatch on one is refused. -/
def tagAt {Sg : Sig} {Γ : Ctx} (s : SomeTerm Sg Γ) :
    Except String (Term Sg Γ (.prim .nat)) :=
  if h : s.1.isTagged = true then .ok (.tagOf s.2 h)
  else .error s!"a value of type `{s.1}` has no runtime tag to dispatch on"

/-- Constructor `i` of `ty`, applied to these fields: the *checked* `Term.ctor`.  A type
    with no layout has only one constructor that can be right — the erased wrapper of a
    newtype, which is its field. -/
def ctorAt {Sg : Sig} {Γ : Ctx} (ty : Ty) (i : Nat) (vals : List (SomeTerm Sg Γ)) :
    Except String (SomeTerm Sg Γ) :=
  match h : ty.ctorFields? i with
  | some fs =>
      if fs.length == vals.length then
        match mkSpine? fs vals with
        | some sp => .ok ⟨ty, .ctor i fs h sp⟩
        | none => .error s!"constructor {i} of `{ty}` is given a field of the wrong type"
      else
        .error s!"constructor {i} of `{ty}` takes {fs.length} fields, not {vals.length}"
  | none =>
    if ty.isTagged then
      .error s!"`{ty}` has no constructor {i}"
    else
      match i, vals with
      | 0, [v] => .ok ⟨ty, coerce ty v⟩
      | _, _ => .error s!"`{ty}` has no constructor {i}"

/-- A reference to a top-level declaration of the signature.  A name the signature does
    not declare is an error: the translation may not invent one.  A name it declares at
    another type is read at the type wanted here, with the reinterpretation recorded as a
    `JsOp.cast`. -/
def globalTerm {Sg : Sig} {Γ : Ctx} (nm : String) (τ : Ty) : Except String (Term Sg Γ τ) :=
  match GlobalRef.find? Sg nm τ with
  | some r => .ok (.global r)
  | none =>
    match GlobalRef.findAny? Sg nm with
    | some ⟨σ, r⟩ => .ok (.jsOp (.cast σ τ) (.cons (.global r) .nil))
    | none => .error s!"the module signature has no declaration named `{nm}`"

/-- A loop body that never continues is an ordinary term. -/
def bodyToTerm? {Sg : Sig} {Γ : Ctx} {σs : List Ty} {τ : Ty} :
    Body Sg Γ σs τ → Option (Term Sg Γ τ)
  | .ret t => some t
  | .cont _ => none
  | .letB e b => (bodyToTerm? b).map (Term.letE e)
  | .iteB c t e =>
    match bodyToTerm? t, bodyToTerm? e with
    | some a, some b => some (.ite c a b)
    | _, _ => none

/-- The words a JavaScript module may not bind to a declaration: the keywords, the two
    identifiers a module — which is always strict — may not bind (`eval`, `arguments`),
    and the literals.  A Lean declaration called `eval` is real (`RecursionSchemes01`
    has one), and `const eval = …` is a syntax error in a module, so such a name gets a
    `$`. -/
def jsReservedWords : List String :=
  [ "arguments", "await", "break", "case", "catch", "class", "const", "continue",
    "debugger", "default", "delete", "do", "else", "enum", "eval", "export", "extends",
    "false", "finally", "for", "function", "if", "implements", "import", "in",
    "instanceof", "interface", "let", "new", "null", "package", "private", "protected",
    "public", "return", "static", "super", "switch", "this", "throw", "true", "try",
    "typeof", "var", "void", "while", "with", "yield",
    "Infinity", "NaN", "undefined" ]

/-- The JavaScript name of a compiled declaration.  It is only the *base* name: two Lean
    names can map to the same one, and `LakeJs.Compile` gives each declaration a name
    that no other declaration of the module has, starting from this one. -/
def jsName (n : Name) : String :=
  let s := n.toString
  let s := s.map fun ch =>
    if ch.isAlphanum || ch == '_' || ch == '$' then ch else '_'
  let s := match s.toList with
    | [] => "_"
    | c :: _ => if c.isDigit then "_" ++ s else s
  if jsReservedWords.contains s then s ++ "$" else s

/-- The JavaScript name this compilation gave `n`: the one `LakeJs.Compile` handed out,
    and `jsName n` for anything it did not name. -/
def Ctx'.js (c : Ctx') (n : Name) : String := c.jsNames[n]?.getD (jsName n)

/-- Pack an unboxed instance back into one value: `{ tag: 0, _1: …, _2: … }`, a record
    of its fields.  A class with a *single* field is a newtype, and packing it is the
    field itself — the wrapper does not exist at run time. -/
def boxInst {Sg : Sig} {Γ : Ctx} (fields : List (SomeTerm Sg Γ)) :
    Except String (SomeTerm Sg Γ) :=
  match fields with
  | [v] => .ok v
  | fs => ctorAt (.record (fs.map (·.1))) 0 fs

/-- Read field `i` out of an instance that was packed by `boxInst`. -/
def unboxInstField {Sg : Sig} {Γ : Ctx} (plan : InstPlan) (t : SomeTerm Sg Γ)
    (i : Nat) (fty : Ty) : Except String (Term Sg Γ fty) :=
  if plan.fields.length == 1 then .ok (coerce fty t) else projAtTy fty t 0 i

/-- The fields of a nullary instance of this module, as references to the declarations
    they were unboxed into. -/
def instGlobalFields {Sg : Sig} {Γ : Ctx} (base : String) (plan : InstPlan) :
    Except String (List (SomeTerm Sg Γ)) :=
  plan.fields.mapM fun (f, ty) => do
    let t ← globalTerm (instFieldName base f) ty
    return ⟨ty, t⟩

/-- Is this argument one that is dropped: a type, an erased value, or a binder that
    was itself dropped? -/
def isErasedArg (vm : VarMap) : Arg → Bool
  | .type _ => true
  | .erased => true
  | .fvar f => match vm[f]? with | some .erased => true | _ => false

/-! ## The translation itself -/

mutual

/-- An LCNF argument, as one value.  A binder that was split into the fields of an
    instance is packed back into a record here, which is the only place a `Term` ever
    rebuilds one. -/
partial def transArg {Sg : Sig} (Γ : Ctx) (vm : VarMap) (a : Arg) : Res Sg Γ :=
  match a with
  | .erased => .error "an erased argument has no value to translate"
  | .type _ => .error "a type argument has no value to translate"
  | .fvar f =>
    match vm[f]? with
    | some .erased => .error "an erased binder has no value to translate"
    | some (.one d) => varAtDepth Γ d
    | some (.split _ ds) => do
        let fields ← ds.mapM fun d => varAtDepth (Sg := Sg) Γ d
        boxInst fields
    | some (.instGlobal base plan) => do
        let fields ← instGlobalFields (Sg := Sg) (Γ := Γ) base plan
        boxInst fields
    | none => .error "a variable is used outside the binder that introduces it"

/-- An argument, as the list of values it is when the parameter it is passed to has been
    split into the fields of an instance. -/
partial def transArgSplit {Sg : Sig} (Γ : Ctx) (vm : VarMap) (plan : InstPlan) (a : Arg) :
    Except String (List (SomeTerm Sg Γ)) :=
  match a with
  | .erased | .type _ =>
      .error "an instance parameter is given an erased argument"
  | .fvar f =>
    match vm[f]? with
    | some .erased => .error "an instance parameter is given an erased binder"
    | some (.split _ ds) => ds.mapM fun d => varAtDepth (Sg := Sg) Γ d
    | some (.instGlobal base p) => instGlobalFields (Sg := Sg) (Γ := Γ) base p
    | some (.one d) => do
        let t ← varAtDepth (Sg := Sg) Γ d
        plan.fields.zipIdx.mapM fun ((_, ty), i) => do
          return (⟨ty, ← unboxInstField plan t i ty⟩ : SomeTerm Sg Γ)
    | none => .error "a variable is used outside the binder that introduces it"

/-- A list of LCNF arguments, with the erased ones dropped. -/
partial def transArgs {Sg : Sig} (Γ : Ctx) (vm : VarMap) :
    List Arg → Except String (List (SomeTerm Sg Γ))
  | [] => .ok []
  | a :: rest =>
    if isErasedArg vm a then transArgs Γ vm rest
    else do
      let t ← transArg Γ vm a
      let ts ← transArgs Γ vm rest
      return t :: ts

/-- The arguments of a call to a declaration of this module, with every parameter that
    was split into the fields of an instance expanded into those fields. -/
partial def transArgsPlanned {Sg : Sig} (Γ : Ctx) (vm : VarMap) :
    List (Option InstPlan) → List Arg → Except String (List (SomeTerm Sg Γ))
  | _, [] => .ok []
  | [], args => transArgs Γ vm args
  | p :: ps, a :: args =>
    -- the plans are one per Lean parameter, so a dropped argument drops its plan too
    if isErasedArg vm a then transArgsPlanned Γ vm ps args
    else do
      let here ← match p with
        | none => do let t ← transArg Γ vm a; pure [t]
        | some plan => transArgSplit Γ vm plan a
      let rest ← transArgsPlanned Γ vm ps args
      return here ++ rest

/-- Apply a term to arguments, one parameter list at a time.  An extern is curried — its
    type is `σ ⇒ τ ⇒ …` — so this is what saturates it; `LakeJs.EmitJs` then prints the
    saturated application as one call of the runtime function. -/
partial def applyCurried {Sg : Sig} {Γ : Ctx}
    (f : SomeTerm Sg Γ) (args : List (SomeTerm Sg Γ)) : SomeTerm Sg Γ :=
  match f.1, args with
  | _, [] => f
  | .fn ps ret, _ =>
      let n := ps.length
      let taken := args.take (max n 1)
      let rest := args.drop (max n 1)
      let fn : Term Sg Γ (.fn ps ret) := coerce (.fn ps ret) f
      match mkSpine? ps (taken.take n) with
      | some sp => applyCurried ⟨ret, .apN fn sp⟩ rest
      | none => f
  | _, _ => f

/-- The value of an LCNF `let`, at the type the `let` gives it. -/
partial def transLetValue {Sg : Sig} (c : Ctx') (Γ : Ctx) (vm : VarMap) (ty : Ty) :
    LetValue → Res Sg Γ
  | .erased => .error "an erased `let` is dropped before it reaches here"
  | .lit (.nat n) => .ok (natLitAt ty n)
  | .lit (.str s) => .ok ⟨Ty.string, .lit (.string s)⟩
  | .lit (.uint8 v) => .ok (natLitAt ty v.toNat)
  | .lit (.uint16 v) => .ok (natLitAt ty v.toNat)
  -- a `Char` is a `UInt32` in LCNF, and a one-character string in the output
  | .lit (.uint32 v) => .ok (natLitAt ty v.toNat)
  | .lit (.uint64 v) => .ok (natLitAt ty v.toNat)
  | .lit (.usize v) => .ok (natLitAt ty v.toNat)
  | .proj sname idx f => do
      -- a projection of a binder that was split into an instance's fields is that field
      match vm[f]? with
      | some (.split _ ds) =>
          match ds[idx]? with
          | some d => varAtDepth Γ d
          | none => .error "a projection reaches past the fields of an instance"
      | some (.instGlobal base plan) =>
          match plan.fields[idx]? with
          | some (nm, fty) => do
              let t ← globalTerm (Sg := Sg) (Γ := Γ) (instFieldName base nm) fty
              return ⟨fty, t⟩
          | none => .error "a projection reaches past the fields of an instance"
      | _ => do
          let s ← transArg Γ vm (.fvar f)
          -- LCNF projects out of a structure, which has one constructor.  A structure
          -- with a single runtime field is a newtype: it has no wrapper at run time, so
          -- reading its field is reading the value itself.
          if isNewtypeInduct c.env sname then
            return ⟨ty, coerce ty s⟩
          match runtimeFieldIndex c.env sname idx with
          | some j => return ⟨ty, ← projAtTy ty s 0 j⟩
          | none =>
            .error s!"a projection reads field {idx} of `{sname}`, which carries \
              nothing at run time"
  | .fvar f args => do
      let fn ← transArg Γ vm (.fvar f)
      let ts ← transArgs Γ vm args.toList
      let sp := spineOfTerms ts
      let fn' : Term Sg Γ (.fn sp.1 ty) := coerce (.fn sp.1 ty) fn
      return ⟨ty, .apN fn' sp.2⟩
  | .const n _ args => transConst c Γ vm ty n args.toList

/-- A call of a named declaration: a primitive, an extern, a constructor, the projection
    of an unboxed instance, or a call of a declaration of the signature. -/
partial def transConst {Sg : Sig} (c : Ctx') (Γ : Ctx) (vm : VarMap) (ty : Ty)
    (n : Name) (args : List Arg) : Res Sg Γ := do
  let runtimeArgs := args.filter (!isErasedArg vm ·)
  let tyArgs : List Ty := args.filterMap fun a => match a with
    | .type e => (toTy c.env e).toOption
    | _ => none
  -- a projection function of a class, applied to an instance the backend has unboxed
  match projectionOfUnboxed? c Γ vm ty n args with
  | some r => return (← r)
  | none => pure ()
  -- a nullary instance of this module, used as one value
  match c.instOf[n]? with
  | some plan =>
      if (c.paramPlan[n]?.getD []).isEmpty && runtimeArgs.isEmpty then
        let fields ← instGlobalFields (Sg := Sg) (Γ := Γ) (c.js n) plan
        return ← boxInst fields
  | none => pure ()
  let ts ← transArgs Γ vm runtimeArgs
  let argTys := ts.map (·.1)
  -- a call of a compiled declaration passes the parameters that survive to run time:
  -- the emitted function has one JavaScript parameter for each of those, and none for
  -- the types and proofs, which are dropped on both sides
  let named : List Arg → Res Sg Γ := fun given => do
    let plans := c.paramPlan[n]?.getD []
    -- the arguments, at whatever context they are read in: the eta-expansion below reads
    -- them again under the parameters it adds, which is sound because a variable is
    -- named by its *depth*, and a depth does not move when the context grows on top
    let mk : (Δ : Ctx) → Except String (List (SomeTerm Sg Δ)) := fun Δ =>
      if plans.isEmpty then transArgs Δ vm given else transArgsPlanned Δ vm plans given
    let tsNamed ← mk Γ
    -- a declaration is emitted with one JavaScript parameter per run-time parameter, so
    -- a call that gives fewer arguments than that is *not* a call: it is the function
    -- that takes the rest.  Eta-expand it, rather than emitting a call the emitted
    -- definition could not answer.
    match GlobalRef.findAny? Sg (c.js n) with
    | some ⟨.fn ps ret, r⟩ =>
        if tsNamed.length < ps.length then
          let extras := ps.drop tsNamed.length
          let Γ' := extras.reverse ++ Γ
          let tsUnder ← mk Γ'
          let vars ← (List.range extras.length).mapM fun j =>
            varAtDepth (Sg := Sg) Γ' (Γ.length + j)
          match mkSpine? (Sg := Sg) (Γ := Γ') ps (tsUnder ++ vars) with
          | some sp => return ⟨.fn extras ret, .lamN (.apN (.global r) sp)⟩
          | none => transNamed c Γ ty n tsNamed
        else
          transNamed c Γ ty n tsNamed
    | _ => transNamed c Γ ty n tsNamed
  match directFor n argTys ty with
  | some p =>
      if ts.length == p.σs.length then
        return ⟨p.τ, p.op.apply (← mkSpine p.σs ts)⟩
      else if ts.isEmpty then
        -- the primitive is used as a value: eta-expand it, so that what the output holds
        -- is a function of the right arity rather than a call with none
        let Γ' := p.σs.reverse ++ Γ
        let vars ← (List.range p.σs.length).mapM fun j =>
          varAtDepth (Sg := Sg) Γ' (Γ.length + j)
        return ⟨.fn p.σs p.τ, .lamN (p.op.apply (← mkSpine p.σs vars))⟩
      else
        named args
  | none =>
    if n == ``Decidable.isTrue then
      return ⟨Ty.bool, .lit (.bool true)⟩
    else if n == ``Decidable.isFalse then
      return ⟨Ty.bool, .lit (.bool false)⟩
    else if n == ``Bool.true then
      return ⟨Ty.bool, .lit (.bool true)⟩
    else if n == ``Bool.false then
      return ⟨Ty.bool, .lit (.bool false)⟩
    else if n == ``Nat.zero then
      return ⟨Ty.nat, .lit (.nat 0)⟩
    else if n == ``Nat.succ then
      match ts.reverse.head? with
      | some a =>
          let one : Term Sg Γ Ty.nat := .lit (.nat 1)
          return ⟨Ty.nat, .callExtern .lean_nat_add
            (.cons (coerce Ty.nat a) (.cons one .nil))⟩
      | none => return ⟨Ty.nat, .lit (.nat 1)⟩
    else if n == ``Int.negSucc then
      match ts.reverse.head? with
      | some a =>
          let minusOne : Term Sg Γ Ty.int := .lit (.int (-1))
          return ⟨Ty.int, .callExtern .lean_int_sub
            (.cons minusOne (.cons (coerce Ty.int a) .nil))⟩
      | none => return ⟨Ty.int, .lit (.int (-1))⟩
    else
    match c.env.find? n with
    | some (.ctorInfo ci) =>
      -- the constructor of a type the backend represents its own way (`Array.mk`) is
      -- not a constructor of a layout but a *conversion*, which the runtime does
      if isConversionCtor n then
        match externFor? n (tyArgs[0]?.getD Ty.typeParam) (tyArgs[1]?.getD Ty.typeParam) with
        | some ⟨eArgs, eRet, e⟩ => return applyCurried ⟨.fn eArgs eRet, .extern e⟩ ts
        | none => named args
      else
        -- the fields are what follows the type parameters; a field that carries nothing
        -- at run time is dropped, here and in the layout alike
        let tsAll ← transArgs Γ vm (args.drop ci.numParams)
        -- a newtype has no wrapper: building one is its field
        match tsAll with
        | [v] =>
            if isNewtypeInduct c.env ci.induct then return ⟨ty, coerce ty v⟩
            else ctorAt ty ci.cidx tsAll
        | _ => ctorAt ty ci.cidx tsAll
    | _ =>
      match externFor? n (tyArgs[0]?.getD Ty.typeParam) (tyArgs[1]?.getD Ty.typeParam) with
      | some ⟨eArgs, eRet, e⟩ => return applyCurried ⟨.fn eArgs eRet, .extern e⟩ ts
      | none => named args

/-- A call of a declaration of the signature, with the arguments already translated. -/
partial def transNamed {Sg : Sig} (c : Ctx') (Γ : Ctx) (ty : Ty)
    (n : Name) (ts : List (SomeTerm Sg Γ)) : Res Sg Γ := do
  if ts.isEmpty then
    let t ← globalTerm (Sg := Sg) (Γ := Γ) (c.js n) ty
    return ⟨ty, t⟩
  else
    let sp := spineOfTerms ts
    let f ← globalTerm (Sg := Sg) (Γ := Γ) (c.js n) (.fn sp.1 ty)
    return ⟨ty, .apN f sp.2⟩

/-- A call of a class's projection function whose instance argument the backend has
    unboxed: the call *is* the field, applied to whatever else the call passes. -/
partial def projectionOfUnboxed? {Sg : Sig} (c : Ctx') (Γ : Ctx) (vm : VarMap) (_ty : Ty)
    (n : Name) (args : List Arg) : Option (Res Sg Γ) :=
  match c.env.getProjectionFnInfo? n with
  | none => none
  | some pi =>
    if !pi.fromClass then none
    else
      match args[pi.numParams]? with
      | some (.fvar f) =>
        let plan? : Option (InstPlan × Except String (SomeTerm Sg Γ)) :=
          match vm[f]? with
          | some (.split plan ds) =>
            match ds[pi.i]? with
            | some d => some (plan, varAtDepth Γ d)
            | none => none
          | some (.instGlobal base plan) =>
            match plan.fields[pi.i]? with
            | some (nm, fty) =>
              some (plan, do
                let t ← globalTerm (Sg := Sg) (Γ := Γ) (instFieldName base nm) fty
                return ⟨fty, t⟩)
            | none => none
          | _ => none
        match plan? with
        | none => none
        | some (_, field) =>
          some do
            let fieldTerm ← field
            let rest := args.drop (pi.numParams + 1) |>.filter (!isErasedArg vm ·)
            let ts ← transArgs Γ vm rest
            return applyCurried fieldTerm ts
      | _ => none

/-- A local function: a `Term.lamN` whose body is a block that cannot continue a loop. -/
partial def transFun {Sg : Sig} (c : Ctx') (Γ : Ctx) (vm : VarMap) (jps : JpMap)
    (d : FunDecl) : Res Sg Γ := do
  -- a parameter that carries nothing at run time is dropped, here and at every call
  let ps := d.params.toList.filter (!isErasedParam ·)
  let dropped := d.params.toList.filter isErasedParam
  let ptys ← ps.mapM fun p => toTy c.env p.type
  let ret ← toTy c.env d.type
  let base := Γ.length
  let vm0 := dropped.foldl (init := vm) fun m p => m.insert p.fvarId .erased
  let vm' := ps.zipIdx.foldl (init := vm0) fun m (p, i) => m.insert p.fvarId (.one (base + i))
  let body ← transBody { c with self := none, group := {} } (ptys.reverse ++ Γ) vm' jps [] ret d.value
  match bodyToTerm? body with
  | some t => return ⟨.fn ptys ret, .lamN t⟩
  | none => .error "a local function cannot continue the loop of the declaration it is in"

/-- A block of LCNF code, as the body of the loop of the declaration being compiled.
    `σs` are the loop variables and `τ` the answer. -/
partial def transBody {Sg : Sig} (c : Ctx') (Γ : Ctx) (vm : VarMap) (jps : JpMap)
    (σs : List Ty) (τ : Ty) : Code → Except String (Body Sg Γ σs τ)
  | .return f => do
      let t ← transArg Γ vm (.fvar f)
      return .ret (coerce τ t)
  | .unreach _ =>
      .error "the declaration has a branch Lean marked unreachable, and the backend \
has no value to put there: every expression it emits is a pure value, so there is no \
`throw` to fall back on"
  | .jp d k =>
      -- a join point with several jumps is bound as a local function, so that its body
      -- is emitted once and each jump is a call of it; one with a single jump, and one
      -- whose body continues the enclosing loop (which no function can do), is inlined
      let jps' := jps.insert d.fvarId (d.params, d.value)
      if jumpCount d.fvarId k ≥ 2 && codeSize d.value ≥ jpShareSize
          && !mentionsLoopCall c.self c.group jps d.value then
        match (transFun c Γ vm jps d : Res Sg Γ) with
        | .ok jp => do
            let rest ← transBody c (jp.1 :: Γ) (vm.insert d.fvarId (.one Γ.length)) jps' σs τ k
            return .letB jp.2 rest
        | .error _ => transBody c Γ vm jps' σs τ k
      else transBody c Γ vm jps' σs τ k
  | .jmp f args =>
      match vm[f]? with
      -- the join point was bound as a local function: the jump is a call of it, and the
      -- value it answers with is the value of this block
      | some (.one d) => do
          let fnTerm ← varAtDepth Γ d
          let ts ← transArgs Γ vm (args.toList.filter (!isErasedArg vm ·))
          return .ret (coerce τ (applyCurried fnTerm ts))
      | _ =>
        match jps[f]? with
        | none => .error "a jump to a join point that is not in scope"
        | some (ps, body) => transJmp c Γ vm jps σs τ ps.toList args.toList body
  | .fun d k => do
      let fn ← transFun c Γ vm jps d
      let rest ← transBody c (fn.1 :: Γ) (vm.insert d.fvarId (.one Γ.length)) jps σs τ k
      return .letB fn.2 rest
  | .let d k => do
      match d.value, k with
      | .const n _ args, .return r =>
        if r != d.fvarId || σs.length == 0 then
          transLet c Γ vm jps σs τ d k
        else if c.self == some n then
          -- a tail call of a self-recursive declaration: go round its loop again
          let plans := c.paramPlan[n]?.getD []
          let ts ← if plans.isEmpty then transArgs Γ vm args.toList
                   else transArgsPlanned Γ vm plans args.toList
          return .cont (← mkSpine σs (ts.take σs.length))
        else
          match c.group[n]? with
          | some tag =>
            -- a tail call to a member of the merged group: go round the *shared* loop
            -- again, with that member's tag and its arguments in the argument slots
            let ts ← transArgs Γ vm args.toList
            let tagTerm : SomeTerm Sg Γ := ⟨Ty.nat, .lit (.nat tag)⟩
            -- a slot the member being entered has no argument for keeps the value it
            -- already holds: the member never reads it, and an assignment of a slot to
            -- itself is not emitted at all
            let keepSlot (j : Nat) : Except String (SomeTerm Sg Γ) :=
              varAtDepth Γ (c.groupSlots + 1 + j)
            -- the member's arguments go to *its* slots, which are not slots `0 … n` when
            -- the group shares slots only where its members agree on the type
            let placed : List (Option (SomeTerm Sg Γ)) :=
              let slotsOf := c.groupArgSlots[n]?.getD (List.range ts.length)
              (List.range c.groupSlots).map fun j =>
                match slotsOf.idxOf? j with
                | some k => ts[k]?
                | none => none
            return .cont (← mkSpineSome keepSlot σs 0 (some tagTerm :: placed))
          | none => transLet c Γ vm jps σs τ d k
      | _, _ => transLet c Γ vm jps σs τ d k
  | .cases cs => transCases c Γ vm jps σs τ cs

/-- An ordinary `let`, with no tail call in it.  A `let` that merely names a nullary
    instance of this module binds nothing: the instance is its fields, which are
    top-level declarations. -/
partial def transLet {Sg : Sig} (c : Ctx') (Γ : Ctx) (vm : VarMap) (jps : JpMap)
    (σs : List Ty) (τ : Ty) (d : LetDecl) (k : Code) : Except String (Body Sg Γ σs τ) := do
  match d.value with
  | .const n _ args =>
    match c.instOf[n]? with
    | some plan =>
        if (c.paramPlan[n]?.getD []).isEmpty
            && (args.toList.filter (!isErasedArg vm ·)).isEmpty then
          transBody c Γ (vm.insert d.fvarId (.instGlobal (c.js n) plan)) jps σs τ k
        else
          transLetPlain c Γ vm jps σs τ d k
    | none => transLetPlain c Γ vm jps σs τ d k
  | _ => transLetPlain c Γ vm jps σs τ d k

/-- A `let` that does bind a value. -/
partial def transLetPlain {Sg : Sig} (c : Ctx') (Γ : Ctx) (vm : VarMap) (jps : JpMap)
    (σs : List Ty) (τ : Ty) (d : LetDecl) (k : Code) : Except String (Body Sg Γ σs τ) := do
  -- a `let` that binds a type or a proof binds nothing at run time: it is dropped, and
  -- so is every argument position that mentions it
  if isErasedLcnfTy d.type || d.value matches .erased then
    return ← transBody c Γ (vm.insert d.fvarId .erased) jps σs τ k
  let ty ← toTy c.env d.type
  let v ← transLetValue (Sg := Sg) c Γ vm ty d.value
  let rest ← transBody c (v.1 :: Γ) (vm.insert d.fvarId (.one Γ.length)) jps σs τ k
  return .letB v.2 rest

/-- Inline a join point at one of its jumps: bind its parameters to the arguments, then
    translate its body. -/
partial def transJmp {Sg : Sig} (c : Ctx') (Γ : Ctx) (vm : VarMap) (jps : JpMap)
    (σs : List Ty) (τ : Ty) (ps : List Param) (args : List Arg) (body : Code) :
    Except String (Body Sg Γ σs τ) := do
  match ps, args with
  | [], _ => transBody c Γ vm jps σs τ body
  | p :: ps', a :: args' =>
    if isErasedParam p || isErasedArg vm a then
      transJmp c Γ (vm.insert p.fvarId .erased) jps σs τ ps' args' body
    else do
      let t ← transArg Γ vm a
      let rest ← transJmp c (t.1 :: Γ) (vm.insert p.fvarId (.one Γ.length)) jps σs τ ps' args' body
      return .letB t.2 rest
  | _, [] => .error "a jump passes fewer arguments than the join point has parameters"

/-- A `cases`, as a chain of tests.  `Nat` and `Bool` are tested as a number and as a
    boolean; every other type is tested on its runtime tag. -/
partial def transCases {Sg : Sig} (c : Ctx') (Γ : Ctx) (vm : VarMap) (jps : JpMap)
    (σs : List Ty) (τ : Ty) (cs : Cases) : Except String (Body Sg Γ σs τ) := do
  let alts := liveAlts jps cs.alts.toList
  if cs.typeName == ``Nat then
    transNatCases c Γ vm jps σs τ cs.discr alts
  else if cs.typeName == ``Int then
    transIntCases c Γ vm jps σs τ cs.discr alts
  else if cs.typeName == ``Bool || cs.typeName == ``Decidable then
    transBoolCases c Γ vm jps σs τ cs.discr alts
  else
    transTagCases c Γ vm jps σs τ cs.discr alts

/-- The alternative of a constructor, if the list has one. -/
partial def findAlt (alts : List Alt) (nm : Name) : Option Alt :=
  alts.find? fun a => match a with
    | .alt n _ _ => n == nm
    | .default _ => false

/-- The default alternative, if the list has one. -/
partial def findDefault (alts : List Alt) : Option Code :=
  alts.findSome? fun a => match a with
    | .default k => some k
    | .alt .. => none

/-- `cases` on a `Nat`: `n === 0`, and the successor branch binds `n - 1`. -/
partial def transNatCases {Sg : Sig} (c : Ctx') (Γ : Ctx) (vm : VarMap) (jps : JpMap)
    (σs : List Ty) (τ : Ty) (discr : FVarId) (alts : List Alt) :
    Except String (Body Sg Γ σs τ) := do
  match alts with
  | [.default k] => transBody c Γ vm jps σs τ k
  | [.alt n ps k] =>
    -- the only branch that can be taken: no test, and the successor branch still binds
    -- the predecessor
    if n == ``Nat.succ then
      let d ← transArg Γ vm (.fvar discr)
      let pred : Term Sg Γ Ty.nat :=
        .callExtern .lean_nat_sub (.cons (coerce Ty.nat d) (.cons (.lit (.nat 1)) .nil))
      let vm' := match ps.toList with
        | [p] => vm.insert p.fvarId (.one Γ.length)
        | _ => vm
      return .letB pred (← transBody c (Ty.nat :: Γ) vm' jps σs τ k)
    else
      transBody c Γ vm jps σs τ k
  | _ =>
    let dflt := findDefault alts
    let zeroCode : Option Code := match findAlt alts ``Nat.zero with
      | some (.alt _ _ k) => some k
      | _ => dflt
    let z : Body Sg Γ σs τ ← match zeroCode with
      | some k => transBody c Γ vm jps σs τ k
      | none => .error "a `cases` on `Nat` has no branch for one of its shapes and no default"
    let d ← transArg Γ vm (.fvar discr)
    let dNat := coerce Ty.nat d
    let pred : Term Sg Γ Ty.nat :=
      .callExtern .lean_nat_sub (.cons dNat (.cons (.lit (.nat 1)) .nil))
    let s : Body Sg (Ty.nat :: Γ) σs τ ← match findAlt alts ``Nat.succ with
      | some (.alt _ ps k) =>
          let vm' := match ps.toList with
            | [p] => vm.insert p.fvarId (.one Γ.length)
            | _ => vm
          transBody c (Ty.nat :: Γ) vm' jps σs τ k
      | _ => match dflt with
        | some k => transBody c (Ty.nat :: Γ) vm jps σs τ k
        | none => .error "a `cases` on `Nat` has no branch for one of its shapes and no default"
    let test : Term Sg Γ (.prim .bool) :=
      .callExtern .lean_nat_dec_eq (.cons dNat (.cons (.lit (.nat 0)) .nil))
    return .iteB test z (.letB pred s)

/-- `cases` on an `Int`: its two constructors are told apart by the sign.
    `Int.ofNat n` binds `n = v`, and `Int.negSucc n` binds `n = -1 - v` — an `Int` is a
    JavaScript number, so neither branch builds anything. -/
partial def transIntCases {Sg : Sig} (c : Ctx') (Γ : Ctx) (vm : VarMap) (jps : JpMap)
    (σs : List Ty) (τ : Ty) (discr : FVarId) (alts : List Alt) :
    Except String (Body Sg Γ σs τ) := do
  -- the value the branch of `ctor` binds: the `Nat` its field holds
  let fieldOf (ctor : Name) (d : SomeTerm Sg Γ) : Term Sg Γ Ty.nat :=
    let v := coerce Ty.int d
    if ctor == ``Int.negSucc then
      coerce Ty.nat
        ⟨Ty.int, .callExtern .lean_int_sub (.cons (.lit (.int (-1))) (.cons v .nil))⟩
    else
      coerce Ty.nat ⟨Ty.int, v⟩
  let branchOf (ctor : Name) (ps : List Param) (k : Code) :
      Except String (Body Sg Γ σs τ) := do
    let d ← transArg Γ vm (.fvar discr)
    match ps.filter (!isErasedParam ·) with
    | [pv] =>
        let vm' := vm.insert pv.fvarId (.one Γ.length)
        return .letB (fieldOf ctor d) (← transBody c (Ty.nat :: Γ) vm' jps σs τ k)
    | _ => transBody c Γ vm jps σs τ k
  match alts with
  | [.default k] => transBody c Γ vm jps σs τ k
  | [.alt n ps k] => branchOf n ps.toList k
  | _ =>
    let dflt := findDefault alts
    let branch (nm : Name) : Except String (Body Sg Γ σs τ) :=
      match findAlt alts nm with
      | some (.alt _ ps k) => branchOf nm ps.toList k
      | _ => match dflt with
        | some k => transBody c Γ vm jps σs τ k
        | none => .error "a `cases` on `Int` has no branch for one of its shapes and no default"
    let neg ← branch ``Int.negSucc
    let pos ← branch ``Int.ofNat
    let d ← transArg Γ vm (.fvar discr)
    let test : Term Sg Γ (.prim .bool) :=
      .callExtern .lean_int_dec_lt (.cons (coerce Ty.int d) (.cons (.lit (.int 0)) .nil))
    return .iteB test neg pos

/-- `cases` on a `Bool`. -/
partial def transBoolCases {Sg : Sig} (c : Ctx') (Γ : Ctx) (vm : VarMap) (jps : JpMap)
    (σs : List Ty) (τ : Ty) (discr : FVarId) (alts : List Alt) :
    Except String (Body Sg Γ σs τ) := do
  match alts with
  | [.default k] => return ← transBody c Γ vm jps σs τ k
  | [.alt _ _ k] => return ← transBody c Γ vm jps σs τ k
  | _ => pure ()
  let dflt := findDefault alts
  let code (nm nm' : Name) : Option Code :=
    match findAlt alts nm, findAlt alts nm' with
    | some (.alt _ _ k), _ => some k
    | _, some (.alt _ _ k) => some k
    | _, _ => dflt
  let branch (k? : Option Code) : Except String (Body Sg Γ σs τ) :=
    match k? with
    | some k => transBody c Γ vm jps σs τ k
    | none => .error "a `cases` has no branch for one of its constructors and no default"
  let t ← branch (code ``Bool.true ``Decidable.isTrue)
  let f ← branch (code ``Bool.false ``Decidable.isFalse)
  let d ← transArg Γ vm (.fvar discr)
  let test := coerce (.prim .bool) d
  return .iteB test t f

/-- `cases` on any other type: a chain of tests on the runtime tag, with the fields of
    each constructor bound to projections of the scrutinee.  A case that has neither a
    branch for the constructor it meets nor a default branch is *refused*: there is no
    `throw` to fall back on, since every expression the backend emits is a value. -/
partial def transTagCases {Sg : Sig} (c : Ctx') (Γ : Ctx) (vm : VarMap) (jps : JpMap)
    (σs : List Ty) (τ : Ty) (discr : FVarId) :
    List Alt → Except String (Body Sg Γ σs τ)
  | [] => .error "a `cases` with no branch at all cannot be compiled to a value"
  | [.default k] => transBody c Γ vm jps σs τ k
  | [.alt n ps k] => transAltBody c Γ vm jps σs τ discr n ps.toList 0 k
  | .default k :: _ => transBody c Γ vm jps σs τ k
  | .alt n ps k :: rest => do
      let body ← transAltBody c Γ vm jps σs τ discr n ps.toList 0 k
      let others ← transTagCases c Γ vm jps σs τ discr rest
      let d ← transArg Γ vm (.fvar discr)
      let idx := ctorIdx c.env n
      let test : Term Sg Γ (.prim .bool) :=
        .callExtern .lean_nat_dec_eq (.cons (← tagAt d) (.cons (.lit (.nat idx)) .nil))
      return .iteB test body others

/-- The body of one branch: each field of the constructor is bound to a projection of
    the scrutinee, then the branch itself is translated.  A field that carries nothing
    at run time is dropped, so the field numbers here are the ones the layout uses. -/
partial def transAltBody {Sg : Sig} (c : Ctx') (Γ : Ctx) (vm : VarMap) (jps : JpMap)
    (σs : List Ty) (τ : Ty) (discr : FVarId) (ctor : Name) (ps : List Param) (i : Nat)
    (k : Code) : Except String (Body Sg Γ σs τ) := do
  match ps with
  | [] => transBody c Γ vm jps σs τ k
  | p :: ps' =>
      if isErasedParam p then
        transAltBody c Γ (vm.insert p.fvarId .erased) jps σs τ discr ctor ps' i k
      else
        let d ← transArg Γ vm (.fvar discr)
        let fld ← if isNewtypeCtor c.env ctor then pure d
                  else projAt d (ctorIdx c.env ctor) i
        let vm' := vm.insert p.fvarId (.one Γ.length)
        let rest ← transAltBody c (fld.1 :: Γ) vm' jps σs τ discr ctor ps' (i + 1) k
        return .letB fld.2 rest

end

end LakeJs.FromLcnf
