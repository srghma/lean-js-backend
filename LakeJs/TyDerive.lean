module

public import LakeJs.TyMeta
public meta import LakeJs.TyMeta
public import Lean.Elab.Command
public meta import Lean.Elab.Command

public section
@[expose] section

/-!
# `derive_ty T as Ty.foo` — generating a `Ty` abbreviation from a real declaration

`LakeJs.TyMeta` reads a schema off a **parameterless** declaration: `lean_ty% Direction`
is a `Ty`, because `Direction` is a type.  `Option` and `Prod` are not types but type
*families*, so they have no single `Ty`; what they have is a `Ty`-valued **function**,
one `Ty` parameter per type parameter:

```lean
derive_ty Option as Ty.option   -- def Ty.option : Ty → Ty
derive_ty Prod   as Ty.prod     -- def Ty.prod   : Ty → Ty → Ty
```

The command reads the constructors of the declaration exactly as `lean_ty%` does —
same classification into the six shapes, same tags, same field names, same
translation of field types — with one addition: a type parameter of the declaration
translates to the corresponding `Ty` argument of the generated function.  So the
schema is *derived* from Lean's own `Option`/`Prod`, and cannot silently drift from
them: if `Option`'s field were renamed from `val`, the generated JS field name would
follow.

## What is supported

Everything `lean_ty%` supports, except a mutual block: the parameters of the members
of a block need not agree, and a `LeanMutualRecFamily` has no room for them.  A
*recursive* parameterised declaration is supported, as long as it refers to itself at
its own parameters (`MyList α` inside `MyList α` — the usual case, and the only one
Lean's own positivity check accepts for a plain parameter).

Parameters must be types (`α : Type u`); a value parameter (`n : Nat`, as in
`Vector α n`) would be an indexed family, which has no JavaScript representation.
-/

open Lean Elab Command Term Meta
open NonEmpty.String

namespace LakeJs.TyDerive

open LakeJs.TyMeta

/-! ## Type parameters as `Ty` arguments -/

/-- The name of the `Ty` argument standing for type parameter `i`. -/
meta def paramName (i : Nat) : Name := Name.mkSimple ("α" ++ toString i)

/-- The identifier of the `Ty` argument standing for type parameter `i`.  The
    generated `fun` binder and every occurrence in the generated body are both built
    from this, so they are the same name. -/
meta def paramIdent (i : Nat) : Ident := mkIdent (paramName i)

/--
Introduce one local constant per parameter of a declaration, named `α0`, `α1`, … so
that `tyOfExpr` renders an occurrence of parameter `i` as `paramIdent i`.

The names come from *us*, not from the declaration, so a declaration whose parameter
is anonymous or shadows something is still handled.
-/
meta partial def withTyParams {β : Type} (declName : Name) (ty : Expr) (todo : Nat)
    (acc : Array Expr) (k : Array Expr → MetaM β) : MetaM β := do
  if todo == 0 then
    k acc
  else
    match ← whnf ty with
    | .forallE _ d b _ =>
        unless d.isSort do
          throwError "parameter #{acc.size + 1} of '{declName}' is a value parameter of \
            type '{d}', not a type parameter; such a declaration is an indexed family \
            and has no JavaScript representation"
        withLocalDeclD (paramName acc.size) d fun x =>
          withTyParams declName (b.instantiate1 x) (todo - 1) (acc.push x) k
    | _ => throwError "'{declName}' has fewer binders than its {todo} declared parameters"

/-- The fields `(name, type)` of a constructor, with the parameters of its inductive
    instantiated to the local constants of `withTyParams`. -/
meta def paramCtorFields (params : Array Expr) (ctorName : Name) :
    MetaM (List (String × Expr)) := do
  let cv ← getConstInfoCtor ctorName
  let t ← instantiateForall cv.type params
  forallTelescopeReducing t fun args _ => do
    args.toList.zipIdx.mapM fun (fv, i) => do
      let decl ← fv.fvarId!.getDecl
      return (fieldName i decl.userName, ← instantiateMVars decl.type)

/-- Is `e` the declaration being derived, applied to exactly its own parameters? -/
meta def isSelfApp (self : Name) (params : Array Expr) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const c _ => c == self && e.getAppArgs == params
  | _          => false

/-! ## Rows -/

/-- A `FieldRow` of ordinary (non-recursive) fields. -/
meta def paramFieldRowSyn : List (String × Expr) → MetaM Term
  | [] => `(FieldRow.nil)
  | (nm, t) :: rest => do
      `(FieldRow.cons $(← nesSyn nm) $(← tyOfExpr [] t) $(← paramFieldRowSyn rest))

/-- A `CtorRow` of non-recursive constructors. -/
meta def paramCtorRowSyn (self : Name) (params : Array Expr) :
    List Name → MetaM Term
  | [] => `(CtorRow.nil)
  | c :: rest => do
      `(CtorRow.cons $(← nesSyn (ctorTag false self c))
          $(← paramFieldRowSyn (← paramCtorFields params c))
          $(← paramCtorRowSyn self params rest))

/-- The `SelfTy` of a field of a recursive parameterised declaration. -/
meta partial def paramSelfTyOfExpr (self : Name) (params : Array Expr) (e₀ : Expr) :
    MetaM Term := do
  let e ← whnf e₀
  if isSelfApp self params e then
    return ← `(SelfTy.self)
  if !mentionsAny [self] e then
    return ← `(SelfTy.ty $(← tyOfExpr [] e))
  if e.isForall then
    return ← forallTelescopeReducing e fun args body => do
      if body.hasLooseBVars then
        throwError "dependent function type '{e}' has no JavaScript representation"
      for a in args do
        if mentionsAny [self] (← inferType a) then
          throwError "'{self}' occurs in a parameter of the function type '{e}': that is \
            a negative occurrence, which has no representation"
      let ps ← args.mapM fun a => do tyOfExpr [] (← inferType a)
      `(SelfTy.fn [$ps,*] $(← paramSelfTyOfExpr self params body))
  match e.getAppFn, e.getAppArgs with
  | .const ``Array _, #[a]   => do `(SelfTy.array $(← paramSelfTyOfExpr self params a))
  | .const ``List _, #[a]    => do `(SelfTy.list $(← paramSelfTyOfExpr self params a))
  | .const ``Option _, #[a]  => do `(SelfTy.option $(← paramSelfTyOfExpr self params a))
  | .const ``Thunk _, #[a]   => do `(SelfTy.thunk $(← paramSelfTyOfExpr self params a))
  | .const ``Task _, #[a]    => do `(SelfTy.task $(← paramSelfTyOfExpr self params a))
  | .const ``Prod _, #[a, b] => do
      `(SelfTy.prod $(← paramSelfTyOfExpr self params a)
          $(← paramSelfTyOfExpr self params b))
  | _, _ => throwError "'{self}' occurs in '{e}' in a position this translation does not \
      understand (supported: an occurrence at the declaration's own parameters, and \
      such an occurrence under `Array`/`List`/`Option`/`Thunk`/`Task`/`Prod`, and the \
      result of a function)"

/-- A `SelfFieldRow`. -/
meta def paramSelfFieldRowSyn (self : Name) (params : Array Expr) :
    List (String × Expr) → MetaM Term
  | [] => `(SelfFieldRow.nil)
  | (nm, t) :: rest => do
      `(SelfFieldRow.cons $(← nesSyn nm) $(← paramSelfTyOfExpr self params t)
          $(← paramSelfFieldRowSyn self params rest))

/-- A `RecCtorRow`. -/
meta def paramRecCtorRowSyn (self : Name) (params : Array Expr) : List Name → MetaM Term
  | [] => `(RecCtorRow.nil)
  | c :: rest => do
      `(RecCtorRow.cons $(← nesSyn (ctorTag false self c))
          $(← paramSelfFieldRowSyn self params (← paramCtorFields params c))
          $(← paramRecCtorRowSyn self params rest))

/-! ## The body of the generated definition -/

/-- The `Ty` of the declaration `self`, with its type parameters standing for the
    arguments of the generated function.  Same classification as `LakeJs.TyMeta`: the
    shape is determined by the number of constructors, whether any constructor has a
    field, and whether the declaration mentions itself. -/
meta def deriveTyBody (self : Name) (params : Array Expr) : MetaM Term := do
  let iv ← getConstInfoInduct self
  if iv.numIndices != 0 then
    throwError "'{self}' is an indexed family, which has no JavaScript representation"
  if iv.all.length ≥ 2 then
    throwError "'{self}' belongs to a mutual block; `derive_ty` handles one \
      declaration at a time, and a `LeanMutualRecFamily` has no room for the type \
      parameters of its members"
  if iv.ctors.isEmpty then
    throwError "'{self}' is a void type: it has no values, so it has no representation"
  let ctors ← iv.ctors.mapM fun c => do return (c, ← paramCtorFields params c)
  let anyField := ctors.any fun (_, fs) => !fs.isEmpty
  let selfRec := ctors.any fun (_, fs) => fs.any fun (_, t) => mentionsAny [self] t
  let nameSyn ← nesSyn (shortName self)
  match ctors with
  | [(_, fs)] =>
      if !anyField then
        throwError "'{self}' is a unit type: it carries no information and is erased"
      if selfRec then
        `(Ty.recObject ({ name := $nameSyn
                        , fields := $(← paramSelfFieldRowSyn self params fs)
                        } : LeanRecObjectSchema Ty))
      else
        `(Ty.record ({ name := $nameSyn
                     , fields := $(← paramFieldRowSyn fs) } : LeanRecordSchema Ty))
  | _ =>
      if !anyField then
        match iv.ctors.map (fun c => ctorTag false self c) with
        | t1 :: t2 :: rest => do
            let restSyn ← rest.toArray.mapM nesSyn
            `(Ty.enum ({ name := $nameSyn
                       , ctor1 := $(← nesSyn t1), ctor2 := $(← nesSyn t2)
                       , ctorRest := [$restSyn,*] } : LeanEnumSchema))
        | _ => throwError "'{self}' has fewer than two constructors"
      else if selfRec then
        `(Ty.recTaggedUnion ({ name := $nameSyn
                             , ctors := $(← paramRecCtorRowSyn self params iv.ctors)
                             } : LeanRecTaggedUnionSchema Ty))
      else
        `(Ty.taggedUnion ({ name := $nameSyn
                          , ctors := $(← paramCtorRowSyn self params iv.ctors)
                          } : LeanTaggedUnionSchema Ty))

/-- `Ty → Ty → … → Ty`, with `n` arguments. -/
meta def arityTySyn : Nat → MetaM Term
  | 0     => `(Ty)
  | n + 1 => do `(Ty → $(← arityTySyn n))

/-- The `def` generated by `derive_ty`. -/
meta def deriveTyCmd (doc : Option (TSyntax ``Lean.Parser.Command.docComment))
    (declName self : Name) : MetaM (TSyntax `command) := do
  let iv ← getConstInfoInduct self
  withTyParams self iv.type iv.numParams #[] fun params => do
    let body ← deriveTyBody self params
    let sig ← arityTySyn params.size
    let binders := (Array.range params.size).map paramIdent
    let val ← if binders.isEmpty then pure body else `(fun $binders* => $body)
    let id := mkIdent declName
    match doc with
    | some d => `(command| $d:docComment def $id:ident : $sig := $val)
    | none   => `(command| def $id:ident : $sig := $val)

/-- `Ty.` + the declaration's short name with a lower-case initial: the default target
    name, so `derive_ty Option` defines `Ty.option`. -/
meta def defaultTargetName (self : Name) : Name :=
  let s := shortName self
  let s := match s.toList with
    | c :: cs => String.ofList (c.toLower :: cs)
    | []      => s
  (Name.mkSimple "Ty").str s

/-! ## The command -/

/--
`derive_ty T` defines `Ty.t` — a `Ty`, or a function from `Ty` to `Ty` with one
argument per type parameter of `T` — by reading the schema of the real Lean
declaration `T`.  `derive_ty T as Ty.foo` chooses the name.
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

end
end
