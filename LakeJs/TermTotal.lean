module

public import LakeJs.Expr

@[expose] public section

namespace LakeJs.TermTotal

/-!
# Why a `Term` cannot diverge

The backend only ever emits `while`/`for` loops, never a self-applying closure.  Two
facts, proved here, are what make that possible.

1. `Ty.ne_arrow_self`: no type is its own argument type, `σ ≠ .fn [σ] τ`.  Applying a
   variable to itself therefore does not typecheck, so `ω = λx. x x` — and with it the
   `Y` combinator and every other fixed point built from self-application — is not a
   `Term`.  This is the standard reason the simply-typed λ-calculus has no Omega, stated
   for `LakeJs.Ty`'s uncurried function space.
2. `Term.noFix`: the grammar of `Term` has no recursive-definition node.  The only
   constructor that repeats work is `Term.loop`, whose body is a `Body`; a `Body` either
   answers or continues, which is exactly the shape of a `while` loop.  `Term.loopCount`
   counts those loops, and `Term.isLoopFree` says a term has none — a loop-free term
   prints to straight-line JavaScript.

Termination of the loops themselves is *not* established here, and it is not the
backend's job to establish it: a declaration only becomes a `Term` if Lean already
proved it terminating, which is what `LakeJs.Totality` checks before the translation
starts.
-/

/-! ## No type is its own argument type -/

mutual

/-- How deeply function arrows nest in a type.  Only `Ty.fn` is counted; every other
    shape is a leaf for this purpose, which is all `Ty.ne_arrow_self` needs. -/
def Ty.arrowDepth : Ty → Nat
  | .fn params ret => 1 + Nat.max (Ty.arrowDepthList params) (Ty.arrowDepth ret)
  | _ => 0

/-- `Ty.arrowDepth` of the deepest member of a list of types. -/
def Ty.arrowDepthList : List Ty → Nat
  | [] => 0
  | t :: ts => Nat.max (Ty.arrowDepth t) (Ty.arrowDepthList ts)

end

theorem Ty.arrowDepth_fn (params : List Ty) (ret : Ty) :
    Ty.arrowDepth (.fn params ret)
      = 1 + Nat.max (Ty.arrowDepthList params) (Ty.arrowDepth ret) := by
  simp [Ty.arrowDepth]

theorem Ty.arrowDepthList_single (t : Ty) :
    Ty.arrowDepthList [t] = Ty.arrowDepth t := by
  simp [Ty.arrowDepthList]

/-- **No Omega.**  A type is never the argument type of itself, so a self-application
    `x x` has no type: it would need `σ = .fn [σ] τ`.  `Term.apN` asks for exactly that
    agreement between the parameter list of the function and the types of the arguments,
    so `ƛ ♯0 ⬝ ♯0` is not a `Term`, and neither is any fixed-point combinator built from
    it. -/
theorem Ty.ne_arrow_self (σ τ : Ty) : σ ≠ Ty.fn [σ] τ := by
  intro h
  have hd : Ty.arrowDepth σ = Ty.arrowDepth (Ty.fn [σ] τ) := congrArg Ty.arrowDepth h
  rw [Ty.arrowDepth_fn, Ty.arrowDepthList_single] at hd
  have : Ty.arrowDepth σ ≤ Nat.max (Ty.arrowDepth σ) (Ty.arrowDepth τ) :=
    Nat.le_max_left _ _
  omega

/-- The same fact for the one-parameter arrow notation. -/
theorem Ty.ne_self_arrow (σ τ : Ty) : σ ≠ (σ ⇒ τ) := Ty.ne_arrow_self σ τ

/-- A variable cannot be applied to itself: there is no context in which the same
    de Bruijn index is both a function and its own argument. -/
theorem Term.no_self_application {Γ : Ctx} {σ τ : Ty}
    (_x : Γ ∋ σ) (h : σ = Ty.fn [σ] τ) : False :=
  Ty.ne_arrow_self σ τ h

/-! ## Data is built and read according to a schema -/

/-- **No record at a function type.**  `Term.ctor` asks for the evidence that the type
    it builds has a constructor of that name, and a function type has none, so
    `{ tag: …, _1: … }` is never a term of a function type. -/
theorem Term.no_ctor_at_function {params : List Ty} {ret : Ty} {fields : FieldLayout}
    (i : Nat) (h : (Ty.fn params ret).ctorFields? i = some fields) : False := by
  rw [Ty.ctorFields?_fn] at h
  cases h

/-- **No field of a function.**  `Term.proj` asks for the evidence that the value it
    reads from has such a field, so `f._1` is never emitted for an `f` of a function
    type. -/
theorem Term.no_proj_of_function {Sg : Sig} {Γ : Ctx} {params : List Ty} {ret τ : Ty}
    (_e : Term Sg Γ (Ty.fn params ret)) (i j : Nat)
    (h : (Ty.fn params ret).fieldTy? i j = some τ) : False := by
  rw [Ty.fieldTy?_fn] at h
  cases h

/-- **No scalar is a record either.**  A `Nat` has no constructor to build and no field
    to read: only a type carrying a schema does. -/
theorem Term.no_ctor_at_scalar {p : LeanPrimTy} {fields : FieldLayout} (i : Nat)
    (h : (Ty.prim p).ctorFields? i = some fields) : False := by
  rw [Ty.ctorFields?_prim] at h
  cases h

/-- **A value of a type parameter cannot be taken apart.**  `Ty.typeParam` is the type
    of a value whose Lean type is a type parameter of the enclosing declaration.  There
    is no longer any *unchecked* data operation to reach for — `Term.dynCtor`,
    `Term.dynProj` and `Term.dynCase` are gone, and with them the `Ty.dynamic` they
    lived at — and the checked ones are unavailable here, so a compiled module never
    reads a field of a value whose shape it does not know. -/
theorem Term.no_ctor_at_typeParam {fields : FieldLayout} (i : Nat)
    (h : Ty.typeParam.ctorFields? i = some fields) : False := by
  rw [Ty.ctorFields?_typeParam] at h
  cases h

/-- **An alias has no constructor of its own.**  A newtype's wrapper is erased, so a
    value of `Ty.recAlias b` is a value of what `b` unfolds to: there is nothing to
    build and nothing to read. -/
theorem Term.no_ctor_at_alias {b : RTy} {fields : FieldLayout} (i : Nat)
    (h : (Ty.recAlias b).ctorFields? i = some fields) : False := by
  rw [Ty.ctorFields?_recAlias] at h
  cases h

/-! ## The only repetition is a loop -/

mutual

/-- How many `Term.loop` nodes a term contains. -/
def Term.loopCount {Sg : Sig} : ∀ {Γ τ}, Term Sg Γ τ → Nat
  | _, _, .var _ => 0
  | _, _, .lit _ => 0
  | _, _, .global _ => 0
  | _, _, .extern _ => 0
  | _, _, .proj e _ _ _ => Term.loopCount e
  | _, _, .tagOf e _ => Term.loopCount e
  | _, _, .ite c t e => Term.loopCount c + Term.loopCount t + Term.loopCount e
  | _, _, .letE e b => Term.loopCount e + Term.loopCount b
  | _, _, .prim _ args => Spine.loopCount args
  | _, _, .lamProd rets => Spine.loopCount rets
  | _, _, .callProd f args _ => Term.loopCount f + Spine.loopCount args
  | _, _, .lamN b => Term.loopCount b
  | _, _, .apN f args => Term.loopCount f + Spine.loopCount args
  | _, _, .ctor _ _ _ args => Spine.loopCount args
  | _, _, .caseTag s alts _ => Term.loopCount s + Alts.loopCount alts
  | _, _, .loop init body => 1 + Spine.loopCount init + Body.loopCount body

/-- `Term.loopCount`, summed over a spine. -/
def Spine.loopCount {Sg : Sig} : ∀ {Γ σs}, Spine Sg Γ σs → Nat
  | _, _, .nil => 0
  | _, _, .cons t rest => Term.loopCount t + Spine.loopCount rest

/-- `Term.loopCount`, summed over the branches of a case. -/
def Alts.loopCount {Sg : Sig} : ∀ {Γ τ} {tags : List Nat}, Alts Sg Γ τ tags → Nat
  | _, _, _, .deflt t => Term.loopCount t
  | _, _, _, .cons _ t rest => Term.loopCount t + Alts.loopCount rest

/-- `Term.loopCount`, summed over a loop body. -/
def Body.loopCount {Sg : Sig} : ∀ {Γ σs τ}, Body Sg Γ σs τ → Nat
  | _, _, _, .ret t => Term.loopCount t
  | _, _, _, .cont args => Spine.loopCount args
  | _, _, _, .letB e b => Term.loopCount e + Body.loopCount b
  | _, _, _, .iteB c t e => Term.loopCount c + Body.loopCount t + Body.loopCount e

end

/-- A term with no loop in it: it prints to straight-line JavaScript. -/
def Term.isLoopFree {Sg : Sig} {Γ : Ctx} {τ : Ty} (t : Term Sg Γ τ) : Bool := t.loopCount == 0

/-- **No recursive definitions.**  Every constructor of `Term` other than `Term.loop`
    builds a term whose loop count is the sum of its children's, so repetition can only
    enter a term through `Term.loop` — there is no fixed-point node to enter it through.
    Stated for the constructors a translated declaration is built from. -/
theorem Term.loopCount_lam {Sg : Sig} {Γ : Ctx} {params : List Ty} {ret : Ty}
    (b : Term Sg (params.reverse ++ Γ) ret) :
    (Term.lamN b).loopCount = b.loopCount := by
  simp [Term.loopCount]

theorem Term.loopCount_ap {Sg : Sig} {Γ : Ctx} {params : List Ty} {ret : Ty}
    (f : Term Sg Γ (.fn params ret)) (args : Spine Sg Γ params) :
    (Term.apN f args).loopCount = f.loopCount + args.loopCount := by
  simp [Term.loopCount]

theorem Term.loopCount_let {Sg : Sig} {Γ : Ctx} {σ τ : Ty} (e : Term Sg Γ σ)
    (b : Term Sg (σ :: Γ) τ) :
    (Term.letE e b).loopCount = e.loopCount + b.loopCount := by
  simp [Term.loopCount]

theorem Term.loopCount_loop {Sg : Sig} {Γ : Ctx} {σs : List Ty} {τ : Ty}
    (init : Spine Sg Γ σs) (body : Body Sg (σs.reverse ++ Γ) σs τ) :
    (Term.loop init body).loopCount = 1 + init.loopCount + body.loopCount := by
  simp [Term.loopCount]

/-- The λ-fragment — variables, lambdas, applications, literals, `let` — is loop-free,
    so a term of it prints without a single `while`.  The Church numerals of
    `LakeJs.Expr` are instances of this. -/
theorem Term.isLoopFree_two {Sg : Sig} {α : Ty} :
    (Term.two (Sg := Sg) (α := α)).isLoopFree = true := by
  simp [Term.isLoopFree, Term.two, Term.lam, Term.ap, Term.loopCount, Spine.loopCount]

/-- The hand-written translation of `Tco01`'s `test` has exactly one loop and no other
    repetition.  It mentions no global, so it is stated of the empty signature. -/
theorem Term.loopCount_tco01 : (Term.tco01 (Sg := [])).loopCount = 1 := by
  decide +kernel

/-! ## A dispatch answers for every tag

What used to need an `unreachable` branch — a tag no constructor of the scrutinee's type
has, or one Lean proved impossible — needs nothing at all: `Alts` ends in a default
branch, so *which* branch a runtime tag takes is a total function of that tag, and it is
always one of the branches the case actually has.  That is the fact that lets the
backend print a dispatch as a chain of tests with no `throw` at the end of it. -/

/-- The branch a runtime tag takes: the first branch that tests it, and the default
    branch if none does.  It is a function, not a partial one: every tag answers. -/
def Alts.select {Sg : Sig} {Γ : Ctx} {τ : Ty} :
    ∀ {tags : List Nat}, Alts Sg Γ τ tags → Nat → Term Sg Γ τ
  | _, .deflt t, _ => t
  | _, .cons tag t rest, n => if n = tag then t else Alts.select rest n

/-- The default branch: the one a tag no branch tests takes. -/
def Alts.deflt? {Sg : Sig} {Γ : Ctx} {τ : Ty} :
    ∀ {tags : List Nat}, Alts Sg Γ τ tags → Term Sg Γ τ
  | _, .deflt t => t
  | _, .cons _ _ rest => Alts.deflt? rest

/-- The branches of a case, the default one included. -/
def Alts.branches {Sg : Sig} {Γ : Ctx} {τ : Ty} :
    ∀ {tags : List Nat}, Alts Sg Γ τ tags → List (Term Sg Γ τ)
  | _, .deflt t => [t]
  | _, .cons _ t rest => t :: Alts.branches rest

/-- **No dispatch falls off the end.**  Whatever the runtime tag is — a constructor the
    case tests, a constructor it does not, or a number no constructor has — the branch
    taken is one of the branches the case has.  There is nothing left for a `throw` to
    do. -/
theorem Alts.select_mem_branches {Sg : Sig} {Γ : Ctx} {τ : Ty} :
    ∀ {tags : List Nat} (a : Alts Sg Γ τ tags) (n : Nat), a.select n ∈ a.branches
  | _, .deflt t, n => by simp [Alts.select, Alts.branches]
  | _, .cons tag t rest, n => by
      by_cases h : n = tag
      · simp [Alts.select, Alts.branches, h]
      · simp only [Alts.select, Alts.branches, if_neg h]
        exact List.mem_cons_of_mem _ (Alts.select_mem_branches rest n)

/-- A tag no branch tests takes the default branch. -/
theorem Alts.select_of_not_mem {Sg : Sig} {Γ : Ctx} {τ : Ty} :
    ∀ {tags : List Nat} (a : Alts Sg Γ τ tags) (n : Nat), n ∉ tags → a.select n = a.deflt?
  | _, .deflt t, n, _ => by simp [Alts.select, Alts.deflt?]
  | _, .cons (tags := ts) tag _ rest, n, h => by
      have hne : n ≠ tag := fun hEq => h (by simp [hEq])
      have hrest : n ∉ ts := fun hMem => h (List.mem_cons_of_mem _ hMem)
      simp only [Alts.select, Alts.deflt?, if_neg hne]
      exact Alts.select_of_not_mem rest n hrest

/-- The number of branches a case answers with is the number it has. -/
theorem Alts.length_branches {Sg : Sig} {Γ : Ctx} {τ : Ty} :
    ∀ {tags : List Nat} (a : Alts Sg Γ τ tags), a.branches.length = a.length
  | _, .deflt _ => by simp [Alts.branches, Alts.length]
  | _, .cons _ _ rest => by
      simp [Alts.branches, Alts.length, Alts.length_branches rest]

end LakeJs.TermTotal
