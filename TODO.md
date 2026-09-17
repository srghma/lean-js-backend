1. currently
  | enum : Nat → Ty

and

  /-- In JS: `-1 | 0 | 1` (int8).  A special enum: without special treatment it would
      be compiled as `"LT" | "EQ" | "GT"` or `0 | 1 | 2`, but it is optimized. -/
  | ordering  : LeanPrimTy

but these can be united

if write
  | enum (nOfConstructors : Nat) (shift : Int) → Ty

using shift can make printer print not 0,1,2 but if shift is -1 then -1,0,1

which is exactly what we need

2. LCNF.saveBase has joint points - make them part of Term too, for optimizations

3. currenly we generate this output

const run = (() => {
  const v0 = 48;
  const v1 = 18;
  return $lean_nat_gcd(v0, v1);
})();
const gcd2 = (v0, v1) => $lean_nat_gcd(v0, v1);
export { run, gcd2 };

should be

export const run = (() => {
  const v0 = 48;
  const v1 = 18;
  return $lean_nat_gcd(v0, v1);
})();
export const gcd2 = (v0, v1) => $lean_nat_gcd(v0, v1);

3. the emitted js files

SnapshotsPBOPure/CaptureDerefRegression01.js
SnapshotsPBOPure/CaseJacobs.js
SnapshotsPBOPure/CaseLeafTco.js
SnapshotsPBOPure/Fusion01.js
SnapshotsPBOPure/Fusion02.js
SnapshotsPBOPure/RecursionSchemes01.js
SnapshotsPBOPure/Tco01.js
SnapshotsPBOPure/Tco03.js
SnapshotsPBOPure/Tco04.js
SnapshotsPBOPure/Tco05.js
SnapshotsPBOPure/Tco06.js
SnapshotsPBOPure/VanLaarhovenTraversals01.js
SnapshotsMy/GcdEntry.js
SnapshotsMy/HashContainers.js
SnapshotsMy/MutualTail.js
SnapshotsMy/StringWalk.js
SnapshotsMy/UnreachBranch.js

should be tested

for each of SnapshotsXXX/File.js write the SnapshotsXXX/File.test.js , inside of them use node:assert module to import exports from SnapshotsXXX/File.js and test the generated function against some inputs

also there should be script with name e.g. "run_snapshots_nodejs_dot_tests"

4. currently emitter emits unused values

e.g. in SnapshotsMy/UnreachBranch.js

```js
const headOf = (v0) => {
  const v1 = v0._1;
  const v2 = v0._2; // UNUSED
  return v1;
};
```

expected: dont print unused variables. the it should be impossible to build Term with unused bound variables. Implement plan in USAGE_INDEX_ASSESSMENT.md.

5. `abbrev Sig := List GlobalDecl` -- TODO names should be unique

6. Term is written wrongly: Term is not a language of Javascript encoded in Lean. Term is not a language of Lean encoded in Lean.

Therefore

a.

```
/-- A constant of a terminal type. -/
inductive Lit : Ty → Type
  | nat    : Nat → Lit (.prim .nat)
  | int    : Int → Lit (.prim .int)
  | bool   : Bool → Lit (.prim .bool)
  | str    : String → Lit (.prim .string)
  | char   : Char → Lit (.prim .char)
  /-- A `Float`, spelled by its decimal rendering so that the printer stays
      deterministic. -/
  | float  : String → Lit (.prim .float)
```

is probably better to replace with

```
inductive Lit : LeanPrimTy → Type
  ... contrucor per each constructor of LeanPrimTy (LeanPrimTy before was named wrongly PrimTy).
  ... NOTE: its ok to use Float and Float32 here. therefore also it is ok to use native_decide to prove theorems concerning Float. BUT lets use instead a wrapper around native_decide called float_decide (from FloatDecide.lean) which should restrict native_decide only for float related cases.
```

OR maybe it makes sense to split `inductive LeanPrimTy where` on `LeanPrimTyCanCreateContant` and `LeanPrimTyCanCreateContant` ?

b. the

```
inductive JsPrim : List Ty → Ty → Type where
  /-- `a + b` on numbers of type `τ`. -/
  | add (τ : Ty) : JsPrim [τ, τ] τ
  /-- `a - b`, without the `Nat` truncation. -/
  | sub (τ : Ty) : JsPrim [τ, τ] τ
  /-- `Math.max(0, a - b)`: subtraction on `Nat`. -/
  | natSub : JsPrim [.nat, .nat] .nat
  | mul (τ : Ty) : JsPrim [τ, τ] τ
  | div (τ : Ty) : JsPrim [τ, τ] τ
  | mod (τ : Ty) : JsPrim [τ, τ] τ
  | lt (τ : Ty) : JsPrim [τ, τ] .bool
  | le (τ : Ty) : JsPrim [τ, τ] .bool
  | gt (τ : Ty) : JsPrim [τ, τ] .bool
  | ge (τ : Ty) : JsPrim [τ, τ] .bool
  /-- `a === b`. -/
  | beq (τ : Ty) : JsPrim [τ, τ] .bool
  /-- `a !== b`. -/
  | bne (τ : Ty) : JsPrim [τ, τ] .bool
  | and : JsPrim [.bool, .bool] .bool
  | or : JsPrim [.bool, .bool] .bool
  | not : JsPrim [.bool] .bool
  /-- `a + b` on strings. -/
  | strAppend : JsPrim [.string, .string] .string
  /-- `a.length`. -/
  | strLength : JsPrim [.string] .nat
  /-- `a.charAt(i)`. -/
  | strGet : JsPrim [.string, .nat] .char
  /-- `(a) | 0`: the 32-bit truncation Lean's `Int` arithmetic gets. -/
  | toInt32 : JsPrim [.int] .int
  /-- `a.length` of an array. -/
  | arraySize (α : Ty) : JsPrim [.array α] .nat
  /-- `a[i]`. -/
  | arrayGet (α : Ty) : JsPrim [.array α, .nat] α
  /-- `[...a, x]`. -/
  | arrayPush (α : Ty) : JsPrim [.array α, α] (.array α)
  /-- `[]`. -/
  | arrayEmpty (α : Ty) : JsPrim [] (.array α)
  /-- `a[a.length - 1]`. -/
  | arrayBack (α : Ty) : JsPrim [.array α] α
  /-- `String(a)`. -/
  | toStr (τ : Ty) : JsPrim [τ] .string
  /-- `Math.abs(a)`. -/
  | natAbs : JsPrim [.int] .nat
  /-- The argument itself, read at another type: a coercion that costs nothing at run
      time, such as the one between a `Decidable` and the boolean it decides, or the one
      between a value of a type parameter (`Ty.typeParam`) and the type the context
      knows it to have.  It prints as the argument, so the reinterpretation is visible
      in the term and invisible in the output. -/
  | cast (σ τ : Ty) : JsPrim [σ] τ
```

should be removed because this is encoded javascript language (why? bc it allows such things like `beq (τ : Ty) : JsPrim [τ, τ] .bool` for any type.) and instead one should use `inductive Externs : List Ty → Ty → Type where` from Externs.lean (the lean @[extern] from lean4 code)

the `Externs` should be handled on optimizer level and (if survives optimization then) on rendering level (TODO: make a list of lean_xxx externs which can never appear in Term and comment it out (if any))


the fact that Term is a representation of Lean code and not Javascript will become important later when we will implement

```
PrimOpIntDivConfigurable-bigint.js -- note that js files export `const xxx_shouldBeTrue` which tests on some random data that optimizer-reduced-inlined-functions and noinline-functions agree in output. for them we should create e.g. `PrimOpIntDivConfigurable-bigint.test.js` that just imports them and tests `xxx_shouldBeTrue === true`
PrimOpIntDivConfigurable-num.js
PrimOpIntDivConfigurable.lean -- compiled to PrimOpIntDivConfigurable-bigint.js if config is `presetFaithful : JsConfig` OR PrimOpIntDivConfigurable-num.js if config is `presetPBO : JsConfig`.
PrimOpIntDivNonConfigurable.js
PrimOpIntDivNonConfigurable.lean -- always compiled to PrimOpIntDivNonConfigurable.js only. where js bigint is not used, but only js number is used
```

7. improve performance of loops based on plan in MUTUAL_LOOP_PERF.md

8.

the optimizer should be written not as function, but as `inductive Prop` relation so that we could later do proofs about like is it or not Church-Rosser `theorem Relation.church_rosser` from `Mathlib.Logic.Relation`, Idempotence `Std.IdempotentOp {α : Sort u} (op : α → α → α) : Prop` etc:

```lean
-- define Value

inductive Value : Γ ⊢ a → Type where
| lam : Value (ƛ (n : Γ‚ a ⊢ b))
...

-- https://plfa.github.io/DeBruijn/#reduction
/--
`Reduce t t'` says that `t` reduces to `t'` via a given step.
-/
inductive Reduce : (Γ ⊢ a) → (Γ ⊢ a) → Prop where
| lamβ : Value v → Reduce ((ƛ n) ⬝ v) (n⟦v⟧)
| apξ₁ : Reduce l l' → Reduce (l ⬝ m) (l' ⬝ m)
...

scoped infix:40 " —→ " => Reduce

abbrev Clos {Γ a} := Relation.ReflTransGen (α := Γ ⊢ a) Reduce

scoped infix:20 " —↠ " => Reduce.Clos

/--
If a term `m` is not ill-typed, then it either is a value or can be reduced.
-/
inductive Progress (m : ∅ ⊢ a) where
| step : (m —→ n) → Progress m
| done : Value m → Progress m

def Progress.progress : (m : ∅ ⊢ a) → Progress m := open Reduce in by

inductive Result (n : Γ ⊢ a) where
| done (val : Value n)
| dnf
deriving BEq, DecidableEq, Repr

inductive Steps (l : Γ ⊢ a) where
| steps : ∀{n : Γ ⊢ a}, (l —↠ n) → Result n → Steps l

def optimize (gas : ℕ) (l : ∅ ⊢ a) : Steps l := -- in PLFA this function is called eval, but I have change a name to the better one.
-- XXX: ALSO PROBABLY DOESNT REQUIRE GAS BC TERM IS TOTAL
-- Only this function should be able transform Term to Term in our repo. the next functions in processing like is just Term -> MiniAST
  if gas = 0 then
    ⟨.refl, .dnf⟩
  else
    match progress l with
    | .done v => .steps .refl <| .done v
    | .step (n := n) r =>
      let ⟨rs, res⟩ := eval (gas - 1) n
      ⟨Trans.trans r rs, res⟩
```
