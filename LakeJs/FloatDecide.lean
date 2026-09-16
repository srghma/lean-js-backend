/-
# `float_decide` — a guarded wrapper around `native_decide`

`native_decide` closes a goal by *running compiled code* and trusting the result.  That
enlarges the trusted code base (the compiler and the runtime, recorded as an extra axiom in
`#print axioms`), so it is not something one wants available everywhere.

The evaluation of the floating point models in this project is, however, exactly the place
where it pays for itself: the definitions are big rational computations that the kernel can
only unfold very slowly, while compiled evaluation is instantaneous.

`float_decide` is therefore a wrapper that behaves like `native_decide`, but *first* checks
that the goal really is a statement about the floating point types

and nothing else.  Concretely the goal must

1. mention at least one constant belonging to one of those types, and
2. mention *only* constants that are either float constants or belong to the neutral
   "plumbing" whitelist below (booleans, naturals, integers, machine integers, strings,
   lists/arrays/products, the logical connectives, and type-class / instance machinery).

If either check fails the tactic fails with an explanatory message and the goal is left
untouched, so a stray `native_decide` cannot creep into an unrelated proof.
-/
import Lean

open Lean Elab Tactic Meta

namespace FloatDecide

/-- The floating point types `float_decide` is willing to evaluate natively. -/
def floatTypeNames : List Name :=
  [`Float, `Float32, `FloatArray]

def isFloatConst (n : Name) : Bool :=
  n.components.any fun c => floatTypeNames.contains c

/-- Head symbols that carry no mathematical content of their own: data types that the float
operations are stated in terms of, the logical connectives, and the type-class plumbing that
numerals and notation elaborate to.  A goal made of these *alone* is not a float goal (check 1
rejects it), but they are allowed to occur alongside float constants. -/
def neutralRoots : List Name :=
  [-- basic data
   `Nat, `Int, `Bool, `String, `Char, `Substring, `List, `Array, `Subarray, `Prod, `Option,
   `Sum, `Subtype, `Fin, `BitVec, `ByteArray, `Rat, `Unit, `PUnit, `Empty, `Thunk,
   -- machine integers
   `UInt8, `UInt16, `UInt32, `UInt64, `USize,
   `Int8, `Int16, `Int32, `Int64, `ISize,
   -- logic
   `Eq, `Ne, `HEq, `Iff, `And, `Or, `Not, `True, `False, `Exists, `ite, `dite, `cond, `id,
   `Decidable, `DecidableEq, `decide, `Function, `Membership, `EmptyCollection,
   `Inhabited, `Nonempty, `Trans,
   -- notation / numerals
   `OfNat, `OfScientific, `NatCast, `IntCast, `Neg, `Add, `Sub, `Mul, `Div, `Mod, `Pow,
   `HAdd, `HSub, `HMul, `HDiv, `HMod, `HPow, `HAppend, `Append,
   `LT, `LE, `GT, `GE, `BEq, `LawfulBEq, `Ord, `Ordering, `Min, `Max, `Zero, `One,
   `ToString, `Repr, `Hashable]

/-- Is `n` a neutral constant: a member of `neutralRoots`, a registered instance (these only
carry the notation attached to a numeral or an operator), or an internal auxiliary name? -/
def isNeutralConst (n : Name) : CoreM Bool := do
  let root := n.getRoot
  if neutralRoots.contains root || root.toString.startsWith "inst" ||
      root.toString.startsWith "_" then
    return true
  Lean.Meta.isInstance n

/-- The constants of `e` that justify calling this a floating point goal. -/
def floatConsts (e : Expr) : Array Name :=
  e.getUsedConstants.filter isFloatConst

/-- The constants of `e` that are neither float constants nor neutral plumbing. -/
def foreignConsts (e : Expr) : CoreM (Array Name) :=
  e.getUsedConstants.filterM fun n => do
    if isFloatConst n then return false else return !(← isNeutralConst n)

/-- Check that `tgt` is a goal about the floating point models, throwing an informative error
otherwise. -/
def checkFloatGoal (tgt : Expr) : MetaM Unit := do
  if (floatConsts tgt).isEmpty then
    throwError
      "`float_decide` only applies to goals about {floatTypeNames}, \
       but the goal mentions none of them:{indentExpr tgt}\n\
       Use `decide` (or an ordinary proof) instead."
  let foreign ← foreignConsts tgt
  unless foreign.isEmpty do
    throwError
      "`float_decide` refuses to evaluate this goal natively: besides the floating point \
       operations it mentions {foreign.toList}, which is outside the trusted floating point \
       fragment.{indentExpr tgt}"

/--
`float_decide` is `native_decide`, restricted to goals about the floating point types
 `Float`, `Float32` and `FloatArray`.

The goal must mention at least one constant of those types and no constants outside the
neutral whitelist (data types, logic, numeral and instance plumbing); otherwise the tactic
fails instead of appealing to the compiler.

Like `native_decide`, a proof produced by this tactic depends on `Lean.ofReduceBool`.
-/
syntax (name := floatDecide) "float_decide" : tactic

@[tactic floatDecide]
def evalFloatDecide : Tactic := fun _stx => do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  checkFloatGoal tgt
  evalTactic (← `(tactic| native_decide))

end FloatDecide
