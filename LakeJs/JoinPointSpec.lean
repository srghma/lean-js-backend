import LakeJs.EmitJs
import LakeJs.Contify

/-!
# Join points, end to end

Three things are checked here, of a join point bound **inside a loop block**
(`Body.joinPointB`), which is the form the language gained last:

1. the contification pass finds it — a `let` of a lambda that is only ever called
   becomes a join point of the block, and its calls become jumps;
2. the emitted JavaScript is **unchanged** by that: a join point prints as the same
   local arrow, a jump as the same call, so contifying is a statement about the term and
   not about the output;
3. the result keeps to the usage discipline of `LakeJs.Usage`, which is what the form is
   for: the name is jumped to and never used as a value.
-/

namespace LakeJs.JoinPointSpec

open LakeJs
open LakeJs.Ty
open LakeJs.Expr
open LakeJs.EmitJs

/-- A loop whose block binds a local function and calls it from both arms of its
    conditional: `let f = (n) => n + slot; if (…) f(1) else f(2)`, all inside the
    `while`. -/
def loopWithLocalFn : Term [] [] Ty.nat :=
  .loop (σs := [Ty.nat]) (.cons (.lit (.nat 3)) .nil)
    (.letB (.lamN (params := [Ty.nat])
        (.apN (.extern .lean_nat_add) (.cons (♯0) (.cons (♯1) .nil))))
      (.iteB (.lit (.bool true))
        (.ret (.apN (♯0) (.cons (.lit (.nat 1)) .nil)))
        (.ret (.apN (♯0) (.cons (.lit (.nat 2)) .nil)))))

/-- The same loop after contification: the local function is a `Body.joinPointB` and the
    two calls are jumps. -/
def loopWithJoinPoint : Term [] [] Ty.nat :=
  .loop (σs := [Ty.nat]) (.cons (.lit (.nat 3)) .nil)
    (.joinPointB (params := [Ty.nat]) (σ := Ty.nat)
      (.apN (.extern .lean_nat_add) (.cons (♯0) (.cons (♯1) .nil)))
      (.iteB (.lit (.bool true))
        (.ret (.jump .head (.cons (.lit (.nat 1)) .nil)))
        (.ret (.jump .head (.cons (.lit (.nat 2)) .nil)))))

/-- **The pass finds it.** -/
example : Contify.Term.contify loopWithLocalFn = loopWithJoinPoint := rfl

/-- One declaration, as the module that binds it. -/
def jsOf (t : Term [] [] Ty.nat) : String :=
  render LakeJs.Config.JsConfig.presetPBO
    [({ name := "test", value := ⟨_, t⟩ } : JsDecl [])] 0

/-- **The output does not change.** -/
example : jsOf loopWithJoinPoint = jsOf loopWithLocalFn := by native_decide

/-- And this is what both print as: the join point is the `const v1 = …` of the loop
    body, and each jump is a call of it. -/
def expectedJs : String :=
  String.intercalate "\n"
    [ "export const test = (() => {"
    , "  let v0 = 3;"
    , "  while (true) {"
    , "    const v1 = (v1) => v1 + v0;"
    , "    if (true) {"
    , "      return v1(1);"
    , "    } else {"
    , "      return v1(2);"
    , "    }"
    , "  }"
    , "})();"
    , "" ]

example : jsOf loopWithJoinPoint = expectedJs := by native_decide

/-- **The result keeps to the discipline**, and so does the term it came from — a `let`
    read twice is a `let` that shares.  What contifying adds is that the term now says
    the name never escapes. -/
example : Usage.Term.usesOk [] loopWithJoinPoint = true := by decide +kernel

example : Usage.Term.usesOk [] loopWithLocalFn = true := by decide +kernel

/-- A join point of a block that nothing jumps to is refused, as one of a term is. -/
example :
    Usage.Term.usesOk []
      (.loop (σs := [Ty.nat]) (.cons (.lit (.nat 3)) .nil)
        (.joinPointB (params := [Ty.nat]) (σ := Ty.nat)
          (.apN (.extern .lean_nat_add) (.cons (♯0) (.cons (♯1) .nil)))
          (.ret (♯1))) : Term [] [] Ty.nat) = false := by decide +kernel

end LakeJs.JoinPointSpec
