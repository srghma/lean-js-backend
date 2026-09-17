import LakeJs.TermElab
import LakeJs.TermDeelab
import LakeJs.Usage

/-!
# The surface syntax, checked against the terms it stands for

Every example below is written twice: once as the constructors of
`LakeJs.Expr.Term`, and once in the surface syntax of `LakeJs.TermElab`.  That the two
are the *same* term is checked by `rfl`, so the elaborator is checked against the
language it elaborates into, one constructor at a time.

The other direction is checked by `Term.roundTrips`: the text a term delaborates to is
parsed again and printed again, and the two texts have to agree.  That is a fact about
the printer of `LakeJs.Surface` and the parser of `LakeJs.SurfaceParse` together, and it
holds for the floating point constants too, which `rfl` cannot see through — a `Float`
is written as the bits of its representation, and `Float.ofBits` does not reduce.
-/

namespace LakeJs.TermSyntaxSpec

open LakeJs
open LakeJs.Expr

/-- The signature the examples that name a declaration are written against. -/
abbrev Sg1 : Sig := [⟨"gcd", .fn [.nat, .nat] .nat⟩, ⟨"pi", .float⟩]

/-! ## A lambda, an extern and a constant -/

/-- `(n : Nat) => n + 1`. -/
def addOne : Term [] [] (.fn [.nat] .nat) :=
  .lamN (params := [Ty.nat])
    (.apN (.extern .lean_nat_add) (.cons (.var .head) (.cons (.lit (.nat 1)) .nil)))

example : addOne = [LEAN|
sig (fn [nat] nat)
|glob
|vars
|
(fn [v0 : nat]
  (app
    (extern lean_nat_add)
    v0
    (lit nat 1)
  )
)
] := rfl

#guard addOne.roundTrips

/-! ## A polymorphic extern writes its type arguments down -/

/-- `(xs : Array Nat) => xs.size`, in a context that already holds the array. -/
def arraySize : Term Sg1 [.array .nat] .nat :=
  .apN (.extern (.lean_array_get_size Ty.nat)) (.cons (.var .head) .nil)

example : arraySize = [LEAN|
sig nat
|glob gcd : (fn [nat, nat] nat), pi : float
|vars v0 : (array nat)
|
(app
  (extern lean_array_get_size nat)
  v0
)
] := rfl

#guard arraySize.roundTrips

/-! ## A constructor, a projection and a tag -/

/-- `{ tag: 0, _1: 7, _2: true }`. -/
def pair : Term Sg1 [] ((.prod .nat .bool)) :=
  .ctor 0 _ rfl (.cons (.lit (.nat 7)) (.cons (.lit (.bool true)) .nil))

example : pair = [LEAN|
sig (record [nat, bool])
|glob gcd : (fn [nat, nat] nat), pi : float
|vars
|
(ctor 0 : (record [nat, bool])
  (lit nat 7)
  (lit bool true)
)
] := rfl

#guard pair.roundTrips

/-- `let x = p._1; x`, the second read being a `cast` that costs nothing. -/
def firstField : Term Sg1 [(.prod .nat .bool)] .nat :=
  .letE (σ := .nat) (.proj (.var .head) 0 0 rfl)
    (.jsOp (.cast .nat .nat) (.cons (.var .head) .nil))

example : firstField = [LEAN|
sig nat
|glob gcd : (fn [nat, nat] nat), pi : float
|vars v0 : (record [nat, bool])
|
(let v1 : nat =
  (proj 0 0
    v0
  )
  (op cast nat nat
    v1
  )
)
] := rfl

#guard firstField.roundTrips

/-- The runtime tag of an `Option Nat`. -/
def optionTag : Term Sg1 [(.option .nat)] .nat :=
  .tagOf (.var .head) rfl

example : optionTag = [LEAN|
sig nat
|glob gcd : (fn [nat, nat] nat), pi : float
|vars v0 : (union [[], [nat]])
|
(tagOf
  v0
)
] := rfl

#guard optionTag.roundTrips

/-! ## A dispatch on the tag -/

/-- `match o with | none => 0 | some n => n`. -/
def optionOrZero : Term [⟨"g", .nat⟩] [(.option .nat)] .nat :=
  .caseTag (.var .head)
    (.cons 0 (.lit (.nat 0)) (.deflt (.proj (.var .head) 1 0 rfl)))
    rfl

example : optionOrZero = [LEAN|
sig nat
|glob g : nat
|vars v0 : (union [[], [nat]])
|
(case
  v0
  (tag 0
    (lit nat 0)
  )
  (default
    (proj 1 0
      v0
    )
  )
)
] := rfl

#guard optionOrZero.roundTrips

/-! ## A name of the signature, and the operations that are JavaScript's -/

/-- `String(pi)`, `pi` being a declaration of the signature. -/
def showPi : Term Sg1 [] .string :=
  .jsOp (.toStr .float) (.cons (.global (.there .here)) .nil)

example : showPi = [LEAN|
sig string
|glob gcd : (fn [nat, nat] nat), pi : float
|vars
|
(op toStr float
  pi
)
] := rfl

#guard showPi.roundTrips

/-- `!false ? gcd(3, 2) : 0`, which names the other declaration of the signature. -/
def gcdOrZero : Term Sg1 [] .nat :=
  .ite (.jsOp .boolNot (.cons (.lit (.bool false)) .nil))
    (.apN (.global .here) (.cons (.lit (.nat 3)) (.cons (.lit (.nat 2)) .nil)))
    (.lit (.nat 0))

example : gcdOrZero = [LEAN|
sig nat
|glob gcd : (fn [nat, nat] nat), pi : float
|vars
|
(if
  (op boolNot
    (lit bool false)
  )
  (app
    gcd
    (lit nat 3)
    (lit nat 2)
  )
  (lit nat 0)
)
] := rfl

#guard gcdOrZero.roundTrips

/-! ## A loop: the only repetition the language has -/

/-- `Tco01`'s `test`, which `LakeJs.Expr` also writes out by hand. -/
example : (Term.tco01 (Sg := [])) = [LEAN|
sig (fn [nat] nat)
|glob
|vars
|
(fn [v0 : nat]
  (loop [v1 : nat]
    v0
    (ifB
      (app
        (extern lean_nat_dec_eq)
        v1
        (lit nat 0)
      )
      (ret
        v1
      )
      (cont
        (app
          (extern lean_nat_sub)
          v1
          (lit nat 1)
        )
      )
    )
  )
)
] := rfl

#guard (Term.tco01 (Sg := [])).roundTrips

/-- A loop whose body binds a value before it decides: `letB` and `iteB` together. -/
def countDown : Term [] [] (.fn [.nat] .nat) :=
  [LEAN|
sig (fn [nat] nat)
|glob
|vars
|
(fn [v0 : nat]
  (loop [v1 : nat]
    v0
    (letB v2 : bool = (app (extern lean_nat_dec_eq) v1 (lit nat 0))
      (ifB
        v2
        (ret (lit nat 0))
        (cont (app (extern lean_nat_sub) v1 (lit nat 1)))
      )
    )
  )
)
]

example : countDown =
    .lamN (params := [Ty.nat])
      (.loop (σs := [Ty.nat]) (.cons (.var .head) .nil)
        (.letB (σ := Ty.bool)
          (.apN (.extern .lean_nat_dec_eq)
            (.cons (.var .head) (.cons (.lit (.nat 0)) .nil)))
          (.iteB (.var .head)
            (.ret (.lit (.nat 0)))
            (.cont (.cons (.apN (.extern .lean_nat_sub)
              (.cons (.var (.tail .head)) (.cons (.lit (.nat 1)) .nil))) .nil))))) := rfl

#guard countDown.roundTrips

/-! ## A function that answers with several values, and a call that keeps one -/

-- the user's example: `(v0, v1) => (v2, v3) => { return [1, 1.0]; }`
#guard (Term.fooReturnsProd (Sg := [])).roundTrips

/-- `Term.fooReturnsProd`, written in the surface syntax.  A `Float` is written as the
    bits of its representation — `4607182418800017408` is `1.0` — so the text is exact;
    `rfl` cannot see that `Float.ofBits` of those bits *is* `1.0`, so the two terms are
    compared as the text they delaborate to. -/
def fooWritten : Term [] []
    (.fn [Ty.int, Ty.float] (.fn_returnsProd [Ty.int, Ty.float] Ty.int [Ty.float])) :=
  [LEAN|
sig (fn [int, float] (fnProd [int, float] [int, float]))
|glob
|vars
|
(fn [v0 : int, v1 : float]
  (prodFn [v2 : int, v3 : float]
    (lit int 1)
    (lit float 4607182418800017408)
  )
)
]

#guard fooWritten.deelab == (Term.fooReturnsProd (Sg := [])).deelab

/-- Calling such a function and keeping its second result. -/
def secondResult : Term [] [] .float :=
  [LEAN|
sig float
|glob
|vars
|
(callProd 1
  (prodFn [v0 : int, v1 : float]
    (lit int 1)
    v1
  )
  (lit int 2)
  (lit float 4607182418800017408)
)
]

#guard secondResult.roundTrips

/-! ## The constants that are not numbers -/

/-- One constant of each of the shapes whose text is not just a number. -/
def constants : Term [] []
    (.record ⟨.char, .string, [.name, .substring, .byteArray, .bitvec 8]⟩) :=
  [LEAN|
sig (record [char, string, name, substring, byteArray, (bitvec 8)])
|glob
|vars
|
(ctor 0 : (record [char, string, name, substring, byteArray, (bitvec 8)])
  (lit char 'q')
  (lit string "a \"quoted\" line\n")
  (lit name "Foo.bar")
  (lit substring "hello" 1 3)
  (lit byteArray [1, 2, 255])
  (lit bitvec 8 200)
)
]

#guard constants.roundTrips

example : constants =
    .ctor 0 _ rfl
      (.cons (.lit (.char 'q'))
        (.cons (.lit (.string "a \"quoted\" line\n"))
          (.cons (.lit (.name `Foo.bar))
            (.cons (.lit (.substring "hello" 1 3))
              (.cons (.lit (.byteArray #[1, 2, 255]))
                (.cons (.lit (.bitvec (n := 8) (h := by decide) 200)) .nil)))))) := rfl

/-! ## The header sections may be written in any order, and may be left out

The delaborator writes `sig`, then `glob`, then `vars`, then the code, but the parser
takes the three sections in whatever order they come and fills in what is missing from
the type the fragment is elaborated against: an omitted `sig` is the expected type, an
omitted `glob` the empty signature, an omitted `vars` the empty context. -/

/-- `arraySize`, with the header sections in the reverse order. -/
example : arraySize = [LEAN|
vars v0 : (array nat)
|glob gcd : (fn [nat, nat] nat), pi : float
|sig nat
|
(app
  (extern lean_array_get_size nat)
  v0
)
] := rfl

/-- `arraySize` again, with `sig` left out: the type it is checked against says it. -/
example : arraySize = [LEAN|
glob gcd : (fn [nat, nat] nat), pi : float
|vars v0 : (array nat)
|
(app
  (extern lean_array_get_size nat)
  v0
)
] := rfl

/-- `addOne` with no header at all: it names no declaration and reads no variable of
    the context it is written in, so there is nothing for the header to say. -/
example : addOne = [LEAN|
(fn [v0 : nat]
  (app
    (extern lean_nat_add)
    v0
    (lit nat 1)
  )
)
] := rfl


/-! ## Join points: the term's own, and a loop block's

`(join j […] : τ body rest)` binds a name the rest may only *jump* to, and
`(joinB j […] : τ body rest)` is the same inside a loop block (`Body.joinPointB`). -/

/-- The join point of `LakeJs.Usage.joinExample`, written in the surface syntax: one
    parameter, jumped to from both arms of a conditional. -/
example : LakeJs.Usage.joinExample = [LEAN|
sig nat
|glob
|vars
|
(join v0 [v0 : nat] : nat
  (app
    (extern lean_nat_add)
    v0
    v0
  )
  (if
    (lit bool true)
    (jump v0 (lit nat 1))
    (jump v0 (lit nat 2))
  )
)
] := rfl

#guard LakeJs.Usage.joinExample.roundTrips

/-- A join point **of a loop block**: the block binds it, both arms of its conditional
    jump to it, and the jump is what the block answers with. -/
def loopJoin : Term [] [] Ty.nat :=
  [LEAN|
sig nat
|glob
|vars
|
(loop [v0 : nat]
  (lit nat 3)
  (joinB v1 [v1 : nat] : nat
    (app
      (extern lean_nat_add)
      v1
      v0
    )
    (ifB
      (lit bool true)
      (ret (jump v1 (lit nat 1)))
      (ret (jump v1 (lit nat 2)))
    )
  )
)
]

example : loopJoin =
    .loop (σs := [Ty.nat]) (.cons (.lit (.nat 3)) .nil)
      (.joinPointB (params := [Ty.nat]) (σ := Ty.nat)
        (.apN (.extern .lean_nat_add)
          (.cons (.var .head) (.cons (.var (.tail .head)) .nil)))
        (.iteB (.lit (.bool true))
          (.ret (.jump .head (.cons (.lit (.nat 1)) .nil)))
          (.ret (.jump .head (.cons (.lit (.nat 2)) .nil))))) := rfl

#guard loopJoin.roundTrips

/-- And it keeps to the usage discipline: the join point is jumped to, its parameter is
    read, and its name is never used as a value. -/
example : LakeJs.Usage.Term.usesOk [] loopJoin = true := by decide +kernel

end LakeJs.TermSyntaxSpec
