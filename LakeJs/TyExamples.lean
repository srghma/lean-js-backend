module

public import LakeJs.Ty
public import LakeJs.TyDerived
public import LakeJs.TyPretty

@[expose] public section

/-!
# Worked examples: which Lean declaration becomes which `Ty`

Every definition below is checked when this file is elaborated, and every `example` is
closed by `decide`, so this file doubles as the test suite for the invariants of `Ty`.

Because well-formedness is *structural*, an ill-formed type is a **type error**, not a
`false`: the rejected cases are therefore shown as commented-out definitions, each
paired with an `example` proving that the corresponding shape condition really fails.
-/

open NonEmpty.String

namespace LakeJs.TyExamples

/-! ## Primitives: no unit types

`BitVec 0` has exactly one value, so it is a unit type.  `Ty.bitvec` takes a proof that
its width is positive, supplied automatically by `by decide`, so `.bitvec 0` does not
elaborate:

```lean
def bad : Ty := .bitvec 0   -- error: `decide` proved `0 < 0` is false
```

Every terminal type is a `PrimTy`, and `Ty.nat`, `Ty.bitvec n`, … are abbreviations
for `Ty.prim`: -/
def bv32 : Ty := .bitvec 32

example : (Ty.bitvec 32) = Ty.prim (.bitvec 32) := rfl
example : PrimTy.isNumberConfigurable (.bitvec 16) = false := by decide
example : PrimTy.isNumberConfigurable .nat = true := by decide

/-! ## Enum — `inductive Direction | north | south | east | west` -/

def direction : Ty :=
  .enum { name := nes!"Direction"
          ctor1 := nes!"north", ctor2 := nes!"south"
          ctorRest := [nes!"east", nes!"west"] }

-- A one-constructor "enum" is a unit type, and a zero-constructor one is void: the
-- schema has two mandatory constructors, so neither can be written at all.
-- Duplicate tags are rejected by `h_tags`:
example : fieldShapeOk [nes!"north", nes!"north"] = false := by decide

/-! ## Record — `structure Point where x, y : Float` -/

def point : Ty :=
  .record { name := nes!"Point", fields := .cons (nes!"x") .float
                                             (.cons (nes!"y") .float .nil) }

/-! Nesting works: `structure Point3 where p : Point; z : Float`. -/
def point3 : Ty :=
  .record { name := nes!"Point3", fields := .cons (nes!"p") point
                                              (.cons (nes!"z") .float .nil) }

-- A field-less record is a unit type: `fields` must be a `.cons`, so `.nil` is a type
-- error.  Duplicate field names are rejected by `h_names`:
example : fieldShapeOk [nes!"x", nes!"x"] = false := by decide

/-! ## Tagged union — `Option`, `Prod` -/

def optChar : Ty := .option .char
def pair : Ty := .prod .float .int64

/-! A tagged union none of whose constructors carries a field is an *enum*, and must be
written as one: `taggedUnionShapeOk` fails for it, so the schema does not elaborate. -/
example : taggedUnionShapeOk [(nes!"false", []), (nes!"true", [])] = false := by decide
example : taggedUnionShapeOk [(nes!"none", []), (nes!"some", [nes!"val"])] = true := by decide

/-! ## Recursive tagged union — `inductive MyList | nil | cons (hd : Int) (tl : MyList)` -/

def myList : Ty :=
  .recTaggedUnion
    { name  := nes!"MyList"
      ctors := .cons (nes!"nil") .nil
                (.cons (nes!"cons")
                  (.cons (nes!"hd") (.ty .int) (.cons (nes!"tl") .self .nil)) .nil) }

/-! `inductive Tree | leaf (kids : Array Tree) | node (v : Int) (kid : Tree)`: `leaf` is
a base constructor even though it mentions the type, because an `Array` may be empty. -/
def tree : Ty :=
  .recTaggedUnion
    { name  := nes!"Tree"
      ctors := .cons (nes!"leaf") (.cons (nes!"kids") (.array .self) .nil)
                (.cons (nes!"node")
                  (.cons (nes!"v") (.ty .int) (.cons (nes!"kid") .self .nil)) .nil) }

/-! `Option` guards a self occurrence just as `Array` does:
`inductive Chain | stop | link (next : Option Chain)`. -/
def chain : Ty :=
  .recTaggedUnion
    { name  := nes!"Chain"
      ctors := .cons (nes!"stop") .nil
                (.cons (nes!"link") (.cons (nes!"next") (.option .self) .nil) .nil) }

/-! A function *returning* the declared type is representable; a function taking one is
not, because that would be a negative occurrence — `SelfTy.fn` takes its parameter
types from `Ty`, not from `SelfTy`. -/
def lazyStream : Ty :=
  .recTaggedUnion
    { name  := nes!"Stream"
      ctors := .cons (nes!"done") .nil
                (.cons (nes!"step")
                  (.cons (nes!"head") (.ty .int)
                    (.cons (nes!"tail") (.fn [.nat] .self) .nil)) .nil) }

/-! Rejected: not actually recursive (that is a `Ty.enum` or a `Ty.taggedUnion`). -/
example : recTaggedUnionShapeOk [(nes!"a", []), (nes!"b", [(nes!"v", false, true)])] = false := by
  decide

/-! Rejected: not well-founded — every constructor needs a value of the type, so the
type is empty (`inductive Bad | l : Bad → Bad | r : Bad → Bad`). -/
example :
    recTaggedUnionShapeOk
        [(nes!"l", [(nes!"x", true, false)]), (nes!"r", [(nes!"x", true, false)])]
      = false := by decide

/-! Accepted: `MyList` and `Tree`. -/
example :
    recTaggedUnionShapeOk
        [(nes!"nil", []), (nes!"cons", [(nes!"hd", false, true), (nes!"tl", true, false)])]
      = true := by decide
example :
    recTaggedUnionShapeOk
        [(nes!"leaf", [(nes!"kids", true, true)]),
         (nes!"node", [(nes!"v", false, true), (nes!"kid", true, false)])]
      = true := by decide

/-! ## Recursive record — `structure Rose where v : Int; kids : Array Rose` -/

def rose : Ty :=
  .recObject
    { name   := nes!"Rose"
      fields := .cons (nes!"v") (.ty .int) (.cons (nes!"kids") (.array .self) .nil) }

/-! Rejected: `structure S where s : S` is uninhabited — the self occurrence is
unguarded. -/
example : recObjectShapeOk [(nes!"s", true, false)] = false := by decide

/-! Rejected: `structure S where s : Thunk S` is uninhabited too — a thunk is not a
guard, since forcing it must produce a value of the type. -/
example : recObjectShapeOk [(nes!"s", true, false)] = false := by decide

/-! Rejected: a "recursive" record that never mentions itself is a `Ty.record`. -/
example : recObjectShapeOk [(nes!"v", false, true)] = false := by decide

/-! ## Mutual families -/

/-! The "fake mutual" block of `Types.md`:

```lean
mutual
  inductive Color | red | blue
  inductive Shape | circle | box
end
```

No field of either type mentions the other, so the block is **two** `Ty.enum`s.  The
member graph has no edges, so it is not strongly connected and `LeanMutualRecFamily`
rejects it. -/
def colorShapeShape : FamShape :=
  [ (nes!"Color", [(nes!"Color.red", []), (nes!"Color.blue", [])])
  , (nes!"Shape", [(nes!"Shape.circle", []), (nes!"Shape.box", [])]) ]

example : famStronglyConnectedOk colorShapeShape = false := by decide
example : famShapeOk colorShapeShape = false := by decide

/-- A genuinely mutual block:

```lean
mutual
  inductive Exp  | lit (n : Int) | block (s : Stm)
  inductive Stm  | ret (e : Exp)
end
``` -/
def expStmShape : FamShape :=
  [ (nes!"Exp", [ (nes!"Exp.lit", [(nes!"n", .nonRec)])
                , (nes!"Exp.block", [(nes!"s", .recAt 1)]) ])
  , (nes!"Stm", [ (nes!"Stm.ret", [(nes!"e", .recAt 0)]) ]) ]

example : famShapeOk expStmShape = true := by decide

/-- Member `0` (`Exp`) of that block.  Note that the *non-recursive* fields carry real
`Ty`s (`Exp.lit` holds an `.int`), which the old family schema could not express. -/
def expTy : Ty :=
  .mutualRecursiveFamily
    { name    := nes!"Exp"
      member  := 0
      members :=
        .cons (nes!"Exp")
          (.cons (nes!"Exp.lit") (.consTy (nes!"n") .int .nil)
            (.cons (nes!"Exp.block") (.consRec (nes!"s") 1 .nil) .nil))
          (.cons (nes!"Stm")
            (.cons (nes!"Stm.ret") (.consRec (nes!"e") 0 .nil) .nil) .nil) }

/-- Member `1` (`Stm`) of the same block. -/
def stmTy : Ty :=
  .mutualRecursiveFamily
    { name    := nes!"Exp"
      member  := 1
      members :=
        .cons (nes!"Exp")
          (.cons (nes!"Exp.lit") (.consTy (nes!"n") .int .nil)
            (.cons (nes!"Exp.block") (.consRec (nes!"s") 1 .nil) .nil))
          (.cons (nes!"Stm")
            (.cons (nes!"Stm.ret") (.consRec (nes!"e") 0 .nil) .nil) .nil) }

-- There is no member `2`: `member := 2` fails `h_member`.
example : ¬ (2 < expStmShape.length) := by decide

/-! A non-mutual single-type family (`MyList` again) is not a `LeanMutualRecFamily`:
the schema demands two members structurally, and it must go through
`Ty.recTaggedUnion`. -/
def myListShape : FamShape :=
  [ (nes!"MyList", [ (nes!"nil", []), (nes!"cons", [(nes!"hd", .nonRec), (nes!"tl", .recAt 0)]) ]) ]

example : myListShape.length < 2 := by decide

/-! One direction only (`Wrap` mentions `Inner`, never the other way round) is two
independent declarations, not a mutual family. -/
def oneWayShape : FamShape :=
  [ (nes!"Wrap",  [ (nes!"Wrap.mk",  [(nes!"inner", .recAt 1)]) ])
  , (nes!"Inner", [ (nes!"Inner.mk", [(nes!"v", .nonRec)]) ]) ]

example : famStronglyConnectedOk oneWayShape = false := by decide

/-! A mutual block in which some member can never be built is not representable
either: every constructor of `B` needs an `A` and every constructor of `A` needs a
`B`. -/
def uninhabitedShape : FamShape :=
  [ (nes!"A", [ (nes!"A.mk", [(nes!"b", .recAt 1)]) ])
  , (nes!"B", [ (nes!"B.mk", [(nes!"a", .recAt 0)]) ]) ]

example : famStronglyConnectedOk uninhabitedShape = true := by decide
example : famWellFoundedOk uninhabitedShape = false := by decide
example : famShapeOk uninhabitedShape = false := by decide

/-! Guarding makes the same block well-founded: `A.mk` holds an `Array B`, which may be
empty. -/
def guardedShape : FamShape :=
  [ (nes!"A", [ (nes!"A.mk", [(nes!"bs", .recUnder .array 1)]) ])
  , (nes!"B", [ (nes!"B.mk", [(nes!"a", .recAt 0)]) ]) ]

example : famWellFoundedOk guardedShape = true := by decide
example : famShapeOk guardedShape = true := by decide

/-! ## Functions

`def foo : Unit → Int → Int` — the unit parameter is erased, so the outer function
takes no parameters at all. -/
def unitToIntToInt : Ty := .nullary (.fn [.int] .int)

/-! ## Rendering -/

example : (Ty.prod .float .float).pretty = "(record Prod fst:float snd:float)" := by
  decide

example : myList.pretty = "(recTaggedUnion MyList nil{}|cons{hd:int tl:self})" := by decide

-- `expTy.pretty` is `"(mutual Exp#0)"`, but the member index goes through
-- `toString : Nat → String`, which the kernel cannot evaluate, so it is not checked
-- by `decide` here.

end LakeJs.TyExamples

end
