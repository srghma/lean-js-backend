import LakeJs.TyMeta
import LakeJs.TyDerived

/-!
# Worked examples for `lean_ty%`, `lean_…_schema%` and `derive_ty`

Each declaration below is a real Lean type, and the `Ty` next to it is read off the
environment while this file is elaborated — by the same translation the backend uses to
compile code — so this file is also the test suite of `LakeJs.TyMeta` and
`LakeJs.TyDerive`.  Every `example` is closed by `rfl` or `decide`.

Three declarations that *used* to have a `Ty` no longer have one, because the type
language no longer has the degenerate shapes: a type with a single value (`Unit`), a
type with none (`Empty`), and a sum of two field-less constructors, which is now
modelled as `Ty.bool`.  They are shown, refused, in the last section.
-/

open LakeJs LakeJs.Ty

namespace LakeJs.TyMetaExamples

/-! ## Enum

An enum has three constructors or more; `LeanEnumSchema` holds the number *beyond* those
three. -/

inductive Direction where
  | north | south | east | west
  deriving Repr

/-- Four constructors, none with a field, numbered from `0`. -/
def directionSchema : LeanEnumSchema := lean_enum_schema% Direction

/-- The same type, as the `Ty` it is. -/
def directionTy : Ty := lean_ty% Direction

example : directionSchema = ⟨1, 0⟩ := rfl
example : directionSchema.nOfConstructors = 4 := rfl
example : directionTy = .enum ⟨1, 0⟩ := rfl

/-- A sum of exactly two field-less constructors is a **boolean**: that is how the
    backend models it, so it prints as `true`/`false` rather than as `0`/`1`. -/
inductive Side where
  | left | right

example : (lean_ty% Side) = Ty.bool := rfl

/-- `Ordering` is the enum the runtime comparisons answer with, numbered from `-1`. -/
example : (lean_ty% Ordering) = Ty.ordering := rfl

/-! ## Record -/

structure Point where
  x : Float
  y : Float

def pointSchema : LeanRecordSchema Ty := lean_record_schema% Point
def pointTy : Ty := lean_ty% Point

example : pointSchema = ⟨.float, .float, []⟩ := rfl
example : pointTy = .record ⟨.float, .float, []⟩ := rfl
example : pointTy.pretty = "(record float float)" := by decide

/-- A record whose field is another user-defined type: that type's own `Ty` is expanded
    in place, since the type language has no names to refer to it by. -/
structure Segment where
  from_ : Point
  to_ : Point
  label : String

example : (lean_ty% Segment) = .record ⟨pointTy, pointTy, [.string]⟩ := rfl

/-! ## Tagged union -/

inductive Shape where
  | circle (r : Float)
  | rect (w : Float) (h : Float)

def shapeSchema : LeanTaggedUnionSchema Ty := lean_tagged_union_schema% Shape

example : shapeSchema = .payloadFirst ⟨.float, []⟩ [.float, .float] [] := rfl
example : shapeSchema.toList = [[.float], [.float, .float]] := rfl
example : (lean_ty% Shape) = .taggedUnion shapeSchema := rfl

/-- A parameterised declaration is read **at its instantiation**, so the elaborator
    takes a type, not only a name. -/
example :
    (lean_ty% (Except Nat String)) = .taggedUnion (.payloadFirst ⟨.nat, []⟩ [.string] []) :=
  rfl
example : (lean_ty% (Option Nat)) = Ty.option .nat := rfl
example : (lean_ty% (Array (Option Nat))) = .array (Ty.option .nat) := rfl
example : (lean_ty% (Nat → Nat)) = .fn [.nat] .nat := rfl

/-! ## Recursive tagged union -/

inductive MyList where
  | nil
  | cons (hd : Int) (tl : MyList)

def myListSchema : LeanTaggedUnionSchema Ty.RTy := lean_rec_tagged_union_schema% MyList
def myListTy : Ty := lean_ty% MyList

example : myListSchema = ⟨.skip (.here ⟨.prim .int, [.self 0]⟩ [])⟩ := rfl
example : myListSchema.ctors.toList = [[], [.prim .int, .self 0]] := rfl
example : myListTy = .recTaggedUnion myListSchema := rfl
example : myListTy.pretty = "(recTaggedUnion ()|(int self#0))" := by decide

/-- An `Option` guards a self occurrence, so `link` is a base constructor — and it is
    an ordinary tagged union *inside* the recursive shape, not a scope of its own. -/
inductive Chain where
  | stop
  | link (next : Option Chain)

example :
    (lean_ty% Chain)
      = .recTaggedUnion
          ⟨.skip (.here ⟨.taggedUnion (.skip (.here ⟨.self 0, []⟩ [])), []⟩ [])⟩ := rfl

/-! ## Recursive record -/

structure Rose where
  v : Int
  kids : Array Rose

def roseSchema : LeanRecordSchema Ty.RTy := lean_rec_object_schema% Rose

example : roseSchema = ⟨⟨.prim .int, .array (.self 0), []⟩⟩ := rfl
example : (lean_ty% Rose).pretty = "(recObject int (array self#0))" := by decide

/-- A self occurrence may sit inside a pair, as long as it is guarded: an
    `Array (Int × Forest)` may be empty, so a `Forest` can be built. -/
structure Forest where
  label : String
  kids : Array (Int × Forest)

example :
    (lean_ty% Forest)
      = .recObject ⟨⟨.prim .string, .array (.record ⟨.prim .int, .self 0, []⟩), []⟩⟩ :=
  rfl

/-! ## Newtypes are erased

A declaration left with one constructor carrying one runtime field has no object of its
own. -/

/-- `structure Rose2 where kids : Array Rose2` — a *recursive* newtype: the wrapper is
    erased and the type is the fixed point `Rose2 = Array Rose2`, i.e. in JS an array of
    arrays of … -/
structure Rose2 where
  kids : Array Rose2

def rose2Schema : Ty.RTy := lean_rec_alias_schema% Rose2

example : rose2Schema = ⟨.array (.self 0)⟩ := rfl
example : (lean_ty% Rose2) = .recAlias ⟨.array (.self 0)⟩ := rfl

/-- A **non-recursive** newtype disappears completely: a `Wrapper` *is* a `Nat`. -/
structure Wrapper where
  x : Nat

example : (lean_ty% Wrapper) = Ty.nat := rfl

/-! ## Fields that carry nothing are dropped -/

/-- A proof field carries nothing at run time, so `Positive` is a `Nat` — a newtype
    again, once the proof is gone. -/
structure Positive where
  val : Nat
  pos : 0 < val

example : (lean_ty% Positive) = Ty.nat := rfl

/-- A type field is dropped, and the value field whose type it is becomes a
    `Ty.typeParam`: the caller chooses the type, so the compiled code can only pass the
    value on. -/
structure Unfold where
  State : Type
  seed : State
  step : Nat

example : (lean_ty% Unfold) = .record ⟨.typeParam, .nat, []⟩ := rfl

/-! ## Genuinely mutual family -/

mutual
  inductive Exp where
    | lit (n : Int)
    | block (s : Stm)
  inductive Stm where
    | ret (e : Exp)
    | seq (ss : List Stm) (tail : Exp)
end

def expFamily : LeanMutualRecFamily Ty.RTy := lean_mutual_rec_family% Exp
def stmFamily : LeanMutualRecFamily Ty.RTy := lean_mutual_rec_family% Stm

/-- Both members are types of the *same* block, differing only in which member they
    are. -/
example : expFamily.members = stmFamily.members := rfl
example : expFamily.memberIdx = 0 := rfl
example : stmFamily.memberIdx = 1 := rfl

example :
    expFamily.members
      = [ .ctors (.payloadFirst ⟨.prim .int, []⟩ [.self 1] [])
        , .ctors (.payloadFirst ⟨.self 0, []⟩ [.list (.self 1), .self 0] []) ] := rfl

/-- What the elaborators check is exactly what `LakeJs.TySchema` says a family has to
    be: two members that reach each other, and values for both. -/
example : LeanMutualRecFamily.wf expFamily = true := by decide

/-! ## A mutual block with an **alias member**

A member left with one constructor carrying one field is a newtype there too: `Block`
below is just an `Array Line`, with no tag and no wrapping object. -/

mutual
  inductive Line where
    | text (s : String)
    | nested (b : Block)
  inductive Block where
    | mk (lines : Array Line)
end

def lineFamily : LeanMutualRecFamily Ty.RTy := lean_mutual_rec_family% Line

example :
    lineFamily.members
      = [.ctors (.payloadFirst ⟨.prim .string, []⟩ [.self 1] []),
         .alias (.array (.self 0))] := rfl
example : LeanMutualRecFamily.wf lineFamily = true := by decide
example : (lean_mutual_rec_family% Block).memberIdx = 1 := rfl

/-! ## `derive_ty`: parameterised declarations

`lean_ty%` reads a *type*.  A declaration with type parameters is a family of types, so
what it has is a function from `Ty` to `Ty`, generated by `derive_ty`; that is how
`LakeJs.TyDerived` checks `Ty.option` and `Ty.prod` against Lean's own `Option` and
`Prod`. -/

example : Ty.option .char = .taggedUnion (.skip (.here ⟨.char, []⟩ [])) := rfl
example : Ty.prod .float .int64 = .record ⟨.float, .int64, []⟩ := rfl

/-- A parameterised record. -/
structure Boxed (α : Type) where
  value : α
  label : String

derive_ty Boxed as boxedTy

example : boxedTy .int = .record ⟨.int, .string, []⟩ := rfl

/-- A parameterised recursive declaration: the occurrence of `MyListG α` inside
    itself is `RTy.self 0`, and the parameter is the generated function's argument, read
    one layer down (`Ty.toRTy`). -/
inductive MyListG (α : Type) where
  | nil
  | cons (hd : α) (tl : MyListG α)

derive_ty MyListG as myListGTy

example :
    myListGTy .string = .recTaggedUnion ⟨.skip (.here ⟨.prim .string, [.self 0]⟩ [])⟩ :=
  rfl

/-- The derived function agrees with the declaration read at an instantiation. -/
example : myListGTy .int = lean_ty% (MyListG Int) := rfl

/-- A parameterised sum type whose payload mentions both parameters. -/
inductive Choice (α β : Type) where
  | left (l : α)
  | right (r : β)
  | both (l : α) (r : β)

derive_ty Choice as choiceTy

example :
    choiceTy .int .bool
      = .taggedUnion (.payloadFirst ⟨.int, []⟩ [.bool] [[.int, .bool]]) := rfl

/-- A parameter is told apart from a scalar the declaration mentions itself: `b` below
    is a `Float32` whatever the parameter is, and the generated function says so. -/
structure Mixed (α : Type) where
  a : α
  b : Float32
  c : Nat

derive_ty Mixed as mixedTy

example : mixedTy .int = .record ⟨.int, .float32, [.nat]⟩ := rfl
example : mixedTy .float32 = .record ⟨.float32, .float32, [.nat]⟩ := rfl

/-- A parameterised **newtype**: the wrapper is erased, so the generated function is the
    identity on `Ty`. -/
structure Ident (α : Type) where
  value : α

derive_ty Ident as identTy

example : identTy .int = Ty.int := rfl
example : identTy (Ty.array .string) = .array .string := rfl

/-! ## What is refused

Each of these is an elaboration error, so it is shown commented out.  The first three
are the degenerate types the language no longer has: a declaration whose `Ty` would be
one of them is refused where it is read, rather than modelled by something it is not.

```lean
def bad0 : Ty := lean_ty% Unit                                -- a single value
def bad1 : Ty := lean_ty% Empty                               -- no values
structure WithUnit where a : Nat; u : Unit
def bad2 : Ty := lean_ty% WithUnit                            -- a field of unit type

mutual
  inductive Color where | red | blue
  inductive Sha where | circle | box
end
def bad3 : Ty := lean_ty% Color    -- two field-less members: two booleans, not a family

def bad4 : LeanEnumSchema := lean_enum_schema% Point          -- `Point` is a record
def bad5 : LeanRecordSchema Ty := lean_record_schema% Rose    -- `Rose` is recursive
def bad6 : LeanRecordSchema Ty.RTy := lean_rec_object_schema% Rose2 -- a newtype
def bad7 : LeanRecordSchema Ty := lean_record_schema% Wrapper -- a newtype: it is a Nat
def bad8 : Ty := lean_ty% Option                              -- a family, not a type
derive_ty Vector as vectorTy   -- `n : Nat` is a value parameter, i.e. an index
```
-/

end LakeJs.TyMetaExamples
