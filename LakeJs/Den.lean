module

public import LakeJs.Ty
public import LakeJs.ExternEval

@[expose] public section

set_option autoImplicit false

/-!
# What a `Ty` *means*: runtime values, denotations and canonical inhabitants

The evaluator of `LakeJs.Reduce` is **denotational**: it maps a term of type `τ` to an
inhabitant of the Lean type `Ty.den τ`.  That is what makes totality free rather than a
theorem with a side condition — the evaluator is an ordinary Lean function, so the Lean
kernel itself is the proof that running a term stops
(`TERM_ONE_GRAMMAR_ASSESSMENT.md` §1, obligation O4).

This module is what the evaluator computes *in*:

* `Data` — the runtime tree of a value of a user-defined type: a tag and its fields,
  exactly the shape `LakeJs.Ty` prescribes (`{ tag: 0, _1: …, _2: … }`), plus a sequence
  node for an array or a list stored in a field, and a leaf for a scalar;
* `Ty.den` — the Lean type a `Ty` denotes.  Every *data* shape of `Ty` — `record`,
  `taggedUnion`, `recTaggedUnion`, `recObject`, `recAlias`, `mutualRecursiveFamily` —
  denotes `Data`.  The semantics does not need the schema: the schema is what the
  *grammar* checks (`Term.ctor` may only use a constructor the layout has), while the
  semantics only has to be total;
* `Ty.dflt` — the canonical inhabitant of every type.  This is what an exhausted
  recursion answers with, and what a lookup the schema would have ruled out answers with,
  so that no operation of the language has to be able to fail;
* `Ty.storable`, `Ty.toData`, `Ty.ofData` — writing a value into a field of a
  constructor and reading it back.  A function is not storable, and `Ty.ofData_toData`
  says that nothing else is lost.

## Why `Data` and not a typed value

A `Ty` of a recursive shape describes an infinite tree of types, so a *typed* runtime
value would be a fixed point of a schema interpretation — and deciding that the fixed
point exists is exactly the well-formedness check `LakeJs.RTyWf` already performs on the
type.  Denoting every data shape by the one untyped tree `Data` keeps the evaluator a
plain structural recursion on the term, which is the whole point: no fuel, no `Option`,
no `partial`.
-/

namespace LakeJs

/-! ## The runtime tree -/

/-- The runtime representation of a value the language stores: a constructor value, a
    sequence, a scalar, or the placeholder for a value that is not storable. -/
inductive Data where
  /-- A constructor value: its tag, and its fields in declaration order. -/
  | node : Nat → List Data → Data
  /-- A sequence — an array or a list — stored in a field. -/
  | seq : List Data → Data
  /-- A scalar of a terminal type. -/
  | leaf : (p : LeanPrimTy) → p.denote → Data
  /-- The placeholder for a value that has no runtime tree: a function, or a delay.
      `Ty.storable` is false exactly for the types whose values need it. -/
  | opaque : Data

instance : Inhabited Data := ⟨.node 0 []⟩

/-- The tag of a runtime value; anything but a constructor value has tag `0`. -/
def Data.tag : Data → Nat
  | .node t _ => t
  | _ => 0

/-- The fields of a runtime value; anything but a constructor value has none. -/
def Data.fields : Data → List Data
  | .node _ fs => fs
  | .seq fs => fs
  | _ => []

mutual

/-- The structural size of a runtime value.  This is the measure of a *structural*
    recursion: what the front end reads off the recursion subject.  It is an ordinary
    total Lean function, so it is no new piece of trust. -/
def Data.size : Data → Nat
  | .node _ fs => 1 + Data.sizeList fs
  | .seq fs => 1 + Data.sizeList fs
  | _ => 1

/-- The summed size of a list of runtime values. -/
def Data.sizeList : List Data → Nat
  | [] => 0
  | d :: ds => Data.size d + Data.sizeList ds

end

@[simp] theorem Data.size_node (t : Nat) (fs : List Data) :
    (Data.node t fs).size = 1 + Data.sizeList fs := by
  simp [Data.size]

@[simp] theorem Data.size_seq (fs : List Data) :
    (Data.seq fs).size = 1 + Data.sizeList fs := by
  simp [Data.size]

/-- Every field of a constructor value is strictly smaller than the value: this is why a
    structural recursion measured by `Data.size` really does descend. -/
theorem Data.size_lt_of_mem {x : Data} : ∀ {fs : List Data}, x ∈ fs →
    x.size < 1 + Data.sizeList fs := by
  intro fs h
  induction fs with
  | nil => cases h
  | cons y fs ih =>
    have hy : Data.sizeList (y :: fs) = y.size + Data.sizeList fs := by
      simp [Data.sizeList]
    cases h with
    | head => omega
    | tail _ h' =>
      have := ih h'
      omega

/-! ## Scalars -/

/-- Every terminal type is inhabited: it is a scalar, and a scalar has a zero. -/
instance instInhabitedDenote (p : LeanPrimTy) : Inhabited p.denote := by
  cases p <;> exact inferInstance

/-- The canonical value of a terminal type. -/
def LeanPrimTy.dflt (p : LeanPrimTy) : p.denote := @default _ (instInhabitedDenote p)

/-! ## What a type denotes -/

/-- The Lean type a `Ty` denotes.  A term of type `τ` evaluates to an inhabitant of it,
    which is what makes the evaluator total by construction.

    * a terminal type denotes the Lean type of its literals (`LeanPrimTy.denote`);
    * the function space denotes the Lean function space — the language is curried, so
      one argument and one result;
    * an array or a list denotes a `List`; a task, a promise and a thunk denote the value
      they will hold, since the language is pure and evaluation is eager; a `lazy` is a
      *delay*, so it denotes `Unit → …` (forcing it twice runs it twice);
    * an enumeration denotes the number of its constructor;
    * every other shape — the ones with a layout — denotes a runtime tree.

    It is `@[reducible]` so that instance search sees a denotation as the Lean type it
    is: `Ty.nat.den` *is* `Nat`, so `n + 1` and the numeral `0` elaborate at it without
    a detour. -/
@[reducible] def Ty.den : Ty → Type
  | .prim p => p.denote
  | .fn σ τ => σ.den → τ.den
  | .primCovariant (.array α) => List α.den
  | .primCovariant (.list α) => List α.den
  | .primCovariant (.task α) => α.den
  | .primCovariant (.promise α) => α.den
  | .primCovariant (.thunk α) => α.den
  | .primCovariant (.lazy α) => Unit → α.den
  | .enum _ => Nat
  | .record _ => Data
  | .taggedUnion _ => Data
  | .recTaggedUnion _ _ => Data
  | .recObject _ _ => Data
  | .recAlias _ _ => Data
  | .mutualRecursiveFamily _ _ => Data

/-- The canonical inhabitant of every type.  The exhausted branch of a recursion, a field
    read that the schema would have ruled out and an out-of-range index all answer with
    it, which is how the evaluator stays total without an error monad
    (`TERM_ONE_GRAMMAR_ASSESSMENT.md` §4). -/
def Ty.dflt : (τ : Ty) → τ.den
  | .prim p => p.dflt
  | .fn _ τ => fun _ => τ.dflt
  | .primCovariant (.array α) => show List α.den from []
  | .primCovariant (.list α) => show List α.den from []
  | .primCovariant (.task α) => α.dflt
  | .primCovariant (.promise α) => α.dflt
  | .primCovariant (.thunk α) => α.dflt
  | .primCovariant (.lazy α) => fun _ => α.dflt
  | .enum _ => show Nat from 0
  | .record _ => Data.node 0 []
  | .taggedUnion _ => Data.node 0 []
  | .recTaggedUnion _ _ => Data.node 0 []
  | .recObject _ _ => Data.node 0 []
  | .recAlias _ _ => Data.node 0 []
  | .mutualRecursiveFamily _ _ => Data.node 0 []

instance instInhabitedDen (τ : Ty) : Inhabited τ.den := ⟨τ.dflt⟩

/-! ## Storing a value in a field -/

/-- A type is *storable* when a value of it can be a field of a constructor, i.e. when it
    has a runtime tree.  A function is not, and neither is a delay; everything else is,
    a container exactly when its element type is. -/
def Ty.storable : Ty → Bool
  | .fn _ _ => false
  | .primCovariant (.lazy _) => false
  | .primCovariant (.array α) => α.storable
  | .primCovariant (.list α) => α.storable
  | .primCovariant (.task α) => α.storable
  | .primCovariant (.promise α) => α.storable
  | .primCovariant (.thunk α) => α.storable
  | _ => true

/-- Write a value into a runtime tree. -/
def Ty.toData : (τ : Ty) → τ.den → Data
  | .prim p, v => .leaf p v
  | .fn _ _, _ => .opaque
  | .primCovariant (.array α), xs => .seq (xs.map α.toData)
  | .primCovariant (.list α), xs => .seq (xs.map α.toData)
  | .primCovariant (.task α), v => α.toData v
  | .primCovariant (.promise α), v => α.toData v
  | .primCovariant (.thunk α), v => α.toData v
  | .primCovariant (.lazy _), _ => .opaque
  | .enum _, n => .node n []
  | .record _, d => d
  | .taggedUnion _, d => d
  | .recTaggedUnion _ _, d => d
  | .recObject _ _, d => d
  | .recAlias _ _, d => d
  | .mutualRecursiveFamily _ _, d => d

/-- Read a value back out of a runtime tree.  A tree of the wrong shape answers with the
    canonical inhabitant, which is what keeps the evaluator total. -/
def Ty.ofData : (τ : Ty) → Data → τ.den
  | .prim p, .leaf q v => if h : q = p then h ▸ v else p.dflt
  | .primCovariant (.array α), .seq ds => show List α.den from ds.map α.ofData
  | .primCovariant (.list α), .seq ds => show List α.den from ds.map α.ofData
  | .primCovariant (.task α), d => show α.den from α.ofData d
  | .primCovariant (.promise α), d => show α.den from α.ofData d
  | .primCovariant (.thunk α), d => show α.den from α.ofData d
  | .enum _, d => show Nat from d.tag
  | .record _, d => d
  | .taggedUnion _, d => d
  | .recTaggedUnion _ _, d => d
  | .recObject _ _, d => d
  | .recAlias _ _, d => d
  | .mutualRecursiveFamily _ _, d => d
  | τ, _ => τ.dflt

/-- Storing a value of a storable type and reading it back is the identity: a constructor
    field loses nothing. -/
theorem Ty.ofData_toData : ∀ (τ : Ty), τ.storable = true → ∀ (v : τ.den),
    τ.ofData (τ.toData v) = v
  | .prim p, _, v => by simp [Ty.toData, Ty.ofData]
  | .enum _, _, v => rfl
  | .record _, _, _ => rfl
  | .taggedUnion _, _, _ => rfl
  | .recTaggedUnion _ _, _, _ => rfl
  | .recObject _ _, _, _ => rfl
  | .recAlias _ _, _, _ => rfl
  | .mutualRecursiveFamily _ _, _, _ => rfl
  | .primCovariant (.array α), h, v => by
      have ih := Ty.ofData_toData α h
      show (List.map α.ofData (List.map α.toData v) : List α.den) = v
      induction v with
      | nil => rfl
      | cons x xs ihx => simp only [List.map_cons, ih x, ihx]
  | .primCovariant (.list α), h, v => by
      have ih := Ty.ofData_toData α h
      show (List.map α.ofData (List.map α.toData v) : List α.den) = v
      induction v with
      | nil => rfl
      | cons x xs ihx => simp only [List.map_cons, ih x, ihx]
  | .primCovariant (.task α), h, v => Ty.ofData_toData α h v
  | .primCovariant (.promise α), h, v => Ty.ofData_toData α h v
  | .primCovariant (.thunk α), h, v => Ty.ofData_toData α h v

/-! ## Values of a type that has a layout

`LakeJs.Layout` gives a type with constructors its **layout**: one entry per constructor,
each holding the types of that constructor's fields.  The data operations of the grammar —
`Term.ctor`, `Term.proj`, `Term.tagOf`, `Term.caseTag` — are checked against it, and these
three functions are how the evaluator runs them.  Three shapes carry their values in a
form of their own rather than as a `Data` tree, and each is handled here:

* a `Bool` is the two-constructor field-less sum, so its tag is `0` for `false` and `1`
  for `true` — the order Lean declares them in;
* a cons list is the built-in recursive sum, so `[]` has tag `0` and `x :: xs` tag `1`
  with the head and the tail as its two fields;
* an enumeration *is* its tag. -/

/-- The runtime tag of a value: which constructor it was built with. -/
def Ty.tagOfVal : (τ : Ty) → τ.den → Nat
  | .prim .bool, b => cond (b : Bool) 1 0
  | .primCovariant (.list α), v =>
      match (v : List α.den) with
      | [] => 0
      | _ :: _ => 1
  | .enum _, n => (n : Nat)
  | .record _, d => Data.tag d
  | .taggedUnion _, d => Data.tag d
  | .recTaggedUnion _ _, d => Data.tag d
  | .recObject _ _, d => Data.tag d
  | .recAlias _ _, d => Data.tag d
  | .mutualRecursiveFamily _ _, d => Data.tag d
  | _, _ => 0

/-- The fields of a value, in declaration order, as runtime trees. -/
def Ty.fieldsOfVal : (τ : Ty) → τ.den → List Data
  | .primCovariant (.list α), v =>
      match (v : List α.den) with
      | [] => []
      | x :: xs => [α.toData x, Data.seq (xs.map α.toData)]
  | .record _, d => Data.fields d
  | .taggedUnion _, d => Data.fields d
  | .recTaggedUnion _ _, d => Data.fields d
  | .recObject _ _, d => Data.fields d
  | .recAlias _ _, d => Data.fields d
  | .mutualRecursiveFamily _ _, d => Data.fields d
  | _, _ => []

/-- Build a value from a tag and its fields.  A tag or a field list the type does not
    have answers with the canonical inhabitant, so the operation is total; the grammar
    admits no such case, since `Term.ctor` carries the evidence that the constructor is
    one the layout has. -/
def Ty.buildVal : (τ : Ty) → Nat → List Data → τ.den
  | .prim .bool, tag, _ => show Bool from tag == 1
  | .primCovariant (.list α), tag, fs =>
      show List α.den from
        match tag, fs with
        | 1, [d, ds] => α.ofData d :: (Ty.primCovariant (.list α)).ofData ds
        | _, _ => []
  | .enum _, tag, _ => show Nat from tag
  | .record _, tag, fs => Data.node tag fs
  | .taggedUnion _, tag, fs => Data.node tag fs
  | .recTaggedUnion _ _, tag, fs => Data.node tag fs
  | .recObject _ _, tag, fs => Data.node tag fs
  | .recAlias _ _, tag, fs => Data.node tag fs
  | .mutualRecursiveFamily _ _, tag, fs => Data.node tag fs
  | τ, _, _ => τ.dflt

end LakeJs

end
