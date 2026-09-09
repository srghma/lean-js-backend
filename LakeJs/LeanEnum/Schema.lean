module

public import Std.Data.HashSet
import Aesop

@[expose] public section

/-!
# Runtime representation of Lean enums (schemas + values)

This module contains the pure (non-meta) layer:

* `LeanEnumCtorSchema` / `LeanEnumSchema` — descriptions of an inductive type,
* `LeanEnum` — a runtime value tagged by a constructor of a schema,
* `LeanEnumAt` — the constructor-indexed ("unboxed") variant,
* `LeanEnum.unboxAt` — the O(1) cast between the two, with all invariants proved.

The metaprogramming layer (`lean_schema%`, `mkEnum!`, `mkEnumAt!`) lives in
`RequestProject.LeanEnum.Meta`, which imports this module. The split is required:
compile-time (meta) code can only call functions coming from *imported* modules.
-/

/-! ### 1. Schema Definitions -/

structure LeanEnumCtorSchema where
  name      : String
  h_name_ne : name != "" := by decide
  numFields : Nat
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

/-! #### The "pairwise distinct constructor names" invariant

This is the invariant that makes name-based lookup (`findCtor?`) unambiguous, and
hence makes `ctorNumFields_of_mem` — and everything built on it — provable.

It is stated as a genuine `Prop`, `CtorNamesNodup`, and not as a `Bool`-valued scan
coerced to `Prop` with `= true`. Reasons:

* it says exactly what is meant (`List.Nodup` of the names), so lemmas about it are
  ordinary `List.Nodup` lemmas rather than lemmas about a bespoke recursion;
* it is proof-irrelevant, so it can never make two otherwise-equal schemas differ;
* it costs nothing in convenience: the `Decidable` instance below keeps
  `h_ctors_nodup := by decide` working on concrete schema literals.

Efficiency: the *decision procedure* used by `decide` is the structural one, which
is quadratic — deliberately, because `decide` is kernel evaluation and string
hashing (`String.hash` is `@[extern]`) does not reduce in the kernel. For checking
at *runtime* — which is what `extractEnumSchema` does when it validates a schema
read off a real inductive type — `ctorNamesNodupFast` does a single left-to-right
pass carrying a `Std.HashSet` of the names already seen: expected `O(n)` instead of
`O(n²)`, and no repeated `String` comparisons. `ctorNamesNodupFast_iff` proves the
two agree, so the fast check can be used to *produce* the `Prop` field. -/

/-- All constructor names in a list are pairwise distinct. -/
def CtorNamesNodup (ctors : List LeanEnumCtorSchema) : Prop :=
  (ctors.map (·.name)).Nodup

instance (ctors : List LeanEnumCtorSchema) : Decidable (CtorNamesNodup ctors) :=
  inferInstanceAs (Decidable (List.Nodup _))

@[simp] theorem ctorNamesNodup_nil : CtorNamesNodup [] := List.nodup_nil

theorem ctorNamesNodup_cons_iff {c : LeanEnumCtorSchema} {cs : List LeanEnumCtorSchema} :
    CtorNamesNodup (c :: cs) ↔ (∀ d ∈ cs, d.name ≠ c.name) ∧ CtorNamesNodup cs := by
  unfold CtorNamesNodup
  rw [List.map_cons, List.nodup_cons]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun d hd hde => h1 (List.mem_map.mpr ⟨d, hd, hde⟩), h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun hmem => ?_, h2⟩
    obtain ⟨d, hd, hde⟩ := List.mem_map.mp hmem
    exact h1 d hd hde

/-- Worker for `ctorNamesNodupFast`: one pass, carrying the set of names seen so far. -/
def nodupAux : List LeanEnumCtorSchema → Std.HashSet String → Bool
  | []      , _    => true
  | c :: cs , seen => !seen.contains c.name && nodupAux cs (seen.insert c.name)

/-- Linear-time (expected) check that all constructor names are pairwise distinct.
    Equivalent to `CtorNamesNodup` by `ctorNamesNodupFast_iff`. -/
def ctorNamesNodupFast (ctors : List LeanEnumCtorSchema) : Bool :=
  nodupAux ctors ∅

theorem nodupAux_eq_true_iff (l : List LeanEnumCtorSchema) (seen : Std.HashSet String) :
    nodupAux l seen = true ↔ CtorNamesNodup l ∧ ∀ c ∈ l, seen.contains c.name = false := by
  induction l generalizing seen with
  | nil => simp [nodupAux]
  | cons c cs ih =>
    simp only [nodupAux, Bool.and_eq_true, Bool.not_eq_true', ih, CtorNamesNodup,
      List.map_cons, List.nodup_cons, List.mem_map, List.mem_cons,
      Std.HashSet.contains_insert, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    constructor
    · rintro ⟨hc, hnodup, hrest⟩
      refine ⟨⟨?_, hnodup⟩, ?_⟩
      · rintro ⟨x, hx, hxe⟩
        exact (hrest x hx).1 hxe.symm
      · rintro d (rfl | hd)
        · exact hc
        · exact (hrest d hd).2
    · rintro ⟨⟨hnotmem, hnodup⟩, hseen⟩
      refine ⟨hseen c (Or.inl rfl), hnodup, ?_⟩
      intro d hd
      exact ⟨fun h => hnotmem ⟨d, hd, h.symm⟩, hseen d (Or.inr hd)⟩

/-- The fast (hash-set) check decides the `CtorNamesNodup` invariant. -/
theorem ctorNamesNodupFast_iff (l : List LeanEnumCtorSchema) :
    ctorNamesNodupFast l = true ↔ CtorNamesNodup l := by
  simp [ctorNamesNodupFast, nodupAux_eq_true_iff]

structure LeanEnumSchema where
  typeName            : String
  h_typeName_ne       : typeName != "" := by decide
  ctors               : List LeanEnumCtorSchema
  h_ctors_more_than_1 : ctors.length > 1 := by decide -- not a structure
  /-- Constructor names are pairwise distinct. This holds automatically for schemas
      extracted from real Lean inductive types (their constructor names are distinct
      by construction), and is checked by `decide` on the concrete schema literals
      produced by `lean_schema%`. It is what makes name-based lookup unambiguous. -/
  h_ctors_nodup       : CtorNamesNodup ctors := by decide
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- With pairwise distinct constructor names, searching a list for a constructor's own
    name returns exactly that constructor. -/
theorem find?_name_eq_self {ctors : List LeanEnumCtorSchema}
    (h_nodup : CtorNamesNodup ctors)
    {c : LeanEnumCtorSchema} (h_mem : c ∈ ctors) :
    ctors.find? (·.name == c.name) = some c := by
  induction ctors with
  | nil => cases h_mem
  | cons d ds ih =>
    obtain ⟨h_head, h_tail⟩ := ctorNamesNodup_cons_iff.mp h_nodup
    rcases List.mem_cons.mp h_mem with rfl | h_mem'
    · simp
    · have h_ne : (d.name == c.name) = false :=
        beq_eq_false_iff_ne.mpr (Ne.symm (h_head c h_mem'))
      simp [h_ne, ih h_tail h_mem']

namespace LeanEnumSchema

/-- Single unified lookup function for constructor schemas. -/
def findCtor? (schema : LeanEnumSchema) (ctorName : String) : Option LeanEnumCtorSchema :=
  schema.ctors.find? (·.name == ctorName)

/-- Returns the number of fields for a constructor, defaulting to 0 if not found. -/
def ctorNumFields (schema : LeanEnumSchema) (ctorName : String) : Nat :=
  schema.findCtor? ctorName |>.map (·.numFields) |>.getD 0

/-- Validates whether a constructor name belongs to the schema (returns Bool). -/
def hasCtor (schema : LeanEnumSchema) (ctorName : String) : Bool :=
  (schema.findCtor? ctorName).isSome

end LeanEnumSchema
