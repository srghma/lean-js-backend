module

public import LakeJs.Den
public import LakeJs.Externs
public import LakeJs.ExternEval1
public import LakeJs.ExternEval2
public import LakeJs.ExternEvalMisc

@[expose] public section

set_option autoImplicit false

/-!
# What an extern *means*

`LakeJs.Externs` is the catalogue of the pure `@[extern]` functions of Lean's `Init` that
the language can call; this module gives each of them a **total Lean function** of the
right type:

```
Extern.den : Extern σs τ → (Ty.arrows σs τ).den
```

`Term.extern e` evaluates to `e.den`, so the evaluator of `LakeJs.Reduce` never has to
stop in front of a runtime function, and never has to answer `none` when it meets one.

Three groups of entry need a word.

* **The terminal families** (`prim1`, `prim2`, `prim3`, `prim5`, `const`) already have
  their meaning written out in `LakeJs.ExternEval1`, `LakeJs.ExternEval2` and
  `LakeJs.ExternEvalMisc`; here they are only curried.
* **The polymorphic families** (`poly1` … `poly6`) are given their meaning here, on the
  denotations of `LakeJs.Den`: an array and a list are both a `List`, a task, a promise
  and a thunk hold the value they will answer with (the language is pure, and evaluation
  is eager), a `lazy` is a delay `Unit → …`, and an `Option` or a product is a runtime
  tree.
* **The entries that speak about the representation rather than the value** —
  `lean_ptr_addr`, `lean_is_exclusive_obj`, `lean_is_scalar`, `lean_sharecommon_quick`,
  `lean_dbg_trace` and friends — denote what they mean *for the value*: the address of a
  value is not part of its meaning, so `lean_ptr_addr` answers `0`, an object is never
  observed to be exclusive or scalar, hash-consing is the identity, and tracing runs its
  delayed argument and answers with it.
* **The two entries that fail** — `lean_sorry` and `lean_panic_fn_borrowed` — answer with
  the canonical inhabitant `Ty.dflt`.  The language has no failure, which is what keeps
  the evaluator a total function; a program that reaches one of them has an answer that
  means nothing, not an evaluation that gets stuck.
-/

namespace LakeJs

namespace ExternDen

/-- `none`, as a runtime tree: constructor `0` of `Ty.option`, which has no field. -/
def optNone : Data := .node 0 []

/-- `some v`, as a runtime tree: constructor `1` of `Ty.option`, whose one field is the
    value. -/
def optSome (α : Ty) (v : α.den) : Data := .node 1 [α.toData v]

/-- An `Option` as a value of `Ty.option`. -/
def optData (α : Ty) : Option α.den → (Ty.option α).den
  | none => optNone
  | some v => optSome α v

/-- A pair of scalars as a value of `LakeJs.primProd`: constructor `0` with two fields. -/
def pairData (a b : LeanPrimTy) (x : a.denote) (y : b.denote) : (primProd a b).den :=
  Data.node 0 [.leaf a x, .leaf b y]

/-- Advance a byte position past the characters a predicate accepts. -/
def nextWhileList (p : Char → Bool) : List Char → Nat → Nat → Nat
  | [], _, acc => acc
  | c :: cs, i, acc =>
      if i > 0 then nextWhileList p cs (i - c.utf8Size) (acc + c.utf8Size)
      else if p c then nextWhileList p cs 0 (acc + c.utf8Size)
      else acc

/-- `String.nextWhile`: the first byte position at or after `i` whose character the
    predicate rejects. -/
def strNextWhile (s : String) (p : Char → Bool) (i : Nat) : Nat :=
  nextWhileList p s.toList i i

/-- Index into a sequence, with the canonical inhabitant out of range. -/
def getD (α : Ty) (xs : List α.den) (i : Nat) : α.den := xs.getD i α.dflt

/-- Swap two elements of a sequence; an out-of-range index leaves it unchanged. -/
def swap (α : Ty) (xs : List α.den) (i j : Nat) : List α.den :=
  if i < xs.length ∧ j < xs.length then
    (xs.set i (getD α xs j)).set j (getD α xs i)
  else xs

end ExternDen

open ExternDen

/-- The meaning of a one-argument polymorphic extern. -/
def Extern.den1 : ∀ {α β : Ty}, Extern1At α β → (α.den → β.den)
  | _, _, (.lean_sorry α) => fun _ => α.dflt
  | _, _, (.lean_array_get_size α) => fun (xs : List α.den) => xs.length
  | _, _, (.lean_array_to_list α) => fun (xs : List α.den) => xs
  | _, _, (.lean_empty_array_with_capacity α) =>
      fun _ => show List α.den from []
  | _, _, (.lean_array_mk_empty α) => fun _ => show List α.den from []
  | _, _, (.lean_panic_fn_borrowed α) => fun _ => α.dflt
  | _, _, (.lean_array_mk α) => fun (xs : List α.den) => xs
  | _, _, (.lean_thunk_pure _) => fun v => v
  | _, _, (.lean_mk_thunk _) => fun f => f ()
  | _, _, (.lean_task_get_own _) => fun v => v
  | _, _, (.lean_task_pure _) => fun v => v
  | _, _, (.lean_thunk_get_own _) => fun v => v
  | _, _, (.lean_ptr_addr _) => fun _ => show UInt64 from 0
  | _, _, (.lean_dbg_stack_trace _) => fun f => f ()
  | _, _, (.lean_is_exclusive_obj _) => fun _ => show Bool from false
  | _, _, (.lean_array_pop α) => fun (xs : List α.den) => xs.dropLast
  | _, _, (.lean_array_size α) =>
      fun (xs : List α.den) => show UInt64 from UInt64.ofNat xs.length
  | _, _, (.lean_io_promise_result_opt α) => fun v => optData α (some v)
  | _, _, (.lean_option_get_or_block α) =>
      fun (d : Data) =>
        match d with
        | .node 1 (f :: _) => α.ofData f
        | _ => α.dflt
  | _, _, (.lean_sharecommon_quick _) => fun v => v
  | _, _, .lean_string_mk => fun (cs : List Char) => String.ofList cs
  | _, _, .lean_string_mk_def => fun (cs : List Char) => String.ofList cs
  | _, _, .lean_string_data => fun (s : String) => s.toList
  | _, _, .lean_string_to_list => fun (s : String) => s.toList
  | _, _, .lean_float_frexp =>
      fun (x : Float) => pairData .float .int64 x.frExp.1 (Int64.ofInt x.frExp.2)
  | _, _, .lean_float32_frexp =>
      fun (x : Float32) =>
        pairData .float32 .int64 x.frExp.1 (Int64.ofInt x.frExp.2)
  | _, _, (.lean_is_scalar _) => fun _ => show Bool from false
  -- the two-argument polymorphic family


/-- The meaning of a two-argument polymorphic extern. -/
def Extern.den2 : ∀ {α β γ : Ty}, Extern2At α β γ → (α.den → β.den → γ.den)
  | _, _, _, (.lean_array_get_borrowed α) =>
      fun (xs : List α.den) (i : Nat) => getD α xs i
  | _, _, _, (.lean_array_push α) => fun (xs : List α.den) x => xs ++ [x]
  | _, _, _, (.lean_array_fget_borrowed α) =>
      fun (xs : List α.den) (i : Nat) => getD α xs i
  | _, _, _, (.lean_array_get α) => fun (xs : List α.den) (i : Nat) => getD α xs i
  | _, _, _, (.lean_array_fget α) => fun (xs : List α.den) (i : Nat) => getD α xs i
  | _, _, _, (.lean_task_spawn _) => fun f (_ : Nat) => f ()
  | _, _, _, (.lean_dbg_sleep _) => fun (_ : UInt32) f => f ()
  | _, _, _, (.lean_dbg_trace _) => fun (_ : String) f => f ()
  | _, _, _, (.lean_dbg_trace_if_shared _) => fun (_ : String) v => v
  | _, _, _, (.lean_array_uget α) =>
      fun (xs : List α.den) (i : UInt64) => getD α xs i.toNat
  | _, _, _, (.lean_mk_array α) =>
      fun (n : Nat) (x : α.den) => List.replicate n x
  | _, _, _, .lean_substring_takewhile =>
      fun (s : Substring.Raw) (p : Char → Bool) => s.takeWhile p
  | _, _, _, .lean_substring_all =>
      fun (s : Substring.Raw) (p : Char → Bool) => s.all p
  | _, _, _, .lean_string_intercalate =>
      fun (sep : String) (parts : List String) => String.intercalate sep parts
  | _, _, _, .lean_string_any =>
      fun (s : String) (p : Char → Bool) => s.toList.any p
  | _, _, _, .lean_string_pos_raw_get_opt =>
      fun (s : String) (i : Nat) => optData (.prim .char) (String.Pos.Raw.get? s ⟨i⟩)
  | _, _, _, .lean_string_get_opt =>
      fun (s : String) (i : Nat) => optData (.prim .char) (String.Pos.Raw.get? s ⟨i⟩)
  | _, _, _, (.lean_array_uget_borrowed α) =>
      fun (xs : List α.den) (i : UInt64) => getD α xs i.toNat
  -- the three-argument polymorphic family


/-- The meaning of a three-argument polymorphic extern. -/
def Extern.den3 : ∀ {α β γ δ : Ty}, Extern3At α β γ δ → (α.den → β.den → γ.den → δ.den)
  | _, _, _, _, (.lean_array_set α) =>
      fun (xs : List α.den) (i : Nat) (x : α.den) => xs.set i x
  | _, _, _, _, (.lean_array_fset α) =>
      fun (xs : List α.den) (i : Nat) (x : α.den) => xs.set i x
  | _, _, _, _, (.lean_array_fswap α) =>
      fun (xs : List α.den) (i j : Nat) => swap α xs i j
  | _, _, _, _, (.lean_array_swap α) =>
      fun (xs : List α.den) (i j : Nat) => swap α xs i j
  | _, _, _, _, (.lean_array_uset α) =>
      fun (xs : List α.den) (i : UInt64) (x : α.den) => xs.set i.toNat x
  | _, _, _, _, .lean_string_foldl =>
      fun (f : String → Char → String) (init : String) (s : String) =>
        s.toList.foldl f init
  | _, _, _, _, .lean_string_nextwhile =>
      fun (s : String) (p : Char → Bool) (i : Nat) => strNextWhile s p i
  | _, _, _, _, .lean_byte_array_set =>
      fun (xs : List UInt8) (i : Nat) (x : UInt8) => xs.set i x
  | _, _, _, _, .lean_byte_array_uset =>
      fun (xs : List UInt8) (i : UInt64) (x : UInt8) => xs.set i.toNat x
  | _, _, _, _, .lean_byte_array_fset =>
      fun (xs : List UInt8) (i : Nat) (x : UInt8) => xs.set i x
  | _, _, _, _, .lean_float_array_fset =>
      fun (xs : List Float) (i : Nat) (x : Float) => xs.set i x
  | _, _, _, _, .lean_float_array_uset =>
      fun (xs : List Float) (i : UInt64) (x : Float) => xs.set i.toNat x
  | _, _, _, _, .lean_float_array_set =>
      fun (xs : List Float) (i : Nat) (x : Float) => xs.set i x
  -- the four-argument polymorphic family: a task holds its value, so mapping one is
  -- applying the function and binding one is applying the continuation


/-- The meaning of a four-argument polymorphic extern. -/
def Extern.den4 : ∀ {α β γ δ ε : Ty}, Extern4At α β γ δ ε → (α.den → β.den → γ.den → δ.den → ε.den)
  | _, _, _, _, _, (.lean_task_map _ _) =>
      fun f v (_ : Nat) (_ : Bool) => f v
  | _, _, _, _, _, (.lean_task_bind _ _) =>
      fun v f (_ : Nat) (_ : Bool) => f v
  -- the six-argument polymorphic family


/-- The meaning of the six-argument polymorphic extern. -/
def Extern.den6 : ∀ {α : Ty} {b : LeanPrimTy} {γ : Ty} {d e f : LeanPrimTy} {ζ : Ty}, Extern6At α b γ d e f ζ → (α.den → b.denote → γ.den → d.denote → e.denote → f.denote → ζ.den)
  | _, _, _, _, _, _, _, .lean_byte_array_copy_slice =>
      fun (src : List UInt8) (srcOff : Nat) (dest : List UInt8) (destOff : Nat)
          (len : Nat) (exact : Bool) =>
        let chunk := (src.drop srcOff).take len
        let chunk := if exact then chunk.take len else chunk
        (dest.take destOff) ++ chunk ++ (dest.drop (destOff + chunk.length))

/-- The **meaning of an extern**: the curried total Lean function it denotes. -/
def Extern.den : ∀ {σs : List Ty} {τ : Ty}, Extern σs τ → (Ty.arrows σs τ).den
  | _, _, .const e => fun _ => e.eval
  | _, _, .prim1 e => fun x => e.eval x
  | _, _, .prim2 e => fun x y => e.eval x y
  | _, _, .prim3 e => fun x y z => e.eval x y z
  | _, _, .prim5 e => fun x y z u v => e.eval x y z u v
  | _, _, .poly1 e => Extern.den1 e
  | _, _, .poly2 e => Extern.den2 e
  | _, _, .poly3 e => Extern.den3 e
  | _, _, .poly4 e => Extern.den4 e
  | _, _, .poly6 e => Extern.den6 e

end LakeJs

end
