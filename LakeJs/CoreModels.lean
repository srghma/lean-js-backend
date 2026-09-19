/-!
# Lean-source models of the core functions the runtime implements in C

A handful of Lean's own total functions carry `@[extern]`, and Lean then stores **no**
LCNF body for them: the compiled module says "this one is a primitive of the runtime".
The front end has two ways to deal with such a function — treat it as a primitive, which
needs an entry in the catalogue of `LakeJs.Externs`, or compile the Lean definition it is
documented to be, which needs a body to read.

This module holds the bodies. Each definition here is the Lean function of the same
name, written out, with the termination proof Lean's own source gives it, so that the
front end can translate it exactly as it translates a function of the module it is
compiling: `LakeJs.Totality` classifies the recursion, and the `termination_by` measure
becomes the measure of the `Term.fix` it is translated into.

`LakeJs.FrontEnd.coreModelOf?` is the table that redirects a name to its model here. A
function reached that way is written into the generated program under **its own** Lean
name, since what is compiled is what that name means in Lean; the `@[extern]`
implementation is simply ignored.
-/

namespace LakeJs.CoreModels

/-- `Nat.gcd`, as the Lean function it is defined to be: the Euclidean algorithm,
    well-founded recursive on its first argument.

    `Nat.gcd` carries `@[extern "lean_nat_gcd"]`, so the compiled module has no body for
    it; this is the body, and it is what the front end compiles. -/
def natGcd (m n : Nat) : Nat :=
  if m = 0 then n
  else natGcd (n % m) m
termination_by m
decreasing_by exact Nat.mod_lt _ (Nat.zero_lt_of_ne_zero ‹_›)

/-- The model really is `Nat.gcd`: the `@[extern]` implementation is the only thing that
    is ignored, not the meaning of the name. -/
theorem natGcd_eq : ∀ (m n : Nat), natGcd m n = Nat.gcd m n
  | 0, n => by rw [natGcd.eq_def, Nat.gcd_def]; simp
  | m + 1, n => by
      rw [natGcd.eq_def, Nat.gcd_def]
      simp only [Nat.succ_ne_zero, if_false]
      exact natGcd_eq (n % (m + 1)) (m + 1)
termination_by m => m
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos m)

/-! ## Appending arrays

`Array.append` is a total function of Lean's library, but the body Lean stores for it is
not the loop it is *defined* to be: the compiler replaces it by a specialization of
`Array.foldlMUnsafe.fold`, an `unsafe` walk over `USize` with no termination measure.
These are the two definitions the source says `Array.append` is — push the elements of the
second array onto the first, from a given index on — well-founded on the number of
elements left, with a proof that the model really is `Array.append`. -/

/-- `Array.append`, from index `i` of `bs` on: the elements of `bs` from `i` on, pushed
    onto `as`.  Well-founded on the number of elements of `bs` that are left. -/
def arrayAppendFrom {α : Type u} (as bs : Array α) (i : Nat) : Array α :=
  if h : i < bs.size then arrayAppendFrom (as.push bs[i]) bs (i + 1) else as
termination_by bs.size - i

/-- `Array.append`: the elements of `bs`, pushed onto `as`. -/
def arrayAppend {α : Type u} (as bs : Array α) : Array α := arrayAppendFrom as bs 0

/-- What the loop computes: `as`, followed by the elements of `bs` from `i` on. -/
theorem arrayAppendFrom_toList {α : Type u} (as bs : Array α) (i : Nat) :
    (arrayAppendFrom as bs i).toList = as.toList ++ bs.toList.drop i := by
  rw [arrayAppendFrom]
  split
  · rename_i h
    have hd : bs.toList.drop i = bs[i] :: bs.toList.drop (i + 1) :=
      List.drop_eq_getElem_cons (by simpa using h)
    rw [arrayAppendFrom_toList (as.push bs[i]) bs (i + 1), Array.toList_push, hd]
    simp
  · rename_i h
    rw [List.drop_eq_nil_of_le (by simp at h ⊢; omega)]
    simp
termination_by bs.size - i

/-- The model really is `Array.append`. -/
theorem arrayAppend_eq {α : Type u} (as bs : Array α) :
    arrayAppend as bs = Array.append as bs := by
  apply Array.toList_inj.mp
  rw [arrayAppend, arrayAppendFrom_toList]
  simp

/-! ## Walking a string by byte position

A `String.Pos.Raw` is a one-field structure over `Nat`, so the type language holds a
position as the byte index it is. The three primitives a position walk uses are
implemented in C and typed, in the catalogue of `LakeJs.Externs`, at the runtime's own
position type; these models say what each of them is, in terms of primitives the
catalogue offers at a `Nat` position (`lean_string_decode_char`, `lean_string_push`,
`lean_string_utf8_byte_size`). -/

/-- `String.Pos.Raw.atEnd`: a position is at the end when it is no earlier than the last
    byte of the string. -/
def posAtEnd (s : String) (p : Nat) : Bool := decide (String.utf8ByteSize s ≤ p)

/-- `String.Pos.Raw.next`: the byte after the character that starts at `p`.  The width of
    that character is the size of the one-character string holding it — the catalogue has
    no `Char.utf8Size` of its own. -/
def posNext (s : String) (p : Nat) : Nat :=
  p + String.utf8ByteSize (String.push "" (String.Pos.Raw.get s ⟨p⟩))

/-- `instDecidableEqChar`: two characters are equal when the one-character strings that
    hold them are — the catalogue has no character comparison of its own, and the UTF-8
    encoding of a character determines it. -/
def charEq (a b : Char) : Bool := decide (String.push "" a = String.push "" b)

/-- `posAtEnd` really is `String.Pos.Raw.atEnd`. -/
theorem posAtEnd_eq (s : String) (p : Nat) : posAtEnd s p = String.Pos.Raw.atEnd s ⟨p⟩ := by
  simp [posAtEnd, String.Pos.Raw.atEnd]

/-- `posNext` really is `String.Pos.Raw.next`. -/
theorem posNext_eq (s : String) (p : Nat) :
    posNext s p = (String.Pos.Raw.next s ⟨p⟩).byteIdx := by
  simp [posNext, String.Pos.Raw.next]

/-- `charEq` really is character equality. -/
theorem charEq_eq (a b : Char) : charEq a b = decide (a = b) := by
  simp [charEq]

/-! ## Building a string from a list of characters

`String.ofList` carries `@[extern "lean_string_mk"]`, and the Lean definition behind it
builds the UTF-8 encoding of the whole list at once.  The model pushes the characters one
at a time, which is `lean_string_push` — a primitive the catalogue has. -/

/-- The characters of `cs`, pushed onto `acc` in order.  Structurally recursive on the
    list. -/
def stringOfListFrom (acc : String) : List Char → String
  | [] => acc
  | c :: cs => stringOfListFrom (acc.push c) cs

/-- What the loop builds: the characters of `acc`, then those of `cs`. -/
theorem stringOfListFrom_toList (acc : String) (cs : List Char) :
    (stringOfListFrom acc cs).toList = acc.toList ++ cs := by
  induction cs generalizing acc with
  | nil => simp [stringOfListFrom]
  | cons c cs ih => simp [stringOfListFrom, ih]

/-- `String.ofList`: the string whose characters are `cs`. -/
def stringOfList (cs : List Char) : String := stringOfListFrom "" cs

/-- The model really is `String.ofList`. -/
theorem stringOfList_eq (cs : List Char) : stringOfList cs = String.ofList cs :=
  String.ext (by simp [stringOfList, stringOfListFrom_toList])

/-! ## Reading an array, and a string, as a list of its elements

`Array.toList` and `String.toList` are `@[extern]` too, and what they answer with is a
list the language builds one element at a time. -/

/-- The elements of `xs` from index `i` on.  Well-founded on the number of elements
    left. -/
def arrayToListFrom {α : Type u} (xs : Array α) (i : Nat) : List α :=
  if h : i < xs.size then xs[i] :: arrayToListFrom xs (i + 1) else []
termination_by xs.size - i

/-- What the loop builds: the elements of `xs` from `i` on. -/
theorem arrayToListFrom_eq {α : Type u} (xs : Array α) (i : Nat) :
    arrayToListFrom xs i = xs.toList.drop i := by
  rw [arrayToListFrom]
  split
  · rename_i h
    rw [arrayToListFrom_eq xs (i + 1)]
    exact (List.drop_eq_getElem_cons (by simpa using h)).symm
  · rename_i h
    rw [List.drop_eq_nil_of_le (by simp at h ⊢; omega)]
termination_by xs.size - i

/-- `Array.toList`: the elements of `xs`, as a list. -/
def arrayToList {α : Type u} (xs : Array α) : List α := arrayToListFrom xs 0

/-- The model really is `Array.toList`. -/
theorem arrayToList_eq {α : Type u} (xs : Array α) : arrayToList xs = xs.toList := by
  simp [arrayToList, arrayToListFrom_eq]

end LakeJs.CoreModels
