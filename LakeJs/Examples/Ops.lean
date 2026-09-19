module

public import LakeJs.CertGen

@[expose] public section

set_option autoImplicit false

/-!
# Arithmetic, spelled once

The worked examples call the runtime's arithmetic through `Term.extern`, whose spines are
verbose to write out.  These abbreviations are the operations the examples use, each with
the equation that says what it evaluates to — every one of them `rfl`, since the evaluator
is an ordinary Lean function.

Nothing here is part of the language: `Term.callExtern` already is, and these are just
names for particular calls of it.
-/

namespace LakeJs.Expr.Ops

open LakeJs
open LakeJs.Ty

variable {Sg : Sig} {Γ : Ctx} {Ρ : RCtx}

/-! ## Any scalar function of the runtime, applied to its arguments

The named abbreviations below are the operations the worked examples use.  A translation
reaches for a great many more — every scalar row of the catalogue — and these four
combinators are how it applies one: the constructor of the catalogue says which function
it is and, through the type it is indexed by, what its arguments and its result are. -/

/-- A one-argument function of the runtime between terminal types. -/
def prim1Op {a b : LeanPrimTy} (e : LeanInitPureExtern1OnlyPrim a b)
    (x : Term Sg Γ Ρ (.prim a)) : Term Sg Γ Ρ (.prim b) :=
  Term.callExtern (.prim1 e) (.cons x .nil)

/-- A two-argument function of the runtime between terminal types. -/
def prim2Op {a b c : LeanPrimTy} (e : LeanInitPureExtern2OnlyPrim a b c)
    (x : Term Sg Γ Ρ (.prim a)) (y : Term Sg Γ Ρ (.prim b)) : Term Sg Γ Ρ (.prim c) :=
  Term.callExtern (.prim2 e) (.cons x (.cons y .nil))

/-- A three-argument function of the runtime between terminal types. -/
def prim3Op {a b c d : LeanPrimTy} (e : LeanInitPureExtern3OnlyPrim a b c d)
    (x : Term Sg Γ Ρ (.prim a)) (y : Term Sg Γ Ρ (.prim b)) (z : Term Sg Γ Ρ (.prim c)) :
    Term Sg Γ Ρ (.prim d) :=
  Term.callExtern (.prim3 e) (.cons x (.cons y (.cons z .nil)))

/-- A five-argument function of the runtime between terminal types. -/
def prim5Op {a b c d e f : LeanPrimTy} (op : LeanInitPureExtern5 a b c d e f)
    (x : Term Sg Γ Ρ (.prim a)) (y : Term Sg Γ Ρ (.prim b)) (z : Term Sg Γ Ρ (.prim c))
    (u : Term Sg Γ Ρ (.prim d)) (v : Term Sg Γ Ρ (.prim e)) : Term Sg Γ Ρ (.prim f) :=
  Term.callExtern (.prim5 op) (.cons x (.cons y (.cons z (.cons u (.cons v .nil)))))

/-- `a + b` on `Nat`. -/
def natAdd (a b : Term Sg Γ Ρ Ty.nat) : Term Sg Γ Ρ Ty.nat :=
  Term.callExtern (.prim2 .lean_nat_add) (.cons a (.cons b .nil))

/-- `a - b` on `Nat` (truncating, as Lean's). -/
def natSub (a b : Term Sg Γ Ρ Ty.nat) : Term Sg Γ Ρ Ty.nat :=
  Term.callExtern (.prim2 .lean_nat_sub) (.cons a (.cons b .nil))

/-- `a * b` on `Nat`. -/
def natMul (a b : Term Sg Γ Ρ Ty.nat) : Term Sg Γ Ρ Ty.nat :=
  Term.callExtern (.prim2 .lean_nat_mul) (.cons a (.cons b .nil))

/-- `a % b` on `Nat`. -/
def natMod (a b : Term Sg Γ Ρ Ty.nat) : Term Sg Γ Ρ Ty.nat :=
  Term.callExtern (.prim2 .lean_nat_mod) (.cons a (.cons b .nil))

/-- `a = b` on `Nat`. -/
def natEq (a b : Term Sg Γ Ρ Ty.nat) : Term Sg Γ Ρ Ty.bool :=
  Term.callExtern (.prim2 .lean_nat_dec_eq) (.cons a (.cons b .nil))

/-- `a ≤ b` on `Nat`. -/
def natLe (a b : Term Sg Γ Ρ Ty.nat) : Term Sg Γ Ρ Ty.bool :=
  Term.callExtern (.prim2 .lean_nat_dec_le) (.cons a (.cons b .nil))

/-- `a - b` on `Int`. -/
def intSub (a b : Term Sg Γ Ρ Ty.int) : Term Sg Γ Ρ Ty.int :=
  Term.callExtern (.prim2 .lean_int_sub) (.cons a (.cons b .nil))

/-- `a = b` on `Int`. -/
def intEq (a b : Term Sg Γ Ρ Ty.int) : Term Sg Γ Ρ Ty.bool :=
  Term.callExtern (.prim2 .lean_int_dec_eq) (.cons a (.cons b .nil))

/-- `a < b` on `Nat`. -/
def natLt (a b : Term Sg Γ Ρ Ty.nat) : Term Sg Γ Ρ Ty.bool :=
  Term.callExtern (.prim2 .lean_nat_dec_lt) (.cons a (.cons b .nil))

/-- `a * b` on `Int`. -/
def intMul (a b : Term Sg Γ Ρ Ty.int) : Term Sg Γ Ρ Ty.int :=
  Term.callExtern (.prim2 .lean_int_mul) (.cons a (.cons b .nil))

/-- `a < b` on `Int`. -/
def intLt (a b : Term Sg Γ Ρ Ty.int) : Term Sg Γ Ρ Ty.bool :=
  Term.callExtern (.prim2 .lean_int_dec_lt) (.cons a (.cons b .nil))

/-- `a + b` on `Int`. -/
def intAdd (a b : Term Sg Γ Ρ Ty.int) : Term Sg Γ Ρ Ty.int :=
  Term.callExtern (.prim2 .lean_int_add) (.cons a (.cons b .nil))

/-- `a ≤ b` on `Int`. -/
def intLe (a b : Term Sg Γ Ρ Ty.int) : Term Sg Γ Ρ Ty.bool :=
  Term.callExtern (.prim2 .lean_int_dec_le) (.cons a (.cons b .nil))

/-- `Int.ofNat a`: a `Nat` as an `Int`. -/
def natToInt (a : Term Sg Γ Ρ Ty.nat) : Term Sg Γ Ρ Ty.int :=
  Term.callExtern (.prim1 .lean_nat_to_int) (.cons a .nil)

/-- `a / b` on `Nat` (`0` when `b = 0`, as Lean's). -/
def natDiv (a b : Term Sg Γ Ρ Ty.nat) : Term Sg Γ Ρ Ty.nat :=
  Term.callExtern (.prim2 .lean_nat_div) (.cons a (.cons b .nil))

/-- `a ^ b` on `Nat`. -/
def natPow (a b : Term Sg Γ Ρ Ty.nat) : Term Sg Γ Ρ Ty.nat :=
  Term.callExtern (.prim2 .lean_nat_pow) (.cons a (.cons b .nil))

/-- `a <<< b` on `Nat`. -/
def natShiftLeft (a b : Term Sg Γ Ρ Ty.nat) : Term Sg Γ Ρ Ty.nat :=
  Term.callExtern (.prim2 .lean_nat_shiftl) (.cons a (.cons b .nil))

/-- `a >>> b` on `Nat`. -/
def natShiftRight (a b : Term Sg Γ Ρ Ty.nat) : Term Sg Γ Ρ Ty.nat :=
  Term.callExtern (.prim2 .lean_nat_shiftr) (.cons a (.cons b .nil))

/-- `a &&& b` on `Nat`. -/
def natLand (a b : Term Sg Γ Ρ Ty.nat) : Term Sg Γ Ρ Ty.nat :=
  Term.callExtern (.prim2 .lean_nat_land) (.cons a (.cons b .nil))

/-- `a ||| b` on `Nat`. -/
def natLor (a b : Term Sg Γ Ρ Ty.nat) : Term Sg Γ Ρ Ty.nat :=
  Term.callExtern (.prim2 .lean_nat_lor) (.cons a (.cons b .nil))

/-- `Nat.log2 a`. -/
def natLog2 (a : Term Sg Γ Ρ Ty.nat) : Term Sg Γ Ρ Ty.nat :=
  Term.callExtern (.prim1 .lean_nat_log2) (.cons a .nil)

/-- `s ++ t` on `String`. -/
def strAppend (s t : Term Sg Γ Ρ Ty.string) : Term Sg Γ Ρ Ty.string :=
  Term.callExtern (.prim2 .lean_string_append) (.cons s (.cons t .nil))

/-- `Int.toNat a`: the measure `Tco04` descends on. -/
def intToNat (a : Term Sg Γ Ρ Ty.int) : Term Sg Γ Ρ Ty.nat :=
  Term.callExtern (.prim1 .lean_int_to_nat) (.cons a .nil)

/-- `s.length`: the measure a string walk descends on. -/
def strLength (s : Term Sg Γ Ρ Ty.string) : Term Sg Γ Ρ Ty.nat :=
  Term.callExtern (.prim1 .lean_string_length) (.cons s .nil)

/-- `s.utf8ByteSize`: the number of bytes of the UTF-8 encoding of `s`. -/
def strUtf8ByteSize (s : Term Sg Γ Ρ Ty.string) : Term Sg Γ Ρ Ty.nat :=
  Term.callExtern (.prim1 .lean_string_utf8_byte_size) (.cons s .nil)

/-- `s.push c`. -/
def strPush (s : Term Sg Γ Ρ Ty.string) (c : Term Sg Γ Ρ Ty.char) :
    Term Sg Γ Ρ Ty.string :=
  Term.callExtern (.prim2 .lean_string_push) (.cons s (.cons c .nil))

/-- The character whose UTF-8 encoding starts at byte `p` of `s`: what
    `String.Pos.Raw.get` answers, at a position held as the byte index it is. -/
def strCharAt (s : Term Sg Γ Ρ Ty.string) (p : Term Sg Γ Ρ Ty.nat) :
    Term Sg Γ Ρ Ty.char :=
  Term.callExtern (.prim2 .lean_string_decode_char) (.cons s (.cons p .nil))

/-- `a = b` on `String`. -/
def strEq (a b : Term Sg Γ Ρ Ty.string) : Term Sg Γ Ρ Ty.bool :=
  Term.callExtern (.prim2 .lean_string_dec_eq) (.cons a (.cons b .nil))

/-- The substring of `s` between byte `b` and byte `e`. -/
def strExtract (s : Term Sg Γ Ρ Ty.string) (b e : Term Sg Γ Ρ Ty.nat) :
    Term Sg Γ Ρ Ty.string :=
  Term.callExtern (.prim3 .lean_string_utf8_extract) (.cons s (.cons b (.cons e .nil)))

/-- Are the `len` bytes of `s` from byte `p` the `len` bytes of `t` from byte `q`?  This
    is what `String.startsWith` and the other pattern primitives are built from. -/
def strMemcmp (s t : Term Sg Γ Ρ Ty.string) (p q len : Term Sg Γ Ρ Ty.nat) :
    Term Sg Γ Ρ Ty.bool :=
  Term.callExtern (.prim5 .lean_string_memcmp)
    (.cons s (.cons t (.cons p (.cons q (.cons len .nil)))))

/-- `xs.size`: the measure an array walk descends on. -/
def arrLen {α : Ty} (xs : Term Sg Γ Ρ (.array α)) : Term Sg Γ Ρ Ty.nat :=
  Term.callExtern (.poly1 (.lean_array_get_size α)) (.cons xs .nil)

/-- `xs[i]`, with the canonical inhabitant out of range. -/
def arrGet {α : Ty} (xs : Term Sg Γ Ρ (.array α)) (i : Term Sg Γ Ρ Ty.nat) :
    Term Sg Γ Ρ α :=
  Term.callExtern (.poly2 (.lean_array_get α)) (.cons xs (.cons i .nil))

/-- An empty array with room for `n` elements. -/
def arrEmpty {α : Ty} (n : Term Sg Γ Ρ Ty.nat) : Term Sg Γ Ρ (.array α) :=
  Term.callExtern (.poly1 (.lean_array_mk_empty α)) (.cons n .nil)

/-- `xs.push x`. -/
def arrPush {α : Ty} (xs : Term Sg Γ Ρ (.array α)) (x : Term Sg Γ Ρ α) :
    Term Sg Γ Ρ (.array α) :=
  Term.callExtern (.poly2 (.lean_array_push α)) (.cons xs (.cons x .nil))

/-- `Array.replicate n x`: the array of `n` copies of `x`. -/
def arrReplicate {α : Ty} (n : Term Sg Γ Ρ Ty.nat) (x : Term Sg Γ Ρ α) :
    Term Sg Γ Ρ (.array α) :=
  Term.callExtern (.poly2 (.lean_mk_array α)) (.cons n (.cons x .nil))

/-- `xs.set i x`, with `xs` unchanged when `i` is out of range. -/
def arrSet {α : Ty} (xs : Term Sg Γ Ρ (.array α)) (i : Term Sg Γ Ρ Ty.nat)
    (x : Term Sg Γ Ρ α) : Term Sg Γ Ρ (.array α) :=
  Term.callExtern (.poly3 (.lean_array_set α)) (.cons xs (.cons i (.cons x .nil)))

/-- `xs.swap i j`. -/
def arrSwap {α : Ty} (xs : Term Sg Γ Ρ (.array α)) (i j : Term Sg Γ Ρ Ty.nat) :
    Term Sg Γ Ρ (.array α) :=
  Term.callExtern (.poly3 (.lean_array_swap α)) (.cons xs (.cons i (.cons j .nil)))

/-- `xs.pop`. -/
def arrPop {α : Ty} (xs : Term Sg Γ Ρ (.array α)) : Term Sg Γ Ρ (.array α) :=
  Term.callExtern (.poly1 (.lean_array_pop α)) (.cons xs .nil)

section Equations

variable (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ)

@[simp] theorem eval_natAdd (a b : Term Sg Γ Ρ Ty.nat) :
    (natAdd a b).eval δ γ ρ = (show Nat from a.eval δ γ ρ) + (show Nat from b.eval δ γ ρ) := rfl

@[simp] theorem eval_natSub (a b : Term Sg Γ Ρ Ty.nat) :
    (natSub a b).eval δ γ ρ = (show Nat from a.eval δ γ ρ) - (show Nat from b.eval δ γ ρ) := rfl

@[simp] theorem eval_natMul (a b : Term Sg Γ Ρ Ty.nat) :
    (natMul a b).eval δ γ ρ = (show Nat from a.eval δ γ ρ) * (show Nat from b.eval δ γ ρ) := rfl

@[simp] theorem eval_natMod (a b : Term Sg Γ Ρ Ty.nat) :
    (natMod a b).eval δ γ ρ = (show Nat from a.eval δ γ ρ) % (show Nat from b.eval δ γ ρ) := rfl

@[simp] theorem eval_natEq (a b : Term Sg Γ Ρ Ty.nat) :
    (natEq a b).eval δ γ ρ = decide ((show Nat from a.eval δ γ ρ) = (show Nat from b.eval δ γ ρ)) := rfl

@[simp] theorem eval_natLe (a b : Term Sg Γ Ρ Ty.nat) :
    (natLe a b).eval δ γ ρ = decide ((show Nat from a.eval δ γ ρ) ≤ (show Nat from b.eval δ γ ρ)) := rfl

@[simp] theorem eval_intSub (a b : Term Sg Γ Ρ Ty.int) :
    (intSub a b).eval δ γ ρ = (show Int from a.eval δ γ ρ) - (show Int from b.eval δ γ ρ) := rfl

@[simp] theorem eval_intEq (a b : Term Sg Γ Ρ Ty.int) :
    (intEq a b).eval δ γ ρ = decide ((show Int from a.eval δ γ ρ) = (show Int from b.eval δ γ ρ)) := rfl

@[simp] theorem eval_intToNat (a : Term Sg Γ Ρ Ty.int) :
    (intToNat a).eval δ γ ρ = Int.toNat (a.eval δ γ ρ) := rfl

@[simp] theorem eval_natLt (a b : Term Sg Γ Ρ Ty.nat) :
    (natLt a b).eval δ γ ρ = decide ((show Nat from a.eval δ γ ρ) < (show Nat from b.eval δ γ ρ)) := rfl

@[simp] theorem eval_intMul (a b : Term Sg Γ Ρ Ty.int) :
    (intMul a b).eval δ γ ρ = (show Int from a.eval δ γ ρ) * (show Int from b.eval δ γ ρ) := rfl

@[simp] theorem eval_intLt (a b : Term Sg Γ Ρ Ty.int) :
    (intLt a b).eval δ γ ρ = decide ((show Int from a.eval δ γ ρ) < (show Int from b.eval δ γ ρ)) := rfl

@[simp] theorem eval_strLength (s : Term Sg Γ Ρ Ty.string) :
    (strLength s).eval δ γ ρ = String.length (s.eval δ γ ρ) := rfl

@[simp] theorem eval_strUtf8ByteSize (s : Term Sg Γ Ρ Ty.string) :
    (strUtf8ByteSize s).eval δ γ ρ = String.utf8ByteSize (s.eval δ γ ρ) := rfl

@[simp] theorem eval_strPush (s : Term Sg Γ Ρ Ty.string) (c : Term Sg Γ Ρ Ty.char) :
    (strPush s c).eval δ γ ρ = String.push (s.eval δ γ ρ) (c.eval δ γ ρ) := rfl

@[simp] theorem eval_strCharAt (s : Term Sg Γ Ρ Ty.string) (p : Term Sg Γ Ρ Ty.nat) :
    (strCharAt s p).eval δ γ ρ = String.Pos.Raw.get (s.eval δ γ ρ) ⟨p.eval δ γ ρ⟩ := rfl

@[simp] theorem eval_strEq (a b : Term Sg Γ Ρ Ty.string) :
    (strEq a b).eval δ γ ρ
      = decide ((show String from a.eval δ γ ρ) = (show String from b.eval δ γ ρ)) := rfl

@[simp] theorem eval_arrLen {α : Ty} (xs : Term Sg Γ Ρ (.array α)) :
    (arrLen xs).eval δ γ ρ = List.length (xs.eval δ γ ρ) := rfl

@[simp] theorem eval_arrGet {α : Ty} (xs : Term Sg Γ Ρ (.array α)) (i : Term Sg Γ Ρ Ty.nat) :
    (arrGet xs i).eval δ γ ρ
      = List.getD (xs.eval δ γ ρ) (i.eval δ γ ρ) α.dflt := rfl

@[simp] theorem eval_arrPush {α : Ty} (xs : Term Sg Γ Ρ (.array α)) (x : Term Sg Γ Ρ α) :
    (arrPush xs x).eval δ γ ρ = (xs.eval δ γ ρ) ++ [x.eval δ γ ρ] := rfl

end Equations

end LakeJs.Expr.Ops

end
