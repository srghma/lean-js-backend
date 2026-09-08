import LakeJs.Js

-- ============
-- Init.Prelude
-- ============

-- ```lean
-- unsafe axiom isScalarObj {α : Type u} (x : α) : Bool
-- ```
--
-- ```cpp
-- static inline LEAN_ALWAYS_INLINE uint8_t lean_is_scalar(lean_object * o) { return ((size_t)(o) & 1) == 1; }
-- ```
def lean_is_scalar := [JS_EXPR|throw new Error("lean_is_scalar is not and should not be implemented")]

-- ```lean
-- axiom sorryAx (α : Sort u) (synthetic : Bool) : α
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT object * lean_sorry(uint8) {
--     lean_internal_panic("executed 'sorry'");
--     lean_unreachable();
-- }
-- ```
def lean_sorry := [JS_EXPR|throw new Error("lean_sorry is not and should not be implemented")]

-- ```lean
-- protected def Nat.add : (@& Nat) → (@& Nat) → Nat
--   | a, Nat.zero   => a
--   | a, Nat.succ b => Nat.succ (Nat.add a b)
-- ```
--
-- ```cpp
-- static inline LEAN_ALWAYS_INLINE lean_obj_res lean_nat_add(b_lean_obj_arg a1, b_lean_obj_arg a2) {
--     if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2)))
--         return lean_usize_to_nat(lean_unbox(a1) + lean_unbox(a2));
--     else
--         return lean_nat_big_add(a1, a2);
-- }
-- ```
def lean_nat_add := [JS_EXPR|#0 + #1]

-- ```lean
-- protected def Nat.mul : (@& Nat) → (@& Nat) → Nat
--   | _, 0          => 0
--   | a, Nat.succ b => Nat.add (Nat.mul a b) a
-- ```
--
-- ```cpp
-- static inline LEAN_ALWAYS_INLINE lean_obj_res lean_nat_mul(b_lean_obj_arg a1, b_lean_obj_arg a2) {
--     if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
--         size_t n1 = lean_unbox(a1);
--         if (n1 == 0)
--             return a1;
--         size_t n2 = lean_unbox(a2);
--         size_t r  = n1*n2;
--         if (r <= LEAN_MAX_SMALL_NAT && r / n1 == n2)
--             return lean_box(r);
--         else
--             return lean_nat_overflow_mul(n1, n2);
--     } else {
--         return lean_nat_big_mul(a1, a2);
--     }
-- }
-- ```
def lean_nat_mul := [JS_EXPR|#0 * #1]

-- ```lean
-- protected def Nat.pow (m : @& Nat) : (@& Nat) → Nat
--   | 0      => 1
--   | succ n => Nat.mul (Nat.pow m n) m
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT lean_obj_res lean_nat_pow(b_lean_obj_arg a1, b_lean_obj_arg a2) {
--     if (!lean_is_scalar(a2) || lean_unbox(a2) > UINT_MAX) {
--         lean_internal_panic("Nat.pow exponent is too big");
--     }
--     if (lean_is_scalar(a1))
--         return mpz_to_nat(mpz::of_size_t(lean_unbox(a1)).pow(lean_unbox(a2)));
--     else
--         return mpz_to_nat(mpz_value(a1).pow(lean_unbox(a2)));
-- }
-- ```
def lean_nat_pow := [JS_EXPR|#0 ^ #1]

-- ```lean
-- def Nat.beq : (@& Nat) → (@& Nat) → Bool
--   | zero,   zero   => true
--   | zero,   succ _ => false
--   | succ _, zero   => false
--   | succ n, succ m => beq n m
-- ```
--
-- ```cpp
-- static inline LEAN_ALWAYS_INLINE uint8_t lean_nat_dec_eq(b_lean_obj_arg a1, b_lean_obj_arg a2) {
--     return lean_nat_eq(a1, a2);
-- }
-- ```
--
-- ```lean
-- protected def Nat.decEq (n m : @& Nat) : Decidable (Eq n m) where
--   decide := beq n m
--   reflects_decide :=
--     match h : beq n m with
--     | true  => eq_of_beq_eq_true h
--     | false => ne_of_beq_eq_false h
-- ```
--
-- ```cpp
-- static inline LEAN_ALWAYS_INLINE uint8_t lean_nat_dec_eq(b_lean_obj_arg a1, b_lean_obj_arg a2) {
--     return lean_nat_eq(a1, a2);
-- }
-- ```
def lean_nat_dec_eq := [JS_EXPR|#0 == #1]

-- ```lean
-- def Nat.ble : @& Nat → @& Nat → Bool
--   | zero,   _      => true
--   | succ _, zero   => false
--   | succ n, succ m => ble n m
-- ```
--
-- ```cpp
-- static inline LEAN_ALWAYS_INLINE uint8_t lean_nat_dec_le(b_lean_obj_arg a1, b_lean_obj_arg a2) {
--     return lean_nat_le(a1, a2);
-- }
-- ```
--
-- ```lean
-- instance Nat.decLe (n m : @& Nat) : Decidable (LE.le n m) where
--   decide := ble n m
--   reflects_decide :=
--     match h : ble n m with
--     | true => Nat.le_of_ble_eq_true h
--     | false => Nat.not_le_of_not_ble_eq_true (fun h' => Bool.noConfusion (h' ▸ h :))
-- ```
--
-- ```cpp
-- static inline LEAN_ALWAYS_INLINE uint8_t lean_nat_dec_le(b_lean_obj_arg a1, b_lean_obj_arg a2) {
--     return lean_nat_le(a1, a2);
-- }
-- ```
def lean_nat_dec_le := [JS_EXPR|#0 <= #1]

-- ```lean
-- def Nat.pred : (@& Nat) → Nat
--   | 0      => 0
--   | succ a => a
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_nat_pred(b_lean_obj_arg n) {
--     return lean_nat_sub(n, lean_box(1));
-- }
-- ```
def lean_nat_pred := [JS_EXPR|(#0 > 0) ? (#0 - 1) : 0]

-- ```lean
-- instance Nat.decLt (n m : @& Nat) : Decidable (LT.lt n m) :=
--   decLe (succ n) m
-- ```
--
-- ```cpp
-- static inline LEAN_ALWAYS_INLINE uint8_t lean_nat_dec_lt(b_lean_obj_arg a1, b_lean_obj_arg a2) {
--     return lean_nat_lt(a1, a2);
-- }
-- ```
def lean_nat_dec_lt := [JS_EXPR|#0 < #1]

-- ```lean
-- protected def Nat.sub : (@& Nat) → (@& Nat) → Nat
--   | a, 0      => a
--   | a, succ b => pred (Nat.sub a b)
-- ```
--
-- ```cpp
-- static inline LEAN_ALWAYS_INLINE lean_obj_res lean_nat_sub(b_lean_obj_arg a1, b_lean_obj_arg a2) {
--     if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
--         size_t n1 = lean_unbox(a1);
--         size_t n2 = lean_unbox(a2);
--         if (n1 < n2)
--             return lean_box(0);
--         else
--             return lean_box(n1 - n2);
--     } else {
--         return lean_nat_big_sub(a1, a2);
--     }
-- }
-- ```
def lean_nat_sub := [JS_EXPR|(#0 > #1) ? (#0 - #1) : 0]

-- ```lean
-- protected def Nat.div (x y : @& Nat) : Nat :=
--   dite (LT.lt 0 y) (fun hy =>
--     let rec
--       go (fuel : Nat) (x : Nat) (hfuel : LT.lt x fuel) : Nat :=
--       match fuel with
--       | succ fuel =>
--         dite (LE.le y x)
--           (fun h => HAdd.hAdd (go fuel (HSub.hSub x y) (div_rec_fuel_lemma hy h hfuel)) 1)
--           (fun _ => 0)
--       termination_by structural fuel
--     go (succ x) x (Nat.lt_succ_self _))
--     (fun _ => 0)
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_nat_div(b_lean_obj_arg a1, b_lean_obj_arg a2) {
--     if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
--         size_t n1 = lean_unbox(a1);
--         size_t n2 = lean_unbox(a2);
--         if (n2 == 0)
--             return lean_box(0);
--         else
--             return lean_box(n1 / n2);
--     } else {
--         return lean_nat_big_div(a1, a2);
--     }
-- }
-- ```
def lean_nat_div := [JS_EXPR|(#1 > 0) ? (#0 / #1) : 0]

-- ```lean
-- protected noncomputable def Nat.modCore (x y : Nat) : Nat :=
--   dite (LT.lt 0 y)
--     (fun hy =>
--       let rec
--         go (fuel : Nat) (x : Nat) (hfuel : LT.lt x fuel) : Nat :=
--         match fuel with
--         | succ fuel =>
--           dite (LE.le y x)
--             (fun h => go fuel (HSub.hSub x y) (div_rec_fuel_lemma hy h hfuel))
--             (fun _ => x)
--         termination_by structural fuel
--       go (succ x) x (Nat.lt_succ_self _))
--     (fun _ => x)
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_nat_mod(b_lean_obj_arg a1, b_lean_obj_arg a2) {
--     if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
--         size_t n1 = lean_unbox(a1);
--         size_t n2 = lean_unbox(a2);
--         if (n2 == 0)
--             return lean_box(n1);
--         else
--             return lean_box(n1 % n2);
--     } else {
--         return lean_nat_big_mod(a1, a2);
--     }
-- }
-- ```
--
-- ```lean
-- protected def Nat.mod : @& Nat → @& Nat → Nat
--   /-
--   Nat.modCore is defined with fuel and thus does not reduce with open terms very well.
--   Nevertheless it is desirable for trivial `Nat.mod` calculations, namely
--   * `Nat.mod 0 m` for all `m`
--   * `Nat.mod n (m + n + 1)` for concrete literals `n`,
--   to reduce definitionally.
--   This property is desirable for `Fin n` literals, as it means `(ofNat 0 : Fin n).val = 0` by
--   definition.
--    -/
--   | 0, _ => 0
--   | n@(succ _), m => ite (LE.le m n) (Nat.modCore n m) n
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_nat_mod(b_lean_obj_arg a1, b_lean_obj_arg a2) {
--     if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
--         size_t n1 = lean_unbox(a1);
--         size_t n2 = lean_unbox(a2);
--         if (n2 == 0)
--             return lean_box(n1);
--         else
--             return lean_box(n1 % n2);
--     } else {
--         return lean_nat_big_mod(a1, a2);
--     }
-- }
-- ```
def lean_nat_mod := [JS_EXPR|(#1 > 0) ? (#0 % #1) : 0]

-- ```lean
-- opaque System.Platform.getNumBits : Unit → Subtype fun (n : Nat) => Or (Eq n 32) (Eq n 64) :=
--   fun _ => ⟨64, Or.inr rfl⟩ -- inhabitant
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_system_platform_nbits(obj_arg) {
--     if (sizeof(void*) == 8) {
--         return box(64);
--     } else {
--         return box(32);
--     }
-- }
-- ```
def lean_system_platform_nbits := [JS_EXPR|64]

-- ```lean
-- attribute [extern "lean_uint8_of_nat_mk"] UInt8.ofBitVec
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint8_of_nat_mk(lean_obj_arg a) { uint8_t r = lean_uint8_of_nat(a); lean_dec(a); return r; }
-- ```
def lean_uint8_of_nat_mk := [JS_EXPR|throw new Error("lean_uint8_of_nat_mk is not implemented")]

-- ```lean
-- attribute [extern "lean_uint8_to_nat"] UInt8.toBitVec
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_uint8_to_nat(uint8_t a) { return lean_usize_to_nat((size_t)a); }
-- ```
def lean_uint8_to_nat := [JS_EXPR|#0]

-- ```lean
-- def UInt8.ofNatLT (n : @& Nat) (h : LT.lt n UInt8.size) : UInt8 where
--   toBitVec := BitVec.ofNatLT n h
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint8_of_nat(b_lean_obj_arg a) { return lean_is_scalar(a) ? (uint8_t)(lean_unbox(a)) : lean_uint8_of_big_nat(a); }
-- ```
--
-- ```lean
-- def UInt8.ofNat (n : @& Nat) : UInt8 := ⟨BitVec.ofNat 8 n⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint8_of_nat(b_lean_obj_arg a) { return lean_is_scalar(a) ? (uint8_t)(lean_unbox(a)) : lean_uint8_of_big_nat(a); }
-- ```
def lean_uint8_of_nat := [JS_EXPR|#0 & 0xFF]

-- ```lean
-- def UInt8.decEq (a b : UInt8) : Decidable (Eq a b) where
--   decide := decide (Eq a.toBitVec b.toBitVec)
--   reflects_decide :=
--     match instDecidableEqBitVec a.toBitVec b.toBitVec with
--     | isTrue  h => congrArg UInt8.ofBitVec h
--     | isFalse h => fun h' => UInt8.noConfusion h' h
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint8_dec_eq(uint8_t a1, uint8_t a2) { return a1 == a2; }
-- ```
def lean_uint8_dec_eq := [JS_EXPR|#0 == #1]

-- ```lean
-- def UInt8.decLt (a b : UInt8) : Decidable (LT.lt a b) :=
--   inferInstanceAs (Decidable (LT.lt a.toBitVec b.toBitVec))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint8_dec_lt(uint8_t a1, uint8_t a2) { return a1 < a2; }
-- ```
def lean_uint8_dec_lt := [JS_EXPR|#0 < #1]

-- ```lean
-- def UInt8.decLe (a b : UInt8) : Decidable (LE.le a b) :=
--   inferInstanceAs (Decidable (LE.le a.toBitVec b.toBitVec))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint8_dec_le(uint8_t a1, uint8_t a2) { return a1 <= a2; }
-- ```
def lean_uint8_dec_le := [JS_EXPR|#0 <= #1]

-- ```lean
-- attribute [extern "lean_uint16_of_nat_mk"] UInt16.ofBitVec
-- ```
--
-- ```cpp
-- static inline uint16_t lean_uint16_of_nat_mk(lean_obj_arg a) { uint16_t r = lean_uint16_of_nat(a); lean_dec(a); return r; }
-- ```
def lean_uint16_of_nat_mk := [JS_EXPR|throw new Error("lean_uint16_of_nat_mk is not implemented")]

-- ```lean
-- attribute [extern "lean_uint16_to_nat"] UInt16.toBitVec
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_uint16_to_nat(uint16_t a) { return lean_usize_to_nat((size_t)a); }
-- ```
def lean_uint16_to_nat := [JS_EXPR|#0]

-- ```lean
-- def UInt16.ofNatLT (n : @& Nat) (h : LT.lt n UInt16.size) : UInt16 where
--   toBitVec := BitVec.ofNatLT n h
-- ```
--
-- ```cpp
-- static inline uint16_t lean_uint16_of_nat(b_lean_obj_arg a) { return lean_is_scalar(a) ? (int16_t)(lean_unbox(a)) : lean_uint16_of_big_nat(a); }
-- ```
def lean_uint16_of_nat := [JS_EXPR|#0 & 0xFFFF]

-- ```lean
-- def UInt16.decEq (a b : UInt16) : Decidable (Eq a b) where
--   decide := decide (Eq a.toBitVec b.toBitVec)
--   reflects_decide :=
--     match instDecidableEqBitVec a.toBitVec b.toBitVec with
--     | isTrue  h => congrArg UInt16.ofBitVec h
--     | isFalse h => fun h' => UInt16.noConfusion h' h
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint16_dec_eq(uint16_t a1, uint16_t a2) { return a1 == a2; }
-- ```
def lean_uint16_dec_eq := [JS_EXPR|#0 == #1]

-- ```lean
-- attribute [extern "lean_uint32_of_nat_mk"] UInt32.ofBitVec
-- ```
--
-- ```cpp
-- static inline uint32_t lean_uint32_of_nat_mk(lean_obj_arg a) { uint32_t r = lean_uint32_of_nat(a); lean_dec(a); return r; }
-- ```
def lean_uint32_of_nat_mk := [JS_EXPR|throw new Error("lean_uint32_of_nat_mk is not implemented")]

-- ```lean
-- attribute [extern "lean_uint32_to_nat"] UInt32.toBitVec
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_uint32_to_nat(uint32_t a) { return lean_usize_to_nat((size_t)a); }
-- ```
--
-- ```lean
-- def UInt32.toNat (n : UInt32) : Nat := n.toBitVec.toNat
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_uint32_to_nat(uint32_t a) { return lean_usize_to_nat((size_t)a); }
-- ```
def lean_uint32_to_nat := [JS_EXPR|#0 >>> 0]

-- ```lean
-- def UInt32.ofNatLT (n : @& Nat) (h : LT.lt n UInt32.size) : UInt32 where
--   toBitVec := BitVec.ofNatLT n h
-- ```
--
-- ```cpp
-- static inline uint32_t lean_uint32_of_nat(b_lean_obj_arg a) { return lean_is_scalar(a) ? (uint32_t)(lean_unbox(a)) : lean_uint32_of_big_nat(a); }
-- ```
--
-- ```lean
-- def Char.ofNatAux (n : @& Nat) (h : n.isValidChar) : Char where
--   val := ⟨BitVec.ofNatLT n
--     -- We would conventionally use `by exact` here to enter a private context, but `exact` does not
--     -- exist here yet.
--     (private_decl% isValidChar_UInt32 h)⟩
--   valid := h
-- ```
--
-- ```cpp
-- static inline uint32_t lean_uint32_of_nat(b_lean_obj_arg a) { return lean_is_scalar(a) ? (uint32_t)(lean_unbox(a)) : lean_uint32_of_big_nat(a); }
-- ```
def lean_uint32_of_nat := [JS_EXPR|#0 >> 0]

-- ```lean
-- def UInt32.decEq (a b : UInt32) : Decidable (Eq a b) where
--   decide := decide (Eq a.toBitVec b.toBitVec)
--   reflects_decide :=
--     match instDecidableEqBitVec a.toBitVec b.toBitVec with
--     | isTrue  h => congrArg UInt32.ofBitVec h
--     | isFalse h => fun h' => UInt32.noConfusion h' h
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint32_dec_eq(uint32_t a1, uint32_t a2) { return a1 == a2; }
-- ```
def lean_uint32_dec_eq := [JS_EXPR|#0 == #1]

-- ```lean
-- def UInt32.decLt (a b : UInt32) : Decidable (LT.lt a b) :=
--   inferInstanceAs (Decidable (LT.lt a.toBitVec b.toBitVec))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint32_dec_lt(uint32_t a1, uint32_t a2) { return a1 < a2; }
-- ```
def lean_uint32_dec_lt := [JS_EXPR|#0 < #1]

-- ```lean
-- def UInt32.decLe (a b : UInt32) : Decidable (LE.le a b) :=
--   inferInstanceAs (Decidable (LE.le a.toBitVec b.toBitVec))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint32_dec_le(uint32_t a1, uint32_t a2) { return a1 <= a2; }
-- ```
def lean_uint32_dec_le := [JS_EXPR|#0 <= #1]

-- ```lean
-- attribute [extern "lean_uint64_of_nat_mk"] UInt64.ofBitVec
-- ```
--
-- ```cpp
-- static inline uint64_t lean_uint64_of_nat_mk(lean_obj_arg a) { uint64_t r = lean_uint64_of_nat(a); lean_dec(a); return r; }
-- ```
def lean_uint64_of_nat_mk := [JS_EXPR|throw new Error("lean_uint64_of_nat_mk is not implemented")]

-- ```lean
-- attribute [extern "lean_uint64_to_nat"] UInt64.toBitVec
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_uint64_to_nat(uint64_t n) {
--     if (LEAN_LIKELY(n <= LEAN_MAX_SMALL_NAT))
--         return lean_box(n);
--     else
--         return lean_big_uint64_to_nat(n);
-- }
-- ```
def lean_uint64_to_nat := [JS_EXPR|#0]

-- ```lean
-- def UInt64.ofNatLT (n : @& Nat) (h : LT.lt n UInt64.size) : UInt64 where
--   toBitVec := BitVec.ofNatLT n h
-- ```
--
-- ```cpp
-- static inline uint64_t lean_uint64_of_nat(b_lean_obj_arg a) { return lean_is_scalar(a) ? (uint64_t)(lean_unbox(a)) : lean_uint64_of_big_nat(a); }
-- ```
def lean_uint64_of_nat := [JS_EXPR|BigInt(#0) & 0xFFFFFFFFFFFFFFFF]

-- ```lean
-- def UInt64.decEq (a b : UInt64) : Decidable (Eq a b) where
--   decide := decide (Eq a.toBitVec b.toBitVec)
--   reflects_decide :=
--     match instDecidableEqBitVec a.toBitVec b.toBitVec with
--     | isTrue  h => congrArg UInt64.ofBitVec h
--     | isFalse h => fun h' => UInt64.noConfusion h' h
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint64_dec_eq(uint64_t a1, uint64_t a2) { return a1 == a2; }
-- ```
def lean_uint64_dec_eq := [JS_EXPR|#0 == #1]

-- ```lean
-- attribute [extern "lean_usize_of_nat_mk"] USize.ofBitVec
-- ```
--
-- ```cpp
-- static inline size_t lean_usize_of_nat_mk(lean_obj_arg a) { size_t r = lean_usize_of_nat(a); lean_dec(a); return r; }
-- ```
def lean_usize_of_nat_mk := [JS_EXPR|throw new Error("lean_usize_of_nat_mk is not implemented")]

-- ```lean
-- attribute [extern "lean_usize_to_nat"] USize.toBitVec
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_usize_to_nat(size_t n) {
--     if (LEAN_LIKELY(n <= LEAN_MAX_SMALL_NAT))
--         return lean_box(n);
--     else
--         return lean_big_usize_to_nat(n);
-- }
-- ```
def lean_usize_to_nat := [JS_EXPR|toUSize(#0)]

-- ```lean
-- def USize.ofNatLT (n : @& Nat) (h : LT.lt n USize.size) : USize where
--   toBitVec := BitVec.ofNatLT n h
-- ```
--
-- ```cpp
-- static inline size_t lean_usize_of_nat(b_lean_obj_arg a) { return lean_is_scalar(a) ? lean_unbox(a) : lean_usize_of_big_nat(a); }
-- ```
def lean_usize_of_nat := [JS_EXPR|toUSize(#0)]

-- ```lean
-- def USize.decEq (a b : USize) : Decidable (Eq a b) where
--   decide := decide (Eq a.toBitVec b.toBitVec)
--   reflects_decide :=
--     match instDecidableEqBitVec a.toBitVec b.toBitVec with
--     | isTrue  h => congrArg USize.ofBitVec h
--     | isFalse h => fun h' => USize.noConfusion h' h
-- ```
--
-- ```cpp
-- static inline uint8_t lean_usize_dec_eq(size_t a1, size_t a2) { return a1 == a2; }
-- ```
def lean_usize_dec_eq := [JS_EXPR|#0 == #1]

-- ```lean
-- attribute [extern "lean_array_to_list"] Array.toList
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT lean_object * lean_array_to_list(lean_obj_arg a) {
--     return lean_array_to_list_impl(lean_box(0), a);
-- }
-- ```
def lean_array_to_list := [JS_EXPR|(#0).reduceRight((out, item) => mkObject(`List.cons, item, out), mkObject(`List.nil))]

-- ```lean
-- attribute [extern "lean_array_mk"] Array.mk
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT object * lean_array_mk(lean_obj_arg lst) {
--     return lean_list_to_array(lean_box(0), lst);
-- }
-- ```
def lean_array_mk := [JS_FUNC|inputs(curr)|returns=out|
  const out = [];
  while (isTag(curr, `List.cons)) {
    const head = getField(curr, 0);
    const tail = getField(curr, 1);
    out.push(head);
    curr = tail;
  }
]

-- ```lean
-- def Array.mkEmpty {α : Type u} (c : @& Nat) : Array α where
--   toList := List.nil
-- ```
--
-- ```cpp
-- static inline lean_object * lean_mk_empty_array_with_capacity(b_lean_obj_arg capacity) {
--     if (!lean_is_scalar(capacity)) lean_internal_panic_out_of_memory();
--     return lean_alloc_array(0, lean_unbox(capacity));
-- }
-- ```
--
-- ```lean
-- def Array.emptyWithCapacity {α : Type u} (c : @& Nat) : Array α where
--   toList := List.nil
-- ```
--
-- ```cpp
-- static inline lean_object * lean_mk_empty_array_with_capacity(b_lean_obj_arg capacity) {
--     if (!lean_is_scalar(capacity)) lean_internal_panic_out_of_memory();
--     return lean_alloc_array(0, lean_unbox(capacity));
-- }
-- ```
def lean_mk_empty_array_with_capacity := [JS_EXPR|[]]

-- ```lean
-- def Array.size {α : Type u} (a : @& Array α) : Nat :=
--  a.toList.length
-- ```
--
-- ```cpp
-- static inline lean_object * lean_array_get_size(b_lean_obj_arg a) {
--     return lean_box(lean_array_size(a));
-- }
-- ```
def lean_array_get_size := [JS_EXPR|(#0).length]

-- ```lean
-- unsafe opaque Array.getInternalBorrowed {α : Type u} (a : @& Array α) (i : @& Nat) (h : LT.lt i a.size) : α :=
--   a.toList.get ⟨i, h⟩
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_array_fget_borrowed(b_lean_obj_arg a, b_lean_obj_arg i) {
--     return lean_array_get_core(a, lean_unbox(i));
-- }
-- ```
def lean_array_fget_borrowed := [JS_EXPR|#0[#1]]

-- ```lean
-- def Array.getInternal {α : Type u} (a : @& Array α) (i : @& Nat) (h : LT.lt i a.size) : α :=
--   a.toList.get ⟨i, h⟩
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_array_fget(b_lean_obj_arg a, b_lean_obj_arg i) {
--     return lean_array_uget(a, lean_unbox(i));
-- }
-- ```
def lean_array_fget := [JS_EXPR|#0[#1]]

-- ```lean
-- def Array.get!Internal {α : Type u} [@&Inhabited α] (a : @& Array α) (i : @& Nat) : α :=
--   Array.getD a i default
-- ```
--
-- ```cpp
-- static inline lean_object * lean_array_get(b_lean_obj_arg def_val, b_lean_obj_arg a, b_lean_obj_arg i) {
--     if (lean_is_scalar(i)) {
--         size_t idx = lean_unbox(i);
--         if (idx < lean_array_size(a)) {
--             return lean_array_uget(a, idx);
--         }
--     }
--     /* Recall that if `i` is not a scalar, then it must be out of bounds because
--        i > LEAN_MAX_SMALL_NAT == MAX_UNSIGNED >> 1
--        but each array entry is 8 bytes in 64-bit machines and 4 in 32-bit ones.
--        In both cases, we would be out-of-memory. */
--     lean_inc(def_val);
--     return lean_array_get_panic(def_val);
-- }
-- ```
def lean_array_get := [JS_EXPR|(#2 < (#1).length) ? #1[#2] : #0]

-- ```lean
-- def Array.push {α : Type u} (a : Array α) (v : α) : Array α where
--   toList := List.concat a.toList v
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT object * lean_array_push(obj_arg a, obj_arg v) {
--     object * r;
--     if (lean_is_exclusive(a)) {
--         if (lean_array_capacity(a) > lean_array_size(a))
--             r = a;
--         else
--             r = lean_copy_expand_array(a, true);
--     } else {
--         r = lean_copy_expand_array_nonlinear(a, lean_array_capacity(a) < 2*lean_array_size(a) + 1);
--     }
--     lean_assert(lean_array_capacity(r) > lean_array_size(r));
--     size_t & sz  = lean_to_array(r)->m_size;
--     object ** it = lean_array_cptr(r) + sz;
--     *it = v;
--     sz++;
--     return r;
-- }
-- ```
def lean_array_push := [JS_EXPR|(#0).concat(Array.of(#1))]

-- ```lean
-- attribute [extern "lean_byte_array_mk"] ByteArray.mk
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_byte_array_mk(obj_arg a) {
--     usize sz      = lean_array_size(a);
--     obj_res r     = lean_alloc_sarray(1, sz, sz);
--     object ** it  = lean_array_cptr(a);
--     object ** end = it + sz;
--     uint8 * dest  = lean_sarray_cptr(r);
--     for (; it != end; ++it, ++dest) {
--         *dest = lean_unbox(*it);
--     }
--     lean_dec(a);
--     return r;
-- }
-- ```
def lean_byte_array_mk := [JS_EXPR|throw new Error("lean_byte_array_mk is not implemented")]

-- ```lean
-- attribute [extern "lean_byte_array_data"] ByteArray.data
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_byte_array_data(obj_arg a) {
--     usize sz       = lean_sarray_size(a);
--     obj_res r      = lean_alloc_array(sz, sz);
--     uint8 * it     = lean_sarray_cptr(a);
--     uint8 * end    = it+sz;
--     object ** dest = lean_array_cptr(r);
--     for (; it != end; ++it, ++dest) {
--         *dest = lean_box(*it);
--     }
--     lean_dec(a);
--     return r;
-- }
-- ```
def lean_byte_array_data := [JS_EXPR|throw new Error("lean_byte_array_data is not implemented")]

-- ```lean
-- def ByteArray.emptyWithCapacity (c : @& Nat) : ByteArray :=
--   { data := Array.empty }
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_mk_empty_byte_array(b_lean_obj_arg capacity) {
--     if (!lean_is_scalar(capacity)) lean_internal_panic_out_of_memory();
--     return lean_alloc_sarray(1, 0, lean_unbox(capacity));
-- }
-- ```
def lean_mk_empty_byte_array := [JS_EXPR|new Uint8Array(0)]

-- ```lean
-- def ByteArray.push : ByteArray → UInt8 → ByteArray
--   | ⟨bs⟩, b => ⟨bs.push b⟩
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_byte_array_push(obj_arg a, uint8 b) {
--     object * r = lean_sarray_ensure_exclusive(lean_sarray_ensure_capacity(a, lean_sarray_size(a) + 1, /* exact */ false));
--     size_t & sz  = lean_to_sarray(r)->m_size;
--     uint8 * it   = lean_sarray_cptr(r) + sz;
--     *it = b;
--     sz++;
--     return r;
-- }
-- ```
def lean_byte_array_push := [JS_EXPR|new Uint8Array(Array.from(#0).concat(Array.of(#1)))]

-- ```lean
-- def ByteArray.size : (@& ByteArray) → Nat
--   | ⟨bs⟩ => bs.size
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_byte_array_size(b_lean_obj_arg a) {
--     return lean_box(lean_sarray_size(a));
-- }
-- ```
def lean_byte_array_size := [JS_EXPR|(#0).length]

-- ```lean
-- attribute [extern "lean_string_to_utf8"] String.toByteArray
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_string_to_utf8(b_obj_arg s) {
--     size_t sz = lean_string_size(s) - 1;
--     obj_res r = lean_alloc_sarray(1, sz, sz);
--     memcpy(lean_sarray_cptr(r), lean_string_cstr(s), sz);
--     return r;
-- }
-- ```
def lean_string_to_utf8 := [JS_EXPR|new TextEncoder().encode(#0)]

-- ```lean
-- attribute [extern "lean_string_from_utf8_unchecked"] String.ofByteArray
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_string_from_utf8_unchecked(obj_arg a) {
--     obj_res ret = lean_mk_string_from_bytes_unchecked(reinterpret_cast<char *>(lean_sarray_cptr(a)), lean_sarray_size(a));
--     lean_dec(a);
--     return ret;
-- }
-- ```
def lean_string_from_utf8_unchecked := [JS_EXPR|new TextDecoder().decode(#0)]

-- ```lean
-- def String.ofList (data : List Char) : String :=
--   ⟨List.utf8Encode data, .intro data rfl⟩
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_string_mk(obj_arg cs) {
--     std::string s;
--     b_obj_arg o = cs;
--     size_t len = 0;
--     while (!lean_is_scalar(o)) {
--         push_unicode_scalar(s, lean_unbox_uint32(lean_ctor_get(o, 0)));
--         o = lean_ctor_get(o, 1);
--         len++;
--     }
--     lean_dec(cs);
--     return lean_mk_string_unchecked(s.data(), s.size(), len);
-- }
-- ```
def lean_string_mk := [JS_EXPR|throw new Error("lean_string_mk should not be implemented")]

-- ```lean
-- def String.decEq (s₁ s₂ : @& String) : Decidable (Eq s₁ s₂) :=
--   match s₁, s₂ with
--   | ⟨⟨⟨s₁⟩⟩, _⟩, ⟨⟨⟨s₂⟩⟩, _⟩ =>
--     dite (Eq s₁ s₂) (fun h => match s₁, s₂, h with | _, _, Eq.refl _ => isTrue rfl)
--       (fun h => isFalse
--         (fun h' => h (congrArg (fun s => Array.toList (ByteArray.data (String.toByteArray s))) h')))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_string_dec_eq(b_lean_obj_arg s1, b_lean_obj_arg s2) { return lean_string_eq(s1, s2); }
-- ```
def lean_string_dec_eq := [JS_EXPR|#0 == #1]

-- ```lean
-- def String.utf8ByteSize (s : @& String) : Nat :=
--   s.toByteArray.size
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_string_utf8_byte_size(b_lean_obj_arg s) { return lean_box(lean_string_size(s) - 1); }
-- ```
def lean_string_utf8_byte_size := [JS_EXPR|new TextEncoder().encode(#0).length]

-- ```lean
-- def panicCore {α : Sort u} [@&Inhabited α] (msg : String) : α := default
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT object * lean_panic_fn_borrowed(b_obj_arg default_val, object * msg) {
--     lean_inc(default_val);
--     return lean_panic_fn(default_val, msg);
-- }
-- ```
def lean_panic_fn_borrowed := [JS_EXPR|throw new Error(#1)]

-- ```lean
-- opaque mixHash (u₁ u₂ : UInt64) : UInt64
-- ```
--
-- ```cpp
-- static inline uint64_t lean_uint64_mix_hash(uint64_t h, uint64_t k) {
--     uint64_t m = 0xc6a4a7935bd1e995;
--     uint64_t r = 47;
--     k *= m;
--     k ^= k >> r;
--     k ^= m;
--     h ^= k;
--     h *= m;
--     return h;
-- }
-- ```
def lean_uint64_mix_hash := [JS_EXPR|throw new Error("lean_uint64_mix_hash is not implemented")]

-- ```lean
-- protected opaque String.hash (s : @& String) : UInt64
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint64 lean_string_hash(b_obj_arg s) {
--     usize sz = lean_string_size(s) - 1;
--     char const * str = lean_string_cstr(s);
--     return hash_str(sz, (unsigned char const *) str, 11);
-- }
-- ```
def lean_string_hash := [JS_EXPR|throw new Error("lean_string_hash is not implemented")]

-- ```lean
-- protected def beq : (@& Name) → (@& Name) → Bool
--   | anonymous, anonymous => true
--   | str p₁ s₁, str p₂ s₂ => and (BEq.beq s₁ s₂) (Name.beq p₁ p₂)
--   | num p₁ n₁, num p₂ n₂ => and (BEq.beq n₁ n₂) (Name.beq p₁ p₂)
--   | _,         _         => false
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8 lean_name_eq(b_lean_obj_arg n1, b_lean_obj_arg n2) {
--     if (n1 == n2)
--         return true;
--     if (lean_is_scalar(n1) != lean_is_scalar(n2) || lean_name_hash_ptr(n1) != lean_name_hash_ptr(n2))
--         return false;
--     while (true) {
--         lean_assert(!lean_is_scalar(n1));
--         lean_assert(!lean_is_scalar(n2));
--         lean_assert(n1 && n2);
--         if (lean_ptr_tag(n1) != lean_ptr_tag(n2))
--             return false;
--         if (lean_ptr_tag(n1) == 1) {
--             if (!lean_string_eq(lean_ctor_get(n1, 1), lean_ctor_get(n2, 1)))
--                 return false;
--         } else {
--             if (!lean_nat_eq(lean_ctor_get(n1, 1), lean_ctor_get(n2, 1)))
--                 return false;
--         }
--         n1 = lean_ctor_get(n1, 0);
--         n2 = lean_ctor_get(n2, 0);
--         if (n1 == n2)
--             return true;
--         if (lean_is_scalar(n1) != lean_is_scalar(n2))
--             return false;
--         /*
--         // The `return false` in the following `if` is seldom reached.
--         if (lean_name_hash_ptr(n1) != lean_name_hash_ptr(n2))
--             return false;
--         */
--     }
-- }
-- ```
def lean_name_eq := [JS_EXPR|throw new Error("lean_name_eq is not implemented")]

-- ============
-- Init.Data.Array.Set
-- ============

-- ```lean
-- def Array.set! (xs : Array α) (i : @& Nat) (v : α) : Array α :=
--   Array.setIfInBounds xs i v
-- ```
--
-- ```cpp
-- static inline lean_object * lean_array_set(lean_obj_arg a, b_lean_obj_arg i, lean_obj_arg v) {
--     if (lean_is_scalar(i)) {
--         size_t idx = lean_unbox(i);
--         if (idx < lean_array_size(a))
--             return lean_array_uset(a, idx, v);
--     }
--     return lean_array_set_panic(a, v);
-- }
-- ```
def lean_array_set := lean_array_fset

-- ============
-- Init.Core
-- ============

-- ```lean
-- attribute [extern "lean_mk_thunk"] Thunk.mk
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_mk_thunk(lean_obj_arg c) {
--     lean_thunk_object * o = (lean_thunk_object*)lean_alloc_small_object(sizeof(lean_thunk_object));
--     lean_set_st_header((lean_object*)o, LeanThunk, 0);
--     o->m_value   = (lean_object*)0;
--     o->m_closure = c;
--     return (lean_object*)o;
-- }
-- ```
def lean_mk_thunk := [JS_FUNC|inputs(fn)|
  let cached = null;
  let evaluated = false;
  return ({
    get: ( ) => {
      if (!evaluated) {
        cached = fn( );
        evaluated = true;
      }
      return cached;
    }
  });
]

-- ```lean
-- protected def Thunk.pure (a : α) : Thunk α :=
--   ⟨fun _ => a⟩
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_thunk_pure(lean_obj_arg v) {
--     lean_thunk_object * o = (lean_thunk_object*)lean_alloc_small_object(sizeof(lean_thunk_object));
--     lean_set_st_header((lean_object*)o, LeanThunk, 0);
--     o->m_value   = v;
--     o->m_closure = (lean_object*)0;
--     return (lean_object*)o;
-- }
-- ```
def lean_thunk_pure := [JS_EXPR| { get: ( ) => #0 } ]

-- ```lean
-- protected def Thunk.get (x : @& Thunk α) : α :=
--   x.fn ()
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_thunk_get_own(b_lean_obj_arg t) {
--     lean_object * r = lean_thunk_get(t);
--     lean_inc(r);
--     return r;
-- }
-- ```
def lean_thunk_get_own := [JS_EXPR| (#0).get() ]

-- ```lean
-- attribute [extern "lean_task_pure"] Task.pure
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_task_pure(obj_arg a) {
--     return (lean_object*)alloc_task(a);
-- }
-- ```
def lean_task_pure := [JS_EXPR|Promise.resolve(#0)]

-- ```lean
-- attribute [extern "lean_task_get_own"] Task.get
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_task_get_own(lean_obj_arg t) {
--     lean_object * r = lean_task_get(t);
--     lean_inc(r);
--     lean_dec(t);
--     return r;
-- }
-- ```
def lean_task_get_own := [JS_EXPR|#0]

-- ```lean
-- protected def spawn {α : Type u} (fn : Unit → α) (prio := Priority.default) : Task α :=
--   ⟨fn ()⟩
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_task_spawn(lean_obj_arg c, lean_obj_arg prio) { return lean_task_spawn_core(c, lean_unbox(prio), false); }
-- ```
def lean_task_spawn := [JS_EXPR|Promise.resolve( ).«then»(#0)]

-- ```lean
-- protected def map (f : α → β) (x : Task α) (prio := Priority.default) (sync := false) : Task β :=
--   ⟨f x.get⟩
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_task_map(lean_obj_arg f, lean_obj_arg t, lean_obj_arg prio, uint8_t sync) { return lean_task_map_core(f, t, lean_unbox(prio), sync, false); }
-- ```
def lean_task_map := [JS_EXPR|(#1).«then»(#0)]

-- ```lean
-- protected def bind (x : Task α) (f : α → Task β) (prio := Priority.default) (sync := false) :
--     Task β :=
--   ⟨(f x.get).get⟩
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_task_bind(lean_obj_arg x, lean_obj_arg f, lean_obj_arg prio, uint8_t sync) { return lean_task_bind_core(x, f, lean_unbox(prio), sync, false); }
-- ```
def lean_task_bind := [JS_EXPR|(#0).«then»(#1)]

-- ```lean
-- def strictOr  (b₁ b₂ : Bool) := b₁ || b₂
-- ```
--
-- ```cpp
-- static inline uint8_t lean_strict_or(uint8_t b1, uint8_t b2) {
--     return b1 || b2;
-- }
-- ```
def lean_strict_or := [JS_EXPR|#0 || #1]

-- ```lean
-- def strictAnd (b₁ b₂ : Bool) := b₁ && b₂
-- ```
--
-- ```cpp
-- static inline uint8_t lean_strict_and(uint8_t b1, uint8_t b2) {
--     return b1 && b2;
-- }
-- ```
def lean_strict_and := [JS_EXPR|#0 && #1]

-- ============
-- Init.Data.Int.Basic
-- ============

-- ```lean
-- attribute [extern "lean_nat_to_int"] Int.ofNat
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_nat_to_int(lean_obj_arg a) {
--     if (lean_is_scalar(a)) {
--         size_t v = lean_unbox(a);
--         if (v <= LEAN_MAX_SMALL_INT)
--             return a;
--         else
--             return lean_big_size_t_to_int(v);
--     } else {
--         return a;
--     }
-- }
-- ```
def lean_nat_to_int := [JS_EXPR|#0]

-- ```lean
-- attribute [extern "lean_int_neg_succ_of_nat"] Int.negSucc
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_int_neg_succ_of_nat(lean_obj_arg a) {
--     lean_obj_res s  = lean_nat_succ(a);    lean_dec(a);
--     lean_obj_res i  = lean_nat_to_int(s);  /* Recall that `lean_nat_to_int` consumes the argument */
--     lean_obj_res r  = lean_int_neg(i);     lean_dec(i);
--     return r;
-- }
-- ```
def lean_int_neg_succ_of_nat := [JS_EXPR|-#0 - 1]

-- ```lean
-- protected def neg (n : @& Int) : Int :=
--   match n with
--   | ofNat n   => negOfNat n
--   | negSucc n => succ n
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_int_neg(b_lean_obj_arg a) {
--     if (LEAN_LIKELY(lean_is_scalar(a))) {
--         return lean_int64_to_int(-lean_scalar_to_int64(a));
--     } else {
--         return lean_int_big_neg(a);
--     }
-- }
-- ```
def lean_int_neg := [JS_EXPR|-#0]

-- ```lean
-- protected def add (m n : @& Int) : Int :=
--   match m, n with
--   | ofNat m, ofNat n => ofNat (m + n)
--   | ofNat m, -[n +1] => subNatNat m (succ n)
--   | -[m +1], ofNat n => subNatNat n (succ m)
--   | -[m +1], -[n +1] => negSucc (succ (m + n))
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_int_add(b_lean_obj_arg a1, b_lean_obj_arg a2) {
--     if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
--         return lean_int64_to_int(lean_scalar_to_int64(a1) + lean_scalar_to_int64(a2));
--     } else {
--         return lean_int_big_add(a1, a2);
--     }
-- }
-- ```
def lean_int_add := [JS_EXPR|#0 + #1]

-- ```lean
-- protected def mul (m n : @& Int) : Int :=
--   match m, n with
--   | ofNat m, ofNat n => ofNat (m * n)
--   | ofNat m, -[n +1] => negOfNat (m * succ n)
--   | -[m +1], ofNat n => negOfNat (succ m * n)
--   | -[m +1], -[n +1] => ofNat (succ m * succ n)
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_int_mul(b_lean_obj_arg a1, b_lean_obj_arg a2) {
--     if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
--         return lean_int64_to_int(lean_scalar_to_int64(a1) * lean_scalar_to_int64(a2));
--     } else {
--         return lean_int_big_mul(a1, a2);
--     }
-- }
-- ```
def lean_int_mul := [JS_EXPR|#0 * #1]

-- ```lean
-- protected def sub (m n : @& Int) : Int := m + (- n)
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_int_sub(b_lean_obj_arg a1, b_lean_obj_arg a2) {
--     if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
--         return lean_int64_to_int(lean_scalar_to_int64(a1) - lean_scalar_to_int64(a2));
--     } else {
--         return lean_int_big_sub(a1, a2);
--     }
-- }
-- ```
def lean_int_sub := [JS_EXPR|#0 - #1]

-- ```lean
-- protected def decEq (a b : @& Int) : Decidable (a = b) :=
--   match a, b with
--   | ofNat a, ofNat b => match decEq a b with
--     | isTrue h  => isTrue  <| h ▸ rfl
--     | isFalse h => isFalse <| fun h' => Int.noConfusion h' (fun h' => absurd h' h)
--   | ofNat _, -[_ +1] => isFalse <| fun h => Int.noConfusion h
--   | -[_ +1], ofNat _ => isFalse <| fun h => Int.noConfusion h
--   | -[a +1], -[b +1] => match decEq a b with
--     | isTrue h  => isTrue  <| h ▸ rfl
--     | isFalse h => isFalse <| fun h' => Int.noConfusion h' (fun h' => absurd h' h)
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int_dec_eq(b_lean_obj_arg a1, b_lean_obj_arg a2) { return lean_int_eq(a1, a2); }
-- ```
def lean_int_dec_eq := [JS_EXPR|#0 == #1]

-- ```lean
-- def decNonneg (m : @& Int) : Decidable (NonNeg m) :=
--   match m with
--   | ofNat m => isTrue <| NonNeg.mk m
--   | -[i +1] => isFalse <| fun h =>
--     have : ∀ j, (j = -[i +1]) → NonNeg j → False := fun _ hj hnn =>
--       Int.NonNeg.casesOn (motive := fun j _ => j = -[i +1] → False) hnn
--         (fun _ h => Int.noConfusion h) hj
--     this -[i +1] rfl h
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int_dec_nonneg(b_lean_obj_arg a) {
--     if (LEAN_LIKELY(lean_is_scalar(a)))
--         return lean_scalar_to_int(a) >= 0;
--     else
--         return lean_int_big_nonneg(a);
-- }
-- ```
def lean_int_dec_nonneg := [JS_EXPR|#0 >= 0]

-- ```lean
-- instance decLe (a b : @& Int) : Decidable (a ≤ b) :=
--   decNonneg _
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int_dec_le(b_lean_obj_arg a1, b_lean_obj_arg a2) { return lean_int_le(a1, a2); }
-- ```
def lean_int_dec_le := [JS_EXPR|#0 <= #1]

-- ```lean
-- instance decLt (a b : @& Int) : Decidable (a < b) :=
--   decNonneg _
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int_dec_lt(b_lean_obj_arg a1, b_lean_obj_arg a2) { return lean_int_lt(a1, a2); }
-- ```
def lean_int_dec_lt := [JS_EXPR|#0 < #1]

-- ```lean
-- def natAbs (m : @& Int) : Nat :=
--   match m with
--   | ofNat m => m
--   | -[m +1] => m.succ
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_nat_abs(b_lean_obj_arg i) {
--     if (lean_int_lt(i, lean_box(0))) {
--         return lean_int_to_nat(lean_int_neg(i));
--     } else {
--         lean_inc(i);
--         return lean_int_to_nat(i);
--     }
-- }
-- ```
def lean_nat_abs := [JS_EXPR|(#0 < 0) ? -#0 : #0]

-- ============
-- Init.Data.Nat.Div.Basic
-- ============

-- ```lean
-- protected def divExact (x y : @& Nat) (h : y ∣ x) : Nat :=
--   x / y
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_nat_div_exact(b_lean_obj_arg a1, b_lean_obj_arg a2) {
--     if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
--         size_t n1 = lean_unbox(a1);
--         size_t n2 = lean_unbox(a2);
--         if (n2 == 0)
--             return lean_box(0);
--         else
--             return lean_box(n1 / n2);
--     } else {
--         return lean_nat_big_div_exact(a1, a2);
--     }
-- }
-- ```
def lean_nat_div_exact := [JS_EXPR|(#1 === 0) ? false : (#0 % #1 === 0)]

-- ============
-- Init.Data.Int.DivMod.Basic
-- ============

-- ```lean
-- def ediv : (@& Int) → (@& Int) → Int
--   | ofNat m, ofNat n => ofNat (m / n)
--   | ofNat m, -[n+1]  => -ofNat (m / succ n)
--   | -[_+1],  0       => 0
--   | -[m+1],  ofNat (succ n) => -[m / succ n +1]
--   | -[m+1],  -[n+1]  => ofNat (succ (m / succ n))
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_int_ediv(b_lean_obj_arg a1, b_lean_obj_arg a2) {
--     if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
--         if (sizeof(void*) == 8) {
--             /* 64-bit version, we use 64-bit numbers to avoid overflow when v1 == LEAN_MIN_SMALL_INT. */
--             int64_t n = lean_scalar_to_int(a1);
--             int64_t d = lean_scalar_to_int(a2);
--             if (d == 0)
--                 return lean_box(0);
--             else {
--                 int64_t q = n / d;
--                 int64_t r = n % d;
--                 if (r < 0)
--                     q = (d > 0) ? q - 1 : q + 1;
--                 return lean_int64_to_int(q);
--             }
--         } else {
--             /* 32-bit version */
--             int n = lean_scalar_to_int(a1);
--             int d = lean_scalar_to_int(a2);
--             if (d == 0) {
--                 return lean_box(0);
--             } else {
--                 int q = n / d;
--                 int r = n % d;
--                 if (r < 0)
--                     q = (d > 0) ? q - 1 : q + 1;
--                 return lean_int_to_int(q);
--             }
--         }
--     } else {
--         return lean_int_big_ediv(a1, a2);
--     }
-- }
-- ```
def lean_int_ediv := [JS_FUNC|inputs(a, b)|
  return (bBig == 0) ? 0 : (aBig / bBig);
]

-- ```lean
-- def emod : (@& Int) → (@& Int) → Int
--   | ofNat m, n => ofNat (m % natAbs n)
--   | -[m+1],  n => subNatNat (natAbs n) (succ (m % natAbs n))
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_int_emod(b_lean_obj_arg a1, b_lean_obj_arg a2) {
--     if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
--         if (sizeof(void*) == 8) {
--             /* 64-bit version, we use 64-bit numbers to avoid overflow when v1 == LEAN_MIN_SMALL_INT. */
--             int64_t n = lean_scalar_to_int64(a1);
--             int64_t d = lean_scalar_to_int64(a2);
--             if (d == 0) {
--                 return a1;
--             } else {
--                 int64_t r = n % d;
--                 if (r < 0)
--                     r = (d > 0) ? r + d : r - d;
--                 return lean_int64_to_int(r);
--             }
--         } else {
--             /* 32-bit version */
--             int n = lean_scalar_to_int(a1);
--             int d = lean_scalar_to_int(a2);
--             if (d == 0)
--                 return a1;
--             else {
--                 int r = n % d;
--                 if (r < 0)
--                     r = (d > 0) ? r + d : r - d;
--                 return lean_int_to_int(r);
--             }
--         }
--     } else {
--         return lean_int_big_emod(a1, a2);
--     }
-- }
-- ```
def lean_int_emod := [JS_FUNC|inputs(a, b)|
  return (bBig == 0) ? aBig : (aBig % bBig);
]

-- ```lean
-- protected def divExact (x y : @& Int) (h : y ∣ x) : Int :=
--   x / y
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_int_div_exact(b_lean_obj_arg a1, b_lean_obj_arg a2) {
--     if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
--         if (sizeof(void*) == 8) {
--             /* 64-bit version, we use 64-bit numbers to avoid overflow when v1 == LEAN_MIN_SMALL_INT. */
--             int64_t v1 = lean_scalar_to_int(a1);
--             int64_t v2 = lean_scalar_to_int(a2);
--             if (v2 == 0)
--                 return lean_box(0);
--             else
--                 return lean_int64_to_int(v1 / v2);
--         } else {
--             /* 32-bit version */
--             int v1 = lean_scalar_to_int(a1);
--             int v2 = lean_scalar_to_int(a2);
--             if (v2 == 0)
--                 return lean_box(0);
--             else
--                 return lean_int_to_int(v1 / v2);
--         }
--     } else {
--         return lean_int_big_div_exact(a1, a2);
--     }
-- }
-- ```
def lean_int_div_exact := [JS_FUNC|inputs(a, b)|
  return (bBig == 0) ? false : (aBig % bBig == 0);
]

-- ```lean
-- def tdiv : (@& Int) → (@& Int) → Int
--   | ofNat m, ofNat n =>  ofNat (m / n)
--   | ofNat m, -[n +1] => -ofNat (m / succ n)
--   | -[m +1], ofNat n => -ofNat (succ m / n)
--   | -[m +1], -[n +1] =>  ofNat (succ m / succ n)
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_int_div(b_lean_obj_arg a1, b_lean_obj_arg a2) {
--     if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
--         if (sizeof(void*) == 8) {
--             /* 64-bit version, we use 64-bit numbers to avoid overflow when v1 == LEAN_MIN_SMALL_INT. */
--             int64_t v1 = lean_scalar_to_int(a1);
--             int64_t v2 = lean_scalar_to_int(a2);
--             if (v2 == 0)
--                 return lean_box(0);
--             else
--                 return lean_int64_to_int(v1 / v2);
--         } else {
--             /* 32-bit version */
--             int v1 = lean_scalar_to_int(a1);
--             int v2 = lean_scalar_to_int(a2);
--             if (v2 == 0)
--                 return lean_box(0);
--             else
--                 return lean_int_to_int(v1 / v2);
--         }
--     } else {
--         return lean_int_big_div(a1, a2);
--     }
-- }
-- ```
def lean_int_div := [JS_FUNC|inputs(a, b)|
  return (bBig == 0) ? 0 : (aBig / bBig);
]

-- ```lean
-- def tmod : (@& Int) → (@& Int) → Int
--   | ofNat m, ofNat n =>  ofNat (m % n)
--   | ofNat m, -[n +1] =>  ofNat (m % succ n)
--   | -[m +1], ofNat n => -ofNat (succ m % n)
--   | -[m +1], -[n +1] => -ofNat (succ m % succ n)
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_int_mod(b_lean_obj_arg a1, b_lean_obj_arg a2) {
--     if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
--         if (sizeof(void*) == 8) {
--             /* 64-bit version, we use 64-bit numbers to avoid overflow when v1 == LEAN_MIN_SMALL_INT. */
--             int64_t v1 = lean_scalar_to_int64(a1);
--             int64_t v2 = lean_scalar_to_int64(a2);
--             if (v2 == 0)
--                 return a1;
--             else
--                 return lean_int64_to_int(v1 % v2);
--         } else {
--             /* 32-bit version */
--             int v1 = lean_scalar_to_int(a1);
--             int v2 = lean_scalar_to_int(a2);
--             if (v2 == 0)
--                 return a1;
--             else
--                 return lean_int_to_int(v1 % v2);
--         }
--     } else {
--         return lean_int_big_mod(a1, a2);
--     }
-- }
-- ```
def lean_int_mod := [JS_FUNC|inputs(a, b)|
  return (bBig == 0) ? aBig : (aBig % bBig);
]

-- ============
-- Init.Data.Nat.Bitwise.Basic
-- ============

-- ```lean
-- def land : @& Nat → @& Nat → Nat := bitwise and
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_nat_land(b_lean_obj_arg a1, b_lean_obj_arg a2) {
--     if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
--         return (lean_object*)((size_t)(a1) & (size_t)(a2));
--     } else {
--         return lean_nat_big_land(a1, a2);
--     }
-- }
-- ```
def lean_nat_land := [JS_EXPR|#0 & #1]

-- ```lean
-- def lor  : @& Nat → @& Nat → Nat := bitwise or
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_nat_lor(b_lean_obj_arg a1, b_lean_obj_arg a2) {
--     if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
--         return (lean_object*)((size_t)(a1) | (size_t)(a2));
--     } else {
--         return lean_nat_big_lor(a1, a2);
--     }
-- }
-- ```
def lean_nat_lor := [JS_EXPR|#0 | #1]

-- ```lean
-- def xor  : @& Nat → @& Nat → Nat := bitwise bne
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_nat_lxor(b_lean_obj_arg a1, b_lean_obj_arg a2) {
--     if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
--         return lean_box(lean_unbox(a1) ^ lean_unbox(a2));
--     } else {
--         return lean_nat_big_xor(a1, a2);
--     }
-- }
-- ```
def lean_nat_lxor := [JS_EXPR|#0 ^ #1]

-- ```lean
-- def shiftLeft : @& Nat → @& Nat → Nat
--   | n, 0 => n
--   | n, succ m => shiftLeft (2*n) m
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT lean_obj_res lean_nat_shiftl(b_lean_obj_arg a1, b_lean_obj_arg a2) {
--     // Special case for shifted value is 0.
--     if (lean_is_scalar(a1) && lean_unbox(a1) == 0) {
--         return lean_box(0);
--     }
--     auto a = lean_is_scalar(a1)
--            ? mpz::of_size_t(lean_unbox(a1))
--            : mpz_value(a1);
--     if (!lean_is_scalar(a2) || lean_unbox(a2) > UINT_MAX) {
--         lean_internal_panic("Nat.shiftl exponent is too big");
--     }
--     mpz r;
--     mul2k(r, a, lean_unbox(a2));
--     return mpz_to_nat(r);
-- }
-- ```
def lean_nat_shiftl := [JS_EXPR|#0 << #1]

-- ```lean
-- def shiftRight : @& Nat → @& Nat → Nat
--   | n, 0 => n
--   | n, succ m => shiftRight n m / 2
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_nat_shiftr(b_lean_obj_arg a1, b_lean_obj_arg a2) {
--     if (LEAN_LIKELY(lean_is_scalar(a1) && lean_is_scalar(a2))) {
--         size_t s1 = lean_unbox(a1);
--         size_t s2 = lean_unbox(a2);
--         size_t r = (s2 < sizeof(size_t)*8) ? s1 >> s2 : 0;
--         return lean_box(r);
--     } else {
--         return lean_nat_big_shiftr(a1, a2);
--     }
-- }
-- ```
def lean_nat_shiftr := [JS_EXPR|#0 >> #1]

-- ============
-- Init.Data.UInt.BasicAux
-- ============

-- ```lean
-- def UInt8.toNat (n : UInt8) : Nat := n.toBitVec.toNat
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_uint8_to_nat(uint8_t a) { return lean_usize_to_nat((size_t)a); }
-- ```
-- duplicate of lean_uint8_to_nat:
-- def lean_uint8_to_nat := [JS_EXPR|#0]

-- ```lean
-- def UInt16.ofNat (n : @& Nat) : UInt16 := ⟨BitVec.ofNat 16 n⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_uint16_of_nat(b_lean_obj_arg a) { return lean_is_scalar(a) ? (int16_t)(lean_unbox(a)) : lean_uint16_of_big_nat(a); }
-- ```
-- duplicate of lean_uint16_of_nat:
-- def lean_uint16_of_nat := [JS_EXPR|BigInt(#0) & 0xFFFF]

-- ```lean
-- def UInt16.toNat (n : UInt16) : Nat := n.toBitVec.toNat
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_uint16_to_nat(uint16_t a) { return lean_usize_to_nat((size_t)a); }
-- ```
-- duplicate of lean_uint16_to_nat:
-- def lean_uint16_to_nat := [JS_EXPR|#0]

-- ```lean
-- def UInt16.toUInt8 (a : UInt16) : UInt8 := a.toNat.toUInt8
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint16_to_uint8(uint16_t a) { return ((uint8_t)a); }
-- ```
def lean_uint16_to_uint8 := [JS_EXPR|#0 & 0xFF]

-- ```lean
-- def UInt8.toUInt16 (a : UInt8) : UInt16 := ⟨⟨a.toNat, Nat.lt_trans a.toBitVec.isLt (by decide)⟩⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_uint8_to_uint16(uint8_t a) { return ((uint16_t)a); }
-- ```
def lean_uint8_to_uint16 := [JS_EXPR|#0 & 0xFFFF]

-- ```lean
-- def UInt32.ofNat (n : @& Nat) : UInt32 := ⟨BitVec.ofNat 32 n⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_uint32_of_nat(b_lean_obj_arg a) { return lean_is_scalar(a) ? (uint32_t)(lean_unbox(a)) : lean_uint32_of_big_nat(a); }
-- ```
-- duplicate of lean_uint32_of_nat:
-- def lean_uint32_of_nat := [JS_EXPR|toUInt32(#0)]

-- ```lean
-- def UInt32.toUInt8 (a : UInt32) : UInt8 := a.toNat.toUInt8
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint32_to_uint8(uint32_t a) { return ((uint8_t)a); }
-- ```
def lean_uint32_to_uint8 := [JS_EXPR|BigInt(toUInt32(#0) & 0xFF)]

-- ```lean
-- def UInt32.toUInt16 (a : UInt32) : UInt16 := a.toNat.toUInt16
-- ```
--
-- ```cpp
-- static inline uint16_t lean_uint32_to_uint16(uint32_t a) { return ((uint16_t)a); }
-- ```
def lean_uint32_to_uint16 := [JS_EXPR|BigInt(toUInt32(#0) & 0xFFFF)]

-- ```lean
-- def UInt8.toUInt32 (a : UInt8) : UInt32 := ⟨⟨a.toNat, Nat.lt_trans a.toBitVec.isLt (by decide)⟩⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_uint8_to_uint32(uint8_t a) { return ((uint32_t)a); }
-- ```
def lean_uint8_to_uint32 := [JS_EXPR|toUInt32(#0)]

-- ```lean
-- def UInt16.toUInt32 (a : UInt16) : UInt32 := ⟨⟨a.toNat, Nat.lt_trans a.toBitVec.isLt (by decide)⟩⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_uint16_to_uint32(uint16_t a) { return ((uint32_t)a); }
-- ```
def lean_uint16_to_uint32 := [JS_EXPR|toUInt32(#0)]

-- ```lean
-- protected def UInt32.add (a b : UInt32) : UInt32 := ⟨a.toBitVec + b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_uint32_add(uint32_t a1, uint32_t a2) { return a1+a2; }
-- ```
def lean_uint32_add := [JS_EXPR|(toUInt32(#0) + toUInt32(#1)) >>> 0]

-- ```lean
-- protected def UInt32.sub (a b : UInt32) : UInt32 := ⟨a.toBitVec - b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_uint32_sub(uint32_t a1, uint32_t a2) { return a1-a2; }
-- ```
def lean_uint32_sub := [JS_EXPR|(toUInt32(#0) - toUInt32(#1)) >>> 0]

-- ```lean
-- def UInt64.ofNat (n : @& Nat) : UInt64 := ⟨BitVec.ofNat 64 n⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_uint64_of_nat(b_lean_obj_arg a) { return lean_is_scalar(a) ? (uint64_t)(lean_unbox(a)) : lean_uint64_of_big_nat(a); }
-- ```
-- duplicate of lean_uint64_of_nat:
-- def lean_uint64_of_nat := [JS_EXPR|BigInt(#0) & 0xFFFFFFFFFFFFFFFF]

-- ```lean
-- def UInt64.toNat (n : UInt64) : Nat := n.toBitVec.toNat
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_uint64_to_nat(uint64_t n) {
--     if (LEAN_LIKELY(n <= LEAN_MAX_SMALL_NAT))
--         return lean_box(n);
--     else
--         return lean_big_uint64_to_nat(n);
-- }
-- ```
-- duplicate of lean_uint64_to_nat:
-- def lean_uint64_to_nat := [JS_EXPR|#0]

-- ```lean
-- def UInt64.toUInt8 (a : UInt64) : UInt8 := a.toNat.toUInt8
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint64_to_uint8(uint64_t a) { return ((uint8_t)a); }
-- ```
def lean_uint64_to_uint8 := [JS_EXPR|#0 & 0xFF]

-- ```lean
-- def UInt64.toUInt16 (a : UInt64) : UInt16 := a.toNat.toUInt16
-- ```
--
-- ```cpp
-- static inline uint16_t lean_uint64_to_uint16(uint64_t a) { return ((uint16_t)a); }
-- ```
def lean_uint64_to_uint16 := [JS_EXPR|#0 & 0xFFFF]

-- ```lean
-- def UInt64.toUInt32 (a : UInt64) : UInt32 := a.toNat.toUInt32
-- ```
--
-- ```cpp
-- static inline uint32_t lean_uint64_to_uint32(uint64_t a) { return ((uint32_t)a); }
-- ```
def lean_uint64_to_uint32 := [JS_EXPR|#0 & 0xFFFFFFFF]

-- ```lean
-- def UInt8.toUInt64 (a : UInt8) : UInt64 := ⟨⟨a.toNat, Nat.lt_trans a.toBitVec.isLt (by decide)⟩⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_uint8_to_uint64(uint8_t a) { return ((uint64_t)a); }
-- ```
def lean_uint8_to_uint64 := [JS_EXPR|#0 & 0xFFFFFFFFFFFFFFFF]

-- ```lean
-- def UInt16.toUInt64 (a : UInt16) : UInt64 := ⟨⟨a.toNat, Nat.lt_trans a.toBitVec.isLt (by decide)⟩⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_uint16_to_uint64(uint16_t a) { return ((uint64_t)a); }
-- ```
def lean_uint16_to_uint64 := [JS_EXPR|#0 & 0xFFFFFFFFFFFFFFFF]

-- ```lean
-- def UInt32.toUInt64 (a : UInt32) : UInt64 := ⟨⟨a.toNat, Nat.lt_trans a.toBitVec.isLt (by decide)⟩⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_uint32_to_uint64(uint32_t a) { return ((uint64_t)a); }
-- ```
def lean_uint32_to_uint64 := [JS_EXPR|#0 & 0xFFFFFFFFFFFFFFFF]

-- ```lean
-- def USize.ofNat (n : @& Nat) : USize := ⟨BitVec.ofNat _ n⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_usize_of_nat(b_lean_obj_arg a) { return lean_is_scalar(a) ? lean_unbox(a) : lean_usize_of_big_nat(a); }
-- ```
-- duplicate of lean_usize_of_nat:
-- def lean_usize_of_nat := [JS_EXPR|toUSize(#0)]

-- ```lean
-- def USize.toNat (n : USize) : Nat := n.toBitVec.toNat
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_usize_to_nat(size_t n) {
--     if (LEAN_LIKELY(n <= LEAN_MAX_SMALL_NAT))
--         return lean_box(n);
--     else
--         return lean_big_usize_to_nat(n);
-- }
-- ```
-- duplicate of lean_usize_to_nat:
-- def lean_usize_to_nat := [JS_EXPR|toUSize(#0)]

-- ```lean
-- def USize.add (a b : USize) : USize := ⟨a.toBitVec + b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_usize_add(size_t a1, size_t a2) { return a1+a2; }
-- ```
def lean_usize_add := [JS_EXPR|(toUSize(#0) + toUSize(#1)) >>> 0]

-- ```lean
-- def USize.sub (a b : USize) : USize := ⟨a.toBitVec - b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_usize_sub(size_t a1, size_t a2) { return a1-a2; }
-- ```
def lean_usize_sub := [JS_EXPR|(toUSize(#0) - toUSize(#1)) >>> 0]

-- ```lean
-- def USize.decLt (a b : USize) : Decidable (a < b) :=
--   inferInstanceAs (Decidable (a.toBitVec < b.toBitVec))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_usize_dec_lt(size_t a1, size_t a2) { return a1 < a2; }
-- ```
def lean_usize_dec_lt := [JS_EXPR|toUSize(#0) < toUSize(#1)]

-- ```lean
-- def USize.decLe (a b : USize) : Decidable (a ≤ b) :=
--   inferInstanceAs (Decidable (a.toBitVec ≤ b.toBitVec))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_usize_dec_le(size_t a1, size_t a2) { return a1 <= a2; }
-- ```
def lean_usize_dec_le := [JS_EXPR|toUSize(#0) <= toUSize(#1)]

-- ============
-- Init.Data.String.Bootstrap
-- ============

-- ```lean
-- def push : String → Char → String
--   | ⟨b, h⟩, c => ⟨b.append (List.utf8Encode [c]), ?pf⟩
-- where finally
--   have ⟨m, hm⟩ := h
--   cases hm
--   exact .intro (m ++ [c]) (by simp [List.utf8Encode, List.toByteArray_append'])
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT object * lean_string_push(object * s, unsigned c) {
--     size_t sz  = lean_string_size(s);
--     size_t len = lean_string_len(s);
--     object * r;
--     if (!lean_is_exclusive(s)) {
--         r = lean_alloc_string(sz, mk_capacity(sz+5), len);
--         memcpy(w_string_cstr(r), lean_string_cstr(s), sz - 1);
--         lean_dec_ref(s);
--     } else {
--         r = string_ensure_capacity(s, 5);
--     }
--     unsigned consumed = push_unicode_scalar(w_string_cstr(r) + sz - 1, c);
--     lean_to_string(r)->m_size   = sz + consumed;
--     lean_to_string(r)->m_length++;
--     w_string_cstr(r)[sz + consumed - 1] = 0;
--     return r;
-- }
-- ```
def lean_string_push := [JS_EXPR|#0 + #1]

-- ```lean
-- opaque posOf (s : String) (c : Char) : Pos.Raw
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_string_posof := [JS_EXPR|throw new Error("lean_string_posof not implemented")]

-- ```lean
-- opaque offsetOfPos (s : String) (pos : Pos.Raw) : Nat
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_string_offsetofpos := [JS_EXPR|#1]

-- ```lean
-- opaque length : (@& String) → Nat
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_string_length(b_lean_obj_arg s) { return lean_box(lean_string_len(s)); }
-- ```
def lean_string_length := [JS_EXPR|(#0).length]

-- ```lean
-- opaque pushn (s : String) (c : Char) (n : Nat) : String
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_string_pushn := [JS_EXPR|(#0) + (#1).join("")]

-- ```lean
-- opaque append : String → (@& String) → String
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT object * lean_string_append(object * s1, object * s2) {
--     size_t sz1      = lean_string_size(s1);
--     size_t sz2      = lean_string_size(s2);
--     size_t len1     = lean_string_len(s1);
--     size_t len2     = lean_string_len(s2);
--     size_t new_len  = len1 + len2;
--     size_t new_sz   = sz1 + sz2 - 1;
--     object * r;
--     if (!lean_is_exclusive(s1)) {
--         r = lean_alloc_string(new_sz, mk_capacity(new_sz), new_len);
--         memcpy(w_string_cstr(r), lean_string_cstr(s1), sz1 - 1);
--         dec_ref(s1);
--     } else {
--         lean_assert(s1 != s2);
--         r = string_ensure_capacity(s1, sz2-1);
--     }
--     memcpy(w_string_cstr(r) + sz1 - 1, lean_string_cstr(s2), sz2 - 1);
--     lean_to_string(r)->m_size   = new_sz;
--     lean_to_string(r)->m_length = new_len;
--     w_string_cstr(r)[new_sz - 1] = 0;
--     return r;
-- }
-- ```
def lean_string_append := [JS_EXPR|#0 + #1]

-- ```lean
-- opaque next (s : @& String) (p : @& Pos.Raw) : Pos.Raw
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_string_utf8_next(b_obj_arg s, b_obj_arg i0) {
--     if (!lean_is_scalar(i0)) {
--         /* See comment at string_utf8_get */
--         return lean_nat_add(i0, lean_box(1));
--     }
--     usize i = lean_unbox(i0);
--     char const * str = lean_string_cstr(s);
--     usize size       = lean_string_size(s) - 1;
--     /* `c.utf8ByteSize` is 1 when `i` is not a valid position in the reference implementation. */
--     if (i >= size) return lean_usize_to_nat(i+1);
--     unsigned c = static_cast<unsigned char>(str[i]);
--     if ((c & 0x80) == 0)    return lean_box(i+1);
--     if ((c & 0xe0) == 0xc0) return lean_box(i+2);
--     if ((c & 0xf0) == 0xe0) return lean_box(i+3);
--     if ((c & 0xf8) == 0xf0) return lean_box(i+4);
--     /* invalid UTF-8 encoded string */
--     return lean_box(i+1);
-- }
-- ```
def lean_string_utf8_next := [JS_EXPR|throw new Error("lean_string_utf8_next not implemented")]

-- ```lean
-- opaque foldl (f : String → Char → String) (init : String) (s : String) : String
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_string_foldl := [JS_EXPR|throw new Error("lean_string_foldl not implemented")]

-- ```lean
-- opaque isPrefixOf (p : String) (s : String) : Bool
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_string_isprefixof := [JS_EXPR|(#1).startsWith(#0)]

-- ```lean
-- opaque any (s : String) (p : Char → Bool) : Bool
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_string_any := [JS_EXPR|throw new Error("lean_string_any not implemented")]

-- ```lean
-- opaque contains (s : String) (c : Char) : Bool
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_string_contains := [JS_EXPR|(#0).includes(#1)]

-- ```lean
-- opaque capitalize (s : String) : String
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_string_capitalize := [JS_EXPR|throw new Error("lean_string_capitalize not implemented")]

-- ```lean
-- opaque atEnd : (@& String) → (@& Pos.Raw) → Bool
-- ```
--
-- ```cpp
-- static inline uint8_t lean_string_utf8_at_end(b_lean_obj_arg s, b_lean_obj_arg i) {
--     return !lean_is_scalar(i) || lean_unbox(i) >= lean_string_size(s) - 1;
-- }
-- ```
def lean_string_utf8_at_end := [JS_EXPR|#1 >= new TextEncoder( ).encode(#0).length]

-- ```lean
-- opaque nextWhile (s : String) (p : Char → Bool) (i : String.Pos.Raw) : String.Pos.Raw
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_string_nextwhile := [JS_EXPR|throw new Error("lean_string_nextwhile not implemented")]

-- ```lean
-- opaque trim (s : String) : String
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_string_trim := [JS_EXPR|(#0).trim( )]

-- ```lean
-- opaque intercalate (s : String) : List String → String
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_string_intercalate := [JS_EXPR|(#1).join(#0)]

-- ```lean
-- opaque dropRight (s : String) (n : Nat) : String
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_string_dropright := [JS_EXPR|throw new Error("lean_string_dropright not implemented")]

-- ```lean
-- opaque getUTF8Byte (s : @& String) (n : Nat) (h : n < s.utf8ByteSize) : UInt8
-- ```
--
-- ```cpp
-- static inline uint8_t lean_string_get_byte_fast(b_lean_obj_arg s, b_lean_obj_arg i) {
--   char const * str = lean_string_cstr(s);
--   size_t idx = lean_unbox(i);
--   return str[idx];
-- }
-- ```
def lean_string_get_byte_fast := [JS_EXPR|throw new Error("lean_string_get_byte_fast not implemented")]

-- ```lean
-- opaque ugetUTF8Byte (s : @& String) (n : USize) (h : n.toNat < s.utf8ByteSize) : UInt8
-- ```
--
-- ```cpp
-- static inline uint8_t lean_string_uget_byte_fast(b_lean_obj_arg s, size_t i) {
--   return (uint8_t)lean_string_cstr(s)[i];
-- }
-- ```
def lean_string_uget_byte_fast := [JS_EXPR|throw new Error("lean_string_uget_byte_fast is not implemented")]

-- ```lean
-- def String.mk (data : List Char) : String :=
--   ⟨List.utf8Encode data,.intro data rfl⟩
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_string_mk(obj_arg cs) {
--     std::string s;
--     b_obj_arg o = cs;
--     size_t len = 0;
--     while (!lean_is_scalar(o)) {
--         push_unicode_scalar(s, lean_unbox_uint32(lean_ctor_get(o, 0)));
--         o = lean_ctor_get(o, 1);
--         len++;
--     }
--     lean_dec(cs);
--     return lean_mk_string_unchecked(s.data(), s.size(), len);
-- }
-- ```
-- duplicate of lean_string_mk:
-- def lean_string_mk := [JS_EXPR|(#0).join("")]

-- ```lean
-- opaque toString : Substring.Raw → String
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_substring_tostring := [JS_EXPR|throw new Error("lean_substring_tostring not implemented")]

-- ```lean
-- opaque drop : Substring.Raw → Nat → Substring.Raw
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_substring_drop := [JS_EXPR|throw new Error("lean_substring_drop not implemented")]

-- ```lean
-- opaque front (s : Substring.Raw) : Char
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_substring_front := [JS_EXPR|throw new Error("lean_substring_front not implemented")]

-- ```lean
-- opaque takeWhile : Substring.Raw → (Char → Bool) → Substring.Raw
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_substring_takewhile := [JS_EXPR|throw new Error("lean_substring_takewhile not implemented")]

-- ```lean
-- opaque extract : Substring.Raw → String.Pos.Raw → String.Pos.Raw → Substring.Raw
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_substring_extract := [JS_EXPR|throw new Error("lean_substring_extract not implemented")]

-- ```lean
-- opaque all (s : Substring.Raw) (p : Char → Bool) : Bool
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_substring_all := [JS_EXPR|throw new Error("lean_substring_all not implemented")]

-- ```lean
-- opaque beq (ss1 ss2 : Substring.Raw) : Bool
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_substring_beq := [JS_EXPR|throw new Error("lean_substring_beq not implemented")]

-- ```lean
-- opaque isEmpty (ss : Substring.Raw) : Bool
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_substring_isempty := [JS_EXPR|#2 == 0]

-- ```lean
-- opaque get : Substring.Raw → String.Pos.Raw → Char
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_substring_get := [JS_EXPR|throw new Error("lean_substring_get not implemented")]

-- ```lean
-- opaque prev : Substring.Raw → String.Pos.Raw → String.Pos.Raw
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_substring_prev := [JS_EXPR|throw new Error("lean_substring_prev not implemented")]

-- ```lean
-- opaque sub : String.Pos.Raw → String.Pos.Raw → String.Pos.Raw
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_string_pos_sub := [JS_EXPR|#0 - #1]

-- ```lean
-- opaque min (p₁ p₂ : Pos.Raw) : Pos.Raw
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_string_pos_min := [JS_EXPR|Math.min(#0, #1)]

-- ============
-- Init.System.Platform
-- ============

-- ```lean
-- opaque getIsWindows : Unit → Bool
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8 lean_system_platform_windows(obj_arg) {
-- #if defined(LEAN_WINDOWS)
--     return 1;
-- #else
--     return 0;
-- #endif
-- }
-- ```
def lean_system_platform_windows := [JS_EXPR|false]

-- ```lean
-- opaque getIsOSX : Unit → Bool
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8 lean_system_platform_osx(obj_arg) {
-- #if defined(__APPLE__)
--     return 1;
-- #else
--     return 0;
-- #endif
-- }
-- ```
def lean_system_platform_osx := [JS_EXPR|false]

-- ```lean
-- opaque getIsLinux : Unit → Bool
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8 lean_system_platform_linux(obj_arg) {
-- #if defined(__linux__) && !defined(LEAN_EMSCRIPTEN)
--     return 1;
-- #else
--     return 0;
-- #endif
-- }
-- ```
def lean_system_platform_linux := [JS_EXPR|throw new Error("lean_system_platform_linux is not implemented")]

-- ```lean
-- opaque getIsEmscripten : Unit → Bool
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8 lean_system_platform_emscripten(obj_arg) {
-- #if defined(LEAN_EMSCRIPTEN)
--     return 1;
-- #else
--     return 0;
-- #endif
-- }
-- ```
def lean_system_platform_emscripten := [JS_EXPR|false]

-- ```lean
-- opaque getTarget : Unit → String
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_system_platform_target(lean_obj_arg _unit) {
--     return lean_mk_string(LEAN_PLATFORM_TARGET);
-- }
-- ```
def lean_system_platform_target := [JS_EXPR|"javascript-unknown-unknown"]

-- ```lean
-- opaque Internal.getHardwareConcurrency : Unit → UInt32
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint32 lean_internal_get_hardware_concurrency(obj_arg) {
--     return hardware_concurrency();
-- }
-- ```
def lean_internal_get_hardware_concurrency := [JS_EXPR|throw new Error("lean_internal_get_hardware_concurrency is not implemented")]

-- ============
-- Init.Data.Repr
-- ============

-- ```lean
-- protected def _root_.USize.repr (n : USize) : String :=
--   String.ofList (toDigits 10 n.toNat)
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_string_of_usize(size_t n) {
--     return mk_ascii_string_unchecked(std::to_string(n));
-- }
-- ```
def lean_string_of_usize := [JS_EXPR|String(#0)]

-- ============
-- Init.Util
-- ============

-- ```lean
-- def dbgTrace {α : Type u} (s : String) (f : Unit → α) : α := f ()
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT object * lean_dbg_trace(obj_arg s, obj_arg fn) {
--     io_eprintln(s);
--     return lean_apply_1(fn, lean_box(0));
-- }
-- ```
def lean_dbg_trace := [JS_FUNC|inputs(s, f)|returns_value=f()|
  console.log(s);
]

-- ```lean
-- def dbgTraceIfShared {α : Type u} (s : @& String) (a : α) : α := a
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT object * lean_dbg_trace_if_shared(b_obj_arg s, obj_arg a) {
--     if (!lean_is_scalar(a) && !lean_is_exclusive(a)) {
--         io_eprintln(mk_string(std::string("shared RC ") + lean_string_cstr(s)));
--     }
--     return a;
-- }
-- ```
def lean_dbg_trace_if_shared := [JS_EXPR|#1]

-- ```lean
-- def dbgStackTrace {α : Type u} (f : Unit → α) : α := f ()
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT object * lean_dbg_stack_trace(obj_arg fn) {
--     print_backtrace(/* force_stderr */ false);
--     return lean_apply_1(fn, lean_box(0));
-- }
-- ```
def lean_dbg_stack_trace := [JS_EXPR|(#0)()]

-- ```lean
-- def dbgSleep {α : Type u} (ms : UInt32) (f : Unit → α) : α := f ()
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT object * lean_dbg_sleep(uint32 ms, obj_arg fn) {
--     chrono::milliseconds c(ms);
--     this_thread::sleep_for(c);
--     return lean_apply_1(fn, lean_box(0));
-- }
-- ```
def lean_dbg_sleep := [JS_EXPR|throw new Error("not implemented")]

-- ```lean
-- unsafe opaque ptrAddrUnsafe {α : Type u} (a : @& α) : USize
-- ```
--
-- ```cpp
-- static inline size_t lean_ptr_addr(b_lean_obj_arg a) { return (size_t)a; }
-- ```
def lean_ptr_addr := [JS_EXPR|throw new Error("not implemented")]

-- ```lean
-- unsafe opaque isExclusiveUnsafe {α : Type u} (a : @& α) : Bool
-- ```
--
-- ```cpp
-- static inline uint8_t lean_is_exclusive_obj(lean_object * o) {
--     return lean_is_exclusive(o);
-- }
-- ```
def lean_is_exclusive_obj := [JS_EXPR|throw new Error("not implemented")]

-- ============
-- Init.Data.Array.Basic
-- ============

-- ```lean
-- def usize (xs : @& Array α) : USize := xs.size.toUSize
-- ```
--
-- ```cpp
-- static inline size_t lean_array_size(b_lean_obj_arg o) { return lean_to_array(o)->m_size; }
-- ```
def lean_array_size := [JS_EXPR|(#0).length]

-- ```lean
-- def uget (xs : @& Array α) (i : USize) (h : i.toNat < xs.size) : α :=
--   xs[i.toNat]
-- ```
--
-- ```cpp
-- static inline lean_object * lean_array_uget(b_lean_obj_arg a, size_t i) {
--     lean_object * r = lean_array_get_core(a, i); lean_inc(r);
--     return r;
-- }
-- ```
def lean_array_uget := [JS_EXPR|#0[#1]]

-- ```lean
-- unsafe opaque ugetBorrowed (xs : @& Array α) (i : USize) (h : i.toNat < xs.size) : α :=
--   xs.uget i h
-- ```
--
-- ```cpp
-- static inline b_lean_obj_res lean_array_uget_borrowed(b_lean_obj_arg a, size_t i) {
--     return lean_array_get_core(a, i);
-- }
-- ```
def lean_array_uget_borrowed := lean_array_uget

-- ```lean
-- def uset (xs : Array α) (i : USize) (v : α) (h : i.toNat < xs.size) : Array α :=
--   xs.set i.toNat v h
-- ```
--
-- ```cpp
-- static inline lean_object * lean_array_uset(lean_obj_arg a, size_t i, lean_obj_arg v) {
--     lean_object * r   = lean_ensure_exclusive_array(a);
--     lean_object ** it = lean_array_cptr(r) + i;
--     lean_dec(*it);
--     *it = v;
--     return r;
-- }
-- ```
def lean_array_uset := [JS_FUNC|inputs(arr, idx, val)|returns=arr|
  arr[idx] = val;
]

-- ```lean
-- def pop (xs : Array α) : Array α where
--   toList := xs.toList.dropLast
-- ```
--
-- ```cpp
-- static inline lean_object * lean_array_pop(lean_obj_arg a) {
--     lean_object * r  = lean_ensure_exclusive_array(a);
--     size_t sz = lean_to_array(r)->m_size;
--     lean_object ** last;
--     if (sz == 0) return r;
--     sz--;
--     last = lean_array_cptr(r) + sz;
--     lean_to_array(r)->m_size = sz;
--     lean_dec(*last);
--     return r;
-- }
-- ```
def lean_array_pop := [JS_FUNC|inputs(arr)|returns=arr|
  arr.pop();
]

-- ```lean
-- def replicate {α : Type u} (n : Nat) (v : α) : Array α where
--   toList := List.replicate n v
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT object * lean_mk_array(obj_arg n, obj_arg v) {
--     size_t sz;
--     if (lean_is_scalar(n)) {
--         sz = lean_unbox(n);
--     } else {
--         mpz const & v = mpz_value(n);
--         if (!v.is_size_t()) lean_internal_panic_out_of_memory();
--         sz = v.get_size_t();
--         lean_dec(n);
--     }
--     object * r    = lean_alloc_array(sz, sz);
--     object ** it  = lean_array_cptr(r);
--     object ** end = it + sz;
--     for (; it != end; ++it) {
--         *it = v;
--     }
--     if (sz == 0) {
--         lean_dec(v);
--     } else if (sz > 1) {
--         lean_inc_n(v, sz - 1);
--     }
--     return r;
-- }
-- ```
def lean_mk_array := [JS_EXPR|Array.from(#0)]

-- ```lean
-- def swap (xs : Array α) (i j : @& Nat) (hi : i < xs.size := by get_elem_tactic) (hj : j < xs.size := by get_elem_tactic) : Array α :=
--   let v₁ := xs[i]
--   let v₂ := xs[j]
--   let xs'  := xs.set i v₂
--   xs'.set j v₁ (Nat.lt_of_lt_of_eq hj (size_set _).symm)
-- ```
--
-- ```cpp
-- static inline lean_object * lean_array_fswap(lean_obj_arg a, b_lean_obj_arg i, b_lean_obj_arg j) {
--     return lean_array_uswap(a, lean_unbox(i), lean_unbox(j));
-- }
-- ```
def lean_array_fswap := [JS_FUNC|inputs(arr, idx1, idx2)|returns=arr|
  const tmp = arr[idx1];
  arr[idx1] = arr[idx2];
  arr[idx2] = tmp;
]

-- ```lean
-- def swapIfInBounds (xs : Array α) (i j : @& Nat) : Array α :=
--   if h₁ : i < xs.size then
--   if h₂ : j < xs.size then swap xs i j
--   else xs
--   else xs
-- ```
--
-- ```cpp
-- static inline lean_object * lean_array_swap(lean_obj_arg a, b_lean_obj_arg i, b_lean_obj_arg j) {
--     if (!lean_is_scalar(i) || !lean_is_scalar(j)) return a;
--     size_t ui = lean_unbox(i);
--     size_t uj = lean_unbox(j);
--     size_t sz = lean_to_array(a)->m_size;
--     if (ui >= sz || uj >= sz) return a;
--     return lean_array_uswap(a, ui, uj);
-- }
-- ```
def lean_array_swap := lean_array_fswap

-- ============
-- Init.Meta.Defs
-- ============

-- ```lean
-- private opaque version.getMajor (u : Unit) : Nat
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_version_get_major(lean_obj_arg _unit) {
--     return lean_box(LEAN_VERSION_MAJOR);
-- }
-- ```
def lean_version_get_major := [JS_EXPR|4]

-- ```lean
-- private opaque version.getMinor (u : Unit) : Nat
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_version_get_minor(lean_obj_arg _unit) {
--     return lean_box(LEAN_VERSION_MINOR);
-- }
-- ```
def lean_version_get_minor := [JS_EXPR|32]

-- ```lean
-- private opaque version.getPatch (u : Unit) : Nat
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_version_get_patch(lean_obj_arg _unit) {
--     return lean_box(LEAN_VERSION_PATCH);
-- }
-- ```
def lean_version_get_patch := [JS_EXPR|0]

-- ```lean
-- opaque getGithash (u : Unit) : String
-- ```
--
-- ```cpp
-- extern "C" object * lean_get_githash(obj_arg) { return lean_mk_string(LEAN_GITHASH); }
-- ```
def lean_get_githash := [JS_EXPR|"" ]

-- ```lean
-- opaque version.getIsRelease (u : Unit) : Bool
-- ```
--
-- ```cpp
-- static inline uint8_t lean_version_get_is_release(lean_obj_arg _unit) {
--     return LEAN_VERSION_IS_RELEASE;
-- }
-- ```
def lean_version_get_is_release := [JS_EXPR|false]

-- ```lean
-- opaque version.getSpecialDesc (u : Unit) : String
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_version_get_special_desc(lean_obj_arg _unit) {
--     return lean_mk_string(LEAN_SPECIAL_VERSION_DESC);
-- }
-- ```
def lean_version_get_special_desc := [JS_EXPR|"" ]

-- ```lean
-- opaque Internal.isStage0 (u : Unit) : Bool
-- ```
--
-- ```cpp
-- static inline uint8_t lean_internal_is_stage0(lean_obj_arg _unit) {
--     return LEAN_IS_STAGE0;
-- }
-- ```
def lean_internal_is_stage0 := [JS_EXPR|false]

-- ```lean
-- opaque Internal.hasLLVMBackend (u : Unit) : Bool
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8 lean_internal_has_llvm_backend(obj_arg) {
-- #ifdef LEAN_LLVM
--     return 1;
-- #else
--     return 0;
-- #endif
-- }
-- ```
def lean_internal_has_llvm_backend := [JS_EXPR|false]

-- ============
-- Init.Data.Nat.Log2
-- ============

-- ```lean
-- def log2 (n : @& Nat) : Nat :=
--   -- Lean "assembly"
--   n.rec (fun _ => nat_lit 0) (fun _ ih n =>
--     ((nat_lit 2).ble n).rec (nat_lit 0) ((ih (n.div (nat_lit 2))).succ)) n
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT lean_obj_res lean_nat_log2(b_lean_obj_arg a) {
--     if (lean_is_scalar(a)) {
--       unsigned res = 0;
--       size_t n = lean_unbox(a);
--       while (n >= 2) {
--         res++;
--         n /= 2;
--       }
--       return lean_box(res);
--     } else {
--       return lean_box(mpz_value(a).log2());
--     }
-- }
-- ```
def lean_nat_log2 := [JS_EXPR|throw new Error("lean_nat_log2 is not implemented")]

-- ============
-- Init.Data.Nat.Gcd
-- ============

-- ```lean
-- def gcd (m n : @& Nat) : Nat :=
--   if m = 0 then
--     n
--   else
--     gcd (n % m) m
--   termination_by m
--   decreasing_by simp_wf; apply mod_lt _ (zero_lt_of_ne_zero _); assumption
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT lean_obj_res lean_nat_gcd(b_lean_obj_arg a1, b_lean_obj_arg a2) {
--     if (lean_is_scalar(a1)) {
--       if (lean_is_scalar(a2))
--         return mpz_to_nat(gcd(mpz::of_size_t(lean_unbox(a1)), mpz::of_size_t(lean_unbox(a2))));
--       else
--         return mpz_to_nat(gcd(mpz::of_size_t(lean_unbox(a1)), mpz_value(a2)));
--     } else {
--       if (lean_is_scalar(a2))
--         return mpz_to_nat(gcd(mpz_value(a1), mpz::of_size_t(lean_unbox(a2))));
--       else
--         return mpz_to_nat(gcd(mpz_value(a1), mpz_value(a2)));
--     }
-- }
-- ```
def lean_nat_gcd := [JS_FUNC|inputs(a, b)|returns=a|
  while (b != 0) {
    const t = b;
    b = a % b;
    a = t;
  }
]

-- ============
-- Init.System.ST
-- ============

-- ```lean
-- opaque Void.mk (x : σ) : Void σ
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_void_mk(lean_obj_arg a) {
--     lean_dec(a);
--     return lean_box(0);
-- }
-- ```
def lean_void_mk := [JS_EXPR|#0]

-- ```lean
-- opaque mkRef {σ α} (a : α) : ST σ (Ref σ α) := pure { ref := Classical.choice RefPointed.property, h := Nonempty.intro a }
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_st_mk_ref(obj_arg a) {
--     lean_ref_object * o = (lean_ref_object*)lean_alloc_small_object(sizeof(lean_ref_object));
--     lean_set_st_header((lean_object*)o, LeanRef, 0);
--     o->m_value = a;
--     return (lean_object*)o;
-- }
-- ```
def lean_st_mk_ref := [JS_EXPR| { value: #0 } ]

-- ```lean
-- opaque Ref.get {σ α} (r : @& Ref σ α) : ST σ α := inhabitedFromRef r
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_st_ref_get(b_obj_arg ref) {
--     if (ref_maybe_mt(ref)) {
--         atomic<object *> * val_addr = mt_ref_val_addr(ref);
--         while (true) {
--             /*
--               We cannot simply read `val` from the ref and `inc` it like in the `else` branch since someone else could
--               write to the ref in between and remove the last owning reference to the object. Instead, we must take
--               ownership of the RC token in the ref via `exchange`, duplicate it, then put one RC token back. */
--             object * val = val_addr->exchange(nullptr);
--             if (val != nullptr) {
--                 inc(val);
--                 object * tmp = val_addr->exchange(val);
--                 lean_assert(tmp == nullptr);
--                 (void)tmp;
--                 return val;
--             }
--         }
--     } else {
--         object * val = lean_to_ref(ref)->m_value;
--         lean_assert(val != nullptr);
--         inc(val);
--         return val;
--     }
-- }
-- ```
def lean_st_ref_get := [JS_EXPR| (#0).value]

-- ```lean
-- opaque Ref.swap {σ α} (r : @& Ref σ α) (a : α) : ST σ α := inhabitedFromRef r
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_st_ref_swap(b_obj_arg ref, obj_arg a) {
--     if (ref_maybe_mt(ref)) {
--         /* See io_ref_write */
--         mark_mt(a);
--         atomic<object *> * val_addr = mt_ref_val_addr(ref);
--         while (true) {
--             object * old_a = val_addr->load();
--             if (old_a != nullptr && val_addr->compare_exchange_strong(old_a, a))
--                 return old_a;
--         }
--     } else {
--         object * old_a = lean_to_ref(ref)->m_value;
--         if (old_a == nullptr)
--             lean_internal_panic("null reference read");
--         lean_to_ref(ref)->m_value = a;
--         return old_a;
--     }
-- }
-- ```
def lean_st_ref_swap := [JS_FUNC|inputs(ref, a)|returns=old|
  const old = ref.value;
  ref.value = a;
]

-- ```lean
-- unsafe opaque Ref.take {σ α} (r : @& Ref σ α) : ST σ α := inhabitedFromRef r
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_st_ref_take(b_obj_arg ref) {
--     if (ref_maybe_mt(ref)) {
--         atomic<object *> * val_addr = mt_ref_val_addr(ref);
--         while (true) {
--             object * val = val_addr->exchange(nullptr);
--             if (val != nullptr)
--                 return val;
--         }
--     } else {
--         object * val = lean_to_ref(ref)->m_value;
--         lean_assert(val != nullptr);
--         lean_to_ref(ref)->m_value = nullptr;
--         return val;
--     }
-- }
-- ```
def lean_st_ref_take := [JS_FUNC|inputs(ref)|returns=old|
  const old = ref.value;
  ref.value = undefined;
]

-- ```lean
-- unsafe opaque Ref.put {σ α} (r : @& Ref σ α) (a : α) : ST σ Unit
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_st_ref_put(b_obj_arg ref, obj_arg a) {
--     if (ref_maybe_mt(ref)) {
--         /* We must mark `a` as multi-threaded if `ref` is marked as multi-threaded.
--            Reason: our runtime relies on the fact that a single-threaded object
--            cannot be reached from a multi-thread object. */
--         mark_mt(a);
--         atomic<object *> * val_addr = mt_ref_val_addr(ref);
--         object * old_a = val_addr->exchange(a);
--         lean_assert(old_a == nullptr);
--         (void)old_a;
--         return box(0);
--     } else {
--         if (lean_to_ref(ref)->m_value != nullptr)
--             dec(lean_to_ref(ref)->m_value);
--         lean_to_ref(ref)->m_value = a;
--         return box(0);
--     }
-- }
-- ```
def lean_st_ref_put := [JS_EXPR|throw new Error("lean_st_ref_put is not implemented")]

-- ```lean
-- opaque Ref.ptrEq {σ α} (r1 r2 : @& Ref σ α) : ST σ Bool
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8_t lean_st_ref_ptr_eq(b_obj_arg ref1, b_obj_arg ref2) {
--     return lean_to_ref(ref1) == lean_to_ref(ref2);
-- }
-- ```
def lean_st_ref_ptr_eq := [JS_EXPR|#0 === #1]

-- ============
-- Init.Data.UInt.Log2
-- ============

-- ```lean
-- def UInt8.log2 (a : UInt8) : UInt8 := ⟨⟨Fin.log2 a.toFin⟩⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint8_log2(uint8_t a) {
--     uint8_t res = 0;
--     while (a >= 2) {
--         res++;
--         a /= 2;
--     }
--     return res;
-- }
-- ```
def lean_uint8_log2 := [JS_EXPR|Math.clz32(1) - Math.clz32(#0)]

-- ```lean
-- def UInt16.log2 (a : UInt16) : UInt16 := ⟨⟨Fin.log2 a.toFin⟩⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_uint16_log2(uint16_t a) {
--     uint16_t res = 0;
--     while (a >= 2) {
--         res++;
--         a /= 2;
--     }
--     return res;
-- }
-- ```
def lean_uint16_log2 := [JS_EXPR|Math.clz32(1) - Math.clz32(#0)]

-- ```lean
-- def UInt32.log2 (a : UInt32) : UInt32 := ⟨⟨Fin.log2 a.toFin⟩⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_uint32_log2(uint32_t a) {
--     uint32_t res = 0;
--     while (a >= 2) {
--         res++;
--         a /= 2;
--     }
--     return res;
-- }
-- ```
def lean_uint32_log2 := [JS_EXPR|Math.clz32(1) - Math.clz32(#0)]

-- ```lean
-- def UInt64.log2 (a : UInt64) : UInt64 := ⟨⟨Fin.log2 a.toFin⟩⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_uint64_log2(uint64_t a) {
--     uint64_t res = 0;
--     while (a >= 2) {
--         res++;
--         a /= 2;
--     }
--     return res;
-- }
-- ```
def lean_uint64_log2 := [JS_EXPR|Math.clz32(1) - Math.clz32(#0)]

-- ```lean
-- def USize.log2 (a : USize) : USize := ⟨⟨Fin.log2 a.toFin⟩⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_usize_log2(size_t a) {
--     size_t res = 0;
--     while (a >= 2) {
--         res++;
--         a /= 2;
--     }
--     return res;
-- }
-- ```
def lean_usize_log2 := [JS_EXPR|Math.clz32(1) - Math.clz32(#0)]

-- ============
-- Init.Data.UInt.Basic
-- ============

-- ```lean
-- protected def UInt8.add (a b : UInt8) : UInt8 := ⟨a.toBitVec + b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint8_add(uint8_t a1, uint8_t a2) { return a1+a2; }
-- ```
def lean_uint8_add := [JS_EXPR|(#0 + #1) & 0xFF]

-- ```lean
-- protected def UInt8.sub (a b : UInt8) : UInt8 := ⟨a.toBitVec - b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint8_sub(uint8_t a1, uint8_t a2) { return a1-a2; }
-- ```
def lean_uint8_sub := [JS_EXPR|(#0 - #1) & 0xFF]

-- ```lean
-- protected def UInt8.mul (a b : UInt8) : UInt8 := ⟨a.toBitVec * b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint8_mul(uint8_t a1, uint8_t a2) { return 1U*a1*a2; }
-- ```
def lean_uint8_mul := [JS_EXPR|(#0 * #1) & 0xFF]

-- ```lean
-- protected def UInt8.div (a b : UInt8) : UInt8 := ⟨BitVec.udiv a.toBitVec b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint8_div(uint8_t a1, uint8_t a2) { return a2 == 0 ? 0  : a1/a2; }
-- ```
def lean_uint8_div := [JS_EXPR|#0 / #1]

-- ```lean
-- protected def UInt8.mod (a b : UInt8) : UInt8 := ⟨BitVec.umod a.toBitVec b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint8_mod(uint8_t a1, uint8_t a2) { return a2 == 0 ? a1 : a1%a2; }
-- ```
def lean_uint8_mod := [JS_EXPR|#0 % #1]

-- ```lean
-- protected def UInt8.land (a b : UInt8) : UInt8 := ⟨a.toBitVec &&& b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint8_land(uint8_t a, uint8_t b) { return a & b; }
-- ```
def lean_uint8_land := [JS_EXPR|#0 & #1]

-- ```lean
-- protected def UInt8.lor (a b : UInt8) : UInt8 := ⟨a.toBitVec ||| b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint8_lor(uint8_t a, uint8_t b) { return a | b; }
-- ```
def lean_uint8_lor := [JS_EXPR|#0 | #1]

-- ```lean
-- protected def UInt8.xor (a b : UInt8) : UInt8 := ⟨a.toBitVec ^^^ b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint8_xor(uint8_t a, uint8_t b) { return a ^ b; }
-- ```
def lean_uint8_xor := [JS_EXPR|#0 ^ #1]

-- ```lean
-- protected def UInt8.shiftLeft (a b : UInt8) : UInt8 := ⟨a.toBitVec <<< (UInt8.mod b 8).toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint8_shift_left(uint8_t a, uint8_t b) { return a << (b % 8); }
-- ```
def lean_uint8_shift_left := [JS_EXPR|(#0 << #1) & 0xFF]

-- ```lean
-- protected def UInt8.shiftRight (a b : UInt8) : UInt8 := ⟨a.toBitVec >>> (UInt8.mod b 8).toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint8_shift_right(uint8_t a, uint8_t b) { return a >> (b % 8); }
-- ```
def lean_uint8_shift_right := [JS_EXPR|#0 >> #1]

-- ```lean
-- protected def UInt8.complement (a : UInt8) : UInt8 := ⟨~~~a.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint8_complement(uint8_t a) { return ~a; }
-- ```
def lean_uint8_complement := [JS_EXPR|(~#0) & 0xFF]

-- ```lean
-- protected def UInt8.neg (a : UInt8) : UInt8 := ⟨-a.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint8_neg(uint8_t a) { return -a; }
-- ```
def lean_uint8_neg := [JS_EXPR|(0 - #0) & 0xFF]

-- ```lean
-- def Bool.toUInt8 (b : Bool) : UInt8 := if b then 1 else 0
-- ```
--
-- ```cpp
-- static inline uint8_t lean_bool_to_uint8(uint8_t a) { return a; }
-- ```
def lean_bool_to_uint8 := [JS_EXPR|#0 ? 1 : 0]

-- ```lean
-- protected def UInt16.add (a b : UInt16) : UInt16 := ⟨a.toBitVec + b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_uint16_add(uint16_t a1, uint16_t a2) { return a1+a2; }
-- ```
def lean_uint16_add := [JS_EXPR|(#0 + #1) & 0xFFFF]

-- ```lean
-- protected def UInt16.sub (a b : UInt16) : UInt16 := ⟨a.toBitVec - b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_uint16_sub(uint16_t a1, uint16_t a2) { return a1-a2; }
-- ```
def lean_uint16_sub := [JS_EXPR|(#0 - #1) & 0xFFFF]

-- ```lean
-- protected def UInt16.mul (a b : UInt16) : UInt16 := ⟨a.toBitVec * b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_uint16_mul(uint16_t a1, uint16_t a2) { return 1U*a1*a2; }
-- ```
def lean_uint16_mul := [JS_EXPR|(#0 * #1) & 0xFFFF]

-- ```lean
-- protected def UInt16.div (a b : UInt16) : UInt16 := ⟨BitVec.udiv a.toBitVec b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_uint16_div(uint16_t a1, uint16_t a2) { return a2 == 0 ? 0  : a1/a2; }
-- ```
def lean_uint16_div := [JS_EXPR|#0 / #1]

-- ```lean
-- protected def UInt16.mod (a b : UInt16) : UInt16 := ⟨BitVec.umod a.toBitVec b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_uint16_mod(uint16_t a1, uint16_t a2) { return a2 == 0 ? a1 : a1%a2; }
-- ```
def lean_uint16_mod := [JS_EXPR|#0 % #1]

-- ```lean
-- protected def UInt16.land (a b : UInt16) : UInt16 := ⟨a.toBitVec &&& b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_uint16_land(uint16_t a, uint16_t b) { return a & b; }
-- ```
def lean_uint16_land := [JS_EXPR|#0 & #1]

-- ```lean
-- protected def UInt16.lor (a b : UInt16) : UInt16 := ⟨a.toBitVec ||| b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_uint16_lor(uint16_t a, uint16_t b) { return a | b; }
-- ```
def lean_uint16_lor := [JS_EXPR|#0 | #1]

-- ```lean
-- protected def UInt16.xor (a b : UInt16) : UInt16 := ⟨a.toBitVec ^^^ b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_uint16_xor(uint16_t a, uint16_t b) { return a ^ b; }
-- ```
def lean_uint16_xor := [JS_EXPR|#0 ^ #1]

-- ```lean
-- protected def UInt16.shiftLeft (a b : UInt16) : UInt16 := ⟨a.toBitVec <<< (UInt16.mod b 16).toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_uint16_shift_left(uint16_t a, uint16_t b) { return a << (b % 16); }
-- ```
def lean_uint16_shift_left := [JS_EXPR|(#0 << #1) & 0xFFFF]

-- ```lean
-- protected def UInt16.shiftRight (a b : UInt16) : UInt16 := ⟨a.toBitVec >>> (UInt16.mod b 16).toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_uint16_shift_right(uint16_t a, uint16_t b) { return a >> (b % 16); }
-- ```
def lean_uint16_shift_right := [JS_EXPR|#0 >> #1]

-- ```lean
-- protected def UInt16.complement (a : UInt16) : UInt16 := ⟨~~~a.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_uint16_complement(uint16_t a) { return ~a; }
-- ```
def lean_uint16_complement := [JS_EXPR|(~#0) & 0xFFFF]

-- ```lean
-- protected def UInt16.neg (a : UInt16) : UInt16 := ⟨-a.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_uint16_neg(uint16_t a) { return -a; }
-- ```
def lean_uint16_neg := [JS_EXPR|(0 - #0) & 0xFFFF]

-- ```lean
-- def Bool.toUInt16 (b : Bool) : UInt16 := if b then 1 else 0
-- ```
--
-- ```cpp
-- static inline uint16_t lean_bool_to_uint16(uint8_t a) { return (uint16_t)a; }
-- ```
def lean_bool_to_uint16 := [JS_EXPR|throw new Error("lean_bool_to_uint16 not implemented")]

-- ```lean
-- def UInt16.decLt (a b : UInt16) : Decidable (a < b) :=
--   inferInstanceAs (Decidable (a.toBitVec < b.toBitVec))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint16_dec_lt(uint16_t a1, uint16_t a2) { return a1 < a2; }
-- ```
def lean_uint16_dec_lt := [JS_EXPR|throw new Error("lean_uint16_dec_lt not implemented")]

-- ```lean
-- def UInt16.decLe (a b : UInt16) : Decidable (a ≤ b) :=
--   inferInstanceAs (Decidable (a.toBitVec ≤ b.toBitVec))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint16_dec_le(uint16_t a1, uint16_t a2) { return a1 <= a2; }
-- ```
def lean_uint16_dec_le := [JS_EXPR|throw new Error("lean_uint16_dec_le not implemented")]

-- ```lean
-- protected def UInt32.mul (a b : UInt32) : UInt32 := ⟨a.toBitVec * b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_uint32_mul(uint32_t a1, uint32_t a2) { return 1U*a1*a2; }
-- ```
def lean_uint32_mul := [JS_EXPR|Math.imul(toUInt32(#0), toUInt32(#1)) >>> 0]

-- ```lean
-- protected def UInt32.div (a b : UInt32) : UInt32 := ⟨BitVec.udiv a.toBitVec b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_uint32_div(uint32_t a1, uint32_t a2) { return a2 == 0 ? 0  : a1/a2; }
-- ```
def lean_uint32_div := [JS_EXPR|throw new Error("lean_uint32_div not implemented")]

-- ```lean
-- protected def UInt32.mod (a b : UInt32) : UInt32 := ⟨BitVec.umod a.toBitVec b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_uint32_mod(uint32_t a1, uint32_t a2) { return a2 == 0 ? a1 : a1%a2; }
-- ```
def lean_uint32_mod := [JS_EXPR|throw new Error("lean_uint32_mod not implemented")]

-- ```lean
-- protected def UInt32.land (a b : UInt32) : UInt32 := ⟨a.toBitVec &&& b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_uint32_land(uint32_t a, uint32_t b) { return a & b; }
-- ```
def lean_uint32_land := [JS_EXPR|(toUInt32(#0) & toUInt32(#1)) >>> 0]

-- ```lean
-- protected def UInt32.lor (a b : UInt32) : UInt32 := ⟨a.toBitVec ||| b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_uint32_lor(uint32_t a, uint32_t b) { return a | b; }
-- ```
def lean_uint32_lor := [JS_EXPR|(toUInt32(#0) | toUInt32(#1)) >>> 0]

-- ```lean
-- protected def UInt32.xor (a b : UInt32) : UInt32 := ⟨a.toBitVec ^^^ b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_uint32_xor(uint32_t a, uint32_t b) { return a ^ b; }
-- ```
def lean_uint32_xor := [JS_EXPR|(toUInt32(#0) ^ toUInt32(#1)) >>> 0]

-- ```lean
-- protected def UInt32.shiftLeft (a b : UInt32) : UInt32 := ⟨a.toBitVec <<< (UInt32.mod b 32).toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_uint32_shift_left(uint32_t a, uint32_t b) { return a << (b % 32); }
-- ```
def lean_uint32_shift_left := [JS_EXPR|(toUInt32(#0) << (toUInt32(#1) & 31)) >>> 0]

-- ```lean
-- protected def UInt32.shiftRight (a b : UInt32) : UInt32 := ⟨a.toBitVec >>> (UInt32.mod b 32).toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_uint32_shift_right(uint32_t a, uint32_t b) { return a >> (b % 32); }
-- ```
def lean_uint32_shift_right := [JS_EXPR|toUInt32(#0) >>> (toUInt32(#1) & 31)]

-- ```lean
-- protected def UInt32.complement (a : UInt32) : UInt32 := ⟨~~~a.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_uint32_complement(uint32_t a) { return ~a; }
-- ```
def lean_uint32_complement := [JS_EXPR|(~toUInt32(#0)) >>> 0]

-- ```lean
-- protected def UInt32.neg (a : UInt32) : UInt32 := ⟨-a.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_uint32_neg(uint32_t a) { return -a; }
-- ```
def lean_uint32_neg := [JS_EXPR|(-toUInt32(#0)) >>> 0]

-- ```lean
-- def Bool.toUInt32 (b : Bool) : UInt32 := if b then 1 else 0
-- ```
--
-- ```cpp
-- static inline uint32_t lean_bool_to_uint32(uint8_t a) { return (uint32_t)a; }
-- ```
def lean_bool_to_uint32 := [JS_EXPR|#0 ? 1 : 0]

-- ```lean
-- protected def UInt64.add (a b : UInt64) : UInt64 := ⟨a.toBitVec + b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_uint64_add(uint64_t a1, uint64_t a2) { return a1+a2; }
-- ```
def lean_uint64_add := [JS_EXPR|throw new Error("lean_uint64_add not implemented")]

-- ```lean
-- protected def UInt64.sub (a b : UInt64) : UInt64 := ⟨a.toBitVec - b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_uint64_sub(uint64_t a1, uint64_t a2) { return a1-a2; }
-- ```
def lean_uint64_sub := [JS_EXPR|throw new Error("lean_uint64_sub not implemented")]

-- ```lean
-- protected def UInt64.mul (a b : UInt64) : UInt64 := ⟨a.toBitVec * b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_uint64_mul(uint64_t a1, uint64_t a2) { return 1U*a1*a2; }
-- ```
def lean_uint64_mul := [JS_EXPR|throw new Error("lean_uint64_mul not implemented")]

-- ```lean
-- protected def UInt64.div (a b : UInt64) : UInt64 := ⟨BitVec.udiv a.toBitVec b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_uint64_div(uint64_t a1, uint64_t a2) { return a2 == 0 ? 0  : a1/a2; }
-- ```
def lean_uint64_div := [JS_EXPR|throw new Error("lean_uint64_div not implemented")]

-- ```lean
-- protected def UInt64.mod (a b : UInt64) : UInt64 := ⟨BitVec.umod a.toBitVec b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_uint64_mod(uint64_t a1, uint64_t a2) { return a2 == 0 ? a1 : a1%a2; }
-- ```
def lean_uint64_mod := [JS_EXPR|throw new Error("lean_uint64_mod not implemented")]

-- ```lean
-- protected def UInt64.land (a b : UInt64) : UInt64 := ⟨a.toBitVec &&& b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_uint64_land(uint64_t a, uint64_t b) { return a & b; }
-- ```
def lean_uint64_land := [JS_EXPR|throw new Error("lean_uint64_land not implemented")]

-- ```lean
-- protected def UInt64.lor (a b : UInt64) : UInt64 := ⟨a.toBitVec ||| b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_uint64_lor(uint64_t a, uint64_t b) { return a | b; }
-- ```
def lean_uint64_lor := [JS_EXPR|throw new Error("lean_uint64_lor not implemented")]

-- ```lean
-- protected def UInt64.xor (a b : UInt64) : UInt64 := ⟨a.toBitVec ^^^ b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_uint64_xor(uint64_t a, uint64_t b) { return a ^ b; }
-- ```
def lean_uint64_xor := [JS_EXPR|throw new Error("lean_uint64_xor not implemented")]

-- ```lean
-- protected def UInt64.shiftLeft (a b : UInt64) : UInt64 := ⟨a.toBitVec <<< (UInt64.mod b 64).toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_uint64_shift_left(uint64_t a, uint64_t b) { return a << (b % 64); }
-- ```
def lean_uint64_shift_left := [JS_EXPR|throw new Error("lean_uint64_shift_left not implemented")]

-- ```lean
-- protected def UInt64.shiftRight (a b : UInt64) : UInt64 := ⟨a.toBitVec >>> (UInt64.mod b 64).toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_uint64_shift_right(uint64_t a, uint64_t b) { return a >> (b % 64); }
-- ```
def lean_uint64_shift_right := [JS_EXPR|throw new Error("lean_uint64_shift_right not implemented")]

-- ```lean
-- protected def UInt64.complement (a : UInt64) : UInt64 := ⟨~~~a.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_uint64_complement(uint64_t a) { return ~a; }
-- ```
def lean_uint64_complement := [JS_EXPR|throw new Error("lean_uint64_complement not implemented")]

-- ```lean
-- protected def UInt64.neg (a : UInt64) : UInt64 := ⟨-a.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_uint64_neg(uint64_t a) { return -a; }
-- ```
def lean_uint64_neg := [JS_EXPR|throw new Error("lean_uint64_neg not implemented")]

-- ```lean
-- def Bool.toUInt64 (b : Bool) : UInt64 := if b then 1 else 0
-- ```
--
-- ```cpp
-- static inline uint64_t lean_bool_to_uint64(uint8_t a) { return (uint64_t)a; }
-- ```
def lean_bool_to_uint64 := [JS_EXPR|throw new Error("lean_bool_to_uint64 not implemented")]

-- ```lean
-- def UInt64.decLt (a b : UInt64) : Decidable (a < b) :=
--   inferInstanceAs (Decidable (a.toBitVec < b.toBitVec))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint64_dec_lt(uint64_t a1, uint64_t a2) { return a1 < a2; }
-- ```
def lean_uint64_dec_lt := [JS_EXPR|throw new Error("lean_uint64_dec_lt not implemented")]

-- ```lean
-- def UInt64.decLe (a b : UInt64) : Decidable (a ≤ b) :=
--   inferInstanceAs (Decidable (a.toBitVec ≤ b.toBitVec))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_uint64_dec_le(uint64_t a1, uint64_t a2) { return a1 <= a2; }
-- ```
def lean_uint64_dec_le := [JS_EXPR|throw new Error("lean_uint64_dec_le not implemented")]

-- ```lean
-- protected def USize.mul (a b : USize) : USize := ⟨a.toBitVec * b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_usize_mul(size_t a1, size_t a2) { return a1*a2; }
-- ```
def lean_usize_mul := [JS_EXPR|throw new Error("lean_usize_mul not implemented")]

-- ```lean
-- protected def USize.div (a b : USize) : USize := ⟨a.toBitVec / b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_usize_div(size_t a1, size_t a2) { return a2 == 0 ? 0  : a1/a2; }
-- ```
def lean_usize_div := [JS_EXPR|throw new Error("lean_usize_div not implemented")]

-- ```lean
-- protected def USize.mod (a b : USize) : USize := ⟨a.toBitVec % b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_usize_mod(size_t a1, size_t a2) { return a2 == 0 ? a1 : a1%a2; }
-- ```
def lean_usize_mod := [JS_EXPR|throw new Error("lean_usize_mod not implemented")]

-- ```lean
-- protected def USize.land (a b : USize) : USize := ⟨a.toBitVec &&& b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_usize_land(size_t a, size_t b) { return a & b; }
-- ```
def lean_usize_land := [JS_EXPR|throw new Error("lean_usize_land not implemented")]

-- ```lean
-- protected def USize.lor (a b : USize) : USize := ⟨a.toBitVec ||| b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_usize_lor(size_t a, size_t b) { return a | b; }
-- ```
def lean_usize_lor := [JS_EXPR|throw new Error("lean_usize_lor not implemented")]

-- ```lean
-- protected def USize.xor (a b : USize) : USize := ⟨a.toBitVec ^^^ b.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_usize_xor(size_t a, size_t b) { return a ^ b; }
-- ```
def lean_usize_xor := [JS_EXPR|throw new Error("lean_usize_xor not implemented")]

-- ```lean
-- protected def USize.shiftLeft (a b : USize) : USize := ⟨a.toBitVec <<< (USize.mod b (USize.ofNat System.Platform.numBits)).toBitVec⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_usize_shift_left(size_t a, size_t b) { return a << (b %  (sizeof(size_t) * 8)); }
-- ```
def lean_usize_shift_left := [JS_EXPR|throw new Error("lean_usize_shift_left not implemented")]

-- ```lean
-- protected def USize.shiftRight (a b : USize) : USize := ⟨a.toBitVec >>> (USize.mod b (USize.ofNat System.Platform.numBits)).toBitVec⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_usize_shift_right(size_t a, size_t b) { return a >> (b % (sizeof(size_t) * 8)); }
-- ```
def lean_usize_shift_right := [JS_EXPR|throw new Error("lean_usize_shift_right not implemented")]

-- ```lean
-- def USize.ofNat32 (n : @& Nat) (h : n < 4294967296) : USize :=
--   USize.ofNatLT n (Nat.lt_of_lt_of_le h USize.le_size)
-- ```
--
-- ```cpp
-- static inline size_t lean_usize_of_nat(b_lean_obj_arg a) { return lean_is_scalar(a) ? lean_unbox(a) : lean_usize_of_big_nat(a); }
-- ```
-- duplicate of lean_usize_of_nat:
-- def lean_usize_of_nat := [JS_EXPR|throw new Error("lean_usize_of_nat not implemented")]

-- ```lean
-- def UInt8.toUSize (a : UInt8) : USize :=
--   USize.ofNat32 a.toBitVec.toNat (Nat.lt_trans a.toBitVec.isLt (by decide))
-- ```
--
-- ```cpp
-- static inline size_t lean_uint8_to_usize(uint8_t a) { return ((size_t)a); }
-- ```
def lean_uint8_to_usize := [JS_EXPR|throw new Error("lean_uint8_to_usize not implemented")]

-- ```lean
-- def USize.toUInt8 (a : USize) : UInt8 := a.toNat.toUInt8
-- ```
--
-- ```cpp
-- static inline uint8_t lean_usize_to_uint8(size_t a) { return ((uint8_t)a); }
-- ```
def lean_usize_to_uint8 := [JS_EXPR|throw new Error("lean_usize_to_uint8 not implemented")]

-- ```lean
-- def UInt16.toUSize (a : UInt16) : USize :=
--   USize.ofNat32 a.toBitVec.toNat (Nat.lt_trans a.toBitVec.isLt (by decide))
-- ```
--
-- ```cpp
-- static inline size_t lean_uint16_to_usize(uint16_t a) { return ((size_t)a); }
-- ```
def lean_uint16_to_usize := [JS_EXPR|throw new Error("lean_uint16_to_usize not implemented")]

-- ```lean
-- def USize.toUInt16 (a : USize) : UInt16 := a.toNat.toUInt16
-- ```
--
-- ```cpp
-- static inline uint16_t lean_usize_to_uint16(size_t a) { return ((uint16_t)a); }
-- ```
def lean_usize_to_uint16 := [JS_EXPR|throw new Error("lean_usize_to_uint16 not implemented")]

-- ```lean
-- def UInt32.toUSize (a : UInt32) : USize := USize.ofNat32 a.toBitVec.toNat a.toBitVec.isLt
-- ```
--
-- ```cpp
-- static inline size_t lean_uint32_to_usize(uint32_t a) { return ((size_t)a); }
-- ```
def lean_uint32_to_usize := [JS_EXPR|throw new Error("lean_uint32_to_usize not implemented")]

-- ```lean
-- def USize.toUInt32 (a : USize) : UInt32 := a.toNat.toUInt32
-- ```
--
-- ```cpp
-- static inline uint32_t lean_usize_to_uint32(size_t a) { return ((uint32_t)a); }
-- ```
def lean_usize_to_uint32 := [JS_EXPR|throw new Error("lean_usize_to_uint32 not implemented")]

-- ```lean
-- def UInt64.toUSize (a : UInt64) : USize := a.toNat.toUSize
-- ```
--
-- ```cpp
-- static inline size_t lean_uint64_to_usize(uint64_t a) { return ((size_t)a); }
-- ```
def lean_uint64_to_usize := [JS_EXPR|throw new Error("lean_uint64_to_usize not implemented")]

-- ```lean
-- def USize.toUInt64 (a : USize) : UInt64 :=
--   UInt64.ofNatLT a.toBitVec.toNat (Nat.lt_of_lt_of_le a.toBitVec.isLt USize.size_le)
-- ```
--
-- ```cpp
-- static inline uint64_t lean_usize_to_uint64(size_t a) { return ((uint64_t)a); }
-- ```
def lean_usize_to_uint64 := [JS_EXPR|throw new Error("lean_usize_to_uint64 not implemented")]

-- ```lean
-- protected def USize.complement (a : USize) : USize := ⟨~~~a.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_usize_complement(size_t a) { return ~a; }
-- ```
def lean_usize_complement := [JS_EXPR|throw new Error("lean_usize_complement not implemented")]

-- ```lean
-- protected def USize.neg (a : USize) : USize := ⟨-a.toBitVec⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_usize_neg(size_t a) { return -a; }
-- ```
def lean_usize_neg := [JS_EXPR|throw new Error("lean_usize_neg not implemented")]

-- ```lean
-- def Bool.toUSize (b : Bool) : USize := if b then 1 else 0
-- ```
--
-- ```cpp
-- static inline size_t lean_bool_to_usize(uint8_t a) { return (size_t)a; }
-- ```
def lean_bool_to_usize := [JS_EXPR|throw new Error("lean_bool_to_usize not implemented")]

-- ============
-- Init.Data.ByteArray.Basic
-- ============

-- ```lean
-- def beq (lhs rhs : @& ByteArray) : Bool :=
--   lhs.data == rhs.data
-- ```
--
-- ```cpp
-- static inline uint8_t lean_sarray_dec_eq(b_lean_obj_arg a1, b_lean_obj_arg a2) { return lean_sarray_eq(a1, a2); }
-- ```
--
-- ```lean
-- def decEq (lhs rhs : @& ByteArray) : Decidable (lhs = rhs) :=
--   decidable_of_decidable_of_iff ByteArray.ext_iff.symm
-- ```
--
-- ```cpp
-- static inline uint8_t lean_sarray_dec_eq(b_lean_obj_arg a1, b_lean_obj_arg a2) { return lean_sarray_eq(a1, a2); }
-- ```
def lean_sarray_dec_eq := [JS_EXPR| #0 == #1 ]

-- ```lean
-- def usize (a : @& ByteArray) : USize :=
--   a.size.toUSize
-- ```
--
-- ```cpp
-- static inline size_t lean_sarray_size(b_lean_obj_arg o) { return lean_to_sarray(o)->m_size; }
-- ```
def lean_sarray_size := [JS_EXPR| (#0).length]

-- ```lean
-- def uget : (a : @& ByteArray) → (i : USize) → (h : i.toNat < a.size := by get_elem_tactic) → UInt8
--   | ⟨bs⟩, i, h => bs[i]
-- ```
--
-- ```cpp
-- static inline uint8_t lean_byte_array_uget(b_lean_obj_arg a, size_t i) {
--     assert(i < lean_sarray_size(a));
--     return lean_sarray_cptr(a)[i];
-- }
-- ```
def lean_byte_array_uget := [JS_EXPR| #0[#1]]

-- ```lean
-- def get : (a : @& ByteArray) → (i : @& Nat) → (h : i < a.size := by get_elem_tactic) → UInt8
--   | ⟨bs⟩, i, _ => bs[i]
-- ```
--
-- ```cpp
-- static inline uint8_t lean_byte_array_fget(b_lean_obj_arg a, b_lean_obj_arg i) {
--     return lean_byte_array_uget(a, lean_unbox(i));
-- }
-- ```
def lean_byte_array_fget := lean_byte_array_uget

-- ```lean
-- def set : (a : ByteArray) → (i : @& Nat) → UInt8 → (h : i < a.size := by get_elem_tactic) → ByteArray
--   | ⟨bs⟩, i, b, h => ⟨bs.set i b h⟩
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_byte_array_fset(lean_obj_arg a, b_lean_obj_arg i, uint8_t b) {
--     return lean_byte_array_uset(a, lean_unbox(i), b);
-- }
-- ```
def lean_byte_array_fset := lean_byte_array_set

-- ```lean
-- def uset : (a : ByteArray) → (i : USize) → UInt8 → (h : i.toNat < a.size := by get_elem_tactic) → ByteArray
--   | ⟨bs⟩, i, v, h => ⟨bs.uset i v h⟩
-- ```
--
-- ```cpp
-- static inline lean_object * lean_byte_array_uset(lean_obj_arg a, size_t i, uint8_t v) {
--     lean_obj_res r;
--     if (lean_is_exclusive(a)) r = a;
--     else r = lean_copy_byte_array(a);
--     uint8_t * it = lean_sarray_cptr(r) + i;
--     *it = v;
--     return r;
-- }
-- ```
def lean_byte_array_uset := lean_byte_array_set

-- ```lean
-- protected opaque hash (a : @& ByteArray) : UInt64
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint64_t lean_byte_array_hash(b_obj_arg a) {
--     return hash_str(lean_sarray_size(a), lean_sarray_cptr(a), 11);
-- }
-- ```
def lean_byte_array_hash := [JS_EXPR| 0 ]

-- ```lean
-- def copySlice (src : @& ByteArray) (srcOff : Nat) (dest : ByteArray) (destOff len : Nat) (exact : Bool := true) : ByteArray :=
--   ⟨dest.data.extract 0 destOff ++ src.data.extract srcOff (srcOff + len) ++ dest.data.extract (destOff + min len (src.data.size - srcOff)) dest.data.size⟩
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_byte_array_copy_slice(b_obj_arg src, obj_arg o_src_off, obj_arg dest, obj_arg o_dest_off, obj_arg o_len, bool exact) {
--     size_t ssz = lean_sarray_size(src);
--     size_t dsz = lean_sarray_size(dest);
--     size_t src_off = lean_nat_to_size_t(o_src_off);
--     if (src_off > ssz) {
--         return dest;
--     }
--     size_t len = std::min(lean_nat_to_size_t(o_len), ssz - src_off);
--     size_t dest_off = lean_nat_to_size_t(o_dest_off);
--     if (dest_off > dsz) {
--         dest_off = dsz;
--     }
--     size_t new_dsz = std::max(dsz, dest_off + len);
--     object * r = lean_sarray_ensure_exclusive(lean_sarray_ensure_capacity(dest, new_dsz, exact));
--     lean_to_sarray(r)->m_size = new_dsz;
--     // `r` is exclusive, so the ranges definitely cannot overlap
--     memcpy(lean_sarray_cptr(r) + dest_off, lean_sarray_cptr(src) + src_off, len);
--     return r;
-- }
-- ```
def lean_byte_array_copy_slice := [JS_FUNC|inputs(dst, dstOff, src, srcOff, len)|returns=dst|
  dst.set(src.subarray(srcOff, srcOff + len), dstOff);
]

-- ============
-- Init.Data.String.PosRaw
-- ============

-- ```lean
-- def getUTF8Byte (s : @& String) (p : Pos.Raw) (h : p < s.rawEndPos) : UInt8 :=
--   s.toByteArray[p.byteIdx]
-- ```
--
-- ```cpp
-- static inline uint8_t lean_string_get_byte_fast(b_lean_obj_arg s, b_lean_obj_arg i) {
--   char const * str = lean_string_cstr(s);
--   size_t idx = lean_unbox(i);
--   return str[idx];
-- }
-- ```
--
-- ```lean
-- abbrev getUtf8Byte (s : String) (p : Pos.Raw) (h : p < s.rawEndPos) : UInt8 :=
--   s.getUTF8Byte p h
-- ```
--
-- ```cpp
-- static inline uint8_t lean_string_get_byte_fast(b_lean_obj_arg s, b_lean_obj_arg i) {
--   char const * str = lean_string_cstr(s);
--   size_t idx = lean_unbox(i);
--   return str[idx];
-- }
-- ```
-- duplicate of lean_string_get_byte_fast:
-- def lean_string_get_byte_fast := [JS_EXPR|new TextEncoder( ).encode(#0)[#1]]

-- ============
-- Init.Data.String.Defs
-- ============

-- ```lean
-- def String.toUTF8 (a : @& String) : ByteArray :=
--   a.toByteArray
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_string_to_utf8(b_obj_arg s) {
--     size_t sz = lean_string_size(s) - 1;
--     obj_res r = lean_alloc_sarray(1, sz, sz);
--     memcpy(lean_sarray_cptr(r), lean_string_cstr(s), sz);
--     return r;
-- }
-- ```
-- duplicate of lean_string_to_utf8:
-- def lean_string_to_utf8 := [JS_EXPR|encoder.encode(#0)]

-- ```lean
-- def String.append (s : String) (t : @& String) : String where
--   toByteArray := s.toByteArray ++ t.toByteArray
--   isValidUTF8 := s.isValidUTF8.append t.isValidUTF8
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT object * lean_string_append(object * s1, object * s2) {
--     size_t sz1      = lean_string_size(s1);
--     size_t sz2      = lean_string_size(s2);
--     size_t len1     = lean_string_len(s1);
--     size_t len2     = lean_string_len(s2);
--     size_t new_len  = len1 + len2;
--     size_t new_sz   = sz1 + sz2 - 1;
--     object * r;
--     if (!lean_is_exclusive(s1)) {
--         r = lean_alloc_string(new_sz, mk_capacity(new_sz), new_len);
--         memcpy(w_string_cstr(r), lean_string_cstr(s1), sz1 - 1);
--         dec_ref(s1);
--     } else {
--         lean_assert(s1 != s2);
--         r = string_ensure_capacity(s1, sz2-1);
--     }
--     memcpy(w_string_cstr(r) + sz1 - 1, lean_string_cstr(s2), sz2 - 1);
--     lean_to_string(r)->m_size   = new_sz;
--     lean_to_string(r)->m_length = new_len;
--     w_string_cstr(r)[new_sz - 1] = 0;
--     return r;
-- }
-- ```
-- duplicate of lean_string_append:
-- def lean_string_append := [JS_EXPR|#0 + #1]

-- ============
-- Init.Data.SInt.Basic
-- ============

-- ```lean
-- def Int8.ofInt (i : @& Int) : Int8 := ⟨⟨BitVec.ofInt 8 i⟩⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int8_of_int(b_lean_obj_arg a) {
--     int8_t res;
-- 
--     if (lean_is_scalar(a)) {
--         res = (int8_t)lean_scalar_to_int64(a);
--     } else {
--         res = lean_int8_of_big_int(a);
--     }
-- 
--     return (uint8_t)res;
-- }
-- ```
def lean_int8_of_int := [JS_EXPR|fromSigned(#0, 0xFF)]

-- ```lean
-- def Int8.ofNat (n : @& Nat) : Int8 := ⟨⟨BitVec.ofNat 8 n⟩⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int8_of_nat(b_lean_obj_arg a) {
--     int8_t res;
-- 
--     if (lean_is_scalar(a)) {
--         res = (int8_t)lean_unbox(a);
--     } else {
--         res = lean_int8_of_big_int(a);
--     }
-- 
--     return (uint8_t)res;
-- }
-- ```
def lean_int8_of_nat := [JS_EXPR|fromSigned(#0, 0xFF)]

-- ```lean
-- def Int8.toInt (i : Int8) : Int := i.toBitVec.toInt
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_int8_to_int(uint8_t a) {
--     int8_t arg = (int8_t)a;
--     return lean_int64_to_int((int64_t)arg);
-- }
-- ```
def lean_int8_to_int := [JS_EXPR|toSigned(#0, 0xFF, 8)]

-- ```lean
-- def Int8.neg (i : Int8) : Int8 := ⟨⟨-i.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int8_neg(uint8_t a) {
--     // do not cast to `int8_t`, as there underflow is undefined behavior
--     return -a;
-- }
-- ```
def lean_int8_neg := [JS_EXPR|fromSigned(-toSigned(#0, 0xFF, 8), 0xFF)]

-- ```lean
-- protected def Int8.add (a b : Int8) : Int8 := ⟨⟨a.toBitVec + b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int8_add(uint8_t a1, uint8_t a2) {
--     // do not cast to `int8_t`, as there overflow is undefined behavior
--     return a1 + a2;
-- }
-- ```
def lean_int8_add := [JS_EXPR|fromSigned(toSigned(#0, 0xFF, 8) + toSigned(#1, 0xFF, 8), 0xFF)]

-- ```lean
-- protected def Int8.sub (a b : Int8) : Int8 := ⟨⟨a.toBitVec - b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int8_sub(uint8_t a1, uint8_t a2) {
--     // do not cast to `int8_t`, as there overflow is undefined behavior
--     return a1 - a2;
-- }
-- ```
def lean_int8_sub := [JS_EXPR|fromSigned(toSigned(#0, 0xFF, 8) - toSigned(#1, 0xFF, 8), 0xFF)]

-- ```lean
-- protected def Int8.mul (a b : Int8) : Int8 := ⟨⟨a.toBitVec * b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int8_mul(uint8_t a1, uint8_t a2) {
--     // do not cast to `int8_t`, as there overflow is undefined behavior
--     return 1U * a1 * a2;
-- }
-- ```
def lean_int8_mul := [JS_EXPR|fromSigned(toSigned(#0, 0xFF, 8) * toSigned(#1, 0xFF, 8), 0xFF)]

-- ```lean
-- protected def Int8.div (a b : Int8) : Int8 := ⟨⟨BitVec.sdiv a.toBitVec b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int8_div(uint8_t a1, uint8_t a2) {
--     int8_t lhs = (int8_t)a1;
--     int8_t rhs = (int8_t)a2;
--     if (rhs == 0) return 0;
--     // Widen to 16-bit to avoid x86 idiv overflow trap on INT8_MIN / -1
--     return (uint8_t)((int16_t)lhs / (int16_t)rhs);
-- }
-- ```
def lean_int8_div := [JS_EXPR|fromSigned(toSigned(#0, 0xFF, 8) / toSigned(#1, 0xFF, 8), 0xFF)]

-- ```lean
-- protected def Int8.mod (a b : Int8) : Int8 := ⟨⟨BitVec.srem a.toBitVec b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int8_mod(uint8_t a1, uint8_t a2) {
--     int8_t lhs = (int8_t)a1;
--     int8_t rhs = (int8_t)a2;
--     if (rhs == 0) return (uint8_t)lhs;
--     // Widen to 16-bit to avoid x86 idiv overflow trap on INT8_MIN % -1
--     return (uint8_t)((int16_t)lhs % (int16_t)rhs);
-- }
-- ```
def lean_int8_mod := [JS_EXPR|fromSigned(toSigned(#0, 0xFF, 8) % toSigned(#1, 0xFF, 8), 0xFF)]

-- ```lean
-- protected def Int8.land (a b : Int8) : Int8 := ⟨⟨a.toBitVec &&& b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int8_land(uint8_t a1, uint8_t a2) {
--     int8_t lhs = (int8_t)a1;
--     int8_t rhs = (int8_t)a2;
-- 
--     return (uint8_t)(lhs & rhs);
-- }
-- ```
def lean_int8_land := [JS_EXPR|#0 & #1]

-- ```lean
-- protected def Int8.lor (a b : Int8) : Int8 := ⟨⟨a.toBitVec ||| b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int8_lor(uint8_t a1, uint8_t a2) {
--     int8_t lhs = (int8_t)a1;
--     int8_t rhs = (int8_t)a2;
-- 
--     return (uint8_t)(lhs | rhs);
-- }
-- ```
def lean_int8_lor := [JS_EXPR|#0 | #1]

-- ```lean
-- protected def Int8.xor (a b : Int8) : Int8 := ⟨⟨a.toBitVec ^^^ b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int8_xor(uint8_t a1, uint8_t a2) {
--     int8_t lhs = (int8_t)a1;
--     int8_t rhs = (int8_t)a2;
-- 
--     return (uint8_t)(lhs ^ rhs);
-- }
-- ```
def lean_int8_xor := [JS_EXPR|#0 ^ #1]

-- ```lean
-- protected def Int8.shiftLeft (a b : Int8) : Int8 := ⟨⟨a.toBitVec <<< (b.toBitVec.smod 8)⟩⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int8_shift_left(uint8_t a1, uint8_t a2) {
--     int8_t rhs = (((int8_t)a2 % 8) + 8) % 8; // this is smod 8
-- 
--     // do not cast to `int8_t`, as there negative `a1` is undefined behavior
--     return a1 << (uint8_t)rhs;
-- }
-- ```
def lean_int8_shift_left := [JS_EXPR|(#0 << #1) & 0xFF]

-- ```lean
-- protected def Int8.shiftRight (a b : Int8) : Int8 := ⟨⟨BitVec.sshiftRight' a.toBitVec (b.toBitVec.smod 8)⟩⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int8_shift_right(uint8_t a1, uint8_t a2) {
--     int8_t lhs = (int8_t)a1;
--     int8_t rhs = (((int8_t)a2 % 8) + 8) % 8; // this is smod 8
-- 
--     return (uint8_t)(lhs >> rhs);
-- }
-- ```
def lean_int8_shift_right := [JS_EXPR|(toSigned(#0, 0xFF, 8) >> #1) & 0xFF]

-- ```lean
-- protected def Int8.complement (a : Int8) : Int8 := ⟨⟨~~~a.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int8_complement(uint8_t a) {
--     int8_t arg = (int8_t)a;
-- 
--     return (uint8_t)(~arg);
-- }
-- ```
def lean_int8_complement := [JS_EXPR|(~#0) & 0xFF]

-- ```lean
-- protected def Int8.abs (a : Int8) : Int8 := ⟨⟨a.toBitVec.abs⟩⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int8_abs(uint8_t a) {
--     // do not cast to `int8_t` to negate, as there underflow is undefined behavior
--     return (int8_t)a < 0 ? -a : a;
-- }
-- ```
def lean_int8_abs := [JS_EXPR|throw new Error("lean_int8_abs not implemented")]

-- ```lean
-- def Int8.decEq (a b : Int8) : Decidable (a = b) :=
--   match a, b with
--   | ⟨n⟩, ⟨m⟩ =>
--     if h : n = m then
--       isTrue <| h ▸ rfl
--     else
--       isFalse (fun h' => Int8.noConfusion h' (fun h' => absurd h' h))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int8_dec_eq(uint8_t a1, uint8_t a2) {
--     int8_t lhs = (int8_t)a1;
--     int8_t rhs = (int8_t)a2;
-- 
--     return lhs == rhs;
-- }
-- ```
def lean_int8_dec_eq := [JS_EXPR|#0 === #1]

-- ```lean
-- def Bool.toInt8 (b : Bool) : Int8 := if b then 1 else 0
-- ```
--
-- ```cpp
-- static inline uint8_t lean_bool_to_int8(uint8_t a) { return (uint8_t)(int8_t)a; }
-- ```
def lean_bool_to_int8 := [JS_EXPR|#0 ? 1 : 0]

-- ```lean
-- def Int8.decLt (a b : Int8) : Decidable (a < b) :=
--   inferInstanceAs (Decidable (a.toBitVec.slt b.toBitVec))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int8_dec_lt(uint8_t a1, uint8_t a2) {
--     int8_t lhs = (int8_t)a1;
--     int8_t rhs = (int8_t)a2;
-- 
--     return lhs < rhs;
-- }
-- ```
def lean_int8_dec_lt := [JS_EXPR|toSigned(#0, 0xFF, 8) < toSigned(#1, 0xFF, 8)]

-- ```lean
-- def Int8.decLe (a b : Int8) : Decidable (a ≤ b) :=
--   inferInstanceAs (Decidable (a.toBitVec.sle b.toBitVec))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int8_dec_le(uint8_t a1, uint8_t a2) {
--     int8_t lhs = (int8_t)a1;
--     int8_t rhs = (int8_t)a2;
-- 
--     return lhs <= rhs;
-- }
-- ```
def lean_int8_dec_le := [JS_EXPR|toSigned(#0, 0xFF, 8) <= toSigned(#1, 0xFF, 8)]

-- ```lean
-- def Int16.ofInt (i : @& Int) : Int16 := ⟨⟨BitVec.ofInt 16 i⟩⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_int16_of_int(b_lean_obj_arg a) {
--     int16_t res;
-- 
--     if (lean_is_scalar(a)) {
--         res = (int16_t)lean_scalar_to_int64(a);
--     } else {
--         res = lean_int16_of_big_int(a);
--     }
-- 
--     return (uint16_t)res;
-- }
-- ```
def lean_int16_of_int := [JS_EXPR|fromSigned(#0, 0xFFFF)]

-- ```lean
-- def Int16.ofNat (n : @& Nat) : Int16 := ⟨⟨BitVec.ofNat 16 n⟩⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_int16_of_nat(b_lean_obj_arg a) {
--     int16_t res;
-- 
--     if (lean_is_scalar(a)) {
--         res = (int16_t)lean_unbox(a);
--     } else {
--         res = lean_int16_of_big_int(a);
--     }
-- 
--     return (uint16_t)res;
-- }
-- ```
def lean_int16_of_nat := [JS_EXPR|fromSigned(#0, 0xFFFF)]

-- ```lean
-- def Int16.toInt (i : Int16) : Int := i.toBitVec.toInt
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_int16_to_int(uint16_t a) {
--     int16_t arg = (int16_t)a;
--     return lean_int64_to_int((int64_t)arg);
-- }
-- ```
def lean_int16_to_int := [JS_EXPR|toSigned(#0, 0xFFFF, 16)]

-- ```lean
-- def Int16.toInt8 (a : Int16) : Int8 := ⟨⟨a.toBitVec.signExtend 8⟩⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int16_to_int8(uint16_t a) { return (uint8_t)(int8_t)(int16_t)a; }
-- ```
def lean_int16_to_int8 := [JS_EXPR|#0 & 0xFF]

-- ```lean
-- def Int8.toInt16 (a : Int8) : Int16 := ⟨⟨a.toBitVec.signExtend 16⟩⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_int8_to_int16(uint8_t a) { return (uint16_t)(int16_t)(int8_t)a; }
-- ```
def lean_int8_to_int16 := [JS_EXPR|#0 & 0xFFFF]

-- ```lean
-- def Int16.neg (i : Int16) : Int16 := ⟨⟨-i.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_int16_neg(uint16_t a) {
--     // do not cast to `int16_t`, as there underflow is undefined behavior
--     return -a;
-- }
-- ```
def lean_int16_neg := [JS_EXPR|fromSigned(-toSigned(#0, 0xFFFF, 16), 0xFFFF)]

-- ```lean
-- protected def Int16.add (a b : Int16) : Int16 := ⟨⟨a.toBitVec + b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_int16_add(uint16_t a1, uint16_t a2) {
--     // do not cast to `int16_t`, as there overflow is undefined behavior
--     return a1 + a2;
-- }
-- ```
def lean_int16_add := [JS_EXPR|fromSigned(toSigned(#0, 0xFFFF, 16) + toSigned(#1, 0xFFFF, 16), 0xFFFF)]

-- ```lean
-- protected def Int16.sub (a b : Int16) : Int16 := ⟨⟨a.toBitVec - b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_int16_sub(uint16_t a1, uint16_t a2) {
--     // do not cast to `int16_t`, as there overflow is undefined behavior
--     return a1 - a2;
-- }
-- ```
def lean_int16_sub := [JS_EXPR|fromSigned(toSigned(#0, 0xFFFF, 16) - toSigned(#1, 0xFFFF, 16), 0xFFFF)]

-- ```lean
-- protected def Int16.mul (a b : Int16) : Int16 := ⟨⟨a.toBitVec * b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_int16_mul(uint16_t a1, uint16_t a2) {
--     // do not cast to `int16_t`, as there overflow is undefined behavior
--     return 1U * a1 * a2;
-- }
-- ```
def lean_int16_mul := [JS_EXPR|fromSigned(toSigned(#0, 0xFFFF, 16) * toSigned(#1, 0xFFFF, 16), 0xFFFF)]

-- ```lean
-- protected def Int16.div (a b : Int16) : Int16 := ⟨⟨BitVec.sdiv a.toBitVec b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_int16_div(uint16_t a1, uint16_t a2) {
--     int16_t lhs = (int16_t)a1;
--     int16_t rhs = (int16_t)a2;
--     if (rhs == 0) return 0;
--     // Widen to 32-bit to avoid x86 idiv overflow trap on INT16_MIN / -1
--     return (uint16_t)((int32_t)lhs / (int32_t)rhs);
-- }
-- ```
def lean_int16_div := [JS_EXPR|fromSigned(toSigned(#0, 0xFFFF, 16) / toSigned(#1, 0xFFFF, 16), 0xFFFF)]

-- ```lean
-- protected def Int16.mod (a b : Int16) : Int16 := ⟨⟨BitVec.srem a.toBitVec b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_int16_mod(uint16_t a1, uint16_t a2) {
--     int16_t lhs = (int16_t)a1;
--     int16_t rhs = (int16_t)a2;
--     if (rhs == 0) return (uint16_t)lhs;
--     // Widen to 32-bit to avoid x86 idiv overflow trap on INT16_MIN % -1
--     return (uint16_t)((int32_t)lhs % (int32_t)rhs);
-- }
-- ```
def lean_int16_mod := [JS_EXPR|fromSigned(toSigned(#0, 0xFFFF, 16) % toSigned(#1, 0xFFFF, 16), 0xFFFF)]

-- ```lean
-- protected def Int16.land (a b : Int16) : Int16 := ⟨⟨a.toBitVec &&& b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_int16_land(uint16_t a1, uint16_t a2) {
--     int16_t lhs = (int16_t)a1;
--     int16_t rhs = (int16_t)a2;
-- 
--     return (uint16_t)(lhs & rhs);
-- }
-- ```
def lean_int16_land := [JS_EXPR|#0 & #1]

-- ```lean
-- protected def Int16.lor (a b : Int16) : Int16 := ⟨⟨a.toBitVec ||| b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_int16_lor(uint16_t a1, uint16_t a2) {
--     int16_t lhs = (int16_t)a1;
--     int16_t rhs = (int16_t)a2;
-- 
--     return (uint16_t)(lhs | rhs);
-- }
-- ```
def lean_int16_lor := [JS_EXPR|#0 | #1]

-- ```lean
-- protected def Int16.xor (a b : Int16) : Int16 := ⟨⟨a.toBitVec ^^^ b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_int16_xor(uint16_t a1, uint16_t a2) {
--     int16_t lhs = (int16_t)a1;
--     int16_t rhs = (int16_t)a2;
-- 
--     return (uint16_t)(lhs ^ rhs);
-- }
-- ```
def lean_int16_xor := [JS_EXPR|#0 ^ #1]

-- ```lean
-- protected def Int16.shiftLeft (a b : Int16) : Int16 := ⟨⟨a.toBitVec <<< (b.toBitVec.smod 16)⟩⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_int16_shift_left(uint16_t a1, uint16_t a2) {
--     int16_t rhs = (((int16_t)a2 % 16) + 16) % 16; // this is smod 16
-- 
--     // do not cast to `int16_t`, as there negative `a1` is undefined behavior
--     return a1 << (uint16_t)rhs;
-- }
-- ```
def lean_int16_shift_left := [JS_EXPR|(#0 << #1) & 0xFFFF]

-- ```lean
-- protected def Int16.shiftRight (a b : Int16) : Int16 := ⟨⟨BitVec.sshiftRight' a.toBitVec (b.toBitVec.smod 16)⟩⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_int16_shift_right(uint16_t a1, uint16_t a2) {
--     int16_t lhs = (int16_t)a1;
--     int16_t rhs = (((int16_t)a2 % 16) + 16) % 16; // this is smod 16
-- 
--     return (uint16_t)(lhs >> rhs);
-- }
-- ```
def lean_int16_shift_right := [JS_EXPR|(toSigned(#0, 0xFFFF, 16) >> #1) & 0xFFFF]

-- ```lean
-- protected def Int16.complement (a : Int16) : Int16 := ⟨⟨~~~a.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_int16_complement(uint16_t a) {
--     int16_t arg = (int16_t)a;
-- 
--     return (uint16_t)(~arg);
-- }
-- ```
def lean_int16_complement := [JS_EXPR|(~#0) & 0xFFFF]

-- ```lean
-- protected def Int16.abs (a : Int16) : Int16 := ⟨⟨a.toBitVec.abs⟩⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_int16_abs(uint16_t a) {
--     // do not cast to `int16_t` to negate, as there underflow is undefined behavior
--     return (int16_t)a < 0 ? -a : a;
-- }
-- ```
def lean_int16_abs := [JS_EXPR|throw new Error("lean_int16_abs not implemented")]

-- ```lean
-- def Int16.decEq (a b : Int16) : Decidable (a = b) :=
--   match a, b with
--   | ⟨n⟩, ⟨m⟩ =>
--     if h : n = m then
--       isTrue <| h ▸ rfl
--     else
--       isFalse (fun h' => Int16.noConfusion h' (fun h' => absurd h' h))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int16_dec_eq(uint16_t a1, uint16_t a2) {
--     int16_t lhs = (int16_t)a1;
--     int16_t rhs = (int16_t)a2;
-- 
--     return lhs == rhs;
-- }
-- ```
def lean_int16_dec_eq := [JS_EXPR|#0 === #1]

-- ```lean
-- def Bool.toInt16 (b : Bool) : Int16 := if b then 1 else 0
-- ```
--
-- ```cpp
-- static inline uint16_t lean_bool_to_int16(uint8_t a) { return (uint16_t)(int16_t)a; }
-- ```
def lean_bool_to_int16 := [JS_EXPR|#0 ? 1 : 0]

-- ```lean
-- def Int16.decLt (a b : Int16) : Decidable (a < b) :=
--   inferInstanceAs (Decidable (a.toBitVec.slt b.toBitVec))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int16_dec_lt(uint16_t a1, uint16_t a2) {
--     int16_t lhs = (int16_t)a1;
--     int16_t rhs = (int16_t)a2;
-- 
--     return lhs < rhs;
-- }
-- ```
def lean_int16_dec_lt := [JS_EXPR|toSigned(#0, 0xFFFF, 16) < toSigned(#1, 0xFFFF, 16)]

-- ```lean
-- def Int16.decLe (a b : Int16) : Decidable (a ≤ b) :=
--   inferInstanceAs (Decidable (a.toBitVec.sle b.toBitVec))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int16_dec_le(uint16_t a1, uint16_t a2) {
--     int16_t lhs = (int16_t)a1;
--     int16_t rhs = (int16_t)a2;
-- 
--     return lhs <= rhs;
-- }
-- ```
def lean_int16_dec_le := [JS_EXPR|toSigned(#0, 0xFFFF, 16) <= toSigned(#1, 0xFFFF, 16)]

-- ```lean
-- def Int32.ofInt (i : @& Int) : Int32 := ⟨⟨BitVec.ofInt 32 i⟩⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_int32_of_int(b_lean_obj_arg a) {
--     int32_t res;
-- 
--     if (lean_is_scalar(a)) {
--         res = (int32_t)lean_scalar_to_int64(a);
--     } else {
--         res = lean_int32_of_big_int(a);
--     }
-- 
--     return (uint32_t)res;
-- }
-- ```
def lean_int32_of_int := [JS_EXPR|fromSigned(#0, 0xFFFFFFFF)]

-- ```lean
-- def Int32.ofNat (n : @& Nat) : Int32 := ⟨⟨BitVec.ofNat 32 n⟩⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_int32_of_nat(b_lean_obj_arg a) {
--     int32_t res;
-- 
--     if (lean_is_scalar(a)) {
--         res = (int32_t)lean_unbox(a);
--     } else {
--         res = lean_int32_of_big_int(a);
--     }
-- 
--     return (uint32_t)res;
-- }
-- ```
def lean_int32_of_nat := [JS_EXPR|fromSigned(#0, 0xFFFFFFFF)]

-- ```lean
-- def Int32.toInt (i : Int32) : Int := i.toBitVec.toInt
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_int32_to_int(uint32_t a) {
--     int32_t arg = (int32_t)a;
--     return lean_int64_to_int((int64_t)arg);
-- }
-- ```
def lean_int32_to_int := [JS_EXPR|toSigned(#0, 0xFFFFFFFF, 32)]

-- ```lean
-- def Int32.toInt8 (a : Int32) : Int8 := ⟨⟨a.toBitVec.signExtend 8⟩⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int32_to_int8(uint32_t a) { return (uint8_t)(int8_t)(int32_t)a; }
-- ```
def lean_int32_to_int8 := [JS_EXPR|#0 & 0xFF]

-- ```lean
-- def Int32.toInt16 (a : Int32) : Int16 := ⟨⟨a.toBitVec.signExtend 16⟩⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_int32_to_int16(uint32_t a) { return (uint16_t)(int16_t)(int32_t)a; }
-- ```
def lean_int32_to_int16 := [JS_EXPR|#0 & 0xFFFF]

-- ```lean
-- def Int8.toInt32 (a : Int8) : Int32 := ⟨⟨a.toBitVec.signExtend 32⟩⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_int8_to_int32(uint8_t a) { return (uint32_t)(int32_t)(int8_t)a; }
-- ```
def lean_int8_to_int32 := [JS_EXPR|#0 & 0xFFFFFFFF]

-- ```lean
-- def Int16.toInt32 (a : Int16) : Int32 := ⟨⟨a.toBitVec.signExtend 32⟩⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_int16_to_int32(uint16_t a) { return (uint32_t)(int32_t)(int16_t)a; }
-- ```
def lean_int16_to_int32 := [JS_EXPR|#0 & 0xFFFFFFFF]

-- ```lean
-- def Int32.neg (i : Int32) : Int32 := ⟨⟨-i.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_int32_neg(uint32_t a) {
--     // do not cast to `int32_t`, as there underflow is undefined behavior
--     return -a;
-- }
-- ```
def lean_int32_neg := [JS_EXPR|fromSigned(-toSigned(#0, 0xFFFFFFFF, 32), 0xFFFFFFFF)]

-- ```lean
-- protected def Int32.add (a b : Int32) : Int32 := ⟨⟨a.toBitVec + b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_int32_add(uint32_t a1, uint32_t a2) {
--     // do not cast to `int32_t`, as there overflow is undefined behavior
--     return a1 + a2;
-- }
-- ```
def lean_int32_add := [JS_EXPR|fromSigned(toSigned(#0, 0xFFFFFFFF, 32) + toSigned(#1, 0xFFFFFFFF, 32), 0xFFFFFFFF)]

-- ```lean
-- protected def Int32.sub (a b : Int32) : Int32 := ⟨⟨a.toBitVec - b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_int32_sub(uint32_t a1, uint32_t a2) {
--     // do not cast to `int32_t`, as there overflow is undefined behavior
--     return a1 - a2;
-- }
-- ```
def lean_int32_sub := [JS_EXPR|fromSigned(toSigned(#0, 0xFFFFFFFF, 32) - toSigned(#1, 0xFFFFFFFF, 32), 0xFFFFFFFF)]

-- ```lean
-- protected def Int32.mul (a b : Int32) : Int32 := ⟨⟨a.toBitVec * b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_int32_mul(uint32_t a1, uint32_t a2) {
--     // do not cast to `int32_t`, as there overflow is undefined behavior
--     return 1U * a1 * a2;
-- }
-- ```
def lean_int32_mul := [JS_EXPR|fromSigned(toSigned(#0, 0xFFFFFFFF, 32) * toSigned(#1, 0xFFFFFFFF, 32), 0xFFFFFFFF)]

-- ```lean
-- protected def Int32.div (a b : Int32) : Int32 := ⟨⟨BitVec.sdiv a.toBitVec b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_int32_div(uint32_t a1, uint32_t a2) {
--     int32_t lhs = (int32_t)a1;
--     int32_t rhs = (int32_t)a2;
--     if (rhs == 0) return 0;
--     // Widen to 64-bit to avoid x86 idiv overflow trap on INT32_MIN / -1
--     return (uint32_t)((int64_t)lhs / (int64_t)rhs);
-- }
-- ```
def lean_int32_div := [JS_EXPR|fromSigned(toSigned(#0, 0xFFFFFFFF, 32) / toSigned(#1, 0xFFFFFFFF, 32), 0xFFFFFFFF)]

-- ```lean
-- protected def Int32.mod (a b : Int32) : Int32 := ⟨⟨BitVec.srem a.toBitVec b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_int32_mod(uint32_t a1, uint32_t a2) {
--     int32_t lhs = (int32_t)a1;
--     int32_t rhs = (int32_t)a2;
--     if (rhs == 0) return (uint32_t)lhs;
--     // Widen to 64-bit to avoid x86 idiv overflow trap on INT32_MIN % -1
--     return (uint32_t)((int64_t)lhs % (int64_t)rhs);
-- }
-- ```
def lean_int32_mod := [JS_EXPR|fromSigned(toSigned(#0, 0xFFFFFFFF, 32) % toSigned(#1, 0xFFFFFFFF, 32), 0xFFFFFFFF)]

-- ```lean
-- protected def Int32.land (a b : Int32) : Int32 := ⟨⟨a.toBitVec &&& b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_int32_land(uint32_t a1, uint32_t a2) {
--     int32_t lhs = (int32_t)a1;
--     int32_t rhs = (int32_t)a2;
-- 
--     return (uint32_t)(lhs & rhs);
-- }
-- ```
def lean_int32_land := [JS_EXPR|#0 & #1]

-- ```lean
-- protected def Int32.lor (a b : Int32) : Int32 := ⟨⟨a.toBitVec ||| b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_int32_lor(uint32_t a1, uint32_t a2) {
--     int32_t lhs = (int32_t)a1;
--     int32_t rhs = (int32_t)a2;
-- 
--     return (uint32_t)(lhs | rhs);
-- }
-- ```
def lean_int32_lor := [JS_EXPR|#0 | #1]

-- ```lean
-- protected def Int32.xor (a b : Int32) : Int32 := ⟨⟨a.toBitVec ^^^ b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_int32_xor(uint32_t a1, uint32_t a2) {
--     int32_t lhs = (int32_t)a1;
--     int32_t rhs = (int32_t)a2;
-- 
--     return (uint32_t)(lhs ^ rhs);
-- }
-- ```
def lean_int32_xor := [JS_EXPR|#0 ^ #1]

-- ```lean
-- protected def Int32.shiftLeft (a b : Int32) : Int32 := ⟨⟨a.toBitVec <<< (b.toBitVec.smod 32)⟩⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_int32_shift_left(uint32_t a1, uint32_t a2) {
--     int32_t rhs = (((int32_t)a2 % 32) + 32) % 32; // this is smod 32
-- 
--     // do not cast to `int32_t`, as there negative `a1` is undefined behavior
--     return a1 << (uint32_t)rhs;
-- }
-- ```
def lean_int32_shift_left := [JS_EXPR|(#0 << #1) & 0xFFFFFFFF]

-- ```lean
-- protected def Int32.shiftRight (a b : Int32) : Int32 := ⟨⟨BitVec.sshiftRight' a.toBitVec (b.toBitVec.smod 32)⟩⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_int32_shift_right(uint32_t a1, uint32_t a2) {
--     int32_t lhs = (int32_t)a1;
--     int32_t rhs = (((int32_t)a2 % 32) + 32) % 32; // this is smod 32
-- 
--     return (uint32_t)(lhs >> rhs);
-- }
-- ```
def lean_int32_shift_right := [JS_EXPR|(toSigned(#0, 0xFFFFFFFF, 32) >> #1) & 0xFFFFFFFF]

-- ```lean
-- protected def Int32.complement (a : Int32) : Int32 := ⟨⟨~~~a.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_int32_complement(uint32_t a) {
--     int32_t arg = (int32_t)a;
-- 
--     return (uint32_t)(~arg);
-- }
-- ```
def lean_int32_complement := [JS_EXPR|(~#0) & 0xFFFFFFFF]

-- ```lean
-- protected def Int32.abs (a : Int32) : Int32 := ⟨⟨a.toBitVec.abs⟩⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_int32_abs(uint32_t a) {
--     // do not cast to `int32_t` to negate, as there underflow is undefined behavior
--     return (int32_t)a < 0 ? -a : a;
-- }
-- ```
def lean_int32_abs := [JS_EXPR|throw new Error("lean_int32_abs not implemented")]

-- ```lean
-- def Int32.decEq (a b : Int32) : Decidable (a = b) :=
--   match a, b with
--   | ⟨n⟩, ⟨m⟩ =>
--     if h : n = m then
--       isTrue <| h ▸ rfl
--     else
--       isFalse (fun h' => Int32.noConfusion h' (fun h' => absurd h' h))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int32_dec_eq(uint32_t a1, uint32_t a2) {
--     int32_t lhs = (int32_t)a1;
--     int32_t rhs = (int32_t)a2;
-- 
--     return lhs == rhs;
-- }
-- ```
def lean_int32_dec_eq := [JS_EXPR|#0 === #1]

-- ```lean
-- def Bool.toInt32 (b : Bool) : Int32 := if b then 1 else 0
-- ```
--
-- ```cpp
-- static inline uint32_t lean_bool_to_int32(uint8_t a) { return (uint32_t)(int32_t)a; }
-- ```
def lean_bool_to_int32 := [JS_EXPR|#0 ? 1 : 0]

-- ```lean
-- def Int32.decLt (a b : Int32) : Decidable (a < b) :=
--   inferInstanceAs (Decidable (a.toBitVec.slt b.toBitVec))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int32_dec_lt(uint32_t a1, uint32_t a2) {
--     int32_t lhs = (int32_t)a1;
--     int32_t rhs = (int32_t)a2;
-- 
--     return lhs < rhs;
-- }
-- ```
def lean_int32_dec_lt := [JS_EXPR|toSigned(#0, 0xFFFFFFFF, 32) < toSigned(#1, 0xFFFFFFFF, 32)]

-- ```lean
-- def Int32.decLe (a b : Int32) : Decidable (a ≤ b) :=
--   inferInstanceAs (Decidable (a.toBitVec.sle b.toBitVec))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int32_dec_le(uint32_t a1, uint32_t a2) {
--     int32_t lhs = (int32_t)a1;
--     int32_t rhs = (int32_t)a2;
-- 
--     return lhs <= rhs;
-- }
-- ```
def lean_int32_dec_le := [JS_EXPR|toSigned(#0, 0xFFFFFFFF, 32) <= toSigned(#1, 0xFFFFFFFF, 32)]

-- ```lean
-- def Int64.ofInt (i : @& Int) : Int64 := ⟨⟨BitVec.ofInt 64 i⟩⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_int64_of_int(b_lean_obj_arg a) {
--     int64_t res;
-- 
--     if (lean_is_scalar(a)) {
--         res = lean_scalar_to_int64(a);
--     } else {
--         res = lean_int64_of_big_int(a);
--     }
-- 
--     return (uint64_t)res;
-- }
-- ```
def lean_int64_of_int := [JS_EXPR|fromSigned(#0, 0xFFFFFFFFFFFFFFFF)]

-- ```lean
-- def Int64.ofNat (n : @& Nat) : Int64 := ⟨⟨BitVec.ofNat 64 n⟩⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_int64_of_nat(b_lean_obj_arg a) {
--     int64_t res;
-- 
--     if (lean_is_scalar(a)) {
--         res = (int64_t)lean_unbox(a);
--     } else {
--         res = lean_int64_of_big_int(a);
--     }
-- 
--     return (uint64_t)res;
-- }
-- ```
def lean_int64_of_nat := [JS_EXPR|fromSigned(#0, 0xFFFFFFFFFFFFFFFF)]

-- ```lean
-- def Int64.toInt (i : Int64) : Int := i.toBitVec.toInt
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_int64_to_int_sint(uint64_t a) {
--     int64_t arg = (int64_t)a;
--     return lean_int64_to_int(arg);
-- }
-- ```
def lean_int64_to_int_sint := [JS_EXPR|toSigned(#0, 0xFFFFFFFFFFFFFFFF, 64)]

-- ```lean
-- def Int64.toInt8 (a : Int64) : Int8 := ⟨⟨a.toBitVec.signExtend 8⟩⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int64_to_int8(uint64_t a) { return (uint8_t)(int8_t)(int64_t)a; }
-- ```
def lean_int64_to_int8 := [JS_EXPR|#0 & 0xFF]

-- ```lean
-- def Int64.toInt16 (a : Int64) : Int16 := ⟨⟨a.toBitVec.signExtend 16⟩⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_int64_to_int16(uint64_t a) { return (uint16_t)(int16_t)(int64_t)a; }
-- ```
def lean_int64_to_int16 := [JS_EXPR|#0 & 0xFFFF]

-- ```lean
-- def Int64.toInt32 (a : Int64) : Int32 := ⟨⟨a.toBitVec.signExtend 32⟩⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_int64_to_int32(uint64_t a) { return (uint32_t)(int32_t)(int64_t)a; }
-- ```
def lean_int64_to_int32 := [JS_EXPR|#0 & 0xFFFFFFFF]

-- ```lean
-- def Int8.toInt64 (a : Int8) : Int64 := ⟨⟨a.toBitVec.signExtend 64⟩⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_int8_to_int64(uint8_t a) { return (uint64_t)(int64_t)(int8_t)a; }
-- ```
def lean_int8_to_int64 := [JS_EXPR|#0 & 0xFFFFFFFFFFFFFFFF]

-- ```lean
-- def Int16.toInt64 (a : Int16) : Int64 := ⟨⟨a.toBitVec.signExtend 64⟩⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_int16_to_int64(uint16_t a) { return (uint64_t)(int64_t)(int16_t)a; }
-- ```
def lean_int16_to_int64 := [JS_EXPR|#0 & 0xFFFFFFFFFFFFFFFF]

-- ```lean
-- def Int32.toInt64 (a : Int32) : Int64 := ⟨⟨a.toBitVec.signExtend 64⟩⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_int32_to_int64(uint32_t a) { return (uint64_t)(int64_t)(int32_t)a; }
-- ```
def lean_int32_to_int64 := [JS_EXPR|#0 & 0xFFFFFFFFFFFFFFFF]

-- ```lean
-- def Int64.neg (i : Int64) : Int64 := ⟨⟨-i.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_int64_neg(uint64_t a) {
--     // do not cast to `int64_t`, as there underflow is undefined behavior
--     return -a;
-- }
-- ```
def lean_int64_neg := [JS_EXPR|fromSigned(-toSigned(#0, 0xFFFFFFFFFFFFFFFF, 64), 0xFFFFFFFFFFFFFFFF)]

-- ```lean
-- protected def Int64.add (a b : Int64) : Int64 := ⟨⟨a.toBitVec + b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_int64_add(uint64_t a1, uint64_t a2) {
--     // do not cast to `int64_t`, as there overflow is undefined behavior
--     return a1 + a2;
-- }
-- ```
def lean_int64_add := [JS_EXPR|fromSigned(toSigned(#0, 0xFFFFFFFFFFFFFFFF, 64) + toSigned(#1, 0xFFFFFFFFFFFFFFFF, 64), 0xFFFFFFFFFFFFFFFF)]

-- ```lean
-- protected def Int64.sub (a b : Int64) : Int64 := ⟨⟨a.toBitVec - b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_int64_sub(uint64_t a1, uint64_t a2) {
--     // do not cast to `int64_t`, as there overflow is undefined behavior
--     return a1 - a2;
-- }
-- ```
def lean_int64_sub := [JS_EXPR|fromSigned(toSigned(#0, 0xFFFFFFFFFFFFFFFF, 64) - toSigned(#1, 0xFFFFFFFFFFFFFFFF, 64), 0xFFFFFFFFFFFFFFFF)]

-- ```lean
-- protected def Int64.mul (a b : Int64) : Int64 := ⟨⟨a.toBitVec * b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_int64_mul(uint64_t a1, uint64_t a2) {
--     // do not cast to `int64_t`, as there overflow is undefined behavior
--     return 1U * a1 * a2;
-- }
-- ```
def lean_int64_mul := [JS_EXPR|fromSigned(toSigned(#0, 0xFFFFFFFFFFFFFFFF, 64) * toSigned(#1, 0xFFFFFFFFFFFFFFFF, 64), 0xFFFFFFFFFFFFFFFF)]

-- ```lean
-- protected def Int64.div (a b : Int64) : Int64 := ⟨⟨BitVec.sdiv a.toBitVec b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_int64_div(uint64_t a1, uint64_t a2) {
--     int64_t lhs = (int64_t)a1;
--     int64_t rhs = (int64_t)a2;
--     if (rhs == 0) return 0;
--     // Check for overflow: INT64_MIN / -1 would trap on x86 idiv
--     if (lhs == INT64_MIN && rhs == -1) return (uint64_t)INT64_MIN;
--     return (uint64_t)(lhs / rhs);
-- }
-- ```
def lean_int64_div := [JS_EXPR|fromSigned(toSigned(#0, 0xFFFFFFFFFFFFFFFF, 64) / toSigned(#1, 0xFFFFFFFFFFFFFFFF, 64), 0xFFFFFFFFFFFFFFFF)]

-- ```lean
-- protected def Int64.mod (a b : Int64) : Int64 := ⟨⟨BitVec.srem a.toBitVec b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_int64_mod(uint64_t a1, uint64_t a2) {
--     int64_t lhs = (int64_t)a1;
--     int64_t rhs = (int64_t)a2;
--     if (rhs == 0) return (uint64_t)lhs;
--     // Check for overflow: INT64_MIN % -1 would trap on x86 idiv
--     if (lhs == INT64_MIN && rhs == -1) return 0;
--     return (uint64_t)(lhs % rhs);
-- }
-- ```
def lean_int64_mod := [JS_EXPR|fromSigned(toSigned(#0, 0xFFFFFFFFFFFFFFFF, 64) % toSigned(#1, 0xFFFFFFFFFFFFFFFF, 64), 0xFFFFFFFFFFFFFFFF)]

-- ```lean
-- protected def Int64.land (a b : Int64) : Int64 := ⟨⟨a.toBitVec &&& b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_int64_land(uint64_t a1, uint64_t a2) {
--     int64_t lhs = (int64_t)a1;
--     int64_t rhs = (int64_t)a2;
-- 
--     return (uint64_t)(lhs & rhs);
-- }
-- ```
def lean_int64_land := [JS_EXPR|#0 & #1]

-- ```lean
-- protected def Int64.lor (a b : Int64) : Int64 := ⟨⟨a.toBitVec ||| b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_int64_lor(uint64_t a1, uint64_t a2) {
--     int64_t lhs = (int64_t)a1;
--     int64_t rhs = (int64_t)a2;
-- 
--     return (uint64_t)(lhs | rhs);
-- }
-- ```
def lean_int64_lor := [JS_EXPR|#0 | #1]

-- ```lean
-- protected def Int64.xor (a b : Int64) : Int64 := ⟨⟨a.toBitVec ^^^ b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_int64_xor(uint64_t a1, uint64_t a2) {
--     int64_t lhs = (int64_t)a1;
--     int64_t rhs = (int64_t)a2;
-- 
--     return (uint64_t)(lhs ^ rhs);
-- }
-- ```
def lean_int64_xor := [JS_EXPR|#0 ^ #1]

-- ```lean
-- protected def Int64.shiftLeft (a b : Int64) : Int64 := ⟨⟨a.toBitVec <<< (b.toBitVec.smod 64)⟩⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_int64_shift_left(uint64_t a1, uint64_t a2) {
--     int64_t rhs = (((int64_t)a2 % 64) + 64) % 64; // this is smod 64
-- 
--     // do not cast to `int64_t`, as there negative `a1` is undefined behavior
--     return a1 << (uint64_t)rhs;
-- }
-- ```
def lean_int64_shift_left := [JS_EXPR|(#0 << #1) & 0xFFFFFFFFFFFFFFFF]

-- ```lean
-- protected def Int64.shiftRight (a b : Int64) : Int64 := ⟨⟨BitVec.sshiftRight' a.toBitVec (b.toBitVec.smod 64)⟩⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_int64_shift_right(uint64_t a1, uint64_t a2) {
--     int64_t lhs = (int64_t)a1;
--     int64_t rhs = (((int64_t)a2 % 64) + 64) % 64; // this is smod 64
-- 
--     return (uint64_t)(lhs >> rhs);
-- }
-- ```
def lean_int64_shift_right := [JS_EXPR|(toSigned(#0, 0xFFFFFFFFFFFFFFFF, 64) >> #1) & 0xFFFFFFFFFFFFFFFF]

-- ```lean
-- protected def Int64.complement (a : Int64) : Int64 := ⟨⟨~~~a.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_int64_complement(uint64_t a) {
--     int64_t arg = (int64_t)a;
-- 
--     return (uint64_t)(~arg);
-- }
-- ```
def lean_int64_complement := [JS_EXPR|(~#0) & 0xFFFFFFFFFFFFFFFF]

-- ```lean
-- protected def Int64.abs (a : Int64) : Int64 := ⟨⟨a.toBitVec.abs⟩⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_int64_abs(uint64_t a) {
--     // do not cast to `int32_t` to negate, as there underflow is undefined behavior
--     return (int64_t)a < 0 ? -a : a;
-- }
-- ```
def lean_int64_abs := [JS_EXPR|throw new Error("lean_int64_abs not implemented")]

-- ```lean
-- def Int64.decEq (a b : Int64) : Decidable (a = b) :=
--   match a, b with
--   | ⟨n⟩, ⟨m⟩ =>
--     if h : n = m then
--       isTrue <| h ▸ rfl
--     else
--       isFalse (fun h' => Int64.noConfusion h' (fun h' => absurd h' h))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int64_dec_eq(uint64_t a1, uint64_t a2) {
--     int64_t lhs = (int64_t)a1;
--     int64_t rhs = (int64_t)a2;
-- 
--     return lhs == rhs;
-- }
-- ```
def lean_int64_dec_eq := [JS_EXPR|#0 === #1]

-- ```lean
-- def Bool.toInt64 (b : Bool) : Int64 := if b then 1 else 0
-- ```
--
-- ```cpp
-- static inline uint64_t lean_bool_to_int64(uint8_t a) { return (uint64_t)(int64_t)a; }
-- ```
def lean_bool_to_int64 := [JS_EXPR|#0 ? 1 : 0]

-- ```lean
-- def Int64.decLt (a b : Int64) : Decidable (a < b) :=
--   inferInstanceAs (Decidable (a.toBitVec.slt b.toBitVec))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int64_dec_lt(uint64_t a1, uint64_t a2) {
--     int64_t lhs = (int64_t)a1;
--     int64_t rhs = (int64_t)a2;
-- 
--     return lhs < rhs;
-- }
-- ```
def lean_int64_dec_lt := [JS_EXPR|toSigned(#0, 0xFFFFFFFFFFFFFFFF, 64) < toSigned(#1, 0xFFFFFFFFFFFFFFFF, 64)]

-- ```lean
-- def Int64.decLe (a b : Int64) : Decidable (a ≤ b) :=
--   inferInstanceAs (Decidable (a.toBitVec.sle b.toBitVec))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_int64_dec_le(uint64_t a1, uint64_t a2) {
--     int64_t lhs = (int64_t)a1;
--     int64_t rhs = (int64_t)a2;
-- 
--     return lhs <= rhs;
-- }
-- ```
def lean_int64_dec_le := [JS_EXPR|toSigned(#0, 0xFFFFFFFFFFFFFFFF, 64) <= toSigned(#1, 0xFFFFFFFFFFFFFFFF, 64)]

-- ```lean
-- def ISize.ofInt (i : @& Int) : ISize := ⟨⟨BitVec.ofInt System.Platform.numBits i⟩⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_isize_of_int(b_lean_obj_arg a) {
--     ptrdiff_t res;
-- 
--     if (lean_is_scalar(a)) {
--         res = (ptrdiff_t)lean_scalar_to_int64(a);
--     } else {
--         res = lean_isize_of_big_int(a);
--     }
-- 
--     return (size_t)res;
-- }
-- ```
def lean_isize_of_int := [JS_EXPR|fromSigned(#0, 0xFFFFFFFFFFFFFFFF)]

-- ```lean
-- def ISize.ofNat (n : @& Nat) : ISize := ⟨⟨BitVec.ofNat System.Platform.numBits n⟩⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_isize_of_nat(b_lean_obj_arg a) {
--     ptrdiff_t res;
-- 
--     if (lean_is_scalar(a)) {
--         res = (ptrdiff_t)lean_unbox(a);
--     } else {
--         res = lean_isize_of_big_int(a);
--     }
-- 
--     return (size_t)res;
-- }
-- ```
def lean_isize_of_nat := [JS_EXPR|fromSigned(#0, 0xFFFFFFFFFFFFFFFF)]

-- ```lean
-- def ISize.toInt (i : ISize) : Int := i.toBitVec.toInt
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_isize_to_int(size_t a) {
--     ptrdiff_t arg = (ptrdiff_t)a;
--     return lean_int64_to_int((int64_t)arg);
-- }
-- ```
def lean_isize_to_int := [JS_EXPR|toSigned(#0, 0xFFFFFFFFFFFFFFFF, 64)]

-- ```lean
-- def ISize.toInt8 (a : ISize) : Int8 := ⟨⟨a.toBitVec.signExtend 8⟩⟩
-- ```
--
-- ```cpp
-- static inline uint8_t lean_isize_to_int8(size_t a) { return (uint8_t)(int8_t)(ptrdiff_t)a; }
-- ```
def lean_isize_to_int8 := [JS_EXPR|#0 & 0xFF]

-- ```lean
-- def ISize.toInt16 (a : ISize) : Int16 := ⟨⟨a.toBitVec.signExtend 16⟩⟩
-- ```
--
-- ```cpp
-- static inline uint16_t lean_isize_to_int16(size_t a) { return (uint16_t)(int16_t)(ptrdiff_t)a; }
-- ```
def lean_isize_to_int16 := [JS_EXPR|#0 & 0xFFFF]

-- ```lean
-- def ISize.toInt32 (a : ISize) : Int32 := ⟨⟨a.toBitVec.signExtend 32⟩⟩
-- ```
--
-- ```cpp
-- static inline uint32_t lean_isize_to_int32(size_t a) { return (uint32_t)(int32_t)(ptrdiff_t)a; }
-- ```
def lean_isize_to_int32 := [JS_EXPR|#0 & 0xFFFFFFFF]

-- ```lean
-- def ISize.toInt64 (a : ISize) : Int64 := ⟨⟨a.toBitVec.signExtend 64⟩⟩
-- ```
--
-- ```cpp
-- static inline uint64_t lean_isize_to_int64(size_t a) { return (uint64_t)(int64_t)(ptrdiff_t)a; }
-- ```
def lean_isize_to_int64 := [JS_EXPR|#0 & 0xFFFFFFFFFFFFFFFF]

-- ```lean
-- def Int8.toISize (a : Int8) : ISize := ⟨⟨a.toBitVec.signExtend System.Platform.numBits⟩⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_int8_to_isize(uint8_t a) { return (size_t)(ptrdiff_t)(int8_t)a; }
-- ```
def lean_int8_to_isize := [JS_EXPR|#0 & 0xFFFFFFFFFFFFFFFF]

-- ```lean
-- def Int16.toISize (a : Int16) : ISize := ⟨⟨a.toBitVec.signExtend System.Platform.numBits⟩⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_int16_to_isize(uint16_t a) { return (size_t)(ptrdiff_t)(int16_t)a; }
-- ```
def lean_int16_to_isize := [JS_EXPR|throw new Error("lean_int16_to_isize not implemented")]

-- ```lean
-- def Int32.toISize (a : Int32) : ISize := ⟨⟨a.toBitVec.signExtend System.Platform.numBits⟩⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_int32_to_isize(uint32_t a) { return (size_t)(ptrdiff_t)(int32_t)a; }
-- ```
def lean_int32_to_isize := [JS_EXPR|throw new Error("lean_int32_to_isize not implemented")]

-- ```lean
-- def Int64.toISize (a : Int64) : ISize := ⟨⟨a.toBitVec.signExtend System.Platform.numBits⟩⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_int64_to_isize(uint64_t a) { return (size_t)(ptrdiff_t)(int64_t)a; }
-- ```
def lean_int64_to_isize := [JS_EXPR|throw new Error("lean_int64_to_isize not implemented")]

-- ```lean
-- protected def ISize.neg (i : ISize) : ISize := ⟨⟨-i.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_isize_neg(size_t a) {
--     // do not cast to `ptrdiff_t`, as there underflow is undefined behavior
--     return -a;
-- }
-- ```
def lean_isize_neg := [JS_EXPR|throw new Error("lean_isize_neg not implemented")]

-- ```lean
-- protected def ISize.add (a b : ISize) : ISize := ⟨⟨a.toBitVec + b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_isize_add(size_t a1, size_t a2) {
--     // do not cast to `ptrdiff_t`, as there overflow is undefined behavior
--     return a1 + a2;
-- }
-- ```
def lean_isize_add := [JS_EXPR|throw new Error("lean_isize_add not implemented")]

-- ```lean
-- protected def ISize.sub (a b : ISize) : ISize := ⟨⟨a.toBitVec - b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_isize_sub(size_t a1, size_t a2) {
--     // do not cast to `ptrdiff_t`, as there overflow is undefined behavior
--     return a1 - a2;
-- }
-- ```
def lean_isize_sub := [JS_EXPR|throw new Error("lean_isize_sub not implemented")]

-- ```lean
-- protected def ISize.mul (a b : ISize) : ISize := ⟨⟨a.toBitVec * b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_isize_mul(size_t a1, size_t a2) {
--     // do not cast to `ptrdiff_t`, as there overflow is undefined behavior
--     return 1U * a1 * a2;
-- }
-- ```
def lean_isize_mul := [JS_EXPR|throw new Error("lean_isize_mul not implemented")]

-- ```lean
-- protected def ISize.div (a b : ISize) : ISize := ⟨⟨BitVec.sdiv a.toBitVec b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_isize_div(size_t a1, size_t a2) {
--     ptrdiff_t lhs = (ptrdiff_t)a1;
--     ptrdiff_t rhs = (ptrdiff_t)a2;
--     if (rhs == 0) return 0;
--     // Check for overflow: PTRDIFF_MIN / -1 would trap on x86 idiv
--     if (lhs == PTRDIFF_MIN && rhs == -1) return (size_t)PTRDIFF_MIN;
--     return (size_t)(lhs / rhs);
-- }
-- ```
def lean_isize_div := [JS_EXPR|throw new Error("lean_isize_div not implemented")]

-- ```lean
-- protected def ISize.mod (a b : ISize) : ISize := ⟨⟨BitVec.srem a.toBitVec b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_isize_mod(size_t a1, size_t a2) {
--     ptrdiff_t lhs = (ptrdiff_t)a1;
--     ptrdiff_t rhs = (ptrdiff_t)a2;
--     if (rhs == 0) return (size_t)lhs;
--     // Check for overflow: PTRDIFF_MIN / -1 would trap on x86 idiv
--     if (lhs == PTRDIFF_MIN && rhs == -1) return 0;
--     return (size_t)(lhs % rhs);
-- }
-- ```
def lean_isize_mod := [JS_EXPR|throw new Error("lean_isize_mod not implemented")]

-- ```lean
-- protected def ISize.land (a b : ISize) : ISize := ⟨⟨a.toBitVec &&& b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_isize_land(size_t a1, size_t a2) {
--     ptrdiff_t lhs = (ptrdiff_t)a1;
--     ptrdiff_t rhs = (ptrdiff_t)a2;
-- 
--     return (size_t)(lhs & rhs);
-- }
-- ```
def lean_isize_land := [JS_EXPR|throw new Error("lean_isize_land not implemented")]

-- ```lean
-- protected def ISize.lor (a b : ISize) : ISize := ⟨⟨a.toBitVec ||| b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_isize_lor(size_t a1, size_t a2) {
--     ptrdiff_t lhs = (ptrdiff_t)a1;
--     ptrdiff_t rhs = (ptrdiff_t)a2;
-- 
--     return (size_t)(lhs | rhs);
-- }
-- ```
def lean_isize_lor := [JS_EXPR|throw new Error("lean_isize_lor not implemented")]

-- ```lean
-- protected def ISize.xor (a b : ISize) : ISize := ⟨⟨a.toBitVec ^^^ b.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_isize_xor(size_t a1, size_t a2) {
--     ptrdiff_t lhs = (ptrdiff_t)a1;
--     ptrdiff_t rhs = (ptrdiff_t)a2;
-- 
--     return (size_t)(lhs ^ rhs);
-- }
-- ```
def lean_isize_xor := [JS_EXPR|throw new Error("lean_isize_xor not implemented")]

-- ```lean
-- protected def ISize.shiftLeft (a b : ISize) : ISize := ⟨⟨a.toBitVec <<< (b.toBitVec.smod System.Platform.numBits)⟩⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_isize_shift_left(size_t a1, size_t a2) {
--     ptrdiff_t size = sizeof(ptrdiff_t) * 8;
--     ptrdiff_t rhs = (((ptrdiff_t)a2 % size) + size) % size; // this is smod
-- 
--     // do not cast to `int64_t`, as there negative `a1` is undefined behavior
--     return a1 << (size_t)rhs;
-- }
-- ```
def lean_isize_shift_left := [JS_EXPR|throw new Error("lean_isize_shift_left not implemented")]

-- ```lean
-- protected def ISize.shiftRight (a b : ISize) : ISize := ⟨⟨BitVec.sshiftRight' a.toBitVec (b.toBitVec.smod System.Platform.numBits)⟩⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_isize_shift_right(size_t a1, size_t a2) {
--     ptrdiff_t lhs = (ptrdiff_t)a1;
--     ptrdiff_t size = sizeof(ptrdiff_t) * 8;
--     ptrdiff_t rhs = (((ptrdiff_t)a2 % size) + size) % size; // this is smod
-- 
--     return (size_t)(lhs >> rhs);
-- }
-- ```
def lean_isize_shift_right := [JS_EXPR|throw new Error("lean_isize_shift_right not implemented")]

-- ```lean
-- protected def ISize.complement (a : ISize) : ISize := ⟨⟨~~~a.toBitVec⟩⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_isize_complement(size_t a) {
--     ptrdiff_t arg = (ptrdiff_t)a;
-- 
--     return (size_t)(~arg);
-- }
-- ```
def lean_isize_complement := [JS_EXPR|throw new Error("lean_isize_complement not implemented")]

-- ```lean
-- protected def ISize.abs (a : ISize) : ISize := ⟨⟨a.toBitVec.abs⟩⟩
-- ```
--
-- ```cpp
-- static inline size_t lean_isize_abs(size_t a) {
--     // do not cast to `ptrdiff_t` to negate, as there underflow is undefined behavior
--     return (ptrdiff_t)a < 0 ? -a : a;
-- }
-- ```
def lean_isize_abs := [JS_EXPR|throw new Error("lean_isize_abs not implemented")]

-- ```lean
-- def ISize.decEq (a b : ISize) : Decidable (a = b) :=
--   match a, b with
--   | ⟨n⟩, ⟨m⟩ =>
--     if h : n = m then
--       isTrue <| h ▸ rfl
--     else
--       isFalse (fun h' => ISize.noConfusion h' (fun h' => absurd h' h))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_isize_dec_eq(size_t a1, size_t a2) {
--     ptrdiff_t lhs = (ptrdiff_t)a1;
--     ptrdiff_t rhs = (ptrdiff_t)a2;
-- 
--     return lhs == rhs;
-- }
-- ```
def lean_isize_dec_eq := [JS_EXPR|throw new Error("lean_isize_dec_eq not implemented")]

-- ```lean
-- def Bool.toISize (b : Bool) : ISize := if b then 1 else 0
-- ```
--
-- ```cpp
-- static inline size_t lean_bool_to_isize(uint8_t a) { return (size_t)(ptrdiff_t)a; }
-- ```
def lean_bool_to_isize := [JS_EXPR|throw new Error("lean_bool_to_isize not implemented")]

-- ```lean
-- def ISize.decLt (a b : ISize) : Decidable (a < b) :=
--   inferInstanceAs (Decidable (a.toBitVec.slt b.toBitVec))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_isize_dec_lt(size_t a1, size_t a2) {
--     ptrdiff_t lhs = (ptrdiff_t)a1;
--     ptrdiff_t rhs = (ptrdiff_t)a2;
-- 
--     return lhs < rhs;
-- }
-- ```
def lean_isize_dec_lt := [JS_EXPR|throw new Error("lean_isize_dec_lt not implemented")]

-- ```lean
-- def ISize.decLe (a b : ISize) : Decidable (a ≤ b) :=
--   inferInstanceAs (Decidable (a.toBitVec.sle b.toBitVec))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_isize_dec_le(size_t a1, size_t a2) {
--     ptrdiff_t lhs = (ptrdiff_t)a1;
--     ptrdiff_t rhs = (ptrdiff_t)a2;
-- 
--     return lhs <= rhs;
-- }
-- ```
def lean_isize_dec_le := [JS_EXPR|throw new Error("lean_isize_dec_le not implemented")]

-- ============
-- Init.Data.String.Basic
-- ============

-- ```lean
-- def ByteArray.validateUTF8 (b : @& ByteArray) : Bool :=
--   go 0 (by simp)
-- where
--   @[semireducible]
--   go (i : Nat) (hi : i ≤ b.size) : Bool :=
--     if hi : i < b.size then
--       match h : validateUTF8At b i with
--       | false => false
--       | true => go (i + b[i].utf8ByteSize (isUTF8FirstByte_of_validateUTF8At h)) ?_
--     else
--       true
--   termination_by b.size - i
--   decreasing_by
--     have := b[i].utf8ByteSize_pos (isUTF8FirstByte_of_validateUTF8At h); omega
-- finally
--   all_goals rw [ByteArray.validateUTF8At_eq_isSome_utf8DecodeChar?] at h
--   · rw [← ByteArray.utf8Size_utf8DecodeChar (h := h)]
--     exact add_utf8Size_utf8DecodeChar_le_size
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8 lean_string_validate_utf8(b_obj_arg a) {
--     size_t pos = 0, i = 0;
--     return validate_utf8(lean_sarray_cptr(a), lean_sarray_size(a), pos, i);
-- }
-- ```
def lean_string_validate_utf8 := [JS_EXPR|throw new Error("lean_string_validate_utf8 not implemented")]

-- ```lean
-- def String.toList (s : String) : List Char :=
--   (String.Internal.toArray s).toList
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_string_data(obj_arg s) {
--     std::string tmp = string_to_std(s);
--     lean_dec_ref(s);
--     return string_to_list_core(tmp);
-- }
-- ```
--
-- ```lean
-- def String.data (b : String) : List Char :=
--   (String.Internal.toArray b).toList
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_string_data(obj_arg s) {
--     std::string tmp = string_to_std(s);
--     lean_dec_ref(s);
--     return string_to_list_core(tmp);
-- }
-- ```
def lean_string_data := [JS_EXPR|new TextEncoder( ).encode(#0)]

-- ```lean
-- instance decidableLT (s₁ s₂ : @& String) : Decidable (s₁ < s₂) :=
--   List.decidableLT s₁.toList s₂.toList
-- ```
--
-- ```cpp
-- static inline uint8_t lean_string_dec_lt(b_lean_obj_arg s1, b_lean_obj_arg s2) { return lean_string_lt(s1, s2); }
-- ```
def lean_string_dec_lt := [JS_EXPR|#0 < #1]

-- ```lean
-- def Pos.Raw.isValid (s : @&String) (p : @& Pos.Raw) : Bool :=
--   if h : p < s.rawEndPos then
--     (s.getUTF8Byte p h).IsUTF8FirstByte
--   else
--     p = s.rawEndPos
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8 lean_string_is_valid_pos(b_obj_arg s, b_obj_arg i0) {
--     if (!lean_is_scalar(i0)) {
--         /* See comment at string_utf8_get */
--         return false;
--     }
--     usize i = lean_unbox(i0);
--     usize sz = lean_string_size(s) - 1;
--     if (i > sz) return false;
--     if (i == sz) return true;
--     char const * str = lean_string_cstr(s);
--     return is_utf8_first_byte(str[i]);
-- }
-- ```
def lean_string_is_valid_pos := [JS_EXPR|throw new Error("lean_string_is_valid_pos not implemented")]

-- ```lean
-- def extract {s : @& String} (b e : @& s.Pos) : String where
--   toByteArray := s.toByteArray.extract b.offset.byteIdx e.offset.byteIdx
--   isValidUTF8 := b.isValidUTF8_extract e
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_string_utf8_extract_fast(b_obj_arg s, b_obj_arg b0, b_obj_arg e0) {
--     usize b = lean_unbox(b0);
--     usize e = lean_unbox(e0);
--     lean_assert(b <= lean_string_size(s) - 1);
--     lean_assert(e <= lean_string_size(s) - 1);
--     if (b >= e) return lean_mk_string_unchecked("", 0, 0);
--     char const * str = lean_string_cstr(s);
--     return lean_mk_string_from_bytes_unchecked(str + b, e - b);
-- }
-- ```
def lean_string_utf8_extract_fast := [JS_EXPR|throw new Error("lean_string_utf8_extract_fast is not implemented")]

-- ```lean
-- def decodeChar (s : @& String) (byteIdx : @& Nat) (h : (s.toByteArray.utf8DecodeChar? byteIdx).isSome) : Char :=
--   s.toByteArray.utf8DecodeChar byteIdx h
-- ```
--
-- ```cpp
-- static inline uint32_t lean_string_utf8_get_fast(b_lean_obj_arg s, b_lean_obj_arg i) {
--   char const * str = lean_string_cstr(s);
--   size_t idx = lean_unbox(i);
--   unsigned char c = (unsigned char)(str[idx]);
--   if ((c & 0x80) == 0) return c;
--   return lean_string_utf8_get_fast_cold(str, idx, lean_string_size(s), c);
-- }
-- ```
--
-- ```lean
-- def Pos.Raw.get' (s : @& String) (p : @& Pos.Raw) (h : ¬ p.atEnd s) : Char :=
--   match s with
--   | s => Pos.Raw.utf8GetAux s.toList 0 p
-- ```
--
-- ```cpp
-- static inline uint32_t lean_string_utf8_get_fast(b_lean_obj_arg s, b_lean_obj_arg i) {
--   char const * str = lean_string_cstr(s);
--   size_t idx = lean_unbox(i);
--   unsigned char c = (unsigned char)(str[idx]);
--   if ((c & 0x80) == 0) return c;
--   return lean_string_utf8_get_fast_cold(str, idx, lean_string_size(s), c);
-- }
-- ```
--
-- ```lean
-- def get' (s : @& String) (p : @& Pos.Raw) (h : ¬ p.atEnd s) : Char :=
--   match s with
--   | s => Pos.Raw.utf8GetAux s.toList 0 p
-- ```
--
-- ```cpp
-- static inline uint32_t lean_string_utf8_get_fast(b_lean_obj_arg s, b_lean_obj_arg i) {
--   char const * str = lean_string_cstr(s);
--   size_t idx = lean_unbox(i);
--   unsigned char c = (unsigned char)(str[idx]);
--   if ((c & 0x80) == 0) return c;
--   return lean_string_utf8_get_fast_cold(str, idx, lean_string_size(s), c);
-- }
-- ```
def lean_string_utf8_get_fast := [JS_EXPR|throw new Error("lean_string_utf8_get_fast not implemented")]

-- ```lean
-- def Pos.next {s : @& String} (pos : @& s.Pos) (h : pos ≠ s.endPos) : s.Pos :=
--   ofToSlice (Slice.Pos.next pos.toSlice (ne_of_apply_ne Pos.ofToSlice (by simpa)))
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_string_utf8_next_fast(b_lean_obj_arg s, b_lean_obj_arg i) {
--   char const * str = lean_string_cstr(s);
--   size_t idx = lean_unbox(i);
--   unsigned char c = (unsigned char)(str[idx]);
--   if ((c & 0x80) == 0) return lean_box(idx+1);
--   return lean_string_utf8_next_fast_cold(idx, c);
-- }
-- ```
--
-- ```lean
-- def Pos.Raw.next' (s : @& String) (p : @& Pos.Raw) (h : ¬ p.atEnd s) : Pos.Raw :=
--   let c := p.get s
--   p + c
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_string_utf8_next_fast(b_lean_obj_arg s, b_lean_obj_arg i) {
--   char const * str = lean_string_cstr(s);
--   size_t idx = lean_unbox(i);
--   unsigned char c = (unsigned char)(str[idx]);
--   if ((c & 0x80) == 0) return lean_box(idx+1);
--   return lean_string_utf8_next_fast_cold(idx, c);
-- }
-- ```
--
-- ```lean
-- def next' (s : @& String) (p : @& Pos.Raw) (h : ¬ p.atEnd s) : Pos.Raw :=
--   let c := p.get s
--   p + c
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_string_utf8_next_fast(b_lean_obj_arg s, b_lean_obj_arg i) {
--   char const * str = lean_string_cstr(s);
--   size_t idx = lean_unbox(i);
--   unsigned char c = (unsigned char)(str[idx]);
--   if ((c & 0x80) == 0) return lean_box(idx+1);
--   return lean_string_utf8_next_fast_cold(idx, c);
-- }
-- ```
def lean_string_utf8_next_fast := [JS_EXPR|throw new Error("lean_string_utf8_next_fast not implemented")]

-- ```lean
-- def Pos.Raw.get! (s : @& String) (p : @& Pos.Raw) : Char :=
--   match s with
--   | s => Pos.Raw.utf8GetAux s.toList 0 p
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint32 lean_string_utf8_get_bang(b_obj_arg s, b_obj_arg i0) {
--     if (!lean_is_scalar(i0)) {
--         return lean_string_utf8_get_panic();
--     }
--     usize i = lean_unbox(i0);
--     char const * str = lean_string_cstr(s);
--     usize size = lean_string_size(s) - 1;
--     if (i >= lean_string_size(s) - 1)
--         return lean_string_utf8_get_panic();
--     uint32 result;
--     if (lean_string_utf8_get_core(str, size, i, result))
--         return result;
--     else
--         return lean_string_utf8_get_panic();
-- }
-- ```
--
-- ```lean
-- def get! (s : @& String) (p : @& Pos.Raw) : Char :=
--   match s with
--   | s => Pos.Raw.utf8GetAux s.toList 0 p
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint32 lean_string_utf8_get_bang(b_obj_arg s, b_obj_arg i0) {
--     if (!lean_is_scalar(i0)) {
--         return lean_string_utf8_get_panic();
--     }
--     usize i = lean_unbox(i0);
--     char const * str = lean_string_cstr(s);
--     usize size = lean_string_size(s) - 1;
--     if (i >= lean_string_size(s) - 1)
--         return lean_string_utf8_get_panic();
--     uint32 result;
--     if (lean_string_utf8_get_core(str, size, i, result))
--         return result;
--     else
--         return lean_string_utf8_get_panic();
-- }
-- ```
def lean_string_utf8_get_bang := [JS_EXPR|throw new Error("lean_string_utf8_get_bang not implemented")]

-- ```lean
-- def Pos.Raw.next (s : @& String) (p : @& Pos.Raw) : Pos.Raw :=
--   let c := get s p
--   p + c
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_string_utf8_next(b_obj_arg s, b_obj_arg i0) {
--     if (!lean_is_scalar(i0)) {
--         /* See comment at string_utf8_get */
--         return lean_nat_add(i0, lean_box(1));
--     }
--     usize i = lean_unbox(i0);
--     char const * str = lean_string_cstr(s);
--     usize size       = lean_string_size(s) - 1;
--     /* `c.utf8ByteSize` is 1 when `i` is not a valid position in the reference implementation. */
--     if (i >= size) return lean_usize_to_nat(i+1);
--     unsigned c = static_cast<unsigned char>(str[i]);
--     if ((c & 0x80) == 0)    return lean_box(i+1);
--     if ((c & 0xe0) == 0xc0) return lean_box(i+2);
--     if ((c & 0xf0) == 0xe0) return lean_box(i+3);
--     if ((c & 0xf8) == 0xf0) return lean_box(i+4);
--     /* invalid UTF-8 encoded string */
--     return lean_box(i+1);
-- }
-- ```
--
-- ```lean
-- def next (s : @& String) (p : @& Pos.Raw) : Pos.Raw :=
--   let c := p.get s
--   p + c
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_string_utf8_next(b_obj_arg s, b_obj_arg i0) {
--     if (!lean_is_scalar(i0)) {
--         /* See comment at string_utf8_get */
--         return lean_nat_add(i0, lean_box(1));
--     }
--     usize i = lean_unbox(i0);
--     char const * str = lean_string_cstr(s);
--     usize size       = lean_string_size(s) - 1;
--     /* `c.utf8ByteSize` is 1 when `i` is not a valid position in the reference implementation. */
--     if (i >= size) return lean_usize_to_nat(i+1);
--     unsigned c = static_cast<unsigned char>(str[i]);
--     if ((c & 0x80) == 0)    return lean_box(i+1);
--     if ((c & 0xe0) == 0xc0) return lean_box(i+2);
--     if ((c & 0xf0) == 0xe0) return lean_box(i+3);
--     if ((c & 0xf8) == 0xf0) return lean_box(i+4);
--     /* invalid UTF-8 encoded string */
--     return lean_box(i+1);
-- }
-- ```
-- duplicate of lean_string_utf8_next:
-- def lean_string_utf8_next := [JS_EXPR|throw new Error("lean_string_utf8_next not implemented")]

-- ```lean
-- def Pos.Raw.prev : (@& String) → (@& Pos.Raw) → Pos.Raw
--   | s, p => utf8PrevAux s.toList 0 p
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_string_utf8_prev(b_obj_arg s, b_obj_arg i0) {
--     if (!lean_is_scalar(i0)) {
--         /* See comment at string_utf8_get */
--         return lean_nat_sub(i0, lean_box(1));
--     }
--     usize i  = lean_unbox(i0);
--     usize sz = lean_string_size(s) - 1;
--     if (i == 0) return lean_box(0);
--     else if (i > sz) return lean_box(i - 1);
--     i--;
--     char const * str = lean_string_cstr(s);
--     while (!is_utf8_first_byte(str[i])) {
--         lean_assert(i > 0);
--         i--;
--     }
--     return lean_box(i);
-- }
-- ```
--
-- ```lean
-- def prev : (@& String) → (@& Pos.Raw) → Pos.Raw
--   | s, p => Pos.Raw.utf8PrevAux s.toList 0 p
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_string_utf8_prev(b_obj_arg s, b_obj_arg i0) {
--     if (!lean_is_scalar(i0)) {
--         /* See comment at string_utf8_get */
--         return lean_nat_sub(i0, lean_box(1));
--     }
--     usize i  = lean_unbox(i0);
--     usize sz = lean_string_size(s) - 1;
--     if (i == 0) return lean_box(0);
--     else if (i > sz) return lean_box(i - 1);
--     i--;
--     char const * str = lean_string_cstr(s);
--     while (!is_utf8_first_byte(str[i])) {
--         lean_assert(i > 0);
--         i--;
--     }
--     return lean_box(i);
-- }
-- ```
def lean_string_utf8_prev := [JS_EXPR|throw new Error("lean_string_utf8_prev not implemented")]

-- ```lean
-- def Pos.Raw.atEnd : (@& String) → (@& Pos.Raw) → Bool
--   | s, p => p.byteIdx ≥ utf8ByteSize s
-- ```
--
-- ```cpp
-- static inline uint8_t lean_string_utf8_at_end(b_lean_obj_arg s, b_lean_obj_arg i) {
--     return !lean_is_scalar(i) || lean_unbox(i) >= lean_string_size(s) - 1;
-- }
-- ```
--
-- ```lean
-- def atEnd : (@& String) → (@& Pos.Raw) → Bool
--   | s, p => p.byteIdx ≥ utf8ByteSize s
-- ```
--
-- ```cpp
-- static inline uint8_t lean_string_utf8_at_end(b_lean_obj_arg s, b_lean_obj_arg i) {
--     return !lean_is_scalar(i) || lean_unbox(i) >= lean_string_size(s) - 1;
-- }
-- ```
-- duplicate of lean_string_utf8_at_end:
-- def lean_string_utf8_at_end := [JS_EXPR|throw new Error("lean_string_utf8_at_end not implemented")]

-- ```lean
-- def Pos.Raw.extract : (@& String) → (@& Pos.Raw) → (@& Pos.Raw) → String
--   | s, b, e => if b.byteIdx ≥ e.byteIdx then "" else ofList (go₁ s.toList 0 b e)
-- where
--   go₁ : List Char → Pos.Raw → Pos.Raw → Pos.Raw → List Char
--     | [],        _, _, _ => []
--     | s@(c::cs), i, b, e => if i = b then go₂ s i e else go₁ cs (i + c) b e
-- 
--   go₂ : List Char → Pos.Raw → Pos.Raw → List Char
--     | [],    _, _ => []
--     | c::cs, i, e => if i = e then [] else c :: go₂ cs (i + c) e
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_string_utf8_extract(b_obj_arg s, b_obj_arg b0, b_obj_arg e0) {
--     /* Replace non-scalar values with SIZE_MAX:
--     Non-scalar values are out of bounds here (see comment at string_utf8_get),
--     including SIZE_MAX, and values that are out of bounds all behave the same here */
--     usize b = lean_is_scalar(b0) ? lean_unbox(b0) : SIZE_MAX;
--     usize e = lean_is_scalar(e0) ? lean_unbox(e0) : SIZE_MAX;
--     char const * str = lean_string_cstr(s);
--     usize sz = lean_string_size(s) - 1;
--     if (b >= e || b >= sz) return lean_mk_string_unchecked("", 0, 0);
--     /* In the reference implementation if `b` is not pointing to a valid UTF8
--        character start position, the result is the empty string. */
--     if (!is_utf8_first_byte(str[b])) return lean_mk_string_unchecked("", 0, 0);
--     if (e > sz) e = sz;
--     lean_assert(b < e);
--     lean_assert(e > 0);
--     /* In the reference implementation if `e` is not pointing to a valid UTF8
--        character start position, it is assumed to be at the end. */
--     if (e < sz && !is_utf8_first_byte(str[e])) e = sz;
--     usize new_sz = e - b;
--     lean_assert(new_sz > 0);
--     return lean_mk_string_from_bytes_unchecked(lean_string_cstr(s) + b, new_sz);
-- }
-- ```
def lean_string_utf8_extract := [JS_EXPR|throw new Error("lean_string_utf8_extract not implemented")]

-- ============
-- Init.Data.String.Length
-- ============

-- ```lean
-- def length (b : @& String) : Nat :=
--   b.toList.length
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_string_length(b_lean_obj_arg s) { return lean_box(lean_string_len(s)); }
-- ```
-- duplicate of lean_string_length:
-- def lean_string_length := [JS_EXPR|(#0).length]

-- ============
-- Init.Data.Float.Float
-- ============

-- ```lean
-- attribute [extern "lean_float_to_bits"] Float.toModel
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint64_t lean_float_to_bits(double d)
-- {
--     if (isnan(d)) return quietNaN64;
--     return std::bit_cast<uint64_t>(d);
-- }
-- ```
--
-- ```lean
-- def Float.toBits : Float → UInt64 :=
--   fun a => a.toModel.toBits
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint64_t lean_float_to_bits(double d)
-- {
--     if (isnan(d)) return quietNaN64;
--     return std::bit_cast<uint64_t>(d);
-- }
-- ```
def lean_float_to_bits := [JS_EXPR|throw new Error("lean_float_to_bits not implemented")]

-- ```lean
-- attribute [extern "lean_float_of_bits"] Float.ofModel
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT double lean_float_of_bits(uint64_t u)
-- {
--     static_assert(sizeof(double) == sizeof(u), "`double` unexpected size.");
--     double ret = std::bit_cast<double>(u);
--     if (isnan(ret)) return std::numeric_limits<double>::quiet_NaN();
--     return ret;
-- }
-- ```
--
-- ```lean
-- def Float.ofBits : UInt64 → Float :=
--   fun a => .ofModel <| .ofBits a
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT double lean_float_of_bits(uint64_t u)
-- {
--     static_assert(sizeof(double) == sizeof(u), "`double` unexpected size.");
--     double ret = std::bit_cast<double>(u);
--     if (isnan(ret)) return std::numeric_limits<double>::quiet_NaN();
--     return ret;
-- }
-- ```
def lean_float_of_bits := [JS_EXPR|throw new Error("lean_float_of_bits not implemented")]

-- ```lean
-- def Float.add : Float → Float → Float :=
--   fun a b => .ofModel (a.toModel + b.toModel)
-- ```
--
-- ```cpp
-- static inline double lean_float_add(double a, double b) { return a + b; }
-- ```
def lean_float_add := [JS_EXPR|#0 + #1]

-- ```lean
-- def Float.sub : Float → Float → Float :=
--   fun a b => .ofModel (a.toModel - b.toModel)
-- ```
--
-- ```cpp
-- static inline double lean_float_sub(double a, double b) { return a - b; }
-- ```
def lean_float_sub := [JS_EXPR|#0 - #1]

-- ```lean
-- def Float.mul : Float → Float → Float :=
--   fun a b => .ofModel (a.toModel * b.toModel)
-- ```
--
-- ```cpp
-- static inline double lean_float_mul(double a, double b) { return a * b; }
-- ```
def lean_float_mul := [JS_EXPR|#0 * #1]

-- ```lean
-- def Float.div : Float → Float → Float :=
--   fun a b => .ofModel (a.toModel / b.toModel)
-- ```
--
-- ```cpp
-- static inline double lean_float_div(double a, double b) { return a / b; }
-- ```
def lean_float_div := [JS_EXPR|#0 / #1]

-- ```lean
-- def Float.neg : Float → Float :=
--   fun a => .ofModel (-a.toModel)
-- ```
--
-- ```cpp
-- static inline double lean_float_negate(double a) { return -a; }
-- ```
def lean_float_negate := [JS_EXPR|-#0]

-- ```lean
-- def Float.lt : Float → Float → Bool :=
--   fun a b => a.toModel < b.toModel
-- ```
--
-- ```cpp
-- static inline uint8_t lean_float_decLt(double a, double b) { return a < b; }
-- ```
--
-- ```lean
-- instance Float.decLt (a b : Float) : Decidable (a < b) :=
--   inferInstanceAs (Decidable (a.lt b))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_float_decLt(double a, double b) { return a < b; }
-- ```
def lean_float_decLt := [JS_EXPR|#0 < #1]

-- ```lean
-- def Float.le : Float → Float → Bool :=
--   fun a b => a.toModel ≤ b.toModel
-- ```
--
-- ```cpp
-- static inline uint8_t lean_float_decLe(double a, double b) { return a <= b; }
-- ```
--
-- ```lean
-- instance Float.decLe (a b : Float) : Decidable (a ≤ b) :=
--   inferInstanceAs (Decidable (a.le b))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_float_decLe(double a, double b) { return a <= b; }
-- ```
def lean_float_decLe := [JS_EXPR|#0 <= #1]

-- ```lean
-- def Float.beq (a b : Float) : Bool :=
--   a.toModel == b.toModel
-- ```
--
-- ```cpp
-- static inline uint8_t lean_float_beq(double a, double b) { return a == b; }
-- ```
def lean_float_beq := [JS_EXPR|#0 === #1]

-- ```lean
-- opaque Float.toString : Float → String
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT lean_obj_res lean_float_to_string(double a) {
--     if (isnan(a))
--         // override NaN because we don't want NaNs to be distinguishable
--         // because the sign bit / payload bits can be architecture-dependent
--         return mk_ascii_string_unchecked("NaN");
--     else
--         return mk_ascii_string_unchecked(std::to_string(a));
-- }
-- ```
def lean_float_to_string := [JS_EXPR|formatFloat(#0)]

-- ```lean
-- def Float.toUInt8 : Float → UInt8 :=
--   fun a => a.toModel.toUInt8
-- ```
--
-- ```cpp
-- static inline uint8_t lean_float_to_uint8(double a) {
--     return 0. <= a ? (a < 256. ? (uint8_t)a : UINT8_MAX) : 0;
-- }
-- ```
def lean_float_to_uint8 := [JS_EXPR|throw new Error("lean_float_to_uint8 not implemented")]

-- ```lean
-- def Float.toUInt16 : Float → UInt16 :=
--   fun a => a.toModel.toUInt16
-- ```
--
-- ```cpp
-- static inline uint16_t lean_float_to_uint16(double a) {
--     return 0. <= a ? (a < 65536. ? (uint16_t)a : UINT16_MAX) : 0;
-- }
-- ```
def lean_float_to_uint16 := [JS_EXPR|throw new Error("lean_float_to_uint16 not implemented")]

-- ```lean
-- def Float.toUInt32 : Float → UInt32 :=
--   fun a => a.toModel.toUInt32
-- ```
--
-- ```cpp
-- static inline uint32_t lean_float_to_uint32(double a) {
--     return 0. <= a ? (a < 4294967296. ? (uint32_t)a : UINT32_MAX) : 0;
-- }
-- ```
def lean_float_to_uint32 := [JS_EXPR|throw new Error("lean_float_to_uint32 not implemented")]

-- ```lean
-- def Float.toUInt64 : Float → UInt64 :=
--   fun a => a.toModel.toUInt64
-- ```
--
-- ```cpp
-- static inline uint64_t lean_float_to_uint64(double a) {
--     return 0. <= a ? (a < 18446744073709551616. ? (uint64_t)a : UINT64_MAX) : 0;
-- }
-- ```
def lean_float_to_uint64 := [JS_EXPR|throw new Error("lean_float_to_uint64 not implemented")]

-- ```lean
-- def Float.toUSize : Float → USize :=
--   fun a => a.toModel.toUSize
-- ```
--
-- ```cpp
-- static inline size_t lean_float_to_usize(double a) {
--     if (sizeof(size_t) == sizeof(uint64_t)) // NOLINT
--         return (size_t) lean_float_to_uint64(a); // NOLINT
--     else
--         return (size_t) lean_float_to_uint32(a); // NOLINT
-- }
-- ```
def lean_float_to_usize := [JS_EXPR|lean_float_to_uint64(#0)]

-- ```lean
-- def Float.isNaN : Float → Bool :=
--   fun a => a.toModel.isNaN
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8_t lean_float_isnan(double a) { return (bool) isnan(a); }
-- ```
def lean_float_isnan := [JS_EXPR|isNaN(#0)]

-- ```lean
-- def Float.isFinite : Float → Bool :=
--   fun a => a.toModel.isFinite
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8_t lean_float_isfinite(double a) { return (bool) isfinite(a); }
-- ```
def lean_float_isfinite := [JS_EXPR|isFinite(#0)]

-- ```lean
-- def Float.isInf : Float → Bool :=
--   fun a => a.toModel.isInf
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8_t lean_float_isinf(double a) { return (bool) isinf(a); }
-- ```
def lean_float_isinf := [JS_EXPR|!isFinite(#0) && !isNaN(#0)]

-- ```lean
-- opaque Float.frExp : Float → Float × Int
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_float_frexp(double a) {
--     object* r = lean_alloc_ctor(0, 2, 0);
--     int exp;
--     lean_ctor_set(r, 0, lean_box_float(frexp(a, &exp)));
--     lean_ctor_set(r, 1, isfinite(a) ? lean_int_to_int(exp) : lean_box(0));
--     return r;
-- }
-- ```
def lean_float_frexp := [JS_EXPR|throw new Error("lean_float_frexp not implemented")]

-- ```lean
-- def UInt8.toFloat (n : UInt8) : Float :=
--   .ofModel (.ofUInt8 n)
-- ```
--
-- ```cpp
-- static inline double lean_uint8_to_float(uint8_t a) { return (double) a; }
-- ```
def lean_uint8_to_float := [JS_EXPR|Number(#0)]

-- ```lean
-- def UInt16.toFloat (n : UInt16) : Float :=
--   .ofModel (.ofUInt16 n)
-- ```
--
-- ```cpp
-- static inline double lean_uint16_to_float(uint16_t a) { return (double) a; }
-- ```
def lean_uint16_to_float := [JS_EXPR|Number(#0)]

-- ```lean
-- def UInt32.toFloat (n : UInt32) : Float :=
--   .ofModel (.ofUInt32 n)
-- ```
--
-- ```cpp
-- static inline double lean_uint32_to_float(uint32_t a) { return (double) a; }
-- ```
def lean_uint32_to_float := [JS_EXPR|Number(#0)]

-- ```lean
-- def UInt64.toFloat (n : UInt64) : Float :=
--   .ofModel (.ofUInt64 n)
-- ```
--
-- ```cpp
-- static inline double lean_uint64_to_float(uint64_t a) { return (double) a; }
-- ```
def lean_uint64_to_float := [JS_EXPR|Number(#0)]

-- ```lean
-- def USize.toFloat (n : USize) : Float :=
--   .ofModel (.ofUSize n)
-- ```
--
-- ```cpp
-- static inline double lean_usize_to_float(size_t a) { return (double) a; }
-- ```
def lean_usize_to_float := [JS_EXPR|Number(#0)]

-- ```lean
-- opaque Float.sin : Float → Float
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def sin := [JS_EXPR|throw new Error("sin is not implemented")]

-- ```lean
-- opaque Float.cos : Float → Float
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def cos := [JS_EXPR|throw new Error("cos is not implemented")]

-- ```lean
-- opaque Float.tan : Float → Float
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def tan := [JS_EXPR|throw new Error("tan is not implemented")]

-- ```lean
-- opaque Float.asin : Float → Float
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def asin := [JS_EXPR|throw new Error("asin is not implemented")]

-- ```lean
-- opaque Float.acos : Float → Float
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def acos := [JS_EXPR|throw new Error("acos is not implemented")]

-- ```lean
-- opaque Float.atan : Float → Float
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def atan := [JS_EXPR|throw new Error("atan is not implemented")]

-- ```lean
-- opaque Float.atan2 (y x : Float) : Float
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def atan2 := [JS_EXPR|throw new Error("atan2 is not implemented")]

-- ```lean
-- opaque Float.sinh : Float → Float
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def sinh := [JS_EXPR|throw new Error("sinh is not implemented")]

-- ```lean
-- opaque Float.cosh : Float → Float
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def cosh := [JS_EXPR|throw new Error("cosh is not implemented")]

-- ```lean
-- opaque Float.tanh : Float → Float
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def tanh := [JS_EXPR|throw new Error("tanh is not implemented")]

-- ```lean
-- opaque Float.asinh : Float → Float
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def asinh := [JS_EXPR|throw new Error("asinh is not implemented")]

-- ```lean
-- opaque Float.acosh : Float → Float
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def acosh := [JS_EXPR|throw new Error("acosh is not implemented")]

-- ```lean
-- opaque Float.atanh : Float → Float
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def atanh := [JS_EXPR|throw new Error("atanh is not implemented")]

-- ```lean
-- opaque Float.exp (x : Float) : Float
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def exp := [JS_EXPR|throw new Error("exp is not implemented")]

-- ```lean
-- opaque Float.exp2 (x : Float) : Float
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def exp2 := [JS_EXPR|throw new Error("exp2 is not implemented")]

-- ```lean
-- opaque Float.log (x : Float) : Float
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def log := [JS_EXPR|throw new Error("log is not implemented")]

-- ```lean
-- opaque Float.log2 : Float → Float
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def log2 := [JS_EXPR|throw new Error("log2 is not implemented")]

-- ```lean
-- opaque Float.log10 : Float → Float
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def log10 := [JS_EXPR|throw new Error("log10 is not implemented")]

-- ```lean
-- opaque Float.pow : Float → Float → Float
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def pow := [JS_EXPR|throw new Error("pow is not implemented")]

-- ```lean
-- def Float.sqrt : Float → Float :=
--   fun a => .ofModel a.toModel.sqrt
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def sqrt := [JS_EXPR|throw new Error("sqrt is not implemented")]

-- ```lean
-- opaque Float.cbrt : Float → Float
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def cbrt := [JS_EXPR|throw new Error("cbrt is not implemented")]

-- ```lean
-- opaque Float.ceil : Float → Float
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def ceil := [JS_EXPR|throw new Error("ceil is not implemented")]

-- ```lean
-- opaque Float.floor : Float → Float
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def floor := [JS_EXPR|throw new Error("floor is not implemented")]

-- ```lean
-- opaque Float.round : Float → Float
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def round := [JS_EXPR|throw new Error("round is not implemented")]

-- ```lean
-- def Float.abs : Float → Float :=
--   fun a => .ofModel a.toModel.abs
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def fabs := [JS_EXPR|throw new Error("fabs is not implemented")]

-- ```lean
-- opaque Float.scaleB (x : Float) (i : @& Int) : Float
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT double lean_float_scaleb(double a, b_lean_obj_arg b) {
--    if (lean_is_scalar(b)) {
--      return scalbn(a, lean_scalar_to_int(b));
--    } else if (a == 0 || mpz_value(b).is_neg()) {
--      return 0;
--    } else {
--      return a * (1.0 / 0.0);
--    }
-- }
-- ```
def lean_float_scaleb := [JS_EXPR|#0 * Math.pow(2, Number(#1))]

-- ============
-- Init.Data.Float.Float32
-- ============

-- ```lean
-- attribute [extern "lean_float32_to_bits"] Float32.toModel
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint32_t lean_float32_to_bits(float d)
-- {
--     if (isnan(d)) return quietNaN32;
--     return std::bit_cast<uint32_t>(d);
-- }
-- ```
--
-- ```lean
-- def Float32.toBits : Float32 → UInt32 :=
--   fun a => a.toModel.toBits
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint32_t lean_float32_to_bits(float d)
-- {
--     if (isnan(d)) return quietNaN32;
--     return std::bit_cast<uint32_t>(d);
-- }
-- ```
def lean_float32_to_bits := [JS_EXPR|throw new Error("lean_float32_to_bits not implemented")]

-- ```lean
-- attribute [extern "lean_float32_of_bits"] Float32.ofModel
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT float lean_float32_of_bits(uint32_t u)
-- {
--     static_assert(sizeof(float) == sizeof(u), "`float` unexpected size.");
--     float ret = std::bit_cast<float>(u);
--     if (isnan(ret)) ret = std::numeric_limits<float>::quiet_NaN();
--     return ret;
-- }
-- ```
--
-- ```lean
-- def Float32.ofBits : UInt32 → Float32 :=
--   fun a => .ofModel <| .ofBits a
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT float lean_float32_of_bits(uint32_t u)
-- {
--     static_assert(sizeof(float) == sizeof(u), "`float` unexpected size.");
--     float ret = std::bit_cast<float>(u);
--     if (isnan(ret)) ret = std::numeric_limits<float>::quiet_NaN();
--     return ret;
-- }
-- ```
def lean_float32_of_bits := [JS_EXPR|throw new Error("lean_float32_of_bits not implemented")]

-- ```lean
-- def Float32.add : Float32 → Float32 → Float32 :=
--   fun a b => .ofModel (a.toModel + b.toModel)
-- ```
--
-- ```cpp
-- static inline float lean_float32_add(float a, float b) { return a + b; }
-- ```
def lean_float32_add := [JS_EXPR|f32(#0 + #1)]

-- ```lean
-- def Float32.sub : Float32 → Float32 → Float32 :=
--   fun a b => .ofModel (a.toModel - b.toModel)
-- ```
--
-- ```cpp
-- static inline float lean_float32_sub(float a, float b) { return a - b; }
-- ```
def lean_float32_sub := [JS_EXPR|f32(#0 - #1)]

-- ```lean
-- def Float32.mul : Float32 → Float32 → Float32 :=
--   fun a b => .ofModel (a.toModel * b.toModel)
-- ```
--
-- ```cpp
-- static inline float lean_float32_mul(float a, float b) { return a * b; }
-- ```
def lean_float32_mul := [JS_EXPR|f32(#0 * #1)]

-- ```lean
-- def Float32.div : Float32 → Float32 → Float32 :=
--   fun a b => .ofModel (a.toModel / b.toModel)
-- ```
--
-- ```cpp
-- static inline float lean_float32_div(float a, float b) { return a / b; }
-- ```
def lean_float32_div := [JS_EXPR|f32(#0 / #1)]

-- ```lean
-- def Float32.neg : Float32 → Float32 :=
--   fun a => .ofModel (-a.toModel)
-- ```
--
-- ```cpp
-- static inline float lean_float32_negate(float a) { return -a; }
-- ```
def lean_float32_negate := [JS_EXPR|f32(-#0)]

-- ```lean
-- def Float32.lt : Float32 → Float32 → Bool :=
--   fun a b => a.toModel < b.toModel
-- ```
--
-- ```cpp
-- static inline uint8_t lean_float32_decLt(float a, float b) { return a < b; }
-- ```
--
-- ```lean
-- instance Float32.decLt (a b : Float32) : Decidable (a < b) :=
--   inferInstanceAs (Decidable (a.lt b))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_float32_decLt(float a, float b) { return a < b; }
-- ```
def lean_float32_decLt := [JS_EXPR|throw new Error("lean_float32_decLt not implemented")]

-- ```lean
-- def Float32.le : Float32 → Float32 → Bool :=
--   fun a b => a.toModel ≤ b.toModel
-- ```
--
-- ```cpp
-- static inline uint8_t lean_float32_decLe(float a, float b) { return a <= b; }
-- ```
--
-- ```lean
-- instance Float32.decLe (a b : Float32) : Decidable (a ≤ b) :=
--   inferInstanceAs (Decidable (a.le b))
-- ```
--
-- ```cpp
-- static inline uint8_t lean_float32_decLe(float a, float b) { return a <= b; }
-- ```
def lean_float32_decLe := [JS_EXPR|throw new Error("lean_float32_decLe not implemented")]

-- ```lean
-- def Float32.beq (a b : Float32) : Bool :=
--   a.toModel == b.toModel
-- ```
--
-- ```cpp
-- static inline uint8_t lean_float32_beq(float a, float b) { return a == b; }
-- ```
def lean_float32_beq := [JS_EXPR|#0 === #1]

-- ```lean
-- opaque Float32.toString : Float32 → String
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT lean_obj_res lean_float32_to_string(float a) {
--     if (isnan(a))
--         // override NaN because we don't want NaNs to be distinguishable
--         // because the sign bit / payload bits can be architecture-dependent
--         return mk_ascii_string_unchecked("NaN");
--     else
--         return mk_ascii_string_unchecked(std::to_string(a));
-- }
-- ```
def lean_float32_to_string := [JS_EXPR|String(#0)]

-- ```lean
-- def Float32.toUInt8 : Float32 → UInt8 :=
--   fun a => a.toModel.toUInt8
-- ```
--
-- ```cpp
-- static inline uint8_t lean_float32_to_uint8(float a) {
--     return 0. <= a ? (a < 256. ? (uint8_t)a : UINT8_MAX) : 0;
-- }
-- ```
def lean_float32_to_uint8 := [JS_EXPR|throw new Error("lean_float32_to_uint8 not implemented")]

-- ```lean
-- def Float32.toUInt16 : Float32 → UInt16 :=
--   fun a => a.toModel.toUInt16
-- ```
--
-- ```cpp
-- static inline uint16_t lean_float32_to_uint16(float a) {
--     return 0. <= a ? (a < 65536. ? (uint16_t)a : UINT16_MAX) : 0;
-- }
-- ```
def lean_float32_to_uint16 := [JS_EXPR|throw new Error("lean_float32_to_uint16 not implemented")]

-- ```lean
-- def Float32.toUInt32 : Float32 → UInt32 :=
--   fun a => a.toModel.toUInt32
-- ```
--
-- ```cpp
-- static inline uint32_t lean_float32_to_uint32(float a) {
--     return 0. <= a ? (a < 4294967296. ? (uint32_t)a : UINT32_MAX) : 0;
-- }
-- ```
def lean_float32_to_uint32 := [JS_EXPR|throw new Error("lean_float32_to_uint32 not implemented")]

-- ```lean
-- def Float32.toUInt64 : Float32 → UInt64 :=
--   fun a => a.toModel.toUInt64
-- ```
--
-- ```cpp
-- static inline uint64_t lean_float32_to_uint64(float a) {
--     return 0. <= a ? (a < 18446744073709551616. ? (uint64_t)a : UINT64_MAX) : 0;
-- }
-- ```
def lean_float32_to_uint64 := [JS_EXPR|throw new Error("lean_float32_to_uint64 not implemented")]

-- ```lean
-- def Float32.toUSize : Float32 → USize :=
--   fun a => a.toModel.toUSize
-- ```
--
-- ```cpp
-- static inline size_t lean_float32_to_usize(float a) {
--     if (sizeof(size_t) == sizeof(uint64_t)) // NOLINT
--         return (size_t) lean_float32_to_uint64(a); // NOLINT
--     else
--         return (size_t) lean_float32_to_uint32(a); // NOLINT
-- }
-- ```
def lean_float32_to_usize := [JS_EXPR|throw new Error("lean_float32_to_usize not implemented")]

-- ```lean
-- def Float32.isNaN : Float32 → Bool :=
--   fun a => a.toModel.isNaN
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8_t lean_float32_isnan(float a) { return (bool) isnan(a); }
-- ```
def lean_float32_isnan := [JS_EXPR|isNaN(#0)]

-- ```lean
-- def Float32.isFinite : Float32 → Bool :=
--   fun a => a.toModel.isFinite
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8_t lean_float32_isfinite(float a) { return (bool) isfinite(a); }
-- ```
def lean_float32_isfinite := [JS_EXPR|isFinite(#0)]

-- ```lean
-- def Float32.isInf : Float32 → Bool :=
--   fun a => a.toModel.isInf
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8_t lean_float32_isinf(float a) { return (bool) isinf(a); }
-- ```
def lean_float32_isinf := [JS_EXPR|!isFinite(#0) && !isNaN(#0)]

-- ```lean
-- opaque Float32.frExp : Float32 → Float32 × Int
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_float32_frexp(float a) {
--     object* r = lean_alloc_ctor(0, 2, 0);
--     int exp;
--     lean_ctor_set(r, 0, lean_box_float32(frexp(a, &exp)));
--     lean_ctor_set(r, 1, isfinite(a) ? lean_int_to_int(exp) : lean_box(0));
--     return r;
-- }
-- ```
def lean_float32_frexp := [JS_EXPR|throw new Error("lean_float32_frexp not implemented")]

-- ```lean
-- def UInt8.toFloat32 (n : UInt8) : Float32 :=
--   .ofModel (.ofUInt8 n)
-- ```
--
-- ```cpp
-- static inline float lean_uint8_to_float32(uint8_t a) { return (float) a; }
-- ```
def lean_uint8_to_float32 := [JS_EXPR|f32(#0)]

-- ```lean
-- def UInt16.toFloat32 (n : UInt16) : Float32 :=
--   .ofModel (.ofUInt16 n)
-- ```
--
-- ```cpp
-- static inline float lean_uint16_to_float32(uint16_t a) { return (float) a; }
-- ```
def lean_uint16_to_float32 := [JS_EXPR|f32(#0)]

-- ```lean
-- def UInt32.toFloat32 (n : UInt32) : Float32 :=
--   .ofModel (.ofUInt32 n)
-- ```
--
-- ```cpp
-- static inline float lean_uint32_to_float32(uint32_t a) { return (float) a; }
-- ```
def lean_uint32_to_float32 := [JS_EXPR|f32(#0)]

-- ```lean
-- def UInt64.toFloat32 (n : UInt64) : Float32 :=
--   .ofModel (.ofUInt64 n)
-- ```
--
-- ```cpp
-- static inline float lean_uint64_to_float32(uint64_t a) { return (float) a; }
-- ```
def lean_uint64_to_float32 := [JS_EXPR|f32(Number(#0))]

-- ```lean
-- def USize.toFloat32 (n : USize) : Float32 :=
--   .ofModel (.ofUSize n)
-- ```
--
-- ```cpp
-- static inline float lean_usize_to_float32(size_t a) { return (float) a; }
-- ```
def lean_usize_to_float32 := [JS_EXPR|f32(Number(#0))]

-- ```lean
-- opaque Float32.sin : Float32 → Float32
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def sinf := [JS_EXPR|throw new Error("sinf is not implemented")]

-- ```lean
-- opaque Float32.cos : Float32 → Float32
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def cosf := [JS_EXPR|throw new Error("cosf is not implemented")]

-- ```lean
-- opaque Float32.tan : Float32 → Float32
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def tanf := [JS_EXPR|throw new Error("tanf is not implemented")]

-- ```lean
-- opaque Float32.asin : Float32 → Float32
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def asinf := [JS_EXPR|throw new Error("asinf is not implemented")]

-- ```lean
-- opaque Float32.acos : Float32 → Float32
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def acosf := [JS_EXPR|throw new Error("acosf is not implemented")]

-- ```lean
-- opaque Float32.atan : Float32 → Float32
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def atanf := [JS_EXPR|throw new Error("atanf is not implemented")]

-- ```lean
-- opaque Float32.atan2 : Float32 → Float32 → Float32
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def atan2f := [JS_EXPR|throw new Error("atan2f is not implemented")]

-- ```lean
-- opaque Float32.sinh : Float32 → Float32
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def sinhf := [JS_EXPR|throw new Error("sinhf is not implemented")]

-- ```lean
-- opaque Float32.cosh : Float32 → Float32
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def coshf := [JS_EXPR|throw new Error("coshf is not implemented")]

-- ```lean
-- opaque Float32.tanh : Float32 → Float32
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def tanhf := [JS_EXPR|throw new Error("tanhf is not implemented")]

-- ```lean
-- opaque Float32.asinh : Float32 → Float32
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def asinhf := [JS_EXPR|throw new Error("asinhf is not implemented")]

-- ```lean
-- opaque Float32.acosh : Float32 → Float32
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def acoshf := [JS_EXPR|throw new Error("acoshf is not implemented")]

-- ```lean
-- opaque Float32.atanh : Float32 → Float32
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def atanhf := [JS_EXPR|throw new Error("atanhf is not implemented")]

-- ```lean
-- opaque Float32.exp : Float32 → Float32
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def expf := [JS_EXPR|throw new Error("expf is not implemented")]

-- ```lean
-- opaque Float32.exp2 : Float32 → Float32
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def exp2f := [JS_EXPR|throw new Error("exp2f is not implemented")]

-- ```lean
-- opaque Float32.log : Float32 → Float32
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def logf := [JS_EXPR|throw new Error("logf is not implemented")]

-- ```lean
-- opaque Float32.log2 : Float32 → Float32
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def log2f := [JS_EXPR|throw new Error("log2f is not implemented")]

-- ```lean
-- opaque Float32.log10 : Float32 → Float32
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def log10f := [JS_EXPR|throw new Error("log10f is not implemented")]

-- ```lean
-- opaque Float32.pow : Float32 → Float32 → Float32
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def powf := [JS_EXPR|throw new Error("powf is not implemented")]

-- ```lean
-- def Float32.sqrt : Float32 → Float32 :=
--   fun a => .ofModel a.toModel.sqrt
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def sqrtf := [JS_EXPR|throw new Error("sqrtf is not implemented")]

-- ```lean
-- opaque Float32.cbrt : Float32 → Float32
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def cbrtf := [JS_EXPR|throw new Error("cbrtf is not implemented")]

-- ```lean
-- opaque Float32.ceil : Float32 → Float32
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def ceilf := [JS_EXPR|throw new Error("ceilf is not implemented")]

-- ```lean
-- opaque Float32.floor : Float32 → Float32
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def floorf := [JS_EXPR|throw new Error("floorf is not implemented")]

-- ```lean
-- opaque Float32.round : Float32 → Float32
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def roundf := [JS_EXPR|throw new Error("roundf is not implemented")]

-- ```lean
-- def Float32.abs : Float32 → Float32 :=
--   fun a => .ofModel a.toModel.abs
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def fabsf := [JS_EXPR|throw new Error("fabsf is not implemented")]

-- ```lean
-- opaque Float32.scaleB (x : Float32) (i : @& Int) : Float32
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT float lean_float32_scaleb(float a, b_lean_obj_arg b) {
--    if (lean_is_scalar(b)) {
--      return scalbn(a, lean_scalar_to_int(b));
--    } else if (a == 0 || mpz_value(b).is_neg()) {
--      return 0;
--    } else {
--      return a * (1.0 / 0.0);
--    }
-- }
-- ```
def lean_float32_scaleb := [JS_EXPR|f32(#0 * Math.pow(2, #1))]

-- ```lean
-- opaque Float32.toFloat : Float32 → Float
-- ```
--
-- ```cpp
-- static inline double lean_float32_to_float(float a) { return (double)a; }
-- ```
def lean_float32_to_float := [JS_EXPR|#0]

-- ```lean
-- opaque Float.toFloat32 : Float → Float32
-- ```
--
-- ```cpp
-- static inline float lean_float_to_float32(double a) { return (float)a; }
-- ```
def lean_float_to_float32 := [JS_EXPR|f32(#0)]

-- ============
-- Init.Data.FloatArray.Basic
-- ============

-- ```lean
-- attribute [extern "lean_float_array_mk"] FloatArray.mk
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_float_array_mk(obj_arg a) {
--     usize sz      = lean_array_size(a);
--     obj_res r     = lean_alloc_sarray(sizeof(double), sz, sz); // NOLINT
--     object ** it  = lean_array_cptr(a);
--     object ** end = it + sz;
--     double * dest = reinterpret_cast<double*>(lean_sarray_cptr(r));
--     for (; it != end; ++it, ++dest) {
--         *dest = lean_unbox_float(*it);
--     }
--     lean_dec(a);
--     return r;
-- }
-- ```
def lean_float_array_mk := [JS_EXPR| new Float64Array(#0) ]

-- ```lean
-- attribute [extern "lean_float_array_data"] FloatArray.data
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_float_array_data(obj_arg a) {
--     usize sz       = lean_sarray_size(a);
--     obj_res r      = lean_alloc_array(sz, sz);
--     double * it    = reinterpret_cast<double*>(lean_sarray_cptr(a));
--     double * end   = it+sz;
--     object ** dest = lean_array_cptr(r);
--     for (; it != end; ++it, ++dest) {
--         *dest = lean_box_float(*it);
--     }
--     lean_dec(a);
--     return r;
-- }
-- ```
def lean_float_array_data := [JS_EXPR| #0]

-- ```lean
-- def emptyWithCapacity (c : @& Nat) : FloatArray :=
--   { data := #[] }
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_mk_empty_float_array(b_lean_obj_arg capacity) {
--     if (!lean_is_scalar(capacity)) lean_internal_panic_out_of_memory();
--     return lean_alloc_sarray(sizeof(double), 0, lean_unbox(capacity)); // NOLINT
-- }
-- ```
def lean_mk_empty_float_array := [JS_EXPR| new Float64Array(0) ]

-- ```lean
-- def push : FloatArray → Float → FloatArray
--   | ⟨ds⟩, b => ⟨ds.push b⟩
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_float_array_push(obj_arg a, double d) {
--     object * r = lean_sarray_ensure_exclusive(lean_sarray_ensure_capacity(a, lean_sarray_size(a) + 1, /* exact */ false));
--     size_t & sz  = lean_to_sarray(r)->m_size;
--     double * it  = reinterpret_cast<double*>(lean_sarray_cptr(r)) + sz;
--     *it = d;
--     sz++;
--     return r;
-- }
-- ```
def lean_float_array_push := [JS_FUNC|inputs(fa, val)|returns=newData|
  const newData = new Float64Array(fa.length + 1);
  newData.set(fa);
  newData[fa.length] = val;
]

-- ```lean
-- def size : (@& FloatArray) → Nat
--   | ⟨ds⟩ => ds.size
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_float_array_size(b_lean_obj_arg a) {
--     return lean_box(lean_sarray_size(a));
-- }
-- ```
def lean_float_array_size := [JS_EXPR| (#0).length]

-- ```lean
-- def usize (a : @& FloatArray) : USize :=
--   a.size.toUSize
-- ```
--
-- ```cpp
-- static inline size_t lean_sarray_size(b_lean_obj_arg o) { return lean_to_sarray(o)->m_size; }
-- ```
-- duplicate of lean_sarray_size:
-- def lean_sarray_size := [JS_EXPR| (#0).length]

-- ```lean
-- def uget : (a : @& FloatArray) → (i : USize) → i.toNat < a.size → Float
--   | ⟨ds⟩, i, h => ds[i]
-- ```
--
-- ```cpp
-- static inline double lean_float_array_uget(b_lean_obj_arg a, size_t i) {
--     return lean_float_array_cptr(a)[i];
-- }
-- ```
def lean_float_array_uget := [JS_EXPR| (#0)[#1]]

-- ```lean
-- def get! : (@& FloatArray) → (@& Nat) → Float
--   | ⟨ds⟩, i => ds[i]!
-- ```
--
-- ```cpp
-- static inline double lean_float_array_get(b_lean_obj_arg a, b_lean_obj_arg i) {
--     if (lean_is_scalar(i)) {
--         size_t idx = lean_unbox(i);
--         return idx < lean_sarray_size(a) ? lean_float_array_uget(a, idx) : 0.0;
--     } else {
--         /* The index must be out of bounds. Otherwise we would be out of memory. */
--         return 0.0;
--     }
-- }
-- ```
def lean_float_array_get := [JS_EXPR| ((#1 < 0 || #1 >= (#0).length) ? NaN : (#0)[#1])]

-- ```lean
-- def uset : (a : FloatArray) → (i : USize) → Float → (h : i.toNat < a.size := by get_elem_tactic) → FloatArray
--   | ⟨ds⟩, i, v, h => ⟨ds.uset i v h⟩
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_float_array_uset(lean_obj_arg a, size_t i, double d) {
--     lean_obj_res r;
--     if (lean_is_exclusive(a)) r = a;
--     else r = lean_copy_float_array(a);
--     double * it = lean_float_array_cptr(r) + i;
--     *it = d;
--     return r;
-- }
-- ```
def lean_float_array_uset := [JS_FUNC|inputs(fa, i, val)|returns=newData|
  const newData = new Float64Array(fa);
  newData[i] = val;
]

-- ```lean
-- def set! : FloatArray → (@& Nat) → Float → FloatArray
--   | ⟨ds⟩, i, d => ⟨ds.set! i d⟩
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_float_array_set(lean_obj_arg a, b_lean_obj_arg i, double d) {
--     if (!lean_is_scalar(i)) {
--         return a;
--     } else {
--         size_t idx = lean_unbox(i);
--         if (idx >= lean_sarray_size(a)) {
--             return a;
--         } else {
--             return lean_float_array_uset(a, idx, d);
--         }
--     }
-- }
-- ```
def lean_float_array_set := lean_float_array_uset

-- ============
-- Init.Data.Ord.String
-- ============

-- ```lean
-- def compare (s₁ s₂ : @& String) : Ordering :=
--   compareOfLessAndEq s₁ s₂
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8_t lean_string_compare(b_obj_arg s1, b_obj_arg s2) {
--     size_t sz1 = lean_string_size(s1) - 1; // ignore null char in the end
--     size_t sz2 = lean_string_size(s2) - 1; // ignore null char in the end
--     int r      = std::memcmp(lean_string_cstr(s1), lean_string_cstr(s2), std::min(sz1, sz2));
--     if (r < 0) return 0;
--     if (r > 0) return 2;
--     if (sz1 < sz2) return 0;
--     if (sz1 > sz2) return 2;
--     return 1;
-- }
-- ```
def lean_string_compare := [JS_EXPR|throw new Error("lean_string_compare is not implemented")]

-- ============
-- Init.Data.SInt.Float
-- ============

-- ```lean
-- def Float.toInt8 : Float → Int8 :=
--   fun a => a.toModel.toInt8
-- ```
--
-- ```cpp
-- static inline uint8_t lean_float_to_int8(double a) {
--     int8_t result;
--     if (lean_float_isnan(a)) result = 0;
--     else result = -129. < a ? (a < 128. ? (int8_t)a : INT8_MAX) : INT8_MIN;
--     return (uint8_t)result;
-- }
-- ```
def lean_float_to_int8 := [JS_EXPR|throw new Error("lean_float_to_int8 not implemented")]

-- ```lean
-- def Float.toInt16 : Float → Int16 :=
--   fun a => a.toModel.toInt16
-- ```
--
-- ```cpp
-- static inline uint16_t lean_float_to_int16(double a) {
--     int16_t result;
--     if (lean_float_isnan(a)) result = 0;
--     else result = -32769. < a ? (a < 32768. ? (int16_t)a : INT16_MAX) : INT16_MIN;
--     return (uint16_t)result;
-- }
-- ```
def lean_float_to_int16 := [JS_EXPR|throw new Error("lean_float_to_int16 not implemented")]

-- ```lean
-- def Float.toInt32 : Float → Int32 :=
--   fun a => a.toModel.toInt32
-- ```
--
-- ```cpp
-- static inline uint32_t lean_float_to_int32(double a) {
--     int32_t result;
--     if (lean_float_isnan(a)) result = 0;
--     else result = -2147483649. < a ? (a < 2147483648. ? (int32_t)a : INT32_MAX) : INT32_MIN;
--     return (uint32_t)result;
-- }
-- ```
def lean_float_to_int32 := [JS_EXPR|throw new Error("lean_float_to_int32 not implemented")]

-- ```lean
-- def Float.toInt64 : Float → Int64 :=
--   fun a => a.toModel.toInt64
-- ```
--
-- ```cpp
-- static inline uint64_t lean_float_to_int64(double a) {
--     int64_t result;
--     if (lean_float_isnan(a)) result = 0;
--     else result = -9223372036854775809. < a ? (a < 9223372036854775808. ? (int64_t)a : INT64_MAX) : INT64_MIN;
--     return (uint64_t)result;
-- }
-- ```
def lean_float_to_int64 := [JS_EXPR|throw new Error("lean_float_to_int64 not implemented")]

-- ```lean
-- def Float.toISize : Float → ISize :=
--   fun a => a.toModel.toISize
-- ```
--
-- ```cpp
-- static inline size_t lean_float_to_isize(double a) {
--     if (sizeof(size_t) == sizeof(uint64_t)) {
--         ptrdiff_t result;
--         if (lean_float_isnan(a)) result = 0;
--         else result = -9223372036854775809. < a ? (a < 9223372036854775808. ? (ptrdiff_t)a : INT64_MAX) : INT64_MIN;
--         return (size_t)result;
--     } else {
--         ptrdiff_t result;
--         if (lean_float_isnan(a)) result = 0;
--         else result = -2147483649. < a ? (a < 2147483648. ? (ptrdiff_t)a : INT32_MAX) : INT32_MIN;
--         return (size_t)result;
--     }
-- }
-- ```
def lean_float_to_isize := [JS_EXPR|throw new Error("lean_float_to_isize not implemented")]

-- ```lean
-- def Int8.toFloat (n : Int8) : Float :=
--   .ofModel (.ofInt8 n)
-- ```
--
-- ```cpp
-- static inline double lean_int8_to_float(uint8_t a) { return (double)(int8_t) a; }
-- ```
def lean_int8_to_float := [JS_EXPR|throw new Error("lean_int8_to_float not implemented")]

-- ```lean
-- def Int16.toFloat (n : Int16) : Float :=
--   .ofModel (.ofInt16 n)
-- ```
--
-- ```cpp
-- static inline double lean_int16_to_float(uint16_t a) { return (double)(int16_t) a; }
-- ```
def lean_int16_to_float := [JS_EXPR|throw new Error("lean_int16_to_float not implemented")]

-- ```lean
-- def Int32.toFloat (n : Int32) : Float :=
--   .ofModel (.ofInt32 n)
-- ```
--
-- ```cpp
-- static inline double lean_int32_to_float(uint32_t a) { return (double)(int32_t) a; }
-- ```
def lean_int32_to_float := [JS_EXPR|throw new Error("lean_int32_to_float not implemented")]

-- ```lean
-- def Int64.toFloat (n : Int64) : Float :=
--   .ofModel (.ofInt64 n)
-- ```
--
-- ```cpp
-- static inline double lean_int64_to_float(uint64_t a) { return (double)(int64_t) a; }
-- ```
def lean_int64_to_float := [JS_EXPR|throw new Error("lean_int64_to_float not implemented")]

-- ```lean
-- def ISize.toFloat (n : ISize) : Float :=
--   .ofModel (.ofISize n)
-- ```
--
-- ```cpp
-- static inline double lean_isize_to_float(size_t a) { return (double)(ptrdiff_t) a; }
-- ```
def lean_isize_to_float := [JS_EXPR|throw new Error("lean_isize_to_float not implemented")]

-- ============
-- Init.Data.SInt.Float32
-- ============

-- ```lean
-- def Float32.toInt8 : Float32 → Int8 :=
--   fun a => a.toModel.toInt8
-- ```
--
-- ```cpp
-- static inline uint8_t lean_float32_to_int8(float a) {
--     int8_t result;
--     if (lean_float32_isnan(a)) result = 0;
--     else result = -129. < a ? (a < 128. ? (int8_t)a : INT8_MAX) : INT8_MIN;
--     return (uint8_t)result;
-- }
-- ```
def lean_float32_to_int8 := [JS_EXPR|throw new Error("lean_float32_to_int8 not implemented")]

-- ```lean
-- def Float32.toInt16 : Float32 → Int16 :=
--   fun a => a.toModel.toInt16
-- ```
--
-- ```cpp
-- static inline uint16_t lean_float32_to_int16(float a) {
--     int16_t result;
--     if (lean_float32_isnan(a)) result = 0;
--     else result = -32769. < a ? (a < 32768. ? (int16_t)a : INT16_MAX) : INT16_MIN;
--     return (uint16_t)result;
-- }
-- ```
def lean_float32_to_int16 := [JS_EXPR|throw new Error("lean_float32_to_int16 not implemented")]

-- ```lean
-- def Float32.toInt32 : Float32 → Int32 :=
--   fun a => a.toModel.toInt32
-- ```
--
-- ```cpp
-- static inline uint32_t lean_float32_to_int32(float a) {
--     int32_t result;
--     if (lean_float32_isnan(a)) result = 0;
--     else result = -2147483649. < a ? (a < 2147483648. ? (int32_t)a : INT32_MAX) : INT32_MIN;
--     return (uint32_t)result;
-- }
-- ```
def lean_float32_to_int32 := [JS_EXPR|throw new Error("lean_float32_to_int32 not implemented")]

-- ```lean
-- def Float32.toInt64 : Float32 → Int64 :=
--   fun a => a.toModel.toInt64
-- ```
--
-- ```cpp
-- static inline uint64_t lean_float32_to_int64(float a) {
--     int64_t result;
--     if (lean_float32_isnan(a)) result = 0;
--     else result = -9223372036854775809. < a ? (a < 9223372036854775808. ? (int64_t)a : INT64_MAX) : INT64_MIN;
--     return (uint64_t)result;
-- }
-- ```
def lean_float32_to_int64 := [JS_EXPR|throw new Error("lean_float32_to_int64 not implemented")]

-- ```lean
-- def Float32.toISize : Float32 → ISize :=
--   fun a => a.toModel.toISize
-- ```
--
-- ```cpp
-- static inline size_t lean_float32_to_isize(float a) {
--     if (sizeof(size_t) == sizeof(uint64_t)) {
--         ptrdiff_t result;
--         if (lean_float32_isnan(a)) result = 0;
--         else result = -9223372036854775809. < a ? (a < 9223372036854775808. ? (ptrdiff_t)a : INT64_MAX) : INT64_MIN;
--         return (size_t)result;
--     } else {
--         ptrdiff_t result;
--         if (lean_float32_isnan(a)) result = 0;
--         else result = -2147483649. < a ? (a < 2147483648. ? (ptrdiff_t)a : INT32_MAX) : INT32_MIN;
--         return (size_t)result;
--     }
-- }
-- ```
def lean_float32_to_isize := [JS_EXPR|throw new Error("lean_float32_to_isize not implemented")]

-- ```lean
-- def Int8.toFloat32 (n : Int8) : Float32 :=
--   .ofModel (.ofInt8 n)
-- ```
--
-- ```cpp
-- static inline float lean_int8_to_float32(uint8_t a) { return (float)(int8_t) a; }
-- ```
def lean_int8_to_float32 := [JS_EXPR|throw new Error("lean_int8_to_float32 not implemented")]

-- ```lean
-- def Int16.toFloat32 (n : Int16) : Float32 :=
--   .ofModel (.ofInt16 n)
-- ```
--
-- ```cpp
-- static inline float lean_int16_to_float32(uint16_t a) { return (float)(int16_t) a; }
-- ```
def lean_int16_to_float32 := [JS_EXPR|throw new Error("lean_int16_to_float32 not implemented")]

-- ```lean
-- def Int32.toFloat32 (n : Int32) : Float32 :=
--   .ofModel (.ofInt32 n)
-- ```
--
-- ```cpp
-- static inline float lean_int32_to_float32(uint32_t a) { return (float)(int32_t) a; }
-- ```
def lean_int32_to_float32 := [JS_EXPR|throw new Error("lean_int32_to_float32 not implemented")]

-- ```lean
-- def Int64.toFloat32 (n : Int64) : Float32 :=
--   .ofModel (.ofInt64 n)
-- ```
--
-- ```cpp
-- static inline float lean_int64_to_float32(uint64_t a) { return (float)(int64_t) a; }
-- ```
def lean_int64_to_float32 := [JS_EXPR|throw new Error("lean_int64_to_float32 not implemented")]

-- ```lean
-- def ISize.toFloat32 (n : ISize) : Float32 :=
--   .ofModel (.ofISize n)
-- ```
--
-- ```cpp
-- static inline float lean_isize_to_float32(size_t a) { return (float)(ptrdiff_t) a; }
-- ```
def lean_isize_to_float32 := [JS_EXPR|throw new Error("lean_isize_to_float32 not implemented")]

-- ============
-- Init.Data.String.Modify
-- ============

-- ```lean
-- def Pos.set {s : String} (p : s.Pos) (c : Char) (hp : p ≠ s.endPos) : String :=
--   if hc : c.utf8Size = 1 ∧ (p.byte hp).utf8ByteSize isUTF8FirstByte_byte = 1 then
--     .ofByteArray (s.toByteArray.set p.offset.byteIdx c.toUInt8 (p.byteIdx_lt_utf8ByteSize hp)) (by
--       rw [ByteArray.set_eq_push_extract_append_extract, ← hc.2, utf8ByteSize_byte,
--         ← Pos.byteIdx_offset_next]
--       refine ByteArray.IsValidUTF8.append ?_ (p.next hp).isValid.isValidUTF8_extract_utf8ByteSize
--       exact p.isValid.isValidUTF8_extract_zero.push hc.1)
--   else
--     (s.sliceTo p).copy ++ singleton c ++ (s.sliceFrom (p.next hp)).copy
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_string_utf8_set(obj_arg s, b_obj_arg i0, uint32 c) {
--     if (!lean_is_scalar(i0)) {
--         /* See comment at string_utf8_get */
--         return s;
--     }
--     usize i  = lean_unbox(i0);
--     usize sz = lean_string_size(s) - 1;
--     if (i >= sz) return s;
--     char * str = w_string_cstr(s);
--     if (lean_is_exclusive(s)) {
--         if (static_cast<unsigned char>(str[i]) < 128 && c < 128) {
--             str[i] = c;
--             return s;
--         }
--     }
--     if (!is_utf8_first_byte(str[i])) return s;
--     /* TODO(Leo): improve performance of other special cases.
--        Example: is_exclusive(s) and new and old characters have the same size; etc. */
--     std::string tmp;
--     push_unicode_scalar(tmp, c);
--     std::string new_s = string_to_std(s);
--     usize len = lean_string_len(s);
--     dec(s);
--     new_s.replace(i, get_utf8_char_size_at(new_s, i), tmp);
--     return lean_mk_string_unchecked(new_s.data(), new_s.size(), len);
-- }
-- ```
--
-- ```lean
-- def Pos.Raw.set : String → (@& Pos.Raw) → Char → String
--   | s, i, c => ofList (Pos.Raw.utf8SetAux c s.toList 0 i)
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_string_utf8_set(obj_arg s, b_obj_arg i0, uint32 c) {
--     if (!lean_is_scalar(i0)) {
--         /* See comment at string_utf8_get */
--         return s;
--     }
--     usize i  = lean_unbox(i0);
--     usize sz = lean_string_size(s) - 1;
--     if (i >= sz) return s;
--     char * str = w_string_cstr(s);
--     if (lean_is_exclusive(s)) {
--         if (static_cast<unsigned char>(str[i]) < 128 && c < 128) {
--             str[i] = c;
--             return s;
--         }
--     }
--     if (!is_utf8_first_byte(str[i])) return s;
--     /* TODO(Leo): improve performance of other special cases.
--        Example: is_exclusive(s) and new and old characters have the same size; etc. */
--     std::string tmp;
--     push_unicode_scalar(tmp, c);
--     std::string new_s = string_to_std(s);
--     usize len = lean_string_len(s);
--     dec(s);
--     new_s.replace(i, get_utf8_char_size_at(new_s, i), tmp);
--     return lean_mk_string_unchecked(new_s.data(), new_s.size(), len);
-- }
-- ```
--
-- ```lean
-- def set : String → (@& Pos.Raw) → Char → String
--   | s, i, c => ofList (Pos.Raw.utf8SetAux c s.toList 0 i)
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_string_utf8_set(obj_arg s, b_obj_arg i0, uint32 c) {
--     if (!lean_is_scalar(i0)) {
--         /* See comment at string_utf8_get */
--         return s;
--     }
--     usize i  = lean_unbox(i0);
--     usize sz = lean_string_size(s) - 1;
--     if (i >= sz) return s;
--     char * str = w_string_cstr(s);
--     if (lean_is_exclusive(s)) {
--         if (static_cast<unsigned char>(str[i]) < 128 && c < 128) {
--             str[i] = c;
--             return s;
--         }
--     }
--     if (!is_utf8_first_byte(str[i])) return s;
--     /* TODO(Leo): improve performance of other special cases.
--        Example: is_exclusive(s) and new and old characters have the same size; etc. */
--     std::string tmp;
--     push_unicode_scalar(tmp, c);
--     std::string new_s = string_to_std(s);
--     usize len = lean_string_len(s);
--     dec(s);
--     new_s.replace(i, get_utf8_char_size_at(new_s, i), tmp);
--     return lean_mk_string_unchecked(new_s.data(), new_s.size(), len);
-- }
-- ```
def lean_string_utf8_set := [JS_FUNC|inputs(str, pos, char)|
  const encoder = new TextEncoder( );
  const decoder = new TextDecoder( );
  const bytes = encoder.encode(str);
  const charBytes = encoder.encode(char);
  if (pos < 0 || pos >= bytes.length) return str;

  let len = 0;
  const firstByte = bytes[pos];
  if (firstByte < 0x80) { len = 1; }
  else if (firstByte < 0xE0) { len = 2; }
  else if (firstByte < 0xF0) { len = 3; }
  else if (firstByte < 0xF8) { len = 4; }
  else { len = 1; }

  const resultBytes = new Uint8Array(bytes.length - len + charBytes.length);
  resultBytes.set(bytes.subarray(0, pos));
  resultBytes.set(charBytes, pos);
  resultBytes.set(bytes.subarray(pos + len));

  return decoder.decode(resultBytes);
]

-- ============
-- Init.Data.String.Pattern.Basic
-- ============

-- ```lean
-- def memcmpStr (lhs rhs : @& String) (lstart : @& String.Pos.Raw) (rstart : @& String.Pos.Raw)
--     (len : @& String.Pos.Raw) (h1 : len.offsetBy lstart ≤ lhs.rawEndPos)
--     (h2 : len.offsetBy rstart ≤ rhs.rawEndPos) : Bool :=
--   go 0
-- where
--   go (curr : String.Pos.Raw) : Bool :=
--     if h : curr < len then
--       have hl := by
--         simp [Pos.Raw.le_iff, Pos.Raw.lt_iff] at h h1 ⊢
--         omega
--       have hr := by
--         simp [Pos.Raw.le_iff, Pos.Raw.lt_iff] at h h2 ⊢
--         omega
--       if lhs.getUTF8Byte (curr.offsetBy lstart) hl == rhs.getUTF8Byte (curr.offsetBy rstart) hr then
--         go curr.inc
--       else
--         false
--     else
--       true
--   termination_by len.byteIdx - curr.byteIdx
--   decreasing_by
--     simp [Pos.Raw.lt_iff] at h ⊢
--     omega
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8_t lean_string_memcmp(b_obj_arg s1, b_obj_arg s2, b_obj_arg lstart, b_obj_arg rstart, b_obj_arg len) {
--     // Thanks to the proof arguments we know that lstart, rstart and len are all scalars.
--     lean_assert(lean_is_scalar(lstart));
--     lean_assert(lean_is_scalar(rstart));
--     lean_assert(lean_is_scalar(len));
-- 
--     char const * lbase = lean_string_cstr(s1) + lean_unbox(lstart);
--     char const * rbase = lean_string_cstr(s2) + lean_unbox(rstart);
--     return std::memcmp(lbase, rbase, lean_unbox(len)) == 0;
-- }
-- ```
def lean_string_memcmp := [JS_EXPR_WITH_NAMED_ARGS(s1, s2, start1, start2, len)|
  s1.slice(start1, start1 + len) == s2.slice(start2, start2 + len)
]

-- ============
-- Init.Data.String.Slice
-- ============

-- ```lean
-- protected def hash (s : @& Slice) : UInt64 :=
--   String.hash s.copy
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint64_t lean_slice_hash(b_obj_arg s) {
--     size_t sz = lean_slice_size(s);
--     char const * str = lean_slice_base(s);
--     return hash_str(sz, (unsigned char const *) str, 11);
-- }
-- ```
def lean_slice_hash := [JS_FUNC|inputs(str, start, len)|returns=hash|
  const s = str.substring(start, start + len);
  loop (i := 0, hash := 0) {
    if (i < s.length) {
      continue (i := i + 1, hash := ((hash << 5) - hash + s.charCodeAt(i)) | 0);
    } else {
      break;
    }
  }
]

-- ```lean
-- instance (x y : @& Slice) : Decidable (x < y) :=
--   inferInstanceAs (Decidable (x.copy < y.copy))
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8_t lean_slice_dec_lt(object * s1, object * s2) {
--     size_t sz1 = lean_slice_size(s1);
--     size_t sz2 = lean_slice_size(s2);
--     int r = std::memcmp(lean_slice_base(s1), lean_slice_base(s2), std::min(sz1, sz2));
--     return r < 0 || (r == 0 && sz1 < sz2);
-- }
-- ```
def lean_slice_dec_lt := [JS_EXPR| (#0).substring(#1, #1 + #2) < (#3).substring(#4, #4 + #5) ]

-- ============
-- Init.System.IO
-- ============

-- ```lean
-- opaque timeit (msg : @& String) (fn : IO α) : IO α
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_timeit(b_obj_arg msg, obj_arg fn) {
--     auto start = std::chrono::steady_clock::now();
--     obj_arg w = apply_1(fn, lean_io_mk_world());
--     auto end   = std::chrono::steady_clock::now();
--     auto diff  = std::chrono::duration<double>(end - start);
--     sstream out;
--     out << std::setprecision(3);
--     if (diff < std::chrono::duration<double>(1)) {
--         out << string_cstr(msg) << " " << std::chrono::duration<double, std::milli>(diff).count() << "ms";
--     } else {
--         out << string_cstr(msg) << " " << diff.count() << "s";
--     }
--     io_eprintln(mk_string(out.str()));
--     return w;
-- }
-- ```
def lean_io_timeit := [JS_EXPR|throw new Error("lean_io_timeit not implemented")]

-- ```lean
-- opaque allocprof (msg : @& String) (fn : IO α) : IO α
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_allocprof(b_obj_arg msg, obj_arg fn) {
--     std::ostringstream out;
--     obj_res res;
--     {
--         allocprof prof(out, string_cstr(msg));
--         res = apply_1(fn, lean_io_mk_world());
--     }
--     io_eprintln(mk_string(out.str()));
--     return res;
-- }
-- ```
def lean_io_allocprof := [JS_EXPR|(#1)( )]

-- ```lean
-- opaque IO.initializing : BaseIO Bool
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8_t lean_io_initializing() {
--     return g_initializing;
-- }
-- ```
def lean_io_initializing := [JS_EXPR|false]

-- ```lean
-- opaque asTask (act : BaseIO α) (prio := Task.Priority.default) : BaseIO (Task α) :=
--   Task.pure <$> act
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_as_task(obj_arg act, obj_arg prio) {
--     object * c = lean_alloc_closure((void*)lean_io_as_task_fn, 2, 1);
--     lean_closure_set(c, 0, act);
--     object * t = lean_task_spawn_core(c, lean_unbox(prio), /* keep_alive */ true);
--     return t;
-- }
-- ```
def lean_io_as_task := [JS_EXPR|throw new Error("lean_io_as_task not implemented")]

-- ```lean
-- opaque mapTask (f : α → BaseIO β) (t : Task α) (prio := Task.Priority.default) (sync := false) :
--     BaseIO (Task β) :=
--   Task.pure <$> f t.get
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_map_task(obj_arg f, obj_arg t, obj_arg prio, uint8 sync) {
--     object * c = lean_alloc_closure((void*)lean_io_bind_task_fn, 2, 1);
--     lean_closure_set(c, 0, f);
--     object * t2 = lean_task_map_core(c, t, lean_unbox(prio), sync, /* keep_alive */ true);
--     return t2;
-- }
-- ```
def lean_io_map_task := [JS_EXPR|throw new Error("lean_io_map_task not implemented")]

-- ```lean
-- opaque bindTask (t : Task α) (f : α → BaseIO (Task β)) (prio := Task.Priority.default)
--     (sync := false) : BaseIO (Task β) :=
--   f t.get
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_bind_task(obj_arg t, obj_arg f, obj_arg prio, uint8 sync) {
--     object * c = lean_alloc_closure((void*)lean_io_bind_task_fn, 2, 1);
--     lean_closure_set(c, 0, f);
--     object * t2 = lean_task_bind_core(t, c, lean_unbox(prio), sync, /* keep_alive */ true);
--     return t2;
-- }
-- ```
def lean_io_bind_task := [JS_EXPR|throw new Error("lean_io_bind_task not implemented")]

-- ```lean
-- opaque monoMsNow : BaseIO Nat
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_mono_ms_now() {
--     static_assert(sizeof(std::chrono::milliseconds::rep) <= sizeof(uint64), "size of std::chrono::nanoseconds::rep may not exceed 64");
--     auto now = std::chrono::steady_clock::now();
--     auto tm = std::chrono::duration_cast<std::chrono::milliseconds>(now.time_since_epoch());
--     return uint64_to_nat(tm.count());
-- }
-- ```
def lean_io_mono_ms_now := [JS_EXPR|BigInt(Date.now( ))]

-- ```lean
-- opaque monoNanosNow : BaseIO Nat
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_mono_nanos_now() {
--     static_assert(sizeof(std::chrono::nanoseconds::rep) <= sizeof(uint64), "size of std::chrono::nanoseconds::rep may not exceed 64");
--     auto now = std::chrono::steady_clock::now();
--     auto tm = std::chrono::duration_cast<std::chrono::nanoseconds>(now.time_since_epoch());
--     return uint64_to_nat(tm.count());
-- }
-- ```
def lean_io_mono_nanos_now := [JS_EXPR|BigInt(Date.now( )) * 1000000]

-- ```lean
-- opaque getRandomBytes (nBytes : USize) : IO ByteArray
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_get_random_bytes (size_t nbytes) {
--     // Adapted from https://github.com/rust-random/getrandom/blob/30308ae845b0bf3839e5a92120559eaf56048c28/src/
-- 
--     if (nbytes == 0) return io_result_mk_ok(lean_alloc_sarray(1, 0, 0));
-- 
-- #if !defined(LEAN_WINDOWS)
--     int fd_urandom = open("/dev/urandom", O_RDONLY | O_CLOEXEC);
--     if (fd_urandom < 0) {
--         return io_result_mk_error(decode_io_error(errno, lean_mk_ascii_string_unchecked("/dev/urandom")));
--     }
-- #endif
-- 
--     if (lean_alloc_sarray_would_overflow(1, nbytes)) {
--         return io_result_mk_error(decode_io_error(ENOMEM, NULL));
--     }
--     obj_res res = lean_alloc_sarray(1, 0, nbytes);
--     size_t remain = nbytes;
--     uint8_t *dst = lean_sarray_cptr(res);
-- 
--     while (remain > 0) {
-- #if defined(LEAN_WINDOWS)
--         // Prevent ULONG (32-bit) overflow
--         size_t read_sz = std::min(remain, static_cast<size_t>(std::numeric_limits<uint32_t>::max()));
--         NTSTATUS status = BCryptGenRandom(
--             NULL,
--             dst,
--             static_cast<ULONG>(read_sz),
--             BCRYPT_USE_SYSTEM_PREFERRED_RNG
--         );
--         if (!NT_SUCCESS(status)) {
--             dec_ref(res);
--             return io_result_mk_error("BCryptGenRandom failed");
--         }
--         remain -= read_sz;
--         dst += read_sz;
-- #else
--     #if defined(LEAN_EMSCRIPTEN)
--         // `Crypto.getRandomValues` documents `dest` should be at most 65536 bytes.
--         size_t read_sz = std::min(remain, static_cast<size_t>(65536));
--     #else
--         size_t read_sz = remain;
--     #endif
--         ssize_t nread = read(fd_urandom, dst, read_sz);
--         if (nread < 0) {
--             if (errno != EINTR) {
--                 close(fd_urandom);
--                 dec_ref(res);
--                 return io_result_mk_error(decode_io_error(errno, nullptr));
--             }
--         } else {
--             remain -= nread;
--             dst += nread;
--         }
-- #endif
--     }
-- 
-- #if !defined(LEAN_WINDOWS)
--     close(fd_urandom);
-- #endif
--     lean_sarray_set_size(res, nbytes);
--     return io_result_mk_ok(res);
-- }
-- ```
def lean_io_get_random_bytes := [JS_EXPR|throw new Error("lean_io_get_random_bytes not implemented")]

-- ```lean
-- opaque checkCanceled : BaseIO Bool
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8_t lean_io_check_canceled() {
--     return lean_io_check_canceled_core();
-- }
-- ```
def lean_io_check_canceled := [JS_EXPR|false]

-- ```lean
-- opaque cancel : @& Task α → BaseIO Unit
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_cancel(b_obj_arg t) {
--     lean_io_cancel_core(t);
--     return box(0);
-- }
-- ```
def lean_io_cancel := [JS_EXPR|null]

-- ```lean
-- opaque getTaskState : @& Task α → BaseIO TaskState
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8_t lean_io_get_task_state(b_obj_arg t) {
--     return lean_io_get_task_state_core(t);
-- }
-- ```
def lean_io_get_task_state := [JS_EXPR|mkObject(`TaskState.finished)]

-- ```lean
-- opaque wait (t : Task α) : BaseIO α :=
--   return t.get
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_wait(obj_arg t) {
--     return lean_task_get_own(t);
-- }
-- ```
def lean_io_wait := [JS_EXPR|#0]

-- ```lean
-- opaque waitAny (tasks : @& List (Task α))
--     (h : tasks.length > 0 := by exact Nat.zero_lt_succ _) : BaseIO α :=
--   return tasks[0].get
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_wait_any(b_obj_arg task_list) {
--     object * t = lean_io_wait_any_core(task_list);
--     object * v = lean_task_get(t);
--     lean_inc(v);
--     return v;
-- }
-- ```
def lean_io_wait_any := [JS_EXPR|#0[0]]

-- ```lean
-- opaque getNumHeartbeats : BaseIO Nat
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_get_num_heartbeats() {
--     return lean_uint64_to_nat(get_num_heartbeats());
-- }
-- ```
def lean_io_get_num_heartbeats := [JS_EXPR|0]

-- ```lean
-- opaque setNumHeartbeats (count : Nat) : BaseIO Unit
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_set_heartbeats(obj_arg count) {
--     set_heartbeats(lean_uint64_of_nat(count));
--     lean_dec(count);
--     return box(0);
-- }
-- ```
def lean_io_set_heartbeats := [JS_EXPR|throw new Error("lean_io_set_heartbeats not implemented")]

-- ```lean
-- opaque getStdin  : BaseIO FS.Stream
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_get_stdin() {
--     return get_stream_current_stdin().to_obj_arg();
-- }
-- ```
def lean_get_stdin := [JS_EXPR|_stdin]

-- ```lean
-- opaque getStdout : BaseIO FS.Stream
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_get_stdout() {
--     return get_stream_current_stdout().to_obj_arg();
-- }
-- ```
def lean_get_stdout := [JS_EXPR|_stdout]

-- ```lean
-- opaque getStderr : BaseIO FS.Stream
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_get_stderr() {
--     return get_stream_current_stderr().to_obj_arg();
-- }
-- ```
def lean_get_stderr := [JS_EXPR|_stderr]

-- ```lean
-- opaque setStdin  : FS.Stream → BaseIO FS.Stream
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_get_set_stdin(obj_arg h) {
--     object_ref & x = get_stream_current_stdin();
--     object * r = x.steal();
--     x = object_ref(h);
--     return r;
-- }
-- ```
def lean_get_set_stdin := [JS_EXPR|throw new Error("lean_get_set_stdin not implemented")]

-- ```lean
-- opaque setStdout : FS.Stream → BaseIO FS.Stream
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_get_set_stdout(obj_arg h) {
--     object_ref & x = get_stream_current_stdout();
--     object * r = x.steal();
--     x = object_ref(h);
--     return r;
-- }
-- ```
def lean_get_set_stdout := [JS_EXPR|throw new Error("lean_get_set_stdout not implemented")]

-- ```lean
-- opaque setStderr : FS.Stream → BaseIO FS.Stream
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_get_set_stderr(obj_arg h) {
--     object_ref & x = get_stream_current_stderr();
--     object * r = x.steal();
--     x = object_ref(h);
--     return r;
-- }
-- ```
def lean_get_set_stderr := [JS_EXPR|throw new Error("lean_get_set_stderr not implemented")]

-- ```lean
-- opaque mk (fn : @& FilePath) (mode : FS.Mode) : IO Handle
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_mk(b_obj_arg filename, uint8 mode) {
--     int flags = 0;
-- #ifdef LEAN_WINDOWS
--     // do not translate line endings
--     flags |= O_BINARY;
--     // do not inherit across process creation
--     flags |= O_NOINHERIT;
-- #else
--     // do not inherit across process creation
--     flags |= O_CLOEXEC;
-- #endif
--     switch (mode) {
--     case 0: flags |= O_RDONLY; break;  // read
--     case 1: flags |= O_WRONLY | O_CREAT | O_TRUNC; break;  // write
--     case 2: flags |= O_WRONLY | O_CREAT | O_TRUNC | O_EXCL; break;  // writeNew
--     case 3: flags |= O_RDWR; break;  // readWrite
--     case 4: flags |= O_WRONLY | O_CREAT | O_APPEND; break;  // append
--     }
--     const char* fname = string_cstr(filename);
--     if (strlen(fname) != lean_string_size(filename) - 1) {
--         return mk_embedded_nul_error(filename);
--     }
--     int fd = open(fname, flags, 0666);
--     if (fd == -1) {
--         return io_result_mk_error(decode_io_error(errno, filename));
--     }
--     char const * fp_mode;
--     switch (mode) {
--     case 0: fp_mode = "r"; break;  // read
--     case 1: fp_mode = "w"; break;  // write
--     case 2: fp_mode = "w"; break;  // writeNew
--     case 3: fp_mode = "r+"; break;  // readWrite
--     case 4: fp_mode = "a"; break;  // append
--     }
--     FILE * fp = fdopen(fd, fp_mode);
--     if (!fp) {
--         return io_result_mk_error(decode_io_error(errno, filename));
--     } else {
--         return io_result_mk_ok(io_wrap_handle(fp));
--     }
-- }
-- ```
def lean_io_prim_handle_mk := [JS_EXPR|throw new Error("lean_io_prim_handle_mk not implemented")]

-- ```lean
-- opaque lock (h : @& Handle) (exclusive := true) : IO Unit
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_lock(b_obj_arg h, uint8_t x) {
--     OVERLAPPED o = {0};
--     HANDLE wh = win_handle(io_get_handle(h));
--     DWORD flags = x ? LOCKFILE_EXCLUSIVE_LOCK : 0;
--     if (LockFileEx(wh, flags, 0, MAXDWORD, MAXDWORD, &o)) {
--         return io_result_mk_ok(box(0));
--     } else {
--         return io_result_mk_error((sstream() << GetLastError()).str());
--     }
-- }
-- ```
def lean_io_prim_handle_lock := [JS_EXPR|null]

-- ```lean
-- opaque tryLock (h : @& Handle) (exclusive := true) : IO Bool
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_try_lock(b_obj_arg h, uint8_t x) {
--     OVERLAPPED o = {0};
--     HANDLE wh = win_handle(io_get_handle(h));
--     DWORD flags = (x ? LOCKFILE_EXCLUSIVE_LOCK : 0) | LOCKFILE_FAIL_IMMEDIATELY;
--     if (LockFileEx(wh, flags, 0, MAXDWORD, MAXDWORD, &o)) {
--         return io_result_mk_ok(box(1));
--     } else {
--         if (GetLastError() == ERROR_LOCK_VIOLATION) {
--             return io_result_mk_ok(box(0));
--         } else {
--             return io_result_mk_error((sstream() << GetLastError()).str());
--         }
--     }
-- }
-- ```
def lean_io_prim_handle_try_lock := [JS_EXPR|true]

-- ```lean
-- opaque unlock (h : @& Handle) : IO Unit
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_unlock(b_obj_arg h) {
--     OVERLAPPED o = {0};
--     HANDLE wh = win_handle(io_get_handle(h));
--     if (UnlockFileEx(wh, 0, MAXDWORD, MAXDWORD, &o)) {
--         return io_result_mk_ok(box(0));
--     } else {
--         if (GetLastError() == ERROR_NOT_LOCKED) {
--             // For consistency with Unix
--             return io_result_mk_ok(box(0));
--         } else {
--             return io_result_mk_error((sstream() << GetLastError()).str());
--         }
--     }
-- }
-- ```
def lean_io_prim_handle_unlock := [JS_EXPR|null]

-- ```lean
-- opaque isTty (h : @& Handle) : BaseIO Bool
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8_t lean_io_prim_handle_is_tty(b_obj_arg h) {
--     FILE * fp = io_get_handle(h);
-- #ifdef LEAN_WINDOWS
--     /*
--     On Windows, there are two approaches for detecting a console.
--     1)  _isatty(_fileno(fp)) != 0
--         This checks whether the file descriptor is a *character device*,
--         not just a terminal (unlike Unix's isatty). Thus, it produces a false
--         positive in some edge cases (such as NUL).
--         https://stackoverflow.com/q/3648711
--     2)  GetConsoleMode(win_handle(fp), &mode) != 0
--         Errors if the handle is not a console. Unfortunately, this produces
--         a false negative for a terminal emulator like MSYS/Cygwin's Mintty,
--         which is not implemented as a Windows-recognized console on
--         old Windows versions (e.g., pre-Windows 10, pre-ConPTY).
--         https://github.com/msys2/MINGW-packages/issues/14087
--     We choose to use GetConsoleMode as that seems like the more modern approach,
--     and Lean does not support pre-Windows 10.
--     */
--     DWORD mode;
--     return GetConsoleMode(win_handle(fp), &mode) != 0;
-- #else
--     // We ignore errors for consistency with Windows.
--     return isatty(fileno(fp));
-- #endif
-- }
-- ```
def lean_io_prim_handle_is_tty := [JS_EXPR|false]

-- ```lean
-- opaque flush (h : @& Handle) : IO Unit
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_flush(b_obj_arg h) {
--     FILE * fp = io_get_handle(h);
--     if (!std::fflush(fp)) {
--         return io_result_mk_ok(box(0));
--     } else {
--         return io_result_mk_error(decode_io_error(errno, nullptr));
--     }
-- }
-- ```
def lean_io_prim_handle_flush := [JS_EXPR|throw new Error("lean_io_prim_handle_flush not implemented")]

-- ```lean
-- opaque rewind (h : @& Handle) : IO Unit
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_rewind(b_obj_arg h) {
--     FILE * fp = io_get_handle(h);
--     if (!std::fseek(fp, 0, SEEK_SET)) {
--         return io_result_mk_ok(box(0));
--     } else {
--         return io_result_mk_error(decode_io_error(errno, nullptr));
--     }
-- }
-- ```
def lean_io_prim_handle_rewind := [JS_EXPR|null]

-- ```lean
-- opaque truncate (h : @& Handle) : IO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_io_prim_handle_truncate := [JS_EXPR|throw new Error("lean_io_prim_handle_truncate not implemented")]

-- ```lean
-- opaque read (h : @& Handle) (bytes : USize) : IO ByteArray
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_read(b_obj_arg h, usize nbytes) {
--     FILE * fp = io_get_handle(h);
--     if (lean_alloc_sarray_would_overflow(1, nbytes)) {
--         return io_result_mk_error(decode_io_error(ENOMEM, NULL));
--     }
--     obj_res res = lean_alloc_sarray(1, 0, nbytes);
--     if (nbytes == 0) {
--         // std::fread doesn't handle 0 reads well, see https://github.com/leanprover/lean4/issues/12138
--         return io_result_mk_ok(res);
--     }
--     usize n = std::fread(lean_sarray_cptr(res), 1, nbytes, fp);
--     if (n > 0) {
--         lean_sarray_set_size(res, n);
--         return io_result_mk_ok(res);
--     } else if (feof(fp)) {
--         clearerr(fp);
--         lean_sarray_set_size(res, n);
--         return io_result_mk_ok(res);
--     } else {
--         dec_ref(res);
--         return io_result_mk_error(decode_io_error(errno, nullptr));
--     }
-- }
-- ```
def lean_io_prim_handle_read := [JS_EXPR|throw new Error("lean_io_prim_handle_read not implemented")]

-- ```lean
-- opaque write (h : @& Handle) (buffer : @& ByteArray) : IO Unit
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_write(b_obj_arg h, b_obj_arg buf) {
--     FILE * fp = io_get_handle(h);
--     usize n = lean_sarray_size(buf);
--     usize m = std::fwrite(lean_sarray_cptr(buf), 1, n, fp);
--     if (m == n) {
--         return io_result_mk_ok(box(0));
--     } else {
--         return io_result_mk_error(decode_io_error(errno, nullptr));
--     }
-- }
-- ```
def lean_io_prim_handle_write := [JS_EXPR|throw new Error("lean_io_prim_handle_write not implemented")]

-- ```lean
-- opaque getLine (h : @& Handle) : IO String
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_get_line(b_obj_arg h) {
--     FILE * fp = io_get_handle(h);
-- 
--     std::string result;
--     int c; // Note: int, not char, required to handle EOF
--     LEAN_IO_LOCK_FILE(fp);
--     while ((c = LEAN_IO_GETC_UNLOCKED(fp)) != EOF) {
--         result.push_back(c);
--         if (c == '\n') {
--             break;
--         }
--     }
--     LEAN_IO_UNLOCK_FILE(fp);
-- 
--     if (std::ferror(fp)) {
--         return io_result_mk_error(decode_io_error(errno, nullptr));
--     } else if (std::feof(fp)) {
--         clearerr(fp);
--         return io_result_mk_ok(mk_string(result));
--     } else {
--         obj_res ret = io_result_mk_ok(mk_string(result));
--         return ret;
--     }
-- }
-- ```
def lean_io_prim_handle_get_line := [JS_EXPR|throw new Error("lean_io_prim_handle_get_line not implemented")]

-- ```lean
-- opaque putStr (h : @& Handle) (s : @& String) : IO Unit
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_put_str(b_obj_arg h, b_obj_arg s) {
--     FILE * fp = io_get_handle(h);
--     usize n = lean_string_size(s) - 1; // - 1 to ignore the terminal NULL byte.
--     usize m = std::fwrite(lean_string_cstr(s), 1, n, fp);
--     if (m == n) {
--         return io_result_mk_ok(box(0));
--     } else {
--         return io_result_mk_error(decode_io_error(errno, nullptr));
--     }
-- }
-- ```
def lean_io_prim_handle_put_str := [JS_EXPR|throw new Error("lean_io_prim_handle_put_str not implemented")]

-- ```lean
-- opaque realPath (fname : FilePath) : IO FilePath
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_realpath(obj_arg filename) {
--     const char* fname = string_cstr(filename);
--     if (strlen(fname) != lean_string_size(filename) - 1) {
--         obj_res res = mk_embedded_nul_error(filename);
--         dec_ref(filename);
--         return res;
--     }
-- #if defined(LEAN_WINDOWS)
--     constexpr unsigned BufferSize = 8192;
--     char buffer[BufferSize];
--     HANDLE handle = CreateFile(fname, 0, FILE_SHARE_READ, NULL, OPEN_EXISTING, FILE_FLAG_BACKUP_SEMANTICS, NULL);
--     if (handle == INVALID_HANDLE_VALUE) {
--         obj_res res = mk_file_not_found_error(filename);
--         dec_ref(filename);
--         return res;
--     }
--     DWORD retval = GetFinalPathNameByHandle(handle, buffer, BufferSize, 0);
--     CloseHandle(handle);
--     if (retval == 0 || retval > BufferSize) {
--         return io_result_mk_ok(filename);
--     } else {
--         dec_ref(filename);
--         char * res = buffer;
--         if (memcmp(res, "\\\\?\\", 4) == 0) {
--             if (memcmp(res + 4, "UNC\\", 4) == 0) {
--                 // network path: convert "\\\\?\\UNC\\..." to "\\\\..."
--                 res[6] = '\\';
--                 res += 6;
--             } else {
--                 // simple path: convert "\\\\?\\C:\\.." to "C:\\..."
--                 res += 4;
--             }
--         }
--         // Hack for making sure disk is lower case
--         // TODO(Leo): more robust solution
--         if (strlen(res) >= 2 && res[1] == ':') {
--             res[0] = tolower(res[0]);
--         }
--         return io_result_mk_ok(mk_string(res));
--     }
-- #else
--     char buffer[PATH_MAX];
--     char * tmp = realpath(fname, buffer);
--     if (tmp) {
--         obj_res s = mk_string(tmp);
--         dec_ref(filename);
--         return io_result_mk_ok(s);
--     } else {
--         obj_res res = mk_file_not_found_error(filename);
--         dec_ref(filename);
--         return res;
--     }
-- #endif
-- }
-- ```
def lean_io_realpath := [JS_EXPR|fs.realpathSync(#0)]

-- ```lean
-- opaque removeFile (fname : @& FilePath) : IO Unit
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_remove_file(b_obj_arg filename) {
--     const char* fname = string_cstr(filename);
--     if (strlen(fname) != lean_string_size(filename) - 1) {
--         return mk_embedded_nul_error(filename);
--     }
--     uv_fs_t req;
--     int ret = uv_fs_unlink(NULL, &req, fname, NULL);
--     uv_fs_req_cleanup(&req);
--     if (ret < 0) {
--         return io_result_mk_error(decode_uv_error(ret, filename));
--     } else {
--         return io_result_mk_ok(box(0));
--     }
-- }
-- ```
def lean_io_remove_file := [JS_EXPR|throw new Error("lean_io_remove_file not implemented")]

-- ```lean
-- opaque removeDir : @& FilePath → IO Unit
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_remove_dir(b_obj_arg p) {
--     const char* str = string_cstr(p);
--     if (strlen(str) != lean_string_size(p) - 1) {
--         return mk_embedded_nul_error(p);
--     }
--     if (rmdir(str) == 0) {
--         return io_result_mk_ok(box(0));
--     } else {
--         return io_result_mk_error(decode_io_error(errno, p));
--     }
-- }
-- ```
def lean_io_remove_dir := [JS_EXPR|throw new Error("lean_io_remove_dir not implemented")]

-- ```lean
-- opaque createDir : @& FilePath → IO Unit
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_create_dir(b_obj_arg p) {
--     const char* str = string_cstr(p);
--     if (strlen(str) != lean_string_size(p) - 1) {
--         return mk_embedded_nul_error(p);
--     }
-- #ifdef LEAN_WINDOWS
--     if (mkdir(str) == 0) {
-- #else
--     if (mkdir(str, 0777) == 0) {
-- #endif
--         return io_result_mk_ok(box(0));
--     } else {
--         return io_result_mk_error(decode_io_error(errno, p));
--     }
-- }
-- 
-- extern "C" LEAN_EXPORT obj_res lean_io_remove_dir(b_obj_arg p) {
--     const char* str = string_cstr(p);
--     if (strlen(str) != lean_string_size(p) - 1) {
--         return mk_embedded_nul_error(p);
--     }
--     if (rmdir(str) == 0) {
--         return io_result_mk_ok(box(0));
--     } else {
--         return io_result_mk_error(decode_io_error(errno, p));
--     }
-- }
-- 
-- extern "C" LEAN_EXPORT obj_res lean_io_rename(b_obj_arg from, b_obj_arg to) {
--     const char* from_str = string_cstr(from);
--     if (strlen(from_str) != lean_string_size(from) - 1) {
--         return mk_embedded_nul_error(from);
--     }
--     const char* to_str = string_cstr(to);
--     if (strlen(to_str) != lean_string_size(to) - 1) {
--         return mk_embedded_nul_error(to);
--     }
-- #ifdef LEAN_WINDOWS
--     // Note: On windows, std::rename gives an error if the `to` file already exists,
--     // so we have to call the underlying windows API directly to get behavior consistent
--     // with the unix-like OSs
--     bool ok = MoveFileEx(from_str, to_str, MOVEFILE_REPLACE_EXISTING) != 0;
--     if (!ok) {
--         // TODO: actually produce the right type of IO error
--         return io_result_mk_error((sstream()
--             << "failed to rename '" << from_str << "' to '" << to_str << "': " << GetLastError()).str());
--     }
-- #else
--     bool ok = std::rename(from_str, to_str) == 0;
--     if (!ok) {
--         std::ostringstream s;
--         s << from_str << " and/or " << to_str;
--         object_ref out{mk_string(s.str())};
--         return io_result_mk_error(decode_io_error(errno, out.raw()));
--     }
-- #endif
--     return io_result_mk_ok(box(0));
-- }
-- 
-- /* hardLink (orig link : @& FilePath) : IO Unit */
-- extern "C" LEAN_EXPORT obj_res lean_io_hard_link(b_obj_arg orig, b_obj_arg link) {
--     const char* orig_str = string_cstr(orig);
--     if (strlen(orig_str) != lean_string_size(orig) - 1) {
--         return mk_embedded_nul_error(orig);
--     }
--     const char* link_str = string_cstr(link);
--     if (strlen(link_str) != lean_string_size(link) - 1) {
--         return mk_embedded_nul_error(link);
--     }
--     uv_fs_t req;
--     int ret = uv_fs_link(NULL, &req, orig_str, link_str, NULL);
--     uv_fs_req_cleanup(&req);
--     if (ret < 0) {
--         return io_result_mk_error(decode_uv_error(ret, orig));
--     } else {
--         return io_result_mk_ok(box(0));
--     }
-- }
-- 
-- /* createTempFile : IO (Handle × FilePath) */
-- extern "C" LEAN_EXPORT obj_res lean_io_create_tempfile(lean_object * /* w */) {
--     char path[PATH_MAX];
--     size_t base_len = PATH_MAX;
--     int ret = uv_os_tmpdir(path, &base_len);
--     if (ret < 0) {
--         return io_result_mk_error(decode_uv_error(ret, nullptr));
--     } else if (base_len == 0) {
--         return lean_io_result_mk_error(decode_uv_error(UV_ENOENT, mk_string("")));
--     }
-- 
-- #if defined(LEAN_WINDOWS)
--     // On Windows `GetTempPathW` always returns a path ending in \, but libuv removes it.
--     // https://learn.microsoft.com/en-us/windows/win32/fileio/creating-and-using-a-temporary-file
--     if (path[base_len - 1] != '\\') {
--         lean_always_assert(PATH_MAX >= base_len + 1 + 1);
--         strcat(path, "\\");
--     }
-- #else
--     // No guarantee that we have a trailing / in TMPDIR.
--     if (path[base_len - 1] != '/') {
--         lean_always_assert(PATH_MAX >= base_len + 1 + 1);
--         strcat(path, "/");
--     }
-- #endif
-- 
--     const char* file_pattern = "tmp.XXXXXXXX";
--     const size_t file_pattern_size = strlen(file_pattern);
--     lean_always_assert(PATH_MAX >= strlen(path) + file_pattern_size + 1);
--     strcat(path, file_pattern);
-- 
--     uv_fs_t req;
--     // Differences from lean_io_create_tempdir start here
--     ret = uv_fs_mkstemp(NULL, &req, path, NULL);
--     if (ret < 0) {
--         uv_fs_req_cleanup(&req);
--         // If mkstemp throws an error we cannot rely on path to contain a proper file name.
--         return io_result_mk_error(decode_uv_error(ret, nullptr));
--     } else {
--         FILE* handle = fdopen(req.result, "r+");
--         object_ref pair = mk_cnstr(0, io_wrap_handle(handle), mk_string(req.path));
--         uv_fs_req_cleanup(&req);
--         return lean_io_result_mk_ok(pair.steal());
--     }
-- }
-- 
-- /* createTempDir : IO FilePath */
-- extern "C" LEAN_EXPORT obj_res lean_io_create_tempdir(lean_object * /* w */) {
--     char path[PATH_MAX];
--     size_t base_len = PATH_MAX;
--     int ret = uv_os_tmpdir(path, &base_len);
--     if (ret < 0) {
--         return io_result_mk_error(decode_uv_error(ret, nullptr));
--     } else if (base_len == 0) {
--         return lean_io_result_mk_error(decode_uv_error(UV_ENOENT, mk_string("")));
--     }
-- 
-- #if defined(LEAN_WINDOWS)
--     // On Windows `GetTempPathW` always returns a path ending in \, but libuv removes it.
--     // https://learn.microsoft.com/en-us/windows/win32/fileio/creating-and-using-a-temporary-file
--     if (path[base_len - 1] != '\\') {
--         lean_always_assert(PATH_MAX >= base_len + 1 + 1);
--         strcat(path, "\\");
--     }
-- #else
--     // No guarantee that we have a trailing / in TMPDIR.
--     if (path[base_len - 1] != '/') {
--         lean_always_assert(PATH_MAX >= base_len + 1 + 1);
--         strcat(path, "/");
--     }
-- #endif
-- 
--     const char* file_pattern = "tmp.XXXXXXXX";
--     const size_t file_pattern_size = strlen(file_pattern);
--     lean_always_assert(PATH_MAX >= strlen(path) + file_pattern_size + 1);
--     strcat(path, file_pattern);
-- 
--     uv_fs_t req;
--     // Differences from lean_io_create_tempfile start here
--     ret = uv_fs_mkdtemp(NULL, &req, path, NULL);
--     if (ret < 0) {
--         uv_fs_req_cleanup(&req);
--         // If mkdtemp throws an error we cannot rely on path to contain a proper file name.
--         return io_result_mk_error(decode_uv_error(ret, nullptr));
--     } else {
--         obj_res res = lean_io_result_mk_ok(mk_string(req.path));
--         uv_fs_req_cleanup(&req);
--         return res;
--     }
-- }
-- 
-- extern "C" LEAN_EXPORT obj_res lean_io_remove_file(b_obj_arg filename) {
--     const char* fname = string_cstr(filename);
--     if (strlen(fname) != lean_string_size(filename) - 1) {
--         return mk_embedded_nul_error(filename);
--     }
--     uv_fs_t req;
--     int ret = uv_fs_unlink(NULL, &req, fname, NULL);
--     uv_fs_req_cleanup(&req);
--     if (ret < 0) {
--         return io_result_mk_error(decode_uv_error(ret, filename));
--     } else {
--         return io_result_mk_ok(box(0));
--     }
-- }
-- 
-- extern "C" LEAN_EXPORT obj_res lean_io_app_path() {
-- #if defined(LEAN_WINDOWS)
--     HMODULE hModule = GetModuleHandle(NULL);
--     char path[MAX_PATH];
--     GetModuleFileName(hModule, path, MAX_PATH);
--     std::string pathstr(path);
--     // Hack for making sure disk is lower case
--     // TODO(Leo): more robust solution
--     if (pathstr.size() >= 2 && pathstr[1] == ':') {
--         pathstr[0] = tolower(pathstr[0]);
--     }
--     return io_result_mk_ok(mk_string(pathstr));
-- #elif defined(__APPLE__)
--     char buf1[PATH_MAX];
--     char buf2[PATH_MAX];
--     uint32_t bufsize = PATH_MAX;
--     if (_NSGetExecutablePath(buf1, &bufsize) != 0)
--         return io_result_mk_error("failed to locate application");
--     if (!realpath(buf1, buf2))
--         return io_result_mk_error("failed to resolve symbolic links when locating application");
--     return io_result_mk_ok(mk_string(buf2));
-- #elif defined(LEAN_EMSCRIPTEN)
--     // See https://emscripten.org/docs/api_reference/emscripten.h.html#c.EM_ASM_INT
--     char* appPath = reinterpret_cast<char*>(EM_ASM_INT({
--         if ((typeof process === "undefined") || (process.release.name !== "node")) {
--             return 0;
--         }
-- 
--         var lengthBytes = lengthBytesUTF8(__filename)+1;
--         var pathOnWasmHeap = _malloc(lengthBytes);
--         stringToUTF8(__filename, pathOnWasmHeap, lengthBytes);
--         return pathOnWasmHeap;
--     }));
--     if (appPath == nullptr) {
--         return io_result_mk_error("no Lean executable file exists in WASM outside of Node.js");
--     }
-- 
--     object * appPathLean = mk_string(appPath);
--     free(appPath);
--     return io_result_mk_ok(appPathLean);
-- #else
--     // Linux version
--     char path[PATH_MAX];
--     char dest[PATH_MAX];
--     memset(dest, 0, PATH_MAX);
--     pid_t pid = getpid();
--     snprintf(path, PATH_MAX, "/proc/%d/exe", pid);
--     if (readlink(path, dest, PATH_MAX - 1) == -1) {
--         return io_result_mk_error("failed to locate application");
--     } else {
--         return io_result_mk_ok(mk_string(dest));
--     }
-- #endif
-- }
-- 
-- extern "C" LEAN_EXPORT obj_res lean_io_current_dir() {
--     char buffer[PATH_MAX];
--     char * cwd = getcwd(buffer, sizeof(buffer));
--     if (cwd) {
--         return io_result_mk_ok(mk_string(cwd));
--     } else {
--         return io_result_mk_error("failed to retrieve current working directory");
--     }
-- }
-- 
-- // =======================================
-- // ST ref primitives
-- 
-- 
-- extern "C" LEAN_EXPORT obj_res lean_st_mk_ref(obj_arg a) {
--     lean_ref_object * o = (lean_ref_object*)lean_alloc_small_object(sizeof(lean_ref_object));
--     lean_set_st_header((lean_object*)o, LeanRef, 0);
--     o->m_value = a;
--     return (lean_object*)o;
-- }
-- 
-- static inline atomic<object*> * mt_ref_val_addr(object * o) {
--     return reinterpret_cast<atomic<object*> *>(&(lean_to_ref(o)->m_value));
-- }
-- 
-- /*
--   Important: we have added support for initializing global constants
--   at program startup. This feature is particularly useful for
--   initializing `ST.Ref` values. Any `ST.Ref` value created during
--   initialization will be marked as persistent. Thus, to make `ST.Ref`
--   API thread-safe, we must treat persistent `ST.Ref` objects created
--   during initialization as a multi-threaded object. Then, whenever we store
--   a value `val` into a global `ST.Ref`, we have to mark `va`l as a multi-threaded
--   object as we do for multi-threaded `ST.Ref`s. It makes sense since
--   the global `ST.Ref` may be used to communicate data between threads.
-- */
-- static inline bool ref_maybe_mt(b_obj_arg ref) { return lean_is_mt(ref) || lean_is_persistent(ref); }
-- 
-- extern "C" LEAN_EXPORT obj_res lean_st_ref_get(b_obj_arg ref) {
--     if (ref_maybe_mt(ref)) {
--         atomic<object *> * val_addr = mt_ref_val_addr(ref);
--         while (true) {
--             /*
--               We cannot simply read `val` from the ref and `inc` it like in the `else` branch since someone else could
--               write to the ref in between and remove the last owning reference to the object. Instead, we must take
--               ownership of the RC token in the ref via `exchange`, duplicate it, then put one RC token back. */
--             object * val = val_addr->exchange(nullptr);
--             if (val != nullptr) {
--                 inc(val);
--                 object * tmp = val_addr->exchange(val);
--                 lean_assert(tmp == nullptr);
--                 (void)tmp;
--                 return val;
--             }
--         }
--     } else {
--         object * val = lean_to_ref(ref)->m_value;
--         lean_assert(val != nullptr);
--         inc(val);
--         return val;
--     }
-- }
-- 
-- extern "C" LEAN_EXPORT obj_res lean_st_ref_take(b_obj_arg ref) {
--     if (ref_maybe_mt(ref)) {
--         atomic<object *> * val_addr = mt_ref_val_addr(ref);
--         while (true) {
--             object * val = val_addr->exchange(nullptr);
--             if (val != nullptr)
--                 return val;
--         }
--     } else {
--         object * val = lean_to_ref(ref)->m_value;
--         lean_assert(val != nullptr);
--         lean_to_ref(ref)->m_value = nullptr;
--         return val;
--     }
-- }
-- 
-- static_assert(sizeof(atomic<unsigned short>) == sizeof(unsigned short), "`atomic<unsigned short>` and `unsigned short` must have the same size"); // NOLINT
-- 
-- extern "C" LEAN_EXPORT obj_res lean_st_ref_put(b_obj_arg ref, obj_arg a) {
--     if (ref_maybe_mt(ref)) {
--         /* We must mark `a` as multi-threaded if `ref` is marked as multi-threaded.
--            Reason: our runtime relies on the fact that a single-threaded object
--            cannot be reached from a multi-thread object. */
--         mark_mt(a);
--         atomic<object *> * val_addr = mt_ref_val_addr(ref);
--         object * old_a = val_addr->exchange(a);
--         lean_assert(old_a == nullptr);
--         (void)old_a;
--         return box(0);
--     } else {
--         if (lean_to_ref(ref)->m_value != nullptr)
--             dec(lean_to_ref(ref)->m_value);
--         lean_to_ref(ref)->m_value = a;
--         return box(0);
--     }
-- }
-- 
-- extern "C" LEAN_EXPORT obj_res lean_st_ref_swap(b_obj_arg ref, obj_arg a) {
--     if (ref_maybe_mt(ref)) {
--         /* See io_ref_write */
--         mark_mt(a);
--         atomic<object *> * val_addr = mt_ref_val_addr(ref);
--         while (true) {
--             object * old_a = val_addr->load();
--             if (old_a != nullptr && val_addr->compare_exchange_strong(old_a, a))
--                 return old_a;
--         }
--     } else {
--         object * old_a = lean_to_ref(ref)->m_value;
--         if (old_a == nullptr)
--             lean_internal_panic("null reference read");
--         lean_to_ref(ref)->m_value = a;
--         return old_a;
--     }
-- }
-- 
-- extern "C" LEAN_EXPORT uint8_t lean_st_ref_ptr_eq(b_obj_arg ref1, b_obj_arg ref2) {
--     return lean_to_ref(ref1) == lean_to_ref(ref2);
-- }
-- 
-- /* {α : Type} (act : BaseIO α) (_ : IO.RealWorld) : α */
-- static obj_res lean_io_as_task_fn(obj_arg act, obj_arg) {
--     object_ref r(apply_1(act, io_mk_world()));
--     return object_ref(r.raw(), true).steal();
-- }
-- 
-- /* asTask {α : Type} (act : BaseIO α) (prio : Nat) : BaseIO (Task α) */
-- extern "C" LEAN_EXPORT obj_res lean_io_as_task(obj_arg act, obj_arg prio) {
--     object * c = lean_alloc_closure((void*)lean_io_as_task_fn, 2, 1);
--     lean_closure_set(c, 0, act);
--     object * t = lean_task_spawn_core(c, lean_unbox(prio), /* keep_alive */ true);
--     return t;
-- }
-- 
-- /* {α β : Type} (f : α → BaseIO β) (a : α) : β */
-- static obj_res lean_io_bind_task_fn(obj_arg f, obj_arg a) {
--     object_ref r(apply_2(f, a, io_mk_world()));
--     return object_ref(r.raw(), true).steal();
-- }
-- 
-- /*  mapTask (f : α → BaseIO β) (t : Task α) (prio : Nat) (sync : Bool) : BaseIO (Task β) */
-- extern "C" LEAN_EXPORT obj_res lean_io_map_task(obj_arg f, obj_arg t, obj_arg prio, uint8 sync) {
--     object * c = lean_alloc_closure((void*)lean_io_bind_task_fn, 2, 1);
--     lean_closure_set(c, 0, f);
--     object * t2 = lean_task_map_core(c, t, lean_unbox(prio), sync, /* keep_alive */ true);
--     return t2;
-- }
-- 
-- /*  bindTask (t : Task α) (f : α → BaseIO (Task β)) (prio : Nat) (sync : Bool) : BaseIO (Task β) */
-- extern "C" LEAN_EXPORT obj_res lean_io_bind_task(obj_arg t, obj_arg f, obj_arg prio, uint8 sync) {
--     object * c = lean_alloc_closure((void*)lean_io_bind_task_fn, 2, 1);
--     lean_closure_set(c, 0, f);
--     object * t2 = lean_task_bind_core(t, c, lean_unbox(prio), sync, /* keep_alive */ true);
--     return t2;
-- }
-- 
-- extern "C" LEAN_EXPORT uint8_t lean_io_check_canceled() {
--     return lean_io_check_canceled_core();
-- }
-- 
-- extern "C" LEAN_EXPORT obj_res lean_io_cancel(b_obj_arg t) {
--     lean_io_cancel_core(t);
--     return box(0);
-- }
-- 
-- extern "C" LEAN_EXPORT uint8_t lean_io_get_task_state(b_obj_arg t) {
--     return lean_io_get_task_state_core(t);
-- }
-- 
-- extern "C" LEAN_EXPORT obj_res lean_io_wait(obj_arg t) {
--     return lean_task_get_own(t);
-- }
-- 
-- extern "C" LEAN_EXPORT obj_res lean_io_wait_any(b_obj_arg task_list) {
--     object * t = lean_io_wait_any_core(task_list);
--     object * v = lean_task_get(t);
--     lean_inc(v);
--     return v;
-- }
-- 
-- extern "C" LEAN_EXPORT obj_res lean_io_exit(uint8_t code) {
--     exit(code);
-- }
-- 
-- extern "C" LEAN_EXPORT obj_res lean_io_force_exit(uint8_t code) {
--     std::_Exit((int)code);
-- }
-- 
-- extern "C" LEAN_EXPORT obj_res lean_runtime_mark_multi_threaded(obj_arg a) {
--     lean_mark_mt(a);
--     return a;
-- }
-- 
-- extern "C" LEAN_EXPORT obj_res lean_runtime_mark_persistent(obj_arg a) {
--     lean_mark_persistent(a);
--     return a;
-- }
-- 
-- #if defined(__has_feature)
-- #if __has_feature(address_sanitizer)
-- #include <sanitizer/lsan_interface.h>
-- #endif
-- #endif
-- 
-- extern "C" LEAN_EXPORT obj_res lean_runtime_forget(obj_arg o) {
-- #if defined(__has_feature)
-- #if __has_feature(address_sanitizer)
--     __lsan_ignore_object(o);
-- #endif
-- #endif
--     return box(0);
-- }
-- 
-- extern "C" LEAN_EXPORT obj_res lean_option_get_or_block(obj_arg o_opt) {
--     option_ref<object_ref> opt = option_ref<object_ref>(o_opt);
--     if (opt) {
--         return opt.get_val().steal();
--     } else {
--         lean_panic("PANIC: Promise.result!: promise has been dropped without ever being resolved",
--           /* force_stderr */ true);
--         // this is only reachable when using non-fatal panics
--         while (true) {
--             this_thread::sleep_for(std::chrono::seconds::max());
--         }
--     }
-- }
-- 
-- void initialize_io() {
--     g_io_handle_external_class = lean_register_external_class(io_handle_finalizer, io_handle_foreach);
-- #if defined(LEAN_WINDOWS)
--     _setmode(_fileno(stdout), _O_BINARY);
--     _setmode(_fileno(stderr), _O_BINARY);
--     _setmode(_fileno(stdin), _O_BINARY);
-- #endif
--     g_stream_stdout = lean_stream_of_handle(io_wrap_handle(stdout));
--     mark_persistent(g_stream_stdout);
--     g_stream_stderr = lean_stream_of_handle(io_wrap_handle(stderr));
--     mark_persistent(g_stream_stderr);
--     g_stream_stdin  = lean_stream_of_handle(io_wrap_handle(stdin));
--     mark_persistent(g_stream_stdin);
-- #if !defined(LEAN_WINDOWS) && !defined(LEAN_EMSCRIPTEN)
--     // We want to handle SIGPIPE ourselves
--     lean_always_assert(signal(SIGPIPE, SIG_IGN) != SIG_ERR);
-- #endif
-- }
-- 
-- void finalize_io() {
-- }
-- }
-- ```
def lean_io_create_dir := [JS_EXPR|throw new Error("lean_io_create_dir not implemented")]

-- ```lean
-- opaque rename (old new : @& FilePath) : IO Unit
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_rename(b_obj_arg from, b_obj_arg to) {
--     const char* from_str = string_cstr(from);
--     if (strlen(from_str) != lean_string_size(from) - 1) {
--         return mk_embedded_nul_error(from);
--     }
--     const char* to_str = string_cstr(to);
--     if (strlen(to_str) != lean_string_size(to) - 1) {
--         return mk_embedded_nul_error(to);
--     }
-- #ifdef LEAN_WINDOWS
--     // Note: On windows, std::rename gives an error if the `to` file already exists,
--     // so we have to call the underlying windows API directly to get behavior consistent
--     // with the unix-like OSs
--     bool ok = MoveFileEx(from_str, to_str, MOVEFILE_REPLACE_EXISTING) != 0;
--     if (!ok) {
--         // TODO: actually produce the right type of IO error
--         return io_result_mk_error((sstream()
--             << "failed to rename '" << from_str << "' to '" << to_str << "': " << GetLastError()).str());
--     }
-- #else
--     bool ok = std::rename(from_str, to_str) == 0;
--     if (!ok) {
--         std::ostringstream s;
--         s << from_str << " and/or " << to_str;
--         object_ref out{mk_string(s.str())};
--         return io_result_mk_error(decode_io_error(errno, out.raw()));
--     }
-- #endif
--     return io_result_mk_ok(box(0));
-- }
-- ```
def lean_io_rename := [JS_EXPR|throw new Error("lean_io_rename not implemented")]

-- ```lean
-- opaque hardLink (orig link : @& FilePath) : IO Unit
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_hard_link(b_obj_arg orig, b_obj_arg link) {
--     const char* orig_str = string_cstr(orig);
--     if (strlen(orig_str) != lean_string_size(orig) - 1) {
--         return mk_embedded_nul_error(orig);
--     }
--     const char* link_str = string_cstr(link);
--     if (strlen(link_str) != lean_string_size(link) - 1) {
--         return mk_embedded_nul_error(link);
--     }
--     uv_fs_t req;
--     int ret = uv_fs_link(NULL, &req, orig_str, link_str, NULL);
--     uv_fs_req_cleanup(&req);
--     if (ret < 0) {
--         return io_result_mk_error(decode_uv_error(ret, orig));
--     } else {
--         return io_result_mk_ok(box(0));
--     }
-- }
-- ```
def lean_io_hard_link := [JS_EXPR|throw new Error("lean_io_hard_link not implemented")]

-- ```lean
-- opaque createTempFile : IO (Handle × FilePath)
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_create_tempfile(lean_object * /* w */) {
--     char path[PATH_MAX];
--     size_t base_len = PATH_MAX;
--     int ret = uv_os_tmpdir(path, &base_len);
--     if (ret < 0) {
--         return io_result_mk_error(decode_uv_error(ret, nullptr));
--     } else if (base_len == 0) {
--         return lean_io_result_mk_error(decode_uv_error(UV_ENOENT, mk_string("")));
--     }
-- 
-- #if defined(LEAN_WINDOWS)
--     // On Windows `GetTempPathW` always returns a path ending in \, but libuv removes it.
--     // https://learn.microsoft.com/en-us/windows/win32/fileio/creating-and-using-a-temporary-file
--     if (path[base_len - 1] != '\\') {
--         lean_always_assert(PATH_MAX >= base_len + 1 + 1);
--         strcat(path, "\\");
--     }
-- #else
--     // No guarantee that we have a trailing / in TMPDIR.
--     if (path[base_len - 1] != '/') {
--         lean_always_assert(PATH_MAX >= base_len + 1 + 1);
--         strcat(path, "/");
--     }
-- #endif
-- 
--     const char* file_pattern = "tmp.XXXXXXXX";
--     const size_t file_pattern_size = strlen(file_pattern);
--     lean_always_assert(PATH_MAX >= strlen(path) + file_pattern_size + 1);
--     strcat(path, file_pattern);
-- 
--     uv_fs_t req;
--     // Differences from lean_io_create_tempdir start here
--     ret = uv_fs_mkstemp(NULL, &req, path, NULL);
--     if (ret < 0) {
--         uv_fs_req_cleanup(&req);
--         // If mkstemp throws an error we cannot rely on path to contain a proper file name.
--         return io_result_mk_error(decode_uv_error(ret, nullptr));
--     } else {
--         FILE* handle = fdopen(req.result, "r+");
--         object_ref pair = mk_cnstr(0, io_wrap_handle(handle), mk_string(req.path));
--         uv_fs_req_cleanup(&req);
--         return lean_io_result_mk_ok(pair.steal());
--     }
-- }
-- ```
def lean_io_create_tempfile := [JS_EXPR|"/tmp/lean_tmp_file"]

-- ```lean
-- opaque createTempDir : IO FilePath
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_create_tempdir(lean_object * /* w */) {
--     char path[PATH_MAX];
--     size_t base_len = PATH_MAX;
--     int ret = uv_os_tmpdir(path, &base_len);
--     if (ret < 0) {
--         return io_result_mk_error(decode_uv_error(ret, nullptr));
--     } else if (base_len == 0) {
--         return lean_io_result_mk_error(decode_uv_error(UV_ENOENT, mk_string("")));
--     }
-- 
-- #if defined(LEAN_WINDOWS)
--     // On Windows `GetTempPathW` always returns a path ending in \, but libuv removes it.
--     // https://learn.microsoft.com/en-us/windows/win32/fileio/creating-and-using-a-temporary-file
--     if (path[base_len - 1] != '\\') {
--         lean_always_assert(PATH_MAX >= base_len + 1 + 1);
--         strcat(path, "\\");
--     }
-- #else
--     // No guarantee that we have a trailing / in TMPDIR.
--     if (path[base_len - 1] != '/') {
--         lean_always_assert(PATH_MAX >= base_len + 1 + 1);
--         strcat(path, "/");
--     }
-- #endif
-- 
--     const char* file_pattern = "tmp.XXXXXXXX";
--     const size_t file_pattern_size = strlen(file_pattern);
--     lean_always_assert(PATH_MAX >= strlen(path) + file_pattern_size + 1);
--     strcat(path, file_pattern);
-- 
--     uv_fs_t req;
--     // Differences from lean_io_create_tempfile start here
--     ret = uv_fs_mkdtemp(NULL, &req, path, NULL);
--     if (ret < 0) {
--         uv_fs_req_cleanup(&req);
--         // If mkdtemp throws an error we cannot rely on path to contain a proper file name.
--         return io_result_mk_error(decode_uv_error(ret, nullptr));
--     } else {
--         obj_res res = lean_io_result_mk_ok(mk_string(req.path));
--         uv_fs_req_cleanup(&req);
--         return res;
--     }
-- }
-- ```
def lean_io_create_tempdir := [JS_EXPR|"/tmp/lean_tmp_dir"]

-- ```lean
-- opaque getEnv (var : @& String) : BaseIO (Option String)
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_getenv(b_obj_arg env_var) {
--     const char* env_var_str = string_cstr(env_var);
--     if (strlen(env_var_str) != lean_string_size(env_var) - 1) {
--         return mk_option_none();
--     }
-- #if defined(LEAN_EMSCRIPTEN)
--     // HACK(WN): getenv doesn't seem to work in Emscripten even though it should
--     // see https://emscripten.org/docs/porting/connecting_cpp_and_javascript/Interacting-with-code.html#interacting-with-code-environment-variables
--     char* val = reinterpret_cast<char*>(EM_ASM_INT({
--         var envVar = UTF8ToString($0);
--         var val = ENV[envVar];
--         if (val) {
--             var lengthBytes = lengthBytesUTF8(val)+1;
--             var valOnWasmHeap = _malloc(lengthBytes);
--             stringToUTF8(val, valOnWasmHeap, lengthBytes);
--             return valOnWasmHeap;
--         } else {
--             return 0;
--         }
--     }, env_var_str));
-- 
--     if (val) {
--         object * valLean = mk_string(val);
--         free(val);
--         return mk_option_some(valLean);
--     } else {
--         return mk_option_none();
--     }
-- #else
--     char * val = std::getenv(env_var_str);
--     if (val) {
--         return mk_option_some(mk_string(val));
--     } else {
--         return mk_option_none();
--     }
-- #endif
-- }
-- ```
def lean_io_getenv := [JS_EXPR|throw new Error("lean_io_getenv not implemented")]

-- ```lean
-- opaque appPath : IO FilePath
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_app_path() {
-- #if defined(LEAN_WINDOWS)
--     HMODULE hModule = GetModuleHandle(NULL);
--     char path[MAX_PATH];
--     GetModuleFileName(hModule, path, MAX_PATH);
--     std::string pathstr(path);
--     // Hack for making sure disk is lower case
--     // TODO(Leo): more robust solution
--     if (pathstr.size() >= 2 && pathstr[1] == ':') {
--         pathstr[0] = tolower(pathstr[0]);
--     }
--     return io_result_mk_ok(mk_string(pathstr));
-- #elif defined(__APPLE__)
--     char buf1[PATH_MAX];
--     char buf2[PATH_MAX];
--     uint32_t bufsize = PATH_MAX;
--     if (_NSGetExecutablePath(buf1, &bufsize) != 0)
--         return io_result_mk_error("failed to locate application");
--     if (!realpath(buf1, buf2))
--         return io_result_mk_error("failed to resolve symbolic links when locating application");
--     return io_result_mk_ok(mk_string(buf2));
-- #elif defined(LEAN_EMSCRIPTEN)
--     // See https://emscripten.org/docs/api_reference/emscripten.h.html#c.EM_ASM_INT
--     char* appPath = reinterpret_cast<char*>(EM_ASM_INT({
--         if ((typeof process === "undefined") || (process.release.name !== "node")) {
--             return 0;
--         }
-- 
--         var lengthBytes = lengthBytesUTF8(__filename)+1;
--         var pathOnWasmHeap = _malloc(lengthBytes);
--         stringToUTF8(__filename, pathOnWasmHeap, lengthBytes);
--         return pathOnWasmHeap;
--     }));
--     if (appPath == nullptr) {
--         return io_result_mk_error("no Lean executable file exists in WASM outside of Node.js");
--     }
-- 
--     object * appPathLean = mk_string(appPath);
--     free(appPath);
--     return io_result_mk_ok(appPathLean);
-- #else
--     // Linux version
--     char path[PATH_MAX];
--     char dest[PATH_MAX];
--     memset(dest, 0, PATH_MAX);
--     pid_t pid = getpid();
--     snprintf(path, PATH_MAX, "/proc/%d/exe", pid);
--     if (readlink(path, dest, PATH_MAX - 1) == -1) {
--         return io_result_mk_error("failed to locate application");
--     } else {
--         return io_result_mk_ok(mk_string(dest));
--     }
-- #endif
-- }
-- ```
def lean_io_app_path := [JS_EXPR|process.argv[1] || ""]

-- ```lean
-- opaque currentDir : IO FilePath
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_current_dir() {
--     char buffer[PATH_MAX];
--     char * cwd = getcwd(buffer, sizeof(buffer));
--     if (cwd) {
--         return io_result_mk_ok(mk_string(cwd));
--     } else {
--         return io_result_mk_error("failed to retrieve current working directory");
--     }
-- }
-- ```
def lean_io_current_dir := [JS_EXPR|process.cwd( )]

-- ```lean
-- opaque readDir : @& FilePath → IO (Array IO.FS.DirEntry)
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_read_dir(b_obj_arg dirname) {
--     const char* dirname_ptr = string_cstr(dirname);
--     if (strlen(dirname_ptr) != lean_string_size(dirname) - 1) {
--         return mk_embedded_nul_error(dirname);
--     }
--     object * arr = array_mk_empty();
--     DIR * dp = opendir(dirname_ptr);
--     if (!dp) {
--         return io_result_mk_error(decode_io_error(errno, dirname));
--     }
--     while (dirent * entry = readdir(dp)) {
--         if (strcmp(entry->d_name, ".") == 0 || strcmp(entry->d_name, "..") == 0) {
--             continue;
--         }
--         object * lentry = alloc_cnstr(0, 2, 0);
--         lean_inc(dirname);
--         cnstr_set(lentry, 0, dirname);
--         cnstr_set(lentry, 1, lean_mk_string(entry->d_name));
--         arr = lean_array_push(arr, lentry);
--     }
--     lean_always_assert(closedir(dp) == 0);
--     return io_result_mk_ok(arr);
-- }
-- ```
def lean_io_read_dir := [JS_EXPR|throw new Error("lean_io_read_dir not implemented")]

-- ```lean
-- opaque metadata : @& FilePath → IO IO.FS.Metadata
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_metadata(b_obj_arg filename) {
--     const char* fname = string_cstr(filename);
--     if (strlen(fname) != lean_string_size(filename) - 1) {
--         return mk_embedded_nul_error(filename);
--     }
--     uv_fs_t req;
--     int ret = uv_fs_stat(NULL, &req, fname, NULL);
--     if (ret < 0) {
--         uv_fs_req_cleanup(&req);
--         return io_result_mk_error(decode_uv_error(ret, filename));
--     } else {
--         object* mdata = metadata_core(req.statbuf);
--         uv_fs_req_cleanup(&req);
--         return mdata;
--     }
-- }
-- ```
def lean_io_metadata := [JS_EXPR|throw new Error("lean_io_metadata not implemented")]

-- ```lean
-- opaque symlinkMetadata : @& FilePath → IO IO.FS.Metadata
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_symlink_metadata(b_obj_arg filename) {
-- #ifdef LEAN_WINDOWS
--     return lean_io_metadata(filename);
-- #else
--     const char* fname = string_cstr(filename);
--     if (strlen(fname) != lean_string_size(filename) - 1) {
--         return mk_embedded_nul_error(filename);
--     }
--     uv_fs_t req;
--     int ret = uv_fs_lstat(NULL, &req, fname, NULL);
--     if (ret < 0) {
--         uv_fs_req_cleanup(&req);
--         return io_result_mk_error(decode_uv_error(ret, filename));
--     } else {
--         object* mdata = metadata_core(req.statbuf);
--         uv_fs_req_cleanup(&req);
--         return mdata;
--     }
-- #endif
-- }
-- ```
def lean_io_symlink_metadata := [JS_EXPR|throw new Error("lean_io_symlink_metadata not implemented")]

-- ```lean
-- opaque getCurrentDir : IO FilePath
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_process_get_current_dir() {
--     char path[MAX_PATH];
--     DWORD sz = GetCurrentDirectory(MAX_PATH, path);
--     if (sz != 0) {
--         return io_result_mk_ok(lean_mk_string_from_bytes(path, sz));
--     } else {
--         return io_result_mk_error((sstream() << GetLastError()).str());
--     }
-- }
-- ```
def lean_io_process_get_current_dir := [JS_EXPR|process.cwd( )]

-- ```lean
-- opaque setCurrentDir (path : @& FilePath) : IO Unit
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_process_set_current_dir(b_obj_arg path) {
--     if (SetCurrentDirectory(string_cstr(path))) {
--         return io_result_mk_ok(box(0));
--     } else {
--         return io_result_mk_error((sstream() << GetLastError()).str());
--     }
-- }
-- ```
def lean_io_process_set_current_dir := [JS_EXPR|throw new Error("lean_io_process_set_current_dir not implemented")]

-- ```lean
-- opaque getPID : BaseIO UInt32
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint32_t lean_io_process_get_pid() {
--     static_assert(sizeof(pid_t) == sizeof(uint32), "pid_t is expected to be a 32-bit type"); // NOLINT
--     return getpid();
-- }
-- ```
def lean_io_process_get_pid := [JS_EXPR|BigInt(process.pid)]

-- ```lean
-- opaque spawn (args : SpawnArgs) : IO (Child args.toStdioConfig)
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_process_spawn(obj_arg args_) {
--     object_ref args(args_);
--     object_ref stdio_cfg = cnstr_get_ref(args, 0);
--     stdio stdin_mode  = static_cast<stdio>(cnstr_get_uint8(stdio_cfg.raw(), 0));
--     stdio stdout_mode = static_cast<stdio>(cnstr_get_uint8(stdio_cfg.raw(), 1));
--     stdio stderr_mode = static_cast<stdio>(cnstr_get_uint8(stdio_cfg.raw(), 2));
--     if (stdin_mode == stdio::INHERIT) {
--         std::cout.flush();
--     }
--     try {
--         return spawn(
--                 cnstr_get_ref_t<string_ref>(args, 1),
--                 cnstr_get_ref_t<array_ref<string_ref>>(args, 2),
--                 stdin_mode,
--                 stdout_mode,
--                 stderr_mode,
--                 cnstr_get_ref_t<option_ref<string_ref>>(args, 3),
--                 cnstr_get_ref_t<array_ref<pair_ref<string_ref, option_ref<string_ref>>>>(args, 4),
--                 cnstr_get_uint8(args.raw(), 5 * sizeof(object *)),
--                 cnstr_get_uint8(args.raw(), 5 * sizeof(object *) + 1));
--     } catch (int err) {
--         return lean_io_result_mk_error(decode_io_error(err, nullptr));
--     } catch (std::system_error const & err) {
--         // TODO: decode
--         return lean_io_result_mk_error(lean_mk_io_error_other_error(err.code().value(), mk_string(err.code().message())));
--     }
-- }
-- ```
def lean_io_process_spawn := [JS_EXPR|throw new Error("lean_io_process_spawn not implemented")]

-- ```lean
-- opaque Child.wait {cfg : @& StdioConfig} : @& Child cfg → IO UInt32
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_process_child_wait(b_obj_arg, b_obj_arg child) {
--     static_assert(sizeof(pid_t) == sizeof(uint32), "pid_t is expected to be a 32-bit type"); // NOLINT
--     pid_t pid = cnstr_get_uint32(child, 3 * sizeof(object *));
--     int status;
--     if (waitpid(pid, &status, 0) == -1) {
--         return io_result_mk_error(decode_io_error(errno, nullptr));
--     }
--     if (WIFEXITED(status)) {
--         return lean_io_result_mk_ok(box_uint32(static_cast<unsigned>(WEXITSTATUS(status))));
--     } else {
--         lean_assert(WIFSIGNALED(status));
--         // use bash's convention
--         return lean_io_result_mk_ok(box_uint32(128 + static_cast<unsigned>(WTERMSIG(status))));
--     }
-- }
-- ```
def lean_io_process_child_wait := [JS_EXPR|0]

-- ```lean
-- opaque Child.tryWait {cfg : @& StdioConfig} : @& Child cfg →
--     IO (Option UInt32)
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_process_child_try_wait(b_obj_arg, b_obj_arg child) {
--     static_assert(sizeof(pid_t) == sizeof(uint32), "pid_t is expected to be a 32-bit type"); // NOLINT
--     pid_t pid = cnstr_get_uint32(child, 3 * sizeof(object *));
--     int status;
--     int ret = waitpid(pid, &status, WNOHANG);
--     if (ret == -1) {
--         return io_result_mk_error(decode_io_error(errno, nullptr));
--     } else if (ret == 0) {
--         return io_result_mk_ok(mk_option_none());
--     } else {
--         if (WIFEXITED(status)) {
--             obj_res output = box_uint32(static_cast<unsigned>(WEXITSTATUS(status)));
--             return lean_io_result_mk_ok(mk_option_some(output));
--         } else {
--             lean_assert(WIFSIGNALED(status));
--             // use bash's convention
--             obj_res output = box_uint32(128 + static_cast<unsigned>(WTERMSIG(status)));
--             return lean_io_result_mk_ok(mk_option_some(output));
--         }
--     }
-- }
-- ```
def lean_io_process_child_try_wait := [JS_EXPR|mkObject(`Option.some, 0)]

-- ```lean
-- opaque Child.kill {cfg : @& StdioConfig} : @& Child cfg → IO Unit
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_process_child_kill(b_obj_arg, b_obj_arg child) {
--     static_assert(sizeof(pid_t) == sizeof(uint32), "pid_t is expected to be a 32-bit type"); // NOLINT
--     pid_t pid = cnstr_get_uint32(child, 3 * sizeof(object *));
--     bool setsid = cnstr_get_uint8(child, 3 * sizeof(object *) + sizeof(pid_t));
--     if ((setsid ? killpg(pid, SIGKILL) : kill(pid, SIGKILL)) == -1) {
--         return io_result_mk_error(decode_io_error(errno, nullptr));
--     }
--     return lean_io_result_mk_ok(box(0));
-- }
-- ```
def lean_io_process_child_kill := [JS_EXPR|null]

-- ```lean
-- opaque Child.takeStdin {cfg : @& StdioConfig} : Child cfg →
--     IO (cfg.stdin.toHandleType × Child { cfg with stdin := Stdio.null })
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_process_child_take_stdin(b_obj_arg, obj_arg lchild) {
--     object_ref child(lchild);
--     object_ref child2 = mk_cnstr(0, object_ref(box(0)), cnstr_get_ref(child, 1), cnstr_get_ref(child, 2), sizeof(pid_t));
--     cnstr_set_uint32(child2.raw(), 3 * sizeof(object *), cnstr_get_uint32(child.raw(), 3 * sizeof(object *)));
--     object_ref r = mk_cnstr(0, cnstr_get_ref(child, 0), child2);
--     return lean_io_result_mk_ok(r.steal());
-- }
-- ```
def lean_io_process_child_take_stdin := [JS_EXPR|null]

-- ```lean
-- opaque Child.pid {cfg : @& StdioConfig} : Child cfg → UInt32
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint32_t lean_io_process_child_pid(b_obj_arg, b_obj_arg child) {
--     static_assert(sizeof(pid_t) == sizeof(uint32), "pid_t is expected to be a 32-bit type"); // NOLINT
--     pid_t pid = cnstr_get_uint32(child, 3 * sizeof(object *));
--     return pid;
-- }
-- ```
def lean_io_process_child_pid := [JS_EXPR|0]

-- ```lean
-- opaque exit : UInt8 → IO α
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_exit(uint8_t code) {
--     exit(code);
-- }
-- ```
def lean_io_exit := [JS_EXPR|throw new Error("lean_io_exit not implemented")]

-- ```lean
-- opaque forceExit : UInt8 → IO α
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_force_exit(uint8_t code) {
--     std::_Exit((int)code);
-- }
-- ```
def lean_io_force_exit := [JS_EXPR|throw new Error("lean_io_force_exit not implemented")]

-- ```lean
-- opaque getTID : BaseIO UInt64
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint64_t lean_io_get_tid() {
--     uint64_t tid;
-- #ifdef __APPLE__
--     lean_always_assert(pthread_threadid_np(NULL, &tid) == 0);
-- #elif defined(LEAN_EMSCRIPTEN)
--     tid = 0;
-- #else
--     // since Linux 2.4.11, our glibc 2.27 requires at least 3.2
--     // glibc 2.30 would provide a wrapper
--     tid = (pid_t)syscall(SYS_gettid);
-- #endif
--     return tid;
-- }
-- ```
def lean_io_get_tid := [JS_EXPR|0]

-- ```lean
-- opaque Prim.setAccessRights (filename : @& FilePath) (mode : UInt32) : IO Unit
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_chmod (b_obj_arg filename, uint32_t mode) {
--     const char* fname = string_cstr(filename);
--     if (strlen(fname) != lean_string_size(filename) - 1) {
--         return mk_embedded_nul_error(filename);
--     }
--     if (!chmod(fname, mode)) {
--         return io_result_mk_ok(box(0));
--     } else {
--         return io_result_mk_error(decode_io_error(errno, filename));
--     }
-- }
-- ```
def lean_chmod := [JS_EXPR|throw new Error("lean_chmod not implemented")]

-- ```lean
-- def Runtime.markMultiThreaded (a : α) : BaseIO α := return a
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_runtime_mark_multi_threaded(obj_arg a) {
--     lean_mark_mt(a);
--     return a;
-- }
-- ```
def lean_runtime_mark_multi_threaded := [JS_EXPR|throw new Error("lean_runtime_mark_multi_threaded not implemented")]

-- ```lean
-- unsafe def Runtime.markPersistent (a : α) : BaseIO α := return a
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_runtime_mark_persistent(obj_arg a) {
--     lean_mark_persistent(a);
--     return a;
-- }
-- ```
def lean_runtime_mark_persistent := [JS_EXPR|throw new Error("lean_runtime_mark_persistent not implemented")]

-- ```lean
-- def Runtime.forget (a : α) : BaseIO Unit := return
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_runtime_forget(obj_arg o) {
-- #if defined(__has_feature)
-- #if __has_feature(address_sanitizer)
--     __lsan_ignore_object(o);
-- #endif
-- #endif
--     return box(0);
-- }
-- ```
def lean_runtime_forget := [JS_EXPR|throw new Error("lean_runtime_forget not implemented")]

-- ```lean
-- def Runtime.hold (a : @& α) : BaseIO Unit := return
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_runtime_hold(b_lean_obj_arg a) {
--     return lean_box(0);
-- }
-- ```
def lean_runtime_hold := [JS_EXPR|throw new Error("lean_runtime_hold not implemented")]

-- ============
-- Init.System.Promise
-- ============

-- ```lean
-- opaque Promise.new [Nonempty α] : BaseIO (Promise α)
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_promise_new() {
--     lean_object * o = lean_promise_new();
--     return o;
-- }
-- ```
def lean_io_promise_new := [JS_EXPR|throw new Error("not implemented")]

-- ```lean
-- opaque Promise.resolve (value : α) (promise : @& Promise α) : BaseIO Unit
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_promise_resolve(obj_arg value, b_obj_arg promise) {
--     lean_promise_resolve(value, promise);
--     return box(0);
-- }
-- ```
def lean_io_promise_resolve := [JS_EXPR|throw new Error("not implemented")]

-- ```lean
-- opaque Promise.result? (promise : @& Promise α) : Task (Option α)
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_io_promise_result_opt(b_obj_arg promise) {
--     lean_object * t = (lean_object *)lean_to_promise(promise)->m_result;
--     lean_inc_ref(t);
--     return t;
-- }
-- ```
def lean_io_promise_result_opt := [JS_EXPR|throw new Error("not implemented")]

-- ```lean
-- private opaque Option.getOrBlock! [Nonempty α] : Option α → α
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_option_get_or_block(obj_arg o_opt) {
--     option_ref<object_ref> opt = option_ref<object_ref>(o_opt);
--     if (opt) {
--         return opt.get_val().steal();
--     } else {
--         lean_panic("PANIC: Promise.result!: promise has been dropped without ever being resolved",
--           /* force_stderr */ true);
--         // this is only reachable when using non-fatal panics
--         while (true) {
--             this_thread::sleep_for(std::chrono::seconds::max());
--         }
--     }
-- }
-- ```
def lean_option_get_or_block := [JS_EXPR|throw new Error("not implemented")]

-- ============
-- Init.ShareCommon
-- ============

-- ```lean
-- unsafe opaque Object.eq (a b : @& Object) : Bool
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8 lean_sharecommon_eq(b_obj_arg o1, b_obj_arg o2) {
--     lean_assert(!lean_is_scalar(o1));
--     lean_assert(!lean_is_scalar(o2));
--     size_t sz1 = lean_object_data_byte_size(o1);
--     size_t sz2 = lean_object_data_byte_size(o2);
--     if (sz1 != sz2) return false;
--     // compare relevant parts of the header
--     uint8_t tag = lean_ptr_tag(o1);
--     if (tag != lean_ptr_tag(o2)) return false;
--     if (lean_ptr_other(o1) != lean_ptr_other(o2)) return false;
--     if (tag == LeanMPZ) {
--         return mpz_value(o1) == mpz_value(o2);
--     } else {
--         size_t header_sz = sizeof(lean_object);
--         lean_assert(sz1 >= header_sz);
--         // compare objects' bodies
--         return memcmp(reinterpret_cast<char*>(o1) + header_sz, reinterpret_cast<char*>(o2) + header_sz, sz1 - header_sz) == 0;
--     }
-- }
-- ```
def lean_sharecommon_eq := [JS_EXPR|throw new Error("not implemented")]

-- ```lean
-- unsafe opaque Object.hash (a : @& Object) : UInt64
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint64_t lean_sharecommon_hash(b_obj_arg o) {
--     lean_assert(!lean_is_scalar(o));
--     size_t sz = lean_object_data_byte_size(o);
--     size_t header_sz = sizeof(lean_object);
--     uint8_t tag = lean_ptr_tag(o);
--     if (tag == LeanMPZ) {
--         return hash(tag, mpz_value(o).hash());
--     } else {
--         // hash relevant parts of the header
--         unsigned init = hash(tag, lean_ptr_other(o));
--         // hash body
--         return hash_str(sz - header_sz, reinterpret_cast<unsigned char const *>(o) + header_sz, init);
--     }
-- }
-- ```
def lean_sharecommon_hash := [JS_EXPR|throw new Error("not implemented")]

-- ```lean
-- def State.shareCommon {σ : @& StateFactory} (s : State σ) (a : α) : α × State σ := (a, s)
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_state_sharecommon(b_obj_arg tc, obj_arg s, obj_arg a) {
--     return sharecommon_fn(tc, s)(a);
-- }
-- ```
def lean_state_sharecommon := [JS_EXPR|throw new Error("not implemented")]

-- ```lean
-- def ShareCommon.shareCommon' (a : @& α) : α := a
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_sharecommon_quick(obj_arg a) {
--     return sharecommon_quick_fn()(a);
-- }
-- ```
def lean_sharecommon_quick := [JS_EXPR|throw new Error("not implemented")]
