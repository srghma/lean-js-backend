module

public import LakeJs.Ty

@[expose] public section

namespace LakeJs.LeanImpureExtern

open LakeJs.Ty


inductive LeanPureExtern : List Ty → Ty → Type where
-- # Lean Init/Prelude runtime extern functions mapped to `Ty`
-- ## The polymorphic externs come first
--
-- A constructor that carries a field — here, the type argument of a polymorphic extern —
-- must have a small runtime tag, so every constructor with a field is declared before the
-- ones without.  Each one keeps the row of the table it was taken from; the rest of the
-- catalogue below is ordered by the Lean source file the extern is declared in.
-- | lean_sorry                        | axiom       | sorryAx                     | (α : Sort u) → Bool → α                                                    |
  | lean_sorry                      : (α : Ty) → LeanPureExtern [.bool] α
-- | lean_array_get_borrowed           | opaque      | Array.get!InternalBorrowed  | {α : Type u} → [@& Inhabited α] → (@& Array α) → (@& Nat) → α              |
  | lean_array_get_borrowed         : (α : Ty) → LeanPureExtern [.array α, .nat] α
-- | lean_array_push                   | def         | Array.push                  | {α : Type u} → Array α → α → Array α                                       |
  | lean_array_push                 : (α : Ty) → LeanPureExtern [.array α, α] (.array α)
-- | lean_array_get_size               | def         | Array.size                  | {α : Type u} → (@& Array α) → Nat                                          |
  | lean_array_get_size             : (α : Ty) → LeanPureExtern [.array α] .nat
-- | lean_array_to_list                | def         | Array.toList                | {α : Type u} → Array α → List α                                            |
  | lean_array_to_list              : (α : Ty) → LeanPureExtern [.array α] (.list α)
-- | lean_array_fget_borrowed          | opaque      | Array.getInternalBorrowed   | {α : Type u} → (a : @& Array α) → (i : @& Nat) → instLTNat.lt i a.size → α |
  | lean_array_fget_borrowed        : (α : Ty) → LeanPureExtern [.array α, .nat] α
-- | lean_mk_empty_array_with_capacity | def         | Array.emptyWithCapacity     | {α : Type u} → (@& Nat) → Array α                                          |
  | lean_empty_array_with_capacity  : (α : Ty) → LeanPureExtern [.nat] (.array α)
-- |                                   |             | Array.mkEmpty               |                                                                            |
  | lean_array_mk_empty             : (α : Ty) → LeanPureExtern [.nat] (.array α)
-- | lean_is_scalar                    | axiom       | isScalarObj                 | {α : Type u} → α → Bool                                                    |
  | lean_is_scalar                  : (α : Ty) → LeanPureExtern [α] .bool
-- | lean_array_get                    | def         | Array.get!Internal          | {α : Type u} → [@& Inhabited α] → (@& Array α) → (@& Nat) → α              |
  | lean_array_get                  : (α : Ty) → LeanPureExtern [.array α, .nat] α
-- | lean_panic_fn_borrowed            | def         | panicCore                   | {α : Sort u} → [@& Inhabited α] → String → α                               |
  | lean_panic_fn_borrowed          : (α : Ty) → LeanPureExtern [.string] α
-- | lean_array_fget                   | def         | Array.getInternal           | {α : Type u} → (a : @& Array α) → (i : @& Nat) → instLTNat.lt i a.size → α |
  | lean_array_fget                 : (α : Ty) → LeanPureExtern [.array α, .nat] α
-- | lean_array_mk                     | constructor | Array.mk                    | {α : Type u} → List α → Array α                                            |
  | lean_array_mk                   : (α : Ty) → LeanPureExtern [.list α] (.array α)
-- | lean_task_map      | def         | Task.map          | {α : Type u_1} → {β : Type u_2} → (α → β) → Task α → optParam Task.Priority Task.Priority.default → optParam Bool Bool.false → Task β      |
  | lean_task_map                    : (α : Ty) → (β : Ty) → LeanPureExtern [(α ⇒ β), .task α, .nat, .bool] (.task β)
-- | lean_task_spawn    | def         | Task.spawn        | {α : Type u} → (Unit → α) → optParam Task.Priority Task.Priority.default → Task α                                                          |
  | lean_task_spawn                  : (α : Ty) → LeanPureExtern [.nullary α, .nat] (.task α)
-- | lean_thunk_pure    | def         | Thunk.pure        | {α : Type u_1} → α → Thunk α                                                                                                             |
  | lean_thunk_pure                  : (α : Ty) → LeanPureExtern [α] (.thunk α)
-- | lean_mk_thunk      | constructor | Thunk.mk          | {α : Type u} → (Unit → α) → Thunk α                                                                                                        |
  | lean_mk_thunk                    : (α : Ty) → LeanPureExtern [.nullary α] (.thunk α)
-- | lean_task_get_own  | def         | Task.get          | {α : Type u} → Task α → α                                                                                                                |
  | lean_task_get_own                : (α : Ty) → LeanPureExtern [.task α] α
-- | lean_task_pure     | constructor | Task.pure         | {α : Type u} → α → Task α                                                                                                                |
  | lean_task_pure                   : (α : Ty) → LeanPureExtern [α] (.task α)
-- | lean_thunk_get_own | def         | Thunk.get         | {α : Type u_1} → (@& Thunk α) → α                                                                                                        |
  | lean_thunk_get_own               : (α : Ty) → LeanPureExtern [.thunk α] α
-- | lean_task_bind     | def         | Task.bind         | {α : Type u_1} → {β : Type u_2} → Task α → (α → Task β) → optParam Task.Priority Task.Priority.default → optParam Bool Bool.false → Task β |
  | lean_task_bind                   : (α : Ty) → (β : Ty) → LeanPureExtern [.task α, (α ⇒ .task β), .nat, .bool] (.task β)
-- | lean_dbg_sleep           | def    | dbgSleep          | {α : Type u} → UInt32 → (Unit → α) → α |
  | lean_dbg_sleep                    : (α : Ty) → LeanPureExtern [.uint32, .nullary α] α
-- | lean_ptr_addr            | opaque | ptrAddrUnsafe     | {α : Type u} → (@& α) → USize        |
  | lean_ptr_addr                     : (α : Ty) → LeanPureExtern [α] .usize
-- | lean_dbg_trace           | def    | dbgTrace          | {α : Type u} → String → (Unit → α) → α |
  | lean_dbg_trace                    : (α : Ty) → LeanPureExtern [.string, .nullary α] α
-- | lean_dbg_trace_if_shared | def    | dbgTraceIfShared  | {α : Type u} → (@& String) → α → α   |
  | lean_dbg_trace_if_shared          : (α : Ty) → LeanPureExtern [.string, α] α
-- | lean_dbg_stack_trace     | def    | dbgStackTrace     | {α : Type u} → (Unit → α) → α          |
  | lean_dbg_stack_trace              : (α : Ty) → LeanPureExtern [.nullary α] α
-- | lean_is_exclusive_obj    | opaque | isExclusiveUnsafe | {α : Type u} → (@& α) → Bool         |
  | lean_is_exclusive_obj             : (α : Ty) → LeanPureExtern [α] .bool
-- | lean_array_set  | def | Array.set!        | {α : Type u_1} → Array α → (@& Nat) → α → Array α                                                                   |
  | lean_array_set                    : (α : Ty) → LeanPureExtern [.array α, .nat, α] (.array α)
-- | lean_array_fset | def | Array.set         | {α : Type u_1} → (xs : Array α) → (i : @& Nat) → α → autoParam (instLTNat.lt i xs.size) Array.set._auto_1 → Array α |
  | lean_array_fset                   : (α : Ty) → LeanPureExtern [.array α, .nat, α] (.array α)
-- | lean_array_fswap         | def    | Array.swap           | {α : Type u} → (xs : Array α) → (i : @& Nat) → (j : @& Nat) → autoParam (instLTNat.lt i xs.size) Array.swap._auto_1 → autoParam (instLTNat.lt j xs.size) Array.swap._auto_3 → Array α |
  | lean_array_fswap                  : (α : Ty) → LeanPureExtern [.array α, .nat, .nat] (.array α)
-- | lean_array_uget          | def    | Array.uget           | {α : Type u} → (xs : @& Array α) → (i : USize) → instLTNat.lt i.toNat xs.size → α                                                                                                     |
  | lean_array_uget                   : (α : Ty) → LeanPureExtern [.array α, .usize] α
-- | lean_mk_array            | def    | Array.replicate      | {α : Type u} → Nat → α → Array α                                                                                                                                                      |
  | lean_mk_array                     : (α : Ty) → LeanPureExtern [.nat, α] (.array α)
-- | lean_array_swap          | def    | Array.swapIfInBounds | {α : Type u} → Array α → (@& Nat) → (@& Nat) → Array α                                                                                                                                |
  | lean_array_swap                   : (α : Ty) → LeanPureExtern [.array α, .nat, .nat] (.array α)
-- | lean_array_uget_borrowed | opaque | Array.ugetBorrowed   | {α : Type u} → (xs : @& Array α) → (i : USize) → instLTNat.lt i.toNat xs.size → α                                                                                                     |
  | lean_array_uget_borrowed          : (α : Ty) → LeanPureExtern [.array α, .usize] α
-- | lean_array_pop           | def    | Array.pop            | {α : Type u} → Array α → Array α                                                                                                                                                      |
  | lean_array_pop                    : (α : Ty) → LeanPureExtern [.array α] (.array α)
-- | lean_array_uset          | def    | Array.uset           | {α : Type u} → (xs : Array α) → (i : USize) → α → instLTNat.lt i.toNat xs.size → Array α                                                                                              |
  | lean_array_uset                   : (α : Ty) → LeanPureExtern [.array α, .usize, α] (.array α)
-- | lean_array_size          | def    | Array.usize          | {α : Type u} → (@& Array α) → USize                                                                                                                                                   |
  | lean_array_size                   : (α : Ty) → LeanPureExtern [.array α] .usize
-- | lean_io_promise_result_opt | opaque | IO.Promise.result?                                   | {α : Type} → (@& IO.Promise α) → Task (Option α) |
  | lean_io_promise_result_opt      : (α : Ty) → LeanPureExtern [.promise α] (.task (.option α))
-- | lean_option_get_or_block   | opaque | _private.Init.System.Promise.0.IO.Option.getOrBlock! | {α : Type u_1} → [Nonempty α] → Option α → α     |
  | lean_option_get_or_block        : (α : Ty) → LeanPureExtern [.option α] α
-- | lean_sharecommon_quick | def    | ShareCommon.shareCommon'      | {α : Sort u_1} → (@& α) → α                                                                                 |
  | lean_sharecommon_quick          : (α : Ty) → LeanPureExtern [α] α
-- | lean_state_sharecommon | def    | ShareCommon.State.shareCommon | {α : Type u_1} → {σ : @& ShareCommon.StateFactory} → ShareCommon.State σ → α → Prod α (ShareCommon.State σ) |
  | lean_state_sharecommon          : (α : Ty) → LeanPureExtern [.shareCommonState, α] (.prod α .shareCommonState)
-- ## The monomorphic externs
-- # Init/Prelude.lean
--
-- | name of extern                    | def         | full name of func           | type of func                                                               |
-- | --------------------------------- | ----------- | --------------------------- | -------------------------------------------------------------------------- |
-- | lean_uint32_of_nat_mk             | constructor | UInt32.ofBitVec             | BitVec 32 → UInt32                                                         |
  | lean_uint32_of_nat_mk           : LeanPureExtern [.bitvec 32] .uint32
-- | lean_uint32_dec_eq                | def         | UInt32.decEq                | (a : UInt32) → (b : UInt32) → Decidable (Eq a b)                           |
  | lean_uint32_dec_eq              : LeanPureExtern [.uint32, .uint32] .bool
-- | lean_byte_array_size              | def         | ByteArray.size              | (@& ByteArray) → Nat                                                       |
  | lean_byte_array_size            : LeanPureExtern [.byteArray] .nat
-- | lean_string_to_utf8               | def         | String.toByteArray          | String → ByteArray                                                         |
  | lean_string_to_utf8             : LeanPureExtern [.string] .byteArray
-- | lean_uint32_dec_lt                | def         | UInt32.decLt                | (a : UInt32) → (b : UInt32) → Decidable (instLTUInt32.lt a b)              |
  | lean_uint32_dec_lt              : LeanPureExtern [.uint32, .uint32] .bool
-- | lean_nat_div                      | def         | Nat.div                     | (@& Nat) → (@& Nat) → Nat                                                  |
  | lean_nat_div                    : LeanPureExtern [.nat, .nat] .nat
-- | lean_uint32_of_nat                | def         | UInt32.ofNatLT              | (n : @& Nat) → instLTNat.lt n UInt32.size → UInt32                         |
  | lean_uint32_of_nat_lt           : LeanPureExtern [.nat] .uint32
-- |                                   |             | Char.ofNatAux               | (n : @& Nat) → n.isValidChar → Char                                        |
  | lean_char_of_nat_aux            : LeanPureExtern [.nat] .char
-- | lean_uint8_to_nat                 | def         | UInt8.toBitVec              | UInt8 → BitVec 8                                                           |
  | lean_uint8_to_bitvec            : LeanPureExtern [.uint8] (.bitvec 8)
-- | lean_nat_dec_lt                   | def         | Nat.decLt                   | (n : @& Nat) → (m : @& Nat) → Decidable (instLTNat.lt n m)                 |
  | lean_nat_dec_lt                 : LeanPureExtern [.nat, .nat] .bool
-- | lean_string_from_utf8_unchecked   | constructor | String.ofByteArray          | (toByteArray : ByteArray) → toByteArray.IsValidUTF8 → String               |
  | lean_string_from_utf8_unchecked : LeanPureExtern [.byteArray] .string
-- | lean_nat_mod                      | def         | Nat.modCore                 | Nat → Nat → Nat                                                            |
  | lean_nat_mod_core               : LeanPureExtern [.nat, .nat] .nat
-- |                                   |             | Nat.mod                     | (@& Nat) → (@& Nat) → Nat                                                  |
  | lean_nat_mod                    : LeanPureExtern [.nat, .nat] .nat
-- | lean_byte_array_mk                | constructor | ByteArray.mk                | Array UInt8 → ByteArray                                                    |
  | lean_byte_array_mk              : LeanPureExtern [.array .uint8] .byteArray
-- | lean_nat_sub                      | def         | Nat.sub                     | (@& Nat) → (@& Nat) → Nat                                                  |
  | lean_nat_sub                    : LeanPureExtern [.nat, .nat] .nat
-- | lean_uint8_dec_lt                 | def         | UInt8.decLt                 | (a : UInt8) → (b : UInt8) → Decidable (instLTUInt8.lt a b)                 |
  | lean_uint8_dec_lt               : LeanPureExtern [.uint8, .uint8] .bool
-- | lean_byte_array_data              | def         | ByteArray.data              | ByteArray → Array UInt8                                                    |
  | lean_byte_array_data            : LeanPureExtern [.byteArray] (.array .uint8)
-- | lean_system_platform_nbits        | opaque      | System.Platform.getNumBits  | Unit → Subtype fun n => Or (Eq n 32) (Eq n 64)                             |
  | lean_system_platform_nbits      : LeanPureExtern [] .nat
-- | lean_uint32_dec_le                | def         | UInt32.decLe                | (a : UInt32) → (b : UInt32) → Decidable (instLEUInt32.le a b)              |
  | lean_uint32_dec_le              : LeanPureExtern [.uint32, .uint32] .bool
-- | lean_nat_dec_eq                   | def         | Nat.decEq                   | (n : @& Nat) → (m : @& Nat) → Decidable (Eq n m)                           |
  | lean_nat_dec_eq                 : LeanPureExtern [.nat, .nat] .bool
-- |                                   |             | Nat.beq                     | (@& Nat) → (@& Nat) → Bool                                                 |
  | lean_nat_beq                    : LeanPureExtern [.nat, .nat] .bool
-- | lean_uint8_of_nat                 | def         | UInt8.ofNat                 | (@& Nat) → UInt8                                                           |
  | lean_uint8_of_nat               : LeanPureExtern [.nat] .uint8
-- |                                   |             | UInt8.ofNatLT               | (n : @& Nat) → instLTNat.lt n UInt8.size → UInt8                           |
  | lean_uint8_of_nat_lt            : LeanPureExtern [.nat] .uint8
-- | lean_uint8_dec_le                 | def         | UInt8.decLe                 | (a : UInt8) → (b : UInt8) → Decidable (instLEUInt8.le a b)                 |
  | lean_uint8_dec_le               : LeanPureExtern [.uint8, .uint8] .bool
-- | lean_nat_dec_le                   | def         | Nat.ble                     | (@& Nat) → (@& Nat) → Bool                                                 |
  | lean_nat_ble                    : LeanPureExtern [.nat, .nat] .bool
-- |                                   |             | Nat.decLe                   | (n : @& Nat) → (m : @& Nat) → Decidable (instLENat.le n m)                 |
  | lean_nat_dec_le                 : LeanPureExtern [.nat, .nat] .bool
-- | lean_nat_add                      | def         | Nat.add                     | (@& Nat) → (@& Nat) → Nat                                                  |
  | lean_nat_add                    : LeanPureExtern [.nat, .nat] .nat
-- | lean_uint16_to_nat                | def         | UInt16.toBitVec             | UInt16 → BitVec 16                                                         |
  | lean_uint16_to_bitvec           : LeanPureExtern [.uint16] (.bitvec 16)
-- | lean_uint16_of_nat_mk             | constructor | UInt16.ofBitVec             | BitVec 16 → UInt16                                                         |
  | lean_uint16_of_nat_mk           : LeanPureExtern [.bitvec 16] .uint16
-- | lean_uint16_dec_eq                | def         | UInt16.decEq                | (a : UInt16) → (b : UInt16) → Decidable (Eq a b)                           |
  | lean_uint16_dec_eq              : LeanPureExtern [.uint16, .uint16] .bool
-- | lean_string_dec_eq                | def         | String.decEq                | (s₁ : @& String) → (s₂ : @& String) → Decidable (Eq s₁ s₂)                 |
  | lean_string_dec_eq              : LeanPureExtern [.string, .string] .bool
-- | lean_nat_pred                     | def         | Nat.pred                    | (@& Nat) → Nat                                                             |
  | lean_nat_pred                   : LeanPureExtern [.nat] .nat
-- | lean_usize_of_nat                 | def         | USize.ofNatLT               | (n : @& Nat) → instLTNat.lt n USize.size → USize                           |
  | lean_usize_of_nat_lt            : LeanPureExtern [.nat] .usize
-- | lean_string_mk                    | def         | String.ofList               | List Char → String                                                         |
  | lean_string_mk                  : LeanPureExtern [.list .char] .string
-- | lean_string_hash                  | opaque      | String.hash                 | (@& String) → UInt64                                                       |
  | lean_string_hash                : LeanPureExtern [.string] .uint64
-- | lean_uint64_to_nat                | def         | UInt64.toBitVec             | UInt64 → BitVec 64                                                         |
  | lean_uint64_to_bitvec           : LeanPureExtern [.uint64] (.bitvec 64)
-- | lean_uint64_of_nat_mk             | constructor | UInt64.ofBitVec             | BitVec 64 → UInt64                                                         |
  | lean_uint64_of_nat_mk           : LeanPureExtern [.bitvec 64] .uint64
-- | lean_uint32_to_nat                | def         | UInt32.toNat                | UInt32 → Nat                                                               |
  | lean_uint32_to_nat              : LeanPureExtern [.uint32] .nat
-- |                                   |             | UInt32.toBitVec             | UInt32 → BitVec 32                                                         |
  | lean_uint32_to_bitvec           : LeanPureExtern [.uint32] (.bitvec 32)
-- | lean_uint64_dec_eq                | def         | UInt64.decEq                | (a : UInt64) → (b : UInt64) → Decidable (Eq a b)                           |
  | lean_uint64_dec_eq              : LeanPureExtern [.uint64, .uint64] .bool
-- | lean_uint16_of_nat                | def         | UInt16.ofNatLT              | (n : @& Nat) → instLTNat.lt n UInt16.size → UInt16                         |
  | lean_uint16_of_nat_lt           : LeanPureExtern [.nat] .uint16
-- | lean_name_eq                      | def         | Lean.Name.beq               | (@& Lean.Name) → (@& Lean.Name) → Bool                                     |
  | lean_name_eq                    : LeanPureExtern [.name, .name] .bool
-- | lean_uint8_of_nat_mk              | constructor | UInt8.ofBitVec              | BitVec 8 → UInt8                                                           |
  | lean_uint8_of_nat_mk            : LeanPureExtern [.bitvec 8] .uint8
-- | lean_mk_empty_byte_array          | def         | ByteArray.emptyWithCapacity | (@& Nat) → ByteArray                                                       |
  | lean_mk_empty_byte_array        : LeanPureExtern [.nat] .byteArray
-- | lean_uint8_dec_eq                 | def         | UInt8.decEq                 | (a : UInt8) → (b : UInt8) → Decidable (Eq a b)                             |
  | lean_uint8_dec_eq               : LeanPureExtern [.uint8, .uint8] .bool
-- | lean_nat_pow                      | def         | Nat.pow                     | (@& Nat) → (@& Nat) → Nat                                                  |
  | lean_nat_pow                    : LeanPureExtern [.nat, .nat] .nat
-- | lean_usize_dec_eq                 | def         | USize.decEq                 | (a : USize) → (b : USize) → Decidable (Eq a b)                             |
  | lean_usize_dec_eq               : LeanPureExtern [.usize, .usize] .bool
-- | lean_usize_of_nat_mk              | constructor | USize.ofBitVec              | BitVec System.Platform.numBits → USize                                     |
  | lean_usize_of_nat_mk            : LeanPureExtern [.bitvec 64] .usize
-- | lean_nat_mul                      | def         | Nat.mul                     | (@& Nat) → (@& Nat) → Nat                                                  |
  | lean_nat_mul                    : LeanPureExtern [.nat, .nat] .nat
-- | lean_usize_to_nat                 | def         | USize.toBitVec              | USize → BitVec System.Platform.numBits                                     |
  | lean_usize_to_bitvec            : LeanPureExtern [.usize] (.bitvec 64)
-- | lean_string_utf8_byte_size        | def         | String.utf8ByteSize         | (@& String) → Nat                                                          |
  | lean_string_utf8_byte_size      : LeanPureExtern [.string] .nat
-- | lean_byte_array_push              | def         | ByteArray.push              | ByteArray → UInt8 → ByteArray                                              |
  | lean_byte_array_push            : LeanPureExtern [.byteArray, .uint8] .byteArray
-- | lean_uint64_mix_hash              | opaque      | mixHash                     | UInt64 → UInt64 → UInt64                                                   |
  | lean_uint64_mix_hash            : LeanPureExtern [.uint64, .uint64] .uint64
-- | lean_uint64_of_nat                | def         | UInt64.ofNatLT              | (n : @& Nat) → instLTNat.lt n UInt64.size → UInt64                         |
  | lean_uint64_of_nat_lt           : LeanPureExtern [.nat] .uint64
--
-- # Init/Data/Int/Basic.lean
--
-- | name of extern           | def         | full name of func | type of func                                                   |
-- | ------------------------ | ----------- | ----------------- | -------------------------------------------------------------- |
-- | lean_nat_to_int          | constructor | Int.ofNat         | Nat → Int                                                      |
  | lean_nat_to_int          : LeanPureExtern [.nat] .int64
-- | lean_int_dec_le          | def         | Int.decLe         | (a : @& Int) → (b : @& Int) → Decidable (Int.instLEInt.le a b) |
  | lean_int_dec_le          : LeanPureExtern [.int64, .int64] .bool
-- | lean_int_dec_lt          | def         | Int.decLt         | (a : @& Int) → (b : @& Int) → Decidable (Int.instLTInt.lt a b) |
  | lean_int_dec_lt          : LeanPureExtern [.int64, .int64] .bool
-- | lean_int_dec_eq          | def         | Int.decEq         | (a : @& Int) → (b : @& Int) → Decidable (Eq a b)               |
  | lean_int_dec_eq          : LeanPureExtern [.int64, .int64] .bool
-- | lean_int_mul             | def         | Int.mul           | (@& Int) → (@& Int) → Int                                      |
  | lean_int_mul             : LeanPureExtern [.int64, .int64] .int64
-- | lean_int_dec_nonneg      | def         | Int.decNonneg     | (m : @& Int) → Decidable m.NonNeg                              |
  | lean_int_dec_nonneg      : LeanPureExtern [.int64] .bool
-- | lean_int_neg_succ_of_nat | constructor | Int.negSucc       | Nat → Int                                                      |
  | lean_int_neg_succ_of_nat : LeanPureExtern [.nat] .int64
-- | lean_int_add             | def         | Int.add           | (@& Int) → (@& Int) → Int                                      |
  | lean_int_add             : LeanPureExtern [.int64, .int64] .int64
-- | lean_int_neg             | def         | Int.neg           | (@& Int) → Int                                                 |
  | lean_int_neg             : LeanPureExtern [.int64] .int64
-- | lean_int_sub             | def         | Int.sub           | (@& Int) → (@& Int) → Int                                      |
  | lean_int_sub             : LeanPureExtern [.int64, .int64] .int64
-- | lean_nat_abs             | def         | Int.natAbs        | (@& Int) → Nat                                                 |
  | lean_nat_abs             : LeanPureExtern [.int64] .nat
--
-- # Init/Data/Nat/Div/Basic.lean
--
-- | name of extern     | def | full name of func | type of func                                            |
-- | ------------------ | --- | ----------------- | ------------------------------------------------------- |
-- | lean_nat_div_exact | def | Nat.divExact      | (x : @& Nat) → (y : @& Nat) → Nat.instDvd.dvd y x → Nat |
  | lean_nat_div_exact : LeanPureExtern [.nat, .nat] .nat
--
-- # Init/Data/Nat/Bitwise/Basic.lean
--
-- | name of extern  | def | full name of func | type of func              |
-- | --------------- | --- | ----------------- | ------------------------- |
-- | lean_nat_lxor   | def | Nat.xor           | (@& Nat) → (@& Nat) → Nat |
  | lean_nat_lxor   : LeanPureExtern [.nat, .nat] .nat
-- | lean_nat_shiftl | def | Nat.shiftLeft     | (@& Nat) → (@& Nat) → Nat |
  | lean_nat_shiftl : LeanPureExtern [.nat, .nat] .nat
-- | lean_nat_shiftr | def | Nat.shiftRight    | (@& Nat) → (@& Nat) → Nat |
  | lean_nat_shiftr : LeanPureExtern [.nat, .nat] .nat
-- | lean_nat_land   | def | Nat.land          | (@& Nat) → (@& Nat) → Nat |
  | lean_nat_land   : LeanPureExtern [.nat, .nat] .nat
-- | lean_nat_lor    | def | Nat.lor           | (@& Nat) → (@& Nat) → Nat |
  | lean_nat_lor    : LeanPureExtern [.nat, .nat] .nat
--
-- # Init/Data/UInt/BasicAux.lean
--
-- | name of extern        | def | full name of func | type of func                                               |
-- | --------------------- | --- | ----------------- | ---------------------------------------------------------- |
-- | lean_uint64_to_nat    | def | UInt64.toNat      | UInt64 → Nat                                               |
  | lean_uint64_to_nat    : LeanPureExtern [.uint64] .nat
-- | lean_uint32_to_uint8  | def | UInt32.toUInt8    | UInt32 → UInt8                                             |
  | lean_uint32_to_uint8  : LeanPureExtern [.uint32] .uint8
-- | lean_usize_to_nat     | def | USize.toNat       | USize → Nat                                                |
  | lean_usize_to_nat     : LeanPureExtern [.usize] .nat
-- | lean_uint64_to_uint32 | def | UInt64.toUInt32   | UInt64 → UInt32                                            |
  | lean_uint64_to_uint32 : LeanPureExtern [.uint64] .uint32
-- | lean_uint32_to_uint16 | def | UInt32.toUInt16   | UInt32 → UInt16                                            |
  | lean_uint32_to_uint16 : LeanPureExtern [.uint32] .uint16
-- | lean_uint16_to_uint32 | def | UInt16.toUInt32   | UInt16 → UInt32                                            |
  | lean_uint16_to_uint32 : LeanPureExtern [.uint16] .uint32
-- | lean_uint32_to_uint64 | def | UInt32.toUInt64   | UInt32 → UInt64                                            |
  | lean_uint32_to_uint64 : LeanPureExtern [.uint32] .uint64
-- | lean_uint32_of_nat    | def | UInt32.ofNat      | (@& Nat) → UInt32                                          |
  | lean_uint32_of_nat    : LeanPureExtern [.nat] .uint32
-- | lean_usize_add        | def | USize.add         | USize → USize → USize                                      |
  | lean_usize_add        : LeanPureExtern [.usize, .usize] .usize
-- | lean_uint32_sub       | def | UInt32.sub        | UInt32 → UInt32 → UInt32                                   |
  | lean_uint32_sub       : LeanPureExtern [.uint32, .uint32] .uint32
-- | lean_uint16_to_nat    | def | UInt16.toNat      | UInt16 → Nat                                               |
  | lean_uint16_to_nat    : LeanPureExtern [.uint16] .nat
-- | lean_uint16_to_uint8  | def | UInt16.toUInt8    | UInt16 → UInt8                                             |
  | lean_uint16_to_uint8  : LeanPureExtern [.uint16] .uint8
-- | lean_usize_sub        | def | USize.sub         | USize → USize → USize                                      |
  | lean_usize_sub        : LeanPureExtern [.usize, .usize] .usize
-- | lean_uint32_add       | def | UInt32.add        | UInt32 → UInt32 → UInt32                                   |
  | lean_uint32_add       : LeanPureExtern [.uint32, .uint32] .uint32
-- | lean_usize_of_nat     | def | USize.ofNat       | (@& Nat) → USize                                           |
  | lean_usize_of_nat     : LeanPureExtern [.nat] .usize
-- | lean_usize_dec_le     | def | USize.decLe       | (a : USize) → (b : USize) → Decidable (instLEUSize.le a b) |
  | lean_usize_dec_le     : LeanPureExtern [.usize, .usize] .bool
-- | lean_uint8_to_uint64  | def | UInt8.toUInt64    | UInt8 → UInt64                                             |
  | lean_uint8_to_uint64  : LeanPureExtern [.uint8] .uint64
-- | lean_uint8_to_nat     | def | UInt8.toNat       | UInt8 → Nat                                                |
  | lean_uint8_to_nat     : LeanPureExtern [.uint8] .nat
-- | lean_uint64_of_nat    | def | UInt64.ofNat      | (@& Nat) → UInt64                                          |
  | lean_uint64_of_nat    : LeanPureExtern [.nat] .uint64
-- | lean_uint8_to_uint32  | def | UInt8.toUInt32    | UInt8 → UInt32                                             |
  | lean_uint8_to_uint32  : LeanPureExtern [.uint8] .uint32
-- | lean_uint16_of_nat    | def | UInt16.ofNat      | (@& Nat) → UInt16                                          |
  | lean_uint16_of_nat    : LeanPureExtern [.nat] .uint16
-- | lean_uint16_to_uint64 | def | UInt16.toUInt64   | UInt16 → UInt64                                            |
  | lean_uint16_to_uint64 : LeanPureExtern [.uint16] .uint64
-- | lean_usize_dec_lt     | def | USize.decLt       | (a : USize) → (b : USize) → Decidable (instLTUSize.lt a b) |
  | lean_usize_dec_lt     : LeanPureExtern [.usize, .usize] .bool
-- | lean_uint64_to_uint8  | def | UInt64.toUInt8    | UInt64 → UInt8                                             |
  | lean_uint64_to_uint8  : LeanPureExtern [.uint64] .uint8
-- | lean_uint64_to_uint16 | def | UInt64.toUInt16   | UInt64 → UInt16                                            |
  | lean_uint64_to_uint16 : LeanPureExtern [.uint64] .uint16
-- | lean_uint8_to_uint16  | def | UInt8.toUInt16    | UInt8 → UInt16                                             |
  | lean_uint8_to_uint16  : LeanPureExtern [.uint8] .uint16
--
-- # Init/Data/String/Bootstrap.lean
--
-- | name of extern             | def    | full name of func                | type of func                                                                |
-- | -------------------------- | ------ | -------------------------------- | --------------------------------------------------------------------------- |
-- | lean_string_utf8_get       | opaque | String.Internal.get              | (@& String) → (@& String.Pos.Raw) → Char                                    |
  | lean_string_utf8_get       : LeanPureExtern [.string, .stringPos] .char
-- | lean_string_trim           | opaque | String.Internal.trim             | String → String                                                             |
  | lean_string_trim           : LeanPureExtern [.string] .string
-- | lean_substring_drop        | opaque | Substring.Raw.Internal.drop      | Substring.Raw → Nat → Substring.Raw                                         |
  | lean_substring_drop        : LeanPureExtern [.substring, .nat] .substring
-- | lean_substring_prev        | opaque | Substring.Raw.Internal.prev      | Substring.Raw → String.Pos.Raw → String.Pos.Raw                             |
  | lean_substring_prev        : LeanPureExtern [.substring, .stringPos] .stringPos
-- | lean_substring_extract     | opaque | Substring.Raw.Internal.extract   | Substring.Raw → String.Pos.Raw → String.Pos.Raw → Substring.Raw             |
  | lean_substring_extract     : LeanPureExtern [.substring, .stringPos, .stringPos] .substring
-- | lean_string_foldl          | opaque | String.Internal.foldl            | (String → Char → String) → String → String → String                           |
  | lean_string_foldl          : LeanPureExtern [(.fn [.string, .char] .string), .string, .string] .string
-- | lean_substring_tostring    | opaque | Substring.Raw.Internal.toString  | Substring.Raw → String                                                      |
  | lean_substring_tostring    : LeanPureExtern [.substring] .string
-- | lean_string_append         | opaque | String.Internal.append           | String → (@& String) → String                                               |
  | lean_string_append         : LeanPureExtern [.string, .string] .string
-- | lean_string_get_byte_fast  | opaque | String.Internal.getUTF8Byte      | (s : @& String) → (n : Nat) → instLTNat.lt n s.utf8ByteSize → UInt8         |
  | lean_string_get_byte_fast  : LeanPureExtern [.string, .nat] .uint8
-- | lean_string_isempty        | opaque | String.Internal.isEmpty          | String → Bool                                                               |
  | lean_string_isempty        : LeanPureExtern [.string] .bool
-- | lean_string_push           | def    | String.push                      | String → Char → String                                                      |
  | lean_string_push           : LeanPureExtern [.string, .char] .string
-- | lean_string_isprefixof     | opaque | String.Internal.isPrefixOf       | String → String → Bool                                                        |
  | lean_string_isprefixof     : LeanPureExtern [.string, .string] .bool
-- | lean_string_dropright      | opaque | String.Internal.dropRight        | String → Nat → String                                                       |
  | lean_string_dropright      : LeanPureExtern [.string, .nat] .string
-- | lean_substring_takewhile   | opaque | Substring.Raw.Internal.takeWhile | Substring.Raw → (Char → Bool) → Substring.Raw                                 |
  | lean_substring_takewhile   : LeanPureExtern [.substring, (.char ⇒ .bool)] .substring
-- | lean_substring_get         | opaque | Substring.Raw.Internal.get       | Substring.Raw → String.Pos.Raw → Char                                       |
  | lean_substring_get         : LeanPureExtern [.substring, .stringPos] .char
-- | lean_string_uget_byte_fast | opaque | String.Internal.ugetUTF8Byte     | (s : @& String) → (n : USize) → instLTNat.lt n.toNat s.utf8ByteSize → UInt8 |
  | lean_string_uget_byte_fast : LeanPureExtern [.string, .usize] .uint8
-- | lean_string_contains       | opaque | String.Internal.contains         | String → Char → Bool                                                        |
  | lean_string_contains       : LeanPureExtern [.string, .char] .bool
-- | lean_string_front          | opaque | String.Internal.front            | String → Char                                                               |
  | lean_string_front          : LeanPureExtern [.string] .char
-- | lean_string_posof          | opaque | String.Internal.posOf            | String → Char → String.Pos.Raw                                              |
  | lean_string_posof          : LeanPureExtern [.string, .char] .stringPos
-- | lean_substring_all         | opaque | Substring.Raw.Internal.all       | Substring.Raw → (Char → Bool) → Bool                                          |
  | lean_substring_all         : LeanPureExtern [.substring, (.char ⇒ .bool)] .bool
-- | lean_string_intercalate    | opaque | String.Internal.intercalate      | String → List String → String                                               |
  | lean_string_intercalate    : LeanPureExtern [.string, .list .string] .string
-- | lean_string_drop           | opaque | String.Internal.drop             | String → Nat → String                                                       |
  | lean_string_drop           : LeanPureExtern [.string, .nat] .string
-- | lean_string_length         | opaque | String.Internal.length           | (@& String) → Nat                                                           |
  | lean_string_length         : LeanPureExtern [.string] .nat
-- | lean_string_utf8_at_end    | opaque | String.Internal.atEnd            | (@& String) → (@& String.Pos.Raw) → Bool                                    |
  | lean_string_utf8_at_end    : LeanPureExtern [.string, .stringPos] .bool
-- | lean_substring_beq         | opaque | Substring.Raw.Internal.beq       | Substring.Raw → Substring.Raw → Bool                                        |
  | lean_substring_beq         : LeanPureExtern [.substring, .substring] .bool
-- | lean_string_nextwhile      | opaque | String.Internal.nextWhile        | String → (Char → Bool) → String.Pos.Raw → String.Pos.Raw                      |
  | lean_string_nextwhile      : LeanPureExtern [.string, (.char ⇒ .bool), .stringPos] .stringPos
-- | lean_string_utf8_next      | opaque | String.Internal.next             | (@& String) → (@& String.Pos.Raw) → String.Pos.Raw                          |
  | lean_string_utf8_next      : LeanPureExtern [.string, .stringPos] .stringPos
-- | lean_string_mk             | def    | String.mk                        | List Char → String                                                          |
  | lean_string_mk_def         : LeanPureExtern [.list .char] .string
-- | lean_string_any            | opaque | String.Internal.any              | String → (Char → Bool) → Bool                                                 |
  | lean_string_any            : LeanPureExtern [.string, (.char ⇒ .bool)] .bool
-- | lean_string_pushn          | opaque | String.Internal.pushn            | String → Char → Nat → String                                                |
  | lean_string_pushn          : LeanPureExtern [.string, .char, .nat] .string
-- | lean_string_capitalize     | opaque | String.Internal.capitalize       | String → String                                                             |
  | lean_string_capitalize     : LeanPureExtern [.string] .string
-- | lean_string_utf8_extract   | opaque | String.Internal.extract          | (@& String) → (@& String.Pos.Raw) → (@& String.Pos.Raw) → String            |
  | lean_string_utf8_extract   : LeanPureExtern [.string, .stringPos, .stringPos] .string
-- | lean_string_pos_min        | opaque | String.Pos.Raw.Internal.min      | String.Pos.Raw → String.Pos.Raw → String.Pos.Raw                            |
  | lean_string_pos_min        : LeanPureExtern [.stringPos, .stringPos] .stringPos
-- | lean_substring_front       | opaque | Substring.Raw.Internal.front     | Substring.Raw → Char                                                        |
  | lean_substring_front       : LeanPureExtern [.substring] .char
-- | lean_string_pos_sub        | opaque | String.Pos.Raw.Internal.sub      | String.Pos.Raw → String.Pos.Raw → String.Pos.Raw                            |
  | lean_string_pos_sub        : LeanPureExtern [.stringPos, .stringPos] .stringPos
-- | lean_substring_isempty     | opaque | Substring.Raw.Internal.isEmpty   | Substring.Raw → Bool                                                        |
  | lean_substring_isempty     : LeanPureExtern [.substring] .bool
-- | lean_string_offsetofpos    | opaque | String.Internal.offsetOfPos      | String → String.Pos.Raw → Nat                                               |
  | lean_string_offsetofpos    : LeanPureExtern [.string, .stringPos] .nat
--
-- # Init/Core.lean
--
-- | name of extern     | def         | full name of func | type of func                                                                                                                             |
-- | ------------------ | ----------- | ----------------- | ---------------------------------------------------------------------------------------------------------------------------------------- |
-- | lean_strict_or     | def         | strictOr          | Bool → Bool → Bool                                                                                                                       |
  | lean_strict_or                   : LeanPureExtern [.bool, .bool] .bool
-- | lean_strict_and    | def         | strictAnd         | Bool → Bool → Bool                                                                                                                       |
  | lean_strict_and                  : LeanPureExtern [.bool, .bool] .bool
--
-- # Init/Data/Repr.lean
--
-- | name of extern       | def | full name of func | type of func   |
-- | -------------------- | --- | ----------------- | -------------- |
-- | lean_string_of_usize | def | USize.repr        | USize → String |
  | lean_string_of_usize              : LeanPureExtern [.usize] .string
--
-- # Init/Util.lean
--
-- | name of extern           | def    | full name of func | type of func                         |
-- | ------------------------ | ------ | ----------------- | ------------------------------------ |
--
-- # Init/Data/Array/Set.lean
--
-- | name of extern  | def | full name of func | type of func                                                                                                        |
-- | --------------- | --- | ----------------- | ------------------------------------------------------------------------------------------------------------------- |
--
-- # Init/Data/Array/Basic.lean
--
-- | name of extern           | def    | full name of func    | type of func                                                                                                                                                                          |
-- | ------------------------ | ------ | -------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
--
-- # Init/Meta/Defs.lean
--
-- | name of extern                 | def    | full name of func                               | type of func  |
-- | ------------------------------ | ------ | ----------------------------------------------- | ------------- |
-- | lean_version_get_special_desc  | opaque | Lean.version.getSpecialDesc                     | Unit → String |
  | lean_version_get_special_desc     : LeanPureExtern [] .string
-- | lean_version_get_is_release    | opaque | Lean.version.getIsRelease                       | Unit → Bool   |
  | lean_version_get_is_release       : LeanPureExtern [] .bool
-- | lean_version_get_major         | opaque | _private.Init.Meta.Defs.0.Lean.version.getMajor | Unit → Nat    |
  | lean_version_get_major            : LeanPureExtern [] .nat
-- | lean_version_get_patch         | opaque | _private.Init.Meta.Defs.0.Lean.version.getPatch | Unit → Nat    |
  | lean_version_get_patch            : LeanPureExtern [] .nat
-- | lean_internal_is_stage0        | opaque | Lean.Internal.isStage0                          | Unit → Bool   |
  | lean_internal_is_stage0           : LeanPureExtern [] .bool
-- | lean_version_get_minor         | opaque | _private.Init.Meta.Defs.0.Lean.version.getMinor | Unit → Nat    |
  | lean_version_get_minor            : LeanPureExtern [] .nat
-- | lean_get_githash               | opaque | Lean.getGithash                                 | Unit → String |
  | lean_get_githash                  : LeanPureExtern [] .string
-- | lean_internal_has_llvm_backend | opaque | Lean.Internal.hasLLVMBackend                    | Unit → Bool   |
  | lean_internal_has_llvm_backend   : LeanPureExtern [] .bool
--
-- # Init/System/ST.lean
--
-- | name of extern | def    | full name of func | type of func            |
-- | -------------- | ------ | ----------------- | ----------------------- |
-- | lean_void_mk   | opaque | Void.mk           | {σ : Type} → σ → Void σ |
  -- COMMENTED OUT: its result type is `Void σ`, a *unit-like* type (`Void.mk` is the
  -- only way to build one and it carries no information).  Unit types are erased, so
  -- this extern has no representable `Ty`; the call itself is erased too.
  -- | lean_void_mk                      : (σ : Ty) → LeanPureExtern (σ ⇒ .unit)
--
-- # Init/Data/Nat/Log2.lean
--
-- | name of extern | def | full name of func | type of func   |
-- | -------------- | --- | ----------------- | -------------- |
-- | lean_nat_log2  | def | Nat.log2          | (@& Nat) → Nat |
  | lean_nat_log2                     : LeanPureExtern [.nat] .nat
--
-- # Init/Data/Int/DivMod/Basic.lean
--
-- | name of extern     | def | full name of func | type of func                                            |
-- | ------------------ | --- | ----------------- | ------------------------------------------------------- |
-- | lean_int_emod      | def | Int.emod          | (@& Int) → (@& Int) → Int                               |
  | lean_int_emod                     : LeanPureExtern [.int64, .int64] .int64
-- | lean_int_div_exact | def | Int.divExact      | (x : @& Int) → (y : @& Int) → Int.instDvd.dvd y x → Int |
  | lean_int_div_exact                : LeanPureExtern [.int64, .int64] .int64
-- | lean_int_mod       | def | Int.tmod          | (@& Int) → (@& Int) → Int                               |
  | lean_int_mod                      : LeanPureExtern [.int64, .int64] .int64
-- | lean_int_ediv      | def | Int.ediv          | (@& Int) → (@& Int) → Int                               |
  | lean_int_ediv                     : LeanPureExtern [.int64, .int64] .int64
-- | lean_int_div       | def | Int.tdiv          | (@& Int) → (@& Int) → Int                               |
  | lean_int_div                      : LeanPureExtern [.int64, .int64] .int64
--
-- # Init/Data/Nat/Gcd.lean
--
-- | name of extern | def | full name of func | type of func              |
-- | -------------- | --- | ----------------- | ------------------------- |
-- | lean_nat_gcd   | def | Nat.gcd._unary    | (_ : Nat) ×' Nat → Nat    |
-- |                |     | Nat.gcd           | (@& Nat) → (@& Nat) → Nat |
  | lean_nat_gcd                      : LeanPureExtern [.nat, .nat] .nat
--
-- # Init/Data/UInt/Basic.lean
--
-- | name of extern          | def | full name of func | type of func                                                  |
-- | ----------------------- | --- | ----------------- | ------------------------------------------------------------- |
-- | lean_uint64_shift_left  | def | UInt64.shiftLeft  | UInt64 → UInt64 → UInt64                                      |
  | lean_uint64_shift_left            : LeanPureExtern [.uint64, .uint64] .uint64
-- | lean_uint32_mod         | def | UInt32.mod        | UInt32 → UInt32 → UInt32                                      |
  | lean_uint32_mod                   : LeanPureExtern [.uint32, .uint32] .uint32
-- | lean_uint16_neg         | def | UInt16.neg        | UInt16 → UInt16                                               |
  | lean_uint16_neg                   : LeanPureExtern [.uint16] .uint16
-- | lean_usize_land         | def | USize.land        | USize → USize → USize                                         |
  | lean_usize_land                   : LeanPureExtern [.usize, .usize] .usize
-- | lean_usize_mul          | def | USize.mul         | USize → USize → USize                                         |
  | lean_usize_mul                    : LeanPureExtern [.usize, .usize] .usize
-- | lean_uint16_to_usize    | def | UInt16.toUSize    | UInt16 → USize                                                |
  | lean_uint16_to_usize              : LeanPureExtern [.uint16] .usize
-- | lean_uint64_shift_right | def | UInt64.shiftRight | UInt64 → UInt64 → UInt64                                      |
  | lean_uint64_shift_right           : LeanPureExtern [.uint64, .uint64] .uint64
-- | lean_usize_shift_left   | def | USize.shiftLeft   | USize → USize → USize                                         |
  | lean_usize_shift_left             : LeanPureExtern [.usize, .usize] .usize
-- | lean_uint16_add         | def | UInt16.add        | UInt16 → UInt16 → UInt16                                      |
  | lean_uint16_add                   : LeanPureExtern [.uint16, .uint16] .uint16
-- | lean_usize_xor          | def | USize.xor         | USize → USize → USize                                         |
  | lean_usize_xor                    : LeanPureExtern [.usize, .usize] .usize
-- | lean_uint64_complement  | def | UInt64.complement | UInt64 → UInt64                                               |
  | lean_uint64_complement            : LeanPureExtern [.uint64] .uint64
-- | lean_bool_to_uint32     | def | Bool.toUInt32     | Bool → UInt32                                                 |
  | lean_bool_to_uint32               : LeanPureExtern [.bool] .uint32
-- | lean_uint16_lor         | def | UInt16.lor        | UInt16 → UInt16 → UInt16                                      |
  | lean_uint16_lor                   : LeanPureExtern [.uint16, .uint16] .uint16
-- | lean_uint16_mul         | def | UInt16.mul        | UInt16 → UInt16 → UInt16                                      |
  | lean_uint16_mul                   : LeanPureExtern [.uint16, .uint16] .uint16
-- | lean_uint16_land        | def | UInt16.land       | UInt16 → UInt16 → UInt16                                      |
  | lean_uint16_land                  : LeanPureExtern [.uint16, .uint16] .uint16
-- | lean_uint8_sub          | def | UInt8.sub         | UInt8 → UInt8 → UInt8                                         |
  | lean_uint8_sub                    : LeanPureExtern [.uint8, .uint8] .uint8
-- | lean_uint32_div         | def | UInt32.div        | UInt32 → UInt32 → UInt32                                      |
  | lean_uint32_div                   : LeanPureExtern [.uint32, .uint32] .uint32
-- | lean_uint64_add         | def | UInt64.add        | UInt64 → UInt64 → UInt64                                      |
  | lean_uint64_add                   : LeanPureExtern [.uint64, .uint64] .uint64
-- | lean_uint8_neg          | def | UInt8.neg         | UInt8 → UInt8                                                 |
  | lean_uint8_neg                    : LeanPureExtern [.uint8] .uint8
-- | lean_uint16_complement  | def | UInt16.complement | UInt16 → UInt16                                               |
  | lean_uint16_complement            : LeanPureExtern [.uint16] .uint16
-- | lean_uint64_lor         | def | UInt64.lor        | UInt64 → UInt64 → UInt64                                      |
  | lean_uint64_lor                   : LeanPureExtern [.uint64, .uint64] .uint64
-- | lean_uint64_mod         | def | UInt64.mod        | UInt64 → UInt64 → UInt64                                      |
  | lean_uint64_mod                   : LeanPureExtern [.uint64, .uint64] .uint64
-- | lean_uint8_lor          | def | UInt8.lor         | UInt8 → UInt8 → UInt8                                         |
  | lean_uint8_lor                    : LeanPureExtern [.uint8, .uint8] .uint8
-- | lean_uint32_shift_right | def | UInt32.shiftRight | UInt32 → UInt32 → UInt32                                      |
  | lean_uint32_shift_right           : LeanPureExtern [.uint32, .uint32] .uint32
-- | lean_uint16_xor         | def | UInt16.xor        | UInt16 → UInt16 → UInt16                                      |
  | lean_uint16_xor                   : LeanPureExtern [.uint16, .uint16] .uint16
-- | lean_usize_lor          | def | USize.lor         | USize → USize → USize                                         |
  | lean_usize_lor                    : LeanPureExtern [.usize, .usize] .usize
-- | lean_uint8_div          | def | UInt8.div         | UInt8 → UInt8 → UInt8                                         |
  | lean_uint8_div                    : LeanPureExtern [.uint8, .uint8] .uint8
-- | lean_uint16_shift_left  | def | UInt16.shiftLeft  | UInt16 → UInt16 → UInt16                                      |
  | lean_uint16_shift_left            : LeanPureExtern [.uint16, .uint16] .uint16
-- | lean_uint32_neg         | def | UInt32.neg        | UInt32 → UInt32                                               |
  | lean_uint32_neg                   : LeanPureExtern [.uint32] .uint32
-- | lean_uint16_mod         | def | UInt16.mod        | UInt16 → UInt16 → UInt16                                      |
  | lean_uint16_mod                   : LeanPureExtern [.uint16, .uint16] .uint16
-- | lean_usize_neg          | def | USize.neg         | USize → USize                                                 |
  | lean_usize_neg                    : LeanPureExtern [.usize] .usize
-- | lean_uint64_div         | def | UInt64.div        | UInt64 → UInt64 → UInt64                                      |
  | lean_uint64_div                   : LeanPureExtern [.uint64, .uint64] .uint64
-- | lean_uint16_dec_lt      | def | UInt16.decLt      | (a : UInt16) → (b : UInt16) → Decidable (instLTUInt16.lt a b) |
  | lean_uint16_dec_lt                : LeanPureExtern [.uint16, .uint16] .bool
-- | lean_uint8_shift_right  | def | UInt8.shiftRight  | UInt8 → UInt8 → UInt8                                         |
  | lean_uint8_shift_right            : LeanPureExtern [.uint8, .uint8] .uint8
-- | lean_usize_to_uint64    | def | USize.toUInt64    | USize → UInt64                                                |
  | lean_usize_to_uint64              : LeanPureExtern [.usize] .uint64
-- | lean_uint32_lor         | def | UInt32.lor        | UInt32 → UInt32 → UInt32                                      |
  | lean_uint32_lor                   : LeanPureExtern [.uint32, .uint32] .uint32
-- | lean_uint64_mul         | def | UInt64.mul        | UInt64 → UInt64 → UInt64                                      |
  | lean_uint64_mul                   : LeanPureExtern [.uint64, .uint64] .uint64
-- | lean_usize_shift_right  | def | USize.shiftRight  | USize → USize → USize                                         |
  | lean_usize_shift_right            : LeanPureExtern [.usize, .usize] .usize
-- | lean_uint64_land        | def | UInt64.land       | UInt64 → UInt64 → UInt64                                      |
  | lean_uint64_land                  : LeanPureExtern [.uint64, .uint64] .uint64
-- | lean_uint8_shift_left   | def | UInt8.shiftLeft   | UInt8 → UInt8 → UInt8                                         |
  | lean_uint8_shift_left             : LeanPureExtern [.uint8, .uint8] .uint8
-- | lean_uint16_div         | def | UInt16.div        | UInt16 → UInt16 → UInt16                                      |
  | lean_uint16_div                   : LeanPureExtern [.uint16, .uint16] .uint16
-- | lean_bool_to_uint64     | def | Bool.toUInt64     | Bool → UInt64                                                 |
  | lean_bool_to_uint64               : LeanPureExtern [.bool] .uint64
-- | lean_uint8_land         | def | UInt8.land        | UInt8 → UInt8 → UInt8                                         |
  | lean_uint8_land                   : LeanPureExtern [.uint8, .uint8] .uint8
-- | lean_uint64_dec_le      | def | UInt64.decLe      | (a : UInt64) → (b : UInt64) → Decidable (instLEUInt64.le a b) |
  | lean_uint64_dec_le                : LeanPureExtern [.uint64, .uint64] .bool
-- | lean_uint8_mul          | def | UInt8.mul         | UInt8 → UInt8 → UInt8                                         |
  | lean_uint8_mul                    : LeanPureExtern [.uint8, .uint8] .uint8
-- | lean_usize_of_nat       | def | USize.ofNat32     | (n : @& Nat) → instLTNat.lt n 4294967296 → USize              |
  | lean_usize_of_nat32               : LeanPureExtern [.nat] .usize
-- | lean_uint64_sub         | def | UInt64.sub        | UInt64 → UInt64 → UInt64                                      |
  | lean_uint64_sub                   : LeanPureExtern [.uint64, .uint64] .uint64
-- | lean_uint64_neg         | def | UInt64.neg        | UInt64 → UInt64                                               |
  | lean_uint64_neg                   : LeanPureExtern [.uint64] .uint64
-- | lean_uint8_add          | def | UInt8.add         | UInt8 → UInt8 → UInt8                                         |
  | lean_uint8_add                    : LeanPureExtern [.uint8, .uint8] .uint8
-- | lean_usize_div          | def | USize.div         | USize → USize → USize                                         |
  | lean_usize_div                    : LeanPureExtern [.usize, .usize] .usize
-- | lean_uint32_to_usize    | def | UInt32.toUSize    | UInt32 → USize                                                |
  | lean_uint32_to_usize              : LeanPureExtern [.uint32] .usize
-- | lean_uint8_complement   | def | UInt8.complement  | UInt8 → UInt8                                                 |
  | lean_uint8_complement             : LeanPureExtern [.uint8] .uint8
-- | lean_usize_to_uint16    | def | USize.toUInt16    | USize → UInt16                                                |
  | lean_usize_to_uint16              : LeanPureExtern [.usize] .uint16
-- | lean_uint32_xor         | def | UInt32.xor        | UInt32 → UInt32 → UInt32                                      |
  | lean_uint32_xor                   : LeanPureExtern [.uint32, .uint32] .uint32
-- | lean_uint16_dec_le      | def | UInt16.decLe      | (a : UInt16) → (b : UInt16) → Decidable (instLEUInt16.le a b) |
  | lean_uint16_dec_le                : LeanPureExtern [.uint16, .uint16] .bool
-- | lean_usize_to_uint8     | def | USize.toUInt8     | USize → UInt8                                                 |
  | lean_usize_to_uint8               : LeanPureExtern [.usize] .uint8
-- | lean_uint32_shift_left  | def | UInt32.shiftLeft  | UInt32 → UInt32 → UInt32                                      |
  | lean_uint32_shift_left            : LeanPureExtern [.uint32, .uint32] .uint32
-- | lean_uint16_sub         | def | UInt16.sub        | UInt16 → UInt16 → UInt16                                      |
  | lean_uint16_sub                   : LeanPureExtern [.uint16, .uint16] .uint16
-- | lean_uint32_mul         | def | UInt32.mul        | UInt32 → UInt32 → UInt32                                      |
  | lean_uint32_mul                   : LeanPureExtern [.uint32, .uint32] .uint32
-- | lean_uint32_land        | def | UInt32.land       | UInt32 → UInt32 → UInt32                                      |
  | lean_uint32_land                  : LeanPureExtern [.uint32, .uint32] .uint32
-- | lean_usize_mod          | def | USize.mod         | USize → USize → USize                                         |
  | lean_usize_mod                    : LeanPureExtern [.usize, .usize] .usize
-- | lean_uint8_mod          | def | UInt8.mod         | UInt8 → UInt8 → UInt8                                         |
  | lean_uint8_mod                    : LeanPureExtern [.uint8, .uint8] .uint8
-- | lean_uint64_dec_lt      | def | UInt64.decLt      | (a : UInt64) → (b : UInt64) → Decidable (instLTUInt64.lt a b) |
  | lean_uint64_dec_lt                : LeanPureExtern [.uint64, .uint64] .bool
-- | lean_bool_to_uint8      | def | Bool.toUInt8      | Bool → UInt8                                                  |
  | lean_bool_to_uint8                : LeanPureExtern [.bool] .uint8
-- | lean_uint32_complement  | def | UInt32.complement | UInt32 → UInt32                                               |
  | lean_uint32_complement            : LeanPureExtern [.uint32] .uint32
-- | lean_uint8_to_usize     | def | UInt8.toUSize     | UInt8 → USize                                                 |
  | lean_uint8_to_usize               : LeanPureExtern [.uint8] .usize
-- | lean_bool_to_uint16     | def | Bool.toUInt16     | Bool → UInt16                                                 |
  | lean_bool_to_uint16               : LeanPureExtern [.bool] .uint16
-- | lean_uint8_xor          | def | UInt8.xor         | UInt8 → UInt8 → UInt8                                         |
  | lean_uint8_xor                    : LeanPureExtern [.uint8, .uint8] .uint8
-- | lean_bool_to_usize      | def | Bool.toUSize      | Bool → USize                                                  |
  | lean_bool_to_usize                : LeanPureExtern [.bool] .usize
-- | lean_uint64_to_usize    | def | UInt64.toUSize    | UInt64 → USize                                                |
  | lean_uint64_to_usize              : LeanPureExtern [.uint64] .usize
-- | lean_uint16_shift_right | def | UInt16.shiftRight | UInt16 → UInt16 → UInt16                                      |
  | lean_uint16_shift_right           : LeanPureExtern [.uint16, .uint16] .uint16
-- | lean_usize_to_uint32    | def | USize.toUInt32    | USize → UInt32                                                |
  | lean_usize_to_uint32              : LeanPureExtern [.usize] .uint32
-- | lean_usize_complement   | def | USize.complement  | USize → USize                                                 |
  | lean_usize_complement             : LeanPureExtern [.usize] .usize
-- | lean_uint64_xor         | def | UInt64.xor        | UInt64 → UInt64 → UInt64                                      |
  | lean_uint64_xor                   : LeanPureExtern [.uint64, .uint64] .uint64
--
-- # Init/Data/ByteArray/Basic.lean
--
-- | name of extern             | def    | full name of func   | type of func                                                                                                       |
-- | -------------------------- | ------ | ------------------- | ------------------------------------------------------------------------------------------------------------------ |
-- | lean_byte_array_copy_slice | def    | ByteArray.copySlice | (@& ByteArray) → Nat → ByteArray → Nat → Nat → optParam Bool Bool.true → ByteArray                                 |
  | lean_byte_array_copy_slice             : LeanPureExtern [.byteArray, .nat, .byteArray, .nat, .nat, .bool] .byteArray
-- | lean_byte_array_hash       | opaque | ByteArray.hash      | (@& ByteArray) → UInt64                                                                                            |
  | lean_byte_array_hash                   : LeanPureExtern [.byteArray] .uint64
-- | lean_sarray_size           | def    | ByteArray.usize     | (@& ByteArray) → USize                                                                                             |
  | lean_sarray_size                       : LeanPureExtern [.byteArray] .usize
-- | lean_sarray_dec_eq         | def    | ByteArray.beq       | (@& ByteArray) → (@& ByteArray) → Bool                                                                             |
  | lean_sarray_beq                        : LeanPureExtern [.byteArray, .byteArray] .bool
-- |                            |        | ByteArray.decEq     | (lhs : @& ByteArray) → (rhs : @& ByteArray) → Decidable (Eq lhs rhs)                                               |
  | lean_sarray_dec_eq                     : LeanPureExtern [.byteArray, .byteArray] .bool
-- | lean_byte_array_set        | def    | ByteArray.set!      | ByteArray → (@& Nat) → UInt8 → ByteArray                                                                           |
  | lean_byte_array_set                    : LeanPureExtern [.byteArray, .nat, .uint8] .byteArray
-- | lean_byte_array_fget       | def    | ByteArray.get       | (a : @& ByteArray) → (i : @& Nat) → autoParam (instLTNat.lt i a.size) ByteArray.get._auto_1 → UInt8                |
  | lean_byte_array_fget                   : LeanPureExtern [.byteArray, .nat] .uint8
-- | lean_byte_array_uset       | def    | ByteArray.uset      | (a : ByteArray) → (i : USize) → UInt8 → autoParam (instLTNat.lt i.toNat a.size) ByteArray.uset._auto_1 → ByteArray |
  | lean_byte_array_uset                   : LeanPureExtern [.byteArray, .usize, .uint8] .byteArray
-- | lean_byte_array_fset       | def    | ByteArray.set       | (a : ByteArray) → (i : @& Nat) → UInt8 → autoParam (instLTNat.lt i a.size) ByteArray.set._auto_1 → ByteArray       |
  | lean_byte_array_fset                   : LeanPureExtern [.byteArray, .nat, .uint8] .byteArray
-- | lean_byte_array_uget       | def    | ByteArray.uget      | (a : @& ByteArray) → (i : USize) → autoParam (instLTNat.lt i.toNat a.size) ByteArray.uget._auto_1 → UInt8          |
  | lean_byte_array_uget                   : LeanPureExtern [.byteArray, .usize] .uint8
-- | lean_byte_array_get        | def    | ByteArray.get!      | (@& ByteArray) → (@& Nat) → UInt8                                                                                  |
  | lean_byte_array_get                    : LeanPureExtern [.byteArray, .nat] .uint8
--
-- # Init/Data/String/PosRaw.lean
--
-- | name of extern            | def | full name of func  | type of func                                                                       |
-- | ------------------------- | --- | ------------------ | ---------------------------------------------------------------------------------- |
-- | lean_string_get_byte_fast | def | String.getUtf8Byte | (s : String) → (p : String.Pos.Raw) → String.instLTRaw.lt p s.rawEndPos → UInt8    |
  | lean_string_get_utf8_byte              : LeanPureExtern [.string, .stringPos] .uint8
-- |                           |     | String.getUTF8Byte | (s : @& String) → (p : String.Pos.Raw) → String.instLTRaw.lt p s.rawEndPos → UInt8 |
  | lean_string_get_byte_fast_raw          : LeanPureExtern [.string, .stringPos] .uint8
--
-- # Init/Data/String/Defs.lean
--
-- | name of extern      | def | full name of func | type of func                  |
-- | ------------------- | --- | ----------------- | ----------------------------- |
-- | lean_string_to_utf8 | def | String.toUTF8     | (@& String) → ByteArray       |
  | lean_string_to_utf8_defs               : LeanPureExtern [.string] .byteArray
-- | lean_string_append  | def | String.append     | String → (@& String) → String |
  | lean_string_append_defs                : LeanPureExtern [.string, .string] .string
--
-- # Init/System/Platform.lean
--
-- | name of extern                         | def    | full name of func                               | type of func  |
-- | -------------------------------------- | ------ | ----------------------------------------------- | ------------- |
-- | lean_internal_get_hardware_concurrency | opaque | System.Platform.Internal.getHardwareConcurrency | Unit → UInt32 |
  | lean_internal_get_hardware_concurrency : LeanPureExtern [] .uint32
-- | lean_system_platform_linux             | opaque | System.Platform.getIsLinux                      | Unit → Bool   |
  | lean_system_platform_linux             : LeanPureExtern [] .bool
-- | lean_system_platform_emscripten        | opaque | System.Platform.getIsEmscripten                 | Unit → Bool   |
  | lean_system_platform_emscripten        : LeanPureExtern [] .bool
-- | lean_system_platform_target            | opaque | System.Platform.getTarget                       | Unit → String |
  | lean_system_platform_target            : LeanPureExtern [] .string
-- | lean_system_platform_windows           | opaque | System.Platform.getIsWindows                    | Unit → Bool   |
  | lean_system_platform_windows           : LeanPureExtern [] .bool
-- | lean_system_platform_osx               | opaque | System.Platform.getIsOSX                        | Unit → Bool   |
  | lean_system_platform_osx               : LeanPureExtern [] .bool
--
-- # Init/Data/String/Basic.lean
--
-- | name of extern                | def | full name of func      | type of func                                                                                               |
-- | ----------------------------- | --- | ---------------------- | ---------------------------------------------------------------------------------------------------------- |
-- | lean_string_utf8_next         | def | String.next            | (@& String) → (@& String.Pos.Raw) → String.Pos.Raw                                                         |
  | lean_string_utf8_next_basic            : LeanPureExtern [.string, .stringPos] .stringPos
-- |                               |     | String.Pos.Raw.next    |                                                                                                            |
  | lean_string_pos_raw_next               : LeanPureExtern [.string, .stringPos] .stringPos
-- | lean_string_utf8_get          | def | String.Pos.Raw.get     | (@& String) → (@& String.Pos.Raw) → Char                                                                   |
  | lean_string_pos_raw_get                : LeanPureExtern [.string, .stringPos] .char
-- |                               |     | String.get             |                                                                                                            |
  | lean_string_get_basic                  : LeanPureExtern [.string, .stringPos] .char
-- | lean_string_utf8_get_opt      | def | String.Pos.Raw.get?    | (@& String) → (@& String.Pos.Raw) → Option Char                                                            |
  | lean_string_pos_raw_get_opt            : LeanPureExtern [.string, .stringPos] (.option .char)
-- |                               |     | String.get?            |                                                                                                            |
  | lean_string_get_opt                    : LeanPureExtern [.string, .stringPos] (.option .char)
-- | lean_string_utf8_prev         | def | String.Pos.Raw.prev    | (@& String) → (@& String.Pos.Raw) → String.Pos.Raw                                                         |
  | lean_string_pos_raw_prev               : LeanPureExtern [.string, .stringPos] .stringPos
-- |                               |     | String.prev            |                                                                                                            |
  | lean_string_prev                       : LeanPureExtern [.string, .stringPos] .stringPos
-- | lean_string_utf8_next_fast    | def | String.next'           | (s : @& String) → (p : @& String.Pos.Raw) → Not (Eq (String.Pos.Raw.atEnd s p) Bool.true) → String.Pos.Raw |
  | lean_string_next_fast                  : LeanPureExtern [.string, .stringPos] .stringPos
-- |                               |     | String.Pos.Raw.next'   |                                                                                                            |
  | lean_string_pos_raw_next_fast          : LeanPureExtern [.string, .stringPos] .stringPos
-- |                               |     | String.Pos.next        | {s : @& String} → (pos : @& s.Pos) → Ne pos s.endPos → s.Pos                                               |
  | lean_string_pos_next                   : LeanPureExtern [.string, .stringPos] .stringPos
-- | lean_string_data              | def | String.data            | String → List Char                                                                                         |
  | lean_string_data                       : LeanPureExtern [.string] (.list .char)
-- |                               |     | String.toList          |                                                                                                            |
  | lean_string_to_list                    : LeanPureExtern [.string] (.list .char)
-- | lean_string_utf8_extract_fast | def | String.extract         | {s : @& String} → (@& s.Pos) → (@& s.Pos) → String                                                         |
  | lean_string_utf8_extract_fast          : LeanPureExtern [.string, .stringPos, .stringPos] .string
-- | lean_string_utf8_at_end       | def | String.atEnd           | (@& String) → (@& String.Pos.Raw) → Bool                                                                   |
  | lean_string_at_end_basic               : LeanPureExtern [.string, .stringPos] .bool
-- |                               |     | String.Pos.Raw.atEnd   |                                                                                                            |
  | lean_string_pos_raw_at_end             : LeanPureExtern [.string, .stringPos] .bool
-- | lean_string_utf8_get_bang     | def | String.Pos.Raw.get!    | (@& String) → (@& String.Pos.Raw) → Char                                                                   |
  | lean_string_pos_raw_get_bang           : LeanPureExtern [.string, .stringPos] .char
-- |                               |     | String.get!            |                                                                                                            |
  | lean_string_get_bang                   : LeanPureExtern [.string, .stringPos] .char
-- | lean_string_utf8_get_fast     | def | String.decodeChar      | (s : @& String) → (byteIdx : @& Nat) → Eq (s.toByteArray.utf8DecodeChar? byteIdx).isSome Bool.true → Char  |
  | lean_string_decode_char                : LeanPureExtern [.string, .nat] .char
-- |                               |     | String.get'            | (s : @& String) → (p : @& String.Pos.Raw) → Not (Eq (String.Pos.Raw.atEnd s p) Bool.true) → Char           |
  | lean_string_get_fast                   : LeanPureExtern [.string, .stringPos] .char
-- |                               |     | String.Pos.Raw.get'    |                                                                                                            |
  | lean_string_pos_raw_get_fast           : LeanPureExtern [.string, .stringPos] .char
-- | lean_string_is_valid_pos      | def | String.Pos.Raw.isValid | (@& String) → (@& String.Pos.Raw) → Bool                                                                   |
  | lean_string_is_valid_pos               : LeanPureExtern [.string, .stringPos] .bool
-- | lean_string_dec_lt            | def | String.decidableLT     | (s₁ : @& String) → (s₂ : @& String) → Decidable (String.instLT.lt s₁ s₂)                                   |
  | lean_string_dec_lt                     : LeanPureExtern [.string, .string] .bool
-- | lean_string_validate_utf8     | def | ByteArray.validateUTF8 | (@& ByteArray) → Bool                                                                                      |
  | lean_string_validate_utf8              : LeanPureExtern [.byteArray] .bool
-- | lean_string_utf8_extract      | def | String.Pos.Raw.extract | (@& String) → (@& String.Pos.Raw) → (@& String.Pos.Raw) → String                                           |
  | lean_string_utf8_extract_basic         : LeanPureExtern [.string, .stringPos, .stringPos] .string
--
-- # Init/Data/String/Length.lean
--
-- | name of extern     | def | full name of func | type of func      |
-- | ------------------ | --- | ----------------- | ----------------- |
-- | lean_string_length | def | String.length     | (@& String) → Nat |
  | lean_string_length_def                 : LeanPureExtern [.string] .nat
--
-- # Init/Data/SInt/Basic.lean
--
-- | name of extern         | def | full name of func | type of func                                               |
-- | ---------------------- | --- | ----------------- | ---------------------------------------------------------- |
-- | lean_isize_complement  | def | ISize.complement  | ISize → ISize                                              |
  | lean_isize_complement                  : LeanPureExtern [.isize] .isize
-- | lean_int8_add          | def | Int8.add          | Int8 → Int8 → Int8                                         |
  | lean_int8_add                          : LeanPureExtern [.int8, .int8] .int8
-- | lean_int16_of_nat      | def | Int16.ofNat       | (@& Nat) → Int16                                           |
  | lean_int16_of_nat                      : LeanPureExtern [.nat] .int16
-- | lean_int16_dec_le      | def | Int16.decLe       | (a : Int16) → (b : Int16) → Decidable (instLEInt16.le a b) |
  | lean_int16_dec_le                      : LeanPureExtern [.int16, .int16] .bool
-- | lean_int32_of_int      | def | Int32.ofInt       | (@& Int) → Int32                                           |
  | lean_int32_of_int                      : LeanPureExtern [.int64] .int32
-- | lean_int64_to_isize    | def | Int64.toISize     | Int64 → ISize                                              |
  | lean_int64_to_isize                    : LeanPureExtern [.int64] .isize
-- | lean_int32_land        | def | Int32.land        | Int32 → Int32 → Int32                                      |
  | lean_int32_land                        : LeanPureExtern [.int32, .int32] .int32
-- | lean_int8_div          | def | Int8.div          | Int8 → Int8 → Int8                                         |
  | lean_int8_div                          : LeanPureExtern [.int8, .int8] .int8
-- | lean_int32_mul         | def | Int32.mul         | Int32 → Int32 → Int32                                      |
  | lean_int32_mul                         : LeanPureExtern [.int32, .int32] .int32
-- | lean_int64_sub         | def | Int64.sub         | Int64 → Int64 → Int64                                      |
  | lean_int64_sub                         : LeanPureExtern [.int64, .int64] .int64
-- | lean_int16_shift_right | def | Int16.shiftRight  | Int16 → Int16 → Int16                                      |
  | lean_int16_shift_right                 : LeanPureExtern [.int16, .int16] .int16
-- | lean_isize_to_int8     | def | ISize.toInt8      | ISize → Int8                                               |
  | lean_isize_to_int8                     : LeanPureExtern [.isize] .int8
-- | lean_int64_xor         | def | Int64.xor         | Int64 → Int64 → Int64                                      |
  | lean_int64_xor                         : LeanPureExtern [.int64, .int64] .int64
-- | lean_int32_dec_le      | def | Int32.decLe       | (a : Int32) → (b : Int32) → Decidable (instLEInt32.le a b) |
  | lean_int32_dec_le                      : LeanPureExtern [.int32, .int32] .bool
-- | lean_int32_of_nat      | def | Int32.ofNat       | (@& Nat) → Int32                                           |
  | lean_int32_of_nat                      : LeanPureExtern [.nat] .int32
-- | lean_isize_xor         | def | ISize.xor         | ISize → ISize → ISize                                      |
  | lean_isize_xor                         : LeanPureExtern [.isize, .isize] .isize
-- | lean_int64_to_int8     | def | Int64.toInt8      | Int64 → Int8                                               |
  | lean_int64_to_int8                     : LeanPureExtern [.int64] .int8
-- | lean_isize_shift_left  | def | ISize.shiftLeft   | ISize → ISize → ISize                                      |
  | lean_isize_shift_left                  : LeanPureExtern [.isize, .isize] .isize
-- | lean_int64_mul         | def | Int64.mul         | Int64 → Int64 → Int64                                      |
  | lean_int64_mul                         : LeanPureExtern [.int64, .int64] .int64
-- | lean_int32_to_int64    | def | Int32.toInt64     | Int32 → Int64                                              |
  | lean_int32_to_int64                    : LeanPureExtern [.int32] .int64
-- | lean_int8_to_int16     | def | Int8.toInt16      | Int8 → Int16                                               |
  | lean_int8_to_int16                     : LeanPureExtern [.int8] .int16
-- | lean_int32_sub         | def | Int32.sub         | Int32 → Int32 → Int32                                      |
  | lean_int32_sub                         : LeanPureExtern [.int32, .int32] .int32
-- | lean_int64_of_int      | def | Int64.ofInt       | (@& Int) → Int64                                           |
  | lean_int64_of_int                      : LeanPureExtern [.int64] .int64
-- | lean_int32_to_isize    | def | Int32.toISize     | Int32 → ISize                                              |
  | lean_int32_to_isize                    : LeanPureExtern [.int32] .isize
-- | lean_int64_land        | def | Int64.land        | Int64 → Int64 → Int64                                      |
  | lean_int64_land                        : LeanPureExtern [.int64, .int64] .int64
-- | lean_int8_shift_right  | def | Int8.shiftRight   | Int8 → Int8 → Int8                                         |
  | lean_int8_shift_right                  : LeanPureExtern [.int8, .int8] .int8
-- | lean_int64_lor         | def | Int64.lor         | Int64 → Int64 → Int64                                      |
  | lean_int64_lor                         : LeanPureExtern [.int64, .int64] .int64
-- | lean_int16_div         | def | Int16.div         | Int16 → Int16 → Int16                                      |
  | lean_int16_div                         : LeanPureExtern [.int16, .int16] .int16
-- | lean_isize_mod         | def | ISize.mod         | ISize → ISize → ISize                                      |
  | lean_isize_mod                         : LeanPureExtern [.isize, .isize] .isize
-- | lean_int32_neg         | def | Int32.neg         | Int32 → Int32                                              |
  | lean_int32_neg                         : LeanPureExtern [.int32] .int32
-- | lean_int8_mod          | def | Int8.mod          | Int8 → Int8 → Int8                                         |
  | lean_int8_mod                          : LeanPureExtern [.int8, .int8] .int8
-- | lean_int32_abs         | def | Int32.abs         | Int32 → Int32                                              |
  | lean_int32_abs                         : LeanPureExtern [.int32] .int32
-- | lean_bool_to_int8      | def | Bool.toInt8       | Bool → Int8                                                |
  | lean_bool_to_int8                      : LeanPureExtern [.bool] .int8
-- | lean_isize_shift_right | def | ISize.shiftRight  | ISize → ISize → ISize                                      |
  | lean_isize_shift_right                 : LeanPureExtern [.isize, .isize] .isize
-- | lean_isize_to_int16    | def | ISize.toInt16     | ISize → Int16                                              |
  | lean_isize_to_int16                    : LeanPureExtern [.isize] .int16
-- | lean_int8_shift_left   | def | Int8.shiftLeft    | Int8 → Int8 → Int8                                         |
  | lean_int8_shift_left                   : LeanPureExtern [.int8, .int8] .int8
-- | lean_int16_dec_lt      | def | Int16.decLt       | (a : Int16) → (b : Int16) → Decidable (instLTInt16.lt a b) |
  | lean_int16_dec_lt                      : LeanPureExtern [.int16, .int16] .bool
-- | lean_int8_xor          | def | Int8.xor          | Int8 → Int8 → Int8                                         |
  | lean_int8_xor                          : LeanPureExtern [.int8, .int8] .int8
-- | lean_int32_dec_eq      | def | Int32.decEq       | (a : Int32) → (b : Int32) → Decidable (Eq a b)             |
  | lean_int32_dec_eq                      : LeanPureExtern [.int32, .int32] .bool
-- | lean_int16_to_int      | def | Int16.toInt       | Int16 → Int                                                |
  | lean_int16_to_int                      : LeanPureExtern [.int16] .int64
-- | lean_int16_mod         | def | Int16.mod         | Int16 → Int16 → Int16                                      |
  | lean_int16_mod                         : LeanPureExtern [.int16, .int16] .int16
-- | lean_isize_div         | def | ISize.div         | ISize → ISize → ISize                                      |
  | lean_isize_div                         : LeanPureExtern [.isize, .isize] .isize
-- | lean_int16_dec_eq      | def | Int16.decEq       | (a : Int16) → (b : Int16) → Decidable (Eq a b)             |
  | lean_int16_dec_eq                      : LeanPureExtern [.int16, .int16] .bool
-- | lean_int8_complement   | def | Int8.complement   | Int8 → Int8                                                |
  | lean_int8_complement                   : LeanPureExtern [.int8] .int8
-- | lean_isize_add         | def | ISize.add         | ISize → ISize → ISize                                      |
  | lean_isize_add                         : LeanPureExtern [.isize, .isize] .isize
-- | lean_bool_to_int16     | def | Bool.toInt16      | Bool → Int16                                               |
  | lean_bool_to_int16                     : LeanPureExtern [.bool] .int16
-- | lean_int32_dec_lt      | def | Int32.decLt       | (a : Int32) → (b : Int32) → Decidable (instLTInt32.lt a b) |
  | lean_int32_dec_lt                      : LeanPureExtern [.int32, .int32] .bool
-- | lean_isize_lor         | def | ISize.lor         | ISize → ISize → ISize                                      |
  | lean_isize_lor                         : LeanPureExtern [.isize, .isize] .isize
-- | lean_int64_mod         | def | Int64.mod         | Int64 → Int64 → Int64                                      |
  | lean_int64_mod                         : LeanPureExtern [.int64, .int64] .int64
-- | lean_isize_of_int      | def | ISize.ofInt       | (@& Int) → ISize                                           |
  | lean_isize_of_int                      : LeanPureExtern [.int64] .isize
-- | lean_int64_shift_left  | def | Int64.shiftLeft   | Int64 → Int64 → Int64                                      |
  | lean_int64_shift_left                  : LeanPureExtern [.int64, .int64] .int64
-- | lean_int16_abs         | def | Int16.abs         | Int16 → Int16                                              |
  | lean_int16_abs                         : LeanPureExtern [.int16] .int16
-- | lean_isize_land        | def | ISize.land        | ISize → ISize → ISize                                      |
  | lean_isize_land                        : LeanPureExtern [.isize, .isize] .isize
-- | lean_int16_to_int32    | def | Int16.toInt32     | Int16 → Int32                                              |
  | lean_int16_to_int32                    : LeanPureExtern [.int16] .int32
-- | lean_isize_mul         | def | ISize.mul         | ISize → ISize → ISize                                      |
  | lean_isize_mul                         : LeanPureExtern [.isize, .isize] .isize
-- | lean_isize_to_int      | def | ISize.toInt       | ISize → Int                                                |
  | lean_isize_to_int                      : LeanPureExtern [.isize] .int64
-- | lean_int64_dec_lt      | def | Int64.decLt       | (a : Int64) → (b : Int64) → Decidable (instLTInt64.lt a b) |
  | lean_int64_dec_lt                      : LeanPureExtern [.int64, .int64] .bool
-- | lean_isize_dec_le      | def | ISize.decLe       | (a : ISize) → (b : ISize) → Decidable (instLEISize.le a b) |
  | lean_isize_dec_le                      : LeanPureExtern [.isize, .isize] .bool
-- | lean_int8_dec_eq       | def | Int8.decEq        | (a : Int8) → (b : Int8) → Decidable (Eq a b)               |
  | lean_int8_dec_eq                       : LeanPureExtern [.int8, .int8] .bool
-- | lean_int32_xor         | def | Int32.xor         | Int32 → Int32 → Int32                                      |
  | lean_int32_xor                         : LeanPureExtern [.int32, .int32] .int32
-- | lean_isize_of_nat      | def | ISize.ofNat       | (@& Nat) → ISize                                           |
  | lean_isize_of_nat                      : LeanPureExtern [.nat] .isize
-- | lean_int16_complement  | def | Int16.complement  | Int16 → Int16                                              |
  | lean_int16_complement                  : LeanPureExtern [.int16] .int16
-- | lean_int32_shift_left  | def | Int32.shiftLeft   | Int32 → Int32 → Int32                                      |
  | lean_int32_shift_left                  : LeanPureExtern [.int32, .int32] .int32
-- | lean_isize_to_int64    | def | ISize.toInt64     | ISize → Int64                                              |
  | lean_isize_to_int64                    : LeanPureExtern [.isize] .int64
-- | lean_isize_sub         | def | ISize.sub         | ISize → ISize → ISize                                      |
  | lean_isize_sub                         : LeanPureExtern [.isize, .isize] .isize
-- | lean_int64_complement  | def | Int64.complement  | Int64 → Int64                                              |
  | lean_int64_complement                  : LeanPureExtern [.int64] .int64
-- | lean_isize_abs         | def | ISize.abs         | ISize → ISize                                              |
  | lean_isize_abs                         : LeanPureExtern [.isize] .isize
-- | lean_int16_land        | def | Int16.land        | Int16 → Int16 → Int16                                      |
  | lean_int16_land                        : LeanPureExtern [.int16, .int16] .int16
-- | lean_int16_of_int      | def | Int16.ofInt       | (@& Int) → Int16                                           |
  | lean_int16_of_int                      : LeanPureExtern [.int64] .int16
-- | lean_int32_shift_right | def | Int32.shiftRight  | Int32 → Int32 → Int32                                      |
  | lean_int32_shift_right                 : LeanPureExtern [.int32, .int32] .int32
-- | lean_int8_neg          | def | Int8.neg          | Int8 → Int8                                                |
  | lean_int8_neg                          : LeanPureExtern [.int8] .int8
-- | lean_int16_mul         | def | Int16.mul         | Int16 → Int16 → Int16                                      |
  | lean_int16_mul                         : LeanPureExtern [.int16, .int16] .int16
-- | lean_isize_to_int32    | def | ISize.toInt32     | ISize → Int32                                              |
  | lean_isize_to_int32                    : LeanPureExtern [.isize] .int32
-- | lean_int64_to_int32    | def | Int64.toInt32     | Int64 → Int32                                              |
  | lean_int64_to_int32                    : LeanPureExtern [.int64] .int32
-- | lean_int16_shift_left  | def | Int16.shiftLeft   | Int16 → Int16 → Int16                                      |
  | lean_int16_shift_left                  : LeanPureExtern [.int16, .int16] .int16
-- | lean_int64_abs         | def | Int64.abs         | Int64 → Int64                                              |
  | lean_int64_abs                         : LeanPureExtern [.int64] .int64
-- | lean_int32_complement  | def | Int32.complement  | Int32 → Int32                                              |
  | lean_int32_complement                  : LeanPureExtern [.int32] .int32
-- | lean_int16_xor         | def | Int16.xor         | Int16 → Int16 → Int16                                      |
  | lean_int16_xor                         : LeanPureExtern [.int16, .int16] .int16
-- | lean_bool_to_int64     | def | Bool.toInt64      | Bool → Int64                                               |
  | lean_bool_to_int64                     : LeanPureExtern [.bool] .int64
-- | lean_bool_to_isize     | def | Bool.toISize      | Bool → ISize                                               |
  | lean_bool_to_isize                     : LeanPureExtern [.bool] .isize
-- | lean_int8_dec_lt       | def | Int8.decLt        | (a : Int8) → (b : Int8) → Decidable (instLTInt8.lt a b)    |
  | lean_int8_dec_lt                       : LeanPureExtern [.int8, .int8] .bool
-- | lean_int64_dec_eq      | def | Int64.decEq       | (a : Int64) → (b : Int64) → Decidable (Eq a b)             |
  | lean_int64_dec_eq                      : LeanPureExtern [.int64, .int64] .bool
-- | lean_int64_dec_le      | def | Int64.decLe       | (a : Int64) → (b : Int64) → Decidable (instLEInt64.le a b) |
  | lean_int64_dec_le                      : LeanPureExtern [.int64, .int64] .bool
-- | lean_bool_to_int32     | def | Bool.toInt32      | Bool → Int32                                               |
  | lean_bool_to_int32                     : LeanPureExtern [.bool] .int32
-- | lean_int64_of_nat      | def | Int64.ofNat       | (@& Nat) → Int64                                           |
  | lean_int64_of_nat                      : LeanPureExtern [.nat] .int64
-- | lean_int32_to_int8     | def | Int32.toInt8      | Int32 → Int8                                               |
  | lean_int32_to_int8                     : LeanPureExtern [.int32] .int8
-- | lean_int64_to_int_sint | def | Int64.toInt       | Int64 → Int                                                |
  | lean_int64_to_int_sint                 : LeanPureExtern [.int64] .int64
-- | lean_int32_add         | def | Int32.add         | Int32 → Int32 → Int32                                      |
  | lean_int32_add                         : LeanPureExtern [.int32, .int32] .int32
-- | lean_isize_dec_lt      | def | ISize.decLt       | (a : ISize) → (b : ISize) → Decidable (instLTISize.lt a b) |
  | lean_isize_dec_lt                      : LeanPureExtern [.isize, .isize] .bool
-- | lean_int64_neg         | def | Int64.neg         | Int64 → Int64                                              |
  | lean_int64_neg                         : LeanPureExtern [.int64] .int64
-- | lean_int32_lor         | def | Int32.lor         | Int32 → Int32 → Int32                                      |
  | lean_int32_lor                         : LeanPureExtern [.int32, .int32] .int32
-- | lean_int8_abs          | def | Int8.abs          | Int8 → Int8                                                |
  | lean_int8_abs                          : LeanPureExtern [.int8] .int8
-- | lean_int8_to_int32     | def | Int8.toInt32      | Int8 → Int32                                               |
  | lean_int8_to_int32                     : LeanPureExtern [.int8] .int32
-- | lean_int32_mod         | def | Int32.mod         | Int32 → Int32 → Int32                                      |
  | lean_int32_mod                         : LeanPureExtern [.int32, .int32] .int32
-- | lean_isize_neg         | def | ISize.neg         | ISize → ISize                                              |
  | lean_isize_neg                         : LeanPureExtern [.isize] .isize
-- | lean_int32_to_int      | def | Int32.toInt       | Int32 → Int                                                |
  | lean_int32_to_int                      : LeanPureExtern [.int32] .int64
-- | lean_int64_add         | def | Int64.add         | Int64 → Int64 → Int64                                      |
  | lean_int64_add                         : LeanPureExtern [.int64, .int64] .int64
-- | lean_int8_sub          | def | Int8.sub          | Int8 → Int8 → Int8                                         |
  | lean_int8_sub                          : LeanPureExtern [.int8, .int8] .int8
-- | lean_int32_to_int16    | def | Int32.toInt16     | Int32 → Int16                                              |
  | lean_int32_to_int16                    : LeanPureExtern [.int32] .int16
-- | lean_int8_to_int64     | def | Int8.toInt64      | Int8 → Int64                                               |
  | lean_int8_to_int64                     : LeanPureExtern [.int8] .int64
-- | lean_int16_lor         | def | Int16.lor         | Int16 → Int16 → Int16                                      |
  | lean_int16_lor                         : LeanPureExtern [.int16, .int16] .int16
-- | lean_int64_div         | def | Int64.div         | Int64 → Int64 → Int64                                      |
  | lean_int64_div                         : LeanPureExtern [.int64, .int64] .int64
-- | lean_int8_to_isize     | def | Int8.toISize      | Int8 → ISize                                               |
  | lean_int8_to_isize                     : LeanPureExtern [.int8] .isize
-- | lean_isize_dec_eq      | def | ISize.decEq       | (a : ISize) → (b : ISize) → Decidable (Eq a b)             |
  | lean_isize_dec_eq                      : LeanPureExtern [.isize, .isize] .bool
-- | lean_int16_add         | def | Int16.add         | Int16 → Int16 → Int16                                      |
  | lean_int16_add                         : LeanPureExtern [.int16, .int16] .int16
-- | lean_int8_of_nat       | def | Int8.ofNat        | (@& Nat) → Int8                                            |
  | lean_int8_of_nat                       : LeanPureExtern [.nat] .int8
-- | lean_int8_dec_le       | def | Int8.decLe        | (a : Int8) → (b : Int8) → Decidable (instLEInt8.le a b)    |
  | lean_int8_dec_le                       : LeanPureExtern [.int8, .int8] .bool
-- | lean_int16_to_int8     | def | Int16.toInt8      | Int16 → Int8                                               |
  | lean_int16_to_int8                     : LeanPureExtern [.int16] .int8
-- | lean_int8_to_int       | def | Int8.toInt        | Int8 → Int                                                 |
  | lean_int8_to_int                       : LeanPureExtern [.int8] .int64
-- | lean_int8_mul          | def | Int8.mul          | Int8 → Int8 → Int8                                         |
  | lean_int8_mul                          : LeanPureExtern [.int8, .int8] .int8
-- | lean_int16_neg         | def | Int16.neg         | Int16 → Int16                                              |
  | lean_int16_neg                         : LeanPureExtern [.int16] .int16
-- | lean_int64_to_int16    | def | Int64.toInt16     | Int64 → Int16                                              |
  | lean_int64_to_int16                    : LeanPureExtern [.int64] .int16
-- | lean_int8_land         | def | Int8.land         | Int8 → Int8 → Int8                                         |
  | lean_int8_land                         : LeanPureExtern [.int8, .int8] .int8
-- | lean_int32_div         | def | Int32.div         | Int32 → Int32 → Int32                                      |
  | lean_int32_div                         : LeanPureExtern [.int32, .int32] .int32
-- | lean_int8_of_int       | def | Int8.ofInt        | (@& Int) → Int8                                            |
  | lean_int8_of_int                       : LeanPureExtern [.int64] .int8
-- | lean_int16_to_isize    | def | Int16.toISize     | Int16 → ISize                                              |
  | lean_int16_to_isize                    : LeanPureExtern [.int16] .isize
-- | lean_int16_sub         | def | Int16.sub         | Int16 → Int16 → Int16                                      |
  | lean_int16_sub                         : LeanPureExtern [.int16, .int16] .int16
-- | lean_int16_to_int64    | def | Int16.toInt64     | Int16 → Int64                                              |
  | lean_int16_to_int64                    : LeanPureExtern [.int16] .int64
-- | lean_int8_lor          | def | Int8.lor          | Int8 → Int8 → Int8                                         |
  | lean_int8_lor                          : LeanPureExtern [.int8, .int8] .int8
-- | lean_int64_shift_right | def | Int64.shiftRight  | Int64 → Int64 → Int64                                      |
  | lean_int64_shift_right                 : LeanPureExtern [.int64, .int64] .int64
--
-- # Init/Data/String/Pattern/Basic.lean
--
-- | name of extern     | def | full name of func                       | type of func                                                                                                                                                                                                                                               |
-- | ------------------ | --- | --------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
-- | lean_string_memcmp | def | String.Slice.Pattern.Internal.memcmpStr | (lhs : @& String) → (rhs : @& String) → (lstart : @& String.Pos.Raw) → (rstart : @& String.Pos.Raw) → (len : @& String.Pos.Raw) → String.instLERaw.le (len.offsetBy lstart) lhs.rawEndPos → String.instLERaw.le (len.offsetBy rstart) rhs.rawEndPos → Bool |
  | lean_string_memcmp                     : LeanPureExtern [.string, .string, .stringPos, .stringPos, .stringPos] .bool
--
-- # Init/Data/String/Slice.lean
--
-- | name of extern    | def | full name of func            | type of func                                                                           |
-- | ----------------- | --- | ---------------------------- | -------------------------------------------------------------------------------------- |
-- | lean_slice_dec_lt | def | String.Slice.instDecidableLt | (x : @& String.Slice) → (y : @& String.Slice) → Decidable (String.Slice.instLT.lt x y) |
  | lean_slice_dec_lt                      : LeanPureExtern [.stringSlice, .stringSlice] .bool
-- | lean_slice_hash   | def | String.Slice.hash            | (@& String.Slice) → UInt64                                                             |
  | lean_slice_hash                        : LeanPureExtern [.stringSlice] .uint64
--
-- # Init/Data/String/Modify.lean
--
-- | name of extern       | def | full name of func  | type of func                                               |
-- | -------------------- | --- | ------------------ | ---------------------------------------------------------- |
-- | lean_string_utf8_set | def | String.Pos.Raw.set | String → (@& String.Pos.Raw) → Char → String               |
  | lean_string_pos_raw_set                : LeanPureExtern [.string, .stringPos, .char] .string
-- |                      |     | String.Pos.set     | {s : String} → (p : s.Pos) → Char → Ne p s.endPos → String |
  | lean_string_pos_set                    : LeanPureExtern [.string, .stringPos, .char] .string
-- |                      |     | String.set         | String → (@& String.Pos.Raw) → Char → String               |
  | lean_string_set                        : LeanPureExtern [.string, .stringPos, .char] .string
--
-- # Init/Data/Float/Float.lean
--
-- | name of extern       | def         | full name of func | type of func                                               |
-- | -------------------- | ----------- | ----------------- | ---------------------------------------------------------- |
-- | lean_float_frexp     | opaque      | Float.frExp       | Float → Prod Float Int                                     |
  | lean_float_frexp                       : LeanPureExtern [.float] (.prod .float .int64)
-- | lean_uint8_to_float  | def         | UInt8.toFloat     | UInt8 → Float                                              |
  | lean_uint8_to_float                    : LeanPureExtern [.uint8] .float
-- | lean_float_to_bits   | def         | Float.toModel     | Float → Float.Model                                        |
  | lean_float_to_model                    : LeanPureExtern [.float] .uint64
-- |                      |             | Float.toBits      | Float → UInt64                                             |
  | lean_float_to_bits                     : LeanPureExtern [.float] .uint64
-- | lean_float_of_bits   | def         | Float.ofBits      | UInt64 → Float                                             |
  | lean_float_of_bits                     : LeanPureExtern [.uint64] .float
-- |                      | constructor | Float.ofModel     | Float.Model → Float                                        |
  | lean_float_of_model                    : LeanPureExtern [.uint64] .float
-- | lean_float_isnan     | def         | Float.isNaN       | Float → Bool                                               |
  | lean_float_isnan                       : LeanPureExtern [.float] .bool
-- | log10                | opaque      | Float.log10       | Float → Float                                              |
  | log10                                  : LeanPureExtern [.float] .float
-- | cbrt                 | opaque      | Float.cbrt        | Float → Float                                              |
  | cbrt                                   : LeanPureExtern [.float] .float
-- | log                  | opaque      | Float.log         | Float → Float                                              |
  | log                                    : LeanPureExtern [.float] .float
-- | lean_float_div       | def         | Float.div         | Float → Float → Float                                      |
  | lean_float_div                         : LeanPureExtern [.float, .float] .float
-- | lean_float_beq       | def         | Float.beq         | Float → Float → Bool                                       |
  | lean_float_beq                         : LeanPureExtern [.float, .float] .bool
-- | tan                  | opaque      | Float.tan         | Float → Float                                              |
  | tan                                    : LeanPureExtern [.float] .float
-- | tanh                 | opaque      | Float.tanh        | Float → Float                                              |
  | tanh                                   : LeanPureExtern [.float] .float
-- | exp2                 | opaque      | Float.exp2        | Float → Float                                              |
  | exp2                                   : LeanPureExtern [.float] .float
-- | lean_float_to_uint16 | def         | Float.toUInt16    | Float → UInt16                                             |
  | lean_float_to_uint16                   : LeanPureExtern [.float] .uint16
-- | lean_uint32_to_float | def         | UInt32.toFloat    | UInt32 → Float                                             |
  | lean_uint32_to_float                   : LeanPureExtern [.uint32] .float
-- | lean_float_decLe     | def         | Float.decLe       | (a : Float) → (b : Float) → Decidable (instLEFloat.le a b) |
  | lean_float_decLe                       : LeanPureExtern [.float, .float] .bool
-- |                      |             | Float.le          | Float → Float → Bool                                       |
  | lean_float_le                          : LeanPureExtern [.float, .float] .bool
-- | lean_float_to_uint64 | def         | Float.toUInt64    | Float → UInt64                                             |
  | lean_float_to_uint64                   : LeanPureExtern [.float] .uint64
-- | sqrt                 | def         | Float.sqrt        | Float → Float                                              |
  | sqrt                                   : LeanPureExtern [.float] .float
-- | acos                 | opaque      | Float.acos        | Float → Float                                              |
  | acos                                   : LeanPureExtern [.float] .float
-- | atan                 | opaque      | Float.atan        | Float → Float                                              |
  | atan                                   : LeanPureExtern [.float] .float
-- | acosh                | opaque      | Float.acosh       | Float → Float                                              |
  | acosh                                  : LeanPureExtern [.float] .float
-- | floor                | opaque      | Float.floor       | Float → Float                                              |
  | floor                                  : LeanPureExtern [.float] .float
-- | fabs                 | def         | Float.abs         | Float → Float                                              |
  | fabs                                   : LeanPureExtern [.float] .float
-- | lean_float_to_uint32 | def         | Float.toUInt32    | Float → UInt32                                             |
  | lean_float_to_uint32                   : LeanPureExtern [.float] .uint32
-- | lean_float_to_string | opaque      | Float.toString    | Float → String                                             |
  | lean_float_to_string                   : LeanPureExtern [.float] .string
-- | lean_uint64_to_float | def         | UInt64.toFloat    | UInt64 → Float                                             |
  | lean_uint64_to_float                   : LeanPureExtern [.uint64] .float
-- | lean_float_decLt     | def         | Float.decLt       | (a : Float) → (b : Float) → Decidable (instLTFloat.lt a b) |
  | lean_float_decLt                       : LeanPureExtern [.float, .float] .bool
-- |                      |             | Float.lt          | Float → Float → Bool                                       |
  | lean_float_lt                          : LeanPureExtern [.float, .float] .bool
-- | lean_float_to_uint8  | def         | Float.toUInt8     | Float → UInt8                                              |
  | lean_float_to_uint8                    : LeanPureExtern [.float] .uint8
-- | sin                  | opaque      | Float.sin         | Float → Float                                              |
  | sin                                    : LeanPureExtern [.float] .float
-- | lean_usize_to_float  | def         | USize.toFloat     | USize → Float                                              |
  | lean_usize_to_float                    : LeanPureExtern [.usize] .float
-- | cosh                 | opaque      | Float.cosh        | Float → Float                                              |
  | cosh                                   : LeanPureExtern [.float] .float
-- | exp                  | opaque      | Float.exp         | Float → Float                                              |
  | exp                                    : LeanPureExtern [.float] .float
-- | ceil                 | opaque      | Float.ceil        | Float → Float                                              |
  | ceil                                   : LeanPureExtern [.float] .float
-- | lean_float_to_usize  | def         | Float.toUSize     | Float → USize                                              |
  | lean_float_to_usize                    : LeanPureExtern [.float] .usize
-- | lean_float_isfinite  | def         | Float.isFinite    | Float → Bool                                               |
  | lean_float_isfinite                    : LeanPureExtern [.float] .bool
-- | round                | opaque      | Float.round       | Float → Float                                              |
  | round                                  : LeanPureExtern [.float] .float
-- | cos                  | opaque      | Float.cos         | Float → Float                                              |
  | cos                                    : LeanPureExtern [.float] .float
-- | log2                 | opaque      | Float.log2        | Float → Float                                              |
  | log2                                   : LeanPureExtern [.float] .float
-- | atanh                | opaque      | Float.atanh       | Float → Float                                              |
  | atanh                                  : LeanPureExtern [.float] .float
-- | atan2                | opaque      | Float.atan2       | Float → Float → Float                                      |
  | atan2                                  : LeanPureExtern [.float, .float] .float
-- | sinh                 | opaque      | Float.sinh        | Float → Float                                              |
  | sinh                                   : LeanPureExtern [.float] .float
-- | asinh                | opaque      | Float.asinh       | Float → Float                                              |
  | asinh                                  : LeanPureExtern [.float] .float
-- | lean_float_mul       | def         | Float.mul         | Float → Float → Float                                      |
  | lean_float_mul                         : LeanPureExtern [.float, .float] .float
-- | lean_uint16_to_float | def         | UInt16.toFloat    | UInt16 → Float                                             |
  | lean_uint16_to_float                   : LeanPureExtern [.uint16] .float
-- | asin                 | opaque      | Float.asin        | Float → Float                                              |
  | asin                                   : LeanPureExtern [.float] .float
-- | pow                  | opaque      | Float.pow         | Float → Float → Float                                      |
  | pow                                    : LeanPureExtern [.float, .float] .float
-- | lean_float_scaleb    | opaque      | Float.scaleB      | Float → (@& Int) → Float                                   |
  | lean_float_scaleb                      : LeanPureExtern [.float, .int64] .float
-- | lean_float_add       | def         | Float.add         | Float → Float → Float                                      |
  | lean_float_add                         : LeanPureExtern [.float, .float] .float
-- | lean_float_sub       | def         | Float.sub         | Float → Float → Float                                      |
  | lean_float_sub                         : LeanPureExtern [.float, .float] .float
-- | lean_float_negate    | def         | Float.neg         | Float → Float                                              |
  | lean_float_negate                      : LeanPureExtern [.float] .float
-- | lean_float_isinf     | def         | Float.isInf       | Float → Bool                                               |
  | lean_float_isinf                       : LeanPureExtern [.float] .bool
--
-- # Init/Data/FloatArray/Basic.lean
--
-- | name of extern            | def         | full name of func            | type of func                                                                                                          |
-- | ------------------------- | ----------- | ---------------------------- | --------------------------------------------------------------------------------------------------------------------- |
-- | lean_mk_empty_float_array | def         | FloatArray.emptyWithCapacity | (@& Nat) → FloatArray                                                                                                 |
  | lean_mk_empty_float_array              : LeanPureExtern [.nat] .floatArray
-- | lean_float_array_get      | def         | FloatArray.get!              | (@& FloatArray) → (@& Nat) → Float                                                                                    |
  | lean_float_array_get                   : LeanPureExtern [.floatArray, .nat] .float
-- | lean_float_array_uget     | def         | FloatArray.uget              | (a : @& FloatArray) → (i : USize) → instLTNat.lt i.toNat a.size → Float                                               |
  | lean_float_array_uget                  : LeanPureExtern [.floatArray, .usize] .float
-- | lean_float_array_fset     | def         | FloatArray.set               | (ds : FloatArray) → (i : @& Nat) → Float → autoParam (instLTNat.lt i ds.size) FloatArray.set._auto_1 → FloatArray     |
  | lean_float_array_fset                  : LeanPureExtern [.floatArray, .nat, .float] .floatArray
-- | lean_float_array_uset     | def         | FloatArray.uset              | (a : FloatArray) → (i : USize) → Float → autoParam (instLTNat.lt i.toNat a.size) FloatArray.uset._auto_1 → FloatArray |
  | lean_float_array_uset                  : LeanPureExtern [.floatArray, .usize, .float] .floatArray
-- | lean_float_array_fget     | def         | FloatArray.get               | (ds : @& FloatArray) → (i : @& Nat) → autoParam (instLTNat.lt i ds.size) FloatArray.get._auto_1 → Float               |
  | lean_float_array_fget                  : LeanPureExtern [.floatArray, .nat] .float
-- | lean_float_array_set      | def         | FloatArray.set!              | FloatArray → (@& Nat) → Float → FloatArray                                                                            |
  | lean_float_array_set                   : LeanPureExtern [.floatArray, .nat, .float] .floatArray
-- | lean_float_array_data     | def         | FloatArray.data              | FloatArray → Array Float                                                                                              |
  | lean_float_array_data                  : LeanPureExtern [.floatArray] (.array .float)
-- | lean_sarray_size          | def         | FloatArray.usize             | (@& FloatArray) → USize                                                                                               |
  | lean_float_array_usize                 : LeanPureExtern [.floatArray] .usize
-- | lean_float_array_mk       | constructor | FloatArray.mk                | Array Float → FloatArray                                                                                              |
  | lean_float_array_mk                    : LeanPureExtern [.array .float] .floatArray
-- | lean_float_array_size     | def         | FloatArray.size              | (@& FloatArray) → Nat                                                                                                 |
  | lean_float_array_size                  : LeanPureExtern [.floatArray] .nat
-- | lean_float_array_push     | def         | FloatArray.push              | FloatArray → Float → FloatArray                                                                                       |
  | lean_float_array_push                  : LeanPureExtern [.floatArray, .float] .floatArray
--
-- # Init/Data/UInt/Log2.lean
--
-- | name of extern   | def | full name of func | type of func    |
-- | ---------------- | --- | ----------------- | --------------- |
-- | lean_usize_log2  | def | USize.log2        | USize → USize   |
  | lean_usize_log2                  : LeanPureExtern [.usize] .usize
-- | lean_uint16_log2 | def | UInt16.log2       | UInt16 → UInt16 |
  | lean_uint16_log2                 : LeanPureExtern [.uint16] .uint16
-- | lean_uint64_log2 | def | UInt64.log2       | UInt64 → UInt64 |
  | lean_uint64_log2                 : LeanPureExtern [.uint64] .uint64
-- | lean_uint8_log2  | def | UInt8.log2        | UInt8 → UInt8   |
  | lean_uint8_log2                  : LeanPureExtern [.uint8] .uint8
-- | lean_uint32_log2 | def | UInt32.log2       | UInt32 → UInt32 |
  | lean_uint32_log2                 : LeanPureExtern [.uint32] .uint32
--
-- # Init/Data/SInt/Float.lean
--
-- | name of extern      | def | full name of func | type of func  |
-- | ------------------- | --- | ----------------- | ------------- |
-- | lean_int32_to_float | def | Int32.toFloat     | Int32 → Float |
  | lean_int32_to_float              : LeanPureExtern [.int32] .float
-- | lean_float_to_int16 | def | Float.toInt16     | Float → Int16 |
  | lean_float_to_int16              : LeanPureExtern [.float] .int16
-- | lean_int16_to_float | def | Int16.toFloat     | Int16 → Float |
  | lean_int16_to_float              : LeanPureExtern [.int16] .float
-- | lean_float_to_int32 | def | Float.toInt32     | Float → Int32 |
  | lean_float_to_int32              : LeanPureExtern [.float] .int32
-- | lean_isize_to_float | def | ISize.toFloat     | ISize → Float |
  | lean_isize_to_float              : LeanPureExtern [.isize] .float
-- | lean_int8_to_float  | def | Int8.toFloat      | Int8 → Float  |
  | lean_int8_to_float               : LeanPureExtern [.int8] .float
-- | lean_float_to_int8  | def | Float.toInt8      | Float → Int8  |
  | lean_float_to_int8               : LeanPureExtern [.float] .int8
-- | lean_int64_to_float | def | Int64.toFloat     | Int64 → Float |
  | lean_int64_to_float              : LeanPureExtern [.int64] .float
-- | lean_float_to_int64 | def | Float.toInt64     | Float → Int64 |
  | lean_float_to_int64              : LeanPureExtern [.float] .int64
-- | lean_float_to_isize | def | Float.toISize     | Float → ISize |
  | lean_float_to_isize              : LeanPureExtern [.float] .isize
--
-- # Init/Data/Float/Float32.lean
--
-- | name of extern         | def         | full name of func | type of func                                                     |
-- | ---------------------- | ----------- | ----------------- | ---------------------------------------------------------------- |
-- | tanhf                  | opaque      | Float32.tanh      | Float32 → Float32                                                |
  | tanhf                           : LeanPureExtern [.float32] .float32
-- | exp2f                  | opaque      | Float32.exp2      | Float32 → Float32                                                |
  | exp2f                           : LeanPureExtern [.float32] .float32
-- | lean_float32_div       | def         | Float32.div       | Float32 → Float32 → Float32                                      |
  | lean_float32_div                : LeanPureExtern [.float32, .float32] .float32
-- | logf                   | opaque      | Float32.log       | Float32 → Float32                                                |
  | logf                            : LeanPureExtern [.float32] .float32
-- | lean_float32_decLe     | def         | Float32.le        | Float32 → Float32 → Bool                                         |
  | lean_float32_le                 : LeanPureExtern [.float32, .float32] .bool
-- |                        |             | Float32.decLe     | (a : Float32) → (b : Float32) → Decidable (instLEFloat32.le a b) |
  | lean_float32_decLe              : LeanPureExtern [.float32, .float32] .bool
-- | lean_float_to_float32  | opaque      | Float.toFloat32   | Float → Float32                                                  |
  | lean_float_to_float32           : LeanPureExtern [.float] .float32
-- | lean_float32_to_bits   | def         | Float32.toModel   | Float32 → Float32.Model                                          |
  | lean_float32_to_model          : LeanPureExtern [.float32] .uint32
-- |                        |             | Float32.toBits    | Float32 → UInt32                                                 |
  | lean_float32_to_bits           : LeanPureExtern [.float32] .uint32
-- | lean_float32_of_bits   | def         | Float32.ofBits    | UInt32 → Float32                                                 |
  | lean_float32_of_bits           : LeanPureExtern [.uint32] .float32
-- |                        | constructor | Float32.ofModel   | Float32.Model → Float32                                          |
  | lean_float32_of_model          : LeanPureExtern [.uint32] .float32
-- | atanf                  | opaque      | Float32.atan      | Float32 → Float32                                                |
  | atanf                           : LeanPureExtern [.float32] .float32
-- | acoshf                 | opaque      | Float32.acosh     | Float32 → Float32                                                |
  | acoshf                          : LeanPureExtern [.float32] .float32
-- | lean_float32_frexp     | opaque      | Float32.frExp     | Float32 → Prod Float32 Int                                       |
  | lean_float32_frexp             : LeanPureExtern [.float32] (.prod .float32 .int64)
-- | lean_float32_to_uint64 | def         | Float32.toUInt64  | Float32 → UInt64                                                 |
  | lean_float32_to_uint64          : LeanPureExtern [.float32] .uint64
-- | lean_float32_sub       | def         | Float32.sub       | Float32 → Float32 → Float32                                      |
  | lean_float32_sub                : LeanPureExtern [.float32, .float32] .float32
-- | lean_float32_to_uint16 | def         | Float32.toUInt16  | Float32 → UInt16                                                 |
  | lean_float32_to_uint16          : LeanPureExtern [.float32] .uint16
-- | lean_usize_to_float32  | def         | USize.toFloat32   | USize → Float32                                                  |
  | lean_usize_to_float32           : LeanPureExtern [.usize] .float32
-- | asinf                  | opaque      | Float32.asin      | Float32 → Float32                                                |
  | asinf                           : LeanPureExtern [.float32] .float32
-- | powf                   | opaque      | Float32.pow       | Float32 → Float32 → Float32                                      |
  | powf                            : LeanPureExtern [.float32, .float32] .float32
-- | lean_float32_beq       | def         | Float32.beq       | Float32 → Float32 → Bool                                         |
  | lean_float32_beq                : LeanPureExtern [.float32, .float32] .bool
-- | lean_uint8_to_float32  | def         | UInt8.toFloat32   | UInt8 → Float32                                                  |
  | lean_uint8_to_float32           : LeanPureExtern [.uint8] .float32
-- | tanf                   | opaque      | Float32.tan       | Float32 → Float32                                                |
  | tanf                            : LeanPureExtern [.float32] .float32
-- | lean_float32_to_float  | opaque      | Float32.toFloat   | Float32 → Float                                                  |
  | lean_float32_to_float           : LeanPureExtern [.float32] .float
-- | lean_float32_isnan     | def         | Float32.isNaN     | Float32 → Bool                                                   |
  | lean_float32_isnan              : LeanPureExtern [.float32] .bool
-- | log10f                 | opaque      | Float32.log10     | Float32 → Float32                                                |
  | log10f                          : LeanPureExtern [.float32] .float32
-- | cbrtf                  | opaque      | Float32.cbrt      | Float32 → Float32                                                |
  | cbrtf                           : LeanPureExtern [.float32] .float32
-- | atan2f                 | opaque      | Float32.atan2     | Float32 → Float32 → Float32                                      |
  | atan2f                          : LeanPureExtern [.float32, .float32] .float32
-- | sinhf                  | opaque      | Float32.sinh      | Float32 → Float32                                                |
  | sinhf                           : LeanPureExtern [.float32] .float32
-- | cosf                   | opaque      | Float32.cos       | Float32 → Float32                                                |
  | cosf                            : LeanPureExtern [.float32] .float32
-- | lean_uint32_to_float32 | def         | UInt32.toFloat32  | UInt32 → Float32                                                 |
  | lean_uint32_to_float32          : LeanPureExtern [.uint32] .float32
-- | lean_float32_isinf     | def         | Float32.isInf     | Float32 → Bool                                                   |
  | lean_float32_isinf              : LeanPureExtern [.float32] .bool
-- | lean_float32_negate    | def         | Float32.neg       | Float32 → Float32                                                |
  | lean_float32_negate             : LeanPureExtern [.float32] .float32
-- | lean_float32_to_usize  | def         | Float32.toUSize   | Float32 → USize                                                  |
  | lean_float32_to_usize           : LeanPureExtern [.float32] .usize
-- | ceilf                  | opaque      | Float32.ceil      | Float32 → Float32                                                |
  | ceilf                           : LeanPureExtern [.float32] .float32
-- | lean_float32_isfinite  | def         | Float32.isFinite  | Float32 → Bool                                                   |
  | lean_float32_isfinite           : LeanPureExtern [.float32] .bool
-- | lean_float32_add       | def         | Float32.add       | Float32 → Float32 → Float32                                      |
  | lean_float32_add                : LeanPureExtern [.float32, .float32] .float32
-- | lean_float32_scaleb    | opaque      | Float32.scaleB    | Float32 → (@& Int) → Float32                                     |
  | lean_float32_scaleb             : LeanPureExtern [.float32, .int64] .float32
-- | sinf                   | opaque      | Float32.sin       | Float32 → Float32                                                |
  | sinf                            : LeanPureExtern [.float32] .float32
-- | lean_float32_mul       | def         | Float32.mul       | Float32 → Float32 → Float32                                      |
  | lean_float32_mul                : LeanPureExtern [.float32, .float32] .float32
-- | lean_float32_to_string | opaque      | Float32.toString  | Float32 → String                                                 |
  | lean_float32_to_string          : LeanPureExtern [.float32] .string
-- | asinhf                 | opaque      | Float32.asinh     | Float32 → Float32                                                |
  | asinhf                          : LeanPureExtern [.float32] .float32
-- | lean_float32_to_uint32 | def         | Float32.toUInt32  | Float32 → UInt32                                                 |
  | lean_float32_to_uint32          : LeanPureExtern [.float32] .uint32
-- | log2f                  | opaque      | Float32.log2      | Float32 → Float32                                                |
  | log2f                           : LeanPureExtern [.float32] .float32
-- | lean_uint64_to_float32 | def         | UInt64.toFloat32  | UInt64 → Float32                                                 |
  | lean_uint64_to_float32          : LeanPureExtern [.uint64] .float32
-- | atanhf                 | opaque      | Float32.atanh     | Float32 → Float32                                                |
  | atanhf                          : LeanPureExtern [.float32] .float32
-- | floorf                 | opaque      | Float32.floor     | Float32 → Float32                                                |
  | floorf                          : LeanPureExtern [.float32] .float32
-- | fabsf                  | def         | Float32.abs       | Float32 → Float32                                                |
  | fabsf                           : LeanPureExtern [.float32] .float32
-- | roundf                 | opaque      | Float32.round     | Float32 → Float32                                                |
  | roundf                          : LeanPureExtern [.float32] .float32
-- | lean_float32_decLt     | def         | Float32.lt        | Float32 → Float32 → Bool                                         |
  | lean_float32_lt                 : LeanPureExtern [.float32, .float32] .bool
-- |                        |             | Float32.decLt     | (a : Float32) → (b : Float32) → Decidable (instLTFloat32.lt a b) |
  | lean_float32_decLt              : LeanPureExtern [.float32, .float32] .bool
-- | acosf                  | opaque      | Float32.acos      | Float32 → Float32                                                |
  | acosf                           : LeanPureExtern [.float32] .float32
-- | sqrtf                  | def         | Float32.sqrt      | Float32 → Float32                                                |
  | sqrtf                           : LeanPureExtern [.float32] .float32
-- | lean_uint16_to_float32 | def         | UInt16.toFloat32  | UInt16 → Float32                                                 |
  | lean_uint16_to_float32          : LeanPureExtern [.uint16] .float32
-- | coshf                  | opaque      | Float32.cosh      | Float32 → Float32                                                |
  | coshf                           : LeanPureExtern [.float32] .float32
-- | expf                   | opaque      | Float32.exp       | Float32 → Float32                                                |
  | expf                            : LeanPureExtern [.float32] .float32
-- | lean_float32_to_uint8  | def         | Float32.toUInt8   | Float32 → UInt8                                                  |
  | lean_float32_to_uint8           : LeanPureExtern [.float32] .uint8
--
-- # Init/Data/SInt/Float32.lean
--
-- | name of extern        | def | full name of func | type of func    |
-- | --------------------- | --- | ----------------- | --------------- |
-- | lean_float32_to_int64 | def | Float32.toInt64   | Float32 → Int64 |
  | lean_float32_to_int64          : LeanPureExtern [.float32] .int64
-- | lean_float32_to_isize | def | Float32.toISize   | Float32 → ISize |
  | lean_float32_to_isize          : LeanPureExtern [.float32] .isize
-- | lean_int32_to_float32 | def | Int32.toFloat32   | Int32 → Float32 |
  | lean_int32_to_float32          : LeanPureExtern [.int32] .float32
-- | lean_float32_to_int8  | def | Float32.toInt8    | Float32 → Int8  |
  | lean_float32_to_int8           : LeanPureExtern [.float32] .int8
-- | lean_float32_to_int16 | def | Float32.toInt16   | Float32 → Int16 |
  | lean_float32_to_int16          : LeanPureExtern [.float32] .int16
-- | lean_isize_to_float32 | def | ISize.toFloat32   | ISize → Float32 |
  | lean_isize_to_float32          : LeanPureExtern [.isize] .float32
-- | lean_int8_to_float32  | def | Int8.toFloat32    | Int8 → Float32  |
  | lean_int8_to_float32           : LeanPureExtern [.int8] .float32
-- | lean_float32_to_int32 | def | Float32.toInt32   | Float32 → Int32 |
  | lean_float32_to_int32          : LeanPureExtern [.float32] .int32
-- | lean_int16_to_float32 | def | Int16.toFloat32   | Int16 → Float32 |
  | lean_int16_to_float32          : LeanPureExtern [.int16] .float32
-- | lean_int64_to_float32 | def | Int64.toFloat32   | Int64 → Float32 |
  | lean_int64_to_float32          : LeanPureExtern [.int64] .float32
--
-- # Init/Data/Ord/String.lean
--
-- | name of extern      | def | full name of func | type of func                         |
-- | ------------------- | --- | ----------------- | ------------------------------------ |
-- | lean_string_compare | def | String.compare    | (@& String) → (@& String) → Ordering |
  | lean_string_compare             : LeanPureExtern [.string, .string] .ordering
--
-- # Init/System/IO.lean
--
-- | name of extern            | def    | full name of func    | type of func                                                      |
-- | ------------------------- | ------ | -------------------- | ----------------------------------------------------------------- |
-- | lean_io_process_child_pid | opaque | IO.Process.Child.pid | {cfg : @& IO.Process.StdioConfig} → IO.Process.Child cfg → UInt32 |
  | lean_io_process_child_pid       : LeanPureExtern [.childProcess] .uint32
--
-- # Init/System/Promise.lean
--
-- | name of extern             | def    | full name of func                                    | type of func                                     |
-- | -------------------------- | ------ | ---------------------------------------------------- | ------------------------------------------------ |
--
-- # Init/ShareCommon.lean
--
-- | name of extern         | def    | full name of func             | type of func                                                                                                |
-- | ---------------------- | ------ | ----------------------------- | ----------------------------------------------------------------------------------------------------------- |
-- | lean_sharecommon_eq    | opaque | ShareCommon.Object.eq         | (@& ShareCommon.Object) → (@& ShareCommon.Object) → Bool                                                    |
  | lean_sharecommon_eq             : LeanPureExtern [.shareCommonObject, .shareCommonObject] .bool
-- | lean_sharecommon_hash  | opaque | ShareCommon.Object.hash       | (@& ShareCommon.Object) → UInt64                                                                            |
  | lean_sharecommon_hash           : LeanPureExtern [.shareCommonObject] .uint64

end LakeJs.LeanImpureExtern
