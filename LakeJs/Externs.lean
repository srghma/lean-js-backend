module
-- public import LakeJs.Ty
public import LakeJs.LeanPrimTy
public import LakeJs.LeanPrimTyCovariant
@[expose] public section
namespace LakeJs

abbrev T := LeanPrimTy
abbrev CT := LeanPrimTyCovariant LeanPrimTy

inductive ExternLazy : T → Type where
  | lean_system_platform_nbits      : ExternLazy .nat
  | lean_version_get_special_desc     : ExternLazy .string
  | lean_version_get_is_release       : ExternLazy .bool
  | lean_version_get_major            : ExternLazy .nat
  | lean_version_get_patch            : ExternLazy .nat
  | lean_internal_is_stage0           : ExternLazy .bool
  | lean_version_get_minor            : ExternLazy .nat
  | lean_get_githash                  : ExternLazy .string
  | lean_internal_has_llvm_backend   : ExternLazy .bool
  | lean_system_platform_emscripten        : ExternLazy .bool
  | lean_system_platform_target            : ExternLazy .string
  | lean_system_platform_windows           : ExternLazy .bool
  | lean_system_platform_osx               : ExternLazy .bool
  | lean_internal_get_hardware_concurrency : ExternLazy .uint32
  | lean_system_platform_linux             : ExternLazy .bool

section

variable {X : Type}
  (v : LeanPrimTy → X)
  (c : LeanPrimTyCovariant LeanPrimTy → X)
  (C : LeanPrimTyCovariant X → X)
  (option : X → X)
  (fn1 : LeanPrimTy → LeanPrimTy → X)

-- Scoped/local coercion using `v` only within this section:
local instance : Coe LeanPrimTy X := ⟨v⟩

-- You can even do the same for `c` and `C` if desired:
local instance : Coe (LeanPrimTyCovariant LeanPrimTy) X := ⟨c⟩
local instance : Coe (LeanPrimTyCovariant X) X := ⟨C⟩

open LeanPrimTy
open LeanPrimTyCovariant

inductive Extern1 : X → X → Type where
  | lean_sorry                      : (α : X) → Extern1 (bool) α
  | lean_array_get_size             : (α : X) → Extern1 (.array α) .nat
  | lean_array_to_list              : (α : X) → Extern1 (.array α) (.list α)
  | lean_empty_array_with_capacity  : (α : X) → Extern1 .nat (.array α)
  | lean_array_mk_empty             : (α : X) → Extern1 .nat (.array α)
  | lean_panic_fn_borrowed          : (α : X) → Extern1 .string α
  | lean_array_mk                   : (α : X) → Extern1 (.list α) (.array α)
  | lean_thunk_pure                  : (α : X) → Extern1 α (.thunk α)
  | lean_mk_thunk                    : (α : X) → Extern1 (.lazy α) (.thunk α)
  | lean_task_get_own                : (α : X) → Extern1 (.task α) α
  | lean_task_pure                   : (α : X) → Extern1 α (.task α)
  | lean_thunk_get_own               : (α : X) → Extern1 (.thunk α) α
  | lean_ptr_addr                     : (α : X) → Extern1 α .usize
  | lean_dbg_stack_trace              : (α : X) → Extern1 (.lazy α) α
  | lean_is_exclusive_obj             : (α : X) → Extern1 α .bool
  | lean_array_pop                    : (α : X) → Extern1 (.array α) (.array α)
  | lean_array_size                   : (α : X) → Extern1 (.array α) .usize
  | lean_io_promise_result_opt      : (α : X) → Extern1 (.promise α) (.task (.option α))
  | lean_option_get_or_block        : (α : X) → Extern1 (.option α) α
  | lean_sharecommon_quick          : (α : X) → Extern1 α α
  | lean_uint32_of_nat_mk           : Extern1 (.bitvec 32) .uint32
  | lean_byte_array_size            : Extern1 .byteArray .nat
  | lean_string_to_utf8             : Extern1 .string .byteArray
  | lean_uint32_of_nat_lt           : Extern1 .nat .uint32
  | lean_char_of_nat_aux            : Extern1 .nat .char
  | lean_uint8_to_bitvec            : Extern1 .uint8 (.bitvec 8)
  | lean_string_from_utf8_unchecked : Extern1 .byteArray .string
  | lean_byte_array_mk              : Extern1 (.array .uint8) .byteArray
  | lean_byte_array_data            : Extern1 .byteArray (.array .uint8)
  | lean_uint8_of_nat               : Extern1 .nat .uint8
  | lean_uint8_of_nat_lt            : Extern1 .nat .uint8
  | lean_uint16_to_bitvec           : Extern1 .uint16 (.bitvec 16)
  | lean_uint16_of_nat_mk           : Extern1 (.bitvec 16) .uint16
  | lean_nat_pred                   : Extern1 .nat .nat
  | lean_usize_of_nat_lt            : Extern1 .nat .usize
  | lean_string_mk                  : Extern1 (.list .char) .string
  | lean_string_hash                : Extern1 .string .uint64
  | lean_uint64_to_bitvec           : Extern1 .uint64 (.bitvec 64)
  | lean_uint64_of_nat_mk           : Extern1 (.bitvec 64) .uint64
  | lean_uint32_to_nat              : Extern1 .uint32 .nat
  | lean_uint32_to_bitvec           : Extern1 .uint32 (.bitvec 32)
  | lean_uint16_of_nat_lt           : Extern1 .nat .uint16
  | lean_uint8_of_nat_mk            : Extern1 (.bitvec 8) .uint8
  | lean_mk_empty_byte_array        : Extern1 .nat .byteArray
  | lean_usize_of_nat_mk            : Extern1 (.bitvec 64) .usize
  | lean_usize_to_bitvec            : Extern1 .usize (.bitvec 64)
  | lean_string_utf8_byte_size      : Extern1 .string .nat
  | lean_uint64_of_nat_lt           : Extern1 .nat .uint64
  | lean_nat_to_int          : Extern1 .nat .int
  | lean_int_to_nat          : Extern1 .int .nat
  | lean_int_dec_nonneg      : Extern1 .int .bool
  | lean_int_neg_succ_of_nat : Extern1 .nat .int
  | lean_int_neg             : Extern1 .int .int
  | lean_nat_abs             : Extern1 .int .nat
  | lean_uint64_to_nat    : Extern1 .uint64 .nat
  | lean_uint32_to_uint8  : Extern1 .uint32 .uint8
  | lean_usize_to_nat     : Extern1 .usize .nat
  | lean_uint64_to_uint32 : Extern1 .uint64 .uint32
  | lean_uint32_to_uint16 : Extern1 .uint32 .uint16
  | lean_uint16_to_uint32 : Extern1 .uint16 .uint32
  | lean_uint32_to_uint64 : Extern1 .uint32 .uint64
  | lean_uint32_of_nat    : Extern1 .nat .uint32
  | lean_uint16_to_nat    : Extern1 .uint16 .nat
  | lean_uint16_to_uint8  : Extern1 .uint16 .uint8
  | lean_usize_of_nat     : Extern1 .nat .usize
  | lean_uint8_to_uint64  : Extern1 .uint8 .uint64
  | lean_uint8_to_nat     : Extern1 .uint8 .nat
  | lean_uint64_of_nat    : Extern1 .nat .uint64
  | lean_uint8_to_uint32  : Extern1 .uint8 .uint32
  | lean_uint16_of_nat    : Extern1 .nat .uint16
  | lean_uint16_to_uint64 : Extern1 .uint16 .uint64
  | lean_uint64_to_uint8  : Extern1 .uint64 .uint8
  | lean_uint64_to_uint16 : Extern1 .uint64 .uint16
  | lean_uint8_to_uint16  : Extern1 .uint8 .uint16
  | lean_string_trim           : Extern1 .string .string
  | lean_substring_tostring    : Extern1 .substring .string
  | lean_string_isempty        : Extern1 .string .bool
  | lean_string_front          : Extern1 .string .char
  | lean_string_length         : Extern1 .string .nat
  | lean_string_mk_def         : Extern1 (.list .char) .string
  | lean_string_capitalize     : Extern1 .string .string
  | lean_substring_front       : Extern1 .substring .char
  | lean_substring_isempty     : Extern1 .substring .bool
  | lean_string_of_usize              : Extern1 .usize .string
  | lean_nat_log2                     : Extern1 .nat .nat
  | lean_uint16_neg                   : Extern1 .uint16 .uint16
  | lean_uint16_to_usize              : Extern1 .uint16 .usize
  | lean_uint64_complement            : Extern1 .uint64 .uint64
  | lean_bool_to_uint32               : Extern1 .bool .uint32
  | lean_uint8_neg                    : Extern1 .uint8 .uint8
  | lean_uint16_complement            : Extern1 .uint16 .uint16
  | lean_uint32_neg                   : Extern1 .uint32 .uint32
  | lean_usize_neg                    : Extern1 .usize .usize
  | lean_usize_to_uint64              : Extern1 .usize .uint64
  | lean_bool_to_uint64               : Extern1 .bool .uint64
  | lean_usize_of_nat32               : Extern1 .nat .usize
  | lean_uint64_neg                   : Extern1 .uint64 .uint64
  | lean_uint32_to_usize              : Extern1 .uint32 .usize
  | lean_uint8_complement             : Extern1 .uint8 .uint8
  | lean_usize_to_uint16              : Extern1 .usize .uint16
  | lean_usize_to_uint8               : Extern1 .usize .uint8
  | lean_bool_to_uint8                : Extern1 .bool .uint8
  | lean_uint32_complement            : Extern1 .uint32 .uint32
  | lean_uint8_to_usize               : Extern1 .uint8 .usize
  | lean_bool_to_uint16               : Extern1 .bool .uint16
  | lean_bool_to_usize                : Extern1 .bool .usize
  | lean_uint64_to_usize              : Extern1 .uint64 .usize
  | lean_usize_to_uint32              : Extern1 .usize .uint32
  | lean_usize_complement             : Extern1 .usize .usize
  | lean_byte_array_hash                   : Extern1 .byteArray .uint64
  | lean_sarray_size                       : Extern1 .byteArray .usize
  | lean_string_to_utf8_defs               : Extern1 .string .byteArray
  | lean_string_data                       : Extern1 .string (.list .char)
  | lean_string_to_list                    : Extern1 .string (.list .char)
  | lean_string_validate_utf8              : Extern1 .byteArray .bool
  | lean_string_length_def                 : Extern1 .string .nat
  | lean_isize_complement                  : Extern1 .isize .isize
  | lean_int16_of_nat                      : Extern1 .nat .int16
  | lean_int32_of_int                      : Extern1 .int .int32
  | lean_int64_to_isize                    : Extern1 .int64 .isize
  | lean_isize_to_int8                     : Extern1 .isize .int8
  | lean_int32_of_nat                      : Extern1 .nat .int32
  | lean_int64_to_int8                     : Extern1 .int64 .int8
  | lean_int32_to_int64                    : Extern1 .int32 .int64
  | lean_int8_to_int16                     : Extern1 .int8 .int16
  | lean_int64_of_int                      : Extern1 .int .int64
  | lean_int32_to_isize                    : Extern1 .int32 .isize
  | lean_int32_neg                         : Extern1 .int32 .int32
  | lean_int32_abs                         : Extern1 .int32 .int32
  | lean_bool_to_int8                      : Extern1 .bool .int8
  | lean_isize_to_int16                    : Extern1 .isize .int16
  | lean_int16_to_int                      : Extern1 .int16 .int
  | lean_int8_complement                   : Extern1 .int8 .int8
  | lean_bool_to_int16                     : Extern1 .bool .int16
  | lean_isize_of_int                      : Extern1 .int .isize
  | lean_int16_abs                         : Extern1 .int16 .int16
  | lean_int16_to_int32                    : Extern1 .int16 .int32
  | lean_isize_to_int                      : Extern1 .isize .int
  | lean_isize_of_nat                      : Extern1 .nat .isize
  | lean_int16_complement                  : Extern1 .int16 .int16
  | lean_isize_to_int64                    : Extern1 .isize .int64
  | lean_int64_complement                  : Extern1 .int64 .int64
  | lean_isize_abs                         : Extern1 .isize .isize
  | lean_int16_of_int                      : Extern1 .int .int16
  | lean_int8_neg                          : Extern1 .int8 .int8
  | lean_isize_to_int32                    : Extern1 .isize .int32
  | lean_int64_to_int32                    : Extern1 .int64 .int32
  | lean_int64_abs                         : Extern1 .int64 .int64
  | lean_int32_complement                  : Extern1 .int32 .int32
  | lean_bool_to_int64                     : Extern1 .bool .int64
  | lean_bool_to_isize                     : Extern1 .bool .isize
  | lean_bool_to_int32                     : Extern1 .bool .int32
  | lean_int64_of_nat                      : Extern1 .nat .int64
  | lean_int32_to_int8                     : Extern1 .int32 .int8
  | lean_int64_to_int_sint                 : Extern1 .int64 .int
  | lean_int64_neg                         : Extern1 .int64 .int64
  | lean_int8_abs                          : Extern1 .int8 .int8
  | lean_int8_to_int32                     : Extern1 .int8 .int32
  | lean_isize_neg                         : Extern1 .isize .isize
  | lean_int32_to_int                      : Extern1 .int32 .int
  | lean_int32_to_int16                    : Extern1 .int32 .int16
  | lean_int8_to_int64                     : Extern1 .int8 .int64
  | lean_int8_to_isize                     : Extern1 .int8 .isize
  | lean_int8_of_nat                       : Extern1 .nat .int8
  | lean_int16_to_int8                     : Extern1 .int16 .int8
  | lean_int8_to_int                       : Extern1 .int8 .int
  | lean_int16_neg                         : Extern1 .int16 .int16
  | lean_int64_to_int16                    : Extern1 .int64 .int16
  | lean_int8_of_int                       : Extern1 .int .int8
  | lean_int16_to_isize                    : Extern1 .int16 .isize
  | lean_int16_to_int64                    : Extern1 .int16 .int64
  | lean_slice_hash                        : Extern1 .stringSlice .uint64
  | lean_float_frexp                       : Extern1 .float (.prod .float .int64)
  | lean_uint8_to_float                    : Extern1 .uint8 .float
  | lean_float_to_bits                     : Extern1 .float .uint64
  | lean_float_of_bits                     : Extern1 .uint64 .float
  | lean_float_isnan                       : Extern1 .float .bool
  | log10                                  : Extern1 .float .float
  | cbrt                                   : Extern1 .float .float
  | log                                    : Extern1 .float .float
  | tan                                    : Extern1 .float .float
  | tanh                                   : Extern1 .float .float
  | exp2                                   : Extern1 .float .float
  | lean_float_to_uint16                   : Extern1 .float .uint16
  | lean_uint32_to_float                   : Extern1 .uint32 .float
  | lean_float_to_uint64                   : Extern1 .float .uint64
  | sqrt                                   : Extern1 .float .float
  | acos                                   : Extern1 .float .float
  | atan                                   : Extern1 .float .float
  | acosh                                  : Extern1 .float .float
  | floor                                  : Extern1 .float .float
  | fabs                                   : Extern1 .float .float
  | lean_float_to_uint32                   : Extern1 .float .uint32
  | lean_float_to_string                   : Extern1 .float .string
  | lean_uint64_to_float                   : Extern1 .uint64 .float
  | lean_float_to_uint8                    : Extern1 .float .uint8
  | sin                                    : Extern1 .float .float
  | lean_usize_to_float                    : Extern1 .usize .float
  | cosh                                   : Extern1 .float .float
  | exp                                    : Extern1 .float .float
  | ceil                                   : Extern1 .float .float
  | lean_float_to_usize                    : Extern1 .float .usize
  | lean_float_isfinite                    : Extern1 .float .bool
  | round                                  : Extern1 .float .float
  | cos                                    : Extern1 .float .float
  | log2                                   : Extern1 .float .float
  | atanh                                  : Extern1 .float .float
  | sinh                                   : Extern1 .float .float
  | asinh                                  : Extern1 .float .float
  | lean_uint16_to_float                   : Extern1 .uint16 .float
  | asin                                   : Extern1 .float .float
  | lean_float_negate                      : Extern1 .float .float
  | lean_float_isinf                       : Extern1 .float .bool
  | lean_mk_empty_float_array              : Extern1 .nat .floatArray
  | lean_float_array_data                  : Extern1 .floatArray (.array .float)
  | lean_float_array_usize                 : Extern1 .floatArray .usize
  | lean_float_array_mk                    : Extern1 (.array .float) .floatArray
  | lean_float_array_size                  : Extern1 .floatArray .nat
  | lean_usize_log2                  : Extern1 .usize .usize
  | lean_uint16_log2                 : Extern1 .uint16 .uint16
  | lean_uint64_log2                 : Extern1 .uint64 .uint64
  | lean_uint8_log2                  : Extern1 .uint8 .uint8
  | lean_uint32_log2                 : Extern1 .uint32 .uint32
  | lean_int32_to_float              : Extern1 .int32 .float
  | lean_float_to_int16              : Extern1 .float .int16
  | lean_int16_to_float              : Extern1 .int16 .float
  | lean_float_to_int32              : Extern1 .float .int32
  | lean_isize_to_float              : Extern1 .isize .float
  | lean_int8_to_float               : Extern1 .int8 .float
  | lean_float_to_int8               : Extern1 .float .int8
  | lean_int64_to_float              : Extern1 .int64 .float
  | lean_float_to_int64              : Extern1 .float .int64
  | lean_float_to_isize              : Extern1 .float .isize
  | tanhf                           : Extern1 .float32 .float32
  | exp2f                           : Extern1 .float32 .float32
  | logf                            : Extern1 .float32 .float32
  | lean_float_to_float32           : Extern1 .float .float32
  | lean_float32_to_bits           : Extern1 .float32 .uint32
  | lean_float32_of_bits           : Extern1 .uint32 .float32
  | atanf                           : Extern1 .float32 .float32
  | acoshf                          : Extern1 .float32 .float32
  | lean_float32_frexp             : Extern1 .float32 (.prod .float32 .int64)
  | lean_float32_to_uint64          : Extern1 .float32 .uint64
  | lean_float32_to_uint16          : Extern1 .float32 .uint16
  | lean_usize_to_float32           : Extern1 .usize .float32
  | asinf                           : Extern1 .float32 .float32
  | lean_uint8_to_float32           : Extern1 .uint8 .float32
  | tanf                            : Extern1 .float32 .float32
  | lean_float32_to_float           : Extern1 .float32 .float
  | lean_float32_isnan              : Extern1 .float32 .bool
  | log10f                          : Extern1 .float32 .float32
  | cbrtf                           : Extern1 .float32 .float32
  | sinhf                           : Extern1 .float32 .float32
  | cosf                            : Extern1 .float32 .float32
  | lean_uint32_to_float32          : Extern1 .uint32 .float32
  | lean_float32_isinf              : Extern1 .float32 .bool
  | lean_float32_negate             : Extern1 .float32 .float32
  | lean_float32_to_usize           : Extern1 .float32 .usize
  | ceilf                           : Extern1 .float32 .float32
  | lean_float32_isfinite           : Extern1 .float32 .bool
  | sinf                            : Extern1 .float32 .float32
  | lean_float32_to_string          : Extern1 .float32 .string
  | asinhf                          : Extern1 .float32 .float32
  | lean_float32_to_uint32          : Extern1 .float32 .uint32
  | log2f                           : Extern1 .float32 .float32
  | lean_uint64_to_float32          : Extern1 .uint64 .float32
  | atanhf                          : Extern1 .float32 .float32
  | floorf                          : Extern1 .float32 .float32
  | fabsf                           : Extern1 .float32 .float32
  | roundf                          : Extern1 .float32 .float32
  | acosf                           : Extern1 .float32 .float32
  | sqrtf                           : Extern1 .float32 .float32
  | lean_uint16_to_float32          : Extern1 .uint16 .float32
  | coshf                           : Extern1 .float32 .float32
  | expf                            : Extern1 .float32 .float32
  | lean_float32_to_uint8           : Extern1 .float32 .uint8
  | lean_float32_to_int64          : Extern1 .float32 .int64
  | lean_float32_to_isize          : Extern1 .float32 .isize
  | lean_int32_to_float32          : Extern1 .int32 .float32
  | lean_float32_to_int8           : Extern1 .float32 .int8
  | lean_float32_to_int16          : Extern1 .float32 .int16
  | lean_isize_to_float32          : Extern1 .isize .float32
  | lean_int8_to_float32           : Extern1 .int8 .float32
  | lean_float32_to_int32          : Extern1 .float32 .int32
  | lean_int16_to_float32          : Extern1 .int16 .float32
  | lean_int64_to_float32          : Extern1 .int64 .float32
  | lean_io_process_child_pid       : Extern1 .childProcess .uint32
  | lean_sharecommon_hash           : Extern1 .shareCommonObject .uint64
  | lean_is_scalar                  : (α : X) → Extern1 α .bool
  | lean_float_to_model                    : Extern1 .float .uint64
  | lean_float_of_model                    : Extern1 .uint64 .float
  | lean_float32_to_model          : Extern1 .float32 .uint32
  | lean_float32_of_model          : Extern1 .uint32 .float32

end

inductive Extern2 : Ty → Ty → Ty → Type where
  | lean_array_get_borrowed         : (α : X) → Extern2 (.array α) .nat α
  | lean_array_push                 : (α : X) → Extern2 (.array α) α (.array α)
  | lean_array_fget_borrowed        : (α : X) → Extern2 (.array α) .nat α
  | lean_array_get                  : (α : X) → Extern2 (.array α) .nat α
  | lean_array_fget                 : (α : X) → Extern2 (.array α) .nat α
  | lean_task_spawn                  : (α : X) → Extern2 (.lazy α) .nat (.task α)
  | lean_dbg_sleep                    : (α : X) → Extern2 .uint32 (.lazy α) α
  | lean_dbg_trace                    : (α : X) → Extern2 .string (.lazy α) α
  | lean_dbg_trace_if_shared          : (α : X) → Extern2 .string α α
  | lean_array_uget                   : (α : X) → Extern2 (.array α) .usize α
  | lean_mk_array                     : (α : X) → Extern2 .nat α (.array α)
  | lean_state_sharecommon          : (α : X) → Extern2 .shareCommonState α (.prod α .shareCommonState)
  | lean_uint32_dec_eq              : Extern2 .uint32 .uint32 .bool
  | lean_uint32_dec_lt              : Extern2 .uint32 .uint32 .bool
  | lean_nat_div                    : Extern2 .nat .nat .nat
  | lean_nat_dec_lt                 : Extern2 .nat .nat .bool
  | lean_nat_mod_core               : Extern2 .nat .nat .nat
  | lean_nat_mod                    : Extern2 .nat .nat .nat
  | lean_nat_sub                    : Extern2 .nat .nat .nat
  | lean_uint8_dec_lt               : Extern2 .uint8 .uint8 .bool
  | lean_uint32_dec_le              : Extern2 .uint32 .uint32 .bool
  | lean_nat_dec_eq                 : Extern2 .nat .nat .bool
  | lean_nat_beq                    : Extern2 .nat .nat .bool
  | lean_uint8_dec_le               : Extern2 .uint8 .uint8 .bool
  | lean_nat_ble                    : Extern2 .nat .nat .bool
  | lean_nat_dec_le                 : Extern2 .nat .nat .bool
  | lean_nat_add                    : Extern2 .nat .nat .nat
  | lean_uint16_dec_eq              : Extern2 .uint16 .uint16 .bool
  | lean_string_dec_eq              : Extern2 .string .string .bool
  | lean_uint64_dec_eq              : Extern2 .uint64 .uint64 .bool
  | lean_name_eq                    : Extern2 .name .name .bool
  | lean_uint8_dec_eq               : Extern2 .uint8 .uint8 .bool
  | lean_nat_pow                    : Extern2 .nat .nat .nat
  | lean_usize_dec_eq               : Extern2 .usize .usize .bool
  | lean_nat_mul                    : Extern2 .nat .nat .nat
  | lean_byte_array_push            : Extern2 .byteArray .uint8 .byteArray
  | lean_uint64_mix_hash            : Extern2 .uint64 .uint64 .uint64
  | lean_int_dec_le          : Extern2 .int .int .bool
  | lean_int_dec_lt          : Extern2 .int .int .bool
  | lean_int_dec_eq          : Extern2 .int .int .bool
  | lean_int_mul             : Extern2 .int .int .int
  | lean_int_add             : Extern2 .int .int .int
  | lean_int_sub             : Extern2 .int .int .int
  | lean_nat_div_exact : Extern2 .nat .nat .nat
  | lean_nat_lxor   : Extern2 .nat .nat .nat
  | lean_nat_shiftl : Extern2 .nat .nat .nat
  | lean_nat_shiftr : Extern2 .nat .nat .nat
  | lean_nat_land   : Extern2 .nat .nat .nat
  | lean_nat_lor    : Extern2 .nat .nat .nat
  | lean_usize_add        : Extern2 .usize .usize .usize
  | lean_uint32_sub       : Extern2 .uint32 .uint32 .uint32
  | lean_usize_sub        : Extern2 .usize .usize .usize
  | lean_uint32_add       : Extern2 .uint32 .uint32 .uint32
  | lean_usize_dec_le     : Extern2 .usize .usize .bool
  | lean_usize_dec_lt     : Extern2 .usize .usize .bool
  | lean_string_utf8_get       : Extern2 .string .stringPos .char
  | lean_substring_drop        : Extern2 .substring .nat .substring
  | lean_substring_prev        : Extern2 .substring .stringPos .stringPos
  | lean_string_append         : Extern2 .string .string .string
  | lean_string_get_byte_fast  : Extern2 .string .nat .uint8
  | lean_string_push           : Extern2 .string .char .string
  | lean_string_isprefixof     : Extern2 .string .string .bool
  | lean_string_dropright      : Extern2 .string .nat .string
  | lean_substring_takewhile   : Extern2 .substring (fn1 .char .bool) .substring
  | lean_substring_get         : Extern2 .substring .stringPos .char
  | lean_string_contains       : Extern2 .string .char .bool
  | lean_string_posof          : Extern2 .string .char .stringPos
  | lean_substring_all         : Extern2 .substring (fn1 .char .bool) .bool
  | lean_string_intercalate    : Extern2 .string (.list .string) .string
  | lean_string_drop           : Extern2 .string .nat .string
  | lean_string_utf8_at_end    : Extern2 .string .stringPos .bool
  | lean_substring_beq         : Extern2 .substring .substring .bool
  | lean_string_utf8_next      : Extern2 .string .stringPos .stringPos
  | lean_string_any            : Extern2 .string (fn1 .char .bool) .bool
  | lean_string_pos_min        : Extern2 .stringPos .stringPos .stringPos
  | lean_string_pos_sub        : Extern2 .stringPos .stringPos .stringPos
  | lean_string_offsetofpos    : Extern2 .string .stringPos .nat
  | lean_strict_or                   : Extern2 .bool .bool .bool
  | lean_strict_and                  : Extern2 .bool .bool .bool
  | lean_int_emod                     : Extern2 .int .int .int
  | lean_int_div_exact                : Extern2 .int .int .int
  | lean_int_mod                      : Extern2 .int .int .int
  | lean_int_ediv                     : Extern2 .int .int .int
  | lean_int_div                      : Extern2 .int .int .int
  | lean_nat_gcd                      : Extern2 .nat .nat .nat
  | lean_uint64_shift_left            : Extern2 .uint64 .uint64 .uint64
  | lean_uint32_mod                   : Extern2 .uint32 .uint32 .uint32
  | lean_usize_land                   : Extern2 .usize .usize .usize
  | lean_usize_mul                    : Extern2 .usize .usize .usize
  | lean_uint64_shift_right           : Extern2 .uint64 .uint64 .uint64
  | lean_usize_shift_left             : Extern2 .usize .usize .usize
  | lean_uint16_add                   : Extern2 .uint16 .uint16 .uint16
  | lean_usize_xor                    : Extern2 .usize .usize .usize
  | lean_uint16_lor                   : Extern2 .uint16 .uint16 .uint16
  | lean_uint16_mul                   : Extern2 .uint16 .uint16 .uint16
  | lean_uint16_land                  : Extern2 .uint16 .uint16 .uint16
  | lean_uint8_sub                    : Extern2 .uint8 .uint8 .uint8
  | lean_uint32_div                   : Extern2 .uint32 .uint32 .uint32
  | lean_uint64_add                   : Extern2 .uint64 .uint64 .uint64
  | lean_uint64_lor                   : Extern2 .uint64 .uint64 .uint64
  | lean_uint64_mod                   : Extern2 .uint64 .uint64 .uint64
  | lean_uint8_lor                    : Extern2 .uint8 .uint8 .uint8
  | lean_uint32_shift_right           : Extern2 .uint32 .uint32 .uint32
  | lean_uint16_xor                   : Extern2 .uint16 .uint16 .uint16
  | lean_usize_lor                    : Extern2 .usize .usize .usize
  | lean_uint8_div                    : Extern2 .uint8 .uint8 .uint8
  | lean_uint16_shift_left            : Extern2 .uint16 .uint16 .uint16
  | lean_uint16_mod                   : Extern2 .uint16 .uint16 .uint16
  | lean_uint64_div                   : Extern2 .uint64 .uint64 .uint64
  | lean_uint16_dec_lt                : Extern2 .uint16 .uint16 .bool
  | lean_uint8_shift_right            : Extern2 .uint8 .uint8 .uint8
  | lean_uint32_lor                   : Extern2 .uint32 .uint32 .uint32
  | lean_uint64_mul                   : Extern2 .uint64 .uint64 .uint64
  | lean_usize_shift_right            : Extern2 .usize .usize .usize
  | lean_uint64_land                  : Extern2 .uint64 .uint64 .uint64
  | lean_uint8_shift_left             : Extern2 .uint8 .uint8 .uint8
  | lean_uint16_div                   : Extern2 .uint16 .uint16 .uint16
  | lean_uint8_land                   : Extern2 .uint8 .uint8 .uint8
  | lean_uint64_dec_le                : Extern2 .uint64 .uint64 .bool
  | lean_uint8_mul                    : Extern2 .uint8 .uint8 .uint8
  | lean_uint64_sub                   : Extern2 .uint64 .uint64 .uint64
  | lean_uint8_add                    : Extern2 .uint8 .uint8 .uint8
  | lean_usize_div                    : Extern2 .usize .usize .usize
  | lean_uint32_xor                   : Extern2 .uint32 .uint32 .uint32
  | lean_uint16_dec_le                : Extern2 .uint16 .uint16 .bool
  | lean_uint32_shift_left            : Extern2 .uint32 .uint32 .uint32
  | lean_uint16_sub                   : Extern2 .uint16 .uint16 .uint16
  | lean_uint32_mul                   : Extern2 .uint32 .uint32 .uint32
  | lean_uint32_land                  : Extern2 .uint32 .uint32 .uint32
  | lean_usize_mod                    : Extern2 .usize .usize .usize
  | lean_uint8_mod                    : Extern2 .uint8 .uint8 .uint8
  | lean_uint64_dec_lt                : Extern2 .uint64 .uint64 .bool
  | lean_uint8_xor                    : Extern2 .uint8 .uint8 .uint8
  | lean_uint16_shift_right           : Extern2 .uint16 .uint16 .uint16
  | lean_uint64_xor                   : Extern2 .uint64 .uint64 .uint64
  | lean_byte_array_fget                   : Extern2 .byteArray .nat .uint8
  | lean_byte_array_uget                   : Extern2 .byteArray .usize .uint8
  | lean_byte_array_get                    : Extern2 .byteArray .nat .uint8
  | lean_string_get_utf8_byte              : Extern2 .string .stringPos .uint8
  | lean_string_get_byte_fast_raw          : Extern2 .string .stringPos .uint8
  | lean_string_append_defs                : Extern2 .string .string .string
  | lean_string_utf8_next_basic            : Extern2 .string .stringPos .stringPos
  | lean_string_pos_raw_next               : Extern2 .string .stringPos .stringPos
  | lean_string_pos_raw_get                : Extern2 .string .stringPos .char
  | lean_string_get_basic                  : Extern2 .string .stringPos .char
  | lean_string_pos_raw_get_opt            : Extern2 .string .stringPos (.option .char)
  | lean_string_get_opt                    : Extern2 .string .stringPos (.option .char)
  | lean_string_pos_raw_prev               : Extern2 .string .stringPos .stringPos
  | lean_string_prev                       : Extern2 .string .stringPos .stringPos
  | lean_string_next_fast                  : Extern2 .string .stringPos .stringPos
  | lean_string_pos_raw_next_fast          : Extern2 .string .stringPos .stringPos
  | lean_string_pos_next                   : Extern2 .string .stringPos .stringPos
  | lean_string_at_end_basic               : Extern2 .string .stringPos .bool
  | lean_string_pos_raw_at_end             : Extern2 .string .stringPos .bool
  | lean_string_pos_raw_get_bang           : Extern2 .string .stringPos .char
  | lean_string_get_bang                   : Extern2 .string .stringPos .char
  | lean_string_decode_char                : Extern2 .string .nat .char
  | lean_string_get_fast                   : Extern2 .string .stringPos .char
  | lean_string_pos_raw_get_fast           : Extern2 .string .stringPos .char
  | lean_string_is_valid_pos               : Extern2 .string .stringPos .bool
  | lean_string_dec_lt                     : Extern2 .string .string .bool
  | lean_int8_add                          : Extern2 .int8 .int8 .int8
  | lean_int16_dec_le                      : Extern2 .int16 .int16 .bool
  | lean_int32_land                        : Extern2 .int32 .int32 .int32
  | lean_int8_div                          : Extern2 .int8 .int8 .int8
  | lean_int32_mul                         : Extern2 .int32 .int32 .int32
  | lean_int64_sub                         : Extern2 .int64 .int64 .int64
  | lean_int16_shift_right                 : Extern2 .int16 .int16 .int16
  | lean_int64_xor                         : Extern2 .int64 .int64 .int64
  | lean_int32_dec_le                      : Extern2 .int32 .int32 .bool
  | lean_isize_xor                         : Extern2 .isize .isize .isize
  | lean_isize_shift_left                  : Extern2 .isize .isize .isize
  | lean_int64_mul                         : Extern2 .int64 .int64 .int64
  | lean_int32_sub                         : Extern2 .int32 .int32 .int32
  | lean_int64_land                        : Extern2 .int64 .int64 .int64
  | lean_int8_shift_right                  : Extern2 .int8 .int8 .int8
  | lean_int64_lor                         : Extern2 .int64 .int64 .int64
  | lean_int16_div                         : Extern2 .int16 .int16 .int16
  | lean_isize_mod                         : Extern2 .isize .isize .isize
  | lean_int8_mod                          : Extern2 .int8 .int8 .int8
  | lean_isize_shift_right                 : Extern2 .isize .isize .isize
  | lean_int8_shift_left                   : Extern2 .int8 .int8 .int8
  | lean_int16_dec_lt                      : Extern2 .int16 .int16 .bool
  | lean_int8_xor                          : Extern2 .int8 .int8 .int8
  | lean_int32_dec_eq                      : Extern2 .int32 .int32 .bool
  | lean_int16_mod                         : Extern2 .int16 .int16 .int16
  | lean_isize_div                         : Extern2 .isize .isize .isize
  | lean_int16_dec_eq                      : Extern2 .int16 .int16 .bool
  | lean_isize_add                         : Extern2 .isize .isize .isize
  | lean_int32_dec_lt                      : Extern2 .int32 .int32 .bool
  | lean_isize_lor                         : Extern2 .isize .isize .isize
  | lean_int64_mod                         : Extern2 .int64 .int64 .int64
  | lean_int64_shift_left                  : Extern2 .int64 .int64 .int64
  | lean_isize_land                        : Extern2 .isize .isize .isize
  | lean_isize_mul                         : Extern2 .isize .isize .isize
  | lean_int64_dec_lt                      : Extern2 .int64 .int64 .bool
  | lean_isize_dec_le                      : Extern2 .isize .isize .bool
  | lean_int8_dec_eq                       : Extern2 .int8 .int8 .bool
  | lean_int32_xor                         : Extern2 .int32 .int32 .int32
  | lean_int32_shift_left                  : Extern2 .int32 .int32 .int32
  | lean_isize_sub                         : Extern2 .isize .isize .isize
  | lean_int16_land                        : Extern2 .int16 .int16 .int16
  | lean_int32_shift_right                 : Extern2 .int32 .int32 .int32
  | lean_int16_mul                         : Extern2 .int16 .int16 .int16
  | lean_int16_shift_left                  : Extern2 .int16 .int16 .int16
  | lean_int16_xor                         : Extern2 .int16 .int16 .int16
  | lean_int8_dec_lt                       : Extern2 .int8 .int8 .bool
  | lean_int64_dec_eq                      : Extern2 .int64 .int64 .bool
  | lean_int64_dec_le                      : Extern2 .int64 .int64 .bool
  | lean_int32_add                         : Extern2 .int32 .int32 .int32
  | lean_isize_dec_lt                      : Extern2 .isize .isize .bool
  | lean_int32_lor                         : Extern2 .int32 .int32 .int32
  | lean_int32_mod                         : Extern2 .int32 .int32 .int32
  | lean_int64_add                         : Extern2 .int64 .int64 .int64
  | lean_int8_sub                          : Extern2 .int8 .int8 .int8
  | lean_int16_lor                         : Extern2 .int16 .int16 .int16
  | lean_int64_div                         : Extern2 .int64 .int64 .int64
  | lean_isize_dec_eq                      : Extern2 .isize .isize .bool
  | lean_int16_add                         : Extern2 .int16 .int16 .int16
  | lean_int8_dec_le                       : Extern2 .int8 .int8 .bool
  | lean_int8_mul                          : Extern2 .int8 .int8 .int8
  | lean_int8_land                         : Extern2 .int8 .int8 .int8
  | lean_int32_div                         : Extern2 .int32 .int32 .int32
  | lean_int16_sub                         : Extern2 .int16 .int16 .int16
  | lean_int8_lor                          : Extern2 .int8 .int8 .int8
  | lean_int64_shift_right                 : Extern2 .int64 .int64 .int64
  | lean_slice_dec_lt                      : Extern2 .stringSlice .stringSlice .bool
  | lean_float_div                         : Extern2 .float .float .float
  | lean_float_beq                         : Extern2 .float .float .bool
  | lean_float_decLe                       : Extern2 .float .float .bool
  | lean_float_le                          : Extern2 .float .float .bool
  | lean_float_decLt                       : Extern2 .float .float .bool
  | lean_float_lt                          : Extern2 .float .float .bool
  | atan2                                  : Extern2 .float .float .float
  | lean_float_mul                         : Extern2 .float .float .float
  | pow                                    : Extern2 .float .float .float
  | lean_float_scaleb                      : Extern2 .float .int64 .float
  | lean_float_add                         : Extern2 .float .float .float
  | lean_float_sub                         : Extern2 .float .float .float
  | lean_float_array_get                   : Extern2 .floatArray .nat .float
  | lean_float_array_uget                  : Extern2 .floatArray .usize .float
  | lean_float_array_fget                  : Extern2 .floatArray .nat .float
  | lean_float_array_push                  : Extern2 .floatArray .float .floatArray
  | lean_float32_div                : Extern2 .float32 .float32 .float32
  | lean_float32_le                 : Extern2 .float32 .float32 .bool
  | lean_float32_decLe              : Extern2 .float32 .float32 .bool
  | lean_float32_sub                : Extern2 .float32 .float32 .float32
  | powf                            : Extern2 .float32 .float32 .float32
  | lean_float32_beq                : Extern2 .float32 .float32 .bool
  | atan2f                          : Extern2 .float32 .float32 .float32
  | lean_float32_add                : Extern2 .float32 .float32 .float32
  | lean_float32_scaleb             : Extern2 .float32 .int64 .float32
  | lean_float32_mul                : Extern2 .float32 .float32 .float32
  | lean_float32_lt                 : Extern2 .float32 .float32 .bool
  | lean_float32_decLt              : Extern2 .float32 .float32 .bool
  | lean_sharecommon_eq             : Extern2 .shareCommonObject .shareCommonObject .bool
  | lean_array_uget_borrowed          : (α : X) → Extern2 (.array α) .usize α
  | lean_string_uget_byte_fast : Extern2 .string .usize .uint8
  | lean_sarray_beq                        : Extern2 .byteArray .byteArray .bool
  | lean_sarray_dec_eq                     : Extern2 .byteArray .byteArray .bool
  | lean_string_compare             : Extern2 .string .string .ordering

inductive Extern3 : Ty → Ty → Ty → Ty → Type where
  | lean_array_set                    : (α : X) → Extern3 (.array α) .nat α (.array α)
  | lean_array_fset                   : (α : X) → Extern3 (.array α) .nat α (.array α)
  | lean_array_fswap                  : (α : X) → Extern3 (.array α) .nat .nat (.array α)
  | lean_array_swap                   : (α : X) → Extern3 (.array α) .nat .nat (.array α)
  | lean_array_uset                   : (α : X) → Extern3 (.array α) .usize α (.array α)
  | lean_substring_extract     : Extern3 .substring .stringPos .stringPos .substring
  | lean_string_foldl          : Extern3 (.fn [.string, .char] .string) .string .string .string
  | lean_string_nextwhile      : Extern3 .string (.fn [.char] .bool) .stringPos .stringPos
  | lean_string_pushn          : Extern3 .string .char .nat .string
  | lean_string_utf8_extract   : Extern3 .string .stringPos .stringPos .string
  | lean_byte_array_set                    : Extern3 .byteArray .nat .uint8 .byteArray
  | lean_byte_array_uset                   : Extern3 .byteArray .usize .uint8 .byteArray
  | lean_byte_array_fset                   : Extern3 .byteArray .nat .uint8 .byteArray
  | lean_string_utf8_extract_fast          : Extern3 .string .stringPos .stringPos .string
  | lean_string_utf8_extract_basic         : Extern3 .string .stringPos .stringPos .string
  | lean_string_pos_raw_set                : Extern3 .string .stringPos .char .string
  | lean_string_pos_set                    : Extern3 .string .stringPos .char .string
  | lean_string_set                        : Extern3 .string .stringPos .char .string
  | lean_float_array_fset                  : Extern3 .floatArray .nat .float .floatArray
  | lean_float_array_uset                  : Extern3 .floatArray .usize .float .floatArray
  | lean_float_array_set                   : Extern3 .floatArray .nat .float .floatArray

inductive Extern4 : Ty → Ty → Ty → Ty → Ty → Type where
  | lean_task_map                    : (α : X) → (β : Ty) → Extern4 (.fn [α] β) (.task α) .nat .bool (.task β)
  | lean_task_bind                   : (α : X) → (β : Ty) → Extern4 (.task α) (.fn [α] (.task β)) .nat .bool (.task β)

inductive Extern5 : Ty → Ty → Ty → Ty → Ty → Ty → Type where
  | lean_string_memcmp                     : Extern5 .string .string .stringPos .stringPos .stringPos .bool

inductive Extern6 : Ty → Ty → Ty → Ty → Ty → Ty → Ty → Type where
  | lean_byte_array_copy_slice             : Extern6 .byteArray .nat .byteArray .nat .nat .bool .byteArray
