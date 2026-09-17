import {
  $lean_int64_complement,
  $lean_int64_land,
  $lean_int64_lor,
  $lean_int64_neg,
  $lean_int64_of_nat,
  $lean_int64_shift_left,
  $lean_int64_shift_right,
  $lean_int64_xor,
  $lean_int_neg,
  $lean_isize_complement,
  $lean_isize_land,
  $lean_isize_lor,
  $lean_isize_neg,
  $lean_isize_of_nat,
  $lean_isize_shift_left,
  $lean_isize_shift_right,
  $lean_isize_xor,
  $lean_nat_land,
  $lean_nat_lor,
  $lean_nat_lxor,
  $lean_nat_shiftl,
  $lean_nat_shiftr,
  $lean_uint64_complement,
  $lean_uint64_land,
  $lean_uint64_lor,
  $lean_uint64_neg,
  $lean_uint64_shift_left,
  $lean_uint64_shift_right,
  $lean_uint64_xor,
  $lean_usize_complement,
  $lean_usize_land,
  $lean_usize_lor,
  $lean_usize_neg,
  $lean_usize_shift_left,
  $lean_usize_shift_right,
  $lean_usize_xor,
  Int_not,
} from "../runtime/lean_runtime_bigint.mjs";
export const TestUSize_xor = $lean_usize_xor(15n, 12n);
export const TestUSize_shiftRight = (() => {
  const v0 = $lean_usize_neg(1023n);
  return $lean_usize_shift_right(v0, 2n);
})();
export const TestUSize_shiftLeft = $lean_usize_shift_left(1023n, 2n);
export const TestUSize_lor = $lean_usize_lor(16n, 15n);
export const TestUSize_land = $lean_usize_land(1023n, 8n);
export const TestUSize_complement = (() => {
  const v0 = $lean_usize_neg(3n);
  return $lean_usize_complement(v0);
})();
export const TestUInt64_xor = $lean_uint64_xor(15n, 12n);
export const TestUInt64_shiftRight = (() => {
  const v0 = $lean_uint64_neg(1023n);
  return $lean_uint64_shift_right(v0, 2n);
})();
export const TestUInt64_shiftLeft = $lean_uint64_shift_left(1023n, 2n);
export const TestUInt64_lor = $lean_uint64_lor(16n, 15n);
export const TestUInt64_land = $lean_uint64_land(1023n, 8n);
export const TestUInt64_complement = (() => {
  const v0 = $lean_uint64_neg(3n);
  return $lean_uint64_complement(v0);
})();
export const TestNat_xor = $lean_nat_lxor(15n, 12n);
export const TestNat_shiftRight = $lean_nat_shiftr(1023n, 2n);
export const TestNat_shiftLeft = $lean_nat_shiftl(1023n, 2n);
export const TestNat_lor = $lean_nat_lor(16n, 15n);
export const TestNat_land = $lean_nat_land(1023n, 8n);
export const TestInt64_xor = (() => {
  const v0 = $lean_int64_of_nat(15n);
  const v1 = $lean_int64_of_nat(12n);
  return $lean_int64_xor(v0, v1);
})();
export const TestInt64_shiftRight = (() => {
  const v0 = $lean_int64_of_nat(1023n);
  const v1 = $lean_int64_neg(v0);
  const v2 = $lean_int64_of_nat(2n);
  return $lean_int64_shift_right(v1, v2);
})();
export const TestInt64_shiftLeft = (() => {
  const v0 = $lean_int64_of_nat(1023n);
  const v1 = $lean_int64_of_nat(2n);
  return $lean_int64_shift_left(v0, v1);
})();
export const TestInt64_lor = (() => {
  const v0 = $lean_int64_of_nat(16n);
  const v1 = $lean_int64_of_nat(15n);
  return $lean_int64_lor(v0, v1);
})();
export const TestInt64_land = (() => {
  const v0 = $lean_int64_of_nat(1023n);
  const v1 = $lean_int64_of_nat(8n);
  return $lean_int64_land(v0, v1);
})();
export const TestInt64_complement = (() => {
  const v0 = $lean_int64_of_nat(3n);
  const v1 = $lean_int64_neg(v0);
  return $lean_int64_complement(v1);
})();
export const TestInt_complement = (() => {
  const v0 = $lean_int_neg(3n);
  return Int_not(v0);
})();
export const TestISize_xor = (() => {
  const v0 = $lean_isize_of_nat(15n);
  const v1 = $lean_isize_of_nat(12n);
  return $lean_isize_xor(v0, v1);
})();
export const TestISize_shiftRight = (() => {
  const v0 = $lean_isize_of_nat(1023n);
  const v1 = $lean_isize_neg(v0);
  const v2 = $lean_isize_of_nat(2n);
  return $lean_isize_shift_right(v1, v2);
})();
export const TestISize_shiftLeft = (() => {
  const v0 = $lean_isize_of_nat(1023n);
  const v1 = $lean_isize_of_nat(2n);
  return $lean_isize_shift_left(v0, v1);
})();
export const TestISize_lor = (() => {
  const v0 = $lean_isize_of_nat(16n);
  const v1 = $lean_isize_of_nat(15n);
  return $lean_isize_lor(v0, v1);
})();
export const TestISize_land = (() => {
  const v0 = $lean_isize_of_nat(1023n);
  const v1 = $lean_isize_of_nat(8n);
  return $lean_isize_land(v0, v1);
})();
export const TestISize_complement = (() => {
  const v0 = $lean_isize_of_nat(3n);
  const v1 = $lean_isize_neg(v0);
  return $lean_isize_complement(v1);
})();
