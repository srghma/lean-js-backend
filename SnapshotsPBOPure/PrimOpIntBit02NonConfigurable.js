import {
  $lean_int16_complement,
  $lean_int16_land,
  $lean_int16_lor,
  $lean_int16_neg,
  $lean_int16_of_nat,
  $lean_int16_shift_left,
  $lean_int16_shift_right,
  $lean_int16_xor,
  $lean_int32_complement,
  $lean_int32_land,
  $lean_int32_lor,
  $lean_int32_neg,
  $lean_int32_of_nat,
  $lean_int32_shift_left,
  $lean_int32_shift_right,
  $lean_int32_xor,
  $lean_int8_complement,
  $lean_int8_land,
  $lean_int8_lor,
  $lean_int8_neg,
  $lean_int8_of_nat,
  $lean_int8_shift_left,
  $lean_int8_shift_right,
  $lean_int8_xor,
  $lean_uint16_complement,
  $lean_uint16_land,
  $lean_uint16_lor,
  $lean_uint16_neg,
  $lean_uint16_shift_left,
  $lean_uint16_shift_right,
  $lean_uint16_xor,
  $lean_uint32_complement,
  $lean_uint32_land,
  $lean_uint32_lor,
  $lean_uint32_neg,
  $lean_uint32_shift_left,
  $lean_uint32_shift_right,
  $lean_uint32_xor,
  $lean_uint8_complement,
  $lean_uint8_land,
  $lean_uint8_lor,
  $lean_uint8_neg,
  $lean_uint8_shift_left,
  $lean_uint8_shift_right,
  $lean_uint8_xor,
} from "../runtime/lean_runtime_non_configurable.mjs";
export const TestUInt8_xor = $lean_uint8_xor(15, 12);
export const TestUInt8_shiftRight = (() => {
  const v0 = $lean_uint8_neg(255);
  return $lean_uint8_shift_right(v0, 2);
})();
export const TestUInt8_shiftLeft = $lean_uint8_shift_left(255, 2);
export const TestUInt8_lor = $lean_uint8_lor(16, 15);
export const TestUInt8_land = $lean_uint8_land(255, 8);
export const TestUInt8_complement = (() => {
  const v0 = $lean_uint8_neg(3);
  return $lean_uint8_complement(v0);
})();
export const TestUInt32_xor = $lean_uint32_xor(15, 12);
export const TestUInt32_shiftRight = (() => {
  const v0 = $lean_uint32_neg(1023);
  return $lean_uint32_shift_right(v0, 2);
})();
export const TestUInt32_shiftLeft = $lean_uint32_shift_left(1023, 2);
export const TestUInt32_lor = $lean_uint32_lor(16, 15);
export const TestUInt32_land = $lean_uint32_land(1023, 8);
export const TestUInt32_complement = (() => {
  const v0 = $lean_uint32_neg(3);
  return $lean_uint32_complement(v0);
})();
export const TestUInt16_xor = $lean_uint16_xor(15, 12);
export const TestUInt16_shiftRight = (() => {
  const v0 = $lean_uint16_neg(1023);
  return $lean_uint16_shift_right(v0, 2);
})();
export const TestUInt16_shiftLeft = $lean_uint16_shift_left(1023, 2);
export const TestUInt16_lor = $lean_uint16_lor(16, 15);
export const TestUInt16_land = $lean_uint16_land(1023, 8);
export const TestUInt16_complement = (() => {
  const v0 = $lean_uint16_neg(3);
  return $lean_uint16_complement(v0);
})();
export const TestInt8_xor = (() => {
  const v0 = 15;
  const v1 = 12;
  return $lean_int8_xor(v0, v1);
})();
export const TestInt8_shiftRight = (() => {
  const v0 = -1;
  const v1 = $lean_int8_neg(v0);
  const v2 = 2;
  return $lean_int8_shift_right(v1, v2);
})();
export const TestInt8_shiftLeft = (() => {
  const v0 = -1;
  const v1 = 2;
  return $lean_int8_shift_left(v0, v1);
})();
export const TestInt8_lor = (() => {
  const v0 = 16;
  const v1 = 15;
  return $lean_int8_lor(v0, v1);
})();
export const TestInt8_land = (() => {
  const v0 = -1;
  const v1 = 8;
  return $lean_int8_land(v0, v1);
})();
export const TestInt8_complement = (() => {
  const v0 = 3;
  const v1 = $lean_int8_neg(v0);
  return $lean_int8_complement(v1);
})();
export const TestInt32_xor = (() => {
  const v0 = 15;
  const v1 = 12;
  return $lean_int32_xor(v0, v1);
})();
export const TestInt32_shiftRight = (() => {
  const v0 = 1023;
  const v1 = $lean_int32_neg(v0);
  const v2 = 2;
  return $lean_int32_shift_right(v1, v2);
})();
export const TestInt32_shiftLeft = (() => {
  const v0 = 1023;
  const v1 = 2;
  return $lean_int32_shift_left(v0, v1);
})();
export const TestInt32_lor = (() => {
  const v0 = 16;
  const v1 = 15;
  return $lean_int32_lor(v0, v1);
})();
export const TestInt32_land = (() => {
  const v0 = 1023;
  const v1 = 8;
  return $lean_int32_land(v0, v1);
})();
export const TestInt32_complement = (() => {
  const v0 = 3;
  const v1 = $lean_int32_neg(v0);
  return $lean_int32_complement(v1);
})();
export const TestInt16_xor = (() => {
  const v0 = 15;
  const v1 = 12;
  return $lean_int16_xor(v0, v1);
})();
export const TestInt16_shiftRight = (() => {
  const v0 = 1023;
  const v1 = $lean_int16_neg(v0);
  const v2 = 2;
  return $lean_int16_shift_right(v1, v2);
})();
export const TestInt16_shiftLeft = (() => {
  const v0 = 1023;
  const v1 = 2;
  return $lean_int16_shift_left(v0, v1);
})();
export const TestInt16_lor = (() => {
  const v0 = 16;
  const v1 = 15;
  return $lean_int16_lor(v0, v1);
})();
export const TestInt16_land = (() => {
  const v0 = 1023;
  const v1 = 8;
  return $lean_int16_land(v0, v1);
})();
export const TestInt16_complement = (() => {
  const v0 = 3;
  const v1 = $lean_int16_neg(v0);
  return $lean_int16_complement(v1);
})();
