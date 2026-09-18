---
addleakage:
  target: [lm_xor, lm_xor_inplace, lm_not, lm_not_inplace, lm_shl, lm_shl_inplace, lm_shr, lm_shr_inplace, lm_rol64_1, lm_and_derand, lm_ref_derand]
  strict: true;

print:
  kind: macrodef
  target: [lm_xor, lm_xor_inplace, lm_not, lm_not_inplace, lm_shl, lm_shl_inplace, lm_shr, lm_shr_inplace, lm_rol64_1, lm_and_derand, lm_ref_derand]
  verbosity: 0;

inlinecall:
  target: [lm_xor, lm_xor_inplace, lm_not, lm_not_inplace, lm_shl, lm_shl_inplace, lm_shr, lm_shr_inplace, lm_rol64_1, lm_and_derand, lm_ref_derand];

partialeval:
  target: [lm_xor, lm_xor_inplace, lm_not, lm_not_inplace, lm_shl, lm_shl_inplace, lm_shr, lm_shr_inplace, lm_rol64_1, lm_and_derand, lm_ref_derand];

print:
  kind: evaltrace
  target: [lm_xor, lm_xor_inplace, lm_not, lm_not_inplace, lm_shl, lm_shl_inplace, lm_shr, lm_shr_inplace, lm_rol64_1, lm_and_derand, lm_ref_derand]
  verbosity: 0;

infertaint:
  inputsAsPublic: true
  outputsAsPublic: true
  memoryAsPublicOut: true
  target: [lm_xor, lm_xor_inplace, lm_not, lm_not_inplace, lm_shl, lm_shl_inplace, lm_shr, lm_shr_inplace, lm_rol64_1, lm_and_derand, lm_ref_derand];

check:
  kind: "Stateful NI"
  target: [lm_xor, lm_xor_inplace, lm_not, lm_not_inplace, lm_shl, lm_shl_inplace, lm_shr, lm_shr_inplace, lm_rol64_1];

check:
  kind: "Stateful SNI"
  target: [lm_and_derand, lm_ref_derand];
...
