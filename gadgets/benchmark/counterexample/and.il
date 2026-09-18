annotate bg_and_derand
    region mem w32 c[0:1]
    region mem w32 a[0:1]
    region mem w32 b[0:1]
    region mem w32 rnd[0:0]
    region mem w32 stack[-100:0]

    init sp [stack 0]
    init r0 [c 0]
    init r1 [a 0]
    init r2 [b 0]
    init r3 [rnd 0]
    init lr exit

    input public ip
    input public apsrc

    input sharing a
    input sharing b
    input urandom rnd
    output sharing c
    ;
  
annotate bg_ref_derand
    region mem w32 c[0:1]
    region mem w32 a[0:1]
    region mem w32 rnd[0:0]
    region mem w32 stack[-100:0]

    init sp [stack 0]
    init r0 [c 0]
    init r1 [a 0]
    init r2 [rnd 0]
    init lr exit

    input public ip
    input public apsrc

    input sharing a
    input urandom rnd
    output sharing c
    ;
  


annotate bg_xor
    region mem w32 c[0:1]
    region mem w32 a[0:1]
    region mem w32 b[0:1]
    region mem w32 stack[-100:0]

    init sp [stack 0]
    init r0 [c 0]
    init r1 [a 0]
    init r2 [b 0]
    init lr exit

    input public ip
    input public apsrc

    input sharing a
    input sharing b
    output sharing c
    ;

// annotate bg_xor_trans
//     region mem w32 c[0:1]
//     region mem w32 a[0:1]
//     region mem w32 b[0:1]
//     region mem w32 stack[-100:0]
// 
//     init sp [stack 0]
//     init r0 [c 0]
//     init r1 [a 0]
//     init r2 [b 0]
//     init lr exit
// 
//     input public ip
//     input public apsrc
// 
//     input sharing a
//     input sharing b
//     output sharing c
//     ;

---
addleakage:
  target: [bg_and_derand, bg_ref_derand, bg_xor]
  strict: true;

print:
  kind: macrodef
  target: [bg_and_derand, bg_ref_derand, bg_xor]
  verbosity: 0;

inlinecall:
  target: [bg_and_derand, bg_ref_derand, bg_xor];

partialeval:
  target: [bg_and_derand, bg_ref_derand, bg_xor];

filterleak:
  target: [bg_and_derand, bg_ref_derand, bg_xor]
  leaks: "*Trans*"
  inverse: false;

print:
  kind: evaltrace
  target: [bg_and_derand, bg_ref_derand, bg_xor]
  verbosity: 0;

infertaint:
  inputsAsPublic: true
  outputsAsPublic: true
  memoryAsPublicOut: true
  target: [bg_and_derand, bg_ref_derand, bg_xor];

check:
  kind: "SNI"
  target: [bg_and_derand];
// check:
//   kind: "SNI"
//   target: [bg_ref_derand];
// check:
//   kind: "NI"
//   target: [bg_xor];
// check:
//   kind: "Stateful NI"
//   target: [bg_xor_trans];
...
