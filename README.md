# Secure Compilation of Probabilistic Side-Channel Countermeasures

This repository contains the artifacts to our paper
_Secure Compilation of Probabilistic Side-Channel Countermeasures_
to appear at S&P'27.

## Requirements

Our development (including Nix shell and the Docker image) is tested on x86-64
Linux. Apart from compiling the dependencies, every step necessary to reproduce
our results is quick (on the order of seconds per command invocation). Thus, we
recommend running the evaluation locally. If you rather run on a public research
infrastructure, we have verified our work on
[SPHERE](http://sphere-testbed.net/) using the topology described in
`sphere-model.py`.

## Quick Overview

- **`proofs/`** --- Rocq theories of the formal framework and the leakage preserving compiler.
- **`gadgets/`** --- `libmasking` sources.
- **`gadgets/src`** --- Library of transition-hardened masked gadgets and masked SHA3 implementation.
- **`gadgets/proofs`** --- EasyCrypt proofs of correctness of some of our gadgets.
- **`gadgets/test`** --- QEMU-based unit-test environment for the gadget library.
- **`gadgets/verify`** --- Our scVerif leakage models and environment for our security verification.
- **`gadgets/benchmark`** --- Benchmarking environment for the `RP2350` microcontroller, scripts, and naive C implementation from the paper.
- **`gadgets/benchmark/counterexample`** --- Various counterexamples for leakage preservation of `gcc` with different optimizations.

## Reproducing

Dependencies are managed with [Nix](https://nixos.org/), and the easiest way to
reproduce our results is to [install Nix](https://nixos.org/download/) and use
our Nix "devshell". Entering the devshell automatically fetches/compiles all
dependencies which are pinned to the correct version. Note that entering the
devshell might take some time (30 minutes on AMD Ryzen AI 7) as it compiles the
RISC-V and ARM toolchains and the Jasmin compiler. The development is tested on
x86-64 Linux.

```sh
nix --experimental-features "nix-command flakes" develop .#default
```

All commands below assume you are inside the devshell.

### Reproducing with Docker

If you do not wish to install Nix, you can use the included Dockerfile to build
a Docker image that drops you in a shell with all dependencies:

```sh
docker build -t scomp .  # This will take some time.
docker run -it scomp     # This will drop you into a shell with all dependencies
```

### List of dependencies for manual installation:

- The Coq Proof Assistant, version 8.19.2 compiled with OCaml 4.14.2
- EasyCrypt 2026.02
- Z3 version 4.15.8 - 64 bit
- CVC4 version 1.8
- arm-none-eabi-gcc (Arm GNU Toolchain 15.2.Rel1 (Build arm-15.86)) 15.2.1 20251203
- riscv32-none-elf-gcc (RISCV GNU Toolchain) 15.2.0
- Python 3.12
- pico-sdk 2.2.0
- QEMU emulator version 10.2.1
- cmake version 4.1.2
- ninja version 1.13.2
- Jasmin on the `inplace-annotation` branch
- scVerif on `33d0068e`

## Proofs

The directory `proofs` contains our Rocq development. To build and verify,
enter the `proofs` directory inside the devshell and run:

```sh
dune build
```

If this command succeeds (empty output, exit status `0`), all proofs were
checked successfully. To step through the proofs interactively (e.g., using
[ProofGeneral](https://proofgeneral.github.io/)), you must first run 
`dune build` like above.

### Soundness

There are no `Admitted` goals, and the general framework results depend on no
axioms. The per-pass `preservation_obs` results depend on axioms
`leaks_mop`/`leaks_mop_eq` (in `semantics.v`), which leave the leakage of
machine operations unspecified. The per-pass results also depend on the result
of the respective program analysis (`analyze_i`, `should_peel`), which is a
parameter because the analysis is untrusted. The per-pass results depend on
axiom K due to dependent pattern matching.

### Overview of the Rocq files (`proofs/src/`)

| File | Contents |
| --- | --- |
| `utils.v`, `utils_facts.v`, `Fsets.v`, `var.v` | notations, finite sets and maps, variable types, ... |
| `syntax.v`, `semantics.v` | Definition of our toy language. |
| `semantics_facts.v` | Lemmas about the toy language's semantics. |
| `language.v` | The abstract `Language` class which is fulfilled by our model language. |
| `safety.v` | Definition of program safety. |
| `correctness.v` | Compiler correctness definition. |
| `preservation_obs.v` | Definition 4.2: `preserves_obs`, Lemma 4.2: `lift_step_preserves_obs` |
| `pass_composition.v` | Lemma 4.1: Correctness and `preserves_obs` are preserved under composition of passes. |
| `ni_preservation.v`, `probabilistic_ni.v`, `probabilistic_sni.v`, `probabilistic_fni.v` | Preservation of various security notions. |

Each of the remaining files defines one compiler pass and proves
`preservation_obs` for it: `eval_const.v`, `constant_propagation.v`,
`dead_code_elimination.v`, `dead_branch_elimination.v`, `flattening.v`,
`loop_peeling.v`, `register_allocation.v`, `array_concatenation.v` and
`array_reuse.v`.

## libmasking (`gadgets/`)

Our Jasmin library of masked gadgets and masked SHA3 can be found in the
directory `gadgets`. We provide a `Makefile` to build the various versions of
the gadget library.

### Building libmasking

We support up to fourth-order masking on both the RISC-V and the ARM backend.

```sh
cd gadgets                            # now in `gadgets/`
make libmasking                       # ARM Cortex-M4, first-order masking
make libmasking ARCH=riscv ORDER=2    # RISC-V, second-order masking
make libmasking ARCH=arm-m4 ORDER=4   # ARM Cortex-M4, fourth-order masking
```

The output binary lands in `_build/<arch>/order<N>/libmasking.a` and can be
linked e.g., in C code. For use with C, we provide a header file in
`gadgets/gadgets.h`. You can specify the current masking order by setting the
C preprocessor symbol `LM_ORDER` (defaults to first-order masking).


### Tests

We provide a QEMU-based testing environment for the two backends in
`gadgets/test`. The environment runs unit tests for the Keccak flavors and tests
the gadgets individually. The testing environment also serves as a usage example
for using `libmasking` on bare-metal platforms. To compile and run the test
environment, run:

```sh
cd gadgets                   # now in `gadgets/`
make test                    # build and run `gadgets/test` under qemu-system-arm
make test ARCH=riscv ORDER=2 # higher order, qemu-system-riscv32
```

### Security Verification

As outlined in the paper, we perform security verification on some gadgets using
scVerif. We provide two instruction set definitions and two leakage models
(probing with transitions): `gadgets/verify/arm-m4-isa.il` and
`gadgets/verify/arm-m4-leakage.il` for the ARM backend and
`gadgets/verify/riscv-isa.il` `gadgets/verify/riscv-leakage.il` for the RISC-V
backend. `gadgets/verify/arm-m4-gen` and `gadgets/verify/riscv-gen` produce
masking-order-dependent annotations for the Jasmin gadgets. The scVerif code for
performing the verification is in `gadgets/verify/check.il`.

To run the whole verification pipeline automatically, enter the `gadgets` folder
and run:

```sh
cd gadgets                            # now in `gadgets/`
make scverif-check                    # NI/SNI verification for first-order-masked ARM backend
make scverif-check ARCH=riscv ORDER=2 # RISC-V, second-order masking
```

### EasyCrypt extraction

Most gadgets are accompanied by correctness proofs in EasyCrypt located in
`gadgets/proofs`. The proofs consist of functional descriptions of gadgets and
accompanying correctness proofs in `Masking.eca`, arbitrary-order gadget
implementations and accompanying correctness proofs in `Gadgets.eca`, and,
finally, instantiations of the gadgets with the extracted Jasmin functions for
orders 1 to 4. To verify the correctness proofs run:

```sh
cd gadgets                              # now in `gadgets/`
make extract                            # extract first-order gadgets to easycrypt
make extract-all                        # extract orders 1..4
cd proofs                               # now in `gadgets/proofs/`
# We have to configure SMT solvers for EasyCrypt first. This takes SMT solvers
# from your path which should be available if you use the Nix devshell or the
# Docker container. Note that this will modify ~/.config/easycrypt on your
# system if you use the devshell.
easycrypt why3config
easycrypt runtest easycrypt.project all # verify correctness proofs
```

### C-compiler counterexample (`gadgets/benchmark/counterexample/`)

In our paper, we claim that off-the-shelf compilers regularly break
side-channel countermeasures. To demonstrate this, we provide several examples
where `gcc` breaks security of masked gadgets. We have several C implementations
of a multiplication gadget in `gadgets/benchmark/counterexample/and.c` with
source-code comments explaining when probing security is broken after
compilation. You can uncomment different multiplication gadgets and see how they
break by running:

```sh
cd gadgets/benchmark/counterexample   # now in `gadgets/benchmark/counterexample`
make check          # compile and verify C gadgets
# we expect an error here! ScVerif will tell us `Cannot check` and output a
# probe it cannot justify.
make check OPT=-O3  # use different optimization settings (default is -O1)
# Uncomment different implementations of the and gadget in 
# gadgets/benchmark/counterexample/and.c and see they fail in different ways.
# All counterexamples were found using 
#   gcc (Arm GNU Toolchain 15.2.Rel1 (Build arm-15.86)) 15.2.1 20251203.
```

Contrary to our own gadget library, we do not consider transition leakage. We
remove transition leakage from our model using scVerif's `filterleak` option in
`gadgets/benchmark/counterexample/and.il`.

### Benchmarks (`gadgets/benchmark/`)

The performance numbers reported in the paper were measured on a physical
`RP2350` microcontroller flashed over USB. This part of the artifact is
therefore **not reproducible without that specific hardware.** However, this is
**not a core claim** of the paper. We include `gadgets/benchmark/benchall.sh`
for completeness: it builds and flashes the C and Jasmin benchmarks for orders
1..4 and collects the measurements, and thus documents how the reported numbers
were obtained.

## License

We release the Rocq development and the libmasking sources (including leakage
models, counterexamples, EasyCrypt proofs) under the MIT license (see
`LICENSE`).