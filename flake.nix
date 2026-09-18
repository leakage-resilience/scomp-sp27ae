{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?rev=194846768975b7ad2c4988bdb82572c00222c0d7";
    # Pinned before menhir 20260203 bump which breaks elpi on aarch64
    # (OCaml 4.14 native compiler "conditional branch out of range")
    nixpkgs-unstable.url = "github:nixos/nixpkgs?rev=3cbadb8d8db0495065347b709baab421139bf6f6";
    flake-compat = {
      url = "github:NixOS/flake-compat";
      flake = false;
    };
    jasmin-src = {
      url = "github:jasmin-lang/jasmin?ref=inplace-annotation";
      flake = false;
    };
    scverif.url = "github:leakage-resilience/scverif-pub";
  };

  outputs =
    {
      self,
      nixpkgs,
      nixpkgs-unstable,
      flake-compat,
      jasmin-src,
      scverif,
    }:
    let
      lib = nixpkgs.lib;
      per-system =
        system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          pkgs-unstable = nixpkgs-unstable.legacyPackages.${system};

          jasmin-inplace-annotation = import jasmin-src {
            pkgs = pkgs-unstable;
          };
          jasmin-eclib = "${jasmin-src}/eclib";

          riscv-toolchain =
            (import nixpkgs-unstable {
              inherit system;
              crossSystem = {
                config = "riscv32-none-elf";
                libc = "newlib";
                abi = "ilp32";
                gcc = {
                  arch = "rv32ima";
                };
              };
            }).buildPackages.gcc;

          pico-sdk = pkgs.fetchFromGitHub {
            owner = "raspberrypi";
            repo = "pico-sdk";
            rev = "a1438dff1d38bd9c65dbd693f0e5db4b9ae91779";
            fetchSubmodules = true;
            hash = "sha256-8ubZW6yQnUTYxQqYI6hi7s3kFVQhe5EaxVvHmo93vgk=";
          };

          devshell = pkgs-unstable.mkShell {
            EC_IDIRS = "Jasmin:${jasmin-eclib}";
            PICO_SDK_PATH = "${pico-sdk}";
            buildInputs =
              (with pkgs.coqPackages; [
                # for Rocq proofs:
                coq
                mathcomp.ssreflect
                coq.ocamlPackages.dune_3
                coq.ocamlPackages.ocaml
              ])
              ++ (with pkgs-unstable; [
                # for Gadget Library:
                jasmin-inplace-annotation
                scverif.packages.${system}.default
                gcc-arm-embedded
                riscv-toolchain
                easycrypt
                z3
                cvc4
                qemu_full
                python3
                picotool
                ninja
                cmake
              ]);
          };

        in
        {
          # for flake-compat
          packages.${system}.default = devshell;
          devShells.${system}.default = devshell;
        };
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
    in
    builtins.foldl' lib.recursiveUpdate { } (map per-system systems);
}
