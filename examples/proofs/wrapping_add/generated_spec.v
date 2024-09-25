From refinedc.typing Require Import typing.
From refinedc.examples.wrapping_add Require Import generated_code.
From caesium Require Import builtins_specs.
From refinedc.examples.wrapping_add Require Import wrapping_rules.
Set Default Proof Using "Type".

(* Generated from [examples/wrapping_add.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Specifications for function [__builtin_ffsll]. *)
  Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (i32))); True.

  (* Specifications for function [wrapping_add]. *)
  Definition type_of_wrapping_add :=
    fn(∀ (a, b, c) : Z * Z * Z; (a @ (int (size_t))), (b @ (int (size_t))), (c @ (int (size_t))); ⌜(b + c < int_modulus size_t)⌝)
      → ∃ () : (), ((((a + (b + c)) `mod` int_modulus size_t)) @ (int (size_t))); True.
End spec.
