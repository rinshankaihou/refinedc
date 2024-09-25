From refinedc.typing Require Import typing.
From refinedc.tutorial.VerifyThis.t01_refinements Require Import generated_code.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/VerifyThis/t01_refinements.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Specifications for function [__builtin_ffsll]. *)
  Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (i32))); True.

  (* Function [avg_1] has been skipped. *)

  (* Specifications for function [avg_2]. *)
  Definition type_of_avg_2 :=
    fn(∀ () : (); (int (u32)), (int (u32)); True)
      → ∃ () : (), (int (u32)); True.

  (* Specifications for function [avg_3]. *)
  Definition type_of_avg_3 :=
    fn(∀ () : (); (int (u32)), (int (u32)); True)
      → ∃ () : (), (int (u32)); True.

  (* Specifications for function [avg_4]. *)
  Definition type_of_avg_4 :=
    fn(∀ (na, nb) : Z * Z; (na @ (int (u32))), (nb @ (int (u32))); True)
      → ∃ r : Z, (r @ (int (u32))); ⌜na `min` nb <= r⌝ ∗ ⌜r <= na `max` nb⌝ ∗ ⌜r = (na + nb) `div` 2⌝.

  (* Specifications for function [avg_5]. *)
  Definition type_of_avg_5 :=
    fn(∀ (na, nb) : Z * Z; (na @ (int (u32))), (nb @ (int (u32))); True)
      → ∃ () : (), (((na + nb) `div` 2) @ (int (u32))); True.
End spec.
