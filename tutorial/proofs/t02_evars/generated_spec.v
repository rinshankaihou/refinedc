From refinedc.typing Require Import typing.
From refinedc.tutorial.t02_evars Require Import generated_code.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/t02_evars.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Inlined code. *)

  Global Instance simpl_both_20_mult_5 n: SimplBoth (20 = n * 5) (n = 4).
  Proof. split; lia. Qed.

  (* Specifications for function [__builtin_ffsll]. *)
  Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (i32))); True.

  (* Specifications for function [evar_create]. *)
  Definition type_of_evar_create :=
    fn(∀ () : (); True) → ∃ n : Z, (void); ⌜n > 0⌝.

  (* Specifications for function [evar_create_sidecond]. *)
  Definition type_of_evar_create_sidecond :=
    fn(∀ () : (); True) → ∃ () : (), (void); ⌜∃ n, n > 0⌝.

  (* Specifications for function [evar_create_return_int]. *)
  Definition type_of_evar_create_return_int :=
    fn(∀ () : (); True) → ∃ n : Z, (n @ (int (i32))); ⌜n > 0⌝.

  (* Specifications for function [evar_instantiate_wrong]. *)
  Definition type_of_evar_instantiate_wrong :=
    fn(∀ l : (list Z); True)
      → ∃ lret : (list Z), (void); ⌜lret = replicate (length l) 0⌝ ∗ ⌜length l = length lret⌝.

  (* Specifications for function [return_multiple_of_8]. *)
  Definition type_of_return_multiple_of_8 :=
    fn(∀ () : (); True) → ∃ n : Z, (n @ (int (i32))); ⌜(8 | n)⌝.

  (* Specifications for function [return_multiple_of_5]. *)
  Definition type_of_return_multiple_of_5 :=
    fn(∀ () : (); True) → ∃ n : Z, ((n * 5) @ (int (i32))); True.
End spec.
