From refinedc.typing Require Import typing.
From refinedc.tutorial.t09_switch Require Import generated_code.
Set Default Proof Using "Type".

(* Generated from [tutorial/t09_switch.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Type definitions. *)

  (* Specifications for function [test_switch]. *)
  Definition type_of_test_switch :=
    fn(∀ i : nat; (i @ (int (i32))); True)
      → ∃ () : (), ((if bool_decide (i ≤ 4)%nat then 4%nat else i) @ (int (i32))); True.

  (* Specifications for function [test_switch_default]. *)
  Definition type_of_test_switch_default :=
    fn(∀ i : nat; (i @ (int (i32))); ⌜i + 1 ≤ max_int i32⌝)
      → ∃ () : (), (((if bool_decide (i ≤ 4) then 5 else i + 1)%nat) @ (int (i32))); True.

  (* Specifications for function [incr_less_than_5]. *)
  Definition type_of_incr_less_than_5 :=
    fn(∀ i : nat; (i @ (int (i32))); True)
      → ∃ () : (), (((if bool_decide (i ≤ 4) then i + 1 else i)%nat) @ (int (i32))); True.

  (* Specifications for function [duffs_identity]. *)
  Definition type_of_duffs_identity :=
    fn(∀ i : Z; (i @ (int (i32))); ⌜0 < i⌝ ∗ ⌜i + 3 ≤ max_int i32⌝)
      → ∃ () : (), (i @ (int (i32))); True.
End spec.
