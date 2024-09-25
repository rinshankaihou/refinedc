From refinedc.typing Require Import typing.
From refinedc.linux.casestudies.early_alloc Require Import generated_code.
Set Default Proof Using "Type".

(* Generated from [linux/casestudies/early_alloc.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Inlined code. *)

  Definition PAGE_SIZE : N := 4096.
  Definition PAGE_LAYOUT := ly_with_align (N.to_nat PAGE_SIZE) (N.to_nat PAGE_SIZE).

  (* Function [hyp_early_alloc_nr_pages] has been skipped. *)

  (* Specifications for function [clear_page]. *)
  Definition type_of_clear_page :=
    fn(∀ p : loc; (p @ (&own (uninit (PAGE_LAYOUT)))); True)
      → ∃ () : (), (void); (p ◁ₗ (zeroed (PAGE_LAYOUT))).

  (* Function [hyp_early_alloc_page] has been skipped. *)

  (* Function [hyp_early_alloc_init] has been skipped. *)

  (* Specifications for function [hyp_early_alloc_page1]. *)
  Definition type_of_hyp_early_alloc_page1 :=
    fn(∀ n : nat; (uninit (void*)); (global_with_type "cur1" Own (&own (uninit (ly_set_size PAGE_LAYOUT n)))) ∗ (global_with_type "size1" Own (n @ (int (u64)))))
      → ∃ m : nat, (optionalO (λ _ : unit,   &own (zeroed (PAGE_LAYOUT))
      ) (null)); (global_with_type "size1" Own (m @ (int (u64)))) ∗ (global_with_type "cur1" Own (&own (uninit (ly_set_size PAGE_LAYOUT m)))).

  (* Specifications for function [hyp_early_alloc_init1]. *)
  Definition type_of_hyp_early_alloc_init1 :=
    fn(∀ n : nat; (&own (uninit (ly_set_size PAGE_LAYOUT n))), (n @ (int (u64))); (global_with_type "cur1" Own (uninit (void*))) ∗ (global_with_type "size1" Own (uninit (u64))) ∗ (global_with_type "base1" Own (uninit (void*))))
      → ∃ m : nat, (void); (global_with_type "size1" Own (m @ (int (u64)))) ∗ (global_with_type "cur1" Own (&own (uninit (ly_set_size PAGE_LAYOUT m)))) ∗ (global_with_type "base1" Own (uninit (void*))).
End spec.
