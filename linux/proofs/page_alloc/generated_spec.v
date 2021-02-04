From refinedc.typing Require Import typing.
From refinedc.linux.page_alloc Require Import generated_code.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [linux/page_alloc.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Inlined code. *)

  Definition PAGE_SIZE : N := 4096.
  Definition PAGE_LAYOUT := ly_with_align (N.to_nat PAGE_SIZE) (N.to_nat PAGE_SIZE).

  (* Type definitions. *)

  (* Function [atomic_thread_fence] has been skipped. *)

  (* Function [atomic_signal_fence] has been skipped. *)

  (* Specifications for function [sl_init]. *)
  Definition type_of_sl_init :=
    fn(∀ p : loc; (p @ (&own (uninit (struct_spinlock)))); True)
      → ∃ gamma : lock_id, (void); (p ◁ₗ (spinlock (gamma))).

  (* Specifications for function [sl_lock]. *)
  Definition type_of_sl_lock :=
    fn(∀ (p, gamma, beta) : loc * lock_id * own_state; (p @ (&frac{beta} (spinlock (gamma)))); True)
      → ∃ () : (), (void); (p ◁ₗ{beta} (spinlock (gamma))) ∗ (lock_token gamma []).

  (* Specifications for function [sl_unlock]. *)
  Definition type_of_sl_unlock :=
    fn(∀ (p, gamma, beta) : loc * lock_id * own_state; (p @ (&frac{beta} (spinlock (gamma)))); (lock_token gamma []))
      → ∃ () : (), (void); (p ◁ₗ{beta} (spinlock (gamma))).

  (* Specifications for function [clear_page]. *)
  Definition type_of_clear_page :=
    fn(∀ p : loc; (p @ (&own (uninit (PAGE_LAYOUT)))); True)
      → ∃ () : (), (void); (p ◁ₗ (zeroed (PAGE_LAYOUT))).

  (* Function [memset] has been skipped. *)

  (* Function [hyp_panic] has been skipped. *)

  (* Function [__list_add_valid] has been skipped. *)

  (* Function [__list_del_entry_valid] has been skipped. *)

  (* Function [INIT_LIST_HEAD] has been skipped. *)

  (* Function [__list_add] has been skipped. *)

  (* Function [list_add] has been skipped. *)

  (* Function [list_add_tail] has been skipped. *)

  (* Function [__list_del] has been skipped. *)

  (* Function [__list_del_entry] has been skipped. *)

  (* Function [list_del_init] has been skipped. *)

  (* Function [list_empty] has been skipped. *)

  (* Function [hyp_phys_to_virt] has been skipped. *)

  (* Function [hyp_virt_to_phys] has been skipped. *)

  (* Function [hyp_page_count] has been skipped. *)

  (* Function [hyp_alloc_pages] has been skipped. *)

  (* Function [hyp_get_page] has been skipped. *)

  (* Function [hyp_put_page] has been skipped. *)

  (* Function [hyp_pool_init] has been skipped. *)

  (* Function [__find_buddy] has been skipped. *)

  (* Function [__hyp_attach_page] has been skipped. *)

  (* Function [__hyp_extract_page] has been skipped. *)

  (* Function [clear_hyp_page] has been skipped. *)

  (* Function [__hyp_alloc_pages] has been skipped. *)
End spec.
