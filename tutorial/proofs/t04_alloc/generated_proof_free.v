From refinedc.typing Require Import typing.
From refinedc.tutorial.t04_alloc Require Import generated_code.
From refinedc.tutorial.t04_alloc Require Import generated_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [tutorial/t04_alloc.c]. *)
Section proof_free.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [free]. *)
  Lemma type_free (allocator_state sl_lock sl_unlock : loc) :
    global_locs !! "allocator_state" = Some allocator_state →
    global_initialized_types !! "allocator_state" = Some (GT () (λ '(), (alloc_state) : type)) →
    sl_lock ◁ᵥ sl_lock @ function_ptr type_of_sl_lock -∗
    sl_unlock ◁ᵥ sl_unlock @ function_ptr type_of_sl_unlock -∗
    typed_function (impl_free allocator_state sl_lock sl_unlock) type_of_free.
  Proof.
    start_function "free" (size) => arg_size arg_ptr local_entry.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "free" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by rewrite ?Nat2Z.inj_mul ?Z2Nat.id //; apply Z.divide_factor_r.
    all: print_sidecondition_goal "free".
  Qed.
End proof_free.
