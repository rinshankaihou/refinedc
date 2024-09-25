From refinedc.typing Require Import typing.
From refinedc.examples.mpool Require Import generated_code.
From refinedc.examples.mpool Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/mpool.c]. *)
Section proof_mpool_alloc_contiguous.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [mpool_alloc_contiguous]. *)
  Lemma type_mpool_alloc_contiguous (global_mpool_alloc_contiguous_no_fallback : loc) :
    global_mpool_alloc_contiguous_no_fallback ◁ᵥ global_mpool_alloc_contiguous_no_fallback @ function_ptr type_of_mpool_alloc_contiguous_no_fallback -∗
    typed_function (impl_mpool_alloc_contiguous global_mpool_alloc_contiguous_no_fallback) type_of_mpool_alloc_contiguous.
  Proof.
    Local Open Scope printing_sugar.
    start_function "mpool_alloc_contiguous" ([[[[[p q] n] entry_size] count] align]) => arg_p arg_count arg_align local_ret.
    prepare_parameters (p q n entry_size count align).
    split_blocks ((
      <[ "#2" :=
        ∃ n2 : nat,
        arg_count ◁ₗ (count @ (int (size_t))) ∗
        arg_align ◁ₗ (align @ (int (size_t))) ∗
        local_ret ◁ₗ uninit void* ∗
        arg_p ◁ₗ (optionalO (λ _ : unit,
          &shr (mpool (entry_size))
        ) null) ∗
        (p ◁ₗ{q} (n2 @ (mpool (entry_size)))) ∗
        ⌜q = Own → n2 <= n⌝
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_alloc_contiguous" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_alloc_contiguous" "#2".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "mpool_alloc_contiguous".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "mpool_alloc_contiguous".
  Qed.
End proof_mpool_alloc_contiguous.
