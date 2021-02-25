From refinedc.typing Require Import typing.
From refinedc.linux.pkvm.early_alloc Require Import generated_code.
From refinedc.linux.pkvm.early_alloc Require Import generated_spec.
From refinedc.linux.pkvm.early_alloc Require Import instances.
Set Default Proof Using "Type".

(* Generated from [linux/pkvm/early_alloc.c]. *)
Section proof_hyp_early_alloc_contig.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [hyp_early_alloc_contig]. *)
  Lemma type_hyp_early_alloc_contig (global_mem global_clear_page : loc) :
    global_locs !! "mem" = Some global_mem →
    global_clear_page ◁ᵥ global_clear_page @ function_ptr type_of_clear_page -∗
    typed_function (impl_hyp_early_alloc_contig global_mem global_clear_page) type_of_hyp_early_alloc_contig.
  Proof.
    Open Scope printing_sugar.
    start_function "hyp_early_alloc_contig" ([[[base given] remaining] n]) => arg_nr_pages local_i local_ret local_p.
    split_blocks ((
      <[ "#3" :=
        ∃ i : nat,
        arg_nr_pages ◁ₗ (n @ (int (u32))) ∗
        local_i ◁ₗ (i @ (int (u32))) ∗
        local_p ◁ₗ (uninit (uintptr_t)) ∗
        local_ret ◁ₗ ((base.2 + given * PAGE_SIZE) @ (int (uintptr_t))) ∗
        ((base +ₗ given * PAGE_SIZE) ◁ₗ zeroed (PAGES i)) ∗
        ((base +ₗ (given + i) * PAGE_SIZE) ◁ₗ uninit (PAGES (Z.to_nat n - i)%nat)) ∗
        (global_with_type "mem" Own (((base, given + n, remaining - n)%Z) @ (region))) ∗
        ⌜i ≤ n⌝
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "hyp_early_alloc_contig" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "hyp_early_alloc_contig" "#3".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try rewrite -> Z.shiftl_mul_pow2 in *; try lia.
    all: rewrite ?ly_offset_PAGES; try solve_goal.
    all: print_sidecondition_goal "hyp_early_alloc_contig".
  Qed.
End proof_hyp_early_alloc_contig.
