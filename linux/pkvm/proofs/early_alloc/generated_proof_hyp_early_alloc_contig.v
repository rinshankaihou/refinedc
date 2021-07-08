From refinedc.typing Require Import typing.
From refinedc.linux.pkvm.early_alloc Require Import generated_code.
From refinedc.linux.pkvm.early_alloc Require Import generated_spec.
From refinedc.linux.pkvm.early_alloc Require Import instances.
Set Default Proof Using "Type".

(* Generated from [linux/pkvm/early_alloc.c]. *)
Section proof_hyp_early_alloc_contig.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [hyp_early_alloc_contig]. *)
  Lemma type_hyp_early_alloc_contig (global_mem global_copy_alloc_id global_memset : loc) :
    global_locs !! "mem" = Some global_mem →
    global_copy_alloc_id ◁ᵥ global_copy_alloc_id @ inline_function_ptr impl_copy_alloc_id -∗
    global_memset ◁ᵥ global_memset @ function_ptr type_of_memset -∗
    typed_function (impl_hyp_early_alloc_contig global_mem global_copy_alloc_id global_memset) type_of_hyp_early_alloc_contig.
  Proof.
    Open Scope printing_sugar.
    start_function "hyp_early_alloc_contig" ([[[base given] remaining] n]) => arg_nr_pages local_size local_ret.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "hyp_early_alloc_contig" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try rewrite -> Z.shiftl_mul_pow2 in *; try lia.
    all: rewrite ?ly_offset_PAGES; try solve_goal.
    all: print_sidecondition_goal "hyp_early_alloc_contig".
  Qed.
End proof_hyp_early_alloc_contig.
