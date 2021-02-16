From refinedc.typing Require Import typing.
From refinedc.linux.pkvm.early_alloc Require Import generated_code.
From refinedc.linux.pkvm.early_alloc Require Import generated_spec.
From refinedc.linux.pkvm.early_alloc Require Import instances.
Set Default Proof Using "Type".

(* Generated from [linux/pkvm/early_alloc.c]. *)
Section proof_hyp_early_alloc_contig.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [hyp_early_alloc_contig]. *)
  Lemma type_hyp_early_alloc_contig (global_mem : loc) :
    global_locs !! "mem" = Some global_mem →
    ⊢ typed_function (impl_hyp_early_alloc_contig global_mem) type_of_hyp_early_alloc_contig.
  Proof.
    Open Scope printing_sugar.
    start_function "hyp_early_alloc_contig" ([[[base given] remaining] n]) => arg_nr_pages local_i local_ret local_p.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "hyp_early_alloc_contig" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: unfold PAGE_SIZE, PAGE_SHIFT in *; try solve_goal.
    + assert (0 ≤ n ≪ 12); last by lia. by apply Z.shiftl_nonneg.
    + transitivity max_alloc_end; last done; etransitivity; last exact H10; rewrite Z.shiftl_mul_pow2 -?Z.add_assoc => //=; apply -> Z.add_le_mono_l; lia.
    + rewrite Z.shiftl_mul_pow2 in H18 => //. lia.
    + rewrite Z.shiftl_mul_pow2 //=. lia.
    + apply: has_layout_loc_trans' => //. by rewrite ly_offset_PAGES.
    all: print_sidecondition_goal "hyp_early_alloc_contig".
  Qed.
End proof_hyp_early_alloc_contig.
