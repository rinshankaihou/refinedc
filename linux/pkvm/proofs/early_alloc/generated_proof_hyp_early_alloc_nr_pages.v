From refinedc.typing Require Import typing.
From refinedc.linux.pkvm.early_alloc Require Import generated_code.
From refinedc.linux.pkvm.early_alloc Require Import generated_spec.
From refinedc.linux.pkvm.early_alloc Require Import instances.
Set Default Proof Using "Type".

(* Generated from [linux/pkvm/early_alloc.c]. *)
Section proof_hyp_early_alloc_nr_pages.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [hyp_early_alloc_nr_pages]. *)
  Lemma type_hyp_early_alloc_nr_pages (global_mem : loc) :
    global_locs !! "mem" = Some global_mem →
    ⊢ typed_function (impl_hyp_early_alloc_nr_pages global_mem) type_of_hyp_early_alloc_nr_pages.
  Proof.
    Open Scope printing_sugar.
    start_function "hyp_early_alloc_nr_pages" ([[base given] remaining]).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "hyp_early_alloc_nr_pages" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: rewrite Z.add_simpl_l; try solve_goal.
    all: rewrite Z.shiftr_div_pow2 //= Z.div_mul //=.
    all: print_sidecondition_goal "hyp_early_alloc_nr_pages".
  Qed.
End proof_hyp_early_alloc_nr_pages.
