From refinedc.typing Require Import typing.
From refinedc.linux.early_alloc Require Import generated_code.
From refinedc.linux.early_alloc Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [linux/early_alloc.c]. *)
Section proof_hyp_early_alloc_init1.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [hyp_early_alloc_init1]. *)
  Lemma type_hyp_early_alloc_init1 (base1 cur1 size1 : loc) :
    global_locs !! "base1" = Some base1 →
    global_locs !! "cur1" = Some cur1 →
    global_locs !! "size1" = Some size1 →
    ⊢ typed_function (impl_hyp_early_alloc_init1 base1 cur1 size1) type_of_hyp_early_alloc_init1.
  Proof.
    start_function "hyp_early_alloc_init1" (n) => arg_virt arg_size.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "hyp_early_alloc_init1" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "hyp_early_alloc_init1".
  Qed.
End proof_hyp_early_alloc_init1.
