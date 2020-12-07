From refinedc.typing Require Import typing.
From refinedc.linux.early_alloc Require Import generated_code.
From refinedc.linux.early_alloc Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [linux/early_alloc.c]. *)
Section proof_hyp_early_alloc_page1.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [hyp_early_alloc_page1]. *)
  Lemma type_hyp_early_alloc_page1 (cur1 size1 clear_page : loc) :
    global_locs !! "cur1" = Some cur1 →
    global_locs !! "size1" = Some size1 →
    clear_page ◁ᵥ clear_page @ function_ptr type_of_clear_page -∗
    typed_function (impl_hyp_early_alloc_page1 cur1 size1 clear_page) type_of_hyp_early_alloc_page1.
  Proof.
    start_function "hyp_early_alloc_page1" (n) => arg_arg local_ret.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "hyp_early_alloc_page1" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "hyp_early_alloc_page1".
  Qed.
End proof_hyp_early_alloc_page1.
