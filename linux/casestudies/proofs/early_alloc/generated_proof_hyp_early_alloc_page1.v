From refinedc.typing Require Import typing.
From refinedc.linux.casestudies.early_alloc Require Import generated_code.
From refinedc.linux.casestudies.early_alloc Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [linux/casestudies/early_alloc.c]. *)
Section proof_hyp_early_alloc_page1.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [hyp_early_alloc_page1]. *)
  Lemma type_hyp_early_alloc_page1 (global_cur1 global_size1 global_clear_page : loc) :
    global_locs !! "cur1" = Some global_cur1 →
    global_locs !! "size1" = Some global_size1 →
    global_clear_page ◁ᵥ global_clear_page @ function_ptr type_of_clear_page -∗
    typed_function (impl_hyp_early_alloc_page1 global_cur1 global_size1 global_clear_page) type_of_hyp_early_alloc_page1.
  Proof.
    Open Scope printing_sugar.
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
