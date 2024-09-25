From refinedc.typing Require Import typing.
From refinedc.linux.casestudies.early_alloc Require Import generated_code.
From refinedc.linux.casestudies.early_alloc Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [linux/casestudies/early_alloc.c]. *)
Section proof_hyp_early_alloc_init1.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [hyp_early_alloc_init1]. *)
  Lemma type_hyp_early_alloc_init1 (global_base1 global_cur1 global_size1 : loc) :
    global_locs !! "base1" = Some global_base1 →
    global_locs !! "cur1" = Some global_cur1 →
    global_locs !! "size1" = Some global_size1 →
    ⊢ typed_function (impl_hyp_early_alloc_init1 global_base1 global_cur1 global_size1) type_of_hyp_early_alloc_init1.
  Proof.
    Local Open Scope printing_sugar.
    start_function "hyp_early_alloc_init1" (n) => arg_virt arg_size.
    prepare_parameters (n).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "hyp_early_alloc_init1" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "hyp_early_alloc_init1".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "hyp_early_alloc_init1".
  Qed.
End proof_hyp_early_alloc_init1.
