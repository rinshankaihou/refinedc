From refinedc.typing Require Import typing.
From refinedc.linux.pkvm.early_alloc Require Import generated_code.
From refinedc.linux.pkvm.early_alloc Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.linux.pkvm.early_alloc Require Import instances.
Set Default Proof Using "Type".

(* Generated from [linux/pkvm/early_alloc.c]. *)
Section proof_hyp_early_alloc_init.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [hyp_early_alloc_init]. *)
  Lemma type_hyp_early_alloc_init (global_mem : loc) :
    global_locs !! "mem" = Some global_mem →
    ⊢ typed_function (impl_hyp_early_alloc_init global_mem) type_of_hyp_early_alloc_init.
  Proof.
    Local Open Scope printing_sugar.
    start_function "hyp_early_alloc_init" ([[l n] s]) => arg_virt arg_size.
    prepare_parameters (l n s).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "hyp_early_alloc_init" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: rewrite -> ly_size_PAGES in *; solve_goal.
    all: print_sidecondition_goal "hyp_early_alloc_init".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "hyp_early_alloc_init".
  Qed.
End proof_hyp_early_alloc_init.
