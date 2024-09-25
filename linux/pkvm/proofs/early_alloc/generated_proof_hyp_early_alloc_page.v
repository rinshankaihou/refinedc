From refinedc.typing Require Import typing.
From refinedc.linux.pkvm.early_alloc Require Import generated_code.
From refinedc.linux.pkvm.early_alloc Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.linux.pkvm.early_alloc Require Import instances.
Set Default Proof Using "Type".

(* Generated from [linux/pkvm/early_alloc.c]. *)
Section proof_hyp_early_alloc_page.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [hyp_early_alloc_page]. *)
  Lemma type_hyp_early_alloc_page (global_hyp_early_alloc_contig : loc) :
    global_hyp_early_alloc_contig ◁ᵥ global_hyp_early_alloc_contig @ function_ptr type_of_hyp_early_alloc_contig -∗
    typed_function (impl_hyp_early_alloc_page global_hyp_early_alloc_contig) type_of_hyp_early_alloc_page.
  Proof.
    Local Open Scope printing_sugar.
    start_function "hyp_early_alloc_page" ([[base given] remaining]) => arg_arg.
    prepare_parameters (base given remaining).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "hyp_early_alloc_page" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "hyp_early_alloc_page".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "hyp_early_alloc_page".
  Qed.
End proof_hyp_early_alloc_page.
