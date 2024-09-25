From refinedc.typing Require Import typing.
From refinedc.linux.casestudies.pgtable Require Import generated_code.
From refinedc.linux.casestudies.pgtable Require Import generated_spec.
From refinedc.linux.casestudies.pgtable Require Import pgtable_lemmas.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [linux/casestudies/pgtable.c]. *)
Section proof_BIT.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [BIT]. *)
  Lemma type_BIT :
    ⊢ typed_function impl_BIT type_of_BIT.
  Proof.
    Local Open Scope printing_sugar.
    start_function "BIT" (i) => arg_i.
    prepare_parameters (i).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "BIT" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: have ? := Z_shiftl_1_range i 64; try solve_goal.
    all: try by apply: bf_mask_bit; solve_goal.
    all: print_sidecondition_goal "BIT".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "BIT".
  Qed.
End proof_BIT.
