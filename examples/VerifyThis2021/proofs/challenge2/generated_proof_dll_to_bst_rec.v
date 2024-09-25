From refinedc.typing Require Import typing.
From refinedc.examples.VerifyThis2021.challenge2 Require Import generated_code.
From refinedc.examples.VerifyThis2021.challenge2 Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.VerifyThis2021.challenge2 Require Import defs.
Set Default Proof Using "Type".

(* Generated from [examples/VerifyThis2021/challenge2.c]. *)
Section proof_dll_to_bst_rec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [dll_to_bst_rec]. *)
  Lemma type_dll_to_bst_rec (global_dll_to_bst_rec : loc) :
    global_dll_to_bst_rec ◁ᵥ global_dll_to_bst_rec @ function_ptr type_of_dll_to_bst_rec -∗
    typed_function (impl_dll_to_bst_rec global_dll_to_bst_rec) type_of_dll_to_bst_rec.
  Proof.
    Local Open Scope printing_sugar.
    start_function "dll_to_bst_rec" ([[l p] n]) => arg_head arg_right arg_n local_left local_temp local_root.
    prepare_parameters (l p n).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "dll_to_bst_rec" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by apply: list_tree_eq_aux_Node_Z; solve_goal.
    all: try by apply: list_tree_eq_aux_is_Some; solve_goal.
    all: try by apply: list_tree_eq_aux_le; solve_goal.
    all: print_sidecondition_goal "dll_to_bst_rec".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "dll_to_bst_rec".
  Qed.
End proof_dll_to_bst_rec.
