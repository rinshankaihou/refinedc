From refinedc.typing Require Import typing.
From refinedc.examples.VerifyThis2021.challenge2 Require Import generated_code.
From refinedc.examples.VerifyThis2021.challenge2 Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.VerifyThis2021.challenge2 Require Import defs.
Set Default Proof Using "Type".

(* Generated from [examples/VerifyThis2021/challenge2.c]. *)
Section proof_dll_to_bst.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [dll_to_bst]. *)
  Lemma type_dll_to_bst (global_dll_to_bst_rec global_size_iter : loc) :
    global_dll_to_bst_rec ◁ᵥ global_dll_to_bst_rec @ function_ptr type_of_dll_to_bst_rec -∗
    global_size_iter ◁ᵥ global_size_iter @ function_ptr type_of_size_iter -∗
    typed_function (impl_dll_to_bst global_dll_to_bst_rec global_size_iter) type_of_dll_to_bst.
  Proof.
    Local Open Scope printing_sugar.
    start_function "dll_to_bst" (l) => arg_head local_right local_n.
    prepare_parameters (l).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "dll_to_bst" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by apply: tree_list_eq_full_length; solve_goal.
    all: print_sidecondition_goal "dll_to_bst".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "dll_to_bst".
  Qed.
End proof_dll_to_bst.
