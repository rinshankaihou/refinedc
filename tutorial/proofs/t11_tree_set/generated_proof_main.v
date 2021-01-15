From refinedc.typing Require Import typing.
From refinedc.tutorial.t11_tree_set Require Import generated_code.
From refinedc.tutorial.t11_tree_set Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t11_tree_set.c]. *)
Section proof_main.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [main]. *)
  Lemma type_main (global_empty global_free_tree global_init global_insert global_member global_remove : loc) :
    global_empty ◁ᵥ global_empty @ function_ptr type_of_empty -∗
    global_free_tree ◁ᵥ global_free_tree @ function_ptr type_of_free_tree -∗
    global_init ◁ᵥ global_init @ function_ptr type_of_init -∗
    global_insert ◁ᵥ global_insert @ function_ptr type_of_insert -∗
    global_member ◁ᵥ global_member @ function_ptr type_of_member -∗
    global_remove ◁ᵥ global_remove @ function_ptr type_of_remove -∗
    typed_function (impl_main global_empty global_free_tree global_init global_insert global_member global_remove) type_of_main.
  Proof.
    Open Scope printing_sugar.
    start_function "main" ([]) => local_t.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "main" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "main".
  Qed.
End proof_main.
