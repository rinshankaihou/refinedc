From refinedc.typing Require Import typing.
From refinedc.examples.tutorial Require Import t11_tree_set_code.
From refinedc.examples.tutorial Require Import t11_tree_set_spec.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t11_tree_set.c]. *)
Section proof_main.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [main]. *)
  Lemma type_main (empty init free_tree member insert remove : loc) :
    empty ◁ᵥ empty @ function_ptr type_of_empty -∗
    init ◁ᵥ init @ function_ptr type_of_init -∗
    free_tree ◁ᵥ free_tree @ function_ptr type_of_free_tree -∗
    member ◁ᵥ member @ function_ptr type_of_member -∗
    insert ◁ᵥ insert @ function_ptr type_of_insert -∗
    remove ◁ᵥ remove @ function_ptr type_of_remove -∗
    typed_function (impl_main empty init free_tree member insert remove) type_of_main.
  Proof.
    start_function "main" ([]) => local_t.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "main" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "main".
  Qed.
End proof_main.
