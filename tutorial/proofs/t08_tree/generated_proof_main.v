From refinedc.typing Require Import typing.
From refinedc.tutorial.t08_tree Require Import generated_code.
From refinedc.tutorial.t08_tree Require Import generated_spec.
From refinedc.tutorial.t08_tree Require Import t08_tree_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t08_tree.c]. *)
Section proof_main.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [main]. *)
  Lemma type_main (global_sempty global_sfree_tree global_sinit global_sinsert global_smember global_sremove : loc) :
    global_sempty ◁ᵥ global_sempty @ function_ptr type_of_sempty -∗
    global_sfree_tree ◁ᵥ global_sfree_tree @ function_ptr type_of_sfree_tree -∗
    global_sinit ◁ᵥ global_sinit @ function_ptr type_of_sinit -∗
    global_sinsert ◁ᵥ global_sinsert @ function_ptr type_of_sinsert -∗
    global_smember ◁ᵥ global_smember @ function_ptr type_of_smember -∗
    global_sremove ◁ᵥ global_sremove @ function_ptr type_of_sremove -∗
    typed_function (impl_main global_sempty global_sfree_tree global_sinit global_sinsert global_smember global_sremove) type_of_main.
  Proof.
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
