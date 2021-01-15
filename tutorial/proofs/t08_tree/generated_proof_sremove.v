From refinedc.typing Require Import typing.
From refinedc.tutorial.t08_tree Require Import generated_code.
From refinedc.tutorial.t08_tree Require Import generated_spec.
From refinedc.tutorial.t08_tree Require Import t08_tree_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t08_tree.c]. *)
Section proof_sremove.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [sremove]. *)
  Lemma type_sremove (global_remove : loc) :
    global_remove ◁ᵥ global_remove @ function_ptr type_of_remove -∗
    typed_function (impl_sremove global_remove) type_of_sremove.
  Proof.
    Open Scope printing_sugar.
    start_function "sremove" ([[p s] k]) => arg_t arg_k.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "sremove" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by apply: tree_rel_remove; solve_goal.
    all: print_sidecondition_goal "sremove".
  Qed.
End proof_sremove.
