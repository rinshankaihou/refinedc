From refinedc.typing Require Import typing.
From refinedc.tutorial.t08_tree Require Import generated_code.
From refinedc.tutorial.t08_tree Require Import generated_spec.
From refinedc.tutorial.t08_tree Require Import t08_tree_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t08_tree.c]. *)
Section proof_sempty.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [sempty]. *)
  Lemma type_sempty (global_empty : loc) :
    global_empty ◁ᵥ global_empty @ function_ptr type_of_empty -∗
    typed_function (impl_sempty global_empty) type_of_sempty.
  Proof.
    Open Scope printing_sugar.
    start_function "sempty" ([]).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "sempty" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by apply: LeafRel; solve_goal.
    all: print_sidecondition_goal "sempty".
  Qed.
End proof_sempty.
