From refinedc.typing Require Import typing.
From refinedc.examples.binary_search Require Import generated_code.
From refinedc.examples.binary_search Require Import generated_spec.
From refinedc.examples.binary_search Require Import binary_search_extra.
Set Default Proof Using "Type".

(* Generated from [examples/binary_search.c]. *)
Section proof_compare_int.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [compare_int]. *)
  Lemma type_compare_int :
    ⊢ typed_function impl_compare_int type_of_compare_int.
  Proof.
    Open Scope printing_sugar.
    start_function "compare_int" ([[[x y] px] py]) => arg_x arg_y local_xi local_yi.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "compare_int" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "compare_int".
  Qed.
End proof_compare_int.
