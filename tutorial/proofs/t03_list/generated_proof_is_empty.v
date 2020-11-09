From refinedc.typing Require Import typing.
From refinedc.tutorial.t03_list Require Import generated_code.
From refinedc.tutorial.t03_list Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t03_list.c]. *)
Section proof_is_empty.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [is_empty]. *)
  Lemma type_is_empty :
    ⊢ typed_function impl_is_empty type_of_is_empty.
  Proof.
    start_function "is_empty" ([p l]) => arg_l.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "is_empty" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "is_empty".
  Qed.
End proof_is_empty.
