From refinedc.typing Require Import typing.
From refinedc.examples.tutorial Require Import t3_list_code.
From refinedc.examples.tutorial Require Import t3_list_spec.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t3_list.c]. *)
Section proof_append.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [append]. *)
  Lemma type_append :
    ⊢ typed_function impl_append type_of_append.
  Proof.
    start_function "append" ([[p l1] l2]) => arg_l1 arg_l2 local_end.
    split_blocks ((
      <[ "#1" :=
        ∃ pl : loc,
        ∃ l1_suffix : list type,
        arg_l2 ◁ₗ (l2 @ (list_t)) ∗
        local_end ◁ₗ (pl @ (&own (l1_suffix @ (list_t)))) ∗
        arg_l1 ◁ₗ (p @ (&own (wand (pl ◁ₗ (l1_suffix ++ l2) @ list_t) ((l1 ++ l2) @ (list_t)))))
    ]> $
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "append" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "append" "#1".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "append".
  Qed.
End proof_append.
