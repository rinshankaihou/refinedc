From refinedc.typing Require Import typing.
From refinedc.examples.tutorial Require Import t3_list_code.
From refinedc.examples.tutorial Require Import t3_list_spec.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t3_list.c]. *)
Section proof_reverse.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [reverse]. *)
  Lemma type_reverse :
    ⊢ typed_function impl_reverse type_of_reverse.
  Proof.
    start_function "reverse" (l) => arg_p local_w local_t.
    split_blocks ((
      <[ "#1" :=
        ∃ l1 : list type,
        ∃ l2 : list type,
        local_t ◁ₗ uninit LPtr ∗
        local_w ◁ₗ (l1 @ (list_t)) ∗
        arg_p ◁ₗ (l2 @ (list_t)) ∗
        ⌜l = rev l1 ++ l2⌝
    ]> $
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "reverse" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "reverse" "#1".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "reverse".
  Qed.
End proof_reverse.
