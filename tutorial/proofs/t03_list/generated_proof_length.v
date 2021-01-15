From refinedc.typing Require Import typing.
From refinedc.tutorial.t03_list Require Import generated_code.
From refinedc.tutorial.t03_list Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t03_list.c]. *)
Section proof_length.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [length]. *)
  Lemma type_length :
    ⊢ typed_function impl_length type_of_length.
  Proof.
    Open Scope printing_sugar.
    start_function "length" ([p l]) => arg_p local_len.
    split_blocks ((
      <[ "#1" :=
        ∃ q : loc,
        ∃ l1 : list type,
        arg_p ◁ₗ (q @ (&own (l1 @ (list_t)))) ∗
        local_len ◁ₗ ((length l - length l1) @ (int (size_t))) ∗
        (p ◁ₗ (wand (q ◁ₗ l1 @ list_t) (l @ (list_t))))
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "length" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "length" "#1".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "length".
  Qed.
End proof_length.
