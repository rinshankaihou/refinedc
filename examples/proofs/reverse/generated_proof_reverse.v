From refinedc.typing Require Import typing.
From refinedc.examples.reverse Require Import generated_code.
From refinedc.examples.reverse Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/reverse.c]. *)
Section proof_reverse.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [reverse]. *)
  Lemma type_reverse :
    ⊢ typed_function impl_reverse type_of_reverse.
  Proof.
    Open Scope printing_sugar.
    start_function "reverse" (l) => arg_p local_v local_w local_t.
    split_blocks ((
      <[ "#1" :=
        ∃ l1 : list type,
        ∃ l2 : list type,
        local_t ◁ₗ uninit void* ∗
        local_w ◁ₗ (l1 @ (list_t)) ∗
        local_v ◁ₗ (l2 @ (list_t)) ∗
        arg_p ◁ₗ (uninit (void*)) ∗
        ⌜l = rev l1 ++ l2⌝
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "reverse" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "reverse" "#1".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "reverse".
  Qed.
End proof_reverse.
