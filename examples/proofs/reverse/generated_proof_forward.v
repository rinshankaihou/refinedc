From refinedc.typing Require Import typing.
From refinedc.examples.reverse Require Import generated_code.
From refinedc.examples.reverse Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/reverse.c]. *)
Section proof_forward.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [forward]. *)
  Lemma type_forward :
    ⊢ typed_function impl_forward type_of_forward.
  Proof.
    start_function "forward" (l) => arg_p local_prev local_cur.
    split_blocks ((
      <[ "#1" :=
        ∃ l1 : list type,
        ∃ pc : loc,
        local_cur ◁ₗ uninit LPtr ∗
        local_prev ◁ₗ (pc @ (&own (l1 @ (list_t)))) ∗
        arg_p ◁ₗ (wand (pc ◁ₗ l1 @ list_t) (l @ (list_t)))
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "forward" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "forward" "#1".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "forward".
  Qed.
End proof_forward.
