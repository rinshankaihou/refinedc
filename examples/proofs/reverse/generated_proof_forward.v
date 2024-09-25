From refinedc.typing Require Import typing.
From refinedc.examples.reverse Require Import generated_code.
From refinedc.examples.reverse Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/reverse.c]. *)
Section proof_forward.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [forward]. *)
  Lemma type_forward :
    ⊢ typed_function impl_forward type_of_forward.
  Proof.
    Local Open Scope printing_sugar.
    start_function "forward" (l) => arg_p local_prev local_cur.
    prepare_parameters (l).
    split_blocks ((
      <[ "#1" :=
        ∃ l1 : list type,
        ∃ pc : loc,
        local_cur ◁ₗ uninit void* ∗
        local_prev ◁ₗ (pc @ (&own (l1 @ (list_t)))) ∗
        arg_p ◁ₗ (wand (pc ◁ₗ l1 @ list_t) (l @ (list_t)))
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "forward" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "forward" "#1".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "forward".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "forward".
  Qed.
End proof_forward.
