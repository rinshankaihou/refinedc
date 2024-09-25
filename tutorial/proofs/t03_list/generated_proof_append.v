From refinedc.typing Require Import typing.
From refinedc.tutorial.t03_list Require Import generated_code.
From refinedc.tutorial.t03_list Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/t03_list.c]. *)
Section proof_append.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [append]. *)
  Lemma type_append :
    ⊢ typed_function impl_append type_of_append.
  Proof.
    Local Open Scope printing_sugar.
    start_function "append" ([[p l1] l2]) => arg_l1 arg_l2 local_end.
    prepare_parameters (p l1 l2).
    split_blocks ((
      <[ "#1" :=
        ∃ pl : loc,
        ∃ l1_suffix : list type,
        arg_l2 ◁ₗ (l2 @ (list_t)) ∗
        local_end ◁ₗ (pl @ (&own (l1_suffix @ (list_t)))) ∗
        arg_l1 ◁ₗ (p @ (&own (wand (pl ◁ₗ (l1_suffix ++ l2) @ list_t) ((l1 ++ l2) @ (list_t)))))
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "append" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "append" "#1".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "append".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "append".
  Qed.
End proof_append.
