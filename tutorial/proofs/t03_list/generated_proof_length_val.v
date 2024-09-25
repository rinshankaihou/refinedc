From refinedc.typing Require Import typing.
From refinedc.tutorial.t03_list Require Import generated_code.
From refinedc.tutorial.t03_list Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/t03_list.c]. *)
Section proof_length_val.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [length_val]. *)
  Lemma type_length_val :
    ⊢ typed_function impl_length_val type_of_length_val.
  Proof.
    Local Open Scope printing_sugar.
    start_function "length_val" ([v l]) => arg_p local_len.
    prepare_parameters (v l).
    split_blocks ((
      <[ "#1" :=
        ∃ v2 : val,
        ∃ l1 : list type,
        arg_p ◁ₗ (at_value (v2) (l1 @ (list_t))) ∗
        local_len ◁ₗ ((length l - length l1) @ (int (size_t))) ∗
        (v ◁ᵥ (wand_val (void*) (v2 ◁ᵥ l1 @ list_t) (l @ (list_t))))
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "length_val" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "length_val" "#1".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "length_val".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "length_val".
  Qed.
End proof_length_val.
