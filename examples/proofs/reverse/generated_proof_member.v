From refinedc.typing Require Import typing.
From refinedc.examples.reverse Require Import generated_code.
From refinedc.examples.reverse Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/reverse.c]. *)
Section proof_member.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [member]. *)
  Lemma type_member :
    ⊢ typed_function impl_member type_of_member.
  Proof.
    Local Open Scope printing_sugar.
    start_function "member" ([[l p] n]) => arg_p arg_k local_prev local_cur local_head.
    prepare_parameters (l p n).
    split_blocks ((
      <[ "#1" :=
        ∃ l1 : list Z,
        ∃ pc : loc,
        arg_k ◁ₗ (n @ (int (size_t))) ∗
        local_cur ◁ₗ uninit void* ∗
        local_head ◁ₗ uninit void* ∗
        local_prev ◁ₗ (pc @ (&own ((l1 `at_type` int size_t) @ (list_t)))) ∗
        arg_p ◁ₗ (p @ (&own (wand (pc ◁ₗ (l1 `at_type` int size_t) @ list_t) ((l `at_type` int size_t) @ (list_t))))) ∗
        ⌜n ∈ l ↔ n ∈ l1⌝
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "member" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "member" "#1".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try set_solver.
    all: print_sidecondition_goal "member".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "member".
  Qed.
End proof_member.
