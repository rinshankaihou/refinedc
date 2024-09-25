From refinedc.typing Require Import typing.
From refinedc.tutorial.VerifyThis.t04_loops Require Import generated_code.
From refinedc.tutorial.VerifyThis.t04_loops Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/VerifyThis/t04_loops.c]. *)
Section proof_reverse_2.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [reverse_2]. *)
  Lemma type_reverse_2 :
    ⊢ typed_function impl_reverse_2 type_of_reverse_2.
  Proof.
    Local Open Scope printing_sugar.
    start_function "reverse_2" (xs) => arg_l local_reversed local_tmp.
    prepare_parameters (xs).
    split_blocks ((
      <[ "#1" :=
        ∃ l1 : list Z,
        ∃ l2 : list Z,
        local_tmp ◁ₗ uninit void* ∗
        local_reversed ◁ₗ (l1 @ (list_t)) ∗
        arg_l ◁ₗ (l2 @ (list_t)) ∗
        ⌜xs = rev l1 ++ l2⌝
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "reverse_2" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "reverse_2" "#1".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "reverse_2".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "reverse_2".
  Qed.
End proof_reverse_2.
