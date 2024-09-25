From refinedc.typing Require Import typing.
From refinedc.tutorial.VerifyThis.t04_loops Require Import generated_code.
From refinedc.tutorial.VerifyThis.t04_loops Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/VerifyThis/t04_loops.c]. *)
Section proof_append_loop_2.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [append_loop_2]. *)
  Lemma type_append_loop_2 :
    ⊢ typed_function impl_append_loop_2 type_of_append_loop_2.
  Proof.
    Local Open Scope printing_sugar.
    start_function "append_loop_2" ([[p xs] ys]) => arg_l arg_k local_end.
    prepare_parameters (p xs ys).
    split_blocks ((
      <[ "#1" :=
        ∃ pl : loc,
        ∃ xs_suffix : list Z,
        arg_k ◁ₗ (ys @ (list_t)) ∗
        local_end ◁ₗ (pl @ (&own (xs_suffix @ (list_t)))) ∗
        arg_l ◁ₗ (p @ (&own (wand (pl ◁ₗ (xs_suffix ++ ys) @ list_t) ((xs ++ ys) @ (list_t)))))
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "append_loop_2" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "append_loop_2" "#1".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "append_loop_2".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "append_loop_2".
  Qed.
End proof_append_loop_2.
