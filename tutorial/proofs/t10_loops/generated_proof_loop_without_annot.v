From refinedc.typing Require Import typing.
From refinedc.tutorial.t10_loops Require Import generated_code.
From refinedc.tutorial.t10_loops Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/t10_loops.c]. *)
Section proof_loop_without_annot.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [loop_without_annot]. *)
  Lemma type_loop_without_annot :
    ⊢ typed_function impl_loop_without_annot type_of_loop_without_annot.
  Proof.
    Local Open Scope printing_sugar.
    start_function "loop_without_annot" ([]) => arg_a arg_b arg_c local_z.
    split_blocks ((
      <[ "#7" :=
        arg_a ◁ₗ (int (i32)) ∗
        arg_b ◁ₗ (int (i32)) ∗
        arg_c ◁ₗ (int (i32)) ∗
        local_z ◁ₗ uninit (it_layout i32)
    ]> $
      <[ "#1" :=
        arg_a ◁ₗ (int (i32)) ∗
        arg_b ◁ₗ (int (i32)) ∗
        arg_c ◁ₗ (int (i32)) ∗
        local_z ◁ₗ uninit (it_layout i32)
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) (
      IPROP_HINT (BLOCK_PRECOND "#4") (λ _ : unit,True
        )%I ::
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "loop_without_annot" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "loop_without_annot" "#7".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "loop_without_annot" "#1".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "loop_without_annot".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "loop_without_annot".
  Qed.
End proof_loop_without_annot.
