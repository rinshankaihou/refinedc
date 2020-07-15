From refinedc.typing Require Import typing.
From refinedc.examples.tutorial Require Import t10_loops_code.
From refinedc.examples.tutorial Require Import t10_loops_spec.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t10_loops.c]. *)
Section proof_loop_without_annot.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [loop_without_annot]. *)
  Lemma type_loop_without_annot :
    ⊢ typed_function impl_loop_without_annot type_of_loop_without_annot.
  Proof.
    start_function "loop_without_annot" ([]) => arg_a.
    split_blocks ((
      <[ "#7" :=
        arg_a ◁ₗ (int (i32))
    ]> $
      <[ "#1" :=
        arg_a ◁ₗ (int (i32))
    ]> $
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      <[ "#4" :=
        arg_a ◁ₗ (int (i32))
    ]> $
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "loop_without_annot" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "loop_without_annot" "#7".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "loop_without_annot" "#1".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "loop_without_annot".
  Qed.
End proof_loop_without_annot.
