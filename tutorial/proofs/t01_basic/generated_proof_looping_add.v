From refinedc.typing Require Import typing.
From refinedc.tutorial.t01_basic Require Import generated_code.
From refinedc.tutorial.t01_basic Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t01_basic.c]. *)
Section proof_looping_add.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [looping_add]. *)
  Lemma type_looping_add :
    ⊢ typed_function impl_looping_add type_of_looping_add.
  Proof.
    start_function "looping_add" ([va vb]) => arg_a arg_b.
    split_blocks ((
      <[ "#1" :=
        ∃ acc : Z,
        arg_a ◁ₗ (acc @ (int (i32))) ∗
        arg_b ◁ₗ ((va + vb - acc) @ (int (i32))) ∗
        ⌜0 <= acc⌝
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "looping_add" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "looping_add" "#1".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "looping_add".
  Qed.
End proof_looping_add.
