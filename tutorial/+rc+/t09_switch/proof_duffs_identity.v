From refinedc.typing Require Import typing.
From refinedc.tutorial.t09_switch Require Import code.
From refinedc.tutorial.t09_switch Require Import spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t09_switch.c]. *)
Section proof_duffs_identity.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [duffs_identity]. *)
  Lemma type_duffs_identity :
    ⊢ typed_function impl_duffs_identity type_of_duffs_identity.
  Proof.
    start_function "duffs_identity" (i) => arg_i local_o local_n.
    split_blocks ((
      <[ "#5" :=
        ∃ n : Z,
        arg_i ◁ₗ (i @ (int (i32))) ∗
        local_n ◁ₗ (n @ (int (i32))) ∗
        local_o ◁ₗ ((i - 4 * n) @ (int (i32))) ∗
        ⌜0 ≤ n⌝
    ]> $
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "duffs_identity" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "duffs_identity" "#5".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "duffs_identity".
  Qed.
End proof_duffs_identity.
