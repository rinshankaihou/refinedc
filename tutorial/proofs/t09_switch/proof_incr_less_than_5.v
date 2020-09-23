From refinedc.typing Require Import typing.
From refinedc.tutorial.t09_switch Require Import code.
From refinedc.tutorial.t09_switch Require Import spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t09_switch.c]. *)
Section proof_incr_less_than_5.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [incr_less_than_5]. *)
  Lemma type_incr_less_than_5 :
    ⊢ typed_function impl_incr_less_than_5 type_of_incr_less_than_5.
  Proof.
    start_function "incr_less_than_5" (i) => arg_i local_o.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "incr_less_than_5" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "incr_less_than_5".
  Qed.
End proof_incr_less_than_5.
