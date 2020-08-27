From refinedc.typing Require Import typing.
From refinedc.examples.misc Require Import shift_code.
From refinedc.examples.misc Require Import shift_spec.
Set Default Proof Using "Type".

(* Generated from [theories/examples/misc/shift.c]. *)
Section proof_times_two.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [times_two]. *)
  Lemma type_times_two :
    ⊢ typed_function impl_times_two type_of_times_two.
  Proof.
    start_function "times_two" (x) => arg_x.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "times_two" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "times_two".
  Qed.
End proof_times_two.
