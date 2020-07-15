From refinedc.typing Require Import typing.
From refinedc.examples.tutorial Require Import t2_pointers_code.
From refinedc.examples.tutorial Require Import t2_pointers_spec.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t2_pointers.c]. *)
Section proof_read_int.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [read_int]. *)
  Lemma type_read_int :
    ⊢ typed_function impl_read_int type_of_read_int.
  Proof.
    start_function "read_int" ([p n]) => arg_a.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "read_int" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "read_int".
  Qed.
End proof_read_int.
