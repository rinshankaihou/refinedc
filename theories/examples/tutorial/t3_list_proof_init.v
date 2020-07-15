From refinedc.typing Require Import typing.
From refinedc.examples.tutorial Require Import t3_list_code.
From refinedc.examples.tutorial Require Import t3_list_spec.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t3_list.c]. *)
Section proof_init.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [init]. *)
  Lemma type_init :
    ⊢ typed_function impl_init type_of_init.
  Proof.
    start_function "init" ([]).
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "init" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "init".
  Qed.
End proof_init.
