From refinedc.typing Require Import typing.
From refinedc.examples.tutorial Require Import t1_basic_code.
From refinedc.examples.tutorial Require Import t1_basic_spec.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t1_basic.c]. *)
Section proof_init_int.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [init_int]. *)
  Lemma type_init_int :
    ⊢ typed_function impl_init_int type_of_init_int.
  Proof.
    start_function "init_int" (p) => arg_out.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "init_int" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "init_int".
  Qed.
End proof_init_int.
