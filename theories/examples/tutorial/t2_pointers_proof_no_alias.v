From refinedc.typing Require Import typing.
From refinedc.examples.tutorial Require Import t2_pointers_code.
From refinedc.examples.tutorial Require Import t2_pointers_spec.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t2_pointers.c]. *)
Section proof_no_alias.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [no_alias]. *)
  Lemma type_no_alias :
    ⊢ typed_function impl_no_alias type_of_no_alias.
  Proof.
    start_function "no_alias" ([p q]) => arg_a arg_b local_old_b.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "no_alias" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "no_alias".
  Qed.
End proof_no_alias.
