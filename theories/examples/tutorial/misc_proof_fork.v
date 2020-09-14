From refinedc.typing Require Import typing.
From refinedc.examples.tutorial Require Import misc_code.
From refinedc.examples.tutorial Require Import misc_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/misc.c]. *)
Section proof_fork.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [fork]. *)
  Lemma type_fork :
    ⊢ typed_function impl_fork type_of_fork.
  Proof.
    start_function "fork" ([ty P]) => arg_fn arg_arg.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "fork" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "fork".
  Qed.
End proof_fork.
