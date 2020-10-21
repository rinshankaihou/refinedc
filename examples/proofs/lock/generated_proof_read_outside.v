From refinedc.typing Require Import typing.
From refinedc.examples.lock Require Import generated_code.
From refinedc.examples.lock Require Import generated_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/lock.c]. *)
Section proof_read_outside.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [read_outside]. *)
  Lemma type_read_outside :
    ⊢ typed_function impl_read_outside type_of_read_outside.
  Proof.
    start_function "read_outside" ([[[p n1] n2] n3]) => arg_t.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "read_outside" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "read_outside".
  Qed.
End proof_read_outside.
