From refinedc.typing Require Import typing.
From refinedc.examples.lock Require Import generated_code.
From refinedc.examples.lock Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/lock.c]. *)
Section proof_write_outside.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [write_outside]. *)
  Lemma type_write_outside :
    ⊢ typed_function impl_write_outside type_of_write_outside.
  Proof.
    Local Open Scope printing_sugar.
    start_function "write_outside" ([[[[p n] n1] n2] n3]) => arg_t arg_n.
    prepare_parameters (p n n1 n2 n3).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "write_outside" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "write_outside".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "write_outside".
  Qed.
End proof_write_outside.
