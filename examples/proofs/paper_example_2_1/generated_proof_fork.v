From refinedc.typing Require Import typing.
From refinedc.examples.paper_example_2_1 Require Import generated_code.
From refinedc.examples.paper_example_2_1 Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/paper_example_2_1.c]. *)
Section proof_fork.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [fork]. *)
  Lemma type_fork :
    ⊢ typed_function impl_fork type_of_fork.
  Proof.
    Local Open Scope printing_sugar.
    start_function "fork" ([ty P]) => arg_fn arg_arg.
    prepare_parameters (ty P).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "fork" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "fork".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "fork".
  Qed.
End proof_fork.
