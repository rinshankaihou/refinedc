From refinedc.typing Require Import typing.
From refinedc.examples.mpool_simpl Require Import generated_code.
From refinedc.examples.mpool_simpl Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/mpool_simpl.c]. *)
Section proof_mpool_init.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [mpool_init]. *)
  Lemma type_mpool_init :
    ⊢ typed_function impl_mpool_init type_of_mpool_init.
  Proof.
    Local Open Scope printing_sugar.
    start_function "mpool_init" (p) => arg_p.
    prepare_parameters (p).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_init" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "mpool_init".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "mpool_init".
  Qed.
End proof_mpool_init.
