From refinedc.typing Require Import typing.
From refinedc.examples.pointers Require Import generated_code.
From refinedc.examples.pointers Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/pointers.c]. *)
Section proof_read_int.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [read_int]. *)
  Lemma type_read_int :
    ⊢ typed_function impl_read_int type_of_read_int.
  Proof.
    Local Open Scope printing_sugar.
    start_function "read_int" ([p n]) => arg_a.
    prepare_parameters (p n).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "read_int" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "read_int".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "read_int".
  Qed.
End proof_read_int.
