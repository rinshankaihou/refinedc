From refinedc.typing Require Import typing.
From refinedc.tutorial.t06_struct Require Import generated_code.
From refinedc.tutorial.t06_struct Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t06_struct.c]. *)
Section proof_set_red.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [set_red]. *)
  Lemma type_set_red :
    ⊢ typed_function impl_set_red type_of_set_red.
  Proof.
    Local Open Scope printing_sugar.
    start_function "set_red" ([[p c] r]) => arg_c arg_r.
    prepare_parameters (p c r).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "set_red" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "set_red".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "set_red".
  Qed.
End proof_set_red.
