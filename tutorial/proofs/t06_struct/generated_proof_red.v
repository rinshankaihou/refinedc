From refinedc.typing Require Import typing.
From refinedc.tutorial.t06_struct Require Import generated_code.
From refinedc.tutorial.t06_struct Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t06_struct.c]. *)
Section proof_red.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [red]. *)
  Lemma type_red :
    ⊢ typed_function impl_red type_of_red.
  Proof.
    Local Open Scope printing_sugar.
    start_function "red" (r) => arg_r local_c.
    prepare_parameters (r).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "red" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "red".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "red".
  Qed.
End proof_red.
