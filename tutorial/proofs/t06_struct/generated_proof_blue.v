From refinedc.typing Require Import typing.
From refinedc.tutorial.t06_struct Require Import generated_code.
From refinedc.tutorial.t06_struct Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t06_struct.c]. *)
Section proof_blue.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [blue]. *)
  Lemma type_blue :
    ⊢ typed_function impl_blue type_of_blue.
  Proof.
    Local Open Scope printing_sugar.
    start_function "blue" (b) => arg_b local_c.
    prepare_parameters (b).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "blue" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "blue".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "blue".
  Qed.
End proof_blue.
