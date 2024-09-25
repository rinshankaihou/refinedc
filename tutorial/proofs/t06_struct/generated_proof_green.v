From refinedc.typing Require Import typing.
From refinedc.tutorial.t06_struct Require Import generated_code.
From refinedc.tutorial.t06_struct Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t06_struct.c]. *)
Section proof_green.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [green]. *)
  Lemma type_green :
    ⊢ typed_function impl_green type_of_green.
  Proof.
    Local Open Scope printing_sugar.
    start_function "green" (g) => arg_g.
    prepare_parameters (g).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "green" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "green".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "green".
  Qed.
End proof_green.
