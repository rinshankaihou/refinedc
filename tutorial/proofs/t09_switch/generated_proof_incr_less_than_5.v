From refinedc.typing Require Import typing.
From refinedc.tutorial.t09_switch Require Import generated_code.
From refinedc.tutorial.t09_switch Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/t09_switch.c]. *)
Section proof_incr_less_than_5.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [incr_less_than_5]. *)
  Lemma type_incr_less_than_5 :
    ⊢ typed_function impl_incr_less_than_5 type_of_incr_less_than_5.
  Proof.
    Local Open Scope printing_sugar.
    start_function "incr_less_than_5" (i) => arg_i local_o.
    prepare_parameters (i).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "incr_less_than_5" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "incr_less_than_5".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "incr_less_than_5".
  Qed.
End proof_incr_less_than_5.
