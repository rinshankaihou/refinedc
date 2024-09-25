From refinedc.typing Require Import typing.
From refinedc.tutorial.t06_struct Require Import generated_code.
From refinedc.tutorial.t06_struct Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t06_struct.c]. *)
Section proof_getblue.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [getblue]. *)
  Lemma type_getblue :
    ⊢ typed_function impl_getblue type_of_getblue.
  Proof.
    Local Open Scope printing_sugar.
    start_function "getblue" ([[r g] b]) => arg_b.
    prepare_parameters (r g b).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "getblue" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "getblue".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "getblue".
  Qed.
End proof_getblue.
