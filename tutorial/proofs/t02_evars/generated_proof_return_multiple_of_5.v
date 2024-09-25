From refinedc.typing Require Import typing.
From refinedc.tutorial.t02_evars Require Import generated_code.
From refinedc.tutorial.t02_evars Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/t02_evars.c]. *)
Section proof_return_multiple_of_5.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [return_multiple_of_5]. *)
  Lemma type_return_multiple_of_5 :
    ⊢ typed_function impl_return_multiple_of_5 type_of_return_multiple_of_5.
  Proof.
    Local Open Scope printing_sugar.
    start_function "return_multiple_of_5" ([]).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "return_multiple_of_5" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "return_multiple_of_5".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "return_multiple_of_5".
  Qed.
End proof_return_multiple_of_5.
