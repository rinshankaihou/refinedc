From refinedc.typing Require Import typing.
From refinedc.tutorial.t02_evars Require Import generated_code.
From refinedc.tutorial.t02_evars Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/t02_evars.c]. *)
Section proof_evar_create_return_int.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [evar_create_return_int]. *)
  Lemma type_evar_create_return_int :
    ⊢ typed_function impl_evar_create_return_int type_of_evar_create_return_int.
  Proof.
    Local Open Scope printing_sugar.
    start_function "evar_create_return_int" ([]).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "evar_create_return_int" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "evar_create_return_int".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "evar_create_return_int".
  Qed.
End proof_evar_create_return_int.
