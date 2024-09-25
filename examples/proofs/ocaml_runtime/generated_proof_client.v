From refinedc.typing Require Import typing.
From refinedc.examples.ocaml_runtime Require Import generated_code.
From refinedc.examples.ocaml_runtime Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/ocaml_runtime.c]. *)
Section proof_client.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [client]. *)
  Lemma type_client :
    ⊢ typed_function impl_client type_of_client.
  Proof.
    Local Open Scope printing_sugar.
    start_function "client" ([]) => local_small_int local_large_int local_large_int_ptr local_v2 local_v1.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "client" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by unfold_aligned_to; rewrite (Z.land_ones _ 1) //; apply Z.mod_divide; [done| etrans; [|done]]; solve_goal.
    all: print_sidecondition_goal "client".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "client".
  Qed.
End proof_client.
