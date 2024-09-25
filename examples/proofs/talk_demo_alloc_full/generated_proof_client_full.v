From refinedc.typing Require Import typing.
From refinedc.examples.talk_demo_alloc_full Require Import generated_code.
From refinedc.examples.talk_demo_alloc_full Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/talk_demo_alloc_full.c]. *)
Section proof_client_full.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [client_full]. *)
  Lemma type_client_full (global_alloc_full : loc) :
    global_alloc_full ◁ᵥ global_alloc_full @ function_ptr type_of_alloc_full -∗
    typed_function (impl_client_full global_alloc_full) type_of_client_full.
  Proof.
    Local Open Scope printing_sugar.
    start_function "client_full" ([]) => arg_d local_s local_t.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "client_full" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "client_full".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "client_full".
  Qed.
End proof_client_full.
