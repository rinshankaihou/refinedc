From refinedc.typing Require Import typing.
From refinedc.examples.talk_demo_alloc Require Import generated_code.
From refinedc.examples.talk_demo_alloc Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/talk_demo_alloc.c]. *)
Section proof_client.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [client]. *)
  Lemma type_client (global_alloc : loc) :
    global_alloc ◁ᵥ global_alloc @ function_ptr type_of_alloc -∗
    typed_function (impl_client global_alloc) type_of_client.
  Proof.
    Local Open Scope printing_sugar.
    start_function "client" ([]) => arg_d local_x local_a.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "client" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "client".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "client".
  Qed.
End proof_client.
