From refinedc.typing Require Import typing.
From refinedc.tutorial.t04_alloc Require Import generated_code.
From refinedc.tutorial.t04_alloc Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [tutorial/t04_alloc.c]. *)
Section proof_tfree.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [tfree]. *)
  Lemma type_tfree (global_allocator_state global_sl_lock global_sl_unlock : loc) :
    global_locs !! "allocator_state" = Some global_allocator_state →
    global_initialized_types !! "allocator_state" = Some (GT (()) (λ '(), (alloc_state) : type)%I) →
    global_sl_lock ◁ᵥ global_sl_lock @ function_ptr type_of_sl_lock -∗
    global_sl_unlock ◁ᵥ global_sl_unlock @ function_ptr type_of_sl_unlock -∗
    typed_function (impl_tfree global_allocator_state global_sl_lock global_sl_unlock) type_of_tfree.
  Proof.
    Local Open Scope printing_sugar.
    start_function "tfree" (size) => arg_size arg_ptr local_entry.
    prepare_parameters (size).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "tfree" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by rewrite ?Nat2Z.inj_mul ?Z2Nat.id //; apply Z.divide_factor_r.
    all: print_sidecondition_goal "tfree".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "tfree".
  Qed.
End proof_tfree.
