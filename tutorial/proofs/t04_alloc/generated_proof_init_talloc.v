From refinedc.typing Require Import typing.
From refinedc.tutorial.t04_alloc Require Import generated_code.
From refinedc.tutorial.t04_alloc Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [tutorial/t04_alloc.c]. *)
Section proof_init_talloc.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [init_talloc]. *)
  Lemma type_init_talloc (global_allocator_state global_sl_init : loc) :
    global_locs !! "allocator_state" = Some global_allocator_state →
    global_initialized_types !! "allocator_state" = Some (GT (()) (λ '(), (alloc_state) : type)%I) →
    global_sl_init ◁ᵥ global_sl_init @ function_ptr type_of_sl_init -∗
    typed_function (impl_init_talloc global_allocator_state global_sl_init) type_of_init_talloc.
  Proof.
    Local Open Scope printing_sugar.
    start_function "init_talloc" ([]).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      IPROP_HINT (ASSERT_COND "0") (λ _ : (),
        
        (global_allocator_state ◁ₗ (alloc_state))
        )%I ::
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "init_talloc" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "init_talloc".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "init_talloc".
  Qed.
End proof_init_talloc.
