From refinedc.typing Require Import typing.
From refinedc.tutorial.t04_alloc Require Import generated_code.
From refinedc.tutorial.t04_alloc Require Import generated_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [tutorial/t04_alloc.c]. *)
Section proof_init_alloc.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [init_alloc]. *)
  Lemma type_init_alloc (allocator_state sl_init : loc) :
    global_locs !! "allocator_state" = Some allocator_state →
    global_initialized_types !! "allocator_state" = Some (GT () (λ '(), (alloc_state) : type)) →
    sl_init ◁ᵥ sl_init @ function_ptr type_of_sl_init -∗
    typed_function (impl_init_alloc allocator_state sl_init) type_of_init_alloc.
  Proof.
    start_function "init_alloc" ([]).
    split_blocks ((
      <[ "#1" :=
        (allocator_state ◁ₗ (alloc_state))
    ]> $
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "init_alloc" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "init_alloc" "#1".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "init_alloc".
  Qed.
End proof_init_alloc.
