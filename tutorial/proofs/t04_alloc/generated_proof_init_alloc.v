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
  Lemma type_init_alloc (global_allocator_state global_sl_init : loc) :
    global_locs !! "allocator_state" = Some global_allocator_state →
    global_initialized_types !! "allocator_state" = Some (GT () (λ '(), (alloc_state) : type)) →
    global_sl_init ◁ᵥ global_sl_init @ function_ptr type_of_sl_init -∗
    typed_function (impl_init_alloc global_allocator_state global_sl_init) type_of_init_alloc.
  Proof.
    Open Scope printing_sugar.
    start_function "init_alloc" ([]).
    split_blocks ((
      <[ "#1" :=
        (global_allocator_state ◁ₗ (alloc_state))
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "init_alloc" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "init_alloc" "#1".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "init_alloc".
  Qed.
End proof_init_alloc.
