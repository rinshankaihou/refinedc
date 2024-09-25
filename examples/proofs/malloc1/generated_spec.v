From refinedc.typing Require Import typing.
From refinedc.examples.malloc1 Require Import generated_code.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/malloc1.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Definition of type [freelist_t]. *)
  Definition freelist_t_rec : (nat * nat → type) → (nat * nat → type) := (λ self patt__,
    let len := patt__.1 in
    let entry_size := patt__.2 in
    (((0 < len)%nat) @ (optional (&own (
      ∃ₜ (nextlen : nat),
      constrained (padded (struct struct_freelist [@{type}
        (self (nextlen, (entry_size)))
      ]) struct_freelist (ly_with_align entry_size entry_size)) (
        ⌜len = S nextlen⌝
      )
    )) null))
  )%I.
  Global Typeclasses Opaque freelist_t_rec.

  Global Instance freelist_t_rec_le : TypeMono freelist_t_rec.
  Proof. solve_type_proper. Qed.

  Definition freelist_t (entry_size : nat) : rtype (nat) := {|
    rty r__ := freelist_t_rec (type_fixpoint freelist_t_rec) (r__, entry_size)
  |}.

  Lemma freelist_t_unfold (entry_size : nat) (len : nat):
    (len @ freelist_t entry_size)%I ≡@{type} (
      (((0 < len)%nat) @ (optional (&own (
        ∃ₜ (nextlen : nat),
        constrained (padded (struct struct_freelist [@{type}
          (nextlen @ (freelist_t (entry_size)))
        ]) struct_freelist (ly_with_align entry_size entry_size)) (
          ⌜len = S nextlen⌝
        )
      )) null))
    )%I.
  Proof. apply: (type_fixpoint_unfold2 freelist_t_rec). Qed.

  Definition freelist_t_simplify_hyp_place_inst_generated (entry_size : nat) patt__ :=
    [instance simplify_hyp_place_eq _ _ (freelist_t_unfold (entry_size : nat) patt__) with 100%N].
  Global Existing Instance freelist_t_simplify_hyp_place_inst_generated.
  Definition freelist_t_simplify_goal_place_inst_generated (entry_size : nat) patt__ :=
    [instance simplify_goal_place_eq _ _ (freelist_t_unfold (entry_size : nat) patt__) with 100%N].
  Global Existing Instance freelist_t_simplify_goal_place_inst_generated.

  Definition freelist_t_simplify_hyp_val_inst_generated (entry_size : nat) patt__ :=
    [instance simplify_hyp_val_eq _ _ (freelist_t_unfold (entry_size : nat) patt__) with 100%N].
  Global Existing Instance freelist_t_simplify_hyp_val_inst_generated.
  Definition freelist_t_simplify_goal_val_inst_generated (entry_size : nat) patt__ :=
    [instance simplify_goal_val_eq _ _ (freelist_t_unfold (entry_size : nat) patt__) with 100%N].
  Global Existing Instance freelist_t_simplify_goal_val_inst_generated.

  (* Definition of type [slab]. *)
  Definition slab_rec : (nat * nat → type) → (nat * nat → type) := (λ self patt__,
    let len := patt__.1 in
    let entry_size := patt__.2 in
    ∃ₜ (entries_in_chunk : nat) (entries_in_entry_list : nat) (chunk_p : loc),
    constrained (struct struct_slab [@{type}
      ((entries_in_chunk * entry_size) @ (int (size_t))) ;
      (entry_size @ (int (size_t))) ;
      (chunk_p @ (&own (uninit (ly_with_align (entries_in_chunk * entry_size) entry_size)))) ;
      (entries_in_entry_list @ (freelist_t (entry_size)))
    ]) (
      ⌜(layout_of struct_freelist) ⊑ ly_with_align entry_size entry_size⌝ ∗
      ⌜len = (entries_in_chunk + entries_in_entry_list)%nat⌝
    )
  )%I.
  Global Typeclasses Opaque slab_rec.

  Global Instance slab_rec_le : TypeMono slab_rec.
  Proof. solve_type_proper. Qed.

  Definition slab (entry_size : nat) : rtype (nat) := {|
    rty r__ := slab_rec (type_fixpoint slab_rec) (r__, entry_size)
  |}.

  Lemma slab_unfold (entry_size : nat) (len : nat):
    (len @ slab entry_size)%I ≡@{type} (
      ∃ₜ (entries_in_chunk : nat) (entries_in_entry_list : nat) (chunk_p : loc),
      constrained (struct struct_slab [@{type}
        ((entries_in_chunk * entry_size) @ (int (size_t))) ;
        (entry_size @ (int (size_t))) ;
        (chunk_p @ (&own (uninit (ly_with_align (entries_in_chunk * entry_size) entry_size)))) ;
        (entries_in_entry_list @ (freelist_t (entry_size)))
      ]) (
        ⌜(layout_of struct_freelist) ⊑ ly_with_align entry_size entry_size⌝ ∗
        ⌜len = (entries_in_chunk + entries_in_entry_list)%nat⌝
      )
    )%I.
  Proof. apply: (type_fixpoint_unfold2 slab_rec). Qed.

  Definition slab_simplify_hyp_place_inst_generated (entry_size : nat) patt__ :=
    [instance simplify_hyp_place_eq _ _ (slab_unfold (entry_size : nat) patt__) with 100%N].
  Global Existing Instance slab_simplify_hyp_place_inst_generated.
  Definition slab_simplify_goal_place_inst_generated (entry_size : nat) patt__ :=
    [instance simplify_goal_place_eq _ _ (slab_unfold (entry_size : nat) patt__) with 100%N].
  Global Existing Instance slab_simplify_goal_place_inst_generated.

  Definition slab_simplify_hyp_val_inst_generated (entry_size : nat) patt__ :=
    [instance simplify_hyp_val_eq _ _ (slab_unfold (entry_size : nat) patt__) with 100%N].
  Global Existing Instance slab_simplify_hyp_val_inst_generated.
  Definition slab_simplify_goal_val_inst_generated (entry_size : nat) patt__ :=
    [instance simplify_goal_val_eq _ _ (slab_unfold (entry_size : nat) patt__) with 100%N].
  Global Existing Instance slab_simplify_goal_val_inst_generated.

  (* Specifications for function [__builtin_ffsll]. *)
  Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (i32))); True.

  (* Specifications for function [slab_init]. *)
  Definition type_of_slab_init :=
    fn(∀ (p, chunk_p, n, entry_size) : loc * loc * nat * nat; (p @ (&own (uninit (struct_slab)))), (chunk_p @ (&own (uninit (ly_with_align (n * entry_size) entry_size)))), ((n * entry_size) @ (int (size_t))), (entry_size @ (int (size_t))); ⌜(layout_of struct_freelist) ⊑ ly_with_align entry_size entry_size⌝)
      → ∃ () : (), (void); (p ◁ₗ (slab (entry_size))).

  (* Specifications for function [slab_alloc]. *)
  Definition type_of_slab_alloc :=
    fn(∀ (p, n, entry_size) : loc * nat * nat; (p @ (&own (n @ (slab (entry_size))))); True)
      → ∃ () : (), (((0 < n)%nat) @ (optional (&own (uninit (ly_with_align entry_size entry_size))) null)); (p ◁ₗ (((n - 1)%nat) @ (slab (entry_size)))).

  (* Specifications for function [slab_free]. *)
  Definition type_of_slab_free :=
    fn(∀ (p, fp, n, entry_size) : loc * loc * nat * nat; (p @ (&own (n @ (slab (entry_size))))), (fp @ (&own (uninit (ly_with_align entry_size entry_size)))); True)
      → ∃ () : (), (void); (p ◁ₗ (((n + 1)%nat) @ (slab (entry_size)))).
End spec.

Notation "freelist_t< entry_size >" := (freelist_t entry_size)
  (only printing, format "'freelist_t<' entry_size '>'") : printing_sugar.
Notation "slab< entry_size >" := (slab entry_size)
  (only printing, format "'slab<' entry_size '>'") : printing_sugar.

Global Typeclasses Opaque freelist_t_rec.
Global Typeclasses Opaque freelist_t.
Global Typeclasses Opaque slab_rec.
Global Typeclasses Opaque slab.
