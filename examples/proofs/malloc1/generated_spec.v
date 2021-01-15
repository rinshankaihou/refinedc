From refinedc.typing Require Import typing.
From refinedc.examples.malloc1 Require Import generated_code.
Set Default Proof Using "Type".

(* Generated from [examples/malloc1.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Definition of type [freelist_t]. *)
  Definition freelist_t_rec : (nat * nat -d> typeO) → (nat * nat -d> typeO) := (λ self patt__,
    let len := patt__.1 in
    let entry_size := patt__.2 in
    (((0 < len)%nat) @ (optional (&own (
      padded (struct struct_freelist [@{type}
        (guarded ("freelist_t_0") (apply_dfun self (((len - 1)%nat), (entry_size))))
      ]) struct_freelist (ly_with_align entry_size entry_size)
    )) null))
  )%I.
  Typeclasses Opaque freelist_t_rec.

  Global Instance freelist_t_rec_ne : Contractive freelist_t_rec.
  Proof. solve_type_proper. Qed.

  Definition freelist_t (entry_size : nat) : rtype := {|
    rty_type := nat;
    rty r__ := fixp freelist_t_rec (r__, entry_size)
  |}.

  Lemma freelist_t_unfold (entry_size : nat) (len : nat) :
    (len @ freelist_t entry_size)%I ≡@{type} (
      (((0 < len)%nat) @ (optional (&own (
        padded (struct struct_freelist [@{type}
          (guarded "freelist_t_0" (((len - 1)%nat) @ (freelist_t (entry_size))))
        ]) struct_freelist (ly_with_align entry_size entry_size)
      )) null))
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance freelist_t_rmovable (entry_size : nat) : RMovable (freelist_t entry_size) :=
    {| rmovable 'len := movable_eq _ _ (freelist_t_unfold entry_size len) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance freelist_t_simplify_hyp_place_inst l_ β_ (entry_size : nat) (len : nat) :
    SimplifyHypPlace l_ β_ (len @ freelist_t entry_size)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (freelist_t_unfold _ _)).
  Global Instance freelist_t_simplify_goal_place_inst l_ β_ (entry_size : nat) (len : nat) :
    SimplifyGoalPlace l_ β_ (len @ freelist_t entry_size)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (freelist_t_unfold _ _)).

  Global Program Instance freelist_t_simplify_hyp_val_inst v_ (entry_size : nat) (len : nat) :
    SimplifyHypVal v_ (len @ freelist_t entry_size)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (freelist_t_unfold _ _) T _).
  Next Obligation. done. Qed.
  Global Program Instance freelist_t_simplify_goal_val_inst v_ (entry_size : nat) (len : nat) :
    SimplifyGoalVal v_ (len @ freelist_t entry_size)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (freelist_t_unfold _ _) T _).
  Next Obligation. done. Qed.

  (* Definition of type [slab]. *)
  Definition slab_rec : (nat * nat -d> typeO) → (nat * nat -d> typeO) := (λ self patt__,
    let len := patt__.1 in
    let entry_size := patt__.2 in
    tyexists (λ entries_in_chunk : nat,
    tyexists (λ entries_in_entry_list : nat,
    tyexists (λ chunk_p : loc,
    constrained (struct struct_slab [@{type}
      ((entries_in_chunk * entry_size) @ (int (size_t))) ;
      (entry_size @ (int (size_t))) ;
      (chunk_p @ (&own (uninit (ly_with_align (entries_in_chunk * entry_size) entry_size)))) ;
      (entries_in_entry_list @ (freelist_t (entry_size)))
    ]) (
      ⌜(layout_of struct_freelist) ⊑ ly_with_align entry_size entry_size⌝ ∗
      ⌜len = (entries_in_chunk + entries_in_entry_list)%nat⌝
    ))))
  )%I.
  Typeclasses Opaque slab_rec.

  Global Instance slab_rec_ne : Contractive slab_rec.
  Proof. solve_type_proper. Qed.

  Definition slab (entry_size : nat) : rtype := {|
    rty_type := nat;
    rty r__ := fixp slab_rec (r__, entry_size)
  |}.

  Lemma slab_unfold (entry_size : nat) (len : nat) :
    (len @ slab entry_size)%I ≡@{type} (
      tyexists (λ entries_in_chunk : nat,
      tyexists (λ entries_in_entry_list : nat,
      tyexists (λ chunk_p : loc,
      constrained (struct struct_slab [@{type}
        ((entries_in_chunk * entry_size) @ (int (size_t))) ;
        (entry_size @ (int (size_t))) ;
        (chunk_p @ (&own (uninit (ly_with_align (entries_in_chunk * entry_size) entry_size)))) ;
        (entries_in_entry_list @ (freelist_t (entry_size)))
      ]) (
        ⌜(layout_of struct_freelist) ⊑ ly_with_align entry_size entry_size⌝ ∗
        ⌜len = (entries_in_chunk + entries_in_entry_list)%nat⌝
      ))))
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance slab_rmovable (entry_size : nat) : RMovable (slab entry_size) :=
    {| rmovable 'len := movable_eq _ _ (slab_unfold entry_size len) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance slab_simplify_hyp_place_inst l_ β_ (entry_size : nat) (len : nat) :
    SimplifyHypPlace l_ β_ (len @ slab entry_size)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (slab_unfold _ _)).
  Global Instance slab_simplify_goal_place_inst l_ β_ (entry_size : nat) (len : nat) :
    SimplifyGoalPlace l_ β_ (len @ slab entry_size)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (slab_unfold _ _)).

  Global Program Instance slab_simplify_hyp_val_inst v_ (entry_size : nat) (len : nat) :
    SimplifyHypVal v_ (len @ slab entry_size)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (slab_unfold _ _) T _).
  Next Obligation. done. Qed.
  Global Program Instance slab_simplify_goal_val_inst v_ (entry_size : nat) (len : nat) :
    SimplifyGoalVal v_ (len @ slab entry_size)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (slab_unfold _ _) T _).
  Next Obligation. done. Qed.

  (* Type definitions. *)

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

Typeclasses Opaque freelist_t_rec.
Typeclasses Opaque slab_rec.
