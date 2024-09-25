From refinedc.typing Require Import typing.
From refinedc.examples.queue Require Import generated_code.
From caesium Require Import builtins_specs.
From refinedc.typing Require Import malloc.
Set Default Proof Using "Type".

(* Generated from [examples/queue.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!mallocG Σ}.

  (* Definition of type [queue_elem]. *)
  Definition queue_elem_rec : (type * type → type) → (type * type → type) := (λ self patt__,
    let ty := patt__.1 in
    let cont := patt__.2 in
    (&own (malloced (ly_size struct_queue_elem) (
      struct struct_queue_elem [@{type}
        (&own (ty)) ;
        (cont)
      ]
    )))
  )%I.
  Global Typeclasses Opaque queue_elem_rec.

  Global Instance queue_elem_rec_le : TypeMono queue_elem_rec.
  Proof. solve_type_proper. Qed.

  Definition queue_elem (cont : type) : rtype (type) := {|
    rty r__ := queue_elem_rec (type_fixpoint queue_elem_rec) (r__, cont)
  |}.

  Lemma queue_elem_unfold (cont : type) (ty : type):
    (ty @ queue_elem cont)%I ≡@{type} (
      (&own (malloced (ly_size struct_queue_elem) (
        struct struct_queue_elem [@{type}
          (&own (ty)) ;
          (cont)
        ]
      )))
    )%I.
  Proof. apply: (type_fixpoint_unfold2 queue_elem_rec). Qed.

  Definition queue_elem_simplify_hyp_place_inst_generated (cont : type) patt__ :=
    [instance simplify_hyp_place_eq _ _ (queue_elem_unfold (cont : type) patt__) with 100%N].
  Global Existing Instance queue_elem_simplify_hyp_place_inst_generated.
  Definition queue_elem_simplify_goal_place_inst_generated (cont : type) patt__ :=
    [instance simplify_goal_place_eq _ _ (queue_elem_unfold (cont : type) patt__) with 100%N].
  Global Existing Instance queue_elem_simplify_goal_place_inst_generated.

  Definition queue_elem_simplify_hyp_val_inst_generated (cont : type) patt__ :=
    [instance simplify_hyp_val_eq _ _ (queue_elem_unfold (cont : type) patt__) with 100%N].
  Global Existing Instance queue_elem_simplify_hyp_val_inst_generated.
  Definition queue_elem_simplify_goal_val_inst_generated (cont : type) patt__ :=
    [instance simplify_goal_val_eq _ _ (queue_elem_unfold (cont : type) patt__) with 100%N].
  Global Existing Instance queue_elem_simplify_goal_val_inst_generated.

  (* Definition of type [queue]. *)
  Definition queue_rec : ((list type) → type) → ((list type) → type) := (λ self tys,
    (∃ₜ p, own_constrained (tyown_constraint (p) (null)) (&own (
      struct struct_queue [@{type}
        (tyfold ((λ ty x, ty @ queue_elem x) <$> tys) (place (p))) ;
        (&own (place (p)))
      ]
    )))
  )%I.
  Global Typeclasses Opaque queue_rec.

  Global Instance queue_rec_le : TypeMono queue_rec.
  Proof. solve_type_proper. Qed.

  Definition queue : rtype ((list type)) := {|
    rty r__ := queue_rec (type_fixpoint queue_rec) r__
  |}.

  Lemma queue_unfold (tys : (list type)):
    (tys @ queue)%I ≡@{type} (
      (∃ₜ p, own_constrained (tyown_constraint (p) (null)) (&own (
        struct struct_queue [@{type}
          (tyfold ((λ ty x, ty @ queue_elem x) <$> tys) (place (p))) ;
          (&own (place (p)))
        ]
      )))
    )%I.
  Proof. apply: (type_fixpoint_unfold2 queue_rec). Qed.

  Definition queue_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (queue_unfold patt__) with 100%N].
  Global Existing Instance queue_simplify_hyp_place_inst_generated.
  Definition queue_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (queue_unfold patt__) with 100%N].
  Global Existing Instance queue_simplify_goal_place_inst_generated.

  Definition queue_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (queue_unfold patt__) with 100%N].
  Global Existing Instance queue_simplify_hyp_val_inst_generated.
  Definition queue_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (queue_unfold patt__) with 100%N].
  Global Existing Instance queue_simplify_goal_val_inst_generated.

  (* Specifications for function [__builtin_ffsll]. *)
  Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (i32))); True.

  (* Specifications for function [safe_exit]. *)
  Definition type_of_safe_exit :=
    fn(∀ () : (); True) → ∃ () : (), (void); ⌜False⌝.

  (* Specifications for function [malloc]. *)
  Definition type_of_malloc :=
    fn(∀ n : Z; (n @ (int (size_t))); True)
      → ∃ () : (), (optionalO (λ _ : unit,
        &own (malloced (n) (uninit (ly_max_align (Z.to_nat n))))
      ) (null)); True.

  (* Specifications for function [free]. *)
  Definition type_of_free :=
    fn(∀ n : Z; (&own (malloced_early (n) (uninit (ly_max_align (Z.to_nat n))))); True)
      → ∃ () : (), (void); True.

  (* Specifications for function [xmalloc]. *)
  Definition type_of_xmalloc :=
    fn(∀ n : Z; (n @ (int (size_t))); True)
      → ∃ () : (), (&own (malloced (n) (uninit (ly_max_align (Z.to_nat n))))); True.

  (* Specifications for function [init_queue]. *)
  Definition type_of_init_queue :=
    fn(∀ () : (); True) → ∃ () : (), (([]) @ (queue)); True.

  (* Specifications for function [is_empty]. *)
  Definition type_of_is_empty :=
    fn(∀ (p, tys) : loc * (list type); (p @ (&own ((tys) @ (queue)))); True)
      → ∃ () : (), ((bool_decide (tys ≠ [])) @ (builtin_boolean)); (p ◁ₗ ((tys) @ (queue))).

  (* Specifications for function [enqueue]. *)
  Definition type_of_enqueue :=
    fn(∀ (p, tys, ty) : loc * (list type) * type; (p @ (&own ((tys) @ (queue)))), (&own (ty)); True)
      → ∃ () : (), (void); (p ◁ₗ ((tys ++ [ty]) @ (queue))).

  (* Specifications for function [dequeue]. *)
  Definition type_of_dequeue :=
    fn(∀ (p, tys) : loc * (list type); (p @ (&own ((tys) @ (queue)))); True)
      → ∃ () : (), ((maybe2 cons tys) @ (optionalO (λ patt__,
        let ty := patt__.1 in
        let _ := patt__.2 in
        &own (ty) ) null)); (p ◁ₗ ((tail tys) @ (queue))).
End spec.

Notation "queue_elem< cont >" := (queue_elem cont)
  (only printing, format "'queue_elem<' cont '>'") : printing_sugar.

Global Typeclasses Opaque queue_elem_rec.
Global Typeclasses Opaque queue_elem.
Global Typeclasses Opaque queue_rec.
Global Typeclasses Opaque queue.
