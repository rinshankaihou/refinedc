From refinedc.typing Require Import typing.
From refinedc.tutorial.quicksort_solution Require Import generated_code.
From refinedc.tutorial.quicksort_solution Require Import list_proofs.
Set Default Proof Using "Type".

(* Generated from [tutorial/quicksort_solution.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Definition of type [list_t]. *)
  Definition list_t_rec : ((list Z) → type) → ((list Z) → type) := (λ self xs,
    ((xs <> []) @ (optional (&own (
      ∃ₜ (y : Z) (ys : list Z),
      constrained (struct struct_list_node [@{type}
        (y @ (int (i32))) ;
        (self (ys))
      ]) (
        ⌜xs = y :: ys⌝
      )
    )) (null)))
  )%I.
  Global Typeclasses Opaque list_t_rec.

  Global Instance list_t_rec_le : TypeMono list_t_rec.
  Proof. solve_type_proper. Qed.

  Definition list_t : rtype ((list Z)) := {|
    rty r__ := list_t_rec (type_fixpoint list_t_rec) r__
  |}.

  Lemma list_t_unfold (xs : (list Z)):
    (xs @ list_t)%I ≡@{type} (
      ((xs <> []) @ (optional (&own (
        ∃ₜ (y : Z) (ys : list Z),
        constrained (struct struct_list_node [@{type}
          (y @ (int (i32))) ;
          (ys @ list_t)
        ]) (
          ⌜xs = y :: ys⌝
        )
      )) (null)))
    )%I.
  Proof. apply: (type_fixpoint_unfold2 list_t_rec). Qed.

  Definition list_t_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (list_t_unfold patt__) with 100%N].
  Global Existing Instance list_t_simplify_hyp_place_inst_generated.
  Definition list_t_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (list_t_unfold patt__) with 100%N].
  Global Existing Instance list_t_simplify_goal_place_inst_generated.

  Definition list_t_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (list_t_unfold patt__) with 100%N].
  Global Existing Instance list_t_simplify_hyp_val_inst_generated.
  Definition list_t_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (list_t_unfold patt__) with 100%N].
  Global Existing Instance list_t_simplify_goal_val_inst_generated.

  (* Specifications for function [append]. *)
  Definition type_of_append :=
    fn(∀ (p, xs, ys) : loc * (list Z) * (list Z); (p @ (&own (xs @ (list_t)))), (ys @ (list_t)); True)
      → ∃ () : (), (void); (p ◁ₗ ((xs ++ ys) @ (list_t))).

  (* Specifications for function [partition]. *)
  Definition type_of_partition :=
    fn(∀ (p, xs, z) : loc * (list Z) * Z; (p @ (&own (xs @ (list_t)))), (z @ (int (i32))); True)
      → ∃ () : (), ((filter (λ v, z <= v) xs) @ (list_t)); (p ◁ₗ ((filter (λ v, v < z) xs) @ (list_t))).

  (* Specifications for function [quicksort]. *)
  Definition type_of_quicksort :=
    fn(∀ (list_l, l) : (list Z) * loc; (l @ (&own (list_l @ (list_t)))); True)
      → ∃ sorted_l : (list Z), (void); (l ◁ₗ (sorted_l @ (list_t))) ∗ ⌜Permutation list_l sorted_l⌝ ∗ ⌜Sorted Z.le sorted_l⌝.
End spec.

Global Typeclasses Opaque list_t_rec.
Global Typeclasses Opaque list_t.
