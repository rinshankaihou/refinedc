From refinedc.typing Require Import typing.
From refinedc.examples.VerifyThis2021.challenge1 Require Import generated_code.
From refinedc.examples.VerifyThis2021.challenge1 Require Import challenge1_lemmas.
Set Default Proof Using "Type".

(* Generated from [examples/VerifyThis2021/challenge1.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Definition of type [list_t]. *)
  Definition list_t_rec : ((list type) → type) → ((list type) → type) := (λ self l,
    ((maybe2 cons l) @ (optionalO (λ patt__,
      let ty := patt__.1 in
      let l := patt__.2 in
      &own (
        struct struct_list [@{type}
          (&own (ty)) ;
          (self (l))
        ]
      )
    ) null))
  )%I.
  Global Typeclasses Opaque list_t_rec.

  Global Instance list_t_rec_le : TypeMono list_t_rec.
  Proof. solve_type_proper. Qed.

  Definition list_t : rtype ((list type)) := {|
    rty r__ := list_t_rec (type_fixpoint list_t_rec) r__
  |}.

  Lemma list_t_unfold (l : (list type)):
    (l @ list_t)%I ≡@{type} (
      ((maybe2 cons l) @ (optionalO (λ patt__,
        let ty := patt__.1 in
        let l := patt__.2 in
        &own (
          struct struct_list [@{type}
            (&own (ty)) ;
            (l @ list_t)
          ]
        )
      ) null))
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

  (* Specifications for function [next]. *)
  Definition type_of_next :=
    fn(∀ (A, p) : (list Z) * loc; (p @ (&own (array (i32) (A `at_type` int i32)))), ((length A) @ (int (i32))); ⌜0 < length A⌝)
      → ∃ (Aret, b) : (list Z) * bool, (b @ (builtin_boolean)); (p ◁ₗ (array (i32) (Aret `at_type` int i32))) ∗ ⌜next_perm A (if b then (Some Aret) else None)⌝ ∗ ⌜if b then True else A = Aret⌝ ∗ ⌜A ≡ₚ Aret⌝.

  (* Specifications for function [list_new]. *)
  Definition type_of_list_new :=
    fn(∀ () : (); True) → ∃ () : (), (([]) @ (list_t)); True.

  (* Specifications for function [list_snoc]. *)
  Definition type_of_list_snoc :=
    fn(∀ (p, l, ty) : loc * (list type) * type; (p @ (&own (l @ (list_t)))), (&own (ty)); True)
      → ∃ () : (), (void); (p ◁ₗ ((l ++ [ty]) @ (list_t))).

  (* Specifications for function [sort]. *)
  Definition type_of_sort :=
    fn(∀ (p, A) : loc * (list Z); (p @ (&own (array (i32) (A `at_type` int i32)))), ((length A) @ (int (i32))); True)
      → ∃ Asorted : (list Z), (void); ⌜Asorted ≡ₚ A⌝ ∗ ⌜Sorted Z.le Asorted⌝ ∗ (p ◁ₗ (array (i32) (Asorted `at_type` int i32))).

  (* Specifications for function [copy_array]. *)
  Definition type_of_copy_array :=
    fn(∀ (p, A) : loc * (list Z); (p @ (&own (array (i32) (A `at_type` int i32)))), ((length A) @ (int (i32))); True)
      → ∃ () : (), (&own (array (i32) (A `at_type` int i32))); (p ◁ₗ (array (i32) (A `at_type` int i32))).

  (* Specifications for function [permut]. *)
  Definition type_of_permut :=
    fn(∀ (p, A) : loc * (list Z); (p @ (&own (array (i32) (A `at_type` int i32)))), ((length A) @ (int (i32))); True)
      → ∃ ps : (list (list Z)), (((λ p, (array i32 (p `at_type` int i32))) <$> ps) @ (list_t)); ⌜∀ i p1 p2, ps !! i = Some p1 → ps !! (S i) = Some p2 → next_perm p1 (Some p2)⌝ ∗ ⌜∀ p, last ps = Some p → next_perm p None⌝ ∗ ⌜∀ A', 0 < length A → A ≡ₚ A' → A' ∈ ps⌝ ∗ ⌜NoDup ps⌝.
End spec.

Global Typeclasses Opaque list_t_rec.
Global Typeclasses Opaque list_t.
