From refinedc.typing Require Import typing.
From refinedc.examples.btree Require Import generated_code.
From caesium Require Import builtins_specs.
From refinedc.typing Require Import malloc.
From refinedc.examples.btree Require Import btree_extra.
Set Default Proof Using "Type".

(* Generated from [examples/btree.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!mallocG Σ}.

  (* Inlined code. *)

  (* B-tree order, should match the defined ORDER in C. *)
  Definition ORDER : nat := 5.

  (* Definition of type [btree_t]. *)
  Definition btree_t_rec : (btree_rfmt → type) → (btree_rfmt → type) := (λ self r,
    (∃ₜ patt__ : nat * list Z * list type * list btree_rfmt, let n := patt__.1.1.1 in
    let ks := patt__.1.1.2 in
    let vs := patt__.1.2 in
    let cs := patt__.2 in
    constrained ((br_map r ≠ ∅) @ (optional (&own (
      constrained (struct struct_btree [@{type}
        (n @ (int (i32))) ;
        (array_p (i32) (ks `at_type` int i32) ((ORDER-1-n)%nat)) ;
        (array_p (void*) ((λ ty, (&own ty : type)) <$> vs) ((ORDER-1-n)%nat)) ;
        (array_p (void*) (cs `at_type`  (tyexists (λ rfmt__, self (rfmt__))) ) ((ORDER-1-n)%nat)) ;
        ((br_height r) @ (int (i32)))
      ]) (
        ⌜length ks = n⌝ ∗
        ⌜length vs = n⌝ ∗
        ⌜length cs = S n⌝
      )
    )) null)) ⌜btree_invariant ORDER r n ks vs cs⌝)
  )%I.
  Global Typeclasses Opaque btree_t_rec.

  Global Instance btree_t_rec_le : TypeMono btree_t_rec.
  Proof. solve_type_proper. Qed.

  Definition btree_t : rtype (btree_rfmt) := {|
    rty r__ := btree_t_rec (type_fixpoint btree_t_rec) r__
  |}.

  Lemma btree_t_unfold (r : btree_rfmt):
    (r @ btree_t)%I ≡@{type} (
      (∃ₜ patt__ : nat * list Z * list type * list btree_rfmt, let n := patt__.1.1.1 in
      let ks := patt__.1.1.2 in
      let vs := patt__.1.2 in
      let cs := patt__.2 in
      constrained ((br_map r ≠ ∅) @ (optional (&own (
        constrained (struct struct_btree [@{type}
          (n @ (int (i32))) ;
          (array_p (i32) (ks `at_type` int i32) ((ORDER-1-n)%nat)) ;
          (array_p (void*) ((λ ty, (&own ty : type)) <$> vs) ((ORDER-1-n)%nat)) ;
          (array_p (void*) (cs `at_type`  (tyexists (λ rfmt__, rfmt__ @ btree_t)) ) ((ORDER-1-n)%nat)) ;
          ((br_height r) @ (int (i32)))
        ]) (
          ⌜length ks = n⌝ ∗
          ⌜length vs = n⌝ ∗
          ⌜length cs = S n⌝
        )
      )) null)) ⌜btree_invariant ORDER r n ks vs cs⌝)
    )%I.
  Proof. apply: (type_fixpoint_unfold2 btree_t_rec). Qed.

  Definition btree_t_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (btree_t_unfold patt__) with 100%N].
  Global Existing Instance btree_t_simplify_hyp_place_inst_generated.
  Definition btree_t_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (btree_t_unfold patt__) with 100%N].
  Global Existing Instance btree_t_simplify_goal_place_inst_generated.

  Definition btree_t_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (btree_t_unfold patt__) with 100%N].
  Global Existing Instance btree_t_simplify_hyp_val_inst_generated.
  Definition btree_t_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (btree_t_unfold patt__) with 100%N].
  Global Existing Instance btree_t_simplify_goal_val_inst_generated.

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

  (* Specifications for function [new_btree]. *)
  Definition type_of_new_btree :=
    fn(∀ () : (); True)
      → ∃ () : (), (&own ((BRroot 0%nat ∅) @ (btree_t))); True.

  (* Specifications for function [free_btree]. *)
  Definition type_of_free_btree :=
    fn(∀ () : (); (&own (malloced (ly_size void*) (btree_t))); True)
      → ∃ () : (), (void); True.

  (* Specifications for function [btree_member]. *)
  Definition type_of_btree_member :=
    fn(∀ (p, h, m, k) : loc * nat * (gmap Z type) * Z; (p @ (&own ((BRroot h m) @ (btree_t)))), (k @ (int (i32))); True)
      → ∃ () : (), ((bool_decide (m !! k ≠ None)) @ (builtin_boolean)); (p ◁ₗ ((BRroot h m) @ (btree_t))).

  (* Specifications for function [btree_find]. *)
  Definition type_of_btree_find :=
    fn(∀ (p, h, m, k) : loc * nat * (gmap Z type) * Z; (p @ (&own ((BRroot h m) @ (btree_t)))), (k @ (int (i32))); True)
      → ∃ v : loc, ((m !! k) @ (optionalO (λ ty,   v @ (&own (ty))
      ) null)); (p ◁ₗ ((BRroot h (make_sp v k m)) @ (btree_t))).

  (* Specifications for function [btree_insert]. *)
  Definition type_of_btree_insert :=
    fn(∀ (v, ty, p, h, m, k) : loc * type * loc * nat * (gmap Z type) * Z; (k @ (int (i32))), (v @ (&own (ty))), (p @ (&own ((BRroot h m) @ (btree_t)))); True)
      → ∃ new_h : nat, (void); (p ◁ₗ ((BRroot new_h (<[k := ty]> m)) @ (btree_t))).

  (* Specifications for function [free_btree_nodes]. *)
  Definition type_of_free_btree_nodes :=
    fn(∀ p : loc; (p @ (&own (btree_t))); True)
      → ∃ () : (), (void); (p ◁ₗ (null)).

  (* Specifications for function [key_index]. *)
  Definition type_of_key_index :=
    fn(∀ (p, l, n, k, sz) : loc * (list Z) * nat * Z * nat; (p @ (&own (array (it_layout i32) ((l `at_type` int i32) ++ replicate (sz - n)%nat (uninit i32 : type))))), (n @ (int (i32))), (k @ (int (i32))); ⌜n = length l⌝ ∗ ⌜StronglySorted (<) l⌝)
      → ∃ s : nat, (s @ (int (i32))); ⌜s ≤ n⌝ ∗ ⌜k ∈ l → l !! s = Some k⌝ ∗ ⌜¬ k ∈ l → StronglySorted (<) (take s l ++ k :: drop s l)⌝ ∗ (p ◁ₗ (array (it_layout i32) ((l `at_type` int i32) ++ replicate (sz - n)%nat (uninit i32 : type)))).

  (* Function [insert_br] has been skipped. *)

  (* Specifications for function [btree_make_root]. *)
  Definition type_of_btree_make_root :=
    fn(∀ (rl, rr, k, v, ty) : btree_rfmt * btree_rfmt * Z * loc * type; (rl @ (btree_t)), (rr @ (btree_t)), (k @ (int (i32))), (v @ (&own (ty))); ⌜br_height rl + 1 ≤ max_int i32⌝ ∗ ⌜br_height rl = br_height rr⌝ ∗ ⌜br_max rl = (k - 1)%Z⌝ ∗ ⌜br_min rr = (k + 1)%Z⌝ ∗ ⌜br_min rl = min_int i32⌝ ∗ ⌜br_max rr = max_int i32⌝)
      → ∃ () : (), ((BR true (br_height rl + 1)%nat (br_min rl) (br_max rr) ({[k:=ty]} ∪ (br_map (non_root rl) ∪ br_map (non_root rr)))) @ (btree_t)); True.
End spec.

Global Typeclasses Opaque btree_t_rec.
Global Typeclasses Opaque btree_t.
