From refinedc.typing Require Import typing.
From refinedc.examples.btree Require Import generated_code.
From refinedc.examples.btree Require Import btree_extra.
Set Default Proof Using "Type".

(* Generated from [examples/btree.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Inlined code. *)

  Definition alloc_initialized := initialized "allocator_state" ().
  (* B-tree order, should match the defined ORDER in C. *)
  Definition ORDER : nat := 5.

  (* Definition of type [btree_t]. *)
  Definition btree_t_rec : (btree_rfmt -d> typeO) → (btree_rfmt -d> typeO) := (λ self r,
    (tyexists (λ patt__ : nat * list Z * list type * list btree_rfmt, let n := patt__.1.1.1 in
    let ks := patt__.1.1.2 in
    let vs := patt__.1.2 in
    let cs := patt__.2 in
    constrained ((br_map r ≠ ∅) @ (optional (&own (
      constrained (struct struct_btree [@{type}
        (n @ (int (i32))) ;
        (array_p (i32) (ks `at_type` int i32) ((ORDER-1-n)%nat)) ;
        (array_p (LPtr) ((λ ty, (&own ty : type)) <$> vs) ((ORDER-1-n)%nat)) ;
        (guarded "btree_t_0" (array_p (LPtr) (cs `at_type`  (tyexists (λ rfmt__, apply_dfun self (rfmt__))) ) ((ORDER-1-n)%nat))) ;
        ((br_height r) @ (int (i32)))
      ]) (
        ⌜length ks = n⌝ ∗
        ⌜length vs = n⌝ ∗
        ⌜length cs = S n⌝
      )
    )) null)) ⌜btree_invariant ORDER r n ks vs cs⌝))
  )%I.
  Typeclasses Opaque btree_t_rec.

  Global Instance btree_t_rec_ne : Contractive btree_t_rec.
  Proof. solve_type_proper. Qed.

  Definition btree_t : rtype := {|
    rty_type := btree_rfmt;
    rty r__ := fixp btree_t_rec r__
  |}.

  Lemma btree_t_unfold (r : btree_rfmt) :
    (r @ btree_t)%I ≡@{type} (
      (tyexists (λ patt__ : nat * list Z * list type * list btree_rfmt, let n := patt__.1.1.1 in
      let ks := patt__.1.1.2 in
      let vs := patt__.1.2 in
      let cs := patt__.2 in
      constrained ((br_map r ≠ ∅) @ (optional (&own (
        constrained (struct struct_btree [@{type}
          (n @ (int (i32))) ;
          (array_p (i32) (ks `at_type` int i32) ((ORDER-1-n)%nat)) ;
          (array_p (LPtr) ((λ ty, (&own ty : type)) <$> vs) ((ORDER-1-n)%nat)) ;
          (guarded "btree_t_0" (array_p (LPtr) (cs `at_type`  (tyexists (λ rfmt__, rfmt__ @ btree_t)) ) ((ORDER-1-n)%nat))) ;
          ((br_height r) @ (int (i32)))
        ]) (
          ⌜length ks = n⌝ ∗
          ⌜length vs = n⌝ ∗
          ⌜length cs = S n⌝
        )
      )) null)) ⌜btree_invariant ORDER r n ks vs cs⌝))
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance btree_t_rmovable : RMovable btree_t :=
    {| rmovable 'r := movable_eq _ _ (btree_t_unfold r) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance btree_t_simplify_hyp_place_inst l_ β_ (r : btree_rfmt) :
    SimplifyHypPlace l_ β_ (r @ btree_t)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (btree_t_unfold _)).
  Global Instance btree_t_simplify_goal_place_inst l_ β_ (r : btree_rfmt) :
    SimplifyGoalPlace l_ β_ (r @ btree_t)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (btree_t_unfold _)).

  Global Program Instance btree_t_simplify_hyp_val_inst v_ (r : btree_rfmt) :
    SimplifyHypVal v_ (r @ btree_t)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (btree_t_unfold _) T _).
  Next Obligation. done. Qed.
  Global Program Instance btree_t_simplify_goal_val_inst v_ (r : btree_rfmt) :
    SimplifyGoalVal v_ (r @ btree_t)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (btree_t_unfold _) T _).
  Next Obligation. done. Qed.

  (* Type definitions. *)

  (* Specifications for function [alloc]. *)
  Definition type_of_alloc :=
    fn(∀ size : nat; (size @ (int (size_t))); ⌜size + 16 < it_max size_t⌝ ∗ ⌜(8 | size)⌝ ∗ (alloc_initialized))
      → ∃ () : (), (&own (uninit (mk_layout size 3))); True.

  (* Specifications for function [free]. *)
  Definition type_of_free :=
    fn(∀ size : nat; (size @ (int (size_t))), (&own (uninit (mk_layout size 3))); (alloc_initialized) ∗ ⌜(8 | size)⌝)
      → ∃ () : (), (void); True.

  (* Specifications for function [alloc_array]. *)
  Definition type_of_alloc_array :=
    fn(∀ (size, n) : nat * nat; (size @ (int (size_t))), (n @ (int (size_t))); ⌜size * n + 16 < it_max size_t⌝ ∗ ⌜(8 | size)⌝ ∗ (alloc_initialized))
      → ∃ () : (), (&own (array (mk_layout size 3) (replicate n (uninit (mk_layout size 3))))); True.

  (* Specifications for function [free_array]. *)
  Definition type_of_free_array :=
    fn(∀ (size, n) : nat * nat; (size @ (int (size_t))), (n @ (int (size_t))), (&own (array (mk_layout size 3) (replicate n (uninit (mk_layout size 3))))); ⌜size * n < it_max size_t⌝ ∗ ⌜(8 | size)⌝ ∗ (alloc_initialized))
      → ∃ () : (), (void); True.

  (* Specifications for function [new_btree]. *)
  Definition type_of_new_btree :=
    fn(∀ () : (); (alloc_initialized))
      → ∃ () : (), (&own ((BRroot 0%nat ∅) @ (btree_t))); True.

  (* Specifications for function [free_btree]. *)
  Definition type_of_free_btree :=
    fn(∀ () : (); (&own (btree_t)); (alloc_initialized))
      → ∃ () : (), (void); True.

  (* Specifications for function [btree_member]. *)
  Definition type_of_btree_member :=
    fn(∀ (p, h, m, k) : loc * nat * (gmap Z type) * Z; (p @ (&own ((BRroot h m) @ (btree_t)))), (k @ (int (i32))); True)
      → ∃ () : (), ((bool_decide (m !! k ≠ None)) @ (boolean (bool_it))); (p ◁ₗ ((BRroot h m) @ (btree_t))).

  (* Specifications for function [btree_find]. *)
  Definition type_of_btree_find :=
    fn(∀ (p, h, m, k) : loc * nat * (gmap Z type) * Z; (p @ (&own ((BRroot h m) @ (btree_t)))), (k @ (int (i32))); True)
      → ∃ v : loc, ((m !! k) @ (optionalO (λ ty,   v @ (&own (ty))
      ) null)); (p ◁ₗ ((BRroot h (make_sp v k m)) @ (btree_t))).

  (* Specifications for function [btree_insert]. *)
  Definition type_of_btree_insert :=
    fn(∀ (v, ty, p, h, m, k) : loc * type * loc * nat * (gmap Z type) * Z; (k @ (int (i32))), (v @ (&own (ty))), (p @ (&own ((BRroot h m) @ (btree_t)))); (alloc_initialized))
      → ∃ new_h : nat, (void); (p ◁ₗ ((BRroot new_h (<[k := ty]> m)) @ (btree_t))).

  (* Specifications for function [free_btree_nodes]. *)
  Definition type_of_free_btree_nodes :=
    fn(∀ p : loc; (p @ (&own (btree_t))); (alloc_initialized))
      → ∃ () : (), (void); (p ◁ₗ (null)).

  (* Specifications for function [key_index]. *)
  Definition type_of_key_index :=
    fn(∀ (p, l, n, k, sz) : loc * (list Z) * nat * Z * nat; (p @ (&own (array (it_layout i32) ((l `at_type` int i32) ++ replicate (sz - n)%nat (uninit i32 : type))))), (n @ (int (i32))), (k @ (int (i32))); ⌜n = length l⌝ ∗ ⌜StronglySorted (<) l⌝)
      → ∃ s : nat, (s @ (int (i32))); ⌜s ≤ n⌝ ∗ ⌜k ∈ l → l !! s = Some k⌝ ∗ ⌜¬ k ∈ l → StronglySorted (<) (take s l ++ k :: drop s l)⌝ ∗ (p ◁ₗ (array (it_layout i32) ((l `at_type` int i32) ++ replicate (sz - n)%nat (uninit i32 : type)))).

  (* Function [insert_br] has been skipped. *)

  (* Specifications for function [btree_make_root]. *)
  Definition type_of_btree_make_root :=
    fn(∀ (rl, rr, k, v, ty) : btree_rfmt * btree_rfmt * Z * loc * type; (rl @ (btree_t)), (rr @ (btree_t)), (k @ (int (i32))), (v @ (&own (ty))); (alloc_initialized) ∗ ⌜br_height rl + 1 < it_max i32⌝ ∗ ⌜br_height rl = br_height rr⌝ ∗ ⌜br_max rl = (k - 1)%Z⌝ ∗ ⌜br_min rr = (k + 1)%Z⌝ ∗ ⌜br_min rl = it_min i32⌝ ∗ ⌜br_max rr = (it_max i32 - 1)%Z⌝)
      → ∃ () : (), ((BR true (br_height rl + 1)%nat (br_min rl) (br_max rr) ({[k:=ty]} ∪ (br_map (non_root rl) ∪ br_map (non_root rr)))) @ (btree_t)); True.
End spec.

Typeclasses Opaque btree_t_rec.
