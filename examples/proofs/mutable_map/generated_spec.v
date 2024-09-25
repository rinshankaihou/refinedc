From refinedc.typing Require Import typing.
From refinedc.examples.mutable_map Require Import generated_code.
From caesium Require Import builtins_specs.
From refinedc.typing Require Import malloc.
From refinedc.examples.mutable_map Require Import mutable_map_extra.
Set Default Proof Using "Type".

(* Generated from [examples/mutable_map.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!mallocG Σ}.

  (* Definition of type [item] (tagged union). *)
  Definition item_tag (c : item_ref) : nat :=
    match c with
    | Empty => 0%nat
    | Entry _ _ => 1%nat
    | Tombstone _ => 2%nat
    end.

  Global Instance simpl_item_tag_Empty c :
    SimplBothRel (=) (item_tag c) 0%nat (c = Empty).
  Proof. split; destruct c; naive_solver. Qed.

  Global Instance simpl_item_tag_Entry c :
    SimplBothRel (=) (item_tag c) 1%nat (∃ (key : Z) (ty : type), c = Entry key ty).
  Proof. split; destruct c; naive_solver. Qed.

  Global Instance simpl_item_tag_Tombstone c :
    SimplBothRel (=) (item_tag c) 2%nat (∃ (key : Z), c = Tombstone key).
  Proof. split; destruct c; naive_solver. Qed.

  Program Definition item_tunion_info : tunion_info item_ref := {|
    ti_base_layout := struct_item;
    ti_tag_field_name := "tag";
    ti_union_field_name := "u";
    ti_union_layout := union_item_union;
    ti_tag := item_tag;
    ti_type c :=
      match c with
      | Empty => struct struct_empty [@{type} (int (size_t))]%I
      | Entry key ty => struct struct_entry [@{type} (key @ (int (size_t))); (&own (ty))]%I
      | Tombstone key => struct struct_tombstone [@{type} (key @ (int (size_t)))]%I
      end;
  |}.
  Next Obligation. done. Qed.
  Next Obligation. by case; eauto. Qed.

  Program Definition item : rtype _ := tunion item_tunion_info.

  (* Definition of type [fixed_size_map]. *)
  Definition fixed_size_map_rec : ((gmap Z type) * (list item_ref) * nat → type) → ((gmap Z type) * (list item_ref) * nat → type) := (λ self patt__,
    let mp := patt__.1.1 in
    let items := patt__.1.2 in
    let count := patt__.2 in
    constrained (struct struct_fixed_size_map [@{type}
      (&own (malloced (ly_size struct_item * length items) (array (struct_item) (items `at_type` item)))) ;
      (count @ (int (size_t))) ;
      ((length items) @ (int (size_t)))
    ]) (
      ⌜1 < length items⌝ ∗
      ⌜count = length (filter (λ x, x = Empty) items)⌝ ∗
      ⌜0 < count⌝ ∗
      ⌜fsm_invariant mp items⌝
    )
  )%I.
  Global Typeclasses Opaque fixed_size_map_rec.

  Global Instance fixed_size_map_rec_le : TypeMono fixed_size_map_rec.
  Proof. solve_type_proper. Qed.

  Definition fixed_size_map : rtype ((gmap Z type) * (list item_ref) * nat) := {|
    rty r__ := fixed_size_map_rec (type_fixpoint fixed_size_map_rec) r__
  |}.

  Lemma fixed_size_map_unfold (patt__ : (gmap Z type) * (list item_ref) * nat):
    (patt__ @ fixed_size_map)%I ≡@{type} (
      let mp := patt__.1.1 in
      let items := patt__.1.2 in
      let count := patt__.2 in
      constrained (struct struct_fixed_size_map [@{type}
        (&own (malloced (ly_size struct_item * length items) (array (struct_item) (items `at_type` item)))) ;
        (count @ (int (size_t))) ;
        ((length items) @ (int (size_t)))
      ]) (
        ⌜1 < length items⌝ ∗
        ⌜count = length (filter (λ x, x = Empty) items)⌝ ∗
        ⌜0 < count⌝ ∗
        ⌜fsm_invariant mp items⌝
      )
    )%I.
  Proof. apply: (type_fixpoint_unfold2 fixed_size_map_rec). Qed.

  Definition fixed_size_map_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (fixed_size_map_unfold patt__) with 100%N].
  Global Existing Instance fixed_size_map_simplify_hyp_place_inst_generated.
  Definition fixed_size_map_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (fixed_size_map_unfold patt__) with 100%N].
  Global Existing Instance fixed_size_map_simplify_goal_place_inst_generated.

  Definition fixed_size_map_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (fixed_size_map_unfold patt__) with 100%N].
  Global Existing Instance fixed_size_map_simplify_hyp_val_inst_generated.
  Definition fixed_size_map_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (fixed_size_map_unfold patt__) with 100%N].
  Global Existing Instance fixed_size_map_simplify_goal_val_inst_generated.

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

  (* Specifications for function [fsm_realloc_if_necessary]. *)
  Definition type_of_fsm_realloc_if_necessary :=
    fn(∀ (m, items, count, mp) : loc * (list item_ref) * nat * (gmap Z type); (m @ (&own ((mp, items, count) @ (fixed_size_map)))); True)
      → ∃ (items2, count2) : (list item_ref) * nat, (void); (m ◁ₗ ((mp, items2, count2) @ (fixed_size_map))) ∗ ⌜count <= count2⌝ ∗ ⌜1 < count2⌝ ∗ ⌜length items <= length items2⌝.

  (* Specifications for function [fsm_init]. *)
  Definition type_of_fsm_init :=
    fn(∀ (m, len) : loc * nat; (m @ (&own (uninit (struct_fixed_size_map)))), (len @ (int (size_t))); ⌜1 < len⌝ ∗ ⌜struct_item.(ly_size) * len + 16 ≤ max_int size_t⌝)
      → ∃ () : (), (void); (m ◁ₗ ((∅, replicate len Empty, len) @ (fixed_size_map))).

  (* Specifications for function [fsm_slot_for_key]. *)
  Definition type_of_fsm_slot_for_key :=
    fn(∀ (len, key) : nat * Z; (len @ (int (size_t))), (key @ (int (size_t))); ⌜(0 < len)%nat⌝)
      → ∃ () : (), ((slot_for_key_ref key len) @ (int (size_t))); True.

  (* Specifications for function [fsm_probe]. *)
  Definition type_of_fsm_probe :=
    fn(∀ (m, mp, items, key, count) : loc * (gmap Z type) * (list item_ref) * Z * nat; (m @ (&own ((mp, items, count) @ (fixed_size_map)))), (key @ (int (size_t))); True)
      → ∃ n : nat, (n @ (int (size_t))); (m ◁ₗ ((mp, items, count) @ (fixed_size_map))) ∗ ⌜∃ x, items !! n = Some x ∧ probe_ref key items = Some (n, x)⌝.

  (* Specifications for function [fsm_insert]. *)
  Definition type_of_fsm_insert :=
    fn(∀ (m, mp, items, count, key, ty) : loc * (gmap Z type) * (list item_ref) * nat * Z * type; (m @ (&own ((mp, items, count) @ (fixed_size_map)))), (key @ (int (size_t))), (&own (ty)); True)
      → ∃ (items2, count2) : (list item_ref) * nat, ((mp !! key) @ (optionalO (λ ty,
        &own (ty)
      ) null)); (m ◁ₗ ((<[key:=ty]>mp, items2, count2) @ (fixed_size_map))) ∗ ⌜count - 1 <= count2⌝ ∗ ⌜length items <= length items2⌝.

  (* Specifications for function [fsm_get]. *)
  Definition type_of_fsm_get :=
    fn(∀ (m, mp, items, count, key) : loc * (gmap Z type) * (list item_ref) * nat * Z; (m @ (&own ((mp, items, count) @ (fixed_size_map)))), (key @ (int (size_t))); True)
      → ∃ (p, items2) : loc * (list item_ref), ((mp !! key) @ (optionalO (λ ty,
        p @ (&own (ty))
      ) null)); (m ◁ₗ ((alter (λ _, place p) key mp, items2, count) @ (fixed_size_map))).

  (* Specifications for function [fsm_remove]. *)
  Definition type_of_fsm_remove :=
    fn(∀ (m, mp, items, count, key) : loc * (gmap Z type) * (list item_ref) * nat * Z; (m @ (&own ((mp, items, count) @ (fixed_size_map)))), (key @ (int (size_t))); True)
      → ∃ items2 : (list item_ref), ((mp !! key) @ (optionalO (λ ty,
        &own (ty)
      ) null)); (m ◁ₗ ((delete key mp, items2, count) @ (fixed_size_map))).

  (* Specifications for function [compute_min_count]. *)
  Definition type_of_compute_min_count :=
    fn(∀ n : Z; (n @ (int (size_t))); ⌜1 < n⌝)
      → ∃ m : Z, (m @ (int (size_t))); ⌜1 < m <= n⌝.
End spec.

Global Typeclasses Opaque fixed_size_map_rec.
Global Typeclasses Opaque fixed_size_map.
