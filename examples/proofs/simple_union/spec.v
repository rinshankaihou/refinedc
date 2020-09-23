From refinedc.typing Require Import typing.
From refinedc.examples.simple_union Require Import code.
Set Default Proof Using "Type".

(* Generated from [examples/simple_union.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Inlined code. *)

  Inductive item_ref type : Type :=
    | Empty
    | Entry (key : Z) (ty : type)
    | Tombstone (key : Z).

  Arguments Empty {_}.
  Arguments Entry {_}.
  Arguments Tombstone {_}.

  (* Definition of type [item] (tagged union). *)
  Definition item_tag (c : item_ref type) : nat :=
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

  Program Definition item_tunion_info : tunion_info := {|
    ti_rtype := item_ref type;
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

  Global Program Instance movable_item_tunion_info : MovableTUnion item_tunion_info := {|
    mti_movable c :=
      match c with
      | Empty => _
      | Entry key ty => _
      | Tombstone key => _
      end;
  |}.
  Next Obligation. simpl. apply _. Defined.
  Next Obligation. simpl. apply _. Defined.
  Next Obligation. simpl. apply _. Defined.
  Next Obligation. by case => /=; apply _. Qed.

  Program Definition item : rtype := tunion item_tunion_info.

  (* Type definitions. *)

  (* Specifications for function [test_item_set_empty]. *)
  Definition type_of_test_item_set_empty :=
    fn(∀ i : loc; (i @ (&own (uninit (struct_item)))); True)
      → ∃ () : (), (void); (i ◁ₗ (Empty @ (item))).

  (* Specifications for function [test_item_set_entry]. *)
  Definition type_of_test_item_set_entry :=
    fn(∀ (i, k, ty) : loc * Z * type; (i @ (&own (uninit (struct_item)))), (k @ (int (size_t))), (&own (ty)); True)
      → ∃ () : (), (void); (i ◁ₗ ((Entry k ty) @ (item))).

  (* Specifications for function [test_item_modify_entry]. *)
  Definition type_of_test_item_modify_entry :=
    fn(∀ (i, x, k) : loc * (item_ref type) * Z; (i @ (&own (x @ (item)))), (k @ (int (size_t))); True)
      → ∃ () : (), (int (size_t)); (i ◁ₗ (item)).
End spec.
