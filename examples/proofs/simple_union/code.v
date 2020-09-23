From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/simple_union.c]. *)
Section code.
  Definition file_0 : string := "examples/simple_union.c".
  Definition loc_2 : location_info := LocationInfo file_0 53 4 53 25.
  Definition loc_3 : location_info := LocationInfo file_0 54 4 54 25.
  Definition loc_4 : location_info := LocationInfo file_0 54 4 54 20.
  Definition loc_5 : location_info := LocationInfo file_0 54 4 54 14.
  Definition loc_6 : location_info := LocationInfo file_0 54 4 54 8.
  Definition loc_7 : location_info := LocationInfo file_0 54 4 54 5.
  Definition loc_8 : location_info := LocationInfo file_0 54 4 54 5.
  Definition loc_9 : location_info := LocationInfo file_0 54 23 54 24.
  Definition loc_10 : location_info := LocationInfo file_0 53 4 53 10.
  Definition loc_11 : location_info := LocationInfo file_0 53 4 53 5.
  Definition loc_12 : location_info := LocationInfo file_0 53 4 53 5.
  Definition loc_13 : location_info := LocationInfo file_0 53 13 53 24.
  Definition loc_14 : location_info := LocationInfo file_0 53 22 53 23.
  Definition loc_17 : location_info := LocationInfo file_0 61 4 61 25.
  Definition loc_18 : location_info := LocationInfo file_0 62 4 62 25.
  Definition loc_19 : location_info := LocationInfo file_0 63 4 63 27.
  Definition loc_20 : location_info := LocationInfo file_0 63 4 63 20.
  Definition loc_21 : location_info := LocationInfo file_0 63 4 63 14.
  Definition loc_22 : location_info := LocationInfo file_0 63 4 63 8.
  Definition loc_23 : location_info := LocationInfo file_0 63 4 63 5.
  Definition loc_24 : location_info := LocationInfo file_0 63 4 63 5.
  Definition loc_25 : location_info := LocationInfo file_0 63 23 63 26.
  Definition loc_26 : location_info := LocationInfo file_0 63 23 63 26.
  Definition loc_27 : location_info := LocationInfo file_0 62 4 62 18.
  Definition loc_28 : location_info := LocationInfo file_0 62 4 62 14.
  Definition loc_29 : location_info := LocationInfo file_0 62 4 62 8.
  Definition loc_30 : location_info := LocationInfo file_0 62 4 62 5.
  Definition loc_31 : location_info := LocationInfo file_0 62 4 62 5.
  Definition loc_32 : location_info := LocationInfo file_0 62 21 62 24.
  Definition loc_33 : location_info := LocationInfo file_0 62 21 62 24.
  Definition loc_34 : location_info := LocationInfo file_0 61 4 61 10.
  Definition loc_35 : location_info := LocationInfo file_0 61 4 61 5.
  Definition loc_36 : location_info := LocationInfo file_0 61 4 61 5.
  Definition loc_37 : location_info := LocationInfo file_0 61 13 61 24.
  Definition loc_38 : location_info := LocationInfo file_0 61 22 61 23.
  Definition loc_41 : location_info := LocationInfo file_0 73 4 78 5.
  Definition loc_42 : location_info := LocationInfo file_0 79 4 79 15.
  Definition loc_43 : location_info := LocationInfo file_0 79 11 79 14.
  Definition loc_44 : location_info := LocationInfo file_0 79 11 79 14.
  Definition loc_45 : location_info := LocationInfo file_0 73 31 78 5.
  Definition loc_46 : location_info := LocationInfo file_0 74 8 74 33.
  Definition loc_47 : location_info := LocationInfo file_0 75 8 75 29.
  Definition loc_48 : location_info := LocationInfo file_0 76 8 76 33.
  Definition loc_49 : location_info := LocationInfo file_0 77 8 77 23.
  Definition loc_50 : location_info := LocationInfo file_0 77 15 77 22.
  Definition loc_51 : location_info := LocationInfo file_0 77 15 77 22.
  Definition loc_52 : location_info := LocationInfo file_0 76 8 76 26.
  Definition loc_53 : location_info := LocationInfo file_0 76 8 76 22.
  Definition loc_54 : location_info := LocationInfo file_0 76 8 76 12.
  Definition loc_55 : location_info := LocationInfo file_0 76 8 76 9.
  Definition loc_56 : location_info := LocationInfo file_0 76 8 76 9.
  Definition loc_57 : location_info := LocationInfo file_0 76 29 76 32.
  Definition loc_58 : location_info := LocationInfo file_0 76 29 76 32.
  Definition loc_59 : location_info := LocationInfo file_0 75 8 75 14.
  Definition loc_60 : location_info := LocationInfo file_0 75 8 75 9.
  Definition loc_61 : location_info := LocationInfo file_0 75 8 75 9.
  Definition loc_62 : location_info := LocationInfo file_0 75 17 75 28.
  Definition loc_63 : location_info := LocationInfo file_0 75 26 75 27.
  Definition loc_64 : location_info := LocationInfo file_0 74 8 74 15.
  Definition loc_65 : location_info := LocationInfo file_0 74 18 74 32.
  Definition loc_66 : location_info := LocationInfo file_0 74 18 74 32.
  Definition loc_67 : location_info := LocationInfo file_0 74 18 74 28.
  Definition loc_68 : location_info := LocationInfo file_0 74 18 74 22.
  Definition loc_69 : location_info := LocationInfo file_0 74 18 74 19.
  Definition loc_70 : location_info := LocationInfo file_0 74 18 74 19.
  Definition loc_72 : location_info := LocationInfo file_0 73 8 73 29.
  Definition loc_73 : location_info := LocationInfo file_0 73 8 73 14.
  Definition loc_74 : location_info := LocationInfo file_0 73 8 73 14.
  Definition loc_75 : location_info := LocationInfo file_0 73 8 73 9.
  Definition loc_76 : location_info := LocationInfo file_0 73 8 73 9.
  Definition loc_77 : location_info := LocationInfo file_0 73 18 73 29.
  Definition loc_78 : location_info := LocationInfo file_0 73 27 73 28.

  (* Definition of struct [empty]. *)
  Program Definition struct_empty := {|
    sl_members := [
      (Some "dummy", it_layout size_t)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [entry]. *)
  Program Definition struct_entry := {|
    sl_members := [
      (Some "key", it_layout size_t);
      (Some "value", LPtr)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [tombstone]. *)
  Program Definition struct_tombstone := {|
    sl_members := [
      (Some "key", it_layout size_t)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of union [item_union]. *)
  Program Definition union_item_union := {|
    ul_members := [
      ("empty", layout_of struct_empty);
      ("entry", layout_of struct_entry);
      ("tombstone", layout_of struct_tombstone)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [item]. *)
  Program Definition struct_item := {|
    sl_members := [
      (Some "tag", it_layout size_t);
      (Some "u", ul_layout union_item_union)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [test_item_set_empty]. *)
  Definition impl_test_item_set_empty : function := {|
    f_args := [
      ("i", LPtr)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        LocInfoE loc_10 ((LocInfoE loc_11 (!{LPtr} (LocInfoE loc_12 ("i")))) at{struct_item} "tag") <-{ it_layout size_t }
          LocInfoE loc_13 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_14 (i2v 0 i32))) ;
        locinfo: loc_3 ;
        LocInfoE loc_4 ((LocInfoE loc_5 ((LocInfoE loc_6 ((LocInfoE loc_7 (!{LPtr} (LocInfoE loc_8 ("i")))) at{struct_item} "u")) at_union{union_item_union} "empty")) at{struct_empty} "dummy") <-{ it_layout size_t }
          LocInfoE loc_9 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_9 (i2v 0 i32))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_item_set_entry]. *)
  Definition impl_test_item_set_entry : function := {|
    f_args := [
      ("i", LPtr);
      ("key", it_layout size_t);
      ("val", LPtr)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_17 ;
        LocInfoE loc_34 ((LocInfoE loc_35 (!{LPtr} (LocInfoE loc_36 ("i")))) at{struct_item} "tag") <-{ it_layout size_t }
          LocInfoE loc_37 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_38 (i2v 1 i32))) ;
        locinfo: loc_18 ;
        LocInfoE loc_27 ((LocInfoE loc_28 ((LocInfoE loc_29 ((LocInfoE loc_30 (!{LPtr} (LocInfoE loc_31 ("i")))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "key") <-{ it_layout size_t }
          LocInfoE loc_32 (use{it_layout size_t} (LocInfoE loc_33 ("key"))) ;
        locinfo: loc_19 ;
        LocInfoE loc_20 ((LocInfoE loc_21 ((LocInfoE loc_22 ((LocInfoE loc_23 (!{LPtr} (LocInfoE loc_24 ("i")))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "value") <-{ LPtr }
          LocInfoE loc_25 (use{LPtr} (LocInfoE loc_26 ("val"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_item_modify_entry]. *)
  Definition impl_test_item_modify_entry : function := {|
    f_args := [
      ("i", LPtr);
      ("key", it_layout size_t)
    ];
    f_local_vars := [
      ("old_key", it_layout size_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_72 ;
        if: LocInfoE loc_72 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_72 ((LocInfoE loc_73 (use{it_layout size_t} (LocInfoE loc_74 ((LocInfoE loc_75 (!{LPtr} (LocInfoE loc_76 ("i")))) at{struct_item} "tag")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_77 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_78 (i2v 1 i32)))))))
        then
        locinfo: loc_46 ;
          Goto "#2"
        else
        locinfo: loc_42 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_42 ;
        Return (LocInfoE loc_43 (use{it_layout size_t} (LocInfoE loc_44 ("key"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_46 ;
        LocInfoE loc_64 ("old_key") <-{ it_layout size_t }
          LocInfoE loc_65 (use{it_layout size_t} (LocInfoE loc_66 ((LocInfoE loc_67 ((LocInfoE loc_68 ((LocInfoE loc_69 (!{LPtr} (LocInfoE loc_70 ("i")))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "key"))) ;
        locinfo: loc_47 ;
        LocInfoE loc_59 ((LocInfoE loc_60 (!{LPtr} (LocInfoE loc_61 ("i")))) at{struct_item} "tag") <-{ it_layout size_t }
          LocInfoE loc_62 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_63 (i2v 2 i32))) ;
        locinfo: loc_48 ;
        LocInfoE loc_52 ((LocInfoE loc_53 ((LocInfoE loc_54 ((LocInfoE loc_55 (!{LPtr} (LocInfoE loc_56 ("i")))) at{struct_item} "u")) at_union{union_item_union} "tombstone")) at{struct_tombstone} "key") <-{ it_layout size_t }
          LocInfoE loc_57 (use{it_layout size_t} (LocInfoE loc_58 ("key"))) ;
        locinfo: loc_49 ;
        Return (LocInfoE loc_50 (use{it_layout size_t} (LocInfoE loc_51 ("old_key"))))
      ]> $
      <[ "#3" :=
        locinfo: loc_42 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.
End code.
