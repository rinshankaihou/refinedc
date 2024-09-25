From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/simple_union.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "examples/simple_union.c".
  Definition loc_2 : location_info := LocationInfo file_0 63 2 63 47.
  Definition loc_3 : location_info := LocationInfo file_0 63 9 63 46.
  Definition loc_4 : location_info := LocationInfo file_0 63 9 63 32.
  Definition loc_5 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_6 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_7 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_8 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_11 : location_info := LocationInfo file_1 53 4 53 25.
  Definition loc_12 : location_info := LocationInfo file_1 54 4 54 25.
  Definition loc_13 : location_info := LocationInfo file_1 54 4 54 20.
  Definition loc_14 : location_info := LocationInfo file_1 54 4 54 14.
  Definition loc_15 : location_info := LocationInfo file_1 54 4 54 8.
  Definition loc_16 : location_info := LocationInfo file_1 54 4 54 5.
  Definition loc_17 : location_info := LocationInfo file_1 54 4 54 5.
  Definition loc_18 : location_info := LocationInfo file_1 54 23 54 24.
  Definition loc_19 : location_info := LocationInfo file_1 53 4 53 10.
  Definition loc_20 : location_info := LocationInfo file_1 53 4 53 5.
  Definition loc_21 : location_info := LocationInfo file_1 53 4 53 5.
  Definition loc_22 : location_info := LocationInfo file_1 53 13 53 24.
  Definition loc_23 : location_info := LocationInfo file_1 53 22 53 23.
  Definition loc_26 : location_info := LocationInfo file_1 61 4 61 25.
  Definition loc_27 : location_info := LocationInfo file_1 62 4 62 25.
  Definition loc_28 : location_info := LocationInfo file_1 63 4 63 27.
  Definition loc_29 : location_info := LocationInfo file_1 63 4 63 20.
  Definition loc_30 : location_info := LocationInfo file_1 63 4 63 14.
  Definition loc_31 : location_info := LocationInfo file_1 63 4 63 8.
  Definition loc_32 : location_info := LocationInfo file_1 63 4 63 5.
  Definition loc_33 : location_info := LocationInfo file_1 63 4 63 5.
  Definition loc_34 : location_info := LocationInfo file_1 63 23 63 26.
  Definition loc_35 : location_info := LocationInfo file_1 63 23 63 26.
  Definition loc_36 : location_info := LocationInfo file_1 62 4 62 18.
  Definition loc_37 : location_info := LocationInfo file_1 62 4 62 14.
  Definition loc_38 : location_info := LocationInfo file_1 62 4 62 8.
  Definition loc_39 : location_info := LocationInfo file_1 62 4 62 5.
  Definition loc_40 : location_info := LocationInfo file_1 62 4 62 5.
  Definition loc_41 : location_info := LocationInfo file_1 62 21 62 24.
  Definition loc_42 : location_info := LocationInfo file_1 62 21 62 24.
  Definition loc_43 : location_info := LocationInfo file_1 61 4 61 10.
  Definition loc_44 : location_info := LocationInfo file_1 61 4 61 5.
  Definition loc_45 : location_info := LocationInfo file_1 61 4 61 5.
  Definition loc_46 : location_info := LocationInfo file_1 61 13 61 24.
  Definition loc_47 : location_info := LocationInfo file_1 61 22 61 23.
  Definition loc_50 : location_info := LocationInfo file_1 71 4 71 19.
  Definition loc_51 : location_info := LocationInfo file_1 73 4 78 5.
  Definition loc_52 : location_info := LocationInfo file_1 79 4 79 15.
  Definition loc_53 : location_info := LocationInfo file_1 79 11 79 14.
  Definition loc_54 : location_info := LocationInfo file_1 79 11 79 14.
  Definition loc_55 : location_info := LocationInfo file_1 73 31 78 5.
  Definition loc_56 : location_info := LocationInfo file_1 74 8 74 33.
  Definition loc_57 : location_info := LocationInfo file_1 75 8 75 29.
  Definition loc_58 : location_info := LocationInfo file_1 76 8 76 33.
  Definition loc_59 : location_info := LocationInfo file_1 77 8 77 23.
  Definition loc_60 : location_info := LocationInfo file_1 77 15 77 22.
  Definition loc_61 : location_info := LocationInfo file_1 77 15 77 22.
  Definition loc_62 : location_info := LocationInfo file_1 76 8 76 26.
  Definition loc_63 : location_info := LocationInfo file_1 76 8 76 22.
  Definition loc_64 : location_info := LocationInfo file_1 76 8 76 12.
  Definition loc_65 : location_info := LocationInfo file_1 76 8 76 9.
  Definition loc_66 : location_info := LocationInfo file_1 76 8 76 9.
  Definition loc_67 : location_info := LocationInfo file_1 76 29 76 32.
  Definition loc_68 : location_info := LocationInfo file_1 76 29 76 32.
  Definition loc_69 : location_info := LocationInfo file_1 75 8 75 14.
  Definition loc_70 : location_info := LocationInfo file_1 75 8 75 9.
  Definition loc_71 : location_info := LocationInfo file_1 75 8 75 9.
  Definition loc_72 : location_info := LocationInfo file_1 75 17 75 28.
  Definition loc_73 : location_info := LocationInfo file_1 75 26 75 27.
  Definition loc_74 : location_info := LocationInfo file_1 74 8 74 15.
  Definition loc_75 : location_info := LocationInfo file_1 74 18 74 32.
  Definition loc_76 : location_info := LocationInfo file_1 74 18 74 32.
  Definition loc_77 : location_info := LocationInfo file_1 74 18 74 28.
  Definition loc_78 : location_info := LocationInfo file_1 74 18 74 22.
  Definition loc_79 : location_info := LocationInfo file_1 74 18 74 19.
  Definition loc_80 : location_info := LocationInfo file_1 74 18 74 19.
  Definition loc_81 : location_info := LocationInfo file_1 73 4 78 5.
  Definition loc_82 : location_info := LocationInfo file_1 73 8 73 29.
  Definition loc_83 : location_info := LocationInfo file_1 73 8 73 14.
  Definition loc_84 : location_info := LocationInfo file_1 73 8 73 14.
  Definition loc_85 : location_info := LocationInfo file_1 73 8 73 9.
  Definition loc_86 : location_info := LocationInfo file_1 73 8 73 9.
  Definition loc_87 : location_info := LocationInfo file_1 73 18 73 29.
  Definition loc_88 : location_info := LocationInfo file_1 73 27 73 28.

  (* Definition of struct [__cerbty_unnamed_tag_486]. *)
  Program Definition struct___cerbty_unnamed_tag_486 := {|
    sl_members := [
      (Some "__dummy_max_align_t", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

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
      (Some "value", void*)
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

  (* Definition of function [copy_alloc_id]. *)
  Definition impl_copy_alloc_id : function := {|
    f_args := [
      ("to", it_layout uintptr_t);
      ("from", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        Return (LocInfoE loc_3 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_5 (use{IntOp uintptr_t} (LocInfoE loc_6 ("to")))) (LocInfoE loc_7 (use{PtrOp} (LocInfoE loc_8 ("from"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_item_set_empty]. *)
  Definition impl_test_item_set_empty : function := {|
    f_args := [
      ("i", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_11 ;
        LocInfoE loc_19 ((LocInfoE loc_20 (!{PtrOp} (LocInfoE loc_21 ("i")))) at{struct_item} "tag") <-{ IntOp size_t }
          LocInfoE loc_22 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_23 (i2v 0 i32))) ;
        locinfo: loc_12 ;
        LocInfoE loc_13 ((LocInfoE loc_14 ((LocInfoE loc_15 ((LocInfoE loc_16 (!{PtrOp} (LocInfoE loc_17 ("i")))) at{struct_item} "u")) at_union{union_item_union} "empty")) at{struct_empty} "dummy") <-{ IntOp size_t }
          LocInfoE loc_18 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_18 (i2v 0 i32))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_item_set_entry]. *)
  Definition impl_test_item_set_entry : function := {|
    f_args := [
      ("i", void*);
      ("key", it_layout size_t);
      ("val", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_26 ;
        LocInfoE loc_43 ((LocInfoE loc_44 (!{PtrOp} (LocInfoE loc_45 ("i")))) at{struct_item} "tag") <-{ IntOp size_t }
          LocInfoE loc_46 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_47 (i2v 1 i32))) ;
        locinfo: loc_27 ;
        LocInfoE loc_36 ((LocInfoE loc_37 ((LocInfoE loc_38 ((LocInfoE loc_39 (!{PtrOp} (LocInfoE loc_40 ("i")))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "key") <-{ IntOp size_t }
          LocInfoE loc_41 (use{IntOp size_t} (LocInfoE loc_42 ("key"))) ;
        locinfo: loc_28 ;
        LocInfoE loc_29 ((LocInfoE loc_30 ((LocInfoE loc_31 ((LocInfoE loc_32 (!{PtrOp} (LocInfoE loc_33 ("i")))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "value") <-{ PtrOp }
          LocInfoE loc_34 (use{PtrOp} (LocInfoE loc_35 ("val"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_item_modify_entry]. *)
  Definition impl_test_item_modify_entry : function := {|
    f_args := [
      ("i", void*);
      ("key", it_layout size_t)
    ];
    f_local_vars := [
      ("old_key", it_layout size_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_82 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_82 ((LocInfoE loc_83 (use{IntOp size_t} (LocInfoE loc_84 ((LocInfoE loc_85 (!{PtrOp} (LocInfoE loc_86 ("i")))) at{struct_item} "tag")))) ={IntOp size_t, IntOp size_t, i32} (LocInfoE loc_87 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_88 (i2v 1 i32)))))
        then
        locinfo: loc_56 ;
          Goto "#2"
        else
        locinfo: loc_52 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_52 ;
        Return (LocInfoE loc_53 (use{IntOp size_t} (LocInfoE loc_54 ("key"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_56 ;
        LocInfoE loc_74 ("old_key") <-{ IntOp size_t }
          LocInfoE loc_75 (use{IntOp size_t} (LocInfoE loc_76 ((LocInfoE loc_77 ((LocInfoE loc_78 ((LocInfoE loc_79 (!{PtrOp} (LocInfoE loc_80 ("i")))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "key"))) ;
        locinfo: loc_57 ;
        LocInfoE loc_69 ((LocInfoE loc_70 (!{PtrOp} (LocInfoE loc_71 ("i")))) at{struct_item} "tag") <-{ IntOp size_t }
          LocInfoE loc_72 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_73 (i2v 2 i32))) ;
        locinfo: loc_58 ;
        LocInfoE loc_62 ((LocInfoE loc_63 ((LocInfoE loc_64 ((LocInfoE loc_65 (!{PtrOp} (LocInfoE loc_66 ("i")))) at{struct_item} "u")) at_union{union_item_union} "tombstone")) at{struct_tombstone} "key") <-{ IntOp size_t }
          LocInfoE loc_67 (use{IntOp size_t} (LocInfoE loc_68 ("key"))) ;
        locinfo: loc_59 ;
        Return (LocInfoE loc_60 (use{IntOp size_t} (LocInfoE loc_61 ("old_key"))))
      ]> $
      <[ "#3" :=
        locinfo: loc_52 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.
End code.
