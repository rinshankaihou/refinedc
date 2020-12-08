From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/talk_demo3.c]. *)
Section code.
  Definition file_0 : string := "examples/talk_demo3.c".
  Definition loc_2 : location_info := LocationInfo file_0 21 2 25 3.
  Definition loc_3 : location_info := LocationInfo file_0 21 27 23 3.
  Definition loc_4 : location_info := LocationInfo file_0 22 4 22 11.
  Definition loc_5 : location_info := LocationInfo file_0 22 4 22 6.
  Definition loc_6 : location_info := LocationInfo file_0 22 5 22 6.
  Definition loc_7 : location_info := LocationInfo file_0 22 5 22 6.
  Definition loc_8 : location_info := LocationInfo file_0 22 9 22 10.
  Definition loc_9 : location_info := LocationInfo file_0 22 9 22 10.
  Definition loc_10 : location_info := LocationInfo file_0 23 9 25 3.
  Definition loc_11 : location_info := LocationInfo file_0 24 4 24 27.
  Definition loc_12 : location_info := LocationInfo file_0 24 4 24 10.
  Definition loc_13 : location_info := LocationInfo file_0 24 4 24 10.
  Definition loc_14 : location_info := LocationInfo file_0 24 11 24 22.
  Definition loc_15 : location_info := LocationInfo file_0 24 12 24 22.
  Definition loc_16 : location_info := LocationInfo file_0 24 12 24 16.
  Definition loc_17 : location_info := LocationInfo file_0 24 12 24 16.
  Definition loc_18 : location_info := LocationInfo file_0 24 14 24 15.
  Definition loc_19 : location_info := LocationInfo file_0 24 14 24 15.
  Definition loc_20 : location_info := LocationInfo file_0 24 24 24 25.
  Definition loc_21 : location_info := LocationInfo file_0 24 24 24 25.
  Definition loc_22 : location_info := LocationInfo file_0 21 5 21 25.
  Definition loc_23 : location_info := LocationInfo file_0 21 5 21 7.
  Definition loc_24 : location_info := LocationInfo file_0 21 5 21 7.
  Definition loc_25 : location_info := LocationInfo file_0 21 6 21 7.
  Definition loc_26 : location_info := LocationInfo file_0 21 6 21 7.
  Definition loc_27 : location_info := LocationInfo file_0 21 11 21 25.
  Definition loc_30 : location_info := LocationInfo file_0 30 2 30 61.
  Definition loc_31 : location_info := LocationInfo file_0 31 2 31 17.
  Definition loc_32 : location_info := LocationInfo file_0 31 18 31 47.
  Definition loc_33 : location_info := LocationInfo file_0 32 2 32 61.
  Definition loc_34 : location_info := LocationInfo file_0 33 2 33 17.
  Definition loc_35 : location_info := LocationInfo file_0 33 18 33 47.
  Definition loc_36 : location_info := LocationInfo file_0 34 2 34 24.
  Definition loc_37 : location_info := LocationInfo file_0 35 2 37 3.
  Definition loc_38 : location_info := LocationInfo file_0 35 30 37 3.
  Definition loc_39 : location_info := LocationInfo file_0 36 4 36 28.
  Definition loc_40 : location_info := LocationInfo file_0 36 11 36 26.
  Definition loc_41 : location_info := LocationInfo file_0 36 11 36 21.
  Definition loc_42 : location_info := LocationInfo file_0 36 11 36 21.
  Definition loc_43 : location_info := LocationInfo file_0 36 11 36 16.
  Definition loc_44 : location_info := LocationInfo file_0 36 11 36 16.
  Definition loc_45 : location_info := LocationInfo file_0 36 25 36 26.
  Definition loc_47 : location_info := LocationInfo file_0 35 5 35 28.
  Definition loc_48 : location_info := LocationInfo file_0 35 5 35 10.
  Definition loc_49 : location_info := LocationInfo file_0 35 5 35 10.
  Definition loc_50 : location_info := LocationInfo file_0 35 14 35 28.
  Definition loc_51 : location_info := LocationInfo file_0 34 2 34 8.
  Definition loc_52 : location_info := LocationInfo file_0 34 2 34 8.
  Definition loc_53 : location_info := LocationInfo file_0 34 9 34 15.
  Definition loc_54 : location_info := LocationInfo file_0 34 10 34 15.
  Definition loc_55 : location_info := LocationInfo file_0 34 17 34 22.
  Definition loc_56 : location_info := LocationInfo file_0 34 17 34 22.
  Definition loc_57 : location_info := LocationInfo file_0 33 18 33 29.
  Definition loc_58 : location_info := LocationInfo file_0 33 18 33 23.
  Definition loc_59 : location_info := LocationInfo file_0 33 18 33 23.
  Definition loc_60 : location_info := LocationInfo file_0 33 32 33 46.
  Definition loc_61 : location_info := LocationInfo file_0 33 2 33 12.
  Definition loc_62 : location_info := LocationInfo file_0 33 2 33 7.
  Definition loc_63 : location_info := LocationInfo file_0 33 2 33 7.
  Definition loc_64 : location_info := LocationInfo file_0 33 15 33 16.
  Definition loc_65 : location_info := LocationInfo file_0 32 29 32 60.
  Definition loc_66 : location_info := LocationInfo file_0 32 29 32 34.
  Definition loc_67 : location_info := LocationInfo file_0 32 29 32 34.
  Definition loc_68 : location_info := LocationInfo file_0 32 35 32 59.
  Definition loc_71 : location_info := LocationInfo file_0 31 18 31 29.
  Definition loc_72 : location_info := LocationInfo file_0 31 18 31 23.
  Definition loc_73 : location_info := LocationInfo file_0 31 18 31 23.
  Definition loc_74 : location_info := LocationInfo file_0 31 32 31 46.
  Definition loc_75 : location_info := LocationInfo file_0 31 2 31 12.
  Definition loc_76 : location_info := LocationInfo file_0 31 2 31 7.
  Definition loc_77 : location_info := LocationInfo file_0 31 2 31 7.
  Definition loc_78 : location_info := LocationInfo file_0 31 15 31 16.
  Definition loc_79 : location_info := LocationInfo file_0 30 29 30 60.
  Definition loc_80 : location_info := LocationInfo file_0 30 29 30 34.
  Definition loc_81 : location_info := LocationInfo file_0 30 29 30 34.
  Definition loc_82 : location_info := LocationInfo file_0 30 35 30 59.

  (* Definition of struct [list_node]. *)
  Program Definition struct_list_node := {|
    sl_members := [
      (Some "val", it_layout i32);
      (None, Layout 4%nat 0%nat);
      (Some "next", LPtr)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [append]. *)
  Definition impl_append (append : loc): function := {|
    f_args := [
      ("l", LPtr);
      ("k", LPtr)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_22 ;
        if: LocInfoE loc_22 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_22 ((LocInfoE loc_23 (use{LPtr} (LocInfoE loc_25 (!{LPtr} (LocInfoE loc_26 ("l")))))) ={PtrOp, PtrOp} (LocInfoE loc_27 (NULL)))))
        then
        locinfo: loc_4 ;
          Goto "#1"
        else
        locinfo: loc_11 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_4 ;
        LocInfoE loc_6 (!{LPtr} (LocInfoE loc_7 ("l"))) <-{ LPtr }
          LocInfoE loc_8 (use{LPtr} (LocInfoE loc_9 ("k"))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_11 ;
        "_" <- LocInfoE loc_13 (append) with
          [ LocInfoE loc_14 (&(LocInfoE loc_15 ((LocInfoE loc_16 (!{LPtr} (LocInfoE loc_18 (!{LPtr} (LocInfoE loc_19 ("l")))))) at{struct_list_node} "next"))) ;
          LocInfoE loc_20 (use{LPtr} (LocInfoE loc_21 ("k"))) ] ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [test]. *)
  Definition impl_test (alloc append : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
      ("node1", LPtr);
      ("node2", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_79 ;
        "$1" <- LocInfoE loc_81 (alloc) with
          [ LocInfoE loc_82 (i2v (layout_of struct_list_node).(ly_size) size_t) ] ;
        "node1" <-{ LPtr }
          LocInfoE loc_79 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_79 ("$1"))) ;
        locinfo: loc_31 ;
        LocInfoE loc_75 ((LocInfoE loc_76 (!{LPtr} (LocInfoE loc_77 ("node1")))) at{struct_list_node} "val") <-{ it_layout i32 }
          LocInfoE loc_78 (i2v 1 i32) ;
        locinfo: loc_32 ;
        LocInfoE loc_71 ((LocInfoE loc_72 (!{LPtr} (LocInfoE loc_73 ("node1")))) at{struct_list_node} "next") <-{ LPtr }
          LocInfoE loc_74 (NULL) ;
        locinfo: loc_65 ;
        "$0" <- LocInfoE loc_67 (alloc) with
          [ LocInfoE loc_68 (i2v (layout_of struct_list_node).(ly_size) size_t) ] ;
        "node2" <-{ LPtr }
          LocInfoE loc_65 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_65 ("$0"))) ;
        locinfo: loc_34 ;
        LocInfoE loc_61 ((LocInfoE loc_62 (!{LPtr} (LocInfoE loc_63 ("node2")))) at{struct_list_node} "val") <-{ it_layout i32 }
          LocInfoE loc_64 (i2v 2 i32) ;
        locinfo: loc_35 ;
        LocInfoE loc_57 ((LocInfoE loc_58 (!{LPtr} (LocInfoE loc_59 ("node2")))) at{struct_list_node} "next") <-{ LPtr }
          LocInfoE loc_60 (NULL) ;
        locinfo: loc_36 ;
        "_" <- LocInfoE loc_52 (append) with
          [ LocInfoE loc_53 (&(LocInfoE loc_54 ("node1"))) ;
          LocInfoE loc_55 (use{LPtr} (LocInfoE loc_56 ("node2"))) ] ;
        locinfo: loc_47 ;
        if: LocInfoE loc_47 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_47 ((LocInfoE loc_48 (use{LPtr} (LocInfoE loc_49 ("node1")))) !={PtrOp, PtrOp} (LocInfoE loc_50 (NULL)))))
        then
        locinfo: loc_39 ;
          Goto "#1"
        else
        Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_39 ;
        assert: (LocInfoE loc_40 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_40 ((LocInfoE loc_41 (use{it_layout i32} (LocInfoE loc_42 ((LocInfoE loc_43 (!{LPtr} (LocInfoE loc_44 ("node1")))) at{struct_list_node} "val")))) ={IntOp i32, IntOp i32} (LocInfoE loc_45 (i2v 1 i32)))))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
