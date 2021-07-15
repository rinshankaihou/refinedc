From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/talk_demo2.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "examples/talk_demo2.c".
  Definition loc_2 : location_info := LocationInfo file_0 50 2 50 47.
  Definition loc_3 : location_info := LocationInfo file_0 50 9 50 46.
  Definition loc_4 : location_info := LocationInfo file_0 50 9 50 32.
  Definition loc_5 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_6 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_7 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_8 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_11 : location_info := LocationInfo file_1 16 2 20 3.
  Definition loc_12 : location_info := LocationInfo file_1 16 27 18 3.
  Definition loc_13 : location_info := LocationInfo file_1 17 4 17 11.
  Definition loc_14 : location_info := LocationInfo file_1 17 4 17 6.
  Definition loc_15 : location_info := LocationInfo file_1 17 5 17 6.
  Definition loc_16 : location_info := LocationInfo file_1 17 5 17 6.
  Definition loc_17 : location_info := LocationInfo file_1 17 9 17 10.
  Definition loc_18 : location_info := LocationInfo file_1 17 9 17 10.
  Definition loc_19 : location_info := LocationInfo file_1 18 9 20 3.
  Definition loc_20 : location_info := LocationInfo file_1 19 4 19 27.
  Definition loc_21 : location_info := LocationInfo file_1 19 4 19 10.
  Definition loc_22 : location_info := LocationInfo file_1 19 4 19 10.
  Definition loc_23 : location_info := LocationInfo file_1 19 11 19 22.
  Definition loc_24 : location_info := LocationInfo file_1 19 12 19 22.
  Definition loc_25 : location_info := LocationInfo file_1 19 12 19 16.
  Definition loc_26 : location_info := LocationInfo file_1 19 12 19 16.
  Definition loc_27 : location_info := LocationInfo file_1 19 14 19 15.
  Definition loc_28 : location_info := LocationInfo file_1 19 14 19 15.
  Definition loc_29 : location_info := LocationInfo file_1 19 24 19 25.
  Definition loc_30 : location_info := LocationInfo file_1 19 24 19 25.
  Definition loc_31 : location_info := LocationInfo file_1 16 5 16 25.
  Definition loc_32 : location_info := LocationInfo file_1 16 5 16 7.
  Definition loc_33 : location_info := LocationInfo file_1 16 5 16 7.
  Definition loc_34 : location_info := LocationInfo file_1 16 6 16 7.
  Definition loc_35 : location_info := LocationInfo file_1 16 6 16 7.
  Definition loc_36 : location_info := LocationInfo file_1 16 11 16 25.
  Definition loc_39 : location_info := LocationInfo file_1 25 2 25 61.
  Definition loc_40 : location_info := LocationInfo file_1 26 2 26 17.
  Definition loc_41 : location_info := LocationInfo file_1 26 18 26 47.
  Definition loc_42 : location_info := LocationInfo file_1 27 2 27 61.
  Definition loc_43 : location_info := LocationInfo file_1 28 2 28 17.
  Definition loc_44 : location_info := LocationInfo file_1 28 18 28 47.
  Definition loc_45 : location_info := LocationInfo file_1 29 2 29 24.
  Definition loc_46 : location_info := LocationInfo file_1 30 2 32 3.
  Definition loc_47 : location_info := LocationInfo file_1 30 30 32 3.
  Definition loc_49 : location_info := LocationInfo file_1 30 5 30 28.
  Definition loc_50 : location_info := LocationInfo file_1 30 5 30 10.
  Definition loc_51 : location_info := LocationInfo file_1 30 5 30 10.
  Definition loc_52 : location_info := LocationInfo file_1 30 14 30 28.
  Definition loc_53 : location_info := LocationInfo file_1 29 2 29 8.
  Definition loc_54 : location_info := LocationInfo file_1 29 2 29 8.
  Definition loc_55 : location_info := LocationInfo file_1 29 9 29 15.
  Definition loc_56 : location_info := LocationInfo file_1 29 10 29 15.
  Definition loc_57 : location_info := LocationInfo file_1 29 17 29 22.
  Definition loc_58 : location_info := LocationInfo file_1 29 17 29 22.
  Definition loc_59 : location_info := LocationInfo file_1 28 18 28 29.
  Definition loc_60 : location_info := LocationInfo file_1 28 18 28 23.
  Definition loc_61 : location_info := LocationInfo file_1 28 18 28 23.
  Definition loc_62 : location_info := LocationInfo file_1 28 32 28 46.
  Definition loc_63 : location_info := LocationInfo file_1 28 2 28 12.
  Definition loc_64 : location_info := LocationInfo file_1 28 2 28 7.
  Definition loc_65 : location_info := LocationInfo file_1 28 2 28 7.
  Definition loc_66 : location_info := LocationInfo file_1 28 15 28 16.
  Definition loc_67 : location_info := LocationInfo file_1 27 29 27 60.
  Definition loc_68 : location_info := LocationInfo file_1 27 29 27 34.
  Definition loc_69 : location_info := LocationInfo file_1 27 29 27 34.
  Definition loc_70 : location_info := LocationInfo file_1 27 35 27 59.
  Definition loc_73 : location_info := LocationInfo file_1 26 18 26 29.
  Definition loc_74 : location_info := LocationInfo file_1 26 18 26 23.
  Definition loc_75 : location_info := LocationInfo file_1 26 18 26 23.
  Definition loc_76 : location_info := LocationInfo file_1 26 32 26 46.
  Definition loc_77 : location_info := LocationInfo file_1 26 2 26 12.
  Definition loc_78 : location_info := LocationInfo file_1 26 2 26 7.
  Definition loc_79 : location_info := LocationInfo file_1 26 2 26 7.
  Definition loc_80 : location_info := LocationInfo file_1 26 15 26 16.
  Definition loc_81 : location_info := LocationInfo file_1 25 29 25 60.
  Definition loc_82 : location_info := LocationInfo file_1 25 29 25 34.
  Definition loc_83 : location_info := LocationInfo file_1 25 29 25 34.
  Definition loc_84 : location_info := LocationInfo file_1 25 35 25 59.

  (* Definition of struct [list_node]. *)
  Program Definition struct_list_node := {|
    sl_members := [
      (Some "val", it_layout i32);
      (None, Layout 4%nat 0%nat);
      (Some "next", void*)
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

  (* Definition of function [append]. *)
  Definition impl_append (global_append : loc): function := {|
    f_args := [
      ("l", void*);
      ("k", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_31 ;
        if: LocInfoE loc_31 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_31 ((LocInfoE loc_32 (use{PtrOp} (LocInfoE loc_34 (!{PtrOp} (LocInfoE loc_35 ("l")))))) ={PtrOp, PtrOp} (LocInfoE loc_36 (NULL)))))
        then
        locinfo: loc_13 ;
          Goto "#1"
        else
        locinfo: loc_20 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_13 ;
        LocInfoE loc_15 (!{PtrOp} (LocInfoE loc_16 ("l"))) <-{ PtrOp }
          LocInfoE loc_17 (use{PtrOp} (LocInfoE loc_18 ("k"))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_20 ;
        expr: (LocInfoE loc_20 (Call (LocInfoE loc_22 (global_append)) [@{expr} LocInfoE loc_23 (&(LocInfoE loc_24 ((LocInfoE loc_25 (!{PtrOp} (LocInfoE loc_27 (!{PtrOp} (LocInfoE loc_28 ("l")))))) at{struct_list_node} "next"))) ;
        LocInfoE loc_29 (use{PtrOp} (LocInfoE loc_30 ("k"))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [test]. *)
  Definition impl_test (global_alloc global_append : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
      ("node1", void*);
      ("node2", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "node1" <-{ PtrOp }
          LocInfoE loc_81 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_81 (Call (LocInfoE loc_83 (global_alloc)) [@{expr} LocInfoE loc_84 (i2v (layout_of struct_list_node).(ly_size) size_t) ]))) ;
        locinfo: loc_40 ;
        LocInfoE loc_77 ((LocInfoE loc_78 (!{PtrOp} (LocInfoE loc_79 ("node1")))) at{struct_list_node} "val") <-{ IntOp i32 }
          LocInfoE loc_80 (i2v 1 i32) ;
        locinfo: loc_41 ;
        LocInfoE loc_73 ((LocInfoE loc_74 (!{PtrOp} (LocInfoE loc_75 ("node1")))) at{struct_list_node} "next") <-{ PtrOp }
          LocInfoE loc_76 (NULL) ;
        "node2" <-{ PtrOp }
          LocInfoE loc_67 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_67 (Call (LocInfoE loc_69 (global_alloc)) [@{expr} LocInfoE loc_70 (i2v (layout_of struct_list_node).(ly_size) size_t) ]))) ;
        locinfo: loc_43 ;
        LocInfoE loc_63 ((LocInfoE loc_64 (!{PtrOp} (LocInfoE loc_65 ("node2")))) at{struct_list_node} "val") <-{ IntOp i32 }
          LocInfoE loc_66 (i2v 2 i32) ;
        locinfo: loc_44 ;
        LocInfoE loc_59 ((LocInfoE loc_60 (!{PtrOp} (LocInfoE loc_61 ("node2")))) at{struct_list_node} "next") <-{ PtrOp }
          LocInfoE loc_62 (NULL) ;
        locinfo: loc_45 ;
        expr: (LocInfoE loc_45 (Call (LocInfoE loc_54 (global_append)) [@{expr} LocInfoE loc_55 (&(LocInfoE loc_56 ("node1"))) ;
        LocInfoE loc_57 (use{PtrOp} (LocInfoE loc_58 ("node2"))) ])) ;
        locinfo: loc_49 ;
        if: LocInfoE loc_49 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_49 ((LocInfoE loc_50 (use{PtrOp} (LocInfoE loc_51 ("node1")))) !={PtrOp, PtrOp} (LocInfoE loc_52 (NULL)))))
        then
        Goto "#1"
        else
        Goto "#2"
      ]> $
      <[ "#1" :=
        Return (VOID)
      ]> $
      <[ "#2" :=
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
