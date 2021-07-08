From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/talk_demo3.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "examples/talk_demo3.c".
  Definition loc_2 : location_info := LocationInfo file_0 50 2 50 47.
  Definition loc_3 : location_info := LocationInfo file_0 50 9 50 46.
  Definition loc_4 : location_info := LocationInfo file_0 50 9 50 32.
  Definition loc_5 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_6 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_7 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_8 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_11 : location_info := LocationInfo file_1 21 2 25 3.
  Definition loc_12 : location_info := LocationInfo file_1 21 27 23 3.
  Definition loc_13 : location_info := LocationInfo file_1 22 4 22 11.
  Definition loc_14 : location_info := LocationInfo file_1 22 4 22 6.
  Definition loc_15 : location_info := LocationInfo file_1 22 5 22 6.
  Definition loc_16 : location_info := LocationInfo file_1 22 5 22 6.
  Definition loc_17 : location_info := LocationInfo file_1 22 9 22 10.
  Definition loc_18 : location_info := LocationInfo file_1 22 9 22 10.
  Definition loc_19 : location_info := LocationInfo file_1 23 9 25 3.
  Definition loc_20 : location_info := LocationInfo file_1 24 4 24 27.
  Definition loc_21 : location_info := LocationInfo file_1 24 4 24 10.
  Definition loc_22 : location_info := LocationInfo file_1 24 4 24 10.
  Definition loc_23 : location_info := LocationInfo file_1 24 11 24 22.
  Definition loc_24 : location_info := LocationInfo file_1 24 12 24 22.
  Definition loc_25 : location_info := LocationInfo file_1 24 12 24 16.
  Definition loc_26 : location_info := LocationInfo file_1 24 12 24 16.
  Definition loc_27 : location_info := LocationInfo file_1 24 14 24 15.
  Definition loc_28 : location_info := LocationInfo file_1 24 14 24 15.
  Definition loc_29 : location_info := LocationInfo file_1 24 24 24 25.
  Definition loc_30 : location_info := LocationInfo file_1 24 24 24 25.
  Definition loc_31 : location_info := LocationInfo file_1 21 5 21 25.
  Definition loc_32 : location_info := LocationInfo file_1 21 5 21 7.
  Definition loc_33 : location_info := LocationInfo file_1 21 5 21 7.
  Definition loc_34 : location_info := LocationInfo file_1 21 6 21 7.
  Definition loc_35 : location_info := LocationInfo file_1 21 6 21 7.
  Definition loc_36 : location_info := LocationInfo file_1 21 11 21 25.
  Definition loc_39 : location_info := LocationInfo file_1 30 2 30 61.
  Definition loc_40 : location_info := LocationInfo file_1 31 2 31 17.
  Definition loc_41 : location_info := LocationInfo file_1 31 18 31 47.
  Definition loc_42 : location_info := LocationInfo file_1 32 2 32 61.
  Definition loc_43 : location_info := LocationInfo file_1 33 2 33 17.
  Definition loc_44 : location_info := LocationInfo file_1 33 18 33 47.
  Definition loc_45 : location_info := LocationInfo file_1 34 2 34 24.
  Definition loc_46 : location_info := LocationInfo file_1 35 2 37 3.
  Definition loc_47 : location_info := LocationInfo file_1 35 30 37 3.
  Definition loc_48 : location_info := LocationInfo file_1 36 4 36 28.
  Definition loc_49 : location_info := LocationInfo file_1 36 11 36 26.
  Definition loc_50 : location_info := LocationInfo file_1 36 11 36 21.
  Definition loc_51 : location_info := LocationInfo file_1 36 11 36 21.
  Definition loc_52 : location_info := LocationInfo file_1 36 11 36 16.
  Definition loc_53 : location_info := LocationInfo file_1 36 11 36 16.
  Definition loc_54 : location_info := LocationInfo file_1 36 25 36 26.
  Definition loc_56 : location_info := LocationInfo file_1 35 5 35 28.
  Definition loc_57 : location_info := LocationInfo file_1 35 5 35 10.
  Definition loc_58 : location_info := LocationInfo file_1 35 5 35 10.
  Definition loc_59 : location_info := LocationInfo file_1 35 14 35 28.
  Definition loc_60 : location_info := LocationInfo file_1 34 2 34 8.
  Definition loc_61 : location_info := LocationInfo file_1 34 2 34 8.
  Definition loc_62 : location_info := LocationInfo file_1 34 9 34 15.
  Definition loc_63 : location_info := LocationInfo file_1 34 10 34 15.
  Definition loc_64 : location_info := LocationInfo file_1 34 17 34 22.
  Definition loc_65 : location_info := LocationInfo file_1 34 17 34 22.
  Definition loc_66 : location_info := LocationInfo file_1 33 18 33 29.
  Definition loc_67 : location_info := LocationInfo file_1 33 18 33 23.
  Definition loc_68 : location_info := LocationInfo file_1 33 18 33 23.
  Definition loc_69 : location_info := LocationInfo file_1 33 32 33 46.
  Definition loc_70 : location_info := LocationInfo file_1 33 2 33 12.
  Definition loc_71 : location_info := LocationInfo file_1 33 2 33 7.
  Definition loc_72 : location_info := LocationInfo file_1 33 2 33 7.
  Definition loc_73 : location_info := LocationInfo file_1 33 15 33 16.
  Definition loc_74 : location_info := LocationInfo file_1 32 29 32 60.
  Definition loc_75 : location_info := LocationInfo file_1 32 29 32 34.
  Definition loc_76 : location_info := LocationInfo file_1 32 29 32 34.
  Definition loc_77 : location_info := LocationInfo file_1 32 35 32 59.
  Definition loc_80 : location_info := LocationInfo file_1 31 18 31 29.
  Definition loc_81 : location_info := LocationInfo file_1 31 18 31 23.
  Definition loc_82 : location_info := LocationInfo file_1 31 18 31 23.
  Definition loc_83 : location_info := LocationInfo file_1 31 32 31 46.
  Definition loc_84 : location_info := LocationInfo file_1 31 2 31 12.
  Definition loc_85 : location_info := LocationInfo file_1 31 2 31 7.
  Definition loc_86 : location_info := LocationInfo file_1 31 2 31 7.
  Definition loc_87 : location_info := LocationInfo file_1 31 15 31 16.
  Definition loc_88 : location_info := LocationInfo file_1 30 29 30 60.
  Definition loc_89 : location_info := LocationInfo file_1 30 29 30 34.
  Definition loc_90 : location_info := LocationInfo file_1 30 29 30 34.
  Definition loc_91 : location_info := LocationInfo file_1 30 35 30 59.

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
        Return (LocInfoE loc_3 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_5 (use{it_layout uintptr_t} (LocInfoE loc_6 ("to")))) (LocInfoE loc_7 (use{void*} (LocInfoE loc_8 ("from"))))))
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
        if: LocInfoE loc_31 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_31 ((LocInfoE loc_32 (use{void*} (LocInfoE loc_34 (!{void*} (LocInfoE loc_35 ("l")))))) ={PtrOp, PtrOp} (LocInfoE loc_36 (NULL)))))
        then
        locinfo: loc_13 ;
          Goto "#1"
        else
        locinfo: loc_20 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_13 ;
        LocInfoE loc_15 (!{void*} (LocInfoE loc_16 ("l"))) <-{ void* }
          LocInfoE loc_17 (use{void*} (LocInfoE loc_18 ("k"))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_20 ;
        expr: (LocInfoE loc_20 (Call (LocInfoE loc_22 (global_append)) [@{expr} LocInfoE loc_23 (&(LocInfoE loc_24 ((LocInfoE loc_25 (!{void*} (LocInfoE loc_27 (!{void*} (LocInfoE loc_28 ("l")))))) at{struct_list_node} "next"))) ;
        LocInfoE loc_29 (use{void*} (LocInfoE loc_30 ("k"))) ])) ;
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
        "node1" <-{ void* }
          LocInfoE loc_88 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_88 (Call (LocInfoE loc_90 (global_alloc)) [@{expr} LocInfoE loc_91 (i2v (layout_of struct_list_node).(ly_size) size_t) ]))) ;
        locinfo: loc_40 ;
        LocInfoE loc_84 ((LocInfoE loc_85 (!{void*} (LocInfoE loc_86 ("node1")))) at{struct_list_node} "val") <-{ it_layout i32 }
          LocInfoE loc_87 (i2v 1 i32) ;
        locinfo: loc_41 ;
        LocInfoE loc_80 ((LocInfoE loc_81 (!{void*} (LocInfoE loc_82 ("node1")))) at{struct_list_node} "next") <-{ void* }
          LocInfoE loc_83 (NULL) ;
        "node2" <-{ void* }
          LocInfoE loc_74 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_74 (Call (LocInfoE loc_76 (global_alloc)) [@{expr} LocInfoE loc_77 (i2v (layout_of struct_list_node).(ly_size) size_t) ]))) ;
        locinfo: loc_43 ;
        LocInfoE loc_70 ((LocInfoE loc_71 (!{void*} (LocInfoE loc_72 ("node2")))) at{struct_list_node} "val") <-{ it_layout i32 }
          LocInfoE loc_73 (i2v 2 i32) ;
        locinfo: loc_44 ;
        LocInfoE loc_66 ((LocInfoE loc_67 (!{void*} (LocInfoE loc_68 ("node2")))) at{struct_list_node} "next") <-{ void* }
          LocInfoE loc_69 (NULL) ;
        locinfo: loc_45 ;
        expr: (LocInfoE loc_45 (Call (LocInfoE loc_61 (global_append)) [@{expr} LocInfoE loc_62 (&(LocInfoE loc_63 ("node1"))) ;
        LocInfoE loc_64 (use{void*} (LocInfoE loc_65 ("node2"))) ])) ;
        locinfo: loc_56 ;
        if: LocInfoE loc_56 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_56 ((LocInfoE loc_57 (use{void*} (LocInfoE loc_58 ("node1")))) !={PtrOp, PtrOp} (LocInfoE loc_59 (NULL)))))
        then
        locinfo: loc_48 ;
          Goto "#1"
        else
        Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_48 ;
        assert: (LocInfoE loc_49 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_49 ((LocInfoE loc_50 (use{it_layout i32} (LocInfoE loc_51 ((LocInfoE loc_52 (!{void*} (LocInfoE loc_53 ("node1")))) at{struct_list_node} "val")))) ={IntOp i32, IntOp i32} (LocInfoE loc_54 (i2v 1 i32)))))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
