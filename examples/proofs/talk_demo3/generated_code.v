From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/talk_demo3.c]. *)
Section code.
  Definition file_0 : string := "include/assume.h".
  Definition file_1 : string := "examples/talk_demo3.c".
  Definition file_2 : string := "include/refinedc.h".
  Definition file_3 : string := "include/refinedc_malloc.h".
  Definition loc_2 : location_info := LocationInfo file_2 63 2 63 47.
  Definition loc_3 : location_info := LocationInfo file_2 63 9 63 46.
  Definition loc_4 : location_info := LocationInfo file_2 63 9 63 32.
  Definition loc_5 : location_info := LocationInfo file_2 63 33 63 37.
  Definition loc_6 : location_info := LocationInfo file_2 63 33 63 37.
  Definition loc_7 : location_info := LocationInfo file_2 63 39 63 45.
  Definition loc_8 : location_info := LocationInfo file_2 63 39 63 45.
  Definition loc_11 : location_info := LocationInfo file_0 10 2 10 12.
  Definition loc_12 : location_info := LocationInfo file_0 15 2 15 11.
  Definition loc_13 : location_info := LocationInfo file_0 15 9 15 10.
  Definition loc_14 : location_info := LocationInfo file_0 10 10 10 12.
  Definition loc_15 : location_info := LocationInfo file_0 10 8 10 9.
  Definition loc_18 : location_info := LocationInfo file_3 33 2 33 23.
  Definition loc_19 : location_info := LocationInfo file_3 34 2 34 42.
  Definition loc_20 : location_info := LocationInfo file_3 35 2 35 11.
  Definition loc_21 : location_info := LocationInfo file_3 35 9 35 10.
  Definition loc_22 : location_info := LocationInfo file_3 35 9 35 10.
  Definition loc_23 : location_info := LocationInfo file_3 34 26 34 42.
  Definition loc_24 : location_info := LocationInfo file_3 34 28 34 40.
  Definition loc_25 : location_info := LocationInfo file_3 34 28 34 37.
  Definition loc_26 : location_info := LocationInfo file_3 34 28 34 37.
  Definition loc_27 : location_info := LocationInfo file_3 34 2 34 42.
  Definition loc_28 : location_info := LocationInfo file_3 34 5 34 24.
  Definition loc_29 : location_info := LocationInfo file_3 34 5 34 6.
  Definition loc_30 : location_info := LocationInfo file_3 34 5 34 6.
  Definition loc_31 : location_info := LocationInfo file_3 34 10 34 24.
  Definition loc_32 : location_info := LocationInfo file_3 33 12 33 22.
  Definition loc_33 : location_info := LocationInfo file_3 33 12 33 18.
  Definition loc_34 : location_info := LocationInfo file_3 33 12 33 18.
  Definition loc_35 : location_info := LocationInfo file_3 33 19 33 21.
  Definition loc_36 : location_info := LocationInfo file_3 33 19 33 21.
  Definition loc_41 : location_info := LocationInfo file_1 21 2 25 3.
  Definition loc_42 : location_info := LocationInfo file_1 21 27 23 3.
  Definition loc_43 : location_info := LocationInfo file_1 22 4 22 11.
  Definition loc_44 : location_info := LocationInfo file_1 22 4 22 6.
  Definition loc_45 : location_info := LocationInfo file_1 22 5 22 6.
  Definition loc_46 : location_info := LocationInfo file_1 22 5 22 6.
  Definition loc_47 : location_info := LocationInfo file_1 22 9 22 10.
  Definition loc_48 : location_info := LocationInfo file_1 22 9 22 10.
  Definition loc_49 : location_info := LocationInfo file_1 23 9 25 3.
  Definition loc_50 : location_info := LocationInfo file_1 24 4 24 27.
  Definition loc_51 : location_info := LocationInfo file_1 24 4 24 10.
  Definition loc_52 : location_info := LocationInfo file_1 24 4 24 10.
  Definition loc_53 : location_info := LocationInfo file_1 24 11 24 22.
  Definition loc_54 : location_info := LocationInfo file_1 24 12 24 22.
  Definition loc_55 : location_info := LocationInfo file_1 24 12 24 16.
  Definition loc_56 : location_info := LocationInfo file_1 24 12 24 16.
  Definition loc_57 : location_info := LocationInfo file_1 24 14 24 15.
  Definition loc_58 : location_info := LocationInfo file_1 24 14 24 15.
  Definition loc_59 : location_info := LocationInfo file_1 24 24 24 25.
  Definition loc_60 : location_info := LocationInfo file_1 24 24 24 25.
  Definition loc_61 : location_info := LocationInfo file_1 21 5 21 25.
  Definition loc_62 : location_info := LocationInfo file_1 21 5 21 7.
  Definition loc_63 : location_info := LocationInfo file_1 21 5 21 7.
  Definition loc_64 : location_info := LocationInfo file_1 21 6 21 7.
  Definition loc_65 : location_info := LocationInfo file_1 21 6 21 7.
  Definition loc_66 : location_info := LocationInfo file_1 21 11 21 25.
  Definition loc_69 : location_info := LocationInfo file_1 30 2 30 63.
  Definition loc_70 : location_info := LocationInfo file_1 31 2 31 17.
  Definition loc_71 : location_info := LocationInfo file_1 31 18 31 47.
  Definition loc_72 : location_info := LocationInfo file_1 32 2 32 63.
  Definition loc_73 : location_info := LocationInfo file_1 33 2 33 17.
  Definition loc_74 : location_info := LocationInfo file_1 33 18 33 47.
  Definition loc_75 : location_info := LocationInfo file_1 34 2 34 24.
  Definition loc_76 : location_info := LocationInfo file_1 35 2 37 3.
  Definition loc_77 : location_info := LocationInfo file_1 35 30 37 3.
  Definition loc_78 : location_info := LocationInfo file_1 36 4 36 28.
  Definition loc_79 : location_info := LocationInfo file_1 36 11 36 26.
  Definition loc_80 : location_info := LocationInfo file_1 36 11 36 21.
  Definition loc_81 : location_info := LocationInfo file_1 36 11 36 21.
  Definition loc_82 : location_info := LocationInfo file_1 36 11 36 16.
  Definition loc_83 : location_info := LocationInfo file_1 36 11 36 16.
  Definition loc_84 : location_info := LocationInfo file_1 36 25 36 26.
  Definition loc_85 : location_info := LocationInfo file_1 35 2 37 3.
  Definition loc_86 : location_info := LocationInfo file_1 35 5 35 28.
  Definition loc_87 : location_info := LocationInfo file_1 35 5 35 10.
  Definition loc_88 : location_info := LocationInfo file_1 35 5 35 10.
  Definition loc_89 : location_info := LocationInfo file_1 35 14 35 28.
  Definition loc_90 : location_info := LocationInfo file_1 34 2 34 8.
  Definition loc_91 : location_info := LocationInfo file_1 34 2 34 8.
  Definition loc_92 : location_info := LocationInfo file_1 34 9 34 15.
  Definition loc_93 : location_info := LocationInfo file_1 34 10 34 15.
  Definition loc_94 : location_info := LocationInfo file_1 34 17 34 22.
  Definition loc_95 : location_info := LocationInfo file_1 34 17 34 22.
  Definition loc_96 : location_info := LocationInfo file_1 33 18 33 29.
  Definition loc_97 : location_info := LocationInfo file_1 33 18 33 23.
  Definition loc_98 : location_info := LocationInfo file_1 33 18 33 23.
  Definition loc_99 : location_info := LocationInfo file_1 33 32 33 46.
  Definition loc_100 : location_info := LocationInfo file_1 33 2 33 12.
  Definition loc_101 : location_info := LocationInfo file_1 33 2 33 7.
  Definition loc_102 : location_info := LocationInfo file_1 33 2 33 7.
  Definition loc_103 : location_info := LocationInfo file_1 33 15 33 16.
  Definition loc_104 : location_info := LocationInfo file_1 32 29 32 62.
  Definition loc_105 : location_info := LocationInfo file_1 32 29 32 36.
  Definition loc_106 : location_info := LocationInfo file_1 32 29 32 36.
  Definition loc_107 : location_info := LocationInfo file_1 32 37 32 61.
  Definition loc_110 : location_info := LocationInfo file_1 31 18 31 29.
  Definition loc_111 : location_info := LocationInfo file_1 31 18 31 23.
  Definition loc_112 : location_info := LocationInfo file_1 31 18 31 23.
  Definition loc_113 : location_info := LocationInfo file_1 31 32 31 46.
  Definition loc_114 : location_info := LocationInfo file_1 31 2 31 12.
  Definition loc_115 : location_info := LocationInfo file_1 31 2 31 7.
  Definition loc_116 : location_info := LocationInfo file_1 31 2 31 7.
  Definition loc_117 : location_info := LocationInfo file_1 31 15 31 16.
  Definition loc_118 : location_info := LocationInfo file_1 30 29 30 62.
  Definition loc_119 : location_info := LocationInfo file_1 30 29 30 36.
  Definition loc_120 : location_info := LocationInfo file_1 30 29 30 36.
  Definition loc_121 : location_info := LocationInfo file_1 30 37 30 61.

  (* Definition of struct [__cerbty_unnamed_tag_486]. *)
  Program Definition struct___cerbty_unnamed_tag_486 := {|
    sl_members := [
      (Some "__dummy_max_align_t", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

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

  (* Definition of function [safe_exit]. *)
  Definition impl_safe_exit : function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_11 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_15 ;
        if{IntOp i32, None}: LocInfoE loc_15 (i2v 1 i32)
        then
        locinfo: loc_11 ;
          Goto "#2"
        else
        locinfo: loc_12 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_11 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_12 ;
        Return (LocInfoE loc_13 (i2v 0 i32))
      ]> $∅
    )%E
  |}.

  (* Definition of function [xmalloc]. *)
  Definition impl_xmalloc (global_malloc global_safe_exit : loc): function := {|
    f_args := [
      ("sz", it_layout size_t)
    ];
    f_local_vars := [
      ("p", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "p" <-{ PtrOp }
          LocInfoE loc_32 (Call (LocInfoE loc_34 (global_malloc)) [@{expr} LocInfoE loc_35 (use{IntOp size_t} (LocInfoE loc_36 ("sz"))) ]) ;
        locinfo: loc_28 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_28 ((LocInfoE loc_29 (use{PtrOp} (LocInfoE loc_30 ("p")))) ={PtrOp, PtrOp, i32} (LocInfoE loc_31 (NULL)))
        then
        locinfo: loc_24 ;
          Goto "#2"
        else
        locinfo: loc_20 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_20 ;
        Return (LocInfoE loc_21 (use{PtrOp} (LocInfoE loc_22 ("p"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_24 ;
        expr: (LocInfoE loc_24 (Call (LocInfoE loc_26 (global_safe_exit)) [@{expr}  ])) ;
        locinfo: loc_20 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_20 ;
        Goto "#1"
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
        locinfo: loc_61 ;
        if{IntOp i32, None}: LocInfoE loc_61 ((LocInfoE loc_62 (use{PtrOp} (LocInfoE loc_64 (!{PtrOp} (LocInfoE loc_65 ("l")))))) ={PtrOp, PtrOp, i32} (LocInfoE loc_66 (NULL)))
        then
        locinfo: loc_43 ;
          Goto "#1"
        else
        locinfo: loc_50 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_43 ;
        LocInfoE loc_45 (!{PtrOp} (LocInfoE loc_46 ("l"))) <-{ PtrOp }
          LocInfoE loc_47 (use{PtrOp} (LocInfoE loc_48 ("k"))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_50 ;
        expr: (LocInfoE loc_50 (Call (LocInfoE loc_52 (global_append)) [@{expr} LocInfoE loc_53 (&(LocInfoE loc_54 ((LocInfoE loc_55 (!{PtrOp} (LocInfoE loc_57 (!{PtrOp} (LocInfoE loc_58 ("l")))))) at{struct_list_node} "next"))) ;
        LocInfoE loc_59 (use{PtrOp} (LocInfoE loc_60 ("k"))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [test]. *)
  Definition impl_test (global_append global_xmalloc : loc): function := {|
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
          LocInfoE loc_118 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_118 (Call (LocInfoE loc_120 (global_xmalloc)) [@{expr} LocInfoE loc_121 (i2v (layout_of struct_list_node).(ly_size) size_t) ]))) ;
        locinfo: loc_70 ;
        LocInfoE loc_114 ((LocInfoE loc_115 (!{PtrOp} (LocInfoE loc_116 ("node1")))) at{struct_list_node} "val") <-{ IntOp i32 }
          LocInfoE loc_117 (i2v 1 i32) ;
        locinfo: loc_71 ;
        LocInfoE loc_110 ((LocInfoE loc_111 (!{PtrOp} (LocInfoE loc_112 ("node1")))) at{struct_list_node} "next") <-{ PtrOp }
          LocInfoE loc_113 (NULL) ;
        "node2" <-{ PtrOp }
          LocInfoE loc_104 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_104 (Call (LocInfoE loc_106 (global_xmalloc)) [@{expr} LocInfoE loc_107 (i2v (layout_of struct_list_node).(ly_size) size_t) ]))) ;
        locinfo: loc_73 ;
        LocInfoE loc_100 ((LocInfoE loc_101 (!{PtrOp} (LocInfoE loc_102 ("node2")))) at{struct_list_node} "val") <-{ IntOp i32 }
          LocInfoE loc_103 (i2v 2 i32) ;
        locinfo: loc_74 ;
        LocInfoE loc_96 ((LocInfoE loc_97 (!{PtrOp} (LocInfoE loc_98 ("node2")))) at{struct_list_node} "next") <-{ PtrOp }
          LocInfoE loc_99 (NULL) ;
        locinfo: loc_75 ;
        expr: (LocInfoE loc_75 (Call (LocInfoE loc_91 (global_append)) [@{expr} LocInfoE loc_92 (&(LocInfoE loc_93 ("node1"))) ;
        LocInfoE loc_94 (use{PtrOp} (LocInfoE loc_95 ("node2"))) ])) ;
        locinfo: loc_86 ;
        if{IntOp i32, None}: LocInfoE loc_86 ((LocInfoE loc_87 (use{PtrOp} (LocInfoE loc_88 ("node1")))) !={PtrOp, PtrOp, i32} (LocInfoE loc_89 (NULL)))
        then
        locinfo: loc_78 ;
          Goto "#1"
        else
        Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_78 ;
        assert{IntOp i32}: (LocInfoE loc_79 ((LocInfoE loc_80 (use{IntOp i32} (LocInfoE loc_81 ((LocInfoE loc_82 (!{PtrOp} (LocInfoE loc_83 ("node1")))) at{struct_list_node} "val")))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_84 (i2v 1 i32)))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
