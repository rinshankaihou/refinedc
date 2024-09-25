From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/VerifyThis/t02_ownership.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "tutorial/VerifyThis/t02_ownership.c".
  Definition loc_2 : location_info := LocationInfo file_0 63 2 63 47.
  Definition loc_3 : location_info := LocationInfo file_0 63 9 63 46.
  Definition loc_4 : location_info := LocationInfo file_0 63 9 63 32.
  Definition loc_5 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_6 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_7 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_8 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_11 : location_info := LocationInfo file_1 48 2 52 3.
  Definition loc_12 : location_info := LocationInfo file_1 48 27 50 3.
  Definition loc_13 : location_info := LocationInfo file_1 49 4 49 11.
  Definition loc_14 : location_info := LocationInfo file_1 49 4 49 6.
  Definition loc_15 : location_info := LocationInfo file_1 49 5 49 6.
  Definition loc_16 : location_info := LocationInfo file_1 49 5 49 6.
  Definition loc_17 : location_info := LocationInfo file_1 49 9 49 10.
  Definition loc_18 : location_info := LocationInfo file_1 49 9 49 10.
  Definition loc_19 : location_info := LocationInfo file_1 50 9 52 3.
  Definition loc_20 : location_info := LocationInfo file_1 51 4 51 27.
  Definition loc_21 : location_info := LocationInfo file_1 51 4 51 10.
  Definition loc_22 : location_info := LocationInfo file_1 51 4 51 10.
  Definition loc_23 : location_info := LocationInfo file_1 51 11 51 22.
  Definition loc_24 : location_info := LocationInfo file_1 51 12 51 22.
  Definition loc_25 : location_info := LocationInfo file_1 51 12 51 16.
  Definition loc_26 : location_info := LocationInfo file_1 51 12 51 16.
  Definition loc_27 : location_info := LocationInfo file_1 51 14 51 15.
  Definition loc_28 : location_info := LocationInfo file_1 51 14 51 15.
  Definition loc_29 : location_info := LocationInfo file_1 51 24 51 25.
  Definition loc_30 : location_info := LocationInfo file_1 51 24 51 25.
  Definition loc_31 : location_info := LocationInfo file_1 48 5 48 25.
  Definition loc_32 : location_info := LocationInfo file_1 48 5 48 7.
  Definition loc_33 : location_info := LocationInfo file_1 48 5 48 7.
  Definition loc_34 : location_info := LocationInfo file_1 48 6 48 7.
  Definition loc_35 : location_info := LocationInfo file_1 48 6 48 7.
  Definition loc_36 : location_info := LocationInfo file_1 48 11 48 25.
  Definition loc_39 : location_info := LocationInfo file_1 59 2 59 62.
  Definition loc_40 : location_info := LocationInfo file_1 60 2 60 17.
  Definition loc_41 : location_info := LocationInfo file_1 60 18 60 47.
  Definition loc_42 : location_info := LocationInfo file_1 61 2 61 62.
  Definition loc_43 : location_info := LocationInfo file_1 62 2 62 17.
  Definition loc_44 : location_info := LocationInfo file_1 62 18 62 47.
  Definition loc_45 : location_info := LocationInfo file_1 64 2 64 24.
  Definition loc_46 : location_info := LocationInfo file_1 65 2 67 3.
  Definition loc_47 : location_info := LocationInfo file_1 65 30 67 3.
  Definition loc_48 : location_info := LocationInfo file_1 65 2 67 3.
  Definition loc_49 : location_info := LocationInfo file_1 65 5 65 28.
  Definition loc_50 : location_info := LocationInfo file_1 65 5 65 10.
  Definition loc_51 : location_info := LocationInfo file_1 65 5 65 10.
  Definition loc_52 : location_info := LocationInfo file_1 65 14 65 28.
  Definition loc_53 : location_info := LocationInfo file_1 64 2 64 8.
  Definition loc_54 : location_info := LocationInfo file_1 64 2 64 8.
  Definition loc_55 : location_info := LocationInfo file_1 64 9 64 15.
  Definition loc_56 : location_info := LocationInfo file_1 64 10 64 15.
  Definition loc_57 : location_info := LocationInfo file_1 64 17 64 22.
  Definition loc_58 : location_info := LocationInfo file_1 64 17 64 22.
  Definition loc_59 : location_info := LocationInfo file_1 62 18 62 29.
  Definition loc_60 : location_info := LocationInfo file_1 62 18 62 23.
  Definition loc_61 : location_info := LocationInfo file_1 62 18 62 23.
  Definition loc_62 : location_info := LocationInfo file_1 62 32 62 46.
  Definition loc_63 : location_info := LocationInfo file_1 62 2 62 12.
  Definition loc_64 : location_info := LocationInfo file_1 62 2 62 7.
  Definition loc_65 : location_info := LocationInfo file_1 62 2 62 7.
  Definition loc_66 : location_info := LocationInfo file_1 62 15 62 16.
  Definition loc_67 : location_info := LocationInfo file_1 61 29 61 61.
  Definition loc_68 : location_info := LocationInfo file_1 61 29 61 35.
  Definition loc_69 : location_info := LocationInfo file_1 61 29 61 35.
  Definition loc_70 : location_info := LocationInfo file_1 61 36 61 60.
  Definition loc_73 : location_info := LocationInfo file_1 60 18 60 29.
  Definition loc_74 : location_info := LocationInfo file_1 60 18 60 23.
  Definition loc_75 : location_info := LocationInfo file_1 60 18 60 23.
  Definition loc_76 : location_info := LocationInfo file_1 60 32 60 46.
  Definition loc_77 : location_info := LocationInfo file_1 60 2 60 12.
  Definition loc_78 : location_info := LocationInfo file_1 60 2 60 7.
  Definition loc_79 : location_info := LocationInfo file_1 60 2 60 7.
  Definition loc_80 : location_info := LocationInfo file_1 60 15 60 16.
  Definition loc_81 : location_info := LocationInfo file_1 59 29 59 61.
  Definition loc_82 : location_info := LocationInfo file_1 59 29 59 35.
  Definition loc_83 : location_info := LocationInfo file_1 59 29 59 35.
  Definition loc_84 : location_info := LocationInfo file_1 59 36 59 60.
  Definition loc_89 : location_info := LocationInfo file_1 80 2 84 3.
  Definition loc_90 : location_info := LocationInfo file_1 80 27 82 3.
  Definition loc_91 : location_info := LocationInfo file_1 81 4 81 11.
  Definition loc_92 : location_info := LocationInfo file_1 81 4 81 6.
  Definition loc_93 : location_info := LocationInfo file_1 81 5 81 6.
  Definition loc_94 : location_info := LocationInfo file_1 81 5 81 6.
  Definition loc_95 : location_info := LocationInfo file_1 81 9 81 10.
  Definition loc_96 : location_info := LocationInfo file_1 81 9 81 10.
  Definition loc_97 : location_info := LocationInfo file_1 82 9 84 3.
  Definition loc_98 : location_info := LocationInfo file_1 83 4 83 29.
  Definition loc_99 : location_info := LocationInfo file_1 83 4 83 12.
  Definition loc_100 : location_info := LocationInfo file_1 83 4 83 12.
  Definition loc_101 : location_info := LocationInfo file_1 83 13 83 24.
  Definition loc_102 : location_info := LocationInfo file_1 83 14 83 24.
  Definition loc_103 : location_info := LocationInfo file_1 83 14 83 18.
  Definition loc_104 : location_info := LocationInfo file_1 83 14 83 18.
  Definition loc_105 : location_info := LocationInfo file_1 83 16 83 17.
  Definition loc_106 : location_info := LocationInfo file_1 83 16 83 17.
  Definition loc_107 : location_info := LocationInfo file_1 83 26 83 27.
  Definition loc_108 : location_info := LocationInfo file_1 83 26 83 27.
  Definition loc_109 : location_info := LocationInfo file_1 80 5 80 25.
  Definition loc_110 : location_info := LocationInfo file_1 80 5 80 7.
  Definition loc_111 : location_info := LocationInfo file_1 80 5 80 7.
  Definition loc_112 : location_info := LocationInfo file_1 80 6 80 7.
  Definition loc_113 : location_info := LocationInfo file_1 80 6 80 7.
  Definition loc_114 : location_info := LocationInfo file_1 80 11 80 25.
  Definition loc_117 : location_info := LocationInfo file_1 91 2 91 62.
  Definition loc_118 : location_info := LocationInfo file_1 92 2 92 17.
  Definition loc_119 : location_info := LocationInfo file_1 92 18 92 47.
  Definition loc_120 : location_info := LocationInfo file_1 93 2 93 62.
  Definition loc_121 : location_info := LocationInfo file_1 94 2 94 17.
  Definition loc_122 : location_info := LocationInfo file_1 94 18 94 47.
  Definition loc_123 : location_info := LocationInfo file_1 96 2 96 26.
  Definition loc_124 : location_info := LocationInfo file_1 97 2 99 3.
  Definition loc_125 : location_info := LocationInfo file_1 97 30 99 3.
  Definition loc_126 : location_info := LocationInfo file_1 97 2 99 3.
  Definition loc_127 : location_info := LocationInfo file_1 97 5 97 28.
  Definition loc_128 : location_info := LocationInfo file_1 97 5 97 10.
  Definition loc_129 : location_info := LocationInfo file_1 97 5 97 10.
  Definition loc_130 : location_info := LocationInfo file_1 97 14 97 28.
  Definition loc_131 : location_info := LocationInfo file_1 96 2 96 10.
  Definition loc_132 : location_info := LocationInfo file_1 96 2 96 10.
  Definition loc_133 : location_info := LocationInfo file_1 96 11 96 17.
  Definition loc_134 : location_info := LocationInfo file_1 96 12 96 17.
  Definition loc_135 : location_info := LocationInfo file_1 96 19 96 24.
  Definition loc_136 : location_info := LocationInfo file_1 96 19 96 24.
  Definition loc_137 : location_info := LocationInfo file_1 94 18 94 29.
  Definition loc_138 : location_info := LocationInfo file_1 94 18 94 23.
  Definition loc_139 : location_info := LocationInfo file_1 94 18 94 23.
  Definition loc_140 : location_info := LocationInfo file_1 94 32 94 46.
  Definition loc_141 : location_info := LocationInfo file_1 94 2 94 12.
  Definition loc_142 : location_info := LocationInfo file_1 94 2 94 7.
  Definition loc_143 : location_info := LocationInfo file_1 94 2 94 7.
  Definition loc_144 : location_info := LocationInfo file_1 94 15 94 16.
  Definition loc_145 : location_info := LocationInfo file_1 93 29 93 61.
  Definition loc_146 : location_info := LocationInfo file_1 93 29 93 35.
  Definition loc_147 : location_info := LocationInfo file_1 93 29 93 35.
  Definition loc_148 : location_info := LocationInfo file_1 93 36 93 60.
  Definition loc_151 : location_info := LocationInfo file_1 92 18 92 29.
  Definition loc_152 : location_info := LocationInfo file_1 92 18 92 23.
  Definition loc_153 : location_info := LocationInfo file_1 92 18 92 23.
  Definition loc_154 : location_info := LocationInfo file_1 92 32 92 46.
  Definition loc_155 : location_info := LocationInfo file_1 92 2 92 12.
  Definition loc_156 : location_info := LocationInfo file_1 92 2 92 7.
  Definition loc_157 : location_info := LocationInfo file_1 92 2 92 7.
  Definition loc_158 : location_info := LocationInfo file_1 92 15 92 16.
  Definition loc_159 : location_info := LocationInfo file_1 91 29 91 61.
  Definition loc_160 : location_info := LocationInfo file_1 91 29 91 35.
  Definition loc_161 : location_info := LocationInfo file_1 91 29 91 35.
  Definition loc_162 : location_info := LocationInfo file_1 91 36 91 60.

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
        if{IntOp i32, None}: LocInfoE loc_31 ((LocInfoE loc_32 (use{PtrOp} (LocInfoE loc_34 (!{PtrOp} (LocInfoE loc_35 ("l")))))) ={PtrOp, PtrOp, i32} (LocInfoE loc_36 (NULL)))
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
  Definition impl_test (global_append global_talloc : loc): function := {|
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
          LocInfoE loc_81 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_81 (Call (LocInfoE loc_83 (global_talloc)) [@{expr} LocInfoE loc_84 (i2v (layout_of struct_list_node).(ly_size) size_t) ]))) ;
        locinfo: loc_40 ;
        LocInfoE loc_77 ((LocInfoE loc_78 (!{PtrOp} (LocInfoE loc_79 ("node1")))) at{struct_list_node} "val") <-{ IntOp i32 }
          LocInfoE loc_80 (i2v 1 i32) ;
        locinfo: loc_41 ;
        LocInfoE loc_73 ((LocInfoE loc_74 (!{PtrOp} (LocInfoE loc_75 ("node1")))) at{struct_list_node} "next") <-{ PtrOp }
          LocInfoE loc_76 (NULL) ;
        "node2" <-{ PtrOp }
          LocInfoE loc_67 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_67 (Call (LocInfoE loc_69 (global_talloc)) [@{expr} LocInfoE loc_70 (i2v (layout_of struct_list_node).(ly_size) size_t) ]))) ;
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
        if{IntOp i32, None}: LocInfoE loc_49 ((LocInfoE loc_50 (use{PtrOp} (LocInfoE loc_51 ("node1")))) !={PtrOp, PtrOp, i32} (LocInfoE loc_52 (NULL)))
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

  (* Definition of function [append_2]. *)
  Definition impl_append_2 (global_append_2 : loc): function := {|
    f_args := [
      ("l", void*);
      ("k", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_109 ;
        if{IntOp i32, None}: LocInfoE loc_109 ((LocInfoE loc_110 (use{PtrOp} (LocInfoE loc_112 (!{PtrOp} (LocInfoE loc_113 ("l")))))) ={PtrOp, PtrOp, i32} (LocInfoE loc_114 (NULL)))
        then
        locinfo: loc_91 ;
          Goto "#1"
        else
        locinfo: loc_98 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_91 ;
        LocInfoE loc_93 (!{PtrOp} (LocInfoE loc_94 ("l"))) <-{ PtrOp }
          LocInfoE loc_95 (use{PtrOp} (LocInfoE loc_96 ("k"))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_98 ;
        expr: (LocInfoE loc_98 (Call (LocInfoE loc_100 (global_append_2)) [@{expr} LocInfoE loc_101 (&(LocInfoE loc_102 ((LocInfoE loc_103 (!{PtrOp} (LocInfoE loc_105 (!{PtrOp} (LocInfoE loc_106 ("l")))))) at{struct_list_node} "next"))) ;
        LocInfoE loc_107 (use{PtrOp} (LocInfoE loc_108 ("k"))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_2]. *)
  Definition impl_test_2 (global_append_2 global_talloc : loc): function := {|
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
          LocInfoE loc_159 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_159 (Call (LocInfoE loc_161 (global_talloc)) [@{expr} LocInfoE loc_162 (i2v (layout_of struct_list_node).(ly_size) size_t) ]))) ;
        locinfo: loc_118 ;
        LocInfoE loc_155 ((LocInfoE loc_156 (!{PtrOp} (LocInfoE loc_157 ("node1")))) at{struct_list_node} "val") <-{ IntOp i32 }
          LocInfoE loc_158 (i2v 1 i32) ;
        locinfo: loc_119 ;
        LocInfoE loc_151 ((LocInfoE loc_152 (!{PtrOp} (LocInfoE loc_153 ("node1")))) at{struct_list_node} "next") <-{ PtrOp }
          LocInfoE loc_154 (NULL) ;
        "node2" <-{ PtrOp }
          LocInfoE loc_145 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_145 (Call (LocInfoE loc_147 (global_talloc)) [@{expr} LocInfoE loc_148 (i2v (layout_of struct_list_node).(ly_size) size_t) ]))) ;
        locinfo: loc_121 ;
        LocInfoE loc_141 ((LocInfoE loc_142 (!{PtrOp} (LocInfoE loc_143 ("node2")))) at{struct_list_node} "val") <-{ IntOp i32 }
          LocInfoE loc_144 (i2v 2 i32) ;
        locinfo: loc_122 ;
        LocInfoE loc_137 ((LocInfoE loc_138 (!{PtrOp} (LocInfoE loc_139 ("node2")))) at{struct_list_node} "next") <-{ PtrOp }
          LocInfoE loc_140 (NULL) ;
        locinfo: loc_123 ;
        expr: (LocInfoE loc_123 (Call (LocInfoE loc_132 (global_append_2)) [@{expr} LocInfoE loc_133 (&(LocInfoE loc_134 ("node1"))) ;
        LocInfoE loc_135 (use{PtrOp} (LocInfoE loc_136 ("node2"))) ])) ;
        locinfo: loc_127 ;
        if{IntOp i32, None}: LocInfoE loc_127 ((LocInfoE loc_128 (use{PtrOp} (LocInfoE loc_129 ("node1")))) !={PtrOp, PtrOp, i32} (LocInfoE loc_130 (NULL)))
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
