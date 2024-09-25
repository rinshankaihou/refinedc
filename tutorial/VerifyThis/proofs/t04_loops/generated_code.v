From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/VerifyThis/t04_loops.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "tutorial/VerifyThis/t04_loops.c".
  Definition loc_2 : location_info := LocationInfo file_0 63 2 63 47.
  Definition loc_3 : location_info := LocationInfo file_0 63 9 63 46.
  Definition loc_4 : location_info := LocationInfo file_0 63 9 63 32.
  Definition loc_5 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_6 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_7 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_8 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_11 : location_info := LocationInfo file_1 16 2 16 23.
  Definition loc_12 : location_info := LocationInfo file_1 17 2 17 28.
  Definition loc_13 : location_info := LocationInfo file_1 18 2 23 3.
  Definition loc_14 : location_info := LocationInfo file_1 24 2 24 18.
  Definition loc_15 : location_info := LocationInfo file_1 24 9 24 17.
  Definition loc_16 : location_info := LocationInfo file_1 24 9 24 17.
  Definition loc_17 : location_info := LocationInfo file_1 18 30 23 3.
  Definition loc_18 : location_info := LocationInfo file_1 19 4 19 18.
  Definition loc_19 : location_info := LocationInfo file_1 20 4 20 23.
  Definition loc_20 : location_info := LocationInfo file_1 21 4 21 17.
  Definition loc_21 : location_info := LocationInfo file_1 22 4 22 12.
  Definition loc_22 : location_info := LocationInfo file_1 22 4 22 5.
  Definition loc_23 : location_info := LocationInfo file_1 22 8 22 11.
  Definition loc_24 : location_info := LocationInfo file_1 22 8 22 11.
  Definition loc_25 : location_info := LocationInfo file_1 21 4 21 12.
  Definition loc_26 : location_info := LocationInfo file_1 21 15 21 16.
  Definition loc_27 : location_info := LocationInfo file_1 21 15 21 16.
  Definition loc_28 : location_info := LocationInfo file_1 20 4 20 11.
  Definition loc_29 : location_info := LocationInfo file_1 20 4 20 5.
  Definition loc_30 : location_info := LocationInfo file_1 20 4 20 5.
  Definition loc_31 : location_info := LocationInfo file_1 20 14 20 22.
  Definition loc_32 : location_info := LocationInfo file_1 20 14 20 22.
  Definition loc_33 : location_info := LocationInfo file_1 19 4 19 7.
  Definition loc_34 : location_info := LocationInfo file_1 19 10 19 17.
  Definition loc_35 : location_info := LocationInfo file_1 19 10 19 17.
  Definition loc_36 : location_info := LocationInfo file_1 19 10 19 11.
  Definition loc_37 : location_info := LocationInfo file_1 19 10 19 11.
  Definition loc_38 : location_info := LocationInfo file_1 18 9 18 28.
  Definition loc_39 : location_info := LocationInfo file_1 18 9 18 10.
  Definition loc_40 : location_info := LocationInfo file_1 18 9 18 10.
  Definition loc_41 : location_info := LocationInfo file_1 18 14 18 28.
  Definition loc_42 : location_info := LocationInfo file_1 17 2 17 10.
  Definition loc_43 : location_info := LocationInfo file_1 17 13 17 27.
  Definition loc_46 : location_info := LocationInfo file_1 31 2 31 23.
  Definition loc_47 : location_info := LocationInfo file_1 32 2 32 28.
  Definition loc_48 : location_info := LocationInfo file_1 36 2 41 3.
  Definition loc_49 : location_info := LocationInfo file_1 42 2 42 18.
  Definition loc_50 : location_info := LocationInfo file_1 42 9 42 17.
  Definition loc_51 : location_info := LocationInfo file_1 42 9 42 17.
  Definition loc_52 : location_info := LocationInfo file_1 36 30 41 3.
  Definition loc_53 : location_info := LocationInfo file_1 37 4 37 18.
  Definition loc_54 : location_info := LocationInfo file_1 38 4 38 23.
  Definition loc_55 : location_info := LocationInfo file_1 39 4 39 17.
  Definition loc_56 : location_info := LocationInfo file_1 40 4 40 12.
  Definition loc_57 : location_info := LocationInfo file_1 40 4 40 5.
  Definition loc_58 : location_info := LocationInfo file_1 40 8 40 11.
  Definition loc_59 : location_info := LocationInfo file_1 40 8 40 11.
  Definition loc_60 : location_info := LocationInfo file_1 39 4 39 12.
  Definition loc_61 : location_info := LocationInfo file_1 39 15 39 16.
  Definition loc_62 : location_info := LocationInfo file_1 39 15 39 16.
  Definition loc_63 : location_info := LocationInfo file_1 38 4 38 11.
  Definition loc_64 : location_info := LocationInfo file_1 38 4 38 5.
  Definition loc_65 : location_info := LocationInfo file_1 38 4 38 5.
  Definition loc_66 : location_info := LocationInfo file_1 38 14 38 22.
  Definition loc_67 : location_info := LocationInfo file_1 38 14 38 22.
  Definition loc_68 : location_info := LocationInfo file_1 37 4 37 7.
  Definition loc_69 : location_info := LocationInfo file_1 37 10 37 17.
  Definition loc_70 : location_info := LocationInfo file_1 37 10 37 17.
  Definition loc_71 : location_info := LocationInfo file_1 37 10 37 11.
  Definition loc_72 : location_info := LocationInfo file_1 37 10 37 11.
  Definition loc_73 : location_info := LocationInfo file_1 36 9 36 28.
  Definition loc_74 : location_info := LocationInfo file_1 36 9 36 10.
  Definition loc_75 : location_info := LocationInfo file_1 36 9 36 10.
  Definition loc_76 : location_info := LocationInfo file_1 36 14 36 28.
  Definition loc_77 : location_info := LocationInfo file_1 32 2 32 10.
  Definition loc_78 : location_info := LocationInfo file_1 32 13 32 27.
  Definition loc_81 : location_info := LocationInfo file_1 50 2 54 3.
  Definition loc_82 : location_info := LocationInfo file_1 50 27 52 3.
  Definition loc_83 : location_info := LocationInfo file_1 51 4 51 11.
  Definition loc_84 : location_info := LocationInfo file_1 51 4 51 6.
  Definition loc_85 : location_info := LocationInfo file_1 51 5 51 6.
  Definition loc_86 : location_info := LocationInfo file_1 51 5 51 6.
  Definition loc_87 : location_info := LocationInfo file_1 51 9 51 10.
  Definition loc_88 : location_info := LocationInfo file_1 51 9 51 10.
  Definition loc_89 : location_info := LocationInfo file_1 52 9 54 3.
  Definition loc_90 : location_info := LocationInfo file_1 53 4 53 27.
  Definition loc_91 : location_info := LocationInfo file_1 53 4 53 10.
  Definition loc_92 : location_info := LocationInfo file_1 53 4 53 10.
  Definition loc_93 : location_info := LocationInfo file_1 53 11 53 22.
  Definition loc_94 : location_info := LocationInfo file_1 53 12 53 22.
  Definition loc_95 : location_info := LocationInfo file_1 53 12 53 16.
  Definition loc_96 : location_info := LocationInfo file_1 53 12 53 16.
  Definition loc_97 : location_info := LocationInfo file_1 53 14 53 15.
  Definition loc_98 : location_info := LocationInfo file_1 53 14 53 15.
  Definition loc_99 : location_info := LocationInfo file_1 53 24 53 25.
  Definition loc_100 : location_info := LocationInfo file_1 53 24 53 25.
  Definition loc_101 : location_info := LocationInfo file_1 50 5 50 25.
  Definition loc_102 : location_info := LocationInfo file_1 50 5 50 7.
  Definition loc_103 : location_info := LocationInfo file_1 50 5 50 7.
  Definition loc_104 : location_info := LocationInfo file_1 50 6 50 7.
  Definition loc_105 : location_info := LocationInfo file_1 50 6 50 7.
  Definition loc_106 : location_info := LocationInfo file_1 50 11 50 25.
  Definition loc_109 : location_info := LocationInfo file_1 58 2 58 18.
  Definition loc_110 : location_info := LocationInfo file_1 59 2 61 3.
  Definition loc_111 : location_info := LocationInfo file_1 62 2 62 11.
  Definition loc_112 : location_info := LocationInfo file_1 62 2 62 6.
  Definition loc_113 : location_info := LocationInfo file_1 62 3 62 6.
  Definition loc_114 : location_info := LocationInfo file_1 62 3 62 6.
  Definition loc_115 : location_info := LocationInfo file_1 62 9 62 10.
  Definition loc_116 : location_info := LocationInfo file_1 62 9 62 10.
  Definition loc_117 : location_info := LocationInfo file_1 59 32 61 3.
  Definition loc_118 : location_info := LocationInfo file_1 60 4 60 24.
  Definition loc_119 : location_info := LocationInfo file_1 60 4 60 7.
  Definition loc_120 : location_info := LocationInfo file_1 60 10 60 23.
  Definition loc_121 : location_info := LocationInfo file_1 60 11 60 23.
  Definition loc_122 : location_info := LocationInfo file_1 60 11 60 17.
  Definition loc_123 : location_info := LocationInfo file_1 60 11 60 17.
  Definition loc_124 : location_info := LocationInfo file_1 60 13 60 16.
  Definition loc_125 : location_info := LocationInfo file_1 60 13 60 16.
  Definition loc_126 : location_info := LocationInfo file_1 59 8 59 30.
  Definition loc_127 : location_info := LocationInfo file_1 59 8 59 12.
  Definition loc_128 : location_info := LocationInfo file_1 59 8 59 12.
  Definition loc_129 : location_info := LocationInfo file_1 59 9 59 12.
  Definition loc_130 : location_info := LocationInfo file_1 59 9 59 12.
  Definition loc_131 : location_info := LocationInfo file_1 59 16 59 30.
  Definition loc_132 : location_info := LocationInfo file_1 58 16 58 17.
  Definition loc_133 : location_info := LocationInfo file_1 58 16 58 17.
  Definition loc_138 : location_info := LocationInfo file_1 69 2 69 18.
  Definition loc_139 : location_info := LocationInfo file_1 73 2 75 3.
  Definition loc_140 : location_info := LocationInfo file_1 76 2 76 11.
  Definition loc_141 : location_info := LocationInfo file_1 76 2 76 6.
  Definition loc_142 : location_info := LocationInfo file_1 76 3 76 6.
  Definition loc_143 : location_info := LocationInfo file_1 76 3 76 6.
  Definition loc_144 : location_info := LocationInfo file_1 76 9 76 10.
  Definition loc_145 : location_info := LocationInfo file_1 76 9 76 10.
  Definition loc_146 : location_info := LocationInfo file_1 73 32 75 3.
  Definition loc_147 : location_info := LocationInfo file_1 74 4 74 24.
  Definition loc_148 : location_info := LocationInfo file_1 74 4 74 7.
  Definition loc_149 : location_info := LocationInfo file_1 74 10 74 23.
  Definition loc_150 : location_info := LocationInfo file_1 74 11 74 23.
  Definition loc_151 : location_info := LocationInfo file_1 74 11 74 17.
  Definition loc_152 : location_info := LocationInfo file_1 74 11 74 17.
  Definition loc_153 : location_info := LocationInfo file_1 74 13 74 16.
  Definition loc_154 : location_info := LocationInfo file_1 74 13 74 16.
  Definition loc_155 : location_info := LocationInfo file_1 73 8 73 30.
  Definition loc_156 : location_info := LocationInfo file_1 73 8 73 12.
  Definition loc_157 : location_info := LocationInfo file_1 73 8 73 12.
  Definition loc_158 : location_info := LocationInfo file_1 73 9 73 12.
  Definition loc_159 : location_info := LocationInfo file_1 73 9 73 12.
  Definition loc_160 : location_info := LocationInfo file_1 73 16 73 30.
  Definition loc_161 : location_info := LocationInfo file_1 69 16 69 17.
  Definition loc_162 : location_info := LocationInfo file_1 69 16 69 17.

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

  (* Definition of function [reverse_1]. *)
  Definition impl_reverse_1 : function := {|
    f_args := [
      ("l", void*)
    ];
    f_local_vars := [
      ("reversed", void*);
      ("tmp", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_12 ;
        LocInfoE loc_42 ("reversed") <-{ PtrOp } LocInfoE loc_43 (NULL) ;
        locinfo: loc_13 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_38 ;
        if{IntOp i32, None}: LocInfoE loc_38 ((LocInfoE loc_39 (use{PtrOp} (LocInfoE loc_40 ("l")))) !={PtrOp, PtrOp, i32} (LocInfoE loc_41 (NULL)))
        then
        locinfo: loc_18 ;
          Goto "#2"
        else
        locinfo: loc_14 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_18 ;
        LocInfoE loc_33 ("tmp") <-{ PtrOp }
          LocInfoE loc_34 (use{PtrOp} (LocInfoE loc_35 ((LocInfoE loc_36 (!{PtrOp} (LocInfoE loc_37 ("l")))) at{struct_list_node} "next"))) ;
        locinfo: loc_19 ;
        LocInfoE loc_28 ((LocInfoE loc_29 (!{PtrOp} (LocInfoE loc_30 ("l")))) at{struct_list_node} "next") <-{ PtrOp }
          LocInfoE loc_31 (use{PtrOp} (LocInfoE loc_32 ("reversed"))) ;
        locinfo: loc_20 ;
        LocInfoE loc_25 ("reversed") <-{ PtrOp }
          LocInfoE loc_26 (use{PtrOp} (LocInfoE loc_27 ("l"))) ;
        locinfo: loc_21 ;
        LocInfoE loc_22 ("l") <-{ PtrOp }
          LocInfoE loc_23 (use{PtrOp} (LocInfoE loc_24 ("tmp"))) ;
        locinfo: loc_13 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_14 ;
        Return (LocInfoE loc_15 (use{PtrOp} (LocInfoE loc_16 ("reversed"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [reverse_2]. *)
  Definition impl_reverse_2 : function := {|
    f_args := [
      ("l", void*)
    ];
    f_local_vars := [
      ("reversed", void*);
      ("tmp", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_47 ;
        LocInfoE loc_77 ("reversed") <-{ PtrOp } LocInfoE loc_78 (NULL) ;
        locinfo: loc_48 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_73 ;
        if{IntOp i32, None}: LocInfoE loc_73 ((LocInfoE loc_74 (use{PtrOp} (LocInfoE loc_75 ("l")))) !={PtrOp, PtrOp, i32} (LocInfoE loc_76 (NULL)))
        then
        locinfo: loc_53 ;
          Goto "#2"
        else
        locinfo: loc_49 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_53 ;
        LocInfoE loc_68 ("tmp") <-{ PtrOp }
          LocInfoE loc_69 (use{PtrOp} (LocInfoE loc_70 ((LocInfoE loc_71 (!{PtrOp} (LocInfoE loc_72 ("l")))) at{struct_list_node} "next"))) ;
        locinfo: loc_54 ;
        LocInfoE loc_63 ((LocInfoE loc_64 (!{PtrOp} (LocInfoE loc_65 ("l")))) at{struct_list_node} "next") <-{ PtrOp }
          LocInfoE loc_66 (use{PtrOp} (LocInfoE loc_67 ("reversed"))) ;
        locinfo: loc_55 ;
        LocInfoE loc_60 ("reversed") <-{ PtrOp }
          LocInfoE loc_61 (use{PtrOp} (LocInfoE loc_62 ("l"))) ;
        locinfo: loc_56 ;
        LocInfoE loc_57 ("l") <-{ PtrOp }
          LocInfoE loc_58 (use{PtrOp} (LocInfoE loc_59 ("tmp"))) ;
        locinfo: loc_48 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_49 ;
        Return (LocInfoE loc_50 (use{PtrOp} (LocInfoE loc_51 ("reversed"))))
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
        locinfo: loc_101 ;
        if{IntOp i32, None}: LocInfoE loc_101 ((LocInfoE loc_102 (use{PtrOp} (LocInfoE loc_104 (!{PtrOp} (LocInfoE loc_105 ("l")))))) ={PtrOp, PtrOp, i32} (LocInfoE loc_106 (NULL)))
        then
        locinfo: loc_83 ;
          Goto "#1"
        else
        locinfo: loc_90 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_83 ;
        LocInfoE loc_85 (!{PtrOp} (LocInfoE loc_86 ("l"))) <-{ PtrOp }
          LocInfoE loc_87 (use{PtrOp} (LocInfoE loc_88 ("k"))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_90 ;
        expr: (LocInfoE loc_90 (Call (LocInfoE loc_92 (global_append)) [@{expr} LocInfoE loc_93 (&(LocInfoE loc_94 ((LocInfoE loc_95 (!{PtrOp} (LocInfoE loc_97 (!{PtrOp} (LocInfoE loc_98 ("l")))))) at{struct_list_node} "next"))) ;
        LocInfoE loc_99 (use{PtrOp} (LocInfoE loc_100 ("k"))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [append_loop_1]. *)
  Definition impl_append_loop_1 : function := {|
    f_args := [
      ("l", void*);
      ("k", void*)
    ];
    f_local_vars := [
      ("end", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "end" <-{ PtrOp }
          LocInfoE loc_132 (use{PtrOp} (LocInfoE loc_133 ("l"))) ;
        locinfo: loc_110 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_126 ;
        if{IntOp i32, None}: LocInfoE loc_126 ((LocInfoE loc_127 (use{PtrOp} (LocInfoE loc_129 (!{PtrOp} (LocInfoE loc_130 ("end")))))) !={PtrOp, PtrOp, i32} (LocInfoE loc_131 (NULL)))
        then
        locinfo: loc_118 ;
          Goto "#2"
        else
        locinfo: loc_111 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_118 ;
        LocInfoE loc_119 ("end") <-{ PtrOp }
          LocInfoE loc_120 (&(LocInfoE loc_121 ((LocInfoE loc_122 (!{PtrOp} (LocInfoE loc_124 (!{PtrOp} (LocInfoE loc_125 ("end")))))) at{struct_list_node} "next"))) ;
        locinfo: loc_110 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_111 ;
        LocInfoE loc_113 (!{PtrOp} (LocInfoE loc_114 ("end"))) <-{ PtrOp }
          LocInfoE loc_115 (use{PtrOp} (LocInfoE loc_116 ("k"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [append_loop_2]. *)
  Definition impl_append_loop_2 : function := {|
    f_args := [
      ("l", void*);
      ("k", void*)
    ];
    f_local_vars := [
      ("end", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "end" <-{ PtrOp }
          LocInfoE loc_161 (use{PtrOp} (LocInfoE loc_162 ("l"))) ;
        locinfo: loc_139 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_155 ;
        if{IntOp i32, None}: LocInfoE loc_155 ((LocInfoE loc_156 (use{PtrOp} (LocInfoE loc_158 (!{PtrOp} (LocInfoE loc_159 ("end")))))) !={PtrOp, PtrOp, i32} (LocInfoE loc_160 (NULL)))
        then
        locinfo: loc_147 ;
          Goto "#2"
        else
        locinfo: loc_140 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_147 ;
        LocInfoE loc_148 ("end") <-{ PtrOp }
          LocInfoE loc_149 (&(LocInfoE loc_150 ((LocInfoE loc_151 (!{PtrOp} (LocInfoE loc_153 (!{PtrOp} (LocInfoE loc_154 ("end")))))) at{struct_list_node} "next"))) ;
        locinfo: loc_139 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_140 ;
        LocInfoE loc_142 (!{PtrOp} (LocInfoE loc_143 ("end"))) <-{ PtrOp }
          LocInfoE loc_144 (use{PtrOp} (LocInfoE loc_145 ("k"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
