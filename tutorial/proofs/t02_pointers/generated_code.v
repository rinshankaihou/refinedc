From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/t02_pointers.c]. *)
Section code.
  Definition file_0 : string := "tutorial/t02_pointers.c".
  Definition loc_2 : location_info := LocationInfo file_0 14 4 14 14.
  Definition loc_3 : location_info := LocationInfo file_0 14 11 14 13.
  Definition loc_4 : location_info := LocationInfo file_0 14 11 14 13.
  Definition loc_5 : location_info := LocationInfo file_0 14 12 14 13.
  Definition loc_6 : location_info := LocationInfo file_0 14 12 14 13.
  Definition loc_9 : location_info := LocationInfo file_0 19 4 19 18.
  Definition loc_10 : location_info := LocationInfo file_0 20 4 20 32.
  Definition loc_11 : location_info := LocationInfo file_0 21 4 21 26.
  Definition loc_12 : location_info := LocationInfo file_0 22 4 22 23.
  Definition loc_13 : location_info := LocationInfo file_0 22 11 22 21.
  Definition loc_14 : location_info := LocationInfo file_0 22 11 22 16.
  Definition loc_15 : location_info := LocationInfo file_0 22 11 22 16.
  Definition loc_16 : location_info := LocationInfo file_0 22 20 22 21.
  Definition loc_17 : location_info := LocationInfo file_0 21 11 21 24.
  Definition loc_18 : location_info := LocationInfo file_0 21 11 21 16.
  Definition loc_19 : location_info := LocationInfo file_0 21 11 21 16.
  Definition loc_20 : location_info := LocationInfo file_0 21 20 21 24.
  Definition loc_21 : location_info := LocationInfo file_0 21 20 21 24.
  Definition loc_22 : location_info := LocationInfo file_0 20 15 20 31.
  Definition loc_23 : location_info := LocationInfo file_0 20 15 20 23.
  Definition loc_24 : location_info := LocationInfo file_0 20 15 20 23.
  Definition loc_25 : location_info := LocationInfo file_0 20 24 20 30.
  Definition loc_26 : location_info := LocationInfo file_0 20 25 20 30.
  Definition loc_29 : location_info := LocationInfo file_0 19 16 19 17.
  Definition loc_34 : location_info := LocationInfo file_0 29 4 29 19.
  Definition loc_35 : location_info := LocationInfo file_0 30 4 30 11.
  Definition loc_36 : location_info := LocationInfo file_0 31 4 31 24.
  Definition loc_37 : location_info := LocationInfo file_0 31 11 31 22.
  Definition loc_38 : location_info := LocationInfo file_0 31 11 31 13.
  Definition loc_39 : location_info := LocationInfo file_0 31 11 31 13.
  Definition loc_40 : location_info := LocationInfo file_0 31 12 31 13.
  Definition loc_41 : location_info := LocationInfo file_0 31 12 31 13.
  Definition loc_42 : location_info := LocationInfo file_0 31 17 31 22.
  Definition loc_43 : location_info := LocationInfo file_0 31 17 31 22.
  Definition loc_44 : location_info := LocationInfo file_0 30 4 30 6.
  Definition loc_45 : location_info := LocationInfo file_0 30 5 30 6.
  Definition loc_46 : location_info := LocationInfo file_0 30 5 30 6.
  Definition loc_47 : location_info := LocationInfo file_0 30 9 30 10.
  Definition loc_48 : location_info := LocationInfo file_0 29 16 29 18.
  Definition loc_49 : location_info := LocationInfo file_0 29 16 29 18.
  Definition loc_50 : location_info := LocationInfo file_0 29 17 29 18.
  Definition loc_51 : location_info := LocationInfo file_0 29 17 29 18.
  Definition loc_56 : location_info := LocationInfo file_0 36 4 36 23.
  Definition loc_57 : location_info := LocationInfo file_0 38 4 38 13.
  Definition loc_58 : location_info := LocationInfo file_0 39 4 45 5.
  Definition loc_59 : location_info := LocationInfo file_0 39 10 42 5.
  Definition loc_60 : location_info := LocationInfo file_0 40 8 40 20.
  Definition loc_61 : location_info := LocationInfo file_0 41 8 41 19.
  Definition loc_62 : location_info := LocationInfo file_0 41 8 41 13.
  Definition loc_63 : location_info := LocationInfo file_0 41 16 41 18.
  Definition loc_64 : location_info := LocationInfo file_0 41 16 41 18.
  Definition loc_65 : location_info := LocationInfo file_0 41 17 41 18.
  Definition loc_66 : location_info := LocationInfo file_0 41 17 41 18.
  Definition loc_67 : location_info := LocationInfo file_0 40 8 40 13.
  Definition loc_68 : location_info := LocationInfo file_0 40 16 40 19.
  Definition loc_69 : location_info := LocationInfo file_0 40 16 40 19.
  Definition loc_70 : location_info := LocationInfo file_0 42 11 45 5.
  Definition loc_71 : location_info := LocationInfo file_0 43 8 43 19.
  Definition loc_72 : location_info := LocationInfo file_0 44 8 44 20.
  Definition loc_73 : location_info := LocationInfo file_0 44 8 44 13.
  Definition loc_74 : location_info := LocationInfo file_0 44 16 44 19.
  Definition loc_75 : location_info := LocationInfo file_0 44 16 44 19.
  Definition loc_76 : location_info := LocationInfo file_0 43 8 43 13.
  Definition loc_77 : location_info := LocationInfo file_0 43 16 43 18.
  Definition loc_78 : location_info := LocationInfo file_0 43 16 43 18.
  Definition loc_79 : location_info := LocationInfo file_0 43 17 43 18.
  Definition loc_80 : location_info := LocationInfo file_0 43 17 43 18.
  Definition loc_81 : location_info := LocationInfo file_0 39 7 39 8.
  Definition loc_82 : location_info := LocationInfo file_0 39 7 39 8.
  Definition loc_83 : location_info := LocationInfo file_0 38 4 38 5.
  Definition loc_84 : location_info := LocationInfo file_0 38 8 38 12.
  Definition loc_85 : location_info := LocationInfo file_0 38 9 38 12.
  Definition loc_86 : location_info := LocationInfo file_0 36 14 36 15.
  Definition loc_91 : location_info := LocationInfo file_0 52 4 52 11.
  Definition loc_92 : location_info := LocationInfo file_0 53 4 53 11.
  Definition loc_93 : location_info := LocationInfo file_0 54 4 60 5.
  Definition loc_94 : location_info := LocationInfo file_0 54 10 57 5.
  Definition loc_95 : location_info := LocationInfo file_0 55 8 55 12.
  Definition loc_96 : location_info := LocationInfo file_0 56 8 56 12.
  Definition loc_97 : location_info := LocationInfo file_0 56 8 56 11.
  Definition loc_98 : location_info := LocationInfo file_0 56 8 56 11.
  Definition loc_99 : location_info := LocationInfo file_0 56 9 56 11.
  Definition loc_100 : location_info := LocationInfo file_0 56 9 56 11.
  Definition loc_101 : location_info := LocationInfo file_0 55 8 55 11.
  Definition loc_102 : location_info := LocationInfo file_0 55 8 55 11.
  Definition loc_103 : location_info := LocationInfo file_0 55 9 55 11.
  Definition loc_104 : location_info := LocationInfo file_0 55 9 55 11.
  Definition loc_105 : location_info := LocationInfo file_0 57 11 60 5.
  Definition loc_106 : location_info := LocationInfo file_0 58 8 58 12.
  Definition loc_107 : location_info := LocationInfo file_0 59 8 59 12.
  Definition loc_108 : location_info := LocationInfo file_0 59 8 59 11.
  Definition loc_109 : location_info := LocationInfo file_0 59 8 59 11.
  Definition loc_110 : location_info := LocationInfo file_0 59 9 59 11.
  Definition loc_111 : location_info := LocationInfo file_0 59 9 59 11.
  Definition loc_112 : location_info := LocationInfo file_0 58 8 58 11.
  Definition loc_113 : location_info := LocationInfo file_0 58 8 58 11.
  Definition loc_114 : location_info := LocationInfo file_0 58 9 58 11.
  Definition loc_115 : location_info := LocationInfo file_0 58 9 58 11.
  Definition loc_116 : location_info := LocationInfo file_0 54 7 54 8.
  Definition loc_117 : location_info := LocationInfo file_0 54 7 54 8.
  Definition loc_118 : location_info := LocationInfo file_0 53 4 53 6.
  Definition loc_119 : location_info := LocationInfo file_0 53 9 53 10.
  Definition loc_120 : location_info := LocationInfo file_0 53 9 53 10.
  Definition loc_121 : location_info := LocationInfo file_0 52 4 52 6.
  Definition loc_122 : location_info := LocationInfo file_0 52 9 52 10.
  Definition loc_123 : location_info := LocationInfo file_0 52 9 52 10.
  Definition loc_126 : location_info := LocationInfo file_0 67 4 67 12.
  Definition loc_127 : location_info := LocationInfo file_0 68 4 74 5.
  Definition loc_128 : location_info := LocationInfo file_0 68 10 71 5.
  Definition loc_129 : location_info := LocationInfo file_0 69 8 69 13.
  Definition loc_130 : location_info := LocationInfo file_0 70 8 70 11.
  Definition loc_131 : location_info := LocationInfo file_0 70 8 70 10.
  Definition loc_132 : location_info := LocationInfo file_0 70 8 70 10.
  Definition loc_133 : location_info := LocationInfo file_0 70 9 70 10.
  Definition loc_134 : location_info := LocationInfo file_0 70 9 70 10.
  Definition loc_135 : location_info := LocationInfo file_0 69 8 69 12.
  Definition loc_136 : location_info := LocationInfo file_0 69 8 69 12.
  Definition loc_137 : location_info := LocationInfo file_0 69 9 69 12.
  Definition loc_138 : location_info := LocationInfo file_0 69 9 69 12.
  Definition loc_139 : location_info := LocationInfo file_0 69 10 69 12.
  Definition loc_140 : location_info := LocationInfo file_0 69 10 69 12.
  Definition loc_141 : location_info := LocationInfo file_0 71 11 74 5.
  Definition loc_142 : location_info := LocationInfo file_0 72 8 72 11.
  Definition loc_143 : location_info := LocationInfo file_0 73 8 73 13.
  Definition loc_144 : location_info := LocationInfo file_0 73 8 73 12.
  Definition loc_145 : location_info := LocationInfo file_0 73 8 73 12.
  Definition loc_146 : location_info := LocationInfo file_0 73 9 73 12.
  Definition loc_147 : location_info := LocationInfo file_0 73 9 73 12.
  Definition loc_148 : location_info := LocationInfo file_0 73 10 73 12.
  Definition loc_149 : location_info := LocationInfo file_0 73 10 73 12.
  Definition loc_150 : location_info := LocationInfo file_0 72 8 72 10.
  Definition loc_151 : location_info := LocationInfo file_0 72 8 72 10.
  Definition loc_152 : location_info := LocationInfo file_0 72 9 72 10.
  Definition loc_153 : location_info := LocationInfo file_0 72 9 72 10.
  Definition loc_154 : location_info := LocationInfo file_0 68 7 68 8.
  Definition loc_155 : location_info := LocationInfo file_0 68 7 68 8.
  Definition loc_156 : location_info := LocationInfo file_0 67 4 67 6.
  Definition loc_157 : location_info := LocationInfo file_0 67 9 67 11.
  Definition loc_158 : location_info := LocationInfo file_0 67 10 67 11.
  Definition loc_161 : location_info := LocationInfo file_0 81 2 81 11.
  Definition loc_162 : location_info := LocationInfo file_0 81 9 81 10.
  Definition loc_163 : location_info := LocationInfo file_0 81 9 81 10.
  Definition loc_166 : location_info := LocationInfo file_0 86 2 86 12.
  Definition loc_167 : location_info := LocationInfo file_0 87 2 87 41.
  Definition loc_168 : location_info := LocationInfo file_0 87 9 87 39.
  Definition loc_169 : location_info := LocationInfo file_0 87 9 87 34.
  Definition loc_170 : location_info := LocationInfo file_0 87 9 87 34.
  Definition loc_171 : location_info := LocationInfo file_0 87 10 87 34.
  Definition loc_172 : location_info := LocationInfo file_0 87 17 87 34.
  Definition loc_173 : location_info := LocationInfo file_0 87 17 87 23.
  Definition loc_174 : location_info := LocationInfo file_0 87 17 87 23.
  Definition loc_175 : location_info := LocationInfo file_0 87 24 87 26.
  Definition loc_176 : location_info := LocationInfo file_0 87 25 87 26.
  Definition loc_177 : location_info := LocationInfo file_0 87 28 87 33.
  Definition loc_178 : location_info := LocationInfo file_0 87 28 87 29.
  Definition loc_179 : location_info := LocationInfo file_0 87 32 87 33.
  Definition loc_180 : location_info := LocationInfo file_0 87 38 87 39.
  Definition loc_181 : location_info := LocationInfo file_0 86 10 86 11.

  (* Definition of function [read_int]. *)
  Definition impl_read_int : function := {|
    f_args := [
      ("a", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        Return (LocInfoE loc_3 (use{it_layout i32} (LocInfoE loc_5 (!{void*} (LocInfoE loc_6 ("a"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [use_read_int]. *)
  Definition impl_use_read_int (global_read_int : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
      ("local", it_layout i32);
      ("read", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "local" <-{ it_layout i32 } LocInfoE loc_29 (i2v 1 i32) ;
        "read" <-{ it_layout i32 }
          LocInfoE loc_22 (Call (LocInfoE loc_24 (global_read_int)) [@{expr} LocInfoE loc_25 (&(LocInfoE loc_26 ("local"))) ]) ;
        locinfo: loc_11 ;
        assert: (LocInfoE loc_17 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_17 ((LocInfoE loc_18 (use{it_layout i32} (LocInfoE loc_19 ("local")))) ={IntOp i32, IntOp i32} (LocInfoE loc_20 (use{it_layout i32} (LocInfoE loc_21 ("read")))))))) ;
        locinfo: loc_12 ;
        assert: (LocInfoE loc_13 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_13 ((LocInfoE loc_14 (use{it_layout i32} (LocInfoE loc_15 ("local")))) ={IntOp i32, IntOp i32} (LocInfoE loc_16 (i2v 1 i32)))))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [no_alias]. *)
  Definition impl_no_alias : function := {|
    f_args := [
      ("a", void*);
      ("b", void*)
    ];
    f_local_vars := [
      ("old_b", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "old_b" <-{ it_layout i32 }
          LocInfoE loc_48 (use{it_layout i32} (LocInfoE loc_50 (!{void*} (LocInfoE loc_51 ("b"))))) ;
        locinfo: loc_35 ;
        LocInfoE loc_45 (!{void*} (LocInfoE loc_46 ("a"))) <-{ it_layout i32 }
          LocInfoE loc_47 (i2v 1 i32) ;
        locinfo: loc_36 ;
        assert: (LocInfoE loc_37 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_37 ((LocInfoE loc_38 (use{it_layout i32} (LocInfoE loc_40 (!{void*} (LocInfoE loc_41 ("b")))))) ={IntOp i32, IntOp i32} (LocInfoE loc_42 (use{it_layout i32} (LocInfoE loc_43 ("old_b")))))))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [local_vars]. *)
  Definition impl_local_vars : function := {|
    f_args := [
      ("b", it_layout bool_it)
    ];
    f_local_vars := [
      ("var", it_layout i32);
      ("dummy", it_layout i32);
      ("p", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "var" <-{ it_layout i32 } LocInfoE loc_86 (i2v 1 i32) ;
        locinfo: loc_57 ;
        LocInfoE loc_83 ("p") <-{ void* }
          LocInfoE loc_84 (&(LocInfoE loc_85 ("var"))) ;
        locinfo: loc_81 ;
        if: LocInfoE loc_81 (use{it_layout bool_it} (LocInfoE loc_82 ("b")))
        then
        locinfo: loc_60 ;
          Goto "#1"
        else
        locinfo: loc_71 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_60 ;
        LocInfoE loc_67 ("dummy") <-{ it_layout i32 }
          LocInfoE loc_68 (use{it_layout i32} (LocInfoE loc_69 ("var"))) ;
        locinfo: loc_61 ;
        LocInfoE loc_62 ("dummy") <-{ it_layout i32 }
          LocInfoE loc_63 (use{it_layout i32} (LocInfoE loc_65 (!{void*} (LocInfoE loc_66 ("p"))))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_71 ;
        LocInfoE loc_76 ("dummy") <-{ it_layout i32 }
          LocInfoE loc_77 (use{it_layout i32} (LocInfoE loc_79 (!{void*} (LocInfoE loc_80 ("p"))))) ;
        locinfo: loc_72 ;
        LocInfoE loc_73 ("dummy") <-{ it_layout i32 }
          LocInfoE loc_74 (use{it_layout i32} (LocInfoE loc_75 ("var"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [ptrs]. *)
  Definition impl_ptrs : function := {|
    f_args := [
      ("b", it_layout bool_it);
      ("p", void*)
    ];
    f_local_vars := [
      ("p1", void*);
      ("p2", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_91 ;
        LocInfoE loc_121 ("p1") <-{ void* }
          LocInfoE loc_122 (use{void*} (LocInfoE loc_123 ("p"))) ;
        locinfo: loc_92 ;
        LocInfoE loc_118 ("p2") <-{ void* }
          LocInfoE loc_119 (use{void*} (LocInfoE loc_120 ("p"))) ;
        locinfo: loc_116 ;
        if: LocInfoE loc_116 (use{it_layout bool_it} (LocInfoE loc_117 ("b")))
        then
        locinfo: loc_95 ;
          Goto "#1"
        else
        locinfo: loc_106 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_95 ;
        expr: (LocInfoE loc_101 (use{it_layout i32} (LocInfoE loc_103 (!{void*} (LocInfoE loc_104 ("p1")))))) ;
        locinfo: loc_96 ;
        expr: (LocInfoE loc_97 (use{it_layout i32} (LocInfoE loc_99 (!{void*} (LocInfoE loc_100 ("p2")))))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_106 ;
        expr: (LocInfoE loc_112 (use{it_layout i32} (LocInfoE loc_114 (!{void*} (LocInfoE loc_115 ("p2")))))) ;
        locinfo: loc_107 ;
        expr: (LocInfoE loc_108 (use{it_layout i32} (LocInfoE loc_110 (!{void*} (LocInfoE loc_111 ("p1")))))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [ptrs2]. *)
  Definition impl_ptrs2 : function := {|
    f_args := [
      ("b", it_layout bool_it);
      ("p", void*)
    ];
    f_local_vars := [
      ("p1", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_126 ;
        LocInfoE loc_156 ("p1") <-{ void* }
          LocInfoE loc_157 (&(LocInfoE loc_158 ("p"))) ;
        locinfo: loc_154 ;
        if: LocInfoE loc_154 (use{it_layout bool_it} (LocInfoE loc_155 ("b")))
        then
        locinfo: loc_129 ;
          Goto "#1"
        else
        locinfo: loc_142 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_129 ;
        expr: (LocInfoE loc_135 (use{it_layout i32} (LocInfoE loc_137 (!{void*} (LocInfoE loc_139 (!{void*} (LocInfoE loc_140 ("p1")))))))) ;
        locinfo: loc_130 ;
        expr: (LocInfoE loc_131 (use{it_layout i32} (LocInfoE loc_133 (!{void*} (LocInfoE loc_134 ("p")))))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_142 ;
        expr: (LocInfoE loc_150 (use{it_layout i32} (LocInfoE loc_152 (!{void*} (LocInfoE loc_153 ("p")))))) ;
        locinfo: loc_143 ;
        expr: (LocInfoE loc_144 (use{it_layout i32} (LocInfoE loc_146 (!{void*} (LocInfoE loc_148 (!{void*} (LocInfoE loc_149 ("p1")))))))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [ptr_id]. *)
  Definition impl_ptr_id : function := {|
    f_args := [
      ("p", void*);
      ("x", it_layout i32)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_161 ;
        Return (LocInfoE loc_162 (use{void*} (LocInfoE loc_163 ("p"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [ptr_id_test]. *)
  Definition impl_ptr_id_test (global_ptr_id : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
      ("x", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "x" <-{ it_layout i32 } LocInfoE loc_181 (i2v 1 i32) ;
        locinfo: loc_167 ;
        assert: (LocInfoE loc_168 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_168 ((LocInfoE loc_169 (use{it_layout i32} (LocInfoE loc_171 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_172 (LValue (LocInfoE loc_172 (Call (LocInfoE loc_174 (global_ptr_id)) [@{expr} LocInfoE loc_175 (&(LocInfoE loc_176 ("x"))) ;
        LocInfoE loc_177 ((LocInfoE loc_178 (i2v 1 i32)) +{IntOp i32, IntOp i32} (LocInfoE loc_179 (i2v 1 i32))) ])))))))) ={IntOp i32, IntOp i32} (LocInfoE loc_180 (i2v 1 i32)))))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
