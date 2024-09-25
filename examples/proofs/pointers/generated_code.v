From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/pointers.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "examples/pointers.c".
  Definition loc_2 : location_info := LocationInfo file_0 63 2 63 47.
  Definition loc_3 : location_info := LocationInfo file_0 63 9 63 46.
  Definition loc_4 : location_info := LocationInfo file_0 63 9 63 32.
  Definition loc_5 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_6 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_7 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_8 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_11 : location_info := LocationInfo file_1 10 4 10 14.
  Definition loc_12 : location_info := LocationInfo file_1 10 11 10 13.
  Definition loc_13 : location_info := LocationInfo file_1 10 11 10 13.
  Definition loc_14 : location_info := LocationInfo file_1 10 12 10 13.
  Definition loc_15 : location_info := LocationInfo file_1 10 12 10 13.
  Definition loc_18 : location_info := LocationInfo file_1 15 4 15 18.
  Definition loc_19 : location_info := LocationInfo file_1 16 4 16 32.
  Definition loc_20 : location_info := LocationInfo file_1 17 4 17 26.
  Definition loc_21 : location_info := LocationInfo file_1 18 4 18 23.
  Definition loc_22 : location_info := LocationInfo file_1 18 11 18 21.
  Definition loc_23 : location_info := LocationInfo file_1 18 11 18 16.
  Definition loc_24 : location_info := LocationInfo file_1 18 11 18 16.
  Definition loc_25 : location_info := LocationInfo file_1 18 20 18 21.
  Definition loc_26 : location_info := LocationInfo file_1 17 11 17 24.
  Definition loc_27 : location_info := LocationInfo file_1 17 11 17 16.
  Definition loc_28 : location_info := LocationInfo file_1 17 11 17 16.
  Definition loc_29 : location_info := LocationInfo file_1 17 20 17 24.
  Definition loc_30 : location_info := LocationInfo file_1 17 20 17 24.
  Definition loc_31 : location_info := LocationInfo file_1 16 15 16 31.
  Definition loc_32 : location_info := LocationInfo file_1 16 15 16 23.
  Definition loc_33 : location_info := LocationInfo file_1 16 15 16 23.
  Definition loc_34 : location_info := LocationInfo file_1 16 24 16 30.
  Definition loc_35 : location_info := LocationInfo file_1 16 25 16 30.
  Definition loc_38 : location_info := LocationInfo file_1 15 16 15 17.
  Definition loc_43 : location_info := LocationInfo file_1 25 4 25 19.
  Definition loc_44 : location_info := LocationInfo file_1 26 4 26 11.
  Definition loc_45 : location_info := LocationInfo file_1 27 4 27 24.
  Definition loc_46 : location_info := LocationInfo file_1 27 11 27 22.
  Definition loc_47 : location_info := LocationInfo file_1 27 11 27 13.
  Definition loc_48 : location_info := LocationInfo file_1 27 11 27 13.
  Definition loc_49 : location_info := LocationInfo file_1 27 12 27 13.
  Definition loc_50 : location_info := LocationInfo file_1 27 12 27 13.
  Definition loc_51 : location_info := LocationInfo file_1 27 17 27 22.
  Definition loc_52 : location_info := LocationInfo file_1 27 17 27 22.
  Definition loc_53 : location_info := LocationInfo file_1 26 4 26 6.
  Definition loc_54 : location_info := LocationInfo file_1 26 5 26 6.
  Definition loc_55 : location_info := LocationInfo file_1 26 5 26 6.
  Definition loc_56 : location_info := LocationInfo file_1 26 9 26 10.
  Definition loc_57 : location_info := LocationInfo file_1 25 16 25 18.
  Definition loc_58 : location_info := LocationInfo file_1 25 16 25 18.
  Definition loc_59 : location_info := LocationInfo file_1 25 17 25 18.
  Definition loc_60 : location_info := LocationInfo file_1 25 17 25 18.
  Definition loc_65 : location_info := LocationInfo file_1 32 4 32 23.
  Definition loc_66 : location_info := LocationInfo file_1 33 4 33 11.
  Definition loc_67 : location_info := LocationInfo file_1 34 4 34 13.
  Definition loc_68 : location_info := LocationInfo file_1 35 4 41 5.
  Definition loc_69 : location_info := LocationInfo file_1 35 10 38 5.
  Definition loc_70 : location_info := LocationInfo file_1 36 8 36 20.
  Definition loc_71 : location_info := LocationInfo file_1 37 8 37 19.
  Definition loc_72 : location_info := LocationInfo file_1 37 8 37 13.
  Definition loc_73 : location_info := LocationInfo file_1 37 16 37 18.
  Definition loc_74 : location_info := LocationInfo file_1 37 16 37 18.
  Definition loc_75 : location_info := LocationInfo file_1 37 17 37 18.
  Definition loc_76 : location_info := LocationInfo file_1 37 17 37 18.
  Definition loc_77 : location_info := LocationInfo file_1 36 8 36 13.
  Definition loc_78 : location_info := LocationInfo file_1 36 16 36 19.
  Definition loc_79 : location_info := LocationInfo file_1 36 16 36 19.
  Definition loc_80 : location_info := LocationInfo file_1 38 11 41 5.
  Definition loc_81 : location_info := LocationInfo file_1 39 8 39 19.
  Definition loc_82 : location_info := LocationInfo file_1 40 8 40 20.
  Definition loc_83 : location_info := LocationInfo file_1 40 8 40 13.
  Definition loc_84 : location_info := LocationInfo file_1 40 16 40 19.
  Definition loc_85 : location_info := LocationInfo file_1 40 16 40 19.
  Definition loc_86 : location_info := LocationInfo file_1 39 8 39 13.
  Definition loc_87 : location_info := LocationInfo file_1 39 16 39 18.
  Definition loc_88 : location_info := LocationInfo file_1 39 16 39 18.
  Definition loc_89 : location_info := LocationInfo file_1 39 17 39 18.
  Definition loc_90 : location_info := LocationInfo file_1 39 17 39 18.
  Definition loc_91 : location_info := LocationInfo file_1 35 7 35 8.
  Definition loc_92 : location_info := LocationInfo file_1 35 7 35 8.
  Definition loc_93 : location_info := LocationInfo file_1 34 4 34 5.
  Definition loc_94 : location_info := LocationInfo file_1 34 8 34 12.
  Definition loc_95 : location_info := LocationInfo file_1 34 9 34 12.
  Definition loc_96 : location_info := LocationInfo file_1 32 14 32 15.
  Definition loc_101 : location_info := LocationInfo file_1 47 4 47 17.
  Definition loc_102 : location_info := LocationInfo file_1 48 4 48 11.
  Definition loc_103 : location_info := LocationInfo file_1 49 4 49 11.
  Definition loc_104 : location_info := LocationInfo file_1 50 4 56 5.
  Definition loc_105 : location_info := LocationInfo file_1 50 10 53 5.
  Definition loc_106 : location_info := LocationInfo file_1 51 8 51 12.
  Definition loc_107 : location_info := LocationInfo file_1 52 8 52 12.
  Definition loc_108 : location_info := LocationInfo file_1 52 8 52 11.
  Definition loc_109 : location_info := LocationInfo file_1 52 8 52 11.
  Definition loc_110 : location_info := LocationInfo file_1 52 9 52 11.
  Definition loc_111 : location_info := LocationInfo file_1 52 9 52 11.
  Definition loc_112 : location_info := LocationInfo file_1 51 8 51 11.
  Definition loc_113 : location_info := LocationInfo file_1 51 8 51 11.
  Definition loc_114 : location_info := LocationInfo file_1 51 9 51 11.
  Definition loc_115 : location_info := LocationInfo file_1 51 9 51 11.
  Definition loc_116 : location_info := LocationInfo file_1 53 11 56 5.
  Definition loc_117 : location_info := LocationInfo file_1 54 8 54 12.
  Definition loc_118 : location_info := LocationInfo file_1 55 8 55 12.
  Definition loc_119 : location_info := LocationInfo file_1 55 8 55 11.
  Definition loc_120 : location_info := LocationInfo file_1 55 8 55 11.
  Definition loc_121 : location_info := LocationInfo file_1 55 9 55 11.
  Definition loc_122 : location_info := LocationInfo file_1 55 9 55 11.
  Definition loc_123 : location_info := LocationInfo file_1 54 8 54 11.
  Definition loc_124 : location_info := LocationInfo file_1 54 8 54 11.
  Definition loc_125 : location_info := LocationInfo file_1 54 9 54 11.
  Definition loc_126 : location_info := LocationInfo file_1 54 9 54 11.
  Definition loc_127 : location_info := LocationInfo file_1 50 7 50 8.
  Definition loc_128 : location_info := LocationInfo file_1 50 7 50 8.
  Definition loc_129 : location_info := LocationInfo file_1 49 4 49 6.
  Definition loc_130 : location_info := LocationInfo file_1 49 9 49 10.
  Definition loc_131 : location_info := LocationInfo file_1 49 9 49 10.
  Definition loc_132 : location_info := LocationInfo file_1 48 4 48 6.
  Definition loc_133 : location_info := LocationInfo file_1 48 9 48 10.
  Definition loc_134 : location_info := LocationInfo file_1 48 9 48 10.
  Definition loc_137 : location_info := LocationInfo file_1 62 4 62 13.
  Definition loc_138 : location_info := LocationInfo file_1 63 4 63 12.
  Definition loc_139 : location_info := LocationInfo file_1 64 4 70 5.
  Definition loc_140 : location_info := LocationInfo file_1 64 10 67 5.
  Definition loc_141 : location_info := LocationInfo file_1 65 8 65 13.
  Definition loc_142 : location_info := LocationInfo file_1 66 8 66 11.
  Definition loc_143 : location_info := LocationInfo file_1 66 8 66 10.
  Definition loc_144 : location_info := LocationInfo file_1 66 8 66 10.
  Definition loc_145 : location_info := LocationInfo file_1 66 9 66 10.
  Definition loc_146 : location_info := LocationInfo file_1 66 9 66 10.
  Definition loc_147 : location_info := LocationInfo file_1 65 8 65 12.
  Definition loc_148 : location_info := LocationInfo file_1 65 8 65 12.
  Definition loc_149 : location_info := LocationInfo file_1 65 9 65 12.
  Definition loc_150 : location_info := LocationInfo file_1 65 9 65 12.
  Definition loc_151 : location_info := LocationInfo file_1 65 10 65 12.
  Definition loc_152 : location_info := LocationInfo file_1 65 10 65 12.
  Definition loc_153 : location_info := LocationInfo file_1 67 11 70 5.
  Definition loc_154 : location_info := LocationInfo file_1 68 8 68 11.
  Definition loc_155 : location_info := LocationInfo file_1 69 8 69 13.
  Definition loc_156 : location_info := LocationInfo file_1 69 8 69 12.
  Definition loc_157 : location_info := LocationInfo file_1 69 8 69 12.
  Definition loc_158 : location_info := LocationInfo file_1 69 9 69 12.
  Definition loc_159 : location_info := LocationInfo file_1 69 9 69 12.
  Definition loc_160 : location_info := LocationInfo file_1 69 10 69 12.
  Definition loc_161 : location_info := LocationInfo file_1 69 10 69 12.
  Definition loc_162 : location_info := LocationInfo file_1 68 8 68 10.
  Definition loc_163 : location_info := LocationInfo file_1 68 8 68 10.
  Definition loc_164 : location_info := LocationInfo file_1 68 9 68 10.
  Definition loc_165 : location_info := LocationInfo file_1 68 9 68 10.
  Definition loc_166 : location_info := LocationInfo file_1 64 7 64 8.
  Definition loc_167 : location_info := LocationInfo file_1 64 7 64 8.
  Definition loc_168 : location_info := LocationInfo file_1 63 4 63 6.
  Definition loc_169 : location_info := LocationInfo file_1 63 9 63 11.
  Definition loc_170 : location_info := LocationInfo file_1 63 10 63 11.
  Definition loc_173 : location_info := LocationInfo file_1 77 2 77 11.
  Definition loc_174 : location_info := LocationInfo file_1 77 9 77 10.
  Definition loc_175 : location_info := LocationInfo file_1 77 9 77 10.
  Definition loc_178 : location_info := LocationInfo file_1 82 2 82 12.
  Definition loc_179 : location_info := LocationInfo file_1 83 2 83 41.
  Definition loc_180 : location_info := LocationInfo file_1 83 9 83 39.
  Definition loc_181 : location_info := LocationInfo file_1 83 9 83 34.
  Definition loc_182 : location_info := LocationInfo file_1 83 9 83 34.
  Definition loc_183 : location_info := LocationInfo file_1 83 10 83 34.
  Definition loc_184 : location_info := LocationInfo file_1 83 17 83 34.
  Definition loc_185 : location_info := LocationInfo file_1 83 17 83 23.
  Definition loc_186 : location_info := LocationInfo file_1 83 17 83 23.
  Definition loc_187 : location_info := LocationInfo file_1 83 24 83 26.
  Definition loc_188 : location_info := LocationInfo file_1 83 25 83 26.
  Definition loc_189 : location_info := LocationInfo file_1 83 28 83 33.
  Definition loc_190 : location_info := LocationInfo file_1 83 28 83 29.
  Definition loc_191 : location_info := LocationInfo file_1 83 32 83 33.
  Definition loc_192 : location_info := LocationInfo file_1 83 38 83 39.
  Definition loc_193 : location_info := LocationInfo file_1 82 10 82 11.

  (* Definition of struct [__cerbty_unnamed_tag_486]. *)
  Program Definition struct___cerbty_unnamed_tag_486 := {|
    sl_members := [
      (Some "__dummy_max_align_t", void*)
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
        locinfo: loc_11 ;
        Return (LocInfoE loc_12 (use{IntOp i32} (LocInfoE loc_14 (!{PtrOp} (LocInfoE loc_15 ("a"))))))
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
        "local" <-{ IntOp i32 } LocInfoE loc_38 (i2v 1 i32) ;
        "read" <-{ IntOp i32 }
          LocInfoE loc_31 (Call (LocInfoE loc_33 (global_read_int)) [@{expr} LocInfoE loc_34 (&(LocInfoE loc_35 ("local"))) ]) ;
        locinfo: loc_20 ;
        assert{IntOp i32}: (LocInfoE loc_26 ((LocInfoE loc_27 (use{IntOp i32} (LocInfoE loc_28 ("local")))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_29 (use{IntOp i32} (LocInfoE loc_30 ("read")))))) ;
        locinfo: loc_21 ;
        assert{IntOp i32}: (LocInfoE loc_22 ((LocInfoE loc_23 (use{IntOp i32} (LocInfoE loc_24 ("local")))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_25 (i2v 1 i32)))) ;
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
        "old_b" <-{ IntOp i32 }
          LocInfoE loc_57 (use{IntOp i32} (LocInfoE loc_59 (!{PtrOp} (LocInfoE loc_60 ("b"))))) ;
        locinfo: loc_44 ;
        LocInfoE loc_54 (!{PtrOp} (LocInfoE loc_55 ("a"))) <-{ IntOp i32 }
          LocInfoE loc_56 (i2v 1 i32) ;
        locinfo: loc_45 ;
        assert{IntOp i32}: (LocInfoE loc_46 ((LocInfoE loc_47 (use{IntOp i32} (LocInfoE loc_49 (!{PtrOp} (LocInfoE loc_50 ("b")))))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_51 (use{IntOp i32} (LocInfoE loc_52 ("old_b")))))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [local_vars]. *)
  Definition impl_local_vars : function := {|
    f_args := [
      ("b", bool_layout)
    ];
    f_local_vars := [
      ("var", it_layout i32);
      ("dummy", it_layout i32);
      ("p", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "var" <-{ IntOp i32 } LocInfoE loc_96 (i2v 1 i32) ;
        locinfo: loc_67 ;
        LocInfoE loc_93 ("p") <-{ PtrOp }
          LocInfoE loc_94 (&(LocInfoE loc_95 ("var"))) ;
        locinfo: loc_91 ;
        if{BoolOp, None}: LocInfoE loc_91 (use{BoolOp} (LocInfoE loc_92 ("b")))
        then
        locinfo: loc_70 ;
          Goto "#1"
        else
        locinfo: loc_81 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_70 ;
        LocInfoE loc_77 ("dummy") <-{ IntOp i32 }
          LocInfoE loc_78 (use{IntOp i32} (LocInfoE loc_79 ("var"))) ;
        locinfo: loc_71 ;
        LocInfoE loc_72 ("dummy") <-{ IntOp i32 }
          LocInfoE loc_73 (use{IntOp i32} (LocInfoE loc_75 (!{PtrOp} (LocInfoE loc_76 ("p"))))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_81 ;
        LocInfoE loc_86 ("dummy") <-{ IntOp i32 }
          LocInfoE loc_87 (use{IntOp i32} (LocInfoE loc_89 (!{PtrOp} (LocInfoE loc_90 ("p"))))) ;
        locinfo: loc_82 ;
        LocInfoE loc_83 ("dummy") <-{ IntOp i32 }
          LocInfoE loc_84 (use{IntOp i32} (LocInfoE loc_85 ("var"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [ptrs]. *)
  Definition impl_ptrs : function := {|
    f_args := [
      ("b", bool_layout);
      ("p", void*)
    ];
    f_local_vars := [
      ("p1", void*);
      ("p2", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_102 ;
        LocInfoE loc_132 ("p1") <-{ PtrOp }
          LocInfoE loc_133 (use{PtrOp} (LocInfoE loc_134 ("p"))) ;
        locinfo: loc_103 ;
        LocInfoE loc_129 ("p2") <-{ PtrOp }
          LocInfoE loc_130 (use{PtrOp} (LocInfoE loc_131 ("p"))) ;
        locinfo: loc_127 ;
        if{BoolOp, None}: LocInfoE loc_127 (use{BoolOp} (LocInfoE loc_128 ("b")))
        then
        locinfo: loc_106 ;
          Goto "#1"
        else
        locinfo: loc_117 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_106 ;
        expr: (LocInfoE loc_112 (use{IntOp i32} (LocInfoE loc_114 (!{PtrOp} (LocInfoE loc_115 ("p1")))))) ;
        locinfo: loc_107 ;
        expr: (LocInfoE loc_108 (use{IntOp i32} (LocInfoE loc_110 (!{PtrOp} (LocInfoE loc_111 ("p2")))))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_117 ;
        expr: (LocInfoE loc_123 (use{IntOp i32} (LocInfoE loc_125 (!{PtrOp} (LocInfoE loc_126 ("p2")))))) ;
        locinfo: loc_118 ;
        expr: (LocInfoE loc_119 (use{IntOp i32} (LocInfoE loc_121 (!{PtrOp} (LocInfoE loc_122 ("p1")))))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [ptrs2]. *)
  Definition impl_ptrs2 : function := {|
    f_args := [
      ("b", bool_layout);
      ("p", void*)
    ];
    f_local_vars := [
      ("p1", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_138 ;
        LocInfoE loc_168 ("p1") <-{ PtrOp }
          LocInfoE loc_169 (&(LocInfoE loc_170 ("p"))) ;
        locinfo: loc_166 ;
        if{BoolOp, None}: LocInfoE loc_166 (use{BoolOp} (LocInfoE loc_167 ("b")))
        then
        locinfo: loc_141 ;
          Goto "#1"
        else
        locinfo: loc_154 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_141 ;
        expr: (LocInfoE loc_147 (use{IntOp i32} (LocInfoE loc_149 (!{PtrOp} (LocInfoE loc_151 (!{PtrOp} (LocInfoE loc_152 ("p1")))))))) ;
        locinfo: loc_142 ;
        expr: (LocInfoE loc_143 (use{IntOp i32} (LocInfoE loc_145 (!{PtrOp} (LocInfoE loc_146 ("p")))))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_154 ;
        expr: (LocInfoE loc_162 (use{IntOp i32} (LocInfoE loc_164 (!{PtrOp} (LocInfoE loc_165 ("p")))))) ;
        locinfo: loc_155 ;
        expr: (LocInfoE loc_156 (use{IntOp i32} (LocInfoE loc_158 (!{PtrOp} (LocInfoE loc_160 (!{PtrOp} (LocInfoE loc_161 ("p1")))))))) ;
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
        locinfo: loc_173 ;
        Return (LocInfoE loc_174 (use{PtrOp} (LocInfoE loc_175 ("p"))))
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
        "x" <-{ IntOp i32 } LocInfoE loc_193 (i2v 1 i32) ;
        locinfo: loc_179 ;
        assert{IntOp i32}: (LocInfoE loc_180 ((LocInfoE loc_181 (use{IntOp i32} (LocInfoE loc_183 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_184 (LValue (LocInfoE loc_184 (Call (LocInfoE loc_186 (global_ptr_id)) [@{expr} LocInfoE loc_187 (&(LocInfoE loc_188 ("x"))) ;
        LocInfoE loc_189 ((LocInfoE loc_190 (i2v 1 i32)) +{IntOp i32, IntOp i32} (LocInfoE loc_191 (i2v 1 i32))) ])))))))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_192 (i2v 1 i32)))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
