From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/t02_pointers.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "tutorial/t02_pointers.c".
  Definition loc_2 : location_info := LocationInfo file_0 50 2 50 47.
  Definition loc_3 : location_info := LocationInfo file_0 50 9 50 46.
  Definition loc_4 : location_info := LocationInfo file_0 50 9 50 32.
  Definition loc_5 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_6 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_7 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_8 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_11 : location_info := LocationInfo file_1 14 4 14 14.
  Definition loc_12 : location_info := LocationInfo file_1 14 11 14 13.
  Definition loc_13 : location_info := LocationInfo file_1 14 11 14 13.
  Definition loc_14 : location_info := LocationInfo file_1 14 12 14 13.
  Definition loc_15 : location_info := LocationInfo file_1 14 12 14 13.
  Definition loc_18 : location_info := LocationInfo file_1 19 4 19 18.
  Definition loc_19 : location_info := LocationInfo file_1 20 4 20 32.
  Definition loc_20 : location_info := LocationInfo file_1 21 4 21 26.
  Definition loc_21 : location_info := LocationInfo file_1 22 4 22 23.
  Definition loc_22 : location_info := LocationInfo file_1 22 11 22 21.
  Definition loc_23 : location_info := LocationInfo file_1 22 11 22 16.
  Definition loc_24 : location_info := LocationInfo file_1 22 11 22 16.
  Definition loc_25 : location_info := LocationInfo file_1 22 20 22 21.
  Definition loc_26 : location_info := LocationInfo file_1 21 11 21 24.
  Definition loc_27 : location_info := LocationInfo file_1 21 11 21 16.
  Definition loc_28 : location_info := LocationInfo file_1 21 11 21 16.
  Definition loc_29 : location_info := LocationInfo file_1 21 20 21 24.
  Definition loc_30 : location_info := LocationInfo file_1 21 20 21 24.
  Definition loc_31 : location_info := LocationInfo file_1 20 15 20 31.
  Definition loc_32 : location_info := LocationInfo file_1 20 15 20 23.
  Definition loc_33 : location_info := LocationInfo file_1 20 15 20 23.
  Definition loc_34 : location_info := LocationInfo file_1 20 24 20 30.
  Definition loc_35 : location_info := LocationInfo file_1 20 25 20 30.
  Definition loc_38 : location_info := LocationInfo file_1 19 16 19 17.
  Definition loc_43 : location_info := LocationInfo file_1 29 4 29 19.
  Definition loc_44 : location_info := LocationInfo file_1 30 4 30 11.
  Definition loc_45 : location_info := LocationInfo file_1 31 4 31 24.
  Definition loc_46 : location_info := LocationInfo file_1 31 11 31 22.
  Definition loc_47 : location_info := LocationInfo file_1 31 11 31 13.
  Definition loc_48 : location_info := LocationInfo file_1 31 11 31 13.
  Definition loc_49 : location_info := LocationInfo file_1 31 12 31 13.
  Definition loc_50 : location_info := LocationInfo file_1 31 12 31 13.
  Definition loc_51 : location_info := LocationInfo file_1 31 17 31 22.
  Definition loc_52 : location_info := LocationInfo file_1 31 17 31 22.
  Definition loc_53 : location_info := LocationInfo file_1 30 4 30 6.
  Definition loc_54 : location_info := LocationInfo file_1 30 5 30 6.
  Definition loc_55 : location_info := LocationInfo file_1 30 5 30 6.
  Definition loc_56 : location_info := LocationInfo file_1 30 9 30 10.
  Definition loc_57 : location_info := LocationInfo file_1 29 16 29 18.
  Definition loc_58 : location_info := LocationInfo file_1 29 16 29 18.
  Definition loc_59 : location_info := LocationInfo file_1 29 17 29 18.
  Definition loc_60 : location_info := LocationInfo file_1 29 17 29 18.
  Definition loc_65 : location_info := LocationInfo file_1 36 4 36 23.
  Definition loc_66 : location_info := LocationInfo file_1 38 4 38 13.
  Definition loc_67 : location_info := LocationInfo file_1 39 4 45 5.
  Definition loc_68 : location_info := LocationInfo file_1 39 10 42 5.
  Definition loc_69 : location_info := LocationInfo file_1 40 8 40 20.
  Definition loc_70 : location_info := LocationInfo file_1 41 8 41 19.
  Definition loc_71 : location_info := LocationInfo file_1 41 8 41 13.
  Definition loc_72 : location_info := LocationInfo file_1 41 16 41 18.
  Definition loc_73 : location_info := LocationInfo file_1 41 16 41 18.
  Definition loc_74 : location_info := LocationInfo file_1 41 17 41 18.
  Definition loc_75 : location_info := LocationInfo file_1 41 17 41 18.
  Definition loc_76 : location_info := LocationInfo file_1 40 8 40 13.
  Definition loc_77 : location_info := LocationInfo file_1 40 16 40 19.
  Definition loc_78 : location_info := LocationInfo file_1 40 16 40 19.
  Definition loc_79 : location_info := LocationInfo file_1 42 11 45 5.
  Definition loc_80 : location_info := LocationInfo file_1 43 8 43 19.
  Definition loc_81 : location_info := LocationInfo file_1 44 8 44 20.
  Definition loc_82 : location_info := LocationInfo file_1 44 8 44 13.
  Definition loc_83 : location_info := LocationInfo file_1 44 16 44 19.
  Definition loc_84 : location_info := LocationInfo file_1 44 16 44 19.
  Definition loc_85 : location_info := LocationInfo file_1 43 8 43 13.
  Definition loc_86 : location_info := LocationInfo file_1 43 16 43 18.
  Definition loc_87 : location_info := LocationInfo file_1 43 16 43 18.
  Definition loc_88 : location_info := LocationInfo file_1 43 17 43 18.
  Definition loc_89 : location_info := LocationInfo file_1 43 17 43 18.
  Definition loc_90 : location_info := LocationInfo file_1 39 7 39 8.
  Definition loc_91 : location_info := LocationInfo file_1 39 7 39 8.
  Definition loc_92 : location_info := LocationInfo file_1 38 4 38 5.
  Definition loc_93 : location_info := LocationInfo file_1 38 8 38 12.
  Definition loc_94 : location_info := LocationInfo file_1 38 9 38 12.
  Definition loc_95 : location_info := LocationInfo file_1 36 14 36 15.
  Definition loc_100 : location_info := LocationInfo file_1 52 4 52 11.
  Definition loc_101 : location_info := LocationInfo file_1 53 4 53 11.
  Definition loc_102 : location_info := LocationInfo file_1 54 4 60 5.
  Definition loc_103 : location_info := LocationInfo file_1 54 10 57 5.
  Definition loc_104 : location_info := LocationInfo file_1 55 8 55 12.
  Definition loc_105 : location_info := LocationInfo file_1 56 8 56 12.
  Definition loc_106 : location_info := LocationInfo file_1 56 8 56 11.
  Definition loc_107 : location_info := LocationInfo file_1 56 8 56 11.
  Definition loc_108 : location_info := LocationInfo file_1 56 9 56 11.
  Definition loc_109 : location_info := LocationInfo file_1 56 9 56 11.
  Definition loc_110 : location_info := LocationInfo file_1 55 8 55 11.
  Definition loc_111 : location_info := LocationInfo file_1 55 8 55 11.
  Definition loc_112 : location_info := LocationInfo file_1 55 9 55 11.
  Definition loc_113 : location_info := LocationInfo file_1 55 9 55 11.
  Definition loc_114 : location_info := LocationInfo file_1 57 11 60 5.
  Definition loc_115 : location_info := LocationInfo file_1 58 8 58 12.
  Definition loc_116 : location_info := LocationInfo file_1 59 8 59 12.
  Definition loc_117 : location_info := LocationInfo file_1 59 8 59 11.
  Definition loc_118 : location_info := LocationInfo file_1 59 8 59 11.
  Definition loc_119 : location_info := LocationInfo file_1 59 9 59 11.
  Definition loc_120 : location_info := LocationInfo file_1 59 9 59 11.
  Definition loc_121 : location_info := LocationInfo file_1 58 8 58 11.
  Definition loc_122 : location_info := LocationInfo file_1 58 8 58 11.
  Definition loc_123 : location_info := LocationInfo file_1 58 9 58 11.
  Definition loc_124 : location_info := LocationInfo file_1 58 9 58 11.
  Definition loc_125 : location_info := LocationInfo file_1 54 7 54 8.
  Definition loc_126 : location_info := LocationInfo file_1 54 7 54 8.
  Definition loc_127 : location_info := LocationInfo file_1 53 4 53 6.
  Definition loc_128 : location_info := LocationInfo file_1 53 9 53 10.
  Definition loc_129 : location_info := LocationInfo file_1 53 9 53 10.
  Definition loc_130 : location_info := LocationInfo file_1 52 4 52 6.
  Definition loc_131 : location_info := LocationInfo file_1 52 9 52 10.
  Definition loc_132 : location_info := LocationInfo file_1 52 9 52 10.
  Definition loc_135 : location_info := LocationInfo file_1 67 4 67 12.
  Definition loc_136 : location_info := LocationInfo file_1 68 4 74 5.
  Definition loc_137 : location_info := LocationInfo file_1 68 10 71 5.
  Definition loc_138 : location_info := LocationInfo file_1 69 8 69 13.
  Definition loc_139 : location_info := LocationInfo file_1 70 8 70 11.
  Definition loc_140 : location_info := LocationInfo file_1 70 8 70 10.
  Definition loc_141 : location_info := LocationInfo file_1 70 8 70 10.
  Definition loc_142 : location_info := LocationInfo file_1 70 9 70 10.
  Definition loc_143 : location_info := LocationInfo file_1 70 9 70 10.
  Definition loc_144 : location_info := LocationInfo file_1 69 8 69 12.
  Definition loc_145 : location_info := LocationInfo file_1 69 8 69 12.
  Definition loc_146 : location_info := LocationInfo file_1 69 9 69 12.
  Definition loc_147 : location_info := LocationInfo file_1 69 9 69 12.
  Definition loc_148 : location_info := LocationInfo file_1 69 10 69 12.
  Definition loc_149 : location_info := LocationInfo file_1 69 10 69 12.
  Definition loc_150 : location_info := LocationInfo file_1 71 11 74 5.
  Definition loc_151 : location_info := LocationInfo file_1 72 8 72 11.
  Definition loc_152 : location_info := LocationInfo file_1 73 8 73 13.
  Definition loc_153 : location_info := LocationInfo file_1 73 8 73 12.
  Definition loc_154 : location_info := LocationInfo file_1 73 8 73 12.
  Definition loc_155 : location_info := LocationInfo file_1 73 9 73 12.
  Definition loc_156 : location_info := LocationInfo file_1 73 9 73 12.
  Definition loc_157 : location_info := LocationInfo file_1 73 10 73 12.
  Definition loc_158 : location_info := LocationInfo file_1 73 10 73 12.
  Definition loc_159 : location_info := LocationInfo file_1 72 8 72 10.
  Definition loc_160 : location_info := LocationInfo file_1 72 8 72 10.
  Definition loc_161 : location_info := LocationInfo file_1 72 9 72 10.
  Definition loc_162 : location_info := LocationInfo file_1 72 9 72 10.
  Definition loc_163 : location_info := LocationInfo file_1 68 7 68 8.
  Definition loc_164 : location_info := LocationInfo file_1 68 7 68 8.
  Definition loc_165 : location_info := LocationInfo file_1 67 4 67 6.
  Definition loc_166 : location_info := LocationInfo file_1 67 9 67 11.
  Definition loc_167 : location_info := LocationInfo file_1 67 10 67 11.
  Definition loc_170 : location_info := LocationInfo file_1 81 2 81 11.
  Definition loc_171 : location_info := LocationInfo file_1 81 9 81 10.
  Definition loc_172 : location_info := LocationInfo file_1 81 9 81 10.
  Definition loc_175 : location_info := LocationInfo file_1 86 2 86 12.
  Definition loc_176 : location_info := LocationInfo file_1 87 2 87 41.
  Definition loc_177 : location_info := LocationInfo file_1 87 9 87 39.
  Definition loc_178 : location_info := LocationInfo file_1 87 9 87 34.
  Definition loc_179 : location_info := LocationInfo file_1 87 9 87 34.
  Definition loc_180 : location_info := LocationInfo file_1 87 10 87 34.
  Definition loc_181 : location_info := LocationInfo file_1 87 17 87 34.
  Definition loc_182 : location_info := LocationInfo file_1 87 17 87 23.
  Definition loc_183 : location_info := LocationInfo file_1 87 17 87 23.
  Definition loc_184 : location_info := LocationInfo file_1 87 24 87 26.
  Definition loc_185 : location_info := LocationInfo file_1 87 25 87 26.
  Definition loc_186 : location_info := LocationInfo file_1 87 28 87 33.
  Definition loc_187 : location_info := LocationInfo file_1 87 28 87 29.
  Definition loc_188 : location_info := LocationInfo file_1 87 32 87 33.
  Definition loc_189 : location_info := LocationInfo file_1 87 38 87 39.
  Definition loc_190 : location_info := LocationInfo file_1 86 10 86 11.

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
        assert: (LocInfoE loc_26 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_26 ((LocInfoE loc_27 (use{IntOp i32} (LocInfoE loc_28 ("local")))) ={IntOp i32, IntOp i32} (LocInfoE loc_29 (use{IntOp i32} (LocInfoE loc_30 ("read")))))))) ;
        locinfo: loc_21 ;
        assert: (LocInfoE loc_22 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_22 ((LocInfoE loc_23 (use{IntOp i32} (LocInfoE loc_24 ("local")))) ={IntOp i32, IntOp i32} (LocInfoE loc_25 (i2v 1 i32)))))) ;
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
        assert: (LocInfoE loc_46 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_46 ((LocInfoE loc_47 (use{IntOp i32} (LocInfoE loc_49 (!{PtrOp} (LocInfoE loc_50 ("b")))))) ={IntOp i32, IntOp i32} (LocInfoE loc_51 (use{IntOp i32} (LocInfoE loc_52 ("old_b")))))))) ;
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
        "var" <-{ IntOp i32 } LocInfoE loc_95 (i2v 1 i32) ;
        locinfo: loc_66 ;
        LocInfoE loc_92 ("p") <-{ PtrOp }
          LocInfoE loc_93 (&(LocInfoE loc_94 ("var"))) ;
        locinfo: loc_90 ;
        if: LocInfoE loc_90 (use{IntOp bool_it} (LocInfoE loc_91 ("b")))
        then
        locinfo: loc_69 ;
          Goto "#1"
        else
        locinfo: loc_80 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_69 ;
        LocInfoE loc_76 ("dummy") <-{ IntOp i32 }
          LocInfoE loc_77 (use{IntOp i32} (LocInfoE loc_78 ("var"))) ;
        locinfo: loc_70 ;
        LocInfoE loc_71 ("dummy") <-{ IntOp i32 }
          LocInfoE loc_72 (use{IntOp i32} (LocInfoE loc_74 (!{PtrOp} (LocInfoE loc_75 ("p"))))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_80 ;
        LocInfoE loc_85 ("dummy") <-{ IntOp i32 }
          LocInfoE loc_86 (use{IntOp i32} (LocInfoE loc_88 (!{PtrOp} (LocInfoE loc_89 ("p"))))) ;
        locinfo: loc_81 ;
        LocInfoE loc_82 ("dummy") <-{ IntOp i32 }
          LocInfoE loc_83 (use{IntOp i32} (LocInfoE loc_84 ("var"))) ;
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
        locinfo: loc_100 ;
        LocInfoE loc_130 ("p1") <-{ PtrOp }
          LocInfoE loc_131 (use{PtrOp} (LocInfoE loc_132 ("p"))) ;
        locinfo: loc_101 ;
        LocInfoE loc_127 ("p2") <-{ PtrOp }
          LocInfoE loc_128 (use{PtrOp} (LocInfoE loc_129 ("p"))) ;
        locinfo: loc_125 ;
        if: LocInfoE loc_125 (use{IntOp bool_it} (LocInfoE loc_126 ("b")))
        then
        locinfo: loc_104 ;
          Goto "#1"
        else
        locinfo: loc_115 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_104 ;
        expr: (LocInfoE loc_110 (use{IntOp i32} (LocInfoE loc_112 (!{PtrOp} (LocInfoE loc_113 ("p1")))))) ;
        locinfo: loc_105 ;
        expr: (LocInfoE loc_106 (use{IntOp i32} (LocInfoE loc_108 (!{PtrOp} (LocInfoE loc_109 ("p2")))))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_115 ;
        expr: (LocInfoE loc_121 (use{IntOp i32} (LocInfoE loc_123 (!{PtrOp} (LocInfoE loc_124 ("p2")))))) ;
        locinfo: loc_116 ;
        expr: (LocInfoE loc_117 (use{IntOp i32} (LocInfoE loc_119 (!{PtrOp} (LocInfoE loc_120 ("p1")))))) ;
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
        locinfo: loc_135 ;
        LocInfoE loc_165 ("p1") <-{ PtrOp }
          LocInfoE loc_166 (&(LocInfoE loc_167 ("p"))) ;
        locinfo: loc_163 ;
        if: LocInfoE loc_163 (use{IntOp bool_it} (LocInfoE loc_164 ("b")))
        then
        locinfo: loc_138 ;
          Goto "#1"
        else
        locinfo: loc_151 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_138 ;
        expr: (LocInfoE loc_144 (use{IntOp i32} (LocInfoE loc_146 (!{PtrOp} (LocInfoE loc_148 (!{PtrOp} (LocInfoE loc_149 ("p1")))))))) ;
        locinfo: loc_139 ;
        expr: (LocInfoE loc_140 (use{IntOp i32} (LocInfoE loc_142 (!{PtrOp} (LocInfoE loc_143 ("p")))))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_151 ;
        expr: (LocInfoE loc_159 (use{IntOp i32} (LocInfoE loc_161 (!{PtrOp} (LocInfoE loc_162 ("p")))))) ;
        locinfo: loc_152 ;
        expr: (LocInfoE loc_153 (use{IntOp i32} (LocInfoE loc_155 (!{PtrOp} (LocInfoE loc_157 (!{PtrOp} (LocInfoE loc_158 ("p1")))))))) ;
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
        locinfo: loc_170 ;
        Return (LocInfoE loc_171 (use{PtrOp} (LocInfoE loc_172 ("p"))))
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
        "x" <-{ IntOp i32 } LocInfoE loc_190 (i2v 1 i32) ;
        locinfo: loc_176 ;
        assert: (LocInfoE loc_177 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_177 ((LocInfoE loc_178 (use{IntOp i32} (LocInfoE loc_180 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_181 (LValue (LocInfoE loc_181 (Call (LocInfoE loc_183 (global_ptr_id)) [@{expr} LocInfoE loc_184 (&(LocInfoE loc_185 ("x"))) ;
        LocInfoE loc_186 ((LocInfoE loc_187 (i2v 1 i32)) +{IntOp i32, IntOp i32} (LocInfoE loc_188 (i2v 1 i32))) ])))))))) ={IntOp i32, IntOp i32} (LocInfoE loc_189 (i2v 1 i32)))))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
