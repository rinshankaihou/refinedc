From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t2_pointers.c]. *)
Section code.
  Definition file_0 : string := "theories/examples/tutorial/t2_pointers.c".
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
  Definition loc_58 : location_info := LocationInfo file_0 39 4 47 5.
  Definition loc_59 : location_info := LocationInfo file_0 39 10 43 5.
  Definition loc_60 : location_info := LocationInfo file_0 40 8 40 20.
  Definition loc_61 : location_info := LocationInfo file_0 41 8 41 19.
  Definition loc_62 : location_info := LocationInfo file_0 42 8 42 14.
  Definition loc_63 : location_info := LocationInfo file_0 42 14 42 9.
  Definition loc_64 : location_info := LocationInfo file_0 42 8 42 13.
  Definition loc_65 : location_info := LocationInfo file_0 42 9 42 13.
  Definition loc_66 : location_info := LocationInfo file_0 42 11 42 12.
  Definition loc_67 : location_info := LocationInfo file_0 42 11 42 12.
  Definition loc_68 : location_info := LocationInfo file_0 41 8 41 13.
  Definition loc_69 : location_info := LocationInfo file_0 41 16 41 18.
  Definition loc_70 : location_info := LocationInfo file_0 41 16 41 18.
  Definition loc_71 : location_info := LocationInfo file_0 41 17 41 18.
  Definition loc_72 : location_info := LocationInfo file_0 41 17 41 18.
  Definition loc_73 : location_info := LocationInfo file_0 40 8 40 13.
  Definition loc_74 : location_info := LocationInfo file_0 40 16 40 19.
  Definition loc_75 : location_info := LocationInfo file_0 40 16 40 19.
  Definition loc_76 : location_info := LocationInfo file_0 43 11 47 5.
  Definition loc_77 : location_info := LocationInfo file_0 44 8 44 19.
  Definition loc_78 : location_info := LocationInfo file_0 45 8 45 14.
  Definition loc_79 : location_info := LocationInfo file_0 45 14 45 9.
  Definition loc_80 : location_info := LocationInfo file_0 46 8 46 20.
  Definition loc_81 : location_info := LocationInfo file_0 46 8 46 13.
  Definition loc_82 : location_info := LocationInfo file_0 46 16 46 19.
  Definition loc_83 : location_info := LocationInfo file_0 46 16 46 19.
  Definition loc_84 : location_info := LocationInfo file_0 45 8 45 13.
  Definition loc_85 : location_info := LocationInfo file_0 45 9 45 13.
  Definition loc_86 : location_info := LocationInfo file_0 45 11 45 12.
  Definition loc_87 : location_info := LocationInfo file_0 45 11 45 12.
  Definition loc_88 : location_info := LocationInfo file_0 44 8 44 13.
  Definition loc_89 : location_info := LocationInfo file_0 44 16 44 18.
  Definition loc_90 : location_info := LocationInfo file_0 44 16 44 18.
  Definition loc_91 : location_info := LocationInfo file_0 44 17 44 18.
  Definition loc_92 : location_info := LocationInfo file_0 44 17 44 18.
  Definition loc_93 : location_info := LocationInfo file_0 39 7 39 8.
  Definition loc_94 : location_info := LocationInfo file_0 39 7 39 8.
  Definition loc_95 : location_info := LocationInfo file_0 38 4 38 5.
  Definition loc_96 : location_info := LocationInfo file_0 38 8 38 12.
  Definition loc_97 : location_info := LocationInfo file_0 38 9 38 12.
  Definition loc_98 : location_info := LocationInfo file_0 36 14 36 15.
  Definition loc_103 : location_info := LocationInfo file_0 54 4 54 11.
  Definition loc_104 : location_info := LocationInfo file_0 55 4 55 11.
  Definition loc_105 : location_info := LocationInfo file_0 56 4 64 5.
  Definition loc_106 : location_info := LocationInfo file_0 56 10 60 5.
  Definition loc_107 : location_info := LocationInfo file_0 57 8 57 12.
  Definition loc_108 : location_info := LocationInfo file_0 58 8 58 15.
  Definition loc_109 : location_info := LocationInfo file_0 58 15 58 9.
  Definition loc_110 : location_info := LocationInfo file_0 59 8 59 12.
  Definition loc_111 : location_info := LocationInfo file_0 59 8 59 11.
  Definition loc_112 : location_info := LocationInfo file_0 59 8 59 11.
  Definition loc_113 : location_info := LocationInfo file_0 59 9 59 11.
  Definition loc_114 : location_info := LocationInfo file_0 59 9 59 11.
  Definition loc_115 : location_info := LocationInfo file_0 58 8 58 14.
  Definition loc_116 : location_info := LocationInfo file_0 58 9 58 14.
  Definition loc_117 : location_info := LocationInfo file_0 58 11 58 13.
  Definition loc_118 : location_info := LocationInfo file_0 58 11 58 13.
  Definition loc_119 : location_info := LocationInfo file_0 57 8 57 11.
  Definition loc_120 : location_info := LocationInfo file_0 57 8 57 11.
  Definition loc_121 : location_info := LocationInfo file_0 57 9 57 11.
  Definition loc_122 : location_info := LocationInfo file_0 57 9 57 11.
  Definition loc_123 : location_info := LocationInfo file_0 60 11 64 5.
  Definition loc_124 : location_info := LocationInfo file_0 61 8 61 12.
  Definition loc_125 : location_info := LocationInfo file_0 62 8 62 15.
  Definition loc_126 : location_info := LocationInfo file_0 62 15 62 9.
  Definition loc_127 : location_info := LocationInfo file_0 63 8 63 12.
  Definition loc_128 : location_info := LocationInfo file_0 63 8 63 11.
  Definition loc_129 : location_info := LocationInfo file_0 63 8 63 11.
  Definition loc_130 : location_info := LocationInfo file_0 63 9 63 11.
  Definition loc_131 : location_info := LocationInfo file_0 63 9 63 11.
  Definition loc_132 : location_info := LocationInfo file_0 62 8 62 14.
  Definition loc_133 : location_info := LocationInfo file_0 62 9 62 14.
  Definition loc_134 : location_info := LocationInfo file_0 62 11 62 13.
  Definition loc_135 : location_info := LocationInfo file_0 62 11 62 13.
  Definition loc_136 : location_info := LocationInfo file_0 61 8 61 11.
  Definition loc_137 : location_info := LocationInfo file_0 61 8 61 11.
  Definition loc_138 : location_info := LocationInfo file_0 61 9 61 11.
  Definition loc_139 : location_info := LocationInfo file_0 61 9 61 11.
  Definition loc_140 : location_info := LocationInfo file_0 56 7 56 8.
  Definition loc_141 : location_info := LocationInfo file_0 56 7 56 8.
  Definition loc_142 : location_info := LocationInfo file_0 55 4 55 6.
  Definition loc_143 : location_info := LocationInfo file_0 55 9 55 10.
  Definition loc_144 : location_info := LocationInfo file_0 55 9 55 10.
  Definition loc_145 : location_info := LocationInfo file_0 54 4 54 6.
  Definition loc_146 : location_info := LocationInfo file_0 54 9 54 10.
  Definition loc_147 : location_info := LocationInfo file_0 54 9 54 10.
  Definition loc_150 : location_info := LocationInfo file_0 71 4 71 12.
  Definition loc_151 : location_info := LocationInfo file_0 72 4 80 5.
  Definition loc_152 : location_info := LocationInfo file_0 72 10 76 5.
  Definition loc_153 : location_info := LocationInfo file_0 73 8 73 13.
  Definition loc_154 : location_info := LocationInfo file_0 74 8 74 15.
  Definition loc_155 : location_info := LocationInfo file_0 74 15 74 9.
  Definition loc_156 : location_info := LocationInfo file_0 75 8 75 11.
  Definition loc_157 : location_info := LocationInfo file_0 75 8 75 10.
  Definition loc_158 : location_info := LocationInfo file_0 75 8 75 10.
  Definition loc_159 : location_info := LocationInfo file_0 75 9 75 10.
  Definition loc_160 : location_info := LocationInfo file_0 75 9 75 10.
  Definition loc_161 : location_info := LocationInfo file_0 74 8 74 14.
  Definition loc_162 : location_info := LocationInfo file_0 74 9 74 14.
  Definition loc_163 : location_info := LocationInfo file_0 74 11 74 13.
  Definition loc_164 : location_info := LocationInfo file_0 74 11 74 13.
  Definition loc_165 : location_info := LocationInfo file_0 73 8 73 12.
  Definition loc_166 : location_info := LocationInfo file_0 73 8 73 12.
  Definition loc_167 : location_info := LocationInfo file_0 73 9 73 12.
  Definition loc_168 : location_info := LocationInfo file_0 73 9 73 12.
  Definition loc_169 : location_info := LocationInfo file_0 73 10 73 12.
  Definition loc_170 : location_info := LocationInfo file_0 73 10 73 12.
  Definition loc_171 : location_info := LocationInfo file_0 76 11 80 5.
  Definition loc_172 : location_info := LocationInfo file_0 77 8 77 11.
  Definition loc_173 : location_info := LocationInfo file_0 78 8 78 13.
  Definition loc_174 : location_info := LocationInfo file_0 79 8 79 15.
  Definition loc_175 : location_info := LocationInfo file_0 79 15 79 9.
  Definition loc_176 : location_info := LocationInfo file_0 79 8 79 14.
  Definition loc_177 : location_info := LocationInfo file_0 79 9 79 14.
  Definition loc_178 : location_info := LocationInfo file_0 79 11 79 13.
  Definition loc_179 : location_info := LocationInfo file_0 79 11 79 13.
  Definition loc_180 : location_info := LocationInfo file_0 78 8 78 12.
  Definition loc_181 : location_info := LocationInfo file_0 78 8 78 12.
  Definition loc_182 : location_info := LocationInfo file_0 78 9 78 12.
  Definition loc_183 : location_info := LocationInfo file_0 78 9 78 12.
  Definition loc_184 : location_info := LocationInfo file_0 78 10 78 12.
  Definition loc_185 : location_info := LocationInfo file_0 78 10 78 12.
  Definition loc_186 : location_info := LocationInfo file_0 77 8 77 10.
  Definition loc_187 : location_info := LocationInfo file_0 77 8 77 10.
  Definition loc_188 : location_info := LocationInfo file_0 77 9 77 10.
  Definition loc_189 : location_info := LocationInfo file_0 77 9 77 10.
  Definition loc_190 : location_info := LocationInfo file_0 72 7 72 8.
  Definition loc_191 : location_info := LocationInfo file_0 72 7 72 8.
  Definition loc_192 : location_info := LocationInfo file_0 71 4 71 6.
  Definition loc_193 : location_info := LocationInfo file_0 71 9 71 11.
  Definition loc_194 : location_info := LocationInfo file_0 71 10 71 11.

  (* Definition of function [read_int]. *)
  Definition impl_read_int : function := {|
    f_args := [
      ("a", LPtr)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        Return (LocInfoE loc_3 (use{it_layout i32} (LocInfoE loc_5 (!{LPtr} (LocInfoE loc_6 ("a"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [use_read_int]. *)
  Definition impl_use_read_int (read_int : loc): function := {|
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
        locinfo: loc_22 ;
        "$0" <- LocInfoE loc_24 (read_int) with
          [ LocInfoE loc_25 (&(LocInfoE loc_26 ("local"))) ] ;
        "read" <-{ it_layout i32 } LocInfoE loc_22 ("$0") ;
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
      ("a", LPtr);
      ("b", LPtr)
    ];
    f_local_vars := [
      ("old_b", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "old_b" <-{ it_layout i32 }
          LocInfoE loc_48 (use{it_layout i32} (LocInfoE loc_50 (!{LPtr} (LocInfoE loc_51 ("b"))))) ;
        locinfo: loc_35 ;
        LocInfoE loc_45 (!{LPtr} (LocInfoE loc_46 ("a"))) <-{ it_layout i32 }
          LocInfoE loc_47 (i2v 1 i32) ;
        locinfo: loc_36 ;
        assert: (LocInfoE loc_37 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_37 ((LocInfoE loc_38 (use{it_layout i32} (LocInfoE loc_40 (!{LPtr} (LocInfoE loc_41 ("b")))))) ={IntOp i32, IntOp i32} (LocInfoE loc_42 (use{it_layout i32} (LocInfoE loc_43 ("old_b")))))))) ;
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
      ("p", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "var" <-{ it_layout i32 } LocInfoE loc_98 (i2v 1 i32) ;
        locinfo: loc_57 ;
        LocInfoE loc_95 ("p") <-{ LPtr }
          LocInfoE loc_96 (&(LocInfoE loc_97 ("var"))) ;
        locinfo: loc_93 ;
        if: LocInfoE loc_93 (use{it_layout bool_it} (LocInfoE loc_94 ("b")))
        then
        locinfo: loc_60 ;
          Goto "#1"
        else
        locinfo: loc_77 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_60 ;
        LocInfoE loc_73 ("dummy") <-{ it_layout i32 }
          LocInfoE loc_74 (use{it_layout i32} (LocInfoE loc_75 ("var"))) ;
        locinfo: loc_61 ;
        LocInfoE loc_68 ("dummy") <-{ it_layout i32 }
          LocInfoE loc_69 (use{it_layout i32} (LocInfoE loc_71 (!{LPtr} (LocInfoE loc_72 ("p"))))) ;
        locinfo: loc_62 ;
        expr: (LocInfoE loc_64 (&(LocInfoE loc_66 (!{LPtr} (LocInfoE loc_67 ("p")))))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_77 ;
        LocInfoE loc_88 ("dummy") <-{ it_layout i32 }
          LocInfoE loc_89 (use{it_layout i32} (LocInfoE loc_91 (!{LPtr} (LocInfoE loc_92 ("p"))))) ;
        locinfo: loc_78 ;
        expr: (LocInfoE loc_84 (&(LocInfoE loc_86 (!{LPtr} (LocInfoE loc_87 ("p")))))) ;
        locinfo: loc_80 ;
        LocInfoE loc_81 ("dummy") <-{ it_layout i32 }
          LocInfoE loc_82 (use{it_layout i32} (LocInfoE loc_83 ("var"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [ptrs]. *)
  Definition impl_ptrs : function := {|
    f_args := [
      ("b", it_layout bool_it);
      ("p", LPtr)
    ];
    f_local_vars := [
      ("p1", LPtr);
      ("p2", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_103 ;
        LocInfoE loc_145 ("p1") <-{ LPtr }
          LocInfoE loc_146 (use{LPtr} (LocInfoE loc_147 ("p"))) ;
        locinfo: loc_104 ;
        LocInfoE loc_142 ("p2") <-{ LPtr }
          LocInfoE loc_143 (use{LPtr} (LocInfoE loc_144 ("p"))) ;
        locinfo: loc_140 ;
        if: LocInfoE loc_140 (use{it_layout bool_it} (LocInfoE loc_141 ("b")))
        then
        locinfo: loc_107 ;
          Goto "#1"
        else
        locinfo: loc_124 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_107 ;
        expr: (LocInfoE loc_119 (use{it_layout i32} (LocInfoE loc_121 (!{LPtr} (LocInfoE loc_122 ("p1")))))) ;
        locinfo: loc_108 ;
        expr: (LocInfoE loc_115 (&(LocInfoE loc_117 (!{LPtr} (LocInfoE loc_118 ("p1")))))) ;
        locinfo: loc_110 ;
        expr: (LocInfoE loc_111 (use{it_layout i32} (LocInfoE loc_113 (!{LPtr} (LocInfoE loc_114 ("p2")))))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_124 ;
        expr: (LocInfoE loc_136 (use{it_layout i32} (LocInfoE loc_138 (!{LPtr} (LocInfoE loc_139 ("p2")))))) ;
        locinfo: loc_125 ;
        expr: (LocInfoE loc_132 (&(LocInfoE loc_134 (!{LPtr} (LocInfoE loc_135 ("p2")))))) ;
        locinfo: loc_127 ;
        expr: (LocInfoE loc_128 (use{it_layout i32} (LocInfoE loc_130 (!{LPtr} (LocInfoE loc_131 ("p1")))))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [ptrs2]. *)
  Definition impl_ptrs2 : function := {|
    f_args := [
      ("b", it_layout bool_it);
      ("p", LPtr)
    ];
    f_local_vars := [
      ("p1", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_150 ;
        LocInfoE loc_192 ("p1") <-{ LPtr }
          LocInfoE loc_193 (&(LocInfoE loc_194 ("p"))) ;
        locinfo: loc_190 ;
        if: LocInfoE loc_190 (use{it_layout bool_it} (LocInfoE loc_191 ("b")))
        then
        locinfo: loc_153 ;
          Goto "#1"
        else
        locinfo: loc_172 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_153 ;
        expr: (LocInfoE loc_165 (use{it_layout i32} (LocInfoE loc_167 (!{LPtr} (LocInfoE loc_169 (!{LPtr} (LocInfoE loc_170 ("p1")))))))) ;
        locinfo: loc_154 ;
        expr: (LocInfoE loc_161 (&(LocInfoE loc_163 (!{LPtr} (LocInfoE loc_164 ("p1")))))) ;
        locinfo: loc_156 ;
        expr: (LocInfoE loc_157 (use{it_layout i32} (LocInfoE loc_159 (!{LPtr} (LocInfoE loc_160 ("p")))))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_172 ;
        expr: (LocInfoE loc_186 (use{it_layout i32} (LocInfoE loc_188 (!{LPtr} (LocInfoE loc_189 ("p")))))) ;
        locinfo: loc_173 ;
        expr: (LocInfoE loc_180 (use{it_layout i32} (LocInfoE loc_182 (!{LPtr} (LocInfoE loc_184 (!{LPtr} (LocInfoE loc_185 ("p1")))))))) ;
        locinfo: loc_174 ;
        expr: (LocInfoE loc_176 (&(LocInfoE loc_178 (!{LPtr} (LocInfoE loc_179 ("p1")))))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
