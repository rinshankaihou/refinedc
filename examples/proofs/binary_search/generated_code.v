From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/binary_search.c]. *)
Section code.
  Definition file_0 : string := "examples/binary_search.c".
  Definition loc_2 : location_info := LocationInfo file_0 24 2 24 19.
  Definition loc_3 : location_info := LocationInfo file_0 30 2 37 3.
  Definition loc_4 : location_info := LocationInfo file_0 38 2 38 11.
  Definition loc_5 : location_info := LocationInfo file_0 38 9 38 10.
  Definition loc_6 : location_info := LocationInfo file_0 38 9 38 10.
  Definition loc_7 : location_info := LocationInfo file_0 30 2 37 3.
  Definition loc_8 : location_info := LocationInfo file_0 30 15 37 3.
  Definition loc_9 : location_info := LocationInfo file_0 31 4 31 28.
  Definition loc_10 : location_info := LocationInfo file_0 32 4 36 5.
  Definition loc_11 : location_info := LocationInfo file_0 30 2 37 3.
  Definition loc_12 : location_info := LocationInfo file_0 30 2 37 3.
  Definition loc_13 : location_info := LocationInfo file_0 32 24 34 7.
  Definition loc_14 : location_info := LocationInfo file_0 33 6 33 16.
  Definition loc_15 : location_info := LocationInfo file_0 33 6 33 7.
  Definition loc_16 : location_info := LocationInfo file_0 33 10 33 15.
  Definition loc_17 : location_info := LocationInfo file_0 33 10 33 11.
  Definition loc_18 : location_info := LocationInfo file_0 33 10 33 11.
  Definition loc_19 : location_info := LocationInfo file_0 33 14 33 15.
  Definition loc_20 : location_info := LocationInfo file_0 34 13 36 5.
  Definition loc_21 : location_info := LocationInfo file_0 35 6 35 12.
  Definition loc_22 : location_info := LocationInfo file_0 35 6 35 7.
  Definition loc_23 : location_info := LocationInfo file_0 35 10 35 11.
  Definition loc_24 : location_info := LocationInfo file_0 35 10 35 11.
  Definition loc_25 : location_info := LocationInfo file_0 32 8 32 22.
  Definition loc_26 : location_info := LocationInfo file_0 32 8 32 12.
  Definition loc_27 : location_info := LocationInfo file_0 32 8 32 12.
  Definition loc_28 : location_info := LocationInfo file_0 32 8 32 12.
  Definition loc_29 : location_info := LocationInfo file_0 32 13 32 18.
  Definition loc_30 : location_info := LocationInfo file_0 32 13 32 18.
  Definition loc_31 : location_info := LocationInfo file_0 32 13 32 18.
  Definition loc_32 : location_info := LocationInfo file_0 32 13 32 15.
  Definition loc_33 : location_info := LocationInfo file_0 32 13 32 15.
  Definition loc_34 : location_info := LocationInfo file_0 32 16 32 17.
  Definition loc_35 : location_info := LocationInfo file_0 32 16 32 17.
  Definition loc_36 : location_info := LocationInfo file_0 32 20 32 21.
  Definition loc_37 : location_info := LocationInfo file_0 32 20 32 21.
  Definition loc_38 : location_info := LocationInfo file_0 31 12 31 27.
  Definition loc_39 : location_info := LocationInfo file_0 31 12 31 13.
  Definition loc_40 : location_info := LocationInfo file_0 31 12 31 13.
  Definition loc_41 : location_info := LocationInfo file_0 31 16 31 27.
  Definition loc_42 : location_info := LocationInfo file_0 31 16 31 23.
  Definition loc_43 : location_info := LocationInfo file_0 31 17 31 18.
  Definition loc_44 : location_info := LocationInfo file_0 31 17 31 18.
  Definition loc_45 : location_info := LocationInfo file_0 31 21 31 22.
  Definition loc_46 : location_info := LocationInfo file_0 31 21 31 22.
  Definition loc_47 : location_info := LocationInfo file_0 31 26 31 27.
  Definition loc_50 : location_info := LocationInfo file_0 30 8 30 13.
  Definition loc_51 : location_info := LocationInfo file_0 30 8 30 9.
  Definition loc_52 : location_info := LocationInfo file_0 30 8 30 9.
  Definition loc_53 : location_info := LocationInfo file_0 30 12 30 13.
  Definition loc_54 : location_info := LocationInfo file_0 30 12 30 13.
  Definition loc_55 : location_info := LocationInfo file_0 24 17 24 18.
  Definition loc_56 : location_info := LocationInfo file_0 24 17 24 18.
  Definition loc_59 : location_info := LocationInfo file_0 24 10 24 11.
  Definition loc_64 : location_info := LocationInfo file_0 47 2 47 26.
  Definition loc_65 : location_info := LocationInfo file_0 48 2 48 20.
  Definition loc_66 : location_info := LocationInfo file_0 48 9 48 19.
  Definition loc_67 : location_info := LocationInfo file_0 48 9 48 12.
  Definition loc_68 : location_info := LocationInfo file_0 48 9 48 12.
  Definition loc_69 : location_info := LocationInfo file_0 48 10 48 12.
  Definition loc_70 : location_info := LocationInfo file_0 48 10 48 12.
  Definition loc_71 : location_info := LocationInfo file_0 48 16 48 19.
  Definition loc_72 : location_info := LocationInfo file_0 48 16 48 19.
  Definition loc_73 : location_info := LocationInfo file_0 48 17 48 19.
  Definition loc_74 : location_info := LocationInfo file_0 48 17 48 19.
  Definition loc_75 : location_info := LocationInfo file_0 47 24 47 25.
  Definition loc_76 : location_info := LocationInfo file_0 47 24 47 25.
  Definition loc_79 : location_info := LocationInfo file_0 47 15 47 16.
  Definition loc_80 : location_info := LocationInfo file_0 47 15 47 16.
  Definition loc_85 : location_info := LocationInfo file_0 57 2 57 34.
  Definition loc_86 : location_info := LocationInfo file_0 58 2 58 34.
  Definition loc_87 : location_info := LocationInfo file_0 59 2 59 34.
  Definition loc_88 : location_info := LocationInfo file_0 60 2 60 34.
  Definition loc_89 : location_info := LocationInfo file_0 61 2 61 34.
  Definition loc_90 : location_info := LocationInfo file_0 62 2 62 15.
  Definition loc_91 : location_info := LocationInfo file_0 63 2 63 15.
  Definition loc_92 : location_info := LocationInfo file_0 64 2 64 15.
  Definition loc_93 : location_info := LocationInfo file_0 65 2 65 15.
  Definition loc_94 : location_info := LocationInfo file_0 66 2 66 15.
  Definition loc_95 : location_info := LocationInfo file_0 68 2 68 20.
  Definition loc_96 : location_info := LocationInfo file_0 69 2 69 66.
  Definition loc_97 : location_info := LocationInfo file_0 70 2 70 19.
  Definition loc_98 : location_info := LocationInfo file_0 72 2 72 32.
  Definition loc_99 : location_info := LocationInfo file_0 73 2 73 32.
  Definition loc_100 : location_info := LocationInfo file_0 74 2 74 32.
  Definition loc_101 : location_info := LocationInfo file_0 75 2 75 32.
  Definition loc_102 : location_info := LocationInfo file_0 76 2 76 32.
  Definition loc_103 : location_info := LocationInfo file_0 76 2 76 6.
  Definition loc_104 : location_info := LocationInfo file_0 76 2 76 6.
  Definition loc_105 : location_info := LocationInfo file_0 76 7 76 21.
  Definition loc_106 : location_info := LocationInfo file_0 76 23 76 30.
  Definition loc_107 : location_info := LocationInfo file_0 76 23 76 30.
  Definition loc_108 : location_info := LocationInfo file_0 76 23 76 30.
  Definition loc_109 : location_info := LocationInfo file_0 76 23 76 27.
  Definition loc_110 : location_info := LocationInfo file_0 76 23 76 27.
  Definition loc_111 : location_info := LocationInfo file_0 76 28 76 29.
  Definition loc_112 : location_info := LocationInfo file_0 75 2 75 6.
  Definition loc_113 : location_info := LocationInfo file_0 75 2 75 6.
  Definition loc_114 : location_info := LocationInfo file_0 75 7 75 21.
  Definition loc_115 : location_info := LocationInfo file_0 75 23 75 30.
  Definition loc_116 : location_info := LocationInfo file_0 75 23 75 30.
  Definition loc_117 : location_info := LocationInfo file_0 75 23 75 30.
  Definition loc_118 : location_info := LocationInfo file_0 75 23 75 27.
  Definition loc_119 : location_info := LocationInfo file_0 75 23 75 27.
  Definition loc_120 : location_info := LocationInfo file_0 75 28 75 29.
  Definition loc_121 : location_info := LocationInfo file_0 74 2 74 6.
  Definition loc_122 : location_info := LocationInfo file_0 74 2 74 6.
  Definition loc_123 : location_info := LocationInfo file_0 74 7 74 21.
  Definition loc_124 : location_info := LocationInfo file_0 74 23 74 30.
  Definition loc_125 : location_info := LocationInfo file_0 74 23 74 30.
  Definition loc_126 : location_info := LocationInfo file_0 74 23 74 30.
  Definition loc_127 : location_info := LocationInfo file_0 74 23 74 27.
  Definition loc_128 : location_info := LocationInfo file_0 74 23 74 27.
  Definition loc_129 : location_info := LocationInfo file_0 74 28 74 29.
  Definition loc_130 : location_info := LocationInfo file_0 73 2 73 6.
  Definition loc_131 : location_info := LocationInfo file_0 73 2 73 6.
  Definition loc_132 : location_info := LocationInfo file_0 73 7 73 21.
  Definition loc_133 : location_info := LocationInfo file_0 73 23 73 30.
  Definition loc_134 : location_info := LocationInfo file_0 73 23 73 30.
  Definition loc_135 : location_info := LocationInfo file_0 73 23 73 30.
  Definition loc_136 : location_info := LocationInfo file_0 73 23 73 27.
  Definition loc_137 : location_info := LocationInfo file_0 73 23 73 27.
  Definition loc_138 : location_info := LocationInfo file_0 73 28 73 29.
  Definition loc_139 : location_info := LocationInfo file_0 72 2 72 6.
  Definition loc_140 : location_info := LocationInfo file_0 72 2 72 6.
  Definition loc_141 : location_info := LocationInfo file_0 72 7 72 21.
  Definition loc_142 : location_info := LocationInfo file_0 72 23 72 30.
  Definition loc_143 : location_info := LocationInfo file_0 72 23 72 30.
  Definition loc_144 : location_info := LocationInfo file_0 72 23 72 30.
  Definition loc_145 : location_info := LocationInfo file_0 72 23 72 27.
  Definition loc_146 : location_info := LocationInfo file_0 72 23 72 27.
  Definition loc_147 : location_info := LocationInfo file_0 72 28 72 29.
  Definition loc_148 : location_info := LocationInfo file_0 70 9 70 17.
  Definition loc_149 : location_info := LocationInfo file_0 70 9 70 12.
  Definition loc_150 : location_info := LocationInfo file_0 70 9 70 12.
  Definition loc_151 : location_info := LocationInfo file_0 70 16 70 17.
  Definition loc_152 : location_info := LocationInfo file_0 69 12 69 65.
  Definition loc_153 : location_info := LocationInfo file_0 69 12 69 25.
  Definition loc_154 : location_info := LocationInfo file_0 69 12 69 25.
  Definition loc_155 : location_info := LocationInfo file_0 69 26 69 37.
  Definition loc_156 : location_info := LocationInfo file_0 69 39 69 52.
  Definition loc_157 : location_info := LocationInfo file_0 69 48 69 52.
  Definition loc_158 : location_info := LocationInfo file_0 69 48 69 52.
  Definition loc_159 : location_info := LocationInfo file_0 69 54 69 55.
  Definition loc_160 : location_info := LocationInfo file_0 69 57 69 64.
  Definition loc_161 : location_info := LocationInfo file_0 69 58 69 64.
  Definition loc_164 : location_info := LocationInfo file_0 68 18 68 19.
  Definition loc_167 : location_info := LocationInfo file_0 66 2 66 10.
  Definition loc_168 : location_info := LocationInfo file_0 66 3 66 10.
  Definition loc_169 : location_info := LocationInfo file_0 66 3 66 10.
  Definition loc_170 : location_info := LocationInfo file_0 66 3 66 10.
  Definition loc_171 : location_info := LocationInfo file_0 66 3 66 7.
  Definition loc_172 : location_info := LocationInfo file_0 66 3 66 7.
  Definition loc_173 : location_info := LocationInfo file_0 66 8 66 9.
  Definition loc_174 : location_info := LocationInfo file_0 66 13 66 14.
  Definition loc_175 : location_info := LocationInfo file_0 65 2 65 10.
  Definition loc_176 : location_info := LocationInfo file_0 65 3 65 10.
  Definition loc_177 : location_info := LocationInfo file_0 65 3 65 10.
  Definition loc_178 : location_info := LocationInfo file_0 65 3 65 10.
  Definition loc_179 : location_info := LocationInfo file_0 65 3 65 7.
  Definition loc_180 : location_info := LocationInfo file_0 65 3 65 7.
  Definition loc_181 : location_info := LocationInfo file_0 65 8 65 9.
  Definition loc_182 : location_info := LocationInfo file_0 65 13 65 14.
  Definition loc_183 : location_info := LocationInfo file_0 64 2 64 10.
  Definition loc_184 : location_info := LocationInfo file_0 64 3 64 10.
  Definition loc_185 : location_info := LocationInfo file_0 64 3 64 10.
  Definition loc_186 : location_info := LocationInfo file_0 64 3 64 10.
  Definition loc_187 : location_info := LocationInfo file_0 64 3 64 7.
  Definition loc_188 : location_info := LocationInfo file_0 64 3 64 7.
  Definition loc_189 : location_info := LocationInfo file_0 64 8 64 9.
  Definition loc_190 : location_info := LocationInfo file_0 64 13 64 14.
  Definition loc_191 : location_info := LocationInfo file_0 63 2 63 10.
  Definition loc_192 : location_info := LocationInfo file_0 63 3 63 10.
  Definition loc_193 : location_info := LocationInfo file_0 63 3 63 10.
  Definition loc_194 : location_info := LocationInfo file_0 63 3 63 10.
  Definition loc_195 : location_info := LocationInfo file_0 63 3 63 7.
  Definition loc_196 : location_info := LocationInfo file_0 63 3 63 7.
  Definition loc_197 : location_info := LocationInfo file_0 63 8 63 9.
  Definition loc_198 : location_info := LocationInfo file_0 63 13 63 14.
  Definition loc_199 : location_info := LocationInfo file_0 62 2 62 10.
  Definition loc_200 : location_info := LocationInfo file_0 62 3 62 10.
  Definition loc_201 : location_info := LocationInfo file_0 62 3 62 10.
  Definition loc_202 : location_info := LocationInfo file_0 62 3 62 10.
  Definition loc_203 : location_info := LocationInfo file_0 62 3 62 7.
  Definition loc_204 : location_info := LocationInfo file_0 62 3 62 7.
  Definition loc_205 : location_info := LocationInfo file_0 62 8 62 9.
  Definition loc_206 : location_info := LocationInfo file_0 62 13 62 14.
  Definition loc_207 : location_info := LocationInfo file_0 61 2 61 9.
  Definition loc_208 : location_info := LocationInfo file_0 61 2 61 9.
  Definition loc_209 : location_info := LocationInfo file_0 61 2 61 6.
  Definition loc_210 : location_info := LocationInfo file_0 61 2 61 6.
  Definition loc_211 : location_info := LocationInfo file_0 61 7 61 8.
  Definition loc_212 : location_info := LocationInfo file_0 61 12 61 33.
  Definition loc_213 : location_info := LocationInfo file_0 61 12 61 17.
  Definition loc_214 : location_info := LocationInfo file_0 61 12 61 17.
  Definition loc_215 : location_info := LocationInfo file_0 61 18 61 32.
  Definition loc_216 : location_info := LocationInfo file_0 60 2 60 9.
  Definition loc_217 : location_info := LocationInfo file_0 60 2 60 9.
  Definition loc_218 : location_info := LocationInfo file_0 60 2 60 6.
  Definition loc_219 : location_info := LocationInfo file_0 60 2 60 6.
  Definition loc_220 : location_info := LocationInfo file_0 60 7 60 8.
  Definition loc_221 : location_info := LocationInfo file_0 60 12 60 33.
  Definition loc_222 : location_info := LocationInfo file_0 60 12 60 17.
  Definition loc_223 : location_info := LocationInfo file_0 60 12 60 17.
  Definition loc_224 : location_info := LocationInfo file_0 60 18 60 32.
  Definition loc_225 : location_info := LocationInfo file_0 59 2 59 9.
  Definition loc_226 : location_info := LocationInfo file_0 59 2 59 9.
  Definition loc_227 : location_info := LocationInfo file_0 59 2 59 6.
  Definition loc_228 : location_info := LocationInfo file_0 59 2 59 6.
  Definition loc_229 : location_info := LocationInfo file_0 59 7 59 8.
  Definition loc_230 : location_info := LocationInfo file_0 59 12 59 33.
  Definition loc_231 : location_info := LocationInfo file_0 59 12 59 17.
  Definition loc_232 : location_info := LocationInfo file_0 59 12 59 17.
  Definition loc_233 : location_info := LocationInfo file_0 59 18 59 32.
  Definition loc_234 : location_info := LocationInfo file_0 58 2 58 9.
  Definition loc_235 : location_info := LocationInfo file_0 58 2 58 9.
  Definition loc_236 : location_info := LocationInfo file_0 58 2 58 6.
  Definition loc_237 : location_info := LocationInfo file_0 58 2 58 6.
  Definition loc_238 : location_info := LocationInfo file_0 58 7 58 8.
  Definition loc_239 : location_info := LocationInfo file_0 58 12 58 33.
  Definition loc_240 : location_info := LocationInfo file_0 58 12 58 17.
  Definition loc_241 : location_info := LocationInfo file_0 58 12 58 17.
  Definition loc_242 : location_info := LocationInfo file_0 58 18 58 32.
  Definition loc_243 : location_info := LocationInfo file_0 57 2 57 9.
  Definition loc_244 : location_info := LocationInfo file_0 57 2 57 9.
  Definition loc_245 : location_info := LocationInfo file_0 57 2 57 6.
  Definition loc_246 : location_info := LocationInfo file_0 57 2 57 6.
  Definition loc_247 : location_info := LocationInfo file_0 57 7 57 8.
  Definition loc_248 : location_info := LocationInfo file_0 57 12 57 33.
  Definition loc_249 : location_info := LocationInfo file_0 57 12 57 17.
  Definition loc_250 : location_info := LocationInfo file_0 57 12 57 17.
  Definition loc_251 : location_info := LocationInfo file_0 57 18 57 32.

  (* Definition of function [binary_search]. *)
  Definition impl_binary_search : function := {|
    f_args := [
      ("comp", void*);
      ("xs", void*);
      ("n", it_layout i32);
      ("x", void*)
    ];
    f_local_vars := [
      ("r", it_layout i32);
      ("l", it_layout i32);
      ("k", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "l" <-{ it_layout i32 } LocInfoE loc_59 (i2v 0 i32) ;
        "r" <-{ it_layout i32 }
          LocInfoE loc_55 (use{it_layout i32} (LocInfoE loc_56 ("n"))) ;
        locinfo: loc_3 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_50 ;
        if: LocInfoE loc_50 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_50 ((LocInfoE loc_51 (use{it_layout i32} (LocInfoE loc_52 ("l")))) <{IntOp i32, IntOp i32} (LocInfoE loc_53 (use{it_layout i32} (LocInfoE loc_54 ("r")))))))
        then
        Goto "#2"
        else
        locinfo: loc_4 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        "k" <-{ it_layout i32 }
          LocInfoE loc_38 ((LocInfoE loc_39 (use{it_layout i32} (LocInfoE loc_40 ("l")))) +{IntOp i32, IntOp i32} (LocInfoE loc_41 ((LocInfoE loc_42 ((LocInfoE loc_43 (use{it_layout i32} (LocInfoE loc_44 ("r")))) -{IntOp i32, IntOp i32} (LocInfoE loc_45 (use{it_layout i32} (LocInfoE loc_46 ("l")))))) /{IntOp i32, IntOp i32} (LocInfoE loc_47 (i2v 2 i32))))) ;
        locinfo: loc_25 ;
        if: LocInfoE loc_25 (Call (LocInfoE loc_27 (use{void*} (LocInfoE loc_28 ("comp")))) [@{expr} LocInfoE loc_29 (use{void*} (LocInfoE loc_31 ((LocInfoE loc_32 (!{void*} (LocInfoE loc_33 ("xs")))) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_34 (use{it_layout i32} (LocInfoE loc_35 ("k"))))))) ;
            LocInfoE loc_36 (use{void*} (LocInfoE loc_37 ("x"))) ])
        then
        locinfo: loc_14 ;
          Goto "#5"
        else
        locinfo: loc_21 ;
          Goto "#6"
      ]> $
      <[ "#3" :=
        locinfo: loc_4 ;
        Return (LocInfoE loc_5 (use{it_layout i32} (LocInfoE loc_6 ("l"))))
      ]> $
      <[ "#4" :=
        locinfo: loc_11 ;
        Goto "continue2"
      ]> $
      <[ "#5" :=
        locinfo: loc_14 ;
        LocInfoE loc_15 ("l") <-{ it_layout i32 }
          LocInfoE loc_16 ((LocInfoE loc_17 (use{it_layout i32} (LocInfoE loc_18 ("k")))) +{IntOp i32, IntOp i32} (LocInfoE loc_19 (i2v 1 i32))) ;
        locinfo: loc_11 ;
        Goto "#4"
      ]> $
      <[ "#6" :=
        locinfo: loc_21 ;
        LocInfoE loc_22 ("r") <-{ it_layout i32 }
          LocInfoE loc_23 (use{it_layout i32} (LocInfoE loc_24 ("k"))) ;
        locinfo: loc_11 ;
        Goto "#4"
      ]> $
      <[ "continue2" :=
        locinfo: loc_3 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [compare_int]. *)
  Definition impl_compare_int : function := {|
    f_args := [
      ("x", void*);
      ("y", void*)
    ];
    f_local_vars := [
      ("xi", void*);
      ("yi", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "xi" <-{ void* }
          LocInfoE loc_79 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_79 (use{void*} (LocInfoE loc_80 ("x"))))) ;
        "yi" <-{ void* }
          LocInfoE loc_75 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_75 (use{void*} (LocInfoE loc_76 ("y"))))) ;
        locinfo: loc_65 ;
        Return (LocInfoE loc_66 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_66 ((LocInfoE loc_67 (use{it_layout size_t} (LocInfoE loc_69 (!{void*} (LocInfoE loc_70 ("xi")))))) ≤{IntOp size_t, IntOp size_t} (LocInfoE loc_71 (use{it_layout size_t} (LocInfoE loc_73 (!{void*} (LocInfoE loc_74 ("yi"))))))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [test]. *)
  Definition impl_test (global_alloc global_binary_search global_compare_int global_free : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
      ("res", it_layout i32);
      ("ptrs", mk_array_layout void* 5);
      ("needle", it_layout size_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_85 ;
        LocInfoE loc_244 ((LocInfoE loc_246 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_247 (i2v 0 i32))) <-{ void* }
          LocInfoE loc_248 (Call (LocInfoE loc_250 (global_alloc)) [@{expr} LocInfoE loc_251 (i2v (it_layout size_t).(ly_size) size_t) ]) ;
        locinfo: loc_86 ;
        LocInfoE loc_235 ((LocInfoE loc_237 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_238 (i2v 1 i32))) <-{ void* }
          LocInfoE loc_239 (Call (LocInfoE loc_241 (global_alloc)) [@{expr} LocInfoE loc_242 (i2v (it_layout size_t).(ly_size) size_t) ]) ;
        locinfo: loc_87 ;
        LocInfoE loc_226 ((LocInfoE loc_228 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_229 (i2v 2 i32))) <-{ void* }
          LocInfoE loc_230 (Call (LocInfoE loc_232 (global_alloc)) [@{expr} LocInfoE loc_233 (i2v (it_layout size_t).(ly_size) size_t) ]) ;
        locinfo: loc_88 ;
        LocInfoE loc_217 ((LocInfoE loc_219 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_220 (i2v 3 i32))) <-{ void* }
          LocInfoE loc_221 (Call (LocInfoE loc_223 (global_alloc)) [@{expr} LocInfoE loc_224 (i2v (it_layout size_t).(ly_size) size_t) ]) ;
        locinfo: loc_89 ;
        LocInfoE loc_208 ((LocInfoE loc_210 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_211 (i2v 4 i32))) <-{ void* }
          LocInfoE loc_212 (Call (LocInfoE loc_214 (global_alloc)) [@{expr} LocInfoE loc_215 (i2v (it_layout size_t).(ly_size) size_t) ]) ;
        locinfo: loc_90 ;
        LocInfoE loc_200 (!{void*} (LocInfoE loc_202 ((LocInfoE loc_204 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_205 (i2v 0 i32))))) <-{ it_layout size_t }
          LocInfoE loc_206 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_206 (i2v 0 i32))) ;
        locinfo: loc_91 ;
        LocInfoE loc_192 (!{void*} (LocInfoE loc_194 ((LocInfoE loc_196 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_197 (i2v 1 i32))))) <-{ it_layout size_t }
          LocInfoE loc_198 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_198 (i2v 1 i32))) ;
        locinfo: loc_92 ;
        LocInfoE loc_184 (!{void*} (LocInfoE loc_186 ((LocInfoE loc_188 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_189 (i2v 2 i32))))) <-{ it_layout size_t }
          LocInfoE loc_190 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_190 (i2v 2 i32))) ;
        locinfo: loc_93 ;
        LocInfoE loc_176 (!{void*} (LocInfoE loc_178 ((LocInfoE loc_180 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_181 (i2v 3 i32))))) <-{ it_layout size_t }
          LocInfoE loc_182 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_182 (i2v 3 i32))) ;
        locinfo: loc_94 ;
        LocInfoE loc_168 (!{void*} (LocInfoE loc_170 ((LocInfoE loc_172 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_173 (i2v 4 i32))))) <-{ it_layout size_t }
          LocInfoE loc_174 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_174 (i2v 4 i32))) ;
        "needle" <-{ it_layout size_t }
          LocInfoE loc_164 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_164 (i2v 2 i32))) ;
        "res" <-{ it_layout i32 }
          LocInfoE loc_152 (Call (LocInfoE loc_154 (global_binary_search)) [@{expr} LocInfoE loc_155 (global_compare_int) ;
          LocInfoE loc_156 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_157 (&(LocInfoE loc_158 ("ptrs"))))) ;
          LocInfoE loc_159 (i2v 5 i32) ;
          LocInfoE loc_160 (&(LocInfoE loc_161 ("needle"))) ]) ;
        locinfo: loc_97 ;
        assert: (LocInfoE loc_148 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_148 ((LocInfoE loc_149 (use{it_layout i32} (LocInfoE loc_150 ("res")))) ={IntOp i32, IntOp i32} (LocInfoE loc_151 (i2v 3 i32)))))) ;
        locinfo: loc_98 ;
        expr: (LocInfoE loc_98 (Call (LocInfoE loc_140 (global_free)) [@{expr} LocInfoE loc_141 (i2v (it_layout size_t).(ly_size) size_t) ;
        LocInfoE loc_142 (use{void*} (LocInfoE loc_144 ((LocInfoE loc_146 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_147 (i2v 0 i32))))) ])) ;
        locinfo: loc_99 ;
        expr: (LocInfoE loc_99 (Call (LocInfoE loc_131 (global_free)) [@{expr} LocInfoE loc_132 (i2v (it_layout size_t).(ly_size) size_t) ;
        LocInfoE loc_133 (use{void*} (LocInfoE loc_135 ((LocInfoE loc_137 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_138 (i2v 1 i32))))) ])) ;
        locinfo: loc_100 ;
        expr: (LocInfoE loc_100 (Call (LocInfoE loc_122 (global_free)) [@{expr} LocInfoE loc_123 (i2v (it_layout size_t).(ly_size) size_t) ;
        LocInfoE loc_124 (use{void*} (LocInfoE loc_126 ((LocInfoE loc_128 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_129 (i2v 2 i32))))) ])) ;
        locinfo: loc_101 ;
        expr: (LocInfoE loc_101 (Call (LocInfoE loc_113 (global_free)) [@{expr} LocInfoE loc_114 (i2v (it_layout size_t).(ly_size) size_t) ;
        LocInfoE loc_115 (use{void*} (LocInfoE loc_117 ((LocInfoE loc_119 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_120 (i2v 3 i32))))) ])) ;
        locinfo: loc_102 ;
        expr: (LocInfoE loc_102 (Call (LocInfoE loc_104 (global_free)) [@{expr} LocInfoE loc_105 (i2v (it_layout size_t).(ly_size) size_t) ;
        LocInfoE loc_106 (use{void*} (LocInfoE loc_108 ((LocInfoE loc_110 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_111 (i2v 4 i32))))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
