From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/binary_search.c]. *)
Section code.
  Definition file_0 : string := "include/assume.h".
  Definition file_1 : string := "examples/binary_search.c".
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
  Definition loc_41 : location_info := LocationInfo file_1 24 2 24 22.
  Definition loc_42 : location_info := LocationInfo file_1 30 2 37 3.
  Definition loc_43 : location_info := LocationInfo file_1 38 2 38 11.
  Definition loc_44 : location_info := LocationInfo file_1 38 9 38 10.
  Definition loc_45 : location_info := LocationInfo file_1 38 9 38 10.
  Definition loc_46 : location_info := LocationInfo file_1 30 15 37 3.
  Definition loc_47 : location_info := LocationInfo file_1 31 4 31 31.
  Definition loc_48 : location_info := LocationInfo file_1 32 4 36 5.
  Definition loc_49 : location_info := LocationInfo file_1 32 24 34 7.
  Definition loc_50 : location_info := LocationInfo file_1 33 6 33 16.
  Definition loc_51 : location_info := LocationInfo file_1 33 6 33 7.
  Definition loc_52 : location_info := LocationInfo file_1 33 10 33 15.
  Definition loc_53 : location_info := LocationInfo file_1 33 10 33 11.
  Definition loc_54 : location_info := LocationInfo file_1 33 10 33 11.
  Definition loc_55 : location_info := LocationInfo file_1 33 14 33 15.
  Definition loc_56 : location_info := LocationInfo file_1 34 13 36 5.
  Definition loc_57 : location_info := LocationInfo file_1 35 6 35 12.
  Definition loc_58 : location_info := LocationInfo file_1 35 6 35 7.
  Definition loc_59 : location_info := LocationInfo file_1 35 10 35 11.
  Definition loc_60 : location_info := LocationInfo file_1 35 10 35 11.
  Definition loc_61 : location_info := LocationInfo file_1 32 8 32 22.
  Definition loc_62 : location_info := LocationInfo file_1 32 8 32 12.
  Definition loc_63 : location_info := LocationInfo file_1 32 8 32 12.
  Definition loc_64 : location_info := LocationInfo file_1 32 8 32 12.
  Definition loc_65 : location_info := LocationInfo file_1 32 13 32 18.
  Definition loc_66 : location_info := LocationInfo file_1 32 13 32 18.
  Definition loc_67 : location_info := LocationInfo file_1 32 13 32 18.
  Definition loc_68 : location_info := LocationInfo file_1 32 13 32 15.
  Definition loc_69 : location_info := LocationInfo file_1 32 13 32 15.
  Definition loc_70 : location_info := LocationInfo file_1 32 16 32 17.
  Definition loc_71 : location_info := LocationInfo file_1 32 16 32 17.
  Definition loc_72 : location_info := LocationInfo file_1 32 20 32 21.
  Definition loc_73 : location_info := LocationInfo file_1 32 20 32 21.
  Definition loc_74 : location_info := LocationInfo file_1 31 15 31 30.
  Definition loc_75 : location_info := LocationInfo file_1 31 15 31 16.
  Definition loc_76 : location_info := LocationInfo file_1 31 15 31 16.
  Definition loc_77 : location_info := LocationInfo file_1 31 19 31 30.
  Definition loc_78 : location_info := LocationInfo file_1 31 19 31 26.
  Definition loc_79 : location_info := LocationInfo file_1 31 20 31 21.
  Definition loc_80 : location_info := LocationInfo file_1 31 20 31 21.
  Definition loc_81 : location_info := LocationInfo file_1 31 24 31 25.
  Definition loc_82 : location_info := LocationInfo file_1 31 24 31 25.
  Definition loc_83 : location_info := LocationInfo file_1 31 29 31 30.
  Definition loc_86 : location_info := LocationInfo file_1 30 8 30 13.
  Definition loc_87 : location_info := LocationInfo file_1 30 8 30 9.
  Definition loc_88 : location_info := LocationInfo file_1 30 8 30 9.
  Definition loc_89 : location_info := LocationInfo file_1 30 12 30 13.
  Definition loc_90 : location_info := LocationInfo file_1 30 12 30 13.
  Definition loc_91 : location_info := LocationInfo file_1 24 20 24 21.
  Definition loc_92 : location_info := LocationInfo file_1 24 20 24 21.
  Definition loc_95 : location_info := LocationInfo file_1 24 13 24 14.
  Definition loc_100 : location_info := LocationInfo file_1 47 2 47 26.
  Definition loc_101 : location_info := LocationInfo file_1 48 2 48 20.
  Definition loc_102 : location_info := LocationInfo file_1 48 9 48 19.
  Definition loc_103 : location_info := LocationInfo file_1 48 9 48 12.
  Definition loc_104 : location_info := LocationInfo file_1 48 9 48 12.
  Definition loc_105 : location_info := LocationInfo file_1 48 10 48 12.
  Definition loc_106 : location_info := LocationInfo file_1 48 10 48 12.
  Definition loc_107 : location_info := LocationInfo file_1 48 16 48 19.
  Definition loc_108 : location_info := LocationInfo file_1 48 16 48 19.
  Definition loc_109 : location_info := LocationInfo file_1 48 17 48 19.
  Definition loc_110 : location_info := LocationInfo file_1 48 17 48 19.
  Definition loc_111 : location_info := LocationInfo file_1 47 24 47 25.
  Definition loc_112 : location_info := LocationInfo file_1 47 24 47 25.
  Definition loc_115 : location_info := LocationInfo file_1 47 15 47 16.
  Definition loc_116 : location_info := LocationInfo file_1 47 15 47 16.
  Definition loc_121 : location_info := LocationInfo file_1 56 2 56 18.
  Definition loc_122 : location_info := LocationInfo file_1 57 2 57 36.
  Definition loc_123 : location_info := LocationInfo file_1 58 2 58 36.
  Definition loc_124 : location_info := LocationInfo file_1 59 2 59 36.
  Definition loc_125 : location_info := LocationInfo file_1 60 2 60 36.
  Definition loc_126 : location_info := LocationInfo file_1 61 2 61 36.
  Definition loc_127 : location_info := LocationInfo file_1 62 2 62 15.
  Definition loc_128 : location_info := LocationInfo file_1 63 2 63 15.
  Definition loc_129 : location_info := LocationInfo file_1 64 2 64 15.
  Definition loc_130 : location_info := LocationInfo file_1 65 2 65 15.
  Definition loc_131 : location_info := LocationInfo file_1 66 2 66 15.
  Definition loc_132 : location_info := LocationInfo file_1 68 2 68 20.
  Definition loc_133 : location_info := LocationInfo file_1 69 2 69 66.
  Definition loc_134 : location_info := LocationInfo file_1 70 2 70 19.
  Definition loc_135 : location_info := LocationInfo file_1 72 2 72 16.
  Definition loc_136 : location_info := LocationInfo file_1 73 2 73 16.
  Definition loc_137 : location_info := LocationInfo file_1 74 2 74 16.
  Definition loc_138 : location_info := LocationInfo file_1 75 2 75 16.
  Definition loc_139 : location_info := LocationInfo file_1 76 2 76 16.
  Definition loc_140 : location_info := LocationInfo file_1 76 2 76 6.
  Definition loc_141 : location_info := LocationInfo file_1 76 2 76 6.
  Definition loc_142 : location_info := LocationInfo file_1 76 7 76 14.
  Definition loc_143 : location_info := LocationInfo file_1 76 7 76 14.
  Definition loc_144 : location_info := LocationInfo file_1 76 7 76 14.
  Definition loc_145 : location_info := LocationInfo file_1 76 7 76 11.
  Definition loc_146 : location_info := LocationInfo file_1 76 7 76 11.
  Definition loc_147 : location_info := LocationInfo file_1 76 12 76 13.
  Definition loc_148 : location_info := LocationInfo file_1 75 2 75 6.
  Definition loc_149 : location_info := LocationInfo file_1 75 2 75 6.
  Definition loc_150 : location_info := LocationInfo file_1 75 7 75 14.
  Definition loc_151 : location_info := LocationInfo file_1 75 7 75 14.
  Definition loc_152 : location_info := LocationInfo file_1 75 7 75 14.
  Definition loc_153 : location_info := LocationInfo file_1 75 7 75 11.
  Definition loc_154 : location_info := LocationInfo file_1 75 7 75 11.
  Definition loc_155 : location_info := LocationInfo file_1 75 12 75 13.
  Definition loc_156 : location_info := LocationInfo file_1 74 2 74 6.
  Definition loc_157 : location_info := LocationInfo file_1 74 2 74 6.
  Definition loc_158 : location_info := LocationInfo file_1 74 7 74 14.
  Definition loc_159 : location_info := LocationInfo file_1 74 7 74 14.
  Definition loc_160 : location_info := LocationInfo file_1 74 7 74 14.
  Definition loc_161 : location_info := LocationInfo file_1 74 7 74 11.
  Definition loc_162 : location_info := LocationInfo file_1 74 7 74 11.
  Definition loc_163 : location_info := LocationInfo file_1 74 12 74 13.
  Definition loc_164 : location_info := LocationInfo file_1 73 2 73 6.
  Definition loc_165 : location_info := LocationInfo file_1 73 2 73 6.
  Definition loc_166 : location_info := LocationInfo file_1 73 7 73 14.
  Definition loc_167 : location_info := LocationInfo file_1 73 7 73 14.
  Definition loc_168 : location_info := LocationInfo file_1 73 7 73 14.
  Definition loc_169 : location_info := LocationInfo file_1 73 7 73 11.
  Definition loc_170 : location_info := LocationInfo file_1 73 7 73 11.
  Definition loc_171 : location_info := LocationInfo file_1 73 12 73 13.
  Definition loc_172 : location_info := LocationInfo file_1 72 2 72 6.
  Definition loc_173 : location_info := LocationInfo file_1 72 2 72 6.
  Definition loc_174 : location_info := LocationInfo file_1 72 7 72 14.
  Definition loc_175 : location_info := LocationInfo file_1 72 7 72 14.
  Definition loc_176 : location_info := LocationInfo file_1 72 7 72 14.
  Definition loc_177 : location_info := LocationInfo file_1 72 7 72 11.
  Definition loc_178 : location_info := LocationInfo file_1 72 7 72 11.
  Definition loc_179 : location_info := LocationInfo file_1 72 12 72 13.
  Definition loc_180 : location_info := LocationInfo file_1 70 9 70 17.
  Definition loc_181 : location_info := LocationInfo file_1 70 9 70 12.
  Definition loc_182 : location_info := LocationInfo file_1 70 9 70 12.
  Definition loc_183 : location_info := LocationInfo file_1 70 16 70 17.
  Definition loc_184 : location_info := LocationInfo file_1 69 12 69 65.
  Definition loc_185 : location_info := LocationInfo file_1 69 12 69 25.
  Definition loc_186 : location_info := LocationInfo file_1 69 12 69 25.
  Definition loc_187 : location_info := LocationInfo file_1 69 26 69 37.
  Definition loc_188 : location_info := LocationInfo file_1 69 39 69 52.
  Definition loc_189 : location_info := LocationInfo file_1 69 48 69 52.
  Definition loc_190 : location_info := LocationInfo file_1 69 48 69 52.
  Definition loc_191 : location_info := LocationInfo file_1 69 54 69 55.
  Definition loc_192 : location_info := LocationInfo file_1 69 57 69 64.
  Definition loc_193 : location_info := LocationInfo file_1 69 58 69 64.
  Definition loc_196 : location_info := LocationInfo file_1 68 18 68 19.
  Definition loc_199 : location_info := LocationInfo file_1 66 2 66 10.
  Definition loc_200 : location_info := LocationInfo file_1 66 3 66 10.
  Definition loc_201 : location_info := LocationInfo file_1 66 3 66 10.
  Definition loc_202 : location_info := LocationInfo file_1 66 3 66 10.
  Definition loc_203 : location_info := LocationInfo file_1 66 3 66 7.
  Definition loc_204 : location_info := LocationInfo file_1 66 3 66 7.
  Definition loc_205 : location_info := LocationInfo file_1 66 8 66 9.
  Definition loc_206 : location_info := LocationInfo file_1 66 13 66 14.
  Definition loc_207 : location_info := LocationInfo file_1 65 2 65 10.
  Definition loc_208 : location_info := LocationInfo file_1 65 3 65 10.
  Definition loc_209 : location_info := LocationInfo file_1 65 3 65 10.
  Definition loc_210 : location_info := LocationInfo file_1 65 3 65 10.
  Definition loc_211 : location_info := LocationInfo file_1 65 3 65 7.
  Definition loc_212 : location_info := LocationInfo file_1 65 3 65 7.
  Definition loc_213 : location_info := LocationInfo file_1 65 8 65 9.
  Definition loc_214 : location_info := LocationInfo file_1 65 13 65 14.
  Definition loc_215 : location_info := LocationInfo file_1 64 2 64 10.
  Definition loc_216 : location_info := LocationInfo file_1 64 3 64 10.
  Definition loc_217 : location_info := LocationInfo file_1 64 3 64 10.
  Definition loc_218 : location_info := LocationInfo file_1 64 3 64 10.
  Definition loc_219 : location_info := LocationInfo file_1 64 3 64 7.
  Definition loc_220 : location_info := LocationInfo file_1 64 3 64 7.
  Definition loc_221 : location_info := LocationInfo file_1 64 8 64 9.
  Definition loc_222 : location_info := LocationInfo file_1 64 13 64 14.
  Definition loc_223 : location_info := LocationInfo file_1 63 2 63 10.
  Definition loc_224 : location_info := LocationInfo file_1 63 3 63 10.
  Definition loc_225 : location_info := LocationInfo file_1 63 3 63 10.
  Definition loc_226 : location_info := LocationInfo file_1 63 3 63 10.
  Definition loc_227 : location_info := LocationInfo file_1 63 3 63 7.
  Definition loc_228 : location_info := LocationInfo file_1 63 3 63 7.
  Definition loc_229 : location_info := LocationInfo file_1 63 8 63 9.
  Definition loc_230 : location_info := LocationInfo file_1 63 13 63 14.
  Definition loc_231 : location_info := LocationInfo file_1 62 2 62 10.
  Definition loc_232 : location_info := LocationInfo file_1 62 3 62 10.
  Definition loc_233 : location_info := LocationInfo file_1 62 3 62 10.
  Definition loc_234 : location_info := LocationInfo file_1 62 3 62 10.
  Definition loc_235 : location_info := LocationInfo file_1 62 3 62 7.
  Definition loc_236 : location_info := LocationInfo file_1 62 3 62 7.
  Definition loc_237 : location_info := LocationInfo file_1 62 8 62 9.
  Definition loc_238 : location_info := LocationInfo file_1 62 13 62 14.
  Definition loc_239 : location_info := LocationInfo file_1 61 2 61 9.
  Definition loc_240 : location_info := LocationInfo file_1 61 2 61 9.
  Definition loc_241 : location_info := LocationInfo file_1 61 2 61 6.
  Definition loc_242 : location_info := LocationInfo file_1 61 2 61 6.
  Definition loc_243 : location_info := LocationInfo file_1 61 7 61 8.
  Definition loc_244 : location_info := LocationInfo file_1 61 12 61 35.
  Definition loc_245 : location_info := LocationInfo file_1 61 12 61 19.
  Definition loc_246 : location_info := LocationInfo file_1 61 12 61 19.
  Definition loc_247 : location_info := LocationInfo file_1 61 20 61 34.
  Definition loc_248 : location_info := LocationInfo file_1 60 2 60 9.
  Definition loc_249 : location_info := LocationInfo file_1 60 2 60 9.
  Definition loc_250 : location_info := LocationInfo file_1 60 2 60 6.
  Definition loc_251 : location_info := LocationInfo file_1 60 2 60 6.
  Definition loc_252 : location_info := LocationInfo file_1 60 7 60 8.
  Definition loc_253 : location_info := LocationInfo file_1 60 12 60 35.
  Definition loc_254 : location_info := LocationInfo file_1 60 12 60 19.
  Definition loc_255 : location_info := LocationInfo file_1 60 12 60 19.
  Definition loc_256 : location_info := LocationInfo file_1 60 20 60 34.
  Definition loc_257 : location_info := LocationInfo file_1 59 2 59 9.
  Definition loc_258 : location_info := LocationInfo file_1 59 2 59 9.
  Definition loc_259 : location_info := LocationInfo file_1 59 2 59 6.
  Definition loc_260 : location_info := LocationInfo file_1 59 2 59 6.
  Definition loc_261 : location_info := LocationInfo file_1 59 7 59 8.
  Definition loc_262 : location_info := LocationInfo file_1 59 12 59 35.
  Definition loc_263 : location_info := LocationInfo file_1 59 12 59 19.
  Definition loc_264 : location_info := LocationInfo file_1 59 12 59 19.
  Definition loc_265 : location_info := LocationInfo file_1 59 20 59 34.
  Definition loc_266 : location_info := LocationInfo file_1 58 2 58 9.
  Definition loc_267 : location_info := LocationInfo file_1 58 2 58 9.
  Definition loc_268 : location_info := LocationInfo file_1 58 2 58 6.
  Definition loc_269 : location_info := LocationInfo file_1 58 2 58 6.
  Definition loc_270 : location_info := LocationInfo file_1 58 7 58 8.
  Definition loc_271 : location_info := LocationInfo file_1 58 12 58 35.
  Definition loc_272 : location_info := LocationInfo file_1 58 12 58 19.
  Definition loc_273 : location_info := LocationInfo file_1 58 12 58 19.
  Definition loc_274 : location_info := LocationInfo file_1 58 20 58 34.
  Definition loc_275 : location_info := LocationInfo file_1 57 2 57 9.
  Definition loc_276 : location_info := LocationInfo file_1 57 2 57 9.
  Definition loc_277 : location_info := LocationInfo file_1 57 2 57 6.
  Definition loc_278 : location_info := LocationInfo file_1 57 2 57 6.
  Definition loc_279 : location_info := LocationInfo file_1 57 7 57 8.
  Definition loc_280 : location_info := LocationInfo file_1 57 12 57 35.
  Definition loc_281 : location_info := LocationInfo file_1 57 12 57 19.
  Definition loc_282 : location_info := LocationInfo file_1 57 12 57 19.
  Definition loc_283 : location_info := LocationInfo file_1 57 20 57 34.

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

  (* Definition of function [binary_search]. *)
  Definition impl_binary_search : function := {|
    f_args := [
      ("comp", void*);
      ("xs", void*);
      ("n", it_layout size_t);
      ("x", void*)
    ];
    f_local_vars := [
      ("r", it_layout size_t);
      ("l", it_layout size_t);
      ("k", it_layout size_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "l" <-{ IntOp size_t }
          LocInfoE loc_95 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_95 (i2v 0 i32))) ;
        "r" <-{ IntOp size_t }
          LocInfoE loc_91 (use{IntOp size_t} (LocInfoE loc_92 ("n"))) ;
        locinfo: loc_42 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_86 ;
        if{IntOp i32, None}: LocInfoE loc_86 ((LocInfoE loc_87 (use{IntOp size_t} (LocInfoE loc_88 ("l")))) <{IntOp size_t, IntOp size_t, i32} (LocInfoE loc_89 (use{IntOp size_t} (LocInfoE loc_90 ("r")))))
        then
        Goto "#2"
        else
        locinfo: loc_43 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        "k" <-{ IntOp size_t }
          LocInfoE loc_74 ((LocInfoE loc_75 (use{IntOp size_t} (LocInfoE loc_76 ("l")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_77 ((LocInfoE loc_78 ((LocInfoE loc_79 (use{IntOp size_t} (LocInfoE loc_80 ("r")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_81 (use{IntOp size_t} (LocInfoE loc_82 ("l")))))) /{IntOp size_t, IntOp size_t} (LocInfoE loc_83 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_83 (i2v 2 i32))))))) ;
        locinfo: loc_61 ;
        if{BoolOp, None}: LocInfoE loc_61 (Call (LocInfoE loc_63 (use{PtrOp} (LocInfoE loc_64 ("comp")))) [@{expr} LocInfoE loc_65 (use{PtrOp} (LocInfoE loc_67 ((LocInfoE loc_68 (!{PtrOp} (LocInfoE loc_69 ("xs")))) at_offset{void*, PtrOp, IntOp size_t} (LocInfoE loc_70 (use{IntOp size_t} (LocInfoE loc_71 ("k"))))))) ;
                          LocInfoE loc_72 (use{PtrOp} (LocInfoE loc_73 ("x"))) ])
        then
        locinfo: loc_50 ;
          Goto "#4"
        else
        locinfo: loc_57 ;
          Goto "#5"
      ]> $
      <[ "#3" :=
        locinfo: loc_43 ;
        Return (LocInfoE loc_44 (use{IntOp size_t} (LocInfoE loc_45 ("l"))))
      ]> $
      <[ "#4" :=
        locinfo: loc_50 ;
        LocInfoE loc_51 ("l") <-{ IntOp size_t }
          LocInfoE loc_52 ((LocInfoE loc_53 (use{IntOp size_t} (LocInfoE loc_54 ("k")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_55 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_55 (i2v 1 i32))))) ;
        locinfo: loc_42 ;
        Goto "#1"
      ]> $
      <[ "#5" :=
        locinfo: loc_57 ;
        LocInfoE loc_58 ("r") <-{ IntOp size_t }
          LocInfoE loc_59 (use{IntOp size_t} (LocInfoE loc_60 ("k"))) ;
        locinfo: loc_42 ;
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
        "xi" <-{ PtrOp }
          LocInfoE loc_115 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_115 (use{PtrOp} (LocInfoE loc_116 ("x"))))) ;
        "yi" <-{ PtrOp }
          LocInfoE loc_111 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_111 (use{PtrOp} (LocInfoE loc_112 ("y"))))) ;
        locinfo: loc_101 ;
        Return (LocInfoE loc_102 (UnOp (CastOp $ BoolOp) (IntOp i32) (LocInfoE loc_102 ((LocInfoE loc_103 (use{IntOp size_t} (LocInfoE loc_105 (!{PtrOp} (LocInfoE loc_106 ("xi")))))) ≤{IntOp size_t, IntOp size_t, i32} (LocInfoE loc_107 (use{IntOp size_t} (LocInfoE loc_109 (!{PtrOp} (LocInfoE loc_110 ("yi"))))))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [test]. *)
  Definition impl_test (global_binary_search global_compare_int global_free global_xmalloc : loc): function := {|
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
        locinfo: loc_122 ;
        LocInfoE loc_276 ((LocInfoE loc_278 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_279 (i2v 0 i32))) <-{ PtrOp }
          LocInfoE loc_280 (Call (LocInfoE loc_282 (global_xmalloc)) [@{expr} LocInfoE loc_283 (i2v (it_layout size_t).(ly_size) size_t) ]) ;
        locinfo: loc_123 ;
        LocInfoE loc_267 ((LocInfoE loc_269 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_270 (i2v 1 i32))) <-{ PtrOp }
          LocInfoE loc_271 (Call (LocInfoE loc_273 (global_xmalloc)) [@{expr} LocInfoE loc_274 (i2v (it_layout size_t).(ly_size) size_t) ]) ;
        locinfo: loc_124 ;
        LocInfoE loc_258 ((LocInfoE loc_260 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_261 (i2v 2 i32))) <-{ PtrOp }
          LocInfoE loc_262 (Call (LocInfoE loc_264 (global_xmalloc)) [@{expr} LocInfoE loc_265 (i2v (it_layout size_t).(ly_size) size_t) ]) ;
        locinfo: loc_125 ;
        LocInfoE loc_249 ((LocInfoE loc_251 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_252 (i2v 3 i32))) <-{ PtrOp }
          LocInfoE loc_253 (Call (LocInfoE loc_255 (global_xmalloc)) [@{expr} LocInfoE loc_256 (i2v (it_layout size_t).(ly_size) size_t) ]) ;
        locinfo: loc_126 ;
        LocInfoE loc_240 ((LocInfoE loc_242 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_243 (i2v 4 i32))) <-{ PtrOp }
          LocInfoE loc_244 (Call (LocInfoE loc_246 (global_xmalloc)) [@{expr} LocInfoE loc_247 (i2v (it_layout size_t).(ly_size) size_t) ]) ;
        locinfo: loc_127 ;
        LocInfoE loc_232 (!{PtrOp} (LocInfoE loc_234 ((LocInfoE loc_236 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_237 (i2v 0 i32))))) <-{ IntOp size_t }
          LocInfoE loc_238 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_238 (i2v 0 i32))) ;
        locinfo: loc_128 ;
        LocInfoE loc_224 (!{PtrOp} (LocInfoE loc_226 ((LocInfoE loc_228 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_229 (i2v 1 i32))))) <-{ IntOp size_t }
          LocInfoE loc_230 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_230 (i2v 1 i32))) ;
        locinfo: loc_129 ;
        LocInfoE loc_216 (!{PtrOp} (LocInfoE loc_218 ((LocInfoE loc_220 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_221 (i2v 2 i32))))) <-{ IntOp size_t }
          LocInfoE loc_222 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_222 (i2v 2 i32))) ;
        locinfo: loc_130 ;
        LocInfoE loc_208 (!{PtrOp} (LocInfoE loc_210 ((LocInfoE loc_212 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_213 (i2v 3 i32))))) <-{ IntOp size_t }
          LocInfoE loc_214 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_214 (i2v 3 i32))) ;
        locinfo: loc_131 ;
        LocInfoE loc_200 (!{PtrOp} (LocInfoE loc_202 ((LocInfoE loc_204 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_205 (i2v 4 i32))))) <-{ IntOp size_t }
          LocInfoE loc_206 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_206 (i2v 4 i32))) ;
        "needle" <-{ IntOp size_t }
          LocInfoE loc_196 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_196 (i2v 2 i32))) ;
        "res" <-{ IntOp i32 }
          LocInfoE loc_184 (UnOp (CastOp $ IntOp i32) (IntOp size_t) (LocInfoE loc_184 (Call (LocInfoE loc_186 (global_binary_search)) [@{expr} LocInfoE loc_187 (global_compare_int) ;
          LocInfoE loc_188 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_189 (&(LocInfoE loc_190 ("ptrs"))))) ;
          LocInfoE loc_191 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_191 (i2v 5 i32))) ;
          LocInfoE loc_192 (&(LocInfoE loc_193 ("needle"))) ]))) ;
        locinfo: loc_134 ;
        assert{IntOp i32}: (LocInfoE loc_180 ((LocInfoE loc_181 (use{IntOp i32} (LocInfoE loc_182 ("res")))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_183 (i2v 3 i32)))) ;
        locinfo: loc_135 ;
        expr: (LocInfoE loc_135 (Call (LocInfoE loc_173 (global_free)) [@{expr} LocInfoE loc_174 (use{PtrOp} (LocInfoE loc_176 ((LocInfoE loc_178 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_179 (i2v 0 i32))))) ])) ;
        locinfo: loc_136 ;
        expr: (LocInfoE loc_136 (Call (LocInfoE loc_165 (global_free)) [@{expr} LocInfoE loc_166 (use{PtrOp} (LocInfoE loc_168 ((LocInfoE loc_170 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_171 (i2v 1 i32))))) ])) ;
        locinfo: loc_137 ;
        expr: (LocInfoE loc_137 (Call (LocInfoE loc_157 (global_free)) [@{expr} LocInfoE loc_158 (use{PtrOp} (LocInfoE loc_160 ((LocInfoE loc_162 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_163 (i2v 2 i32))))) ])) ;
        locinfo: loc_138 ;
        expr: (LocInfoE loc_138 (Call (LocInfoE loc_149 (global_free)) [@{expr} LocInfoE loc_150 (use{PtrOp} (LocInfoE loc_152 ((LocInfoE loc_154 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_155 (i2v 3 i32))))) ])) ;
        locinfo: loc_139 ;
        expr: (LocInfoE loc_139 (Call (LocInfoE loc_141 (global_free)) [@{expr} LocInfoE loc_142 (use{PtrOp} (LocInfoE loc_144 ((LocInfoE loc_146 ("ptrs")) at_offset{void*, PtrOp, IntOp i32} (LocInfoE loc_147 (i2v 4 i32))))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
