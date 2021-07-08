From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/reverse.c]. *)
Section code.
  Definition file_0 : string := "examples/reverse.c".
  Definition file_1 : string := "include/refinedc.h".
  Definition loc_2 : location_info := LocationInfo file_1 50 2 50 47.
  Definition loc_3 : location_info := LocationInfo file_1 50 9 50 46.
  Definition loc_4 : location_info := LocationInfo file_1 50 9 50 32.
  Definition loc_5 : location_info := LocationInfo file_1 50 33 50 37.
  Definition loc_6 : location_info := LocationInfo file_1 50 33 50 37.
  Definition loc_7 : location_info := LocationInfo file_1 50 39 50 45.
  Definition loc_8 : location_info := LocationInfo file_1 50 39 50 45.
  Definition loc_11 : location_info := LocationInfo file_0 16 4 16 26.
  Definition loc_12 : location_info := LocationInfo file_0 16 11 16 25.
  Definition loc_15 : location_info := LocationInfo file_0 23 4 23 19.
  Definition loc_16 : location_info := LocationInfo file_0 24 4 24 19.
  Definition loc_17 : location_info := LocationInfo file_0 25 4 25 16.
  Definition loc_18 : location_info := LocationInfo file_0 25 11 25 15.
  Definition loc_19 : location_info := LocationInfo file_0 25 11 25 15.
  Definition loc_20 : location_info := LocationInfo file_0 24 4 24 14.
  Definition loc_21 : location_info := LocationInfo file_0 24 4 24 8.
  Definition loc_22 : location_info := LocationInfo file_0 24 4 24 8.
  Definition loc_23 : location_info := LocationInfo file_0 24 17 24 18.
  Definition loc_24 : location_info := LocationInfo file_0 24 17 24 18.
  Definition loc_25 : location_info := LocationInfo file_0 23 4 23 14.
  Definition loc_26 : location_info := LocationInfo file_0 23 4 23 8.
  Definition loc_27 : location_info := LocationInfo file_0 23 4 23 8.
  Definition loc_28 : location_info := LocationInfo file_0 23 17 23 18.
  Definition loc_29 : location_info := LocationInfo file_0 23 17 23 18.
  Definition loc_32 : location_info := LocationInfo file_0 33 2 35 3.
  Definition loc_33 : location_info := LocationInfo file_0 36 2 36 25.
  Definition loc_34 : location_info := LocationInfo file_0 37 2 37 18.
  Definition loc_35 : location_info := LocationInfo file_0 38 2 38 13.
  Definition loc_36 : location_info := LocationInfo file_0 38 9 38 12.
  Definition loc_37 : location_info := LocationInfo file_0 38 9 38 12.
  Definition loc_38 : location_info := LocationInfo file_0 37 2 37 4.
  Definition loc_39 : location_info := LocationInfo file_0 37 3 37 4.
  Definition loc_40 : location_info := LocationInfo file_0 37 3 37 4.
  Definition loc_41 : location_info := LocationInfo file_0 37 7 37 17.
  Definition loc_42 : location_info := LocationInfo file_0 37 7 37 17.
  Definition loc_43 : location_info := LocationInfo file_0 37 7 37 11.
  Definition loc_44 : location_info := LocationInfo file_0 37 7 37 11.
  Definition loc_45 : location_info := LocationInfo file_0 37 9 37 10.
  Definition loc_46 : location_info := LocationInfo file_0 37 9 37 10.
  Definition loc_47 : location_info := LocationInfo file_0 36 14 36 24.
  Definition loc_48 : location_info := LocationInfo file_0 36 14 36 24.
  Definition loc_49 : location_info := LocationInfo file_0 36 14 36 18.
  Definition loc_50 : location_info := LocationInfo file_0 36 14 36 18.
  Definition loc_51 : location_info := LocationInfo file_0 36 16 36 17.
  Definition loc_52 : location_info := LocationInfo file_0 36 16 36 17.
  Definition loc_55 : location_info := LocationInfo file_0 33 28 35 3.
  Definition loc_56 : location_info := LocationInfo file_0 34 6 34 28.
  Definition loc_57 : location_info := LocationInfo file_0 34 13 34 27.
  Definition loc_59 : location_info := LocationInfo file_0 33 6 33 26.
  Definition loc_60 : location_info := LocationInfo file_0 33 6 33 8.
  Definition loc_61 : location_info := LocationInfo file_0 33 6 33 8.
  Definition loc_62 : location_info := LocationInfo file_0 33 7 33 8.
  Definition loc_63 : location_info := LocationInfo file_0 33 7 33 8.
  Definition loc_64 : location_info := LocationInfo file_0 33 12 33 26.
  Definition loc_67 : location_info := LocationInfo file_0 48 2 50 3.
  Definition loc_68 : location_info := LocationInfo file_0 51 2 51 28.
  Definition loc_69 : location_info := LocationInfo file_0 52 2 54 3.
  Definition loc_70 : location_info := LocationInfo file_0 55 2 55 36.
  Definition loc_71 : location_info := LocationInfo file_0 55 9 55 35.
  Definition loc_72 : location_info := LocationInfo file_0 55 9 55 19.
  Definition loc_73 : location_info := LocationInfo file_0 55 9 55 19.
  Definition loc_74 : location_info := LocationInfo file_0 55 20 55 31.
  Definition loc_75 : location_info := LocationInfo file_0 55 21 55 31.
  Definition loc_76 : location_info := LocationInfo file_0 55 21 55 25.
  Definition loc_77 : location_info := LocationInfo file_0 55 21 55 25.
  Definition loc_78 : location_info := LocationInfo file_0 55 23 55 24.
  Definition loc_79 : location_info := LocationInfo file_0 55 23 55 24.
  Definition loc_80 : location_info := LocationInfo file_0 55 33 55 34.
  Definition loc_81 : location_info := LocationInfo file_0 55 33 55 34.
  Definition loc_82 : location_info := LocationInfo file_0 52 18 54 3.
  Definition loc_83 : location_info := LocationInfo file_0 53 6 53 15.
  Definition loc_84 : location_info := LocationInfo file_0 53 13 53 14.
  Definition loc_86 : location_info := LocationInfo file_0 52 6 52 16.
  Definition loc_87 : location_info := LocationInfo file_0 52 6 52 11.
  Definition loc_88 : location_info := LocationInfo file_0 52 6 52 11.
  Definition loc_89 : location_info := LocationInfo file_0 52 7 52 11.
  Definition loc_90 : location_info := LocationInfo file_0 52 7 52 11.
  Definition loc_91 : location_info := LocationInfo file_0 52 15 52 16.
  Definition loc_92 : location_info := LocationInfo file_0 52 15 52 16.
  Definition loc_93 : location_info := LocationInfo file_0 51 17 51 27.
  Definition loc_94 : location_info := LocationInfo file_0 51 17 51 27.
  Definition loc_95 : location_info := LocationInfo file_0 51 17 51 21.
  Definition loc_96 : location_info := LocationInfo file_0 51 17 51 21.
  Definition loc_97 : location_info := LocationInfo file_0 51 19 51 20.
  Definition loc_98 : location_info := LocationInfo file_0 51 19 51 20.
  Definition loc_101 : location_info := LocationInfo file_0 48 28 50 3.
  Definition loc_102 : location_info := LocationInfo file_0 49 6 49 15.
  Definition loc_103 : location_info := LocationInfo file_0 49 13 49 14.
  Definition loc_105 : location_info := LocationInfo file_0 48 6 48 26.
  Definition loc_106 : location_info := LocationInfo file_0 48 6 48 8.
  Definition loc_107 : location_info := LocationInfo file_0 48 6 48 8.
  Definition loc_108 : location_info := LocationInfo file_0 48 7 48 8.
  Definition loc_109 : location_info := LocationInfo file_0 48 7 48 8.
  Definition loc_110 : location_info := LocationInfo file_0 48 12 48 26.
  Definition loc_113 : location_info := LocationInfo file_0 65 4 65 23.
  Definition loc_114 : location_info := LocationInfo file_0 71 4 80 5.
  Definition loc_115 : location_info := LocationInfo file_0 81 4 81 13.
  Definition loc_116 : location_info := LocationInfo file_0 81 11 81 12.
  Definition loc_117 : location_info := LocationInfo file_0 71 4 80 5.
  Definition loc_118 : location_info := LocationInfo file_0 71 35 80 5.
  Definition loc_119 : location_info := LocationInfo file_0 72 8 72 27.
  Definition loc_120 : location_info := LocationInfo file_0 74 8 74 33.
  Definition loc_121 : location_info := LocationInfo file_0 75 8 77 9.
  Definition loc_122 : location_info := LocationInfo file_0 79 8 79 26.
  Definition loc_123 : location_info := LocationInfo file_0 71 4 80 5.
  Definition loc_124 : location_info := LocationInfo file_0 71 4 80 5.
  Definition loc_125 : location_info := LocationInfo file_0 79 8 79 12.
  Definition loc_126 : location_info := LocationInfo file_0 79 15 79 25.
  Definition loc_127 : location_info := LocationInfo file_0 79 16 79 25.
  Definition loc_128 : location_info := LocationInfo file_0 79 16 79 19.
  Definition loc_129 : location_info := LocationInfo file_0 79 16 79 19.
  Definition loc_130 : location_info := LocationInfo file_0 75 23 77 9.
  Definition loc_131 : location_info := LocationInfo file_0 76 12 76 21.
  Definition loc_132 : location_info := LocationInfo file_0 76 19 76 20.
  Definition loc_134 : location_info := LocationInfo file_0 75 11 75 21.
  Definition loc_135 : location_info := LocationInfo file_0 75 11 75 16.
  Definition loc_136 : location_info := LocationInfo file_0 75 11 75 16.
  Definition loc_137 : location_info := LocationInfo file_0 75 12 75 16.
  Definition loc_138 : location_info := LocationInfo file_0 75 12 75 16.
  Definition loc_139 : location_info := LocationInfo file_0 75 20 75 21.
  Definition loc_140 : location_info := LocationInfo file_0 75 20 75 21.
  Definition loc_141 : location_info := LocationInfo file_0 74 23 74 32.
  Definition loc_142 : location_info := LocationInfo file_0 74 23 74 32.
  Definition loc_143 : location_info := LocationInfo file_0 74 23 74 26.
  Definition loc_144 : location_info := LocationInfo file_0 74 23 74 26.
  Definition loc_147 : location_info := LocationInfo file_0 72 21 72 26.
  Definition loc_148 : location_info := LocationInfo file_0 72 21 72 26.
  Definition loc_149 : location_info := LocationInfo file_0 72 22 72 26.
  Definition loc_150 : location_info := LocationInfo file_0 72 22 72 26.
  Definition loc_153 : location_info := LocationInfo file_0 71 10 71 33.
  Definition loc_154 : location_info := LocationInfo file_0 71 10 71 15.
  Definition loc_155 : location_info := LocationInfo file_0 71 10 71 15.
  Definition loc_156 : location_info := LocationInfo file_0 71 11 71 15.
  Definition loc_157 : location_info := LocationInfo file_0 71 11 71 15.
  Definition loc_158 : location_info := LocationInfo file_0 71 19 71 33.
  Definition loc_159 : location_info := LocationInfo file_0 65 19 65 22.
  Definition loc_160 : location_info := LocationInfo file_0 65 20 65 22.
  Definition loc_161 : location_info := LocationInfo file_0 65 21 65 22.
  Definition loc_162 : location_info := LocationInfo file_0 65 21 65 22.
  Definition loc_167 : location_info := LocationInfo file_0 88 4 88 25.
  Definition loc_168 : location_info := LocationInfo file_0 89 4 89 19.
  Definition loc_169 : location_info := LocationInfo file_0 90 4 90 45.
  Definition loc_170 : location_info := LocationInfo file_0 91 4 91 19.
  Definition loc_171 : location_info := LocationInfo file_0 92 4 92 45.
  Definition loc_172 : location_info := LocationInfo file_0 93 4 93 24.
  Definition loc_173 : location_info := LocationInfo file_0 94 4 94 28.
  Definition loc_174 : location_info := LocationInfo file_0 95 4 95 25.
  Definition loc_175 : location_info := LocationInfo file_0 99 4 99 13.
  Definition loc_176 : location_info := LocationInfo file_0 99 4 99 13.
  Definition loc_177 : location_info := LocationInfo file_0 99 12 99 13.
  Definition loc_178 : location_info := LocationInfo file_0 99 4 99 13.
  Definition loc_179 : location_info := LocationInfo file_0 99 4 99 13.
  Definition loc_180 : location_info := LocationInfo file_0 99 10 99 11.
  Definition loc_181 : location_info := LocationInfo file_0 95 11 95 23.
  Definition loc_182 : location_info := LocationInfo file_0 95 11 95 18.
  Definition loc_183 : location_info := LocationInfo file_0 95 11 95 18.
  Definition loc_184 : location_info := LocationInfo file_0 95 12 95 18.
  Definition loc_185 : location_info := LocationInfo file_0 95 12 95 18.
  Definition loc_186 : location_info := LocationInfo file_0 95 22 95 23.
  Definition loc_187 : location_info := LocationInfo file_0 94 4 94 10.
  Definition loc_188 : location_info := LocationInfo file_0 94 13 94 27.
  Definition loc_189 : location_info := LocationInfo file_0 94 13 94 16.
  Definition loc_190 : location_info := LocationInfo file_0 94 13 94 16.
  Definition loc_191 : location_info := LocationInfo file_0 94 17 94 26.
  Definition loc_192 : location_info := LocationInfo file_0 94 18 94 26.
  Definition loc_193 : location_info := LocationInfo file_0 94 19 94 26.
  Definition loc_194 : location_info := LocationInfo file_0 94 19 94 26.
  Definition loc_195 : location_info := LocationInfo file_0 94 20 94 26.
  Definition loc_196 : location_info := LocationInfo file_0 94 20 94 26.
  Definition loc_197 : location_info := LocationInfo file_0 93 4 93 10.
  Definition loc_198 : location_info := LocationInfo file_0 93 13 93 23.
  Definition loc_199 : location_info := LocationInfo file_0 93 13 93 16.
  Definition loc_200 : location_info := LocationInfo file_0 93 13 93 16.
  Definition loc_201 : location_info := LocationInfo file_0 93 17 93 22.
  Definition loc_202 : location_info := LocationInfo file_0 93 18 93 22.
  Definition loc_203 : location_info := LocationInfo file_0 92 4 92 8.
  Definition loc_204 : location_info := LocationInfo file_0 92 11 92 44.
  Definition loc_205 : location_info := LocationInfo file_0 92 11 92 15.
  Definition loc_206 : location_info := LocationInfo file_0 92 11 92 15.
  Definition loc_207 : location_info := LocationInfo file_0 92 16 92 20.
  Definition loc_208 : location_info := LocationInfo file_0 92 16 92 20.
  Definition loc_209 : location_info := LocationInfo file_0 92 22 92 29.
  Definition loc_210 : location_info := LocationInfo file_0 92 23 92 29.
  Definition loc_211 : location_info := LocationInfo file_0 92 31 92 43.
  Definition loc_212 : location_info := LocationInfo file_0 92 32 92 43.
  Definition loc_213 : location_info := LocationInfo file_0 91 4 91 10.
  Definition loc_214 : location_info := LocationInfo file_0 91 13 91 18.
  Definition loc_215 : location_info := LocationInfo file_0 91 14 91 18.
  Definition loc_216 : location_info := LocationInfo file_0 90 4 90 8.
  Definition loc_217 : location_info := LocationInfo file_0 90 11 90 44.
  Definition loc_218 : location_info := LocationInfo file_0 90 11 90 15.
  Definition loc_219 : location_info := LocationInfo file_0 90 11 90 15.
  Definition loc_220 : location_info := LocationInfo file_0 90 16 90 20.
  Definition loc_221 : location_info := LocationInfo file_0 90 16 90 20.
  Definition loc_222 : location_info := LocationInfo file_0 90 22 90 29.
  Definition loc_223 : location_info := LocationInfo file_0 90 23 90 29.
  Definition loc_224 : location_info := LocationInfo file_0 90 31 90 43.
  Definition loc_225 : location_info := LocationInfo file_0 90 32 90 43.
  Definition loc_226 : location_info := LocationInfo file_0 89 17 89 18.
  Definition loc_229 : location_info := LocationInfo file_0 88 18 88 24.
  Definition loc_230 : location_info := LocationInfo file_0 88 18 88 22.
  Definition loc_231 : location_info := LocationInfo file_0 88 18 88 22.
  Definition loc_236 : location_info := LocationInfo file_0 108 2 108 21.
  Definition loc_237 : location_info := LocationInfo file_0 109 2 109 8.
  Definition loc_238 : location_info := LocationInfo file_0 113 2 118 3.
  Definition loc_239 : location_info := LocationInfo file_0 119 2 119 11.
  Definition loc_240 : location_info := LocationInfo file_0 119 9 119 10.
  Definition loc_241 : location_info := LocationInfo file_0 119 9 119 10.
  Definition loc_242 : location_info := LocationInfo file_0 113 2 118 3.
  Definition loc_243 : location_info := LocationInfo file_0 113 30 118 3.
  Definition loc_244 : location_info := LocationInfo file_0 114 4 114 16.
  Definition loc_245 : location_info := LocationInfo file_0 115 4 115 16.
  Definition loc_246 : location_info := LocationInfo file_0 116 4 116 10.
  Definition loc_247 : location_info := LocationInfo file_0 117 4 117 10.
  Definition loc_248 : location_info := LocationInfo file_0 113 2 118 3.
  Definition loc_249 : location_info := LocationInfo file_0 113 2 118 3.
  Definition loc_250 : location_info := LocationInfo file_0 117 4 117 5.
  Definition loc_251 : location_info := LocationInfo file_0 117 8 117 9.
  Definition loc_252 : location_info := LocationInfo file_0 117 8 117 9.
  Definition loc_253 : location_info := LocationInfo file_0 116 4 116 5.
  Definition loc_254 : location_info := LocationInfo file_0 116 8 116 9.
  Definition loc_255 : location_info := LocationInfo file_0 116 8 116 9.
  Definition loc_256 : location_info := LocationInfo file_0 115 4 115 11.
  Definition loc_257 : location_info := LocationInfo file_0 115 4 115 5.
  Definition loc_258 : location_info := LocationInfo file_0 115 4 115 5.
  Definition loc_259 : location_info := LocationInfo file_0 115 14 115 15.
  Definition loc_260 : location_info := LocationInfo file_0 115 14 115 15.
  Definition loc_261 : location_info := LocationInfo file_0 114 4 114 5.
  Definition loc_262 : location_info := LocationInfo file_0 114 8 114 15.
  Definition loc_263 : location_info := LocationInfo file_0 114 8 114 15.
  Definition loc_264 : location_info := LocationInfo file_0 114 8 114 9.
  Definition loc_265 : location_info := LocationInfo file_0 114 8 114 9.
  Definition loc_266 : location_info := LocationInfo file_0 113 9 113 28.
  Definition loc_267 : location_info := LocationInfo file_0 113 9 113 10.
  Definition loc_268 : location_info := LocationInfo file_0 113 9 113 10.
  Definition loc_269 : location_info := LocationInfo file_0 113 14 113 28.
  Definition loc_270 : location_info := LocationInfo file_0 109 2 109 3.
  Definition loc_271 : location_info := LocationInfo file_0 109 6 109 7.
  Definition loc_272 : location_info := LocationInfo file_0 109 6 109 7.
  Definition loc_273 : location_info := LocationInfo file_0 108 2 108 3.
  Definition loc_274 : location_info := LocationInfo file_0 108 6 108 20.
  Definition loc_277 : location_info := LocationInfo file_0 127 2 127 26.
  Definition loc_278 : location_info := LocationInfo file_0 132 2 136 3.
  Definition loc_279 : location_info := LocationInfo file_0 137 2 137 11.
  Definition loc_280 : location_info := LocationInfo file_0 137 11 137 3.
  Definition loc_281 : location_info := LocationInfo file_0 138 2 138 11.
  Definition loc_282 : location_info := LocationInfo file_0 138 9 138 10.
  Definition loc_283 : location_info := LocationInfo file_0 138 9 138 10.
  Definition loc_284 : location_info := LocationInfo file_0 137 2 137 10.
  Definition loc_285 : location_info := LocationInfo file_0 137 3 137 10.
  Definition loc_286 : location_info := LocationInfo file_0 137 5 137 9.
  Definition loc_287 : location_info := LocationInfo file_0 137 5 137 9.
  Definition loc_288 : location_info := LocationInfo file_0 132 2 136 3.
  Definition loc_289 : location_info := LocationInfo file_0 132 34 136 3.
  Definition loc_290 : location_info := LocationInfo file_0 133 6 133 31.
  Definition loc_291 : location_info := LocationInfo file_0 135 6 135 24.
  Definition loc_292 : location_info := LocationInfo file_0 132 2 136 3.
  Definition loc_293 : location_info := LocationInfo file_0 132 2 136 3.
  Definition loc_294 : location_info := LocationInfo file_0 135 6 135 10.
  Definition loc_295 : location_info := LocationInfo file_0 135 13 135 23.
  Definition loc_296 : location_info := LocationInfo file_0 135 14 135 23.
  Definition loc_297 : location_info := LocationInfo file_0 135 14 135 17.
  Definition loc_298 : location_info := LocationInfo file_0 135 14 135 17.
  Definition loc_299 : location_info := LocationInfo file_0 133 25 133 30.
  Definition loc_300 : location_info := LocationInfo file_0 133 25 133 30.
  Definition loc_301 : location_info := LocationInfo file_0 133 26 133 30.
  Definition loc_302 : location_info := LocationInfo file_0 133 26 133 30.
  Definition loc_305 : location_info := LocationInfo file_0 132 9 132 32.
  Definition loc_306 : location_info := LocationInfo file_0 132 9 132 14.
  Definition loc_307 : location_info := LocationInfo file_0 132 9 132 14.
  Definition loc_308 : location_info := LocationInfo file_0 132 10 132 14.
  Definition loc_309 : location_info := LocationInfo file_0 132 10 132 14.
  Definition loc_310 : location_info := LocationInfo file_0 132 18 132 32.
  Definition loc_311 : location_info := LocationInfo file_0 127 23 127 25.
  Definition loc_312 : location_info := LocationInfo file_0 127 24 127 25.

  (* Definition of struct [list]. *)
  Program Definition struct_list := {|
    sl_members := [
      (Some "head", void*);
      (Some "tail", void*)
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

  (* Definition of function [init]. *)
  Definition impl_init : function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_11 ;
        Return (LocInfoE loc_12 (NULL))
      ]> $∅
    )%E
  |}.

  (* Definition of function [push]. *)
  Definition impl_push : function := {|
    f_args := [
      ("p", void*);
      ("e", void*);
      ("node", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_15 ;
        LocInfoE loc_25 ((LocInfoE loc_26 (!{void*} (LocInfoE loc_27 ("node")))) at{struct_list} "head") <-{ void* }
          LocInfoE loc_28 (use{void*} (LocInfoE loc_29 ("e"))) ;
        locinfo: loc_16 ;
        LocInfoE loc_20 ((LocInfoE loc_21 (!{void*} (LocInfoE loc_22 ("node")))) at{struct_list} "tail") <-{ void* }
          LocInfoE loc_23 (use{void*} (LocInfoE loc_24 ("p"))) ;
        locinfo: loc_17 ;
        Return (LocInfoE loc_18 (use{void*} (LocInfoE loc_19 ("node"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [pop]. *)
  Definition impl_pop : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("ret", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_59 ;
        if: LocInfoE loc_59 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_59 ((LocInfoE loc_60 (use{void*} (LocInfoE loc_62 (!{void*} (LocInfoE loc_63 ("p")))))) ={PtrOp, PtrOp} (LocInfoE loc_64 (NULL)))))
        then
        locinfo: loc_56 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#1" :=
        "ret" <-{ void* }
          LocInfoE loc_47 (use{void*} (LocInfoE loc_48 ((LocInfoE loc_49 (!{void*} (LocInfoE loc_51 (!{void*} (LocInfoE loc_52 ("p")))))) at{struct_list} "head"))) ;
        locinfo: loc_34 ;
        LocInfoE loc_39 (!{void*} (LocInfoE loc_40 ("p"))) <-{ void* }
          LocInfoE loc_41 (use{void*} (LocInfoE loc_42 ((LocInfoE loc_43 (!{void*} (LocInfoE loc_45 (!{void*} (LocInfoE loc_46 ("p")))))) at{struct_list} "tail"))) ;
        locinfo: loc_35 ;
        Return (LocInfoE loc_36 (use{void*} (LocInfoE loc_37 ("ret"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_56 ;
        Return (LocInfoE loc_57 (NULL))
      ]> $
      <[ "#3" :=
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [member_rec]. *)
  Definition impl_member_rec (global_member_rec : loc): function := {|
    f_args := [
      ("p", void*);
      ("k", it_layout size_t)
    ];
    f_local_vars := [
      ("head", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_105 ;
        if: LocInfoE loc_105 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_105 ((LocInfoE loc_106 (use{void*} (LocInfoE loc_108 (!{void*} (LocInfoE loc_109 ("p")))))) ={PtrOp, PtrOp} (LocInfoE loc_110 (NULL)))))
        then
        locinfo: loc_102 ;
          Goto "#5"
        else
        Goto "#6"
      ]> $
      <[ "#1" :=
        "head" <-{ void* }
          LocInfoE loc_93 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_93 (use{void*} (LocInfoE loc_94 ((LocInfoE loc_95 (!{void*} (LocInfoE loc_97 (!{void*} (LocInfoE loc_98 ("p")))))) at{struct_list} "head"))))) ;
        locinfo: loc_86 ;
        if: LocInfoE loc_86 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_86 ((LocInfoE loc_87 (use{it_layout size_t} (LocInfoE loc_89 (!{void*} (LocInfoE loc_90 ("head")))))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_91 (use{it_layout size_t} (LocInfoE loc_92 ("k")))))))
        then
        locinfo: loc_83 ;
          Goto "#3"
        else
        locinfo: loc_70 ;
          Goto "#4"
      ]> $
      <[ "#2" :=
        locinfo: loc_70 ;
        Return (LocInfoE loc_71 (Call (LocInfoE loc_73 (global_member_rec)) [@{expr} LocInfoE loc_74 (&(LocInfoE loc_75 ((LocInfoE loc_76 (!{void*} (LocInfoE loc_78 (!{void*} (LocInfoE loc_79 ("p")))))) at{struct_list} "tail"))) ;
               LocInfoE loc_80 (use{it_layout size_t} (LocInfoE loc_81 ("k"))) ]))
      ]> $
      <[ "#3" :=
        locinfo: loc_83 ;
        Return (LocInfoE loc_84 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_84 (i2v 1 i32))))
      ]> $
      <[ "#4" :=
        locinfo: loc_70 ;
        Goto "#2"
      ]> $
      <[ "#5" :=
        locinfo: loc_102 ;
        Return (LocInfoE loc_103 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_103 (i2v 0 i32))))
      ]> $
      <[ "#6" :=
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [member]. *)
  Definition impl_member : function := {|
    f_args := [
      ("p", void*);
      ("k", it_layout size_t)
    ];
    f_local_vars := [
      ("prev", void*);
      ("cur", void*);
      ("head", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "prev" <-{ void* }
          LocInfoE loc_159 (&(LocInfoE loc_161 (!{void*} (LocInfoE loc_162 ("p"))))) ;
        locinfo: loc_114 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_153 ;
        if: LocInfoE loc_153 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_153 ((LocInfoE loc_154 (use{void*} (LocInfoE loc_156 (!{void*} (LocInfoE loc_157 ("prev")))))) !={PtrOp, PtrOp} (LocInfoE loc_158 (NULL)))))
        then
        Goto "#2"
        else
        locinfo: loc_115 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        "cur" <-{ void* }
          LocInfoE loc_147 (use{void*} (LocInfoE loc_149 (!{void*} (LocInfoE loc_150 ("prev"))))) ;
        "head" <-{ void* }
          LocInfoE loc_141 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_141 (use{void*} (LocInfoE loc_142 ((LocInfoE loc_143 (!{void*} (LocInfoE loc_144 ("cur")))) at{struct_list} "head"))))) ;
        locinfo: loc_134 ;
        if: LocInfoE loc_134 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_134 ((LocInfoE loc_135 (use{it_layout size_t} (LocInfoE loc_137 (!{void*} (LocInfoE loc_138 ("head")))))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_139 (use{it_layout size_t} (LocInfoE loc_140 ("k")))))))
        then
        locinfo: loc_131 ;
          Goto "#5"
        else
        locinfo: loc_122 ;
          Goto "#6"
      ]> $
      <[ "#3" :=
        locinfo: loc_115 ;
        Return (LocInfoE loc_116 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_116 (i2v 0 i32))))
      ]> $
      <[ "#4" :=
        locinfo: loc_122 ;
        LocInfoE loc_125 ("prev") <-{ void* }
          LocInfoE loc_126 (&(LocInfoE loc_127 ((LocInfoE loc_128 (!{void*} (LocInfoE loc_129 ("cur")))) at{struct_list} "tail"))) ;
        locinfo: loc_123 ;
        Goto "continue15"
      ]> $
      <[ "#5" :=
        locinfo: loc_131 ;
        Return (LocInfoE loc_132 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_132 (i2v 1 i32))))
      ]> $
      <[ "#6" :=
        locinfo: loc_122 ;
        Goto "#4"
      ]> $
      <[ "continue15" :=
        locinfo: loc_114 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [test]. *)
  Definition impl_test (global_init global_pop global_push : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
      ("list", void*);
      ("local1", it_layout i32);
      ("local1_node", layout_of struct_list);
      ("local3", void*);
      ("local2", void*);
      ("local4", void*);
      ("local2_node", layout_of struct_list)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "list" <-{ void* }
          LocInfoE loc_229 (Call (LocInfoE loc_231 (global_init)) [@{expr}  ]) ;
        "local1" <-{ it_layout i32 } LocInfoE loc_226 (i2v 0 i32) ;
        locinfo: loc_169 ;
        LocInfoE loc_216 ("list") <-{ void* }
          LocInfoE loc_217 (Call (LocInfoE loc_219 (global_push)) [@{expr} LocInfoE loc_220 (use{void*} (LocInfoE loc_221 ("list"))) ;
          LocInfoE loc_222 (&(LocInfoE loc_223 ("local1"))) ;
          LocInfoE loc_224 (&(LocInfoE loc_225 ("local1_node"))) ]) ;
        locinfo: loc_170 ;
        LocInfoE loc_213 ("local2") <-{ void* }
          LocInfoE loc_214 (&(LocInfoE loc_215 ("list"))) ;
        locinfo: loc_171 ;
        LocInfoE loc_203 ("list") <-{ void* }
          LocInfoE loc_204 (Call (LocInfoE loc_206 (global_push)) [@{expr} LocInfoE loc_207 (use{void*} (LocInfoE loc_208 ("list"))) ;
          LocInfoE loc_209 (&(LocInfoE loc_210 ("local2"))) ;
          LocInfoE loc_211 (&(LocInfoE loc_212 ("local2_node"))) ]) ;
        locinfo: loc_172 ;
        LocInfoE loc_197 ("local3") <-{ void* }
          LocInfoE loc_198 (Call (LocInfoE loc_200 (global_pop)) [@{expr} LocInfoE loc_201 (&(LocInfoE loc_202 ("list"))) ]) ;
        locinfo: loc_173 ;
        LocInfoE loc_187 ("local4") <-{ void* }
          LocInfoE loc_188 (Call (LocInfoE loc_190 (global_pop)) [@{expr} LocInfoE loc_191 (&(LocInfoE loc_193 (!{void*} (LocInfoE loc_195 (!{void*} (LocInfoE loc_196 ("local3"))))))) ]) ;
        locinfo: loc_174 ;
        assert: (LocInfoE loc_181 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_181 ((LocInfoE loc_182 (use{it_layout i32} (LocInfoE loc_184 (!{void*} (LocInfoE loc_185 ("local4")))))) ={IntOp i32, IntOp i32} (LocInfoE loc_186 (i2v 0 i32)))))) ;
        locinfo: loc_175 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_180 ;
        if: LocInfoE loc_180 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_180 (i2v 1 i32)))
        then
        locinfo: loc_178 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_178 ;
        Goto "continue20"
      ]> $
      <[ "#3" :=
        Return (VOID)
      ]> $
      <[ "continue20" :=
        locinfo: loc_175 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [reverse]. *)
  Definition impl_reverse : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("v", void*);
      ("w", void*);
      ("t", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_236 ;
        LocInfoE loc_273 ("w") <-{ void* } LocInfoE loc_274 (NULL) ;
        locinfo: loc_237 ;
        LocInfoE loc_270 ("v") <-{ void* }
          LocInfoE loc_271 (use{void*} (LocInfoE loc_272 ("p"))) ;
        locinfo: loc_238 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_266 ;
        if: LocInfoE loc_266 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_266 ((LocInfoE loc_267 (use{void*} (LocInfoE loc_268 ("v")))) !={PtrOp, PtrOp} (LocInfoE loc_269 (NULL)))))
        then
        locinfo: loc_244 ;
          Goto "#2"
        else
        locinfo: loc_239 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_244 ;
        LocInfoE loc_261 ("t") <-{ void* }
          LocInfoE loc_262 (use{void*} (LocInfoE loc_263 ((LocInfoE loc_264 (!{void*} (LocInfoE loc_265 ("v")))) at{struct_list} "tail"))) ;
        locinfo: loc_245 ;
        LocInfoE loc_256 ((LocInfoE loc_257 (!{void*} (LocInfoE loc_258 ("v")))) at{struct_list} "tail") <-{ void* }
          LocInfoE loc_259 (use{void*} (LocInfoE loc_260 ("w"))) ;
        locinfo: loc_246 ;
        LocInfoE loc_253 ("w") <-{ void* }
          LocInfoE loc_254 (use{void*} (LocInfoE loc_255 ("v"))) ;
        locinfo: loc_247 ;
        LocInfoE loc_250 ("v") <-{ void* }
          LocInfoE loc_251 (use{void*} (LocInfoE loc_252 ("t"))) ;
        locinfo: loc_248 ;
        Goto "continue23"
      ]> $
      <[ "#3" :=
        locinfo: loc_239 ;
        Return (LocInfoE loc_240 (use{void*} (LocInfoE loc_241 ("w"))))
      ]> $
      <[ "continue23" :=
        locinfo: loc_238 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [forward]. *)
  Definition impl_forward : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("prev", void*);
      ("cur", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "prev" <-{ void* } LocInfoE loc_311 (&(LocInfoE loc_312 ("p"))) ;
        locinfo: loc_278 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_305 ;
        if: LocInfoE loc_305 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_305 ((LocInfoE loc_306 (use{void*} (LocInfoE loc_308 (!{void*} (LocInfoE loc_309 ("prev")))))) !={PtrOp, PtrOp} (LocInfoE loc_310 (NULL)))))
        then
        Goto "#2"
        else
        locinfo: loc_279 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        "cur" <-{ void* }
          LocInfoE loc_299 (use{void*} (LocInfoE loc_301 (!{void*} (LocInfoE loc_302 ("prev"))))) ;
        locinfo: loc_291 ;
        LocInfoE loc_294 ("prev") <-{ void* }
          LocInfoE loc_295 (&(LocInfoE loc_296 ((LocInfoE loc_297 (!{void*} (LocInfoE loc_298 ("cur")))) at{struct_list} "tail"))) ;
        locinfo: loc_292 ;
        Goto "continue27"
      ]> $
      <[ "#3" :=
        locinfo: loc_279 ;
        expr: (LocInfoE loc_284 (&(LocInfoE loc_286 (!{void*} (LocInfoE loc_287 ("prev")))))) ;
        locinfo: loc_281 ;
        Return (LocInfoE loc_282 (use{void*} (LocInfoE loc_283 ("p"))))
      ]> $
      <[ "continue27" :=
        locinfo: loc_278 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.
End code.
