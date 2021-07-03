From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/intptr.c]. *)
Section code.
  Definition file_0 : string := "examples/intptr.c".
  Definition loc_2 : location_info := LocationInfo file_0 18 2 18 30.
  Definition loc_3 : location_info := LocationInfo file_0 20 2 20 11.
  Definition loc_4 : location_info := LocationInfo file_0 20 9 20 10.
  Definition loc_5 : location_info := LocationInfo file_0 20 9 20 10.
  Definition loc_6 : location_info := LocationInfo file_0 18 16 18 29.
  Definition loc_7 : location_info := LocationInfo file_0 18 28 18 29.
  Definition loc_8 : location_info := LocationInfo file_0 18 28 18 29.
  Definition loc_13 : location_info := LocationInfo file_0 28 2 28 30.
  Definition loc_14 : location_info := LocationInfo file_0 29 2 29 11.
  Definition loc_15 : location_info := LocationInfo file_0 29 9 29 10.
  Definition loc_16 : location_info := LocationInfo file_0 29 9 29 10.
  Definition loc_17 : location_info := LocationInfo file_0 28 16 28 29.
  Definition loc_18 : location_info := LocationInfo file_0 28 28 28 29.
  Definition loc_19 : location_info := LocationInfo file_0 28 28 28 29.
  Definition loc_24 : location_info := LocationInfo file_0 37 2 37 30.
  Definition loc_25 : location_info := LocationInfo file_0 38 2 38 15.
  Definition loc_26 : location_info := LocationInfo file_0 38 9 38 14.
  Definition loc_27 : location_info := LocationInfo file_0 38 9 38 10.
  Definition loc_28 : location_info := LocationInfo file_0 38 9 38 10.
  Definition loc_29 : location_info := LocationInfo file_0 38 13 38 14.
  Definition loc_30 : location_info := LocationInfo file_0 37 16 37 29.
  Definition loc_31 : location_info := LocationInfo file_0 37 28 37 29.
  Definition loc_32 : location_info := LocationInfo file_0 37 28 37 29.
  Definition loc_37 : location_info := LocationInfo file_0 46 2 46 32.
  Definition loc_38 : location_info := LocationInfo file_0 47 2 47 32.
  Definition loc_39 : location_info := LocationInfo file_0 49 2 51 3.
  Definition loc_40 : location_info := LocationInfo file_0 53 2 53 12.
  Definition loc_41 : location_info := LocationInfo file_0 53 9 53 11.
  Definition loc_42 : location_info := LocationInfo file_0 53 9 53 11.
  Definition loc_43 : location_info := LocationInfo file_0 49 14 51 3.
  Definition loc_44 : location_info := LocationInfo file_0 50 4 50 14.
  Definition loc_45 : location_info := LocationInfo file_0 50 11 50 13.
  Definition loc_46 : location_info := LocationInfo file_0 50 11 50 13.
  Definition loc_48 : location_info := LocationInfo file_0 49 5 49 13.
  Definition loc_49 : location_info := LocationInfo file_0 49 5 49 7.
  Definition loc_50 : location_info := LocationInfo file_0 49 5 49 7.
  Definition loc_51 : location_info := LocationInfo file_0 49 11 49 13.
  Definition loc_52 : location_info := LocationInfo file_0 49 11 49 13.
  Definition loc_53 : location_info := LocationInfo file_0 47 17 47 31.
  Definition loc_54 : location_info := LocationInfo file_0 47 29 47 31.
  Definition loc_55 : location_info := LocationInfo file_0 47 29 47 31.
  Definition loc_58 : location_info := LocationInfo file_0 46 17 46 31.
  Definition loc_59 : location_info := LocationInfo file_0 46 29 46 31.
  Definition loc_60 : location_info := LocationInfo file_0 46 29 46 31.
  Definition loc_65 : location_info := LocationInfo file_0 61 2 61 32.
  Definition loc_66 : location_info := LocationInfo file_0 62 2 62 32.
  Definition loc_67 : location_info := LocationInfo file_0 64 2 66 3.
  Definition loc_68 : location_info := LocationInfo file_0 68 2 68 12.
  Definition loc_69 : location_info := LocationInfo file_0 68 9 68 11.
  Definition loc_70 : location_info := LocationInfo file_0 68 9 68 11.
  Definition loc_71 : location_info := LocationInfo file_0 64 14 66 3.
  Definition loc_72 : location_info := LocationInfo file_0 65 4 65 14.
  Definition loc_73 : location_info := LocationInfo file_0 65 11 65 13.
  Definition loc_74 : location_info := LocationInfo file_0 65 11 65 13.
  Definition loc_76 : location_info := LocationInfo file_0 64 5 64 13.
  Definition loc_77 : location_info := LocationInfo file_0 64 5 64 7.
  Definition loc_78 : location_info := LocationInfo file_0 64 5 64 7.
  Definition loc_79 : location_info := LocationInfo file_0 64 11 64 13.
  Definition loc_80 : location_info := LocationInfo file_0 64 11 64 13.
  Definition loc_81 : location_info := LocationInfo file_0 62 17 62 31.
  Definition loc_82 : location_info := LocationInfo file_0 62 29 62 31.
  Definition loc_83 : location_info := LocationInfo file_0 62 29 62 31.
  Definition loc_86 : location_info := LocationInfo file_0 61 17 61 31.
  Definition loc_87 : location_info := LocationInfo file_0 61 29 61 31.
  Definition loc_88 : location_info := LocationInfo file_0 61 29 61 31.
  Definition loc_93 : location_info := LocationInfo file_0 76 2 76 12.
  Definition loc_94 : location_info := LocationInfo file_0 77 2 77 12.
  Definition loc_95 : location_info := LocationInfo file_0 78 2 78 30.
  Definition loc_96 : location_info := LocationInfo file_0 79 2 79 30.
  Definition loc_97 : location_info := LocationInfo file_0 81 2 82 18.
  Definition loc_98 : location_info := LocationInfo file_0 84 2 85 43.
  Definition loc_99 : location_info := LocationInfo file_0 84 13 84 49.
  Definition loc_100 : location_info := LocationInfo file_0 84 15 84 31.
  Definition loc_101 : location_info := LocationInfo file_0 84 32 84 47.
  Definition loc_102 : location_info := LocationInfo file_0 84 39 84 45.
  Definition loc_103 : location_info := LocationInfo file_0 84 39 84 40.
  Definition loc_104 : location_info := LocationInfo file_0 84 39 84 40.
  Definition loc_105 : location_info := LocationInfo file_0 84 44 84 45.
  Definition loc_106 : location_info := LocationInfo file_0 84 22 84 29.
  Definition loc_107 : location_info := LocationInfo file_0 84 22 84 23.
  Definition loc_108 : location_info := LocationInfo file_0 84 22 84 23.
  Definition loc_109 : location_info := LocationInfo file_0 84 27 84 29.
  Definition loc_110 : location_info := LocationInfo file_0 85 7 85 43.
  Definition loc_111 : location_info := LocationInfo file_0 85 9 85 25.
  Definition loc_112 : location_info := LocationInfo file_0 85 26 85 41.
  Definition loc_113 : location_info := LocationInfo file_0 85 33 85 39.
  Definition loc_114 : location_info := LocationInfo file_0 85 33 85 34.
  Definition loc_115 : location_info := LocationInfo file_0 85 33 85 34.
  Definition loc_116 : location_info := LocationInfo file_0 85 38 85 39.
  Definition loc_117 : location_info := LocationInfo file_0 85 16 85 23.
  Definition loc_118 : location_info := LocationInfo file_0 85 16 85 17.
  Definition loc_119 : location_info := LocationInfo file_0 85 16 85 17.
  Definition loc_120 : location_info := LocationInfo file_0 85 21 85 23.
  Definition loc_121 : location_info := LocationInfo file_0 84 6 84 11.
  Definition loc_122 : location_info := LocationInfo file_0 84 6 84 7.
  Definition loc_123 : location_info := LocationInfo file_0 84 6 84 7.
  Definition loc_124 : location_info := LocationInfo file_0 84 10 84 11.
  Definition loc_125 : location_info := LocationInfo file_0 84 10 84 11.
  Definition loc_126 : location_info := LocationInfo file_0 81 13 81 24.
  Definition loc_127 : location_info := LocationInfo file_0 81 15 81 22.
  Definition loc_128 : location_info := LocationInfo file_0 81 15 81 16.
  Definition loc_129 : location_info := LocationInfo file_0 81 19 81 21.
  Definition loc_130 : location_info := LocationInfo file_0 82 7 82 18.
  Definition loc_131 : location_info := LocationInfo file_0 82 9 82 16.
  Definition loc_132 : location_info := LocationInfo file_0 82 9 82 10.
  Definition loc_133 : location_info := LocationInfo file_0 82 13 82 15.
  Definition loc_134 : location_info := LocationInfo file_0 81 6 81 11.
  Definition loc_135 : location_info := LocationInfo file_0 81 6 81 7.
  Definition loc_136 : location_info := LocationInfo file_0 81 6 81 7.
  Definition loc_137 : location_info := LocationInfo file_0 81 10 81 11.
  Definition loc_138 : location_info := LocationInfo file_0 81 10 81 11.
  Definition loc_139 : location_info := LocationInfo file_0 79 16 79 29.
  Definition loc_140 : location_info := LocationInfo file_0 79 27 79 29.
  Definition loc_141 : location_info := LocationInfo file_0 79 28 79 29.
  Definition loc_144 : location_info := LocationInfo file_0 78 16 78 29.
  Definition loc_145 : location_info := LocationInfo file_0 78 27 78 29.
  Definition loc_146 : location_info := LocationInfo file_0 78 28 78 29.
  Definition loc_149 : location_info := LocationInfo file_0 77 10 77 11.
  Definition loc_152 : location_info := LocationInfo file_0 76 10 76 11.
  Definition loc_157 : location_info := LocationInfo file_0 95 2 95 30.
  Definition loc_158 : location_info := LocationInfo file_0 96 2 96 22.
  Definition loc_159 : location_info := LocationInfo file_0 97 2 97 11.
  Definition loc_160 : location_info := LocationInfo file_0 97 9 97 10.
  Definition loc_161 : location_info := LocationInfo file_0 97 9 97 10.
  Definition loc_162 : location_info := LocationInfo file_0 96 12 96 21.
  Definition loc_163 : location_info := LocationInfo file_0 96 20 96 21.
  Definition loc_164 : location_info := LocationInfo file_0 96 20 96 21.
  Definition loc_167 : location_info := LocationInfo file_0 95 16 95 29.
  Definition loc_168 : location_info := LocationInfo file_0 95 28 95 29.
  Definition loc_169 : location_info := LocationInfo file_0 95 28 95 29.
  Definition loc_174 : location_info := LocationInfo file_0 106 2 106 30.
  Definition loc_175 : location_info := LocationInfo file_0 107 2 107 28.
  Definition loc_176 : location_info := LocationInfo file_0 108 2 108 11.
  Definition loc_177 : location_info := LocationInfo file_0 108 9 108 10.
  Definition loc_178 : location_info := LocationInfo file_0 108 9 108 10.
  Definition loc_179 : location_info := LocationInfo file_0 107 12 107 27.
  Definition loc_180 : location_info := LocationInfo file_0 107 20 107 27.
  Definition loc_181 : location_info := LocationInfo file_0 107 21 107 22.
  Definition loc_182 : location_info := LocationInfo file_0 107 21 107 22.
  Definition loc_183 : location_info := LocationInfo file_0 107 25 107 26.
  Definition loc_186 : location_info := LocationInfo file_0 106 16 106 29.
  Definition loc_187 : location_info := LocationInfo file_0 106 28 106 29.
  Definition loc_188 : location_info := LocationInfo file_0 106 28 106 29.
  Definition loc_193 : location_info := LocationInfo file_0 116 2 116 30.
  Definition loc_194 : location_info := LocationInfo file_0 117 2 117 22.
  Definition loc_195 : location_info := LocationInfo file_0 118 2 118 43.
  Definition loc_196 : location_info := LocationInfo file_0 118 9 118 42.
  Definition loc_197 : location_info := LocationInfo file_0 118 9 118 32.
  Definition loc_198 : location_info := LocationInfo file_0 118 33 118 36.
  Definition loc_199 : location_info := LocationInfo file_0 118 33 118 36.
  Definition loc_200 : location_info := LocationInfo file_0 118 38 118 41.
  Definition loc_201 : location_info := LocationInfo file_0 118 38 118 41.
  Definition loc_202 : location_info := LocationInfo file_0 117 16 117 21.
  Definition loc_203 : location_info := LocationInfo file_0 117 16 117 17.
  Definition loc_204 : location_info := LocationInfo file_0 117 16 117 17.
  Definition loc_205 : location_info := LocationInfo file_0 117 20 117 21.
  Definition loc_208 : location_info := LocationInfo file_0 116 16 116 29.
  Definition loc_209 : location_info := LocationInfo file_0 116 28 116 29.
  Definition loc_210 : location_info := LocationInfo file_0 116 28 116 29.
  Definition loc_215 : location_info := LocationInfo file_0 127 2 127 30.
  Definition loc_216 : location_info := LocationInfo file_0 128 2 128 20.
  Definition loc_217 : location_info := LocationInfo file_0 129 2 129 13.
  Definition loc_218 : location_info := LocationInfo file_0 130 2 130 11.
  Definition loc_219 : location_info := LocationInfo file_0 130 9 130 10.
  Definition loc_220 : location_info := LocationInfo file_0 130 9 130 10.
  Definition loc_221 : location_info := LocationInfo file_0 129 10 129 12.
  Definition loc_222 : location_info := LocationInfo file_0 129 10 129 12.
  Definition loc_223 : location_info := LocationInfo file_0 129 11 129 12.
  Definition loc_224 : location_info := LocationInfo file_0 129 11 129 12.
  Definition loc_227 : location_info := LocationInfo file_0 128 11 128 19.
  Definition loc_228 : location_info := LocationInfo file_0 128 18 128 19.
  Definition loc_229 : location_info := LocationInfo file_0 128 18 128 19.
  Definition loc_232 : location_info := LocationInfo file_0 127 16 127 29.
  Definition loc_233 : location_info := LocationInfo file_0 127 28 127 29.
  Definition loc_234 : location_info := LocationInfo file_0 127 28 127 29.
  Definition loc_239 : location_info := LocationInfo file_0 139 2 139 30.
  Definition loc_240 : location_info := LocationInfo file_0 140 2 140 22.
  Definition loc_241 : location_info := LocationInfo file_0 141 2 141 52.
  Definition loc_242 : location_info := LocationInfo file_0 142 2 142 13.
  Definition loc_243 : location_info := LocationInfo file_0 143 2 143 11.
  Definition loc_244 : location_info := LocationInfo file_0 143 9 143 10.
  Definition loc_245 : location_info := LocationInfo file_0 143 9 143 10.
  Definition loc_246 : location_info := LocationInfo file_0 142 10 142 12.
  Definition loc_247 : location_info := LocationInfo file_0 142 10 142 12.
  Definition loc_248 : location_info := LocationInfo file_0 142 11 142 12.
  Definition loc_249 : location_info := LocationInfo file_0 142 11 142 12.
  Definition loc_252 : location_info := LocationInfo file_0 141 11 141 51.
  Definition loc_253 : location_info := LocationInfo file_0 141 18 141 51.
  Definition loc_254 : location_info := LocationInfo file_0 141 18 141 41.
  Definition loc_255 : location_info := LocationInfo file_0 141 42 141 45.
  Definition loc_256 : location_info := LocationInfo file_0 141 42 141 45.
  Definition loc_257 : location_info := LocationInfo file_0 141 47 141 50.
  Definition loc_258 : location_info := LocationInfo file_0 141 47 141 50.
  Definition loc_261 : location_info := LocationInfo file_0 140 16 140 21.
  Definition loc_262 : location_info := LocationInfo file_0 140 16 140 17.
  Definition loc_263 : location_info := LocationInfo file_0 140 16 140 17.
  Definition loc_264 : location_info := LocationInfo file_0 140 20 140 21.
  Definition loc_267 : location_info := LocationInfo file_0 139 16 139 29.
  Definition loc_268 : location_info := LocationInfo file_0 139 28 139 29.
  Definition loc_269 : location_info := LocationInfo file_0 139 28 139 29.
  Definition loc_274 : location_info := LocationInfo file_0 152 2 152 30.
  Definition loc_275 : location_info := LocationInfo file_0 153 2 153 56.
  Definition loc_276 : location_info := LocationInfo file_0 154 2 154 12.
  Definition loc_277 : location_info := LocationInfo file_0 154 9 154 11.
  Definition loc_278 : location_info := LocationInfo file_0 154 9 154 11.
  Definition loc_279 : location_info := LocationInfo file_0 154 10 154 11.
  Definition loc_280 : location_info := LocationInfo file_0 154 10 154 11.
  Definition loc_281 : location_info := LocationInfo file_0 153 11 153 55.
  Definition loc_282 : location_info := LocationInfo file_0 153 18 153 55.
  Definition loc_283 : location_info := LocationInfo file_0 153 18 153 41.
  Definition loc_284 : location_info := LocationInfo file_0 153 42 153 49.
  Definition loc_285 : location_info := LocationInfo file_0 153 43 153 44.
  Definition loc_286 : location_info := LocationInfo file_0 153 43 153 44.
  Definition loc_287 : location_info := LocationInfo file_0 153 47 153 48.
  Definition loc_288 : location_info := LocationInfo file_0 153 51 153 54.
  Definition loc_289 : location_info := LocationInfo file_0 153 51 153 54.
  Definition loc_292 : location_info := LocationInfo file_0 152 16 152 29.
  Definition loc_293 : location_info := LocationInfo file_0 152 28 152 29.
  Definition loc_294 : location_info := LocationInfo file_0 152 28 152 29.
  Definition loc_299 : location_info := LocationInfo file_0 163 2 163 30.
  Definition loc_300 : location_info := LocationInfo file_0 164 2 164 22.
  Definition loc_301 : location_info := LocationInfo file_0 165 2 165 52.
  Definition loc_302 : location_info := LocationInfo file_0 166 2 166 12.
  Definition loc_303 : location_info := LocationInfo file_0 166 9 166 11.
  Definition loc_304 : location_info := LocationInfo file_0 166 9 166 11.
  Definition loc_305 : location_info := LocationInfo file_0 166 10 166 11.
  Definition loc_306 : location_info := LocationInfo file_0 166 10 166 11.
  Definition loc_307 : location_info := LocationInfo file_0 165 11 165 51.
  Definition loc_308 : location_info := LocationInfo file_0 165 18 165 51.
  Definition loc_309 : location_info := LocationInfo file_0 165 18 165 41.
  Definition loc_310 : location_info := LocationInfo file_0 165 42 165 45.
  Definition loc_311 : location_info := LocationInfo file_0 165 42 165 45.
  Definition loc_312 : location_info := LocationInfo file_0 165 47 165 50.
  Definition loc_313 : location_info := LocationInfo file_0 165 47 165 50.
  Definition loc_316 : location_info := LocationInfo file_0 164 16 164 21.
  Definition loc_317 : location_info := LocationInfo file_0 164 16 164 17.
  Definition loc_318 : location_info := LocationInfo file_0 164 16 164 17.
  Definition loc_319 : location_info := LocationInfo file_0 164 20 164 21.
  Definition loc_322 : location_info := LocationInfo file_0 163 16 163 29.
  Definition loc_323 : location_info := LocationInfo file_0 163 28 163 29.
  Definition loc_324 : location_info := LocationInfo file_0 163 28 163 29.
  Definition loc_329 : location_info := LocationInfo file_0 172 2 172 11.
  Definition loc_330 : location_info := LocationInfo file_0 173 2 173 17.
  Definition loc_331 : location_info := LocationInfo file_0 174 2 174 36.
  Definition loc_332 : location_info := LocationInfo file_0 175 2 175 12.
  Definition loc_333 : location_info := LocationInfo file_0 175 9 175 11.
  Definition loc_334 : location_info := LocationInfo file_0 175 9 175 11.
  Definition loc_335 : location_info := LocationInfo file_0 175 10 175 11.
  Definition loc_336 : location_info := LocationInfo file_0 175 10 175 11.
  Definition loc_337 : location_info := LocationInfo file_0 174 11 174 35.
  Definition loc_338 : location_info := LocationInfo file_0 174 11 174 31.
  Definition loc_339 : location_info := LocationInfo file_0 174 17 174 31.
  Definition loc_340 : location_info := LocationInfo file_0 174 29 174 30.
  Definition loc_341 : location_info := LocationInfo file_0 174 29 174 30.
  Definition loc_342 : location_info := LocationInfo file_0 174 34 174 35.
  Definition loc_345 : location_info := LocationInfo file_0 173 11 173 16.
  Definition loc_346 : location_info := LocationInfo file_0 173 11 173 12.
  Definition loc_347 : location_info := LocationInfo file_0 173 11 173 12.
  Definition loc_348 : location_info := LocationInfo file_0 173 15 173 16.
  Definition loc_351 : location_info := LocationInfo file_0 172 2 172 6.
  Definition loc_352 : location_info := LocationInfo file_0 172 2 172 6.
  Definition loc_353 : location_info := LocationInfo file_0 172 2 172 3.
  Definition loc_354 : location_info := LocationInfo file_0 172 2 172 3.
  Definition loc_355 : location_info := LocationInfo file_0 172 4 172 5.
  Definition loc_356 : location_info := LocationInfo file_0 172 9 172 10.
  Definition loc_359 : location_info := LocationInfo file_0 182 2 182 30.
  Definition loc_360 : location_info := LocationInfo file_0 182 9 182 29.
  Definition loc_361 : location_info := LocationInfo file_0 182 15 182 29.

  (* Definition of function [int_ptr1]. *)
  Definition impl_int_ptr1 : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout uintptr_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_6 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_7 (use{void*} (LocInfoE loc_8 ("p"))))) ;
        locinfo: loc_3 ;
        Return (LocInfoE loc_4 (use{it_layout uintptr_t} (LocInfoE loc_5 ("i"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [int_ptr2]. *)
  Definition impl_int_ptr2 : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout uintptr_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_17 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_18 (use{void*} (LocInfoE loc_19 ("p"))))) ;
        locinfo: loc_14 ;
        Return (LocInfoE loc_15 (use{it_layout uintptr_t} (LocInfoE loc_16 ("i"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [int_ptr3]. *)
  Definition impl_int_ptr3 : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout uintptr_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_30 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_31 (use{void*} (LocInfoE loc_32 ("p"))))) ;
        locinfo: loc_25 ;
        Return (LocInfoE loc_26 ((LocInfoE loc_27 (use{it_layout uintptr_t} (LocInfoE loc_28 ("i")))) +{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_29 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_29 (i2v 0 i32))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [min_ptr_val1]. *)
  Definition impl_min_ptr_val1 : function := {|
    f_args := [
      ("p1", void*);
      ("p2", void*)
    ];
    f_local_vars := [
      ("i2", it_layout uintptr_t);
      ("i1", it_layout uintptr_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i1" <-{ it_layout uintptr_t }
          LocInfoE loc_58 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_59 (use{void*} (LocInfoE loc_60 ("p1"))))) ;
        "i2" <-{ it_layout uintptr_t }
          LocInfoE loc_53 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_54 (use{void*} (LocInfoE loc_55 ("p2"))))) ;
        locinfo: loc_48 ;
        if: LocInfoE loc_48 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_48 ((LocInfoE loc_49 (use{it_layout uintptr_t} (LocInfoE loc_50 ("i1")))) ≤{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_51 (use{it_layout uintptr_t} (LocInfoE loc_52 ("i2")))))))
        then
        locinfo: loc_44 ;
          Goto "#2"
        else
        locinfo: loc_40 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_40 ;
        Return (LocInfoE loc_41 (use{it_layout uintptr_t} (LocInfoE loc_42 ("i2"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_44 ;
        Return (LocInfoE loc_45 (use{it_layout uintptr_t} (LocInfoE loc_46 ("i1"))))
      ]> $
      <[ "#3" :=
        locinfo: loc_40 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [min_ptr_val2]. *)
  Definition impl_min_ptr_val2 : function := {|
    f_args := [
      ("p1", void*);
      ("p2", void*)
    ];
    f_local_vars := [
      ("i2", it_layout uintptr_t);
      ("i1", it_layout uintptr_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i1" <-{ it_layout uintptr_t }
          LocInfoE loc_86 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_87 (use{void*} (LocInfoE loc_88 ("p1"))))) ;
        "i2" <-{ it_layout uintptr_t }
          LocInfoE loc_81 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_82 (use{void*} (LocInfoE loc_83 ("p2"))))) ;
        locinfo: loc_76 ;
        if: LocInfoE loc_76 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_76 ((LocInfoE loc_77 (use{it_layout uintptr_t} (LocInfoE loc_78 ("i1")))) ≤{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_79 (use{it_layout uintptr_t} (LocInfoE loc_80 ("i2")))))))
        then
        locinfo: loc_72 ;
          Goto "#2"
        else
        locinfo: loc_68 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_68 ;
        Return (LocInfoE loc_69 (use{it_layout uintptr_t} (LocInfoE loc_70 ("i2"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_72 ;
        Return (LocInfoE loc_73 (use{it_layout uintptr_t} (LocInfoE loc_74 ("i1"))))
      ]> $
      <[ "#3" :=
        locinfo: loc_68 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [pointer_to_integer_comp_det]. *)
  Definition impl_pointer_to_integer_comp_det : function := {|
    f_args := [
    ];
    f_local_vars := [
      ("i", it_layout uintptr_t);
      ("x", it_layout i32);
      ("y", it_layout i32);
      ("j", it_layout uintptr_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "x" <-{ it_layout i32 } LocInfoE loc_152 (i2v 0 i32) ;
        "y" <-{ it_layout i32 } LocInfoE loc_149 (i2v 0 i32) ;
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_144 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_145 (&(LocInfoE loc_146 ("x"))))) ;
        "j" <-{ it_layout uintptr_t }
          LocInfoE loc_139 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_140 (&(LocInfoE loc_141 ("y"))))) ;
        locinfo: loc_134 ;
        if: LocInfoE loc_134 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_134 ((LocInfoE loc_135 (use{it_layout uintptr_t} (LocInfoE loc_136 ("i")))) <{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_137 (use{it_layout uintptr_t} (LocInfoE loc_138 ("j")))))))
        then
        locinfo: loc_127 ;
          Goto "#4"
        else
        locinfo: loc_131 ;
          Goto "#5"
      ]> $
      <[ "#1" :=
        locinfo: loc_121 ;
        if: LocInfoE loc_121 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_121 ((LocInfoE loc_122 (use{it_layout uintptr_t} (LocInfoE loc_123 ("i")))) <{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_124 (use{it_layout uintptr_t} (LocInfoE loc_125 ("j")))))))
        then
        locinfo: loc_100 ;
          Goto "#2"
        else
        locinfo: loc_111 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_100 ;
        assert: (LocInfoE loc_106 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_106 ((LocInfoE loc_107 (use{it_layout i32} (LocInfoE loc_108 ("y")))) ={IntOp i32, IntOp i32} (LocInfoE loc_109 (i2v 10 i32)))))) ;
        locinfo: loc_101 ;
        assert: (LocInfoE loc_102 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_102 ((LocInfoE loc_103 (use{it_layout i32} (LocInfoE loc_104 ("x")))) ={IntOp i32, IntOp i32} (LocInfoE loc_105 (i2v 0 i32)))))) ;
        Return (VOID)
      ]> $
      <[ "#3" :=
        locinfo: loc_111 ;
        assert: (LocInfoE loc_117 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_117 ((LocInfoE loc_118 (use{it_layout i32} (LocInfoE loc_119 ("x")))) ={IntOp i32, IntOp i32} (LocInfoE loc_120 (i2v 10 i32)))))) ;
        locinfo: loc_112 ;
        assert: (LocInfoE loc_113 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_113 ((LocInfoE loc_114 (use{it_layout i32} (LocInfoE loc_115 ("y")))) ={IntOp i32, IntOp i32} (LocInfoE loc_116 (i2v 0 i32)))))) ;
        Return (VOID)
      ]> $
      <[ "#4" :=
        locinfo: loc_127 ;
        LocInfoE loc_128 ("y") <-{ it_layout i32 }
          LocInfoE loc_129 (i2v 10 i32) ;
        locinfo: loc_121 ;
        Goto "#1"
      ]> $
      <[ "#5" :=
        locinfo: loc_131 ;
        LocInfoE loc_132 ("x") <-{ it_layout i32 }
          LocInfoE loc_133 (i2v 10 i32) ;
        locinfo: loc_121 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip1]. *)
  Definition impl_roundtrip1 : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout uintptr_t);
      ("q", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_167 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_168 (use{void*} (LocInfoE loc_169 ("p"))))) ;
        "q" <-{ void* }
          LocInfoE loc_162 (UnOp (CastOp $ PtrOp) (IntOp uintptr_t) (LocInfoE loc_163 (use{it_layout uintptr_t} (LocInfoE loc_164 ("i"))))) ;
        locinfo: loc_159 ;
        Return (LocInfoE loc_160 (use{void*} (LocInfoE loc_161 ("q"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip2]. *)
  Definition impl_roundtrip2 : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout uintptr_t);
      ("q", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_186 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_187 (use{void*} (LocInfoE loc_188 ("p"))))) ;
        "q" <-{ void* }
          LocInfoE loc_179 (UnOp (CastOp $ PtrOp) (IntOp uintptr_t) (LocInfoE loc_180 ((LocInfoE loc_181 (use{it_layout uintptr_t} (LocInfoE loc_182 ("i")))) +{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_183 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_183 (i2v 0 i32))))))) ;
        locinfo: loc_176 ;
        Return (LocInfoE loc_177 (use{void*} (LocInfoE loc_178 ("q"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip3]. *)
  Definition impl_roundtrip3 : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout uintptr_t);
      ("k", it_layout uintptr_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_208 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_209 (use{void*} (LocInfoE loc_210 ("p"))))) ;
        "k" <-{ it_layout uintptr_t }
          LocInfoE loc_202 ((LocInfoE loc_203 (use{it_layout uintptr_t} (LocInfoE loc_204 ("i")))) +{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_205 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_205 (i2v 0 i32))))) ;
        locinfo: loc_195 ;
        Return (LocInfoE loc_196 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_198 (use{it_layout uintptr_t} (LocInfoE loc_199 ("k")))) (LocInfoE loc_200 (use{void*} (LocInfoE loc_201 ("p"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip_and_read1]. *)
  Definition impl_roundtrip_and_read1 : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout uintptr_t);
      ("r", it_layout i32);
      ("q", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_232 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_233 (use{void*} (LocInfoE loc_234 ("p"))))) ;
        "q" <-{ void* }
          LocInfoE loc_227 (UnOp (CastOp $ PtrOp) (IntOp uintptr_t) (LocInfoE loc_228 (use{it_layout uintptr_t} (LocInfoE loc_229 ("i"))))) ;
        "r" <-{ it_layout i32 }
          LocInfoE loc_221 (use{it_layout i32} (LocInfoE loc_223 (!{void*} (LocInfoE loc_224 ("q"))))) ;
        locinfo: loc_218 ;
        Return (LocInfoE loc_219 (use{it_layout i32} (LocInfoE loc_220 ("r"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip_and_read2]. *)
  Definition impl_roundtrip_and_read2 : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout uintptr_t);
      ("r", it_layout i32);
      ("q", void*);
      ("j", it_layout uintptr_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_267 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_268 (use{void*} (LocInfoE loc_269 ("p"))))) ;
        "j" <-{ it_layout uintptr_t }
          LocInfoE loc_261 ((LocInfoE loc_262 (use{it_layout uintptr_t} (LocInfoE loc_263 ("i")))) ×{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_264 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_264 (i2v 1 i32))))) ;
        "q" <-{ void* }
          LocInfoE loc_252 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_253 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_255 (use{it_layout uintptr_t} (LocInfoE loc_256 ("j")))) (LocInfoE loc_257 (use{void*} (LocInfoE loc_258 ("p"))))))) ;
        "r" <-{ it_layout i32 }
          LocInfoE loc_246 (use{it_layout i32} (LocInfoE loc_248 (!{void*} (LocInfoE loc_249 ("q"))))) ;
        locinfo: loc_243 ;
        Return (LocInfoE loc_244 (use{it_layout i32} (LocInfoE loc_245 ("r"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip_and_read3]. *)
  Definition impl_roundtrip_and_read3 : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout uintptr_t);
      ("q", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_292 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_293 (use{void*} (LocInfoE loc_294 ("p"))))) ;
        "q" <-{ void* }
          LocInfoE loc_281 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_282 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_284 ((LocInfoE loc_285 (use{it_layout uintptr_t} (LocInfoE loc_286 ("i")))) ×{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_287 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_287 (i2v 1 i32)))))) (LocInfoE loc_288 (use{void*} (LocInfoE loc_289 ("p"))))))) ;
        locinfo: loc_276 ;
        Return (LocInfoE loc_277 (use{it_layout i32} (LocInfoE loc_279 (!{void*} (LocInfoE loc_280 ("q"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip_and_read4]. *)
  Definition impl_roundtrip_and_read4 : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout uintptr_t);
      ("q", void*);
      ("j", it_layout uintptr_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_322 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_323 (use{void*} (LocInfoE loc_324 ("p"))))) ;
        "j" <-{ it_layout uintptr_t }
          LocInfoE loc_316 ((LocInfoE loc_317 (use{it_layout uintptr_t} (LocInfoE loc_318 ("i")))) ×{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_319 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_319 (i2v 1 i32))))) ;
        "q" <-{ void* }
          LocInfoE loc_307 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_308 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_310 (use{it_layout uintptr_t} (LocInfoE loc_311 ("j")))) (LocInfoE loc_312 (use{void*} (LocInfoE loc_313 ("p"))))))) ;
        locinfo: loc_302 ;
        Return (LocInfoE loc_303 (use{it_layout i32} (LocInfoE loc_305 (!{void*} (LocInfoE loc_306 ("q"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip_and_read_past_the_end]. *)
  Definition impl_roundtrip_and_read_past_the_end : function := {|
    f_args := [
    ];
    f_local_vars := [
      ("x", mk_array_layout (it_layout i32) 1);
      ("q", void*);
      ("p", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_329 ;
        LocInfoE loc_352 ((LocInfoE loc_354 ("x")) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_355 (i2v 0 i32))) <-{ it_layout i32 }
          LocInfoE loc_356 (i2v 0 i32) ;
        "p" <-{ void* }
          LocInfoE loc_345 ((LocInfoE loc_346 (&(LocInfoE loc_347 ("x")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_348 (i2v 1 i32))) ;
        "q" <-{ void* }
          LocInfoE loc_337 ((LocInfoE loc_338 (UnOp (CastOp $ PtrOp) (IntOp uintptr_t) (LocInfoE loc_339 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_340 (use{void*} (LocInfoE loc_341 ("p")))))))) at_neg_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_342 (i2v 1 i32))) ;
        locinfo: loc_332 ;
        Return (LocInfoE loc_333 (use{it_layout i32} (LocInfoE loc_335 (!{void*} (LocInfoE loc_336 ("q"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [cast_NULL]. *)
  Definition impl_cast_NULL : function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_359 ;
        Return (LocInfoE loc_360 (UnOp (CastOp $ IntOp i32) (PtrOp) (LocInfoE loc_361 (NULL))))
      ]> $∅
    )%E
  |}.
End code.
