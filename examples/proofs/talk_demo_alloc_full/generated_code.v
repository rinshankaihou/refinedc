From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/talk_demo_alloc_full.c]. *)
Section code.
  Definition file_0 : string := "examples/talk_demo_alloc_full.c".
  Definition file_1 : string := "include/refinedc.h".
  Definition loc_2 : location_info := LocationInfo file_1 63 2 63 47.
  Definition loc_3 : location_info := LocationInfo file_1 63 9 63 46.
  Definition loc_4 : location_info := LocationInfo file_1 63 9 63 32.
  Definition loc_5 : location_info := LocationInfo file_1 63 33 63 37.
  Definition loc_6 : location_info := LocationInfo file_1 63 33 63 37.
  Definition loc_7 : location_info := LocationInfo file_1 63 39 63 45.
  Definition loc_8 : location_info := LocationInfo file_1 63 39 63 45.
  Definition loc_11 : location_info := LocationInfo file_0 29 2 29 40.
  Definition loc_12 : location_info := LocationInfo file_0 30 2 30 15.
  Definition loc_13 : location_info := LocationInfo file_0 31 2 31 28.
  Definition loc_14 : location_info := LocationInfo file_0 31 9 31 27.
  Definition loc_15 : location_info := LocationInfo file_0 31 9 31 18.
  Definition loc_16 : location_info := LocationInfo file_0 31 9 31 18.
  Definition loc_17 : location_info := LocationInfo file_0 31 9 31 10.
  Definition loc_18 : location_info := LocationInfo file_0 31 9 31 10.
  Definition loc_19 : location_info := LocationInfo file_0 31 21 31 27.
  Definition loc_20 : location_info := LocationInfo file_0 31 21 31 27.
  Definition loc_21 : location_info := LocationInfo file_0 31 21 31 22.
  Definition loc_22 : location_info := LocationInfo file_0 31 21 31 22.
  Definition loc_23 : location_info := LocationInfo file_0 30 2 30 8.
  Definition loc_24 : location_info := LocationInfo file_0 30 2 30 3.
  Definition loc_25 : location_info := LocationInfo file_0 30 2 30 3.
  Definition loc_26 : location_info := LocationInfo file_0 30 2 30 14.
  Definition loc_27 : location_info := LocationInfo file_0 30 2 30 8.
  Definition loc_28 : location_info := LocationInfo file_0 30 2 30 8.
  Definition loc_29 : location_info := LocationInfo file_0 30 2 30 3.
  Definition loc_30 : location_info := LocationInfo file_0 30 2 30 3.
  Definition loc_31 : location_info := LocationInfo file_0 30 12 30 14.
  Definition loc_32 : location_info := LocationInfo file_0 30 12 30 14.
  Definition loc_33 : location_info := LocationInfo file_0 29 18 29 40.
  Definition loc_34 : location_info := LocationInfo file_0 29 25 29 39.
  Definition loc_35 : location_info := LocationInfo file_0 29 2 29 40.
  Definition loc_36 : location_info := LocationInfo file_0 29 5 29 16.
  Definition loc_37 : location_info := LocationInfo file_0 29 5 29 7.
  Definition loc_38 : location_info := LocationInfo file_0 29 5 29 7.
  Definition loc_39 : location_info := LocationInfo file_0 29 10 29 16.
  Definition loc_40 : location_info := LocationInfo file_0 29 10 29 16.
  Definition loc_41 : location_info := LocationInfo file_0 29 10 29 11.
  Definition loc_42 : location_info := LocationInfo file_0 29 10 29 11.
  Definition loc_45 : location_info := LocationInfo file_0 38 2 38 40.
  Definition loc_46 : location_info := LocationInfo file_0 39 2 39 15.
  Definition loc_47 : location_info := LocationInfo file_0 40 2 40 28.
  Definition loc_48 : location_info := LocationInfo file_0 40 9 40 27.
  Definition loc_49 : location_info := LocationInfo file_0 40 9 40 18.
  Definition loc_50 : location_info := LocationInfo file_0 40 9 40 18.
  Definition loc_51 : location_info := LocationInfo file_0 40 9 40 10.
  Definition loc_52 : location_info := LocationInfo file_0 40 9 40 10.
  Definition loc_53 : location_info := LocationInfo file_0 40 21 40 27.
  Definition loc_54 : location_info := LocationInfo file_0 40 21 40 27.
  Definition loc_55 : location_info := LocationInfo file_0 40 21 40 22.
  Definition loc_56 : location_info := LocationInfo file_0 40 21 40 22.
  Definition loc_57 : location_info := LocationInfo file_0 39 2 39 8.
  Definition loc_58 : location_info := LocationInfo file_0 39 2 39 3.
  Definition loc_59 : location_info := LocationInfo file_0 39 2 39 3.
  Definition loc_60 : location_info := LocationInfo file_0 39 2 39 14.
  Definition loc_61 : location_info := LocationInfo file_0 39 2 39 8.
  Definition loc_62 : location_info := LocationInfo file_0 39 2 39 8.
  Definition loc_63 : location_info := LocationInfo file_0 39 2 39 3.
  Definition loc_64 : location_info := LocationInfo file_0 39 2 39 3.
  Definition loc_65 : location_info := LocationInfo file_0 39 12 39 14.
  Definition loc_66 : location_info := LocationInfo file_0 39 12 39 14.
  Definition loc_67 : location_info := LocationInfo file_0 38 18 38 40.
  Definition loc_68 : location_info := LocationInfo file_0 38 25 38 39.
  Definition loc_69 : location_info := LocationInfo file_0 38 2 38 40.
  Definition loc_70 : location_info := LocationInfo file_0 38 5 38 16.
  Definition loc_71 : location_info := LocationInfo file_0 38 5 38 7.
  Definition loc_72 : location_info := LocationInfo file_0 38 5 38 7.
  Definition loc_73 : location_info := LocationInfo file_0 38 10 38 16.
  Definition loc_74 : location_info := LocationInfo file_0 38 10 38 16.
  Definition loc_75 : location_info := LocationInfo file_0 38 10 38 11.
  Definition loc_76 : location_info := LocationInfo file_0 38 10 38 11.
  Definition loc_79 : location_info := LocationInfo file_0 47 2 47 48.
  Definition loc_80 : location_info := LocationInfo file_0 48 2 48 37.
  Definition loc_81 : location_info := LocationInfo file_0 49 2 49 11.
  Definition loc_82 : location_info := LocationInfo file_0 49 2 49 6.
  Definition loc_83 : location_info := LocationInfo file_0 49 2 49 3.
  Definition loc_84 : location_info := LocationInfo file_0 49 2 49 3.
  Definition loc_85 : location_info := LocationInfo file_0 49 9 49 10.
  Definition loc_86 : location_info := LocationInfo file_0 48 26 48 37.
  Definition loc_87 : location_info := LocationInfo file_0 48 28 48 35.
  Definition loc_89 : location_info := LocationInfo file_0 48 2 48 37.
  Definition loc_90 : location_info := LocationInfo file_0 48 5 48 24.
  Definition loc_91 : location_info := LocationInfo file_0 48 5 48 6.
  Definition loc_92 : location_info := LocationInfo file_0 48 5 48 6.
  Definition loc_93 : location_info := LocationInfo file_0 48 10 48 24.
  Definition loc_94 : location_info := LocationInfo file_0 47 18 47 47.
  Definition loc_95 : location_info := LocationInfo file_0 47 18 47 25.
  Definition loc_96 : location_info := LocationInfo file_0 47 18 47 25.
  Definition loc_97 : location_info := LocationInfo file_0 47 26 47 27.
  Definition loc_98 : location_info := LocationInfo file_0 47 26 47 27.
  Definition loc_99 : location_info := LocationInfo file_0 47 29 47 46.
  Definition loc_104 : location_info := LocationInfo file_0 58 2 58 40.
  Definition loc_105 : location_info := LocationInfo file_0 59 2 59 15.
  Definition loc_106 : location_info := LocationInfo file_0 60 2 60 28.
  Definition loc_107 : location_info := LocationInfo file_0 60 9 60 27.
  Definition loc_108 : location_info := LocationInfo file_0 60 9 60 18.
  Definition loc_109 : location_info := LocationInfo file_0 60 9 60 18.
  Definition loc_110 : location_info := LocationInfo file_0 60 9 60 10.
  Definition loc_111 : location_info := LocationInfo file_0 60 9 60 10.
  Definition loc_112 : location_info := LocationInfo file_0 60 21 60 27.
  Definition loc_113 : location_info := LocationInfo file_0 60 21 60 27.
  Definition loc_114 : location_info := LocationInfo file_0 60 21 60 22.
  Definition loc_115 : location_info := LocationInfo file_0 60 21 60 22.
  Definition loc_116 : location_info := LocationInfo file_0 59 2 59 8.
  Definition loc_117 : location_info := LocationInfo file_0 59 2 59 3.
  Definition loc_118 : location_info := LocationInfo file_0 59 2 59 3.
  Definition loc_119 : location_info := LocationInfo file_0 59 2 59 14.
  Definition loc_120 : location_info := LocationInfo file_0 59 2 59 8.
  Definition loc_121 : location_info := LocationInfo file_0 59 2 59 8.
  Definition loc_122 : location_info := LocationInfo file_0 59 2 59 3.
  Definition loc_123 : location_info := LocationInfo file_0 59 2 59 3.
  Definition loc_124 : location_info := LocationInfo file_0 59 12 59 14.
  Definition loc_125 : location_info := LocationInfo file_0 59 12 59 14.
  Definition loc_126 : location_info := LocationInfo file_0 58 18 58 40.
  Definition loc_127 : location_info := LocationInfo file_0 58 25 58 39.
  Definition loc_128 : location_info := LocationInfo file_0 58 2 58 40.
  Definition loc_129 : location_info := LocationInfo file_0 58 5 58 16.
  Definition loc_130 : location_info := LocationInfo file_0 58 5 58 7.
  Definition loc_131 : location_info := LocationInfo file_0 58 5 58 7.
  Definition loc_132 : location_info := LocationInfo file_0 58 10 58 16.
  Definition loc_133 : location_info := LocationInfo file_0 58 10 58 16.
  Definition loc_134 : location_info := LocationInfo file_0 58 10 58 11.
  Definition loc_135 : location_info := LocationInfo file_0 58 10 58 11.
  Definition loc_138 : location_info := LocationInfo file_0 68 2 68 40.
  Definition loc_139 : location_info := LocationInfo file_0 69 2 69 15.
  Definition loc_140 : location_info := LocationInfo file_0 70 2 70 28.
  Definition loc_141 : location_info := LocationInfo file_0 70 9 70 27.
  Definition loc_142 : location_info := LocationInfo file_0 70 9 70 18.
  Definition loc_143 : location_info := LocationInfo file_0 70 9 70 18.
  Definition loc_144 : location_info := LocationInfo file_0 70 9 70 10.
  Definition loc_145 : location_info := LocationInfo file_0 70 9 70 10.
  Definition loc_146 : location_info := LocationInfo file_0 70 21 70 27.
  Definition loc_147 : location_info := LocationInfo file_0 70 21 70 27.
  Definition loc_148 : location_info := LocationInfo file_0 70 21 70 22.
  Definition loc_149 : location_info := LocationInfo file_0 70 21 70 22.
  Definition loc_150 : location_info := LocationInfo file_0 69 2 69 8.
  Definition loc_151 : location_info := LocationInfo file_0 69 2 69 3.
  Definition loc_152 : location_info := LocationInfo file_0 69 2 69 3.
  Definition loc_153 : location_info := LocationInfo file_0 69 2 69 14.
  Definition loc_154 : location_info := LocationInfo file_0 69 2 69 8.
  Definition loc_155 : location_info := LocationInfo file_0 69 2 69 8.
  Definition loc_156 : location_info := LocationInfo file_0 69 2 69 3.
  Definition loc_157 : location_info := LocationInfo file_0 69 2 69 3.
  Definition loc_158 : location_info := LocationInfo file_0 69 12 69 14.
  Definition loc_159 : location_info := LocationInfo file_0 69 12 69 14.
  Definition loc_160 : location_info := LocationInfo file_0 68 18 68 40.
  Definition loc_161 : location_info := LocationInfo file_0 68 25 68 39.
  Definition loc_162 : location_info := LocationInfo file_0 68 2 68 40.
  Definition loc_163 : location_info := LocationInfo file_0 68 5 68 16.
  Definition loc_164 : location_info := LocationInfo file_0 68 5 68 7.
  Definition loc_165 : location_info := LocationInfo file_0 68 5 68 7.
  Definition loc_166 : location_info := LocationInfo file_0 68 10 68 16.
  Definition loc_167 : location_info := LocationInfo file_0 68 10 68 16.
  Definition loc_168 : location_info := LocationInfo file_0 68 10 68 11.
  Definition loc_169 : location_info := LocationInfo file_0 68 10 68 11.
  Definition loc_172 : location_info := LocationInfo file_0 78 2 78 40.
  Definition loc_173 : location_info := LocationInfo file_0 79 2 79 15.
  Definition loc_174 : location_info := LocationInfo file_0 80 2 80 28.
  Definition loc_175 : location_info := LocationInfo file_0 80 9 80 27.
  Definition loc_176 : location_info := LocationInfo file_0 80 9 80 18.
  Definition loc_177 : location_info := LocationInfo file_0 80 9 80 18.
  Definition loc_178 : location_info := LocationInfo file_0 80 9 80 10.
  Definition loc_179 : location_info := LocationInfo file_0 80 9 80 10.
  Definition loc_180 : location_info := LocationInfo file_0 80 21 80 27.
  Definition loc_181 : location_info := LocationInfo file_0 80 21 80 27.
  Definition loc_182 : location_info := LocationInfo file_0 80 21 80 22.
  Definition loc_183 : location_info := LocationInfo file_0 80 21 80 22.
  Definition loc_184 : location_info := LocationInfo file_0 79 2 79 8.
  Definition loc_185 : location_info := LocationInfo file_0 79 2 79 3.
  Definition loc_186 : location_info := LocationInfo file_0 79 2 79 3.
  Definition loc_187 : location_info := LocationInfo file_0 79 2 79 14.
  Definition loc_188 : location_info := LocationInfo file_0 79 2 79 8.
  Definition loc_189 : location_info := LocationInfo file_0 79 2 79 8.
  Definition loc_190 : location_info := LocationInfo file_0 79 2 79 3.
  Definition loc_191 : location_info := LocationInfo file_0 79 2 79 3.
  Definition loc_192 : location_info := LocationInfo file_0 79 12 79 14.
  Definition loc_193 : location_info := LocationInfo file_0 79 12 79 14.
  Definition loc_194 : location_info := LocationInfo file_0 78 18 78 40.
  Definition loc_195 : location_info := LocationInfo file_0 78 25 78 39.
  Definition loc_196 : location_info := LocationInfo file_0 78 2 78 40.
  Definition loc_197 : location_info := LocationInfo file_0 78 5 78 16.
  Definition loc_198 : location_info := LocationInfo file_0 78 5 78 7.
  Definition loc_199 : location_info := LocationInfo file_0 78 5 78 7.
  Definition loc_200 : location_info := LocationInfo file_0 78 10 78 16.
  Definition loc_201 : location_info := LocationInfo file_0 78 10 78 16.
  Definition loc_202 : location_info := LocationInfo file_0 78 10 78 11.
  Definition loc_203 : location_info := LocationInfo file_0 78 10 78 11.
  Definition loc_206 : location_info := LocationInfo file_0 85 2 85 51.
  Definition loc_207 : location_info := LocationInfo file_0 86 2 86 37.
  Definition loc_208 : location_info := LocationInfo file_0 87 2 87 11.
  Definition loc_209 : location_info := LocationInfo file_0 88 2 88 51.
  Definition loc_210 : location_info := LocationInfo file_0 89 2 89 37.
  Definition loc_211 : location_info := LocationInfo file_0 90 2 90 11.
  Definition loc_212 : location_info := LocationInfo file_0 90 2 90 6.
  Definition loc_213 : location_info := LocationInfo file_0 90 2 90 3.
  Definition loc_214 : location_info := LocationInfo file_0 90 2 90 3.
  Definition loc_215 : location_info := LocationInfo file_0 90 9 90 10.
  Definition loc_216 : location_info := LocationInfo file_0 89 26 89 37.
  Definition loc_217 : location_info := LocationInfo file_0 89 28 89 35.
  Definition loc_219 : location_info := LocationInfo file_0 89 2 89 37.
  Definition loc_220 : location_info := LocationInfo file_0 89 5 89 24.
  Definition loc_221 : location_info := LocationInfo file_0 89 5 89 6.
  Definition loc_222 : location_info := LocationInfo file_0 89 5 89 6.
  Definition loc_223 : location_info := LocationInfo file_0 89 10 89 24.
  Definition loc_224 : location_info := LocationInfo file_0 88 18 88 50.
  Definition loc_225 : location_info := LocationInfo file_0 88 18 88 28.
  Definition loc_226 : location_info := LocationInfo file_0 88 18 88 28.
  Definition loc_227 : location_info := LocationInfo file_0 88 29 88 30.
  Definition loc_228 : location_info := LocationInfo file_0 88 29 88 30.
  Definition loc_229 : location_info := LocationInfo file_0 88 32 88 49.
  Definition loc_232 : location_info := LocationInfo file_0 87 2 87 6.
  Definition loc_233 : location_info := LocationInfo file_0 87 2 87 3.
  Definition loc_234 : location_info := LocationInfo file_0 87 2 87 3.
  Definition loc_235 : location_info := LocationInfo file_0 87 9 87 10.
  Definition loc_236 : location_info := LocationInfo file_0 86 26 86 37.
  Definition loc_237 : location_info := LocationInfo file_0 86 28 86 35.
  Definition loc_239 : location_info := LocationInfo file_0 86 2 86 37.
  Definition loc_240 : location_info := LocationInfo file_0 86 5 86 24.
  Definition loc_241 : location_info := LocationInfo file_0 86 5 86 6.
  Definition loc_242 : location_info := LocationInfo file_0 86 5 86 6.
  Definition loc_243 : location_info := LocationInfo file_0 86 10 86 24.
  Definition loc_244 : location_info := LocationInfo file_0 85 18 85 50.
  Definition loc_245 : location_info := LocationInfo file_0 85 18 85 28.
  Definition loc_246 : location_info := LocationInfo file_0 85 18 85 28.
  Definition loc_247 : location_info := LocationInfo file_0 85 29 85 30.
  Definition loc_248 : location_info := LocationInfo file_0 85 29 85 30.
  Definition loc_249 : location_info := LocationInfo file_0 85 32 85 49.
  Definition loc_254 : location_info := LocationInfo file_0 98 2 98 40.
  Definition loc_255 : location_info := LocationInfo file_0 99 2 99 15.
  Definition loc_256 : location_info := LocationInfo file_0 100 2 100 33.
  Definition loc_257 : location_info := LocationInfo file_0 101 2 101 18.
  Definition loc_258 : location_info := LocationInfo file_0 102 2 102 13.
  Definition loc_259 : location_info := LocationInfo file_0 102 9 102 12.
  Definition loc_260 : location_info := LocationInfo file_0 102 9 102 12.
  Definition loc_261 : location_info := LocationInfo file_0 101 2 101 11.
  Definition loc_262 : location_info := LocationInfo file_0 101 2 101 3.
  Definition loc_263 : location_info := LocationInfo file_0 101 2 101 3.
  Definition loc_264 : location_info := LocationInfo file_0 101 2 101 17.
  Definition loc_265 : location_info := LocationInfo file_0 101 2 101 11.
  Definition loc_266 : location_info := LocationInfo file_0 101 2 101 11.
  Definition loc_267 : location_info := LocationInfo file_0 101 2 101 3.
  Definition loc_268 : location_info := LocationInfo file_0 101 2 101 3.
  Definition loc_269 : location_info := LocationInfo file_0 101 15 101 17.
  Definition loc_270 : location_info := LocationInfo file_0 101 15 101 17.
  Definition loc_271 : location_info := LocationInfo file_0 100 23 100 32.
  Definition loc_272 : location_info := LocationInfo file_0 100 23 100 32.
  Definition loc_273 : location_info := LocationInfo file_0 100 23 100 24.
  Definition loc_274 : location_info := LocationInfo file_0 100 23 100 24.
  Definition loc_277 : location_info := LocationInfo file_0 99 2 99 8.
  Definition loc_278 : location_info := LocationInfo file_0 99 2 99 3.
  Definition loc_279 : location_info := LocationInfo file_0 99 2 99 3.
  Definition loc_280 : location_info := LocationInfo file_0 99 2 99 14.
  Definition loc_281 : location_info := LocationInfo file_0 99 2 99 8.
  Definition loc_282 : location_info := LocationInfo file_0 99 2 99 8.
  Definition loc_283 : location_info := LocationInfo file_0 99 2 99 3.
  Definition loc_284 : location_info := LocationInfo file_0 99 2 99 3.
  Definition loc_285 : location_info := LocationInfo file_0 99 12 99 14.
  Definition loc_286 : location_info := LocationInfo file_0 99 12 99 14.
  Definition loc_287 : location_info := LocationInfo file_0 98 18 98 40.
  Definition loc_288 : location_info := LocationInfo file_0 98 25 98 39.
  Definition loc_289 : location_info := LocationInfo file_0 98 2 98 40.
  Definition loc_290 : location_info := LocationInfo file_0 98 5 98 16.
  Definition loc_291 : location_info := LocationInfo file_0 98 5 98 7.
  Definition loc_292 : location_info := LocationInfo file_0 98 5 98 7.
  Definition loc_293 : location_info := LocationInfo file_0 98 10 98 16.
  Definition loc_294 : location_info := LocationInfo file_0 98 10 98 16.
  Definition loc_295 : location_info := LocationInfo file_0 98 10 98 11.
  Definition loc_296 : location_info := LocationInfo file_0 98 10 98 11.

  (* Definition of struct [__cerbty_unnamed_tag_486]. *)
  Program Definition struct___cerbty_unnamed_tag_486 := {|
    sl_members := [
      (Some "__dummy_max_align_t", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [atomic_flag]. *)
  Program Definition struct_atomic_flag := {|
    sl_members := [
      (Some "_Value", bool_layout)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [spinlock]. *)
  Program Definition struct_spinlock := {|
    sl_members := [
      (Some "lock", bool_layout)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [mem_t]. *)
  Program Definition struct_mem_t := {|
    sl_members := [
      (Some "len", it_layout size_t);
      (Some "buffer", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [xy]. *)
  Program Definition struct_xy := {|
    sl_members := [
      (Some "x", it_layout u8);
      (Some "y", it_layout u8)
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

  (* Definition of function [alloc_1]. *)
  Definition impl_alloc_1 : function := {|
    f_args := [
      ("d", void*);
      ("sz", it_layout size_t)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_36 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_36 ((LocInfoE loc_37 (use{IntOp size_t} (LocInfoE loc_38 ("sz")))) >{IntOp size_t, IntOp size_t, i32} (LocInfoE loc_39 (use{IntOp size_t} (LocInfoE loc_40 ((LocInfoE loc_41 (!{PtrOp} (LocInfoE loc_42 ("d")))) at{struct_mem_t} "len")))))
        then
        locinfo: loc_33 ;
          Goto "#2"
        else
        locinfo: loc_12 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_12 ;
        LocInfoE loc_23 ((LocInfoE loc_24 (!{PtrOp} (LocInfoE loc_25 ("d")))) at{struct_mem_t} "len") <-{ IntOp size_t }
          LocInfoE loc_26 ((LocInfoE loc_27 (use{IntOp size_t} (LocInfoE loc_28 ((LocInfoE loc_29 (!{PtrOp} (LocInfoE loc_30 ("d")))) at{struct_mem_t} "len")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_31 (use{IntOp size_t} (LocInfoE loc_32 ("sz"))))) ;
        locinfo: loc_13 ;
        Return (LocInfoE loc_14 ((LocInfoE loc_15 (use{PtrOp} (LocInfoE loc_16 ((LocInfoE loc_17 (!{PtrOp} (LocInfoE loc_18 ("d")))) at{struct_mem_t} "buffer")))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_19 (use{IntOp size_t} (LocInfoE loc_20 ((LocInfoE loc_21 (!{PtrOp} (LocInfoE loc_22 ("d")))) at{struct_mem_t} "len"))))))
      ]> $
      <[ "#2" :=
        locinfo: loc_33 ;
        Return (LocInfoE loc_34 (NULL))
      ]> $
      <[ "#3" :=
        locinfo: loc_12 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [alloc_2]. *)
  Definition impl_alloc_2 : function := {|
    f_args := [
      ("d", void*);
      ("sz", it_layout size_t)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_70 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_70 ((LocInfoE loc_71 (use{IntOp size_t} (LocInfoE loc_72 ("sz")))) >{IntOp size_t, IntOp size_t, i32} (LocInfoE loc_73 (use{IntOp size_t} (LocInfoE loc_74 ((LocInfoE loc_75 (!{PtrOp} (LocInfoE loc_76 ("d")))) at{struct_mem_t} "len")))))
        then
        locinfo: loc_67 ;
          Goto "#2"
        else
        locinfo: loc_46 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_46 ;
        LocInfoE loc_57 ((LocInfoE loc_58 (!{PtrOp} (LocInfoE loc_59 ("d")))) at{struct_mem_t} "len") <-{ IntOp size_t }
          LocInfoE loc_60 ((LocInfoE loc_61 (use{IntOp size_t} (LocInfoE loc_62 ((LocInfoE loc_63 (!{PtrOp} (LocInfoE loc_64 ("d")))) at{struct_mem_t} "len")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_65 (use{IntOp size_t} (LocInfoE loc_66 ("sz"))))) ;
        locinfo: loc_47 ;
        Return (LocInfoE loc_48 ((LocInfoE loc_49 (use{PtrOp} (LocInfoE loc_50 ((LocInfoE loc_51 (!{PtrOp} (LocInfoE loc_52 ("d")))) at{struct_mem_t} "buffer")))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_53 (use{IntOp size_t} (LocInfoE loc_54 ((LocInfoE loc_55 (!{PtrOp} (LocInfoE loc_56 ("d")))) at{struct_mem_t} "len"))))))
      ]> $
      <[ "#2" :=
        locinfo: loc_67 ;
        Return (LocInfoE loc_68 (NULL))
      ]> $
      <[ "#3" :=
        locinfo: loc_46 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [client_2]. *)
  Definition impl_client_2 (global_alloc_2 : loc): function := {|
    f_args := [
      ("d", void*)
    ];
    f_local_vars := [
      ("s", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "s" <-{ PtrOp }
          LocInfoE loc_94 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_94 (Call (LocInfoE loc_96 (global_alloc_2)) [@{expr} LocInfoE loc_97 (use{PtrOp} (LocInfoE loc_98 ("d"))) ;
          LocInfoE loc_99 (i2v (layout_of struct_xy).(ly_size) size_t) ]))) ;
        locinfo: loc_90 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_90 ((LocInfoE loc_91 (use{PtrOp} (LocInfoE loc_92 ("s")))) ={PtrOp, PtrOp, i32} (LocInfoE loc_93 (NULL)))
        then
        locinfo: loc_87 ;
          Goto "#2"
        else
        locinfo: loc_81 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_81 ;
        LocInfoE loc_82 ((LocInfoE loc_83 (!{PtrOp} (LocInfoE loc_84 ("s")))) at{struct_xy} "x") <-{ IntOp u8 }
          LocInfoE loc_85 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_85 (i2v 0 i32))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_87 ;
        Return (VOID)
      ]> $
      <[ "#3" :=
        locinfo: loc_81 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [alloc_2_alt]. *)
  Definition impl_alloc_2_alt : function := {|
    f_args := [
      ("d", void*);
      ("sz", it_layout size_t)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_129 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_129 ((LocInfoE loc_130 (use{IntOp size_t} (LocInfoE loc_131 ("sz")))) >{IntOp size_t, IntOp size_t, i32} (LocInfoE loc_132 (use{IntOp size_t} (LocInfoE loc_133 ((LocInfoE loc_134 (!{PtrOp} (LocInfoE loc_135 ("d")))) at{struct_mem_t} "len")))))
        then
        locinfo: loc_126 ;
          Goto "#2"
        else
        locinfo: loc_105 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_105 ;
        LocInfoE loc_116 ((LocInfoE loc_117 (!{PtrOp} (LocInfoE loc_118 ("d")))) at{struct_mem_t} "len") <-{ IntOp size_t }
          LocInfoE loc_119 ((LocInfoE loc_120 (use{IntOp size_t} (LocInfoE loc_121 ((LocInfoE loc_122 (!{PtrOp} (LocInfoE loc_123 ("d")))) at{struct_mem_t} "len")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_124 (use{IntOp size_t} (LocInfoE loc_125 ("sz"))))) ;
        locinfo: loc_106 ;
        Return (LocInfoE loc_107 ((LocInfoE loc_108 (use{PtrOp} (LocInfoE loc_109 ((LocInfoE loc_110 (!{PtrOp} (LocInfoE loc_111 ("d")))) at{struct_mem_t} "buffer")))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_112 (use{IntOp size_t} (LocInfoE loc_113 ((LocInfoE loc_114 (!{PtrOp} (LocInfoE loc_115 ("d")))) at{struct_mem_t} "len"))))))
      ]> $
      <[ "#2" :=
        locinfo: loc_126 ;
        Return (LocInfoE loc_127 (NULL))
      ]> $
      <[ "#3" :=
        locinfo: loc_105 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [alloc_3]. *)
  Definition impl_alloc_3 : function := {|
    f_args := [
      ("d", void*);
      ("sz", it_layout size_t)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_163 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_163 ((LocInfoE loc_164 (use{IntOp size_t} (LocInfoE loc_165 ("sz")))) >{IntOp size_t, IntOp size_t, i32} (LocInfoE loc_166 (use{IntOp size_t} (LocInfoE loc_167 ((LocInfoE loc_168 (!{PtrOp} (LocInfoE loc_169 ("d")))) at{struct_mem_t} "len")))))
        then
        locinfo: loc_160 ;
          Goto "#2"
        else
        locinfo: loc_139 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_139 ;
        LocInfoE loc_150 ((LocInfoE loc_151 (!{PtrOp} (LocInfoE loc_152 ("d")))) at{struct_mem_t} "len") <-{ IntOp size_t }
          LocInfoE loc_153 ((LocInfoE loc_154 (use{IntOp size_t} (LocInfoE loc_155 ((LocInfoE loc_156 (!{PtrOp} (LocInfoE loc_157 ("d")))) at{struct_mem_t} "len")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_158 (use{IntOp size_t} (LocInfoE loc_159 ("sz"))))) ;
        locinfo: loc_140 ;
        Return (LocInfoE loc_141 ((LocInfoE loc_142 (use{PtrOp} (LocInfoE loc_143 ((LocInfoE loc_144 (!{PtrOp} (LocInfoE loc_145 ("d")))) at{struct_mem_t} "buffer")))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_146 (use{IntOp size_t} (LocInfoE loc_147 ((LocInfoE loc_148 (!{PtrOp} (LocInfoE loc_149 ("d")))) at{struct_mem_t} "len"))))))
      ]> $
      <[ "#2" :=
        locinfo: loc_160 ;
        Return (LocInfoE loc_161 (NULL))
      ]> $
      <[ "#3" :=
        locinfo: loc_139 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [alloc_full]. *)
  Definition impl_alloc_full : function := {|
    f_args := [
      ("d", void*);
      ("sz", it_layout size_t)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_197 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_197 ((LocInfoE loc_198 (use{IntOp size_t} (LocInfoE loc_199 ("sz")))) >{IntOp size_t, IntOp size_t, i32} (LocInfoE loc_200 (use{IntOp size_t} (LocInfoE loc_201 ((LocInfoE loc_202 (!{PtrOp} (LocInfoE loc_203 ("d")))) at{struct_mem_t} "len")))))
        then
        locinfo: loc_194 ;
          Goto "#2"
        else
        locinfo: loc_173 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_173 ;
        LocInfoE loc_184 ((LocInfoE loc_185 (!{PtrOp} (LocInfoE loc_186 ("d")))) at{struct_mem_t} "len") <-{ IntOp size_t }
          LocInfoE loc_187 ((LocInfoE loc_188 (use{IntOp size_t} (LocInfoE loc_189 ((LocInfoE loc_190 (!{PtrOp} (LocInfoE loc_191 ("d")))) at{struct_mem_t} "len")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_192 (use{IntOp size_t} (LocInfoE loc_193 ("sz"))))) ;
        locinfo: loc_174 ;
        Return (LocInfoE loc_175 ((LocInfoE loc_176 (use{PtrOp} (LocInfoE loc_177 ((LocInfoE loc_178 (!{PtrOp} (LocInfoE loc_179 ("d")))) at{struct_mem_t} "buffer")))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_180 (use{IntOp size_t} (LocInfoE loc_181 ((LocInfoE loc_182 (!{PtrOp} (LocInfoE loc_183 ("d")))) at{struct_mem_t} "len"))))))
      ]> $
      <[ "#2" :=
        locinfo: loc_194 ;
        Return (LocInfoE loc_195 (NULL))
      ]> $
      <[ "#3" :=
        locinfo: loc_173 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [client_full]. *)
  Definition impl_client_full (global_alloc_full : loc): function := {|
    f_args := [
      ("d", void*)
    ];
    f_local_vars := [
      ("s", void*);
      ("t", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "s" <-{ PtrOp }
          LocInfoE loc_244 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_244 (Call (LocInfoE loc_246 (global_alloc_full)) [@{expr} LocInfoE loc_247 (use{PtrOp} (LocInfoE loc_248 ("d"))) ;
          LocInfoE loc_249 (i2v (layout_of struct_xy).(ly_size) size_t) ]))) ;
        locinfo: loc_240 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_240 ((LocInfoE loc_241 (use{PtrOp} (LocInfoE loc_242 ("s")))) ={PtrOp, PtrOp, i32} (LocInfoE loc_243 (NULL)))
        then
        locinfo: loc_237 ;
          Goto "#5"
        else
        locinfo: loc_208 ;
          Goto "#6"
      ]> $
      <[ "#1" :=
        locinfo: loc_208 ;
        LocInfoE loc_232 ((LocInfoE loc_233 (!{PtrOp} (LocInfoE loc_234 ("s")))) at{struct_xy} "x") <-{ IntOp u8 }
          LocInfoE loc_235 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_235 (i2v 0 i32))) ;
        "t" <-{ PtrOp }
          LocInfoE loc_224 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_224 (Call (LocInfoE loc_226 (global_alloc_full)) [@{expr} LocInfoE loc_227 (use{PtrOp} (LocInfoE loc_228 ("d"))) ;
          LocInfoE loc_229 (i2v (layout_of struct_xy).(ly_size) size_t) ]))) ;
        locinfo: loc_220 ;
        if{IntOp i32, Some "#2"}: LocInfoE loc_220 ((LocInfoE loc_221 (use{PtrOp} (LocInfoE loc_222 ("t")))) ={PtrOp, PtrOp, i32} (LocInfoE loc_223 (NULL)))
        then
        locinfo: loc_217 ;
          Goto "#3"
        else
        locinfo: loc_211 ;
          Goto "#4"
      ]> $
      <[ "#2" :=
        locinfo: loc_211 ;
        LocInfoE loc_212 ((LocInfoE loc_213 (!{PtrOp} (LocInfoE loc_214 ("t")))) at{struct_xy} "x") <-{ IntOp u8 }
          LocInfoE loc_215 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_215 (i2v 0 i32))) ;
        Return (VOID)
      ]> $
      <[ "#3" :=
        locinfo: loc_217 ;
        Return (VOID)
      ]> $
      <[ "#4" :=
        locinfo: loc_211 ;
        Goto "#2"
      ]> $
      <[ "#5" :=
        locinfo: loc_237 ;
        Return (VOID)
      ]> $
      <[ "#6" :=
        locinfo: loc_208 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [alloc_from_start]. *)
  Definition impl_alloc_from_start : function := {|
    f_args := [
      ("d", void*);
      ("sz", it_layout size_t)
    ];
    f_local_vars := [
      ("res", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_290 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_290 ((LocInfoE loc_291 (use{IntOp size_t} (LocInfoE loc_292 ("sz")))) >{IntOp size_t, IntOp size_t, i32} (LocInfoE loc_293 (use{IntOp size_t} (LocInfoE loc_294 ((LocInfoE loc_295 (!{PtrOp} (LocInfoE loc_296 ("d")))) at{struct_mem_t} "len")))))
        then
        locinfo: loc_287 ;
          Goto "#2"
        else
        locinfo: loc_255 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_255 ;
        LocInfoE loc_277 ((LocInfoE loc_278 (!{PtrOp} (LocInfoE loc_279 ("d")))) at{struct_mem_t} "len") <-{ IntOp size_t }
          LocInfoE loc_280 ((LocInfoE loc_281 (use{IntOp size_t} (LocInfoE loc_282 ((LocInfoE loc_283 (!{PtrOp} (LocInfoE loc_284 ("d")))) at{struct_mem_t} "len")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_285 (use{IntOp size_t} (LocInfoE loc_286 ("sz"))))) ;
        "res" <-{ PtrOp }
          LocInfoE loc_271 (use{PtrOp} (LocInfoE loc_272 ((LocInfoE loc_273 (!{PtrOp} (LocInfoE loc_274 ("d")))) at{struct_mem_t} "buffer"))) ;
        locinfo: loc_257 ;
        LocInfoE loc_261 ((LocInfoE loc_262 (!{PtrOp} (LocInfoE loc_263 ("d")))) at{struct_mem_t} "buffer") <-{ PtrOp }
          LocInfoE loc_264 ((LocInfoE loc_265 (use{PtrOp} (LocInfoE loc_266 ((LocInfoE loc_267 (!{PtrOp} (LocInfoE loc_268 ("d")))) at{struct_mem_t} "buffer")))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_269 (use{IntOp size_t} (LocInfoE loc_270 ("sz"))))) ;
        locinfo: loc_258 ;
        Return (LocInfoE loc_259 (use{PtrOp} (LocInfoE loc_260 ("res"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_287 ;
        Return (LocInfoE loc_288 (NULL))
      ]> $
      <[ "#3" :=
        locinfo: loc_255 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.
End code.
