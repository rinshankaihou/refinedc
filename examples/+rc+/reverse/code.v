From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/reverse.c]. *)
Section code.
  Definition file_0 : string := "examples/reverse.c".
  Definition loc_2 : location_info := LocationInfo file_0 16 4 16 26.
  Definition loc_3 : location_info := LocationInfo file_0 16 11 16 25.
  Definition loc_6 : location_info := LocationInfo file_0 23 4 23 19.
  Definition loc_7 : location_info := LocationInfo file_0 24 4 24 19.
  Definition loc_8 : location_info := LocationInfo file_0 25 4 25 16.
  Definition loc_9 : location_info := LocationInfo file_0 25 11 25 15.
  Definition loc_10 : location_info := LocationInfo file_0 25 11 25 15.
  Definition loc_11 : location_info := LocationInfo file_0 24 4 24 14.
  Definition loc_12 : location_info := LocationInfo file_0 24 4 24 8.
  Definition loc_13 : location_info := LocationInfo file_0 24 4 24 8.
  Definition loc_14 : location_info := LocationInfo file_0 24 17 24 18.
  Definition loc_15 : location_info := LocationInfo file_0 24 17 24 18.
  Definition loc_16 : location_info := LocationInfo file_0 23 4 23 14.
  Definition loc_17 : location_info := LocationInfo file_0 23 4 23 8.
  Definition loc_18 : location_info := LocationInfo file_0 23 4 23 8.
  Definition loc_19 : location_info := LocationInfo file_0 23 17 23 18.
  Definition loc_20 : location_info := LocationInfo file_0 23 17 23 18.
  Definition loc_23 : location_info := LocationInfo file_0 33 2 35 3.
  Definition loc_24 : location_info := LocationInfo file_0 36 2 36 25.
  Definition loc_25 : location_info := LocationInfo file_0 37 2 37 18.
  Definition loc_26 : location_info := LocationInfo file_0 38 2 38 13.
  Definition loc_27 : location_info := LocationInfo file_0 38 9 38 12.
  Definition loc_28 : location_info := LocationInfo file_0 38 9 38 12.
  Definition loc_29 : location_info := LocationInfo file_0 37 2 37 4.
  Definition loc_30 : location_info := LocationInfo file_0 37 3 37 4.
  Definition loc_31 : location_info := LocationInfo file_0 37 3 37 4.
  Definition loc_32 : location_info := LocationInfo file_0 37 7 37 17.
  Definition loc_33 : location_info := LocationInfo file_0 37 7 37 17.
  Definition loc_34 : location_info := LocationInfo file_0 37 7 37 11.
  Definition loc_35 : location_info := LocationInfo file_0 37 7 37 11.
  Definition loc_36 : location_info := LocationInfo file_0 37 9 37 10.
  Definition loc_37 : location_info := LocationInfo file_0 37 9 37 10.
  Definition loc_38 : location_info := LocationInfo file_0 36 14 36 24.
  Definition loc_39 : location_info := LocationInfo file_0 36 14 36 24.
  Definition loc_40 : location_info := LocationInfo file_0 36 14 36 18.
  Definition loc_41 : location_info := LocationInfo file_0 36 14 36 18.
  Definition loc_42 : location_info := LocationInfo file_0 36 16 36 17.
  Definition loc_43 : location_info := LocationInfo file_0 36 16 36 17.
  Definition loc_46 : location_info := LocationInfo file_0 33 28 35 3.
  Definition loc_47 : location_info := LocationInfo file_0 34 6 34 28.
  Definition loc_48 : location_info := LocationInfo file_0 34 13 34 27.
  Definition loc_50 : location_info := LocationInfo file_0 33 6 33 26.
  Definition loc_51 : location_info := LocationInfo file_0 33 6 33 8.
  Definition loc_52 : location_info := LocationInfo file_0 33 6 33 8.
  Definition loc_53 : location_info := LocationInfo file_0 33 7 33 8.
  Definition loc_54 : location_info := LocationInfo file_0 33 7 33 8.
  Definition loc_55 : location_info := LocationInfo file_0 33 12 33 26.
  Definition loc_58 : location_info := LocationInfo file_0 48 2 50 3.
  Definition loc_59 : location_info := LocationInfo file_0 51 2 51 28.
  Definition loc_60 : location_info := LocationInfo file_0 52 2 54 3.
  Definition loc_61 : location_info := LocationInfo file_0 55 2 55 36.
  Definition loc_62 : location_info := LocationInfo file_0 55 9 55 35.
  Definition loc_63 : location_info := LocationInfo file_0 55 9 55 19.
  Definition loc_64 : location_info := LocationInfo file_0 55 9 55 19.
  Definition loc_65 : location_info := LocationInfo file_0 55 20 55 31.
  Definition loc_66 : location_info := LocationInfo file_0 55 21 55 31.
  Definition loc_67 : location_info := LocationInfo file_0 55 21 55 25.
  Definition loc_68 : location_info := LocationInfo file_0 55 21 55 25.
  Definition loc_69 : location_info := LocationInfo file_0 55 23 55 24.
  Definition loc_70 : location_info := LocationInfo file_0 55 23 55 24.
  Definition loc_71 : location_info := LocationInfo file_0 55 33 55 34.
  Definition loc_72 : location_info := LocationInfo file_0 55 33 55 34.
  Definition loc_73 : location_info := LocationInfo file_0 52 18 54 3.
  Definition loc_74 : location_info := LocationInfo file_0 53 6 53 15.
  Definition loc_75 : location_info := LocationInfo file_0 53 13 53 14.
  Definition loc_77 : location_info := LocationInfo file_0 52 6 52 16.
  Definition loc_78 : location_info := LocationInfo file_0 52 6 52 11.
  Definition loc_79 : location_info := LocationInfo file_0 52 6 52 11.
  Definition loc_80 : location_info := LocationInfo file_0 52 7 52 11.
  Definition loc_81 : location_info := LocationInfo file_0 52 7 52 11.
  Definition loc_82 : location_info := LocationInfo file_0 52 15 52 16.
  Definition loc_83 : location_info := LocationInfo file_0 52 15 52 16.
  Definition loc_84 : location_info := LocationInfo file_0 51 17 51 27.
  Definition loc_85 : location_info := LocationInfo file_0 51 17 51 27.
  Definition loc_86 : location_info := LocationInfo file_0 51 17 51 21.
  Definition loc_87 : location_info := LocationInfo file_0 51 17 51 21.
  Definition loc_88 : location_info := LocationInfo file_0 51 19 51 20.
  Definition loc_89 : location_info := LocationInfo file_0 51 19 51 20.
  Definition loc_92 : location_info := LocationInfo file_0 48 28 50 3.
  Definition loc_93 : location_info := LocationInfo file_0 49 6 49 15.
  Definition loc_94 : location_info := LocationInfo file_0 49 13 49 14.
  Definition loc_96 : location_info := LocationInfo file_0 48 6 48 26.
  Definition loc_97 : location_info := LocationInfo file_0 48 6 48 8.
  Definition loc_98 : location_info := LocationInfo file_0 48 6 48 8.
  Definition loc_99 : location_info := LocationInfo file_0 48 7 48 8.
  Definition loc_100 : location_info := LocationInfo file_0 48 7 48 8.
  Definition loc_101 : location_info := LocationInfo file_0 48 12 48 26.
  Definition loc_104 : location_info := LocationInfo file_0 65 4 65 23.
  Definition loc_105 : location_info := LocationInfo file_0 71 4 80 5.
  Definition loc_106 : location_info := LocationInfo file_0 81 4 81 13.
  Definition loc_107 : location_info := LocationInfo file_0 81 11 81 12.
  Definition loc_108 : location_info := LocationInfo file_0 71 4 80 5.
  Definition loc_109 : location_info := LocationInfo file_0 71 35 80 5.
  Definition loc_110 : location_info := LocationInfo file_0 72 8 72 27.
  Definition loc_111 : location_info := LocationInfo file_0 74 8 74 33.
  Definition loc_112 : location_info := LocationInfo file_0 75 8 77 9.
  Definition loc_113 : location_info := LocationInfo file_0 79 8 79 26.
  Definition loc_114 : location_info := LocationInfo file_0 71 4 80 5.
  Definition loc_115 : location_info := LocationInfo file_0 71 4 80 5.
  Definition loc_116 : location_info := LocationInfo file_0 79 8 79 12.
  Definition loc_117 : location_info := LocationInfo file_0 79 15 79 25.
  Definition loc_118 : location_info := LocationInfo file_0 79 16 79 25.
  Definition loc_119 : location_info := LocationInfo file_0 79 16 79 19.
  Definition loc_120 : location_info := LocationInfo file_0 79 16 79 19.
  Definition loc_121 : location_info := LocationInfo file_0 75 23 77 9.
  Definition loc_122 : location_info := LocationInfo file_0 76 12 76 21.
  Definition loc_123 : location_info := LocationInfo file_0 76 19 76 20.
  Definition loc_125 : location_info := LocationInfo file_0 75 11 75 21.
  Definition loc_126 : location_info := LocationInfo file_0 75 11 75 16.
  Definition loc_127 : location_info := LocationInfo file_0 75 11 75 16.
  Definition loc_128 : location_info := LocationInfo file_0 75 12 75 16.
  Definition loc_129 : location_info := LocationInfo file_0 75 12 75 16.
  Definition loc_130 : location_info := LocationInfo file_0 75 20 75 21.
  Definition loc_131 : location_info := LocationInfo file_0 75 20 75 21.
  Definition loc_132 : location_info := LocationInfo file_0 74 23 74 32.
  Definition loc_133 : location_info := LocationInfo file_0 74 23 74 32.
  Definition loc_134 : location_info := LocationInfo file_0 74 23 74 26.
  Definition loc_135 : location_info := LocationInfo file_0 74 23 74 26.
  Definition loc_138 : location_info := LocationInfo file_0 72 21 72 26.
  Definition loc_139 : location_info := LocationInfo file_0 72 21 72 26.
  Definition loc_140 : location_info := LocationInfo file_0 72 22 72 26.
  Definition loc_141 : location_info := LocationInfo file_0 72 22 72 26.
  Definition loc_144 : location_info := LocationInfo file_0 71 10 71 33.
  Definition loc_145 : location_info := LocationInfo file_0 71 10 71 15.
  Definition loc_146 : location_info := LocationInfo file_0 71 10 71 15.
  Definition loc_147 : location_info := LocationInfo file_0 71 11 71 15.
  Definition loc_148 : location_info := LocationInfo file_0 71 11 71 15.
  Definition loc_149 : location_info := LocationInfo file_0 71 19 71 33.
  Definition loc_150 : location_info := LocationInfo file_0 65 19 65 22.
  Definition loc_151 : location_info := LocationInfo file_0 65 20 65 22.
  Definition loc_152 : location_info := LocationInfo file_0 65 21 65 22.
  Definition loc_153 : location_info := LocationInfo file_0 65 21 65 22.
  Definition loc_158 : location_info := LocationInfo file_0 88 4 88 25.
  Definition loc_159 : location_info := LocationInfo file_0 89 4 89 19.
  Definition loc_160 : location_info := LocationInfo file_0 90 4 90 45.
  Definition loc_161 : location_info := LocationInfo file_0 91 4 91 19.
  Definition loc_162 : location_info := LocationInfo file_0 92 4 92 45.
  Definition loc_163 : location_info := LocationInfo file_0 93 4 93 24.
  Definition loc_164 : location_info := LocationInfo file_0 94 4 94 28.
  Definition loc_165 : location_info := LocationInfo file_0 95 4 95 25.
  Definition loc_166 : location_info := LocationInfo file_0 99 4 99 13.
  Definition loc_167 : location_info := LocationInfo file_0 99 4 99 13.
  Definition loc_168 : location_info := LocationInfo file_0 99 12 99 13.
  Definition loc_169 : location_info := LocationInfo file_0 99 4 99 13.
  Definition loc_170 : location_info := LocationInfo file_0 99 4 99 13.
  Definition loc_171 : location_info := LocationInfo file_0 99 10 99 11.
  Definition loc_172 : location_info := LocationInfo file_0 95 11 95 23.
  Definition loc_173 : location_info := LocationInfo file_0 95 11 95 18.
  Definition loc_174 : location_info := LocationInfo file_0 95 11 95 18.
  Definition loc_175 : location_info := LocationInfo file_0 95 12 95 18.
  Definition loc_176 : location_info := LocationInfo file_0 95 12 95 18.
  Definition loc_177 : location_info := LocationInfo file_0 95 22 95 23.
  Definition loc_178 : location_info := LocationInfo file_0 94 4 94 10.
  Definition loc_179 : location_info := LocationInfo file_0 94 13 94 27.
  Definition loc_180 : location_info := LocationInfo file_0 94 13 94 16.
  Definition loc_181 : location_info := LocationInfo file_0 94 13 94 16.
  Definition loc_182 : location_info := LocationInfo file_0 94 17 94 26.
  Definition loc_183 : location_info := LocationInfo file_0 94 18 94 26.
  Definition loc_184 : location_info := LocationInfo file_0 94 19 94 26.
  Definition loc_185 : location_info := LocationInfo file_0 94 19 94 26.
  Definition loc_186 : location_info := LocationInfo file_0 94 20 94 26.
  Definition loc_187 : location_info := LocationInfo file_0 94 20 94 26.
  Definition loc_188 : location_info := LocationInfo file_0 93 4 93 10.
  Definition loc_189 : location_info := LocationInfo file_0 93 13 93 23.
  Definition loc_190 : location_info := LocationInfo file_0 93 13 93 16.
  Definition loc_191 : location_info := LocationInfo file_0 93 13 93 16.
  Definition loc_192 : location_info := LocationInfo file_0 93 17 93 22.
  Definition loc_193 : location_info := LocationInfo file_0 93 18 93 22.
  Definition loc_194 : location_info := LocationInfo file_0 92 4 92 8.
  Definition loc_195 : location_info := LocationInfo file_0 92 11 92 44.
  Definition loc_196 : location_info := LocationInfo file_0 92 11 92 15.
  Definition loc_197 : location_info := LocationInfo file_0 92 11 92 15.
  Definition loc_198 : location_info := LocationInfo file_0 92 16 92 20.
  Definition loc_199 : location_info := LocationInfo file_0 92 16 92 20.
  Definition loc_200 : location_info := LocationInfo file_0 92 22 92 29.
  Definition loc_201 : location_info := LocationInfo file_0 92 23 92 29.
  Definition loc_202 : location_info := LocationInfo file_0 92 31 92 43.
  Definition loc_203 : location_info := LocationInfo file_0 92 32 92 43.
  Definition loc_204 : location_info := LocationInfo file_0 91 4 91 10.
  Definition loc_205 : location_info := LocationInfo file_0 91 13 91 18.
  Definition loc_206 : location_info := LocationInfo file_0 91 14 91 18.
  Definition loc_207 : location_info := LocationInfo file_0 90 4 90 8.
  Definition loc_208 : location_info := LocationInfo file_0 90 11 90 44.
  Definition loc_209 : location_info := LocationInfo file_0 90 11 90 15.
  Definition loc_210 : location_info := LocationInfo file_0 90 11 90 15.
  Definition loc_211 : location_info := LocationInfo file_0 90 16 90 20.
  Definition loc_212 : location_info := LocationInfo file_0 90 16 90 20.
  Definition loc_213 : location_info := LocationInfo file_0 90 22 90 29.
  Definition loc_214 : location_info := LocationInfo file_0 90 23 90 29.
  Definition loc_215 : location_info := LocationInfo file_0 90 31 90 43.
  Definition loc_216 : location_info := LocationInfo file_0 90 32 90 43.
  Definition loc_217 : location_info := LocationInfo file_0 89 17 89 18.
  Definition loc_220 : location_info := LocationInfo file_0 88 18 88 24.
  Definition loc_221 : location_info := LocationInfo file_0 88 18 88 22.
  Definition loc_222 : location_info := LocationInfo file_0 88 18 88 22.
  Definition loc_227 : location_info := LocationInfo file_0 108 2 108 21.
  Definition loc_228 : location_info := LocationInfo file_0 109 2 109 8.
  Definition loc_229 : location_info := LocationInfo file_0 113 2 118 3.
  Definition loc_230 : location_info := LocationInfo file_0 119 2 119 11.
  Definition loc_231 : location_info := LocationInfo file_0 119 9 119 10.
  Definition loc_232 : location_info := LocationInfo file_0 119 9 119 10.
  Definition loc_233 : location_info := LocationInfo file_0 113 2 118 3.
  Definition loc_234 : location_info := LocationInfo file_0 113 30 118 3.
  Definition loc_235 : location_info := LocationInfo file_0 114 4 114 16.
  Definition loc_236 : location_info := LocationInfo file_0 115 4 115 16.
  Definition loc_237 : location_info := LocationInfo file_0 116 4 116 10.
  Definition loc_238 : location_info := LocationInfo file_0 117 4 117 10.
  Definition loc_239 : location_info := LocationInfo file_0 113 2 118 3.
  Definition loc_240 : location_info := LocationInfo file_0 113 2 118 3.
  Definition loc_241 : location_info := LocationInfo file_0 117 4 117 5.
  Definition loc_242 : location_info := LocationInfo file_0 117 8 117 9.
  Definition loc_243 : location_info := LocationInfo file_0 117 8 117 9.
  Definition loc_244 : location_info := LocationInfo file_0 116 4 116 5.
  Definition loc_245 : location_info := LocationInfo file_0 116 8 116 9.
  Definition loc_246 : location_info := LocationInfo file_0 116 8 116 9.
  Definition loc_247 : location_info := LocationInfo file_0 115 4 115 11.
  Definition loc_248 : location_info := LocationInfo file_0 115 4 115 5.
  Definition loc_249 : location_info := LocationInfo file_0 115 4 115 5.
  Definition loc_250 : location_info := LocationInfo file_0 115 14 115 15.
  Definition loc_251 : location_info := LocationInfo file_0 115 14 115 15.
  Definition loc_252 : location_info := LocationInfo file_0 114 4 114 5.
  Definition loc_253 : location_info := LocationInfo file_0 114 8 114 15.
  Definition loc_254 : location_info := LocationInfo file_0 114 8 114 15.
  Definition loc_255 : location_info := LocationInfo file_0 114 8 114 9.
  Definition loc_256 : location_info := LocationInfo file_0 114 8 114 9.
  Definition loc_257 : location_info := LocationInfo file_0 113 9 113 28.
  Definition loc_258 : location_info := LocationInfo file_0 113 9 113 10.
  Definition loc_259 : location_info := LocationInfo file_0 113 9 113 10.
  Definition loc_260 : location_info := LocationInfo file_0 113 14 113 28.
  Definition loc_261 : location_info := LocationInfo file_0 109 2 109 3.
  Definition loc_262 : location_info := LocationInfo file_0 109 6 109 7.
  Definition loc_263 : location_info := LocationInfo file_0 109 6 109 7.
  Definition loc_264 : location_info := LocationInfo file_0 108 2 108 3.
  Definition loc_265 : location_info := LocationInfo file_0 108 6 108 20.
  Definition loc_268 : location_info := LocationInfo file_0 127 2 127 26.
  Definition loc_269 : location_info := LocationInfo file_0 132 2 136 3.
  Definition loc_270 : location_info := LocationInfo file_0 137 2 137 11.
  Definition loc_271 : location_info := LocationInfo file_0 137 11 137 3.
  Definition loc_272 : location_info := LocationInfo file_0 138 2 138 11.
  Definition loc_273 : location_info := LocationInfo file_0 138 9 138 10.
  Definition loc_274 : location_info := LocationInfo file_0 138 9 138 10.
  Definition loc_275 : location_info := LocationInfo file_0 137 2 137 10.
  Definition loc_276 : location_info := LocationInfo file_0 137 3 137 10.
  Definition loc_277 : location_info := LocationInfo file_0 137 5 137 9.
  Definition loc_278 : location_info := LocationInfo file_0 137 5 137 9.
  Definition loc_279 : location_info := LocationInfo file_0 132 2 136 3.
  Definition loc_280 : location_info := LocationInfo file_0 132 34 136 3.
  Definition loc_281 : location_info := LocationInfo file_0 133 6 133 31.
  Definition loc_282 : location_info := LocationInfo file_0 135 6 135 24.
  Definition loc_283 : location_info := LocationInfo file_0 132 2 136 3.
  Definition loc_284 : location_info := LocationInfo file_0 132 2 136 3.
  Definition loc_285 : location_info := LocationInfo file_0 135 6 135 10.
  Definition loc_286 : location_info := LocationInfo file_0 135 13 135 23.
  Definition loc_287 : location_info := LocationInfo file_0 135 14 135 23.
  Definition loc_288 : location_info := LocationInfo file_0 135 14 135 17.
  Definition loc_289 : location_info := LocationInfo file_0 135 14 135 17.
  Definition loc_290 : location_info := LocationInfo file_0 133 25 133 30.
  Definition loc_291 : location_info := LocationInfo file_0 133 25 133 30.
  Definition loc_292 : location_info := LocationInfo file_0 133 26 133 30.
  Definition loc_293 : location_info := LocationInfo file_0 133 26 133 30.
  Definition loc_296 : location_info := LocationInfo file_0 132 9 132 32.
  Definition loc_297 : location_info := LocationInfo file_0 132 9 132 14.
  Definition loc_298 : location_info := LocationInfo file_0 132 9 132 14.
  Definition loc_299 : location_info := LocationInfo file_0 132 10 132 14.
  Definition loc_300 : location_info := LocationInfo file_0 132 10 132 14.
  Definition loc_301 : location_info := LocationInfo file_0 132 18 132 32.
  Definition loc_302 : location_info := LocationInfo file_0 127 23 127 25.
  Definition loc_303 : location_info := LocationInfo file_0 127 24 127 25.

  (* Definition of struct [list]. *)
  Program Definition struct_list := {|
    sl_members := [
      (Some "head", LPtr);
      (Some "tail", LPtr)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [init]. *)
  Definition impl_init : function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        Return (LocInfoE loc_3 (NULL))
      ]> $∅
    )%E
  |}.

  (* Definition of function [push]. *)
  Definition impl_push : function := {|
    f_args := [
      ("p", LPtr);
      ("e", LPtr);
      ("node", LPtr)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_6 ;
        LocInfoE loc_16 ((LocInfoE loc_17 (!{LPtr} (LocInfoE loc_18 ("node")))) at{struct_list} "head") <-{ LPtr }
          LocInfoE loc_19 (use{LPtr} (LocInfoE loc_20 ("e"))) ;
        locinfo: loc_7 ;
        LocInfoE loc_11 ((LocInfoE loc_12 (!{LPtr} (LocInfoE loc_13 ("node")))) at{struct_list} "tail") <-{ LPtr }
          LocInfoE loc_14 (use{LPtr} (LocInfoE loc_15 ("p"))) ;
        locinfo: loc_8 ;
        Return (LocInfoE loc_9 (use{LPtr} (LocInfoE loc_10 ("node"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [pop]. *)
  Definition impl_pop : function := {|
    f_args := [
      ("p", LPtr)
    ];
    f_local_vars := [
      ("ret", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_50 ;
        if: LocInfoE loc_50 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_50 ((LocInfoE loc_51 (use{LPtr} (LocInfoE loc_53 (!{LPtr} (LocInfoE loc_54 ("p")))))) ={PtrOp, PtrOp} (LocInfoE loc_55 (NULL)))))
        then
        locinfo: loc_47 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#1" :=
        "ret" <-{ LPtr }
          LocInfoE loc_38 (use{LPtr} (LocInfoE loc_39 ((LocInfoE loc_40 (!{LPtr} (LocInfoE loc_42 (!{LPtr} (LocInfoE loc_43 ("p")))))) at{struct_list} "head"))) ;
        locinfo: loc_25 ;
        LocInfoE loc_30 (!{LPtr} (LocInfoE loc_31 ("p"))) <-{ LPtr }
          LocInfoE loc_32 (use{LPtr} (LocInfoE loc_33 ((LocInfoE loc_34 (!{LPtr} (LocInfoE loc_36 (!{LPtr} (LocInfoE loc_37 ("p")))))) at{struct_list} "tail"))) ;
        locinfo: loc_26 ;
        Return (LocInfoE loc_27 (use{LPtr} (LocInfoE loc_28 ("ret"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_47 ;
        Return (LocInfoE loc_48 (NULL))
      ]> $
      <[ "#3" :=
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [member_rec]. *)
  Definition impl_member_rec (member_rec : loc): function := {|
    f_args := [
      ("p", LPtr);
      ("k", it_layout size_t)
    ];
    f_local_vars := [
      ("head", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_96 ;
        if: LocInfoE loc_96 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_96 ((LocInfoE loc_97 (use{LPtr} (LocInfoE loc_99 (!{LPtr} (LocInfoE loc_100 ("p")))))) ={PtrOp, PtrOp} (LocInfoE loc_101 (NULL)))))
        then
        locinfo: loc_93 ;
          Goto "#5"
        else
        Goto "#6"
      ]> $
      <[ "#1" :=
        "head" <-{ LPtr }
          LocInfoE loc_84 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_84 (use{LPtr} (LocInfoE loc_85 ((LocInfoE loc_86 (!{LPtr} (LocInfoE loc_88 (!{LPtr} (LocInfoE loc_89 ("p")))))) at{struct_list} "head"))))) ;
        locinfo: loc_77 ;
        if: LocInfoE loc_77 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_77 ((LocInfoE loc_78 (use{it_layout size_t} (LocInfoE loc_80 (!{LPtr} (LocInfoE loc_81 ("head")))))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_82 (use{it_layout size_t} (LocInfoE loc_83 ("k")))))))
        then
        locinfo: loc_74 ;
          Goto "#3"
        else
        locinfo: loc_62 ;
          Goto "#4"
      ]> $
      <[ "#2" :=
        locinfo: loc_62 ;
        "$0" <- LocInfoE loc_64 (member_rec) with
          [ LocInfoE loc_65 (&(LocInfoE loc_66 ((LocInfoE loc_67 (!{LPtr} (LocInfoE loc_69 (!{LPtr} (LocInfoE loc_70 ("p")))))) at{struct_list} "tail"))) ;
          LocInfoE loc_71 (use{it_layout size_t} (LocInfoE loc_72 ("k"))) ] ;
        locinfo: loc_61 ;
        Return (LocInfoE loc_62 ("$0"))
      ]> $
      <[ "#3" :=
        locinfo: loc_74 ;
        Return (LocInfoE loc_75 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_75 (i2v 1 i32))))
      ]> $
      <[ "#4" :=
        locinfo: loc_62 ;
        Goto "#2"
      ]> $
      <[ "#5" :=
        locinfo: loc_93 ;
        Return (LocInfoE loc_94 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_94 (i2v 0 i32))))
      ]> $
      <[ "#6" :=
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [member]. *)
  Definition impl_member : function := {|
    f_args := [
      ("p", LPtr);
      ("k", it_layout size_t)
    ];
    f_local_vars := [
      ("prev", LPtr);
      ("cur", LPtr);
      ("head", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "prev" <-{ LPtr }
          LocInfoE loc_150 (&(LocInfoE loc_152 (!{LPtr} (LocInfoE loc_153 ("p"))))) ;
        locinfo: loc_105 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_144 ;
        if: LocInfoE loc_144 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_144 ((LocInfoE loc_145 (use{LPtr} (LocInfoE loc_147 (!{LPtr} (LocInfoE loc_148 ("prev")))))) !={PtrOp, PtrOp} (LocInfoE loc_149 (NULL)))))
        then
        Goto "#2"
        else
        locinfo: loc_106 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        "cur" <-{ LPtr }
          LocInfoE loc_138 (use{LPtr} (LocInfoE loc_140 (!{LPtr} (LocInfoE loc_141 ("prev"))))) ;
        "head" <-{ LPtr }
          LocInfoE loc_132 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_132 (use{LPtr} (LocInfoE loc_133 ((LocInfoE loc_134 (!{LPtr} (LocInfoE loc_135 ("cur")))) at{struct_list} "head"))))) ;
        locinfo: loc_125 ;
        if: LocInfoE loc_125 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_125 ((LocInfoE loc_126 (use{it_layout size_t} (LocInfoE loc_128 (!{LPtr} (LocInfoE loc_129 ("head")))))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_130 (use{it_layout size_t} (LocInfoE loc_131 ("k")))))))
        then
        locinfo: loc_122 ;
          Goto "#5"
        else
        locinfo: loc_113 ;
          Goto "#6"
      ]> $
      <[ "#3" :=
        locinfo: loc_106 ;
        Return (LocInfoE loc_107 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_107 (i2v 0 i32))))
      ]> $
      <[ "#4" :=
        locinfo: loc_113 ;
        LocInfoE loc_116 ("prev") <-{ LPtr }
          LocInfoE loc_117 (&(LocInfoE loc_118 ((LocInfoE loc_119 (!{LPtr} (LocInfoE loc_120 ("cur")))) at{struct_list} "tail"))) ;
        locinfo: loc_114 ;
        Goto "continue13"
      ]> $
      <[ "#5" :=
        locinfo: loc_122 ;
        Return (LocInfoE loc_123 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_123 (i2v 1 i32))))
      ]> $
      <[ "#6" :=
        locinfo: loc_113 ;
        Goto "#4"
      ]> $
      <[ "continue13" :=
        locinfo: loc_105 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [test]. *)
  Definition impl_test (init push pop : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
      ("list", LPtr);
      ("local1", it_layout i32);
      ("local1_node", layout_of struct_list);
      ("local3", LPtr);
      ("local2", LPtr);
      ("local4", LPtr);
      ("local2_node", layout_of struct_list)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_220 ;
        "$4" <- LocInfoE loc_222 (init) with [  ] ;
        "list" <-{ LPtr } LocInfoE loc_220 ("$4") ;
        "local1" <-{ it_layout i32 } LocInfoE loc_217 (i2v 0 i32) ;
        locinfo: loc_208 ;
        "$3" <- LocInfoE loc_210 (push) with
          [ LocInfoE loc_211 (use{LPtr} (LocInfoE loc_212 ("list"))) ;
          LocInfoE loc_213 (&(LocInfoE loc_214 ("local1"))) ;
          LocInfoE loc_215 (&(LocInfoE loc_216 ("local1_node"))) ] ;
        locinfo: loc_160 ;
        LocInfoE loc_207 ("list") <-{ LPtr } LocInfoE loc_208 ("$3") ;
        locinfo: loc_161 ;
        LocInfoE loc_204 ("local2") <-{ LPtr }
          LocInfoE loc_205 (&(LocInfoE loc_206 ("list"))) ;
        locinfo: loc_195 ;
        "$2" <- LocInfoE loc_197 (push) with
          [ LocInfoE loc_198 (use{LPtr} (LocInfoE loc_199 ("list"))) ;
          LocInfoE loc_200 (&(LocInfoE loc_201 ("local2"))) ;
          LocInfoE loc_202 (&(LocInfoE loc_203 ("local2_node"))) ] ;
        locinfo: loc_162 ;
        LocInfoE loc_194 ("list") <-{ LPtr } LocInfoE loc_195 ("$2") ;
        locinfo: loc_189 ;
        "$1" <- LocInfoE loc_191 (pop) with
          [ LocInfoE loc_192 (&(LocInfoE loc_193 ("list"))) ] ;
        locinfo: loc_163 ;
        LocInfoE loc_188 ("local3") <-{ LPtr } LocInfoE loc_189 ("$1") ;
        locinfo: loc_179 ;
        "$0" <- LocInfoE loc_181 (pop) with
          [ LocInfoE loc_182 (&(LocInfoE loc_184 (!{LPtr} (LocInfoE loc_186 (!{LPtr} (LocInfoE loc_187 ("local3"))))))) ] ;
        locinfo: loc_164 ;
        LocInfoE loc_178 ("local4") <-{ LPtr } LocInfoE loc_179 ("$0") ;
        locinfo: loc_165 ;
        assert: (LocInfoE loc_172 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_172 ((LocInfoE loc_173 (use{it_layout i32} (LocInfoE loc_175 (!{LPtr} (LocInfoE loc_176 ("local4")))))) ={IntOp i32, IntOp i32} (LocInfoE loc_177 (i2v 0 i32)))))) ;
        locinfo: loc_166 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_171 ;
        if: LocInfoE loc_171 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_171 (i2v 1 i32)))
        then
        locinfo: loc_169 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_169 ;
        Goto "continue18"
      ]> $
      <[ "#3" :=
        Return (VOID)
      ]> $
      <[ "continue18" :=
        locinfo: loc_166 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [reverse]. *)
  Definition impl_reverse : function := {|
    f_args := [
      ("p", LPtr)
    ];
    f_local_vars := [
      ("v", LPtr);
      ("w", LPtr);
      ("t", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_227 ;
        LocInfoE loc_264 ("w") <-{ LPtr } LocInfoE loc_265 (NULL) ;
        locinfo: loc_228 ;
        LocInfoE loc_261 ("v") <-{ LPtr }
          LocInfoE loc_262 (use{LPtr} (LocInfoE loc_263 ("p"))) ;
        locinfo: loc_229 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_257 ;
        if: LocInfoE loc_257 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_257 ((LocInfoE loc_258 (use{LPtr} (LocInfoE loc_259 ("v")))) !={PtrOp, PtrOp} (LocInfoE loc_260 (NULL)))))
        then
        locinfo: loc_235 ;
          Goto "#2"
        else
        locinfo: loc_230 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_235 ;
        LocInfoE loc_252 ("t") <-{ LPtr }
          LocInfoE loc_253 (use{LPtr} (LocInfoE loc_254 ((LocInfoE loc_255 (!{LPtr} (LocInfoE loc_256 ("v")))) at{struct_list} "tail"))) ;
        locinfo: loc_236 ;
        LocInfoE loc_247 ((LocInfoE loc_248 (!{LPtr} (LocInfoE loc_249 ("v")))) at{struct_list} "tail") <-{ LPtr }
          LocInfoE loc_250 (use{LPtr} (LocInfoE loc_251 ("w"))) ;
        locinfo: loc_237 ;
        LocInfoE loc_244 ("w") <-{ LPtr }
          LocInfoE loc_245 (use{LPtr} (LocInfoE loc_246 ("v"))) ;
        locinfo: loc_238 ;
        LocInfoE loc_241 ("v") <-{ LPtr }
          LocInfoE loc_242 (use{LPtr} (LocInfoE loc_243 ("t"))) ;
        locinfo: loc_239 ;
        Goto "continue21"
      ]> $
      <[ "#3" :=
        locinfo: loc_230 ;
        Return (LocInfoE loc_231 (use{LPtr} (LocInfoE loc_232 ("w"))))
      ]> $
      <[ "continue21" :=
        locinfo: loc_229 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [forward]. *)
  Definition impl_forward : function := {|
    f_args := [
      ("p", LPtr)
    ];
    f_local_vars := [
      ("prev", LPtr);
      ("cur", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "prev" <-{ LPtr } LocInfoE loc_302 (&(LocInfoE loc_303 ("p"))) ;
        locinfo: loc_269 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_296 ;
        if: LocInfoE loc_296 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_296 ((LocInfoE loc_297 (use{LPtr} (LocInfoE loc_299 (!{LPtr} (LocInfoE loc_300 ("prev")))))) !={PtrOp, PtrOp} (LocInfoE loc_301 (NULL)))))
        then
        Goto "#2"
        else
        locinfo: loc_270 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        "cur" <-{ LPtr }
          LocInfoE loc_290 (use{LPtr} (LocInfoE loc_292 (!{LPtr} (LocInfoE loc_293 ("prev"))))) ;
        locinfo: loc_282 ;
        LocInfoE loc_285 ("prev") <-{ LPtr }
          LocInfoE loc_286 (&(LocInfoE loc_287 ((LocInfoE loc_288 (!{LPtr} (LocInfoE loc_289 ("cur")))) at{struct_list} "tail"))) ;
        locinfo: loc_283 ;
        Goto "continue25"
      ]> $
      <[ "#3" :=
        locinfo: loc_270 ;
        expr: (LocInfoE loc_275 (&(LocInfoE loc_277 (!{LPtr} (LocInfoE loc_278 ("prev")))))) ;
        locinfo: loc_272 ;
        Return (LocInfoE loc_273 (use{LPtr} (LocInfoE loc_274 ("p"))))
      ]> $
      <[ "continue25" :=
        locinfo: loc_269 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.
End code.
