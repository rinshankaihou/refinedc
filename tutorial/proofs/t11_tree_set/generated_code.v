From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/t11_tree_set.c]. *)
Section code.
  Definition file_0 : string := "tutorial/t11_tree_set.c".
  Definition file_1 : string := "include/refinedc.h".
  Definition loc_2 : location_info := LocationInfo file_1 63 2 63 47.
  Definition loc_3 : location_info := LocationInfo file_1 63 9 63 46.
  Definition loc_4 : location_info := LocationInfo file_1 63 9 63 32.
  Definition loc_5 : location_info := LocationInfo file_1 63 33 63 37.
  Definition loc_6 : location_info := LocationInfo file_1 63 33 63 37.
  Definition loc_7 : location_info := LocationInfo file_1 63 39 63 45.
  Definition loc_8 : location_info := LocationInfo file_1 63 39 63 45.
  Definition loc_11 : location_info := LocationInfo file_0 26 2 26 24.
  Definition loc_12 : location_info := LocationInfo file_0 26 9 26 23.
  Definition loc_15 : location_info := LocationInfo file_0 35 2 35 50.
  Definition loc_16 : location_info := LocationInfo file_0 36 2 36 30.
  Definition loc_17 : location_info := LocationInfo file_0 37 2 37 18.
  Definition loc_18 : location_info := LocationInfo file_0 38 2 38 31.
  Definition loc_19 : location_info := LocationInfo file_0 39 2 39 14.
  Definition loc_20 : location_info := LocationInfo file_0 39 9 39 13.
  Definition loc_21 : location_info := LocationInfo file_0 39 9 39 13.
  Definition loc_22 : location_info := LocationInfo file_0 38 2 38 13.
  Definition loc_23 : location_info := LocationInfo file_0 38 2 38 6.
  Definition loc_24 : location_info := LocationInfo file_0 38 2 38 6.
  Definition loc_25 : location_info := LocationInfo file_0 38 16 38 30.
  Definition loc_26 : location_info := LocationInfo file_0 37 2 37 11.
  Definition loc_27 : location_info := LocationInfo file_0 37 2 37 6.
  Definition loc_28 : location_info := LocationInfo file_0 37 2 37 6.
  Definition loc_29 : location_info := LocationInfo file_0 37 14 37 17.
  Definition loc_30 : location_info := LocationInfo file_0 37 14 37 17.
  Definition loc_31 : location_info := LocationInfo file_0 36 2 36 12.
  Definition loc_32 : location_info := LocationInfo file_0 36 2 36 6.
  Definition loc_33 : location_info := LocationInfo file_0 36 2 36 6.
  Definition loc_34 : location_info := LocationInfo file_0 36 15 36 29.
  Definition loc_35 : location_info := LocationInfo file_0 35 22 35 49.
  Definition loc_36 : location_info := LocationInfo file_0 35 22 35 28.
  Definition loc_37 : location_info := LocationInfo file_0 35 22 35 28.
  Definition loc_38 : location_info := LocationInfo file_0 35 29 35 48.
  Definition loc_43 : location_info := LocationInfo file_0 49 2 49 50.
  Definition loc_44 : location_info := LocationInfo file_0 50 2 50 20.
  Definition loc_45 : location_info := LocationInfo file_0 51 2 51 18.
  Definition loc_46 : location_info := LocationInfo file_0 52 2 52 22.
  Definition loc_47 : location_info := LocationInfo file_0 53 2 53 14.
  Definition loc_48 : location_info := LocationInfo file_0 53 9 53 13.
  Definition loc_49 : location_info := LocationInfo file_0 53 9 53 13.
  Definition loc_50 : location_info := LocationInfo file_0 52 2 52 13.
  Definition loc_51 : location_info := LocationInfo file_0 52 2 52 6.
  Definition loc_52 : location_info := LocationInfo file_0 52 2 52 6.
  Definition loc_53 : location_info := LocationInfo file_0 52 16 52 21.
  Definition loc_54 : location_info := LocationInfo file_0 52 16 52 21.
  Definition loc_55 : location_info := LocationInfo file_0 51 2 51 11.
  Definition loc_56 : location_info := LocationInfo file_0 51 2 51 6.
  Definition loc_57 : location_info := LocationInfo file_0 51 2 51 6.
  Definition loc_58 : location_info := LocationInfo file_0 51 14 51 17.
  Definition loc_59 : location_info := LocationInfo file_0 51 14 51 17.
  Definition loc_60 : location_info := LocationInfo file_0 50 2 50 12.
  Definition loc_61 : location_info := LocationInfo file_0 50 2 50 6.
  Definition loc_62 : location_info := LocationInfo file_0 50 2 50 6.
  Definition loc_63 : location_info := LocationInfo file_0 50 15 50 19.
  Definition loc_64 : location_info := LocationInfo file_0 50 15 50 19.
  Definition loc_65 : location_info := LocationInfo file_0 49 22 49 49.
  Definition loc_66 : location_info := LocationInfo file_0 49 22 49 28.
  Definition loc_67 : location_info := LocationInfo file_0 49 22 49 28.
  Definition loc_68 : location_info := LocationInfo file_0 49 29 49 48.
  Definition loc_73 : location_info := LocationInfo file_0 61 2 65 3.
  Definition loc_74 : location_info := LocationInfo file_0 61 26 65 3.
  Definition loc_75 : location_info := LocationInfo file_0 62 4 62 29.
  Definition loc_76 : location_info := LocationInfo file_0 63 4 63 30.
  Definition loc_77 : location_info := LocationInfo file_0 64 4 64 35.
  Definition loc_78 : location_info := LocationInfo file_0 64 4 64 9.
  Definition loc_79 : location_info := LocationInfo file_0 64 4 64 9.
  Definition loc_80 : location_info := LocationInfo file_0 64 10 64 29.
  Definition loc_81 : location_info := LocationInfo file_0 64 31 64 33.
  Definition loc_82 : location_info := LocationInfo file_0 64 31 64 33.
  Definition loc_83 : location_info := LocationInfo file_0 64 32 64 33.
  Definition loc_84 : location_info := LocationInfo file_0 64 32 64 33.
  Definition loc_85 : location_info := LocationInfo file_0 63 4 63 13.
  Definition loc_86 : location_info := LocationInfo file_0 63 4 63 13.
  Definition loc_87 : location_info := LocationInfo file_0 63 14 63 28.
  Definition loc_88 : location_info := LocationInfo file_0 63 15 63 28.
  Definition loc_89 : location_info := LocationInfo file_0 63 16 63 20.
  Definition loc_90 : location_info := LocationInfo file_0 63 16 63 20.
  Definition loc_91 : location_info := LocationInfo file_0 63 18 63 19.
  Definition loc_92 : location_info := LocationInfo file_0 63 18 63 19.
  Definition loc_93 : location_info := LocationInfo file_0 62 4 62 13.
  Definition loc_94 : location_info := LocationInfo file_0 62 4 62 13.
  Definition loc_95 : location_info := LocationInfo file_0 62 14 62 27.
  Definition loc_96 : location_info := LocationInfo file_0 62 15 62 27.
  Definition loc_97 : location_info := LocationInfo file_0 62 16 62 20.
  Definition loc_98 : location_info := LocationInfo file_0 62 16 62 20.
  Definition loc_99 : location_info := LocationInfo file_0 62 18 62 19.
  Definition loc_100 : location_info := LocationInfo file_0 62 18 62 19.
  Definition loc_101 : location_info := LocationInfo file_0 61 2 65 3.
  Definition loc_102 : location_info := LocationInfo file_0 61 5 61 25.
  Definition loc_103 : location_info := LocationInfo file_0 61 5 61 7.
  Definition loc_104 : location_info := LocationInfo file_0 61 5 61 7.
  Definition loc_105 : location_info := LocationInfo file_0 61 6 61 7.
  Definition loc_106 : location_info := LocationInfo file_0 61 6 61 7.
  Definition loc_107 : location_info := LocationInfo file_0 61 11 61 25.
  Definition loc_110 : location_info := LocationInfo file_0 74 2 74 36.
  Definition loc_111 : location_info := LocationInfo file_0 75 2 75 30.
  Definition loc_112 : location_info := LocationInfo file_0 76 2 76 56.
  Definition loc_113 : location_info := LocationInfo file_0 77 2 77 39.
  Definition loc_114 : location_info := LocationInfo file_0 77 9 77 38.
  Definition loc_115 : location_info := LocationInfo file_0 77 9 77 19.
  Definition loc_116 : location_info := LocationInfo file_0 77 9 77 19.
  Definition loc_117 : location_info := LocationInfo file_0 77 20 77 34.
  Definition loc_118 : location_info := LocationInfo file_0 77 21 77 34.
  Definition loc_119 : location_info := LocationInfo file_0 77 22 77 26.
  Definition loc_120 : location_info := LocationInfo file_0 77 22 77 26.
  Definition loc_121 : location_info := LocationInfo file_0 77 24 77 25.
  Definition loc_122 : location_info := LocationInfo file_0 77 24 77 25.
  Definition loc_123 : location_info := LocationInfo file_0 77 36 77 37.
  Definition loc_124 : location_info := LocationInfo file_0 77 36 77 37.
  Definition loc_125 : location_info := LocationInfo file_0 76 20 76 56.
  Definition loc_126 : location_info := LocationInfo file_0 76 27 76 55.
  Definition loc_127 : location_info := LocationInfo file_0 76 27 76 37.
  Definition loc_128 : location_info := LocationInfo file_0 76 27 76 37.
  Definition loc_129 : location_info := LocationInfo file_0 76 38 76 51.
  Definition loc_130 : location_info := LocationInfo file_0 76 39 76 51.
  Definition loc_131 : location_info := LocationInfo file_0 76 40 76 44.
  Definition loc_132 : location_info := LocationInfo file_0 76 40 76 44.
  Definition loc_133 : location_info := LocationInfo file_0 76 42 76 43.
  Definition loc_134 : location_info := LocationInfo file_0 76 42 76 43.
  Definition loc_135 : location_info := LocationInfo file_0 76 53 76 54.
  Definition loc_136 : location_info := LocationInfo file_0 76 53 76 54.
  Definition loc_137 : location_info := LocationInfo file_0 76 2 76 56.
  Definition loc_138 : location_info := LocationInfo file_0 76 5 76 18.
  Definition loc_139 : location_info := LocationInfo file_0 76 5 76 6.
  Definition loc_140 : location_info := LocationInfo file_0 76 5 76 6.
  Definition loc_141 : location_info := LocationInfo file_0 76 9 76 18.
  Definition loc_142 : location_info := LocationInfo file_0 76 9 76 18.
  Definition loc_143 : location_info := LocationInfo file_0 76 9 76 13.
  Definition loc_144 : location_info := LocationInfo file_0 76 9 76 13.
  Definition loc_145 : location_info := LocationInfo file_0 76 11 76 12.
  Definition loc_146 : location_info := LocationInfo file_0 76 11 76 12.
  Definition loc_147 : location_info := LocationInfo file_0 75 21 75 30.
  Definition loc_148 : location_info := LocationInfo file_0 75 28 75 29.
  Definition loc_149 : location_info := LocationInfo file_0 75 2 75 30.
  Definition loc_150 : location_info := LocationInfo file_0 75 5 75 19.
  Definition loc_151 : location_info := LocationInfo file_0 75 5 75 14.
  Definition loc_152 : location_info := LocationInfo file_0 75 5 75 14.
  Definition loc_153 : location_info := LocationInfo file_0 75 5 75 9.
  Definition loc_154 : location_info := LocationInfo file_0 75 5 75 9.
  Definition loc_155 : location_info := LocationInfo file_0 75 7 75 8.
  Definition loc_156 : location_info := LocationInfo file_0 75 7 75 8.
  Definition loc_157 : location_info := LocationInfo file_0 75 18 75 19.
  Definition loc_158 : location_info := LocationInfo file_0 75 18 75 19.
  Definition loc_159 : location_info := LocationInfo file_0 74 27 74 36.
  Definition loc_160 : location_info := LocationInfo file_0 74 34 74 35.
  Definition loc_161 : location_info := LocationInfo file_0 74 2 74 36.
  Definition loc_162 : location_info := LocationInfo file_0 74 5 74 25.
  Definition loc_163 : location_info := LocationInfo file_0 74 5 74 7.
  Definition loc_164 : location_info := LocationInfo file_0 74 5 74 7.
  Definition loc_165 : location_info := LocationInfo file_0 74 6 74 7.
  Definition loc_166 : location_info := LocationInfo file_0 74 6 74 7.
  Definition loc_167 : location_info := LocationInfo file_0 74 11 74 25.
  Definition loc_170 : location_info := LocationInfo file_0 86 2 86 20.
  Definition loc_171 : location_info := LocationInfo file_0 92 2 99 3.
  Definition loc_172 : location_info := LocationInfo file_0 100 2 100 11.
  Definition loc_173 : location_info := LocationInfo file_0 100 9 100 10.
  Definition loc_174 : location_info := LocationInfo file_0 92 31 99 3.
  Definition loc_175 : location_info := LocationInfo file_0 93 4 93 34.
  Definition loc_176 : location_info := LocationInfo file_0 94 4 98 5.
  Definition loc_177 : location_info := LocationInfo file_0 94 23 96 5.
  Definition loc_178 : location_info := LocationInfo file_0 95 6 95 28.
  Definition loc_179 : location_info := LocationInfo file_0 95 6 95 9.
  Definition loc_180 : location_info := LocationInfo file_0 95 12 95 27.
  Definition loc_181 : location_info := LocationInfo file_0 95 13 95 27.
  Definition loc_182 : location_info := LocationInfo file_0 95 14 95 20.
  Definition loc_183 : location_info := LocationInfo file_0 95 14 95 20.
  Definition loc_184 : location_info := LocationInfo file_0 95 16 95 19.
  Definition loc_185 : location_info := LocationInfo file_0 95 16 95 19.
  Definition loc_186 : location_info := LocationInfo file_0 96 11 98 5.
  Definition loc_187 : location_info := LocationInfo file_0 97 6 97 29.
  Definition loc_188 : location_info := LocationInfo file_0 97 6 97 9.
  Definition loc_189 : location_info := LocationInfo file_0 97 12 97 28.
  Definition loc_190 : location_info := LocationInfo file_0 97 13 97 28.
  Definition loc_191 : location_info := LocationInfo file_0 97 14 97 20.
  Definition loc_192 : location_info := LocationInfo file_0 97 14 97 20.
  Definition loc_193 : location_info := LocationInfo file_0 97 16 97 19.
  Definition loc_194 : location_info := LocationInfo file_0 97 16 97 19.
  Definition loc_195 : location_info := LocationInfo file_0 94 7 94 22.
  Definition loc_196 : location_info := LocationInfo file_0 94 7 94 8.
  Definition loc_197 : location_info := LocationInfo file_0 94 7 94 8.
  Definition loc_198 : location_info := LocationInfo file_0 94 11 94 22.
  Definition loc_199 : location_info := LocationInfo file_0 94 11 94 22.
  Definition loc_200 : location_info := LocationInfo file_0 94 11 94 17.
  Definition loc_201 : location_info := LocationInfo file_0 94 11 94 17.
  Definition loc_202 : location_info := LocationInfo file_0 94 13 94 16.
  Definition loc_203 : location_info := LocationInfo file_0 94 13 94 16.
  Definition loc_204 : location_info := LocationInfo file_0 93 25 93 34.
  Definition loc_205 : location_info := LocationInfo file_0 93 32 93 33.
  Definition loc_206 : location_info := LocationInfo file_0 93 4 93 34.
  Definition loc_207 : location_info := LocationInfo file_0 93 7 93 23.
  Definition loc_208 : location_info := LocationInfo file_0 93 7 93 18.
  Definition loc_209 : location_info := LocationInfo file_0 93 7 93 18.
  Definition loc_210 : location_info := LocationInfo file_0 93 7 93 13.
  Definition loc_211 : location_info := LocationInfo file_0 93 7 93 13.
  Definition loc_212 : location_info := LocationInfo file_0 93 9 93 12.
  Definition loc_213 : location_info := LocationInfo file_0 93 9 93 12.
  Definition loc_214 : location_info := LocationInfo file_0 93 22 93 23.
  Definition loc_215 : location_info := LocationInfo file_0 93 22 93 23.
  Definition loc_216 : location_info := LocationInfo file_0 92 8 92 30.
  Definition loc_217 : location_info := LocationInfo file_0 92 8 92 12.
  Definition loc_218 : location_info := LocationInfo file_0 92 8 92 12.
  Definition loc_219 : location_info := LocationInfo file_0 92 9 92 12.
  Definition loc_220 : location_info := LocationInfo file_0 92 9 92 12.
  Definition loc_221 : location_info := LocationInfo file_0 92 16 92 30.
  Definition loc_222 : location_info := LocationInfo file_0 86 16 86 19.
  Definition loc_223 : location_info := LocationInfo file_0 86 17 86 19.
  Definition loc_224 : location_info := LocationInfo file_0 86 18 86 19.
  Definition loc_225 : location_info := LocationInfo file_0 86 18 86 19.
  Definition loc_230 : location_info := LocationInfo file_0 109 2 119 3.
  Definition loc_231 : location_info := LocationInfo file_0 109 27 111 3.
  Definition loc_232 : location_info := LocationInfo file_0 110 4 110 49.
  Definition loc_233 : location_info := LocationInfo file_0 110 4 110 6.
  Definition loc_234 : location_info := LocationInfo file_0 110 5 110 6.
  Definition loc_235 : location_info := LocationInfo file_0 110 5 110 6.
  Definition loc_236 : location_info := LocationInfo file_0 110 9 110 48.
  Definition loc_237 : location_info := LocationInfo file_0 110 9 110 13.
  Definition loc_238 : location_info := LocationInfo file_0 110 9 110 13.
  Definition loc_239 : location_info := LocationInfo file_0 110 14 110 28.
  Definition loc_240 : location_info := LocationInfo file_0 110 30 110 31.
  Definition loc_241 : location_info := LocationInfo file_0 110 30 110 31.
  Definition loc_242 : location_info := LocationInfo file_0 110 33 110 47.
  Definition loc_243 : location_info := LocationInfo file_0 111 9 119 3.
  Definition loc_244 : location_info := LocationInfo file_0 112 4 118 5.
  Definition loc_245 : location_info := LocationInfo file_0 112 23 114 5.
  Definition loc_246 : location_info := LocationInfo file_0 113 6 113 13.
  Definition loc_248 : location_info := LocationInfo file_0 114 11 118 5.
  Definition loc_249 : location_info := LocationInfo file_0 114 29 116 5.
  Definition loc_250 : location_info := LocationInfo file_0 115 6 115 35.
  Definition loc_251 : location_info := LocationInfo file_0 115 6 115 16.
  Definition loc_252 : location_info := LocationInfo file_0 115 6 115 16.
  Definition loc_253 : location_info := LocationInfo file_0 115 17 115 30.
  Definition loc_254 : location_info := LocationInfo file_0 115 18 115 30.
  Definition loc_255 : location_info := LocationInfo file_0 115 19 115 23.
  Definition loc_256 : location_info := LocationInfo file_0 115 19 115 23.
  Definition loc_257 : location_info := LocationInfo file_0 115 21 115 22.
  Definition loc_258 : location_info := LocationInfo file_0 115 21 115 22.
  Definition loc_259 : location_info := LocationInfo file_0 115 32 115 33.
  Definition loc_260 : location_info := LocationInfo file_0 115 32 115 33.
  Definition loc_261 : location_info := LocationInfo file_0 116 11 118 5.
  Definition loc_262 : location_info := LocationInfo file_0 117 6 117 36.
  Definition loc_263 : location_info := LocationInfo file_0 117 6 117 16.
  Definition loc_264 : location_info := LocationInfo file_0 117 6 117 16.
  Definition loc_265 : location_info := LocationInfo file_0 117 17 117 31.
  Definition loc_266 : location_info := LocationInfo file_0 117 18 117 31.
  Definition loc_267 : location_info := LocationInfo file_0 117 19 117 23.
  Definition loc_268 : location_info := LocationInfo file_0 117 19 117 23.
  Definition loc_269 : location_info := LocationInfo file_0 117 21 117 22.
  Definition loc_270 : location_info := LocationInfo file_0 117 21 117 22.
  Definition loc_271 : location_info := LocationInfo file_0 117 33 117 34.
  Definition loc_272 : location_info := LocationInfo file_0 117 33 117 34.
  Definition loc_273 : location_info := LocationInfo file_0 114 14 114 27.
  Definition loc_274 : location_info := LocationInfo file_0 114 14 114 15.
  Definition loc_275 : location_info := LocationInfo file_0 114 14 114 15.
  Definition loc_276 : location_info := LocationInfo file_0 114 18 114 27.
  Definition loc_277 : location_info := LocationInfo file_0 114 18 114 27.
  Definition loc_278 : location_info := LocationInfo file_0 114 18 114 22.
  Definition loc_279 : location_info := LocationInfo file_0 114 18 114 22.
  Definition loc_280 : location_info := LocationInfo file_0 114 20 114 21.
  Definition loc_281 : location_info := LocationInfo file_0 114 20 114 21.
  Definition loc_282 : location_info := LocationInfo file_0 112 7 112 21.
  Definition loc_283 : location_info := LocationInfo file_0 112 7 112 16.
  Definition loc_284 : location_info := LocationInfo file_0 112 7 112 16.
  Definition loc_285 : location_info := LocationInfo file_0 112 7 112 11.
  Definition loc_286 : location_info := LocationInfo file_0 112 7 112 11.
  Definition loc_287 : location_info := LocationInfo file_0 112 9 112 10.
  Definition loc_288 : location_info := LocationInfo file_0 112 9 112 10.
  Definition loc_289 : location_info := LocationInfo file_0 112 20 112 21.
  Definition loc_290 : location_info := LocationInfo file_0 112 20 112 21.
  Definition loc_291 : location_info := LocationInfo file_0 109 5 109 25.
  Definition loc_292 : location_info := LocationInfo file_0 109 5 109 7.
  Definition loc_293 : location_info := LocationInfo file_0 109 5 109 7.
  Definition loc_294 : location_info := LocationInfo file_0 109 6 109 7.
  Definition loc_295 : location_info := LocationInfo file_0 109 6 109 7.
  Definition loc_296 : location_info := LocationInfo file_0 109 11 109 25.
  Definition loc_299 : location_info := LocationInfo file_0 128 2 128 20.
  Definition loc_300 : location_info := LocationInfo file_0 133 2 140 3.
  Definition loc_301 : location_info := LocationInfo file_0 142 2 142 49.
  Definition loc_302 : location_info := LocationInfo file_0 142 2 142 6.
  Definition loc_303 : location_info := LocationInfo file_0 142 3 142 6.
  Definition loc_304 : location_info := LocationInfo file_0 142 3 142 6.
  Definition loc_305 : location_info := LocationInfo file_0 142 9 142 48.
  Definition loc_306 : location_info := LocationInfo file_0 142 9 142 13.
  Definition loc_307 : location_info := LocationInfo file_0 142 9 142 13.
  Definition loc_308 : location_info := LocationInfo file_0 142 14 142 28.
  Definition loc_309 : location_info := LocationInfo file_0 142 30 142 31.
  Definition loc_310 : location_info := LocationInfo file_0 142 30 142 31.
  Definition loc_311 : location_info := LocationInfo file_0 142 33 142 47.
  Definition loc_312 : location_info := LocationInfo file_0 133 31 140 3.
  Definition loc_313 : location_info := LocationInfo file_0 134 4 134 32.
  Definition loc_314 : location_info := LocationInfo file_0 135 4 139 5.
  Definition loc_315 : location_info := LocationInfo file_0 135 23 137 5.
  Definition loc_316 : location_info := LocationInfo file_0 136 6 136 28.
  Definition loc_317 : location_info := LocationInfo file_0 136 6 136 9.
  Definition loc_318 : location_info := LocationInfo file_0 136 12 136 27.
  Definition loc_319 : location_info := LocationInfo file_0 136 13 136 27.
  Definition loc_320 : location_info := LocationInfo file_0 136 14 136 20.
  Definition loc_321 : location_info := LocationInfo file_0 136 14 136 20.
  Definition loc_322 : location_info := LocationInfo file_0 136 16 136 19.
  Definition loc_323 : location_info := LocationInfo file_0 136 16 136 19.
  Definition loc_324 : location_info := LocationInfo file_0 137 11 139 5.
  Definition loc_325 : location_info := LocationInfo file_0 138 6 138 29.
  Definition loc_326 : location_info := LocationInfo file_0 138 6 138 9.
  Definition loc_327 : location_info := LocationInfo file_0 138 12 138 28.
  Definition loc_328 : location_info := LocationInfo file_0 138 13 138 28.
  Definition loc_329 : location_info := LocationInfo file_0 138 14 138 20.
  Definition loc_330 : location_info := LocationInfo file_0 138 14 138 20.
  Definition loc_331 : location_info := LocationInfo file_0 138 16 138 19.
  Definition loc_332 : location_info := LocationInfo file_0 138 16 138 19.
  Definition loc_333 : location_info := LocationInfo file_0 135 7 135 22.
  Definition loc_334 : location_info := LocationInfo file_0 135 7 135 8.
  Definition loc_335 : location_info := LocationInfo file_0 135 7 135 8.
  Definition loc_336 : location_info := LocationInfo file_0 135 11 135 22.
  Definition loc_337 : location_info := LocationInfo file_0 135 11 135 22.
  Definition loc_338 : location_info := LocationInfo file_0 135 11 135 17.
  Definition loc_339 : location_info := LocationInfo file_0 135 11 135 17.
  Definition loc_340 : location_info := LocationInfo file_0 135 13 135 16.
  Definition loc_341 : location_info := LocationInfo file_0 135 13 135 16.
  Definition loc_342 : location_info := LocationInfo file_0 134 25 134 32.
  Definition loc_344 : location_info := LocationInfo file_0 134 4 134 32.
  Definition loc_345 : location_info := LocationInfo file_0 134 7 134 23.
  Definition loc_346 : location_info := LocationInfo file_0 134 7 134 18.
  Definition loc_347 : location_info := LocationInfo file_0 134 7 134 18.
  Definition loc_348 : location_info := LocationInfo file_0 134 7 134 13.
  Definition loc_349 : location_info := LocationInfo file_0 134 7 134 13.
  Definition loc_350 : location_info := LocationInfo file_0 134 9 134 12.
  Definition loc_351 : location_info := LocationInfo file_0 134 9 134 12.
  Definition loc_352 : location_info := LocationInfo file_0 134 22 134 23.
  Definition loc_353 : location_info := LocationInfo file_0 134 22 134 23.
  Definition loc_354 : location_info := LocationInfo file_0 133 8 133 30.
  Definition loc_355 : location_info := LocationInfo file_0 133 8 133 12.
  Definition loc_356 : location_info := LocationInfo file_0 133 8 133 12.
  Definition loc_357 : location_info := LocationInfo file_0 133 9 133 12.
  Definition loc_358 : location_info := LocationInfo file_0 133 9 133 12.
  Definition loc_359 : location_info := LocationInfo file_0 133 16 133 30.
  Definition loc_360 : location_info := LocationInfo file_0 128 16 128 19.
  Definition loc_361 : location_info := LocationInfo file_0 128 17 128 19.
  Definition loc_362 : location_info := LocationInfo file_0 128 18 128 19.
  Definition loc_363 : location_info := LocationInfo file_0 128 18 128 19.
  Definition loc_368 : location_info := LocationInfo file_0 154 2 156 3.
  Definition loc_369 : location_info := LocationInfo file_0 157 2 157 34.
  Definition loc_370 : location_info := LocationInfo file_0 157 9 157 33.
  Definition loc_371 : location_info := LocationInfo file_0 157 9 157 17.
  Definition loc_372 : location_info := LocationInfo file_0 157 9 157 17.
  Definition loc_373 : location_info := LocationInfo file_0 157 18 157 32.
  Definition loc_374 : location_info := LocationInfo file_0 157 19 157 32.
  Definition loc_375 : location_info := LocationInfo file_0 157 20 157 24.
  Definition loc_376 : location_info := LocationInfo file_0 157 20 157 24.
  Definition loc_377 : location_info := LocationInfo file_0 157 22 157 23.
  Definition loc_378 : location_info := LocationInfo file_0 157 22 157 23.
  Definition loc_379 : location_info := LocationInfo file_0 154 36 156 3.
  Definition loc_380 : location_info := LocationInfo file_0 155 4 155 21.
  Definition loc_381 : location_info := LocationInfo file_0 155 11 155 20.
  Definition loc_382 : location_info := LocationInfo file_0 155 11 155 20.
  Definition loc_383 : location_info := LocationInfo file_0 155 11 155 15.
  Definition loc_384 : location_info := LocationInfo file_0 155 11 155 15.
  Definition loc_385 : location_info := LocationInfo file_0 155 13 155 14.
  Definition loc_386 : location_info := LocationInfo file_0 155 13 155 14.
  Definition loc_387 : location_info := LocationInfo file_0 154 2 156 3.
  Definition loc_388 : location_info := LocationInfo file_0 154 5 154 34.
  Definition loc_389 : location_info := LocationInfo file_0 154 5 154 16.
  Definition loc_390 : location_info := LocationInfo file_0 154 5 154 16.
  Definition loc_391 : location_info := LocationInfo file_0 154 5 154 9.
  Definition loc_392 : location_info := LocationInfo file_0 154 5 154 9.
  Definition loc_393 : location_info := LocationInfo file_0 154 7 154 8.
  Definition loc_394 : location_info := LocationInfo file_0 154 7 154 8.
  Definition loc_395 : location_info := LocationInfo file_0 154 20 154 34.
  Definition loc_398 : location_info := LocationInfo file_0 168 2 168 13.
  Definition loc_399 : location_info := LocationInfo file_0 169 2 169 11.
  Definition loc_400 : location_info := LocationInfo file_0 170 2 172 3.
  Definition loc_401 : location_info := LocationInfo file_0 174 2 188 3.
  Definition loc_402 : location_info := LocationInfo file_0 174 21 184 3.
  Definition loc_403 : location_info := LocationInfo file_0 175 4 183 5.
  Definition loc_404 : location_info := LocationInfo file_0 175 36 179 5.
  Definition loc_405 : location_info := LocationInfo file_0 176 6 176 32.
  Definition loc_406 : location_info := LocationInfo file_0 177 6 177 29.
  Definition loc_407 : location_info := LocationInfo file_0 178 6 178 20.
  Definition loc_408 : location_info := LocationInfo file_0 178 6 178 15.
  Definition loc_409 : location_info := LocationInfo file_0 178 6 178 10.
  Definition loc_410 : location_info := LocationInfo file_0 178 6 178 10.
  Definition loc_411 : location_info := LocationInfo file_0 178 8 178 9.
  Definition loc_412 : location_info := LocationInfo file_0 178 8 178 9.
  Definition loc_413 : location_info := LocationInfo file_0 178 18 178 19.
  Definition loc_414 : location_info := LocationInfo file_0 178 18 178 19.
  Definition loc_415 : location_info := LocationInfo file_0 177 6 177 12.
  Definition loc_416 : location_info := LocationInfo file_0 177 6 177 12.
  Definition loc_417 : location_info := LocationInfo file_0 177 13 177 24.
  Definition loc_418 : location_info := LocationInfo file_0 177 14 177 24.
  Definition loc_419 : location_info := LocationInfo file_0 177 14 177 18.
  Definition loc_420 : location_info := LocationInfo file_0 177 14 177 18.
  Definition loc_421 : location_info := LocationInfo file_0 177 16 177 17.
  Definition loc_422 : location_info := LocationInfo file_0 177 16 177 17.
  Definition loc_423 : location_info := LocationInfo file_0 177 26 177 27.
  Definition loc_424 : location_info := LocationInfo file_0 177 26 177 27.
  Definition loc_425 : location_info := LocationInfo file_0 176 6 176 7.
  Definition loc_426 : location_info := LocationInfo file_0 176 10 176 31.
  Definition loc_427 : location_info := LocationInfo file_0 176 10 176 18.
  Definition loc_428 : location_info := LocationInfo file_0 176 10 176 18.
  Definition loc_429 : location_info := LocationInfo file_0 176 19 176 30.
  Definition loc_430 : location_info := LocationInfo file_0 176 20 176 30.
  Definition loc_431 : location_info := LocationInfo file_0 176 20 176 24.
  Definition loc_432 : location_info := LocationInfo file_0 176 20 176 24.
  Definition loc_433 : location_info := LocationInfo file_0 176 22 176 23.
  Definition loc_434 : location_info := LocationInfo file_0 176 22 176 23.
  Definition loc_435 : location_info := LocationInfo file_0 179 11 183 5.
  Definition loc_436 : location_info := LocationInfo file_0 180 6 180 24.
  Definition loc_437 : location_info := LocationInfo file_0 181 6 181 37.
  Definition loc_438 : location_info := LocationInfo file_0 182 6 182 15.
  Definition loc_439 : location_info := LocationInfo file_0 182 6 182 8.
  Definition loc_440 : location_info := LocationInfo file_0 182 7 182 8.
  Definition loc_441 : location_info := LocationInfo file_0 182 7 182 8.
  Definition loc_442 : location_info := LocationInfo file_0 182 11 182 14.
  Definition loc_443 : location_info := LocationInfo file_0 182 11 182 14.
  Definition loc_444 : location_info := LocationInfo file_0 181 6 181 11.
  Definition loc_445 : location_info := LocationInfo file_0 181 6 181 11.
  Definition loc_446 : location_info := LocationInfo file_0 181 12 181 31.
  Definition loc_447 : location_info := LocationInfo file_0 181 33 181 35.
  Definition loc_448 : location_info := LocationInfo file_0 181 33 181 35.
  Definition loc_449 : location_info := LocationInfo file_0 181 34 181 35.
  Definition loc_450 : location_info := LocationInfo file_0 181 34 181 35.
  Definition loc_451 : location_info := LocationInfo file_0 180 6 180 9.
  Definition loc_452 : location_info := LocationInfo file_0 180 12 180 23.
  Definition loc_453 : location_info := LocationInfo file_0 180 12 180 23.
  Definition loc_454 : location_info := LocationInfo file_0 180 12 180 16.
  Definition loc_455 : location_info := LocationInfo file_0 180 12 180 16.
  Definition loc_456 : location_info := LocationInfo file_0 180 14 180 15.
  Definition loc_457 : location_info := LocationInfo file_0 180 14 180 15.
  Definition loc_458 : location_info := LocationInfo file_0 175 7 175 35.
  Definition loc_459 : location_info := LocationInfo file_0 175 7 175 17.
  Definition loc_460 : location_info := LocationInfo file_0 175 7 175 17.
  Definition loc_461 : location_info := LocationInfo file_0 175 7 175 11.
  Definition loc_462 : location_info := LocationInfo file_0 175 7 175 11.
  Definition loc_463 : location_info := LocationInfo file_0 175 9 175 10.
  Definition loc_464 : location_info := LocationInfo file_0 175 9 175 10.
  Definition loc_465 : location_info := LocationInfo file_0 175 21 175 35.
  Definition loc_466 : location_info := LocationInfo file_0 184 9 188 3.
  Definition loc_467 : location_info := LocationInfo file_0 184 26 186 3.
  Definition loc_468 : location_info := LocationInfo file_0 185 4 185 27.
  Definition loc_469 : location_info := LocationInfo file_0 185 4 185 10.
  Definition loc_470 : location_info := LocationInfo file_0 185 4 185 10.
  Definition loc_471 : location_info := LocationInfo file_0 185 11 185 22.
  Definition loc_472 : location_info := LocationInfo file_0 185 12 185 22.
  Definition loc_473 : location_info := LocationInfo file_0 185 12 185 16.
  Definition loc_474 : location_info := LocationInfo file_0 185 12 185 16.
  Definition loc_475 : location_info := LocationInfo file_0 185 14 185 15.
  Definition loc_476 : location_info := LocationInfo file_0 185 14 185 15.
  Definition loc_477 : location_info := LocationInfo file_0 185 24 185 25.
  Definition loc_478 : location_info := LocationInfo file_0 185 24 185 25.
  Definition loc_479 : location_info := LocationInfo file_0 186 9 188 3.
  Definition loc_480 : location_info := LocationInfo file_0 187 4 187 28.
  Definition loc_481 : location_info := LocationInfo file_0 187 4 187 10.
  Definition loc_482 : location_info := LocationInfo file_0 187 4 187 10.
  Definition loc_483 : location_info := LocationInfo file_0 187 11 187 23.
  Definition loc_484 : location_info := LocationInfo file_0 187 12 187 23.
  Definition loc_485 : location_info := LocationInfo file_0 187 12 187 16.
  Definition loc_486 : location_info := LocationInfo file_0 187 12 187 16.
  Definition loc_487 : location_info := LocationInfo file_0 187 14 187 15.
  Definition loc_488 : location_info := LocationInfo file_0 187 14 187 15.
  Definition loc_489 : location_info := LocationInfo file_0 187 25 187 26.
  Definition loc_490 : location_info := LocationInfo file_0 187 25 187 26.
  Definition loc_491 : location_info := LocationInfo file_0 184 12 184 25.
  Definition loc_492 : location_info := LocationInfo file_0 184 12 184 13.
  Definition loc_493 : location_info := LocationInfo file_0 184 12 184 13.
  Definition loc_494 : location_info := LocationInfo file_0 184 16 184 25.
  Definition loc_495 : location_info := LocationInfo file_0 184 16 184 25.
  Definition loc_496 : location_info := LocationInfo file_0 184 16 184 20.
  Definition loc_497 : location_info := LocationInfo file_0 184 16 184 20.
  Definition loc_498 : location_info := LocationInfo file_0 184 18 184 19.
  Definition loc_499 : location_info := LocationInfo file_0 184 18 184 19.
  Definition loc_500 : location_info := LocationInfo file_0 174 5 174 19.
  Definition loc_501 : location_info := LocationInfo file_0 174 5 174 6.
  Definition loc_502 : location_info := LocationInfo file_0 174 5 174 6.
  Definition loc_503 : location_info := LocationInfo file_0 174 10 174 19.
  Definition loc_504 : location_info := LocationInfo file_0 174 10 174 19.
  Definition loc_505 : location_info := LocationInfo file_0 174 10 174 14.
  Definition loc_506 : location_info := LocationInfo file_0 174 10 174 14.
  Definition loc_507 : location_info := LocationInfo file_0 174 12 174 13.
  Definition loc_508 : location_info := LocationInfo file_0 174 12 174 13.
  Definition loc_509 : location_info := LocationInfo file_0 170 27 172 3.
  Definition loc_510 : location_info := LocationInfo file_0 171 4 171 11.
  Definition loc_512 : location_info := LocationInfo file_0 170 2 172 3.
  Definition loc_513 : location_info := LocationInfo file_0 170 5 170 25.
  Definition loc_514 : location_info := LocationInfo file_0 170 5 170 7.
  Definition loc_515 : location_info := LocationInfo file_0 170 5 170 7.
  Definition loc_516 : location_info := LocationInfo file_0 170 6 170 7.
  Definition loc_517 : location_info := LocationInfo file_0 170 6 170 7.
  Definition loc_518 : location_info := LocationInfo file_0 170 11 170 25.
  Definition loc_521 : location_info := LocationInfo file_0 194 2 194 21.
  Definition loc_522 : location_info := LocationInfo file_0 195 2 195 14.
  Definition loc_523 : location_info := LocationInfo file_0 199 2 199 16.
  Definition loc_524 : location_info := LocationInfo file_0 201 2 201 24.
  Definition loc_525 : location_info := LocationInfo file_0 202 2 202 24.
  Definition loc_526 : location_info := LocationInfo file_0 204 2 204 16.
  Definition loc_527 : location_info := LocationInfo file_0 207 2 207 16.
  Definition loc_528 : location_info := LocationInfo file_0 208 2 208 24.
  Definition loc_529 : location_info := LocationInfo file_0 210 2 210 16.
  Definition loc_530 : location_info := LocationInfo file_0 213 2 213 16.
  Definition loc_531 : location_info := LocationInfo file_0 215 2 215 11.
  Definition loc_532 : location_info := LocationInfo file_0 215 9 215 10.
  Definition loc_533 : location_info := LocationInfo file_0 213 2 213 11.
  Definition loc_534 : location_info := LocationInfo file_0 213 2 213 11.
  Definition loc_535 : location_info := LocationInfo file_0 213 12 213 14.
  Definition loc_536 : location_info := LocationInfo file_0 213 13 213 14.
  Definition loc_537 : location_info := LocationInfo file_0 210 2 210 8.
  Definition loc_538 : location_info := LocationInfo file_0 210 2 210 8.
  Definition loc_539 : location_info := LocationInfo file_0 210 9 210 11.
  Definition loc_540 : location_info := LocationInfo file_0 210 10 210 11.
  Definition loc_541 : location_info := LocationInfo file_0 210 13 210 14.
  Definition loc_542 : location_info := LocationInfo file_0 208 9 208 22.
  Definition loc_543 : location_info := LocationInfo file_0 208 9 208 15.
  Definition loc_544 : location_info := LocationInfo file_0 208 9 208 15.
  Definition loc_545 : location_info := LocationInfo file_0 208 16 208 18.
  Definition loc_546 : location_info := LocationInfo file_0 208 17 208 18.
  Definition loc_547 : location_info := LocationInfo file_0 208 20 208 21.
  Definition loc_548 : location_info := LocationInfo file_0 207 2 207 8.
  Definition loc_549 : location_info := LocationInfo file_0 207 2 207 8.
  Definition loc_550 : location_info := LocationInfo file_0 207 9 207 11.
  Definition loc_551 : location_info := LocationInfo file_0 207 10 207 11.
  Definition loc_552 : location_info := LocationInfo file_0 207 13 207 14.
  Definition loc_553 : location_info := LocationInfo file_0 204 2 204 8.
  Definition loc_554 : location_info := LocationInfo file_0 204 2 204 8.
  Definition loc_555 : location_info := LocationInfo file_0 204 9 204 11.
  Definition loc_556 : location_info := LocationInfo file_0 204 10 204 11.
  Definition loc_557 : location_info := LocationInfo file_0 204 13 204 14.
  Definition loc_558 : location_info := LocationInfo file_0 202 9 202 22.
  Definition loc_559 : location_info := LocationInfo file_0 202 9 202 15.
  Definition loc_560 : location_info := LocationInfo file_0 202 9 202 15.
  Definition loc_561 : location_info := LocationInfo file_0 202 16 202 18.
  Definition loc_562 : location_info := LocationInfo file_0 202 17 202 18.
  Definition loc_563 : location_info := LocationInfo file_0 202 20 202 21.
  Definition loc_564 : location_info := LocationInfo file_0 201 9 201 22.
  Definition loc_565 : location_info := LocationInfo file_0 201 9 201 15.
  Definition loc_566 : location_info := LocationInfo file_0 201 9 201 15.
  Definition loc_567 : location_info := LocationInfo file_0 201 16 201 18.
  Definition loc_568 : location_info := LocationInfo file_0 201 17 201 18.
  Definition loc_569 : location_info := LocationInfo file_0 201 20 201 21.
  Definition loc_570 : location_info := LocationInfo file_0 199 2 199 8.
  Definition loc_571 : location_info := LocationInfo file_0 199 2 199 8.
  Definition loc_572 : location_info := LocationInfo file_0 199 9 199 11.
  Definition loc_573 : location_info := LocationInfo file_0 199 10 199 11.
  Definition loc_574 : location_info := LocationInfo file_0 199 13 199 14.
  Definition loc_575 : location_info := LocationInfo file_0 195 2 195 3.
  Definition loc_576 : location_info := LocationInfo file_0 195 6 195 13.
  Definition loc_577 : location_info := LocationInfo file_0 195 6 195 10.
  Definition loc_578 : location_info := LocationInfo file_0 195 6 195 10.
  Definition loc_579 : location_info := LocationInfo file_0 195 11 195 12.
  Definition loc_580 : location_info := LocationInfo file_0 194 13 194 20.
  Definition loc_581 : location_info := LocationInfo file_0 194 13 194 18.
  Definition loc_582 : location_info := LocationInfo file_0 194 13 194 18.

  (* Definition of struct [__cerbty_unnamed_tag_520]. *)
  Program Definition struct___cerbty_unnamed_tag_520 := {|
    sl_members := [
      (Some "__dummy_max_align_t", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [tree]. *)
  Program Definition struct_tree := {|
    sl_members := [
      (Some "left", void*);
      (Some "right", void*);
      (Some "key", it_layout size_t)
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

  (* Definition of function [empty]. *)
  Definition impl_empty : function := {|
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

  (* Definition of function [init]. *)
  Definition impl_init (global_talloc : loc): function := {|
    f_args := [
      ("key", it_layout size_t)
    ];
    f_local_vars := [
      ("node", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "node" <-{ PtrOp }
          LocInfoE loc_35 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_35 (Call (LocInfoE loc_37 (global_talloc)) [@{expr} LocInfoE loc_38 (i2v (layout_of struct_tree).(ly_size) size_t) ]))) ;
        locinfo: loc_16 ;
        LocInfoE loc_31 ((LocInfoE loc_32 (!{PtrOp} (LocInfoE loc_33 ("node")))) at{struct_tree} "left") <-{ PtrOp }
          LocInfoE loc_34 (NULL) ;
        locinfo: loc_17 ;
        LocInfoE loc_26 ((LocInfoE loc_27 (!{PtrOp} (LocInfoE loc_28 ("node")))) at{struct_tree} "key") <-{ IntOp size_t }
          LocInfoE loc_29 (use{IntOp size_t} (LocInfoE loc_30 ("key"))) ;
        locinfo: loc_18 ;
        LocInfoE loc_22 ((LocInfoE loc_23 (!{PtrOp} (LocInfoE loc_24 ("node")))) at{struct_tree} "right") <-{ PtrOp }
          LocInfoE loc_25 (NULL) ;
        locinfo: loc_19 ;
        Return (LocInfoE loc_20 (use{PtrOp} (LocInfoE loc_21 ("node"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [node]. *)
  Definition impl_node (global_talloc : loc): function := {|
    f_args := [
      ("left", void*);
      ("key", it_layout size_t);
      ("right", void*)
    ];
    f_local_vars := [
      ("node", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "node" <-{ PtrOp }
          LocInfoE loc_65 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_65 (Call (LocInfoE loc_67 (global_talloc)) [@{expr} LocInfoE loc_68 (i2v (layout_of struct_tree).(ly_size) size_t) ]))) ;
        locinfo: loc_44 ;
        LocInfoE loc_60 ((LocInfoE loc_61 (!{PtrOp} (LocInfoE loc_62 ("node")))) at{struct_tree} "left") <-{ PtrOp }
          LocInfoE loc_63 (use{PtrOp} (LocInfoE loc_64 ("left"))) ;
        locinfo: loc_45 ;
        LocInfoE loc_55 ((LocInfoE loc_56 (!{PtrOp} (LocInfoE loc_57 ("node")))) at{struct_tree} "key") <-{ IntOp size_t }
          LocInfoE loc_58 (use{IntOp size_t} (LocInfoE loc_59 ("key"))) ;
        locinfo: loc_46 ;
        LocInfoE loc_50 ((LocInfoE loc_51 (!{PtrOp} (LocInfoE loc_52 ("node")))) at{struct_tree} "right") <-{ PtrOp }
          LocInfoE loc_53 (use{PtrOp} (LocInfoE loc_54 ("right"))) ;
        locinfo: loc_47 ;
        Return (LocInfoE loc_48 (use{PtrOp} (LocInfoE loc_49 ("node"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [free_tree]. *)
  Definition impl_free_tree (global_free_tree global_tfree : loc): function := {|
    f_args := [
      ("t", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_102 ;
        if{IntOp i32, None}: LocInfoE loc_102 ((LocInfoE loc_103 (use{PtrOp} (LocInfoE loc_105 (!{PtrOp} (LocInfoE loc_106 ("t")))))) !={PtrOp, PtrOp, i32} (LocInfoE loc_107 (NULL)))
        then
        locinfo: loc_75 ;
          Goto "#1"
        else
        Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_75 ;
        expr: (LocInfoE loc_75 (Call (LocInfoE loc_94 (global_free_tree)) [@{expr} LocInfoE loc_95 (&(LocInfoE loc_96 ((LocInfoE loc_97 (!{PtrOp} (LocInfoE loc_99 (!{PtrOp} (LocInfoE loc_100 ("t")))))) at{struct_tree} "left"))) ])) ;
        locinfo: loc_76 ;
        expr: (LocInfoE loc_76 (Call (LocInfoE loc_86 (global_free_tree)) [@{expr} LocInfoE loc_87 (&(LocInfoE loc_88 ((LocInfoE loc_89 (!{PtrOp} (LocInfoE loc_91 (!{PtrOp} (LocInfoE loc_92 ("t")))))) at{struct_tree} "right"))) ])) ;
        locinfo: loc_77 ;
        expr: (LocInfoE loc_77 (Call (LocInfoE loc_79 (global_tfree)) [@{expr} LocInfoE loc_80 (i2v (layout_of struct_tree).(ly_size) size_t) ;
        LocInfoE loc_81 (use{PtrOp} (LocInfoE loc_83 (!{PtrOp} (LocInfoE loc_84 ("t"))))) ])) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [member_rec]. *)
  Definition impl_member_rec (global_member_rec : loc): function := {|
    f_args := [
      ("t", void*);
      ("k", it_layout size_t)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_162 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_162 ((LocInfoE loc_163 (use{PtrOp} (LocInfoE loc_165 (!{PtrOp} (LocInfoE loc_166 ("t")))))) ={PtrOp, PtrOp, i32} (LocInfoE loc_167 (NULL)))
        then
        locinfo: loc_159 ;
          Goto "#8"
        else
        locinfo: loc_150 ;
          Goto "#9"
      ]> $
      <[ "#1" :=
        locinfo: loc_150 ;
        if{IntOp i32, Some "#2"}: LocInfoE loc_150 ((LocInfoE loc_151 (use{IntOp size_t} (LocInfoE loc_152 ((LocInfoE loc_153 (!{PtrOp} (LocInfoE loc_155 (!{PtrOp} (LocInfoE loc_156 ("t")))))) at{struct_tree} "key")))) ={IntOp size_t, IntOp size_t, i32} (LocInfoE loc_157 (use{IntOp size_t} (LocInfoE loc_158 ("k")))))
        then
        locinfo: loc_147 ;
          Goto "#6"
        else
        locinfo: loc_138 ;
          Goto "#7"
      ]> $
      <[ "#2" :=
        locinfo: loc_138 ;
        if{IntOp i32, Some "#3"}: LocInfoE loc_138 ((LocInfoE loc_139 (use{IntOp size_t} (LocInfoE loc_140 ("k")))) <{IntOp size_t, IntOp size_t, i32} (LocInfoE loc_141 (use{IntOp size_t} (LocInfoE loc_142 ((LocInfoE loc_143 (!{PtrOp} (LocInfoE loc_145 (!{PtrOp} (LocInfoE loc_146 ("t")))))) at{struct_tree} "key")))))
        then
        locinfo: loc_125 ;
          Goto "#4"
        else
        locinfo: loc_113 ;
          Goto "#5"
      ]> $
      <[ "#3" :=
        locinfo: loc_113 ;
        Return (LocInfoE loc_114 (Call (LocInfoE loc_116 (global_member_rec)) [@{expr} LocInfoE loc_117 (&(LocInfoE loc_118 ((LocInfoE loc_119 (!{PtrOp} (LocInfoE loc_121 (!{PtrOp} (LocInfoE loc_122 ("t")))))) at{struct_tree} "right"))) ;
               LocInfoE loc_123 (use{IntOp size_t} (LocInfoE loc_124 ("k"))) ]))
      ]> $
      <[ "#4" :=
        locinfo: loc_125 ;
        Return (LocInfoE loc_126 (Call (LocInfoE loc_128 (global_member_rec)) [@{expr} LocInfoE loc_129 (&(LocInfoE loc_130 ((LocInfoE loc_131 (!{PtrOp} (LocInfoE loc_133 (!{PtrOp} (LocInfoE loc_134 ("t")))))) at{struct_tree} "left"))) ;
               LocInfoE loc_135 (use{IntOp size_t} (LocInfoE loc_136 ("k"))) ]))
      ]> $
      <[ "#5" :=
        locinfo: loc_113 ;
        Goto "#3"
      ]> $
      <[ "#6" :=
        locinfo: loc_147 ;
        Return (LocInfoE loc_148 (UnOp (CastOp $ BoolOp) (IntOp i32) (LocInfoE loc_148 (i2v 1 i32))))
      ]> $
      <[ "#7" :=
        locinfo: loc_138 ;
        Goto "#2"
      ]> $
      <[ "#8" :=
        locinfo: loc_159 ;
        Return (LocInfoE loc_160 (UnOp (CastOp $ BoolOp) (IntOp i32) (LocInfoE loc_160 (i2v 0 i32))))
      ]> $
      <[ "#9" :=
        locinfo: loc_150 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [member]. *)
  Definition impl_member : function := {|
    f_args := [
      ("t", void*);
      ("k", it_layout size_t)
    ];
    f_local_vars := [
      ("cur", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "cur" <-{ PtrOp }
          LocInfoE loc_222 (&(LocInfoE loc_224 (!{PtrOp} (LocInfoE loc_225 ("t"))))) ;
        locinfo: loc_171 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_216 ;
        if{IntOp i32, None}: LocInfoE loc_216 ((LocInfoE loc_217 (use{PtrOp} (LocInfoE loc_219 (!{PtrOp} (LocInfoE loc_220 ("cur")))))) !={PtrOp, PtrOp, i32} (LocInfoE loc_221 (NULL)))
        then
        locinfo: loc_207 ;
          Goto "#2"
        else
        locinfo: loc_172 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_207 ;
        if{IntOp i32, Some "#4"}: LocInfoE loc_207 ((LocInfoE loc_208 (use{IntOp size_t} (LocInfoE loc_209 ((LocInfoE loc_210 (!{PtrOp} (LocInfoE loc_212 (!{PtrOp} (LocInfoE loc_213 ("cur")))))) at{struct_tree} "key")))) ={IntOp size_t, IntOp size_t, i32} (LocInfoE loc_214 (use{IntOp size_t} (LocInfoE loc_215 ("k")))))
        then
        locinfo: loc_204 ;
          Goto "#7"
        else
        locinfo: loc_195 ;
          Goto "#8"
      ]> $
      <[ "#3" :=
        locinfo: loc_172 ;
        Return (LocInfoE loc_173 (UnOp (CastOp $ BoolOp) (IntOp i32) (LocInfoE loc_173 (i2v 0 i32))))
      ]> $
      <[ "#4" :=
        locinfo: loc_195 ;
        if{IntOp i32, None}: LocInfoE loc_195 ((LocInfoE loc_196 (use{IntOp size_t} (LocInfoE loc_197 ("k")))) <{IntOp size_t, IntOp size_t, i32} (LocInfoE loc_198 (use{IntOp size_t} (LocInfoE loc_199 ((LocInfoE loc_200 (!{PtrOp} (LocInfoE loc_202 (!{PtrOp} (LocInfoE loc_203 ("cur")))))) at{struct_tree} "key")))))
        then
        locinfo: loc_178 ;
          Goto "#5"
        else
        locinfo: loc_187 ;
          Goto "#6"
      ]> $
      <[ "#5" :=
        locinfo: loc_178 ;
        LocInfoE loc_179 ("cur") <-{ PtrOp }
          LocInfoE loc_180 (&(LocInfoE loc_181 ((LocInfoE loc_182 (!{PtrOp} (LocInfoE loc_184 (!{PtrOp} (LocInfoE loc_185 ("cur")))))) at{struct_tree} "left"))) ;
        locinfo: loc_171 ;
        Goto "#1"
      ]> $
      <[ "#6" :=
        locinfo: loc_187 ;
        LocInfoE loc_188 ("cur") <-{ PtrOp }
          LocInfoE loc_189 (&(LocInfoE loc_190 ((LocInfoE loc_191 (!{PtrOp} (LocInfoE loc_193 (!{PtrOp} (LocInfoE loc_194 ("cur")))))) at{struct_tree} "right"))) ;
        locinfo: loc_171 ;
        Goto "#1"
      ]> $
      <[ "#7" :=
        locinfo: loc_204 ;
        Return (LocInfoE loc_205 (UnOp (CastOp $ BoolOp) (IntOp i32) (LocInfoE loc_205 (i2v 1 i32))))
      ]> $
      <[ "#8" :=
        locinfo: loc_195 ;
        Goto "#4"
      ]> $∅
    )%E
  |}.

  (* Definition of function [insert_rec]. *)
  Definition impl_insert_rec (global_insert_rec global_node : loc): function := {|
    f_args := [
      ("t", void*);
      ("k", it_layout size_t)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_291 ;
        if{IntOp i32, None}: LocInfoE loc_291 ((LocInfoE loc_292 (use{PtrOp} (LocInfoE loc_294 (!{PtrOp} (LocInfoE loc_295 ("t")))))) ={PtrOp, PtrOp, i32} (LocInfoE loc_296 (NULL)))
        then
        locinfo: loc_232 ;
          Goto "#1"
        else
        locinfo: loc_282 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_232 ;
        LocInfoE loc_234 (!{PtrOp} (LocInfoE loc_235 ("t"))) <-{ PtrOp }
          LocInfoE loc_236 (Call (LocInfoE loc_238 (global_node)) [@{expr} LocInfoE loc_239 (NULL) ;
          LocInfoE loc_240 (use{IntOp size_t} (LocInfoE loc_241 ("k"))) ;
          LocInfoE loc_242 (NULL) ]) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_282 ;
        if{IntOp i32, None}: LocInfoE loc_282 ((LocInfoE loc_283 (use{IntOp size_t} (LocInfoE loc_284 ((LocInfoE loc_285 (!{PtrOp} (LocInfoE loc_287 (!{PtrOp} (LocInfoE loc_288 ("t")))))) at{struct_tree} "key")))) ={IntOp size_t, IntOp size_t, i32} (LocInfoE loc_289 (use{IntOp size_t} (LocInfoE loc_290 ("k")))))
        then
        locinfo: loc_246 ;
          Goto "#3"
        else
        locinfo: loc_273 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_246 ;
        Return (VOID)
      ]> $
      <[ "#4" :=
        locinfo: loc_273 ;
        if{IntOp i32, None}: LocInfoE loc_273 ((LocInfoE loc_274 (use{IntOp size_t} (LocInfoE loc_275 ("k")))) <{IntOp size_t, IntOp size_t, i32} (LocInfoE loc_276 (use{IntOp size_t} (LocInfoE loc_277 ((LocInfoE loc_278 (!{PtrOp} (LocInfoE loc_280 (!{PtrOp} (LocInfoE loc_281 ("t")))))) at{struct_tree} "key")))))
        then
        locinfo: loc_250 ;
          Goto "#5"
        else
        locinfo: loc_262 ;
          Goto "#6"
      ]> $
      <[ "#5" :=
        locinfo: loc_250 ;
        expr: (LocInfoE loc_250 (Call (LocInfoE loc_252 (global_insert_rec)) [@{expr} LocInfoE loc_253 (&(LocInfoE loc_254 ((LocInfoE loc_255 (!{PtrOp} (LocInfoE loc_257 (!{PtrOp} (LocInfoE loc_258 ("t")))))) at{struct_tree} "left"))) ;
        LocInfoE loc_259 (use{IntOp size_t} (LocInfoE loc_260 ("k"))) ])) ;
        Return (VOID)
      ]> $
      <[ "#6" :=
        locinfo: loc_262 ;
        expr: (LocInfoE loc_262 (Call (LocInfoE loc_264 (global_insert_rec)) [@{expr} LocInfoE loc_265 (&(LocInfoE loc_266 ((LocInfoE loc_267 (!{PtrOp} (LocInfoE loc_269 (!{PtrOp} (LocInfoE loc_270 ("t")))))) at{struct_tree} "right"))) ;
        LocInfoE loc_271 (use{IntOp size_t} (LocInfoE loc_272 ("k"))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [insert]. *)
  Definition impl_insert (global_node : loc): function := {|
    f_args := [
      ("t", void*);
      ("k", it_layout size_t)
    ];
    f_local_vars := [
      ("cur", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "cur" <-{ PtrOp }
          LocInfoE loc_360 (&(LocInfoE loc_362 (!{PtrOp} (LocInfoE loc_363 ("t"))))) ;
        locinfo: loc_300 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_354 ;
        if{IntOp i32, None}: LocInfoE loc_354 ((LocInfoE loc_355 (use{PtrOp} (LocInfoE loc_357 (!{PtrOp} (LocInfoE loc_358 ("cur")))))) !={PtrOp, PtrOp, i32} (LocInfoE loc_359 (NULL)))
        then
        locinfo: loc_345 ;
          Goto "#2"
        else
        locinfo: loc_301 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_345 ;
        if{IntOp i32, Some "#4"}: LocInfoE loc_345 ((LocInfoE loc_346 (use{IntOp size_t} (LocInfoE loc_347 ((LocInfoE loc_348 (!{PtrOp} (LocInfoE loc_350 (!{PtrOp} (LocInfoE loc_351 ("cur")))))) at{struct_tree} "key")))) ={IntOp size_t, IntOp size_t, i32} (LocInfoE loc_352 (use{IntOp size_t} (LocInfoE loc_353 ("k")))))
        then
        locinfo: loc_342 ;
          Goto "#7"
        else
        locinfo: loc_333 ;
          Goto "#8"
      ]> $
      <[ "#3" :=
        locinfo: loc_301 ;
        LocInfoE loc_303 (!{PtrOp} (LocInfoE loc_304 ("cur"))) <-{ PtrOp }
          LocInfoE loc_305 (Call (LocInfoE loc_307 (global_node)) [@{expr} LocInfoE loc_308 (NULL) ;
          LocInfoE loc_309 (use{IntOp size_t} (LocInfoE loc_310 ("k"))) ;
          LocInfoE loc_311 (NULL) ]) ;
        Return (VOID)
      ]> $
      <[ "#4" :=
        locinfo: loc_333 ;
        if{IntOp i32, None}: LocInfoE loc_333 ((LocInfoE loc_334 (use{IntOp size_t} (LocInfoE loc_335 ("k")))) <{IntOp size_t, IntOp size_t, i32} (LocInfoE loc_336 (use{IntOp size_t} (LocInfoE loc_337 ((LocInfoE loc_338 (!{PtrOp} (LocInfoE loc_340 (!{PtrOp} (LocInfoE loc_341 ("cur")))))) at{struct_tree} "key")))))
        then
        locinfo: loc_316 ;
          Goto "#5"
        else
        locinfo: loc_325 ;
          Goto "#6"
      ]> $
      <[ "#5" :=
        locinfo: loc_316 ;
        LocInfoE loc_317 ("cur") <-{ PtrOp }
          LocInfoE loc_318 (&(LocInfoE loc_319 ((LocInfoE loc_320 (!{PtrOp} (LocInfoE loc_322 (!{PtrOp} (LocInfoE loc_323 ("cur")))))) at{struct_tree} "left"))) ;
        locinfo: loc_300 ;
        Goto "#1"
      ]> $
      <[ "#6" :=
        locinfo: loc_325 ;
        LocInfoE loc_326 ("cur") <-{ PtrOp }
          LocInfoE loc_327 (&(LocInfoE loc_328 ((LocInfoE loc_329 (!{PtrOp} (LocInfoE loc_331 (!{PtrOp} (LocInfoE loc_332 ("cur")))))) at{struct_tree} "right"))) ;
        locinfo: loc_300 ;
        Goto "#1"
      ]> $
      <[ "#7" :=
        locinfo: loc_342 ;
        Return (VOID)
      ]> $
      <[ "#8" :=
        locinfo: loc_333 ;
        Goto "#4"
      ]> $∅
    )%E
  |}.

  (* Definition of function [tree_max]. *)
  Definition impl_tree_max (global_tree_max : loc): function := {|
    f_args := [
      ("t", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_388 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_388 ((LocInfoE loc_389 (use{PtrOp} (LocInfoE loc_390 ((LocInfoE loc_391 (!{PtrOp} (LocInfoE loc_393 (!{PtrOp} (LocInfoE loc_394 ("t")))))) at{struct_tree} "right")))) ={PtrOp, PtrOp, i32} (LocInfoE loc_395 (NULL)))
        then
        locinfo: loc_380 ;
          Goto "#2"
        else
        locinfo: loc_369 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_369 ;
        Return (LocInfoE loc_370 (Call (LocInfoE loc_372 (global_tree_max)) [@{expr} LocInfoE loc_373 (&(LocInfoE loc_374 ((LocInfoE loc_375 (!{PtrOp} (LocInfoE loc_377 (!{PtrOp} (LocInfoE loc_378 ("t")))))) at{struct_tree} "right"))) ]))
      ]> $
      <[ "#2" :=
        locinfo: loc_380 ;
        Return (LocInfoE loc_381 (use{IntOp size_t} (LocInfoE loc_382 ((LocInfoE loc_383 (!{PtrOp} (LocInfoE loc_385 (!{PtrOp} (LocInfoE loc_386 ("t")))))) at{struct_tree} "key"))))
      ]> $
      <[ "#3" :=
        locinfo: loc_369 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [remove]. *)
  Definition impl_remove (global_remove global_tfree global_tree_max : loc): function := {|
    f_args := [
      ("t", void*);
      ("k", it_layout size_t)
    ];
    f_local_vars := [
      ("m", it_layout size_t);
      ("tmp", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_513 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_513 ((LocInfoE loc_514 (use{PtrOp} (LocInfoE loc_516 (!{PtrOp} (LocInfoE loc_517 ("t")))))) ={PtrOp, PtrOp, i32} (LocInfoE loc_518 (NULL)))
        then
        locinfo: loc_510 ;
          Goto "#8"
        else
        locinfo: loc_500 ;
          Goto "#9"
      ]> $
      <[ "#1" :=
        locinfo: loc_500 ;
        if{IntOp i32, None}: LocInfoE loc_500 ((LocInfoE loc_501 (use{IntOp size_t} (LocInfoE loc_502 ("k")))) ={IntOp size_t, IntOp size_t, i32} (LocInfoE loc_503 (use{IntOp size_t} (LocInfoE loc_504 ((LocInfoE loc_505 (!{PtrOp} (LocInfoE loc_507 (!{PtrOp} (LocInfoE loc_508 ("t")))))) at{struct_tree} "key")))))
        then
        locinfo: loc_458 ;
          Goto "#2"
        else
        locinfo: loc_491 ;
          Goto "#5"
      ]> $
      <[ "#2" :=
        locinfo: loc_458 ;
        if{IntOp i32, None}: LocInfoE loc_458 ((LocInfoE loc_459 (use{PtrOp} (LocInfoE loc_460 ((LocInfoE loc_461 (!{PtrOp} (LocInfoE loc_463 (!{PtrOp} (LocInfoE loc_464 ("t")))))) at{struct_tree} "left")))) !={PtrOp, PtrOp, i32} (LocInfoE loc_465 (NULL)))
        then
        locinfo: loc_405 ;
          Goto "#3"
        else
        locinfo: loc_436 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_405 ;
        LocInfoE loc_425 ("m") <-{ IntOp size_t }
          LocInfoE loc_426 (Call (LocInfoE loc_428 (global_tree_max)) [@{expr} LocInfoE loc_429 (&(LocInfoE loc_430 ((LocInfoE loc_431 (!{PtrOp} (LocInfoE loc_433 (!{PtrOp} (LocInfoE loc_434 ("t")))))) at{struct_tree} "left"))) ]) ;
        locinfo: loc_406 ;
        expr: (LocInfoE loc_406 (Call (LocInfoE loc_416 (global_remove)) [@{expr} LocInfoE loc_417 (&(LocInfoE loc_418 ((LocInfoE loc_419 (!{PtrOp} (LocInfoE loc_421 (!{PtrOp} (LocInfoE loc_422 ("t")))))) at{struct_tree} "left"))) ;
        LocInfoE loc_423 (use{IntOp size_t} (LocInfoE loc_424 ("m"))) ])) ;
        locinfo: loc_407 ;
        LocInfoE loc_408 ((LocInfoE loc_409 (!{PtrOp} (LocInfoE loc_411 (!{PtrOp} (LocInfoE loc_412 ("t")))))) at{struct_tree} "key") <-{ IntOp size_t }
          LocInfoE loc_413 (use{IntOp size_t} (LocInfoE loc_414 ("m"))) ;
        Return (VOID)
      ]> $
      <[ "#4" :=
        locinfo: loc_436 ;
        LocInfoE loc_451 ("tmp") <-{ PtrOp }
          LocInfoE loc_452 (use{PtrOp} (LocInfoE loc_453 ((LocInfoE loc_454 (!{PtrOp} (LocInfoE loc_456 (!{PtrOp} (LocInfoE loc_457 ("t")))))) at{struct_tree} "right"))) ;
        locinfo: loc_437 ;
        expr: (LocInfoE loc_437 (Call (LocInfoE loc_445 (global_tfree)) [@{expr} LocInfoE loc_446 (i2v (layout_of struct_tree).(ly_size) size_t) ;
        LocInfoE loc_447 (use{PtrOp} (LocInfoE loc_449 (!{PtrOp} (LocInfoE loc_450 ("t"))))) ])) ;
        locinfo: loc_438 ;
        LocInfoE loc_440 (!{PtrOp} (LocInfoE loc_441 ("t"))) <-{ PtrOp }
          LocInfoE loc_442 (use{PtrOp} (LocInfoE loc_443 ("tmp"))) ;
        Return (VOID)
      ]> $
      <[ "#5" :=
        locinfo: loc_491 ;
        if{IntOp i32, None}: LocInfoE loc_491 ((LocInfoE loc_492 (use{IntOp size_t} (LocInfoE loc_493 ("k")))) <{IntOp size_t, IntOp size_t, i32} (LocInfoE loc_494 (use{IntOp size_t} (LocInfoE loc_495 ((LocInfoE loc_496 (!{PtrOp} (LocInfoE loc_498 (!{PtrOp} (LocInfoE loc_499 ("t")))))) at{struct_tree} "key")))))
        then
        locinfo: loc_468 ;
          Goto "#6"
        else
        locinfo: loc_480 ;
          Goto "#7"
      ]> $
      <[ "#6" :=
        locinfo: loc_468 ;
        expr: (LocInfoE loc_468 (Call (LocInfoE loc_470 (global_remove)) [@{expr} LocInfoE loc_471 (&(LocInfoE loc_472 ((LocInfoE loc_473 (!{PtrOp} (LocInfoE loc_475 (!{PtrOp} (LocInfoE loc_476 ("t")))))) at{struct_tree} "left"))) ;
        LocInfoE loc_477 (use{IntOp size_t} (LocInfoE loc_478 ("k"))) ])) ;
        Return (VOID)
      ]> $
      <[ "#7" :=
        locinfo: loc_480 ;
        expr: (LocInfoE loc_480 (Call (LocInfoE loc_482 (global_remove)) [@{expr} LocInfoE loc_483 (&(LocInfoE loc_484 ((LocInfoE loc_485 (!{PtrOp} (LocInfoE loc_487 (!{PtrOp} (LocInfoE loc_488 ("t")))))) at{struct_tree} "right"))) ;
        LocInfoE loc_489 (use{IntOp size_t} (LocInfoE loc_490 ("k"))) ])) ;
        Return (VOID)
      ]> $
      <[ "#8" :=
        locinfo: loc_510 ;
        Return (VOID)
      ]> $
      <[ "#9" :=
        locinfo: loc_500 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [main]. *)
  Definition impl_main (global_empty global_free_tree global_init global_insert global_member global_remove : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
      ("t", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "t" <-{ PtrOp }
          LocInfoE loc_580 (Call (LocInfoE loc_582 (global_empty)) [@{expr}  ]) ;
        locinfo: loc_522 ;
        LocInfoE loc_575 ("t") <-{ PtrOp }
          LocInfoE loc_576 (Call (LocInfoE loc_578 (global_init)) [@{expr} LocInfoE loc_579 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_579 (i2v 3 i32))) ]) ;
        locinfo: loc_523 ;
        expr: (LocInfoE loc_523 (Call (LocInfoE loc_571 (global_insert)) [@{expr} LocInfoE loc_572 (&(LocInfoE loc_573 ("t"))) ;
        LocInfoE loc_574 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_574 (i2v 2 i32))) ])) ;
        locinfo: loc_524 ;
        assert{BoolOp}: (LocInfoE loc_564 (Call (LocInfoE loc_566 (global_member)) [@{expr} LocInfoE loc_567 (&(LocInfoE loc_568 ("t"))) ;
        LocInfoE loc_569 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_569 (i2v 2 i32))) ])) ;
        locinfo: loc_525 ;
        assert{BoolOp}: (LocInfoE loc_558 (Call (LocInfoE loc_560 (global_member)) [@{expr} LocInfoE loc_561 (&(LocInfoE loc_562 ("t"))) ;
        LocInfoE loc_563 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_563 (i2v 3 i32))) ])) ;
        locinfo: loc_526 ;
        expr: (LocInfoE loc_526 (Call (LocInfoE loc_554 (global_remove)) [@{expr} LocInfoE loc_555 (&(LocInfoE loc_556 ("t"))) ;
        LocInfoE loc_557 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_557 (i2v 3 i32))) ])) ;
        locinfo: loc_527 ;
        expr: (LocInfoE loc_527 (Call (LocInfoE loc_549 (global_insert)) [@{expr} LocInfoE loc_550 (&(LocInfoE loc_551 ("t"))) ;
        LocInfoE loc_552 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_552 (i2v 3 i32))) ])) ;
        locinfo: loc_528 ;
        assert{BoolOp}: (LocInfoE loc_542 (Call (LocInfoE loc_544 (global_member)) [@{expr} LocInfoE loc_545 (&(LocInfoE loc_546 ("t"))) ;
        LocInfoE loc_547 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_547 (i2v 2 i32))) ])) ;
        locinfo: loc_529 ;
        expr: (LocInfoE loc_529 (Call (LocInfoE loc_538 (global_remove)) [@{expr} LocInfoE loc_539 (&(LocInfoE loc_540 ("t"))) ;
        LocInfoE loc_541 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_541 (i2v 3 i32))) ])) ;
        locinfo: loc_530 ;
        expr: (LocInfoE loc_530 (Call (LocInfoE loc_534 (global_free_tree)) [@{expr} LocInfoE loc_535 (&(LocInfoE loc_536 ("t"))) ])) ;
        locinfo: loc_531 ;
        Return (LocInfoE loc_532 (i2v 0 i32))
      ]> $∅
    )%E
  |}.
End code.
