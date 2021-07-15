From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/t11_tree_set.c]. *)
Section code.
  Definition file_0 : string := "tutorial/t11_tree_set.c".
  Definition file_1 : string := "include/refinedc.h".
  Definition loc_2 : location_info := LocationInfo file_1 50 2 50 47.
  Definition loc_3 : location_info := LocationInfo file_1 50 9 50 46.
  Definition loc_4 : location_info := LocationInfo file_1 50 9 50 32.
  Definition loc_5 : location_info := LocationInfo file_1 50 33 50 37.
  Definition loc_6 : location_info := LocationInfo file_1 50 33 50 37.
  Definition loc_7 : location_info := LocationInfo file_1 50 39 50 45.
  Definition loc_8 : location_info := LocationInfo file_1 50 39 50 45.
  Definition loc_11 : location_info := LocationInfo file_0 26 2 26 24.
  Definition loc_12 : location_info := LocationInfo file_0 26 9 26 23.
  Definition loc_15 : location_info := LocationInfo file_0 35 2 35 49.
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
  Definition loc_35 : location_info := LocationInfo file_0 35 22 35 48.
  Definition loc_36 : location_info := LocationInfo file_0 35 22 35 27.
  Definition loc_37 : location_info := LocationInfo file_0 35 22 35 27.
  Definition loc_38 : location_info := LocationInfo file_0 35 28 35 47.
  Definition loc_43 : location_info := LocationInfo file_0 49 2 49 49.
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
  Definition loc_65 : location_info := LocationInfo file_0 49 22 49 48.
  Definition loc_66 : location_info := LocationInfo file_0 49 22 49 27.
  Definition loc_67 : location_info := LocationInfo file_0 49 22 49 27.
  Definition loc_68 : location_info := LocationInfo file_0 49 28 49 47.
  Definition loc_73 : location_info := LocationInfo file_0 61 2 65 3.
  Definition loc_74 : location_info := LocationInfo file_0 61 26 65 3.
  Definition loc_75 : location_info := LocationInfo file_0 62 4 62 29.
  Definition loc_76 : location_info := LocationInfo file_0 63 4 63 30.
  Definition loc_77 : location_info := LocationInfo file_0 64 4 64 34.
  Definition loc_78 : location_info := LocationInfo file_0 64 4 64 8.
  Definition loc_79 : location_info := LocationInfo file_0 64 4 64 8.
  Definition loc_80 : location_info := LocationInfo file_0 64 9 64 28.
  Definition loc_81 : location_info := LocationInfo file_0 64 30 64 32.
  Definition loc_82 : location_info := LocationInfo file_0 64 30 64 32.
  Definition loc_83 : location_info := LocationInfo file_0 64 31 64 32.
  Definition loc_84 : location_info := LocationInfo file_0 64 31 64 32.
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
  Definition loc_174 : location_info := LocationInfo file_0 92 2 99 3.
  Definition loc_175 : location_info := LocationInfo file_0 92 31 99 3.
  Definition loc_176 : location_info := LocationInfo file_0 93 4 93 34.
  Definition loc_177 : location_info := LocationInfo file_0 94 4 98 5.
  Definition loc_178 : location_info := LocationInfo file_0 92 2 99 3.
  Definition loc_179 : location_info := LocationInfo file_0 92 2 99 3.
  Definition loc_180 : location_info := LocationInfo file_0 94 23 96 5.
  Definition loc_181 : location_info := LocationInfo file_0 95 6 95 28.
  Definition loc_182 : location_info := LocationInfo file_0 95 6 95 9.
  Definition loc_183 : location_info := LocationInfo file_0 95 12 95 27.
  Definition loc_184 : location_info := LocationInfo file_0 95 13 95 27.
  Definition loc_185 : location_info := LocationInfo file_0 95 14 95 20.
  Definition loc_186 : location_info := LocationInfo file_0 95 14 95 20.
  Definition loc_187 : location_info := LocationInfo file_0 95 16 95 19.
  Definition loc_188 : location_info := LocationInfo file_0 95 16 95 19.
  Definition loc_189 : location_info := LocationInfo file_0 96 11 98 5.
  Definition loc_190 : location_info := LocationInfo file_0 97 6 97 29.
  Definition loc_191 : location_info := LocationInfo file_0 97 6 97 9.
  Definition loc_192 : location_info := LocationInfo file_0 97 12 97 28.
  Definition loc_193 : location_info := LocationInfo file_0 97 13 97 28.
  Definition loc_194 : location_info := LocationInfo file_0 97 14 97 20.
  Definition loc_195 : location_info := LocationInfo file_0 97 14 97 20.
  Definition loc_196 : location_info := LocationInfo file_0 97 16 97 19.
  Definition loc_197 : location_info := LocationInfo file_0 97 16 97 19.
  Definition loc_198 : location_info := LocationInfo file_0 94 7 94 22.
  Definition loc_199 : location_info := LocationInfo file_0 94 7 94 8.
  Definition loc_200 : location_info := LocationInfo file_0 94 7 94 8.
  Definition loc_201 : location_info := LocationInfo file_0 94 11 94 22.
  Definition loc_202 : location_info := LocationInfo file_0 94 11 94 22.
  Definition loc_203 : location_info := LocationInfo file_0 94 11 94 17.
  Definition loc_204 : location_info := LocationInfo file_0 94 11 94 17.
  Definition loc_205 : location_info := LocationInfo file_0 94 13 94 16.
  Definition loc_206 : location_info := LocationInfo file_0 94 13 94 16.
  Definition loc_207 : location_info := LocationInfo file_0 93 25 93 34.
  Definition loc_208 : location_info := LocationInfo file_0 93 32 93 33.
  Definition loc_210 : location_info := LocationInfo file_0 93 7 93 23.
  Definition loc_211 : location_info := LocationInfo file_0 93 7 93 18.
  Definition loc_212 : location_info := LocationInfo file_0 93 7 93 18.
  Definition loc_213 : location_info := LocationInfo file_0 93 7 93 13.
  Definition loc_214 : location_info := LocationInfo file_0 93 7 93 13.
  Definition loc_215 : location_info := LocationInfo file_0 93 9 93 12.
  Definition loc_216 : location_info := LocationInfo file_0 93 9 93 12.
  Definition loc_217 : location_info := LocationInfo file_0 93 22 93 23.
  Definition loc_218 : location_info := LocationInfo file_0 93 22 93 23.
  Definition loc_219 : location_info := LocationInfo file_0 92 8 92 30.
  Definition loc_220 : location_info := LocationInfo file_0 92 8 92 12.
  Definition loc_221 : location_info := LocationInfo file_0 92 8 92 12.
  Definition loc_222 : location_info := LocationInfo file_0 92 9 92 12.
  Definition loc_223 : location_info := LocationInfo file_0 92 9 92 12.
  Definition loc_224 : location_info := LocationInfo file_0 92 16 92 30.
  Definition loc_225 : location_info := LocationInfo file_0 86 16 86 19.
  Definition loc_226 : location_info := LocationInfo file_0 86 17 86 19.
  Definition loc_227 : location_info := LocationInfo file_0 86 18 86 19.
  Definition loc_228 : location_info := LocationInfo file_0 86 18 86 19.
  Definition loc_233 : location_info := LocationInfo file_0 109 2 118 3.
  Definition loc_234 : location_info := LocationInfo file_0 109 26 111 3.
  Definition loc_235 : location_info := LocationInfo file_0 110 4 110 49.
  Definition loc_236 : location_info := LocationInfo file_0 110 4 110 6.
  Definition loc_237 : location_info := LocationInfo file_0 110 5 110 6.
  Definition loc_238 : location_info := LocationInfo file_0 110 5 110 6.
  Definition loc_239 : location_info := LocationInfo file_0 110 9 110 48.
  Definition loc_240 : location_info := LocationInfo file_0 110 9 110 13.
  Definition loc_241 : location_info := LocationInfo file_0 110 9 110 13.
  Definition loc_242 : location_info := LocationInfo file_0 110 14 110 28.
  Definition loc_243 : location_info := LocationInfo file_0 110 30 110 31.
  Definition loc_244 : location_info := LocationInfo file_0 110 30 110 31.
  Definition loc_245 : location_info := LocationInfo file_0 110 33 110 47.
  Definition loc_246 : location_info := LocationInfo file_0 111 9 118 3.
  Definition loc_247 : location_info := LocationInfo file_0 112 4 112 30.
  Definition loc_248 : location_info := LocationInfo file_0 113 4 117 5.
  Definition loc_249 : location_info := LocationInfo file_0 113 21 115 5.
  Definition loc_250 : location_info := LocationInfo file_0 114 6 114 35.
  Definition loc_251 : location_info := LocationInfo file_0 114 6 114 16.
  Definition loc_252 : location_info := LocationInfo file_0 114 6 114 16.
  Definition loc_253 : location_info := LocationInfo file_0 114 17 114 30.
  Definition loc_254 : location_info := LocationInfo file_0 114 18 114 30.
  Definition loc_255 : location_info := LocationInfo file_0 114 19 114 23.
  Definition loc_256 : location_info := LocationInfo file_0 114 19 114 23.
  Definition loc_257 : location_info := LocationInfo file_0 114 21 114 22.
  Definition loc_258 : location_info := LocationInfo file_0 114 21 114 22.
  Definition loc_259 : location_info := LocationInfo file_0 114 32 114 33.
  Definition loc_260 : location_info := LocationInfo file_0 114 32 114 33.
  Definition loc_261 : location_info := LocationInfo file_0 115 11 117 5.
  Definition loc_262 : location_info := LocationInfo file_0 116 6 116 36.
  Definition loc_263 : location_info := LocationInfo file_0 116 6 116 16.
  Definition loc_264 : location_info := LocationInfo file_0 116 6 116 16.
  Definition loc_265 : location_info := LocationInfo file_0 116 17 116 31.
  Definition loc_266 : location_info := LocationInfo file_0 116 18 116 31.
  Definition loc_267 : location_info := LocationInfo file_0 116 19 116 23.
  Definition loc_268 : location_info := LocationInfo file_0 116 19 116 23.
  Definition loc_269 : location_info := LocationInfo file_0 116 21 116 22.
  Definition loc_270 : location_info := LocationInfo file_0 116 21 116 22.
  Definition loc_271 : location_info := LocationInfo file_0 116 33 116 34.
  Definition loc_272 : location_info := LocationInfo file_0 116 33 116 34.
  Definition loc_273 : location_info := LocationInfo file_0 113 7 113 20.
  Definition loc_274 : location_info := LocationInfo file_0 113 7 113 8.
  Definition loc_275 : location_info := LocationInfo file_0 113 7 113 8.
  Definition loc_276 : location_info := LocationInfo file_0 113 11 113 20.
  Definition loc_277 : location_info := LocationInfo file_0 113 11 113 20.
  Definition loc_278 : location_info := LocationInfo file_0 113 11 113 15.
  Definition loc_279 : location_info := LocationInfo file_0 113 11 113 15.
  Definition loc_280 : location_info := LocationInfo file_0 113 13 113 14.
  Definition loc_281 : location_info := LocationInfo file_0 113 13 113 14.
  Definition loc_282 : location_info := LocationInfo file_0 112 23 112 30.
  Definition loc_285 : location_info := LocationInfo file_0 112 7 112 21.
  Definition loc_286 : location_info := LocationInfo file_0 112 7 112 16.
  Definition loc_287 : location_info := LocationInfo file_0 112 7 112 16.
  Definition loc_288 : location_info := LocationInfo file_0 112 7 112 11.
  Definition loc_289 : location_info := LocationInfo file_0 112 7 112 11.
  Definition loc_290 : location_info := LocationInfo file_0 112 9 112 10.
  Definition loc_291 : location_info := LocationInfo file_0 112 9 112 10.
  Definition loc_292 : location_info := LocationInfo file_0 112 20 112 21.
  Definition loc_293 : location_info := LocationInfo file_0 112 20 112 21.
  Definition loc_294 : location_info := LocationInfo file_0 109 5 109 25.
  Definition loc_295 : location_info := LocationInfo file_0 109 5 109 7.
  Definition loc_296 : location_info := LocationInfo file_0 109 5 109 7.
  Definition loc_297 : location_info := LocationInfo file_0 109 6 109 7.
  Definition loc_298 : location_info := LocationInfo file_0 109 6 109 7.
  Definition loc_299 : location_info := LocationInfo file_0 109 11 109 25.
  Definition loc_302 : location_info := LocationInfo file_0 127 2 127 20.
  Definition loc_303 : location_info := LocationInfo file_0 132 2 139 3.
  Definition loc_304 : location_info := LocationInfo file_0 141 2 141 49.
  Definition loc_305 : location_info := LocationInfo file_0 141 2 141 6.
  Definition loc_306 : location_info := LocationInfo file_0 141 3 141 6.
  Definition loc_307 : location_info := LocationInfo file_0 141 3 141 6.
  Definition loc_308 : location_info := LocationInfo file_0 141 9 141 48.
  Definition loc_309 : location_info := LocationInfo file_0 141 9 141 13.
  Definition loc_310 : location_info := LocationInfo file_0 141 9 141 13.
  Definition loc_311 : location_info := LocationInfo file_0 141 14 141 28.
  Definition loc_312 : location_info := LocationInfo file_0 141 30 141 31.
  Definition loc_313 : location_info := LocationInfo file_0 141 30 141 31.
  Definition loc_314 : location_info := LocationInfo file_0 141 33 141 47.
  Definition loc_315 : location_info := LocationInfo file_0 132 2 139 3.
  Definition loc_316 : location_info := LocationInfo file_0 132 31 139 3.
  Definition loc_317 : location_info := LocationInfo file_0 133 4 133 32.
  Definition loc_318 : location_info := LocationInfo file_0 134 4 138 5.
  Definition loc_319 : location_info := LocationInfo file_0 132 2 139 3.
  Definition loc_320 : location_info := LocationInfo file_0 132 2 139 3.
  Definition loc_321 : location_info := LocationInfo file_0 134 23 136 5.
  Definition loc_322 : location_info := LocationInfo file_0 135 6 135 28.
  Definition loc_323 : location_info := LocationInfo file_0 135 6 135 9.
  Definition loc_324 : location_info := LocationInfo file_0 135 12 135 27.
  Definition loc_325 : location_info := LocationInfo file_0 135 13 135 27.
  Definition loc_326 : location_info := LocationInfo file_0 135 14 135 20.
  Definition loc_327 : location_info := LocationInfo file_0 135 14 135 20.
  Definition loc_328 : location_info := LocationInfo file_0 135 16 135 19.
  Definition loc_329 : location_info := LocationInfo file_0 135 16 135 19.
  Definition loc_330 : location_info := LocationInfo file_0 136 11 138 5.
  Definition loc_331 : location_info := LocationInfo file_0 137 6 137 29.
  Definition loc_332 : location_info := LocationInfo file_0 137 6 137 9.
  Definition loc_333 : location_info := LocationInfo file_0 137 12 137 28.
  Definition loc_334 : location_info := LocationInfo file_0 137 13 137 28.
  Definition loc_335 : location_info := LocationInfo file_0 137 14 137 20.
  Definition loc_336 : location_info := LocationInfo file_0 137 14 137 20.
  Definition loc_337 : location_info := LocationInfo file_0 137 16 137 19.
  Definition loc_338 : location_info := LocationInfo file_0 137 16 137 19.
  Definition loc_339 : location_info := LocationInfo file_0 134 7 134 22.
  Definition loc_340 : location_info := LocationInfo file_0 134 7 134 8.
  Definition loc_341 : location_info := LocationInfo file_0 134 7 134 8.
  Definition loc_342 : location_info := LocationInfo file_0 134 11 134 22.
  Definition loc_343 : location_info := LocationInfo file_0 134 11 134 22.
  Definition loc_344 : location_info := LocationInfo file_0 134 11 134 17.
  Definition loc_345 : location_info := LocationInfo file_0 134 11 134 17.
  Definition loc_346 : location_info := LocationInfo file_0 134 13 134 16.
  Definition loc_347 : location_info := LocationInfo file_0 134 13 134 16.
  Definition loc_348 : location_info := LocationInfo file_0 133 25 133 32.
  Definition loc_351 : location_info := LocationInfo file_0 133 7 133 23.
  Definition loc_352 : location_info := LocationInfo file_0 133 7 133 18.
  Definition loc_353 : location_info := LocationInfo file_0 133 7 133 18.
  Definition loc_354 : location_info := LocationInfo file_0 133 7 133 13.
  Definition loc_355 : location_info := LocationInfo file_0 133 7 133 13.
  Definition loc_356 : location_info := LocationInfo file_0 133 9 133 12.
  Definition loc_357 : location_info := LocationInfo file_0 133 9 133 12.
  Definition loc_358 : location_info := LocationInfo file_0 133 22 133 23.
  Definition loc_359 : location_info := LocationInfo file_0 133 22 133 23.
  Definition loc_360 : location_info := LocationInfo file_0 132 8 132 30.
  Definition loc_361 : location_info := LocationInfo file_0 132 8 132 12.
  Definition loc_362 : location_info := LocationInfo file_0 132 8 132 12.
  Definition loc_363 : location_info := LocationInfo file_0 132 9 132 12.
  Definition loc_364 : location_info := LocationInfo file_0 132 9 132 12.
  Definition loc_365 : location_info := LocationInfo file_0 132 16 132 30.
  Definition loc_366 : location_info := LocationInfo file_0 127 16 127 19.
  Definition loc_367 : location_info := LocationInfo file_0 127 17 127 19.
  Definition loc_368 : location_info := LocationInfo file_0 127 18 127 19.
  Definition loc_369 : location_info := LocationInfo file_0 127 18 127 19.
  Definition loc_374 : location_info := LocationInfo file_0 153 2 155 3.
  Definition loc_375 : location_info := LocationInfo file_0 156 2 156 22.
  Definition loc_376 : location_info := LocationInfo file_0 156 22 156 3.
  Definition loc_377 : location_info := LocationInfo file_0 157 2 157 34.
  Definition loc_378 : location_info := LocationInfo file_0 157 9 157 33.
  Definition loc_379 : location_info := LocationInfo file_0 157 9 157 17.
  Definition loc_380 : location_info := LocationInfo file_0 157 9 157 17.
  Definition loc_381 : location_info := LocationInfo file_0 157 18 157 32.
  Definition loc_382 : location_info := LocationInfo file_0 157 19 157 32.
  Definition loc_383 : location_info := LocationInfo file_0 157 20 157 24.
  Definition loc_384 : location_info := LocationInfo file_0 157 20 157 24.
  Definition loc_385 : location_info := LocationInfo file_0 157 22 157 23.
  Definition loc_386 : location_info := LocationInfo file_0 157 22 157 23.
  Definition loc_387 : location_info := LocationInfo file_0 156 2 156 21.
  Definition loc_388 : location_info := LocationInfo file_0 156 3 156 21.
  Definition loc_389 : location_info := LocationInfo file_0 156 4 156 15.
  Definition loc_390 : location_info := LocationInfo file_0 156 4 156 15.
  Definition loc_391 : location_info := LocationInfo file_0 156 4 156 8.
  Definition loc_392 : location_info := LocationInfo file_0 156 4 156 8.
  Definition loc_393 : location_info := LocationInfo file_0 156 6 156 7.
  Definition loc_394 : location_info := LocationInfo file_0 156 6 156 7.
  Definition loc_395 : location_info := LocationInfo file_0 153 36 155 3.
  Definition loc_396 : location_info := LocationInfo file_0 154 4 154 21.
  Definition loc_397 : location_info := LocationInfo file_0 154 11 154 20.
  Definition loc_398 : location_info := LocationInfo file_0 154 11 154 20.
  Definition loc_399 : location_info := LocationInfo file_0 154 11 154 15.
  Definition loc_400 : location_info := LocationInfo file_0 154 11 154 15.
  Definition loc_401 : location_info := LocationInfo file_0 154 13 154 14.
  Definition loc_402 : location_info := LocationInfo file_0 154 13 154 14.
  Definition loc_404 : location_info := LocationInfo file_0 153 5 153 34.
  Definition loc_405 : location_info := LocationInfo file_0 153 5 153 16.
  Definition loc_406 : location_info := LocationInfo file_0 153 5 153 16.
  Definition loc_407 : location_info := LocationInfo file_0 153 5 153 9.
  Definition loc_408 : location_info := LocationInfo file_0 153 5 153 9.
  Definition loc_409 : location_info := LocationInfo file_0 153 7 153 8.
  Definition loc_410 : location_info := LocationInfo file_0 153 7 153 8.
  Definition loc_411 : location_info := LocationInfo file_0 153 20 153 34.
  Definition loc_414 : location_info := LocationInfo file_0 170 2 172 3.
  Definition loc_415 : location_info := LocationInfo file_0 174 2 189 3.
  Definition loc_416 : location_info := LocationInfo file_0 174 21 185 3.
  Definition loc_417 : location_info := LocationInfo file_0 175 4 184 5.
  Definition loc_418 : location_info := LocationInfo file_0 175 36 180 5.
  Definition loc_419 : location_info := LocationInfo file_0 176 6 176 25.
  Definition loc_420 : location_info := LocationInfo file_0 176 25 176 7.
  Definition loc_421 : location_info := LocationInfo file_0 177 6 177 32.
  Definition loc_422 : location_info := LocationInfo file_0 178 6 178 29.
  Definition loc_423 : location_info := LocationInfo file_0 179 6 179 20.
  Definition loc_424 : location_info := LocationInfo file_0 179 6 179 15.
  Definition loc_425 : location_info := LocationInfo file_0 179 6 179 10.
  Definition loc_426 : location_info := LocationInfo file_0 179 6 179 10.
  Definition loc_427 : location_info := LocationInfo file_0 179 8 179 9.
  Definition loc_428 : location_info := LocationInfo file_0 179 8 179 9.
  Definition loc_429 : location_info := LocationInfo file_0 179 18 179 19.
  Definition loc_430 : location_info := LocationInfo file_0 179 18 179 19.
  Definition loc_431 : location_info := LocationInfo file_0 178 6 178 12.
  Definition loc_432 : location_info := LocationInfo file_0 178 6 178 12.
  Definition loc_433 : location_info := LocationInfo file_0 178 13 178 24.
  Definition loc_434 : location_info := LocationInfo file_0 178 14 178 24.
  Definition loc_435 : location_info := LocationInfo file_0 178 14 178 18.
  Definition loc_436 : location_info := LocationInfo file_0 178 14 178 18.
  Definition loc_437 : location_info := LocationInfo file_0 178 16 178 17.
  Definition loc_438 : location_info := LocationInfo file_0 178 16 178 17.
  Definition loc_439 : location_info := LocationInfo file_0 178 26 178 27.
  Definition loc_440 : location_info := LocationInfo file_0 178 26 178 27.
  Definition loc_441 : location_info := LocationInfo file_0 177 6 177 7.
  Definition loc_442 : location_info := LocationInfo file_0 177 10 177 31.
  Definition loc_443 : location_info := LocationInfo file_0 177 10 177 18.
  Definition loc_444 : location_info := LocationInfo file_0 177 10 177 18.
  Definition loc_445 : location_info := LocationInfo file_0 177 19 177 30.
  Definition loc_446 : location_info := LocationInfo file_0 177 20 177 30.
  Definition loc_447 : location_info := LocationInfo file_0 177 20 177 24.
  Definition loc_448 : location_info := LocationInfo file_0 177 20 177 24.
  Definition loc_449 : location_info := LocationInfo file_0 177 22 177 23.
  Definition loc_450 : location_info := LocationInfo file_0 177 22 177 23.
  Definition loc_451 : location_info := LocationInfo file_0 176 6 176 24.
  Definition loc_452 : location_info := LocationInfo file_0 176 7 176 24.
  Definition loc_453 : location_info := LocationInfo file_0 176 8 176 18.
  Definition loc_454 : location_info := LocationInfo file_0 176 8 176 18.
  Definition loc_455 : location_info := LocationInfo file_0 176 8 176 12.
  Definition loc_456 : location_info := LocationInfo file_0 176 8 176 12.
  Definition loc_457 : location_info := LocationInfo file_0 176 10 176 11.
  Definition loc_458 : location_info := LocationInfo file_0 176 10 176 11.
  Definition loc_459 : location_info := LocationInfo file_0 180 11 184 5.
  Definition loc_460 : location_info := LocationInfo file_0 181 6 181 24.
  Definition loc_461 : location_info := LocationInfo file_0 182 6 182 36.
  Definition loc_462 : location_info := LocationInfo file_0 183 6 183 15.
  Definition loc_463 : location_info := LocationInfo file_0 183 6 183 8.
  Definition loc_464 : location_info := LocationInfo file_0 183 7 183 8.
  Definition loc_465 : location_info := LocationInfo file_0 183 7 183 8.
  Definition loc_466 : location_info := LocationInfo file_0 183 11 183 14.
  Definition loc_467 : location_info := LocationInfo file_0 183 11 183 14.
  Definition loc_468 : location_info := LocationInfo file_0 182 6 182 10.
  Definition loc_469 : location_info := LocationInfo file_0 182 6 182 10.
  Definition loc_470 : location_info := LocationInfo file_0 182 11 182 30.
  Definition loc_471 : location_info := LocationInfo file_0 182 32 182 34.
  Definition loc_472 : location_info := LocationInfo file_0 182 32 182 34.
  Definition loc_473 : location_info := LocationInfo file_0 182 33 182 34.
  Definition loc_474 : location_info := LocationInfo file_0 182 33 182 34.
  Definition loc_475 : location_info := LocationInfo file_0 181 6 181 9.
  Definition loc_476 : location_info := LocationInfo file_0 181 12 181 23.
  Definition loc_477 : location_info := LocationInfo file_0 181 12 181 23.
  Definition loc_478 : location_info := LocationInfo file_0 181 12 181 16.
  Definition loc_479 : location_info := LocationInfo file_0 181 12 181 16.
  Definition loc_480 : location_info := LocationInfo file_0 181 14 181 15.
  Definition loc_481 : location_info := LocationInfo file_0 181 14 181 15.
  Definition loc_482 : location_info := LocationInfo file_0 175 7 175 35.
  Definition loc_483 : location_info := LocationInfo file_0 175 7 175 17.
  Definition loc_484 : location_info := LocationInfo file_0 175 7 175 17.
  Definition loc_485 : location_info := LocationInfo file_0 175 7 175 11.
  Definition loc_486 : location_info := LocationInfo file_0 175 7 175 11.
  Definition loc_487 : location_info := LocationInfo file_0 175 9 175 10.
  Definition loc_488 : location_info := LocationInfo file_0 175 9 175 10.
  Definition loc_489 : location_info := LocationInfo file_0 175 21 175 35.
  Definition loc_490 : location_info := LocationInfo file_0 185 9 189 3.
  Definition loc_491 : location_info := LocationInfo file_0 185 26 187 3.
  Definition loc_492 : location_info := LocationInfo file_0 186 4 186 27.
  Definition loc_493 : location_info := LocationInfo file_0 186 4 186 10.
  Definition loc_494 : location_info := LocationInfo file_0 186 4 186 10.
  Definition loc_495 : location_info := LocationInfo file_0 186 11 186 22.
  Definition loc_496 : location_info := LocationInfo file_0 186 12 186 22.
  Definition loc_497 : location_info := LocationInfo file_0 186 12 186 16.
  Definition loc_498 : location_info := LocationInfo file_0 186 12 186 16.
  Definition loc_499 : location_info := LocationInfo file_0 186 14 186 15.
  Definition loc_500 : location_info := LocationInfo file_0 186 14 186 15.
  Definition loc_501 : location_info := LocationInfo file_0 186 24 186 25.
  Definition loc_502 : location_info := LocationInfo file_0 186 24 186 25.
  Definition loc_503 : location_info := LocationInfo file_0 187 9 189 3.
  Definition loc_504 : location_info := LocationInfo file_0 188 4 188 28.
  Definition loc_505 : location_info := LocationInfo file_0 188 4 188 10.
  Definition loc_506 : location_info := LocationInfo file_0 188 4 188 10.
  Definition loc_507 : location_info := LocationInfo file_0 188 11 188 23.
  Definition loc_508 : location_info := LocationInfo file_0 188 12 188 23.
  Definition loc_509 : location_info := LocationInfo file_0 188 12 188 16.
  Definition loc_510 : location_info := LocationInfo file_0 188 12 188 16.
  Definition loc_511 : location_info := LocationInfo file_0 188 14 188 15.
  Definition loc_512 : location_info := LocationInfo file_0 188 14 188 15.
  Definition loc_513 : location_info := LocationInfo file_0 188 25 188 26.
  Definition loc_514 : location_info := LocationInfo file_0 188 25 188 26.
  Definition loc_515 : location_info := LocationInfo file_0 185 12 185 25.
  Definition loc_516 : location_info := LocationInfo file_0 185 12 185 13.
  Definition loc_517 : location_info := LocationInfo file_0 185 12 185 13.
  Definition loc_518 : location_info := LocationInfo file_0 185 16 185 25.
  Definition loc_519 : location_info := LocationInfo file_0 185 16 185 25.
  Definition loc_520 : location_info := LocationInfo file_0 185 16 185 20.
  Definition loc_521 : location_info := LocationInfo file_0 185 16 185 20.
  Definition loc_522 : location_info := LocationInfo file_0 185 18 185 19.
  Definition loc_523 : location_info := LocationInfo file_0 185 18 185 19.
  Definition loc_524 : location_info := LocationInfo file_0 174 5 174 19.
  Definition loc_525 : location_info := LocationInfo file_0 174 5 174 6.
  Definition loc_526 : location_info := LocationInfo file_0 174 5 174 6.
  Definition loc_527 : location_info := LocationInfo file_0 174 10 174 19.
  Definition loc_528 : location_info := LocationInfo file_0 174 10 174 19.
  Definition loc_529 : location_info := LocationInfo file_0 174 10 174 14.
  Definition loc_530 : location_info := LocationInfo file_0 174 10 174 14.
  Definition loc_531 : location_info := LocationInfo file_0 174 12 174 13.
  Definition loc_532 : location_info := LocationInfo file_0 174 12 174 13.
  Definition loc_533 : location_info := LocationInfo file_0 170 27 172 3.
  Definition loc_534 : location_info := LocationInfo file_0 171 4 171 11.
  Definition loc_537 : location_info := LocationInfo file_0 170 5 170 25.
  Definition loc_538 : location_info := LocationInfo file_0 170 5 170 7.
  Definition loc_539 : location_info := LocationInfo file_0 170 5 170 7.
  Definition loc_540 : location_info := LocationInfo file_0 170 6 170 7.
  Definition loc_541 : location_info := LocationInfo file_0 170 6 170 7.
  Definition loc_542 : location_info := LocationInfo file_0 170 11 170 25.
  Definition loc_545 : location_info := LocationInfo file_0 195 2 195 21.
  Definition loc_546 : location_info := LocationInfo file_0 196 2 196 14.
  Definition loc_547 : location_info := LocationInfo file_0 200 2 200 16.
  Definition loc_548 : location_info := LocationInfo file_0 202 2 202 24.
  Definition loc_549 : location_info := LocationInfo file_0 203 2 203 24.
  Definition loc_550 : location_info := LocationInfo file_0 205 2 205 16.
  Definition loc_551 : location_info := LocationInfo file_0 208 2 208 16.
  Definition loc_552 : location_info := LocationInfo file_0 209 2 209 24.
  Definition loc_553 : location_info := LocationInfo file_0 211 2 211 16.
  Definition loc_554 : location_info := LocationInfo file_0 214 2 214 16.
  Definition loc_555 : location_info := LocationInfo file_0 216 2 216 11.
  Definition loc_556 : location_info := LocationInfo file_0 216 9 216 10.
  Definition loc_557 : location_info := LocationInfo file_0 214 2 214 11.
  Definition loc_558 : location_info := LocationInfo file_0 214 2 214 11.
  Definition loc_559 : location_info := LocationInfo file_0 214 12 214 14.
  Definition loc_560 : location_info := LocationInfo file_0 214 13 214 14.
  Definition loc_561 : location_info := LocationInfo file_0 211 2 211 8.
  Definition loc_562 : location_info := LocationInfo file_0 211 2 211 8.
  Definition loc_563 : location_info := LocationInfo file_0 211 9 211 11.
  Definition loc_564 : location_info := LocationInfo file_0 211 10 211 11.
  Definition loc_565 : location_info := LocationInfo file_0 211 13 211 14.
  Definition loc_566 : location_info := LocationInfo file_0 209 9 209 22.
  Definition loc_567 : location_info := LocationInfo file_0 209 9 209 15.
  Definition loc_568 : location_info := LocationInfo file_0 209 9 209 15.
  Definition loc_569 : location_info := LocationInfo file_0 209 16 209 18.
  Definition loc_570 : location_info := LocationInfo file_0 209 17 209 18.
  Definition loc_571 : location_info := LocationInfo file_0 209 20 209 21.
  Definition loc_572 : location_info := LocationInfo file_0 208 2 208 8.
  Definition loc_573 : location_info := LocationInfo file_0 208 2 208 8.
  Definition loc_574 : location_info := LocationInfo file_0 208 9 208 11.
  Definition loc_575 : location_info := LocationInfo file_0 208 10 208 11.
  Definition loc_576 : location_info := LocationInfo file_0 208 13 208 14.
  Definition loc_577 : location_info := LocationInfo file_0 205 2 205 8.
  Definition loc_578 : location_info := LocationInfo file_0 205 2 205 8.
  Definition loc_579 : location_info := LocationInfo file_0 205 9 205 11.
  Definition loc_580 : location_info := LocationInfo file_0 205 10 205 11.
  Definition loc_581 : location_info := LocationInfo file_0 205 13 205 14.
  Definition loc_582 : location_info := LocationInfo file_0 203 9 203 22.
  Definition loc_583 : location_info := LocationInfo file_0 203 9 203 15.
  Definition loc_584 : location_info := LocationInfo file_0 203 9 203 15.
  Definition loc_585 : location_info := LocationInfo file_0 203 16 203 18.
  Definition loc_586 : location_info := LocationInfo file_0 203 17 203 18.
  Definition loc_587 : location_info := LocationInfo file_0 203 20 203 21.
  Definition loc_588 : location_info := LocationInfo file_0 202 9 202 22.
  Definition loc_589 : location_info := LocationInfo file_0 202 9 202 15.
  Definition loc_590 : location_info := LocationInfo file_0 202 9 202 15.
  Definition loc_591 : location_info := LocationInfo file_0 202 16 202 18.
  Definition loc_592 : location_info := LocationInfo file_0 202 17 202 18.
  Definition loc_593 : location_info := LocationInfo file_0 202 20 202 21.
  Definition loc_594 : location_info := LocationInfo file_0 200 2 200 8.
  Definition loc_595 : location_info := LocationInfo file_0 200 2 200 8.
  Definition loc_596 : location_info := LocationInfo file_0 200 9 200 11.
  Definition loc_597 : location_info := LocationInfo file_0 200 10 200 11.
  Definition loc_598 : location_info := LocationInfo file_0 200 13 200 14.
  Definition loc_599 : location_info := LocationInfo file_0 196 2 196 3.
  Definition loc_600 : location_info := LocationInfo file_0 196 6 196 13.
  Definition loc_601 : location_info := LocationInfo file_0 196 6 196 10.
  Definition loc_602 : location_info := LocationInfo file_0 196 6 196 10.
  Definition loc_603 : location_info := LocationInfo file_0 196 11 196 12.
  Definition loc_604 : location_info := LocationInfo file_0 195 13 195 20.
  Definition loc_605 : location_info := LocationInfo file_0 195 13 195 18.
  Definition loc_606 : location_info := LocationInfo file_0 195 13 195 18.

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
  Definition impl_init (global_alloc : loc): function := {|
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
          LocInfoE loc_35 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_35 (Call (LocInfoE loc_37 (global_alloc)) [@{expr} LocInfoE loc_38 (i2v (layout_of struct_tree).(ly_size) size_t) ]))) ;
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
  Definition impl_node (global_alloc : loc): function := {|
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
          LocInfoE loc_65 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_65 (Call (LocInfoE loc_67 (global_alloc)) [@{expr} LocInfoE loc_68 (i2v (layout_of struct_tree).(ly_size) size_t) ]))) ;
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
  Definition impl_free_tree (global_free global_free_tree : loc): function := {|
    f_args := [
      ("t", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_102 ;
        if: LocInfoE loc_102 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_102 ((LocInfoE loc_103 (use{PtrOp} (LocInfoE loc_105 (!{PtrOp} (LocInfoE loc_106 ("t")))))) !={PtrOp, PtrOp} (LocInfoE loc_107 (NULL)))))
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
        expr: (LocInfoE loc_77 (Call (LocInfoE loc_79 (global_free)) [@{expr} LocInfoE loc_80 (i2v (layout_of struct_tree).(ly_size) size_t) ;
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
        if: LocInfoE loc_162 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_162 ((LocInfoE loc_163 (use{PtrOp} (LocInfoE loc_165 (!{PtrOp} (LocInfoE loc_166 ("t")))))) ={PtrOp, PtrOp} (LocInfoE loc_167 (NULL)))))
        then
        locinfo: loc_159 ;
          Goto "#8"
        else
        locinfo: loc_150 ;
          Goto "#9"
      ]> $
      <[ "#1" :=
        locinfo: loc_150 ;
        if: LocInfoE loc_150 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_150 ((LocInfoE loc_151 (use{IntOp size_t} (LocInfoE loc_152 ((LocInfoE loc_153 (!{PtrOp} (LocInfoE loc_155 (!{PtrOp} (LocInfoE loc_156 ("t")))))) at{struct_tree} "key")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_157 (use{IntOp size_t} (LocInfoE loc_158 ("k")))))))
        then
        locinfo: loc_147 ;
          Goto "#6"
        else
        locinfo: loc_138 ;
          Goto "#7"
      ]> $
      <[ "#2" :=
        locinfo: loc_138 ;
        if: LocInfoE loc_138 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_138 ((LocInfoE loc_139 (use{IntOp size_t} (LocInfoE loc_140 ("k")))) <{IntOp size_t, IntOp size_t} (LocInfoE loc_141 (use{IntOp size_t} (LocInfoE loc_142 ((LocInfoE loc_143 (!{PtrOp} (LocInfoE loc_145 (!{PtrOp} (LocInfoE loc_146 ("t")))))) at{struct_tree} "key")))))))
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
        Return (LocInfoE loc_148 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_148 (i2v 1 i32))))
      ]> $
      <[ "#7" :=
        locinfo: loc_138 ;
        Goto "#2"
      ]> $
      <[ "#8" :=
        locinfo: loc_159 ;
        Return (LocInfoE loc_160 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_160 (i2v 0 i32))))
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
          LocInfoE loc_225 (&(LocInfoE loc_227 (!{PtrOp} (LocInfoE loc_228 ("t"))))) ;
        locinfo: loc_171 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_219 ;
        if: LocInfoE loc_219 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_219 ((LocInfoE loc_220 (use{PtrOp} (LocInfoE loc_222 (!{PtrOp} (LocInfoE loc_223 ("cur")))))) !={PtrOp, PtrOp} (LocInfoE loc_224 (NULL)))))
        then
        locinfo: loc_210 ;
          Goto "#2"
        else
        locinfo: loc_172 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_210 ;
        if: LocInfoE loc_210 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_210 ((LocInfoE loc_211 (use{IntOp size_t} (LocInfoE loc_212 ((LocInfoE loc_213 (!{PtrOp} (LocInfoE loc_215 (!{PtrOp} (LocInfoE loc_216 ("cur")))))) at{struct_tree} "key")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_217 (use{IntOp size_t} (LocInfoE loc_218 ("k")))))))
        then
        locinfo: loc_207 ;
          Goto "#8"
        else
        locinfo: loc_198 ;
          Goto "#9"
      ]> $
      <[ "#3" :=
        locinfo: loc_172 ;
        Return (LocInfoE loc_173 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_173 (i2v 0 i32))))
      ]> $
      <[ "#4" :=
        locinfo: loc_198 ;
        if: LocInfoE loc_198 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_198 ((LocInfoE loc_199 (use{IntOp size_t} (LocInfoE loc_200 ("k")))) <{IntOp size_t, IntOp size_t} (LocInfoE loc_201 (use{IntOp size_t} (LocInfoE loc_202 ((LocInfoE loc_203 (!{PtrOp} (LocInfoE loc_205 (!{PtrOp} (LocInfoE loc_206 ("cur")))))) at{struct_tree} "key")))))))
        then
        locinfo: loc_181 ;
          Goto "#6"
        else
        locinfo: loc_190 ;
          Goto "#7"
      ]> $
      <[ "#5" :=
        locinfo: loc_178 ;
        Goto "continue15"
      ]> $
      <[ "#6" :=
        locinfo: loc_181 ;
        LocInfoE loc_182 ("cur") <-{ PtrOp }
          LocInfoE loc_183 (&(LocInfoE loc_184 ((LocInfoE loc_185 (!{PtrOp} (LocInfoE loc_187 (!{PtrOp} (LocInfoE loc_188 ("cur")))))) at{struct_tree} "left"))) ;
        locinfo: loc_178 ;
        Goto "#5"
      ]> $
      <[ "#7" :=
        locinfo: loc_190 ;
        LocInfoE loc_191 ("cur") <-{ PtrOp }
          LocInfoE loc_192 (&(LocInfoE loc_193 ((LocInfoE loc_194 (!{PtrOp} (LocInfoE loc_196 (!{PtrOp} (LocInfoE loc_197 ("cur")))))) at{struct_tree} "right"))) ;
        locinfo: loc_178 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        locinfo: loc_207 ;
        Return (LocInfoE loc_208 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_208 (i2v 1 i32))))
      ]> $
      <[ "#9" :=
        locinfo: loc_198 ;
        Goto "#4"
      ]> $
      <[ "continue15" :=
        locinfo: loc_171 ;
        Goto "#1"
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
        locinfo: loc_294 ;
        if: LocInfoE loc_294 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_294 ((LocInfoE loc_295 (use{PtrOp} (LocInfoE loc_297 (!{PtrOp} (LocInfoE loc_298 ("t")))))) ={PtrOp, PtrOp} (LocInfoE loc_299 (NULL)))))
        then
        locinfo: loc_235 ;
          Goto "#1"
        else
        locinfo: loc_285 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_235 ;
        LocInfoE loc_237 (!{PtrOp} (LocInfoE loc_238 ("t"))) <-{ PtrOp }
          LocInfoE loc_239 (Call (LocInfoE loc_241 (global_node)) [@{expr} LocInfoE loc_242 (NULL) ;
          LocInfoE loc_243 (use{IntOp size_t} (LocInfoE loc_244 ("k"))) ;
          LocInfoE loc_245 (NULL) ]) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_285 ;
        if: LocInfoE loc_285 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_285 ((LocInfoE loc_286 (use{IntOp size_t} (LocInfoE loc_287 ((LocInfoE loc_288 (!{PtrOp} (LocInfoE loc_290 (!{PtrOp} (LocInfoE loc_291 ("t")))))) at{struct_tree} "key")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_292 (use{IntOp size_t} (LocInfoE loc_293 ("k")))))))
        then
        locinfo: loc_282 ;
          Goto "#6"
        else
        locinfo: loc_273 ;
          Goto "#7"
      ]> $
      <[ "#3" :=
        locinfo: loc_273 ;
        if: LocInfoE loc_273 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_273 ((LocInfoE loc_274 (use{IntOp size_t} (LocInfoE loc_275 ("k")))) <{IntOp size_t, IntOp size_t} (LocInfoE loc_276 (use{IntOp size_t} (LocInfoE loc_277 ((LocInfoE loc_278 (!{PtrOp} (LocInfoE loc_280 (!{PtrOp} (LocInfoE loc_281 ("t")))))) at{struct_tree} "key")))))))
        then
        locinfo: loc_250 ;
          Goto "#4"
        else
        locinfo: loc_262 ;
          Goto "#5"
      ]> $
      <[ "#4" :=
        locinfo: loc_250 ;
        expr: (LocInfoE loc_250 (Call (LocInfoE loc_252 (global_insert_rec)) [@{expr} LocInfoE loc_253 (&(LocInfoE loc_254 ((LocInfoE loc_255 (!{PtrOp} (LocInfoE loc_257 (!{PtrOp} (LocInfoE loc_258 ("t")))))) at{struct_tree} "left"))) ;
        LocInfoE loc_259 (use{IntOp size_t} (LocInfoE loc_260 ("k"))) ])) ;
        Return (VOID)
      ]> $
      <[ "#5" :=
        locinfo: loc_262 ;
        expr: (LocInfoE loc_262 (Call (LocInfoE loc_264 (global_insert_rec)) [@{expr} LocInfoE loc_265 (&(LocInfoE loc_266 ((LocInfoE loc_267 (!{PtrOp} (LocInfoE loc_269 (!{PtrOp} (LocInfoE loc_270 ("t")))))) at{struct_tree} "right"))) ;
        LocInfoE loc_271 (use{IntOp size_t} (LocInfoE loc_272 ("k"))) ])) ;
        Return (VOID)
      ]> $
      <[ "#6" :=
        locinfo: loc_282 ;
        Return (VOID)
      ]> $
      <[ "#7" :=
        locinfo: loc_273 ;
        Goto "#3"
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
          LocInfoE loc_366 (&(LocInfoE loc_368 (!{PtrOp} (LocInfoE loc_369 ("t"))))) ;
        locinfo: loc_303 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_360 ;
        if: LocInfoE loc_360 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_360 ((LocInfoE loc_361 (use{PtrOp} (LocInfoE loc_363 (!{PtrOp} (LocInfoE loc_364 ("cur")))))) !={PtrOp, PtrOp} (LocInfoE loc_365 (NULL)))))
        then
        locinfo: loc_351 ;
          Goto "#2"
        else
        locinfo: loc_304 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_351 ;
        if: LocInfoE loc_351 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_351 ((LocInfoE loc_352 (use{IntOp size_t} (LocInfoE loc_353 ((LocInfoE loc_354 (!{PtrOp} (LocInfoE loc_356 (!{PtrOp} (LocInfoE loc_357 ("cur")))))) at{struct_tree} "key")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_358 (use{IntOp size_t} (LocInfoE loc_359 ("k")))))))
        then
        locinfo: loc_348 ;
          Goto "#8"
        else
        locinfo: loc_339 ;
          Goto "#9"
      ]> $
      <[ "#3" :=
        locinfo: loc_304 ;
        LocInfoE loc_306 (!{PtrOp} (LocInfoE loc_307 ("cur"))) <-{ PtrOp }
          LocInfoE loc_308 (Call (LocInfoE loc_310 (global_node)) [@{expr} LocInfoE loc_311 (NULL) ;
          LocInfoE loc_312 (use{IntOp size_t} (LocInfoE loc_313 ("k"))) ;
          LocInfoE loc_314 (NULL) ]) ;
        Return (VOID)
      ]> $
      <[ "#4" :=
        locinfo: loc_339 ;
        if: LocInfoE loc_339 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_339 ((LocInfoE loc_340 (use{IntOp size_t} (LocInfoE loc_341 ("k")))) <{IntOp size_t, IntOp size_t} (LocInfoE loc_342 (use{IntOp size_t} (LocInfoE loc_343 ((LocInfoE loc_344 (!{PtrOp} (LocInfoE loc_346 (!{PtrOp} (LocInfoE loc_347 ("cur")))))) at{struct_tree} "key")))))))
        then
        locinfo: loc_322 ;
          Goto "#6"
        else
        locinfo: loc_331 ;
          Goto "#7"
      ]> $
      <[ "#5" :=
        locinfo: loc_319 ;
        Goto "continue27"
      ]> $
      <[ "#6" :=
        locinfo: loc_322 ;
        LocInfoE loc_323 ("cur") <-{ PtrOp }
          LocInfoE loc_324 (&(LocInfoE loc_325 ((LocInfoE loc_326 (!{PtrOp} (LocInfoE loc_328 (!{PtrOp} (LocInfoE loc_329 ("cur")))))) at{struct_tree} "left"))) ;
        locinfo: loc_319 ;
        Goto "#5"
      ]> $
      <[ "#7" :=
        locinfo: loc_331 ;
        LocInfoE loc_332 ("cur") <-{ PtrOp }
          LocInfoE loc_333 (&(LocInfoE loc_334 ((LocInfoE loc_335 (!{PtrOp} (LocInfoE loc_337 (!{PtrOp} (LocInfoE loc_338 ("cur")))))) at{struct_tree} "right"))) ;
        locinfo: loc_319 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        locinfo: loc_348 ;
        Return (VOID)
      ]> $
      <[ "#9" :=
        locinfo: loc_339 ;
        Goto "#4"
      ]> $
      <[ "continue27" :=
        locinfo: loc_303 ;
        Goto "#1"
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
        locinfo: loc_404 ;
        if: LocInfoE loc_404 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_404 ((LocInfoE loc_405 (use{PtrOp} (LocInfoE loc_406 ((LocInfoE loc_407 (!{PtrOp} (LocInfoE loc_409 (!{PtrOp} (LocInfoE loc_410 ("t")))))) at{struct_tree} "right")))) ={PtrOp, PtrOp} (LocInfoE loc_411 (NULL)))))
        then
        locinfo: loc_396 ;
          Goto "#2"
        else
        locinfo: loc_375 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_375 ;
        expr: (LocInfoE loc_387 (&(LocInfoE loc_388 ((LocInfoE loc_389 (!{PtrOp} (LocInfoE loc_390 ((LocInfoE loc_391 (!{PtrOp} (LocInfoE loc_393 (!{PtrOp} (LocInfoE loc_394 ("t")))))) at{struct_tree} "right")))) at{struct_tree} "key")))) ;
        locinfo: loc_377 ;
        Return (LocInfoE loc_378 (Call (LocInfoE loc_380 (global_tree_max)) [@{expr} LocInfoE loc_381 (&(LocInfoE loc_382 ((LocInfoE loc_383 (!{PtrOp} (LocInfoE loc_385 (!{PtrOp} (LocInfoE loc_386 ("t")))))) at{struct_tree} "right"))) ]))
      ]> $
      <[ "#2" :=
        locinfo: loc_396 ;
        Return (LocInfoE loc_397 (use{IntOp size_t} (LocInfoE loc_398 ((LocInfoE loc_399 (!{PtrOp} (LocInfoE loc_401 (!{PtrOp} (LocInfoE loc_402 ("t")))))) at{struct_tree} "key"))))
      ]> $
      <[ "#3" :=
        locinfo: loc_375 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [remove]. *)
  Definition impl_remove (global_free global_remove global_tree_max : loc): function := {|
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
        locinfo: loc_537 ;
        if: LocInfoE loc_537 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_537 ((LocInfoE loc_538 (use{PtrOp} (LocInfoE loc_540 (!{PtrOp} (LocInfoE loc_541 ("t")))))) ={PtrOp, PtrOp} (LocInfoE loc_542 (NULL)))))
        then
        locinfo: loc_534 ;
          Goto "#8"
        else
        locinfo: loc_524 ;
          Goto "#9"
      ]> $
      <[ "#1" :=
        locinfo: loc_524 ;
        if: LocInfoE loc_524 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_524 ((LocInfoE loc_525 (use{IntOp size_t} (LocInfoE loc_526 ("k")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_527 (use{IntOp size_t} (LocInfoE loc_528 ((LocInfoE loc_529 (!{PtrOp} (LocInfoE loc_531 (!{PtrOp} (LocInfoE loc_532 ("t")))))) at{struct_tree} "key")))))))
        then
        locinfo: loc_482 ;
          Goto "#2"
        else
        locinfo: loc_515 ;
          Goto "#5"
      ]> $
      <[ "#2" :=
        locinfo: loc_482 ;
        if: LocInfoE loc_482 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_482 ((LocInfoE loc_483 (use{PtrOp} (LocInfoE loc_484 ((LocInfoE loc_485 (!{PtrOp} (LocInfoE loc_487 (!{PtrOp} (LocInfoE loc_488 ("t")))))) at{struct_tree} "left")))) !={PtrOp, PtrOp} (LocInfoE loc_489 (NULL)))))
        then
        locinfo: loc_419 ;
          Goto "#3"
        else
        locinfo: loc_460 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_419 ;
        expr: (LocInfoE loc_451 (&(LocInfoE loc_452 ((LocInfoE loc_453 (!{PtrOp} (LocInfoE loc_454 ((LocInfoE loc_455 (!{PtrOp} (LocInfoE loc_457 (!{PtrOp} (LocInfoE loc_458 ("t")))))) at{struct_tree} "left")))) at{struct_tree} "key")))) ;
        locinfo: loc_421 ;
        LocInfoE loc_441 ("m") <-{ IntOp size_t }
          LocInfoE loc_442 (Call (LocInfoE loc_444 (global_tree_max)) [@{expr} LocInfoE loc_445 (&(LocInfoE loc_446 ((LocInfoE loc_447 (!{PtrOp} (LocInfoE loc_449 (!{PtrOp} (LocInfoE loc_450 ("t")))))) at{struct_tree} "left"))) ]) ;
        locinfo: loc_422 ;
        expr: (LocInfoE loc_422 (Call (LocInfoE loc_432 (global_remove)) [@{expr} LocInfoE loc_433 (&(LocInfoE loc_434 ((LocInfoE loc_435 (!{PtrOp} (LocInfoE loc_437 (!{PtrOp} (LocInfoE loc_438 ("t")))))) at{struct_tree} "left"))) ;
        LocInfoE loc_439 (use{IntOp size_t} (LocInfoE loc_440 ("m"))) ])) ;
        locinfo: loc_423 ;
        LocInfoE loc_424 ((LocInfoE loc_425 (!{PtrOp} (LocInfoE loc_427 (!{PtrOp} (LocInfoE loc_428 ("t")))))) at{struct_tree} "key") <-{ IntOp size_t }
          LocInfoE loc_429 (use{IntOp size_t} (LocInfoE loc_430 ("m"))) ;
        Return (VOID)
      ]> $
      <[ "#4" :=
        locinfo: loc_460 ;
        LocInfoE loc_475 ("tmp") <-{ PtrOp }
          LocInfoE loc_476 (use{PtrOp} (LocInfoE loc_477 ((LocInfoE loc_478 (!{PtrOp} (LocInfoE loc_480 (!{PtrOp} (LocInfoE loc_481 ("t")))))) at{struct_tree} "right"))) ;
        locinfo: loc_461 ;
        expr: (LocInfoE loc_461 (Call (LocInfoE loc_469 (global_free)) [@{expr} LocInfoE loc_470 (i2v (layout_of struct_tree).(ly_size) size_t) ;
        LocInfoE loc_471 (use{PtrOp} (LocInfoE loc_473 (!{PtrOp} (LocInfoE loc_474 ("t"))))) ])) ;
        locinfo: loc_462 ;
        LocInfoE loc_464 (!{PtrOp} (LocInfoE loc_465 ("t"))) <-{ PtrOp }
          LocInfoE loc_466 (use{PtrOp} (LocInfoE loc_467 ("tmp"))) ;
        Return (VOID)
      ]> $
      <[ "#5" :=
        locinfo: loc_515 ;
        if: LocInfoE loc_515 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_515 ((LocInfoE loc_516 (use{IntOp size_t} (LocInfoE loc_517 ("k")))) <{IntOp size_t, IntOp size_t} (LocInfoE loc_518 (use{IntOp size_t} (LocInfoE loc_519 ((LocInfoE loc_520 (!{PtrOp} (LocInfoE loc_522 (!{PtrOp} (LocInfoE loc_523 ("t")))))) at{struct_tree} "key")))))))
        then
        locinfo: loc_492 ;
          Goto "#6"
        else
        locinfo: loc_504 ;
          Goto "#7"
      ]> $
      <[ "#6" :=
        locinfo: loc_492 ;
        expr: (LocInfoE loc_492 (Call (LocInfoE loc_494 (global_remove)) [@{expr} LocInfoE loc_495 (&(LocInfoE loc_496 ((LocInfoE loc_497 (!{PtrOp} (LocInfoE loc_499 (!{PtrOp} (LocInfoE loc_500 ("t")))))) at{struct_tree} "left"))) ;
        LocInfoE loc_501 (use{IntOp size_t} (LocInfoE loc_502 ("k"))) ])) ;
        Return (VOID)
      ]> $
      <[ "#7" :=
        locinfo: loc_504 ;
        expr: (LocInfoE loc_504 (Call (LocInfoE loc_506 (global_remove)) [@{expr} LocInfoE loc_507 (&(LocInfoE loc_508 ((LocInfoE loc_509 (!{PtrOp} (LocInfoE loc_511 (!{PtrOp} (LocInfoE loc_512 ("t")))))) at{struct_tree} "right"))) ;
        LocInfoE loc_513 (use{IntOp size_t} (LocInfoE loc_514 ("k"))) ])) ;
        Return (VOID)
      ]> $
      <[ "#8" :=
        locinfo: loc_534 ;
        Return (VOID)
      ]> $
      <[ "#9" :=
        locinfo: loc_524 ;
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
          LocInfoE loc_604 (Call (LocInfoE loc_606 (global_empty)) [@{expr}  ]) ;
        locinfo: loc_546 ;
        LocInfoE loc_599 ("t") <-{ PtrOp }
          LocInfoE loc_600 (Call (LocInfoE loc_602 (global_init)) [@{expr} LocInfoE loc_603 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_603 (i2v 3 i32))) ]) ;
        locinfo: loc_547 ;
        expr: (LocInfoE loc_547 (Call (LocInfoE loc_595 (global_insert)) [@{expr} LocInfoE loc_596 (&(LocInfoE loc_597 ("t"))) ;
        LocInfoE loc_598 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_598 (i2v 2 i32))) ])) ;
        locinfo: loc_548 ;
        assert: (LocInfoE loc_588 (Call (LocInfoE loc_590 (global_member)) [@{expr} LocInfoE loc_591 (&(LocInfoE loc_592 ("t"))) ;
        LocInfoE loc_593 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_593 (i2v 2 i32))) ])) ;
        locinfo: loc_549 ;
        assert: (LocInfoE loc_582 (Call (LocInfoE loc_584 (global_member)) [@{expr} LocInfoE loc_585 (&(LocInfoE loc_586 ("t"))) ;
        LocInfoE loc_587 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_587 (i2v 3 i32))) ])) ;
        locinfo: loc_550 ;
        expr: (LocInfoE loc_550 (Call (LocInfoE loc_578 (global_remove)) [@{expr} LocInfoE loc_579 (&(LocInfoE loc_580 ("t"))) ;
        LocInfoE loc_581 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_581 (i2v 3 i32))) ])) ;
        locinfo: loc_551 ;
        expr: (LocInfoE loc_551 (Call (LocInfoE loc_573 (global_insert)) [@{expr} LocInfoE loc_574 (&(LocInfoE loc_575 ("t"))) ;
        LocInfoE loc_576 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_576 (i2v 3 i32))) ])) ;
        locinfo: loc_552 ;
        assert: (LocInfoE loc_566 (Call (LocInfoE loc_568 (global_member)) [@{expr} LocInfoE loc_569 (&(LocInfoE loc_570 ("t"))) ;
        LocInfoE loc_571 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_571 (i2v 2 i32))) ])) ;
        locinfo: loc_553 ;
        expr: (LocInfoE loc_553 (Call (LocInfoE loc_562 (global_remove)) [@{expr} LocInfoE loc_563 (&(LocInfoE loc_564 ("t"))) ;
        LocInfoE loc_565 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_565 (i2v 3 i32))) ])) ;
        locinfo: loc_554 ;
        expr: (LocInfoE loc_554 (Call (LocInfoE loc_558 (global_free_tree)) [@{expr} LocInfoE loc_559 (&(LocInfoE loc_560 ("t"))) ])) ;
        locinfo: loc_555 ;
        Return (LocInfoE loc_556 (i2v 0 i32))
      ]> $∅
    )%E
  |}.
End code.
