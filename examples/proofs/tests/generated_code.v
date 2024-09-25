From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/tests.c]. *)
Section code.
  Definition file_0 : string := "include/assume.h".
  Definition file_1 : string := "examples/tests.c".
  Definition file_2 : string := "include/refinedc.h".
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
  Definition loc_18 : location_info := LocationInfo file_1 10 2 10 19.
  Definition loc_19 : location_info := LocationInfo file_1 11 2 11 13.
  Definition loc_20 : location_info := LocationInfo file_1 12 2 12 12.
  Definition loc_21 : location_info := LocationInfo file_1 13 2 13 14.
  Definition loc_22 : location_info := LocationInfo file_1 14 2 14 13.
  Definition loc_23 : location_info := LocationInfo file_1 16 2 16 21.
  Definition loc_24 : location_info := LocationInfo file_1 17 2 17 21.
  Definition loc_25 : location_info := LocationInfo file_1 18 2 18 21.
  Definition loc_26 : location_info := LocationInfo file_1 19 2 19 21.
  Definition loc_27 : location_info := LocationInfo file_1 20 2 20 21.
  Definition loc_28 : location_info := LocationInfo file_1 22 2 22 17.
  Definition loc_29 : location_info := LocationInfo file_1 23 2 23 16.
  Definition loc_30 : location_info := LocationInfo file_1 24 2 24 16.
  Definition loc_31 : location_info := LocationInfo file_1 25 2 25 16.
  Definition loc_32 : location_info := LocationInfo file_1 26 2 26 16.
  Definition loc_33 : location_info := LocationInfo file_1 28 2 28 9.
  Definition loc_35 : location_info := LocationInfo file_1 26 9 26 16.
  Definition loc_37 : location_info := LocationInfo file_1 26 2 26 16.
  Definition loc_38 : location_info := LocationInfo file_1 26 5 26 7.
  Definition loc_40 : location_info := LocationInfo file_1 26 6 26 7.
  Definition loc_41 : location_info := LocationInfo file_1 26 6 26 7.
  Definition loc_42 : location_info := LocationInfo file_1 25 9 25 16.
  Definition loc_44 : location_info := LocationInfo file_1 25 2 25 16.
  Definition loc_45 : location_info := LocationInfo file_1 25 5 25 7.
  Definition loc_47 : location_info := LocationInfo file_1 25 6 25 7.
  Definition loc_48 : location_info := LocationInfo file_1 25 6 25 7.
  Definition loc_49 : location_info := LocationInfo file_1 24 9 24 16.
  Definition loc_51 : location_info := LocationInfo file_1 24 2 24 16.
  Definition loc_52 : location_info := LocationInfo file_1 24 5 24 7.
  Definition loc_54 : location_info := LocationInfo file_1 24 6 24 7.
  Definition loc_55 : location_info := LocationInfo file_1 24 6 24 7.
  Definition loc_56 : location_info := LocationInfo file_1 23 9 23 16.
  Definition loc_58 : location_info := LocationInfo file_1 23 2 23 16.
  Definition loc_59 : location_info := LocationInfo file_1 23 5 23 7.
  Definition loc_61 : location_info := LocationInfo file_1 23 6 23 7.
  Definition loc_62 : location_info := LocationInfo file_1 23 6 23 7.
  Definition loc_63 : location_info := LocationInfo file_1 22 10 22 17.
  Definition loc_65 : location_info := LocationInfo file_1 22 2 22 17.
  Definition loc_66 : location_info := LocationInfo file_1 22 5 22 8.
  Definition loc_68 : location_info := LocationInfo file_1 22 6 22 8.
  Definition loc_69 : location_info := LocationInfo file_1 22 6 22 8.
  Definition loc_70 : location_info := LocationInfo file_1 20 14 20 21.
  Definition loc_72 : location_info := LocationInfo file_1 20 2 20 21.
  Definition loc_73 : location_info := LocationInfo file_1 20 5 20 12.
  Definition loc_74 : location_info := LocationInfo file_1 20 5 20 7.
  Definition loc_75 : location_info := LocationInfo file_1 20 5 20 7.
  Definition loc_76 : location_info := LocationInfo file_1 20 11 20 12.
  Definition loc_77 : location_info := LocationInfo file_1 20 11 20 12.
  Definition loc_78 : location_info := LocationInfo file_1 19 14 19 21.
  Definition loc_80 : location_info := LocationInfo file_1 19 2 19 21.
  Definition loc_81 : location_info := LocationInfo file_1 19 5 19 12.
  Definition loc_82 : location_info := LocationInfo file_1 19 5 19 7.
  Definition loc_83 : location_info := LocationInfo file_1 19 5 19 7.
  Definition loc_84 : location_info := LocationInfo file_1 19 11 19 12.
  Definition loc_85 : location_info := LocationInfo file_1 19 11 19 12.
  Definition loc_86 : location_info := LocationInfo file_1 18 14 18 21.
  Definition loc_88 : location_info := LocationInfo file_1 18 2 18 21.
  Definition loc_89 : location_info := LocationInfo file_1 18 5 18 12.
  Definition loc_90 : location_info := LocationInfo file_1 18 5 18 7.
  Definition loc_91 : location_info := LocationInfo file_1 18 5 18 7.
  Definition loc_92 : location_info := LocationInfo file_1 18 11 18 12.
  Definition loc_93 : location_info := LocationInfo file_1 18 11 18 12.
  Definition loc_94 : location_info := LocationInfo file_1 17 14 17 21.
  Definition loc_96 : location_info := LocationInfo file_1 17 2 17 21.
  Definition loc_97 : location_info := LocationInfo file_1 17 5 17 12.
  Definition loc_98 : location_info := LocationInfo file_1 17 5 17 7.
  Definition loc_99 : location_info := LocationInfo file_1 17 5 17 7.
  Definition loc_100 : location_info := LocationInfo file_1 17 11 17 12.
  Definition loc_101 : location_info := LocationInfo file_1 17 11 17 12.
  Definition loc_102 : location_info := LocationInfo file_1 16 14 16 21.
  Definition loc_104 : location_info := LocationInfo file_1 16 2 16 21.
  Definition loc_105 : location_info := LocationInfo file_1 16 5 16 12.
  Definition loc_106 : location_info := LocationInfo file_1 16 5 16 7.
  Definition loc_107 : location_info := LocationInfo file_1 16 5 16 7.
  Definition loc_108 : location_info := LocationInfo file_1 16 11 16 12.
  Definition loc_109 : location_info := LocationInfo file_1 16 11 16 12.
  Definition loc_110 : location_info := LocationInfo file_1 14 11 14 12.
  Definition loc_113 : location_info := LocationInfo file_1 13 12 13 13.
  Definition loc_116 : location_info := LocationInfo file_1 12 10 12 11.
  Definition loc_119 : location_info := LocationInfo file_1 11 11 11 12.
  Definition loc_122 : location_info := LocationInfo file_1 10 17 10 18.
  Definition loc_127 : location_info := LocationInfo file_1 33 2 33 11.
  Definition loc_128 : location_info := LocationInfo file_1 33 9 33 10.
  Definition loc_131 : location_info := LocationInfo file_1 41 2 41 16.
  Definition loc_132 : location_info := LocationInfo file_1 42 2 42 27.
  Definition loc_133 : location_info := LocationInfo file_1 43 2 43 92.
  Definition loc_134 : location_info := LocationInfo file_1 43 9 43 90.
  Definition loc_135 : location_info := LocationInfo file_1 43 9 43 85.
  Definition loc_136 : location_info := LocationInfo file_1 43 10 43 34.
  Definition loc_137 : location_info := LocationInfo file_1 43 10 43 16.
  Definition loc_138 : location_info := LocationInfo file_1 43 11 43 16.
  Definition loc_139 : location_info := LocationInfo file_1 43 20 43 34.
  Definition loc_140 : location_info := LocationInfo file_1 43 37 43 80.
  Definition loc_141 : location_info := LocationInfo file_1 43 37 43 76.
  Definition loc_142 : location_info := LocationInfo file_1 43 38 43 47.
  Definition loc_143 : location_info := LocationInfo file_1 43 38 43 45.
  Definition loc_144 : location_info := LocationInfo file_1 43 38 43 45.
  Definition loc_145 : location_info := LocationInfo file_1 43 50 43 59.
  Definition loc_146 : location_info := LocationInfo file_1 43 50 43 57.
  Definition loc_147 : location_info := LocationInfo file_1 43 50 43 57.
  Definition loc_148 : location_info := LocationInfo file_1 43 62 43 75.
  Definition loc_149 : location_info := LocationInfo file_1 43 62 43 73.
  Definition loc_150 : location_info := LocationInfo file_1 43 62 43 73.
  Definition loc_151 : location_info := LocationInfo file_1 43 79 43 80.
  Definition loc_152 : location_info := LocationInfo file_1 43 83 43 84.
  Definition loc_153 : location_info := LocationInfo file_1 43 89 43 90.
  Definition loc_154 : location_info := LocationInfo file_1 42 9 42 25.
  Definition loc_155 : location_info := LocationInfo file_1 42 9 42 20.
  Definition loc_156 : location_info := LocationInfo file_1 42 10 42 11.
  Definition loc_157 : location_info := LocationInfo file_1 42 14 42 15.
  Definition loc_158 : location_info := LocationInfo file_1 42 18 42 19.
  Definition loc_159 : location_info := LocationInfo file_1 42 24 42 25.
  Definition loc_160 : location_info := LocationInfo file_1 41 14 41 15.
  Definition loc_165 : location_info := LocationInfo file_1 48 2 48 30.
  Definition loc_166 : location_info := LocationInfo file_1 49 2 49 17.
  Definition loc_167 : location_info := LocationInfo file_1 49 9 49 15.
  Definition loc_168 : location_info := LocationInfo file_1 49 9 49 10.
  Definition loc_169 : location_info := LocationInfo file_1 49 14 49 15.
  Definition loc_170 : location_info := LocationInfo file_1 48 2 48 29.
  Definition loc_171 : location_info := LocationInfo file_1 48 3 48 7.
  Definition loc_173 : location_info := LocationInfo file_1 48 5 48 6.
  Definition loc_174 : location_info := LocationInfo file_1 48 10 48 24.
  Definition loc_175 : location_info := LocationInfo file_1 48 10 48 21.
  Definition loc_176 : location_info := LocationInfo file_1 48 10 48 19.
  Definition loc_177 : location_info := LocationInfo file_1 48 10 48 19.
  Definition loc_178 : location_info := LocationInfo file_1 48 23 48 24.
  Definition loc_179 : location_info := LocationInfo file_1 48 27 48 28.
  Definition loc_182 : location_info := LocationInfo file_1 55 2 55 29.
  Definition loc_183 : location_info := LocationInfo file_1 56 2 56 30.
  Definition loc_184 : location_info := LocationInfo file_1 57 2 57 39.
  Definition loc_185 : location_info := LocationInfo file_1 58 2 58 41.
  Definition loc_186 : location_info := LocationInfo file_1 59 2 59 41.
  Definition loc_187 : location_info := LocationInfo file_1 60 2 60 37.
  Definition loc_188 : location_info := LocationInfo file_1 61 2 61 33.
  Definition loc_189 : location_info := LocationInfo file_1 62 2 62 38.
  Definition loc_190 : location_info := LocationInfo file_1 65 2 65 21.
  Definition loc_191 : location_info := LocationInfo file_1 66 2 66 19.
  Definition loc_192 : location_info := LocationInfo file_1 66 9 66 17.
  Definition loc_193 : location_info := LocationInfo file_1 66 9 66 11.
  Definition loc_194 : location_info := LocationInfo file_1 66 10 66 11.
  Definition loc_195 : location_info := LocationInfo file_1 66 15 66 17.
  Definition loc_196 : location_info := LocationInfo file_1 66 16 66 17.
  Definition loc_197 : location_info := LocationInfo file_1 65 9 65 19.
  Definition loc_198 : location_info := LocationInfo file_1 65 9 65 14.
  Definition loc_199 : location_info := LocationInfo file_1 65 10 65 14.
  Definition loc_200 : location_info := LocationInfo file_1 65 12 65 13.
  Definition loc_201 : location_info := LocationInfo file_1 65 18 65 19.
  Definition loc_202 : location_info := LocationInfo file_1 62 9 62 36.
  Definition loc_203 : location_info := LocationInfo file_1 62 9 62 22.
  Definition loc_204 : location_info := LocationInfo file_1 62 9 62 22.
  Definition loc_205 : location_info := LocationInfo file_1 62 26 62 36.
  Definition loc_206 : location_info := LocationInfo file_1 61 9 61 31.
  Definition loc_207 : location_info := LocationInfo file_1 61 9 61 23.
  Definition loc_208 : location_info := LocationInfo file_1 61 9 61 23.
  Definition loc_209 : location_info := LocationInfo file_1 61 27 61 31.
  Definition loc_210 : location_info := LocationInfo file_1 60 9 60 35.
  Definition loc_211 : location_info := LocationInfo file_1 60 9 60 21.
  Definition loc_212 : location_info := LocationInfo file_1 60 9 60 21.
  Definition loc_213 : location_info := LocationInfo file_1 60 25 60 35.
  Definition loc_214 : location_info := LocationInfo file_1 59 31 59 40.
  Definition loc_215 : location_info := LocationInfo file_1 59 31 59 32.
  Definition loc_216 : location_info := LocationInfo file_1 59 31 59 32.
  Definition loc_217 : location_info := LocationInfo file_1 59 35 59 40.
  Definition loc_218 : location_info := LocationInfo file_1 59 36 59 40.
  Definition loc_219 : location_info := LocationInfo file_1 59 36 59 40.
  Definition loc_222 : location_info := LocationInfo file_1 58 32 58 40.
  Definition loc_223 : location_info := LocationInfo file_1 58 32 58 33.
  Definition loc_224 : location_info := LocationInfo file_1 58 32 58 33.
  Definition loc_225 : location_info := LocationInfo file_1 58 36 58 40.
  Definition loc_226 : location_info := LocationInfo file_1 58 36 58 40.
  Definition loc_229 : location_info := LocationInfo file_1 57 30 57 38.
  Definition loc_230 : location_info := LocationInfo file_1 57 30 57 31.
  Definition loc_231 : location_info := LocationInfo file_1 57 30 57 31.
  Definition loc_232 : location_info := LocationInfo file_1 57 34 57 38.
  Definition loc_233 : location_info := LocationInfo file_1 57 34 57 38.
  Definition loc_236 : location_info := LocationInfo file_1 56 19 56 29.
  Definition loc_239 : location_info := LocationInfo file_1 55 22 55 28.
  Definition loc_244 : location_info := LocationInfo file_1 71 2 71 31.
  Definition loc_245 : location_info := LocationInfo file_1 73 2 73 22.
  Definition loc_246 : location_info := LocationInfo file_1 73 9 73 21.
  Definition loc_247 : location_info := LocationInfo file_1 73 9 73 14.
  Definition loc_248 : location_info := LocationInfo file_1 73 9 73 10.
  Definition loc_249 : location_info := LocationInfo file_1 73 9 73 10.
  Definition loc_250 : location_info := LocationInfo file_1 73 13 73 14.
  Definition loc_251 : location_info := LocationInfo file_1 73 13 73 14.
  Definition loc_252 : location_info := LocationInfo file_1 73 16 73 21.
  Definition loc_253 : location_info := LocationInfo file_1 73 16 73 17.
  Definition loc_254 : location_info := LocationInfo file_1 73 16 73 17.
  Definition loc_255 : location_info := LocationInfo file_1 73 20 73 21.
  Definition loc_256 : location_info := LocationInfo file_1 73 20 73 21.
  Definition loc_257 : location_info := LocationInfo file_1 71 10 71 30.
  Definition loc_258 : location_info := LocationInfo file_1 71 11 71 25.
  Definition loc_259 : location_info := LocationInfo file_1 71 27 71 29.
  Definition loc_264 : location_info := LocationInfo file_1 81 2 81 16.
  Definition loc_265 : location_info := LocationInfo file_1 81 9 81 15.
  Definition loc_266 : location_info := LocationInfo file_1 81 9 81 15.
  Definition loc_269 : location_info := LocationInfo file_1 87 2 87 26.
  Definition loc_270 : location_info := LocationInfo file_1 87 9 87 25.
  Definition loc_271 : location_info := LocationInfo file_1 87 9 87 23.
  Definition loc_272 : location_info := LocationInfo file_1 87 9 87 23.
  Definition loc_275 : location_info := LocationInfo file_1 92 2 96 3.
  Definition loc_276 : location_info := LocationInfo file_1 97 2 97 41.
  Definition loc_277 : location_info := LocationInfo file_1 98 2 98 58.
  Definition loc_278 : location_info := LocationInfo file_1 99 2 99 29.
  Definition loc_279 : location_info := LocationInfo file_1 99 9 99 27.
  Definition loc_280 : location_info := LocationInfo file_1 98 24 98 38.
  Definition loc_281 : location_info := LocationInfo file_1 98 26 98 36.
  Definition loc_282 : location_info := LocationInfo file_1 98 33 98 34.
  Definition loc_283 : location_info := LocationInfo file_1 98 44 98 58.
  Definition loc_284 : location_info := LocationInfo file_1 98 46 98 56.
  Definition loc_285 : location_info := LocationInfo file_1 98 53 98 54.
  Definition loc_286 : location_info := LocationInfo file_1 98 5 98 22.
  Definition loc_287 : location_info := LocationInfo file_1 97 9 97 39.
  Definition loc_288 : location_info := LocationInfo file_1 97 9 97 22.
  Definition loc_289 : location_info := LocationInfo file_1 97 9 97 17.
  Definition loc_290 : location_info := LocationInfo file_1 97 10 97 11.
  Definition loc_291 : location_info := LocationInfo file_1 97 15 97 16.
  Definition loc_292 : location_info := LocationInfo file_1 97 21 97 22.
  Definition loc_293 : location_info := LocationInfo file_1 97 26 97 39.
  Definition loc_294 : location_info := LocationInfo file_1 97 26 97 34.
  Definition loc_295 : location_info := LocationInfo file_1 97 27 97 28.
  Definition loc_296 : location_info := LocationInfo file_1 97 32 97 33.
  Definition loc_297 : location_info := LocationInfo file_1 97 38 97 39.
  Definition loc_298 : location_info := LocationInfo file_1 92 23 94 3.
  Definition loc_299 : location_info := LocationInfo file_1 93 4 93 14.
  Definition loc_300 : location_info := LocationInfo file_1 93 11 93 12.
  Definition loc_301 : location_info := LocationInfo file_1 94 9 96 3.
  Definition loc_302 : location_info := LocationInfo file_1 95 4 95 14.
  Definition loc_303 : location_info := LocationInfo file_1 95 11 95 12.
  Definition loc_304 : location_info := LocationInfo file_1 92 6 92 21.
  Definition loc_305 : location_info := LocationInfo file_1 92 6 92 14.
  Definition loc_306 : location_info := LocationInfo file_1 92 7 92 8.
  Definition loc_307 : location_info := LocationInfo file_1 92 12 92 13.
  Definition loc_308 : location_info := LocationInfo file_1 92 18 92 21.
  Definition loc_309 : location_info := LocationInfo file_1 92 18 92 19.
  Definition loc_310 : location_info := LocationInfo file_1 92 20 92 21.
  Definition loc_313 : location_info := LocationInfo file_1 104 2 104 8.
  Definition loc_314 : location_info := LocationInfo file_1 105 2 105 15.
  Definition loc_315 : location_info := LocationInfo file_1 107 2 109 3.
  Definition loc_316 : location_info := LocationInfo file_1 111 2 115 3.
  Definition loc_317 : location_info := LocationInfo file_1 117 2 117 13.
  Definition loc_318 : location_info := LocationInfo file_1 119 2 119 27.
  Definition loc_319 : location_info := LocationInfo file_1 120 2 122 3.
  Definition loc_320 : location_info := LocationInfo file_1 124 2 128 3.
  Definition loc_321 : location_info := LocationInfo file_1 130 2 130 13.
  Definition loc_322 : location_info := LocationInfo file_1 130 9 130 11.
  Definition loc_324 : location_info := LocationInfo file_1 130 10 130 11.
  Definition loc_325 : location_info := LocationInfo file_1 130 10 130 11.
  Definition loc_326 : location_info := LocationInfo file_1 124 8 126 3.
  Definition loc_327 : location_info := LocationInfo file_1 125 4 125 14.
  Definition loc_328 : location_info := LocationInfo file_1 125 11 125 12.
  Definition loc_329 : location_info := LocationInfo file_1 126 9 128 3.
  Definition loc_330 : location_info := LocationInfo file_1 127 4 127 14.
  Definition loc_331 : location_info := LocationInfo file_1 127 11 127 12.
  Definition loc_332 : location_info := LocationInfo file_1 124 5 124 7.
  Definition loc_334 : location_info := LocationInfo file_1 124 6 124 7.
  Definition loc_335 : location_info := LocationInfo file_1 124 6 124 7.
  Definition loc_336 : location_info := LocationInfo file_1 120 7 122 3.
  Definition loc_337 : location_info := LocationInfo file_1 121 4 121 14.
  Definition loc_338 : location_info := LocationInfo file_1 121 11 121 12.
  Definition loc_339 : location_info := LocationInfo file_1 120 2 122 3.
  Definition loc_340 : location_info := LocationInfo file_1 120 5 120 6.
  Definition loc_341 : location_info := LocationInfo file_1 120 5 120 6.
  Definition loc_342 : location_info := LocationInfo file_1 119 12 119 26.
  Definition loc_345 : location_info := LocationInfo file_1 117 9 117 11.
  Definition loc_346 : location_info := LocationInfo file_1 117 9 117 11.
  Definition loc_347 : location_info := LocationInfo file_1 111 8 113 3.
  Definition loc_348 : location_info := LocationInfo file_1 112 4 112 14.
  Definition loc_349 : location_info := LocationInfo file_1 112 11 112 12.
  Definition loc_350 : location_info := LocationInfo file_1 113 9 115 3.
  Definition loc_351 : location_info := LocationInfo file_1 114 4 114 14.
  Definition loc_352 : location_info := LocationInfo file_1 114 11 114 12.
  Definition loc_353 : location_info := LocationInfo file_1 111 5 111 7.
  Definition loc_354 : location_info := LocationInfo file_1 111 5 111 7.
  Definition loc_355 : location_info := LocationInfo file_1 107 9 109 3.
  Definition loc_356 : location_info := LocationInfo file_1 108 4 108 14.
  Definition loc_357 : location_info := LocationInfo file_1 108 11 108 12.
  Definition loc_358 : location_info := LocationInfo file_1 107 2 109 3.
  Definition loc_359 : location_info := LocationInfo file_1 107 5 107 8.
  Definition loc_361 : location_info := LocationInfo file_1 107 6 107 8.
  Definition loc_362 : location_info := LocationInfo file_1 107 6 107 8.
  Definition loc_363 : location_info := LocationInfo file_1 105 12 105 14.
  Definition loc_364 : location_info := LocationInfo file_1 105 13 105 14.
  Definition loc_371 : location_info := LocationInfo file_1 144 2 144 19.
  Definition loc_372 : location_info := LocationInfo file_1 145 2 145 13.
  Definition loc_373 : location_info := LocationInfo file_1 146 2 146 14.
  Definition loc_374 : location_info := LocationInfo file_1 146 9 146 13.
  Definition loc_375 : location_info := LocationInfo file_1 146 9 146 13.
  Definition loc_376 : location_info := LocationInfo file_1 145 2 145 8.
  Definition loc_377 : location_info := LocationInfo file_1 145 2 145 6.
  Definition loc_378 : location_info := LocationInfo file_1 145 11 145 12.
  Definition loc_381 : location_info := LocationInfo file_1 155 4 155 13.
  Definition loc_382 : location_info := LocationInfo file_1 155 11 155 12.
  Definition loc_383 : location_info := LocationInfo file_1 155 11 155 12.
  Definition loc_386 : location_info := LocationInfo file_1 169 2 169 13.
  Definition loc_387 : location_info := LocationInfo file_1 169 9 169 12.
  Definition loc_388 : location_info := LocationInfo file_1 169 9 169 12.
  Definition loc_389 : location_info := LocationInfo file_1 169 9 169 10.
  Definition loc_392 : location_info := LocationInfo file_1 174 2 174 88.
  Definition loc_393 : location_info := LocationInfo file_1 174 9 174 87.
  Definition loc_394 : location_info := LocationInfo file_1 174 66 174 86.
  Definition loc_395 : location_info := LocationInfo file_1 174 67 174 78.
  Definition loc_396 : location_info := LocationInfo file_1 174 68 174 69.
  Definition loc_397 : location_info := LocationInfo file_1 174 72 174 77.
  Definition loc_398 : location_info := LocationInfo file_1 174 81 174 85.
  Definition loc_401 : location_info := LocationInfo file_1 180 2 180 66.
  Definition loc_402 : location_info := LocationInfo file_1 181 2 181 12.
  Definition loc_403 : location_info := LocationInfo file_1 181 9 181 11.
  Definition loc_404 : location_info := LocationInfo file_1 181 9 181 11.
  Definition loc_405 : location_info := LocationInfo file_1 180 22 180 65.
  Definition loc_406 : location_info := LocationInfo file_1 180 22 180 23.
  Definition loc_407 : location_info := LocationInfo file_1 180 26 180 44.
  Definition loc_408 : location_info := LocationInfo file_1 180 43 180 44.
  Definition loc_409 : location_info := LocationInfo file_1 180 47 180 65.
  Definition loc_410 : location_info := LocationInfo file_1 180 64 180 65.
  Definition loc_415 : location_info := LocationInfo file_1 190 2 192 17.
  Definition loc_416 : location_info := LocationInfo file_1 192 17 192 3.
  Definition loc_417 : location_info := LocationInfo file_1 195 2 198 17.
  Definition loc_418 : location_info := LocationInfo file_1 198 17 198 3.
  Definition loc_419 : location_info := LocationInfo file_1 199 2 199 11.
  Definition loc_420 : location_info := LocationInfo file_1 199 9 199 10.
  Definition loc_421 : location_info := LocationInfo file_1 199 9 199 10.
  Definition loc_422 : location_info := LocationInfo file_1 198 15 198 16.
  Definition loc_423 : location_info := LocationInfo file_1 192 15 192 16.
  Definition loc_428 : location_info := LocationInfo file_1 208 2 208 12.
  Definition loc_429 : location_info := LocationInfo file_1 210 2 211 17.
  Definition loc_430 : location_info := LocationInfo file_1 211 17 211 3.
  Definition loc_431 : location_info := LocationInfo file_1 212 2 212 28.
  Definition loc_432 : location_info := LocationInfo file_1 214 2 217 17.
  Definition loc_433 : location_info := LocationInfo file_1 217 17 217 3.
  Definition loc_434 : location_info := LocationInfo file_1 218 2 218 28.
  Definition loc_435 : location_info := LocationInfo file_1 218 2 218 23.
  Definition loc_436 : location_info := LocationInfo file_1 218 2 218 23.
  Definition loc_437 : location_info := LocationInfo file_1 218 24 218 26.
  Definition loc_438 : location_info := LocationInfo file_1 217 15 217 16.
  Definition loc_439 : location_info := LocationInfo file_1 212 2 212 23.
  Definition loc_440 : location_info := LocationInfo file_1 212 2 212 23.
  Definition loc_441 : location_info := LocationInfo file_1 212 24 212 26.
  Definition loc_442 : location_info := LocationInfo file_1 211 15 211 16.
  Definition loc_443 : location_info := LocationInfo file_1 208 10 208 11.
  Definition loc_448 : location_info := LocationInfo file_1 228 2 228 13.
  Definition loc_449 : location_info := LocationInfo file_1 228 14 228 25.
  Definition loc_450 : location_info := LocationInfo file_1 229 2 229 14.
  Definition loc_451 : location_info := LocationInfo file_1 229 2 229 3.
  Definition loc_452 : location_info := LocationInfo file_1 229 2 229 3.
  Definition loc_453 : location_info := LocationInfo file_1 229 2 229 3.
  Definition loc_454 : location_info := LocationInfo file_1 229 4 229 7.
  Definition loc_455 : location_info := LocationInfo file_1 229 5 229 7.
  Definition loc_456 : location_info := LocationInfo file_1 229 9 229 12.
  Definition loc_457 : location_info := LocationInfo file_1 229 10 229 12.
  Definition loc_458 : location_info := LocationInfo file_1 228 23 228 24.
  Definition loc_461 : location_info := LocationInfo file_1 228 11 228 12.
  Definition loc_466 : location_info := LocationInfo file_1 236 2 236 9.
  Definition loc_467 : location_info := LocationInfo file_1 237 2 237 11.
  Definition loc_468 : location_info := LocationInfo file_1 237 9 237 10.
  Definition loc_469 : location_info := LocationInfo file_1 237 9 237 10.
  Definition loc_470 : location_info := LocationInfo file_1 236 2 236 4.
  Definition loc_471 : location_info := LocationInfo file_1 236 3 236 4.
  Definition loc_472 : location_info := LocationInfo file_1 236 3 236 4.
  Definition loc_473 : location_info := LocationInfo file_1 236 7 236 8.
  Definition loc_476 : location_info := LocationInfo file_1 242 2 242 19.
  Definition loc_477 : location_info := LocationInfo file_1 242 2 242 10.
  Definition loc_478 : location_info := LocationInfo file_1 242 2 242 10.
  Definition loc_479 : location_info := LocationInfo file_1 242 11 242 17.
  Definition loc_482 : location_info := LocationInfo file_1 254 2 319 3.
  Definition loc_483 : location_info := LocationInfo file_1 254 13 319 3.
  Definition loc_484 : location_info := LocationInfo file_1 254 14 258 36.
  Definition loc_486 : location_info := LocationInfo file_1 258 4 258 36.
  Definition loc_487 : location_info := LocationInfo file_1 258 36 258 5.
  Definition loc_488 : location_info := LocationInfo file_1 258 5 263 13.
  Definition loc_490 : location_info := LocationInfo file_1 263 4 263 13.
  Definition loc_491 : location_info := LocationInfo file_1 264 4 264 36.
  Definition loc_492 : location_info := LocationInfo file_1 264 36 264 5.
  Definition loc_493 : location_info := LocationInfo file_1 264 5 268 13.
  Definition loc_495 : location_info := LocationInfo file_1 268 4 268 13.
  Definition loc_496 : location_info := LocationInfo file_1 269 4 269 36.
  Definition loc_497 : location_info := LocationInfo file_1 269 36 269 5.
  Definition loc_498 : location_info := LocationInfo file_1 269 5 275 18.
  Definition loc_500 : location_info := LocationInfo file_1 275 4 275 18.
  Definition loc_501 : location_info := LocationInfo file_1 276 4 276 36.
  Definition loc_502 : location_info := LocationInfo file_1 276 36 276 5.
  Definition loc_503 : location_info := LocationInfo file_1 276 5 280 18.
  Definition loc_505 : location_info := LocationInfo file_1 280 4 280 18.
  Definition loc_506 : location_info := LocationInfo file_1 281 4 281 36.
  Definition loc_507 : location_info := LocationInfo file_1 281 36 281 5.
  Definition loc_508 : location_info := LocationInfo file_1 281 5 288 32.
  Definition loc_510 : location_info := LocationInfo file_1 288 4 288 32.
  Definition loc_511 : location_info := LocationInfo file_1 289 4 289 36.
  Definition loc_512 : location_info := LocationInfo file_1 289 36 289 5.
  Definition loc_513 : location_info := LocationInfo file_1 289 5 296 32.
  Definition loc_515 : location_info := LocationInfo file_1 296 4 296 32.
  Definition loc_516 : location_info := LocationInfo file_1 297 4 297 36.
  Definition loc_517 : location_info := LocationInfo file_1 297 36 297 5.
  Definition loc_518 : location_info := LocationInfo file_1 297 5 304 32.
  Definition loc_520 : location_info := LocationInfo file_1 304 4 304 32.
  Definition loc_521 : location_info := LocationInfo file_1 305 4 305 36.
  Definition loc_522 : location_info := LocationInfo file_1 305 36 305 5.
  Definition loc_523 : location_info := LocationInfo file_1 305 5 312 32.
  Definition loc_525 : location_info := LocationInfo file_1 312 4 312 32.
  Definition loc_526 : location_info := LocationInfo file_1 313 4 313 36.
  Definition loc_527 : location_info := LocationInfo file_1 313 36 313 5.
  Definition loc_528 : location_info := LocationInfo file_1 313 5 318 36.
  Definition loc_530 : location_info := LocationInfo file_1 318 4 318 36.
  Definition loc_531 : location_info := LocationInfo file_1 318 36 318 5.
  Definition loc_532 : location_info := LocationInfo file_1 318 31 318 35.
  Definition loc_533 : location_info := LocationInfo file_1 318 32 318 35.
  Definition loc_534 : location_info := LocationInfo file_1 313 31 313 35.
  Definition loc_535 : location_info := LocationInfo file_1 313 32 313 35.
  Definition loc_536 : location_info := LocationInfo file_1 312 30 312 32.
  Definition loc_537 : location_info := LocationInfo file_1 312 4 312 32.
  Definition loc_538 : location_info := LocationInfo file_1 312 8 312 28.
  Definition loc_539 : location_info := LocationInfo file_1 312 8 312 10.
  Definition loc_540 : location_info := LocationInfo file_1 312 8 312 10.
  Definition loc_541 : location_info := LocationInfo file_1 312 14 312 28.
  Definition loc_542 : location_info := LocationInfo file_1 305 31 305 35.
  Definition loc_543 : location_info := LocationInfo file_1 305 32 305 35.
  Definition loc_544 : location_info := LocationInfo file_1 304 30 304 32.
  Definition loc_545 : location_info := LocationInfo file_1 304 4 304 32.
  Definition loc_546 : location_info := LocationInfo file_1 304 8 304 28.
  Definition loc_547 : location_info := LocationInfo file_1 304 8 304 10.
  Definition loc_548 : location_info := LocationInfo file_1 304 8 304 10.
  Definition loc_549 : location_info := LocationInfo file_1 304 14 304 28.
  Definition loc_550 : location_info := LocationInfo file_1 297 31 297 35.
  Definition loc_551 : location_info := LocationInfo file_1 297 32 297 35.
  Definition loc_552 : location_info := LocationInfo file_1 296 30 296 32.
  Definition loc_553 : location_info := LocationInfo file_1 296 4 296 32.
  Definition loc_554 : location_info := LocationInfo file_1 296 8 296 28.
  Definition loc_555 : location_info := LocationInfo file_1 296 8 296 10.
  Definition loc_556 : location_info := LocationInfo file_1 296 8 296 10.
  Definition loc_557 : location_info := LocationInfo file_1 296 14 296 28.
  Definition loc_558 : location_info := LocationInfo file_1 289 31 289 35.
  Definition loc_559 : location_info := LocationInfo file_1 289 32 289 35.
  Definition loc_560 : location_info := LocationInfo file_1 288 30 288 32.
  Definition loc_561 : location_info := LocationInfo file_1 288 4 288 32.
  Definition loc_562 : location_info := LocationInfo file_1 288 8 288 28.
  Definition loc_563 : location_info := LocationInfo file_1 288 8 288 10.
  Definition loc_564 : location_info := LocationInfo file_1 288 8 288 10.
  Definition loc_565 : location_info := LocationInfo file_1 288 14 288 28.
  Definition loc_566 : location_info := LocationInfo file_1 281 31 281 35.
  Definition loc_567 : location_info := LocationInfo file_1 281 32 281 35.
  Definition loc_568 : location_info := LocationInfo file_1 280 16 280 18.
  Definition loc_569 : location_info := LocationInfo file_1 280 4 280 18.
  Definition loc_570 : location_info := LocationInfo file_1 280 8 280 14.
  Definition loc_571 : location_info := LocationInfo file_1 280 8 280 9.
  Definition loc_572 : location_info := LocationInfo file_1 280 8 280 9.
  Definition loc_573 : location_info := LocationInfo file_1 280 13 280 14.
  Definition loc_574 : location_info := LocationInfo file_1 276 31 276 35.
  Definition loc_575 : location_info := LocationInfo file_1 276 32 276 35.
  Definition loc_576 : location_info := LocationInfo file_1 275 16 275 18.
  Definition loc_577 : location_info := LocationInfo file_1 275 4 275 18.
  Definition loc_578 : location_info := LocationInfo file_1 275 8 275 14.
  Definition loc_579 : location_info := LocationInfo file_1 275 8 275 9.
  Definition loc_580 : location_info := LocationInfo file_1 275 13 275 14.
  Definition loc_581 : location_info := LocationInfo file_1 269 31 269 35.
  Definition loc_582 : location_info := LocationInfo file_1 269 32 269 35.
  Definition loc_583 : location_info := LocationInfo file_1 268 11 268 13.
  Definition loc_584 : location_info := LocationInfo file_1 268 4 268 13.
  Definition loc_585 : location_info := LocationInfo file_1 268 8 268 9.
  Definition loc_586 : location_info := LocationInfo file_1 268 8 268 9.
  Definition loc_587 : location_info := LocationInfo file_1 264 31 264 35.
  Definition loc_588 : location_info := LocationInfo file_1 264 32 264 35.
  Definition loc_589 : location_info := LocationInfo file_1 263 11 263 13.
  Definition loc_590 : location_info := LocationInfo file_1 263 4 263 13.
  Definition loc_591 : location_info := LocationInfo file_1 263 8 263 9.
  Definition loc_592 : location_info := LocationInfo file_1 258 31 258 35.
  Definition loc_593 : location_info := LocationInfo file_1 258 32 258 35.
  Definition loc_594 : location_info := LocationInfo file_1 254 10 254 11.
  Definition loc_595 : location_info := LocationInfo file_1 254 10 254 11.

  (* Definition of struct [__cerbty_unnamed_tag_486]. *)
  Program Definition struct___cerbty_unnamed_tag_486 := {|
    sl_members := [
      (Some "__dummy_max_align_t", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [test]. *)
  Program Definition struct_test := {|
    sl_members := [
      (Some "a", it_layout i32)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [test2]. *)
  Program Definition struct_test2 := {|
    sl_members := [
      (Some "a", it_layout i32);
      (None, Layout 4%nat 0%nat);
      (Some "next", void*)
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

  (* Definition of function [test1]. *)
  Definition impl_test1 : function := {|
    f_args := [
    ];
    f_local_vars := [
      ("i", it_layout i32);
      ("c", it_layout u8);
      ("s", it_layout i16);
      ("ll", it_layout i64);
      ("l", it_layout i64)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "ll" <-{ IntOp i64 }
          LocInfoE loc_122 (UnOp (CastOp $ IntOp i64) (IntOp i32) (LocInfoE loc_122 (i2v 0 i32))) ;
        "l" <-{ IntOp i64 }
          LocInfoE loc_119 (UnOp (CastOp $ IntOp i64) (IntOp i32) (LocInfoE loc_119 (i2v 0 i32))) ;
        "i" <-{ IntOp i32 } LocInfoE loc_116 (i2v 0 i32) ;
        "s" <-{ IntOp i16 }
          LocInfoE loc_113 (UnOp (CastOp $ IntOp i16) (IntOp i32) (LocInfoE loc_113 (i2v 0 i32))) ;
        "c" <-{ IntOp u8 }
          LocInfoE loc_110 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_110 (i2v 0 i32))) ;
        locinfo: loc_105 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_105 ((LocInfoE loc_106 (use{IntOp i64} (LocInfoE loc_107 ("ll")))) ={IntOp i64, IntOp i64, i32} (LocInfoE loc_108 (use{IntOp i64} (LocInfoE loc_109 ("l")))))
        then
        locinfo: loc_102 ;
          Goto "#29"
        else
        locinfo: loc_97 ;
          Goto "#30"
      ]> $
      <[ "#1" :=
        locinfo: loc_97 ;
        if{IntOp i32, Some "#2"}: LocInfoE loc_97 ((LocInfoE loc_98 (use{IntOp i64} (LocInfoE loc_99 ("ll")))) ={IntOp i64, IntOp i64, i32} (LocInfoE loc_100 (use{IntOp i64} (LocInfoE loc_101 ("l")))))
        then
        locinfo: loc_94 ;
          Goto "#27"
        else
        locinfo: loc_89 ;
          Goto "#28"
      ]> $
      <[ "#10" :=
        locinfo: loc_33 ;
        Return (VOID)
      ]> $
      <[ "#11" :=
        locinfo: loc_35 ;
        Return (VOID)
      ]> $
      <[ "#12" :=
        locinfo: loc_33 ;
        Goto "#10"
      ]> $
      <[ "#13" :=
        locinfo: loc_42 ;
        Return (VOID)
      ]> $
      <[ "#14" :=
        locinfo: loc_38 ;
        Goto "#9"
      ]> $
      <[ "#15" :=
        locinfo: loc_49 ;
        Return (VOID)
      ]> $
      <[ "#16" :=
        locinfo: loc_45 ;
        Goto "#8"
      ]> $
      <[ "#17" :=
        locinfo: loc_56 ;
        Return (VOID)
      ]> $
      <[ "#18" :=
        locinfo: loc_52 ;
        Goto "#7"
      ]> $
      <[ "#19" :=
        locinfo: loc_63 ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_89 ;
        if{IntOp i32, Some "#3"}: LocInfoE loc_89 ((LocInfoE loc_90 (use{IntOp i64} (LocInfoE loc_91 ("ll")))) ={IntOp i64, IntOp i64, i32} (LocInfoE loc_92 (UnOp (CastOp $ IntOp i64) (IntOp i32) (LocInfoE loc_92 (use{IntOp i32} (LocInfoE loc_93 ("i")))))))
        then
        locinfo: loc_86 ;
          Goto "#25"
        else
        locinfo: loc_81 ;
          Goto "#26"
      ]> $
      <[ "#20" :=
        locinfo: loc_59 ;
        Goto "#6"
      ]> $
      <[ "#21" :=
        locinfo: loc_70 ;
        Return (VOID)
      ]> $
      <[ "#22" :=
        locinfo: loc_66 ;
        Goto "#5"
      ]> $
      <[ "#23" :=
        locinfo: loc_78 ;
        Return (VOID)
      ]> $
      <[ "#24" :=
        locinfo: loc_73 ;
        Goto "#4"
      ]> $
      <[ "#25" :=
        locinfo: loc_86 ;
        Return (VOID)
      ]> $
      <[ "#26" :=
        locinfo: loc_81 ;
        Goto "#3"
      ]> $
      <[ "#27" :=
        locinfo: loc_94 ;
        Return (VOID)
      ]> $
      <[ "#28" :=
        locinfo: loc_89 ;
        Goto "#2"
      ]> $
      <[ "#29" :=
        locinfo: loc_102 ;
        Return (VOID)
      ]> $
      <[ "#3" :=
        locinfo: loc_81 ;
        if{IntOp i32, Some "#4"}: LocInfoE loc_81 ((LocInfoE loc_82 (use{IntOp i64} (LocInfoE loc_83 ("ll")))) ={IntOp i64, IntOp i64, i32} (LocInfoE loc_84 (UnOp (CastOp $ IntOp i64) (IntOp i16) (LocInfoE loc_84 (use{IntOp i16} (LocInfoE loc_85 ("s")))))))
        then
        locinfo: loc_78 ;
          Goto "#23"
        else
        locinfo: loc_73 ;
          Goto "#24"
      ]> $
      <[ "#30" :=
        locinfo: loc_97 ;
        Goto "#1"
      ]> $
      <[ "#4" :=
        locinfo: loc_73 ;
        if{IntOp i32, Some "#5"}: LocInfoE loc_73 ((LocInfoE loc_74 (use{IntOp i64} (LocInfoE loc_75 ("ll")))) ={IntOp i64, IntOp i64, i32} (LocInfoE loc_76 (UnOp (CastOp $ IntOp i64) (IntOp u8) (LocInfoE loc_76 (use{IntOp u8} (LocInfoE loc_77 ("c")))))))
        then
        locinfo: loc_70 ;
          Goto "#21"
        else
        locinfo: loc_66 ;
          Goto "#22"
      ]> $
      <[ "#5" :=
        locinfo: loc_66 ;
        if{IntOp i32, Some "#6"}: LocInfoE loc_66 ((UnOp (CastOp $ IntOp i64) (IntOp i32) (i2v 0 i32)) ={IntOp i64, IntOp i64, i32} (LocInfoE loc_68 (use{IntOp i64} (LocInfoE loc_69 ("ll")))))
        then
        locinfo: loc_63 ;
          Goto "#19"
        else
        locinfo: loc_59 ;
          Goto "#20"
      ]> $
      <[ "#6" :=
        locinfo: loc_59 ;
        if{IntOp i32, Some "#7"}: LocInfoE loc_59 ((UnOp (CastOp $ IntOp i64) (IntOp i32) (i2v 0 i32)) ={IntOp i64, IntOp i64, i32} (LocInfoE loc_61 (use{IntOp i64} (LocInfoE loc_62 ("l")))))
        then
        locinfo: loc_56 ;
          Goto "#17"
        else
        locinfo: loc_52 ;
          Goto "#18"
      ]> $
      <[ "#7" :=
        locinfo: loc_52 ;
        if{IntOp i32, Some "#8"}: LocInfoE loc_52 ((i2v 0 i32) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_54 (use{IntOp i32} (LocInfoE loc_55 ("i")))))
        then
        locinfo: loc_49 ;
          Goto "#15"
        else
        locinfo: loc_45 ;
          Goto "#16"
      ]> $
      <[ "#8" :=
        locinfo: loc_45 ;
        if{IntOp i32, Some "#9"}: LocInfoE loc_45 ((i2v 0 i32) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_47 (UnOp (CastOp $ IntOp i32) (IntOp i16) (LocInfoE loc_47 (use{IntOp i16} (LocInfoE loc_48 ("s")))))))
        then
        locinfo: loc_42 ;
          Goto "#13"
        else
        locinfo: loc_38 ;
          Goto "#14"
      ]> $
      <[ "#9" :=
        locinfo: loc_38 ;
        if{IntOp i32, Some "#10"}: LocInfoE loc_38 ((i2v 0 i32) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_40 (UnOp (CastOp $ IntOp i32) (IntOp u8) (LocInfoE loc_40 (use{IntOp u8} (LocInfoE loc_41 ("c")))))))
        then
        locinfo: loc_35 ;
          Goto "#11"
        else
        locinfo: loc_33 ;
          Goto "#12"
      ]> $∅
    )%E
  |}.

  (* Definition of function [return1]. *)
  Definition impl_return1 : function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_127 ;
        Return (LocInfoE loc_128 (i2v 1 i32))
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_ternary]. *)
  Definition impl_test_ternary (global_return1 global_unreachable : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
      ("local", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "local" <-{ IntOp i32 } LocInfoE loc_160 (i2v 0 i32) ;
        locinfo: loc_132 ;
        assert{IntOp i32}: (LocInfoE loc_154 ((LocInfoE loc_155 (IfE
        (IntOp i32)
        (LocInfoE loc_156 (i2v 2 i32))
        (LocInfoE loc_157 (i2v 3 i32))
        (LocInfoE loc_158 (i2v 2 i32)))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_159 (i2v 3 i32)))) ;
        locinfo: loc_133 ;
        assert{IntOp i32}: (LocInfoE loc_134 ((LocInfoE loc_135 (IfE
        (IntOp i32)
        (LocInfoE loc_136 ((LocInfoE loc_137 (&(LocInfoE loc_138 ("local")))) !={PtrOp, PtrOp, i32} (LocInfoE loc_139 (NULL))))
        (LocInfoE loc_140 ((LocInfoE loc_141 (IfE
        (IntOp i32)
        (LocInfoE loc_142 (Call (LocInfoE loc_144 (global_return1)) [@{expr}  ]))
        (LocInfoE loc_145 (Call (LocInfoE loc_147 (global_return1)) [@{expr}  ]))
        (LocInfoE loc_148 (Call (LocInfoE loc_150 (global_unreachable)) [@{expr}  ])))) +{IntOp i32, IntOp i32} (LocInfoE loc_151 (i2v 3 i32))))
        (LocInfoE loc_152 (i2v 2 i32)))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_153 (i2v 4 i32)))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_assume]. *)
  Definition impl_test_assume (global_safe_exit : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_165 ;
        expr: (LocInfoE loc_170 (IfE
        (IntOp i32)
        (LocInfoE loc_171 ((i2v 0 i32) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_173 (i2v 0 i32))))
        (LocInfoE loc_174 ((LocInfoE loc_175 (Call (LocInfoE loc_177 (global_safe_exit)) [@{expr}  ])) ,{IntOp i32, IntOp i32} (LocInfoE loc_178 (i2v 0 i32))))
        (LocInfoE loc_179 (i2v 0 i32)))) ;
        locinfo: loc_166 ;
        assert{IntOp i32}: (LocInfoE loc_167 ((LocInfoE loc_168 (i2v 1 i32)) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_169 (i2v 2 i32)))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_bits]. *)
  Definition impl_test_bits : function := {|
    f_args := [
    ];
    f_local_vars := [
      ("selecting_bits", it_layout u32);
      ("mask", it_layout u32);
      ("clearing_bits", it_layout u32);
      ("setting_bits", it_layout u32);
      ("a", it_layout u32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "mask" <-{ IntOp u32 }
          LocInfoE loc_239 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_239 (i2v 240 i32))) ;
        "a" <-{ IntOp u32 }
          LocInfoE loc_236 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_236 (i2v 305419896 i32))) ;
        "setting_bits" <-{ IntOp u32 }
          LocInfoE loc_229 ((LocInfoE loc_230 (use{IntOp u32} (LocInfoE loc_231 ("a")))) |{IntOp u32, IntOp u32} (LocInfoE loc_232 (use{IntOp u32} (LocInfoE loc_233 ("mask"))))) ;
        "selecting_bits" <-{ IntOp u32 }
          LocInfoE loc_222 ((LocInfoE loc_223 (use{IntOp u32} (LocInfoE loc_224 ("a")))) &{IntOp u32, IntOp u32} (LocInfoE loc_225 (use{IntOp u32} (LocInfoE loc_226 ("mask"))))) ;
        "clearing_bits" <-{ IntOp u32 }
          LocInfoE loc_214 ((LocInfoE loc_215 (use{IntOp u32} (LocInfoE loc_216 ("a")))) &{IntOp u32, IntOp u32} (LocInfoE loc_217 (UnOp NotIntOp (IntOp u32) (LocInfoE loc_218 (use{IntOp u32} (LocInfoE loc_219 ("mask"))))))) ;
        locinfo: loc_187 ;
        assert{IntOp i32}: (LocInfoE loc_210 ((LocInfoE loc_211 (use{IntOp u32} (LocInfoE loc_212 ("setting_bits")))) ={IntOp u32, IntOp u32, i32} (LocInfoE loc_213 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_213 (i2v 305420024 i32)))))) ;
        locinfo: loc_188 ;
        assert{IntOp i32}: (LocInfoE loc_206 ((LocInfoE loc_207 (use{IntOp u32} (LocInfoE loc_208 ("selecting_bits")))) ={IntOp u32, IntOp u32, i32} (LocInfoE loc_209 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_209 (i2v 112 i32)))))) ;
        locinfo: loc_189 ;
        assert{IntOp i32}: (LocInfoE loc_202 ((LocInfoE loc_203 (use{IntOp u32} (LocInfoE loc_204 ("clearing_bits")))) ={IntOp u32, IntOp u32, i32} (LocInfoE loc_205 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_205 (i2v 305419784 i32)))))) ;
        locinfo: loc_190 ;
        assert{IntOp i32}: (LocInfoE loc_197 ((LocInfoE loc_198 (UnOp NotIntOp (IntOp i32) (LocInfoE loc_199 (UnOp NegOp (IntOp i32) (LocInfoE loc_200 (i2v 2 i32)))))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_201 (i2v 1 i32)))) ;
        locinfo: loc_191 ;
        assert{IntOp i32}: (LocInfoE loc_192 ((LocInfoE loc_193 (UnOp NotIntOp (IntOp i32) (LocInfoE loc_194 (i2v 0 i32)))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_195 (UnOp NegOp (IntOp i32) (LocInfoE loc_196 (i2v 1 i32)))))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_comma]. *)
  Definition impl_test_comma : function := {|
    f_args := [
    ];
    f_local_vars := [
      ("x", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "x" <-{ IntOp i32 }
          LocInfoE loc_257 ((LocInfoE loc_258 (NULL)) ,{PtrOp, IntOp i32} (LocInfoE loc_259 (i2v 42 i32))) ;
        locinfo: loc_245 ;
        Return (LocInfoE loc_246 ((LocInfoE loc_247 ((LocInfoE loc_248 (use{IntOp i32} (LocInfoE loc_249 ("x")))) +{IntOp i32, IntOp i32} (LocInfoE loc_250 (use{IntOp i32} (LocInfoE loc_251 ("x")))))) ,{IntOp i32, IntOp i32} (LocInfoE loc_252 ((LocInfoE loc_253 (use{IntOp i32} (LocInfoE loc_254 ("x")))) -{IntOp i32, IntOp i32} (LocInfoE loc_255 (use{IntOp i32} (LocInfoE loc_256 ("x"))))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [inline_global1]. *)
  Definition impl_inline_global1 (global_global : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_264 ;
        Return (LocInfoE loc_265 (use{IntOp i32} (LocInfoE loc_266 (global_global))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [inline_global2]. *)
  Definition impl_inline_global2 (global_inline_global1 : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_269 ;
        Return (LocInfoE loc_270 (Call (LocInfoE loc_272 (global_inline_global1)) [@{expr}  ]))
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_logical]. *)
  Definition impl_test_logical : function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_304 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_304 ((LocInfoE loc_305 ((LocInfoE loc_306 (i2v 1 i32)) &&{IntOp i32, IntOp i32, i32} (LocInfoE loc_307 (i2v 2 i32)))) ||{IntOp i32, IntOp i32, i32} (LocInfoE loc_308 ((LocInfoE loc_309 (i2v 0 i32)) /{IntOp i32, IntOp i32} (LocInfoE loc_310 (i2v 0 i32)))))
        then
        locinfo: loc_299 ;
          Goto "#5"
        else
        locinfo: loc_302 ;
          Goto "#6"
      ]> $
      <[ "#1" :=
        locinfo: loc_276 ;
        assert{IntOp i32}: (LocInfoE loc_287 ((LocInfoE loc_288 ((LocInfoE loc_289 ((LocInfoE loc_290 (i2v 1 i32)) &&{IntOp i32, IntOp i32, i32} (LocInfoE loc_291 (i2v 2 i32)))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_292 (i2v 1 i32)))) &&{IntOp i32, IntOp i32, i32} (LocInfoE loc_293 ((LocInfoE loc_294 ((LocInfoE loc_295 (i2v 2 i32)) ||{IntOp i32, IntOp i32, i32} (LocInfoE loc_296 (i2v 0 i32)))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_297 (i2v 1 i32)))))) ;
        locinfo: loc_286 ;
        if{IntOp i32, Some "#2"}: LocInfoE loc_286 (i2v (max_int i32) i32)
        then
        locinfo: loc_281 ;
          Goto "#3"
        else
        locinfo: loc_284 ;
          Goto "#4"
      ]> $
      <[ "#2" :=
        locinfo: loc_278 ;
        assert{IntOp u32}: (LocInfoE loc_279 (i2v (max_int u32) u32)) ;
        Return (VOID)
      ]> $
      <[ "#3" :=
        locinfo: loc_281 ;
        assert{IntOp i32}: (LocInfoE loc_282 (i2v 1 i32)) ;
        locinfo: loc_278 ;
        Goto "#2"
      ]> $
      <[ "#4" :=
        locinfo: loc_284 ;
        assert{IntOp i32}: (LocInfoE loc_285 (i2v 0 i32)) ;
        locinfo: loc_278 ;
        Goto "#2"
      ]> $
      <[ "#5" :=
        locinfo: loc_299 ;
        assert{IntOp i32}: (LocInfoE loc_300 (i2v 1 i32)) ;
        locinfo: loc_276 ;
        Goto "#1"
      ]> $
      <[ "#6" :=
        locinfo: loc_302 ;
        assert{IntOp i32}: (LocInfoE loc_303 (i2v 0 i32)) ;
        locinfo: loc_276 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_not_ptr]. *)
  Definition impl_test_not_ptr : function := {|
    f_args := [
    ];
    f_local_vars := [
      ("i", it_layout i32);
      ("p", void*);
      ("pi", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "pi" <-{ PtrOp } LocInfoE loc_363 (&(LocInfoE loc_364 ("i"))) ;
        locinfo: loc_359 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_359 ((UnOp (CastOp $ PtrOp) (IntOp i32) (i2v 0 i32)) ={PtrOp, PtrOp, i32} (LocInfoE loc_361 (use{PtrOp} (LocInfoE loc_362 ("pi")))))
        then
        locinfo: loc_356 ;
          Goto "#11"
        else
        locinfo: loc_353 ;
          Goto "#12"
      ]> $
      <[ "#1" :=
        locinfo: loc_353 ;
        if{PtrOp, Some "#2"}: LocInfoE loc_353 (use{PtrOp} (LocInfoE loc_354 ("pi")))
        then
        locinfo: loc_348 ;
          Goto "#9"
        else
        locinfo: loc_351 ;
          Goto "#10"
      ]> $
      <[ "#10" :=
        locinfo: loc_351 ;
        assert{IntOp i32}: (LocInfoE loc_352 (i2v 0 i32)) ;
        locinfo: loc_317 ;
        Goto "#2"
      ]> $
      <[ "#11" :=
        locinfo: loc_356 ;
        assert{IntOp i32}: (LocInfoE loc_357 (i2v 0 i32)) ;
        locinfo: loc_353 ;
        Goto "#1"
      ]> $
      <[ "#12" :=
        locinfo: loc_353 ;
        Goto "#1"
      ]> $
      <[ "#2" :=
        locinfo: loc_317 ;
        assert{PtrOp}: (LocInfoE loc_345 (use{PtrOp} (LocInfoE loc_346 ("pi")))) ;
        "p" <-{ PtrOp } LocInfoE loc_342 (NULL) ;
        locinfo: loc_340 ;
        if{PtrOp, Some "#3"}: LocInfoE loc_340 (use{PtrOp} (LocInfoE loc_341 ("p")))
        then
        locinfo: loc_337 ;
          Goto "#7"
        else
        locinfo: loc_332 ;
          Goto "#8"
      ]> $
      <[ "#3" :=
        locinfo: loc_332 ;
        if{IntOp i32, Some "#4"}: LocInfoE loc_332 ((UnOp (CastOp $ PtrOp) (IntOp i32) (i2v 0 i32)) ={PtrOp, PtrOp, i32} (LocInfoE loc_334 (use{PtrOp} (LocInfoE loc_335 ("p")))))
        then
        locinfo: loc_327 ;
          Goto "#5"
        else
        locinfo: loc_330 ;
          Goto "#6"
      ]> $
      <[ "#4" :=
        locinfo: loc_321 ;
        assert{IntOp i32}: (LocInfoE loc_322 ((UnOp (CastOp $ PtrOp) (IntOp i32) (i2v 0 i32)) ={PtrOp, PtrOp, i32} (LocInfoE loc_324 (use{PtrOp} (LocInfoE loc_325 ("p")))))) ;
        Return (VOID)
      ]> $
      <[ "#5" :=
        locinfo: loc_327 ;
        assert{IntOp i32}: (LocInfoE loc_328 (i2v 1 i32)) ;
        locinfo: loc_321 ;
        Goto "#4"
      ]> $
      <[ "#6" :=
        locinfo: loc_330 ;
        assert{IntOp i32}: (LocInfoE loc_331 (i2v 0 i32)) ;
        locinfo: loc_321 ;
        Goto "#4"
      ]> $
      <[ "#7" :=
        locinfo: loc_337 ;
        assert{IntOp i32}: (LocInfoE loc_338 (i2v 0 i32)) ;
        locinfo: loc_332 ;
        Goto "#3"
      ]> $
      <[ "#8" :=
        locinfo: loc_332 ;
        Goto "#3"
      ]> $
      <[ "#9" :=
        locinfo: loc_348 ;
        assert{IntOp i32}: (LocInfoE loc_349 (i2v 1 i32)) ;
        locinfo: loc_317 ;
        Goto "#2"
      ]> $∅
    )%E
  |}.

  (* Definition of function [main]. *)
  Definition impl_main : function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        Return (i2v 0 i32)
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_struct_return]. *)
  Definition impl_test_struct_return : function := {|
    f_args := [
    ];
    f_local_vars := [
      ("test", layout_of struct_test)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_372 ;
        LocInfoE loc_376 ((LocInfoE loc_377 ("test")) at{struct_test} "a") <-{ IntOp i32 }
          LocInfoE loc_378 (i2v 1 i32) ;
        locinfo: loc_373 ;
        Return (LocInfoE loc_374 (use{StructOp struct_test ([ IntOp i32 ])} (LocInfoE loc_375 ("test"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_fn_params]. *)
  Definition impl_test_fn_params : function := {|
    f_args := [
      ("f", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_381 ;
        Return (LocInfoE loc_382 (use{PtrOp} (LocInfoE loc_383 ("f"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_struct2]. *)
  Definition impl_test_struct2 : function := {|
    f_args := [
      ("s", layout_of struct_test2)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_386 ;
        Return (LocInfoE loc_387 (use{IntOp i32} (LocInfoE loc_388 ((LocInfoE loc_389 ("s")) at{struct_test2} "a"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_reduce]. *)
  Definition impl_test_reduce : function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_392 ;
        Return (LocInfoE loc_393 (AnnotExpr 1%nat ReduceAnnot (LocInfoE loc_394 ((LocInfoE loc_395 ((LocInfoE loc_396 (i2v 1 i32)) |{IntOp i32, IntOp i32} (LocInfoE loc_397 (i2v 4080 i32)))) &{IntOp i32, IntOp i32} (LocInfoE loc_398 (i2v 255 i32))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_conditional_annot]. *)
  Definition impl_test_conditional_annot : function := {|
    f_args := [
    ];
    f_local_vars := [
      ("i2", it_layout u16)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i2" <-{ IntOp u16 }
          LocInfoE loc_405 (UnOp (CastOp $ IntOp u16) (IntOp i32) (LocInfoE loc_405 (IfE
          (IntOp i32) (LocInfoE loc_406 (i2v 0 i32))
          (LocInfoE loc_407 (UnOp (CastOp $ IntOp i32) (IntOp u16) (LocInfoE loc_407 (UnOp (CastOp $ IntOp u16) (IntOp i32) (LocInfoE loc_408 (i2v 0 i32))))))
          (LocInfoE loc_409 (UnOp (CastOp $ IntOp i32) (IntOp u16) (LocInfoE loc_409 (UnOp (CastOp $ IntOp u16) (IntOp i32) (LocInfoE loc_410 (i2v 0 i32))))))))) ;
        locinfo: loc_402 ;
        Return (LocInfoE loc_403 (UnOp (CastOp $ IntOp i32) (IntOp u16) (LocInfoE loc_403 (use{IntOp u16} (LocInfoE loc_404 ("i2"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_rc_assert]. *)
  Definition impl_test_rc_assert : function := {|
    f_args := [
      ("i", it_layout i32)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_415 ;
        annot: (AssertAnnot "1") ;
        expr: (LocInfoE loc_423 (i2v 0 i32)) ;
        locinfo: loc_417 ;
        annot: (AssertAnnot "0") ;
        expr: (LocInfoE loc_422 (i2v 0 i32)) ;
        locinfo: loc_419 ;
        Return (LocInfoE loc_420 (use{IntOp i32} (LocInfoE loc_421 ("i"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_manual_exist_arg]. *)
  Definition impl_test_manual_exist_arg : function := {|
    f_args := [
      ("i", it_layout i32)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_manual_exist_arg_client]. *)
  Definition impl_test_manual_exist_arg_client (global_test_manual_exist_arg : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
      ("x", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "x" <-{ IntOp i32 } LocInfoE loc_443 (i2v 8 i32) ;
        locinfo: loc_429 ;
        annot: (AssertAnnot "1") ;
        expr: (LocInfoE loc_442 (i2v 0 i32)) ;
        locinfo: loc_431 ;
        expr: (LocInfoE loc_431 (Call (LocInfoE loc_440 (global_test_manual_exist_arg)) [@{expr} LocInfoE loc_441 (i2v 20 i32) ])) ;
        locinfo: loc_432 ;
        annot: (AssertAnnot "0") ;
        expr: (LocInfoE loc_438 (i2v 0 i32)) ;
        locinfo: loc_434 ;
        expr: (LocInfoE loc_434 (Call (LocInfoE loc_436 (global_test_manual_exist_arg)) [@{expr} LocInfoE loc_437 (i2v 40 i32) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_hof]. *)
  Definition impl_test_hof : function := {|
    f_args := [
      ("f", void*)
    ];
    f_local_vars := [
      ("n1", it_layout i32);
      ("n2", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "n1" <-{ IntOp i32 } LocInfoE loc_461 (i2v 0 i32) ;
        "n2" <-{ IntOp i32 } LocInfoE loc_458 (i2v 0 i32) ;
        locinfo: loc_450 ;
        expr: (LocInfoE loc_450 (Call (LocInfoE loc_452 (use{PtrOp} (LocInfoE loc_453 ("f")))) [@{expr} LocInfoE loc_454 (&(LocInfoE loc_455 ("n1"))) ;
        LocInfoE loc_456 (&(LocInfoE loc_457 ("n2"))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_f]. *)
  Definition impl_test_f : function := {|
    f_args := [
      ("x", void*);
      ("y", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_466 ;
        LocInfoE loc_471 (!{PtrOp} (LocInfoE loc_472 ("x"))) <-{ IntOp i32 }
          LocInfoE loc_473 (i2v 1 i32) ;
        locinfo: loc_467 ;
        Return (LocInfoE loc_468 (use{PtrOp} (LocInfoE loc_469 ("x"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_hof_client]. *)
  Definition impl_test_hof_client (global_test_f global_test_hof : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_476 ;
        expr: (LocInfoE loc_476 (Call (LocInfoE loc_478 (global_test_hof)) [@{expr} LocInfoE loc_479 (global_test_f) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_case_printing]. *)
  Definition impl_test_case_printing : function := {|
    f_args := [
      ("n", it_layout i32);
      ("m", it_layout i32);
      ("p1", void*);
      ("p2", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_482 ;
        Switch i32
          (LocInfoE loc_594 (use{IntOp i32} (LocInfoE loc_595 ("n"))))
          (
            <[ 1 := 0%nat ]> $
            <[ 2 := 1%nat ]> $
            <[ 3 := 2%nat ]> $
            <[ 4 := 3%nat ]> $
            <[ 5 := 4%nat ]> $
            <[ 6 := 5%nat ]> $
            <[ 7 := 6%nat ]> $
            <[ 8 := 7%nat ]> $
            <[ 9 := 8%nat ]> ∅
          )
          (
            (locinfo: loc_484 ;
            Goto "#2") ::
            (locinfo: loc_488 ;
            Goto "#3") ::
            (locinfo: loc_493 ;
            Goto "#4") ::
            (locinfo: loc_498 ;
            Goto "#5") ::
            (locinfo: loc_503 ;
            Goto "#7") ::
            (locinfo: loc_508 ;
            Goto "#9") ::
            (locinfo: loc_513 ;
            Goto "#11") ::
            (locinfo: loc_518 ;
            Goto "#13") ::
            (locinfo: loc_523 ;
            Goto "#15") :: []
          )
          (locinfo: loc_528 ;
          Goto "#17")
      ]> $
      <[ "#1" :=
        Return (VOID)
      ]> $
      <[ "#10" :=
        locinfo: loc_501 ;
        annot: (StopAnnot) ;
        expr: (LocInfoE loc_574 (&(LocInfoE loc_575 ("n")))) ;
        locinfo: loc_503 ;
        Goto "#7"
      ]> $
      <[ "#11" :=
        locinfo: loc_554 ;
        if{IntOp i32, Some "#16"}: LocInfoE loc_554 ((LocInfoE loc_555 (use{PtrOp} (LocInfoE loc_556 ("p1")))) !={PtrOp, PtrOp, i32} (LocInfoE loc_557 (NULL)))
        then
        locinfo: loc_516 ;
          Goto "#26"
        else
        locinfo: loc_516 ;
          Goto "#27"
      ]> $
      <[ "#12" :=
        locinfo: loc_506 ;
        annot: (StopAnnot) ;
        expr: (LocInfoE loc_566 (&(LocInfoE loc_567 ("n")))) ;
        locinfo: loc_508 ;
        Goto "#9"
      ]> $
      <[ "#13" :=
        locinfo: loc_546 ;
        if{IntOp i32, Some "#18"}: LocInfoE loc_546 ((LocInfoE loc_547 (use{PtrOp} (LocInfoE loc_548 ("p2")))) ={PtrOp, PtrOp, i32} (LocInfoE loc_549 (NULL)))
        then
        locinfo: loc_521 ;
          Goto "#24"
        else
        locinfo: loc_521 ;
          Goto "#25"
      ]> $
      <[ "#14" :=
        locinfo: loc_511 ;
        annot: (StopAnnot) ;
        expr: (LocInfoE loc_558 (&(LocInfoE loc_559 ("n")))) ;
        locinfo: loc_513 ;
        Goto "#11"
      ]> $
      <[ "#15" :=
        locinfo: loc_538 ;
        if{IntOp i32, Some "#20"}: LocInfoE loc_538 ((LocInfoE loc_539 (use{PtrOp} (LocInfoE loc_540 ("p2")))) !={PtrOp, PtrOp, i32} (LocInfoE loc_541 (NULL)))
        then
        locinfo: loc_526 ;
          Goto "#22"
        else
        locinfo: loc_526 ;
          Goto "#23"
      ]> $
      <[ "#16" :=
        locinfo: loc_516 ;
        annot: (StopAnnot) ;
        expr: (LocInfoE loc_550 (&(LocInfoE loc_551 ("n")))) ;
        locinfo: loc_518 ;
        Goto "#13"
      ]> $
      <[ "#17" :=
        locinfo: loc_530 ;
        annot: (StopAnnot) ;
        expr: (LocInfoE loc_532 (&(LocInfoE loc_533 ("n")))) ;
        Goto "#1"
      ]> $
      <[ "#18" :=
        locinfo: loc_521 ;
        annot: (StopAnnot) ;
        expr: (LocInfoE loc_542 (&(LocInfoE loc_543 ("n")))) ;
        locinfo: loc_523 ;
        Goto "#15"
      ]> $
      <[ "#19" :=
        Goto "#1"
      ]> $
      <[ "#2" :=
        locinfo: loc_486 ;
        annot: (StopAnnot) ;
        expr: (LocInfoE loc_592 (&(LocInfoE loc_593 ("n")))) ;
        locinfo: loc_488 ;
        Goto "#3"
      ]> $
      <[ "#20" :=
        locinfo: loc_526 ;
        annot: (StopAnnot) ;
        expr: (LocInfoE loc_534 (&(LocInfoE loc_535 ("n")))) ;
        locinfo: loc_528 ;
        Goto "#17"
      ]> $
      <[ "#22" :=
        locinfo: loc_526 ;
        Goto "#20"
      ]> $
      <[ "#23" :=
        locinfo: loc_526 ;
        Goto "#20"
      ]> $
      <[ "#24" :=
        locinfo: loc_521 ;
        Goto "#18"
      ]> $
      <[ "#25" :=
        locinfo: loc_521 ;
        Goto "#18"
      ]> $
      <[ "#26" :=
        locinfo: loc_516 ;
        Goto "#16"
      ]> $
      <[ "#27" :=
        locinfo: loc_516 ;
        Goto "#16"
      ]> $
      <[ "#28" :=
        locinfo: loc_511 ;
        Goto "#14"
      ]> $
      <[ "#29" :=
        locinfo: loc_511 ;
        Goto "#14"
      ]> $
      <[ "#3" :=
        locinfo: loc_591 ;
        if{IntOp i32, Some "#6"}: LocInfoE loc_591 (i2v 1 i32)
        then
        locinfo: loc_491 ;
          Goto "#36"
        else
        locinfo: loc_491 ;
          Goto "#37"
      ]> $
      <[ "#30" :=
        locinfo: loc_506 ;
        Goto "#12"
      ]> $
      <[ "#31" :=
        locinfo: loc_506 ;
        Goto "#12"
      ]> $
      <[ "#32" :=
        locinfo: loc_501 ;
        Goto "#10"
      ]> $
      <[ "#33" :=
        locinfo: loc_501 ;
        Goto "#10"
      ]> $
      <[ "#34" :=
        locinfo: loc_496 ;
        Goto "#8"
      ]> $
      <[ "#35" :=
        locinfo: loc_496 ;
        Goto "#8"
      ]> $
      <[ "#36" :=
        locinfo: loc_491 ;
        Goto "#6"
      ]> $
      <[ "#37" :=
        locinfo: loc_491 ;
        Goto "#6"
      ]> $
      <[ "#4" :=
        locinfo: loc_585 ;
        if{IntOp i32, Some "#8"}: LocInfoE loc_585 (use{IntOp i32} (LocInfoE loc_586 ("m")))
        then
        locinfo: loc_496 ;
          Goto "#34"
        else
        locinfo: loc_496 ;
          Goto "#35"
      ]> $
      <[ "#5" :=
        locinfo: loc_578 ;
        if{IntOp i32, Some "#10"}: LocInfoE loc_578 ((LocInfoE loc_579 (i2v 1 i32)) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_580 (i2v 1 i32)))
        then
        locinfo: loc_501 ;
          Goto "#32"
        else
        locinfo: loc_501 ;
          Goto "#33"
      ]> $
      <[ "#6" :=
        locinfo: loc_491 ;
        annot: (StopAnnot) ;
        expr: (LocInfoE loc_587 (&(LocInfoE loc_588 ("n")))) ;
        locinfo: loc_493 ;
        Goto "#4"
      ]> $
      <[ "#7" :=
        locinfo: loc_570 ;
        if{IntOp i32, Some "#12"}: LocInfoE loc_570 ((LocInfoE loc_571 (use{IntOp i32} (LocInfoE loc_572 ("m")))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_573 (i2v 1 i32)))
        then
        locinfo: loc_506 ;
          Goto "#30"
        else
        locinfo: loc_506 ;
          Goto "#31"
      ]> $
      <[ "#8" :=
        locinfo: loc_496 ;
        annot: (StopAnnot) ;
        expr: (LocInfoE loc_581 (&(LocInfoE loc_582 ("n")))) ;
        locinfo: loc_498 ;
        Goto "#5"
      ]> $
      <[ "#9" :=
        locinfo: loc_562 ;
        if{IntOp i32, Some "#14"}: LocInfoE loc_562 ((LocInfoE loc_563 (use{PtrOp} (LocInfoE loc_564 ("p1")))) ={PtrOp, PtrOp, i32} (LocInfoE loc_565 (NULL)))
        then
        locinfo: loc_511 ;
          Goto "#28"
        else
        locinfo: loc_511 ;
          Goto "#29"
      ]> $∅
    )%E
  |}.
End code.
