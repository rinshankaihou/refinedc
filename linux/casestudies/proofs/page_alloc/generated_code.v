From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [linux/casestudies/page_alloc.c]. *)
Section code.
  Definition file_0 : string := "linux/casestudies/page_alloc.c".
  Definition loc_2 : location_info := LocationInfo file_0 36 1 36 11.
  Definition loc_3 : location_info := LocationInfo file_0 36 8 36 9.
  Definition loc_6 : location_info := LocationInfo file_0 66 1 66 10.
  Definition loc_7 : location_info := LocationInfo file_0 66 8 66 9.
  Definition loc_10 : location_info := LocationInfo file_0 70 1 70 10.
  Definition loc_11 : location_info := LocationInfo file_0 70 8 70 9.
  Definition loc_14 : location_info := LocationInfo file_0 82 1 82 25.
  Definition loc_15 : location_info := LocationInfo file_0 83 1 83 19.
  Definition loc_16 : location_info := LocationInfo file_0 83 1 83 11.
  Definition loc_17 : location_info := LocationInfo file_0 83 1 83 5.
  Definition loc_18 : location_info := LocationInfo file_0 83 1 83 5.
  Definition loc_19 : location_info := LocationInfo file_0 83 14 83 18.
  Definition loc_20 : location_info := LocationInfo file_0 83 14 83 18.
  Definition loc_21 : location_info := LocationInfo file_0 82 2 82 14.
  Definition loc_22 : location_info := LocationInfo file_0 82 3 82 7.
  Definition loc_23 : location_info := LocationInfo file_0 82 3 82 7.
  Definition loc_24 : location_info := LocationInfo file_0 82 17 82 23.
  Definition loc_25 : location_info := LocationInfo file_0 82 17 82 23.
  Definition loc_28 : location_info := LocationInfo file_0 96 1 97 9.
  Definition loc_29 : location_info := LocationInfo file_0 99 1 99 18.
  Definition loc_30 : location_info := LocationInfo file_0 100 1 100 18.
  Definition loc_31 : location_info := LocationInfo file_0 101 1 101 18.
  Definition loc_32 : location_info := LocationInfo file_0 102 1 102 24.
  Definition loc_33 : location_info := LocationInfo file_0 102 2 102 14.
  Definition loc_34 : location_info := LocationInfo file_0 102 3 102 7.
  Definition loc_35 : location_info := LocationInfo file_0 102 3 102 7.
  Definition loc_36 : location_info := LocationInfo file_0 102 17 102 22.
  Definition loc_37 : location_info := LocationInfo file_0 102 17 102 22.
  Definition loc_38 : location_info := LocationInfo file_0 101 1 101 10.
  Definition loc_39 : location_info := LocationInfo file_0 101 1 101 4.
  Definition loc_40 : location_info := LocationInfo file_0 101 1 101 4.
  Definition loc_41 : location_info := LocationInfo file_0 101 13 101 17.
  Definition loc_42 : location_info := LocationInfo file_0 101 13 101 17.
  Definition loc_43 : location_info := LocationInfo file_0 100 1 100 10.
  Definition loc_44 : location_info := LocationInfo file_0 100 1 100 4.
  Definition loc_45 : location_info := LocationInfo file_0 100 1 100 4.
  Definition loc_46 : location_info := LocationInfo file_0 100 13 100 17.
  Definition loc_47 : location_info := LocationInfo file_0 100 13 100 17.
  Definition loc_48 : location_info := LocationInfo file_0 99 1 99 11.
  Definition loc_49 : location_info := LocationInfo file_0 99 1 99 5.
  Definition loc_50 : location_info := LocationInfo file_0 99 1 99 5.
  Definition loc_51 : location_info := LocationInfo file_0 99 14 99 17.
  Definition loc_52 : location_info := LocationInfo file_0 99 14 99 17.
  Definition loc_53 : location_info := LocationInfo file_0 97 2 97 9.
  Definition loc_56 : location_info := LocationInfo file_0 96 5 96 39.
  Definition loc_58 : location_info := LocationInfo file_0 96 6 96 39.
  Definition loc_59 : location_info := LocationInfo file_0 96 6 96 22.
  Definition loc_60 : location_info := LocationInfo file_0 96 6 96 22.
  Definition loc_61 : location_info := LocationInfo file_0 96 23 96 26.
  Definition loc_62 : location_info := LocationInfo file_0 96 23 96 26.
  Definition loc_63 : location_info := LocationInfo file_0 96 28 96 32.
  Definition loc_64 : location_info := LocationInfo file_0 96 28 96 32.
  Definition loc_65 : location_info := LocationInfo file_0 96 34 96 38.
  Definition loc_66 : location_info := LocationInfo file_0 96 34 96 38.
  Definition loc_69 : location_info := LocationInfo file_0 119 1 119 35.
  Definition loc_70 : location_info := LocationInfo file_0 119 1 119 11.
  Definition loc_71 : location_info := LocationInfo file_0 119 1 119 11.
  Definition loc_72 : location_info := LocationInfo file_0 119 12 119 15.
  Definition loc_73 : location_info := LocationInfo file_0 119 12 119 15.
  Definition loc_74 : location_info := LocationInfo file_0 119 17 119 21.
  Definition loc_75 : location_info := LocationInfo file_0 119 17 119 21.
  Definition loc_76 : location_info := LocationInfo file_0 119 23 119 33.
  Definition loc_77 : location_info := LocationInfo file_0 119 23 119 33.
  Definition loc_78 : location_info := LocationInfo file_0 119 23 119 27.
  Definition loc_79 : location_info := LocationInfo file_0 119 23 119 27.
  Definition loc_82 : location_info := LocationInfo file_0 133 1 133 35.
  Definition loc_83 : location_info := LocationInfo file_0 133 1 133 11.
  Definition loc_84 : location_info := LocationInfo file_0 133 1 133 11.
  Definition loc_85 : location_info := LocationInfo file_0 133 12 133 15.
  Definition loc_86 : location_info := LocationInfo file_0 133 12 133 15.
  Definition loc_87 : location_info := LocationInfo file_0 133 17 133 27.
  Definition loc_88 : location_info := LocationInfo file_0 133 17 133 27.
  Definition loc_89 : location_info := LocationInfo file_0 133 17 133 21.
  Definition loc_90 : location_info := LocationInfo file_0 133 17 133 21.
  Definition loc_91 : location_info := LocationInfo file_0 133 29 133 33.
  Definition loc_92 : location_info := LocationInfo file_0 133 29 133 33.
  Definition loc_95 : location_info := LocationInfo file_0 145 1 145 19.
  Definition loc_96 : location_info := LocationInfo file_0 146 1 146 25.
  Definition loc_97 : location_info := LocationInfo file_0 146 2 146 14.
  Definition loc_98 : location_info := LocationInfo file_0 146 3 146 7.
  Definition loc_99 : location_info := LocationInfo file_0 146 3 146 7.
  Definition loc_100 : location_info := LocationInfo file_0 146 17 146 23.
  Definition loc_101 : location_info := LocationInfo file_0 146 17 146 23.
  Definition loc_102 : location_info := LocationInfo file_0 145 1 145 11.
  Definition loc_103 : location_info := LocationInfo file_0 145 1 145 5.
  Definition loc_104 : location_info := LocationInfo file_0 145 1 145 5.
  Definition loc_105 : location_info := LocationInfo file_0 145 14 145 18.
  Definition loc_106 : location_info := LocationInfo file_0 145 14 145 18.
  Definition loc_109 : location_info := LocationInfo file_0 151 1 152 9.
  Definition loc_110 : location_info := LocationInfo file_0 154 1 154 38.
  Definition loc_111 : location_info := LocationInfo file_0 154 1 154 11.
  Definition loc_112 : location_info := LocationInfo file_0 154 1 154 11.
  Definition loc_113 : location_info := LocationInfo file_0 154 12 154 23.
  Definition loc_114 : location_info := LocationInfo file_0 154 12 154 23.
  Definition loc_115 : location_info := LocationInfo file_0 154 12 154 17.
  Definition loc_116 : location_info := LocationInfo file_0 154 12 154 17.
  Definition loc_117 : location_info := LocationInfo file_0 154 25 154 36.
  Definition loc_118 : location_info := LocationInfo file_0 154 25 154 36.
  Definition loc_119 : location_info := LocationInfo file_0 154 25 154 30.
  Definition loc_120 : location_info := LocationInfo file_0 154 25 154 30.
  Definition loc_121 : location_info := LocationInfo file_0 152 2 152 9.
  Definition loc_124 : location_info := LocationInfo file_0 151 5 151 35.
  Definition loc_126 : location_info := LocationInfo file_0 151 6 151 35.
  Definition loc_127 : location_info := LocationInfo file_0 151 6 151 28.
  Definition loc_128 : location_info := LocationInfo file_0 151 6 151 28.
  Definition loc_129 : location_info := LocationInfo file_0 151 29 151 34.
  Definition loc_130 : location_info := LocationInfo file_0 151 29 151 34.
  Definition loc_133 : location_info := LocationInfo file_0 168 1 168 25.
  Definition loc_134 : location_info := LocationInfo file_0 169 1 169 23.
  Definition loc_135 : location_info := LocationInfo file_0 169 1 169 15.
  Definition loc_136 : location_info := LocationInfo file_0 169 1 169 15.
  Definition loc_137 : location_info := LocationInfo file_0 169 16 169 21.
  Definition loc_138 : location_info := LocationInfo file_0 169 16 169 21.
  Definition loc_139 : location_info := LocationInfo file_0 168 1 168 17.
  Definition loc_140 : location_info := LocationInfo file_0 168 1 168 17.
  Definition loc_141 : location_info := LocationInfo file_0 168 18 168 23.
  Definition loc_142 : location_info := LocationInfo file_0 168 18 168 23.
  Definition loc_145 : location_info := LocationInfo file_0 183 1 183 29.
  Definition loc_146 : location_info := LocationInfo file_0 183 8 183 28.
  Definition loc_147 : location_info := LocationInfo file_0 183 8 183 20.
  Definition loc_148 : location_info := LocationInfo file_0 183 8 183 20.
  Definition loc_149 : location_info := LocationInfo file_0 183 9 183 13.
  Definition loc_150 : location_info := LocationInfo file_0 183 9 183 13.
  Definition loc_151 : location_info := LocationInfo file_0 183 24 183 28.
  Definition loc_152 : location_info := LocationInfo file_0 183 24 183 28.
  Definition loc_155 : location_info := LocationInfo file_0 250 1 250 62.
  Definition loc_156 : location_info := LocationInfo file_0 250 8 250 61.
  Definition loc_157 : location_info := LocationInfo file_0 250 17 250 60.
  Definition loc_158 : location_info := LocationInfo file_0 250 18 250 37.
  Definition loc_159 : location_info := LocationInfo file_0 250 31 250 37.
  Definition loc_160 : location_info := LocationInfo file_0 250 31 250 37.
  Definition loc_161 : location_info := LocationInfo file_0 250 40 250 59.
  Definition loc_162 : location_info := LocationInfo file_0 250 40 250 59.
  Definition loc_165 : location_info := LocationInfo file_0 255 1 255 52.
  Definition loc_166 : location_info := LocationInfo file_0 255 8 255 51.
  Definition loc_167 : location_info := LocationInfo file_0 255 9 255 28.
  Definition loc_168 : location_info := LocationInfo file_0 255 22 255 28.
  Definition loc_169 : location_info := LocationInfo file_0 255 22 255 28.
  Definition loc_170 : location_info := LocationInfo file_0 255 31 255 50.
  Definition loc_171 : location_info := LocationInfo file_0 255 31 255 50.
  Definition loc_174 : location_info := LocationInfo file_0 269 1 269 62.
  Definition loc_175 : location_info := LocationInfo file_0 269 8 269 61.
  Definition loc_176 : location_info := LocationInfo file_0 269 9 269 43.
  Definition loc_177 : location_info := LocationInfo file_0 269 29 269 42.
  Definition loc_178 : location_info := LocationInfo file_0 269 29 269 42.
  Definition loc_179 : location_info := LocationInfo file_0 269 46 269 60.
  Definition loc_180 : location_info := LocationInfo file_0 269 47 269 53.
  Definition loc_181 : location_info := LocationInfo file_0 269 47 269 53.
  Definition loc_182 : location_info := LocationInfo file_0 269 57 269 59.
  Definition loc_185 : location_info := LocationInfo file_0 282 1 282 75.
  Definition loc_186 : location_info := LocationInfo file_0 282 8 282 74.
  Definition loc_187 : location_info := LocationInfo file_0 282 9 282 67.
  Definition loc_188 : location_info := LocationInfo file_0 282 22 282 67.
  Definition loc_189 : location_info := LocationInfo file_0 282 23 282 29.
  Definition loc_190 : location_info := LocationInfo file_0 282 23 282 29.
  Definition loc_191 : location_info := LocationInfo file_0 282 32 282 66.
  Definition loc_192 : location_info := LocationInfo file_0 282 52 282 65.
  Definition loc_193 : location_info := LocationInfo file_0 282 52 282 65.
  Definition loc_194 : location_info := LocationInfo file_0 282 71 282 73.
  Definition loc_197 : location_info := LocationInfo file_0 290 1 290 84.
  Definition loc_198 : location_info := LocationInfo file_0 292 1 292 20.
  Definition loc_199 : location_info := LocationInfo file_0 292 8 292 19.
  Definition loc_200 : location_info := LocationInfo file_0 292 8 292 19.
  Definition loc_201 : location_info := LocationInfo file_0 292 8 292 9.
  Definition loc_202 : location_info := LocationInfo file_0 292 8 292 9.
  Definition loc_203 : location_info := LocationInfo file_0 290 22 290 83.
  Definition loc_204 : location_info := LocationInfo file_0 290 22 290 38.
  Definition loc_205 : location_info := LocationInfo file_0 290 22 290 38.
  Definition loc_206 : location_info := LocationInfo file_0 290 39 290 82.
  Definition loc_207 : location_info := LocationInfo file_0 290 40 290 59.
  Definition loc_208 : location_info := LocationInfo file_0 290 53 290 59.
  Definition loc_209 : location_info := LocationInfo file_0 290 53 290 59.
  Definition loc_210 : location_info := LocationInfo file_0 290 62 290 81.
  Definition loc_211 : location_info := LocationInfo file_0 290 62 290 81.
  Definition loc_216 : location_info := LocationInfo file_0 527 1 527 22.
  Definition loc_217 : location_info := LocationInfo file_0 528 1 528 42.
  Definition loc_218 : location_info := LocationInfo file_0 529 1 529 24.
  Definition loc_219 : location_info := LocationInfo file_0 531 1 531 98.
  Definition loc_220 : location_info := LocationInfo file_0 531 8 531 97.
  Definition loc_221 : location_info := LocationInfo file_0 531 8 531 9.
  Definition loc_222 : location_info := LocationInfo file_0 531 8 531 9.
  Definition loc_223 : location_info := LocationInfo file_0 531 12 531 80.
  Definition loc_224 : location_info := LocationInfo file_0 531 21 531 79.
  Definition loc_225 : location_info := LocationInfo file_0 531 22 531 56.
  Definition loc_226 : location_info := LocationInfo file_0 531 35 531 56.
  Definition loc_227 : location_info := LocationInfo file_0 531 36 531 52.
  Definition loc_228 : location_info := LocationInfo file_0 531 36 531 52.
  Definition loc_229 : location_info := LocationInfo file_0 531 53 531 54.
  Definition loc_230 : location_info := LocationInfo file_0 531 53 531 54.
  Definition loc_231 : location_info := LocationInfo file_0 531 59 531 78.
  Definition loc_232 : location_info := LocationInfo file_0 531 59 531 78.
  Definition loc_233 : location_info := LocationInfo file_0 531 83 531 97.
  Definition loc_234 : location_info := LocationInfo file_0 529 1 529 10.
  Definition loc_235 : location_info := LocationInfo file_0 529 1 529 10.
  Definition loc_236 : location_info := LocationInfo file_0 529 11 529 22.
  Definition loc_237 : location_info := LocationInfo file_0 529 12 529 22.
  Definition loc_238 : location_info := LocationInfo file_0 529 12 529 16.
  Definition loc_239 : location_info := LocationInfo file_0 529 12 529 16.
  Definition loc_240 : location_info := LocationInfo file_0 528 1 528 2.
  Definition loc_241 : location_info := LocationInfo file_0 528 5 528 41.
  Definition loc_242 : location_info := LocationInfo file_0 528 5 528 22.
  Definition loc_243 : location_info := LocationInfo file_0 528 5 528 22.
  Definition loc_244 : location_info := LocationInfo file_0 528 23 528 27.
  Definition loc_245 : location_info := LocationInfo file_0 528 23 528 27.
  Definition loc_246 : location_info := LocationInfo file_0 528 29 528 33.
  Definition loc_247 : location_info := LocationInfo file_0 528 29 528 33.
  Definition loc_248 : location_info := LocationInfo file_0 528 35 528 40.
  Definition loc_249 : location_info := LocationInfo file_0 528 35 528 40.
  Definition loc_250 : location_info := LocationInfo file_0 527 1 527 8.
  Definition loc_251 : location_info := LocationInfo file_0 527 1 527 8.
  Definition loc_252 : location_info := LocationInfo file_0 527 9 527 20.
  Definition loc_253 : location_info := LocationInfo file_0 527 10 527 20.
  Definition loc_254 : location_info := LocationInfo file_0 527 10 527 14.
  Definition loc_255 : location_info := LocationInfo file_0 527 10 527 14.
  Definition loc_258 : location_info := LocationInfo file_0 458 1 458 84.
  Definition loc_259 : location_info := LocationInfo file_0 459 1 459 56.
  Definition loc_260 : location_info := LocationInfo file_0 461 1 461 22.
  Definition loc_261 : location_info := LocationInfo file_0 462 1 462 15.
  Definition loc_262 : location_info := LocationInfo file_0 463 1 463 24.
  Definition loc_263 : location_info := LocationInfo file_0 463 1 463 10.
  Definition loc_264 : location_info := LocationInfo file_0 463 1 463 10.
  Definition loc_265 : location_info := LocationInfo file_0 463 11 463 22.
  Definition loc_266 : location_info := LocationInfo file_0 463 12 463 22.
  Definition loc_267 : location_info := LocationInfo file_0 463 12 463 16.
  Definition loc_268 : location_info := LocationInfo file_0 463 12 463 16.
  Definition loc_269 : location_info := LocationInfo file_0 462 1 462 12.
  Definition loc_270 : location_info := LocationInfo file_0 462 1 462 2.
  Definition loc_271 : location_info := LocationInfo file_0 462 1 462 2.
  Definition loc_272 : location_info := LocationInfo file_0 461 1 461 8.
  Definition loc_273 : location_info := LocationInfo file_0 461 1 461 8.
  Definition loc_274 : location_info := LocationInfo file_0 461 9 461 20.
  Definition loc_275 : location_info := LocationInfo file_0 461 10 461 20.
  Definition loc_276 : location_info := LocationInfo file_0 461 10 461 14.
  Definition loc_277 : location_info := LocationInfo file_0 461 10 461 14.
  Definition loc_278 : location_info := LocationInfo file_0 459 25 459 55.
  Definition loc_279 : location_info := LocationInfo file_0 459 25 459 55.
  Definition loc_280 : location_info := LocationInfo file_0 459 26 459 48.
  Definition loc_281 : location_info := LocationInfo file_0 459 46 459 47.
  Definition loc_282 : location_info := LocationInfo file_0 459 46 459 47.
  Definition loc_285 : location_info := LocationInfo file_0 458 22 458 83.
  Definition loc_286 : location_info := LocationInfo file_0 458 22 458 38.
  Definition loc_287 : location_info := LocationInfo file_0 458 22 458 38.
  Definition loc_288 : location_info := LocationInfo file_0 458 39 458 82.
  Definition loc_289 : location_info := LocationInfo file_0 458 40 458 59.
  Definition loc_290 : location_info := LocationInfo file_0 458 53 458 59.
  Definition loc_291 : location_info := LocationInfo file_0 458 53 458 59.
  Definition loc_292 : location_info := LocationInfo file_0 458 62 458 81.
  Definition loc_293 : location_info := LocationInfo file_0 458 62 458 81.
  Definition loc_298 : location_info := LocationInfo file_0 444 1 444 84.
  Definition loc_299 : location_info := LocationInfo file_0 445 1 445 56.
  Definition loc_300 : location_info := LocationInfo file_0 447 1 447 22.
  Definition loc_301 : location_info := LocationInfo file_0 448 1 449 14.
  Definition loc_302 : location_info := LocationInfo file_0 450 1 450 15.
  Definition loc_303 : location_info := LocationInfo file_0 451 1 452 29.
  Definition loc_304 : location_info := LocationInfo file_0 453 1 453 24.
  Definition loc_305 : location_info := LocationInfo file_0 453 1 453 10.
  Definition loc_306 : location_info := LocationInfo file_0 453 1 453 10.
  Definition loc_307 : location_info := LocationInfo file_0 453 11 453 22.
  Definition loc_308 : location_info := LocationInfo file_0 453 12 453 22.
  Definition loc_309 : location_info := LocationInfo file_0 453 12 453 16.
  Definition loc_310 : location_info := LocationInfo file_0 453 12 453 16.
  Definition loc_311 : location_info := LocationInfo file_0 452 2 452 29.
  Definition loc_312 : location_info := LocationInfo file_0 452 2 452 19.
  Definition loc_313 : location_info := LocationInfo file_0 452 2 452 19.
  Definition loc_314 : location_info := LocationInfo file_0 452 20 452 24.
  Definition loc_315 : location_info := LocationInfo file_0 452 20 452 24.
  Definition loc_316 : location_info := LocationInfo file_0 452 26 452 27.
  Definition loc_317 : location_info := LocationInfo file_0 452 26 452 27.
  Definition loc_319 : location_info := LocationInfo file_0 451 5 451 17.
  Definition loc_321 : location_info := LocationInfo file_0 451 6 451 17.
  Definition loc_322 : location_info := LocationInfo file_0 451 6 451 17.
  Definition loc_323 : location_info := LocationInfo file_0 451 6 451 7.
  Definition loc_324 : location_info := LocationInfo file_0 451 6 451 7.
  Definition loc_325 : location_info := LocationInfo file_0 450 1 450 12.
  Definition loc_326 : location_info := LocationInfo file_0 450 1 450 2.
  Definition loc_327 : location_info := LocationInfo file_0 450 1 450 2.
  Definition loc_328 : location_info := LocationInfo file_0 449 2 449 14.
  Definition loc_329 : location_info := LocationInfo file_0 449 2 449 11.
  Definition loc_330 : location_info := LocationInfo file_0 449 2 449 11.
  Definition loc_332 : location_info := LocationInfo file_0 448 5 448 17.
  Definition loc_334 : location_info := LocationInfo file_0 448 6 448 17.
  Definition loc_335 : location_info := LocationInfo file_0 448 6 448 17.
  Definition loc_336 : location_info := LocationInfo file_0 448 6 448 7.
  Definition loc_337 : location_info := LocationInfo file_0 448 6 448 7.
  Definition loc_338 : location_info := LocationInfo file_0 447 1 447 8.
  Definition loc_339 : location_info := LocationInfo file_0 447 1 447 8.
  Definition loc_340 : location_info := LocationInfo file_0 447 9 447 20.
  Definition loc_341 : location_info := LocationInfo file_0 447 10 447 20.
  Definition loc_342 : location_info := LocationInfo file_0 447 10 447 14.
  Definition loc_343 : location_info := LocationInfo file_0 447 10 447 14.
  Definition loc_344 : location_info := LocationInfo file_0 445 25 445 55.
  Definition loc_345 : location_info := LocationInfo file_0 445 25 445 55.
  Definition loc_346 : location_info := LocationInfo file_0 445 26 445 48.
  Definition loc_347 : location_info := LocationInfo file_0 445 46 445 47.
  Definition loc_348 : location_info := LocationInfo file_0 445 46 445 47.
  Definition loc_351 : location_info := LocationInfo file_0 444 22 444 83.
  Definition loc_352 : location_info := LocationInfo file_0 444 22 444 38.
  Definition loc_353 : location_info := LocationInfo file_0 444 22 444 38.
  Definition loc_354 : location_info := LocationInfo file_0 444 39 444 82.
  Definition loc_355 : location_info := LocationInfo file_0 444 40 444 59.
  Definition loc_356 : location_info := LocationInfo file_0 444 53 444 59.
  Definition loc_357 : location_info := LocationInfo file_0 444 53 444 59.
  Definition loc_358 : location_info := LocationInfo file_0 444 62 444 81.
  Definition loc_359 : location_info := LocationInfo file_0 444 62 444 81.
  Definition loc_364 : location_info := LocationInfo file_0 541 1 542 13.
  Definition loc_365 : location_info := LocationInfo file_0 544 1 544 22.
  Definition loc_366 : location_info := LocationInfo file_0 545 6 545 11.
  Definition loc_367 : location_info := LocationInfo file_0 545 1 546 38.
  Definition loc_368 : location_info := LocationInfo file_0 547 1 547 26.
  Definition loc_369 : location_info := LocationInfo file_0 548 1 548 43.
  Definition loc_370 : location_info := LocationInfo file_0 551 1 551 28.
  Definition loc_371 : location_info := LocationInfo file_0 552 1 552 37.
  Definition loc_372 : location_info := LocationInfo file_0 555 6 555 11.
  Definition loc_373 : location_info := LocationInfo file_0 555 1 560 2.
  Definition loc_374 : location_info := LocationInfo file_0 563 1 563 49.
  Definition loc_375 : location_info := LocationInfo file_0 566 6 566 20.
  Definition loc_376 : location_info := LocationInfo file_0 566 1 570 2.
  Definition loc_377 : location_info := LocationInfo file_0 572 1 572 10.
  Definition loc_378 : location_info := LocationInfo file_0 572 8 572 9.
  Definition loc_379 : location_info := LocationInfo file_0 566 41 570 2.
  Definition loc_380 : location_info := LocationInfo file_0 567 2 567 29.
  Definition loc_381 : location_info := LocationInfo file_0 569 2 569 9.
  Definition loc_382 : location_info := LocationInfo file_0 566 1 570 2.
  Definition loc_383 : location_info := LocationInfo file_0 566 36 566 39.
  Definition loc_384 : location_info := LocationInfo file_0 566 36 566 37.
  Definition loc_385 : location_info := LocationInfo file_0 569 2 569 3.
  Definition loc_386 : location_info := LocationInfo file_0 569 2 569 8.
  Definition loc_387 : location_info := LocationInfo file_0 569 2 569 3.
  Definition loc_388 : location_info := LocationInfo file_0 569 2 569 3.
  Definition loc_389 : location_info := LocationInfo file_0 569 7 569 8.
  Definition loc_390 : location_info := LocationInfo file_0 567 2 567 19.
  Definition loc_391 : location_info := LocationInfo file_0 567 2 567 19.
  Definition loc_392 : location_info := LocationInfo file_0 567 20 567 24.
  Definition loc_393 : location_info := LocationInfo file_0 567 20 567 24.
  Definition loc_394 : location_info := LocationInfo file_0 567 26 567 27.
  Definition loc_395 : location_info := LocationInfo file_0 567 26 567 27.
  Definition loc_396 : location_info := LocationInfo file_0 566 22 566 34.
  Definition loc_397 : location_info := LocationInfo file_0 566 22 566 23.
  Definition loc_398 : location_info := LocationInfo file_0 566 22 566 23.
  Definition loc_399 : location_info := LocationInfo file_0 566 26 566 34.
  Definition loc_400 : location_info := LocationInfo file_0 566 26 566 34.
  Definition loc_401 : location_info := LocationInfo file_0 566 6 566 7.
  Definition loc_402 : location_info := LocationInfo file_0 566 10 566 20.
  Definition loc_403 : location_info := LocationInfo file_0 566 10 566 20.
  Definition loc_404 : location_info := LocationInfo file_0 563 1 563 2.
  Definition loc_405 : location_info := LocationInfo file_0 563 5 563 48.
  Definition loc_406 : location_info := LocationInfo file_0 563 5 563 21.
  Definition loc_407 : location_info := LocationInfo file_0 563 5 563 21.
  Definition loc_408 : location_info := LocationInfo file_0 563 22 563 47.
  Definition loc_409 : location_info := LocationInfo file_0 563 22 563 26.
  Definition loc_410 : location_info := LocationInfo file_0 563 22 563 26.
  Definition loc_411 : location_info := LocationInfo file_0 563 29 563 47.
  Definition loc_412 : location_info := LocationInfo file_0 563 30 563 40.
  Definition loc_413 : location_info := LocationInfo file_0 563 30 563 40.
  Definition loc_414 : location_info := LocationInfo file_0 563 44 563 46.
  Definition loc_415 : location_info := LocationInfo file_0 555 32 560 2.
  Definition loc_416 : location_info := LocationInfo file_0 556 2 556 17.
  Definition loc_417 : location_info := LocationInfo file_0 557 2 557 27.
  Definition loc_418 : location_info := LocationInfo file_0 559 2 559 9.
  Definition loc_419 : location_info := LocationInfo file_0 555 1 560 2.
  Definition loc_420 : location_info := LocationInfo file_0 555 27 555 30.
  Definition loc_421 : location_info := LocationInfo file_0 555 27 555 28.
  Definition loc_422 : location_info := LocationInfo file_0 559 2 559 3.
  Definition loc_423 : location_info := LocationInfo file_0 559 2 559 8.
  Definition loc_424 : location_info := LocationInfo file_0 559 2 559 3.
  Definition loc_425 : location_info := LocationInfo file_0 559 2 559 3.
  Definition loc_426 : location_info := LocationInfo file_0 559 7 559 8.
  Definition loc_427 : location_info := LocationInfo file_0 557 2 557 16.
  Definition loc_428 : location_info := LocationInfo file_0 557 2 557 16.
  Definition loc_429 : location_info := LocationInfo file_0 557 17 557 25.
  Definition loc_430 : location_info := LocationInfo file_0 557 18 557 25.
  Definition loc_431 : location_info := LocationInfo file_0 557 18 557 19.
  Definition loc_432 : location_info := LocationInfo file_0 557 18 557 19.
  Definition loc_433 : location_info := LocationInfo file_0 556 2 556 9.
  Definition loc_434 : location_info := LocationInfo file_0 556 2 556 3.
  Definition loc_435 : location_info := LocationInfo file_0 556 2 556 3.
  Definition loc_436 : location_info := LocationInfo file_0 556 12 556 16.
  Definition loc_437 : location_info := LocationInfo file_0 556 12 556 16.
  Definition loc_438 : location_info := LocationInfo file_0 555 13 555 25.
  Definition loc_439 : location_info := LocationInfo file_0 555 13 555 14.
  Definition loc_440 : location_info := LocationInfo file_0 555 13 555 14.
  Definition loc_441 : location_info := LocationInfo file_0 555 17 555 25.
  Definition loc_442 : location_info := LocationInfo file_0 555 17 555 25.
  Definition loc_443 : location_info := LocationInfo file_0 555 6 555 7.
  Definition loc_444 : location_info := LocationInfo file_0 555 10 555 11.
  Definition loc_445 : location_info := LocationInfo file_0 552 1 552 7.
  Definition loc_446 : location_info := LocationInfo file_0 552 1 552 7.
  Definition loc_447 : location_info := LocationInfo file_0 552 8 552 9.
  Definition loc_448 : location_info := LocationInfo file_0 552 8 552 9.
  Definition loc_449 : location_info := LocationInfo file_0 552 11 552 12.
  Definition loc_450 : location_info := LocationInfo file_0 552 14 552 35.
  Definition loc_451 : location_info := LocationInfo file_0 552 14 552 24.
  Definition loc_452 : location_info := LocationInfo file_0 552 27 552 35.
  Definition loc_453 : location_info := LocationInfo file_0 552 27 552 35.
  Definition loc_454 : location_info := LocationInfo file_0 551 1 551 2.
  Definition loc_455 : location_info := LocationInfo file_0 551 5 551 27.
  Definition loc_456 : location_info := LocationInfo file_0 551 5 551 21.
  Definition loc_457 : location_info := LocationInfo file_0 551 5 551 21.
  Definition loc_458 : location_info := LocationInfo file_0 551 22 551 26.
  Definition loc_459 : location_info := LocationInfo file_0 551 22 551 26.
  Definition loc_460 : location_info := LocationInfo file_0 548 1 548 16.
  Definition loc_461 : location_info := LocationInfo file_0 548 1 548 5.
  Definition loc_462 : location_info := LocationInfo file_0 548 1 548 5.
  Definition loc_463 : location_info := LocationInfo file_0 548 19 548 42.
  Definition loc_464 : location_info := LocationInfo file_0 548 19 548 23.
  Definition loc_465 : location_info := LocationInfo file_0 548 19 548 23.
  Definition loc_466 : location_info := LocationInfo file_0 548 26 548 42.
  Definition loc_467 : location_info := LocationInfo file_0 548 27 548 35.
  Definition loc_468 : location_info := LocationInfo file_0 548 27 548 35.
  Definition loc_469 : location_info := LocationInfo file_0 548 39 548 41.
  Definition loc_470 : location_info := LocationInfo file_0 547 1 547 18.
  Definition loc_471 : location_info := LocationInfo file_0 547 1 547 5.
  Definition loc_472 : location_info := LocationInfo file_0 547 1 547 5.
  Definition loc_473 : location_info := LocationInfo file_0 547 21 547 25.
  Definition loc_474 : location_info := LocationInfo file_0 547 21 547 25.
  Definition loc_475 : location_info := LocationInfo file_0 545 1 546 38.
  Definition loc_476 : location_info := LocationInfo file_0 546 2 546 38.
  Definition loc_477 : location_info := LocationInfo file_0 545 1 546 38.
  Definition loc_478 : location_info := LocationInfo file_0 545 23 545 26.
  Definition loc_479 : location_info := LocationInfo file_0 545 23 545 24.
  Definition loc_480 : location_info := LocationInfo file_0 546 2 546 16.
  Definition loc_481 : location_info := LocationInfo file_0 546 2 546 16.
  Definition loc_482 : location_info := LocationInfo file_0 546 17 546 36.
  Definition loc_483 : location_info := LocationInfo file_0 546 18 546 36.
  Definition loc_484 : location_info := LocationInfo file_0 546 18 546 36.
  Definition loc_485 : location_info := LocationInfo file_0 546 18 546 33.
  Definition loc_486 : location_info := LocationInfo file_0 546 18 546 33.
  Definition loc_487 : location_info := LocationInfo file_0 546 18 546 22.
  Definition loc_488 : location_info := LocationInfo file_0 546 18 546 22.
  Definition loc_489 : location_info := LocationInfo file_0 546 34 546 35.
  Definition loc_490 : location_info := LocationInfo file_0 546 34 546 35.
  Definition loc_491 : location_info := LocationInfo file_0 545 13 545 21.
  Definition loc_492 : location_info := LocationInfo file_0 545 13 545 14.
  Definition loc_493 : location_info := LocationInfo file_0 545 13 545 14.
  Definition loc_494 : location_info := LocationInfo file_0 545 18 545 21.
  Definition loc_495 : location_info := LocationInfo file_0 545 6 545 7.
  Definition loc_496 : location_info := LocationInfo file_0 545 10 545 11.
  Definition loc_497 : location_info := LocationInfo file_0 544 1 544 8.
  Definition loc_498 : location_info := LocationInfo file_0 544 1 544 8.
  Definition loc_499 : location_info := LocationInfo file_0 544 9 544 20.
  Definition loc_500 : location_info := LocationInfo file_0 544 10 544 20.
  Definition loc_501 : location_info := LocationInfo file_0 544 10 544 14.
  Definition loc_502 : location_info := LocationInfo file_0 544 10 544 14.
  Definition loc_503 : location_info := LocationInfo file_0 542 2 542 13.
  Definition loc_504 : location_info := LocationInfo file_0 542 9 542 12.
  Definition loc_505 : location_info := LocationInfo file_0 542 10 542 12.
  Definition loc_507 : location_info := LocationInfo file_0 541 5 541 16.
  Definition loc_508 : location_info := LocationInfo file_0 541 5 541 9.
  Definition loc_509 : location_info := LocationInfo file_0 541 5 541 9.
  Definition loc_510 : location_info := LocationInfo file_0 541 12 541 16.
  Definition loc_513 : location_info := LocationInfo file_0 378 1 378 15.
  Definition loc_514 : location_info := LocationInfo file_0 378 15 378 2.
  Definition loc_515 : location_info := LocationInfo file_0 379 1 379 40.
  Definition loc_516 : location_info := LocationInfo file_0 381 1 381 25.
  Definition loc_517 : location_info := LocationInfo file_0 382 1 383 24.
  Definition loc_518 : location_info := LocationInfo file_0 385 1 385 31.
  Definition loc_519 : location_info := LocationInfo file_0 385 8 385 30.
  Definition loc_520 : location_info := LocationInfo file_0 385 8 385 24.
  Definition loc_521 : location_info := LocationInfo file_0 385 8 385 24.
  Definition loc_522 : location_info := LocationInfo file_0 385 25 385 29.
  Definition loc_523 : location_info := LocationInfo file_0 385 25 385 29.
  Definition loc_524 : location_info := LocationInfo file_0 383 2 383 24.
  Definition loc_525 : location_info := LocationInfo file_0 383 9 383 23.
  Definition loc_528 : location_info := LocationInfo file_0 382 5 382 29.
  Definition loc_529 : location_info := LocationInfo file_0 382 5 382 9.
  Definition loc_530 : location_info := LocationInfo file_0 382 5 382 9.
  Definition loc_531 : location_info := LocationInfo file_0 382 12 382 29.
  Definition loc_532 : location_info := LocationInfo file_0 382 12 382 29.
  Definition loc_533 : location_info := LocationInfo file_0 382 12 382 16.
  Definition loc_534 : location_info := LocationInfo file_0 382 12 382 16.
  Definition loc_535 : location_info := LocationInfo file_0 382 33 382 56.
  Definition loc_536 : location_info := LocationInfo file_0 382 33 382 37.
  Definition loc_537 : location_info := LocationInfo file_0 382 33 382 37.
  Definition loc_538 : location_info := LocationInfo file_0 382 41 382 56.
  Definition loc_539 : location_info := LocationInfo file_0 382 41 382 56.
  Definition loc_540 : location_info := LocationInfo file_0 382 41 382 45.
  Definition loc_541 : location_info := LocationInfo file_0 382 41 382 45.
  Definition loc_542 : location_info := LocationInfo file_0 381 1 381 5.
  Definition loc_543 : location_info := LocationInfo file_0 381 1 381 24.
  Definition loc_544 : location_info := LocationInfo file_0 381 1 381 5.
  Definition loc_545 : location_info := LocationInfo file_0 381 1 381 5.
  Definition loc_546 : location_info := LocationInfo file_0 381 9 381 24.
  Definition loc_547 : location_info := LocationInfo file_0 381 10 381 14.
  Definition loc_548 : location_info := LocationInfo file_0 381 18 381 23.
  Definition loc_549 : location_info := LocationInfo file_0 381 18 381 23.
  Definition loc_550 : location_info := LocationInfo file_0 379 20 379 39.
  Definition loc_551 : location_info := LocationInfo file_0 379 20 379 36.
  Definition loc_552 : location_info := LocationInfo file_0 379 20 379 36.
  Definition loc_553 : location_info := LocationInfo file_0 379 37 379 38.
  Definition loc_554 : location_info := LocationInfo file_0 379 37 379 38.
  Definition loc_557 : location_info := LocationInfo file_0 378 1 378 14.
  Definition loc_558 : location_info := LocationInfo file_0 378 2 378 14.
  Definition loc_559 : location_info := LocationInfo file_0 378 3 378 7.
  Definition loc_560 : location_info := LocationInfo file_0 378 3 378 7.
  Definition loc_563 : location_info := LocationInfo file_0 402 1 402 15.
  Definition loc_564 : location_info := LocationInfo file_0 402 15 402 2.
  Definition loc_565 : location_info := LocationInfo file_0 403 1 403 31.
  Definition loc_566 : location_info := LocationInfo file_0 406 1 406 31.
  Definition loc_567 : location_info := LocationInfo file_0 414 1 433 2.
  Definition loc_568 : location_info := LocationInfo file_0 434 1 434 15.
  Definition loc_569 : location_info := LocationInfo file_0 434 15 434 2.
  Definition loc_570 : location_info := LocationInfo file_0 436 1 436 18.
  Definition loc_571 : location_info := LocationInfo file_0 439 1 439 45.
  Definition loc_572 : location_info := LocationInfo file_0 439 1 439 9.
  Definition loc_573 : location_info := LocationInfo file_0 439 1 439 9.
  Definition loc_574 : location_info := LocationInfo file_0 439 10 439 18.
  Definition loc_575 : location_info := LocationInfo file_0 439 11 439 18.
  Definition loc_576 : location_info := LocationInfo file_0 439 11 439 12.
  Definition loc_577 : location_info := LocationInfo file_0 439 11 439 12.
  Definition loc_578 : location_info := LocationInfo file_0 439 20 439 43.
  Definition loc_579 : location_info := LocationInfo file_0 439 21 439 43.
  Definition loc_580 : location_info := LocationInfo file_0 439 21 439 43.
  Definition loc_581 : location_info := LocationInfo file_0 439 21 439 36.
  Definition loc_582 : location_info := LocationInfo file_0 439 21 439 36.
  Definition loc_583 : location_info := LocationInfo file_0 439 21 439 25.
  Definition loc_584 : location_info := LocationInfo file_0 439 21 439 25.
  Definition loc_585 : location_info := LocationInfo file_0 439 37 439 42.
  Definition loc_586 : location_info := LocationInfo file_0 439 37 439 42.
  Definition loc_587 : location_info := LocationInfo file_0 436 1 436 9.
  Definition loc_588 : location_info := LocationInfo file_0 436 1 436 2.
  Definition loc_589 : location_info := LocationInfo file_0 436 1 436 2.
  Definition loc_590 : location_info := LocationInfo file_0 436 12 436 17.
  Definition loc_591 : location_info := LocationInfo file_0 436 12 436 17.
  Definition loc_592 : location_info := LocationInfo file_0 434 1 434 14.
  Definition loc_593 : location_info := LocationInfo file_0 434 2 434 14.
  Definition loc_594 : location_info := LocationInfo file_0 434 3 434 7.
  Definition loc_595 : location_info := LocationInfo file_0 434 3 434 7.
  Definition loc_596 : location_info := LocationInfo file_0 414 30 433 2.
  Definition loc_597 : location_info := LocationInfo file_0 416 2 416 39.
  Definition loc_598 : location_info := LocationInfo file_0 417 2 417 16.
  Definition loc_599 : location_info := LocationInfo file_0 417 16 417 3.
  Definition loc_600 : location_info := LocationInfo file_0 420 2 421 9.
  Definition loc_601 : location_info := LocationInfo file_0 424 2 424 30.
  Definition loc_602 : location_info := LocationInfo file_0 425 2 425 36.
  Definition loc_603 : location_info := LocationInfo file_0 428 2 432 3.
  Definition loc_604 : location_info := LocationInfo file_0 414 1 433 2.
  Definition loc_605 : location_info := LocationInfo file_0 414 21 414 28.
  Definition loc_606 : location_info := LocationInfo file_0 414 21 414 26.
  Definition loc_607 : location_info := LocationInfo file_0 428 17 430 3.
  Definition loc_608 : location_info := LocationInfo file_0 429 3 429 9.
  Definition loc_609 : location_info := LocationInfo file_0 429 3 429 4.
  Definition loc_610 : location_info := LocationInfo file_0 429 7 429 8.
  Definition loc_611 : location_info := LocationInfo file_0 429 7 429 8.
  Definition loc_612 : location_info := LocationInfo file_0 430 9 432 3.
  Definition loc_613 : location_info := LocationInfo file_0 431 3 431 13.
  Definition loc_614 : location_info := LocationInfo file_0 431 3 431 4.
  Definition loc_615 : location_info := LocationInfo file_0 431 7 431 12.
  Definition loc_616 : location_info := LocationInfo file_0 431 7 431 12.
  Definition loc_617 : location_info := LocationInfo file_0 428 6 428 15.
  Definition loc_618 : location_info := LocationInfo file_0 428 6 428 7.
  Definition loc_619 : location_info := LocationInfo file_0 428 6 428 7.
  Definition loc_620 : location_info := LocationInfo file_0 428 10 428 15.
  Definition loc_621 : location_info := LocationInfo file_0 428 10 428 15.
  Definition loc_622 : location_info := LocationInfo file_0 425 2 425 14.
  Definition loc_623 : location_info := LocationInfo file_0 425 2 425 7.
  Definition loc_624 : location_info := LocationInfo file_0 425 2 425 7.
  Definition loc_625 : location_info := LocationInfo file_0 425 17 425 35.
  Definition loc_626 : location_info := LocationInfo file_0 424 2 424 15.
  Definition loc_627 : location_info := LocationInfo file_0 424 2 424 15.
  Definition loc_628 : location_info := LocationInfo file_0 424 16 424 28.
  Definition loc_629 : location_info := LocationInfo file_0 424 17 424 28.
  Definition loc_630 : location_info := LocationInfo file_0 424 17 424 22.
  Definition loc_631 : location_info := LocationInfo file_0 424 17 424 22.
  Definition loc_632 : location_info := LocationInfo file_0 421 3 421 9.
  Definition loc_636 : location_info := LocationInfo file_0 420 6 420 29.
  Definition loc_637 : location_info := LocationInfo file_0 420 6 420 11.
  Definition loc_638 : location_info := LocationInfo file_0 420 6 420 11.
  Definition loc_639 : location_info := LocationInfo file_0 420 15 420 29.
  Definition loc_640 : location_info := LocationInfo file_0 420 33 420 57.
  Definition loc_641 : location_info := LocationInfo file_0 420 33 420 43.
  Definition loc_642 : location_info := LocationInfo file_0 420 33 420 43.
  Definition loc_643 : location_info := LocationInfo file_0 420 44 420 56.
  Definition loc_644 : location_info := LocationInfo file_0 420 45 420 56.
  Definition loc_645 : location_info := LocationInfo file_0 420 45 420 50.
  Definition loc_646 : location_info := LocationInfo file_0 420 45 420 50.
  Definition loc_647 : location_info := LocationInfo file_0 420 61 420 82.
  Definition loc_648 : location_info := LocationInfo file_0 420 61 420 73.
  Definition loc_649 : location_info := LocationInfo file_0 420 61 420 73.
  Definition loc_650 : location_info := LocationInfo file_0 420 61 420 66.
  Definition loc_651 : location_info := LocationInfo file_0 420 61 420 66.
  Definition loc_652 : location_info := LocationInfo file_0 420 77 420 82.
  Definition loc_653 : location_info := LocationInfo file_0 420 77 420 82.
  Definition loc_654 : location_info := LocationInfo file_0 417 2 417 15.
  Definition loc_655 : location_info := LocationInfo file_0 417 3 417 15.
  Definition loc_656 : location_info := LocationInfo file_0 417 4 417 8.
  Definition loc_657 : location_info := LocationInfo file_0 417 4 417 8.
  Definition loc_658 : location_info := LocationInfo file_0 416 2 416 7.
  Definition loc_659 : location_info := LocationInfo file_0 416 10 416 38.
  Definition loc_660 : location_info := LocationInfo file_0 416 10 416 22.
  Definition loc_661 : location_info := LocationInfo file_0 416 10 416 22.
  Definition loc_662 : location_info := LocationInfo file_0 416 23 416 27.
  Definition loc_663 : location_info := LocationInfo file_0 416 23 416 27.
  Definition loc_664 : location_info := LocationInfo file_0 416 29 416 30.
  Definition loc_665 : location_info := LocationInfo file_0 416 29 416 30.
  Definition loc_666 : location_info := LocationInfo file_0 416 32 416 37.
  Definition loc_667 : location_info := LocationInfo file_0 416 32 416 37.
  Definition loc_668 : location_info := LocationInfo file_0 414 8 414 19.
  Definition loc_669 : location_info := LocationInfo file_0 414 8 414 13.
  Definition loc_670 : location_info := LocationInfo file_0 414 8 414 13.
  Definition loc_671 : location_info := LocationInfo file_0 414 16 414 19.
  Definition loc_672 : location_info := LocationInfo file_0 406 1 406 9.
  Definition loc_673 : location_info := LocationInfo file_0 406 1 406 2.
  Definition loc_674 : location_info := LocationInfo file_0 406 1 406 2.
  Definition loc_675 : location_info := LocationInfo file_0 406 12 406 30.
  Definition loc_676 : location_info := LocationInfo file_0 403 22 403 30.
  Definition loc_677 : location_info := LocationInfo file_0 403 22 403 30.
  Definition loc_678 : location_info := LocationInfo file_0 403 22 403 23.
  Definition loc_679 : location_info := LocationInfo file_0 403 22 403 23.
  Definition loc_682 : location_info := LocationInfo file_0 402 1 402 14.
  Definition loc_683 : location_info := LocationInfo file_0 402 2 402 14.
  Definition loc_684 : location_info := LocationInfo file_0 402 3 402 7.
  Definition loc_685 : location_info := LocationInfo file_0 402 3 402 7.
  Definition loc_688 : location_info := LocationInfo file_0 473 1 474 24.
  Definition loc_689 : location_info := LocationInfo file_0 476 1 476 25.
  Definition loc_690 : location_info := LocationInfo file_0 479 1 484 2.
  Definition loc_691 : location_info := LocationInfo file_0 486 1 486 17.
  Definition loc_692 : location_info := LocationInfo file_0 488 1 488 10.
  Definition loc_693 : location_info := LocationInfo file_0 488 8 488 9.
  Definition loc_694 : location_info := LocationInfo file_0 488 8 488 9.
  Definition loc_695 : location_info := LocationInfo file_0 486 1 486 12.
  Definition loc_696 : location_info := LocationInfo file_0 486 1 486 2.
  Definition loc_697 : location_info := LocationInfo file_0 486 1 486 2.
  Definition loc_698 : location_info := LocationInfo file_0 486 15 486 16.
  Definition loc_699 : location_info := LocationInfo file_0 479 1 484 2.
  Definition loc_700 : location_info := LocationInfo file_0 479 26 484 2.
  Definition loc_701 : location_info := LocationInfo file_0 480 2 480 13.
  Definition loc_702 : location_info := LocationInfo file_0 481 2 481 42.
  Definition loc_703 : location_info := LocationInfo file_0 482 2 482 26.
  Definition loc_704 : location_info := LocationInfo file_0 483 2 483 62.
  Definition loc_705 : location_info := LocationInfo file_0 479 1 484 2.
  Definition loc_706 : location_info := LocationInfo file_0 479 1 484 2.
  Definition loc_707 : location_info := LocationInfo file_0 483 2 483 15.
  Definition loc_708 : location_info := LocationInfo file_0 483 2 483 15.
  Definition loc_709 : location_info := LocationInfo file_0 483 16 483 28.
  Definition loc_710 : location_info := LocationInfo file_0 483 17 483 28.
  Definition loc_711 : location_info := LocationInfo file_0 483 17 483 22.
  Definition loc_712 : location_info := LocationInfo file_0 483 17 483 22.
  Definition loc_713 : location_info := LocationInfo file_0 483 30 483 60.
  Definition loc_714 : location_info := LocationInfo file_0 483 31 483 60.
  Definition loc_715 : location_info := LocationInfo file_0 483 31 483 60.
  Definition loc_716 : location_info := LocationInfo file_0 483 31 483 46.
  Definition loc_717 : location_info := LocationInfo file_0 483 31 483 46.
  Definition loc_718 : location_info := LocationInfo file_0 483 31 483 35.
  Definition loc_719 : location_info := LocationInfo file_0 483 31 483 35.
  Definition loc_720 : location_info := LocationInfo file_0 483 47 483 59.
  Definition loc_721 : location_info := LocationInfo file_0 483 47 483 59.
  Definition loc_722 : location_info := LocationInfo file_0 483 47 483 52.
  Definition loc_723 : location_info := LocationInfo file_0 483 47 483 52.
  Definition loc_724 : location_info := LocationInfo file_0 482 2 482 14.
  Definition loc_725 : location_info := LocationInfo file_0 482 2 482 7.
  Definition loc_726 : location_info := LocationInfo file_0 482 2 482 7.
  Definition loc_727 : location_info := LocationInfo file_0 482 17 482 25.
  Definition loc_728 : location_info := LocationInfo file_0 482 17 482 25.
  Definition loc_729 : location_info := LocationInfo file_0 482 17 482 18.
  Definition loc_730 : location_info := LocationInfo file_0 482 17 482 18.
  Definition loc_731 : location_info := LocationInfo file_0 481 2 481 7.
  Definition loc_732 : location_info := LocationInfo file_0 481 10 481 41.
  Definition loc_733 : location_info := LocationInfo file_0 481 10 481 22.
  Definition loc_734 : location_info := LocationInfo file_0 481 10 481 22.
  Definition loc_735 : location_info := LocationInfo file_0 481 23 481 27.
  Definition loc_736 : location_info := LocationInfo file_0 481 23 481 27.
  Definition loc_737 : location_info := LocationInfo file_0 481 29 481 30.
  Definition loc_738 : location_info := LocationInfo file_0 481 29 481 30.
  Definition loc_739 : location_info := LocationInfo file_0 481 32 481 40.
  Definition loc_740 : location_info := LocationInfo file_0 481 32 481 40.
  Definition loc_741 : location_info := LocationInfo file_0 481 32 481 33.
  Definition loc_742 : location_info := LocationInfo file_0 481 32 481 33.
  Definition loc_743 : location_info := LocationInfo file_0 480 2 480 10.
  Definition loc_744 : location_info := LocationInfo file_0 480 2 480 3.
  Definition loc_745 : location_info := LocationInfo file_0 480 2 480 3.
  Definition loc_746 : location_info := LocationInfo file_0 479 8 479 24.
  Definition loc_747 : location_info := LocationInfo file_0 479 8 479 16.
  Definition loc_748 : location_info := LocationInfo file_0 479 8 479 16.
  Definition loc_749 : location_info := LocationInfo file_0 479 8 479 9.
  Definition loc_750 : location_info := LocationInfo file_0 479 8 479 9.
  Definition loc_751 : location_info := LocationInfo file_0 479 19 479 24.
  Definition loc_752 : location_info := LocationInfo file_0 479 19 479 24.
  Definition loc_753 : location_info := LocationInfo file_0 476 1 476 14.
  Definition loc_754 : location_info := LocationInfo file_0 476 1 476 14.
  Definition loc_755 : location_info := LocationInfo file_0 476 15 476 23.
  Definition loc_756 : location_info := LocationInfo file_0 476 16 476 23.
  Definition loc_757 : location_info := LocationInfo file_0 476 16 476 17.
  Definition loc_758 : location_info := LocationInfo file_0 476 16 476 17.
  Definition loc_759 : location_info := LocationInfo file_0 474 2 474 24.
  Definition loc_760 : location_info := LocationInfo file_0 474 9 474 23.
  Definition loc_763 : location_info := LocationInfo file_0 473 5 473 35.
  Definition loc_764 : location_info := LocationInfo file_0 473 5 473 13.
  Definition loc_765 : location_info := LocationInfo file_0 473 5 473 13.
  Definition loc_766 : location_info := LocationInfo file_0 473 5 473 6.
  Definition loc_767 : location_info := LocationInfo file_0 473 5 473 6.
  Definition loc_768 : location_info := LocationInfo file_0 473 17 473 35.
  Definition loc_769 : location_info := LocationInfo file_0 473 39 473 55.
  Definition loc_770 : location_info := LocationInfo file_0 473 39 473 47.
  Definition loc_771 : location_info := LocationInfo file_0 473 39 473 47.
  Definition loc_772 : location_info := LocationInfo file_0 473 39 473 40.
  Definition loc_773 : location_info := LocationInfo file_0 473 39 473 40.
  Definition loc_774 : location_info := LocationInfo file_0 473 50 473 55.
  Definition loc_775 : location_info := LocationInfo file_0 473 50 473 55.
  Definition loc_778 : location_info := LocationInfo file_0 495 6 495 11.
  Definition loc_779 : location_info := LocationInfo file_0 495 1 496 112.
  Definition loc_780 : location_info := LocationInfo file_0 495 1 496 112.
  Definition loc_781 : location_info := LocationInfo file_0 496 2 496 112.
  Definition loc_782 : location_info := LocationInfo file_0 495 1 496 112.
  Definition loc_783 : location_info := LocationInfo file_0 495 34 495 37.
  Definition loc_784 : location_info := LocationInfo file_0 495 34 495 35.
  Definition loc_785 : location_info := LocationInfo file_0 496 2 496 12.
  Definition loc_786 : location_info := LocationInfo file_0 496 2 496 12.
  Definition loc_787 : location_info := LocationInfo file_0 496 13 496 110.
  Definition loc_788 : location_info := LocationInfo file_0 496 13 496 98.
  Definition loc_789 : location_info := LocationInfo file_0 496 30 496 98.
  Definition loc_790 : location_info := LocationInfo file_0 496 39 496 97.
  Definition loc_791 : location_info := LocationInfo file_0 496 40 496 74.
  Definition loc_792 : location_info := LocationInfo file_0 496 53 496 74.
  Definition loc_793 : location_info := LocationInfo file_0 496 54 496 70.
  Definition loc_794 : location_info := LocationInfo file_0 496 54 496 70.
  Definition loc_795 : location_info := LocationInfo file_0 496 71 496 72.
  Definition loc_796 : location_info := LocationInfo file_0 496 71 496 72.
  Definition loc_797 : location_info := LocationInfo file_0 496 77 496 96.
  Definition loc_798 : location_info := LocationInfo file_0 496 77 496 96.
  Definition loc_799 : location_info := LocationInfo file_0 496 101 496 110.
  Definition loc_800 : location_info := LocationInfo file_0 496 102 496 103.
  Definition loc_801 : location_info := LocationInfo file_0 496 102 496 103.
  Definition loc_802 : location_info := LocationInfo file_0 496 107 496 109.
  Definition loc_803 : location_info := LocationInfo file_0 495 13 495 32.
  Definition loc_804 : location_info := LocationInfo file_0 495 13 495 14.
  Definition loc_805 : location_info := LocationInfo file_0 495 13 495 14.
  Definition loc_806 : location_info := LocationInfo file_0 495 17 495 32.
  Definition loc_807 : location_info := LocationInfo file_0 495 18 495 19.
  Definition loc_808 : location_info := LocationInfo file_0 495 23 495 31.
  Definition loc_809 : location_info := LocationInfo file_0 495 23 495 31.
  Definition loc_810 : location_info := LocationInfo file_0 495 23 495 24.
  Definition loc_811 : location_info := LocationInfo file_0 495 23 495 24.
  Definition loc_812 : location_info := LocationInfo file_0 495 6 495 7.
  Definition loc_813 : location_info := LocationInfo file_0 495 10 495 11.
  Definition loc_816 : location_info := LocationInfo file_0 504 1 504 24.
  Definition loc_817 : location_info := LocationInfo file_0 508 1 509 6.
  Definition loc_818 : location_info := LocationInfo file_0 510 1 511 24.
  Definition loc_819 : location_info := LocationInfo file_0 514 1 514 99.
  Definition loc_820 : location_info := LocationInfo file_0 515 1 515 40.
  Definition loc_821 : location_info := LocationInfo file_0 517 1 518 20.
  Definition loc_822 : location_info := LocationInfo file_0 520 1 520 10.
  Definition loc_823 : location_info := LocationInfo file_0 520 8 520 9.
  Definition loc_824 : location_info := LocationInfo file_0 520 8 520 9.
  Definition loc_825 : location_info := LocationInfo file_0 518 2 518 20.
  Definition loc_826 : location_info := LocationInfo file_0 518 2 518 16.
  Definition loc_827 : location_info := LocationInfo file_0 518 2 518 16.
  Definition loc_828 : location_info := LocationInfo file_0 518 17 518 18.
  Definition loc_829 : location_info := LocationInfo file_0 518 17 518 18.
  Definition loc_831 : location_info := LocationInfo file_0 517 5 517 13.
  Definition loc_832 : location_info := LocationInfo file_0 517 5 517 9.
  Definition loc_833 : location_info := LocationInfo file_0 517 5 517 9.
  Definition loc_834 : location_info := LocationInfo file_0 517 12 517 13.
  Definition loc_835 : location_info := LocationInfo file_0 515 1 515 2.
  Definition loc_836 : location_info := LocationInfo file_0 515 5 515 39.
  Definition loc_837 : location_info := LocationInfo file_0 515 5 515 23.
  Definition loc_838 : location_info := LocationInfo file_0 515 5 515 23.
  Definition loc_839 : location_info := LocationInfo file_0 515 24 515 28.
  Definition loc_840 : location_info := LocationInfo file_0 515 24 515 28.
  Definition loc_841 : location_info := LocationInfo file_0 515 30 515 31.
  Definition loc_842 : location_info := LocationInfo file_0 515 30 515 31.
  Definition loc_843 : location_info := LocationInfo file_0 515 33 515 38.
  Definition loc_844 : location_info := LocationInfo file_0 515 33 515 38.
  Definition loc_845 : location_info := LocationInfo file_0 514 1 514 2.
  Definition loc_846 : location_info := LocationInfo file_0 514 5 514 98.
  Definition loc_847 : location_info := LocationInfo file_0 514 24 514 98.
  Definition loc_848 : location_info := LocationInfo file_0 514 26 514 63.
  Definition loc_849 : location_info := LocationInfo file_0 514 34 514 63.
  Definition loc_850 : location_info := LocationInfo file_0 514 34 514 63.
  Definition loc_851 : location_info := LocationInfo file_0 514 35 514 56.
  Definition loc_852 : location_info := LocationInfo file_0 514 37 514 55.
  Definition loc_853 : location_info := LocationInfo file_0 514 37 514 55.
  Definition loc_854 : location_info := LocationInfo file_0 514 37 514 52.
  Definition loc_855 : location_info := LocationInfo file_0 514 37 514 52.
  Definition loc_856 : location_info := LocationInfo file_0 514 37 514 41.
  Definition loc_857 : location_info := LocationInfo file_0 514 37 514 41.
  Definition loc_858 : location_info := LocationInfo file_0 514 53 514 54.
  Definition loc_859 : location_info := LocationInfo file_0 514 53 514 54.
  Definition loc_860 : location_info := LocationInfo file_0 514 66 514 96.
  Definition loc_861 : location_info := LocationInfo file_0 511 2 511 24.
  Definition loc_862 : location_info := LocationInfo file_0 511 9 511 23.
  Definition loc_864 : location_info := LocationInfo file_0 510 5 510 12.
  Definition loc_865 : location_info := LocationInfo file_0 510 5 510 6.
  Definition loc_866 : location_info := LocationInfo file_0 510 5 510 6.
  Definition loc_867 : location_info := LocationInfo file_0 510 9 510 12.
  Definition loc_868 : location_info := LocationInfo file_0 508 1 509 6.
  Definition loc_869 : location_info := LocationInfo file_0 509 2 509 6.
  Definition loc_870 : location_info := LocationInfo file_0 508 1 509 6.
  Definition loc_871 : location_info := LocationInfo file_0 508 1 509 6.
  Definition loc_872 : location_info := LocationInfo file_0 509 2 509 3.
  Definition loc_874 : location_info := LocationInfo file_0 508 8 508 16.
  Definition loc_875 : location_info := LocationInfo file_0 508 8 508 9.
  Definition loc_876 : location_info := LocationInfo file_0 508 8 508 9.
  Definition loc_877 : location_info := LocationInfo file_0 508 13 508 16.
  Definition loc_878 : location_info := LocationInfo file_0 508 20 508 51.
  Definition loc_879 : location_info := LocationInfo file_0 508 20 508 30.
  Definition loc_880 : location_info := LocationInfo file_0 508 20 508 30.
  Definition loc_881 : location_info := LocationInfo file_0 508 31 508 50.
  Definition loc_882 : location_info := LocationInfo file_0 508 32 508 50.
  Definition loc_883 : location_info := LocationInfo file_0 508 32 508 50.
  Definition loc_884 : location_info := LocationInfo file_0 508 32 508 47.
  Definition loc_885 : location_info := LocationInfo file_0 508 32 508 47.
  Definition loc_886 : location_info := LocationInfo file_0 508 32 508 36.
  Definition loc_887 : location_info := LocationInfo file_0 508 32 508 36.
  Definition loc_888 : location_info := LocationInfo file_0 508 48 508 49.
  Definition loc_889 : location_info := LocationInfo file_0 508 48 508 49.
  Definition loc_890 : location_info := LocationInfo file_0 504 18 504 23.
  Definition loc_891 : location_info := LocationInfo file_0 504 18 504 23.

  (* Definition of struct [atomic_flag]. *)
  Program Definition struct_atomic_flag := {|
    sl_members := [
      (Some "_Value", it_layout bool_it)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [spinlock]. *)
  Program Definition struct_spinlock := {|
    sl_members := [
      (Some "lock", it_layout bool_it)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [list_head]. *)
  Program Definition struct_list_head := {|
    sl_members := [
      (Some "next", void*);
      (Some "prev", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [hyp_memblock_region]. *)
  Program Definition struct_hyp_memblock_region := {|
    sl_members := [
      (Some "start", it_layout u64);
      (Some "end", it_layout u64)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [hyp_page]. *)
  Program Definition struct_hyp_page := {|
    sl_members := [
      (Some "refcount", it_layout u32);
      (Some "order", it_layout u32);
      (Some "pool", void*);
      (Some "node", layout_of struct_list_head)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [hyp_pool]. *)
  Program Definition struct_hyp_pool := {|
    sl_members := [
      (Some "lock", layout_of struct_spinlock);
      (None, Layout 7%nat 0%nat);
      (Some "free_area", mk_array_layout (layout_of struct_list_head) 12);
      (Some "range_start", it_layout u64);
      (Some "range_end", it_layout u64)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [hyp_panic]. *)
  Definition impl_hyp_panic : function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        assert: (LocInfoE loc_3 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_3 (i2v 0 i32)))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [__list_add_valid]. *)
  Definition impl___list_add_valid : function := {|
    f_args := [
      ("new", void*);
      ("prev", void*);
      ("next", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_6 ;
        Return (LocInfoE loc_7 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_7 (i2v 1 i32))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [__list_del_entry_valid]. *)
  Definition impl___list_del_entry_valid : function := {|
    f_args := [
      ("entry", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_10 ;
        Return (LocInfoE loc_11 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_11 (i2v 1 i32))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [INIT_LIST_HEAD]. *)
  Definition impl_INIT_LIST_HEAD : function := {|
    f_args := [
      ("list", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_14 ;
        LocInfoE loc_21 ((LocInfoE loc_22 (!{void*} (LocInfoE loc_23 ("list")))) at{struct_list_head} "next") <-{ void* }
          LocInfoE loc_24 (use{void*} (LocInfoE loc_25 ("list"))) ;
        locinfo: loc_15 ;
        LocInfoE loc_16 ((LocInfoE loc_17 (!{void*} (LocInfoE loc_18 ("list")))) at{struct_list_head} "prev") <-{ void* }
          LocInfoE loc_19 (use{void*} (LocInfoE loc_20 ("list"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [__list_add]. *)
  Definition impl___list_add (global___list_add_valid : loc): function := {|
    f_args := [
      ("new", void*);
      ("prev", void*);
      ("next", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_56 ;
        if: LocInfoE loc_56 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_56 ((i2v 0 i32) ={IntOp i32, IntOp i32} (LocInfoE loc_58 (UnOp (CastOp $ IntOp i32) (IntOp bool_it) (LocInfoE loc_58 (Call (LocInfoE loc_60 (global___list_add_valid)) [@{expr} LocInfoE loc_61 (use{void*} (LocInfoE loc_62 ("new"))) ;
            LocInfoE loc_63 (use{void*} (LocInfoE loc_64 ("prev"))) ;
            LocInfoE loc_65 (use{void*} (LocInfoE loc_66 ("next"))) ])))))))
        then
        locinfo: loc_53 ;
          Goto "#2"
        else
        locinfo: loc_29 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_29 ;
        LocInfoE loc_48 ((LocInfoE loc_49 (!{void*} (LocInfoE loc_50 ("next")))) at{struct_list_head} "prev") <-{ void* }
          LocInfoE loc_51 (use{void*} (LocInfoE loc_52 ("new"))) ;
        locinfo: loc_30 ;
        LocInfoE loc_43 ((LocInfoE loc_44 (!{void*} (LocInfoE loc_45 ("new")))) at{struct_list_head} "next") <-{ void* }
          LocInfoE loc_46 (use{void*} (LocInfoE loc_47 ("next"))) ;
        locinfo: loc_31 ;
        LocInfoE loc_38 ((LocInfoE loc_39 (!{void*} (LocInfoE loc_40 ("new")))) at{struct_list_head} "prev") <-{ void* }
          LocInfoE loc_41 (use{void*} (LocInfoE loc_42 ("prev"))) ;
        locinfo: loc_32 ;
        LocInfoE loc_33 ((LocInfoE loc_34 (!{void*} (LocInfoE loc_35 ("prev")))) at{struct_list_head} "next") <-{ void* }
          LocInfoE loc_36 (use{void*} (LocInfoE loc_37 ("new"))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_53 ;
        Return (VOID)
      ]> $
      <[ "#3" :=
        locinfo: loc_29 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [list_add]. *)
  Definition impl_list_add (global___list_add : loc): function := {|
    f_args := [
      ("new", void*);
      ("head", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_69 ;
        expr: (LocInfoE loc_69 (Call (LocInfoE loc_71 (global___list_add)) [@{expr} LocInfoE loc_72 (use{void*} (LocInfoE loc_73 ("new"))) ;
        LocInfoE loc_74 (use{void*} (LocInfoE loc_75 ("head"))) ;
        LocInfoE loc_76 (use{void*} (LocInfoE loc_77 ((LocInfoE loc_78 (!{void*} (LocInfoE loc_79 ("head")))) at{struct_list_head} "next"))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [list_add_tail]. *)
  Definition impl_list_add_tail (global___list_add : loc): function := {|
    f_args := [
      ("new", void*);
      ("head", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_82 ;
        expr: (LocInfoE loc_82 (Call (LocInfoE loc_84 (global___list_add)) [@{expr} LocInfoE loc_85 (use{void*} (LocInfoE loc_86 ("new"))) ;
        LocInfoE loc_87 (use{void*} (LocInfoE loc_88 ((LocInfoE loc_89 (!{void*} (LocInfoE loc_90 ("head")))) at{struct_list_head} "prev"))) ;
        LocInfoE loc_91 (use{void*} (LocInfoE loc_92 ("head"))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [__list_del]. *)
  Definition impl___list_del : function := {|
    f_args := [
      ("prev", void*);
      ("next", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_95 ;
        LocInfoE loc_102 ((LocInfoE loc_103 (!{void*} (LocInfoE loc_104 ("next")))) at{struct_list_head} "prev") <-{ void* }
          LocInfoE loc_105 (use{void*} (LocInfoE loc_106 ("prev"))) ;
        locinfo: loc_96 ;
        LocInfoE loc_97 ((LocInfoE loc_98 (!{void*} (LocInfoE loc_99 ("prev")))) at{struct_list_head} "next") <-{ void* }
          LocInfoE loc_100 (use{void*} (LocInfoE loc_101 ("next"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [__list_del_entry]. *)
  Definition impl___list_del_entry (global___list_del global___list_del_entry_valid : loc): function := {|
    f_args := [
      ("entry", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_124 ;
        if: LocInfoE loc_124 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_124 ((i2v 0 i32) ={IntOp i32, IntOp i32} (LocInfoE loc_126 (UnOp (CastOp $ IntOp i32) (IntOp bool_it) (LocInfoE loc_126 (Call (LocInfoE loc_128 (global___list_del_entry_valid)) [@{expr} LocInfoE loc_129 (use{void*} (LocInfoE loc_130 ("entry"))) ])))))))
        then
        locinfo: loc_121 ;
          Goto "#2"
        else
        locinfo: loc_110 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_110 ;
        expr: (LocInfoE loc_110 (Call (LocInfoE loc_112 (global___list_del)) [@{expr} LocInfoE loc_113 (use{void*} (LocInfoE loc_114 ((LocInfoE loc_115 (!{void*} (LocInfoE loc_116 ("entry")))) at{struct_list_head} "prev"))) ;
        LocInfoE loc_117 (use{void*} (LocInfoE loc_118 ((LocInfoE loc_119 (!{void*} (LocInfoE loc_120 ("entry")))) at{struct_list_head} "next"))) ])) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_121 ;
        Return (VOID)
      ]> $
      <[ "#3" :=
        locinfo: loc_110 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [list_del_init]. *)
  Definition impl_list_del_init (global_INIT_LIST_HEAD global___list_del_entry : loc): function := {|
    f_args := [
      ("entry", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_133 ;
        expr: (LocInfoE loc_133 (Call (LocInfoE loc_140 (global___list_del_entry)) [@{expr} LocInfoE loc_141 (use{void*} (LocInfoE loc_142 ("entry"))) ])) ;
        locinfo: loc_134 ;
        expr: (LocInfoE loc_134 (Call (LocInfoE loc_136 (global_INIT_LIST_HEAD)) [@{expr} LocInfoE loc_137 (use{void*} (LocInfoE loc_138 ("entry"))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [list_empty]. *)
  Definition impl_list_empty : function := {|
    f_args := [
      ("head", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_145 ;
        Return (LocInfoE loc_146 ((LocInfoE loc_147 (use{void*} (LocInfoE loc_148 ((LocInfoE loc_149 (!{void*} (LocInfoE loc_150 ("head")))) at{struct_list_head} "next")))) ={PtrOp, PtrOp} (LocInfoE loc_151 (use{void*} (LocInfoE loc_152 ("head"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_phys_to_virt]. *)
  Definition impl_hyp_phys_to_virt (global_hyp_physvirt_offset : loc): function := {|
    f_args := [
      ("phys", it_layout u64)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_155 ;
        Return (LocInfoE loc_156 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_157 ((LocInfoE loc_158 (UnOp (CastOp $ IntOp u64) (IntOp u64) (LocInfoE loc_159 (use{it_layout u64} (LocInfoE loc_160 ("phys")))))) -{IntOp u64, IntOp u64} (LocInfoE loc_161 (UnOp (CastOp $ IntOp u64) (IntOp i64) (LocInfoE loc_161 (use{it_layout i64} (LocInfoE loc_162 (global_hyp_physvirt_offset))))))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_virt_to_phys]. *)
  Definition impl_hyp_virt_to_phys (global_hyp_physvirt_offset : loc): function := {|
    f_args := [
      ("addr", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_165 ;
        Return (LocInfoE loc_166 ((LocInfoE loc_167 (UnOp (CastOp $ IntOp u64) (PtrOp) (LocInfoE loc_168 (use{void*} (LocInfoE loc_169 ("addr")))))) +{IntOp u64, IntOp u64} (LocInfoE loc_170 (UnOp (CastOp $ IntOp u64) (IntOp i64) (LocInfoE loc_170 (use{it_layout i64} (LocInfoE loc_171 (global_hyp_physvirt_offset))))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_phys_to_page]. *)
  Definition impl_hyp_phys_to_page (global___hyp_vmemmap : loc): function := {|
    f_args := [
      ("phys", it_layout u64)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_174 ;
        Return (LocInfoE loc_175 ((LocInfoE loc_176 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_177 (use{void*} (LocInfoE loc_178 (global___hyp_vmemmap)))))) at_offset{layout_of struct_hyp_page, PtrOp, IntOp u64} (LocInfoE loc_179 ((LocInfoE loc_180 (use{it_layout u64} (LocInfoE loc_181 ("phys")))) >>{IntOp u64, IntOp u64} (LocInfoE loc_182 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_182 (i2v 12 i32))))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_page_to_phys]. *)
  Definition impl_hyp_page_to_phys (global___hyp_vmemmap : loc): function := {|
    f_args := [
      ("page", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_185 ;
        Return (LocInfoE loc_186 ((LocInfoE loc_187 (UnOp (CastOp $ IntOp u64) (IntOp ssize_t) (LocInfoE loc_188 ((LocInfoE loc_189 (use{void*} (LocInfoE loc_190 ("page")))) -{PtrOp, PtrOp} (LocInfoE loc_191 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_192 (use{void*} (LocInfoE loc_193 (global___hyp_vmemmap)))))))))) <<{IntOp u64, IntOp u64} (LocInfoE loc_194 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_194 (i2v 12 i32))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_page_count]. *)
  Definition impl_hyp_page_count (global_hyp_physvirt_offset global_hyp_phys_to_page : loc): function := {|
    f_args := [
      ("addr", void*)
    ];
    f_local_vars := [
      ("p", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "p" <-{ void* }
          LocInfoE loc_203 (Call (LocInfoE loc_205 (global_hyp_phys_to_page)) [@{expr} LocInfoE loc_206 ((LocInfoE loc_207 (UnOp (CastOp $ IntOp u64) (PtrOp) (LocInfoE loc_208 (use{void*} (LocInfoE loc_209 ("addr")))))) +{IntOp u64, IntOp u64} (LocInfoE loc_210 (UnOp (CastOp $ IntOp u64) (IntOp i64) (LocInfoE loc_210 (use{it_layout i64} (LocInfoE loc_211 (global_hyp_physvirt_offset))))))) ]) ;
        locinfo: loc_198 ;
        Return (LocInfoE loc_199 (UnOp (CastOp $ IntOp i32) (IntOp u32) (LocInfoE loc_199 (use{it_layout u32} (LocInfoE loc_200 ((LocInfoE loc_201 (!{void*} (LocInfoE loc_202 ("p")))) at{struct_hyp_page} "refcount"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_alloc_pages]. *)
  Definition impl_hyp_alloc_pages (global_hyp_physvirt_offset global___hyp_alloc_pages global_hyp_page_to_phys global_sl_lock global_sl_unlock : loc): function := {|
    f_args := [
      ("pool", void*);
      ("mask", it_layout u64);
      ("order", it_layout u32)
    ];
    f_local_vars := [
      ("p", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_216 ;
        expr: (LocInfoE loc_216 (Call (LocInfoE loc_251 (global_sl_lock)) [@{expr} LocInfoE loc_252 (&(LocInfoE loc_253 ((LocInfoE loc_254 (!{void*} (LocInfoE loc_255 ("pool")))) at{struct_hyp_pool} "lock"))) ])) ;
        locinfo: loc_217 ;
        LocInfoE loc_240 ("p") <-{ void* }
          LocInfoE loc_241 (Call (LocInfoE loc_243 (global___hyp_alloc_pages)) [@{expr} LocInfoE loc_244 (use{void*} (LocInfoE loc_245 ("pool"))) ;
          LocInfoE loc_246 (use{it_layout u64} (LocInfoE loc_247 ("mask"))) ;
          LocInfoE loc_248 (use{it_layout u32} (LocInfoE loc_249 ("order"))) ]) ;
        locinfo: loc_218 ;
        expr: (LocInfoE loc_218 (Call (LocInfoE loc_235 (global_sl_unlock)) [@{expr} LocInfoE loc_236 (AnnotExpr 1%nat LockA (LocInfoE loc_236 (&(LocInfoE loc_237 ((LocInfoE loc_238 (!{void*} (LocInfoE loc_239 ("pool")))) at{struct_hyp_pool} "lock"))))) ])) ;
        locinfo: loc_219 ;
        Return (LocInfoE loc_220 (IfE (PtrOp)
               (LocInfoE loc_221 (use{void*} (LocInfoE loc_222 ("p"))))
               (LocInfoE loc_223 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_224 ((LocInfoE loc_225 (UnOp (CastOp $ IntOp u64) (IntOp u64) (LocInfoE loc_226 (Call (LocInfoE loc_228 (global_hyp_page_to_phys)) [@{expr} LocInfoE loc_229 (use{void*} (LocInfoE loc_230 ("p"))) ])))) -{IntOp u64, IntOp u64} (LocInfoE loc_231 (UnOp (CastOp $ IntOp u64) (IntOp i64) (LocInfoE loc_231 (use{it_layout i64} (LocInfoE loc_232 (global_hyp_physvirt_offset))))))))))
               (LocInfoE loc_233 (NULL))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_get_page]. *)
  Definition impl_hyp_get_page (global_hyp_physvirt_offset global_hyp_phys_to_page global_sl_lock global_sl_unlock : loc): function := {|
    f_args := [
      ("addr", void*)
    ];
    f_local_vars := [
      ("pool", void*);
      ("p", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "p" <-{ void* }
          LocInfoE loc_285 (Call (LocInfoE loc_287 (global_hyp_phys_to_page)) [@{expr} LocInfoE loc_288 ((LocInfoE loc_289 (UnOp (CastOp $ IntOp u64) (PtrOp) (LocInfoE loc_290 (use{void*} (LocInfoE loc_291 ("addr")))))) +{IntOp u64, IntOp u64} (LocInfoE loc_292 (UnOp (CastOp $ IntOp u64) (IntOp i64) (LocInfoE loc_292 (use{it_layout i64} (LocInfoE loc_293 (global_hyp_physvirt_offset))))))) ]) ;
        "pool" <-{ void* }
          LocInfoE loc_278 (use{void*} (LocInfoE loc_279 ((LocInfoE loc_280 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_281 (!{void*} (LocInfoE loc_282 ("p")))))) at{struct_hyp_page} "pool"))) ;
        locinfo: loc_260 ;
        expr: (LocInfoE loc_260 (Call (LocInfoE loc_273 (global_sl_lock)) [@{expr} LocInfoE loc_274 (&(LocInfoE loc_275 ((LocInfoE loc_276 (!{void*} (LocInfoE loc_277 ("pool")))) at{struct_hyp_pool} "lock"))) ])) ;
        locinfo: loc_261 ;
        LocInfoE loc_269 ((LocInfoE loc_270 (!{void*} (LocInfoE loc_271 ("p")))) at{struct_hyp_page} "refcount") <-{ it_layout u32 }
          LocInfoE loc_261 ((LocInfoE loc_261 (use{it_layout u32} (LocInfoE loc_269 ((LocInfoE loc_270 (!{void*} (LocInfoE loc_271 ("p")))) at{struct_hyp_page} "refcount")))) +{IntOp u32, IntOp u32} (LocInfoE loc_261 (i2v 1 u32))) ;
        locinfo: loc_262 ;
        expr: (LocInfoE loc_262 (Call (LocInfoE loc_264 (global_sl_unlock)) [@{expr} LocInfoE loc_265 (AnnotExpr 1%nat LockA (LocInfoE loc_265 (&(LocInfoE loc_266 ((LocInfoE loc_267 (!{void*} (LocInfoE loc_268 ("pool")))) at{struct_hyp_pool} "lock"))))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_put_page]. *)
  Definition impl_hyp_put_page (global_hyp_physvirt_offset global___hyp_attach_page global_hyp_panic global_hyp_phys_to_page global_sl_lock global_sl_unlock : loc): function := {|
    f_args := [
      ("addr", void*)
    ];
    f_local_vars := [
      ("pool", void*);
      ("p", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "p" <-{ void* }
          LocInfoE loc_351 (Call (LocInfoE loc_353 (global_hyp_phys_to_page)) [@{expr} LocInfoE loc_354 ((LocInfoE loc_355 (UnOp (CastOp $ IntOp u64) (PtrOp) (LocInfoE loc_356 (use{void*} (LocInfoE loc_357 ("addr")))))) +{IntOp u64, IntOp u64} (LocInfoE loc_358 (UnOp (CastOp $ IntOp u64) (IntOp i64) (LocInfoE loc_358 (use{it_layout i64} (LocInfoE loc_359 (global_hyp_physvirt_offset))))))) ]) ;
        "pool" <-{ void* }
          LocInfoE loc_344 (use{void*} (LocInfoE loc_345 ((LocInfoE loc_346 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_347 (!{void*} (LocInfoE loc_348 ("p")))))) at{struct_hyp_page} "pool"))) ;
        locinfo: loc_300 ;
        expr: (LocInfoE loc_300 (Call (LocInfoE loc_339 (global_sl_lock)) [@{expr} LocInfoE loc_340 (&(LocInfoE loc_341 ((LocInfoE loc_342 (!{void*} (LocInfoE loc_343 ("pool")))) at{struct_hyp_pool} "lock"))) ])) ;
        locinfo: loc_332 ;
        if: LocInfoE loc_332 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_332 ((UnOp (CastOp $ IntOp u32) (IntOp i32) (i2v 0 i32)) ={IntOp u32, IntOp u32} (LocInfoE loc_334 (use{it_layout u32} (LocInfoE loc_335 ((LocInfoE loc_336 (!{void*} (LocInfoE loc_337 ("p")))) at{struct_hyp_page} "refcount")))))))
        then
        locinfo: loc_328 ;
          Goto "#5"
        else
        locinfo: loc_302 ;
          Goto "#6"
      ]> $
      <[ "#1" :=
        locinfo: loc_302 ;
        LocInfoE loc_325 ((LocInfoE loc_326 (!{void*} (LocInfoE loc_327 ("p")))) at{struct_hyp_page} "refcount") <-{ it_layout u32 }
          LocInfoE loc_302 ((LocInfoE loc_302 (use{it_layout u32} (LocInfoE loc_325 ((LocInfoE loc_326 (!{void*} (LocInfoE loc_327 ("p")))) at{struct_hyp_page} "refcount")))) -{IntOp u32, IntOp u32} (LocInfoE loc_302 (i2v 1 u32))) ;
        locinfo: loc_319 ;
        if: LocInfoE loc_319 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_319 ((UnOp (CastOp $ IntOp u32) (IntOp i32) (i2v 0 i32)) ={IntOp u32, IntOp u32} (LocInfoE loc_321 (use{it_layout u32} (LocInfoE loc_322 ((LocInfoE loc_323 (!{void*} (LocInfoE loc_324 ("p")))) at{struct_hyp_page} "refcount")))))))
        then
        locinfo: loc_311 ;
          Goto "#3"
        else
        locinfo: loc_304 ;
          Goto "#4"
      ]> $
      <[ "#2" :=
        locinfo: loc_304 ;
        expr: (LocInfoE loc_304 (Call (LocInfoE loc_306 (global_sl_unlock)) [@{expr} LocInfoE loc_307 (AnnotExpr 1%nat LockA (LocInfoE loc_307 (&(LocInfoE loc_308 ((LocInfoE loc_309 (!{void*} (LocInfoE loc_310 ("pool")))) at{struct_hyp_pool} "lock"))))) ])) ;
        Return (VOID)
      ]> $
      <[ "#3" :=
        locinfo: loc_311 ;
        expr: (LocInfoE loc_311 (Call (LocInfoE loc_313 (global___hyp_attach_page)) [@{expr} LocInfoE loc_314 (use{void*} (LocInfoE loc_315 ("pool"))) ;
        LocInfoE loc_316 (use{void*} (LocInfoE loc_317 ("p"))) ])) ;
        locinfo: loc_304 ;
        Goto "#2"
      ]> $
      <[ "#4" :=
        locinfo: loc_304 ;
        Goto "#2"
      ]> $
      <[ "#5" :=
        locinfo: loc_328 ;
        expr: (LocInfoE loc_328 (Call (LocInfoE loc_330 (global_hyp_panic)) [@{expr}  ])) ;
        locinfo: loc_302 ;
        Goto "#1"
      ]> $
      <[ "#6" :=
        locinfo: loc_302 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_pool_init]. *)
  Definition impl_hyp_pool_init (global_INIT_LIST_HEAD global___hyp_attach_page global_hyp_phys_to_page global_memset global_sl_init : loc): function := {|
    f_args := [
      ("pool", void*);
      ("phys", it_layout u64);
      ("nr_pages", it_layout u32);
      ("used_pages", it_layout u32)
    ];
    f_local_vars := [
      ("i", it_layout i32);
      ("p", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_507 ;
        if: LocInfoE loc_507 (UnOp (CastOp $ IntOp bool_it) (IntOp u64) (LocInfoE loc_507 ((LocInfoE loc_508 (use{it_layout u64} (LocInfoE loc_509 ("phys")))) %{IntOp u64, IntOp u64} (LocInfoE loc_510 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_510 (i2v 4096 i32)))))))
        then
        locinfo: loc_503 ;
          Goto "#11"
        else
        locinfo: loc_365 ;
          Goto "#12"
      ]> $
      <[ "#1" :=
        locinfo: loc_365 ;
        expr: (LocInfoE loc_365 (Call (LocInfoE loc_498 (global_sl_init)) [@{expr} LocInfoE loc_499 (&(LocInfoE loc_500 ((LocInfoE loc_501 (!{void*} (LocInfoE loc_502 ("pool")))) at{struct_hyp_pool} "lock"))) ])) ;
        locinfo: loc_366 ;
        LocInfoE loc_495 ("i") <-{ it_layout i32 }
          LocInfoE loc_496 (i2v 0 i32) ;
        locinfo: loc_367 ;
        Goto "#2"
      ]> $
      <[ "#10" :=
        locinfo: loc_377 ;
        Return (LocInfoE loc_378 (i2v 0 i32))
      ]> $
      <[ "#11" :=
        locinfo: loc_503 ;
        Return (LocInfoE loc_504 (UnOp NegOp (IntOp i32) (LocInfoE loc_505 (i2v 22 i32))))
      ]> $
      <[ "#12" :=
        locinfo: loc_365 ;
        Goto "#1"
      ]> $
      <[ "#2" :=
        locinfo: loc_491 ;
        if: LocInfoE loc_491 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_491 ((LocInfoE loc_492 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_492 (use{it_layout i32} (LocInfoE loc_493 ("i")))))) ≤{IntOp u32, IntOp u32} (LocInfoE loc_494 (i2v 11 u32)))))
        then
        locinfo: loc_476 ;
          Goto "#3"
        else
        locinfo: loc_368 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_476 ;
        expr: (LocInfoE loc_476 (Call (LocInfoE loc_481 (global_INIT_LIST_HEAD)) [@{expr} LocInfoE loc_482 (&(LocInfoE loc_484 ((LocInfoE loc_486 ((LocInfoE loc_487 (!{void*} (LocInfoE loc_488 ("pool")))) at{struct_hyp_pool} "free_area")) at_offset{layout_of struct_list_head, PtrOp, IntOp i32} (LocInfoE loc_489 (use{it_layout i32} (LocInfoE loc_490 ("i"))))))) ])) ;
        locinfo: loc_477 ;
        Goto "continue58"
      ]> $
      <[ "#4" :=
        locinfo: loc_368 ;
        LocInfoE loc_470 ((LocInfoE loc_471 (!{void*} (LocInfoE loc_472 ("pool")))) at{struct_hyp_pool} "range_start") <-{ it_layout u64 }
          LocInfoE loc_473 (use{it_layout u64} (LocInfoE loc_474 ("phys"))) ;
        locinfo: loc_369 ;
        LocInfoE loc_460 ((LocInfoE loc_461 (!{void*} (LocInfoE loc_462 ("pool")))) at{struct_hyp_pool} "range_end") <-{ it_layout u64 }
          LocInfoE loc_463 ((LocInfoE loc_464 (use{it_layout u64} (LocInfoE loc_465 ("phys")))) +{IntOp u64, IntOp u64} (LocInfoE loc_466 (UnOp (CastOp $ IntOp u64) (IntOp u32) (LocInfoE loc_466 ((LocInfoE loc_467 (use{it_layout u32} (LocInfoE loc_468 ("nr_pages")))) <<{IntOp u32, IntOp u32} (LocInfoE loc_469 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_469 (i2v 12 i32))))))))) ;
        locinfo: loc_370 ;
        LocInfoE loc_454 ("p") <-{ void* }
          LocInfoE loc_455 (Call (LocInfoE loc_457 (global_hyp_phys_to_page)) [@{expr} LocInfoE loc_458 (use{it_layout u64} (LocInfoE loc_459 ("phys"))) ]) ;
        locinfo: loc_371 ;
        expr: (LocInfoE loc_371 (Call (LocInfoE loc_446 (global_memset)) [@{expr} LocInfoE loc_447 (use{void*} (LocInfoE loc_448 ("p"))) ;
        LocInfoE loc_449 (i2v 0 i32) ;
        LocInfoE loc_450 ((LocInfoE loc_451 (i2v (layout_of struct_hyp_page).(ly_size) size_t)) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_452 (UnOp (CastOp $ IntOp size_t) (IntOp u32) (LocInfoE loc_452 (use{it_layout u32} (LocInfoE loc_453 ("nr_pages"))))))) ])) ;
        locinfo: loc_372 ;
        LocInfoE loc_443 ("i") <-{ it_layout i32 }
          LocInfoE loc_444 (i2v 0 i32) ;
        locinfo: loc_373 ;
        Goto "#5"
      ]> $
      <[ "#5" :=
        locinfo: loc_438 ;
        if: LocInfoE loc_438 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_438 ((LocInfoE loc_439 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_439 (use{it_layout i32} (LocInfoE loc_440 ("i")))))) <{IntOp u32, IntOp u32} (LocInfoE loc_441 (use{it_layout u32} (LocInfoE loc_442 ("nr_pages")))))))
        then
        locinfo: loc_416 ;
          Goto "#6"
        else
        locinfo: loc_374 ;
          Goto "#7"
      ]> $
      <[ "#6" :=
        locinfo: loc_416 ;
        LocInfoE loc_433 ((LocInfoE loc_434 (!{void*} (LocInfoE loc_435 ("p")))) at{struct_hyp_page} "pool") <-{ void* }
          LocInfoE loc_436 (use{void*} (LocInfoE loc_437 ("pool"))) ;
        locinfo: loc_417 ;
        expr: (LocInfoE loc_417 (Call (LocInfoE loc_428 (global_INIT_LIST_HEAD)) [@{expr} LocInfoE loc_429 (&(LocInfoE loc_430 ((LocInfoE loc_431 (!{void*} (LocInfoE loc_432 ("p")))) at{struct_hyp_page} "node"))) ])) ;
        locinfo: loc_418 ;
        LocInfoE loc_422 ("p") <-{ void* }
          LocInfoE loc_423 ((LocInfoE loc_424 (use{void*} (LocInfoE loc_425 ("p")))) at_offset{layout_of struct_hyp_page, PtrOp, IntOp i32} (LocInfoE loc_426 (i2v 1 i32))) ;
        locinfo: loc_419 ;
        Goto "continue59"
      ]> $
      <[ "#7" :=
        locinfo: loc_374 ;
        LocInfoE loc_404 ("p") <-{ void* }
          LocInfoE loc_405 (Call (LocInfoE loc_407 (global_hyp_phys_to_page)) [@{expr} LocInfoE loc_408 ((LocInfoE loc_409 (use{it_layout u64} (LocInfoE loc_410 ("phys")))) +{IntOp u64, IntOp u64} (LocInfoE loc_411 (UnOp (CastOp $ IntOp u64) (IntOp u32) (LocInfoE loc_411 ((LocInfoE loc_412 (use{it_layout u32} (LocInfoE loc_413 ("used_pages")))) <<{IntOp u32, IntOp u32} (LocInfoE loc_414 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_414 (i2v 12 i32))))))))) ]) ;
        locinfo: loc_375 ;
        LocInfoE loc_401 ("i") <-{ it_layout i32 }
          LocInfoE loc_402 (UnOp (CastOp $ IntOp i32) (IntOp u32) (LocInfoE loc_402 (use{it_layout u32} (LocInfoE loc_403 ("used_pages"))))) ;
        locinfo: loc_376 ;
        Goto "#8"
      ]> $
      <[ "#8" :=
        locinfo: loc_396 ;
        if: LocInfoE loc_396 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_396 ((LocInfoE loc_397 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_397 (use{it_layout i32} (LocInfoE loc_398 ("i")))))) <{IntOp u32, IntOp u32} (LocInfoE loc_399 (use{it_layout u32} (LocInfoE loc_400 ("nr_pages")))))))
        then
        locinfo: loc_380 ;
          Goto "#9"
        else
        locinfo: loc_377 ;
          Goto "#10"
      ]> $
      <[ "#9" :=
        locinfo: loc_380 ;
        expr: (LocInfoE loc_380 (Call (LocInfoE loc_391 (global___hyp_attach_page)) [@{expr} LocInfoE loc_392 (use{void*} (LocInfoE loc_393 ("pool"))) ;
        LocInfoE loc_394 (use{void*} (LocInfoE loc_395 ("p"))) ])) ;
        locinfo: loc_381 ;
        LocInfoE loc_385 ("p") <-{ void* }
          LocInfoE loc_386 ((LocInfoE loc_387 (use{void*} (LocInfoE loc_388 ("p")))) at_offset{layout_of struct_hyp_page, PtrOp, IntOp i32} (LocInfoE loc_389 (i2v 1 i32))) ;
        locinfo: loc_382 ;
        Goto "continue61"
      ]> $
      <[ "continue58" :=
        locinfo: loc_478 ;
        LocInfoE loc_479 ("i") <-{ it_layout i32 }
          LocInfoE loc_478 ((LocInfoE loc_478 (use{it_layout i32} (LocInfoE loc_479 ("i")))) +{IntOp i32, IntOp i32} (LocInfoE loc_478 (i2v 1 i32))) ;
        locinfo: loc_367 ;
        Goto "#2"
      ]> $
      <[ "continue59" :=
        locinfo: loc_420 ;
        LocInfoE loc_421 ("i") <-{ it_layout i32 }
          LocInfoE loc_420 ((LocInfoE loc_420 (use{it_layout i32} (LocInfoE loc_421 ("i")))) +{IntOp i32, IntOp i32} (LocInfoE loc_420 (i2v 1 i32))) ;
        locinfo: loc_373 ;
        Goto "#5"
      ]> $
      <[ "continue61" :=
        locinfo: loc_383 ;
        LocInfoE loc_384 ("i") <-{ it_layout i32 }
          LocInfoE loc_383 ((LocInfoE loc_383 (use{it_layout i32} (LocInfoE loc_384 ("i")))) +{IntOp i32, IntOp i32} (LocInfoE loc_383 (i2v 1 i32))) ;
        locinfo: loc_376 ;
        Goto "#8"
      ]> $∅
    )%E
  |}.

  (* Definition of function [__find_buddy]. *)
  Definition impl___find_buddy (global_hyp_page_to_phys global_hyp_phys_to_page : loc): function := {|
    f_args := [
      ("pool", void*);
      ("p", void*);
      ("order", it_layout u32)
    ];
    f_local_vars := [
      ("addr", it_layout u64)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_513 ;
        expr: (LocInfoE loc_557 (&(LocInfoE loc_558 ((LocInfoE loc_559 (!{void*} (LocInfoE loc_560 ("pool")))) at{struct_hyp_pool} "lock")))) ;
        "addr" <-{ it_layout u64 }
          LocInfoE loc_550 (Call (LocInfoE loc_552 (global_hyp_page_to_phys)) [@{expr} LocInfoE loc_553 (use{void*} (LocInfoE loc_554 ("p"))) ]) ;
        locinfo: loc_516 ;
        LocInfoE loc_542 ("addr") <-{ it_layout u64 }
          LocInfoE loc_543 ((LocInfoE loc_544 (use{it_layout u64} (LocInfoE loc_545 ("addr")))) ^{IntOp u64, IntOp u64} (LocInfoE loc_546 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_546 ((LocInfoE loc_547 (i2v 4096 i32)) <<{IntOp i32, IntOp i32} (LocInfoE loc_548 (UnOp (CastOp $ IntOp i32) (IntOp u32) (LocInfoE loc_548 (use{it_layout u32} (LocInfoE loc_549 ("order"))))))))))) ;
        locinfo: loc_528 ;
        if: LocInfoE loc_528 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_528 ((LocInfoE loc_529 (use{it_layout u64} (LocInfoE loc_530 ("addr")))) <{IntOp u64, IntOp u64} (LocInfoE loc_531 (use{it_layout u64} (LocInfoE loc_532 ((LocInfoE loc_533 (!{void*} (LocInfoE loc_534 ("pool")))) at{struct_hyp_pool} "range_start")))))))
        then
        locinfo: loc_524 ;
          Goto "#2"
        else
        Goto "#4"
      ]> $
      <[ "#1" :=
        locinfo: loc_518 ;
        Return (LocInfoE loc_519 (Call (LocInfoE loc_521 (global_hyp_phys_to_page)) [@{expr} LocInfoE loc_522 (use{it_layout u64} (LocInfoE loc_523 ("addr"))) ]))
      ]> $
      <[ "#2" :=
        locinfo: loc_524 ;
        Return (LocInfoE loc_525 (NULL))
      ]> $
      <[ "#3" :=
        locinfo: loc_518 ;
        Goto "#1"
      ]> $
      <[ "#4" :=
        locinfo: loc_535 ;
        if: LocInfoE loc_535 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_535 ((LocInfoE loc_536 (use{it_layout u64} (LocInfoE loc_537 ("addr")))) ≥{IntOp u64, IntOp u64} (LocInfoE loc_538 (use{it_layout u64} (LocInfoE loc_539 ((LocInfoE loc_540 (!{void*} (LocInfoE loc_541 ("pool")))) at{struct_hyp_pool} "range_end")))))))
        then
        locinfo: loc_524 ;
          Goto "#2"
        else
        locinfo: loc_518 ;
          Goto "#3"
      ]> $∅
    )%E
  |}.

  (* Definition of function [__hyp_attach_page]. *)
  Definition impl___hyp_attach_page (global___find_buddy global_list_add global_list_del_init global_list_empty : loc): function := {|
    f_args := [
      ("pool", void*);
      ("p", void*)
    ];
    f_local_vars := [
      ("order", it_layout u32);
      ("buddy", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_563 ;
        expr: (LocInfoE loc_682 (&(LocInfoE loc_683 ((LocInfoE loc_684 (!{void*} (LocInfoE loc_685 ("pool")))) at{struct_hyp_pool} "lock")))) ;
        "order" <-{ it_layout u32 }
          LocInfoE loc_676 (use{it_layout u32} (LocInfoE loc_677 ((LocInfoE loc_678 (!{void*} (LocInfoE loc_679 ("p")))) at{struct_hyp_page} "order"))) ;
        locinfo: loc_566 ;
        LocInfoE loc_672 ((LocInfoE loc_673 (!{void*} (LocInfoE loc_674 ("p")))) at{struct_hyp_page} "order") <-{ it_layout u32 }
          LocInfoE loc_675 (i2v (max_int u32) u32) ;
        locinfo: loc_567 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_668 ;
        if: LocInfoE loc_668 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_668 ((LocInfoE loc_669 (use{it_layout u32} (LocInfoE loc_670 ("order")))) <{IntOp u32, IntOp u32} (LocInfoE loc_671 (i2v 11 u32)))))
        then
        locinfo: loc_597 ;
          Goto "#2"
        else
        locinfo: loc_568 ;
          Goto "#3"
      ]> $
      <[ "#10" :=
        locinfo: loc_647 ;
        if: LocInfoE loc_647 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_647 ((LocInfoE loc_648 (use{it_layout u32} (LocInfoE loc_649 ((LocInfoE loc_650 (!{void*} (LocInfoE loc_651 ("buddy")))) at{struct_hyp_page} "order")))) !={IntOp u32, IntOp u32} (LocInfoE loc_652 (use{it_layout u32} (LocInfoE loc_653 ("order")))))))
        then
        locinfo: loc_568 ;
          Goto "#8"
        else
        locinfo: loc_601 ;
          Goto "#9"
      ]> $
      <[ "#11" :=
        locinfo: loc_640 ;
        if: LocInfoE loc_640 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_640 (Call (LocInfoE loc_642 (global_list_empty)) [@{expr} LocInfoE loc_643 (&(LocInfoE loc_644 ((LocInfoE loc_645 (!{void*} (LocInfoE loc_646 ("buddy")))) at{struct_hyp_page} "node"))) ])))
        then
        locinfo: loc_568 ;
          Goto "#8"
        else
        Goto "#10"
      ]> $
      <[ "#2" :=
        locinfo: loc_597 ;
        LocInfoE loc_658 ("buddy") <-{ void* }
          LocInfoE loc_659 (Call (LocInfoE loc_661 (global___find_buddy)) [@{expr} LocInfoE loc_662 (use{void*} (LocInfoE loc_663 ("pool"))) ;
          LocInfoE loc_664 (use{void*} (LocInfoE loc_665 ("p"))) ;
          LocInfoE loc_666 (use{it_layout u32} (LocInfoE loc_667 ("order"))) ]) ;
        locinfo: loc_598 ;
        expr: (LocInfoE loc_654 (&(LocInfoE loc_655 ((LocInfoE loc_656 (!{void*} (LocInfoE loc_657 ("pool")))) at{struct_hyp_pool} "lock")))) ;
        locinfo: loc_636 ;
        if: LocInfoE loc_636 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_636 ((LocInfoE loc_637 (use{void*} (LocInfoE loc_638 ("buddy")))) ={PtrOp, PtrOp} (LocInfoE loc_639 (NULL)))))
        then
        locinfo: loc_568 ;
          Goto "#8"
        else
        Goto "#11"
      ]> $
      <[ "#3" :=
        locinfo: loc_568 ;
        expr: (LocInfoE loc_592 (&(LocInfoE loc_593 ((LocInfoE loc_594 (!{void*} (LocInfoE loc_595 ("pool")))) at{struct_hyp_pool} "lock")))) ;
        locinfo: loc_570 ;
        LocInfoE loc_587 ((LocInfoE loc_588 (!{void*} (LocInfoE loc_589 ("p")))) at{struct_hyp_page} "order") <-{ it_layout u32 }
          LocInfoE loc_590 (use{it_layout u32} (LocInfoE loc_591 ("order"))) ;
        locinfo: loc_571 ;
        expr: (LocInfoE loc_571 (Call (LocInfoE loc_573 (global_list_add)) [@{expr} LocInfoE loc_574 (&(LocInfoE loc_575 ((LocInfoE loc_576 (!{void*} (LocInfoE loc_577 ("p")))) at{struct_hyp_page} "node"))) ;
        LocInfoE loc_578 (&(LocInfoE loc_580 ((LocInfoE loc_582 ((LocInfoE loc_583 (!{void*} (LocInfoE loc_584 ("pool")))) at{struct_hyp_pool} "free_area")) at_offset{layout_of struct_list_head, PtrOp, IntOp u32} (LocInfoE loc_585 (use{it_layout u32} (LocInfoE loc_586 ("order"))))))) ])) ;
        Return (VOID)
      ]> $
      <[ "#4" :=
        locinfo: loc_601 ;
        expr: (LocInfoE loc_601 (Call (LocInfoE loc_627 (global_list_del_init)) [@{expr} LocInfoE loc_628 (&(LocInfoE loc_629 ((LocInfoE loc_630 (!{void*} (LocInfoE loc_631 ("buddy")))) at{struct_hyp_page} "node"))) ])) ;
        locinfo: loc_602 ;
        LocInfoE loc_622 ((LocInfoE loc_623 (!{void*} (LocInfoE loc_624 ("buddy")))) at{struct_hyp_page} "order") <-{ it_layout u32 }
          LocInfoE loc_625 (i2v (max_int u32) u32) ;
        locinfo: loc_617 ;
        if: LocInfoE loc_617 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_617 ((LocInfoE loc_618 (use{void*} (LocInfoE loc_619 ("p")))) <{PtrOp, PtrOp} (LocInfoE loc_620 (use{void*} (LocInfoE loc_621 ("buddy")))))))
        then
        locinfo: loc_608 ;
          Goto "#6"
        else
        locinfo: loc_613 ;
          Goto "#7"
      ]> $
      <[ "#5" :=
        locinfo: loc_604 ;
        Goto "continue36"
      ]> $
      <[ "#6" :=
        locinfo: loc_608 ;
        LocInfoE loc_609 ("p") <-{ void* }
          LocInfoE loc_610 (use{void*} (LocInfoE loc_611 ("p"))) ;
        locinfo: loc_604 ;
        Goto "#5"
      ]> $
      <[ "#7" :=
        locinfo: loc_613 ;
        LocInfoE loc_614 ("p") <-{ void* }
          LocInfoE loc_615 (use{void*} (LocInfoE loc_616 ("buddy"))) ;
        locinfo: loc_604 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        locinfo: loc_568 ;
        Goto "#3"
      ]> $
      <[ "#9" :=
        locinfo: loc_601 ;
        Goto "#4"
      ]> $
      <[ "continue36" :=
        locinfo: loc_605 ;
        LocInfoE loc_606 ("order") <-{ it_layout u32 }
          LocInfoE loc_605 ((LocInfoE loc_605 (use{it_layout u32} (LocInfoE loc_606 ("order")))) +{IntOp u32, IntOp u32} (LocInfoE loc_605 (i2v 1 u32))) ;
        locinfo: loc_567 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [__hyp_extract_page]. *)
  Definition impl___hyp_extract_page (global___find_buddy global_list_add_tail global_list_del_init : loc): function := {|
    f_args := [
      ("pool", void*);
      ("p", void*);
      ("order", it_layout u32)
    ];
    f_local_vars := [
      ("buddy", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_763 ;
        if: LocInfoE loc_763 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_763 ((LocInfoE loc_764 (use{it_layout u32} (LocInfoE loc_765 ((LocInfoE loc_766 (!{void*} (LocInfoE loc_767 ("p")))) at{struct_hyp_page} "order")))) ={IntOp u32, IntOp u32} (LocInfoE loc_768 (i2v (max_int u32) u32)))))
        then
        locinfo: loc_759 ;
          Goto "#5"
        else
        Goto "#7"
      ]> $
      <[ "#1" :=
        locinfo: loc_689 ;
        expr: (LocInfoE loc_689 (Call (LocInfoE loc_754 (global_list_del_init)) [@{expr} LocInfoE loc_755 (&(LocInfoE loc_756 ((LocInfoE loc_757 (!{void*} (LocInfoE loc_758 ("p")))) at{struct_hyp_page} "node"))) ])) ;
        locinfo: loc_690 ;
        Goto "#2"
      ]> $
      <[ "#2" :=
        locinfo: loc_746 ;
        if: LocInfoE loc_746 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_746 ((LocInfoE loc_747 (use{it_layout u32} (LocInfoE loc_748 ((LocInfoE loc_749 (!{void*} (LocInfoE loc_750 ("p")))) at{struct_hyp_page} "order")))) >{IntOp u32, IntOp u32} (LocInfoE loc_751 (use{it_layout u32} (LocInfoE loc_752 ("order")))))))
        then
        locinfo: loc_701 ;
          Goto "#3"
        else
        locinfo: loc_691 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_701 ;
        LocInfoE loc_743 ((LocInfoE loc_744 (!{void*} (LocInfoE loc_745 ("p")))) at{struct_hyp_page} "order") <-{ it_layout u32 }
          LocInfoE loc_701 ((LocInfoE loc_701 (use{it_layout u32} (LocInfoE loc_743 ((LocInfoE loc_744 (!{void*} (LocInfoE loc_745 ("p")))) at{struct_hyp_page} "order")))) -{IntOp u32, IntOp u32} (LocInfoE loc_701 (i2v 1 u32))) ;
        locinfo: loc_702 ;
        LocInfoE loc_731 ("buddy") <-{ void* }
          LocInfoE loc_732 (Call (LocInfoE loc_734 (global___find_buddy)) [@{expr} LocInfoE loc_735 (use{void*} (LocInfoE loc_736 ("pool"))) ;
          LocInfoE loc_737 (use{void*} (LocInfoE loc_738 ("p"))) ;
          LocInfoE loc_739 (use{it_layout u32} (LocInfoE loc_740 ((LocInfoE loc_741 (!{void*} (LocInfoE loc_742 ("p")))) at{struct_hyp_page} "order"))) ]) ;
        locinfo: loc_703 ;
        LocInfoE loc_724 ((LocInfoE loc_725 (!{void*} (LocInfoE loc_726 ("buddy")))) at{struct_hyp_page} "order") <-{ it_layout u32 }
          LocInfoE loc_727 (use{it_layout u32} (LocInfoE loc_728 ((LocInfoE loc_729 (!{void*} (LocInfoE loc_730 ("p")))) at{struct_hyp_page} "order"))) ;
        locinfo: loc_704 ;
        expr: (LocInfoE loc_704 (Call (LocInfoE loc_708 (global_list_add_tail)) [@{expr} LocInfoE loc_709 (&(LocInfoE loc_710 ((LocInfoE loc_711 (!{void*} (LocInfoE loc_712 ("buddy")))) at{struct_hyp_page} "node"))) ;
        LocInfoE loc_713 (&(LocInfoE loc_715 ((LocInfoE loc_717 ((LocInfoE loc_718 (!{void*} (LocInfoE loc_719 ("pool")))) at{struct_hyp_pool} "free_area")) at_offset{layout_of struct_list_head, PtrOp, IntOp u32} (LocInfoE loc_720 (use{it_layout u32} (LocInfoE loc_721 ((LocInfoE loc_722 (!{void*} (LocInfoE loc_723 ("buddy")))) at{struct_hyp_page} "order"))))))) ])) ;
        locinfo: loc_705 ;
        Goto "continue46"
      ]> $
      <[ "#4" :=
        locinfo: loc_691 ;
        LocInfoE loc_695 ((LocInfoE loc_696 (!{void*} (LocInfoE loc_697 ("p")))) at{struct_hyp_page} "refcount") <-{ it_layout u32 }
          LocInfoE loc_698 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_698 (i2v 1 i32))) ;
        locinfo: loc_692 ;
        Return (LocInfoE loc_693 (use{void*} (LocInfoE loc_694 ("p"))))
      ]> $
      <[ "#5" :=
        locinfo: loc_759 ;
        Return (LocInfoE loc_760 (NULL))
      ]> $
      <[ "#6" :=
        locinfo: loc_689 ;
        Goto "#1"
      ]> $
      <[ "#7" :=
        locinfo: loc_769 ;
        if: LocInfoE loc_769 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_769 ((LocInfoE loc_770 (use{it_layout u32} (LocInfoE loc_771 ((LocInfoE loc_772 (!{void*} (LocInfoE loc_773 ("p")))) at{struct_hyp_page} "order")))) <{IntOp u32, IntOp u32} (LocInfoE loc_774 (use{it_layout u32} (LocInfoE loc_775 ("order")))))))
        then
        locinfo: loc_759 ;
          Goto "#5"
        else
        locinfo: loc_689 ;
          Goto "#6"
      ]> $
      <[ "continue46" :=
        locinfo: loc_690 ;
        Goto "#2"
      ]> $∅
    )%E
  |}.

  (* Definition of function [clear_hyp_page]. *)
  Definition impl_clear_hyp_page (global_hyp_physvirt_offset global_clear_page global_hyp_page_to_phys : loc): function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout u64)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_778 ;
        LocInfoE loc_812 ("i") <-{ it_layout u64 }
          LocInfoE loc_813 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_813 (i2v 0 i32))) ;
        locinfo: loc_779 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_803 ;
        if: LocInfoE loc_803 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_803 ((LocInfoE loc_804 (use{it_layout u64} (LocInfoE loc_805 ("i")))) <{IntOp u64, IntOp u64} (LocInfoE loc_806 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_806 ((LocInfoE loc_807 (i2v 1 i32)) <<{IntOp i32, IntOp i32} (LocInfoE loc_808 (UnOp (CastOp $ IntOp i32) (IntOp u32) (LocInfoE loc_808 (use{it_layout u32} (LocInfoE loc_809 ((LocInfoE loc_810 (!{void*} (LocInfoE loc_811 ("p")))) at{struct_hyp_page} "order")))))))))))))
        then
        locinfo: loc_781 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_781 ;
        expr: (LocInfoE loc_781 (Call (LocInfoE loc_786 (global_clear_page)) [@{expr} LocInfoE loc_787 ((LocInfoE loc_788 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_789 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_790 ((LocInfoE loc_791 (UnOp (CastOp $ IntOp u64) (IntOp u64) (LocInfoE loc_792 (Call (LocInfoE loc_794 (global_hyp_page_to_phys)) [@{expr} LocInfoE loc_795 (use{void*} (LocInfoE loc_796 ("p"))) ])))) -{IntOp u64, IntOp u64} (LocInfoE loc_797 (UnOp (CastOp $ IntOp u64) (IntOp i64) (LocInfoE loc_797 (use{it_layout i64} (LocInfoE loc_798 (global_hyp_physvirt_offset)))))))))))) at_offset{it_layout u8, PtrOp, IntOp u64} (LocInfoE loc_799 ((LocInfoE loc_800 (use{it_layout u64} (LocInfoE loc_801 ("i")))) <<{IntOp u64, IntOp u64} (LocInfoE loc_802 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_802 (i2v 12 i32))))))) ])) ;
        locinfo: loc_782 ;
        Goto "continue50"
      ]> $
      <[ "#3" :=
        Return (VOID)
      ]> $
      <[ "continue50" :=
        locinfo: loc_783 ;
        LocInfoE loc_784 ("i") <-{ it_layout u64 }
          LocInfoE loc_783 ((LocInfoE loc_783 (use{it_layout u64} (LocInfoE loc_784 ("i")))) +{IntOp u64, IntOp u64} (LocInfoE loc_783 (i2v 1 u64))) ;
        locinfo: loc_779 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [__hyp_alloc_pages]. *)
  Definition impl___hyp_alloc_pages (global___hyp_extract_page global_clear_hyp_page global_list_empty : loc): function := {|
    f_args := [
      ("pool", void*);
      ("mask", it_layout u64);
      ("order", it_layout u32)
    ];
    f_local_vars := [
      ("i", it_layout u32);
      ("p", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout u32 }
          LocInfoE loc_890 (use{it_layout u32} (LocInfoE loc_891 ("order"))) ;
        locinfo: loc_817 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_874 ;
        if: LocInfoE loc_874 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_874 ((LocInfoE loc_875 (use{it_layout u32} (LocInfoE loc_876 ("i")))) ≤{IntOp u32, IntOp u32} (LocInfoE loc_877 (i2v 11 u32)))))
        then
        Goto "#10"
        else
        locinfo: loc_864 ;
          Goto "#3"
      ]> $
      <[ "#10" :=
        locinfo: loc_878 ;
        if: LocInfoE loc_878 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_878 (Call (LocInfoE loc_880 (global_list_empty)) [@{expr} LocInfoE loc_881 (&(LocInfoE loc_883 ((LocInfoE loc_885 ((LocInfoE loc_886 (!{void*} (LocInfoE loc_887 ("pool")))) at{struct_hyp_pool} "free_area")) at_offset{layout_of struct_list_head, PtrOp, IntOp u32} (LocInfoE loc_888 (use{it_layout u32} (LocInfoE loc_889 ("i"))))))) ])))
        then
        locinfo: loc_869 ;
          Goto "#2"
        else
        locinfo: loc_864 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_869 ;
        LocInfoE loc_872 ("i") <-{ it_layout u32 }
          LocInfoE loc_869 ((LocInfoE loc_869 (use{it_layout u32} (LocInfoE loc_872 ("i")))) +{IntOp u32, IntOp u32} (LocInfoE loc_869 (i2v 1 u32))) ;
        locinfo: loc_870 ;
        Goto "continue53"
      ]> $
      <[ "#3" :=
        locinfo: loc_864 ;
        if: LocInfoE loc_864 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_864 ((LocInfoE loc_865 (use{it_layout u32} (LocInfoE loc_866 ("i")))) >{IntOp u32, IntOp u32} (LocInfoE loc_867 (i2v 11 u32)))))
        then
        locinfo: loc_861 ;
          Goto "#8"
        else
        locinfo: loc_819 ;
          Goto "#9"
      ]> $
      <[ "#4" :=
        locinfo: loc_819 ;
        LocInfoE loc_845 ("p") <-{ void* }
          LocInfoE loc_846 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_847 ((LocInfoE loc_848 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_849 (use{void*} (LocInfoE loc_850 ((LocInfoE loc_851 (&(LocInfoE loc_853 ((LocInfoE loc_855 ((LocInfoE loc_856 (!{void*} (LocInfoE loc_857 ("pool")))) at{struct_hyp_pool} "free_area")) at_offset{layout_of struct_list_head, PtrOp, IntOp u32} (LocInfoE loc_858 (use{it_layout u32} (LocInfoE loc_859 ("i")))))))) at{struct_list_head} "next")))))) at_neg_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_860 ((OffsetOf (struct_hyp_page) ("node"))))))) ;
        locinfo: loc_820 ;
        LocInfoE loc_835 ("p") <-{ void* }
          LocInfoE loc_836 (Call (LocInfoE loc_838 (global___hyp_extract_page)) [@{expr} LocInfoE loc_839 (use{void*} (LocInfoE loc_840 ("pool"))) ;
          LocInfoE loc_841 (use{void*} (LocInfoE loc_842 ("p"))) ;
          LocInfoE loc_843 (use{it_layout u32} (LocInfoE loc_844 ("order"))) ]) ;
        locinfo: loc_831 ;
        if: LocInfoE loc_831 (UnOp (CastOp $ IntOp bool_it) (IntOp u64) (LocInfoE loc_831 ((LocInfoE loc_832 (use{it_layout u64} (LocInfoE loc_833 ("mask")))) &{IntOp u64, IntOp u64} (LocInfoE loc_834 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_834 (i2v 1 i32)))))))
        then
        locinfo: loc_825 ;
          Goto "#6"
        else
        locinfo: loc_822 ;
          Goto "#7"
      ]> $
      <[ "#5" :=
        locinfo: loc_822 ;
        Return (LocInfoE loc_823 (use{void*} (LocInfoE loc_824 ("p"))))
      ]> $
      <[ "#6" :=
        locinfo: loc_825 ;
        expr: (LocInfoE loc_825 (Call (LocInfoE loc_827 (global_clear_hyp_page)) [@{expr} LocInfoE loc_828 (use{void*} (LocInfoE loc_829 ("p"))) ])) ;
        locinfo: loc_822 ;
        Goto "#5"
      ]> $
      <[ "#7" :=
        locinfo: loc_822 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        locinfo: loc_861 ;
        Return (LocInfoE loc_862 (NULL))
      ]> $
      <[ "#9" :=
        locinfo: loc_819 ;
        Goto "#4"
      ]> $
      <[ "continue53" :=
        locinfo: loc_817 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.
End code.
