From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [linux/casestudies/page_alloc.c]. *)
Section code.
  Definition file_0 : string := "linux/casestudies/page_alloc.c".
  Definition loc_2 : location_info := LocationInfo file_0 34 1 34 11.
  Definition loc_3 : location_info := LocationInfo file_0 34 8 34 9.
  Definition loc_6 : location_info := LocationInfo file_0 64 1 64 10.
  Definition loc_7 : location_info := LocationInfo file_0 64 8 64 9.
  Definition loc_10 : location_info := LocationInfo file_0 68 1 68 10.
  Definition loc_11 : location_info := LocationInfo file_0 68 8 68 9.
  Definition loc_14 : location_info := LocationInfo file_0 80 1 80 25.
  Definition loc_15 : location_info := LocationInfo file_0 81 1 81 19.
  Definition loc_16 : location_info := LocationInfo file_0 81 1 81 11.
  Definition loc_17 : location_info := LocationInfo file_0 81 1 81 5.
  Definition loc_18 : location_info := LocationInfo file_0 81 1 81 5.
  Definition loc_19 : location_info := LocationInfo file_0 81 14 81 18.
  Definition loc_20 : location_info := LocationInfo file_0 81 14 81 18.
  Definition loc_21 : location_info := LocationInfo file_0 80 2 80 14.
  Definition loc_22 : location_info := LocationInfo file_0 80 3 80 7.
  Definition loc_23 : location_info := LocationInfo file_0 80 3 80 7.
  Definition loc_24 : location_info := LocationInfo file_0 80 17 80 23.
  Definition loc_25 : location_info := LocationInfo file_0 80 17 80 23.
  Definition loc_28 : location_info := LocationInfo file_0 94 1 95 9.
  Definition loc_29 : location_info := LocationInfo file_0 97 1 97 18.
  Definition loc_30 : location_info := LocationInfo file_0 98 1 98 18.
  Definition loc_31 : location_info := LocationInfo file_0 99 1 99 18.
  Definition loc_32 : location_info := LocationInfo file_0 100 1 100 24.
  Definition loc_33 : location_info := LocationInfo file_0 100 2 100 14.
  Definition loc_34 : location_info := LocationInfo file_0 100 3 100 7.
  Definition loc_35 : location_info := LocationInfo file_0 100 3 100 7.
  Definition loc_36 : location_info := LocationInfo file_0 100 17 100 22.
  Definition loc_37 : location_info := LocationInfo file_0 100 17 100 22.
  Definition loc_38 : location_info := LocationInfo file_0 99 1 99 10.
  Definition loc_39 : location_info := LocationInfo file_0 99 1 99 4.
  Definition loc_40 : location_info := LocationInfo file_0 99 1 99 4.
  Definition loc_41 : location_info := LocationInfo file_0 99 13 99 17.
  Definition loc_42 : location_info := LocationInfo file_0 99 13 99 17.
  Definition loc_43 : location_info := LocationInfo file_0 98 1 98 10.
  Definition loc_44 : location_info := LocationInfo file_0 98 1 98 4.
  Definition loc_45 : location_info := LocationInfo file_0 98 1 98 4.
  Definition loc_46 : location_info := LocationInfo file_0 98 13 98 17.
  Definition loc_47 : location_info := LocationInfo file_0 98 13 98 17.
  Definition loc_48 : location_info := LocationInfo file_0 97 1 97 11.
  Definition loc_49 : location_info := LocationInfo file_0 97 1 97 5.
  Definition loc_50 : location_info := LocationInfo file_0 97 1 97 5.
  Definition loc_51 : location_info := LocationInfo file_0 97 14 97 17.
  Definition loc_52 : location_info := LocationInfo file_0 97 14 97 17.
  Definition loc_53 : location_info := LocationInfo file_0 95 2 95 9.
  Definition loc_56 : location_info := LocationInfo file_0 94 5 94 39.
  Definition loc_58 : location_info := LocationInfo file_0 94 6 94 39.
  Definition loc_59 : location_info := LocationInfo file_0 94 6 94 22.
  Definition loc_60 : location_info := LocationInfo file_0 94 6 94 22.
  Definition loc_61 : location_info := LocationInfo file_0 94 23 94 26.
  Definition loc_62 : location_info := LocationInfo file_0 94 23 94 26.
  Definition loc_63 : location_info := LocationInfo file_0 94 28 94 32.
  Definition loc_64 : location_info := LocationInfo file_0 94 28 94 32.
  Definition loc_65 : location_info := LocationInfo file_0 94 34 94 38.
  Definition loc_66 : location_info := LocationInfo file_0 94 34 94 38.
  Definition loc_69 : location_info := LocationInfo file_0 117 1 117 35.
  Definition loc_70 : location_info := LocationInfo file_0 117 1 117 11.
  Definition loc_71 : location_info := LocationInfo file_0 117 1 117 11.
  Definition loc_72 : location_info := LocationInfo file_0 117 12 117 15.
  Definition loc_73 : location_info := LocationInfo file_0 117 12 117 15.
  Definition loc_74 : location_info := LocationInfo file_0 117 17 117 21.
  Definition loc_75 : location_info := LocationInfo file_0 117 17 117 21.
  Definition loc_76 : location_info := LocationInfo file_0 117 23 117 33.
  Definition loc_77 : location_info := LocationInfo file_0 117 23 117 33.
  Definition loc_78 : location_info := LocationInfo file_0 117 23 117 27.
  Definition loc_79 : location_info := LocationInfo file_0 117 23 117 27.
  Definition loc_82 : location_info := LocationInfo file_0 131 1 131 35.
  Definition loc_83 : location_info := LocationInfo file_0 131 1 131 11.
  Definition loc_84 : location_info := LocationInfo file_0 131 1 131 11.
  Definition loc_85 : location_info := LocationInfo file_0 131 12 131 15.
  Definition loc_86 : location_info := LocationInfo file_0 131 12 131 15.
  Definition loc_87 : location_info := LocationInfo file_0 131 17 131 27.
  Definition loc_88 : location_info := LocationInfo file_0 131 17 131 27.
  Definition loc_89 : location_info := LocationInfo file_0 131 17 131 21.
  Definition loc_90 : location_info := LocationInfo file_0 131 17 131 21.
  Definition loc_91 : location_info := LocationInfo file_0 131 29 131 33.
  Definition loc_92 : location_info := LocationInfo file_0 131 29 131 33.
  Definition loc_95 : location_info := LocationInfo file_0 143 1 143 19.
  Definition loc_96 : location_info := LocationInfo file_0 144 1 144 25.
  Definition loc_97 : location_info := LocationInfo file_0 144 2 144 14.
  Definition loc_98 : location_info := LocationInfo file_0 144 3 144 7.
  Definition loc_99 : location_info := LocationInfo file_0 144 3 144 7.
  Definition loc_100 : location_info := LocationInfo file_0 144 17 144 23.
  Definition loc_101 : location_info := LocationInfo file_0 144 17 144 23.
  Definition loc_102 : location_info := LocationInfo file_0 143 1 143 11.
  Definition loc_103 : location_info := LocationInfo file_0 143 1 143 5.
  Definition loc_104 : location_info := LocationInfo file_0 143 1 143 5.
  Definition loc_105 : location_info := LocationInfo file_0 143 14 143 18.
  Definition loc_106 : location_info := LocationInfo file_0 143 14 143 18.
  Definition loc_109 : location_info := LocationInfo file_0 149 1 150 9.
  Definition loc_110 : location_info := LocationInfo file_0 152 1 152 38.
  Definition loc_111 : location_info := LocationInfo file_0 152 1 152 11.
  Definition loc_112 : location_info := LocationInfo file_0 152 1 152 11.
  Definition loc_113 : location_info := LocationInfo file_0 152 12 152 23.
  Definition loc_114 : location_info := LocationInfo file_0 152 12 152 23.
  Definition loc_115 : location_info := LocationInfo file_0 152 12 152 17.
  Definition loc_116 : location_info := LocationInfo file_0 152 12 152 17.
  Definition loc_117 : location_info := LocationInfo file_0 152 25 152 36.
  Definition loc_118 : location_info := LocationInfo file_0 152 25 152 36.
  Definition loc_119 : location_info := LocationInfo file_0 152 25 152 30.
  Definition loc_120 : location_info := LocationInfo file_0 152 25 152 30.
  Definition loc_121 : location_info := LocationInfo file_0 150 2 150 9.
  Definition loc_124 : location_info := LocationInfo file_0 149 5 149 35.
  Definition loc_126 : location_info := LocationInfo file_0 149 6 149 35.
  Definition loc_127 : location_info := LocationInfo file_0 149 6 149 28.
  Definition loc_128 : location_info := LocationInfo file_0 149 6 149 28.
  Definition loc_129 : location_info := LocationInfo file_0 149 29 149 34.
  Definition loc_130 : location_info := LocationInfo file_0 149 29 149 34.
  Definition loc_133 : location_info := LocationInfo file_0 166 1 166 25.
  Definition loc_134 : location_info := LocationInfo file_0 167 1 167 23.
  Definition loc_135 : location_info := LocationInfo file_0 167 1 167 15.
  Definition loc_136 : location_info := LocationInfo file_0 167 1 167 15.
  Definition loc_137 : location_info := LocationInfo file_0 167 16 167 21.
  Definition loc_138 : location_info := LocationInfo file_0 167 16 167 21.
  Definition loc_139 : location_info := LocationInfo file_0 166 1 166 17.
  Definition loc_140 : location_info := LocationInfo file_0 166 1 166 17.
  Definition loc_141 : location_info := LocationInfo file_0 166 18 166 23.
  Definition loc_142 : location_info := LocationInfo file_0 166 18 166 23.
  Definition loc_145 : location_info := LocationInfo file_0 181 1 181 29.
  Definition loc_146 : location_info := LocationInfo file_0 181 8 181 28.
  Definition loc_147 : location_info := LocationInfo file_0 181 8 181 20.
  Definition loc_148 : location_info := LocationInfo file_0 181 8 181 20.
  Definition loc_149 : location_info := LocationInfo file_0 181 9 181 13.
  Definition loc_150 : location_info := LocationInfo file_0 181 9 181 13.
  Definition loc_151 : location_info := LocationInfo file_0 181 24 181 28.
  Definition loc_152 : location_info := LocationInfo file_0 181 24 181 28.
  Definition loc_155 : location_info := LocationInfo file_0 248 1 248 62.
  Definition loc_156 : location_info := LocationInfo file_0 248 8 248 61.
  Definition loc_157 : location_info := LocationInfo file_0 248 17 248 60.
  Definition loc_158 : location_info := LocationInfo file_0 248 18 248 37.
  Definition loc_159 : location_info := LocationInfo file_0 248 31 248 37.
  Definition loc_160 : location_info := LocationInfo file_0 248 31 248 37.
  Definition loc_161 : location_info := LocationInfo file_0 248 40 248 59.
  Definition loc_162 : location_info := LocationInfo file_0 248 40 248 59.
  Definition loc_165 : location_info := LocationInfo file_0 253 1 253 52.
  Definition loc_166 : location_info := LocationInfo file_0 253 8 253 51.
  Definition loc_167 : location_info := LocationInfo file_0 253 9 253 28.
  Definition loc_168 : location_info := LocationInfo file_0 253 22 253 28.
  Definition loc_169 : location_info := LocationInfo file_0 253 22 253 28.
  Definition loc_170 : location_info := LocationInfo file_0 253 31 253 50.
  Definition loc_171 : location_info := LocationInfo file_0 253 31 253 50.
  Definition loc_174 : location_info := LocationInfo file_0 266 1 266 62.
  Definition loc_175 : location_info := LocationInfo file_0 266 8 266 61.
  Definition loc_176 : location_info := LocationInfo file_0 266 9 266 43.
  Definition loc_177 : location_info := LocationInfo file_0 266 29 266 42.
  Definition loc_178 : location_info := LocationInfo file_0 266 29 266 42.
  Definition loc_179 : location_info := LocationInfo file_0 266 46 266 60.
  Definition loc_180 : location_info := LocationInfo file_0 266 47 266 53.
  Definition loc_181 : location_info := LocationInfo file_0 266 47 266 53.
  Definition loc_182 : location_info := LocationInfo file_0 266 57 266 59.
  Definition loc_185 : location_info := LocationInfo file_0 278 1 278 75.
  Definition loc_186 : location_info := LocationInfo file_0 278 8 278 74.
  Definition loc_187 : location_info := LocationInfo file_0 278 9 278 67.
  Definition loc_188 : location_info := LocationInfo file_0 278 22 278 67.
  Definition loc_189 : location_info := LocationInfo file_0 278 23 278 29.
  Definition loc_190 : location_info := LocationInfo file_0 278 23 278 29.
  Definition loc_191 : location_info := LocationInfo file_0 278 32 278 66.
  Definition loc_192 : location_info := LocationInfo file_0 278 52 278 65.
  Definition loc_193 : location_info := LocationInfo file_0 278 52 278 65.
  Definition loc_194 : location_info := LocationInfo file_0 278 71 278 73.
  Definition loc_197 : location_info := LocationInfo file_0 285 1 285 84.
  Definition loc_198 : location_info := LocationInfo file_0 287 1 287 20.
  Definition loc_199 : location_info := LocationInfo file_0 287 8 287 19.
  Definition loc_200 : location_info := LocationInfo file_0 287 8 287 19.
  Definition loc_201 : location_info := LocationInfo file_0 287 8 287 9.
  Definition loc_202 : location_info := LocationInfo file_0 287 8 287 9.
  Definition loc_203 : location_info := LocationInfo file_0 285 22 285 83.
  Definition loc_204 : location_info := LocationInfo file_0 285 22 285 38.
  Definition loc_205 : location_info := LocationInfo file_0 285 22 285 38.
  Definition loc_206 : location_info := LocationInfo file_0 285 39 285 82.
  Definition loc_207 : location_info := LocationInfo file_0 285 40 285 59.
  Definition loc_208 : location_info := LocationInfo file_0 285 53 285 59.
  Definition loc_209 : location_info := LocationInfo file_0 285 53 285 59.
  Definition loc_210 : location_info := LocationInfo file_0 285 62 285 81.
  Definition loc_211 : location_info := LocationInfo file_0 285 62 285 81.
  Definition loc_216 : location_info := LocationInfo file_0 522 1 522 22.
  Definition loc_217 : location_info := LocationInfo file_0 523 1 523 42.
  Definition loc_218 : location_info := LocationInfo file_0 524 1 524 24.
  Definition loc_219 : location_info := LocationInfo file_0 526 1 526 98.
  Definition loc_220 : location_info := LocationInfo file_0 526 8 526 97.
  Definition loc_221 : location_info := LocationInfo file_0 526 8 526 9.
  Definition loc_222 : location_info := LocationInfo file_0 526 8 526 9.
  Definition loc_223 : location_info := LocationInfo file_0 526 12 526 80.
  Definition loc_224 : location_info := LocationInfo file_0 526 21 526 79.
  Definition loc_225 : location_info := LocationInfo file_0 526 22 526 56.
  Definition loc_226 : location_info := LocationInfo file_0 526 35 526 56.
  Definition loc_227 : location_info := LocationInfo file_0 526 36 526 52.
  Definition loc_228 : location_info := LocationInfo file_0 526 36 526 52.
  Definition loc_229 : location_info := LocationInfo file_0 526 53 526 54.
  Definition loc_230 : location_info := LocationInfo file_0 526 53 526 54.
  Definition loc_231 : location_info := LocationInfo file_0 526 59 526 78.
  Definition loc_232 : location_info := LocationInfo file_0 526 59 526 78.
  Definition loc_233 : location_info := LocationInfo file_0 526 83 526 97.
  Definition loc_234 : location_info := LocationInfo file_0 524 1 524 10.
  Definition loc_235 : location_info := LocationInfo file_0 524 1 524 10.
  Definition loc_236 : location_info := LocationInfo file_0 524 11 524 22.
  Definition loc_237 : location_info := LocationInfo file_0 524 12 524 22.
  Definition loc_238 : location_info := LocationInfo file_0 524 12 524 16.
  Definition loc_239 : location_info := LocationInfo file_0 524 12 524 16.
  Definition loc_240 : location_info := LocationInfo file_0 523 1 523 2.
  Definition loc_241 : location_info := LocationInfo file_0 523 5 523 41.
  Definition loc_242 : location_info := LocationInfo file_0 523 5 523 22.
  Definition loc_243 : location_info := LocationInfo file_0 523 5 523 22.
  Definition loc_244 : location_info := LocationInfo file_0 523 23 523 27.
  Definition loc_245 : location_info := LocationInfo file_0 523 23 523 27.
  Definition loc_246 : location_info := LocationInfo file_0 523 29 523 33.
  Definition loc_247 : location_info := LocationInfo file_0 523 29 523 33.
  Definition loc_248 : location_info := LocationInfo file_0 523 35 523 40.
  Definition loc_249 : location_info := LocationInfo file_0 523 35 523 40.
  Definition loc_250 : location_info := LocationInfo file_0 522 1 522 8.
  Definition loc_251 : location_info := LocationInfo file_0 522 1 522 8.
  Definition loc_252 : location_info := LocationInfo file_0 522 9 522 20.
  Definition loc_253 : location_info := LocationInfo file_0 522 10 522 20.
  Definition loc_254 : location_info := LocationInfo file_0 522 10 522 14.
  Definition loc_255 : location_info := LocationInfo file_0 522 10 522 14.
  Definition loc_258 : location_info := LocationInfo file_0 453 1 453 84.
  Definition loc_259 : location_info := LocationInfo file_0 454 1 454 56.
  Definition loc_260 : location_info := LocationInfo file_0 456 1 456 22.
  Definition loc_261 : location_info := LocationInfo file_0 457 1 457 15.
  Definition loc_262 : location_info := LocationInfo file_0 458 1 458 24.
  Definition loc_263 : location_info := LocationInfo file_0 458 1 458 10.
  Definition loc_264 : location_info := LocationInfo file_0 458 1 458 10.
  Definition loc_265 : location_info := LocationInfo file_0 458 11 458 22.
  Definition loc_266 : location_info := LocationInfo file_0 458 12 458 22.
  Definition loc_267 : location_info := LocationInfo file_0 458 12 458 16.
  Definition loc_268 : location_info := LocationInfo file_0 458 12 458 16.
  Definition loc_269 : location_info := LocationInfo file_0 457 1 457 12.
  Definition loc_270 : location_info := LocationInfo file_0 457 1 457 2.
  Definition loc_271 : location_info := LocationInfo file_0 457 1 457 2.
  Definition loc_272 : location_info := LocationInfo file_0 456 1 456 8.
  Definition loc_273 : location_info := LocationInfo file_0 456 1 456 8.
  Definition loc_274 : location_info := LocationInfo file_0 456 9 456 20.
  Definition loc_275 : location_info := LocationInfo file_0 456 10 456 20.
  Definition loc_276 : location_info := LocationInfo file_0 456 10 456 14.
  Definition loc_277 : location_info := LocationInfo file_0 456 10 456 14.
  Definition loc_278 : location_info := LocationInfo file_0 454 25 454 55.
  Definition loc_279 : location_info := LocationInfo file_0 454 25 454 55.
  Definition loc_280 : location_info := LocationInfo file_0 454 26 454 48.
  Definition loc_281 : location_info := LocationInfo file_0 454 46 454 47.
  Definition loc_282 : location_info := LocationInfo file_0 454 46 454 47.
  Definition loc_285 : location_info := LocationInfo file_0 453 22 453 83.
  Definition loc_286 : location_info := LocationInfo file_0 453 22 453 38.
  Definition loc_287 : location_info := LocationInfo file_0 453 22 453 38.
  Definition loc_288 : location_info := LocationInfo file_0 453 39 453 82.
  Definition loc_289 : location_info := LocationInfo file_0 453 40 453 59.
  Definition loc_290 : location_info := LocationInfo file_0 453 53 453 59.
  Definition loc_291 : location_info := LocationInfo file_0 453 53 453 59.
  Definition loc_292 : location_info := LocationInfo file_0 453 62 453 81.
  Definition loc_293 : location_info := LocationInfo file_0 453 62 453 81.
  Definition loc_298 : location_info := LocationInfo file_0 439 1 439 84.
  Definition loc_299 : location_info := LocationInfo file_0 440 1 440 56.
  Definition loc_300 : location_info := LocationInfo file_0 442 1 442 22.
  Definition loc_301 : location_info := LocationInfo file_0 443 1 444 14.
  Definition loc_302 : location_info := LocationInfo file_0 445 1 445 15.
  Definition loc_303 : location_info := LocationInfo file_0 446 1 447 29.
  Definition loc_304 : location_info := LocationInfo file_0 448 1 448 24.
  Definition loc_305 : location_info := LocationInfo file_0 448 1 448 10.
  Definition loc_306 : location_info := LocationInfo file_0 448 1 448 10.
  Definition loc_307 : location_info := LocationInfo file_0 448 11 448 22.
  Definition loc_308 : location_info := LocationInfo file_0 448 12 448 22.
  Definition loc_309 : location_info := LocationInfo file_0 448 12 448 16.
  Definition loc_310 : location_info := LocationInfo file_0 448 12 448 16.
  Definition loc_311 : location_info := LocationInfo file_0 447 2 447 29.
  Definition loc_312 : location_info := LocationInfo file_0 447 2 447 19.
  Definition loc_313 : location_info := LocationInfo file_0 447 2 447 19.
  Definition loc_314 : location_info := LocationInfo file_0 447 20 447 24.
  Definition loc_315 : location_info := LocationInfo file_0 447 20 447 24.
  Definition loc_316 : location_info := LocationInfo file_0 447 26 447 27.
  Definition loc_317 : location_info := LocationInfo file_0 447 26 447 27.
  Definition loc_319 : location_info := LocationInfo file_0 446 5 446 17.
  Definition loc_321 : location_info := LocationInfo file_0 446 6 446 17.
  Definition loc_322 : location_info := LocationInfo file_0 446 6 446 17.
  Definition loc_323 : location_info := LocationInfo file_0 446 6 446 7.
  Definition loc_324 : location_info := LocationInfo file_0 446 6 446 7.
  Definition loc_325 : location_info := LocationInfo file_0 445 1 445 12.
  Definition loc_326 : location_info := LocationInfo file_0 445 1 445 2.
  Definition loc_327 : location_info := LocationInfo file_0 445 1 445 2.
  Definition loc_328 : location_info := LocationInfo file_0 444 2 444 14.
  Definition loc_329 : location_info := LocationInfo file_0 444 2 444 11.
  Definition loc_330 : location_info := LocationInfo file_0 444 2 444 11.
  Definition loc_332 : location_info := LocationInfo file_0 443 5 443 17.
  Definition loc_334 : location_info := LocationInfo file_0 443 6 443 17.
  Definition loc_335 : location_info := LocationInfo file_0 443 6 443 17.
  Definition loc_336 : location_info := LocationInfo file_0 443 6 443 7.
  Definition loc_337 : location_info := LocationInfo file_0 443 6 443 7.
  Definition loc_338 : location_info := LocationInfo file_0 442 1 442 8.
  Definition loc_339 : location_info := LocationInfo file_0 442 1 442 8.
  Definition loc_340 : location_info := LocationInfo file_0 442 9 442 20.
  Definition loc_341 : location_info := LocationInfo file_0 442 10 442 20.
  Definition loc_342 : location_info := LocationInfo file_0 442 10 442 14.
  Definition loc_343 : location_info := LocationInfo file_0 442 10 442 14.
  Definition loc_344 : location_info := LocationInfo file_0 440 25 440 55.
  Definition loc_345 : location_info := LocationInfo file_0 440 25 440 55.
  Definition loc_346 : location_info := LocationInfo file_0 440 26 440 48.
  Definition loc_347 : location_info := LocationInfo file_0 440 46 440 47.
  Definition loc_348 : location_info := LocationInfo file_0 440 46 440 47.
  Definition loc_351 : location_info := LocationInfo file_0 439 22 439 83.
  Definition loc_352 : location_info := LocationInfo file_0 439 22 439 38.
  Definition loc_353 : location_info := LocationInfo file_0 439 22 439 38.
  Definition loc_354 : location_info := LocationInfo file_0 439 39 439 82.
  Definition loc_355 : location_info := LocationInfo file_0 439 40 439 59.
  Definition loc_356 : location_info := LocationInfo file_0 439 53 439 59.
  Definition loc_357 : location_info := LocationInfo file_0 439 53 439 59.
  Definition loc_358 : location_info := LocationInfo file_0 439 62 439 81.
  Definition loc_359 : location_info := LocationInfo file_0 439 62 439 81.
  Definition loc_364 : location_info := LocationInfo file_0 536 1 537 13.
  Definition loc_365 : location_info := LocationInfo file_0 539 1 539 22.
  Definition loc_366 : location_info := LocationInfo file_0 540 6 540 11.
  Definition loc_367 : location_info := LocationInfo file_0 540 1 541 38.
  Definition loc_368 : location_info := LocationInfo file_0 542 1 542 26.
  Definition loc_369 : location_info := LocationInfo file_0 543 1 543 43.
  Definition loc_370 : location_info := LocationInfo file_0 546 1 546 28.
  Definition loc_371 : location_info := LocationInfo file_0 547 1 547 37.
  Definition loc_372 : location_info := LocationInfo file_0 550 6 550 11.
  Definition loc_373 : location_info := LocationInfo file_0 550 1 554 2.
  Definition loc_374 : location_info := LocationInfo file_0 557 1 557 49.
  Definition loc_375 : location_info := LocationInfo file_0 560 6 560 20.
  Definition loc_376 : location_info := LocationInfo file_0 560 1 563 2.
  Definition loc_377 : location_info := LocationInfo file_0 565 1 565 10.
  Definition loc_378 : location_info := LocationInfo file_0 565 8 565 9.
  Definition loc_379 : location_info := LocationInfo file_0 560 41 563 2.
  Definition loc_380 : location_info := LocationInfo file_0 561 2 561 29.
  Definition loc_381 : location_info := LocationInfo file_0 562 2 562 6.
  Definition loc_382 : location_info := LocationInfo file_0 560 1 563 2.
  Definition loc_383 : location_info := LocationInfo file_0 560 36 560 39.
  Definition loc_384 : location_info := LocationInfo file_0 560 36 560 37.
  Definition loc_385 : location_info := LocationInfo file_0 562 2 562 3.
  Definition loc_386 : location_info := LocationInfo file_0 561 2 561 19.
  Definition loc_387 : location_info := LocationInfo file_0 561 2 561 19.
  Definition loc_388 : location_info := LocationInfo file_0 561 20 561 24.
  Definition loc_389 : location_info := LocationInfo file_0 561 20 561 24.
  Definition loc_390 : location_info := LocationInfo file_0 561 26 561 27.
  Definition loc_391 : location_info := LocationInfo file_0 561 26 561 27.
  Definition loc_392 : location_info := LocationInfo file_0 560 22 560 34.
  Definition loc_393 : location_info := LocationInfo file_0 560 22 560 23.
  Definition loc_394 : location_info := LocationInfo file_0 560 22 560 23.
  Definition loc_395 : location_info := LocationInfo file_0 560 26 560 34.
  Definition loc_396 : location_info := LocationInfo file_0 560 26 560 34.
  Definition loc_397 : location_info := LocationInfo file_0 560 6 560 7.
  Definition loc_398 : location_info := LocationInfo file_0 560 10 560 20.
  Definition loc_399 : location_info := LocationInfo file_0 560 10 560 20.
  Definition loc_400 : location_info := LocationInfo file_0 557 1 557 2.
  Definition loc_401 : location_info := LocationInfo file_0 557 5 557 48.
  Definition loc_402 : location_info := LocationInfo file_0 557 5 557 21.
  Definition loc_403 : location_info := LocationInfo file_0 557 5 557 21.
  Definition loc_404 : location_info := LocationInfo file_0 557 22 557 47.
  Definition loc_405 : location_info := LocationInfo file_0 557 22 557 26.
  Definition loc_406 : location_info := LocationInfo file_0 557 22 557 26.
  Definition loc_407 : location_info := LocationInfo file_0 557 29 557 47.
  Definition loc_408 : location_info := LocationInfo file_0 557 30 557 40.
  Definition loc_409 : location_info := LocationInfo file_0 557 30 557 40.
  Definition loc_410 : location_info := LocationInfo file_0 557 44 557 46.
  Definition loc_411 : location_info := LocationInfo file_0 550 32 554 2.
  Definition loc_412 : location_info := LocationInfo file_0 551 2 551 17.
  Definition loc_413 : location_info := LocationInfo file_0 552 2 552 27.
  Definition loc_414 : location_info := LocationInfo file_0 553 2 553 6.
  Definition loc_415 : location_info := LocationInfo file_0 550 1 554 2.
  Definition loc_416 : location_info := LocationInfo file_0 550 27 550 30.
  Definition loc_417 : location_info := LocationInfo file_0 550 27 550 28.
  Definition loc_418 : location_info := LocationInfo file_0 553 2 553 3.
  Definition loc_419 : location_info := LocationInfo file_0 552 2 552 16.
  Definition loc_420 : location_info := LocationInfo file_0 552 2 552 16.
  Definition loc_421 : location_info := LocationInfo file_0 552 17 552 25.
  Definition loc_422 : location_info := LocationInfo file_0 552 18 552 25.
  Definition loc_423 : location_info := LocationInfo file_0 552 18 552 19.
  Definition loc_424 : location_info := LocationInfo file_0 552 18 552 19.
  Definition loc_425 : location_info := LocationInfo file_0 551 2 551 9.
  Definition loc_426 : location_info := LocationInfo file_0 551 2 551 3.
  Definition loc_427 : location_info := LocationInfo file_0 551 2 551 3.
  Definition loc_428 : location_info := LocationInfo file_0 551 12 551 16.
  Definition loc_429 : location_info := LocationInfo file_0 551 12 551 16.
  Definition loc_430 : location_info := LocationInfo file_0 550 13 550 25.
  Definition loc_431 : location_info := LocationInfo file_0 550 13 550 14.
  Definition loc_432 : location_info := LocationInfo file_0 550 13 550 14.
  Definition loc_433 : location_info := LocationInfo file_0 550 17 550 25.
  Definition loc_434 : location_info := LocationInfo file_0 550 17 550 25.
  Definition loc_435 : location_info := LocationInfo file_0 550 6 550 7.
  Definition loc_436 : location_info := LocationInfo file_0 550 10 550 11.
  Definition loc_437 : location_info := LocationInfo file_0 547 1 547 7.
  Definition loc_438 : location_info := LocationInfo file_0 547 1 547 7.
  Definition loc_439 : location_info := LocationInfo file_0 547 8 547 9.
  Definition loc_440 : location_info := LocationInfo file_0 547 8 547 9.
  Definition loc_441 : location_info := LocationInfo file_0 547 11 547 12.
  Definition loc_442 : location_info := LocationInfo file_0 547 14 547 35.
  Definition loc_443 : location_info := LocationInfo file_0 547 14 547 24.
  Definition loc_444 : location_info := LocationInfo file_0 547 27 547 35.
  Definition loc_445 : location_info := LocationInfo file_0 547 27 547 35.
  Definition loc_446 : location_info := LocationInfo file_0 546 1 546 2.
  Definition loc_447 : location_info := LocationInfo file_0 546 5 546 27.
  Definition loc_448 : location_info := LocationInfo file_0 546 5 546 21.
  Definition loc_449 : location_info := LocationInfo file_0 546 5 546 21.
  Definition loc_450 : location_info := LocationInfo file_0 546 22 546 26.
  Definition loc_451 : location_info := LocationInfo file_0 546 22 546 26.
  Definition loc_452 : location_info := LocationInfo file_0 543 1 543 16.
  Definition loc_453 : location_info := LocationInfo file_0 543 1 543 5.
  Definition loc_454 : location_info := LocationInfo file_0 543 1 543 5.
  Definition loc_455 : location_info := LocationInfo file_0 543 19 543 42.
  Definition loc_456 : location_info := LocationInfo file_0 543 19 543 23.
  Definition loc_457 : location_info := LocationInfo file_0 543 19 543 23.
  Definition loc_458 : location_info := LocationInfo file_0 543 26 543 42.
  Definition loc_459 : location_info := LocationInfo file_0 543 27 543 35.
  Definition loc_460 : location_info := LocationInfo file_0 543 27 543 35.
  Definition loc_461 : location_info := LocationInfo file_0 543 39 543 41.
  Definition loc_462 : location_info := LocationInfo file_0 542 1 542 18.
  Definition loc_463 : location_info := LocationInfo file_0 542 1 542 5.
  Definition loc_464 : location_info := LocationInfo file_0 542 1 542 5.
  Definition loc_465 : location_info := LocationInfo file_0 542 21 542 25.
  Definition loc_466 : location_info := LocationInfo file_0 542 21 542 25.
  Definition loc_467 : location_info := LocationInfo file_0 540 1 541 38.
  Definition loc_468 : location_info := LocationInfo file_0 541 2 541 38.
  Definition loc_469 : location_info := LocationInfo file_0 540 1 541 38.
  Definition loc_470 : location_info := LocationInfo file_0 540 23 540 26.
  Definition loc_471 : location_info := LocationInfo file_0 540 23 540 24.
  Definition loc_472 : location_info := LocationInfo file_0 541 2 541 16.
  Definition loc_473 : location_info := LocationInfo file_0 541 2 541 16.
  Definition loc_474 : location_info := LocationInfo file_0 541 17 541 36.
  Definition loc_475 : location_info := LocationInfo file_0 541 18 541 36.
  Definition loc_476 : location_info := LocationInfo file_0 541 18 541 36.
  Definition loc_477 : location_info := LocationInfo file_0 541 18 541 33.
  Definition loc_478 : location_info := LocationInfo file_0 541 18 541 33.
  Definition loc_479 : location_info := LocationInfo file_0 541 18 541 22.
  Definition loc_480 : location_info := LocationInfo file_0 541 18 541 22.
  Definition loc_481 : location_info := LocationInfo file_0 541 34 541 35.
  Definition loc_482 : location_info := LocationInfo file_0 541 34 541 35.
  Definition loc_483 : location_info := LocationInfo file_0 540 13 540 21.
  Definition loc_484 : location_info := LocationInfo file_0 540 13 540 14.
  Definition loc_485 : location_info := LocationInfo file_0 540 13 540 14.
  Definition loc_486 : location_info := LocationInfo file_0 540 18 540 21.
  Definition loc_487 : location_info := LocationInfo file_0 540 6 540 7.
  Definition loc_488 : location_info := LocationInfo file_0 540 10 540 11.
  Definition loc_489 : location_info := LocationInfo file_0 539 1 539 8.
  Definition loc_490 : location_info := LocationInfo file_0 539 1 539 8.
  Definition loc_491 : location_info := LocationInfo file_0 539 9 539 20.
  Definition loc_492 : location_info := LocationInfo file_0 539 10 539 20.
  Definition loc_493 : location_info := LocationInfo file_0 539 10 539 14.
  Definition loc_494 : location_info := LocationInfo file_0 539 10 539 14.
  Definition loc_495 : location_info := LocationInfo file_0 537 2 537 13.
  Definition loc_496 : location_info := LocationInfo file_0 537 9 537 12.
  Definition loc_497 : location_info := LocationInfo file_0 537 10 537 12.
  Definition loc_499 : location_info := LocationInfo file_0 536 5 536 16.
  Definition loc_500 : location_info := LocationInfo file_0 536 5 536 9.
  Definition loc_501 : location_info := LocationInfo file_0 536 5 536 9.
  Definition loc_502 : location_info := LocationInfo file_0 536 12 536 16.
  Definition loc_505 : location_info := LocationInfo file_0 373 1 373 15.
  Definition loc_506 : location_info := LocationInfo file_0 373 15 373 2.
  Definition loc_507 : location_info := LocationInfo file_0 374 1 374 40.
  Definition loc_508 : location_info := LocationInfo file_0 376 1 376 25.
  Definition loc_509 : location_info := LocationInfo file_0 377 1 378 24.
  Definition loc_510 : location_info := LocationInfo file_0 380 1 380 31.
  Definition loc_511 : location_info := LocationInfo file_0 380 8 380 30.
  Definition loc_512 : location_info := LocationInfo file_0 380 8 380 24.
  Definition loc_513 : location_info := LocationInfo file_0 380 8 380 24.
  Definition loc_514 : location_info := LocationInfo file_0 380 25 380 29.
  Definition loc_515 : location_info := LocationInfo file_0 380 25 380 29.
  Definition loc_516 : location_info := LocationInfo file_0 378 2 378 24.
  Definition loc_517 : location_info := LocationInfo file_0 378 9 378 23.
  Definition loc_520 : location_info := LocationInfo file_0 377 5 377 29.
  Definition loc_521 : location_info := LocationInfo file_0 377 5 377 9.
  Definition loc_522 : location_info := LocationInfo file_0 377 5 377 9.
  Definition loc_523 : location_info := LocationInfo file_0 377 12 377 29.
  Definition loc_524 : location_info := LocationInfo file_0 377 12 377 29.
  Definition loc_525 : location_info := LocationInfo file_0 377 12 377 16.
  Definition loc_526 : location_info := LocationInfo file_0 377 12 377 16.
  Definition loc_527 : location_info := LocationInfo file_0 377 33 377 56.
  Definition loc_528 : location_info := LocationInfo file_0 377 33 377 37.
  Definition loc_529 : location_info := LocationInfo file_0 377 33 377 37.
  Definition loc_530 : location_info := LocationInfo file_0 377 41 377 56.
  Definition loc_531 : location_info := LocationInfo file_0 377 41 377 56.
  Definition loc_532 : location_info := LocationInfo file_0 377 41 377 45.
  Definition loc_533 : location_info := LocationInfo file_0 377 41 377 45.
  Definition loc_534 : location_info := LocationInfo file_0 376 1 376 5.
  Definition loc_535 : location_info := LocationInfo file_0 376 1 376 24.
  Definition loc_536 : location_info := LocationInfo file_0 376 1 376 5.
  Definition loc_537 : location_info := LocationInfo file_0 376 1 376 5.
  Definition loc_538 : location_info := LocationInfo file_0 376 9 376 24.
  Definition loc_539 : location_info := LocationInfo file_0 376 10 376 14.
  Definition loc_540 : location_info := LocationInfo file_0 376 18 376 23.
  Definition loc_541 : location_info := LocationInfo file_0 376 18 376 23.
  Definition loc_542 : location_info := LocationInfo file_0 374 20 374 39.
  Definition loc_543 : location_info := LocationInfo file_0 374 20 374 36.
  Definition loc_544 : location_info := LocationInfo file_0 374 20 374 36.
  Definition loc_545 : location_info := LocationInfo file_0 374 37 374 38.
  Definition loc_546 : location_info := LocationInfo file_0 374 37 374 38.
  Definition loc_549 : location_info := LocationInfo file_0 373 1 373 14.
  Definition loc_550 : location_info := LocationInfo file_0 373 2 373 14.
  Definition loc_551 : location_info := LocationInfo file_0 373 3 373 7.
  Definition loc_552 : location_info := LocationInfo file_0 373 3 373 7.
  Definition loc_555 : location_info := LocationInfo file_0 397 1 397 15.
  Definition loc_556 : location_info := LocationInfo file_0 397 15 397 2.
  Definition loc_557 : location_info := LocationInfo file_0 398 1 398 31.
  Definition loc_558 : location_info := LocationInfo file_0 401 1 401 31.
  Definition loc_559 : location_info := LocationInfo file_0 409 1 428 2.
  Definition loc_560 : location_info := LocationInfo file_0 429 1 429 15.
  Definition loc_561 : location_info := LocationInfo file_0 429 15 429 2.
  Definition loc_562 : location_info := LocationInfo file_0 431 1 431 18.
  Definition loc_563 : location_info := LocationInfo file_0 434 1 434 45.
  Definition loc_564 : location_info := LocationInfo file_0 434 1 434 9.
  Definition loc_565 : location_info := LocationInfo file_0 434 1 434 9.
  Definition loc_566 : location_info := LocationInfo file_0 434 10 434 18.
  Definition loc_567 : location_info := LocationInfo file_0 434 11 434 18.
  Definition loc_568 : location_info := LocationInfo file_0 434 11 434 12.
  Definition loc_569 : location_info := LocationInfo file_0 434 11 434 12.
  Definition loc_570 : location_info := LocationInfo file_0 434 20 434 43.
  Definition loc_571 : location_info := LocationInfo file_0 434 21 434 43.
  Definition loc_572 : location_info := LocationInfo file_0 434 21 434 43.
  Definition loc_573 : location_info := LocationInfo file_0 434 21 434 36.
  Definition loc_574 : location_info := LocationInfo file_0 434 21 434 36.
  Definition loc_575 : location_info := LocationInfo file_0 434 21 434 25.
  Definition loc_576 : location_info := LocationInfo file_0 434 21 434 25.
  Definition loc_577 : location_info := LocationInfo file_0 434 37 434 42.
  Definition loc_578 : location_info := LocationInfo file_0 434 37 434 42.
  Definition loc_579 : location_info := LocationInfo file_0 431 1 431 9.
  Definition loc_580 : location_info := LocationInfo file_0 431 1 431 2.
  Definition loc_581 : location_info := LocationInfo file_0 431 1 431 2.
  Definition loc_582 : location_info := LocationInfo file_0 431 12 431 17.
  Definition loc_583 : location_info := LocationInfo file_0 431 12 431 17.
  Definition loc_584 : location_info := LocationInfo file_0 429 1 429 14.
  Definition loc_585 : location_info := LocationInfo file_0 429 2 429 14.
  Definition loc_586 : location_info := LocationInfo file_0 429 3 429 7.
  Definition loc_587 : location_info := LocationInfo file_0 429 3 429 7.
  Definition loc_588 : location_info := LocationInfo file_0 409 30 428 2.
  Definition loc_589 : location_info := LocationInfo file_0 411 2 411 39.
  Definition loc_590 : location_info := LocationInfo file_0 412 2 412 16.
  Definition loc_591 : location_info := LocationInfo file_0 412 16 412 3.
  Definition loc_592 : location_info := LocationInfo file_0 415 2 416 9.
  Definition loc_593 : location_info := LocationInfo file_0 419 2 419 30.
  Definition loc_594 : location_info := LocationInfo file_0 420 2 420 36.
  Definition loc_595 : location_info := LocationInfo file_0 423 2 427 3.
  Definition loc_596 : location_info := LocationInfo file_0 409 1 428 2.
  Definition loc_597 : location_info := LocationInfo file_0 409 21 409 28.
  Definition loc_598 : location_info := LocationInfo file_0 409 21 409 26.
  Definition loc_599 : location_info := LocationInfo file_0 423 17 425 3.
  Definition loc_600 : location_info := LocationInfo file_0 424 3 424 9.
  Definition loc_601 : location_info := LocationInfo file_0 424 3 424 4.
  Definition loc_602 : location_info := LocationInfo file_0 424 7 424 8.
  Definition loc_603 : location_info := LocationInfo file_0 424 7 424 8.
  Definition loc_604 : location_info := LocationInfo file_0 425 9 427 3.
  Definition loc_605 : location_info := LocationInfo file_0 426 3 426 13.
  Definition loc_606 : location_info := LocationInfo file_0 426 3 426 4.
  Definition loc_607 : location_info := LocationInfo file_0 426 7 426 12.
  Definition loc_608 : location_info := LocationInfo file_0 426 7 426 12.
  Definition loc_609 : location_info := LocationInfo file_0 423 6 423 15.
  Definition loc_610 : location_info := LocationInfo file_0 423 6 423 7.
  Definition loc_611 : location_info := LocationInfo file_0 423 6 423 7.
  Definition loc_612 : location_info := LocationInfo file_0 423 10 423 15.
  Definition loc_613 : location_info := LocationInfo file_0 423 10 423 15.
  Definition loc_614 : location_info := LocationInfo file_0 420 2 420 14.
  Definition loc_615 : location_info := LocationInfo file_0 420 2 420 7.
  Definition loc_616 : location_info := LocationInfo file_0 420 2 420 7.
  Definition loc_617 : location_info := LocationInfo file_0 420 17 420 35.
  Definition loc_618 : location_info := LocationInfo file_0 419 2 419 15.
  Definition loc_619 : location_info := LocationInfo file_0 419 2 419 15.
  Definition loc_620 : location_info := LocationInfo file_0 419 16 419 28.
  Definition loc_621 : location_info := LocationInfo file_0 419 17 419 28.
  Definition loc_622 : location_info := LocationInfo file_0 419 17 419 22.
  Definition loc_623 : location_info := LocationInfo file_0 419 17 419 22.
  Definition loc_624 : location_info := LocationInfo file_0 416 3 416 9.
  Definition loc_628 : location_info := LocationInfo file_0 415 6 415 29.
  Definition loc_629 : location_info := LocationInfo file_0 415 6 415 11.
  Definition loc_630 : location_info := LocationInfo file_0 415 6 415 11.
  Definition loc_631 : location_info := LocationInfo file_0 415 15 415 29.
  Definition loc_632 : location_info := LocationInfo file_0 415 33 415 57.
  Definition loc_633 : location_info := LocationInfo file_0 415 33 415 43.
  Definition loc_634 : location_info := LocationInfo file_0 415 33 415 43.
  Definition loc_635 : location_info := LocationInfo file_0 415 44 415 56.
  Definition loc_636 : location_info := LocationInfo file_0 415 45 415 56.
  Definition loc_637 : location_info := LocationInfo file_0 415 45 415 50.
  Definition loc_638 : location_info := LocationInfo file_0 415 45 415 50.
  Definition loc_639 : location_info := LocationInfo file_0 415 61 415 82.
  Definition loc_640 : location_info := LocationInfo file_0 415 61 415 73.
  Definition loc_641 : location_info := LocationInfo file_0 415 61 415 73.
  Definition loc_642 : location_info := LocationInfo file_0 415 61 415 66.
  Definition loc_643 : location_info := LocationInfo file_0 415 61 415 66.
  Definition loc_644 : location_info := LocationInfo file_0 415 77 415 82.
  Definition loc_645 : location_info := LocationInfo file_0 415 77 415 82.
  Definition loc_646 : location_info := LocationInfo file_0 412 2 412 15.
  Definition loc_647 : location_info := LocationInfo file_0 412 3 412 15.
  Definition loc_648 : location_info := LocationInfo file_0 412 4 412 8.
  Definition loc_649 : location_info := LocationInfo file_0 412 4 412 8.
  Definition loc_650 : location_info := LocationInfo file_0 411 2 411 7.
  Definition loc_651 : location_info := LocationInfo file_0 411 10 411 38.
  Definition loc_652 : location_info := LocationInfo file_0 411 10 411 22.
  Definition loc_653 : location_info := LocationInfo file_0 411 10 411 22.
  Definition loc_654 : location_info := LocationInfo file_0 411 23 411 27.
  Definition loc_655 : location_info := LocationInfo file_0 411 23 411 27.
  Definition loc_656 : location_info := LocationInfo file_0 411 29 411 30.
  Definition loc_657 : location_info := LocationInfo file_0 411 29 411 30.
  Definition loc_658 : location_info := LocationInfo file_0 411 32 411 37.
  Definition loc_659 : location_info := LocationInfo file_0 411 32 411 37.
  Definition loc_660 : location_info := LocationInfo file_0 409 8 409 19.
  Definition loc_661 : location_info := LocationInfo file_0 409 8 409 13.
  Definition loc_662 : location_info := LocationInfo file_0 409 8 409 13.
  Definition loc_663 : location_info := LocationInfo file_0 409 16 409 19.
  Definition loc_664 : location_info := LocationInfo file_0 401 1 401 9.
  Definition loc_665 : location_info := LocationInfo file_0 401 1 401 2.
  Definition loc_666 : location_info := LocationInfo file_0 401 1 401 2.
  Definition loc_667 : location_info := LocationInfo file_0 401 12 401 30.
  Definition loc_668 : location_info := LocationInfo file_0 398 22 398 30.
  Definition loc_669 : location_info := LocationInfo file_0 398 22 398 30.
  Definition loc_670 : location_info := LocationInfo file_0 398 22 398 23.
  Definition loc_671 : location_info := LocationInfo file_0 398 22 398 23.
  Definition loc_674 : location_info := LocationInfo file_0 397 1 397 14.
  Definition loc_675 : location_info := LocationInfo file_0 397 2 397 14.
  Definition loc_676 : location_info := LocationInfo file_0 397 3 397 7.
  Definition loc_677 : location_info := LocationInfo file_0 397 3 397 7.
  Definition loc_680 : location_info := LocationInfo file_0 468 1 469 24.
  Definition loc_681 : location_info := LocationInfo file_0 471 1 471 25.
  Definition loc_682 : location_info := LocationInfo file_0 474 1 479 2.
  Definition loc_683 : location_info := LocationInfo file_0 481 1 481 17.
  Definition loc_684 : location_info := LocationInfo file_0 483 1 483 10.
  Definition loc_685 : location_info := LocationInfo file_0 483 8 483 9.
  Definition loc_686 : location_info := LocationInfo file_0 483 8 483 9.
  Definition loc_687 : location_info := LocationInfo file_0 481 1 481 12.
  Definition loc_688 : location_info := LocationInfo file_0 481 1 481 2.
  Definition loc_689 : location_info := LocationInfo file_0 481 1 481 2.
  Definition loc_690 : location_info := LocationInfo file_0 481 15 481 16.
  Definition loc_691 : location_info := LocationInfo file_0 474 1 479 2.
  Definition loc_692 : location_info := LocationInfo file_0 474 26 479 2.
  Definition loc_693 : location_info := LocationInfo file_0 475 2 475 13.
  Definition loc_694 : location_info := LocationInfo file_0 476 2 476 42.
  Definition loc_695 : location_info := LocationInfo file_0 477 2 477 26.
  Definition loc_696 : location_info := LocationInfo file_0 478 2 478 62.
  Definition loc_697 : location_info := LocationInfo file_0 474 1 479 2.
  Definition loc_698 : location_info := LocationInfo file_0 474 1 479 2.
  Definition loc_699 : location_info := LocationInfo file_0 478 2 478 15.
  Definition loc_700 : location_info := LocationInfo file_0 478 2 478 15.
  Definition loc_701 : location_info := LocationInfo file_0 478 16 478 28.
  Definition loc_702 : location_info := LocationInfo file_0 478 17 478 28.
  Definition loc_703 : location_info := LocationInfo file_0 478 17 478 22.
  Definition loc_704 : location_info := LocationInfo file_0 478 17 478 22.
  Definition loc_705 : location_info := LocationInfo file_0 478 30 478 60.
  Definition loc_706 : location_info := LocationInfo file_0 478 31 478 60.
  Definition loc_707 : location_info := LocationInfo file_0 478 31 478 60.
  Definition loc_708 : location_info := LocationInfo file_0 478 31 478 46.
  Definition loc_709 : location_info := LocationInfo file_0 478 31 478 46.
  Definition loc_710 : location_info := LocationInfo file_0 478 31 478 35.
  Definition loc_711 : location_info := LocationInfo file_0 478 31 478 35.
  Definition loc_712 : location_info := LocationInfo file_0 478 47 478 59.
  Definition loc_713 : location_info := LocationInfo file_0 478 47 478 59.
  Definition loc_714 : location_info := LocationInfo file_0 478 47 478 52.
  Definition loc_715 : location_info := LocationInfo file_0 478 47 478 52.
  Definition loc_716 : location_info := LocationInfo file_0 477 2 477 14.
  Definition loc_717 : location_info := LocationInfo file_0 477 2 477 7.
  Definition loc_718 : location_info := LocationInfo file_0 477 2 477 7.
  Definition loc_719 : location_info := LocationInfo file_0 477 17 477 25.
  Definition loc_720 : location_info := LocationInfo file_0 477 17 477 25.
  Definition loc_721 : location_info := LocationInfo file_0 477 17 477 18.
  Definition loc_722 : location_info := LocationInfo file_0 477 17 477 18.
  Definition loc_723 : location_info := LocationInfo file_0 476 2 476 7.
  Definition loc_724 : location_info := LocationInfo file_0 476 10 476 41.
  Definition loc_725 : location_info := LocationInfo file_0 476 10 476 22.
  Definition loc_726 : location_info := LocationInfo file_0 476 10 476 22.
  Definition loc_727 : location_info := LocationInfo file_0 476 23 476 27.
  Definition loc_728 : location_info := LocationInfo file_0 476 23 476 27.
  Definition loc_729 : location_info := LocationInfo file_0 476 29 476 30.
  Definition loc_730 : location_info := LocationInfo file_0 476 29 476 30.
  Definition loc_731 : location_info := LocationInfo file_0 476 32 476 40.
  Definition loc_732 : location_info := LocationInfo file_0 476 32 476 40.
  Definition loc_733 : location_info := LocationInfo file_0 476 32 476 33.
  Definition loc_734 : location_info := LocationInfo file_0 476 32 476 33.
  Definition loc_735 : location_info := LocationInfo file_0 475 2 475 10.
  Definition loc_736 : location_info := LocationInfo file_0 475 2 475 3.
  Definition loc_737 : location_info := LocationInfo file_0 475 2 475 3.
  Definition loc_738 : location_info := LocationInfo file_0 474 8 474 24.
  Definition loc_739 : location_info := LocationInfo file_0 474 8 474 16.
  Definition loc_740 : location_info := LocationInfo file_0 474 8 474 16.
  Definition loc_741 : location_info := LocationInfo file_0 474 8 474 9.
  Definition loc_742 : location_info := LocationInfo file_0 474 8 474 9.
  Definition loc_743 : location_info := LocationInfo file_0 474 19 474 24.
  Definition loc_744 : location_info := LocationInfo file_0 474 19 474 24.
  Definition loc_745 : location_info := LocationInfo file_0 471 1 471 14.
  Definition loc_746 : location_info := LocationInfo file_0 471 1 471 14.
  Definition loc_747 : location_info := LocationInfo file_0 471 15 471 23.
  Definition loc_748 : location_info := LocationInfo file_0 471 16 471 23.
  Definition loc_749 : location_info := LocationInfo file_0 471 16 471 17.
  Definition loc_750 : location_info := LocationInfo file_0 471 16 471 17.
  Definition loc_751 : location_info := LocationInfo file_0 469 2 469 24.
  Definition loc_752 : location_info := LocationInfo file_0 469 9 469 23.
  Definition loc_755 : location_info := LocationInfo file_0 468 5 468 35.
  Definition loc_756 : location_info := LocationInfo file_0 468 5 468 13.
  Definition loc_757 : location_info := LocationInfo file_0 468 5 468 13.
  Definition loc_758 : location_info := LocationInfo file_0 468 5 468 6.
  Definition loc_759 : location_info := LocationInfo file_0 468 5 468 6.
  Definition loc_760 : location_info := LocationInfo file_0 468 17 468 35.
  Definition loc_761 : location_info := LocationInfo file_0 468 39 468 55.
  Definition loc_762 : location_info := LocationInfo file_0 468 39 468 47.
  Definition loc_763 : location_info := LocationInfo file_0 468 39 468 47.
  Definition loc_764 : location_info := LocationInfo file_0 468 39 468 40.
  Definition loc_765 : location_info := LocationInfo file_0 468 39 468 40.
  Definition loc_766 : location_info := LocationInfo file_0 468 50 468 55.
  Definition loc_767 : location_info := LocationInfo file_0 468 50 468 55.
  Definition loc_770 : location_info := LocationInfo file_0 490 6 490 11.
  Definition loc_771 : location_info := LocationInfo file_0 490 1 491 112.
  Definition loc_772 : location_info := LocationInfo file_0 490 1 491 112.
  Definition loc_773 : location_info := LocationInfo file_0 491 2 491 112.
  Definition loc_774 : location_info := LocationInfo file_0 490 1 491 112.
  Definition loc_775 : location_info := LocationInfo file_0 490 34 490 37.
  Definition loc_776 : location_info := LocationInfo file_0 490 34 490 35.
  Definition loc_777 : location_info := LocationInfo file_0 491 2 491 12.
  Definition loc_778 : location_info := LocationInfo file_0 491 2 491 12.
  Definition loc_779 : location_info := LocationInfo file_0 491 13 491 110.
  Definition loc_780 : location_info := LocationInfo file_0 491 13 491 98.
  Definition loc_781 : location_info := LocationInfo file_0 491 30 491 98.
  Definition loc_782 : location_info := LocationInfo file_0 491 39 491 97.
  Definition loc_783 : location_info := LocationInfo file_0 491 40 491 74.
  Definition loc_784 : location_info := LocationInfo file_0 491 53 491 74.
  Definition loc_785 : location_info := LocationInfo file_0 491 54 491 70.
  Definition loc_786 : location_info := LocationInfo file_0 491 54 491 70.
  Definition loc_787 : location_info := LocationInfo file_0 491 71 491 72.
  Definition loc_788 : location_info := LocationInfo file_0 491 71 491 72.
  Definition loc_789 : location_info := LocationInfo file_0 491 77 491 96.
  Definition loc_790 : location_info := LocationInfo file_0 491 77 491 96.
  Definition loc_791 : location_info := LocationInfo file_0 491 101 491 110.
  Definition loc_792 : location_info := LocationInfo file_0 491 102 491 103.
  Definition loc_793 : location_info := LocationInfo file_0 491 102 491 103.
  Definition loc_794 : location_info := LocationInfo file_0 491 107 491 109.
  Definition loc_795 : location_info := LocationInfo file_0 490 13 490 32.
  Definition loc_796 : location_info := LocationInfo file_0 490 13 490 14.
  Definition loc_797 : location_info := LocationInfo file_0 490 13 490 14.
  Definition loc_798 : location_info := LocationInfo file_0 490 17 490 32.
  Definition loc_799 : location_info := LocationInfo file_0 490 18 490 19.
  Definition loc_800 : location_info := LocationInfo file_0 490 23 490 31.
  Definition loc_801 : location_info := LocationInfo file_0 490 23 490 31.
  Definition loc_802 : location_info := LocationInfo file_0 490 23 490 24.
  Definition loc_803 : location_info := LocationInfo file_0 490 23 490 24.
  Definition loc_804 : location_info := LocationInfo file_0 490 6 490 7.
  Definition loc_805 : location_info := LocationInfo file_0 490 10 490 11.
  Definition loc_808 : location_info := LocationInfo file_0 499 1 499 24.
  Definition loc_809 : location_info := LocationInfo file_0 503 1 504 6.
  Definition loc_810 : location_info := LocationInfo file_0 505 1 506 24.
  Definition loc_811 : location_info := LocationInfo file_0 509 1 509 99.
  Definition loc_812 : location_info := LocationInfo file_0 510 1 510 40.
  Definition loc_813 : location_info := LocationInfo file_0 512 1 513 20.
  Definition loc_814 : location_info := LocationInfo file_0 515 1 515 10.
  Definition loc_815 : location_info := LocationInfo file_0 515 8 515 9.
  Definition loc_816 : location_info := LocationInfo file_0 515 8 515 9.
  Definition loc_817 : location_info := LocationInfo file_0 513 2 513 20.
  Definition loc_818 : location_info := LocationInfo file_0 513 2 513 16.
  Definition loc_819 : location_info := LocationInfo file_0 513 2 513 16.
  Definition loc_820 : location_info := LocationInfo file_0 513 17 513 18.
  Definition loc_821 : location_info := LocationInfo file_0 513 17 513 18.
  Definition loc_823 : location_info := LocationInfo file_0 512 5 512 13.
  Definition loc_824 : location_info := LocationInfo file_0 512 5 512 9.
  Definition loc_825 : location_info := LocationInfo file_0 512 5 512 9.
  Definition loc_826 : location_info := LocationInfo file_0 512 12 512 13.
  Definition loc_827 : location_info := LocationInfo file_0 510 1 510 2.
  Definition loc_828 : location_info := LocationInfo file_0 510 5 510 39.
  Definition loc_829 : location_info := LocationInfo file_0 510 5 510 23.
  Definition loc_830 : location_info := LocationInfo file_0 510 5 510 23.
  Definition loc_831 : location_info := LocationInfo file_0 510 24 510 28.
  Definition loc_832 : location_info := LocationInfo file_0 510 24 510 28.
  Definition loc_833 : location_info := LocationInfo file_0 510 30 510 31.
  Definition loc_834 : location_info := LocationInfo file_0 510 30 510 31.
  Definition loc_835 : location_info := LocationInfo file_0 510 33 510 38.
  Definition loc_836 : location_info := LocationInfo file_0 510 33 510 38.
  Definition loc_837 : location_info := LocationInfo file_0 509 1 509 2.
  Definition loc_838 : location_info := LocationInfo file_0 509 5 509 98.
  Definition loc_839 : location_info := LocationInfo file_0 509 24 509 98.
  Definition loc_840 : location_info := LocationInfo file_0 509 26 509 63.
  Definition loc_841 : location_info := LocationInfo file_0 509 34 509 63.
  Definition loc_842 : location_info := LocationInfo file_0 509 34 509 63.
  Definition loc_843 : location_info := LocationInfo file_0 509 35 509 56.
  Definition loc_844 : location_info := LocationInfo file_0 509 37 509 55.
  Definition loc_845 : location_info := LocationInfo file_0 509 37 509 55.
  Definition loc_846 : location_info := LocationInfo file_0 509 37 509 52.
  Definition loc_847 : location_info := LocationInfo file_0 509 37 509 52.
  Definition loc_848 : location_info := LocationInfo file_0 509 37 509 41.
  Definition loc_849 : location_info := LocationInfo file_0 509 37 509 41.
  Definition loc_850 : location_info := LocationInfo file_0 509 53 509 54.
  Definition loc_851 : location_info := LocationInfo file_0 509 53 509 54.
  Definition loc_852 : location_info := LocationInfo file_0 509 66 509 96.
  Definition loc_853 : location_info := LocationInfo file_0 506 2 506 24.
  Definition loc_854 : location_info := LocationInfo file_0 506 9 506 23.
  Definition loc_856 : location_info := LocationInfo file_0 505 5 505 12.
  Definition loc_857 : location_info := LocationInfo file_0 505 5 505 6.
  Definition loc_858 : location_info := LocationInfo file_0 505 5 505 6.
  Definition loc_859 : location_info := LocationInfo file_0 505 9 505 12.
  Definition loc_860 : location_info := LocationInfo file_0 503 1 504 6.
  Definition loc_861 : location_info := LocationInfo file_0 504 2 504 6.
  Definition loc_862 : location_info := LocationInfo file_0 503 1 504 6.
  Definition loc_863 : location_info := LocationInfo file_0 503 1 504 6.
  Definition loc_864 : location_info := LocationInfo file_0 504 2 504 3.
  Definition loc_866 : location_info := LocationInfo file_0 503 8 503 16.
  Definition loc_867 : location_info := LocationInfo file_0 503 8 503 9.
  Definition loc_868 : location_info := LocationInfo file_0 503 8 503 9.
  Definition loc_869 : location_info := LocationInfo file_0 503 13 503 16.
  Definition loc_870 : location_info := LocationInfo file_0 503 20 503 51.
  Definition loc_871 : location_info := LocationInfo file_0 503 20 503 30.
  Definition loc_872 : location_info := LocationInfo file_0 503 20 503 30.
  Definition loc_873 : location_info := LocationInfo file_0 503 31 503 50.
  Definition loc_874 : location_info := LocationInfo file_0 503 32 503 50.
  Definition loc_875 : location_info := LocationInfo file_0 503 32 503 50.
  Definition loc_876 : location_info := LocationInfo file_0 503 32 503 47.
  Definition loc_877 : location_info := LocationInfo file_0 503 32 503 47.
  Definition loc_878 : location_info := LocationInfo file_0 503 32 503 36.
  Definition loc_879 : location_info := LocationInfo file_0 503 32 503 36.
  Definition loc_880 : location_info := LocationInfo file_0 503 48 503 49.
  Definition loc_881 : location_info := LocationInfo file_0 503 48 503 49.
  Definition loc_882 : location_info := LocationInfo file_0 499 18 499 23.
  Definition loc_883 : location_info := LocationInfo file_0 499 18 499 23.

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
        Return (LocInfoE loc_186 ((LocInfoE loc_187 (UnOp (CastOp $ IntOp u64) (IntOp ptrdiff_t) (LocInfoE loc_188 ((LocInfoE loc_189 (use{void*} (LocInfoE loc_190 ("page")))) sub_ptr{layout_of struct_hyp_page, PtrOp, PtrOp} (LocInfoE loc_191 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_192 (use{void*} (LocInfoE loc_193 (global___hyp_vmemmap)))))))))) <<{IntOp u64, IntOp u64} (LocInfoE loc_194 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_194 (i2v 12 i32))))))
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
        locinfo: loc_499 ;
        if: LocInfoE loc_499 (UnOp (CastOp $ IntOp bool_it) (IntOp u64) (LocInfoE loc_499 ((LocInfoE loc_500 (use{it_layout u64} (LocInfoE loc_501 ("phys")))) %{IntOp u64, IntOp u64} (LocInfoE loc_502 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_502 (i2v 4096 i32)))))))
        then
        locinfo: loc_495 ;
          Goto "#11"
        else
        locinfo: loc_365 ;
          Goto "#12"
      ]> $
      <[ "#1" :=
        locinfo: loc_365 ;
        expr: (LocInfoE loc_365 (Call (LocInfoE loc_490 (global_sl_init)) [@{expr} LocInfoE loc_491 (&(LocInfoE loc_492 ((LocInfoE loc_493 (!{void*} (LocInfoE loc_494 ("pool")))) at{struct_hyp_pool} "lock"))) ])) ;
        locinfo: loc_366 ;
        LocInfoE loc_487 ("i") <-{ it_layout i32 }
          LocInfoE loc_488 (i2v 0 i32) ;
        locinfo: loc_367 ;
        Goto "#2"
      ]> $
      <[ "#10" :=
        locinfo: loc_377 ;
        Return (LocInfoE loc_378 (i2v 0 i32))
      ]> $
      <[ "#11" :=
        locinfo: loc_495 ;
        Return (LocInfoE loc_496 (UnOp NegOp (IntOp i32) (LocInfoE loc_497 (i2v 22 i32))))
      ]> $
      <[ "#12" :=
        locinfo: loc_365 ;
        Goto "#1"
      ]> $
      <[ "#2" :=
        locinfo: loc_483 ;
        if: LocInfoE loc_483 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_483 ((LocInfoE loc_484 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_484 (use{it_layout i32} (LocInfoE loc_485 ("i")))))) ≤{IntOp u32, IntOp u32} (LocInfoE loc_486 (i2v 11 u32)))))
        then
        locinfo: loc_468 ;
          Goto "#3"
        else
        locinfo: loc_368 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_468 ;
        expr: (LocInfoE loc_468 (Call (LocInfoE loc_473 (global_INIT_LIST_HEAD)) [@{expr} LocInfoE loc_474 (&(LocInfoE loc_476 ((LocInfoE loc_478 ((LocInfoE loc_479 (!{void*} (LocInfoE loc_480 ("pool")))) at{struct_hyp_pool} "free_area")) at_offset{layout_of struct_list_head, PtrOp, IntOp i32} (LocInfoE loc_481 (use{it_layout i32} (LocInfoE loc_482 ("i"))))))) ])) ;
        locinfo: loc_469 ;
        Goto "continue58"
      ]> $
      <[ "#4" :=
        locinfo: loc_368 ;
        LocInfoE loc_462 ((LocInfoE loc_463 (!{void*} (LocInfoE loc_464 ("pool")))) at{struct_hyp_pool} "range_start") <-{ it_layout u64 }
          LocInfoE loc_465 (use{it_layout u64} (LocInfoE loc_466 ("phys"))) ;
        locinfo: loc_369 ;
        LocInfoE loc_452 ((LocInfoE loc_453 (!{void*} (LocInfoE loc_454 ("pool")))) at{struct_hyp_pool} "range_end") <-{ it_layout u64 }
          LocInfoE loc_455 ((LocInfoE loc_456 (use{it_layout u64} (LocInfoE loc_457 ("phys")))) +{IntOp u64, IntOp u64} (LocInfoE loc_458 (UnOp (CastOp $ IntOp u64) (IntOp u32) (LocInfoE loc_458 ((LocInfoE loc_459 (use{it_layout u32} (LocInfoE loc_460 ("nr_pages")))) <<{IntOp u32, IntOp u32} (LocInfoE loc_461 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_461 (i2v 12 i32))))))))) ;
        locinfo: loc_370 ;
        LocInfoE loc_446 ("p") <-{ void* }
          LocInfoE loc_447 (Call (LocInfoE loc_449 (global_hyp_phys_to_page)) [@{expr} LocInfoE loc_450 (use{it_layout u64} (LocInfoE loc_451 ("phys"))) ]) ;
        locinfo: loc_371 ;
        expr: (LocInfoE loc_371 (Call (LocInfoE loc_438 (global_memset)) [@{expr} LocInfoE loc_439 (use{void*} (LocInfoE loc_440 ("p"))) ;
        LocInfoE loc_441 (i2v 0 i32) ;
        LocInfoE loc_442 ((LocInfoE loc_443 (i2v (layout_of struct_hyp_page).(ly_size) size_t)) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_444 (UnOp (CastOp $ IntOp size_t) (IntOp u32) (LocInfoE loc_444 (use{it_layout u32} (LocInfoE loc_445 ("nr_pages"))))))) ])) ;
        locinfo: loc_372 ;
        LocInfoE loc_435 ("i") <-{ it_layout i32 }
          LocInfoE loc_436 (i2v 0 i32) ;
        locinfo: loc_373 ;
        Goto "#5"
      ]> $
      <[ "#5" :=
        locinfo: loc_430 ;
        if: LocInfoE loc_430 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_430 ((LocInfoE loc_431 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_431 (use{it_layout i32} (LocInfoE loc_432 ("i")))))) <{IntOp u32, IntOp u32} (LocInfoE loc_433 (use{it_layout u32} (LocInfoE loc_434 ("nr_pages")))))))
        then
        locinfo: loc_412 ;
          Goto "#6"
        else
        locinfo: loc_374 ;
          Goto "#7"
      ]> $
      <[ "#6" :=
        locinfo: loc_412 ;
        LocInfoE loc_425 ((LocInfoE loc_426 (!{void*} (LocInfoE loc_427 ("p")))) at{struct_hyp_page} "pool") <-{ void* }
          LocInfoE loc_428 (use{void*} (LocInfoE loc_429 ("pool"))) ;
        locinfo: loc_413 ;
        expr: (LocInfoE loc_413 (Call (LocInfoE loc_420 (global_INIT_LIST_HEAD)) [@{expr} LocInfoE loc_421 (&(LocInfoE loc_422 ((LocInfoE loc_423 (!{void*} (LocInfoE loc_424 ("p")))) at{struct_hyp_page} "node"))) ])) ;
        locinfo: loc_414 ;
        LocInfoE loc_418 ("p") <-{ void* }
          LocInfoE loc_414 ((LocInfoE loc_414 (use{void*} (LocInfoE loc_418 ("p")))) at_offset{layout_of struct_hyp_page, PtrOp, IntOp i32} (LocInfoE loc_414 (i2v 1 i32))) ;
        locinfo: loc_415 ;
        Goto "continue59"
      ]> $
      <[ "#7" :=
        locinfo: loc_374 ;
        LocInfoE loc_400 ("p") <-{ void* }
          LocInfoE loc_401 (Call (LocInfoE loc_403 (global_hyp_phys_to_page)) [@{expr} LocInfoE loc_404 ((LocInfoE loc_405 (use{it_layout u64} (LocInfoE loc_406 ("phys")))) +{IntOp u64, IntOp u64} (LocInfoE loc_407 (UnOp (CastOp $ IntOp u64) (IntOp u32) (LocInfoE loc_407 ((LocInfoE loc_408 (use{it_layout u32} (LocInfoE loc_409 ("used_pages")))) <<{IntOp u32, IntOp u32} (LocInfoE loc_410 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_410 (i2v 12 i32))))))))) ]) ;
        locinfo: loc_375 ;
        LocInfoE loc_397 ("i") <-{ it_layout i32 }
          LocInfoE loc_398 (UnOp (CastOp $ IntOp i32) (IntOp u32) (LocInfoE loc_398 (use{it_layout u32} (LocInfoE loc_399 ("used_pages"))))) ;
        locinfo: loc_376 ;
        Goto "#8"
      ]> $
      <[ "#8" :=
        locinfo: loc_392 ;
        if: LocInfoE loc_392 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_392 ((LocInfoE loc_393 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_393 (use{it_layout i32} (LocInfoE loc_394 ("i")))))) <{IntOp u32, IntOp u32} (LocInfoE loc_395 (use{it_layout u32} (LocInfoE loc_396 ("nr_pages")))))))
        then
        locinfo: loc_380 ;
          Goto "#9"
        else
        locinfo: loc_377 ;
          Goto "#10"
      ]> $
      <[ "#9" :=
        locinfo: loc_380 ;
        expr: (LocInfoE loc_380 (Call (LocInfoE loc_387 (global___hyp_attach_page)) [@{expr} LocInfoE loc_388 (use{void*} (LocInfoE loc_389 ("pool"))) ;
        LocInfoE loc_390 (use{void*} (LocInfoE loc_391 ("p"))) ])) ;
        locinfo: loc_381 ;
        LocInfoE loc_385 ("p") <-{ void* }
          LocInfoE loc_381 ((LocInfoE loc_381 (use{void*} (LocInfoE loc_385 ("p")))) at_offset{layout_of struct_hyp_page, PtrOp, IntOp i32} (LocInfoE loc_381 (i2v 1 i32))) ;
        locinfo: loc_382 ;
        Goto "continue61"
      ]> $
      <[ "continue58" :=
        locinfo: loc_470 ;
        LocInfoE loc_471 ("i") <-{ it_layout i32 }
          LocInfoE loc_470 ((LocInfoE loc_470 (use{it_layout i32} (LocInfoE loc_471 ("i")))) +{IntOp i32, IntOp i32} (LocInfoE loc_470 (i2v 1 i32))) ;
        locinfo: loc_367 ;
        Goto "#2"
      ]> $
      <[ "continue59" :=
        locinfo: loc_416 ;
        LocInfoE loc_417 ("i") <-{ it_layout i32 }
          LocInfoE loc_416 ((LocInfoE loc_416 (use{it_layout i32} (LocInfoE loc_417 ("i")))) +{IntOp i32, IntOp i32} (LocInfoE loc_416 (i2v 1 i32))) ;
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
        locinfo: loc_505 ;
        expr: (LocInfoE loc_549 (&(LocInfoE loc_550 ((LocInfoE loc_551 (!{void*} (LocInfoE loc_552 ("pool")))) at{struct_hyp_pool} "lock")))) ;
        "addr" <-{ it_layout u64 }
          LocInfoE loc_542 (Call (LocInfoE loc_544 (global_hyp_page_to_phys)) [@{expr} LocInfoE loc_545 (use{void*} (LocInfoE loc_546 ("p"))) ]) ;
        locinfo: loc_508 ;
        LocInfoE loc_534 ("addr") <-{ it_layout u64 }
          LocInfoE loc_535 ((LocInfoE loc_536 (use{it_layout u64} (LocInfoE loc_537 ("addr")))) ^{IntOp u64, IntOp u64} (LocInfoE loc_538 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_538 ((LocInfoE loc_539 (i2v 4096 i32)) <<{IntOp i32, IntOp i32} (LocInfoE loc_540 (UnOp (CastOp $ IntOp i32) (IntOp u32) (LocInfoE loc_540 (use{it_layout u32} (LocInfoE loc_541 ("order"))))))))))) ;
        locinfo: loc_520 ;
        if: LocInfoE loc_520 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_520 ((LocInfoE loc_521 (use{it_layout u64} (LocInfoE loc_522 ("addr")))) <{IntOp u64, IntOp u64} (LocInfoE loc_523 (use{it_layout u64} (LocInfoE loc_524 ((LocInfoE loc_525 (!{void*} (LocInfoE loc_526 ("pool")))) at{struct_hyp_pool} "range_start")))))))
        then
        locinfo: loc_516 ;
          Goto "#2"
        else
        Goto "#4"
      ]> $
      <[ "#1" :=
        locinfo: loc_510 ;
        Return (LocInfoE loc_511 (Call (LocInfoE loc_513 (global_hyp_phys_to_page)) [@{expr} LocInfoE loc_514 (use{it_layout u64} (LocInfoE loc_515 ("addr"))) ]))
      ]> $
      <[ "#2" :=
        locinfo: loc_516 ;
        Return (LocInfoE loc_517 (NULL))
      ]> $
      <[ "#3" :=
        locinfo: loc_510 ;
        Goto "#1"
      ]> $
      <[ "#4" :=
        locinfo: loc_527 ;
        if: LocInfoE loc_527 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_527 ((LocInfoE loc_528 (use{it_layout u64} (LocInfoE loc_529 ("addr")))) ≥{IntOp u64, IntOp u64} (LocInfoE loc_530 (use{it_layout u64} (LocInfoE loc_531 ((LocInfoE loc_532 (!{void*} (LocInfoE loc_533 ("pool")))) at{struct_hyp_pool} "range_end")))))))
        then
        locinfo: loc_516 ;
          Goto "#2"
        else
        locinfo: loc_510 ;
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
        locinfo: loc_555 ;
        expr: (LocInfoE loc_674 (&(LocInfoE loc_675 ((LocInfoE loc_676 (!{void*} (LocInfoE loc_677 ("pool")))) at{struct_hyp_pool} "lock")))) ;
        "order" <-{ it_layout u32 }
          LocInfoE loc_668 (use{it_layout u32} (LocInfoE loc_669 ((LocInfoE loc_670 (!{void*} (LocInfoE loc_671 ("p")))) at{struct_hyp_page} "order"))) ;
        locinfo: loc_558 ;
        LocInfoE loc_664 ((LocInfoE loc_665 (!{void*} (LocInfoE loc_666 ("p")))) at{struct_hyp_page} "order") <-{ it_layout u32 }
          LocInfoE loc_667 (i2v (max_int u32) u32) ;
        locinfo: loc_559 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_660 ;
        if: LocInfoE loc_660 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_660 ((LocInfoE loc_661 (use{it_layout u32} (LocInfoE loc_662 ("order")))) <{IntOp u32, IntOp u32} (LocInfoE loc_663 (i2v 11 u32)))))
        then
        locinfo: loc_589 ;
          Goto "#2"
        else
        locinfo: loc_560 ;
          Goto "#3"
      ]> $
      <[ "#10" :=
        locinfo: loc_639 ;
        if: LocInfoE loc_639 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_639 ((LocInfoE loc_640 (use{it_layout u32} (LocInfoE loc_641 ((LocInfoE loc_642 (!{void*} (LocInfoE loc_643 ("buddy")))) at{struct_hyp_page} "order")))) !={IntOp u32, IntOp u32} (LocInfoE loc_644 (use{it_layout u32} (LocInfoE loc_645 ("order")))))))
        then
        locinfo: loc_560 ;
          Goto "#8"
        else
        locinfo: loc_593 ;
          Goto "#9"
      ]> $
      <[ "#11" :=
        locinfo: loc_632 ;
        if: LocInfoE loc_632 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_632 (Call (LocInfoE loc_634 (global_list_empty)) [@{expr} LocInfoE loc_635 (&(LocInfoE loc_636 ((LocInfoE loc_637 (!{void*} (LocInfoE loc_638 ("buddy")))) at{struct_hyp_page} "node"))) ])))
        then
        locinfo: loc_560 ;
          Goto "#8"
        else
        Goto "#10"
      ]> $
      <[ "#2" :=
        locinfo: loc_589 ;
        LocInfoE loc_650 ("buddy") <-{ void* }
          LocInfoE loc_651 (Call (LocInfoE loc_653 (global___find_buddy)) [@{expr} LocInfoE loc_654 (use{void*} (LocInfoE loc_655 ("pool"))) ;
          LocInfoE loc_656 (use{void*} (LocInfoE loc_657 ("p"))) ;
          LocInfoE loc_658 (use{it_layout u32} (LocInfoE loc_659 ("order"))) ]) ;
        locinfo: loc_590 ;
        expr: (LocInfoE loc_646 (&(LocInfoE loc_647 ((LocInfoE loc_648 (!{void*} (LocInfoE loc_649 ("pool")))) at{struct_hyp_pool} "lock")))) ;
        locinfo: loc_628 ;
        if: LocInfoE loc_628 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_628 ((LocInfoE loc_629 (use{void*} (LocInfoE loc_630 ("buddy")))) ={PtrOp, PtrOp} (LocInfoE loc_631 (NULL)))))
        then
        locinfo: loc_560 ;
          Goto "#8"
        else
        Goto "#11"
      ]> $
      <[ "#3" :=
        locinfo: loc_560 ;
        expr: (LocInfoE loc_584 (&(LocInfoE loc_585 ((LocInfoE loc_586 (!{void*} (LocInfoE loc_587 ("pool")))) at{struct_hyp_pool} "lock")))) ;
        locinfo: loc_562 ;
        LocInfoE loc_579 ((LocInfoE loc_580 (!{void*} (LocInfoE loc_581 ("p")))) at{struct_hyp_page} "order") <-{ it_layout u32 }
          LocInfoE loc_582 (use{it_layout u32} (LocInfoE loc_583 ("order"))) ;
        locinfo: loc_563 ;
        expr: (LocInfoE loc_563 (Call (LocInfoE loc_565 (global_list_add)) [@{expr} LocInfoE loc_566 (&(LocInfoE loc_567 ((LocInfoE loc_568 (!{void*} (LocInfoE loc_569 ("p")))) at{struct_hyp_page} "node"))) ;
        LocInfoE loc_570 (&(LocInfoE loc_572 ((LocInfoE loc_574 ((LocInfoE loc_575 (!{void*} (LocInfoE loc_576 ("pool")))) at{struct_hyp_pool} "free_area")) at_offset{layout_of struct_list_head, PtrOp, IntOp u32} (LocInfoE loc_577 (use{it_layout u32} (LocInfoE loc_578 ("order"))))))) ])) ;
        Return (VOID)
      ]> $
      <[ "#4" :=
        locinfo: loc_593 ;
        expr: (LocInfoE loc_593 (Call (LocInfoE loc_619 (global_list_del_init)) [@{expr} LocInfoE loc_620 (&(LocInfoE loc_621 ((LocInfoE loc_622 (!{void*} (LocInfoE loc_623 ("buddy")))) at{struct_hyp_page} "node"))) ])) ;
        locinfo: loc_594 ;
        LocInfoE loc_614 ((LocInfoE loc_615 (!{void*} (LocInfoE loc_616 ("buddy")))) at{struct_hyp_page} "order") <-{ it_layout u32 }
          LocInfoE loc_617 (i2v (max_int u32) u32) ;
        locinfo: loc_609 ;
        if: LocInfoE loc_609 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_609 ((LocInfoE loc_610 (use{void*} (LocInfoE loc_611 ("p")))) <{PtrOp, PtrOp} (LocInfoE loc_612 (use{void*} (LocInfoE loc_613 ("buddy")))))))
        then
        locinfo: loc_600 ;
          Goto "#6"
        else
        locinfo: loc_605 ;
          Goto "#7"
      ]> $
      <[ "#5" :=
        locinfo: loc_596 ;
        Goto "continue36"
      ]> $
      <[ "#6" :=
        locinfo: loc_600 ;
        LocInfoE loc_601 ("p") <-{ void* }
          LocInfoE loc_602 (use{void*} (LocInfoE loc_603 ("p"))) ;
        locinfo: loc_596 ;
        Goto "#5"
      ]> $
      <[ "#7" :=
        locinfo: loc_605 ;
        LocInfoE loc_606 ("p") <-{ void* }
          LocInfoE loc_607 (use{void*} (LocInfoE loc_608 ("buddy"))) ;
        locinfo: loc_596 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        locinfo: loc_560 ;
        Goto "#3"
      ]> $
      <[ "#9" :=
        locinfo: loc_593 ;
        Goto "#4"
      ]> $
      <[ "continue36" :=
        locinfo: loc_597 ;
        LocInfoE loc_598 ("order") <-{ it_layout u32 }
          LocInfoE loc_597 ((LocInfoE loc_597 (use{it_layout u32} (LocInfoE loc_598 ("order")))) +{IntOp u32, IntOp u32} (LocInfoE loc_597 (i2v 1 u32))) ;
        locinfo: loc_559 ;
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
        locinfo: loc_755 ;
        if: LocInfoE loc_755 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_755 ((LocInfoE loc_756 (use{it_layout u32} (LocInfoE loc_757 ((LocInfoE loc_758 (!{void*} (LocInfoE loc_759 ("p")))) at{struct_hyp_page} "order")))) ={IntOp u32, IntOp u32} (LocInfoE loc_760 (i2v (max_int u32) u32)))))
        then
        locinfo: loc_751 ;
          Goto "#5"
        else
        Goto "#7"
      ]> $
      <[ "#1" :=
        locinfo: loc_681 ;
        expr: (LocInfoE loc_681 (Call (LocInfoE loc_746 (global_list_del_init)) [@{expr} LocInfoE loc_747 (&(LocInfoE loc_748 ((LocInfoE loc_749 (!{void*} (LocInfoE loc_750 ("p")))) at{struct_hyp_page} "node"))) ])) ;
        locinfo: loc_682 ;
        Goto "#2"
      ]> $
      <[ "#2" :=
        locinfo: loc_738 ;
        if: LocInfoE loc_738 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_738 ((LocInfoE loc_739 (use{it_layout u32} (LocInfoE loc_740 ((LocInfoE loc_741 (!{void*} (LocInfoE loc_742 ("p")))) at{struct_hyp_page} "order")))) >{IntOp u32, IntOp u32} (LocInfoE loc_743 (use{it_layout u32} (LocInfoE loc_744 ("order")))))))
        then
        locinfo: loc_693 ;
          Goto "#3"
        else
        locinfo: loc_683 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_693 ;
        LocInfoE loc_735 ((LocInfoE loc_736 (!{void*} (LocInfoE loc_737 ("p")))) at{struct_hyp_page} "order") <-{ it_layout u32 }
          LocInfoE loc_693 ((LocInfoE loc_693 (use{it_layout u32} (LocInfoE loc_735 ((LocInfoE loc_736 (!{void*} (LocInfoE loc_737 ("p")))) at{struct_hyp_page} "order")))) -{IntOp u32, IntOp u32} (LocInfoE loc_693 (i2v 1 u32))) ;
        locinfo: loc_694 ;
        LocInfoE loc_723 ("buddy") <-{ void* }
          LocInfoE loc_724 (Call (LocInfoE loc_726 (global___find_buddy)) [@{expr} LocInfoE loc_727 (use{void*} (LocInfoE loc_728 ("pool"))) ;
          LocInfoE loc_729 (use{void*} (LocInfoE loc_730 ("p"))) ;
          LocInfoE loc_731 (use{it_layout u32} (LocInfoE loc_732 ((LocInfoE loc_733 (!{void*} (LocInfoE loc_734 ("p")))) at{struct_hyp_page} "order"))) ]) ;
        locinfo: loc_695 ;
        LocInfoE loc_716 ((LocInfoE loc_717 (!{void*} (LocInfoE loc_718 ("buddy")))) at{struct_hyp_page} "order") <-{ it_layout u32 }
          LocInfoE loc_719 (use{it_layout u32} (LocInfoE loc_720 ((LocInfoE loc_721 (!{void*} (LocInfoE loc_722 ("p")))) at{struct_hyp_page} "order"))) ;
        locinfo: loc_696 ;
        expr: (LocInfoE loc_696 (Call (LocInfoE loc_700 (global_list_add_tail)) [@{expr} LocInfoE loc_701 (&(LocInfoE loc_702 ((LocInfoE loc_703 (!{void*} (LocInfoE loc_704 ("buddy")))) at{struct_hyp_page} "node"))) ;
        LocInfoE loc_705 (&(LocInfoE loc_707 ((LocInfoE loc_709 ((LocInfoE loc_710 (!{void*} (LocInfoE loc_711 ("pool")))) at{struct_hyp_pool} "free_area")) at_offset{layout_of struct_list_head, PtrOp, IntOp u32} (LocInfoE loc_712 (use{it_layout u32} (LocInfoE loc_713 ((LocInfoE loc_714 (!{void*} (LocInfoE loc_715 ("buddy")))) at{struct_hyp_page} "order"))))))) ])) ;
        locinfo: loc_697 ;
        Goto "continue46"
      ]> $
      <[ "#4" :=
        locinfo: loc_683 ;
        LocInfoE loc_687 ((LocInfoE loc_688 (!{void*} (LocInfoE loc_689 ("p")))) at{struct_hyp_page} "refcount") <-{ it_layout u32 }
          LocInfoE loc_690 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_690 (i2v 1 i32))) ;
        locinfo: loc_684 ;
        Return (LocInfoE loc_685 (use{void*} (LocInfoE loc_686 ("p"))))
      ]> $
      <[ "#5" :=
        locinfo: loc_751 ;
        Return (LocInfoE loc_752 (NULL))
      ]> $
      <[ "#6" :=
        locinfo: loc_681 ;
        Goto "#1"
      ]> $
      <[ "#7" :=
        locinfo: loc_761 ;
        if: LocInfoE loc_761 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_761 ((LocInfoE loc_762 (use{it_layout u32} (LocInfoE loc_763 ((LocInfoE loc_764 (!{void*} (LocInfoE loc_765 ("p")))) at{struct_hyp_page} "order")))) <{IntOp u32, IntOp u32} (LocInfoE loc_766 (use{it_layout u32} (LocInfoE loc_767 ("order")))))))
        then
        locinfo: loc_751 ;
          Goto "#5"
        else
        locinfo: loc_681 ;
          Goto "#6"
      ]> $
      <[ "continue46" :=
        locinfo: loc_682 ;
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
        locinfo: loc_770 ;
        LocInfoE loc_804 ("i") <-{ it_layout u64 }
          LocInfoE loc_805 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_805 (i2v 0 i32))) ;
        locinfo: loc_771 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_795 ;
        if: LocInfoE loc_795 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_795 ((LocInfoE loc_796 (use{it_layout u64} (LocInfoE loc_797 ("i")))) <{IntOp u64, IntOp u64} (LocInfoE loc_798 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_798 ((LocInfoE loc_799 (i2v 1 i32)) <<{IntOp i32, IntOp i32} (LocInfoE loc_800 (UnOp (CastOp $ IntOp i32) (IntOp u32) (LocInfoE loc_800 (use{it_layout u32} (LocInfoE loc_801 ((LocInfoE loc_802 (!{void*} (LocInfoE loc_803 ("p")))) at{struct_hyp_page} "order")))))))))))))
        then
        locinfo: loc_773 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_773 ;
        expr: (LocInfoE loc_773 (Call (LocInfoE loc_778 (global_clear_page)) [@{expr} LocInfoE loc_779 ((LocInfoE loc_780 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_781 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_782 ((LocInfoE loc_783 (UnOp (CastOp $ IntOp u64) (IntOp u64) (LocInfoE loc_784 (Call (LocInfoE loc_786 (global_hyp_page_to_phys)) [@{expr} LocInfoE loc_787 (use{void*} (LocInfoE loc_788 ("p"))) ])))) -{IntOp u64, IntOp u64} (LocInfoE loc_789 (UnOp (CastOp $ IntOp u64) (IntOp i64) (LocInfoE loc_789 (use{it_layout i64} (LocInfoE loc_790 (global_hyp_physvirt_offset)))))))))))) at_offset{it_layout u8, PtrOp, IntOp u64} (LocInfoE loc_791 ((LocInfoE loc_792 (use{it_layout u64} (LocInfoE loc_793 ("i")))) <<{IntOp u64, IntOp u64} (LocInfoE loc_794 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_794 (i2v 12 i32))))))) ])) ;
        locinfo: loc_774 ;
        Goto "continue50"
      ]> $
      <[ "#3" :=
        Return (VOID)
      ]> $
      <[ "continue50" :=
        locinfo: loc_775 ;
        LocInfoE loc_776 ("i") <-{ it_layout u64 }
          LocInfoE loc_775 ((LocInfoE loc_775 (use{it_layout u64} (LocInfoE loc_776 ("i")))) +{IntOp u64, IntOp u64} (LocInfoE loc_775 (i2v 1 u64))) ;
        locinfo: loc_771 ;
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
          LocInfoE loc_882 (use{it_layout u32} (LocInfoE loc_883 ("order"))) ;
        locinfo: loc_809 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_866 ;
        if: LocInfoE loc_866 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_866 ((LocInfoE loc_867 (use{it_layout u32} (LocInfoE loc_868 ("i")))) ≤{IntOp u32, IntOp u32} (LocInfoE loc_869 (i2v 11 u32)))))
        then
        Goto "#10"
        else
        locinfo: loc_856 ;
          Goto "#3"
      ]> $
      <[ "#10" :=
        locinfo: loc_870 ;
        if: LocInfoE loc_870 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_870 (Call (LocInfoE loc_872 (global_list_empty)) [@{expr} LocInfoE loc_873 (&(LocInfoE loc_875 ((LocInfoE loc_877 ((LocInfoE loc_878 (!{void*} (LocInfoE loc_879 ("pool")))) at{struct_hyp_pool} "free_area")) at_offset{layout_of struct_list_head, PtrOp, IntOp u32} (LocInfoE loc_880 (use{it_layout u32} (LocInfoE loc_881 ("i"))))))) ])))
        then
        locinfo: loc_861 ;
          Goto "#2"
        else
        locinfo: loc_856 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_861 ;
        LocInfoE loc_864 ("i") <-{ it_layout u32 }
          LocInfoE loc_861 ((LocInfoE loc_861 (use{it_layout u32} (LocInfoE loc_864 ("i")))) +{IntOp u32, IntOp u32} (LocInfoE loc_861 (i2v 1 u32))) ;
        locinfo: loc_862 ;
        Goto "continue53"
      ]> $
      <[ "#3" :=
        locinfo: loc_856 ;
        if: LocInfoE loc_856 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_856 ((LocInfoE loc_857 (use{it_layout u32} (LocInfoE loc_858 ("i")))) >{IntOp u32, IntOp u32} (LocInfoE loc_859 (i2v 11 u32)))))
        then
        locinfo: loc_853 ;
          Goto "#8"
        else
        locinfo: loc_811 ;
          Goto "#9"
      ]> $
      <[ "#4" :=
        locinfo: loc_811 ;
        LocInfoE loc_837 ("p") <-{ void* }
          LocInfoE loc_838 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_839 ((LocInfoE loc_840 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_841 (use{void*} (LocInfoE loc_842 ((LocInfoE loc_843 (&(LocInfoE loc_845 ((LocInfoE loc_847 ((LocInfoE loc_848 (!{void*} (LocInfoE loc_849 ("pool")))) at{struct_hyp_pool} "free_area")) at_offset{layout_of struct_list_head, PtrOp, IntOp u32} (LocInfoE loc_850 (use{it_layout u32} (LocInfoE loc_851 ("i")))))))) at{struct_list_head} "next")))))) at_neg_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_852 ((OffsetOf (struct_hyp_page) ("node"))))))) ;
        locinfo: loc_812 ;
        LocInfoE loc_827 ("p") <-{ void* }
          LocInfoE loc_828 (Call (LocInfoE loc_830 (global___hyp_extract_page)) [@{expr} LocInfoE loc_831 (use{void*} (LocInfoE loc_832 ("pool"))) ;
          LocInfoE loc_833 (use{void*} (LocInfoE loc_834 ("p"))) ;
          LocInfoE loc_835 (use{it_layout u32} (LocInfoE loc_836 ("order"))) ]) ;
        locinfo: loc_823 ;
        if: LocInfoE loc_823 (UnOp (CastOp $ IntOp bool_it) (IntOp u64) (LocInfoE loc_823 ((LocInfoE loc_824 (use{it_layout u64} (LocInfoE loc_825 ("mask")))) &{IntOp u64, IntOp u64} (LocInfoE loc_826 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_826 (i2v 1 i32)))))))
        then
        locinfo: loc_817 ;
          Goto "#6"
        else
        locinfo: loc_814 ;
          Goto "#7"
      ]> $
      <[ "#5" :=
        locinfo: loc_814 ;
        Return (LocInfoE loc_815 (use{void*} (LocInfoE loc_816 ("p"))))
      ]> $
      <[ "#6" :=
        locinfo: loc_817 ;
        expr: (LocInfoE loc_817 (Call (LocInfoE loc_819 (global_clear_hyp_page)) [@{expr} LocInfoE loc_820 (use{void*} (LocInfoE loc_821 ("p"))) ])) ;
        locinfo: loc_814 ;
        Goto "#5"
      ]> $
      <[ "#7" :=
        locinfo: loc_814 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        locinfo: loc_853 ;
        Return (LocInfoE loc_854 (NULL))
      ]> $
      <[ "#9" :=
        locinfo: loc_811 ;
        Goto "#4"
      ]> $
      <[ "continue53" :=
        locinfo: loc_809 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.
End code.
