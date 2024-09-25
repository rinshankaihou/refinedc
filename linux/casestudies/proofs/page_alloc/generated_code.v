From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [linux/casestudies/page_alloc.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "linux/casestudies/page_alloc.c".
  Definition loc_2 : location_info := LocationInfo file_0 63 2 63 47.
  Definition loc_3 : location_info := LocationInfo file_0 63 9 63 46.
  Definition loc_4 : location_info := LocationInfo file_0 63 9 63 32.
  Definition loc_5 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_6 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_7 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_8 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_11 : location_info := LocationInfo file_1 34 1 34 11.
  Definition loc_12 : location_info := LocationInfo file_1 34 8 34 9.
  Definition loc_15 : location_info := LocationInfo file_1 64 1 64 10.
  Definition loc_16 : location_info := LocationInfo file_1 64 8 64 9.
  Definition loc_19 : location_info := LocationInfo file_1 68 1 68 10.
  Definition loc_20 : location_info := LocationInfo file_1 68 8 68 9.
  Definition loc_23 : location_info := LocationInfo file_1 80 1 80 25.
  Definition loc_24 : location_info := LocationInfo file_1 81 1 81 19.
  Definition loc_25 : location_info := LocationInfo file_1 81 1 81 11.
  Definition loc_26 : location_info := LocationInfo file_1 81 1 81 5.
  Definition loc_27 : location_info := LocationInfo file_1 81 1 81 5.
  Definition loc_28 : location_info := LocationInfo file_1 81 14 81 18.
  Definition loc_29 : location_info := LocationInfo file_1 81 14 81 18.
  Definition loc_30 : location_info := LocationInfo file_1 80 2 80 14.
  Definition loc_31 : location_info := LocationInfo file_1 80 3 80 7.
  Definition loc_32 : location_info := LocationInfo file_1 80 3 80 7.
  Definition loc_33 : location_info := LocationInfo file_1 80 17 80 23.
  Definition loc_34 : location_info := LocationInfo file_1 80 17 80 23.
  Definition loc_37 : location_info := LocationInfo file_1 94 1 95 9.
  Definition loc_38 : location_info := LocationInfo file_1 97 1 97 18.
  Definition loc_39 : location_info := LocationInfo file_1 98 1 98 18.
  Definition loc_40 : location_info := LocationInfo file_1 99 1 99 18.
  Definition loc_41 : location_info := LocationInfo file_1 100 1 100 24.
  Definition loc_42 : location_info := LocationInfo file_1 100 2 100 14.
  Definition loc_43 : location_info := LocationInfo file_1 100 3 100 7.
  Definition loc_44 : location_info := LocationInfo file_1 100 3 100 7.
  Definition loc_45 : location_info := LocationInfo file_1 100 17 100 22.
  Definition loc_46 : location_info := LocationInfo file_1 100 17 100 22.
  Definition loc_47 : location_info := LocationInfo file_1 99 1 99 10.
  Definition loc_48 : location_info := LocationInfo file_1 99 1 99 4.
  Definition loc_49 : location_info := LocationInfo file_1 99 1 99 4.
  Definition loc_50 : location_info := LocationInfo file_1 99 13 99 17.
  Definition loc_51 : location_info := LocationInfo file_1 99 13 99 17.
  Definition loc_52 : location_info := LocationInfo file_1 98 1 98 10.
  Definition loc_53 : location_info := LocationInfo file_1 98 1 98 4.
  Definition loc_54 : location_info := LocationInfo file_1 98 1 98 4.
  Definition loc_55 : location_info := LocationInfo file_1 98 13 98 17.
  Definition loc_56 : location_info := LocationInfo file_1 98 13 98 17.
  Definition loc_57 : location_info := LocationInfo file_1 97 1 97 11.
  Definition loc_58 : location_info := LocationInfo file_1 97 1 97 5.
  Definition loc_59 : location_info := LocationInfo file_1 97 1 97 5.
  Definition loc_60 : location_info := LocationInfo file_1 97 14 97 17.
  Definition loc_61 : location_info := LocationInfo file_1 97 14 97 17.
  Definition loc_62 : location_info := LocationInfo file_1 95 2 95 9.
  Definition loc_64 : location_info := LocationInfo file_1 94 1 95 9.
  Definition loc_65 : location_info := LocationInfo file_1 94 5 94 39.
  Definition loc_67 : location_info := LocationInfo file_1 94 6 94 39.
  Definition loc_68 : location_info := LocationInfo file_1 94 6 94 22.
  Definition loc_69 : location_info := LocationInfo file_1 94 6 94 22.
  Definition loc_70 : location_info := LocationInfo file_1 94 23 94 26.
  Definition loc_71 : location_info := LocationInfo file_1 94 23 94 26.
  Definition loc_72 : location_info := LocationInfo file_1 94 28 94 32.
  Definition loc_73 : location_info := LocationInfo file_1 94 28 94 32.
  Definition loc_74 : location_info := LocationInfo file_1 94 34 94 38.
  Definition loc_75 : location_info := LocationInfo file_1 94 34 94 38.
  Definition loc_78 : location_info := LocationInfo file_1 117 1 117 35.
  Definition loc_79 : location_info := LocationInfo file_1 117 1 117 11.
  Definition loc_80 : location_info := LocationInfo file_1 117 1 117 11.
  Definition loc_81 : location_info := LocationInfo file_1 117 12 117 15.
  Definition loc_82 : location_info := LocationInfo file_1 117 12 117 15.
  Definition loc_83 : location_info := LocationInfo file_1 117 17 117 21.
  Definition loc_84 : location_info := LocationInfo file_1 117 17 117 21.
  Definition loc_85 : location_info := LocationInfo file_1 117 23 117 33.
  Definition loc_86 : location_info := LocationInfo file_1 117 23 117 33.
  Definition loc_87 : location_info := LocationInfo file_1 117 23 117 27.
  Definition loc_88 : location_info := LocationInfo file_1 117 23 117 27.
  Definition loc_91 : location_info := LocationInfo file_1 131 1 131 35.
  Definition loc_92 : location_info := LocationInfo file_1 131 1 131 11.
  Definition loc_93 : location_info := LocationInfo file_1 131 1 131 11.
  Definition loc_94 : location_info := LocationInfo file_1 131 12 131 15.
  Definition loc_95 : location_info := LocationInfo file_1 131 12 131 15.
  Definition loc_96 : location_info := LocationInfo file_1 131 17 131 27.
  Definition loc_97 : location_info := LocationInfo file_1 131 17 131 27.
  Definition loc_98 : location_info := LocationInfo file_1 131 17 131 21.
  Definition loc_99 : location_info := LocationInfo file_1 131 17 131 21.
  Definition loc_100 : location_info := LocationInfo file_1 131 29 131 33.
  Definition loc_101 : location_info := LocationInfo file_1 131 29 131 33.
  Definition loc_104 : location_info := LocationInfo file_1 143 1 143 19.
  Definition loc_105 : location_info := LocationInfo file_1 144 1 144 25.
  Definition loc_106 : location_info := LocationInfo file_1 144 2 144 14.
  Definition loc_107 : location_info := LocationInfo file_1 144 3 144 7.
  Definition loc_108 : location_info := LocationInfo file_1 144 3 144 7.
  Definition loc_109 : location_info := LocationInfo file_1 144 17 144 23.
  Definition loc_110 : location_info := LocationInfo file_1 144 17 144 23.
  Definition loc_111 : location_info := LocationInfo file_1 143 1 143 11.
  Definition loc_112 : location_info := LocationInfo file_1 143 1 143 5.
  Definition loc_113 : location_info := LocationInfo file_1 143 1 143 5.
  Definition loc_114 : location_info := LocationInfo file_1 143 14 143 18.
  Definition loc_115 : location_info := LocationInfo file_1 143 14 143 18.
  Definition loc_118 : location_info := LocationInfo file_1 149 1 150 9.
  Definition loc_119 : location_info := LocationInfo file_1 152 1 152 38.
  Definition loc_120 : location_info := LocationInfo file_1 152 1 152 11.
  Definition loc_121 : location_info := LocationInfo file_1 152 1 152 11.
  Definition loc_122 : location_info := LocationInfo file_1 152 12 152 23.
  Definition loc_123 : location_info := LocationInfo file_1 152 12 152 23.
  Definition loc_124 : location_info := LocationInfo file_1 152 12 152 17.
  Definition loc_125 : location_info := LocationInfo file_1 152 12 152 17.
  Definition loc_126 : location_info := LocationInfo file_1 152 25 152 36.
  Definition loc_127 : location_info := LocationInfo file_1 152 25 152 36.
  Definition loc_128 : location_info := LocationInfo file_1 152 25 152 30.
  Definition loc_129 : location_info := LocationInfo file_1 152 25 152 30.
  Definition loc_130 : location_info := LocationInfo file_1 150 2 150 9.
  Definition loc_132 : location_info := LocationInfo file_1 149 1 150 9.
  Definition loc_133 : location_info := LocationInfo file_1 149 5 149 35.
  Definition loc_135 : location_info := LocationInfo file_1 149 6 149 35.
  Definition loc_136 : location_info := LocationInfo file_1 149 6 149 28.
  Definition loc_137 : location_info := LocationInfo file_1 149 6 149 28.
  Definition loc_138 : location_info := LocationInfo file_1 149 29 149 34.
  Definition loc_139 : location_info := LocationInfo file_1 149 29 149 34.
  Definition loc_142 : location_info := LocationInfo file_1 166 1 166 25.
  Definition loc_143 : location_info := LocationInfo file_1 167 1 167 23.
  Definition loc_144 : location_info := LocationInfo file_1 167 1 167 15.
  Definition loc_145 : location_info := LocationInfo file_1 167 1 167 15.
  Definition loc_146 : location_info := LocationInfo file_1 167 16 167 21.
  Definition loc_147 : location_info := LocationInfo file_1 167 16 167 21.
  Definition loc_148 : location_info := LocationInfo file_1 166 1 166 17.
  Definition loc_149 : location_info := LocationInfo file_1 166 1 166 17.
  Definition loc_150 : location_info := LocationInfo file_1 166 18 166 23.
  Definition loc_151 : location_info := LocationInfo file_1 166 18 166 23.
  Definition loc_154 : location_info := LocationInfo file_1 181 1 181 29.
  Definition loc_155 : location_info := LocationInfo file_1 181 8 181 28.
  Definition loc_156 : location_info := LocationInfo file_1 181 8 181 20.
  Definition loc_157 : location_info := LocationInfo file_1 181 8 181 20.
  Definition loc_158 : location_info := LocationInfo file_1 181 9 181 13.
  Definition loc_159 : location_info := LocationInfo file_1 181 9 181 13.
  Definition loc_160 : location_info := LocationInfo file_1 181 24 181 28.
  Definition loc_161 : location_info := LocationInfo file_1 181 24 181 28.
  Definition loc_164 : location_info := LocationInfo file_1 248 1 248 62.
  Definition loc_165 : location_info := LocationInfo file_1 248 8 248 61.
  Definition loc_166 : location_info := LocationInfo file_1 248 17 248 60.
  Definition loc_167 : location_info := LocationInfo file_1 248 18 248 37.
  Definition loc_168 : location_info := LocationInfo file_1 248 31 248 37.
  Definition loc_169 : location_info := LocationInfo file_1 248 31 248 37.
  Definition loc_170 : location_info := LocationInfo file_1 248 40 248 59.
  Definition loc_171 : location_info := LocationInfo file_1 248 40 248 59.
  Definition loc_174 : location_info := LocationInfo file_1 253 1 253 52.
  Definition loc_175 : location_info := LocationInfo file_1 253 8 253 51.
  Definition loc_176 : location_info := LocationInfo file_1 253 9 253 28.
  Definition loc_177 : location_info := LocationInfo file_1 253 22 253 28.
  Definition loc_178 : location_info := LocationInfo file_1 253 22 253 28.
  Definition loc_179 : location_info := LocationInfo file_1 253 31 253 50.
  Definition loc_180 : location_info := LocationInfo file_1 253 31 253 50.
  Definition loc_183 : location_info := LocationInfo file_1 266 1 266 62.
  Definition loc_184 : location_info := LocationInfo file_1 266 8 266 61.
  Definition loc_185 : location_info := LocationInfo file_1 266 9 266 43.
  Definition loc_186 : location_info := LocationInfo file_1 266 29 266 42.
  Definition loc_187 : location_info := LocationInfo file_1 266 29 266 42.
  Definition loc_188 : location_info := LocationInfo file_1 266 46 266 60.
  Definition loc_189 : location_info := LocationInfo file_1 266 47 266 53.
  Definition loc_190 : location_info := LocationInfo file_1 266 47 266 53.
  Definition loc_191 : location_info := LocationInfo file_1 266 57 266 59.
  Definition loc_194 : location_info := LocationInfo file_1 278 1 278 75.
  Definition loc_195 : location_info := LocationInfo file_1 278 8 278 74.
  Definition loc_196 : location_info := LocationInfo file_1 278 9 278 67.
  Definition loc_197 : location_info := LocationInfo file_1 278 22 278 67.
  Definition loc_198 : location_info := LocationInfo file_1 278 23 278 29.
  Definition loc_199 : location_info := LocationInfo file_1 278 23 278 29.
  Definition loc_200 : location_info := LocationInfo file_1 278 32 278 66.
  Definition loc_201 : location_info := LocationInfo file_1 278 52 278 65.
  Definition loc_202 : location_info := LocationInfo file_1 278 52 278 65.
  Definition loc_203 : location_info := LocationInfo file_1 278 71 278 73.
  Definition loc_206 : location_info := LocationInfo file_1 285 1 285 84.
  Definition loc_207 : location_info := LocationInfo file_1 287 1 287 20.
  Definition loc_208 : location_info := LocationInfo file_1 287 8 287 19.
  Definition loc_209 : location_info := LocationInfo file_1 287 8 287 19.
  Definition loc_210 : location_info := LocationInfo file_1 287 8 287 9.
  Definition loc_211 : location_info := LocationInfo file_1 287 8 287 9.
  Definition loc_212 : location_info := LocationInfo file_1 285 22 285 83.
  Definition loc_213 : location_info := LocationInfo file_1 285 22 285 38.
  Definition loc_214 : location_info := LocationInfo file_1 285 22 285 38.
  Definition loc_215 : location_info := LocationInfo file_1 285 39 285 82.
  Definition loc_216 : location_info := LocationInfo file_1 285 40 285 59.
  Definition loc_217 : location_info := LocationInfo file_1 285 53 285 59.
  Definition loc_218 : location_info := LocationInfo file_1 285 53 285 59.
  Definition loc_219 : location_info := LocationInfo file_1 285 62 285 81.
  Definition loc_220 : location_info := LocationInfo file_1 285 62 285 81.
  Definition loc_225 : location_info := LocationInfo file_1 520 1 520 20.
  Definition loc_226 : location_info := LocationInfo file_1 522 1 522 22.
  Definition loc_227 : location_info := LocationInfo file_1 523 1 523 42.
  Definition loc_228 : location_info := LocationInfo file_1 524 1 524 24.
  Definition loc_229 : location_info := LocationInfo file_1 526 1 526 98.
  Definition loc_230 : location_info := LocationInfo file_1 526 8 526 97.
  Definition loc_231 : location_info := LocationInfo file_1 526 8 526 9.
  Definition loc_232 : location_info := LocationInfo file_1 526 8 526 9.
  Definition loc_233 : location_info := LocationInfo file_1 526 12 526 80.
  Definition loc_234 : location_info := LocationInfo file_1 526 21 526 79.
  Definition loc_235 : location_info := LocationInfo file_1 526 22 526 56.
  Definition loc_236 : location_info := LocationInfo file_1 526 35 526 56.
  Definition loc_237 : location_info := LocationInfo file_1 526 36 526 52.
  Definition loc_238 : location_info := LocationInfo file_1 526 36 526 52.
  Definition loc_239 : location_info := LocationInfo file_1 526 53 526 54.
  Definition loc_240 : location_info := LocationInfo file_1 526 53 526 54.
  Definition loc_241 : location_info := LocationInfo file_1 526 59 526 78.
  Definition loc_242 : location_info := LocationInfo file_1 526 59 526 78.
  Definition loc_243 : location_info := LocationInfo file_1 526 83 526 97.
  Definition loc_244 : location_info := LocationInfo file_1 524 1 524 10.
  Definition loc_245 : location_info := LocationInfo file_1 524 1 524 10.
  Definition loc_246 : location_info := LocationInfo file_1 524 11 524 22.
  Definition loc_247 : location_info := LocationInfo file_1 524 12 524 22.
  Definition loc_248 : location_info := LocationInfo file_1 524 12 524 16.
  Definition loc_249 : location_info := LocationInfo file_1 524 12 524 16.
  Definition loc_250 : location_info := LocationInfo file_1 523 1 523 2.
  Definition loc_251 : location_info := LocationInfo file_1 523 5 523 41.
  Definition loc_252 : location_info := LocationInfo file_1 523 5 523 22.
  Definition loc_253 : location_info := LocationInfo file_1 523 5 523 22.
  Definition loc_254 : location_info := LocationInfo file_1 523 23 523 27.
  Definition loc_255 : location_info := LocationInfo file_1 523 23 523 27.
  Definition loc_256 : location_info := LocationInfo file_1 523 29 523 33.
  Definition loc_257 : location_info := LocationInfo file_1 523 29 523 33.
  Definition loc_258 : location_info := LocationInfo file_1 523 35 523 40.
  Definition loc_259 : location_info := LocationInfo file_1 523 35 523 40.
  Definition loc_260 : location_info := LocationInfo file_1 522 1 522 8.
  Definition loc_261 : location_info := LocationInfo file_1 522 1 522 8.
  Definition loc_262 : location_info := LocationInfo file_1 522 9 522 20.
  Definition loc_263 : location_info := LocationInfo file_1 522 10 522 20.
  Definition loc_264 : location_info := LocationInfo file_1 522 10 522 14.
  Definition loc_265 : location_info := LocationInfo file_1 522 10 522 14.
  Definition loc_268 : location_info := LocationInfo file_1 453 1 453 84.
  Definition loc_269 : location_info := LocationInfo file_1 454 1 454 56.
  Definition loc_270 : location_info := LocationInfo file_1 456 1 456 22.
  Definition loc_271 : location_info := LocationInfo file_1 457 1 457 15.
  Definition loc_272 : location_info := LocationInfo file_1 458 1 458 24.
  Definition loc_273 : location_info := LocationInfo file_1 458 1 458 10.
  Definition loc_274 : location_info := LocationInfo file_1 458 1 458 10.
  Definition loc_275 : location_info := LocationInfo file_1 458 11 458 22.
  Definition loc_276 : location_info := LocationInfo file_1 458 12 458 22.
  Definition loc_277 : location_info := LocationInfo file_1 458 12 458 16.
  Definition loc_278 : location_info := LocationInfo file_1 458 12 458 16.
  Definition loc_279 : location_info := LocationInfo file_1 457 1 457 12.
  Definition loc_280 : location_info := LocationInfo file_1 457 1 457 2.
  Definition loc_281 : location_info := LocationInfo file_1 457 1 457 2.
  Definition loc_282 : location_info := LocationInfo file_1 456 1 456 8.
  Definition loc_283 : location_info := LocationInfo file_1 456 1 456 8.
  Definition loc_284 : location_info := LocationInfo file_1 456 9 456 20.
  Definition loc_285 : location_info := LocationInfo file_1 456 10 456 20.
  Definition loc_286 : location_info := LocationInfo file_1 456 10 456 14.
  Definition loc_287 : location_info := LocationInfo file_1 456 10 456 14.
  Definition loc_288 : location_info := LocationInfo file_1 454 25 454 55.
  Definition loc_289 : location_info := LocationInfo file_1 454 25 454 55.
  Definition loc_290 : location_info := LocationInfo file_1 454 26 454 48.
  Definition loc_291 : location_info := LocationInfo file_1 454 46 454 47.
  Definition loc_292 : location_info := LocationInfo file_1 454 46 454 47.
  Definition loc_295 : location_info := LocationInfo file_1 453 22 453 83.
  Definition loc_296 : location_info := LocationInfo file_1 453 22 453 38.
  Definition loc_297 : location_info := LocationInfo file_1 453 22 453 38.
  Definition loc_298 : location_info := LocationInfo file_1 453 39 453 82.
  Definition loc_299 : location_info := LocationInfo file_1 453 40 453 59.
  Definition loc_300 : location_info := LocationInfo file_1 453 53 453 59.
  Definition loc_301 : location_info := LocationInfo file_1 453 53 453 59.
  Definition loc_302 : location_info := LocationInfo file_1 453 62 453 81.
  Definition loc_303 : location_info := LocationInfo file_1 453 62 453 81.
  Definition loc_308 : location_info := LocationInfo file_1 439 1 439 84.
  Definition loc_309 : location_info := LocationInfo file_1 440 1 440 56.
  Definition loc_310 : location_info := LocationInfo file_1 442 1 442 22.
  Definition loc_311 : location_info := LocationInfo file_1 443 1 444 14.
  Definition loc_312 : location_info := LocationInfo file_1 445 1 445 15.
  Definition loc_313 : location_info := LocationInfo file_1 446 1 447 29.
  Definition loc_314 : location_info := LocationInfo file_1 448 1 448 24.
  Definition loc_315 : location_info := LocationInfo file_1 448 1 448 10.
  Definition loc_316 : location_info := LocationInfo file_1 448 1 448 10.
  Definition loc_317 : location_info := LocationInfo file_1 448 11 448 22.
  Definition loc_318 : location_info := LocationInfo file_1 448 12 448 22.
  Definition loc_319 : location_info := LocationInfo file_1 448 12 448 16.
  Definition loc_320 : location_info := LocationInfo file_1 448 12 448 16.
  Definition loc_321 : location_info := LocationInfo file_1 447 2 447 29.
  Definition loc_322 : location_info := LocationInfo file_1 447 2 447 19.
  Definition loc_323 : location_info := LocationInfo file_1 447 2 447 19.
  Definition loc_324 : location_info := LocationInfo file_1 447 20 447 24.
  Definition loc_325 : location_info := LocationInfo file_1 447 20 447 24.
  Definition loc_326 : location_info := LocationInfo file_1 447 26 447 27.
  Definition loc_327 : location_info := LocationInfo file_1 447 26 447 27.
  Definition loc_328 : location_info := LocationInfo file_1 446 1 447 29.
  Definition loc_329 : location_info := LocationInfo file_1 446 5 446 17.
  Definition loc_331 : location_info := LocationInfo file_1 446 6 446 17.
  Definition loc_332 : location_info := LocationInfo file_1 446 6 446 17.
  Definition loc_333 : location_info := LocationInfo file_1 446 6 446 7.
  Definition loc_334 : location_info := LocationInfo file_1 446 6 446 7.
  Definition loc_335 : location_info := LocationInfo file_1 445 1 445 12.
  Definition loc_336 : location_info := LocationInfo file_1 445 1 445 2.
  Definition loc_337 : location_info := LocationInfo file_1 445 1 445 2.
  Definition loc_338 : location_info := LocationInfo file_1 444 2 444 14.
  Definition loc_339 : location_info := LocationInfo file_1 444 2 444 11.
  Definition loc_340 : location_info := LocationInfo file_1 444 2 444 11.
  Definition loc_341 : location_info := LocationInfo file_1 443 1 444 14.
  Definition loc_342 : location_info := LocationInfo file_1 443 5 443 17.
  Definition loc_344 : location_info := LocationInfo file_1 443 6 443 17.
  Definition loc_345 : location_info := LocationInfo file_1 443 6 443 17.
  Definition loc_346 : location_info := LocationInfo file_1 443 6 443 7.
  Definition loc_347 : location_info := LocationInfo file_1 443 6 443 7.
  Definition loc_348 : location_info := LocationInfo file_1 442 1 442 8.
  Definition loc_349 : location_info := LocationInfo file_1 442 1 442 8.
  Definition loc_350 : location_info := LocationInfo file_1 442 9 442 20.
  Definition loc_351 : location_info := LocationInfo file_1 442 10 442 20.
  Definition loc_352 : location_info := LocationInfo file_1 442 10 442 14.
  Definition loc_353 : location_info := LocationInfo file_1 442 10 442 14.
  Definition loc_354 : location_info := LocationInfo file_1 440 25 440 55.
  Definition loc_355 : location_info := LocationInfo file_1 440 25 440 55.
  Definition loc_356 : location_info := LocationInfo file_1 440 26 440 48.
  Definition loc_357 : location_info := LocationInfo file_1 440 46 440 47.
  Definition loc_358 : location_info := LocationInfo file_1 440 46 440 47.
  Definition loc_361 : location_info := LocationInfo file_1 439 22 439 83.
  Definition loc_362 : location_info := LocationInfo file_1 439 22 439 38.
  Definition loc_363 : location_info := LocationInfo file_1 439 22 439 38.
  Definition loc_364 : location_info := LocationInfo file_1 439 39 439 82.
  Definition loc_365 : location_info := LocationInfo file_1 439 40 439 59.
  Definition loc_366 : location_info := LocationInfo file_1 439 53 439 59.
  Definition loc_367 : location_info := LocationInfo file_1 439 53 439 59.
  Definition loc_368 : location_info := LocationInfo file_1 439 62 439 81.
  Definition loc_369 : location_info := LocationInfo file_1 439 62 439 81.
  Definition loc_374 : location_info := LocationInfo file_1 533 1 533 20.
  Definition loc_375 : location_info := LocationInfo file_1 534 1 534 7.
  Definition loc_376 : location_info := LocationInfo file_1 536 1 537 13.
  Definition loc_377 : location_info := LocationInfo file_1 539 1 539 22.
  Definition loc_378 : location_info := LocationInfo file_1 540 6 540 11.
  Definition loc_379 : location_info := LocationInfo file_1 540 1 541 38.
  Definition loc_380 : location_info := LocationInfo file_1 542 1 542 26.
  Definition loc_381 : location_info := LocationInfo file_1 543 1 543 43.
  Definition loc_382 : location_info := LocationInfo file_1 546 1 546 28.
  Definition loc_383 : location_info := LocationInfo file_1 547 1 547 37.
  Definition loc_384 : location_info := LocationInfo file_1 550 6 550 11.
  Definition loc_385 : location_info := LocationInfo file_1 550 1 554 2.
  Definition loc_386 : location_info := LocationInfo file_1 557 1 557 49.
  Definition loc_387 : location_info := LocationInfo file_1 560 6 560 20.
  Definition loc_388 : location_info := LocationInfo file_1 560 1 563 2.
  Definition loc_389 : location_info := LocationInfo file_1 565 1 565 10.
  Definition loc_390 : location_info := LocationInfo file_1 565 8 565 9.
  Definition loc_391 : location_info := LocationInfo file_1 560 41 563 2.
  Definition loc_392 : location_info := LocationInfo file_1 561 2 561 29.
  Definition loc_393 : location_info := LocationInfo file_1 562 2 562 6.
  Definition loc_394 : location_info := LocationInfo file_1 560 1 563 2.
  Definition loc_395 : location_info := LocationInfo file_1 560 36 560 39.
  Definition loc_396 : location_info := LocationInfo file_1 560 36 560 37.
  Definition loc_397 : location_info := LocationInfo file_1 562 2 562 3.
  Definition loc_398 : location_info := LocationInfo file_1 561 2 561 19.
  Definition loc_399 : location_info := LocationInfo file_1 561 2 561 19.
  Definition loc_400 : location_info := LocationInfo file_1 561 20 561 24.
  Definition loc_401 : location_info := LocationInfo file_1 561 20 561 24.
  Definition loc_402 : location_info := LocationInfo file_1 561 26 561 27.
  Definition loc_403 : location_info := LocationInfo file_1 561 26 561 27.
  Definition loc_404 : location_info := LocationInfo file_1 560 22 560 34.
  Definition loc_405 : location_info := LocationInfo file_1 560 22 560 23.
  Definition loc_406 : location_info := LocationInfo file_1 560 22 560 23.
  Definition loc_407 : location_info := LocationInfo file_1 560 26 560 34.
  Definition loc_408 : location_info := LocationInfo file_1 560 26 560 34.
  Definition loc_409 : location_info := LocationInfo file_1 560 6 560 7.
  Definition loc_410 : location_info := LocationInfo file_1 560 10 560 20.
  Definition loc_411 : location_info := LocationInfo file_1 560 10 560 20.
  Definition loc_412 : location_info := LocationInfo file_1 557 1 557 2.
  Definition loc_413 : location_info := LocationInfo file_1 557 5 557 48.
  Definition loc_414 : location_info := LocationInfo file_1 557 5 557 21.
  Definition loc_415 : location_info := LocationInfo file_1 557 5 557 21.
  Definition loc_416 : location_info := LocationInfo file_1 557 22 557 47.
  Definition loc_417 : location_info := LocationInfo file_1 557 22 557 26.
  Definition loc_418 : location_info := LocationInfo file_1 557 22 557 26.
  Definition loc_419 : location_info := LocationInfo file_1 557 29 557 47.
  Definition loc_420 : location_info := LocationInfo file_1 557 30 557 40.
  Definition loc_421 : location_info := LocationInfo file_1 557 30 557 40.
  Definition loc_422 : location_info := LocationInfo file_1 557 44 557 46.
  Definition loc_423 : location_info := LocationInfo file_1 550 32 554 2.
  Definition loc_424 : location_info := LocationInfo file_1 551 2 551 17.
  Definition loc_425 : location_info := LocationInfo file_1 552 2 552 27.
  Definition loc_426 : location_info := LocationInfo file_1 553 2 553 6.
  Definition loc_427 : location_info := LocationInfo file_1 550 1 554 2.
  Definition loc_428 : location_info := LocationInfo file_1 550 27 550 30.
  Definition loc_429 : location_info := LocationInfo file_1 550 27 550 28.
  Definition loc_430 : location_info := LocationInfo file_1 553 2 553 3.
  Definition loc_431 : location_info := LocationInfo file_1 552 2 552 16.
  Definition loc_432 : location_info := LocationInfo file_1 552 2 552 16.
  Definition loc_433 : location_info := LocationInfo file_1 552 17 552 25.
  Definition loc_434 : location_info := LocationInfo file_1 552 18 552 25.
  Definition loc_435 : location_info := LocationInfo file_1 552 18 552 19.
  Definition loc_436 : location_info := LocationInfo file_1 552 18 552 19.
  Definition loc_437 : location_info := LocationInfo file_1 551 2 551 9.
  Definition loc_438 : location_info := LocationInfo file_1 551 2 551 3.
  Definition loc_439 : location_info := LocationInfo file_1 551 2 551 3.
  Definition loc_440 : location_info := LocationInfo file_1 551 12 551 16.
  Definition loc_441 : location_info := LocationInfo file_1 551 12 551 16.
  Definition loc_442 : location_info := LocationInfo file_1 550 13 550 25.
  Definition loc_443 : location_info := LocationInfo file_1 550 13 550 14.
  Definition loc_444 : location_info := LocationInfo file_1 550 13 550 14.
  Definition loc_445 : location_info := LocationInfo file_1 550 17 550 25.
  Definition loc_446 : location_info := LocationInfo file_1 550 17 550 25.
  Definition loc_447 : location_info := LocationInfo file_1 550 6 550 7.
  Definition loc_448 : location_info := LocationInfo file_1 550 10 550 11.
  Definition loc_449 : location_info := LocationInfo file_1 547 1 547 7.
  Definition loc_450 : location_info := LocationInfo file_1 547 1 547 7.
  Definition loc_451 : location_info := LocationInfo file_1 547 8 547 9.
  Definition loc_452 : location_info := LocationInfo file_1 547 8 547 9.
  Definition loc_453 : location_info := LocationInfo file_1 547 11 547 12.
  Definition loc_454 : location_info := LocationInfo file_1 547 14 547 35.
  Definition loc_455 : location_info := LocationInfo file_1 547 14 547 24.
  Definition loc_456 : location_info := LocationInfo file_1 547 27 547 35.
  Definition loc_457 : location_info := LocationInfo file_1 547 27 547 35.
  Definition loc_458 : location_info := LocationInfo file_1 546 1 546 2.
  Definition loc_459 : location_info := LocationInfo file_1 546 5 546 27.
  Definition loc_460 : location_info := LocationInfo file_1 546 5 546 21.
  Definition loc_461 : location_info := LocationInfo file_1 546 5 546 21.
  Definition loc_462 : location_info := LocationInfo file_1 546 22 546 26.
  Definition loc_463 : location_info := LocationInfo file_1 546 22 546 26.
  Definition loc_464 : location_info := LocationInfo file_1 543 1 543 16.
  Definition loc_465 : location_info := LocationInfo file_1 543 1 543 5.
  Definition loc_466 : location_info := LocationInfo file_1 543 1 543 5.
  Definition loc_467 : location_info := LocationInfo file_1 543 19 543 42.
  Definition loc_468 : location_info := LocationInfo file_1 543 19 543 23.
  Definition loc_469 : location_info := LocationInfo file_1 543 19 543 23.
  Definition loc_470 : location_info := LocationInfo file_1 543 26 543 42.
  Definition loc_471 : location_info := LocationInfo file_1 543 27 543 35.
  Definition loc_472 : location_info := LocationInfo file_1 543 27 543 35.
  Definition loc_473 : location_info := LocationInfo file_1 543 39 543 41.
  Definition loc_474 : location_info := LocationInfo file_1 542 1 542 18.
  Definition loc_475 : location_info := LocationInfo file_1 542 1 542 5.
  Definition loc_476 : location_info := LocationInfo file_1 542 1 542 5.
  Definition loc_477 : location_info := LocationInfo file_1 542 21 542 25.
  Definition loc_478 : location_info := LocationInfo file_1 542 21 542 25.
  Definition loc_479 : location_info := LocationInfo file_1 540 1 541 38.
  Definition loc_480 : location_info := LocationInfo file_1 541 2 541 38.
  Definition loc_481 : location_info := LocationInfo file_1 540 1 541 38.
  Definition loc_482 : location_info := LocationInfo file_1 540 23 540 26.
  Definition loc_483 : location_info := LocationInfo file_1 540 23 540 24.
  Definition loc_484 : location_info := LocationInfo file_1 541 2 541 16.
  Definition loc_485 : location_info := LocationInfo file_1 541 2 541 16.
  Definition loc_486 : location_info := LocationInfo file_1 541 17 541 36.
  Definition loc_487 : location_info := LocationInfo file_1 541 18 541 36.
  Definition loc_488 : location_info := LocationInfo file_1 541 18 541 36.
  Definition loc_489 : location_info := LocationInfo file_1 541 18 541 33.
  Definition loc_490 : location_info := LocationInfo file_1 541 18 541 33.
  Definition loc_491 : location_info := LocationInfo file_1 541 18 541 22.
  Definition loc_492 : location_info := LocationInfo file_1 541 18 541 22.
  Definition loc_493 : location_info := LocationInfo file_1 541 34 541 35.
  Definition loc_494 : location_info := LocationInfo file_1 541 34 541 35.
  Definition loc_495 : location_info := LocationInfo file_1 540 13 540 21.
  Definition loc_496 : location_info := LocationInfo file_1 540 13 540 14.
  Definition loc_497 : location_info := LocationInfo file_1 540 13 540 14.
  Definition loc_498 : location_info := LocationInfo file_1 540 18 540 21.
  Definition loc_499 : location_info := LocationInfo file_1 540 6 540 7.
  Definition loc_500 : location_info := LocationInfo file_1 540 10 540 11.
  Definition loc_501 : location_info := LocationInfo file_1 539 1 539 8.
  Definition loc_502 : location_info := LocationInfo file_1 539 1 539 8.
  Definition loc_503 : location_info := LocationInfo file_1 539 9 539 20.
  Definition loc_504 : location_info := LocationInfo file_1 539 10 539 20.
  Definition loc_505 : location_info := LocationInfo file_1 539 10 539 14.
  Definition loc_506 : location_info := LocationInfo file_1 539 10 539 14.
  Definition loc_507 : location_info := LocationInfo file_1 537 2 537 13.
  Definition loc_508 : location_info := LocationInfo file_1 537 9 537 12.
  Definition loc_509 : location_info := LocationInfo file_1 537 10 537 12.
  Definition loc_510 : location_info := LocationInfo file_1 536 1 537 13.
  Definition loc_511 : location_info := LocationInfo file_1 536 5 536 16.
  Definition loc_512 : location_info := LocationInfo file_1 536 5 536 9.
  Definition loc_513 : location_info := LocationInfo file_1 536 5 536 9.
  Definition loc_514 : location_info := LocationInfo file_1 536 12 536 16.
  Definition loc_517 : location_info := LocationInfo file_1 373 1 373 15.
  Definition loc_518 : location_info := LocationInfo file_1 373 15 373 2.
  Definition loc_519 : location_info := LocationInfo file_1 374 1 374 40.
  Definition loc_520 : location_info := LocationInfo file_1 376 1 376 25.
  Definition loc_521 : location_info := LocationInfo file_1 377 1 378 24.
  Definition loc_522 : location_info := LocationInfo file_1 380 1 380 31.
  Definition loc_523 : location_info := LocationInfo file_1 380 8 380 30.
  Definition loc_524 : location_info := LocationInfo file_1 380 8 380 24.
  Definition loc_525 : location_info := LocationInfo file_1 380 8 380 24.
  Definition loc_526 : location_info := LocationInfo file_1 380 25 380 29.
  Definition loc_527 : location_info := LocationInfo file_1 380 25 380 29.
  Definition loc_528 : location_info := LocationInfo file_1 378 2 378 24.
  Definition loc_529 : location_info := LocationInfo file_1 378 9 378 23.
  Definition loc_530 : location_info := LocationInfo file_1 377 1 378 24.
  Definition loc_531 : location_info := LocationInfo file_1 377 5 377 56.
  Definition loc_532 : location_info := LocationInfo file_1 377 5 377 29.
  Definition loc_533 : location_info := LocationInfo file_1 377 5 377 9.
  Definition loc_534 : location_info := LocationInfo file_1 377 5 377 9.
  Definition loc_535 : location_info := LocationInfo file_1 377 12 377 29.
  Definition loc_536 : location_info := LocationInfo file_1 377 12 377 29.
  Definition loc_537 : location_info := LocationInfo file_1 377 12 377 16.
  Definition loc_538 : location_info := LocationInfo file_1 377 12 377 16.
  Definition loc_539 : location_info := LocationInfo file_1 377 33 377 56.
  Definition loc_540 : location_info := LocationInfo file_1 377 33 377 37.
  Definition loc_541 : location_info := LocationInfo file_1 377 33 377 37.
  Definition loc_542 : location_info := LocationInfo file_1 377 41 377 56.
  Definition loc_543 : location_info := LocationInfo file_1 377 41 377 56.
  Definition loc_544 : location_info := LocationInfo file_1 377 41 377 45.
  Definition loc_545 : location_info := LocationInfo file_1 377 41 377 45.
  Definition loc_546 : location_info := LocationInfo file_1 376 1 376 5.
  Definition loc_547 : location_info := LocationInfo file_1 376 1 376 24.
  Definition loc_548 : location_info := LocationInfo file_1 376 1 376 5.
  Definition loc_549 : location_info := LocationInfo file_1 376 1 376 5.
  Definition loc_550 : location_info := LocationInfo file_1 376 9 376 24.
  Definition loc_551 : location_info := LocationInfo file_1 376 10 376 14.
  Definition loc_552 : location_info := LocationInfo file_1 376 18 376 23.
  Definition loc_553 : location_info := LocationInfo file_1 376 18 376 23.
  Definition loc_554 : location_info := LocationInfo file_1 374 20 374 39.
  Definition loc_555 : location_info := LocationInfo file_1 374 20 374 36.
  Definition loc_556 : location_info := LocationInfo file_1 374 20 374 36.
  Definition loc_557 : location_info := LocationInfo file_1 374 37 374 38.
  Definition loc_558 : location_info := LocationInfo file_1 374 37 374 38.
  Definition loc_561 : location_info := LocationInfo file_1 373 1 373 14.
  Definition loc_562 : location_info := LocationInfo file_1 373 2 373 14.
  Definition loc_563 : location_info := LocationInfo file_1 373 3 373 7.
  Definition loc_564 : location_info := LocationInfo file_1 373 3 373 7.
  Definition loc_567 : location_info := LocationInfo file_1 397 1 397 15.
  Definition loc_568 : location_info := LocationInfo file_1 397 15 397 2.
  Definition loc_569 : location_info := LocationInfo file_1 398 1 398 31.
  Definition loc_570 : location_info := LocationInfo file_1 399 1 399 24.
  Definition loc_571 : location_info := LocationInfo file_1 401 1 401 31.
  Definition loc_572 : location_info := LocationInfo file_1 409 1 428 2.
  Definition loc_573 : location_info := LocationInfo file_1 429 1 429 15.
  Definition loc_574 : location_info := LocationInfo file_1 429 15 429 2.
  Definition loc_575 : location_info := LocationInfo file_1 431 1 431 18.
  Definition loc_576 : location_info := LocationInfo file_1 434 1 434 45.
  Definition loc_577 : location_info := LocationInfo file_1 434 1 434 9.
  Definition loc_578 : location_info := LocationInfo file_1 434 1 434 9.
  Definition loc_579 : location_info := LocationInfo file_1 434 10 434 18.
  Definition loc_580 : location_info := LocationInfo file_1 434 11 434 18.
  Definition loc_581 : location_info := LocationInfo file_1 434 11 434 12.
  Definition loc_582 : location_info := LocationInfo file_1 434 11 434 12.
  Definition loc_583 : location_info := LocationInfo file_1 434 20 434 43.
  Definition loc_584 : location_info := LocationInfo file_1 434 21 434 43.
  Definition loc_585 : location_info := LocationInfo file_1 434 21 434 43.
  Definition loc_586 : location_info := LocationInfo file_1 434 21 434 36.
  Definition loc_587 : location_info := LocationInfo file_1 434 21 434 36.
  Definition loc_588 : location_info := LocationInfo file_1 434 21 434 25.
  Definition loc_589 : location_info := LocationInfo file_1 434 21 434 25.
  Definition loc_590 : location_info := LocationInfo file_1 434 37 434 42.
  Definition loc_591 : location_info := LocationInfo file_1 434 37 434 42.
  Definition loc_592 : location_info := LocationInfo file_1 431 1 431 9.
  Definition loc_593 : location_info := LocationInfo file_1 431 1 431 2.
  Definition loc_594 : location_info := LocationInfo file_1 431 1 431 2.
  Definition loc_595 : location_info := LocationInfo file_1 431 12 431 17.
  Definition loc_596 : location_info := LocationInfo file_1 431 12 431 17.
  Definition loc_597 : location_info := LocationInfo file_1 429 1 429 14.
  Definition loc_598 : location_info := LocationInfo file_1 429 2 429 14.
  Definition loc_599 : location_info := LocationInfo file_1 429 3 429 7.
  Definition loc_600 : location_info := LocationInfo file_1 429 3 429 7.
  Definition loc_601 : location_info := LocationInfo file_1 409 30 428 2.
  Definition loc_602 : location_info := LocationInfo file_1 411 2 411 39.
  Definition loc_603 : location_info := LocationInfo file_1 412 2 412 16.
  Definition loc_604 : location_info := LocationInfo file_1 412 16 412 3.
  Definition loc_605 : location_info := LocationInfo file_1 415 2 416 9.
  Definition loc_606 : location_info := LocationInfo file_1 419 2 419 30.
  Definition loc_607 : location_info := LocationInfo file_1 420 2 420 36.
  Definition loc_608 : location_info := LocationInfo file_1 423 2 427 3.
  Definition loc_609 : location_info := LocationInfo file_1 409 1 428 2.
  Definition loc_610 : location_info := LocationInfo file_1 409 21 409 28.
  Definition loc_611 : location_info := LocationInfo file_1 409 21 409 26.
  Definition loc_612 : location_info := LocationInfo file_1 423 17 425 3.
  Definition loc_613 : location_info := LocationInfo file_1 424 3 424 9.
  Definition loc_614 : location_info := LocationInfo file_1 424 3 424 4.
  Definition loc_615 : location_info := LocationInfo file_1 424 7 424 8.
  Definition loc_616 : location_info := LocationInfo file_1 424 7 424 8.
  Definition loc_617 : location_info := LocationInfo file_1 425 9 427 3.
  Definition loc_618 : location_info := LocationInfo file_1 426 3 426 13.
  Definition loc_619 : location_info := LocationInfo file_1 426 3 426 4.
  Definition loc_620 : location_info := LocationInfo file_1 426 7 426 12.
  Definition loc_621 : location_info := LocationInfo file_1 426 7 426 12.
  Definition loc_622 : location_info := LocationInfo file_1 423 6 423 15.
  Definition loc_623 : location_info := LocationInfo file_1 423 6 423 7.
  Definition loc_624 : location_info := LocationInfo file_1 423 6 423 7.
  Definition loc_625 : location_info := LocationInfo file_1 423 10 423 15.
  Definition loc_626 : location_info := LocationInfo file_1 423 10 423 15.
  Definition loc_627 : location_info := LocationInfo file_1 420 2 420 14.
  Definition loc_628 : location_info := LocationInfo file_1 420 2 420 7.
  Definition loc_629 : location_info := LocationInfo file_1 420 2 420 7.
  Definition loc_630 : location_info := LocationInfo file_1 420 17 420 35.
  Definition loc_631 : location_info := LocationInfo file_1 419 2 419 15.
  Definition loc_632 : location_info := LocationInfo file_1 419 2 419 15.
  Definition loc_633 : location_info := LocationInfo file_1 419 16 419 28.
  Definition loc_634 : location_info := LocationInfo file_1 419 17 419 28.
  Definition loc_635 : location_info := LocationInfo file_1 419 17 419 22.
  Definition loc_636 : location_info := LocationInfo file_1 419 17 419 22.
  Definition loc_637 : location_info := LocationInfo file_1 416 3 416 9.
  Definition loc_638 : location_info := LocationInfo file_1 415 2 416 9.
  Definition loc_639 : location_info := LocationInfo file_1 415 6 415 82.
  Definition loc_640 : location_info := LocationInfo file_1 415 6 415 57.
  Definition loc_641 : location_info := LocationInfo file_1 415 6 415 29.
  Definition loc_642 : location_info := LocationInfo file_1 415 6 415 11.
  Definition loc_643 : location_info := LocationInfo file_1 415 6 415 11.
  Definition loc_644 : location_info := LocationInfo file_1 415 15 415 29.
  Definition loc_645 : location_info := LocationInfo file_1 415 33 415 57.
  Definition loc_646 : location_info := LocationInfo file_1 415 33 415 43.
  Definition loc_647 : location_info := LocationInfo file_1 415 33 415 43.
  Definition loc_648 : location_info := LocationInfo file_1 415 44 415 56.
  Definition loc_649 : location_info := LocationInfo file_1 415 45 415 56.
  Definition loc_650 : location_info := LocationInfo file_1 415 45 415 50.
  Definition loc_651 : location_info := LocationInfo file_1 415 45 415 50.
  Definition loc_652 : location_info := LocationInfo file_1 415 61 415 82.
  Definition loc_653 : location_info := LocationInfo file_1 415 61 415 73.
  Definition loc_654 : location_info := LocationInfo file_1 415 61 415 73.
  Definition loc_655 : location_info := LocationInfo file_1 415 61 415 66.
  Definition loc_656 : location_info := LocationInfo file_1 415 61 415 66.
  Definition loc_657 : location_info := LocationInfo file_1 415 77 415 82.
  Definition loc_658 : location_info := LocationInfo file_1 415 77 415 82.
  Definition loc_659 : location_info := LocationInfo file_1 412 2 412 15.
  Definition loc_660 : location_info := LocationInfo file_1 412 3 412 15.
  Definition loc_661 : location_info := LocationInfo file_1 412 4 412 8.
  Definition loc_662 : location_info := LocationInfo file_1 412 4 412 8.
  Definition loc_663 : location_info := LocationInfo file_1 411 2 411 7.
  Definition loc_664 : location_info := LocationInfo file_1 411 10 411 38.
  Definition loc_665 : location_info := LocationInfo file_1 411 10 411 22.
  Definition loc_666 : location_info := LocationInfo file_1 411 10 411 22.
  Definition loc_667 : location_info := LocationInfo file_1 411 23 411 27.
  Definition loc_668 : location_info := LocationInfo file_1 411 23 411 27.
  Definition loc_669 : location_info := LocationInfo file_1 411 29 411 30.
  Definition loc_670 : location_info := LocationInfo file_1 411 29 411 30.
  Definition loc_671 : location_info := LocationInfo file_1 411 32 411 37.
  Definition loc_672 : location_info := LocationInfo file_1 411 32 411 37.
  Definition loc_673 : location_info := LocationInfo file_1 409 8 409 19.
  Definition loc_674 : location_info := LocationInfo file_1 409 8 409 13.
  Definition loc_675 : location_info := LocationInfo file_1 409 8 409 13.
  Definition loc_676 : location_info := LocationInfo file_1 409 16 409 19.
  Definition loc_677 : location_info := LocationInfo file_1 401 1 401 9.
  Definition loc_678 : location_info := LocationInfo file_1 401 1 401 2.
  Definition loc_679 : location_info := LocationInfo file_1 401 1 401 2.
  Definition loc_680 : location_info := LocationInfo file_1 401 12 401 30.
  Definition loc_681 : location_info := LocationInfo file_1 398 22 398 30.
  Definition loc_682 : location_info := LocationInfo file_1 398 22 398 30.
  Definition loc_683 : location_info := LocationInfo file_1 398 22 398 23.
  Definition loc_684 : location_info := LocationInfo file_1 398 22 398 23.
  Definition loc_687 : location_info := LocationInfo file_1 397 1 397 14.
  Definition loc_688 : location_info := LocationInfo file_1 397 2 397 14.
  Definition loc_689 : location_info := LocationInfo file_1 397 3 397 7.
  Definition loc_690 : location_info := LocationInfo file_1 397 3 397 7.
  Definition loc_693 : location_info := LocationInfo file_1 466 1 466 24.
  Definition loc_694 : location_info := LocationInfo file_1 468 1 469 24.
  Definition loc_695 : location_info := LocationInfo file_1 471 1 471 25.
  Definition loc_696 : location_info := LocationInfo file_1 474 1 479 2.
  Definition loc_697 : location_info := LocationInfo file_1 481 1 481 17.
  Definition loc_698 : location_info := LocationInfo file_1 483 1 483 10.
  Definition loc_699 : location_info := LocationInfo file_1 483 8 483 9.
  Definition loc_700 : location_info := LocationInfo file_1 483 8 483 9.
  Definition loc_701 : location_info := LocationInfo file_1 481 1 481 12.
  Definition loc_702 : location_info := LocationInfo file_1 481 1 481 2.
  Definition loc_703 : location_info := LocationInfo file_1 481 1 481 2.
  Definition loc_704 : location_info := LocationInfo file_1 481 15 481 16.
  Definition loc_705 : location_info := LocationInfo file_1 474 26 479 2.
  Definition loc_706 : location_info := LocationInfo file_1 475 2 475 13.
  Definition loc_707 : location_info := LocationInfo file_1 476 2 476 42.
  Definition loc_708 : location_info := LocationInfo file_1 477 2 477 26.
  Definition loc_709 : location_info := LocationInfo file_1 478 2 478 62.
  Definition loc_710 : location_info := LocationInfo file_1 478 2 478 15.
  Definition loc_711 : location_info := LocationInfo file_1 478 2 478 15.
  Definition loc_712 : location_info := LocationInfo file_1 478 16 478 28.
  Definition loc_713 : location_info := LocationInfo file_1 478 17 478 28.
  Definition loc_714 : location_info := LocationInfo file_1 478 17 478 22.
  Definition loc_715 : location_info := LocationInfo file_1 478 17 478 22.
  Definition loc_716 : location_info := LocationInfo file_1 478 30 478 60.
  Definition loc_717 : location_info := LocationInfo file_1 478 31 478 60.
  Definition loc_718 : location_info := LocationInfo file_1 478 31 478 60.
  Definition loc_719 : location_info := LocationInfo file_1 478 31 478 46.
  Definition loc_720 : location_info := LocationInfo file_1 478 31 478 46.
  Definition loc_721 : location_info := LocationInfo file_1 478 31 478 35.
  Definition loc_722 : location_info := LocationInfo file_1 478 31 478 35.
  Definition loc_723 : location_info := LocationInfo file_1 478 47 478 59.
  Definition loc_724 : location_info := LocationInfo file_1 478 47 478 59.
  Definition loc_725 : location_info := LocationInfo file_1 478 47 478 52.
  Definition loc_726 : location_info := LocationInfo file_1 478 47 478 52.
  Definition loc_727 : location_info := LocationInfo file_1 477 2 477 14.
  Definition loc_728 : location_info := LocationInfo file_1 477 2 477 7.
  Definition loc_729 : location_info := LocationInfo file_1 477 2 477 7.
  Definition loc_730 : location_info := LocationInfo file_1 477 17 477 25.
  Definition loc_731 : location_info := LocationInfo file_1 477 17 477 25.
  Definition loc_732 : location_info := LocationInfo file_1 477 17 477 18.
  Definition loc_733 : location_info := LocationInfo file_1 477 17 477 18.
  Definition loc_734 : location_info := LocationInfo file_1 476 2 476 7.
  Definition loc_735 : location_info := LocationInfo file_1 476 10 476 41.
  Definition loc_736 : location_info := LocationInfo file_1 476 10 476 22.
  Definition loc_737 : location_info := LocationInfo file_1 476 10 476 22.
  Definition loc_738 : location_info := LocationInfo file_1 476 23 476 27.
  Definition loc_739 : location_info := LocationInfo file_1 476 23 476 27.
  Definition loc_740 : location_info := LocationInfo file_1 476 29 476 30.
  Definition loc_741 : location_info := LocationInfo file_1 476 29 476 30.
  Definition loc_742 : location_info := LocationInfo file_1 476 32 476 40.
  Definition loc_743 : location_info := LocationInfo file_1 476 32 476 40.
  Definition loc_744 : location_info := LocationInfo file_1 476 32 476 33.
  Definition loc_745 : location_info := LocationInfo file_1 476 32 476 33.
  Definition loc_746 : location_info := LocationInfo file_1 475 2 475 10.
  Definition loc_747 : location_info := LocationInfo file_1 475 2 475 3.
  Definition loc_748 : location_info := LocationInfo file_1 475 2 475 3.
  Definition loc_749 : location_info := LocationInfo file_1 474 8 474 24.
  Definition loc_750 : location_info := LocationInfo file_1 474 8 474 16.
  Definition loc_751 : location_info := LocationInfo file_1 474 8 474 16.
  Definition loc_752 : location_info := LocationInfo file_1 474 8 474 9.
  Definition loc_753 : location_info := LocationInfo file_1 474 8 474 9.
  Definition loc_754 : location_info := LocationInfo file_1 474 19 474 24.
  Definition loc_755 : location_info := LocationInfo file_1 474 19 474 24.
  Definition loc_756 : location_info := LocationInfo file_1 471 1 471 14.
  Definition loc_757 : location_info := LocationInfo file_1 471 1 471 14.
  Definition loc_758 : location_info := LocationInfo file_1 471 15 471 23.
  Definition loc_759 : location_info := LocationInfo file_1 471 16 471 23.
  Definition loc_760 : location_info := LocationInfo file_1 471 16 471 17.
  Definition loc_761 : location_info := LocationInfo file_1 471 16 471 17.
  Definition loc_762 : location_info := LocationInfo file_1 469 2 469 24.
  Definition loc_763 : location_info := LocationInfo file_1 469 9 469 23.
  Definition loc_764 : location_info := LocationInfo file_1 468 1 469 24.
  Definition loc_765 : location_info := LocationInfo file_1 468 5 468 55.
  Definition loc_766 : location_info := LocationInfo file_1 468 5 468 35.
  Definition loc_767 : location_info := LocationInfo file_1 468 5 468 13.
  Definition loc_768 : location_info := LocationInfo file_1 468 5 468 13.
  Definition loc_769 : location_info := LocationInfo file_1 468 5 468 6.
  Definition loc_770 : location_info := LocationInfo file_1 468 5 468 6.
  Definition loc_771 : location_info := LocationInfo file_1 468 17 468 35.
  Definition loc_772 : location_info := LocationInfo file_1 468 39 468 55.
  Definition loc_773 : location_info := LocationInfo file_1 468 39 468 47.
  Definition loc_774 : location_info := LocationInfo file_1 468 39 468 47.
  Definition loc_775 : location_info := LocationInfo file_1 468 39 468 40.
  Definition loc_776 : location_info := LocationInfo file_1 468 39 468 40.
  Definition loc_777 : location_info := LocationInfo file_1 468 50 468 55.
  Definition loc_778 : location_info := LocationInfo file_1 468 50 468 55.
  Definition loc_781 : location_info := LocationInfo file_1 488 1 488 17.
  Definition loc_782 : location_info := LocationInfo file_1 490 6 490 11.
  Definition loc_783 : location_info := LocationInfo file_1 490 1 491 112.
  Definition loc_784 : location_info := LocationInfo file_1 490 1 491 112.
  Definition loc_785 : location_info := LocationInfo file_1 491 2 491 112.
  Definition loc_786 : location_info := LocationInfo file_1 490 1 491 112.
  Definition loc_787 : location_info := LocationInfo file_1 490 34 490 37.
  Definition loc_788 : location_info := LocationInfo file_1 490 34 490 35.
  Definition loc_789 : location_info := LocationInfo file_1 491 2 491 12.
  Definition loc_790 : location_info := LocationInfo file_1 491 2 491 12.
  Definition loc_791 : location_info := LocationInfo file_1 491 13 491 110.
  Definition loc_792 : location_info := LocationInfo file_1 491 13 491 98.
  Definition loc_793 : location_info := LocationInfo file_1 491 30 491 98.
  Definition loc_794 : location_info := LocationInfo file_1 491 39 491 97.
  Definition loc_795 : location_info := LocationInfo file_1 491 40 491 74.
  Definition loc_796 : location_info := LocationInfo file_1 491 53 491 74.
  Definition loc_797 : location_info := LocationInfo file_1 491 54 491 70.
  Definition loc_798 : location_info := LocationInfo file_1 491 54 491 70.
  Definition loc_799 : location_info := LocationInfo file_1 491 71 491 72.
  Definition loc_800 : location_info := LocationInfo file_1 491 71 491 72.
  Definition loc_801 : location_info := LocationInfo file_1 491 77 491 96.
  Definition loc_802 : location_info := LocationInfo file_1 491 77 491 96.
  Definition loc_803 : location_info := LocationInfo file_1 491 101 491 110.
  Definition loc_804 : location_info := LocationInfo file_1 491 102 491 103.
  Definition loc_805 : location_info := LocationInfo file_1 491 102 491 103.
  Definition loc_806 : location_info := LocationInfo file_1 491 107 491 109.
  Definition loc_807 : location_info := LocationInfo file_1 490 13 490 32.
  Definition loc_808 : location_info := LocationInfo file_1 490 13 490 14.
  Definition loc_809 : location_info := LocationInfo file_1 490 13 490 14.
  Definition loc_810 : location_info := LocationInfo file_1 490 17 490 32.
  Definition loc_811 : location_info := LocationInfo file_1 490 18 490 19.
  Definition loc_812 : location_info := LocationInfo file_1 490 23 490 31.
  Definition loc_813 : location_info := LocationInfo file_1 490 23 490 31.
  Definition loc_814 : location_info := LocationInfo file_1 490 23 490 24.
  Definition loc_815 : location_info := LocationInfo file_1 490 23 490 24.
  Definition loc_816 : location_info := LocationInfo file_1 490 6 490 7.
  Definition loc_817 : location_info := LocationInfo file_1 490 10 490 11.
  Definition loc_820 : location_info := LocationInfo file_1 499 1 499 24.
  Definition loc_821 : location_info := LocationInfo file_1 500 1 500 20.
  Definition loc_822 : location_info := LocationInfo file_1 503 1 504 6.
  Definition loc_823 : location_info := LocationInfo file_1 505 1 506 24.
  Definition loc_824 : location_info := LocationInfo file_1 509 1 509 99.
  Definition loc_825 : location_info := LocationInfo file_1 510 1 510 40.
  Definition loc_826 : location_info := LocationInfo file_1 512 1 513 20.
  Definition loc_827 : location_info := LocationInfo file_1 515 1 515 10.
  Definition loc_828 : location_info := LocationInfo file_1 515 8 515 9.
  Definition loc_829 : location_info := LocationInfo file_1 515 8 515 9.
  Definition loc_830 : location_info := LocationInfo file_1 513 2 513 20.
  Definition loc_831 : location_info := LocationInfo file_1 513 2 513 16.
  Definition loc_832 : location_info := LocationInfo file_1 513 2 513 16.
  Definition loc_833 : location_info := LocationInfo file_1 513 17 513 18.
  Definition loc_834 : location_info := LocationInfo file_1 513 17 513 18.
  Definition loc_835 : location_info := LocationInfo file_1 512 1 513 20.
  Definition loc_836 : location_info := LocationInfo file_1 512 5 512 13.
  Definition loc_837 : location_info := LocationInfo file_1 512 5 512 9.
  Definition loc_838 : location_info := LocationInfo file_1 512 5 512 9.
  Definition loc_839 : location_info := LocationInfo file_1 512 12 512 13.
  Definition loc_840 : location_info := LocationInfo file_1 510 1 510 2.
  Definition loc_841 : location_info := LocationInfo file_1 510 5 510 39.
  Definition loc_842 : location_info := LocationInfo file_1 510 5 510 23.
  Definition loc_843 : location_info := LocationInfo file_1 510 5 510 23.
  Definition loc_844 : location_info := LocationInfo file_1 510 24 510 28.
  Definition loc_845 : location_info := LocationInfo file_1 510 24 510 28.
  Definition loc_846 : location_info := LocationInfo file_1 510 30 510 31.
  Definition loc_847 : location_info := LocationInfo file_1 510 30 510 31.
  Definition loc_848 : location_info := LocationInfo file_1 510 33 510 38.
  Definition loc_849 : location_info := LocationInfo file_1 510 33 510 38.
  Definition loc_850 : location_info := LocationInfo file_1 509 1 509 2.
  Definition loc_851 : location_info := LocationInfo file_1 509 5 509 98.
  Definition loc_852 : location_info := LocationInfo file_1 509 24 509 98.
  Definition loc_853 : location_info := LocationInfo file_1 509 26 509 63.
  Definition loc_854 : location_info := LocationInfo file_1 509 34 509 63.
  Definition loc_855 : location_info := LocationInfo file_1 509 34 509 63.
  Definition loc_856 : location_info := LocationInfo file_1 509 35 509 56.
  Definition loc_857 : location_info := LocationInfo file_1 509 37 509 55.
  Definition loc_858 : location_info := LocationInfo file_1 509 37 509 55.
  Definition loc_859 : location_info := LocationInfo file_1 509 37 509 52.
  Definition loc_860 : location_info := LocationInfo file_1 509 37 509 52.
  Definition loc_861 : location_info := LocationInfo file_1 509 37 509 41.
  Definition loc_862 : location_info := LocationInfo file_1 509 37 509 41.
  Definition loc_863 : location_info := LocationInfo file_1 509 53 509 54.
  Definition loc_864 : location_info := LocationInfo file_1 509 53 509 54.
  Definition loc_865 : location_info := LocationInfo file_1 509 66 509 96.
  Definition loc_866 : location_info := LocationInfo file_1 506 2 506 24.
  Definition loc_867 : location_info := LocationInfo file_1 506 9 506 23.
  Definition loc_868 : location_info := LocationInfo file_1 505 1 506 24.
  Definition loc_869 : location_info := LocationInfo file_1 505 5 505 12.
  Definition loc_870 : location_info := LocationInfo file_1 505 5 505 6.
  Definition loc_871 : location_info := LocationInfo file_1 505 5 505 6.
  Definition loc_872 : location_info := LocationInfo file_1 505 9 505 12.
  Definition loc_873 : location_info := LocationInfo file_1 504 2 504 6.
  Definition loc_874 : location_info := LocationInfo file_1 504 2 504 3.
  Definition loc_875 : location_info := LocationInfo file_1 503 8 503 51.
  Definition loc_876 : location_info := LocationInfo file_1 503 8 503 16.
  Definition loc_877 : location_info := LocationInfo file_1 503 8 503 9.
  Definition loc_878 : location_info := LocationInfo file_1 503 8 503 9.
  Definition loc_879 : location_info := LocationInfo file_1 503 13 503 16.
  Definition loc_880 : location_info := LocationInfo file_1 503 20 503 51.
  Definition loc_881 : location_info := LocationInfo file_1 503 20 503 30.
  Definition loc_882 : location_info := LocationInfo file_1 503 20 503 30.
  Definition loc_883 : location_info := LocationInfo file_1 503 31 503 50.
  Definition loc_884 : location_info := LocationInfo file_1 503 32 503 50.
  Definition loc_885 : location_info := LocationInfo file_1 503 32 503 50.
  Definition loc_886 : location_info := LocationInfo file_1 503 32 503 47.
  Definition loc_887 : location_info := LocationInfo file_1 503 32 503 47.
  Definition loc_888 : location_info := LocationInfo file_1 503 32 503 36.
  Definition loc_889 : location_info := LocationInfo file_1 503 32 503 36.
  Definition loc_890 : location_info := LocationInfo file_1 503 48 503 49.
  Definition loc_891 : location_info := LocationInfo file_1 503 48 503 49.
  Definition loc_892 : location_info := LocationInfo file_1 499 18 499 23.
  Definition loc_893 : location_info := LocationInfo file_1 499 18 499 23.

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

  (* Definition of function [hyp_panic]. *)
  Definition impl_hyp_panic : function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_11 ;
        assert{IntOp i32}: (LocInfoE loc_12 (i2v 0 i32)) ;
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
        locinfo: loc_15 ;
        Return (LocInfoE loc_16 (UnOp (CastOp $ BoolOp) (IntOp i32) (LocInfoE loc_16 (i2v 1 i32))))
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
        locinfo: loc_19 ;
        Return (LocInfoE loc_20 (UnOp (CastOp $ BoolOp) (IntOp i32) (LocInfoE loc_20 (i2v 1 i32))))
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
        locinfo: loc_23 ;
        LocInfoE loc_30 ((LocInfoE loc_31 (!{PtrOp} (LocInfoE loc_32 ("list")))) at{struct_list_head} "next") <-{ PtrOp }
          LocInfoE loc_33 (use{PtrOp} (LocInfoE loc_34 ("list"))) ;
        locinfo: loc_24 ;
        LocInfoE loc_25 ((LocInfoE loc_26 (!{PtrOp} (LocInfoE loc_27 ("list")))) at{struct_list_head} "prev") <-{ PtrOp }
          LocInfoE loc_28 (use{PtrOp} (LocInfoE loc_29 ("list"))) ;
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
        locinfo: loc_65 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_65 ((i2v 0 i32) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_67 (UnOp (CastOp $ IntOp i32) (BoolOp) (LocInfoE loc_67 (Call (LocInfoE loc_69 (global___list_add_valid)) [@{expr} LocInfoE loc_70 (use{PtrOp} (LocInfoE loc_71 ("new"))) ;
                                  LocInfoE loc_72 (use{PtrOp} (LocInfoE loc_73 ("prev"))) ;
                                  LocInfoE loc_74 (use{PtrOp} (LocInfoE loc_75 ("next"))) ])))))
        then
        locinfo: loc_62 ;
          Goto "#2"
        else
        locinfo: loc_38 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_38 ;
        LocInfoE loc_57 ((LocInfoE loc_58 (!{PtrOp} (LocInfoE loc_59 ("next")))) at{struct_list_head} "prev") <-{ PtrOp }
          LocInfoE loc_60 (use{PtrOp} (LocInfoE loc_61 ("new"))) ;
        locinfo: loc_39 ;
        LocInfoE loc_52 ((LocInfoE loc_53 (!{PtrOp} (LocInfoE loc_54 ("new")))) at{struct_list_head} "next") <-{ PtrOp }
          LocInfoE loc_55 (use{PtrOp} (LocInfoE loc_56 ("next"))) ;
        locinfo: loc_40 ;
        LocInfoE loc_47 ((LocInfoE loc_48 (!{PtrOp} (LocInfoE loc_49 ("new")))) at{struct_list_head} "prev") <-{ PtrOp }
          LocInfoE loc_50 (use{PtrOp} (LocInfoE loc_51 ("prev"))) ;
        locinfo: loc_41 ;
        LocInfoE loc_42 ((LocInfoE loc_43 (!{PtrOp} (LocInfoE loc_44 ("prev")))) at{struct_list_head} "next") <-{ PtrOp }
          LocInfoE loc_45 (use{PtrOp} (LocInfoE loc_46 ("new"))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_62 ;
        Return (VOID)
      ]> $
      <[ "#3" :=
        locinfo: loc_38 ;
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
        locinfo: loc_78 ;
        expr: (LocInfoE loc_78 (Call (LocInfoE loc_80 (global___list_add)) [@{expr} LocInfoE loc_81 (use{PtrOp} (LocInfoE loc_82 ("new"))) ;
        LocInfoE loc_83 (use{PtrOp} (LocInfoE loc_84 ("head"))) ;
        LocInfoE loc_85 (use{PtrOp} (LocInfoE loc_86 ((LocInfoE loc_87 (!{PtrOp} (LocInfoE loc_88 ("head")))) at{struct_list_head} "next"))) ])) ;
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
        locinfo: loc_91 ;
        expr: (LocInfoE loc_91 (Call (LocInfoE loc_93 (global___list_add)) [@{expr} LocInfoE loc_94 (use{PtrOp} (LocInfoE loc_95 ("new"))) ;
        LocInfoE loc_96 (use{PtrOp} (LocInfoE loc_97 ((LocInfoE loc_98 (!{PtrOp} (LocInfoE loc_99 ("head")))) at{struct_list_head} "prev"))) ;
        LocInfoE loc_100 (use{PtrOp} (LocInfoE loc_101 ("head"))) ])) ;
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
        locinfo: loc_104 ;
        LocInfoE loc_111 ((LocInfoE loc_112 (!{PtrOp} (LocInfoE loc_113 ("next")))) at{struct_list_head} "prev") <-{ PtrOp }
          LocInfoE loc_114 (use{PtrOp} (LocInfoE loc_115 ("prev"))) ;
        locinfo: loc_105 ;
        LocInfoE loc_106 ((LocInfoE loc_107 (!{PtrOp} (LocInfoE loc_108 ("prev")))) at{struct_list_head} "next") <-{ PtrOp }
          LocInfoE loc_109 (use{PtrOp} (LocInfoE loc_110 ("next"))) ;
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
        locinfo: loc_133 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_133 ((i2v 0 i32) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_135 (UnOp (CastOp $ IntOp i32) (BoolOp) (LocInfoE loc_135 (Call (LocInfoE loc_137 (global___list_del_entry_valid)) [@{expr} LocInfoE loc_138 (use{PtrOp} (LocInfoE loc_139 ("entry"))) ])))))
        then
        locinfo: loc_130 ;
          Goto "#2"
        else
        locinfo: loc_119 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_119 ;
        expr: (LocInfoE loc_119 (Call (LocInfoE loc_121 (global___list_del)) [@{expr} LocInfoE loc_122 (use{PtrOp} (LocInfoE loc_123 ((LocInfoE loc_124 (!{PtrOp} (LocInfoE loc_125 ("entry")))) at{struct_list_head} "prev"))) ;
        LocInfoE loc_126 (use{PtrOp} (LocInfoE loc_127 ((LocInfoE loc_128 (!{PtrOp} (LocInfoE loc_129 ("entry")))) at{struct_list_head} "next"))) ])) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_130 ;
        Return (VOID)
      ]> $
      <[ "#3" :=
        locinfo: loc_119 ;
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
        locinfo: loc_142 ;
        expr: (LocInfoE loc_142 (Call (LocInfoE loc_149 (global___list_del_entry)) [@{expr} LocInfoE loc_150 (use{PtrOp} (LocInfoE loc_151 ("entry"))) ])) ;
        locinfo: loc_143 ;
        expr: (LocInfoE loc_143 (Call (LocInfoE loc_145 (global_INIT_LIST_HEAD)) [@{expr} LocInfoE loc_146 (use{PtrOp} (LocInfoE loc_147 ("entry"))) ])) ;
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
        locinfo: loc_154 ;
        Return (LocInfoE loc_155 ((LocInfoE loc_156 (use{PtrOp} (LocInfoE loc_157 ((LocInfoE loc_158 (!{PtrOp} (LocInfoE loc_159 ("head")))) at{struct_list_head} "next")))) ={PtrOp, PtrOp, i32} (LocInfoE loc_160 (use{PtrOp} (LocInfoE loc_161 ("head"))))))
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
        locinfo: loc_164 ;
        Return (LocInfoE loc_165 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_166 ((LocInfoE loc_167 (UnOp (CastOp $ IntOp u64) (IntOp u64) (LocInfoE loc_168 (use{IntOp u64} (LocInfoE loc_169 ("phys")))))) -{IntOp u64, IntOp u64} (LocInfoE loc_170 (UnOp (CastOp $ IntOp u64) (IntOp i64) (LocInfoE loc_170 (use{IntOp i64} (LocInfoE loc_171 (global_hyp_physvirt_offset))))))))))
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
        locinfo: loc_174 ;
        Return (LocInfoE loc_175 ((LocInfoE loc_176 (UnOp (CastOp $ IntOp u64) (PtrOp) (LocInfoE loc_177 (use{PtrOp} (LocInfoE loc_178 ("addr")))))) +{IntOp u64, IntOp u64} (LocInfoE loc_179 (UnOp (CastOp $ IntOp u64) (IntOp i64) (LocInfoE loc_179 (use{IntOp i64} (LocInfoE loc_180 (global_hyp_physvirt_offset))))))))
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
        locinfo: loc_183 ;
        Return (LocInfoE loc_184 ((LocInfoE loc_185 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_186 (use{PtrOp} (LocInfoE loc_187 (global___hyp_vmemmap)))))) at_offset{layout_of struct_hyp_page, PtrOp, IntOp u64} (LocInfoE loc_188 ((LocInfoE loc_189 (use{IntOp u64} (LocInfoE loc_190 ("phys")))) >>{IntOp u64, IntOp u64} (LocInfoE loc_191 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_191 (i2v 12 i32))))))))
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
        locinfo: loc_194 ;
        Return (LocInfoE loc_195 ((LocInfoE loc_196 (UnOp (CastOp $ IntOp u64) (IntOp ptrdiff_t) (LocInfoE loc_197 ((LocInfoE loc_198 (use{PtrOp} (LocInfoE loc_199 ("page")))) sub_ptr{layout_of struct_hyp_page, PtrOp, PtrOp} (LocInfoE loc_200 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_201 (use{PtrOp} (LocInfoE loc_202 (global___hyp_vmemmap)))))))))) <<{IntOp u64, IntOp u64} (LocInfoE loc_203 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_203 (i2v 12 i32))))))
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
        "p" <-{ PtrOp }
          LocInfoE loc_212 (Call (LocInfoE loc_214 (global_hyp_phys_to_page)) [@{expr} LocInfoE loc_215 ((LocInfoE loc_216 (UnOp (CastOp $ IntOp u64) (PtrOp) (LocInfoE loc_217 (use{PtrOp} (LocInfoE loc_218 ("addr")))))) +{IntOp u64, IntOp u64} (LocInfoE loc_219 (UnOp (CastOp $ IntOp u64) (IntOp i64) (LocInfoE loc_219 (use{IntOp i64} (LocInfoE loc_220 (global_hyp_physvirt_offset))))))) ]) ;
        locinfo: loc_207 ;
        Return (LocInfoE loc_208 (UnOp (CastOp $ IntOp i32) (IntOp u32) (LocInfoE loc_208 (use{IntOp u32} (LocInfoE loc_209 ((LocInfoE loc_210 (!{PtrOp} (LocInfoE loc_211 ("p")))) at{struct_hyp_page} "refcount"))))))
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
        locinfo: loc_226 ;
        expr: (LocInfoE loc_226 (Call (LocInfoE loc_261 (global_sl_lock)) [@{expr} LocInfoE loc_262 (&(LocInfoE loc_263 ((LocInfoE loc_264 (!{PtrOp} (LocInfoE loc_265 ("pool")))) at{struct_hyp_pool} "lock"))) ])) ;
        locinfo: loc_227 ;
        LocInfoE loc_250 ("p") <-{ PtrOp }
          LocInfoE loc_251 (Call (LocInfoE loc_253 (global___hyp_alloc_pages)) [@{expr} LocInfoE loc_254 (use{PtrOp} (LocInfoE loc_255 ("pool"))) ;
          LocInfoE loc_256 (use{IntOp u64} (LocInfoE loc_257 ("mask"))) ;
          LocInfoE loc_258 (use{IntOp u32} (LocInfoE loc_259 ("order"))) ]) ;
        locinfo: loc_228 ;
        expr: (LocInfoE loc_228 (Call (LocInfoE loc_245 (global_sl_unlock)) [@{expr} LocInfoE loc_246 (AnnotExpr 1%nat LockA (LocInfoE loc_246 (&(LocInfoE loc_247 ((LocInfoE loc_248 (!{PtrOp} (LocInfoE loc_249 ("pool")))) at{struct_hyp_pool} "lock"))))) ])) ;
        locinfo: loc_229 ;
        Return (LocInfoE loc_230 (IfE (PtrOp)
               (LocInfoE loc_231 (use{PtrOp} (LocInfoE loc_232 ("p"))))
               (LocInfoE loc_233 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_234 ((LocInfoE loc_235 (UnOp (CastOp $ IntOp u64) (IntOp u64) (LocInfoE loc_236 (Call (LocInfoE loc_238 (global_hyp_page_to_phys)) [@{expr} LocInfoE loc_239 (use{PtrOp} (LocInfoE loc_240 ("p"))) ])))) -{IntOp u64, IntOp u64} (LocInfoE loc_241 (UnOp (CastOp $ IntOp u64) (IntOp i64) (LocInfoE loc_241 (use{IntOp i64} (LocInfoE loc_242 (global_hyp_physvirt_offset))))))))))
               (LocInfoE loc_243 (NULL))))
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
        "p" <-{ PtrOp }
          LocInfoE loc_295 (Call (LocInfoE loc_297 (global_hyp_phys_to_page)) [@{expr} LocInfoE loc_298 ((LocInfoE loc_299 (UnOp (CastOp $ IntOp u64) (PtrOp) (LocInfoE loc_300 (use{PtrOp} (LocInfoE loc_301 ("addr")))))) +{IntOp u64, IntOp u64} (LocInfoE loc_302 (UnOp (CastOp $ IntOp u64) (IntOp i64) (LocInfoE loc_302 (use{IntOp i64} (LocInfoE loc_303 (global_hyp_physvirt_offset))))))) ]) ;
        "pool" <-{ PtrOp }
          LocInfoE loc_288 (use{PtrOp} (LocInfoE loc_289 ((LocInfoE loc_290 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_291 (!{PtrOp} (LocInfoE loc_292 ("p")))))) at{struct_hyp_page} "pool"))) ;
        locinfo: loc_270 ;
        expr: (LocInfoE loc_270 (Call (LocInfoE loc_283 (global_sl_lock)) [@{expr} LocInfoE loc_284 (&(LocInfoE loc_285 ((LocInfoE loc_286 (!{PtrOp} (LocInfoE loc_287 ("pool")))) at{struct_hyp_pool} "lock"))) ])) ;
        locinfo: loc_271 ;
        LocInfoE loc_279 ((LocInfoE loc_280 (!{PtrOp} (LocInfoE loc_281 ("p")))) at{struct_hyp_page} "refcount") <-{ IntOp u32 }
          LocInfoE loc_271 ((LocInfoE loc_271 (use{IntOp u32} (LocInfoE loc_279 ((LocInfoE loc_280 (!{PtrOp} (LocInfoE loc_281 ("p")))) at{struct_hyp_page} "refcount")))) +{IntOp u32, IntOp u32} (LocInfoE loc_271 (i2v 1 u32))) ;
        locinfo: loc_272 ;
        expr: (LocInfoE loc_272 (Call (LocInfoE loc_274 (global_sl_unlock)) [@{expr} LocInfoE loc_275 (AnnotExpr 1%nat LockA (LocInfoE loc_275 (&(LocInfoE loc_276 ((LocInfoE loc_277 (!{PtrOp} (LocInfoE loc_278 ("pool")))) at{struct_hyp_pool} "lock"))))) ])) ;
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
        "p" <-{ PtrOp }
          LocInfoE loc_361 (Call (LocInfoE loc_363 (global_hyp_phys_to_page)) [@{expr} LocInfoE loc_364 ((LocInfoE loc_365 (UnOp (CastOp $ IntOp u64) (PtrOp) (LocInfoE loc_366 (use{PtrOp} (LocInfoE loc_367 ("addr")))))) +{IntOp u64, IntOp u64} (LocInfoE loc_368 (UnOp (CastOp $ IntOp u64) (IntOp i64) (LocInfoE loc_368 (use{IntOp i64} (LocInfoE loc_369 (global_hyp_physvirt_offset))))))) ]) ;
        "pool" <-{ PtrOp }
          LocInfoE loc_354 (use{PtrOp} (LocInfoE loc_355 ((LocInfoE loc_356 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_357 (!{PtrOp} (LocInfoE loc_358 ("p")))))) at{struct_hyp_page} "pool"))) ;
        locinfo: loc_310 ;
        expr: (LocInfoE loc_310 (Call (LocInfoE loc_349 (global_sl_lock)) [@{expr} LocInfoE loc_350 (&(LocInfoE loc_351 ((LocInfoE loc_352 (!{PtrOp} (LocInfoE loc_353 ("pool")))) at{struct_hyp_pool} "lock"))) ])) ;
        locinfo: loc_342 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_342 ((UnOp (CastOp $ IntOp u32) (IntOp i32) (i2v 0 i32)) ={IntOp u32, IntOp u32, i32} (LocInfoE loc_344 (use{IntOp u32} (LocInfoE loc_345 ((LocInfoE loc_346 (!{PtrOp} (LocInfoE loc_347 ("p")))) at{struct_hyp_page} "refcount")))))
        then
        locinfo: loc_338 ;
          Goto "#5"
        else
        locinfo: loc_312 ;
          Goto "#6"
      ]> $
      <[ "#1" :=
        locinfo: loc_312 ;
        LocInfoE loc_335 ((LocInfoE loc_336 (!{PtrOp} (LocInfoE loc_337 ("p")))) at{struct_hyp_page} "refcount") <-{ IntOp u32 }
          LocInfoE loc_312 ((LocInfoE loc_312 (use{IntOp u32} (LocInfoE loc_335 ((LocInfoE loc_336 (!{PtrOp} (LocInfoE loc_337 ("p")))) at{struct_hyp_page} "refcount")))) -{IntOp u32, IntOp u32} (LocInfoE loc_312 (i2v 1 u32))) ;
        locinfo: loc_329 ;
        if{IntOp i32, Some "#2"}: LocInfoE loc_329 ((UnOp (CastOp $ IntOp u32) (IntOp i32) (i2v 0 i32)) ={IntOp u32, IntOp u32, i32} (LocInfoE loc_331 (use{IntOp u32} (LocInfoE loc_332 ((LocInfoE loc_333 (!{PtrOp} (LocInfoE loc_334 ("p")))) at{struct_hyp_page} "refcount")))))
        then
        locinfo: loc_321 ;
          Goto "#3"
        else
        locinfo: loc_314 ;
          Goto "#4"
      ]> $
      <[ "#2" :=
        locinfo: loc_314 ;
        expr: (LocInfoE loc_314 (Call (LocInfoE loc_316 (global_sl_unlock)) [@{expr} LocInfoE loc_317 (AnnotExpr 1%nat LockA (LocInfoE loc_317 (&(LocInfoE loc_318 ((LocInfoE loc_319 (!{PtrOp} (LocInfoE loc_320 ("pool")))) at{struct_hyp_pool} "lock"))))) ])) ;
        Return (VOID)
      ]> $
      <[ "#3" :=
        locinfo: loc_321 ;
        expr: (LocInfoE loc_321 (Call (LocInfoE loc_323 (global___hyp_attach_page)) [@{expr} LocInfoE loc_324 (use{PtrOp} (LocInfoE loc_325 ("pool"))) ;
        LocInfoE loc_326 (use{PtrOp} (LocInfoE loc_327 ("p"))) ])) ;
        locinfo: loc_314 ;
        Goto "#2"
      ]> $
      <[ "#4" :=
        locinfo: loc_314 ;
        Goto "#2"
      ]> $
      <[ "#5" :=
        locinfo: loc_338 ;
        expr: (LocInfoE loc_338 (Call (LocInfoE loc_340 (global_hyp_panic)) [@{expr}  ])) ;
        locinfo: loc_312 ;
        Goto "#1"
      ]> $
      <[ "#6" :=
        locinfo: loc_312 ;
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
        locinfo: loc_511 ;
        if{IntOp u64, Some "#1"}: LocInfoE loc_511 ((LocInfoE loc_512 (use{IntOp u64} (LocInfoE loc_513 ("phys")))) %{IntOp u64, IntOp u64} (LocInfoE loc_514 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_514 (i2v 4096 i32)))))
        then
        locinfo: loc_507 ;
          Goto "#11"
        else
        locinfo: loc_377 ;
          Goto "#12"
      ]> $
      <[ "#1" :=
        locinfo: loc_377 ;
        expr: (LocInfoE loc_377 (Call (LocInfoE loc_502 (global_sl_init)) [@{expr} LocInfoE loc_503 (&(LocInfoE loc_504 ((LocInfoE loc_505 (!{PtrOp} (LocInfoE loc_506 ("pool")))) at{struct_hyp_pool} "lock"))) ])) ;
        locinfo: loc_378 ;
        LocInfoE loc_499 ("i") <-{ IntOp i32 } LocInfoE loc_500 (i2v 0 i32) ;
        locinfo: loc_379 ;
        Goto "#2"
      ]> $
      <[ "#10" :=
        locinfo: loc_389 ;
        Return (LocInfoE loc_390 (i2v 0 i32))
      ]> $
      <[ "#11" :=
        locinfo: loc_507 ;
        Return (LocInfoE loc_508 (UnOp NegOp (IntOp i32) (LocInfoE loc_509 (i2v 22 i32))))
      ]> $
      <[ "#12" :=
        locinfo: loc_377 ;
        Goto "#1"
      ]> $
      <[ "#2" :=
        locinfo: loc_495 ;
        if{IntOp i32, None}: LocInfoE loc_495 ((LocInfoE loc_496 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_496 (use{IntOp i32} (LocInfoE loc_497 ("i")))))) ≤{IntOp u32, IntOp u32, i32} (LocInfoE loc_498 (i2v 11 u32)))
        then
        locinfo: loc_480 ;
          Goto "#3"
        else
        locinfo: loc_380 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_480 ;
        expr: (LocInfoE loc_480 (Call (LocInfoE loc_485 (global_INIT_LIST_HEAD)) [@{expr} LocInfoE loc_486 (&(LocInfoE loc_488 ((LocInfoE loc_490 ((LocInfoE loc_491 (!{PtrOp} (LocInfoE loc_492 ("pool")))) at{struct_hyp_pool} "free_area")) at_offset{layout_of struct_list_head, PtrOp, IntOp i32} (LocInfoE loc_493 (use{IntOp i32} (LocInfoE loc_494 ("i"))))))) ])) ;
        locinfo: loc_481 ;
        Goto "__cerb_continue4"
      ]> $
      <[ "#4" :=
        locinfo: loc_380 ;
        LocInfoE loc_474 ((LocInfoE loc_475 (!{PtrOp} (LocInfoE loc_476 ("pool")))) at{struct_hyp_pool} "range_start") <-{ IntOp u64 }
          LocInfoE loc_477 (use{IntOp u64} (LocInfoE loc_478 ("phys"))) ;
        locinfo: loc_381 ;
        LocInfoE loc_464 ((LocInfoE loc_465 (!{PtrOp} (LocInfoE loc_466 ("pool")))) at{struct_hyp_pool} "range_end") <-{ IntOp u64 }
          LocInfoE loc_467 ((LocInfoE loc_468 (use{IntOp u64} (LocInfoE loc_469 ("phys")))) +{IntOp u64, IntOp u64} (LocInfoE loc_470 (UnOp (CastOp $ IntOp u64) (IntOp u32) (LocInfoE loc_470 ((LocInfoE loc_471 (use{IntOp u32} (LocInfoE loc_472 ("nr_pages")))) <<{IntOp u32, IntOp u32} (LocInfoE loc_473 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_473 (i2v 12 i32))))))))) ;
        locinfo: loc_382 ;
        LocInfoE loc_458 ("p") <-{ PtrOp }
          LocInfoE loc_459 (Call (LocInfoE loc_461 (global_hyp_phys_to_page)) [@{expr} LocInfoE loc_462 (use{IntOp u64} (LocInfoE loc_463 ("phys"))) ]) ;
        locinfo: loc_383 ;
        expr: (LocInfoE loc_383 (Call (LocInfoE loc_450 (global_memset)) [@{expr} LocInfoE loc_451 (use{PtrOp} (LocInfoE loc_452 ("p"))) ;
        LocInfoE loc_453 (i2v 0 i32) ;
        LocInfoE loc_454 ((LocInfoE loc_455 (i2v (layout_of struct_hyp_page).(ly_size) size_t)) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_456 (UnOp (CastOp $ IntOp size_t) (IntOp u32) (LocInfoE loc_456 (use{IntOp u32} (LocInfoE loc_457 ("nr_pages"))))))) ])) ;
        locinfo: loc_384 ;
        LocInfoE loc_447 ("i") <-{ IntOp i32 } LocInfoE loc_448 (i2v 0 i32) ;
        locinfo: loc_385 ;
        Goto "#5"
      ]> $
      <[ "#5" :=
        locinfo: loc_442 ;
        if{IntOp i32, None}: LocInfoE loc_442 ((LocInfoE loc_443 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_443 (use{IntOp i32} (LocInfoE loc_444 ("i")))))) <{IntOp u32, IntOp u32, i32} (LocInfoE loc_445 (use{IntOp u32} (LocInfoE loc_446 ("nr_pages")))))
        then
        locinfo: loc_424 ;
          Goto "#6"
        else
        locinfo: loc_386 ;
          Goto "#7"
      ]> $
      <[ "#6" :=
        locinfo: loc_424 ;
        LocInfoE loc_437 ((LocInfoE loc_438 (!{PtrOp} (LocInfoE loc_439 ("p")))) at{struct_hyp_page} "pool") <-{ PtrOp }
          LocInfoE loc_440 (use{PtrOp} (LocInfoE loc_441 ("pool"))) ;
        locinfo: loc_425 ;
        expr: (LocInfoE loc_425 (Call (LocInfoE loc_432 (global_INIT_LIST_HEAD)) [@{expr} LocInfoE loc_433 (&(LocInfoE loc_434 ((LocInfoE loc_435 (!{PtrOp} (LocInfoE loc_436 ("p")))) at{struct_hyp_page} "node"))) ])) ;
        locinfo: loc_426 ;
        LocInfoE loc_430 ("p") <-{ PtrOp }
          LocInfoE loc_426 ((LocInfoE loc_426 (use{PtrOp} (LocInfoE loc_430 ("p")))) at_offset{layout_of struct_hyp_page, PtrOp, IntOp i32} (LocInfoE loc_426 (i2v 1 i32))) ;
        locinfo: loc_427 ;
        Goto "__cerb_continue5"
      ]> $
      <[ "#7" :=
        locinfo: loc_386 ;
        LocInfoE loc_412 ("p") <-{ PtrOp }
          LocInfoE loc_413 (Call (LocInfoE loc_415 (global_hyp_phys_to_page)) [@{expr} LocInfoE loc_416 ((LocInfoE loc_417 (use{IntOp u64} (LocInfoE loc_418 ("phys")))) +{IntOp u64, IntOp u64} (LocInfoE loc_419 (UnOp (CastOp $ IntOp u64) (IntOp u32) (LocInfoE loc_419 ((LocInfoE loc_420 (use{IntOp u32} (LocInfoE loc_421 ("used_pages")))) <<{IntOp u32, IntOp u32} (LocInfoE loc_422 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_422 (i2v 12 i32))))))))) ]) ;
        locinfo: loc_387 ;
        LocInfoE loc_409 ("i") <-{ IntOp i32 }
          LocInfoE loc_410 (UnOp (CastOp $ IntOp i32) (IntOp u32) (LocInfoE loc_410 (use{IntOp u32} (LocInfoE loc_411 ("used_pages"))))) ;
        locinfo: loc_388 ;
        Goto "#8"
      ]> $
      <[ "#8" :=
        locinfo: loc_404 ;
        if{IntOp i32, None}: LocInfoE loc_404 ((LocInfoE loc_405 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_405 (use{IntOp i32} (LocInfoE loc_406 ("i")))))) <{IntOp u32, IntOp u32, i32} (LocInfoE loc_407 (use{IntOp u32} (LocInfoE loc_408 ("nr_pages")))))
        then
        locinfo: loc_392 ;
          Goto "#9"
        else
        locinfo: loc_389 ;
          Goto "#10"
      ]> $
      <[ "#9" :=
        locinfo: loc_392 ;
        expr: (LocInfoE loc_392 (Call (LocInfoE loc_399 (global___hyp_attach_page)) [@{expr} LocInfoE loc_400 (use{PtrOp} (LocInfoE loc_401 ("pool"))) ;
        LocInfoE loc_402 (use{PtrOp} (LocInfoE loc_403 ("p"))) ])) ;
        locinfo: loc_393 ;
        LocInfoE loc_397 ("p") <-{ PtrOp }
          LocInfoE loc_393 ((LocInfoE loc_393 (use{PtrOp} (LocInfoE loc_397 ("p")))) at_offset{layout_of struct_hyp_page, PtrOp, IntOp i32} (LocInfoE loc_393 (i2v 1 i32))) ;
        locinfo: loc_394 ;
        Goto "__cerb_continue6"
      ]> $
      <[ "__cerb_continue4" :=
        locinfo: loc_482 ;
        LocInfoE loc_483 ("i") <-{ IntOp i32 }
          LocInfoE loc_482 ((LocInfoE loc_482 (use{IntOp i32} (LocInfoE loc_483 ("i")))) +{IntOp i32, IntOp i32} (LocInfoE loc_482 (i2v 1 i32))) ;
        locinfo: loc_379 ;
        Goto "#2"
      ]> $
      <[ "__cerb_continue5" :=
        locinfo: loc_428 ;
        LocInfoE loc_429 ("i") <-{ IntOp i32 }
          LocInfoE loc_428 ((LocInfoE loc_428 (use{IntOp i32} (LocInfoE loc_429 ("i")))) +{IntOp i32, IntOp i32} (LocInfoE loc_428 (i2v 1 i32))) ;
        locinfo: loc_385 ;
        Goto "#5"
      ]> $
      <[ "__cerb_continue6" :=
        locinfo: loc_395 ;
        LocInfoE loc_396 ("i") <-{ IntOp i32 }
          LocInfoE loc_395 ((LocInfoE loc_395 (use{IntOp i32} (LocInfoE loc_396 ("i")))) +{IntOp i32, IntOp i32} (LocInfoE loc_395 (i2v 1 i32))) ;
        locinfo: loc_388 ;
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
        locinfo: loc_517 ;
        expr: (LocInfoE loc_561 (&(LocInfoE loc_562 ((LocInfoE loc_563 (!{PtrOp} (LocInfoE loc_564 ("pool")))) at{struct_hyp_pool} "lock")))) ;
        "addr" <-{ IntOp u64 }
          LocInfoE loc_554 (Call (LocInfoE loc_556 (global_hyp_page_to_phys)) [@{expr} LocInfoE loc_557 (use{PtrOp} (LocInfoE loc_558 ("p"))) ]) ;
        locinfo: loc_520 ;
        LocInfoE loc_546 ("addr") <-{ IntOp u64 }
          LocInfoE loc_547 ((LocInfoE loc_548 (use{IntOp u64} (LocInfoE loc_549 ("addr")))) ^{IntOp u64, IntOp u64} (LocInfoE loc_550 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_550 ((LocInfoE loc_551 (i2v 4096 i32)) <<{IntOp i32, IntOp i32} (LocInfoE loc_552 (UnOp (CastOp $ IntOp i32) (IntOp u32) (LocInfoE loc_552 (use{IntOp u32} (LocInfoE loc_553 ("order"))))))))))) ;
        locinfo: loc_531 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_531 ((LocInfoE loc_532 ((LocInfoE loc_533 (use{IntOp u64} (LocInfoE loc_534 ("addr")))) <{IntOp u64, IntOp u64, i32} (LocInfoE loc_535 (use{IntOp u64} (LocInfoE loc_536 ((LocInfoE loc_537 (!{PtrOp} (LocInfoE loc_538 ("pool")))) at{struct_hyp_pool} "range_start")))))) ||{IntOp i32, IntOp i32, i32} (LocInfoE loc_539 ((LocInfoE loc_540 (use{IntOp u64} (LocInfoE loc_541 ("addr")))) ≥{IntOp u64, IntOp u64, i32} (LocInfoE loc_542 (use{IntOp u64} (LocInfoE loc_543 ((LocInfoE loc_544 (!{PtrOp} (LocInfoE loc_545 ("pool")))) at{struct_hyp_pool} "range_end")))))))
        then
        locinfo: loc_528 ;
          Goto "#2"
        else
        locinfo: loc_522 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_522 ;
        Return (LocInfoE loc_523 (Call (LocInfoE loc_525 (global_hyp_phys_to_page)) [@{expr} LocInfoE loc_526 (use{IntOp u64} (LocInfoE loc_527 ("addr"))) ]))
      ]> $
      <[ "#2" :=
        locinfo: loc_528 ;
        Return (LocInfoE loc_529 (NULL))
      ]> $
      <[ "#3" :=
        locinfo: loc_522 ;
        Goto "#1"
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
        locinfo: loc_567 ;
        expr: (LocInfoE loc_687 (&(LocInfoE loc_688 ((LocInfoE loc_689 (!{PtrOp} (LocInfoE loc_690 ("pool")))) at{struct_hyp_pool} "lock")))) ;
        "order" <-{ IntOp u32 }
          LocInfoE loc_681 (use{IntOp u32} (LocInfoE loc_682 ((LocInfoE loc_683 (!{PtrOp} (LocInfoE loc_684 ("p")))) at{struct_hyp_page} "order"))) ;
        locinfo: loc_571 ;
        LocInfoE loc_677 ((LocInfoE loc_678 (!{PtrOp} (LocInfoE loc_679 ("p")))) at{struct_hyp_page} "order") <-{ IntOp u32 }
          LocInfoE loc_680 (i2v (max_int u32) u32) ;
        locinfo: loc_572 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_673 ;
        if{IntOp i32, None}: LocInfoE loc_673 ((LocInfoE loc_674 (use{IntOp u32} (LocInfoE loc_675 ("order")))) <{IntOp u32, IntOp u32, i32} (LocInfoE loc_676 (i2v 11 u32)))
        then
        locinfo: loc_602 ;
          Goto "#2"
        else
        locinfo: loc_573 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_602 ;
        LocInfoE loc_663 ("buddy") <-{ PtrOp }
          LocInfoE loc_664 (Call (LocInfoE loc_666 (global___find_buddy)) [@{expr} LocInfoE loc_667 (use{PtrOp} (LocInfoE loc_668 ("pool"))) ;
          LocInfoE loc_669 (use{PtrOp} (LocInfoE loc_670 ("p"))) ;
          LocInfoE loc_671 (use{IntOp u32} (LocInfoE loc_672 ("order"))) ]) ;
        locinfo: loc_603 ;
        expr: (LocInfoE loc_659 (&(LocInfoE loc_660 ((LocInfoE loc_661 (!{PtrOp} (LocInfoE loc_662 ("pool")))) at{struct_hyp_pool} "lock")))) ;
        locinfo: loc_639 ;
        if{IntOp i32, Some "#4"}: LocInfoE loc_639 ((LocInfoE loc_640 ((LocInfoE loc_641 ((LocInfoE loc_642 (use{PtrOp} (LocInfoE loc_643 ("buddy")))) ={PtrOp, PtrOp, i32} (LocInfoE loc_644 (NULL)))) ||{IntOp i32, IntOp i32, i32} (LocInfoE loc_645 (Call (LocInfoE loc_647 (global_list_empty)) [@{expr} LocInfoE loc_648 (&(LocInfoE loc_649 ((LocInfoE loc_650 (!{PtrOp} (LocInfoE loc_651 ("buddy")))) at{struct_hyp_page} "node"))) ])))) ||{IntOp i32, IntOp i32, i32} (LocInfoE loc_652 ((LocInfoE loc_653 (use{IntOp u32} (LocInfoE loc_654 ((LocInfoE loc_655 (!{PtrOp} (LocInfoE loc_656 ("buddy")))) at{struct_hyp_page} "order")))) !={IntOp u32, IntOp u32, i32} (LocInfoE loc_657 (use{IntOp u32} (LocInfoE loc_658 ("order")))))))
        then
        locinfo: loc_573 ;
          Goto "#8"
        else
        locinfo: loc_606 ;
          Goto "#9"
      ]> $
      <[ "#3" :=
        locinfo: loc_573 ;
        expr: (LocInfoE loc_597 (&(LocInfoE loc_598 ((LocInfoE loc_599 (!{PtrOp} (LocInfoE loc_600 ("pool")))) at{struct_hyp_pool} "lock")))) ;
        locinfo: loc_575 ;
        LocInfoE loc_592 ((LocInfoE loc_593 (!{PtrOp} (LocInfoE loc_594 ("p")))) at{struct_hyp_page} "order") <-{ IntOp u32 }
          LocInfoE loc_595 (use{IntOp u32} (LocInfoE loc_596 ("order"))) ;
        locinfo: loc_576 ;
        expr: (LocInfoE loc_576 (Call (LocInfoE loc_578 (global_list_add)) [@{expr} LocInfoE loc_579 (&(LocInfoE loc_580 ((LocInfoE loc_581 (!{PtrOp} (LocInfoE loc_582 ("p")))) at{struct_hyp_page} "node"))) ;
        LocInfoE loc_583 (&(LocInfoE loc_585 ((LocInfoE loc_587 ((LocInfoE loc_588 (!{PtrOp} (LocInfoE loc_589 ("pool")))) at{struct_hyp_pool} "free_area")) at_offset{layout_of struct_list_head, PtrOp, IntOp u32} (LocInfoE loc_590 (use{IntOp u32} (LocInfoE loc_591 ("order"))))))) ])) ;
        Return (VOID)
      ]> $
      <[ "#4" :=
        locinfo: loc_606 ;
        expr: (LocInfoE loc_606 (Call (LocInfoE loc_632 (global_list_del_init)) [@{expr} LocInfoE loc_633 (&(LocInfoE loc_634 ((LocInfoE loc_635 (!{PtrOp} (LocInfoE loc_636 ("buddy")))) at{struct_hyp_page} "node"))) ])) ;
        locinfo: loc_607 ;
        LocInfoE loc_627 ((LocInfoE loc_628 (!{PtrOp} (LocInfoE loc_629 ("buddy")))) at{struct_hyp_page} "order") <-{ IntOp u32 }
          LocInfoE loc_630 (i2v (max_int u32) u32) ;
        locinfo: loc_622 ;
        if{IntOp i32, Some "#5"}: LocInfoE loc_622 ((LocInfoE loc_623 (use{PtrOp} (LocInfoE loc_624 ("p")))) <{PtrOp, PtrOp, i32} (LocInfoE loc_625 (use{PtrOp} (LocInfoE loc_626 ("buddy")))))
        then
        locinfo: loc_613 ;
          Goto "#6"
        else
        locinfo: loc_618 ;
          Goto "#7"
      ]> $
      <[ "#5" :=
        locinfo: loc_609 ;
        Goto "__cerb_continue0"
      ]> $
      <[ "#6" :=
        locinfo: loc_613 ;
        LocInfoE loc_614 ("p") <-{ PtrOp }
          LocInfoE loc_615 (use{PtrOp} (LocInfoE loc_616 ("p"))) ;
        locinfo: loc_609 ;
        Goto "#5"
      ]> $
      <[ "#7" :=
        locinfo: loc_618 ;
        LocInfoE loc_619 ("p") <-{ PtrOp }
          LocInfoE loc_620 (use{PtrOp} (LocInfoE loc_621 ("buddy"))) ;
        locinfo: loc_609 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        locinfo: loc_573 ;
        Goto "#3"
      ]> $
      <[ "#9" :=
        locinfo: loc_606 ;
        Goto "#4"
      ]> $
      <[ "__cerb_continue0" :=
        locinfo: loc_610 ;
        LocInfoE loc_611 ("order") <-{ IntOp u32 }
          LocInfoE loc_610 ((LocInfoE loc_610 (use{IntOp u32} (LocInfoE loc_611 ("order")))) +{IntOp u32, IntOp u32} (LocInfoE loc_610 (i2v 1 u32))) ;
        locinfo: loc_572 ;
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
        locinfo: loc_765 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_765 ((LocInfoE loc_766 ((LocInfoE loc_767 (use{IntOp u32} (LocInfoE loc_768 ((LocInfoE loc_769 (!{PtrOp} (LocInfoE loc_770 ("p")))) at{struct_hyp_page} "order")))) ={IntOp u32, IntOp u32, i32} (LocInfoE loc_771 (i2v (max_int u32) u32)))) ||{IntOp i32, IntOp i32, i32} (LocInfoE loc_772 ((LocInfoE loc_773 (use{IntOp u32} (LocInfoE loc_774 ((LocInfoE loc_775 (!{PtrOp} (LocInfoE loc_776 ("p")))) at{struct_hyp_page} "order")))) <{IntOp u32, IntOp u32, i32} (LocInfoE loc_777 (use{IntOp u32} (LocInfoE loc_778 ("order")))))))
        then
        locinfo: loc_762 ;
          Goto "#5"
        else
        locinfo: loc_695 ;
          Goto "#6"
      ]> $
      <[ "#1" :=
        locinfo: loc_695 ;
        expr: (LocInfoE loc_695 (Call (LocInfoE loc_757 (global_list_del_init)) [@{expr} LocInfoE loc_758 (&(LocInfoE loc_759 ((LocInfoE loc_760 (!{PtrOp} (LocInfoE loc_761 ("p")))) at{struct_hyp_page} "node"))) ])) ;
        locinfo: loc_696 ;
        Goto "#2"
      ]> $
      <[ "#2" :=
        locinfo: loc_749 ;
        if{IntOp i32, None}: LocInfoE loc_749 ((LocInfoE loc_750 (use{IntOp u32} (LocInfoE loc_751 ((LocInfoE loc_752 (!{PtrOp} (LocInfoE loc_753 ("p")))) at{struct_hyp_page} "order")))) >{IntOp u32, IntOp u32, i32} (LocInfoE loc_754 (use{IntOp u32} (LocInfoE loc_755 ("order")))))
        then
        locinfo: loc_706 ;
          Goto "#3"
        else
        locinfo: loc_697 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_706 ;
        LocInfoE loc_746 ((LocInfoE loc_747 (!{PtrOp} (LocInfoE loc_748 ("p")))) at{struct_hyp_page} "order") <-{ IntOp u32 }
          LocInfoE loc_706 ((LocInfoE loc_706 (use{IntOp u32} (LocInfoE loc_746 ((LocInfoE loc_747 (!{PtrOp} (LocInfoE loc_748 ("p")))) at{struct_hyp_page} "order")))) -{IntOp u32, IntOp u32} (LocInfoE loc_706 (i2v 1 u32))) ;
        locinfo: loc_707 ;
        LocInfoE loc_734 ("buddy") <-{ PtrOp }
          LocInfoE loc_735 (Call (LocInfoE loc_737 (global___find_buddy)) [@{expr} LocInfoE loc_738 (use{PtrOp} (LocInfoE loc_739 ("pool"))) ;
          LocInfoE loc_740 (use{PtrOp} (LocInfoE loc_741 ("p"))) ;
          LocInfoE loc_742 (use{IntOp u32} (LocInfoE loc_743 ((LocInfoE loc_744 (!{PtrOp} (LocInfoE loc_745 ("p")))) at{struct_hyp_page} "order"))) ]) ;
        locinfo: loc_708 ;
        LocInfoE loc_727 ((LocInfoE loc_728 (!{PtrOp} (LocInfoE loc_729 ("buddy")))) at{struct_hyp_page} "order") <-{ IntOp u32 }
          LocInfoE loc_730 (use{IntOp u32} (LocInfoE loc_731 ((LocInfoE loc_732 (!{PtrOp} (LocInfoE loc_733 ("p")))) at{struct_hyp_page} "order"))) ;
        locinfo: loc_709 ;
        expr: (LocInfoE loc_709 (Call (LocInfoE loc_711 (global_list_add_tail)) [@{expr} LocInfoE loc_712 (&(LocInfoE loc_713 ((LocInfoE loc_714 (!{PtrOp} (LocInfoE loc_715 ("buddy")))) at{struct_hyp_page} "node"))) ;
        LocInfoE loc_716 (&(LocInfoE loc_718 ((LocInfoE loc_720 ((LocInfoE loc_721 (!{PtrOp} (LocInfoE loc_722 ("pool")))) at{struct_hyp_pool} "free_area")) at_offset{layout_of struct_list_head, PtrOp, IntOp u32} (LocInfoE loc_723 (use{IntOp u32} (LocInfoE loc_724 ((LocInfoE loc_725 (!{PtrOp} (LocInfoE loc_726 ("buddy")))) at{struct_hyp_page} "order"))))))) ])) ;
        locinfo: loc_696 ;
        Goto "#2"
      ]> $
      <[ "#4" :=
        locinfo: loc_697 ;
        LocInfoE loc_701 ((LocInfoE loc_702 (!{PtrOp} (LocInfoE loc_703 ("p")))) at{struct_hyp_page} "refcount") <-{ IntOp u32 }
          LocInfoE loc_704 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_704 (i2v 1 i32))) ;
        locinfo: loc_698 ;
        Return (LocInfoE loc_699 (use{PtrOp} (LocInfoE loc_700 ("p"))))
      ]> $
      <[ "#5" :=
        locinfo: loc_762 ;
        Return (LocInfoE loc_763 (NULL))
      ]> $
      <[ "#6" :=
        locinfo: loc_695 ;
        Goto "#1"
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
        locinfo: loc_782 ;
        LocInfoE loc_816 ("i") <-{ IntOp u64 }
          LocInfoE loc_817 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_817 (i2v 0 i32))) ;
        locinfo: loc_783 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_807 ;
        if{IntOp i32, None}: LocInfoE loc_807 ((LocInfoE loc_808 (use{IntOp u64} (LocInfoE loc_809 ("i")))) <{IntOp u64, IntOp u64, i32} (LocInfoE loc_810 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_810 ((LocInfoE loc_811 (i2v 1 i32)) <<{IntOp i32, IntOp i32} (LocInfoE loc_812 (UnOp (CastOp $ IntOp i32) (IntOp u32) (LocInfoE loc_812 (use{IntOp u32} (LocInfoE loc_813 ((LocInfoE loc_814 (!{PtrOp} (LocInfoE loc_815 ("p")))) at{struct_hyp_page} "order")))))))))))
        then
        locinfo: loc_785 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_785 ;
        expr: (LocInfoE loc_785 (Call (LocInfoE loc_790 (global_clear_page)) [@{expr} LocInfoE loc_791 ((LocInfoE loc_792 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_793 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_794 ((LocInfoE loc_795 (UnOp (CastOp $ IntOp u64) (IntOp u64) (LocInfoE loc_796 (Call (LocInfoE loc_798 (global_hyp_page_to_phys)) [@{expr} LocInfoE loc_799 (use{PtrOp} (LocInfoE loc_800 ("p"))) ])))) -{IntOp u64, IntOp u64} (LocInfoE loc_801 (UnOp (CastOp $ IntOp u64) (IntOp i64) (LocInfoE loc_801 (use{IntOp i64} (LocInfoE loc_802 (global_hyp_physvirt_offset)))))))))))) at_offset{it_layout u8, PtrOp, IntOp u64} (LocInfoE loc_803 ((LocInfoE loc_804 (use{IntOp u64} (LocInfoE loc_805 ("i")))) <<{IntOp u64, IntOp u64} (LocInfoE loc_806 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_806 (i2v 12 i32))))))) ])) ;
        locinfo: loc_786 ;
        Goto "__cerb_continue2"
      ]> $
      <[ "#3" :=
        Return (VOID)
      ]> $
      <[ "__cerb_continue2" :=
        locinfo: loc_787 ;
        LocInfoE loc_788 ("i") <-{ IntOp u64 }
          LocInfoE loc_787 ((LocInfoE loc_787 (use{IntOp u64} (LocInfoE loc_788 ("i")))) +{IntOp u64, IntOp u64} (LocInfoE loc_787 (i2v 1 u64))) ;
        locinfo: loc_783 ;
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
        "i" <-{ IntOp u32 }
          LocInfoE loc_892 (use{IntOp u32} (LocInfoE loc_893 ("order"))) ;
        locinfo: loc_822 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_875 ;
        if{IntOp i32, None}: LocInfoE loc_875 ((LocInfoE loc_876 ((LocInfoE loc_877 (use{IntOp u32} (LocInfoE loc_878 ("i")))) ≤{IntOp u32, IntOp u32, i32} (LocInfoE loc_879 (i2v 11 u32)))) &&{IntOp i32, IntOp i32, i32} (LocInfoE loc_880 (Call (LocInfoE loc_882 (global_list_empty)) [@{expr} LocInfoE loc_883 (&(LocInfoE loc_885 ((LocInfoE loc_887 ((LocInfoE loc_888 (!{PtrOp} (LocInfoE loc_889 ("pool")))) at{struct_hyp_pool} "free_area")) at_offset{layout_of struct_list_head, PtrOp, IntOp u32} (LocInfoE loc_890 (use{IntOp u32} (LocInfoE loc_891 ("i"))))))) ])))
        then
        locinfo: loc_873 ;
          Goto "#2"
        else
        locinfo: loc_869 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_873 ;
        LocInfoE loc_874 ("i") <-{ IntOp u32 }
          LocInfoE loc_873 ((LocInfoE loc_873 (use{IntOp u32} (LocInfoE loc_874 ("i")))) +{IntOp u32, IntOp u32} (LocInfoE loc_873 (i2v 1 u32))) ;
        locinfo: loc_822 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_869 ;
        if{IntOp i32, Some "#4"}: LocInfoE loc_869 ((LocInfoE loc_870 (use{IntOp u32} (LocInfoE loc_871 ("i")))) >{IntOp u32, IntOp u32, i32} (LocInfoE loc_872 (i2v 11 u32)))
        then
        locinfo: loc_866 ;
          Goto "#8"
        else
        locinfo: loc_824 ;
          Goto "#9"
      ]> $
      <[ "#4" :=
        locinfo: loc_824 ;
        LocInfoE loc_850 ("p") <-{ PtrOp }
          LocInfoE loc_851 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_852 ((LocInfoE loc_853 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_854 (use{PtrOp} (LocInfoE loc_855 ((LocInfoE loc_856 (&(LocInfoE loc_858 ((LocInfoE loc_860 ((LocInfoE loc_861 (!{PtrOp} (LocInfoE loc_862 ("pool")))) at{struct_hyp_pool} "free_area")) at_offset{layout_of struct_list_head, PtrOp, IntOp u32} (LocInfoE loc_863 (use{IntOp u32} (LocInfoE loc_864 ("i")))))))) at{struct_list_head} "next")))))) at_neg_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_865 ((OffsetOf (struct_hyp_page) ("node"))))))) ;
        locinfo: loc_825 ;
        LocInfoE loc_840 ("p") <-{ PtrOp }
          LocInfoE loc_841 (Call (LocInfoE loc_843 (global___hyp_extract_page)) [@{expr} LocInfoE loc_844 (use{PtrOp} (LocInfoE loc_845 ("pool"))) ;
          LocInfoE loc_846 (use{PtrOp} (LocInfoE loc_847 ("p"))) ;
          LocInfoE loc_848 (use{IntOp u32} (LocInfoE loc_849 ("order"))) ]) ;
        locinfo: loc_836 ;
        if{IntOp u64, Some "#5"}: LocInfoE loc_836 ((LocInfoE loc_837 (use{IntOp u64} (LocInfoE loc_838 ("mask")))) &{IntOp u64, IntOp u64} (LocInfoE loc_839 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_839 (i2v 1 i32)))))
        then
        locinfo: loc_830 ;
          Goto "#6"
        else
        locinfo: loc_827 ;
          Goto "#7"
      ]> $
      <[ "#5" :=
        locinfo: loc_827 ;
        Return (LocInfoE loc_828 (use{PtrOp} (LocInfoE loc_829 ("p"))))
      ]> $
      <[ "#6" :=
        locinfo: loc_830 ;
        expr: (LocInfoE loc_830 (Call (LocInfoE loc_832 (global_clear_hyp_page)) [@{expr} LocInfoE loc_833 (use{PtrOp} (LocInfoE loc_834 ("p"))) ])) ;
        locinfo: loc_827 ;
        Goto "#5"
      ]> $
      <[ "#7" :=
        locinfo: loc_827 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        locinfo: loc_866 ;
        Return (LocInfoE loc_867 (NULL))
      ]> $
      <[ "#9" :=
        locinfo: loc_824 ;
        Goto "#4"
      ]> $∅
    )%E
  |}.
End code.
