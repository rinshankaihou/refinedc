From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [linux/page_alloc.c]. *)
Section code.
  Definition file_0 : string := "linux/page_alloc.c".
  Definition loc_2 : location_info := LocationInfo file_0 32 1 32 11.
  Definition loc_3 : location_info := LocationInfo file_0 32 8 32 9.
  Definition loc_6 : location_info := LocationInfo file_0 63 1 63 10.
  Definition loc_7 : location_info := LocationInfo file_0 63 8 63 9.
  Definition loc_10 : location_info := LocationInfo file_0 67 1 67 10.
  Definition loc_11 : location_info := LocationInfo file_0 67 8 67 9.
  Definition loc_14 : location_info := LocationInfo file_0 79 1 79 25.
  Definition loc_15 : location_info := LocationInfo file_0 80 1 80 19.
  Definition loc_16 : location_info := LocationInfo file_0 80 1 80 11.
  Definition loc_17 : location_info := LocationInfo file_0 80 1 80 5.
  Definition loc_18 : location_info := LocationInfo file_0 80 1 80 5.
  Definition loc_19 : location_info := LocationInfo file_0 80 14 80 18.
  Definition loc_20 : location_info := LocationInfo file_0 80 14 80 18.
  Definition loc_21 : location_info := LocationInfo file_0 79 2 79 14.
  Definition loc_22 : location_info := LocationInfo file_0 79 3 79 7.
  Definition loc_23 : location_info := LocationInfo file_0 79 3 79 7.
  Definition loc_24 : location_info := LocationInfo file_0 79 17 79 23.
  Definition loc_25 : location_info := LocationInfo file_0 79 17 79 23.
  Definition loc_28 : location_info := LocationInfo file_0 93 1 94 9.
  Definition loc_29 : location_info := LocationInfo file_0 96 1 96 18.
  Definition loc_30 : location_info := LocationInfo file_0 97 1 97 18.
  Definition loc_31 : location_info := LocationInfo file_0 98 1 98 18.
  Definition loc_32 : location_info := LocationInfo file_0 99 1 99 24.
  Definition loc_33 : location_info := LocationInfo file_0 99 2 99 14.
  Definition loc_34 : location_info := LocationInfo file_0 99 3 99 7.
  Definition loc_35 : location_info := LocationInfo file_0 99 3 99 7.
  Definition loc_36 : location_info := LocationInfo file_0 99 17 99 22.
  Definition loc_37 : location_info := LocationInfo file_0 99 17 99 22.
  Definition loc_38 : location_info := LocationInfo file_0 98 1 98 10.
  Definition loc_39 : location_info := LocationInfo file_0 98 1 98 4.
  Definition loc_40 : location_info := LocationInfo file_0 98 1 98 4.
  Definition loc_41 : location_info := LocationInfo file_0 98 13 98 17.
  Definition loc_42 : location_info := LocationInfo file_0 98 13 98 17.
  Definition loc_43 : location_info := LocationInfo file_0 97 1 97 10.
  Definition loc_44 : location_info := LocationInfo file_0 97 1 97 4.
  Definition loc_45 : location_info := LocationInfo file_0 97 1 97 4.
  Definition loc_46 : location_info := LocationInfo file_0 97 13 97 17.
  Definition loc_47 : location_info := LocationInfo file_0 97 13 97 17.
  Definition loc_48 : location_info := LocationInfo file_0 96 1 96 11.
  Definition loc_49 : location_info := LocationInfo file_0 96 1 96 5.
  Definition loc_50 : location_info := LocationInfo file_0 96 1 96 5.
  Definition loc_51 : location_info := LocationInfo file_0 96 14 96 17.
  Definition loc_52 : location_info := LocationInfo file_0 96 14 96 17.
  Definition loc_53 : location_info := LocationInfo file_0 94 2 94 9.
  Definition loc_56 : location_info := LocationInfo file_0 93 5 93 39.
  Definition loc_58 : location_info := LocationInfo file_0 93 6 93 39.
  Definition loc_59 : location_info := LocationInfo file_0 93 6 93 22.
  Definition loc_60 : location_info := LocationInfo file_0 93 6 93 22.
  Definition loc_61 : location_info := LocationInfo file_0 93 23 93 26.
  Definition loc_62 : location_info := LocationInfo file_0 93 23 93 26.
  Definition loc_63 : location_info := LocationInfo file_0 93 28 93 32.
  Definition loc_64 : location_info := LocationInfo file_0 93 28 93 32.
  Definition loc_65 : location_info := LocationInfo file_0 93 34 93 38.
  Definition loc_66 : location_info := LocationInfo file_0 93 34 93 38.
  Definition loc_69 : location_info := LocationInfo file_0 112 1 112 35.
  Definition loc_70 : location_info := LocationInfo file_0 112 1 112 11.
  Definition loc_71 : location_info := LocationInfo file_0 112 1 112 11.
  Definition loc_72 : location_info := LocationInfo file_0 112 12 112 15.
  Definition loc_73 : location_info := LocationInfo file_0 112 12 112 15.
  Definition loc_74 : location_info := LocationInfo file_0 112 17 112 21.
  Definition loc_75 : location_info := LocationInfo file_0 112 17 112 21.
  Definition loc_76 : location_info := LocationInfo file_0 112 23 112 33.
  Definition loc_77 : location_info := LocationInfo file_0 112 23 112 33.
  Definition loc_78 : location_info := LocationInfo file_0 112 23 112 27.
  Definition loc_79 : location_info := LocationInfo file_0 112 23 112 27.
  Definition loc_82 : location_info := LocationInfo file_0 126 1 126 35.
  Definition loc_83 : location_info := LocationInfo file_0 126 1 126 11.
  Definition loc_84 : location_info := LocationInfo file_0 126 1 126 11.
  Definition loc_85 : location_info := LocationInfo file_0 126 12 126 15.
  Definition loc_86 : location_info := LocationInfo file_0 126 12 126 15.
  Definition loc_87 : location_info := LocationInfo file_0 126 17 126 27.
  Definition loc_88 : location_info := LocationInfo file_0 126 17 126 27.
  Definition loc_89 : location_info := LocationInfo file_0 126 17 126 21.
  Definition loc_90 : location_info := LocationInfo file_0 126 17 126 21.
  Definition loc_91 : location_info := LocationInfo file_0 126 29 126 33.
  Definition loc_92 : location_info := LocationInfo file_0 126 29 126 33.
  Definition loc_95 : location_info := LocationInfo file_0 138 1 138 19.
  Definition loc_96 : location_info := LocationInfo file_0 139 1 139 25.
  Definition loc_97 : location_info := LocationInfo file_0 139 2 139 14.
  Definition loc_98 : location_info := LocationInfo file_0 139 3 139 7.
  Definition loc_99 : location_info := LocationInfo file_0 139 3 139 7.
  Definition loc_100 : location_info := LocationInfo file_0 139 17 139 23.
  Definition loc_101 : location_info := LocationInfo file_0 139 17 139 23.
  Definition loc_102 : location_info := LocationInfo file_0 138 1 138 11.
  Definition loc_103 : location_info := LocationInfo file_0 138 1 138 5.
  Definition loc_104 : location_info := LocationInfo file_0 138 1 138 5.
  Definition loc_105 : location_info := LocationInfo file_0 138 14 138 18.
  Definition loc_106 : location_info := LocationInfo file_0 138 14 138 18.
  Definition loc_109 : location_info := LocationInfo file_0 144 1 145 9.
  Definition loc_110 : location_info := LocationInfo file_0 147 1 147 38.
  Definition loc_111 : location_info := LocationInfo file_0 147 1 147 11.
  Definition loc_112 : location_info := LocationInfo file_0 147 1 147 11.
  Definition loc_113 : location_info := LocationInfo file_0 147 12 147 23.
  Definition loc_114 : location_info := LocationInfo file_0 147 12 147 23.
  Definition loc_115 : location_info := LocationInfo file_0 147 12 147 17.
  Definition loc_116 : location_info := LocationInfo file_0 147 12 147 17.
  Definition loc_117 : location_info := LocationInfo file_0 147 25 147 36.
  Definition loc_118 : location_info := LocationInfo file_0 147 25 147 36.
  Definition loc_119 : location_info := LocationInfo file_0 147 25 147 30.
  Definition loc_120 : location_info := LocationInfo file_0 147 25 147 30.
  Definition loc_121 : location_info := LocationInfo file_0 145 2 145 9.
  Definition loc_124 : location_info := LocationInfo file_0 144 5 144 35.
  Definition loc_126 : location_info := LocationInfo file_0 144 6 144 35.
  Definition loc_127 : location_info := LocationInfo file_0 144 6 144 28.
  Definition loc_128 : location_info := LocationInfo file_0 144 6 144 28.
  Definition loc_129 : location_info := LocationInfo file_0 144 29 144 34.
  Definition loc_130 : location_info := LocationInfo file_0 144 29 144 34.
  Definition loc_133 : location_info := LocationInfo file_0 156 1 156 25.
  Definition loc_134 : location_info := LocationInfo file_0 157 1 157 23.
  Definition loc_135 : location_info := LocationInfo file_0 157 1 157 15.
  Definition loc_136 : location_info := LocationInfo file_0 157 1 157 15.
  Definition loc_137 : location_info := LocationInfo file_0 157 16 157 21.
  Definition loc_138 : location_info := LocationInfo file_0 157 16 157 21.
  Definition loc_139 : location_info := LocationInfo file_0 156 1 156 17.
  Definition loc_140 : location_info := LocationInfo file_0 156 1 156 17.
  Definition loc_141 : location_info := LocationInfo file_0 156 18 156 23.
  Definition loc_142 : location_info := LocationInfo file_0 156 18 156 23.
  Definition loc_145 : location_info := LocationInfo file_0 166 1 166 29.
  Definition loc_146 : location_info := LocationInfo file_0 166 8 166 28.
  Definition loc_147 : location_info := LocationInfo file_0 166 8 166 20.
  Definition loc_148 : location_info := LocationInfo file_0 166 8 166 20.
  Definition loc_149 : location_info := LocationInfo file_0 166 9 166 13.
  Definition loc_150 : location_info := LocationInfo file_0 166 9 166 13.
  Definition loc_151 : location_info := LocationInfo file_0 166 24 166 28.
  Definition loc_152 : location_info := LocationInfo file_0 166 24 166 28.
  Definition loc_155 : location_info := LocationInfo file_0 222 1 222 62.
  Definition loc_156 : location_info := LocationInfo file_0 222 8 222 61.
  Definition loc_157 : location_info := LocationInfo file_0 222 17 222 60.
  Definition loc_158 : location_info := LocationInfo file_0 222 18 222 37.
  Definition loc_159 : location_info := LocationInfo file_0 222 31 222 37.
  Definition loc_160 : location_info := LocationInfo file_0 222 31 222 37.
  Definition loc_161 : location_info := LocationInfo file_0 222 40 222 59.
  Definition loc_162 : location_info := LocationInfo file_0 222 40 222 59.
  Definition loc_165 : location_info := LocationInfo file_0 227 1 227 52.
  Definition loc_166 : location_info := LocationInfo file_0 227 8 227 51.
  Definition loc_167 : location_info := LocationInfo file_0 227 9 227 28.
  Definition loc_168 : location_info := LocationInfo file_0 227 22 227 28.
  Definition loc_169 : location_info := LocationInfo file_0 227 22 227 28.
  Definition loc_170 : location_info := LocationInfo file_0 227 31 227 50.
  Definition loc_171 : location_info := LocationInfo file_0 227 31 227 50.
  Definition loc_174 : location_info := LocationInfo file_0 240 1 240 115.
  Definition loc_175 : location_info := LocationInfo file_0 242 1 242 20.
  Definition loc_176 : location_info := LocationInfo file_0 242 8 242 19.
  Definition loc_177 : location_info := LocationInfo file_0 242 8 242 19.
  Definition loc_178 : location_info := LocationInfo file_0 242 8 242 9.
  Definition loc_179 : location_info := LocationInfo file_0 242 8 242 9.
  Definition loc_180 : location_info := LocationInfo file_0 240 22 240 114.
  Definition loc_181 : location_info := LocationInfo file_0 240 24 240 113.
  Definition loc_182 : location_info := LocationInfo file_0 240 24 240 113.
  Definition loc_183 : location_info := LocationInfo file_0 240 24 240 58.
  Definition loc_184 : location_info := LocationInfo file_0 240 44 240 57.
  Definition loc_185 : location_info := LocationInfo file_0 240 44 240 57.
  Definition loc_186 : location_info := LocationInfo file_0 240 59 240 112.
  Definition loc_187 : location_info := LocationInfo file_0 240 60 240 105.
  Definition loc_188 : location_info := LocationInfo file_0 240 62 240 81.
  Definition loc_189 : location_info := LocationInfo file_0 240 75 240 81.
  Definition loc_190 : location_info := LocationInfo file_0 240 75 240 81.
  Definition loc_191 : location_info := LocationInfo file_0 240 84 240 103.
  Definition loc_192 : location_info := LocationInfo file_0 240 84 240 103.
  Definition loc_193 : location_info := LocationInfo file_0 240 109 240 111.
  Definition loc_198 : location_info := LocationInfo file_0 428 1 428 22.
  Definition loc_199 : location_info := LocationInfo file_0 429 1 429 42.
  Definition loc_200 : location_info := LocationInfo file_0 430 1 430 24.
  Definition loc_201 : location_info := LocationInfo file_0 432 1 432 142.
  Definition loc_202 : location_info := LocationInfo file_0 432 8 432 141.
  Definition loc_203 : location_info := LocationInfo file_0 432 8 432 9.
  Definition loc_204 : location_info := LocationInfo file_0 432 8 432 9.
  Definition loc_205 : location_info := LocationInfo file_0 432 12 432 124.
  Definition loc_206 : location_info := LocationInfo file_0 432 21 432 123.
  Definition loc_207 : location_info := LocationInfo file_0 432 22 432 100.
  Definition loc_208 : location_info := LocationInfo file_0 432 35 432 100.
  Definition loc_209 : location_info := LocationInfo file_0 432 37 432 92.
  Definition loc_210 : location_info := LocationInfo file_0 432 50 432 92.
  Definition loc_211 : location_info := LocationInfo file_0 432 51 432 54.
  Definition loc_212 : location_info := LocationInfo file_0 432 51 432 54.
  Definition loc_213 : location_info := LocationInfo file_0 432 57 432 91.
  Definition loc_214 : location_info := LocationInfo file_0 432 77 432 90.
  Definition loc_215 : location_info := LocationInfo file_0 432 77 432 90.
  Definition loc_216 : location_info := LocationInfo file_0 432 96 432 98.
  Definition loc_217 : location_info := LocationInfo file_0 432 103 432 122.
  Definition loc_218 : location_info := LocationInfo file_0 432 103 432 122.
  Definition loc_219 : location_info := LocationInfo file_0 432 127 432 141.
  Definition loc_220 : location_info := LocationInfo file_0 430 1 430 10.
  Definition loc_221 : location_info := LocationInfo file_0 430 1 430 10.
  Definition loc_222 : location_info := LocationInfo file_0 430 11 430 22.
  Definition loc_223 : location_info := LocationInfo file_0 430 12 430 22.
  Definition loc_224 : location_info := LocationInfo file_0 430 12 430 16.
  Definition loc_225 : location_info := LocationInfo file_0 430 12 430 16.
  Definition loc_226 : location_info := LocationInfo file_0 429 1 429 2.
  Definition loc_227 : location_info := LocationInfo file_0 429 5 429 41.
  Definition loc_228 : location_info := LocationInfo file_0 429 5 429 22.
  Definition loc_229 : location_info := LocationInfo file_0 429 5 429 22.
  Definition loc_230 : location_info := LocationInfo file_0 429 23 429 27.
  Definition loc_231 : location_info := LocationInfo file_0 429 23 429 27.
  Definition loc_232 : location_info := LocationInfo file_0 429 29 429 33.
  Definition loc_233 : location_info := LocationInfo file_0 429 29 429 33.
  Definition loc_234 : location_info := LocationInfo file_0 429 35 429 40.
  Definition loc_235 : location_info := LocationInfo file_0 429 35 429 40.
  Definition loc_236 : location_info := LocationInfo file_0 428 1 428 8.
  Definition loc_237 : location_info := LocationInfo file_0 428 1 428 8.
  Definition loc_238 : location_info := LocationInfo file_0 428 9 428 20.
  Definition loc_239 : location_info := LocationInfo file_0 428 10 428 20.
  Definition loc_240 : location_info := LocationInfo file_0 428 10 428 14.
  Definition loc_241 : location_info := LocationInfo file_0 428 10 428 14.
  Definition loc_244 : location_info := LocationInfo file_0 359 1 359 115.
  Definition loc_245 : location_info := LocationInfo file_0 360 1 360 56.
  Definition loc_246 : location_info := LocationInfo file_0 362 1 362 22.
  Definition loc_247 : location_info := LocationInfo file_0 363 1 363 15.
  Definition loc_248 : location_info := LocationInfo file_0 364 1 364 24.
  Definition loc_249 : location_info := LocationInfo file_0 364 1 364 10.
  Definition loc_250 : location_info := LocationInfo file_0 364 1 364 10.
  Definition loc_251 : location_info := LocationInfo file_0 364 11 364 22.
  Definition loc_252 : location_info := LocationInfo file_0 364 12 364 22.
  Definition loc_253 : location_info := LocationInfo file_0 364 12 364 16.
  Definition loc_254 : location_info := LocationInfo file_0 364 12 364 16.
  Definition loc_255 : location_info := LocationInfo file_0 363 1 363 12.
  Definition loc_256 : location_info := LocationInfo file_0 363 1 363 2.
  Definition loc_257 : location_info := LocationInfo file_0 363 1 363 2.
  Definition loc_258 : location_info := LocationInfo file_0 362 1 362 8.
  Definition loc_259 : location_info := LocationInfo file_0 362 1 362 8.
  Definition loc_260 : location_info := LocationInfo file_0 362 9 362 20.
  Definition loc_261 : location_info := LocationInfo file_0 362 10 362 20.
  Definition loc_262 : location_info := LocationInfo file_0 362 10 362 14.
  Definition loc_263 : location_info := LocationInfo file_0 362 10 362 14.
  Definition loc_264 : location_info := LocationInfo file_0 360 25 360 55.
  Definition loc_265 : location_info := LocationInfo file_0 360 25 360 55.
  Definition loc_266 : location_info := LocationInfo file_0 360 26 360 48.
  Definition loc_267 : location_info := LocationInfo file_0 360 46 360 47.
  Definition loc_268 : location_info := LocationInfo file_0 360 46 360 47.
  Definition loc_271 : location_info := LocationInfo file_0 359 22 359 114.
  Definition loc_272 : location_info := LocationInfo file_0 359 24 359 113.
  Definition loc_273 : location_info := LocationInfo file_0 359 24 359 113.
  Definition loc_274 : location_info := LocationInfo file_0 359 24 359 58.
  Definition loc_275 : location_info := LocationInfo file_0 359 44 359 57.
  Definition loc_276 : location_info := LocationInfo file_0 359 44 359 57.
  Definition loc_277 : location_info := LocationInfo file_0 359 59 359 112.
  Definition loc_278 : location_info := LocationInfo file_0 359 60 359 105.
  Definition loc_279 : location_info := LocationInfo file_0 359 62 359 81.
  Definition loc_280 : location_info := LocationInfo file_0 359 75 359 81.
  Definition loc_281 : location_info := LocationInfo file_0 359 75 359 81.
  Definition loc_282 : location_info := LocationInfo file_0 359 84 359 103.
  Definition loc_283 : location_info := LocationInfo file_0 359 84 359 103.
  Definition loc_284 : location_info := LocationInfo file_0 359 109 359 111.
  Definition loc_289 : location_info := LocationInfo file_0 345 1 345 115.
  Definition loc_290 : location_info := LocationInfo file_0 346 1 346 56.
  Definition loc_291 : location_info := LocationInfo file_0 348 1 348 22.
  Definition loc_292 : location_info := LocationInfo file_0 349 1 350 14.
  Definition loc_293 : location_info := LocationInfo file_0 351 1 351 15.
  Definition loc_294 : location_info := LocationInfo file_0 352 1 353 29.
  Definition loc_295 : location_info := LocationInfo file_0 354 1 354 24.
  Definition loc_296 : location_info := LocationInfo file_0 354 1 354 10.
  Definition loc_297 : location_info := LocationInfo file_0 354 1 354 10.
  Definition loc_298 : location_info := LocationInfo file_0 354 11 354 22.
  Definition loc_299 : location_info := LocationInfo file_0 354 12 354 22.
  Definition loc_300 : location_info := LocationInfo file_0 354 12 354 16.
  Definition loc_301 : location_info := LocationInfo file_0 354 12 354 16.
  Definition loc_302 : location_info := LocationInfo file_0 353 2 353 29.
  Definition loc_303 : location_info := LocationInfo file_0 353 2 353 19.
  Definition loc_304 : location_info := LocationInfo file_0 353 2 353 19.
  Definition loc_305 : location_info := LocationInfo file_0 353 20 353 24.
  Definition loc_306 : location_info := LocationInfo file_0 353 20 353 24.
  Definition loc_307 : location_info := LocationInfo file_0 353 26 353 27.
  Definition loc_308 : location_info := LocationInfo file_0 353 26 353 27.
  Definition loc_310 : location_info := LocationInfo file_0 352 5 352 17.
  Definition loc_312 : location_info := LocationInfo file_0 352 6 352 17.
  Definition loc_313 : location_info := LocationInfo file_0 352 6 352 17.
  Definition loc_314 : location_info := LocationInfo file_0 352 6 352 7.
  Definition loc_315 : location_info := LocationInfo file_0 352 6 352 7.
  Definition loc_316 : location_info := LocationInfo file_0 351 1 351 12.
  Definition loc_317 : location_info := LocationInfo file_0 351 1 351 2.
  Definition loc_318 : location_info := LocationInfo file_0 351 1 351 2.
  Definition loc_319 : location_info := LocationInfo file_0 350 2 350 14.
  Definition loc_320 : location_info := LocationInfo file_0 350 2 350 11.
  Definition loc_321 : location_info := LocationInfo file_0 350 2 350 11.
  Definition loc_323 : location_info := LocationInfo file_0 349 5 349 17.
  Definition loc_325 : location_info := LocationInfo file_0 349 6 349 17.
  Definition loc_326 : location_info := LocationInfo file_0 349 6 349 17.
  Definition loc_327 : location_info := LocationInfo file_0 349 6 349 7.
  Definition loc_328 : location_info := LocationInfo file_0 349 6 349 7.
  Definition loc_329 : location_info := LocationInfo file_0 348 1 348 8.
  Definition loc_330 : location_info := LocationInfo file_0 348 1 348 8.
  Definition loc_331 : location_info := LocationInfo file_0 348 9 348 20.
  Definition loc_332 : location_info := LocationInfo file_0 348 10 348 20.
  Definition loc_333 : location_info := LocationInfo file_0 348 10 348 14.
  Definition loc_334 : location_info := LocationInfo file_0 348 10 348 14.
  Definition loc_335 : location_info := LocationInfo file_0 346 25 346 55.
  Definition loc_336 : location_info := LocationInfo file_0 346 25 346 55.
  Definition loc_337 : location_info := LocationInfo file_0 346 26 346 48.
  Definition loc_338 : location_info := LocationInfo file_0 346 46 346 47.
  Definition loc_339 : location_info := LocationInfo file_0 346 46 346 47.
  Definition loc_342 : location_info := LocationInfo file_0 345 22 345 114.
  Definition loc_343 : location_info := LocationInfo file_0 345 24 345 113.
  Definition loc_344 : location_info := LocationInfo file_0 345 24 345 113.
  Definition loc_345 : location_info := LocationInfo file_0 345 24 345 58.
  Definition loc_346 : location_info := LocationInfo file_0 345 44 345 57.
  Definition loc_347 : location_info := LocationInfo file_0 345 44 345 57.
  Definition loc_348 : location_info := LocationInfo file_0 345 59 345 112.
  Definition loc_349 : location_info := LocationInfo file_0 345 60 345 105.
  Definition loc_350 : location_info := LocationInfo file_0 345 62 345 81.
  Definition loc_351 : location_info := LocationInfo file_0 345 75 345 81.
  Definition loc_352 : location_info := LocationInfo file_0 345 75 345 81.
  Definition loc_353 : location_info := LocationInfo file_0 345 84 345 103.
  Definition loc_354 : location_info := LocationInfo file_0 345 84 345 103.
  Definition loc_355 : location_info := LocationInfo file_0 345 109 345 111.
  Definition loc_360 : location_info := LocationInfo file_0 442 1 443 13.
  Definition loc_361 : location_info := LocationInfo file_0 445 1 445 22.
  Definition loc_362 : location_info := LocationInfo file_0 446 6 446 11.
  Definition loc_363 : location_info := LocationInfo file_0 446 1 447 38.
  Definition loc_364 : location_info := LocationInfo file_0 448 1 448 26.
  Definition loc_365 : location_info := LocationInfo file_0 449 1 449 43.
  Definition loc_366 : location_info := LocationInfo file_0 452 1 452 59.
  Definition loc_367 : location_info := LocationInfo file_0 453 1 453 37.
  Definition loc_368 : location_info := LocationInfo file_0 456 6 456 11.
  Definition loc_369 : location_info := LocationInfo file_0 456 1 461 2.
  Definition loc_370 : location_info := LocationInfo file_0 464 1 464 80.
  Definition loc_371 : location_info := LocationInfo file_0 467 6 467 20.
  Definition loc_372 : location_info := LocationInfo file_0 467 1 471 2.
  Definition loc_373 : location_info := LocationInfo file_0 473 1 473 10.
  Definition loc_374 : location_info := LocationInfo file_0 473 8 473 9.
  Definition loc_375 : location_info := LocationInfo file_0 467 41 471 2.
  Definition loc_376 : location_info := LocationInfo file_0 468 2 468 29.
  Definition loc_377 : location_info := LocationInfo file_0 470 2 470 9.
  Definition loc_378 : location_info := LocationInfo file_0 467 1 471 2.
  Definition loc_379 : location_info := LocationInfo file_0 467 36 467 39.
  Definition loc_380 : location_info := LocationInfo file_0 467 36 467 37.
  Definition loc_381 : location_info := LocationInfo file_0 470 2 470 3.
  Definition loc_382 : location_info := LocationInfo file_0 470 2 470 8.
  Definition loc_383 : location_info := LocationInfo file_0 470 2 470 3.
  Definition loc_384 : location_info := LocationInfo file_0 470 2 470 3.
  Definition loc_385 : location_info := LocationInfo file_0 470 7 470 8.
  Definition loc_386 : location_info := LocationInfo file_0 468 2 468 19.
  Definition loc_387 : location_info := LocationInfo file_0 468 2 468 19.
  Definition loc_388 : location_info := LocationInfo file_0 468 20 468 24.
  Definition loc_389 : location_info := LocationInfo file_0 468 20 468 24.
  Definition loc_390 : location_info := LocationInfo file_0 468 26 468 27.
  Definition loc_391 : location_info := LocationInfo file_0 468 26 468 27.
  Definition loc_392 : location_info := LocationInfo file_0 467 22 467 34.
  Definition loc_393 : location_info := LocationInfo file_0 467 22 467 23.
  Definition loc_394 : location_info := LocationInfo file_0 467 22 467 23.
  Definition loc_395 : location_info := LocationInfo file_0 467 26 467 34.
  Definition loc_396 : location_info := LocationInfo file_0 467 26 467 34.
  Definition loc_397 : location_info := LocationInfo file_0 467 6 467 7.
  Definition loc_398 : location_info := LocationInfo file_0 467 10 467 20.
  Definition loc_399 : location_info := LocationInfo file_0 467 10 467 20.
  Definition loc_400 : location_info := LocationInfo file_0 464 1 464 2.
  Definition loc_401 : location_info := LocationInfo file_0 464 5 464 79.
  Definition loc_402 : location_info := LocationInfo file_0 464 7 464 78.
  Definition loc_403 : location_info := LocationInfo file_0 464 7 464 78.
  Definition loc_404 : location_info := LocationInfo file_0 464 7 464 41.
  Definition loc_405 : location_info := LocationInfo file_0 464 27 464 40.
  Definition loc_406 : location_info := LocationInfo file_0 464 27 464 40.
  Definition loc_407 : location_info := LocationInfo file_0 464 42 464 77.
  Definition loc_408 : location_info := LocationInfo file_0 464 43 464 70.
  Definition loc_409 : location_info := LocationInfo file_0 464 44 464 48.
  Definition loc_410 : location_info := LocationInfo file_0 464 44 464 48.
  Definition loc_411 : location_info := LocationInfo file_0 464 51 464 69.
  Definition loc_412 : location_info := LocationInfo file_0 464 52 464 62.
  Definition loc_413 : location_info := LocationInfo file_0 464 52 464 62.
  Definition loc_414 : location_info := LocationInfo file_0 464 66 464 68.
  Definition loc_415 : location_info := LocationInfo file_0 464 74 464 76.
  Definition loc_416 : location_info := LocationInfo file_0 456 32 461 2.
  Definition loc_417 : location_info := LocationInfo file_0 457 2 457 17.
  Definition loc_418 : location_info := LocationInfo file_0 458 2 458 27.
  Definition loc_419 : location_info := LocationInfo file_0 460 2 460 9.
  Definition loc_420 : location_info := LocationInfo file_0 456 1 461 2.
  Definition loc_421 : location_info := LocationInfo file_0 456 27 456 30.
  Definition loc_422 : location_info := LocationInfo file_0 456 27 456 28.
  Definition loc_423 : location_info := LocationInfo file_0 460 2 460 3.
  Definition loc_424 : location_info := LocationInfo file_0 460 2 460 8.
  Definition loc_425 : location_info := LocationInfo file_0 460 2 460 3.
  Definition loc_426 : location_info := LocationInfo file_0 460 2 460 3.
  Definition loc_427 : location_info := LocationInfo file_0 460 7 460 8.
  Definition loc_428 : location_info := LocationInfo file_0 458 2 458 16.
  Definition loc_429 : location_info := LocationInfo file_0 458 2 458 16.
  Definition loc_430 : location_info := LocationInfo file_0 458 17 458 25.
  Definition loc_431 : location_info := LocationInfo file_0 458 18 458 25.
  Definition loc_432 : location_info := LocationInfo file_0 458 18 458 19.
  Definition loc_433 : location_info := LocationInfo file_0 458 18 458 19.
  Definition loc_434 : location_info := LocationInfo file_0 457 2 457 9.
  Definition loc_435 : location_info := LocationInfo file_0 457 2 457 3.
  Definition loc_436 : location_info := LocationInfo file_0 457 2 457 3.
  Definition loc_437 : location_info := LocationInfo file_0 457 12 457 16.
  Definition loc_438 : location_info := LocationInfo file_0 457 12 457 16.
  Definition loc_439 : location_info := LocationInfo file_0 456 13 456 25.
  Definition loc_440 : location_info := LocationInfo file_0 456 13 456 14.
  Definition loc_441 : location_info := LocationInfo file_0 456 13 456 14.
  Definition loc_442 : location_info := LocationInfo file_0 456 17 456 25.
  Definition loc_443 : location_info := LocationInfo file_0 456 17 456 25.
  Definition loc_444 : location_info := LocationInfo file_0 456 6 456 7.
  Definition loc_445 : location_info := LocationInfo file_0 456 10 456 11.
  Definition loc_446 : location_info := LocationInfo file_0 453 1 453 7.
  Definition loc_447 : location_info := LocationInfo file_0 453 1 453 7.
  Definition loc_448 : location_info := LocationInfo file_0 453 8 453 9.
  Definition loc_449 : location_info := LocationInfo file_0 453 8 453 9.
  Definition loc_450 : location_info := LocationInfo file_0 453 11 453 12.
  Definition loc_451 : location_info := LocationInfo file_0 453 14 453 35.
  Definition loc_452 : location_info := LocationInfo file_0 453 14 453 24.
  Definition loc_453 : location_info := LocationInfo file_0 453 27 453 35.
  Definition loc_454 : location_info := LocationInfo file_0 453 27 453 35.
  Definition loc_455 : location_info := LocationInfo file_0 452 1 452 2.
  Definition loc_456 : location_info := LocationInfo file_0 452 5 452 58.
  Definition loc_457 : location_info := LocationInfo file_0 452 7 452 57.
  Definition loc_458 : location_info := LocationInfo file_0 452 7 452 57.
  Definition loc_459 : location_info := LocationInfo file_0 452 7 452 41.
  Definition loc_460 : location_info := LocationInfo file_0 452 27 452 40.
  Definition loc_461 : location_info := LocationInfo file_0 452 27 452 40.
  Definition loc_462 : location_info := LocationInfo file_0 452 42 452 56.
  Definition loc_463 : location_info := LocationInfo file_0 452 43 452 49.
  Definition loc_464 : location_info := LocationInfo file_0 452 43 452 49.
  Definition loc_465 : location_info := LocationInfo file_0 452 53 452 55.
  Definition loc_466 : location_info := LocationInfo file_0 449 1 449 16.
  Definition loc_467 : location_info := LocationInfo file_0 449 1 449 5.
  Definition loc_468 : location_info := LocationInfo file_0 449 1 449 5.
  Definition loc_469 : location_info := LocationInfo file_0 449 19 449 42.
  Definition loc_470 : location_info := LocationInfo file_0 449 19 449 23.
  Definition loc_471 : location_info := LocationInfo file_0 449 19 449 23.
  Definition loc_472 : location_info := LocationInfo file_0 449 26 449 42.
  Definition loc_473 : location_info := LocationInfo file_0 449 27 449 35.
  Definition loc_474 : location_info := LocationInfo file_0 449 27 449 35.
  Definition loc_475 : location_info := LocationInfo file_0 449 39 449 41.
  Definition loc_476 : location_info := LocationInfo file_0 448 1 448 18.
  Definition loc_477 : location_info := LocationInfo file_0 448 1 448 5.
  Definition loc_478 : location_info := LocationInfo file_0 448 1 448 5.
  Definition loc_479 : location_info := LocationInfo file_0 448 21 448 25.
  Definition loc_480 : location_info := LocationInfo file_0 448 21 448 25.
  Definition loc_481 : location_info := LocationInfo file_0 446 1 447 38.
  Definition loc_482 : location_info := LocationInfo file_0 447 2 447 38.
  Definition loc_483 : location_info := LocationInfo file_0 446 1 447 38.
  Definition loc_484 : location_info := LocationInfo file_0 446 23 446 26.
  Definition loc_485 : location_info := LocationInfo file_0 446 23 446 24.
  Definition loc_486 : location_info := LocationInfo file_0 447 2 447 16.
  Definition loc_487 : location_info := LocationInfo file_0 447 2 447 16.
  Definition loc_488 : location_info := LocationInfo file_0 447 17 447 36.
  Definition loc_489 : location_info := LocationInfo file_0 447 18 447 36.
  Definition loc_490 : location_info := LocationInfo file_0 447 18 447 36.
  Definition loc_491 : location_info := LocationInfo file_0 447 18 447 33.
  Definition loc_492 : location_info := LocationInfo file_0 447 18 447 33.
  Definition loc_493 : location_info := LocationInfo file_0 447 18 447 22.
  Definition loc_494 : location_info := LocationInfo file_0 447 18 447 22.
  Definition loc_495 : location_info := LocationInfo file_0 447 34 447 35.
  Definition loc_496 : location_info := LocationInfo file_0 447 34 447 35.
  Definition loc_497 : location_info := LocationInfo file_0 446 13 446 21.
  Definition loc_498 : location_info := LocationInfo file_0 446 13 446 14.
  Definition loc_499 : location_info := LocationInfo file_0 446 13 446 14.
  Definition loc_500 : location_info := LocationInfo file_0 446 18 446 21.
  Definition loc_501 : location_info := LocationInfo file_0 446 6 446 7.
  Definition loc_502 : location_info := LocationInfo file_0 446 10 446 11.
  Definition loc_503 : location_info := LocationInfo file_0 445 1 445 8.
  Definition loc_504 : location_info := LocationInfo file_0 445 1 445 8.
  Definition loc_505 : location_info := LocationInfo file_0 445 9 445 20.
  Definition loc_506 : location_info := LocationInfo file_0 445 10 445 20.
  Definition loc_507 : location_info := LocationInfo file_0 445 10 445 14.
  Definition loc_508 : location_info := LocationInfo file_0 445 10 445 14.
  Definition loc_509 : location_info := LocationInfo file_0 443 2 443 13.
  Definition loc_510 : location_info := LocationInfo file_0 443 9 443 12.
  Definition loc_511 : location_info := LocationInfo file_0 443 10 443 12.
  Definition loc_513 : location_info := LocationInfo file_0 442 5 442 16.
  Definition loc_514 : location_info := LocationInfo file_0 442 5 442 9.
  Definition loc_515 : location_info := LocationInfo file_0 442 5 442 9.
  Definition loc_516 : location_info := LocationInfo file_0 442 12 442 16.
  Definition loc_519 : location_info := LocationInfo file_0 303 1 303 84.
  Definition loc_520 : location_info := LocationInfo file_0 305 1 305 25.
  Definition loc_521 : location_info := LocationInfo file_0 306 1 307 24.
  Definition loc_522 : location_info := LocationInfo file_0 309 1 309 62.
  Definition loc_523 : location_info := LocationInfo file_0 309 8 309 61.
  Definition loc_524 : location_info := LocationInfo file_0 309 10 309 60.
  Definition loc_525 : location_info := LocationInfo file_0 309 10 309 60.
  Definition loc_526 : location_info := LocationInfo file_0 309 10 309 44.
  Definition loc_527 : location_info := LocationInfo file_0 309 30 309 43.
  Definition loc_528 : location_info := LocationInfo file_0 309 30 309 43.
  Definition loc_529 : location_info := LocationInfo file_0 309 45 309 59.
  Definition loc_530 : location_info := LocationInfo file_0 309 46 309 52.
  Definition loc_531 : location_info := LocationInfo file_0 309 46 309 52.
  Definition loc_532 : location_info := LocationInfo file_0 309 56 309 58.
  Definition loc_533 : location_info := LocationInfo file_0 307 2 307 24.
  Definition loc_534 : location_info := LocationInfo file_0 307 9 307 23.
  Definition loc_537 : location_info := LocationInfo file_0 306 5 306 29.
  Definition loc_538 : location_info := LocationInfo file_0 306 5 306 9.
  Definition loc_539 : location_info := LocationInfo file_0 306 5 306 9.
  Definition loc_540 : location_info := LocationInfo file_0 306 12 306 29.
  Definition loc_541 : location_info := LocationInfo file_0 306 12 306 29.
  Definition loc_542 : location_info := LocationInfo file_0 306 12 306 16.
  Definition loc_543 : location_info := LocationInfo file_0 306 12 306 16.
  Definition loc_544 : location_info := LocationInfo file_0 306 33 306 56.
  Definition loc_545 : location_info := LocationInfo file_0 306 33 306 37.
  Definition loc_546 : location_info := LocationInfo file_0 306 33 306 37.
  Definition loc_547 : location_info := LocationInfo file_0 306 41 306 56.
  Definition loc_548 : location_info := LocationInfo file_0 306 41 306 56.
  Definition loc_549 : location_info := LocationInfo file_0 306 41 306 45.
  Definition loc_550 : location_info := LocationInfo file_0 306 41 306 45.
  Definition loc_551 : location_info := LocationInfo file_0 305 1 305 5.
  Definition loc_552 : location_info := LocationInfo file_0 305 1 305 24.
  Definition loc_553 : location_info := LocationInfo file_0 305 1 305 5.
  Definition loc_554 : location_info := LocationInfo file_0 305 1 305 5.
  Definition loc_555 : location_info := LocationInfo file_0 305 9 305 24.
  Definition loc_556 : location_info := LocationInfo file_0 305 10 305 14.
  Definition loc_557 : location_info := LocationInfo file_0 305 18 305 23.
  Definition loc_558 : location_info := LocationInfo file_0 305 18 305 23.
  Definition loc_559 : location_info := LocationInfo file_0 303 20 303 83.
  Definition loc_560 : location_info := LocationInfo file_0 303 21 303 76.
  Definition loc_561 : location_info := LocationInfo file_0 303 34 303 76.
  Definition loc_562 : location_info := LocationInfo file_0 303 35 303 38.
  Definition loc_563 : location_info := LocationInfo file_0 303 35 303 38.
  Definition loc_564 : location_info := LocationInfo file_0 303 41 303 75.
  Definition loc_565 : location_info := LocationInfo file_0 303 61 303 74.
  Definition loc_566 : location_info := LocationInfo file_0 303 61 303 74.
  Definition loc_567 : location_info := LocationInfo file_0 303 80 303 82.
  Definition loc_572 : location_info := LocationInfo file_0 315 1 315 31.
  Definition loc_573 : location_info := LocationInfo file_0 318 1 318 31.
  Definition loc_574 : location_info := LocationInfo file_0 319 1 337 2.
  Definition loc_575 : location_info := LocationInfo file_0 339 1 339 18.
  Definition loc_576 : location_info := LocationInfo file_0 340 1 340 50.
  Definition loc_577 : location_info := LocationInfo file_0 340 1 340 14.
  Definition loc_578 : location_info := LocationInfo file_0 340 1 340 14.
  Definition loc_579 : location_info := LocationInfo file_0 340 15 340 23.
  Definition loc_580 : location_info := LocationInfo file_0 340 16 340 23.
  Definition loc_581 : location_info := LocationInfo file_0 340 16 340 17.
  Definition loc_582 : location_info := LocationInfo file_0 340 16 340 17.
  Definition loc_583 : location_info := LocationInfo file_0 340 25 340 48.
  Definition loc_584 : location_info := LocationInfo file_0 340 26 340 48.
  Definition loc_585 : location_info := LocationInfo file_0 340 26 340 48.
  Definition loc_586 : location_info := LocationInfo file_0 340 26 340 41.
  Definition loc_587 : location_info := LocationInfo file_0 340 26 340 41.
  Definition loc_588 : location_info := LocationInfo file_0 340 26 340 30.
  Definition loc_589 : location_info := LocationInfo file_0 340 26 340 30.
  Definition loc_590 : location_info := LocationInfo file_0 340 42 340 47.
  Definition loc_591 : location_info := LocationInfo file_0 340 42 340 47.
  Definition loc_592 : location_info := LocationInfo file_0 339 1 339 9.
  Definition loc_593 : location_info := LocationInfo file_0 339 1 339 2.
  Definition loc_594 : location_info := LocationInfo file_0 339 1 339 2.
  Definition loc_595 : location_info := LocationInfo file_0 339 12 339 17.
  Definition loc_596 : location_info := LocationInfo file_0 339 12 339 17.
  Definition loc_597 : location_info := LocationInfo file_0 319 30 337 2.
  Definition loc_598 : location_info := LocationInfo file_0 321 2 321 39.
  Definition loc_599 : location_info := LocationInfo file_0 324 2 325 9.
  Definition loc_600 : location_info := LocationInfo file_0 328 2 328 30.
  Definition loc_601 : location_info := LocationInfo file_0 329 2 329 36.
  Definition loc_602 : location_info := LocationInfo file_0 332 2 336 3.
  Definition loc_603 : location_info := LocationInfo file_0 319 1 337 2.
  Definition loc_604 : location_info := LocationInfo file_0 319 21 319 28.
  Definition loc_605 : location_info := LocationInfo file_0 319 21 319 26.
  Definition loc_606 : location_info := LocationInfo file_0 332 17 334 3.
  Definition loc_607 : location_info := LocationInfo file_0 333 3 333 9.
  Definition loc_608 : location_info := LocationInfo file_0 333 3 333 4.
  Definition loc_609 : location_info := LocationInfo file_0 333 7 333 8.
  Definition loc_610 : location_info := LocationInfo file_0 333 7 333 8.
  Definition loc_611 : location_info := LocationInfo file_0 334 9 336 3.
  Definition loc_612 : location_info := LocationInfo file_0 335 3 335 13.
  Definition loc_613 : location_info := LocationInfo file_0 335 3 335 4.
  Definition loc_614 : location_info := LocationInfo file_0 335 7 335 12.
  Definition loc_615 : location_info := LocationInfo file_0 335 7 335 12.
  Definition loc_616 : location_info := LocationInfo file_0 332 6 332 15.
  Definition loc_617 : location_info := LocationInfo file_0 332 6 332 7.
  Definition loc_618 : location_info := LocationInfo file_0 332 6 332 7.
  Definition loc_619 : location_info := LocationInfo file_0 332 10 332 15.
  Definition loc_620 : location_info := LocationInfo file_0 332 10 332 15.
  Definition loc_621 : location_info := LocationInfo file_0 329 2 329 14.
  Definition loc_622 : location_info := LocationInfo file_0 329 2 329 7.
  Definition loc_623 : location_info := LocationInfo file_0 329 2 329 7.
  Definition loc_624 : location_info := LocationInfo file_0 329 17 329 35.
  Definition loc_625 : location_info := LocationInfo file_0 328 2 328 15.
  Definition loc_626 : location_info := LocationInfo file_0 328 2 328 15.
  Definition loc_627 : location_info := LocationInfo file_0 328 16 328 28.
  Definition loc_628 : location_info := LocationInfo file_0 328 17 328 28.
  Definition loc_629 : location_info := LocationInfo file_0 328 17 328 22.
  Definition loc_630 : location_info := LocationInfo file_0 328 17 328 22.
  Definition loc_631 : location_info := LocationInfo file_0 325 3 325 9.
  Definition loc_635 : location_info := LocationInfo file_0 324 6 324 29.
  Definition loc_636 : location_info := LocationInfo file_0 324 6 324 11.
  Definition loc_637 : location_info := LocationInfo file_0 324 6 324 11.
  Definition loc_638 : location_info := LocationInfo file_0 324 15 324 29.
  Definition loc_639 : location_info := LocationInfo file_0 324 33 324 57.
  Definition loc_640 : location_info := LocationInfo file_0 324 33 324 43.
  Definition loc_641 : location_info := LocationInfo file_0 324 33 324 43.
  Definition loc_642 : location_info := LocationInfo file_0 324 44 324 56.
  Definition loc_643 : location_info := LocationInfo file_0 324 45 324 56.
  Definition loc_644 : location_info := LocationInfo file_0 324 45 324 50.
  Definition loc_645 : location_info := LocationInfo file_0 324 45 324 50.
  Definition loc_646 : location_info := LocationInfo file_0 324 61 324 82.
  Definition loc_647 : location_info := LocationInfo file_0 324 61 324 73.
  Definition loc_648 : location_info := LocationInfo file_0 324 61 324 73.
  Definition loc_649 : location_info := LocationInfo file_0 324 61 324 66.
  Definition loc_650 : location_info := LocationInfo file_0 324 61 324 66.
  Definition loc_651 : location_info := LocationInfo file_0 324 77 324 82.
  Definition loc_652 : location_info := LocationInfo file_0 324 77 324 82.
  Definition loc_653 : location_info := LocationInfo file_0 321 2 321 7.
  Definition loc_654 : location_info := LocationInfo file_0 321 10 321 38.
  Definition loc_655 : location_info := LocationInfo file_0 321 10 321 22.
  Definition loc_656 : location_info := LocationInfo file_0 321 10 321 22.
  Definition loc_657 : location_info := LocationInfo file_0 321 23 321 27.
  Definition loc_658 : location_info := LocationInfo file_0 321 23 321 27.
  Definition loc_659 : location_info := LocationInfo file_0 321 29 321 30.
  Definition loc_660 : location_info := LocationInfo file_0 321 29 321 30.
  Definition loc_661 : location_info := LocationInfo file_0 321 32 321 37.
  Definition loc_662 : location_info := LocationInfo file_0 321 32 321 37.
  Definition loc_663 : location_info := LocationInfo file_0 319 8 319 19.
  Definition loc_664 : location_info := LocationInfo file_0 319 8 319 13.
  Definition loc_665 : location_info := LocationInfo file_0 319 8 319 13.
  Definition loc_666 : location_info := LocationInfo file_0 319 16 319 19.
  Definition loc_667 : location_info := LocationInfo file_0 318 1 318 9.
  Definition loc_668 : location_info := LocationInfo file_0 318 1 318 2.
  Definition loc_669 : location_info := LocationInfo file_0 318 1 318 2.
  Definition loc_670 : location_info := LocationInfo file_0 318 12 318 30.
  Definition loc_671 : location_info := LocationInfo file_0 315 22 315 30.
  Definition loc_672 : location_info := LocationInfo file_0 315 22 315 30.
  Definition loc_673 : location_info := LocationInfo file_0 315 22 315 23.
  Definition loc_674 : location_info := LocationInfo file_0 315 22 315 23.
  Definition loc_679 : location_info := LocationInfo file_0 374 1 375 24.
  Definition loc_680 : location_info := LocationInfo file_0 377 1 377 25.
  Definition loc_681 : location_info := LocationInfo file_0 380 1 385 2.
  Definition loc_682 : location_info := LocationInfo file_0 387 1 387 17.
  Definition loc_683 : location_info := LocationInfo file_0 389 1 389 10.
  Definition loc_684 : location_info := LocationInfo file_0 389 8 389 9.
  Definition loc_685 : location_info := LocationInfo file_0 389 8 389 9.
  Definition loc_686 : location_info := LocationInfo file_0 387 1 387 12.
  Definition loc_687 : location_info := LocationInfo file_0 387 1 387 2.
  Definition loc_688 : location_info := LocationInfo file_0 387 1 387 2.
  Definition loc_689 : location_info := LocationInfo file_0 387 15 387 16.
  Definition loc_690 : location_info := LocationInfo file_0 380 1 385 2.
  Definition loc_691 : location_info := LocationInfo file_0 380 26 385 2.
  Definition loc_692 : location_info := LocationInfo file_0 381 2 381 13.
  Definition loc_693 : location_info := LocationInfo file_0 382 2 382 42.
  Definition loc_694 : location_info := LocationInfo file_0 383 2 383 26.
  Definition loc_695 : location_info := LocationInfo file_0 384 2 384 62.
  Definition loc_696 : location_info := LocationInfo file_0 380 1 385 2.
  Definition loc_697 : location_info := LocationInfo file_0 380 1 385 2.
  Definition loc_698 : location_info := LocationInfo file_0 384 2 384 15.
  Definition loc_699 : location_info := LocationInfo file_0 384 2 384 15.
  Definition loc_700 : location_info := LocationInfo file_0 384 16 384 28.
  Definition loc_701 : location_info := LocationInfo file_0 384 17 384 28.
  Definition loc_702 : location_info := LocationInfo file_0 384 17 384 22.
  Definition loc_703 : location_info := LocationInfo file_0 384 17 384 22.
  Definition loc_704 : location_info := LocationInfo file_0 384 30 384 60.
  Definition loc_705 : location_info := LocationInfo file_0 384 31 384 60.
  Definition loc_706 : location_info := LocationInfo file_0 384 31 384 60.
  Definition loc_707 : location_info := LocationInfo file_0 384 31 384 46.
  Definition loc_708 : location_info := LocationInfo file_0 384 31 384 46.
  Definition loc_709 : location_info := LocationInfo file_0 384 31 384 35.
  Definition loc_710 : location_info := LocationInfo file_0 384 31 384 35.
  Definition loc_711 : location_info := LocationInfo file_0 384 47 384 59.
  Definition loc_712 : location_info := LocationInfo file_0 384 47 384 59.
  Definition loc_713 : location_info := LocationInfo file_0 384 47 384 52.
  Definition loc_714 : location_info := LocationInfo file_0 384 47 384 52.
  Definition loc_715 : location_info := LocationInfo file_0 383 2 383 14.
  Definition loc_716 : location_info := LocationInfo file_0 383 2 383 7.
  Definition loc_717 : location_info := LocationInfo file_0 383 2 383 7.
  Definition loc_718 : location_info := LocationInfo file_0 383 17 383 25.
  Definition loc_719 : location_info := LocationInfo file_0 383 17 383 25.
  Definition loc_720 : location_info := LocationInfo file_0 383 17 383 18.
  Definition loc_721 : location_info := LocationInfo file_0 383 17 383 18.
  Definition loc_722 : location_info := LocationInfo file_0 382 2 382 7.
  Definition loc_723 : location_info := LocationInfo file_0 382 10 382 41.
  Definition loc_724 : location_info := LocationInfo file_0 382 10 382 22.
  Definition loc_725 : location_info := LocationInfo file_0 382 10 382 22.
  Definition loc_726 : location_info := LocationInfo file_0 382 23 382 27.
  Definition loc_727 : location_info := LocationInfo file_0 382 23 382 27.
  Definition loc_728 : location_info := LocationInfo file_0 382 29 382 30.
  Definition loc_729 : location_info := LocationInfo file_0 382 29 382 30.
  Definition loc_730 : location_info := LocationInfo file_0 382 32 382 40.
  Definition loc_731 : location_info := LocationInfo file_0 382 32 382 40.
  Definition loc_732 : location_info := LocationInfo file_0 382 32 382 33.
  Definition loc_733 : location_info := LocationInfo file_0 382 32 382 33.
  Definition loc_734 : location_info := LocationInfo file_0 381 2 381 10.
  Definition loc_735 : location_info := LocationInfo file_0 381 2 381 3.
  Definition loc_736 : location_info := LocationInfo file_0 381 2 381 3.
  Definition loc_737 : location_info := LocationInfo file_0 380 8 380 24.
  Definition loc_738 : location_info := LocationInfo file_0 380 8 380 16.
  Definition loc_739 : location_info := LocationInfo file_0 380 8 380 16.
  Definition loc_740 : location_info := LocationInfo file_0 380 8 380 9.
  Definition loc_741 : location_info := LocationInfo file_0 380 8 380 9.
  Definition loc_742 : location_info := LocationInfo file_0 380 19 380 24.
  Definition loc_743 : location_info := LocationInfo file_0 380 19 380 24.
  Definition loc_744 : location_info := LocationInfo file_0 377 1 377 14.
  Definition loc_745 : location_info := LocationInfo file_0 377 1 377 14.
  Definition loc_746 : location_info := LocationInfo file_0 377 15 377 23.
  Definition loc_747 : location_info := LocationInfo file_0 377 16 377 23.
  Definition loc_748 : location_info := LocationInfo file_0 377 16 377 17.
  Definition loc_749 : location_info := LocationInfo file_0 377 16 377 17.
  Definition loc_750 : location_info := LocationInfo file_0 375 2 375 24.
  Definition loc_751 : location_info := LocationInfo file_0 375 9 375 23.
  Definition loc_754 : location_info := LocationInfo file_0 374 5 374 35.
  Definition loc_755 : location_info := LocationInfo file_0 374 5 374 13.
  Definition loc_756 : location_info := LocationInfo file_0 374 5 374 13.
  Definition loc_757 : location_info := LocationInfo file_0 374 5 374 6.
  Definition loc_758 : location_info := LocationInfo file_0 374 5 374 6.
  Definition loc_759 : location_info := LocationInfo file_0 374 17 374 35.
  Definition loc_760 : location_info := LocationInfo file_0 374 39 374 55.
  Definition loc_761 : location_info := LocationInfo file_0 374 39 374 47.
  Definition loc_762 : location_info := LocationInfo file_0 374 39 374 47.
  Definition loc_763 : location_info := LocationInfo file_0 374 39 374 40.
  Definition loc_764 : location_info := LocationInfo file_0 374 39 374 40.
  Definition loc_765 : location_info := LocationInfo file_0 374 50 374 55.
  Definition loc_766 : location_info := LocationInfo file_0 374 50 374 55.
  Definition loc_769 : location_info := LocationInfo file_0 396 6 396 11.
  Definition loc_770 : location_info := LocationInfo file_0 396 1 397 156.
  Definition loc_771 : location_info := LocationInfo file_0 396 1 397 156.
  Definition loc_772 : location_info := LocationInfo file_0 397 2 397 156.
  Definition loc_773 : location_info := LocationInfo file_0 396 1 397 156.
  Definition loc_774 : location_info := LocationInfo file_0 396 34 396 37.
  Definition loc_775 : location_info := LocationInfo file_0 396 34 396 35.
  Definition loc_776 : location_info := LocationInfo file_0 397 2 397 12.
  Definition loc_777 : location_info := LocationInfo file_0 397 2 397 12.
  Definition loc_778 : location_info := LocationInfo file_0 397 13 397 154.
  Definition loc_779 : location_info := LocationInfo file_0 397 13 397 142.
  Definition loc_780 : location_info := LocationInfo file_0 397 30 397 142.
  Definition loc_781 : location_info := LocationInfo file_0 397 39 397 141.
  Definition loc_782 : location_info := LocationInfo file_0 397 40 397 118.
  Definition loc_783 : location_info := LocationInfo file_0 397 53 397 118.
  Definition loc_784 : location_info := LocationInfo file_0 397 55 397 110.
  Definition loc_785 : location_info := LocationInfo file_0 397 68 397 110.
  Definition loc_786 : location_info := LocationInfo file_0 397 69 397 72.
  Definition loc_787 : location_info := LocationInfo file_0 397 69 397 72.
  Definition loc_788 : location_info := LocationInfo file_0 397 75 397 109.
  Definition loc_789 : location_info := LocationInfo file_0 397 95 397 108.
  Definition loc_790 : location_info := LocationInfo file_0 397 95 397 108.
  Definition loc_791 : location_info := LocationInfo file_0 397 114 397 116.
  Definition loc_792 : location_info := LocationInfo file_0 397 121 397 140.
  Definition loc_793 : location_info := LocationInfo file_0 397 121 397 140.
  Definition loc_794 : location_info := LocationInfo file_0 397 145 397 154.
  Definition loc_795 : location_info := LocationInfo file_0 397 146 397 147.
  Definition loc_796 : location_info := LocationInfo file_0 397 146 397 147.
  Definition loc_797 : location_info := LocationInfo file_0 397 151 397 153.
  Definition loc_798 : location_info := LocationInfo file_0 396 13 396 32.
  Definition loc_799 : location_info := LocationInfo file_0 396 13 396 14.
  Definition loc_800 : location_info := LocationInfo file_0 396 13 396 14.
  Definition loc_801 : location_info := LocationInfo file_0 396 17 396 32.
  Definition loc_802 : location_info := LocationInfo file_0 396 18 396 19.
  Definition loc_803 : location_info := LocationInfo file_0 396 23 396 31.
  Definition loc_804 : location_info := LocationInfo file_0 396 23 396 31.
  Definition loc_805 : location_info := LocationInfo file_0 396 23 396 24.
  Definition loc_806 : location_info := LocationInfo file_0 396 23 396 24.
  Definition loc_807 : location_info := LocationInfo file_0 396 6 396 7.
  Definition loc_808 : location_info := LocationInfo file_0 396 10 396 11.
  Definition loc_811 : location_info := LocationInfo file_0 405 1 405 24.
  Definition loc_812 : location_info := LocationInfo file_0 409 1 410 6.
  Definition loc_813 : location_info := LocationInfo file_0 411 1 412 24.
  Definition loc_814 : location_info := LocationInfo file_0 415 1 415 99.
  Definition loc_815 : location_info := LocationInfo file_0 416 1 416 40.
  Definition loc_816 : location_info := LocationInfo file_0 418 1 419 20.
  Definition loc_817 : location_info := LocationInfo file_0 421 1 421 10.
  Definition loc_818 : location_info := LocationInfo file_0 421 8 421 9.
  Definition loc_819 : location_info := LocationInfo file_0 421 8 421 9.
  Definition loc_820 : location_info := LocationInfo file_0 419 2 419 20.
  Definition loc_821 : location_info := LocationInfo file_0 419 2 419 16.
  Definition loc_822 : location_info := LocationInfo file_0 419 2 419 16.
  Definition loc_823 : location_info := LocationInfo file_0 419 17 419 18.
  Definition loc_824 : location_info := LocationInfo file_0 419 17 419 18.
  Definition loc_826 : location_info := LocationInfo file_0 418 5 418 13.
  Definition loc_827 : location_info := LocationInfo file_0 418 5 418 9.
  Definition loc_828 : location_info := LocationInfo file_0 418 5 418 9.
  Definition loc_829 : location_info := LocationInfo file_0 418 12 418 13.
  Definition loc_830 : location_info := LocationInfo file_0 416 1 416 2.
  Definition loc_831 : location_info := LocationInfo file_0 416 5 416 39.
  Definition loc_832 : location_info := LocationInfo file_0 416 5 416 23.
  Definition loc_833 : location_info := LocationInfo file_0 416 5 416 23.
  Definition loc_834 : location_info := LocationInfo file_0 416 24 416 28.
  Definition loc_835 : location_info := LocationInfo file_0 416 24 416 28.
  Definition loc_836 : location_info := LocationInfo file_0 416 30 416 31.
  Definition loc_837 : location_info := LocationInfo file_0 416 30 416 31.
  Definition loc_838 : location_info := LocationInfo file_0 416 33 416 38.
  Definition loc_839 : location_info := LocationInfo file_0 416 33 416 38.
  Definition loc_840 : location_info := LocationInfo file_0 415 1 415 2.
  Definition loc_841 : location_info := LocationInfo file_0 415 5 415 98.
  Definition loc_842 : location_info := LocationInfo file_0 415 24 415 98.
  Definition loc_843 : location_info := LocationInfo file_0 415 26 415 63.
  Definition loc_844 : location_info := LocationInfo file_0 415 34 415 63.
  Definition loc_845 : location_info := LocationInfo file_0 415 34 415 63.
  Definition loc_846 : location_info := LocationInfo file_0 415 35 415 56.
  Definition loc_847 : location_info := LocationInfo file_0 415 37 415 55.
  Definition loc_848 : location_info := LocationInfo file_0 415 37 415 55.
  Definition loc_849 : location_info := LocationInfo file_0 415 37 415 52.
  Definition loc_850 : location_info := LocationInfo file_0 415 37 415 52.
  Definition loc_851 : location_info := LocationInfo file_0 415 37 415 41.
  Definition loc_852 : location_info := LocationInfo file_0 415 37 415 41.
  Definition loc_853 : location_info := LocationInfo file_0 415 53 415 54.
  Definition loc_854 : location_info := LocationInfo file_0 415 53 415 54.
  Definition loc_855 : location_info := LocationInfo file_0 415 66 415 96.
  Definition loc_856 : location_info := LocationInfo file_0 412 2 412 24.
  Definition loc_857 : location_info := LocationInfo file_0 412 9 412 23.
  Definition loc_859 : location_info := LocationInfo file_0 411 5 411 12.
  Definition loc_860 : location_info := LocationInfo file_0 411 5 411 6.
  Definition loc_861 : location_info := LocationInfo file_0 411 5 411 6.
  Definition loc_862 : location_info := LocationInfo file_0 411 9 411 12.
  Definition loc_863 : location_info := LocationInfo file_0 409 1 410 6.
  Definition loc_864 : location_info := LocationInfo file_0 410 2 410 6.
  Definition loc_865 : location_info := LocationInfo file_0 409 1 410 6.
  Definition loc_866 : location_info := LocationInfo file_0 409 1 410 6.
  Definition loc_867 : location_info := LocationInfo file_0 410 2 410 3.
  Definition loc_869 : location_info := LocationInfo file_0 409 8 409 16.
  Definition loc_870 : location_info := LocationInfo file_0 409 8 409 9.
  Definition loc_871 : location_info := LocationInfo file_0 409 8 409 9.
  Definition loc_872 : location_info := LocationInfo file_0 409 13 409 16.
  Definition loc_873 : location_info := LocationInfo file_0 409 20 409 51.
  Definition loc_874 : location_info := LocationInfo file_0 409 20 409 30.
  Definition loc_875 : location_info := LocationInfo file_0 409 20 409 30.
  Definition loc_876 : location_info := LocationInfo file_0 409 31 409 50.
  Definition loc_877 : location_info := LocationInfo file_0 409 32 409 50.
  Definition loc_878 : location_info := LocationInfo file_0 409 32 409 50.
  Definition loc_879 : location_info := LocationInfo file_0 409 32 409 47.
  Definition loc_880 : location_info := LocationInfo file_0 409 32 409 47.
  Definition loc_881 : location_info := LocationInfo file_0 409 32 409 36.
  Definition loc_882 : location_info := LocationInfo file_0 409 32 409 36.
  Definition loc_883 : location_info := LocationInfo file_0 409 48 409 49.
  Definition loc_884 : location_info := LocationInfo file_0 409 48 409 49.
  Definition loc_885 : location_info := LocationInfo file_0 405 18 405 23.
  Definition loc_886 : location_info := LocationInfo file_0 405 18 405 23.

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

  (* Definition of function [hyp_page_count]. *)
  Definition impl_hyp_page_count (global___hyp_vmemmap global_hyp_physvirt_offset : loc): function := {|
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
          LocInfoE loc_180 (&(LocInfoE loc_182 ((LocInfoE loc_183 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_184 (!{it_layout u64} (LocInfoE loc_185 (global___hyp_vmemmap)))))) at_offset{layout_of struct_hyp_page, PtrOp, IntOp u64} (LocInfoE loc_186 ((LocInfoE loc_187 ((LocInfoE loc_188 (UnOp (CastOp $ IntOp u64) (PtrOp) (LocInfoE loc_189 (use{void*} (LocInfoE loc_190 ("addr")))))) +{IntOp u64, IntOp u64} (LocInfoE loc_191 (UnOp (CastOp $ IntOp u64) (IntOp i64) (LocInfoE loc_191 (use{it_layout i64} (LocInfoE loc_192 (global_hyp_physvirt_offset)))))))) >>{IntOp u64, IntOp u64} (LocInfoE loc_193 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_193 (i2v 12 i32))))))))) ;
        locinfo: loc_175 ;
        Return (LocInfoE loc_176 (UnOp (CastOp $ IntOp i32) (IntOp u32) (LocInfoE loc_176 (use{it_layout u32} (LocInfoE loc_177 ((LocInfoE loc_178 (!{void*} (LocInfoE loc_179 ("p")))) at{struct_hyp_page} "refcount"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_alloc_pages]. *)
  Definition impl_hyp_alloc_pages (global___hyp_vmemmap global_hyp_physvirt_offset global___hyp_alloc_pages global_sl_lock global_sl_unlock : loc): function := {|
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
        locinfo: loc_198 ;
        expr: (LocInfoE loc_198 (Call (LocInfoE loc_237 (global_sl_lock)) [@{expr} LocInfoE loc_238 (&(LocInfoE loc_239 ((LocInfoE loc_240 (!{void*} (LocInfoE loc_241 ("pool")))) at{struct_hyp_pool} "lock"))) ])) ;
        locinfo: loc_199 ;
        LocInfoE loc_226 ("p") <-{ void* }
          LocInfoE loc_227 (Call (LocInfoE loc_229 (global___hyp_alloc_pages)) [@{expr} LocInfoE loc_230 (use{void*} (LocInfoE loc_231 ("pool"))) ;
          LocInfoE loc_232 (use{it_layout u64} (LocInfoE loc_233 ("mask"))) ;
          LocInfoE loc_234 (use{it_layout u32} (LocInfoE loc_235 ("order"))) ]) ;
        locinfo: loc_200 ;
        expr: (LocInfoE loc_200 (Call (LocInfoE loc_221 (global_sl_unlock)) [@{expr} LocInfoE loc_222 (AnnotExpr 1%nat LockA (LocInfoE loc_222 (&(LocInfoE loc_223 ((LocInfoE loc_224 (!{void*} (LocInfoE loc_225 ("pool")))) at{struct_hyp_pool} "lock"))))) ])) ;
        locinfo: loc_201 ;
        Return (LocInfoE loc_202 (IfE (PtrOp)
               (LocInfoE loc_203 (use{void*} (LocInfoE loc_204 ("p"))))
               (LocInfoE loc_205 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_206 ((LocInfoE loc_207 (UnOp (CastOp $ IntOp u64) (IntOp u64) (LocInfoE loc_208 ((LocInfoE loc_209 (UnOp (CastOp $ IntOp u64) (IntOp ssize_t) (LocInfoE loc_210 ((LocInfoE loc_211 (use{void*} (LocInfoE loc_212 ("p")))) -{PtrOp, PtrOp} (LocInfoE loc_213 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_214 (use{it_layout u64} (LocInfoE loc_215 (global___hyp_vmemmap)))))))))) <<{IntOp u64, IntOp u64} (LocInfoE loc_216 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_216 (i2v 12 i32)))))))) -{IntOp u64, IntOp u64} (LocInfoE loc_217 (UnOp (CastOp $ IntOp u64) (IntOp i64) (LocInfoE loc_217 (use{it_layout i64} (LocInfoE loc_218 (global_hyp_physvirt_offset))))))))))
               (LocInfoE loc_219 (NULL))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_get_page]. *)
  Definition impl_hyp_get_page (global___hyp_vmemmap global_hyp_physvirt_offset global_sl_lock global_sl_unlock : loc): function := {|
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
          LocInfoE loc_271 (&(LocInfoE loc_273 ((LocInfoE loc_274 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_275 (!{it_layout u64} (LocInfoE loc_276 (global___hyp_vmemmap)))))) at_offset{layout_of struct_hyp_page, PtrOp, IntOp u64} (LocInfoE loc_277 ((LocInfoE loc_278 ((LocInfoE loc_279 (UnOp (CastOp $ IntOp u64) (PtrOp) (LocInfoE loc_280 (use{void*} (LocInfoE loc_281 ("addr")))))) +{IntOp u64, IntOp u64} (LocInfoE loc_282 (UnOp (CastOp $ IntOp u64) (IntOp i64) (LocInfoE loc_282 (use{it_layout i64} (LocInfoE loc_283 (global_hyp_physvirt_offset)))))))) >>{IntOp u64, IntOp u64} (LocInfoE loc_284 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_284 (i2v 12 i32))))))))) ;
        "pool" <-{ void* }
          LocInfoE loc_264 (use{void*} (LocInfoE loc_265 ((LocInfoE loc_266 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_267 (!{void*} (LocInfoE loc_268 ("p")))))) at{struct_hyp_page} "pool"))) ;
        locinfo: loc_246 ;
        expr: (LocInfoE loc_246 (Call (LocInfoE loc_259 (global_sl_lock)) [@{expr} LocInfoE loc_260 (&(LocInfoE loc_261 ((LocInfoE loc_262 (!{void*} (LocInfoE loc_263 ("pool")))) at{struct_hyp_pool} "lock"))) ])) ;
        locinfo: loc_247 ;
        LocInfoE loc_255 ((LocInfoE loc_256 (!{void*} (LocInfoE loc_257 ("p")))) at{struct_hyp_page} "refcount") <-{ it_layout u32 }
          LocInfoE loc_247 ((LocInfoE loc_247 (use{it_layout u32} (LocInfoE loc_255 ((LocInfoE loc_256 (!{void*} (LocInfoE loc_257 ("p")))) at{struct_hyp_page} "refcount")))) +{IntOp u32, IntOp u32} (LocInfoE loc_247 (i2v 1 u32))) ;
        locinfo: loc_248 ;
        expr: (LocInfoE loc_248 (Call (LocInfoE loc_250 (global_sl_unlock)) [@{expr} LocInfoE loc_251 (AnnotExpr 1%nat LockA (LocInfoE loc_251 (&(LocInfoE loc_252 ((LocInfoE loc_253 (!{void*} (LocInfoE loc_254 ("pool")))) at{struct_hyp_pool} "lock"))))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_put_page]. *)
  Definition impl_hyp_put_page (global___hyp_vmemmap global_hyp_physvirt_offset global___hyp_attach_page global_hyp_panic global_sl_lock global_sl_unlock : loc): function := {|
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
          LocInfoE loc_342 (&(LocInfoE loc_344 ((LocInfoE loc_345 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_346 (!{it_layout u64} (LocInfoE loc_347 (global___hyp_vmemmap)))))) at_offset{layout_of struct_hyp_page, PtrOp, IntOp u64} (LocInfoE loc_348 ((LocInfoE loc_349 ((LocInfoE loc_350 (UnOp (CastOp $ IntOp u64) (PtrOp) (LocInfoE loc_351 (use{void*} (LocInfoE loc_352 ("addr")))))) +{IntOp u64, IntOp u64} (LocInfoE loc_353 (UnOp (CastOp $ IntOp u64) (IntOp i64) (LocInfoE loc_353 (use{it_layout i64} (LocInfoE loc_354 (global_hyp_physvirt_offset)))))))) >>{IntOp u64, IntOp u64} (LocInfoE loc_355 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_355 (i2v 12 i32))))))))) ;
        "pool" <-{ void* }
          LocInfoE loc_335 (use{void*} (LocInfoE loc_336 ((LocInfoE loc_337 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_338 (!{void*} (LocInfoE loc_339 ("p")))))) at{struct_hyp_page} "pool"))) ;
        locinfo: loc_291 ;
        expr: (LocInfoE loc_291 (Call (LocInfoE loc_330 (global_sl_lock)) [@{expr} LocInfoE loc_331 (&(LocInfoE loc_332 ((LocInfoE loc_333 (!{void*} (LocInfoE loc_334 ("pool")))) at{struct_hyp_pool} "lock"))) ])) ;
        locinfo: loc_323 ;
        if: LocInfoE loc_323 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_323 ((UnOp (CastOp $ IntOp u32) (IntOp i32) (i2v 0 i32)) ={IntOp u32, IntOp u32} (LocInfoE loc_325 (use{it_layout u32} (LocInfoE loc_326 ((LocInfoE loc_327 (!{void*} (LocInfoE loc_328 ("p")))) at{struct_hyp_page} "refcount")))))))
        then
        locinfo: loc_319 ;
          Goto "#5"
        else
        locinfo: loc_293 ;
          Goto "#6"
      ]> $
      <[ "#1" :=
        locinfo: loc_293 ;
        LocInfoE loc_316 ((LocInfoE loc_317 (!{void*} (LocInfoE loc_318 ("p")))) at{struct_hyp_page} "refcount") <-{ it_layout u32 }
          LocInfoE loc_293 ((LocInfoE loc_293 (use{it_layout u32} (LocInfoE loc_316 ((LocInfoE loc_317 (!{void*} (LocInfoE loc_318 ("p")))) at{struct_hyp_page} "refcount")))) -{IntOp u32, IntOp u32} (LocInfoE loc_293 (i2v 1 u32))) ;
        locinfo: loc_310 ;
        if: LocInfoE loc_310 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_310 ((UnOp (CastOp $ IntOp u32) (IntOp i32) (i2v 0 i32)) ={IntOp u32, IntOp u32} (LocInfoE loc_312 (use{it_layout u32} (LocInfoE loc_313 ((LocInfoE loc_314 (!{void*} (LocInfoE loc_315 ("p")))) at{struct_hyp_page} "refcount")))))))
        then
        locinfo: loc_302 ;
          Goto "#3"
        else
        locinfo: loc_295 ;
          Goto "#4"
      ]> $
      <[ "#2" :=
        locinfo: loc_295 ;
        expr: (LocInfoE loc_295 (Call (LocInfoE loc_297 (global_sl_unlock)) [@{expr} LocInfoE loc_298 (AnnotExpr 1%nat LockA (LocInfoE loc_298 (&(LocInfoE loc_299 ((LocInfoE loc_300 (!{void*} (LocInfoE loc_301 ("pool")))) at{struct_hyp_pool} "lock"))))) ])) ;
        Return (VOID)
      ]> $
      <[ "#3" :=
        locinfo: loc_302 ;
        expr: (LocInfoE loc_302 (Call (LocInfoE loc_304 (global___hyp_attach_page)) [@{expr} LocInfoE loc_305 (use{void*} (LocInfoE loc_306 ("pool"))) ;
        LocInfoE loc_307 (use{void*} (LocInfoE loc_308 ("p"))) ])) ;
        locinfo: loc_295 ;
        Goto "#2"
      ]> $
      <[ "#4" :=
        locinfo: loc_295 ;
        Goto "#2"
      ]> $
      <[ "#5" :=
        locinfo: loc_319 ;
        expr: (LocInfoE loc_319 (Call (LocInfoE loc_321 (global_hyp_panic)) [@{expr}  ])) ;
        locinfo: loc_293 ;
        Goto "#1"
      ]> $
      <[ "#6" :=
        locinfo: loc_293 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_pool_init]. *)
  Definition impl_hyp_pool_init (global___hyp_vmemmap global_INIT_LIST_HEAD global___hyp_attach_page global_memset global_sl_init : loc): function := {|
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
        locinfo: loc_513 ;
        if: LocInfoE loc_513 (UnOp (CastOp $ IntOp bool_it) (IntOp u64) (LocInfoE loc_513 ((LocInfoE loc_514 (use{it_layout u64} (LocInfoE loc_515 ("phys")))) %{IntOp u64, IntOp u64} (LocInfoE loc_516 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_516 (i2v 4096 i32)))))))
        then
        locinfo: loc_509 ;
          Goto "#11"
        else
        locinfo: loc_361 ;
          Goto "#12"
      ]> $
      <[ "#1" :=
        locinfo: loc_361 ;
        expr: (LocInfoE loc_361 (Call (LocInfoE loc_504 (global_sl_init)) [@{expr} LocInfoE loc_505 (&(LocInfoE loc_506 ((LocInfoE loc_507 (!{void*} (LocInfoE loc_508 ("pool")))) at{struct_hyp_pool} "lock"))) ])) ;
        locinfo: loc_362 ;
        LocInfoE loc_501 ("i") <-{ it_layout i32 }
          LocInfoE loc_502 (i2v 0 i32) ;
        locinfo: loc_363 ;
        Goto "#2"
      ]> $
      <[ "#10" :=
        locinfo: loc_373 ;
        Return (LocInfoE loc_374 (i2v 0 i32))
      ]> $
      <[ "#11" :=
        locinfo: loc_509 ;
        Return (LocInfoE loc_510 (UnOp NegOp (IntOp i32) (LocInfoE loc_511 (i2v 22 i32))))
      ]> $
      <[ "#12" :=
        locinfo: loc_361 ;
        Goto "#1"
      ]> $
      <[ "#2" :=
        locinfo: loc_497 ;
        if: LocInfoE loc_497 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_497 ((LocInfoE loc_498 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_498 (use{it_layout i32} (LocInfoE loc_499 ("i")))))) ≤{IntOp u32, IntOp u32} (LocInfoE loc_500 (i2v 11 u32)))))
        then
        locinfo: loc_482 ;
          Goto "#3"
        else
        locinfo: loc_364 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_482 ;
        expr: (LocInfoE loc_482 (Call (LocInfoE loc_487 (global_INIT_LIST_HEAD)) [@{expr} LocInfoE loc_488 (&(LocInfoE loc_490 ((LocInfoE loc_492 ((LocInfoE loc_493 (!{void*} (LocInfoE loc_494 ("pool")))) at{struct_hyp_pool} "free_area")) at_offset{layout_of struct_list_head, PtrOp, IntOp i32} (LocInfoE loc_495 (use{it_layout i32} (LocInfoE loc_496 ("i"))))))) ])) ;
        locinfo: loc_483 ;
        Goto "continue54"
      ]> $
      <[ "#4" :=
        locinfo: loc_364 ;
        LocInfoE loc_476 ((LocInfoE loc_477 (!{void*} (LocInfoE loc_478 ("pool")))) at{struct_hyp_pool} "range_start") <-{ it_layout u64 }
          LocInfoE loc_479 (use{it_layout u64} (LocInfoE loc_480 ("phys"))) ;
        locinfo: loc_365 ;
        LocInfoE loc_466 ((LocInfoE loc_467 (!{void*} (LocInfoE loc_468 ("pool")))) at{struct_hyp_pool} "range_end") <-{ it_layout u64 }
          LocInfoE loc_469 ((LocInfoE loc_470 (use{it_layout u64} (LocInfoE loc_471 ("phys")))) +{IntOp u64, IntOp u64} (LocInfoE loc_472 (UnOp (CastOp $ IntOp u64) (IntOp u32) (LocInfoE loc_472 ((LocInfoE loc_473 (use{it_layout u32} (LocInfoE loc_474 ("nr_pages")))) <<{IntOp u32, IntOp u32} (LocInfoE loc_475 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_475 (i2v 12 i32))))))))) ;
        locinfo: loc_366 ;
        LocInfoE loc_455 ("p") <-{ void* }
          LocInfoE loc_456 (&(LocInfoE loc_458 ((LocInfoE loc_459 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_460 (!{it_layout u64} (LocInfoE loc_461 (global___hyp_vmemmap)))))) at_offset{layout_of struct_hyp_page, PtrOp, IntOp u64} (LocInfoE loc_462 ((LocInfoE loc_463 (use{it_layout u64} (LocInfoE loc_464 ("phys")))) >>{IntOp u64, IntOp u64} (LocInfoE loc_465 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_465 (i2v 12 i32))))))))) ;
        locinfo: loc_367 ;
        expr: (LocInfoE loc_367 (Call (LocInfoE loc_447 (global_memset)) [@{expr} LocInfoE loc_448 (use{void*} (LocInfoE loc_449 ("p"))) ;
        LocInfoE loc_450 (i2v 0 i32) ;
        LocInfoE loc_451 ((LocInfoE loc_452 (i2v (layout_of struct_hyp_page).(ly_size) size_t)) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_453 (UnOp (CastOp $ IntOp size_t) (IntOp u32) (LocInfoE loc_453 (use{it_layout u32} (LocInfoE loc_454 ("nr_pages"))))))) ])) ;
        locinfo: loc_368 ;
        LocInfoE loc_444 ("i") <-{ it_layout i32 }
          LocInfoE loc_445 (i2v 0 i32) ;
        locinfo: loc_369 ;
        Goto "#5"
      ]> $
      <[ "#5" :=
        locinfo: loc_439 ;
        if: LocInfoE loc_439 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_439 ((LocInfoE loc_440 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_440 (use{it_layout i32} (LocInfoE loc_441 ("i")))))) <{IntOp u32, IntOp u32} (LocInfoE loc_442 (use{it_layout u32} (LocInfoE loc_443 ("nr_pages")))))))
        then
        locinfo: loc_417 ;
          Goto "#6"
        else
        locinfo: loc_370 ;
          Goto "#7"
      ]> $
      <[ "#6" :=
        locinfo: loc_417 ;
        LocInfoE loc_434 ((LocInfoE loc_435 (!{void*} (LocInfoE loc_436 ("p")))) at{struct_hyp_page} "pool") <-{ void* }
          LocInfoE loc_437 (use{void*} (LocInfoE loc_438 ("pool"))) ;
        locinfo: loc_418 ;
        expr: (LocInfoE loc_418 (Call (LocInfoE loc_429 (global_INIT_LIST_HEAD)) [@{expr} LocInfoE loc_430 (&(LocInfoE loc_431 ((LocInfoE loc_432 (!{void*} (LocInfoE loc_433 ("p")))) at{struct_hyp_page} "node"))) ])) ;
        locinfo: loc_419 ;
        LocInfoE loc_423 ("p") <-{ void* }
          LocInfoE loc_424 ((LocInfoE loc_425 (use{void*} (LocInfoE loc_426 ("p")))) at_offset{layout_of struct_hyp_page, PtrOp, IntOp i32} (LocInfoE loc_427 (i2v 1 i32))) ;
        locinfo: loc_420 ;
        Goto "continue55"
      ]> $
      <[ "#7" :=
        locinfo: loc_370 ;
        LocInfoE loc_400 ("p") <-{ void* }
          LocInfoE loc_401 (&(LocInfoE loc_403 ((LocInfoE loc_404 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_405 (!{it_layout u64} (LocInfoE loc_406 (global___hyp_vmemmap)))))) at_offset{layout_of struct_hyp_page, PtrOp, IntOp u64} (LocInfoE loc_407 ((LocInfoE loc_408 ((LocInfoE loc_409 (use{it_layout u64} (LocInfoE loc_410 ("phys")))) +{IntOp u64, IntOp u64} (LocInfoE loc_411 (UnOp (CastOp $ IntOp u64) (IntOp u32) (LocInfoE loc_411 ((LocInfoE loc_412 (use{it_layout u32} (LocInfoE loc_413 ("used_pages")))) <<{IntOp u32, IntOp u32} (LocInfoE loc_414 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_414 (i2v 12 i32)))))))))) >>{IntOp u64, IntOp u64} (LocInfoE loc_415 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_415 (i2v 12 i32))))))))) ;
        locinfo: loc_371 ;
        LocInfoE loc_397 ("i") <-{ it_layout i32 }
          LocInfoE loc_398 (UnOp (CastOp $ IntOp i32) (IntOp u32) (LocInfoE loc_398 (use{it_layout u32} (LocInfoE loc_399 ("used_pages"))))) ;
        locinfo: loc_372 ;
        Goto "#8"
      ]> $
      <[ "#8" :=
        locinfo: loc_392 ;
        if: LocInfoE loc_392 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_392 ((LocInfoE loc_393 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_393 (use{it_layout i32} (LocInfoE loc_394 ("i")))))) <{IntOp u32, IntOp u32} (LocInfoE loc_395 (use{it_layout u32} (LocInfoE loc_396 ("nr_pages")))))))
        then
        locinfo: loc_376 ;
          Goto "#9"
        else
        locinfo: loc_373 ;
          Goto "#10"
      ]> $
      <[ "#9" :=
        locinfo: loc_376 ;
        expr: (LocInfoE loc_376 (Call (LocInfoE loc_387 (global___hyp_attach_page)) [@{expr} LocInfoE loc_388 (use{void*} (LocInfoE loc_389 ("pool"))) ;
        LocInfoE loc_390 (use{void*} (LocInfoE loc_391 ("p"))) ])) ;
        locinfo: loc_377 ;
        LocInfoE loc_381 ("p") <-{ void* }
          LocInfoE loc_382 ((LocInfoE loc_383 (use{void*} (LocInfoE loc_384 ("p")))) at_offset{layout_of struct_hyp_page, PtrOp, IntOp i32} (LocInfoE loc_385 (i2v 1 i32))) ;
        locinfo: loc_378 ;
        Goto "continue57"
      ]> $
      <[ "continue54" :=
        locinfo: loc_484 ;
        LocInfoE loc_485 ("i") <-{ it_layout i32 }
          LocInfoE loc_484 ((LocInfoE loc_484 (use{it_layout i32} (LocInfoE loc_485 ("i")))) +{IntOp i32, IntOp i32} (LocInfoE loc_484 (i2v 1 i32))) ;
        locinfo: loc_363 ;
        Goto "#2"
      ]> $
      <[ "continue55" :=
        locinfo: loc_421 ;
        LocInfoE loc_422 ("i") <-{ it_layout i32 }
          LocInfoE loc_421 ((LocInfoE loc_421 (use{it_layout i32} (LocInfoE loc_422 ("i")))) +{IntOp i32, IntOp i32} (LocInfoE loc_421 (i2v 1 i32))) ;
        locinfo: loc_369 ;
        Goto "#5"
      ]> $
      <[ "continue57" :=
        locinfo: loc_379 ;
        LocInfoE loc_380 ("i") <-{ it_layout i32 }
          LocInfoE loc_379 ((LocInfoE loc_379 (use{it_layout i32} (LocInfoE loc_380 ("i")))) +{IntOp i32, IntOp i32} (LocInfoE loc_379 (i2v 1 i32))) ;
        locinfo: loc_372 ;
        Goto "#8"
      ]> $∅
    )%E
  |}.

  (* Definition of function [__find_buddy]. *)
  Definition impl___find_buddy (global___hyp_vmemmap : loc): function := {|
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
        "addr" <-{ it_layout u64 }
          LocInfoE loc_559 ((LocInfoE loc_560 (UnOp (CastOp $ IntOp u64) (IntOp ssize_t) (LocInfoE loc_561 ((LocInfoE loc_562 (use{void*} (LocInfoE loc_563 ("p")))) -{PtrOp, PtrOp} (LocInfoE loc_564 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_565 (use{it_layout u64} (LocInfoE loc_566 (global___hyp_vmemmap)))))))))) <<{IntOp u64, IntOp u64} (LocInfoE loc_567 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_567 (i2v 12 i32))))) ;
        locinfo: loc_520 ;
        LocInfoE loc_551 ("addr") <-{ it_layout u64 }
          LocInfoE loc_552 ((LocInfoE loc_553 (use{it_layout u64} (LocInfoE loc_554 ("addr")))) ^{IntOp u64, IntOp u64} (LocInfoE loc_555 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_555 ((LocInfoE loc_556 (i2v 4096 i32)) <<{IntOp i32, IntOp i32} (LocInfoE loc_557 (UnOp (CastOp $ IntOp i32) (IntOp u32) (LocInfoE loc_557 (use{it_layout u32} (LocInfoE loc_558 ("order"))))))))))) ;
        locinfo: loc_537 ;
        if: LocInfoE loc_537 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_537 ((LocInfoE loc_538 (use{it_layout u64} (LocInfoE loc_539 ("addr")))) <{IntOp u64, IntOp u64} (LocInfoE loc_540 (use{it_layout u64} (LocInfoE loc_541 ((LocInfoE loc_542 (!{void*} (LocInfoE loc_543 ("pool")))) at{struct_hyp_pool} "range_start")))))))
        then
        locinfo: loc_533 ;
          Goto "#2"
        else
        Goto "#4"
      ]> $
      <[ "#1" :=
        locinfo: loc_522 ;
        Return (LocInfoE loc_523 (&(LocInfoE loc_525 ((LocInfoE loc_526 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_527 (!{it_layout u64} (LocInfoE loc_528 (global___hyp_vmemmap)))))) at_offset{layout_of struct_hyp_page, PtrOp, IntOp u64} (LocInfoE loc_529 ((LocInfoE loc_530 (use{it_layout u64} (LocInfoE loc_531 ("addr")))) >>{IntOp u64, IntOp u64} (LocInfoE loc_532 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_532 (i2v 12 i32))))))))))
      ]> $
      <[ "#2" :=
        locinfo: loc_533 ;
        Return (LocInfoE loc_534 (NULL))
      ]> $
      <[ "#3" :=
        locinfo: loc_522 ;
        Goto "#1"
      ]> $
      <[ "#4" :=
        locinfo: loc_544 ;
        if: LocInfoE loc_544 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_544 ((LocInfoE loc_545 (use{it_layout u64} (LocInfoE loc_546 ("addr")))) ≥{IntOp u64, IntOp u64} (LocInfoE loc_547 (use{it_layout u64} (LocInfoE loc_548 ((LocInfoE loc_549 (!{void*} (LocInfoE loc_550 ("pool")))) at{struct_hyp_pool} "range_end")))))))
        then
        locinfo: loc_533 ;
          Goto "#2"
        else
        locinfo: loc_522 ;
          Goto "#3"
      ]> $∅
    )%E
  |}.

  (* Definition of function [__hyp_attach_page]. *)
  Definition impl___hyp_attach_page (global___find_buddy global_list_add_tail global_list_del_init global_list_empty : loc): function := {|
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
        "order" <-{ it_layout u32 }
          LocInfoE loc_671 (use{it_layout u32} (LocInfoE loc_672 ((LocInfoE loc_673 (!{void*} (LocInfoE loc_674 ("p")))) at{struct_hyp_page} "order"))) ;
        locinfo: loc_573 ;
        LocInfoE loc_667 ((LocInfoE loc_668 (!{void*} (LocInfoE loc_669 ("p")))) at{struct_hyp_page} "order") <-{ it_layout u32 }
          LocInfoE loc_670 (i2v (max_int u32) u32) ;
        locinfo: loc_574 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_663 ;
        if: LocInfoE loc_663 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_663 ((LocInfoE loc_664 (use{it_layout u32} (LocInfoE loc_665 ("order")))) <{IntOp u32, IntOp u32} (LocInfoE loc_666 (i2v 11 u32)))))
        then
        locinfo: loc_598 ;
          Goto "#2"
        else
        locinfo: loc_575 ;
          Goto "#3"
      ]> $
      <[ "#10" :=
        locinfo: loc_646 ;
        if: LocInfoE loc_646 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_646 ((LocInfoE loc_647 (use{it_layout u32} (LocInfoE loc_648 ((LocInfoE loc_649 (!{void*} (LocInfoE loc_650 ("buddy")))) at{struct_hyp_page} "order")))) !={IntOp u32, IntOp u32} (LocInfoE loc_651 (use{it_layout u32} (LocInfoE loc_652 ("order")))))))
        then
        locinfo: loc_575 ;
          Goto "#8"
        else
        locinfo: loc_600 ;
          Goto "#9"
      ]> $
      <[ "#11" :=
        locinfo: loc_639 ;
        if: LocInfoE loc_639 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_639 (Call (LocInfoE loc_641 (global_list_empty)) [@{expr} LocInfoE loc_642 (&(LocInfoE loc_643 ((LocInfoE loc_644 (!{void*} (LocInfoE loc_645 ("buddy")))) at{struct_hyp_page} "node"))) ])))
        then
        locinfo: loc_575 ;
          Goto "#8"
        else
        Goto "#10"
      ]> $
      <[ "#2" :=
        locinfo: loc_598 ;
        LocInfoE loc_653 ("buddy") <-{ void* }
          LocInfoE loc_654 (Call (LocInfoE loc_656 (global___find_buddy)) [@{expr} LocInfoE loc_657 (use{void*} (LocInfoE loc_658 ("pool"))) ;
          LocInfoE loc_659 (use{void*} (LocInfoE loc_660 ("p"))) ;
          LocInfoE loc_661 (use{it_layout u32} (LocInfoE loc_662 ("order"))) ]) ;
        locinfo: loc_635 ;
        if: LocInfoE loc_635 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_635 ((LocInfoE loc_636 (use{void*} (LocInfoE loc_637 ("buddy")))) ={PtrOp, PtrOp} (LocInfoE loc_638 (NULL)))))
        then
        locinfo: loc_575 ;
          Goto "#8"
        else
        Goto "#11"
      ]> $
      <[ "#3" :=
        locinfo: loc_575 ;
        LocInfoE loc_592 ((LocInfoE loc_593 (!{void*} (LocInfoE loc_594 ("p")))) at{struct_hyp_page} "order") <-{ it_layout u32 }
          LocInfoE loc_595 (use{it_layout u32} (LocInfoE loc_596 ("order"))) ;
        locinfo: loc_576 ;
        expr: (LocInfoE loc_576 (Call (LocInfoE loc_578 (global_list_add_tail)) [@{expr} LocInfoE loc_579 (&(LocInfoE loc_580 ((LocInfoE loc_581 (!{void*} (LocInfoE loc_582 ("p")))) at{struct_hyp_page} "node"))) ;
        LocInfoE loc_583 (&(LocInfoE loc_585 ((LocInfoE loc_587 ((LocInfoE loc_588 (!{void*} (LocInfoE loc_589 ("pool")))) at{struct_hyp_pool} "free_area")) at_offset{layout_of struct_list_head, PtrOp, IntOp u32} (LocInfoE loc_590 (use{it_layout u32} (LocInfoE loc_591 ("order"))))))) ])) ;
        Return (VOID)
      ]> $
      <[ "#4" :=
        locinfo: loc_600 ;
        expr: (LocInfoE loc_600 (Call (LocInfoE loc_626 (global_list_del_init)) [@{expr} LocInfoE loc_627 (&(LocInfoE loc_628 ((LocInfoE loc_629 (!{void*} (LocInfoE loc_630 ("buddy")))) at{struct_hyp_page} "node"))) ])) ;
        locinfo: loc_601 ;
        LocInfoE loc_621 ((LocInfoE loc_622 (!{void*} (LocInfoE loc_623 ("buddy")))) at{struct_hyp_page} "order") <-{ it_layout u32 }
          LocInfoE loc_624 (i2v (max_int u32) u32) ;
        locinfo: loc_616 ;
        if: LocInfoE loc_616 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_616 ((LocInfoE loc_617 (use{void*} (LocInfoE loc_618 ("p")))) <{PtrOp, PtrOp} (LocInfoE loc_619 (use{void*} (LocInfoE loc_620 ("buddy")))))))
        then
        locinfo: loc_607 ;
          Goto "#6"
        else
        locinfo: loc_612 ;
          Goto "#7"
      ]> $
      <[ "#5" :=
        locinfo: loc_603 ;
        Goto "continue32"
      ]> $
      <[ "#6" :=
        locinfo: loc_607 ;
        LocInfoE loc_608 ("p") <-{ void* }
          LocInfoE loc_609 (use{void*} (LocInfoE loc_610 ("p"))) ;
        locinfo: loc_603 ;
        Goto "#5"
      ]> $
      <[ "#7" :=
        locinfo: loc_612 ;
        LocInfoE loc_613 ("p") <-{ void* }
          LocInfoE loc_614 (use{void*} (LocInfoE loc_615 ("buddy"))) ;
        locinfo: loc_603 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        locinfo: loc_575 ;
        Goto "#3"
      ]> $
      <[ "#9" :=
        locinfo: loc_600 ;
        Goto "#4"
      ]> $
      <[ "continue32" :=
        locinfo: loc_604 ;
        LocInfoE loc_605 ("order") <-{ it_layout u32 }
          LocInfoE loc_604 ((LocInfoE loc_604 (use{it_layout u32} (LocInfoE loc_605 ("order")))) +{IntOp u32, IntOp u32} (LocInfoE loc_604 (i2v 1 u32))) ;
        locinfo: loc_574 ;
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
        locinfo: loc_754 ;
        if: LocInfoE loc_754 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_754 ((LocInfoE loc_755 (use{it_layout u32} (LocInfoE loc_756 ((LocInfoE loc_757 (!{void*} (LocInfoE loc_758 ("p")))) at{struct_hyp_page} "order")))) ={IntOp u32, IntOp u32} (LocInfoE loc_759 (i2v (max_int u32) u32)))))
        then
        locinfo: loc_750 ;
          Goto "#5"
        else
        Goto "#7"
      ]> $
      <[ "#1" :=
        locinfo: loc_680 ;
        expr: (LocInfoE loc_680 (Call (LocInfoE loc_745 (global_list_del_init)) [@{expr} LocInfoE loc_746 (&(LocInfoE loc_747 ((LocInfoE loc_748 (!{void*} (LocInfoE loc_749 ("p")))) at{struct_hyp_page} "node"))) ])) ;
        locinfo: loc_681 ;
        Goto "#2"
      ]> $
      <[ "#2" :=
        locinfo: loc_737 ;
        if: LocInfoE loc_737 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_737 ((LocInfoE loc_738 (use{it_layout u32} (LocInfoE loc_739 ((LocInfoE loc_740 (!{void*} (LocInfoE loc_741 ("p")))) at{struct_hyp_page} "order")))) >{IntOp u32, IntOp u32} (LocInfoE loc_742 (use{it_layout u32} (LocInfoE loc_743 ("order")))))))
        then
        locinfo: loc_692 ;
          Goto "#3"
        else
        locinfo: loc_682 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_692 ;
        LocInfoE loc_734 ((LocInfoE loc_735 (!{void*} (LocInfoE loc_736 ("p")))) at{struct_hyp_page} "order") <-{ it_layout u32 }
          LocInfoE loc_692 ((LocInfoE loc_692 (use{it_layout u32} (LocInfoE loc_734 ((LocInfoE loc_735 (!{void*} (LocInfoE loc_736 ("p")))) at{struct_hyp_page} "order")))) -{IntOp u32, IntOp u32} (LocInfoE loc_692 (i2v 1 u32))) ;
        locinfo: loc_693 ;
        LocInfoE loc_722 ("buddy") <-{ void* }
          LocInfoE loc_723 (Call (LocInfoE loc_725 (global___find_buddy)) [@{expr} LocInfoE loc_726 (use{void*} (LocInfoE loc_727 ("pool"))) ;
          LocInfoE loc_728 (use{void*} (LocInfoE loc_729 ("p"))) ;
          LocInfoE loc_730 (use{it_layout u32} (LocInfoE loc_731 ((LocInfoE loc_732 (!{void*} (LocInfoE loc_733 ("p")))) at{struct_hyp_page} "order"))) ]) ;
        locinfo: loc_694 ;
        LocInfoE loc_715 ((LocInfoE loc_716 (!{void*} (LocInfoE loc_717 ("buddy")))) at{struct_hyp_page} "order") <-{ it_layout u32 }
          LocInfoE loc_718 (use{it_layout u32} (LocInfoE loc_719 ((LocInfoE loc_720 (!{void*} (LocInfoE loc_721 ("p")))) at{struct_hyp_page} "order"))) ;
        locinfo: loc_695 ;
        expr: (LocInfoE loc_695 (Call (LocInfoE loc_699 (global_list_add_tail)) [@{expr} LocInfoE loc_700 (&(LocInfoE loc_701 ((LocInfoE loc_702 (!{void*} (LocInfoE loc_703 ("buddy")))) at{struct_hyp_page} "node"))) ;
        LocInfoE loc_704 (&(LocInfoE loc_706 ((LocInfoE loc_708 ((LocInfoE loc_709 (!{void*} (LocInfoE loc_710 ("pool")))) at{struct_hyp_pool} "free_area")) at_offset{layout_of struct_list_head, PtrOp, IntOp u32} (LocInfoE loc_711 (use{it_layout u32} (LocInfoE loc_712 ((LocInfoE loc_713 (!{void*} (LocInfoE loc_714 ("buddy")))) at{struct_hyp_page} "order"))))))) ])) ;
        locinfo: loc_696 ;
        Goto "continue42"
      ]> $
      <[ "#4" :=
        locinfo: loc_682 ;
        LocInfoE loc_686 ((LocInfoE loc_687 (!{void*} (LocInfoE loc_688 ("p")))) at{struct_hyp_page} "refcount") <-{ it_layout u32 }
          LocInfoE loc_689 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_689 (i2v 1 i32))) ;
        locinfo: loc_683 ;
        Return (LocInfoE loc_684 (use{void*} (LocInfoE loc_685 ("p"))))
      ]> $
      <[ "#5" :=
        locinfo: loc_750 ;
        Return (LocInfoE loc_751 (NULL))
      ]> $
      <[ "#6" :=
        locinfo: loc_680 ;
        Goto "#1"
      ]> $
      <[ "#7" :=
        locinfo: loc_760 ;
        if: LocInfoE loc_760 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_760 ((LocInfoE loc_761 (use{it_layout u32} (LocInfoE loc_762 ((LocInfoE loc_763 (!{void*} (LocInfoE loc_764 ("p")))) at{struct_hyp_page} "order")))) <{IntOp u32, IntOp u32} (LocInfoE loc_765 (use{it_layout u32} (LocInfoE loc_766 ("order")))))))
        then
        locinfo: loc_750 ;
          Goto "#5"
        else
        locinfo: loc_680 ;
          Goto "#6"
      ]> $
      <[ "continue42" :=
        locinfo: loc_681 ;
        Goto "#2"
      ]> $∅
    )%E
  |}.

  (* Definition of function [clear_hyp_page]. *)
  Definition impl_clear_hyp_page (global___hyp_vmemmap global_hyp_physvirt_offset global_clear_page : loc): function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout u64)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_769 ;
        LocInfoE loc_807 ("i") <-{ it_layout u64 }
          LocInfoE loc_808 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_808 (i2v 0 i32))) ;
        locinfo: loc_770 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_798 ;
        if: LocInfoE loc_798 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_798 ((LocInfoE loc_799 (use{it_layout u64} (LocInfoE loc_800 ("i")))) <{IntOp u64, IntOp u64} (LocInfoE loc_801 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_801 ((LocInfoE loc_802 (i2v 1 i32)) <<{IntOp i32, IntOp i32} (LocInfoE loc_803 (UnOp (CastOp $ IntOp i32) (IntOp u32) (LocInfoE loc_803 (use{it_layout u32} (LocInfoE loc_804 ((LocInfoE loc_805 (!{void*} (LocInfoE loc_806 ("p")))) at{struct_hyp_page} "order")))))))))))))
        then
        locinfo: loc_772 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_772 ;
        expr: (LocInfoE loc_772 (Call (LocInfoE loc_777 (global_clear_page)) [@{expr} LocInfoE loc_778 ((LocInfoE loc_779 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_780 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_781 ((LocInfoE loc_782 (UnOp (CastOp $ IntOp u64) (IntOp u64) (LocInfoE loc_783 ((LocInfoE loc_784 (UnOp (CastOp $ IntOp u64) (IntOp ssize_t) (LocInfoE loc_785 ((LocInfoE loc_786 (use{void*} (LocInfoE loc_787 ("p")))) -{PtrOp, PtrOp} (LocInfoE loc_788 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_789 (use{it_layout u64} (LocInfoE loc_790 (global___hyp_vmemmap)))))))))) <<{IntOp u64, IntOp u64} (LocInfoE loc_791 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_791 (i2v 12 i32)))))))) -{IntOp u64, IntOp u64} (LocInfoE loc_792 (UnOp (CastOp $ IntOp u64) (IntOp i64) (LocInfoE loc_792 (use{it_layout i64} (LocInfoE loc_793 (global_hyp_physvirt_offset)))))))))))) at_offset{it_layout u8, PtrOp, IntOp u64} (LocInfoE loc_794 ((LocInfoE loc_795 (use{it_layout u64} (LocInfoE loc_796 ("i")))) <<{IntOp u64, IntOp u64} (LocInfoE loc_797 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_797 (i2v 12 i32))))))) ])) ;
        locinfo: loc_773 ;
        Goto "continue46"
      ]> $
      <[ "#3" :=
        Return (VOID)
      ]> $
      <[ "continue46" :=
        locinfo: loc_774 ;
        LocInfoE loc_775 ("i") <-{ it_layout u64 }
          LocInfoE loc_774 ((LocInfoE loc_774 (use{it_layout u64} (LocInfoE loc_775 ("i")))) +{IntOp u64, IntOp u64} (LocInfoE loc_774 (i2v 1 u64))) ;
        locinfo: loc_770 ;
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
          LocInfoE loc_885 (use{it_layout u32} (LocInfoE loc_886 ("order"))) ;
        locinfo: loc_812 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_869 ;
        if: LocInfoE loc_869 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_869 ((LocInfoE loc_870 (use{it_layout u32} (LocInfoE loc_871 ("i")))) ≤{IntOp u32, IntOp u32} (LocInfoE loc_872 (i2v 11 u32)))))
        then
        Goto "#10"
        else
        locinfo: loc_859 ;
          Goto "#3"
      ]> $
      <[ "#10" :=
        locinfo: loc_873 ;
        if: LocInfoE loc_873 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_873 (Call (LocInfoE loc_875 (global_list_empty)) [@{expr} LocInfoE loc_876 (&(LocInfoE loc_878 ((LocInfoE loc_880 ((LocInfoE loc_881 (!{void*} (LocInfoE loc_882 ("pool")))) at{struct_hyp_pool} "free_area")) at_offset{layout_of struct_list_head, PtrOp, IntOp u32} (LocInfoE loc_883 (use{it_layout u32} (LocInfoE loc_884 ("i"))))))) ])))
        then
        locinfo: loc_864 ;
          Goto "#2"
        else
        locinfo: loc_859 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_864 ;
        LocInfoE loc_867 ("i") <-{ it_layout u32 }
          LocInfoE loc_864 ((LocInfoE loc_864 (use{it_layout u32} (LocInfoE loc_867 ("i")))) +{IntOp u32, IntOp u32} (LocInfoE loc_864 (i2v 1 u32))) ;
        locinfo: loc_865 ;
        Goto "continue49"
      ]> $
      <[ "#3" :=
        locinfo: loc_859 ;
        if: LocInfoE loc_859 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_859 ((LocInfoE loc_860 (use{it_layout u32} (LocInfoE loc_861 ("i")))) >{IntOp u32, IntOp u32} (LocInfoE loc_862 (i2v 11 u32)))))
        then
        locinfo: loc_856 ;
          Goto "#8"
        else
        locinfo: loc_814 ;
          Goto "#9"
      ]> $
      <[ "#4" :=
        locinfo: loc_814 ;
        LocInfoE loc_840 ("p") <-{ void* }
          LocInfoE loc_841 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_842 ((LocInfoE loc_843 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_844 (use{void*} (LocInfoE loc_845 ((LocInfoE loc_846 (&(LocInfoE loc_848 ((LocInfoE loc_850 ((LocInfoE loc_851 (!{void*} (LocInfoE loc_852 ("pool")))) at{struct_hyp_pool} "free_area")) at_offset{layout_of struct_list_head, PtrOp, IntOp u32} (LocInfoE loc_853 (use{it_layout u32} (LocInfoE loc_854 ("i")))))))) at{struct_list_head} "next")))))) at_neg_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_855 ((OffsetOf (struct_hyp_page) ("node"))))))) ;
        locinfo: loc_815 ;
        LocInfoE loc_830 ("p") <-{ void* }
          LocInfoE loc_831 (Call (LocInfoE loc_833 (global___hyp_extract_page)) [@{expr} LocInfoE loc_834 (use{void*} (LocInfoE loc_835 ("pool"))) ;
          LocInfoE loc_836 (use{void*} (LocInfoE loc_837 ("p"))) ;
          LocInfoE loc_838 (use{it_layout u32} (LocInfoE loc_839 ("order"))) ]) ;
        locinfo: loc_826 ;
        if: LocInfoE loc_826 (UnOp (CastOp $ IntOp bool_it) (IntOp u64) (LocInfoE loc_826 ((LocInfoE loc_827 (use{it_layout u64} (LocInfoE loc_828 ("mask")))) &{IntOp u64, IntOp u64} (LocInfoE loc_829 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_829 (i2v 1 i32)))))))
        then
        locinfo: loc_820 ;
          Goto "#6"
        else
        locinfo: loc_817 ;
          Goto "#7"
      ]> $
      <[ "#5" :=
        locinfo: loc_817 ;
        Return (LocInfoE loc_818 (use{void*} (LocInfoE loc_819 ("p"))))
      ]> $
      <[ "#6" :=
        locinfo: loc_820 ;
        expr: (LocInfoE loc_820 (Call (LocInfoE loc_822 (global_clear_hyp_page)) [@{expr} LocInfoE loc_823 (use{void*} (LocInfoE loc_824 ("p"))) ])) ;
        locinfo: loc_817 ;
        Goto "#5"
      ]> $
      <[ "#7" :=
        locinfo: loc_817 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        locinfo: loc_856 ;
        Return (LocInfoE loc_857 (NULL))
      ]> $
      <[ "#9" :=
        locinfo: loc_814 ;
        Goto "#4"
      ]> $
      <[ "continue49" :=
        locinfo: loc_812 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.
End code.
