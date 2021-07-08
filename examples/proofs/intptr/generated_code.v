From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/intptr.c]. *)
Section code.
  Definition file_0 : string := "examples/intptr.c".
  Definition file_1 : string := "include/refinedc.h".
  Definition loc_2 : location_info := LocationInfo file_1 50 2 50 47.
  Definition loc_3 : location_info := LocationInfo file_1 50 9 50 46.
  Definition loc_4 : location_info := LocationInfo file_1 50 9 50 32.
  Definition loc_5 : location_info := LocationInfo file_1 50 33 50 37.
  Definition loc_6 : location_info := LocationInfo file_1 50 33 50 37.
  Definition loc_7 : location_info := LocationInfo file_1 50 39 50 45.
  Definition loc_8 : location_info := LocationInfo file_1 50 39 50 45.
  Definition loc_11 : location_info := LocationInfo file_0 18 2 18 30.
  Definition loc_12 : location_info := LocationInfo file_0 20 2 20 11.
  Definition loc_13 : location_info := LocationInfo file_0 20 9 20 10.
  Definition loc_14 : location_info := LocationInfo file_0 20 9 20 10.
  Definition loc_15 : location_info := LocationInfo file_0 18 16 18 29.
  Definition loc_16 : location_info := LocationInfo file_0 18 28 18 29.
  Definition loc_17 : location_info := LocationInfo file_0 18 28 18 29.
  Definition loc_22 : location_info := LocationInfo file_0 28 2 28 30.
  Definition loc_23 : location_info := LocationInfo file_0 29 2 29 11.
  Definition loc_24 : location_info := LocationInfo file_0 29 9 29 10.
  Definition loc_25 : location_info := LocationInfo file_0 29 9 29 10.
  Definition loc_26 : location_info := LocationInfo file_0 28 16 28 29.
  Definition loc_27 : location_info := LocationInfo file_0 28 28 28 29.
  Definition loc_28 : location_info := LocationInfo file_0 28 28 28 29.
  Definition loc_33 : location_info := LocationInfo file_0 37 2 37 30.
  Definition loc_34 : location_info := LocationInfo file_0 38 2 38 15.
  Definition loc_35 : location_info := LocationInfo file_0 38 9 38 14.
  Definition loc_36 : location_info := LocationInfo file_0 38 9 38 10.
  Definition loc_37 : location_info := LocationInfo file_0 38 9 38 10.
  Definition loc_38 : location_info := LocationInfo file_0 38 13 38 14.
  Definition loc_39 : location_info := LocationInfo file_0 37 16 37 29.
  Definition loc_40 : location_info := LocationInfo file_0 37 28 37 29.
  Definition loc_41 : location_info := LocationInfo file_0 37 28 37 29.
  Definition loc_46 : location_info := LocationInfo file_0 46 2 46 32.
  Definition loc_47 : location_info := LocationInfo file_0 47 2 47 32.
  Definition loc_48 : location_info := LocationInfo file_0 49 2 51 3.
  Definition loc_49 : location_info := LocationInfo file_0 53 2 53 12.
  Definition loc_50 : location_info := LocationInfo file_0 53 9 53 11.
  Definition loc_51 : location_info := LocationInfo file_0 53 9 53 11.
  Definition loc_52 : location_info := LocationInfo file_0 49 14 51 3.
  Definition loc_53 : location_info := LocationInfo file_0 50 4 50 14.
  Definition loc_54 : location_info := LocationInfo file_0 50 11 50 13.
  Definition loc_55 : location_info := LocationInfo file_0 50 11 50 13.
  Definition loc_57 : location_info := LocationInfo file_0 49 5 49 13.
  Definition loc_58 : location_info := LocationInfo file_0 49 5 49 7.
  Definition loc_59 : location_info := LocationInfo file_0 49 5 49 7.
  Definition loc_60 : location_info := LocationInfo file_0 49 11 49 13.
  Definition loc_61 : location_info := LocationInfo file_0 49 11 49 13.
  Definition loc_62 : location_info := LocationInfo file_0 47 17 47 31.
  Definition loc_63 : location_info := LocationInfo file_0 47 29 47 31.
  Definition loc_64 : location_info := LocationInfo file_0 47 29 47 31.
  Definition loc_67 : location_info := LocationInfo file_0 46 17 46 31.
  Definition loc_68 : location_info := LocationInfo file_0 46 29 46 31.
  Definition loc_69 : location_info := LocationInfo file_0 46 29 46 31.
  Definition loc_74 : location_info := LocationInfo file_0 61 2 61 32.
  Definition loc_75 : location_info := LocationInfo file_0 62 2 62 32.
  Definition loc_76 : location_info := LocationInfo file_0 64 2 66 3.
  Definition loc_77 : location_info := LocationInfo file_0 68 2 68 12.
  Definition loc_78 : location_info := LocationInfo file_0 68 9 68 11.
  Definition loc_79 : location_info := LocationInfo file_0 68 9 68 11.
  Definition loc_80 : location_info := LocationInfo file_0 64 14 66 3.
  Definition loc_81 : location_info := LocationInfo file_0 65 4 65 14.
  Definition loc_82 : location_info := LocationInfo file_0 65 11 65 13.
  Definition loc_83 : location_info := LocationInfo file_0 65 11 65 13.
  Definition loc_85 : location_info := LocationInfo file_0 64 5 64 13.
  Definition loc_86 : location_info := LocationInfo file_0 64 5 64 7.
  Definition loc_87 : location_info := LocationInfo file_0 64 5 64 7.
  Definition loc_88 : location_info := LocationInfo file_0 64 11 64 13.
  Definition loc_89 : location_info := LocationInfo file_0 64 11 64 13.
  Definition loc_90 : location_info := LocationInfo file_0 62 17 62 31.
  Definition loc_91 : location_info := LocationInfo file_0 62 29 62 31.
  Definition loc_92 : location_info := LocationInfo file_0 62 29 62 31.
  Definition loc_95 : location_info := LocationInfo file_0 61 17 61 31.
  Definition loc_96 : location_info := LocationInfo file_0 61 29 61 31.
  Definition loc_97 : location_info := LocationInfo file_0 61 29 61 31.
  Definition loc_102 : location_info := LocationInfo file_0 76 2 76 12.
  Definition loc_103 : location_info := LocationInfo file_0 77 2 77 12.
  Definition loc_104 : location_info := LocationInfo file_0 78 2 78 30.
  Definition loc_105 : location_info := LocationInfo file_0 79 2 79 30.
  Definition loc_106 : location_info := LocationInfo file_0 81 2 82 18.
  Definition loc_107 : location_info := LocationInfo file_0 84 2 85 43.
  Definition loc_108 : location_info := LocationInfo file_0 84 13 84 49.
  Definition loc_109 : location_info := LocationInfo file_0 84 15 84 31.
  Definition loc_110 : location_info := LocationInfo file_0 84 32 84 47.
  Definition loc_111 : location_info := LocationInfo file_0 84 39 84 45.
  Definition loc_112 : location_info := LocationInfo file_0 84 39 84 40.
  Definition loc_113 : location_info := LocationInfo file_0 84 39 84 40.
  Definition loc_114 : location_info := LocationInfo file_0 84 44 84 45.
  Definition loc_115 : location_info := LocationInfo file_0 84 22 84 29.
  Definition loc_116 : location_info := LocationInfo file_0 84 22 84 23.
  Definition loc_117 : location_info := LocationInfo file_0 84 22 84 23.
  Definition loc_118 : location_info := LocationInfo file_0 84 27 84 29.
  Definition loc_119 : location_info := LocationInfo file_0 85 7 85 43.
  Definition loc_120 : location_info := LocationInfo file_0 85 9 85 25.
  Definition loc_121 : location_info := LocationInfo file_0 85 26 85 41.
  Definition loc_122 : location_info := LocationInfo file_0 85 33 85 39.
  Definition loc_123 : location_info := LocationInfo file_0 85 33 85 34.
  Definition loc_124 : location_info := LocationInfo file_0 85 33 85 34.
  Definition loc_125 : location_info := LocationInfo file_0 85 38 85 39.
  Definition loc_126 : location_info := LocationInfo file_0 85 16 85 23.
  Definition loc_127 : location_info := LocationInfo file_0 85 16 85 17.
  Definition loc_128 : location_info := LocationInfo file_0 85 16 85 17.
  Definition loc_129 : location_info := LocationInfo file_0 85 21 85 23.
  Definition loc_130 : location_info := LocationInfo file_0 84 6 84 11.
  Definition loc_131 : location_info := LocationInfo file_0 84 6 84 7.
  Definition loc_132 : location_info := LocationInfo file_0 84 6 84 7.
  Definition loc_133 : location_info := LocationInfo file_0 84 10 84 11.
  Definition loc_134 : location_info := LocationInfo file_0 84 10 84 11.
  Definition loc_135 : location_info := LocationInfo file_0 81 13 81 24.
  Definition loc_136 : location_info := LocationInfo file_0 81 15 81 22.
  Definition loc_137 : location_info := LocationInfo file_0 81 15 81 16.
  Definition loc_138 : location_info := LocationInfo file_0 81 19 81 21.
  Definition loc_139 : location_info := LocationInfo file_0 82 7 82 18.
  Definition loc_140 : location_info := LocationInfo file_0 82 9 82 16.
  Definition loc_141 : location_info := LocationInfo file_0 82 9 82 10.
  Definition loc_142 : location_info := LocationInfo file_0 82 13 82 15.
  Definition loc_143 : location_info := LocationInfo file_0 81 6 81 11.
  Definition loc_144 : location_info := LocationInfo file_0 81 6 81 7.
  Definition loc_145 : location_info := LocationInfo file_0 81 6 81 7.
  Definition loc_146 : location_info := LocationInfo file_0 81 10 81 11.
  Definition loc_147 : location_info := LocationInfo file_0 81 10 81 11.
  Definition loc_148 : location_info := LocationInfo file_0 79 16 79 29.
  Definition loc_149 : location_info := LocationInfo file_0 79 27 79 29.
  Definition loc_150 : location_info := LocationInfo file_0 79 28 79 29.
  Definition loc_153 : location_info := LocationInfo file_0 78 16 78 29.
  Definition loc_154 : location_info := LocationInfo file_0 78 27 78 29.
  Definition loc_155 : location_info := LocationInfo file_0 78 28 78 29.
  Definition loc_158 : location_info := LocationInfo file_0 77 10 77 11.
  Definition loc_161 : location_info := LocationInfo file_0 76 10 76 11.
  Definition loc_166 : location_info := LocationInfo file_0 95 2 95 30.
  Definition loc_167 : location_info := LocationInfo file_0 96 2 96 22.
  Definition loc_168 : location_info := LocationInfo file_0 97 2 97 11.
  Definition loc_169 : location_info := LocationInfo file_0 97 9 97 10.
  Definition loc_170 : location_info := LocationInfo file_0 97 9 97 10.
  Definition loc_171 : location_info := LocationInfo file_0 96 12 96 21.
  Definition loc_172 : location_info := LocationInfo file_0 96 20 96 21.
  Definition loc_173 : location_info := LocationInfo file_0 96 20 96 21.
  Definition loc_176 : location_info := LocationInfo file_0 95 16 95 29.
  Definition loc_177 : location_info := LocationInfo file_0 95 28 95 29.
  Definition loc_178 : location_info := LocationInfo file_0 95 28 95 29.
  Definition loc_183 : location_info := LocationInfo file_0 106 2 106 30.
  Definition loc_184 : location_info := LocationInfo file_0 107 2 107 28.
  Definition loc_185 : location_info := LocationInfo file_0 108 2 108 11.
  Definition loc_186 : location_info := LocationInfo file_0 108 9 108 10.
  Definition loc_187 : location_info := LocationInfo file_0 108 9 108 10.
  Definition loc_188 : location_info := LocationInfo file_0 107 12 107 27.
  Definition loc_189 : location_info := LocationInfo file_0 107 20 107 27.
  Definition loc_190 : location_info := LocationInfo file_0 107 21 107 22.
  Definition loc_191 : location_info := LocationInfo file_0 107 21 107 22.
  Definition loc_192 : location_info := LocationInfo file_0 107 25 107 26.
  Definition loc_195 : location_info := LocationInfo file_0 106 16 106 29.
  Definition loc_196 : location_info := LocationInfo file_0 106 28 106 29.
  Definition loc_197 : location_info := LocationInfo file_0 106 28 106 29.
  Definition loc_202 : location_info := LocationInfo file_0 116 2 116 30.
  Definition loc_203 : location_info := LocationInfo file_0 117 2 117 22.
  Definition loc_204 : location_info := LocationInfo file_0 118 2 118 29.
  Definition loc_205 : location_info := LocationInfo file_0 118 9 118 28.
  Definition loc_206 : location_info := LocationInfo file_0 118 9 118 22.
  Definition loc_207 : location_info := LocationInfo file_0 118 9 118 22.
  Definition loc_208 : location_info := LocationInfo file_0 118 23 118 24.
  Definition loc_209 : location_info := LocationInfo file_0 118 23 118 24.
  Definition loc_210 : location_info := LocationInfo file_0 118 26 118 27.
  Definition loc_211 : location_info := LocationInfo file_0 118 26 118 27.
  Definition loc_212 : location_info := LocationInfo file_0 117 16 117 21.
  Definition loc_213 : location_info := LocationInfo file_0 117 16 117 17.
  Definition loc_214 : location_info := LocationInfo file_0 117 16 117 17.
  Definition loc_215 : location_info := LocationInfo file_0 117 20 117 21.
  Definition loc_218 : location_info := LocationInfo file_0 116 16 116 29.
  Definition loc_219 : location_info := LocationInfo file_0 116 28 116 29.
  Definition loc_220 : location_info := LocationInfo file_0 116 28 116 29.
  Definition loc_225 : location_info := LocationInfo file_0 127 2 127 30.
  Definition loc_226 : location_info := LocationInfo file_0 128 2 128 20.
  Definition loc_227 : location_info := LocationInfo file_0 129 2 129 13.
  Definition loc_228 : location_info := LocationInfo file_0 130 2 130 11.
  Definition loc_229 : location_info := LocationInfo file_0 130 9 130 10.
  Definition loc_230 : location_info := LocationInfo file_0 130 9 130 10.
  Definition loc_231 : location_info := LocationInfo file_0 129 10 129 12.
  Definition loc_232 : location_info := LocationInfo file_0 129 10 129 12.
  Definition loc_233 : location_info := LocationInfo file_0 129 11 129 12.
  Definition loc_234 : location_info := LocationInfo file_0 129 11 129 12.
  Definition loc_237 : location_info := LocationInfo file_0 128 11 128 19.
  Definition loc_238 : location_info := LocationInfo file_0 128 18 128 19.
  Definition loc_239 : location_info := LocationInfo file_0 128 18 128 19.
  Definition loc_242 : location_info := LocationInfo file_0 127 16 127 29.
  Definition loc_243 : location_info := LocationInfo file_0 127 28 127 29.
  Definition loc_244 : location_info := LocationInfo file_0 127 28 127 29.
  Definition loc_249 : location_info := LocationInfo file_0 139 2 139 30.
  Definition loc_250 : location_info := LocationInfo file_0 140 2 140 22.
  Definition loc_251 : location_info := LocationInfo file_0 141 2 141 38.
  Definition loc_252 : location_info := LocationInfo file_0 142 2 142 13.
  Definition loc_253 : location_info := LocationInfo file_0 143 2 143 11.
  Definition loc_254 : location_info := LocationInfo file_0 143 9 143 10.
  Definition loc_255 : location_info := LocationInfo file_0 143 9 143 10.
  Definition loc_256 : location_info := LocationInfo file_0 142 10 142 12.
  Definition loc_257 : location_info := LocationInfo file_0 142 10 142 12.
  Definition loc_258 : location_info := LocationInfo file_0 142 11 142 12.
  Definition loc_259 : location_info := LocationInfo file_0 142 11 142 12.
  Definition loc_262 : location_info := LocationInfo file_0 141 11 141 37.
  Definition loc_263 : location_info := LocationInfo file_0 141 18 141 37.
  Definition loc_264 : location_info := LocationInfo file_0 141 18 141 31.
  Definition loc_265 : location_info := LocationInfo file_0 141 18 141 31.
  Definition loc_266 : location_info := LocationInfo file_0 141 32 141 33.
  Definition loc_267 : location_info := LocationInfo file_0 141 32 141 33.
  Definition loc_268 : location_info := LocationInfo file_0 141 35 141 36.
  Definition loc_269 : location_info := LocationInfo file_0 141 35 141 36.
  Definition loc_272 : location_info := LocationInfo file_0 140 16 140 21.
  Definition loc_273 : location_info := LocationInfo file_0 140 16 140 17.
  Definition loc_274 : location_info := LocationInfo file_0 140 16 140 17.
  Definition loc_275 : location_info := LocationInfo file_0 140 20 140 21.
  Definition loc_278 : location_info := LocationInfo file_0 139 16 139 29.
  Definition loc_279 : location_info := LocationInfo file_0 139 28 139 29.
  Definition loc_280 : location_info := LocationInfo file_0 139 28 139 29.
  Definition loc_285 : location_info := LocationInfo file_0 152 2 152 30.
  Definition loc_286 : location_info := LocationInfo file_0 153 2 153 42.
  Definition loc_287 : location_info := LocationInfo file_0 154 2 154 12.
  Definition loc_288 : location_info := LocationInfo file_0 154 9 154 11.
  Definition loc_289 : location_info := LocationInfo file_0 154 9 154 11.
  Definition loc_290 : location_info := LocationInfo file_0 154 10 154 11.
  Definition loc_291 : location_info := LocationInfo file_0 154 10 154 11.
  Definition loc_292 : location_info := LocationInfo file_0 153 11 153 41.
  Definition loc_293 : location_info := LocationInfo file_0 153 18 153 41.
  Definition loc_294 : location_info := LocationInfo file_0 153 18 153 31.
  Definition loc_295 : location_info := LocationInfo file_0 153 18 153 31.
  Definition loc_296 : location_info := LocationInfo file_0 153 32 153 37.
  Definition loc_297 : location_info := LocationInfo file_0 153 32 153 33.
  Definition loc_298 : location_info := LocationInfo file_0 153 32 153 33.
  Definition loc_299 : location_info := LocationInfo file_0 153 36 153 37.
  Definition loc_300 : location_info := LocationInfo file_0 153 39 153 40.
  Definition loc_301 : location_info := LocationInfo file_0 153 39 153 40.
  Definition loc_304 : location_info := LocationInfo file_0 152 16 152 29.
  Definition loc_305 : location_info := LocationInfo file_0 152 28 152 29.
  Definition loc_306 : location_info := LocationInfo file_0 152 28 152 29.
  Definition loc_311 : location_info := LocationInfo file_0 163 2 163 30.
  Definition loc_312 : location_info := LocationInfo file_0 164 2 164 22.
  Definition loc_313 : location_info := LocationInfo file_0 165 2 165 38.
  Definition loc_314 : location_info := LocationInfo file_0 166 2 166 12.
  Definition loc_315 : location_info := LocationInfo file_0 166 9 166 11.
  Definition loc_316 : location_info := LocationInfo file_0 166 9 166 11.
  Definition loc_317 : location_info := LocationInfo file_0 166 10 166 11.
  Definition loc_318 : location_info := LocationInfo file_0 166 10 166 11.
  Definition loc_319 : location_info := LocationInfo file_0 165 11 165 37.
  Definition loc_320 : location_info := LocationInfo file_0 165 18 165 37.
  Definition loc_321 : location_info := LocationInfo file_0 165 18 165 31.
  Definition loc_322 : location_info := LocationInfo file_0 165 18 165 31.
  Definition loc_323 : location_info := LocationInfo file_0 165 32 165 33.
  Definition loc_324 : location_info := LocationInfo file_0 165 32 165 33.
  Definition loc_325 : location_info := LocationInfo file_0 165 35 165 36.
  Definition loc_326 : location_info := LocationInfo file_0 165 35 165 36.
  Definition loc_329 : location_info := LocationInfo file_0 164 16 164 21.
  Definition loc_330 : location_info := LocationInfo file_0 164 16 164 17.
  Definition loc_331 : location_info := LocationInfo file_0 164 16 164 17.
  Definition loc_332 : location_info := LocationInfo file_0 164 20 164 21.
  Definition loc_335 : location_info := LocationInfo file_0 163 16 163 29.
  Definition loc_336 : location_info := LocationInfo file_0 163 28 163 29.
  Definition loc_337 : location_info := LocationInfo file_0 163 28 163 29.
  Definition loc_342 : location_info := LocationInfo file_0 172 2 172 11.
  Definition loc_343 : location_info := LocationInfo file_0 173 2 173 17.
  Definition loc_344 : location_info := LocationInfo file_0 174 2 174 36.
  Definition loc_345 : location_info := LocationInfo file_0 175 2 175 12.
  Definition loc_346 : location_info := LocationInfo file_0 175 9 175 11.
  Definition loc_347 : location_info := LocationInfo file_0 175 9 175 11.
  Definition loc_348 : location_info := LocationInfo file_0 175 10 175 11.
  Definition loc_349 : location_info := LocationInfo file_0 175 10 175 11.
  Definition loc_350 : location_info := LocationInfo file_0 174 11 174 35.
  Definition loc_351 : location_info := LocationInfo file_0 174 11 174 31.
  Definition loc_352 : location_info := LocationInfo file_0 174 17 174 31.
  Definition loc_353 : location_info := LocationInfo file_0 174 29 174 30.
  Definition loc_354 : location_info := LocationInfo file_0 174 29 174 30.
  Definition loc_355 : location_info := LocationInfo file_0 174 34 174 35.
  Definition loc_358 : location_info := LocationInfo file_0 173 11 173 16.
  Definition loc_359 : location_info := LocationInfo file_0 173 11 173 12.
  Definition loc_360 : location_info := LocationInfo file_0 173 11 173 12.
  Definition loc_361 : location_info := LocationInfo file_0 173 15 173 16.
  Definition loc_364 : location_info := LocationInfo file_0 172 2 172 6.
  Definition loc_365 : location_info := LocationInfo file_0 172 2 172 6.
  Definition loc_366 : location_info := LocationInfo file_0 172 2 172 3.
  Definition loc_367 : location_info := LocationInfo file_0 172 2 172 3.
  Definition loc_368 : location_info := LocationInfo file_0 172 4 172 5.
  Definition loc_369 : location_info := LocationInfo file_0 172 9 172 10.
  Definition loc_372 : location_info := LocationInfo file_0 181 2 181 11.
  Definition loc_373 : location_info := LocationInfo file_0 182 2 182 17.
  Definition loc_374 : location_info := LocationInfo file_0 183 2 183 34.
  Definition loc_375 : location_info := LocationInfo file_0 184 2 184 43.
  Definition loc_376 : location_info := LocationInfo file_0 185 2 185 12.
  Definition loc_377 : location_info := LocationInfo file_0 185 9 185 11.
  Definition loc_378 : location_info := LocationInfo file_0 185 9 185 11.
  Definition loc_379 : location_info := LocationInfo file_0 185 10 185 11.
  Definition loc_380 : location_info := LocationInfo file_0 185 10 185 11.
  Definition loc_381 : location_info := LocationInfo file_0 184 11 184 42.
  Definition loc_382 : location_info := LocationInfo file_0 184 11 184 38.
  Definition loc_383 : location_info := LocationInfo file_0 184 17 184 38.
  Definition loc_384 : location_info := LocationInfo file_0 184 17 184 30.
  Definition loc_385 : location_info := LocationInfo file_0 184 17 184 30.
  Definition loc_386 : location_info := LocationInfo file_0 184 31 184 33.
  Definition loc_387 : location_info := LocationInfo file_0 184 31 184 33.
  Definition loc_388 : location_info := LocationInfo file_0 184 35 184 37.
  Definition loc_389 : location_info := LocationInfo file_0 184 36 184 37.
  Definition loc_390 : location_info := LocationInfo file_0 184 41 184 42.
  Definition loc_393 : location_info := LocationInfo file_0 183 17 183 33.
  Definition loc_394 : location_info := LocationInfo file_0 183 17 183 29.
  Definition loc_395 : location_info := LocationInfo file_0 183 28 183 29.
  Definition loc_396 : location_info := LocationInfo file_0 183 28 183 29.
  Definition loc_397 : location_info := LocationInfo file_0 183 32 183 33.
  Definition loc_400 : location_info := LocationInfo file_0 182 11 182 16.
  Definition loc_401 : location_info := LocationInfo file_0 182 11 182 12.
  Definition loc_402 : location_info := LocationInfo file_0 182 11 182 12.
  Definition loc_403 : location_info := LocationInfo file_0 182 15 182 16.
  Definition loc_406 : location_info := LocationInfo file_0 181 2 181 6.
  Definition loc_407 : location_info := LocationInfo file_0 181 2 181 6.
  Definition loc_408 : location_info := LocationInfo file_0 181 2 181 3.
  Definition loc_409 : location_info := LocationInfo file_0 181 2 181 3.
  Definition loc_410 : location_info := LocationInfo file_0 181 4 181 5.
  Definition loc_411 : location_info := LocationInfo file_0 181 9 181 10.
  Definition loc_414 : location_info := LocationInfo file_0 192 2 192 30.
  Definition loc_415 : location_info := LocationInfo file_0 192 9 192 29.
  Definition loc_416 : location_info := LocationInfo file_0 192 15 192 29.

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
        Return (LocInfoE loc_3 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_5 (use{it_layout uintptr_t} (LocInfoE loc_6 ("to")))) (LocInfoE loc_7 (use{void*} (LocInfoE loc_8 ("from"))))))
      ]> $∅
    )%E
  |}.

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
          LocInfoE loc_15 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_16 (use{void*} (LocInfoE loc_17 ("p"))))) ;
        locinfo: loc_12 ;
        Return (LocInfoE loc_13 (use{it_layout uintptr_t} (LocInfoE loc_14 ("i"))))
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
          LocInfoE loc_26 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_27 (use{void*} (LocInfoE loc_28 ("p"))))) ;
        locinfo: loc_23 ;
        Return (LocInfoE loc_24 (use{it_layout uintptr_t} (LocInfoE loc_25 ("i"))))
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
          LocInfoE loc_39 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_40 (use{void*} (LocInfoE loc_41 ("p"))))) ;
        locinfo: loc_34 ;
        Return (LocInfoE loc_35 ((LocInfoE loc_36 (use{it_layout uintptr_t} (LocInfoE loc_37 ("i")))) +{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_38 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_38 (i2v 0 i32))))))
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
          LocInfoE loc_67 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_68 (use{void*} (LocInfoE loc_69 ("p1"))))) ;
        "i2" <-{ it_layout uintptr_t }
          LocInfoE loc_62 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_63 (use{void*} (LocInfoE loc_64 ("p2"))))) ;
        locinfo: loc_57 ;
        if: LocInfoE loc_57 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_57 ((LocInfoE loc_58 (use{it_layout uintptr_t} (LocInfoE loc_59 ("i1")))) ≤{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_60 (use{it_layout uintptr_t} (LocInfoE loc_61 ("i2")))))))
        then
        locinfo: loc_53 ;
          Goto "#2"
        else
        locinfo: loc_49 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_49 ;
        Return (LocInfoE loc_50 (use{it_layout uintptr_t} (LocInfoE loc_51 ("i2"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_53 ;
        Return (LocInfoE loc_54 (use{it_layout uintptr_t} (LocInfoE loc_55 ("i1"))))
      ]> $
      <[ "#3" :=
        locinfo: loc_49 ;
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
          LocInfoE loc_95 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_96 (use{void*} (LocInfoE loc_97 ("p1"))))) ;
        "i2" <-{ it_layout uintptr_t }
          LocInfoE loc_90 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_91 (use{void*} (LocInfoE loc_92 ("p2"))))) ;
        locinfo: loc_85 ;
        if: LocInfoE loc_85 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_85 ((LocInfoE loc_86 (use{it_layout uintptr_t} (LocInfoE loc_87 ("i1")))) ≤{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_88 (use{it_layout uintptr_t} (LocInfoE loc_89 ("i2")))))))
        then
        locinfo: loc_81 ;
          Goto "#2"
        else
        locinfo: loc_77 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_77 ;
        Return (LocInfoE loc_78 (use{it_layout uintptr_t} (LocInfoE loc_79 ("i2"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_81 ;
        Return (LocInfoE loc_82 (use{it_layout uintptr_t} (LocInfoE loc_83 ("i1"))))
      ]> $
      <[ "#3" :=
        locinfo: loc_77 ;
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
        "x" <-{ it_layout i32 } LocInfoE loc_161 (i2v 0 i32) ;
        "y" <-{ it_layout i32 } LocInfoE loc_158 (i2v 0 i32) ;
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_153 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_154 (&(LocInfoE loc_155 ("x"))))) ;
        "j" <-{ it_layout uintptr_t }
          LocInfoE loc_148 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_149 (&(LocInfoE loc_150 ("y"))))) ;
        locinfo: loc_143 ;
        if: LocInfoE loc_143 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_143 ((LocInfoE loc_144 (use{it_layout uintptr_t} (LocInfoE loc_145 ("i")))) <{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_146 (use{it_layout uintptr_t} (LocInfoE loc_147 ("j")))))))
        then
        locinfo: loc_136 ;
          Goto "#4"
        else
        locinfo: loc_140 ;
          Goto "#5"
      ]> $
      <[ "#1" :=
        locinfo: loc_130 ;
        if: LocInfoE loc_130 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_130 ((LocInfoE loc_131 (use{it_layout uintptr_t} (LocInfoE loc_132 ("i")))) <{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_133 (use{it_layout uintptr_t} (LocInfoE loc_134 ("j")))))))
        then
        locinfo: loc_109 ;
          Goto "#2"
        else
        locinfo: loc_120 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_109 ;
        assert: (LocInfoE loc_115 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_115 ((LocInfoE loc_116 (use{it_layout i32} (LocInfoE loc_117 ("y")))) ={IntOp i32, IntOp i32} (LocInfoE loc_118 (i2v 10 i32)))))) ;
        locinfo: loc_110 ;
        assert: (LocInfoE loc_111 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_111 ((LocInfoE loc_112 (use{it_layout i32} (LocInfoE loc_113 ("x")))) ={IntOp i32, IntOp i32} (LocInfoE loc_114 (i2v 0 i32)))))) ;
        Return (VOID)
      ]> $
      <[ "#3" :=
        locinfo: loc_120 ;
        assert: (LocInfoE loc_126 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_126 ((LocInfoE loc_127 (use{it_layout i32} (LocInfoE loc_128 ("x")))) ={IntOp i32, IntOp i32} (LocInfoE loc_129 (i2v 10 i32)))))) ;
        locinfo: loc_121 ;
        assert: (LocInfoE loc_122 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_122 ((LocInfoE loc_123 (use{it_layout i32} (LocInfoE loc_124 ("y")))) ={IntOp i32, IntOp i32} (LocInfoE loc_125 (i2v 0 i32)))))) ;
        Return (VOID)
      ]> $
      <[ "#4" :=
        locinfo: loc_136 ;
        LocInfoE loc_137 ("y") <-{ it_layout i32 }
          LocInfoE loc_138 (i2v 10 i32) ;
        locinfo: loc_130 ;
        Goto "#1"
      ]> $
      <[ "#5" :=
        locinfo: loc_140 ;
        LocInfoE loc_141 ("x") <-{ it_layout i32 }
          LocInfoE loc_142 (i2v 10 i32) ;
        locinfo: loc_130 ;
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
          LocInfoE loc_176 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_177 (use{void*} (LocInfoE loc_178 ("p"))))) ;
        "q" <-{ void* }
          LocInfoE loc_171 (UnOp (CastOp $ PtrOp) (IntOp uintptr_t) (LocInfoE loc_172 (use{it_layout uintptr_t} (LocInfoE loc_173 ("i"))))) ;
        locinfo: loc_168 ;
        Return (LocInfoE loc_169 (use{void*} (LocInfoE loc_170 ("q"))))
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
          LocInfoE loc_195 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_196 (use{void*} (LocInfoE loc_197 ("p"))))) ;
        "q" <-{ void* }
          LocInfoE loc_188 (UnOp (CastOp $ PtrOp) (IntOp uintptr_t) (LocInfoE loc_189 ((LocInfoE loc_190 (use{it_layout uintptr_t} (LocInfoE loc_191 ("i")))) +{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_192 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_192 (i2v 0 i32))))))) ;
        locinfo: loc_185 ;
        Return (LocInfoE loc_186 (use{void*} (LocInfoE loc_187 ("q"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip3]. *)
  Definition impl_roundtrip3 (global_copy_alloc_id : loc): function := {|
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
          LocInfoE loc_218 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_219 (use{void*} (LocInfoE loc_220 ("p"))))) ;
        "k" <-{ it_layout uintptr_t }
          LocInfoE loc_212 ((LocInfoE loc_213 (use{it_layout uintptr_t} (LocInfoE loc_214 ("i")))) +{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_215 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_215 (i2v 0 i32))))) ;
        locinfo: loc_204 ;
        Return (LocInfoE loc_205 (Call (LocInfoE loc_207 (global_copy_alloc_id)) [@{expr} LocInfoE loc_208 (use{it_layout uintptr_t} (LocInfoE loc_209 ("k"))) ;
               LocInfoE loc_210 (use{void*} (LocInfoE loc_211 ("p"))) ]))
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
          LocInfoE loc_242 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_243 (use{void*} (LocInfoE loc_244 ("p"))))) ;
        "q" <-{ void* }
          LocInfoE loc_237 (UnOp (CastOp $ PtrOp) (IntOp uintptr_t) (LocInfoE loc_238 (use{it_layout uintptr_t} (LocInfoE loc_239 ("i"))))) ;
        "r" <-{ it_layout i32 }
          LocInfoE loc_231 (use{it_layout i32} (LocInfoE loc_233 (!{void*} (LocInfoE loc_234 ("q"))))) ;
        locinfo: loc_228 ;
        Return (LocInfoE loc_229 (use{it_layout i32} (LocInfoE loc_230 ("r"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip_and_read2]. *)
  Definition impl_roundtrip_and_read2 (global_copy_alloc_id : loc): function := {|
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
          LocInfoE loc_278 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_279 (use{void*} (LocInfoE loc_280 ("p"))))) ;
        "j" <-{ it_layout uintptr_t }
          LocInfoE loc_272 ((LocInfoE loc_273 (use{it_layout uintptr_t} (LocInfoE loc_274 ("i")))) ×{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_275 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_275 (i2v 1 i32))))) ;
        "q" <-{ void* }
          LocInfoE loc_262 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_263 (Call (LocInfoE loc_265 (global_copy_alloc_id)) [@{expr} LocInfoE loc_266 (use{it_layout uintptr_t} (LocInfoE loc_267 ("j"))) ;
          LocInfoE loc_268 (use{void*} (LocInfoE loc_269 ("p"))) ]))) ;
        "r" <-{ it_layout i32 }
          LocInfoE loc_256 (use{it_layout i32} (LocInfoE loc_258 (!{void*} (LocInfoE loc_259 ("q"))))) ;
        locinfo: loc_253 ;
        Return (LocInfoE loc_254 (use{it_layout i32} (LocInfoE loc_255 ("r"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip_and_read3]. *)
  Definition impl_roundtrip_and_read3 (global_copy_alloc_id : loc): function := {|
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
          LocInfoE loc_304 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_305 (use{void*} (LocInfoE loc_306 ("p"))))) ;
        "q" <-{ void* }
          LocInfoE loc_292 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_293 (Call (LocInfoE loc_295 (global_copy_alloc_id)) [@{expr} LocInfoE loc_296 ((LocInfoE loc_297 (use{it_layout uintptr_t} (LocInfoE loc_298 ("i")))) ×{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_299 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_299 (i2v 1 i32))))) ;
          LocInfoE loc_300 (use{void*} (LocInfoE loc_301 ("p"))) ]))) ;
        locinfo: loc_287 ;
        Return (LocInfoE loc_288 (use{it_layout i32} (LocInfoE loc_290 (!{void*} (LocInfoE loc_291 ("q"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip_and_read4]. *)
  Definition impl_roundtrip_and_read4 (global_copy_alloc_id : loc): function := {|
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
          LocInfoE loc_335 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_336 (use{void*} (LocInfoE loc_337 ("p"))))) ;
        "j" <-{ it_layout uintptr_t }
          LocInfoE loc_329 ((LocInfoE loc_330 (use{it_layout uintptr_t} (LocInfoE loc_331 ("i")))) ×{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_332 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_332 (i2v 1 i32))))) ;
        "q" <-{ void* }
          LocInfoE loc_319 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_320 (Call (LocInfoE loc_322 (global_copy_alloc_id)) [@{expr} LocInfoE loc_323 (use{it_layout uintptr_t} (LocInfoE loc_324 ("j"))) ;
          LocInfoE loc_325 (use{void*} (LocInfoE loc_326 ("p"))) ]))) ;
        locinfo: loc_314 ;
        Return (LocInfoE loc_315 (use{it_layout i32} (LocInfoE loc_317 (!{void*} (LocInfoE loc_318 ("q"))))))
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
        locinfo: loc_342 ;
        LocInfoE loc_365 ((LocInfoE loc_367 ("x")) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_368 (i2v 0 i32))) <-{ it_layout i32 }
          LocInfoE loc_369 (i2v 0 i32) ;
        "p" <-{ void* }
          LocInfoE loc_358 ((LocInfoE loc_359 (&(LocInfoE loc_360 ("x")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_361 (i2v 1 i32))) ;
        "q" <-{ void* }
          LocInfoE loc_350 ((LocInfoE loc_351 (UnOp (CastOp $ PtrOp) (IntOp uintptr_t) (LocInfoE loc_352 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_353 (use{void*} (LocInfoE loc_354 ("p")))))))) at_neg_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_355 (i2v 1 i32))) ;
        locinfo: loc_345 ;
        Return (LocInfoE loc_346 (use{it_layout i32} (LocInfoE loc_348 (!{void*} (LocInfoE loc_349 ("q"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip_and_read_past_the_end_copy_alloc_id]. *)
  Definition impl_roundtrip_and_read_past_the_end_copy_alloc_id (global_copy_alloc_id : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
      ("x", mk_array_layout (it_layout i32) 1);
      ("q", void*);
      ("p", void*);
      ("pi", it_layout uintptr_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_372 ;
        LocInfoE loc_407 ((LocInfoE loc_409 ("x")) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_410 (i2v 0 i32))) <-{ it_layout i32 }
          LocInfoE loc_411 (i2v 0 i32) ;
        "p" <-{ void* }
          LocInfoE loc_400 ((LocInfoE loc_401 (&(LocInfoE loc_402 ("x")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_403 (i2v 1 i32))) ;
        "pi" <-{ it_layout uintptr_t }
          LocInfoE loc_393 ((LocInfoE loc_394 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_395 (use{void*} (LocInfoE loc_396 ("p")))))) +{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_397 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_397 (i2v 0 i32))))) ;
        "q" <-{ void* }
          LocInfoE loc_381 ((LocInfoE loc_382 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_383 (Call (LocInfoE loc_385 (global_copy_alloc_id)) [@{expr} LocInfoE loc_386 (use{it_layout uintptr_t} (LocInfoE loc_387 ("pi"))) ;
          LocInfoE loc_388 (&(LocInfoE loc_389 ("x"))) ])))) at_neg_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_390 (i2v 1 i32))) ;
        locinfo: loc_376 ;
        Return (LocInfoE loc_377 (use{it_layout i32} (LocInfoE loc_379 (!{void*} (LocInfoE loc_380 ("q"))))))
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
        locinfo: loc_414 ;
        Return (LocInfoE loc_415 (UnOp (CastOp $ IntOp i32) (PtrOp) (LocInfoE loc_416 (NULL))))
      ]> $∅
    )%E
  |}.
End code.
