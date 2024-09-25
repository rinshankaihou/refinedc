From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/scheduler/src/fdsched.c]. *)
Section code.
  Definition file_0 : string := "include/assume.h".
  Definition file_1 : string := "include/refinedc_malloc.h".
  Definition file_2 : string := "examples/scheduler/include/fdsched/scheduler.h".
  Definition file_3 : string := "examples/scheduler/include/fdsched/priority.h".
  Definition file_4 : string := "examples/scheduler/include/fdsched/message.h".
  Definition file_5 : string := "examples/scheduler/src/fdsched.c".
  Definition loc_2 : location_info := LocationInfo file_4 67 2 67 29.
  Definition loc_3 : location_info := LocationInfo file_4 68 2 68 17.
  Definition loc_4 : location_info := LocationInfo file_4 69 2 69 23.
  Definition loc_5 : location_info := LocationInfo file_4 69 2 69 9.
  Definition loc_6 : location_info := LocationInfo file_4 69 2 69 3.
  Definition loc_7 : location_info := LocationInfo file_4 69 2 69 3.
  Definition loc_8 : location_info := LocationInfo file_4 69 12 69 22.
  Definition loc_9 : location_info := LocationInfo file_4 69 13 69 22.
  Definition loc_10 : location_info := LocationInfo file_4 69 13 69 16.
  Definition loc_11 : location_info := LocationInfo file_4 69 13 69 16.
  Definition loc_12 : location_info := LocationInfo file_4 68 2 68 10.
  Definition loc_13 : location_info := LocationInfo file_4 68 3 68 10.
  Definition loc_14 : location_info := LocationInfo file_4 68 3 68 10.
  Definition loc_15 : location_info := LocationInfo file_4 68 3 68 4.
  Definition loc_16 : location_info := LocationInfo file_4 68 3 68 4.
  Definition loc_17 : location_info := LocationInfo file_4 68 13 68 16.
  Definition loc_18 : location_info := LocationInfo file_4 68 13 68 16.
  Definition loc_19 : location_info := LocationInfo file_4 67 2 67 11.
  Definition loc_20 : location_info := LocationInfo file_4 67 2 67 5.
  Definition loc_21 : location_info := LocationInfo file_4 67 2 67 5.
  Definition loc_22 : location_info := LocationInfo file_4 67 14 67 28.
  Definition loc_25 : location_info := LocationInfo file_4 80 2 80 36.
  Definition loc_26 : location_info := LocationInfo file_4 80 9 80 35.
  Definition loc_27 : location_info := LocationInfo file_4 80 9 80 17.
  Definition loc_28 : location_info := LocationInfo file_4 80 9 80 17.
  Definition loc_29 : location_info := LocationInfo file_4 80 9 80 10.
  Definition loc_30 : location_info := LocationInfo file_4 80 9 80 10.
  Definition loc_31 : location_info := LocationInfo file_4 80 21 80 35.
  Definition loc_34 : location_info := LocationInfo file_4 91 2 91 34.
  Definition loc_35 : location_info := LocationInfo file_4 93 2 93 34.
  Definition loc_36 : location_info := LocationInfo file_4 96 2 102 3.
  Definition loc_37 : location_info := LocationInfo file_4 103 2 103 14.
  Definition loc_38 : location_info := LocationInfo file_4 103 9 103 13.
  Definition loc_39 : location_info := LocationInfo file_4 103 9 103 13.
  Definition loc_40 : location_info := LocationInfo file_4 96 36 100 3.
  Definition loc_41 : location_info := LocationInfo file_4 98 4 98 30.
  Definition loc_42 : location_info := LocationInfo file_4 99 4 99 24.
  Definition loc_43 : location_info := LocationInfo file_4 99 4 99 11.
  Definition loc_44 : location_info := LocationInfo file_4 99 4 99 5.
  Definition loc_45 : location_info := LocationInfo file_4 99 4 99 5.
  Definition loc_46 : location_info := LocationInfo file_4 99 14 99 23.
  Definition loc_47 : location_info := LocationInfo file_4 99 15 99 23.
  Definition loc_48 : location_info := LocationInfo file_4 99 15 99 16.
  Definition loc_49 : location_info := LocationInfo file_4 99 15 99 16.
  Definition loc_50 : location_info := LocationInfo file_4 98 4 98 12.
  Definition loc_51 : location_info := LocationInfo file_4 98 4 98 5.
  Definition loc_52 : location_info := LocationInfo file_4 98 4 98 5.
  Definition loc_53 : location_info := LocationInfo file_4 98 15 98 29.
  Definition loc_54 : location_info := LocationInfo file_4 100 9 102 3.
  Definition loc_55 : location_info := LocationInfo file_4 101 4 101 26.
  Definition loc_56 : location_info := LocationInfo file_4 101 4 101 12.
  Definition loc_57 : location_info := LocationInfo file_4 101 4 101 5.
  Definition loc_58 : location_info := LocationInfo file_4 101 4 101 5.
  Definition loc_59 : location_info := LocationInfo file_4 101 15 101 25.
  Definition loc_60 : location_info := LocationInfo file_4 101 15 101 25.
  Definition loc_61 : location_info := LocationInfo file_4 101 15 101 19.
  Definition loc_62 : location_info := LocationInfo file_4 101 15 101 19.
  Definition loc_63 : location_info := LocationInfo file_4 96 6 96 34.
  Definition loc_64 : location_info := LocationInfo file_4 96 6 96 16.
  Definition loc_65 : location_info := LocationInfo file_4 96 6 96 16.
  Definition loc_66 : location_info := LocationInfo file_4 96 6 96 10.
  Definition loc_67 : location_info := LocationInfo file_4 96 6 96 10.
  Definition loc_68 : location_info := LocationInfo file_4 96 20 96 34.
  Definition loc_69 : location_info := LocationInfo file_4 93 25 93 33.
  Definition loc_70 : location_info := LocationInfo file_4 93 25 93 33.
  Definition loc_71 : location_info := LocationInfo file_4 93 25 93 26.
  Definition loc_72 : location_info := LocationInfo file_4 93 25 93 26.
  Definition loc_75 : location_info := LocationInfo file_4 91 9 91 32.
  Definition loc_77 : location_info := LocationInfo file_4 91 10 91 32.
  Definition loc_78 : location_info := LocationInfo file_4 91 10 91 29.
  Definition loc_79 : location_info := LocationInfo file_4 91 10 91 29.
  Definition loc_80 : location_info := LocationInfo file_4 91 30 91 31.
  Definition loc_81 : location_info := LocationInfo file_4 91 30 91 31.
  Definition loc_84 : location_info := LocationInfo file_3 44 2 46 3.
  Definition loc_85 : location_info := LocationInfo file_3 44 2 46 3.
  Definition loc_86 : location_info := LocationInfo file_3 44 2 46 3.
  Definition loc_87 : location_info := LocationInfo file_3 44 38 46 3.
  Definition loc_88 : location_info := LocationInfo file_3 45 4 45 22.
  Definition loc_89 : location_info := LocationInfo file_3 44 2 46 3.
  Definition loc_91 : location_info := LocationInfo file_3 44 28 44 31.
  Definition loc_92 : location_info := LocationInfo file_3 44 28 44 36.
  Definition loc_93 : location_info := LocationInfo file_3 44 28 44 31.
  Definition loc_94 : location_info := LocationInfo file_3 44 28 44 31.
  Definition loc_95 : location_info := LocationInfo file_3 44 35 44 36.
  Definition loc_96 : location_info := LocationInfo file_3 45 4 45 17.
  Definition loc_97 : location_info := LocationInfo file_3 45 4 45 17.
  Definition loc_98 : location_info := LocationInfo file_3 45 4 45 12.
  Definition loc_99 : location_info := LocationInfo file_3 45 4 45 12.
  Definition loc_100 : location_info := LocationInfo file_3 45 4 45 6.
  Definition loc_101 : location_info := LocationInfo file_3 45 4 45 6.
  Definition loc_102 : location_info := LocationInfo file_3 45 13 45 16.
  Definition loc_103 : location_info := LocationInfo file_3 45 13 45 16.
  Definition loc_104 : location_info := LocationInfo file_3 45 20 45 21.
  Definition loc_105 : location_info := LocationInfo file_3 44 19 44 26.
  Definition loc_106 : location_info := LocationInfo file_3 44 19 44 22.
  Definition loc_107 : location_info := LocationInfo file_3 44 19 44 22.
  Definition loc_108 : location_info := LocationInfo file_3 44 25 44 26.
  Definition loc_109 : location_info := LocationInfo file_3 44 16 44 17.
  Definition loc_114 : location_info := LocationInfo file_3 62 2 62 18.
  Definition loc_115 : location_info := LocationInfo file_3 69 2 76 3.
  Definition loc_116 : location_info := LocationInfo file_3 69 2 76 3.
  Definition loc_117 : location_info := LocationInfo file_3 69 2 76 3.
  Definition loc_118 : location_info := LocationInfo file_3 77 2 77 12.
  Definition loc_119 : location_info := LocationInfo file_3 77 9 77 11.
  Definition loc_120 : location_info := LocationInfo file_3 77 10 77 11.
  Definition loc_121 : location_info := LocationInfo file_3 69 30 76 3.
  Definition loc_122 : location_info := LocationInfo file_3 70 4 70 49.
  Definition loc_123 : location_info := LocationInfo file_3 71 4 75 5.
  Definition loc_124 : location_info := LocationInfo file_3 69 2 76 3.
  Definition loc_126 : location_info := LocationInfo file_3 69 25 69 26.
  Definition loc_127 : location_info := LocationInfo file_3 71 19 73 5.
  Definition loc_128 : location_info := LocationInfo file_3 72 6 72 32.
  Definition loc_129 : location_info := LocationInfo file_3 72 13 72 31.
  Definition loc_130 : location_info := LocationInfo file_3 72 13 72 22.
  Definition loc_131 : location_info := LocationInfo file_3 72 13 72 22.
  Definition loc_132 : location_info := LocationInfo file_3 72 25 72 31.
  Definition loc_133 : location_info := LocationInfo file_3 72 25 72 31.
  Definition loc_134 : location_info := LocationInfo file_3 73 11 75 5.
  Definition loc_135 : location_info := LocationInfo file_3 74 6 74 19.
  Definition loc_136 : location_info := LocationInfo file_3 74 6 74 12.
  Definition loc_137 : location_info := LocationInfo file_3 74 6 74 18.
  Definition loc_138 : location_info := LocationInfo file_3 74 6 74 12.
  Definition loc_139 : location_info := LocationInfo file_3 74 6 74 12.
  Definition loc_140 : location_info := LocationInfo file_3 74 16 74 18.
  Definition loc_141 : location_info := LocationInfo file_3 71 8 71 17.
  Definition loc_142 : location_info := LocationInfo file_3 71 8 71 17.
  Definition loc_143 : location_info := LocationInfo file_3 70 20 70 48.
  Definition loc_144 : location_info := LocationInfo file_3 70 20 70 35.
  Definition loc_145 : location_info := LocationInfo file_3 70 20 70 35.
  Definition loc_146 : location_info := LocationInfo file_3 70 36 70 47.
  Definition loc_147 : location_info := LocationInfo file_3 70 36 70 47.
  Definition loc_148 : location_info := LocationInfo file_3 70 36 70 47.
  Definition loc_149 : location_info := LocationInfo file_3 70 36 70 44.
  Definition loc_150 : location_info := LocationInfo file_3 70 36 70 44.
  Definition loc_151 : location_info := LocationInfo file_3 70 36 70 38.
  Definition loc_152 : location_info := LocationInfo file_3 70 36 70 38.
  Definition loc_153 : location_info := LocationInfo file_3 70 45 70 46.
  Definition loc_154 : location_info := LocationInfo file_3 70 45 70 46.
  Definition loc_157 : location_info := LocationInfo file_3 69 18 69 23.
  Definition loc_158 : location_info := LocationInfo file_3 69 18 69 19.
  Definition loc_159 : location_info := LocationInfo file_3 69 18 69 19.
  Definition loc_160 : location_info := LocationInfo file_3 69 22 69 23.
  Definition loc_161 : location_info := LocationInfo file_3 69 15 69 16.
  Definition loc_164 : location_info := LocationInfo file_3 62 15 62 17.
  Definition loc_165 : location_info := LocationInfo file_3 62 16 62 17.
  Definition loc_170 : location_info := LocationInfo file_3 86 2 86 20.
  Definition loc_171 : location_info := LocationInfo file_3 86 9 86 19.
  Definition loc_172 : location_info := LocationInfo file_3 86 9 86 15.
  Definition loc_173 : location_info := LocationInfo file_3 86 9 86 15.
  Definition loc_174 : location_info := LocationInfo file_3 86 18 86 19.
  Definition loc_177 : location_info := LocationInfo file_3 99 2 99 27.
  Definition loc_178 : location_info := LocationInfo file_3 100 2 100 26.
  Definition loc_179 : location_info := LocationInfo file_3 101 2 101 44.
  Definition loc_180 : location_info := LocationInfo file_3 101 2 101 16.
  Definition loc_181 : location_info := LocationInfo file_3 101 2 101 16.
  Definition loc_182 : location_info := LocationInfo file_3 101 2 101 10.
  Definition loc_183 : location_info := LocationInfo file_3 101 2 101 10.
  Definition loc_184 : location_info := LocationInfo file_3 101 2 101 4.
  Definition loc_185 : location_info := LocationInfo file_3 101 2 101 4.
  Definition loc_186 : location_info := LocationInfo file_3 101 11 101 15.
  Definition loc_187 : location_info := LocationInfo file_3 101 11 101 15.
  Definition loc_188 : location_info := LocationInfo file_3 101 2 101 43.
  Definition loc_189 : location_info := LocationInfo file_3 101 2 101 16.
  Definition loc_190 : location_info := LocationInfo file_3 101 2 101 16.
  Definition loc_191 : location_info := LocationInfo file_3 101 2 101 16.
  Definition loc_192 : location_info := LocationInfo file_3 101 2 101 10.
  Definition loc_193 : location_info := LocationInfo file_3 101 2 101 10.
  Definition loc_194 : location_info := LocationInfo file_3 101 2 101 4.
  Definition loc_195 : location_info := LocationInfo file_3 101 2 101 4.
  Definition loc_196 : location_info := LocationInfo file_3 101 11 101 15.
  Definition loc_197 : location_info := LocationInfo file_3 101 11 101 15.
  Definition loc_198 : location_info := LocationInfo file_3 101 20 101 43.
  Definition loc_199 : location_info := LocationInfo file_3 101 21 101 35.
  Definition loc_200 : location_info := LocationInfo file_3 101 33 101 34.
  Definition loc_201 : location_info := LocationInfo file_3 101 39 101 42.
  Definition loc_202 : location_info := LocationInfo file_3 101 39 101 42.
  Definition loc_203 : location_info := LocationInfo file_3 100 16 100 25.
  Definition loc_204 : location_info := LocationInfo file_3 100 16 100 20.
  Definition loc_205 : location_info := LocationInfo file_3 100 16 100 20.
  Definition loc_206 : location_info := LocationInfo file_3 100 23 100 25.
  Definition loc_209 : location_info := LocationInfo file_3 99 17 99 26.
  Definition loc_210 : location_info := LocationInfo file_3 99 17 99 21.
  Definition loc_211 : location_info := LocationInfo file_3 99 17 99 21.
  Definition loc_212 : location_info := LocationInfo file_3 99 24 99 26.
  Definition loc_217 : location_info := LocationInfo file_3 114 2 114 27.
  Definition loc_218 : location_info := LocationInfo file_3 115 2 115 26.
  Definition loc_219 : location_info := LocationInfo file_3 116 2 116 45.
  Definition loc_220 : location_info := LocationInfo file_3 116 2 116 16.
  Definition loc_221 : location_info := LocationInfo file_3 116 2 116 16.
  Definition loc_222 : location_info := LocationInfo file_3 116 2 116 10.
  Definition loc_223 : location_info := LocationInfo file_3 116 2 116 10.
  Definition loc_224 : location_info := LocationInfo file_3 116 2 116 4.
  Definition loc_225 : location_info := LocationInfo file_3 116 2 116 4.
  Definition loc_226 : location_info := LocationInfo file_3 116 11 116 15.
  Definition loc_227 : location_info := LocationInfo file_3 116 11 116 15.
  Definition loc_228 : location_info := LocationInfo file_3 116 2 116 44.
  Definition loc_229 : location_info := LocationInfo file_3 116 2 116 16.
  Definition loc_230 : location_info := LocationInfo file_3 116 2 116 16.
  Definition loc_231 : location_info := LocationInfo file_3 116 2 116 16.
  Definition loc_232 : location_info := LocationInfo file_3 116 2 116 10.
  Definition loc_233 : location_info := LocationInfo file_3 116 2 116 10.
  Definition loc_234 : location_info := LocationInfo file_3 116 2 116 4.
  Definition loc_235 : location_info := LocationInfo file_3 116 2 116 4.
  Definition loc_236 : location_info := LocationInfo file_3 116 11 116 15.
  Definition loc_237 : location_info := LocationInfo file_3 116 11 116 15.
  Definition loc_238 : location_info := LocationInfo file_3 116 20 116 44.
  Definition loc_239 : location_info := LocationInfo file_3 116 21 116 44.
  Definition loc_240 : location_info := LocationInfo file_3 116 22 116 36.
  Definition loc_241 : location_info := LocationInfo file_3 116 34 116 35.
  Definition loc_242 : location_info := LocationInfo file_3 116 40 116 43.
  Definition loc_243 : location_info := LocationInfo file_3 116 40 116 43.
  Definition loc_244 : location_info := LocationInfo file_3 115 16 115 25.
  Definition loc_245 : location_info := LocationInfo file_3 115 16 115 20.
  Definition loc_246 : location_info := LocationInfo file_3 115 16 115 20.
  Definition loc_247 : location_info := LocationInfo file_3 115 23 115 25.
  Definition loc_250 : location_info := LocationInfo file_3 114 17 114 26.
  Definition loc_251 : location_info := LocationInfo file_3 114 17 114 21.
  Definition loc_252 : location_info := LocationInfo file_3 114 17 114 21.
  Definition loc_253 : location_info := LocationInfo file_3 114 24 114 26.
  Definition loc_258 : location_info := LocationInfo file_2 62 2 62 41.
  Definition loc_259 : location_info := LocationInfo file_2 64 2 64 57.
  Definition loc_260 : location_info := LocationInfo file_2 66 2 66 52.
  Definition loc_261 : location_info := LocationInfo file_2 68 2 68 52.
  Definition loc_262 : location_info := LocationInfo file_2 68 2 68 20.
  Definition loc_263 : location_info := LocationInfo file_2 68 2 68 20.
  Definition loc_264 : location_info := LocationInfo file_2 68 21 68 40.
  Definition loc_265 : location_info := LocationInfo file_2 68 22 68 40.
  Definition loc_266 : location_info := LocationInfo file_2 68 22 68 27.
  Definition loc_267 : location_info := LocationInfo file_2 68 22 68 27.
  Definition loc_268 : location_info := LocationInfo file_2 68 42 68 50.
  Definition loc_269 : location_info := LocationInfo file_2 68 42 68 50.
  Definition loc_270 : location_info := LocationInfo file_2 66 2 66 19.
  Definition loc_271 : location_info := LocationInfo file_2 66 2 66 19.
  Definition loc_272 : location_info := LocationInfo file_2 66 20 66 45.
  Definition loc_273 : location_info := LocationInfo file_2 66 21 66 45.
  Definition loc_274 : location_info := LocationInfo file_2 66 21 66 45.
  Definition loc_275 : location_info := LocationInfo file_2 66 21 66 35.
  Definition loc_276 : location_info := LocationInfo file_2 66 21 66 35.
  Definition loc_277 : location_info := LocationInfo file_2 66 21 66 26.
  Definition loc_278 : location_info := LocationInfo file_2 66 21 66 26.
  Definition loc_279 : location_info := LocationInfo file_2 66 36 66 44.
  Definition loc_280 : location_info := LocationInfo file_2 66 36 66 44.
  Definition loc_281 : location_info := LocationInfo file_2 66 47 66 50.
  Definition loc_282 : location_info := LocationInfo file_2 66 47 66 50.
  Definition loc_283 : location_info := LocationInfo file_2 64 24 64 56.
  Definition loc_284 : location_info := LocationInfo file_2 64 24 64 56.
  Definition loc_285 : location_info := LocationInfo file_2 64 24 64 51.
  Definition loc_286 : location_info := LocationInfo file_2 64 24 64 51.
  Definition loc_287 : location_info := LocationInfo file_2 64 24 64 40.
  Definition loc_288 : location_info := LocationInfo file_2 64 24 64 40.
  Definition loc_289 : location_info := LocationInfo file_2 64 24 64 29.
  Definition loc_290 : location_info := LocationInfo file_2 64 24 64 29.
  Definition loc_291 : location_info := LocationInfo file_2 64 41 64 50.
  Definition loc_292 : location_info := LocationInfo file_2 64 41 64 50.
  Definition loc_293 : location_info := LocationInfo file_2 64 41 64 44.
  Definition loc_294 : location_info := LocationInfo file_2 64 41 64 44.
  Definition loc_297 : location_info := LocationInfo file_2 62 2 62 11.
  Definition loc_298 : location_info := LocationInfo file_2 62 2 62 5.
  Definition loc_299 : location_info := LocationInfo file_2 62 2 62 5.
  Definition loc_300 : location_info := LocationInfo file_2 62 14 62 40.
  Definition loc_301 : location_info := LocationInfo file_2 62 14 62 35.
  Definition loc_302 : location_info := LocationInfo file_2 62 14 62 35.
  Definition loc_303 : location_info := LocationInfo file_2 62 36 62 39.
  Definition loc_304 : location_info := LocationInfo file_2 62 36 62 39.
  Definition loc_307 : location_info := LocationInfo file_2 92 2 92 63.
  Definition loc_308 : location_info := LocationInfo file_2 93 2 106 3.
  Definition loc_309 : location_info := LocationInfo file_2 94 4 94 26.
  Definition loc_310 : location_info := LocationInfo file_2 94 11 94 25.
  Definition loc_311 : location_info := LocationInfo file_2 95 7 106 3.
  Definition loc_312 : location_info := LocationInfo file_2 97 4 97 74.
  Definition loc_313 : location_info := LocationInfo file_2 100 4 103 5.
  Definition loc_314 : location_info := LocationInfo file_2 105 4 105 15.
  Definition loc_315 : location_info := LocationInfo file_2 105 11 105 14.
  Definition loc_316 : location_info := LocationInfo file_2 105 11 105 14.
  Definition loc_317 : location_info := LocationInfo file_2 100 56 103 5.
  Definition loc_318 : location_info := LocationInfo file_2 102 6 102 58.
  Definition loc_319 : location_info := LocationInfo file_2 102 6 102 26.
  Definition loc_320 : location_info := LocationInfo file_2 102 6 102 26.
  Definition loc_321 : location_info := LocationInfo file_2 102 27 102 46.
  Definition loc_322 : location_info := LocationInfo file_2 102 28 102 46.
  Definition loc_323 : location_info := LocationInfo file_2 102 28 102 33.
  Definition loc_324 : location_info := LocationInfo file_2 102 28 102 33.
  Definition loc_325 : location_info := LocationInfo file_2 102 48 102 56.
  Definition loc_326 : location_info := LocationInfo file_2 102 48 102 56.
  Definition loc_327 : location_info := LocationInfo file_2 100 4 103 5.
  Definition loc_328 : location_info := LocationInfo file_2 100 8 100 54.
  Definition loc_329 : location_info := LocationInfo file_2 100 8 100 27.
  Definition loc_330 : location_info := LocationInfo file_2 100 8 100 27.
  Definition loc_331 : location_info := LocationInfo file_2 100 28 100 53.
  Definition loc_332 : location_info := LocationInfo file_2 100 29 100 53.
  Definition loc_333 : location_info := LocationInfo file_2 100 29 100 53.
  Definition loc_334 : location_info := LocationInfo file_2 100 29 100 43.
  Definition loc_335 : location_info := LocationInfo file_2 100 29 100 43.
  Definition loc_336 : location_info := LocationInfo file_2 100 29 100 34.
  Definition loc_337 : location_info := LocationInfo file_2 100 29 100 34.
  Definition loc_338 : location_info := LocationInfo file_2 100 44 100 52.
  Definition loc_339 : location_info := LocationInfo file_2 100 44 100 52.
  Definition loc_340 : location_info := LocationInfo file_2 97 26 97 73.
  Definition loc_341 : location_info := LocationInfo file_2 97 26 97 46.
  Definition loc_342 : location_info := LocationInfo file_2 97 26 97 46.
  Definition loc_343 : location_info := LocationInfo file_2 97 47 97 72.
  Definition loc_344 : location_info := LocationInfo file_2 97 48 97 72.
  Definition loc_345 : location_info := LocationInfo file_2 97 48 97 72.
  Definition loc_346 : location_info := LocationInfo file_2 97 48 97 62.
  Definition loc_347 : location_info := LocationInfo file_2 97 48 97 62.
  Definition loc_348 : location_info := LocationInfo file_2 97 48 97 53.
  Definition loc_349 : location_info := LocationInfo file_2 97 48 97 53.
  Definition loc_350 : location_info := LocationInfo file_2 97 63 97 71.
  Definition loc_351 : location_info := LocationInfo file_2 97 63 97 71.
  Definition loc_354 : location_info := LocationInfo file_2 93 6 93 42.
  Definition loc_355 : location_info := LocationInfo file_2 93 6 93 32.
  Definition loc_356 : location_info := LocationInfo file_2 93 6 93 32.
  Definition loc_357 : location_info := LocationInfo file_2 93 33 93 41.
  Definition loc_358 : location_info := LocationInfo file_2 93 33 93 41.
  Definition loc_359 : location_info := LocationInfo file_2 92 17 92 62.
  Definition loc_360 : location_info := LocationInfo file_2 92 17 92 41.
  Definition loc_361 : location_info := LocationInfo file_2 92 17 92 41.
  Definition loc_362 : location_info := LocationInfo file_2 92 42 92 61.
  Definition loc_363 : location_info := LocationInfo file_2 92 43 92 61.
  Definition loc_364 : location_info := LocationInfo file_2 92 43 92 48.
  Definition loc_365 : location_info := LocationInfo file_2 92 43 92 48.
  Definition loc_370 : location_info := LocationInfo file_2 111 2 111 44.
  Definition loc_371 : location_info := LocationInfo file_2 111 9 111 43.
  Definition loc_372 : location_info := LocationInfo file_2 111 9 111 38.
  Definition loc_373 : location_info := LocationInfo file_2 111 9 111 38.
  Definition loc_374 : location_info := LocationInfo file_2 111 9 111 38.
  Definition loc_375 : location_info := LocationInfo file_2 111 9 111 36.
  Definition loc_376 : location_info := LocationInfo file_2 111 9 111 36.
  Definition loc_377 : location_info := LocationInfo file_2 111 9 111 25.
  Definition loc_378 : location_info := LocationInfo file_2 111 9 111 25.
  Definition loc_379 : location_info := LocationInfo file_2 111 9 111 14.
  Definition loc_380 : location_info := LocationInfo file_2 111 9 111 14.
  Definition loc_381 : location_info := LocationInfo file_2 111 26 111 35.
  Definition loc_382 : location_info := LocationInfo file_2 111 26 111 35.
  Definition loc_383 : location_info := LocationInfo file_2 111 26 111 29.
  Definition loc_384 : location_info := LocationInfo file_2 111 26 111 29.
  Definition loc_385 : location_info := LocationInfo file_2 111 39 111 42.
  Definition loc_386 : location_info := LocationInfo file_2 111 39 111 42.
  Definition loc_389 : location_info := LocationInfo file_5 36 2 36 24.
  Definition loc_390 : location_info := LocationInfo file_5 39 2 39 43.
  Definition loc_391 : location_info := LocationInfo file_5 52 2 54 3.
  Definition loc_392 : location_info := LocationInfo file_5 52 2 54 3.
  Definition loc_393 : location_info := LocationInfo file_5 52 2 54 3.
  Definition loc_394 : location_info := LocationInfo file_5 66 2 69 3.
  Definition loc_395 : location_info := LocationInfo file_5 66 2 69 3.
  Definition loc_396 : location_info := LocationInfo file_5 66 2 69 3.
  Definition loc_397 : location_info := LocationInfo file_5 66 65 69 3.
  Definition loc_398 : location_info := LocationInfo file_5 67 4 67 87.
  Definition loc_399 : location_info := LocationInfo file_5 68 4 68 68.
  Definition loc_400 : location_info := LocationInfo file_5 66 2 69 3.
  Definition loc_402 : location_info := LocationInfo file_5 66 54 66 58.
  Definition loc_403 : location_info := LocationInfo file_5 66 54 66 63.
  Definition loc_404 : location_info := LocationInfo file_5 66 54 66 58.
  Definition loc_405 : location_info := LocationInfo file_5 66 54 66 58.
  Definition loc_406 : location_info := LocationInfo file_5 66 62 66 63.
  Definition loc_407 : location_info := LocationInfo file_5 68 4 68 33.
  Definition loc_408 : location_info := LocationInfo file_5 68 4 68 28.
  Definition loc_409 : location_info := LocationInfo file_5 68 4 68 28.
  Definition loc_410 : location_info := LocationInfo file_5 68 4 68 22.
  Definition loc_411 : location_info := LocationInfo file_5 68 4 68 22.
  Definition loc_412 : location_info := LocationInfo file_5 68 4 68 14.
  Definition loc_413 : location_info := LocationInfo file_5 68 4 68 7.
  Definition loc_414 : location_info := LocationInfo file_5 68 4 68 7.
  Definition loc_415 : location_info := LocationInfo file_5 68 23 68 27.
  Definition loc_416 : location_info := LocationInfo file_5 68 23 68 27.
  Definition loc_417 : location_info := LocationInfo file_5 68 36 68 67.
  Definition loc_418 : location_info := LocationInfo file_5 68 37 68 67.
  Definition loc_419 : location_info := LocationInfo file_5 68 37 68 61.
  Definition loc_420 : location_info := LocationInfo file_5 68 37 68 61.
  Definition loc_421 : location_info := LocationInfo file_5 68 37 68 55.
  Definition loc_422 : location_info := LocationInfo file_5 68 37 68 55.
  Definition loc_423 : location_info := LocationInfo file_5 68 37 68 47.
  Definition loc_424 : location_info := LocationInfo file_5 68 37 68 40.
  Definition loc_425 : location_info := LocationInfo file_5 68 37 68 40.
  Definition loc_426 : location_info := LocationInfo file_5 68 56 68 60.
  Definition loc_427 : location_info := LocationInfo file_5 68 56 68 60.
  Definition loc_428 : location_info := LocationInfo file_5 67 4 67 28.
  Definition loc_429 : location_info := LocationInfo file_5 67 4 67 28.
  Definition loc_430 : location_info := LocationInfo file_5 67 4 67 22.
  Definition loc_431 : location_info := LocationInfo file_5 67 4 67 22.
  Definition loc_432 : location_info := LocationInfo file_5 67 4 67 14.
  Definition loc_433 : location_info := LocationInfo file_5 67 4 67 7.
  Definition loc_434 : location_info := LocationInfo file_5 67 4 67 7.
  Definition loc_435 : location_info := LocationInfo file_5 67 23 67 27.
  Definition loc_436 : location_info := LocationInfo file_5 67 23 67 27.
  Definition loc_437 : location_info := LocationInfo file_5 67 31 67 86.
  Definition loc_438 : location_info := LocationInfo file_5 67 31 67 86.
  Definition loc_440 : location_info := LocationInfo file_5 67 55 67 69.
  Definition loc_441 : location_info := LocationInfo file_5 67 71 67 85.
  Definition loc_442 : location_info := LocationInfo file_5 66 20 66 52.
  Definition loc_443 : location_info := LocationInfo file_5 66 20 66 24.
  Definition loc_444 : location_info := LocationInfo file_5 66 20 66 24.
  Definition loc_445 : location_info := LocationInfo file_5 66 27 66 52.
  Definition loc_446 : location_info := LocationInfo file_5 66 28 66 47.
  Definition loc_447 : location_info := LocationInfo file_5 66 50 66 51.
  Definition loc_448 : location_info := LocationInfo file_5 66 17 66 18.
  Definition loc_451 : location_info := LocationInfo file_5 52 62 54 3.
  Definition loc_452 : location_info := LocationInfo file_5 53 4 53 68.
  Definition loc_453 : location_info := LocationInfo file_5 52 2 54 3.
  Definition loc_455 : location_info := LocationInfo file_5 52 52 52 55.
  Definition loc_456 : location_info := LocationInfo file_5 52 52 52 60.
  Definition loc_457 : location_info := LocationInfo file_5 52 52 52 55.
  Definition loc_458 : location_info := LocationInfo file_5 52 52 52 55.
  Definition loc_459 : location_info := LocationInfo file_5 52 59 52 60.
  Definition loc_460 : location_info := LocationInfo file_5 53 4 53 29.
  Definition loc_461 : location_info := LocationInfo file_5 53 4 53 29.
  Definition loc_462 : location_info := LocationInfo file_5 53 4 53 24.
  Definition loc_463 : location_info := LocationInfo file_5 53 4 53 24.
  Definition loc_464 : location_info := LocationInfo file_5 53 4 53 14.
  Definition loc_465 : location_info := LocationInfo file_5 53 4 53 7.
  Definition loc_466 : location_info := LocationInfo file_5 53 4 53 7.
  Definition loc_467 : location_info := LocationInfo file_5 53 25 53 28.
  Definition loc_468 : location_info := LocationInfo file_5 53 25 53 28.
  Definition loc_469 : location_info := LocationInfo file_5 53 32 53 67.
  Definition loc_470 : location_info := LocationInfo file_5 53 32 53 67.
  Definition loc_472 : location_info := LocationInfo file_5 53 51 53 52.
  Definition loc_473 : location_info := LocationInfo file_5 53 54 53 66.
  Definition loc_474 : location_info := LocationInfo file_5 52 19 52 50.
  Definition loc_475 : location_info := LocationInfo file_5 52 19 52 22.
  Definition loc_476 : location_info := LocationInfo file_5 52 19 52 22.
  Definition loc_477 : location_info := LocationInfo file_5 52 25 52 50.
  Definition loc_478 : location_info := LocationInfo file_5 52 26 52 45.
  Definition loc_479 : location_info := LocationInfo file_5 52 48 52 49.
  Definition loc_480 : location_info := LocationInfo file_5 52 16 52 17.
  Definition loc_483 : location_info := LocationInfo file_5 39 2 39 17.
  Definition loc_484 : location_info := LocationInfo file_5 39 2 39 17.
  Definition loc_485 : location_info := LocationInfo file_5 39 18 39 41.
  Definition loc_486 : location_info := LocationInfo file_5 39 19 39 41.
  Definition loc_487 : location_info := LocationInfo file_5 39 19 39 29.
  Definition loc_488 : location_info := LocationInfo file_5 39 19 39 22.
  Definition loc_489 : location_info := LocationInfo file_5 39 19 39 22.
  Definition loc_490 : location_info := LocationInfo file_5 36 2 36 19.
  Definition loc_491 : location_info := LocationInfo file_5 36 2 36 5.
  Definition loc_492 : location_info := LocationInfo file_5 36 2 36 5.
  Definition loc_493 : location_info := LocationInfo file_5 36 22 36 23.
  Definition loc_496 : location_info := LocationInfo file_5 79 2 79 33.
  Definition loc_497 : location_info := LocationInfo file_5 82 2 82 32.
  Definition loc_498 : location_info := LocationInfo file_5 83 2 84 15.
  Definition loc_499 : location_info := LocationInfo file_5 86 2 86 46.
  Definition loc_500 : location_info := LocationInfo file_5 87 2 87 22.
  Definition loc_501 : location_info := LocationInfo file_5 89 2 89 11.
  Definition loc_502 : location_info := LocationInfo file_5 89 9 89 10.
  Definition loc_503 : location_info := LocationInfo file_5 87 2 87 19.
  Definition loc_504 : location_info := LocationInfo file_5 87 2 87 5.
  Definition loc_505 : location_info := LocationInfo file_5 87 2 87 5.
  Definition loc_506 : location_info := LocationInfo file_5 86 2 86 40.
  Definition loc_507 : location_info := LocationInfo file_5 86 2 86 40.
  Definition loc_508 : location_info := LocationInfo file_5 86 2 86 21.
  Definition loc_509 : location_info := LocationInfo file_5 86 2 86 21.
  Definition loc_510 : location_info := LocationInfo file_5 86 2 86 5.
  Definition loc_511 : location_info := LocationInfo file_5 86 2 86 5.
  Definition loc_512 : location_info := LocationInfo file_5 86 22 86 39.
  Definition loc_513 : location_info := LocationInfo file_5 86 22 86 39.
  Definition loc_514 : location_info := LocationInfo file_5 86 22 86 25.
  Definition loc_515 : location_info := LocationInfo file_5 86 22 86 25.
  Definition loc_516 : location_info := LocationInfo file_5 86 43 86 45.
  Definition loc_517 : location_info := LocationInfo file_5 86 43 86 45.
  Definition loc_518 : location_info := LocationInfo file_5 84 4 84 15.
  Definition loc_519 : location_info := LocationInfo file_5 84 11 84 14.
  Definition loc_520 : location_info := LocationInfo file_5 84 11 84 14.
  Definition loc_521 : location_info := LocationInfo file_5 83 2 84 15.
  Definition loc_522 : location_info := LocationInfo file_5 83 6 83 9.
  Definition loc_523 : location_info := LocationInfo file_5 83 6 83 9.
  Definition loc_524 : location_info := LocationInfo file_5 82 12 82 31.
  Definition loc_525 : location_info := LocationInfo file_5 82 12 82 17.
  Definition loc_526 : location_info := LocationInfo file_5 82 12 82 17.
  Definition loc_527 : location_info := LocationInfo file_5 82 18 82 20.
  Definition loc_528 : location_info := LocationInfo file_5 82 18 82 20.
  Definition loc_529 : location_info := LocationInfo file_5 82 22 82 23.
  Definition loc_530 : location_info := LocationInfo file_5 82 25 82 30.
  Definition loc_533 : location_info := LocationInfo file_5 79 9 79 31.
  Definition loc_534 : location_info := LocationInfo file_5 79 9 79 26.
  Definition loc_535 : location_info := LocationInfo file_5 79 9 79 26.
  Definition loc_536 : location_info := LocationInfo file_5 79 9 79 12.
  Definition loc_537 : location_info := LocationInfo file_5 79 9 79 12.
  Definition loc_538 : location_info := LocationInfo file_5 79 29 79 31.
  Definition loc_541 : location_info := LocationInfo file_5 104 2 104 59.
  Definition loc_542 : location_info := LocationInfo file_5 104 2 104 28.
  Definition loc_543 : location_info := LocationInfo file_5 104 2 104 28.
  Definition loc_544 : location_info := LocationInfo file_5 104 2 104 22.
  Definition loc_545 : location_info := LocationInfo file_5 104 2 104 22.
  Definition loc_546 : location_info := LocationInfo file_5 104 2 104 12.
  Definition loc_547 : location_info := LocationInfo file_5 104 2 104 5.
  Definition loc_548 : location_info := LocationInfo file_5 104 2 104 5.
  Definition loc_549 : location_info := LocationInfo file_5 104 23 104 27.
  Definition loc_550 : location_info := LocationInfo file_5 104 23 104 27.
  Definition loc_551 : location_info := LocationInfo file_5 104 31 104 58.
  Definition loc_552 : location_info := LocationInfo file_5 104 31 104 58.
  Definition loc_554 : location_info := LocationInfo file_5 104 50 104 54.
  Definition loc_555 : location_info := LocationInfo file_5 104 50 104 54.
  Definition loc_556 : location_info := LocationInfo file_5 104 56 104 57.
  Definition loc_557 : location_info := LocationInfo file_5 104 56 104 57.
  Definition loc_560 : location_info := LocationInfo file_5 280 2 280 10.
  Definition loc_561 : location_info := LocationInfo file_5 282 2 282 32.
  Definition loc_562 : location_info := LocationInfo file_5 284 2 306 3.
  Definition loc_563 : location_info := LocationInfo file_5 284 12 306 3.
  Definition loc_564 : location_info := LocationInfo file_5 285 4 305 19.
  Definition loc_566 : location_info := LocationInfo file_5 285 7 305 5.
  Definition loc_567 : location_info := LocationInfo file_5 287 6 287 44.
  Definition loc_568 : location_info := LocationInfo file_5 290 6 290 54.
  Definition loc_569 : location_info := LocationInfo file_5 293 6 294 14.
  Definition loc_570 : location_info := LocationInfo file_5 297 6 297 44.
  Definition loc_571 : location_info := LocationInfo file_5 300 6 300 16.
  Definition loc_572 : location_info := LocationInfo file_5 303 6 304 19.
  Definition loc_573 : location_info := LocationInfo file_5 304 8 304 19.
  Definition loc_574 : location_info := LocationInfo file_5 304 15 304 18.
  Definition loc_575 : location_info := LocationInfo file_5 304 15 304 18.
  Definition loc_576 : location_info := LocationInfo file_5 303 6 304 19.
  Definition loc_577 : location_info := LocationInfo file_5 303 10 303 13.
  Definition loc_578 : location_info := LocationInfo file_5 303 10 303 13.
  Definition loc_579 : location_info := LocationInfo file_5 300 6 300 10.
  Definition loc_580 : location_info := LocationInfo file_5 300 6 300 10.
  Definition loc_581 : location_info := LocationInfo file_5 300 11 300 14.
  Definition loc_582 : location_info := LocationInfo file_5 300 11 300 14.
  Definition loc_583 : location_info := LocationInfo file_5 297 6 297 9.
  Definition loc_584 : location_info := LocationInfo file_5 297 12 297 43.
  Definition loc_585 : location_info := LocationInfo file_5 297 12 297 25.
  Definition loc_586 : location_info := LocationInfo file_5 297 12 297 25.
  Definition loc_587 : location_info := LocationInfo file_5 297 26 297 37.
  Definition loc_588 : location_info := LocationInfo file_5 297 27 297 37.
  Definition loc_589 : location_info := LocationInfo file_5 297 27 297 30.
  Definition loc_590 : location_info := LocationInfo file_5 297 27 297 30.
  Definition loc_591 : location_info := LocationInfo file_5 297 39 297 42.
  Definition loc_592 : location_info := LocationInfo file_5 297 39 297 42.
  Definition loc_593 : location_info := LocationInfo file_5 294 8 294 14.
  Definition loc_594 : location_info := LocationInfo file_5 293 6 294 14.
  Definition loc_595 : location_info := LocationInfo file_5 293 10 293 14.
  Definition loc_597 : location_info := LocationInfo file_5 293 11 293 14.
  Definition loc_598 : location_info := LocationInfo file_5 293 11 293 14.
  Definition loc_599 : location_info := LocationInfo file_5 290 28 290 53.
  Definition loc_600 : location_info := LocationInfo file_5 290 28 290 40.
  Definition loc_601 : location_info := LocationInfo file_5 290 28 290 40.
  Definition loc_602 : location_info := LocationInfo file_5 290 41 290 52.
  Definition loc_603 : location_info := LocationInfo file_5 290 42 290 52.
  Definition loc_604 : location_info := LocationInfo file_5 290 42 290 45.
  Definition loc_605 : location_info := LocationInfo file_5 290 42 290 45.
  Definition loc_608 : location_info := LocationInfo file_5 287 6 287 9.
  Definition loc_609 : location_info := LocationInfo file_5 287 12 287 43.
  Definition loc_610 : location_info := LocationInfo file_5 287 12 287 38.
  Definition loc_611 : location_info := LocationInfo file_5 287 12 287 38.
  Definition loc_612 : location_info := LocationInfo file_5 287 39 287 42.
  Definition loc_613 : location_info := LocationInfo file_5 287 39 287 42.
  Definition loc_614 : location_info := LocationInfo file_5 305 13 305 17.
  Definition loc_616 : location_info := LocationInfo file_5 305 14 305 17.
  Definition loc_617 : location_info := LocationInfo file_5 305 14 305 17.
  Definition loc_618 : location_info := LocationInfo file_5 284 9 284 10.
  Definition loc_619 : location_info := LocationInfo file_5 282 9 282 30.
  Definition loc_620 : location_info := LocationInfo file_5 282 9 282 26.
  Definition loc_621 : location_info := LocationInfo file_5 282 9 282 26.
  Definition loc_622 : location_info := LocationInfo file_5 282 9 282 12.
  Definition loc_623 : location_info := LocationInfo file_5 282 9 282 12.
  Definition loc_624 : location_info := LocationInfo file_5 282 29 282 30.
  Definition loc_627 : location_info := LocationInfo file_0 10 2 10 12.
  Definition loc_628 : location_info := LocationInfo file_0 15 2 15 11.
  Definition loc_629 : location_info := LocationInfo file_0 15 9 15 10.
  Definition loc_630 : location_info := LocationInfo file_0 10 10 10 12.
  Definition loc_631 : location_info := LocationInfo file_0 10 8 10 9.
  Definition loc_634 : location_info := LocationInfo file_1 33 2 33 23.
  Definition loc_635 : location_info := LocationInfo file_1 34 2 34 42.
  Definition loc_636 : location_info := LocationInfo file_1 35 2 35 11.
  Definition loc_637 : location_info := LocationInfo file_1 35 9 35 10.
  Definition loc_638 : location_info := LocationInfo file_1 35 9 35 10.
  Definition loc_639 : location_info := LocationInfo file_1 34 26 34 42.
  Definition loc_640 : location_info := LocationInfo file_1 34 28 34 40.
  Definition loc_641 : location_info := LocationInfo file_1 34 28 34 37.
  Definition loc_642 : location_info := LocationInfo file_1 34 28 34 37.
  Definition loc_643 : location_info := LocationInfo file_1 34 2 34 42.
  Definition loc_644 : location_info := LocationInfo file_1 34 5 34 24.
  Definition loc_645 : location_info := LocationInfo file_1 34 5 34 6.
  Definition loc_646 : location_info := LocationInfo file_1 34 5 34 6.
  Definition loc_647 : location_info := LocationInfo file_1 34 10 34 24.
  Definition loc_648 : location_info := LocationInfo file_1 33 12 33 22.
  Definition loc_649 : location_info := LocationInfo file_1 33 12 33 18.
  Definition loc_650 : location_info := LocationInfo file_1 33 12 33 18.
  Definition loc_651 : location_info := LocationInfo file_1 33 19 33 21.
  Definition loc_652 : location_info := LocationInfo file_1 33 19 33 21.
  Definition loc_657 : location_info := LocationInfo file_5 20 2 20 11.
  Definition loc_658 : location_info := LocationInfo file_5 20 9 20 10.
  Definition loc_661 : location_info := LocationInfo file_5 126 2 126 46.
  Definition loc_662 : location_info := LocationInfo file_5 129 2 129 14.
  Definition loc_663 : location_info := LocationInfo file_5 132 2 132 107.
  Definition loc_664 : location_info := LocationInfo file_5 134 2 142 3.
  Definition loc_665 : location_info := LocationInfo file_5 134 13 138 3.
  Definition loc_666 : location_info := LocationInfo file_5 136 4 136 14.
  Definition loc_667 : location_info := LocationInfo file_5 137 4 137 13.
  Definition loc_668 : location_info := LocationInfo file_5 137 11 137 12.
  Definition loc_669 : location_info := LocationInfo file_5 137 11 137 12.
  Definition loc_670 : location_info := LocationInfo file_5 136 4 136 8.
  Definition loc_671 : location_info := LocationInfo file_5 136 4 136 8.
  Definition loc_672 : location_info := LocationInfo file_5 136 9 136 12.
  Definition loc_673 : location_info := LocationInfo file_5 136 9 136 12.
  Definition loc_674 : location_info := LocationInfo file_5 138 9 142 3.
  Definition loc_675 : location_info := LocationInfo file_5 139 4 139 17.
  Definition loc_676 : location_info := LocationInfo file_5 140 4 140 35.
  Definition loc_677 : location_info := LocationInfo file_5 141 4 141 13.
  Definition loc_678 : location_info := LocationInfo file_5 141 11 141 12.
  Definition loc_679 : location_info := LocationInfo file_5 140 4 140 16.
  Definition loc_680 : location_info := LocationInfo file_5 140 4 140 16.
  Definition loc_681 : location_info := LocationInfo file_5 140 17 140 28.
  Definition loc_682 : location_info := LocationInfo file_5 140 18 140 28.
  Definition loc_683 : location_info := LocationInfo file_5 140 18 140 21.
  Definition loc_684 : location_info := LocationInfo file_5 140 18 140 21.
  Definition loc_685 : location_info := LocationInfo file_5 140 30 140 33.
  Definition loc_686 : location_info := LocationInfo file_5 140 30 140 33.
  Definition loc_687 : location_info := LocationInfo file_5 139 4 139 12.
  Definition loc_688 : location_info := LocationInfo file_5 139 4 139 7.
  Definition loc_689 : location_info := LocationInfo file_5 139 4 139 7.
  Definition loc_690 : location_info := LocationInfo file_5 139 15 139 16.
  Definition loc_691 : location_info := LocationInfo file_5 139 15 139 16.
  Definition loc_692 : location_info := LocationInfo file_5 134 6 134 11.
  Definition loc_693 : location_info := LocationInfo file_5 134 6 134 7.
  Definition loc_694 : location_info := LocationInfo file_5 134 6 134 7.
  Definition loc_695 : location_info := LocationInfo file_5 134 10 134 11.
  Definition loc_696 : location_info := LocationInfo file_5 132 10 132 106.
  Definition loc_697 : location_info := LocationInfo file_5 132 10 132 14.
  Definition loc_698 : location_info := LocationInfo file_5 132 10 132 14.
  Definition loc_699 : location_info := LocationInfo file_5 132 15 132 17.
  Definition loc_700 : location_info := LocationInfo file_5 132 15 132 17.
  Definition loc_701 : location_info := LocationInfo file_5 132 19 132 29.
  Definition loc_702 : location_info := LocationInfo file_5 132 20 132 29.
  Definition loc_703 : location_info := LocationInfo file_5 132 20 132 23.
  Definition loc_704 : location_info := LocationInfo file_5 132 20 132 23.
  Definition loc_705 : location_info := LocationInfo file_5 132 31 132 105.
  Definition loc_706 : location_info := LocationInfo file_5 132 32 132 78.
  Definition loc_707 : location_info := LocationInfo file_5 132 32 132 61.
  Definition loc_708 : location_info := LocationInfo file_5 132 32 132 36.
  Definition loc_709 : location_info := LocationInfo file_5 132 39 132 61.
  Definition loc_710 : location_info := LocationInfo file_5 132 64 132 78.
  Definition loc_711 : location_info := LocationInfo file_5 132 81 132 104.
  Definition loc_714 : location_info := LocationInfo file_5 129 9 129 12.
  Definition loc_715 : location_info := LocationInfo file_5 129 9 129 12.
  Definition loc_716 : location_info := LocationInfo file_5 126 24 126 45.
  Definition loc_717 : location_info := LocationInfo file_5 126 24 126 31.
  Definition loc_718 : location_info := LocationInfo file_5 126 24 126 31.
  Definition loc_719 : location_info := LocationInfo file_5 126 32 126 44.
  Definition loc_724 : location_info := LocationInfo file_5 160 2 160 10.
  Definition loc_725 : location_info := LocationInfo file_5 161 2 161 20.
  Definition loc_726 : location_info := LocationInfo file_5 177 2 181 15.
  Definition loc_727 : location_info := LocationInfo file_5 183 2 187 15.
  Definition loc_728 : location_info := LocationInfo file_5 185 4 185 21.
  Definition loc_729 : location_info := LocationInfo file_5 185 11 185 20.
  Definition loc_730 : location_info := LocationInfo file_5 185 11 185 20.
  Definition loc_731 : location_info := LocationInfo file_5 187 4 187 15.
  Definition loc_732 : location_info := LocationInfo file_5 187 11 187 14.
  Definition loc_733 : location_info := LocationInfo file_5 187 11 187 14.
  Definition loc_734 : location_info := LocationInfo file_5 183 6 183 95.
  Definition loc_735 : location_info := LocationInfo file_5 183 6 183 51.
  Definition loc_736 : location_info := LocationInfo file_5 183 6 183 26.
  Definition loc_737 : location_info := LocationInfo file_5 183 6 183 26.
  Definition loc_738 : location_info := LocationInfo file_5 183 8 183 25.
  Definition loc_739 : location_info := LocationInfo file_5 183 8 183 23.
  Definition loc_740 : location_info := LocationInfo file_5 183 8 183 23.
  Definition loc_741 : location_info := LocationInfo file_5 183 30 183 51.
  Definition loc_742 : location_info := LocationInfo file_5 183 55 183 95.
  Definition loc_743 : location_info := LocationInfo file_5 183 55 183 75.
  Definition loc_744 : location_info := LocationInfo file_5 183 55 183 75.
  Definition loc_745 : location_info := LocationInfo file_5 183 57 183 74.
  Definition loc_746 : location_info := LocationInfo file_5 183 57 183 72.
  Definition loc_747 : location_info := LocationInfo file_5 183 57 183 72.
  Definition loc_748 : location_info := LocationInfo file_5 183 79 183 95.
  Definition loc_750 : location_info := LocationInfo file_5 177 5 180 3.
  Definition loc_751 : location_info := LocationInfo file_5 178 4 178 39.
  Definition loc_752 : location_info := LocationInfo file_5 179 4 179 28.
  Definition loc_753 : location_info := LocationInfo file_5 179 14 179 28.
  Definition loc_754 : location_info := LocationInfo file_5 179 14 179 23.
  Definition loc_755 : location_info := LocationInfo file_5 179 26 179 27.
  Definition loc_756 : location_info := LocationInfo file_5 179 4 179 28.
  Definition loc_757 : location_info := LocationInfo file_5 179 8 179 12.
  Definition loc_759 : location_info := LocationInfo file_5 179 9 179 12.
  Definition loc_760 : location_info := LocationInfo file_5 179 9 179 12.
  Definition loc_761 : location_info := LocationInfo file_5 178 4 178 7.
  Definition loc_762 : location_info := LocationInfo file_5 178 10 178 38.
  Definition loc_763 : location_info := LocationInfo file_5 178 10 178 29.
  Definition loc_764 : location_info := LocationInfo file_5 178 10 178 29.
  Definition loc_765 : location_info := LocationInfo file_5 178 30 178 33.
  Definition loc_766 : location_info := LocationInfo file_5 178 30 178 33.
  Definition loc_767 : location_info := LocationInfo file_5 178 35 178 37.
  Definition loc_768 : location_info := LocationInfo file_5 178 35 178 37.
  Definition loc_769 : location_info := LocationInfo file_5 181 9 181 13.
  Definition loc_771 : location_info := LocationInfo file_5 181 10 181 13.
  Definition loc_772 : location_info := LocationInfo file_5 181 10 181 13.
  Definition loc_773 : location_info := LocationInfo file_5 161 18 161 19.
  Definition loc_778 : location_info := LocationInfo file_5 215 2 215 24.
  Definition loc_779 : location_info := LocationInfo file_5 229 2 236 3.
  Definition loc_780 : location_info := LocationInfo file_5 229 2 236 3.
  Definition loc_781 : location_info := LocationInfo file_5 229 2 236 3.
  Definition loc_782 : location_info := LocationInfo file_5 237 2 237 14.
  Definition loc_783 : location_info := LocationInfo file_5 237 9 237 13.
  Definition loc_784 : location_info := LocationInfo file_5 237 9 237 13.
  Definition loc_785 : location_info := LocationInfo file_5 229 52 236 3.
  Definition loc_786 : location_info := LocationInfo file_5 230 4 230 33.
  Definition loc_787 : location_info := LocationInfo file_5 231 4 231 36.
  Definition loc_788 : location_info := LocationInfo file_5 232 4 233 17.
  Definition loc_789 : location_info := LocationInfo file_5 234 4 235 15.
  Definition loc_790 : location_info := LocationInfo file_5 229 2 236 3.
  Definition loc_792 : location_info := LocationInfo file_5 229 46 229 48.
  Definition loc_793 : location_info := LocationInfo file_5 235 6 235 15.
  Definition loc_794 : location_info := LocationInfo file_5 235 6 235 10.
  Definition loc_795 : location_info := LocationInfo file_5 235 13 235 14.
  Definition loc_796 : location_info := LocationInfo file_5 234 4 235 15.
  Definition loc_797 : location_info := LocationInfo file_5 234 8 234 15.
  Definition loc_798 : location_info := LocationInfo file_5 234 8 234 11.
  Definition loc_799 : location_info := LocationInfo file_5 234 8 234 11.
  Definition loc_800 : location_info := LocationInfo file_5 234 14 234 15.
  Definition loc_801 : location_info := LocationInfo file_5 233 6 233 17.
  Definition loc_802 : location_info := LocationInfo file_5 233 13 233 16.
  Definition loc_803 : location_info := LocationInfo file_5 233 13 233 16.
  Definition loc_804 : location_info := LocationInfo file_5 232 4 233 17.
  Definition loc_805 : location_info := LocationInfo file_5 232 8 232 15.
  Definition loc_806 : location_info := LocationInfo file_5 232 8 232 11.
  Definition loc_807 : location_info := LocationInfo file_5 232 8 232 11.
  Definition loc_808 : location_info := LocationInfo file_5 232 14 232 15.
  Definition loc_809 : location_info := LocationInfo file_5 231 4 231 7.
  Definition loc_810 : location_info := LocationInfo file_5 231 10 231 35.
  Definition loc_811 : location_info := LocationInfo file_5 231 10 231 26.
  Definition loc_812 : location_info := LocationInfo file_5 231 10 231 26.
  Definition loc_813 : location_info := LocationInfo file_5 231 27 231 30.
  Definition loc_814 : location_info := LocationInfo file_5 231 27 231 30.
  Definition loc_815 : location_info := LocationInfo file_5 231 32 231 34.
  Definition loc_816 : location_info := LocationInfo file_5 231 32 231 34.
  Definition loc_817 : location_info := LocationInfo file_5 230 4 230 6.
  Definition loc_818 : location_info := LocationInfo file_5 230 9 230 32.
  Definition loc_819 : location_info := LocationInfo file_5 230 9 230 32.
  Definition loc_820 : location_info := LocationInfo file_5 230 9 230 32.
  Definition loc_821 : location_info := LocationInfo file_5 230 9 230 28.
  Definition loc_822 : location_info := LocationInfo file_5 230 9 230 28.
  Definition loc_823 : location_info := LocationInfo file_5 230 9 230 12.
  Definition loc_824 : location_info := LocationInfo file_5 230 9 230 12.
  Definition loc_825 : location_info := LocationInfo file_5 230 29 230 31.
  Definition loc_826 : location_info := LocationInfo file_5 230 29 230 31.
  Definition loc_827 : location_info := LocationInfo file_5 229 22 229 44.
  Definition loc_828 : location_info := LocationInfo file_5 229 22 229 24.
  Definition loc_829 : location_info := LocationInfo file_5 229 22 229 24.
  Definition loc_830 : location_info := LocationInfo file_5 229 27 229 44.
  Definition loc_831 : location_info := LocationInfo file_5 229 27 229 44.
  Definition loc_832 : location_info := LocationInfo file_5 229 27 229 30.
  Definition loc_833 : location_info := LocationInfo file_5 229 27 229 30.
  Definition loc_834 : location_info := LocationInfo file_5 229 19 229 20.
  Definition loc_837 : location_info := LocationInfo file_5 215 22 215 23.
  Definition loc_842 : location_info := LocationInfo file_5 255 2 255 10.
  Definition loc_843 : location_info := LocationInfo file_5 269 2 273 20.
  Definition loc_844 : location_info := LocationInfo file_5 275 2 275 13.
  Definition loc_845 : location_info := LocationInfo file_5 275 9 275 12.
  Definition loc_846 : location_info := LocationInfo file_5 275 9 275 12.
  Definition loc_848 : location_info := LocationInfo file_5 269 5 273 3.
  Definition loc_849 : location_info := LocationInfo file_5 270 4 270 30.
  Definition loc_850 : location_info := LocationInfo file_5 271 4 272 17.
  Definition loc_851 : location_info := LocationInfo file_5 272 6 272 17.
  Definition loc_852 : location_info := LocationInfo file_5 272 13 272 16.
  Definition loc_853 : location_info := LocationInfo file_5 272 13 272 16.
  Definition loc_854 : location_info := LocationInfo file_5 271 4 272 17.
  Definition loc_855 : location_info := LocationInfo file_5 271 8 271 15.
  Definition loc_856 : location_info := LocationInfo file_5 271 8 271 11.
  Definition loc_857 : location_info := LocationInfo file_5 271 8 271 11.
  Definition loc_858 : location_info := LocationInfo file_5 271 14 271 15.
  Definition loc_859 : location_info := LocationInfo file_5 270 4 270 7.
  Definition loc_860 : location_info := LocationInfo file_5 270 10 270 29.
  Definition loc_861 : location_info := LocationInfo file_5 270 10 270 24.
  Definition loc_862 : location_info := LocationInfo file_5 270 10 270 24.
  Definition loc_863 : location_info := LocationInfo file_5 270 25 270 28.
  Definition loc_864 : location_info := LocationInfo file_5 270 25 270 28.
  Definition loc_865 : location_info := LocationInfo file_5 273 11 273 18.
  Definition loc_866 : location_info := LocationInfo file_5 273 11 273 14.
  Definition loc_867 : location_info := LocationInfo file_5 273 11 273 14.
  Definition loc_868 : location_info := LocationInfo file_5 273 17 273 18.

  (* Definition of struct [__cerbty_unnamed_tag_488]. *)
  Program Definition struct___cerbty_unnamed_tag_488 := {|
    sl_members := [
      (Some "__dummy_max_align_t", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [pollfd]. *)
  Program Definition struct_pollfd := {|
    sl_members := [
      (Some "fd", it_layout i32);
      (Some "events", it_layout i16);
      (Some "revents", it_layout i16)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [message]. *)
  Program Definition struct_message := {|
    sl_members := [
      (Some "type", it_layout u8);
      (None, Layout 7%nat 0%nat);
      (Some "len", it_layout size_t);
      (Some "next", void*);
      (Some "data", mk_array_layout (it_layout u8) 4079);
      (None, Layout 1%nat 0%nat)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [message_queue]. *)
  Program Definition struct_message_queue := {|
    sl_members := [
      (Some "first", void*);
      (Some "last", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [prio_bitmap]. *)
  Program Definition struct_prio_bitmap := {|
    sl_members := [
      (Some "bits", mk_array_layout (it_layout u64) 4)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [callback]. *)
  Program Definition struct_callback := {|
    sl_members := [
      (Some "prio", it_layout u8);
      (None, Layout 7%nat 0%nat);
      (Some "f", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [npfp_scheduler]. *)
  Program Definition struct_npfp_scheduler := {|
    sl_members := [
      (Some "callbacks", mk_array_layout (layout_of struct_callback) 256);
      (Some "pending", mk_array_layout (layout_of struct_message_queue) 256);
      (Some "prio_levels", layout_of struct_prio_bitmap)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [fd_scheduler]. *)
  Program Definition struct_fd_scheduler := {|
    sl_members := [
      (Some "input_channels", mk_array_layout (it_layout i32) 16);
      (Some "num_channels", it_layout u64);
      (Some "sched", layout_of struct_npfp_scheduler)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [message_queue_add]. *)
  Definition impl_message_queue_add : function := {|
    f_args := [
      ("q", void*);
      ("msg", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        LocInfoE loc_19 ((LocInfoE loc_20 (!{PtrOp} (LocInfoE loc_21 ("msg")))) at{struct_message} "next") <-{ PtrOp }
          LocInfoE loc_22 (NULL) ;
        locinfo: loc_3 ;
        LocInfoE loc_13 (!{PtrOp} (LocInfoE loc_14 ((LocInfoE loc_15 (!{PtrOp} (LocInfoE loc_16 ("q")))) at{struct_message_queue} "last"))) <-{ PtrOp }
          LocInfoE loc_17 (use{PtrOp} (LocInfoE loc_18 ("msg"))) ;
        locinfo: loc_4 ;
        LocInfoE loc_5 ((LocInfoE loc_6 (!{PtrOp} (LocInfoE loc_7 ("q")))) at{struct_message_queue} "last") <-{ PtrOp }
          LocInfoE loc_8 (&(LocInfoE loc_9 ((LocInfoE loc_10 (!{PtrOp} (LocInfoE loc_11 ("msg")))) at{struct_message} "next"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [message_queue_empty]. *)
  Definition impl_message_queue_empty : function := {|
    f_args := [
      ("q", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_25 ;
        Return (LocInfoE loc_26 ((LocInfoE loc_27 (use{PtrOp} (LocInfoE loc_28 ((LocInfoE loc_29 (!{PtrOp} (LocInfoE loc_30 ("q")))) at{struct_message_queue} "first")))) ={PtrOp, PtrOp, i32} (LocInfoE loc_31 (NULL))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [message_queue_remove]. *)
  Definition impl_message_queue_remove (global_message_queue_empty : loc): function := {|
    f_args := [
      ("q", void*)
    ];
    f_local_vars := [
      ("head", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_34 ;
        assert{IntOp i32}: (LocInfoE loc_75 ((i2v 0 i32) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_77 (Call (LocInfoE loc_79 (global_message_queue_empty)) [@{expr} LocInfoE loc_80 (use{PtrOp} (LocInfoE loc_81 ("q"))) ])))) ;
        "head" <-{ PtrOp }
          LocInfoE loc_69 (use{PtrOp} (LocInfoE loc_70 ((LocInfoE loc_71 (!{PtrOp} (LocInfoE loc_72 ("q")))) at{struct_message_queue} "first"))) ;
        locinfo: loc_63 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_63 ((LocInfoE loc_64 (use{PtrOp} (LocInfoE loc_65 ((LocInfoE loc_66 (!{PtrOp} (LocInfoE loc_67 ("head")))) at{struct_message} "next")))) ={PtrOp, PtrOp, i32} (LocInfoE loc_68 (NULL)))
        then
        locinfo: loc_41 ;
          Goto "#2"
        else
        locinfo: loc_55 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_37 ;
        Return (LocInfoE loc_38 (use{PtrOp} (LocInfoE loc_39 ("head"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_41 ;
        LocInfoE loc_50 ((LocInfoE loc_51 (!{PtrOp} (LocInfoE loc_52 ("q")))) at{struct_message_queue} "first") <-{ PtrOp }
          LocInfoE loc_53 (NULL) ;
        locinfo: loc_42 ;
        LocInfoE loc_43 ((LocInfoE loc_44 (!{PtrOp} (LocInfoE loc_45 ("q")))) at{struct_message_queue} "last") <-{ PtrOp }
          LocInfoE loc_46 (&(LocInfoE loc_47 ((LocInfoE loc_48 (!{PtrOp} (LocInfoE loc_49 ("q")))) at{struct_message_queue} "first"))) ;
        locinfo: loc_37 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_55 ;
        LocInfoE loc_56 ((LocInfoE loc_57 (!{PtrOp} (LocInfoE loc_58 ("q")))) at{struct_message_queue} "first") <-{ PtrOp }
          LocInfoE loc_59 (use{PtrOp} (LocInfoE loc_60 ((LocInfoE loc_61 (!{PtrOp} (LocInfoE loc_62 ("head")))) at{struct_message} "next"))) ;
        locinfo: loc_37 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [prio_level_init]. *)
  Definition impl_prio_level_init : function := {|
    f_args := [
      ("bm", void*)
    ];
    f_local_vars := [
      ("lvl", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "lvl" <-{ IntOp i32 } LocInfoE loc_109 (i2v 0 i32) ;
        locinfo: loc_86 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_105 ;
        if{IntOp i32, None}: LocInfoE loc_105 ((LocInfoE loc_106 (use{IntOp i32} (LocInfoE loc_107 ("lvl")))) <{IntOp i32, IntOp i32, i32} (LocInfoE loc_108 (i2v 4 i32)))
        then
        locinfo: loc_88 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_88 ;
        LocInfoE loc_97 ((LocInfoE loc_99 ((LocInfoE loc_100 (!{PtrOp} (LocInfoE loc_101 ("bm")))) at{struct_prio_bitmap} "bits")) at_offset{it_layout u64, PtrOp, IntOp i32} (LocInfoE loc_102 (use{IntOp i32} (LocInfoE loc_103 ("lvl"))))) <-{ IntOp u64 }
          LocInfoE loc_104 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_104 (i2v 0 i32))) ;
        locinfo: loc_89 ;
        Goto "__cerb_continue0"
      ]> $
      <[ "#3" :=
        Return (VOID)
      ]> $
      <[ "__cerb_continue0" :=
        LocInfoE loc_91 ("lvl") <-{ IntOp i32 }
          LocInfoE loc_92 ((LocInfoE loc_93 (use{IntOp i32} (LocInfoE loc_94 ("lvl")))) +{IntOp i32, IntOp i32} (LocInfoE loc_95 (i2v 1 i32))) ;
        locinfo: loc_86 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [highest_pending_priority]. *)
  Definition impl_highest_pending_priority (global___builtin_ffsll : loc): function := {|
    f_args := [
      ("bm", void*)
    ];
    f_local_vars := [
      ("i", it_layout i32);
      ("first_bit", it_layout i32);
      ("offset", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "offset" <-{ IntOp i32 }
          LocInfoE loc_164 (UnOp NegOp (IntOp i32) (LocInfoE loc_165 (i2v 1 i32))) ;
        "i" <-{ IntOp i32 } LocInfoE loc_161 (i2v 0 i32) ;
        locinfo: loc_117 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_157 ;
        if{IntOp i32, None}: LocInfoE loc_157 ((LocInfoE loc_158 (use{IntOp i32} (LocInfoE loc_159 ("i")))) <{IntOp i32, IntOp i32, i32} (LocInfoE loc_160 (i2v 4 i32)))
        then
        Goto "#2"
        else
        locinfo: loc_118 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        "first_bit" <-{ IntOp i32 }
          LocInfoE loc_143 (Call (LocInfoE loc_145 (global___builtin_ffsll)) [@{expr} LocInfoE loc_146 (use{IntOp u64} (LocInfoE loc_148 ((LocInfoE loc_150 ((LocInfoE loc_151 (!{PtrOp} (LocInfoE loc_152 ("bm")))) at{struct_prio_bitmap} "bits")) at_offset{it_layout u64, PtrOp, IntOp i32} (LocInfoE loc_153 (use{IntOp i32} (LocInfoE loc_154 ("i"))))))) ]) ;
        locinfo: loc_141 ;
        if{IntOp i32, Some "#4"}: LocInfoE loc_141 (use{IntOp i32} (LocInfoE loc_142 ("first_bit")))
        then
        locinfo: loc_128 ;
          Goto "#5"
        else
        locinfo: loc_135 ;
          Goto "#6"
      ]> $
      <[ "#3" :=
        locinfo: loc_118 ;
        Return (LocInfoE loc_119 (UnOp NegOp (IntOp i32) (LocInfoE loc_120 (i2v 1 i32))))
      ]> $
      <[ "#4" :=
        locinfo: loc_124 ;
        Goto "__cerb_continue1"
      ]> $
      <[ "#5" :=
        locinfo: loc_128 ;
        Return (LocInfoE loc_129 ((LocInfoE loc_130 (use{IntOp i32} (LocInfoE loc_131 ("first_bit")))) +{IntOp i32, IntOp i32} (LocInfoE loc_132 (use{IntOp i32} (LocInfoE loc_133 ("offset"))))))
      ]> $
      <[ "#6" :=
        locinfo: loc_135 ;
        LocInfoE loc_136 ("offset") <-{ IntOp i32 }
          LocInfoE loc_137 ((LocInfoE loc_138 (use{IntOp i32} (LocInfoE loc_139 ("offset")))) +{IntOp i32, IntOp i32} (LocInfoE loc_140 (i2v 64 i32))) ;
        locinfo: loc_124 ;
        Goto "#4"
      ]> $
      <[ "__cerb_continue1" :=
        LocInfoE loc_126 ("i") <-{ IntOp i32 }
          (use{IntOp i32} (LocInfoE loc_126 ("i"))) +{IntOp i32, IntOp i32} (i2v 1 i32) ;
        locinfo: loc_117 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [priority_search_none_found]. *)
  Definition impl_priority_search_none_found : function := {|
    f_args := [
      ("result", it_layout i32)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_170 ;
        Return (LocInfoE loc_171 ((LocInfoE loc_172 (use{IntOp i32} (LocInfoE loc_173 ("result")))) <{IntOp i32, IntOp i32, i32} (LocInfoE loc_174 (i2v 0 i32))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [priority_level_set]. *)
  Definition impl_priority_level_set : function := {|
    f_args := [
      ("bm", void*);
      ("prio", it_layout u8)
    ];
    f_local_vars := [
      ("bit", it_layout u8);
      ("word", it_layout u8)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "word" <-{ IntOp u8 }
          LocInfoE loc_209 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_209 ((LocInfoE loc_210 (UnOp (CastOp $ IntOp i32) (IntOp u8) (LocInfoE loc_210 (use{IntOp u8} (LocInfoE loc_211 ("prio")))))) /{IntOp i32, IntOp i32} (LocInfoE loc_212 (i2v 64 i32))))) ;
        "bit" <-{ IntOp u8 }
          LocInfoE loc_203 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_203 ((LocInfoE loc_204 (UnOp (CastOp $ IntOp i32) (IntOp u8) (LocInfoE loc_204 (use{IntOp u8} (LocInfoE loc_205 ("prio")))))) %{IntOp i32, IntOp i32} (LocInfoE loc_206 (i2v 64 i32))))) ;
        locinfo: loc_179 ;
        LocInfoE loc_181 ((LocInfoE loc_183 ((LocInfoE loc_184 (!{PtrOp} (LocInfoE loc_185 ("bm")))) at{struct_prio_bitmap} "bits")) at_offset{it_layout u64, PtrOp, IntOp u8} (LocInfoE loc_186 (use{IntOp u8} (LocInfoE loc_187 ("word"))))) <-{ IntOp u64 }
          LocInfoE loc_188 ((LocInfoE loc_189 (use{IntOp u64} (LocInfoE loc_191 ((LocInfoE loc_193 ((LocInfoE loc_194 (!{PtrOp} (LocInfoE loc_195 ("bm")))) at{struct_prio_bitmap} "bits")) at_offset{it_layout u64, PtrOp, IntOp u8} (LocInfoE loc_196 (use{IntOp u8} (LocInfoE loc_197 ("word")))))))) |{IntOp u64, IntOp u64} (LocInfoE loc_198 ((LocInfoE loc_199 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_200 (i2v 1 i32)))) <<{IntOp u64, IntOp u64} (LocInfoE loc_201 (UnOp (CastOp $ IntOp u64) (IntOp u8) (LocInfoE loc_201 (use{IntOp u8} (LocInfoE loc_202 ("bit"))))))))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [priority_level_clear]. *)
  Definition impl_priority_level_clear : function := {|
    f_args := [
      ("bm", void*);
      ("prio", it_layout u8)
    ];
    f_local_vars := [
      ("bit", it_layout u8);
      ("word", it_layout u8)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "word" <-{ IntOp u8 }
          LocInfoE loc_250 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_250 ((LocInfoE loc_251 (UnOp (CastOp $ IntOp i32) (IntOp u8) (LocInfoE loc_251 (use{IntOp u8} (LocInfoE loc_252 ("prio")))))) /{IntOp i32, IntOp i32} (LocInfoE loc_253 (i2v 64 i32))))) ;
        "bit" <-{ IntOp u8 }
          LocInfoE loc_244 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_244 ((LocInfoE loc_245 (UnOp (CastOp $ IntOp i32) (IntOp u8) (LocInfoE loc_245 (use{IntOp u8} (LocInfoE loc_246 ("prio")))))) %{IntOp i32, IntOp i32} (LocInfoE loc_247 (i2v 64 i32))))) ;
        locinfo: loc_219 ;
        LocInfoE loc_221 ((LocInfoE loc_223 ((LocInfoE loc_224 (!{PtrOp} (LocInfoE loc_225 ("bm")))) at{struct_prio_bitmap} "bits")) at_offset{it_layout u64, PtrOp, IntOp u8} (LocInfoE loc_226 (use{IntOp u8} (LocInfoE loc_227 ("word"))))) <-{ IntOp u64 }
          LocInfoE loc_228 ((LocInfoE loc_229 (use{IntOp u64} (LocInfoE loc_231 ((LocInfoE loc_233 ((LocInfoE loc_234 (!{PtrOp} (LocInfoE loc_235 ("bm")))) at{struct_prio_bitmap} "bits")) at_offset{it_layout u64, PtrOp, IntOp u8} (LocInfoE loc_236 (use{IntOp u8} (LocInfoE loc_237 ("word")))))))) &{IntOp u64, IntOp u64} (LocInfoE loc_238 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_239 ((LocInfoE loc_240 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_241 (i2v 1 i32)))) <<{IntOp u64, IntOp u64} (LocInfoE loc_242 (UnOp (CastOp $ IntOp u64) (IntOp u8) (LocInfoE loc_242 (use{IntOp u8} (LocInfoE loc_243 ("bit"))))))))))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [npfp_enqueue]. *)
  Definition impl_npfp_enqueue (global_message_identify_type global_message_queue_add global_priority_level_set : loc): function := {|
    f_args := [
      ("sched", void*);
      ("msg", void*)
    ];
    f_local_vars := [
      ("msg_prio", it_layout u8)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_258 ;
        LocInfoE loc_297 ((LocInfoE loc_298 (!{PtrOp} (LocInfoE loc_299 ("msg")))) at{struct_message} "type") <-{ IntOp u8 }
          LocInfoE loc_300 (Call (LocInfoE loc_302 (global_message_identify_type)) [@{expr} LocInfoE loc_303 (use{PtrOp} (LocInfoE loc_304 ("msg"))) ]) ;
        "msg_prio" <-{ IntOp u8 }
          LocInfoE loc_283 (use{IntOp u8} (LocInfoE loc_284 ((LocInfoE loc_286 ((LocInfoE loc_288 ((LocInfoE loc_289 (!{PtrOp} (LocInfoE loc_290 ("sched")))) at{struct_npfp_scheduler} "callbacks")) at_offset{layout_of struct_callback, PtrOp, IntOp u8} (LocInfoE loc_291 (use{IntOp u8} (LocInfoE loc_292 ((LocInfoE loc_293 (!{PtrOp} (LocInfoE loc_294 ("msg")))) at{struct_message} "type")))))) at{struct_callback} "prio"))) ;
        locinfo: loc_260 ;
        expr: (LocInfoE loc_260 (Call (LocInfoE loc_271 (global_message_queue_add)) [@{expr} LocInfoE loc_272 (&(LocInfoE loc_274 ((LocInfoE loc_276 ((LocInfoE loc_277 (!{PtrOp} (LocInfoE loc_278 ("sched")))) at{struct_npfp_scheduler} "pending")) at_offset{layout_of struct_message_queue, PtrOp, IntOp u8} (LocInfoE loc_279 (use{IntOp u8} (LocInfoE loc_280 ("msg_prio"))))))) ;
        LocInfoE loc_281 (use{PtrOp} (LocInfoE loc_282 ("msg"))) ])) ;
        locinfo: loc_261 ;
        expr: (LocInfoE loc_261 (Call (LocInfoE loc_263 (global_priority_level_set)) [@{expr} LocInfoE loc_264 (&(LocInfoE loc_265 ((LocInfoE loc_266 (!{PtrOp} (LocInfoE loc_267 ("sched")))) at{struct_npfp_scheduler} "prio_levels"))) ;
        LocInfoE loc_268 (use{IntOp u8} (LocInfoE loc_269 ("msg_prio"))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [npfp_dequeue]. *)
  Definition impl_npfp_dequeue (global_highest_pending_priority global_message_queue_empty global_message_queue_remove global_priority_level_clear global_priority_search_none_found : loc): function := {|
    f_args := [
      ("sched", void*)
    ];
    f_local_vars := [
      ("msg", void*);
      ("top_prio", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "top_prio" <-{ IntOp i32 }
          LocInfoE loc_359 (Call (LocInfoE loc_361 (global_highest_pending_priority)) [@{expr} LocInfoE loc_362 (&(LocInfoE loc_363 ((LocInfoE loc_364 (!{PtrOp} (LocInfoE loc_365 ("sched")))) at{struct_npfp_scheduler} "prio_levels"))) ]) ;
        locinfo: loc_354 ;
        if{IntOp i32, None}: LocInfoE loc_354 (Call (LocInfoE loc_356 (global_priority_search_none_found)) [@{expr} LocInfoE loc_357 (use{IntOp i32} (LocInfoE loc_358 ("top_prio"))) ])
        then
        locinfo: loc_309 ;
          Goto "#1"
        else
        Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_309 ;
        Return (LocInfoE loc_310 (NULL))
      ]> $
      <[ "#2" :=
        "msg" <-{ PtrOp }
          LocInfoE loc_340 (Call (LocInfoE loc_342 (global_message_queue_remove)) [@{expr} LocInfoE loc_343 (&(LocInfoE loc_345 ((LocInfoE loc_347 ((LocInfoE loc_348 (!{PtrOp} (LocInfoE loc_349 ("sched")))) at{struct_npfp_scheduler} "pending")) at_offset{layout_of struct_message_queue, PtrOp, IntOp i32} (LocInfoE loc_350 (use{IntOp i32} (LocInfoE loc_351 ("top_prio"))))))) ]) ;
        locinfo: loc_328 ;
        if{IntOp i32, Some "#3"}: LocInfoE loc_328 (Call (LocInfoE loc_330 (global_message_queue_empty)) [@{expr} LocInfoE loc_331 (&(LocInfoE loc_333 ((LocInfoE loc_335 ((LocInfoE loc_336 (!{PtrOp} (LocInfoE loc_337 ("sched")))) at{struct_npfp_scheduler} "pending")) at_offset{layout_of struct_message_queue, PtrOp, IntOp i32} (LocInfoE loc_338 (use{IntOp i32} (LocInfoE loc_339 ("top_prio"))))))) ])
        then
        locinfo: loc_318 ;
          Goto "#4"
        else
        locinfo: loc_314 ;
          Goto "#5"
      ]> $
      <[ "#3" :=
        locinfo: loc_314 ;
        Return (LocInfoE loc_315 (use{PtrOp} (LocInfoE loc_316 ("msg"))))
      ]> $
      <[ "#4" :=
        locinfo: loc_318 ;
        expr: (LocInfoE loc_318 (Call (LocInfoE loc_320 (global_priority_level_clear)) [@{expr} LocInfoE loc_321 (&(LocInfoE loc_322 ((LocInfoE loc_323 (!{PtrOp} (LocInfoE loc_324 ("sched")))) at{struct_npfp_scheduler} "prio_levels"))) ;
        LocInfoE loc_325 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_325 (use{IntOp i32} (LocInfoE loc_326 ("top_prio"))))) ])) ;
        locinfo: loc_314 ;
        Goto "#3"
      ]> $
      <[ "#5" :=
        locinfo: loc_314 ;
        Goto "#3"
      ]> $∅
    )%E
  |}.

  (* Definition of function [npfp_dispatch]. *)
  Definition impl_npfp_dispatch : function := {|
    f_args := [
      ("sched", void*);
      ("msg", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_370 ;
        Return (LocInfoE loc_371 (Call (LocInfoE loc_373 (use{PtrOp} (LocInfoE loc_374 ((LocInfoE loc_376 ((LocInfoE loc_378 ((LocInfoE loc_379 (!{PtrOp} (LocInfoE loc_380 ("sched")))) at{struct_npfp_scheduler} "callbacks")) at_offset{layout_of struct_callback, PtrOp, IntOp u8} (LocInfoE loc_381 (use{IntOp u8} (LocInfoE loc_382 ((LocInfoE loc_383 (!{PtrOp} (LocInfoE loc_384 ("msg")))) at{struct_message} "type")))))) at{struct_callback} "f")))) [@{expr} LocInfoE loc_385 (use{PtrOp} (LocInfoE loc_386 ("msg"))) ]))
      ]> $∅
    )%E
  |}.

  (* Definition of function [fds_init]. *)
  Definition impl_fds_init (global_nop_callback global_prio_level_init : loc): function := {|
    f_args := [
      ("fds", void*)
    ];
    f_local_vars := [
      ("prio", it_layout i32);
      ("typ", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_389 ;
        LocInfoE loc_490 ((LocInfoE loc_491 (!{PtrOp} (LocInfoE loc_492 ("fds")))) at{struct_fd_scheduler} "num_channels") <-{ IntOp u64 }
          LocInfoE loc_493 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_493 (i2v 0 i32))) ;
        locinfo: loc_390 ;
        expr: (LocInfoE loc_390 (Call (LocInfoE loc_484 (global_prio_level_init)) [@{expr} LocInfoE loc_485 (&(LocInfoE loc_486 ((LocInfoE loc_487 ((LocInfoE loc_488 (!{PtrOp} (LocInfoE loc_489 ("fds")))) at{struct_fd_scheduler} "sched")) at{struct_npfp_scheduler} "prio_levels"))) ])) ;
        "typ" <-{ IntOp i32 } LocInfoE loc_480 (i2v 0 i32) ;
        locinfo: loc_393 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_474 ;
        if{IntOp i32, None}: LocInfoE loc_474 ((LocInfoE loc_475 (use{IntOp i32} (LocInfoE loc_476 ("typ")))) <{IntOp i32, IntOp i32, i32} (LocInfoE loc_477 ((LocInfoE loc_478 (UnOp (CastOp $ IntOp i32) (IntOp u8) (LocInfoE loc_478 (i2v (max_int u8) u8)))) +{IntOp i32, IntOp i32} (LocInfoE loc_479 (i2v 1 i32)))))
        then
        locinfo: loc_452 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_452 ;
        LocInfoE loc_461 ((LocInfoE loc_463 ((LocInfoE loc_464 ((LocInfoE loc_465 (!{PtrOp} (LocInfoE loc_466 ("fds")))) at{struct_fd_scheduler} "sched")) at{struct_npfp_scheduler} "callbacks")) at_offset{layout_of struct_callback, PtrOp, IntOp i32} (LocInfoE loc_467 (use{IntOp i32} (LocInfoE loc_468 ("typ"))))) <-{ StructOp struct_callback ([ IntOp u8 ; PtrOp ]) }
          StructInit struct_callback [
            ("prio", LocInfoE loc_472 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_472 (i2v 0 i32))) : expr) ;
            ("f", LocInfoE loc_473 (global_nop_callback) : expr)
          ] ;
        locinfo: loc_453 ;
        Goto "__cerb_continue3"
      ]> $
      <[ "#3" :=
        "prio" <-{ IntOp i32 } LocInfoE loc_448 (i2v 0 i32) ;
        locinfo: loc_396 ;
        Goto "#4"
      ]> $
      <[ "#4" :=
        locinfo: loc_442 ;
        if{IntOp i32, None}: LocInfoE loc_442 ((LocInfoE loc_443 (use{IntOp i32} (LocInfoE loc_444 ("prio")))) <{IntOp i32, IntOp i32, i32} (LocInfoE loc_445 ((LocInfoE loc_446 (UnOp (CastOp $ IntOp i32) (IntOp u8) (LocInfoE loc_446 (i2v (max_int u8) u8)))) +{IntOp i32, IntOp i32} (LocInfoE loc_447 (i2v 1 i32)))))
        then
        locinfo: loc_398 ;
          Goto "#5"
        else
        Goto "#6"
      ]> $
      <[ "#5" :=
        locinfo: loc_398 ;
        LocInfoE loc_429 ((LocInfoE loc_431 ((LocInfoE loc_432 ((LocInfoE loc_433 (!{PtrOp} (LocInfoE loc_434 ("fds")))) at{struct_fd_scheduler} "sched")) at{struct_npfp_scheduler} "pending")) at_offset{layout_of struct_message_queue, PtrOp, IntOp i32} (LocInfoE loc_435 (use{IntOp i32} (LocInfoE loc_436 ("prio"))))) <-{ StructOp struct_message_queue ([ PtrOp ; PtrOp ]) }
          StructInit struct_message_queue [
            ("first", LocInfoE loc_440 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_440 (NULL))) : expr) ;
            ("last", LocInfoE loc_441 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_441 (NULL))) : expr)
          ] ;
        locinfo: loc_399 ;
        LocInfoE loc_407 ((LocInfoE loc_409 ((LocInfoE loc_411 ((LocInfoE loc_412 ((LocInfoE loc_413 (!{PtrOp} (LocInfoE loc_414 ("fds")))) at{struct_fd_scheduler} "sched")) at{struct_npfp_scheduler} "pending")) at_offset{layout_of struct_message_queue, PtrOp, IntOp i32} (LocInfoE loc_415 (use{IntOp i32} (LocInfoE loc_416 ("prio")))))) at{struct_message_queue} "last") <-{ PtrOp }
          LocInfoE loc_417 (&(LocInfoE loc_418 ((LocInfoE loc_420 ((LocInfoE loc_422 ((LocInfoE loc_423 ((LocInfoE loc_424 (!{PtrOp} (LocInfoE loc_425 ("fds")))) at{struct_fd_scheduler} "sched")) at{struct_npfp_scheduler} "pending")) at_offset{layout_of struct_message_queue, PtrOp, IntOp i32} (LocInfoE loc_426 (use{IntOp i32} (LocInfoE loc_427 ("prio")))))) at{struct_message_queue} "first"))) ;
        locinfo: loc_400 ;
        Goto "__cerb_continue4"
      ]> $
      <[ "#6" :=
        Return (VOID)
      ]> $
      <[ "__cerb_continue3" :=
        LocInfoE loc_455 ("typ") <-{ IntOp i32 }
          LocInfoE loc_456 ((LocInfoE loc_457 (use{IntOp i32} (LocInfoE loc_458 ("typ")))) +{IntOp i32, IntOp i32} (LocInfoE loc_459 (i2v 1 i32))) ;
        locinfo: loc_393 ;
        Goto "#1"
      ]> $
      <[ "__cerb_continue4" :=
        LocInfoE loc_402 ("prio") <-{ IntOp i32 }
          LocInfoE loc_403 ((LocInfoE loc_404 (use{IntOp i32} (LocInfoE loc_405 ("prio")))) +{IntOp i32, IntOp i32} (LocInfoE loc_406 (i2v 1 i32))) ;
        locinfo: loc_396 ;
        Goto "#4"
      ]> $∅
    )%E
  |}.

  (* Definition of function [fds_add_channel]. *)
  Definition impl_fds_add_channel (global_fcntl : loc): function := {|
    f_args := [
      ("fds", void*);
      ("fd", it_layout i32)
    ];
    f_local_vars := [
      ("err", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_496 ;
        assert{IntOp i32}: (LocInfoE loc_533 ((LocInfoE loc_534 (use{IntOp u64} (LocInfoE loc_535 ((LocInfoE loc_536 (!{PtrOp} (LocInfoE loc_537 ("fds")))) at{struct_fd_scheduler} "num_channels")))) <{IntOp u64, IntOp u64, i32} (LocInfoE loc_538 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_538 (i2v 16 i32)))))) ;
        "err" <-{ IntOp i32 }
          LocInfoE loc_524 (Call (LocInfoE loc_526 (global_fcntl)) [@{expr} LocInfoE loc_527 (use{IntOp i32} (LocInfoE loc_528 ("fd"))) ;
          LocInfoE loc_529 (i2v 4 i32) ; LocInfoE loc_530 (i2v 2048 i32) ]) ;
        locinfo: loc_522 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_522 (use{IntOp i32} (LocInfoE loc_523 ("err")))
        then
        locinfo: loc_518 ;
          Goto "#2"
        else
        locinfo: loc_499 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_499 ;
        LocInfoE loc_507 ((LocInfoE loc_509 ((LocInfoE loc_510 (!{PtrOp} (LocInfoE loc_511 ("fds")))) at{struct_fd_scheduler} "input_channels")) at_offset{it_layout i32, PtrOp, IntOp u64} (LocInfoE loc_512 (use{IntOp u64} (LocInfoE loc_513 ((LocInfoE loc_514 (!{PtrOp} (LocInfoE loc_515 ("fds")))) at{struct_fd_scheduler} "num_channels"))))) <-{ IntOp i32 }
          LocInfoE loc_516 (use{IntOp i32} (LocInfoE loc_517 ("fd"))) ;
        locinfo: loc_500 ;
        LocInfoE loc_503 ((LocInfoE loc_504 (!{PtrOp} (LocInfoE loc_505 ("fds")))) at{struct_fd_scheduler} "num_channels") <-{ IntOp u64 }
          LocInfoE loc_500 ((LocInfoE loc_500 (use{IntOp u64} (LocInfoE loc_503 ((LocInfoE loc_504 (!{PtrOp} (LocInfoE loc_505 ("fds")))) at{struct_fd_scheduler} "num_channels")))) +{IntOp u64, IntOp u64} (LocInfoE loc_500 (i2v 1 u64))) ;
        locinfo: loc_501 ;
        Return (LocInfoE loc_502 (i2v 0 i32))
      ]> $
      <[ "#2" :=
        locinfo: loc_518 ;
        Return (LocInfoE loc_519 (use{IntOp i32} (LocInfoE loc_520 ("err"))))
      ]> $
      <[ "#3" :=
        locinfo: loc_499 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [fds_set_callback]. *)
  Definition impl_fds_set_callback : function := {|
    f_args := [
      ("fds", void*);
      ("type", it_layout u8);
      ("f", void*);
      ("prio", it_layout u8)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_541 ;
        LocInfoE loc_543 ((LocInfoE loc_545 ((LocInfoE loc_546 ((LocInfoE loc_547 (!{PtrOp} (LocInfoE loc_548 ("fds")))) at{struct_fd_scheduler} "sched")) at{struct_npfp_scheduler} "callbacks")) at_offset{layout_of struct_callback, PtrOp, IntOp u8} (LocInfoE loc_549 (use{IntOp u8} (LocInfoE loc_550 ("type"))))) <-{ StructOp struct_callback ([ IntOp u8 ; PtrOp ]) }
          StructInit struct_callback [
            ("prio", LocInfoE loc_554 (use{IntOp u8} (LocInfoE loc_555 ("prio"))) : expr) ;
            ("f", LocInfoE loc_556 (use{PtrOp} (LocInfoE loc_557 ("f"))) : expr)
          ] ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [fds_run]. *)
  Definition impl_fds_run (global_check_channels_until_empty global_free global_npfp_dequeue global_npfp_dispatch : loc): function := {|
    f_args := [
      ("fds", void*)
    ];
    f_local_vars := [
      ("msg", void*);
      ("err", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_561 ;
        assert{IntOp i32}: (LocInfoE loc_619 ((LocInfoE loc_620 (use{IntOp u64} (LocInfoE loc_621 ((LocInfoE loc_622 (!{PtrOp} (LocInfoE loc_623 ("fds")))) at{struct_fd_scheduler} "num_channels")))) >{IntOp u64, IntOp u64, i32} (LocInfoE loc_624 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_624 (i2v 0 i32)))))) ;
        locinfo: loc_562 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_618 ;
        if{IntOp i32, None}: LocInfoE loc_618 (i2v 1 i32)
        then
        locinfo: loc_564 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#10" :=
        locinfo: loc_562 ;
        Goto "#6"
      ]> $
      <[ "#11" :=
        locinfo: loc_570 ;
        Goto "#7"
      ]> $
      <[ "#2" :=
        locinfo: loc_564 ;
        Goto "#5"
      ]> $
      <[ "#3" :=
        Return (VOID)
      ]> $
      <[ "#4" :=
        locinfo: loc_614 ;
        if{IntOp i32, None}: LocInfoE loc_614 ((i2v 0 i32) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_616 (use{IntOp i32} (LocInfoE loc_617 ("err")))))
        then
        locinfo: loc_564 ;
          Goto "#5"
        else
        locinfo: loc_562 ;
          Goto "#6"
      ]> $
      <[ "#5" :=
        locinfo: loc_567 ;
        LocInfoE loc_608 ("err") <-{ IntOp i32 }
          LocInfoE loc_609 (Call (LocInfoE loc_611 (global_check_channels_until_empty)) [@{expr} LocInfoE loc_612 (use{PtrOp} (LocInfoE loc_613 ("fds"))) ]) ;
        "msg" <-{ PtrOp }
          LocInfoE loc_599 (Call (LocInfoE loc_601 (global_npfp_dequeue)) [@{expr} LocInfoE loc_602 (&(LocInfoE loc_603 ((LocInfoE loc_604 (!{PtrOp} (LocInfoE loc_605 ("fds")))) at{struct_fd_scheduler} "sched"))) ]) ;
        locinfo: loc_595 ;
        if{IntOp i32, Some "#7"}: LocInfoE loc_595 ((UnOp (CastOp $ PtrOp) (IntOp i32) (i2v 0 i32)) ={PtrOp, PtrOp, i32} (LocInfoE loc_597 (use{PtrOp} (LocInfoE loc_598 ("msg")))))
        then
        locinfo: loc_562 ;
          Goto "#10"
        else
        locinfo: loc_570 ;
          Goto "#11"
      ]> $
      <[ "#6" :=
        locinfo: loc_562 ;
        Goto "#1"
      ]> $
      <[ "#7" :=
        locinfo: loc_570 ;
        LocInfoE loc_583 ("err") <-{ IntOp i32 }
          LocInfoE loc_584 (Call (LocInfoE loc_586 (global_npfp_dispatch)) [@{expr} LocInfoE loc_587 (&(LocInfoE loc_588 ((LocInfoE loc_589 (!{PtrOp} (LocInfoE loc_590 ("fds")))) at{struct_fd_scheduler} "sched"))) ;
          LocInfoE loc_591 (use{PtrOp} (LocInfoE loc_592 ("msg"))) ]) ;
        locinfo: loc_571 ;
        expr: (LocInfoE loc_571 (Call (LocInfoE loc_580 (global_free)) [@{expr} LocInfoE loc_581 (use{PtrOp} (LocInfoE loc_582 ("msg"))) ])) ;
        locinfo: loc_577 ;
        if{IntOp i32, None}: LocInfoE loc_577 (use{IntOp i32} (LocInfoE loc_578 ("err")))
        then
        locinfo: loc_573 ;
          Goto "#8"
        else
        Goto "#9"
      ]> $
      <[ "#8" :=
        locinfo: loc_573 ;
        Return (LocInfoE loc_574 (use{IntOp i32} (LocInfoE loc_575 ("err"))))
      ]> $
      <[ "#9" :=
        Goto "#4"
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
        locinfo: loc_627 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_631 ;
        if{IntOp i32, None}: LocInfoE loc_631 (i2v 1 i32)
        then
        locinfo: loc_627 ;
          Goto "#2"
        else
        locinfo: loc_628 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_627 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_628 ;
        Return (LocInfoE loc_629 (i2v 0 i32))
      ]> $∅
    )%E
  |}.

  (* Definition of function [xmalloc]. *)
  Definition impl_xmalloc (global_malloc global_safe_exit : loc): function := {|
    f_args := [
      ("sz", it_layout size_t)
    ];
    f_local_vars := [
      ("p", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "p" <-{ PtrOp }
          LocInfoE loc_648 (Call (LocInfoE loc_650 (global_malloc)) [@{expr} LocInfoE loc_651 (use{IntOp size_t} (LocInfoE loc_652 ("sz"))) ]) ;
        locinfo: loc_644 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_644 ((LocInfoE loc_645 (use{PtrOp} (LocInfoE loc_646 ("p")))) ={PtrOp, PtrOp, i32} (LocInfoE loc_647 (NULL)))
        then
        locinfo: loc_640 ;
          Goto "#2"
        else
        locinfo: loc_636 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_636 ;
        Return (LocInfoE loc_637 (use{PtrOp} (LocInfoE loc_638 ("p"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_640 ;
        expr: (LocInfoE loc_640 (Call (LocInfoE loc_642 (global_safe_exit)) [@{expr}  ])) ;
        locinfo: loc_636 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_636 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [nop_callback]. *)
  Definition impl_nop_callback : function := {|
    f_args := [
      ("_", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_657 ;
        Return (LocInfoE loc_658 (i2v 0 i32))
      ]> $∅
    )%E
  |}.

  (* Definition of function [receive_one_message]. *)
  Definition impl_receive_one_message (global_free global_npfp_enqueue global_read global_xmalloc : loc): function := {|
    f_args := [
      ("fds", void*);
      ("fd", it_layout i32)
    ];
    f_local_vars := [
      ("msg", void*);
      ("n", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "msg" <-{ PtrOp }
          LocInfoE loc_716 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_716 (Call (LocInfoE loc_718 (global_xmalloc)) [@{expr} LocInfoE loc_719 (i2v (layout_of struct_message).(ly_size) size_t) ]))) ;
        locinfo: loc_662 ;
        assert{PtrOp}: (LocInfoE loc_714 (use{PtrOp} (LocInfoE loc_715 ("msg")))) ;
        "n" <-{ IntOp i32 }
          LocInfoE loc_696 (UnOp (CastOp $ IntOp i32) (IntOp i64) (LocInfoE loc_696 (Call (LocInfoE loc_698 (global_read)) [@{expr} LocInfoE loc_699 (use{IntOp i32} (LocInfoE loc_700 ("fd"))) ;
          LocInfoE loc_701 (&(LocInfoE loc_702 ((LocInfoE loc_703 (!{PtrOp} (LocInfoE loc_704 ("msg")))) at{struct_message} "data"))) ;
          LocInfoE loc_705 ((LocInfoE loc_706 ((LocInfoE loc_707 ((LocInfoE loc_708 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_708 (i2v 4096 i32)))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_709 (i2v (it_layout u8).(ly_size) size_t)))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_710 (i2v (it_layout size_t).(ly_size) size_t)))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_711 (i2v (void*).(ly_size) size_t))) ]))) ;
        locinfo: loc_692 ;
        if{IntOp i32, None}: LocInfoE loc_692 ((LocInfoE loc_693 (use{IntOp i32} (LocInfoE loc_694 ("n")))) <{IntOp i32, IntOp i32, i32} (LocInfoE loc_695 (i2v 0 i32)))
        then
        locinfo: loc_666 ;
          Goto "#1"
        else
        locinfo: loc_675 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_666 ;
        expr: (LocInfoE loc_666 (Call (LocInfoE loc_671 (global_free)) [@{expr} LocInfoE loc_672 (use{PtrOp} (LocInfoE loc_673 ("msg"))) ])) ;
        locinfo: loc_667 ;
        Return (LocInfoE loc_668 (use{IntOp i32} (LocInfoE loc_669 ("n"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_675 ;
        LocInfoE loc_687 ((LocInfoE loc_688 (!{PtrOp} (LocInfoE loc_689 ("msg")))) at{struct_message} "len") <-{ IntOp size_t }
          LocInfoE loc_690 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_690 (use{IntOp i32} (LocInfoE loc_691 ("n"))))) ;
        locinfo: loc_676 ;
        expr: (LocInfoE loc_676 (Call (LocInfoE loc_680 (global_npfp_enqueue)) [@{expr} LocInfoE loc_681 (&(LocInfoE loc_682 ((LocInfoE loc_683 (!{PtrOp} (LocInfoE loc_684 ("fds")))) at{struct_fd_scheduler} "sched"))) ;
        LocInfoE loc_685 (use{PtrOp} (LocInfoE loc_686 ("msg"))) ])) ;
        locinfo: loc_677 ;
        Return (LocInfoE loc_678 (i2v 0 i32))
      ]> $∅
    )%E
  |}.

  (* Definition of function [receive_messages]. *)
  Definition impl_receive_messages (global___builtin_errno global_receive_one_message : loc): function := {|
    f_args := [
      ("fds", void*);
      ("fd", it_layout i32)
    ];
    f_local_vars := [
      ("err", it_layout i32);
      ("non_empty", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "non_empty" <-{ IntOp i32 } LocInfoE loc_773 (i2v 0 i32) ;
        locinfo: loc_726 ;
        Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_769 ;
        if{IntOp i32, None}: LocInfoE loc_769 ((i2v 0 i32) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_771 (use{IntOp i32} (LocInfoE loc_772 ("err")))))
        then
        locinfo: loc_726 ;
          Goto "#2"
        else
        locinfo: loc_734 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_751 ;
        LocInfoE loc_761 ("err") <-{ IntOp i32 }
          LocInfoE loc_762 (Call (LocInfoE loc_764 (global_receive_one_message)) [@{expr} LocInfoE loc_765 (use{PtrOp} (LocInfoE loc_766 ("fds"))) ;
          LocInfoE loc_767 (use{IntOp i32} (LocInfoE loc_768 ("fd"))) ]) ;
        locinfo: loc_757 ;
        if{IntOp i32, None}: LocInfoE loc_757 ((i2v 0 i32) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_759 (use{IntOp i32} (LocInfoE loc_760 ("err")))))
        then
        locinfo: loc_753 ;
          Goto "#6"
        else
        Goto "#7"
      ]> $
      <[ "#3" :=
        locinfo: loc_734 ;
        if{IntOp i32, None}: LocInfoE loc_734 ((LocInfoE loc_735 ((LocInfoE loc_736 (use{IntOp i32} (LocInfoE loc_738 (LValue (LocInfoE loc_738 (Call (LocInfoE loc_740 (global___builtin_errno)) [@{expr}  ])))))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_741 (i2v 80 i32)))) ||{IntOp i32, IntOp i32, i32} (LocInfoE loc_742 ((LocInfoE loc_743 (use{IntOp i32} (LocInfoE loc_745 (LValue (LocInfoE loc_745 (Call (LocInfoE loc_747 (global___builtin_errno)) [@{expr}  ])))))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_748 (i2v 9 i32)))))
        then
        locinfo: loc_728 ;
          Goto "#4"
        else
        locinfo: loc_731 ;
          Goto "#5"
      ]> $
      <[ "#4" :=
        locinfo: loc_728 ;
        Return (LocInfoE loc_729 (use{IntOp i32} (LocInfoE loc_730 ("non_empty"))))
      ]> $
      <[ "#5" :=
        locinfo: loc_731 ;
        Return (LocInfoE loc_732 (use{IntOp i32} (LocInfoE loc_733 ("err"))))
      ]> $
      <[ "#6" :=
        locinfo: loc_753 ;
        LocInfoE loc_754 ("non_empty") <-{ IntOp i32 }
          LocInfoE loc_755 (i2v 1 i32) ;
        Goto "#1"
      ]> $
      <[ "#7" :=
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [check_channels]. *)
  Definition impl_check_channels (global_receive_messages : loc): function := {|
    f_args := [
      ("fds", void*)
    ];
    f_local_vars := [
      ("ch", it_layout u64);
      ("fd", it_layout i32);
      ("flag", it_layout i32);
      ("err", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "flag" <-{ IntOp i32 } LocInfoE loc_837 (i2v 0 i32) ;
        "ch" <-{ IntOp u64 }
          LocInfoE loc_834 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_834 (i2v 0 i32))) ;
        locinfo: loc_781 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_827 ;
        if{IntOp i32, None}: LocInfoE loc_827 ((LocInfoE loc_828 (use{IntOp u64} (LocInfoE loc_829 ("ch")))) <{IntOp u64, IntOp u64, i32} (LocInfoE loc_830 (use{IntOp u64} (LocInfoE loc_831 ((LocInfoE loc_832 (!{PtrOp} (LocInfoE loc_833 ("fds")))) at{struct_fd_scheduler} "num_channels")))))
        then
        locinfo: loc_786 ;
          Goto "#2"
        else
        locinfo: loc_782 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_786 ;
        LocInfoE loc_817 ("fd") <-{ IntOp i32 }
          LocInfoE loc_818 (use{IntOp i32} (LocInfoE loc_820 ((LocInfoE loc_822 ((LocInfoE loc_823 (!{PtrOp} (LocInfoE loc_824 ("fds")))) at{struct_fd_scheduler} "input_channels")) at_offset{it_layout i32, PtrOp, IntOp u64} (LocInfoE loc_825 (use{IntOp u64} (LocInfoE loc_826 ("ch"))))))) ;
        locinfo: loc_787 ;
        LocInfoE loc_809 ("err") <-{ IntOp i32 }
          LocInfoE loc_810 (Call (LocInfoE loc_812 (global_receive_messages)) [@{expr} LocInfoE loc_813 (use{PtrOp} (LocInfoE loc_814 ("fds"))) ;
          LocInfoE loc_815 (use{IntOp i32} (LocInfoE loc_816 ("fd"))) ]) ;
        locinfo: loc_805 ;
        if{IntOp i32, Some "#4"}: LocInfoE loc_805 ((LocInfoE loc_806 (use{IntOp i32} (LocInfoE loc_807 ("err")))) <{IntOp i32, IntOp i32, i32} (LocInfoE loc_808 (i2v 0 i32)))
        then
        locinfo: loc_801 ;
          Goto "#8"
        else
        locinfo: loc_797 ;
          Goto "#9"
      ]> $
      <[ "#3" :=
        locinfo: loc_782 ;
        Return (LocInfoE loc_783 (use{IntOp i32} (LocInfoE loc_784 ("flag"))))
      ]> $
      <[ "#4" :=
        locinfo: loc_797 ;
        if{IntOp i32, Some "#5"}: LocInfoE loc_797 ((LocInfoE loc_798 (use{IntOp i32} (LocInfoE loc_799 ("err")))) >{IntOp i32, IntOp i32, i32} (LocInfoE loc_800 (i2v 0 i32)))
        then
        locinfo: loc_793 ;
          Goto "#6"
        else
        locinfo: loc_790 ;
          Goto "#7"
      ]> $
      <[ "#5" :=
        locinfo: loc_790 ;
        Goto "__cerb_continue6"
      ]> $
      <[ "#6" :=
        locinfo: loc_793 ;
        LocInfoE loc_794 ("flag") <-{ IntOp i32 }
          LocInfoE loc_795 (i2v 1 i32) ;
        locinfo: loc_790 ;
        Goto "#5"
      ]> $
      <[ "#7" :=
        locinfo: loc_790 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        locinfo: loc_801 ;
        Return (LocInfoE loc_802 (use{IntOp i32} (LocInfoE loc_803 ("err"))))
      ]> $
      <[ "#9" :=
        locinfo: loc_797 ;
        Goto "#4"
      ]> $
      <[ "__cerb_continue6" :=
        LocInfoE loc_792 ("ch") <-{ IntOp u64 }
          (use{IntOp u64} (LocInfoE loc_792 ("ch"))) +{IntOp u64, IntOp u64} (i2v 1 u64) ;
        locinfo: loc_781 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [check_channels_until_empty]. *)
  Definition impl_check_channels_until_empty (global_check_channels : loc): function := {|
    f_args := [
      ("fds", void*)
    ];
    f_local_vars := [
      ("err", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_843 ;
        Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_865 ;
        if{IntOp i32, None}: LocInfoE loc_865 ((LocInfoE loc_866 (use{IntOp i32} (LocInfoE loc_867 ("err")))) >{IntOp i32, IntOp i32, i32} (LocInfoE loc_868 (i2v 0 i32)))
        then
        locinfo: loc_843 ;
          Goto "#2"
        else
        locinfo: loc_844 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_849 ;
        LocInfoE loc_859 ("err") <-{ IntOp i32 }
          LocInfoE loc_860 (Call (LocInfoE loc_862 (global_check_channels)) [@{expr} LocInfoE loc_863 (use{PtrOp} (LocInfoE loc_864 ("fds"))) ]) ;
        locinfo: loc_855 ;
        if{IntOp i32, None}: LocInfoE loc_855 ((LocInfoE loc_856 (use{IntOp i32} (LocInfoE loc_857 ("err")))) <{IntOp i32, IntOp i32, i32} (LocInfoE loc_858 (i2v 0 i32)))
        then
        locinfo: loc_851 ;
          Goto "#4"
        else
        Goto "#5"
      ]> $
      <[ "#3" :=
        locinfo: loc_844 ;
        Return (LocInfoE loc_845 (use{IntOp i32} (LocInfoE loc_846 ("err"))))
      ]> $
      <[ "#4" :=
        locinfo: loc_851 ;
        Return (LocInfoE loc_852 (use{IntOp i32} (LocInfoE loc_853 ("err"))))
      ]> $
      <[ "#5" :=
        Goto "#1"
      ]> $∅
    )%E
  |}.
End code.
