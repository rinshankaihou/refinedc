From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/mutable_map.c]. *)
Section code.
  Definition file_0 : string := "include/assume.h".
  Definition file_1 : string := "include/refinedc_malloc.h".
  Definition file_2 : string := "examples/mutable_map.c".
  Definition file_3 : string := "include/refinedc.h".
  Definition loc_2 : location_info := LocationInfo file_3 63 2 63 47.
  Definition loc_3 : location_info := LocationInfo file_3 63 9 63 46.
  Definition loc_4 : location_info := LocationInfo file_3 63 9 63 32.
  Definition loc_5 : location_info := LocationInfo file_3 63 33 63 37.
  Definition loc_6 : location_info := LocationInfo file_3 63 33 63 37.
  Definition loc_7 : location_info := LocationInfo file_3 63 39 63 45.
  Definition loc_8 : location_info := LocationInfo file_3 63 39 63 45.
  Definition loc_11 : location_info := LocationInfo file_0 10 2 10 12.
  Definition loc_12 : location_info := LocationInfo file_0 15 2 15 11.
  Definition loc_13 : location_info := LocationInfo file_0 15 9 15 10.
  Definition loc_14 : location_info := LocationInfo file_0 10 10 10 12.
  Definition loc_15 : location_info := LocationInfo file_0 10 8 10 9.
  Definition loc_18 : location_info := LocationInfo file_1 33 2 33 23.
  Definition loc_19 : location_info := LocationInfo file_1 34 2 34 42.
  Definition loc_20 : location_info := LocationInfo file_1 35 2 35 11.
  Definition loc_21 : location_info := LocationInfo file_1 35 9 35 10.
  Definition loc_22 : location_info := LocationInfo file_1 35 9 35 10.
  Definition loc_23 : location_info := LocationInfo file_1 34 26 34 42.
  Definition loc_24 : location_info := LocationInfo file_1 34 28 34 40.
  Definition loc_25 : location_info := LocationInfo file_1 34 28 34 37.
  Definition loc_26 : location_info := LocationInfo file_1 34 28 34 37.
  Definition loc_27 : location_info := LocationInfo file_1 34 2 34 42.
  Definition loc_28 : location_info := LocationInfo file_1 34 5 34 24.
  Definition loc_29 : location_info := LocationInfo file_1 34 5 34 6.
  Definition loc_30 : location_info := LocationInfo file_1 34 5 34 6.
  Definition loc_31 : location_info := LocationInfo file_1 34 10 34 24.
  Definition loc_32 : location_info := LocationInfo file_1 33 12 33 22.
  Definition loc_33 : location_info := LocationInfo file_1 33 12 33 18.
  Definition loc_34 : location_info := LocationInfo file_1 33 12 33 18.
  Definition loc_35 : location_info := LocationInfo file_1 33 19 33 21.
  Definition loc_36 : location_info := LocationInfo file_1 33 19 33 21.
  Definition loc_41 : location_info := LocationInfo file_2 217 2 219 3.
  Definition loc_42 : location_info := LocationInfo file_2 221 2 221 89.
  Definition loc_43 : location_info := LocationInfo file_2 223 2 223 27.
  Definition loc_44 : location_info := LocationInfo file_2 224 2 224 33.
  Definition loc_45 : location_info := LocationInfo file_2 226 2 226 25.
  Definition loc_46 : location_info := LocationInfo file_2 234 2 239 3.
  Definition loc_47 : location_info := LocationInfo file_2 234 2 239 3.
  Definition loc_48 : location_info := LocationInfo file_2 234 2 239 3.
  Definition loc_49 : location_info := LocationInfo file_2 240 2 240 17.
  Definition loc_50 : location_info := LocationInfo file_2 241 2 241 10.
  Definition loc_51 : location_info := LocationInfo file_2 241 2 241 4.
  Definition loc_52 : location_info := LocationInfo file_2 241 3 241 4.
  Definition loc_53 : location_info := LocationInfo file_2 241 3 241 4.
  Definition loc_54 : location_info := LocationInfo file_2 241 7 241 9.
  Definition loc_55 : location_info := LocationInfo file_2 241 7 241 9.
  Definition loc_56 : location_info := LocationInfo file_2 240 2 240 6.
  Definition loc_57 : location_info := LocationInfo file_2 240 2 240 6.
  Definition loc_58 : location_info := LocationInfo file_2 240 7 240 15.
  Definition loc_59 : location_info := LocationInfo file_2 240 7 240 15.
  Definition loc_60 : location_info := LocationInfo file_2 240 7 240 8.
  Definition loc_61 : location_info := LocationInfo file_2 240 7 240 8.
  Definition loc_62 : location_info := LocationInfo file_2 234 43 239 3.
  Definition loc_63 : location_info := LocationInfo file_2 235 4 237 5.
  Definition loc_64 : location_info := LocationInfo file_2 238 4 238 17.
  Definition loc_65 : location_info := LocationInfo file_2 238 17 238 5.
  Definition loc_66 : location_info := LocationInfo file_2 234 2 239 3.
  Definition loc_68 : location_info := LocationInfo file_2 234 35 234 36.
  Definition loc_69 : location_info := LocationInfo file_2 234 35 234 41.
  Definition loc_70 : location_info := LocationInfo file_2 234 35 234 36.
  Definition loc_71 : location_info := LocationInfo file_2 234 35 234 36.
  Definition loc_72 : location_info := LocationInfo file_2 234 40 234 41.
  Definition loc_73 : location_info := LocationInfo file_2 238 4 238 16.
  Definition loc_74 : location_info := LocationInfo file_2 238 5 238 16.
  Definition loc_75 : location_info := LocationInfo file_2 238 6 238 8.
  Definition loc_76 : location_info := LocationInfo file_2 235 42 237 5.
  Definition loc_77 : location_info := LocationInfo file_2 236 6 236 80.
  Definition loc_78 : location_info := LocationInfo file_2 236 6 236 16.
  Definition loc_79 : location_info := LocationInfo file_2 236 6 236 16.
  Definition loc_80 : location_info := LocationInfo file_2 236 17 236 20.
  Definition loc_81 : location_info := LocationInfo file_2 236 18 236 20.
  Definition loc_82 : location_info := LocationInfo file_2 236 22 236 48.
  Definition loc_83 : location_info := LocationInfo file_2 236 22 236 48.
  Definition loc_84 : location_info := LocationInfo file_2 236 22 236 44.
  Definition loc_85 : location_info := LocationInfo file_2 236 22 236 38.
  Definition loc_86 : location_info := LocationInfo file_2 236 22 236 36.
  Definition loc_87 : location_info := LocationInfo file_2 236 22 236 36.
  Definition loc_88 : location_info := LocationInfo file_2 236 22 236 33.
  Definition loc_89 : location_info := LocationInfo file_2 236 22 236 33.
  Definition loc_90 : location_info := LocationInfo file_2 236 24 236 32.
  Definition loc_91 : location_info := LocationInfo file_2 236 24 236 32.
  Definition loc_92 : location_info := LocationInfo file_2 236 24 236 25.
  Definition loc_93 : location_info := LocationInfo file_2 236 24 236 25.
  Definition loc_94 : location_info := LocationInfo file_2 236 34 236 35.
  Definition loc_95 : location_info := LocationInfo file_2 236 34 236 35.
  Definition loc_96 : location_info := LocationInfo file_2 236 50 236 78.
  Definition loc_97 : location_info := LocationInfo file_2 236 50 236 78.
  Definition loc_98 : location_info := LocationInfo file_2 236 50 236 72.
  Definition loc_99 : location_info := LocationInfo file_2 236 50 236 66.
  Definition loc_100 : location_info := LocationInfo file_2 236 50 236 64.
  Definition loc_101 : location_info := LocationInfo file_2 236 50 236 64.
  Definition loc_102 : location_info := LocationInfo file_2 236 50 236 61.
  Definition loc_103 : location_info := LocationInfo file_2 236 50 236 61.
  Definition loc_104 : location_info := LocationInfo file_2 236 52 236 60.
  Definition loc_105 : location_info := LocationInfo file_2 236 52 236 60.
  Definition loc_106 : location_info := LocationInfo file_2 236 52 236 53.
  Definition loc_107 : location_info := LocationInfo file_2 236 52 236 53.
  Definition loc_108 : location_info := LocationInfo file_2 236 62 236 63.
  Definition loc_109 : location_info := LocationInfo file_2 236 62 236 63.
  Definition loc_110 : location_info := LocationInfo file_2 235 4 237 5.
  Definition loc_111 : location_info := LocationInfo file_2 235 7 235 40.
  Definition loc_112 : location_info := LocationInfo file_2 235 7 235 25.
  Definition loc_113 : location_info := LocationInfo file_2 235 7 235 25.
  Definition loc_114 : location_info := LocationInfo file_2 235 7 235 21.
  Definition loc_115 : location_info := LocationInfo file_2 235 7 235 21.
  Definition loc_116 : location_info := LocationInfo file_2 235 7 235 18.
  Definition loc_117 : location_info := LocationInfo file_2 235 7 235 18.
  Definition loc_118 : location_info := LocationInfo file_2 235 9 235 17.
  Definition loc_119 : location_info := LocationInfo file_2 235 9 235 17.
  Definition loc_120 : location_info := LocationInfo file_2 235 9 235 10.
  Definition loc_121 : location_info := LocationInfo file_2 235 9 235 10.
  Definition loc_122 : location_info := LocationInfo file_2 235 19 235 20.
  Definition loc_123 : location_info := LocationInfo file_2 235 19 235 20.
  Definition loc_124 : location_info := LocationInfo file_2 235 29 235 40.
  Definition loc_125 : location_info := LocationInfo file_2 235 38 235 39.
  Definition loc_126 : location_info := LocationInfo file_2 234 20 234 33.
  Definition loc_127 : location_info := LocationInfo file_2 234 20 234 21.
  Definition loc_128 : location_info := LocationInfo file_2 234 20 234 21.
  Definition loc_129 : location_info := LocationInfo file_2 234 24 234 33.
  Definition loc_130 : location_info := LocationInfo file_2 234 24 234 33.
  Definition loc_131 : location_info := LocationInfo file_2 234 24 234 25.
  Definition loc_132 : location_info := LocationInfo file_2 234 24 234 25.
  Definition loc_133 : location_info := LocationInfo file_2 234 17 234 18.
  Definition loc_136 : location_info := LocationInfo file_2 226 2 226 10.
  Definition loc_137 : location_info := LocationInfo file_2 226 2 226 10.
  Definition loc_138 : location_info := LocationInfo file_2 226 11 226 14.
  Definition loc_139 : location_info := LocationInfo file_2 226 12 226 14.
  Definition loc_140 : location_info := LocationInfo file_2 226 16 226 23.
  Definition loc_141 : location_info := LocationInfo file_2 226 16 226 23.
  Definition loc_142 : location_info := LocationInfo file_2 224 19 224 32.
  Definition loc_143 : location_info := LocationInfo file_2 224 19 224 28.
  Definition loc_144 : location_info := LocationInfo file_2 224 19 224 28.
  Definition loc_145 : location_info := LocationInfo file_2 224 19 224 20.
  Definition loc_146 : location_info := LocationInfo file_2 224 19 224 20.
  Definition loc_147 : location_info := LocationInfo file_2 224 31 224 32.
  Definition loc_150 : location_info := LocationInfo file_2 221 68 221 70.
  Definition loc_151 : location_info := LocationInfo file_2 221 76 221 89.
  Definition loc_152 : location_info := LocationInfo file_2 221 78 221 87.
  Definition loc_153 : location_info := LocationInfo file_2 221 86 221 87.
  Definition loc_154 : location_info := LocationInfo file_2 221 84 221 85.
  Definition loc_155 : location_info := LocationInfo file_2 221 5 221 66.
  Definition loc_156 : location_info := LocationInfo file_2 221 5 221 14.
  Definition loc_157 : location_info := LocationInfo file_2 221 5 221 14.
  Definition loc_158 : location_info := LocationInfo file_2 221 5 221 6.
  Definition loc_159 : location_info := LocationInfo file_2 221 5 221 6.
  Definition loc_160 : location_info := LocationInfo file_2 221 17 221 66.
  Definition loc_161 : location_info := LocationInfo file_2 221 17 221 61.
  Definition loc_162 : location_info := LocationInfo file_2 221 17 221 39.
  Definition loc_163 : location_info := LocationInfo file_2 221 17 221 35.
  Definition loc_164 : location_info := LocationInfo file_2 221 38 221 39.
  Definition loc_165 : location_info := LocationInfo file_2 221 42 221 61.
  Definition loc_166 : location_info := LocationInfo file_2 221 64 221 66.
  Definition loc_167 : location_info := LocationInfo file_2 217 47 219 3.
  Definition loc_168 : location_info := LocationInfo file_2 218 4 218 11.
  Definition loc_170 : location_info := LocationInfo file_2 217 2 219 3.
  Definition loc_171 : location_info := LocationInfo file_2 217 5 217 45.
  Definition loc_172 : location_info := LocationInfo file_2 217 5 217 33.
  Definition loc_173 : location_info := LocationInfo file_2 217 5 217 22.
  Definition loc_174 : location_info := LocationInfo file_2 217 5 217 22.
  Definition loc_175 : location_info := LocationInfo file_2 217 23 217 32.
  Definition loc_176 : location_info := LocationInfo file_2 217 23 217 32.
  Definition loc_177 : location_info := LocationInfo file_2 217 23 217 24.
  Definition loc_178 : location_info := LocationInfo file_2 217 23 217 24.
  Definition loc_179 : location_info := LocationInfo file_2 217 37 217 45.
  Definition loc_180 : location_info := LocationInfo file_2 217 37 217 45.
  Definition loc_181 : location_info := LocationInfo file_2 217 37 217 38.
  Definition loc_182 : location_info := LocationInfo file_2 217 37 217 38.
  Definition loc_185 : location_info := LocationInfo file_2 75 2 75 11.
  Definition loc_186 : location_info := LocationInfo file_2 76 2 76 53.
  Definition loc_187 : location_info := LocationInfo file_2 77 2 77 18.
  Definition loc_188 : location_info := LocationInfo file_2 78 2 78 21.
  Definition loc_189 : location_info := LocationInfo file_2 79 2 79 17.
  Definition loc_190 : location_info := LocationInfo file_2 87 2 90 3.
  Definition loc_191 : location_info := LocationInfo file_2 87 6 87 11.
  Definition loc_192 : location_info := LocationInfo file_2 87 2 90 3.
  Definition loc_193 : location_info := LocationInfo file_2 87 30 90 3.
  Definition loc_194 : location_info := LocationInfo file_2 88 4 88 37.
  Definition loc_195 : location_info := LocationInfo file_2 89 4 89 37.
  Definition loc_196 : location_info := LocationInfo file_2 87 2 90 3.
  Definition loc_197 : location_info := LocationInfo file_2 87 22 87 28.
  Definition loc_198 : location_info := LocationInfo file_2 87 22 87 23.
  Definition loc_199 : location_info := LocationInfo file_2 87 22 87 28.
  Definition loc_200 : location_info := LocationInfo file_2 87 22 87 23.
  Definition loc_201 : location_info := LocationInfo file_2 87 22 87 23.
  Definition loc_202 : location_info := LocationInfo file_2 87 27 87 28.
  Definition loc_203 : location_info := LocationInfo file_2 89 4 89 32.
  Definition loc_204 : location_info := LocationInfo file_2 89 4 89 26.
  Definition loc_205 : location_info := LocationInfo file_2 89 4 89 20.
  Definition loc_206 : location_info := LocationInfo file_2 89 4 89 18.
  Definition loc_207 : location_info := LocationInfo file_2 89 4 89 18.
  Definition loc_208 : location_info := LocationInfo file_2 89 4 89 15.
  Definition loc_209 : location_info := LocationInfo file_2 89 4 89 15.
  Definition loc_210 : location_info := LocationInfo file_2 89 6 89 14.
  Definition loc_211 : location_info := LocationInfo file_2 89 6 89 14.
  Definition loc_212 : location_info := LocationInfo file_2 89 6 89 7.
  Definition loc_213 : location_info := LocationInfo file_2 89 6 89 7.
  Definition loc_214 : location_info := LocationInfo file_2 89 16 89 17.
  Definition loc_215 : location_info := LocationInfo file_2 89 16 89 17.
  Definition loc_216 : location_info := LocationInfo file_2 89 35 89 36.
  Definition loc_217 : location_info := LocationInfo file_2 88 4 88 22.
  Definition loc_218 : location_info := LocationInfo file_2 88 4 88 18.
  Definition loc_219 : location_info := LocationInfo file_2 88 4 88 18.
  Definition loc_220 : location_info := LocationInfo file_2 88 4 88 15.
  Definition loc_221 : location_info := LocationInfo file_2 88 4 88 15.
  Definition loc_222 : location_info := LocationInfo file_2 88 6 88 14.
  Definition loc_223 : location_info := LocationInfo file_2 88 6 88 14.
  Definition loc_224 : location_info := LocationInfo file_2 88 6 88 7.
  Definition loc_225 : location_info := LocationInfo file_2 88 6 88 7.
  Definition loc_226 : location_info := LocationInfo file_2 88 16 88 17.
  Definition loc_227 : location_info := LocationInfo file_2 88 16 88 17.
  Definition loc_228 : location_info := LocationInfo file_2 88 25 88 36.
  Definition loc_229 : location_info := LocationInfo file_2 88 34 88 35.
  Definition loc_230 : location_info := LocationInfo file_2 87 13 87 20.
  Definition loc_231 : location_info := LocationInfo file_2 87 13 87 14.
  Definition loc_232 : location_info := LocationInfo file_2 87 13 87 14.
  Definition loc_233 : location_info := LocationInfo file_2 87 17 87 20.
  Definition loc_234 : location_info := LocationInfo file_2 87 17 87 20.
  Definition loc_235 : location_info := LocationInfo file_2 87 6 87 7.
  Definition loc_236 : location_info := LocationInfo file_2 87 10 87 11.
  Definition loc_237 : location_info := LocationInfo file_2 79 2 79 10.
  Definition loc_238 : location_info := LocationInfo file_2 79 2 79 3.
  Definition loc_239 : location_info := LocationInfo file_2 79 2 79 3.
  Definition loc_240 : location_info := LocationInfo file_2 79 13 79 16.
  Definition loc_241 : location_info := LocationInfo file_2 79 13 79 16.
  Definition loc_242 : location_info := LocationInfo file_2 78 2 78 10.
  Definition loc_243 : location_info := LocationInfo file_2 78 2 78 3.
  Definition loc_244 : location_info := LocationInfo file_2 78 2 78 3.
  Definition loc_245 : location_info := LocationInfo file_2 78 13 78 20.
  Definition loc_246 : location_info := LocationInfo file_2 78 13 78 20.
  Definition loc_247 : location_info := LocationInfo file_2 77 2 77 11.
  Definition loc_248 : location_info := LocationInfo file_2 77 2 77 3.
  Definition loc_249 : location_info := LocationInfo file_2 77 2 77 3.
  Definition loc_250 : location_info := LocationInfo file_2 77 14 77 17.
  Definition loc_251 : location_info := LocationInfo file_2 77 14 77 17.
  Definition loc_252 : location_info := LocationInfo file_2 76 18 76 52.
  Definition loc_253 : location_info := LocationInfo file_2 76 18 76 25.
  Definition loc_254 : location_info := LocationInfo file_2 76 18 76 25.
  Definition loc_255 : location_info := LocationInfo file_2 76 26 76 51.
  Definition loc_256 : location_info := LocationInfo file_2 76 26 76 45.
  Definition loc_257 : location_info := LocationInfo file_2 76 48 76 51.
  Definition loc_258 : location_info := LocationInfo file_2 76 48 76 51.
  Definition loc_263 : location_info := LocationInfo file_2 101 4 101 21.
  Definition loc_264 : location_info := LocationInfo file_2 101 11 101 20.
  Definition loc_265 : location_info := LocationInfo file_2 101 11 101 14.
  Definition loc_266 : location_info := LocationInfo file_2 101 11 101 14.
  Definition loc_267 : location_info := LocationInfo file_2 101 17 101 20.
  Definition loc_268 : location_info := LocationInfo file_2 101 17 101 20.
  Definition loc_271 : location_info := LocationInfo file_2 114 4 114 55.
  Definition loc_272 : location_info := LocationInfo file_2 120 4 129 5.
  Definition loc_273 : location_info := LocationInfo file_2 120 13 129 5.
  Definition loc_274 : location_info := LocationInfo file_2 121 8 123 9.
  Definition loc_275 : location_info := LocationInfo file_2 124 8 126 9.
  Definition loc_276 : location_info := LocationInfo file_2 127 8 127 22.
  Definition loc_277 : location_info := LocationInfo file_2 127 22 127 9.
  Definition loc_278 : location_info := LocationInfo file_2 128 8 128 46.
  Definition loc_279 : location_info := LocationInfo file_2 128 8 128 16.
  Definition loc_280 : location_info := LocationInfo file_2 128 19 128 45.
  Definition loc_281 : location_info := LocationInfo file_2 128 19 128 33.
  Definition loc_282 : location_info := LocationInfo file_2 128 20 128 28.
  Definition loc_283 : location_info := LocationInfo file_2 128 20 128 28.
  Definition loc_284 : location_info := LocationInfo file_2 128 31 128 32.
  Definition loc_285 : location_info := LocationInfo file_2 128 36 128 45.
  Definition loc_286 : location_info := LocationInfo file_2 128 36 128 45.
  Definition loc_287 : location_info := LocationInfo file_2 128 36 128 37.
  Definition loc_288 : location_info := LocationInfo file_2 128 36 128 37.
  Definition loc_289 : location_info := LocationInfo file_2 127 8 127 21.
  Definition loc_290 : location_info := LocationInfo file_2 127 8 127 17.
  Definition loc_291 : location_info := LocationInfo file_2 127 8 127 17.
  Definition loc_292 : location_info := LocationInfo file_2 127 8 127 9.
  Definition loc_293 : location_info := LocationInfo file_2 127 8 127 9.
  Definition loc_294 : location_info := LocationInfo file_2 127 20 127 21.
  Definition loc_295 : location_info := LocationInfo file_2 124 97 126 9.
  Definition loc_296 : location_info := LocationInfo file_2 125 12 125 28.
  Definition loc_297 : location_info := LocationInfo file_2 125 19 125 27.
  Definition loc_298 : location_info := LocationInfo file_2 125 19 125 27.
  Definition loc_299 : location_info := LocationInfo file_2 124 8 126 9.
  Definition loc_300 : location_info := LocationInfo file_2 124 11 124 95.
  Definition loc_301 : location_info := LocationInfo file_2 124 11 124 51.
  Definition loc_302 : location_info := LocationInfo file_2 124 11 124 36.
  Definition loc_303 : location_info := LocationInfo file_2 124 11 124 36.
  Definition loc_304 : location_info := LocationInfo file_2 124 11 124 32.
  Definition loc_305 : location_info := LocationInfo file_2 124 11 124 32.
  Definition loc_306 : location_info := LocationInfo file_2 124 11 124 22.
  Definition loc_307 : location_info := LocationInfo file_2 124 11 124 22.
  Definition loc_308 : location_info := LocationInfo file_2 124 13 124 21.
  Definition loc_309 : location_info := LocationInfo file_2 124 13 124 21.
  Definition loc_310 : location_info := LocationInfo file_2 124 13 124 14.
  Definition loc_311 : location_info := LocationInfo file_2 124 13 124 14.
  Definition loc_312 : location_info := LocationInfo file_2 124 23 124 31.
  Definition loc_313 : location_info := LocationInfo file_2 124 23 124 31.
  Definition loc_314 : location_info := LocationInfo file_2 124 40 124 51.
  Definition loc_315 : location_info := LocationInfo file_2 124 49 124 50.
  Definition loc_316 : location_info := LocationInfo file_2 124 55 124 95.
  Definition loc_317 : location_info := LocationInfo file_2 124 55 124 88.
  Definition loc_318 : location_info := LocationInfo file_2 124 55 124 88.
  Definition loc_319 : location_info := LocationInfo file_2 124 55 124 84.
  Definition loc_320 : location_info := LocationInfo file_2 124 55 124 78.
  Definition loc_321 : location_info := LocationInfo file_2 124 55 124 76.
  Definition loc_322 : location_info := LocationInfo file_2 124 55 124 76.
  Definition loc_323 : location_info := LocationInfo file_2 124 55 124 66.
  Definition loc_324 : location_info := LocationInfo file_2 124 55 124 66.
  Definition loc_325 : location_info := LocationInfo file_2 124 57 124 65.
  Definition loc_326 : location_info := LocationInfo file_2 124 57 124 65.
  Definition loc_327 : location_info := LocationInfo file_2 124 57 124 58.
  Definition loc_328 : location_info := LocationInfo file_2 124 57 124 58.
  Definition loc_329 : location_info := LocationInfo file_2 124 67 124 75.
  Definition loc_330 : location_info := LocationInfo file_2 124 67 124 75.
  Definition loc_331 : location_info := LocationInfo file_2 124 92 124 95.
  Definition loc_332 : location_info := LocationInfo file_2 124 92 124 95.
  Definition loc_333 : location_info := LocationInfo file_2 121 147 123 9.
  Definition loc_334 : location_info := LocationInfo file_2 122 12 122 28.
  Definition loc_335 : location_info := LocationInfo file_2 122 19 122 27.
  Definition loc_336 : location_info := LocationInfo file_2 122 19 122 27.
  Definition loc_337 : location_info := LocationInfo file_2 121 8 123 9.
  Definition loc_338 : location_info := LocationInfo file_2 121 11 121 145.
  Definition loc_339 : location_info := LocationInfo file_2 121 11 121 51.
  Definition loc_340 : location_info := LocationInfo file_2 121 11 121 36.
  Definition loc_341 : location_info := LocationInfo file_2 121 11 121 36.
  Definition loc_342 : location_info := LocationInfo file_2 121 11 121 32.
  Definition loc_343 : location_info := LocationInfo file_2 121 11 121 32.
  Definition loc_344 : location_info := LocationInfo file_2 121 11 121 22.
  Definition loc_345 : location_info := LocationInfo file_2 121 11 121 22.
  Definition loc_346 : location_info := LocationInfo file_2 121 13 121 21.
  Definition loc_347 : location_info := LocationInfo file_2 121 13 121 21.
  Definition loc_348 : location_info := LocationInfo file_2 121 13 121 14.
  Definition loc_349 : location_info := LocationInfo file_2 121 13 121 14.
  Definition loc_350 : location_info := LocationInfo file_2 121 23 121 31.
  Definition loc_351 : location_info := LocationInfo file_2 121 23 121 31.
  Definition loc_352 : location_info := LocationInfo file_2 121 40 121 51.
  Definition loc_353 : location_info := LocationInfo file_2 121 49 121 50.
  Definition loc_354 : location_info := LocationInfo file_2 121 55 121 145.
  Definition loc_355 : location_info := LocationInfo file_2 121 56 121 96.
  Definition loc_356 : location_info := LocationInfo file_2 121 56 121 81.
  Definition loc_357 : location_info := LocationInfo file_2 121 56 121 81.
  Definition loc_358 : location_info := LocationInfo file_2 121 56 121 77.
  Definition loc_359 : location_info := LocationInfo file_2 121 56 121 77.
  Definition loc_360 : location_info := LocationInfo file_2 121 56 121 67.
  Definition loc_361 : location_info := LocationInfo file_2 121 56 121 67.
  Definition loc_362 : location_info := LocationInfo file_2 121 58 121 66.
  Definition loc_363 : location_info := LocationInfo file_2 121 58 121 66.
  Definition loc_364 : location_info := LocationInfo file_2 121 58 121 59.
  Definition loc_365 : location_info := LocationInfo file_2 121 58 121 59.
  Definition loc_366 : location_info := LocationInfo file_2 121 68 121 76.
  Definition loc_367 : location_info := LocationInfo file_2 121 68 121 76.
  Definition loc_368 : location_info := LocationInfo file_2 121 85 121 96.
  Definition loc_369 : location_info := LocationInfo file_2 121 94 121 95.
  Definition loc_370 : location_info := LocationInfo file_2 121 100 121 144.
  Definition loc_371 : location_info := LocationInfo file_2 121 100 121 137.
  Definition loc_372 : location_info := LocationInfo file_2 121 100 121 137.
  Definition loc_373 : location_info := LocationInfo file_2 121 100 121 133.
  Definition loc_374 : location_info := LocationInfo file_2 121 100 121 123.
  Definition loc_375 : location_info := LocationInfo file_2 121 100 121 121.
  Definition loc_376 : location_info := LocationInfo file_2 121 100 121 121.
  Definition loc_377 : location_info := LocationInfo file_2 121 100 121 111.
  Definition loc_378 : location_info := LocationInfo file_2 121 100 121 111.
  Definition loc_379 : location_info := LocationInfo file_2 121 102 121 110.
  Definition loc_380 : location_info := LocationInfo file_2 121 102 121 110.
  Definition loc_381 : location_info := LocationInfo file_2 121 102 121 103.
  Definition loc_382 : location_info := LocationInfo file_2 121 102 121 103.
  Definition loc_383 : location_info := LocationInfo file_2 121 112 121 120.
  Definition loc_384 : location_info := LocationInfo file_2 121 112 121 120.
  Definition loc_385 : location_info := LocationInfo file_2 121 141 121 144.
  Definition loc_386 : location_info := LocationInfo file_2 121 141 121 144.
  Definition loc_387 : location_info := LocationInfo file_2 120 10 120 11.
  Definition loc_388 : location_info := LocationInfo file_2 114 22 114 54.
  Definition loc_389 : location_info := LocationInfo file_2 114 22 114 38.
  Definition loc_390 : location_info := LocationInfo file_2 114 22 114 38.
  Definition loc_391 : location_info := LocationInfo file_2 114 39 114 48.
  Definition loc_392 : location_info := LocationInfo file_2 114 39 114 48.
  Definition loc_393 : location_info := LocationInfo file_2 114 39 114 40.
  Definition loc_394 : location_info := LocationInfo file_2 114 39 114 40.
  Definition loc_395 : location_info := LocationInfo file_2 114 50 114 53.
  Definition loc_396 : location_info := LocationInfo file_2 114 50 114 53.
  Definition loc_401 : location_info := LocationInfo file_2 142 4 142 32.
  Definition loc_402 : location_info := LocationInfo file_2 143 4 143 40.
  Definition loc_403 : location_info := LocationInfo file_2 144 4 144 36.
  Definition loc_404 : location_info := LocationInfo file_2 145 4 145 47.
  Definition loc_405 : location_info := LocationInfo file_2 146 4 150 5.
  Definition loc_406 : location_info := LocationInfo file_2 152 4 152 28.
  Definition loc_407 : location_info := LocationInfo file_2 153 4 153 28.
  Definition loc_408 : location_info := LocationInfo file_2 154 4 154 32.
  Definition loc_409 : location_info := LocationInfo file_2 156 4 156 20.
  Definition loc_410 : location_info := LocationInfo file_2 156 11 156 19.
  Definition loc_411 : location_info := LocationInfo file_2 156 11 156 19.
  Definition loc_412 : location_info := LocationInfo file_2 154 4 154 23.
  Definition loc_413 : location_info := LocationInfo file_2 154 4 154 17.
  Definition loc_414 : location_info := LocationInfo file_2 154 4 154 11.
  Definition loc_415 : location_info := LocationInfo file_2 154 4 154 8.
  Definition loc_416 : location_info := LocationInfo file_2 154 4 154 8.
  Definition loc_417 : location_info := LocationInfo file_2 154 26 154 31.
  Definition loc_418 : location_info := LocationInfo file_2 154 26 154 31.
  Definition loc_419 : location_info := LocationInfo file_2 153 4 153 21.
  Definition loc_420 : location_info := LocationInfo file_2 153 4 153 17.
  Definition loc_421 : location_info := LocationInfo file_2 153 4 153 11.
  Definition loc_422 : location_info := LocationInfo file_2 153 4 153 8.
  Definition loc_423 : location_info := LocationInfo file_2 153 4 153 8.
  Definition loc_424 : location_info := LocationInfo file_2 153 24 153 27.
  Definition loc_425 : location_info := LocationInfo file_2 153 24 153 27.
  Definition loc_426 : location_info := LocationInfo file_2 152 4 152 13.
  Definition loc_427 : location_info := LocationInfo file_2 152 4 152 8.
  Definition loc_428 : location_info := LocationInfo file_2 152 4 152 8.
  Definition loc_429 : location_info := LocationInfo file_2 152 16 152 27.
  Definition loc_430 : location_info := LocationInfo file_2 152 25 152 26.
  Definition loc_431 : location_info := LocationInfo file_2 146 34 148 5.
  Definition loc_432 : location_info := LocationInfo file_2 147 8 147 39.
  Definition loc_433 : location_info := LocationInfo file_2 147 8 147 16.
  Definition loc_434 : location_info := LocationInfo file_2 147 19 147 38.
  Definition loc_435 : location_info := LocationInfo file_2 147 19 147 38.
  Definition loc_436 : location_info := LocationInfo file_2 147 19 147 32.
  Definition loc_437 : location_info := LocationInfo file_2 147 19 147 26.
  Definition loc_438 : location_info := LocationInfo file_2 147 19 147 23.
  Definition loc_439 : location_info := LocationInfo file_2 147 19 147 23.
  Definition loc_440 : location_info := LocationInfo file_2 148 11 150 5.
  Definition loc_441 : location_info := LocationInfo file_2 148 40 150 5.
  Definition loc_442 : location_info := LocationInfo file_2 149 6 149 20.
  Definition loc_443 : location_info := LocationInfo file_2 149 6 149 14.
  Definition loc_444 : location_info := LocationInfo file_2 149 6 149 7.
  Definition loc_445 : location_info := LocationInfo file_2 149 6 149 7.
  Definition loc_446 : location_info := LocationInfo file_2 149 6 149 19.
  Definition loc_447 : location_info := LocationInfo file_2 149 6 149 14.
  Definition loc_448 : location_info := LocationInfo file_2 149 6 149 14.
  Definition loc_449 : location_info := LocationInfo file_2 149 6 149 7.
  Definition loc_450 : location_info := LocationInfo file_2 149 6 149 7.
  Definition loc_451 : location_info := LocationInfo file_2 149 18 149 19.
  Definition loc_452 : location_info := LocationInfo file_2 148 11 150 5.
  Definition loc_453 : location_info := LocationInfo file_2 148 14 148 38.
  Definition loc_454 : location_info := LocationInfo file_2 148 14 148 23.
  Definition loc_455 : location_info := LocationInfo file_2 148 14 148 23.
  Definition loc_456 : location_info := LocationInfo file_2 148 14 148 18.
  Definition loc_457 : location_info := LocationInfo file_2 148 14 148 18.
  Definition loc_458 : location_info := LocationInfo file_2 148 27 148 38.
  Definition loc_459 : location_info := LocationInfo file_2 148 36 148 37.
  Definition loc_460 : location_info := LocationInfo file_2 146 8 146 32.
  Definition loc_461 : location_info := LocationInfo file_2 146 8 146 17.
  Definition loc_462 : location_info := LocationInfo file_2 146 8 146 17.
  Definition loc_463 : location_info := LocationInfo file_2 146 8 146 12.
  Definition loc_464 : location_info := LocationInfo file_2 146 8 146 12.
  Definition loc_465 : location_info := LocationInfo file_2 146 21 146 32.
  Definition loc_466 : location_info := LocationInfo file_2 146 30 146 31.
  Definition loc_467 : location_info := LocationInfo file_2 145 24 145 46.
  Definition loc_468 : location_info := LocationInfo file_2 145 25 145 46.
  Definition loc_469 : location_info := LocationInfo file_2 145 25 145 46.
  Definition loc_470 : location_info := LocationInfo file_2 145 25 145 36.
  Definition loc_471 : location_info := LocationInfo file_2 145 25 145 36.
  Definition loc_472 : location_info := LocationInfo file_2 145 27 145 35.
  Definition loc_473 : location_info := LocationInfo file_2 145 27 145 35.
  Definition loc_474 : location_info := LocationInfo file_2 145 27 145 28.
  Definition loc_475 : location_info := LocationInfo file_2 145 27 145 28.
  Definition loc_476 : location_info := LocationInfo file_2 145 37 145 45.
  Definition loc_477 : location_info := LocationInfo file_2 145 37 145 45.
  Definition loc_480 : location_info := LocationInfo file_2 144 21 144 35.
  Definition loc_483 : location_info := LocationInfo file_2 143 22 143 39.
  Definition loc_484 : location_info := LocationInfo file_2 143 22 143 31.
  Definition loc_485 : location_info := LocationInfo file_2 143 22 143 31.
  Definition loc_486 : location_info := LocationInfo file_2 143 32 143 33.
  Definition loc_487 : location_info := LocationInfo file_2 143 32 143 33.
  Definition loc_488 : location_info := LocationInfo file_2 143 35 143 38.
  Definition loc_489 : location_info := LocationInfo file_2 143 35 143 38.
  Definition loc_492 : location_info := LocationInfo file_2 142 4 142 28.
  Definition loc_493 : location_info := LocationInfo file_2 142 4 142 28.
  Definition loc_494 : location_info := LocationInfo file_2 142 29 142 30.
  Definition loc_495 : location_info := LocationInfo file_2 142 29 142 30.
  Definition loc_498 : location_info := LocationInfo file_2 166 4 166 40.
  Definition loc_499 : location_info := LocationInfo file_2 167 4 167 47.
  Definition loc_500 : location_info := LocationInfo file_2 169 4 173 5.
  Definition loc_501 : location_info := LocationInfo file_2 169 34 171 5.
  Definition loc_502 : location_info := LocationInfo file_2 170 8 170 37.
  Definition loc_503 : location_info := LocationInfo file_2 170 15 170 36.
  Definition loc_504 : location_info := LocationInfo file_2 170 16 170 36.
  Definition loc_505 : location_info := LocationInfo file_2 170 17 170 36.
  Definition loc_506 : location_info := LocationInfo file_2 170 17 170 36.
  Definition loc_507 : location_info := LocationInfo file_2 170 17 170 30.
  Definition loc_508 : location_info := LocationInfo file_2 170 17 170 24.
  Definition loc_509 : location_info := LocationInfo file_2 170 17 170 21.
  Definition loc_510 : location_info := LocationInfo file_2 170 17 170 21.
  Definition loc_511 : location_info := LocationInfo file_2 171 11 173 5.
  Definition loc_512 : location_info := LocationInfo file_2 172 8 172 30.
  Definition loc_513 : location_info := LocationInfo file_2 172 15 172 29.
  Definition loc_514 : location_info := LocationInfo file_2 169 8 169 32.
  Definition loc_515 : location_info := LocationInfo file_2 169 8 169 17.
  Definition loc_516 : location_info := LocationInfo file_2 169 8 169 17.
  Definition loc_517 : location_info := LocationInfo file_2 169 8 169 12.
  Definition loc_518 : location_info := LocationInfo file_2 169 8 169 12.
  Definition loc_519 : location_info := LocationInfo file_2 169 21 169 32.
  Definition loc_520 : location_info := LocationInfo file_2 169 30 169 31.
  Definition loc_521 : location_info := LocationInfo file_2 167 24 167 46.
  Definition loc_522 : location_info := LocationInfo file_2 167 25 167 46.
  Definition loc_523 : location_info := LocationInfo file_2 167 25 167 46.
  Definition loc_524 : location_info := LocationInfo file_2 167 25 167 36.
  Definition loc_525 : location_info := LocationInfo file_2 167 25 167 36.
  Definition loc_526 : location_info := LocationInfo file_2 167 27 167 35.
  Definition loc_527 : location_info := LocationInfo file_2 167 27 167 35.
  Definition loc_528 : location_info := LocationInfo file_2 167 27 167 28.
  Definition loc_529 : location_info := LocationInfo file_2 167 27 167 28.
  Definition loc_530 : location_info := LocationInfo file_2 167 37 167 45.
  Definition loc_531 : location_info := LocationInfo file_2 167 37 167 45.
  Definition loc_534 : location_info := LocationInfo file_2 166 22 166 39.
  Definition loc_535 : location_info := LocationInfo file_2 166 22 166 31.
  Definition loc_536 : location_info := LocationInfo file_2 166 22 166 31.
  Definition loc_537 : location_info := LocationInfo file_2 166 32 166 33.
  Definition loc_538 : location_info := LocationInfo file_2 166 32 166 33.
  Definition loc_539 : location_info := LocationInfo file_2 166 35 166 38.
  Definition loc_540 : location_info := LocationInfo file_2 166 35 166 38.
  Definition loc_545 : location_info := LocationInfo file_2 185 4 185 18.
  Definition loc_546 : location_info := LocationInfo file_2 186 4 186 40.
  Definition loc_547 : location_info := LocationInfo file_2 187 4 187 47.
  Definition loc_548 : location_info := LocationInfo file_2 189 4 196 5.
  Definition loc_549 : location_info := LocationInfo file_2 189 34 194 5.
  Definition loc_550 : location_info := LocationInfo file_2 190 8 190 38.
  Definition loc_551 : location_info := LocationInfo file_2 191 8 191 32.
  Definition loc_552 : location_info := LocationInfo file_2 192 8 192 36.
  Definition loc_553 : location_info := LocationInfo file_2 193 8 193 23.
  Definition loc_554 : location_info := LocationInfo file_2 193 15 193 22.
  Definition loc_555 : location_info := LocationInfo file_2 193 15 193 22.
  Definition loc_556 : location_info := LocationInfo file_2 192 8 192 29.
  Definition loc_557 : location_info := LocationInfo file_2 192 8 192 25.
  Definition loc_558 : location_info := LocationInfo file_2 192 8 192 15.
  Definition loc_559 : location_info := LocationInfo file_2 192 8 192 12.
  Definition loc_560 : location_info := LocationInfo file_2 192 8 192 12.
  Definition loc_561 : location_info := LocationInfo file_2 192 32 192 35.
  Definition loc_562 : location_info := LocationInfo file_2 192 32 192 35.
  Definition loc_563 : location_info := LocationInfo file_2 191 8 191 17.
  Definition loc_564 : location_info := LocationInfo file_2 191 8 191 12.
  Definition loc_565 : location_info := LocationInfo file_2 191 8 191 12.
  Definition loc_566 : location_info := LocationInfo file_2 191 20 191 31.
  Definition loc_567 : location_info := LocationInfo file_2 191 29 191 30.
  Definition loc_568 : location_info := LocationInfo file_2 190 8 190 15.
  Definition loc_569 : location_info := LocationInfo file_2 190 18 190 37.
  Definition loc_570 : location_info := LocationInfo file_2 190 18 190 37.
  Definition loc_571 : location_info := LocationInfo file_2 190 18 190 31.
  Definition loc_572 : location_info := LocationInfo file_2 190 18 190 25.
  Definition loc_573 : location_info := LocationInfo file_2 190 18 190 22.
  Definition loc_574 : location_info := LocationInfo file_2 190 18 190 22.
  Definition loc_575 : location_info := LocationInfo file_2 194 11 196 5.
  Definition loc_576 : location_info := LocationInfo file_2 195 8 195 30.
  Definition loc_577 : location_info := LocationInfo file_2 195 15 195 29.
  Definition loc_578 : location_info := LocationInfo file_2 189 8 189 32.
  Definition loc_579 : location_info := LocationInfo file_2 189 8 189 17.
  Definition loc_580 : location_info := LocationInfo file_2 189 8 189 17.
  Definition loc_581 : location_info := LocationInfo file_2 189 8 189 12.
  Definition loc_582 : location_info := LocationInfo file_2 189 8 189 12.
  Definition loc_583 : location_info := LocationInfo file_2 189 21 189 32.
  Definition loc_584 : location_info := LocationInfo file_2 189 30 189 31.
  Definition loc_585 : location_info := LocationInfo file_2 187 24 187 46.
  Definition loc_586 : location_info := LocationInfo file_2 187 25 187 46.
  Definition loc_587 : location_info := LocationInfo file_2 187 25 187 46.
  Definition loc_588 : location_info := LocationInfo file_2 187 25 187 36.
  Definition loc_589 : location_info := LocationInfo file_2 187 25 187 36.
  Definition loc_590 : location_info := LocationInfo file_2 187 27 187 35.
  Definition loc_591 : location_info := LocationInfo file_2 187 27 187 35.
  Definition loc_592 : location_info := LocationInfo file_2 187 27 187 28.
  Definition loc_593 : location_info := LocationInfo file_2 187 27 187 28.
  Definition loc_594 : location_info := LocationInfo file_2 187 37 187 45.
  Definition loc_595 : location_info := LocationInfo file_2 187 37 187 45.
  Definition loc_598 : location_info := LocationInfo file_2 186 22 186 39.
  Definition loc_599 : location_info := LocationInfo file_2 186 22 186 31.
  Definition loc_600 : location_info := LocationInfo file_2 186 22 186 31.
  Definition loc_601 : location_info := LocationInfo file_2 186 32 186 33.
  Definition loc_602 : location_info := LocationInfo file_2 186 32 186 33.
  Definition loc_603 : location_info := LocationInfo file_2 186 35 186 38.
  Definition loc_604 : location_info := LocationInfo file_2 186 35 186 38.
  Definition loc_609 : location_info := LocationInfo file_2 206 2 206 11.
  Definition loc_610 : location_info := LocationInfo file_2 206 9 206 10.

  (* Definition of struct [__cerbty_unnamed_tag_486]. *)
  Program Definition struct___cerbty_unnamed_tag_486 := {|
    sl_members := [
      (Some "__dummy_max_align_t", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [empty]. *)
  Program Definition struct_empty := {|
    sl_members := [
      (Some "dummy", it_layout size_t)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [entry]. *)
  Program Definition struct_entry := {|
    sl_members := [
      (Some "key", it_layout size_t);
      (Some "value", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [tombstone]. *)
  Program Definition struct_tombstone := {|
    sl_members := [
      (Some "key", it_layout size_t)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [fixed_size_map]. *)
  Program Definition struct_fixed_size_map := {|
    sl_members := [
      (Some "items", void*);
      (Some "count", it_layout size_t);
      (Some "length", it_layout size_t)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of union [item_union]. *)
  Program Definition union_item_union := {|
    ul_members := [
      ("empty", layout_of struct_empty);
      ("entry", layout_of struct_entry);
      ("tombstone", layout_of struct_tombstone)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [item]. *)
  Program Definition struct_item := {|
    sl_members := [
      (Some "tag", it_layout size_t);
      (Some "u", ul_layout union_item_union)
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
          LocInfoE loc_32 (Call (LocInfoE loc_34 (global_malloc)) [@{expr} LocInfoE loc_35 (use{IntOp size_t} (LocInfoE loc_36 ("sz"))) ]) ;
        locinfo: loc_28 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_28 ((LocInfoE loc_29 (use{PtrOp} (LocInfoE loc_30 ("p")))) ={PtrOp, PtrOp, i32} (LocInfoE loc_31 (NULL)))
        then
        locinfo: loc_24 ;
          Goto "#2"
        else
        locinfo: loc_20 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_20 ;
        Return (LocInfoE loc_21 (use{PtrOp} (LocInfoE loc_22 ("p"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_24 ;
        expr: (LocInfoE loc_24 (Call (LocInfoE loc_26 (global_safe_exit)) [@{expr}  ])) ;
        locinfo: loc_20 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_20 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [fsm_realloc_if_necessary]. *)
  Definition impl_fsm_realloc_if_necessary (global_compute_min_count global_free global_fsm_init global_fsm_insert : loc): function := {|
    f_args := [
      ("m", void*)
    ];
    f_local_vars := [
      ("i", it_layout size_t);
      ("m2", layout_of struct_fixed_size_map);
      ("new_len", it_layout size_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_171 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_171 ((LocInfoE loc_172 (Call (LocInfoE loc_174 (global_compute_min_count)) [@{expr} LocInfoE loc_175 (use{IntOp size_t} (LocInfoE loc_176 ((LocInfoE loc_177 (!{PtrOp} (LocInfoE loc_178 ("m")))) at{struct_fixed_size_map} "length"))) ])) ≤{IntOp size_t, IntOp size_t, i32} (LocInfoE loc_179 (use{IntOp size_t} (LocInfoE loc_180 ((LocInfoE loc_181 (!{PtrOp} (LocInfoE loc_182 ("m")))) at{struct_fixed_size_map} "count")))))
        then
        locinfo: loc_168 ;
          Goto "#14"
        else
        locinfo: loc_155 ;
          Goto "#15"
      ]> $
      <[ "#1" :=
        locinfo: loc_155 ;
        if{IntOp i32, Some "#2"}: LocInfoE loc_155 ((LocInfoE loc_156 (use{IntOp size_t} (LocInfoE loc_157 ((LocInfoE loc_158 (!{PtrOp} (LocInfoE loc_159 ("m")))) at{struct_fixed_size_map} "length")))) <{IntOp size_t, IntOp size_t, i32} (LocInfoE loc_160 ((LocInfoE loc_161 ((LocInfoE loc_162 ((LocInfoE loc_163 (i2v (max_int size_t) size_t)) /{IntOp size_t, IntOp size_t} (LocInfoE loc_164 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_164 (i2v 2 i32)))))) /{IntOp size_t, IntOp size_t} (LocInfoE loc_165 (i2v (layout_of struct_item).(ly_size) size_t)))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_166 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_166 (i2v 16 i32)))))))
        then
        Goto "#9"
        else
        locinfo: loc_152 ;
          Goto "#10"
      ]> $
      <[ "#10" :=
        locinfo: loc_152 ;
        Goto "#11"
      ]> $
      <[ "#11" :=
        locinfo: loc_154 ;
        if{IntOp i32, None}: LocInfoE loc_154 (i2v 1 i32)
        then
        locinfo: loc_152 ;
          Goto "#12"
        else
        Goto "#13"
      ]> $
      <[ "#12" :=
        locinfo: loc_152 ;
        Goto "#11"
      ]> $
      <[ "#13" :=
        Goto "#2"
      ]> $
      <[ "#14" :=
        locinfo: loc_168 ;
        Return (VOID)
      ]> $
      <[ "#15" :=
        locinfo: loc_155 ;
        Goto "#1"
      ]> $
      <[ "#2" :=
        "new_len" <-{ IntOp size_t }
          LocInfoE loc_142 ((LocInfoE loc_143 (use{IntOp size_t} (LocInfoE loc_144 ((LocInfoE loc_145 (!{PtrOp} (LocInfoE loc_146 ("m")))) at{struct_fixed_size_map} "length")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_147 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_147 (i2v 2 i32))))) ;
        locinfo: loc_45 ;
        expr: (LocInfoE loc_45 (Call (LocInfoE loc_137 (global_fsm_init)) [@{expr} LocInfoE loc_138 (&(LocInfoE loc_139 ("m2"))) ;
        LocInfoE loc_140 (use{IntOp size_t} (LocInfoE loc_141 ("new_len"))) ])) ;
        "i" <-{ IntOp size_t }
          LocInfoE loc_133 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_133 (i2v 0 i32))) ;
        locinfo: loc_48 ;
        Goto "#3"
      ]> $
      <[ "#3" :=
        locinfo: loc_126 ;
        if{IntOp i32, None}: LocInfoE loc_126 ((LocInfoE loc_127 (use{IntOp size_t} (LocInfoE loc_128 ("i")))) <{IntOp size_t, IntOp size_t, i32} (LocInfoE loc_129 (use{IntOp size_t} (LocInfoE loc_130 ((LocInfoE loc_131 (!{PtrOp} (LocInfoE loc_132 ("m")))) at{struct_fixed_size_map} "length")))))
        then
        locinfo: loc_111 ;
          Goto "#4"
        else
        locinfo: loc_49 ;
          Goto "#5"
      ]> $
      <[ "#4" :=
        locinfo: loc_111 ;
        if{IntOp i32, Some "#6"}: LocInfoE loc_111 ((LocInfoE loc_112 (use{IntOp size_t} (LocInfoE loc_113 ((LocInfoE loc_115 ((LocInfoE loc_118 (!{PtrOp} (LocInfoE loc_119 ((LocInfoE loc_120 (!{PtrOp} (LocInfoE loc_121 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_122 (use{IntOp size_t} (LocInfoE loc_123 ("i")))))) at{struct_item} "tag")))) ={IntOp size_t, IntOp size_t, i32} (LocInfoE loc_124 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_125 (i2v 1 i32)))))
        then
        locinfo: loc_77 ;
          Goto "#7"
        else
        locinfo: loc_64 ;
          Goto "#8"
      ]> $
      <[ "#5" :=
        locinfo: loc_49 ;
        expr: (LocInfoE loc_49 (Call (LocInfoE loc_57 (global_free)) [@{expr} LocInfoE loc_58 (use{PtrOp} (LocInfoE loc_59 ((LocInfoE loc_60 (!{PtrOp} (LocInfoE loc_61 ("m")))) at{struct_fixed_size_map} "items"))) ])) ;
        locinfo: loc_50 ;
        LocInfoE loc_52 (!{PtrOp} (LocInfoE loc_53 ("m"))) <-{ StructOp struct_fixed_size_map ([ PtrOp ; IntOp size_t ; IntOp size_t ]) }
          LocInfoE loc_54 (use{StructOp struct_fixed_size_map ([ PtrOp ; IntOp size_t ; IntOp size_t ])} (LocInfoE loc_55 ("m2"))) ;
        Return (VOID)
      ]> $
      <[ "#6" :=
        locinfo: loc_64 ;
        expr: (LocInfoE loc_73 (&(LocInfoE loc_74 ((LocInfoE loc_75 ("m2")) at{struct_fixed_size_map} "length")))) ;
        locinfo: loc_66 ;
        Goto "__cerb_continue4"
      ]> $
      <[ "#7" :=
        locinfo: loc_77 ;
        expr: (LocInfoE loc_77 (Call (LocInfoE loc_79 (global_fsm_insert)) [@{expr} LocInfoE loc_80 (&(LocInfoE loc_81 ("m2"))) ;
        LocInfoE loc_82 (use{IntOp size_t} (LocInfoE loc_83 ((LocInfoE loc_84 ((LocInfoE loc_85 ((LocInfoE loc_87 ((LocInfoE loc_90 (!{PtrOp} (LocInfoE loc_91 ((LocInfoE loc_92 (!{PtrOp} (LocInfoE loc_93 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_94 (use{IntOp size_t} (LocInfoE loc_95 ("i")))))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "key"))) ;
        LocInfoE loc_96 (use{PtrOp} (LocInfoE loc_97 ((LocInfoE loc_98 ((LocInfoE loc_99 ((LocInfoE loc_101 ((LocInfoE loc_104 (!{PtrOp} (LocInfoE loc_105 ((LocInfoE loc_106 (!{PtrOp} (LocInfoE loc_107 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_108 (use{IntOp size_t} (LocInfoE loc_109 ("i")))))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "value"))) ])) ;
        locinfo: loc_64 ;
        Goto "#6"
      ]> $
      <[ "#8" :=
        locinfo: loc_64 ;
        Goto "#6"
      ]> $
      <[ "#9" :=
        Goto "#2"
      ]> $
      <[ "__cerb_continue4" :=
        LocInfoE loc_68 ("i") <-{ IntOp size_t }
          LocInfoE loc_69 ((LocInfoE loc_70 (use{IntOp size_t} (LocInfoE loc_71 ("i")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_72 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_72 (i2v 1 i32))))) ;
        locinfo: loc_48 ;
        Goto "#3"
      ]> $∅
    )%E
  |}.

  (* Definition of function [fsm_init]. *)
  Definition impl_fsm_init (global_xmalloc : loc): function := {|
    f_args := [
      ("m", void*);
      ("len", it_layout size_t)
    ];
    f_local_vars := [
      ("i", it_layout size_t);
      ("storage", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "storage" <-{ PtrOp }
          LocInfoE loc_252 (Call (LocInfoE loc_254 (global_xmalloc)) [@{expr} LocInfoE loc_255 ((LocInfoE loc_256 (i2v (layout_of struct_item).(ly_size) size_t)) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_257 (use{IntOp size_t} (LocInfoE loc_258 ("len"))))) ]) ;
        locinfo: loc_187 ;
        LocInfoE loc_247 ((LocInfoE loc_248 (!{PtrOp} (LocInfoE loc_249 ("m")))) at{struct_fixed_size_map} "length") <-{ IntOp size_t }
          LocInfoE loc_250 (use{IntOp size_t} (LocInfoE loc_251 ("len"))) ;
        locinfo: loc_188 ;
        LocInfoE loc_242 ((LocInfoE loc_243 (!{PtrOp} (LocInfoE loc_244 ("m")))) at{struct_fixed_size_map} "items") <-{ PtrOp }
          LocInfoE loc_245 (use{PtrOp} (LocInfoE loc_246 ("storage"))) ;
        locinfo: loc_189 ;
        LocInfoE loc_237 ((LocInfoE loc_238 (!{PtrOp} (LocInfoE loc_239 ("m")))) at{struct_fixed_size_map} "count") <-{ IntOp size_t }
          LocInfoE loc_240 (use{IntOp size_t} (LocInfoE loc_241 ("len"))) ;
        locinfo: loc_191 ;
        LocInfoE loc_235 ("i") <-{ IntOp size_t }
          LocInfoE loc_236 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_236 (i2v 0 i32))) ;
        locinfo: loc_192 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_230 ;
        if{IntOp i32, None}: LocInfoE loc_230 ((LocInfoE loc_231 (use{IntOp size_t} (LocInfoE loc_232 ("i")))) <{IntOp size_t, IntOp size_t, i32} (LocInfoE loc_233 (use{IntOp size_t} (LocInfoE loc_234 ("len")))))
        then
        locinfo: loc_194 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_194 ;
        LocInfoE loc_217 ((LocInfoE loc_219 ((LocInfoE loc_222 (!{PtrOp} (LocInfoE loc_223 ((LocInfoE loc_224 (!{PtrOp} (LocInfoE loc_225 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_226 (use{IntOp size_t} (LocInfoE loc_227 ("i")))))) at{struct_item} "tag") <-{ IntOp size_t }
          LocInfoE loc_228 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_229 (i2v 0 i32))) ;
        locinfo: loc_195 ;
        LocInfoE loc_203 ((LocInfoE loc_204 ((LocInfoE loc_205 ((LocInfoE loc_207 ((LocInfoE loc_210 (!{PtrOp} (LocInfoE loc_211 ((LocInfoE loc_212 (!{PtrOp} (LocInfoE loc_213 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_214 (use{IntOp size_t} (LocInfoE loc_215 ("i")))))) at{struct_item} "u")) at_union{union_item_union} "empty")) at{struct_empty} "dummy") <-{ IntOp size_t }
          LocInfoE loc_216 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_216 (i2v 0 i32))) ;
        locinfo: loc_196 ;
        Goto "__cerb_continue1"
      ]> $
      <[ "#3" :=
        Return (VOID)
      ]> $
      <[ "__cerb_continue1" :=
        locinfo: loc_197 ;
        LocInfoE loc_198 ("i") <-{ IntOp size_t }
          LocInfoE loc_199 ((LocInfoE loc_200 (use{IntOp size_t} (LocInfoE loc_201 ("i")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_202 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_202 (i2v 1 i32))))) ;
        locinfo: loc_192 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [fsm_slot_for_key]. *)
  Definition impl_fsm_slot_for_key : function := {|
    f_args := [
      ("len", it_layout size_t);
      ("key", it_layout size_t)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_263 ;
        Return (LocInfoE loc_264 ((LocInfoE loc_265 (use{IntOp size_t} (LocInfoE loc_266 ("key")))) %{IntOp size_t, IntOp size_t} (LocInfoE loc_267 (use{IntOp size_t} (LocInfoE loc_268 ("len"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [fsm_probe]. *)
  Definition impl_fsm_probe (global_fsm_slot_for_key : loc): function := {|
    f_args := [
      ("m", void*);
      ("key", it_layout size_t)
    ];
    f_local_vars := [
      ("slot_idx", it_layout size_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "slot_idx" <-{ IntOp size_t }
          LocInfoE loc_388 (Call (LocInfoE loc_390 (global_fsm_slot_for_key)) [@{expr} LocInfoE loc_391 (use{IntOp size_t} (LocInfoE loc_392 ((LocInfoE loc_393 (!{PtrOp} (LocInfoE loc_394 ("m")))) at{struct_fixed_size_map} "length"))) ;
          LocInfoE loc_395 (use{IntOp size_t} (LocInfoE loc_396 ("key"))) ]) ;
        locinfo: loc_272 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_387 ;
        if{IntOp i32, None}: LocInfoE loc_387 (i2v 1 i32)
        then
        locinfo: loc_338 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_338 ;
        if{IntOp i32, Some "#4"}: LocInfoE loc_338 ((LocInfoE loc_339 ((LocInfoE loc_340 (use{IntOp size_t} (LocInfoE loc_341 ((LocInfoE loc_343 ((LocInfoE loc_346 (!{PtrOp} (LocInfoE loc_347 ((LocInfoE loc_348 (!{PtrOp} (LocInfoE loc_349 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_350 (use{IntOp size_t} (LocInfoE loc_351 ("slot_idx")))))) at{struct_item} "tag")))) ={IntOp size_t, IntOp size_t, i32} (LocInfoE loc_352 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_353 (i2v 0 i32)))))) ||{IntOp i32, IntOp i32, i32} (LocInfoE loc_354 ((LocInfoE loc_355 ((LocInfoE loc_356 (use{IntOp size_t} (LocInfoE loc_357 ((LocInfoE loc_359 ((LocInfoE loc_362 (!{PtrOp} (LocInfoE loc_363 ((LocInfoE loc_364 (!{PtrOp} (LocInfoE loc_365 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_366 (use{IntOp size_t} (LocInfoE loc_367 ("slot_idx")))))) at{struct_item} "tag")))) ={IntOp size_t, IntOp size_t, i32} (LocInfoE loc_368 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_369 (i2v 2 i32)))))) &&{IntOp i32, IntOp i32, i32} (LocInfoE loc_370 ((LocInfoE loc_371 (use{IntOp size_t} (LocInfoE loc_372 ((LocInfoE loc_373 ((LocInfoE loc_374 ((LocInfoE loc_376 ((LocInfoE loc_379 (!{PtrOp} (LocInfoE loc_380 ((LocInfoE loc_381 (!{PtrOp} (LocInfoE loc_382 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_383 (use{IntOp size_t} (LocInfoE loc_384 ("slot_idx")))))) at{struct_item} "u")) at_union{union_item_union} "tombstone")) at{struct_tombstone} "key")))) ={IntOp size_t, IntOp size_t, i32} (LocInfoE loc_385 (use{IntOp size_t} (LocInfoE loc_386 ("key")))))))))
        then
        locinfo: loc_334 ;
          Goto "#8"
        else
        locinfo: loc_300 ;
          Goto "#9"
      ]> $
      <[ "#3" :=
        Return (VOID)
      ]> $
      <[ "#4" :=
        locinfo: loc_300 ;
        if{IntOp i32, Some "#5"}: LocInfoE loc_300 ((LocInfoE loc_301 ((LocInfoE loc_302 (use{IntOp size_t} (LocInfoE loc_303 ((LocInfoE loc_305 ((LocInfoE loc_308 (!{PtrOp} (LocInfoE loc_309 ((LocInfoE loc_310 (!{PtrOp} (LocInfoE loc_311 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_312 (use{IntOp size_t} (LocInfoE loc_313 ("slot_idx")))))) at{struct_item} "tag")))) ={IntOp size_t, IntOp size_t, i32} (LocInfoE loc_314 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_315 (i2v 1 i32)))))) &&{IntOp i32, IntOp i32, i32} (LocInfoE loc_316 ((LocInfoE loc_317 (use{IntOp size_t} (LocInfoE loc_318 ((LocInfoE loc_319 ((LocInfoE loc_320 ((LocInfoE loc_322 ((LocInfoE loc_325 (!{PtrOp} (LocInfoE loc_326 ((LocInfoE loc_327 (!{PtrOp} (LocInfoE loc_328 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_329 (use{IntOp size_t} (LocInfoE loc_330 ("slot_idx")))))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "key")))) ={IntOp size_t, IntOp size_t, i32} (LocInfoE loc_331 (use{IntOp size_t} (LocInfoE loc_332 ("key")))))))
        then
        locinfo: loc_296 ;
          Goto "#6"
        else
        locinfo: loc_276 ;
          Goto "#7"
      ]> $
      <[ "#5" :=
        locinfo: loc_276 ;
        expr: (LocInfoE loc_289 ((LocInfoE loc_290 (use{IntOp size_t} (LocInfoE loc_291 ((LocInfoE loc_292 (!{PtrOp} (LocInfoE loc_293 ("m")))) at{struct_fixed_size_map} "length")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_294 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_294 (i2v 0 i32)))))) ;
        locinfo: loc_278 ;
        LocInfoE loc_279 ("slot_idx") <-{ IntOp size_t }
          LocInfoE loc_280 ((LocInfoE loc_281 ((LocInfoE loc_282 (use{IntOp size_t} (LocInfoE loc_283 ("slot_idx")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_284 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_284 (i2v 1 i32)))))) %{IntOp size_t, IntOp size_t} (LocInfoE loc_285 (use{IntOp size_t} (LocInfoE loc_286 ((LocInfoE loc_287 (!{PtrOp} (LocInfoE loc_288 ("m")))) at{struct_fixed_size_map} "length"))))) ;
        locinfo: loc_272 ;
        Goto "#1"
      ]> $
      <[ "#6" :=
        locinfo: loc_296 ;
        Return (LocInfoE loc_297 (use{IntOp size_t} (LocInfoE loc_298 ("slot_idx"))))
      ]> $
      <[ "#7" :=
        locinfo: loc_276 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        locinfo: loc_334 ;
        Return (LocInfoE loc_335 (use{IntOp size_t} (LocInfoE loc_336 ("slot_idx"))))
      ]> $
      <[ "#9" :=
        locinfo: loc_300 ;
        Goto "#4"
      ]> $∅
    )%E
  |}.

  (* Definition of function [fsm_insert]. *)
  Definition impl_fsm_insert (global_fsm_probe global_fsm_realloc_if_necessary : loc): function := {|
    f_args := [
      ("m", void*);
      ("key", it_layout size_t);
      ("value", void*)
    ];
    f_local_vars := [
      ("item", void*);
      ("replaced", void*);
      ("slot_idx", it_layout size_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_401 ;
        expr: (LocInfoE loc_401 (Call (LocInfoE loc_493 (global_fsm_realloc_if_necessary)) [@{expr} LocInfoE loc_494 (use{PtrOp} (LocInfoE loc_495 ("m"))) ])) ;
        "slot_idx" <-{ IntOp size_t }
          LocInfoE loc_483 (Call (LocInfoE loc_485 (global_fsm_probe)) [@{expr} LocInfoE loc_486 (use{PtrOp} (LocInfoE loc_487 ("m"))) ;
          LocInfoE loc_488 (use{IntOp size_t} (LocInfoE loc_489 ("key"))) ]) ;
        "replaced" <-{ PtrOp } LocInfoE loc_480 (NULL) ;
        "item" <-{ PtrOp }
          LocInfoE loc_467 (&(LocInfoE loc_469 ((LocInfoE loc_472 (!{PtrOp} (LocInfoE loc_473 ((LocInfoE loc_474 (!{PtrOp} (LocInfoE loc_475 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_476 (use{IntOp size_t} (LocInfoE loc_477 ("slot_idx"))))))) ;
        locinfo: loc_460 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_460 ((LocInfoE loc_461 (use{IntOp size_t} (LocInfoE loc_462 ((LocInfoE loc_463 (!{PtrOp} (LocInfoE loc_464 ("item")))) at{struct_item} "tag")))) ={IntOp size_t, IntOp size_t, i32} (LocInfoE loc_465 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_466 (i2v 1 i32)))))
        then
        locinfo: loc_432 ;
          Goto "#2"
        else
        locinfo: loc_453 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_406 ;
        LocInfoE loc_426 ((LocInfoE loc_427 (!{PtrOp} (LocInfoE loc_428 ("item")))) at{struct_item} "tag") <-{ IntOp size_t }
          LocInfoE loc_429 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_430 (i2v 1 i32))) ;
        locinfo: loc_407 ;
        LocInfoE loc_419 ((LocInfoE loc_420 ((LocInfoE loc_421 ((LocInfoE loc_422 (!{PtrOp} (LocInfoE loc_423 ("item")))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "key") <-{ IntOp size_t }
          LocInfoE loc_424 (use{IntOp size_t} (LocInfoE loc_425 ("key"))) ;
        locinfo: loc_408 ;
        LocInfoE loc_412 ((LocInfoE loc_413 ((LocInfoE loc_414 ((LocInfoE loc_415 (!{PtrOp} (LocInfoE loc_416 ("item")))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "value") <-{ PtrOp }
          LocInfoE loc_417 (use{PtrOp} (LocInfoE loc_418 ("value"))) ;
        locinfo: loc_409 ;
        Return (LocInfoE loc_410 (use{PtrOp} (LocInfoE loc_411 ("replaced"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_432 ;
        LocInfoE loc_433 ("replaced") <-{ PtrOp }
          LocInfoE loc_434 (use{PtrOp} (LocInfoE loc_435 ((LocInfoE loc_436 ((LocInfoE loc_437 ((LocInfoE loc_438 (!{PtrOp} (LocInfoE loc_439 ("item")))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "value"))) ;
        locinfo: loc_406 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_453 ;
        if{IntOp i32, None}: LocInfoE loc_453 ((LocInfoE loc_454 (use{IntOp size_t} (LocInfoE loc_455 ((LocInfoE loc_456 (!{PtrOp} (LocInfoE loc_457 ("item")))) at{struct_item} "tag")))) ={IntOp size_t, IntOp size_t, i32} (LocInfoE loc_458 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_459 (i2v 0 i32)))))
        then
        locinfo: loc_442 ;
          Goto "#4"
        else
        locinfo: loc_406 ;
          Goto "#5"
      ]> $
      <[ "#4" :=
        locinfo: loc_442 ;
        LocInfoE loc_443 ((LocInfoE loc_444 (!{PtrOp} (LocInfoE loc_445 ("m")))) at{struct_fixed_size_map} "count") <-{ IntOp size_t }
          LocInfoE loc_446 ((LocInfoE loc_447 (use{IntOp size_t} (LocInfoE loc_448 ((LocInfoE loc_449 (!{PtrOp} (LocInfoE loc_450 ("m")))) at{struct_fixed_size_map} "count")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_451 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_451 (i2v 1 i32))))) ;
        locinfo: loc_406 ;
        Goto "#1"
      ]> $
      <[ "#5" :=
        locinfo: loc_406 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [fsm_get]. *)
  Definition impl_fsm_get (global_fsm_probe : loc): function := {|
    f_args := [
      ("m", void*);
      ("key", it_layout size_t)
    ];
    f_local_vars := [
      ("item", void*);
      ("slot_idx", it_layout size_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "slot_idx" <-{ IntOp size_t }
          LocInfoE loc_534 (Call (LocInfoE loc_536 (global_fsm_probe)) [@{expr} LocInfoE loc_537 (use{PtrOp} (LocInfoE loc_538 ("m"))) ;
          LocInfoE loc_539 (use{IntOp size_t} (LocInfoE loc_540 ("key"))) ]) ;
        "item" <-{ PtrOp }
          LocInfoE loc_521 (&(LocInfoE loc_523 ((LocInfoE loc_526 (!{PtrOp} (LocInfoE loc_527 ((LocInfoE loc_528 (!{PtrOp} (LocInfoE loc_529 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_530 (use{IntOp size_t} (LocInfoE loc_531 ("slot_idx"))))))) ;
        locinfo: loc_514 ;
        if{IntOp i32, None}: LocInfoE loc_514 ((LocInfoE loc_515 (use{IntOp size_t} (LocInfoE loc_516 ((LocInfoE loc_517 (!{PtrOp} (LocInfoE loc_518 ("item")))) at{struct_item} "tag")))) ={IntOp size_t, IntOp size_t, i32} (LocInfoE loc_519 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_520 (i2v 1 i32)))))
        then
        locinfo: loc_502 ;
          Goto "#1"
        else
        locinfo: loc_512 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_502 ;
        Return (LocInfoE loc_503 (&(LocInfoE loc_505 (!{PtrOp} (LocInfoE loc_506 ((LocInfoE loc_507 ((LocInfoE loc_508 ((LocInfoE loc_509 (!{PtrOp} (LocInfoE loc_510 ("item")))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "value"))))))
      ]> $
      <[ "#2" :=
        locinfo: loc_512 ;
        Return (LocInfoE loc_513 (NULL))
      ]> $∅
    )%E
  |}.

  (* Definition of function [fsm_remove]. *)
  Definition impl_fsm_remove (global_fsm_probe : loc): function := {|
    f_args := [
      ("m", void*);
      ("key", it_layout size_t)
    ];
    f_local_vars := [
      ("item", void*);
      ("removed", void*);
      ("slot_idx", it_layout size_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "slot_idx" <-{ IntOp size_t }
          LocInfoE loc_598 (Call (LocInfoE loc_600 (global_fsm_probe)) [@{expr} LocInfoE loc_601 (use{PtrOp} (LocInfoE loc_602 ("m"))) ;
          LocInfoE loc_603 (use{IntOp size_t} (LocInfoE loc_604 ("key"))) ]) ;
        "item" <-{ PtrOp }
          LocInfoE loc_585 (&(LocInfoE loc_587 ((LocInfoE loc_590 (!{PtrOp} (LocInfoE loc_591 ((LocInfoE loc_592 (!{PtrOp} (LocInfoE loc_593 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_594 (use{IntOp size_t} (LocInfoE loc_595 ("slot_idx"))))))) ;
        locinfo: loc_578 ;
        if{IntOp i32, None}: LocInfoE loc_578 ((LocInfoE loc_579 (use{IntOp size_t} (LocInfoE loc_580 ((LocInfoE loc_581 (!{PtrOp} (LocInfoE loc_582 ("item")))) at{struct_item} "tag")))) ={IntOp size_t, IntOp size_t, i32} (LocInfoE loc_583 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_584 (i2v 1 i32)))))
        then
        locinfo: loc_550 ;
          Goto "#1"
        else
        locinfo: loc_576 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_550 ;
        LocInfoE loc_568 ("removed") <-{ PtrOp }
          LocInfoE loc_569 (use{PtrOp} (LocInfoE loc_570 ((LocInfoE loc_571 ((LocInfoE loc_572 ((LocInfoE loc_573 (!{PtrOp} (LocInfoE loc_574 ("item")))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "value"))) ;
        locinfo: loc_551 ;
        LocInfoE loc_563 ((LocInfoE loc_564 (!{PtrOp} (LocInfoE loc_565 ("item")))) at{struct_item} "tag") <-{ IntOp size_t }
          LocInfoE loc_566 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_567 (i2v 2 i32))) ;
        locinfo: loc_552 ;
        LocInfoE loc_556 ((LocInfoE loc_557 ((LocInfoE loc_558 ((LocInfoE loc_559 (!{PtrOp} (LocInfoE loc_560 ("item")))) at{struct_item} "u")) at_union{union_item_union} "tombstone")) at{struct_tombstone} "key") <-{ IntOp size_t }
          LocInfoE loc_561 (use{IntOp size_t} (LocInfoE loc_562 ("key"))) ;
        locinfo: loc_553 ;
        Return (LocInfoE loc_554 (use{PtrOp} (LocInfoE loc_555 ("removed"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_576 ;
        Return (LocInfoE loc_577 (NULL))
      ]> $∅
    )%E
  |}.

  (* Definition of function [compute_min_count]. *)
  Definition impl_compute_min_count : function := {|
    f_args := [
      ("len", it_layout size_t)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_609 ;
        Return (LocInfoE loc_610 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_610 (i2v 2 i32))))
      ]> $∅
    )%E
  |}.
End code.
