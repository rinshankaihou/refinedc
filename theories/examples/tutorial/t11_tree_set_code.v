From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t11_tree_set.c]. *)
Section code.
  Definition file_0 : string := "theories/examples/tutorial/t11_tree_set.c".
  Definition loc_2 : location_info := LocationInfo file_0 26 2 26 24.
  Definition loc_3 : location_info := LocationInfo file_0 26 9 26 23.
  Definition loc_6 : location_info := LocationInfo file_0 35 2 35 49.
  Definition loc_7 : location_info := LocationInfo file_0 36 2 36 30.
  Definition loc_8 : location_info := LocationInfo file_0 37 2 37 18.
  Definition loc_9 : location_info := LocationInfo file_0 38 2 38 31.
  Definition loc_10 : location_info := LocationInfo file_0 39 2 39 14.
  Definition loc_11 : location_info := LocationInfo file_0 39 9 39 13.
  Definition loc_12 : location_info := LocationInfo file_0 39 9 39 13.
  Definition loc_13 : location_info := LocationInfo file_0 38 2 38 13.
  Definition loc_14 : location_info := LocationInfo file_0 38 2 38 6.
  Definition loc_15 : location_info := LocationInfo file_0 38 2 38 6.
  Definition loc_16 : location_info := LocationInfo file_0 38 16 38 30.
  Definition loc_17 : location_info := LocationInfo file_0 37 2 37 11.
  Definition loc_18 : location_info := LocationInfo file_0 37 2 37 6.
  Definition loc_19 : location_info := LocationInfo file_0 37 2 37 6.
  Definition loc_20 : location_info := LocationInfo file_0 37 14 37 17.
  Definition loc_21 : location_info := LocationInfo file_0 37 14 37 17.
  Definition loc_22 : location_info := LocationInfo file_0 36 2 36 12.
  Definition loc_23 : location_info := LocationInfo file_0 36 2 36 6.
  Definition loc_24 : location_info := LocationInfo file_0 36 2 36 6.
  Definition loc_25 : location_info := LocationInfo file_0 36 15 36 29.
  Definition loc_26 : location_info := LocationInfo file_0 35 22 35 48.
  Definition loc_27 : location_info := LocationInfo file_0 35 22 35 27.
  Definition loc_28 : location_info := LocationInfo file_0 35 22 35 27.
  Definition loc_29 : location_info := LocationInfo file_0 35 28 35 47.
  Definition loc_34 : location_info := LocationInfo file_0 49 2 49 49.
  Definition loc_35 : location_info := LocationInfo file_0 50 2 50 20.
  Definition loc_36 : location_info := LocationInfo file_0 51 2 51 18.
  Definition loc_37 : location_info := LocationInfo file_0 52 2 52 22.
  Definition loc_38 : location_info := LocationInfo file_0 53 2 53 14.
  Definition loc_39 : location_info := LocationInfo file_0 53 9 53 13.
  Definition loc_40 : location_info := LocationInfo file_0 53 9 53 13.
  Definition loc_41 : location_info := LocationInfo file_0 52 2 52 13.
  Definition loc_42 : location_info := LocationInfo file_0 52 2 52 6.
  Definition loc_43 : location_info := LocationInfo file_0 52 2 52 6.
  Definition loc_44 : location_info := LocationInfo file_0 52 16 52 21.
  Definition loc_45 : location_info := LocationInfo file_0 52 16 52 21.
  Definition loc_46 : location_info := LocationInfo file_0 51 2 51 11.
  Definition loc_47 : location_info := LocationInfo file_0 51 2 51 6.
  Definition loc_48 : location_info := LocationInfo file_0 51 2 51 6.
  Definition loc_49 : location_info := LocationInfo file_0 51 14 51 17.
  Definition loc_50 : location_info := LocationInfo file_0 51 14 51 17.
  Definition loc_51 : location_info := LocationInfo file_0 50 2 50 12.
  Definition loc_52 : location_info := LocationInfo file_0 50 2 50 6.
  Definition loc_53 : location_info := LocationInfo file_0 50 2 50 6.
  Definition loc_54 : location_info := LocationInfo file_0 50 15 50 19.
  Definition loc_55 : location_info := LocationInfo file_0 50 15 50 19.
  Definition loc_56 : location_info := LocationInfo file_0 49 22 49 48.
  Definition loc_57 : location_info := LocationInfo file_0 49 22 49 27.
  Definition loc_58 : location_info := LocationInfo file_0 49 22 49 27.
  Definition loc_59 : location_info := LocationInfo file_0 49 28 49 47.
  Definition loc_64 : location_info := LocationInfo file_0 61 2 65 3.
  Definition loc_65 : location_info := LocationInfo file_0 61 26 65 3.
  Definition loc_66 : location_info := LocationInfo file_0 62 4 62 29.
  Definition loc_67 : location_info := LocationInfo file_0 63 4 63 30.
  Definition loc_68 : location_info := LocationInfo file_0 64 4 64 34.
  Definition loc_69 : location_info := LocationInfo file_0 64 4 64 8.
  Definition loc_70 : location_info := LocationInfo file_0 64 4 64 8.
  Definition loc_71 : location_info := LocationInfo file_0 64 9 64 28.
  Definition loc_72 : location_info := LocationInfo file_0 64 30 64 32.
  Definition loc_73 : location_info := LocationInfo file_0 64 30 64 32.
  Definition loc_74 : location_info := LocationInfo file_0 64 31 64 32.
  Definition loc_75 : location_info := LocationInfo file_0 64 31 64 32.
  Definition loc_76 : location_info := LocationInfo file_0 63 4 63 13.
  Definition loc_77 : location_info := LocationInfo file_0 63 4 63 13.
  Definition loc_78 : location_info := LocationInfo file_0 63 14 63 28.
  Definition loc_79 : location_info := LocationInfo file_0 63 15 63 28.
  Definition loc_80 : location_info := LocationInfo file_0 63 16 63 20.
  Definition loc_81 : location_info := LocationInfo file_0 63 16 63 20.
  Definition loc_82 : location_info := LocationInfo file_0 63 18 63 19.
  Definition loc_83 : location_info := LocationInfo file_0 63 18 63 19.
  Definition loc_84 : location_info := LocationInfo file_0 62 4 62 13.
  Definition loc_85 : location_info := LocationInfo file_0 62 4 62 13.
  Definition loc_86 : location_info := LocationInfo file_0 62 14 62 27.
  Definition loc_87 : location_info := LocationInfo file_0 62 15 62 27.
  Definition loc_88 : location_info := LocationInfo file_0 62 16 62 20.
  Definition loc_89 : location_info := LocationInfo file_0 62 16 62 20.
  Definition loc_90 : location_info := LocationInfo file_0 62 18 62 19.
  Definition loc_91 : location_info := LocationInfo file_0 62 18 62 19.
  Definition loc_93 : location_info := LocationInfo file_0 61 5 61 25.
  Definition loc_94 : location_info := LocationInfo file_0 61 5 61 7.
  Definition loc_95 : location_info := LocationInfo file_0 61 5 61 7.
  Definition loc_96 : location_info := LocationInfo file_0 61 6 61 7.
  Definition loc_97 : location_info := LocationInfo file_0 61 6 61 7.
  Definition loc_98 : location_info := LocationInfo file_0 61 11 61 25.
  Definition loc_101 : location_info := LocationInfo file_0 74 2 74 36.
  Definition loc_102 : location_info := LocationInfo file_0 75 2 75 30.
  Definition loc_103 : location_info := LocationInfo file_0 76 2 76 56.
  Definition loc_104 : location_info := LocationInfo file_0 77 2 77 39.
  Definition loc_105 : location_info := LocationInfo file_0 77 9 77 38.
  Definition loc_106 : location_info := LocationInfo file_0 77 9 77 19.
  Definition loc_107 : location_info := LocationInfo file_0 77 9 77 19.
  Definition loc_108 : location_info := LocationInfo file_0 77 20 77 34.
  Definition loc_109 : location_info := LocationInfo file_0 77 21 77 34.
  Definition loc_110 : location_info := LocationInfo file_0 77 22 77 26.
  Definition loc_111 : location_info := LocationInfo file_0 77 22 77 26.
  Definition loc_112 : location_info := LocationInfo file_0 77 24 77 25.
  Definition loc_113 : location_info := LocationInfo file_0 77 24 77 25.
  Definition loc_114 : location_info := LocationInfo file_0 77 36 77 37.
  Definition loc_115 : location_info := LocationInfo file_0 77 36 77 37.
  Definition loc_116 : location_info := LocationInfo file_0 76 20 76 56.
  Definition loc_117 : location_info := LocationInfo file_0 76 27 76 55.
  Definition loc_118 : location_info := LocationInfo file_0 76 27 76 37.
  Definition loc_119 : location_info := LocationInfo file_0 76 27 76 37.
  Definition loc_120 : location_info := LocationInfo file_0 76 38 76 51.
  Definition loc_121 : location_info := LocationInfo file_0 76 39 76 51.
  Definition loc_122 : location_info := LocationInfo file_0 76 40 76 44.
  Definition loc_123 : location_info := LocationInfo file_0 76 40 76 44.
  Definition loc_124 : location_info := LocationInfo file_0 76 42 76 43.
  Definition loc_125 : location_info := LocationInfo file_0 76 42 76 43.
  Definition loc_126 : location_info := LocationInfo file_0 76 53 76 54.
  Definition loc_127 : location_info := LocationInfo file_0 76 53 76 54.
  Definition loc_129 : location_info := LocationInfo file_0 76 5 76 18.
  Definition loc_130 : location_info := LocationInfo file_0 76 5 76 6.
  Definition loc_131 : location_info := LocationInfo file_0 76 5 76 6.
  Definition loc_132 : location_info := LocationInfo file_0 76 9 76 18.
  Definition loc_133 : location_info := LocationInfo file_0 76 9 76 18.
  Definition loc_134 : location_info := LocationInfo file_0 76 9 76 13.
  Definition loc_135 : location_info := LocationInfo file_0 76 9 76 13.
  Definition loc_136 : location_info := LocationInfo file_0 76 11 76 12.
  Definition loc_137 : location_info := LocationInfo file_0 76 11 76 12.
  Definition loc_138 : location_info := LocationInfo file_0 75 21 75 30.
  Definition loc_139 : location_info := LocationInfo file_0 75 28 75 29.
  Definition loc_141 : location_info := LocationInfo file_0 75 5 75 19.
  Definition loc_142 : location_info := LocationInfo file_0 75 5 75 14.
  Definition loc_143 : location_info := LocationInfo file_0 75 5 75 14.
  Definition loc_144 : location_info := LocationInfo file_0 75 5 75 9.
  Definition loc_145 : location_info := LocationInfo file_0 75 5 75 9.
  Definition loc_146 : location_info := LocationInfo file_0 75 7 75 8.
  Definition loc_147 : location_info := LocationInfo file_0 75 7 75 8.
  Definition loc_148 : location_info := LocationInfo file_0 75 18 75 19.
  Definition loc_149 : location_info := LocationInfo file_0 75 18 75 19.
  Definition loc_150 : location_info := LocationInfo file_0 74 27 74 36.
  Definition loc_151 : location_info := LocationInfo file_0 74 34 74 35.
  Definition loc_153 : location_info := LocationInfo file_0 74 5 74 25.
  Definition loc_154 : location_info := LocationInfo file_0 74 5 74 7.
  Definition loc_155 : location_info := LocationInfo file_0 74 5 74 7.
  Definition loc_156 : location_info := LocationInfo file_0 74 6 74 7.
  Definition loc_157 : location_info := LocationInfo file_0 74 6 74 7.
  Definition loc_158 : location_info := LocationInfo file_0 74 11 74 25.
  Definition loc_161 : location_info := LocationInfo file_0 86 2 86 20.
  Definition loc_162 : location_info := LocationInfo file_0 92 2 99 3.
  Definition loc_163 : location_info := LocationInfo file_0 100 2 100 11.
  Definition loc_164 : location_info := LocationInfo file_0 100 9 100 10.
  Definition loc_165 : location_info := LocationInfo file_0 92 2 99 3.
  Definition loc_166 : location_info := LocationInfo file_0 92 31 99 3.
  Definition loc_167 : location_info := LocationInfo file_0 93 4 93 34.
  Definition loc_168 : location_info := LocationInfo file_0 94 4 98 5.
  Definition loc_169 : location_info := LocationInfo file_0 92 2 99 3.
  Definition loc_170 : location_info := LocationInfo file_0 92 2 99 3.
  Definition loc_171 : location_info := LocationInfo file_0 94 23 96 5.
  Definition loc_172 : location_info := LocationInfo file_0 95 6 95 28.
  Definition loc_173 : location_info := LocationInfo file_0 95 6 95 9.
  Definition loc_174 : location_info := LocationInfo file_0 95 12 95 27.
  Definition loc_175 : location_info := LocationInfo file_0 95 13 95 27.
  Definition loc_176 : location_info := LocationInfo file_0 95 14 95 20.
  Definition loc_177 : location_info := LocationInfo file_0 95 14 95 20.
  Definition loc_178 : location_info := LocationInfo file_0 95 16 95 19.
  Definition loc_179 : location_info := LocationInfo file_0 95 16 95 19.
  Definition loc_180 : location_info := LocationInfo file_0 96 11 98 5.
  Definition loc_181 : location_info := LocationInfo file_0 97 6 97 29.
  Definition loc_182 : location_info := LocationInfo file_0 97 6 97 9.
  Definition loc_183 : location_info := LocationInfo file_0 97 12 97 28.
  Definition loc_184 : location_info := LocationInfo file_0 97 13 97 28.
  Definition loc_185 : location_info := LocationInfo file_0 97 14 97 20.
  Definition loc_186 : location_info := LocationInfo file_0 97 14 97 20.
  Definition loc_187 : location_info := LocationInfo file_0 97 16 97 19.
  Definition loc_188 : location_info := LocationInfo file_0 97 16 97 19.
  Definition loc_189 : location_info := LocationInfo file_0 94 7 94 22.
  Definition loc_190 : location_info := LocationInfo file_0 94 7 94 8.
  Definition loc_191 : location_info := LocationInfo file_0 94 7 94 8.
  Definition loc_192 : location_info := LocationInfo file_0 94 11 94 22.
  Definition loc_193 : location_info := LocationInfo file_0 94 11 94 22.
  Definition loc_194 : location_info := LocationInfo file_0 94 11 94 17.
  Definition loc_195 : location_info := LocationInfo file_0 94 11 94 17.
  Definition loc_196 : location_info := LocationInfo file_0 94 13 94 16.
  Definition loc_197 : location_info := LocationInfo file_0 94 13 94 16.
  Definition loc_198 : location_info := LocationInfo file_0 93 25 93 34.
  Definition loc_199 : location_info := LocationInfo file_0 93 32 93 33.
  Definition loc_201 : location_info := LocationInfo file_0 93 7 93 23.
  Definition loc_202 : location_info := LocationInfo file_0 93 7 93 18.
  Definition loc_203 : location_info := LocationInfo file_0 93 7 93 18.
  Definition loc_204 : location_info := LocationInfo file_0 93 7 93 13.
  Definition loc_205 : location_info := LocationInfo file_0 93 7 93 13.
  Definition loc_206 : location_info := LocationInfo file_0 93 9 93 12.
  Definition loc_207 : location_info := LocationInfo file_0 93 9 93 12.
  Definition loc_208 : location_info := LocationInfo file_0 93 22 93 23.
  Definition loc_209 : location_info := LocationInfo file_0 93 22 93 23.
  Definition loc_210 : location_info := LocationInfo file_0 92 8 92 30.
  Definition loc_211 : location_info := LocationInfo file_0 92 8 92 12.
  Definition loc_212 : location_info := LocationInfo file_0 92 8 92 12.
  Definition loc_213 : location_info := LocationInfo file_0 92 9 92 12.
  Definition loc_214 : location_info := LocationInfo file_0 92 9 92 12.
  Definition loc_215 : location_info := LocationInfo file_0 92 16 92 30.
  Definition loc_216 : location_info := LocationInfo file_0 86 16 86 19.
  Definition loc_217 : location_info := LocationInfo file_0 86 17 86 19.
  Definition loc_218 : location_info := LocationInfo file_0 86 18 86 19.
  Definition loc_219 : location_info := LocationInfo file_0 86 18 86 19.
  Definition loc_224 : location_info := LocationInfo file_0 109 2 118 3.
  Definition loc_225 : location_info := LocationInfo file_0 109 26 111 3.
  Definition loc_226 : location_info := LocationInfo file_0 110 4 110 49.
  Definition loc_227 : location_info := LocationInfo file_0 110 4 110 6.
  Definition loc_228 : location_info := LocationInfo file_0 110 5 110 6.
  Definition loc_229 : location_info := LocationInfo file_0 110 5 110 6.
  Definition loc_230 : location_info := LocationInfo file_0 110 9 110 48.
  Definition loc_231 : location_info := LocationInfo file_0 110 9 110 13.
  Definition loc_232 : location_info := LocationInfo file_0 110 9 110 13.
  Definition loc_233 : location_info := LocationInfo file_0 110 14 110 28.
  Definition loc_234 : location_info := LocationInfo file_0 110 30 110 31.
  Definition loc_235 : location_info := LocationInfo file_0 110 30 110 31.
  Definition loc_236 : location_info := LocationInfo file_0 110 33 110 47.
  Definition loc_237 : location_info := LocationInfo file_0 111 9 118 3.
  Definition loc_238 : location_info := LocationInfo file_0 112 4 112 30.
  Definition loc_239 : location_info := LocationInfo file_0 113 4 117 5.
  Definition loc_240 : location_info := LocationInfo file_0 113 21 115 5.
  Definition loc_241 : location_info := LocationInfo file_0 114 6 114 35.
  Definition loc_242 : location_info := LocationInfo file_0 114 6 114 16.
  Definition loc_243 : location_info := LocationInfo file_0 114 6 114 16.
  Definition loc_244 : location_info := LocationInfo file_0 114 17 114 30.
  Definition loc_245 : location_info := LocationInfo file_0 114 18 114 30.
  Definition loc_246 : location_info := LocationInfo file_0 114 19 114 23.
  Definition loc_247 : location_info := LocationInfo file_0 114 19 114 23.
  Definition loc_248 : location_info := LocationInfo file_0 114 21 114 22.
  Definition loc_249 : location_info := LocationInfo file_0 114 21 114 22.
  Definition loc_250 : location_info := LocationInfo file_0 114 32 114 33.
  Definition loc_251 : location_info := LocationInfo file_0 114 32 114 33.
  Definition loc_252 : location_info := LocationInfo file_0 115 11 117 5.
  Definition loc_253 : location_info := LocationInfo file_0 116 6 116 36.
  Definition loc_254 : location_info := LocationInfo file_0 116 6 116 16.
  Definition loc_255 : location_info := LocationInfo file_0 116 6 116 16.
  Definition loc_256 : location_info := LocationInfo file_0 116 17 116 31.
  Definition loc_257 : location_info := LocationInfo file_0 116 18 116 31.
  Definition loc_258 : location_info := LocationInfo file_0 116 19 116 23.
  Definition loc_259 : location_info := LocationInfo file_0 116 19 116 23.
  Definition loc_260 : location_info := LocationInfo file_0 116 21 116 22.
  Definition loc_261 : location_info := LocationInfo file_0 116 21 116 22.
  Definition loc_262 : location_info := LocationInfo file_0 116 33 116 34.
  Definition loc_263 : location_info := LocationInfo file_0 116 33 116 34.
  Definition loc_264 : location_info := LocationInfo file_0 113 7 113 20.
  Definition loc_265 : location_info := LocationInfo file_0 113 7 113 8.
  Definition loc_266 : location_info := LocationInfo file_0 113 7 113 8.
  Definition loc_267 : location_info := LocationInfo file_0 113 11 113 20.
  Definition loc_268 : location_info := LocationInfo file_0 113 11 113 20.
  Definition loc_269 : location_info := LocationInfo file_0 113 11 113 15.
  Definition loc_270 : location_info := LocationInfo file_0 113 11 113 15.
  Definition loc_271 : location_info := LocationInfo file_0 113 13 113 14.
  Definition loc_272 : location_info := LocationInfo file_0 113 13 113 14.
  Definition loc_273 : location_info := LocationInfo file_0 112 23 112 30.
  Definition loc_276 : location_info := LocationInfo file_0 112 7 112 21.
  Definition loc_277 : location_info := LocationInfo file_0 112 7 112 16.
  Definition loc_278 : location_info := LocationInfo file_0 112 7 112 16.
  Definition loc_279 : location_info := LocationInfo file_0 112 7 112 11.
  Definition loc_280 : location_info := LocationInfo file_0 112 7 112 11.
  Definition loc_281 : location_info := LocationInfo file_0 112 9 112 10.
  Definition loc_282 : location_info := LocationInfo file_0 112 9 112 10.
  Definition loc_283 : location_info := LocationInfo file_0 112 20 112 21.
  Definition loc_284 : location_info := LocationInfo file_0 112 20 112 21.
  Definition loc_285 : location_info := LocationInfo file_0 109 5 109 25.
  Definition loc_286 : location_info := LocationInfo file_0 109 5 109 7.
  Definition loc_287 : location_info := LocationInfo file_0 109 5 109 7.
  Definition loc_288 : location_info := LocationInfo file_0 109 6 109 7.
  Definition loc_289 : location_info := LocationInfo file_0 109 6 109 7.
  Definition loc_290 : location_info := LocationInfo file_0 109 11 109 25.
  Definition loc_293 : location_info := LocationInfo file_0 127 2 127 20.
  Definition loc_294 : location_info := LocationInfo file_0 132 2 139 3.
  Definition loc_295 : location_info := LocationInfo file_0 141 2 141 49.
  Definition loc_296 : location_info := LocationInfo file_0 141 2 141 6.
  Definition loc_297 : location_info := LocationInfo file_0 141 3 141 6.
  Definition loc_298 : location_info := LocationInfo file_0 141 3 141 6.
  Definition loc_299 : location_info := LocationInfo file_0 141 9 141 48.
  Definition loc_300 : location_info := LocationInfo file_0 141 9 141 13.
  Definition loc_301 : location_info := LocationInfo file_0 141 9 141 13.
  Definition loc_302 : location_info := LocationInfo file_0 141 14 141 28.
  Definition loc_303 : location_info := LocationInfo file_0 141 30 141 31.
  Definition loc_304 : location_info := LocationInfo file_0 141 30 141 31.
  Definition loc_305 : location_info := LocationInfo file_0 141 33 141 47.
  Definition loc_306 : location_info := LocationInfo file_0 132 2 139 3.
  Definition loc_307 : location_info := LocationInfo file_0 132 31 139 3.
  Definition loc_308 : location_info := LocationInfo file_0 133 4 133 32.
  Definition loc_309 : location_info := LocationInfo file_0 134 4 138 5.
  Definition loc_310 : location_info := LocationInfo file_0 132 2 139 3.
  Definition loc_311 : location_info := LocationInfo file_0 132 2 139 3.
  Definition loc_312 : location_info := LocationInfo file_0 134 23 136 5.
  Definition loc_313 : location_info := LocationInfo file_0 135 6 135 28.
  Definition loc_314 : location_info := LocationInfo file_0 135 6 135 9.
  Definition loc_315 : location_info := LocationInfo file_0 135 12 135 27.
  Definition loc_316 : location_info := LocationInfo file_0 135 13 135 27.
  Definition loc_317 : location_info := LocationInfo file_0 135 14 135 20.
  Definition loc_318 : location_info := LocationInfo file_0 135 14 135 20.
  Definition loc_319 : location_info := LocationInfo file_0 135 16 135 19.
  Definition loc_320 : location_info := LocationInfo file_0 135 16 135 19.
  Definition loc_321 : location_info := LocationInfo file_0 136 11 138 5.
  Definition loc_322 : location_info := LocationInfo file_0 137 6 137 29.
  Definition loc_323 : location_info := LocationInfo file_0 137 6 137 9.
  Definition loc_324 : location_info := LocationInfo file_0 137 12 137 28.
  Definition loc_325 : location_info := LocationInfo file_0 137 13 137 28.
  Definition loc_326 : location_info := LocationInfo file_0 137 14 137 20.
  Definition loc_327 : location_info := LocationInfo file_0 137 14 137 20.
  Definition loc_328 : location_info := LocationInfo file_0 137 16 137 19.
  Definition loc_329 : location_info := LocationInfo file_0 137 16 137 19.
  Definition loc_330 : location_info := LocationInfo file_0 134 7 134 22.
  Definition loc_331 : location_info := LocationInfo file_0 134 7 134 8.
  Definition loc_332 : location_info := LocationInfo file_0 134 7 134 8.
  Definition loc_333 : location_info := LocationInfo file_0 134 11 134 22.
  Definition loc_334 : location_info := LocationInfo file_0 134 11 134 22.
  Definition loc_335 : location_info := LocationInfo file_0 134 11 134 17.
  Definition loc_336 : location_info := LocationInfo file_0 134 11 134 17.
  Definition loc_337 : location_info := LocationInfo file_0 134 13 134 16.
  Definition loc_338 : location_info := LocationInfo file_0 134 13 134 16.
  Definition loc_339 : location_info := LocationInfo file_0 133 25 133 32.
  Definition loc_342 : location_info := LocationInfo file_0 133 7 133 23.
  Definition loc_343 : location_info := LocationInfo file_0 133 7 133 18.
  Definition loc_344 : location_info := LocationInfo file_0 133 7 133 18.
  Definition loc_345 : location_info := LocationInfo file_0 133 7 133 13.
  Definition loc_346 : location_info := LocationInfo file_0 133 7 133 13.
  Definition loc_347 : location_info := LocationInfo file_0 133 9 133 12.
  Definition loc_348 : location_info := LocationInfo file_0 133 9 133 12.
  Definition loc_349 : location_info := LocationInfo file_0 133 22 133 23.
  Definition loc_350 : location_info := LocationInfo file_0 133 22 133 23.
  Definition loc_351 : location_info := LocationInfo file_0 132 8 132 30.
  Definition loc_352 : location_info := LocationInfo file_0 132 8 132 12.
  Definition loc_353 : location_info := LocationInfo file_0 132 8 132 12.
  Definition loc_354 : location_info := LocationInfo file_0 132 9 132 12.
  Definition loc_355 : location_info := LocationInfo file_0 132 9 132 12.
  Definition loc_356 : location_info := LocationInfo file_0 132 16 132 30.
  Definition loc_357 : location_info := LocationInfo file_0 127 16 127 19.
  Definition loc_358 : location_info := LocationInfo file_0 127 17 127 19.
  Definition loc_359 : location_info := LocationInfo file_0 127 18 127 19.
  Definition loc_360 : location_info := LocationInfo file_0 127 18 127 19.
  Definition loc_365 : location_info := LocationInfo file_0 153 2 155 3.
  Definition loc_366 : location_info := LocationInfo file_0 156 2 156 22.
  Definition loc_367 : location_info := LocationInfo file_0 156 22 156 3.
  Definition loc_368 : location_info := LocationInfo file_0 157 2 157 34.
  Definition loc_369 : location_info := LocationInfo file_0 157 9 157 33.
  Definition loc_370 : location_info := LocationInfo file_0 157 9 157 17.
  Definition loc_371 : location_info := LocationInfo file_0 157 9 157 17.
  Definition loc_372 : location_info := LocationInfo file_0 157 18 157 32.
  Definition loc_373 : location_info := LocationInfo file_0 157 19 157 32.
  Definition loc_374 : location_info := LocationInfo file_0 157 20 157 24.
  Definition loc_375 : location_info := LocationInfo file_0 157 20 157 24.
  Definition loc_376 : location_info := LocationInfo file_0 157 22 157 23.
  Definition loc_377 : location_info := LocationInfo file_0 157 22 157 23.
  Definition loc_378 : location_info := LocationInfo file_0 156 2 156 21.
  Definition loc_379 : location_info := LocationInfo file_0 156 3 156 21.
  Definition loc_380 : location_info := LocationInfo file_0 156 4 156 15.
  Definition loc_381 : location_info := LocationInfo file_0 156 4 156 15.
  Definition loc_382 : location_info := LocationInfo file_0 156 4 156 8.
  Definition loc_383 : location_info := LocationInfo file_0 156 4 156 8.
  Definition loc_384 : location_info := LocationInfo file_0 156 6 156 7.
  Definition loc_385 : location_info := LocationInfo file_0 156 6 156 7.
  Definition loc_386 : location_info := LocationInfo file_0 153 36 155 3.
  Definition loc_387 : location_info := LocationInfo file_0 154 4 154 21.
  Definition loc_388 : location_info := LocationInfo file_0 154 11 154 20.
  Definition loc_389 : location_info := LocationInfo file_0 154 11 154 20.
  Definition loc_390 : location_info := LocationInfo file_0 154 11 154 15.
  Definition loc_391 : location_info := LocationInfo file_0 154 11 154 15.
  Definition loc_392 : location_info := LocationInfo file_0 154 13 154 14.
  Definition loc_393 : location_info := LocationInfo file_0 154 13 154 14.
  Definition loc_395 : location_info := LocationInfo file_0 153 5 153 34.
  Definition loc_396 : location_info := LocationInfo file_0 153 5 153 16.
  Definition loc_397 : location_info := LocationInfo file_0 153 5 153 16.
  Definition loc_398 : location_info := LocationInfo file_0 153 5 153 9.
  Definition loc_399 : location_info := LocationInfo file_0 153 5 153 9.
  Definition loc_400 : location_info := LocationInfo file_0 153 7 153 8.
  Definition loc_401 : location_info := LocationInfo file_0 153 7 153 8.
  Definition loc_402 : location_info := LocationInfo file_0 153 20 153 34.
  Definition loc_405 : location_info := LocationInfo file_0 170 2 172 3.
  Definition loc_406 : location_info := LocationInfo file_0 174 2 189 3.
  Definition loc_407 : location_info := LocationInfo file_0 174 21 185 3.
  Definition loc_408 : location_info := LocationInfo file_0 175 4 184 5.
  Definition loc_409 : location_info := LocationInfo file_0 175 36 180 5.
  Definition loc_410 : location_info := LocationInfo file_0 176 6 176 25.
  Definition loc_411 : location_info := LocationInfo file_0 176 25 176 7.
  Definition loc_412 : location_info := LocationInfo file_0 177 6 177 32.
  Definition loc_413 : location_info := LocationInfo file_0 178 6 178 29.
  Definition loc_414 : location_info := LocationInfo file_0 179 6 179 20.
  Definition loc_415 : location_info := LocationInfo file_0 179 6 179 15.
  Definition loc_416 : location_info := LocationInfo file_0 179 6 179 10.
  Definition loc_417 : location_info := LocationInfo file_0 179 6 179 10.
  Definition loc_418 : location_info := LocationInfo file_0 179 8 179 9.
  Definition loc_419 : location_info := LocationInfo file_0 179 8 179 9.
  Definition loc_420 : location_info := LocationInfo file_0 179 18 179 19.
  Definition loc_421 : location_info := LocationInfo file_0 179 18 179 19.
  Definition loc_422 : location_info := LocationInfo file_0 178 6 178 12.
  Definition loc_423 : location_info := LocationInfo file_0 178 6 178 12.
  Definition loc_424 : location_info := LocationInfo file_0 178 13 178 24.
  Definition loc_425 : location_info := LocationInfo file_0 178 14 178 24.
  Definition loc_426 : location_info := LocationInfo file_0 178 14 178 18.
  Definition loc_427 : location_info := LocationInfo file_0 178 14 178 18.
  Definition loc_428 : location_info := LocationInfo file_0 178 16 178 17.
  Definition loc_429 : location_info := LocationInfo file_0 178 16 178 17.
  Definition loc_430 : location_info := LocationInfo file_0 178 26 178 27.
  Definition loc_431 : location_info := LocationInfo file_0 178 26 178 27.
  Definition loc_432 : location_info := LocationInfo file_0 177 6 177 7.
  Definition loc_433 : location_info := LocationInfo file_0 177 10 177 31.
  Definition loc_434 : location_info := LocationInfo file_0 177 10 177 18.
  Definition loc_435 : location_info := LocationInfo file_0 177 10 177 18.
  Definition loc_436 : location_info := LocationInfo file_0 177 19 177 30.
  Definition loc_437 : location_info := LocationInfo file_0 177 20 177 30.
  Definition loc_438 : location_info := LocationInfo file_0 177 20 177 24.
  Definition loc_439 : location_info := LocationInfo file_0 177 20 177 24.
  Definition loc_440 : location_info := LocationInfo file_0 177 22 177 23.
  Definition loc_441 : location_info := LocationInfo file_0 177 22 177 23.
  Definition loc_442 : location_info := LocationInfo file_0 176 6 176 24.
  Definition loc_443 : location_info := LocationInfo file_0 176 7 176 24.
  Definition loc_444 : location_info := LocationInfo file_0 176 8 176 18.
  Definition loc_445 : location_info := LocationInfo file_0 176 8 176 18.
  Definition loc_446 : location_info := LocationInfo file_0 176 8 176 12.
  Definition loc_447 : location_info := LocationInfo file_0 176 8 176 12.
  Definition loc_448 : location_info := LocationInfo file_0 176 10 176 11.
  Definition loc_449 : location_info := LocationInfo file_0 176 10 176 11.
  Definition loc_450 : location_info := LocationInfo file_0 180 11 184 5.
  Definition loc_451 : location_info := LocationInfo file_0 181 6 181 24.
  Definition loc_452 : location_info := LocationInfo file_0 182 6 182 36.
  Definition loc_453 : location_info := LocationInfo file_0 183 6 183 15.
  Definition loc_454 : location_info := LocationInfo file_0 183 6 183 8.
  Definition loc_455 : location_info := LocationInfo file_0 183 7 183 8.
  Definition loc_456 : location_info := LocationInfo file_0 183 7 183 8.
  Definition loc_457 : location_info := LocationInfo file_0 183 11 183 14.
  Definition loc_458 : location_info := LocationInfo file_0 183 11 183 14.
  Definition loc_459 : location_info := LocationInfo file_0 182 6 182 10.
  Definition loc_460 : location_info := LocationInfo file_0 182 6 182 10.
  Definition loc_461 : location_info := LocationInfo file_0 182 11 182 30.
  Definition loc_462 : location_info := LocationInfo file_0 182 32 182 34.
  Definition loc_463 : location_info := LocationInfo file_0 182 32 182 34.
  Definition loc_464 : location_info := LocationInfo file_0 182 33 182 34.
  Definition loc_465 : location_info := LocationInfo file_0 182 33 182 34.
  Definition loc_466 : location_info := LocationInfo file_0 181 6 181 9.
  Definition loc_467 : location_info := LocationInfo file_0 181 12 181 23.
  Definition loc_468 : location_info := LocationInfo file_0 181 12 181 23.
  Definition loc_469 : location_info := LocationInfo file_0 181 12 181 16.
  Definition loc_470 : location_info := LocationInfo file_0 181 12 181 16.
  Definition loc_471 : location_info := LocationInfo file_0 181 14 181 15.
  Definition loc_472 : location_info := LocationInfo file_0 181 14 181 15.
  Definition loc_473 : location_info := LocationInfo file_0 175 7 175 35.
  Definition loc_474 : location_info := LocationInfo file_0 175 7 175 17.
  Definition loc_475 : location_info := LocationInfo file_0 175 7 175 17.
  Definition loc_476 : location_info := LocationInfo file_0 175 7 175 11.
  Definition loc_477 : location_info := LocationInfo file_0 175 7 175 11.
  Definition loc_478 : location_info := LocationInfo file_0 175 9 175 10.
  Definition loc_479 : location_info := LocationInfo file_0 175 9 175 10.
  Definition loc_480 : location_info := LocationInfo file_0 175 21 175 35.
  Definition loc_481 : location_info := LocationInfo file_0 185 9 189 3.
  Definition loc_482 : location_info := LocationInfo file_0 185 26 187 3.
  Definition loc_483 : location_info := LocationInfo file_0 186 4 186 27.
  Definition loc_484 : location_info := LocationInfo file_0 186 4 186 10.
  Definition loc_485 : location_info := LocationInfo file_0 186 4 186 10.
  Definition loc_486 : location_info := LocationInfo file_0 186 11 186 22.
  Definition loc_487 : location_info := LocationInfo file_0 186 12 186 22.
  Definition loc_488 : location_info := LocationInfo file_0 186 12 186 16.
  Definition loc_489 : location_info := LocationInfo file_0 186 12 186 16.
  Definition loc_490 : location_info := LocationInfo file_0 186 14 186 15.
  Definition loc_491 : location_info := LocationInfo file_0 186 14 186 15.
  Definition loc_492 : location_info := LocationInfo file_0 186 24 186 25.
  Definition loc_493 : location_info := LocationInfo file_0 186 24 186 25.
  Definition loc_494 : location_info := LocationInfo file_0 187 9 189 3.
  Definition loc_495 : location_info := LocationInfo file_0 188 4 188 28.
  Definition loc_496 : location_info := LocationInfo file_0 188 4 188 10.
  Definition loc_497 : location_info := LocationInfo file_0 188 4 188 10.
  Definition loc_498 : location_info := LocationInfo file_0 188 11 188 23.
  Definition loc_499 : location_info := LocationInfo file_0 188 12 188 23.
  Definition loc_500 : location_info := LocationInfo file_0 188 12 188 16.
  Definition loc_501 : location_info := LocationInfo file_0 188 12 188 16.
  Definition loc_502 : location_info := LocationInfo file_0 188 14 188 15.
  Definition loc_503 : location_info := LocationInfo file_0 188 14 188 15.
  Definition loc_504 : location_info := LocationInfo file_0 188 25 188 26.
  Definition loc_505 : location_info := LocationInfo file_0 188 25 188 26.
  Definition loc_506 : location_info := LocationInfo file_0 185 12 185 25.
  Definition loc_507 : location_info := LocationInfo file_0 185 12 185 13.
  Definition loc_508 : location_info := LocationInfo file_0 185 12 185 13.
  Definition loc_509 : location_info := LocationInfo file_0 185 16 185 25.
  Definition loc_510 : location_info := LocationInfo file_0 185 16 185 25.
  Definition loc_511 : location_info := LocationInfo file_0 185 16 185 20.
  Definition loc_512 : location_info := LocationInfo file_0 185 16 185 20.
  Definition loc_513 : location_info := LocationInfo file_0 185 18 185 19.
  Definition loc_514 : location_info := LocationInfo file_0 185 18 185 19.
  Definition loc_515 : location_info := LocationInfo file_0 174 5 174 19.
  Definition loc_516 : location_info := LocationInfo file_0 174 5 174 6.
  Definition loc_517 : location_info := LocationInfo file_0 174 5 174 6.
  Definition loc_518 : location_info := LocationInfo file_0 174 10 174 19.
  Definition loc_519 : location_info := LocationInfo file_0 174 10 174 19.
  Definition loc_520 : location_info := LocationInfo file_0 174 10 174 14.
  Definition loc_521 : location_info := LocationInfo file_0 174 10 174 14.
  Definition loc_522 : location_info := LocationInfo file_0 174 12 174 13.
  Definition loc_523 : location_info := LocationInfo file_0 174 12 174 13.
  Definition loc_524 : location_info := LocationInfo file_0 170 27 172 3.
  Definition loc_525 : location_info := LocationInfo file_0 171 4 171 11.
  Definition loc_528 : location_info := LocationInfo file_0 170 5 170 25.
  Definition loc_529 : location_info := LocationInfo file_0 170 5 170 7.
  Definition loc_530 : location_info := LocationInfo file_0 170 5 170 7.
  Definition loc_531 : location_info := LocationInfo file_0 170 6 170 7.
  Definition loc_532 : location_info := LocationInfo file_0 170 6 170 7.
  Definition loc_533 : location_info := LocationInfo file_0 170 11 170 25.
  Definition loc_536 : location_info := LocationInfo file_0 195 2 195 21.
  Definition loc_537 : location_info := LocationInfo file_0 196 2 196 14.
  Definition loc_538 : location_info := LocationInfo file_0 200 2 200 16.
  Definition loc_539 : location_info := LocationInfo file_0 202 2 202 24.
  Definition loc_540 : location_info := LocationInfo file_0 203 2 203 24.
  Definition loc_541 : location_info := LocationInfo file_0 205 2 205 16.
  Definition loc_542 : location_info := LocationInfo file_0 208 2 208 16.
  Definition loc_543 : location_info := LocationInfo file_0 209 2 209 24.
  Definition loc_544 : location_info := LocationInfo file_0 211 2 211 16.
  Definition loc_545 : location_info := LocationInfo file_0 214 2 214 16.
  Definition loc_546 : location_info := LocationInfo file_0 216 2 216 11.
  Definition loc_547 : location_info := LocationInfo file_0 216 9 216 10.
  Definition loc_548 : location_info := LocationInfo file_0 214 2 214 11.
  Definition loc_549 : location_info := LocationInfo file_0 214 2 214 11.
  Definition loc_550 : location_info := LocationInfo file_0 214 12 214 14.
  Definition loc_551 : location_info := LocationInfo file_0 214 13 214 14.
  Definition loc_552 : location_info := LocationInfo file_0 211 2 211 8.
  Definition loc_553 : location_info := LocationInfo file_0 211 2 211 8.
  Definition loc_554 : location_info := LocationInfo file_0 211 9 211 11.
  Definition loc_555 : location_info := LocationInfo file_0 211 10 211 11.
  Definition loc_556 : location_info := LocationInfo file_0 211 13 211 14.
  Definition loc_557 : location_info := LocationInfo file_0 209 9 209 22.
  Definition loc_558 : location_info := LocationInfo file_0 209 9 209 15.
  Definition loc_559 : location_info := LocationInfo file_0 209 9 209 15.
  Definition loc_560 : location_info := LocationInfo file_0 209 16 209 18.
  Definition loc_561 : location_info := LocationInfo file_0 209 17 209 18.
  Definition loc_562 : location_info := LocationInfo file_0 209 20 209 21.
  Definition loc_563 : location_info := LocationInfo file_0 208 2 208 8.
  Definition loc_564 : location_info := LocationInfo file_0 208 2 208 8.
  Definition loc_565 : location_info := LocationInfo file_0 208 9 208 11.
  Definition loc_566 : location_info := LocationInfo file_0 208 10 208 11.
  Definition loc_567 : location_info := LocationInfo file_0 208 13 208 14.
  Definition loc_568 : location_info := LocationInfo file_0 205 2 205 8.
  Definition loc_569 : location_info := LocationInfo file_0 205 2 205 8.
  Definition loc_570 : location_info := LocationInfo file_0 205 9 205 11.
  Definition loc_571 : location_info := LocationInfo file_0 205 10 205 11.
  Definition loc_572 : location_info := LocationInfo file_0 205 13 205 14.
  Definition loc_573 : location_info := LocationInfo file_0 203 9 203 22.
  Definition loc_574 : location_info := LocationInfo file_0 203 9 203 15.
  Definition loc_575 : location_info := LocationInfo file_0 203 9 203 15.
  Definition loc_576 : location_info := LocationInfo file_0 203 16 203 18.
  Definition loc_577 : location_info := LocationInfo file_0 203 17 203 18.
  Definition loc_578 : location_info := LocationInfo file_0 203 20 203 21.
  Definition loc_579 : location_info := LocationInfo file_0 202 9 202 22.
  Definition loc_580 : location_info := LocationInfo file_0 202 9 202 15.
  Definition loc_581 : location_info := LocationInfo file_0 202 9 202 15.
  Definition loc_582 : location_info := LocationInfo file_0 202 16 202 18.
  Definition loc_583 : location_info := LocationInfo file_0 202 17 202 18.
  Definition loc_584 : location_info := LocationInfo file_0 202 20 202 21.
  Definition loc_585 : location_info := LocationInfo file_0 200 2 200 8.
  Definition loc_586 : location_info := LocationInfo file_0 200 2 200 8.
  Definition loc_587 : location_info := LocationInfo file_0 200 9 200 11.
  Definition loc_588 : location_info := LocationInfo file_0 200 10 200 11.
  Definition loc_589 : location_info := LocationInfo file_0 200 13 200 14.
  Definition loc_590 : location_info := LocationInfo file_0 196 2 196 3.
  Definition loc_591 : location_info := LocationInfo file_0 196 6 196 13.
  Definition loc_592 : location_info := LocationInfo file_0 196 6 196 10.
  Definition loc_593 : location_info := LocationInfo file_0 196 6 196 10.
  Definition loc_594 : location_info := LocationInfo file_0 196 11 196 12.
  Definition loc_595 : location_info := LocationInfo file_0 195 13 195 20.
  Definition loc_596 : location_info := LocationInfo file_0 195 13 195 18.
  Definition loc_597 : location_info := LocationInfo file_0 195 13 195 18.

  (* Definition of struct [tree]. *)
  Program Definition struct_tree := {|
    sl_members := [
      (Some "left", LPtr);
      (Some "right", LPtr);
      (Some "key", it_layout size_t)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [empty]. *)
  Definition impl_empty : function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        Return (LocInfoE loc_3 (NULL))
      ]> $∅
    )%E
  |}.

  (* Definition of function [init]. *)
  Definition impl_init (alloc : loc): function := {|
    f_args := [
      ("key", it_layout size_t)
    ];
    f_local_vars := [
      ("node", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_26 ;
        "$0" <- LocInfoE loc_28 (alloc) with
          [ LocInfoE loc_29 (i2v (layout_of struct_tree).(ly_size) size_t) ] ;
        "node" <-{ LPtr }
          LocInfoE loc_26 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_26 ("$0"))) ;
        locinfo: loc_7 ;
        LocInfoE loc_22 ((LocInfoE loc_23 (!{LPtr} (LocInfoE loc_24 ("node")))) at{struct_tree} "left") <-{ LPtr }
          LocInfoE loc_25 (NULL) ;
        locinfo: loc_8 ;
        LocInfoE loc_17 ((LocInfoE loc_18 (!{LPtr} (LocInfoE loc_19 ("node")))) at{struct_tree} "key") <-{ it_layout size_t }
          LocInfoE loc_20 (use{it_layout size_t} (LocInfoE loc_21 ("key"))) ;
        locinfo: loc_9 ;
        LocInfoE loc_13 ((LocInfoE loc_14 (!{LPtr} (LocInfoE loc_15 ("node")))) at{struct_tree} "right") <-{ LPtr }
          LocInfoE loc_16 (NULL) ;
        locinfo: loc_10 ;
        Return (LocInfoE loc_11 (use{LPtr} (LocInfoE loc_12 ("node"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [node]. *)
  Definition impl_node (alloc : loc): function := {|
    f_args := [
      ("left", LPtr);
      ("key", it_layout size_t);
      ("right", LPtr)
    ];
    f_local_vars := [
      ("node", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_56 ;
        "$0" <- LocInfoE loc_58 (alloc) with
          [ LocInfoE loc_59 (i2v (layout_of struct_tree).(ly_size) size_t) ] ;
        "node" <-{ LPtr }
          LocInfoE loc_56 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_56 ("$0"))) ;
        locinfo: loc_35 ;
        LocInfoE loc_51 ((LocInfoE loc_52 (!{LPtr} (LocInfoE loc_53 ("node")))) at{struct_tree} "left") <-{ LPtr }
          LocInfoE loc_54 (use{LPtr} (LocInfoE loc_55 ("left"))) ;
        locinfo: loc_36 ;
        LocInfoE loc_46 ((LocInfoE loc_47 (!{LPtr} (LocInfoE loc_48 ("node")))) at{struct_tree} "key") <-{ it_layout size_t }
          LocInfoE loc_49 (use{it_layout size_t} (LocInfoE loc_50 ("key"))) ;
        locinfo: loc_37 ;
        LocInfoE loc_41 ((LocInfoE loc_42 (!{LPtr} (LocInfoE loc_43 ("node")))) at{struct_tree} "right") <-{ LPtr }
          LocInfoE loc_44 (use{LPtr} (LocInfoE loc_45 ("right"))) ;
        locinfo: loc_38 ;
        Return (LocInfoE loc_39 (use{LPtr} (LocInfoE loc_40 ("node"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [free_tree]. *)
  Definition impl_free_tree (free free_tree : loc): function := {|
    f_args := [
      ("t", LPtr)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_93 ;
        if: LocInfoE loc_93 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_93 ((LocInfoE loc_94 (use{LPtr} (LocInfoE loc_96 (!{LPtr} (LocInfoE loc_97 ("t")))))) !={PtrOp, PtrOp} (LocInfoE loc_98 (NULL)))))
        then
        locinfo: loc_66 ;
          Goto "#1"
        else
        Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_66 ;
        "_" <- LocInfoE loc_85 (free_tree) with
          [ LocInfoE loc_86 (&(LocInfoE loc_87 ((LocInfoE loc_88 (!{LPtr} (LocInfoE loc_90 (!{LPtr} (LocInfoE loc_91 ("t")))))) at{struct_tree} "left"))) ] ;
        locinfo: loc_67 ;
        "_" <- LocInfoE loc_77 (free_tree) with
          [ LocInfoE loc_78 (&(LocInfoE loc_79 ((LocInfoE loc_80 (!{LPtr} (LocInfoE loc_82 (!{LPtr} (LocInfoE loc_83 ("t")))))) at{struct_tree} "right"))) ] ;
        locinfo: loc_68 ;
        "_" <- LocInfoE loc_70 (free) with
          [ LocInfoE loc_71 (i2v (layout_of struct_tree).(ly_size) size_t) ;
          LocInfoE loc_72 (use{LPtr} (LocInfoE loc_74 (!{LPtr} (LocInfoE loc_75 ("t"))))) ] ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [member_rec]. *)
  Definition impl_member_rec (member_rec : loc): function := {|
    f_args := [
      ("t", LPtr);
      ("k", it_layout size_t)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_153 ;
        if: LocInfoE loc_153 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_153 ((LocInfoE loc_154 (use{LPtr} (LocInfoE loc_156 (!{LPtr} (LocInfoE loc_157 ("t")))))) ={PtrOp, PtrOp} (LocInfoE loc_158 (NULL)))))
        then
        locinfo: loc_150 ;
          Goto "#8"
        else
        locinfo: loc_141 ;
          Goto "#9"
      ]> $
      <[ "#1" :=
        locinfo: loc_141 ;
        if: LocInfoE loc_141 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_141 ((LocInfoE loc_142 (use{it_layout size_t} (LocInfoE loc_143 ((LocInfoE loc_144 (!{LPtr} (LocInfoE loc_146 (!{LPtr} (LocInfoE loc_147 ("t")))))) at{struct_tree} "key")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_148 (use{it_layout size_t} (LocInfoE loc_149 ("k")))))))
        then
        locinfo: loc_138 ;
          Goto "#6"
        else
        locinfo: loc_129 ;
          Goto "#7"
      ]> $
      <[ "#2" :=
        locinfo: loc_129 ;
        if: LocInfoE loc_129 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_129 ((LocInfoE loc_130 (use{it_layout size_t} (LocInfoE loc_131 ("k")))) <{IntOp size_t, IntOp size_t} (LocInfoE loc_132 (use{it_layout size_t} (LocInfoE loc_133 ((LocInfoE loc_134 (!{LPtr} (LocInfoE loc_136 (!{LPtr} (LocInfoE loc_137 ("t")))))) at{struct_tree} "key")))))))
        then
        locinfo: loc_117 ;
          Goto "#4"
        else
        locinfo: loc_105 ;
          Goto "#5"
      ]> $
      <[ "#3" :=
        locinfo: loc_105 ;
        "$0" <- LocInfoE loc_107 (member_rec) with
          [ LocInfoE loc_108 (&(LocInfoE loc_109 ((LocInfoE loc_110 (!{LPtr} (LocInfoE loc_112 (!{LPtr} (LocInfoE loc_113 ("t")))))) at{struct_tree} "right"))) ;
          LocInfoE loc_114 (use{it_layout size_t} (LocInfoE loc_115 ("k"))) ] ;
        locinfo: loc_104 ;
        Return (LocInfoE loc_105 ("$0"))
      ]> $
      <[ "#4" :=
        locinfo: loc_117 ;
        "$1" <- LocInfoE loc_119 (member_rec) with
          [ LocInfoE loc_120 (&(LocInfoE loc_121 ((LocInfoE loc_122 (!{LPtr} (LocInfoE loc_124 (!{LPtr} (LocInfoE loc_125 ("t")))))) at{struct_tree} "left"))) ;
          LocInfoE loc_126 (use{it_layout size_t} (LocInfoE loc_127 ("k"))) ] ;
        locinfo: loc_116 ;
        Return (LocInfoE loc_117 ("$1"))
      ]> $
      <[ "#5" :=
        locinfo: loc_105 ;
        Goto "#3"
      ]> $
      <[ "#6" :=
        locinfo: loc_138 ;
        Return (LocInfoE loc_139 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_139 (i2v 1 i32))))
      ]> $
      <[ "#7" :=
        locinfo: loc_129 ;
        Goto "#2"
      ]> $
      <[ "#8" :=
        locinfo: loc_150 ;
        Return (LocInfoE loc_151 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_151 (i2v 0 i32))))
      ]> $
      <[ "#9" :=
        locinfo: loc_141 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [member]. *)
  Definition impl_member : function := {|
    f_args := [
      ("t", LPtr);
      ("k", it_layout size_t)
    ];
    f_local_vars := [
      ("cur", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "cur" <-{ LPtr }
          LocInfoE loc_216 (&(LocInfoE loc_218 (!{LPtr} (LocInfoE loc_219 ("t"))))) ;
        locinfo: loc_162 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_210 ;
        if: LocInfoE loc_210 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_210 ((LocInfoE loc_211 (use{LPtr} (LocInfoE loc_213 (!{LPtr} (LocInfoE loc_214 ("cur")))))) !={PtrOp, PtrOp} (LocInfoE loc_215 (NULL)))))
        then
        locinfo: loc_201 ;
          Goto "#2"
        else
        locinfo: loc_163 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_201 ;
        if: LocInfoE loc_201 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_201 ((LocInfoE loc_202 (use{it_layout size_t} (LocInfoE loc_203 ((LocInfoE loc_204 (!{LPtr} (LocInfoE loc_206 (!{LPtr} (LocInfoE loc_207 ("cur")))))) at{struct_tree} "key")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_208 (use{it_layout size_t} (LocInfoE loc_209 ("k")))))))
        then
        locinfo: loc_198 ;
          Goto "#8"
        else
        locinfo: loc_189 ;
          Goto "#9"
      ]> $
      <[ "#3" :=
        locinfo: loc_163 ;
        Return (LocInfoE loc_164 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_164 (i2v 0 i32))))
      ]> $
      <[ "#4" :=
        locinfo: loc_189 ;
        if: LocInfoE loc_189 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_189 ((LocInfoE loc_190 (use{it_layout size_t} (LocInfoE loc_191 ("k")))) <{IntOp size_t, IntOp size_t} (LocInfoE loc_192 (use{it_layout size_t} (LocInfoE loc_193 ((LocInfoE loc_194 (!{LPtr} (LocInfoE loc_196 (!{LPtr} (LocInfoE loc_197 ("cur")))))) at{struct_tree} "key")))))))
        then
        locinfo: loc_172 ;
          Goto "#6"
        else
        locinfo: loc_181 ;
          Goto "#7"
      ]> $
      <[ "#5" :=
        locinfo: loc_169 ;
        Goto "continue13"
      ]> $
      <[ "#6" :=
        locinfo: loc_172 ;
        LocInfoE loc_173 ("cur") <-{ LPtr }
          LocInfoE loc_174 (&(LocInfoE loc_175 ((LocInfoE loc_176 (!{LPtr} (LocInfoE loc_178 (!{LPtr} (LocInfoE loc_179 ("cur")))))) at{struct_tree} "left"))) ;
        locinfo: loc_169 ;
        Goto "#5"
      ]> $
      <[ "#7" :=
        locinfo: loc_181 ;
        LocInfoE loc_182 ("cur") <-{ LPtr }
          LocInfoE loc_183 (&(LocInfoE loc_184 ((LocInfoE loc_185 (!{LPtr} (LocInfoE loc_187 (!{LPtr} (LocInfoE loc_188 ("cur")))))) at{struct_tree} "right"))) ;
        locinfo: loc_169 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        locinfo: loc_198 ;
        Return (LocInfoE loc_199 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_199 (i2v 1 i32))))
      ]> $
      <[ "#9" :=
        locinfo: loc_189 ;
        Goto "#4"
      ]> $
      <[ "continue13" :=
        locinfo: loc_162 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [insert_rec]. *)
  Definition impl_insert_rec (node insert_rec : loc): function := {|
    f_args := [
      ("t", LPtr);
      ("k", it_layout size_t)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_285 ;
        if: LocInfoE loc_285 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_285 ((LocInfoE loc_286 (use{LPtr} (LocInfoE loc_288 (!{LPtr} (LocInfoE loc_289 ("t")))))) ={PtrOp, PtrOp} (LocInfoE loc_290 (NULL)))))
        then
        locinfo: loc_230 ;
          Goto "#1"
        else
        locinfo: loc_276 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_230 ;
        "$0" <- LocInfoE loc_232 (node) with [ LocInfoE loc_233 (NULL) ;
          LocInfoE loc_234 (use{it_layout size_t} (LocInfoE loc_235 ("k"))) ;
          LocInfoE loc_236 (NULL) ] ;
        locinfo: loc_226 ;
        LocInfoE loc_228 (!{LPtr} (LocInfoE loc_229 ("t"))) <-{ LPtr }
          LocInfoE loc_230 ("$0") ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_276 ;
        if: LocInfoE loc_276 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_276 ((LocInfoE loc_277 (use{it_layout size_t} (LocInfoE loc_278 ((LocInfoE loc_279 (!{LPtr} (LocInfoE loc_281 (!{LPtr} (LocInfoE loc_282 ("t")))))) at{struct_tree} "key")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_283 (use{it_layout size_t} (LocInfoE loc_284 ("k")))))))
        then
        locinfo: loc_273 ;
          Goto "#6"
        else
        locinfo: loc_264 ;
          Goto "#7"
      ]> $
      <[ "#3" :=
        locinfo: loc_264 ;
        if: LocInfoE loc_264 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_264 ((LocInfoE loc_265 (use{it_layout size_t} (LocInfoE loc_266 ("k")))) <{IntOp size_t, IntOp size_t} (LocInfoE loc_267 (use{it_layout size_t} (LocInfoE loc_268 ((LocInfoE loc_269 (!{LPtr} (LocInfoE loc_271 (!{LPtr} (LocInfoE loc_272 ("t")))))) at{struct_tree} "key")))))))
        then
        locinfo: loc_241 ;
          Goto "#4"
        else
        locinfo: loc_253 ;
          Goto "#5"
      ]> $
      <[ "#4" :=
        locinfo: loc_241 ;
        "_" <- LocInfoE loc_243 (insert_rec) with
          [ LocInfoE loc_244 (&(LocInfoE loc_245 ((LocInfoE loc_246 (!{LPtr} (LocInfoE loc_248 (!{LPtr} (LocInfoE loc_249 ("t")))))) at{struct_tree} "left"))) ;
          LocInfoE loc_250 (use{it_layout size_t} (LocInfoE loc_251 ("k"))) ] ;
        Return (VOID)
      ]> $
      <[ "#5" :=
        locinfo: loc_253 ;
        "_" <- LocInfoE loc_255 (insert_rec) with
          [ LocInfoE loc_256 (&(LocInfoE loc_257 ((LocInfoE loc_258 (!{LPtr} (LocInfoE loc_260 (!{LPtr} (LocInfoE loc_261 ("t")))))) at{struct_tree} "right"))) ;
          LocInfoE loc_262 (use{it_layout size_t} (LocInfoE loc_263 ("k"))) ] ;
        Return (VOID)
      ]> $
      <[ "#6" :=
        locinfo: loc_273 ;
        Return (VOID)
      ]> $
      <[ "#7" :=
        locinfo: loc_264 ;
        Goto "#3"
      ]> $∅
    )%E
  |}.

  (* Definition of function [insert]. *)
  Definition impl_insert (node : loc): function := {|
    f_args := [
      ("t", LPtr);
      ("k", it_layout size_t)
    ];
    f_local_vars := [
      ("cur", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "cur" <-{ LPtr }
          LocInfoE loc_357 (&(LocInfoE loc_359 (!{LPtr} (LocInfoE loc_360 ("t"))))) ;
        locinfo: loc_294 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_351 ;
        if: LocInfoE loc_351 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_351 ((LocInfoE loc_352 (use{LPtr} (LocInfoE loc_354 (!{LPtr} (LocInfoE loc_355 ("cur")))))) !={PtrOp, PtrOp} (LocInfoE loc_356 (NULL)))))
        then
        locinfo: loc_342 ;
          Goto "#2"
        else
        locinfo: loc_299 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_342 ;
        if: LocInfoE loc_342 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_342 ((LocInfoE loc_343 (use{it_layout size_t} (LocInfoE loc_344 ((LocInfoE loc_345 (!{LPtr} (LocInfoE loc_347 (!{LPtr} (LocInfoE loc_348 ("cur")))))) at{struct_tree} "key")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_349 (use{it_layout size_t} (LocInfoE loc_350 ("k")))))))
        then
        locinfo: loc_339 ;
          Goto "#8"
        else
        locinfo: loc_330 ;
          Goto "#9"
      ]> $
      <[ "#3" :=
        locinfo: loc_299 ;
        "$0" <- LocInfoE loc_301 (node) with [ LocInfoE loc_302 (NULL) ;
          LocInfoE loc_303 (use{it_layout size_t} (LocInfoE loc_304 ("k"))) ;
          LocInfoE loc_305 (NULL) ] ;
        locinfo: loc_295 ;
        LocInfoE loc_297 (!{LPtr} (LocInfoE loc_298 ("cur"))) <-{ LPtr }
          LocInfoE loc_299 ("$0") ;
        Return (VOID)
      ]> $
      <[ "#4" :=
        locinfo: loc_330 ;
        if: LocInfoE loc_330 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_330 ((LocInfoE loc_331 (use{it_layout size_t} (LocInfoE loc_332 ("k")))) <{IntOp size_t, IntOp size_t} (LocInfoE loc_333 (use{it_layout size_t} (LocInfoE loc_334 ((LocInfoE loc_335 (!{LPtr} (LocInfoE loc_337 (!{LPtr} (LocInfoE loc_338 ("cur")))))) at{struct_tree} "key")))))))
        then
        locinfo: loc_313 ;
          Goto "#6"
        else
        locinfo: loc_322 ;
          Goto "#7"
      ]> $
      <[ "#5" :=
        locinfo: loc_310 ;
        Goto "continue25"
      ]> $
      <[ "#6" :=
        locinfo: loc_313 ;
        LocInfoE loc_314 ("cur") <-{ LPtr }
          LocInfoE loc_315 (&(LocInfoE loc_316 ((LocInfoE loc_317 (!{LPtr} (LocInfoE loc_319 (!{LPtr} (LocInfoE loc_320 ("cur")))))) at{struct_tree} "left"))) ;
        locinfo: loc_310 ;
        Goto "#5"
      ]> $
      <[ "#7" :=
        locinfo: loc_322 ;
        LocInfoE loc_323 ("cur") <-{ LPtr }
          LocInfoE loc_324 (&(LocInfoE loc_325 ((LocInfoE loc_326 (!{LPtr} (LocInfoE loc_328 (!{LPtr} (LocInfoE loc_329 ("cur")))))) at{struct_tree} "right"))) ;
        locinfo: loc_310 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        locinfo: loc_339 ;
        Return (VOID)
      ]> $
      <[ "#9" :=
        locinfo: loc_330 ;
        Goto "#4"
      ]> $
      <[ "continue25" :=
        locinfo: loc_294 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [tree_max]. *)
  Definition impl_tree_max (tree_max : loc): function := {|
    f_args := [
      ("t", LPtr)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_395 ;
        if: LocInfoE loc_395 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_395 ((LocInfoE loc_396 (use{LPtr} (LocInfoE loc_397 ((LocInfoE loc_398 (!{LPtr} (LocInfoE loc_400 (!{LPtr} (LocInfoE loc_401 ("t")))))) at{struct_tree} "right")))) ={PtrOp, PtrOp} (LocInfoE loc_402 (NULL)))))
        then
        locinfo: loc_387 ;
          Goto "#2"
        else
        locinfo: loc_366 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_366 ;
        expr: (LocInfoE loc_378 (&(LocInfoE loc_379 ((LocInfoE loc_380 (!{LPtr} (LocInfoE loc_381 ((LocInfoE loc_382 (!{LPtr} (LocInfoE loc_384 (!{LPtr} (LocInfoE loc_385 ("t")))))) at{struct_tree} "right")))) at{struct_tree} "key")))) ;
        locinfo: loc_369 ;
        "$0" <- LocInfoE loc_371 (tree_max) with
          [ LocInfoE loc_372 (&(LocInfoE loc_373 ((LocInfoE loc_374 (!{LPtr} (LocInfoE loc_376 (!{LPtr} (LocInfoE loc_377 ("t")))))) at{struct_tree} "right"))) ] ;
        locinfo: loc_368 ;
        Return (LocInfoE loc_369 ("$0"))
      ]> $
      <[ "#2" :=
        locinfo: loc_387 ;
        Return (LocInfoE loc_388 (use{it_layout size_t} (LocInfoE loc_389 ((LocInfoE loc_390 (!{LPtr} (LocInfoE loc_392 (!{LPtr} (LocInfoE loc_393 ("t")))))) at{struct_tree} "key"))))
      ]> $
      <[ "#3" :=
        locinfo: loc_366 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [remove]. *)
  Definition impl_remove (free tree_max remove : loc): function := {|
    f_args := [
      ("t", LPtr);
      ("k", it_layout size_t)
    ];
    f_local_vars := [
      ("m", it_layout size_t);
      ("tmp", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_528 ;
        if: LocInfoE loc_528 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_528 ((LocInfoE loc_529 (use{LPtr} (LocInfoE loc_531 (!{LPtr} (LocInfoE loc_532 ("t")))))) ={PtrOp, PtrOp} (LocInfoE loc_533 (NULL)))))
        then
        locinfo: loc_525 ;
          Goto "#8"
        else
        locinfo: loc_515 ;
          Goto "#9"
      ]> $
      <[ "#1" :=
        locinfo: loc_515 ;
        if: LocInfoE loc_515 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_515 ((LocInfoE loc_516 (use{it_layout size_t} (LocInfoE loc_517 ("k")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_518 (use{it_layout size_t} (LocInfoE loc_519 ((LocInfoE loc_520 (!{LPtr} (LocInfoE loc_522 (!{LPtr} (LocInfoE loc_523 ("t")))))) at{struct_tree} "key")))))))
        then
        locinfo: loc_473 ;
          Goto "#2"
        else
        locinfo: loc_506 ;
          Goto "#5"
      ]> $
      <[ "#2" :=
        locinfo: loc_473 ;
        if: LocInfoE loc_473 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_473 ((LocInfoE loc_474 (use{LPtr} (LocInfoE loc_475 ((LocInfoE loc_476 (!{LPtr} (LocInfoE loc_478 (!{LPtr} (LocInfoE loc_479 ("t")))))) at{struct_tree} "left")))) !={PtrOp, PtrOp} (LocInfoE loc_480 (NULL)))))
        then
        locinfo: loc_410 ;
          Goto "#3"
        else
        locinfo: loc_451 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_410 ;
        expr: (LocInfoE loc_442 (&(LocInfoE loc_443 ((LocInfoE loc_444 (!{LPtr} (LocInfoE loc_445 ((LocInfoE loc_446 (!{LPtr} (LocInfoE loc_448 (!{LPtr} (LocInfoE loc_449 ("t")))))) at{struct_tree} "left")))) at{struct_tree} "key")))) ;
        locinfo: loc_433 ;
        "$0" <- LocInfoE loc_435 (tree_max) with
          [ LocInfoE loc_436 (&(LocInfoE loc_437 ((LocInfoE loc_438 (!{LPtr} (LocInfoE loc_440 (!{LPtr} (LocInfoE loc_441 ("t")))))) at{struct_tree} "left"))) ] ;
        locinfo: loc_412 ;
        LocInfoE loc_432 ("m") <-{ it_layout size_t }
          LocInfoE loc_433 ("$0") ;
        locinfo: loc_413 ;
        "_" <- LocInfoE loc_423 (remove) with
          [ LocInfoE loc_424 (&(LocInfoE loc_425 ((LocInfoE loc_426 (!{LPtr} (LocInfoE loc_428 (!{LPtr} (LocInfoE loc_429 ("t")))))) at{struct_tree} "left"))) ;
          LocInfoE loc_430 (use{it_layout size_t} (LocInfoE loc_431 ("m"))) ] ;
        locinfo: loc_414 ;
        LocInfoE loc_415 ((LocInfoE loc_416 (!{LPtr} (LocInfoE loc_418 (!{LPtr} (LocInfoE loc_419 ("t")))))) at{struct_tree} "key") <-{ it_layout size_t }
          LocInfoE loc_420 (use{it_layout size_t} (LocInfoE loc_421 ("m"))) ;
        Return (VOID)
      ]> $
      <[ "#4" :=
        locinfo: loc_451 ;
        LocInfoE loc_466 ("tmp") <-{ LPtr }
          LocInfoE loc_467 (use{LPtr} (LocInfoE loc_468 ((LocInfoE loc_469 (!{LPtr} (LocInfoE loc_471 (!{LPtr} (LocInfoE loc_472 ("t")))))) at{struct_tree} "right"))) ;
        locinfo: loc_452 ;
        "_" <- LocInfoE loc_460 (free) with
          [ LocInfoE loc_461 (i2v (layout_of struct_tree).(ly_size) size_t) ;
          LocInfoE loc_462 (use{LPtr} (LocInfoE loc_464 (!{LPtr} (LocInfoE loc_465 ("t"))))) ] ;
        locinfo: loc_453 ;
        LocInfoE loc_455 (!{LPtr} (LocInfoE loc_456 ("t"))) <-{ LPtr }
          LocInfoE loc_457 (use{LPtr} (LocInfoE loc_458 ("tmp"))) ;
        Return (VOID)
      ]> $
      <[ "#5" :=
        locinfo: loc_506 ;
        if: LocInfoE loc_506 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_506 ((LocInfoE loc_507 (use{it_layout size_t} (LocInfoE loc_508 ("k")))) <{IntOp size_t, IntOp size_t} (LocInfoE loc_509 (use{it_layout size_t} (LocInfoE loc_510 ((LocInfoE loc_511 (!{LPtr} (LocInfoE loc_513 (!{LPtr} (LocInfoE loc_514 ("t")))))) at{struct_tree} "key")))))))
        then
        locinfo: loc_483 ;
          Goto "#6"
        else
        locinfo: loc_495 ;
          Goto "#7"
      ]> $
      <[ "#6" :=
        locinfo: loc_483 ;
        "_" <- LocInfoE loc_485 (remove) with
          [ LocInfoE loc_486 (&(LocInfoE loc_487 ((LocInfoE loc_488 (!{LPtr} (LocInfoE loc_490 (!{LPtr} (LocInfoE loc_491 ("t")))))) at{struct_tree} "left"))) ;
          LocInfoE loc_492 (use{it_layout size_t} (LocInfoE loc_493 ("k"))) ] ;
        Return (VOID)
      ]> $
      <[ "#7" :=
        locinfo: loc_495 ;
        "_" <- LocInfoE loc_497 (remove) with
          [ LocInfoE loc_498 (&(LocInfoE loc_499 ((LocInfoE loc_500 (!{LPtr} (LocInfoE loc_502 (!{LPtr} (LocInfoE loc_503 ("t")))))) at{struct_tree} "right"))) ;
          LocInfoE loc_504 (use{it_layout size_t} (LocInfoE loc_505 ("k"))) ] ;
        Return (VOID)
      ]> $
      <[ "#8" :=
        locinfo: loc_525 ;
        Return (VOID)
      ]> $
      <[ "#9" :=
        locinfo: loc_515 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [main]. *)
  Definition impl_main (empty init free_tree member insert remove : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
      ("t", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_595 ;
        "$4" <- LocInfoE loc_597 (empty) with [  ] ;
        "t" <-{ LPtr } LocInfoE loc_595 ("$4") ;
        locinfo: loc_591 ;
        "$3" <- LocInfoE loc_593 (init) with
          [ LocInfoE loc_594 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_594 (i2v 3 i32))) ] ;
        locinfo: loc_537 ;
        LocInfoE loc_590 ("t") <-{ LPtr } LocInfoE loc_591 ("$3") ;
        locinfo: loc_538 ;
        "_" <- LocInfoE loc_586 (insert) with
          [ LocInfoE loc_587 (&(LocInfoE loc_588 ("t"))) ;
          LocInfoE loc_589 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_589 (i2v 2 i32))) ] ;
        locinfo: loc_579 ;
        "$2" <- LocInfoE loc_581 (member) with
          [ LocInfoE loc_582 (&(LocInfoE loc_583 ("t"))) ;
          LocInfoE loc_584 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_584 (i2v 2 i32))) ] ;
        locinfo: loc_539 ;
        assert: (LocInfoE loc_579 ("$2")) ;
        locinfo: loc_573 ;
        "$1" <- LocInfoE loc_575 (member) with
          [ LocInfoE loc_576 (&(LocInfoE loc_577 ("t"))) ;
          LocInfoE loc_578 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_578 (i2v 3 i32))) ] ;
        locinfo: loc_540 ;
        assert: (LocInfoE loc_573 ("$1")) ;
        locinfo: loc_541 ;
        "_" <- LocInfoE loc_569 (remove) with
          [ LocInfoE loc_570 (&(LocInfoE loc_571 ("t"))) ;
          LocInfoE loc_572 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_572 (i2v 3 i32))) ] ;
        locinfo: loc_542 ;
        "_" <- LocInfoE loc_564 (insert) with
          [ LocInfoE loc_565 (&(LocInfoE loc_566 ("t"))) ;
          LocInfoE loc_567 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_567 (i2v 3 i32))) ] ;
        locinfo: loc_557 ;
        "$0" <- LocInfoE loc_559 (member) with
          [ LocInfoE loc_560 (&(LocInfoE loc_561 ("t"))) ;
          LocInfoE loc_562 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_562 (i2v 2 i32))) ] ;
        locinfo: loc_543 ;
        assert: (LocInfoE loc_557 ("$0")) ;
        locinfo: loc_544 ;
        "_" <- LocInfoE loc_553 (remove) with
          [ LocInfoE loc_554 (&(LocInfoE loc_555 ("t"))) ;
          LocInfoE loc_556 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_556 (i2v 3 i32))) ] ;
        locinfo: loc_545 ;
        "_" <- LocInfoE loc_549 (free_tree) with
          [ LocInfoE loc_550 (&(LocInfoE loc_551 ("t"))) ] ;
        locinfo: loc_546 ;
        Return (LocInfoE loc_547 (i2v 0 i32))
      ]> $∅
    )%E
  |}.
End code.
