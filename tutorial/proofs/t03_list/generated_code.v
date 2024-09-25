From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/t03_list.c]. *)
Section code.
  Definition file_0 : string := "tutorial/t03_list.c".
  Definition file_1 : string := "include/refinedc.h".
  Definition loc_2 : location_info := LocationInfo file_1 63 2 63 47.
  Definition loc_3 : location_info := LocationInfo file_1 63 9 63 46.
  Definition loc_4 : location_info := LocationInfo file_1 63 9 63 32.
  Definition loc_5 : location_info := LocationInfo file_1 63 33 63 37.
  Definition loc_6 : location_info := LocationInfo file_1 63 33 63 37.
  Definition loc_7 : location_info := LocationInfo file_1 63 39 63 45.
  Definition loc_8 : location_info := LocationInfo file_1 63 39 63 45.
  Definition loc_11 : location_info := LocationInfo file_0 170 4 170 25.
  Definition loc_12 : location_info := LocationInfo file_0 171 4 171 43.
  Definition loc_13 : location_info := LocationInfo file_0 172 4 172 43.
  Definition loc_14 : location_info := LocationInfo file_0 173 4 173 43.
  Definition loc_15 : location_info := LocationInfo file_0 175 4 175 28.
  Definition loc_16 : location_info := LocationInfo file_0 177 4 177 15.
  Definition loc_17 : location_info := LocationInfo file_0 178 4 178 15.
  Definition loc_18 : location_info := LocationInfo file_0 179 4 179 15.
  Definition loc_19 : location_info := LocationInfo file_0 181 4 181 29.
  Definition loc_20 : location_info := LocationInfo file_0 182 4 182 29.
  Definition loc_21 : location_info := LocationInfo file_0 183 4 183 29.
  Definition loc_22 : location_info := LocationInfo file_0 185 4 185 29.
  Definition loc_23 : location_info := LocationInfo file_0 187 4 187 25.
  Definition loc_24 : location_info := LocationInfo file_0 189 4 189 29.
  Definition loc_25 : location_info := LocationInfo file_0 191 4 191 23.
  Definition loc_26 : location_info := LocationInfo file_0 192 4 192 23.
  Definition loc_27 : location_info := LocationInfo file_0 193 4 193 23.
  Definition loc_28 : location_info := LocationInfo file_0 195 4 195 28.
  Definition loc_29 : location_info := LocationInfo file_0 197 4 197 32.
  Definition loc_30 : location_info := LocationInfo file_0 198 4 198 32.
  Definition loc_31 : location_info := LocationInfo file_0 199 4 199 32.
  Definition loc_32 : location_info := LocationInfo file_0 201 4 201 33.
  Definition loc_33 : location_info := LocationInfo file_0 202 4 202 33.
  Definition loc_34 : location_info := LocationInfo file_0 203 4 203 33.
  Definition loc_35 : location_info := LocationInfo file_0 203 4 203 9.
  Definition loc_36 : location_info := LocationInfo file_0 203 4 203 9.
  Definition loc_37 : location_info := LocationInfo file_0 203 10 203 24.
  Definition loc_38 : location_info := LocationInfo file_0 203 26 203 31.
  Definition loc_39 : location_info := LocationInfo file_0 203 26 203 31.
  Definition loc_40 : location_info := LocationInfo file_0 202 4 202 9.
  Definition loc_41 : location_info := LocationInfo file_0 202 4 202 9.
  Definition loc_42 : location_info := LocationInfo file_0 202 10 202 24.
  Definition loc_43 : location_info := LocationInfo file_0 202 26 202 31.
  Definition loc_44 : location_info := LocationInfo file_0 202 26 202 31.
  Definition loc_45 : location_info := LocationInfo file_0 201 4 201 9.
  Definition loc_46 : location_info := LocationInfo file_0 201 4 201 9.
  Definition loc_47 : location_info := LocationInfo file_0 201 10 201 24.
  Definition loc_48 : location_info := LocationInfo file_0 201 26 201 31.
  Definition loc_49 : location_info := LocationInfo file_0 201 26 201 31.
  Definition loc_50 : location_info := LocationInfo file_0 199 11 199 30.
  Definition loc_51 : location_info := LocationInfo file_0 199 11 199 17.
  Definition loc_52 : location_info := LocationInfo file_0 199 11 199 17.
  Definition loc_53 : location_info := LocationInfo file_0 199 12 199 17.
  Definition loc_54 : location_info := LocationInfo file_0 199 12 199 17.
  Definition loc_55 : location_info := LocationInfo file_0 199 21 199 30.
  Definition loc_56 : location_info := LocationInfo file_0 199 29 199 30.
  Definition loc_57 : location_info := LocationInfo file_0 198 11 198 30.
  Definition loc_58 : location_info := LocationInfo file_0 198 11 198 17.
  Definition loc_59 : location_info := LocationInfo file_0 198 11 198 17.
  Definition loc_60 : location_info := LocationInfo file_0 198 12 198 17.
  Definition loc_61 : location_info := LocationInfo file_0 198 12 198 17.
  Definition loc_62 : location_info := LocationInfo file_0 198 21 198 30.
  Definition loc_63 : location_info := LocationInfo file_0 198 29 198 30.
  Definition loc_64 : location_info := LocationInfo file_0 197 11 197 30.
  Definition loc_65 : location_info := LocationInfo file_0 197 11 197 17.
  Definition loc_66 : location_info := LocationInfo file_0 197 11 197 17.
  Definition loc_67 : location_info := LocationInfo file_0 197 12 197 17.
  Definition loc_68 : location_info := LocationInfo file_0 197 12 197 17.
  Definition loc_69 : location_info := LocationInfo file_0 197 21 197 30.
  Definition loc_70 : location_info := LocationInfo file_0 197 29 197 30.
  Definition loc_71 : location_info := LocationInfo file_0 195 11 195 26.
  Definition loc_72 : location_info := LocationInfo file_0 195 11 195 19.
  Definition loc_73 : location_info := LocationInfo file_0 195 11 195 19.
  Definition loc_74 : location_info := LocationInfo file_0 195 20 195 25.
  Definition loc_75 : location_info := LocationInfo file_0 195 21 195 25.
  Definition loc_76 : location_info := LocationInfo file_0 193 4 193 9.
  Definition loc_77 : location_info := LocationInfo file_0 193 12 193 22.
  Definition loc_78 : location_info := LocationInfo file_0 193 12 193 15.
  Definition loc_79 : location_info := LocationInfo file_0 193 12 193 15.
  Definition loc_80 : location_info := LocationInfo file_0 193 16 193 21.
  Definition loc_81 : location_info := LocationInfo file_0 193 17 193 21.
  Definition loc_82 : location_info := LocationInfo file_0 192 4 192 9.
  Definition loc_83 : location_info := LocationInfo file_0 192 12 192 22.
  Definition loc_84 : location_info := LocationInfo file_0 192 12 192 15.
  Definition loc_85 : location_info := LocationInfo file_0 192 12 192 15.
  Definition loc_86 : location_info := LocationInfo file_0 192 16 192 21.
  Definition loc_87 : location_info := LocationInfo file_0 192 17 192 21.
  Definition loc_88 : location_info := LocationInfo file_0 191 4 191 9.
  Definition loc_89 : location_info := LocationInfo file_0 191 12 191 22.
  Definition loc_90 : location_info := LocationInfo file_0 191 12 191 15.
  Definition loc_91 : location_info := LocationInfo file_0 191 12 191 15.
  Definition loc_92 : location_info := LocationInfo file_0 191 16 191 21.
  Definition loc_93 : location_info := LocationInfo file_0 191 17 191 21.
  Definition loc_94 : location_info := LocationInfo file_0 189 11 189 27.
  Definition loc_95 : location_info := LocationInfo file_0 189 11 189 17.
  Definition loc_96 : location_info := LocationInfo file_0 189 11 189 17.
  Definition loc_97 : location_info := LocationInfo file_0 189 18 189 23.
  Definition loc_98 : location_info := LocationInfo file_0 189 19 189 23.
  Definition loc_99 : location_info := LocationInfo file_0 189 25 189 26.
  Definition loc_100 : location_info := LocationInfo file_0 187 4 187 8.
  Definition loc_101 : location_info := LocationInfo file_0 187 11 187 24.
  Definition loc_102 : location_info := LocationInfo file_0 187 11 187 18.
  Definition loc_103 : location_info := LocationInfo file_0 187 11 187 18.
  Definition loc_104 : location_info := LocationInfo file_0 187 19 187 23.
  Definition loc_105 : location_info := LocationInfo file_0 187 19 187 23.
  Definition loc_106 : location_info := LocationInfo file_0 185 11 185 27.
  Definition loc_107 : location_info := LocationInfo file_0 185 11 185 17.
  Definition loc_108 : location_info := LocationInfo file_0 185 11 185 17.
  Definition loc_109 : location_info := LocationInfo file_0 185 18 185 23.
  Definition loc_110 : location_info := LocationInfo file_0 185 19 185 23.
  Definition loc_111 : location_info := LocationInfo file_0 185 25 185 26.
  Definition loc_112 : location_info := LocationInfo file_0 183 4 183 8.
  Definition loc_113 : location_info := LocationInfo file_0 183 11 183 28.
  Definition loc_114 : location_info := LocationInfo file_0 183 11 183 15.
  Definition loc_115 : location_info := LocationInfo file_0 183 11 183 15.
  Definition loc_116 : location_info := LocationInfo file_0 183 16 183 20.
  Definition loc_117 : location_info := LocationInfo file_0 183 16 183 20.
  Definition loc_118 : location_info := LocationInfo file_0 183 22 183 27.
  Definition loc_119 : location_info := LocationInfo file_0 183 22 183 27.
  Definition loc_120 : location_info := LocationInfo file_0 182 4 182 8.
  Definition loc_121 : location_info := LocationInfo file_0 182 11 182 28.
  Definition loc_122 : location_info := LocationInfo file_0 182 11 182 15.
  Definition loc_123 : location_info := LocationInfo file_0 182 11 182 15.
  Definition loc_124 : location_info := LocationInfo file_0 182 16 182 20.
  Definition loc_125 : location_info := LocationInfo file_0 182 16 182 20.
  Definition loc_126 : location_info := LocationInfo file_0 182 22 182 27.
  Definition loc_127 : location_info := LocationInfo file_0 182 22 182 27.
  Definition loc_128 : location_info := LocationInfo file_0 181 4 181 8.
  Definition loc_129 : location_info := LocationInfo file_0 181 11 181 28.
  Definition loc_130 : location_info := LocationInfo file_0 181 11 181 15.
  Definition loc_131 : location_info := LocationInfo file_0 181 11 181 15.
  Definition loc_132 : location_info := LocationInfo file_0 181 16 181 20.
  Definition loc_133 : location_info := LocationInfo file_0 181 16 181 20.
  Definition loc_134 : location_info := LocationInfo file_0 181 22 181 27.
  Definition loc_135 : location_info := LocationInfo file_0 181 22 181 27.
  Definition loc_136 : location_info := LocationInfo file_0 179 4 179 10.
  Definition loc_137 : location_info := LocationInfo file_0 179 5 179 10.
  Definition loc_138 : location_info := LocationInfo file_0 179 5 179 10.
  Definition loc_139 : location_info := LocationInfo file_0 179 13 179 14.
  Definition loc_140 : location_info := LocationInfo file_0 178 4 178 10.
  Definition loc_141 : location_info := LocationInfo file_0 178 5 178 10.
  Definition loc_142 : location_info := LocationInfo file_0 178 5 178 10.
  Definition loc_143 : location_info := LocationInfo file_0 178 13 178 14.
  Definition loc_144 : location_info := LocationInfo file_0 177 4 177 10.
  Definition loc_145 : location_info := LocationInfo file_0 177 5 177 10.
  Definition loc_146 : location_info := LocationInfo file_0 177 5 177 10.
  Definition loc_147 : location_info := LocationInfo file_0 177 13 177 14.
  Definition loc_148 : location_info := LocationInfo file_0 175 11 175 26.
  Definition loc_149 : location_info := LocationInfo file_0 175 11 175 19.
  Definition loc_150 : location_info := LocationInfo file_0 175 11 175 19.
  Definition loc_151 : location_info := LocationInfo file_0 175 20 175 25.
  Definition loc_152 : location_info := LocationInfo file_0 175 21 175 25.
  Definition loc_153 : location_info := LocationInfo file_0 173 20 173 42.
  Definition loc_154 : location_info := LocationInfo file_0 173 20 173 26.
  Definition loc_155 : location_info := LocationInfo file_0 173 20 173 26.
  Definition loc_156 : location_info := LocationInfo file_0 173 27 173 41.
  Definition loc_159 : location_info := LocationInfo file_0 172 20 172 42.
  Definition loc_160 : location_info := LocationInfo file_0 172 20 172 26.
  Definition loc_161 : location_info := LocationInfo file_0 172 20 172 26.
  Definition loc_162 : location_info := LocationInfo file_0 172 27 172 41.
  Definition loc_165 : location_info := LocationInfo file_0 171 20 171 42.
  Definition loc_166 : location_info := LocationInfo file_0 171 20 171 26.
  Definition loc_167 : location_info := LocationInfo file_0 171 20 171 26.
  Definition loc_168 : location_info := LocationInfo file_0 171 27 171 41.
  Definition loc_171 : location_info := LocationInfo file_0 170 18 170 24.
  Definition loc_172 : location_info := LocationInfo file_0 170 18 170 22.
  Definition loc_173 : location_info := LocationInfo file_0 170 18 170 22.
  Definition loc_178 : location_info := LocationInfo file_0 27 4 27 26.
  Definition loc_179 : location_info := LocationInfo file_0 27 11 27 25.
  Definition loc_182 : location_info := LocationInfo file_0 35 4 35 32.
  Definition loc_183 : location_info := LocationInfo file_0 35 11 35 31.
  Definition loc_184 : location_info := LocationInfo file_0 35 11 35 13.
  Definition loc_185 : location_info := LocationInfo file_0 35 11 35 13.
  Definition loc_186 : location_info := LocationInfo file_0 35 12 35 13.
  Definition loc_187 : location_info := LocationInfo file_0 35 12 35 13.
  Definition loc_188 : location_info := LocationInfo file_0 35 17 35 31.
  Definition loc_191 : location_info := LocationInfo file_0 43 4 43 52.
  Definition loc_192 : location_info := LocationInfo file_0 44 4 44 19.
  Definition loc_193 : location_info := LocationInfo file_0 45 4 45 19.
  Definition loc_194 : location_info := LocationInfo file_0 46 4 46 16.
  Definition loc_195 : location_info := LocationInfo file_0 46 11 46 15.
  Definition loc_196 : location_info := LocationInfo file_0 46 11 46 15.
  Definition loc_197 : location_info := LocationInfo file_0 45 4 45 14.
  Definition loc_198 : location_info := LocationInfo file_0 45 4 45 8.
  Definition loc_199 : location_info := LocationInfo file_0 45 4 45 8.
  Definition loc_200 : location_info := LocationInfo file_0 45 17 45 18.
  Definition loc_201 : location_info := LocationInfo file_0 45 17 45 18.
  Definition loc_202 : location_info := LocationInfo file_0 44 4 44 14.
  Definition loc_203 : location_info := LocationInfo file_0 44 4 44 8.
  Definition loc_204 : location_info := LocationInfo file_0 44 4 44 8.
  Definition loc_205 : location_info := LocationInfo file_0 44 17 44 18.
  Definition loc_206 : location_info := LocationInfo file_0 44 17 44 18.
  Definition loc_207 : location_info := LocationInfo file_0 43 24 43 51.
  Definition loc_208 : location_info := LocationInfo file_0 43 24 43 30.
  Definition loc_209 : location_info := LocationInfo file_0 43 24 43 30.
  Definition loc_210 : location_info := LocationInfo file_0 43 31 43 50.
  Definition loc_215 : location_info := LocationInfo file_0 55 2 57 3.
  Definition loc_216 : location_info := LocationInfo file_0 58 2 58 25.
  Definition loc_217 : location_info := LocationInfo file_0 59 2 59 25.
  Definition loc_218 : location_info := LocationInfo file_0 60 2 60 18.
  Definition loc_219 : location_info := LocationInfo file_0 61 2 61 35.
  Definition loc_220 : location_info := LocationInfo file_0 62 2 62 13.
  Definition loc_221 : location_info := LocationInfo file_0 62 9 62 12.
  Definition loc_222 : location_info := LocationInfo file_0 62 9 62 12.
  Definition loc_223 : location_info := LocationInfo file_0 61 2 61 7.
  Definition loc_224 : location_info := LocationInfo file_0 61 2 61 7.
  Definition loc_225 : location_info := LocationInfo file_0 61 8 61 27.
  Definition loc_226 : location_info := LocationInfo file_0 61 29 61 33.
  Definition loc_227 : location_info := LocationInfo file_0 61 29 61 33.
  Definition loc_228 : location_info := LocationInfo file_0 60 2 60 4.
  Definition loc_229 : location_info := LocationInfo file_0 60 3 60 4.
  Definition loc_230 : location_info := LocationInfo file_0 60 3 60 4.
  Definition loc_231 : location_info := LocationInfo file_0 60 7 60 17.
  Definition loc_232 : location_info := LocationInfo file_0 60 7 60 17.
  Definition loc_233 : location_info := LocationInfo file_0 60 7 60 11.
  Definition loc_234 : location_info := LocationInfo file_0 60 7 60 11.
  Definition loc_235 : location_info := LocationInfo file_0 59 14 59 24.
  Definition loc_236 : location_info := LocationInfo file_0 59 14 59 24.
  Definition loc_237 : location_info := LocationInfo file_0 59 14 59 18.
  Definition loc_238 : location_info := LocationInfo file_0 59 14 59 18.
  Definition loc_241 : location_info := LocationInfo file_0 58 22 58 24.
  Definition loc_242 : location_info := LocationInfo file_0 58 22 58 24.
  Definition loc_243 : location_info := LocationInfo file_0 58 23 58 24.
  Definition loc_244 : location_info := LocationInfo file_0 58 23 58 24.
  Definition loc_247 : location_info := LocationInfo file_0 55 28 57 3.
  Definition loc_248 : location_info := LocationInfo file_0 56 6 56 28.
  Definition loc_249 : location_info := LocationInfo file_0 56 13 56 27.
  Definition loc_250 : location_info := LocationInfo file_0 55 2 57 3.
  Definition loc_251 : location_info := LocationInfo file_0 55 6 55 26.
  Definition loc_252 : location_info := LocationInfo file_0 55 6 55 8.
  Definition loc_253 : location_info := LocationInfo file_0 55 6 55 8.
  Definition loc_254 : location_info := LocationInfo file_0 55 7 55 8.
  Definition loc_255 : location_info := LocationInfo file_0 55 7 55 8.
  Definition loc_256 : location_info := LocationInfo file_0 55 12 55 26.
  Definition loc_259 : location_info := LocationInfo file_0 69 4 69 16.
  Definition loc_260 : location_info := LocationInfo file_0 70 4 70 23.
  Definition loc_261 : location_info := LocationInfo file_0 74 4 79 5.
  Definition loc_262 : location_info := LocationInfo file_0 80 4 80 13.
  Definition loc_263 : location_info := LocationInfo file_0 80 11 80 12.
  Definition loc_264 : location_info := LocationInfo file_0 80 11 80 12.
  Definition loc_265 : location_info := LocationInfo file_0 74 32 79 5.
  Definition loc_266 : location_info := LocationInfo file_0 75 8 75 20.
  Definition loc_267 : location_info := LocationInfo file_0 76 8 76 20.
  Definition loc_268 : location_info := LocationInfo file_0 77 8 77 14.
  Definition loc_269 : location_info := LocationInfo file_0 78 8 78 14.
  Definition loc_270 : location_info := LocationInfo file_0 78 8 78 9.
  Definition loc_271 : location_info := LocationInfo file_0 78 12 78 13.
  Definition loc_272 : location_info := LocationInfo file_0 78 12 78 13.
  Definition loc_273 : location_info := LocationInfo file_0 77 8 77 9.
  Definition loc_274 : location_info := LocationInfo file_0 77 12 77 13.
  Definition loc_275 : location_info := LocationInfo file_0 77 12 77 13.
  Definition loc_276 : location_info := LocationInfo file_0 76 8 76 15.
  Definition loc_277 : location_info := LocationInfo file_0 76 8 76 9.
  Definition loc_278 : location_info := LocationInfo file_0 76 8 76 9.
  Definition loc_279 : location_info := LocationInfo file_0 76 18 76 19.
  Definition loc_280 : location_info := LocationInfo file_0 76 18 76 19.
  Definition loc_281 : location_info := LocationInfo file_0 75 8 75 9.
  Definition loc_282 : location_info := LocationInfo file_0 75 12 75 19.
  Definition loc_283 : location_info := LocationInfo file_0 75 12 75 19.
  Definition loc_284 : location_info := LocationInfo file_0 75 12 75 13.
  Definition loc_285 : location_info := LocationInfo file_0 75 12 75 13.
  Definition loc_286 : location_info := LocationInfo file_0 74 11 74 30.
  Definition loc_287 : location_info := LocationInfo file_0 74 11 74 12.
  Definition loc_288 : location_info := LocationInfo file_0 74 11 74 12.
  Definition loc_289 : location_info := LocationInfo file_0 74 16 74 30.
  Definition loc_290 : location_info := LocationInfo file_0 70 4 70 5.
  Definition loc_291 : location_info := LocationInfo file_0 70 8 70 22.
  Definition loc_294 : location_info := LocationInfo file_0 89 2 89 17.
  Definition loc_295 : location_info := LocationInfo file_0 93 2 96 3.
  Definition loc_296 : location_info := LocationInfo file_0 97 2 97 13.
  Definition loc_297 : location_info := LocationInfo file_0 97 9 97 12.
  Definition loc_298 : location_info := LocationInfo file_0 97 9 97 12.
  Definition loc_299 : location_info := LocationInfo file_0 93 31 96 3.
  Definition loc_300 : location_info := LocationInfo file_0 94 4 94 20.
  Definition loc_301 : location_info := LocationInfo file_0 95 4 95 13.
  Definition loc_302 : location_info := LocationInfo file_0 95 4 95 7.
  Definition loc_303 : location_info := LocationInfo file_0 95 4 95 12.
  Definition loc_304 : location_info := LocationInfo file_0 95 4 95 7.
  Definition loc_305 : location_info := LocationInfo file_0 95 4 95 7.
  Definition loc_306 : location_info := LocationInfo file_0 95 11 95 12.
  Definition loc_307 : location_info := LocationInfo file_0 94 4 94 5.
  Definition loc_308 : location_info := LocationInfo file_0 94 8 94 19.
  Definition loc_309 : location_info := LocationInfo file_0 94 9 94 19.
  Definition loc_310 : location_info := LocationInfo file_0 94 9 94 13.
  Definition loc_311 : location_info := LocationInfo file_0 94 9 94 13.
  Definition loc_312 : location_info := LocationInfo file_0 94 11 94 12.
  Definition loc_313 : location_info := LocationInfo file_0 94 11 94 12.
  Definition loc_314 : location_info := LocationInfo file_0 93 9 93 29.
  Definition loc_315 : location_info := LocationInfo file_0 93 9 93 11.
  Definition loc_316 : location_info := LocationInfo file_0 93 9 93 11.
  Definition loc_317 : location_info := LocationInfo file_0 93 10 93 11.
  Definition loc_318 : location_info := LocationInfo file_0 93 10 93 11.
  Definition loc_319 : location_info := LocationInfo file_0 93 15 93 29.
  Definition loc_320 : location_info := LocationInfo file_0 89 15 89 16.
  Definition loc_325 : location_info := LocationInfo file_0 106 2 108 3.
  Definition loc_326 : location_info := LocationInfo file_0 109 2 109 37.
  Definition loc_327 : location_info := LocationInfo file_0 109 9 109 36.
  Definition loc_328 : location_info := LocationInfo file_0 109 9 109 32.
  Definition loc_329 : location_info := LocationInfo file_0 109 9 109 23.
  Definition loc_330 : location_info := LocationInfo file_0 109 9 109 23.
  Definition loc_331 : location_info := LocationInfo file_0 109 24 109 31.
  Definition loc_332 : location_info := LocationInfo file_0 109 24 109 31.
  Definition loc_333 : location_info := LocationInfo file_0 109 24 109 25.
  Definition loc_334 : location_info := LocationInfo file_0 109 24 109 25.
  Definition loc_335 : location_info := LocationInfo file_0 109 35 109 36.
  Definition loc_336 : location_info := LocationInfo file_0 106 26 108 3.
  Definition loc_337 : location_info := LocationInfo file_0 107 4 107 13.
  Definition loc_338 : location_info := LocationInfo file_0 107 11 107 12.
  Definition loc_339 : location_info := LocationInfo file_0 106 2 108 3.
  Definition loc_340 : location_info := LocationInfo file_0 106 5 106 24.
  Definition loc_341 : location_info := LocationInfo file_0 106 5 106 6.
  Definition loc_342 : location_info := LocationInfo file_0 106 5 106 6.
  Definition loc_343 : location_info := LocationInfo file_0 106 10 106 24.
  Definition loc_346 : location_info := LocationInfo file_0 118 2 118 17.
  Definition loc_347 : location_info := LocationInfo file_0 122 2 125 3.
  Definition loc_348 : location_info := LocationInfo file_0 126 2 126 13.
  Definition loc_349 : location_info := LocationInfo file_0 126 9 126 12.
  Definition loc_350 : location_info := LocationInfo file_0 126 9 126 12.
  Definition loc_351 : location_info := LocationInfo file_0 122 30 125 3.
  Definition loc_352 : location_info := LocationInfo file_0 123 4 123 16.
  Definition loc_353 : location_info := LocationInfo file_0 124 4 124 13.
  Definition loc_354 : location_info := LocationInfo file_0 124 4 124 7.
  Definition loc_355 : location_info := LocationInfo file_0 124 4 124 12.
  Definition loc_356 : location_info := LocationInfo file_0 124 4 124 7.
  Definition loc_357 : location_info := LocationInfo file_0 124 4 124 7.
  Definition loc_358 : location_info := LocationInfo file_0 124 11 124 12.
  Definition loc_359 : location_info := LocationInfo file_0 123 4 123 5.
  Definition loc_360 : location_info := LocationInfo file_0 123 8 123 15.
  Definition loc_361 : location_info := LocationInfo file_0 123 8 123 15.
  Definition loc_362 : location_info := LocationInfo file_0 123 8 123 9.
  Definition loc_363 : location_info := LocationInfo file_0 123 8 123 9.
  Definition loc_364 : location_info := LocationInfo file_0 122 9 122 28.
  Definition loc_365 : location_info := LocationInfo file_0 122 9 122 10.
  Definition loc_366 : location_info := LocationInfo file_0 122 9 122 10.
  Definition loc_367 : location_info := LocationInfo file_0 122 14 122 28.
  Definition loc_368 : location_info := LocationInfo file_0 118 15 118 16.
  Definition loc_373 : location_info := LocationInfo file_0 133 2 133 19.
  Definition loc_374 : location_info := LocationInfo file_0 137 2 139 3.
  Definition loc_375 : location_info := LocationInfo file_0 140 2 140 12.
  Definition loc_376 : location_info := LocationInfo file_0 140 2 140 6.
  Definition loc_377 : location_info := LocationInfo file_0 140 3 140 6.
  Definition loc_378 : location_info := LocationInfo file_0 140 3 140 6.
  Definition loc_379 : location_info := LocationInfo file_0 140 9 140 11.
  Definition loc_380 : location_info := LocationInfo file_0 140 9 140 11.
  Definition loc_381 : location_info := LocationInfo file_0 137 31 139 3.
  Definition loc_382 : location_info := LocationInfo file_0 138 4 138 26.
  Definition loc_383 : location_info := LocationInfo file_0 138 4 138 7.
  Definition loc_384 : location_info := LocationInfo file_0 138 10 138 25.
  Definition loc_385 : location_info := LocationInfo file_0 138 11 138 25.
  Definition loc_386 : location_info := LocationInfo file_0 138 12 138 18.
  Definition loc_387 : location_info := LocationInfo file_0 138 12 138 18.
  Definition loc_388 : location_info := LocationInfo file_0 138 14 138 17.
  Definition loc_389 : location_info := LocationInfo file_0 138 14 138 17.
  Definition loc_390 : location_info := LocationInfo file_0 137 8 137 30.
  Definition loc_391 : location_info := LocationInfo file_0 137 8 137 12.
  Definition loc_392 : location_info := LocationInfo file_0 137 8 137 12.
  Definition loc_393 : location_info := LocationInfo file_0 137 9 137 12.
  Definition loc_394 : location_info := LocationInfo file_0 137 9 137 12.
  Definition loc_395 : location_info := LocationInfo file_0 137 16 137 30.
  Definition loc_396 : location_info := LocationInfo file_0 133 16 133 18.
  Definition loc_397 : location_info := LocationInfo file_0 133 16 133 18.
  Definition loc_402 : location_info := LocationInfo file_0 150 4 150 21.
  Definition loc_403 : location_info := LocationInfo file_0 155 4 164 5.
  Definition loc_404 : location_info := LocationInfo file_0 165 4 165 13.
  Definition loc_405 : location_info := LocationInfo file_0 165 11 165 12.
  Definition loc_406 : location_info := LocationInfo file_0 155 35 164 5.
  Definition loc_407 : location_info := LocationInfo file_0 156 8 156 27.
  Definition loc_408 : location_info := LocationInfo file_0 158 8 158 33.
  Definition loc_409 : location_info := LocationInfo file_0 159 8 161 9.
  Definition loc_410 : location_info := LocationInfo file_0 163 8 163 26.
  Definition loc_411 : location_info := LocationInfo file_0 163 8 163 12.
  Definition loc_412 : location_info := LocationInfo file_0 163 15 163 25.
  Definition loc_413 : location_info := LocationInfo file_0 163 16 163 25.
  Definition loc_414 : location_info := LocationInfo file_0 163 16 163 19.
  Definition loc_415 : location_info := LocationInfo file_0 163 16 163 19.
  Definition loc_416 : location_info := LocationInfo file_0 159 23 161 9.
  Definition loc_417 : location_info := LocationInfo file_0 160 12 160 21.
  Definition loc_418 : location_info := LocationInfo file_0 160 19 160 20.
  Definition loc_419 : location_info := LocationInfo file_0 159 8 161 9.
  Definition loc_420 : location_info := LocationInfo file_0 159 11 159 21.
  Definition loc_421 : location_info := LocationInfo file_0 159 11 159 16.
  Definition loc_422 : location_info := LocationInfo file_0 159 11 159 16.
  Definition loc_423 : location_info := LocationInfo file_0 159 12 159 16.
  Definition loc_424 : location_info := LocationInfo file_0 159 12 159 16.
  Definition loc_425 : location_info := LocationInfo file_0 159 20 159 21.
  Definition loc_426 : location_info := LocationInfo file_0 159 20 159 21.
  Definition loc_427 : location_info := LocationInfo file_0 158 23 158 32.
  Definition loc_428 : location_info := LocationInfo file_0 158 23 158 32.
  Definition loc_429 : location_info := LocationInfo file_0 158 23 158 26.
  Definition loc_430 : location_info := LocationInfo file_0 158 23 158 26.
  Definition loc_433 : location_info := LocationInfo file_0 156 21 156 26.
  Definition loc_434 : location_info := LocationInfo file_0 156 21 156 26.
  Definition loc_435 : location_info := LocationInfo file_0 156 22 156 26.
  Definition loc_436 : location_info := LocationInfo file_0 156 22 156 26.
  Definition loc_439 : location_info := LocationInfo file_0 155 10 155 33.
  Definition loc_440 : location_info := LocationInfo file_0 155 10 155 15.
  Definition loc_441 : location_info := LocationInfo file_0 155 10 155 15.
  Definition loc_442 : location_info := LocationInfo file_0 155 11 155 15.
  Definition loc_443 : location_info := LocationInfo file_0 155 11 155 15.
  Definition loc_444 : location_info := LocationInfo file_0 155 19 155 33.
  Definition loc_445 : location_info := LocationInfo file_0 150 19 150 20.
  Definition loc_446 : location_info := LocationInfo file_0 150 19 150 20.
  Definition loc_451 : location_info := LocationInfo file_0 210 2 210 18.
  Definition loc_452 : location_info := LocationInfo file_0 211 2 211 18.
  Definition loc_453 : location_info := LocationInfo file_0 220 2 225 3.
  Definition loc_454 : location_info := LocationInfo file_0 220 31 225 3.
  Definition loc_455 : location_info := LocationInfo file_0 221 4 221 25.
  Definition loc_456 : location_info := LocationInfo file_0 222 4 222 20.
  Definition loc_457 : location_info := LocationInfo file_0 223 4 223 14.
  Definition loc_458 : location_info := LocationInfo file_0 224 4 224 19.
  Definition loc_459 : location_info := LocationInfo file_0 224 4 224 7.
  Definition loc_460 : location_info := LocationInfo file_0 224 10 224 18.
  Definition loc_461 : location_info := LocationInfo file_0 224 10 224 18.
  Definition loc_462 : location_info := LocationInfo file_0 223 4 223 7.
  Definition loc_463 : location_info := LocationInfo file_0 223 5 223 7.
  Definition loc_464 : location_info := LocationInfo file_0 223 5 223 7.
  Definition loc_465 : location_info := LocationInfo file_0 223 10 223 13.
  Definition loc_466 : location_info := LocationInfo file_0 223 10 223 13.
  Definition loc_467 : location_info := LocationInfo file_0 222 4 222 13.
  Definition loc_468 : location_info := LocationInfo file_0 222 4 222 7.
  Definition loc_469 : location_info := LocationInfo file_0 222 4 222 7.
  Definition loc_470 : location_info := LocationInfo file_0 222 16 222 19.
  Definition loc_471 : location_info := LocationInfo file_0 222 16 222 19.
  Definition loc_472 : location_info := LocationInfo file_0 222 17 222 19.
  Definition loc_473 : location_info := LocationInfo file_0 222 17 222 19.
  Definition loc_474 : location_info := LocationInfo file_0 221 4 221 12.
  Definition loc_475 : location_info := LocationInfo file_0 221 15 221 24.
  Definition loc_476 : location_info := LocationInfo file_0 221 15 221 24.
  Definition loc_477 : location_info := LocationInfo file_0 221 15 221 18.
  Definition loc_478 : location_info := LocationInfo file_0 221 15 221 18.
  Definition loc_479 : location_info := LocationInfo file_0 220 8 220 29.
  Definition loc_480 : location_info := LocationInfo file_0 220 8 220 11.
  Definition loc_481 : location_info := LocationInfo file_0 220 8 220 11.
  Definition loc_482 : location_info := LocationInfo file_0 220 15 220 29.
  Definition loc_483 : location_info := LocationInfo file_0 210 15 210 17.
  Definition loc_484 : location_info := LocationInfo file_0 210 15 210 17.

  (* Definition of struct [__cerbty_unnamed_tag_486]. *)
  Program Definition struct___cerbty_unnamed_tag_486 := {|
    sl_members := [
      (Some "__dummy_max_align_t", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [list]. *)
  Program Definition struct_list := {|
    sl_members := [
      (Some "head", void*);
      (Some "tail", void*)
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

  (* Definition of function [test]. *)
  Definition impl_test (global_init global_is_empty global_member global_pop global_push global_reverse global_talloc global_tfree : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
      ("list", void*);
      ("elem2", void*);
      ("elem1", void*);
      ("elem3", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "list" <-{ PtrOp }
          LocInfoE loc_171 (Call (LocInfoE loc_173 (global_init)) [@{expr}  ]) ;
        "elem1" <-{ PtrOp }
          LocInfoE loc_165 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_165 (Call (LocInfoE loc_167 (global_talloc)) [@{expr} LocInfoE loc_168 (i2v (it_layout size_t).(ly_size) size_t) ]))) ;
        "elem2" <-{ PtrOp }
          LocInfoE loc_159 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_159 (Call (LocInfoE loc_161 (global_talloc)) [@{expr} LocInfoE loc_162 (i2v (it_layout size_t).(ly_size) size_t) ]))) ;
        "elem3" <-{ PtrOp }
          LocInfoE loc_153 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_153 (Call (LocInfoE loc_155 (global_talloc)) [@{expr} LocInfoE loc_156 (i2v (it_layout size_t).(ly_size) size_t) ]))) ;
        locinfo: loc_15 ;
        assert{BoolOp}: (LocInfoE loc_148 (Call (LocInfoE loc_150 (global_is_empty)) [@{expr} LocInfoE loc_151 (&(LocInfoE loc_152 ("list"))) ])) ;
        locinfo: loc_16 ;
        LocInfoE loc_145 (!{PtrOp} (LocInfoE loc_146 ("elem1"))) <-{ IntOp size_t }
          LocInfoE loc_147 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_147 (i2v 1 i32))) ;
        locinfo: loc_17 ;
        LocInfoE loc_141 (!{PtrOp} (LocInfoE loc_142 ("elem2"))) <-{ IntOp size_t }
          LocInfoE loc_143 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_143 (i2v 2 i32))) ;
        locinfo: loc_18 ;
        LocInfoE loc_137 (!{PtrOp} (LocInfoE loc_138 ("elem3"))) <-{ IntOp size_t }
          LocInfoE loc_139 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_139 (i2v 3 i32))) ;
        locinfo: loc_19 ;
        LocInfoE loc_128 ("list") <-{ PtrOp }
          LocInfoE loc_129 (Call (LocInfoE loc_131 (global_push)) [@{expr} LocInfoE loc_132 (use{PtrOp} (LocInfoE loc_133 ("list"))) ;
          LocInfoE loc_134 (use{PtrOp} (LocInfoE loc_135 ("elem1"))) ]) ;
        locinfo: loc_20 ;
        LocInfoE loc_120 ("list") <-{ PtrOp }
          LocInfoE loc_121 (Call (LocInfoE loc_123 (global_push)) [@{expr} LocInfoE loc_124 (use{PtrOp} (LocInfoE loc_125 ("list"))) ;
          LocInfoE loc_126 (use{PtrOp} (LocInfoE loc_127 ("elem2"))) ]) ;
        locinfo: loc_21 ;
        LocInfoE loc_112 ("list") <-{ PtrOp }
          LocInfoE loc_113 (Call (LocInfoE loc_115 (global_push)) [@{expr} LocInfoE loc_116 (use{PtrOp} (LocInfoE loc_117 ("list"))) ;
          LocInfoE loc_118 (use{PtrOp} (LocInfoE loc_119 ("elem3"))) ]) ;
        locinfo: loc_22 ;
        assert{BoolOp}: (LocInfoE loc_106 (Call (LocInfoE loc_108 (global_member)) [@{expr} LocInfoE loc_109 (&(LocInfoE loc_110 ("list"))) ;
        LocInfoE loc_111 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_111 (i2v 1 i32))) ])) ;
        locinfo: loc_23 ;
        LocInfoE loc_100 ("list") <-{ PtrOp }
          LocInfoE loc_101 (Call (LocInfoE loc_103 (global_reverse)) [@{expr} LocInfoE loc_104 (use{PtrOp} (LocInfoE loc_105 ("list"))) ]) ;
        locinfo: loc_24 ;
        assert{BoolOp}: (LocInfoE loc_94 (Call (LocInfoE loc_96 (global_member)) [@{expr} LocInfoE loc_97 (&(LocInfoE loc_98 ("list"))) ;
        LocInfoE loc_99 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_99 (i2v 1 i32))) ])) ;
        locinfo: loc_25 ;
        LocInfoE loc_88 ("elem1") <-{ PtrOp }
          LocInfoE loc_89 (Call (LocInfoE loc_91 (global_pop)) [@{expr} LocInfoE loc_92 (&(LocInfoE loc_93 ("list"))) ]) ;
        locinfo: loc_26 ;
        LocInfoE loc_82 ("elem2") <-{ PtrOp }
          LocInfoE loc_83 (Call (LocInfoE loc_85 (global_pop)) [@{expr} LocInfoE loc_86 (&(LocInfoE loc_87 ("list"))) ]) ;
        locinfo: loc_27 ;
        LocInfoE loc_76 ("elem3") <-{ PtrOp }
          LocInfoE loc_77 (Call (LocInfoE loc_79 (global_pop)) [@{expr} LocInfoE loc_80 (&(LocInfoE loc_81 ("list"))) ]) ;
        locinfo: loc_28 ;
        assert{BoolOp}: (LocInfoE loc_71 (Call (LocInfoE loc_73 (global_is_empty)) [@{expr} LocInfoE loc_74 (&(LocInfoE loc_75 ("list"))) ])) ;
        locinfo: loc_29 ;
        assert{IntOp i32}: (LocInfoE loc_64 ((LocInfoE loc_65 (use{IntOp size_t} (LocInfoE loc_67 (!{PtrOp} (LocInfoE loc_68 ("elem1")))))) ={IntOp size_t, IntOp size_t, i32} (LocInfoE loc_69 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_70 (i2v 1 i32)))))) ;
        locinfo: loc_30 ;
        assert{IntOp i32}: (LocInfoE loc_57 ((LocInfoE loc_58 (use{IntOp size_t} (LocInfoE loc_60 (!{PtrOp} (LocInfoE loc_61 ("elem2")))))) ={IntOp size_t, IntOp size_t, i32} (LocInfoE loc_62 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_63 (i2v 2 i32)))))) ;
        locinfo: loc_31 ;
        assert{IntOp i32}: (LocInfoE loc_50 ((LocInfoE loc_51 (use{IntOp size_t} (LocInfoE loc_53 (!{PtrOp} (LocInfoE loc_54 ("elem3")))))) ={IntOp size_t, IntOp size_t, i32} (LocInfoE loc_55 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_56 (i2v 3 i32)))))) ;
        locinfo: loc_32 ;
        expr: (LocInfoE loc_32 (Call (LocInfoE loc_46 (global_tfree)) [@{expr} LocInfoE loc_47 (i2v (it_layout size_t).(ly_size) size_t) ;
        LocInfoE loc_48 (use{PtrOp} (LocInfoE loc_49 ("elem1"))) ])) ;
        locinfo: loc_33 ;
        expr: (LocInfoE loc_33 (Call (LocInfoE loc_41 (global_tfree)) [@{expr} LocInfoE loc_42 (i2v (it_layout size_t).(ly_size) size_t) ;
        LocInfoE loc_43 (use{PtrOp} (LocInfoE loc_44 ("elem2"))) ])) ;
        locinfo: loc_34 ;
        expr: (LocInfoE loc_34 (Call (LocInfoE loc_36 (global_tfree)) [@{expr} LocInfoE loc_37 (i2v (it_layout size_t).(ly_size) size_t) ;
        LocInfoE loc_38 (use{PtrOp} (LocInfoE loc_39 ("elem3"))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [init]. *)
  Definition impl_init : function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_178 ;
        Return (LocInfoE loc_179 (NULL))
      ]> $∅
    )%E
  |}.

  (* Definition of function [is_empty]. *)
  Definition impl_is_empty : function := {|
    f_args := [
      ("l", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_182 ;
        Return (LocInfoE loc_183 (UnOp (CastOp $ BoolOp) (IntOp i32) (LocInfoE loc_183 ((LocInfoE loc_184 (use{PtrOp} (LocInfoE loc_186 (!{PtrOp} (LocInfoE loc_187 ("l")))))) ={PtrOp, PtrOp, i32} (LocInfoE loc_188 (NULL))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [push]. *)
  Definition impl_push (global_talloc : loc): function := {|
    f_args := [
      ("p", void*);
      ("e", void*)
    ];
    f_local_vars := [
      ("node", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "node" <-{ PtrOp }
          LocInfoE loc_207 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_207 (Call (LocInfoE loc_209 (global_talloc)) [@{expr} LocInfoE loc_210 (i2v (layout_of struct_list).(ly_size) size_t) ]))) ;
        locinfo: loc_192 ;
        LocInfoE loc_202 ((LocInfoE loc_203 (!{PtrOp} (LocInfoE loc_204 ("node")))) at{struct_list} "head") <-{ PtrOp }
          LocInfoE loc_205 (use{PtrOp} (LocInfoE loc_206 ("e"))) ;
        locinfo: loc_193 ;
        LocInfoE loc_197 ((LocInfoE loc_198 (!{PtrOp} (LocInfoE loc_199 ("node")))) at{struct_list} "tail") <-{ PtrOp }
          LocInfoE loc_200 (use{PtrOp} (LocInfoE loc_201 ("p"))) ;
        locinfo: loc_194 ;
        Return (LocInfoE loc_195 (use{PtrOp} (LocInfoE loc_196 ("node"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [pop]. *)
  Definition impl_pop (global_tfree : loc): function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("node", void*);
      ("ret", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_251 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_251 ((LocInfoE loc_252 (use{PtrOp} (LocInfoE loc_254 (!{PtrOp} (LocInfoE loc_255 ("p")))))) ={PtrOp, PtrOp, i32} (LocInfoE loc_256 (NULL)))
        then
        locinfo: loc_248 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#1" :=
        "node" <-{ PtrOp }
          LocInfoE loc_241 (use{PtrOp} (LocInfoE loc_243 (!{PtrOp} (LocInfoE loc_244 ("p"))))) ;
        "ret" <-{ PtrOp }
          LocInfoE loc_235 (use{PtrOp} (LocInfoE loc_236 ((LocInfoE loc_237 (!{PtrOp} (LocInfoE loc_238 ("node")))) at{struct_list} "head"))) ;
        locinfo: loc_218 ;
        LocInfoE loc_229 (!{PtrOp} (LocInfoE loc_230 ("p"))) <-{ PtrOp }
          LocInfoE loc_231 (use{PtrOp} (LocInfoE loc_232 ((LocInfoE loc_233 (!{PtrOp} (LocInfoE loc_234 ("node")))) at{struct_list} "tail"))) ;
        locinfo: loc_219 ;
        expr: (LocInfoE loc_219 (Call (LocInfoE loc_224 (global_tfree)) [@{expr} LocInfoE loc_225 (i2v (layout_of struct_list).(ly_size) size_t) ;
        LocInfoE loc_226 (use{PtrOp} (LocInfoE loc_227 ("node"))) ])) ;
        locinfo: loc_220 ;
        Return (LocInfoE loc_221 (use{PtrOp} (LocInfoE loc_222 ("ret"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_248 ;
        Return (LocInfoE loc_249 (NULL))
      ]> $
      <[ "#3" :=
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [reverse]. *)
  Definition impl_reverse : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("w", void*);
      ("t", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_260 ;
        LocInfoE loc_290 ("w") <-{ PtrOp } LocInfoE loc_291 (NULL) ;
        locinfo: loc_261 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_286 ;
        if{IntOp i32, None}: LocInfoE loc_286 ((LocInfoE loc_287 (use{PtrOp} (LocInfoE loc_288 ("p")))) !={PtrOp, PtrOp, i32} (LocInfoE loc_289 (NULL)))
        then
        locinfo: loc_266 ;
          Goto "#2"
        else
        locinfo: loc_262 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_266 ;
        LocInfoE loc_281 ("t") <-{ PtrOp }
          LocInfoE loc_282 (use{PtrOp} (LocInfoE loc_283 ((LocInfoE loc_284 (!{PtrOp} (LocInfoE loc_285 ("p")))) at{struct_list} "tail"))) ;
        locinfo: loc_267 ;
        LocInfoE loc_276 ((LocInfoE loc_277 (!{PtrOp} (LocInfoE loc_278 ("p")))) at{struct_list} "tail") <-{ PtrOp }
          LocInfoE loc_279 (use{PtrOp} (LocInfoE loc_280 ("w"))) ;
        locinfo: loc_268 ;
        LocInfoE loc_273 ("w") <-{ PtrOp }
          LocInfoE loc_274 (use{PtrOp} (LocInfoE loc_275 ("p"))) ;
        locinfo: loc_269 ;
        LocInfoE loc_270 ("p") <-{ PtrOp }
          LocInfoE loc_271 (use{PtrOp} (LocInfoE loc_272 ("t"))) ;
        locinfo: loc_261 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_262 ;
        Return (LocInfoE loc_263 (use{PtrOp} (LocInfoE loc_264 ("w"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [length]. *)
  Definition impl_length : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("len", it_layout size_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "len" <-{ IntOp size_t }
          LocInfoE loc_320 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_320 (i2v 0 i32))) ;
        locinfo: loc_295 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_314 ;
        if{IntOp i32, None}: LocInfoE loc_314 ((LocInfoE loc_315 (use{PtrOp} (LocInfoE loc_317 (!{PtrOp} (LocInfoE loc_318 ("p")))))) !={PtrOp, PtrOp, i32} (LocInfoE loc_319 (NULL)))
        then
        locinfo: loc_300 ;
          Goto "#2"
        else
        locinfo: loc_296 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_300 ;
        LocInfoE loc_307 ("p") <-{ PtrOp }
          LocInfoE loc_308 (&(LocInfoE loc_309 ((LocInfoE loc_310 (!{PtrOp} (LocInfoE loc_312 (!{PtrOp} (LocInfoE loc_313 ("p")))))) at{struct_list} "tail"))) ;
        locinfo: loc_301 ;
        LocInfoE loc_302 ("len") <-{ IntOp size_t }
          LocInfoE loc_303 ((LocInfoE loc_304 (use{IntOp size_t} (LocInfoE loc_305 ("len")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_306 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_306 (i2v 1 i32))))) ;
        locinfo: loc_295 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_296 ;
        Return (LocInfoE loc_297 (use{IntOp size_t} (LocInfoE loc_298 ("len"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [length_val_rec]. *)
  Definition impl_length_val_rec (global_length_val_rec : loc): function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_340 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_340 ((LocInfoE loc_341 (use{PtrOp} (LocInfoE loc_342 ("p")))) ={PtrOp, PtrOp, i32} (LocInfoE loc_343 (NULL)))
        then
        locinfo: loc_337 ;
          Goto "#2"
        else
        locinfo: loc_326 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_326 ;
        Return (LocInfoE loc_327 ((LocInfoE loc_328 (Call (LocInfoE loc_330 (global_length_val_rec)) [@{expr} LocInfoE loc_331 (use{PtrOp} (LocInfoE loc_332 ((LocInfoE loc_333 (!{PtrOp} (LocInfoE loc_334 ("p")))) at{struct_list} "tail"))) ])) +{IntOp size_t, IntOp size_t} (LocInfoE loc_335 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_335 (i2v 1 i32))))))
      ]> $
      <[ "#2" :=
        locinfo: loc_337 ;
        Return (LocInfoE loc_338 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_338 (i2v 0 i32))))
      ]> $
      <[ "#3" :=
        locinfo: loc_326 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [length_val]. *)
  Definition impl_length_val : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("len", it_layout size_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "len" <-{ IntOp size_t }
          LocInfoE loc_368 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_368 (i2v 0 i32))) ;
        locinfo: loc_347 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_364 ;
        if{IntOp i32, None}: LocInfoE loc_364 ((LocInfoE loc_365 (use{PtrOp} (LocInfoE loc_366 ("p")))) !={PtrOp, PtrOp, i32} (LocInfoE loc_367 (NULL)))
        then
        locinfo: loc_352 ;
          Goto "#2"
        else
        locinfo: loc_348 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_352 ;
        LocInfoE loc_359 ("p") <-{ PtrOp }
          LocInfoE loc_360 (use{PtrOp} (LocInfoE loc_361 ((LocInfoE loc_362 (!{PtrOp} (LocInfoE loc_363 ("p")))) at{struct_list} "tail"))) ;
        locinfo: loc_353 ;
        LocInfoE loc_354 ("len") <-{ IntOp size_t }
          LocInfoE loc_355 ((LocInfoE loc_356 (use{IntOp size_t} (LocInfoE loc_357 ("len")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_358 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_358 (i2v 1 i32))))) ;
        locinfo: loc_347 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_348 ;
        Return (LocInfoE loc_349 (use{IntOp size_t} (LocInfoE loc_350 ("len"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [append]. *)
  Definition impl_append : function := {|
    f_args := [
      ("l1", void*);
      ("l2", void*)
    ];
    f_local_vars := [
      ("end", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "end" <-{ PtrOp }
          LocInfoE loc_396 (use{PtrOp} (LocInfoE loc_397 ("l1"))) ;
        locinfo: loc_374 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_390 ;
        if{IntOp i32, None}: LocInfoE loc_390 ((LocInfoE loc_391 (use{PtrOp} (LocInfoE loc_393 (!{PtrOp} (LocInfoE loc_394 ("end")))))) !={PtrOp, PtrOp, i32} (LocInfoE loc_395 (NULL)))
        then
        locinfo: loc_382 ;
          Goto "#2"
        else
        locinfo: loc_375 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_382 ;
        LocInfoE loc_383 ("end") <-{ PtrOp }
          LocInfoE loc_384 (&(LocInfoE loc_385 ((LocInfoE loc_386 (!{PtrOp} (LocInfoE loc_388 (!{PtrOp} (LocInfoE loc_389 ("end")))))) at{struct_list} "tail"))) ;
        locinfo: loc_374 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_375 ;
        LocInfoE loc_377 (!{PtrOp} (LocInfoE loc_378 ("end"))) <-{ PtrOp }
          LocInfoE loc_379 (use{PtrOp} (LocInfoE loc_380 ("l2"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [member]. *)
  Definition impl_member : function := {|
    f_args := [
      ("p", void*);
      ("k", it_layout size_t)
    ];
    f_local_vars := [
      ("prev", void*);
      ("cur", void*);
      ("head", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "prev" <-{ PtrOp }
          LocInfoE loc_445 (use{PtrOp} (LocInfoE loc_446 ("p"))) ;
        locinfo: loc_403 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_439 ;
        if{IntOp i32, None}: LocInfoE loc_439 ((LocInfoE loc_440 (use{PtrOp} (LocInfoE loc_442 (!{PtrOp} (LocInfoE loc_443 ("prev")))))) !={PtrOp, PtrOp, i32} (LocInfoE loc_444 (NULL)))
        then
        Goto "#2"
        else
        locinfo: loc_404 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        "cur" <-{ PtrOp }
          LocInfoE loc_433 (use{PtrOp} (LocInfoE loc_435 (!{PtrOp} (LocInfoE loc_436 ("prev"))))) ;
        "head" <-{ PtrOp }
          LocInfoE loc_427 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_427 (use{PtrOp} (LocInfoE loc_428 ((LocInfoE loc_429 (!{PtrOp} (LocInfoE loc_430 ("cur")))) at{struct_list} "head"))))) ;
        locinfo: loc_420 ;
        if{IntOp i32, Some "#4"}: LocInfoE loc_420 ((LocInfoE loc_421 (use{IntOp size_t} (LocInfoE loc_423 (!{PtrOp} (LocInfoE loc_424 ("head")))))) ={IntOp size_t, IntOp size_t, i32} (LocInfoE loc_425 (use{IntOp size_t} (LocInfoE loc_426 ("k")))))
        then
        locinfo: loc_417 ;
          Goto "#5"
        else
        locinfo: loc_410 ;
          Goto "#6"
      ]> $
      <[ "#3" :=
        locinfo: loc_404 ;
        Return (LocInfoE loc_405 (UnOp (CastOp $ BoolOp) (IntOp i32) (LocInfoE loc_405 (i2v 0 i32))))
      ]> $
      <[ "#4" :=
        locinfo: loc_410 ;
        LocInfoE loc_411 ("prev") <-{ PtrOp }
          LocInfoE loc_412 (&(LocInfoE loc_413 ((LocInfoE loc_414 (!{PtrOp} (LocInfoE loc_415 ("cur")))) at{struct_list} "tail"))) ;
        locinfo: loc_403 ;
        Goto "#1"
      ]> $
      <[ "#5" :=
        locinfo: loc_417 ;
        Return (LocInfoE loc_418 (UnOp (CastOp $ BoolOp) (IntOp i32) (LocInfoE loc_418 (i2v 1 i32))))
      ]> $
      <[ "#6" :=
        locinfo: loc_410 ;
        Goto "#4"
      ]> $∅
    )%E
  |}.

  (* Definition of function [rev_append]. *)
  Definition impl_rev_append : function := {|
    f_args := [
      ("l1", void*);
      ("l2", void*)
    ];
    f_local_vars := [
      ("cur", void*);
      ("cur_tail", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "cur" <-{ PtrOp }
          LocInfoE loc_483 (use{PtrOp} (LocInfoE loc_484 ("l1"))) ;
        locinfo: loc_453 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_479 ;
        if{IntOp i32, None}: LocInfoE loc_479 ((LocInfoE loc_480 (use{PtrOp} (LocInfoE loc_481 ("cur")))) !={PtrOp, PtrOp, i32} (LocInfoE loc_482 (NULL)))
        then
        locinfo: loc_455 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_455 ;
        LocInfoE loc_474 ("cur_tail") <-{ PtrOp }
          LocInfoE loc_475 (use{PtrOp} (LocInfoE loc_476 ((LocInfoE loc_477 (!{PtrOp} (LocInfoE loc_478 ("cur")))) at{struct_list} "tail"))) ;
        locinfo: loc_456 ;
        LocInfoE loc_467 ((LocInfoE loc_468 (!{PtrOp} (LocInfoE loc_469 ("cur")))) at{struct_list} "tail") <-{ PtrOp }
          LocInfoE loc_470 (use{PtrOp} (LocInfoE loc_472 (!{PtrOp} (LocInfoE loc_473 ("l2"))))) ;
        locinfo: loc_457 ;
        LocInfoE loc_463 (!{PtrOp} (LocInfoE loc_464 ("l2"))) <-{ PtrOp }
          LocInfoE loc_465 (use{PtrOp} (LocInfoE loc_466 ("cur"))) ;
        locinfo: loc_458 ;
        LocInfoE loc_459 ("cur") <-{ PtrOp }
          LocInfoE loc_460 (use{PtrOp} (LocInfoE loc_461 ("cur_tail"))) ;
        locinfo: loc_453 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
