From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/mutable_map.c]. *)
Section code.
  Definition file_0 : string := "examples/mutable_map.c".
  Definition loc_2 : location_info := LocationInfo file_0 223 2 225 3.
  Definition loc_3 : location_info := LocationInfo file_0 227 2 227 89.
  Definition loc_4 : location_info := LocationInfo file_0 230 2 230 33.
  Definition loc_5 : location_info := LocationInfo file_0 232 2 232 25.
  Definition loc_6 : location_info := LocationInfo file_0 240 2 245 3.
  Definition loc_7 : location_info := LocationInfo file_0 240 2 245 3.
  Definition loc_8 : location_info := LocationInfo file_0 240 2 245 3.
  Definition loc_9 : location_info := LocationInfo file_0 246 2 246 55.
  Definition loc_10 : location_info := LocationInfo file_0 247 2 247 10.
  Definition loc_11 : location_info := LocationInfo file_0 247 2 247 4.
  Definition loc_12 : location_info := LocationInfo file_0 247 3 247 4.
  Definition loc_13 : location_info := LocationInfo file_0 247 3 247 4.
  Definition loc_14 : location_info := LocationInfo file_0 247 7 247 9.
  Definition loc_15 : location_info := LocationInfo file_0 247 7 247 9.
  Definition loc_16 : location_info := LocationInfo file_0 246 2 246 12.
  Definition loc_17 : location_info := LocationInfo file_0 246 2 246 12.
  Definition loc_18 : location_info := LocationInfo file_0 246 13 246 32.
  Definition loc_19 : location_info := LocationInfo file_0 246 34 246 43.
  Definition loc_20 : location_info := LocationInfo file_0 246 34 246 43.
  Definition loc_21 : location_info := LocationInfo file_0 246 34 246 35.
  Definition loc_22 : location_info := LocationInfo file_0 246 34 246 35.
  Definition loc_23 : location_info := LocationInfo file_0 246 45 246 53.
  Definition loc_24 : location_info := LocationInfo file_0 246 45 246 53.
  Definition loc_25 : location_info := LocationInfo file_0 246 45 246 46.
  Definition loc_26 : location_info := LocationInfo file_0 246 45 246 46.
  Definition loc_27 : location_info := LocationInfo file_0 240 43 245 3.
  Definition loc_28 : location_info := LocationInfo file_0 241 4 243 5.
  Definition loc_29 : location_info := LocationInfo file_0 244 4 244 17.
  Definition loc_30 : location_info := LocationInfo file_0 244 17 244 5.
  Definition loc_31 : location_info := LocationInfo file_0 240 2 245 3.
  Definition loc_33 : location_info := LocationInfo file_0 240 35 240 36.
  Definition loc_34 : location_info := LocationInfo file_0 240 35 240 41.
  Definition loc_35 : location_info := LocationInfo file_0 240 35 240 36.
  Definition loc_36 : location_info := LocationInfo file_0 240 35 240 36.
  Definition loc_37 : location_info := LocationInfo file_0 240 40 240 41.
  Definition loc_38 : location_info := LocationInfo file_0 244 4 244 16.
  Definition loc_39 : location_info := LocationInfo file_0 244 5 244 16.
  Definition loc_40 : location_info := LocationInfo file_0 244 6 244 8.
  Definition loc_41 : location_info := LocationInfo file_0 241 42 243 5.
  Definition loc_42 : location_info := LocationInfo file_0 242 6 242 80.
  Definition loc_43 : location_info := LocationInfo file_0 242 6 242 16.
  Definition loc_44 : location_info := LocationInfo file_0 242 6 242 16.
  Definition loc_45 : location_info := LocationInfo file_0 242 17 242 20.
  Definition loc_46 : location_info := LocationInfo file_0 242 18 242 20.
  Definition loc_47 : location_info := LocationInfo file_0 242 22 242 48.
  Definition loc_48 : location_info := LocationInfo file_0 242 22 242 48.
  Definition loc_49 : location_info := LocationInfo file_0 242 22 242 44.
  Definition loc_50 : location_info := LocationInfo file_0 242 22 242 38.
  Definition loc_51 : location_info := LocationInfo file_0 242 22 242 36.
  Definition loc_52 : location_info := LocationInfo file_0 242 22 242 36.
  Definition loc_53 : location_info := LocationInfo file_0 242 22 242 33.
  Definition loc_54 : location_info := LocationInfo file_0 242 22 242 33.
  Definition loc_55 : location_info := LocationInfo file_0 242 24 242 32.
  Definition loc_56 : location_info := LocationInfo file_0 242 24 242 32.
  Definition loc_57 : location_info := LocationInfo file_0 242 24 242 25.
  Definition loc_58 : location_info := LocationInfo file_0 242 24 242 25.
  Definition loc_59 : location_info := LocationInfo file_0 242 34 242 35.
  Definition loc_60 : location_info := LocationInfo file_0 242 34 242 35.
  Definition loc_61 : location_info := LocationInfo file_0 242 50 242 78.
  Definition loc_62 : location_info := LocationInfo file_0 242 50 242 78.
  Definition loc_63 : location_info := LocationInfo file_0 242 50 242 72.
  Definition loc_64 : location_info := LocationInfo file_0 242 50 242 66.
  Definition loc_65 : location_info := LocationInfo file_0 242 50 242 64.
  Definition loc_66 : location_info := LocationInfo file_0 242 50 242 64.
  Definition loc_67 : location_info := LocationInfo file_0 242 50 242 61.
  Definition loc_68 : location_info := LocationInfo file_0 242 50 242 61.
  Definition loc_69 : location_info := LocationInfo file_0 242 52 242 60.
  Definition loc_70 : location_info := LocationInfo file_0 242 52 242 60.
  Definition loc_71 : location_info := LocationInfo file_0 242 52 242 53.
  Definition loc_72 : location_info := LocationInfo file_0 242 52 242 53.
  Definition loc_73 : location_info := LocationInfo file_0 242 62 242 63.
  Definition loc_74 : location_info := LocationInfo file_0 242 62 242 63.
  Definition loc_76 : location_info := LocationInfo file_0 241 7 241 40.
  Definition loc_77 : location_info := LocationInfo file_0 241 7 241 25.
  Definition loc_78 : location_info := LocationInfo file_0 241 7 241 25.
  Definition loc_79 : location_info := LocationInfo file_0 241 7 241 21.
  Definition loc_80 : location_info := LocationInfo file_0 241 7 241 21.
  Definition loc_81 : location_info := LocationInfo file_0 241 7 241 18.
  Definition loc_82 : location_info := LocationInfo file_0 241 7 241 18.
  Definition loc_83 : location_info := LocationInfo file_0 241 9 241 17.
  Definition loc_84 : location_info := LocationInfo file_0 241 9 241 17.
  Definition loc_85 : location_info := LocationInfo file_0 241 9 241 10.
  Definition loc_86 : location_info := LocationInfo file_0 241 9 241 10.
  Definition loc_87 : location_info := LocationInfo file_0 241 19 241 20.
  Definition loc_88 : location_info := LocationInfo file_0 241 19 241 20.
  Definition loc_89 : location_info := LocationInfo file_0 241 29 241 40.
  Definition loc_90 : location_info := LocationInfo file_0 241 38 241 39.
  Definition loc_91 : location_info := LocationInfo file_0 240 20 240 33.
  Definition loc_92 : location_info := LocationInfo file_0 240 20 240 21.
  Definition loc_93 : location_info := LocationInfo file_0 240 20 240 21.
  Definition loc_94 : location_info := LocationInfo file_0 240 24 240 33.
  Definition loc_95 : location_info := LocationInfo file_0 240 24 240 33.
  Definition loc_96 : location_info := LocationInfo file_0 240 24 240 25.
  Definition loc_97 : location_info := LocationInfo file_0 240 24 240 25.
  Definition loc_98 : location_info := LocationInfo file_0 240 17 240 18.
  Definition loc_101 : location_info := LocationInfo file_0 232 2 232 10.
  Definition loc_102 : location_info := LocationInfo file_0 232 2 232 10.
  Definition loc_103 : location_info := LocationInfo file_0 232 11 232 14.
  Definition loc_104 : location_info := LocationInfo file_0 232 12 232 14.
  Definition loc_105 : location_info := LocationInfo file_0 232 16 232 23.
  Definition loc_106 : location_info := LocationInfo file_0 232 16 232 23.
  Definition loc_107 : location_info := LocationInfo file_0 230 19 230 32.
  Definition loc_108 : location_info := LocationInfo file_0 230 19 230 28.
  Definition loc_109 : location_info := LocationInfo file_0 230 19 230 28.
  Definition loc_110 : location_info := LocationInfo file_0 230 19 230 20.
  Definition loc_111 : location_info := LocationInfo file_0 230 19 230 20.
  Definition loc_112 : location_info := LocationInfo file_0 230 31 230 32.
  Definition loc_115 : location_info := LocationInfo file_0 227 68 227 70.
  Definition loc_116 : location_info := LocationInfo file_0 227 76 227 89.
  Definition loc_117 : location_info := LocationInfo file_0 227 78 227 87.
  Definition loc_118 : location_info := LocationInfo file_0 227 78 227 87.
  Definition loc_119 : location_info := LocationInfo file_0 227 86 227 87.
  Definition loc_120 : location_info := LocationInfo file_0 227 78 227 87.
  Definition loc_121 : location_info := LocationInfo file_0 227 78 227 87.
  Definition loc_122 : location_info := LocationInfo file_0 227 84 227 85.
  Definition loc_123 : location_info := LocationInfo file_0 227 5 227 66.
  Definition loc_124 : location_info := LocationInfo file_0 227 5 227 14.
  Definition loc_125 : location_info := LocationInfo file_0 227 5 227 14.
  Definition loc_126 : location_info := LocationInfo file_0 227 5 227 6.
  Definition loc_127 : location_info := LocationInfo file_0 227 5 227 6.
  Definition loc_128 : location_info := LocationInfo file_0 227 17 227 66.
  Definition loc_129 : location_info := LocationInfo file_0 227 17 227 61.
  Definition loc_130 : location_info := LocationInfo file_0 227 17 227 39.
  Definition loc_131 : location_info := LocationInfo file_0 227 17 227 35.
  Definition loc_132 : location_info := LocationInfo file_0 227 38 227 39.
  Definition loc_133 : location_info := LocationInfo file_0 227 42 227 61.
  Definition loc_134 : location_info := LocationInfo file_0 227 64 227 66.
  Definition loc_135 : location_info := LocationInfo file_0 223 47 225 3.
  Definition loc_136 : location_info := LocationInfo file_0 224 4 224 11.
  Definition loc_139 : location_info := LocationInfo file_0 223 5 223 45.
  Definition loc_140 : location_info := LocationInfo file_0 223 5 223 33.
  Definition loc_141 : location_info := LocationInfo file_0 223 5 223 22.
  Definition loc_142 : location_info := LocationInfo file_0 223 5 223 22.
  Definition loc_143 : location_info := LocationInfo file_0 223 23 223 32.
  Definition loc_144 : location_info := LocationInfo file_0 223 23 223 32.
  Definition loc_145 : location_info := LocationInfo file_0 223 23 223 24.
  Definition loc_146 : location_info := LocationInfo file_0 223 23 223 24.
  Definition loc_147 : location_info := LocationInfo file_0 223 37 223 45.
  Definition loc_148 : location_info := LocationInfo file_0 223 37 223 45.
  Definition loc_149 : location_info := LocationInfo file_0 223 37 223 38.
  Definition loc_150 : location_info := LocationInfo file_0 223 37 223 38.
  Definition loc_153 : location_info := LocationInfo file_0 77 2 77 56.
  Definition loc_154 : location_info := LocationInfo file_0 78 2 78 18.
  Definition loc_155 : location_info := LocationInfo file_0 79 2 79 21.
  Definition loc_156 : location_info := LocationInfo file_0 80 2 80 17.
  Definition loc_157 : location_info := LocationInfo file_0 88 2 91 3.
  Definition loc_158 : location_info := LocationInfo file_0 88 6 88 11.
  Definition loc_159 : location_info := LocationInfo file_0 88 2 91 3.
  Definition loc_160 : location_info := LocationInfo file_0 88 30 91 3.
  Definition loc_161 : location_info := LocationInfo file_0 89 4 89 37.
  Definition loc_162 : location_info := LocationInfo file_0 90 4 90 37.
  Definition loc_163 : location_info := LocationInfo file_0 88 2 91 3.
  Definition loc_164 : location_info := LocationInfo file_0 88 22 88 28.
  Definition loc_165 : location_info := LocationInfo file_0 88 22 88 23.
  Definition loc_166 : location_info := LocationInfo file_0 88 22 88 28.
  Definition loc_167 : location_info := LocationInfo file_0 88 22 88 23.
  Definition loc_168 : location_info := LocationInfo file_0 88 22 88 23.
  Definition loc_169 : location_info := LocationInfo file_0 88 27 88 28.
  Definition loc_170 : location_info := LocationInfo file_0 90 4 90 32.
  Definition loc_171 : location_info := LocationInfo file_0 90 4 90 26.
  Definition loc_172 : location_info := LocationInfo file_0 90 4 90 20.
  Definition loc_173 : location_info := LocationInfo file_0 90 4 90 18.
  Definition loc_174 : location_info := LocationInfo file_0 90 4 90 18.
  Definition loc_175 : location_info := LocationInfo file_0 90 4 90 15.
  Definition loc_176 : location_info := LocationInfo file_0 90 4 90 15.
  Definition loc_177 : location_info := LocationInfo file_0 90 6 90 14.
  Definition loc_178 : location_info := LocationInfo file_0 90 6 90 14.
  Definition loc_179 : location_info := LocationInfo file_0 90 6 90 7.
  Definition loc_180 : location_info := LocationInfo file_0 90 6 90 7.
  Definition loc_181 : location_info := LocationInfo file_0 90 16 90 17.
  Definition loc_182 : location_info := LocationInfo file_0 90 16 90 17.
  Definition loc_183 : location_info := LocationInfo file_0 90 35 90 36.
  Definition loc_184 : location_info := LocationInfo file_0 89 4 89 22.
  Definition loc_185 : location_info := LocationInfo file_0 89 4 89 18.
  Definition loc_186 : location_info := LocationInfo file_0 89 4 89 18.
  Definition loc_187 : location_info := LocationInfo file_0 89 4 89 15.
  Definition loc_188 : location_info := LocationInfo file_0 89 4 89 15.
  Definition loc_189 : location_info := LocationInfo file_0 89 6 89 14.
  Definition loc_190 : location_info := LocationInfo file_0 89 6 89 14.
  Definition loc_191 : location_info := LocationInfo file_0 89 6 89 7.
  Definition loc_192 : location_info := LocationInfo file_0 89 6 89 7.
  Definition loc_193 : location_info := LocationInfo file_0 89 16 89 17.
  Definition loc_194 : location_info := LocationInfo file_0 89 16 89 17.
  Definition loc_195 : location_info := LocationInfo file_0 89 25 89 36.
  Definition loc_196 : location_info := LocationInfo file_0 89 34 89 35.
  Definition loc_197 : location_info := LocationInfo file_0 88 13 88 20.
  Definition loc_198 : location_info := LocationInfo file_0 88 13 88 14.
  Definition loc_199 : location_info := LocationInfo file_0 88 13 88 14.
  Definition loc_200 : location_info := LocationInfo file_0 88 17 88 20.
  Definition loc_201 : location_info := LocationInfo file_0 88 17 88 20.
  Definition loc_202 : location_info := LocationInfo file_0 88 6 88 7.
  Definition loc_203 : location_info := LocationInfo file_0 88 10 88 11.
  Definition loc_204 : location_info := LocationInfo file_0 80 2 80 10.
  Definition loc_205 : location_info := LocationInfo file_0 80 2 80 3.
  Definition loc_206 : location_info := LocationInfo file_0 80 2 80 3.
  Definition loc_207 : location_info := LocationInfo file_0 80 13 80 16.
  Definition loc_208 : location_info := LocationInfo file_0 80 13 80 16.
  Definition loc_209 : location_info := LocationInfo file_0 79 2 79 10.
  Definition loc_210 : location_info := LocationInfo file_0 79 2 79 3.
  Definition loc_211 : location_info := LocationInfo file_0 79 2 79 3.
  Definition loc_212 : location_info := LocationInfo file_0 79 13 79 20.
  Definition loc_213 : location_info := LocationInfo file_0 79 13 79 20.
  Definition loc_214 : location_info := LocationInfo file_0 78 2 78 11.
  Definition loc_215 : location_info := LocationInfo file_0 78 2 78 3.
  Definition loc_216 : location_info := LocationInfo file_0 78 2 78 3.
  Definition loc_217 : location_info := LocationInfo file_0 78 14 78 17.
  Definition loc_218 : location_info := LocationInfo file_0 78 14 78 17.
  Definition loc_219 : location_info := LocationInfo file_0 77 18 77 55.
  Definition loc_220 : location_info := LocationInfo file_0 77 18 77 29.
  Definition loc_221 : location_info := LocationInfo file_0 77 18 77 29.
  Definition loc_222 : location_info := LocationInfo file_0 77 30 77 49.
  Definition loc_223 : location_info := LocationInfo file_0 77 51 77 54.
  Definition loc_224 : location_info := LocationInfo file_0 77 51 77 54.
  Definition loc_229 : location_info := LocationInfo file_0 102 4 102 21.
  Definition loc_230 : location_info := LocationInfo file_0 102 11 102 20.
  Definition loc_231 : location_info := LocationInfo file_0 102 11 102 14.
  Definition loc_232 : location_info := LocationInfo file_0 102 11 102 14.
  Definition loc_233 : location_info := LocationInfo file_0 102 17 102 20.
  Definition loc_234 : location_info := LocationInfo file_0 102 17 102 20.
  Definition loc_237 : location_info := LocationInfo file_0 115 4 115 55.
  Definition loc_238 : location_info := LocationInfo file_0 121 4 130 5.
  Definition loc_239 : location_info := LocationInfo file_0 121 4 130 5.
  Definition loc_240 : location_info := LocationInfo file_0 121 13 130 5.
  Definition loc_241 : location_info := LocationInfo file_0 122 8 124 9.
  Definition loc_242 : location_info := LocationInfo file_0 125 8 127 9.
  Definition loc_243 : location_info := LocationInfo file_0 128 8 128 22.
  Definition loc_244 : location_info := LocationInfo file_0 128 22 128 9.
  Definition loc_245 : location_info := LocationInfo file_0 129 8 129 46.
  Definition loc_246 : location_info := LocationInfo file_0 121 4 130 5.
  Definition loc_247 : location_info := LocationInfo file_0 121 4 130 5.
  Definition loc_248 : location_info := LocationInfo file_0 129 8 129 16.
  Definition loc_249 : location_info := LocationInfo file_0 129 19 129 45.
  Definition loc_250 : location_info := LocationInfo file_0 129 19 129 33.
  Definition loc_251 : location_info := LocationInfo file_0 129 20 129 28.
  Definition loc_252 : location_info := LocationInfo file_0 129 20 129 28.
  Definition loc_253 : location_info := LocationInfo file_0 129 31 129 32.
  Definition loc_254 : location_info := LocationInfo file_0 129 36 129 45.
  Definition loc_255 : location_info := LocationInfo file_0 129 36 129 45.
  Definition loc_256 : location_info := LocationInfo file_0 129 36 129 37.
  Definition loc_257 : location_info := LocationInfo file_0 129 36 129 37.
  Definition loc_258 : location_info := LocationInfo file_0 128 8 128 21.
  Definition loc_259 : location_info := LocationInfo file_0 128 8 128 17.
  Definition loc_260 : location_info := LocationInfo file_0 128 8 128 17.
  Definition loc_261 : location_info := LocationInfo file_0 128 8 128 9.
  Definition loc_262 : location_info := LocationInfo file_0 128 8 128 9.
  Definition loc_263 : location_info := LocationInfo file_0 128 20 128 21.
  Definition loc_264 : location_info := LocationInfo file_0 125 97 127 9.
  Definition loc_265 : location_info := LocationInfo file_0 126 12 126 28.
  Definition loc_266 : location_info := LocationInfo file_0 126 19 126 27.
  Definition loc_267 : location_info := LocationInfo file_0 126 19 126 27.
  Definition loc_270 : location_info := LocationInfo file_0 125 11 125 51.
  Definition loc_271 : location_info := LocationInfo file_0 125 11 125 36.
  Definition loc_272 : location_info := LocationInfo file_0 125 11 125 36.
  Definition loc_273 : location_info := LocationInfo file_0 125 11 125 32.
  Definition loc_274 : location_info := LocationInfo file_0 125 11 125 32.
  Definition loc_275 : location_info := LocationInfo file_0 125 11 125 22.
  Definition loc_276 : location_info := LocationInfo file_0 125 11 125 22.
  Definition loc_277 : location_info := LocationInfo file_0 125 13 125 21.
  Definition loc_278 : location_info := LocationInfo file_0 125 13 125 21.
  Definition loc_279 : location_info := LocationInfo file_0 125 13 125 14.
  Definition loc_280 : location_info := LocationInfo file_0 125 13 125 14.
  Definition loc_281 : location_info := LocationInfo file_0 125 23 125 31.
  Definition loc_282 : location_info := LocationInfo file_0 125 23 125 31.
  Definition loc_283 : location_info := LocationInfo file_0 125 40 125 51.
  Definition loc_284 : location_info := LocationInfo file_0 125 49 125 50.
  Definition loc_285 : location_info := LocationInfo file_0 125 55 125 95.
  Definition loc_286 : location_info := LocationInfo file_0 125 55 125 88.
  Definition loc_287 : location_info := LocationInfo file_0 125 55 125 88.
  Definition loc_288 : location_info := LocationInfo file_0 125 55 125 84.
  Definition loc_289 : location_info := LocationInfo file_0 125 55 125 78.
  Definition loc_290 : location_info := LocationInfo file_0 125 55 125 76.
  Definition loc_291 : location_info := LocationInfo file_0 125 55 125 76.
  Definition loc_292 : location_info := LocationInfo file_0 125 55 125 66.
  Definition loc_293 : location_info := LocationInfo file_0 125 55 125 66.
  Definition loc_294 : location_info := LocationInfo file_0 125 57 125 65.
  Definition loc_295 : location_info := LocationInfo file_0 125 57 125 65.
  Definition loc_296 : location_info := LocationInfo file_0 125 57 125 58.
  Definition loc_297 : location_info := LocationInfo file_0 125 57 125 58.
  Definition loc_298 : location_info := LocationInfo file_0 125 67 125 75.
  Definition loc_299 : location_info := LocationInfo file_0 125 67 125 75.
  Definition loc_300 : location_info := LocationInfo file_0 125 92 125 95.
  Definition loc_301 : location_info := LocationInfo file_0 125 92 125 95.
  Definition loc_302 : location_info := LocationInfo file_0 122 147 124 9.
  Definition loc_303 : location_info := LocationInfo file_0 123 12 123 28.
  Definition loc_304 : location_info := LocationInfo file_0 123 19 123 27.
  Definition loc_305 : location_info := LocationInfo file_0 123 19 123 27.
  Definition loc_308 : location_info := LocationInfo file_0 122 11 122 51.
  Definition loc_309 : location_info := LocationInfo file_0 122 11 122 36.
  Definition loc_310 : location_info := LocationInfo file_0 122 11 122 36.
  Definition loc_311 : location_info := LocationInfo file_0 122 11 122 32.
  Definition loc_312 : location_info := LocationInfo file_0 122 11 122 32.
  Definition loc_313 : location_info := LocationInfo file_0 122 11 122 22.
  Definition loc_314 : location_info := LocationInfo file_0 122 11 122 22.
  Definition loc_315 : location_info := LocationInfo file_0 122 13 122 21.
  Definition loc_316 : location_info := LocationInfo file_0 122 13 122 21.
  Definition loc_317 : location_info := LocationInfo file_0 122 13 122 14.
  Definition loc_318 : location_info := LocationInfo file_0 122 13 122 14.
  Definition loc_319 : location_info := LocationInfo file_0 122 23 122 31.
  Definition loc_320 : location_info := LocationInfo file_0 122 23 122 31.
  Definition loc_321 : location_info := LocationInfo file_0 122 40 122 51.
  Definition loc_322 : location_info := LocationInfo file_0 122 49 122 50.
  Definition loc_324 : location_info := LocationInfo file_0 122 56 122 96.
  Definition loc_325 : location_info := LocationInfo file_0 122 56 122 81.
  Definition loc_326 : location_info := LocationInfo file_0 122 56 122 81.
  Definition loc_327 : location_info := LocationInfo file_0 122 56 122 77.
  Definition loc_328 : location_info := LocationInfo file_0 122 56 122 77.
  Definition loc_329 : location_info := LocationInfo file_0 122 56 122 67.
  Definition loc_330 : location_info := LocationInfo file_0 122 56 122 67.
  Definition loc_331 : location_info := LocationInfo file_0 122 58 122 66.
  Definition loc_332 : location_info := LocationInfo file_0 122 58 122 66.
  Definition loc_333 : location_info := LocationInfo file_0 122 58 122 59.
  Definition loc_334 : location_info := LocationInfo file_0 122 58 122 59.
  Definition loc_335 : location_info := LocationInfo file_0 122 68 122 76.
  Definition loc_336 : location_info := LocationInfo file_0 122 68 122 76.
  Definition loc_337 : location_info := LocationInfo file_0 122 85 122 96.
  Definition loc_338 : location_info := LocationInfo file_0 122 94 122 95.
  Definition loc_339 : location_info := LocationInfo file_0 122 100 122 144.
  Definition loc_340 : location_info := LocationInfo file_0 122 100 122 137.
  Definition loc_341 : location_info := LocationInfo file_0 122 100 122 137.
  Definition loc_342 : location_info := LocationInfo file_0 122 100 122 133.
  Definition loc_343 : location_info := LocationInfo file_0 122 100 122 123.
  Definition loc_344 : location_info := LocationInfo file_0 122 100 122 121.
  Definition loc_345 : location_info := LocationInfo file_0 122 100 122 121.
  Definition loc_346 : location_info := LocationInfo file_0 122 100 122 111.
  Definition loc_347 : location_info := LocationInfo file_0 122 100 122 111.
  Definition loc_348 : location_info := LocationInfo file_0 122 102 122 110.
  Definition loc_349 : location_info := LocationInfo file_0 122 102 122 110.
  Definition loc_350 : location_info := LocationInfo file_0 122 102 122 103.
  Definition loc_351 : location_info := LocationInfo file_0 122 102 122 103.
  Definition loc_352 : location_info := LocationInfo file_0 122 112 122 120.
  Definition loc_353 : location_info := LocationInfo file_0 122 112 122 120.
  Definition loc_354 : location_info := LocationInfo file_0 122 141 122 144.
  Definition loc_355 : location_info := LocationInfo file_0 122 141 122 144.
  Definition loc_356 : location_info := LocationInfo file_0 121 10 121 11.
  Definition loc_357 : location_info := LocationInfo file_0 115 22 115 54.
  Definition loc_358 : location_info := LocationInfo file_0 115 22 115 38.
  Definition loc_359 : location_info := LocationInfo file_0 115 22 115 38.
  Definition loc_360 : location_info := LocationInfo file_0 115 39 115 48.
  Definition loc_361 : location_info := LocationInfo file_0 115 39 115 48.
  Definition loc_362 : location_info := LocationInfo file_0 115 39 115 40.
  Definition loc_363 : location_info := LocationInfo file_0 115 39 115 40.
  Definition loc_364 : location_info := LocationInfo file_0 115 50 115 53.
  Definition loc_365 : location_info := LocationInfo file_0 115 50 115 53.
  Definition loc_370 : location_info := LocationInfo file_0 143 4 143 32.
  Definition loc_371 : location_info := LocationInfo file_0 144 4 144 40.
  Definition loc_372 : location_info := LocationInfo file_0 145 4 145 36.
  Definition loc_373 : location_info := LocationInfo file_0 146 4 146 47.
  Definition loc_374 : location_info := LocationInfo file_0 147 4 151 5.
  Definition loc_375 : location_info := LocationInfo file_0 153 4 153 28.
  Definition loc_376 : location_info := LocationInfo file_0 154 4 154 28.
  Definition loc_377 : location_info := LocationInfo file_0 155 4 155 32.
  Definition loc_378 : location_info := LocationInfo file_0 157 4 157 20.
  Definition loc_379 : location_info := LocationInfo file_0 157 11 157 19.
  Definition loc_380 : location_info := LocationInfo file_0 157 11 157 19.
  Definition loc_381 : location_info := LocationInfo file_0 155 4 155 23.
  Definition loc_382 : location_info := LocationInfo file_0 155 4 155 17.
  Definition loc_383 : location_info := LocationInfo file_0 155 4 155 11.
  Definition loc_384 : location_info := LocationInfo file_0 155 4 155 8.
  Definition loc_385 : location_info := LocationInfo file_0 155 4 155 8.
  Definition loc_386 : location_info := LocationInfo file_0 155 26 155 31.
  Definition loc_387 : location_info := LocationInfo file_0 155 26 155 31.
  Definition loc_388 : location_info := LocationInfo file_0 154 4 154 21.
  Definition loc_389 : location_info := LocationInfo file_0 154 4 154 17.
  Definition loc_390 : location_info := LocationInfo file_0 154 4 154 11.
  Definition loc_391 : location_info := LocationInfo file_0 154 4 154 8.
  Definition loc_392 : location_info := LocationInfo file_0 154 4 154 8.
  Definition loc_393 : location_info := LocationInfo file_0 154 24 154 27.
  Definition loc_394 : location_info := LocationInfo file_0 154 24 154 27.
  Definition loc_395 : location_info := LocationInfo file_0 153 4 153 13.
  Definition loc_396 : location_info := LocationInfo file_0 153 4 153 8.
  Definition loc_397 : location_info := LocationInfo file_0 153 4 153 8.
  Definition loc_398 : location_info := LocationInfo file_0 153 16 153 27.
  Definition loc_399 : location_info := LocationInfo file_0 153 25 153 26.
  Definition loc_400 : location_info := LocationInfo file_0 147 34 149 5.
  Definition loc_401 : location_info := LocationInfo file_0 148 8 148 39.
  Definition loc_402 : location_info := LocationInfo file_0 148 8 148 16.
  Definition loc_403 : location_info := LocationInfo file_0 148 19 148 38.
  Definition loc_404 : location_info := LocationInfo file_0 148 19 148 38.
  Definition loc_405 : location_info := LocationInfo file_0 148 19 148 32.
  Definition loc_406 : location_info := LocationInfo file_0 148 19 148 26.
  Definition loc_407 : location_info := LocationInfo file_0 148 19 148 23.
  Definition loc_408 : location_info := LocationInfo file_0 148 19 148 23.
  Definition loc_409 : location_info := LocationInfo file_0 149 11 151 5.
  Definition loc_410 : location_info := LocationInfo file_0 149 40 151 5.
  Definition loc_411 : location_info := LocationInfo file_0 150 6 150 20.
  Definition loc_412 : location_info := LocationInfo file_0 150 6 150 14.
  Definition loc_413 : location_info := LocationInfo file_0 150 6 150 7.
  Definition loc_414 : location_info := LocationInfo file_0 150 6 150 7.
  Definition loc_415 : location_info := LocationInfo file_0 150 6 150 19.
  Definition loc_416 : location_info := LocationInfo file_0 150 6 150 14.
  Definition loc_417 : location_info := LocationInfo file_0 150 6 150 14.
  Definition loc_418 : location_info := LocationInfo file_0 150 6 150 7.
  Definition loc_419 : location_info := LocationInfo file_0 150 6 150 7.
  Definition loc_420 : location_info := LocationInfo file_0 150 18 150 19.
  Definition loc_422 : location_info := LocationInfo file_0 149 14 149 38.
  Definition loc_423 : location_info := LocationInfo file_0 149 14 149 23.
  Definition loc_424 : location_info := LocationInfo file_0 149 14 149 23.
  Definition loc_425 : location_info := LocationInfo file_0 149 14 149 18.
  Definition loc_426 : location_info := LocationInfo file_0 149 14 149 18.
  Definition loc_427 : location_info := LocationInfo file_0 149 27 149 38.
  Definition loc_428 : location_info := LocationInfo file_0 149 36 149 37.
  Definition loc_429 : location_info := LocationInfo file_0 147 8 147 32.
  Definition loc_430 : location_info := LocationInfo file_0 147 8 147 17.
  Definition loc_431 : location_info := LocationInfo file_0 147 8 147 17.
  Definition loc_432 : location_info := LocationInfo file_0 147 8 147 12.
  Definition loc_433 : location_info := LocationInfo file_0 147 8 147 12.
  Definition loc_434 : location_info := LocationInfo file_0 147 21 147 32.
  Definition loc_435 : location_info := LocationInfo file_0 147 30 147 31.
  Definition loc_436 : location_info := LocationInfo file_0 146 24 146 46.
  Definition loc_437 : location_info := LocationInfo file_0 146 25 146 46.
  Definition loc_438 : location_info := LocationInfo file_0 146 25 146 46.
  Definition loc_439 : location_info := LocationInfo file_0 146 25 146 36.
  Definition loc_440 : location_info := LocationInfo file_0 146 25 146 36.
  Definition loc_441 : location_info := LocationInfo file_0 146 27 146 35.
  Definition loc_442 : location_info := LocationInfo file_0 146 27 146 35.
  Definition loc_443 : location_info := LocationInfo file_0 146 27 146 28.
  Definition loc_444 : location_info := LocationInfo file_0 146 27 146 28.
  Definition loc_445 : location_info := LocationInfo file_0 146 37 146 45.
  Definition loc_446 : location_info := LocationInfo file_0 146 37 146 45.
  Definition loc_449 : location_info := LocationInfo file_0 145 21 145 35.
  Definition loc_452 : location_info := LocationInfo file_0 144 22 144 39.
  Definition loc_453 : location_info := LocationInfo file_0 144 22 144 31.
  Definition loc_454 : location_info := LocationInfo file_0 144 22 144 31.
  Definition loc_455 : location_info := LocationInfo file_0 144 32 144 33.
  Definition loc_456 : location_info := LocationInfo file_0 144 32 144 33.
  Definition loc_457 : location_info := LocationInfo file_0 144 35 144 38.
  Definition loc_458 : location_info := LocationInfo file_0 144 35 144 38.
  Definition loc_461 : location_info := LocationInfo file_0 143 4 143 28.
  Definition loc_462 : location_info := LocationInfo file_0 143 4 143 28.
  Definition loc_463 : location_info := LocationInfo file_0 143 29 143 30.
  Definition loc_464 : location_info := LocationInfo file_0 143 29 143 30.
  Definition loc_467 : location_info := LocationInfo file_0 168 4 168 40.
  Definition loc_468 : location_info := LocationInfo file_0 169 4 169 47.
  Definition loc_469 : location_info := LocationInfo file_0 171 4 175 5.
  Definition loc_470 : location_info := LocationInfo file_0 171 34 173 5.
  Definition loc_471 : location_info := LocationInfo file_0 172 8 172 37.
  Definition loc_472 : location_info := LocationInfo file_0 172 15 172 36.
  Definition loc_473 : location_info := LocationInfo file_0 172 16 172 36.
  Definition loc_474 : location_info := LocationInfo file_0 172 17 172 36.
  Definition loc_475 : location_info := LocationInfo file_0 172 17 172 36.
  Definition loc_476 : location_info := LocationInfo file_0 172 17 172 30.
  Definition loc_477 : location_info := LocationInfo file_0 172 17 172 24.
  Definition loc_478 : location_info := LocationInfo file_0 172 17 172 21.
  Definition loc_479 : location_info := LocationInfo file_0 172 17 172 21.
  Definition loc_480 : location_info := LocationInfo file_0 173 11 175 5.
  Definition loc_481 : location_info := LocationInfo file_0 174 8 174 30.
  Definition loc_482 : location_info := LocationInfo file_0 174 15 174 29.
  Definition loc_483 : location_info := LocationInfo file_0 171 8 171 32.
  Definition loc_484 : location_info := LocationInfo file_0 171 8 171 17.
  Definition loc_485 : location_info := LocationInfo file_0 171 8 171 17.
  Definition loc_486 : location_info := LocationInfo file_0 171 8 171 12.
  Definition loc_487 : location_info := LocationInfo file_0 171 8 171 12.
  Definition loc_488 : location_info := LocationInfo file_0 171 21 171 32.
  Definition loc_489 : location_info := LocationInfo file_0 171 30 171 31.
  Definition loc_490 : location_info := LocationInfo file_0 169 24 169 46.
  Definition loc_491 : location_info := LocationInfo file_0 169 25 169 46.
  Definition loc_492 : location_info := LocationInfo file_0 169 25 169 46.
  Definition loc_493 : location_info := LocationInfo file_0 169 25 169 36.
  Definition loc_494 : location_info := LocationInfo file_0 169 25 169 36.
  Definition loc_495 : location_info := LocationInfo file_0 169 27 169 35.
  Definition loc_496 : location_info := LocationInfo file_0 169 27 169 35.
  Definition loc_497 : location_info := LocationInfo file_0 169 27 169 28.
  Definition loc_498 : location_info := LocationInfo file_0 169 27 169 28.
  Definition loc_499 : location_info := LocationInfo file_0 169 37 169 45.
  Definition loc_500 : location_info := LocationInfo file_0 169 37 169 45.
  Definition loc_503 : location_info := LocationInfo file_0 168 22 168 39.
  Definition loc_504 : location_info := LocationInfo file_0 168 22 168 31.
  Definition loc_505 : location_info := LocationInfo file_0 168 22 168 31.
  Definition loc_506 : location_info := LocationInfo file_0 168 32 168 33.
  Definition loc_507 : location_info := LocationInfo file_0 168 32 168 33.
  Definition loc_508 : location_info := LocationInfo file_0 168 35 168 38.
  Definition loc_509 : location_info := LocationInfo file_0 168 35 168 38.
  Definition loc_514 : location_info := LocationInfo file_0 187 4 187 40.
  Definition loc_515 : location_info := LocationInfo file_0 188 4 188 47.
  Definition loc_516 : location_info := LocationInfo file_0 190 4 197 5.
  Definition loc_517 : location_info := LocationInfo file_0 190 34 195 5.
  Definition loc_518 : location_info := LocationInfo file_0 191 8 191 38.
  Definition loc_519 : location_info := LocationInfo file_0 192 8 192 32.
  Definition loc_520 : location_info := LocationInfo file_0 193 8 193 36.
  Definition loc_521 : location_info := LocationInfo file_0 194 8 194 23.
  Definition loc_522 : location_info := LocationInfo file_0 194 15 194 22.
  Definition loc_523 : location_info := LocationInfo file_0 194 15 194 22.
  Definition loc_524 : location_info := LocationInfo file_0 193 8 193 29.
  Definition loc_525 : location_info := LocationInfo file_0 193 8 193 25.
  Definition loc_526 : location_info := LocationInfo file_0 193 8 193 15.
  Definition loc_527 : location_info := LocationInfo file_0 193 8 193 12.
  Definition loc_528 : location_info := LocationInfo file_0 193 8 193 12.
  Definition loc_529 : location_info := LocationInfo file_0 193 32 193 35.
  Definition loc_530 : location_info := LocationInfo file_0 193 32 193 35.
  Definition loc_531 : location_info := LocationInfo file_0 192 8 192 17.
  Definition loc_532 : location_info := LocationInfo file_0 192 8 192 12.
  Definition loc_533 : location_info := LocationInfo file_0 192 8 192 12.
  Definition loc_534 : location_info := LocationInfo file_0 192 20 192 31.
  Definition loc_535 : location_info := LocationInfo file_0 192 29 192 30.
  Definition loc_536 : location_info := LocationInfo file_0 191 8 191 15.
  Definition loc_537 : location_info := LocationInfo file_0 191 18 191 37.
  Definition loc_538 : location_info := LocationInfo file_0 191 18 191 37.
  Definition loc_539 : location_info := LocationInfo file_0 191 18 191 31.
  Definition loc_540 : location_info := LocationInfo file_0 191 18 191 25.
  Definition loc_541 : location_info := LocationInfo file_0 191 18 191 22.
  Definition loc_542 : location_info := LocationInfo file_0 191 18 191 22.
  Definition loc_543 : location_info := LocationInfo file_0 195 11 197 5.
  Definition loc_544 : location_info := LocationInfo file_0 196 8 196 30.
  Definition loc_545 : location_info := LocationInfo file_0 196 15 196 29.
  Definition loc_546 : location_info := LocationInfo file_0 190 8 190 32.
  Definition loc_547 : location_info := LocationInfo file_0 190 8 190 17.
  Definition loc_548 : location_info := LocationInfo file_0 190 8 190 17.
  Definition loc_549 : location_info := LocationInfo file_0 190 8 190 12.
  Definition loc_550 : location_info := LocationInfo file_0 190 8 190 12.
  Definition loc_551 : location_info := LocationInfo file_0 190 21 190 32.
  Definition loc_552 : location_info := LocationInfo file_0 190 30 190 31.
  Definition loc_553 : location_info := LocationInfo file_0 188 24 188 46.
  Definition loc_554 : location_info := LocationInfo file_0 188 25 188 46.
  Definition loc_555 : location_info := LocationInfo file_0 188 25 188 46.
  Definition loc_556 : location_info := LocationInfo file_0 188 25 188 36.
  Definition loc_557 : location_info := LocationInfo file_0 188 25 188 36.
  Definition loc_558 : location_info := LocationInfo file_0 188 27 188 35.
  Definition loc_559 : location_info := LocationInfo file_0 188 27 188 35.
  Definition loc_560 : location_info := LocationInfo file_0 188 27 188 28.
  Definition loc_561 : location_info := LocationInfo file_0 188 27 188 28.
  Definition loc_562 : location_info := LocationInfo file_0 188 37 188 45.
  Definition loc_563 : location_info := LocationInfo file_0 188 37 188 45.
  Definition loc_566 : location_info := LocationInfo file_0 187 22 187 39.
  Definition loc_567 : location_info := LocationInfo file_0 187 22 187 31.
  Definition loc_568 : location_info := LocationInfo file_0 187 22 187 31.
  Definition loc_569 : location_info := LocationInfo file_0 187 32 187 33.
  Definition loc_570 : location_info := LocationInfo file_0 187 32 187 33.
  Definition loc_571 : location_info := LocationInfo file_0 187 35 187 38.
  Definition loc_572 : location_info := LocationInfo file_0 187 35 187 38.
  Definition loc_577 : location_info := LocationInfo file_0 207 2 207 11.
  Definition loc_578 : location_info := LocationInfo file_0 207 9 207 10.

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
      (Some "value", LPtr)
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
      (Some "items", LPtr);
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

  (* Definition of function [fsm_realloc_if_necessary]. *)
  Definition impl_fsm_realloc_if_necessary (compute_min_count free_array fsm_init fsm_insert : loc): function := {|
    f_args := [
      ("m", LPtr)
    ];
    f_local_vars := [
      ("i", it_layout size_t);
      ("m2", layout_of struct_fixed_size_map);
      ("new_len", it_layout size_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_140 ;
        "$0" <- LocInfoE loc_142 (compute_min_count) with
          [ LocInfoE loc_143 (use{it_layout size_t} (LocInfoE loc_144 ((LocInfoE loc_145 (!{LPtr} (LocInfoE loc_146 ("m")))) at{struct_fixed_size_map} "length"))) ] ;
        locinfo: loc_139 ;
        if: LocInfoE loc_139 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_139 ((LocInfoE loc_140 ("$0")) ≤{IntOp size_t, IntOp size_t} (LocInfoE loc_147 (use{it_layout size_t} (LocInfoE loc_148 ((LocInfoE loc_149 (!{LPtr} (LocInfoE loc_150 ("m")))) at{struct_fixed_size_map} "count")))))))
        then
        locinfo: loc_136 ;
          Goto "#14"
        else
        locinfo: loc_123 ;
          Goto "#15"
      ]> $
      <[ "#1" :=
        locinfo: loc_123 ;
        if: LocInfoE loc_123 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_123 ((LocInfoE loc_124 (use{it_layout size_t} (LocInfoE loc_125 ((LocInfoE loc_126 (!{LPtr} (LocInfoE loc_127 ("m")))) at{struct_fixed_size_map} "length")))) <{IntOp size_t, IntOp size_t} (LocInfoE loc_128 ((LocInfoE loc_129 ((LocInfoE loc_130 ((LocInfoE loc_131 (i2v (it_max size_t - 1) size_t)) /{IntOp size_t, IntOp size_t} (LocInfoE loc_132 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_132 (i2v 2 i32)))))) /{IntOp size_t, IntOp size_t} (LocInfoE loc_133 (i2v (layout_of struct_item).(ly_size) size_t)))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_134 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_134 (i2v 16 i32)))))))))
        then
        Goto "#9"
        else
        locinfo: loc_117 ;
          Goto "#10"
      ]> $
      <[ "#10" :=
        locinfo: loc_117 ;
        Goto "#11"
      ]> $
      <[ "#11" :=
        locinfo: loc_122 ;
        if: LocInfoE loc_122 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_122 (i2v 1 i32)))
        then
        locinfo: loc_120 ;
          Goto "#12"
        else
        Goto "#13"
      ]> $
      <[ "#12" :=
        locinfo: loc_120 ;
        Goto "continue31"
      ]> $
      <[ "#13" :=
        Goto "#2"
      ]> $
      <[ "#14" :=
        locinfo: loc_136 ;
        Return (VOID)
      ]> $
      <[ "#15" :=
        locinfo: loc_123 ;
        Goto "#1"
      ]> $
      <[ "#2" :=
        "new_len" <-{ it_layout size_t }
          LocInfoE loc_107 ((LocInfoE loc_108 (use{it_layout size_t} (LocInfoE loc_109 ((LocInfoE loc_110 (!{LPtr} (LocInfoE loc_111 ("m")))) at{struct_fixed_size_map} "length")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_112 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_112 (i2v 2 i32))))) ;
        locinfo: loc_5 ;
        "_" <- LocInfoE loc_102 (fsm_init) with
          [ LocInfoE loc_103 (&(LocInfoE loc_104 ("m2"))) ;
          LocInfoE loc_105 (use{it_layout size_t} (LocInfoE loc_106 ("new_len"))) ] ;
        "i" <-{ it_layout size_t }
          LocInfoE loc_98 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_98 (i2v 0 i32))) ;
        locinfo: loc_8 ;
        Goto "#3"
      ]> $
      <[ "#3" :=
        locinfo: loc_91 ;
        if: LocInfoE loc_91 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_91 ((LocInfoE loc_92 (use{it_layout size_t} (LocInfoE loc_93 ("i")))) <{IntOp size_t, IntOp size_t} (LocInfoE loc_94 (use{it_layout size_t} (LocInfoE loc_95 ((LocInfoE loc_96 (!{LPtr} (LocInfoE loc_97 ("m")))) at{struct_fixed_size_map} "length")))))))
        then
        locinfo: loc_76 ;
          Goto "#4"
        else
        locinfo: loc_9 ;
          Goto "#5"
      ]> $
      <[ "#4" :=
        locinfo: loc_76 ;
        if: LocInfoE loc_76 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_76 ((LocInfoE loc_77 (use{it_layout size_t} (LocInfoE loc_78 ((LocInfoE loc_80 ((LocInfoE loc_83 (!{LPtr} (LocInfoE loc_84 ((LocInfoE loc_85 (!{LPtr} (LocInfoE loc_86 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_87 (use{it_layout size_t} (LocInfoE loc_88 ("i")))))) at{struct_item} "tag")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_89 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_90 (i2v 1 i32)))))))
        then
        locinfo: loc_42 ;
          Goto "#7"
        else
        locinfo: loc_29 ;
          Goto "#8"
      ]> $
      <[ "#5" :=
        locinfo: loc_9 ;
        "_" <- LocInfoE loc_17 (free_array) with
          [ LocInfoE loc_18 (i2v (layout_of struct_item).(ly_size) size_t) ;
          LocInfoE loc_19 (use{it_layout size_t} (LocInfoE loc_20 ((LocInfoE loc_21 (!{LPtr} (LocInfoE loc_22 ("m")))) at{struct_fixed_size_map} "length"))) ;
          LocInfoE loc_23 (use{LPtr} (LocInfoE loc_24 ((LocInfoE loc_25 (!{LPtr} (LocInfoE loc_26 ("m")))) at{struct_fixed_size_map} "items"))) ] ;
        locinfo: loc_10 ;
        LocInfoE loc_12 (!{LPtr} (LocInfoE loc_13 ("m"))) <-{ layout_of struct_fixed_size_map }
          LocInfoE loc_14 (use{layout_of struct_fixed_size_map} (LocInfoE loc_15 ("m2"))) ;
        Return (VOID)
      ]> $
      <[ "#6" :=
        locinfo: loc_29 ;
        expr: (LocInfoE loc_38 (&(LocInfoE loc_39 ((LocInfoE loc_40 ("m2")) at{struct_fixed_size_map} "length")))) ;
        locinfo: loc_31 ;
        Goto "continue32"
      ]> $
      <[ "#7" :=
        locinfo: loc_42 ;
        "_" <- LocInfoE loc_44 (fsm_insert) with
          [ LocInfoE loc_45 (&(LocInfoE loc_46 ("m2"))) ;
          LocInfoE loc_47 (use{it_layout size_t} (LocInfoE loc_48 ((LocInfoE loc_49 ((LocInfoE loc_50 ((LocInfoE loc_52 ((LocInfoE loc_55 (!{LPtr} (LocInfoE loc_56 ((LocInfoE loc_57 (!{LPtr} (LocInfoE loc_58 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_59 (use{it_layout size_t} (LocInfoE loc_60 ("i")))))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "key"))) ;
          LocInfoE loc_61 (use{LPtr} (LocInfoE loc_62 ((LocInfoE loc_63 ((LocInfoE loc_64 ((LocInfoE loc_66 ((LocInfoE loc_69 (!{LPtr} (LocInfoE loc_70 ((LocInfoE loc_71 (!{LPtr} (LocInfoE loc_72 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_73 (use{it_layout size_t} (LocInfoE loc_74 ("i")))))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "value"))) ] ;
        locinfo: loc_29 ;
        Goto "#6"
      ]> $
      <[ "#8" :=
        locinfo: loc_29 ;
        Goto "#6"
      ]> $
      <[ "#9" :=
        Goto "#2"
      ]> $
      <[ "continue31" :=
        locinfo: loc_117 ;
        Goto "#11"
      ]> $
      <[ "continue32" :=
        LocInfoE loc_33 ("i") <-{ it_layout size_t }
          LocInfoE loc_34 ((LocInfoE loc_35 (use{it_layout size_t} (LocInfoE loc_36 ("i")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_37 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_37 (i2v 1 i32))))) ;
        locinfo: loc_8 ;
        Goto "#3"
      ]> $∅
    )%E
  |}.

  (* Definition of function [fsm_init]. *)
  Definition impl_fsm_init (alloc_array : loc): function := {|
    f_args := [
      ("m", LPtr);
      ("len", it_layout size_t)
    ];
    f_local_vars := [
      ("i", it_layout size_t);
      ("storage", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_219 ;
        "$0" <- LocInfoE loc_221 (alloc_array) with
          [ LocInfoE loc_222 (i2v (layout_of struct_item).(ly_size) size_t) ;
          LocInfoE loc_223 (use{it_layout size_t} (LocInfoE loc_224 ("len"))) ] ;
        "storage" <-{ LPtr } LocInfoE loc_219 ("$0") ;
        locinfo: loc_154 ;
        LocInfoE loc_214 ((LocInfoE loc_215 (!{LPtr} (LocInfoE loc_216 ("m")))) at{struct_fixed_size_map} "length") <-{ it_layout size_t }
          LocInfoE loc_217 (use{it_layout size_t} (LocInfoE loc_218 ("len"))) ;
        locinfo: loc_155 ;
        LocInfoE loc_209 ((LocInfoE loc_210 (!{LPtr} (LocInfoE loc_211 ("m")))) at{struct_fixed_size_map} "items") <-{ LPtr }
          LocInfoE loc_212 (use{LPtr} (LocInfoE loc_213 ("storage"))) ;
        locinfo: loc_156 ;
        LocInfoE loc_204 ((LocInfoE loc_205 (!{LPtr} (LocInfoE loc_206 ("m")))) at{struct_fixed_size_map} "count") <-{ it_layout size_t }
          LocInfoE loc_207 (use{it_layout size_t} (LocInfoE loc_208 ("len"))) ;
        locinfo: loc_158 ;
        LocInfoE loc_202 ("i") <-{ it_layout size_t }
          LocInfoE loc_203 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_203 (i2v 0 i32))) ;
        locinfo: loc_159 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_197 ;
        if: LocInfoE loc_197 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_197 ((LocInfoE loc_198 (use{it_layout size_t} (LocInfoE loc_199 ("i")))) <{IntOp size_t, IntOp size_t} (LocInfoE loc_200 (use{it_layout size_t} (LocInfoE loc_201 ("len")))))))
        then
        locinfo: loc_161 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_161 ;
        LocInfoE loc_184 ((LocInfoE loc_186 ((LocInfoE loc_189 (!{LPtr} (LocInfoE loc_190 ((LocInfoE loc_191 (!{LPtr} (LocInfoE loc_192 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_193 (use{it_layout size_t} (LocInfoE loc_194 ("i")))))) at{struct_item} "tag") <-{ it_layout size_t }
          LocInfoE loc_195 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_196 (i2v 0 i32))) ;
        locinfo: loc_162 ;
        LocInfoE loc_170 ((LocInfoE loc_171 ((LocInfoE loc_172 ((LocInfoE loc_174 ((LocInfoE loc_177 (!{LPtr} (LocInfoE loc_178 ((LocInfoE loc_179 (!{LPtr} (LocInfoE loc_180 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_181 (use{it_layout size_t} (LocInfoE loc_182 ("i")))))) at{struct_item} "u")) at_union{union_item_union} "empty")) at{struct_empty} "dummy") <-{ it_layout size_t }
          LocInfoE loc_183 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_183 (i2v 0 i32))) ;
        locinfo: loc_163 ;
        Goto "continue2"
      ]> $
      <[ "#3" :=
        Return (VOID)
      ]> $
      <[ "continue2" :=
        locinfo: loc_164 ;
        LocInfoE loc_165 ("i") <-{ it_layout size_t }
          LocInfoE loc_166 ((LocInfoE loc_167 (use{it_layout size_t} (LocInfoE loc_168 ("i")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_169 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_169 (i2v 1 i32))))) ;
        locinfo: loc_159 ;
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
        locinfo: loc_229 ;
        Return (LocInfoE loc_230 ((LocInfoE loc_231 (use{it_layout size_t} (LocInfoE loc_232 ("key")))) %{IntOp size_t, IntOp size_t} (LocInfoE loc_233 (use{it_layout size_t} (LocInfoE loc_234 ("len"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [fsm_probe]. *)
  Definition impl_fsm_probe (fsm_slot_for_key : loc): function := {|
    f_args := [
      ("m", LPtr);
      ("key", it_layout size_t)
    ];
    f_local_vars := [
      ("slot_idx", it_layout size_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_357 ;
        "$0" <- LocInfoE loc_359 (fsm_slot_for_key) with
          [ LocInfoE loc_360 (use{it_layout size_t} (LocInfoE loc_361 ((LocInfoE loc_362 (!{LPtr} (LocInfoE loc_363 ("m")))) at{struct_fixed_size_map} "length"))) ;
          LocInfoE loc_364 (use{it_layout size_t} (LocInfoE loc_365 ("key"))) ] ;
        "slot_idx" <-{ it_layout size_t } LocInfoE loc_357 ("$0") ;
        locinfo: loc_238 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_356 ;
        if: LocInfoE loc_356 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_356 (i2v 1 i32)))
        then
        locinfo: loc_308 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#10" :=
        locinfo: loc_270 ;
        Goto "#4"
      ]> $
      <[ "#11" :=
        locinfo: loc_324 ;
        if: LocInfoE loc_324 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_324 ((LocInfoE loc_325 (use{it_layout size_t} (LocInfoE loc_326 ((LocInfoE loc_328 ((LocInfoE loc_331 (!{LPtr} (LocInfoE loc_332 ((LocInfoE loc_333 (!{LPtr} (LocInfoE loc_334 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_335 (use{it_layout size_t} (LocInfoE loc_336 ("slot_idx")))))) at{struct_item} "tag")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_337 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_338 (i2v 2 i32)))))))
        then
        Goto "#12"
        else
        locinfo: loc_270 ;
          Goto "#10"
      ]> $
      <[ "#12" :=
        locinfo: loc_339 ;
        if: LocInfoE loc_339 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_339 ((LocInfoE loc_340 (use{it_layout size_t} (LocInfoE loc_341 ((LocInfoE loc_342 ((LocInfoE loc_343 ((LocInfoE loc_345 ((LocInfoE loc_348 (!{LPtr} (LocInfoE loc_349 ((LocInfoE loc_350 (!{LPtr} (LocInfoE loc_351 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_352 (use{it_layout size_t} (LocInfoE loc_353 ("slot_idx")))))) at{struct_item} "u")) at_union{union_item_union} "tombstone")) at{struct_tombstone} "key")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_354 (use{it_layout size_t} (LocInfoE loc_355 ("key")))))))
        then
        locinfo: loc_303 ;
          Goto "#9"
        else
        locinfo: loc_270 ;
          Goto "#10"
      ]> $
      <[ "#2" :=
        locinfo: loc_308 ;
        if: LocInfoE loc_308 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_308 ((LocInfoE loc_309 (use{it_layout size_t} (LocInfoE loc_310 ((LocInfoE loc_312 ((LocInfoE loc_315 (!{LPtr} (LocInfoE loc_316 ((LocInfoE loc_317 (!{LPtr} (LocInfoE loc_318 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_319 (use{it_layout size_t} (LocInfoE loc_320 ("slot_idx")))))) at{struct_item} "tag")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_321 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_322 (i2v 0 i32)))))))
        then
        locinfo: loc_303 ;
          Goto "#9"
        else
        Goto "#11"
      ]> $
      <[ "#3" :=
        Return (VOID)
      ]> $
      <[ "#4" :=
        locinfo: loc_270 ;
        if: LocInfoE loc_270 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_270 ((LocInfoE loc_271 (use{it_layout size_t} (LocInfoE loc_272 ((LocInfoE loc_274 ((LocInfoE loc_277 (!{LPtr} (LocInfoE loc_278 ((LocInfoE loc_279 (!{LPtr} (LocInfoE loc_280 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_281 (use{it_layout size_t} (LocInfoE loc_282 ("slot_idx")))))) at{struct_item} "tag")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_283 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_284 (i2v 1 i32)))))))
        then
        Goto "#8"
        else
        locinfo: loc_243 ;
          Goto "#7"
      ]> $
      <[ "#5" :=
        locinfo: loc_243 ;
        expr: (LocInfoE loc_258 ((LocInfoE loc_259 (use{it_layout size_t} (LocInfoE loc_260 ((LocInfoE loc_261 (!{LPtr} (LocInfoE loc_262 ("m")))) at{struct_fixed_size_map} "length")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_263 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_263 (i2v 0 i32)))))) ;
        locinfo: loc_245 ;
        LocInfoE loc_248 ("slot_idx") <-{ it_layout size_t }
          LocInfoE loc_249 ((LocInfoE loc_250 ((LocInfoE loc_251 (use{it_layout size_t} (LocInfoE loc_252 ("slot_idx")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_253 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_253 (i2v 1 i32)))))) %{IntOp size_t, IntOp size_t} (LocInfoE loc_254 (use{it_layout size_t} (LocInfoE loc_255 ((LocInfoE loc_256 (!{LPtr} (LocInfoE loc_257 ("m")))) at{struct_fixed_size_map} "length"))))) ;
        locinfo: loc_246 ;
        Goto "continue8"
      ]> $
      <[ "#6" :=
        locinfo: loc_265 ;
        Return (LocInfoE loc_266 (use{it_layout size_t} (LocInfoE loc_267 ("slot_idx"))))
      ]> $
      <[ "#7" :=
        locinfo: loc_243 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        locinfo: loc_285 ;
        if: LocInfoE loc_285 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_285 ((LocInfoE loc_286 (use{it_layout size_t} (LocInfoE loc_287 ((LocInfoE loc_288 ((LocInfoE loc_289 ((LocInfoE loc_291 ((LocInfoE loc_294 (!{LPtr} (LocInfoE loc_295 ((LocInfoE loc_296 (!{LPtr} (LocInfoE loc_297 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_298 (use{it_layout size_t} (LocInfoE loc_299 ("slot_idx")))))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "key")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_300 (use{it_layout size_t} (LocInfoE loc_301 ("key")))))))
        then
        locinfo: loc_265 ;
          Goto "#6"
        else
        locinfo: loc_243 ;
          Goto "#7"
      ]> $
      <[ "#9" :=
        locinfo: loc_303 ;
        Return (LocInfoE loc_304 (use{it_layout size_t} (LocInfoE loc_305 ("slot_idx"))))
      ]> $
      <[ "continue8" :=
        locinfo: loc_238 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [fsm_insert]. *)
  Definition impl_fsm_insert (fsm_probe fsm_realloc_if_necessary : loc): function := {|
    f_args := [
      ("m", LPtr);
      ("key", it_layout size_t);
      ("value", LPtr)
    ];
    f_local_vars := [
      ("item", LPtr);
      ("replaced", LPtr);
      ("slot_idx", it_layout size_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_370 ;
        "_" <- LocInfoE loc_462 (fsm_realloc_if_necessary) with
          [ LocInfoE loc_463 (use{LPtr} (LocInfoE loc_464 ("m"))) ] ;
        locinfo: loc_452 ;
        "$0" <- LocInfoE loc_454 (fsm_probe) with
          [ LocInfoE loc_455 (use{LPtr} (LocInfoE loc_456 ("m"))) ;
          LocInfoE loc_457 (use{it_layout size_t} (LocInfoE loc_458 ("key"))) ] ;
        "slot_idx" <-{ it_layout size_t } LocInfoE loc_452 ("$0") ;
        "replaced" <-{ LPtr } LocInfoE loc_449 (NULL) ;
        "item" <-{ LPtr }
          LocInfoE loc_436 (&(LocInfoE loc_438 ((LocInfoE loc_441 (!{LPtr} (LocInfoE loc_442 ((LocInfoE loc_443 (!{LPtr} (LocInfoE loc_444 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_445 (use{it_layout size_t} (LocInfoE loc_446 ("slot_idx"))))))) ;
        locinfo: loc_429 ;
        if: LocInfoE loc_429 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_429 ((LocInfoE loc_430 (use{it_layout size_t} (LocInfoE loc_431 ((LocInfoE loc_432 (!{LPtr} (LocInfoE loc_433 ("item")))) at{struct_item} "tag")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_434 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_435 (i2v 1 i32)))))))
        then
        locinfo: loc_401 ;
          Goto "#2"
        else
        locinfo: loc_422 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_375 ;
        LocInfoE loc_395 ((LocInfoE loc_396 (!{LPtr} (LocInfoE loc_397 ("item")))) at{struct_item} "tag") <-{ it_layout size_t }
          LocInfoE loc_398 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_399 (i2v 1 i32))) ;
        locinfo: loc_376 ;
        LocInfoE loc_388 ((LocInfoE loc_389 ((LocInfoE loc_390 ((LocInfoE loc_391 (!{LPtr} (LocInfoE loc_392 ("item")))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "key") <-{ it_layout size_t }
          LocInfoE loc_393 (use{it_layout size_t} (LocInfoE loc_394 ("key"))) ;
        locinfo: loc_377 ;
        LocInfoE loc_381 ((LocInfoE loc_382 ((LocInfoE loc_383 ((LocInfoE loc_384 (!{LPtr} (LocInfoE loc_385 ("item")))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "value") <-{ LPtr }
          LocInfoE loc_386 (use{LPtr} (LocInfoE loc_387 ("value"))) ;
        locinfo: loc_378 ;
        Return (LocInfoE loc_379 (use{LPtr} (LocInfoE loc_380 ("replaced"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_401 ;
        LocInfoE loc_402 ("replaced") <-{ LPtr }
          LocInfoE loc_403 (use{LPtr} (LocInfoE loc_404 ((LocInfoE loc_405 ((LocInfoE loc_406 ((LocInfoE loc_407 (!{LPtr} (LocInfoE loc_408 ("item")))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "value"))) ;
        locinfo: loc_375 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_422 ;
        if: LocInfoE loc_422 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_422 ((LocInfoE loc_423 (use{it_layout size_t} (LocInfoE loc_424 ((LocInfoE loc_425 (!{LPtr} (LocInfoE loc_426 ("item")))) at{struct_item} "tag")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_427 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_428 (i2v 0 i32)))))))
        then
        locinfo: loc_411 ;
          Goto "#4"
        else
        locinfo: loc_375 ;
          Goto "#5"
      ]> $
      <[ "#4" :=
        locinfo: loc_411 ;
        LocInfoE loc_412 ((LocInfoE loc_413 (!{LPtr} (LocInfoE loc_414 ("m")))) at{struct_fixed_size_map} "count") <-{ it_layout size_t }
          LocInfoE loc_415 ((LocInfoE loc_416 (use{it_layout size_t} (LocInfoE loc_417 ((LocInfoE loc_418 (!{LPtr} (LocInfoE loc_419 ("m")))) at{struct_fixed_size_map} "count")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_420 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_420 (i2v 1 i32))))) ;
        locinfo: loc_375 ;
        Goto "#1"
      ]> $
      <[ "#5" :=
        locinfo: loc_375 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [fsm_get]. *)
  Definition impl_fsm_get (fsm_probe : loc): function := {|
    f_args := [
      ("m", LPtr);
      ("key", it_layout size_t)
    ];
    f_local_vars := [
      ("item", LPtr);
      ("slot_idx", it_layout size_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_503 ;
        "$0" <- LocInfoE loc_505 (fsm_probe) with
          [ LocInfoE loc_506 (use{LPtr} (LocInfoE loc_507 ("m"))) ;
          LocInfoE loc_508 (use{it_layout size_t} (LocInfoE loc_509 ("key"))) ] ;
        "slot_idx" <-{ it_layout size_t } LocInfoE loc_503 ("$0") ;
        "item" <-{ LPtr }
          LocInfoE loc_490 (&(LocInfoE loc_492 ((LocInfoE loc_495 (!{LPtr} (LocInfoE loc_496 ((LocInfoE loc_497 (!{LPtr} (LocInfoE loc_498 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_499 (use{it_layout size_t} (LocInfoE loc_500 ("slot_idx"))))))) ;
        locinfo: loc_483 ;
        if: LocInfoE loc_483 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_483 ((LocInfoE loc_484 (use{it_layout size_t} (LocInfoE loc_485 ((LocInfoE loc_486 (!{LPtr} (LocInfoE loc_487 ("item")))) at{struct_item} "tag")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_488 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_489 (i2v 1 i32)))))))
        then
        locinfo: loc_471 ;
          Goto "#1"
        else
        locinfo: loc_481 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_471 ;
        Return (LocInfoE loc_472 (&(LocInfoE loc_474 (!{LPtr} (LocInfoE loc_475 ((LocInfoE loc_476 ((LocInfoE loc_477 ((LocInfoE loc_478 (!{LPtr} (LocInfoE loc_479 ("item")))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "value"))))))
      ]> $
      <[ "#2" :=
        locinfo: loc_481 ;
        Return (LocInfoE loc_482 (NULL))
      ]> $∅
    )%E
  |}.

  (* Definition of function [fsm_remove]. *)
  Definition impl_fsm_remove (fsm_probe : loc): function := {|
    f_args := [
      ("m", LPtr);
      ("key", it_layout size_t)
    ];
    f_local_vars := [
      ("item", LPtr);
      ("removed", LPtr);
      ("slot_idx", it_layout size_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_566 ;
        "$0" <- LocInfoE loc_568 (fsm_probe) with
          [ LocInfoE loc_569 (use{LPtr} (LocInfoE loc_570 ("m"))) ;
          LocInfoE loc_571 (use{it_layout size_t} (LocInfoE loc_572 ("key"))) ] ;
        "slot_idx" <-{ it_layout size_t } LocInfoE loc_566 ("$0") ;
        "item" <-{ LPtr }
          LocInfoE loc_553 (&(LocInfoE loc_555 ((LocInfoE loc_558 (!{LPtr} (LocInfoE loc_559 ((LocInfoE loc_560 (!{LPtr} (LocInfoE loc_561 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_562 (use{it_layout size_t} (LocInfoE loc_563 ("slot_idx"))))))) ;
        locinfo: loc_546 ;
        if: LocInfoE loc_546 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_546 ((LocInfoE loc_547 (use{it_layout size_t} (LocInfoE loc_548 ((LocInfoE loc_549 (!{LPtr} (LocInfoE loc_550 ("item")))) at{struct_item} "tag")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_551 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_552 (i2v 1 i32)))))))
        then
        locinfo: loc_518 ;
          Goto "#1"
        else
        locinfo: loc_544 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_518 ;
        LocInfoE loc_536 ("removed") <-{ LPtr }
          LocInfoE loc_537 (use{LPtr} (LocInfoE loc_538 ((LocInfoE loc_539 ((LocInfoE loc_540 ((LocInfoE loc_541 (!{LPtr} (LocInfoE loc_542 ("item")))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "value"))) ;
        locinfo: loc_519 ;
        LocInfoE loc_531 ((LocInfoE loc_532 (!{LPtr} (LocInfoE loc_533 ("item")))) at{struct_item} "tag") <-{ it_layout size_t }
          LocInfoE loc_534 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_535 (i2v 2 i32))) ;
        locinfo: loc_520 ;
        LocInfoE loc_524 ((LocInfoE loc_525 ((LocInfoE loc_526 ((LocInfoE loc_527 (!{LPtr} (LocInfoE loc_528 ("item")))) at{struct_item} "u")) at_union{union_item_union} "tombstone")) at{struct_tombstone} "key") <-{ it_layout size_t }
          LocInfoE loc_529 (use{it_layout size_t} (LocInfoE loc_530 ("key"))) ;
        locinfo: loc_521 ;
        Return (LocInfoE loc_522 (use{LPtr} (LocInfoE loc_523 ("removed"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_544 ;
        Return (LocInfoE loc_545 (NULL))
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
        locinfo: loc_577 ;
        Return (LocInfoE loc_578 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_578 (i2v 2 i32))))
      ]> $∅
    )%E
  |}.
End code.
