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
  Definition loc_153 : location_info := LocationInfo file_0 78 2 78 56.
  Definition loc_154 : location_info := LocationInfo file_0 79 2 79 18.
  Definition loc_155 : location_info := LocationInfo file_0 80 2 80 21.
  Definition loc_156 : location_info := LocationInfo file_0 81 2 81 17.
  Definition loc_157 : location_info := LocationInfo file_0 89 2 92 3.
  Definition loc_158 : location_info := LocationInfo file_0 89 6 89 11.
  Definition loc_159 : location_info := LocationInfo file_0 89 2 92 3.
  Definition loc_160 : location_info := LocationInfo file_0 89 30 92 3.
  Definition loc_161 : location_info := LocationInfo file_0 90 4 90 37.
  Definition loc_162 : location_info := LocationInfo file_0 91 4 91 37.
  Definition loc_163 : location_info := LocationInfo file_0 89 2 92 3.
  Definition loc_164 : location_info := LocationInfo file_0 89 22 89 28.
  Definition loc_165 : location_info := LocationInfo file_0 89 22 89 23.
  Definition loc_166 : location_info := LocationInfo file_0 89 22 89 28.
  Definition loc_167 : location_info := LocationInfo file_0 89 22 89 23.
  Definition loc_168 : location_info := LocationInfo file_0 89 22 89 23.
  Definition loc_169 : location_info := LocationInfo file_0 89 27 89 28.
  Definition loc_170 : location_info := LocationInfo file_0 91 4 91 32.
  Definition loc_171 : location_info := LocationInfo file_0 91 4 91 26.
  Definition loc_172 : location_info := LocationInfo file_0 91 4 91 20.
  Definition loc_173 : location_info := LocationInfo file_0 91 4 91 18.
  Definition loc_174 : location_info := LocationInfo file_0 91 4 91 18.
  Definition loc_175 : location_info := LocationInfo file_0 91 4 91 15.
  Definition loc_176 : location_info := LocationInfo file_0 91 4 91 15.
  Definition loc_177 : location_info := LocationInfo file_0 91 6 91 14.
  Definition loc_178 : location_info := LocationInfo file_0 91 6 91 14.
  Definition loc_179 : location_info := LocationInfo file_0 91 6 91 7.
  Definition loc_180 : location_info := LocationInfo file_0 91 6 91 7.
  Definition loc_181 : location_info := LocationInfo file_0 91 16 91 17.
  Definition loc_182 : location_info := LocationInfo file_0 91 16 91 17.
  Definition loc_183 : location_info := LocationInfo file_0 91 35 91 36.
  Definition loc_184 : location_info := LocationInfo file_0 90 4 90 22.
  Definition loc_185 : location_info := LocationInfo file_0 90 4 90 18.
  Definition loc_186 : location_info := LocationInfo file_0 90 4 90 18.
  Definition loc_187 : location_info := LocationInfo file_0 90 4 90 15.
  Definition loc_188 : location_info := LocationInfo file_0 90 4 90 15.
  Definition loc_189 : location_info := LocationInfo file_0 90 6 90 14.
  Definition loc_190 : location_info := LocationInfo file_0 90 6 90 14.
  Definition loc_191 : location_info := LocationInfo file_0 90 6 90 7.
  Definition loc_192 : location_info := LocationInfo file_0 90 6 90 7.
  Definition loc_193 : location_info := LocationInfo file_0 90 16 90 17.
  Definition loc_194 : location_info := LocationInfo file_0 90 16 90 17.
  Definition loc_195 : location_info := LocationInfo file_0 90 25 90 36.
  Definition loc_196 : location_info := LocationInfo file_0 90 34 90 35.
  Definition loc_197 : location_info := LocationInfo file_0 89 13 89 20.
  Definition loc_198 : location_info := LocationInfo file_0 89 13 89 14.
  Definition loc_199 : location_info := LocationInfo file_0 89 13 89 14.
  Definition loc_200 : location_info := LocationInfo file_0 89 17 89 20.
  Definition loc_201 : location_info := LocationInfo file_0 89 17 89 20.
  Definition loc_202 : location_info := LocationInfo file_0 89 6 89 7.
  Definition loc_203 : location_info := LocationInfo file_0 89 10 89 11.
  Definition loc_204 : location_info := LocationInfo file_0 81 2 81 10.
  Definition loc_205 : location_info := LocationInfo file_0 81 2 81 3.
  Definition loc_206 : location_info := LocationInfo file_0 81 2 81 3.
  Definition loc_207 : location_info := LocationInfo file_0 81 13 81 16.
  Definition loc_208 : location_info := LocationInfo file_0 81 13 81 16.
  Definition loc_209 : location_info := LocationInfo file_0 80 2 80 10.
  Definition loc_210 : location_info := LocationInfo file_0 80 2 80 3.
  Definition loc_211 : location_info := LocationInfo file_0 80 2 80 3.
  Definition loc_212 : location_info := LocationInfo file_0 80 13 80 20.
  Definition loc_213 : location_info := LocationInfo file_0 80 13 80 20.
  Definition loc_214 : location_info := LocationInfo file_0 79 2 79 11.
  Definition loc_215 : location_info := LocationInfo file_0 79 2 79 3.
  Definition loc_216 : location_info := LocationInfo file_0 79 2 79 3.
  Definition loc_217 : location_info := LocationInfo file_0 79 14 79 17.
  Definition loc_218 : location_info := LocationInfo file_0 79 14 79 17.
  Definition loc_219 : location_info := LocationInfo file_0 78 18 78 55.
  Definition loc_220 : location_info := LocationInfo file_0 78 18 78 29.
  Definition loc_221 : location_info := LocationInfo file_0 78 18 78 29.
  Definition loc_222 : location_info := LocationInfo file_0 78 30 78 49.
  Definition loc_223 : location_info := LocationInfo file_0 78 51 78 54.
  Definition loc_224 : location_info := LocationInfo file_0 78 51 78 54.
  Definition loc_229 : location_info := LocationInfo file_0 103 4 103 21.
  Definition loc_230 : location_info := LocationInfo file_0 103 11 103 20.
  Definition loc_231 : location_info := LocationInfo file_0 103 11 103 14.
  Definition loc_232 : location_info := LocationInfo file_0 103 11 103 14.
  Definition loc_233 : location_info := LocationInfo file_0 103 17 103 20.
  Definition loc_234 : location_info := LocationInfo file_0 103 17 103 20.
  Definition loc_237 : location_info := LocationInfo file_0 116 4 116 55.
  Definition loc_238 : location_info := LocationInfo file_0 122 4 131 5.
  Definition loc_239 : location_info := LocationInfo file_0 122 4 131 5.
  Definition loc_240 : location_info := LocationInfo file_0 122 13 131 5.
  Definition loc_241 : location_info := LocationInfo file_0 123 8 125 9.
  Definition loc_242 : location_info := LocationInfo file_0 126 8 128 9.
  Definition loc_243 : location_info := LocationInfo file_0 129 8 129 22.
  Definition loc_244 : location_info := LocationInfo file_0 129 22 129 9.
  Definition loc_245 : location_info := LocationInfo file_0 130 8 130 46.
  Definition loc_246 : location_info := LocationInfo file_0 122 4 131 5.
  Definition loc_247 : location_info := LocationInfo file_0 122 4 131 5.
  Definition loc_248 : location_info := LocationInfo file_0 130 8 130 16.
  Definition loc_249 : location_info := LocationInfo file_0 130 19 130 45.
  Definition loc_250 : location_info := LocationInfo file_0 130 19 130 33.
  Definition loc_251 : location_info := LocationInfo file_0 130 20 130 28.
  Definition loc_252 : location_info := LocationInfo file_0 130 20 130 28.
  Definition loc_253 : location_info := LocationInfo file_0 130 31 130 32.
  Definition loc_254 : location_info := LocationInfo file_0 130 36 130 45.
  Definition loc_255 : location_info := LocationInfo file_0 130 36 130 45.
  Definition loc_256 : location_info := LocationInfo file_0 130 36 130 37.
  Definition loc_257 : location_info := LocationInfo file_0 130 36 130 37.
  Definition loc_258 : location_info := LocationInfo file_0 129 8 129 21.
  Definition loc_259 : location_info := LocationInfo file_0 129 8 129 17.
  Definition loc_260 : location_info := LocationInfo file_0 129 8 129 17.
  Definition loc_261 : location_info := LocationInfo file_0 129 8 129 9.
  Definition loc_262 : location_info := LocationInfo file_0 129 8 129 9.
  Definition loc_263 : location_info := LocationInfo file_0 129 20 129 21.
  Definition loc_264 : location_info := LocationInfo file_0 126 97 128 9.
  Definition loc_265 : location_info := LocationInfo file_0 127 12 127 28.
  Definition loc_266 : location_info := LocationInfo file_0 127 19 127 27.
  Definition loc_267 : location_info := LocationInfo file_0 127 19 127 27.
  Definition loc_270 : location_info := LocationInfo file_0 126 11 126 51.
  Definition loc_271 : location_info := LocationInfo file_0 126 11 126 36.
  Definition loc_272 : location_info := LocationInfo file_0 126 11 126 36.
  Definition loc_273 : location_info := LocationInfo file_0 126 11 126 32.
  Definition loc_274 : location_info := LocationInfo file_0 126 11 126 32.
  Definition loc_275 : location_info := LocationInfo file_0 126 11 126 22.
  Definition loc_276 : location_info := LocationInfo file_0 126 11 126 22.
  Definition loc_277 : location_info := LocationInfo file_0 126 13 126 21.
  Definition loc_278 : location_info := LocationInfo file_0 126 13 126 21.
  Definition loc_279 : location_info := LocationInfo file_0 126 13 126 14.
  Definition loc_280 : location_info := LocationInfo file_0 126 13 126 14.
  Definition loc_281 : location_info := LocationInfo file_0 126 23 126 31.
  Definition loc_282 : location_info := LocationInfo file_0 126 23 126 31.
  Definition loc_283 : location_info := LocationInfo file_0 126 40 126 51.
  Definition loc_284 : location_info := LocationInfo file_0 126 49 126 50.
  Definition loc_285 : location_info := LocationInfo file_0 126 55 126 95.
  Definition loc_286 : location_info := LocationInfo file_0 126 55 126 88.
  Definition loc_287 : location_info := LocationInfo file_0 126 55 126 88.
  Definition loc_288 : location_info := LocationInfo file_0 126 55 126 84.
  Definition loc_289 : location_info := LocationInfo file_0 126 55 126 78.
  Definition loc_290 : location_info := LocationInfo file_0 126 55 126 76.
  Definition loc_291 : location_info := LocationInfo file_0 126 55 126 76.
  Definition loc_292 : location_info := LocationInfo file_0 126 55 126 66.
  Definition loc_293 : location_info := LocationInfo file_0 126 55 126 66.
  Definition loc_294 : location_info := LocationInfo file_0 126 57 126 65.
  Definition loc_295 : location_info := LocationInfo file_0 126 57 126 65.
  Definition loc_296 : location_info := LocationInfo file_0 126 57 126 58.
  Definition loc_297 : location_info := LocationInfo file_0 126 57 126 58.
  Definition loc_298 : location_info := LocationInfo file_0 126 67 126 75.
  Definition loc_299 : location_info := LocationInfo file_0 126 67 126 75.
  Definition loc_300 : location_info := LocationInfo file_0 126 92 126 95.
  Definition loc_301 : location_info := LocationInfo file_0 126 92 126 95.
  Definition loc_302 : location_info := LocationInfo file_0 123 147 125 9.
  Definition loc_303 : location_info := LocationInfo file_0 124 12 124 28.
  Definition loc_304 : location_info := LocationInfo file_0 124 19 124 27.
  Definition loc_305 : location_info := LocationInfo file_0 124 19 124 27.
  Definition loc_308 : location_info := LocationInfo file_0 123 11 123 51.
  Definition loc_309 : location_info := LocationInfo file_0 123 11 123 36.
  Definition loc_310 : location_info := LocationInfo file_0 123 11 123 36.
  Definition loc_311 : location_info := LocationInfo file_0 123 11 123 32.
  Definition loc_312 : location_info := LocationInfo file_0 123 11 123 32.
  Definition loc_313 : location_info := LocationInfo file_0 123 11 123 22.
  Definition loc_314 : location_info := LocationInfo file_0 123 11 123 22.
  Definition loc_315 : location_info := LocationInfo file_0 123 13 123 21.
  Definition loc_316 : location_info := LocationInfo file_0 123 13 123 21.
  Definition loc_317 : location_info := LocationInfo file_0 123 13 123 14.
  Definition loc_318 : location_info := LocationInfo file_0 123 13 123 14.
  Definition loc_319 : location_info := LocationInfo file_0 123 23 123 31.
  Definition loc_320 : location_info := LocationInfo file_0 123 23 123 31.
  Definition loc_321 : location_info := LocationInfo file_0 123 40 123 51.
  Definition loc_322 : location_info := LocationInfo file_0 123 49 123 50.
  Definition loc_324 : location_info := LocationInfo file_0 123 56 123 96.
  Definition loc_325 : location_info := LocationInfo file_0 123 56 123 81.
  Definition loc_326 : location_info := LocationInfo file_0 123 56 123 81.
  Definition loc_327 : location_info := LocationInfo file_0 123 56 123 77.
  Definition loc_328 : location_info := LocationInfo file_0 123 56 123 77.
  Definition loc_329 : location_info := LocationInfo file_0 123 56 123 67.
  Definition loc_330 : location_info := LocationInfo file_0 123 56 123 67.
  Definition loc_331 : location_info := LocationInfo file_0 123 58 123 66.
  Definition loc_332 : location_info := LocationInfo file_0 123 58 123 66.
  Definition loc_333 : location_info := LocationInfo file_0 123 58 123 59.
  Definition loc_334 : location_info := LocationInfo file_0 123 58 123 59.
  Definition loc_335 : location_info := LocationInfo file_0 123 68 123 76.
  Definition loc_336 : location_info := LocationInfo file_0 123 68 123 76.
  Definition loc_337 : location_info := LocationInfo file_0 123 85 123 96.
  Definition loc_338 : location_info := LocationInfo file_0 123 94 123 95.
  Definition loc_339 : location_info := LocationInfo file_0 123 100 123 144.
  Definition loc_340 : location_info := LocationInfo file_0 123 100 123 137.
  Definition loc_341 : location_info := LocationInfo file_0 123 100 123 137.
  Definition loc_342 : location_info := LocationInfo file_0 123 100 123 133.
  Definition loc_343 : location_info := LocationInfo file_0 123 100 123 123.
  Definition loc_344 : location_info := LocationInfo file_0 123 100 123 121.
  Definition loc_345 : location_info := LocationInfo file_0 123 100 123 121.
  Definition loc_346 : location_info := LocationInfo file_0 123 100 123 111.
  Definition loc_347 : location_info := LocationInfo file_0 123 100 123 111.
  Definition loc_348 : location_info := LocationInfo file_0 123 102 123 110.
  Definition loc_349 : location_info := LocationInfo file_0 123 102 123 110.
  Definition loc_350 : location_info := LocationInfo file_0 123 102 123 103.
  Definition loc_351 : location_info := LocationInfo file_0 123 102 123 103.
  Definition loc_352 : location_info := LocationInfo file_0 123 112 123 120.
  Definition loc_353 : location_info := LocationInfo file_0 123 112 123 120.
  Definition loc_354 : location_info := LocationInfo file_0 123 141 123 144.
  Definition loc_355 : location_info := LocationInfo file_0 123 141 123 144.
  Definition loc_356 : location_info := LocationInfo file_0 122 10 122 11.
  Definition loc_357 : location_info := LocationInfo file_0 116 22 116 54.
  Definition loc_358 : location_info := LocationInfo file_0 116 22 116 38.
  Definition loc_359 : location_info := LocationInfo file_0 116 22 116 38.
  Definition loc_360 : location_info := LocationInfo file_0 116 39 116 48.
  Definition loc_361 : location_info := LocationInfo file_0 116 39 116 48.
  Definition loc_362 : location_info := LocationInfo file_0 116 39 116 40.
  Definition loc_363 : location_info := LocationInfo file_0 116 39 116 40.
  Definition loc_364 : location_info := LocationInfo file_0 116 50 116 53.
  Definition loc_365 : location_info := LocationInfo file_0 116 50 116 53.
  Definition loc_370 : location_info := LocationInfo file_0 145 4 145 32.
  Definition loc_371 : location_info := LocationInfo file_0 146 4 146 40.
  Definition loc_372 : location_info := LocationInfo file_0 147 4 147 36.
  Definition loc_373 : location_info := LocationInfo file_0 148 4 148 47.
  Definition loc_374 : location_info := LocationInfo file_0 149 4 153 5.
  Definition loc_375 : location_info := LocationInfo file_0 155 4 155 28.
  Definition loc_376 : location_info := LocationInfo file_0 156 4 156 28.
  Definition loc_377 : location_info := LocationInfo file_0 157 4 157 32.
  Definition loc_378 : location_info := LocationInfo file_0 159 4 159 20.
  Definition loc_379 : location_info := LocationInfo file_0 159 11 159 19.
  Definition loc_380 : location_info := LocationInfo file_0 159 11 159 19.
  Definition loc_381 : location_info := LocationInfo file_0 157 4 157 23.
  Definition loc_382 : location_info := LocationInfo file_0 157 4 157 17.
  Definition loc_383 : location_info := LocationInfo file_0 157 4 157 11.
  Definition loc_384 : location_info := LocationInfo file_0 157 4 157 8.
  Definition loc_385 : location_info := LocationInfo file_0 157 4 157 8.
  Definition loc_386 : location_info := LocationInfo file_0 157 26 157 31.
  Definition loc_387 : location_info := LocationInfo file_0 157 26 157 31.
  Definition loc_388 : location_info := LocationInfo file_0 156 4 156 21.
  Definition loc_389 : location_info := LocationInfo file_0 156 4 156 17.
  Definition loc_390 : location_info := LocationInfo file_0 156 4 156 11.
  Definition loc_391 : location_info := LocationInfo file_0 156 4 156 8.
  Definition loc_392 : location_info := LocationInfo file_0 156 4 156 8.
  Definition loc_393 : location_info := LocationInfo file_0 156 24 156 27.
  Definition loc_394 : location_info := LocationInfo file_0 156 24 156 27.
  Definition loc_395 : location_info := LocationInfo file_0 155 4 155 13.
  Definition loc_396 : location_info := LocationInfo file_0 155 4 155 8.
  Definition loc_397 : location_info := LocationInfo file_0 155 4 155 8.
  Definition loc_398 : location_info := LocationInfo file_0 155 16 155 27.
  Definition loc_399 : location_info := LocationInfo file_0 155 25 155 26.
  Definition loc_400 : location_info := LocationInfo file_0 149 34 151 5.
  Definition loc_401 : location_info := LocationInfo file_0 150 8 150 39.
  Definition loc_402 : location_info := LocationInfo file_0 150 8 150 16.
  Definition loc_403 : location_info := LocationInfo file_0 150 19 150 38.
  Definition loc_404 : location_info := LocationInfo file_0 150 19 150 38.
  Definition loc_405 : location_info := LocationInfo file_0 150 19 150 32.
  Definition loc_406 : location_info := LocationInfo file_0 150 19 150 26.
  Definition loc_407 : location_info := LocationInfo file_0 150 19 150 23.
  Definition loc_408 : location_info := LocationInfo file_0 150 19 150 23.
  Definition loc_409 : location_info := LocationInfo file_0 151 11 153 5.
  Definition loc_410 : location_info := LocationInfo file_0 151 40 153 5.
  Definition loc_411 : location_info := LocationInfo file_0 152 6 152 20.
  Definition loc_412 : location_info := LocationInfo file_0 152 6 152 14.
  Definition loc_413 : location_info := LocationInfo file_0 152 6 152 7.
  Definition loc_414 : location_info := LocationInfo file_0 152 6 152 7.
  Definition loc_415 : location_info := LocationInfo file_0 152 6 152 19.
  Definition loc_416 : location_info := LocationInfo file_0 152 6 152 14.
  Definition loc_417 : location_info := LocationInfo file_0 152 6 152 14.
  Definition loc_418 : location_info := LocationInfo file_0 152 6 152 7.
  Definition loc_419 : location_info := LocationInfo file_0 152 6 152 7.
  Definition loc_420 : location_info := LocationInfo file_0 152 18 152 19.
  Definition loc_422 : location_info := LocationInfo file_0 151 14 151 38.
  Definition loc_423 : location_info := LocationInfo file_0 151 14 151 23.
  Definition loc_424 : location_info := LocationInfo file_0 151 14 151 23.
  Definition loc_425 : location_info := LocationInfo file_0 151 14 151 18.
  Definition loc_426 : location_info := LocationInfo file_0 151 14 151 18.
  Definition loc_427 : location_info := LocationInfo file_0 151 27 151 38.
  Definition loc_428 : location_info := LocationInfo file_0 151 36 151 37.
  Definition loc_429 : location_info := LocationInfo file_0 149 8 149 32.
  Definition loc_430 : location_info := LocationInfo file_0 149 8 149 17.
  Definition loc_431 : location_info := LocationInfo file_0 149 8 149 17.
  Definition loc_432 : location_info := LocationInfo file_0 149 8 149 12.
  Definition loc_433 : location_info := LocationInfo file_0 149 8 149 12.
  Definition loc_434 : location_info := LocationInfo file_0 149 21 149 32.
  Definition loc_435 : location_info := LocationInfo file_0 149 30 149 31.
  Definition loc_436 : location_info := LocationInfo file_0 148 24 148 46.
  Definition loc_437 : location_info := LocationInfo file_0 148 25 148 46.
  Definition loc_438 : location_info := LocationInfo file_0 148 25 148 46.
  Definition loc_439 : location_info := LocationInfo file_0 148 25 148 36.
  Definition loc_440 : location_info := LocationInfo file_0 148 25 148 36.
  Definition loc_441 : location_info := LocationInfo file_0 148 27 148 35.
  Definition loc_442 : location_info := LocationInfo file_0 148 27 148 35.
  Definition loc_443 : location_info := LocationInfo file_0 148 27 148 28.
  Definition loc_444 : location_info := LocationInfo file_0 148 27 148 28.
  Definition loc_445 : location_info := LocationInfo file_0 148 37 148 45.
  Definition loc_446 : location_info := LocationInfo file_0 148 37 148 45.
  Definition loc_449 : location_info := LocationInfo file_0 147 21 147 35.
  Definition loc_452 : location_info := LocationInfo file_0 146 22 146 39.
  Definition loc_453 : location_info := LocationInfo file_0 146 22 146 31.
  Definition loc_454 : location_info := LocationInfo file_0 146 22 146 31.
  Definition loc_455 : location_info := LocationInfo file_0 146 32 146 33.
  Definition loc_456 : location_info := LocationInfo file_0 146 32 146 33.
  Definition loc_457 : location_info := LocationInfo file_0 146 35 146 38.
  Definition loc_458 : location_info := LocationInfo file_0 146 35 146 38.
  Definition loc_461 : location_info := LocationInfo file_0 145 4 145 28.
  Definition loc_462 : location_info := LocationInfo file_0 145 4 145 28.
  Definition loc_463 : location_info := LocationInfo file_0 145 29 145 30.
  Definition loc_464 : location_info := LocationInfo file_0 145 29 145 30.
  Definition loc_467 : location_info := LocationInfo file_0 172 4 172 40.
  Definition loc_468 : location_info := LocationInfo file_0 173 4 173 47.
  Definition loc_469 : location_info := LocationInfo file_0 175 4 179 5.
  Definition loc_470 : location_info := LocationInfo file_0 175 34 177 5.
  Definition loc_471 : location_info := LocationInfo file_0 176 8 176 37.
  Definition loc_472 : location_info := LocationInfo file_0 176 15 176 36.
  Definition loc_473 : location_info := LocationInfo file_0 176 16 176 36.
  Definition loc_474 : location_info := LocationInfo file_0 176 17 176 36.
  Definition loc_475 : location_info := LocationInfo file_0 176 17 176 36.
  Definition loc_476 : location_info := LocationInfo file_0 176 17 176 30.
  Definition loc_477 : location_info := LocationInfo file_0 176 17 176 24.
  Definition loc_478 : location_info := LocationInfo file_0 176 17 176 21.
  Definition loc_479 : location_info := LocationInfo file_0 176 17 176 21.
  Definition loc_480 : location_info := LocationInfo file_0 177 11 179 5.
  Definition loc_481 : location_info := LocationInfo file_0 178 8 178 30.
  Definition loc_482 : location_info := LocationInfo file_0 178 15 178 29.
  Definition loc_483 : location_info := LocationInfo file_0 175 8 175 32.
  Definition loc_484 : location_info := LocationInfo file_0 175 8 175 17.
  Definition loc_485 : location_info := LocationInfo file_0 175 8 175 17.
  Definition loc_486 : location_info := LocationInfo file_0 175 8 175 12.
  Definition loc_487 : location_info := LocationInfo file_0 175 8 175 12.
  Definition loc_488 : location_info := LocationInfo file_0 175 21 175 32.
  Definition loc_489 : location_info := LocationInfo file_0 175 30 175 31.
  Definition loc_490 : location_info := LocationInfo file_0 173 24 173 46.
  Definition loc_491 : location_info := LocationInfo file_0 173 25 173 46.
  Definition loc_492 : location_info := LocationInfo file_0 173 25 173 46.
  Definition loc_493 : location_info := LocationInfo file_0 173 25 173 36.
  Definition loc_494 : location_info := LocationInfo file_0 173 25 173 36.
  Definition loc_495 : location_info := LocationInfo file_0 173 27 173 35.
  Definition loc_496 : location_info := LocationInfo file_0 173 27 173 35.
  Definition loc_497 : location_info := LocationInfo file_0 173 27 173 28.
  Definition loc_498 : location_info := LocationInfo file_0 173 27 173 28.
  Definition loc_499 : location_info := LocationInfo file_0 173 37 173 45.
  Definition loc_500 : location_info := LocationInfo file_0 173 37 173 45.
  Definition loc_503 : location_info := LocationInfo file_0 172 22 172 39.
  Definition loc_504 : location_info := LocationInfo file_0 172 22 172 31.
  Definition loc_505 : location_info := LocationInfo file_0 172 22 172 31.
  Definition loc_506 : location_info := LocationInfo file_0 172 32 172 33.
  Definition loc_507 : location_info := LocationInfo file_0 172 32 172 33.
  Definition loc_508 : location_info := LocationInfo file_0 172 35 172 38.
  Definition loc_509 : location_info := LocationInfo file_0 172 35 172 38.
  Definition loc_514 : location_info := LocationInfo file_0 192 4 192 40.
  Definition loc_515 : location_info := LocationInfo file_0 193 4 193 47.
  Definition loc_516 : location_info := LocationInfo file_0 195 4 202 5.
  Definition loc_517 : location_info := LocationInfo file_0 195 34 200 5.
  Definition loc_518 : location_info := LocationInfo file_0 196 8 196 38.
  Definition loc_519 : location_info := LocationInfo file_0 197 8 197 32.
  Definition loc_520 : location_info := LocationInfo file_0 198 8 198 36.
  Definition loc_521 : location_info := LocationInfo file_0 199 8 199 23.
  Definition loc_522 : location_info := LocationInfo file_0 199 15 199 22.
  Definition loc_523 : location_info := LocationInfo file_0 199 15 199 22.
  Definition loc_524 : location_info := LocationInfo file_0 198 8 198 29.
  Definition loc_525 : location_info := LocationInfo file_0 198 8 198 25.
  Definition loc_526 : location_info := LocationInfo file_0 198 8 198 15.
  Definition loc_527 : location_info := LocationInfo file_0 198 8 198 12.
  Definition loc_528 : location_info := LocationInfo file_0 198 8 198 12.
  Definition loc_529 : location_info := LocationInfo file_0 198 32 198 35.
  Definition loc_530 : location_info := LocationInfo file_0 198 32 198 35.
  Definition loc_531 : location_info := LocationInfo file_0 197 8 197 17.
  Definition loc_532 : location_info := LocationInfo file_0 197 8 197 12.
  Definition loc_533 : location_info := LocationInfo file_0 197 8 197 12.
  Definition loc_534 : location_info := LocationInfo file_0 197 20 197 31.
  Definition loc_535 : location_info := LocationInfo file_0 197 29 197 30.
  Definition loc_536 : location_info := LocationInfo file_0 196 8 196 15.
  Definition loc_537 : location_info := LocationInfo file_0 196 18 196 37.
  Definition loc_538 : location_info := LocationInfo file_0 196 18 196 37.
  Definition loc_539 : location_info := LocationInfo file_0 196 18 196 31.
  Definition loc_540 : location_info := LocationInfo file_0 196 18 196 25.
  Definition loc_541 : location_info := LocationInfo file_0 196 18 196 22.
  Definition loc_542 : location_info := LocationInfo file_0 196 18 196 22.
  Definition loc_543 : location_info := LocationInfo file_0 200 11 202 5.
  Definition loc_544 : location_info := LocationInfo file_0 201 8 201 30.
  Definition loc_545 : location_info := LocationInfo file_0 201 15 201 29.
  Definition loc_546 : location_info := LocationInfo file_0 195 8 195 32.
  Definition loc_547 : location_info := LocationInfo file_0 195 8 195 17.
  Definition loc_548 : location_info := LocationInfo file_0 195 8 195 17.
  Definition loc_549 : location_info := LocationInfo file_0 195 8 195 12.
  Definition loc_550 : location_info := LocationInfo file_0 195 8 195 12.
  Definition loc_551 : location_info := LocationInfo file_0 195 21 195 32.
  Definition loc_552 : location_info := LocationInfo file_0 195 30 195 31.
  Definition loc_553 : location_info := LocationInfo file_0 193 24 193 46.
  Definition loc_554 : location_info := LocationInfo file_0 193 25 193 46.
  Definition loc_555 : location_info := LocationInfo file_0 193 25 193 46.
  Definition loc_556 : location_info := LocationInfo file_0 193 25 193 36.
  Definition loc_557 : location_info := LocationInfo file_0 193 25 193 36.
  Definition loc_558 : location_info := LocationInfo file_0 193 27 193 35.
  Definition loc_559 : location_info := LocationInfo file_0 193 27 193 35.
  Definition loc_560 : location_info := LocationInfo file_0 193 27 193 28.
  Definition loc_561 : location_info := LocationInfo file_0 193 27 193 28.
  Definition loc_562 : location_info := LocationInfo file_0 193 37 193 45.
  Definition loc_563 : location_info := LocationInfo file_0 193 37 193 45.
  Definition loc_566 : location_info := LocationInfo file_0 192 22 192 39.
  Definition loc_567 : location_info := LocationInfo file_0 192 22 192 31.
  Definition loc_568 : location_info := LocationInfo file_0 192 22 192 31.
  Definition loc_569 : location_info := LocationInfo file_0 192 32 192 33.
  Definition loc_570 : location_info := LocationInfo file_0 192 32 192 33.
  Definition loc_571 : location_info := LocationInfo file_0 192 35 192 38.
  Definition loc_572 : location_info := LocationInfo file_0 192 35 192 38.
  Definition loc_577 : location_info := LocationInfo file_0 212 2 212 11.
  Definition loc_578 : location_info := LocationInfo file_0 212 9 212 10.

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

  (* Definition of function [fsm_realloc_if_necessary]. *)
  Definition impl_fsm_realloc_if_necessary (global_compute_min_count global_free_array global_fsm_init global_fsm_insert : loc): function := {|
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
        locinfo: loc_139 ;
        if: LocInfoE loc_139 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_139 ((LocInfoE loc_140 (Call (LocInfoE loc_142 (global_compute_min_count)) [@{expr} LocInfoE loc_143 (use{it_layout size_t} (LocInfoE loc_144 ((LocInfoE loc_145 (!{void*} (LocInfoE loc_146 ("m")))) at{struct_fixed_size_map} "length"))) ])) ≤{IntOp size_t, IntOp size_t} (LocInfoE loc_147 (use{it_layout size_t} (LocInfoE loc_148 ((LocInfoE loc_149 (!{void*} (LocInfoE loc_150 ("m")))) at{struct_fixed_size_map} "count")))))))
        then
        locinfo: loc_136 ;
          Goto "#14"
        else
        locinfo: loc_123 ;
          Goto "#15"
      ]> $
      <[ "#1" :=
        locinfo: loc_123 ;
        if: LocInfoE loc_123 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_123 ((LocInfoE loc_124 (use{it_layout size_t} (LocInfoE loc_125 ((LocInfoE loc_126 (!{void*} (LocInfoE loc_127 ("m")))) at{struct_fixed_size_map} "length")))) <{IntOp size_t, IntOp size_t} (LocInfoE loc_128 ((LocInfoE loc_129 ((LocInfoE loc_130 ((LocInfoE loc_131 (i2v (max_int size_t) size_t)) /{IntOp size_t, IntOp size_t} (LocInfoE loc_132 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_132 (i2v 2 i32)))))) /{IntOp size_t, IntOp size_t} (LocInfoE loc_133 (i2v (layout_of struct_item).(ly_size) size_t)))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_134 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_134 (i2v 16 i32)))))))))
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
          LocInfoE loc_107 ((LocInfoE loc_108 (use{it_layout size_t} (LocInfoE loc_109 ((LocInfoE loc_110 (!{void*} (LocInfoE loc_111 ("m")))) at{struct_fixed_size_map} "length")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_112 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_112 (i2v 2 i32))))) ;
        locinfo: loc_5 ;
        expr: (LocInfoE loc_5 (Call (LocInfoE loc_102 (global_fsm_init)) [@{expr} LocInfoE loc_103 (&(LocInfoE loc_104 ("m2"))) ;
        LocInfoE loc_105 (use{it_layout size_t} (LocInfoE loc_106 ("new_len"))) ])) ;
        "i" <-{ it_layout size_t }
          LocInfoE loc_98 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_98 (i2v 0 i32))) ;
        locinfo: loc_8 ;
        Goto "#3"
      ]> $
      <[ "#3" :=
        locinfo: loc_91 ;
        if: LocInfoE loc_91 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_91 ((LocInfoE loc_92 (use{it_layout size_t} (LocInfoE loc_93 ("i")))) <{IntOp size_t, IntOp size_t} (LocInfoE loc_94 (use{it_layout size_t} (LocInfoE loc_95 ((LocInfoE loc_96 (!{void*} (LocInfoE loc_97 ("m")))) at{struct_fixed_size_map} "length")))))))
        then
        locinfo: loc_76 ;
          Goto "#4"
        else
        locinfo: loc_9 ;
          Goto "#5"
      ]> $
      <[ "#4" :=
        locinfo: loc_76 ;
        if: LocInfoE loc_76 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_76 ((LocInfoE loc_77 (use{it_layout size_t} (LocInfoE loc_78 ((LocInfoE loc_80 ((LocInfoE loc_83 (!{void*} (LocInfoE loc_84 ((LocInfoE loc_85 (!{void*} (LocInfoE loc_86 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_87 (use{it_layout size_t} (LocInfoE loc_88 ("i")))))) at{struct_item} "tag")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_89 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_90 (i2v 1 i32)))))))
        then
        locinfo: loc_42 ;
          Goto "#7"
        else
        locinfo: loc_29 ;
          Goto "#8"
      ]> $
      <[ "#5" :=
        locinfo: loc_9 ;
        expr: (LocInfoE loc_9 (Call (LocInfoE loc_17 (global_free_array)) [@{expr} LocInfoE loc_18 (i2v (layout_of struct_item).(ly_size) size_t) ;
        LocInfoE loc_19 (use{it_layout size_t} (LocInfoE loc_20 ((LocInfoE loc_21 (!{void*} (LocInfoE loc_22 ("m")))) at{struct_fixed_size_map} "length"))) ;
        LocInfoE loc_23 (use{void*} (LocInfoE loc_24 ((LocInfoE loc_25 (!{void*} (LocInfoE loc_26 ("m")))) at{struct_fixed_size_map} "items"))) ])) ;
        locinfo: loc_10 ;
        LocInfoE loc_12 (!{void*} (LocInfoE loc_13 ("m"))) <-{ layout_of struct_fixed_size_map }
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
        expr: (LocInfoE loc_42 (Call (LocInfoE loc_44 (global_fsm_insert)) [@{expr} LocInfoE loc_45 (&(LocInfoE loc_46 ("m2"))) ;
        LocInfoE loc_47 (use{it_layout size_t} (LocInfoE loc_48 ((LocInfoE loc_49 ((LocInfoE loc_50 ((LocInfoE loc_52 ((LocInfoE loc_55 (!{void*} (LocInfoE loc_56 ((LocInfoE loc_57 (!{void*} (LocInfoE loc_58 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_59 (use{it_layout size_t} (LocInfoE loc_60 ("i")))))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "key"))) ;
        LocInfoE loc_61 (use{void*} (LocInfoE loc_62 ((LocInfoE loc_63 ((LocInfoE loc_64 ((LocInfoE loc_66 ((LocInfoE loc_69 (!{void*} (LocInfoE loc_70 ((LocInfoE loc_71 (!{void*} (LocInfoE loc_72 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_73 (use{it_layout size_t} (LocInfoE loc_74 ("i")))))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "value"))) ])) ;
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
  Definition impl_fsm_init (global_alloc_array : loc): function := {|
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
        "storage" <-{ void* }
          LocInfoE loc_219 (Call (LocInfoE loc_221 (global_alloc_array)) [@{expr} LocInfoE loc_222 (i2v (layout_of struct_item).(ly_size) size_t) ;
          LocInfoE loc_223 (use{it_layout size_t} (LocInfoE loc_224 ("len"))) ]) ;
        locinfo: loc_154 ;
        LocInfoE loc_214 ((LocInfoE loc_215 (!{void*} (LocInfoE loc_216 ("m")))) at{struct_fixed_size_map} "length") <-{ it_layout size_t }
          LocInfoE loc_217 (use{it_layout size_t} (LocInfoE loc_218 ("len"))) ;
        locinfo: loc_155 ;
        LocInfoE loc_209 ((LocInfoE loc_210 (!{void*} (LocInfoE loc_211 ("m")))) at{struct_fixed_size_map} "items") <-{ void* }
          LocInfoE loc_212 (use{void*} (LocInfoE loc_213 ("storage"))) ;
        locinfo: loc_156 ;
        LocInfoE loc_204 ((LocInfoE loc_205 (!{void*} (LocInfoE loc_206 ("m")))) at{struct_fixed_size_map} "count") <-{ it_layout size_t }
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
        LocInfoE loc_184 ((LocInfoE loc_186 ((LocInfoE loc_189 (!{void*} (LocInfoE loc_190 ((LocInfoE loc_191 (!{void*} (LocInfoE loc_192 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_193 (use{it_layout size_t} (LocInfoE loc_194 ("i")))))) at{struct_item} "tag") <-{ it_layout size_t }
          LocInfoE loc_195 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_196 (i2v 0 i32))) ;
        locinfo: loc_162 ;
        LocInfoE loc_170 ((LocInfoE loc_171 ((LocInfoE loc_172 ((LocInfoE loc_174 ((LocInfoE loc_177 (!{void*} (LocInfoE loc_178 ((LocInfoE loc_179 (!{void*} (LocInfoE loc_180 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_181 (use{it_layout size_t} (LocInfoE loc_182 ("i")))))) at{struct_item} "u")) at_union{union_item_union} "empty")) at{struct_empty} "dummy") <-{ it_layout size_t }
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
        "slot_idx" <-{ it_layout size_t }
          LocInfoE loc_357 (Call (LocInfoE loc_359 (global_fsm_slot_for_key)) [@{expr} LocInfoE loc_360 (use{it_layout size_t} (LocInfoE loc_361 ((LocInfoE loc_362 (!{void*} (LocInfoE loc_363 ("m")))) at{struct_fixed_size_map} "length"))) ;
          LocInfoE loc_364 (use{it_layout size_t} (LocInfoE loc_365 ("key"))) ]) ;
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
        if: LocInfoE loc_324 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_324 ((LocInfoE loc_325 (use{it_layout size_t} (LocInfoE loc_326 ((LocInfoE loc_328 ((LocInfoE loc_331 (!{void*} (LocInfoE loc_332 ((LocInfoE loc_333 (!{void*} (LocInfoE loc_334 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_335 (use{it_layout size_t} (LocInfoE loc_336 ("slot_idx")))))) at{struct_item} "tag")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_337 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_338 (i2v 2 i32)))))))
        then
        Goto "#12"
        else
        locinfo: loc_270 ;
          Goto "#10"
      ]> $
      <[ "#12" :=
        locinfo: loc_339 ;
        if: LocInfoE loc_339 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_339 ((LocInfoE loc_340 (use{it_layout size_t} (LocInfoE loc_341 ((LocInfoE loc_342 ((LocInfoE loc_343 ((LocInfoE loc_345 ((LocInfoE loc_348 (!{void*} (LocInfoE loc_349 ((LocInfoE loc_350 (!{void*} (LocInfoE loc_351 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_352 (use{it_layout size_t} (LocInfoE loc_353 ("slot_idx")))))) at{struct_item} "u")) at_union{union_item_union} "tombstone")) at{struct_tombstone} "key")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_354 (use{it_layout size_t} (LocInfoE loc_355 ("key")))))))
        then
        locinfo: loc_303 ;
          Goto "#9"
        else
        locinfo: loc_270 ;
          Goto "#10"
      ]> $
      <[ "#2" :=
        locinfo: loc_308 ;
        if: LocInfoE loc_308 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_308 ((LocInfoE loc_309 (use{it_layout size_t} (LocInfoE loc_310 ((LocInfoE loc_312 ((LocInfoE loc_315 (!{void*} (LocInfoE loc_316 ((LocInfoE loc_317 (!{void*} (LocInfoE loc_318 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_319 (use{it_layout size_t} (LocInfoE loc_320 ("slot_idx")))))) at{struct_item} "tag")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_321 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_322 (i2v 0 i32)))))))
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
        if: LocInfoE loc_270 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_270 ((LocInfoE loc_271 (use{it_layout size_t} (LocInfoE loc_272 ((LocInfoE loc_274 ((LocInfoE loc_277 (!{void*} (LocInfoE loc_278 ((LocInfoE loc_279 (!{void*} (LocInfoE loc_280 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_281 (use{it_layout size_t} (LocInfoE loc_282 ("slot_idx")))))) at{struct_item} "tag")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_283 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_284 (i2v 1 i32)))))))
        then
        Goto "#8"
        else
        locinfo: loc_243 ;
          Goto "#7"
      ]> $
      <[ "#5" :=
        locinfo: loc_243 ;
        expr: (LocInfoE loc_258 ((LocInfoE loc_259 (use{it_layout size_t} (LocInfoE loc_260 ((LocInfoE loc_261 (!{void*} (LocInfoE loc_262 ("m")))) at{struct_fixed_size_map} "length")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_263 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_263 (i2v 0 i32)))))) ;
        locinfo: loc_245 ;
        LocInfoE loc_248 ("slot_idx") <-{ it_layout size_t }
          LocInfoE loc_249 ((LocInfoE loc_250 ((LocInfoE loc_251 (use{it_layout size_t} (LocInfoE loc_252 ("slot_idx")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_253 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_253 (i2v 1 i32)))))) %{IntOp size_t, IntOp size_t} (LocInfoE loc_254 (use{it_layout size_t} (LocInfoE loc_255 ((LocInfoE loc_256 (!{void*} (LocInfoE loc_257 ("m")))) at{struct_fixed_size_map} "length"))))) ;
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
        if: LocInfoE loc_285 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_285 ((LocInfoE loc_286 (use{it_layout size_t} (LocInfoE loc_287 ((LocInfoE loc_288 ((LocInfoE loc_289 ((LocInfoE loc_291 ((LocInfoE loc_294 (!{void*} (LocInfoE loc_295 ((LocInfoE loc_296 (!{void*} (LocInfoE loc_297 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_298 (use{it_layout size_t} (LocInfoE loc_299 ("slot_idx")))))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "key")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_300 (use{it_layout size_t} (LocInfoE loc_301 ("key")))))))
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
        locinfo: loc_370 ;
        expr: (LocInfoE loc_370 (Call (LocInfoE loc_462 (global_fsm_realloc_if_necessary)) [@{expr} LocInfoE loc_463 (use{void*} (LocInfoE loc_464 ("m"))) ])) ;
        "slot_idx" <-{ it_layout size_t }
          LocInfoE loc_452 (Call (LocInfoE loc_454 (global_fsm_probe)) [@{expr} LocInfoE loc_455 (use{void*} (LocInfoE loc_456 ("m"))) ;
          LocInfoE loc_457 (use{it_layout size_t} (LocInfoE loc_458 ("key"))) ]) ;
        "replaced" <-{ void* } LocInfoE loc_449 (NULL) ;
        "item" <-{ void* }
          LocInfoE loc_436 (&(LocInfoE loc_438 ((LocInfoE loc_441 (!{void*} (LocInfoE loc_442 ((LocInfoE loc_443 (!{void*} (LocInfoE loc_444 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_445 (use{it_layout size_t} (LocInfoE loc_446 ("slot_idx"))))))) ;
        locinfo: loc_429 ;
        if: LocInfoE loc_429 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_429 ((LocInfoE loc_430 (use{it_layout size_t} (LocInfoE loc_431 ((LocInfoE loc_432 (!{void*} (LocInfoE loc_433 ("item")))) at{struct_item} "tag")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_434 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_435 (i2v 1 i32)))))))
        then
        locinfo: loc_401 ;
          Goto "#2"
        else
        locinfo: loc_422 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_375 ;
        LocInfoE loc_395 ((LocInfoE loc_396 (!{void*} (LocInfoE loc_397 ("item")))) at{struct_item} "tag") <-{ it_layout size_t }
          LocInfoE loc_398 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_399 (i2v 1 i32))) ;
        locinfo: loc_376 ;
        LocInfoE loc_388 ((LocInfoE loc_389 ((LocInfoE loc_390 ((LocInfoE loc_391 (!{void*} (LocInfoE loc_392 ("item")))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "key") <-{ it_layout size_t }
          LocInfoE loc_393 (use{it_layout size_t} (LocInfoE loc_394 ("key"))) ;
        locinfo: loc_377 ;
        LocInfoE loc_381 ((LocInfoE loc_382 ((LocInfoE loc_383 ((LocInfoE loc_384 (!{void*} (LocInfoE loc_385 ("item")))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "value") <-{ void* }
          LocInfoE loc_386 (use{void*} (LocInfoE loc_387 ("value"))) ;
        locinfo: loc_378 ;
        Return (LocInfoE loc_379 (use{void*} (LocInfoE loc_380 ("replaced"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_401 ;
        LocInfoE loc_402 ("replaced") <-{ void* }
          LocInfoE loc_403 (use{void*} (LocInfoE loc_404 ((LocInfoE loc_405 ((LocInfoE loc_406 ((LocInfoE loc_407 (!{void*} (LocInfoE loc_408 ("item")))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "value"))) ;
        locinfo: loc_375 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_422 ;
        if: LocInfoE loc_422 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_422 ((LocInfoE loc_423 (use{it_layout size_t} (LocInfoE loc_424 ((LocInfoE loc_425 (!{void*} (LocInfoE loc_426 ("item")))) at{struct_item} "tag")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_427 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_428 (i2v 0 i32)))))))
        then
        locinfo: loc_411 ;
          Goto "#4"
        else
        locinfo: loc_375 ;
          Goto "#5"
      ]> $
      <[ "#4" :=
        locinfo: loc_411 ;
        LocInfoE loc_412 ((LocInfoE loc_413 (!{void*} (LocInfoE loc_414 ("m")))) at{struct_fixed_size_map} "count") <-{ it_layout size_t }
          LocInfoE loc_415 ((LocInfoE loc_416 (use{it_layout size_t} (LocInfoE loc_417 ((LocInfoE loc_418 (!{void*} (LocInfoE loc_419 ("m")))) at{struct_fixed_size_map} "count")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_420 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_420 (i2v 1 i32))))) ;
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
        "slot_idx" <-{ it_layout size_t }
          LocInfoE loc_503 (Call (LocInfoE loc_505 (global_fsm_probe)) [@{expr} LocInfoE loc_506 (use{void*} (LocInfoE loc_507 ("m"))) ;
          LocInfoE loc_508 (use{it_layout size_t} (LocInfoE loc_509 ("key"))) ]) ;
        "item" <-{ void* }
          LocInfoE loc_490 (&(LocInfoE loc_492 ((LocInfoE loc_495 (!{void*} (LocInfoE loc_496 ((LocInfoE loc_497 (!{void*} (LocInfoE loc_498 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_499 (use{it_layout size_t} (LocInfoE loc_500 ("slot_idx"))))))) ;
        locinfo: loc_483 ;
        if: LocInfoE loc_483 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_483 ((LocInfoE loc_484 (use{it_layout size_t} (LocInfoE loc_485 ((LocInfoE loc_486 (!{void*} (LocInfoE loc_487 ("item")))) at{struct_item} "tag")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_488 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_489 (i2v 1 i32)))))))
        then
        locinfo: loc_471 ;
          Goto "#1"
        else
        locinfo: loc_481 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_471 ;
        Return (LocInfoE loc_472 (&(LocInfoE loc_474 (!{void*} (LocInfoE loc_475 ((LocInfoE loc_476 ((LocInfoE loc_477 ((LocInfoE loc_478 (!{void*} (LocInfoE loc_479 ("item")))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "value"))))))
      ]> $
      <[ "#2" :=
        locinfo: loc_481 ;
        Return (LocInfoE loc_482 (NULL))
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
        "slot_idx" <-{ it_layout size_t }
          LocInfoE loc_566 (Call (LocInfoE loc_568 (global_fsm_probe)) [@{expr} LocInfoE loc_569 (use{void*} (LocInfoE loc_570 ("m"))) ;
          LocInfoE loc_571 (use{it_layout size_t} (LocInfoE loc_572 ("key"))) ]) ;
        "item" <-{ void* }
          LocInfoE loc_553 (&(LocInfoE loc_555 ((LocInfoE loc_558 (!{void*} (LocInfoE loc_559 ((LocInfoE loc_560 (!{void*} (LocInfoE loc_561 ("m")))) at{struct_fixed_size_map} "items")))) at_offset{layout_of struct_item, PtrOp, IntOp size_t} (LocInfoE loc_562 (use{it_layout size_t} (LocInfoE loc_563 ("slot_idx"))))))) ;
        locinfo: loc_546 ;
        if: LocInfoE loc_546 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_546 ((LocInfoE loc_547 (use{it_layout size_t} (LocInfoE loc_548 ((LocInfoE loc_549 (!{void*} (LocInfoE loc_550 ("item")))) at{struct_item} "tag")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_551 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_552 (i2v 1 i32)))))))
        then
        locinfo: loc_518 ;
          Goto "#1"
        else
        locinfo: loc_544 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_518 ;
        LocInfoE loc_536 ("removed") <-{ void* }
          LocInfoE loc_537 (use{void*} (LocInfoE loc_538 ((LocInfoE loc_539 ((LocInfoE loc_540 ((LocInfoE loc_541 (!{void*} (LocInfoE loc_542 ("item")))) at{struct_item} "u")) at_union{union_item_union} "entry")) at{struct_entry} "value"))) ;
        locinfo: loc_519 ;
        LocInfoE loc_531 ((LocInfoE loc_532 (!{void*} (LocInfoE loc_533 ("item")))) at{struct_item} "tag") <-{ it_layout size_t }
          LocInfoE loc_534 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_535 (i2v 2 i32))) ;
        locinfo: loc_520 ;
        LocInfoE loc_524 ((LocInfoE loc_525 ((LocInfoE loc_526 ((LocInfoE loc_527 (!{void*} (LocInfoE loc_528 ("item")))) at{struct_item} "u")) at_union{union_item_union} "tombstone")) at{struct_tombstone} "key") <-{ it_layout size_t }
          LocInfoE loc_529 (use{it_layout size_t} (LocInfoE loc_530 ("key"))) ;
        locinfo: loc_521 ;
        Return (LocInfoE loc_522 (use{void*} (LocInfoE loc_523 ("removed"))))
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
