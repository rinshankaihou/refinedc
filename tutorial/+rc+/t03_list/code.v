From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/t03_list.c]. *)
Section code.
  Definition file_0 : string := "tutorial/t03_list.c".
  Definition loc_2 : location_info := LocationInfo file_0 124 4 124 25.
  Definition loc_3 : location_info := LocationInfo file_0 125 4 125 42.
  Definition loc_4 : location_info := LocationInfo file_0 126 4 126 42.
  Definition loc_5 : location_info := LocationInfo file_0 127 4 127 42.
  Definition loc_6 : location_info := LocationInfo file_0 129 4 129 28.
  Definition loc_7 : location_info := LocationInfo file_0 131 4 131 15.
  Definition loc_8 : location_info := LocationInfo file_0 132 4 132 15.
  Definition loc_9 : location_info := LocationInfo file_0 133 4 133 15.
  Definition loc_10 : location_info := LocationInfo file_0 135 4 135 29.
  Definition loc_11 : location_info := LocationInfo file_0 136 4 136 29.
  Definition loc_12 : location_info := LocationInfo file_0 137 4 137 29.
  Definition loc_13 : location_info := LocationInfo file_0 139 4 139 29.
  Definition loc_14 : location_info := LocationInfo file_0 141 4 141 25.
  Definition loc_15 : location_info := LocationInfo file_0 143 4 143 29.
  Definition loc_16 : location_info := LocationInfo file_0 145 4 145 23.
  Definition loc_17 : location_info := LocationInfo file_0 146 4 146 23.
  Definition loc_18 : location_info := LocationInfo file_0 147 4 147 23.
  Definition loc_19 : location_info := LocationInfo file_0 149 4 149 28.
  Definition loc_20 : location_info := LocationInfo file_0 151 4 151 32.
  Definition loc_21 : location_info := LocationInfo file_0 152 4 152 32.
  Definition loc_22 : location_info := LocationInfo file_0 153 4 153 32.
  Definition loc_23 : location_info := LocationInfo file_0 155 4 155 32.
  Definition loc_24 : location_info := LocationInfo file_0 156 4 156 32.
  Definition loc_25 : location_info := LocationInfo file_0 157 4 157 32.
  Definition loc_26 : location_info := LocationInfo file_0 157 4 157 8.
  Definition loc_27 : location_info := LocationInfo file_0 157 4 157 8.
  Definition loc_28 : location_info := LocationInfo file_0 157 9 157 23.
  Definition loc_29 : location_info := LocationInfo file_0 157 25 157 30.
  Definition loc_30 : location_info := LocationInfo file_0 157 25 157 30.
  Definition loc_31 : location_info := LocationInfo file_0 156 4 156 8.
  Definition loc_32 : location_info := LocationInfo file_0 156 4 156 8.
  Definition loc_33 : location_info := LocationInfo file_0 156 9 156 23.
  Definition loc_34 : location_info := LocationInfo file_0 156 25 156 30.
  Definition loc_35 : location_info := LocationInfo file_0 156 25 156 30.
  Definition loc_36 : location_info := LocationInfo file_0 155 4 155 8.
  Definition loc_37 : location_info := LocationInfo file_0 155 4 155 8.
  Definition loc_38 : location_info := LocationInfo file_0 155 9 155 23.
  Definition loc_39 : location_info := LocationInfo file_0 155 25 155 30.
  Definition loc_40 : location_info := LocationInfo file_0 155 25 155 30.
  Definition loc_41 : location_info := LocationInfo file_0 153 11 153 30.
  Definition loc_42 : location_info := LocationInfo file_0 153 11 153 17.
  Definition loc_43 : location_info := LocationInfo file_0 153 11 153 17.
  Definition loc_44 : location_info := LocationInfo file_0 153 12 153 17.
  Definition loc_45 : location_info := LocationInfo file_0 153 12 153 17.
  Definition loc_46 : location_info := LocationInfo file_0 153 21 153 30.
  Definition loc_47 : location_info := LocationInfo file_0 153 29 153 30.
  Definition loc_48 : location_info := LocationInfo file_0 152 11 152 30.
  Definition loc_49 : location_info := LocationInfo file_0 152 11 152 17.
  Definition loc_50 : location_info := LocationInfo file_0 152 11 152 17.
  Definition loc_51 : location_info := LocationInfo file_0 152 12 152 17.
  Definition loc_52 : location_info := LocationInfo file_0 152 12 152 17.
  Definition loc_53 : location_info := LocationInfo file_0 152 21 152 30.
  Definition loc_54 : location_info := LocationInfo file_0 152 29 152 30.
  Definition loc_55 : location_info := LocationInfo file_0 151 11 151 30.
  Definition loc_56 : location_info := LocationInfo file_0 151 11 151 17.
  Definition loc_57 : location_info := LocationInfo file_0 151 11 151 17.
  Definition loc_58 : location_info := LocationInfo file_0 151 12 151 17.
  Definition loc_59 : location_info := LocationInfo file_0 151 12 151 17.
  Definition loc_60 : location_info := LocationInfo file_0 151 21 151 30.
  Definition loc_61 : location_info := LocationInfo file_0 151 29 151 30.
  Definition loc_62 : location_info := LocationInfo file_0 149 11 149 26.
  Definition loc_63 : location_info := LocationInfo file_0 149 11 149 19.
  Definition loc_64 : location_info := LocationInfo file_0 149 11 149 19.
  Definition loc_65 : location_info := LocationInfo file_0 149 20 149 25.
  Definition loc_66 : location_info := LocationInfo file_0 149 21 149 25.
  Definition loc_67 : location_info := LocationInfo file_0 147 4 147 9.
  Definition loc_68 : location_info := LocationInfo file_0 147 12 147 22.
  Definition loc_69 : location_info := LocationInfo file_0 147 12 147 15.
  Definition loc_70 : location_info := LocationInfo file_0 147 12 147 15.
  Definition loc_71 : location_info := LocationInfo file_0 147 16 147 21.
  Definition loc_72 : location_info := LocationInfo file_0 147 17 147 21.
  Definition loc_73 : location_info := LocationInfo file_0 146 4 146 9.
  Definition loc_74 : location_info := LocationInfo file_0 146 12 146 22.
  Definition loc_75 : location_info := LocationInfo file_0 146 12 146 15.
  Definition loc_76 : location_info := LocationInfo file_0 146 12 146 15.
  Definition loc_77 : location_info := LocationInfo file_0 146 16 146 21.
  Definition loc_78 : location_info := LocationInfo file_0 146 17 146 21.
  Definition loc_79 : location_info := LocationInfo file_0 145 4 145 9.
  Definition loc_80 : location_info := LocationInfo file_0 145 12 145 22.
  Definition loc_81 : location_info := LocationInfo file_0 145 12 145 15.
  Definition loc_82 : location_info := LocationInfo file_0 145 12 145 15.
  Definition loc_83 : location_info := LocationInfo file_0 145 16 145 21.
  Definition loc_84 : location_info := LocationInfo file_0 145 17 145 21.
  Definition loc_85 : location_info := LocationInfo file_0 143 11 143 27.
  Definition loc_86 : location_info := LocationInfo file_0 143 11 143 17.
  Definition loc_87 : location_info := LocationInfo file_0 143 11 143 17.
  Definition loc_88 : location_info := LocationInfo file_0 143 18 143 23.
  Definition loc_89 : location_info := LocationInfo file_0 143 19 143 23.
  Definition loc_90 : location_info := LocationInfo file_0 143 25 143 26.
  Definition loc_91 : location_info := LocationInfo file_0 141 4 141 8.
  Definition loc_92 : location_info := LocationInfo file_0 141 11 141 24.
  Definition loc_93 : location_info := LocationInfo file_0 141 11 141 18.
  Definition loc_94 : location_info := LocationInfo file_0 141 11 141 18.
  Definition loc_95 : location_info := LocationInfo file_0 141 19 141 23.
  Definition loc_96 : location_info := LocationInfo file_0 141 19 141 23.
  Definition loc_97 : location_info := LocationInfo file_0 139 11 139 27.
  Definition loc_98 : location_info := LocationInfo file_0 139 11 139 17.
  Definition loc_99 : location_info := LocationInfo file_0 139 11 139 17.
  Definition loc_100 : location_info := LocationInfo file_0 139 18 139 23.
  Definition loc_101 : location_info := LocationInfo file_0 139 19 139 23.
  Definition loc_102 : location_info := LocationInfo file_0 139 25 139 26.
  Definition loc_103 : location_info := LocationInfo file_0 137 4 137 8.
  Definition loc_104 : location_info := LocationInfo file_0 137 11 137 28.
  Definition loc_105 : location_info := LocationInfo file_0 137 11 137 15.
  Definition loc_106 : location_info := LocationInfo file_0 137 11 137 15.
  Definition loc_107 : location_info := LocationInfo file_0 137 16 137 20.
  Definition loc_108 : location_info := LocationInfo file_0 137 16 137 20.
  Definition loc_109 : location_info := LocationInfo file_0 137 22 137 27.
  Definition loc_110 : location_info := LocationInfo file_0 137 22 137 27.
  Definition loc_111 : location_info := LocationInfo file_0 136 4 136 8.
  Definition loc_112 : location_info := LocationInfo file_0 136 11 136 28.
  Definition loc_113 : location_info := LocationInfo file_0 136 11 136 15.
  Definition loc_114 : location_info := LocationInfo file_0 136 11 136 15.
  Definition loc_115 : location_info := LocationInfo file_0 136 16 136 20.
  Definition loc_116 : location_info := LocationInfo file_0 136 16 136 20.
  Definition loc_117 : location_info := LocationInfo file_0 136 22 136 27.
  Definition loc_118 : location_info := LocationInfo file_0 136 22 136 27.
  Definition loc_119 : location_info := LocationInfo file_0 135 4 135 8.
  Definition loc_120 : location_info := LocationInfo file_0 135 11 135 28.
  Definition loc_121 : location_info := LocationInfo file_0 135 11 135 15.
  Definition loc_122 : location_info := LocationInfo file_0 135 11 135 15.
  Definition loc_123 : location_info := LocationInfo file_0 135 16 135 20.
  Definition loc_124 : location_info := LocationInfo file_0 135 16 135 20.
  Definition loc_125 : location_info := LocationInfo file_0 135 22 135 27.
  Definition loc_126 : location_info := LocationInfo file_0 135 22 135 27.
  Definition loc_127 : location_info := LocationInfo file_0 133 4 133 10.
  Definition loc_128 : location_info := LocationInfo file_0 133 5 133 10.
  Definition loc_129 : location_info := LocationInfo file_0 133 5 133 10.
  Definition loc_130 : location_info := LocationInfo file_0 133 13 133 14.
  Definition loc_131 : location_info := LocationInfo file_0 132 4 132 10.
  Definition loc_132 : location_info := LocationInfo file_0 132 5 132 10.
  Definition loc_133 : location_info := LocationInfo file_0 132 5 132 10.
  Definition loc_134 : location_info := LocationInfo file_0 132 13 132 14.
  Definition loc_135 : location_info := LocationInfo file_0 131 4 131 10.
  Definition loc_136 : location_info := LocationInfo file_0 131 5 131 10.
  Definition loc_137 : location_info := LocationInfo file_0 131 5 131 10.
  Definition loc_138 : location_info := LocationInfo file_0 131 13 131 14.
  Definition loc_139 : location_info := LocationInfo file_0 129 11 129 26.
  Definition loc_140 : location_info := LocationInfo file_0 129 11 129 19.
  Definition loc_141 : location_info := LocationInfo file_0 129 11 129 19.
  Definition loc_142 : location_info := LocationInfo file_0 129 20 129 25.
  Definition loc_143 : location_info := LocationInfo file_0 129 21 129 25.
  Definition loc_144 : location_info := LocationInfo file_0 127 20 127 41.
  Definition loc_145 : location_info := LocationInfo file_0 127 20 127 25.
  Definition loc_146 : location_info := LocationInfo file_0 127 20 127 25.
  Definition loc_147 : location_info := LocationInfo file_0 127 26 127 40.
  Definition loc_150 : location_info := LocationInfo file_0 126 20 126 41.
  Definition loc_151 : location_info := LocationInfo file_0 126 20 126 25.
  Definition loc_152 : location_info := LocationInfo file_0 126 20 126 25.
  Definition loc_153 : location_info := LocationInfo file_0 126 26 126 40.
  Definition loc_156 : location_info := LocationInfo file_0 125 20 125 41.
  Definition loc_157 : location_info := LocationInfo file_0 125 20 125 25.
  Definition loc_158 : location_info := LocationInfo file_0 125 20 125 25.
  Definition loc_159 : location_info := LocationInfo file_0 125 26 125 40.
  Definition loc_162 : location_info := LocationInfo file_0 124 18 124 24.
  Definition loc_163 : location_info := LocationInfo file_0 124 18 124 22.
  Definition loc_164 : location_info := LocationInfo file_0 124 18 124 22.
  Definition loc_169 : location_info := LocationInfo file_0 27 4 27 26.
  Definition loc_170 : location_info := LocationInfo file_0 27 11 27 25.
  Definition loc_173 : location_info := LocationInfo file_0 35 4 35 32.
  Definition loc_174 : location_info := LocationInfo file_0 35 11 35 31.
  Definition loc_175 : location_info := LocationInfo file_0 35 11 35 13.
  Definition loc_176 : location_info := LocationInfo file_0 35 11 35 13.
  Definition loc_177 : location_info := LocationInfo file_0 35 12 35 13.
  Definition loc_178 : location_info := LocationInfo file_0 35 12 35 13.
  Definition loc_179 : location_info := LocationInfo file_0 35 17 35 31.
  Definition loc_182 : location_info := LocationInfo file_0 43 4 43 51.
  Definition loc_183 : location_info := LocationInfo file_0 44 4 44 19.
  Definition loc_184 : location_info := LocationInfo file_0 45 4 45 19.
  Definition loc_185 : location_info := LocationInfo file_0 46 4 46 16.
  Definition loc_186 : location_info := LocationInfo file_0 46 11 46 15.
  Definition loc_187 : location_info := LocationInfo file_0 46 11 46 15.
  Definition loc_188 : location_info := LocationInfo file_0 45 4 45 14.
  Definition loc_189 : location_info := LocationInfo file_0 45 4 45 8.
  Definition loc_190 : location_info := LocationInfo file_0 45 4 45 8.
  Definition loc_191 : location_info := LocationInfo file_0 45 17 45 18.
  Definition loc_192 : location_info := LocationInfo file_0 45 17 45 18.
  Definition loc_193 : location_info := LocationInfo file_0 44 4 44 14.
  Definition loc_194 : location_info := LocationInfo file_0 44 4 44 8.
  Definition loc_195 : location_info := LocationInfo file_0 44 4 44 8.
  Definition loc_196 : location_info := LocationInfo file_0 44 17 44 18.
  Definition loc_197 : location_info := LocationInfo file_0 44 17 44 18.
  Definition loc_198 : location_info := LocationInfo file_0 43 24 43 50.
  Definition loc_199 : location_info := LocationInfo file_0 43 24 43 29.
  Definition loc_200 : location_info := LocationInfo file_0 43 24 43 29.
  Definition loc_201 : location_info := LocationInfo file_0 43 30 43 49.
  Definition loc_206 : location_info := LocationInfo file_0 55 2 57 3.
  Definition loc_207 : location_info := LocationInfo file_0 58 2 58 25.
  Definition loc_208 : location_info := LocationInfo file_0 59 2 59 25.
  Definition loc_209 : location_info := LocationInfo file_0 60 2 60 18.
  Definition loc_210 : location_info := LocationInfo file_0 61 2 61 34.
  Definition loc_211 : location_info := LocationInfo file_0 62 2 62 13.
  Definition loc_212 : location_info := LocationInfo file_0 62 9 62 12.
  Definition loc_213 : location_info := LocationInfo file_0 62 9 62 12.
  Definition loc_214 : location_info := LocationInfo file_0 61 2 61 6.
  Definition loc_215 : location_info := LocationInfo file_0 61 2 61 6.
  Definition loc_216 : location_info := LocationInfo file_0 61 7 61 26.
  Definition loc_217 : location_info := LocationInfo file_0 61 28 61 32.
  Definition loc_218 : location_info := LocationInfo file_0 61 28 61 32.
  Definition loc_219 : location_info := LocationInfo file_0 60 2 60 4.
  Definition loc_220 : location_info := LocationInfo file_0 60 3 60 4.
  Definition loc_221 : location_info := LocationInfo file_0 60 3 60 4.
  Definition loc_222 : location_info := LocationInfo file_0 60 7 60 17.
  Definition loc_223 : location_info := LocationInfo file_0 60 7 60 17.
  Definition loc_224 : location_info := LocationInfo file_0 60 7 60 11.
  Definition loc_225 : location_info := LocationInfo file_0 60 7 60 11.
  Definition loc_226 : location_info := LocationInfo file_0 59 14 59 24.
  Definition loc_227 : location_info := LocationInfo file_0 59 14 59 24.
  Definition loc_228 : location_info := LocationInfo file_0 59 14 59 18.
  Definition loc_229 : location_info := LocationInfo file_0 59 14 59 18.
  Definition loc_232 : location_info := LocationInfo file_0 58 22 58 24.
  Definition loc_233 : location_info := LocationInfo file_0 58 22 58 24.
  Definition loc_234 : location_info := LocationInfo file_0 58 23 58 24.
  Definition loc_235 : location_info := LocationInfo file_0 58 23 58 24.
  Definition loc_238 : location_info := LocationInfo file_0 55 28 57 3.
  Definition loc_239 : location_info := LocationInfo file_0 56 6 56 28.
  Definition loc_240 : location_info := LocationInfo file_0 56 13 56 27.
  Definition loc_242 : location_info := LocationInfo file_0 55 6 55 26.
  Definition loc_243 : location_info := LocationInfo file_0 55 6 55 8.
  Definition loc_244 : location_info := LocationInfo file_0 55 6 55 8.
  Definition loc_245 : location_info := LocationInfo file_0 55 7 55 8.
  Definition loc_246 : location_info := LocationInfo file_0 55 7 55 8.
  Definition loc_247 : location_info := LocationInfo file_0 55 12 55 26.
  Definition loc_250 : location_info := LocationInfo file_0 70 4 70 23.
  Definition loc_251 : location_info := LocationInfo file_0 74 4 79 5.
  Definition loc_252 : location_info := LocationInfo file_0 80 4 80 13.
  Definition loc_253 : location_info := LocationInfo file_0 80 11 80 12.
  Definition loc_254 : location_info := LocationInfo file_0 80 11 80 12.
  Definition loc_255 : location_info := LocationInfo file_0 74 4 79 5.
  Definition loc_256 : location_info := LocationInfo file_0 74 32 79 5.
  Definition loc_257 : location_info := LocationInfo file_0 75 8 75 20.
  Definition loc_258 : location_info := LocationInfo file_0 76 8 76 20.
  Definition loc_259 : location_info := LocationInfo file_0 77 8 77 14.
  Definition loc_260 : location_info := LocationInfo file_0 78 8 78 14.
  Definition loc_261 : location_info := LocationInfo file_0 74 4 79 5.
  Definition loc_262 : location_info := LocationInfo file_0 74 4 79 5.
  Definition loc_263 : location_info := LocationInfo file_0 78 8 78 9.
  Definition loc_264 : location_info := LocationInfo file_0 78 12 78 13.
  Definition loc_265 : location_info := LocationInfo file_0 78 12 78 13.
  Definition loc_266 : location_info := LocationInfo file_0 77 8 77 9.
  Definition loc_267 : location_info := LocationInfo file_0 77 12 77 13.
  Definition loc_268 : location_info := LocationInfo file_0 77 12 77 13.
  Definition loc_269 : location_info := LocationInfo file_0 76 8 76 15.
  Definition loc_270 : location_info := LocationInfo file_0 76 8 76 9.
  Definition loc_271 : location_info := LocationInfo file_0 76 8 76 9.
  Definition loc_272 : location_info := LocationInfo file_0 76 18 76 19.
  Definition loc_273 : location_info := LocationInfo file_0 76 18 76 19.
  Definition loc_274 : location_info := LocationInfo file_0 75 8 75 9.
  Definition loc_275 : location_info := LocationInfo file_0 75 12 75 19.
  Definition loc_276 : location_info := LocationInfo file_0 75 12 75 19.
  Definition loc_277 : location_info := LocationInfo file_0 75 12 75 13.
  Definition loc_278 : location_info := LocationInfo file_0 75 12 75 13.
  Definition loc_279 : location_info := LocationInfo file_0 74 11 74 30.
  Definition loc_280 : location_info := LocationInfo file_0 74 11 74 12.
  Definition loc_281 : location_info := LocationInfo file_0 74 11 74 12.
  Definition loc_282 : location_info := LocationInfo file_0 74 16 74 30.
  Definition loc_283 : location_info := LocationInfo file_0 70 4 70 5.
  Definition loc_284 : location_info := LocationInfo file_0 70 8 70 22.
  Definition loc_287 : location_info := LocationInfo file_0 87 2 87 19.
  Definition loc_288 : location_info := LocationInfo file_0 91 2 93 3.
  Definition loc_289 : location_info := LocationInfo file_0 94 2 94 12.
  Definition loc_290 : location_info := LocationInfo file_0 94 2 94 6.
  Definition loc_291 : location_info := LocationInfo file_0 94 3 94 6.
  Definition loc_292 : location_info := LocationInfo file_0 94 3 94 6.
  Definition loc_293 : location_info := LocationInfo file_0 94 9 94 11.
  Definition loc_294 : location_info := LocationInfo file_0 94 9 94 11.
  Definition loc_295 : location_info := LocationInfo file_0 91 2 93 3.
  Definition loc_296 : location_info := LocationInfo file_0 91 31 93 3.
  Definition loc_297 : location_info := LocationInfo file_0 92 4 92 26.
  Definition loc_298 : location_info := LocationInfo file_0 91 2 93 3.
  Definition loc_299 : location_info := LocationInfo file_0 91 2 93 3.
  Definition loc_300 : location_info := LocationInfo file_0 92 4 92 7.
  Definition loc_301 : location_info := LocationInfo file_0 92 10 92 25.
  Definition loc_302 : location_info := LocationInfo file_0 92 11 92 25.
  Definition loc_303 : location_info := LocationInfo file_0 92 12 92 18.
  Definition loc_304 : location_info := LocationInfo file_0 92 12 92 18.
  Definition loc_305 : location_info := LocationInfo file_0 92 14 92 17.
  Definition loc_306 : location_info := LocationInfo file_0 92 14 92 17.
  Definition loc_307 : location_info := LocationInfo file_0 91 8 91 30.
  Definition loc_308 : location_info := LocationInfo file_0 91 8 91 12.
  Definition loc_309 : location_info := LocationInfo file_0 91 8 91 12.
  Definition loc_310 : location_info := LocationInfo file_0 91 9 91 12.
  Definition loc_311 : location_info := LocationInfo file_0 91 9 91 12.
  Definition loc_312 : location_info := LocationInfo file_0 91 16 91 30.
  Definition loc_313 : location_info := LocationInfo file_0 87 16 87 18.
  Definition loc_314 : location_info := LocationInfo file_0 87 16 87 18.
  Definition loc_319 : location_info := LocationInfo file_0 104 4 104 21.
  Definition loc_320 : location_info := LocationInfo file_0 109 4 118 5.
  Definition loc_321 : location_info := LocationInfo file_0 119 4 119 13.
  Definition loc_322 : location_info := LocationInfo file_0 119 11 119 12.
  Definition loc_323 : location_info := LocationInfo file_0 109 4 118 5.
  Definition loc_324 : location_info := LocationInfo file_0 109 35 118 5.
  Definition loc_325 : location_info := LocationInfo file_0 110 8 110 27.
  Definition loc_326 : location_info := LocationInfo file_0 112 8 112 33.
  Definition loc_327 : location_info := LocationInfo file_0 113 8 115 9.
  Definition loc_328 : location_info := LocationInfo file_0 117 8 117 26.
  Definition loc_329 : location_info := LocationInfo file_0 109 4 118 5.
  Definition loc_330 : location_info := LocationInfo file_0 109 4 118 5.
  Definition loc_331 : location_info := LocationInfo file_0 117 8 117 12.
  Definition loc_332 : location_info := LocationInfo file_0 117 15 117 25.
  Definition loc_333 : location_info := LocationInfo file_0 117 16 117 25.
  Definition loc_334 : location_info := LocationInfo file_0 117 16 117 19.
  Definition loc_335 : location_info := LocationInfo file_0 117 16 117 19.
  Definition loc_336 : location_info := LocationInfo file_0 113 23 115 9.
  Definition loc_337 : location_info := LocationInfo file_0 114 12 114 21.
  Definition loc_338 : location_info := LocationInfo file_0 114 19 114 20.
  Definition loc_340 : location_info := LocationInfo file_0 113 11 113 21.
  Definition loc_341 : location_info := LocationInfo file_0 113 11 113 16.
  Definition loc_342 : location_info := LocationInfo file_0 113 11 113 16.
  Definition loc_343 : location_info := LocationInfo file_0 113 12 113 16.
  Definition loc_344 : location_info := LocationInfo file_0 113 12 113 16.
  Definition loc_345 : location_info := LocationInfo file_0 113 20 113 21.
  Definition loc_346 : location_info := LocationInfo file_0 113 20 113 21.
  Definition loc_347 : location_info := LocationInfo file_0 112 23 112 32.
  Definition loc_348 : location_info := LocationInfo file_0 112 23 112 32.
  Definition loc_349 : location_info := LocationInfo file_0 112 23 112 26.
  Definition loc_350 : location_info := LocationInfo file_0 112 23 112 26.
  Definition loc_353 : location_info := LocationInfo file_0 110 21 110 26.
  Definition loc_354 : location_info := LocationInfo file_0 110 21 110 26.
  Definition loc_355 : location_info := LocationInfo file_0 110 22 110 26.
  Definition loc_356 : location_info := LocationInfo file_0 110 22 110 26.
  Definition loc_359 : location_info := LocationInfo file_0 109 10 109 33.
  Definition loc_360 : location_info := LocationInfo file_0 109 10 109 15.
  Definition loc_361 : location_info := LocationInfo file_0 109 10 109 15.
  Definition loc_362 : location_info := LocationInfo file_0 109 11 109 15.
  Definition loc_363 : location_info := LocationInfo file_0 109 11 109 15.
  Definition loc_364 : location_info := LocationInfo file_0 109 19 109 33.
  Definition loc_365 : location_info := LocationInfo file_0 104 19 104 20.
  Definition loc_366 : location_info := LocationInfo file_0 104 19 104 20.
  Definition loc_371 : location_info := LocationInfo file_0 164 2 164 18.
  Definition loc_372 : location_info := LocationInfo file_0 174 2 179 3.
  Definition loc_373 : location_info := LocationInfo file_0 174 2 179 3.
  Definition loc_374 : location_info := LocationInfo file_0 174 31 179 3.
  Definition loc_375 : location_info := LocationInfo file_0 175 4 175 25.
  Definition loc_376 : location_info := LocationInfo file_0 176 4 176 20.
  Definition loc_377 : location_info := LocationInfo file_0 177 4 177 14.
  Definition loc_378 : location_info := LocationInfo file_0 178 4 178 19.
  Definition loc_379 : location_info := LocationInfo file_0 174 2 179 3.
  Definition loc_380 : location_info := LocationInfo file_0 174 2 179 3.
  Definition loc_381 : location_info := LocationInfo file_0 178 4 178 7.
  Definition loc_382 : location_info := LocationInfo file_0 178 10 178 18.
  Definition loc_383 : location_info := LocationInfo file_0 178 10 178 18.
  Definition loc_384 : location_info := LocationInfo file_0 177 4 177 7.
  Definition loc_385 : location_info := LocationInfo file_0 177 5 177 7.
  Definition loc_386 : location_info := LocationInfo file_0 177 5 177 7.
  Definition loc_387 : location_info := LocationInfo file_0 177 10 177 13.
  Definition loc_388 : location_info := LocationInfo file_0 177 10 177 13.
  Definition loc_389 : location_info := LocationInfo file_0 176 4 176 13.
  Definition loc_390 : location_info := LocationInfo file_0 176 4 176 7.
  Definition loc_391 : location_info := LocationInfo file_0 176 4 176 7.
  Definition loc_392 : location_info := LocationInfo file_0 176 16 176 19.
  Definition loc_393 : location_info := LocationInfo file_0 176 16 176 19.
  Definition loc_394 : location_info := LocationInfo file_0 176 17 176 19.
  Definition loc_395 : location_info := LocationInfo file_0 176 17 176 19.
  Definition loc_396 : location_info := LocationInfo file_0 175 4 175 12.
  Definition loc_397 : location_info := LocationInfo file_0 175 15 175 24.
  Definition loc_398 : location_info := LocationInfo file_0 175 15 175 24.
  Definition loc_399 : location_info := LocationInfo file_0 175 15 175 18.
  Definition loc_400 : location_info := LocationInfo file_0 175 15 175 18.
  Definition loc_401 : location_info := LocationInfo file_0 174 8 174 29.
  Definition loc_402 : location_info := LocationInfo file_0 174 8 174 11.
  Definition loc_403 : location_info := LocationInfo file_0 174 8 174 11.
  Definition loc_404 : location_info := LocationInfo file_0 174 15 174 29.
  Definition loc_405 : location_info := LocationInfo file_0 164 15 164 17.
  Definition loc_406 : location_info := LocationInfo file_0 164 15 164 17.

  (* Definition of struct [list]. *)
  Program Definition struct_list := {|
    sl_members := [
      (Some "head", LPtr);
      (Some "tail", LPtr)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [test]. *)
  Definition impl_test (alloc free init is_empty push pop reverse member : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
      ("list", LPtr);
      ("elem2", LPtr);
      ("elem1", LPtr);
      ("elem3", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_162 ;
        "$14" <- LocInfoE loc_164 (init) with [  ] ;
        "list" <-{ LPtr } LocInfoE loc_162 ("$14") ;
        locinfo: loc_156 ;
        "$13" <- LocInfoE loc_158 (alloc) with
          [ LocInfoE loc_159 (i2v (it_layout size_t).(ly_size) size_t) ] ;
        "elem1" <-{ LPtr }
          LocInfoE loc_156 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_156 ("$13"))) ;
        locinfo: loc_150 ;
        "$12" <- LocInfoE loc_152 (alloc) with
          [ LocInfoE loc_153 (i2v (it_layout size_t).(ly_size) size_t) ] ;
        "elem2" <-{ LPtr }
          LocInfoE loc_150 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_150 ("$12"))) ;
        locinfo: loc_144 ;
        "$11" <- LocInfoE loc_146 (alloc) with
          [ LocInfoE loc_147 (i2v (it_layout size_t).(ly_size) size_t) ] ;
        "elem3" <-{ LPtr }
          LocInfoE loc_144 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_144 ("$11"))) ;
        locinfo: loc_139 ;
        "$10" <- LocInfoE loc_141 (is_empty) with
          [ LocInfoE loc_142 (&(LocInfoE loc_143 ("list"))) ] ;
        locinfo: loc_6 ;
        assert: (LocInfoE loc_139 ("$10")) ;
        locinfo: loc_7 ;
        LocInfoE loc_136 (!{LPtr} (LocInfoE loc_137 ("elem1"))) <-{ it_layout size_t }
          LocInfoE loc_138 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_138 (i2v 1 i32))) ;
        locinfo: loc_8 ;
        LocInfoE loc_132 (!{LPtr} (LocInfoE loc_133 ("elem2"))) <-{ it_layout size_t }
          LocInfoE loc_134 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_134 (i2v 2 i32))) ;
        locinfo: loc_9 ;
        LocInfoE loc_128 (!{LPtr} (LocInfoE loc_129 ("elem3"))) <-{ it_layout size_t }
          LocInfoE loc_130 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_130 (i2v 3 i32))) ;
        locinfo: loc_120 ;
        "$9" <- LocInfoE loc_122 (push) with
          [ LocInfoE loc_123 (use{LPtr} (LocInfoE loc_124 ("list"))) ;
          LocInfoE loc_125 (use{LPtr} (LocInfoE loc_126 ("elem1"))) ] ;
        locinfo: loc_10 ;
        LocInfoE loc_119 ("list") <-{ LPtr } LocInfoE loc_120 ("$9") ;
        locinfo: loc_112 ;
        "$8" <- LocInfoE loc_114 (push) with
          [ LocInfoE loc_115 (use{LPtr} (LocInfoE loc_116 ("list"))) ;
          LocInfoE loc_117 (use{LPtr} (LocInfoE loc_118 ("elem2"))) ] ;
        locinfo: loc_11 ;
        LocInfoE loc_111 ("list") <-{ LPtr } LocInfoE loc_112 ("$8") ;
        locinfo: loc_104 ;
        "$7" <- LocInfoE loc_106 (push) with
          [ LocInfoE loc_107 (use{LPtr} (LocInfoE loc_108 ("list"))) ;
          LocInfoE loc_109 (use{LPtr} (LocInfoE loc_110 ("elem3"))) ] ;
        locinfo: loc_12 ;
        LocInfoE loc_103 ("list") <-{ LPtr } LocInfoE loc_104 ("$7") ;
        locinfo: loc_97 ;
        "$6" <- LocInfoE loc_99 (member) with
          [ LocInfoE loc_100 (&(LocInfoE loc_101 ("list"))) ;
          LocInfoE loc_102 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_102 (i2v 1 i32))) ] ;
        locinfo: loc_13 ;
        assert: (LocInfoE loc_97 ("$6")) ;
        locinfo: loc_92 ;
        "$5" <- LocInfoE loc_94 (reverse) with
          [ LocInfoE loc_95 (use{LPtr} (LocInfoE loc_96 ("list"))) ] ;
        locinfo: loc_14 ;
        LocInfoE loc_91 ("list") <-{ LPtr } LocInfoE loc_92 ("$5") ;
        locinfo: loc_85 ;
        "$4" <- LocInfoE loc_87 (member) with
          [ LocInfoE loc_88 (&(LocInfoE loc_89 ("list"))) ;
          LocInfoE loc_90 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_90 (i2v 1 i32))) ] ;
        locinfo: loc_15 ;
        assert: (LocInfoE loc_85 ("$4")) ;
        locinfo: loc_80 ;
        "$3" <- LocInfoE loc_82 (pop) with
          [ LocInfoE loc_83 (&(LocInfoE loc_84 ("list"))) ] ;
        locinfo: loc_16 ;
        LocInfoE loc_79 ("elem1") <-{ LPtr } LocInfoE loc_80 ("$3") ;
        locinfo: loc_74 ;
        "$2" <- LocInfoE loc_76 (pop) with
          [ LocInfoE loc_77 (&(LocInfoE loc_78 ("list"))) ] ;
        locinfo: loc_17 ;
        LocInfoE loc_73 ("elem2") <-{ LPtr } LocInfoE loc_74 ("$2") ;
        locinfo: loc_68 ;
        "$1" <- LocInfoE loc_70 (pop) with
          [ LocInfoE loc_71 (&(LocInfoE loc_72 ("list"))) ] ;
        locinfo: loc_18 ;
        LocInfoE loc_67 ("elem3") <-{ LPtr } LocInfoE loc_68 ("$1") ;
        locinfo: loc_62 ;
        "$0" <- LocInfoE loc_64 (is_empty) with
          [ LocInfoE loc_65 (&(LocInfoE loc_66 ("list"))) ] ;
        locinfo: loc_19 ;
        assert: (LocInfoE loc_62 ("$0")) ;
        locinfo: loc_20 ;
        assert: (LocInfoE loc_55 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_55 ((LocInfoE loc_56 (use{it_layout size_t} (LocInfoE loc_58 (!{LPtr} (LocInfoE loc_59 ("elem1")))))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_60 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_61 (i2v 1 i32)))))))) ;
        locinfo: loc_21 ;
        assert: (LocInfoE loc_48 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_48 ((LocInfoE loc_49 (use{it_layout size_t} (LocInfoE loc_51 (!{LPtr} (LocInfoE loc_52 ("elem2")))))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_53 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_54 (i2v 2 i32)))))))) ;
        locinfo: loc_22 ;
        assert: (LocInfoE loc_41 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_41 ((LocInfoE loc_42 (use{it_layout size_t} (LocInfoE loc_44 (!{LPtr} (LocInfoE loc_45 ("elem3")))))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_46 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_47 (i2v 3 i32)))))))) ;
        locinfo: loc_23 ;
        "_" <- LocInfoE loc_37 (free) with
          [ LocInfoE loc_38 (i2v (it_layout size_t).(ly_size) size_t) ;
          LocInfoE loc_39 (use{LPtr} (LocInfoE loc_40 ("elem1"))) ] ;
        locinfo: loc_24 ;
        "_" <- LocInfoE loc_32 (free) with
          [ LocInfoE loc_33 (i2v (it_layout size_t).(ly_size) size_t) ;
          LocInfoE loc_34 (use{LPtr} (LocInfoE loc_35 ("elem2"))) ] ;
        locinfo: loc_25 ;
        "_" <- LocInfoE loc_27 (free) with
          [ LocInfoE loc_28 (i2v (it_layout size_t).(ly_size) size_t) ;
          LocInfoE loc_29 (use{LPtr} (LocInfoE loc_30 ("elem3"))) ] ;
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
        locinfo: loc_169 ;
        Return (LocInfoE loc_170 (NULL))
      ]> $∅
    )%E
  |}.

  (* Definition of function [is_empty]. *)
  Definition impl_is_empty : function := {|
    f_args := [
      ("l", LPtr)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_173 ;
        Return (LocInfoE loc_174 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_174 ((LocInfoE loc_175 (use{LPtr} (LocInfoE loc_177 (!{LPtr} (LocInfoE loc_178 ("l")))))) ={PtrOp, PtrOp} (LocInfoE loc_179 (NULL))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [push]. *)
  Definition impl_push (alloc : loc): function := {|
    f_args := [
      ("p", LPtr);
      ("e", LPtr)
    ];
    f_local_vars := [
      ("node", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_198 ;
        "$0" <- LocInfoE loc_200 (alloc) with
          [ LocInfoE loc_201 (i2v (layout_of struct_list).(ly_size) size_t) ] ;
        "node" <-{ LPtr }
          LocInfoE loc_198 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_198 ("$0"))) ;
        locinfo: loc_183 ;
        LocInfoE loc_193 ((LocInfoE loc_194 (!{LPtr} (LocInfoE loc_195 ("node")))) at{struct_list} "head") <-{ LPtr }
          LocInfoE loc_196 (use{LPtr} (LocInfoE loc_197 ("e"))) ;
        locinfo: loc_184 ;
        LocInfoE loc_188 ((LocInfoE loc_189 (!{LPtr} (LocInfoE loc_190 ("node")))) at{struct_list} "tail") <-{ LPtr }
          LocInfoE loc_191 (use{LPtr} (LocInfoE loc_192 ("p"))) ;
        locinfo: loc_185 ;
        Return (LocInfoE loc_186 (use{LPtr} (LocInfoE loc_187 ("node"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [pop]. *)
  Definition impl_pop (free : loc): function := {|
    f_args := [
      ("p", LPtr)
    ];
    f_local_vars := [
      ("node", LPtr);
      ("ret", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_242 ;
        if: LocInfoE loc_242 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_242 ((LocInfoE loc_243 (use{LPtr} (LocInfoE loc_245 (!{LPtr} (LocInfoE loc_246 ("p")))))) ={PtrOp, PtrOp} (LocInfoE loc_247 (NULL)))))
        then
        locinfo: loc_239 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#1" :=
        "node" <-{ LPtr }
          LocInfoE loc_232 (use{LPtr} (LocInfoE loc_234 (!{LPtr} (LocInfoE loc_235 ("p"))))) ;
        "ret" <-{ LPtr }
          LocInfoE loc_226 (use{LPtr} (LocInfoE loc_227 ((LocInfoE loc_228 (!{LPtr} (LocInfoE loc_229 ("node")))) at{struct_list} "head"))) ;
        locinfo: loc_209 ;
        LocInfoE loc_220 (!{LPtr} (LocInfoE loc_221 ("p"))) <-{ LPtr }
          LocInfoE loc_222 (use{LPtr} (LocInfoE loc_223 ((LocInfoE loc_224 (!{LPtr} (LocInfoE loc_225 ("node")))) at{struct_list} "tail"))) ;
        locinfo: loc_210 ;
        "_" <- LocInfoE loc_215 (free) with
          [ LocInfoE loc_216 (i2v (layout_of struct_list).(ly_size) size_t) ;
          LocInfoE loc_217 (use{LPtr} (LocInfoE loc_218 ("node"))) ] ;
        locinfo: loc_211 ;
        Return (LocInfoE loc_212 (use{LPtr} (LocInfoE loc_213 ("ret"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_239 ;
        Return (LocInfoE loc_240 (NULL))
      ]> $
      <[ "#3" :=
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [reverse]. *)
  Definition impl_reverse : function := {|
    f_args := [
      ("p", LPtr)
    ];
    f_local_vars := [
      ("w", LPtr);
      ("t", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_250 ;
        LocInfoE loc_283 ("w") <-{ LPtr } LocInfoE loc_284 (NULL) ;
        locinfo: loc_251 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_279 ;
        if: LocInfoE loc_279 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_279 ((LocInfoE loc_280 (use{LPtr} (LocInfoE loc_281 ("p")))) !={PtrOp, PtrOp} (LocInfoE loc_282 (NULL)))))
        then
        locinfo: loc_257 ;
          Goto "#2"
        else
        locinfo: loc_252 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_257 ;
        LocInfoE loc_274 ("t") <-{ LPtr }
          LocInfoE loc_275 (use{LPtr} (LocInfoE loc_276 ((LocInfoE loc_277 (!{LPtr} (LocInfoE loc_278 ("p")))) at{struct_list} "tail"))) ;
        locinfo: loc_258 ;
        LocInfoE loc_269 ((LocInfoE loc_270 (!{LPtr} (LocInfoE loc_271 ("p")))) at{struct_list} "tail") <-{ LPtr }
          LocInfoE loc_272 (use{LPtr} (LocInfoE loc_273 ("w"))) ;
        locinfo: loc_259 ;
        LocInfoE loc_266 ("w") <-{ LPtr }
          LocInfoE loc_267 (use{LPtr} (LocInfoE loc_268 ("p"))) ;
        locinfo: loc_260 ;
        LocInfoE loc_263 ("p") <-{ LPtr }
          LocInfoE loc_264 (use{LPtr} (LocInfoE loc_265 ("t"))) ;
        locinfo: loc_261 ;
        Goto "continue11"
      ]> $
      <[ "#3" :=
        locinfo: loc_252 ;
        Return (LocInfoE loc_253 (use{LPtr} (LocInfoE loc_254 ("w"))))
      ]> $
      <[ "continue11" :=
        locinfo: loc_251 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [append]. *)
  Definition impl_append : function := {|
    f_args := [
      ("l1", LPtr);
      ("l2", LPtr)
    ];
    f_local_vars := [
      ("end", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "end" <-{ LPtr }
          LocInfoE loc_313 (use{LPtr} (LocInfoE loc_314 ("l1"))) ;
        locinfo: loc_288 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_307 ;
        if: LocInfoE loc_307 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_307 ((LocInfoE loc_308 (use{LPtr} (LocInfoE loc_310 (!{LPtr} (LocInfoE loc_311 ("end")))))) !={PtrOp, PtrOp} (LocInfoE loc_312 (NULL)))))
        then
        locinfo: loc_297 ;
          Goto "#2"
        else
        locinfo: loc_289 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_297 ;
        LocInfoE loc_300 ("end") <-{ LPtr }
          LocInfoE loc_301 (&(LocInfoE loc_302 ((LocInfoE loc_303 (!{LPtr} (LocInfoE loc_305 (!{LPtr} (LocInfoE loc_306 ("end")))))) at{struct_list} "tail"))) ;
        locinfo: loc_298 ;
        Goto "continue15"
      ]> $
      <[ "#3" :=
        locinfo: loc_289 ;
        LocInfoE loc_291 (!{LPtr} (LocInfoE loc_292 ("end"))) <-{ LPtr }
          LocInfoE loc_293 (use{LPtr} (LocInfoE loc_294 ("l2"))) ;
        Return (VOID)
      ]> $
      <[ "continue15" :=
        locinfo: loc_288 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [member]. *)
  Definition impl_member : function := {|
    f_args := [
      ("p", LPtr);
      ("k", it_layout size_t)
    ];
    f_local_vars := [
      ("prev", LPtr);
      ("cur", LPtr);
      ("head", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "prev" <-{ LPtr }
          LocInfoE loc_365 (use{LPtr} (LocInfoE loc_366 ("p"))) ;
        locinfo: loc_320 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_359 ;
        if: LocInfoE loc_359 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_359 ((LocInfoE loc_360 (use{LPtr} (LocInfoE loc_362 (!{LPtr} (LocInfoE loc_363 ("prev")))))) !={PtrOp, PtrOp} (LocInfoE loc_364 (NULL)))))
        then
        Goto "#2"
        else
        locinfo: loc_321 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        "cur" <-{ LPtr }
          LocInfoE loc_353 (use{LPtr} (LocInfoE loc_355 (!{LPtr} (LocInfoE loc_356 ("prev"))))) ;
        "head" <-{ LPtr }
          LocInfoE loc_347 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_347 (use{LPtr} (LocInfoE loc_348 ((LocInfoE loc_349 (!{LPtr} (LocInfoE loc_350 ("cur")))) at{struct_list} "head"))))) ;
        locinfo: loc_340 ;
        if: LocInfoE loc_340 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_340 ((LocInfoE loc_341 (use{it_layout size_t} (LocInfoE loc_343 (!{LPtr} (LocInfoE loc_344 ("head")))))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_345 (use{it_layout size_t} (LocInfoE loc_346 ("k")))))))
        then
        locinfo: loc_337 ;
          Goto "#5"
        else
        locinfo: loc_328 ;
          Goto "#6"
      ]> $
      <[ "#3" :=
        locinfo: loc_321 ;
        Return (LocInfoE loc_322 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_322 (i2v 0 i32))))
      ]> $
      <[ "#4" :=
        locinfo: loc_328 ;
        LocInfoE loc_331 ("prev") <-{ LPtr }
          LocInfoE loc_332 (&(LocInfoE loc_333 ((LocInfoE loc_334 (!{LPtr} (LocInfoE loc_335 ("cur")))) at{struct_list} "tail"))) ;
        locinfo: loc_329 ;
        Goto "continue19"
      ]> $
      <[ "#5" :=
        locinfo: loc_337 ;
        Return (LocInfoE loc_338 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_338 (i2v 1 i32))))
      ]> $
      <[ "#6" :=
        locinfo: loc_328 ;
        Goto "#4"
      ]> $
      <[ "continue19" :=
        locinfo: loc_320 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [rev_append]. *)
  Definition impl_rev_append : function := {|
    f_args := [
      ("l1", LPtr);
      ("l2", LPtr)
    ];
    f_local_vars := [
      ("cur", LPtr);
      ("cur_tail", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "cur" <-{ LPtr }
          LocInfoE loc_405 (use{LPtr} (LocInfoE loc_406 ("l1"))) ;
        locinfo: loc_372 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_401 ;
        if: LocInfoE loc_401 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_401 ((LocInfoE loc_402 (use{LPtr} (LocInfoE loc_403 ("cur")))) !={PtrOp, PtrOp} (LocInfoE loc_404 (NULL)))))
        then
        locinfo: loc_375 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_375 ;
        LocInfoE loc_396 ("cur_tail") <-{ LPtr }
          LocInfoE loc_397 (use{LPtr} (LocInfoE loc_398 ((LocInfoE loc_399 (!{LPtr} (LocInfoE loc_400 ("cur")))) at{struct_list} "tail"))) ;
        locinfo: loc_376 ;
        LocInfoE loc_389 ((LocInfoE loc_390 (!{LPtr} (LocInfoE loc_391 ("cur")))) at{struct_list} "tail") <-{ LPtr }
          LocInfoE loc_392 (use{LPtr} (LocInfoE loc_394 (!{LPtr} (LocInfoE loc_395 ("l2"))))) ;
        locinfo: loc_377 ;
        LocInfoE loc_385 (!{LPtr} (LocInfoE loc_386 ("l2"))) <-{ LPtr }
          LocInfoE loc_387 (use{LPtr} (LocInfoE loc_388 ("cur"))) ;
        locinfo: loc_378 ;
        LocInfoE loc_381 ("cur") <-{ LPtr }
          LocInfoE loc_382 (use{LPtr} (LocInfoE loc_383 ("cur_tail"))) ;
        locinfo: loc_379 ;
        Goto "continue26"
      ]> $
      <[ "#3" :=
        Return (VOID)
      ]> $
      <[ "continue26" :=
        locinfo: loc_372 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.
End code.
