From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/t08_tree.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "tutorial/t08_tree.c".
  Definition loc_2 : location_info := LocationInfo file_0 63 2 63 47.
  Definition loc_3 : location_info := LocationInfo file_0 63 9 63 46.
  Definition loc_4 : location_info := LocationInfo file_0 63 9 63 32.
  Definition loc_5 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_6 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_7 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_8 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_11 : location_info := LocationInfo file_1 25 2 25 24.
  Definition loc_12 : location_info := LocationInfo file_1 25 9 25 23.
  Definition loc_15 : location_info := LocationInfo file_1 33 2 33 50.
  Definition loc_16 : location_info := LocationInfo file_1 34 2 34 30.
  Definition loc_17 : location_info := LocationInfo file_1 35 2 35 18.
  Definition loc_18 : location_info := LocationInfo file_1 36 2 36 31.
  Definition loc_19 : location_info := LocationInfo file_1 37 2 37 14.
  Definition loc_20 : location_info := LocationInfo file_1 37 9 37 13.
  Definition loc_21 : location_info := LocationInfo file_1 37 9 37 13.
  Definition loc_22 : location_info := LocationInfo file_1 36 2 36 13.
  Definition loc_23 : location_info := LocationInfo file_1 36 2 36 6.
  Definition loc_24 : location_info := LocationInfo file_1 36 2 36 6.
  Definition loc_25 : location_info := LocationInfo file_1 36 16 36 30.
  Definition loc_26 : location_info := LocationInfo file_1 35 2 35 11.
  Definition loc_27 : location_info := LocationInfo file_1 35 2 35 6.
  Definition loc_28 : location_info := LocationInfo file_1 35 2 35 6.
  Definition loc_29 : location_info := LocationInfo file_1 35 14 35 17.
  Definition loc_30 : location_info := LocationInfo file_1 35 14 35 17.
  Definition loc_31 : location_info := LocationInfo file_1 34 2 34 12.
  Definition loc_32 : location_info := LocationInfo file_1 34 2 34 6.
  Definition loc_33 : location_info := LocationInfo file_1 34 2 34 6.
  Definition loc_34 : location_info := LocationInfo file_1 34 15 34 29.
  Definition loc_35 : location_info := LocationInfo file_1 33 22 33 49.
  Definition loc_36 : location_info := LocationInfo file_1 33 22 33 28.
  Definition loc_37 : location_info := LocationInfo file_1 33 22 33 28.
  Definition loc_38 : location_info := LocationInfo file_1 33 29 33 48.
  Definition loc_43 : location_info := LocationInfo file_1 45 2 45 50.
  Definition loc_44 : location_info := LocationInfo file_1 46 2 46 20.
  Definition loc_45 : location_info := LocationInfo file_1 47 2 47 18.
  Definition loc_46 : location_info := LocationInfo file_1 48 2 48 22.
  Definition loc_47 : location_info := LocationInfo file_1 49 2 49 14.
  Definition loc_48 : location_info := LocationInfo file_1 49 9 49 13.
  Definition loc_49 : location_info := LocationInfo file_1 49 9 49 13.
  Definition loc_50 : location_info := LocationInfo file_1 48 2 48 13.
  Definition loc_51 : location_info := LocationInfo file_1 48 2 48 6.
  Definition loc_52 : location_info := LocationInfo file_1 48 2 48 6.
  Definition loc_53 : location_info := LocationInfo file_1 48 16 48 21.
  Definition loc_54 : location_info := LocationInfo file_1 48 16 48 21.
  Definition loc_55 : location_info := LocationInfo file_1 47 2 47 11.
  Definition loc_56 : location_info := LocationInfo file_1 47 2 47 6.
  Definition loc_57 : location_info := LocationInfo file_1 47 2 47 6.
  Definition loc_58 : location_info := LocationInfo file_1 47 14 47 17.
  Definition loc_59 : location_info := LocationInfo file_1 47 14 47 17.
  Definition loc_60 : location_info := LocationInfo file_1 46 2 46 12.
  Definition loc_61 : location_info := LocationInfo file_1 46 2 46 6.
  Definition loc_62 : location_info := LocationInfo file_1 46 2 46 6.
  Definition loc_63 : location_info := LocationInfo file_1 46 15 46 19.
  Definition loc_64 : location_info := LocationInfo file_1 46 15 46 19.
  Definition loc_65 : location_info := LocationInfo file_1 45 22 45 49.
  Definition loc_66 : location_info := LocationInfo file_1 45 22 45 28.
  Definition loc_67 : location_info := LocationInfo file_1 45 22 45 28.
  Definition loc_68 : location_info := LocationInfo file_1 45 29 45 48.
  Definition loc_73 : location_info := LocationInfo file_1 57 2 61 3.
  Definition loc_74 : location_info := LocationInfo file_1 57 26 61 3.
  Definition loc_75 : location_info := LocationInfo file_1 58 4 58 29.
  Definition loc_76 : location_info := LocationInfo file_1 59 4 59 30.
  Definition loc_77 : location_info := LocationInfo file_1 60 4 60 35.
  Definition loc_78 : location_info := LocationInfo file_1 60 4 60 9.
  Definition loc_79 : location_info := LocationInfo file_1 60 4 60 9.
  Definition loc_80 : location_info := LocationInfo file_1 60 10 60 29.
  Definition loc_81 : location_info := LocationInfo file_1 60 31 60 33.
  Definition loc_82 : location_info := LocationInfo file_1 60 31 60 33.
  Definition loc_83 : location_info := LocationInfo file_1 60 32 60 33.
  Definition loc_84 : location_info := LocationInfo file_1 60 32 60 33.
  Definition loc_85 : location_info := LocationInfo file_1 59 4 59 13.
  Definition loc_86 : location_info := LocationInfo file_1 59 4 59 13.
  Definition loc_87 : location_info := LocationInfo file_1 59 14 59 28.
  Definition loc_88 : location_info := LocationInfo file_1 59 15 59 28.
  Definition loc_89 : location_info := LocationInfo file_1 59 16 59 20.
  Definition loc_90 : location_info := LocationInfo file_1 59 16 59 20.
  Definition loc_91 : location_info := LocationInfo file_1 59 18 59 19.
  Definition loc_92 : location_info := LocationInfo file_1 59 18 59 19.
  Definition loc_93 : location_info := LocationInfo file_1 58 4 58 13.
  Definition loc_94 : location_info := LocationInfo file_1 58 4 58 13.
  Definition loc_95 : location_info := LocationInfo file_1 58 14 58 27.
  Definition loc_96 : location_info := LocationInfo file_1 58 15 58 27.
  Definition loc_97 : location_info := LocationInfo file_1 58 16 58 20.
  Definition loc_98 : location_info := LocationInfo file_1 58 16 58 20.
  Definition loc_99 : location_info := LocationInfo file_1 58 18 58 19.
  Definition loc_100 : location_info := LocationInfo file_1 58 18 58 19.
  Definition loc_101 : location_info := LocationInfo file_1 57 2 61 3.
  Definition loc_102 : location_info := LocationInfo file_1 57 5 57 25.
  Definition loc_103 : location_info := LocationInfo file_1 57 5 57 7.
  Definition loc_104 : location_info := LocationInfo file_1 57 5 57 7.
  Definition loc_105 : location_info := LocationInfo file_1 57 6 57 7.
  Definition loc_106 : location_info := LocationInfo file_1 57 6 57 7.
  Definition loc_107 : location_info := LocationInfo file_1 57 11 57 25.
  Definition loc_110 : location_info := LocationInfo file_1 70 2 70 36.
  Definition loc_111 : location_info := LocationInfo file_1 71 2 71 30.
  Definition loc_112 : location_info := LocationInfo file_1 72 2 72 56.
  Definition loc_113 : location_info := LocationInfo file_1 73 2 73 39.
  Definition loc_114 : location_info := LocationInfo file_1 73 9 73 38.
  Definition loc_115 : location_info := LocationInfo file_1 73 9 73 19.
  Definition loc_116 : location_info := LocationInfo file_1 73 9 73 19.
  Definition loc_117 : location_info := LocationInfo file_1 73 20 73 34.
  Definition loc_118 : location_info := LocationInfo file_1 73 21 73 34.
  Definition loc_119 : location_info := LocationInfo file_1 73 22 73 26.
  Definition loc_120 : location_info := LocationInfo file_1 73 22 73 26.
  Definition loc_121 : location_info := LocationInfo file_1 73 24 73 25.
  Definition loc_122 : location_info := LocationInfo file_1 73 24 73 25.
  Definition loc_123 : location_info := LocationInfo file_1 73 36 73 37.
  Definition loc_124 : location_info := LocationInfo file_1 73 36 73 37.
  Definition loc_125 : location_info := LocationInfo file_1 72 20 72 56.
  Definition loc_126 : location_info := LocationInfo file_1 72 27 72 55.
  Definition loc_127 : location_info := LocationInfo file_1 72 27 72 37.
  Definition loc_128 : location_info := LocationInfo file_1 72 27 72 37.
  Definition loc_129 : location_info := LocationInfo file_1 72 38 72 51.
  Definition loc_130 : location_info := LocationInfo file_1 72 39 72 51.
  Definition loc_131 : location_info := LocationInfo file_1 72 40 72 44.
  Definition loc_132 : location_info := LocationInfo file_1 72 40 72 44.
  Definition loc_133 : location_info := LocationInfo file_1 72 42 72 43.
  Definition loc_134 : location_info := LocationInfo file_1 72 42 72 43.
  Definition loc_135 : location_info := LocationInfo file_1 72 53 72 54.
  Definition loc_136 : location_info := LocationInfo file_1 72 53 72 54.
  Definition loc_137 : location_info := LocationInfo file_1 72 2 72 56.
  Definition loc_138 : location_info := LocationInfo file_1 72 5 72 18.
  Definition loc_139 : location_info := LocationInfo file_1 72 5 72 6.
  Definition loc_140 : location_info := LocationInfo file_1 72 5 72 6.
  Definition loc_141 : location_info := LocationInfo file_1 72 9 72 18.
  Definition loc_142 : location_info := LocationInfo file_1 72 9 72 18.
  Definition loc_143 : location_info := LocationInfo file_1 72 9 72 13.
  Definition loc_144 : location_info := LocationInfo file_1 72 9 72 13.
  Definition loc_145 : location_info := LocationInfo file_1 72 11 72 12.
  Definition loc_146 : location_info := LocationInfo file_1 72 11 72 12.
  Definition loc_147 : location_info := LocationInfo file_1 71 21 71 30.
  Definition loc_148 : location_info := LocationInfo file_1 71 28 71 29.
  Definition loc_149 : location_info := LocationInfo file_1 71 2 71 30.
  Definition loc_150 : location_info := LocationInfo file_1 71 5 71 19.
  Definition loc_151 : location_info := LocationInfo file_1 71 5 71 14.
  Definition loc_152 : location_info := LocationInfo file_1 71 5 71 14.
  Definition loc_153 : location_info := LocationInfo file_1 71 5 71 9.
  Definition loc_154 : location_info := LocationInfo file_1 71 5 71 9.
  Definition loc_155 : location_info := LocationInfo file_1 71 7 71 8.
  Definition loc_156 : location_info := LocationInfo file_1 71 7 71 8.
  Definition loc_157 : location_info := LocationInfo file_1 71 18 71 19.
  Definition loc_158 : location_info := LocationInfo file_1 71 18 71 19.
  Definition loc_159 : location_info := LocationInfo file_1 70 27 70 36.
  Definition loc_160 : location_info := LocationInfo file_1 70 34 70 35.
  Definition loc_161 : location_info := LocationInfo file_1 70 2 70 36.
  Definition loc_162 : location_info := LocationInfo file_1 70 5 70 25.
  Definition loc_163 : location_info := LocationInfo file_1 70 5 70 7.
  Definition loc_164 : location_info := LocationInfo file_1 70 5 70 7.
  Definition loc_165 : location_info := LocationInfo file_1 70 6 70 7.
  Definition loc_166 : location_info := LocationInfo file_1 70 6 70 7.
  Definition loc_167 : location_info := LocationInfo file_1 70 11 70 25.
  Definition loc_170 : location_info := LocationInfo file_1 82 2 82 20.
  Definition loc_171 : location_info := LocationInfo file_1 88 2 95 3.
  Definition loc_172 : location_info := LocationInfo file_1 96 2 96 11.
  Definition loc_173 : location_info := LocationInfo file_1 96 9 96 10.
  Definition loc_174 : location_info := LocationInfo file_1 88 31 95 3.
  Definition loc_175 : location_info := LocationInfo file_1 89 4 89 34.
  Definition loc_176 : location_info := LocationInfo file_1 90 4 94 5.
  Definition loc_177 : location_info := LocationInfo file_1 90 23 92 5.
  Definition loc_178 : location_info := LocationInfo file_1 91 6 91 28.
  Definition loc_179 : location_info := LocationInfo file_1 91 6 91 9.
  Definition loc_180 : location_info := LocationInfo file_1 91 12 91 27.
  Definition loc_181 : location_info := LocationInfo file_1 91 13 91 27.
  Definition loc_182 : location_info := LocationInfo file_1 91 14 91 20.
  Definition loc_183 : location_info := LocationInfo file_1 91 14 91 20.
  Definition loc_184 : location_info := LocationInfo file_1 91 16 91 19.
  Definition loc_185 : location_info := LocationInfo file_1 91 16 91 19.
  Definition loc_186 : location_info := LocationInfo file_1 92 11 94 5.
  Definition loc_187 : location_info := LocationInfo file_1 93 6 93 29.
  Definition loc_188 : location_info := LocationInfo file_1 93 6 93 9.
  Definition loc_189 : location_info := LocationInfo file_1 93 12 93 28.
  Definition loc_190 : location_info := LocationInfo file_1 93 13 93 28.
  Definition loc_191 : location_info := LocationInfo file_1 93 14 93 20.
  Definition loc_192 : location_info := LocationInfo file_1 93 14 93 20.
  Definition loc_193 : location_info := LocationInfo file_1 93 16 93 19.
  Definition loc_194 : location_info := LocationInfo file_1 93 16 93 19.
  Definition loc_195 : location_info := LocationInfo file_1 90 7 90 22.
  Definition loc_196 : location_info := LocationInfo file_1 90 7 90 8.
  Definition loc_197 : location_info := LocationInfo file_1 90 7 90 8.
  Definition loc_198 : location_info := LocationInfo file_1 90 11 90 22.
  Definition loc_199 : location_info := LocationInfo file_1 90 11 90 22.
  Definition loc_200 : location_info := LocationInfo file_1 90 11 90 17.
  Definition loc_201 : location_info := LocationInfo file_1 90 11 90 17.
  Definition loc_202 : location_info := LocationInfo file_1 90 13 90 16.
  Definition loc_203 : location_info := LocationInfo file_1 90 13 90 16.
  Definition loc_204 : location_info := LocationInfo file_1 89 25 89 34.
  Definition loc_205 : location_info := LocationInfo file_1 89 32 89 33.
  Definition loc_206 : location_info := LocationInfo file_1 89 4 89 34.
  Definition loc_207 : location_info := LocationInfo file_1 89 7 89 23.
  Definition loc_208 : location_info := LocationInfo file_1 89 7 89 18.
  Definition loc_209 : location_info := LocationInfo file_1 89 7 89 18.
  Definition loc_210 : location_info := LocationInfo file_1 89 7 89 13.
  Definition loc_211 : location_info := LocationInfo file_1 89 7 89 13.
  Definition loc_212 : location_info := LocationInfo file_1 89 9 89 12.
  Definition loc_213 : location_info := LocationInfo file_1 89 9 89 12.
  Definition loc_214 : location_info := LocationInfo file_1 89 22 89 23.
  Definition loc_215 : location_info := LocationInfo file_1 89 22 89 23.
  Definition loc_216 : location_info := LocationInfo file_1 88 8 88 30.
  Definition loc_217 : location_info := LocationInfo file_1 88 8 88 12.
  Definition loc_218 : location_info := LocationInfo file_1 88 8 88 12.
  Definition loc_219 : location_info := LocationInfo file_1 88 9 88 12.
  Definition loc_220 : location_info := LocationInfo file_1 88 9 88 12.
  Definition loc_221 : location_info := LocationInfo file_1 88 16 88 30.
  Definition loc_222 : location_info := LocationInfo file_1 82 16 82 19.
  Definition loc_223 : location_info := LocationInfo file_1 82 17 82 19.
  Definition loc_224 : location_info := LocationInfo file_1 82 18 82 19.
  Definition loc_225 : location_info := LocationInfo file_1 82 18 82 19.
  Definition loc_230 : location_info := LocationInfo file_1 104 2 113 3.
  Definition loc_231 : location_info := LocationInfo file_1 104 26 106 3.
  Definition loc_232 : location_info := LocationInfo file_1 105 4 105 49.
  Definition loc_233 : location_info := LocationInfo file_1 105 4 105 6.
  Definition loc_234 : location_info := LocationInfo file_1 105 5 105 6.
  Definition loc_235 : location_info := LocationInfo file_1 105 5 105 6.
  Definition loc_236 : location_info := LocationInfo file_1 105 9 105 48.
  Definition loc_237 : location_info := LocationInfo file_1 105 9 105 13.
  Definition loc_238 : location_info := LocationInfo file_1 105 9 105 13.
  Definition loc_239 : location_info := LocationInfo file_1 105 14 105 28.
  Definition loc_240 : location_info := LocationInfo file_1 105 30 105 31.
  Definition loc_241 : location_info := LocationInfo file_1 105 30 105 31.
  Definition loc_242 : location_info := LocationInfo file_1 105 33 105 47.
  Definition loc_243 : location_info := LocationInfo file_1 106 9 113 3.
  Definition loc_244 : location_info := LocationInfo file_1 107 4 107 30.
  Definition loc_245 : location_info := LocationInfo file_1 108 4 112 5.
  Definition loc_246 : location_info := LocationInfo file_1 108 21 110 5.
  Definition loc_247 : location_info := LocationInfo file_1 109 6 109 35.
  Definition loc_248 : location_info := LocationInfo file_1 109 6 109 16.
  Definition loc_249 : location_info := LocationInfo file_1 109 6 109 16.
  Definition loc_250 : location_info := LocationInfo file_1 109 17 109 30.
  Definition loc_251 : location_info := LocationInfo file_1 109 18 109 30.
  Definition loc_252 : location_info := LocationInfo file_1 109 19 109 23.
  Definition loc_253 : location_info := LocationInfo file_1 109 19 109 23.
  Definition loc_254 : location_info := LocationInfo file_1 109 21 109 22.
  Definition loc_255 : location_info := LocationInfo file_1 109 21 109 22.
  Definition loc_256 : location_info := LocationInfo file_1 109 32 109 33.
  Definition loc_257 : location_info := LocationInfo file_1 109 32 109 33.
  Definition loc_258 : location_info := LocationInfo file_1 110 11 112 5.
  Definition loc_259 : location_info := LocationInfo file_1 111 6 111 36.
  Definition loc_260 : location_info := LocationInfo file_1 111 6 111 16.
  Definition loc_261 : location_info := LocationInfo file_1 111 6 111 16.
  Definition loc_262 : location_info := LocationInfo file_1 111 17 111 31.
  Definition loc_263 : location_info := LocationInfo file_1 111 18 111 31.
  Definition loc_264 : location_info := LocationInfo file_1 111 19 111 23.
  Definition loc_265 : location_info := LocationInfo file_1 111 19 111 23.
  Definition loc_266 : location_info := LocationInfo file_1 111 21 111 22.
  Definition loc_267 : location_info := LocationInfo file_1 111 21 111 22.
  Definition loc_268 : location_info := LocationInfo file_1 111 33 111 34.
  Definition loc_269 : location_info := LocationInfo file_1 111 33 111 34.
  Definition loc_270 : location_info := LocationInfo file_1 108 7 108 20.
  Definition loc_271 : location_info := LocationInfo file_1 108 7 108 8.
  Definition loc_272 : location_info := LocationInfo file_1 108 7 108 8.
  Definition loc_273 : location_info := LocationInfo file_1 108 11 108 20.
  Definition loc_274 : location_info := LocationInfo file_1 108 11 108 20.
  Definition loc_275 : location_info := LocationInfo file_1 108 11 108 15.
  Definition loc_276 : location_info := LocationInfo file_1 108 11 108 15.
  Definition loc_277 : location_info := LocationInfo file_1 108 13 108 14.
  Definition loc_278 : location_info := LocationInfo file_1 108 13 108 14.
  Definition loc_279 : location_info := LocationInfo file_1 107 23 107 30.
  Definition loc_281 : location_info := LocationInfo file_1 107 4 107 30.
  Definition loc_282 : location_info := LocationInfo file_1 107 7 107 21.
  Definition loc_283 : location_info := LocationInfo file_1 107 7 107 16.
  Definition loc_284 : location_info := LocationInfo file_1 107 7 107 16.
  Definition loc_285 : location_info := LocationInfo file_1 107 7 107 11.
  Definition loc_286 : location_info := LocationInfo file_1 107 7 107 11.
  Definition loc_287 : location_info := LocationInfo file_1 107 9 107 10.
  Definition loc_288 : location_info := LocationInfo file_1 107 9 107 10.
  Definition loc_289 : location_info := LocationInfo file_1 107 20 107 21.
  Definition loc_290 : location_info := LocationInfo file_1 107 20 107 21.
  Definition loc_291 : location_info := LocationInfo file_1 104 5 104 25.
  Definition loc_292 : location_info := LocationInfo file_1 104 5 104 7.
  Definition loc_293 : location_info := LocationInfo file_1 104 5 104 7.
  Definition loc_294 : location_info := LocationInfo file_1 104 6 104 7.
  Definition loc_295 : location_info := LocationInfo file_1 104 6 104 7.
  Definition loc_296 : location_info := LocationInfo file_1 104 11 104 25.
  Definition loc_299 : location_info := LocationInfo file_1 121 2 121 20.
  Definition loc_300 : location_info := LocationInfo file_1 126 2 133 3.
  Definition loc_301 : location_info := LocationInfo file_1 135 2 135 49.
  Definition loc_302 : location_info := LocationInfo file_1 135 2 135 6.
  Definition loc_303 : location_info := LocationInfo file_1 135 3 135 6.
  Definition loc_304 : location_info := LocationInfo file_1 135 3 135 6.
  Definition loc_305 : location_info := LocationInfo file_1 135 9 135 48.
  Definition loc_306 : location_info := LocationInfo file_1 135 9 135 13.
  Definition loc_307 : location_info := LocationInfo file_1 135 9 135 13.
  Definition loc_308 : location_info := LocationInfo file_1 135 14 135 28.
  Definition loc_309 : location_info := LocationInfo file_1 135 30 135 31.
  Definition loc_310 : location_info := LocationInfo file_1 135 30 135 31.
  Definition loc_311 : location_info := LocationInfo file_1 135 33 135 47.
  Definition loc_312 : location_info := LocationInfo file_1 126 31 133 3.
  Definition loc_313 : location_info := LocationInfo file_1 127 4 127 32.
  Definition loc_314 : location_info := LocationInfo file_1 128 4 132 5.
  Definition loc_315 : location_info := LocationInfo file_1 128 23 130 5.
  Definition loc_316 : location_info := LocationInfo file_1 129 6 129 28.
  Definition loc_317 : location_info := LocationInfo file_1 129 6 129 9.
  Definition loc_318 : location_info := LocationInfo file_1 129 12 129 27.
  Definition loc_319 : location_info := LocationInfo file_1 129 13 129 27.
  Definition loc_320 : location_info := LocationInfo file_1 129 14 129 20.
  Definition loc_321 : location_info := LocationInfo file_1 129 14 129 20.
  Definition loc_322 : location_info := LocationInfo file_1 129 16 129 19.
  Definition loc_323 : location_info := LocationInfo file_1 129 16 129 19.
  Definition loc_324 : location_info := LocationInfo file_1 130 11 132 5.
  Definition loc_325 : location_info := LocationInfo file_1 131 6 131 29.
  Definition loc_326 : location_info := LocationInfo file_1 131 6 131 9.
  Definition loc_327 : location_info := LocationInfo file_1 131 12 131 28.
  Definition loc_328 : location_info := LocationInfo file_1 131 13 131 28.
  Definition loc_329 : location_info := LocationInfo file_1 131 14 131 20.
  Definition loc_330 : location_info := LocationInfo file_1 131 14 131 20.
  Definition loc_331 : location_info := LocationInfo file_1 131 16 131 19.
  Definition loc_332 : location_info := LocationInfo file_1 131 16 131 19.
  Definition loc_333 : location_info := LocationInfo file_1 128 7 128 22.
  Definition loc_334 : location_info := LocationInfo file_1 128 7 128 8.
  Definition loc_335 : location_info := LocationInfo file_1 128 7 128 8.
  Definition loc_336 : location_info := LocationInfo file_1 128 11 128 22.
  Definition loc_337 : location_info := LocationInfo file_1 128 11 128 22.
  Definition loc_338 : location_info := LocationInfo file_1 128 11 128 17.
  Definition loc_339 : location_info := LocationInfo file_1 128 11 128 17.
  Definition loc_340 : location_info := LocationInfo file_1 128 13 128 16.
  Definition loc_341 : location_info := LocationInfo file_1 128 13 128 16.
  Definition loc_342 : location_info := LocationInfo file_1 127 25 127 32.
  Definition loc_344 : location_info := LocationInfo file_1 127 4 127 32.
  Definition loc_345 : location_info := LocationInfo file_1 127 7 127 23.
  Definition loc_346 : location_info := LocationInfo file_1 127 7 127 18.
  Definition loc_347 : location_info := LocationInfo file_1 127 7 127 18.
  Definition loc_348 : location_info := LocationInfo file_1 127 7 127 13.
  Definition loc_349 : location_info := LocationInfo file_1 127 7 127 13.
  Definition loc_350 : location_info := LocationInfo file_1 127 9 127 12.
  Definition loc_351 : location_info := LocationInfo file_1 127 9 127 12.
  Definition loc_352 : location_info := LocationInfo file_1 127 22 127 23.
  Definition loc_353 : location_info := LocationInfo file_1 127 22 127 23.
  Definition loc_354 : location_info := LocationInfo file_1 126 8 126 30.
  Definition loc_355 : location_info := LocationInfo file_1 126 8 126 12.
  Definition loc_356 : location_info := LocationInfo file_1 126 8 126 12.
  Definition loc_357 : location_info := LocationInfo file_1 126 9 126 12.
  Definition loc_358 : location_info := LocationInfo file_1 126 9 126 12.
  Definition loc_359 : location_info := LocationInfo file_1 126 16 126 30.
  Definition loc_360 : location_info := LocationInfo file_1 121 16 121 19.
  Definition loc_361 : location_info := LocationInfo file_1 121 17 121 19.
  Definition loc_362 : location_info := LocationInfo file_1 121 18 121 19.
  Definition loc_363 : location_info := LocationInfo file_1 121 18 121 19.
  Definition loc_368 : location_info := LocationInfo file_1 145 4 147 5.
  Definition loc_369 : location_info := LocationInfo file_1 148 4 148 36.
  Definition loc_370 : location_info := LocationInfo file_1 148 11 148 35.
  Definition loc_371 : location_info := LocationInfo file_1 148 11 148 19.
  Definition loc_372 : location_info := LocationInfo file_1 148 11 148 19.
  Definition loc_373 : location_info := LocationInfo file_1 148 20 148 34.
  Definition loc_374 : location_info := LocationInfo file_1 148 21 148 34.
  Definition loc_375 : location_info := LocationInfo file_1 148 22 148 26.
  Definition loc_376 : location_info := LocationInfo file_1 148 22 148 26.
  Definition loc_377 : location_info := LocationInfo file_1 148 24 148 25.
  Definition loc_378 : location_info := LocationInfo file_1 148 24 148 25.
  Definition loc_379 : location_info := LocationInfo file_1 145 38 147 5.
  Definition loc_380 : location_info := LocationInfo file_1 146 8 146 25.
  Definition loc_381 : location_info := LocationInfo file_1 146 15 146 24.
  Definition loc_382 : location_info := LocationInfo file_1 146 15 146 24.
  Definition loc_383 : location_info := LocationInfo file_1 146 15 146 19.
  Definition loc_384 : location_info := LocationInfo file_1 146 15 146 19.
  Definition loc_385 : location_info := LocationInfo file_1 146 17 146 18.
  Definition loc_386 : location_info := LocationInfo file_1 146 17 146 18.
  Definition loc_387 : location_info := LocationInfo file_1 145 4 147 5.
  Definition loc_388 : location_info := LocationInfo file_1 145 7 145 36.
  Definition loc_389 : location_info := LocationInfo file_1 145 7 145 18.
  Definition loc_390 : location_info := LocationInfo file_1 145 7 145 18.
  Definition loc_391 : location_info := LocationInfo file_1 145 7 145 11.
  Definition loc_392 : location_info := LocationInfo file_1 145 7 145 11.
  Definition loc_393 : location_info := LocationInfo file_1 145 9 145 10.
  Definition loc_394 : location_info := LocationInfo file_1 145 9 145 10.
  Definition loc_395 : location_info := LocationInfo file_1 145 22 145 36.
  Definition loc_398 : location_info := LocationInfo file_1 157 2 157 13.
  Definition loc_399 : location_info := LocationInfo file_1 158 2 158 8.
  Definition loc_400 : location_info := LocationInfo file_1 159 2 161 3.
  Definition loc_401 : location_info := LocationInfo file_1 163 2 177 3.
  Definition loc_402 : location_info := LocationInfo file_1 163 21 173 3.
  Definition loc_403 : location_info := LocationInfo file_1 164 4 172 5.
  Definition loc_404 : location_info := LocationInfo file_1 164 36 168 5.
  Definition loc_405 : location_info := LocationInfo file_1 165 6 165 32.
  Definition loc_406 : location_info := LocationInfo file_1 166 6 166 29.
  Definition loc_407 : location_info := LocationInfo file_1 167 6 167 20.
  Definition loc_408 : location_info := LocationInfo file_1 167 6 167 15.
  Definition loc_409 : location_info := LocationInfo file_1 167 6 167 10.
  Definition loc_410 : location_info := LocationInfo file_1 167 6 167 10.
  Definition loc_411 : location_info := LocationInfo file_1 167 8 167 9.
  Definition loc_412 : location_info := LocationInfo file_1 167 8 167 9.
  Definition loc_413 : location_info := LocationInfo file_1 167 18 167 19.
  Definition loc_414 : location_info := LocationInfo file_1 167 18 167 19.
  Definition loc_415 : location_info := LocationInfo file_1 166 6 166 12.
  Definition loc_416 : location_info := LocationInfo file_1 166 6 166 12.
  Definition loc_417 : location_info := LocationInfo file_1 166 13 166 24.
  Definition loc_418 : location_info := LocationInfo file_1 166 14 166 24.
  Definition loc_419 : location_info := LocationInfo file_1 166 14 166 18.
  Definition loc_420 : location_info := LocationInfo file_1 166 14 166 18.
  Definition loc_421 : location_info := LocationInfo file_1 166 16 166 17.
  Definition loc_422 : location_info := LocationInfo file_1 166 16 166 17.
  Definition loc_423 : location_info := LocationInfo file_1 166 26 166 27.
  Definition loc_424 : location_info := LocationInfo file_1 166 26 166 27.
  Definition loc_425 : location_info := LocationInfo file_1 165 6 165 7.
  Definition loc_426 : location_info := LocationInfo file_1 165 10 165 31.
  Definition loc_427 : location_info := LocationInfo file_1 165 10 165 18.
  Definition loc_428 : location_info := LocationInfo file_1 165 10 165 18.
  Definition loc_429 : location_info := LocationInfo file_1 165 19 165 30.
  Definition loc_430 : location_info := LocationInfo file_1 165 20 165 30.
  Definition loc_431 : location_info := LocationInfo file_1 165 20 165 24.
  Definition loc_432 : location_info := LocationInfo file_1 165 20 165 24.
  Definition loc_433 : location_info := LocationInfo file_1 165 22 165 23.
  Definition loc_434 : location_info := LocationInfo file_1 165 22 165 23.
  Definition loc_435 : location_info := LocationInfo file_1 168 11 172 5.
  Definition loc_436 : location_info := LocationInfo file_1 169 6 169 24.
  Definition loc_437 : location_info := LocationInfo file_1 170 6 170 37.
  Definition loc_438 : location_info := LocationInfo file_1 171 6 171 15.
  Definition loc_439 : location_info := LocationInfo file_1 171 6 171 8.
  Definition loc_440 : location_info := LocationInfo file_1 171 7 171 8.
  Definition loc_441 : location_info := LocationInfo file_1 171 7 171 8.
  Definition loc_442 : location_info := LocationInfo file_1 171 11 171 14.
  Definition loc_443 : location_info := LocationInfo file_1 171 11 171 14.
  Definition loc_444 : location_info := LocationInfo file_1 170 6 170 11.
  Definition loc_445 : location_info := LocationInfo file_1 170 6 170 11.
  Definition loc_446 : location_info := LocationInfo file_1 170 12 170 31.
  Definition loc_447 : location_info := LocationInfo file_1 170 33 170 35.
  Definition loc_448 : location_info := LocationInfo file_1 170 33 170 35.
  Definition loc_449 : location_info := LocationInfo file_1 170 34 170 35.
  Definition loc_450 : location_info := LocationInfo file_1 170 34 170 35.
  Definition loc_451 : location_info := LocationInfo file_1 169 6 169 9.
  Definition loc_452 : location_info := LocationInfo file_1 169 12 169 23.
  Definition loc_453 : location_info := LocationInfo file_1 169 12 169 23.
  Definition loc_454 : location_info := LocationInfo file_1 169 12 169 16.
  Definition loc_455 : location_info := LocationInfo file_1 169 12 169 16.
  Definition loc_456 : location_info := LocationInfo file_1 169 14 169 15.
  Definition loc_457 : location_info := LocationInfo file_1 169 14 169 15.
  Definition loc_458 : location_info := LocationInfo file_1 164 7 164 35.
  Definition loc_459 : location_info := LocationInfo file_1 164 7 164 17.
  Definition loc_460 : location_info := LocationInfo file_1 164 7 164 17.
  Definition loc_461 : location_info := LocationInfo file_1 164 7 164 11.
  Definition loc_462 : location_info := LocationInfo file_1 164 7 164 11.
  Definition loc_463 : location_info := LocationInfo file_1 164 9 164 10.
  Definition loc_464 : location_info := LocationInfo file_1 164 9 164 10.
  Definition loc_465 : location_info := LocationInfo file_1 164 21 164 35.
  Definition loc_466 : location_info := LocationInfo file_1 173 9 177 3.
  Definition loc_467 : location_info := LocationInfo file_1 173 26 175 3.
  Definition loc_468 : location_info := LocationInfo file_1 174 4 174 27.
  Definition loc_469 : location_info := LocationInfo file_1 174 4 174 10.
  Definition loc_470 : location_info := LocationInfo file_1 174 4 174 10.
  Definition loc_471 : location_info := LocationInfo file_1 174 11 174 22.
  Definition loc_472 : location_info := LocationInfo file_1 174 12 174 22.
  Definition loc_473 : location_info := LocationInfo file_1 174 12 174 16.
  Definition loc_474 : location_info := LocationInfo file_1 174 12 174 16.
  Definition loc_475 : location_info := LocationInfo file_1 174 14 174 15.
  Definition loc_476 : location_info := LocationInfo file_1 174 14 174 15.
  Definition loc_477 : location_info := LocationInfo file_1 174 24 174 25.
  Definition loc_478 : location_info := LocationInfo file_1 174 24 174 25.
  Definition loc_479 : location_info := LocationInfo file_1 175 9 177 3.
  Definition loc_480 : location_info := LocationInfo file_1 176 4 176 28.
  Definition loc_481 : location_info := LocationInfo file_1 176 4 176 10.
  Definition loc_482 : location_info := LocationInfo file_1 176 4 176 10.
  Definition loc_483 : location_info := LocationInfo file_1 176 11 176 23.
  Definition loc_484 : location_info := LocationInfo file_1 176 12 176 23.
  Definition loc_485 : location_info := LocationInfo file_1 176 12 176 16.
  Definition loc_486 : location_info := LocationInfo file_1 176 12 176 16.
  Definition loc_487 : location_info := LocationInfo file_1 176 14 176 15.
  Definition loc_488 : location_info := LocationInfo file_1 176 14 176 15.
  Definition loc_489 : location_info := LocationInfo file_1 176 25 176 26.
  Definition loc_490 : location_info := LocationInfo file_1 176 25 176 26.
  Definition loc_491 : location_info := LocationInfo file_1 173 12 173 25.
  Definition loc_492 : location_info := LocationInfo file_1 173 12 173 13.
  Definition loc_493 : location_info := LocationInfo file_1 173 12 173 13.
  Definition loc_494 : location_info := LocationInfo file_1 173 16 173 25.
  Definition loc_495 : location_info := LocationInfo file_1 173 16 173 25.
  Definition loc_496 : location_info := LocationInfo file_1 173 16 173 20.
  Definition loc_497 : location_info := LocationInfo file_1 173 16 173 20.
  Definition loc_498 : location_info := LocationInfo file_1 173 18 173 19.
  Definition loc_499 : location_info := LocationInfo file_1 173 18 173 19.
  Definition loc_500 : location_info := LocationInfo file_1 163 5 163 19.
  Definition loc_501 : location_info := LocationInfo file_1 163 5 163 6.
  Definition loc_502 : location_info := LocationInfo file_1 163 5 163 6.
  Definition loc_503 : location_info := LocationInfo file_1 163 10 163 19.
  Definition loc_504 : location_info := LocationInfo file_1 163 10 163 19.
  Definition loc_505 : location_info := LocationInfo file_1 163 10 163 14.
  Definition loc_506 : location_info := LocationInfo file_1 163 10 163 14.
  Definition loc_507 : location_info := LocationInfo file_1 163 12 163 13.
  Definition loc_508 : location_info := LocationInfo file_1 163 12 163 13.
  Definition loc_509 : location_info := LocationInfo file_1 159 27 161 3.
  Definition loc_510 : location_info := LocationInfo file_1 160 4 160 11.
  Definition loc_512 : location_info := LocationInfo file_1 159 2 161 3.
  Definition loc_513 : location_info := LocationInfo file_1 159 5 159 25.
  Definition loc_514 : location_info := LocationInfo file_1 159 5 159 7.
  Definition loc_515 : location_info := LocationInfo file_1 159 5 159 7.
  Definition loc_516 : location_info := LocationInfo file_1 159 6 159 7.
  Definition loc_517 : location_info := LocationInfo file_1 159 6 159 7.
  Definition loc_518 : location_info := LocationInfo file_1 159 11 159 25.
  Definition loc_521 : location_info := LocationInfo file_1 185 2 185 17.
  Definition loc_522 : location_info := LocationInfo file_1 185 9 185 16.
  Definition loc_523 : location_info := LocationInfo file_1 185 9 185 14.
  Definition loc_524 : location_info := LocationInfo file_1 185 9 185 14.
  Definition loc_527 : location_info := LocationInfo file_1 194 2 194 19.
  Definition loc_528 : location_info := LocationInfo file_1 194 9 194 18.
  Definition loc_529 : location_info := LocationInfo file_1 194 9 194 13.
  Definition loc_530 : location_info := LocationInfo file_1 194 9 194 13.
  Definition loc_531 : location_info := LocationInfo file_1 194 14 194 17.
  Definition loc_532 : location_info := LocationInfo file_1 194 14 194 17.
  Definition loc_535 : location_info := LocationInfo file_1 202 2 202 15.
  Definition loc_536 : location_info := LocationInfo file_1 202 2 202 11.
  Definition loc_537 : location_info := LocationInfo file_1 202 2 202 11.
  Definition loc_538 : location_info := LocationInfo file_1 202 12 202 13.
  Definition loc_539 : location_info := LocationInfo file_1 202 12 202 13.
  Definition loc_542 : location_info := LocationInfo file_1 212 2 212 22.
  Definition loc_543 : location_info := LocationInfo file_1 212 9 212 21.
  Definition loc_544 : location_info := LocationInfo file_1 212 9 212 15.
  Definition loc_545 : location_info := LocationInfo file_1 212 9 212 15.
  Definition loc_546 : location_info := LocationInfo file_1 212 16 212 17.
  Definition loc_547 : location_info := LocationInfo file_1 212 16 212 17.
  Definition loc_548 : location_info := LocationInfo file_1 212 19 212 20.
  Definition loc_549 : location_info := LocationInfo file_1 212 19 212 20.
  Definition loc_552 : location_info := LocationInfo file_1 221 2 221 15.
  Definition loc_553 : location_info := LocationInfo file_1 221 2 221 8.
  Definition loc_554 : location_info := LocationInfo file_1 221 2 221 8.
  Definition loc_555 : location_info := LocationInfo file_1 221 9 221 10.
  Definition loc_556 : location_info := LocationInfo file_1 221 9 221 10.
  Definition loc_557 : location_info := LocationInfo file_1 221 12 221 13.
  Definition loc_558 : location_info := LocationInfo file_1 221 12 221 13.
  Definition loc_561 : location_info := LocationInfo file_1 230 2 230 15.
  Definition loc_562 : location_info := LocationInfo file_1 230 2 230 8.
  Definition loc_563 : location_info := LocationInfo file_1 230 2 230 8.
  Definition loc_564 : location_info := LocationInfo file_1 230 9 230 10.
  Definition loc_565 : location_info := LocationInfo file_1 230 9 230 10.
  Definition loc_566 : location_info := LocationInfo file_1 230 12 230 13.
  Definition loc_567 : location_info := LocationInfo file_1 230 12 230 13.
  Definition loc_570 : location_info := LocationInfo file_1 237 2 237 22.
  Definition loc_571 : location_info := LocationInfo file_1 238 2 238 15.
  Definition loc_572 : location_info := LocationInfo file_1 242 2 242 17.
  Definition loc_573 : location_info := LocationInfo file_1 244 2 244 25.
  Definition loc_574 : location_info := LocationInfo file_1 245 2 245 25.
  Definition loc_575 : location_info := LocationInfo file_1 247 2 247 17.
  Definition loc_576 : location_info := LocationInfo file_1 250 2 250 17.
  Definition loc_577 : location_info := LocationInfo file_1 251 2 251 25.
  Definition loc_578 : location_info := LocationInfo file_1 253 2 253 17.
  Definition loc_579 : location_info := LocationInfo file_1 256 2 256 17.
  Definition loc_580 : location_info := LocationInfo file_1 258 2 258 11.
  Definition loc_581 : location_info := LocationInfo file_1 258 9 258 10.
  Definition loc_582 : location_info := LocationInfo file_1 256 2 256 12.
  Definition loc_583 : location_info := LocationInfo file_1 256 2 256 12.
  Definition loc_584 : location_info := LocationInfo file_1 256 13 256 15.
  Definition loc_585 : location_info := LocationInfo file_1 256 14 256 15.
  Definition loc_586 : location_info := LocationInfo file_1 253 2 253 9.
  Definition loc_587 : location_info := LocationInfo file_1 253 2 253 9.
  Definition loc_588 : location_info := LocationInfo file_1 253 10 253 12.
  Definition loc_589 : location_info := LocationInfo file_1 253 11 253 12.
  Definition loc_590 : location_info := LocationInfo file_1 253 14 253 15.
  Definition loc_591 : location_info := LocationInfo file_1 251 9 251 23.
  Definition loc_592 : location_info := LocationInfo file_1 251 9 251 16.
  Definition loc_593 : location_info := LocationInfo file_1 251 9 251 16.
  Definition loc_594 : location_info := LocationInfo file_1 251 17 251 19.
  Definition loc_595 : location_info := LocationInfo file_1 251 18 251 19.
  Definition loc_596 : location_info := LocationInfo file_1 251 21 251 22.
  Definition loc_597 : location_info := LocationInfo file_1 250 2 250 9.
  Definition loc_598 : location_info := LocationInfo file_1 250 2 250 9.
  Definition loc_599 : location_info := LocationInfo file_1 250 10 250 12.
  Definition loc_600 : location_info := LocationInfo file_1 250 11 250 12.
  Definition loc_601 : location_info := LocationInfo file_1 250 14 250 15.
  Definition loc_602 : location_info := LocationInfo file_1 247 2 247 9.
  Definition loc_603 : location_info := LocationInfo file_1 247 2 247 9.
  Definition loc_604 : location_info := LocationInfo file_1 247 10 247 12.
  Definition loc_605 : location_info := LocationInfo file_1 247 11 247 12.
  Definition loc_606 : location_info := LocationInfo file_1 247 14 247 15.
  Definition loc_607 : location_info := LocationInfo file_1 245 9 245 23.
  Definition loc_608 : location_info := LocationInfo file_1 245 9 245 16.
  Definition loc_609 : location_info := LocationInfo file_1 245 9 245 16.
  Definition loc_610 : location_info := LocationInfo file_1 245 17 245 19.
  Definition loc_611 : location_info := LocationInfo file_1 245 18 245 19.
  Definition loc_612 : location_info := LocationInfo file_1 245 21 245 22.
  Definition loc_613 : location_info := LocationInfo file_1 244 9 244 23.
  Definition loc_614 : location_info := LocationInfo file_1 244 9 244 16.
  Definition loc_615 : location_info := LocationInfo file_1 244 9 244 16.
  Definition loc_616 : location_info := LocationInfo file_1 244 17 244 19.
  Definition loc_617 : location_info := LocationInfo file_1 244 18 244 19.
  Definition loc_618 : location_info := LocationInfo file_1 244 21 244 22.
  Definition loc_619 : location_info := LocationInfo file_1 242 2 242 9.
  Definition loc_620 : location_info := LocationInfo file_1 242 2 242 9.
  Definition loc_621 : location_info := LocationInfo file_1 242 10 242 12.
  Definition loc_622 : location_info := LocationInfo file_1 242 11 242 12.
  Definition loc_623 : location_info := LocationInfo file_1 242 14 242 15.
  Definition loc_624 : location_info := LocationInfo file_1 238 2 238 3.
  Definition loc_625 : location_info := LocationInfo file_1 238 6 238 14.
  Definition loc_626 : location_info := LocationInfo file_1 238 6 238 11.
  Definition loc_627 : location_info := LocationInfo file_1 238 6 238 11.
  Definition loc_628 : location_info := LocationInfo file_1 238 12 238 13.
  Definition loc_629 : location_info := LocationInfo file_1 237 13 237 21.
  Definition loc_630 : location_info := LocationInfo file_1 237 13 237 19.
  Definition loc_631 : location_info := LocationInfo file_1 237 13 237 19.

  (* Definition of struct [__cerbty_unnamed_tag_520]. *)
  Program Definition struct___cerbty_unnamed_tag_520 := {|
    sl_members := [
      (Some "__dummy_max_align_t", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [tree]. *)
  Program Definition struct_tree := {|
    sl_members := [
      (Some "left", void*);
      (Some "right", void*);
      (Some "key", it_layout i32);
      (None, Layout 4%nat 0%nat)
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

  (* Definition of function [empty]. *)
  Definition impl_empty : function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_11 ;
        Return (LocInfoE loc_12 (NULL))
      ]> $∅
    )%E
  |}.

  (* Definition of function [init]. *)
  Definition impl_init (global_talloc : loc): function := {|
    f_args := [
      ("key", it_layout i32)
    ];
    f_local_vars := [
      ("node", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "node" <-{ PtrOp }
          LocInfoE loc_35 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_35 (Call (LocInfoE loc_37 (global_talloc)) [@{expr} LocInfoE loc_38 (i2v (layout_of struct_tree).(ly_size) size_t) ]))) ;
        locinfo: loc_16 ;
        LocInfoE loc_31 ((LocInfoE loc_32 (!{PtrOp} (LocInfoE loc_33 ("node")))) at{struct_tree} "left") <-{ PtrOp }
          LocInfoE loc_34 (NULL) ;
        locinfo: loc_17 ;
        LocInfoE loc_26 ((LocInfoE loc_27 (!{PtrOp} (LocInfoE loc_28 ("node")))) at{struct_tree} "key") <-{ IntOp i32 }
          LocInfoE loc_29 (use{IntOp i32} (LocInfoE loc_30 ("key"))) ;
        locinfo: loc_18 ;
        LocInfoE loc_22 ((LocInfoE loc_23 (!{PtrOp} (LocInfoE loc_24 ("node")))) at{struct_tree} "right") <-{ PtrOp }
          LocInfoE loc_25 (NULL) ;
        locinfo: loc_19 ;
        Return (LocInfoE loc_20 (use{PtrOp} (LocInfoE loc_21 ("node"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [node]. *)
  Definition impl_node (global_talloc : loc): function := {|
    f_args := [
      ("left", void*);
      ("key", it_layout i32);
      ("right", void*)
    ];
    f_local_vars := [
      ("node", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "node" <-{ PtrOp }
          LocInfoE loc_65 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_65 (Call (LocInfoE loc_67 (global_talloc)) [@{expr} LocInfoE loc_68 (i2v (layout_of struct_tree).(ly_size) size_t) ]))) ;
        locinfo: loc_44 ;
        LocInfoE loc_60 ((LocInfoE loc_61 (!{PtrOp} (LocInfoE loc_62 ("node")))) at{struct_tree} "left") <-{ PtrOp }
          LocInfoE loc_63 (use{PtrOp} (LocInfoE loc_64 ("left"))) ;
        locinfo: loc_45 ;
        LocInfoE loc_55 ((LocInfoE loc_56 (!{PtrOp} (LocInfoE loc_57 ("node")))) at{struct_tree} "key") <-{ IntOp i32 }
          LocInfoE loc_58 (use{IntOp i32} (LocInfoE loc_59 ("key"))) ;
        locinfo: loc_46 ;
        LocInfoE loc_50 ((LocInfoE loc_51 (!{PtrOp} (LocInfoE loc_52 ("node")))) at{struct_tree} "right") <-{ PtrOp }
          LocInfoE loc_53 (use{PtrOp} (LocInfoE loc_54 ("right"))) ;
        locinfo: loc_47 ;
        Return (LocInfoE loc_48 (use{PtrOp} (LocInfoE loc_49 ("node"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [free_tree]. *)
  Definition impl_free_tree (global_free_tree global_tfree : loc): function := {|
    f_args := [
      ("t", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_102 ;
        if{IntOp i32, None}: LocInfoE loc_102 ((LocInfoE loc_103 (use{PtrOp} (LocInfoE loc_105 (!{PtrOp} (LocInfoE loc_106 ("t")))))) !={PtrOp, PtrOp, i32} (LocInfoE loc_107 (NULL)))
        then
        locinfo: loc_75 ;
          Goto "#1"
        else
        Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_75 ;
        expr: (LocInfoE loc_75 (Call (LocInfoE loc_94 (global_free_tree)) [@{expr} LocInfoE loc_95 (&(LocInfoE loc_96 ((LocInfoE loc_97 (!{PtrOp} (LocInfoE loc_99 (!{PtrOp} (LocInfoE loc_100 ("t")))))) at{struct_tree} "left"))) ])) ;
        locinfo: loc_76 ;
        expr: (LocInfoE loc_76 (Call (LocInfoE loc_86 (global_free_tree)) [@{expr} LocInfoE loc_87 (&(LocInfoE loc_88 ((LocInfoE loc_89 (!{PtrOp} (LocInfoE loc_91 (!{PtrOp} (LocInfoE loc_92 ("t")))))) at{struct_tree} "right"))) ])) ;
        locinfo: loc_77 ;
        expr: (LocInfoE loc_77 (Call (LocInfoE loc_79 (global_tfree)) [@{expr} LocInfoE loc_80 (i2v (layout_of struct_tree).(ly_size) size_t) ;
        LocInfoE loc_81 (use{PtrOp} (LocInfoE loc_83 (!{PtrOp} (LocInfoE loc_84 ("t"))))) ])) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [member_rec]. *)
  Definition impl_member_rec (global_member_rec : loc): function := {|
    f_args := [
      ("t", void*);
      ("k", it_layout i32)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_162 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_162 ((LocInfoE loc_163 (use{PtrOp} (LocInfoE loc_165 (!{PtrOp} (LocInfoE loc_166 ("t")))))) ={PtrOp, PtrOp, i32} (LocInfoE loc_167 (NULL)))
        then
        locinfo: loc_159 ;
          Goto "#8"
        else
        locinfo: loc_150 ;
          Goto "#9"
      ]> $
      <[ "#1" :=
        locinfo: loc_150 ;
        if{IntOp i32, Some "#2"}: LocInfoE loc_150 ((LocInfoE loc_151 (use{IntOp i32} (LocInfoE loc_152 ((LocInfoE loc_153 (!{PtrOp} (LocInfoE loc_155 (!{PtrOp} (LocInfoE loc_156 ("t")))))) at{struct_tree} "key")))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_157 (use{IntOp i32} (LocInfoE loc_158 ("k")))))
        then
        locinfo: loc_147 ;
          Goto "#6"
        else
        locinfo: loc_138 ;
          Goto "#7"
      ]> $
      <[ "#2" :=
        locinfo: loc_138 ;
        if{IntOp i32, Some "#3"}: LocInfoE loc_138 ((LocInfoE loc_139 (use{IntOp i32} (LocInfoE loc_140 ("k")))) <{IntOp i32, IntOp i32, i32} (LocInfoE loc_141 (use{IntOp i32} (LocInfoE loc_142 ((LocInfoE loc_143 (!{PtrOp} (LocInfoE loc_145 (!{PtrOp} (LocInfoE loc_146 ("t")))))) at{struct_tree} "key")))))
        then
        locinfo: loc_125 ;
          Goto "#4"
        else
        locinfo: loc_113 ;
          Goto "#5"
      ]> $
      <[ "#3" :=
        locinfo: loc_113 ;
        Return (LocInfoE loc_114 (Call (LocInfoE loc_116 (global_member_rec)) [@{expr} LocInfoE loc_117 (&(LocInfoE loc_118 ((LocInfoE loc_119 (!{PtrOp} (LocInfoE loc_121 (!{PtrOp} (LocInfoE loc_122 ("t")))))) at{struct_tree} "right"))) ;
               LocInfoE loc_123 (use{IntOp i32} (LocInfoE loc_124 ("k"))) ]))
      ]> $
      <[ "#4" :=
        locinfo: loc_125 ;
        Return (LocInfoE loc_126 (Call (LocInfoE loc_128 (global_member_rec)) [@{expr} LocInfoE loc_129 (&(LocInfoE loc_130 ((LocInfoE loc_131 (!{PtrOp} (LocInfoE loc_133 (!{PtrOp} (LocInfoE loc_134 ("t")))))) at{struct_tree} "left"))) ;
               LocInfoE loc_135 (use{IntOp i32} (LocInfoE loc_136 ("k"))) ]))
      ]> $
      <[ "#5" :=
        locinfo: loc_113 ;
        Goto "#3"
      ]> $
      <[ "#6" :=
        locinfo: loc_147 ;
        Return (LocInfoE loc_148 (UnOp (CastOp $ BoolOp) (IntOp i32) (LocInfoE loc_148 (i2v 1 i32))))
      ]> $
      <[ "#7" :=
        locinfo: loc_138 ;
        Goto "#2"
      ]> $
      <[ "#8" :=
        locinfo: loc_159 ;
        Return (LocInfoE loc_160 (UnOp (CastOp $ BoolOp) (IntOp i32) (LocInfoE loc_160 (i2v 0 i32))))
      ]> $
      <[ "#9" :=
        locinfo: loc_150 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [member]. *)
  Definition impl_member : function := {|
    f_args := [
      ("t", void*);
      ("k", it_layout i32)
    ];
    f_local_vars := [
      ("cur", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "cur" <-{ PtrOp }
          LocInfoE loc_222 (&(LocInfoE loc_224 (!{PtrOp} (LocInfoE loc_225 ("t"))))) ;
        locinfo: loc_171 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_216 ;
        if{IntOp i32, None}: LocInfoE loc_216 ((LocInfoE loc_217 (use{PtrOp} (LocInfoE loc_219 (!{PtrOp} (LocInfoE loc_220 ("cur")))))) !={PtrOp, PtrOp, i32} (LocInfoE loc_221 (NULL)))
        then
        locinfo: loc_207 ;
          Goto "#2"
        else
        locinfo: loc_172 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_207 ;
        if{IntOp i32, Some "#4"}: LocInfoE loc_207 ((LocInfoE loc_208 (use{IntOp i32} (LocInfoE loc_209 ((LocInfoE loc_210 (!{PtrOp} (LocInfoE loc_212 (!{PtrOp} (LocInfoE loc_213 ("cur")))))) at{struct_tree} "key")))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_214 (use{IntOp i32} (LocInfoE loc_215 ("k")))))
        then
        locinfo: loc_204 ;
          Goto "#7"
        else
        locinfo: loc_195 ;
          Goto "#8"
      ]> $
      <[ "#3" :=
        locinfo: loc_172 ;
        Return (LocInfoE loc_173 (UnOp (CastOp $ BoolOp) (IntOp i32) (LocInfoE loc_173 (i2v 0 i32))))
      ]> $
      <[ "#4" :=
        locinfo: loc_195 ;
        if{IntOp i32, None}: LocInfoE loc_195 ((LocInfoE loc_196 (use{IntOp i32} (LocInfoE loc_197 ("k")))) <{IntOp i32, IntOp i32, i32} (LocInfoE loc_198 (use{IntOp i32} (LocInfoE loc_199 ((LocInfoE loc_200 (!{PtrOp} (LocInfoE loc_202 (!{PtrOp} (LocInfoE loc_203 ("cur")))))) at{struct_tree} "key")))))
        then
        locinfo: loc_178 ;
          Goto "#5"
        else
        locinfo: loc_187 ;
          Goto "#6"
      ]> $
      <[ "#5" :=
        locinfo: loc_178 ;
        LocInfoE loc_179 ("cur") <-{ PtrOp }
          LocInfoE loc_180 (&(LocInfoE loc_181 ((LocInfoE loc_182 (!{PtrOp} (LocInfoE loc_184 (!{PtrOp} (LocInfoE loc_185 ("cur")))))) at{struct_tree} "left"))) ;
        locinfo: loc_171 ;
        Goto "#1"
      ]> $
      <[ "#6" :=
        locinfo: loc_187 ;
        LocInfoE loc_188 ("cur") <-{ PtrOp }
          LocInfoE loc_189 (&(LocInfoE loc_190 ((LocInfoE loc_191 (!{PtrOp} (LocInfoE loc_193 (!{PtrOp} (LocInfoE loc_194 ("cur")))))) at{struct_tree} "right"))) ;
        locinfo: loc_171 ;
        Goto "#1"
      ]> $
      <[ "#7" :=
        locinfo: loc_204 ;
        Return (LocInfoE loc_205 (UnOp (CastOp $ BoolOp) (IntOp i32) (LocInfoE loc_205 (i2v 1 i32))))
      ]> $
      <[ "#8" :=
        locinfo: loc_195 ;
        Goto "#4"
      ]> $∅
    )%E
  |}.

  (* Definition of function [insert_rec]. *)
  Definition impl_insert_rec (global_insert_rec global_node : loc): function := {|
    f_args := [
      ("t", void*);
      ("k", it_layout i32)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_291 ;
        if{IntOp i32, None}: LocInfoE loc_291 ((LocInfoE loc_292 (use{PtrOp} (LocInfoE loc_294 (!{PtrOp} (LocInfoE loc_295 ("t")))))) ={PtrOp, PtrOp, i32} (LocInfoE loc_296 (NULL)))
        then
        locinfo: loc_232 ;
          Goto "#1"
        else
        locinfo: loc_282 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_232 ;
        LocInfoE loc_234 (!{PtrOp} (LocInfoE loc_235 ("t"))) <-{ PtrOp }
          LocInfoE loc_236 (Call (LocInfoE loc_238 (global_node)) [@{expr} LocInfoE loc_239 (NULL) ;
          LocInfoE loc_240 (use{IntOp i32} (LocInfoE loc_241 ("k"))) ;
          LocInfoE loc_242 (NULL) ]) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_282 ;
        if{IntOp i32, Some "#3"}: LocInfoE loc_282 ((LocInfoE loc_283 (use{IntOp i32} (LocInfoE loc_284 ((LocInfoE loc_285 (!{PtrOp} (LocInfoE loc_287 (!{PtrOp} (LocInfoE loc_288 ("t")))))) at{struct_tree} "key")))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_289 (use{IntOp i32} (LocInfoE loc_290 ("k")))))
        then
        locinfo: loc_279 ;
          Goto "#6"
        else
        locinfo: loc_270 ;
          Goto "#7"
      ]> $
      <[ "#3" :=
        locinfo: loc_270 ;
        if{IntOp i32, None}: LocInfoE loc_270 ((LocInfoE loc_271 (use{IntOp i32} (LocInfoE loc_272 ("k")))) <{IntOp i32, IntOp i32, i32} (LocInfoE loc_273 (use{IntOp i32} (LocInfoE loc_274 ((LocInfoE loc_275 (!{PtrOp} (LocInfoE loc_277 (!{PtrOp} (LocInfoE loc_278 ("t")))))) at{struct_tree} "key")))))
        then
        locinfo: loc_247 ;
          Goto "#4"
        else
        locinfo: loc_259 ;
          Goto "#5"
      ]> $
      <[ "#4" :=
        locinfo: loc_247 ;
        expr: (LocInfoE loc_247 (Call (LocInfoE loc_249 (global_insert_rec)) [@{expr} LocInfoE loc_250 (&(LocInfoE loc_251 ((LocInfoE loc_252 (!{PtrOp} (LocInfoE loc_254 (!{PtrOp} (LocInfoE loc_255 ("t")))))) at{struct_tree} "left"))) ;
        LocInfoE loc_256 (use{IntOp i32} (LocInfoE loc_257 ("k"))) ])) ;
        Return (VOID)
      ]> $
      <[ "#5" :=
        locinfo: loc_259 ;
        expr: (LocInfoE loc_259 (Call (LocInfoE loc_261 (global_insert_rec)) [@{expr} LocInfoE loc_262 (&(LocInfoE loc_263 ((LocInfoE loc_264 (!{PtrOp} (LocInfoE loc_266 (!{PtrOp} (LocInfoE loc_267 ("t")))))) at{struct_tree} "right"))) ;
        LocInfoE loc_268 (use{IntOp i32} (LocInfoE loc_269 ("k"))) ])) ;
        Return (VOID)
      ]> $
      <[ "#6" :=
        locinfo: loc_279 ;
        Return (VOID)
      ]> $
      <[ "#7" :=
        locinfo: loc_270 ;
        Goto "#3"
      ]> $∅
    )%E
  |}.

  (* Definition of function [insert]. *)
  Definition impl_insert (global_node : loc): function := {|
    f_args := [
      ("t", void*);
      ("k", it_layout i32)
    ];
    f_local_vars := [
      ("cur", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "cur" <-{ PtrOp }
          LocInfoE loc_360 (&(LocInfoE loc_362 (!{PtrOp} (LocInfoE loc_363 ("t"))))) ;
        locinfo: loc_300 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_354 ;
        if{IntOp i32, None}: LocInfoE loc_354 ((LocInfoE loc_355 (use{PtrOp} (LocInfoE loc_357 (!{PtrOp} (LocInfoE loc_358 ("cur")))))) !={PtrOp, PtrOp, i32} (LocInfoE loc_359 (NULL)))
        then
        locinfo: loc_345 ;
          Goto "#2"
        else
        locinfo: loc_301 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_345 ;
        if{IntOp i32, Some "#4"}: LocInfoE loc_345 ((LocInfoE loc_346 (use{IntOp i32} (LocInfoE loc_347 ((LocInfoE loc_348 (!{PtrOp} (LocInfoE loc_350 (!{PtrOp} (LocInfoE loc_351 ("cur")))))) at{struct_tree} "key")))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_352 (use{IntOp i32} (LocInfoE loc_353 ("k")))))
        then
        locinfo: loc_342 ;
          Goto "#7"
        else
        locinfo: loc_333 ;
          Goto "#8"
      ]> $
      <[ "#3" :=
        locinfo: loc_301 ;
        LocInfoE loc_303 (!{PtrOp} (LocInfoE loc_304 ("cur"))) <-{ PtrOp }
          LocInfoE loc_305 (Call (LocInfoE loc_307 (global_node)) [@{expr} LocInfoE loc_308 (NULL) ;
          LocInfoE loc_309 (use{IntOp i32} (LocInfoE loc_310 ("k"))) ;
          LocInfoE loc_311 (NULL) ]) ;
        Return (VOID)
      ]> $
      <[ "#4" :=
        locinfo: loc_333 ;
        if{IntOp i32, None}: LocInfoE loc_333 ((LocInfoE loc_334 (use{IntOp i32} (LocInfoE loc_335 ("k")))) <{IntOp i32, IntOp i32, i32} (LocInfoE loc_336 (use{IntOp i32} (LocInfoE loc_337 ((LocInfoE loc_338 (!{PtrOp} (LocInfoE loc_340 (!{PtrOp} (LocInfoE loc_341 ("cur")))))) at{struct_tree} "key")))))
        then
        locinfo: loc_316 ;
          Goto "#5"
        else
        locinfo: loc_325 ;
          Goto "#6"
      ]> $
      <[ "#5" :=
        locinfo: loc_316 ;
        LocInfoE loc_317 ("cur") <-{ PtrOp }
          LocInfoE loc_318 (&(LocInfoE loc_319 ((LocInfoE loc_320 (!{PtrOp} (LocInfoE loc_322 (!{PtrOp} (LocInfoE loc_323 ("cur")))))) at{struct_tree} "left"))) ;
        locinfo: loc_300 ;
        Goto "#1"
      ]> $
      <[ "#6" :=
        locinfo: loc_325 ;
        LocInfoE loc_326 ("cur") <-{ PtrOp }
          LocInfoE loc_327 (&(LocInfoE loc_328 ((LocInfoE loc_329 (!{PtrOp} (LocInfoE loc_331 (!{PtrOp} (LocInfoE loc_332 ("cur")))))) at{struct_tree} "right"))) ;
        locinfo: loc_300 ;
        Goto "#1"
      ]> $
      <[ "#7" :=
        locinfo: loc_342 ;
        Return (VOID)
      ]> $
      <[ "#8" :=
        locinfo: loc_333 ;
        Goto "#4"
      ]> $∅
    )%E
  |}.

  (* Definition of function [tree_max]. *)
  Definition impl_tree_max (global_tree_max : loc): function := {|
    f_args := [
      ("t", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_388 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_388 ((LocInfoE loc_389 (use{PtrOp} (LocInfoE loc_390 ((LocInfoE loc_391 (!{PtrOp} (LocInfoE loc_393 (!{PtrOp} (LocInfoE loc_394 ("t")))))) at{struct_tree} "right")))) ={PtrOp, PtrOp, i32} (LocInfoE loc_395 (NULL)))
        then
        locinfo: loc_380 ;
          Goto "#2"
        else
        locinfo: loc_369 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_369 ;
        Return (LocInfoE loc_370 (Call (LocInfoE loc_372 (global_tree_max)) [@{expr} LocInfoE loc_373 (&(LocInfoE loc_374 ((LocInfoE loc_375 (!{PtrOp} (LocInfoE loc_377 (!{PtrOp} (LocInfoE loc_378 ("t")))))) at{struct_tree} "right"))) ]))
      ]> $
      <[ "#2" :=
        locinfo: loc_380 ;
        Return (LocInfoE loc_381 (use{IntOp i32} (LocInfoE loc_382 ((LocInfoE loc_383 (!{PtrOp} (LocInfoE loc_385 (!{PtrOp} (LocInfoE loc_386 ("t")))))) at{struct_tree} "key"))))
      ]> $
      <[ "#3" :=
        locinfo: loc_369 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [remove]. *)
  Definition impl_remove (global_remove global_tfree global_tree_max : loc): function := {|
    f_args := [
      ("t", void*);
      ("k", it_layout i32)
    ];
    f_local_vars := [
      ("m", it_layout i32);
      ("tmp", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_513 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_513 ((LocInfoE loc_514 (use{PtrOp} (LocInfoE loc_516 (!{PtrOp} (LocInfoE loc_517 ("t")))))) ={PtrOp, PtrOp, i32} (LocInfoE loc_518 (NULL)))
        then
        locinfo: loc_510 ;
          Goto "#8"
        else
        locinfo: loc_500 ;
          Goto "#9"
      ]> $
      <[ "#1" :=
        locinfo: loc_500 ;
        if{IntOp i32, None}: LocInfoE loc_500 ((LocInfoE loc_501 (use{IntOp i32} (LocInfoE loc_502 ("k")))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_503 (use{IntOp i32} (LocInfoE loc_504 ((LocInfoE loc_505 (!{PtrOp} (LocInfoE loc_507 (!{PtrOp} (LocInfoE loc_508 ("t")))))) at{struct_tree} "key")))))
        then
        locinfo: loc_458 ;
          Goto "#2"
        else
        locinfo: loc_491 ;
          Goto "#5"
      ]> $
      <[ "#2" :=
        locinfo: loc_458 ;
        if{IntOp i32, None}: LocInfoE loc_458 ((LocInfoE loc_459 (use{PtrOp} (LocInfoE loc_460 ((LocInfoE loc_461 (!{PtrOp} (LocInfoE loc_463 (!{PtrOp} (LocInfoE loc_464 ("t")))))) at{struct_tree} "left")))) !={PtrOp, PtrOp, i32} (LocInfoE loc_465 (NULL)))
        then
        locinfo: loc_405 ;
          Goto "#3"
        else
        locinfo: loc_436 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_405 ;
        LocInfoE loc_425 ("m") <-{ IntOp i32 }
          LocInfoE loc_426 (Call (LocInfoE loc_428 (global_tree_max)) [@{expr} LocInfoE loc_429 (&(LocInfoE loc_430 ((LocInfoE loc_431 (!{PtrOp} (LocInfoE loc_433 (!{PtrOp} (LocInfoE loc_434 ("t")))))) at{struct_tree} "left"))) ]) ;
        locinfo: loc_406 ;
        expr: (LocInfoE loc_406 (Call (LocInfoE loc_416 (global_remove)) [@{expr} LocInfoE loc_417 (&(LocInfoE loc_418 ((LocInfoE loc_419 (!{PtrOp} (LocInfoE loc_421 (!{PtrOp} (LocInfoE loc_422 ("t")))))) at{struct_tree} "left"))) ;
        LocInfoE loc_423 (use{IntOp i32} (LocInfoE loc_424 ("m"))) ])) ;
        locinfo: loc_407 ;
        LocInfoE loc_408 ((LocInfoE loc_409 (!{PtrOp} (LocInfoE loc_411 (!{PtrOp} (LocInfoE loc_412 ("t")))))) at{struct_tree} "key") <-{ IntOp i32 }
          LocInfoE loc_413 (use{IntOp i32} (LocInfoE loc_414 ("m"))) ;
        Return (VOID)
      ]> $
      <[ "#4" :=
        locinfo: loc_436 ;
        LocInfoE loc_451 ("tmp") <-{ PtrOp }
          LocInfoE loc_452 (use{PtrOp} (LocInfoE loc_453 ((LocInfoE loc_454 (!{PtrOp} (LocInfoE loc_456 (!{PtrOp} (LocInfoE loc_457 ("t")))))) at{struct_tree} "right"))) ;
        locinfo: loc_437 ;
        expr: (LocInfoE loc_437 (Call (LocInfoE loc_445 (global_tfree)) [@{expr} LocInfoE loc_446 (i2v (layout_of struct_tree).(ly_size) size_t) ;
        LocInfoE loc_447 (use{PtrOp} (LocInfoE loc_449 (!{PtrOp} (LocInfoE loc_450 ("t"))))) ])) ;
        locinfo: loc_438 ;
        LocInfoE loc_440 (!{PtrOp} (LocInfoE loc_441 ("t"))) <-{ PtrOp }
          LocInfoE loc_442 (use{PtrOp} (LocInfoE loc_443 ("tmp"))) ;
        Return (VOID)
      ]> $
      <[ "#5" :=
        locinfo: loc_491 ;
        if{IntOp i32, None}: LocInfoE loc_491 ((LocInfoE loc_492 (use{IntOp i32} (LocInfoE loc_493 ("k")))) <{IntOp i32, IntOp i32, i32} (LocInfoE loc_494 (use{IntOp i32} (LocInfoE loc_495 ((LocInfoE loc_496 (!{PtrOp} (LocInfoE loc_498 (!{PtrOp} (LocInfoE loc_499 ("t")))))) at{struct_tree} "key")))))
        then
        locinfo: loc_468 ;
          Goto "#6"
        else
        locinfo: loc_480 ;
          Goto "#7"
      ]> $
      <[ "#6" :=
        locinfo: loc_468 ;
        expr: (LocInfoE loc_468 (Call (LocInfoE loc_470 (global_remove)) [@{expr} LocInfoE loc_471 (&(LocInfoE loc_472 ((LocInfoE loc_473 (!{PtrOp} (LocInfoE loc_475 (!{PtrOp} (LocInfoE loc_476 ("t")))))) at{struct_tree} "left"))) ;
        LocInfoE loc_477 (use{IntOp i32} (LocInfoE loc_478 ("k"))) ])) ;
        Return (VOID)
      ]> $
      <[ "#7" :=
        locinfo: loc_480 ;
        expr: (LocInfoE loc_480 (Call (LocInfoE loc_482 (global_remove)) [@{expr} LocInfoE loc_483 (&(LocInfoE loc_484 ((LocInfoE loc_485 (!{PtrOp} (LocInfoE loc_487 (!{PtrOp} (LocInfoE loc_488 ("t")))))) at{struct_tree} "right"))) ;
        LocInfoE loc_489 (use{IntOp i32} (LocInfoE loc_490 ("k"))) ])) ;
        Return (VOID)
      ]> $
      <[ "#8" :=
        locinfo: loc_510 ;
        Return (VOID)
      ]> $
      <[ "#9" :=
        locinfo: loc_500 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [sempty]. *)
  Definition impl_sempty (global_empty : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_521 ;
        Return (LocInfoE loc_522 (Call (LocInfoE loc_524 (global_empty)) [@{expr}  ]))
      ]> $∅
    )%E
  |}.

  (* Definition of function [sinit]. *)
  Definition impl_sinit (global_init : loc): function := {|
    f_args := [
      ("key", it_layout i32)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_527 ;
        Return (LocInfoE loc_528 (Call (LocInfoE loc_530 (global_init)) [@{expr} LocInfoE loc_531 (use{IntOp i32} (LocInfoE loc_532 ("key"))) ]))
      ]> $∅
    )%E
  |}.

  (* Definition of function [sfree_tree]. *)
  Definition impl_sfree_tree (global_free_tree : loc): function := {|
    f_args := [
      ("t", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_535 ;
        expr: (LocInfoE loc_535 (Call (LocInfoE loc_537 (global_free_tree)) [@{expr} LocInfoE loc_538 (use{PtrOp} (LocInfoE loc_539 ("t"))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [smember]. *)
  Definition impl_smember (global_member : loc): function := {|
    f_args := [
      ("t", void*);
      ("k", it_layout i32)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_542 ;
        Return (LocInfoE loc_543 (Call (LocInfoE loc_545 (global_member)) [@{expr} LocInfoE loc_546 (use{PtrOp} (LocInfoE loc_547 ("t"))) ;
               LocInfoE loc_548 (use{IntOp i32} (LocInfoE loc_549 ("k"))) ]))
      ]> $∅
    )%E
  |}.

  (* Definition of function [sinsert]. *)
  Definition impl_sinsert (global_insert : loc): function := {|
    f_args := [
      ("t", void*);
      ("k", it_layout i32)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_552 ;
        expr: (LocInfoE loc_552 (Call (LocInfoE loc_554 (global_insert)) [@{expr} LocInfoE loc_555 (use{PtrOp} (LocInfoE loc_556 ("t"))) ;
        LocInfoE loc_557 (use{IntOp i32} (LocInfoE loc_558 ("k"))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [sremove]. *)
  Definition impl_sremove (global_remove : loc): function := {|
    f_args := [
      ("t", void*);
      ("k", it_layout i32)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_561 ;
        expr: (LocInfoE loc_561 (Call (LocInfoE loc_563 (global_remove)) [@{expr} LocInfoE loc_564 (use{PtrOp} (LocInfoE loc_565 ("t"))) ;
        LocInfoE loc_566 (use{IntOp i32} (LocInfoE loc_567 ("k"))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [main]. *)
  Definition impl_main (global_sempty global_sfree_tree global_sinit global_sinsert global_smember global_sremove : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
      ("t", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "t" <-{ PtrOp }
          LocInfoE loc_629 (Call (LocInfoE loc_631 (global_sempty)) [@{expr}  ]) ;
        locinfo: loc_571 ;
        LocInfoE loc_624 ("t") <-{ PtrOp }
          LocInfoE loc_625 (Call (LocInfoE loc_627 (global_sinit)) [@{expr} LocInfoE loc_628 (i2v 3 i32) ]) ;
        locinfo: loc_572 ;
        expr: (LocInfoE loc_572 (Call (LocInfoE loc_620 (global_sinsert)) [@{expr} LocInfoE loc_621 (&(LocInfoE loc_622 ("t"))) ;
        LocInfoE loc_623 (i2v 2 i32) ])) ;
        locinfo: loc_573 ;
        assert{BoolOp}: (LocInfoE loc_613 (Call (LocInfoE loc_615 (global_smember)) [@{expr} LocInfoE loc_616 (&(LocInfoE loc_617 ("t"))) ;
        LocInfoE loc_618 (i2v 2 i32) ])) ;
        locinfo: loc_574 ;
        assert{BoolOp}: (LocInfoE loc_607 (Call (LocInfoE loc_609 (global_smember)) [@{expr} LocInfoE loc_610 (&(LocInfoE loc_611 ("t"))) ;
        LocInfoE loc_612 (i2v 3 i32) ])) ;
        locinfo: loc_575 ;
        expr: (LocInfoE loc_575 (Call (LocInfoE loc_603 (global_sremove)) [@{expr} LocInfoE loc_604 (&(LocInfoE loc_605 ("t"))) ;
        LocInfoE loc_606 (i2v 3 i32) ])) ;
        locinfo: loc_576 ;
        expr: (LocInfoE loc_576 (Call (LocInfoE loc_598 (global_sinsert)) [@{expr} LocInfoE loc_599 (&(LocInfoE loc_600 ("t"))) ;
        LocInfoE loc_601 (i2v 3 i32) ])) ;
        locinfo: loc_577 ;
        assert{BoolOp}: (LocInfoE loc_591 (Call (LocInfoE loc_593 (global_smember)) [@{expr} LocInfoE loc_594 (&(LocInfoE loc_595 ("t"))) ;
        LocInfoE loc_596 (i2v 2 i32) ])) ;
        locinfo: loc_578 ;
        expr: (LocInfoE loc_578 (Call (LocInfoE loc_587 (global_sremove)) [@{expr} LocInfoE loc_588 (&(LocInfoE loc_589 ("t"))) ;
        LocInfoE loc_590 (i2v 3 i32) ])) ;
        locinfo: loc_579 ;
        expr: (LocInfoE loc_579 (Call (LocInfoE loc_583 (global_sfree_tree)) [@{expr} LocInfoE loc_584 (&(LocInfoE loc_585 ("t"))) ])) ;
        locinfo: loc_580 ;
        Return (LocInfoE loc_581 (i2v 0 i32))
      ]> $∅
    )%E
  |}.
End code.
