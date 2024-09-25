From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [linux/casestudies/pgtable.c]. *)
Section code.
  Definition file_0 : string := "linux/casestudies/pgtable.c".
  Definition file_1 : string := "include/refinedc.h".
  Definition loc_2 : location_info := LocationInfo file_1 63 2 63 47.
  Definition loc_3 : location_info := LocationInfo file_1 63 9 63 46.
  Definition loc_4 : location_info := LocationInfo file_1 63 9 63 32.
  Definition loc_5 : location_info := LocationInfo file_1 63 33 63 37.
  Definition loc_6 : location_info := LocationInfo file_1 63 33 63 37.
  Definition loc_7 : location_info := LocationInfo file_1 63 39 63 45.
  Definition loc_8 : location_info := LocationInfo file_1 63 39 63 45.
  Definition loc_11 : location_info := LocationInfo file_0 28 4 28 24.
  Definition loc_12 : location_info := LocationInfo file_0 28 11 28 23.
  Definition loc_13 : location_info := LocationInfo file_0 28 12 28 15.
  Definition loc_14 : location_info := LocationInfo file_0 28 19 28 22.
  Definition loc_15 : location_info := LocationInfo file_0 28 19 28 22.
  Definition loc_18 : location_info := LocationInfo file_0 51 4 51 84.
  Definition loc_19 : location_info := LocationInfo file_0 51 11 51 83.
  Definition loc_20 : location_info := LocationInfo file_0 51 12 51 39.
  Definition loc_21 : location_info := LocationInfo file_0 51 13 51 34.
  Definition loc_22 : location_info := LocationInfo file_0 51 13 51 19.
  Definition loc_23 : location_info := LocationInfo file_0 51 15 51 18.
  Definition loc_24 : location_info := LocationInfo file_0 51 22 51 34.
  Definition loc_25 : location_info := LocationInfo file_0 51 23 51 26.
  Definition loc_26 : location_info := LocationInfo file_0 51 30 51 33.
  Definition loc_27 : location_info := LocationInfo file_0 51 30 51 33.
  Definition loc_28 : location_info := LocationInfo file_0 51 37 51 38.
  Definition loc_29 : location_info := LocationInfo file_0 51 42 51 82.
  Definition loc_30 : location_info := LocationInfo file_0 51 43 51 47.
  Definition loc_31 : location_info := LocationInfo file_0 51 44 51 47.
  Definition loc_32 : location_info := LocationInfo file_0 51 51 51 81.
  Definition loc_33 : location_info := LocationInfo file_0 51 52 51 74.
  Definition loc_34 : location_info := LocationInfo file_0 51 52 51 70.
  Definition loc_35 : location_info := LocationInfo file_0 51 53 51 65.
  Definition loc_36 : location_info := LocationInfo file_0 51 68 51 69.
  Definition loc_37 : location_info := LocationInfo file_0 51 73 51 74.
  Definition loc_38 : location_info := LocationInfo file_0 51 77 51 80.
  Definition loc_39 : location_info := LocationInfo file_0 51 77 51 80.
  Definition loc_42 : location_info := LocationInfo file_0 83 4 83 64.
  Definition loc_43 : location_info := LocationInfo file_0 83 11 83 63.
  Definition loc_44 : location_info := LocationInfo file_0 83 12 83 30.
  Definition loc_45 : location_info := LocationInfo file_0 83 13 83 19.
  Definition loc_46 : location_info := LocationInfo file_0 83 13 83 19.
  Definition loc_47 : location_info := LocationInfo file_0 83 22 83 29.
  Definition loc_48 : location_info := LocationInfo file_0 83 22 83 29.
  Definition loc_49 : location_info := LocationInfo file_0 83 34 83 62.
  Definition loc_50 : location_info := LocationInfo file_0 83 35 83 57.
  Definition loc_51 : location_info := LocationInfo file_0 83 35 83 50.
  Definition loc_52 : location_info := LocationInfo file_0 83 35 83 50.
  Definition loc_53 : location_info := LocationInfo file_0 83 51 83 56.
  Definition loc_54 : location_info := LocationInfo file_0 83 51 83 56.
  Definition loc_55 : location_info := LocationInfo file_0 83 60 83 61.
  Definition loc_58 : location_info := LocationInfo file_0 112 4 112 62.
  Definition loc_59 : location_info := LocationInfo file_0 112 11 112 61.
  Definition loc_60 : location_info := LocationInfo file_0 112 11 112 51.
  Definition loc_61 : location_info := LocationInfo file_0 112 12 112 18.
  Definition loc_62 : location_info := LocationInfo file_0 112 12 112 18.
  Definition loc_63 : location_info := LocationInfo file_0 112 22 112 50.
  Definition loc_64 : location_info := LocationInfo file_0 112 23 112 45.
  Definition loc_65 : location_info := LocationInfo file_0 112 23 112 38.
  Definition loc_66 : location_info := LocationInfo file_0 112 23 112 38.
  Definition loc_67 : location_info := LocationInfo file_0 112 39 112 44.
  Definition loc_68 : location_info := LocationInfo file_0 112 39 112 44.
  Definition loc_69 : location_info := LocationInfo file_0 112 48 112 49.
  Definition loc_70 : location_info := LocationInfo file_0 112 54 112 61.
  Definition loc_71 : location_info := LocationInfo file_0 112 54 112 61.
  Definition loc_74 : location_info := LocationInfo file_0 202 4 202 31.
  Definition loc_75 : location_info := LocationInfo file_0 202 11 202 30.
  Definition loc_76 : location_info := LocationInfo file_0 202 11 202 12.
  Definition loc_77 : location_info := LocationInfo file_0 202 16 202 30.
  Definition loc_78 : location_info := LocationInfo file_0 202 17 202 20.
  Definition loc_79 : location_info := LocationInfo file_0 202 17 202 20.
  Definition loc_80 : location_info := LocationInfo file_0 202 23 202 29.
  Definition loc_81 : location_info := LocationInfo file_0 202 23 202 26.
  Definition loc_82 : location_info := LocationInfo file_0 202 23 202 26.
  Definition loc_83 : location_info := LocationInfo file_0 202 27 202 28.
  Definition loc_86 : location_info := LocationInfo file_0 213 4 214 17.
  Definition loc_87 : location_info := LocationInfo file_0 215 4 216 17.
  Definition loc_88 : location_info := LocationInfo file_0 217 4 217 39.
  Definition loc_89 : location_info := LocationInfo file_0 217 11 217 38.
  Definition loc_90 : location_info := LocationInfo file_0 217 11 217 33.
  Definition loc_91 : location_info := LocationInfo file_0 217 11 217 20.
  Definition loc_92 : location_info := LocationInfo file_0 217 11 217 20.
  Definition loc_93 : location_info := LocationInfo file_0 217 21 217 27.
  Definition loc_94 : location_info := LocationInfo file_0 217 21 217 24.
  Definition loc_95 : location_info := LocationInfo file_0 217 21 217 24.
  Definition loc_96 : location_info := LocationInfo file_0 217 25 217 26.
  Definition loc_97 : location_info := LocationInfo file_0 217 29 217 32.
  Definition loc_98 : location_info := LocationInfo file_0 217 29 217 32.
  Definition loc_99 : location_info := LocationInfo file_0 217 37 217 38.
  Definition loc_100 : location_info := LocationInfo file_0 216 8 216 17.
  Definition loc_101 : location_info := LocationInfo file_0 216 15 216 16.
  Definition loc_102 : location_info := LocationInfo file_0 215 4 216 17.
  Definition loc_103 : location_info := LocationInfo file_0 215 8 215 27.
  Definition loc_105 : location_info := LocationInfo file_0 215 9 215 27.
  Definition loc_106 : location_info := LocationInfo file_0 215 9 215 22.
  Definition loc_107 : location_info := LocationInfo file_0 215 9 215 22.
  Definition loc_108 : location_info := LocationInfo file_0 215 23 215 26.
  Definition loc_109 : location_info := LocationInfo file_0 215 23 215 26.
  Definition loc_110 : location_info := LocationInfo file_0 214 8 214 17.
  Definition loc_111 : location_info := LocationInfo file_0 214 15 214 16.
  Definition loc_112 : location_info := LocationInfo file_0 213 4 214 17.
  Definition loc_113 : location_info := LocationInfo file_0 213 8 213 23.
  Definition loc_114 : location_info := LocationInfo file_0 213 8 213 13.
  Definition loc_115 : location_info := LocationInfo file_0 213 8 213 13.
  Definition loc_116 : location_info := LocationInfo file_0 213 17 213 23.
  Definition loc_117 : location_info := LocationInfo file_0 213 17 213 19.
  Definition loc_118 : location_info := LocationInfo file_0 213 22 213 23.
  Definition loc_121 : location_info := LocationInfo file_0 226 4 226 26.
  Definition loc_122 : location_info := LocationInfo file_0 227 4 227 32.
  Definition loc_123 : location_info := LocationInfo file_0 227 5 227 12.
  Definition loc_124 : location_info := LocationInfo file_0 227 7 227 11.
  Definition loc_125 : location_info := LocationInfo file_0 227 7 227 11.
  Definition loc_126 : location_info := LocationInfo file_0 227 15 227 30.
  Definition loc_127 : location_info := LocationInfo file_0 227 16 227 19.
  Definition loc_128 : location_info := LocationInfo file_0 227 16 227 19.
  Definition loc_129 : location_info := LocationInfo file_0 227 22 227 29.
  Definition loc_130 : location_info := LocationInfo file_0 227 23 227 29.
  Definition loc_131 : location_info := LocationInfo file_0 227 23 227 26.
  Definition loc_132 : location_info := LocationInfo file_0 227 23 227 26.
  Definition loc_133 : location_info := LocationInfo file_0 227 27 227 28.
  Definition loc_134 : location_info := LocationInfo file_0 226 20 226 25.
  Definition loc_135 : location_info := LocationInfo file_0 226 20 226 25.
  Definition loc_136 : location_info := LocationInfo file_0 226 21 226 25.
  Definition loc_137 : location_info := LocationInfo file_0 226 21 226 25.
  Definition loc_142 : location_info := LocationInfo file_0 235 4 235 41.
  Definition loc_143 : location_info := LocationInfo file_0 237 4 238 53.
  Definition loc_144 : location_info := LocationInfo file_0 240 4 240 15.
  Definition loc_145 : location_info := LocationInfo file_0 240 11 240 14.
  Definition loc_146 : location_info := LocationInfo file_0 240 11 240 14.
  Definition loc_147 : location_info := LocationInfo file_0 238 8 238 53.
  Definition loc_148 : location_info := LocationInfo file_0 238 8 238 11.
  Definition loc_149 : location_info := LocationInfo file_0 238 8 238 52.
  Definition loc_150 : location_info := LocationInfo file_0 238 8 238 11.
  Definition loc_151 : location_info := LocationInfo file_0 238 8 238 11.
  Definition loc_152 : location_info := LocationInfo file_0 238 15 238 52.
  Definition loc_153 : location_info := LocationInfo file_0 238 15 238 25.
  Definition loc_154 : location_info := LocationInfo file_0 238 15 238 25.
  Definition loc_155 : location_info := LocationInfo file_0 238 26 238 41.
  Definition loc_156 : location_info := LocationInfo file_0 238 26 238 33.
  Definition loc_157 : location_info := LocationInfo file_0 238 26 238 33.
  Definition loc_158 : location_info := LocationInfo file_0 238 34 238 36.
  Definition loc_159 : location_info := LocationInfo file_0 238 38 238 40.
  Definition loc_160 : location_info := LocationInfo file_0 238 43 238 51.
  Definition loc_161 : location_info := LocationInfo file_0 238 43 238 45.
  Definition loc_162 : location_info := LocationInfo file_0 238 43 238 45.
  Definition loc_163 : location_info := LocationInfo file_0 238 49 238 51.
  Definition loc_164 : location_info := LocationInfo file_0 237 4 238 53.
  Definition loc_165 : location_info := LocationInfo file_0 237 8 237 16.
  Definition loc_166 : location_info := LocationInfo file_0 237 8 237 10.
  Definition loc_167 : location_info := LocationInfo file_0 237 14 237 16.
  Definition loc_168 : location_info := LocationInfo file_0 235 20 235 40.
  Definition loc_169 : location_info := LocationInfo file_0 235 20 235 22.
  Definition loc_170 : location_info := LocationInfo file_0 235 20 235 22.
  Definition loc_171 : location_info := LocationInfo file_0 235 25 235 40.
  Definition loc_172 : location_info := LocationInfo file_0 235 25 235 32.
  Definition loc_173 : location_info := LocationInfo file_0 235 25 235 32.
  Definition loc_174 : location_info := LocationInfo file_0 235 33 235 35.
  Definition loc_175 : location_info := LocationInfo file_0 235 37 235 39.
  Definition loc_180 : location_info := LocationInfo file_0 254 4 254 79.
  Definition loc_181 : location_info := LocationInfo file_0 255 4 255 33.
  Definition loc_182 : location_info := LocationInfo file_0 256 4 256 18.
  Definition loc_183 : location_info := LocationInfo file_0 257 4 257 33.
  Definition loc_184 : location_info := LocationInfo file_0 259 4 259 16.
  Definition loc_185 : location_info := LocationInfo file_0 259 4 259 9.
  Definition loc_186 : location_info := LocationInfo file_0 259 5 259 9.
  Definition loc_187 : location_info := LocationInfo file_0 259 5 259 9.
  Definition loc_188 : location_info := LocationInfo file_0 259 12 259 15.
  Definition loc_189 : location_info := LocationInfo file_0 259 12 259 15.
  Definition loc_190 : location_info := LocationInfo file_0 257 12 257 30.
  Definition loc_191 : location_info := LocationInfo file_0 257 12 257 25.
  Definition loc_192 : location_info := LocationInfo file_0 257 12 257 25.
  Definition loc_193 : location_info := LocationInfo file_0 257 26 257 29.
  Definition loc_194 : location_info := LocationInfo file_0 257 26 257 29.
  Definition loc_195 : location_info := LocationInfo file_0 256 4 256 7.
  Definition loc_196 : location_info := LocationInfo file_0 256 4 256 17.
  Definition loc_197 : location_info := LocationInfo file_0 256 4 256 7.
  Definition loc_198 : location_info := LocationInfo file_0 256 4 256 7.
  Definition loc_199 : location_info := LocationInfo file_0 256 11 256 17.
  Definition loc_200 : location_info := LocationInfo file_0 256 11 256 14.
  Definition loc_201 : location_info := LocationInfo file_0 256 11 256 14.
  Definition loc_202 : location_info := LocationInfo file_0 256 15 256 16.
  Definition loc_203 : location_info := LocationInfo file_0 255 4 255 7.
  Definition loc_204 : location_info := LocationInfo file_0 255 4 255 32.
  Definition loc_205 : location_info := LocationInfo file_0 255 4 255 7.
  Definition loc_206 : location_info := LocationInfo file_0 255 4 255 7.
  Definition loc_207 : location_info := LocationInfo file_0 255 11 255 32.
  Definition loc_208 : location_info := LocationInfo file_0 255 11 255 21.
  Definition loc_209 : location_info := LocationInfo file_0 255 11 255 21.
  Definition loc_210 : location_info := LocationInfo file_0 255 22 255 28.
  Definition loc_211 : location_info := LocationInfo file_0 255 22 255 25.
  Definition loc_212 : location_info := LocationInfo file_0 255 22 255 25.
  Definition loc_213 : location_info := LocationInfo file_0 255 26 255 27.
  Definition loc_214 : location_info := LocationInfo file_0 255 30 255 31.
  Definition loc_215 : location_info := LocationInfo file_0 254 33 254 78.
  Definition loc_216 : location_info := LocationInfo file_0 254 33 254 48.
  Definition loc_217 : location_info := LocationInfo file_0 254 33 254 48.
  Definition loc_218 : location_info := LocationInfo file_0 254 49 254 77.
  Definition loc_219 : location_info := LocationInfo file_0 254 49 254 69.
  Definition loc_220 : location_info := LocationInfo file_0 254 49 254 69.
  Definition loc_221 : location_info := LocationInfo file_0 254 49 254 69.
  Definition loc_222 : location_info := LocationInfo file_0 254 49 254 55.
  Definition loc_223 : location_info := LocationInfo file_0 254 49 254 55.
  Definition loc_224 : location_info := LocationInfo file_0 254 70 254 76.
  Definition loc_225 : location_info := LocationInfo file_0 254 70 254 76.
  Definition loc_228 : location_info := LocationInfo file_0 254 20 254 25.
  Definition loc_229 : location_info := LocationInfo file_0 254 20 254 25.
  Definition loc_230 : location_info := LocationInfo file_0 254 21 254 25.
  Definition loc_231 : location_info := LocationInfo file_0 254 21 254 25.
  Definition loc_236 : location_info := LocationInfo file_0 273 4 273 53.
  Definition loc_237 : location_info := LocationInfo file_0 274 4 275 33.
  Definition loc_238 : location_info := LocationInfo file_0 276 4 276 53.
  Definition loc_239 : location_info := LocationInfo file_0 277 4 277 36.
  Definition loc_240 : location_info := LocationInfo file_0 278 4 278 18.
  Definition loc_241 : location_info := LocationInfo file_0 280 4 281 26.
  Definition loc_242 : location_info := LocationInfo file_0 283 4 283 16.
  Definition loc_243 : location_info := LocationInfo file_0 284 4 284 13.
  Definition loc_244 : location_info := LocationInfo file_0 284 11 284 12.
  Definition loc_245 : location_info := LocationInfo file_0 283 4 283 9.
  Definition loc_246 : location_info := LocationInfo file_0 283 5 283 9.
  Definition loc_247 : location_info := LocationInfo file_0 283 5 283 9.
  Definition loc_248 : location_info := LocationInfo file_0 283 12 283 15.
  Definition loc_249 : location_info := LocationInfo file_0 283 12 283 15.
  Definition loc_250 : location_info := LocationInfo file_0 281 8 281 26.
  Definition loc_251 : location_info := LocationInfo file_0 281 15 281 25.
  Definition loc_252 : location_info := LocationInfo file_0 281 15 281 18.
  Definition loc_253 : location_info := LocationInfo file_0 281 15 281 18.
  Definition loc_254 : location_info := LocationInfo file_0 281 22 281 25.
  Definition loc_255 : location_info := LocationInfo file_0 281 22 281 25.
  Definition loc_256 : location_info := LocationInfo file_0 280 4 281 26.
  Definition loc_257 : location_info := LocationInfo file_0 280 8 280 26.
  Definition loc_258 : location_info := LocationInfo file_0 280 8 280 21.
  Definition loc_259 : location_info := LocationInfo file_0 280 8 280 21.
  Definition loc_260 : location_info := LocationInfo file_0 280 22 280 25.
  Definition loc_261 : location_info := LocationInfo file_0 280 22 280 25.
  Definition loc_262 : location_info := LocationInfo file_0 278 4 278 7.
  Definition loc_263 : location_info := LocationInfo file_0 278 4 278 17.
  Definition loc_264 : location_info := LocationInfo file_0 278 4 278 7.
  Definition loc_265 : location_info := LocationInfo file_0 278 4 278 7.
  Definition loc_266 : location_info := LocationInfo file_0 278 11 278 17.
  Definition loc_267 : location_info := LocationInfo file_0 278 11 278 14.
  Definition loc_268 : location_info := LocationInfo file_0 278 11 278 14.
  Definition loc_269 : location_info := LocationInfo file_0 278 15 278 16.
  Definition loc_270 : location_info := LocationInfo file_0 277 4 277 7.
  Definition loc_271 : location_info := LocationInfo file_0 277 4 277 35.
  Definition loc_272 : location_info := LocationInfo file_0 277 4 277 7.
  Definition loc_273 : location_info := LocationInfo file_0 277 4 277 7.
  Definition loc_274 : location_info := LocationInfo file_0 277 11 277 35.
  Definition loc_275 : location_info := LocationInfo file_0 277 11 277 21.
  Definition loc_276 : location_info := LocationInfo file_0 277 11 277 21.
  Definition loc_277 : location_info := LocationInfo file_0 277 22 277 28.
  Definition loc_278 : location_info := LocationInfo file_0 277 22 277 25.
  Definition loc_279 : location_info := LocationInfo file_0 277 22 277 25.
  Definition loc_280 : location_info := LocationInfo file_0 277 26 277 27.
  Definition loc_281 : location_info := LocationInfo file_0 277 30 277 34.
  Definition loc_282 : location_info := LocationInfo file_0 277 30 277 34.
  Definition loc_283 : location_info := LocationInfo file_0 276 4 276 7.
  Definition loc_284 : location_info := LocationInfo file_0 276 4 276 52.
  Definition loc_285 : location_info := LocationInfo file_0 276 4 276 7.
  Definition loc_286 : location_info := LocationInfo file_0 276 4 276 7.
  Definition loc_287 : location_info := LocationInfo file_0 276 11 276 52.
  Definition loc_288 : location_info := LocationInfo file_0 276 11 276 15.
  Definition loc_289 : location_info := LocationInfo file_0 276 11 276 15.
  Definition loc_290 : location_info := LocationInfo file_0 276 18 276 52.
  Definition loc_291 : location_info := LocationInfo file_0 276 19 276 33.
  Definition loc_292 : location_info := LocationInfo file_0 276 19 276 26.
  Definition loc_293 : location_info := LocationInfo file_0 276 19 276 26.
  Definition loc_294 : location_info := LocationInfo file_0 276 27 276 29.
  Definition loc_295 : location_info := LocationInfo file_0 276 31 276 32.
  Definition loc_296 : location_info := LocationInfo file_0 276 36 276 51.
  Definition loc_297 : location_info := LocationInfo file_0 276 36 276 43.
  Definition loc_298 : location_info := LocationInfo file_0 276 36 276 43.
  Definition loc_299 : location_info := LocationInfo file_0 276 44 276 46.
  Definition loc_300 : location_info := LocationInfo file_0 276 48 276 50.
  Definition loc_301 : location_info := LocationInfo file_0 274 15 275 32.
  Definition loc_302 : location_info := LocationInfo file_0 274 15 274 32.
  Definition loc_303 : location_info := LocationInfo file_0 274 16 274 21.
  Definition loc_304 : location_info := LocationInfo file_0 274 16 274 21.
  Definition loc_305 : location_info := LocationInfo file_0 274 25 274 31.
  Definition loc_306 : location_info := LocationInfo file_0 274 25 274 27.
  Definition loc_307 : location_info := LocationInfo file_0 274 30 274 31.
  Definition loc_308 : location_info := LocationInfo file_0 274 35 274 36.
  Definition loc_309 : location_info := LocationInfo file_0 275 31 275 32.
  Definition loc_312 : location_info := LocationInfo file_0 273 33 273 52.
  Definition loc_313 : location_info := LocationInfo file_0 273 33 273 48.
  Definition loc_314 : location_info := LocationInfo file_0 273 33 273 48.
  Definition loc_315 : location_info := LocationInfo file_0 273 49 273 51.
  Definition loc_316 : location_info := LocationInfo file_0 273 49 273 51.
  Definition loc_319 : location_info := LocationInfo file_0 273 20 273 25.
  Definition loc_320 : location_info := LocationInfo file_0 273 20 273 25.
  Definition loc_321 : location_info := LocationInfo file_0 273 21 273 25.
  Definition loc_322 : location_info := LocationInfo file_0 273 21 273 25.
  Definition loc_327 : location_info := LocationInfo file_0 311 4 311 40.
  Definition loc_328 : location_info := LocationInfo file_0 312 4 312 31.
  Definition loc_329 : location_info := LocationInfo file_0 313 4 313 54.
  Definition loc_330 : location_info := LocationInfo file_0 314 4 314 15.
  Definition loc_331 : location_info := LocationInfo file_0 315 4 316 29.
  Definition loc_332 : location_info := LocationInfo file_0 317 4 318 19.
  Definition loc_333 : location_info := LocationInfo file_0 319 4 326 5.
  Definition loc_334 : location_info := LocationInfo file_0 327 4 327 42.
  Definition loc_335 : location_info := LocationInfo file_0 328 4 328 42.
  Definition loc_336 : location_info := LocationInfo file_0 329 4 329 20.
  Definition loc_337 : location_info := LocationInfo file_0 330 4 330 22.
  Definition loc_338 : location_info := LocationInfo file_0 331 4 331 13.
  Definition loc_339 : location_info := LocationInfo file_0 331 11 331 12.
  Definition loc_340 : location_info := LocationInfo file_0 330 4 330 14.
  Definition loc_341 : location_info := LocationInfo file_0 330 4 330 8.
  Definition loc_342 : location_info := LocationInfo file_0 330 4 330 8.
  Definition loc_343 : location_info := LocationInfo file_0 330 17 330 21.
  Definition loc_344 : location_info := LocationInfo file_0 330 17 330 21.
  Definition loc_345 : location_info := LocationInfo file_0 329 4 329 8.
  Definition loc_346 : location_info := LocationInfo file_0 329 4 329 19.
  Definition loc_347 : location_info := LocationInfo file_0 329 4 329 8.
  Definition loc_348 : location_info := LocationInfo file_0 329 4 329 8.
  Definition loc_349 : location_info := LocationInfo file_0 329 12 329 19.
  Definition loc_350 : location_info := LocationInfo file_0 329 12 329 15.
  Definition loc_351 : location_info := LocationInfo file_0 329 12 329 15.
  Definition loc_352 : location_info := LocationInfo file_0 329 16 329 18.
  Definition loc_353 : location_info := LocationInfo file_0 328 4 328 8.
  Definition loc_354 : location_info := LocationInfo file_0 328 4 328 41.
  Definition loc_355 : location_info := LocationInfo file_0 328 4 328 8.
  Definition loc_356 : location_info := LocationInfo file_0 328 4 328 8.
  Definition loc_357 : location_info := LocationInfo file_0 328 12 328 41.
  Definition loc_358 : location_info := LocationInfo file_0 328 12 328 22.
  Definition loc_359 : location_info := LocationInfo file_0 328 12 328 22.
  Definition loc_360 : location_info := LocationInfo file_0 328 23 328 36.
  Definition loc_361 : location_info := LocationInfo file_0 328 23 328 30.
  Definition loc_362 : location_info := LocationInfo file_0 328 23 328 30.
  Definition loc_363 : location_info := LocationInfo file_0 328 31 328 32.
  Definition loc_364 : location_info := LocationInfo file_0 328 34 328 35.
  Definition loc_365 : location_info := LocationInfo file_0 328 38 328 40.
  Definition loc_366 : location_info := LocationInfo file_0 328 38 328 40.
  Definition loc_367 : location_info := LocationInfo file_0 327 4 327 8.
  Definition loc_368 : location_info := LocationInfo file_0 327 4 327 41.
  Definition loc_369 : location_info := LocationInfo file_0 327 4 327 8.
  Definition loc_370 : location_info := LocationInfo file_0 327 4 327 8.
  Definition loc_371 : location_info := LocationInfo file_0 327 12 327 41.
  Definition loc_372 : location_info := LocationInfo file_0 327 12 327 22.
  Definition loc_373 : location_info := LocationInfo file_0 327 12 327 22.
  Definition loc_374 : location_info := LocationInfo file_0 327 23 327 36.
  Definition loc_375 : location_info := LocationInfo file_0 327 23 327 30.
  Definition loc_376 : location_info := LocationInfo file_0 327 23 327 30.
  Definition loc_377 : location_info := LocationInfo file_0 327 31 327 32.
  Definition loc_378 : location_info := LocationInfo file_0 327 34 327 35.
  Definition loc_379 : location_info := LocationInfo file_0 327 38 327 40.
  Definition loc_380 : location_info := LocationInfo file_0 327 38 327 40.
  Definition loc_381 : location_info := LocationInfo file_0 319 23 324 5.
  Definition loc_382 : location_info := LocationInfo file_0 320 8 321 23.
  Definition loc_383 : location_info := LocationInfo file_0 322 8 323 23.
  Definition loc_384 : location_info := LocationInfo file_0 323 12 323 23.
  Definition loc_385 : location_info := LocationInfo file_0 323 19 323 22.
  Definition loc_386 : location_info := LocationInfo file_0 323 20 323 22.
  Definition loc_387 : location_info := LocationInfo file_0 322 8 323 23.
  Definition loc_388 : location_info := LocationInfo file_0 322 12 322 18.
  Definition loc_389 : location_info := LocationInfo file_0 322 12 322 18.
  Definition loc_390 : location_info := LocationInfo file_0 321 12 321 23.
  Definition loc_391 : location_info := LocationInfo file_0 321 19 321 22.
  Definition loc_392 : location_info := LocationInfo file_0 321 20 321 22.
  Definition loc_393 : location_info := LocationInfo file_0 320 8 321 23.
  Definition loc_394 : location_info := LocationInfo file_0 320 12 320 25.
  Definition loc_395 : location_info := LocationInfo file_0 320 12 320 16.
  Definition loc_396 : location_info := LocationInfo file_0 320 12 320 16.
  Definition loc_397 : location_info := LocationInfo file_0 320 19 320 25.
  Definition loc_398 : location_info := LocationInfo file_0 320 19 320 22.
  Definition loc_399 : location_info := LocationInfo file_0 320 19 320 22.
  Definition loc_400 : location_info := LocationInfo file_0 320 23 320 24.
  Definition loc_401 : location_info := LocationInfo file_0 324 11 326 5.
  Definition loc_402 : location_info := LocationInfo file_0 325 8 325 24.
  Definition loc_403 : location_info := LocationInfo file_0 325 8 325 12.
  Definition loc_404 : location_info := LocationInfo file_0 325 8 325 23.
  Definition loc_405 : location_info := LocationInfo file_0 325 8 325 12.
  Definition loc_406 : location_info := LocationInfo file_0 325 8 325 12.
  Definition loc_407 : location_info := LocationInfo file_0 325 16 325 23.
  Definition loc_408 : location_info := LocationInfo file_0 325 16 325 19.
  Definition loc_409 : location_info := LocationInfo file_0 325 16 325 19.
  Definition loc_410 : location_info := LocationInfo file_0 325 20 325 22.
  Definition loc_411 : location_info := LocationInfo file_0 319 8 319 21.
  Definition loc_412 : location_info := LocationInfo file_0 319 8 319 12.
  Definition loc_413 : location_info := LocationInfo file_0 319 8 319 12.
  Definition loc_414 : location_info := LocationInfo file_0 319 15 319 21.
  Definition loc_415 : location_info := LocationInfo file_0 319 15 319 18.
  Definition loc_416 : location_info := LocationInfo file_0 319 15 319 18.
  Definition loc_417 : location_info := LocationInfo file_0 319 19 319 20.
  Definition loc_418 : location_info := LocationInfo file_0 318 8 318 19.
  Definition loc_419 : location_info := LocationInfo file_0 318 15 318 18.
  Definition loc_420 : location_info := LocationInfo file_0 318 16 318 18.
  Definition loc_421 : location_info := LocationInfo file_0 317 4 318 19.
  Definition loc_422 : location_info := LocationInfo file_0 317 8 317 24.
  Definition loc_424 : location_info := LocationInfo file_0 317 9 317 24.
  Definition loc_425 : location_info := LocationInfo file_0 317 10 317 14.
  Definition loc_426 : location_info := LocationInfo file_0 317 10 317 14.
  Definition loc_427 : location_info := LocationInfo file_0 317 17 317 23.
  Definition loc_428 : location_info := LocationInfo file_0 317 17 317 20.
  Definition loc_429 : location_info := LocationInfo file_0 317 17 317 20.
  Definition loc_430 : location_info := LocationInfo file_0 317 21 317 22.
  Definition loc_431 : location_info := LocationInfo file_0 315 13 316 28.
  Definition loc_432 : location_info := LocationInfo file_0 315 13 315 28.
  Definition loc_433 : location_info := LocationInfo file_0 315 14 315 18.
  Definition loc_434 : location_info := LocationInfo file_0 315 14 315 18.
  Definition loc_435 : location_info := LocationInfo file_0 315 21 315 27.
  Definition loc_436 : location_info := LocationInfo file_0 315 21 315 24.
  Definition loc_437 : location_info := LocationInfo file_0 315 21 315 24.
  Definition loc_438 : location_info := LocationInfo file_0 315 25 315 26.
  Definition loc_439 : location_info := LocationInfo file_0 315 31 315 32.
  Definition loc_440 : location_info := LocationInfo file_0 316 27 316 28.
  Definition loc_443 : location_info := LocationInfo file_0 314 13 314 14.
  Definition loc_446 : location_info := LocationInfo file_0 313 21 313 53.
  Definition loc_447 : location_info := LocationInfo file_0 313 21 313 31.
  Definition loc_448 : location_info := LocationInfo file_0 313 21 313 31.
  Definition loc_449 : location_info := LocationInfo file_0 313 32 313 45.
  Definition loc_450 : location_info := LocationInfo file_0 313 32 313 39.
  Definition loc_451 : location_info := LocationInfo file_0 313 32 313 39.
  Definition loc_452 : location_info := LocationInfo file_0 313 40 313 41.
  Definition loc_453 : location_info := LocationInfo file_0 313 43 313 44.
  Definition loc_454 : location_info := LocationInfo file_0 313 47 313 52.
  Definition loc_455 : location_info := LocationInfo file_0 313 47 313 52.
  Definition loc_458 : location_info := LocationInfo file_0 312 16 312 30.
  Definition loc_459 : location_info := LocationInfo file_0 312 16 312 22.
  Definition loc_460 : location_info := LocationInfo file_0 312 16 312 22.
  Definition loc_461 : location_info := LocationInfo file_0 312 25 312 26.
  Definition loc_462 : location_info := LocationInfo file_0 312 29 312 30.
  Definition loc_465 : location_info := LocationInfo file_0 311 19 311 39.
  Definition loc_466 : location_info := LocationInfo file_0 311 19 311 20.
  Definition loc_467 : location_info := LocationInfo file_0 311 24 311 39.
  Definition loc_468 : location_info := LocationInfo file_0 311 25 311 29.
  Definition loc_469 : location_info := LocationInfo file_0 311 25 311 29.
  Definition loc_470 : location_info := LocationInfo file_0 311 32 311 38.
  Definition loc_471 : location_info := LocationInfo file_0 311 32 311 35.
  Definition loc_472 : location_info := LocationInfo file_0 311 32 311 35.
  Definition loc_473 : location_info := LocationInfo file_0 311 36 311 37.

  (* Definition of struct [__cerbty_unnamed_tag_486]. *)
  Program Definition struct___cerbty_unnamed_tag_486 := {|
    sl_members := [
      (Some "__dummy_max_align_t", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [kvm_pgtable_mm_ops]. *)
  Program Definition struct_kvm_pgtable_mm_ops := {|
    sl_members := [
      (Some "virt_to_phys", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [hyp_map_data]. *)
  Program Definition struct_hyp_map_data := {|
    sl_members := [
      (Some "phys", it_layout u64);
      (Some "attr", it_layout u64);
      (Some "mm_ops", void*)
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

  (* Definition of function [BIT]. *)
  Definition impl_BIT : function := {|
    f_args := [
      ("i", it_layout i32)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_11 ;
        Return (LocInfoE loc_12 ((LocInfoE loc_13 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_14 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_14 (use{IntOp i32} (LocInfoE loc_15 ("i"))))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [GENMASK]. *)
  Definition impl_GENMASK : function := {|
    f_args := [
      ("h", it_layout i32);
      ("l", it_layout i32)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_18 ;
        Return (LocInfoE loc_19 ((LocInfoE loc_20 ((LocInfoE loc_21 ((LocInfoE loc_22 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_23 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_24 ((LocInfoE loc_25 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_26 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_26 (use{IntOp i32} (LocInfoE loc_27 ("l")))))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_28 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_28 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_29 ((LocInfoE loc_30 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_31 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_32 (UnOp (CastOp $ IntOp u64) (IntOp size_t) (LocInfoE loc_32 ((LocInfoE loc_33 ((LocInfoE loc_34 ((LocInfoE loc_35 (i2v (it_layout i64).(ly_size) size_t)) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_36 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_36 (i2v 8 i32)))))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_37 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_37 (i2v 1 i32)))))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_38 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_38 (use{IntOp i32} (LocInfoE loc_39 ("h"))))))))))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [FIELD_GET]. *)
  Definition impl_FIELD_GET (global___builtin_ffsll : loc): function := {|
    f_args := [
      ("_mask", it_layout u64);
      ("_reg", it_layout u64)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_42 ;
        Return (LocInfoE loc_43 ((LocInfoE loc_44 ((LocInfoE loc_45 (use{IntOp u64} (LocInfoE loc_46 ("_reg")))) &{IntOp u64, IntOp u64} (LocInfoE loc_47 (use{IntOp u64} (LocInfoE loc_48 ("_mask")))))) >>{IntOp u64, IntOp u64} (LocInfoE loc_49 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_49 ((LocInfoE loc_50 (Call (LocInfoE loc_52 (global___builtin_ffsll)) [@{expr} LocInfoE loc_53 (use{IntOp u64} (LocInfoE loc_54 ("_mask"))) ])) -{IntOp i32, IntOp i32} (LocInfoE loc_55 (i2v 1 i32))))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [FIELD_PREP]. *)
  Definition impl_FIELD_PREP (global___builtin_ffsll : loc): function := {|
    f_args := [
      ("_mask", it_layout u64);
      ("_val", it_layout u64)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_58 ;
        Return (LocInfoE loc_59 ((LocInfoE loc_60 ((LocInfoE loc_61 (use{IntOp u64} (LocInfoE loc_62 ("_val")))) <<{IntOp u64, IntOp u64} (LocInfoE loc_63 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_63 ((LocInfoE loc_64 (Call (LocInfoE loc_66 (global___builtin_ffsll)) [@{expr} LocInfoE loc_67 (use{IntOp u64} (LocInfoE loc_68 ("_mask"))) ])) -{IntOp i32, IntOp i32} (LocInfoE loc_69 (i2v 1 i32)))))))) &{IntOp u64, IntOp u64} (LocInfoE loc_70 (use{IntOp u64} (LocInfoE loc_71 ("_mask"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [kvm_pte_valid]. *)
  Definition impl_kvm_pte_valid (global_BIT : loc): function := {|
    f_args := [
      ("pte", it_layout u64)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_74 ;
        Return (LocInfoE loc_75 (UnOp (CastOp $ BoolOp) (IntOp i32) (LocInfoE loc_75 ((LocInfoE loc_76 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_76 (i2v 0 i32)))) !={IntOp u64, IntOp u64, i32} (LocInfoE loc_77 ((LocInfoE loc_78 (use{IntOp u64} (LocInfoE loc_79 ("pte")))) &{IntOp u64, IntOp u64} (LocInfoE loc_80 (Call (LocInfoE loc_82 (global_BIT)) [@{expr} LocInfoE loc_83 (i2v 0 i32) ]))))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [kvm_pte_table]. *)
  Definition impl_kvm_pte_table (global_BIT global_FIELD_GET global_kvm_pte_valid : loc): function := {|
    f_args := [
      ("pte", it_layout u64);
      ("level", it_layout u32)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_113 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_113 ((LocInfoE loc_114 (use{IntOp u32} (LocInfoE loc_115 ("level")))) ={IntOp u32, IntOp u32, i32} (LocInfoE loc_116 ((LocInfoE loc_117 (i2v 4 u32)) -{IntOp u32, IntOp u32} (LocInfoE loc_118 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_118 (i2v 1 i32)))))))
        then
        locinfo: loc_110 ;
          Goto "#5"
        else
        locinfo: loc_103 ;
          Goto "#6"
      ]> $
      <[ "#1" :=
        locinfo: loc_103 ;
        if{IntOp i32, Some "#2"}: LocInfoE loc_103 ((i2v 0 i32) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_105 (UnOp (CastOp $ IntOp i32) (BoolOp) (LocInfoE loc_105 (Call (LocInfoE loc_107 (global_kvm_pte_valid)) [@{expr} LocInfoE loc_108 (use{IntOp u64} (LocInfoE loc_109 ("pte"))) ])))))
        then
        locinfo: loc_100 ;
          Goto "#3"
        else
        locinfo: loc_88 ;
          Goto "#4"
      ]> $
      <[ "#2" :=
        locinfo: loc_88 ;
        Return (LocInfoE loc_89 (UnOp (CastOp $ BoolOp) (IntOp i32) (LocInfoE loc_89 ((LocInfoE loc_90 (Call (LocInfoE loc_92 (global_FIELD_GET)) [@{expr} LocInfoE loc_93 (Call (LocInfoE loc_95 (global_BIT)) [@{expr} LocInfoE loc_96 (i2v 1 i32) ]) ;
               LocInfoE loc_97 (use{IntOp u64} (LocInfoE loc_98 ("pte"))) ])) ={IntOp u64, IntOp u64, i32} (LocInfoE loc_99 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_99 (i2v 1 i32))))))))
      ]> $
      <[ "#3" :=
        locinfo: loc_100 ;
        Return (LocInfoE loc_101 (UnOp (CastOp $ BoolOp) (IntOp i32) (LocInfoE loc_101 (i2v 0 i32))))
      ]> $
      <[ "#4" :=
        locinfo: loc_88 ;
        Goto "#2"
      ]> $
      <[ "#5" :=
        locinfo: loc_110 ;
        Return (LocInfoE loc_111 (UnOp (CastOp $ BoolOp) (IntOp i32) (LocInfoE loc_111 (i2v 0 i32))))
      ]> $
      <[ "#6" :=
        locinfo: loc_103 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [kvm_set_invalid_pte]. *)
  Definition impl_kvm_set_invalid_pte (global_BIT : loc): function := {|
    f_args := [
      ("ptep", void*)
    ];
    f_local_vars := [
      ("pte", it_layout u64)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "pte" <-{ IntOp u64 }
          LocInfoE loc_134 (use{IntOp u64} (LocInfoE loc_136 (!{PtrOp} (LocInfoE loc_137 ("ptep"))))) ;
        locinfo: loc_122 ;
        LocInfoE loc_124 (!{PtrOp} (LocInfoE loc_125 ("ptep"))) <-{ IntOp u64 }
          LocInfoE loc_126 ((LocInfoE loc_127 (use{IntOp u64} (LocInfoE loc_128 ("pte")))) &{IntOp u64, IntOp u64} (LocInfoE loc_129 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_130 (Call (LocInfoE loc_132 (global_BIT)) [@{expr} LocInfoE loc_133 (i2v 0 i32) ]))))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [kvm_phys_to_pte]. *)
  Definition impl_kvm_phys_to_pte (global_FIELD_PREP global_GENMASK : loc): function := {|
    f_args := [
      ("pa", it_layout u64)
    ];
    f_local_vars := [
      ("pte", it_layout u64)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "pte" <-{ IntOp u64 }
          LocInfoE loc_168 ((LocInfoE loc_169 (use{IntOp u64} (LocInfoE loc_170 ("pa")))) &{IntOp u64, IntOp u64} (LocInfoE loc_171 (Call (LocInfoE loc_173 (global_GENMASK)) [@{expr} LocInfoE loc_174 (i2v 47 i32) ;
          LocInfoE loc_175 (i2v 12 i32) ]))) ;
        locinfo: loc_165 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_165 ((LocInfoE loc_166 (i2v 12 i32)) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_167 (i2v 16 i32)))
        then
        locinfo: loc_147 ;
          Goto "#2"
        else
        locinfo: loc_144 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_144 ;
        Return (LocInfoE loc_145 (use{IntOp u64} (LocInfoE loc_146 ("pte"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_147 ;
        LocInfoE loc_148 ("pte") <-{ IntOp u64 }
          LocInfoE loc_149 ((LocInfoE loc_150 (use{IntOp u64} (LocInfoE loc_151 ("pte")))) |{IntOp u64, IntOp u64} (LocInfoE loc_152 (Call (LocInfoE loc_154 (global_FIELD_PREP)) [@{expr} LocInfoE loc_155 (Call (LocInfoE loc_157 (global_GENMASK)) [@{expr} LocInfoE loc_158 (i2v 15 i32) ;
          LocInfoE loc_159 (i2v 12 i32) ]) ;
          LocInfoE loc_160 ((LocInfoE loc_161 (use{IntOp u64} (LocInfoE loc_162 ("pa")))) >>{IntOp u64, IntOp u64} (LocInfoE loc_163 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_163 (i2v 48 i32))))) ]))) ;
        locinfo: loc_144 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_144 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [kvm_set_table_pte]. *)
  Definition impl_kvm_set_table_pte (global_BIT global_FIELD_PREP global_kvm_phys_to_pte global_kvm_pte_valid : loc): function := {|
    f_args := [
      ("ptep", void*);
      ("childp", void*);
      ("mm_ops", void*)
    ];
    f_local_vars := [
      ("old", it_layout u64);
      ("pte", it_layout u64)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "old" <-{ IntOp u64 }
          LocInfoE loc_228 (use{IntOp u64} (LocInfoE loc_230 (!{PtrOp} (LocInfoE loc_231 ("ptep"))))) ;
        "pte" <-{ IntOp u64 }
          LocInfoE loc_215 (Call (LocInfoE loc_217 (global_kvm_phys_to_pte)) [@{expr} LocInfoE loc_218 (Call (LocInfoE loc_220 (use{PtrOp} (LocInfoE loc_221 ((LocInfoE loc_222 (!{PtrOp} (LocInfoE loc_223 ("mm_ops")))) at{struct_kvm_pgtable_mm_ops} "virt_to_phys")))) [@{expr} LocInfoE loc_224 (use{PtrOp} (LocInfoE loc_225 ("childp"))) ]) ]) ;
        locinfo: loc_181 ;
        LocInfoE loc_203 ("pte") <-{ IntOp u64 }
          LocInfoE loc_204 ((LocInfoE loc_205 (use{IntOp u64} (LocInfoE loc_206 ("pte")))) |{IntOp u64, IntOp u64} (LocInfoE loc_207 (Call (LocInfoE loc_209 (global_FIELD_PREP)) [@{expr} LocInfoE loc_210 (Call (LocInfoE loc_212 (global_BIT)) [@{expr} LocInfoE loc_213 (i2v 1 i32) ]) ;
          LocInfoE loc_214 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_214 (i2v 1 i32))) ]))) ;
        locinfo: loc_182 ;
        LocInfoE loc_195 ("pte") <-{ IntOp u64 }
          LocInfoE loc_196 ((LocInfoE loc_197 (use{IntOp u64} (LocInfoE loc_198 ("pte")))) |{IntOp u64, IntOp u64} (LocInfoE loc_199 (Call (LocInfoE loc_201 (global_BIT)) [@{expr} LocInfoE loc_202 (i2v 0 i32) ]))) ;
        locinfo: loc_183 ;
        assert{BoolOp}: (LocInfoE loc_190 (Call (LocInfoE loc_192 (global_kvm_pte_valid)) [@{expr} LocInfoE loc_193 (use{IntOp u64} (LocInfoE loc_194 ("old"))) ])) ;
        locinfo: loc_184 ;
        LocInfoE loc_186 (!{PtrOp} (LocInfoE loc_187 ("ptep"))) <-{ IntOp u64 }
          LocInfoE loc_188 (use{IntOp u64} (LocInfoE loc_189 ("pte"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [kvm_set_valid_leaf_pte]. *)
  Definition impl_kvm_set_valid_leaf_pte (global_BIT global_FIELD_PREP global_GENMASK global_kvm_phys_to_pte global_kvm_pte_valid : loc): function := {|
    f_args := [
      ("ptep", void*);
      ("pa", it_layout u64);
      ("attr", it_layout u64);
      ("level", it_layout u32)
    ];
    f_local_vars := [
      ("old", it_layout u64);
      ("type", it_layout u64);
      ("pte", it_layout u64)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "old" <-{ IntOp u64 }
          LocInfoE loc_319 (use{IntOp u64} (LocInfoE loc_321 (!{PtrOp} (LocInfoE loc_322 ("ptep"))))) ;
        "pte" <-{ IntOp u64 }
          LocInfoE loc_312 (Call (LocInfoE loc_314 (global_kvm_phys_to_pte)) [@{expr} LocInfoE loc_315 (use{IntOp u64} (LocInfoE loc_316 ("pa"))) ]) ;
        "type" <-{ IntOp u64 }
          LocInfoE loc_301 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_301 (IfE
          (IntOp i32)
          (LocInfoE loc_302 ((LocInfoE loc_303 (use{IntOp u32} (LocInfoE loc_304 ("level")))) ={IntOp u32, IntOp u32, i32} (LocInfoE loc_305 ((LocInfoE loc_306 (i2v 4 u32)) -{IntOp u32, IntOp u32} (LocInfoE loc_307 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_307 (i2v 1 i32))))))))
          (LocInfoE loc_308 (i2v 1 i32)) (LocInfoE loc_309 (i2v 0 i32))))) ;
        locinfo: loc_238 ;
        LocInfoE loc_283 ("pte") <-{ IntOp u64 }
          LocInfoE loc_284 ((LocInfoE loc_285 (use{IntOp u64} (LocInfoE loc_286 ("pte")))) |{IntOp u64, IntOp u64} (LocInfoE loc_287 ((LocInfoE loc_288 (use{IntOp u64} (LocInfoE loc_289 ("attr")))) &{IntOp u64, IntOp u64} (LocInfoE loc_290 ((LocInfoE loc_291 (Call (LocInfoE loc_293 (global_GENMASK)) [@{expr} LocInfoE loc_294 (i2v 11 i32) ;
          LocInfoE loc_295 (i2v 2 i32) ])) |{IntOp u64, IntOp u64} (LocInfoE loc_296 (Call (LocInfoE loc_298 (global_GENMASK)) [@{expr} LocInfoE loc_299 (i2v 63 i32) ;
          LocInfoE loc_300 (i2v 51 i32) ]))))))) ;
        locinfo: loc_239 ;
        LocInfoE loc_270 ("pte") <-{ IntOp u64 }
          LocInfoE loc_271 ((LocInfoE loc_272 (use{IntOp u64} (LocInfoE loc_273 ("pte")))) |{IntOp u64, IntOp u64} (LocInfoE loc_274 (Call (LocInfoE loc_276 (global_FIELD_PREP)) [@{expr} LocInfoE loc_277 (Call (LocInfoE loc_279 (global_BIT)) [@{expr} LocInfoE loc_280 (i2v 1 i32) ]) ;
          LocInfoE loc_281 (use{IntOp u64} (LocInfoE loc_282 ("type"))) ]))) ;
        locinfo: loc_240 ;
        LocInfoE loc_262 ("pte") <-{ IntOp u64 }
          LocInfoE loc_263 ((LocInfoE loc_264 (use{IntOp u64} (LocInfoE loc_265 ("pte")))) |{IntOp u64, IntOp u64} (LocInfoE loc_266 (Call (LocInfoE loc_268 (global_BIT)) [@{expr} LocInfoE loc_269 (i2v 0 i32) ]))) ;
        locinfo: loc_257 ;
        if{BoolOp, Some "#1"}: LocInfoE loc_257 (Call (LocInfoE loc_259 (global_kvm_pte_valid)) [@{expr} LocInfoE loc_260 (use{IntOp u64} (LocInfoE loc_261 ("old"))) ])
        then
        locinfo: loc_250 ;
          Goto "#2"
        else
        locinfo: loc_242 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_242 ;
        LocInfoE loc_246 (!{PtrOp} (LocInfoE loc_247 ("ptep"))) <-{ IntOp u64 }
          LocInfoE loc_248 (use{IntOp u64} (LocInfoE loc_249 ("pte"))) ;
        locinfo: loc_243 ;
        Return (LocInfoE loc_244 (UnOp (CastOp $ BoolOp) (IntOp i32) (LocInfoE loc_244 (i2v 1 i32))))
      ]> $
      <[ "#2" :=
        locinfo: loc_250 ;
        Return (LocInfoE loc_251 (UnOp (CastOp $ BoolOp) (IntOp i32) (LocInfoE loc_251 ((LocInfoE loc_252 (use{IntOp u64} (LocInfoE loc_253 ("old")))) ={IntOp u64, IntOp u64, i32} (LocInfoE loc_254 (use{IntOp u64} (LocInfoE loc_255 ("pte"))))))))
      ]> $
      <[ "#3" :=
        locinfo: loc_242 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_map_set_prot_attr]. *)
  Definition impl_hyp_map_set_prot_attr (global_BIT global_FIELD_PREP global_GENMASK : loc): function := {|
    f_args := [
      ("prot", it_layout u64);
      ("data", void*)
    ];
    f_local_vars := [
      ("mtype", it_layout u32);
      ("sh", it_layout u32);
      ("ap", it_layout u32);
      ("attr", it_layout u64);
      ("device", bool_layout)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "device" <-{ BoolOp }
          LocInfoE loc_465 (UnOp (CastOp $ BoolOp) (IntOp i32) (LocInfoE loc_465 ((LocInfoE loc_466 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_466 (i2v 0 i32)))) !={IntOp u64, IntOp u64, i32} (LocInfoE loc_467 ((LocInfoE loc_468 (use{IntOp u64} (LocInfoE loc_469 ("prot")))) &{IntOp u64, IntOp u64} (LocInfoE loc_470 (Call (LocInfoE loc_472 (global_BIT)) [@{expr} LocInfoE loc_473 (i2v 3 i32) ]))))))) ;
        "mtype" <-{ IntOp u32 }
          LocInfoE loc_458 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_458 (IfE
          (BoolOp)
          (LocInfoE loc_459 (use{BoolOp} (LocInfoE loc_460 ("device"))))
          (LocInfoE loc_461 (i2v 5 i32)) (LocInfoE loc_462 (i2v 0 i32))))) ;
        "attr" <-{ IntOp u64 }
          LocInfoE loc_446 (Call (LocInfoE loc_448 (global_FIELD_PREP)) [@{expr} LocInfoE loc_449 (Call (LocInfoE loc_451 (global_GENMASK)) [@{expr} LocInfoE loc_452 (i2v 4 i32) ;
          LocInfoE loc_453 (i2v 2 i32) ]) ;
          LocInfoE loc_454 (UnOp (CastOp $ IntOp u64) (IntOp u32) (LocInfoE loc_454 (use{IntOp u32} (LocInfoE loc_455 ("mtype"))))) ]) ;
        "sh" <-{ IntOp u32 }
          LocInfoE loc_443 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_443 (i2v 3 i32))) ;
        "ap" <-{ IntOp u32 }
          LocInfoE loc_431 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_431 (IfE
          (IntOp u64)
          (LocInfoE loc_432 ((LocInfoE loc_433 (use{IntOp u64} (LocInfoE loc_434 ("prot")))) &{IntOp u64, IntOp u64} (LocInfoE loc_435 (Call (LocInfoE loc_437 (global_BIT)) [@{expr} LocInfoE loc_438 (i2v 1 i32) ]))))
          (LocInfoE loc_439 (i2v 1 i32)) (LocInfoE loc_440 (i2v 3 i32))))) ;
        locinfo: loc_422 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_422 ((UnOp (CastOp $ IntOp u64) (IntOp i32) (i2v 0 i32)) ={IntOp u64, IntOp u64, i32} (LocInfoE loc_424 ((LocInfoE loc_425 (use{IntOp u64} (LocInfoE loc_426 ("prot")))) &{IntOp u64, IntOp u64} (LocInfoE loc_427 (Call (LocInfoE loc_429 (global_BIT)) [@{expr} LocInfoE loc_430 (i2v 2 i32) ])))))
        then
        locinfo: loc_418 ;
          Goto "#10"
        else
        locinfo: loc_411 ;
          Goto "#11"
      ]> $
      <[ "#1" :=
        locinfo: loc_411 ;
        if{IntOp u64, Some "#2"}: LocInfoE loc_411 ((LocInfoE loc_412 (use{IntOp u64} (LocInfoE loc_413 ("prot")))) &{IntOp u64, IntOp u64} (LocInfoE loc_414 (Call (LocInfoE loc_416 (global_BIT)) [@{expr} LocInfoE loc_417 (i2v 0 i32) ])))
        then
        locinfo: loc_394 ;
          Goto "#3"
        else
        locinfo: loc_402 ;
          Goto "#9"
      ]> $
      <[ "#10" :=
        locinfo: loc_418 ;
        Return (LocInfoE loc_419 (UnOp NegOp (IntOp i32) (LocInfoE loc_420 (i2v 22 i32))))
      ]> $
      <[ "#11" :=
        locinfo: loc_411 ;
        Goto "#1"
      ]> $
      <[ "#2" :=
        locinfo: loc_334 ;
        LocInfoE loc_367 ("attr") <-{ IntOp u64 }
          LocInfoE loc_368 ((LocInfoE loc_369 (use{IntOp u64} (LocInfoE loc_370 ("attr")))) |{IntOp u64, IntOp u64} (LocInfoE loc_371 (Call (LocInfoE loc_373 (global_FIELD_PREP)) [@{expr} LocInfoE loc_374 (Call (LocInfoE loc_376 (global_GENMASK)) [@{expr} LocInfoE loc_377 (i2v 7 i32) ;
          LocInfoE loc_378 (i2v 6 i32) ]) ;
          LocInfoE loc_379 (UnOp (CastOp $ IntOp u64) (IntOp u32) (LocInfoE loc_379 (use{IntOp u32} (LocInfoE loc_380 ("ap"))))) ]))) ;
        locinfo: loc_335 ;
        LocInfoE loc_353 ("attr") <-{ IntOp u64 }
          LocInfoE loc_354 ((LocInfoE loc_355 (use{IntOp u64} (LocInfoE loc_356 ("attr")))) |{IntOp u64, IntOp u64} (LocInfoE loc_357 (Call (LocInfoE loc_359 (global_FIELD_PREP)) [@{expr} LocInfoE loc_360 (Call (LocInfoE loc_362 (global_GENMASK)) [@{expr} LocInfoE loc_363 (i2v 9 i32) ;
          LocInfoE loc_364 (i2v 8 i32) ]) ;
          LocInfoE loc_365 (UnOp (CastOp $ IntOp u64) (IntOp u32) (LocInfoE loc_365 (use{IntOp u32} (LocInfoE loc_366 ("sh"))))) ]))) ;
        locinfo: loc_336 ;
        LocInfoE loc_345 ("attr") <-{ IntOp u64 }
          LocInfoE loc_346 ((LocInfoE loc_347 (use{IntOp u64} (LocInfoE loc_348 ("attr")))) |{IntOp u64, IntOp u64} (LocInfoE loc_349 (Call (LocInfoE loc_351 (global_BIT)) [@{expr} LocInfoE loc_352 (i2v 10 i32) ]))) ;
        locinfo: loc_337 ;
        LocInfoE loc_340 ((LocInfoE loc_341 (!{PtrOp} (LocInfoE loc_342 ("data")))) at{struct_hyp_map_data} "attr") <-{ IntOp u64 }
          LocInfoE loc_343 (use{IntOp u64} (LocInfoE loc_344 ("attr"))) ;
        locinfo: loc_338 ;
        Return (LocInfoE loc_339 (i2v 0 i32))
      ]> $
      <[ "#3" :=
        locinfo: loc_394 ;
        if{IntOp u64, Some "#4"}: LocInfoE loc_394 ((LocInfoE loc_395 (use{IntOp u64} (LocInfoE loc_396 ("prot")))) &{IntOp u64, IntOp u64} (LocInfoE loc_397 (Call (LocInfoE loc_399 (global_BIT)) [@{expr} LocInfoE loc_400 (i2v 1 i32) ])))
        then
        locinfo: loc_390 ;
          Goto "#7"
        else
        locinfo: loc_388 ;
          Goto "#8"
      ]> $
      <[ "#4" :=
        locinfo: loc_388 ;
        if{BoolOp, None}: LocInfoE loc_388 (use{BoolOp} (LocInfoE loc_389 ("device")))
        then
        locinfo: loc_384 ;
          Goto "#5"
        else
        locinfo: loc_334 ;
          Goto "#6"
      ]> $
      <[ "#5" :=
        locinfo: loc_384 ;
        Return (LocInfoE loc_385 (UnOp NegOp (IntOp i32) (LocInfoE loc_386 (i2v 22 i32))))
      ]> $
      <[ "#6" :=
        locinfo: loc_334 ;
        Goto "#2"
      ]> $
      <[ "#7" :=
        locinfo: loc_390 ;
        Return (LocInfoE loc_391 (UnOp NegOp (IntOp i32) (LocInfoE loc_392 (i2v 22 i32))))
      ]> $
      <[ "#8" :=
        locinfo: loc_388 ;
        Goto "#4"
      ]> $
      <[ "#9" :=
        locinfo: loc_402 ;
        LocInfoE loc_403 ("attr") <-{ IntOp u64 }
          LocInfoE loc_404 ((LocInfoE loc_405 (use{IntOp u64} (LocInfoE loc_406 ("attr")))) |{IntOp u64, IntOp u64} (LocInfoE loc_407 (Call (LocInfoE loc_409 (global_BIT)) [@{expr} LocInfoE loc_410 (i2v 54 i32) ]))) ;
        locinfo: loc_334 ;
        Goto "#2"
      ]> $∅
    )%E
  |}.
End code.
