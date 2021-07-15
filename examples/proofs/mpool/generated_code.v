From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/mpool.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "examples/mpool.c".
  Definition loc_2 : location_info := LocationInfo file_0 50 2 50 47.
  Definition loc_3 : location_info := LocationInfo file_0 50 9 50 46.
  Definition loc_4 : location_info := LocationInfo file_0 50 9 50 32.
  Definition loc_5 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_6 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_7 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_8 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_11 : location_info := LocationInfo file_1 224 2 224 19.
  Definition loc_12 : location_info := LocationInfo file_1 224 19 224 3.
  Definition loc_13 : location_info := LocationInfo file_1 227 2 229 3.
  Definition loc_14 : location_info := LocationInfo file_1 231 2 231 16.
  Definition loc_15 : location_info := LocationInfo file_1 232 2 232 21.
  Definition loc_16 : location_info := LocationInfo file_1 234 2 234 20.
  Definition loc_17 : location_info := LocationInfo file_1 235 2 235 40.
  Definition loc_18 : location_info := LocationInfo file_1 235 40 235 3.
  Definition loc_19 : location_info := LocationInfo file_1 236 2 236 43.
  Definition loc_20 : location_info := LocationInfo file_1 237 2 237 31.
  Definition loc_21 : location_info := LocationInfo file_1 238 2 238 22.
  Definition loc_22 : location_info := LocationInfo file_1 240 2 240 11.
  Definition loc_23 : location_info := LocationInfo file_1 240 9 240 10.
  Definition loc_24 : location_info := LocationInfo file_1 238 2 238 11.
  Definition loc_25 : location_info := LocationInfo file_1 238 2 238 11.
  Definition loc_26 : location_info := LocationInfo file_1 238 12 238 20.
  Definition loc_27 : location_info := LocationInfo file_1 238 13 238 20.
  Definition loc_28 : location_info := LocationInfo file_1 238 13 238 14.
  Definition loc_29 : location_info := LocationInfo file_1 238 13 238 14.
  Definition loc_30 : location_info := LocationInfo file_1 237 2 237 22.
  Definition loc_31 : location_info := LocationInfo file_1 237 2 237 11.
  Definition loc_32 : location_info := LocationInfo file_1 237 2 237 3.
  Definition loc_33 : location_info := LocationInfo file_1 237 2 237 3.
  Definition loc_34 : location_info := LocationInfo file_1 237 25 237 30.
  Definition loc_35 : location_info := LocationInfo file_1 237 25 237 30.
  Definition loc_36 : location_info := LocationInfo file_1 236 2 236 19.
  Definition loc_37 : location_info := LocationInfo file_1 236 2 236 7.
  Definition loc_38 : location_info := LocationInfo file_1 236 2 236 7.
  Definition loc_39 : location_info := LocationInfo file_1 236 22 236 42.
  Definition loc_40 : location_info := LocationInfo file_1 236 22 236 42.
  Definition loc_41 : location_info := LocationInfo file_1 236 22 236 31.
  Definition loc_42 : location_info := LocationInfo file_1 236 22 236 23.
  Definition loc_43 : location_info := LocationInfo file_1 236 22 236 23.
  Definition loc_44 : location_info := LocationInfo file_1 235 27 235 39.
  Definition loc_45 : location_info := LocationInfo file_1 235 28 235 39.
  Definition loc_46 : location_info := LocationInfo file_1 235 29 235 30.
  Definition loc_47 : location_info := LocationInfo file_1 235 29 235 30.
  Definition loc_48 : location_info := LocationInfo file_1 234 2 234 9.
  Definition loc_49 : location_info := LocationInfo file_1 234 2 234 9.
  Definition loc_50 : location_info := LocationInfo file_1 234 10 234 18.
  Definition loc_51 : location_info := LocationInfo file_1 234 11 234 18.
  Definition loc_52 : location_info := LocationInfo file_1 234 11 234 12.
  Definition loc_53 : location_info := LocationInfo file_1 234 11 234 12.
  Definition loc_54 : location_info := LocationInfo file_1 232 2 232 13.
  Definition loc_55 : location_info := LocationInfo file_1 232 2 232 7.
  Definition loc_56 : location_info := LocationInfo file_1 232 2 232 7.
  Definition loc_57 : location_info := LocationInfo file_1 232 16 232 20.
  Definition loc_58 : location_info := LocationInfo file_1 232 16 232 20.
  Definition loc_59 : location_info := LocationInfo file_1 231 2 231 7.
  Definition loc_60 : location_info := LocationInfo file_1 231 10 231 15.
  Definition loc_61 : location_info := LocationInfo file_1 231 10 231 15.
  Definition loc_62 : location_info := LocationInfo file_1 227 26 229 3.
  Definition loc_63 : location_info := LocationInfo file_1 228 4 228 13.
  Definition loc_64 : location_info := LocationInfo file_1 228 11 228 12.
  Definition loc_66 : location_info := LocationInfo file_1 227 6 227 24.
  Definition loc_67 : location_info := LocationInfo file_1 227 6 227 10.
  Definition loc_68 : location_info := LocationInfo file_1 227 6 227 10.
  Definition loc_69 : location_info := LocationInfo file_1 227 14 227 24.
  Definition loc_70 : location_info := LocationInfo file_1 227 23 227 24.
  Definition loc_71 : location_info := LocationInfo file_1 224 2 224 18.
  Definition loc_72 : location_info := LocationInfo file_1 224 3 224 18.
  Definition loc_73 : location_info := LocationInfo file_1 224 4 224 5.
  Definition loc_74 : location_info := LocationInfo file_1 224 4 224 5.
  Definition loc_77 : location_info := LocationInfo file_1 336 2 336 30.
  Definition loc_78 : location_info := LocationInfo file_1 339 2 339 20.
  Definition loc_79 : location_info := LocationInfo file_1 340 2 340 40.
  Definition loc_80 : location_info := LocationInfo file_1 340 40 340 3.
  Definition loc_81 : location_info := LocationInfo file_1 341 2 341 33.
  Definition loc_82 : location_info := LocationInfo file_1 342 2 342 27.
  Definition loc_83 : location_info := LocationInfo file_1 343 2 343 22.
  Definition loc_84 : location_info := LocationInfo file_1 343 2 343 11.
  Definition loc_85 : location_info := LocationInfo file_1 343 2 343 11.
  Definition loc_86 : location_info := LocationInfo file_1 343 12 343 20.
  Definition loc_87 : location_info := LocationInfo file_1 343 13 343 20.
  Definition loc_88 : location_info := LocationInfo file_1 343 13 343 14.
  Definition loc_89 : location_info := LocationInfo file_1 343 13 343 14.
  Definition loc_90 : location_info := LocationInfo file_1 342 2 342 22.
  Definition loc_91 : location_info := LocationInfo file_1 342 2 342 11.
  Definition loc_92 : location_info := LocationInfo file_1 342 2 342 3.
  Definition loc_93 : location_info := LocationInfo file_1 342 2 342 3.
  Definition loc_94 : location_info := LocationInfo file_1 342 25 342 26.
  Definition loc_95 : location_info := LocationInfo file_1 342 25 342 26.
  Definition loc_96 : location_info := LocationInfo file_1 341 2 341 9.
  Definition loc_97 : location_info := LocationInfo file_1 341 2 341 3.
  Definition loc_98 : location_info := LocationInfo file_1 341 2 341 3.
  Definition loc_99 : location_info := LocationInfo file_1 341 12 341 32.
  Definition loc_100 : location_info := LocationInfo file_1 341 12 341 32.
  Definition loc_101 : location_info := LocationInfo file_1 341 12 341 21.
  Definition loc_102 : location_info := LocationInfo file_1 341 12 341 13.
  Definition loc_103 : location_info := LocationInfo file_1 341 12 341 13.
  Definition loc_104 : location_info := LocationInfo file_1 340 27 340 39.
  Definition loc_105 : location_info := LocationInfo file_1 340 28 340 39.
  Definition loc_106 : location_info := LocationInfo file_1 340 29 340 30.
  Definition loc_107 : location_info := LocationInfo file_1 340 29 340 30.
  Definition loc_108 : location_info := LocationInfo file_1 339 2 339 9.
  Definition loc_109 : location_info := LocationInfo file_1 339 2 339 9.
  Definition loc_110 : location_info := LocationInfo file_1 339 10 339 18.
  Definition loc_111 : location_info := LocationInfo file_1 339 11 339 18.
  Definition loc_112 : location_info := LocationInfo file_1 339 11 339 12.
  Definition loc_113 : location_info := LocationInfo file_1 339 11 339 12.
  Definition loc_114 : location_info := LocationInfo file_1 336 26 336 29.
  Definition loc_115 : location_info := LocationInfo file_1 336 26 336 29.
  Definition loc_120 : location_info := LocationInfo file_1 111 2 111 29.
  Definition loc_121 : location_info := LocationInfo file_1 112 2 112 40.
  Definition loc_122 : location_info := LocationInfo file_1 113 2 113 40.
  Definition loc_123 : location_info := LocationInfo file_1 114 2 114 31.
  Definition loc_124 : location_info := LocationInfo file_1 115 2 115 20.
  Definition loc_125 : location_info := LocationInfo file_1 115 2 115 9.
  Definition loc_126 : location_info := LocationInfo file_1 115 2 115 9.
  Definition loc_127 : location_info := LocationInfo file_1 115 10 115 18.
  Definition loc_128 : location_info := LocationInfo file_1 115 11 115 18.
  Definition loc_129 : location_info := LocationInfo file_1 115 11 115 12.
  Definition loc_130 : location_info := LocationInfo file_1 115 11 115 12.
  Definition loc_131 : location_info := LocationInfo file_1 114 2 114 13.
  Definition loc_132 : location_info := LocationInfo file_1 114 2 114 3.
  Definition loc_133 : location_info := LocationInfo file_1 114 2 114 3.
  Definition loc_134 : location_info := LocationInfo file_1 114 16 114 30.
  Definition loc_135 : location_info := LocationInfo file_1 113 2 113 22.
  Definition loc_136 : location_info := LocationInfo file_1 113 2 113 11.
  Definition loc_137 : location_info := LocationInfo file_1 113 2 113 3.
  Definition loc_138 : location_info := LocationInfo file_1 113 2 113 3.
  Definition loc_139 : location_info := LocationInfo file_1 113 25 113 39.
  Definition loc_140 : location_info := LocationInfo file_1 112 2 112 22.
  Definition loc_141 : location_info := LocationInfo file_1 112 2 112 11.
  Definition loc_142 : location_info := LocationInfo file_1 112 2 112 3.
  Definition loc_143 : location_info := LocationInfo file_1 112 2 112 3.
  Definition loc_144 : location_info := LocationInfo file_1 112 25 112 39.
  Definition loc_145 : location_info := LocationInfo file_1 111 2 111 15.
  Definition loc_146 : location_info := LocationInfo file_1 111 2 111 3.
  Definition loc_147 : location_info := LocationInfo file_1 111 2 111 3.
  Definition loc_148 : location_info := LocationInfo file_1 111 18 111 28.
  Definition loc_149 : location_info := LocationInfo file_1 111 18 111 28.
  Definition loc_152 : location_info := LocationInfo file_1 130 2 130 34.
  Definition loc_153 : location_info := LocationInfo file_1 132 2 132 23.
  Definition loc_154 : location_info := LocationInfo file_1 133 2 133 43.
  Definition loc_155 : location_info := LocationInfo file_1 133 43 133 3.
  Definition loc_156 : location_info := LocationInfo file_1 135 2 135 49.
  Definition loc_157 : location_info := LocationInfo file_1 136 2 136 49.
  Definition loc_158 : location_info := LocationInfo file_1 137 2 137 31.
  Definition loc_159 : location_info := LocationInfo file_1 139 2 139 43.
  Definition loc_160 : location_info := LocationInfo file_1 140 2 140 43.
  Definition loc_161 : location_info := LocationInfo file_1 143 2 143 25.
  Definition loc_162 : location_info := LocationInfo file_1 143 2 143 11.
  Definition loc_163 : location_info := LocationInfo file_1 143 2 143 11.
  Definition loc_164 : location_info := LocationInfo file_1 143 12 143 23.
  Definition loc_165 : location_info := LocationInfo file_1 143 13 143 23.
  Definition loc_166 : location_info := LocationInfo file_1 143 13 143 17.
  Definition loc_167 : location_info := LocationInfo file_1 143 13 143 17.
  Definition loc_168 : location_info := LocationInfo file_1 140 2 140 25.
  Definition loc_169 : location_info := LocationInfo file_1 140 2 140 14.
  Definition loc_170 : location_info := LocationInfo file_1 140 2 140 6.
  Definition loc_171 : location_info := LocationInfo file_1 140 2 140 6.
  Definition loc_172 : location_info := LocationInfo file_1 140 28 140 42.
  Definition loc_173 : location_info := LocationInfo file_1 139 2 139 25.
  Definition loc_174 : location_info := LocationInfo file_1 139 2 139 14.
  Definition loc_175 : location_info := LocationInfo file_1 139 2 139 6.
  Definition loc_176 : location_info := LocationInfo file_1 139 2 139 6.
  Definition loc_177 : location_info := LocationInfo file_1 139 28 139 42.
  Definition loc_178 : location_info := LocationInfo file_1 137 2 137 13.
  Definition loc_179 : location_info := LocationInfo file_1 137 2 137 3.
  Definition loc_180 : location_info := LocationInfo file_1 137 2 137 3.
  Definition loc_181 : location_info := LocationInfo file_1 137 16 137 30.
  Definition loc_182 : location_info := LocationInfo file_1 137 16 137 30.
  Definition loc_183 : location_info := LocationInfo file_1 137 16 137 20.
  Definition loc_184 : location_info := LocationInfo file_1 137 16 137 20.
  Definition loc_185 : location_info := LocationInfo file_1 136 2 136 22.
  Definition loc_186 : location_info := LocationInfo file_1 136 2 136 11.
  Definition loc_187 : location_info := LocationInfo file_1 136 2 136 3.
  Definition loc_188 : location_info := LocationInfo file_1 136 2 136 3.
  Definition loc_189 : location_info := LocationInfo file_1 136 25 136 48.
  Definition loc_190 : location_info := LocationInfo file_1 136 25 136 48.
  Definition loc_191 : location_info := LocationInfo file_1 136 25 136 37.
  Definition loc_192 : location_info := LocationInfo file_1 136 25 136 29.
  Definition loc_193 : location_info := LocationInfo file_1 136 25 136 29.
  Definition loc_194 : location_info := LocationInfo file_1 135 2 135 22.
  Definition loc_195 : location_info := LocationInfo file_1 135 2 135 11.
  Definition loc_196 : location_info := LocationInfo file_1 135 2 135 3.
  Definition loc_197 : location_info := LocationInfo file_1 135 2 135 3.
  Definition loc_198 : location_info := LocationInfo file_1 135 25 135 48.
  Definition loc_199 : location_info := LocationInfo file_1 135 25 135 48.
  Definition loc_200 : location_info := LocationInfo file_1 135 25 135 37.
  Definition loc_201 : location_info := LocationInfo file_1 135 25 135 29.
  Definition loc_202 : location_info := LocationInfo file_1 135 25 135 29.
  Definition loc_203 : location_info := LocationInfo file_1 133 27 133 42.
  Definition loc_204 : location_info := LocationInfo file_1 133 28 133 42.
  Definition loc_205 : location_info := LocationInfo file_1 133 29 133 33.
  Definition loc_206 : location_info := LocationInfo file_1 133 29 133 33.
  Definition loc_207 : location_info := LocationInfo file_1 132 2 132 9.
  Definition loc_208 : location_info := LocationInfo file_1 132 2 132 9.
  Definition loc_209 : location_info := LocationInfo file_1 132 10 132 21.
  Definition loc_210 : location_info := LocationInfo file_1 132 11 132 21.
  Definition loc_211 : location_info := LocationInfo file_1 132 11 132 15.
  Definition loc_212 : location_info := LocationInfo file_1 132 11 132 15.
  Definition loc_213 : location_info := LocationInfo file_1 130 2 130 12.
  Definition loc_214 : location_info := LocationInfo file_1 130 2 130 12.
  Definition loc_215 : location_info := LocationInfo file_1 130 13 130 14.
  Definition loc_216 : location_info := LocationInfo file_1 130 13 130 14.
  Definition loc_217 : location_info := LocationInfo file_1 130 16 130 32.
  Definition loc_218 : location_info := LocationInfo file_1 130 16 130 32.
  Definition loc_219 : location_info := LocationInfo file_1 130 16 130 20.
  Definition loc_220 : location_info := LocationInfo file_1 130 16 130 20.
  Definition loc_223 : location_info := LocationInfo file_1 155 2 155 38.
  Definition loc_224 : location_info := LocationInfo file_1 156 2 156 25.
  Definition loc_225 : location_info := LocationInfo file_1 156 2 156 13.
  Definition loc_226 : location_info := LocationInfo file_1 156 2 156 3.
  Definition loc_227 : location_info := LocationInfo file_1 156 2 156 3.
  Definition loc_228 : location_info := LocationInfo file_1 156 16 156 24.
  Definition loc_229 : location_info := LocationInfo file_1 156 16 156 24.
  Definition loc_230 : location_info := LocationInfo file_1 155 2 155 12.
  Definition loc_231 : location_info := LocationInfo file_1 155 2 155 12.
  Definition loc_232 : location_info := LocationInfo file_1 155 13 155 14.
  Definition loc_233 : location_info := LocationInfo file_1 155 13 155 14.
  Definition loc_234 : location_info := LocationInfo file_1 155 16 155 36.
  Definition loc_235 : location_info := LocationInfo file_1 155 16 155 36.
  Definition loc_236 : location_info := LocationInfo file_1 155 16 155 24.
  Definition loc_237 : location_info := LocationInfo file_1 155 16 155 24.
  Definition loc_240 : location_info := LocationInfo file_1 170 2 172 3.
  Definition loc_241 : location_info := LocationInfo file_1 174 2 174 31.
  Definition loc_242 : location_info := LocationInfo file_1 175 2 175 31.
  Definition loc_243 : location_info := LocationInfo file_1 180 2 184 3.
  Definition loc_244 : location_info := LocationInfo file_1 190 2 196 3.
  Definition loc_245 : location_info := LocationInfo file_1 198 2 198 40.
  Definition loc_246 : location_info := LocationInfo file_1 199 2 199 40.
  Definition loc_247 : location_info := LocationInfo file_1 200 2 200 31.
  Definition loc_248 : location_info := LocationInfo file_1 200 2 200 13.
  Definition loc_249 : location_info := LocationInfo file_1 200 2 200 3.
  Definition loc_250 : location_info := LocationInfo file_1 200 2 200 3.
  Definition loc_251 : location_info := LocationInfo file_1 200 16 200 30.
  Definition loc_252 : location_info := LocationInfo file_1 199 2 199 22.
  Definition loc_253 : location_info := LocationInfo file_1 199 2 199 11.
  Definition loc_254 : location_info := LocationInfo file_1 199 2 199 3.
  Definition loc_255 : location_info := LocationInfo file_1 199 2 199 3.
  Definition loc_256 : location_info := LocationInfo file_1 199 25 199 39.
  Definition loc_257 : location_info := LocationInfo file_1 198 2 198 22.
  Definition loc_258 : location_info := LocationInfo file_1 198 2 198 11.
  Definition loc_259 : location_info := LocationInfo file_1 198 2 198 3.
  Definition loc_260 : location_info := LocationInfo file_1 198 2 198 3.
  Definition loc_261 : location_info := LocationInfo file_1 198 25 198 39.
  Definition loc_262 : location_info := LocationInfo file_1 190 2 196 3.
  Definition loc_263 : location_info := LocationInfo file_1 190 34 196 3.
  Definition loc_264 : location_info := LocationInfo file_1 191 4 191 23.
  Definition loc_265 : location_info := LocationInfo file_1 192 4 192 30.
  Definition loc_266 : location_info := LocationInfo file_1 194 4 194 30.
  Definition loc_267 : location_info := LocationInfo file_1 195 4 195 45.
  Definition loc_268 : location_info := LocationInfo file_1 190 2 196 3.
  Definition loc_269 : location_info := LocationInfo file_1 190 2 196 3.
  Definition loc_270 : location_info := LocationInfo file_1 195 4 195 19.
  Definition loc_271 : location_info := LocationInfo file_1 195 4 195 19.
  Definition loc_272 : location_info := LocationInfo file_1 195 20 195 31.
  Definition loc_273 : location_info := LocationInfo file_1 195 20 195 31.
  Definition loc_274 : location_info := LocationInfo file_1 195 20 195 21.
  Definition loc_275 : location_info := LocationInfo file_1 195 20 195 21.
  Definition loc_276 : location_info := LocationInfo file_1 195 33 195 37.
  Definition loc_277 : location_info := LocationInfo file_1 195 33 195 37.
  Definition loc_278 : location_info := LocationInfo file_1 195 39 195 43.
  Definition loc_279 : location_info := LocationInfo file_1 195 39 195 43.
  Definition loc_280 : location_info := LocationInfo file_1 194 4 194 9.
  Definition loc_281 : location_info := LocationInfo file_1 194 12 194 29.
  Definition loc_282 : location_info := LocationInfo file_1 194 12 194 29.
  Definition loc_283 : location_info := LocationInfo file_1 194 12 194 17.
  Definition loc_284 : location_info := LocationInfo file_1 194 12 194 17.
  Definition loc_285 : location_info := LocationInfo file_1 192 18 192 29.
  Definition loc_286 : location_info := LocationInfo file_1 192 18 192 29.
  Definition loc_287 : location_info := LocationInfo file_1 192 18 192 23.
  Definition loc_288 : location_info := LocationInfo file_1 192 18 192 23.
  Definition loc_291 : location_info := LocationInfo file_1 191 17 191 22.
  Definition loc_292 : location_info := LocationInfo file_1 191 17 191 22.
  Definition loc_295 : location_info := LocationInfo file_1 190 9 190 32.
  Definition loc_296 : location_info := LocationInfo file_1 190 9 190 14.
  Definition loc_297 : location_info := LocationInfo file_1 190 9 190 14.
  Definition loc_298 : location_info := LocationInfo file_1 190 18 190 32.
  Definition loc_299 : location_info := LocationInfo file_1 180 2 184 3.
  Definition loc_300 : location_info := LocationInfo file_1 180 34 184 3.
  Definition loc_301 : location_info := LocationInfo file_1 181 4 181 23.
  Definition loc_302 : location_info := LocationInfo file_1 182 4 182 24.
  Definition loc_303 : location_info := LocationInfo file_1 183 4 183 34.
  Definition loc_304 : location_info := LocationInfo file_1 180 2 184 3.
  Definition loc_305 : location_info := LocationInfo file_1 180 2 184 3.
  Definition loc_306 : location_info := LocationInfo file_1 183 4 183 14.
  Definition loc_307 : location_info := LocationInfo file_1 183 4 183 14.
  Definition loc_308 : location_info := LocationInfo file_1 183 15 183 26.
  Definition loc_309 : location_info := LocationInfo file_1 183 15 183 26.
  Definition loc_310 : location_info := LocationInfo file_1 183 15 183 16.
  Definition loc_311 : location_info := LocationInfo file_1 183 15 183 16.
  Definition loc_312 : location_info := LocationInfo file_1 183 28 183 32.
  Definition loc_313 : location_info := LocationInfo file_1 183 28 183 32.
  Definition loc_314 : location_info := LocationInfo file_1 182 4 182 9.
  Definition loc_315 : location_info := LocationInfo file_1 182 12 182 23.
  Definition loc_316 : location_info := LocationInfo file_1 182 12 182 23.
  Definition loc_317 : location_info := LocationInfo file_1 182 12 182 17.
  Definition loc_318 : location_info := LocationInfo file_1 182 12 182 17.
  Definition loc_319 : location_info := LocationInfo file_1 181 17 181 22.
  Definition loc_320 : location_info := LocationInfo file_1 181 17 181 22.
  Definition loc_323 : location_info := LocationInfo file_1 180 9 180 32.
  Definition loc_324 : location_info := LocationInfo file_1 180 9 180 14.
  Definition loc_325 : location_info := LocationInfo file_1 180 9 180 14.
  Definition loc_326 : location_info := LocationInfo file_1 180 18 180 32.
  Definition loc_327 : location_info := LocationInfo file_1 175 2 175 7.
  Definition loc_328 : location_info := LocationInfo file_1 175 10 175 30.
  Definition loc_329 : location_info := LocationInfo file_1 175 10 175 30.
  Definition loc_330 : location_info := LocationInfo file_1 175 10 175 19.
  Definition loc_331 : location_info := LocationInfo file_1 175 10 175 11.
  Definition loc_332 : location_info := LocationInfo file_1 175 10 175 11.
  Definition loc_333 : location_info := LocationInfo file_1 174 2 174 7.
  Definition loc_334 : location_info := LocationInfo file_1 174 10 174 30.
  Definition loc_335 : location_info := LocationInfo file_1 174 10 174 30.
  Definition loc_336 : location_info := LocationInfo file_1 174 10 174 19.
  Definition loc_337 : location_info := LocationInfo file_1 174 10 174 11.
  Definition loc_338 : location_info := LocationInfo file_1 174 10 174 11.
  Definition loc_339 : location_info := LocationInfo file_1 170 37 172 3.
  Definition loc_340 : location_info := LocationInfo file_1 171 4 171 11.
  Definition loc_343 : location_info := LocationInfo file_1 170 6 170 35.
  Definition loc_344 : location_info := LocationInfo file_1 170 6 170 17.
  Definition loc_345 : location_info := LocationInfo file_1 170 6 170 17.
  Definition loc_346 : location_info := LocationInfo file_1 170 6 170 7.
  Definition loc_347 : location_info := LocationInfo file_1 170 6 170 7.
  Definition loc_348 : location_info := LocationInfo file_1 170 21 170 35.
  Definition loc_351 : location_info := LocationInfo file_1 262 2 262 20.
  Definition loc_352 : location_info := LocationInfo file_1 263 2 263 40.
  Definition loc_353 : location_info := LocationInfo file_1 263 40 263 3.
  Definition loc_354 : location_info := LocationInfo file_1 264 2 270 3.
  Definition loc_355 : location_info := LocationInfo file_1 273 2 273 31.
  Definition loc_356 : location_info := LocationInfo file_1 274 2 278 3.
  Definition loc_357 : location_info := LocationInfo file_1 280 2 287 3.
  Definition loc_358 : location_info := LocationInfo file_1 289 2 289 14.
  Definition loc_359 : location_info := LocationInfo file_1 289 14 292 22.
  Definition loc_360 : location_info := LocationInfo file_1 292 2 292 22.
  Definition loc_361 : location_info := LocationInfo file_1 294 2 294 13.
  Definition loc_362 : location_info := LocationInfo file_1 294 9 294 12.
  Definition loc_363 : location_info := LocationInfo file_1 294 9 294 12.
  Definition loc_364 : location_info := LocationInfo file_1 292 2 292 11.
  Definition loc_365 : location_info := LocationInfo file_1 292 2 292 11.
  Definition loc_366 : location_info := LocationInfo file_1 292 12 292 20.
  Definition loc_367 : location_info := LocationInfo file_1 292 13 292 20.
  Definition loc_368 : location_info := LocationInfo file_1 292 13 292 14.
  Definition loc_369 : location_info := LocationInfo file_1 292 13 292 14.
  Definition loc_370 : location_info := LocationInfo file_1 289 2 289 5.
  Definition loc_371 : location_info := LocationInfo file_1 289 8 289 13.
  Definition loc_372 : location_info := LocationInfo file_1 289 8 289 13.
  Definition loc_373 : location_info := LocationInfo file_1 280 36 282 3.
  Definition loc_374 : location_info := LocationInfo file_1 281 4 281 45.
  Definition loc_375 : location_info := LocationInfo file_1 281 4 281 24.
  Definition loc_376 : location_info := LocationInfo file_1 281 4 281 13.
  Definition loc_377 : location_info := LocationInfo file_1 281 4 281 5.
  Definition loc_378 : location_info := LocationInfo file_1 281 4 281 5.
  Definition loc_379 : location_info := LocationInfo file_1 281 27 281 44.
  Definition loc_380 : location_info := LocationInfo file_1 281 27 281 44.
  Definition loc_381 : location_info := LocationInfo file_1 281 27 281 32.
  Definition loc_382 : location_info := LocationInfo file_1 281 27 281 32.
  Definition loc_383 : location_info := LocationInfo file_1 282 9 287 3.
  Definition loc_384 : location_info := LocationInfo file_1 283 4 283 79.
  Definition loc_385 : location_info := LocationInfo file_1 284 4 284 46.
  Definition loc_386 : location_info := LocationInfo file_1 285 4 285 50.
  Definition loc_387 : location_info := LocationInfo file_1 286 4 286 37.
  Definition loc_388 : location_info := LocationInfo file_1 286 4 286 24.
  Definition loc_389 : location_info := LocationInfo file_1 286 4 286 13.
  Definition loc_390 : location_info := LocationInfo file_1 286 4 286 5.
  Definition loc_391 : location_info := LocationInfo file_1 286 4 286 5.
  Definition loc_392 : location_info := LocationInfo file_1 286 27 286 36.
  Definition loc_393 : location_info := LocationInfo file_1 286 27 286 36.
  Definition loc_394 : location_info := LocationInfo file_1 285 4 285 19.
  Definition loc_395 : location_info := LocationInfo file_1 285 4 285 13.
  Definition loc_396 : location_info := LocationInfo file_1 285 4 285 13.
  Definition loc_397 : location_info := LocationInfo file_1 285 22 285 49.
  Definition loc_398 : location_info := LocationInfo file_1 285 22 285 33.
  Definition loc_399 : location_info := LocationInfo file_1 285 22 285 33.
  Definition loc_400 : location_info := LocationInfo file_1 285 22 285 27.
  Definition loc_401 : location_info := LocationInfo file_1 285 22 285 27.
  Definition loc_402 : location_info := LocationInfo file_1 285 36 285 49.
  Definition loc_403 : location_info := LocationInfo file_1 285 36 285 49.
  Definition loc_404 : location_info := LocationInfo file_1 285 36 285 37.
  Definition loc_405 : location_info := LocationInfo file_1 285 36 285 37.
  Definition loc_406 : location_info := LocationInfo file_1 284 4 284 25.
  Definition loc_407 : location_info := LocationInfo file_1 284 4 284 13.
  Definition loc_408 : location_info := LocationInfo file_1 284 4 284 13.
  Definition loc_409 : location_info := LocationInfo file_1 284 28 284 45.
  Definition loc_410 : location_info := LocationInfo file_1 284 28 284 45.
  Definition loc_411 : location_info := LocationInfo file_1 284 28 284 33.
  Definition loc_412 : location_info := LocationInfo file_1 284 28 284 33.
  Definition loc_413 : location_info := LocationInfo file_1 283 4 283 13.
  Definition loc_414 : location_info := LocationInfo file_1 283 16 283 78.
  Definition loc_415 : location_info := LocationInfo file_1 283 38 283 78.
  Definition loc_416 : location_info := LocationInfo file_1 283 39 283 61.
  Definition loc_417 : location_info := LocationInfo file_1 283 56 283 61.
  Definition loc_418 : location_info := LocationInfo file_1 283 56 283 61.
  Definition loc_419 : location_info := LocationInfo file_1 283 64 283 77.
  Definition loc_420 : location_info := LocationInfo file_1 283 64 283 77.
  Definition loc_421 : location_info := LocationInfo file_1 283 64 283 65.
  Definition loc_422 : location_info := LocationInfo file_1 283 64 283 65.
  Definition loc_423 : location_info := LocationInfo file_1 280 6 280 34.
  Definition loc_424 : location_info := LocationInfo file_1 280 6 280 19.
  Definition loc_425 : location_info := LocationInfo file_1 280 6 280 19.
  Definition loc_426 : location_info := LocationInfo file_1 280 6 280 7.
  Definition loc_427 : location_info := LocationInfo file_1 280 6 280 7.
  Definition loc_428 : location_info := LocationInfo file_1 280 23 280 34.
  Definition loc_429 : location_info := LocationInfo file_1 280 23 280 34.
  Definition loc_430 : location_info := LocationInfo file_1 280 23 280 28.
  Definition loc_431 : location_info := LocationInfo file_1 280 23 280 28.
  Definition loc_432 : location_info := LocationInfo file_1 274 31 278 3.
  Definition loc_433 : location_info := LocationInfo file_1 276 4 276 25.
  Definition loc_434 : location_info := LocationInfo file_1 277 4 277 14.
  Definition loc_435 : location_info := LocationInfo file_1 276 4 276 7.
  Definition loc_436 : location_info := LocationInfo file_1 276 10 276 24.
  Definition loc_438 : location_info := LocationInfo file_1 274 6 274 29.
  Definition loc_439 : location_info := LocationInfo file_1 274 6 274 11.
  Definition loc_440 : location_info := LocationInfo file_1 274 6 274 11.
  Definition loc_441 : location_info := LocationInfo file_1 274 15 274 29.
  Definition loc_442 : location_info := LocationInfo file_1 273 2 273 7.
  Definition loc_443 : location_info := LocationInfo file_1 273 10 273 30.
  Definition loc_444 : location_info := LocationInfo file_1 273 10 273 30.
  Definition loc_445 : location_info := LocationInfo file_1 273 10 273 19.
  Definition loc_446 : location_info := LocationInfo file_1 273 10 273 11.
  Definition loc_447 : location_info := LocationInfo file_1 273 10 273 11.
  Definition loc_448 : location_info := LocationInfo file_1 264 46 270 3.
  Definition loc_449 : location_info := LocationInfo file_1 265 4 265 53.
  Definition loc_450 : location_info := LocationInfo file_1 267 4 267 39.
  Definition loc_451 : location_info := LocationInfo file_1 268 4 268 16.
  Definition loc_452 : location_info := LocationInfo file_1 269 4 269 14.
  Definition loc_453 : location_info := LocationInfo file_1 268 4 268 7.
  Definition loc_454 : location_info := LocationInfo file_1 268 10 268 15.
  Definition loc_455 : location_info := LocationInfo file_1 268 10 268 15.
  Definition loc_456 : location_info := LocationInfo file_1 267 4 267 24.
  Definition loc_457 : location_info := LocationInfo file_1 267 4 267 13.
  Definition loc_458 : location_info := LocationInfo file_1 267 4 267 5.
  Definition loc_459 : location_info := LocationInfo file_1 267 4 267 5.
  Definition loc_460 : location_info := LocationInfo file_1 267 27 267 38.
  Definition loc_461 : location_info := LocationInfo file_1 267 27 267 38.
  Definition loc_462 : location_info := LocationInfo file_1 267 27 267 32.
  Definition loc_463 : location_info := LocationInfo file_1 267 27 267 32.
  Definition loc_464 : location_info := LocationInfo file_1 265 32 265 52.
  Definition loc_465 : location_info := LocationInfo file_1 265 32 265 52.
  Definition loc_466 : location_info := LocationInfo file_1 265 32 265 41.
  Definition loc_467 : location_info := LocationInfo file_1 265 32 265 33.
  Definition loc_468 : location_info := LocationInfo file_1 265 32 265 33.
  Definition loc_472 : location_info := LocationInfo file_1 264 6 264 44.
  Definition loc_473 : location_info := LocationInfo file_1 264 6 264 26.
  Definition loc_474 : location_info := LocationInfo file_1 264 6 264 26.
  Definition loc_475 : location_info := LocationInfo file_1 264 6 264 15.
  Definition loc_476 : location_info := LocationInfo file_1 264 6 264 7.
  Definition loc_477 : location_info := LocationInfo file_1 264 6 264 7.
  Definition loc_478 : location_info := LocationInfo file_1 264 30 264 44.
  Definition loc_479 : location_info := LocationInfo file_1 263 27 263 39.
  Definition loc_480 : location_info := LocationInfo file_1 263 28 263 39.
  Definition loc_481 : location_info := LocationInfo file_1 263 29 263 30.
  Definition loc_482 : location_info := LocationInfo file_1 263 29 263 30.
  Definition loc_483 : location_info := LocationInfo file_1 262 2 262 9.
  Definition loc_484 : location_info := LocationInfo file_1 262 2 262 9.
  Definition loc_485 : location_info := LocationInfo file_1 262 10 262 18.
  Definition loc_486 : location_info := LocationInfo file_1 262 11 262 18.
  Definition loc_487 : location_info := LocationInfo file_1 262 11 262 12.
  Definition loc_488 : location_info := LocationInfo file_1 262 11 262 12.
  Definition loc_491 : location_info := LocationInfo file_1 307 2 307 41.
  Definition loc_492 : location_info := LocationInfo file_1 308 2 310 3.
  Definition loc_493 : location_info := LocationInfo file_1 311 2 311 18.
  Definition loc_494 : location_info := LocationInfo file_1 315 2 321 3.
  Definition loc_495 : location_info := LocationInfo file_1 323 2 323 24.
  Definition loc_496 : location_info := LocationInfo file_1 323 9 323 23.
  Definition loc_497 : location_info := LocationInfo file_1 315 2 321 3.
  Definition loc_498 : location_info := LocationInfo file_1 315 30 321 3.
  Definition loc_499 : location_info := LocationInfo file_1 316 4 316 37.
  Definition loc_500 : location_info := LocationInfo file_1 317 4 319 5.
  Definition loc_501 : location_info := LocationInfo file_1 320 4 320 20.
  Definition loc_502 : location_info := LocationInfo file_1 315 2 321 3.
  Definition loc_503 : location_info := LocationInfo file_1 315 2 321 3.
  Definition loc_504 : location_info := LocationInfo file_1 320 4 320 5.
  Definition loc_505 : location_info := LocationInfo file_1 320 8 320 19.
  Definition loc_506 : location_info := LocationInfo file_1 320 8 320 19.
  Definition loc_507 : location_info := LocationInfo file_1 320 8 320 9.
  Definition loc_508 : location_info := LocationInfo file_1 320 8 320 9.
  Definition loc_509 : location_info := LocationInfo file_1 317 31 319 5.
  Definition loc_510 : location_info := LocationInfo file_1 318 6 318 17.
  Definition loc_511 : location_info := LocationInfo file_1 318 13 318 16.
  Definition loc_512 : location_info := LocationInfo file_1 318 13 318 16.
  Definition loc_514 : location_info := LocationInfo file_1 317 8 317 29.
  Definition loc_515 : location_info := LocationInfo file_1 317 8 317 11.
  Definition loc_516 : location_info := LocationInfo file_1 317 8 317 11.
  Definition loc_517 : location_info := LocationInfo file_1 317 15 317 29.
  Definition loc_518 : location_info := LocationInfo file_1 316 4 316 7.
  Definition loc_519 : location_info := LocationInfo file_1 316 10 316 36.
  Definition loc_520 : location_info := LocationInfo file_1 316 10 316 33.
  Definition loc_521 : location_info := LocationInfo file_1 316 10 316 33.
  Definition loc_522 : location_info := LocationInfo file_1 316 34 316 35.
  Definition loc_523 : location_info := LocationInfo file_1 316 34 316 35.
  Definition loc_524 : location_info := LocationInfo file_1 315 9 315 28.
  Definition loc_525 : location_info := LocationInfo file_1 315 9 315 10.
  Definition loc_526 : location_info := LocationInfo file_1 315 9 315 10.
  Definition loc_527 : location_info := LocationInfo file_1 315 14 315 28.
  Definition loc_528 : location_info := LocationInfo file_1 311 2 311 3.
  Definition loc_529 : location_info := LocationInfo file_1 311 6 311 17.
  Definition loc_530 : location_info := LocationInfo file_1 311 6 311 17.
  Definition loc_531 : location_info := LocationInfo file_1 311 6 311 7.
  Definition loc_532 : location_info := LocationInfo file_1 311 6 311 7.
  Definition loc_533 : location_info := LocationInfo file_1 308 29 310 3.
  Definition loc_534 : location_info := LocationInfo file_1 309 4 309 15.
  Definition loc_535 : location_info := LocationInfo file_1 309 11 309 14.
  Definition loc_536 : location_info := LocationInfo file_1 309 11 309 14.
  Definition loc_538 : location_info := LocationInfo file_1 308 6 308 27.
  Definition loc_539 : location_info := LocationInfo file_1 308 6 308 9.
  Definition loc_540 : location_info := LocationInfo file_1 308 6 308 9.
  Definition loc_541 : location_info := LocationInfo file_1 308 13 308 27.
  Definition loc_542 : location_info := LocationInfo file_1 307 14 307 40.
  Definition loc_543 : location_info := LocationInfo file_1 307 14 307 37.
  Definition loc_544 : location_info := LocationInfo file_1 307 14 307 37.
  Definition loc_545 : location_info := LocationInfo file_1 307 38 307 39.
  Definition loc_546 : location_info := LocationInfo file_1 307 38 307 39.
  Definition loc_551 : location_info := LocationInfo file_1 363 2 363 29.
  Definition loc_552 : location_info := LocationInfo file_1 365 2 365 25.
  Definition loc_553 : location_info := LocationInfo file_1 367 2 367 20.
  Definition loc_554 : location_info := LocationInfo file_1 368 2 368 40.
  Definition loc_555 : location_info := LocationInfo file_1 368 40 368 3.
  Definition loc_556 : location_info := LocationInfo file_1 374 2 374 31.
  Definition loc_557 : location_info := LocationInfo file_1 384 2 429 3.
  Definition loc_558 : location_info := LocationInfo file_1 431 2 431 22.
  Definition loc_559 : location_info := LocationInfo file_1 433 2 433 13.
  Definition loc_560 : location_info := LocationInfo file_1 433 9 433 12.
  Definition loc_561 : location_info := LocationInfo file_1 433 9 433 12.
  Definition loc_562 : location_info := LocationInfo file_1 431 2 431 11.
  Definition loc_563 : location_info := LocationInfo file_1 431 2 431 11.
  Definition loc_564 : location_info := LocationInfo file_1 431 12 431 20.
  Definition loc_565 : location_info := LocationInfo file_1 431 13 431 20.
  Definition loc_566 : location_info := LocationInfo file_1 431 13 431 14.
  Definition loc_567 : location_info := LocationInfo file_1 431 13 431 14.
  Definition loc_568 : location_info := LocationInfo file_1 384 2 429 3.
  Definition loc_569 : location_info := LocationInfo file_1 384 34 429 3.
  Definition loc_570 : location_info := LocationInfo file_1 387 4 387 38.
  Definition loc_571 : location_info := LocationInfo file_1 390 4 390 51.
  Definition loc_572 : location_info := LocationInfo file_1 390 51 390 5.
  Definition loc_573 : location_info := LocationInfo file_1 392 4 392 67.
  Definition loc_574 : location_info := LocationInfo file_1 399 4 426 5.
  Definition loc_575 : location_info := LocationInfo file_1 428 4 428 30.
  Definition loc_576 : location_info := LocationInfo file_1 384 2 429 3.
  Definition loc_577 : location_info := LocationInfo file_1 384 2 429 3.
  Definition loc_578 : location_info := LocationInfo file_1 428 4 428 8.
  Definition loc_579 : location_info := LocationInfo file_1 428 11 428 29.
  Definition loc_580 : location_info := LocationInfo file_1 428 12 428 29.
  Definition loc_581 : location_info := LocationInfo file_1 428 12 428 17.
  Definition loc_582 : location_info := LocationInfo file_1 428 12 428 17.
  Definition loc_583 : location_info := LocationInfo file_1 399 61 426 5.
  Definition loc_584 : location_info := LocationInfo file_1 400 6 400 38.
  Definition loc_585 : location_info := LocationInfo file_1 401 6 401 57.
  Definition loc_586 : location_info := LocationInfo file_1 402 6 402 42.
  Definition loc_587 : location_info := LocationInfo file_1 402 42 402 7.
  Definition loc_588 : location_info := LocationInfo file_1 403 6 403 52.
  Definition loc_589 : location_info := LocationInfo file_1 405 6 412 7.
  Definition loc_590 : location_info := LocationInfo file_1 418 6 422 7.
  Definition loc_591 : location_info := LocationInfo file_1 424 6 424 26.
  Definition loc_592 : location_info := LocationInfo file_1 425 6 425 12.
  Definition loc_593 : location_info := LocationInfo file_1 424 6 424 9.
  Definition loc_594 : location_info := LocationInfo file_1 424 12 424 25.
  Definition loc_595 : location_info := LocationInfo file_1 424 20 424 25.
  Definition loc_596 : location_info := LocationInfo file_1 424 20 424 25.
  Definition loc_597 : location_info := LocationInfo file_1 418 41 422 7.
  Definition loc_598 : location_info := LocationInfo file_1 419 8 419 34.
  Definition loc_599 : location_info := LocationInfo file_1 420 8 420 22.
  Definition loc_600 : location_info := LocationInfo file_1 421 8 421 35.
  Definition loc_601 : location_info := LocationInfo file_1 421 8 421 19.
  Definition loc_602 : location_info := LocationInfo file_1 421 8 421 13.
  Definition loc_603 : location_info := LocationInfo file_1 421 8 421 13.
  Definition loc_604 : location_info := LocationInfo file_1 421 22 421 34.
  Definition loc_605 : location_info := LocationInfo file_1 421 22 421 34.
  Definition loc_606 : location_info := LocationInfo file_1 420 8 420 13.
  Definition loc_607 : location_info := LocationInfo file_1 420 9 420 13.
  Definition loc_608 : location_info := LocationInfo file_1 420 9 420 13.
  Definition loc_609 : location_info := LocationInfo file_1 420 16 420 21.
  Definition loc_610 : location_info := LocationInfo file_1 420 16 420 21.
  Definition loc_611 : location_info := LocationInfo file_1 419 8 419 25.
  Definition loc_612 : location_info := LocationInfo file_1 419 8 419 13.
  Definition loc_613 : location_info := LocationInfo file_1 419 8 419 13.
  Definition loc_614 : location_info := LocationInfo file_1 419 28 419 33.
  Definition loc_615 : location_info := LocationInfo file_1 419 28 419 33.
  Definition loc_616 : location_info := LocationInfo file_1 419 29 419 33.
  Definition loc_617 : location_info := LocationInfo file_1 419 29 419 33.
  Definition loc_619 : location_info := LocationInfo file_1 418 10 418 39.
  Definition loc_620 : location_info := LocationInfo file_1 418 10 418 22.
  Definition loc_621 : location_info := LocationInfo file_1 418 10 418 22.
  Definition loc_622 : location_info := LocationInfo file_1 418 26 418 39.
  Definition loc_623 : location_info := LocationInfo file_1 418 26 418 39.
  Definition loc_624 : location_info := LocationInfo file_1 418 26 418 27.
  Definition loc_625 : location_info := LocationInfo file_1 418 26 418 27.
  Definition loc_626 : location_info := LocationInfo file_1 405 62 407 7.
  Definition loc_627 : location_info := LocationInfo file_1 406 8 406 27.
  Definition loc_628 : location_info := LocationInfo file_1 406 8 406 13.
  Definition loc_629 : location_info := LocationInfo file_1 406 9 406 13.
  Definition loc_630 : location_info := LocationInfo file_1 406 9 406 13.
  Definition loc_631 : location_info := LocationInfo file_1 406 16 406 26.
  Definition loc_632 : location_info := LocationInfo file_1 406 16 406 26.
  Definition loc_633 : location_info := LocationInfo file_1 407 13 412 7.
  Definition loc_634 : location_info := LocationInfo file_1 408 8 408 76.
  Definition loc_635 : location_info := LocationInfo file_1 409 8 409 78.
  Definition loc_636 : location_info := LocationInfo file_1 410 8 410 43.
  Definition loc_637 : location_info := LocationInfo file_1 411 8 411 26.
  Definition loc_638 : location_info := LocationInfo file_1 411 8 411 13.
  Definition loc_639 : location_info := LocationInfo file_1 411 9 411 13.
  Definition loc_640 : location_info := LocationInfo file_1 411 9 411 13.
  Definition loc_641 : location_info := LocationInfo file_1 411 16 411 25.
  Definition loc_642 : location_info := LocationInfo file_1 411 16 411 25.
  Definition loc_643 : location_info := LocationInfo file_1 410 8 410 29.
  Definition loc_644 : location_info := LocationInfo file_1 410 8 410 17.
  Definition loc_645 : location_info := LocationInfo file_1 410 8 410 17.
  Definition loc_646 : location_info := LocationInfo file_1 410 32 410 42.
  Definition loc_647 : location_info := LocationInfo file_1 410 32 410 42.
  Definition loc_648 : location_info := LocationInfo file_1 409 8 409 23.
  Definition loc_649 : location_info := LocationInfo file_1 409 8 409 17.
  Definition loc_650 : location_info := LocationInfo file_1 409 8 409 17.
  Definition loc_651 : location_info := LocationInfo file_1 409 26 409 77.
  Definition loc_652 : location_info := LocationInfo file_1 409 26 409 36.
  Definition loc_653 : location_info := LocationInfo file_1 409 26 409 36.
  Definition loc_654 : location_info := LocationInfo file_1 409 39 409 77.
  Definition loc_655 : location_info := LocationInfo file_1 409 40 409 52.
  Definition loc_656 : location_info := LocationInfo file_1 409 40 409 52.
  Definition loc_657 : location_info := LocationInfo file_1 409 55 409 76.
  Definition loc_658 : location_info := LocationInfo file_1 409 55 409 60.
  Definition loc_659 : location_info := LocationInfo file_1 409 55 409 60.
  Definition loc_660 : location_info := LocationInfo file_1 409 63 409 76.
  Definition loc_661 : location_info := LocationInfo file_1 409 63 409 76.
  Definition loc_662 : location_info := LocationInfo file_1 409 63 409 64.
  Definition loc_663 : location_info := LocationInfo file_1 409 63 409 64.
  Definition loc_664 : location_info := LocationInfo file_1 408 8 408 17.
  Definition loc_665 : location_info := LocationInfo file_1 408 20 408 75.
  Definition loc_666 : location_info := LocationInfo file_1 408 42 408 75.
  Definition loc_667 : location_info := LocationInfo file_1 408 43 408 48.
  Definition loc_668 : location_info := LocationInfo file_1 408 43 408 48.
  Definition loc_669 : location_info := LocationInfo file_1 408 51 408 74.
  Definition loc_670 : location_info := LocationInfo file_1 408 52 408 57.
  Definition loc_671 : location_info := LocationInfo file_1 408 52 408 57.
  Definition loc_672 : location_info := LocationInfo file_1 408 60 408 73.
  Definition loc_673 : location_info := LocationInfo file_1 408 60 408 73.
  Definition loc_674 : location_info := LocationInfo file_1 408 60 408 61.
  Definition loc_675 : location_info := LocationInfo file_1 408 60 408 61.
  Definition loc_676 : location_info := LocationInfo file_1 405 10 405 60.
  Definition loc_677 : location_info := LocationInfo file_1 405 10 405 46.
  Definition loc_678 : location_info := LocationInfo file_1 405 10 405 22.
  Definition loc_679 : location_info := LocationInfo file_1 405 10 405 22.
  Definition loc_680 : location_info := LocationInfo file_1 405 25 405 46.
  Definition loc_681 : location_info := LocationInfo file_1 405 25 405 30.
  Definition loc_682 : location_info := LocationInfo file_1 405 25 405 30.
  Definition loc_683 : location_info := LocationInfo file_1 405 33 405 46.
  Definition loc_684 : location_info := LocationInfo file_1 405 33 405 46.
  Definition loc_685 : location_info := LocationInfo file_1 405 33 405 34.
  Definition loc_686 : location_info := LocationInfo file_1 405 33 405 34.
  Definition loc_687 : location_info := LocationInfo file_1 405 50 405 60.
  Definition loc_688 : location_info := LocationInfo file_1 405 50 405 60.
  Definition loc_689 : location_info := LocationInfo file_1 403 6 403 11.
  Definition loc_690 : location_info := LocationInfo file_1 403 14 403 51.
  Definition loc_691 : location_info := LocationInfo file_1 403 14 403 36.
  Definition loc_692 : location_info := LocationInfo file_1 403 31 403 36.
  Definition loc_693 : location_info := LocationInfo file_1 403 31 403 36.
  Definition loc_694 : location_info := LocationInfo file_1 403 39 403 51.
  Definition loc_695 : location_info := LocationInfo file_1 403 39 403 51.
  Definition loc_696 : location_info := LocationInfo file_1 402 32 402 41.
  Definition loc_697 : location_info := LocationInfo file_1 402 33 402 41.
  Definition loc_698 : location_info := LocationInfo file_1 402 35 402 40.
  Definition loc_699 : location_info := LocationInfo file_1 402 35 402 40.
  Definition loc_700 : location_info := LocationInfo file_1 401 39 401 56.
  Definition loc_701 : location_info := LocationInfo file_1 401 39 401 56.
  Definition loc_702 : location_info := LocationInfo file_1 401 39 401 44.
  Definition loc_703 : location_info := LocationInfo file_1 401 39 401 44.
  Definition loc_706 : location_info := LocationInfo file_1 400 26 400 37.
  Definition loc_707 : location_info := LocationInfo file_1 400 26 400 37.
  Definition loc_708 : location_info := LocationInfo file_1 400 26 400 31.
  Definition loc_709 : location_info := LocationInfo file_1 400 26 400 31.
  Definition loc_713 : location_info := LocationInfo file_1 399 8 399 59.
  Definition loc_714 : location_info := LocationInfo file_1 399 8 399 44.
  Definition loc_715 : location_info := LocationInfo file_1 399 8 399 20.
  Definition loc_716 : location_info := LocationInfo file_1 399 8 399 20.
  Definition loc_717 : location_info := LocationInfo file_1 399 23 399 44.
  Definition loc_718 : location_info := LocationInfo file_1 399 23 399 28.
  Definition loc_719 : location_info := LocationInfo file_1 399 23 399 28.
  Definition loc_720 : location_info := LocationInfo file_1 399 31 399 44.
  Definition loc_721 : location_info := LocationInfo file_1 399 31 399 44.
  Definition loc_722 : location_info := LocationInfo file_1 399 31 399 32.
  Definition loc_723 : location_info := LocationInfo file_1 399 31 399 32.
  Definition loc_724 : location_info := LocationInfo file_1 399 48 399 59.
  Definition loc_725 : location_info := LocationInfo file_1 399 48 399 59.
  Definition loc_726 : location_info := LocationInfo file_1 399 48 399 53.
  Definition loc_727 : location_info := LocationInfo file_1 399 48 399 53.
  Definition loc_728 : location_info := LocationInfo file_1 392 4 392 20.
  Definition loc_729 : location_info := LocationInfo file_1 392 4 392 20.
  Definition loc_730 : location_info := LocationInfo file_1 392 21 392 43.
  Definition loc_731 : location_info := LocationInfo file_1 392 38 392 43.
  Definition loc_732 : location_info := LocationInfo file_1 392 38 392 43.
  Definition loc_733 : location_info := LocationInfo file_1 392 45 392 50.
  Definition loc_734 : location_info := LocationInfo file_1 392 45 392 50.
  Definition loc_735 : location_info := LocationInfo file_1 392 52 392 65.
  Definition loc_736 : location_info := LocationInfo file_1 392 53 392 65.
  Definition loc_737 : location_info := LocationInfo file_1 390 41 390 50.
  Definition loc_738 : location_info := LocationInfo file_1 390 42 390 50.
  Definition loc_739 : location_info := LocationInfo file_1 390 44 390 49.
  Definition loc_740 : location_info := LocationInfo file_1 390 44 390 49.
  Definition loc_741 : location_info := LocationInfo file_1 387 32 387 37.
  Definition loc_742 : location_info := LocationInfo file_1 387 32 387 37.
  Definition loc_743 : location_info := LocationInfo file_1 387 33 387 37.
  Definition loc_744 : location_info := LocationInfo file_1 387 33 387 37.
  Definition loc_747 : location_info := LocationInfo file_1 384 9 384 32.
  Definition loc_748 : location_info := LocationInfo file_1 384 9 384 14.
  Definition loc_749 : location_info := LocationInfo file_1 384 9 384 14.
  Definition loc_750 : location_info := LocationInfo file_1 384 10 384 14.
  Definition loc_751 : location_info := LocationInfo file_1 384 10 384 14.
  Definition loc_752 : location_info := LocationInfo file_1 384 18 384 32.
  Definition loc_753 : location_info := LocationInfo file_1 374 2 374 6.
  Definition loc_754 : location_info := LocationInfo file_1 374 9 374 30.
  Definition loc_755 : location_info := LocationInfo file_1 374 10 374 30.
  Definition loc_756 : location_info := LocationInfo file_1 374 10 374 19.
  Definition loc_757 : location_info := LocationInfo file_1 374 10 374 11.
  Definition loc_758 : location_info := LocationInfo file_1 374 10 374 11.
  Definition loc_759 : location_info := LocationInfo file_1 368 27 368 39.
  Definition loc_760 : location_info := LocationInfo file_1 368 28 368 39.
  Definition loc_761 : location_info := LocationInfo file_1 368 29 368 30.
  Definition loc_762 : location_info := LocationInfo file_1 368 29 368 30.
  Definition loc_763 : location_info := LocationInfo file_1 367 2 367 9.
  Definition loc_764 : location_info := LocationInfo file_1 367 2 367 9.
  Definition loc_765 : location_info := LocationInfo file_1 367 10 367 18.
  Definition loc_766 : location_info := LocationInfo file_1 367 11 367 18.
  Definition loc_767 : location_info := LocationInfo file_1 367 11 367 12.
  Definition loc_768 : location_info := LocationInfo file_1 367 11 367 12.
  Definition loc_769 : location_info := LocationInfo file_1 365 2 365 7.
  Definition loc_770 : location_info := LocationInfo file_1 365 2 365 24.
  Definition loc_771 : location_info := LocationInfo file_1 365 2 365 7.
  Definition loc_772 : location_info := LocationInfo file_1 365 2 365 7.
  Definition loc_773 : location_info := LocationInfo file_1 365 11 365 24.
  Definition loc_774 : location_info := LocationInfo file_1 365 11 365 24.
  Definition loc_775 : location_info := LocationInfo file_1 365 11 365 12.
  Definition loc_776 : location_info := LocationInfo file_1 365 11 365 12.
  Definition loc_777 : location_info := LocationInfo file_1 363 14 363 28.
  Definition loc_782 : location_info := LocationInfo file_1 456 2 456 66.
  Definition loc_783 : location_info := LocationInfo file_1 458 2 460 3.
  Definition loc_784 : location_info := LocationInfo file_1 462 2 462 18.
  Definition loc_785 : location_info := LocationInfo file_1 466 2 475 3.
  Definition loc_786 : location_info := LocationInfo file_1 477 2 477 24.
  Definition loc_787 : location_info := LocationInfo file_1 477 9 477 23.
  Definition loc_788 : location_info := LocationInfo file_1 466 2 475 3.
  Definition loc_789 : location_info := LocationInfo file_1 466 30 475 3.
  Definition loc_790 : location_info := LocationInfo file_1 467 4 467 62.
  Definition loc_791 : location_info := LocationInfo file_1 469 4 471 5.
  Definition loc_792 : location_info := LocationInfo file_1 473 4 473 20.
  Definition loc_793 : location_info := LocationInfo file_1 466 2 475 3.
  Definition loc_794 : location_info := LocationInfo file_1 466 2 475 3.
  Definition loc_795 : location_info := LocationInfo file_1 473 4 473 5.
  Definition loc_796 : location_info := LocationInfo file_1 473 8 473 19.
  Definition loc_797 : location_info := LocationInfo file_1 473 8 473 19.
  Definition loc_798 : location_info := LocationInfo file_1 473 8 473 9.
  Definition loc_799 : location_info := LocationInfo file_1 473 8 473 9.
  Definition loc_800 : location_info := LocationInfo file_1 469 31 471 5.
  Definition loc_801 : location_info := LocationInfo file_1 470 6 470 17.
  Definition loc_802 : location_info := LocationInfo file_1 470 13 470 16.
  Definition loc_803 : location_info := LocationInfo file_1 470 13 470 16.
  Definition loc_805 : location_info := LocationInfo file_1 469 8 469 29.
  Definition loc_806 : location_info := LocationInfo file_1 469 8 469 11.
  Definition loc_807 : location_info := LocationInfo file_1 469 8 469 11.
  Definition loc_808 : location_info := LocationInfo file_1 469 15 469 29.
  Definition loc_809 : location_info := LocationInfo file_1 467 4 467 7.
  Definition loc_810 : location_info := LocationInfo file_1 467 10 467 61.
  Definition loc_811 : location_info := LocationInfo file_1 467 10 467 44.
  Definition loc_812 : location_info := LocationInfo file_1 467 10 467 44.
  Definition loc_813 : location_info := LocationInfo file_1 467 45 467 46.
  Definition loc_814 : location_info := LocationInfo file_1 467 45 467 46.
  Definition loc_815 : location_info := LocationInfo file_1 467 48 467 53.
  Definition loc_816 : location_info := LocationInfo file_1 467 48 467 53.
  Definition loc_817 : location_info := LocationInfo file_1 467 55 467 60.
  Definition loc_818 : location_info := LocationInfo file_1 467 55 467 60.
  Definition loc_819 : location_info := LocationInfo file_1 466 9 466 28.
  Definition loc_820 : location_info := LocationInfo file_1 466 9 466 10.
  Definition loc_821 : location_info := LocationInfo file_1 466 9 466 10.
  Definition loc_822 : location_info := LocationInfo file_1 466 14 466 28.
  Definition loc_823 : location_info := LocationInfo file_1 462 2 462 3.
  Definition loc_824 : location_info := LocationInfo file_1 462 6 462 17.
  Definition loc_825 : location_info := LocationInfo file_1 462 6 462 17.
  Definition loc_826 : location_info := LocationInfo file_1 462 6 462 7.
  Definition loc_827 : location_info := LocationInfo file_1 462 6 462 7.
  Definition loc_828 : location_info := LocationInfo file_1 458 29 460 3.
  Definition loc_829 : location_info := LocationInfo file_1 459 4 459 15.
  Definition loc_830 : location_info := LocationInfo file_1 459 11 459 14.
  Definition loc_831 : location_info := LocationInfo file_1 459 11 459 14.
  Definition loc_833 : location_info := LocationInfo file_1 458 6 458 27.
  Definition loc_834 : location_info := LocationInfo file_1 458 6 458 9.
  Definition loc_835 : location_info := LocationInfo file_1 458 6 458 9.
  Definition loc_836 : location_info := LocationInfo file_1 458 13 458 27.
  Definition loc_837 : location_info := LocationInfo file_1 456 14 456 65.
  Definition loc_838 : location_info := LocationInfo file_1 456 14 456 48.
  Definition loc_839 : location_info := LocationInfo file_1 456 14 456 48.
  Definition loc_840 : location_info := LocationInfo file_1 456 49 456 50.
  Definition loc_841 : location_info := LocationInfo file_1 456 49 456 50.
  Definition loc_842 : location_info := LocationInfo file_1 456 52 456 57.
  Definition loc_843 : location_info := LocationInfo file_1 456 52 456 57.
  Definition loc_844 : location_info := LocationInfo file_1 456 59 456 64.
  Definition loc_845 : location_info := LocationInfo file_1 456 59 456 64.

  (* Definition of struct [atomic_flag]. *)
  Program Definition struct_atomic_flag := {|
    sl_members := [
      (Some "_Value", it_layout bool_it)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [spinlock]. *)
  Program Definition struct_spinlock := {|
    sl_members := [
      (Some "lock", it_layout bool_it)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [mpool_chunk]. *)
  Program Definition struct_mpool_chunk := {|
    sl_members := [
      (Some "size", it_layout size_t);
      (Some "next_chunk", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [mpool_entry]. *)
  Program Definition struct_mpool_entry := {|
    sl_members := [
      (Some "next", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [mpool_locked_inner]. *)
  Program Definition struct_mpool_locked_inner := {|
    sl_members := [
      (Some "chunk_list", void*);
      (Some "entry_list", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [mpool]. *)
  Program Definition struct_mpool := {|
    sl_members := [
      (Some "entry_size", it_layout size_t);
      (Some "lock", layout_of struct_spinlock);
      (None, Layout 7%nat 0%nat);
      (Some "locked", layout_of struct_mpool_locked_inner);
      (Some "fallback", void*)
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

  (* Definition of function [mpool_add_chunk]. *)
  Definition impl_mpool_add_chunk (global_sl_lock global_sl_unlock : loc): function := {|
    f_args := [
      ("p", void*);
      ("begin", void*);
      ("size", it_layout size_t)
    ];
    f_local_vars := [
      ("chunk", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_11 ;
        expr: (LocInfoE loc_71 (&(LocInfoE loc_72 ((LocInfoE loc_73 (!{PtrOp} (LocInfoE loc_74 ("p")))) at{struct_mpool} "entry_size")))) ;
        locinfo: loc_66 ;
        if: LocInfoE loc_66 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_66 ((LocInfoE loc_67 (use{IntOp size_t} (LocInfoE loc_68 ("size")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_69 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_70 (i2v 0 i32)))))))
        then
        locinfo: loc_63 ;
          Goto "#2"
        else
        locinfo: loc_14 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_14 ;
        LocInfoE loc_59 ("chunk") <-{ PtrOp }
          LocInfoE loc_60 (use{PtrOp} (LocInfoE loc_61 ("begin"))) ;
        locinfo: loc_15 ;
        LocInfoE loc_54 ((LocInfoE loc_55 (!{PtrOp} (LocInfoE loc_56 ("chunk")))) at{struct_mpool_chunk} "size") <-{ IntOp size_t }
          LocInfoE loc_57 (use{IntOp size_t} (LocInfoE loc_58 ("size"))) ;
        locinfo: loc_16 ;
        expr: (LocInfoE loc_16 (Call (LocInfoE loc_49 (global_sl_lock)) [@{expr} LocInfoE loc_50 (&(LocInfoE loc_51 ((LocInfoE loc_52 (!{PtrOp} (LocInfoE loc_53 ("p")))) at{struct_mpool} "lock"))) ])) ;
        locinfo: loc_17 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_44 (&(LocInfoE loc_45 ((LocInfoE loc_46 (!{PtrOp} (LocInfoE loc_47 ("p")))) at{struct_mpool} "locked")))) ;
        locinfo: loc_19 ;
        LocInfoE loc_36 ((LocInfoE loc_37 (!{PtrOp} (LocInfoE loc_38 ("chunk")))) at{struct_mpool_chunk} "next_chunk") <-{ PtrOp }
          LocInfoE loc_39 (use{PtrOp} (LocInfoE loc_40 ((LocInfoE loc_41 ((LocInfoE loc_42 (!{PtrOp} (LocInfoE loc_43 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list"))) ;
        locinfo: loc_20 ;
        LocInfoE loc_30 ((LocInfoE loc_31 ((LocInfoE loc_32 (!{PtrOp} (LocInfoE loc_33 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list") <-{ PtrOp }
          LocInfoE loc_34 (use{PtrOp} (LocInfoE loc_35 ("chunk"))) ;
        locinfo: loc_21 ;
        expr: (LocInfoE loc_21 (Call (LocInfoE loc_25 (global_sl_unlock)) [@{expr} LocInfoE loc_26 (AnnotExpr 1%nat LockA (LocInfoE loc_26 (&(LocInfoE loc_27 ((LocInfoE loc_28 (!{PtrOp} (LocInfoE loc_29 ("p")))) at{struct_mpool} "lock"))))) ])) ;
        locinfo: loc_22 ;
        Return (LocInfoE loc_23 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_23 (i2v 1 i32))))
      ]> $
      <[ "#2" :=
        locinfo: loc_63 ;
        Return (LocInfoE loc_64 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_64 (i2v 0 i32))))
      ]> $
      <[ "#3" :=
        locinfo: loc_14 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [mpool_free]. *)
  Definition impl_mpool_free (global_sl_lock global_sl_unlock : loc): function := {|
    f_args := [
      ("p", void*);
      ("ptr", void*)
    ];
    f_local_vars := [
      ("e", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "e" <-{ PtrOp }
          LocInfoE loc_114 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_114 (use{PtrOp} (LocInfoE loc_115 ("ptr"))))) ;
        locinfo: loc_78 ;
        expr: (LocInfoE loc_78 (Call (LocInfoE loc_109 (global_sl_lock)) [@{expr} LocInfoE loc_110 (&(LocInfoE loc_111 ((LocInfoE loc_112 (!{PtrOp} (LocInfoE loc_113 ("p")))) at{struct_mpool} "lock"))) ])) ;
        locinfo: loc_79 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_104 (&(LocInfoE loc_105 ((LocInfoE loc_106 (!{PtrOp} (LocInfoE loc_107 ("p")))) at{struct_mpool} "locked")))) ;
        locinfo: loc_81 ;
        LocInfoE loc_96 ((LocInfoE loc_97 (!{PtrOp} (LocInfoE loc_98 ("e")))) at{struct_mpool_entry} "next") <-{ PtrOp }
          LocInfoE loc_99 (use{PtrOp} (LocInfoE loc_100 ((LocInfoE loc_101 ((LocInfoE loc_102 (!{PtrOp} (LocInfoE loc_103 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list"))) ;
        locinfo: loc_82 ;
        LocInfoE loc_90 ((LocInfoE loc_91 ((LocInfoE loc_92 (!{PtrOp} (LocInfoE loc_93 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list") <-{ PtrOp }
          LocInfoE loc_94 (use{PtrOp} (LocInfoE loc_95 ("e"))) ;
        locinfo: loc_83 ;
        expr: (LocInfoE loc_83 (Call (LocInfoE loc_85 (global_sl_unlock)) [@{expr} LocInfoE loc_86 (AnnotExpr 1%nat LockA (LocInfoE loc_86 (&(LocInfoE loc_87 ((LocInfoE loc_88 (!{PtrOp} (LocInfoE loc_89 ("p")))) at{struct_mpool} "lock"))))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [mpool_init]. *)
  Definition impl_mpool_init (global_sl_init : loc): function := {|
    f_args := [
      ("p", void*);
      ("entry_size", it_layout size_t)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_120 ;
        LocInfoE loc_145 ((LocInfoE loc_146 (!{PtrOp} (LocInfoE loc_147 ("p")))) at{struct_mpool} "entry_size") <-{ IntOp size_t }
          LocInfoE loc_148 (use{IntOp size_t} (LocInfoE loc_149 ("entry_size"))) ;
        locinfo: loc_121 ;
        LocInfoE loc_140 ((LocInfoE loc_141 ((LocInfoE loc_142 (!{PtrOp} (LocInfoE loc_143 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list") <-{ PtrOp }
          LocInfoE loc_144 (NULL) ;
        locinfo: loc_122 ;
        LocInfoE loc_135 ((LocInfoE loc_136 ((LocInfoE loc_137 (!{PtrOp} (LocInfoE loc_138 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list") <-{ PtrOp }
          LocInfoE loc_139 (NULL) ;
        locinfo: loc_123 ;
        LocInfoE loc_131 ((LocInfoE loc_132 (!{PtrOp} (LocInfoE loc_133 ("p")))) at{struct_mpool} "fallback") <-{ PtrOp }
          LocInfoE loc_134 (NULL) ;
        locinfo: loc_124 ;
        expr: (LocInfoE loc_124 (Call (LocInfoE loc_126 (global_sl_init)) [@{expr} LocInfoE loc_127 (&(LocInfoE loc_128 ((LocInfoE loc_129 (!{PtrOp} (LocInfoE loc_130 ("p")))) at{struct_mpool} "lock"))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [mpool_init_from]. *)
  Definition impl_mpool_init_from (global_mpool_init global_sl_lock global_sl_unlock : loc): function := {|
    f_args := [
      ("p", void*);
      ("from", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_152 ;
        expr: (LocInfoE loc_152 (Call (LocInfoE loc_214 (global_mpool_init)) [@{expr} LocInfoE loc_215 (use{PtrOp} (LocInfoE loc_216 ("p"))) ;
        LocInfoE loc_217 (use{IntOp size_t} (LocInfoE loc_218 ((LocInfoE loc_219 (!{PtrOp} (LocInfoE loc_220 ("from")))) at{struct_mpool} "entry_size"))) ])) ;
        locinfo: loc_153 ;
        expr: (LocInfoE loc_153 (Call (LocInfoE loc_208 (global_sl_lock)) [@{expr} LocInfoE loc_209 (&(LocInfoE loc_210 ((LocInfoE loc_211 (!{PtrOp} (LocInfoE loc_212 ("from")))) at{struct_mpool} "lock"))) ])) ;
        locinfo: loc_154 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_203 (&(LocInfoE loc_204 ((LocInfoE loc_205 (!{PtrOp} (LocInfoE loc_206 ("from")))) at{struct_mpool} "locked")))) ;
        locinfo: loc_156 ;
        LocInfoE loc_194 ((LocInfoE loc_195 ((LocInfoE loc_196 (!{PtrOp} (LocInfoE loc_197 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list") <-{ PtrOp }
          LocInfoE loc_198 (use{PtrOp} (LocInfoE loc_199 ((LocInfoE loc_200 ((LocInfoE loc_201 (!{PtrOp} (LocInfoE loc_202 ("from")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list"))) ;
        locinfo: loc_157 ;
        LocInfoE loc_185 ((LocInfoE loc_186 ((LocInfoE loc_187 (!{PtrOp} (LocInfoE loc_188 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list") <-{ PtrOp }
          LocInfoE loc_189 (use{PtrOp} (LocInfoE loc_190 ((LocInfoE loc_191 ((LocInfoE loc_192 (!{PtrOp} (LocInfoE loc_193 ("from")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list"))) ;
        locinfo: loc_158 ;
        LocInfoE loc_178 ((LocInfoE loc_179 (!{PtrOp} (LocInfoE loc_180 ("p")))) at{struct_mpool} "fallback") <-{ PtrOp }
          LocInfoE loc_181 (use{PtrOp} (LocInfoE loc_182 ((LocInfoE loc_183 (!{PtrOp} (LocInfoE loc_184 ("from")))) at{struct_mpool} "fallback"))) ;
        locinfo: loc_159 ;
        LocInfoE loc_173 ((LocInfoE loc_174 ((LocInfoE loc_175 (!{PtrOp} (LocInfoE loc_176 ("from")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list") <-{ PtrOp }
          LocInfoE loc_177 (NULL) ;
        locinfo: loc_160 ;
        LocInfoE loc_168 ((LocInfoE loc_169 ((LocInfoE loc_170 (!{PtrOp} (LocInfoE loc_171 ("from")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list") <-{ PtrOp }
          LocInfoE loc_172 (NULL) ;
        locinfo: loc_161 ;
        expr: (LocInfoE loc_161 (Call (LocInfoE loc_163 (global_sl_unlock)) [@{expr} LocInfoE loc_164 (AnnotExpr 1%nat LockA (LocInfoE loc_164 (&(LocInfoE loc_165 ((LocInfoE loc_166 (!{PtrOp} (LocInfoE loc_167 ("from")))) at{struct_mpool} "lock"))))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [mpool_init_with_fallback]. *)
  Definition impl_mpool_init_with_fallback (global_mpool_init : loc): function := {|
    f_args := [
      ("p", void*);
      ("fallback", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_223 ;
        expr: (LocInfoE loc_223 (Call (LocInfoE loc_231 (global_mpool_init)) [@{expr} LocInfoE loc_232 (use{PtrOp} (LocInfoE loc_233 ("p"))) ;
        LocInfoE loc_234 (use{IntOp size_t} (LocInfoE loc_235 ((LocInfoE loc_236 (!{PtrOp} (LocInfoE loc_237 ("fallback")))) at{struct_mpool} "entry_size"))) ])) ;
        locinfo: loc_224 ;
        LocInfoE loc_225 ((LocInfoE loc_226 (!{PtrOp} (LocInfoE loc_227 ("p")))) at{struct_mpool} "fallback") <-{ PtrOp }
          LocInfoE loc_228 (use{PtrOp} (LocInfoE loc_229 ("fallback"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [mpool_fini]. *)
  Definition impl_mpool_fini (global_mpool_add_chunk global_mpool_free : loc): function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("size", it_layout size_t);
      ("ptr1", void*);
      ("ptr2", void*);
      ("entry", void*);
      ("chunk", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_343 ;
        if: LocInfoE loc_343 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_343 ((LocInfoE loc_344 (use{PtrOp} (LocInfoE loc_345 ((LocInfoE loc_346 (!{PtrOp} (LocInfoE loc_347 ("p")))) at{struct_mpool} "fallback")))) ={PtrOp, PtrOp} (LocInfoE loc_348 (NULL)))))
        then
        locinfo: loc_340 ;
          Goto "#8"
        else
        locinfo: loc_241 ;
          Goto "#9"
      ]> $
      <[ "#1" :=
        locinfo: loc_241 ;
        LocInfoE loc_333 ("entry") <-{ PtrOp }
          LocInfoE loc_334 (use{PtrOp} (LocInfoE loc_335 ((LocInfoE loc_336 ((LocInfoE loc_337 (!{PtrOp} (LocInfoE loc_338 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list"))) ;
        locinfo: loc_242 ;
        LocInfoE loc_327 ("chunk") <-{ PtrOp }
          LocInfoE loc_328 (use{PtrOp} (LocInfoE loc_329 ((LocInfoE loc_330 ((LocInfoE loc_331 (!{PtrOp} (LocInfoE loc_332 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list"))) ;
        locinfo: loc_243 ;
        Goto "#2"
      ]> $
      <[ "#2" :=
        locinfo: loc_323 ;
        if: LocInfoE loc_323 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_323 ((LocInfoE loc_324 (use{PtrOp} (LocInfoE loc_325 ("entry")))) !={PtrOp, PtrOp} (LocInfoE loc_326 (NULL)))))
        then
        Goto "#3"
        else
        locinfo: loc_244 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        "ptr1" <-{ PtrOp }
          LocInfoE loc_319 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_319 (use{PtrOp} (LocInfoE loc_320 ("entry"))))) ;
        locinfo: loc_302 ;
        LocInfoE loc_314 ("entry") <-{ PtrOp }
          LocInfoE loc_315 (use{PtrOp} (LocInfoE loc_316 ((LocInfoE loc_317 (!{PtrOp} (LocInfoE loc_318 ("entry")))) at{struct_mpool_entry} "next"))) ;
        locinfo: loc_303 ;
        expr: (LocInfoE loc_303 (Call (LocInfoE loc_307 (global_mpool_free)) [@{expr} LocInfoE loc_308 (use{PtrOp} (LocInfoE loc_309 ((LocInfoE loc_310 (!{PtrOp} (LocInfoE loc_311 ("p")))) at{struct_mpool} "fallback"))) ;
        LocInfoE loc_312 (use{PtrOp} (LocInfoE loc_313 ("ptr1"))) ])) ;
        locinfo: loc_304 ;
        Goto "continue11"
      ]> $
      <[ "#4" :=
        locinfo: loc_244 ;
        Goto "#5"
      ]> $
      <[ "#5" :=
        locinfo: loc_295 ;
        if: LocInfoE loc_295 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_295 ((LocInfoE loc_296 (use{PtrOp} (LocInfoE loc_297 ("chunk")))) !={PtrOp, PtrOp} (LocInfoE loc_298 (NULL)))))
        then
        Goto "#6"
        else
        locinfo: loc_245 ;
          Goto "#7"
      ]> $
      <[ "#6" :=
        "ptr2" <-{ PtrOp }
          LocInfoE loc_291 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_291 (use{PtrOp} (LocInfoE loc_292 ("chunk"))))) ;
        "size" <-{ IntOp size_t }
          LocInfoE loc_285 (use{IntOp size_t} (LocInfoE loc_286 ((LocInfoE loc_287 (!{PtrOp} (LocInfoE loc_288 ("chunk")))) at{struct_mpool_chunk} "size"))) ;
        locinfo: loc_266 ;
        LocInfoE loc_280 ("chunk") <-{ PtrOp }
          LocInfoE loc_281 (use{PtrOp} (LocInfoE loc_282 ((LocInfoE loc_283 (!{PtrOp} (LocInfoE loc_284 ("chunk")))) at{struct_mpool_chunk} "next_chunk"))) ;
        locinfo: loc_267 ;
        expr: (LocInfoE loc_267 (Call (LocInfoE loc_271 (global_mpool_add_chunk)) [@{expr} LocInfoE loc_272 (use{PtrOp} (LocInfoE loc_273 ((LocInfoE loc_274 (!{PtrOp} (LocInfoE loc_275 ("p")))) at{struct_mpool} "fallback"))) ;
        LocInfoE loc_276 (use{PtrOp} (LocInfoE loc_277 ("ptr2"))) ;
        LocInfoE loc_278 (use{IntOp size_t} (LocInfoE loc_279 ("size"))) ])) ;
        locinfo: loc_268 ;
        Goto "continue13"
      ]> $
      <[ "#7" :=
        locinfo: loc_245 ;
        LocInfoE loc_257 ((LocInfoE loc_258 ((LocInfoE loc_259 (!{PtrOp} (LocInfoE loc_260 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list") <-{ PtrOp }
          LocInfoE loc_261 (NULL) ;
        locinfo: loc_246 ;
        LocInfoE loc_252 ((LocInfoE loc_253 ((LocInfoE loc_254 (!{PtrOp} (LocInfoE loc_255 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list") <-{ PtrOp }
          LocInfoE loc_256 (NULL) ;
        locinfo: loc_247 ;
        LocInfoE loc_248 ((LocInfoE loc_249 (!{PtrOp} (LocInfoE loc_250 ("p")))) at{struct_mpool} "fallback") <-{ PtrOp }
          LocInfoE loc_251 (NULL) ;
        Return (VOID)
      ]> $
      <[ "#8" :=
        locinfo: loc_340 ;
        Return (VOID)
      ]> $
      <[ "#9" :=
        locinfo: loc_241 ;
        Goto "#1"
      ]> $
      <[ "continue11" :=
        locinfo: loc_243 ;
        Goto "#2"
      ]> $
      <[ "continue13" :=
        locinfo: loc_244 ;
        Goto "#5"
      ]> $∅
    )%E
  |}.

  (* Definition of function [mpool_alloc_no_fallback]. *)
  Definition impl_mpool_alloc_no_fallback (global_sl_lock global_sl_unlock : loc): function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("new_chunk", void*);
      ("entry", void*);
      ("ret", void*);
      ("chunk", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_351 ;
        expr: (LocInfoE loc_351 (Call (LocInfoE loc_484 (global_sl_lock)) [@{expr} LocInfoE loc_485 (&(LocInfoE loc_486 ((LocInfoE loc_487 (!{PtrOp} (LocInfoE loc_488 ("p")))) at{struct_mpool} "lock"))) ])) ;
        locinfo: loc_352 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_479 (&(LocInfoE loc_480 ((LocInfoE loc_481 (!{PtrOp} (LocInfoE loc_482 ("p")))) at{struct_mpool} "locked")))) ;
        locinfo: loc_472 ;
        if: LocInfoE loc_472 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_472 ((LocInfoE loc_473 (use{PtrOp} (LocInfoE loc_474 ((LocInfoE loc_475 ((LocInfoE loc_476 (!{PtrOp} (LocInfoE loc_477 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list")))) !={PtrOp, PtrOp} (LocInfoE loc_478 (NULL)))))
        then
        Goto "#8"
        else
        locinfo: loc_355 ;
          Goto "#9"
      ]> $
      <[ "#1" :=
        locinfo: loc_355 ;
        LocInfoE loc_442 ("chunk") <-{ PtrOp }
          LocInfoE loc_443 (use{PtrOp} (LocInfoE loc_444 ((LocInfoE loc_445 ((LocInfoE loc_446 (!{PtrOp} (LocInfoE loc_447 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list"))) ;
        locinfo: loc_438 ;
        if: LocInfoE loc_438 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_438 ((LocInfoE loc_439 (use{PtrOp} (LocInfoE loc_440 ("chunk")))) ={PtrOp, PtrOp} (LocInfoE loc_441 (NULL)))))
        then
        locinfo: loc_433 ;
          Goto "#6"
        else
        locinfo: loc_423 ;
          Goto "#7"
      ]> $
      <[ "#2" :=
        locinfo: loc_423 ;
        if: LocInfoE loc_423 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_423 ((LocInfoE loc_424 (use{IntOp size_t} (LocInfoE loc_425 ((LocInfoE loc_426 (!{PtrOp} (LocInfoE loc_427 ("p")))) at{struct_mpool} "entry_size")))) ≥{IntOp size_t, IntOp size_t} (LocInfoE loc_428 (use{IntOp size_t} (LocInfoE loc_429 ((LocInfoE loc_430 (!{PtrOp} (LocInfoE loc_431 ("chunk")))) at{struct_mpool_chunk} "size")))))))
        then
        locinfo: loc_374 ;
          Goto "#4"
        else
        locinfo: loc_384 ;
          Goto "#5"
      ]> $
      <[ "#3" :=
        locinfo: loc_358 ;
        LocInfoE loc_370 ("ret") <-{ PtrOp }
          LocInfoE loc_371 (use{PtrOp} (LocInfoE loc_372 ("chunk"))) ;
        locinfo: loc_359 ;
        Goto "exit"
      ]> $
      <[ "#4" :=
        locinfo: loc_374 ;
        LocInfoE loc_375 ((LocInfoE loc_376 ((LocInfoE loc_377 (!{PtrOp} (LocInfoE loc_378 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list") <-{ PtrOp }
          LocInfoE loc_379 (use{PtrOp} (LocInfoE loc_380 ((LocInfoE loc_381 (!{PtrOp} (LocInfoE loc_382 ("chunk")))) at{struct_mpool_chunk} "next_chunk"))) ;
        locinfo: loc_358 ;
        Goto "#3"
      ]> $
      <[ "#5" :=
        locinfo: loc_384 ;
        LocInfoE loc_413 ("new_chunk") <-{ PtrOp }
          LocInfoE loc_414 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_415 ((LocInfoE loc_416 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_417 (use{PtrOp} (LocInfoE loc_418 ("chunk")))))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_419 (use{IntOp size_t} (LocInfoE loc_420 ((LocInfoE loc_421 (!{PtrOp} (LocInfoE loc_422 ("p")))) at{struct_mpool} "entry_size"))))))) ;
        locinfo: loc_385 ;
        LocInfoE loc_406 ((LocInfoE loc_407 (!{PtrOp} (LocInfoE loc_408 ("new_chunk")))) at{struct_mpool_chunk} "next_chunk") <-{ PtrOp }
          LocInfoE loc_409 (use{PtrOp} (LocInfoE loc_410 ((LocInfoE loc_411 (!{PtrOp} (LocInfoE loc_412 ("chunk")))) at{struct_mpool_chunk} "next_chunk"))) ;
        locinfo: loc_386 ;
        LocInfoE loc_394 ((LocInfoE loc_395 (!{PtrOp} (LocInfoE loc_396 ("new_chunk")))) at{struct_mpool_chunk} "size") <-{ IntOp size_t }
          LocInfoE loc_397 ((LocInfoE loc_398 (use{IntOp size_t} (LocInfoE loc_399 ((LocInfoE loc_400 (!{PtrOp} (LocInfoE loc_401 ("chunk")))) at{struct_mpool_chunk} "size")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_402 (use{IntOp size_t} (LocInfoE loc_403 ((LocInfoE loc_404 (!{PtrOp} (LocInfoE loc_405 ("p")))) at{struct_mpool} "entry_size"))))) ;
        locinfo: loc_387 ;
        LocInfoE loc_388 ((LocInfoE loc_389 ((LocInfoE loc_390 (!{PtrOp} (LocInfoE loc_391 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list") <-{ PtrOp }
          LocInfoE loc_392 (use{PtrOp} (LocInfoE loc_393 ("new_chunk"))) ;
        locinfo: loc_358 ;
        Goto "#3"
      ]> $
      <[ "#6" :=
        locinfo: loc_433 ;
        LocInfoE loc_435 ("ret") <-{ PtrOp } LocInfoE loc_436 (NULL) ;
        locinfo: loc_434 ;
        Goto "exit"
      ]> $
      <[ "#7" :=
        locinfo: loc_423 ;
        Goto "#2"
      ]> $
      <[ "#8" :=
        "entry" <-{ PtrOp }
          LocInfoE loc_464 (use{PtrOp} (LocInfoE loc_465 ((LocInfoE loc_466 ((LocInfoE loc_467 (!{PtrOp} (LocInfoE loc_468 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list"))) ;
        locinfo: loc_450 ;
        LocInfoE loc_456 ((LocInfoE loc_457 ((LocInfoE loc_458 (!{PtrOp} (LocInfoE loc_459 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list") <-{ PtrOp }
          LocInfoE loc_460 (use{PtrOp} (LocInfoE loc_461 ((LocInfoE loc_462 (!{PtrOp} (LocInfoE loc_463 ("entry")))) at{struct_mpool_entry} "next"))) ;
        locinfo: loc_451 ;
        LocInfoE loc_453 ("ret") <-{ PtrOp }
          LocInfoE loc_454 (use{PtrOp} (LocInfoE loc_455 ("entry"))) ;
        locinfo: loc_452 ;
        Goto "exit"
      ]> $
      <[ "#9" :=
        locinfo: loc_355 ;
        Goto "#1"
      ]> $
      <[ "exit" :=
        locinfo: loc_360 ;
        expr: (LocInfoE loc_360 (Call (LocInfoE loc_365 (global_sl_unlock)) [@{expr} LocInfoE loc_366 (AnnotExpr 1%nat LockA (LocInfoE loc_366 (&(LocInfoE loc_367 ((LocInfoE loc_368 (!{PtrOp} (LocInfoE loc_369 ("p")))) at{struct_mpool} "lock"))))) ])) ;
        locinfo: loc_361 ;
        Return (LocInfoE loc_362 (use{PtrOp} (LocInfoE loc_363 ("ret"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [mpool_alloc]. *)
  Definition impl_mpool_alloc (global_mpool_alloc_no_fallback : loc): function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("ret", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "ret" <-{ PtrOp }
          LocInfoE loc_542 (Call (LocInfoE loc_544 (global_mpool_alloc_no_fallback)) [@{expr} LocInfoE loc_545 (use{PtrOp} (LocInfoE loc_546 ("p"))) ]) ;
        locinfo: loc_538 ;
        if: LocInfoE loc_538 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_538 ((LocInfoE loc_539 (use{PtrOp} (LocInfoE loc_540 ("ret")))) !={PtrOp, PtrOp} (LocInfoE loc_541 (NULL)))))
        then
        locinfo: loc_534 ;
          Goto "#8"
        else
        locinfo: loc_493 ;
          Goto "#9"
      ]> $
      <[ "#1" :=
        locinfo: loc_493 ;
        LocInfoE loc_528 ("p") <-{ PtrOp }
          LocInfoE loc_529 (use{PtrOp} (LocInfoE loc_530 ((LocInfoE loc_531 (!{PtrOp} (LocInfoE loc_532 ("p")))) at{struct_mpool} "fallback"))) ;
        locinfo: loc_494 ;
        Goto "#2"
      ]> $
      <[ "#2" :=
        locinfo: loc_524 ;
        if: LocInfoE loc_524 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_524 ((LocInfoE loc_525 (use{PtrOp} (LocInfoE loc_526 ("p")))) !={PtrOp, PtrOp} (LocInfoE loc_527 (NULL)))))
        then
        locinfo: loc_499 ;
          Goto "#3"
        else
        locinfo: loc_495 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_499 ;
        LocInfoE loc_518 ("ret") <-{ PtrOp }
          LocInfoE loc_519 (Call (LocInfoE loc_521 (global_mpool_alloc_no_fallback)) [@{expr} LocInfoE loc_522 (use{PtrOp} (LocInfoE loc_523 ("p"))) ]) ;
        locinfo: loc_514 ;
        if: LocInfoE loc_514 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_514 ((LocInfoE loc_515 (use{PtrOp} (LocInfoE loc_516 ("ret")))) !={PtrOp, PtrOp} (LocInfoE loc_517 (NULL)))))
        then
        locinfo: loc_510 ;
          Goto "#6"
        else
        locinfo: loc_501 ;
          Goto "#7"
      ]> $
      <[ "#4" :=
        locinfo: loc_495 ;
        Return (LocInfoE loc_496 (NULL))
      ]> $
      <[ "#5" :=
        locinfo: loc_501 ;
        LocInfoE loc_504 ("p") <-{ PtrOp }
          LocInfoE loc_505 (use{PtrOp} (LocInfoE loc_506 ((LocInfoE loc_507 (!{PtrOp} (LocInfoE loc_508 ("p")))) at{struct_mpool} "fallback"))) ;
        locinfo: loc_502 ;
        Goto "continue27"
      ]> $
      <[ "#6" :=
        locinfo: loc_510 ;
        Return (LocInfoE loc_511 (use{PtrOp} (LocInfoE loc_512 ("ret"))))
      ]> $
      <[ "#7" :=
        locinfo: loc_501 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        locinfo: loc_534 ;
        Return (LocInfoE loc_535 (use{PtrOp} (LocInfoE loc_536 ("ret"))))
      ]> $
      <[ "#9" :=
        locinfo: loc_493 ;
        Goto "#1"
      ]> $
      <[ "continue27" :=
        locinfo: loc_494 ;
        Goto "#2"
      ]> $∅
    )%E
  |}.

  (* Definition of function [mpool_alloc_contiguous_no_fallback]. *)
  Definition impl_mpool_alloc_contiguous_no_fallback (global_round_pointer_up global_sl_lock global_sl_unlock : loc): function := {|
    f_args := [
      ("p", void*);
      ("count", it_layout size_t);
      ("align", it_layout size_t)
    ];
    f_local_vars := [
      ("prev", void*);
      ("before_start", it_layout size_t);
      ("chunk_next", void*);
      ("new_chunk", void*);
      ("start", void*);
      ("ret", void*);
      ("chunk_size", it_layout size_t);
      ("chunk", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "ret" <-{ PtrOp } LocInfoE loc_777 (NULL) ;
        locinfo: loc_552 ;
        LocInfoE loc_769 ("align") <-{ IntOp size_t }
          LocInfoE loc_770 ((LocInfoE loc_771 (use{IntOp size_t} (LocInfoE loc_772 ("align")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_773 (use{IntOp size_t} (LocInfoE loc_774 ((LocInfoE loc_775 (!{PtrOp} (LocInfoE loc_776 ("p")))) at{struct_mpool} "entry_size"))))) ;
        locinfo: loc_553 ;
        expr: (LocInfoE loc_553 (Call (LocInfoE loc_764 (global_sl_lock)) [@{expr} LocInfoE loc_765 (&(LocInfoE loc_766 ((LocInfoE loc_767 (!{PtrOp} (LocInfoE loc_768 ("p")))) at{struct_mpool} "lock"))) ])) ;
        locinfo: loc_554 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_759 (&(LocInfoE loc_760 ((LocInfoE loc_761 (!{PtrOp} (LocInfoE loc_762 ("p")))) at{struct_mpool} "locked")))) ;
        locinfo: loc_556 ;
        LocInfoE loc_753 ("prev") <-{ PtrOp }
          LocInfoE loc_754 (&(LocInfoE loc_755 ((LocInfoE loc_756 ((LocInfoE loc_757 (!{PtrOp} (LocInfoE loc_758 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list"))) ;
        locinfo: loc_557 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_747 ;
        if: LocInfoE loc_747 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_747 ((LocInfoE loc_748 (use{PtrOp} (LocInfoE loc_750 (!{PtrOp} (LocInfoE loc_751 ("prev")))))) !={PtrOp, PtrOp} (LocInfoE loc_752 (NULL)))))
        then
        Goto "#2"
        else
        locinfo: loc_558 ;
          Goto "#3"
      ]> $
      <[ "#10" :=
        locinfo: loc_627 ;
        LocInfoE loc_629 (!{PtrOp} (LocInfoE loc_630 ("prev"))) <-{ PtrOp }
          LocInfoE loc_631 (use{PtrOp} (LocInfoE loc_632 ("chunk_next"))) ;
        locinfo: loc_619 ;
        Goto "#6"
      ]> $
      <[ "#11" :=
        locinfo: loc_634 ;
        LocInfoE loc_664 ("new_chunk") <-{ PtrOp }
          LocInfoE loc_665 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_666 ((LocInfoE loc_667 (use{PtrOp} (LocInfoE loc_668 ("start")))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_669 ((LocInfoE loc_670 (use{IntOp size_t} (LocInfoE loc_671 ("count")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_672 (use{IntOp size_t} (LocInfoE loc_673 ((LocInfoE loc_674 (!{PtrOp} (LocInfoE loc_675 ("p")))) at{struct_mpool} "entry_size"))))))))) ;
        locinfo: loc_635 ;
        LocInfoE loc_648 ((LocInfoE loc_649 (!{PtrOp} (LocInfoE loc_650 ("new_chunk")))) at{struct_mpool_chunk} "size") <-{ IntOp size_t }
          LocInfoE loc_651 ((LocInfoE loc_652 (use{IntOp size_t} (LocInfoE loc_653 ("chunk_size")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_654 ((LocInfoE loc_655 (use{IntOp size_t} (LocInfoE loc_656 ("before_start")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_657 ((LocInfoE loc_658 (use{IntOp size_t} (LocInfoE loc_659 ("count")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_660 (use{IntOp size_t} (LocInfoE loc_661 ((LocInfoE loc_662 (!{PtrOp} (LocInfoE loc_663 ("p")))) at{struct_mpool} "entry_size"))))))))) ;
        locinfo: loc_636 ;
        LocInfoE loc_643 ((LocInfoE loc_644 (!{PtrOp} (LocInfoE loc_645 ("new_chunk")))) at{struct_mpool_chunk} "next_chunk") <-{ PtrOp }
          LocInfoE loc_646 (use{PtrOp} (LocInfoE loc_647 ("chunk_next"))) ;
        locinfo: loc_637 ;
        LocInfoE loc_639 (!{PtrOp} (LocInfoE loc_640 ("prev"))) <-{ PtrOp }
          LocInfoE loc_641 (use{PtrOp} (LocInfoE loc_642 ("new_chunk"))) ;
        locinfo: loc_619 ;
        Goto "#6"
      ]> $
      <[ "#12" :=
        locinfo: loc_575 ;
        Goto "#4"
      ]> $
      <[ "#2" :=
        "chunk" <-{ PtrOp }
          LocInfoE loc_741 (use{PtrOp} (LocInfoE loc_743 (!{PtrOp} (LocInfoE loc_744 ("prev"))))) ;
        locinfo: loc_571 ;
        annot: (LearnAlignmentAnnot) ;
        expr: (LocInfoE loc_737 (&(LocInfoE loc_739 (!{PtrOp} (LocInfoE loc_740 ("chunk")))))) ;
        locinfo: loc_573 ;
        expr: (LocInfoE loc_573 (Call (LocInfoE loc_729 (global_round_pointer_up)) [@{expr} LocInfoE loc_730 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_731 (use{PtrOp} (LocInfoE loc_732 ("chunk"))))) ;
        LocInfoE loc_733 (use{IntOp size_t} (LocInfoE loc_734 ("align"))) ;
        LocInfoE loc_735 (&(LocInfoE loc_736 ("before_start"))) ])) ;
        locinfo: loc_713 ;
        if: LocInfoE loc_713 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_713 ((LocInfoE loc_714 ((LocInfoE loc_715 (use{IntOp size_t} (LocInfoE loc_716 ("before_start")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_717 ((LocInfoE loc_718 (use{IntOp size_t} (LocInfoE loc_719 ("count")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_720 (use{IntOp size_t} (LocInfoE loc_721 ((LocInfoE loc_722 (!{PtrOp} (LocInfoE loc_723 ("p")))) at{struct_mpool} "entry_size")))))))) ≤{IntOp size_t, IntOp size_t} (LocInfoE loc_724 (use{IntOp size_t} (LocInfoE loc_725 ((LocInfoE loc_726 (!{PtrOp} (LocInfoE loc_727 ("chunk")))) at{struct_mpool_chunk} "size")))))))
        then
        Goto "#5"
        else
        locinfo: loc_575 ;
          Goto "#12"
      ]> $
      <[ "#3" :=
        locinfo: loc_558 ;
        expr: (LocInfoE loc_558 (Call (LocInfoE loc_563 (global_sl_unlock)) [@{expr} LocInfoE loc_564 (AnnotExpr 1%nat LockA (LocInfoE loc_564 (&(LocInfoE loc_565 ((LocInfoE loc_566 (!{PtrOp} (LocInfoE loc_567 ("p")))) at{struct_mpool} "lock"))))) ])) ;
        locinfo: loc_559 ;
        Return (LocInfoE loc_560 (use{PtrOp} (LocInfoE loc_561 ("ret"))))
      ]> $
      <[ "#4" :=
        locinfo: loc_575 ;
        LocInfoE loc_578 ("prev") <-{ PtrOp }
          LocInfoE loc_579 (&(LocInfoE loc_580 ((LocInfoE loc_581 (!{PtrOp} (LocInfoE loc_582 ("chunk")))) at{struct_mpool_chunk} "next_chunk"))) ;
        locinfo: loc_576 ;
        Goto "continue34"
      ]> $
      <[ "#5" :=
        "chunk_size" <-{ IntOp size_t }
          LocInfoE loc_706 (use{IntOp size_t} (LocInfoE loc_707 ((LocInfoE loc_708 (!{PtrOp} (LocInfoE loc_709 ("chunk")))) at{struct_mpool_chunk} "size"))) ;
        "chunk_next" <-{ PtrOp }
          LocInfoE loc_700 (use{PtrOp} (LocInfoE loc_701 ((LocInfoE loc_702 (!{PtrOp} (LocInfoE loc_703 ("chunk")))) at{struct_mpool_chunk} "next_chunk"))) ;
        locinfo: loc_586 ;
        annot: (ToUninit) ;
        expr: (LocInfoE loc_696 (&(LocInfoE loc_698 (!{PtrOp} (LocInfoE loc_699 ("chunk")))))) ;
        locinfo: loc_588 ;
        LocInfoE loc_689 ("start") <-{ PtrOp }
          LocInfoE loc_690 ((LocInfoE loc_691 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_692 (use{PtrOp} (LocInfoE loc_693 ("chunk")))))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_694 (use{IntOp size_t} (LocInfoE loc_695 ("before_start"))))) ;
        locinfo: loc_676 ;
        if: LocInfoE loc_676 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_676 ((LocInfoE loc_677 ((LocInfoE loc_678 (use{IntOp size_t} (LocInfoE loc_679 ("before_start")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_680 ((LocInfoE loc_681 (use{IntOp size_t} (LocInfoE loc_682 ("count")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_683 (use{IntOp size_t} (LocInfoE loc_684 ((LocInfoE loc_685 (!{PtrOp} (LocInfoE loc_686 ("p")))) at{struct_mpool} "entry_size")))))))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_687 (use{IntOp size_t} (LocInfoE loc_688 ("chunk_size")))))))
        then
        locinfo: loc_627 ;
          Goto "#10"
        else
        locinfo: loc_634 ;
          Goto "#11"
      ]> $
      <[ "#6" :=
        locinfo: loc_619 ;
        if: LocInfoE loc_619 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_619 ((LocInfoE loc_620 (use{IntOp size_t} (LocInfoE loc_621 ("before_start")))) ≥{IntOp size_t, IntOp size_t} (LocInfoE loc_622 (use{IntOp size_t} (LocInfoE loc_623 ((LocInfoE loc_624 (!{PtrOp} (LocInfoE loc_625 ("p")))) at{struct_mpool} "entry_size")))))))
        then
        locinfo: loc_598 ;
          Goto "#8"
        else
        locinfo: loc_591 ;
          Goto "#9"
      ]> $
      <[ "#7" :=
        locinfo: loc_591 ;
        LocInfoE loc_593 ("ret") <-{ PtrOp }
          LocInfoE loc_594 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_595 (use{PtrOp} (LocInfoE loc_596 ("start"))))) ;
        locinfo: loc_558 ;
        Goto "#3"
      ]> $
      <[ "#8" :=
        locinfo: loc_598 ;
        LocInfoE loc_611 ((LocInfoE loc_612 (!{PtrOp} (LocInfoE loc_613 ("chunk")))) at{struct_mpool_chunk} "next_chunk") <-{ PtrOp }
          LocInfoE loc_614 (use{PtrOp} (LocInfoE loc_616 (!{PtrOp} (LocInfoE loc_617 ("prev"))))) ;
        locinfo: loc_599 ;
        LocInfoE loc_607 (!{PtrOp} (LocInfoE loc_608 ("prev"))) <-{ PtrOp }
          LocInfoE loc_609 (use{PtrOp} (LocInfoE loc_610 ("chunk"))) ;
        locinfo: loc_600 ;
        LocInfoE loc_601 ((LocInfoE loc_602 (!{PtrOp} (LocInfoE loc_603 ("chunk")))) at{struct_mpool_chunk} "size") <-{ IntOp size_t }
          LocInfoE loc_604 (use{IntOp size_t} (LocInfoE loc_605 ("before_start"))) ;
        locinfo: loc_591 ;
        Goto "#7"
      ]> $
      <[ "#9" :=
        locinfo: loc_591 ;
        Goto "#7"
      ]> $
      <[ "continue34" :=
        locinfo: loc_557 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [mpool_alloc_contiguous]. *)
  Definition impl_mpool_alloc_contiguous (global_mpool_alloc_contiguous_no_fallback : loc): function := {|
    f_args := [
      ("p", void*);
      ("count", it_layout size_t);
      ("align", it_layout size_t)
    ];
    f_local_vars := [
      ("ret", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "ret" <-{ PtrOp }
          LocInfoE loc_837 (Call (LocInfoE loc_839 (global_mpool_alloc_contiguous_no_fallback)) [@{expr} LocInfoE loc_840 (use{PtrOp} (LocInfoE loc_841 ("p"))) ;
          LocInfoE loc_842 (use{IntOp size_t} (LocInfoE loc_843 ("count"))) ;
          LocInfoE loc_844 (use{IntOp size_t} (LocInfoE loc_845 ("align"))) ]) ;
        locinfo: loc_833 ;
        if: LocInfoE loc_833 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_833 ((LocInfoE loc_834 (use{PtrOp} (LocInfoE loc_835 ("ret")))) !={PtrOp, PtrOp} (LocInfoE loc_836 (NULL)))))
        then
        locinfo: loc_829 ;
          Goto "#8"
        else
        locinfo: loc_784 ;
          Goto "#9"
      ]> $
      <[ "#1" :=
        locinfo: loc_784 ;
        LocInfoE loc_823 ("p") <-{ PtrOp }
          LocInfoE loc_824 (use{PtrOp} (LocInfoE loc_825 ((LocInfoE loc_826 (!{PtrOp} (LocInfoE loc_827 ("p")))) at{struct_mpool} "fallback"))) ;
        locinfo: loc_785 ;
        Goto "#2"
      ]> $
      <[ "#2" :=
        locinfo: loc_819 ;
        if: LocInfoE loc_819 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_819 ((LocInfoE loc_820 (use{PtrOp} (LocInfoE loc_821 ("p")))) !={PtrOp, PtrOp} (LocInfoE loc_822 (NULL)))))
        then
        locinfo: loc_790 ;
          Goto "#3"
        else
        locinfo: loc_786 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_790 ;
        LocInfoE loc_809 ("ret") <-{ PtrOp }
          LocInfoE loc_810 (Call (LocInfoE loc_812 (global_mpool_alloc_contiguous_no_fallback)) [@{expr} LocInfoE loc_813 (use{PtrOp} (LocInfoE loc_814 ("p"))) ;
          LocInfoE loc_815 (use{IntOp size_t} (LocInfoE loc_816 ("count"))) ;
          LocInfoE loc_817 (use{IntOp size_t} (LocInfoE loc_818 ("align"))) ]) ;
        locinfo: loc_805 ;
        if: LocInfoE loc_805 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_805 ((LocInfoE loc_806 (use{PtrOp} (LocInfoE loc_807 ("ret")))) !={PtrOp, PtrOp} (LocInfoE loc_808 (NULL)))))
        then
        locinfo: loc_801 ;
          Goto "#6"
        else
        locinfo: loc_792 ;
          Goto "#7"
      ]> $
      <[ "#4" :=
        locinfo: loc_786 ;
        Return (LocInfoE loc_787 (NULL))
      ]> $
      <[ "#5" :=
        locinfo: loc_792 ;
        LocInfoE loc_795 ("p") <-{ PtrOp }
          LocInfoE loc_796 (use{PtrOp} (LocInfoE loc_797 ((LocInfoE loc_798 (!{PtrOp} (LocInfoE loc_799 ("p")))) at{struct_mpool} "fallback"))) ;
        locinfo: loc_793 ;
        Goto "continue43"
      ]> $
      <[ "#6" :=
        locinfo: loc_801 ;
        Return (LocInfoE loc_802 (use{PtrOp} (LocInfoE loc_803 ("ret"))))
      ]> $
      <[ "#7" :=
        locinfo: loc_792 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        locinfo: loc_829 ;
        Return (LocInfoE loc_830 (use{PtrOp} (LocInfoE loc_831 ("ret"))))
      ]> $
      <[ "#9" :=
        locinfo: loc_784 ;
        Goto "#1"
      ]> $
      <[ "continue43" :=
        locinfo: loc_785 ;
        Goto "#2"
      ]> $∅
    )%E
  |}.
End code.
