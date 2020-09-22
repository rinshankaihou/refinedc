From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
From refinedc.examples.spinlock Require Import spinlock_annot.
Set Default Proof Using "Type".

(* Generated from [examples/mpool.c]. *)
Section code.
  Definition file_0 : string := "examples/mpool.c".
  Definition loc_2 : location_info := LocationInfo file_0 224 2 224 19.
  Definition loc_3 : location_info := LocationInfo file_0 224 19 224 3.
  Definition loc_4 : location_info := LocationInfo file_0 227 2 229 3.
  Definition loc_5 : location_info := LocationInfo file_0 231 2 231 16.
  Definition loc_6 : location_info := LocationInfo file_0 232 2 232 21.
  Definition loc_7 : location_info := LocationInfo file_0 234 2 234 20.
  Definition loc_8 : location_info := LocationInfo file_0 235 2 235 40.
  Definition loc_9 : location_info := LocationInfo file_0 235 40 235 3.
  Definition loc_10 : location_info := LocationInfo file_0 236 2 236 43.
  Definition loc_11 : location_info := LocationInfo file_0 237 2 237 31.
  Definition loc_12 : location_info := LocationInfo file_0 238 2 238 22.
  Definition loc_13 : location_info := LocationInfo file_0 240 2 240 11.
  Definition loc_14 : location_info := LocationInfo file_0 240 9 240 10.
  Definition loc_15 : location_info := LocationInfo file_0 238 2 238 11.
  Definition loc_16 : location_info := LocationInfo file_0 238 2 238 11.
  Definition loc_17 : location_info := LocationInfo file_0 238 12 238 20.
  Definition loc_18 : location_info := LocationInfo file_0 238 13 238 20.
  Definition loc_19 : location_info := LocationInfo file_0 238 13 238 14.
  Definition loc_20 : location_info := LocationInfo file_0 238 13 238 14.
  Definition loc_21 : location_info := LocationInfo file_0 237 2 237 22.
  Definition loc_22 : location_info := LocationInfo file_0 237 2 237 11.
  Definition loc_23 : location_info := LocationInfo file_0 237 2 237 3.
  Definition loc_24 : location_info := LocationInfo file_0 237 2 237 3.
  Definition loc_25 : location_info := LocationInfo file_0 237 25 237 30.
  Definition loc_26 : location_info := LocationInfo file_0 237 25 237 30.
  Definition loc_27 : location_info := LocationInfo file_0 236 2 236 19.
  Definition loc_28 : location_info := LocationInfo file_0 236 2 236 7.
  Definition loc_29 : location_info := LocationInfo file_0 236 2 236 7.
  Definition loc_30 : location_info := LocationInfo file_0 236 22 236 42.
  Definition loc_31 : location_info := LocationInfo file_0 236 22 236 42.
  Definition loc_32 : location_info := LocationInfo file_0 236 22 236 31.
  Definition loc_33 : location_info := LocationInfo file_0 236 22 236 23.
  Definition loc_34 : location_info := LocationInfo file_0 236 22 236 23.
  Definition loc_35 : location_info := LocationInfo file_0 235 27 235 39.
  Definition loc_36 : location_info := LocationInfo file_0 235 28 235 39.
  Definition loc_37 : location_info := LocationInfo file_0 235 29 235 30.
  Definition loc_38 : location_info := LocationInfo file_0 235 29 235 30.
  Definition loc_39 : location_info := LocationInfo file_0 234 2 234 9.
  Definition loc_40 : location_info := LocationInfo file_0 234 2 234 9.
  Definition loc_41 : location_info := LocationInfo file_0 234 10 234 18.
  Definition loc_42 : location_info := LocationInfo file_0 234 11 234 18.
  Definition loc_43 : location_info := LocationInfo file_0 234 11 234 12.
  Definition loc_44 : location_info := LocationInfo file_0 234 11 234 12.
  Definition loc_45 : location_info := LocationInfo file_0 232 2 232 13.
  Definition loc_46 : location_info := LocationInfo file_0 232 2 232 7.
  Definition loc_47 : location_info := LocationInfo file_0 232 2 232 7.
  Definition loc_48 : location_info := LocationInfo file_0 232 16 232 20.
  Definition loc_49 : location_info := LocationInfo file_0 232 16 232 20.
  Definition loc_50 : location_info := LocationInfo file_0 231 2 231 7.
  Definition loc_51 : location_info := LocationInfo file_0 231 10 231 15.
  Definition loc_52 : location_info := LocationInfo file_0 231 10 231 15.
  Definition loc_53 : location_info := LocationInfo file_0 227 26 229 3.
  Definition loc_54 : location_info := LocationInfo file_0 228 4 228 13.
  Definition loc_55 : location_info := LocationInfo file_0 228 11 228 12.
  Definition loc_57 : location_info := LocationInfo file_0 227 6 227 24.
  Definition loc_58 : location_info := LocationInfo file_0 227 6 227 10.
  Definition loc_59 : location_info := LocationInfo file_0 227 6 227 10.
  Definition loc_60 : location_info := LocationInfo file_0 227 14 227 24.
  Definition loc_61 : location_info := LocationInfo file_0 227 23 227 24.
  Definition loc_62 : location_info := LocationInfo file_0 224 2 224 18.
  Definition loc_63 : location_info := LocationInfo file_0 224 3 224 18.
  Definition loc_64 : location_info := LocationInfo file_0 224 4 224 5.
  Definition loc_65 : location_info := LocationInfo file_0 224 4 224 5.
  Definition loc_68 : location_info := LocationInfo file_0 334 2 334 30.
  Definition loc_69 : location_info := LocationInfo file_0 335 2 335 19.
  Definition loc_70 : location_info := LocationInfo file_0 335 19 335 3.
  Definition loc_71 : location_info := LocationInfo file_0 338 2 338 20.
  Definition loc_72 : location_info := LocationInfo file_0 339 2 339 40.
  Definition loc_73 : location_info := LocationInfo file_0 339 40 339 3.
  Definition loc_74 : location_info := LocationInfo file_0 340 2 340 33.
  Definition loc_75 : location_info := LocationInfo file_0 341 2 341 27.
  Definition loc_76 : location_info := LocationInfo file_0 342 2 342 22.
  Definition loc_77 : location_info := LocationInfo file_0 342 2 342 11.
  Definition loc_78 : location_info := LocationInfo file_0 342 2 342 11.
  Definition loc_79 : location_info := LocationInfo file_0 342 12 342 20.
  Definition loc_80 : location_info := LocationInfo file_0 342 13 342 20.
  Definition loc_81 : location_info := LocationInfo file_0 342 13 342 14.
  Definition loc_82 : location_info := LocationInfo file_0 342 13 342 14.
  Definition loc_83 : location_info := LocationInfo file_0 341 2 341 22.
  Definition loc_84 : location_info := LocationInfo file_0 341 2 341 11.
  Definition loc_85 : location_info := LocationInfo file_0 341 2 341 3.
  Definition loc_86 : location_info := LocationInfo file_0 341 2 341 3.
  Definition loc_87 : location_info := LocationInfo file_0 341 25 341 26.
  Definition loc_88 : location_info := LocationInfo file_0 341 25 341 26.
  Definition loc_89 : location_info := LocationInfo file_0 340 2 340 9.
  Definition loc_90 : location_info := LocationInfo file_0 340 2 340 3.
  Definition loc_91 : location_info := LocationInfo file_0 340 2 340 3.
  Definition loc_92 : location_info := LocationInfo file_0 340 12 340 32.
  Definition loc_93 : location_info := LocationInfo file_0 340 12 340 32.
  Definition loc_94 : location_info := LocationInfo file_0 340 12 340 21.
  Definition loc_95 : location_info := LocationInfo file_0 340 12 340 13.
  Definition loc_96 : location_info := LocationInfo file_0 340 12 340 13.
  Definition loc_97 : location_info := LocationInfo file_0 339 27 339 39.
  Definition loc_98 : location_info := LocationInfo file_0 339 28 339 39.
  Definition loc_99 : location_info := LocationInfo file_0 339 29 339 30.
  Definition loc_100 : location_info := LocationInfo file_0 339 29 339 30.
  Definition loc_101 : location_info := LocationInfo file_0 338 2 338 9.
  Definition loc_102 : location_info := LocationInfo file_0 338 2 338 9.
  Definition loc_103 : location_info := LocationInfo file_0 338 10 338 18.
  Definition loc_104 : location_info := LocationInfo file_0 338 11 338 18.
  Definition loc_105 : location_info := LocationInfo file_0 338 11 338 12.
  Definition loc_106 : location_info := LocationInfo file_0 338 11 338 12.
  Definition loc_107 : location_info := LocationInfo file_0 335 2 335 18.
  Definition loc_108 : location_info := LocationInfo file_0 335 3 335 18.
  Definition loc_109 : location_info := LocationInfo file_0 335 4 335 5.
  Definition loc_110 : location_info := LocationInfo file_0 335 4 335 5.
  Definition loc_111 : location_info := LocationInfo file_0 334 26 334 29.
  Definition loc_112 : location_info := LocationInfo file_0 334 26 334 29.
  Definition loc_117 : location_info := LocationInfo file_0 111 2 111 29.
  Definition loc_118 : location_info := LocationInfo file_0 112 2 112 40.
  Definition loc_119 : location_info := LocationInfo file_0 113 2 113 40.
  Definition loc_120 : location_info := LocationInfo file_0 114 2 114 31.
  Definition loc_121 : location_info := LocationInfo file_0 115 2 115 20.
  Definition loc_122 : location_info := LocationInfo file_0 115 2 115 9.
  Definition loc_123 : location_info := LocationInfo file_0 115 2 115 9.
  Definition loc_124 : location_info := LocationInfo file_0 115 10 115 18.
  Definition loc_125 : location_info := LocationInfo file_0 115 11 115 18.
  Definition loc_126 : location_info := LocationInfo file_0 115 11 115 12.
  Definition loc_127 : location_info := LocationInfo file_0 115 11 115 12.
  Definition loc_128 : location_info := LocationInfo file_0 114 2 114 13.
  Definition loc_129 : location_info := LocationInfo file_0 114 2 114 3.
  Definition loc_130 : location_info := LocationInfo file_0 114 2 114 3.
  Definition loc_131 : location_info := LocationInfo file_0 114 16 114 30.
  Definition loc_132 : location_info := LocationInfo file_0 113 2 113 22.
  Definition loc_133 : location_info := LocationInfo file_0 113 2 113 11.
  Definition loc_134 : location_info := LocationInfo file_0 113 2 113 3.
  Definition loc_135 : location_info := LocationInfo file_0 113 2 113 3.
  Definition loc_136 : location_info := LocationInfo file_0 113 25 113 39.
  Definition loc_137 : location_info := LocationInfo file_0 112 2 112 22.
  Definition loc_138 : location_info := LocationInfo file_0 112 2 112 11.
  Definition loc_139 : location_info := LocationInfo file_0 112 2 112 3.
  Definition loc_140 : location_info := LocationInfo file_0 112 2 112 3.
  Definition loc_141 : location_info := LocationInfo file_0 112 25 112 39.
  Definition loc_142 : location_info := LocationInfo file_0 111 2 111 15.
  Definition loc_143 : location_info := LocationInfo file_0 111 2 111 3.
  Definition loc_144 : location_info := LocationInfo file_0 111 2 111 3.
  Definition loc_145 : location_info := LocationInfo file_0 111 18 111 28.
  Definition loc_146 : location_info := LocationInfo file_0 111 18 111 28.
  Definition loc_149 : location_info := LocationInfo file_0 130 2 130 34.
  Definition loc_150 : location_info := LocationInfo file_0 132 2 132 23.
  Definition loc_151 : location_info := LocationInfo file_0 133 2 133 43.
  Definition loc_152 : location_info := LocationInfo file_0 133 43 133 3.
  Definition loc_153 : location_info := LocationInfo file_0 135 2 135 49.
  Definition loc_154 : location_info := LocationInfo file_0 136 2 136 49.
  Definition loc_155 : location_info := LocationInfo file_0 137 2 137 31.
  Definition loc_156 : location_info := LocationInfo file_0 139 2 139 43.
  Definition loc_157 : location_info := LocationInfo file_0 140 2 140 43.
  Definition loc_158 : location_info := LocationInfo file_0 143 2 143 25.
  Definition loc_159 : location_info := LocationInfo file_0 143 2 143 11.
  Definition loc_160 : location_info := LocationInfo file_0 143 2 143 11.
  Definition loc_161 : location_info := LocationInfo file_0 143 12 143 23.
  Definition loc_162 : location_info := LocationInfo file_0 143 13 143 23.
  Definition loc_163 : location_info := LocationInfo file_0 143 13 143 17.
  Definition loc_164 : location_info := LocationInfo file_0 143 13 143 17.
  Definition loc_165 : location_info := LocationInfo file_0 140 2 140 25.
  Definition loc_166 : location_info := LocationInfo file_0 140 2 140 14.
  Definition loc_167 : location_info := LocationInfo file_0 140 2 140 6.
  Definition loc_168 : location_info := LocationInfo file_0 140 2 140 6.
  Definition loc_169 : location_info := LocationInfo file_0 140 28 140 42.
  Definition loc_170 : location_info := LocationInfo file_0 139 2 139 25.
  Definition loc_171 : location_info := LocationInfo file_0 139 2 139 14.
  Definition loc_172 : location_info := LocationInfo file_0 139 2 139 6.
  Definition loc_173 : location_info := LocationInfo file_0 139 2 139 6.
  Definition loc_174 : location_info := LocationInfo file_0 139 28 139 42.
  Definition loc_175 : location_info := LocationInfo file_0 137 2 137 13.
  Definition loc_176 : location_info := LocationInfo file_0 137 2 137 3.
  Definition loc_177 : location_info := LocationInfo file_0 137 2 137 3.
  Definition loc_178 : location_info := LocationInfo file_0 137 16 137 30.
  Definition loc_179 : location_info := LocationInfo file_0 137 16 137 30.
  Definition loc_180 : location_info := LocationInfo file_0 137 16 137 20.
  Definition loc_181 : location_info := LocationInfo file_0 137 16 137 20.
  Definition loc_182 : location_info := LocationInfo file_0 136 2 136 22.
  Definition loc_183 : location_info := LocationInfo file_0 136 2 136 11.
  Definition loc_184 : location_info := LocationInfo file_0 136 2 136 3.
  Definition loc_185 : location_info := LocationInfo file_0 136 2 136 3.
  Definition loc_186 : location_info := LocationInfo file_0 136 25 136 48.
  Definition loc_187 : location_info := LocationInfo file_0 136 25 136 48.
  Definition loc_188 : location_info := LocationInfo file_0 136 25 136 37.
  Definition loc_189 : location_info := LocationInfo file_0 136 25 136 29.
  Definition loc_190 : location_info := LocationInfo file_0 136 25 136 29.
  Definition loc_191 : location_info := LocationInfo file_0 135 2 135 22.
  Definition loc_192 : location_info := LocationInfo file_0 135 2 135 11.
  Definition loc_193 : location_info := LocationInfo file_0 135 2 135 3.
  Definition loc_194 : location_info := LocationInfo file_0 135 2 135 3.
  Definition loc_195 : location_info := LocationInfo file_0 135 25 135 48.
  Definition loc_196 : location_info := LocationInfo file_0 135 25 135 48.
  Definition loc_197 : location_info := LocationInfo file_0 135 25 135 37.
  Definition loc_198 : location_info := LocationInfo file_0 135 25 135 29.
  Definition loc_199 : location_info := LocationInfo file_0 135 25 135 29.
  Definition loc_200 : location_info := LocationInfo file_0 133 27 133 42.
  Definition loc_201 : location_info := LocationInfo file_0 133 28 133 42.
  Definition loc_202 : location_info := LocationInfo file_0 133 29 133 33.
  Definition loc_203 : location_info := LocationInfo file_0 133 29 133 33.
  Definition loc_204 : location_info := LocationInfo file_0 132 2 132 9.
  Definition loc_205 : location_info := LocationInfo file_0 132 2 132 9.
  Definition loc_206 : location_info := LocationInfo file_0 132 10 132 21.
  Definition loc_207 : location_info := LocationInfo file_0 132 11 132 21.
  Definition loc_208 : location_info := LocationInfo file_0 132 11 132 15.
  Definition loc_209 : location_info := LocationInfo file_0 132 11 132 15.
  Definition loc_210 : location_info := LocationInfo file_0 130 2 130 12.
  Definition loc_211 : location_info := LocationInfo file_0 130 2 130 12.
  Definition loc_212 : location_info := LocationInfo file_0 130 13 130 14.
  Definition loc_213 : location_info := LocationInfo file_0 130 13 130 14.
  Definition loc_214 : location_info := LocationInfo file_0 130 16 130 32.
  Definition loc_215 : location_info := LocationInfo file_0 130 16 130 32.
  Definition loc_216 : location_info := LocationInfo file_0 130 16 130 20.
  Definition loc_217 : location_info := LocationInfo file_0 130 16 130 20.
  Definition loc_220 : location_info := LocationInfo file_0 155 2 155 38.
  Definition loc_221 : location_info := LocationInfo file_0 156 2 156 25.
  Definition loc_222 : location_info := LocationInfo file_0 156 2 156 13.
  Definition loc_223 : location_info := LocationInfo file_0 156 2 156 3.
  Definition loc_224 : location_info := LocationInfo file_0 156 2 156 3.
  Definition loc_225 : location_info := LocationInfo file_0 156 16 156 24.
  Definition loc_226 : location_info := LocationInfo file_0 156 16 156 24.
  Definition loc_227 : location_info := LocationInfo file_0 155 2 155 12.
  Definition loc_228 : location_info := LocationInfo file_0 155 2 155 12.
  Definition loc_229 : location_info := LocationInfo file_0 155 13 155 14.
  Definition loc_230 : location_info := LocationInfo file_0 155 13 155 14.
  Definition loc_231 : location_info := LocationInfo file_0 155 16 155 36.
  Definition loc_232 : location_info := LocationInfo file_0 155 16 155 36.
  Definition loc_233 : location_info := LocationInfo file_0 155 16 155 24.
  Definition loc_234 : location_info := LocationInfo file_0 155 16 155 24.
  Definition loc_237 : location_info := LocationInfo file_0 170 2 172 3.
  Definition loc_238 : location_info := LocationInfo file_0 174 2 174 31.
  Definition loc_239 : location_info := LocationInfo file_0 175 2 175 31.
  Definition loc_240 : location_info := LocationInfo file_0 180 2 184 3.
  Definition loc_241 : location_info := LocationInfo file_0 190 2 196 3.
  Definition loc_242 : location_info := LocationInfo file_0 198 2 198 40.
  Definition loc_243 : location_info := LocationInfo file_0 199 2 199 40.
  Definition loc_244 : location_info := LocationInfo file_0 200 2 200 31.
  Definition loc_245 : location_info := LocationInfo file_0 200 2 200 13.
  Definition loc_246 : location_info := LocationInfo file_0 200 2 200 3.
  Definition loc_247 : location_info := LocationInfo file_0 200 2 200 3.
  Definition loc_248 : location_info := LocationInfo file_0 200 16 200 30.
  Definition loc_249 : location_info := LocationInfo file_0 199 2 199 22.
  Definition loc_250 : location_info := LocationInfo file_0 199 2 199 11.
  Definition loc_251 : location_info := LocationInfo file_0 199 2 199 3.
  Definition loc_252 : location_info := LocationInfo file_0 199 2 199 3.
  Definition loc_253 : location_info := LocationInfo file_0 199 25 199 39.
  Definition loc_254 : location_info := LocationInfo file_0 198 2 198 22.
  Definition loc_255 : location_info := LocationInfo file_0 198 2 198 11.
  Definition loc_256 : location_info := LocationInfo file_0 198 2 198 3.
  Definition loc_257 : location_info := LocationInfo file_0 198 2 198 3.
  Definition loc_258 : location_info := LocationInfo file_0 198 25 198 39.
  Definition loc_259 : location_info := LocationInfo file_0 190 2 196 3.
  Definition loc_260 : location_info := LocationInfo file_0 190 34 196 3.
  Definition loc_261 : location_info := LocationInfo file_0 191 4 191 23.
  Definition loc_262 : location_info := LocationInfo file_0 192 4 192 30.
  Definition loc_263 : location_info := LocationInfo file_0 194 4 194 30.
  Definition loc_264 : location_info := LocationInfo file_0 195 4 195 45.
  Definition loc_265 : location_info := LocationInfo file_0 190 2 196 3.
  Definition loc_266 : location_info := LocationInfo file_0 190 2 196 3.
  Definition loc_267 : location_info := LocationInfo file_0 195 4 195 19.
  Definition loc_268 : location_info := LocationInfo file_0 195 4 195 19.
  Definition loc_269 : location_info := LocationInfo file_0 195 20 195 31.
  Definition loc_270 : location_info := LocationInfo file_0 195 20 195 31.
  Definition loc_271 : location_info := LocationInfo file_0 195 20 195 21.
  Definition loc_272 : location_info := LocationInfo file_0 195 20 195 21.
  Definition loc_273 : location_info := LocationInfo file_0 195 33 195 37.
  Definition loc_274 : location_info := LocationInfo file_0 195 33 195 37.
  Definition loc_275 : location_info := LocationInfo file_0 195 39 195 43.
  Definition loc_276 : location_info := LocationInfo file_0 195 39 195 43.
  Definition loc_277 : location_info := LocationInfo file_0 194 4 194 9.
  Definition loc_278 : location_info := LocationInfo file_0 194 12 194 29.
  Definition loc_279 : location_info := LocationInfo file_0 194 12 194 29.
  Definition loc_280 : location_info := LocationInfo file_0 194 12 194 17.
  Definition loc_281 : location_info := LocationInfo file_0 194 12 194 17.
  Definition loc_282 : location_info := LocationInfo file_0 192 18 192 29.
  Definition loc_283 : location_info := LocationInfo file_0 192 18 192 29.
  Definition loc_284 : location_info := LocationInfo file_0 192 18 192 23.
  Definition loc_285 : location_info := LocationInfo file_0 192 18 192 23.
  Definition loc_288 : location_info := LocationInfo file_0 191 17 191 22.
  Definition loc_289 : location_info := LocationInfo file_0 191 17 191 22.
  Definition loc_292 : location_info := LocationInfo file_0 190 9 190 32.
  Definition loc_293 : location_info := LocationInfo file_0 190 9 190 14.
  Definition loc_294 : location_info := LocationInfo file_0 190 9 190 14.
  Definition loc_295 : location_info := LocationInfo file_0 190 18 190 32.
  Definition loc_296 : location_info := LocationInfo file_0 180 2 184 3.
  Definition loc_297 : location_info := LocationInfo file_0 180 34 184 3.
  Definition loc_298 : location_info := LocationInfo file_0 181 4 181 23.
  Definition loc_299 : location_info := LocationInfo file_0 182 4 182 24.
  Definition loc_300 : location_info := LocationInfo file_0 183 4 183 34.
  Definition loc_301 : location_info := LocationInfo file_0 180 2 184 3.
  Definition loc_302 : location_info := LocationInfo file_0 180 2 184 3.
  Definition loc_303 : location_info := LocationInfo file_0 183 4 183 14.
  Definition loc_304 : location_info := LocationInfo file_0 183 4 183 14.
  Definition loc_305 : location_info := LocationInfo file_0 183 15 183 26.
  Definition loc_306 : location_info := LocationInfo file_0 183 15 183 26.
  Definition loc_307 : location_info := LocationInfo file_0 183 15 183 16.
  Definition loc_308 : location_info := LocationInfo file_0 183 15 183 16.
  Definition loc_309 : location_info := LocationInfo file_0 183 28 183 32.
  Definition loc_310 : location_info := LocationInfo file_0 183 28 183 32.
  Definition loc_311 : location_info := LocationInfo file_0 182 4 182 9.
  Definition loc_312 : location_info := LocationInfo file_0 182 12 182 23.
  Definition loc_313 : location_info := LocationInfo file_0 182 12 182 23.
  Definition loc_314 : location_info := LocationInfo file_0 182 12 182 17.
  Definition loc_315 : location_info := LocationInfo file_0 182 12 182 17.
  Definition loc_316 : location_info := LocationInfo file_0 181 17 181 22.
  Definition loc_317 : location_info := LocationInfo file_0 181 17 181 22.
  Definition loc_320 : location_info := LocationInfo file_0 180 9 180 32.
  Definition loc_321 : location_info := LocationInfo file_0 180 9 180 14.
  Definition loc_322 : location_info := LocationInfo file_0 180 9 180 14.
  Definition loc_323 : location_info := LocationInfo file_0 180 18 180 32.
  Definition loc_324 : location_info := LocationInfo file_0 175 2 175 7.
  Definition loc_325 : location_info := LocationInfo file_0 175 10 175 30.
  Definition loc_326 : location_info := LocationInfo file_0 175 10 175 30.
  Definition loc_327 : location_info := LocationInfo file_0 175 10 175 19.
  Definition loc_328 : location_info := LocationInfo file_0 175 10 175 11.
  Definition loc_329 : location_info := LocationInfo file_0 175 10 175 11.
  Definition loc_330 : location_info := LocationInfo file_0 174 2 174 7.
  Definition loc_331 : location_info := LocationInfo file_0 174 10 174 30.
  Definition loc_332 : location_info := LocationInfo file_0 174 10 174 30.
  Definition loc_333 : location_info := LocationInfo file_0 174 10 174 19.
  Definition loc_334 : location_info := LocationInfo file_0 174 10 174 11.
  Definition loc_335 : location_info := LocationInfo file_0 174 10 174 11.
  Definition loc_336 : location_info := LocationInfo file_0 170 37 172 3.
  Definition loc_337 : location_info := LocationInfo file_0 171 4 171 11.
  Definition loc_340 : location_info := LocationInfo file_0 170 6 170 35.
  Definition loc_341 : location_info := LocationInfo file_0 170 6 170 17.
  Definition loc_342 : location_info := LocationInfo file_0 170 6 170 17.
  Definition loc_343 : location_info := LocationInfo file_0 170 6 170 7.
  Definition loc_344 : location_info := LocationInfo file_0 170 6 170 7.
  Definition loc_345 : location_info := LocationInfo file_0 170 21 170 35.
  Definition loc_348 : location_info := LocationInfo file_0 260 2 260 20.
  Definition loc_349 : location_info := LocationInfo file_0 261 2 261 40.
  Definition loc_350 : location_info := LocationInfo file_0 261 40 261 3.
  Definition loc_351 : location_info := LocationInfo file_0 262 2 268 3.
  Definition loc_352 : location_info := LocationInfo file_0 271 2 271 31.
  Definition loc_353 : location_info := LocationInfo file_0 272 2 276 3.
  Definition loc_354 : location_info := LocationInfo file_0 278 2 285 3.
  Definition loc_355 : location_info := LocationInfo file_0 287 2 287 14.
  Definition loc_356 : location_info := LocationInfo file_0 287 14 290 22.
  Definition loc_357 : location_info := LocationInfo file_0 290 2 290 22.
  Definition loc_358 : location_info := LocationInfo file_0 292 2 292 13.
  Definition loc_359 : location_info := LocationInfo file_0 292 9 292 12.
  Definition loc_360 : location_info := LocationInfo file_0 292 9 292 12.
  Definition loc_361 : location_info := LocationInfo file_0 290 2 290 11.
  Definition loc_362 : location_info := LocationInfo file_0 290 2 290 11.
  Definition loc_363 : location_info := LocationInfo file_0 290 12 290 20.
  Definition loc_364 : location_info := LocationInfo file_0 290 13 290 20.
  Definition loc_365 : location_info := LocationInfo file_0 290 13 290 14.
  Definition loc_366 : location_info := LocationInfo file_0 290 13 290 14.
  Definition loc_367 : location_info := LocationInfo file_0 287 2 287 5.
  Definition loc_368 : location_info := LocationInfo file_0 287 8 287 13.
  Definition loc_369 : location_info := LocationInfo file_0 287 8 287 13.
  Definition loc_370 : location_info := LocationInfo file_0 278 36 280 3.
  Definition loc_371 : location_info := LocationInfo file_0 279 4 279 45.
  Definition loc_372 : location_info := LocationInfo file_0 279 4 279 24.
  Definition loc_373 : location_info := LocationInfo file_0 279 4 279 13.
  Definition loc_374 : location_info := LocationInfo file_0 279 4 279 5.
  Definition loc_375 : location_info := LocationInfo file_0 279 4 279 5.
  Definition loc_376 : location_info := LocationInfo file_0 279 27 279 44.
  Definition loc_377 : location_info := LocationInfo file_0 279 27 279 44.
  Definition loc_378 : location_info := LocationInfo file_0 279 27 279 32.
  Definition loc_379 : location_info := LocationInfo file_0 279 27 279 32.
  Definition loc_380 : location_info := LocationInfo file_0 280 9 285 3.
  Definition loc_381 : location_info := LocationInfo file_0 281 4 281 79.
  Definition loc_382 : location_info := LocationInfo file_0 282 4 282 46.
  Definition loc_383 : location_info := LocationInfo file_0 283 4 283 50.
  Definition loc_384 : location_info := LocationInfo file_0 284 4 284 37.
  Definition loc_385 : location_info := LocationInfo file_0 284 4 284 24.
  Definition loc_386 : location_info := LocationInfo file_0 284 4 284 13.
  Definition loc_387 : location_info := LocationInfo file_0 284 4 284 5.
  Definition loc_388 : location_info := LocationInfo file_0 284 4 284 5.
  Definition loc_389 : location_info := LocationInfo file_0 284 27 284 36.
  Definition loc_390 : location_info := LocationInfo file_0 284 27 284 36.
  Definition loc_391 : location_info := LocationInfo file_0 283 4 283 19.
  Definition loc_392 : location_info := LocationInfo file_0 283 4 283 13.
  Definition loc_393 : location_info := LocationInfo file_0 283 4 283 13.
  Definition loc_394 : location_info := LocationInfo file_0 283 22 283 49.
  Definition loc_395 : location_info := LocationInfo file_0 283 22 283 33.
  Definition loc_396 : location_info := LocationInfo file_0 283 22 283 33.
  Definition loc_397 : location_info := LocationInfo file_0 283 22 283 27.
  Definition loc_398 : location_info := LocationInfo file_0 283 22 283 27.
  Definition loc_399 : location_info := LocationInfo file_0 283 36 283 49.
  Definition loc_400 : location_info := LocationInfo file_0 283 36 283 49.
  Definition loc_401 : location_info := LocationInfo file_0 283 36 283 37.
  Definition loc_402 : location_info := LocationInfo file_0 283 36 283 37.
  Definition loc_403 : location_info := LocationInfo file_0 282 4 282 25.
  Definition loc_404 : location_info := LocationInfo file_0 282 4 282 13.
  Definition loc_405 : location_info := LocationInfo file_0 282 4 282 13.
  Definition loc_406 : location_info := LocationInfo file_0 282 28 282 45.
  Definition loc_407 : location_info := LocationInfo file_0 282 28 282 45.
  Definition loc_408 : location_info := LocationInfo file_0 282 28 282 33.
  Definition loc_409 : location_info := LocationInfo file_0 282 28 282 33.
  Definition loc_410 : location_info := LocationInfo file_0 281 4 281 13.
  Definition loc_411 : location_info := LocationInfo file_0 281 16 281 78.
  Definition loc_412 : location_info := LocationInfo file_0 281 38 281 78.
  Definition loc_413 : location_info := LocationInfo file_0 281 39 281 61.
  Definition loc_414 : location_info := LocationInfo file_0 281 56 281 61.
  Definition loc_415 : location_info := LocationInfo file_0 281 56 281 61.
  Definition loc_416 : location_info := LocationInfo file_0 281 64 281 77.
  Definition loc_417 : location_info := LocationInfo file_0 281 64 281 77.
  Definition loc_418 : location_info := LocationInfo file_0 281 64 281 65.
  Definition loc_419 : location_info := LocationInfo file_0 281 64 281 65.
  Definition loc_420 : location_info := LocationInfo file_0 278 6 278 34.
  Definition loc_421 : location_info := LocationInfo file_0 278 6 278 19.
  Definition loc_422 : location_info := LocationInfo file_0 278 6 278 19.
  Definition loc_423 : location_info := LocationInfo file_0 278 6 278 7.
  Definition loc_424 : location_info := LocationInfo file_0 278 6 278 7.
  Definition loc_425 : location_info := LocationInfo file_0 278 23 278 34.
  Definition loc_426 : location_info := LocationInfo file_0 278 23 278 34.
  Definition loc_427 : location_info := LocationInfo file_0 278 23 278 28.
  Definition loc_428 : location_info := LocationInfo file_0 278 23 278 28.
  Definition loc_429 : location_info := LocationInfo file_0 272 31 276 3.
  Definition loc_430 : location_info := LocationInfo file_0 274 4 274 25.
  Definition loc_431 : location_info := LocationInfo file_0 275 4 275 14.
  Definition loc_432 : location_info := LocationInfo file_0 274 4 274 7.
  Definition loc_433 : location_info := LocationInfo file_0 274 10 274 24.
  Definition loc_435 : location_info := LocationInfo file_0 272 6 272 29.
  Definition loc_436 : location_info := LocationInfo file_0 272 6 272 11.
  Definition loc_437 : location_info := LocationInfo file_0 272 6 272 11.
  Definition loc_438 : location_info := LocationInfo file_0 272 15 272 29.
  Definition loc_439 : location_info := LocationInfo file_0 271 2 271 7.
  Definition loc_440 : location_info := LocationInfo file_0 271 10 271 30.
  Definition loc_441 : location_info := LocationInfo file_0 271 10 271 30.
  Definition loc_442 : location_info := LocationInfo file_0 271 10 271 19.
  Definition loc_443 : location_info := LocationInfo file_0 271 10 271 11.
  Definition loc_444 : location_info := LocationInfo file_0 271 10 271 11.
  Definition loc_445 : location_info := LocationInfo file_0 262 46 268 3.
  Definition loc_446 : location_info := LocationInfo file_0 263 4 263 53.
  Definition loc_447 : location_info := LocationInfo file_0 265 4 265 39.
  Definition loc_448 : location_info := LocationInfo file_0 266 4 266 16.
  Definition loc_449 : location_info := LocationInfo file_0 267 4 267 14.
  Definition loc_450 : location_info := LocationInfo file_0 266 4 266 7.
  Definition loc_451 : location_info := LocationInfo file_0 266 10 266 15.
  Definition loc_452 : location_info := LocationInfo file_0 266 10 266 15.
  Definition loc_453 : location_info := LocationInfo file_0 265 4 265 24.
  Definition loc_454 : location_info := LocationInfo file_0 265 4 265 13.
  Definition loc_455 : location_info := LocationInfo file_0 265 4 265 5.
  Definition loc_456 : location_info := LocationInfo file_0 265 4 265 5.
  Definition loc_457 : location_info := LocationInfo file_0 265 27 265 38.
  Definition loc_458 : location_info := LocationInfo file_0 265 27 265 38.
  Definition loc_459 : location_info := LocationInfo file_0 265 27 265 32.
  Definition loc_460 : location_info := LocationInfo file_0 265 27 265 32.
  Definition loc_461 : location_info := LocationInfo file_0 263 32 263 52.
  Definition loc_462 : location_info := LocationInfo file_0 263 32 263 52.
  Definition loc_463 : location_info := LocationInfo file_0 263 32 263 41.
  Definition loc_464 : location_info := LocationInfo file_0 263 32 263 33.
  Definition loc_465 : location_info := LocationInfo file_0 263 32 263 33.
  Definition loc_469 : location_info := LocationInfo file_0 262 6 262 44.
  Definition loc_470 : location_info := LocationInfo file_0 262 6 262 26.
  Definition loc_471 : location_info := LocationInfo file_0 262 6 262 26.
  Definition loc_472 : location_info := LocationInfo file_0 262 6 262 15.
  Definition loc_473 : location_info := LocationInfo file_0 262 6 262 7.
  Definition loc_474 : location_info := LocationInfo file_0 262 6 262 7.
  Definition loc_475 : location_info := LocationInfo file_0 262 30 262 44.
  Definition loc_476 : location_info := LocationInfo file_0 261 27 261 39.
  Definition loc_477 : location_info := LocationInfo file_0 261 28 261 39.
  Definition loc_478 : location_info := LocationInfo file_0 261 29 261 30.
  Definition loc_479 : location_info := LocationInfo file_0 261 29 261 30.
  Definition loc_480 : location_info := LocationInfo file_0 260 2 260 9.
  Definition loc_481 : location_info := LocationInfo file_0 260 2 260 9.
  Definition loc_482 : location_info := LocationInfo file_0 260 10 260 18.
  Definition loc_483 : location_info := LocationInfo file_0 260 11 260 18.
  Definition loc_484 : location_info := LocationInfo file_0 260 11 260 12.
  Definition loc_485 : location_info := LocationInfo file_0 260 11 260 12.
  Definition loc_488 : location_info := LocationInfo file_0 305 2 305 41.
  Definition loc_489 : location_info := LocationInfo file_0 306 2 308 3.
  Definition loc_490 : location_info := LocationInfo file_0 309 2 309 18.
  Definition loc_491 : location_info := LocationInfo file_0 313 2 319 3.
  Definition loc_492 : location_info := LocationInfo file_0 321 2 321 24.
  Definition loc_493 : location_info := LocationInfo file_0 321 9 321 23.
  Definition loc_494 : location_info := LocationInfo file_0 313 2 319 3.
  Definition loc_495 : location_info := LocationInfo file_0 313 30 319 3.
  Definition loc_496 : location_info := LocationInfo file_0 314 4 314 37.
  Definition loc_497 : location_info := LocationInfo file_0 315 4 317 5.
  Definition loc_498 : location_info := LocationInfo file_0 318 4 318 20.
  Definition loc_499 : location_info := LocationInfo file_0 313 2 319 3.
  Definition loc_500 : location_info := LocationInfo file_0 313 2 319 3.
  Definition loc_501 : location_info := LocationInfo file_0 318 4 318 5.
  Definition loc_502 : location_info := LocationInfo file_0 318 8 318 19.
  Definition loc_503 : location_info := LocationInfo file_0 318 8 318 19.
  Definition loc_504 : location_info := LocationInfo file_0 318 8 318 9.
  Definition loc_505 : location_info := LocationInfo file_0 318 8 318 9.
  Definition loc_506 : location_info := LocationInfo file_0 315 31 317 5.
  Definition loc_507 : location_info := LocationInfo file_0 316 6 316 17.
  Definition loc_508 : location_info := LocationInfo file_0 316 13 316 16.
  Definition loc_509 : location_info := LocationInfo file_0 316 13 316 16.
  Definition loc_511 : location_info := LocationInfo file_0 315 8 315 29.
  Definition loc_512 : location_info := LocationInfo file_0 315 8 315 11.
  Definition loc_513 : location_info := LocationInfo file_0 315 8 315 11.
  Definition loc_514 : location_info := LocationInfo file_0 315 15 315 29.
  Definition loc_515 : location_info := LocationInfo file_0 314 4 314 7.
  Definition loc_516 : location_info := LocationInfo file_0 314 10 314 36.
  Definition loc_517 : location_info := LocationInfo file_0 314 10 314 33.
  Definition loc_518 : location_info := LocationInfo file_0 314 10 314 33.
  Definition loc_519 : location_info := LocationInfo file_0 314 34 314 35.
  Definition loc_520 : location_info := LocationInfo file_0 314 34 314 35.
  Definition loc_521 : location_info := LocationInfo file_0 313 9 313 28.
  Definition loc_522 : location_info := LocationInfo file_0 313 9 313 10.
  Definition loc_523 : location_info := LocationInfo file_0 313 9 313 10.
  Definition loc_524 : location_info := LocationInfo file_0 313 14 313 28.
  Definition loc_525 : location_info := LocationInfo file_0 309 2 309 3.
  Definition loc_526 : location_info := LocationInfo file_0 309 6 309 17.
  Definition loc_527 : location_info := LocationInfo file_0 309 6 309 17.
  Definition loc_528 : location_info := LocationInfo file_0 309 6 309 7.
  Definition loc_529 : location_info := LocationInfo file_0 309 6 309 7.
  Definition loc_530 : location_info := LocationInfo file_0 306 29 308 3.
  Definition loc_531 : location_info := LocationInfo file_0 307 4 307 15.
  Definition loc_532 : location_info := LocationInfo file_0 307 11 307 14.
  Definition loc_533 : location_info := LocationInfo file_0 307 11 307 14.
  Definition loc_535 : location_info := LocationInfo file_0 306 6 306 27.
  Definition loc_536 : location_info := LocationInfo file_0 306 6 306 9.
  Definition loc_537 : location_info := LocationInfo file_0 306 6 306 9.
  Definition loc_538 : location_info := LocationInfo file_0 306 13 306 27.
  Definition loc_539 : location_info := LocationInfo file_0 305 14 305 40.
  Definition loc_540 : location_info := LocationInfo file_0 305 14 305 37.
  Definition loc_541 : location_info := LocationInfo file_0 305 14 305 37.
  Definition loc_542 : location_info := LocationInfo file_0 305 38 305 39.
  Definition loc_543 : location_info := LocationInfo file_0 305 38 305 39.
  Definition loc_548 : location_info := LocationInfo file_0 362 2 362 29.
  Definition loc_549 : location_info := LocationInfo file_0 364 2 364 25.
  Definition loc_550 : location_info := LocationInfo file_0 366 2 366 20.
  Definition loc_551 : location_info := LocationInfo file_0 367 2 367 40.
  Definition loc_552 : location_info := LocationInfo file_0 367 40 367 3.
  Definition loc_553 : location_info := LocationInfo file_0 373 2 373 31.
  Definition loc_554 : location_info := LocationInfo file_0 383 2 429 3.
  Definition loc_555 : location_info := LocationInfo file_0 430 2 430 11.
  Definition loc_556 : location_info := LocationInfo file_0 430 11 430 3.
  Definition loc_557 : location_info := LocationInfo file_0 432 2 432 22.
  Definition loc_558 : location_info := LocationInfo file_0 434 2 434 13.
  Definition loc_559 : location_info := LocationInfo file_0 434 9 434 12.
  Definition loc_560 : location_info := LocationInfo file_0 434 9 434 12.
  Definition loc_561 : location_info := LocationInfo file_0 432 2 432 11.
  Definition loc_562 : location_info := LocationInfo file_0 432 2 432 11.
  Definition loc_563 : location_info := LocationInfo file_0 432 12 432 20.
  Definition loc_564 : location_info := LocationInfo file_0 432 13 432 20.
  Definition loc_565 : location_info := LocationInfo file_0 432 13 432 14.
  Definition loc_566 : location_info := LocationInfo file_0 432 13 432 14.
  Definition loc_567 : location_info := LocationInfo file_0 430 2 430 10.
  Definition loc_568 : location_info := LocationInfo file_0 430 3 430 10.
  Definition loc_569 : location_info := LocationInfo file_0 430 5 430 9.
  Definition loc_570 : location_info := LocationInfo file_0 430 5 430 9.
  Definition loc_571 : location_info := LocationInfo file_0 383 2 429 3.
  Definition loc_572 : location_info := LocationInfo file_0 383 34 429 3.
  Definition loc_573 : location_info := LocationInfo file_0 386 4 386 38.
  Definition loc_574 : location_info := LocationInfo file_0 390 4 390 67.
  Definition loc_575 : location_info := LocationInfo file_0 397 4 426 5.
  Definition loc_576 : location_info := LocationInfo file_0 428 4 428 30.
  Definition loc_577 : location_info := LocationInfo file_0 383 2 429 3.
  Definition loc_578 : location_info := LocationInfo file_0 383 2 429 3.
  Definition loc_579 : location_info := LocationInfo file_0 428 4 428 8.
  Definition loc_580 : location_info := LocationInfo file_0 428 11 428 29.
  Definition loc_581 : location_info := LocationInfo file_0 428 12 428 29.
  Definition loc_582 : location_info := LocationInfo file_0 428 12 428 17.
  Definition loc_583 : location_info := LocationInfo file_0 428 12 428 17.
  Definition loc_584 : location_info := LocationInfo file_0 397 61 426 5.
  Definition loc_585 : location_info := LocationInfo file_0 398 6 398 38.
  Definition loc_586 : location_info := LocationInfo file_0 399 6 399 57.
  Definition loc_587 : location_info := LocationInfo file_0 400 6 400 42.
  Definition loc_588 : location_info := LocationInfo file_0 400 42 400 7.
  Definition loc_589 : location_info := LocationInfo file_0 401 6 401 52.
  Definition loc_590 : location_info := LocationInfo file_0 403 6 410 7.
  Definition loc_591 : location_info := LocationInfo file_0 416 6 420 7.
  Definition loc_592 : location_info := LocationInfo file_0 422 6 422 16.
  Definition loc_593 : location_info := LocationInfo file_0 422 16 422 7.
  Definition loc_594 : location_info := LocationInfo file_0 423 6 423 55.
  Definition loc_595 : location_info := LocationInfo file_0 423 55 423 7.
  Definition loc_596 : location_info := LocationInfo file_0 424 6 424 26.
  Definition loc_597 : location_info := LocationInfo file_0 425 6 425 12.
  Definition loc_598 : location_info := LocationInfo file_0 424 6 424 9.
  Definition loc_599 : location_info := LocationInfo file_0 424 12 424 25.
  Definition loc_600 : location_info := LocationInfo file_0 424 20 424 25.
  Definition loc_601 : location_info := LocationInfo file_0 424 20 424 25.
  Definition loc_602 : location_info := LocationInfo file_0 423 45 423 54.
  Definition loc_603 : location_info := LocationInfo file_0 423 46 423 54.
  Definition loc_604 : location_info := LocationInfo file_0 423 48 423 53.
  Definition loc_605 : location_info := LocationInfo file_0 423 48 423 53.
  Definition loc_606 : location_info := LocationInfo file_0 422 6 422 15.
  Definition loc_607 : location_info := LocationInfo file_0 422 7 422 15.
  Definition loc_608 : location_info := LocationInfo file_0 422 9 422 14.
  Definition loc_609 : location_info := LocationInfo file_0 422 9 422 14.
  Definition loc_610 : location_info := LocationInfo file_0 416 41 420 7.
  Definition loc_611 : location_info := LocationInfo file_0 417 8 417 34.
  Definition loc_612 : location_info := LocationInfo file_0 418 8 418 22.
  Definition loc_613 : location_info := LocationInfo file_0 419 8 419 35.
  Definition loc_614 : location_info := LocationInfo file_0 419 8 419 19.
  Definition loc_615 : location_info := LocationInfo file_0 419 8 419 13.
  Definition loc_616 : location_info := LocationInfo file_0 419 8 419 13.
  Definition loc_617 : location_info := LocationInfo file_0 419 22 419 34.
  Definition loc_618 : location_info := LocationInfo file_0 419 22 419 34.
  Definition loc_619 : location_info := LocationInfo file_0 418 8 418 13.
  Definition loc_620 : location_info := LocationInfo file_0 418 9 418 13.
  Definition loc_621 : location_info := LocationInfo file_0 418 9 418 13.
  Definition loc_622 : location_info := LocationInfo file_0 418 16 418 21.
  Definition loc_623 : location_info := LocationInfo file_0 418 16 418 21.
  Definition loc_624 : location_info := LocationInfo file_0 417 8 417 25.
  Definition loc_625 : location_info := LocationInfo file_0 417 8 417 13.
  Definition loc_626 : location_info := LocationInfo file_0 417 8 417 13.
  Definition loc_627 : location_info := LocationInfo file_0 417 28 417 33.
  Definition loc_628 : location_info := LocationInfo file_0 417 28 417 33.
  Definition loc_629 : location_info := LocationInfo file_0 417 29 417 33.
  Definition loc_630 : location_info := LocationInfo file_0 417 29 417 33.
  Definition loc_632 : location_info := LocationInfo file_0 416 10 416 39.
  Definition loc_633 : location_info := LocationInfo file_0 416 10 416 22.
  Definition loc_634 : location_info := LocationInfo file_0 416 10 416 22.
  Definition loc_635 : location_info := LocationInfo file_0 416 26 416 39.
  Definition loc_636 : location_info := LocationInfo file_0 416 26 416 39.
  Definition loc_637 : location_info := LocationInfo file_0 416 26 416 27.
  Definition loc_638 : location_info := LocationInfo file_0 416 26 416 27.
  Definition loc_639 : location_info := LocationInfo file_0 403 62 405 7.
  Definition loc_640 : location_info := LocationInfo file_0 404 8 404 27.
  Definition loc_641 : location_info := LocationInfo file_0 404 8 404 13.
  Definition loc_642 : location_info := LocationInfo file_0 404 9 404 13.
  Definition loc_643 : location_info := LocationInfo file_0 404 9 404 13.
  Definition loc_644 : location_info := LocationInfo file_0 404 16 404 26.
  Definition loc_645 : location_info := LocationInfo file_0 404 16 404 26.
  Definition loc_646 : location_info := LocationInfo file_0 405 13 410 7.
  Definition loc_647 : location_info := LocationInfo file_0 406 8 406 76.
  Definition loc_648 : location_info := LocationInfo file_0 407 8 407 78.
  Definition loc_649 : location_info := LocationInfo file_0 408 8 408 43.
  Definition loc_650 : location_info := LocationInfo file_0 409 8 409 26.
  Definition loc_651 : location_info := LocationInfo file_0 409 8 409 13.
  Definition loc_652 : location_info := LocationInfo file_0 409 9 409 13.
  Definition loc_653 : location_info := LocationInfo file_0 409 9 409 13.
  Definition loc_654 : location_info := LocationInfo file_0 409 16 409 25.
  Definition loc_655 : location_info := LocationInfo file_0 409 16 409 25.
  Definition loc_656 : location_info := LocationInfo file_0 408 8 408 29.
  Definition loc_657 : location_info := LocationInfo file_0 408 8 408 17.
  Definition loc_658 : location_info := LocationInfo file_0 408 8 408 17.
  Definition loc_659 : location_info := LocationInfo file_0 408 32 408 42.
  Definition loc_660 : location_info := LocationInfo file_0 408 32 408 42.
  Definition loc_661 : location_info := LocationInfo file_0 407 8 407 23.
  Definition loc_662 : location_info := LocationInfo file_0 407 8 407 17.
  Definition loc_663 : location_info := LocationInfo file_0 407 8 407 17.
  Definition loc_664 : location_info := LocationInfo file_0 407 26 407 77.
  Definition loc_665 : location_info := LocationInfo file_0 407 26 407 36.
  Definition loc_666 : location_info := LocationInfo file_0 407 26 407 36.
  Definition loc_667 : location_info := LocationInfo file_0 407 39 407 77.
  Definition loc_668 : location_info := LocationInfo file_0 407 40 407 52.
  Definition loc_669 : location_info := LocationInfo file_0 407 40 407 52.
  Definition loc_670 : location_info := LocationInfo file_0 407 55 407 76.
  Definition loc_671 : location_info := LocationInfo file_0 407 55 407 60.
  Definition loc_672 : location_info := LocationInfo file_0 407 55 407 60.
  Definition loc_673 : location_info := LocationInfo file_0 407 63 407 76.
  Definition loc_674 : location_info := LocationInfo file_0 407 63 407 76.
  Definition loc_675 : location_info := LocationInfo file_0 407 63 407 64.
  Definition loc_676 : location_info := LocationInfo file_0 407 63 407 64.
  Definition loc_677 : location_info := LocationInfo file_0 406 8 406 17.
  Definition loc_678 : location_info := LocationInfo file_0 406 20 406 75.
  Definition loc_679 : location_info := LocationInfo file_0 406 42 406 75.
  Definition loc_680 : location_info := LocationInfo file_0 406 43 406 48.
  Definition loc_681 : location_info := LocationInfo file_0 406 43 406 48.
  Definition loc_682 : location_info := LocationInfo file_0 406 51 406 74.
  Definition loc_683 : location_info := LocationInfo file_0 406 52 406 57.
  Definition loc_684 : location_info := LocationInfo file_0 406 52 406 57.
  Definition loc_685 : location_info := LocationInfo file_0 406 60 406 73.
  Definition loc_686 : location_info := LocationInfo file_0 406 60 406 73.
  Definition loc_687 : location_info := LocationInfo file_0 406 60 406 61.
  Definition loc_688 : location_info := LocationInfo file_0 406 60 406 61.
  Definition loc_689 : location_info := LocationInfo file_0 403 10 403 60.
  Definition loc_690 : location_info := LocationInfo file_0 403 10 403 46.
  Definition loc_691 : location_info := LocationInfo file_0 403 10 403 22.
  Definition loc_692 : location_info := LocationInfo file_0 403 10 403 22.
  Definition loc_693 : location_info := LocationInfo file_0 403 25 403 46.
  Definition loc_694 : location_info := LocationInfo file_0 403 25 403 30.
  Definition loc_695 : location_info := LocationInfo file_0 403 25 403 30.
  Definition loc_696 : location_info := LocationInfo file_0 403 33 403 46.
  Definition loc_697 : location_info := LocationInfo file_0 403 33 403 46.
  Definition loc_698 : location_info := LocationInfo file_0 403 33 403 34.
  Definition loc_699 : location_info := LocationInfo file_0 403 33 403 34.
  Definition loc_700 : location_info := LocationInfo file_0 403 50 403 60.
  Definition loc_701 : location_info := LocationInfo file_0 403 50 403 60.
  Definition loc_702 : location_info := LocationInfo file_0 401 6 401 11.
  Definition loc_703 : location_info := LocationInfo file_0 401 14 401 51.
  Definition loc_704 : location_info := LocationInfo file_0 401 14 401 36.
  Definition loc_705 : location_info := LocationInfo file_0 401 31 401 36.
  Definition loc_706 : location_info := LocationInfo file_0 401 31 401 36.
  Definition loc_707 : location_info := LocationInfo file_0 401 39 401 51.
  Definition loc_708 : location_info := LocationInfo file_0 401 39 401 51.
  Definition loc_709 : location_info := LocationInfo file_0 400 32 400 41.
  Definition loc_710 : location_info := LocationInfo file_0 400 33 400 41.
  Definition loc_711 : location_info := LocationInfo file_0 400 35 400 40.
  Definition loc_712 : location_info := LocationInfo file_0 400 35 400 40.
  Definition loc_713 : location_info := LocationInfo file_0 399 39 399 56.
  Definition loc_714 : location_info := LocationInfo file_0 399 39 399 56.
  Definition loc_715 : location_info := LocationInfo file_0 399 39 399 44.
  Definition loc_716 : location_info := LocationInfo file_0 399 39 399 44.
  Definition loc_719 : location_info := LocationInfo file_0 398 26 398 37.
  Definition loc_720 : location_info := LocationInfo file_0 398 26 398 37.
  Definition loc_721 : location_info := LocationInfo file_0 398 26 398 31.
  Definition loc_722 : location_info := LocationInfo file_0 398 26 398 31.
  Definition loc_726 : location_info := LocationInfo file_0 397 8 397 59.
  Definition loc_727 : location_info := LocationInfo file_0 397 8 397 44.
  Definition loc_728 : location_info := LocationInfo file_0 397 8 397 20.
  Definition loc_729 : location_info := LocationInfo file_0 397 8 397 20.
  Definition loc_730 : location_info := LocationInfo file_0 397 23 397 44.
  Definition loc_731 : location_info := LocationInfo file_0 397 23 397 28.
  Definition loc_732 : location_info := LocationInfo file_0 397 23 397 28.
  Definition loc_733 : location_info := LocationInfo file_0 397 31 397 44.
  Definition loc_734 : location_info := LocationInfo file_0 397 31 397 44.
  Definition loc_735 : location_info := LocationInfo file_0 397 31 397 32.
  Definition loc_736 : location_info := LocationInfo file_0 397 31 397 32.
  Definition loc_737 : location_info := LocationInfo file_0 397 48 397 59.
  Definition loc_738 : location_info := LocationInfo file_0 397 48 397 59.
  Definition loc_739 : location_info := LocationInfo file_0 397 48 397 53.
  Definition loc_740 : location_info := LocationInfo file_0 397 48 397 53.
  Definition loc_741 : location_info := LocationInfo file_0 390 4 390 20.
  Definition loc_742 : location_info := LocationInfo file_0 390 4 390 20.
  Definition loc_743 : location_info := LocationInfo file_0 390 21 390 43.
  Definition loc_744 : location_info := LocationInfo file_0 390 38 390 43.
  Definition loc_745 : location_info := LocationInfo file_0 390 38 390 43.
  Definition loc_746 : location_info := LocationInfo file_0 390 45 390 50.
  Definition loc_747 : location_info := LocationInfo file_0 390 45 390 50.
  Definition loc_748 : location_info := LocationInfo file_0 390 52 390 65.
  Definition loc_749 : location_info := LocationInfo file_0 390 53 390 65.
  Definition loc_750 : location_info := LocationInfo file_0 386 32 386 37.
  Definition loc_751 : location_info := LocationInfo file_0 386 32 386 37.
  Definition loc_752 : location_info := LocationInfo file_0 386 33 386 37.
  Definition loc_753 : location_info := LocationInfo file_0 386 33 386 37.
  Definition loc_756 : location_info := LocationInfo file_0 383 9 383 32.
  Definition loc_757 : location_info := LocationInfo file_0 383 9 383 14.
  Definition loc_758 : location_info := LocationInfo file_0 383 9 383 14.
  Definition loc_759 : location_info := LocationInfo file_0 383 10 383 14.
  Definition loc_760 : location_info := LocationInfo file_0 383 10 383 14.
  Definition loc_761 : location_info := LocationInfo file_0 383 18 383 32.
  Definition loc_762 : location_info := LocationInfo file_0 373 2 373 6.
  Definition loc_763 : location_info := LocationInfo file_0 373 9 373 30.
  Definition loc_764 : location_info := LocationInfo file_0 373 10 373 30.
  Definition loc_765 : location_info := LocationInfo file_0 373 10 373 19.
  Definition loc_766 : location_info := LocationInfo file_0 373 10 373 11.
  Definition loc_767 : location_info := LocationInfo file_0 373 10 373 11.
  Definition loc_768 : location_info := LocationInfo file_0 367 27 367 39.
  Definition loc_769 : location_info := LocationInfo file_0 367 28 367 39.
  Definition loc_770 : location_info := LocationInfo file_0 367 29 367 30.
  Definition loc_771 : location_info := LocationInfo file_0 367 29 367 30.
  Definition loc_772 : location_info := LocationInfo file_0 366 2 366 9.
  Definition loc_773 : location_info := LocationInfo file_0 366 2 366 9.
  Definition loc_774 : location_info := LocationInfo file_0 366 10 366 18.
  Definition loc_775 : location_info := LocationInfo file_0 366 11 366 18.
  Definition loc_776 : location_info := LocationInfo file_0 366 11 366 12.
  Definition loc_777 : location_info := LocationInfo file_0 366 11 366 12.
  Definition loc_778 : location_info := LocationInfo file_0 364 2 364 7.
  Definition loc_779 : location_info := LocationInfo file_0 364 2 364 24.
  Definition loc_780 : location_info := LocationInfo file_0 364 2 364 7.
  Definition loc_781 : location_info := LocationInfo file_0 364 2 364 7.
  Definition loc_782 : location_info := LocationInfo file_0 364 11 364 24.
  Definition loc_783 : location_info := LocationInfo file_0 364 11 364 24.
  Definition loc_784 : location_info := LocationInfo file_0 364 11 364 12.
  Definition loc_785 : location_info := LocationInfo file_0 364 11 364 12.
  Definition loc_786 : location_info := LocationInfo file_0 362 14 362 28.
  Definition loc_791 : location_info := LocationInfo file_0 457 2 457 66.
  Definition loc_792 : location_info := LocationInfo file_0 459 2 461 3.
  Definition loc_793 : location_info := LocationInfo file_0 463 2 463 18.
  Definition loc_794 : location_info := LocationInfo file_0 467 2 476 3.
  Definition loc_795 : location_info := LocationInfo file_0 478 2 478 24.
  Definition loc_796 : location_info := LocationInfo file_0 478 9 478 23.
  Definition loc_797 : location_info := LocationInfo file_0 467 2 476 3.
  Definition loc_798 : location_info := LocationInfo file_0 467 30 476 3.
  Definition loc_799 : location_info := LocationInfo file_0 468 4 468 62.
  Definition loc_800 : location_info := LocationInfo file_0 470 4 472 5.
  Definition loc_801 : location_info := LocationInfo file_0 474 4 474 20.
  Definition loc_802 : location_info := LocationInfo file_0 467 2 476 3.
  Definition loc_803 : location_info := LocationInfo file_0 467 2 476 3.
  Definition loc_804 : location_info := LocationInfo file_0 474 4 474 5.
  Definition loc_805 : location_info := LocationInfo file_0 474 8 474 19.
  Definition loc_806 : location_info := LocationInfo file_0 474 8 474 19.
  Definition loc_807 : location_info := LocationInfo file_0 474 8 474 9.
  Definition loc_808 : location_info := LocationInfo file_0 474 8 474 9.
  Definition loc_809 : location_info := LocationInfo file_0 470 31 472 5.
  Definition loc_810 : location_info := LocationInfo file_0 471 6 471 17.
  Definition loc_811 : location_info := LocationInfo file_0 471 13 471 16.
  Definition loc_812 : location_info := LocationInfo file_0 471 13 471 16.
  Definition loc_814 : location_info := LocationInfo file_0 470 8 470 29.
  Definition loc_815 : location_info := LocationInfo file_0 470 8 470 11.
  Definition loc_816 : location_info := LocationInfo file_0 470 8 470 11.
  Definition loc_817 : location_info := LocationInfo file_0 470 15 470 29.
  Definition loc_818 : location_info := LocationInfo file_0 468 4 468 7.
  Definition loc_819 : location_info := LocationInfo file_0 468 10 468 61.
  Definition loc_820 : location_info := LocationInfo file_0 468 10 468 44.
  Definition loc_821 : location_info := LocationInfo file_0 468 10 468 44.
  Definition loc_822 : location_info := LocationInfo file_0 468 45 468 46.
  Definition loc_823 : location_info := LocationInfo file_0 468 45 468 46.
  Definition loc_824 : location_info := LocationInfo file_0 468 48 468 53.
  Definition loc_825 : location_info := LocationInfo file_0 468 48 468 53.
  Definition loc_826 : location_info := LocationInfo file_0 468 55 468 60.
  Definition loc_827 : location_info := LocationInfo file_0 468 55 468 60.
  Definition loc_828 : location_info := LocationInfo file_0 467 9 467 28.
  Definition loc_829 : location_info := LocationInfo file_0 467 9 467 10.
  Definition loc_830 : location_info := LocationInfo file_0 467 9 467 10.
  Definition loc_831 : location_info := LocationInfo file_0 467 14 467 28.
  Definition loc_832 : location_info := LocationInfo file_0 463 2 463 3.
  Definition loc_833 : location_info := LocationInfo file_0 463 6 463 17.
  Definition loc_834 : location_info := LocationInfo file_0 463 6 463 17.
  Definition loc_835 : location_info := LocationInfo file_0 463 6 463 7.
  Definition loc_836 : location_info := LocationInfo file_0 463 6 463 7.
  Definition loc_837 : location_info := LocationInfo file_0 459 29 461 3.
  Definition loc_838 : location_info := LocationInfo file_0 460 4 460 15.
  Definition loc_839 : location_info := LocationInfo file_0 460 11 460 14.
  Definition loc_840 : location_info := LocationInfo file_0 460 11 460 14.
  Definition loc_842 : location_info := LocationInfo file_0 459 6 459 27.
  Definition loc_843 : location_info := LocationInfo file_0 459 6 459 9.
  Definition loc_844 : location_info := LocationInfo file_0 459 6 459 9.
  Definition loc_845 : location_info := LocationInfo file_0 459 13 459 27.
  Definition loc_846 : location_info := LocationInfo file_0 457 14 457 65.
  Definition loc_847 : location_info := LocationInfo file_0 457 14 457 48.
  Definition loc_848 : location_info := LocationInfo file_0 457 14 457 48.
  Definition loc_849 : location_info := LocationInfo file_0 457 49 457 50.
  Definition loc_850 : location_info := LocationInfo file_0 457 49 457 50.
  Definition loc_851 : location_info := LocationInfo file_0 457 52 457 57.
  Definition loc_852 : location_info := LocationInfo file_0 457 52 457 57.
  Definition loc_853 : location_info := LocationInfo file_0 457 59 457 64.
  Definition loc_854 : location_info := LocationInfo file_0 457 59 457 64.

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
      (Some "next_chunk", LPtr)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [mpool_entry]. *)
  Program Definition struct_mpool_entry := {|
    sl_members := [
      (Some "next", LPtr)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [mpool_locked_inner]. *)
  Program Definition struct_mpool_locked_inner := {|
    sl_members := [
      (Some "chunk_list", LPtr);
      (Some "entry_list", LPtr)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [mpool]. *)
  Program Definition struct_mpool := {|
    sl_members := [
      (Some "entry_size", it_layout size_t);
      (Some "lock", layout_of struct_spinlock);
      (None, mk_layout 7%nat 0%nat);
      (Some "locked", layout_of struct_mpool_locked_inner);
      (Some "fallback", LPtr)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [mpool_add_chunk]. *)
  Definition impl_mpool_add_chunk (sl_lock sl_unlock : loc): function := {|
    f_args := [
      ("p", LPtr);
      ("begin", LPtr);
      ("size", it_layout size_t)
    ];
    f_local_vars := [
      ("chunk", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        expr: (LocInfoE loc_62 (&(LocInfoE loc_63 ((LocInfoE loc_64 (!{LPtr} (LocInfoE loc_65 ("p")))) at{struct_mpool} "entry_size")))) ;
        locinfo: loc_57 ;
        if: LocInfoE loc_57 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_57 ((LocInfoE loc_58 (use{it_layout size_t} (LocInfoE loc_59 ("size")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_60 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_61 (i2v 0 i32)))))))
        then
        locinfo: loc_54 ;
          Goto "#2"
        else
        locinfo: loc_5 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_5 ;
        LocInfoE loc_50 ("chunk") <-{ LPtr }
          LocInfoE loc_51 (use{LPtr} (LocInfoE loc_52 ("begin"))) ;
        locinfo: loc_6 ;
        LocInfoE loc_45 ((LocInfoE loc_46 (!{LPtr} (LocInfoE loc_47 ("chunk")))) at{struct_mpool_chunk} "size") <-{ it_layout size_t }
          LocInfoE loc_48 (use{it_layout size_t} (LocInfoE loc_49 ("size"))) ;
        locinfo: loc_7 ;
        "_" <- LocInfoE loc_40 (sl_lock) with
          [ LocInfoE loc_41 (&(LocInfoE loc_42 ((LocInfoE loc_43 (!{LPtr} (LocInfoE loc_44 ("p")))) at{struct_mpool} "lock"))) ] ;
        locinfo: loc_8 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_35 (&(LocInfoE loc_36 ((LocInfoE loc_37 (!{LPtr} (LocInfoE loc_38 ("p")))) at{struct_mpool} "locked")))) ;
        locinfo: loc_10 ;
        LocInfoE loc_27 ((LocInfoE loc_28 (!{LPtr} (LocInfoE loc_29 ("chunk")))) at{struct_mpool_chunk} "next_chunk") <-{ LPtr }
          LocInfoE loc_30 (use{LPtr} (LocInfoE loc_31 ((LocInfoE loc_32 ((LocInfoE loc_33 (!{LPtr} (LocInfoE loc_34 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list"))) ;
        locinfo: loc_11 ;
        LocInfoE loc_21 ((LocInfoE loc_22 ((LocInfoE loc_23 (!{LPtr} (LocInfoE loc_24 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list") <-{ LPtr }
          LocInfoE loc_25 (use{LPtr} (LocInfoE loc_26 ("chunk"))) ;
        locinfo: loc_12 ;
        "_" <- LocInfoE loc_16 (sl_unlock) with
          [ LocInfoE loc_17 (AnnotExpr 1%nat LockA (LocInfoE loc_17 (&(LocInfoE loc_18 ((LocInfoE loc_19 (!{LPtr} (LocInfoE loc_20 ("p")))) at{struct_mpool} "lock"))))) ] ;
        locinfo: loc_13 ;
        Return (LocInfoE loc_14 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_14 (i2v 1 i32))))
      ]> $
      <[ "#2" :=
        locinfo: loc_54 ;
        Return (LocInfoE loc_55 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_55 (i2v 0 i32))))
      ]> $
      <[ "#3" :=
        locinfo: loc_5 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [mpool_free]. *)
  Definition impl_mpool_free (sl_lock sl_unlock : loc): function := {|
    f_args := [
      ("p", LPtr);
      ("ptr", LPtr)
    ];
    f_local_vars := [
      ("e", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "e" <-{ LPtr }
          LocInfoE loc_111 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_111 (use{LPtr} (LocInfoE loc_112 ("ptr"))))) ;
        locinfo: loc_69 ;
        expr: (LocInfoE loc_107 (&(LocInfoE loc_108 ((LocInfoE loc_109 (!{LPtr} (LocInfoE loc_110 ("p")))) at{struct_mpool} "entry_size")))) ;
        locinfo: loc_71 ;
        "_" <- LocInfoE loc_102 (sl_lock) with
          [ LocInfoE loc_103 (&(LocInfoE loc_104 ((LocInfoE loc_105 (!{LPtr} (LocInfoE loc_106 ("p")))) at{struct_mpool} "lock"))) ] ;
        locinfo: loc_72 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_97 (&(LocInfoE loc_98 ((LocInfoE loc_99 (!{LPtr} (LocInfoE loc_100 ("p")))) at{struct_mpool} "locked")))) ;
        locinfo: loc_74 ;
        LocInfoE loc_89 ((LocInfoE loc_90 (!{LPtr} (LocInfoE loc_91 ("e")))) at{struct_mpool_entry} "next") <-{ LPtr }
          LocInfoE loc_92 (use{LPtr} (LocInfoE loc_93 ((LocInfoE loc_94 ((LocInfoE loc_95 (!{LPtr} (LocInfoE loc_96 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list"))) ;
        locinfo: loc_75 ;
        LocInfoE loc_83 ((LocInfoE loc_84 ((LocInfoE loc_85 (!{LPtr} (LocInfoE loc_86 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list") <-{ LPtr }
          LocInfoE loc_87 (use{LPtr} (LocInfoE loc_88 ("e"))) ;
        locinfo: loc_76 ;
        "_" <- LocInfoE loc_78 (sl_unlock) with
          [ LocInfoE loc_79 (AnnotExpr 1%nat LockA (LocInfoE loc_79 (&(LocInfoE loc_80 ((LocInfoE loc_81 (!{LPtr} (LocInfoE loc_82 ("p")))) at{struct_mpool} "lock"))))) ] ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [mpool_init]. *)
  Definition impl_mpool_init (sl_init : loc): function := {|
    f_args := [
      ("p", LPtr);
      ("entry_size", it_layout size_t)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_117 ;
        LocInfoE loc_142 ((LocInfoE loc_143 (!{LPtr} (LocInfoE loc_144 ("p")))) at{struct_mpool} "entry_size") <-{ it_layout size_t }
          LocInfoE loc_145 (use{it_layout size_t} (LocInfoE loc_146 ("entry_size"))) ;
        locinfo: loc_118 ;
        LocInfoE loc_137 ((LocInfoE loc_138 ((LocInfoE loc_139 (!{LPtr} (LocInfoE loc_140 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list") <-{ LPtr }
          LocInfoE loc_141 (NULL) ;
        locinfo: loc_119 ;
        LocInfoE loc_132 ((LocInfoE loc_133 ((LocInfoE loc_134 (!{LPtr} (LocInfoE loc_135 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list") <-{ LPtr }
          LocInfoE loc_136 (NULL) ;
        locinfo: loc_120 ;
        LocInfoE loc_128 ((LocInfoE loc_129 (!{LPtr} (LocInfoE loc_130 ("p")))) at{struct_mpool} "fallback") <-{ LPtr }
          LocInfoE loc_131 (NULL) ;
        locinfo: loc_121 ;
        "_" <- LocInfoE loc_123 (sl_init) with
          [ LocInfoE loc_124 (&(LocInfoE loc_125 ((LocInfoE loc_126 (!{LPtr} (LocInfoE loc_127 ("p")))) at{struct_mpool} "lock"))) ] ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [mpool_init_from]. *)
  Definition impl_mpool_init_from (mpool_init sl_lock sl_unlock : loc): function := {|
    f_args := [
      ("p", LPtr);
      ("from", LPtr)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_149 ;
        "_" <- LocInfoE loc_211 (mpool_init) with
          [ LocInfoE loc_212 (use{LPtr} (LocInfoE loc_213 ("p"))) ;
          LocInfoE loc_214 (use{it_layout size_t} (LocInfoE loc_215 ((LocInfoE loc_216 (!{LPtr} (LocInfoE loc_217 ("from")))) at{struct_mpool} "entry_size"))) ] ;
        locinfo: loc_150 ;
        "_" <- LocInfoE loc_205 (sl_lock) with
          [ LocInfoE loc_206 (&(LocInfoE loc_207 ((LocInfoE loc_208 (!{LPtr} (LocInfoE loc_209 ("from")))) at{struct_mpool} "lock"))) ] ;
        locinfo: loc_151 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_200 (&(LocInfoE loc_201 ((LocInfoE loc_202 (!{LPtr} (LocInfoE loc_203 ("from")))) at{struct_mpool} "locked")))) ;
        locinfo: loc_153 ;
        LocInfoE loc_191 ((LocInfoE loc_192 ((LocInfoE loc_193 (!{LPtr} (LocInfoE loc_194 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list") <-{ LPtr }
          LocInfoE loc_195 (use{LPtr} (LocInfoE loc_196 ((LocInfoE loc_197 ((LocInfoE loc_198 (!{LPtr} (LocInfoE loc_199 ("from")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list"))) ;
        locinfo: loc_154 ;
        LocInfoE loc_182 ((LocInfoE loc_183 ((LocInfoE loc_184 (!{LPtr} (LocInfoE loc_185 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list") <-{ LPtr }
          LocInfoE loc_186 (use{LPtr} (LocInfoE loc_187 ((LocInfoE loc_188 ((LocInfoE loc_189 (!{LPtr} (LocInfoE loc_190 ("from")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list"))) ;
        locinfo: loc_155 ;
        LocInfoE loc_175 ((LocInfoE loc_176 (!{LPtr} (LocInfoE loc_177 ("p")))) at{struct_mpool} "fallback") <-{ LPtr }
          LocInfoE loc_178 (use{LPtr} (LocInfoE loc_179 ((LocInfoE loc_180 (!{LPtr} (LocInfoE loc_181 ("from")))) at{struct_mpool} "fallback"))) ;
        locinfo: loc_156 ;
        LocInfoE loc_170 ((LocInfoE loc_171 ((LocInfoE loc_172 (!{LPtr} (LocInfoE loc_173 ("from")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list") <-{ LPtr }
          LocInfoE loc_174 (NULL) ;
        locinfo: loc_157 ;
        LocInfoE loc_165 ((LocInfoE loc_166 ((LocInfoE loc_167 (!{LPtr} (LocInfoE loc_168 ("from")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list") <-{ LPtr }
          LocInfoE loc_169 (NULL) ;
        locinfo: loc_158 ;
        "_" <- LocInfoE loc_160 (sl_unlock) with
          [ LocInfoE loc_161 (AnnotExpr 1%nat LockA (LocInfoE loc_161 (&(LocInfoE loc_162 ((LocInfoE loc_163 (!{LPtr} (LocInfoE loc_164 ("from")))) at{struct_mpool} "lock"))))) ] ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [mpool_init_with_fallback]. *)
  Definition impl_mpool_init_with_fallback (mpool_init : loc): function := {|
    f_args := [
      ("p", LPtr);
      ("fallback", LPtr)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_220 ;
        "_" <- LocInfoE loc_228 (mpool_init) with
          [ LocInfoE loc_229 (use{LPtr} (LocInfoE loc_230 ("p"))) ;
          LocInfoE loc_231 (use{it_layout size_t} (LocInfoE loc_232 ((LocInfoE loc_233 (!{LPtr} (LocInfoE loc_234 ("fallback")))) at{struct_mpool} "entry_size"))) ] ;
        locinfo: loc_221 ;
        LocInfoE loc_222 ((LocInfoE loc_223 (!{LPtr} (LocInfoE loc_224 ("p")))) at{struct_mpool} "fallback") <-{ LPtr }
          LocInfoE loc_225 (use{LPtr} (LocInfoE loc_226 ("fallback"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [mpool_fini]. *)
  Definition impl_mpool_fini (mpool_add_chunk mpool_free : loc): function := {|
    f_args := [
      ("p", LPtr)
    ];
    f_local_vars := [
      ("size", it_layout size_t);
      ("ptr1", LPtr);
      ("ptr2", LPtr);
      ("entry", LPtr);
      ("chunk", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_340 ;
        if: LocInfoE loc_340 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_340 ((LocInfoE loc_341 (use{LPtr} (LocInfoE loc_342 ((LocInfoE loc_343 (!{LPtr} (LocInfoE loc_344 ("p")))) at{struct_mpool} "fallback")))) ={PtrOp, PtrOp} (LocInfoE loc_345 (NULL)))))
        then
        locinfo: loc_337 ;
          Goto "#8"
        else
        locinfo: loc_238 ;
          Goto "#9"
      ]> $
      <[ "#1" :=
        locinfo: loc_238 ;
        LocInfoE loc_330 ("entry") <-{ LPtr }
          LocInfoE loc_331 (use{LPtr} (LocInfoE loc_332 ((LocInfoE loc_333 ((LocInfoE loc_334 (!{LPtr} (LocInfoE loc_335 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list"))) ;
        locinfo: loc_239 ;
        LocInfoE loc_324 ("chunk") <-{ LPtr }
          LocInfoE loc_325 (use{LPtr} (LocInfoE loc_326 ((LocInfoE loc_327 ((LocInfoE loc_328 (!{LPtr} (LocInfoE loc_329 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list"))) ;
        locinfo: loc_240 ;
        Goto "#2"
      ]> $
      <[ "#2" :=
        locinfo: loc_320 ;
        if: LocInfoE loc_320 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_320 ((LocInfoE loc_321 (use{LPtr} (LocInfoE loc_322 ("entry")))) !={PtrOp, PtrOp} (LocInfoE loc_323 (NULL)))))
        then
        Goto "#3"
        else
        locinfo: loc_241 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        "ptr1" <-{ LPtr }
          LocInfoE loc_316 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_316 (use{LPtr} (LocInfoE loc_317 ("entry"))))) ;
        locinfo: loc_299 ;
        LocInfoE loc_311 ("entry") <-{ LPtr }
          LocInfoE loc_312 (use{LPtr} (LocInfoE loc_313 ((LocInfoE loc_314 (!{LPtr} (LocInfoE loc_315 ("entry")))) at{struct_mpool_entry} "next"))) ;
        locinfo: loc_300 ;
        "_" <- LocInfoE loc_304 (mpool_free) with
          [ LocInfoE loc_305 (use{LPtr} (LocInfoE loc_306 ((LocInfoE loc_307 (!{LPtr} (LocInfoE loc_308 ("p")))) at{struct_mpool} "fallback"))) ;
          LocInfoE loc_309 (use{LPtr} (LocInfoE loc_310 ("ptr1"))) ] ;
        locinfo: loc_301 ;
        Goto "continue9"
      ]> $
      <[ "#4" :=
        locinfo: loc_241 ;
        Goto "#5"
      ]> $
      <[ "#5" :=
        locinfo: loc_292 ;
        if: LocInfoE loc_292 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_292 ((LocInfoE loc_293 (use{LPtr} (LocInfoE loc_294 ("chunk")))) !={PtrOp, PtrOp} (LocInfoE loc_295 (NULL)))))
        then
        Goto "#6"
        else
        locinfo: loc_242 ;
          Goto "#7"
      ]> $
      <[ "#6" :=
        "ptr2" <-{ LPtr }
          LocInfoE loc_288 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_288 (use{LPtr} (LocInfoE loc_289 ("chunk"))))) ;
        "size" <-{ it_layout size_t }
          LocInfoE loc_282 (use{it_layout size_t} (LocInfoE loc_283 ((LocInfoE loc_284 (!{LPtr} (LocInfoE loc_285 ("chunk")))) at{struct_mpool_chunk} "size"))) ;
        locinfo: loc_263 ;
        LocInfoE loc_277 ("chunk") <-{ LPtr }
          LocInfoE loc_278 (use{LPtr} (LocInfoE loc_279 ((LocInfoE loc_280 (!{LPtr} (LocInfoE loc_281 ("chunk")))) at{struct_mpool_chunk} "next_chunk"))) ;
        locinfo: loc_264 ;
        "_" <- LocInfoE loc_268 (mpool_add_chunk) with
          [ LocInfoE loc_269 (use{LPtr} (LocInfoE loc_270 ((LocInfoE loc_271 (!{LPtr} (LocInfoE loc_272 ("p")))) at{struct_mpool} "fallback"))) ;
          LocInfoE loc_273 (use{LPtr} (LocInfoE loc_274 ("ptr2"))) ;
          LocInfoE loc_275 (use{it_layout size_t} (LocInfoE loc_276 ("size"))) ] ;
        locinfo: loc_265 ;
        Goto "continue11"
      ]> $
      <[ "#7" :=
        locinfo: loc_242 ;
        LocInfoE loc_254 ((LocInfoE loc_255 ((LocInfoE loc_256 (!{LPtr} (LocInfoE loc_257 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list") <-{ LPtr }
          LocInfoE loc_258 (NULL) ;
        locinfo: loc_243 ;
        LocInfoE loc_249 ((LocInfoE loc_250 ((LocInfoE loc_251 (!{LPtr} (LocInfoE loc_252 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list") <-{ LPtr }
          LocInfoE loc_253 (NULL) ;
        locinfo: loc_244 ;
        LocInfoE loc_245 ((LocInfoE loc_246 (!{LPtr} (LocInfoE loc_247 ("p")))) at{struct_mpool} "fallback") <-{ LPtr }
          LocInfoE loc_248 (NULL) ;
        Return (VOID)
      ]> $
      <[ "#8" :=
        locinfo: loc_337 ;
        Return (VOID)
      ]> $
      <[ "#9" :=
        locinfo: loc_238 ;
        Goto "#1"
      ]> $
      <[ "continue11" :=
        locinfo: loc_241 ;
        Goto "#5"
      ]> $
      <[ "continue9" :=
        locinfo: loc_240 ;
        Goto "#2"
      ]> $∅
    )%E
  |}.

  (* Definition of function [mpool_alloc_no_fallback]. *)
  Definition impl_mpool_alloc_no_fallback (sl_lock sl_unlock : loc): function := {|
    f_args := [
      ("p", LPtr)
    ];
    f_local_vars := [
      ("new_chunk", LPtr);
      ("entry", LPtr);
      ("ret", LPtr);
      ("chunk", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_348 ;
        "_" <- LocInfoE loc_481 (sl_lock) with
          [ LocInfoE loc_482 (&(LocInfoE loc_483 ((LocInfoE loc_484 (!{LPtr} (LocInfoE loc_485 ("p")))) at{struct_mpool} "lock"))) ] ;
        locinfo: loc_349 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_476 (&(LocInfoE loc_477 ((LocInfoE loc_478 (!{LPtr} (LocInfoE loc_479 ("p")))) at{struct_mpool} "locked")))) ;
        locinfo: loc_469 ;
        if: LocInfoE loc_469 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_469 ((LocInfoE loc_470 (use{LPtr} (LocInfoE loc_471 ((LocInfoE loc_472 ((LocInfoE loc_473 (!{LPtr} (LocInfoE loc_474 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list")))) !={PtrOp, PtrOp} (LocInfoE loc_475 (NULL)))))
        then
        Goto "#8"
        else
        locinfo: loc_352 ;
          Goto "#9"
      ]> $
      <[ "#1" :=
        locinfo: loc_352 ;
        LocInfoE loc_439 ("chunk") <-{ LPtr }
          LocInfoE loc_440 (use{LPtr} (LocInfoE loc_441 ((LocInfoE loc_442 ((LocInfoE loc_443 (!{LPtr} (LocInfoE loc_444 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list"))) ;
        locinfo: loc_435 ;
        if: LocInfoE loc_435 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_435 ((LocInfoE loc_436 (use{LPtr} (LocInfoE loc_437 ("chunk")))) ={PtrOp, PtrOp} (LocInfoE loc_438 (NULL)))))
        then
        locinfo: loc_430 ;
          Goto "#6"
        else
        locinfo: loc_420 ;
          Goto "#7"
      ]> $
      <[ "#2" :=
        locinfo: loc_420 ;
        if: LocInfoE loc_420 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_420 ((LocInfoE loc_421 (use{it_layout size_t} (LocInfoE loc_422 ((LocInfoE loc_423 (!{LPtr} (LocInfoE loc_424 ("p")))) at{struct_mpool} "entry_size")))) ≥{IntOp size_t, IntOp size_t} (LocInfoE loc_425 (use{it_layout size_t} (LocInfoE loc_426 ((LocInfoE loc_427 (!{LPtr} (LocInfoE loc_428 ("chunk")))) at{struct_mpool_chunk} "size")))))))
        then
        locinfo: loc_371 ;
          Goto "#4"
        else
        locinfo: loc_381 ;
          Goto "#5"
      ]> $
      <[ "#3" :=
        locinfo: loc_355 ;
        LocInfoE loc_367 ("ret") <-{ LPtr }
          LocInfoE loc_368 (use{LPtr} (LocInfoE loc_369 ("chunk"))) ;
        locinfo: loc_356 ;
        Goto "exit"
      ]> $
      <[ "#4" :=
        locinfo: loc_371 ;
        LocInfoE loc_372 ((LocInfoE loc_373 ((LocInfoE loc_374 (!{LPtr} (LocInfoE loc_375 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list") <-{ LPtr }
          LocInfoE loc_376 (use{LPtr} (LocInfoE loc_377 ((LocInfoE loc_378 (!{LPtr} (LocInfoE loc_379 ("chunk")))) at{struct_mpool_chunk} "next_chunk"))) ;
        locinfo: loc_355 ;
        Goto "#3"
      ]> $
      <[ "#5" :=
        locinfo: loc_381 ;
        LocInfoE loc_410 ("new_chunk") <-{ LPtr }
          LocInfoE loc_411 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_412 ((LocInfoE loc_413 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_414 (use{LPtr} (LocInfoE loc_415 ("chunk")))))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_416 (use{it_layout size_t} (LocInfoE loc_417 ((LocInfoE loc_418 (!{LPtr} (LocInfoE loc_419 ("p")))) at{struct_mpool} "entry_size"))))))) ;
        locinfo: loc_382 ;
        LocInfoE loc_403 ((LocInfoE loc_404 (!{LPtr} (LocInfoE loc_405 ("new_chunk")))) at{struct_mpool_chunk} "next_chunk") <-{ LPtr }
          LocInfoE loc_406 (use{LPtr} (LocInfoE loc_407 ((LocInfoE loc_408 (!{LPtr} (LocInfoE loc_409 ("chunk")))) at{struct_mpool_chunk} "next_chunk"))) ;
        locinfo: loc_383 ;
        LocInfoE loc_391 ((LocInfoE loc_392 (!{LPtr} (LocInfoE loc_393 ("new_chunk")))) at{struct_mpool_chunk} "size") <-{ it_layout size_t }
          LocInfoE loc_394 ((LocInfoE loc_395 (use{it_layout size_t} (LocInfoE loc_396 ((LocInfoE loc_397 (!{LPtr} (LocInfoE loc_398 ("chunk")))) at{struct_mpool_chunk} "size")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_399 (use{it_layout size_t} (LocInfoE loc_400 ((LocInfoE loc_401 (!{LPtr} (LocInfoE loc_402 ("p")))) at{struct_mpool} "entry_size"))))) ;
        locinfo: loc_384 ;
        LocInfoE loc_385 ((LocInfoE loc_386 ((LocInfoE loc_387 (!{LPtr} (LocInfoE loc_388 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list") <-{ LPtr }
          LocInfoE loc_389 (use{LPtr} (LocInfoE loc_390 ("new_chunk"))) ;
        locinfo: loc_355 ;
        Goto "#3"
      ]> $
      <[ "#6" :=
        locinfo: loc_430 ;
        LocInfoE loc_432 ("ret") <-{ LPtr } LocInfoE loc_433 (NULL) ;
        locinfo: loc_431 ;
        Goto "exit"
      ]> $
      <[ "#7" :=
        locinfo: loc_420 ;
        Goto "#2"
      ]> $
      <[ "#8" :=
        "entry" <-{ LPtr }
          LocInfoE loc_461 (use{LPtr} (LocInfoE loc_462 ((LocInfoE loc_463 ((LocInfoE loc_464 (!{LPtr} (LocInfoE loc_465 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list"))) ;
        locinfo: loc_447 ;
        LocInfoE loc_453 ((LocInfoE loc_454 ((LocInfoE loc_455 (!{LPtr} (LocInfoE loc_456 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list") <-{ LPtr }
          LocInfoE loc_457 (use{LPtr} (LocInfoE loc_458 ((LocInfoE loc_459 (!{LPtr} (LocInfoE loc_460 ("entry")))) at{struct_mpool_entry} "next"))) ;
        locinfo: loc_448 ;
        LocInfoE loc_450 ("ret") <-{ LPtr }
          LocInfoE loc_451 (use{LPtr} (LocInfoE loc_452 ("entry"))) ;
        locinfo: loc_449 ;
        Goto "exit"
      ]> $
      <[ "#9" :=
        locinfo: loc_352 ;
        Goto "#1"
      ]> $
      <[ "exit" :=
        locinfo: loc_357 ;
        "_" <- LocInfoE loc_362 (sl_unlock) with
          [ LocInfoE loc_363 (AnnotExpr 1%nat LockA (LocInfoE loc_363 (&(LocInfoE loc_364 ((LocInfoE loc_365 (!{LPtr} (LocInfoE loc_366 ("p")))) at{struct_mpool} "lock"))))) ] ;
        locinfo: loc_358 ;
        Return (LocInfoE loc_359 (use{LPtr} (LocInfoE loc_360 ("ret"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [mpool_alloc]. *)
  Definition impl_mpool_alloc (mpool_alloc_no_fallback : loc): function := {|
    f_args := [
      ("p", LPtr)
    ];
    f_local_vars := [
      ("ret", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_539 ;
        "$1" <- LocInfoE loc_541 (mpool_alloc_no_fallback) with
          [ LocInfoE loc_542 (use{LPtr} (LocInfoE loc_543 ("p"))) ] ;
        "ret" <-{ LPtr } LocInfoE loc_539 ("$1") ;
        locinfo: loc_535 ;
        if: LocInfoE loc_535 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_535 ((LocInfoE loc_536 (use{LPtr} (LocInfoE loc_537 ("ret")))) !={PtrOp, PtrOp} (LocInfoE loc_538 (NULL)))))
        then
        locinfo: loc_531 ;
          Goto "#8"
        else
        locinfo: loc_490 ;
          Goto "#9"
      ]> $
      <[ "#1" :=
        locinfo: loc_490 ;
        LocInfoE loc_525 ("p") <-{ LPtr }
          LocInfoE loc_526 (use{LPtr} (LocInfoE loc_527 ((LocInfoE loc_528 (!{LPtr} (LocInfoE loc_529 ("p")))) at{struct_mpool} "fallback"))) ;
        locinfo: loc_491 ;
        Goto "#2"
      ]> $
      <[ "#2" :=
        locinfo: loc_521 ;
        if: LocInfoE loc_521 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_521 ((LocInfoE loc_522 (use{LPtr} (LocInfoE loc_523 ("p")))) !={PtrOp, PtrOp} (LocInfoE loc_524 (NULL)))))
        then
        locinfo: loc_516 ;
          Goto "#3"
        else
        locinfo: loc_492 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_516 ;
        "$0" <- LocInfoE loc_518 (mpool_alloc_no_fallback) with
          [ LocInfoE loc_519 (use{LPtr} (LocInfoE loc_520 ("p"))) ] ;
        locinfo: loc_496 ;
        LocInfoE loc_515 ("ret") <-{ LPtr } LocInfoE loc_516 ("$0") ;
        locinfo: loc_511 ;
        if: LocInfoE loc_511 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_511 ((LocInfoE loc_512 (use{LPtr} (LocInfoE loc_513 ("ret")))) !={PtrOp, PtrOp} (LocInfoE loc_514 (NULL)))))
        then
        locinfo: loc_507 ;
          Goto "#6"
        else
        locinfo: loc_498 ;
          Goto "#7"
      ]> $
      <[ "#4" :=
        locinfo: loc_492 ;
        Return (LocInfoE loc_493 (NULL))
      ]> $
      <[ "#5" :=
        locinfo: loc_498 ;
        LocInfoE loc_501 ("p") <-{ LPtr }
          LocInfoE loc_502 (use{LPtr} (LocInfoE loc_503 ((LocInfoE loc_504 (!{LPtr} (LocInfoE loc_505 ("p")))) at{struct_mpool} "fallback"))) ;
        locinfo: loc_499 ;
        Goto "continue25"
      ]> $
      <[ "#6" :=
        locinfo: loc_507 ;
        Return (LocInfoE loc_508 (use{LPtr} (LocInfoE loc_509 ("ret"))))
      ]> $
      <[ "#7" :=
        locinfo: loc_498 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        locinfo: loc_531 ;
        Return (LocInfoE loc_532 (use{LPtr} (LocInfoE loc_533 ("ret"))))
      ]> $
      <[ "#9" :=
        locinfo: loc_490 ;
        Goto "#1"
      ]> $
      <[ "continue25" :=
        locinfo: loc_491 ;
        Goto "#2"
      ]> $∅
    )%E
  |}.

  (* Definition of function [mpool_alloc_contiguous_no_fallback]. *)
  Definition impl_mpool_alloc_contiguous_no_fallback (round_pointer_up sl_lock sl_unlock : loc): function := {|
    f_args := [
      ("p", LPtr);
      ("count", it_layout size_t);
      ("align", it_layout size_t)
    ];
    f_local_vars := [
      ("prev", LPtr);
      ("before_start", it_layout size_t);
      ("chunk_next", LPtr);
      ("new_chunk", LPtr);
      ("start", LPtr);
      ("ret", LPtr);
      ("chunk_size", it_layout size_t);
      ("chunk", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "ret" <-{ LPtr } LocInfoE loc_786 (NULL) ;
        locinfo: loc_549 ;
        LocInfoE loc_778 ("align") <-{ it_layout size_t }
          LocInfoE loc_779 ((LocInfoE loc_780 (use{it_layout size_t} (LocInfoE loc_781 ("align")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_782 (use{it_layout size_t} (LocInfoE loc_783 ((LocInfoE loc_784 (!{LPtr} (LocInfoE loc_785 ("p")))) at{struct_mpool} "entry_size"))))) ;
        locinfo: loc_550 ;
        "_" <- LocInfoE loc_773 (sl_lock) with
          [ LocInfoE loc_774 (&(LocInfoE loc_775 ((LocInfoE loc_776 (!{LPtr} (LocInfoE loc_777 ("p")))) at{struct_mpool} "lock"))) ] ;
        locinfo: loc_551 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_768 (&(LocInfoE loc_769 ((LocInfoE loc_770 (!{LPtr} (LocInfoE loc_771 ("p")))) at{struct_mpool} "locked")))) ;
        locinfo: loc_553 ;
        LocInfoE loc_762 ("prev") <-{ LPtr }
          LocInfoE loc_763 (&(LocInfoE loc_764 ((LocInfoE loc_765 ((LocInfoE loc_766 (!{LPtr} (LocInfoE loc_767 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list"))) ;
        locinfo: loc_554 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_756 ;
        if: LocInfoE loc_756 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_756 ((LocInfoE loc_757 (use{LPtr} (LocInfoE loc_759 (!{LPtr} (LocInfoE loc_760 ("prev")))))) !={PtrOp, PtrOp} (LocInfoE loc_761 (NULL)))))
        then
        Goto "#2"
        else
        locinfo: loc_555 ;
          Goto "#3"
      ]> $
      <[ "#10" :=
        locinfo: loc_640 ;
        LocInfoE loc_642 (!{LPtr} (LocInfoE loc_643 ("prev"))) <-{ LPtr }
          LocInfoE loc_644 (use{LPtr} (LocInfoE loc_645 ("chunk_next"))) ;
        locinfo: loc_632 ;
        Goto "#6"
      ]> $
      <[ "#11" :=
        locinfo: loc_647 ;
        LocInfoE loc_677 ("new_chunk") <-{ LPtr }
          LocInfoE loc_678 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_679 ((LocInfoE loc_680 (use{LPtr} (LocInfoE loc_681 ("start")))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_682 ((LocInfoE loc_683 (use{it_layout size_t} (LocInfoE loc_684 ("count")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_685 (use{it_layout size_t} (LocInfoE loc_686 ((LocInfoE loc_687 (!{LPtr} (LocInfoE loc_688 ("p")))) at{struct_mpool} "entry_size"))))))))) ;
        locinfo: loc_648 ;
        LocInfoE loc_661 ((LocInfoE loc_662 (!{LPtr} (LocInfoE loc_663 ("new_chunk")))) at{struct_mpool_chunk} "size") <-{ it_layout size_t }
          LocInfoE loc_664 ((LocInfoE loc_665 (use{it_layout size_t} (LocInfoE loc_666 ("chunk_size")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_667 ((LocInfoE loc_668 (use{it_layout size_t} (LocInfoE loc_669 ("before_start")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_670 ((LocInfoE loc_671 (use{it_layout size_t} (LocInfoE loc_672 ("count")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_673 (use{it_layout size_t} (LocInfoE loc_674 ((LocInfoE loc_675 (!{LPtr} (LocInfoE loc_676 ("p")))) at{struct_mpool} "entry_size"))))))))) ;
        locinfo: loc_649 ;
        LocInfoE loc_656 ((LocInfoE loc_657 (!{LPtr} (LocInfoE loc_658 ("new_chunk")))) at{struct_mpool_chunk} "next_chunk") <-{ LPtr }
          LocInfoE loc_659 (use{LPtr} (LocInfoE loc_660 ("chunk_next"))) ;
        locinfo: loc_650 ;
        LocInfoE loc_652 (!{LPtr} (LocInfoE loc_653 ("prev"))) <-{ LPtr }
          LocInfoE loc_654 (use{LPtr} (LocInfoE loc_655 ("new_chunk"))) ;
        locinfo: loc_632 ;
        Goto "#6"
      ]> $
      <[ "#12" :=
        locinfo: loc_576 ;
        Goto "#4"
      ]> $
      <[ "#2" :=
        "chunk" <-{ LPtr }
          LocInfoE loc_750 (use{LPtr} (LocInfoE loc_752 (!{LPtr} (LocInfoE loc_753 ("prev"))))) ;
        locinfo: loc_574 ;
        "_" <- LocInfoE loc_742 (round_pointer_up) with
          [ LocInfoE loc_743 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_744 (use{LPtr} (LocInfoE loc_745 ("chunk"))))) ;
          LocInfoE loc_746 (use{it_layout size_t} (LocInfoE loc_747 ("align"))) ;
          LocInfoE loc_748 (&(LocInfoE loc_749 ("before_start"))) ] ;
        locinfo: loc_726 ;
        if: LocInfoE loc_726 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_726 ((LocInfoE loc_727 ((LocInfoE loc_728 (use{it_layout size_t} (LocInfoE loc_729 ("before_start")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_730 ((LocInfoE loc_731 (use{it_layout size_t} (LocInfoE loc_732 ("count")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_733 (use{it_layout size_t} (LocInfoE loc_734 ((LocInfoE loc_735 (!{LPtr} (LocInfoE loc_736 ("p")))) at{struct_mpool} "entry_size")))))))) ≤{IntOp size_t, IntOp size_t} (LocInfoE loc_737 (use{it_layout size_t} (LocInfoE loc_738 ((LocInfoE loc_739 (!{LPtr} (LocInfoE loc_740 ("chunk")))) at{struct_mpool_chunk} "size")))))))
        then
        Goto "#5"
        else
        locinfo: loc_576 ;
          Goto "#12"
      ]> $
      <[ "#3" :=
        locinfo: loc_555 ;
        expr: (LocInfoE loc_567 (&(LocInfoE loc_569 (!{LPtr} (LocInfoE loc_570 ("prev")))))) ;
        locinfo: loc_557 ;
        "_" <- LocInfoE loc_562 (sl_unlock) with
          [ LocInfoE loc_563 (AnnotExpr 1%nat LockA (LocInfoE loc_563 (&(LocInfoE loc_564 ((LocInfoE loc_565 (!{LPtr} (LocInfoE loc_566 ("p")))) at{struct_mpool} "lock"))))) ] ;
        locinfo: loc_558 ;
        Return (LocInfoE loc_559 (use{LPtr} (LocInfoE loc_560 ("ret"))))
      ]> $
      <[ "#4" :=
        locinfo: loc_576 ;
        LocInfoE loc_579 ("prev") <-{ LPtr }
          LocInfoE loc_580 (&(LocInfoE loc_581 ((LocInfoE loc_582 (!{LPtr} (LocInfoE loc_583 ("chunk")))) at{struct_mpool_chunk} "next_chunk"))) ;
        locinfo: loc_577 ;
        Goto "continue32"
      ]> $
      <[ "#5" :=
        "chunk_size" <-{ it_layout size_t }
          LocInfoE loc_719 (use{it_layout size_t} (LocInfoE loc_720 ((LocInfoE loc_721 (!{LPtr} (LocInfoE loc_722 ("chunk")))) at{struct_mpool_chunk} "size"))) ;
        "chunk_next" <-{ LPtr }
          LocInfoE loc_713 (use{LPtr} (LocInfoE loc_714 ((LocInfoE loc_715 (!{LPtr} (LocInfoE loc_716 ("chunk")))) at{struct_mpool_chunk} "next_chunk"))) ;
        locinfo: loc_587 ;
        annot: (ToUninit) ;
        expr: (LocInfoE loc_709 (&(LocInfoE loc_711 (!{LPtr} (LocInfoE loc_712 ("chunk")))))) ;
        locinfo: loc_589 ;
        LocInfoE loc_702 ("start") <-{ LPtr }
          LocInfoE loc_703 ((LocInfoE loc_704 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_705 (use{LPtr} (LocInfoE loc_706 ("chunk")))))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_707 (use{it_layout size_t} (LocInfoE loc_708 ("before_start"))))) ;
        locinfo: loc_689 ;
        if: LocInfoE loc_689 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_689 ((LocInfoE loc_690 ((LocInfoE loc_691 (use{it_layout size_t} (LocInfoE loc_692 ("before_start")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_693 ((LocInfoE loc_694 (use{it_layout size_t} (LocInfoE loc_695 ("count")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_696 (use{it_layout size_t} (LocInfoE loc_697 ((LocInfoE loc_698 (!{LPtr} (LocInfoE loc_699 ("p")))) at{struct_mpool} "entry_size")))))))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_700 (use{it_layout size_t} (LocInfoE loc_701 ("chunk_size")))))))
        then
        locinfo: loc_640 ;
          Goto "#10"
        else
        locinfo: loc_647 ;
          Goto "#11"
      ]> $
      <[ "#6" :=
        locinfo: loc_632 ;
        if: LocInfoE loc_632 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_632 ((LocInfoE loc_633 (use{it_layout size_t} (LocInfoE loc_634 ("before_start")))) ≥{IntOp size_t, IntOp size_t} (LocInfoE loc_635 (use{it_layout size_t} (LocInfoE loc_636 ((LocInfoE loc_637 (!{LPtr} (LocInfoE loc_638 ("p")))) at{struct_mpool} "entry_size")))))))
        then
        locinfo: loc_611 ;
          Goto "#8"
        else
        locinfo: loc_592 ;
          Goto "#9"
      ]> $
      <[ "#7" :=
        locinfo: loc_592 ;
        expr: (LocInfoE loc_606 (&(LocInfoE loc_608 (!{LPtr} (LocInfoE loc_609 ("chunk")))))) ;
        locinfo: loc_594 ;
        annot: (UninitStrengthenAlign) ;
        expr: (LocInfoE loc_602 (&(LocInfoE loc_604 (!{LPtr} (LocInfoE loc_605 ("start")))))) ;
        locinfo: loc_596 ;
        LocInfoE loc_598 ("ret") <-{ LPtr }
          LocInfoE loc_599 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_600 (use{LPtr} (LocInfoE loc_601 ("start"))))) ;
        locinfo: loc_555 ;
        Goto "#3"
      ]> $
      <[ "#8" :=
        locinfo: loc_611 ;
        LocInfoE loc_624 ((LocInfoE loc_625 (!{LPtr} (LocInfoE loc_626 ("chunk")))) at{struct_mpool_chunk} "next_chunk") <-{ LPtr }
          LocInfoE loc_627 (use{LPtr} (LocInfoE loc_629 (!{LPtr} (LocInfoE loc_630 ("prev"))))) ;
        locinfo: loc_612 ;
        LocInfoE loc_620 (!{LPtr} (LocInfoE loc_621 ("prev"))) <-{ LPtr }
          LocInfoE loc_622 (use{LPtr} (LocInfoE loc_623 ("chunk"))) ;
        locinfo: loc_613 ;
        LocInfoE loc_614 ((LocInfoE loc_615 (!{LPtr} (LocInfoE loc_616 ("chunk")))) at{struct_mpool_chunk} "size") <-{ it_layout size_t }
          LocInfoE loc_617 (use{it_layout size_t} (LocInfoE loc_618 ("before_start"))) ;
        locinfo: loc_592 ;
        Goto "#7"
      ]> $
      <[ "#9" :=
        locinfo: loc_592 ;
        Goto "#7"
      ]> $
      <[ "continue32" :=
        locinfo: loc_554 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [mpool_alloc_contiguous]. *)
  Definition impl_mpool_alloc_contiguous (mpool_alloc_contiguous_no_fallback : loc): function := {|
    f_args := [
      ("p", LPtr);
      ("count", it_layout size_t);
      ("align", it_layout size_t)
    ];
    f_local_vars := [
      ("ret", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_846 ;
        "$1" <- LocInfoE loc_848 (mpool_alloc_contiguous_no_fallback) with
          [ LocInfoE loc_849 (use{LPtr} (LocInfoE loc_850 ("p"))) ;
          LocInfoE loc_851 (use{it_layout size_t} (LocInfoE loc_852 ("count"))) ;
          LocInfoE loc_853 (use{it_layout size_t} (LocInfoE loc_854 ("align"))) ] ;
        "ret" <-{ LPtr } LocInfoE loc_846 ("$1") ;
        locinfo: loc_842 ;
        if: LocInfoE loc_842 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_842 ((LocInfoE loc_843 (use{LPtr} (LocInfoE loc_844 ("ret")))) !={PtrOp, PtrOp} (LocInfoE loc_845 (NULL)))))
        then
        locinfo: loc_838 ;
          Goto "#8"
        else
        locinfo: loc_793 ;
          Goto "#9"
      ]> $
      <[ "#1" :=
        locinfo: loc_793 ;
        LocInfoE loc_832 ("p") <-{ LPtr }
          LocInfoE loc_833 (use{LPtr} (LocInfoE loc_834 ((LocInfoE loc_835 (!{LPtr} (LocInfoE loc_836 ("p")))) at{struct_mpool} "fallback"))) ;
        locinfo: loc_794 ;
        Goto "#2"
      ]> $
      <[ "#2" :=
        locinfo: loc_828 ;
        if: LocInfoE loc_828 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_828 ((LocInfoE loc_829 (use{LPtr} (LocInfoE loc_830 ("p")))) !={PtrOp, PtrOp} (LocInfoE loc_831 (NULL)))))
        then
        locinfo: loc_819 ;
          Goto "#3"
        else
        locinfo: loc_795 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_819 ;
        "$0" <- LocInfoE loc_821 (mpool_alloc_contiguous_no_fallback) with
          [ LocInfoE loc_822 (use{LPtr} (LocInfoE loc_823 ("p"))) ;
          LocInfoE loc_824 (use{it_layout size_t} (LocInfoE loc_825 ("count"))) ;
          LocInfoE loc_826 (use{it_layout size_t} (LocInfoE loc_827 ("align"))) ] ;
        locinfo: loc_799 ;
        LocInfoE loc_818 ("ret") <-{ LPtr } LocInfoE loc_819 ("$0") ;
        locinfo: loc_814 ;
        if: LocInfoE loc_814 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_814 ((LocInfoE loc_815 (use{LPtr} (LocInfoE loc_816 ("ret")))) !={PtrOp, PtrOp} (LocInfoE loc_817 (NULL)))))
        then
        locinfo: loc_810 ;
          Goto "#6"
        else
        locinfo: loc_801 ;
          Goto "#7"
      ]> $
      <[ "#4" :=
        locinfo: loc_795 ;
        Return (LocInfoE loc_796 (NULL))
      ]> $
      <[ "#5" :=
        locinfo: loc_801 ;
        LocInfoE loc_804 ("p") <-{ LPtr }
          LocInfoE loc_805 (use{LPtr} (LocInfoE loc_806 ((LocInfoE loc_807 (!{LPtr} (LocInfoE loc_808 ("p")))) at{struct_mpool} "fallback"))) ;
        locinfo: loc_802 ;
        Goto "continue41"
      ]> $
      <[ "#6" :=
        locinfo: loc_810 ;
        Return (LocInfoE loc_811 (use{LPtr} (LocInfoE loc_812 ("ret"))))
      ]> $
      <[ "#7" :=
        locinfo: loc_801 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        locinfo: loc_838 ;
        Return (LocInfoE loc_839 (use{LPtr} (LocInfoE loc_840 ("ret"))))
      ]> $
      <[ "#9" :=
        locinfo: loc_793 ;
        Goto "#1"
      ]> $
      <[ "continue41" :=
        locinfo: loc_794 ;
        Goto "#2"
      ]> $∅
    )%E
  |}.
End code.
