From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
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
  Definition loc_68 : location_info := LocationInfo file_0 336 2 336 30.
  Definition loc_69 : location_info := LocationInfo file_0 339 2 339 20.
  Definition loc_70 : location_info := LocationInfo file_0 340 2 340 40.
  Definition loc_71 : location_info := LocationInfo file_0 340 40 340 3.
  Definition loc_72 : location_info := LocationInfo file_0 341 2 341 33.
  Definition loc_73 : location_info := LocationInfo file_0 342 2 342 27.
  Definition loc_74 : location_info := LocationInfo file_0 343 2 343 22.
  Definition loc_75 : location_info := LocationInfo file_0 343 2 343 11.
  Definition loc_76 : location_info := LocationInfo file_0 343 2 343 11.
  Definition loc_77 : location_info := LocationInfo file_0 343 12 343 20.
  Definition loc_78 : location_info := LocationInfo file_0 343 13 343 20.
  Definition loc_79 : location_info := LocationInfo file_0 343 13 343 14.
  Definition loc_80 : location_info := LocationInfo file_0 343 13 343 14.
  Definition loc_81 : location_info := LocationInfo file_0 342 2 342 22.
  Definition loc_82 : location_info := LocationInfo file_0 342 2 342 11.
  Definition loc_83 : location_info := LocationInfo file_0 342 2 342 3.
  Definition loc_84 : location_info := LocationInfo file_0 342 2 342 3.
  Definition loc_85 : location_info := LocationInfo file_0 342 25 342 26.
  Definition loc_86 : location_info := LocationInfo file_0 342 25 342 26.
  Definition loc_87 : location_info := LocationInfo file_0 341 2 341 9.
  Definition loc_88 : location_info := LocationInfo file_0 341 2 341 3.
  Definition loc_89 : location_info := LocationInfo file_0 341 2 341 3.
  Definition loc_90 : location_info := LocationInfo file_0 341 12 341 32.
  Definition loc_91 : location_info := LocationInfo file_0 341 12 341 32.
  Definition loc_92 : location_info := LocationInfo file_0 341 12 341 21.
  Definition loc_93 : location_info := LocationInfo file_0 341 12 341 13.
  Definition loc_94 : location_info := LocationInfo file_0 341 12 341 13.
  Definition loc_95 : location_info := LocationInfo file_0 340 27 340 39.
  Definition loc_96 : location_info := LocationInfo file_0 340 28 340 39.
  Definition loc_97 : location_info := LocationInfo file_0 340 29 340 30.
  Definition loc_98 : location_info := LocationInfo file_0 340 29 340 30.
  Definition loc_99 : location_info := LocationInfo file_0 339 2 339 9.
  Definition loc_100 : location_info := LocationInfo file_0 339 2 339 9.
  Definition loc_101 : location_info := LocationInfo file_0 339 10 339 18.
  Definition loc_102 : location_info := LocationInfo file_0 339 11 339 18.
  Definition loc_103 : location_info := LocationInfo file_0 339 11 339 12.
  Definition loc_104 : location_info := LocationInfo file_0 339 11 339 12.
  Definition loc_105 : location_info := LocationInfo file_0 336 26 336 29.
  Definition loc_106 : location_info := LocationInfo file_0 336 26 336 29.
  Definition loc_111 : location_info := LocationInfo file_0 111 2 111 29.
  Definition loc_112 : location_info := LocationInfo file_0 112 2 112 40.
  Definition loc_113 : location_info := LocationInfo file_0 113 2 113 40.
  Definition loc_114 : location_info := LocationInfo file_0 114 2 114 31.
  Definition loc_115 : location_info := LocationInfo file_0 115 2 115 20.
  Definition loc_116 : location_info := LocationInfo file_0 115 2 115 9.
  Definition loc_117 : location_info := LocationInfo file_0 115 2 115 9.
  Definition loc_118 : location_info := LocationInfo file_0 115 10 115 18.
  Definition loc_119 : location_info := LocationInfo file_0 115 11 115 18.
  Definition loc_120 : location_info := LocationInfo file_0 115 11 115 12.
  Definition loc_121 : location_info := LocationInfo file_0 115 11 115 12.
  Definition loc_122 : location_info := LocationInfo file_0 114 2 114 13.
  Definition loc_123 : location_info := LocationInfo file_0 114 2 114 3.
  Definition loc_124 : location_info := LocationInfo file_0 114 2 114 3.
  Definition loc_125 : location_info := LocationInfo file_0 114 16 114 30.
  Definition loc_126 : location_info := LocationInfo file_0 113 2 113 22.
  Definition loc_127 : location_info := LocationInfo file_0 113 2 113 11.
  Definition loc_128 : location_info := LocationInfo file_0 113 2 113 3.
  Definition loc_129 : location_info := LocationInfo file_0 113 2 113 3.
  Definition loc_130 : location_info := LocationInfo file_0 113 25 113 39.
  Definition loc_131 : location_info := LocationInfo file_0 112 2 112 22.
  Definition loc_132 : location_info := LocationInfo file_0 112 2 112 11.
  Definition loc_133 : location_info := LocationInfo file_0 112 2 112 3.
  Definition loc_134 : location_info := LocationInfo file_0 112 2 112 3.
  Definition loc_135 : location_info := LocationInfo file_0 112 25 112 39.
  Definition loc_136 : location_info := LocationInfo file_0 111 2 111 15.
  Definition loc_137 : location_info := LocationInfo file_0 111 2 111 3.
  Definition loc_138 : location_info := LocationInfo file_0 111 2 111 3.
  Definition loc_139 : location_info := LocationInfo file_0 111 18 111 28.
  Definition loc_140 : location_info := LocationInfo file_0 111 18 111 28.
  Definition loc_143 : location_info := LocationInfo file_0 130 2 130 34.
  Definition loc_144 : location_info := LocationInfo file_0 132 2 132 23.
  Definition loc_145 : location_info := LocationInfo file_0 133 2 133 43.
  Definition loc_146 : location_info := LocationInfo file_0 133 43 133 3.
  Definition loc_147 : location_info := LocationInfo file_0 135 2 135 49.
  Definition loc_148 : location_info := LocationInfo file_0 136 2 136 49.
  Definition loc_149 : location_info := LocationInfo file_0 137 2 137 31.
  Definition loc_150 : location_info := LocationInfo file_0 139 2 139 43.
  Definition loc_151 : location_info := LocationInfo file_0 140 2 140 43.
  Definition loc_152 : location_info := LocationInfo file_0 143 2 143 25.
  Definition loc_153 : location_info := LocationInfo file_0 143 2 143 11.
  Definition loc_154 : location_info := LocationInfo file_0 143 2 143 11.
  Definition loc_155 : location_info := LocationInfo file_0 143 12 143 23.
  Definition loc_156 : location_info := LocationInfo file_0 143 13 143 23.
  Definition loc_157 : location_info := LocationInfo file_0 143 13 143 17.
  Definition loc_158 : location_info := LocationInfo file_0 143 13 143 17.
  Definition loc_159 : location_info := LocationInfo file_0 140 2 140 25.
  Definition loc_160 : location_info := LocationInfo file_0 140 2 140 14.
  Definition loc_161 : location_info := LocationInfo file_0 140 2 140 6.
  Definition loc_162 : location_info := LocationInfo file_0 140 2 140 6.
  Definition loc_163 : location_info := LocationInfo file_0 140 28 140 42.
  Definition loc_164 : location_info := LocationInfo file_0 139 2 139 25.
  Definition loc_165 : location_info := LocationInfo file_0 139 2 139 14.
  Definition loc_166 : location_info := LocationInfo file_0 139 2 139 6.
  Definition loc_167 : location_info := LocationInfo file_0 139 2 139 6.
  Definition loc_168 : location_info := LocationInfo file_0 139 28 139 42.
  Definition loc_169 : location_info := LocationInfo file_0 137 2 137 13.
  Definition loc_170 : location_info := LocationInfo file_0 137 2 137 3.
  Definition loc_171 : location_info := LocationInfo file_0 137 2 137 3.
  Definition loc_172 : location_info := LocationInfo file_0 137 16 137 30.
  Definition loc_173 : location_info := LocationInfo file_0 137 16 137 30.
  Definition loc_174 : location_info := LocationInfo file_0 137 16 137 20.
  Definition loc_175 : location_info := LocationInfo file_0 137 16 137 20.
  Definition loc_176 : location_info := LocationInfo file_0 136 2 136 22.
  Definition loc_177 : location_info := LocationInfo file_0 136 2 136 11.
  Definition loc_178 : location_info := LocationInfo file_0 136 2 136 3.
  Definition loc_179 : location_info := LocationInfo file_0 136 2 136 3.
  Definition loc_180 : location_info := LocationInfo file_0 136 25 136 48.
  Definition loc_181 : location_info := LocationInfo file_0 136 25 136 48.
  Definition loc_182 : location_info := LocationInfo file_0 136 25 136 37.
  Definition loc_183 : location_info := LocationInfo file_0 136 25 136 29.
  Definition loc_184 : location_info := LocationInfo file_0 136 25 136 29.
  Definition loc_185 : location_info := LocationInfo file_0 135 2 135 22.
  Definition loc_186 : location_info := LocationInfo file_0 135 2 135 11.
  Definition loc_187 : location_info := LocationInfo file_0 135 2 135 3.
  Definition loc_188 : location_info := LocationInfo file_0 135 2 135 3.
  Definition loc_189 : location_info := LocationInfo file_0 135 25 135 48.
  Definition loc_190 : location_info := LocationInfo file_0 135 25 135 48.
  Definition loc_191 : location_info := LocationInfo file_0 135 25 135 37.
  Definition loc_192 : location_info := LocationInfo file_0 135 25 135 29.
  Definition loc_193 : location_info := LocationInfo file_0 135 25 135 29.
  Definition loc_194 : location_info := LocationInfo file_0 133 27 133 42.
  Definition loc_195 : location_info := LocationInfo file_0 133 28 133 42.
  Definition loc_196 : location_info := LocationInfo file_0 133 29 133 33.
  Definition loc_197 : location_info := LocationInfo file_0 133 29 133 33.
  Definition loc_198 : location_info := LocationInfo file_0 132 2 132 9.
  Definition loc_199 : location_info := LocationInfo file_0 132 2 132 9.
  Definition loc_200 : location_info := LocationInfo file_0 132 10 132 21.
  Definition loc_201 : location_info := LocationInfo file_0 132 11 132 21.
  Definition loc_202 : location_info := LocationInfo file_0 132 11 132 15.
  Definition loc_203 : location_info := LocationInfo file_0 132 11 132 15.
  Definition loc_204 : location_info := LocationInfo file_0 130 2 130 12.
  Definition loc_205 : location_info := LocationInfo file_0 130 2 130 12.
  Definition loc_206 : location_info := LocationInfo file_0 130 13 130 14.
  Definition loc_207 : location_info := LocationInfo file_0 130 13 130 14.
  Definition loc_208 : location_info := LocationInfo file_0 130 16 130 32.
  Definition loc_209 : location_info := LocationInfo file_0 130 16 130 32.
  Definition loc_210 : location_info := LocationInfo file_0 130 16 130 20.
  Definition loc_211 : location_info := LocationInfo file_0 130 16 130 20.
  Definition loc_214 : location_info := LocationInfo file_0 155 2 155 38.
  Definition loc_215 : location_info := LocationInfo file_0 156 2 156 25.
  Definition loc_216 : location_info := LocationInfo file_0 156 2 156 13.
  Definition loc_217 : location_info := LocationInfo file_0 156 2 156 3.
  Definition loc_218 : location_info := LocationInfo file_0 156 2 156 3.
  Definition loc_219 : location_info := LocationInfo file_0 156 16 156 24.
  Definition loc_220 : location_info := LocationInfo file_0 156 16 156 24.
  Definition loc_221 : location_info := LocationInfo file_0 155 2 155 12.
  Definition loc_222 : location_info := LocationInfo file_0 155 2 155 12.
  Definition loc_223 : location_info := LocationInfo file_0 155 13 155 14.
  Definition loc_224 : location_info := LocationInfo file_0 155 13 155 14.
  Definition loc_225 : location_info := LocationInfo file_0 155 16 155 36.
  Definition loc_226 : location_info := LocationInfo file_0 155 16 155 36.
  Definition loc_227 : location_info := LocationInfo file_0 155 16 155 24.
  Definition loc_228 : location_info := LocationInfo file_0 155 16 155 24.
  Definition loc_231 : location_info := LocationInfo file_0 170 2 172 3.
  Definition loc_232 : location_info := LocationInfo file_0 174 2 174 31.
  Definition loc_233 : location_info := LocationInfo file_0 175 2 175 31.
  Definition loc_234 : location_info := LocationInfo file_0 180 2 184 3.
  Definition loc_235 : location_info := LocationInfo file_0 190 2 196 3.
  Definition loc_236 : location_info := LocationInfo file_0 198 2 198 40.
  Definition loc_237 : location_info := LocationInfo file_0 199 2 199 40.
  Definition loc_238 : location_info := LocationInfo file_0 200 2 200 31.
  Definition loc_239 : location_info := LocationInfo file_0 200 2 200 13.
  Definition loc_240 : location_info := LocationInfo file_0 200 2 200 3.
  Definition loc_241 : location_info := LocationInfo file_0 200 2 200 3.
  Definition loc_242 : location_info := LocationInfo file_0 200 16 200 30.
  Definition loc_243 : location_info := LocationInfo file_0 199 2 199 22.
  Definition loc_244 : location_info := LocationInfo file_0 199 2 199 11.
  Definition loc_245 : location_info := LocationInfo file_0 199 2 199 3.
  Definition loc_246 : location_info := LocationInfo file_0 199 2 199 3.
  Definition loc_247 : location_info := LocationInfo file_0 199 25 199 39.
  Definition loc_248 : location_info := LocationInfo file_0 198 2 198 22.
  Definition loc_249 : location_info := LocationInfo file_0 198 2 198 11.
  Definition loc_250 : location_info := LocationInfo file_0 198 2 198 3.
  Definition loc_251 : location_info := LocationInfo file_0 198 2 198 3.
  Definition loc_252 : location_info := LocationInfo file_0 198 25 198 39.
  Definition loc_253 : location_info := LocationInfo file_0 190 2 196 3.
  Definition loc_254 : location_info := LocationInfo file_0 190 34 196 3.
  Definition loc_255 : location_info := LocationInfo file_0 191 4 191 23.
  Definition loc_256 : location_info := LocationInfo file_0 192 4 192 30.
  Definition loc_257 : location_info := LocationInfo file_0 194 4 194 30.
  Definition loc_258 : location_info := LocationInfo file_0 195 4 195 45.
  Definition loc_259 : location_info := LocationInfo file_0 190 2 196 3.
  Definition loc_260 : location_info := LocationInfo file_0 190 2 196 3.
  Definition loc_261 : location_info := LocationInfo file_0 195 4 195 19.
  Definition loc_262 : location_info := LocationInfo file_0 195 4 195 19.
  Definition loc_263 : location_info := LocationInfo file_0 195 20 195 31.
  Definition loc_264 : location_info := LocationInfo file_0 195 20 195 31.
  Definition loc_265 : location_info := LocationInfo file_0 195 20 195 21.
  Definition loc_266 : location_info := LocationInfo file_0 195 20 195 21.
  Definition loc_267 : location_info := LocationInfo file_0 195 33 195 37.
  Definition loc_268 : location_info := LocationInfo file_0 195 33 195 37.
  Definition loc_269 : location_info := LocationInfo file_0 195 39 195 43.
  Definition loc_270 : location_info := LocationInfo file_0 195 39 195 43.
  Definition loc_271 : location_info := LocationInfo file_0 194 4 194 9.
  Definition loc_272 : location_info := LocationInfo file_0 194 12 194 29.
  Definition loc_273 : location_info := LocationInfo file_0 194 12 194 29.
  Definition loc_274 : location_info := LocationInfo file_0 194 12 194 17.
  Definition loc_275 : location_info := LocationInfo file_0 194 12 194 17.
  Definition loc_276 : location_info := LocationInfo file_0 192 18 192 29.
  Definition loc_277 : location_info := LocationInfo file_0 192 18 192 29.
  Definition loc_278 : location_info := LocationInfo file_0 192 18 192 23.
  Definition loc_279 : location_info := LocationInfo file_0 192 18 192 23.
  Definition loc_282 : location_info := LocationInfo file_0 191 17 191 22.
  Definition loc_283 : location_info := LocationInfo file_0 191 17 191 22.
  Definition loc_286 : location_info := LocationInfo file_0 190 9 190 32.
  Definition loc_287 : location_info := LocationInfo file_0 190 9 190 14.
  Definition loc_288 : location_info := LocationInfo file_0 190 9 190 14.
  Definition loc_289 : location_info := LocationInfo file_0 190 18 190 32.
  Definition loc_290 : location_info := LocationInfo file_0 180 2 184 3.
  Definition loc_291 : location_info := LocationInfo file_0 180 34 184 3.
  Definition loc_292 : location_info := LocationInfo file_0 181 4 181 23.
  Definition loc_293 : location_info := LocationInfo file_0 182 4 182 24.
  Definition loc_294 : location_info := LocationInfo file_0 183 4 183 34.
  Definition loc_295 : location_info := LocationInfo file_0 180 2 184 3.
  Definition loc_296 : location_info := LocationInfo file_0 180 2 184 3.
  Definition loc_297 : location_info := LocationInfo file_0 183 4 183 14.
  Definition loc_298 : location_info := LocationInfo file_0 183 4 183 14.
  Definition loc_299 : location_info := LocationInfo file_0 183 15 183 26.
  Definition loc_300 : location_info := LocationInfo file_0 183 15 183 26.
  Definition loc_301 : location_info := LocationInfo file_0 183 15 183 16.
  Definition loc_302 : location_info := LocationInfo file_0 183 15 183 16.
  Definition loc_303 : location_info := LocationInfo file_0 183 28 183 32.
  Definition loc_304 : location_info := LocationInfo file_0 183 28 183 32.
  Definition loc_305 : location_info := LocationInfo file_0 182 4 182 9.
  Definition loc_306 : location_info := LocationInfo file_0 182 12 182 23.
  Definition loc_307 : location_info := LocationInfo file_0 182 12 182 23.
  Definition loc_308 : location_info := LocationInfo file_0 182 12 182 17.
  Definition loc_309 : location_info := LocationInfo file_0 182 12 182 17.
  Definition loc_310 : location_info := LocationInfo file_0 181 17 181 22.
  Definition loc_311 : location_info := LocationInfo file_0 181 17 181 22.
  Definition loc_314 : location_info := LocationInfo file_0 180 9 180 32.
  Definition loc_315 : location_info := LocationInfo file_0 180 9 180 14.
  Definition loc_316 : location_info := LocationInfo file_0 180 9 180 14.
  Definition loc_317 : location_info := LocationInfo file_0 180 18 180 32.
  Definition loc_318 : location_info := LocationInfo file_0 175 2 175 7.
  Definition loc_319 : location_info := LocationInfo file_0 175 10 175 30.
  Definition loc_320 : location_info := LocationInfo file_0 175 10 175 30.
  Definition loc_321 : location_info := LocationInfo file_0 175 10 175 19.
  Definition loc_322 : location_info := LocationInfo file_0 175 10 175 11.
  Definition loc_323 : location_info := LocationInfo file_0 175 10 175 11.
  Definition loc_324 : location_info := LocationInfo file_0 174 2 174 7.
  Definition loc_325 : location_info := LocationInfo file_0 174 10 174 30.
  Definition loc_326 : location_info := LocationInfo file_0 174 10 174 30.
  Definition loc_327 : location_info := LocationInfo file_0 174 10 174 19.
  Definition loc_328 : location_info := LocationInfo file_0 174 10 174 11.
  Definition loc_329 : location_info := LocationInfo file_0 174 10 174 11.
  Definition loc_330 : location_info := LocationInfo file_0 170 37 172 3.
  Definition loc_331 : location_info := LocationInfo file_0 171 4 171 11.
  Definition loc_334 : location_info := LocationInfo file_0 170 6 170 35.
  Definition loc_335 : location_info := LocationInfo file_0 170 6 170 17.
  Definition loc_336 : location_info := LocationInfo file_0 170 6 170 17.
  Definition loc_337 : location_info := LocationInfo file_0 170 6 170 7.
  Definition loc_338 : location_info := LocationInfo file_0 170 6 170 7.
  Definition loc_339 : location_info := LocationInfo file_0 170 21 170 35.
  Definition loc_342 : location_info := LocationInfo file_0 262 2 262 20.
  Definition loc_343 : location_info := LocationInfo file_0 263 2 263 40.
  Definition loc_344 : location_info := LocationInfo file_0 263 40 263 3.
  Definition loc_345 : location_info := LocationInfo file_0 264 2 270 3.
  Definition loc_346 : location_info := LocationInfo file_0 273 2 273 31.
  Definition loc_347 : location_info := LocationInfo file_0 274 2 278 3.
  Definition loc_348 : location_info := LocationInfo file_0 280 2 287 3.
  Definition loc_349 : location_info := LocationInfo file_0 289 2 289 14.
  Definition loc_350 : location_info := LocationInfo file_0 289 14 292 22.
  Definition loc_351 : location_info := LocationInfo file_0 292 2 292 22.
  Definition loc_352 : location_info := LocationInfo file_0 294 2 294 13.
  Definition loc_353 : location_info := LocationInfo file_0 294 9 294 12.
  Definition loc_354 : location_info := LocationInfo file_0 294 9 294 12.
  Definition loc_355 : location_info := LocationInfo file_0 292 2 292 11.
  Definition loc_356 : location_info := LocationInfo file_0 292 2 292 11.
  Definition loc_357 : location_info := LocationInfo file_0 292 12 292 20.
  Definition loc_358 : location_info := LocationInfo file_0 292 13 292 20.
  Definition loc_359 : location_info := LocationInfo file_0 292 13 292 14.
  Definition loc_360 : location_info := LocationInfo file_0 292 13 292 14.
  Definition loc_361 : location_info := LocationInfo file_0 289 2 289 5.
  Definition loc_362 : location_info := LocationInfo file_0 289 8 289 13.
  Definition loc_363 : location_info := LocationInfo file_0 289 8 289 13.
  Definition loc_364 : location_info := LocationInfo file_0 280 36 282 3.
  Definition loc_365 : location_info := LocationInfo file_0 281 4 281 45.
  Definition loc_366 : location_info := LocationInfo file_0 281 4 281 24.
  Definition loc_367 : location_info := LocationInfo file_0 281 4 281 13.
  Definition loc_368 : location_info := LocationInfo file_0 281 4 281 5.
  Definition loc_369 : location_info := LocationInfo file_0 281 4 281 5.
  Definition loc_370 : location_info := LocationInfo file_0 281 27 281 44.
  Definition loc_371 : location_info := LocationInfo file_0 281 27 281 44.
  Definition loc_372 : location_info := LocationInfo file_0 281 27 281 32.
  Definition loc_373 : location_info := LocationInfo file_0 281 27 281 32.
  Definition loc_374 : location_info := LocationInfo file_0 282 9 287 3.
  Definition loc_375 : location_info := LocationInfo file_0 283 4 283 79.
  Definition loc_376 : location_info := LocationInfo file_0 284 4 284 46.
  Definition loc_377 : location_info := LocationInfo file_0 285 4 285 50.
  Definition loc_378 : location_info := LocationInfo file_0 286 4 286 37.
  Definition loc_379 : location_info := LocationInfo file_0 286 4 286 24.
  Definition loc_380 : location_info := LocationInfo file_0 286 4 286 13.
  Definition loc_381 : location_info := LocationInfo file_0 286 4 286 5.
  Definition loc_382 : location_info := LocationInfo file_0 286 4 286 5.
  Definition loc_383 : location_info := LocationInfo file_0 286 27 286 36.
  Definition loc_384 : location_info := LocationInfo file_0 286 27 286 36.
  Definition loc_385 : location_info := LocationInfo file_0 285 4 285 19.
  Definition loc_386 : location_info := LocationInfo file_0 285 4 285 13.
  Definition loc_387 : location_info := LocationInfo file_0 285 4 285 13.
  Definition loc_388 : location_info := LocationInfo file_0 285 22 285 49.
  Definition loc_389 : location_info := LocationInfo file_0 285 22 285 33.
  Definition loc_390 : location_info := LocationInfo file_0 285 22 285 33.
  Definition loc_391 : location_info := LocationInfo file_0 285 22 285 27.
  Definition loc_392 : location_info := LocationInfo file_0 285 22 285 27.
  Definition loc_393 : location_info := LocationInfo file_0 285 36 285 49.
  Definition loc_394 : location_info := LocationInfo file_0 285 36 285 49.
  Definition loc_395 : location_info := LocationInfo file_0 285 36 285 37.
  Definition loc_396 : location_info := LocationInfo file_0 285 36 285 37.
  Definition loc_397 : location_info := LocationInfo file_0 284 4 284 25.
  Definition loc_398 : location_info := LocationInfo file_0 284 4 284 13.
  Definition loc_399 : location_info := LocationInfo file_0 284 4 284 13.
  Definition loc_400 : location_info := LocationInfo file_0 284 28 284 45.
  Definition loc_401 : location_info := LocationInfo file_0 284 28 284 45.
  Definition loc_402 : location_info := LocationInfo file_0 284 28 284 33.
  Definition loc_403 : location_info := LocationInfo file_0 284 28 284 33.
  Definition loc_404 : location_info := LocationInfo file_0 283 4 283 13.
  Definition loc_405 : location_info := LocationInfo file_0 283 16 283 78.
  Definition loc_406 : location_info := LocationInfo file_0 283 38 283 78.
  Definition loc_407 : location_info := LocationInfo file_0 283 39 283 61.
  Definition loc_408 : location_info := LocationInfo file_0 283 56 283 61.
  Definition loc_409 : location_info := LocationInfo file_0 283 56 283 61.
  Definition loc_410 : location_info := LocationInfo file_0 283 64 283 77.
  Definition loc_411 : location_info := LocationInfo file_0 283 64 283 77.
  Definition loc_412 : location_info := LocationInfo file_0 283 64 283 65.
  Definition loc_413 : location_info := LocationInfo file_0 283 64 283 65.
  Definition loc_414 : location_info := LocationInfo file_0 280 6 280 34.
  Definition loc_415 : location_info := LocationInfo file_0 280 6 280 19.
  Definition loc_416 : location_info := LocationInfo file_0 280 6 280 19.
  Definition loc_417 : location_info := LocationInfo file_0 280 6 280 7.
  Definition loc_418 : location_info := LocationInfo file_0 280 6 280 7.
  Definition loc_419 : location_info := LocationInfo file_0 280 23 280 34.
  Definition loc_420 : location_info := LocationInfo file_0 280 23 280 34.
  Definition loc_421 : location_info := LocationInfo file_0 280 23 280 28.
  Definition loc_422 : location_info := LocationInfo file_0 280 23 280 28.
  Definition loc_423 : location_info := LocationInfo file_0 274 31 278 3.
  Definition loc_424 : location_info := LocationInfo file_0 276 4 276 25.
  Definition loc_425 : location_info := LocationInfo file_0 277 4 277 14.
  Definition loc_426 : location_info := LocationInfo file_0 276 4 276 7.
  Definition loc_427 : location_info := LocationInfo file_0 276 10 276 24.
  Definition loc_429 : location_info := LocationInfo file_0 274 6 274 29.
  Definition loc_430 : location_info := LocationInfo file_0 274 6 274 11.
  Definition loc_431 : location_info := LocationInfo file_0 274 6 274 11.
  Definition loc_432 : location_info := LocationInfo file_0 274 15 274 29.
  Definition loc_433 : location_info := LocationInfo file_0 273 2 273 7.
  Definition loc_434 : location_info := LocationInfo file_0 273 10 273 30.
  Definition loc_435 : location_info := LocationInfo file_0 273 10 273 30.
  Definition loc_436 : location_info := LocationInfo file_0 273 10 273 19.
  Definition loc_437 : location_info := LocationInfo file_0 273 10 273 11.
  Definition loc_438 : location_info := LocationInfo file_0 273 10 273 11.
  Definition loc_439 : location_info := LocationInfo file_0 264 46 270 3.
  Definition loc_440 : location_info := LocationInfo file_0 265 4 265 53.
  Definition loc_441 : location_info := LocationInfo file_0 267 4 267 39.
  Definition loc_442 : location_info := LocationInfo file_0 268 4 268 16.
  Definition loc_443 : location_info := LocationInfo file_0 269 4 269 14.
  Definition loc_444 : location_info := LocationInfo file_0 268 4 268 7.
  Definition loc_445 : location_info := LocationInfo file_0 268 10 268 15.
  Definition loc_446 : location_info := LocationInfo file_0 268 10 268 15.
  Definition loc_447 : location_info := LocationInfo file_0 267 4 267 24.
  Definition loc_448 : location_info := LocationInfo file_0 267 4 267 13.
  Definition loc_449 : location_info := LocationInfo file_0 267 4 267 5.
  Definition loc_450 : location_info := LocationInfo file_0 267 4 267 5.
  Definition loc_451 : location_info := LocationInfo file_0 267 27 267 38.
  Definition loc_452 : location_info := LocationInfo file_0 267 27 267 38.
  Definition loc_453 : location_info := LocationInfo file_0 267 27 267 32.
  Definition loc_454 : location_info := LocationInfo file_0 267 27 267 32.
  Definition loc_455 : location_info := LocationInfo file_0 265 32 265 52.
  Definition loc_456 : location_info := LocationInfo file_0 265 32 265 52.
  Definition loc_457 : location_info := LocationInfo file_0 265 32 265 41.
  Definition loc_458 : location_info := LocationInfo file_0 265 32 265 33.
  Definition loc_459 : location_info := LocationInfo file_0 265 32 265 33.
  Definition loc_463 : location_info := LocationInfo file_0 264 6 264 44.
  Definition loc_464 : location_info := LocationInfo file_0 264 6 264 26.
  Definition loc_465 : location_info := LocationInfo file_0 264 6 264 26.
  Definition loc_466 : location_info := LocationInfo file_0 264 6 264 15.
  Definition loc_467 : location_info := LocationInfo file_0 264 6 264 7.
  Definition loc_468 : location_info := LocationInfo file_0 264 6 264 7.
  Definition loc_469 : location_info := LocationInfo file_0 264 30 264 44.
  Definition loc_470 : location_info := LocationInfo file_0 263 27 263 39.
  Definition loc_471 : location_info := LocationInfo file_0 263 28 263 39.
  Definition loc_472 : location_info := LocationInfo file_0 263 29 263 30.
  Definition loc_473 : location_info := LocationInfo file_0 263 29 263 30.
  Definition loc_474 : location_info := LocationInfo file_0 262 2 262 9.
  Definition loc_475 : location_info := LocationInfo file_0 262 2 262 9.
  Definition loc_476 : location_info := LocationInfo file_0 262 10 262 18.
  Definition loc_477 : location_info := LocationInfo file_0 262 11 262 18.
  Definition loc_478 : location_info := LocationInfo file_0 262 11 262 12.
  Definition loc_479 : location_info := LocationInfo file_0 262 11 262 12.
  Definition loc_482 : location_info := LocationInfo file_0 307 2 307 41.
  Definition loc_483 : location_info := LocationInfo file_0 308 2 310 3.
  Definition loc_484 : location_info := LocationInfo file_0 311 2 311 18.
  Definition loc_485 : location_info := LocationInfo file_0 315 2 321 3.
  Definition loc_486 : location_info := LocationInfo file_0 323 2 323 24.
  Definition loc_487 : location_info := LocationInfo file_0 323 9 323 23.
  Definition loc_488 : location_info := LocationInfo file_0 315 2 321 3.
  Definition loc_489 : location_info := LocationInfo file_0 315 30 321 3.
  Definition loc_490 : location_info := LocationInfo file_0 316 4 316 37.
  Definition loc_491 : location_info := LocationInfo file_0 317 4 319 5.
  Definition loc_492 : location_info := LocationInfo file_0 320 4 320 20.
  Definition loc_493 : location_info := LocationInfo file_0 315 2 321 3.
  Definition loc_494 : location_info := LocationInfo file_0 315 2 321 3.
  Definition loc_495 : location_info := LocationInfo file_0 320 4 320 5.
  Definition loc_496 : location_info := LocationInfo file_0 320 8 320 19.
  Definition loc_497 : location_info := LocationInfo file_0 320 8 320 19.
  Definition loc_498 : location_info := LocationInfo file_0 320 8 320 9.
  Definition loc_499 : location_info := LocationInfo file_0 320 8 320 9.
  Definition loc_500 : location_info := LocationInfo file_0 317 31 319 5.
  Definition loc_501 : location_info := LocationInfo file_0 318 6 318 17.
  Definition loc_502 : location_info := LocationInfo file_0 318 13 318 16.
  Definition loc_503 : location_info := LocationInfo file_0 318 13 318 16.
  Definition loc_505 : location_info := LocationInfo file_0 317 8 317 29.
  Definition loc_506 : location_info := LocationInfo file_0 317 8 317 11.
  Definition loc_507 : location_info := LocationInfo file_0 317 8 317 11.
  Definition loc_508 : location_info := LocationInfo file_0 317 15 317 29.
  Definition loc_509 : location_info := LocationInfo file_0 316 4 316 7.
  Definition loc_510 : location_info := LocationInfo file_0 316 10 316 36.
  Definition loc_511 : location_info := LocationInfo file_0 316 10 316 33.
  Definition loc_512 : location_info := LocationInfo file_0 316 10 316 33.
  Definition loc_513 : location_info := LocationInfo file_0 316 34 316 35.
  Definition loc_514 : location_info := LocationInfo file_0 316 34 316 35.
  Definition loc_515 : location_info := LocationInfo file_0 315 9 315 28.
  Definition loc_516 : location_info := LocationInfo file_0 315 9 315 10.
  Definition loc_517 : location_info := LocationInfo file_0 315 9 315 10.
  Definition loc_518 : location_info := LocationInfo file_0 315 14 315 28.
  Definition loc_519 : location_info := LocationInfo file_0 311 2 311 3.
  Definition loc_520 : location_info := LocationInfo file_0 311 6 311 17.
  Definition loc_521 : location_info := LocationInfo file_0 311 6 311 17.
  Definition loc_522 : location_info := LocationInfo file_0 311 6 311 7.
  Definition loc_523 : location_info := LocationInfo file_0 311 6 311 7.
  Definition loc_524 : location_info := LocationInfo file_0 308 29 310 3.
  Definition loc_525 : location_info := LocationInfo file_0 309 4 309 15.
  Definition loc_526 : location_info := LocationInfo file_0 309 11 309 14.
  Definition loc_527 : location_info := LocationInfo file_0 309 11 309 14.
  Definition loc_529 : location_info := LocationInfo file_0 308 6 308 27.
  Definition loc_530 : location_info := LocationInfo file_0 308 6 308 9.
  Definition loc_531 : location_info := LocationInfo file_0 308 6 308 9.
  Definition loc_532 : location_info := LocationInfo file_0 308 13 308 27.
  Definition loc_533 : location_info := LocationInfo file_0 307 14 307 40.
  Definition loc_534 : location_info := LocationInfo file_0 307 14 307 37.
  Definition loc_535 : location_info := LocationInfo file_0 307 14 307 37.
  Definition loc_536 : location_info := LocationInfo file_0 307 38 307 39.
  Definition loc_537 : location_info := LocationInfo file_0 307 38 307 39.
  Definition loc_542 : location_info := LocationInfo file_0 363 2 363 29.
  Definition loc_543 : location_info := LocationInfo file_0 365 2 365 25.
  Definition loc_544 : location_info := LocationInfo file_0 367 2 367 20.
  Definition loc_545 : location_info := LocationInfo file_0 368 2 368 40.
  Definition loc_546 : location_info := LocationInfo file_0 368 40 368 3.
  Definition loc_547 : location_info := LocationInfo file_0 374 2 374 31.
  Definition loc_548 : location_info := LocationInfo file_0 384 2 430 3.
  Definition loc_549 : location_info := LocationInfo file_0 432 2 432 22.
  Definition loc_550 : location_info := LocationInfo file_0 434 2 434 13.
  Definition loc_551 : location_info := LocationInfo file_0 434 9 434 12.
  Definition loc_552 : location_info := LocationInfo file_0 434 9 434 12.
  Definition loc_553 : location_info := LocationInfo file_0 432 2 432 11.
  Definition loc_554 : location_info := LocationInfo file_0 432 2 432 11.
  Definition loc_555 : location_info := LocationInfo file_0 432 12 432 20.
  Definition loc_556 : location_info := LocationInfo file_0 432 13 432 20.
  Definition loc_557 : location_info := LocationInfo file_0 432 13 432 14.
  Definition loc_558 : location_info := LocationInfo file_0 432 13 432 14.
  Definition loc_559 : location_info := LocationInfo file_0 384 2 430 3.
  Definition loc_560 : location_info := LocationInfo file_0 384 34 430 3.
  Definition loc_561 : location_info := LocationInfo file_0 387 4 387 38.
  Definition loc_562 : location_info := LocationInfo file_0 390 4 390 51.
  Definition loc_563 : location_info := LocationInfo file_0 390 51 390 5.
  Definition loc_564 : location_info := LocationInfo file_0 392 4 392 67.
  Definition loc_565 : location_info := LocationInfo file_0 399 4 427 5.
  Definition loc_566 : location_info := LocationInfo file_0 429 4 429 30.
  Definition loc_567 : location_info := LocationInfo file_0 384 2 430 3.
  Definition loc_568 : location_info := LocationInfo file_0 384 2 430 3.
  Definition loc_569 : location_info := LocationInfo file_0 429 4 429 8.
  Definition loc_570 : location_info := LocationInfo file_0 429 11 429 29.
  Definition loc_571 : location_info := LocationInfo file_0 429 12 429 29.
  Definition loc_572 : location_info := LocationInfo file_0 429 12 429 17.
  Definition loc_573 : location_info := LocationInfo file_0 429 12 429 17.
  Definition loc_574 : location_info := LocationInfo file_0 399 61 427 5.
  Definition loc_575 : location_info := LocationInfo file_0 400 6 400 38.
  Definition loc_576 : location_info := LocationInfo file_0 401 6 401 57.
  Definition loc_577 : location_info := LocationInfo file_0 402 6 402 42.
  Definition loc_578 : location_info := LocationInfo file_0 402 42 402 7.
  Definition loc_579 : location_info := LocationInfo file_0 403 6 403 52.
  Definition loc_580 : location_info := LocationInfo file_0 405 6 412 7.
  Definition loc_581 : location_info := LocationInfo file_0 418 6 422 7.
  Definition loc_582 : location_info := LocationInfo file_0 424 6 424 55.
  Definition loc_583 : location_info := LocationInfo file_0 424 55 424 7.
  Definition loc_584 : location_info := LocationInfo file_0 425 6 425 26.
  Definition loc_585 : location_info := LocationInfo file_0 426 6 426 12.
  Definition loc_586 : location_info := LocationInfo file_0 425 6 425 9.
  Definition loc_587 : location_info := LocationInfo file_0 425 12 425 25.
  Definition loc_588 : location_info := LocationInfo file_0 425 20 425 25.
  Definition loc_589 : location_info := LocationInfo file_0 425 20 425 25.
  Definition loc_590 : location_info := LocationInfo file_0 424 45 424 54.
  Definition loc_591 : location_info := LocationInfo file_0 424 46 424 54.
  Definition loc_592 : location_info := LocationInfo file_0 424 48 424 53.
  Definition loc_593 : location_info := LocationInfo file_0 424 48 424 53.
  Definition loc_594 : location_info := LocationInfo file_0 418 41 422 7.
  Definition loc_595 : location_info := LocationInfo file_0 419 8 419 34.
  Definition loc_596 : location_info := LocationInfo file_0 420 8 420 22.
  Definition loc_597 : location_info := LocationInfo file_0 421 8 421 35.
  Definition loc_598 : location_info := LocationInfo file_0 421 8 421 19.
  Definition loc_599 : location_info := LocationInfo file_0 421 8 421 13.
  Definition loc_600 : location_info := LocationInfo file_0 421 8 421 13.
  Definition loc_601 : location_info := LocationInfo file_0 421 22 421 34.
  Definition loc_602 : location_info := LocationInfo file_0 421 22 421 34.
  Definition loc_603 : location_info := LocationInfo file_0 420 8 420 13.
  Definition loc_604 : location_info := LocationInfo file_0 420 9 420 13.
  Definition loc_605 : location_info := LocationInfo file_0 420 9 420 13.
  Definition loc_606 : location_info := LocationInfo file_0 420 16 420 21.
  Definition loc_607 : location_info := LocationInfo file_0 420 16 420 21.
  Definition loc_608 : location_info := LocationInfo file_0 419 8 419 25.
  Definition loc_609 : location_info := LocationInfo file_0 419 8 419 13.
  Definition loc_610 : location_info := LocationInfo file_0 419 8 419 13.
  Definition loc_611 : location_info := LocationInfo file_0 419 28 419 33.
  Definition loc_612 : location_info := LocationInfo file_0 419 28 419 33.
  Definition loc_613 : location_info := LocationInfo file_0 419 29 419 33.
  Definition loc_614 : location_info := LocationInfo file_0 419 29 419 33.
  Definition loc_616 : location_info := LocationInfo file_0 418 10 418 39.
  Definition loc_617 : location_info := LocationInfo file_0 418 10 418 22.
  Definition loc_618 : location_info := LocationInfo file_0 418 10 418 22.
  Definition loc_619 : location_info := LocationInfo file_0 418 26 418 39.
  Definition loc_620 : location_info := LocationInfo file_0 418 26 418 39.
  Definition loc_621 : location_info := LocationInfo file_0 418 26 418 27.
  Definition loc_622 : location_info := LocationInfo file_0 418 26 418 27.
  Definition loc_623 : location_info := LocationInfo file_0 405 62 407 7.
  Definition loc_624 : location_info := LocationInfo file_0 406 8 406 27.
  Definition loc_625 : location_info := LocationInfo file_0 406 8 406 13.
  Definition loc_626 : location_info := LocationInfo file_0 406 9 406 13.
  Definition loc_627 : location_info := LocationInfo file_0 406 9 406 13.
  Definition loc_628 : location_info := LocationInfo file_0 406 16 406 26.
  Definition loc_629 : location_info := LocationInfo file_0 406 16 406 26.
  Definition loc_630 : location_info := LocationInfo file_0 407 13 412 7.
  Definition loc_631 : location_info := LocationInfo file_0 408 8 408 76.
  Definition loc_632 : location_info := LocationInfo file_0 409 8 409 78.
  Definition loc_633 : location_info := LocationInfo file_0 410 8 410 43.
  Definition loc_634 : location_info := LocationInfo file_0 411 8 411 26.
  Definition loc_635 : location_info := LocationInfo file_0 411 8 411 13.
  Definition loc_636 : location_info := LocationInfo file_0 411 9 411 13.
  Definition loc_637 : location_info := LocationInfo file_0 411 9 411 13.
  Definition loc_638 : location_info := LocationInfo file_0 411 16 411 25.
  Definition loc_639 : location_info := LocationInfo file_0 411 16 411 25.
  Definition loc_640 : location_info := LocationInfo file_0 410 8 410 29.
  Definition loc_641 : location_info := LocationInfo file_0 410 8 410 17.
  Definition loc_642 : location_info := LocationInfo file_0 410 8 410 17.
  Definition loc_643 : location_info := LocationInfo file_0 410 32 410 42.
  Definition loc_644 : location_info := LocationInfo file_0 410 32 410 42.
  Definition loc_645 : location_info := LocationInfo file_0 409 8 409 23.
  Definition loc_646 : location_info := LocationInfo file_0 409 8 409 17.
  Definition loc_647 : location_info := LocationInfo file_0 409 8 409 17.
  Definition loc_648 : location_info := LocationInfo file_0 409 26 409 77.
  Definition loc_649 : location_info := LocationInfo file_0 409 26 409 36.
  Definition loc_650 : location_info := LocationInfo file_0 409 26 409 36.
  Definition loc_651 : location_info := LocationInfo file_0 409 39 409 77.
  Definition loc_652 : location_info := LocationInfo file_0 409 40 409 52.
  Definition loc_653 : location_info := LocationInfo file_0 409 40 409 52.
  Definition loc_654 : location_info := LocationInfo file_0 409 55 409 76.
  Definition loc_655 : location_info := LocationInfo file_0 409 55 409 60.
  Definition loc_656 : location_info := LocationInfo file_0 409 55 409 60.
  Definition loc_657 : location_info := LocationInfo file_0 409 63 409 76.
  Definition loc_658 : location_info := LocationInfo file_0 409 63 409 76.
  Definition loc_659 : location_info := LocationInfo file_0 409 63 409 64.
  Definition loc_660 : location_info := LocationInfo file_0 409 63 409 64.
  Definition loc_661 : location_info := LocationInfo file_0 408 8 408 17.
  Definition loc_662 : location_info := LocationInfo file_0 408 20 408 75.
  Definition loc_663 : location_info := LocationInfo file_0 408 42 408 75.
  Definition loc_664 : location_info := LocationInfo file_0 408 43 408 48.
  Definition loc_665 : location_info := LocationInfo file_0 408 43 408 48.
  Definition loc_666 : location_info := LocationInfo file_0 408 51 408 74.
  Definition loc_667 : location_info := LocationInfo file_0 408 52 408 57.
  Definition loc_668 : location_info := LocationInfo file_0 408 52 408 57.
  Definition loc_669 : location_info := LocationInfo file_0 408 60 408 73.
  Definition loc_670 : location_info := LocationInfo file_0 408 60 408 73.
  Definition loc_671 : location_info := LocationInfo file_0 408 60 408 61.
  Definition loc_672 : location_info := LocationInfo file_0 408 60 408 61.
  Definition loc_673 : location_info := LocationInfo file_0 405 10 405 60.
  Definition loc_674 : location_info := LocationInfo file_0 405 10 405 46.
  Definition loc_675 : location_info := LocationInfo file_0 405 10 405 22.
  Definition loc_676 : location_info := LocationInfo file_0 405 10 405 22.
  Definition loc_677 : location_info := LocationInfo file_0 405 25 405 46.
  Definition loc_678 : location_info := LocationInfo file_0 405 25 405 30.
  Definition loc_679 : location_info := LocationInfo file_0 405 25 405 30.
  Definition loc_680 : location_info := LocationInfo file_0 405 33 405 46.
  Definition loc_681 : location_info := LocationInfo file_0 405 33 405 46.
  Definition loc_682 : location_info := LocationInfo file_0 405 33 405 34.
  Definition loc_683 : location_info := LocationInfo file_0 405 33 405 34.
  Definition loc_684 : location_info := LocationInfo file_0 405 50 405 60.
  Definition loc_685 : location_info := LocationInfo file_0 405 50 405 60.
  Definition loc_686 : location_info := LocationInfo file_0 403 6 403 11.
  Definition loc_687 : location_info := LocationInfo file_0 403 14 403 51.
  Definition loc_688 : location_info := LocationInfo file_0 403 14 403 36.
  Definition loc_689 : location_info := LocationInfo file_0 403 31 403 36.
  Definition loc_690 : location_info := LocationInfo file_0 403 31 403 36.
  Definition loc_691 : location_info := LocationInfo file_0 403 39 403 51.
  Definition loc_692 : location_info := LocationInfo file_0 403 39 403 51.
  Definition loc_693 : location_info := LocationInfo file_0 402 32 402 41.
  Definition loc_694 : location_info := LocationInfo file_0 402 33 402 41.
  Definition loc_695 : location_info := LocationInfo file_0 402 35 402 40.
  Definition loc_696 : location_info := LocationInfo file_0 402 35 402 40.
  Definition loc_697 : location_info := LocationInfo file_0 401 39 401 56.
  Definition loc_698 : location_info := LocationInfo file_0 401 39 401 56.
  Definition loc_699 : location_info := LocationInfo file_0 401 39 401 44.
  Definition loc_700 : location_info := LocationInfo file_0 401 39 401 44.
  Definition loc_703 : location_info := LocationInfo file_0 400 26 400 37.
  Definition loc_704 : location_info := LocationInfo file_0 400 26 400 37.
  Definition loc_705 : location_info := LocationInfo file_0 400 26 400 31.
  Definition loc_706 : location_info := LocationInfo file_0 400 26 400 31.
  Definition loc_710 : location_info := LocationInfo file_0 399 8 399 59.
  Definition loc_711 : location_info := LocationInfo file_0 399 8 399 44.
  Definition loc_712 : location_info := LocationInfo file_0 399 8 399 20.
  Definition loc_713 : location_info := LocationInfo file_0 399 8 399 20.
  Definition loc_714 : location_info := LocationInfo file_0 399 23 399 44.
  Definition loc_715 : location_info := LocationInfo file_0 399 23 399 28.
  Definition loc_716 : location_info := LocationInfo file_0 399 23 399 28.
  Definition loc_717 : location_info := LocationInfo file_0 399 31 399 44.
  Definition loc_718 : location_info := LocationInfo file_0 399 31 399 44.
  Definition loc_719 : location_info := LocationInfo file_0 399 31 399 32.
  Definition loc_720 : location_info := LocationInfo file_0 399 31 399 32.
  Definition loc_721 : location_info := LocationInfo file_0 399 48 399 59.
  Definition loc_722 : location_info := LocationInfo file_0 399 48 399 59.
  Definition loc_723 : location_info := LocationInfo file_0 399 48 399 53.
  Definition loc_724 : location_info := LocationInfo file_0 399 48 399 53.
  Definition loc_725 : location_info := LocationInfo file_0 392 4 392 20.
  Definition loc_726 : location_info := LocationInfo file_0 392 4 392 20.
  Definition loc_727 : location_info := LocationInfo file_0 392 21 392 43.
  Definition loc_728 : location_info := LocationInfo file_0 392 38 392 43.
  Definition loc_729 : location_info := LocationInfo file_0 392 38 392 43.
  Definition loc_730 : location_info := LocationInfo file_0 392 45 392 50.
  Definition loc_731 : location_info := LocationInfo file_0 392 45 392 50.
  Definition loc_732 : location_info := LocationInfo file_0 392 52 392 65.
  Definition loc_733 : location_info := LocationInfo file_0 392 53 392 65.
  Definition loc_734 : location_info := LocationInfo file_0 390 41 390 50.
  Definition loc_735 : location_info := LocationInfo file_0 390 42 390 50.
  Definition loc_736 : location_info := LocationInfo file_0 390 44 390 49.
  Definition loc_737 : location_info := LocationInfo file_0 390 44 390 49.
  Definition loc_738 : location_info := LocationInfo file_0 387 32 387 37.
  Definition loc_739 : location_info := LocationInfo file_0 387 32 387 37.
  Definition loc_740 : location_info := LocationInfo file_0 387 33 387 37.
  Definition loc_741 : location_info := LocationInfo file_0 387 33 387 37.
  Definition loc_744 : location_info := LocationInfo file_0 384 9 384 32.
  Definition loc_745 : location_info := LocationInfo file_0 384 9 384 14.
  Definition loc_746 : location_info := LocationInfo file_0 384 9 384 14.
  Definition loc_747 : location_info := LocationInfo file_0 384 10 384 14.
  Definition loc_748 : location_info := LocationInfo file_0 384 10 384 14.
  Definition loc_749 : location_info := LocationInfo file_0 384 18 384 32.
  Definition loc_750 : location_info := LocationInfo file_0 374 2 374 6.
  Definition loc_751 : location_info := LocationInfo file_0 374 9 374 30.
  Definition loc_752 : location_info := LocationInfo file_0 374 10 374 30.
  Definition loc_753 : location_info := LocationInfo file_0 374 10 374 19.
  Definition loc_754 : location_info := LocationInfo file_0 374 10 374 11.
  Definition loc_755 : location_info := LocationInfo file_0 374 10 374 11.
  Definition loc_756 : location_info := LocationInfo file_0 368 27 368 39.
  Definition loc_757 : location_info := LocationInfo file_0 368 28 368 39.
  Definition loc_758 : location_info := LocationInfo file_0 368 29 368 30.
  Definition loc_759 : location_info := LocationInfo file_0 368 29 368 30.
  Definition loc_760 : location_info := LocationInfo file_0 367 2 367 9.
  Definition loc_761 : location_info := LocationInfo file_0 367 2 367 9.
  Definition loc_762 : location_info := LocationInfo file_0 367 10 367 18.
  Definition loc_763 : location_info := LocationInfo file_0 367 11 367 18.
  Definition loc_764 : location_info := LocationInfo file_0 367 11 367 12.
  Definition loc_765 : location_info := LocationInfo file_0 367 11 367 12.
  Definition loc_766 : location_info := LocationInfo file_0 365 2 365 7.
  Definition loc_767 : location_info := LocationInfo file_0 365 2 365 24.
  Definition loc_768 : location_info := LocationInfo file_0 365 2 365 7.
  Definition loc_769 : location_info := LocationInfo file_0 365 2 365 7.
  Definition loc_770 : location_info := LocationInfo file_0 365 11 365 24.
  Definition loc_771 : location_info := LocationInfo file_0 365 11 365 24.
  Definition loc_772 : location_info := LocationInfo file_0 365 11 365 12.
  Definition loc_773 : location_info := LocationInfo file_0 365 11 365 12.
  Definition loc_774 : location_info := LocationInfo file_0 363 14 363 28.
  Definition loc_779 : location_info := LocationInfo file_0 457 2 457 66.
  Definition loc_780 : location_info := LocationInfo file_0 459 2 461 3.
  Definition loc_781 : location_info := LocationInfo file_0 463 2 463 18.
  Definition loc_782 : location_info := LocationInfo file_0 467 2 476 3.
  Definition loc_783 : location_info := LocationInfo file_0 478 2 478 24.
  Definition loc_784 : location_info := LocationInfo file_0 478 9 478 23.
  Definition loc_785 : location_info := LocationInfo file_0 467 2 476 3.
  Definition loc_786 : location_info := LocationInfo file_0 467 30 476 3.
  Definition loc_787 : location_info := LocationInfo file_0 468 4 468 62.
  Definition loc_788 : location_info := LocationInfo file_0 470 4 472 5.
  Definition loc_789 : location_info := LocationInfo file_0 474 4 474 20.
  Definition loc_790 : location_info := LocationInfo file_0 467 2 476 3.
  Definition loc_791 : location_info := LocationInfo file_0 467 2 476 3.
  Definition loc_792 : location_info := LocationInfo file_0 474 4 474 5.
  Definition loc_793 : location_info := LocationInfo file_0 474 8 474 19.
  Definition loc_794 : location_info := LocationInfo file_0 474 8 474 19.
  Definition loc_795 : location_info := LocationInfo file_0 474 8 474 9.
  Definition loc_796 : location_info := LocationInfo file_0 474 8 474 9.
  Definition loc_797 : location_info := LocationInfo file_0 470 31 472 5.
  Definition loc_798 : location_info := LocationInfo file_0 471 6 471 17.
  Definition loc_799 : location_info := LocationInfo file_0 471 13 471 16.
  Definition loc_800 : location_info := LocationInfo file_0 471 13 471 16.
  Definition loc_802 : location_info := LocationInfo file_0 470 8 470 29.
  Definition loc_803 : location_info := LocationInfo file_0 470 8 470 11.
  Definition loc_804 : location_info := LocationInfo file_0 470 8 470 11.
  Definition loc_805 : location_info := LocationInfo file_0 470 15 470 29.
  Definition loc_806 : location_info := LocationInfo file_0 468 4 468 7.
  Definition loc_807 : location_info := LocationInfo file_0 468 10 468 61.
  Definition loc_808 : location_info := LocationInfo file_0 468 10 468 44.
  Definition loc_809 : location_info := LocationInfo file_0 468 10 468 44.
  Definition loc_810 : location_info := LocationInfo file_0 468 45 468 46.
  Definition loc_811 : location_info := LocationInfo file_0 468 45 468 46.
  Definition loc_812 : location_info := LocationInfo file_0 468 48 468 53.
  Definition loc_813 : location_info := LocationInfo file_0 468 48 468 53.
  Definition loc_814 : location_info := LocationInfo file_0 468 55 468 60.
  Definition loc_815 : location_info := LocationInfo file_0 468 55 468 60.
  Definition loc_816 : location_info := LocationInfo file_0 467 9 467 28.
  Definition loc_817 : location_info := LocationInfo file_0 467 9 467 10.
  Definition loc_818 : location_info := LocationInfo file_0 467 9 467 10.
  Definition loc_819 : location_info := LocationInfo file_0 467 14 467 28.
  Definition loc_820 : location_info := LocationInfo file_0 463 2 463 3.
  Definition loc_821 : location_info := LocationInfo file_0 463 6 463 17.
  Definition loc_822 : location_info := LocationInfo file_0 463 6 463 17.
  Definition loc_823 : location_info := LocationInfo file_0 463 6 463 7.
  Definition loc_824 : location_info := LocationInfo file_0 463 6 463 7.
  Definition loc_825 : location_info := LocationInfo file_0 459 29 461 3.
  Definition loc_826 : location_info := LocationInfo file_0 460 4 460 15.
  Definition loc_827 : location_info := LocationInfo file_0 460 11 460 14.
  Definition loc_828 : location_info := LocationInfo file_0 460 11 460 14.
  Definition loc_830 : location_info := LocationInfo file_0 459 6 459 27.
  Definition loc_831 : location_info := LocationInfo file_0 459 6 459 9.
  Definition loc_832 : location_info := LocationInfo file_0 459 6 459 9.
  Definition loc_833 : location_info := LocationInfo file_0 459 13 459 27.
  Definition loc_834 : location_info := LocationInfo file_0 457 14 457 65.
  Definition loc_835 : location_info := LocationInfo file_0 457 14 457 48.
  Definition loc_836 : location_info := LocationInfo file_0 457 14 457 48.
  Definition loc_837 : location_info := LocationInfo file_0 457 49 457 50.
  Definition loc_838 : location_info := LocationInfo file_0 457 49 457 50.
  Definition loc_839 : location_info := LocationInfo file_0 457 52 457 57.
  Definition loc_840 : location_info := LocationInfo file_0 457 52 457 57.
  Definition loc_841 : location_info := LocationInfo file_0 457 59 457 64.
  Definition loc_842 : location_info := LocationInfo file_0 457 59 457 64.

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
        locinfo: loc_2 ;
        expr: (LocInfoE loc_62 (&(LocInfoE loc_63 ((LocInfoE loc_64 (!{void*} (LocInfoE loc_65 ("p")))) at{struct_mpool} "entry_size")))) ;
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
        LocInfoE loc_50 ("chunk") <-{ void* }
          LocInfoE loc_51 (use{void*} (LocInfoE loc_52 ("begin"))) ;
        locinfo: loc_6 ;
        LocInfoE loc_45 ((LocInfoE loc_46 (!{void*} (LocInfoE loc_47 ("chunk")))) at{struct_mpool_chunk} "size") <-{ it_layout size_t }
          LocInfoE loc_48 (use{it_layout size_t} (LocInfoE loc_49 ("size"))) ;
        locinfo: loc_7 ;
        expr: (LocInfoE loc_7 (Call (LocInfoE loc_40 (global_sl_lock)) [@{expr} LocInfoE loc_41 (&(LocInfoE loc_42 ((LocInfoE loc_43 (!{void*} (LocInfoE loc_44 ("p")))) at{struct_mpool} "lock"))) ])) ;
        locinfo: loc_8 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_35 (&(LocInfoE loc_36 ((LocInfoE loc_37 (!{void*} (LocInfoE loc_38 ("p")))) at{struct_mpool} "locked")))) ;
        locinfo: loc_10 ;
        LocInfoE loc_27 ((LocInfoE loc_28 (!{void*} (LocInfoE loc_29 ("chunk")))) at{struct_mpool_chunk} "next_chunk") <-{ void* }
          LocInfoE loc_30 (use{void*} (LocInfoE loc_31 ((LocInfoE loc_32 ((LocInfoE loc_33 (!{void*} (LocInfoE loc_34 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list"))) ;
        locinfo: loc_11 ;
        LocInfoE loc_21 ((LocInfoE loc_22 ((LocInfoE loc_23 (!{void*} (LocInfoE loc_24 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list") <-{ void* }
          LocInfoE loc_25 (use{void*} (LocInfoE loc_26 ("chunk"))) ;
        locinfo: loc_12 ;
        expr: (LocInfoE loc_12 (Call (LocInfoE loc_16 (global_sl_unlock)) [@{expr} LocInfoE loc_17 (AnnotExpr 1%nat LockA (LocInfoE loc_17 (&(LocInfoE loc_18 ((LocInfoE loc_19 (!{void*} (LocInfoE loc_20 ("p")))) at{struct_mpool} "lock"))))) ])) ;
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
        "e" <-{ void* }
          LocInfoE loc_105 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_105 (use{void*} (LocInfoE loc_106 ("ptr"))))) ;
        locinfo: loc_69 ;
        expr: (LocInfoE loc_69 (Call (LocInfoE loc_100 (global_sl_lock)) [@{expr} LocInfoE loc_101 (&(LocInfoE loc_102 ((LocInfoE loc_103 (!{void*} (LocInfoE loc_104 ("p")))) at{struct_mpool} "lock"))) ])) ;
        locinfo: loc_70 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_95 (&(LocInfoE loc_96 ((LocInfoE loc_97 (!{void*} (LocInfoE loc_98 ("p")))) at{struct_mpool} "locked")))) ;
        locinfo: loc_72 ;
        LocInfoE loc_87 ((LocInfoE loc_88 (!{void*} (LocInfoE loc_89 ("e")))) at{struct_mpool_entry} "next") <-{ void* }
          LocInfoE loc_90 (use{void*} (LocInfoE loc_91 ((LocInfoE loc_92 ((LocInfoE loc_93 (!{void*} (LocInfoE loc_94 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list"))) ;
        locinfo: loc_73 ;
        LocInfoE loc_81 ((LocInfoE loc_82 ((LocInfoE loc_83 (!{void*} (LocInfoE loc_84 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list") <-{ void* }
          LocInfoE loc_85 (use{void*} (LocInfoE loc_86 ("e"))) ;
        locinfo: loc_74 ;
        expr: (LocInfoE loc_74 (Call (LocInfoE loc_76 (global_sl_unlock)) [@{expr} LocInfoE loc_77 (AnnotExpr 1%nat LockA (LocInfoE loc_77 (&(LocInfoE loc_78 ((LocInfoE loc_79 (!{void*} (LocInfoE loc_80 ("p")))) at{struct_mpool} "lock"))))) ])) ;
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
        locinfo: loc_111 ;
        LocInfoE loc_136 ((LocInfoE loc_137 (!{void*} (LocInfoE loc_138 ("p")))) at{struct_mpool} "entry_size") <-{ it_layout size_t }
          LocInfoE loc_139 (use{it_layout size_t} (LocInfoE loc_140 ("entry_size"))) ;
        locinfo: loc_112 ;
        LocInfoE loc_131 ((LocInfoE loc_132 ((LocInfoE loc_133 (!{void*} (LocInfoE loc_134 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list") <-{ void* }
          LocInfoE loc_135 (NULL) ;
        locinfo: loc_113 ;
        LocInfoE loc_126 ((LocInfoE loc_127 ((LocInfoE loc_128 (!{void*} (LocInfoE loc_129 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list") <-{ void* }
          LocInfoE loc_130 (NULL) ;
        locinfo: loc_114 ;
        LocInfoE loc_122 ((LocInfoE loc_123 (!{void*} (LocInfoE loc_124 ("p")))) at{struct_mpool} "fallback") <-{ void* }
          LocInfoE loc_125 (NULL) ;
        locinfo: loc_115 ;
        expr: (LocInfoE loc_115 (Call (LocInfoE loc_117 (global_sl_init)) [@{expr} LocInfoE loc_118 (&(LocInfoE loc_119 ((LocInfoE loc_120 (!{void*} (LocInfoE loc_121 ("p")))) at{struct_mpool} "lock"))) ])) ;
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
        locinfo: loc_143 ;
        expr: (LocInfoE loc_143 (Call (LocInfoE loc_205 (global_mpool_init)) [@{expr} LocInfoE loc_206 (use{void*} (LocInfoE loc_207 ("p"))) ;
        LocInfoE loc_208 (use{it_layout size_t} (LocInfoE loc_209 ((LocInfoE loc_210 (!{void*} (LocInfoE loc_211 ("from")))) at{struct_mpool} "entry_size"))) ])) ;
        locinfo: loc_144 ;
        expr: (LocInfoE loc_144 (Call (LocInfoE loc_199 (global_sl_lock)) [@{expr} LocInfoE loc_200 (&(LocInfoE loc_201 ((LocInfoE loc_202 (!{void*} (LocInfoE loc_203 ("from")))) at{struct_mpool} "lock"))) ])) ;
        locinfo: loc_145 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_194 (&(LocInfoE loc_195 ((LocInfoE loc_196 (!{void*} (LocInfoE loc_197 ("from")))) at{struct_mpool} "locked")))) ;
        locinfo: loc_147 ;
        LocInfoE loc_185 ((LocInfoE loc_186 ((LocInfoE loc_187 (!{void*} (LocInfoE loc_188 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list") <-{ void* }
          LocInfoE loc_189 (use{void*} (LocInfoE loc_190 ((LocInfoE loc_191 ((LocInfoE loc_192 (!{void*} (LocInfoE loc_193 ("from")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list"))) ;
        locinfo: loc_148 ;
        LocInfoE loc_176 ((LocInfoE loc_177 ((LocInfoE loc_178 (!{void*} (LocInfoE loc_179 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list") <-{ void* }
          LocInfoE loc_180 (use{void*} (LocInfoE loc_181 ((LocInfoE loc_182 ((LocInfoE loc_183 (!{void*} (LocInfoE loc_184 ("from")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list"))) ;
        locinfo: loc_149 ;
        LocInfoE loc_169 ((LocInfoE loc_170 (!{void*} (LocInfoE loc_171 ("p")))) at{struct_mpool} "fallback") <-{ void* }
          LocInfoE loc_172 (use{void*} (LocInfoE loc_173 ((LocInfoE loc_174 (!{void*} (LocInfoE loc_175 ("from")))) at{struct_mpool} "fallback"))) ;
        locinfo: loc_150 ;
        LocInfoE loc_164 ((LocInfoE loc_165 ((LocInfoE loc_166 (!{void*} (LocInfoE loc_167 ("from")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list") <-{ void* }
          LocInfoE loc_168 (NULL) ;
        locinfo: loc_151 ;
        LocInfoE loc_159 ((LocInfoE loc_160 ((LocInfoE loc_161 (!{void*} (LocInfoE loc_162 ("from")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list") <-{ void* }
          LocInfoE loc_163 (NULL) ;
        locinfo: loc_152 ;
        expr: (LocInfoE loc_152 (Call (LocInfoE loc_154 (global_sl_unlock)) [@{expr} LocInfoE loc_155 (AnnotExpr 1%nat LockA (LocInfoE loc_155 (&(LocInfoE loc_156 ((LocInfoE loc_157 (!{void*} (LocInfoE loc_158 ("from")))) at{struct_mpool} "lock"))))) ])) ;
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
        locinfo: loc_214 ;
        expr: (LocInfoE loc_214 (Call (LocInfoE loc_222 (global_mpool_init)) [@{expr} LocInfoE loc_223 (use{void*} (LocInfoE loc_224 ("p"))) ;
        LocInfoE loc_225 (use{it_layout size_t} (LocInfoE loc_226 ((LocInfoE loc_227 (!{void*} (LocInfoE loc_228 ("fallback")))) at{struct_mpool} "entry_size"))) ])) ;
        locinfo: loc_215 ;
        LocInfoE loc_216 ((LocInfoE loc_217 (!{void*} (LocInfoE loc_218 ("p")))) at{struct_mpool} "fallback") <-{ void* }
          LocInfoE loc_219 (use{void*} (LocInfoE loc_220 ("fallback"))) ;
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
        locinfo: loc_334 ;
        if: LocInfoE loc_334 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_334 ((LocInfoE loc_335 (use{void*} (LocInfoE loc_336 ((LocInfoE loc_337 (!{void*} (LocInfoE loc_338 ("p")))) at{struct_mpool} "fallback")))) ={PtrOp, PtrOp} (LocInfoE loc_339 (NULL)))))
        then
        locinfo: loc_331 ;
          Goto "#8"
        else
        locinfo: loc_232 ;
          Goto "#9"
      ]> $
      <[ "#1" :=
        locinfo: loc_232 ;
        LocInfoE loc_324 ("entry") <-{ void* }
          LocInfoE loc_325 (use{void*} (LocInfoE loc_326 ((LocInfoE loc_327 ((LocInfoE loc_328 (!{void*} (LocInfoE loc_329 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list"))) ;
        locinfo: loc_233 ;
        LocInfoE loc_318 ("chunk") <-{ void* }
          LocInfoE loc_319 (use{void*} (LocInfoE loc_320 ((LocInfoE loc_321 ((LocInfoE loc_322 (!{void*} (LocInfoE loc_323 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list"))) ;
        locinfo: loc_234 ;
        Goto "#2"
      ]> $
      <[ "#2" :=
        locinfo: loc_314 ;
        if: LocInfoE loc_314 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_314 ((LocInfoE loc_315 (use{void*} (LocInfoE loc_316 ("entry")))) !={PtrOp, PtrOp} (LocInfoE loc_317 (NULL)))))
        then
        Goto "#3"
        else
        locinfo: loc_235 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        "ptr1" <-{ void* }
          LocInfoE loc_310 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_310 (use{void*} (LocInfoE loc_311 ("entry"))))) ;
        locinfo: loc_293 ;
        LocInfoE loc_305 ("entry") <-{ void* }
          LocInfoE loc_306 (use{void*} (LocInfoE loc_307 ((LocInfoE loc_308 (!{void*} (LocInfoE loc_309 ("entry")))) at{struct_mpool_entry} "next"))) ;
        locinfo: loc_294 ;
        expr: (LocInfoE loc_294 (Call (LocInfoE loc_298 (global_mpool_free)) [@{expr} LocInfoE loc_299 (use{void*} (LocInfoE loc_300 ((LocInfoE loc_301 (!{void*} (LocInfoE loc_302 ("p")))) at{struct_mpool} "fallback"))) ;
        LocInfoE loc_303 (use{void*} (LocInfoE loc_304 ("ptr1"))) ])) ;
        locinfo: loc_295 ;
        Goto "continue9"
      ]> $
      <[ "#4" :=
        locinfo: loc_235 ;
        Goto "#5"
      ]> $
      <[ "#5" :=
        locinfo: loc_286 ;
        if: LocInfoE loc_286 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_286 ((LocInfoE loc_287 (use{void*} (LocInfoE loc_288 ("chunk")))) !={PtrOp, PtrOp} (LocInfoE loc_289 (NULL)))))
        then
        Goto "#6"
        else
        locinfo: loc_236 ;
          Goto "#7"
      ]> $
      <[ "#6" :=
        "ptr2" <-{ void* }
          LocInfoE loc_282 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_282 (use{void*} (LocInfoE loc_283 ("chunk"))))) ;
        "size" <-{ it_layout size_t }
          LocInfoE loc_276 (use{it_layout size_t} (LocInfoE loc_277 ((LocInfoE loc_278 (!{void*} (LocInfoE loc_279 ("chunk")))) at{struct_mpool_chunk} "size"))) ;
        locinfo: loc_257 ;
        LocInfoE loc_271 ("chunk") <-{ void* }
          LocInfoE loc_272 (use{void*} (LocInfoE loc_273 ((LocInfoE loc_274 (!{void*} (LocInfoE loc_275 ("chunk")))) at{struct_mpool_chunk} "next_chunk"))) ;
        locinfo: loc_258 ;
        expr: (LocInfoE loc_258 (Call (LocInfoE loc_262 (global_mpool_add_chunk)) [@{expr} LocInfoE loc_263 (use{void*} (LocInfoE loc_264 ((LocInfoE loc_265 (!{void*} (LocInfoE loc_266 ("p")))) at{struct_mpool} "fallback"))) ;
        LocInfoE loc_267 (use{void*} (LocInfoE loc_268 ("ptr2"))) ;
        LocInfoE loc_269 (use{it_layout size_t} (LocInfoE loc_270 ("size"))) ])) ;
        locinfo: loc_259 ;
        Goto "continue11"
      ]> $
      <[ "#7" :=
        locinfo: loc_236 ;
        LocInfoE loc_248 ((LocInfoE loc_249 ((LocInfoE loc_250 (!{void*} (LocInfoE loc_251 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list") <-{ void* }
          LocInfoE loc_252 (NULL) ;
        locinfo: loc_237 ;
        LocInfoE loc_243 ((LocInfoE loc_244 ((LocInfoE loc_245 (!{void*} (LocInfoE loc_246 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list") <-{ void* }
          LocInfoE loc_247 (NULL) ;
        locinfo: loc_238 ;
        LocInfoE loc_239 ((LocInfoE loc_240 (!{void*} (LocInfoE loc_241 ("p")))) at{struct_mpool} "fallback") <-{ void* }
          LocInfoE loc_242 (NULL) ;
        Return (VOID)
      ]> $
      <[ "#8" :=
        locinfo: loc_331 ;
        Return (VOID)
      ]> $
      <[ "#9" :=
        locinfo: loc_232 ;
        Goto "#1"
      ]> $
      <[ "continue11" :=
        locinfo: loc_235 ;
        Goto "#5"
      ]> $
      <[ "continue9" :=
        locinfo: loc_234 ;
        Goto "#2"
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
        locinfo: loc_342 ;
        expr: (LocInfoE loc_342 (Call (LocInfoE loc_475 (global_sl_lock)) [@{expr} LocInfoE loc_476 (&(LocInfoE loc_477 ((LocInfoE loc_478 (!{void*} (LocInfoE loc_479 ("p")))) at{struct_mpool} "lock"))) ])) ;
        locinfo: loc_343 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_470 (&(LocInfoE loc_471 ((LocInfoE loc_472 (!{void*} (LocInfoE loc_473 ("p")))) at{struct_mpool} "locked")))) ;
        locinfo: loc_463 ;
        if: LocInfoE loc_463 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_463 ((LocInfoE loc_464 (use{void*} (LocInfoE loc_465 ((LocInfoE loc_466 ((LocInfoE loc_467 (!{void*} (LocInfoE loc_468 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list")))) !={PtrOp, PtrOp} (LocInfoE loc_469 (NULL)))))
        then
        Goto "#8"
        else
        locinfo: loc_346 ;
          Goto "#9"
      ]> $
      <[ "#1" :=
        locinfo: loc_346 ;
        LocInfoE loc_433 ("chunk") <-{ void* }
          LocInfoE loc_434 (use{void*} (LocInfoE loc_435 ((LocInfoE loc_436 ((LocInfoE loc_437 (!{void*} (LocInfoE loc_438 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list"))) ;
        locinfo: loc_429 ;
        if: LocInfoE loc_429 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_429 ((LocInfoE loc_430 (use{void*} (LocInfoE loc_431 ("chunk")))) ={PtrOp, PtrOp} (LocInfoE loc_432 (NULL)))))
        then
        locinfo: loc_424 ;
          Goto "#6"
        else
        locinfo: loc_414 ;
          Goto "#7"
      ]> $
      <[ "#2" :=
        locinfo: loc_414 ;
        if: LocInfoE loc_414 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_414 ((LocInfoE loc_415 (use{it_layout size_t} (LocInfoE loc_416 ((LocInfoE loc_417 (!{void*} (LocInfoE loc_418 ("p")))) at{struct_mpool} "entry_size")))) ≥{IntOp size_t, IntOp size_t} (LocInfoE loc_419 (use{it_layout size_t} (LocInfoE loc_420 ((LocInfoE loc_421 (!{void*} (LocInfoE loc_422 ("chunk")))) at{struct_mpool_chunk} "size")))))))
        then
        locinfo: loc_365 ;
          Goto "#4"
        else
        locinfo: loc_375 ;
          Goto "#5"
      ]> $
      <[ "#3" :=
        locinfo: loc_349 ;
        LocInfoE loc_361 ("ret") <-{ void* }
          LocInfoE loc_362 (use{void*} (LocInfoE loc_363 ("chunk"))) ;
        locinfo: loc_350 ;
        Goto "exit"
      ]> $
      <[ "#4" :=
        locinfo: loc_365 ;
        LocInfoE loc_366 ((LocInfoE loc_367 ((LocInfoE loc_368 (!{void*} (LocInfoE loc_369 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list") <-{ void* }
          LocInfoE loc_370 (use{void*} (LocInfoE loc_371 ((LocInfoE loc_372 (!{void*} (LocInfoE loc_373 ("chunk")))) at{struct_mpool_chunk} "next_chunk"))) ;
        locinfo: loc_349 ;
        Goto "#3"
      ]> $
      <[ "#5" :=
        locinfo: loc_375 ;
        LocInfoE loc_404 ("new_chunk") <-{ void* }
          LocInfoE loc_405 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_406 ((LocInfoE loc_407 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_408 (use{void*} (LocInfoE loc_409 ("chunk")))))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_410 (use{it_layout size_t} (LocInfoE loc_411 ((LocInfoE loc_412 (!{void*} (LocInfoE loc_413 ("p")))) at{struct_mpool} "entry_size"))))))) ;
        locinfo: loc_376 ;
        LocInfoE loc_397 ((LocInfoE loc_398 (!{void*} (LocInfoE loc_399 ("new_chunk")))) at{struct_mpool_chunk} "next_chunk") <-{ void* }
          LocInfoE loc_400 (use{void*} (LocInfoE loc_401 ((LocInfoE loc_402 (!{void*} (LocInfoE loc_403 ("chunk")))) at{struct_mpool_chunk} "next_chunk"))) ;
        locinfo: loc_377 ;
        LocInfoE loc_385 ((LocInfoE loc_386 (!{void*} (LocInfoE loc_387 ("new_chunk")))) at{struct_mpool_chunk} "size") <-{ it_layout size_t }
          LocInfoE loc_388 ((LocInfoE loc_389 (use{it_layout size_t} (LocInfoE loc_390 ((LocInfoE loc_391 (!{void*} (LocInfoE loc_392 ("chunk")))) at{struct_mpool_chunk} "size")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_393 (use{it_layout size_t} (LocInfoE loc_394 ((LocInfoE loc_395 (!{void*} (LocInfoE loc_396 ("p")))) at{struct_mpool} "entry_size"))))) ;
        locinfo: loc_378 ;
        LocInfoE loc_379 ((LocInfoE loc_380 ((LocInfoE loc_381 (!{void*} (LocInfoE loc_382 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list") <-{ void* }
          LocInfoE loc_383 (use{void*} (LocInfoE loc_384 ("new_chunk"))) ;
        locinfo: loc_349 ;
        Goto "#3"
      ]> $
      <[ "#6" :=
        locinfo: loc_424 ;
        LocInfoE loc_426 ("ret") <-{ void* } LocInfoE loc_427 (NULL) ;
        locinfo: loc_425 ;
        Goto "exit"
      ]> $
      <[ "#7" :=
        locinfo: loc_414 ;
        Goto "#2"
      ]> $
      <[ "#8" :=
        "entry" <-{ void* }
          LocInfoE loc_455 (use{void*} (LocInfoE loc_456 ((LocInfoE loc_457 ((LocInfoE loc_458 (!{void*} (LocInfoE loc_459 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list"))) ;
        locinfo: loc_441 ;
        LocInfoE loc_447 ((LocInfoE loc_448 ((LocInfoE loc_449 (!{void*} (LocInfoE loc_450 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list") <-{ void* }
          LocInfoE loc_451 (use{void*} (LocInfoE loc_452 ((LocInfoE loc_453 (!{void*} (LocInfoE loc_454 ("entry")))) at{struct_mpool_entry} "next"))) ;
        locinfo: loc_442 ;
        LocInfoE loc_444 ("ret") <-{ void* }
          LocInfoE loc_445 (use{void*} (LocInfoE loc_446 ("entry"))) ;
        locinfo: loc_443 ;
        Goto "exit"
      ]> $
      <[ "#9" :=
        locinfo: loc_346 ;
        Goto "#1"
      ]> $
      <[ "exit" :=
        locinfo: loc_351 ;
        expr: (LocInfoE loc_351 (Call (LocInfoE loc_356 (global_sl_unlock)) [@{expr} LocInfoE loc_357 (AnnotExpr 1%nat LockA (LocInfoE loc_357 (&(LocInfoE loc_358 ((LocInfoE loc_359 (!{void*} (LocInfoE loc_360 ("p")))) at{struct_mpool} "lock"))))) ])) ;
        locinfo: loc_352 ;
        Return (LocInfoE loc_353 (use{void*} (LocInfoE loc_354 ("ret"))))
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
        "ret" <-{ void* }
          LocInfoE loc_533 (Call (LocInfoE loc_535 (global_mpool_alloc_no_fallback)) [@{expr} LocInfoE loc_536 (use{void*} (LocInfoE loc_537 ("p"))) ]) ;
        locinfo: loc_529 ;
        if: LocInfoE loc_529 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_529 ((LocInfoE loc_530 (use{void*} (LocInfoE loc_531 ("ret")))) !={PtrOp, PtrOp} (LocInfoE loc_532 (NULL)))))
        then
        locinfo: loc_525 ;
          Goto "#8"
        else
        locinfo: loc_484 ;
          Goto "#9"
      ]> $
      <[ "#1" :=
        locinfo: loc_484 ;
        LocInfoE loc_519 ("p") <-{ void* }
          LocInfoE loc_520 (use{void*} (LocInfoE loc_521 ((LocInfoE loc_522 (!{void*} (LocInfoE loc_523 ("p")))) at{struct_mpool} "fallback"))) ;
        locinfo: loc_485 ;
        Goto "#2"
      ]> $
      <[ "#2" :=
        locinfo: loc_515 ;
        if: LocInfoE loc_515 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_515 ((LocInfoE loc_516 (use{void*} (LocInfoE loc_517 ("p")))) !={PtrOp, PtrOp} (LocInfoE loc_518 (NULL)))))
        then
        locinfo: loc_490 ;
          Goto "#3"
        else
        locinfo: loc_486 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_490 ;
        LocInfoE loc_509 ("ret") <-{ void* }
          LocInfoE loc_510 (Call (LocInfoE loc_512 (global_mpool_alloc_no_fallback)) [@{expr} LocInfoE loc_513 (use{void*} (LocInfoE loc_514 ("p"))) ]) ;
        locinfo: loc_505 ;
        if: LocInfoE loc_505 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_505 ((LocInfoE loc_506 (use{void*} (LocInfoE loc_507 ("ret")))) !={PtrOp, PtrOp} (LocInfoE loc_508 (NULL)))))
        then
        locinfo: loc_501 ;
          Goto "#6"
        else
        locinfo: loc_492 ;
          Goto "#7"
      ]> $
      <[ "#4" :=
        locinfo: loc_486 ;
        Return (LocInfoE loc_487 (NULL))
      ]> $
      <[ "#5" :=
        locinfo: loc_492 ;
        LocInfoE loc_495 ("p") <-{ void* }
          LocInfoE loc_496 (use{void*} (LocInfoE loc_497 ((LocInfoE loc_498 (!{void*} (LocInfoE loc_499 ("p")))) at{struct_mpool} "fallback"))) ;
        locinfo: loc_493 ;
        Goto "continue25"
      ]> $
      <[ "#6" :=
        locinfo: loc_501 ;
        Return (LocInfoE loc_502 (use{void*} (LocInfoE loc_503 ("ret"))))
      ]> $
      <[ "#7" :=
        locinfo: loc_492 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        locinfo: loc_525 ;
        Return (LocInfoE loc_526 (use{void*} (LocInfoE loc_527 ("ret"))))
      ]> $
      <[ "#9" :=
        locinfo: loc_484 ;
        Goto "#1"
      ]> $
      <[ "continue25" :=
        locinfo: loc_485 ;
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
        "ret" <-{ void* } LocInfoE loc_774 (NULL) ;
        locinfo: loc_543 ;
        LocInfoE loc_766 ("align") <-{ it_layout size_t }
          LocInfoE loc_767 ((LocInfoE loc_768 (use{it_layout size_t} (LocInfoE loc_769 ("align")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_770 (use{it_layout size_t} (LocInfoE loc_771 ((LocInfoE loc_772 (!{void*} (LocInfoE loc_773 ("p")))) at{struct_mpool} "entry_size"))))) ;
        locinfo: loc_544 ;
        expr: (LocInfoE loc_544 (Call (LocInfoE loc_761 (global_sl_lock)) [@{expr} LocInfoE loc_762 (&(LocInfoE loc_763 ((LocInfoE loc_764 (!{void*} (LocInfoE loc_765 ("p")))) at{struct_mpool} "lock"))) ])) ;
        locinfo: loc_545 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_756 (&(LocInfoE loc_757 ((LocInfoE loc_758 (!{void*} (LocInfoE loc_759 ("p")))) at{struct_mpool} "locked")))) ;
        locinfo: loc_547 ;
        LocInfoE loc_750 ("prev") <-{ void* }
          LocInfoE loc_751 (&(LocInfoE loc_752 ((LocInfoE loc_753 ((LocInfoE loc_754 (!{void*} (LocInfoE loc_755 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list"))) ;
        locinfo: loc_548 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_744 ;
        if: LocInfoE loc_744 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_744 ((LocInfoE loc_745 (use{void*} (LocInfoE loc_747 (!{void*} (LocInfoE loc_748 ("prev")))))) !={PtrOp, PtrOp} (LocInfoE loc_749 (NULL)))))
        then
        Goto "#2"
        else
        locinfo: loc_549 ;
          Goto "#3"
      ]> $
      <[ "#10" :=
        locinfo: loc_624 ;
        LocInfoE loc_626 (!{void*} (LocInfoE loc_627 ("prev"))) <-{ void* }
          LocInfoE loc_628 (use{void*} (LocInfoE loc_629 ("chunk_next"))) ;
        locinfo: loc_616 ;
        Goto "#6"
      ]> $
      <[ "#11" :=
        locinfo: loc_631 ;
        LocInfoE loc_661 ("new_chunk") <-{ void* }
          LocInfoE loc_662 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_663 ((LocInfoE loc_664 (use{void*} (LocInfoE loc_665 ("start")))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_666 ((LocInfoE loc_667 (use{it_layout size_t} (LocInfoE loc_668 ("count")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_669 (use{it_layout size_t} (LocInfoE loc_670 ((LocInfoE loc_671 (!{void*} (LocInfoE loc_672 ("p")))) at{struct_mpool} "entry_size"))))))))) ;
        locinfo: loc_632 ;
        LocInfoE loc_645 ((LocInfoE loc_646 (!{void*} (LocInfoE loc_647 ("new_chunk")))) at{struct_mpool_chunk} "size") <-{ it_layout size_t }
          LocInfoE loc_648 ((LocInfoE loc_649 (use{it_layout size_t} (LocInfoE loc_650 ("chunk_size")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_651 ((LocInfoE loc_652 (use{it_layout size_t} (LocInfoE loc_653 ("before_start")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_654 ((LocInfoE loc_655 (use{it_layout size_t} (LocInfoE loc_656 ("count")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_657 (use{it_layout size_t} (LocInfoE loc_658 ((LocInfoE loc_659 (!{void*} (LocInfoE loc_660 ("p")))) at{struct_mpool} "entry_size"))))))))) ;
        locinfo: loc_633 ;
        LocInfoE loc_640 ((LocInfoE loc_641 (!{void*} (LocInfoE loc_642 ("new_chunk")))) at{struct_mpool_chunk} "next_chunk") <-{ void* }
          LocInfoE loc_643 (use{void*} (LocInfoE loc_644 ("chunk_next"))) ;
        locinfo: loc_634 ;
        LocInfoE loc_636 (!{void*} (LocInfoE loc_637 ("prev"))) <-{ void* }
          LocInfoE loc_638 (use{void*} (LocInfoE loc_639 ("new_chunk"))) ;
        locinfo: loc_616 ;
        Goto "#6"
      ]> $
      <[ "#12" :=
        locinfo: loc_566 ;
        Goto "#4"
      ]> $
      <[ "#2" :=
        "chunk" <-{ void* }
          LocInfoE loc_738 (use{void*} (LocInfoE loc_740 (!{void*} (LocInfoE loc_741 ("prev"))))) ;
        locinfo: loc_562 ;
        annot: (LearnAlignmentAnnot) ;
        expr: (LocInfoE loc_734 (&(LocInfoE loc_736 (!{void*} (LocInfoE loc_737 ("chunk")))))) ;
        locinfo: loc_564 ;
        expr: (LocInfoE loc_564 (Call (LocInfoE loc_726 (global_round_pointer_up)) [@{expr} LocInfoE loc_727 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_728 (use{void*} (LocInfoE loc_729 ("chunk"))))) ;
        LocInfoE loc_730 (use{it_layout size_t} (LocInfoE loc_731 ("align"))) ;
        LocInfoE loc_732 (&(LocInfoE loc_733 ("before_start"))) ])) ;
        locinfo: loc_710 ;
        if: LocInfoE loc_710 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_710 ((LocInfoE loc_711 ((LocInfoE loc_712 (use{it_layout size_t} (LocInfoE loc_713 ("before_start")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_714 ((LocInfoE loc_715 (use{it_layout size_t} (LocInfoE loc_716 ("count")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_717 (use{it_layout size_t} (LocInfoE loc_718 ((LocInfoE loc_719 (!{void*} (LocInfoE loc_720 ("p")))) at{struct_mpool} "entry_size")))))))) ≤{IntOp size_t, IntOp size_t} (LocInfoE loc_721 (use{it_layout size_t} (LocInfoE loc_722 ((LocInfoE loc_723 (!{void*} (LocInfoE loc_724 ("chunk")))) at{struct_mpool_chunk} "size")))))))
        then
        Goto "#5"
        else
        locinfo: loc_566 ;
          Goto "#12"
      ]> $
      <[ "#3" :=
        locinfo: loc_549 ;
        expr: (LocInfoE loc_549 (Call (LocInfoE loc_554 (global_sl_unlock)) [@{expr} LocInfoE loc_555 (AnnotExpr 1%nat LockA (LocInfoE loc_555 (&(LocInfoE loc_556 ((LocInfoE loc_557 (!{void*} (LocInfoE loc_558 ("p")))) at{struct_mpool} "lock"))))) ])) ;
        locinfo: loc_550 ;
        Return (LocInfoE loc_551 (use{void*} (LocInfoE loc_552 ("ret"))))
      ]> $
      <[ "#4" :=
        locinfo: loc_566 ;
        LocInfoE loc_569 ("prev") <-{ void* }
          LocInfoE loc_570 (&(LocInfoE loc_571 ((LocInfoE loc_572 (!{void*} (LocInfoE loc_573 ("chunk")))) at{struct_mpool_chunk} "next_chunk"))) ;
        locinfo: loc_567 ;
        Goto "continue32"
      ]> $
      <[ "#5" :=
        "chunk_size" <-{ it_layout size_t }
          LocInfoE loc_703 (use{it_layout size_t} (LocInfoE loc_704 ((LocInfoE loc_705 (!{void*} (LocInfoE loc_706 ("chunk")))) at{struct_mpool_chunk} "size"))) ;
        "chunk_next" <-{ void* }
          LocInfoE loc_697 (use{void*} (LocInfoE loc_698 ((LocInfoE loc_699 (!{void*} (LocInfoE loc_700 ("chunk")))) at{struct_mpool_chunk} "next_chunk"))) ;
        locinfo: loc_577 ;
        annot: (ToUninit) ;
        expr: (LocInfoE loc_693 (&(LocInfoE loc_695 (!{void*} (LocInfoE loc_696 ("chunk")))))) ;
        locinfo: loc_579 ;
        LocInfoE loc_686 ("start") <-{ void* }
          LocInfoE loc_687 ((LocInfoE loc_688 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_689 (use{void*} (LocInfoE loc_690 ("chunk")))))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_691 (use{it_layout size_t} (LocInfoE loc_692 ("before_start"))))) ;
        locinfo: loc_673 ;
        if: LocInfoE loc_673 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_673 ((LocInfoE loc_674 ((LocInfoE loc_675 (use{it_layout size_t} (LocInfoE loc_676 ("before_start")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_677 ((LocInfoE loc_678 (use{it_layout size_t} (LocInfoE loc_679 ("count")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_680 (use{it_layout size_t} (LocInfoE loc_681 ((LocInfoE loc_682 (!{void*} (LocInfoE loc_683 ("p")))) at{struct_mpool} "entry_size")))))))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_684 (use{it_layout size_t} (LocInfoE loc_685 ("chunk_size")))))))
        then
        locinfo: loc_624 ;
          Goto "#10"
        else
        locinfo: loc_631 ;
          Goto "#11"
      ]> $
      <[ "#6" :=
        locinfo: loc_616 ;
        if: LocInfoE loc_616 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_616 ((LocInfoE loc_617 (use{it_layout size_t} (LocInfoE loc_618 ("before_start")))) ≥{IntOp size_t, IntOp size_t} (LocInfoE loc_619 (use{it_layout size_t} (LocInfoE loc_620 ((LocInfoE loc_621 (!{void*} (LocInfoE loc_622 ("p")))) at{struct_mpool} "entry_size")))))))
        then
        locinfo: loc_595 ;
          Goto "#8"
        else
        locinfo: loc_582 ;
          Goto "#9"
      ]> $
      <[ "#7" :=
        locinfo: loc_582 ;
        annot: (UninitStrengthenAlign) ;
        expr: (LocInfoE loc_590 (&(LocInfoE loc_592 (!{void*} (LocInfoE loc_593 ("start")))))) ;
        locinfo: loc_584 ;
        LocInfoE loc_586 ("ret") <-{ void* }
          LocInfoE loc_587 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_588 (use{void*} (LocInfoE loc_589 ("start"))))) ;
        locinfo: loc_549 ;
        Goto "#3"
      ]> $
      <[ "#8" :=
        locinfo: loc_595 ;
        LocInfoE loc_608 ((LocInfoE loc_609 (!{void*} (LocInfoE loc_610 ("chunk")))) at{struct_mpool_chunk} "next_chunk") <-{ void* }
          LocInfoE loc_611 (use{void*} (LocInfoE loc_613 (!{void*} (LocInfoE loc_614 ("prev"))))) ;
        locinfo: loc_596 ;
        LocInfoE loc_604 (!{void*} (LocInfoE loc_605 ("prev"))) <-{ void* }
          LocInfoE loc_606 (use{void*} (LocInfoE loc_607 ("chunk"))) ;
        locinfo: loc_597 ;
        LocInfoE loc_598 ((LocInfoE loc_599 (!{void*} (LocInfoE loc_600 ("chunk")))) at{struct_mpool_chunk} "size") <-{ it_layout size_t }
          LocInfoE loc_601 (use{it_layout size_t} (LocInfoE loc_602 ("before_start"))) ;
        locinfo: loc_582 ;
        Goto "#7"
      ]> $
      <[ "#9" :=
        locinfo: loc_582 ;
        Goto "#7"
      ]> $
      <[ "continue32" :=
        locinfo: loc_548 ;
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
        "ret" <-{ void* }
          LocInfoE loc_834 (Call (LocInfoE loc_836 (global_mpool_alloc_contiguous_no_fallback)) [@{expr} LocInfoE loc_837 (use{void*} (LocInfoE loc_838 ("p"))) ;
          LocInfoE loc_839 (use{it_layout size_t} (LocInfoE loc_840 ("count"))) ;
          LocInfoE loc_841 (use{it_layout size_t} (LocInfoE loc_842 ("align"))) ]) ;
        locinfo: loc_830 ;
        if: LocInfoE loc_830 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_830 ((LocInfoE loc_831 (use{void*} (LocInfoE loc_832 ("ret")))) !={PtrOp, PtrOp} (LocInfoE loc_833 (NULL)))))
        then
        locinfo: loc_826 ;
          Goto "#8"
        else
        locinfo: loc_781 ;
          Goto "#9"
      ]> $
      <[ "#1" :=
        locinfo: loc_781 ;
        LocInfoE loc_820 ("p") <-{ void* }
          LocInfoE loc_821 (use{void*} (LocInfoE loc_822 ((LocInfoE loc_823 (!{void*} (LocInfoE loc_824 ("p")))) at{struct_mpool} "fallback"))) ;
        locinfo: loc_782 ;
        Goto "#2"
      ]> $
      <[ "#2" :=
        locinfo: loc_816 ;
        if: LocInfoE loc_816 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_816 ((LocInfoE loc_817 (use{void*} (LocInfoE loc_818 ("p")))) !={PtrOp, PtrOp} (LocInfoE loc_819 (NULL)))))
        then
        locinfo: loc_787 ;
          Goto "#3"
        else
        locinfo: loc_783 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_787 ;
        LocInfoE loc_806 ("ret") <-{ void* }
          LocInfoE loc_807 (Call (LocInfoE loc_809 (global_mpool_alloc_contiguous_no_fallback)) [@{expr} LocInfoE loc_810 (use{void*} (LocInfoE loc_811 ("p"))) ;
          LocInfoE loc_812 (use{it_layout size_t} (LocInfoE loc_813 ("count"))) ;
          LocInfoE loc_814 (use{it_layout size_t} (LocInfoE loc_815 ("align"))) ]) ;
        locinfo: loc_802 ;
        if: LocInfoE loc_802 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_802 ((LocInfoE loc_803 (use{void*} (LocInfoE loc_804 ("ret")))) !={PtrOp, PtrOp} (LocInfoE loc_805 (NULL)))))
        then
        locinfo: loc_798 ;
          Goto "#6"
        else
        locinfo: loc_789 ;
          Goto "#7"
      ]> $
      <[ "#4" :=
        locinfo: loc_783 ;
        Return (LocInfoE loc_784 (NULL))
      ]> $
      <[ "#5" :=
        locinfo: loc_789 ;
        LocInfoE loc_792 ("p") <-{ void* }
          LocInfoE loc_793 (use{void*} (LocInfoE loc_794 ((LocInfoE loc_795 (!{void*} (LocInfoE loc_796 ("p")))) at{struct_mpool} "fallback"))) ;
        locinfo: loc_790 ;
        Goto "continue41"
      ]> $
      <[ "#6" :=
        locinfo: loc_798 ;
        Return (LocInfoE loc_799 (use{void*} (LocInfoE loc_800 ("ret"))))
      ]> $
      <[ "#7" :=
        locinfo: loc_789 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        locinfo: loc_826 ;
        Return (LocInfoE loc_827 (use{void*} (LocInfoE loc_828 ("ret"))))
      ]> $
      <[ "#9" :=
        locinfo: loc_781 ;
        Goto "#1"
      ]> $
      <[ "continue41" :=
        locinfo: loc_782 ;
        Goto "#2"
      ]> $∅
    )%E
  |}.
End code.
