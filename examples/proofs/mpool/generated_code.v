From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/mpool.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "examples/mpool.c".
  Definition loc_2 : location_info := LocationInfo file_0 63 2 63 47.
  Definition loc_3 : location_info := LocationInfo file_0 63 9 63 46.
  Definition loc_4 : location_info := LocationInfo file_0 63 9 63 32.
  Definition loc_5 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_6 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_7 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_8 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_11 : location_info := LocationInfo file_1 224 2 224 28.
  Definition loc_12 : location_info := LocationInfo file_1 226 2 226 19.
  Definition loc_13 : location_info := LocationInfo file_1 226 19 226 3.
  Definition loc_14 : location_info := LocationInfo file_1 229 2 231 3.
  Definition loc_15 : location_info := LocationInfo file_1 233 2 233 16.
  Definition loc_16 : location_info := LocationInfo file_1 234 2 234 21.
  Definition loc_17 : location_info := LocationInfo file_1 236 2 236 20.
  Definition loc_18 : location_info := LocationInfo file_1 237 2 237 40.
  Definition loc_19 : location_info := LocationInfo file_1 237 40 237 3.
  Definition loc_20 : location_info := LocationInfo file_1 238 2 238 43.
  Definition loc_21 : location_info := LocationInfo file_1 239 2 239 31.
  Definition loc_22 : location_info := LocationInfo file_1 240 2 240 22.
  Definition loc_23 : location_info := LocationInfo file_1 242 2 242 11.
  Definition loc_24 : location_info := LocationInfo file_1 242 9 242 10.
  Definition loc_25 : location_info := LocationInfo file_1 240 2 240 11.
  Definition loc_26 : location_info := LocationInfo file_1 240 2 240 11.
  Definition loc_27 : location_info := LocationInfo file_1 240 12 240 20.
  Definition loc_28 : location_info := LocationInfo file_1 240 13 240 20.
  Definition loc_29 : location_info := LocationInfo file_1 240 13 240 14.
  Definition loc_30 : location_info := LocationInfo file_1 240 13 240 14.
  Definition loc_31 : location_info := LocationInfo file_1 239 2 239 22.
  Definition loc_32 : location_info := LocationInfo file_1 239 2 239 11.
  Definition loc_33 : location_info := LocationInfo file_1 239 2 239 3.
  Definition loc_34 : location_info := LocationInfo file_1 239 2 239 3.
  Definition loc_35 : location_info := LocationInfo file_1 239 25 239 30.
  Definition loc_36 : location_info := LocationInfo file_1 239 25 239 30.
  Definition loc_37 : location_info := LocationInfo file_1 238 2 238 19.
  Definition loc_38 : location_info := LocationInfo file_1 238 2 238 7.
  Definition loc_39 : location_info := LocationInfo file_1 238 2 238 7.
  Definition loc_40 : location_info := LocationInfo file_1 238 22 238 42.
  Definition loc_41 : location_info := LocationInfo file_1 238 22 238 42.
  Definition loc_42 : location_info := LocationInfo file_1 238 22 238 31.
  Definition loc_43 : location_info := LocationInfo file_1 238 22 238 23.
  Definition loc_44 : location_info := LocationInfo file_1 238 22 238 23.
  Definition loc_45 : location_info := LocationInfo file_1 237 27 237 39.
  Definition loc_46 : location_info := LocationInfo file_1 237 28 237 39.
  Definition loc_47 : location_info := LocationInfo file_1 237 29 237 30.
  Definition loc_48 : location_info := LocationInfo file_1 237 29 237 30.
  Definition loc_49 : location_info := LocationInfo file_1 236 2 236 9.
  Definition loc_50 : location_info := LocationInfo file_1 236 2 236 9.
  Definition loc_51 : location_info := LocationInfo file_1 236 10 236 18.
  Definition loc_52 : location_info := LocationInfo file_1 236 11 236 18.
  Definition loc_53 : location_info := LocationInfo file_1 236 11 236 12.
  Definition loc_54 : location_info := LocationInfo file_1 236 11 236 12.
  Definition loc_55 : location_info := LocationInfo file_1 234 2 234 13.
  Definition loc_56 : location_info := LocationInfo file_1 234 2 234 7.
  Definition loc_57 : location_info := LocationInfo file_1 234 2 234 7.
  Definition loc_58 : location_info := LocationInfo file_1 234 16 234 20.
  Definition loc_59 : location_info := LocationInfo file_1 234 16 234 20.
  Definition loc_60 : location_info := LocationInfo file_1 233 2 233 7.
  Definition loc_61 : location_info := LocationInfo file_1 233 10 233 15.
  Definition loc_62 : location_info := LocationInfo file_1 233 10 233 15.
  Definition loc_63 : location_info := LocationInfo file_1 229 26 231 3.
  Definition loc_64 : location_info := LocationInfo file_1 230 4 230 13.
  Definition loc_65 : location_info := LocationInfo file_1 230 11 230 12.
  Definition loc_66 : location_info := LocationInfo file_1 229 2 231 3.
  Definition loc_67 : location_info := LocationInfo file_1 229 6 229 24.
  Definition loc_68 : location_info := LocationInfo file_1 229 6 229 10.
  Definition loc_69 : location_info := LocationInfo file_1 229 6 229 10.
  Definition loc_70 : location_info := LocationInfo file_1 229 14 229 24.
  Definition loc_71 : location_info := LocationInfo file_1 229 23 229 24.
  Definition loc_72 : location_info := LocationInfo file_1 226 2 226 18.
  Definition loc_73 : location_info := LocationInfo file_1 226 3 226 18.
  Definition loc_74 : location_info := LocationInfo file_1 226 4 226 5.
  Definition loc_75 : location_info := LocationInfo file_1 226 4 226 5.
  Definition loc_78 : location_info := LocationInfo file_1 338 2 338 30.
  Definition loc_79 : location_info := LocationInfo file_1 341 2 341 20.
  Definition loc_80 : location_info := LocationInfo file_1 342 2 342 40.
  Definition loc_81 : location_info := LocationInfo file_1 342 40 342 3.
  Definition loc_82 : location_info := LocationInfo file_1 343 2 343 33.
  Definition loc_83 : location_info := LocationInfo file_1 344 2 344 27.
  Definition loc_84 : location_info := LocationInfo file_1 345 2 345 22.
  Definition loc_85 : location_info := LocationInfo file_1 345 2 345 11.
  Definition loc_86 : location_info := LocationInfo file_1 345 2 345 11.
  Definition loc_87 : location_info := LocationInfo file_1 345 12 345 20.
  Definition loc_88 : location_info := LocationInfo file_1 345 13 345 20.
  Definition loc_89 : location_info := LocationInfo file_1 345 13 345 14.
  Definition loc_90 : location_info := LocationInfo file_1 345 13 345 14.
  Definition loc_91 : location_info := LocationInfo file_1 344 2 344 22.
  Definition loc_92 : location_info := LocationInfo file_1 344 2 344 11.
  Definition loc_93 : location_info := LocationInfo file_1 344 2 344 3.
  Definition loc_94 : location_info := LocationInfo file_1 344 2 344 3.
  Definition loc_95 : location_info := LocationInfo file_1 344 25 344 26.
  Definition loc_96 : location_info := LocationInfo file_1 344 25 344 26.
  Definition loc_97 : location_info := LocationInfo file_1 343 2 343 9.
  Definition loc_98 : location_info := LocationInfo file_1 343 2 343 3.
  Definition loc_99 : location_info := LocationInfo file_1 343 2 343 3.
  Definition loc_100 : location_info := LocationInfo file_1 343 12 343 32.
  Definition loc_101 : location_info := LocationInfo file_1 343 12 343 32.
  Definition loc_102 : location_info := LocationInfo file_1 343 12 343 21.
  Definition loc_103 : location_info := LocationInfo file_1 343 12 343 13.
  Definition loc_104 : location_info := LocationInfo file_1 343 12 343 13.
  Definition loc_105 : location_info := LocationInfo file_1 342 27 342 39.
  Definition loc_106 : location_info := LocationInfo file_1 342 28 342 39.
  Definition loc_107 : location_info := LocationInfo file_1 342 29 342 30.
  Definition loc_108 : location_info := LocationInfo file_1 342 29 342 30.
  Definition loc_109 : location_info := LocationInfo file_1 341 2 341 9.
  Definition loc_110 : location_info := LocationInfo file_1 341 2 341 9.
  Definition loc_111 : location_info := LocationInfo file_1 341 10 341 18.
  Definition loc_112 : location_info := LocationInfo file_1 341 11 341 18.
  Definition loc_113 : location_info := LocationInfo file_1 341 11 341 12.
  Definition loc_114 : location_info := LocationInfo file_1 341 11 341 12.
  Definition loc_115 : location_info := LocationInfo file_1 338 26 338 29.
  Definition loc_116 : location_info := LocationInfo file_1 338 26 338 29.
  Definition loc_121 : location_info := LocationInfo file_1 113 2 113 29.
  Definition loc_122 : location_info := LocationInfo file_1 114 2 114 40.
  Definition loc_123 : location_info := LocationInfo file_1 115 2 115 40.
  Definition loc_124 : location_info := LocationInfo file_1 116 2 116 31.
  Definition loc_125 : location_info := LocationInfo file_1 117 2 117 20.
  Definition loc_126 : location_info := LocationInfo file_1 117 2 117 9.
  Definition loc_127 : location_info := LocationInfo file_1 117 2 117 9.
  Definition loc_128 : location_info := LocationInfo file_1 117 10 117 18.
  Definition loc_129 : location_info := LocationInfo file_1 117 11 117 18.
  Definition loc_130 : location_info := LocationInfo file_1 117 11 117 12.
  Definition loc_131 : location_info := LocationInfo file_1 117 11 117 12.
  Definition loc_132 : location_info := LocationInfo file_1 116 2 116 13.
  Definition loc_133 : location_info := LocationInfo file_1 116 2 116 3.
  Definition loc_134 : location_info := LocationInfo file_1 116 2 116 3.
  Definition loc_135 : location_info := LocationInfo file_1 116 16 116 30.
  Definition loc_136 : location_info := LocationInfo file_1 115 2 115 22.
  Definition loc_137 : location_info := LocationInfo file_1 115 2 115 11.
  Definition loc_138 : location_info := LocationInfo file_1 115 2 115 3.
  Definition loc_139 : location_info := LocationInfo file_1 115 2 115 3.
  Definition loc_140 : location_info := LocationInfo file_1 115 25 115 39.
  Definition loc_141 : location_info := LocationInfo file_1 114 2 114 22.
  Definition loc_142 : location_info := LocationInfo file_1 114 2 114 11.
  Definition loc_143 : location_info := LocationInfo file_1 114 2 114 3.
  Definition loc_144 : location_info := LocationInfo file_1 114 2 114 3.
  Definition loc_145 : location_info := LocationInfo file_1 114 25 114 39.
  Definition loc_146 : location_info := LocationInfo file_1 113 2 113 15.
  Definition loc_147 : location_info := LocationInfo file_1 113 2 113 3.
  Definition loc_148 : location_info := LocationInfo file_1 113 2 113 3.
  Definition loc_149 : location_info := LocationInfo file_1 113 18 113 28.
  Definition loc_150 : location_info := LocationInfo file_1 113 18 113 28.
  Definition loc_153 : location_info := LocationInfo file_1 132 2 132 34.
  Definition loc_154 : location_info := LocationInfo file_1 134 2 134 23.
  Definition loc_155 : location_info := LocationInfo file_1 135 2 135 43.
  Definition loc_156 : location_info := LocationInfo file_1 135 43 135 3.
  Definition loc_157 : location_info := LocationInfo file_1 137 2 137 49.
  Definition loc_158 : location_info := LocationInfo file_1 138 2 138 49.
  Definition loc_159 : location_info := LocationInfo file_1 139 2 139 31.
  Definition loc_160 : location_info := LocationInfo file_1 141 2 141 43.
  Definition loc_161 : location_info := LocationInfo file_1 142 2 142 43.
  Definition loc_162 : location_info := LocationInfo file_1 145 2 145 25.
  Definition loc_163 : location_info := LocationInfo file_1 145 2 145 11.
  Definition loc_164 : location_info := LocationInfo file_1 145 2 145 11.
  Definition loc_165 : location_info := LocationInfo file_1 145 12 145 23.
  Definition loc_166 : location_info := LocationInfo file_1 145 13 145 23.
  Definition loc_167 : location_info := LocationInfo file_1 145 13 145 17.
  Definition loc_168 : location_info := LocationInfo file_1 145 13 145 17.
  Definition loc_169 : location_info := LocationInfo file_1 142 2 142 25.
  Definition loc_170 : location_info := LocationInfo file_1 142 2 142 14.
  Definition loc_171 : location_info := LocationInfo file_1 142 2 142 6.
  Definition loc_172 : location_info := LocationInfo file_1 142 2 142 6.
  Definition loc_173 : location_info := LocationInfo file_1 142 28 142 42.
  Definition loc_174 : location_info := LocationInfo file_1 141 2 141 25.
  Definition loc_175 : location_info := LocationInfo file_1 141 2 141 14.
  Definition loc_176 : location_info := LocationInfo file_1 141 2 141 6.
  Definition loc_177 : location_info := LocationInfo file_1 141 2 141 6.
  Definition loc_178 : location_info := LocationInfo file_1 141 28 141 42.
  Definition loc_179 : location_info := LocationInfo file_1 139 2 139 13.
  Definition loc_180 : location_info := LocationInfo file_1 139 2 139 3.
  Definition loc_181 : location_info := LocationInfo file_1 139 2 139 3.
  Definition loc_182 : location_info := LocationInfo file_1 139 16 139 30.
  Definition loc_183 : location_info := LocationInfo file_1 139 16 139 30.
  Definition loc_184 : location_info := LocationInfo file_1 139 16 139 20.
  Definition loc_185 : location_info := LocationInfo file_1 139 16 139 20.
  Definition loc_186 : location_info := LocationInfo file_1 138 2 138 22.
  Definition loc_187 : location_info := LocationInfo file_1 138 2 138 11.
  Definition loc_188 : location_info := LocationInfo file_1 138 2 138 3.
  Definition loc_189 : location_info := LocationInfo file_1 138 2 138 3.
  Definition loc_190 : location_info := LocationInfo file_1 138 25 138 48.
  Definition loc_191 : location_info := LocationInfo file_1 138 25 138 48.
  Definition loc_192 : location_info := LocationInfo file_1 138 25 138 37.
  Definition loc_193 : location_info := LocationInfo file_1 138 25 138 29.
  Definition loc_194 : location_info := LocationInfo file_1 138 25 138 29.
  Definition loc_195 : location_info := LocationInfo file_1 137 2 137 22.
  Definition loc_196 : location_info := LocationInfo file_1 137 2 137 11.
  Definition loc_197 : location_info := LocationInfo file_1 137 2 137 3.
  Definition loc_198 : location_info := LocationInfo file_1 137 2 137 3.
  Definition loc_199 : location_info := LocationInfo file_1 137 25 137 48.
  Definition loc_200 : location_info := LocationInfo file_1 137 25 137 48.
  Definition loc_201 : location_info := LocationInfo file_1 137 25 137 37.
  Definition loc_202 : location_info := LocationInfo file_1 137 25 137 29.
  Definition loc_203 : location_info := LocationInfo file_1 137 25 137 29.
  Definition loc_204 : location_info := LocationInfo file_1 135 27 135 42.
  Definition loc_205 : location_info := LocationInfo file_1 135 28 135 42.
  Definition loc_206 : location_info := LocationInfo file_1 135 29 135 33.
  Definition loc_207 : location_info := LocationInfo file_1 135 29 135 33.
  Definition loc_208 : location_info := LocationInfo file_1 134 2 134 9.
  Definition loc_209 : location_info := LocationInfo file_1 134 2 134 9.
  Definition loc_210 : location_info := LocationInfo file_1 134 10 134 21.
  Definition loc_211 : location_info := LocationInfo file_1 134 11 134 21.
  Definition loc_212 : location_info := LocationInfo file_1 134 11 134 15.
  Definition loc_213 : location_info := LocationInfo file_1 134 11 134 15.
  Definition loc_214 : location_info := LocationInfo file_1 132 2 132 12.
  Definition loc_215 : location_info := LocationInfo file_1 132 2 132 12.
  Definition loc_216 : location_info := LocationInfo file_1 132 13 132 14.
  Definition loc_217 : location_info := LocationInfo file_1 132 13 132 14.
  Definition loc_218 : location_info := LocationInfo file_1 132 16 132 32.
  Definition loc_219 : location_info := LocationInfo file_1 132 16 132 32.
  Definition loc_220 : location_info := LocationInfo file_1 132 16 132 20.
  Definition loc_221 : location_info := LocationInfo file_1 132 16 132 20.
  Definition loc_224 : location_info := LocationInfo file_1 157 2 157 38.
  Definition loc_225 : location_info := LocationInfo file_1 158 2 158 25.
  Definition loc_226 : location_info := LocationInfo file_1 158 2 158 13.
  Definition loc_227 : location_info := LocationInfo file_1 158 2 158 3.
  Definition loc_228 : location_info := LocationInfo file_1 158 2 158 3.
  Definition loc_229 : location_info := LocationInfo file_1 158 16 158 24.
  Definition loc_230 : location_info := LocationInfo file_1 158 16 158 24.
  Definition loc_231 : location_info := LocationInfo file_1 157 2 157 12.
  Definition loc_232 : location_info := LocationInfo file_1 157 2 157 12.
  Definition loc_233 : location_info := LocationInfo file_1 157 13 157 14.
  Definition loc_234 : location_info := LocationInfo file_1 157 13 157 14.
  Definition loc_235 : location_info := LocationInfo file_1 157 16 157 36.
  Definition loc_236 : location_info := LocationInfo file_1 157 16 157 36.
  Definition loc_237 : location_info := LocationInfo file_1 157 16 157 24.
  Definition loc_238 : location_info := LocationInfo file_1 157 16 157 24.
  Definition loc_241 : location_info := LocationInfo file_1 169 2 169 28.
  Definition loc_242 : location_info := LocationInfo file_1 170 2 170 28.
  Definition loc_243 : location_info := LocationInfo file_1 172 2 174 3.
  Definition loc_244 : location_info := LocationInfo file_1 176 2 176 31.
  Definition loc_245 : location_info := LocationInfo file_1 177 2 177 31.
  Definition loc_246 : location_info := LocationInfo file_1 182 2 186 3.
  Definition loc_247 : location_info := LocationInfo file_1 192 2 198 3.
  Definition loc_248 : location_info := LocationInfo file_1 200 2 200 40.
  Definition loc_249 : location_info := LocationInfo file_1 201 2 201 40.
  Definition loc_250 : location_info := LocationInfo file_1 202 2 202 31.
  Definition loc_251 : location_info := LocationInfo file_1 202 2 202 13.
  Definition loc_252 : location_info := LocationInfo file_1 202 2 202 3.
  Definition loc_253 : location_info := LocationInfo file_1 202 2 202 3.
  Definition loc_254 : location_info := LocationInfo file_1 202 16 202 30.
  Definition loc_255 : location_info := LocationInfo file_1 201 2 201 22.
  Definition loc_256 : location_info := LocationInfo file_1 201 2 201 11.
  Definition loc_257 : location_info := LocationInfo file_1 201 2 201 3.
  Definition loc_258 : location_info := LocationInfo file_1 201 2 201 3.
  Definition loc_259 : location_info := LocationInfo file_1 201 25 201 39.
  Definition loc_260 : location_info := LocationInfo file_1 200 2 200 22.
  Definition loc_261 : location_info := LocationInfo file_1 200 2 200 11.
  Definition loc_262 : location_info := LocationInfo file_1 200 2 200 3.
  Definition loc_263 : location_info := LocationInfo file_1 200 2 200 3.
  Definition loc_264 : location_info := LocationInfo file_1 200 25 200 39.
  Definition loc_265 : location_info := LocationInfo file_1 192 34 198 3.
  Definition loc_266 : location_info := LocationInfo file_1 193 4 193 23.
  Definition loc_267 : location_info := LocationInfo file_1 194 4 194 30.
  Definition loc_268 : location_info := LocationInfo file_1 196 4 196 30.
  Definition loc_269 : location_info := LocationInfo file_1 197 4 197 45.
  Definition loc_270 : location_info := LocationInfo file_1 197 4 197 19.
  Definition loc_271 : location_info := LocationInfo file_1 197 4 197 19.
  Definition loc_272 : location_info := LocationInfo file_1 197 20 197 31.
  Definition loc_273 : location_info := LocationInfo file_1 197 20 197 31.
  Definition loc_274 : location_info := LocationInfo file_1 197 20 197 21.
  Definition loc_275 : location_info := LocationInfo file_1 197 20 197 21.
  Definition loc_276 : location_info := LocationInfo file_1 197 33 197 37.
  Definition loc_277 : location_info := LocationInfo file_1 197 33 197 37.
  Definition loc_278 : location_info := LocationInfo file_1 197 39 197 43.
  Definition loc_279 : location_info := LocationInfo file_1 197 39 197 43.
  Definition loc_280 : location_info := LocationInfo file_1 196 4 196 9.
  Definition loc_281 : location_info := LocationInfo file_1 196 12 196 29.
  Definition loc_282 : location_info := LocationInfo file_1 196 12 196 29.
  Definition loc_283 : location_info := LocationInfo file_1 196 12 196 17.
  Definition loc_284 : location_info := LocationInfo file_1 196 12 196 17.
  Definition loc_285 : location_info := LocationInfo file_1 194 18 194 29.
  Definition loc_286 : location_info := LocationInfo file_1 194 18 194 29.
  Definition loc_287 : location_info := LocationInfo file_1 194 18 194 23.
  Definition loc_288 : location_info := LocationInfo file_1 194 18 194 23.
  Definition loc_291 : location_info := LocationInfo file_1 193 17 193 22.
  Definition loc_292 : location_info := LocationInfo file_1 193 17 193 22.
  Definition loc_295 : location_info := LocationInfo file_1 192 9 192 32.
  Definition loc_296 : location_info := LocationInfo file_1 192 9 192 14.
  Definition loc_297 : location_info := LocationInfo file_1 192 9 192 14.
  Definition loc_298 : location_info := LocationInfo file_1 192 18 192 32.
  Definition loc_299 : location_info := LocationInfo file_1 182 34 186 3.
  Definition loc_300 : location_info := LocationInfo file_1 183 4 183 23.
  Definition loc_301 : location_info := LocationInfo file_1 184 4 184 24.
  Definition loc_302 : location_info := LocationInfo file_1 185 4 185 34.
  Definition loc_303 : location_info := LocationInfo file_1 185 4 185 14.
  Definition loc_304 : location_info := LocationInfo file_1 185 4 185 14.
  Definition loc_305 : location_info := LocationInfo file_1 185 15 185 26.
  Definition loc_306 : location_info := LocationInfo file_1 185 15 185 26.
  Definition loc_307 : location_info := LocationInfo file_1 185 15 185 16.
  Definition loc_308 : location_info := LocationInfo file_1 185 15 185 16.
  Definition loc_309 : location_info := LocationInfo file_1 185 28 185 32.
  Definition loc_310 : location_info := LocationInfo file_1 185 28 185 32.
  Definition loc_311 : location_info := LocationInfo file_1 184 4 184 9.
  Definition loc_312 : location_info := LocationInfo file_1 184 12 184 23.
  Definition loc_313 : location_info := LocationInfo file_1 184 12 184 23.
  Definition loc_314 : location_info := LocationInfo file_1 184 12 184 17.
  Definition loc_315 : location_info := LocationInfo file_1 184 12 184 17.
  Definition loc_316 : location_info := LocationInfo file_1 183 17 183 22.
  Definition loc_317 : location_info := LocationInfo file_1 183 17 183 22.
  Definition loc_320 : location_info := LocationInfo file_1 182 9 182 32.
  Definition loc_321 : location_info := LocationInfo file_1 182 9 182 14.
  Definition loc_322 : location_info := LocationInfo file_1 182 9 182 14.
  Definition loc_323 : location_info := LocationInfo file_1 182 18 182 32.
  Definition loc_324 : location_info := LocationInfo file_1 177 2 177 7.
  Definition loc_325 : location_info := LocationInfo file_1 177 10 177 30.
  Definition loc_326 : location_info := LocationInfo file_1 177 10 177 30.
  Definition loc_327 : location_info := LocationInfo file_1 177 10 177 19.
  Definition loc_328 : location_info := LocationInfo file_1 177 10 177 11.
  Definition loc_329 : location_info := LocationInfo file_1 177 10 177 11.
  Definition loc_330 : location_info := LocationInfo file_1 176 2 176 7.
  Definition loc_331 : location_info := LocationInfo file_1 176 10 176 30.
  Definition loc_332 : location_info := LocationInfo file_1 176 10 176 30.
  Definition loc_333 : location_info := LocationInfo file_1 176 10 176 19.
  Definition loc_334 : location_info := LocationInfo file_1 176 10 176 11.
  Definition loc_335 : location_info := LocationInfo file_1 176 10 176 11.
  Definition loc_336 : location_info := LocationInfo file_1 172 37 174 3.
  Definition loc_337 : location_info := LocationInfo file_1 173 4 173 11.
  Definition loc_339 : location_info := LocationInfo file_1 172 2 174 3.
  Definition loc_340 : location_info := LocationInfo file_1 172 6 172 35.
  Definition loc_341 : location_info := LocationInfo file_1 172 6 172 17.
  Definition loc_342 : location_info := LocationInfo file_1 172 6 172 17.
  Definition loc_343 : location_info := LocationInfo file_1 172 6 172 7.
  Definition loc_344 : location_info := LocationInfo file_1 172 6 172 7.
  Definition loc_345 : location_info := LocationInfo file_1 172 21 172 35.
  Definition loc_348 : location_info := LocationInfo file_1 259 2 259 12.
  Definition loc_349 : location_info := LocationInfo file_1 260 2 260 28.
  Definition loc_350 : location_info := LocationInfo file_1 261 2 261 32.
  Definition loc_351 : location_info := LocationInfo file_1 264 2 264 20.
  Definition loc_352 : location_info := LocationInfo file_1 265 2 265 40.
  Definition loc_353 : location_info := LocationInfo file_1 265 40 265 3.
  Definition loc_354 : location_info := LocationInfo file_1 266 2 272 3.
  Definition loc_355 : location_info := LocationInfo file_1 275 2 275 31.
  Definition loc_356 : location_info := LocationInfo file_1 276 2 280 3.
  Definition loc_357 : location_info := LocationInfo file_1 282 2 289 3.
  Definition loc_358 : location_info := LocationInfo file_1 291 2 291 14.
  Definition loc_359 : location_info := LocationInfo file_1 291 14 294 22.
  Definition loc_360 : location_info := LocationInfo file_1 294 2 294 22.
  Definition loc_361 : location_info := LocationInfo file_1 296 2 296 13.
  Definition loc_362 : location_info := LocationInfo file_1 296 9 296 12.
  Definition loc_363 : location_info := LocationInfo file_1 296 9 296 12.
  Definition loc_364 : location_info := LocationInfo file_1 294 2 294 11.
  Definition loc_365 : location_info := LocationInfo file_1 294 2 294 11.
  Definition loc_366 : location_info := LocationInfo file_1 294 12 294 20.
  Definition loc_367 : location_info := LocationInfo file_1 294 13 294 20.
  Definition loc_368 : location_info := LocationInfo file_1 294 13 294 14.
  Definition loc_369 : location_info := LocationInfo file_1 294 13 294 14.
  Definition loc_370 : location_info := LocationInfo file_1 291 2 291 5.
  Definition loc_371 : location_info := LocationInfo file_1 291 8 291 13.
  Definition loc_372 : location_info := LocationInfo file_1 291 8 291 13.
  Definition loc_373 : location_info := LocationInfo file_1 282 36 284 3.
  Definition loc_374 : location_info := LocationInfo file_1 283 4 283 45.
  Definition loc_375 : location_info := LocationInfo file_1 283 4 283 24.
  Definition loc_376 : location_info := LocationInfo file_1 283 4 283 13.
  Definition loc_377 : location_info := LocationInfo file_1 283 4 283 5.
  Definition loc_378 : location_info := LocationInfo file_1 283 4 283 5.
  Definition loc_379 : location_info := LocationInfo file_1 283 27 283 44.
  Definition loc_380 : location_info := LocationInfo file_1 283 27 283 44.
  Definition loc_381 : location_info := LocationInfo file_1 283 27 283 32.
  Definition loc_382 : location_info := LocationInfo file_1 283 27 283 32.
  Definition loc_383 : location_info := LocationInfo file_1 284 9 289 3.
  Definition loc_384 : location_info := LocationInfo file_1 285 4 285 79.
  Definition loc_385 : location_info := LocationInfo file_1 286 4 286 46.
  Definition loc_386 : location_info := LocationInfo file_1 287 4 287 50.
  Definition loc_387 : location_info := LocationInfo file_1 288 4 288 37.
  Definition loc_388 : location_info := LocationInfo file_1 288 4 288 24.
  Definition loc_389 : location_info := LocationInfo file_1 288 4 288 13.
  Definition loc_390 : location_info := LocationInfo file_1 288 4 288 5.
  Definition loc_391 : location_info := LocationInfo file_1 288 4 288 5.
  Definition loc_392 : location_info := LocationInfo file_1 288 27 288 36.
  Definition loc_393 : location_info := LocationInfo file_1 288 27 288 36.
  Definition loc_394 : location_info := LocationInfo file_1 287 4 287 19.
  Definition loc_395 : location_info := LocationInfo file_1 287 4 287 13.
  Definition loc_396 : location_info := LocationInfo file_1 287 4 287 13.
  Definition loc_397 : location_info := LocationInfo file_1 287 22 287 49.
  Definition loc_398 : location_info := LocationInfo file_1 287 22 287 33.
  Definition loc_399 : location_info := LocationInfo file_1 287 22 287 33.
  Definition loc_400 : location_info := LocationInfo file_1 287 22 287 27.
  Definition loc_401 : location_info := LocationInfo file_1 287 22 287 27.
  Definition loc_402 : location_info := LocationInfo file_1 287 36 287 49.
  Definition loc_403 : location_info := LocationInfo file_1 287 36 287 49.
  Definition loc_404 : location_info := LocationInfo file_1 287 36 287 37.
  Definition loc_405 : location_info := LocationInfo file_1 287 36 287 37.
  Definition loc_406 : location_info := LocationInfo file_1 286 4 286 25.
  Definition loc_407 : location_info := LocationInfo file_1 286 4 286 13.
  Definition loc_408 : location_info := LocationInfo file_1 286 4 286 13.
  Definition loc_409 : location_info := LocationInfo file_1 286 28 286 45.
  Definition loc_410 : location_info := LocationInfo file_1 286 28 286 45.
  Definition loc_411 : location_info := LocationInfo file_1 286 28 286 33.
  Definition loc_412 : location_info := LocationInfo file_1 286 28 286 33.
  Definition loc_413 : location_info := LocationInfo file_1 285 4 285 13.
  Definition loc_414 : location_info := LocationInfo file_1 285 16 285 78.
  Definition loc_415 : location_info := LocationInfo file_1 285 38 285 78.
  Definition loc_416 : location_info := LocationInfo file_1 285 39 285 61.
  Definition loc_417 : location_info := LocationInfo file_1 285 56 285 61.
  Definition loc_418 : location_info := LocationInfo file_1 285 56 285 61.
  Definition loc_419 : location_info := LocationInfo file_1 285 64 285 77.
  Definition loc_420 : location_info := LocationInfo file_1 285 64 285 77.
  Definition loc_421 : location_info := LocationInfo file_1 285 64 285 65.
  Definition loc_422 : location_info := LocationInfo file_1 285 64 285 65.
  Definition loc_423 : location_info := LocationInfo file_1 282 6 282 34.
  Definition loc_424 : location_info := LocationInfo file_1 282 6 282 19.
  Definition loc_425 : location_info := LocationInfo file_1 282 6 282 19.
  Definition loc_426 : location_info := LocationInfo file_1 282 6 282 7.
  Definition loc_427 : location_info := LocationInfo file_1 282 6 282 7.
  Definition loc_428 : location_info := LocationInfo file_1 282 23 282 34.
  Definition loc_429 : location_info := LocationInfo file_1 282 23 282 34.
  Definition loc_430 : location_info := LocationInfo file_1 282 23 282 28.
  Definition loc_431 : location_info := LocationInfo file_1 282 23 282 28.
  Definition loc_432 : location_info := LocationInfo file_1 276 31 280 3.
  Definition loc_433 : location_info := LocationInfo file_1 278 4 278 25.
  Definition loc_434 : location_info := LocationInfo file_1 279 4 279 14.
  Definition loc_435 : location_info := LocationInfo file_1 278 4 278 7.
  Definition loc_436 : location_info := LocationInfo file_1 278 10 278 24.
  Definition loc_437 : location_info := LocationInfo file_1 276 2 280 3.
  Definition loc_438 : location_info := LocationInfo file_1 276 6 276 29.
  Definition loc_439 : location_info := LocationInfo file_1 276 6 276 11.
  Definition loc_440 : location_info := LocationInfo file_1 276 6 276 11.
  Definition loc_441 : location_info := LocationInfo file_1 276 15 276 29.
  Definition loc_442 : location_info := LocationInfo file_1 275 2 275 7.
  Definition loc_443 : location_info := LocationInfo file_1 275 10 275 30.
  Definition loc_444 : location_info := LocationInfo file_1 275 10 275 30.
  Definition loc_445 : location_info := LocationInfo file_1 275 10 275 19.
  Definition loc_446 : location_info := LocationInfo file_1 275 10 275 11.
  Definition loc_447 : location_info := LocationInfo file_1 275 10 275 11.
  Definition loc_448 : location_info := LocationInfo file_1 266 46 272 3.
  Definition loc_449 : location_info := LocationInfo file_1 267 4 267 53.
  Definition loc_450 : location_info := LocationInfo file_1 269 4 269 39.
  Definition loc_451 : location_info := LocationInfo file_1 270 4 270 16.
  Definition loc_452 : location_info := LocationInfo file_1 271 4 271 14.
  Definition loc_453 : location_info := LocationInfo file_1 270 4 270 7.
  Definition loc_454 : location_info := LocationInfo file_1 270 10 270 15.
  Definition loc_455 : location_info := LocationInfo file_1 270 10 270 15.
  Definition loc_456 : location_info := LocationInfo file_1 269 4 269 24.
  Definition loc_457 : location_info := LocationInfo file_1 269 4 269 13.
  Definition loc_458 : location_info := LocationInfo file_1 269 4 269 5.
  Definition loc_459 : location_info := LocationInfo file_1 269 4 269 5.
  Definition loc_460 : location_info := LocationInfo file_1 269 27 269 38.
  Definition loc_461 : location_info := LocationInfo file_1 269 27 269 38.
  Definition loc_462 : location_info := LocationInfo file_1 269 27 269 32.
  Definition loc_463 : location_info := LocationInfo file_1 269 27 269 32.
  Definition loc_464 : location_info := LocationInfo file_1 267 32 267 52.
  Definition loc_465 : location_info := LocationInfo file_1 267 32 267 52.
  Definition loc_466 : location_info := LocationInfo file_1 267 32 267 41.
  Definition loc_467 : location_info := LocationInfo file_1 267 32 267 33.
  Definition loc_468 : location_info := LocationInfo file_1 267 32 267 33.
  Definition loc_471 : location_info := LocationInfo file_1 266 2 272 3.
  Definition loc_472 : location_info := LocationInfo file_1 266 6 266 44.
  Definition loc_473 : location_info := LocationInfo file_1 266 6 266 26.
  Definition loc_474 : location_info := LocationInfo file_1 266 6 266 26.
  Definition loc_475 : location_info := LocationInfo file_1 266 6 266 15.
  Definition loc_476 : location_info := LocationInfo file_1 266 6 266 7.
  Definition loc_477 : location_info := LocationInfo file_1 266 6 266 7.
  Definition loc_478 : location_info := LocationInfo file_1 266 30 266 44.
  Definition loc_479 : location_info := LocationInfo file_1 265 27 265 39.
  Definition loc_480 : location_info := LocationInfo file_1 265 28 265 39.
  Definition loc_481 : location_info := LocationInfo file_1 265 29 265 30.
  Definition loc_482 : location_info := LocationInfo file_1 265 29 265 30.
  Definition loc_483 : location_info := LocationInfo file_1 264 2 264 9.
  Definition loc_484 : location_info := LocationInfo file_1 264 2 264 9.
  Definition loc_485 : location_info := LocationInfo file_1 264 10 264 18.
  Definition loc_486 : location_info := LocationInfo file_1 264 11 264 18.
  Definition loc_487 : location_info := LocationInfo file_1 264 11 264 12.
  Definition loc_488 : location_info := LocationInfo file_1 264 11 264 12.
  Definition loc_491 : location_info := LocationInfo file_1 309 2 309 41.
  Definition loc_492 : location_info := LocationInfo file_1 310 2 312 3.
  Definition loc_493 : location_info := LocationInfo file_1 313 2 313 18.
  Definition loc_494 : location_info := LocationInfo file_1 317 2 323 3.
  Definition loc_495 : location_info := LocationInfo file_1 325 2 325 24.
  Definition loc_496 : location_info := LocationInfo file_1 325 9 325 23.
  Definition loc_497 : location_info := LocationInfo file_1 317 30 323 3.
  Definition loc_498 : location_info := LocationInfo file_1 318 4 318 37.
  Definition loc_499 : location_info := LocationInfo file_1 319 4 321 5.
  Definition loc_500 : location_info := LocationInfo file_1 322 4 322 20.
  Definition loc_501 : location_info := LocationInfo file_1 322 4 322 5.
  Definition loc_502 : location_info := LocationInfo file_1 322 8 322 19.
  Definition loc_503 : location_info := LocationInfo file_1 322 8 322 19.
  Definition loc_504 : location_info := LocationInfo file_1 322 8 322 9.
  Definition loc_505 : location_info := LocationInfo file_1 322 8 322 9.
  Definition loc_506 : location_info := LocationInfo file_1 319 31 321 5.
  Definition loc_507 : location_info := LocationInfo file_1 320 6 320 17.
  Definition loc_508 : location_info := LocationInfo file_1 320 13 320 16.
  Definition loc_509 : location_info := LocationInfo file_1 320 13 320 16.
  Definition loc_510 : location_info := LocationInfo file_1 319 4 321 5.
  Definition loc_511 : location_info := LocationInfo file_1 319 8 319 29.
  Definition loc_512 : location_info := LocationInfo file_1 319 8 319 11.
  Definition loc_513 : location_info := LocationInfo file_1 319 8 319 11.
  Definition loc_514 : location_info := LocationInfo file_1 319 15 319 29.
  Definition loc_515 : location_info := LocationInfo file_1 318 4 318 7.
  Definition loc_516 : location_info := LocationInfo file_1 318 10 318 36.
  Definition loc_517 : location_info := LocationInfo file_1 318 10 318 33.
  Definition loc_518 : location_info := LocationInfo file_1 318 10 318 33.
  Definition loc_519 : location_info := LocationInfo file_1 318 34 318 35.
  Definition loc_520 : location_info := LocationInfo file_1 318 34 318 35.
  Definition loc_521 : location_info := LocationInfo file_1 317 9 317 28.
  Definition loc_522 : location_info := LocationInfo file_1 317 9 317 10.
  Definition loc_523 : location_info := LocationInfo file_1 317 9 317 10.
  Definition loc_524 : location_info := LocationInfo file_1 317 14 317 28.
  Definition loc_525 : location_info := LocationInfo file_1 313 2 313 3.
  Definition loc_526 : location_info := LocationInfo file_1 313 6 313 17.
  Definition loc_527 : location_info := LocationInfo file_1 313 6 313 17.
  Definition loc_528 : location_info := LocationInfo file_1 313 6 313 7.
  Definition loc_529 : location_info := LocationInfo file_1 313 6 313 7.
  Definition loc_530 : location_info := LocationInfo file_1 310 29 312 3.
  Definition loc_531 : location_info := LocationInfo file_1 311 4 311 15.
  Definition loc_532 : location_info := LocationInfo file_1 311 11 311 14.
  Definition loc_533 : location_info := LocationInfo file_1 311 11 311 14.
  Definition loc_534 : location_info := LocationInfo file_1 310 2 312 3.
  Definition loc_535 : location_info := LocationInfo file_1 310 6 310 27.
  Definition loc_536 : location_info := LocationInfo file_1 310 6 310 9.
  Definition loc_537 : location_info := LocationInfo file_1 310 6 310 9.
  Definition loc_538 : location_info := LocationInfo file_1 310 13 310 27.
  Definition loc_539 : location_info := LocationInfo file_1 309 14 309 40.
  Definition loc_540 : location_info := LocationInfo file_1 309 14 309 37.
  Definition loc_541 : location_info := LocationInfo file_1 309 14 309 37.
  Definition loc_542 : location_info := LocationInfo file_1 309 38 309 39.
  Definition loc_543 : location_info := LocationInfo file_1 309 38 309 39.
  Definition loc_548 : location_info := LocationInfo file_1 365 2 365 28.
  Definition loc_549 : location_info := LocationInfo file_1 366 2 366 29.
  Definition loc_550 : location_info := LocationInfo file_1 368 2 368 25.
  Definition loc_551 : location_info := LocationInfo file_1 370 2 370 20.
  Definition loc_552 : location_info := LocationInfo file_1 371 2 371 40.
  Definition loc_553 : location_info := LocationInfo file_1 371 40 371 3.
  Definition loc_554 : location_info := LocationInfo file_1 377 2 377 31.
  Definition loc_555 : location_info := LocationInfo file_1 387 2 432 3.
  Definition loc_556 : location_info := LocationInfo file_1 434 2 434 22.
  Definition loc_557 : location_info := LocationInfo file_1 436 2 436 13.
  Definition loc_558 : location_info := LocationInfo file_1 436 9 436 12.
  Definition loc_559 : location_info := LocationInfo file_1 436 9 436 12.
  Definition loc_560 : location_info := LocationInfo file_1 434 2 434 11.
  Definition loc_561 : location_info := LocationInfo file_1 434 2 434 11.
  Definition loc_562 : location_info := LocationInfo file_1 434 12 434 20.
  Definition loc_563 : location_info := LocationInfo file_1 434 13 434 20.
  Definition loc_564 : location_info := LocationInfo file_1 434 13 434 14.
  Definition loc_565 : location_info := LocationInfo file_1 434 13 434 14.
  Definition loc_566 : location_info := LocationInfo file_1 387 34 432 3.
  Definition loc_567 : location_info := LocationInfo file_1 388 4 388 25.
  Definition loc_568 : location_info := LocationInfo file_1 389 4 389 34.
  Definition loc_569 : location_info := LocationInfo file_1 390 4 390 38.
  Definition loc_570 : location_info := LocationInfo file_1 391 4 391 24.
  Definition loc_571 : location_info := LocationInfo file_1 393 4 393 51.
  Definition loc_572 : location_info := LocationInfo file_1 393 51 393 5.
  Definition loc_573 : location_info := LocationInfo file_1 395 4 395 67.
  Definition loc_574 : location_info := LocationInfo file_1 402 4 429 5.
  Definition loc_575 : location_info := LocationInfo file_1 431 4 431 30.
  Definition loc_576 : location_info := LocationInfo file_1 431 4 431 8.
  Definition loc_577 : location_info := LocationInfo file_1 431 11 431 29.
  Definition loc_578 : location_info := LocationInfo file_1 431 12 431 29.
  Definition loc_579 : location_info := LocationInfo file_1 431 12 431 17.
  Definition loc_580 : location_info := LocationInfo file_1 431 12 431 17.
  Definition loc_581 : location_info := LocationInfo file_1 402 61 429 5.
  Definition loc_582 : location_info := LocationInfo file_1 403 6 403 38.
  Definition loc_583 : location_info := LocationInfo file_1 404 6 404 57.
  Definition loc_584 : location_info := LocationInfo file_1 405 6 405 42.
  Definition loc_585 : location_info := LocationInfo file_1 405 42 405 7.
  Definition loc_586 : location_info := LocationInfo file_1 406 6 406 52.
  Definition loc_587 : location_info := LocationInfo file_1 408 6 415 7.
  Definition loc_588 : location_info := LocationInfo file_1 421 6 425 7.
  Definition loc_589 : location_info := LocationInfo file_1 427 6 427 26.
  Definition loc_590 : location_info := LocationInfo file_1 428 6 428 12.
  Definition loc_591 : location_info := LocationInfo file_1 427 6 427 9.
  Definition loc_592 : location_info := LocationInfo file_1 427 12 427 25.
  Definition loc_593 : location_info := LocationInfo file_1 427 20 427 25.
  Definition loc_594 : location_info := LocationInfo file_1 427 20 427 25.
  Definition loc_595 : location_info := LocationInfo file_1 421 41 425 7.
  Definition loc_596 : location_info := LocationInfo file_1 422 8 422 34.
  Definition loc_597 : location_info := LocationInfo file_1 423 8 423 22.
  Definition loc_598 : location_info := LocationInfo file_1 424 8 424 35.
  Definition loc_599 : location_info := LocationInfo file_1 424 8 424 19.
  Definition loc_600 : location_info := LocationInfo file_1 424 8 424 13.
  Definition loc_601 : location_info := LocationInfo file_1 424 8 424 13.
  Definition loc_602 : location_info := LocationInfo file_1 424 22 424 34.
  Definition loc_603 : location_info := LocationInfo file_1 424 22 424 34.
  Definition loc_604 : location_info := LocationInfo file_1 423 8 423 13.
  Definition loc_605 : location_info := LocationInfo file_1 423 9 423 13.
  Definition loc_606 : location_info := LocationInfo file_1 423 9 423 13.
  Definition loc_607 : location_info := LocationInfo file_1 423 16 423 21.
  Definition loc_608 : location_info := LocationInfo file_1 423 16 423 21.
  Definition loc_609 : location_info := LocationInfo file_1 422 8 422 25.
  Definition loc_610 : location_info := LocationInfo file_1 422 8 422 13.
  Definition loc_611 : location_info := LocationInfo file_1 422 8 422 13.
  Definition loc_612 : location_info := LocationInfo file_1 422 28 422 33.
  Definition loc_613 : location_info := LocationInfo file_1 422 28 422 33.
  Definition loc_614 : location_info := LocationInfo file_1 422 29 422 33.
  Definition loc_615 : location_info := LocationInfo file_1 422 29 422 33.
  Definition loc_616 : location_info := LocationInfo file_1 421 6 425 7.
  Definition loc_617 : location_info := LocationInfo file_1 421 10 421 39.
  Definition loc_618 : location_info := LocationInfo file_1 421 10 421 22.
  Definition loc_619 : location_info := LocationInfo file_1 421 10 421 22.
  Definition loc_620 : location_info := LocationInfo file_1 421 26 421 39.
  Definition loc_621 : location_info := LocationInfo file_1 421 26 421 39.
  Definition loc_622 : location_info := LocationInfo file_1 421 26 421 27.
  Definition loc_623 : location_info := LocationInfo file_1 421 26 421 27.
  Definition loc_624 : location_info := LocationInfo file_1 408 62 410 7.
  Definition loc_625 : location_info := LocationInfo file_1 409 8 409 27.
  Definition loc_626 : location_info := LocationInfo file_1 409 8 409 13.
  Definition loc_627 : location_info := LocationInfo file_1 409 9 409 13.
  Definition loc_628 : location_info := LocationInfo file_1 409 9 409 13.
  Definition loc_629 : location_info := LocationInfo file_1 409 16 409 26.
  Definition loc_630 : location_info := LocationInfo file_1 409 16 409 26.
  Definition loc_631 : location_info := LocationInfo file_1 410 13 415 7.
  Definition loc_632 : location_info := LocationInfo file_1 411 8 411 76.
  Definition loc_633 : location_info := LocationInfo file_1 412 8 412 78.
  Definition loc_634 : location_info := LocationInfo file_1 413 8 413 43.
  Definition loc_635 : location_info := LocationInfo file_1 414 8 414 26.
  Definition loc_636 : location_info := LocationInfo file_1 414 8 414 13.
  Definition loc_637 : location_info := LocationInfo file_1 414 9 414 13.
  Definition loc_638 : location_info := LocationInfo file_1 414 9 414 13.
  Definition loc_639 : location_info := LocationInfo file_1 414 16 414 25.
  Definition loc_640 : location_info := LocationInfo file_1 414 16 414 25.
  Definition loc_641 : location_info := LocationInfo file_1 413 8 413 29.
  Definition loc_642 : location_info := LocationInfo file_1 413 8 413 17.
  Definition loc_643 : location_info := LocationInfo file_1 413 8 413 17.
  Definition loc_644 : location_info := LocationInfo file_1 413 32 413 42.
  Definition loc_645 : location_info := LocationInfo file_1 413 32 413 42.
  Definition loc_646 : location_info := LocationInfo file_1 412 8 412 23.
  Definition loc_647 : location_info := LocationInfo file_1 412 8 412 17.
  Definition loc_648 : location_info := LocationInfo file_1 412 8 412 17.
  Definition loc_649 : location_info := LocationInfo file_1 412 26 412 77.
  Definition loc_650 : location_info := LocationInfo file_1 412 26 412 36.
  Definition loc_651 : location_info := LocationInfo file_1 412 26 412 36.
  Definition loc_652 : location_info := LocationInfo file_1 412 39 412 77.
  Definition loc_653 : location_info := LocationInfo file_1 412 40 412 52.
  Definition loc_654 : location_info := LocationInfo file_1 412 40 412 52.
  Definition loc_655 : location_info := LocationInfo file_1 412 55 412 76.
  Definition loc_656 : location_info := LocationInfo file_1 412 55 412 60.
  Definition loc_657 : location_info := LocationInfo file_1 412 55 412 60.
  Definition loc_658 : location_info := LocationInfo file_1 412 63 412 76.
  Definition loc_659 : location_info := LocationInfo file_1 412 63 412 76.
  Definition loc_660 : location_info := LocationInfo file_1 412 63 412 64.
  Definition loc_661 : location_info := LocationInfo file_1 412 63 412 64.
  Definition loc_662 : location_info := LocationInfo file_1 411 8 411 17.
  Definition loc_663 : location_info := LocationInfo file_1 411 20 411 75.
  Definition loc_664 : location_info := LocationInfo file_1 411 42 411 75.
  Definition loc_665 : location_info := LocationInfo file_1 411 43 411 48.
  Definition loc_666 : location_info := LocationInfo file_1 411 43 411 48.
  Definition loc_667 : location_info := LocationInfo file_1 411 51 411 74.
  Definition loc_668 : location_info := LocationInfo file_1 411 52 411 57.
  Definition loc_669 : location_info := LocationInfo file_1 411 52 411 57.
  Definition loc_670 : location_info := LocationInfo file_1 411 60 411 73.
  Definition loc_671 : location_info := LocationInfo file_1 411 60 411 73.
  Definition loc_672 : location_info := LocationInfo file_1 411 60 411 61.
  Definition loc_673 : location_info := LocationInfo file_1 411 60 411 61.
  Definition loc_674 : location_info := LocationInfo file_1 408 10 408 60.
  Definition loc_675 : location_info := LocationInfo file_1 408 10 408 46.
  Definition loc_676 : location_info := LocationInfo file_1 408 10 408 22.
  Definition loc_677 : location_info := LocationInfo file_1 408 10 408 22.
  Definition loc_678 : location_info := LocationInfo file_1 408 25 408 46.
  Definition loc_679 : location_info := LocationInfo file_1 408 25 408 30.
  Definition loc_680 : location_info := LocationInfo file_1 408 25 408 30.
  Definition loc_681 : location_info := LocationInfo file_1 408 33 408 46.
  Definition loc_682 : location_info := LocationInfo file_1 408 33 408 46.
  Definition loc_683 : location_info := LocationInfo file_1 408 33 408 34.
  Definition loc_684 : location_info := LocationInfo file_1 408 33 408 34.
  Definition loc_685 : location_info := LocationInfo file_1 408 50 408 60.
  Definition loc_686 : location_info := LocationInfo file_1 408 50 408 60.
  Definition loc_687 : location_info := LocationInfo file_1 406 6 406 11.
  Definition loc_688 : location_info := LocationInfo file_1 406 14 406 51.
  Definition loc_689 : location_info := LocationInfo file_1 406 14 406 36.
  Definition loc_690 : location_info := LocationInfo file_1 406 31 406 36.
  Definition loc_691 : location_info := LocationInfo file_1 406 31 406 36.
  Definition loc_692 : location_info := LocationInfo file_1 406 39 406 51.
  Definition loc_693 : location_info := LocationInfo file_1 406 39 406 51.
  Definition loc_694 : location_info := LocationInfo file_1 405 32 405 41.
  Definition loc_695 : location_info := LocationInfo file_1 405 33 405 41.
  Definition loc_696 : location_info := LocationInfo file_1 405 35 405 40.
  Definition loc_697 : location_info := LocationInfo file_1 405 35 405 40.
  Definition loc_698 : location_info := LocationInfo file_1 404 39 404 56.
  Definition loc_699 : location_info := LocationInfo file_1 404 39 404 56.
  Definition loc_700 : location_info := LocationInfo file_1 404 39 404 44.
  Definition loc_701 : location_info := LocationInfo file_1 404 39 404 44.
  Definition loc_704 : location_info := LocationInfo file_1 403 26 403 37.
  Definition loc_705 : location_info := LocationInfo file_1 403 26 403 37.
  Definition loc_706 : location_info := LocationInfo file_1 403 26 403 31.
  Definition loc_707 : location_info := LocationInfo file_1 403 26 403 31.
  Definition loc_710 : location_info := LocationInfo file_1 402 4 429 5.
  Definition loc_711 : location_info := LocationInfo file_1 402 8 402 59.
  Definition loc_712 : location_info := LocationInfo file_1 402 8 402 44.
  Definition loc_713 : location_info := LocationInfo file_1 402 8 402 20.
  Definition loc_714 : location_info := LocationInfo file_1 402 8 402 20.
  Definition loc_715 : location_info := LocationInfo file_1 402 23 402 44.
  Definition loc_716 : location_info := LocationInfo file_1 402 23 402 28.
  Definition loc_717 : location_info := LocationInfo file_1 402 23 402 28.
  Definition loc_718 : location_info := LocationInfo file_1 402 31 402 44.
  Definition loc_719 : location_info := LocationInfo file_1 402 31 402 44.
  Definition loc_720 : location_info := LocationInfo file_1 402 31 402 32.
  Definition loc_721 : location_info := LocationInfo file_1 402 31 402 32.
  Definition loc_722 : location_info := LocationInfo file_1 402 48 402 59.
  Definition loc_723 : location_info := LocationInfo file_1 402 48 402 59.
  Definition loc_724 : location_info := LocationInfo file_1 402 48 402 53.
  Definition loc_725 : location_info := LocationInfo file_1 402 48 402 53.
  Definition loc_726 : location_info := LocationInfo file_1 395 4 395 20.
  Definition loc_727 : location_info := LocationInfo file_1 395 4 395 20.
  Definition loc_728 : location_info := LocationInfo file_1 395 21 395 43.
  Definition loc_729 : location_info := LocationInfo file_1 395 38 395 43.
  Definition loc_730 : location_info := LocationInfo file_1 395 38 395 43.
  Definition loc_731 : location_info := LocationInfo file_1 395 45 395 50.
  Definition loc_732 : location_info := LocationInfo file_1 395 45 395 50.
  Definition loc_733 : location_info := LocationInfo file_1 395 52 395 65.
  Definition loc_734 : location_info := LocationInfo file_1 395 53 395 65.
  Definition loc_735 : location_info := LocationInfo file_1 393 41 393 50.
  Definition loc_736 : location_info := LocationInfo file_1 393 42 393 50.
  Definition loc_737 : location_info := LocationInfo file_1 393 44 393 49.
  Definition loc_738 : location_info := LocationInfo file_1 393 44 393 49.
  Definition loc_739 : location_info := LocationInfo file_1 390 32 390 37.
  Definition loc_740 : location_info := LocationInfo file_1 390 32 390 37.
  Definition loc_741 : location_info := LocationInfo file_1 390 33 390 37.
  Definition loc_742 : location_info := LocationInfo file_1 390 33 390 37.
  Definition loc_745 : location_info := LocationInfo file_1 387 9 387 32.
  Definition loc_746 : location_info := LocationInfo file_1 387 9 387 14.
  Definition loc_747 : location_info := LocationInfo file_1 387 9 387 14.
  Definition loc_748 : location_info := LocationInfo file_1 387 10 387 14.
  Definition loc_749 : location_info := LocationInfo file_1 387 10 387 14.
  Definition loc_750 : location_info := LocationInfo file_1 387 18 387 32.
  Definition loc_751 : location_info := LocationInfo file_1 377 2 377 6.
  Definition loc_752 : location_info := LocationInfo file_1 377 9 377 30.
  Definition loc_753 : location_info := LocationInfo file_1 377 10 377 30.
  Definition loc_754 : location_info := LocationInfo file_1 377 10 377 19.
  Definition loc_755 : location_info := LocationInfo file_1 377 10 377 11.
  Definition loc_756 : location_info := LocationInfo file_1 377 10 377 11.
  Definition loc_757 : location_info := LocationInfo file_1 371 27 371 39.
  Definition loc_758 : location_info := LocationInfo file_1 371 28 371 39.
  Definition loc_759 : location_info := LocationInfo file_1 371 29 371 30.
  Definition loc_760 : location_info := LocationInfo file_1 371 29 371 30.
  Definition loc_761 : location_info := LocationInfo file_1 370 2 370 9.
  Definition loc_762 : location_info := LocationInfo file_1 370 2 370 9.
  Definition loc_763 : location_info := LocationInfo file_1 370 10 370 18.
  Definition loc_764 : location_info := LocationInfo file_1 370 11 370 18.
  Definition loc_765 : location_info := LocationInfo file_1 370 11 370 12.
  Definition loc_766 : location_info := LocationInfo file_1 370 11 370 12.
  Definition loc_767 : location_info := LocationInfo file_1 368 2 368 7.
  Definition loc_768 : location_info := LocationInfo file_1 368 2 368 24.
  Definition loc_769 : location_info := LocationInfo file_1 368 2 368 7.
  Definition loc_770 : location_info := LocationInfo file_1 368 2 368 7.
  Definition loc_771 : location_info := LocationInfo file_1 368 11 368 24.
  Definition loc_772 : location_info := LocationInfo file_1 368 11 368 24.
  Definition loc_773 : location_info := LocationInfo file_1 368 11 368 12.
  Definition loc_774 : location_info := LocationInfo file_1 368 11 368 12.
  Definition loc_775 : location_info := LocationInfo file_1 366 14 366 28.
  Definition loc_780 : location_info := LocationInfo file_1 460 2 460 66.
  Definition loc_781 : location_info := LocationInfo file_1 462 2 464 3.
  Definition loc_782 : location_info := LocationInfo file_1 466 2 466 18.
  Definition loc_783 : location_info := LocationInfo file_1 470 2 479 3.
  Definition loc_784 : location_info := LocationInfo file_1 481 2 481 24.
  Definition loc_785 : location_info := LocationInfo file_1 481 9 481 23.
  Definition loc_786 : location_info := LocationInfo file_1 470 30 479 3.
  Definition loc_787 : location_info := LocationInfo file_1 471 4 471 62.
  Definition loc_788 : location_info := LocationInfo file_1 473 4 475 5.
  Definition loc_789 : location_info := LocationInfo file_1 477 4 477 20.
  Definition loc_790 : location_info := LocationInfo file_1 477 4 477 5.
  Definition loc_791 : location_info := LocationInfo file_1 477 8 477 19.
  Definition loc_792 : location_info := LocationInfo file_1 477 8 477 19.
  Definition loc_793 : location_info := LocationInfo file_1 477 8 477 9.
  Definition loc_794 : location_info := LocationInfo file_1 477 8 477 9.
  Definition loc_795 : location_info := LocationInfo file_1 473 31 475 5.
  Definition loc_796 : location_info := LocationInfo file_1 474 6 474 17.
  Definition loc_797 : location_info := LocationInfo file_1 474 13 474 16.
  Definition loc_798 : location_info := LocationInfo file_1 474 13 474 16.
  Definition loc_799 : location_info := LocationInfo file_1 473 4 475 5.
  Definition loc_800 : location_info := LocationInfo file_1 473 8 473 29.
  Definition loc_801 : location_info := LocationInfo file_1 473 8 473 11.
  Definition loc_802 : location_info := LocationInfo file_1 473 8 473 11.
  Definition loc_803 : location_info := LocationInfo file_1 473 15 473 29.
  Definition loc_804 : location_info := LocationInfo file_1 471 4 471 7.
  Definition loc_805 : location_info := LocationInfo file_1 471 10 471 61.
  Definition loc_806 : location_info := LocationInfo file_1 471 10 471 44.
  Definition loc_807 : location_info := LocationInfo file_1 471 10 471 44.
  Definition loc_808 : location_info := LocationInfo file_1 471 45 471 46.
  Definition loc_809 : location_info := LocationInfo file_1 471 45 471 46.
  Definition loc_810 : location_info := LocationInfo file_1 471 48 471 53.
  Definition loc_811 : location_info := LocationInfo file_1 471 48 471 53.
  Definition loc_812 : location_info := LocationInfo file_1 471 55 471 60.
  Definition loc_813 : location_info := LocationInfo file_1 471 55 471 60.
  Definition loc_814 : location_info := LocationInfo file_1 470 9 470 28.
  Definition loc_815 : location_info := LocationInfo file_1 470 9 470 10.
  Definition loc_816 : location_info := LocationInfo file_1 470 9 470 10.
  Definition loc_817 : location_info := LocationInfo file_1 470 14 470 28.
  Definition loc_818 : location_info := LocationInfo file_1 466 2 466 3.
  Definition loc_819 : location_info := LocationInfo file_1 466 6 466 17.
  Definition loc_820 : location_info := LocationInfo file_1 466 6 466 17.
  Definition loc_821 : location_info := LocationInfo file_1 466 6 466 7.
  Definition loc_822 : location_info := LocationInfo file_1 466 6 466 7.
  Definition loc_823 : location_info := LocationInfo file_1 462 29 464 3.
  Definition loc_824 : location_info := LocationInfo file_1 463 4 463 15.
  Definition loc_825 : location_info := LocationInfo file_1 463 11 463 14.
  Definition loc_826 : location_info := LocationInfo file_1 463 11 463 14.
  Definition loc_827 : location_info := LocationInfo file_1 462 2 464 3.
  Definition loc_828 : location_info := LocationInfo file_1 462 6 462 27.
  Definition loc_829 : location_info := LocationInfo file_1 462 6 462 9.
  Definition loc_830 : location_info := LocationInfo file_1 462 6 462 9.
  Definition loc_831 : location_info := LocationInfo file_1 462 13 462 27.
  Definition loc_832 : location_info := LocationInfo file_1 460 14 460 65.
  Definition loc_833 : location_info := LocationInfo file_1 460 14 460 48.
  Definition loc_834 : location_info := LocationInfo file_1 460 14 460 48.
  Definition loc_835 : location_info := LocationInfo file_1 460 49 460 50.
  Definition loc_836 : location_info := LocationInfo file_1 460 49 460 50.
  Definition loc_837 : location_info := LocationInfo file_1 460 52 460 57.
  Definition loc_838 : location_info := LocationInfo file_1 460 52 460 57.
  Definition loc_839 : location_info := LocationInfo file_1 460 59 460 64.
  Definition loc_840 : location_info := LocationInfo file_1 460 59 460 64.

  (* Definition of struct [__cerbty_unnamed_tag_486]. *)
  Program Definition struct___cerbty_unnamed_tag_486 := {|
    sl_members := [
      (Some "__dummy_max_align_t", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [atomic_flag]. *)
  Program Definition struct_atomic_flag := {|
    sl_members := [
      (Some "_Value", bool_layout)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [spinlock]. *)
  Program Definition struct_spinlock := {|
    sl_members := [
      (Some "lock", bool_layout)
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
        locinfo: loc_12 ;
        expr: (LocInfoE loc_72 (&(LocInfoE loc_73 ((LocInfoE loc_74 (!{PtrOp} (LocInfoE loc_75 ("p")))) at{struct_mpool} "entry_size")))) ;
        locinfo: loc_67 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_67 ((LocInfoE loc_68 (use{IntOp size_t} (LocInfoE loc_69 ("size")))) ={IntOp size_t, IntOp size_t, i32} (LocInfoE loc_70 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_71 (i2v 0 i32)))))
        then
        locinfo: loc_64 ;
          Goto "#2"
        else
        locinfo: loc_15 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_15 ;
        LocInfoE loc_60 ("chunk") <-{ PtrOp }
          LocInfoE loc_61 (use{PtrOp} (LocInfoE loc_62 ("begin"))) ;
        locinfo: loc_16 ;
        LocInfoE loc_55 ((LocInfoE loc_56 (!{PtrOp} (LocInfoE loc_57 ("chunk")))) at{struct_mpool_chunk} "size") <-{ IntOp size_t }
          LocInfoE loc_58 (use{IntOp size_t} (LocInfoE loc_59 ("size"))) ;
        locinfo: loc_17 ;
        expr: (LocInfoE loc_17 (Call (LocInfoE loc_50 (global_sl_lock)) [@{expr} LocInfoE loc_51 (&(LocInfoE loc_52 ((LocInfoE loc_53 (!{PtrOp} (LocInfoE loc_54 ("p")))) at{struct_mpool} "lock"))) ])) ;
        locinfo: loc_18 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_45 (&(LocInfoE loc_46 ((LocInfoE loc_47 (!{PtrOp} (LocInfoE loc_48 ("p")))) at{struct_mpool} "locked")))) ;
        locinfo: loc_20 ;
        LocInfoE loc_37 ((LocInfoE loc_38 (!{PtrOp} (LocInfoE loc_39 ("chunk")))) at{struct_mpool_chunk} "next_chunk") <-{ PtrOp }
          LocInfoE loc_40 (use{PtrOp} (LocInfoE loc_41 ((LocInfoE loc_42 ((LocInfoE loc_43 (!{PtrOp} (LocInfoE loc_44 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list"))) ;
        locinfo: loc_21 ;
        LocInfoE loc_31 ((LocInfoE loc_32 ((LocInfoE loc_33 (!{PtrOp} (LocInfoE loc_34 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list") <-{ PtrOp }
          LocInfoE loc_35 (use{PtrOp} (LocInfoE loc_36 ("chunk"))) ;
        locinfo: loc_22 ;
        expr: (LocInfoE loc_22 (Call (LocInfoE loc_26 (global_sl_unlock)) [@{expr} LocInfoE loc_27 (AnnotExpr 1%nat LockA (LocInfoE loc_27 (&(LocInfoE loc_28 ((LocInfoE loc_29 (!{PtrOp} (LocInfoE loc_30 ("p")))) at{struct_mpool} "lock"))))) ])) ;
        locinfo: loc_23 ;
        Return (LocInfoE loc_24 (UnOp (CastOp $ BoolOp) (IntOp i32) (LocInfoE loc_24 (i2v 1 i32))))
      ]> $
      <[ "#2" :=
        locinfo: loc_64 ;
        Return (LocInfoE loc_65 (UnOp (CastOp $ BoolOp) (IntOp i32) (LocInfoE loc_65 (i2v 0 i32))))
      ]> $
      <[ "#3" :=
        locinfo: loc_15 ;
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
          LocInfoE loc_115 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_115 (use{PtrOp} (LocInfoE loc_116 ("ptr"))))) ;
        locinfo: loc_79 ;
        expr: (LocInfoE loc_79 (Call (LocInfoE loc_110 (global_sl_lock)) [@{expr} LocInfoE loc_111 (&(LocInfoE loc_112 ((LocInfoE loc_113 (!{PtrOp} (LocInfoE loc_114 ("p")))) at{struct_mpool} "lock"))) ])) ;
        locinfo: loc_80 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_105 (&(LocInfoE loc_106 ((LocInfoE loc_107 (!{PtrOp} (LocInfoE loc_108 ("p")))) at{struct_mpool} "locked")))) ;
        locinfo: loc_82 ;
        LocInfoE loc_97 ((LocInfoE loc_98 (!{PtrOp} (LocInfoE loc_99 ("e")))) at{struct_mpool_entry} "next") <-{ PtrOp }
          LocInfoE loc_100 (use{PtrOp} (LocInfoE loc_101 ((LocInfoE loc_102 ((LocInfoE loc_103 (!{PtrOp} (LocInfoE loc_104 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list"))) ;
        locinfo: loc_83 ;
        LocInfoE loc_91 ((LocInfoE loc_92 ((LocInfoE loc_93 (!{PtrOp} (LocInfoE loc_94 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list") <-{ PtrOp }
          LocInfoE loc_95 (use{PtrOp} (LocInfoE loc_96 ("e"))) ;
        locinfo: loc_84 ;
        expr: (LocInfoE loc_84 (Call (LocInfoE loc_86 (global_sl_unlock)) [@{expr} LocInfoE loc_87 (AnnotExpr 1%nat LockA (LocInfoE loc_87 (&(LocInfoE loc_88 ((LocInfoE loc_89 (!{PtrOp} (LocInfoE loc_90 ("p")))) at{struct_mpool} "lock"))))) ])) ;
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
        locinfo: loc_121 ;
        LocInfoE loc_146 ((LocInfoE loc_147 (!{PtrOp} (LocInfoE loc_148 ("p")))) at{struct_mpool} "entry_size") <-{ IntOp size_t }
          LocInfoE loc_149 (use{IntOp size_t} (LocInfoE loc_150 ("entry_size"))) ;
        locinfo: loc_122 ;
        LocInfoE loc_141 ((LocInfoE loc_142 ((LocInfoE loc_143 (!{PtrOp} (LocInfoE loc_144 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list") <-{ PtrOp }
          LocInfoE loc_145 (NULL) ;
        locinfo: loc_123 ;
        LocInfoE loc_136 ((LocInfoE loc_137 ((LocInfoE loc_138 (!{PtrOp} (LocInfoE loc_139 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list") <-{ PtrOp }
          LocInfoE loc_140 (NULL) ;
        locinfo: loc_124 ;
        LocInfoE loc_132 ((LocInfoE loc_133 (!{PtrOp} (LocInfoE loc_134 ("p")))) at{struct_mpool} "fallback") <-{ PtrOp }
          LocInfoE loc_135 (NULL) ;
        locinfo: loc_125 ;
        expr: (LocInfoE loc_125 (Call (LocInfoE loc_127 (global_sl_init)) [@{expr} LocInfoE loc_128 (&(LocInfoE loc_129 ((LocInfoE loc_130 (!{PtrOp} (LocInfoE loc_131 ("p")))) at{struct_mpool} "lock"))) ])) ;
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
        locinfo: loc_153 ;
        expr: (LocInfoE loc_153 (Call (LocInfoE loc_215 (global_mpool_init)) [@{expr} LocInfoE loc_216 (use{PtrOp} (LocInfoE loc_217 ("p"))) ;
        LocInfoE loc_218 (use{IntOp size_t} (LocInfoE loc_219 ((LocInfoE loc_220 (!{PtrOp} (LocInfoE loc_221 ("from")))) at{struct_mpool} "entry_size"))) ])) ;
        locinfo: loc_154 ;
        expr: (LocInfoE loc_154 (Call (LocInfoE loc_209 (global_sl_lock)) [@{expr} LocInfoE loc_210 (&(LocInfoE loc_211 ((LocInfoE loc_212 (!{PtrOp} (LocInfoE loc_213 ("from")))) at{struct_mpool} "lock"))) ])) ;
        locinfo: loc_155 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_204 (&(LocInfoE loc_205 ((LocInfoE loc_206 (!{PtrOp} (LocInfoE loc_207 ("from")))) at{struct_mpool} "locked")))) ;
        locinfo: loc_157 ;
        LocInfoE loc_195 ((LocInfoE loc_196 ((LocInfoE loc_197 (!{PtrOp} (LocInfoE loc_198 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list") <-{ PtrOp }
          LocInfoE loc_199 (use{PtrOp} (LocInfoE loc_200 ((LocInfoE loc_201 ((LocInfoE loc_202 (!{PtrOp} (LocInfoE loc_203 ("from")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list"))) ;
        locinfo: loc_158 ;
        LocInfoE loc_186 ((LocInfoE loc_187 ((LocInfoE loc_188 (!{PtrOp} (LocInfoE loc_189 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list") <-{ PtrOp }
          LocInfoE loc_190 (use{PtrOp} (LocInfoE loc_191 ((LocInfoE loc_192 ((LocInfoE loc_193 (!{PtrOp} (LocInfoE loc_194 ("from")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list"))) ;
        locinfo: loc_159 ;
        LocInfoE loc_179 ((LocInfoE loc_180 (!{PtrOp} (LocInfoE loc_181 ("p")))) at{struct_mpool} "fallback") <-{ PtrOp }
          LocInfoE loc_182 (use{PtrOp} (LocInfoE loc_183 ((LocInfoE loc_184 (!{PtrOp} (LocInfoE loc_185 ("from")))) at{struct_mpool} "fallback"))) ;
        locinfo: loc_160 ;
        LocInfoE loc_174 ((LocInfoE loc_175 ((LocInfoE loc_176 (!{PtrOp} (LocInfoE loc_177 ("from")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list") <-{ PtrOp }
          LocInfoE loc_178 (NULL) ;
        locinfo: loc_161 ;
        LocInfoE loc_169 ((LocInfoE loc_170 ((LocInfoE loc_171 (!{PtrOp} (LocInfoE loc_172 ("from")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list") <-{ PtrOp }
          LocInfoE loc_173 (NULL) ;
        locinfo: loc_162 ;
        expr: (LocInfoE loc_162 (Call (LocInfoE loc_164 (global_sl_unlock)) [@{expr} LocInfoE loc_165 (AnnotExpr 1%nat LockA (LocInfoE loc_165 (&(LocInfoE loc_166 ((LocInfoE loc_167 (!{PtrOp} (LocInfoE loc_168 ("from")))) at{struct_mpool} "lock"))))) ])) ;
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
        locinfo: loc_224 ;
        expr: (LocInfoE loc_224 (Call (LocInfoE loc_232 (global_mpool_init)) [@{expr} LocInfoE loc_233 (use{PtrOp} (LocInfoE loc_234 ("p"))) ;
        LocInfoE loc_235 (use{IntOp size_t} (LocInfoE loc_236 ((LocInfoE loc_237 (!{PtrOp} (LocInfoE loc_238 ("fallback")))) at{struct_mpool} "entry_size"))) ])) ;
        locinfo: loc_225 ;
        LocInfoE loc_226 ((LocInfoE loc_227 (!{PtrOp} (LocInfoE loc_228 ("p")))) at{struct_mpool} "fallback") <-{ PtrOp }
          LocInfoE loc_229 (use{PtrOp} (LocInfoE loc_230 ("fallback"))) ;
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
        locinfo: loc_340 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_340 ((LocInfoE loc_341 (use{PtrOp} (LocInfoE loc_342 ((LocInfoE loc_343 (!{PtrOp} (LocInfoE loc_344 ("p")))) at{struct_mpool} "fallback")))) ={PtrOp, PtrOp, i32} (LocInfoE loc_345 (NULL)))
        then
        locinfo: loc_337 ;
          Goto "#8"
        else
        locinfo: loc_244 ;
          Goto "#9"
      ]> $
      <[ "#1" :=
        locinfo: loc_244 ;
        LocInfoE loc_330 ("entry") <-{ PtrOp }
          LocInfoE loc_331 (use{PtrOp} (LocInfoE loc_332 ((LocInfoE loc_333 ((LocInfoE loc_334 (!{PtrOp} (LocInfoE loc_335 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list"))) ;
        locinfo: loc_245 ;
        LocInfoE loc_324 ("chunk") <-{ PtrOp }
          LocInfoE loc_325 (use{PtrOp} (LocInfoE loc_326 ((LocInfoE loc_327 ((LocInfoE loc_328 (!{PtrOp} (LocInfoE loc_329 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list"))) ;
        locinfo: loc_246 ;
        Goto "#2"
      ]> $
      <[ "#2" :=
        locinfo: loc_320 ;
        if{IntOp i32, None}: LocInfoE loc_320 ((LocInfoE loc_321 (use{PtrOp} (LocInfoE loc_322 ("entry")))) !={PtrOp, PtrOp, i32} (LocInfoE loc_323 (NULL)))
        then
        Goto "#3"
        else
        locinfo: loc_247 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        "ptr1" <-{ PtrOp }
          LocInfoE loc_316 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_316 (use{PtrOp} (LocInfoE loc_317 ("entry"))))) ;
        locinfo: loc_301 ;
        LocInfoE loc_311 ("entry") <-{ PtrOp }
          LocInfoE loc_312 (use{PtrOp} (LocInfoE loc_313 ((LocInfoE loc_314 (!{PtrOp} (LocInfoE loc_315 ("entry")))) at{struct_mpool_entry} "next"))) ;
        locinfo: loc_302 ;
        expr: (LocInfoE loc_302 (Call (LocInfoE loc_304 (global_mpool_free)) [@{expr} LocInfoE loc_305 (use{PtrOp} (LocInfoE loc_306 ((LocInfoE loc_307 (!{PtrOp} (LocInfoE loc_308 ("p")))) at{struct_mpool} "fallback"))) ;
        LocInfoE loc_309 (use{PtrOp} (LocInfoE loc_310 ("ptr1"))) ])) ;
        locinfo: loc_246 ;
        Goto "#2"
      ]> $
      <[ "#4" :=
        locinfo: loc_247 ;
        Goto "#5"
      ]> $
      <[ "#5" :=
        locinfo: loc_295 ;
        if{IntOp i32, None}: LocInfoE loc_295 ((LocInfoE loc_296 (use{PtrOp} (LocInfoE loc_297 ("chunk")))) !={PtrOp, PtrOp, i32} (LocInfoE loc_298 (NULL)))
        then
        Goto "#6"
        else
        locinfo: loc_248 ;
          Goto "#7"
      ]> $
      <[ "#6" :=
        "ptr2" <-{ PtrOp }
          LocInfoE loc_291 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_291 (use{PtrOp} (LocInfoE loc_292 ("chunk"))))) ;
        "size" <-{ IntOp size_t }
          LocInfoE loc_285 (use{IntOp size_t} (LocInfoE loc_286 ((LocInfoE loc_287 (!{PtrOp} (LocInfoE loc_288 ("chunk")))) at{struct_mpool_chunk} "size"))) ;
        locinfo: loc_268 ;
        LocInfoE loc_280 ("chunk") <-{ PtrOp }
          LocInfoE loc_281 (use{PtrOp} (LocInfoE loc_282 ((LocInfoE loc_283 (!{PtrOp} (LocInfoE loc_284 ("chunk")))) at{struct_mpool_chunk} "next_chunk"))) ;
        locinfo: loc_269 ;
        expr: (LocInfoE loc_269 (Call (LocInfoE loc_271 (global_mpool_add_chunk)) [@{expr} LocInfoE loc_272 (use{PtrOp} (LocInfoE loc_273 ((LocInfoE loc_274 (!{PtrOp} (LocInfoE loc_275 ("p")))) at{struct_mpool} "fallback"))) ;
        LocInfoE loc_276 (use{PtrOp} (LocInfoE loc_277 ("ptr2"))) ;
        LocInfoE loc_278 (use{IntOp size_t} (LocInfoE loc_279 ("size"))) ])) ;
        locinfo: loc_247 ;
        Goto "#5"
      ]> $
      <[ "#7" :=
        locinfo: loc_248 ;
        LocInfoE loc_260 ((LocInfoE loc_261 ((LocInfoE loc_262 (!{PtrOp} (LocInfoE loc_263 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list") <-{ PtrOp }
          LocInfoE loc_264 (NULL) ;
        locinfo: loc_249 ;
        LocInfoE loc_255 ((LocInfoE loc_256 ((LocInfoE loc_257 (!{PtrOp} (LocInfoE loc_258 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list") <-{ PtrOp }
          LocInfoE loc_259 (NULL) ;
        locinfo: loc_250 ;
        LocInfoE loc_251 ((LocInfoE loc_252 (!{PtrOp} (LocInfoE loc_253 ("p")))) at{struct_mpool} "fallback") <-{ PtrOp }
          LocInfoE loc_254 (NULL) ;
        Return (VOID)
      ]> $
      <[ "#8" :=
        locinfo: loc_337 ;
        Return (VOID)
      ]> $
      <[ "#9" :=
        locinfo: loc_244 ;
        Goto "#1"
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
        if{IntOp i32, Some "#1"}: LocInfoE loc_472 ((LocInfoE loc_473 (use{PtrOp} (LocInfoE loc_474 ((LocInfoE loc_475 ((LocInfoE loc_476 (!{PtrOp} (LocInfoE loc_477 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "entry_list")))) !={PtrOp, PtrOp, i32} (LocInfoE loc_478 (NULL)))
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
        if{IntOp i32, Some "#2"}: LocInfoE loc_438 ((LocInfoE loc_439 (use{PtrOp} (LocInfoE loc_440 ("chunk")))) ={PtrOp, PtrOp, i32} (LocInfoE loc_441 (NULL)))
        then
        locinfo: loc_433 ;
          Goto "#6"
        else
        locinfo: loc_423 ;
          Goto "#7"
      ]> $
      <[ "#2" :=
        locinfo: loc_423 ;
        if{IntOp i32, Some "#3"}: LocInfoE loc_423 ((LocInfoE loc_424 (use{IntOp size_t} (LocInfoE loc_425 ((LocInfoE loc_426 (!{PtrOp} (LocInfoE loc_427 ("p")))) at{struct_mpool} "entry_size")))) ≥{IntOp size_t, IntOp size_t, i32} (LocInfoE loc_428 (use{IntOp size_t} (LocInfoE loc_429 ((LocInfoE loc_430 (!{PtrOp} (LocInfoE loc_431 ("chunk")))) at{struct_mpool_chunk} "size")))))
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
          LocInfoE loc_539 (Call (LocInfoE loc_541 (global_mpool_alloc_no_fallback)) [@{expr} LocInfoE loc_542 (use{PtrOp} (LocInfoE loc_543 ("p"))) ]) ;
        locinfo: loc_535 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_535 ((LocInfoE loc_536 (use{PtrOp} (LocInfoE loc_537 ("ret")))) !={PtrOp, PtrOp, i32} (LocInfoE loc_538 (NULL)))
        then
        locinfo: loc_531 ;
          Goto "#8"
        else
        locinfo: loc_493 ;
          Goto "#9"
      ]> $
      <[ "#1" :=
        locinfo: loc_493 ;
        LocInfoE loc_525 ("p") <-{ PtrOp }
          LocInfoE loc_526 (use{PtrOp} (LocInfoE loc_527 ((LocInfoE loc_528 (!{PtrOp} (LocInfoE loc_529 ("p")))) at{struct_mpool} "fallback"))) ;
        locinfo: loc_494 ;
        Goto "#2"
      ]> $
      <[ "#2" :=
        locinfo: loc_521 ;
        if{IntOp i32, None}: LocInfoE loc_521 ((LocInfoE loc_522 (use{PtrOp} (LocInfoE loc_523 ("p")))) !={PtrOp, PtrOp, i32} (LocInfoE loc_524 (NULL)))
        then
        locinfo: loc_498 ;
          Goto "#3"
        else
        locinfo: loc_495 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_498 ;
        LocInfoE loc_515 ("ret") <-{ PtrOp }
          LocInfoE loc_516 (Call (LocInfoE loc_518 (global_mpool_alloc_no_fallback)) [@{expr} LocInfoE loc_519 (use{PtrOp} (LocInfoE loc_520 ("p"))) ]) ;
        locinfo: loc_511 ;
        if{IntOp i32, Some "#5"}: LocInfoE loc_511 ((LocInfoE loc_512 (use{PtrOp} (LocInfoE loc_513 ("ret")))) !={PtrOp, PtrOp, i32} (LocInfoE loc_514 (NULL)))
        then
        locinfo: loc_507 ;
          Goto "#6"
        else
        locinfo: loc_500 ;
          Goto "#7"
      ]> $
      <[ "#4" :=
        locinfo: loc_495 ;
        Return (LocInfoE loc_496 (NULL))
      ]> $
      <[ "#5" :=
        locinfo: loc_500 ;
        LocInfoE loc_501 ("p") <-{ PtrOp }
          LocInfoE loc_502 (use{PtrOp} (LocInfoE loc_503 ((LocInfoE loc_504 (!{PtrOp} (LocInfoE loc_505 ("p")))) at{struct_mpool} "fallback"))) ;
        locinfo: loc_494 ;
        Goto "#2"
      ]> $
      <[ "#6" :=
        locinfo: loc_507 ;
        Return (LocInfoE loc_508 (use{PtrOp} (LocInfoE loc_509 ("ret"))))
      ]> $
      <[ "#7" :=
        locinfo: loc_500 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        locinfo: loc_531 ;
        Return (LocInfoE loc_532 (use{PtrOp} (LocInfoE loc_533 ("ret"))))
      ]> $
      <[ "#9" :=
        locinfo: loc_493 ;
        Goto "#1"
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
        "ret" <-{ PtrOp } LocInfoE loc_775 (NULL) ;
        locinfo: loc_550 ;
        LocInfoE loc_767 ("align") <-{ IntOp size_t }
          LocInfoE loc_768 ((LocInfoE loc_769 (use{IntOp size_t} (LocInfoE loc_770 ("align")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_771 (use{IntOp size_t} (LocInfoE loc_772 ((LocInfoE loc_773 (!{PtrOp} (LocInfoE loc_774 ("p")))) at{struct_mpool} "entry_size"))))) ;
        locinfo: loc_551 ;
        expr: (LocInfoE loc_551 (Call (LocInfoE loc_762 (global_sl_lock)) [@{expr} LocInfoE loc_763 (&(LocInfoE loc_764 ((LocInfoE loc_765 (!{PtrOp} (LocInfoE loc_766 ("p")))) at{struct_mpool} "lock"))) ])) ;
        locinfo: loc_552 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_757 (&(LocInfoE loc_758 ((LocInfoE loc_759 (!{PtrOp} (LocInfoE loc_760 ("p")))) at{struct_mpool} "locked")))) ;
        locinfo: loc_554 ;
        LocInfoE loc_751 ("prev") <-{ PtrOp }
          LocInfoE loc_752 (&(LocInfoE loc_753 ((LocInfoE loc_754 ((LocInfoE loc_755 (!{PtrOp} (LocInfoE loc_756 ("p")))) at{struct_mpool} "locked")) at{struct_mpool_locked_inner} "chunk_list"))) ;
        locinfo: loc_555 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_745 ;
        if{IntOp i32, None}: LocInfoE loc_745 ((LocInfoE loc_746 (use{PtrOp} (LocInfoE loc_748 (!{PtrOp} (LocInfoE loc_749 ("prev")))))) !={PtrOp, PtrOp, i32} (LocInfoE loc_750 (NULL)))
        then
        Goto "#2"
        else
        locinfo: loc_556 ;
          Goto "#3"
      ]> $
      <[ "#10" :=
        locinfo: loc_625 ;
        LocInfoE loc_627 (!{PtrOp} (LocInfoE loc_628 ("prev"))) <-{ PtrOp }
          LocInfoE loc_629 (use{PtrOp} (LocInfoE loc_630 ("chunk_next"))) ;
        locinfo: loc_617 ;
        Goto "#6"
      ]> $
      <[ "#11" :=
        locinfo: loc_632 ;
        LocInfoE loc_662 ("new_chunk") <-{ PtrOp }
          LocInfoE loc_663 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_664 ((LocInfoE loc_665 (use{PtrOp} (LocInfoE loc_666 ("start")))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_667 ((LocInfoE loc_668 (use{IntOp size_t} (LocInfoE loc_669 ("count")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_670 (use{IntOp size_t} (LocInfoE loc_671 ((LocInfoE loc_672 (!{PtrOp} (LocInfoE loc_673 ("p")))) at{struct_mpool} "entry_size"))))))))) ;
        locinfo: loc_633 ;
        LocInfoE loc_646 ((LocInfoE loc_647 (!{PtrOp} (LocInfoE loc_648 ("new_chunk")))) at{struct_mpool_chunk} "size") <-{ IntOp size_t }
          LocInfoE loc_649 ((LocInfoE loc_650 (use{IntOp size_t} (LocInfoE loc_651 ("chunk_size")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_652 ((LocInfoE loc_653 (use{IntOp size_t} (LocInfoE loc_654 ("before_start")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_655 ((LocInfoE loc_656 (use{IntOp size_t} (LocInfoE loc_657 ("count")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_658 (use{IntOp size_t} (LocInfoE loc_659 ((LocInfoE loc_660 (!{PtrOp} (LocInfoE loc_661 ("p")))) at{struct_mpool} "entry_size"))))))))) ;
        locinfo: loc_634 ;
        LocInfoE loc_641 ((LocInfoE loc_642 (!{PtrOp} (LocInfoE loc_643 ("new_chunk")))) at{struct_mpool_chunk} "next_chunk") <-{ PtrOp }
          LocInfoE loc_644 (use{PtrOp} (LocInfoE loc_645 ("chunk_next"))) ;
        locinfo: loc_635 ;
        LocInfoE loc_637 (!{PtrOp} (LocInfoE loc_638 ("prev"))) <-{ PtrOp }
          LocInfoE loc_639 (use{PtrOp} (LocInfoE loc_640 ("new_chunk"))) ;
        locinfo: loc_617 ;
        Goto "#6"
      ]> $
      <[ "#12" :=
        locinfo: loc_575 ;
        Goto "#4"
      ]> $
      <[ "#2" :=
        "chunk" <-{ PtrOp }
          LocInfoE loc_739 (use{PtrOp} (LocInfoE loc_741 (!{PtrOp} (LocInfoE loc_742 ("prev"))))) ;
        locinfo: loc_571 ;
        annot: (LearnAlignmentAnnot) ;
        expr: (LocInfoE loc_735 (&(LocInfoE loc_737 (!{PtrOp} (LocInfoE loc_738 ("chunk")))))) ;
        locinfo: loc_573 ;
        expr: (LocInfoE loc_573 (Call (LocInfoE loc_727 (global_round_pointer_up)) [@{expr} LocInfoE loc_728 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_729 (use{PtrOp} (LocInfoE loc_730 ("chunk"))))) ;
        LocInfoE loc_731 (use{IntOp size_t} (LocInfoE loc_732 ("align"))) ;
        LocInfoE loc_733 (&(LocInfoE loc_734 ("before_start"))) ])) ;
        locinfo: loc_711 ;
        if{IntOp i32, Some "#4"}: LocInfoE loc_711 ((LocInfoE loc_712 ((LocInfoE loc_713 (use{IntOp size_t} (LocInfoE loc_714 ("before_start")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_715 ((LocInfoE loc_716 (use{IntOp size_t} (LocInfoE loc_717 ("count")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_718 (use{IntOp size_t} (LocInfoE loc_719 ((LocInfoE loc_720 (!{PtrOp} (LocInfoE loc_721 ("p")))) at{struct_mpool} "entry_size")))))))) ≤{IntOp size_t, IntOp size_t, i32} (LocInfoE loc_722 (use{IntOp size_t} (LocInfoE loc_723 ((LocInfoE loc_724 (!{PtrOp} (LocInfoE loc_725 ("chunk")))) at{struct_mpool_chunk} "size")))))
        then
        Goto "#5"
        else
        locinfo: loc_575 ;
          Goto "#12"
      ]> $
      <[ "#3" :=
        locinfo: loc_556 ;
        expr: (LocInfoE loc_556 (Call (LocInfoE loc_561 (global_sl_unlock)) [@{expr} LocInfoE loc_562 (AnnotExpr 1%nat LockA (LocInfoE loc_562 (&(LocInfoE loc_563 ((LocInfoE loc_564 (!{PtrOp} (LocInfoE loc_565 ("p")))) at{struct_mpool} "lock"))))) ])) ;
        locinfo: loc_557 ;
        Return (LocInfoE loc_558 (use{PtrOp} (LocInfoE loc_559 ("ret"))))
      ]> $
      <[ "#4" :=
        locinfo: loc_575 ;
        LocInfoE loc_576 ("prev") <-{ PtrOp }
          LocInfoE loc_577 (&(LocInfoE loc_578 ((LocInfoE loc_579 (!{PtrOp} (LocInfoE loc_580 ("chunk")))) at{struct_mpool_chunk} "next_chunk"))) ;
        locinfo: loc_555 ;
        Goto "#1"
      ]> $
      <[ "#5" :=
        "chunk_size" <-{ IntOp size_t }
          LocInfoE loc_704 (use{IntOp size_t} (LocInfoE loc_705 ((LocInfoE loc_706 (!{PtrOp} (LocInfoE loc_707 ("chunk")))) at{struct_mpool_chunk} "size"))) ;
        "chunk_next" <-{ PtrOp }
          LocInfoE loc_698 (use{PtrOp} (LocInfoE loc_699 ((LocInfoE loc_700 (!{PtrOp} (LocInfoE loc_701 ("chunk")))) at{struct_mpool_chunk} "next_chunk"))) ;
        locinfo: loc_584 ;
        annot: (ToUninit) ;
        expr: (LocInfoE loc_694 (&(LocInfoE loc_696 (!{PtrOp} (LocInfoE loc_697 ("chunk")))))) ;
        locinfo: loc_586 ;
        LocInfoE loc_687 ("start") <-{ PtrOp }
          LocInfoE loc_688 ((LocInfoE loc_689 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_690 (use{PtrOp} (LocInfoE loc_691 ("chunk")))))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_692 (use{IntOp size_t} (LocInfoE loc_693 ("before_start"))))) ;
        locinfo: loc_674 ;
        if{IntOp i32, Some "#6"}: LocInfoE loc_674 ((LocInfoE loc_675 ((LocInfoE loc_676 (use{IntOp size_t} (LocInfoE loc_677 ("before_start")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_678 ((LocInfoE loc_679 (use{IntOp size_t} (LocInfoE loc_680 ("count")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_681 (use{IntOp size_t} (LocInfoE loc_682 ((LocInfoE loc_683 (!{PtrOp} (LocInfoE loc_684 ("p")))) at{struct_mpool} "entry_size")))))))) ={IntOp size_t, IntOp size_t, i32} (LocInfoE loc_685 (use{IntOp size_t} (LocInfoE loc_686 ("chunk_size")))))
        then
        locinfo: loc_625 ;
          Goto "#10"
        else
        locinfo: loc_632 ;
          Goto "#11"
      ]> $
      <[ "#6" :=
        locinfo: loc_617 ;
        if{IntOp i32, Some "#7"}: LocInfoE loc_617 ((LocInfoE loc_618 (use{IntOp size_t} (LocInfoE loc_619 ("before_start")))) ≥{IntOp size_t, IntOp size_t, i32} (LocInfoE loc_620 (use{IntOp size_t} (LocInfoE loc_621 ((LocInfoE loc_622 (!{PtrOp} (LocInfoE loc_623 ("p")))) at{struct_mpool} "entry_size")))))
        then
        locinfo: loc_596 ;
          Goto "#8"
        else
        locinfo: loc_589 ;
          Goto "#9"
      ]> $
      <[ "#7" :=
        locinfo: loc_589 ;
        LocInfoE loc_591 ("ret") <-{ PtrOp }
          LocInfoE loc_592 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_593 (use{PtrOp} (LocInfoE loc_594 ("start"))))) ;
        locinfo: loc_556 ;
        Goto "#3"
      ]> $
      <[ "#8" :=
        locinfo: loc_596 ;
        LocInfoE loc_609 ((LocInfoE loc_610 (!{PtrOp} (LocInfoE loc_611 ("chunk")))) at{struct_mpool_chunk} "next_chunk") <-{ PtrOp }
          LocInfoE loc_612 (use{PtrOp} (LocInfoE loc_614 (!{PtrOp} (LocInfoE loc_615 ("prev"))))) ;
        locinfo: loc_597 ;
        LocInfoE loc_605 (!{PtrOp} (LocInfoE loc_606 ("prev"))) <-{ PtrOp }
          LocInfoE loc_607 (use{PtrOp} (LocInfoE loc_608 ("chunk"))) ;
        locinfo: loc_598 ;
        LocInfoE loc_599 ((LocInfoE loc_600 (!{PtrOp} (LocInfoE loc_601 ("chunk")))) at{struct_mpool_chunk} "size") <-{ IntOp size_t }
          LocInfoE loc_602 (use{IntOp size_t} (LocInfoE loc_603 ("before_start"))) ;
        locinfo: loc_589 ;
        Goto "#7"
      ]> $
      <[ "#9" :=
        locinfo: loc_589 ;
        Goto "#7"
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
          LocInfoE loc_832 (Call (LocInfoE loc_834 (global_mpool_alloc_contiguous_no_fallback)) [@{expr} LocInfoE loc_835 (use{PtrOp} (LocInfoE loc_836 ("p"))) ;
          LocInfoE loc_837 (use{IntOp size_t} (LocInfoE loc_838 ("count"))) ;
          LocInfoE loc_839 (use{IntOp size_t} (LocInfoE loc_840 ("align"))) ]) ;
        locinfo: loc_828 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_828 ((LocInfoE loc_829 (use{PtrOp} (LocInfoE loc_830 ("ret")))) !={PtrOp, PtrOp, i32} (LocInfoE loc_831 (NULL)))
        then
        locinfo: loc_824 ;
          Goto "#8"
        else
        locinfo: loc_782 ;
          Goto "#9"
      ]> $
      <[ "#1" :=
        locinfo: loc_782 ;
        LocInfoE loc_818 ("p") <-{ PtrOp }
          LocInfoE loc_819 (use{PtrOp} (LocInfoE loc_820 ((LocInfoE loc_821 (!{PtrOp} (LocInfoE loc_822 ("p")))) at{struct_mpool} "fallback"))) ;
        locinfo: loc_783 ;
        Goto "#2"
      ]> $
      <[ "#2" :=
        locinfo: loc_814 ;
        if{IntOp i32, None}: LocInfoE loc_814 ((LocInfoE loc_815 (use{PtrOp} (LocInfoE loc_816 ("p")))) !={PtrOp, PtrOp, i32} (LocInfoE loc_817 (NULL)))
        then
        locinfo: loc_787 ;
          Goto "#3"
        else
        locinfo: loc_784 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_787 ;
        LocInfoE loc_804 ("ret") <-{ PtrOp }
          LocInfoE loc_805 (Call (LocInfoE loc_807 (global_mpool_alloc_contiguous_no_fallback)) [@{expr} LocInfoE loc_808 (use{PtrOp} (LocInfoE loc_809 ("p"))) ;
          LocInfoE loc_810 (use{IntOp size_t} (LocInfoE loc_811 ("count"))) ;
          LocInfoE loc_812 (use{IntOp size_t} (LocInfoE loc_813 ("align"))) ]) ;
        locinfo: loc_800 ;
        if{IntOp i32, Some "#5"}: LocInfoE loc_800 ((LocInfoE loc_801 (use{PtrOp} (LocInfoE loc_802 ("ret")))) !={PtrOp, PtrOp, i32} (LocInfoE loc_803 (NULL)))
        then
        locinfo: loc_796 ;
          Goto "#6"
        else
        locinfo: loc_789 ;
          Goto "#7"
      ]> $
      <[ "#4" :=
        locinfo: loc_784 ;
        Return (LocInfoE loc_785 (NULL))
      ]> $
      <[ "#5" :=
        locinfo: loc_789 ;
        LocInfoE loc_790 ("p") <-{ PtrOp }
          LocInfoE loc_791 (use{PtrOp} (LocInfoE loc_792 ((LocInfoE loc_793 (!{PtrOp} (LocInfoE loc_794 ("p")))) at{struct_mpool} "fallback"))) ;
        locinfo: loc_783 ;
        Goto "#2"
      ]> $
      <[ "#6" :=
        locinfo: loc_796 ;
        Return (LocInfoE loc_797 (use{PtrOp} (LocInfoE loc_798 ("ret"))))
      ]> $
      <[ "#7" :=
        locinfo: loc_789 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        locinfo: loc_824 ;
        Return (LocInfoE loc_825 (use{PtrOp} (LocInfoE loc_826 ("ret"))))
      ]> $
      <[ "#9" :=
        locinfo: loc_782 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.
End code.
