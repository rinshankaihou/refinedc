From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
From refinedc.examples.spinlock Require Import spinlock_annot.
Set Default Proof Using "Type".

(* Generated from [theories/examples/mpool/mpool.c]. *)
Section code.
  Definition file_0 : string := "theories/examples/mpool/mpool.c".
  Definition loc_2 : location_info := LocationInfo file_0 223 2 223 19.
  Definition loc_3 : location_info := LocationInfo file_0 223 19 223 3.
  Definition loc_4 : location_info := LocationInfo file_0 226 2 228 3.
  Definition loc_5 : location_info := LocationInfo file_0 230 2 230 16.
  Definition loc_6 : location_info := LocationInfo file_0 231 2 231 21.
  Definition loc_7 : location_info := LocationInfo file_0 233 2 233 20.
  Definition loc_8 : location_info := LocationInfo file_0 234 2 234 40.
  Definition loc_9 : location_info := LocationInfo file_0 234 40 234 3.
  Definition loc_10 : location_info := LocationInfo file_0 235 2 235 43.
  Definition loc_11 : location_info := LocationInfo file_0 236 2 236 31.
  Definition loc_12 : location_info := LocationInfo file_0 237 2 237 22.
  Definition loc_13 : location_info := LocationInfo file_0 239 2 239 11.
  Definition loc_14 : location_info := LocationInfo file_0 239 9 239 10.
  Definition loc_15 : location_info := LocationInfo file_0 237 2 237 11.
  Definition loc_16 : location_info := LocationInfo file_0 237 2 237 11.
  Definition loc_17 : location_info := LocationInfo file_0 237 12 237 20.
  Definition loc_18 : location_info := LocationInfo file_0 237 13 237 20.
  Definition loc_19 : location_info := LocationInfo file_0 237 13 237 14.
  Definition loc_20 : location_info := LocationInfo file_0 237 13 237 14.
  Definition loc_21 : location_info := LocationInfo file_0 236 2 236 22.
  Definition loc_22 : location_info := LocationInfo file_0 236 2 236 11.
  Definition loc_23 : location_info := LocationInfo file_0 236 2 236 3.
  Definition loc_24 : location_info := LocationInfo file_0 236 2 236 3.
  Definition loc_25 : location_info := LocationInfo file_0 236 25 236 30.
  Definition loc_26 : location_info := LocationInfo file_0 236 25 236 30.
  Definition loc_27 : location_info := LocationInfo file_0 235 2 235 19.
  Definition loc_28 : location_info := LocationInfo file_0 235 2 235 7.
  Definition loc_29 : location_info := LocationInfo file_0 235 2 235 7.
  Definition loc_30 : location_info := LocationInfo file_0 235 22 235 42.
  Definition loc_31 : location_info := LocationInfo file_0 235 22 235 42.
  Definition loc_32 : location_info := LocationInfo file_0 235 22 235 31.
  Definition loc_33 : location_info := LocationInfo file_0 235 22 235 23.
  Definition loc_34 : location_info := LocationInfo file_0 235 22 235 23.
  Definition loc_35 : location_info := LocationInfo file_0 234 27 234 39.
  Definition loc_36 : location_info := LocationInfo file_0 234 28 234 39.
  Definition loc_37 : location_info := LocationInfo file_0 234 29 234 30.
  Definition loc_38 : location_info := LocationInfo file_0 234 29 234 30.
  Definition loc_39 : location_info := LocationInfo file_0 233 2 233 9.
  Definition loc_40 : location_info := LocationInfo file_0 233 2 233 9.
  Definition loc_41 : location_info := LocationInfo file_0 233 10 233 18.
  Definition loc_42 : location_info := LocationInfo file_0 233 11 233 18.
  Definition loc_43 : location_info := LocationInfo file_0 233 11 233 12.
  Definition loc_44 : location_info := LocationInfo file_0 233 11 233 12.
  Definition loc_45 : location_info := LocationInfo file_0 231 2 231 13.
  Definition loc_46 : location_info := LocationInfo file_0 231 2 231 7.
  Definition loc_47 : location_info := LocationInfo file_0 231 2 231 7.
  Definition loc_48 : location_info := LocationInfo file_0 231 16 231 20.
  Definition loc_49 : location_info := LocationInfo file_0 231 16 231 20.
  Definition loc_50 : location_info := LocationInfo file_0 230 2 230 7.
  Definition loc_51 : location_info := LocationInfo file_0 230 10 230 15.
  Definition loc_52 : location_info := LocationInfo file_0 230 10 230 15.
  Definition loc_53 : location_info := LocationInfo file_0 226 26 228 3.
  Definition loc_54 : location_info := LocationInfo file_0 227 4 227 13.
  Definition loc_55 : location_info := LocationInfo file_0 227 11 227 12.
  Definition loc_57 : location_info := LocationInfo file_0 226 6 226 24.
  Definition loc_58 : location_info := LocationInfo file_0 226 6 226 10.
  Definition loc_59 : location_info := LocationInfo file_0 226 6 226 10.
  Definition loc_60 : location_info := LocationInfo file_0 226 14 226 24.
  Definition loc_61 : location_info := LocationInfo file_0 226 23 226 24.
  Definition loc_62 : location_info := LocationInfo file_0 223 2 223 18.
  Definition loc_63 : location_info := LocationInfo file_0 223 3 223 18.
  Definition loc_64 : location_info := LocationInfo file_0 223 4 223 5.
  Definition loc_65 : location_info := LocationInfo file_0 223 4 223 5.
  Definition loc_68 : location_info := LocationInfo file_0 333 2 333 30.
  Definition loc_69 : location_info := LocationInfo file_0 334 2 334 19.
  Definition loc_70 : location_info := LocationInfo file_0 334 19 334 3.
  Definition loc_71 : location_info := LocationInfo file_0 337 2 337 20.
  Definition loc_72 : location_info := LocationInfo file_0 338 2 338 40.
  Definition loc_73 : location_info := LocationInfo file_0 338 40 338 3.
  Definition loc_74 : location_info := LocationInfo file_0 339 2 339 33.
  Definition loc_75 : location_info := LocationInfo file_0 340 2 340 27.
  Definition loc_76 : location_info := LocationInfo file_0 341 2 341 22.
  Definition loc_77 : location_info := LocationInfo file_0 341 2 341 11.
  Definition loc_78 : location_info := LocationInfo file_0 341 2 341 11.
  Definition loc_79 : location_info := LocationInfo file_0 341 12 341 20.
  Definition loc_80 : location_info := LocationInfo file_0 341 13 341 20.
  Definition loc_81 : location_info := LocationInfo file_0 341 13 341 14.
  Definition loc_82 : location_info := LocationInfo file_0 341 13 341 14.
  Definition loc_83 : location_info := LocationInfo file_0 340 2 340 22.
  Definition loc_84 : location_info := LocationInfo file_0 340 2 340 11.
  Definition loc_85 : location_info := LocationInfo file_0 340 2 340 3.
  Definition loc_86 : location_info := LocationInfo file_0 340 2 340 3.
  Definition loc_87 : location_info := LocationInfo file_0 340 25 340 26.
  Definition loc_88 : location_info := LocationInfo file_0 340 25 340 26.
  Definition loc_89 : location_info := LocationInfo file_0 339 2 339 9.
  Definition loc_90 : location_info := LocationInfo file_0 339 2 339 3.
  Definition loc_91 : location_info := LocationInfo file_0 339 2 339 3.
  Definition loc_92 : location_info := LocationInfo file_0 339 12 339 32.
  Definition loc_93 : location_info := LocationInfo file_0 339 12 339 32.
  Definition loc_94 : location_info := LocationInfo file_0 339 12 339 21.
  Definition loc_95 : location_info := LocationInfo file_0 339 12 339 13.
  Definition loc_96 : location_info := LocationInfo file_0 339 12 339 13.
  Definition loc_97 : location_info := LocationInfo file_0 338 27 338 39.
  Definition loc_98 : location_info := LocationInfo file_0 338 28 338 39.
  Definition loc_99 : location_info := LocationInfo file_0 338 29 338 30.
  Definition loc_100 : location_info := LocationInfo file_0 338 29 338 30.
  Definition loc_101 : location_info := LocationInfo file_0 337 2 337 9.
  Definition loc_102 : location_info := LocationInfo file_0 337 2 337 9.
  Definition loc_103 : location_info := LocationInfo file_0 337 10 337 18.
  Definition loc_104 : location_info := LocationInfo file_0 337 11 337 18.
  Definition loc_105 : location_info := LocationInfo file_0 337 11 337 12.
  Definition loc_106 : location_info := LocationInfo file_0 337 11 337 12.
  Definition loc_107 : location_info := LocationInfo file_0 334 2 334 18.
  Definition loc_108 : location_info := LocationInfo file_0 334 3 334 18.
  Definition loc_109 : location_info := LocationInfo file_0 334 4 334 5.
  Definition loc_110 : location_info := LocationInfo file_0 334 4 334 5.
  Definition loc_111 : location_info := LocationInfo file_0 333 26 333 29.
  Definition loc_112 : location_info := LocationInfo file_0 333 26 333 29.
  Definition loc_117 : location_info := LocationInfo file_0 110 2 110 29.
  Definition loc_118 : location_info := LocationInfo file_0 111 2 111 40.
  Definition loc_119 : location_info := LocationInfo file_0 112 2 112 40.
  Definition loc_120 : location_info := LocationInfo file_0 113 2 113 31.
  Definition loc_121 : location_info := LocationInfo file_0 114 2 114 20.
  Definition loc_122 : location_info := LocationInfo file_0 114 2 114 9.
  Definition loc_123 : location_info := LocationInfo file_0 114 2 114 9.
  Definition loc_124 : location_info := LocationInfo file_0 114 10 114 18.
  Definition loc_125 : location_info := LocationInfo file_0 114 11 114 18.
  Definition loc_126 : location_info := LocationInfo file_0 114 11 114 12.
  Definition loc_127 : location_info := LocationInfo file_0 114 11 114 12.
  Definition loc_128 : location_info := LocationInfo file_0 113 2 113 13.
  Definition loc_129 : location_info := LocationInfo file_0 113 2 113 3.
  Definition loc_130 : location_info := LocationInfo file_0 113 2 113 3.
  Definition loc_131 : location_info := LocationInfo file_0 113 16 113 30.
  Definition loc_132 : location_info := LocationInfo file_0 112 2 112 22.
  Definition loc_133 : location_info := LocationInfo file_0 112 2 112 11.
  Definition loc_134 : location_info := LocationInfo file_0 112 2 112 3.
  Definition loc_135 : location_info := LocationInfo file_0 112 2 112 3.
  Definition loc_136 : location_info := LocationInfo file_0 112 25 112 39.
  Definition loc_137 : location_info := LocationInfo file_0 111 2 111 22.
  Definition loc_138 : location_info := LocationInfo file_0 111 2 111 11.
  Definition loc_139 : location_info := LocationInfo file_0 111 2 111 3.
  Definition loc_140 : location_info := LocationInfo file_0 111 2 111 3.
  Definition loc_141 : location_info := LocationInfo file_0 111 25 111 39.
  Definition loc_142 : location_info := LocationInfo file_0 110 2 110 15.
  Definition loc_143 : location_info := LocationInfo file_0 110 2 110 3.
  Definition loc_144 : location_info := LocationInfo file_0 110 2 110 3.
  Definition loc_145 : location_info := LocationInfo file_0 110 18 110 28.
  Definition loc_146 : location_info := LocationInfo file_0 110 18 110 28.
  Definition loc_149 : location_info := LocationInfo file_0 129 2 129 34.
  Definition loc_150 : location_info := LocationInfo file_0 131 2 131 23.
  Definition loc_151 : location_info := LocationInfo file_0 132 2 132 43.
  Definition loc_152 : location_info := LocationInfo file_0 132 43 132 3.
  Definition loc_153 : location_info := LocationInfo file_0 134 2 134 49.
  Definition loc_154 : location_info := LocationInfo file_0 135 2 135 49.
  Definition loc_155 : location_info := LocationInfo file_0 136 2 136 31.
  Definition loc_156 : location_info := LocationInfo file_0 138 2 138 43.
  Definition loc_157 : location_info := LocationInfo file_0 139 2 139 43.
  Definition loc_158 : location_info := LocationInfo file_0 142 2 142 25.
  Definition loc_159 : location_info := LocationInfo file_0 142 2 142 11.
  Definition loc_160 : location_info := LocationInfo file_0 142 2 142 11.
  Definition loc_161 : location_info := LocationInfo file_0 142 12 142 23.
  Definition loc_162 : location_info := LocationInfo file_0 142 13 142 23.
  Definition loc_163 : location_info := LocationInfo file_0 142 13 142 17.
  Definition loc_164 : location_info := LocationInfo file_0 142 13 142 17.
  Definition loc_165 : location_info := LocationInfo file_0 139 2 139 25.
  Definition loc_166 : location_info := LocationInfo file_0 139 2 139 14.
  Definition loc_167 : location_info := LocationInfo file_0 139 2 139 6.
  Definition loc_168 : location_info := LocationInfo file_0 139 2 139 6.
  Definition loc_169 : location_info := LocationInfo file_0 139 28 139 42.
  Definition loc_170 : location_info := LocationInfo file_0 138 2 138 25.
  Definition loc_171 : location_info := LocationInfo file_0 138 2 138 14.
  Definition loc_172 : location_info := LocationInfo file_0 138 2 138 6.
  Definition loc_173 : location_info := LocationInfo file_0 138 2 138 6.
  Definition loc_174 : location_info := LocationInfo file_0 138 28 138 42.
  Definition loc_175 : location_info := LocationInfo file_0 136 2 136 13.
  Definition loc_176 : location_info := LocationInfo file_0 136 2 136 3.
  Definition loc_177 : location_info := LocationInfo file_0 136 2 136 3.
  Definition loc_178 : location_info := LocationInfo file_0 136 16 136 30.
  Definition loc_179 : location_info := LocationInfo file_0 136 16 136 30.
  Definition loc_180 : location_info := LocationInfo file_0 136 16 136 20.
  Definition loc_181 : location_info := LocationInfo file_0 136 16 136 20.
  Definition loc_182 : location_info := LocationInfo file_0 135 2 135 22.
  Definition loc_183 : location_info := LocationInfo file_0 135 2 135 11.
  Definition loc_184 : location_info := LocationInfo file_0 135 2 135 3.
  Definition loc_185 : location_info := LocationInfo file_0 135 2 135 3.
  Definition loc_186 : location_info := LocationInfo file_0 135 25 135 48.
  Definition loc_187 : location_info := LocationInfo file_0 135 25 135 48.
  Definition loc_188 : location_info := LocationInfo file_0 135 25 135 37.
  Definition loc_189 : location_info := LocationInfo file_0 135 25 135 29.
  Definition loc_190 : location_info := LocationInfo file_0 135 25 135 29.
  Definition loc_191 : location_info := LocationInfo file_0 134 2 134 22.
  Definition loc_192 : location_info := LocationInfo file_0 134 2 134 11.
  Definition loc_193 : location_info := LocationInfo file_0 134 2 134 3.
  Definition loc_194 : location_info := LocationInfo file_0 134 2 134 3.
  Definition loc_195 : location_info := LocationInfo file_0 134 25 134 48.
  Definition loc_196 : location_info := LocationInfo file_0 134 25 134 48.
  Definition loc_197 : location_info := LocationInfo file_0 134 25 134 37.
  Definition loc_198 : location_info := LocationInfo file_0 134 25 134 29.
  Definition loc_199 : location_info := LocationInfo file_0 134 25 134 29.
  Definition loc_200 : location_info := LocationInfo file_0 132 27 132 42.
  Definition loc_201 : location_info := LocationInfo file_0 132 28 132 42.
  Definition loc_202 : location_info := LocationInfo file_0 132 29 132 33.
  Definition loc_203 : location_info := LocationInfo file_0 132 29 132 33.
  Definition loc_204 : location_info := LocationInfo file_0 131 2 131 9.
  Definition loc_205 : location_info := LocationInfo file_0 131 2 131 9.
  Definition loc_206 : location_info := LocationInfo file_0 131 10 131 21.
  Definition loc_207 : location_info := LocationInfo file_0 131 11 131 21.
  Definition loc_208 : location_info := LocationInfo file_0 131 11 131 15.
  Definition loc_209 : location_info := LocationInfo file_0 131 11 131 15.
  Definition loc_210 : location_info := LocationInfo file_0 129 2 129 12.
  Definition loc_211 : location_info := LocationInfo file_0 129 2 129 12.
  Definition loc_212 : location_info := LocationInfo file_0 129 13 129 14.
  Definition loc_213 : location_info := LocationInfo file_0 129 13 129 14.
  Definition loc_214 : location_info := LocationInfo file_0 129 16 129 32.
  Definition loc_215 : location_info := LocationInfo file_0 129 16 129 32.
  Definition loc_216 : location_info := LocationInfo file_0 129 16 129 20.
  Definition loc_217 : location_info := LocationInfo file_0 129 16 129 20.
  Definition loc_220 : location_info := LocationInfo file_0 154 2 154 38.
  Definition loc_221 : location_info := LocationInfo file_0 155 2 155 25.
  Definition loc_222 : location_info := LocationInfo file_0 155 2 155 13.
  Definition loc_223 : location_info := LocationInfo file_0 155 2 155 3.
  Definition loc_224 : location_info := LocationInfo file_0 155 2 155 3.
  Definition loc_225 : location_info := LocationInfo file_0 155 16 155 24.
  Definition loc_226 : location_info := LocationInfo file_0 155 16 155 24.
  Definition loc_227 : location_info := LocationInfo file_0 154 2 154 12.
  Definition loc_228 : location_info := LocationInfo file_0 154 2 154 12.
  Definition loc_229 : location_info := LocationInfo file_0 154 13 154 14.
  Definition loc_230 : location_info := LocationInfo file_0 154 13 154 14.
  Definition loc_231 : location_info := LocationInfo file_0 154 16 154 36.
  Definition loc_232 : location_info := LocationInfo file_0 154 16 154 36.
  Definition loc_233 : location_info := LocationInfo file_0 154 16 154 24.
  Definition loc_234 : location_info := LocationInfo file_0 154 16 154 24.
  Definition loc_237 : location_info := LocationInfo file_0 169 2 171 3.
  Definition loc_238 : location_info := LocationInfo file_0 173 2 173 31.
  Definition loc_239 : location_info := LocationInfo file_0 174 2 174 31.
  Definition loc_240 : location_info := LocationInfo file_0 179 2 183 3.
  Definition loc_241 : location_info := LocationInfo file_0 189 2 195 3.
  Definition loc_242 : location_info := LocationInfo file_0 197 2 197 40.
  Definition loc_243 : location_info := LocationInfo file_0 198 2 198 40.
  Definition loc_244 : location_info := LocationInfo file_0 199 2 199 31.
  Definition loc_245 : location_info := LocationInfo file_0 199 2 199 13.
  Definition loc_246 : location_info := LocationInfo file_0 199 2 199 3.
  Definition loc_247 : location_info := LocationInfo file_0 199 2 199 3.
  Definition loc_248 : location_info := LocationInfo file_0 199 16 199 30.
  Definition loc_249 : location_info := LocationInfo file_0 198 2 198 22.
  Definition loc_250 : location_info := LocationInfo file_0 198 2 198 11.
  Definition loc_251 : location_info := LocationInfo file_0 198 2 198 3.
  Definition loc_252 : location_info := LocationInfo file_0 198 2 198 3.
  Definition loc_253 : location_info := LocationInfo file_0 198 25 198 39.
  Definition loc_254 : location_info := LocationInfo file_0 197 2 197 22.
  Definition loc_255 : location_info := LocationInfo file_0 197 2 197 11.
  Definition loc_256 : location_info := LocationInfo file_0 197 2 197 3.
  Definition loc_257 : location_info := LocationInfo file_0 197 2 197 3.
  Definition loc_258 : location_info := LocationInfo file_0 197 25 197 39.
  Definition loc_259 : location_info := LocationInfo file_0 189 2 195 3.
  Definition loc_260 : location_info := LocationInfo file_0 189 34 195 3.
  Definition loc_261 : location_info := LocationInfo file_0 190 4 190 23.
  Definition loc_262 : location_info := LocationInfo file_0 191 4 191 30.
  Definition loc_263 : location_info := LocationInfo file_0 193 4 193 30.
  Definition loc_264 : location_info := LocationInfo file_0 194 4 194 45.
  Definition loc_265 : location_info := LocationInfo file_0 189 2 195 3.
  Definition loc_266 : location_info := LocationInfo file_0 189 2 195 3.
  Definition loc_267 : location_info := LocationInfo file_0 194 4 194 19.
  Definition loc_268 : location_info := LocationInfo file_0 194 4 194 19.
  Definition loc_269 : location_info := LocationInfo file_0 194 20 194 31.
  Definition loc_270 : location_info := LocationInfo file_0 194 20 194 31.
  Definition loc_271 : location_info := LocationInfo file_0 194 20 194 21.
  Definition loc_272 : location_info := LocationInfo file_0 194 20 194 21.
  Definition loc_273 : location_info := LocationInfo file_0 194 33 194 37.
  Definition loc_274 : location_info := LocationInfo file_0 194 33 194 37.
  Definition loc_275 : location_info := LocationInfo file_0 194 39 194 43.
  Definition loc_276 : location_info := LocationInfo file_0 194 39 194 43.
  Definition loc_277 : location_info := LocationInfo file_0 193 4 193 9.
  Definition loc_278 : location_info := LocationInfo file_0 193 12 193 29.
  Definition loc_279 : location_info := LocationInfo file_0 193 12 193 29.
  Definition loc_280 : location_info := LocationInfo file_0 193 12 193 17.
  Definition loc_281 : location_info := LocationInfo file_0 193 12 193 17.
  Definition loc_282 : location_info := LocationInfo file_0 191 18 191 29.
  Definition loc_283 : location_info := LocationInfo file_0 191 18 191 29.
  Definition loc_284 : location_info := LocationInfo file_0 191 18 191 23.
  Definition loc_285 : location_info := LocationInfo file_0 191 18 191 23.
  Definition loc_288 : location_info := LocationInfo file_0 190 17 190 22.
  Definition loc_289 : location_info := LocationInfo file_0 190 17 190 22.
  Definition loc_292 : location_info := LocationInfo file_0 189 9 189 32.
  Definition loc_293 : location_info := LocationInfo file_0 189 9 189 14.
  Definition loc_294 : location_info := LocationInfo file_0 189 9 189 14.
  Definition loc_295 : location_info := LocationInfo file_0 189 18 189 32.
  Definition loc_296 : location_info := LocationInfo file_0 179 2 183 3.
  Definition loc_297 : location_info := LocationInfo file_0 179 34 183 3.
  Definition loc_298 : location_info := LocationInfo file_0 180 4 180 23.
  Definition loc_299 : location_info := LocationInfo file_0 181 4 181 24.
  Definition loc_300 : location_info := LocationInfo file_0 182 4 182 34.
  Definition loc_301 : location_info := LocationInfo file_0 179 2 183 3.
  Definition loc_302 : location_info := LocationInfo file_0 179 2 183 3.
  Definition loc_303 : location_info := LocationInfo file_0 182 4 182 14.
  Definition loc_304 : location_info := LocationInfo file_0 182 4 182 14.
  Definition loc_305 : location_info := LocationInfo file_0 182 15 182 26.
  Definition loc_306 : location_info := LocationInfo file_0 182 15 182 26.
  Definition loc_307 : location_info := LocationInfo file_0 182 15 182 16.
  Definition loc_308 : location_info := LocationInfo file_0 182 15 182 16.
  Definition loc_309 : location_info := LocationInfo file_0 182 28 182 32.
  Definition loc_310 : location_info := LocationInfo file_0 182 28 182 32.
  Definition loc_311 : location_info := LocationInfo file_0 181 4 181 9.
  Definition loc_312 : location_info := LocationInfo file_0 181 12 181 23.
  Definition loc_313 : location_info := LocationInfo file_0 181 12 181 23.
  Definition loc_314 : location_info := LocationInfo file_0 181 12 181 17.
  Definition loc_315 : location_info := LocationInfo file_0 181 12 181 17.
  Definition loc_316 : location_info := LocationInfo file_0 180 17 180 22.
  Definition loc_317 : location_info := LocationInfo file_0 180 17 180 22.
  Definition loc_320 : location_info := LocationInfo file_0 179 9 179 32.
  Definition loc_321 : location_info := LocationInfo file_0 179 9 179 14.
  Definition loc_322 : location_info := LocationInfo file_0 179 9 179 14.
  Definition loc_323 : location_info := LocationInfo file_0 179 18 179 32.
  Definition loc_324 : location_info := LocationInfo file_0 174 2 174 7.
  Definition loc_325 : location_info := LocationInfo file_0 174 10 174 30.
  Definition loc_326 : location_info := LocationInfo file_0 174 10 174 30.
  Definition loc_327 : location_info := LocationInfo file_0 174 10 174 19.
  Definition loc_328 : location_info := LocationInfo file_0 174 10 174 11.
  Definition loc_329 : location_info := LocationInfo file_0 174 10 174 11.
  Definition loc_330 : location_info := LocationInfo file_0 173 2 173 7.
  Definition loc_331 : location_info := LocationInfo file_0 173 10 173 30.
  Definition loc_332 : location_info := LocationInfo file_0 173 10 173 30.
  Definition loc_333 : location_info := LocationInfo file_0 173 10 173 19.
  Definition loc_334 : location_info := LocationInfo file_0 173 10 173 11.
  Definition loc_335 : location_info := LocationInfo file_0 173 10 173 11.
  Definition loc_336 : location_info := LocationInfo file_0 169 37 171 3.
  Definition loc_337 : location_info := LocationInfo file_0 170 4 170 11.
  Definition loc_340 : location_info := LocationInfo file_0 169 6 169 35.
  Definition loc_341 : location_info := LocationInfo file_0 169 6 169 17.
  Definition loc_342 : location_info := LocationInfo file_0 169 6 169 17.
  Definition loc_343 : location_info := LocationInfo file_0 169 6 169 7.
  Definition loc_344 : location_info := LocationInfo file_0 169 6 169 7.
  Definition loc_345 : location_info := LocationInfo file_0 169 21 169 35.
  Definition loc_348 : location_info := LocationInfo file_0 259 2 259 20.
  Definition loc_349 : location_info := LocationInfo file_0 260 2 260 40.
  Definition loc_350 : location_info := LocationInfo file_0 260 40 260 3.
  Definition loc_351 : location_info := LocationInfo file_0 261 2 267 3.
  Definition loc_352 : location_info := LocationInfo file_0 270 2 270 31.
  Definition loc_353 : location_info := LocationInfo file_0 271 2 275 3.
  Definition loc_354 : location_info := LocationInfo file_0 277 2 284 3.
  Definition loc_355 : location_info := LocationInfo file_0 286 2 286 14.
  Definition loc_356 : location_info := LocationInfo file_0 286 14 289 22.
  Definition loc_357 : location_info := LocationInfo file_0 289 2 289 22.
  Definition loc_358 : location_info := LocationInfo file_0 291 2 291 13.
  Definition loc_359 : location_info := LocationInfo file_0 291 9 291 12.
  Definition loc_360 : location_info := LocationInfo file_0 291 9 291 12.
  Definition loc_361 : location_info := LocationInfo file_0 289 2 289 11.
  Definition loc_362 : location_info := LocationInfo file_0 289 2 289 11.
  Definition loc_363 : location_info := LocationInfo file_0 289 12 289 20.
  Definition loc_364 : location_info := LocationInfo file_0 289 13 289 20.
  Definition loc_365 : location_info := LocationInfo file_0 289 13 289 14.
  Definition loc_366 : location_info := LocationInfo file_0 289 13 289 14.
  Definition loc_367 : location_info := LocationInfo file_0 286 2 286 5.
  Definition loc_368 : location_info := LocationInfo file_0 286 8 286 13.
  Definition loc_369 : location_info := LocationInfo file_0 286 8 286 13.
  Definition loc_370 : location_info := LocationInfo file_0 277 36 279 3.
  Definition loc_371 : location_info := LocationInfo file_0 278 4 278 45.
  Definition loc_372 : location_info := LocationInfo file_0 278 4 278 24.
  Definition loc_373 : location_info := LocationInfo file_0 278 4 278 13.
  Definition loc_374 : location_info := LocationInfo file_0 278 4 278 5.
  Definition loc_375 : location_info := LocationInfo file_0 278 4 278 5.
  Definition loc_376 : location_info := LocationInfo file_0 278 27 278 44.
  Definition loc_377 : location_info := LocationInfo file_0 278 27 278 44.
  Definition loc_378 : location_info := LocationInfo file_0 278 27 278 32.
  Definition loc_379 : location_info := LocationInfo file_0 278 27 278 32.
  Definition loc_380 : location_info := LocationInfo file_0 279 9 284 3.
  Definition loc_381 : location_info := LocationInfo file_0 280 4 280 79.
  Definition loc_382 : location_info := LocationInfo file_0 281 4 281 46.
  Definition loc_383 : location_info := LocationInfo file_0 282 4 282 50.
  Definition loc_384 : location_info := LocationInfo file_0 283 4 283 37.
  Definition loc_385 : location_info := LocationInfo file_0 283 4 283 24.
  Definition loc_386 : location_info := LocationInfo file_0 283 4 283 13.
  Definition loc_387 : location_info := LocationInfo file_0 283 4 283 5.
  Definition loc_388 : location_info := LocationInfo file_0 283 4 283 5.
  Definition loc_389 : location_info := LocationInfo file_0 283 27 283 36.
  Definition loc_390 : location_info := LocationInfo file_0 283 27 283 36.
  Definition loc_391 : location_info := LocationInfo file_0 282 4 282 19.
  Definition loc_392 : location_info := LocationInfo file_0 282 4 282 13.
  Definition loc_393 : location_info := LocationInfo file_0 282 4 282 13.
  Definition loc_394 : location_info := LocationInfo file_0 282 22 282 49.
  Definition loc_395 : location_info := LocationInfo file_0 282 22 282 33.
  Definition loc_396 : location_info := LocationInfo file_0 282 22 282 33.
  Definition loc_397 : location_info := LocationInfo file_0 282 22 282 27.
  Definition loc_398 : location_info := LocationInfo file_0 282 22 282 27.
  Definition loc_399 : location_info := LocationInfo file_0 282 36 282 49.
  Definition loc_400 : location_info := LocationInfo file_0 282 36 282 49.
  Definition loc_401 : location_info := LocationInfo file_0 282 36 282 37.
  Definition loc_402 : location_info := LocationInfo file_0 282 36 282 37.
  Definition loc_403 : location_info := LocationInfo file_0 281 4 281 25.
  Definition loc_404 : location_info := LocationInfo file_0 281 4 281 13.
  Definition loc_405 : location_info := LocationInfo file_0 281 4 281 13.
  Definition loc_406 : location_info := LocationInfo file_0 281 28 281 45.
  Definition loc_407 : location_info := LocationInfo file_0 281 28 281 45.
  Definition loc_408 : location_info := LocationInfo file_0 281 28 281 33.
  Definition loc_409 : location_info := LocationInfo file_0 281 28 281 33.
  Definition loc_410 : location_info := LocationInfo file_0 280 4 280 13.
  Definition loc_411 : location_info := LocationInfo file_0 280 16 280 78.
  Definition loc_412 : location_info := LocationInfo file_0 280 38 280 78.
  Definition loc_413 : location_info := LocationInfo file_0 280 39 280 61.
  Definition loc_414 : location_info := LocationInfo file_0 280 56 280 61.
  Definition loc_415 : location_info := LocationInfo file_0 280 56 280 61.
  Definition loc_416 : location_info := LocationInfo file_0 280 64 280 77.
  Definition loc_417 : location_info := LocationInfo file_0 280 64 280 77.
  Definition loc_418 : location_info := LocationInfo file_0 280 64 280 65.
  Definition loc_419 : location_info := LocationInfo file_0 280 64 280 65.
  Definition loc_420 : location_info := LocationInfo file_0 277 6 277 34.
  Definition loc_421 : location_info := LocationInfo file_0 277 6 277 19.
  Definition loc_422 : location_info := LocationInfo file_0 277 6 277 19.
  Definition loc_423 : location_info := LocationInfo file_0 277 6 277 7.
  Definition loc_424 : location_info := LocationInfo file_0 277 6 277 7.
  Definition loc_425 : location_info := LocationInfo file_0 277 23 277 34.
  Definition loc_426 : location_info := LocationInfo file_0 277 23 277 34.
  Definition loc_427 : location_info := LocationInfo file_0 277 23 277 28.
  Definition loc_428 : location_info := LocationInfo file_0 277 23 277 28.
  Definition loc_429 : location_info := LocationInfo file_0 271 31 275 3.
  Definition loc_430 : location_info := LocationInfo file_0 273 4 273 25.
  Definition loc_431 : location_info := LocationInfo file_0 274 4 274 14.
  Definition loc_432 : location_info := LocationInfo file_0 273 4 273 7.
  Definition loc_433 : location_info := LocationInfo file_0 273 10 273 24.
  Definition loc_435 : location_info := LocationInfo file_0 271 6 271 29.
  Definition loc_436 : location_info := LocationInfo file_0 271 6 271 11.
  Definition loc_437 : location_info := LocationInfo file_0 271 6 271 11.
  Definition loc_438 : location_info := LocationInfo file_0 271 15 271 29.
  Definition loc_439 : location_info := LocationInfo file_0 270 2 270 7.
  Definition loc_440 : location_info := LocationInfo file_0 270 10 270 30.
  Definition loc_441 : location_info := LocationInfo file_0 270 10 270 30.
  Definition loc_442 : location_info := LocationInfo file_0 270 10 270 19.
  Definition loc_443 : location_info := LocationInfo file_0 270 10 270 11.
  Definition loc_444 : location_info := LocationInfo file_0 270 10 270 11.
  Definition loc_445 : location_info := LocationInfo file_0 261 46 267 3.
  Definition loc_446 : location_info := LocationInfo file_0 262 4 262 53.
  Definition loc_447 : location_info := LocationInfo file_0 264 4 264 39.
  Definition loc_448 : location_info := LocationInfo file_0 265 4 265 16.
  Definition loc_449 : location_info := LocationInfo file_0 266 4 266 14.
  Definition loc_450 : location_info := LocationInfo file_0 265 4 265 7.
  Definition loc_451 : location_info := LocationInfo file_0 265 10 265 15.
  Definition loc_452 : location_info := LocationInfo file_0 265 10 265 15.
  Definition loc_453 : location_info := LocationInfo file_0 264 4 264 24.
  Definition loc_454 : location_info := LocationInfo file_0 264 4 264 13.
  Definition loc_455 : location_info := LocationInfo file_0 264 4 264 5.
  Definition loc_456 : location_info := LocationInfo file_0 264 4 264 5.
  Definition loc_457 : location_info := LocationInfo file_0 264 27 264 38.
  Definition loc_458 : location_info := LocationInfo file_0 264 27 264 38.
  Definition loc_459 : location_info := LocationInfo file_0 264 27 264 32.
  Definition loc_460 : location_info := LocationInfo file_0 264 27 264 32.
  Definition loc_461 : location_info := LocationInfo file_0 262 32 262 52.
  Definition loc_462 : location_info := LocationInfo file_0 262 32 262 52.
  Definition loc_463 : location_info := LocationInfo file_0 262 32 262 41.
  Definition loc_464 : location_info := LocationInfo file_0 262 32 262 33.
  Definition loc_465 : location_info := LocationInfo file_0 262 32 262 33.
  Definition loc_469 : location_info := LocationInfo file_0 261 6 261 44.
  Definition loc_470 : location_info := LocationInfo file_0 261 6 261 26.
  Definition loc_471 : location_info := LocationInfo file_0 261 6 261 26.
  Definition loc_472 : location_info := LocationInfo file_0 261 6 261 15.
  Definition loc_473 : location_info := LocationInfo file_0 261 6 261 7.
  Definition loc_474 : location_info := LocationInfo file_0 261 6 261 7.
  Definition loc_475 : location_info := LocationInfo file_0 261 30 261 44.
  Definition loc_476 : location_info := LocationInfo file_0 260 27 260 39.
  Definition loc_477 : location_info := LocationInfo file_0 260 28 260 39.
  Definition loc_478 : location_info := LocationInfo file_0 260 29 260 30.
  Definition loc_479 : location_info := LocationInfo file_0 260 29 260 30.
  Definition loc_480 : location_info := LocationInfo file_0 259 2 259 9.
  Definition loc_481 : location_info := LocationInfo file_0 259 2 259 9.
  Definition loc_482 : location_info := LocationInfo file_0 259 10 259 18.
  Definition loc_483 : location_info := LocationInfo file_0 259 11 259 18.
  Definition loc_484 : location_info := LocationInfo file_0 259 11 259 12.
  Definition loc_485 : location_info := LocationInfo file_0 259 11 259 12.
  Definition loc_488 : location_info := LocationInfo file_0 304 2 304 41.
  Definition loc_489 : location_info := LocationInfo file_0 305 2 307 3.
  Definition loc_490 : location_info := LocationInfo file_0 308 2 308 18.
  Definition loc_491 : location_info := LocationInfo file_0 312 2 318 3.
  Definition loc_492 : location_info := LocationInfo file_0 320 2 320 24.
  Definition loc_493 : location_info := LocationInfo file_0 320 9 320 23.
  Definition loc_494 : location_info := LocationInfo file_0 312 2 318 3.
  Definition loc_495 : location_info := LocationInfo file_0 312 30 318 3.
  Definition loc_496 : location_info := LocationInfo file_0 313 4 313 37.
  Definition loc_497 : location_info := LocationInfo file_0 314 4 316 5.
  Definition loc_498 : location_info := LocationInfo file_0 317 4 317 20.
  Definition loc_499 : location_info := LocationInfo file_0 312 2 318 3.
  Definition loc_500 : location_info := LocationInfo file_0 312 2 318 3.
  Definition loc_501 : location_info := LocationInfo file_0 317 4 317 5.
  Definition loc_502 : location_info := LocationInfo file_0 317 8 317 19.
  Definition loc_503 : location_info := LocationInfo file_0 317 8 317 19.
  Definition loc_504 : location_info := LocationInfo file_0 317 8 317 9.
  Definition loc_505 : location_info := LocationInfo file_0 317 8 317 9.
  Definition loc_506 : location_info := LocationInfo file_0 314 31 316 5.
  Definition loc_507 : location_info := LocationInfo file_0 315 6 315 17.
  Definition loc_508 : location_info := LocationInfo file_0 315 13 315 16.
  Definition loc_509 : location_info := LocationInfo file_0 315 13 315 16.
  Definition loc_511 : location_info := LocationInfo file_0 314 8 314 29.
  Definition loc_512 : location_info := LocationInfo file_0 314 8 314 11.
  Definition loc_513 : location_info := LocationInfo file_0 314 8 314 11.
  Definition loc_514 : location_info := LocationInfo file_0 314 15 314 29.
  Definition loc_515 : location_info := LocationInfo file_0 313 4 313 7.
  Definition loc_516 : location_info := LocationInfo file_0 313 10 313 36.
  Definition loc_517 : location_info := LocationInfo file_0 313 10 313 33.
  Definition loc_518 : location_info := LocationInfo file_0 313 10 313 33.
  Definition loc_519 : location_info := LocationInfo file_0 313 34 313 35.
  Definition loc_520 : location_info := LocationInfo file_0 313 34 313 35.
  Definition loc_521 : location_info := LocationInfo file_0 312 9 312 28.
  Definition loc_522 : location_info := LocationInfo file_0 312 9 312 10.
  Definition loc_523 : location_info := LocationInfo file_0 312 9 312 10.
  Definition loc_524 : location_info := LocationInfo file_0 312 14 312 28.
  Definition loc_525 : location_info := LocationInfo file_0 308 2 308 3.
  Definition loc_526 : location_info := LocationInfo file_0 308 6 308 17.
  Definition loc_527 : location_info := LocationInfo file_0 308 6 308 17.
  Definition loc_528 : location_info := LocationInfo file_0 308 6 308 7.
  Definition loc_529 : location_info := LocationInfo file_0 308 6 308 7.
  Definition loc_530 : location_info := LocationInfo file_0 305 29 307 3.
  Definition loc_531 : location_info := LocationInfo file_0 306 4 306 15.
  Definition loc_532 : location_info := LocationInfo file_0 306 11 306 14.
  Definition loc_533 : location_info := LocationInfo file_0 306 11 306 14.
  Definition loc_535 : location_info := LocationInfo file_0 305 6 305 27.
  Definition loc_536 : location_info := LocationInfo file_0 305 6 305 9.
  Definition loc_537 : location_info := LocationInfo file_0 305 6 305 9.
  Definition loc_538 : location_info := LocationInfo file_0 305 13 305 27.
  Definition loc_539 : location_info := LocationInfo file_0 304 14 304 40.
  Definition loc_540 : location_info := LocationInfo file_0 304 14 304 37.
  Definition loc_541 : location_info := LocationInfo file_0 304 14 304 37.
  Definition loc_542 : location_info := LocationInfo file_0 304 38 304 39.
  Definition loc_543 : location_info := LocationInfo file_0 304 38 304 39.
  Definition loc_548 : location_info := LocationInfo file_0 361 2 361 29.
  Definition loc_549 : location_info := LocationInfo file_0 363 2 363 25.
  Definition loc_550 : location_info := LocationInfo file_0 365 2 365 20.
  Definition loc_551 : location_info := LocationInfo file_0 366 2 366 40.
  Definition loc_552 : location_info := LocationInfo file_0 366 40 366 3.
  Definition loc_553 : location_info := LocationInfo file_0 372 2 372 31.
  Definition loc_554 : location_info := LocationInfo file_0 382 2 428 3.
  Definition loc_555 : location_info := LocationInfo file_0 429 2 429 11.
  Definition loc_556 : location_info := LocationInfo file_0 429 11 429 3.
  Definition loc_557 : location_info := LocationInfo file_0 431 2 431 22.
  Definition loc_558 : location_info := LocationInfo file_0 433 2 433 13.
  Definition loc_559 : location_info := LocationInfo file_0 433 9 433 12.
  Definition loc_560 : location_info := LocationInfo file_0 433 9 433 12.
  Definition loc_561 : location_info := LocationInfo file_0 431 2 431 11.
  Definition loc_562 : location_info := LocationInfo file_0 431 2 431 11.
  Definition loc_563 : location_info := LocationInfo file_0 431 12 431 20.
  Definition loc_564 : location_info := LocationInfo file_0 431 13 431 20.
  Definition loc_565 : location_info := LocationInfo file_0 431 13 431 14.
  Definition loc_566 : location_info := LocationInfo file_0 431 13 431 14.
  Definition loc_567 : location_info := LocationInfo file_0 429 2 429 10.
  Definition loc_568 : location_info := LocationInfo file_0 429 3 429 10.
  Definition loc_569 : location_info := LocationInfo file_0 429 5 429 9.
  Definition loc_570 : location_info := LocationInfo file_0 429 5 429 9.
  Definition loc_571 : location_info := LocationInfo file_0 382 2 428 3.
  Definition loc_572 : location_info := LocationInfo file_0 382 34 428 3.
  Definition loc_573 : location_info := LocationInfo file_0 385 4 385 38.
  Definition loc_574 : location_info := LocationInfo file_0 389 4 389 67.
  Definition loc_575 : location_info := LocationInfo file_0 396 4 425 5.
  Definition loc_576 : location_info := LocationInfo file_0 427 4 427 30.
  Definition loc_577 : location_info := LocationInfo file_0 382 2 428 3.
  Definition loc_578 : location_info := LocationInfo file_0 382 2 428 3.
  Definition loc_579 : location_info := LocationInfo file_0 427 4 427 8.
  Definition loc_580 : location_info := LocationInfo file_0 427 11 427 29.
  Definition loc_581 : location_info := LocationInfo file_0 427 12 427 29.
  Definition loc_582 : location_info := LocationInfo file_0 427 12 427 17.
  Definition loc_583 : location_info := LocationInfo file_0 427 12 427 17.
  Definition loc_584 : location_info := LocationInfo file_0 396 61 425 5.
  Definition loc_585 : location_info := LocationInfo file_0 397 6 397 38.
  Definition loc_586 : location_info := LocationInfo file_0 398 6 398 57.
  Definition loc_587 : location_info := LocationInfo file_0 399 6 399 42.
  Definition loc_588 : location_info := LocationInfo file_0 399 42 399 7.
  Definition loc_589 : location_info := LocationInfo file_0 400 6 400 52.
  Definition loc_590 : location_info := LocationInfo file_0 402 6 409 7.
  Definition loc_591 : location_info := LocationInfo file_0 415 6 419 7.
  Definition loc_592 : location_info := LocationInfo file_0 421 6 421 16.
  Definition loc_593 : location_info := LocationInfo file_0 421 16 421 7.
  Definition loc_594 : location_info := LocationInfo file_0 422 6 422 55.
  Definition loc_595 : location_info := LocationInfo file_0 422 55 422 7.
  Definition loc_596 : location_info := LocationInfo file_0 423 6 423 26.
  Definition loc_597 : location_info := LocationInfo file_0 424 6 424 12.
  Definition loc_598 : location_info := LocationInfo file_0 423 6 423 9.
  Definition loc_599 : location_info := LocationInfo file_0 423 12 423 25.
  Definition loc_600 : location_info := LocationInfo file_0 423 20 423 25.
  Definition loc_601 : location_info := LocationInfo file_0 423 20 423 25.
  Definition loc_602 : location_info := LocationInfo file_0 422 45 422 54.
  Definition loc_603 : location_info := LocationInfo file_0 422 46 422 54.
  Definition loc_604 : location_info := LocationInfo file_0 422 48 422 53.
  Definition loc_605 : location_info := LocationInfo file_0 422 48 422 53.
  Definition loc_606 : location_info := LocationInfo file_0 421 6 421 15.
  Definition loc_607 : location_info := LocationInfo file_0 421 7 421 15.
  Definition loc_608 : location_info := LocationInfo file_0 421 9 421 14.
  Definition loc_609 : location_info := LocationInfo file_0 421 9 421 14.
  Definition loc_610 : location_info := LocationInfo file_0 415 41 419 7.
  Definition loc_611 : location_info := LocationInfo file_0 416 8 416 34.
  Definition loc_612 : location_info := LocationInfo file_0 417 8 417 22.
  Definition loc_613 : location_info := LocationInfo file_0 418 8 418 35.
  Definition loc_614 : location_info := LocationInfo file_0 418 8 418 19.
  Definition loc_615 : location_info := LocationInfo file_0 418 8 418 13.
  Definition loc_616 : location_info := LocationInfo file_0 418 8 418 13.
  Definition loc_617 : location_info := LocationInfo file_0 418 22 418 34.
  Definition loc_618 : location_info := LocationInfo file_0 418 22 418 34.
  Definition loc_619 : location_info := LocationInfo file_0 417 8 417 13.
  Definition loc_620 : location_info := LocationInfo file_0 417 9 417 13.
  Definition loc_621 : location_info := LocationInfo file_0 417 9 417 13.
  Definition loc_622 : location_info := LocationInfo file_0 417 16 417 21.
  Definition loc_623 : location_info := LocationInfo file_0 417 16 417 21.
  Definition loc_624 : location_info := LocationInfo file_0 416 8 416 25.
  Definition loc_625 : location_info := LocationInfo file_0 416 8 416 13.
  Definition loc_626 : location_info := LocationInfo file_0 416 8 416 13.
  Definition loc_627 : location_info := LocationInfo file_0 416 28 416 33.
  Definition loc_628 : location_info := LocationInfo file_0 416 28 416 33.
  Definition loc_629 : location_info := LocationInfo file_0 416 29 416 33.
  Definition loc_630 : location_info := LocationInfo file_0 416 29 416 33.
  Definition loc_632 : location_info := LocationInfo file_0 415 10 415 39.
  Definition loc_633 : location_info := LocationInfo file_0 415 10 415 22.
  Definition loc_634 : location_info := LocationInfo file_0 415 10 415 22.
  Definition loc_635 : location_info := LocationInfo file_0 415 26 415 39.
  Definition loc_636 : location_info := LocationInfo file_0 415 26 415 39.
  Definition loc_637 : location_info := LocationInfo file_0 415 26 415 27.
  Definition loc_638 : location_info := LocationInfo file_0 415 26 415 27.
  Definition loc_639 : location_info := LocationInfo file_0 402 62 404 7.
  Definition loc_640 : location_info := LocationInfo file_0 403 8 403 27.
  Definition loc_641 : location_info := LocationInfo file_0 403 8 403 13.
  Definition loc_642 : location_info := LocationInfo file_0 403 9 403 13.
  Definition loc_643 : location_info := LocationInfo file_0 403 9 403 13.
  Definition loc_644 : location_info := LocationInfo file_0 403 16 403 26.
  Definition loc_645 : location_info := LocationInfo file_0 403 16 403 26.
  Definition loc_646 : location_info := LocationInfo file_0 404 13 409 7.
  Definition loc_647 : location_info := LocationInfo file_0 405 8 405 76.
  Definition loc_648 : location_info := LocationInfo file_0 406 8 406 78.
  Definition loc_649 : location_info := LocationInfo file_0 407 8 407 43.
  Definition loc_650 : location_info := LocationInfo file_0 408 8 408 26.
  Definition loc_651 : location_info := LocationInfo file_0 408 8 408 13.
  Definition loc_652 : location_info := LocationInfo file_0 408 9 408 13.
  Definition loc_653 : location_info := LocationInfo file_0 408 9 408 13.
  Definition loc_654 : location_info := LocationInfo file_0 408 16 408 25.
  Definition loc_655 : location_info := LocationInfo file_0 408 16 408 25.
  Definition loc_656 : location_info := LocationInfo file_0 407 8 407 29.
  Definition loc_657 : location_info := LocationInfo file_0 407 8 407 17.
  Definition loc_658 : location_info := LocationInfo file_0 407 8 407 17.
  Definition loc_659 : location_info := LocationInfo file_0 407 32 407 42.
  Definition loc_660 : location_info := LocationInfo file_0 407 32 407 42.
  Definition loc_661 : location_info := LocationInfo file_0 406 8 406 23.
  Definition loc_662 : location_info := LocationInfo file_0 406 8 406 17.
  Definition loc_663 : location_info := LocationInfo file_0 406 8 406 17.
  Definition loc_664 : location_info := LocationInfo file_0 406 26 406 77.
  Definition loc_665 : location_info := LocationInfo file_0 406 26 406 36.
  Definition loc_666 : location_info := LocationInfo file_0 406 26 406 36.
  Definition loc_667 : location_info := LocationInfo file_0 406 39 406 77.
  Definition loc_668 : location_info := LocationInfo file_0 406 40 406 52.
  Definition loc_669 : location_info := LocationInfo file_0 406 40 406 52.
  Definition loc_670 : location_info := LocationInfo file_0 406 55 406 76.
  Definition loc_671 : location_info := LocationInfo file_0 406 55 406 60.
  Definition loc_672 : location_info := LocationInfo file_0 406 55 406 60.
  Definition loc_673 : location_info := LocationInfo file_0 406 63 406 76.
  Definition loc_674 : location_info := LocationInfo file_0 406 63 406 76.
  Definition loc_675 : location_info := LocationInfo file_0 406 63 406 64.
  Definition loc_676 : location_info := LocationInfo file_0 406 63 406 64.
  Definition loc_677 : location_info := LocationInfo file_0 405 8 405 17.
  Definition loc_678 : location_info := LocationInfo file_0 405 20 405 75.
  Definition loc_679 : location_info := LocationInfo file_0 405 42 405 75.
  Definition loc_680 : location_info := LocationInfo file_0 405 43 405 48.
  Definition loc_681 : location_info := LocationInfo file_0 405 43 405 48.
  Definition loc_682 : location_info := LocationInfo file_0 405 51 405 74.
  Definition loc_683 : location_info := LocationInfo file_0 405 52 405 57.
  Definition loc_684 : location_info := LocationInfo file_0 405 52 405 57.
  Definition loc_685 : location_info := LocationInfo file_0 405 60 405 73.
  Definition loc_686 : location_info := LocationInfo file_0 405 60 405 73.
  Definition loc_687 : location_info := LocationInfo file_0 405 60 405 61.
  Definition loc_688 : location_info := LocationInfo file_0 405 60 405 61.
  Definition loc_689 : location_info := LocationInfo file_0 402 10 402 60.
  Definition loc_690 : location_info := LocationInfo file_0 402 10 402 46.
  Definition loc_691 : location_info := LocationInfo file_0 402 10 402 22.
  Definition loc_692 : location_info := LocationInfo file_0 402 10 402 22.
  Definition loc_693 : location_info := LocationInfo file_0 402 25 402 46.
  Definition loc_694 : location_info := LocationInfo file_0 402 25 402 30.
  Definition loc_695 : location_info := LocationInfo file_0 402 25 402 30.
  Definition loc_696 : location_info := LocationInfo file_0 402 33 402 46.
  Definition loc_697 : location_info := LocationInfo file_0 402 33 402 46.
  Definition loc_698 : location_info := LocationInfo file_0 402 33 402 34.
  Definition loc_699 : location_info := LocationInfo file_0 402 33 402 34.
  Definition loc_700 : location_info := LocationInfo file_0 402 50 402 60.
  Definition loc_701 : location_info := LocationInfo file_0 402 50 402 60.
  Definition loc_702 : location_info := LocationInfo file_0 400 6 400 11.
  Definition loc_703 : location_info := LocationInfo file_0 400 14 400 51.
  Definition loc_704 : location_info := LocationInfo file_0 400 14 400 36.
  Definition loc_705 : location_info := LocationInfo file_0 400 31 400 36.
  Definition loc_706 : location_info := LocationInfo file_0 400 31 400 36.
  Definition loc_707 : location_info := LocationInfo file_0 400 39 400 51.
  Definition loc_708 : location_info := LocationInfo file_0 400 39 400 51.
  Definition loc_709 : location_info := LocationInfo file_0 399 32 399 41.
  Definition loc_710 : location_info := LocationInfo file_0 399 33 399 41.
  Definition loc_711 : location_info := LocationInfo file_0 399 35 399 40.
  Definition loc_712 : location_info := LocationInfo file_0 399 35 399 40.
  Definition loc_713 : location_info := LocationInfo file_0 398 39 398 56.
  Definition loc_714 : location_info := LocationInfo file_0 398 39 398 56.
  Definition loc_715 : location_info := LocationInfo file_0 398 39 398 44.
  Definition loc_716 : location_info := LocationInfo file_0 398 39 398 44.
  Definition loc_719 : location_info := LocationInfo file_0 397 26 397 37.
  Definition loc_720 : location_info := LocationInfo file_0 397 26 397 37.
  Definition loc_721 : location_info := LocationInfo file_0 397 26 397 31.
  Definition loc_722 : location_info := LocationInfo file_0 397 26 397 31.
  Definition loc_726 : location_info := LocationInfo file_0 396 8 396 59.
  Definition loc_727 : location_info := LocationInfo file_0 396 8 396 44.
  Definition loc_728 : location_info := LocationInfo file_0 396 8 396 20.
  Definition loc_729 : location_info := LocationInfo file_0 396 8 396 20.
  Definition loc_730 : location_info := LocationInfo file_0 396 23 396 44.
  Definition loc_731 : location_info := LocationInfo file_0 396 23 396 28.
  Definition loc_732 : location_info := LocationInfo file_0 396 23 396 28.
  Definition loc_733 : location_info := LocationInfo file_0 396 31 396 44.
  Definition loc_734 : location_info := LocationInfo file_0 396 31 396 44.
  Definition loc_735 : location_info := LocationInfo file_0 396 31 396 32.
  Definition loc_736 : location_info := LocationInfo file_0 396 31 396 32.
  Definition loc_737 : location_info := LocationInfo file_0 396 48 396 59.
  Definition loc_738 : location_info := LocationInfo file_0 396 48 396 59.
  Definition loc_739 : location_info := LocationInfo file_0 396 48 396 53.
  Definition loc_740 : location_info := LocationInfo file_0 396 48 396 53.
  Definition loc_741 : location_info := LocationInfo file_0 389 4 389 20.
  Definition loc_742 : location_info := LocationInfo file_0 389 4 389 20.
  Definition loc_743 : location_info := LocationInfo file_0 389 21 389 43.
  Definition loc_744 : location_info := LocationInfo file_0 389 38 389 43.
  Definition loc_745 : location_info := LocationInfo file_0 389 38 389 43.
  Definition loc_746 : location_info := LocationInfo file_0 389 45 389 50.
  Definition loc_747 : location_info := LocationInfo file_0 389 45 389 50.
  Definition loc_748 : location_info := LocationInfo file_0 389 52 389 65.
  Definition loc_749 : location_info := LocationInfo file_0 389 53 389 65.
  Definition loc_750 : location_info := LocationInfo file_0 385 32 385 37.
  Definition loc_751 : location_info := LocationInfo file_0 385 32 385 37.
  Definition loc_752 : location_info := LocationInfo file_0 385 33 385 37.
  Definition loc_753 : location_info := LocationInfo file_0 385 33 385 37.
  Definition loc_756 : location_info := LocationInfo file_0 382 9 382 32.
  Definition loc_757 : location_info := LocationInfo file_0 382 9 382 14.
  Definition loc_758 : location_info := LocationInfo file_0 382 9 382 14.
  Definition loc_759 : location_info := LocationInfo file_0 382 10 382 14.
  Definition loc_760 : location_info := LocationInfo file_0 382 10 382 14.
  Definition loc_761 : location_info := LocationInfo file_0 382 18 382 32.
  Definition loc_762 : location_info := LocationInfo file_0 372 2 372 6.
  Definition loc_763 : location_info := LocationInfo file_0 372 9 372 30.
  Definition loc_764 : location_info := LocationInfo file_0 372 10 372 30.
  Definition loc_765 : location_info := LocationInfo file_0 372 10 372 19.
  Definition loc_766 : location_info := LocationInfo file_0 372 10 372 11.
  Definition loc_767 : location_info := LocationInfo file_0 372 10 372 11.
  Definition loc_768 : location_info := LocationInfo file_0 366 27 366 39.
  Definition loc_769 : location_info := LocationInfo file_0 366 28 366 39.
  Definition loc_770 : location_info := LocationInfo file_0 366 29 366 30.
  Definition loc_771 : location_info := LocationInfo file_0 366 29 366 30.
  Definition loc_772 : location_info := LocationInfo file_0 365 2 365 9.
  Definition loc_773 : location_info := LocationInfo file_0 365 2 365 9.
  Definition loc_774 : location_info := LocationInfo file_0 365 10 365 18.
  Definition loc_775 : location_info := LocationInfo file_0 365 11 365 18.
  Definition loc_776 : location_info := LocationInfo file_0 365 11 365 12.
  Definition loc_777 : location_info := LocationInfo file_0 365 11 365 12.
  Definition loc_778 : location_info := LocationInfo file_0 363 2 363 7.
  Definition loc_779 : location_info := LocationInfo file_0 363 2 363 24.
  Definition loc_780 : location_info := LocationInfo file_0 363 2 363 7.
  Definition loc_781 : location_info := LocationInfo file_0 363 2 363 7.
  Definition loc_782 : location_info := LocationInfo file_0 363 11 363 24.
  Definition loc_783 : location_info := LocationInfo file_0 363 11 363 24.
  Definition loc_784 : location_info := LocationInfo file_0 363 11 363 12.
  Definition loc_785 : location_info := LocationInfo file_0 363 11 363 12.
  Definition loc_786 : location_info := LocationInfo file_0 361 14 361 28.
  Definition loc_791 : location_info := LocationInfo file_0 456 2 456 66.
  Definition loc_792 : location_info := LocationInfo file_0 458 2 460 3.
  Definition loc_793 : location_info := LocationInfo file_0 462 2 462 18.
  Definition loc_794 : location_info := LocationInfo file_0 466 2 475 3.
  Definition loc_795 : location_info := LocationInfo file_0 477 2 477 24.
  Definition loc_796 : location_info := LocationInfo file_0 477 9 477 23.
  Definition loc_797 : location_info := LocationInfo file_0 466 2 475 3.
  Definition loc_798 : location_info := LocationInfo file_0 466 30 475 3.
  Definition loc_799 : location_info := LocationInfo file_0 467 4 467 62.
  Definition loc_800 : location_info := LocationInfo file_0 469 4 471 5.
  Definition loc_801 : location_info := LocationInfo file_0 473 4 473 20.
  Definition loc_802 : location_info := LocationInfo file_0 466 2 475 3.
  Definition loc_803 : location_info := LocationInfo file_0 466 2 475 3.
  Definition loc_804 : location_info := LocationInfo file_0 473 4 473 5.
  Definition loc_805 : location_info := LocationInfo file_0 473 8 473 19.
  Definition loc_806 : location_info := LocationInfo file_0 473 8 473 19.
  Definition loc_807 : location_info := LocationInfo file_0 473 8 473 9.
  Definition loc_808 : location_info := LocationInfo file_0 473 8 473 9.
  Definition loc_809 : location_info := LocationInfo file_0 469 31 471 5.
  Definition loc_810 : location_info := LocationInfo file_0 470 6 470 17.
  Definition loc_811 : location_info := LocationInfo file_0 470 13 470 16.
  Definition loc_812 : location_info := LocationInfo file_0 470 13 470 16.
  Definition loc_814 : location_info := LocationInfo file_0 469 8 469 29.
  Definition loc_815 : location_info := LocationInfo file_0 469 8 469 11.
  Definition loc_816 : location_info := LocationInfo file_0 469 8 469 11.
  Definition loc_817 : location_info := LocationInfo file_0 469 15 469 29.
  Definition loc_818 : location_info := LocationInfo file_0 467 4 467 7.
  Definition loc_819 : location_info := LocationInfo file_0 467 10 467 61.
  Definition loc_820 : location_info := LocationInfo file_0 467 10 467 44.
  Definition loc_821 : location_info := LocationInfo file_0 467 10 467 44.
  Definition loc_822 : location_info := LocationInfo file_0 467 45 467 46.
  Definition loc_823 : location_info := LocationInfo file_0 467 45 467 46.
  Definition loc_824 : location_info := LocationInfo file_0 467 48 467 53.
  Definition loc_825 : location_info := LocationInfo file_0 467 48 467 53.
  Definition loc_826 : location_info := LocationInfo file_0 467 55 467 60.
  Definition loc_827 : location_info := LocationInfo file_0 467 55 467 60.
  Definition loc_828 : location_info := LocationInfo file_0 466 9 466 28.
  Definition loc_829 : location_info := LocationInfo file_0 466 9 466 10.
  Definition loc_830 : location_info := LocationInfo file_0 466 9 466 10.
  Definition loc_831 : location_info := LocationInfo file_0 466 14 466 28.
  Definition loc_832 : location_info := LocationInfo file_0 462 2 462 3.
  Definition loc_833 : location_info := LocationInfo file_0 462 6 462 17.
  Definition loc_834 : location_info := LocationInfo file_0 462 6 462 17.
  Definition loc_835 : location_info := LocationInfo file_0 462 6 462 7.
  Definition loc_836 : location_info := LocationInfo file_0 462 6 462 7.
  Definition loc_837 : location_info := LocationInfo file_0 458 29 460 3.
  Definition loc_838 : location_info := LocationInfo file_0 459 4 459 15.
  Definition loc_839 : location_info := LocationInfo file_0 459 11 459 14.
  Definition loc_840 : location_info := LocationInfo file_0 459 11 459 14.
  Definition loc_842 : location_info := LocationInfo file_0 458 6 458 27.
  Definition loc_843 : location_info := LocationInfo file_0 458 6 458 9.
  Definition loc_844 : location_info := LocationInfo file_0 458 6 458 9.
  Definition loc_845 : location_info := LocationInfo file_0 458 13 458 27.
  Definition loc_846 : location_info := LocationInfo file_0 456 14 456 65.
  Definition loc_847 : location_info := LocationInfo file_0 456 14 456 48.
  Definition loc_848 : location_info := LocationInfo file_0 456 14 456 48.
  Definition loc_849 : location_info := LocationInfo file_0 456 49 456 50.
  Definition loc_850 : location_info := LocationInfo file_0 456 49 456 50.
  Definition loc_851 : location_info := LocationInfo file_0 456 52 456 57.
  Definition loc_852 : location_info := LocationInfo file_0 456 52 456 57.
  Definition loc_853 : location_info := LocationInfo file_0 456 59 456 64.
  Definition loc_854 : location_info := LocationInfo file_0 456 59 456 64.

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
  Definition impl_mpool_init_from (sl_lock sl_unlock mpool_init : loc): function := {|
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
  Definition impl_mpool_alloc_contiguous_no_fallback (sl_lock sl_unlock round_pointer_up : loc): function := {|
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
