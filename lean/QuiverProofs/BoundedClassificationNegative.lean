import QuiverProofs.BoundedClassificationData
import QuiverProofs.AffineFiveCompletion
import QuiverProofs.AffineFourCompletion
import QuiverProofs.AffineFourOddCompletion
import QuiverProofs.AffineThreeCompletion
import QuiverProofs.AffineTwoCorridor
import QuiverProofs.BaselineNegative
import QuiverProofs.BoundedLStarCompletion
import QuiverProofs.E2Certificate
import QuiverProofs.E3Completion
import QuiverProofs.HereditaryTrianglePendant
import QuiverProofs.HereditaryTriangleRegions00
import QuiverProofs.HereditaryTriangleRegions01
import QuiverProofs.HereditaryTriangleRegions02
import QuiverProofs.HereditaryTriangleRegions03
import QuiverProofs.HereditaryTriangleRegions04
import QuiverProofs.HereditaryTriangleRegions05
import QuiverProofs.HereditaryTriangleRegions06
import QuiverProofs.HereditaryTriangleRegions07
import QuiverProofs.NegativeContinuation
import QuiverProofs.PrintedLStarCompletion
import QuiverProofs.ProperPendantRegions00
import QuiverProofs.ProperPendantRegions01
import QuiverProofs.Q041Corridor
import QuiverProofs.Q184Corridor
import QuiverProofs.Q207Structural
import QuiverProofs.Q426Structural
import QuiverProofs.UnitBoxStructural

namespace QuiverProofs.BoundedClassificationNegative
open BoundedClassificationData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 4096

/-- Exact source q013, census index 13. -/
theorem negative_000 : ¬ MutationAcyclic (negativeRepresentative 0) :=
  QuiverProofs.BoundedLStarCompletion.nma_q013

/-- Exact source q014, census index 14. -/
theorem negative_001 : ¬ MutationAcyclic (negativeRepresentative 1) :=
  QuiverProofs.AffineTwoCorridor.nma_q014

/-- Exact source q017, census index 17. -/
theorem negative_002 : ¬ MutationAcyclic (negativeRepresentative 2) :=
  QuiverProofs.NegativeContinuation.nma_q017

/-- Exact source q023, census index 23. -/
theorem negative_003 : ¬ MutationAcyclic (negativeRepresentative 3) :=
  QuiverProofs.BaselineNegative.nma_q023

/-- Exact source q040, census index 40. -/
theorem negative_004 : ¬ MutationAcyclic (negativeRepresentative 4) :=
  QuiverProofs.BoundedLStarCompletion.nma_q040

/-- Exact source q041, census index 41. -/
theorem negative_005 : ¬ MutationAcyclic (negativeRepresentative 5) :=
  QuiverProofs.Q041Corridor.nma_q041

/-- Exact source q045, census index 45. -/
theorem negative_006 : ¬ MutationAcyclic (negativeRepresentative 6) :=
  QuiverProofs.NegativeContinuation.nma_q045

/-- Exact source q046, census index 46. -/
theorem negative_007 : ¬ MutationAcyclic (negativeRepresentative 7) :=
  QuiverProofs.BoundedLStarCompletion.nma_q046

/-- Exact source q065, census index 65. -/
theorem negative_008 : ¬ MutationAcyclic (negativeRepresentative 8) :=
  QuiverProofs.AffineFiveCompletion.nma_q065

/-- Exact source q066, census index 66. -/
theorem negative_009 : ¬ MutationAcyclic (negativeRepresentative 9) :=
  QuiverProofs.BoundedLStarCompletion.nma_q066

/-- Exact source q070, census index 70. -/
theorem negative_010 : ¬ MutationAcyclic (negativeRepresentative 10) :=
  QuiverProofs.BoundedLStarCompletion.nma_q070

/-- Exact source q071, census index 71. -/
theorem negative_011 : ¬ MutationAcyclic (negativeRepresentative 11) :=
  QuiverProofs.AffineFiveCompletion.nma_q071

/-- Exact source q109, census index 110. -/
theorem negative_012 : ¬ MutationAcyclic (negativeRepresentative 12) :=
  QuiverProofs.NegativeContinuation.nma_q109

/-- Exact source q128, census index 130. -/
theorem negative_013 : ¬ MutationAcyclic (negativeRepresentative 13) :=
  QuiverProofs.AffineFourCompletion.nma_q128

/-- Exact source q133, census index 135. -/
theorem negative_014 : ¬ MutationAcyclic (negativeRepresentative 14) :=
  QuiverProofs.ProperPendantRegions00.nma_q133

/-- Exact source q134, census index 136. -/
theorem negative_015 : ¬ MutationAcyclic (negativeRepresentative 15) :=
  QuiverProofs.AffineFourCompletion.nma_q134

/-- Exact source q155, census index 158. -/
theorem negative_016 : ¬ MutationAcyclic (negativeRepresentative 16) :=
  QuiverProofs.BoundedLStarCompletion.nma_q155

/-- Exact source q156, census index 159. -/
theorem negative_017 : ¬ MutationAcyclic (negativeRepresentative 17) :=
  QuiverProofs.BoundedLStarCompletion.nma_q156

/-- Exact source q160, census index 163. -/
theorem negative_018 : ¬ MutationAcyclic (negativeRepresentative 18) :=
  QuiverProofs.Q041Corridor.nma_q160

/-- Exact source q161, census index 164. -/
theorem negative_019 : ¬ MutationAcyclic (negativeRepresentative 19) :=
  QuiverProofs.AffineTwoCorridor.nma_q161

/-- Exact source q172, census index 175. -/
theorem negative_020 : ¬ MutationAcyclic (negativeRepresentative 20) :=
  QuiverProofs.HereditaryTriangleRegions00.nma_q172

/-- Exact source q179, census index 182. -/
theorem negative_021 : ¬ MutationAcyclic (negativeRepresentative 21) :=
  QuiverProofs.BoundedLStarCompletion.nma_q179

/-- Exact source q180, census index 183. -/
theorem negative_022 : ¬ MutationAcyclic (negativeRepresentative 22) :=
  QuiverProofs.BoundedLStarCompletion.nma_q180

/-- Exact source q184, census index 187. -/
theorem negative_023 : ¬ MutationAcyclic (negativeRepresentative 23) :=
  QuiverProofs.Q184Corridor.nma_q184

/-- Exact source q185, census index 188. -/
theorem negative_024 : ¬ MutationAcyclic (negativeRepresentative 24) :=
  QuiverProofs.AffineFiveCompletion.nma_q185

/-- Exact source q191, census index 194. -/
theorem negative_025 : ¬ MutationAcyclic (negativeRepresentative 25) :=
  QuiverProofs.AffineThreeCompletion.nma_q191

/-- Exact source q196, census index 199. -/
theorem negative_026 : ¬ MutationAcyclic (negativeRepresentative 26) :=
  QuiverProofs.PrintedLStarCompletion.nma_q196

/-- Exact source q197, census index 200. -/
theorem negative_027 : ¬ MutationAcyclic (negativeRepresentative 27) :=
  QuiverProofs.Q184Corridor.nma_q197

/-- Exact source q203, census index 206. -/
theorem negative_028 : ¬ MutationAcyclic (negativeRepresentative 28) :=
  QuiverProofs.ProperPendantRegions01.nma_q203

/-- Exact source q204, census index 207. -/
theorem negative_029 : ¬ MutationAcyclic (negativeRepresentative 29) :=
  QuiverProofs.ProperPendantRegions00.nma_q204

/-- Exact source q207, census index 210. -/
theorem negative_030 : ¬ MutationAcyclic (negativeRepresentative 30) :=
  QuiverProofs.Q207Structural.nma_q207

/-- Exact source q208, census index 211. -/
theorem negative_031 : ¬ MutationAcyclic (negativeRepresentative 31) :=
  QuiverProofs.AffineFourCompletion.nma_q208

/-- Exact source q214, census index 217. -/
theorem negative_032 : ¬ MutationAcyclic (negativeRepresentative 32) :=
  QuiverProofs.NegativeContinuation.nma_q214

/-- Exact source q215, census index 218. -/
theorem negative_033 : ¬ MutationAcyclic (negativeRepresentative 33) :=
  QuiverProofs.HereditaryTriangleRegions00.nma_q215

/-- Exact source q216, census index 219. -/
theorem negative_034 : ¬ MutationAcyclic (negativeRepresentative 34) :=
  QuiverProofs.NegativeContinuation.nma_q216

/-- Exact source q217, census index 220. -/
theorem negative_035 : ¬ MutationAcyclic (negativeRepresentative 35) :=
  QuiverProofs.NegativeContinuation.nma_q217

/-- Exact source q218, census index 221. -/
theorem negative_036 : ¬ MutationAcyclic (negativeRepresentative 36) :=
  QuiverProofs.NegativeContinuation.nma_q218

/-- Exact source q219, census index 222. -/
theorem negative_037 : ¬ MutationAcyclic (negativeRepresentative 37) :=
  QuiverProofs.HereditaryTrianglePendant.nma_q219

/-- Exact source q222, census index 225. -/
theorem negative_038 : ¬ MutationAcyclic (negativeRepresentative 38) :=
  QuiverProofs.BoundedLStarCompletion.nma_q222

/-- Exact source q223, census index 226. -/
theorem negative_039 : ¬ MutationAcyclic (negativeRepresentative 39) :=
  QuiverProofs.NegativeContinuation.nma_q223

/-- Exact source q227, census index 230. -/
theorem negative_040 : ¬ MutationAcyclic (negativeRepresentative 40) :=
  QuiverProofs.HereditaryTrianglePendant.nma_q227

/-- Exact source q231, census index 234. -/
theorem negative_041 : ¬ MutationAcyclic (negativeRepresentative 41) :=
  QuiverProofs.NegativeContinuation.nma_q231

/-- Exact source q232, census index 235. -/
theorem negative_042 : ¬ MutationAcyclic (negativeRepresentative 42) :=
  QuiverProofs.HereditaryTriangleRegions01.nma_q232

/-- Exact source q233, census index 236. -/
theorem negative_043 : ¬ MutationAcyclic (negativeRepresentative 43) :=
  QuiverProofs.HereditaryTriangleRegions00.nma_q233

/-- Exact source q234, census index 237. -/
theorem negative_044 : ¬ MutationAcyclic (negativeRepresentative 44) :=
  QuiverProofs.HereditaryTriangleRegions02.nma_q234

/-- Exact source q235, census index 238. -/
theorem negative_045 : ¬ MutationAcyclic (negativeRepresentative 45) :=
  QuiverProofs.HereditaryTriangleRegions03.nma_q235

/-- Exact source q238, census index 241. -/
theorem negative_046 : ¬ MutationAcyclic (negativeRepresentative 46) :=
  QuiverProofs.AffineFourCompletion.nma_q238

/-- Exact source q239, census index 242. -/
theorem negative_047 : ¬ MutationAcyclic (negativeRepresentative 47) :=
  QuiverProofs.HereditaryTrianglePendant.nma_q239

/-- Exact source q243, census index 246. -/
theorem negative_048 : ¬ MutationAcyclic (negativeRepresentative 48) :=
  QuiverProofs.NegativeContinuation.nma_q243

/-- Exact source q247, census index 250. -/
theorem negative_049 : ¬ MutationAcyclic (negativeRepresentative 49) :=
  QuiverProofs.NegativeContinuation.nma_q247

/-- Exact source q248, census index 251. -/
theorem negative_050 : ¬ MutationAcyclic (negativeRepresentative 50) :=
  QuiverProofs.HereditaryTrianglePendant.nma_q248

/-- Exact source q249, census index 252. -/
theorem negative_051 : ¬ MutationAcyclic (negativeRepresentative 51) :=
  QuiverProofs.NegativeContinuation.nma_q249

/-- Exact source q250, census index 253. -/
theorem negative_052 : ¬ MutationAcyclic (negativeRepresentative 52) :=
  QuiverProofs.HereditaryTriangleRegions00.nma_q250

/-- Exact source q267, census index 270. -/
theorem negative_053 : ¬ MutationAcyclic (negativeRepresentative 53) :=
  QuiverProofs.BoundedLStarCompletion.nma_q267

/-- Exact source q268, census index 271. -/
theorem negative_054 : ¬ MutationAcyclic (negativeRepresentative 54) :=
  QuiverProofs.Q184Corridor.nma_q268

/-- Exact source q272, census index 275. -/
theorem negative_055 : ¬ MutationAcyclic (negativeRepresentative 55) :=
  QuiverProofs.HereditaryTriangleRegions02.nma_q272

/-- Exact source q273, census index 276. -/
theorem negative_056 : ¬ MutationAcyclic (negativeRepresentative 56) :=
  QuiverProofs.AffineFourCompletion.nma_q273

/-- Exact source q284, census index 287. -/
theorem negative_057 : ¬ MutationAcyclic (negativeRepresentative 57) :=
  QuiverProofs.AffineFourOddCompletion.nma_q284

/-- Exact source q285, census index 288. -/
theorem negative_058 : ¬ MutationAcyclic (negativeRepresentative 58) :=
  QuiverProofs.Q207Structural.nma_q285

/-- Exact source q289, census index 292. -/
theorem negative_059 : ¬ MutationAcyclic (negativeRepresentative 59) :=
  QuiverProofs.BoundedLStarCompletion.nma_q289

/-- Exact source q290, census index 293. -/
theorem negative_060 : ¬ MutationAcyclic (negativeRepresentative 60) :=
  QuiverProofs.Q184Corridor.nma_q290

/-- Exact source q328, census index 332. -/
theorem negative_061 : ¬ MutationAcyclic (negativeRepresentative 61) :=
  QuiverProofs.HereditaryTriangleRegions00.nma_q328

/-- Exact source q346, census index 351. -/
theorem negative_062 : ¬ MutationAcyclic (negativeRepresentative 62) :=
  QuiverProofs.AffineThreeCompletion.nma_q346

/-- Exact source q351, census index 356. -/
theorem negative_063 : ¬ MutationAcyclic (negativeRepresentative 63) :=
  QuiverProofs.ProperPendantRegions01.nma_q351

/-- Exact source q352, census index 357. -/
theorem negative_064 : ¬ MutationAcyclic (negativeRepresentative 64) :=
  QuiverProofs.Q207Structural.nma_q352

/-- Exact source q381, census index 387. -/
theorem negative_065 : ¬ MutationAcyclic (negativeRepresentative 65) :=
  QuiverProofs.Q207Structural.nma_q381

/-- Exact source q382, census index 388. -/
theorem negative_066 : ¬ MutationAcyclic (negativeRepresentative 66) :=
  QuiverProofs.ProperPendantRegions01.nma_q382

/-- Exact source q387, census index 393. -/
theorem negative_067 : ¬ MutationAcyclic (negativeRepresentative 67) :=
  QuiverProofs.AffineThreeCompletion.nma_q387

/-- Exact source q403, census index 410. -/
theorem negative_068 : ¬ MutationAcyclic (negativeRepresentative 68) :=
  QuiverProofs.HereditaryTriangleRegions00.nma_q403

/-- Exact source q420, census index 428. -/
theorem negative_069 : ¬ MutationAcyclic (negativeRepresentative 69) :=
  QuiverProofs.Q184Corridor.nma_q420

/-- Exact source q421, census index 429. -/
theorem negative_070 : ¬ MutationAcyclic (negativeRepresentative 70) :=
  QuiverProofs.AffineFiveCompletion.nma_q421

/-- Exact source q426, census index 434. -/
theorem negative_071 : ¬ MutationAcyclic (negativeRepresentative 71) :=
  QuiverProofs.Q426Structural.nma_q426

/-- Exact source q430, census index 438. -/
theorem negative_072 : ¬ MutationAcyclic (negativeRepresentative 72) :=
  QuiverProofs.NegativeContinuation.nma_q430

/-- Exact source q435, census index 443. -/
theorem negative_073 : ¬ MutationAcyclic (negativeRepresentative 73) :=
  QuiverProofs.AffineThreeCompletion.nma_q435

/-- Exact source q436, census index 444. -/
theorem negative_074 : ¬ MutationAcyclic (negativeRepresentative 74) :=
  QuiverProofs.BoundedLStarCompletion.nma_q436

/-- Exact source q440, census index 448. -/
theorem negative_075 : ¬ MutationAcyclic (negativeRepresentative 75) :=
  QuiverProofs.Q207Structural.nma_q440

/-- Exact source q441, census index 449. -/
theorem negative_076 : ¬ MutationAcyclic (negativeRepresentative 76) :=
  QuiverProofs.AffineFourOddCompletion.nma_q441

/-- Exact source q442, census index 450. -/
theorem negative_077 : ¬ MutationAcyclic (negativeRepresentative 77) :=
  QuiverProofs.Q426Structural.nma_q442

/-- Exact source q446, census index 454. -/
theorem negative_078 : ¬ MutationAcyclic (negativeRepresentative 78) :=
  QuiverProofs.E2Certificate.E2_NMA

/-- Exact source q450, census index 458. -/
theorem negative_079 : ¬ MutationAcyclic (negativeRepresentative 79) :=
  QuiverProofs.AffineThreeCompletion.nma_q450

/-- Exact source q455, census index 463. -/
theorem negative_080 : ¬ MutationAcyclic (negativeRepresentative 80) :=
  QuiverProofs.BoundedLStarCompletion.nma_q455

/-- Exact source q456, census index 464. -/
theorem negative_081 : ¬ MutationAcyclic (negativeRepresentative 81) :=
  QuiverProofs.ProperPendantRegions01.nma_q456

/-- Exact source q457, census index 465. -/
theorem negative_082 : ¬ MutationAcyclic (negativeRepresentative 82) :=
  QuiverProofs.Q426Structural.nma_q457

/-- Exact source q460, census index 468. -/
theorem negative_083 : ¬ MutationAcyclic (negativeRepresentative 83) :=
  QuiverProofs.Q426Structural.nma_q460

/-- Exact source q461, census index 469. -/
theorem negative_084 : ¬ MutationAcyclic (negativeRepresentative 84) :=
  QuiverProofs.AffineThreeCompletion.nma_q461

/-- Exact source q462, census index 470. -/
theorem negative_085 : ¬ MutationAcyclic (negativeRepresentative 85) :=
  QuiverProofs.BoundedLStarCompletion.nma_q462

/-- Exact source q466, census index 474. -/
theorem negative_086 : ¬ MutationAcyclic (negativeRepresentative 86) :=
  QuiverProofs.AffineThreeCompletion.nma_q466

/-- Exact source q470, census index 478. -/
theorem negative_087 : ¬ MutationAcyclic (negativeRepresentative 87) :=
  QuiverProofs.AffineFourCompletion.nma_q470

/-- Exact source q475, census index 483. -/
theorem negative_088 : ¬ MutationAcyclic (negativeRepresentative 88) :=
  QuiverProofs.Q426Structural.nma_q475

/-- Exact source q476, census index 484. -/
theorem negative_089 : ¬ MutationAcyclic (negativeRepresentative 89) :=
  QuiverProofs.E3Completion.nma_q476

/-- Exact source q477, census index 485. -/
theorem negative_090 : ¬ MutationAcyclic (negativeRepresentative 90) :=
  QuiverProofs.Q207Structural.nma_q477

/-- Exact source q484, census index 492. -/
theorem negative_091 : ¬ MutationAcyclic (negativeRepresentative 91) :=
  QuiverProofs.Q207Structural.nma_q484

/-- Exact source q487, census index 495. -/
theorem negative_092 : ¬ MutationAcyclic (negativeRepresentative 92) :=
  QuiverProofs.BoundedLStarCompletion.nma_q487

/-- Exact source q490, census index 498. -/
theorem negative_093 : ¬ MutationAcyclic (negativeRepresentative 93) :=
  QuiverProofs.HereditaryTriangleRegions01.nma_q490

/-- Exact source q497, census index 505. -/
theorem negative_094 : ¬ MutationAcyclic (negativeRepresentative 94) :=
  QuiverProofs.BaselineNegative.nma_q497

/-- Exact source q498, census index 506. -/
theorem negative_095 : ¬ MutationAcyclic (negativeRepresentative 95) :=
  QuiverProofs.PrintedLStarCompletion.nma_q498

/-- Exact source q499, census index 507. -/
theorem negative_096 : ¬ MutationAcyclic (negativeRepresentative 96) :=
  QuiverProofs.Q426Structural.nma_q499

/-- Exact source q501, census index 509. -/
theorem negative_097 : ¬ MutationAcyclic (negativeRepresentative 97) :=
  QuiverProofs.HereditaryTriangleRegions04.nma_q501

/-- Exact source q504, census index 512. -/
theorem negative_098 : ¬ MutationAcyclic (negativeRepresentative 98) :=
  QuiverProofs.HereditaryTriangleRegions03.nma_q504

/-- Exact source q505, census index 513. -/
theorem negative_099 : ¬ MutationAcyclic (negativeRepresentative 99) :=
  QuiverProofs.HereditaryTriangleRegions05.nma_q505

/-- Exact source q506, census index 514. -/
theorem negative_100 : ¬ MutationAcyclic (negativeRepresentative 100) :=
  QuiverProofs.HereditaryTriangleRegions01.nma_q506

/-- Exact source q507, census index 515. -/
theorem negative_101 : ¬ MutationAcyclic (negativeRepresentative 101) :=
  QuiverProofs.HereditaryTriangleRegions06.nma_q507

/-- Exact source q508, census index 516. -/
theorem negative_102 : ¬ MutationAcyclic (negativeRepresentative 102) :=
  QuiverProofs.HereditaryTriangleRegions07.nma_q508

/-- Exact source q511, census index 519. -/
theorem negative_103 : ¬ MutationAcyclic (negativeRepresentative 103) :=
  QuiverProofs.BoundedLStarCompletion.nma_q511

/-- Exact source q514, census index 522. -/
theorem negative_104 : ¬ MutationAcyclic (negativeRepresentative 104) :=
  QuiverProofs.HereditaryTrianglePendant.nma_q514

/-- Exact source q515, census index 523. -/
theorem negative_105 : ¬ MutationAcyclic (negativeRepresentative 105) :=
  QuiverProofs.HereditaryTriangleRegions03.nma_q515

/-- Exact source q516, census index 524. -/
theorem negative_106 : ¬ MutationAcyclic (negativeRepresentative 106) :=
  QuiverProofs.HereditaryTrianglePendant.nma_q516

/-- Exact source q517, census index 525. -/
theorem negative_107 : ¬ MutationAcyclic (negativeRepresentative 107) :=
  QuiverProofs.UnitBoxStructural.nma_q517

/-- Exact source q523, census index 531. -/
theorem negative_108 : ¬ MutationAcyclic (negativeRepresentative 108) :=
  QuiverProofs.HereditaryTriangleRegions05.nma_q523

/-- Exact source q524, census index 532. -/
theorem negative_109 : ¬ MutationAcyclic (negativeRepresentative 109) :=
  QuiverProofs.HereditaryTriangleRegions03.nma_q524

/-- Exact source q525, census index 533. -/
theorem negative_110 : ¬ MutationAcyclic (negativeRepresentative 110) :=
  QuiverProofs.Q426Structural.nma_q525

/-- Exact source q527, census index 535. -/
theorem negative_111 : ¬ MutationAcyclic (negativeRepresentative 111) :=
  QuiverProofs.Q207Structural.nma_q527

/-- Exact source q529, census index 537. -/
theorem negative_112 : ¬ MutationAcyclic (negativeRepresentative 112) :=
  QuiverProofs.HereditaryTrianglePendant.nma_q529

/-- Exact source q540, census index 549. -/
theorem negative_113 : ¬ MutationAcyclic (negativeRepresentative 113) :=
  QuiverProofs.NegativeContinuation.nma_q540

/-- Exact source q550, census index 560. -/
theorem negative_114 : ¬ MutationAcyclic (negativeRepresentative 114) :=
  QuiverProofs.BoundedLStarCompletion.nma_q550

/-- Exact source q565, census index 580. -/
theorem negative_115 : ¬ MutationAcyclic (negativeRepresentative 115) :=
  QuiverProofs.HereditaryTrianglePendant.nma_q565

/-- Exact source q569, census index 584. -/
theorem negative_116 : ¬ MutationAcyclic (negativeRepresentative 116) :=
  QuiverProofs.BoundedLStarCompletion.nma_q569

/-- Exact source q573, census index 588. -/
theorem negative_117 : ¬ MutationAcyclic (negativeRepresentative 117) :=
  QuiverProofs.Q426Structural.nma_q573

/-- Exact source q576, census index 591. -/
theorem negative_118 : ¬ MutationAcyclic (negativeRepresentative 118) :=
  QuiverProofs.Q426Structural.nma_q576

/-- Exact source q577, census index 592. -/
theorem negative_119 : ¬ MutationAcyclic (negativeRepresentative 119) :=
  QuiverProofs.UnitBoxStructural.nma_q577

/-- Exact source q595, census index 614. -/
theorem negative_120 : ¬ MutationAcyclic (negativeRepresentative 120) :=
  QuiverProofs.Q426Structural.nma_q595

/-- Exact source q608, census index 627. -/
theorem negative_121 : ¬ MutationAcyclic (negativeRepresentative 121) :=
  QuiverProofs.BaselineNegative.nma_q608

/-- Exact source q609, census index 628. -/
theorem negative_122 : ¬ MutationAcyclic (negativeRepresentative 122) :=
  QuiverProofs.HereditaryTriangleRegions03.nma_q609

/-- Exact source q610, census index 629. -/
theorem negative_123 : ¬ MutationAcyclic (negativeRepresentative 123) :=
  QuiverProofs.HereditaryTrianglePendant.nma_q610

/-- Exact source qd019, census index 630. -/
theorem negative_124 : ¬ MutationAcyclic (negativeRepresentative 124) :=
  QuiverProofs.BaselineNegative.nma_qd019

/-- Exact source q612, census index 632. -/
theorem negative_125 : ¬ MutationAcyclic (negativeRepresentative 125) :=
  QuiverProofs.HereditaryTriangleRegions01.nma_q612

/-- Exact source q613, census index 633. -/
theorem negative_126 : ¬ MutationAcyclic (negativeRepresentative 126) :=
  QuiverProofs.BoundedLStarCompletion.nma_q613

/-- Exact source q616, census index 636. -/
theorem negative_127 : ¬ MutationAcyclic (negativeRepresentative 127) :=
  QuiverProofs.AffineThreeCompletion.nma_q616

/-- Exact source q617, census index 637. -/
theorem negative_128 : ¬ MutationAcyclic (negativeRepresentative 128) :=
  QuiverProofs.BaselineNegative.nma_q617

/-- Exact source q621, census index 641. -/
theorem negative_129 : ¬ MutationAcyclic (negativeRepresentative 129) :=
  QuiverProofs.Q426Structural.nma_q621

/-- Exact source q624, census index 644. -/
theorem negative_130 : ¬ MutationAcyclic (negativeRepresentative 130) :=
  QuiverProofs.Q207Structural.nma_q624

/-- Exact source q632, census index 652. -/
theorem negative_131 : ¬ MutationAcyclic (negativeRepresentative 131) :=
  QuiverProofs.HereditaryTriangleRegions06.nma_q632

/-- Exact source q638, census index 658. -/
theorem negative_132 : ¬ MutationAcyclic (negativeRepresentative 132) :=
  QuiverProofs.Q426Structural.nma_q638

/-- Exact source q655, census index 677. -/
theorem negative_133 : ¬ MutationAcyclic (negativeRepresentative 133) :=
  QuiverProofs.Q426Structural.nma_q655

theorem all_negative (i : Fin 134) : ¬ MutationAcyclic (negativeRepresentative i) := by
  have hi : ∀ i : Fin 134, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63 ∨ i = 64 ∨ i = 65 ∨ i = 66 ∨ i = 67 ∨ i = 68 ∨ i = 69 ∨ i = 70 ∨ i = 71 ∨ i = 72 ∨ i = 73 ∨ i = 74 ∨ i = 75 ∨ i = 76 ∨ i = 77 ∨ i = 78 ∨ i = 79 ∨ i = 80 ∨ i = 81 ∨ i = 82 ∨ i = 83 ∨ i = 84 ∨ i = 85 ∨ i = 86 ∨ i = 87 ∨ i = 88 ∨ i = 89 ∨ i = 90 ∨ i = 91 ∨ i = 92 ∨ i = 93 ∨ i = 94 ∨ i = 95 ∨ i = 96 ∨ i = 97 ∨ i = 98 ∨ i = 99 ∨ i = 100 ∨ i = 101 ∨ i = 102 ∨ i = 103 ∨ i = 104 ∨ i = 105 ∨ i = 106 ∨ i = 107 ∨ i = 108 ∨ i = 109 ∨ i = 110 ∨ i = 111 ∨ i = 112 ∨ i = 113 ∨ i = 114 ∨ i = 115 ∨ i = 116 ∨ i = 117 ∨ i = 118 ∨ i = 119 ∨ i = 120 ∨ i = 121 ∨ i = 122 ∨ i = 123 ∨ i = 124 ∨ i = 125 ∨ i = 126 ∨ i = 127 ∨ i = 128 ∨ i = 129 ∨ i = 130 ∨ i = 131 ∨ i = 132 ∨ i = 133 := by decide +kernel
  rcases hi i with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst i
  · exact negative_000
  · exact negative_001
  · exact negative_002
  · exact negative_003
  · exact negative_004
  · exact negative_005
  · exact negative_006
  · exact negative_007
  · exact negative_008
  · exact negative_009
  · exact negative_010
  · exact negative_011
  · exact negative_012
  · exact negative_013
  · exact negative_014
  · exact negative_015
  · exact negative_016
  · exact negative_017
  · exact negative_018
  · exact negative_019
  · exact negative_020
  · exact negative_021
  · exact negative_022
  · exact negative_023
  · exact negative_024
  · exact negative_025
  · exact negative_026
  · exact negative_027
  · exact negative_028
  · exact negative_029
  · exact negative_030
  · exact negative_031
  · exact negative_032
  · exact negative_033
  · exact negative_034
  · exact negative_035
  · exact negative_036
  · exact negative_037
  · exact negative_038
  · exact negative_039
  · exact negative_040
  · exact negative_041
  · exact negative_042
  · exact negative_043
  · exact negative_044
  · exact negative_045
  · exact negative_046
  · exact negative_047
  · exact negative_048
  · exact negative_049
  · exact negative_050
  · exact negative_051
  · exact negative_052
  · exact negative_053
  · exact negative_054
  · exact negative_055
  · exact negative_056
  · exact negative_057
  · exact negative_058
  · exact negative_059
  · exact negative_060
  · exact negative_061
  · exact negative_062
  · exact negative_063
  · exact negative_064
  · exact negative_065
  · exact negative_066
  · exact negative_067
  · exact negative_068
  · exact negative_069
  · exact negative_070
  · exact negative_071
  · exact negative_072
  · exact negative_073
  · exact negative_074
  · exact negative_075
  · exact negative_076
  · exact negative_077
  · exact negative_078
  · exact negative_079
  · exact negative_080
  · exact negative_081
  · exact negative_082
  · exact negative_083
  · exact negative_084
  · exact negative_085
  · exact negative_086
  · exact negative_087
  · exact negative_088
  · exact negative_089
  · exact negative_090
  · exact negative_091
  · exact negative_092
  · exact negative_093
  · exact negative_094
  · exact negative_095
  · exact negative_096
  · exact negative_097
  · exact negative_098
  · exact negative_099
  · exact negative_100
  · exact negative_101
  · exact negative_102
  · exact negative_103
  · exact negative_104
  · exact negative_105
  · exact negative_106
  · exact negative_107
  · exact negative_108
  · exact negative_109
  · exact negative_110
  · exact negative_111
  · exact negative_112
  · exact negative_113
  · exact negative_114
  · exact negative_115
  · exact negative_116
  · exact negative_117
  · exact negative_118
  · exact negative_119
  · exact negative_120
  · exact negative_121
  · exact negative_122
  · exact negative_123
  · exact negative_124
  · exact negative_125
  · exact negative_126
  · exact negative_127
  · exact negative_128
  · exact negative_129
  · exact negative_130
  · exact negative_131
  · exact negative_132
  · exact negative_133

end QuiverProofs.BoundedClassificationNegative
