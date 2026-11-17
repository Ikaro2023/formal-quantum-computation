/-
Copyright 2026 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Pure-Integer Certificate Checkers & Real-Analytic Soundness for Coherent Peer Fusion
Self-contained real-analytic and integer certificate infrastructure for coherent peer fusion
(`PipelinedFuse`), importing only Mathlib's `ArctanDeriv`.
Padé `[5/4]` upper bound, `invSqrtLo` / `sqrtMUpNat` integer tables, and `clickRow_sound`
- Octant-folded `[5/4]` + `[5/6]` Padé bounds on `Real.arctan (tNum / 100000)` (`tNum ≤
100000`),
- Exact rational square identity `tan²(arcsin(√((r - 1)/r) * sin(arctan t)))` for coherent
peer
  fusion (`slotFuseUnitary`),
- `[5/4]` Padé drift bound on `tan(φ_{r-1} - γ_r)`.
-/
@[expose] public section
namespace QuantumComputation.Specs.GroverFindAll.PipeFuseCert
open Real
/-- Certified integer parameters for one coherent-fusion stage `r`. -/
structure FuseStageRow where
  /-- Scaled cumulative potential `V_r * 10^12 / √N`. -/
  v : ℕ
  /-- Scaled tangent `t_r * 10^5` (`phiFn r = arctan (tNum / 100000)`). -/
  tNum : ℕ
  /-- Certified upper bound `phiHi / 10^12 ≥ arctan (tNum / 100000)`. -/
  phiHi : ℕ
  /-- Certified lower bound `tBfLo / 10^12 ≤ tan (arcsin (√((r - 1)/r) * sin φ_r))`. -/
  tBfLo : ℕ
  /-- Certified upper bound `tanDiffHi / 10^8 ≥ tan (φ_{r-1} - γ_r)` when `φ_{r-1} > γ_r`. -/
  tanDiffHi : ℕ
  /-- Certified drift numerator `numU / 10^12 ≥ max 0 (φ_{r-1} - γ_r)`. -/
  numU : ℕ
  /-- Certified click-term numerator `stepNum`. -/
  stepNum : ℕ
  /-- Certified reset-slot step bound `cNat`. -/
  cNat : ℕ
  /-- Certified unclicked-slot drift step bound `uNat`. -/
  uNat : ℕ
/-- WHNF-forcing wrapper preventing call-by-name thunk duplication in `decide +kernel`. -/
def withForcedNat {α : Type*} (x : ℕ) (k : ℕ → α) : α :=
  Nat.casesOn x (k 0) (fun n ↦ k (Nat.succ n))
theorem withForcedNat_eq {α : Type*} (x : ℕ) (k : ℕ → α) : withForcedNat x k = k x := by
  cases x <;> rfl
/-- Linear conjunction `p 0 &&... && p (cnt - 1)` for `decide +kernel`. -/
def allRange (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | cnt + 1 => allRange p cnt && p cnt
theorem of_allRange {p : ℕ → Bool} : ∀ {cnt i : ℕ}, allRange p cnt = true → i < cnt → p i = true
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | cnt + 1, i, h, hi => by
    simp only [allRange, Bool.and_eq_true] at h; rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
    · exact of_allRange h.1 hlt
    · exact h.2
/-- WHNF-forced prefix sum `∑ r ∈ Finset.Icc 1 cnt, f r`. -/
def sumIccOne (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | cnt + 1 => withForcedNat (sumIccOne f cnt) fun acc ↦ acc + f (cnt + 1)
/-- Chunk 0 (`1..64`) of `invSqrtLo`. -/
def invSqrtLoChunk0 (r : ℕ) : ℕ :=
  cond (Nat.blt r 33) (cond (Nat.blt r 17) (cond (Nat.blt r 9) (cond (Nat.blt r 5) (cond (Nat.blt r
  3) (cond (Nat.blt r 2) 1000000000000 707106781186) (cond (Nat.blt r 4) 577350269189
  500000000000)) (cond (Nat.blt r 7) (cond (Nat.blt r 6) 447213595499 408248290463) (cond (Nat.blt
  r 8) 377964473009 353553390593))) (cond (Nat.blt r 13) (cond (Nat.blt r 11) (cond (Nat.blt r 10)
  333333333333 316227766016) (cond (Nat.blt r 12) 301511344577 288675134594)) (cond (Nat.blt r 15)
  (cond (Nat.blt r 14) 277350098112 267261241912) (cond (Nat.blt r 16) 258198889747
  250000000000)))) (cond (Nat.blt r 25) (cond (Nat.blt r 21) (cond (Nat.blt r 19) (cond (Nat.blt r
  18) 242535625036 235702260395) (cond (Nat.blt r 20) 229415733870 223606797749)) (cond (Nat.blt r
  23) (cond (Nat.blt r 22) 218217890235 213200716355) (cond (Nat.blt r 24) 208514414057
  204124145231))) (cond (Nat.blt r 29) (cond (Nat.blt r 27) (cond (Nat.blt r 26) 200000000000
  196116135138) (cond (Nat.blt r 28) 192450089729 188982236504)) (cond (Nat.blt r 31) (cond
  (Nat.blt r 30) 185695338177 182574185835) (cond (Nat.blt r 32) 179605302026 176776695296)))))
  (cond (Nat.blt r 49) (cond (Nat.blt r 41) (cond (Nat.blt r 37) (cond (Nat.blt r 35) (cond
  (Nat.blt r 34) 174077655955 171498585142) (cond (Nat.blt r 36) 169030850945 166666666666)) (cond
  (Nat.blt r 39) (cond (Nat.blt r 38) 164398987305 162221421130) (cond (Nat.blt r 40) 160128153805
  158113883008))) (cond (Nat.blt r 45) (cond (Nat.blt r 43) (cond (Nat.blt r 42) 156173761888
  154303349962) (cond (Nat.blt r 44) 152498570332 150755672288)) (cond (Nat.blt r 47) (cond
  (Nat.blt r 46) 149071198499 147441956154) (cond (Nat.blt r 48) 145864991497 144337567297))))
  (cond (Nat.blt r 57) (cond (Nat.blt r 53) (cond (Nat.blt r 51) (cond (Nat.blt r 50) 142857142857
  141421356237) (cond (Nat.blt r 52) 140028008402 138675049056)) (cond (Nat.blt r 55) (cond
  (Nat.blt r 54) 137360563948 136082763487) (cond (Nat.blt r 56) 134839972492 133630620956))) (cond
  (Nat.blt r 61) (cond (Nat.blt r 59) (cond (Nat.blt r 58) 132453235706 131306432859) (cond
  (Nat.blt r 60) 130188910980 129099444873)) (cond (Nat.blt r 63) (cond (Nat.blt r 62) 128036879932
  127000127000) (cond (Nat.blt r 64) 125988157669 125000000000)))))
/-- Chunk 1 (`65..128`) of `invSqrtLo`. -/
def invSqrtLoChunk1 (r : ℕ) : ℕ :=
  cond (Nat.blt r 97) (cond (Nat.blt r 81) (cond (Nat.blt r 73) (cond (Nat.blt r 69) (cond (Nat.blt
  r 67) (cond (Nat.blt r 66) 124034734589 123091490979) (cond (Nat.blt r 68) 122169444356
  121267812518)) (cond (Nat.blt r 71) (cond (Nat.blt r 70) 120385853085 119522860933) (cond
  (Nat.blt r 72) 118678165819 117851130197))) (cond (Nat.blt r 77) (cond (Nat.blt r 75) (cond
  (Nat.blt r 74) 117041147196 116247638743) (cond (Nat.blt r 76) 115470053837 114707866935)) (cond
  (Nat.blt r 79) (cond (Nat.blt r 78) 113960576459 113227703414) (cond (Nat.blt r 80) 112508790092
  111803398874)))) (cond (Nat.blt r 89) (cond (Nat.blt r 85) (cond (Nat.blt r 83) (cond (Nat.blt r
  82) 111111111111 110431526074) (cond (Nat.blt r 84) 109764259989 109108945117)) (cond (Nat.blt r
  87) (cond (Nat.blt r 86) 108465228909 107832773203) (cond (Nat.blt r 88) 107211253483
  106600358177))) (cond (Nat.blt r 93) (cond (Nat.blt r 91) (cond (Nat.blt r 90) 105999788000
  105409255338) (cond (Nat.blt r 92) 104828483672 104257207028)) (cond (Nat.blt r 95) (cond
  (Nat.blt r 94) 103695169473 103142124625) (cond (Nat.blt r 96) 102597835208 102062072615)))))
  (cond (Nat.blt r 113) (cond (Nat.blt r 105) (cond (Nat.blt r 101) (cond (Nat.blt r 99) (cond
  (Nat.blt r 98) 101534616513 101015254455) (cond (Nat.blt r 100) 100503781525 100000000000)) (cond
  (Nat.blt r 103) (cond (Nat.blt r 102) 99503719020 99014754297) (cond (Nat.blt r 104) 98532927816
  98058067569))) (cond (Nat.blt r 109) (cond (Nat.blt r 107) (cond (Nat.blt r 106) 97590007294
  97128586235) (cond (Nat.blt r 108) 96673648904 96225044864)) (cond (Nat.blt r 111) (cond (Nat.blt
  r 110) 95782628522 95346258924) (cond (Nat.blt r 112) 94915799575 94491118252)))) (cond (Nat.blt
  r 121) (cond (Nat.blt r 117) (cond (Nat.blt r 115) (cond (Nat.blt r 114) 94072086838 93658581158)
  (cond (Nat.blt r 116) 93250480824 92847669088)) (cond (Nat.blt r 119) (cond (Nat.blt r 118)
  92450032704 92057461789) (cond (Nat.blt r 120) 91669849702 91287092917))) (cond (Nat.blt r 125)
  (cond (Nat.blt r 123) (cond (Nat.blt r 122) 90909090909 90535746042) (cond (Nat.blt r 124)
  90166963466 89802651013)) (cond (Nat.blt r 127) (cond (Nat.blt r 126) 89442719099 89087080637)
  (cond (Nat.blt r 128) 88735650941 88388347648)))))
/-- Chunk 2 (`129..192`) of `invSqrtLo`. -/
def invSqrtLoChunk2 (r : ℕ) : ℕ :=
  cond (Nat.blt r 161) (cond (Nat.blt r 145) (cond (Nat.blt r 137) (cond (Nat.blt r 133) (cond
  (Nat.blt r 131) (cond (Nat.blt r 130) 88045090632 87705801930) (cond (Nat.blt r 132) 87370405666
  87038827977)) (cond (Nat.blt r 135) (cond (Nat.blt r 134) 86710996952 86386842558) (cond (Nat.blt
  r 136) 86066296582 85749292571))) (cond (Nat.blt r 141) (cond (Nat.blt r 139) (cond (Nat.blt r
  138) 85435765771 85125653075) (cond (Nat.blt r 140) 84818892967 84515425472)) (cond (Nat.blt r
  143) (cond (Nat.blt r 142) 84215192106 83918135829) (cond (Nat.blt r 144) 83624201000
  83333333333)))) (cond (Nat.blt r 153) (cond (Nat.blt r 149) (cond (Nat.blt r 147) (cond (Nat.blt
  r 146) 83045479853 82760588860) (cond (Nat.blt r 148) 82478609884 82199493652)) (cond (Nat.blt r
  151) (cond (Nat.blt r 150) 81923192051 81649658092) (cond (Nat.blt r 152) 81378845877
  81110710565))) (cond (Nat.blt r 157) (cond (Nat.blt r 155) (cond (Nat.blt r 154) 80845208345
  80582296402) (cond (Nat.blt r 156) 80321932890 80064076902)) (cond (Nat.blt r 159) (cond (Nat.blt
  r 158) 79808688446 79555728417) (cond (Nat.blt r 160) 79305158571 79056941504))))) (cond (Nat.blt
  r 177) (cond (Nat.blt r 169) (cond (Nat.blt r 165) (cond (Nat.blt r 163) (cond (Nat.blt r 162)
  78811040623 78567420131) (cond (Nat.blt r 164) 78326044998 78086880944)) (cond (Nat.blt r 167)
  (cond (Nat.blt r 166) 77849894416 77615052570) (cond (Nat.blt r 168) 77382323253 77151674981)))
  (cond (Nat.blt r 173) (cond (Nat.blt r 171) (cond (Nat.blt r 170) 76923076923 76696498884) (cond
  (Nat.blt r 172) 76471911290 76249285166)) (cond (Nat.blt r 175) (cond (Nat.blt r 174) 76028592126
  75809804357) (cond (Nat.blt r 176) 75592894601 75377836144)))) (cond (Nat.blt r 185) (cond
  (Nat.blt r 181) (cond (Nat.blt r 179) (cond (Nat.blt r 178) 75164602800 74953168899) (cond
  (Nat.blt r 180) 74743509275 74535599249)) (cond (Nat.blt r 183) (cond (Nat.blt r 182) 74329414624
  74124931666) (cond (Nat.blt r 184) 73922127095 73720978077))) (cond (Nat.blt r 189) (cond
  (Nat.blt r 187) (cond (Nat.blt r 186) 73521462209 73323557510) (cond (Nat.blt r 188) 73127242412
  72932495748)) (cond (Nat.blt r 191) (cond (Nat.blt r 190) 72739296745 72547625011) (cond (Nat.blt
  r 192) 72357460529 72168783648)))))
/-- Chunk 3 (`193..256`) of `invSqrtLo`. -/
def invSqrtLoChunk3 (r : ℕ) : ℕ :=
  cond (Nat.blt r 225) (cond (Nat.blt r 209) (cond (Nat.blt r 201) (cond (Nat.blt r 197) (cond
  (Nat.blt r 195) (cond (Nat.blt r 194) 71981575074 71795815861) (cond (Nat.blt r 196) 71611487403
  71428571428)) (cond (Nat.blt r 199) (cond (Nat.blt r 198) 71247049987 71066905451) (cond (Nat.blt
  r 200) 70888120500 70710678118))) (cond (Nat.blt r 205) (cond (Nat.blt r 203) (cond (Nat.blt r
  202) 70534561585 70359754473) (cond (Nat.blt r 204) 70186240634 70014004201)) (cond (Nat.blt r
  207) (cond (Nat.blt r 206) 69843029576 69673301429) (cond (Nat.blt r 208) 69504804685
  69337524528)))) (cond (Nat.blt r 217) (cond (Nat.blt r 213) (cond (Nat.blt r 211) (cond (Nat.blt
  r 210) 69171446386 69006555934) (cond (Nat.blt r 212) 68842839082 68680281974)) (cond (Nat.blt r
  215) (cond (Nat.blt r 214) 68518870982 68358592702) (cond (Nat.blt r 216) 68199433947
  68041381743))) (cond (Nat.blt r 221) (cond (Nat.blt r 219) (cond (Nat.blt r 218) 67884423330
  67728546147) (cond (Nat.blt r 220) 67573737839 67419986246)) (cond (Nat.blt r 223) (cond (Nat.blt
  r 222) 67267279399 67115605521) (cond (Nat.blt r 224) 66964953018 66815310478))))) (cond (Nat.blt
  r 241) (cond (Nat.blt r 233) (cond (Nat.blt r 229) (cond (Nat.blt r 227) (cond (Nat.blt r 226)
  66666666666 66519010523) (cond (Nat.blt r 228) 66372331159 66226617853)) (cond (Nat.blt r 231)
  (cond (Nat.blt r 230) 66081860045 65938047339) (cond (Nat.blt r 232) 65795169495 65653216429)))
  (cond (Nat.blt r 237) (cond (Nat.blt r 235) (cond (Nat.blt r 234) 65512178208 65372045046) (cond
  (Nat.blt r 236) 65232807305 65094455490)) (cond (Nat.blt r 239) (cond (Nat.blt r 238) 64956980246
  64820372355) (cond (Nat.blt r 240) 64684622735 64549722436)))) (cond (Nat.blt r 249) (cond
  (Nat.blt r 245) (cond (Nat.blt r 243) (cond (Nat.blt r 242) 64415662640 64282434653) (cond
  (Nat.blt r 244) 64150029909 64018439966)) (cond (Nat.blt r 247) (cond (Nat.blt r 246) 63887656499
  63757671306) (cond (Nat.blt r 248) 63628476297 63500063500))) (cond (Nat.blt r 253) (cond
  (Nat.blt r 251) (cond (Nat.blt r 250) 63372425052 63245553203) (cond (Nat.blt r 252) 63119440309
  62994078834)) (cond (Nat.blt r 255) (cond (Nat.blt r 254) 62869461346 62745580513) (cond (Nat.blt
  r 256) 62622429108 62500000000)))))
/-- Chunk 4 (`257..320`) of `invSqrtLo`. -/
def invSqrtLoChunk4 (r : ℕ) : ℕ :=
  cond (Nat.blt r 289) (cond (Nat.blt r 273) (cond (Nat.blt r 265) (cond (Nat.blt r 261) (cond
  (Nat.blt r 259) (cond (Nat.blt r 258) 62378286155 62257280636) (cond (Nat.blt r 260) 62136976600
  62017367294)) (cond (Nat.blt r 263) (cond (Nat.blt r 262) 61898446059 61780206321) (cond (Nat.blt
  r 264) 61662641597 61545745489))) (cond (Nat.blt r 269) (cond (Nat.blt r 267) (cond (Nat.blt r
  266) 61429511683 61313933948) (cond (Nat.blt r 268) 61199006136 61084722178)) (cond (Nat.blt r
  271) (cond (Nat.blt r 270) 60971076084 60858061945) (cond (Nat.blt r 272) 60745673923
  60633906259)))) (cond (Nat.blt r 281) (cond (Nat.blt r 277) (cond (Nat.blt r 275) (cond (Nat.blt
  r 274) 60522753266 60412209333) (cond (Nat.blt r 276) 60302268915 60192926542)) (cond (Nat.blt r
  279) (cond (Nat.blt r 278) 60084176812 59976014390) (cond (Nat.blt r 280) 59868434008
  59761430466))) (cond (Nat.blt r 285) (cond (Nat.blt r 283) (cond (Nat.blt r 282) 59654998627
  59549133417) (cond (Nat.blt r 284) 59443829827 59339082909)) (cond (Nat.blt r 287) (cond (Nat.blt
  r 286) 59234887775 59131239598) (cond (Nat.blt r 288) 59028133610 58925565098))))) (cond (Nat.blt
  r 305) (cond (Nat.blt r 297) (cond (Nat.blt r 293) (cond (Nat.blt r 291) (cond (Nat.blt r 290)
  58823529411 58722021951) (cond (Nat.blt r 292) 58621038176 58520573598)) (cond (Nat.blt r 295)
  (cond (Nat.blt r 294) 58420623783 58321184351) (cond (Nat.blt r 296) 58222250973 58123819371)))
  (cond (Nat.blt r 301) (cond (Nat.blt r 299) (cond (Nat.blt r 298) 58025885318 57928444636) (cond
  (Nat.blt r 300) 57831493196 57735026918)) (cond (Nat.blt r 303) (cond (Nat.blt r 302) 57639041770
  57543533764) (cond (Nat.blt r 304) 57448498962 57353933467)))) (cond (Nat.blt r 313) (cond
  (Nat.blt r 309) (cond (Nat.blt r 307) (cond (Nat.blt r 306) 57259833431 57166195047) (cond
  (Nat.blt r 308) 57073014553 56980288229)) (cond (Nat.blt r 311) (cond (Nat.blt r 310) 56888012398
  56796183424) (cond (Nat.blt r 312) 56704797712 56613851707))) (cond (Nat.blt r 317) (cond
  (Nat.blt r 315) (cond (Nat.blt r 314) 56523341894 56433264798) (cond (Nat.blt r 316) 56343616981
  56254395046)) (cond (Nat.blt r 319) (cond (Nat.blt r 318) 56165595630 56077215409) (cond (Nat.blt
  r 320) 55989251095 55901699437)))))
/-- Chunk 5 (`321..384`) of `invSqrtLo`. -/
def invSqrtLoChunk5 (r : ℕ) : ℕ :=
  cond (Nat.blt r 353) (cond (Nat.blt r 337) (cond (Nat.blt r 329) (cond (Nat.blt r 325) (cond
  (Nat.blt r 323) (cond (Nat.blt r 322) 55814557218 55727821257) (cond (Nat.blt r 324) 55641488407
  55555555555)) (cond (Nat.blt r 327) (cond (Nat.blt r 326) 55470019622 55384877562) (cond (Nat.blt
  r 328) 55300126360 55215763037))) (cond (Nat.blt r 333) (cond (Nat.blt r 331) (cond (Nat.blt r
  330) 55131784641 55048188256) (cond (Nat.blt r 332) 54964970992 54882129994)) (cond (Nat.blt r
  335) (cond (Nat.blt r 334) 54799662435 54717565516) (cond (Nat.blt r 336) 54635836470
  54554472558)))) (cond (Nat.blt r 345) (cond (Nat.blt r 341) (cond (Nat.blt r 339) (cond (Nat.blt
  r 338) 54473471070 54392829322) (cond (Nat.blt r 340) 54312544659 54232614454)) (cond (Nat.blt r
  343) (cond (Nat.blt r 342) 54153036107 54073807043) (cond (Nat.blt r 344) 53994924715
  53916386601))) (cond (Nat.blt r 349) (cond (Nat.blt r 347) (cond (Nat.blt r 346) 53838190205
  53760333057) (cond (Nat.blt r 348) 53682812709 53605626741)) (cond (Nat.blt r 351) (cond (Nat.blt
  r 350) 53528772757 53452248382) (cond (Nat.blt r 352) 53376051268 53300179088))))) (cond (Nat.blt
  r 369) (cond (Nat.blt r 361) (cond (Nat.blt r 357) (cond (Nat.blt r 355) (cond (Nat.blt r 354)
  53224629541 53149400345) (cond (Nat.blt r 356) 53074489243 52999894000)) (cond (Nat.blt r 359)
  (cond (Nat.blt r 358) 52925612402 52851642258) (cond (Nat.blt r 360) 52777981396 52704627669)))
  (cond (Nat.blt r 365) (cond (Nat.blt r 363) (cond (Nat.blt r 362) 52631578947 52558833122) (cond
  (Nat.blt r 364) 52486388108 52414241836)) (cond (Nat.blt r 367) (cond (Nat.blt r 366) 52342392259
  52270837348) (cond (Nat.blt r 368) 52199575097 52128603514)))) (cond (Nat.blt r 377) (cond
  (Nat.blt r 373) (cond (Nat.blt r 371) (cond (Nat.blt r 370) 52057920629 51987524491) (cond
  (Nat.blt r 372) 51917413165 51847584736)) (cond (Nat.blt r 375) (cond (Nat.blt r 374) 51778037307
  51708768999) (cond (Nat.blt r 376) 51639777949 51571062312))) (cond (Nat.blt r 381) (cond
  (Nat.blt r 379) (cond (Nat.blt r 378) 51502620262 51434449987) (cond (Nat.blt r 380) 51366549693
  51298917604)) (cond (Nat.blt r 383) (cond (Nat.blt r 382) 51231551957 51164451009) (cond (Nat.blt
  r 384) 51097613030 51031036307)))))
/-- Chunk 6 (`385..448`) of `invSqrtLo`. -/
def invSqrtLoChunk6 (r : ℕ) : ℕ :=
  cond (Nat.blt r 417) (cond (Nat.blt r 401) (cond (Nat.blt r 393) (cond (Nat.blt r 389) (cond
  (Nat.blt r 387) (cond (Nat.blt r 386) 50964719143 50898659855) (cond (Nat.blt r 388) 50832856777
  50767308256)) (cond (Nat.blt r 391) (cond (Nat.blt r 390) 50702012656 50636968354) (cond (Nat.blt
  r 392) 50572173742 50507627227))) (cond (Nat.blt r 397) (cond (Nat.blt r 395) (cond (Nat.blt r
  394) 50443327230 50379272185) (cond (Nat.blt r 396) 50315460542 50251890762)) (cond (Nat.blt r
  399) (cond (Nat.blt r 398) 50188561322 50125470711) (cond (Nat.blt r 400) 50062617432
  50000000000)))) (cond (Nat.blt r 409) (cond (Nat.blt r 405) (cond (Nat.blt r 403) (cond (Nat.blt
  r 402) 49937616943 49875466805) (cond (Nat.blt r 404) 49813548138 49751859510)) (cond (Nat.blt r
  407) (cond (Nat.blt r 406) 49690399499 49629166698) (cond (Nat.blt r 408) 49568159709
  49507377148))) (cond (Nat.blt r 413) (cond (Nat.blt r 411) (cond (Nat.blt r 410) 49446817643
  49386479832) (cond (Nat.blt r 412) 49326362366 49266463908)) (cond (Nat.blt r 415) (cond (Nat.blt
  r 414) 49206783130 49147318718) (cond (Nat.blt r 416) 49088069367 49029033784))))) (cond (Nat.blt
  r 433) (cond (Nat.blt r 425) (cond (Nat.blt r 421) (cond (Nat.blt r 419) (cond (Nat.blt r 418)
  48970210687 48911598804) (cond (Nat.blt r 420) 48853196874 48795003647)) (cond (Nat.blt r 423)
  (cond (Nat.blt r 422) 48737017882 48679238351) (cond (Nat.blt r 424) 48621663832 48564293117)))
  (cond (Nat.blt r 429) (cond (Nat.blt r 427) (cond (Nat.blt r 426) 48507125007 48450158311) (cond
  (Nat.blt r 428) 48393391849 48336824452)) (cond (Nat.blt r 431) (cond (Nat.blt r 430) 48280454958
  48224282217) (cond (Nat.blt r 432) 48168305085 48112522432)))) (cond (Nat.blt r 441) (cond
  (Nat.blt r 437) (cond (Nat.blt r 435) (cond (Nat.blt r 434) 48056933133 48001536073) (cond
  (Nat.blt r 436) 47946330148 47891314261)) (cond (Nat.blt r 439) (cond (Nat.blt r 438) 47836487323
  47781848256) (cond (Nat.blt r 440) 47727395990 47673129462))) (cond (Nat.blt r 445) (cond
  (Nat.blt r 443) (cond (Nat.blt r 442) 47619047619 47565149415) (cond (Nat.blt r 444) 47511433814
  47457899787)) (cond (Nat.blt r 447) (cond (Nat.blt r 446) 47404546313 47351372381) (cond (Nat.blt
  r 448) 47298376984 47245559126)))))
/-- Chunk 7 (`449..512`) of `invSqrtLo`. -/
def invSqrtLoChunk7 (r : ℕ) : ℕ :=
  cond (Nat.blt r 481) (cond (Nat.blt r 465) (cond (Nat.blt r 457) (cond (Nat.blt r 453) (cond
  (Nat.blt r 451) (cond (Nat.blt r 450) 47192917818 47140452079) (cond (Nat.blt r 452) 47088160934
  47036043419)) (cond (Nat.blt r 455) (cond (Nat.blt r 454) 46984098573 46932325446) (cond (Nat.blt
  r 456) 46880723093 46829290579))) (cond (Nat.blt r 461) (cond (Nat.blt r 459) (cond (Nat.blt r
  458) 46778026972 46726931351) (cond (Nat.blt r 460) 46676002800 46625240412)) (cond (Nat.blt r
  463) (cond (Nat.blt r 462) 46574643283 46524210519) (cond (Nat.blt r 464) 46473941234
  46423834544)))) (cond (Nat.blt r 473) (cond (Nat.blt r 469) (cond (Nat.blt r 467) (cond (Nat.blt
  r 466) 46373889576 46324105461) (cond (Nat.blt r 468) 46274481338 46225016352)) (cond (Nat.blt r
  471) (cond (Nat.blt r 470) 46175709653 46126560401) (cond (Nat.blt r 472) 46077567758
  46028730894))) (cond (Nat.blt r 477) (cond (Nat.blt r 475) (cond (Nat.blt r 474) 45980048987
  45931521217) (cond (Nat.blt r 476) 45883146774 45834924851)) (cond (Nat.blt r 479) (cond (Nat.blt
  r 478) 45786854649 45738935374) (cond (Nat.blt r 480) 45691166238 45643546458))))) (cond (Nat.blt
  r 497) (cond (Nat.blt r 489) (cond (Nat.blt r 485) (cond (Nat.blt r 483) (cond (Nat.blt r 482)
  45596075258 45548751867) (cond (Nat.blt r 484) 45501575519 45454545454)) (cond (Nat.blt r 487)
  (cond (Nat.blt r 486) 45407660918 45360921162) (cond (Nat.blt r 488) 45314325442 45267873021)))
  (cond (Nat.blt r 493) (cond (Nat.blt r 491) (cond (Nat.blt r 490) 45221563164 45175395145) (cond
  (Nat.blt r 492) 45129368240 45083481733)) (cond (Nat.blt r 495) (cond (Nat.blt r 494) 45037734911
  44992127066) (cond (Nat.blt r 496) 44946657497 44901325506)))) (cond (Nat.blt r 505) (cond
  (Nat.blt r 501) (cond (Nat.blt r 499) (cond (Nat.blt r 498) 44856130401 44811071494) (cond
  (Nat.blt r 500) 44766148103 44721359549)) (cond (Nat.blt r 503) (cond (Nat.blt r 502) 44676705160
  44632184267) (cond (Nat.blt r 504) 44587796206 44543540318))) (cond (Nat.blt r 509) (cond
  (Nat.blt r 507) (cond (Nat.blt r 506) 44499415948 44455422447) (cond (Nat.blt r 508) 44411559168
  44367825470)) (cond (Nat.blt r 511) (cond (Nat.blt r 510) 44324220717 44280744277) (cond (Nat.blt
  r 512) 44237395520 44194173824)))))
/-- Chunk 8 (`513..576`) of `invSqrtLo`. -/
def invSqrtLoChunk8 (r : ℕ) : ℕ :=
  cond (Nat.blt r 545) (cond (Nat.blt r 529) (cond (Nat.blt r 521) (cond (Nat.blt r 517) (cond
  (Nat.blt r 515) (cond (Nat.blt r 514) 44151078568 44108109139) (cond (Nat.blt r 516) 44065264923
  44022545316)) (cond (Nat.blt r 519) (cond (Nat.blt r 518) 43979949713 43937477516) (cond (Nat.blt
  r 520) 43895128130 43852900965))) (cond (Nat.blt r 525) (cond (Nat.blt r 523) (cond (Nat.blt r
  522) 43810795433 43768810953) (cond (Nat.blt r 524) 43726946944 43685202833)) (cond (Nat.blt r
  527) (cond (Nat.blt r 526) 43643578047 43602072019) (cond (Nat.blt r 528) 43560684186
  43519413988)))) (cond (Nat.blt r 537) (cond (Nat.blt r 533) (cond (Nat.blt r 531) (cond (Nat.blt
  r 530) 43478260869 43437224276) (cond (Nat.blt r 532) 43396303660 43355498476)) (cond (Nat.blt r
  535) (cond (Nat.blt r 534) 43314808182 43274232240) (cond (Nat.blt r 536) 43233770116
  43193421279))) (cond (Nat.blt r 541) (cond (Nat.blt r 539) (cond (Nat.blt r 538) 43153185200
  43113061355) (cond (Nat.blt r 540) 43073049225 43033148291)) (cond (Nat.blt r 543) (cond (Nat.blt
  r 542) 42993358039 42953677958) (cond (Nat.blt r 544) 42914107542 42874646285))))) (cond (Nat.blt
  r 561) (cond (Nat.blt r 553) (cond (Nat.blt r 549) (cond (Nat.blt r 547) (cond (Nat.blt r 546)
  42835293687 42796049251) (cond (Nat.blt r 548) 42756912480 42717882885)) (cond (Nat.blt r 551)
  (cond (Nat.blt r 550) 42678959977 42640143271) (cond (Nat.blt r 552) 42601432284 42562826537)))
  (cond (Nat.blt r 557) (cond (Nat.blt r 555) (cond (Nat.blt r 554) 42524325556 42485928866) (cond
  (Nat.blt r 556) 42447635997 42409446483)) (cond (Nat.blt r 559) (cond (Nat.blt r 558) 42371359860
  42333375666) (cond (Nat.blt r 560) 42295493443 42257712736)))) (cond (Nat.blt r 569) (cond
  (Nat.blt r 565) (cond (Nat.blt r 563) (cond (Nat.blt r 562) 42220033092 42182454060) (cond
  (Nat.blt r 564) 42144975196 42107596053)) (cond (Nat.blt r 567) (cond (Nat.blt r 566) 42070316191
  42033135170) (cond (Nat.blt r 568) 41996052556 41959067914))) (cond (Nat.blt r 573) (cond
  (Nat.blt r 571) (cond (Nat.blt r 570) 41922180815 41885390829) (cond (Nat.blt r 572) 41848697531
  41812100500)) (cond (Nat.blt r 575) (cond (Nat.blt r 574) 41775599314 41739193556) (cond (Nat.blt
  r 576) 41702882811 41666666666)))))
/-- Chunk 9 (`577..640`) of `invSqrtLo`. -/
def invSqrtLoChunk9 (r : ℕ) : ℕ :=
  cond (Nat.blt r 609) (cond (Nat.blt r 593) (cond (Nat.blt r 585) (cond (Nat.blt r 581) (cond
  (Nat.blt r 579) (cond (Nat.blt r 578) 41630544712 41594516540) (cond (Nat.blt r 580) 41558581746
  41522739926)) (cond (Nat.blt r 583) (cond (Nat.blt r 582) 41486990682 41451333614) (cond (Nat.blt
  r 584) 41415768328 41380294430))) (cond (Nat.blt r 589) (cond (Nat.blt r 587) (cond (Nat.blt r
  586) 41344911529 41309619238) (cond (Nat.blt r 588) 41274417170 41239304942)) (cond (Nat.blt r
  591) (cond (Nat.blt r 590) 41204282171 41169348479) (cond (Nat.blt r 592) 41134503489
  41099746826)))) (cond (Nat.blt r 601) (cond (Nat.blt r 597) (cond (Nat.blt r 595) (cond (Nat.blt
  r 594) 41065078117 41030496993) (cond (Nat.blt r 596) 40996003084 40961596025)) (cond (Nat.blt r
  599) (cond (Nat.blt r 598) 40927275453 40893041005) (cond (Nat.blt r 600) 40858892322
  40824829046))) (cond (Nat.blt r 605) (cond (Nat.blt r 603) (cond (Nat.blt r 602) 40790850822
  40756957296) (cond (Nat.blt r 604) 40723148118 40689422938)) (cond (Nat.blt r 607) (cond (Nat.blt
  r 606) 40655781409 40622223185) (cond (Nat.blt r 608) 40588747923 40555355282))))) (cond (Nat.blt
  r 625) (cond (Nat.blt r 617) (cond (Nat.blt r 613) (cond (Nat.blt r 611) (cond (Nat.blt r 610)
  40522044923 40488816508) (cond (Nat.blt r 612) 40455669703 40422604172)) (cond (Nat.blt r 615)
  (cond (Nat.blt r 614) 40389619586 40356715613) (cond (Nat.blt r 616) 40323891927 40291148201)))
  (cond (Nat.blt r 621) (cond (Nat.blt r 619) (cond (Nat.blt r 618) 40258484111 40225899335) (cond
  (Nat.blt r 620) 40193393552 40160966445)) (cond (Nat.blt r 623) (cond (Nat.blt r 622) 40128617695
  40096346988) (cond (Nat.blt r 624) 40064154010 40032038451)))) (cond (Nat.blt r 633) (cond
  (Nat.blt r 629) (cond (Nat.blt r 627) (cond (Nat.blt r 626) 40000000000 39968038348) (cond
  (Nat.blt r 628) 39936153191 39904344223)) (cond (Nat.blt r 631) (cond (Nat.blt r 630) 39872611141
  39840953644) (cond (Nat.blt r 632) 39809371432 39777864208))) (cond (Nat.blt r 637) (cond
  (Nat.blt r 635) (cond (Nat.blt r 634) 39746431675 39715073539) (cond (Nat.blt r 636) 39683789506
  39652579285)) (cond (Nat.blt r 639) (cond (Nat.blt r 638) 39621442587 39590379123) (cond (Nat.blt
  r 640) 39559388606 39528470752)))))
/-- Chunk 10 (`641..704`) of `invSqrtLo`. -/
def invSqrtLoChunk10 (r : ℕ) : ℕ :=
  cond (Nat.blt r 673) (cond (Nat.blt r 657) (cond (Nat.blt r 649) (cond (Nat.blt r 645) (cond
  (Nat.blt r 643) (cond (Nat.blt r 642) 39497625276 39466851898) (cond (Nat.blt r 644) 39436150336
  39405520311)) (cond (Nat.blt r 647) (cond (Nat.blt r 646) 39374961547 39344473768) (cond (Nat.blt
  r 648) 39314056698 39283710065))) (cond (Nat.blt r 653) (cond (Nat.blt r 651) (cond (Nat.blt r
  650) 39253433598 39223227027) (cond (Nat.blt r 652) 39193090083 39163022499)) (cond (Nat.blt r
  655) (cond (Nat.blt r 654) 39133024009 39103094350) (cond (Nat.blt r 656) 39073233258
  39043440472)))) (cond (Nat.blt r 665) (cond (Nat.blt r 661) (cond (Nat.blt r 659) (cond (Nat.blt
  r 658) 39013715732 38984058779) (cond (Nat.blt r 660) 38954469356 38924947208)) (cond (Nat.blt r
  663) (cond (Nat.blt r 662) 38895492079 38866103716) (cond (Nat.blt r 664) 38836781869
  38807526285))) (cond (Nat.blt r 669) (cond (Nat.blt r 667) (cond (Nat.blt r 666) 38778336716
  38749212914) (cond (Nat.blt r 668) 38720154633 38691161626)) (cond (Nat.blt r 671) (cond (Nat.blt
  r 670) 38662233651 38633370464) (cond (Nat.blt r 672) 38604571824 38575837490))))) (cond (Nat.blt
  r 689) (cond (Nat.blt r 681) (cond (Nat.blt r 677) (cond (Nat.blt r 675) (cond (Nat.blt r 674)
  38547167224 38518560788) (cond (Nat.blt r 676) 38490017945 38461538461)) (cond (Nat.blt r 679)
  (cond (Nat.blt r 678) 38433122101 38404768632) (cond (Nat.blt r 680) 38376477822 38348249442)))
  (cond (Nat.blt r 685) (cond (Nat.blt r 683) (cond (Nat.blt r 682) 38320083261 38291979053) (cond
  (Nat.blt r 684) 38263936589 38235955645)) (cond (Nat.blt r 687) (cond (Nat.blt r 686) 38208035995
  38180177416) (cond (Nat.blt r 688) 38152379685 38124642583)))) (cond (Nat.blt r 697) (cond
  (Nat.blt r 693) (cond (Nat.blt r 691) (cond (Nat.blt r 690) 38096965887 38069349381) (cond
  (Nat.blt r 692) 38041792845 38014296063)) (cond (Nat.blt r 695) (cond (Nat.blt r 694) 37986858819
  37959480900) (cond (Nat.blt r 696) 37932162090 37904902178))) (cond (Nat.blt r 701) (cond
  (Nat.blt r 699) (cond (Nat.blt r 698) 37877700953 37850558205) (cond (Nat.blt r 700) 37823473723
  37796447300)) (cond (Nat.blt r 703) (cond (Nat.blt r 702) 37769478730 37742567804) (cond (Nat.blt
  r 704) 37715714320 37688918072)))))
/-- Chunk 11 (`705..768`) of `invSqrtLo`. -/
def invSqrtLoChunk11 (r : ℕ) : ℕ :=
  cond (Nat.blt r 737) (cond (Nat.blt r 721) (cond (Nat.blt r 713) (cond (Nat.blt r 709) (cond
  (Nat.blt r 707) (cond (Nat.blt r 706) 37662178857 37635496474) (cond (Nat.blt r 708) 37608870722
  37582301400)) (cond (Nat.blt r 711) (cond (Nat.blt r 710) 37555788309 37529331252) (cond (Nat.blt
  r 712) 37502930030 37476584449))) (cond (Nat.blt r 717) (cond (Nat.blt r 715) (cond (Nat.blt r
  714) 37450294313 37424059428) (cond (Nat.blt r 716) 37397879600 37371754637)) (cond (Nat.blt r
  719) (cond (Nat.blt r 718) 37345684348 37319668543) (cond (Nat.blt r 720) 37293707031
  37267799624)))) (cond (Nat.blt r 729) (cond (Nat.blt r 725) (cond (Nat.blt r 723) (cond (Nat.blt
  r 722) 37241946136 37216146378) (cond (Nat.blt r 724) 37190400165 37164707312)) (cond (Nat.blt r
  727) (cond (Nat.blt r 726) 37139067635 37113480951) (cond (Nat.blt r 728) 37087947077
  37062465833))) (cond (Nat.blt r 733) (cond (Nat.blt r 731) (cond (Nat.blt r 730) 37037037037
  37011660509) (cond (Nat.blt r 732) 36986336072 36961063547)) (cond (Nat.blt r 735) (cond (Nat.blt
  r 734) 36935842757 36910673526) (cond (Nat.blt r 736) 36885555678 36860489038))))) (cond (Nat.blt
  r 753) (cond (Nat.blt r 745) (cond (Nat.blt r 741) (cond (Nat.blt r 739) (cond (Nat.blt r 738)
  36835473434 36810508691) (cond (Nat.blt r 740) 36785594638 36760731104)) (cond (Nat.blt r 743)
  (cond (Nat.blt r 742) 36735917918 36711154910) (cond (Nat.blt r 744) 36686441912 36661778755)))
  (cond (Nat.blt r 749) (cond (Nat.blt r 747) (cond (Nat.blt r 746) 36637165272 36612601296) (cond
  (Nat.blt r 748) 36588086663 36563621206)) (cond (Nat.blt r 751) (cond (Nat.blt r 750) 36539204762
  36514837167) (cond (Nat.blt r 752) 36490518258 36466247874)))) (cond (Nat.blt r 761) (cond
  (Nat.blt r 757) (cond (Nat.blt r 755) (cond (Nat.blt r 754) 36442025853 36417852036) (cond
  (Nat.blt r 756) 36393726262 36369648372)) (cond (Nat.blt r 759) (cond (Nat.blt r 758) 36345618209
  36321635614) (cond (Nat.blt r 760) 36297700432 36273812505))) (cond (Nat.blt r 765) (cond
  (Nat.blt r 763) (cond (Nat.blt r 762) 36249971679 36226177800) (cond (Nat.blt r 764) 36202430712
  36178730264)) (cond (Nat.blt r 767) (cond (Nat.blt r 766) 36155076303 36131468676) (cond (Nat.blt
  r 768) 36107907233 36084391824)))))
/-- Chunk 12 (`769..832`) of `invSqrtLo`. -/
def invSqrtLoChunk12 (r : ℕ) : ℕ :=
  cond (Nat.blt r 801) (cond (Nat.blt r 785) (cond (Nat.blt r 777) (cond (Nat.blt r 773) (cond
  (Nat.blt r 771) (cond (Nat.blt r 770) 36060922298 36037498507) (cond (Nat.blt r 772) 36014120303
  35990787537)) (cond (Nat.blt r 775) (cond (Nat.blt r 774) 35967500063 35944257734) (cond (Nat.blt
  r 776) 35921060405 35897907930))) (cond (Nat.blt r 781) (cond (Nat.blt r 779) (cond (Nat.blt r
  778) 35874800166 35851736969) (cond (Nat.blt r 780) 35828718195 35805743701)) (cond (Nat.blt r
  783) (cond (Nat.blt r 782) 35782813348 35759926992) (cond (Nat.blt r 784) 35737084494
  35714285714)))) (cond (Nat.blt r 793) (cond (Nat.blt r 789) (cond (Nat.blt r 787) (cond (Nat.blt
  r 786) 35691530512 35668818750) (cond (Nat.blt r 788) 35646150289 35623524993)) (cond (Nat.blt r
  791) (cond (Nat.blt r 790) 35600942725 35578403348) (cond (Nat.blt r 792) 35555906726
  35533452725))) (cond (Nat.blt r 797) (cond (Nat.blt r 795) (cond (Nat.blt r 794) 35511041211
  35488672049) (cond (Nat.blt r 796) 35466345106 35444060250)) (cond (Nat.blt r 799) (cond (Nat.blt
  r 798) 35421817348 35399616270) (cond (Nat.blt r 800) 35377456883 35355339059))))) (cond (Nat.blt
  r 817) (cond (Nat.blt r 809) (cond (Nat.blt r 805) (cond (Nat.blt r 803) (cond (Nat.blt r 802)
  35333262666 35311227577) (cond (Nat.blt r 804) 35289233662 35267280792)) (cond (Nat.blt r 807)
  (cond (Nat.blt r 806) 35245368842 35223497683) (cond (Nat.blt r 808) 35201667190 35179877236)))
  (cond (Nat.blt r 813) (cond (Nat.blt r 811) (cond (Nat.blt r 810) 35158127696 35136418446) (cond
  (Nat.blt r 812) 35114749361 35093120317)) (cond (Nat.blt r 815) (cond (Nat.blt r 814) 35071531191
  35049981861) (cond (Nat.blt r 816) 35028472205 35007002100)))) (cond (Nat.blt r 825) (cond
  (Nat.blt r 821) (cond (Nat.blt r 819) (cond (Nat.blt r 818) 34985571427 34964180063) (cond
  (Nat.blt r 820) 34942827890 34921514788)) (cond (Nat.blt r 823) (cond (Nat.blt r 822) 34900240637
  34879005320) (cond (Nat.blt r 824) 34857808718 34836650714))) (cond (Nat.blt r 829) (cond
  (Nat.blt r 827) (cond (Nat.blt r 826) 34815531191 34794450031) (cond (Nat.blt r 828) 34773407121
  34752402342)) (cond (Nat.blt r 831) (cond (Nat.blt r 830) 34731435582 34710506725) (cond (Nat.blt
  r 832) 34689615656 34668762264)))))
/-- Chunk 13 (`833..896`) of `invSqrtLo`. -/
def invSqrtLoChunk13 (r : ℕ) : ℕ :=
  cond (Nat.blt r 865) (cond (Nat.blt r 849) (cond (Nat.blt r 841) (cond (Nat.blt r 837) (cond
  (Nat.blt r 835) (cond (Nat.blt r 834) 34647946433 34627168053) (cond (Nat.blt r 836) 34606427010
  34585723193)) (cond (Nat.blt r 839) (cond (Nat.blt r 838) 34565056491 34544426792) (cond (Nat.blt
  r 840) 34523833987 34503277967))) (cond (Nat.blt r 845) (cond (Nat.blt r 843) (cond (Nat.blt r
  842) 34482758620 34462275839) (cond (Nat.blt r 844) 34441829515 34421419541)) (cond (Nat.blt r
  847) (cond (Nat.blt r 846) 34401045807 34380708208) (cond (Nat.blt r 848) 34360406637
  34340140987)))) (cond (Nat.blt r 857) (cond (Nat.blt r 853) (cond (Nat.blt r 851) (cond (Nat.blt
  r 850) 34319911152 34299717028) (cond (Nat.blt r 852) 34279558509 34259435491)) (cond (Nat.blt r
  855) (cond (Nat.blt r 854) 34239347869 34219295541) (cond (Nat.blt r 856) 34199278402
  34179296351))) (cond (Nat.blt r 861) (cond (Nat.blt r 859) (cond (Nat.blt r 858) 34159349284
  34139437099) (cond (Nat.blt r 860) 34119559696 34099716973)) (cond (Nat.blt r 863) (cond (Nat.blt
  r 862) 34079908829 34060135164) (cond (Nat.blt r 864) 34040395878 34020690871))))) (cond (Nat.blt
  r 881) (cond (Nat.blt r 873) (cond (Nat.blt r 869) (cond (Nat.blt r 867) (cond (Nat.blt r 866)
  34001020045 33981383301) (cond (Nat.blt r 868) 33961780540 33942211665)) (cond (Nat.blt r 871)
  (cond (Nat.blt r 870) 33922676577 33903175181) (cond (Nat.blt r 872) 33883707378 33864273073)))
  (cond (Nat.blt r 877) (cond (Nat.blt r 875) (cond (Nat.blt r 874) 33844872171 33825504574) (cond
  (Nat.blt r 876) 33806170189 33786868919)) (cond (Nat.blt r 879) (cond (Nat.blt r 878) 33767600672
  33748365353) (cond (Nat.blt r 880) 33729162867 33709993123)))) (cond (Nat.blt r 889) (cond
  (Nat.blt r 885) (cond (Nat.blt r 883) (cond (Nat.blt r 882) 33690856026 33671751485) (cond
  (Nat.blt r 884) 33652679406 33633639699)) (cond (Nat.blt r 887) (cond (Nat.blt r 886) 33614632272
  33595657034) (cond (Nat.blt r 888) 33576713893 33557802760))) (cond (Nat.blt r 893) (cond
  (Nat.blt r 891) (cond (Nat.blt r 890) 33538923545 33520076157) (cond (Nat.blt r 892) 33501260508
  33482476509)) (cond (Nat.blt r 895) (cond (Nat.blt r 894) 33463724070 33445003104) (cond (Nat.blt
  r 896) 33426313523 33407655239)))))
/-- Chunk 14 (`897..960`) of `invSqrtLo`. -/
def invSqrtLoChunk14 (r : ℕ) : ℕ :=
  cond (Nat.blt r 929) (cond (Nat.blt r 913) (cond (Nat.blt r 905) (cond (Nat.blt r 901) (cond
  (Nat.blt r 899) (cond (Nat.blt r 898) 33389028164 33370432213) (cond (Nat.blt r 900) 33351867298
  33333333333)) (cond (Nat.blt r 903) (cond (Nat.blt r 902) 33314830232 33296357910) (cond (Nat.blt
  r 904) 33277916281 33259505261))) (cond (Nat.blt r 909) (cond (Nat.blt r 907) (cond (Nat.blt r
  906) 33241124765 33222774709) (cond (Nat.blt r 908) 33204455008 33186165579)) (cond (Nat.blt r
  911) (cond (Nat.blt r 910) 33167906340 33149677206) (cond (Nat.blt r 912) 33131478096
  33113308926)))) (cond (Nat.blt r 921) (cond (Nat.blt r 917) (cond (Nat.blt r 915) (cond (Nat.blt
  r 914) 33095169616 33077060082) (cond (Nat.blt r 916) 33058980245 33040930022)) (cond (Nat.blt r
  919) (cond (Nat.blt r 918) 33022909334 33004918099) (cond (Nat.blt r 920) 32986956237
  32969023669))) (cond (Nat.blt r 925) (cond (Nat.blt r 923) (cond (Nat.blt r 922) 32951120315
  32933246096) (cond (Nat.blt r 924) 32915400933 32897584747)) (cond (Nat.blt r 927) (cond (Nat.blt
  r 926) 32879797461 32862038995) (cond (Nat.blt r 928) 32844309272 32826608214))))) (cond (Nat.blt
  r 945) (cond (Nat.blt r 937) (cond (Nat.blt r 933) (cond (Nat.blt r 931) (cond (Nat.blt r 930)
  32808935746 32791291789) (cond (Nat.blt r 932) 32773676267 32756089104)) (cond (Nat.blt r 935)
  (cond (Nat.blt r 934) 32738530223 32720999550) (cond (Nat.blt r 936) 32703497008 32686022523)))
  (cond (Nat.blt r 941) (cond (Nat.blt r 939) (cond (Nat.blt r 938) 32668576019 32651157422) (cond
  (Nat.blt r 940) 32633766658 32616403652)) (cond (Nat.blt r 943) (cond (Nat.blt r 942) 32599068331
  32581760622) (cond (Nat.blt r 944) 32564480451 32547227745)))) (cond (Nat.blt r 953) (cond
  (Nat.blt r 949) (cond (Nat.blt r 947) (cond (Nat.blt r 946) 32530002431 32512804438) (cond
  (Nat.blt r 948) 32495633692 32478490123)) (cond (Nat.blt r 951) (cond (Nat.blt r 950) 32461373658
  32444284226) (cond (Nat.blt r 952) 32427221756 32410186177))) (cond (Nat.blt r 957) (cond
  (Nat.blt r 955) (cond (Nat.blt r 954) 32393177419 32376195411) (cond (Nat.blt r 956) 32359240084
  32342311367)) (cond (Nat.blt r 959) (cond (Nat.blt r 958) 32325409191 32308533487) (cond (Nat.blt
  r 960) 32291684186 32274861218)))))
/-- Chunk 15 (`961..1024`) of `invSqrtLo`. -/
def invSqrtLoChunk15 (r : ℕ) : ℕ :=
  cond (Nat.blt r 993) (cond (Nat.blt r 977) (cond (Nat.blt r 969) (cond (Nat.blt r 965) (cond
  (Nat.blt r 963) (cond (Nat.blt r 962) 32258064516 32241294010) (cond (Nat.blt r 964) 32224549634
  32207831320)) (cond (Nat.blt r 967) (cond (Nat.blt r 966) 32191138998 32174472604) (cond (Nat.blt
  r 968) 32157832069 32141217326))) (cond (Nat.blt r 973) (cond (Nat.blt r 971) (cond (Nat.blt r
  970) 32124628310 32108064953) (cond (Nat.blt r 972) 32091527190 32075014954)) (cond (Nat.blt r
  975) (cond (Nat.blt r 974) 32058528181 32042066805) (cond (Nat.blt r 976) 32025630761
  32009219983)))) (cond (Nat.blt r 985) (cond (Nat.blt r 981) (cond (Nat.blt r 979) (cond (Nat.blt
  r 978) 31992834407 31976473969) (cond (Nat.blt r 980) 31960138605 31943828249)) (cond (Nat.blt r
  983) (cond (Nat.blt r 982) 31927542840 31911282313) (cond (Nat.blt r 984) 31895046605
  31878835653))) (cond (Nat.blt r 989) (cond (Nat.blt r 987) (cond (Nat.blt r 986) 31862649393
  31846487764) (cond (Nat.blt r 988) 31830350703 31814238148)) (cond (Nat.blt r 991) (cond (Nat.blt
  r 990) 31798150037 31782086308) (cond (Nat.blt r 992) 31766046899 31750031750))))) (cond (Nat.blt
  r 1009) (cond (Nat.blt r 1001) (cond (Nat.blt r 997) (cond (Nat.blt r 995) (cond (Nat.blt r 994)
  31734040798 31718073984) (cond (Nat.blt r 996) 31702131247 31686212526)) (cond (Nat.blt r 999)
  (cond (Nat.blt r 998) 31670317760 31654446891) (cond (Nat.blt r 1000) 31638599858 31622776601)))
  (cond (Nat.blt r 1005) (cond (Nat.blt r 1003) (cond (Nat.blt r 1002) 31606977062 31591201180)
  (cond (Nat.blt r 1004) 31575448897 31559720154)) (cond (Nat.blt r 1007) (cond (Nat.blt r 1006)
  31544014893 31528333055) (cond (Nat.blt r 1008) 31512674583 31497039417)))) (cond (Nat.blt r
  1017) (cond (Nat.blt r 1013) (cond (Nat.blt r 1011) (cond (Nat.blt r 1010) 31481427501
  31465838776) (cond (Nat.blt r 1012) 31450273186 31434730673)) (cond (Nat.blt r 1015) (cond
  (Nat.blt r 1014) 31419211180 31403714651) (cond (Nat.blt r 1016) 31388241028 31372790256))) (cond
  (Nat.blt r 1021) (cond (Nat.blt r 1019) (cond (Nat.blt r 1018) 31357362279 31341957040) (cond
  (Nat.blt r 1020) 31326574483 31311214554)) (cond (Nat.blt r 1023) (cond (Nat.blt r 1022)
  31295877196 31280562354) (cond (Nat.blt r 1024) 31265269974 31250000000)))))
/-- Certified floor table `invSqrtLo r ≤ 10^12 / √r` for `1 ≤ r ≤ 1024`. -/
def invSqrtLo (r : ℕ) : ℕ :=
  cond (Nat.blt r 1) 0 (cond (Nat.blt 1024 r) 0 (cond (Nat.blt r 513) (cond (Nat.blt r 257)
  (cond (Nat.blt r 129) (cond (Nat.blt r 65) (invSqrtLoChunk0 r) (invSqrtLoChunk1 r)) (cond
  (Nat.blt r 193) (invSqrtLoChunk2 r) (invSqrtLoChunk3 r))) (cond (Nat.blt r 385) (cond
  (Nat.blt r 321) (invSqrtLoChunk4 r) (invSqrtLoChunk5 r)) (cond (Nat.blt r 449)
  (invSqrtLoChunk6 r) (invSqrtLoChunk7 r)))) (cond (Nat.blt r 769) (cond (Nat.blt r 641)
  (cond (Nat.blt r 577) (invSqrtLoChunk8 r) (invSqrtLoChunk9 r)) (cond (Nat.blt r 705)
  (invSqrtLoChunk10 r) (invSqrtLoChunk11 r))) (cond (Nat.blt r 897) (cond (Nat.blt r 833)
  (invSqrtLoChunk12 r) (invSqrtLoChunk13 r)) (cond (Nat.blt r 961) (invSqrtLoChunk14 r)
  (invSqrtLoChunk15 r))))))
/-- Certified harmonic lower bound `harmSumPow2 kIdx ≤ 10^12 * ∑_{r=1}^{2^kIdx} 1/√r`. -/
def harmSumPow2 (kIdx : ℕ) : ℕ :=
  cond (Nat.blt 10 kIdx) 0 (cond (Nat.blt kIdx 5) (cond (Nat.blt kIdx 2) (cond (Nat.blt kIdx
  1) 1000000000000 1707106781186) (cond (Nat.blt kIdx 3) 2784457050375 (cond (Nat.blt kIdx
  4) 4371436799939 6663994608230))) (cond (Nat.blt kIdx 8) (cond (Nat.blt kIdx 6)
  9941512173863 (cond (Nat.blt kIdx 7) 14602064112190 21211227890778)) (cond (Nat.blt kIdx
  9) 30570885318540 (cond (Nat.blt kIdx 10) 43816572977247 62555269219112))))
/-- Certified upper bound `sqrtMUpNat d ≥ 10^12 * √(2 ^ d)` for `d ≤ 10`. -/
def sqrtMUpNat (d : ℕ) : ℕ :=
  cond (Nat.blt 10 d) 0 (cond (Nat.blt d 5) (cond (Nat.blt d 2) (cond (Nat.blt d 1)
  1000000000000 1414213562374) (cond (Nat.blt d 3) 2000000000000 (cond (Nat.blt d 4)
  2828427124747 4000000000000))) (cond (Nat.blt d 8) (cond (Nat.blt d 6) 5656854249493 (cond
  (Nat.blt d 7) 8000000000000 11313708498985)) (cond (Nat.blt d 9) 16000000000000 (cond
  (Nat.blt d 10) 22627416997970 32000000000000))))
/-- `[5/4]` Padé check at scale `10^5` (`arctan (tn / 10^5) ≤ phiHi / 10^12`). -/
def checkPade54Scale5 (tn phiHi : ℕ) : Bool :=
  decide (tn * (945 * 100000000000000000000 + 735 * tn * tn * 10000000000 +
      64 * tn * tn * tn * tn) * 1000000000000 ≤
    phiHi * 100000 * (945 * 100000000000000000000 + 1050 * tn * tn * 10000000000 +
      225 * tn * tn * tn * tn))
/-- `[5/4]` Padé check at scale `10^8` (`arctan (td / 10^8) ≤ numU / 10^12`). -/
def checkPade54Scale8 (td numU : ℕ) : Bool :=
  decide (td * 10000 * (945 * 100000000000000000000000000000000 +
      735 * td * td * 10000000000000000 + 64 * td * td * td * td) ≤
    numU * (945 * 100000000000000000000000000000000 +
      1050 * td * td * 10000000000000000 + 225 * td * td * td * td))
/-- Octant-folded `[5/4]` / `[5/6]` Padé check for `arctan (tn / 100000) ≤ phiHi / 10^12`. -/
def checkOctantAtan (tn phiHi : ℕ) : Bool :=
  decide (tn ≤ 100000) &&
  if 12 * tn ≤ 500000 then
    checkPade54Scale5 tn phiHi
  else
    withForcedNat (100000 - tn) fun a ↦
    withForcedNat (100000 + tn) fun b ↦
    withForcedNat (a * a) fun a2 ↦
    withForcedNat (b * b) fun b2 ↦
    withForcedNat (a * b * (1155 * b2 * b2 + 1190 * a2 * b2 + 231 * a2 * a2)) fun pHom ↦
    withForcedNat (1155 * b2 * b2 * b2 + 1575 * a2 * b2 * b2 +
      525 * a2 * a2 * b2 + 25 * a2 * a2 * a2) fun qHom ↦
    decide (785398163398 * qHom ≤ phiHi * qHom + 1000000000000 * pHom)
/-- Computable click-term bound check at stage `r ≥ 1` (`m = 2 ^ d`). -/
def checkClickRow (m r tn stepNum : ℕ) : Bool :=
  decide ((100000000 * 100000 * 1000000000000) * (100000000 * 100000 * 1000000000000) ≤
    r * (4 * m * 99999998 * tn * stepNum) * (4 * m * 99999998 * tn * stepNum))
/-- Computable coherent-fusion drift check at stage `r ≥ 2`. -/
def checkFuseDriftCert (r tCur tPrev phiHiPrev tBfLo tanDiffHi numU cNat uNat : ℕ) : Bool :=
  decide ((r * 10000000000 + tCur * tCur) * tBfLo * tBfLo ≤
    (r - 1) * tCur * tCur * 1000000000000 * 1000000000000) &&
  (if tPrev * 10000000 ≤ tBfLo then
    numU == 0
  else
    decide ((tPrev * 10000000 - tBfLo) * 10000000000000 ≤
      tanDiffHi * (100000000000000000 + tPrev * tBfLo)) &&
    checkPade54Scale8 tanDiffHi numU) &&
  decide (1 ≤ cNat) &&
  decide (phiHiPrev * phiHiPrev ≤ 4 * (r - 1) * (cNat - 1) * (cNat - 1)) &&
  decide (1 ≤ uNat) &&
  decide (uNat ≤ cNat) &&
  decide (numU * numU ≤ 4 * (r - 1) * (uNat - 1) * (uNat - 1))
/-- Computable certificate for stage `r = i + 1` of cell `(d, kIdx)`. -/
def checkFuseStageIdx (rowFn : ℕ → FuseStageRow) (d i : ℕ) : Bool :=
  let m := 2 ^ d
  let r := i + 1
  match rowFn r with
  | ⟨v, tCur, phiHi, tBfLo, tdHi, numU, stepNum, cNat, uNat⟩ =>
    decide (500 ≤ tCur) && decide (tCur ≤ 100000) &&
    checkOctantAtan tCur phiHi &&
    checkClickRow m r tCur stepNum &&
    if r == 1 then
      decide (stepNum ≤ v)
    else
      match rowFn i with
      | ⟨vPrev, tPrev, phiHiPrev, _, _, _, _, _, _⟩ =>
        checkFuseDriftCert r tCur tPrev phiHiPrev tBfLo tdHi numU cNat uNat &&
        checkOctantAtan tPrev phiHiPrev &&
        decide (vPrev + stepNum ≤ v) &&
        decide (m * 99999999 * uNat + 100000000 * (cNat - uNat) ≤
          (v - vPrev - stepNum) * (m * 99999999))
/-- Full certificate for coherent-fusion cell `(d, kIdx)`. -/
def checkFuseCellRow (rowFn : ℕ → FuseStageRow) (d kIdx topR relCostNum : ℕ) : Bool :=
  let k := 2 ^ kIdx
  match rowFn 0, rowFn k with
  | ⟨v0, _, _, _, _, _, _, _, _⟩, ⟨vK, tK, phiHiK, _, _, _, _, _, _⟩ =>
    (v0 == 0) &&
    decide (d < 11) &&
    decide (kIdx < 11) &&
    allRange (checkFuseStageIdx rowFn d) k &&
    decide (1 ≤ topR) &&
    decide (500 ≤ tK) && decide (tK ≤ 100000) &&
    checkOctantAtan tK phiHiK &&
    decide (phiHiK * phiHiK ≤ 4 * k * (topR - 1) * (topR - 1)) &&
    decide ((vK + topR) * 10000000000 * sqrtMUpNat d ≤
      relCostNum * 785398163397 * harmSumPow2 kIdx)
/-- Check `invSqrtLo (i + 1)` floor square bound. -/
def checkInvSqrtItem (i : ℕ) : Bool :=
  withForcedNat (invSqrtLo (i + 1)) fun v ↦
    decide ((i + 1) * v * v ≤ 1000000000000 * 1000000000000)
/-- Check `harmSumPow2 kIdx == sumIccOne invSqrtLo (2 ^ kIdx)`. -/
def checkHarmPow2Item (kIdx : ℕ) : Bool :=
  harmSumPow2 kIdx == sumIccOne invSqrtLo (2 ^ kIdx)
/-- Check `sqrtMUpNat d` upper square bound. -/
def checkSqrtMItem (d : ℕ) : Bool :=
  withForcedNat (sqrtMUpNat d) fun s ↦
    decide (0 < s) && decide ((2 ^ d) * 1000000000000 * 1000000000000 ≤ s * s)
/-- Master certificate for `invSqrtLo`, `harmSumPow2`, and `sqrtMUpNat`. -/
def checkAuxTables : Bool :=
  allRange checkInvSqrtItem 1024 &&
  allRange checkHarmPow2Item 11 &&
  allRange checkSqrtMItem 11
private def rSeg (lo : ℕ) : ℕ → Bool
  | 0 => true | k + 1 => rSeg lo k && checkInvSqrtItem (lo + k)
private theorem allR_add (lo : ℕ) : ∀ k, allRange checkInvSqrtItem lo = true → rSeg lo k = true →
  allRange checkInvSqrtItem (lo + k) = true
  | 0, h0, _ => h0 | k + 1, h0, hs => by
    rw [rSeg, Bool.and_eq_true] at hs; rw [← Nat.add_assoc, allRange, Bool.and_eq_true]
    exact ⟨allR_add lo k h0 hs.1, hs.2⟩
private def sSeg (b a : ℕ) : ℕ → ℕ
  | 0 => a | k + 1 => withForcedNat (sSeg b a k) fun x ↦ x + invSqrtLo (b + k + 1)
private theorem sIcc_add (b : ℕ) : ∀ k, sumIccOne invSqrtLo (b + k) = sSeg b (sumIccOne invSqrtLo b)
  k
  | 0 => rfl | k + 1 => by rw [← Nat.add_assoc, sumIccOne, sSeg, sIcc_add b k]
private def sFast : ℕ → ℕ
  | 0 => 0 | b + 1 => withForcedNat (sFast b) fun a ↦ sSeg (128 * b) a 128
private theorem sFast_eq : ∀ b, sFast b = sumIccOne invSqrtLo (128 * b)
  | 0 => rfl | b + 1 => by rw [sFast, withForcedNat_eq, sFast_eq b, Nat.mul_succ, ← sIcc_add]
private theorem aux_ok : (rSeg 0 128 && rSeg 128 128 && rSeg 256 128 && rSeg 384 128 &&
    rSeg 512 128 && rSeg 640 128 && rSeg 768 128 && rSeg 896 128 && allRange checkHarmPow2Item 8 &&
    (harmSumPow2 8 == sFast 2) && (harmSumPow2 9 == sFast 4) && (harmSumPow2 10 == sFast 8) &&
    allRange checkSqrtMItem 11) = true := rfl
theorem cert_auxTables : checkAuxTables = true := by
  have h := aux_ok; simp only [Bool.and_eq_true, and_assoc] at h; rcases h with ⟨h0, h1, h2, h3, h4,
    h5, h6, h7, hh7, hh8, hh9, hh10, hs⟩
  rw [sFast_eq 2, show 128 * 2 = 2 ^ 8 by norm_num] at hh8
  rw [sFast_eq 4, show 128 * 4 = 2 ^ 9 by norm_num] at hh9
  rw [sFast_eq 8, show 128 * 8 = 2 ^ 10 by norm_num] at hh10
  unfold checkAuxTables;
    simp only [Bool.and_eq_true]; refine ⟨⟨?_, ?_⟩, hs⟩
  · exact allR_add 896 128 (allR_add 768 128 (allR_add 640 128 (allR_add 512 128 (allR_add 384 128
      (allR_add 256 128 (allR_add 128 128 (allR_add 0 128 rfl h0) h1) h2) h3) h4) h5) h6) h7
  · rw [allRange, Bool.and_eq_true]; refine ⟨?_, hh10⟩; rw [allRange, Bool.and_eq_true]; refine ⟨?_,
      hh9⟩; rw [allRange, Bool.and_eq_true]; exact ⟨hh7, hh8⟩

/-! ## Real-Analytic Soundness Lemmas -/
theorem sq_le_imp_le {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith [sq_nonneg (b - a)]
/-- `[5/4]` Padé upper bound on `Real.arctan x` for `0 ≤ x`. -/
theorem arctan_le_pade54 {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x * (945 + 735 * x ^ 2 + 64 * x ^ 4)
  / (945 + 1050 * x ^ 2 + 225 * x ^ 4) := by
  let P : ℝ → ℝ := fun y ↦ 945 * y + 735 * y ^ 3 + 64 * y ^ 5
  let Q : ℝ → ℝ := fun y ↦ 945 + 1050 * y ^ 2 + 225 * y ^ 4
  have hQ_pos : ∀ y : ℝ, 0 < Q y := fun y ↦ by dsimp only [Q]; positivity
  have hd : ∀ y : ℝ, HasDerivAt (fun z : ℝ ↦ P z / Q z - Real.arctan z) (((945 + 2205 * y ^ 2 + 320
    * y ^ 4) * Q y - P y * (2100 * y + 900 * y ^ 3)) / Q y ^ 2 - 1 / (1 + y ^ 2)) y := fun y ↦ by
    have hdP : HasDerivAt P (945 + 2205 * y ^ 2 + 320 * y ^ 4) y := ((((hasDerivAt_id' y).const_mul
      945).add ((hasDerivAt_pow 3 y).const_mul 735)).add ((hasDerivAt_pow 5 y).const_mul
      64)).congr_deriv (by push_cast; ring); have hdQ : HasDerivAt Q (2100 * y + 900 * y ^ 3) y :=
      ((((hasDerivAt_pow 2 y).const_mul 1050).const_add 945).add ((hasDerivAt_pow 4 y).const_mul
      225)).congr_deriv (by push_cast; ring)
    exact (hdP.div hdQ (hQ_pos y).ne').sub (Real.hasDerivAt_arctan y)
  have hcont : ContinuousOn (fun z : ℝ ↦ P z / Q z - Real.arctan z) (Set.Ici 0) := fun y _ ↦ (hd
    y).continuousAt.continuousWithinAt; have hdiff : DifferentiableOn ℝ (fun z : ℝ ↦ P z / Q z -
    Real.arctan z) (interior (Set.Ici (0 : ℝ))) := fun y _ ↦ (hd
    y).differentiableAt.differentiableWithinAt
  have hmono := monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hcont hdiff fun y _ ↦ by
    rw [(hd y).deriv]; have h1y : 0 < 1 + y ^ 2 := (by positivity); have hQy : 0 < Q y := hQ_pos y
    have hident : ((945 + 2205 * y ^ 2 + 320 * y ^ 4) * Q y - P y * (2100 * y + 900 * y ^ 3)) / Q y
      ^ 2 - 1 / (1 + y ^ 2) = (14400 * (y ^ 5) ^ 2) / (Q y ^ 2 * (1 + y ^ 2)) :=
      (by dsimp only [P, Q]; field_simp [hQy.ne', h1y.ne']; ring); rw [hident]; positivity
  have h0 := hmono (le_rfl : (0 : ℝ) ≤ 0) hx hx; dsimp only at h0; have h0_eq : P 0 / Q 0 -
    Real.arctan 0 = 0 := (by simp [P, Q]); rw [h0_eq] at h0; have hPx : P x = x * (945 + 735 * x ^ 2
    + 64 * x ^ 4) := (by dsimp only [P]; ring); rw [← hPx]; linarith
/-- `[5/6]` Padé lower bound on `Real.arctan y` for `0 ≤ y` (residual `-6400 y^12`). -/
theorem pade56_le_arctan {y : ℝ} (hy : 0 ≤ y) : y * (1155 + 1190 * y ^ 2 + 231 * y ^ 4) / (1155 +
  1575 * y ^ 2 + 525 * y ^ 4 + 25 * y ^ 6) ≤ Real.arctan y := by
  let P : ℝ → ℝ := fun z ↦ 1155 * z + 1190 * z ^ 3 + 231 * z ^ 5
  let Q : ℝ → ℝ := fun z ↦ 1155 + 1575 * z ^ 2 + 525 * z ^ 4 + 25 * z ^ 6
  have hQ_pos : ∀ z : ℝ, 0 < Q z := fun z ↦ by dsimp only [Q]; positivity
  have hd : ∀ z : ℝ, HasDerivAt (fun w : ℝ ↦ Real.arctan w - P w / Q w) (1 / (1 + z ^ 2) - ((1155 +
    3570 * z ^ 2 + 1155 * z ^ 4) * Q z - P z * (3150 * z + 2100 * z ^ 3 + 150 * z ^ 5)) / Q z ^ 2) z
    := fun z ↦ by
    have hdP : HasDerivAt P (1155 + 3570 * z ^ 2 + 1155 * z ^ 4) z := ((((hasDerivAt_id'
      z).const_mul 1155).add ((hasDerivAt_pow 3 z).const_mul 1190)).add ((hasDerivAt_pow 5
      z).const_mul 231)).congr_deriv (by push_cast; ring)
    have hdQ : HasDerivAt Q (3150 * z + 2100 * z ^ 3 + 150 * z ^ 5) z := (((((hasDerivAt_pow 2
      z).const_mul 1575).const_add 1155).add ((hasDerivAt_pow 4 z).const_mul 525)).add
      ((hasDerivAt_pow 6 z).const_mul 25)).congr_deriv (by push_cast; ring)
    exact (Real.hasDerivAt_arctan z).sub (hdP.div hdQ (hQ_pos z).ne')
  have hcont : ContinuousOn (fun w : ℝ ↦ Real.arctan w - P w / Q w) (Set.Ici 0) := fun z _ ↦ (hd
    z).continuousAt.continuousWithinAt; have hdiff : DifferentiableOn ℝ (fun w : ℝ ↦ Real.arctan w -
    P w / Q w) (interior (Set.Ici (0 : ℝ))) := fun z _ ↦ (hd
    z).differentiableAt.differentiableWithinAt
  have hmono := monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hcont hdiff fun z _ ↦ by
    rw [(hd z).deriv]; have h1z : 0 < 1 + z ^ 2 := (by positivity); have hQz : 0 < Q z := hQ_pos z
    have hident : 1 / (1 + z ^ 2) - ((1155 + 3570 * z ^ 2 + 1155 * z ^ 4) * Q z - P z * (3150 * z +
      2100 * z ^ 3 + 150 * z ^ 5)) / Q z ^ 2 = (6400 * (z ^ 6) ^ 2) / ((1 + z ^ 2) * Q z ^ 2) :=
      (by dsimp only [P, Q]; field_simp [h1z.ne', hQz.ne']; ring); rw [hident]; positivity
  have h0 := hmono (le_rfl : (0 : ℝ) ≤ 0) hy hy; dsimp only at h0
  have h0_eq : Real.arctan 0 - P 0 / Q 0 = 0 := (by simp [P, Q]); rw [h0_eq] at h0; have hPy : P y =
    y * (1155 + 1190 * y ^ 2 + 231 * y ^ 4) := (by dsimp only [P]; ring); rw [← hPy]; linarith
/-- Octant reflection inequality `arctan x ≤ π / 4 - arctan ((1 - x) / (1 + x))` for `0 ≤ x
  ≤ 1`. -/
theorem arctan_le_pi_div_four_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : Real.arctan x ≤ π / 4 -
  Real.arctan ((1 - x) / (1 + x)) := by
  let F : ℝ → ℝ := fun z ↦ Real.arctan z + Real.arctan ((1 + (-1 : ℝ) * z) / (1 + z))
  have hd : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt F 0 z := fun z hz ↦ by
    have hz0 : 0 ≤ z := hz; have h1z : 0 < 1 + z := (by linarith)
    have hnum : HasDerivAt (fun w : ℝ ↦ 1 + (-1 : ℝ) * w) (-1) z :=
      ((hasDerivAt_id' z).const_mul (-1)).const_add 1 |>.congr_deriv (by ring)
    have hden : HasDerivAt (fun w : ℝ ↦ 1 + w) 1 z := (hasDerivAt_id' z).const_add 1; have hq :=
      hnum.div hden h1z.ne'; have hcomp := (Real.hasDerivAt_arctan ((1 + (-1 : ℝ) * z) / (1 +
      z))).comp z hq; refine ((Real.hasDerivAt_arctan z).add hcomp).congr_deriv ?_; have hden2 : 0 <
      1 + ((1 + (-1 : ℝ) * z) / (1 + z)) ^ 2 := (by positivity); have h1z2 : 0 < 1 + z ^ 2 :=
      (by positivity); field_simp [h1z.ne', hden2.ne', h1z2.ne']; ring
  have hcont : ContinuousOn F (Set.Ici 0) := fun z hz ↦ (hd z hz).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ F (interior (Set.Ici (0 : ℝ))) := fun z hz ↦ by
    rw [interior_Ici] at hz; exact (hd z hz.le).differentiableAt.differentiableWithinAt
  have hmono := monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hcont hdiff fun z hz ↦ by
    rw [interior_Ici] at hz; rw [(hd z hz.le).deriv]
  have hle := hmono hx0 (by norm_num : (0 : ℝ) ≤ 1) hx1; have hF1 : F 1 = π / 4 :=
    (by dsimp only [F]; norm_num [Real.arctan_one]); rw [hF1] at hle; dsimp only [F] at hle
  have hrew : (1 + (-1 : ℝ) * x) / (1 + x) = (1 - x) / (1 + x) := (by ring); rw [hrew] at hle;
    linarith
theorem pade54Scale5_sound {tn phiHi : ℕ} (h : checkPade54Scale5 tn phiHi = true) : Real.arctan ((tn
  : ℝ) / 100000) ≤ (phiHi : ℝ) / 1000000000000 := by
  have hnat := of_decide_eq_true h; set x : ℝ := (tn : ℝ) / 100000; refine (arctan_le_pade54
    (by positivity : 0 ≤ x)).trans ?_; have hden_pos : 0 < 945 + 1050 * x ^ 2 + 225 * x ^ 4 :=
    (by positivity); rw [div_le_div_iff₀ hden_pos (by norm_num)]; have hcast : (tn : ℝ) * (945 *
    100000000000000000000 + 735 * tn * tn * 10000000000 + 64 * tn * tn * tn * tn) * 1000000000000 ≤
    (phiHi : ℝ) * 100000 * (945 * 100000000000000000000 + 1050 * tn * tn * 10000000000 + 225 * tn *
    tn * tn * tn) := (by exact_mod_cast hnat); dsimp only [x]; linarith [hcast, show ((tn : ℝ) /
    100000) * (945 + 735 * ((tn : ℝ) / 100000) ^ 2 + 64 * ((tn : ℝ) / 100000) ^ 4) * 1000000000000 -
    (phiHi : ℝ) * (945 + 1050 * ((tn : ℝ) / 100000) ^ 2 + 225 * ((tn : ℝ) / 100000) ^ 4) = ((tn : ℝ)
    * (945 * 100000000000000000000 + 735 * tn * tn * 10000000000 + 64 * tn * tn * tn * tn) *
    1000000000000 - (phiHi : ℝ) * 100000 * (945 * 100000000000000000000 + 1050 * tn * tn *
    10000000000 + 225 * tn * tn * tn * tn)) / 10000000000000000000000000 by ring]
theorem pade54Scale8_sound {td numU : ℕ} (h : checkPade54Scale8 td numU = true) : Real.arctan ((td :
  ℝ) / 100000000) ≤ (numU : ℝ) / 1000000000000 := by
  have hnat := of_decide_eq_true h; set x : ℝ := (td : ℝ) / 100000000; refine (arctan_le_pade54
    (by positivity : 0 ≤ x)).trans ?_; have hden_pos : 0 < 945 + 1050 * x ^ 2 + 225 * x ^ 4 :=
    (by positivity); rw [div_le_div_iff₀ hden_pos (by norm_num)]; have hcast : (td : ℝ) * 10000 *
    (945 * 100000000000000000000000000000000 + 735 * td * td * 10000000000000000 + 64 * td * td * td
    * td) ≤ (numU : ℝ) * (945 * 100000000000000000000000000000000 + 1050 * td * td *
    10000000000000000 + 225 * td * td * td * td) := (by exact_mod_cast hnat); dsimp only [x]
  linarith [hcast, show ((td : ℝ) / 100000000) * (945 + 735 * ((td : ℝ) / 100000000) ^ 2 + 64 * ((td
    : ℝ) / 100000000) ^ 4) * 1000000000000 - (numU : ℝ) * (945 + 1050 * ((td : ℝ) / 100000000) ^ 2 +
    225 * ((td : ℝ) / 100000000) ^ 4) = ((td : ℝ) * 10000 * (945 * 100000000000000000000000000000000
    + 735 * td * td * 10000000000000000 + 64 * td * td * td * td) - (numU : ℝ) * (945 *
    100000000000000000000000000000000 + 1050 * td * td * 10000000000000000 + 225 * td * td * td *
    td)) / 100000000000000000000000000000000 by ring]
theorem octantAtan_sound {tn phiHi : ℕ} (h : checkOctantAtan tn phiHi = true) : Real.arctan ((tn :
  ℝ) / 100000) ≤ (phiHi : ℝ) / 1000000000000 := by
  simp only [checkOctantAtan, Bool.and_eq_true] at h; have htn_le := of_decide_eq_true h.1
  have hbody := h.2; by_cases h12 : 12 * tn ≤ 500000
  · rw [ite_eq_left h12] at hbody; exact pade54Scale5_sound hbody
  · rw [ite_eq_right h12] at hbody; simp only [withForcedNat_eq] at hbody; have hnat :=
      of_decide_eq_true hbody; set a : ℕ := 100000 - tn; set b : ℕ := 100000 + tn; set x : ℝ := (tn
      : ℝ) / 100000; set y : ℝ := (a : ℝ) / b; have hx0 : 0 ≤ x := (by positivity)
    have hx1 : x ≤ 1 :=
      (by dsimp only [x]; have : (tn : ℝ) ≤ 100000 := (by exact_mod_cast htn_le); linarith)
    have hb_pos : (0 : ℝ) < b := (by have : 0 < b := (by omega); exact_mod_cast this)
    have ha_sub : (a : ℝ) = 100000 - tn :=
      (by dsimp only [a]; rw [Nat.cast_sub htn_le]; push_cast; rfl)
    have hb_add : (b : ℝ) = 100000 + tn := (by dsimp only [b]; push_cast; rfl)
    have hy_eq : (1 - x) / (1 + x) = y := by
      dsimp only [x, y]; rw [ha_sub, hb_add]; have h1x : (1 : ℝ) + (tn : ℝ) / 100000 ≠ 0 :=
        (by positivity); have hb_ne : (100000 : ℝ) + tn ≠ 0 := (by positivity); field_simp [h1x,
        hb_ne]
    have hy0 : 0 ≤ y := (by positivity); have hp56 := pade56_le_arctan hy0; have hoct :=
      arctan_le_pi_div_four_sub hx0 hx1; rw [hy_eq] at hoct; have hpi : π / 4 ≤ (785398163398 : ℝ) /
      1000000000000 := (by linarith [Real.pi_lt_d20]); set pHomR : ℝ := (a : ℝ) * b * (1155 * (b :
      ℝ) ^ 4 + 1190 * (a : ℝ) ^ 2 * (b : ℝ) ^ 2 + 231 * (a : ℝ) ^ 4); set qHomR : ℝ := 1155 * (b :
      ℝ) ^ 6 + 1575 * (a : ℝ) ^ 2 * (b : ℝ) ^ 4 + 525 * (a : ℝ) ^ 4 * (b : ℝ) ^ 2 + 25 * (a : ℝ) ^ 6
    have hq_pos : 0 < qHomR := (by dsimp only [qHomR]; positivity)
    have hrat_eq : y * (1155 + 1190 * y ^ 2 + 231 * y ^ 4) / (1155 + 1575 * y ^ 2 + 525 * y ^ 4 + 25
      * y ^ 6) = pHomR / qHomR := by
      dsimp only [y, pHomR, qHomR]; have hden_y : 0 < 1155 + 1575 * ((a : ℝ) / b) ^ 2 + 525 * ((a :
        ℝ) / b) ^ 4 + 25 * ((a : ℝ) / b) ^ 6 := (by positivity); field_simp [hb_pos.ne', hden_y.ne',
        hq_pos.ne']
    have hcast : 785398163398 * qHomR ≤ (phiHi : ℝ) * qHomR + 1000000000000 * pHomR := by
      have hraw : (785398163398 : ℝ) * (1155 * (b * b : ℝ) * (b * b) * (b * b) + 1575 * (a * a) * (b
        * b) * (b * b) + 525 * (a * a) * (a * a) * (b * b) + 25 * (a * a) * (a * a) * (a * a)) ≤
        (phiHi : ℝ) * (1155 * (b * b : ℝ) * (b * b) * (b * b) + 1575 * (a * a) * (b * b) * (b * b) +
        525 * (a * a) * (a * a) * (b * b) + 25 * (a * a) * (a * a) * (a * a)) + 1000000000000 * ((a
        : ℝ) * b * (1155 * (b * b) * (b * b) + 1190 * (a * a) * (b * b) + 231 * (a * a) * (a * a)))
        := (by exact_mod_cast hnat); dsimp only [pHomR, qHomR]
      linarith [hraw, show 1155 * (b : ℝ) ^ 6 + 1575 * (a : ℝ) ^ 2 * (b : ℝ) ^ 4 +
            525 * (a : ℝ) ^ 4 * (b : ℝ) ^ 2 + 25 * (a : ℝ) ^ 6 =
          1155 * (b * b : ℝ) * (b * b) * (b * b) + 1575 * (a * a) * (b * b) * (b * b) +
            525 * (a * a) * (a * a) * (b * b) + 25 * (a * a) * (a * a) * (a * a) by ring,
        show (a : ℝ) * b * (1155 * (b : ℝ) ^ 4 + 1190 * (a : ℝ) ^ 2 * (b : ℝ) ^ 2 +
            231 * (a : ℝ) ^ 4) =
          (a : ℝ) * b * (1155 * (b * b) * (b * b) + 1190 * (a * a) * (b * b) +
            231 * (a * a) * (a * a)) by ring]
    have hdiv : (785398163398 : ℝ) / 1000000000000 - pHomR / qHomR ≤ (phiHi : ℝ) / 1000000000000
      := by
      have h1 : (785398163398 : ℝ) / 1000000000000 - pHomR / qHomR = (785398163398 * qHomR -
        1000000000000 * pHomR) / (1000000000000 * qHomR) := (by field_simp [hq_pos.ne'])
      have h2 : (phiHi : ℝ) / 1000000000000 = ((phiHi : ℝ) * qHomR) / (1000000000000 * qHomR) :=
        (by field_simp [hq_pos.ne'])
      rw [h1, h2]; exact div_le_div_of_nonneg_right (by linarith [hcast]) (by positivity)
    rw [hrat_eq] at hp56; linarith [hoct, hpi, hp56, hdiv]
/-- Exact rational square lower bound on `tan(arcsin(√((r - 1)/r) * sin(arctan(tc /
  10^5))))`. -/
theorem tan_arcsin_sqrt_ratio_ge {r tc tBfLo : ℕ} (hr2 : 2 ≤ r) (hbf : (r * 10000000000 + tc * tc) *
  tBfLo * tBfLo ≤ (r - 1) * tc * tc * 1000000000000 * 1000000000000) :
    let γ := Real.arcsin (√(((r - 1 : ℕ) : ℝ) / r) * Real.sin (Real.arctan ((tc : ℝ) / 100000)))
    0 ≤ γ ∧ γ < π / 2 ∧ (tBfLo : ℝ) / 1000000000000 ≤ Real.tan γ := by
  intro γ; have hr_pos : (0 : ℝ) < r := Nat.cast_pos.2 (by omega); have hr1_pos : (0 : ℝ) < ((r - 1
    : ℕ) : ℝ) := Nat.cast_pos.2 (by omega); have hr1_sub : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 :=
    (by rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one])
  set t : ℝ := (tc : ℝ) / 100000; have ht_nn : 0 ≤ t := (by positivity); set s : ℝ := √(((r - 1 : ℕ)
    : ℝ) / r) * Real.sin (Real.arctan t); have hsin_atan : Real.sin (Real.arctan t) = t / √(1 + t ^
    2) := Real.sin_arctan t; have hs_nn : 0 ≤ s := (by dsimp only [s]; rw [hsin_atan]; positivity)
  have hs_sq : s ^ 2 = (((r - 1 : ℕ) : ℝ) * (tc : ℝ) ^ 2) / ((r : ℝ) * (10000000000 + (tc : ℝ) ^ 2))
    := by
    dsimp only [s, t]; rw [hsin_atan, mul_pow, Real.sq_sqrt (by positivity), div_pow, Real.sq_sqrt
      (by positivity)]; have hden1 : (0 : ℝ) < 1 + ((tc : ℝ) / 100000) ^ 2 := (by positivity)
    have hden2 : (0 : ℝ) < 10000000000 + (tc : ℝ) ^ 2 := (by positivity); field_simp [hr_pos.ne',
      hden1.ne', hden2.ne']; ring
  have h1_sub_s2 : 1 - s ^ 2 = ((r : ℝ) * 10000000000 + (tc : ℝ) ^ 2) / ((r : ℝ) * (10000000000 +
    (tc : ℝ) ^ 2)) := by
    rw [hs_sq, hr1_sub]; have hden2 : (0 : ℝ) < 10000000000 + (tc : ℝ) ^ 2 := (by positivity)
    field_simp [hr_pos.ne', hden2.ne']; ring
  have hs2_lt1 : s ^ 2 < 1 :=
    (by have hpos : 0 < 1 - s ^ 2 := (by rw [h1_sub_s2]; positivity); linarith)
  have hs_lt1 : s < 1 := (by nlinarith [sq_nonneg s, hs_nn]); have hγ_nn : 0 ≤ γ :=
    Real.arcsin_nonneg.2 hs_nn
  have hγ_lt : γ < π / 2 := Real.arcsin_lt_pi_div_two.2 hs_lt1; refine ⟨hγ_nn, hγ_lt, ?_⟩
  have hsin_γ : Real.sin γ = s := Real.sin_arcsin (by linarith) hs_lt1.le
  have hcos_γ : Real.cos γ = √(1 - s ^ 2) := Real.cos_arcsin s; have hcos_pos : 0 < Real.cos γ :=
    (by rw [hcos_γ]; exact Real.sqrt_pos.2 (by linarith)); have htan_nn : 0 ≤ Real.tan γ :=
    (by rw [Real.tan_eq_sin_div_cos, hsin_γ]; exact div_nonneg hs_nn hcos_pos.le)
  refine sq_le_imp_le (by positivity) htan_nn ?_
  have htan_sq : Real.tan γ ^ 2 = (((r - 1 : ℕ) : ℝ) * (tc : ℝ) ^ 2) / ((r : ℝ) * 10000000000 + (tc
    : ℝ) ^ 2) := by
    rw [Real.tan_eq_sin_div_cos, div_pow, hsin_γ, hcos_γ, Real.sq_sqrt (by linarith), h1_sub_s2,
      hs_sq]; have hden2 : (0 : ℝ) < 10000000000 + (tc : ℝ) ^ 2 := (by positivity); have hden3 : (0
      : ℝ) < (r : ℝ) * 10000000000 + (tc : ℝ) ^ 2 := (by positivity); field_simp [hr_pos.ne',
      hden2.ne', hden3.ne']
  rw [htan_sq, div_pow, div_le_div_iff₀ (by norm_num) (by positivity)]; have hcast : ((r : ℝ) *
    10000000000 + (tc : ℝ) * tc) * tBfLo * tBfLo ≤ ((r - 1 : ℕ) : ℝ) * tc * tc * 1000000000000 *
    1000000000000 := (by exact_mod_cast hbf); linarith [hcast, show (tBfLo : ℝ) ^ 2 * ((r : ℝ) *
    10000000000 + (tc : ℝ) ^ 2) - (1000000000000 : ℝ) ^ 2 * (((r - 1 : ℕ) : ℝ) * (tc : ℝ) ^ 2) = ((r
    : ℝ) * 10000000000 + (tc : ℝ) * tc) * tBfLo * tBfLo - ((r - 1 : ℕ) : ℝ) * tc * tc *
    1000000000000 * 1000000000000 by ring]
/-- Soundness of `checkFuseDriftCert`: bounds both the reset-slot steps `cNat` and unclicked
  coherent-fusion drift steps `uNat` for any post-fusion angle `βFuse ≥ γ`. -/
theorem fuseDriftCert_sound {r tCur tPrev phiHiPrev tBfLo tdHi numU cNat uNat : ℕ} {θp SN βFuse : ℝ}
  (hr2 : 2 ≤ r) (hSN_ge : 1000000000000000 ≤ SN) (hθp_lo : √((r - 1 : ℕ) : ℝ) / SN ≤ θp) (hphi_p :
  Real.arctan ((tPrev : ℝ) / 100000) ≤ (phiHiPrev : ℝ) / 1000000000000) (hβFuse : Real.arcsin (√(((r
  - 1 : ℕ) : ℝ) / r) * Real.sin (Real.arctan ((tCur : ℝ) / 100000))) ≤ βFuse) (hchk :
  checkFuseDriftCert r tCur tPrev phiHiPrev tBfLo tdHi numU cNat uNat = true) : uNat ≤ cNat ∧ 1 +
  (Real.arctan ((tPrev : ℝ) / 100000) - θp) / (2 * θp) ≤ ((cNat : ℝ) / 1000000000000) * SN ∧ 3 + max
  0 ((Real.arctan ((tPrev : ℝ) / 100000) - βFuse) / (2 * θp)) ≤ ((uNat : ℝ) / 1000000000000) * SN :=
  by
  simp only [checkFuseDriftCert, Bool.and_eq_true] at hchk
  have hbf := of_decide_eq_true hchk.1.1.1.1.1.1; have hbranch := hchk.1.1.1.1.1.2; have hc_pos :=
    of_decide_eq_true hchk.1.1.1.1.2; have hc_sq := of_decide_eq_true hchk.1.1.1.2; have hu_pos :=
    of_decide_eq_true hchk.1.1.2; have hu_le_c := of_decide_eq_true hchk.1.2; have hu_sq :=
    of_decide_eq_true hchk.2; set φp : ℝ := Real.arctan ((tPrev : ℝ) / 100000); set γ : ℝ :=
    Real.arcsin (√(((r - 1 : ℕ) : ℝ) / r) * Real.sin (Real.arctan ((tCur : ℝ) / 100000)))
  obtain ⟨hγ_nn, hγ_lt, htan_γ⟩ := tan_arcsin_sqrt_ratio_ge hr2 hbf; have hSN_pos : 0 < SN :=
    lt_of_lt_of_le (by positivity) hSN_ge; have hr1_pos : (0 : ℝ) < ((r - 1 : ℕ) : ℝ) :=
    Nat.cast_pos.2 (by omega)
  have hsr1_pos : (0 : ℝ) < √((r - 1 : ℕ) : ℝ) := Real.sqrt_pos.2 hr1_pos; have hθp_pos : 0 < θp :=
    lt_of_lt_of_le (by positivity) hθp_lo
  have hφp_nn : 0 ≤ φp := Real.arctan_nonneg.2 (by positivity); have hφp_lt : φp < π / 2 :=
    Real.arctan_lt_pi_div_two _
  have hmax_numU : max 0 (φp - γ) ≤ (numU : ℝ) / 1000000000000 := by
    by_cases htp : tPrev * 10000000 ≤ tBfLo
    · rw [ite_eq_left htp, beq_iff_eq] at hbranch
      have htan_p : Real.tan φp ≤ Real.tan γ := by
        dsimp only [φp]; rw [Real.tan_arctan]; have htp_r : (tPrev : ℝ) * 10000000 ≤ tBfLo :=
          (by exact_mod_cast htp); have h1 : (tPrev : ℝ) / 100000 ≤ (tBfLo : ℝ) / 1000000000000 :=
          (by linarith); exact h1.trans htan_γ
      have hφ_le_γ : φp ≤ γ := by
        calc φp = Real.arctan (Real.tan φp) :=
              (Real.arctan_tan (by linarith [Real.pi_pos]) hφp_lt).symm
          _ ≤ Real.arctan (Real.tan γ) := Real.arctan_mono htan_p
          _ = γ := Real.arctan_tan (by linarith [Real.pi_pos]) hγ_lt
      have hmax0 : max 0 (φp - γ) = 0 := max_eq_left (by linarith); rw [hmax0]; positivity
    · rw [ite_eq_right htp, Bool.and_eq_true] at hbranch
      have htd_nat := of_decide_eq_true hbranch.1; have hpade_u := pade54Scale8_sound hbranch.2
      refine max_le (by positivity) ?_; by_cases hle : φp ≤ γ
      · exact (by linarith : φp - γ ≤ 0).trans (by positivity)
      · have hgt_φ : γ < φp := lt_of_not_ge hle; have hdiff_gt : -(π / 2) < φp - γ :=
          (by linarith [Real.pi_pos]); have hdiff_lt : φp - γ < π / 2 := (by linarith)
        have hcφ : 0 < Real.cos φp := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hφp_lt⟩
        have hcγ : 0 < Real.cos γ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hγ_lt⟩
        have hcd : 0 < Real.cos (φp - γ) := Real.cos_pos_of_mem_Ioo ⟨hdiff_gt, hdiff_lt⟩
        have htan_sub : Real.tan (φp - γ) = (Real.tan φp - Real.tan γ) / (1 + Real.tan φp * Real.tan
          γ) := by
          rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos,
            Real.sin_sub, Real.cos_sub]
          have hden_pos : 0 < Real.cos φp * Real.cos γ + Real.sin φp * Real.sin γ :=
            (by linarith [Real.cos_sub φp γ]); field_simp [hcφ.ne', hcγ.ne', hcd.ne', hden_pos.ne']
        have htan_φp : Real.tan φp = (tPrev : ℝ) / 100000 := Real.tan_arctan _; set b : ℝ := (tBfLo
          : ℝ) / 1000000000000; have hb_nn : 0 ≤ b := (by positivity)
        have htan_γ_nn : 0 ≤ Real.tan γ := hb_nn.trans htan_γ
        have hden_t_pos : 0 < 1 + Real.tan φp * Real.tan γ := by
          rw [htan_φp]; exact add_pos_of_pos_of_nonneg one_pos (mul_nonneg (by positivity)
            htan_γ_nn)
        have hnum_le : Real.tan φp - Real.tan γ ≤ (tPrev : ℝ) / 100000 - b :=
          (by rw [htan_φp]; linarith [htan_γ])
        have hden_ge : 1 + ((tPrev : ℝ) / 100000) * b ≤ 1 + Real.tan φp * Real.tan γ := by
          rw [htan_φp]; exact add_le_add_right (mul_le_mul_of_nonneg_left htan_γ (by positivity)) 1
        have hnum_pos : 0 ≤ (tPrev : ℝ) / 100000 - b := by
          dsimp only [b]; have hgt : tBfLo < tPrev * 10000000 := (by omega); have hgt_r : (tBfLo :
            ℝ) ≤ (tPrev : ℝ) * 10000000 := (by exact_mod_cast hgt.le); linarith
        have hrat_le : Real.tan (φp - γ) ≤ ((tPrev : ℝ) / 100000 - b) / (1 + ((tPrev : ℝ) / 100000)
          * b) := by
          rw [htan_sub]; exact (div_le_div_of_nonneg_right hnum_le hden_t_pos.le).trans
            (div_le_div_of_nonneg_left hnum_pos (by positivity) hden_ge)
        have htd_le : ((tPrev : ℝ) / 100000 - b) / (1 + ((tPrev : ℝ) / 100000) * b) ≤ (tdHi : ℝ) /
          100000000 := by
          dsimp only [b]; have hden_b : (0 : ℝ) < 1 + (tPrev : ℝ) / 100000 * ((tBfLo : ℝ) /
            1000000000000) := (by positivity); have hden_i : (0 : ℝ) < 100000000000000000 + (tPrev :
            ℝ) * tBfLo := (by positivity); have heq : ((tPrev : ℝ) / 100000 - (tBfLo : ℝ) /
            1000000000000) / (1 + (tPrev : ℝ) / 100000 * ((tBfLo : ℝ) / 1000000000000)) = (((tPrev :
            ℝ) * 10000000 - tBfLo) * 100000) / (100000000000000000 + (tPrev : ℝ) * tBfLo) :=
            (by field_simp [hden_b.ne', hden_i.ne']; ring); rw [heq, div_le_div_iff₀ hden_i
            (by norm_num)]
          have hsub_nat : ((tPrev * 10000000 - tBfLo : ℕ) : ℝ) = (tPrev : ℝ) * 10000000 - tBfLo
            := by
            have hle_b : tBfLo ≤ tPrev * 10000000 := (by omega); rw [Nat.cast_sub hle_b]; push_cast;
              ring
          have hcast : ((tPrev * 10000000 - tBfLo : ℕ) : ℝ) * 10000000000000 ≤ (tdHi : ℝ) *
            (100000000000000000 + (tPrev : ℝ) * tBfLo) := (by exact_mod_cast htd_nat)
          rw [hsub_nat] at hcast; linarith [hcast]
        calc φp - γ = Real.arctan (Real.tan (φp - γ)) := (Real.arctan_tan hdiff_gt hdiff_lt).symm
          _ ≤ Real.arctan ((tdHi : ℝ) / 100000000) := Real.arctan_mono (hrat_le.trans htd_le)
          _ ≤ (numU : ℝ) / 1000000000000 := hpade_u
  have hc_bound : 1 + (φp - θp) / (2 * θp) ≤ ((cNat : ℝ) / 1000000000000) * SN := by
    have hnum : φp - θp ≤ (phiHiPrev : ℝ) / 1000000000000 := (by linarith [hphi_p, hθp_pos])
    have h1 : (φp - θp) / (2 * θp) ≤ ((phiHiPrev : ℝ) / 1000000000000) / (2 * (√((r - 1 : ℕ) : ℝ) /
      SN)) := (div_le_div_of_nonneg_right hnum (by positivity)).trans (div_le_div_of_nonneg_left
      (by positivity) (by positivity) (by linarith [hθp_lo]))
    have h2 : ((phiHiPrev : ℝ) / 1000000000000) / (2 * (√((r - 1 : ℕ) : ℝ) / SN)) ≤ (((cNat - 1 : ℕ)
      : ℝ) / 1000000000000) * SN := by
      have hrew : ((phiHiPrev : ℝ) / 1000000000000) / (2 * (√((r - 1 : ℕ) : ℝ) / SN)) = ((phiHiPrev
        : ℝ) / (2 * √((r - 1 : ℕ) : ℝ)) / 1000000000000) * SN :=
        (by field_simp [hsr1_pos.ne', hSN_pos.ne']); rw [hrew]
      refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ?_ (by norm_num)) hSN_pos.le
      rw [div_le_iff₀ (by positivity)]; refine sq_le_imp_le (by positivity) (by positivity) ?_
      have hcsq : (phiHiPrev : ℝ) * phiHiPrev ≤ 4 * ((r - 1 : ℕ) : ℝ) * ((cNat - 1 : ℕ) : ℝ) * (cNat
        - 1 : ℕ) := (by exact_mod_cast hc_sq); rw [mul_pow, mul_pow (2 : ℝ), Real.sq_sqrt
        hr1_pos.le]; linarith [hcsq, show (phiHiPrev : ℝ) ^ 2 - ((cNat - 1 : ℕ) : ℝ) ^ 2 * ((2 : ℝ)
        ^ 2 * ((r - 1 : ℕ) : ℝ)) = (phiHiPrev : ℝ) * phiHiPrev - 4 * ((r - 1 : ℕ) : ℝ) * ((cNat - 1
        : ℕ) : ℝ) * (cNat - 1 : ℕ) by ring]
    rw [Nat.cast_sub hc_pos, Nat.cast_one] at h2; have h1_sn : (1 : ℝ) ≤ (1 / 1000000000000) * SN :=
      (by linarith [hSN_ge]); linarith [h1, h2, h1_sn, show (((cNat : ℝ) - 1) / 1000000000000) * SN
      + (1 / 1000000000000) * SN = ((cNat : ℝ) / 1000000000000) * SN by ring]
  have hu_bound : 3 + max 0 ((φp - βFuse) / (2 * θp)) ≤ ((uNat : ℝ) / 1000000000000) * SN := by
    have hmax_div : max 0 ((φp - βFuse) / (2 * θp)) ≤ ((numU : ℝ) / 1000000000000) / (2 * (√((r - 1
      : ℕ) : ℝ) / SN)) := by
      refine max_le (by positivity) ?_
      have hsub : φp - βFuse ≤ (numU : ℝ) / 1000000000000 := by
        have h1 : φp - βFuse ≤ φp - γ := (by linarith [hβFuse]); exact h1.trans ((le_max_right 0 (φp
          - γ)).trans hmax_numU)
      exact (div_le_div_of_nonneg_right hsub (by positivity)).trans (div_le_div_of_nonneg_left
        (by positivity) (by positivity) (by linarith [hθp_lo]))
    have h2 : ((numU : ℝ) / 1000000000000) / (2 * (√((r - 1 : ℕ) : ℝ) / SN)) ≤ (((uNat - 1 : ℕ) : ℝ)
      / 1000000000000) * SN := by
      have hrew : ((numU : ℝ) / 1000000000000) / (2 * (√((r - 1 : ℕ) : ℝ) / SN)) = ((numU : ℝ) / (2
        * √((r - 1 : ℕ) : ℝ)) / 1000000000000) * SN := (by field_simp [hsr1_pos.ne', hSN_pos.ne'])
      rw [hrew]
      refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ?_ (by norm_num)) hSN_pos.le
      rw [div_le_iff₀ (by positivity)]; refine sq_le_imp_le (by positivity) (by positivity) ?_
      have husq : (numU : ℝ) * numU ≤ 4 * ((r - 1 : ℕ) : ℝ) * ((uNat - 1 : ℕ) : ℝ) * (uNat - 1 : ℕ)
        := (by exact_mod_cast hu_sq); rw [mul_pow, mul_pow (2 : ℝ), Real.sq_sqrt hr1_pos.le]
      linarith [husq, show (numU : ℝ) ^ 2 - ((uNat - 1 : ℕ) : ℝ) ^ 2 * ((2 : ℝ) ^ 2 * ((r - 1 : ℕ) :
        ℝ)) = (numU : ℝ) * numU - 4 * ((r - 1 : ℕ) : ℝ) * ((uNat - 1 : ℕ) : ℝ) * (uNat - 1 : ℕ)
        by ring]
    rw [Nat.cast_sub hu_pos, Nat.cast_one] at h2; have h3_sn : (3 : ℝ) ≤ (1 / 1000000000000) * SN :=
      (by linarith [hSN_ge]); linarith [hmax_div, h2, h3_sn, show (((uNat : ℝ) - 1) / 1000000000000)
      * SN + (1 / 1000000000000) * SN = ((uNat : ℝ) / 1000000000000) * SN by ring]
  exact ⟨hu_le_c, hc_bound, hu_bound⟩
theorem clickRow_sound {m n r tn stepNum : ℕ} (hm : 1 ≤ m) (hr1 : 1 ≤ r) (ht : 500 ≤ tn) (hchk :
  checkClickRow m r tn stepNum = true) : 1 / ((m : ℝ) * (4 * ((tn : ℝ) / 100000) * (99999999 /
  100000000) * √(r : ℝ) / √(2 ^ n : ℝ)) * (1 - (m : ℝ) * (1 / (100000000 * (m : ℝ))))) ≤ ((stepNum :
  ℝ) / 1000000000000) * √(2 ^ n : ℝ) := by
  set p_min : ℝ := 4 * ((tn : ℝ) / 100000) * (99999999 / 100000000) * √(r : ℝ) / √(2 ^ n : ℝ)
  set p_max : ℝ := 1 / (100000000 * (m : ℝ)); have hsq_nat := of_decide_eq_true hchk
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.2 hm; have hr_pos : (0 : ℝ) < r := Nat.cast_pos.2 hr1
  have hsr_pos : (0 : ℝ) < √(r : ℝ) := Real.sqrt_pos.2 hr_pos; have ht_pos : (0 : ℝ) < tn :=
    Nat.cast_pos.2 (by omega)
  have hSN_pos : (0 : ℝ) < √(2 ^ n : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hrho : 1 - (m : ℝ) * p_max = 99999999 / 100000000 :=
    (by dsimp only [p_max]; field_simp [hm_pos.ne']; norm_num)
  have hden_ge : ((4 * (m : ℝ) * 99999998 * tn) / (100000 * 100000000)) * (√(r : ℝ) / √(2 ^ n : ℝ))
    ≤ (m : ℝ) * p_min * (1 - (m : ℝ) * p_max) := by
    rw [hrho]; dsimp only [p_min]; have h98 : (99999998 / 100000000 : ℝ) ≤ (99999999 / 100000000) *
      (99999999 / 100000000) := (by norm_num)
    have hfac_nn : 0 ≤ 4 * (m : ℝ) * ((tn : ℝ) / 100000) * (√(r : ℝ) / √(2 ^ n : ℝ)) :=
      (by positivity); have hm_le := mul_le_mul_of_nonneg_left h98 hfac_nn
    linarith [hm_le, show 4 * (m : ℝ) * ((tn : ℝ) / 100000) * (√(r : ℝ) / √(2 ^ n : ℝ)) *
          (99999998 / 100000000) =
        ((4 * (m : ℝ) * 99999998 * tn) / (100000 * 100000000)) *
          (√(r : ℝ) / √(2 ^ n : ℝ)) by ring,
      show 4 * (m : ℝ) * ((tn : ℝ) / 100000) * (√(r : ℝ) / √(2 ^ n : ℝ)) *
          ((99999999 / 100000000) * (99999999 / 100000000)) =
        (m : ℝ) * (4 * ((tn : ℝ) / 100000) * (99999999 / 100000000) * √(r : ℝ) / √(2 ^ n : ℝ)) *
          (99999999 / 100000000) by ring]
  have hlhs_le : 1 / ((m : ℝ) * p_min * (1 - (m : ℝ) * p_max)) ≤ ((100000 * 100000000 : ℝ) / (4 * (m
    : ℝ) * 99999998 * tn * √(r : ℝ))) * √(2 ^ n : ℝ) := by
    have h1 := one_div_le_one_div_of_le (by positivity) hden_ge; refine h1.trans (le_of_eq ?_)
    field_simp [hm_pos.ne', ht_pos.ne', hsr_pos.ne', hSN_pos.ne']
  refine hlhs_le.trans (mul_le_mul_of_nonneg_right ?_ hSN_pos.le); rw [div_le_div_iff₀
    (by positivity) (by norm_num)]; refine sq_le_imp_le (by positivity) (by positivity) ?_
  have hcast : ((100000000 * 100000 * 1000000000000 : ℝ)) * (100000000 * 100000 * 1000000000000) ≤
    (r : ℝ) * (4 * (m : ℝ) * 99999998 * tn * stepNum) * (4 * (m : ℝ) * 99999998 * tn * stepNum) :=
    (by exact_mod_cast hsq_nat)
  have hr_sq : ((stepNum : ℝ) * (4 * (m : ℝ) * 99999998 * tn * √(r : ℝ))) ^ 2 = (r : ℝ) * (4 * (m :
    ℝ) * 99999998 * tn * stepNum) * (4 * (m : ℝ) * 99999998 * tn * stepNum) := by
    calc ((stepNum : ℝ) * (4 * (m : ℝ) * 99999998 * tn * √(r : ℝ))) ^ 2
        = (stepNum : ℝ) ^ 2 * (4 * (m : ℝ) * 99999998 * tn) ^ 2 * (√(r : ℝ)) ^ 2 := by ring
      _ = (stepNum : ℝ) ^ 2 * (4 * (m : ℝ) * 99999998 * tn) ^ 2 * (r : ℝ) := by
            rw [Real.sq_sqrt hr_pos.le]
      _ = (r : ℝ) * (4 * (m : ℝ) * 99999998 * tn * stepNum) *
            (4 * (m : ℝ) * 99999998 * tn * stepNum) := by ring
  rw [hr_sq]; linarith [hcast, show ((100000 * 100000000 : ℝ) * 1000000000000) ^ 2 = (100000000 *
    100000 * 1000000000000 : ℝ) * (100000000 * 100000 * 1000000000000) by ring]
theorem sumIccOne_invSqrtLo_le {cnt : ℕ} (hcnt : cnt ≤ 1024) : (sumIccOne invSqrtLo cnt : ℝ) /
  1000000000000 ≤ ∑ r ∈ Finset.Icc (1 : ℕ) cnt, 1 / √(r : ℝ) := by
  have haux := cert_auxTables; simp only [checkAuxTables, Bool.and_eq_true] at haux; have hinv :=
    haux.1.1
  induction cnt with
  | zero =>
    have hz : Finset.Icc (1 : ℕ) 0 = ∅ := (by ext x; simp)
    rw [hz, Finset.sum_empty]; simp [sumIccOne]
  | succ i ih =>
    have hi1024 : i < 1024 := (by omega); have hprev := ih (by omega)
    have hitem := of_allRange hinv hi1024; simp only [checkInvSqrtItem, withForcedNat_eq] at hitem
    have hsq_nat := of_decide_eq_true hitem
    have hterm : (invSqrtLo (i + 1) : ℝ) / 1000000000000 ≤ 1 / √((i + 1 : ℕ) : ℝ) := by
      have hr_pos : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := (by positivity); have hsr_pos : (0 : ℝ) < √((i +
        1 : ℕ) : ℝ) := Real.sqrt_pos.2 hr_pos; rw [div_le_div_iff₀ (by norm_num) hsr_pos, one_mul]
      refine sq_le_imp_le (by positivity) (by norm_num) ?_; rw [mul_pow, Real.sq_sqrt hr_pos.le]
      have hcast : ((i + 1 : ℕ) : ℝ) * invSqrtLo (i + 1) * invSqrtLo (i + 1) ≤ 1000000000000 *
        1000000000000 := (by exact_mod_cast hsq_nat); linarith [hcast, show (invSqrtLo (i + 1) : ℝ)
        ^ 2 * ((i + 1 : ℕ) : ℝ) - (1000000000000 : ℝ) ^ 2 = ((i + 1 : ℕ) : ℝ) * invSqrtLo (i + 1) *
        invSqrtLo (i + 1) - 1000000000000 * 1000000000000 by ring]
    have hIcc : Finset.Icc (1 : ℕ) (i + 1) = insert (i + 1) (Finset.Icc (1 : ℕ) i) :=
      (by ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega)
    have hnotmem : i + 1 ∉ Finset.Icc (1 : ℕ) i := (by simp); rw [hIcc, Finset.sum_insert hnotmem,
      sumIccOne, withForcedNat_eq, Nat.cast_add, add_div, add_comm]; exact add_le_add hterm hprev
theorem harmSumPow2_le_sum {kIdx : ℕ} (hkIdx : kIdx < 11) : (harmSumPow2 kIdx : ℝ) / 1000000000000 ≤
  ∑ r ∈ Finset.Icc (1 : ℕ) (2 ^ kIdx), 1 / √(r : ℝ) := by
  have haux := cert_auxTables; simp only [checkAuxTables, Bool.and_eq_true] at haux; have hharm :=
    of_allRange haux.1.2 hkIdx; simp only [checkHarmPow2Item, beq_iff_eq] at hharm; rw [hharm]
  have hk1024 : 2 ^ kIdx ≤ 1024 := by
    calc 2 ^ kIdx ≤ 2 ^ 10 := Nat.pow_le_pow_right (by positivity) (by omega)
      _ = 1024 := by norm_num
  exact sumIccOne_invSqrtLo_le hk1024
theorem sqrtMUpNat_bounds {d : ℕ} (hd : d < 11) : 0 < sqrtMUpNat d ∧ (2 ^ d) * 1000000000000 *
  1000000000000 ≤ sqrtMUpNat d * sqrtMUpNat d := by
  have haux := cert_auxTables; simp only [checkAuxTables, Bool.and_eq_true] at haux; have h :=
    of_allRange haux.2 hd; simp only [checkSqrtMItem, withForcedNat_eq, Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩
attribute [irreducible]
  invSqrtLoChunk0 invSqrtLoChunk1 invSqrtLoChunk2 invSqrtLoChunk3
  invSqrtLoChunk4 invSqrtLoChunk5 invSqrtLoChunk6 invSqrtLoChunk7
  invSqrtLoChunk8 invSqrtLoChunk9 invSqrtLoChunk10 invSqrtLoChunk11
  invSqrtLoChunk12 invSqrtLoChunk13 invSqrtLoChunk14 invSqrtLoChunk15
  invSqrtLo harmSumPow2 sqrtMUpNat
end QuantumComputation.Specs.GroverFindAll.PipeFuseCert
