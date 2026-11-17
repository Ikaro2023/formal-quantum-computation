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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.PulseM1MultiPulseQHL
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.PulseM1Grover1Step

/-
# `m = 1` Multi-pulse 39-Stage Arm B Bellman Table & `L = 2` Range Buckets
-/
@[expose] public section
namespace QuantumComputation.Specs.GroverFindAll.GroverM1PulseTable
open Real
open QuantumComputation.Specs.GroverFindAll.SchurWeylLCert (IvInt)
open QuantumComputation.Specs.GroverFindAll.PulseM1
/-- Stage-level Bellman soundness predicate matching `PulseM1CertBundle.hStageSound`. -/
abbrev PulseStageTableProp (n r : ℕ) (s : PulseM1StageSpec) (vTable : ℕ → ℤ) : Prop :=
  ∃ (hL2 : 2 ≤ s.L),
    s.L ≤ 1024 ∧ s.L ≤ r ∧
    s.pulses.all SchurWeylLCert.swLPulseValid = true ∧
    ∀ (M : Fin (2 * s.L) → Fin (2 * s.L) → ℝ),
      SchurWeylLCert.IsValidSwLOverlap M →
      let K_blk := SchurWeylLCert.swLKBlk n r s.tauNum s.tauDen
      let cs : Fin s.L → ℝ × ℝ := fun w ↦
        (Real.cos ((K_blk : ℝ) * SchurWeylLCert.swLThetaShiftReal (2 ^ n) r w.1),
         Real.sin ((K_blk : ℝ) * SchurWeylLCert.swLThetaShiftReal (2 ^ n) r w.1))
      let out := SchurWeylLCert.swLEvolutionReal s.L hL2 cs s.pulses
      let p : ℕ → ℝ := SchurWeylLCert.swLAttemptProbReal s.L hL2 M out.1 out.2.1
      let pSucc : ℝ := ∑ h ∈ Finset.Icc 1 s.L, p h
      let V : ℕ → ℝ := fun j ↦
        ((vTable j : ℝ) / (SchurWeylLCert.multiUnitScale : ℝ)) * √(2 ^ n : ℝ)
      0 < pSucc ∧
      (out.2.2 * (K_blk : ℝ) + (s.L : ℝ) +
        ∑ h ∈ Finset.Icc 1 s.L, p h * V (r - h)) / pSucc ≤ V r
/-- First-argument structural `Nat` walk checking `p (lo + j) = true` for `0 ≤ j < len`. -/
def solAllBelow : ℕ → ℕ → (ℕ → Bool) → Bool
  | 0, _, _ => true
  | k + 1, lo, p => p lo && solAllBelow k (Nat.add lo 1) p
theorem solAllBelow_true : ∀ {len lo : ℕ} {p : ℕ → Bool}, solAllBelow len lo p = true → ∀ r : ℕ, lo
  ≤ r → r < lo + len → p r = true
  | 0, _, _, _, _, _hlo, _hhi => by omega
  | k + 1, lo, p, h, r, _hlo, _hhi => by
    simp only [solAllBelow, Bool.and_eq_true] at h; by_cases heq : r = lo
    · subst heq; exact h.1
    · have h2 : solAllBelow k (lo + 1) p = true := (by rw [← solNatAdd_eq]; exact h.2)
      exact solAllBelow_true h2 r (by omega) (by omega)
/-- Prefix-maximum reverse walk `[env (idx + fuel - 1),..., env idx]` in `O(fuel)` steps. -/
def solEnvRevWalk (vTable : ℕ → ℤ) : ℕ → ℕ → ℤ → List ℤ → List ℤ
  | 0, _, _, acc => acc
  | fuel + 1, idx, curMax, acc =>
      solSeqInt (vTable idx) fun v ↦
        solSeqInt (cond (solBleZ curMax v) v curMax) fun nextMax ↦
          solEnvRevWalk vTable fuel (Nat.add idx 1) nextMax (nextMax :: acc)
/-- Monotone upper-envelope `vPrevs` list `[env (r - 1),..., env (r - L)]` of length `L`. -/
def solEnvPrevs (L r : ℕ) (vTable : ℕ → ℤ) : List ℤ := (solEnvRevWalk vTable r 0 0 []).take L
theorem solVPrevsDomWalk_range' (r : ℕ) (vTable : ℕ → ℤ) : ∀ (k w : ℕ), solVPrevsDomWalk r vTable w
  ((List.range' w k).map fun u ↦ vTable (Nat.sub r (Nat.add u 1))) = true
  | 0, _ => rfl
  | k + 1, w => by
    simp only [List.range'_succ, List.map_cons, solVPrevsDomWalk, Bool.and_eq_true]
    refine ⟨by rw [solBleZ_eq_decide, decide_eq_true_eq], ?_⟩
    rw [solNatAdd_eq]; exact solVPrevsDomWalk_range' r vTable k (w + 1)
theorem checkPulseVTableDom_table (L r : ℕ) (vTable : ℕ → ℤ) : checkPulseVTableDom L r vTable
  (vTable r) ((List.range L).map fun w ↦ vTable (Nat.sub r (Nat.add w 1))) = true := by
  unfold checkPulseVTableDom; simp only [Bool.and_eq_true, Nat.beq_eq, solBleZ_eq_decide,
    decide_eq_true_eq, List.length_map, List.length_range]; refine ⟨⟨True.intro, le_rfl⟩, ?_⟩
  rw [List.range_eq_range']; exact solVPrevsDomWalk_range' r vTable L 0
theorem solWkbRunPrefix_step_eq {q : SolWkbSched} {trigIvs : List (IvInt × IvInt)} {t len tNext : ℕ}
  {cIn : List ℤ} {hIn rhoIn : ℕ} {survIn : ℤ} {cOut : List ℤ} {hOut rhoOut : ℕ} {survOut : ℤ} (ht :
  t + len = tNext) (hprev : SolWkbRunPrefix q trigIvs t cIn hIn rhoIn survIn) (hslice :
  checkPulseWkbSlice q t len trigIvs cIn hIn rhoIn survIn cOut hOut rhoOut survOut = true) :
  SolWkbRunPrefix q trigIvs tNext cOut hOut rhoOut survOut := ht ▸ solWkbRunPrefix_step hprev hslice
/-- Single-stage explicit `L2Ball` + Bellman check against `vTable`. -/
def checkPulseExplicitStageTable (L r tauNum tauDen uvDen : ℕ)
    (ratios : List IvInt) (trigIvs : List (IvInt × IvInt))
    (sps : List SolSparsePulse) (p0Lb : ℤ) (tailLbs : List ℤ) (survUb : ℤ)
    (vTable : ℕ → ℤ) : Bool :=
  checkPulseBucketCertL2 L r r tauNum tauDen uvDen ratios trigIvs sps
    p0Lb tailLbs survUb &&
  checkPulseCascadeStepTable L r tauNum tauDen survUb p0Lb tailLbs vTable
/-- Range-bucket `L = 2` `L2Ball` + `solAllBelow` Bellman check against `vTable`. -/
def checkPulseL2RangeBucketTable (rMin rMax len tauNum tauDen uvDen : ℕ)
    (ratios : List IvInt) (trigIvs : List (IvInt × IvInt))
    (sps : List SolSparsePulse) (p0Lb : ℤ) (tailLbs : List ℤ) (survUb : ℤ)
    (vTable : ℕ → ℤ) : Bool :=
  checkPulseBucketCertL2 2 rMin rMax tauNum tauDen uvDen ratios trigIvs sps
    p0Lb tailLbs survUb &&
  solAllBelow len rMin (fun r ↦
    checkPulseCascadeStepTable 2 r tauNum tauDen survUb p0Lb tailLbs vTable)
/-- Terminal WKB `O(L)` angle + Parseval + direct-`vTable` Bellman check. -/
def checkPulseWkbTerminalTable (r : ℕ) (q : SolWkbSched)
    (ratios : List IvInt) (trigIvs : List (IvInt × IvInt))
    (cEnd : List ℤ) (rhoEnd : ℕ) (survEnd : ℤ)
    (certP0Lb : ℤ) (certTailLbs : List ℤ) (certSurvUb : ℤ)
    (vTable : ℕ → ℤ) : Bool :=
  checkPulseWkbTerminal r r q ratios trigIvs cEnd rhoEnd survEnd
    certP0Lb certTailLbs certSurvUb &&
  checkPulseCascadeStepTable q.L r q.tauNum q.tauDen certSurvUb certP0Lb
    certTailLbs vTable
/-- Terminal WKB `O(L)` angle + Parseval + monotone-envelope Bellman check (`r = 64`). -/
def checkPulseWkbTerminalEnv (r : ℕ) (q : SolWkbSched)
    (ratios : List IvInt) (trigIvs : List (IvInt × IvInt))
    (cEnd : List ℤ) (rhoEnd : ℕ) (survEnd : ℤ)
    (certP0Lb : ℤ) (certTailLbs : List ℤ) (certSurvUb : ℤ)
    (vTable : ℕ → ℤ) : Bool :=
  checkPulseWkbTerminal r r q ratios trigIvs cEnd rhoEnd survEnd
    certP0Lb certTailLbs certSurvUb &&
  checkPulseCascadeStep q.L r q.tauNum q.tauDen certSurvUb certP0Lb
    certTailLbs (vTable r) (solEnvPrevs q.L r vTable) &&
  checkPulseVTableDom q.L r vTable (vTable r) (solEnvPrevs q.L r vTable)
theorem checkPulseStageTable_sound {L n r rMin rMax tauNum tauDen uvDen : ℕ} {ratios : List IvInt}
  {trigIvs : List (IvInt × IvInt)} {sps : List SolSparsePulse} {p0Lb : ℤ} {tailLbs : List ℤ} {survUb
  : ℤ} {vTable : ℕ → ℤ} (hn96 : 96 ≤ n) (hmin : rMin ≤ r) (hmax : r ≤ rMax) (hbkt :
  checkPulseBucketCertL2 L rMin rMax tauNum tauDen uvDen ratios trigIvs sps p0Lb tailLbs survUb =
  true) (hstep : checkPulseCascadeStepTable L r tauNum tauDen survUb p0Lb tailLbs vTable = true) :
  PulseStageTableProp n r ⟨L, tauNum, tauDen, solToSwLPulses L uvDen sps⟩ vTable :=
  checkPulseCascadeStage_sound hn96 hmin hmax hbkt hstep (checkPulseVTableDom_table L r vTable)
theorem checkPulseExplicitStageTable_sound {L n r tauNum tauDen uvDen : ℕ} {ratios : List IvInt}
  {trigIvs : List (IvInt × IvInt)} {sps : List SolSparsePulse} {p0Lb : ℤ} {tailLbs : List ℤ} {survUb
  : ℤ} {vTable : ℕ → ℤ} (hn96 : 96 ≤ n) (hchk : checkPulseExplicitStageTable L r tauNum tauDen
  uvDen ratios trigIvs sps p0Lb tailLbs survUb vTable = true) : PulseStageTableProp n r ⟨L,
  tauNum, tauDen, solToSwLPulses L uvDen sps⟩ vTable := by
  unfold checkPulseExplicitStageTable at hchk; rw [Bool.and_eq_true] at hchk
  exact checkPulseStageTable_sound hn96 le_rfl le_rfl hchk.1 hchk.2
theorem checkPulseL2RangeBucketTable_sound {n r rMin rMax len tauNum tauDen uvDen : ℕ} {ratios :
  List IvInt} {trigIvs : List (IvInt × IvInt)} {sps : List SolSparsePulse} {p0Lb : ℤ} {tailLbs :
  List ℤ} {survUb : ℤ} {vTable : ℕ → ℤ} (hn96 : 96 ≤ n) (hmin : rMin ≤ r) (hmax : r ≤ rMax) (hlt : r
  < rMin + len) (hchk : checkPulseL2RangeBucketTable rMin rMax len tauNum tauDen uvDen ratios
  trigIvs sps p0Lb tailLbs survUb vTable = true) : PulseStageTableProp n r ⟨2, tauNum, tauDen,
  solToSwLPulses 2 uvDen sps⟩ vTable := by
  unfold checkPulseL2RangeBucketTable at hchk; rw [Bool.and_eq_true] at hchk
  exact checkPulseStageTable_sound hn96 hmin hmax hchk.1 (solAllBelow_true hchk.2 r hmin hlt)
theorem checkPulseWkbTerminalTable_sound {n r : ℕ} {q : SolWkbSched} {ratios : List IvInt}
  {trigIvs : List (IvInt × IvInt)} {cEnd : List ℤ} {hEnd rhoEnd : ℕ} {survEnd : ℤ} {p0Lb : ℤ}
  {tailLbs : List ℤ} {survUb : ℤ} {vTable : ℕ → ℤ} (hn96 : 96 ≤ n) (hrun : SolWkbRunPrefix q trigIvs
  q.K cEnd hEnd rhoEnd survEnd) (hterm : checkPulseWkbTerminalTable r q ratios trigIvs cEnd rhoEnd
  survEnd p0Lb tailLbs survUb vTable = true) : PulseStageTableProp n r ⟨q.L, q.tauNum, q.tauDen,
  solWkbToSwLPulses q⟩ vTable := by
  unfold checkPulseWkbTerminalTable at hterm; rw [Bool.and_eq_true] at hterm
  exact checkPulseStageTable_sound hn96 le_rfl le_rfl (checkPulseWkbBucketCertL2_of_runPrefix
    hrun hterm.1) hterm.2
theorem checkPulseWkbTerminalEnv_sound {n r : ℕ} {q : SolWkbSched} {ratios : List IvInt} {trigIvs
  : List (IvInt × IvInt)} {cEnd : List ℤ} {hEnd rhoEnd : ℕ} {survEnd : ℤ} {p0Lb : ℤ} {tailLbs : List
  ℤ} {survUb : ℤ} {vTable : ℕ → ℤ} (hn96 : 96 ≤ n) (hrun : SolWkbRunPrefix q trigIvs q.K cEnd hEnd
  rhoEnd survEnd) (hterm : checkPulseWkbTerminalEnv r q ratios trigIvs cEnd rhoEnd survEnd p0Lb
  tailLbs survUb vTable = true) : PulseStageTableProp n r ⟨q.L, q.tauNum, q.tauDen,
  solWkbToSwLPulses q⟩ vTable := by
  unfold checkPulseWkbTerminalEnv at hterm; rw [Bool.and_eq_true, Bool.and_eq_true] at hterm
  exact checkPulseWkbCascadeStage_sound hn96 le_rfl le_rfl
    (checkPulseWkbBucketCertL2_of_runPrefix hrun hterm.1.1) hterm.1.2 hterm.2
/-- Tier-2 Bellman block 0 (`0 ≤ r ≤ 63`) at `10^16` scale. -/
def solM1VTblB0 (r : ℕ) : ℤ :=
  cond (Nat.ble r 31) (cond (Nat.ble r 15) (cond (Nat.ble r 7) (cond (Nat.ble r 3) (cond
  (Nat.ble r 1) (cond (Nat.ble r 0) 0 6426990820000000) (cond (Nat.ble r 2)
  10187328428426061 13175508012640705)) (cond (Nat.ble r 5) (cond (Nat.ble r 4)
  15740156417043251 18024060448081190) (cond (Nat.ble r 6) 20103837702830080
  22026988737800588))) (cond (Nat.ble r 11) (cond (Nat.ble r 9) (cond (Nat.ble r 8)
  23825313375424955 25521304221747159) (cond (Nat.ble r 10) 27131481315976220
  28668413151197577)) (cond (Nat.ble r 13) (cond (Nat.ble r 12) 30141902465823300
  31559860202215743) (cond (Nat.ble r 14) 32928748775102470 34253982373180853)))) (cond
  (Nat.ble r 23) (cond (Nat.ble r 19) (cond (Nat.ble r 17) (cond (Nat.ble r 16)
  35540146164648222 37704432149503034) (cond (Nat.ble r 18) 38917342186724467
  40968134476063401)) (cond (Nat.ble r 21) (cond (Nat.ble r 20) 42121167975336284
  44079462353919063) (cond (Nat.ble r 22) 45183604486971373 47052503885060042))) (cond
  (Nat.ble r 27) (cond (Nat.ble r 25) (cond (Nat.ble r 24) 48115500210264993
  49904252411940573) (cond (Nat.ble r 26) 50936874423500198 52652585201437431)) (cond
  (Nat.ble r 29) (cond (Nat.ble r 28) 53655394650382462 55304635685826095) (cond (Nat.ble r
  30) 56281501747697659 57869905002076330))))) (cond (Nat.ble r 47) (cond (Nat.ble r 39)
  (cond (Nat.ble r 35) (cond (Nat.ble r 33) (cond (Nat.ble r 32) 52584678373846368
  53951881263715276) (cond (Nat.ble r 34) 55056447398268447 56381095809731332)) (cond
  (Nat.ble r 37) (cond (Nat.ble r 36) 57458459094672623 58743832014112188) (cond (Nat.ble r
  38) 59796292138009153 61045276682949175))) (cond (Nat.ble r 43) (cond (Nat.ble r 41) (cond
  (Nat.ble r 40) 62074819431082964 63289975173178387) (cond (Nat.ble r 42) 64298327155329716
  65481937177367689)) (cond (Nat.ble r 45) (cond (Nat.ble r 44) 66470609178435707
  67624721094040171) (cond (Nat.ble r 46) 68597764929671815 69724148245775206)))) (cond
  (Nat.ble r 55) (cond (Nat.ble r 51) (cond (Nat.ble r 49) (cond (Nat.ble r 48)
  70680032284385760 71780369295475814) (cond (Nat.ble r 50) 72720132272503375
  73795951940305452)) (cond (Nat.ble r 53) (cond (Nat.ble r 52) 74720521981169403
  75773218936412111) (cond (Nat.ble r 54) 76683429067569936 77714279606114188))) (cond
  (Nat.ble r 59) (cond (Nat.ble r 57) (cond (Nat.ble r 56) 78610880675526246
  79621056321160198) (cond (Nat.ble r 58) 80504727826746960 81495306907396846)) (cond
  (Nat.ble r 61) (cond (Nat.ble r 60) 82366666123543353 83338643712932144) (cond (Nat.ble r
  62) 84198253422853931 85152549927438961)))))
/-- Tier-2 Bellman block 1 (`64 ≤ r ≤ 127`) at `10^16` scale. -/
def solM1VTblB1 (r : ℕ) : ℤ :=
  cond (Nat.ble r 95) (cond (Nat.ble r 79) (cond (Nat.ble r 71) (cond (Nat.ble r 67) (cond
  (Nat.ble r 65) (cond (Nat.ble r 64) 76246191345252473 77220358004025149) (cond (Nat.ble r
  66) 78024166879819201 78980099186306499)) (cond (Nat.ble r 69) (cond (Nat.ble r 68)
  79775685972489587 80714255247564416) (cond (Nat.ble r 70) 81501893265863747
  82423912700752334))) (cond (Nat.ble r 75) (cond (Nat.ble r 73) (cond (Nat.ble r 72)
  83203853432822804 84110083028190001) (cond (Nat.ble r 74) 84882558775779073
  85773709750746120)) (cond (Nat.ble r 77) (cond (Nat.ble r 76) 86538935921672871
  87415674663369541) (cond (Nat.ble r 78) 88173851740946428 89036803353964857)))) (cond
  (Nat.ble r 87) (cond (Nat.ble r 83) (cond (Nat.ble r 81) (cond (Nat.ble r 80)
  89788118597761781 90637870103697865) (cond (Nat.ble r 82) 91382499021624715
  92219602251346076)) (cond (Nat.ble r 85) (cond (Nat.ble r 84) 92957709876544946
  93782684091586982) (cond (Nat.ble r 86) 94514426092292692 95327760366601765))) (cond
  (Nat.ble r 91) (cond (Nat.ble r 89) (cond (Nat.ble r 88) 96053284012725118
  96855439401640431) (cond (Nat.ble r 90) 97574884408176090 98366295927910821)) (cond
  (Nat.ble r 93) (cond (Nat.ble r 92) 99079795192230665 99860873630052300) (cond (Nat.ble r
  94) 100568553877603952 101339687450322497))))) (cond (Nat.ble r 111) (cond (Nat.ble r 103)
  (cond (Nat.ble r 99) (cond (Nat.ble r 97) (cond (Nat.ble r 96) 102040912587152644
  102802412472566104) (cond (Nat.ble r 98) 103498116824529492 104250336199048845)) (cond
  (Nat.ble r 101) (cond (Nat.ble r 100) 104940625453614029 105683898662416601) (cond
  (Nat.ble r 102) 106368874688852040 107103518470164122))) (cond (Nat.ble r 107) (cond
  (Nat.ble r 105) (cond (Nat.ble r 104) 107783279625694675 108509594241461667) (cond
  (Nat.ble r 106) 109184235640800367 109902505922219276)) (cond (Nat.ble r 109) (cond
  (Nat.ble r 108) 110572119675293534 111282615990768396) (cond (Nat.ble r 110)
  111947291412798406 112650270565081100)))) (cond (Nat.ble r 119) (cond (Nat.ble r 115)
  (cond (Nat.ble r 113) (cond (Nat.ble r 112) 113310094362602488 114005800421182479) (cond
  (Nat.ble r 114) 114660856857120375 115349521931313060)) (cond (Nat.ble r 117) (cond
  (Nat.ble r 116) 115999892971798448 116681737929441022) (cond (Nat.ble r 118)
  117327503374702161 118002738510888238))) (cond (Nat.ble r 123) (cond (Nat.ble r 121) (cond
  (Nat.ble r 120) 118643976112241464 119312801772102651) (cond (Nat.ble r 122)
  119949587336800721 120612194495967653)) (cond (Nat.ble r 125) (cond (Nat.ble r 124)
  121244601981433849 121901172787474803) (cond (Nat.ble r 126) 122529274386252081
  123179982664088883)))))
/-- Tier-2 Bellman block 2 (`128 ≤ r ≤ 191`) at `10^16` scale. -/
def solM1VTblB2 (r : ℕ) : ℤ :=
  cond (Nat.ble r 159) (cond (Nat.ble r 143) (cond (Nat.ble r 135) (cond (Nat.ble r 131)
  (cond (Nat.ble r 129) (cond (Nat.ble r 128) 110428173702809821 111119678327255833) (cond
  (Nat.ble r 130) 111695390424595287 112378547511161059)) (cond (Nat.ble r 133) (cond
  (Nat.ble r 132) 112952874786938605 113628007269483267) (cond (Nat.ble r 134)
  114200849688184185 114868263431089003))) (cond (Nat.ble r 139) (cond (Nat.ble r 137) (cond
  (Nat.ble r 136) 115439529641919262 116099514440447336) (cond (Nat.ble r 138)
  116669121207915964 117321951726826134)) (cond (Nat.ble r 141) (cond (Nat.ble r 140)
  117889823395355856 118535760049761842) (cond (Nat.ble r 142) 119101828040466766
  119741117822658080)))) (cond (Nat.ble r 151) (cond (Nat.ble r 147) (cond (Nat.ble r 145)
  (cond (Nat.ble r 144) 120305320160511421 120938197416198878) (cond (Nat.ble r 146)
  121500478285896551 122127165443110438)) (cond (Nat.ble r 149) (cond (Nat.ble r 148)
  122687474772017416 123308183025668951) (cond (Nat.ble r 150) 123866476092314212
  124481406047229399))) (cond (Nat.ble r 155) (cond (Nat.ble r 153) (cond (Nat.ble r 152)
  125037643113891894 125646985388939913) (cond (Nat.ble r 154) 126201131356942041
  126805067152706747)) (cond (Nat.ble r 157) (cond (Nat.ble r 156) 127357091239103257
  127955792871385120) (cond (Nat.ble r 158) 128505668305804056 129099299707089967))))) (cond
  (Nat.ble r 175) (cond (Nat.ble r 167) (cond (Nat.ble r 163) (cond (Nat.ble r 161) (cond
  (Nat.ble r 160) 129647003447548205 130235720638447160) (cond (Nat.ble r 162)
  130781233105026258 131365184637539132)) (cond (Nat.ble r 165) (cond (Nat.ble r 164)
  131908489462867614 132487816837238418) (cond (Nat.ble r 166) 133028900632784288
  133603738689567701))) (cond (Nat.ble r 171) (cond (Nat.ble r 169) (cond (Nat.ble r 168)
  134142590826799982 134713068115675006) (cond (Nat.ble r 170) 135249680521205482
  135815919647967205)) (cond (Nat.ble r 173) (cond (Nat.ble r 172) 136350286611833374
  136912404564903525) (cond (Nat.ble r 174) 137444522561201127 138002631018912913)))) (cond
  (Nat.ble r 183) (cond (Nat.ble r 179) (cond (Nat.ble r 177) (cond (Nat.ble r 176)
  138532498538031369 139086704157864520) (cond (Nat.ble r 178) 139614321549621283
  140164726240488952)) (cond (Nat.ble r 181) (cond (Nat.ble r 180) 140690095567499221
  141236796746118970) (cond (Nat.ble r 182) 141759921646775534 142303012479091789))) (cond
  (Nat.ble r 187) (cond (Nat.ble r 185) (cond (Nat.ble r 184) 142823898039566051
  143363467668130758) (cond (Nat.ble r 186) 143882120302840328 144418254061001872)) (cond
  (Nat.ble r 189) (cond (Nat.ble r 188) 144934681401022571 145467461014719987) (cond
  (Nat.ble r 190) 145981671803650808 146510854370861765)))))
/-- Tier-2 Bellman block 3 (`192 ≤ r ≤ 255`) at `10^16` scale. -/
def solM1VTblB3 (r : ℕ) : ℤ :=
  cond (Nat.ble r 223) (cond (Nat.ble r 207) (cond (Nat.ble r 199) (cond (Nat.ble r 195)
  (cond (Nat.ble r 193) (cond (Nat.ble r 192) 147022854081780931 147548841841604242) (cond
  (Nat.ble r 194) 148058641165727518 148581506077662861)) (cond (Nat.ble r 197) (cond
  (Nat.ble r 196) 149089116563601892 149608927661935285) (cond (Nat.ble r 198)
  150114361634880656 150631185180843091))) (cond (Nat.ble r 203) (cond (Nat.ble r 201) (cond
  (Nat.ble r 200) 151134455667344859 151648355292532557) (cond (Nat.ble r 202)
  152149475950521926 152660512792103530)) (cond (Nat.ble r 205) (cond (Nat.ble r 204)
  153159497845821039 153667730674024589) (cond (Nat.ble r 206) 154164594853540640
  154670080191882750)))) (cond (Nat.ble r 215) (cond (Nat.ble r 211) (cond (Nat.ble r 209)
  (cond (Nat.ble r 208) 155164838676915531 155667630915606678) (cond (Nat.ble r 210)
  156160299283360659 156660450786293821)) (cond (Nat.ble r 213) (cond (Nat.ble r 212)
  157151044963059036 157648606168763874) (cond (Nat.ble r 214) 158137142385032232
  158632161901953590))) (cond (Nat.ble r 219) (cond (Nat.ble r 217) (cond (Nat.ble r 216)
  159118656650823537 159611181347261057) (cond (Nat.ble r 218) 160095651345916082
  160585726434941144)) (cond (Nat.ble r 221) (cond (Nat.ble r 220) 161068188589000961
  161555857708647842) (cond (Nat.ble r 222) 162036329079203598 162521634368213661))))) (cond
  (Nat.ble r 239) (cond (Nat.ble r 231) (cond (Nat.ble r 227) (cond (Nat.ble r 225) (cond
  (Nat.ble r 224) 163000132141370306 163483114310751053) (cond (Nat.ble r 226)
  163959655769511059 164440354170155971)) (cond (Nat.ble r 229) (cond (Nat.ble r 228)
  164914956668488997 165393409355089155) (cond (Nat.ble r 230) 165866090294042011
  166342334085506504))) (cond (Nat.ble r 235) (cond (Nat.ble r 233) (cond (Nat.ble r 232)
  166813110891216946 167287181427805934) (cond (Nat.ble r 234) 167756071531292427
  168228003328654409)) (cond (Nat.ble r 237) (cond (Nat.ble r 236) 168695024147262095
  169164850647555384) (cond (Nat.ble r 238) 169630019567946076 170097773188213630)))) (cond
  (Nat.ble r 247) (cond (Nat.ble r 243) (cond (Nat.ble r 241) (cond (Nat.ble r 240)
  170561107550794784 171026819728751372) (cond (Nat.ble r 242) 171488336813445683
  171952038050826817)) (cond (Nat.ble r 245) (cond (Nat.ble r 244) 172411755064090359
  172873474967703457) (cond (Nat.ble r 246) 173331409030706185 173791176351316020))) (cond
  (Nat.ble r 251) (cond (Nat.ble r 249) (cond (Nat.ble r 248) 174247344489203976
  174705187158376574) (cond (Nat.ble r 250) 175159606290540326 175615551455562054)) (cond
  (Nat.ble r 253) (cond (Nat.ble r 252) 176068238386840758 176522312443822395) (cond
  (Nat.ble r 254) 176973283856577448 177425512481846486)))))
/-- Tier-2 Bellman block 4 (`256 ≤ r ≤ 319`) at `10^16` scale. -/
def solM1VTblB4 (r : ℕ) : ℤ :=
  cond (Nat.ble r 287) (cond (Nat.ble r 271) (cond (Nat.ble r 263) (cond (Nat.ble r 259)
  (cond (Nat.ble r 257) (cond (Nat.ble r 256) 158474578023221618 158964496017564339) (cond
  (Nat.ble r 258) 159374182797329776 159859875973070655)) (cond (Nat.ble r 261) (cond
  (Nat.ble r 260) 160270247586299308 160751889555498654) (cond (Nat.ble r 262)
  161162816926701696 161640571435421459))) (cond (Nat.ble r 267) (cond (Nat.ble r 265) (cond
  (Nat.ble r 264) 162051934303911603 162525955827928827) (cond (Nat.ble r 266)
  162937642190346823 163408076494369420)) (cond (Nat.ble r 269) (cond (Nat.ble r 268)
  163819982081905598 164286966744536726) (cond (Nat.ble r 270) 164698994532698603
  165162659439257431)))) (cond (Nat.ble r 279) (cond (Nat.ble r 275) (cond (Nat.ble r 273)
  (cond (Nat.ble r 272) 165574719188167284 166035186993343982) (cond (Nat.ble r 274)
  166447194816674921 166904581378875787)) (cond (Nat.ble r 277) (cond (Nat.ble r 276)
  167316459339651836 167770874128776067) (cond (Nat.ble r 278) 168182549860371477
  168634096340653743))) (cond (Nat.ble r 283) (cond (Nat.ble r 281) (cond (Nat.ble r 280)
  169045502691429722 169494278680881980) (cond (Nat.ble r 282) 169905353380995609
  170351451388887083)) (cond (Nat.ble r 285) (cond (Nat.ble r 284) 170762136737897813
  171205644281623392) (cond (Nat.ble r 286) 171615886855607535 172056886758211632))))) (cond
  (Nat.ble r 303) (cond (Nat.ble r 295) (cond (Nat.ble r 291) (cond (Nat.ble r 289) (cond
  (Nat.ble r 288) 172466637135175037 172905207804719871) (cond (Nat.ble r 290)
  173314420307173810 173750635999067821)) (cond (Nat.ble r 293) (cond (Nat.ble r 292)
  174159268452703333 174593199516036701) (cond (Nat.ble r 294) 175001213023498507
  175432926132368236))) (cond (Nat.ble r 299) (cond (Nat.ble r 297) (cond (Nat.ble r 296)
  175840284861191159 176269843231937683) (cond (Nat.ble r 298) 176676514215766485
  177103977810986942)) (cond (Nat.ble r 301) (cond (Nat.ble r 300) 177509930763254891
  177935356483404945) (cond (Nat.ble r 302) 178340563622697471 178764005486043546)))) (cond
  (Nat.ble r 311) (cond (Nat.ble r 307) (cond (Nat.ble r 305) (cond (Nat.ble r 304)
  179168441372421224 179589950684058109) (cond (Nat.ble r 306) 179993592065658145
  180413217576262894)) (cond (Nat.ble r 309) (cond (Nat.ble r 308) 180816043245540418
  181233831300492172) (cond (Nat.ble r 310) 181635821959502205 182051816638958789))) (cond
  (Nat.ble r 315) (cond (Nat.ble r 313) (cond (Nat.ble r 312) 182452954773116839
  182867198023602623) (cond (Nat.ble r 314) 183267467783396673 183679999541422054)) (cond
  (Nat.ble r 317) (cond (Nat.ble r 316) 184079386631581353 184490244939782190) (cond
  (Nat.ble r 318) 184888736515438903 185297957631694180)))))
/-- Tier-2 Bellman block 5 (`320 ≤ r ≤ 383`) at `10^16` scale. -/
def solM1VTblB5 (r : ℕ) : ℤ :=
  cond (Nat.ble r 351) (cond (Nat.ble r 335) (cond (Nat.ble r 327) (cond (Nat.ble r 323)
  (cond (Nat.ble r 321) (cond (Nat.ble r 320) 185695542201102684 186103160701060488) (cond
  (Nat.ble r 322) 186499828034466063 186905876907881495)) (cond (Nat.ble r 325) (cond
  (Nat.ble r 324) 187301617952155461 187706128693419272) (cond (Nat.ble r 326)
  188100935492101350 188503938185314790))) (cond (Nat.ble r 331) (cond (Nat.ble r 329) (cond
  (Nat.ble r 328) 188897803803725729 189299327202655242) (cond (Nat.ble r 330)
  189692245657763639 190092317260988515)) (cond (Nat.ble r 333) (cond (Nat.ble r 332)
  190484283455735351 190882929577282191) (cond (Nat.ble r 334) 191273939239084990
  191671185074824787)))) (cond (Nat.ble r 343) (cond (Nat.ble r 339) (cond (Nat.ble r 337)
  (cond (Nat.ble r 336) 192061234698000546 192457104388067218) (cond (Nat.ble r 338)
  192846191179929435 193240707867402747)) (cond (Nat.ble r 341) (cond (Nat.ble r 340)
  193628829697803059 194022015583883940) (cond (Nat.ble r 342) 194409170937983109
  194801047333875362))) (cond (Nat.ble r 347) (cond (Nat.ble r 345) (cond (Nat.ble r 344)
  195187235267941710 195577822643640971) (cond (Nat.ble r 346) 195963042743686900
  196352360773865358)) (cond (Nat.ble r 349) (cond (Nat.ble r 348) 196736613116944337
  197124680724108160) (cond (Nat.ble r 350) 197507965842105593 197894801237191135))))) (cond
  (Nat.ble r 367) (cond (Nat.ble r 359) (cond (Nat.ble r 355) (cond (Nat.ble r 353) (cond
  (Nat.ble r 352) 198277120082952874 198662740803517549) (cond (Nat.ble r 354)
  199044094719169507 199428517665323642)) (cond (Nat.ble r 357) (cond (Nat.ble r 356)
  199808908352645081 200192149820862092) (cond (Nat.ble r 358) 200571579313583687
  200953655028517491))) (cond (Nat.ble r 363) (cond (Nat.ble r 361) (cond (Nat.ble r 360)
  201332125666423285 201713050810853955) (cond (Nat.ble r 362) 202090565215573849
  202470354458595097)) (cond (Nat.ble r 365) (cond (Nat.ble r 364) 202846915510981546
  203225583034536665) (cond (Nat.ble r 366) 203601193853525877 203978753377392228)))) (cond
  (Nat.ble r 375) (cond (Nat.ble r 371) (cond (Nat.ble r 369) (cond (Nat.ble r 368)
  204353417300256371 204729882105572374) (cond (Nat.ble r 370) 205103602669475099
  205478985620897930)) (cond (Nat.ble r 373) (cond (Nat.ble r 372) 205851766545670995
  206226080112247790) (cond (Nat.ble r 374) 206597925284311667 206971181559141967))) (cond
  (Nat.ble r 379) (cond (Nat.ble r 377) (cond (Nat.ble r 376) 207342095016498148
  207714305735260554) (cond (Nat.ble r 378) 208084291653487743 208455468211899303)) (cond
  (Nat.ble r 381) (cond (Nat.ble r 380) 208824530891089932 209194563338586123) (cond
  (Nat.ble r 382) 209562703774099933 209931727530427312)))))
/-- Tier-2 Bellman block 6 (`384 ≤ r ≤ 447`) at `10^16` scale. -/
def solM1VTblB6 (r : ℕ) : ℤ :=
  cond (Nat.ble r 415) (cond (Nat.ble r 399) (cond (Nat.ble r 391) (cond (Nat.ble r 387)
  (cond (Nat.ble r 385) (cond (Nat.ble r 384) 210298950441863137 210666975775249808) (cond
  (Nat.ble r 386) 211033285960635406 211400322871383606)) (cond (Nat.ble r 389) (cond
  (Nat.ble r 388) 211765725198000751 212131783430831541) (cond (Nat.ble r 390)
  212496282826679109 212861371882379458))) (cond (Nat.ble r 395) (cond (Nat.ble r 393) (cond
  (Nat.ble r 392) 213224973328233541 213589102474647711) (cond (Nat.ble r 394)
  213951810996680371 214314989279084942)) (cond (Nat.ble r 397) (cond (Nat.ble r 396)
  214676809942005636 215039046192905096) (cond (Nat.ble r 398) 215399984093591054
  215761286941968628)))) (cond (Nat.ble r 407) (cond (Nat.ble r 403) (cond (Nat.ble r 401)
  (cond (Nat.ble r 400) 216121347203552605 216481725083608869) (cond (Nat.ble r 402)
  216840912849994662 217200374009404508)) (cond (Nat.ble r 405) (cond (Nat.ble r 404)
  217558694440182508 217917246947899142) (cond (Nat.ble r 406) 218274705213635935
  218632356967268861))) (cond (Nat.ble r 411) (cond (Nat.ble r 409) (cond (Nat.ble r 408)
  218988958245146530 219345716977938804) (cond (Nat.ble r 410) 219701466447721122
  220057339735149642)) (cond (Nat.ble r 413) (cond (Nat.ble r 412) 220412242575453790
  220767237841474917) (cond (Nat.ble r 414) 221121299226328702 221475423749290164))))) (cond
  (Nat.ble r 431) (cond (Nat.ble r 423) (cond (Nat.ble r 419) (cond (Nat.ble r 417) (cond
  (Nat.ble r 416) 221828648844955997 222181909763194748) (cond (Nat.ble r 418)
  222534303725242802 222886708042387309)) (cond (Nat.ble r 421) (cond (Nat.ble r 420)
  223238276013001423 223589830602995734) (cond (Nat.ble r 422) 223940577708496637
  224291289320362530))) (cond (Nat.ble r 427) (cond (Nat.ble r 425) (cond (Nat.ble r 424)
  224641220668933966 224991095931286484) (cond (Nat.ble r 426) 225340216610890722
  225689262036221478)) (cond (Nat.ble r 429) (cond (Nat.ble r 428) 226037577112691548
  226385799101433305) (cond (Nat.ble r 430) 226733313616730116 227080718461115340)))) (cond
  (Nat.ble r 439) (cond (Nat.ble r 435) (cond (Nat.ble r 433) (cond (Nat.ble r 432)
  227427437431738582 227774031319463884) (cond (Nat.ble r 434) 228119959735006326
  228465748752714000)) (cond (Nat.ble r 437) (cond (Nat.ble r 436) 228810891574549470
  229155881711136654) (cond (Nat.ble r 438) 229500243871232582 229844441020997934))) (cond
  (Nat.ble r 443) (cond (Nat.ble r 441) (cond (Nat.ble r 440) 230188027420843954
  230531437386481135) (cond (Nat.ble r 442) 230874252896125765 231216881391572471)) (cond
  (Nat.ble r 445) (cond (Nat.ble r 444) 231558930848760411 231900783501911161) (cond
  (Nat.ble r 446) 232242071711314223 232583154066604625)))))
/-- Tier-2 Bellman block 7 (`448 ≤ r ≤ 511`) at `10^16` scale. -/
def solM1VTblB7 (r : ℕ) : ℤ :=
  cond (Nat.ble r 479) (cond (Nat.ble r 463) (cond (Nat.ble r 455) (cond (Nat.ble r 451)
  (cond (Nat.ble r 449) (cond (Nat.ble r 448) 232923685799139766 233264003320009513) (cond
  (Nat.ble r 450) 233603783312237858 233943341383479278)) (cond (Nat.ble r 453) (cond
  (Nat.ble r 452) 234282374337080412 234621178267078981) (cond (Nat.ble r 454)
  234959468848395167 235297523871268021))) (cond (Nat.ble r 459) (cond (Nat.ble r 457) (cond
  (Nat.ble r 456) 235635076710913336 235972387988551446) (cond (Nat.ble r 458)
  236309207681081164 236645780305100512)) (cond (Nat.ble r 461) (cond (Nat.ble r 460)
  236981871408736354 237317710402343121) (cond (Nat.ble r 462) 237653077438750291
  237988187758524777)))) (cond (Nat.ble r 471) (cond (Nat.ble r 467) (cond (Nat.ble r 465)
  (cond (Nat.ble r 464) 238322835212636958 238657221750240674) (cond (Nat.ble r 466)
  238991154070129410 239324821653939512)) (cond (Nat.ble r 469) (cond (Nat.ble r 468)
  239658043250724645 239990996647399647) (cond (Nat.ble r 470) 240323511895197682
  240655755811178137))) (cond (Nat.ble r 475) (cond (Nat.ble r 473) (cond (Nat.ble r 472)
  240987569047085634 241319108130033267) (cond (Nat.ble r 474) 241650223654142524
  241981062494321096)) (cond (Nat.ble r 477) (cond (Nat.ble r 476) 242311484569765598
  242641627701366574) (cond (Nat.ble r 478) 242971360554393824 243300812456809761))))) (cond
  (Nat.ble r 495) (cond (Nat.ble r 487) (cond (Nat.ble r 483) (cond (Nat.ble r 481) (cond
  (Nat.ble r 480) 243629860276879289 243958625375927666) (cond (Nat.ble r 482)
  244286992315832141 244615074984932217)) (cond (Nat.ble r 485) (cond (Nat.ble r 484)
  244942765160939741 245270169722244855) (cond (Nat.ble r 486) 245597187214260640
  245923917939748245))) (cond (Nat.ble r 491) (cond (Nat.ble r 489) (cond (Nat.ble r 488)
  246250266791493996 246576327904015579) (cond (Nat.ble r 490) 246902012123225016
  247227407797517931)) (cond (Nat.ble r 493) (cond (Nat.ble r 492) 247552431356147003
  247877165719810126) (cond (Nat.ble r 494) 248201532554260553 248525609688695570)))) (cond
  (Nat.ble r 503) (cond (Nat.ble r 499) (cond (Nat.ble r 497) (cond (Nat.ble r 496)
  248849323700050446 249172747641370465) (cond (Nat.ble r 498) 249495812695640757
  249818587435547853)) (cond (Nat.ble r 501) (cond (Nat.ble r 500) 250141007363928688
  250463136850561888) (cond (Nat.ble r 502) 250784915449697618 251106403588452753))) (cond
  (Nat.ble r 507) (cond (Nat.ble r 505) (cond (Nat.ble r 504) 251427544620709848
  251748395275032621) (cond (Nat.ble r 506) 252068902468779506 252389119460933045)) (cond
  (Nat.ble r 509) (cond (Nat.ble r 508) 252708996510826063 253028583622634157) (cond
  (Nat.ble r 510) 253347834189908906 253666795163476053)))))
/-- Tier-2 Bellman block 8 (`512 ≤ r ≤ 575`) at `10^16` scale. -/
def solM1VTblB8 (r : ℕ) : ℤ :=
  cond (Nat.ble r 543) (cond (Nat.ble r 527) (cond (Nat.ble r 519) (cond (Nat.ble r 515)
  (cond (Nat.ble r 513) (cond (Nat.ble r 512) 225972690854121154 226319452685594204) (cond
  (Nat.ble r 514) 226610063649222038 226954444200544243)) (cond (Nat.ble r 517) (cond
  (Nat.ble r 516) 227246146081987298 227588258508813377) (cond (Nat.ble r 518)
  227880948769521008 228220899383554273))) (cond (Nat.ble r 523) (cond (Nat.ble r 521) (cond
  (Nat.ble r 520) 228514482045047543 228852370737691133) (cond (Nat.ble r 522)
  229146755972197260 229482676611897357)) (cond (Nat.ble r 525) (cond (Nat.ble r 524)
  229777780358445928 230111821163361602) (cond (Nat.ble r 526) 230407564767759849
  230739808655292602)))) (cond (Nat.ble r 535) (cond (Nat.ble r 531) (cond (Nat.ble r 529)
  (cond (Nat.ble r 528) 231036118532495388 231366643447116190) (cond (Nat.ble r 530)
  231663450764598623 231992329985320887)) (cond (Nat.ble r 533) (cond (Nat.ble r 532)
  232289570366147985 232616872794911135) (cond (Nat.ble r 534) 232914486039280122
  233240276471429810))) (cond (Nat.ble r 539) (cond (Nat.ble r 537) (cond (Nat.ble r 536)
  233538206295536713 233862545673514045) (cond (Nat.ble r 538) 234160739464667640
  234483685115950638)) (cond (Nat.ble r 541) (cond (Nat.ble r 540) 234782093702923729
  235103699563199437) (cond (Nat.ble r 542) 235402277000870221 235722593823355049))))) (cond
  (Nat.ble r 559) (cond (Nat.ble r 551) (cond (Nat.ble r 547) (cond (Nat.ble r 545) (cond
  (Nat.ble r 544) 236021297190750201 236340372742519096) (cond (Nat.ble r 546)
  236639161953425417 236957041199556956)) (cond (Nat.ble r 549) (cond (Nat.ble r 548)
  237255878824920220 237572604101214580) (cond (Nat.ble r 550) 237871455202592767
  238187066377572477))) (cond (Nat.ble r 555) (cond (Nat.ble r 553) (cond (Nat.ble r 552)
  238485898350956137 238800432977815412) (cond (Nat.ble r 554) 239099215407170618
  239412708866297693)) (cond (Nat.ble r 557) (cond (Nat.ble r 556) 239711413386227104
  240023899018885194) (cond (Nat.ble r 558) 240322499185840312 240634008419556426)))) (cond
  (Nat.ble r 567) (cond (Nat.ble r 563) (cond (Nat.ble r 561) (cond (Nat.ble r 560)
  240932479591069380 241243042057246091) (cond (Nat.ble r 562) 241541361278682318
  241851004922915584)) (cond (Nat.ble r 565) (cond (Nat.ble r 564) 242149150821279774
  242457902006835882) (cond (Nat.ble r 566) 242755854691192619 243063738296069175))) (cond
  (Nat.ble r 571) (cond (Nat.ble r 569) (cond (Nat.ble r 568) 243361479264166967
  243668518772136447) (cond (Nat.ble r 570) 243966030822849402 244272248408859022)) (cond
  (Nat.ble r 573) (cond (Nat.ble r 572) 244569515560084404 244874932170362836) (cond
  (Nat.ble r 574) 245171939582035225 245476575009234910)))))
/-- Tier-2 Bellman block 9 (`576 ≤ r ≤ 639`) at `10^16` scale. -/
def solM1VTblB9 (r : ℕ) : ℤ :=
  cond (Nat.ble r 607) (cond (Nat.ble r 591) (cond (Nat.ble r 583) (cond (Nat.ble r 579)
  (cond (Nat.ble r 577) (cond (Nat.ble r 576) 245773308911138774 246077181864822153) (cond
  (Nat.ble r 578) 246373629488904421 246676757661663249)) (cond (Nat.ble r 581) (cond
  (Nat.ble r 580) 246972907178566023 247275307308044960) (cond (Nat.ble r 582)
  247571147767595900 247872835694674734))) (cond (Nat.ble r 587) (cond (Nat.ble r 585) (cond
  (Nat.ble r 584) 248168356970088965 248469347693461995) (cond (Nat.ble r 586)
  248764540429024686 249064848156400998)) (cond (Nat.ble r 589) (cond (Nat.ble r 588)
  249359703718414112 249659341914548564) (cond (Nat.ble r 590) 249953852345338739
  250252833777090435)))) (cond (Nat.ble r 599) (cond (Nat.ble r 595) (cond (Nat.ble r 593)
  (cond (Nat.ble r 592) 250546991751887577 250845328530490395) (cond (Nat.ble r 594)
  251139127316998392 251436830937716652)) (cond (Nat.ble r 597) (cond (Nat.ble r 596)
  251730264358208738 252027345737540344) (cond (Nat.ble r 598) 252320408133322038
  252616877643901347))) (cond (Nat.ble r 603) (cond (Nat.ble r 601) (cond (Nat.ble r 600)
  252909563841993661 253205431345336872) (cond (Nat.ble r 602) 253497736627241642
  253793011504468623)) (cond (Nat.ble r 605) (cond (Nat.ble r 604) 254084931576886398
  254379622757544549) (cond (Nat.ble r 606) 254671153724923543 254965269714031496))))) (cond
  (Nat.ble r 623) (cond (Nat.ble r 615) (cond (Nat.ble r 611) (cond (Nat.ble r 609) (cond
  (Nat.ble r 608) 255256408052833642 255549956956255271) (cond (Nat.ble r 610)
  255840699490832512 256133689039084877)) (cond (Nat.ble r 613) (cond (Nat.ble r 612)
  256424032919065477 256716470489657868) (cond (Nat.ble r 614) 257006413168748747
  257298305807143981))) (cond (Nat.ble r 619) (cond (Nat.ble r 617) (cond (Nat.ble r 616)
  257587845023260922 257879199462544369) (cond (Nat.ble r 618) 258168333219187438
  258459155898523941)) (cond (Nat.ble r 621) (cond (Nat.ble r 620) 258747882447320587
  259038179529274472) (cond (Nat.ble r 622) 259326497353617604 259616274740406296)))) (cond
  (Nat.ble r 631) (cond (Nat.ble r 627) (cond (Nat.ble r 625) (cond (Nat.ble r 624)
  259904182540119145 260193445888866528) (cond (Nat.ble r 626) 260480942565830356
  260769697302881912)) (cond (Nat.ble r 629) (cond (Nat.ble r 628) 261056781947566588
  261345033281924489) (cond (Nat.ble r 630) 261631705160765701 261919458096698416))) (cond
  (Nat.ble r 635) (cond (Nat.ble r 633) (cond (Nat.ble r 632) 262205716640268770
  262492975989146368) (cond (Nat.ble r 634) 262778820781070913 263065591172474057)) (cond
  (Nat.ble r 637) (cond (Nat.ble r 636) 263351021939043842 263637307831191489) (cond
  (Nat.ble r 638) 263922324431631660 264208130121169684)))))
/-- Tier-2 Bellman block 10 (`640 ≤ r ≤ 703`) at `10^16` scale. -/
def solM1VTblB10 (r : ℕ) : ℤ :=
  cond (Nat.ble r 671) (cond (Nat.ble r 655) (cond (Nat.ble r 647) (cond (Nat.ble r 643)
  (cond (Nat.ble r 641) (cond (Nat.ble r 640) 264492732538521319 264778062169711664) (cond
  (Nat.ble r 642) 265062250502289079 265347108075636575)) (cond (Nat.ble r 645) (cond
  (Nat.ble r 644) 265630882529024233 265915271909375910) (cond (Nat.ble r 646)
  266198632788931279 266482557713080845))) (cond (Nat.ble r 651) (cond (Nat.ble r 649) (cond
  (Nat.ble r 648) 266765505416911648 267048969500739783) (cond (Nat.ble r 650)
  267331504513126049 267614511258305241)) (cond (Nat.ble r 653) (cond (Nat.ble r 652)
  267896634143538406 268179186943829295) (cond (Nat.ble r 654) 268460898340442328
  268743000487606829)))) (cond (Nat.ble r 663) (cond (Nat.ble r 659) (cond (Nat.ble r 657)
  (cond (Nat.ble r 656) 269024301102970974 269305955792325903) (cond (Nat.ble r 658)
  269586846397591151 269868056733224579)) (cond (Nat.ble r 661) (cond (Nat.ble r 660)
  270148538158582408 270429307158253616) (cond (Nat.ble r 662) 270709380288501868
  270989710888244457))) (cond (Nat.ble r 667) (cond (Nat.ble r 665) (cond (Nat.ble r 664)
  271269376658635476 271549271717081989) (cond (Nat.ble r 666) 271828531109436322
  272107993411881583)) (cond (Nat.ble r 669) (cond (Nat.ble r 668) 272386847450950642
  272665879713169964) (cond (Nat.ble r 670) 272944329463232081 273222934335069473))))) (cond
  (Nat.ble r 687) (cond (Nat.ble r 679) (cond (Nat.ble r 675) (cond (Nat.ble r 673) (cond
  (Nat.ble r 672) 273500980896744755 273779160965485339) (cond (Nat.ble r 674)
  274056805472755630 274334563266295582)) (cond (Nat.ble r 677) (cond (Nat.ble r 676)
  274611806883716697 274889144873543210) (cond (Nat.ble r 678) 275165988793637402
  275442909397630391))) (cond (Nat.ble r 683) (cond (Nat.ble r 681) (cond (Nat.ble r 680)
  275719354838447763 275995860423514298) (cond (Nat.ble r 682) 276271908626352577
  276548001510904359)) (cond (Nat.ble r 685) (cond (Nat.ble r 684) 276823653738177104
  277099336194460655) (cond (Nat.ble r 686) 277374593727704587 277649867983993223)))) (cond
  (Nat.ble r 695) (cond (Nat.ble r 691) (cond (Nat.ble r 689) (cond (Nat.ble r 688)
  277924732122005956 278199600364662048) (cond (Nat.ble r 690) 278474072421762034
  278748536797177547)) (cond (Nat.ble r 693) (cond (Nat.ble r 692) 279022618101578553
  279296680718001341) (cond (Nat.ble r 694) 279570372610294276 279844035539547156))) (cond
  (Nat.ble r 699) (cond (Nat.ble r 697) (cond (Nat.ble r 696) 280117339371282482
  280390604650381681) (cond (Nat.ble r 698) 280663521782746096 280936391415425238)) (cond
  (Nat.ble r 701) (cond (Nat.ble r 700) 281208923218006689 281481399176152128) (cond
  (Nat.ble r 702) 281753547025787591 282025631250790519)))))
/-- Tier-2 Bellman block 11 (`704 ≤ r ≤ 767`) at `10^16` scale. -/
def solM1VTblB11 (r : ℕ) : ℤ :=
  cond (Nat.ble r 735) (cond (Nat.ble r 719) (cond (Nat.ble r 711) (cond (Nat.ble r 707)
  (cond (Nat.ble r 705) (cond (Nat.ble r 704) 282297396530491334 282569090934521771) (cond
  (Nat.ble r 706) 282840475032471634 283111781499679076)) (cond (Nat.ble r 709) (cond
  (Nat.ble r 708) 283382785808300110 283653706195945330) (cond (Nat.ble r 710)
  283924332111027925 284194868250550132))) (cond (Nat.ble r 715) (cond (Nat.ble r 713) (cond
  (Nat.ble r 712) 284465117170442531 284735270868465838) (cond (Nat.ble r 714)
  285005144193319682 285274917232602586)) (cond (Nat.ble r 717) (cond (Nat.ble r 716)
  285544416363670879 285813810504002231) (cond (Nat.ble r 718) 286082936842986397
  286351953822031122)))) (cond (Nat.ble r 727) (cond (Nat.ble r 723) (cond (Nat.ble r 721)
  (cond (Nat.ble r 720) 286620708770474039 286889350304571663) (cond (Nat.ble r 722)
  287157735263293756 287426003048212611)) (cond (Nat.ble r 725) (cond (Nat.ble r 724)
  287694019416788262 287961915128438060) (cond (Nat.ble r 726) 288229564304709770
  288497089599815073))) (cond (Nat.ble r 731) (cond (Nat.ble r 729) (cond (Nat.ble r 728)
  288764372979442966 289031529496179918) (cond (Nat.ble r 730) 289298448472224332
  289565237830822886)) (cond (Nat.ble r 733) (cond (Nat.ble r 732) 289831793793357935
  290098217596671647) (cond (Nat.ble r 734) 290364411932427771 290630471766473130))))) (cond
  (Nat.ble r 751) (cond (Nat.ble r 743) (cond (Nat.ble r 739) (cond (Nat.ble r 737) (cond
  (Nat.ble r 736) 290896305858506773 291162003292973894) (cond (Nat.ble r 738)
  291427478520362570 291692815109098982)) (cond (Nat.ble r 741) (cond (Nat.ble r 740)
  291957932846660090 292222910128129228) (cond (Nat.ble r 742) 292487671746161088
  292752291243877012))) (cond (Nat.ble r 747) (cond (Nat.ble r 745) (cond (Nat.ble r 744)
  293016698107920688 293280961330860447) (cond (Nat.ble r 746) 293545014801481008
  293808923244475987)) (cond (Nat.ble r 749) (cond (Nat.ble r 748) 294072624677061949
  294336179821169456) (cond (Nat.ble r 750) 294599530565749216 294862733878605479)))) (cond
  (Nat.ble r 759) (cond (Nat.ble r 755) (cond (Nat.ble r 753) (cond (Nat.ble r 752)
  295125735279679643 295388588215835326) (cond (Nat.ble r 754) 295651241612223882
  295913745613463156)) (cond (Nat.ble r 757) (cond (Nat.ble r 756) 296176052338166529
  296438208833810663) (cond (Nat.ble r 758) 296700170213883733 296961980621080129))) (cond
  (Nat.ble r 763) (cond (Nat.ble r 761) (cond (Nat.ble r 760) 297223597977518361
  297485019471254814) (cond (Nat.ble r 762) 297746292749629540 298007372337743840)) (cond
  (Nat.ble r 765) (cond (Nat.ble r 764) 298268302933560630 298529041913874210) (cond
  (Nat.ble r 766) 298789631210886807 299050030875320085)))))
/-- Tier-2 Bellman block 12 (`768 ≤ r ≤ 831`) at `10^16` scale. -/
def solM1VTblB12 (r : ℕ) : ℤ :=
  cond (Nat.ble r 799) (cond (Nat.ble r 783) (cond (Nat.ble r 775) (cond (Nat.ble r 771)
  (cond (Nat.ble r 769) (cond (Nat.ble r 768) 299310280245794510 299570341880268551) (cond
  (Nat.ble r 770) 299830252685234814 300089977569583149)) (cond (Nat.ble r 773) (cond
  (Nat.ble r 772) 300349551159075296 300608940566965230) (cond (Nat.ble r 774)
  300868178280250402 301127233479113172))) (cond (Nat.ble r 779) (cond (Nat.ble r 777) (cond
  (Nat.ble r 776) 301386136644910323 301644858895879508) (cond (Nat.ble r 778)
  301903428832568380 302161819390426011)) (cond (Nat.ble r 781) (cond (Nat.ble r 780)
  302420057406246931 302678117519376776) (cond (Nat.ble r 782) 302936024912621802
  303193755822969340)))) (cond (Nat.ble r 791) (cond (Nat.ble r 787) (cond (Nat.ble r 785)
  (cond (Nat.ble r 784) 303451333882165257 303708736825203878) (cond (Nat.ble r 786)
  303965986829287511 304223063033990518)) (cond (Nat.ble r 789) (cond (Nat.ble r 788)
  304479986252476796 304736736941294808) (cond (Nat.ble r 790) 304993334634437994
  305249761023281368))) (cond (Nat.ble r 795) (cond (Nat.ble r 793) (cond (Nat.ble r 792)
  305506034442229841 305762137740455768) (cond (Nat.ble r 794) 306018088127400719
  306273869537804659)) (cond (Nat.ble r 797) (cond (Nat.ble r 796) 306529498126123042
  306784958844934195) (cond (Nat.ble r 798) 307040266859326253 307295408076206771))))) (cond
  (Nat.ble r 815) (cond (Nat.ble r 807) (cond (Nat.ble r 803) (cond (Nat.ble r 801) (cond
  (Nat.ble r 800) 307550396732828438 307805219630876111) (cond (Nat.ble r 802)
  308059890137466574 308314395893220738)) (cond (Nat.ble r 805) (cond (Nat.ble r 804)
  308568749449225420 308822939232675847) (cond (Nat.ble r 806) 309076977029365062
  309330852003963615))) (cond (Nat.ble r 811) (cond (Nat.ble r 809) (cond (Nat.ble r 808)
  309584575224547132 309838136547221972) (cond (Nat.ble r 810) 310091546366959704
  310344795188131861)) (cond (Nat.ble r 813) (cond (Nat.ble r 812) 310597892774440889
  310850830238043008) (cond (Nat.ble r 814) 311103616750601131 311356243994098235)))) (cond
  (Nat.ble r 823) (cond (Nat.ble r 819) (cond (Nat.ble r 817) (cond (Nat.ble r 816)
  311608720584944231 311861038739356329) (cond (Nat.ble r 818) 312113206552987099
  312365216742913499)) (cond (Nat.ble r 821) (cond (Nat.ble r 820) 312617076916378255
  312868780260023444) (cond (Nat.ble r 822) 313120333923015089 313371731532216043))) (cond
  (Nat.ble r 827) (cond (Nat.ble r 825) (cond (Nat.ble r 824) 313622979807159894
  313874072787414706) (cond (Nat.ble r 826) 314125016789554685 314375806240052390)) (cond
  (Nat.ble r 829) (cond (Nat.ble r 828) 314626447077534817 314876934091186314) (cond
  (Nat.ble r 830) 315127272865141414 315377458528611382)))))
/-- Tier-2 Bellman block 13 (`832 ≤ r ≤ 895`) at `10^16` scale. -/
def solM1VTblB13 (r : ℕ) : ℤ :=
  cond (Nat.ble r 863) (cond (Nat.ble r 847) (cond (Nat.ble r 839) (cond (Nat.ble r 835)
  (cond (Nat.ble r 833) (cond (Nat.ble r 832) 315627496333232626 315877381726972346) (cond
  (Nat.ble r 834) 316127119649593721 316376705847874713)) (cond (Nat.ble r 837) (cond
  (Nat.ble r 836) 316626144969046031 316875433039994430) (cond (Nat.ble r 838)
  317124574433554759 317373565439186352))) (cond (Nat.ble r 843) (cond (Nat.ble r 841) (cond
  (Nat.ble r 840) 317622410172335666 317871105168591523) (cond (Nat.ble r 842)
  318119654301960646 318368054338743274)) (cond (Nat.ble r 845) (cond (Nat.ble r 844)
  318616308926462202 318864415047672170) (cond (Nat.ble r 846) 319112376137436839
  319360189381009810)))) (cond (Nat.ble r 855) (cond (Nat.ble r 851) (cond (Nat.ble r 849)
  (cond (Nat.ble r 848) 319607858014147383 319855379412091503) (cond (Nat.ble r 850)
  320102756623624241 320349987202057835)) (cond (Nat.ble r 853) (cond (Nat.ble r 852)
  320597074020765610 320844014799955142) (cond (Nat.ble r 854) 321090812248436655
  321337464242834904))) (cond (Nat.ble r 859) (cond (Nat.ble r 857) (cond (Nat.ble r 856)
  321583973337567658 321830337555852076) (cond (Nat.ble r 858) 322076559307251159
  322322636752362369)) (cond (Nat.ble r 861) (cond (Nat.ble r 860) 322568572164838096
  322814363834018500) (cond (Nat.ble r 862) 323060013906032955 323305520790865419))))) (cond
  (Nat.ble r 879) (cond (Nat.ble r 871) (cond (Nat.ble r 867) (cond (Nat.ble r 865) (cond
  (Nat.ble r 864) 323550886514987947 323796109601434532) (cond (Nat.ble r 866)
  324041191964396215 324286132232836929)) (cond (Nat.ble r 869) (cond (Nat.ble r 868)
  324530932215584093 324775590640855636) (cond (Nat.ble r 870) 325020109218602419
  325264486770036898))) (cond (Nat.ble r 875) (cond (Nat.ble r 873) (cond (Nat.ble r 872)
  325508724912316915 325752822553780512) (cond (Nat.ble r 874) 325996781224497654
  326240599914429218)) (cond (Nat.ble r 877) (cond (Nat.ble r 876) 326484280071907608
  326727820763357161) (cond (Nat.ble r 878) 326971223360390306 327214487001057441)))) (cond
  (Nat.ble r 887) (cond (Nat.ble r 883) (cond (Nat.ble r 881) (cond (Nat.ble r 880)
  327457612984956599 327700600517228755) (cond (Nat.ble r 882) 327943450829870548
  328186163190861150)) (cond (Nat.ble r 885) (cond (Nat.ble r 884) 328428738768734450
  328671176890320895) (cond (Nat.ble r 886) 328913478664573000 329155643473434482))) (cond
  (Nat.ble r 891) (cond (Nat.ble r 889) (cond (Nat.ble r 888) 329397672369916611
  329639564787571773) (cond (Nat.ble r 890) 329881321726883897 330122942669728298)) (cond
  (Nat.ble r 893) (cond (Nat.ble r 892) 330364428567263330 330605778946606716) (cond
  (Nat.ble r 894) 330846994712594078 331088075434697456)))))
/-- Tier-2 Bellman block 14 (`896 ≤ r ≤ 959`) at `10^16` scale. -/
def solM1VTblB14 (r : ℕ) : ℤ :=
  cond (Nat.ble r 927) (cond (Nat.ble r 911) (cond (Nat.ble r 903) (cond (Nat.ble r 899)
  (cond (Nat.ble r 897) (cond (Nat.ble r 896) 331329021974246039 331569833940358534) (cond
  (Nat.ble r 898) 331810512153499074 332051056259894574)) (cond (Nat.ble r 901) (cond
  (Nat.ble r 900) 332291467041621457 332531744179635032) (cond (Nat.ble r 902)
  332771888419947540 333011899476011634))) (cond (Nat.ble r 907) (cond (Nat.ble r 905) (cond
  (Nat.ble r 904) 333251778059954655 333491523915635039) (cond (Nat.ble r 906)
  333731137723339251 333970619255370740)) (cond (Nat.ble r 909) (cond (Nat.ble r 908)
  334209969162092281 334449187242414207) (cond (Nat.ble r 910) 334688274118573848
  334927229614365287)))) (cond (Nat.ble r 919) (cond (Nat.ble r 915) (cond (Nat.ble r 913)
  (cond (Nat.ble r 912) 335166054325587114 335404748099301860) (cond (Nat.ble r 914)
  335643311506451488 335881744415852777)) (cond (Nat.ble r 917) (cond (Nat.ble r 916)
  336120047375075094 336358220273270070) (cond (Nat.ble r 918) 336596263636026532
  336834177371500458))) (cond (Nat.ble r 923) (cond (Nat.ble r 921) (cond (Nat.ble r 920)
  337071961984605939 337309617401256147) (cond (Nat.ble r 922) 337547144106915359
  337784542044084941)) (cond (Nat.ble r 925) (cond (Nat.ble r 924) 338021811679928428
  338258952972439665) (cond (Nat.ble r 926) 338495966371559387 338732851849746913))))) (cond
  (Nat.ble r 943) (cond (Nat.ble r 935) (cond (Nat.ble r 931) (cond (Nat.ble r 929) (cond
  (Nat.ble r 928) 338969609840731422 339206240330475127) (cond (Nat.ble r 930)
  339442743737444348 339679120060202018)) (cond (Nat.ble r 933) (cond (Nat.ble r 932)
  339915369702841638 340151492675681332) (cond (Nat.ble r 934) 340387489369276811
  340623359804908972))) (cond (Nat.ble r 939) (cond (Nat.ble r 937) (cond (Nat.ble r 936)
  340859104360379180 341094723067188484) (cond (Nat.ble r 938) 341330216291118971
  341565584073195912)) (cond (Nat.ble r 941) (cond (Nat.ble r 940) 341800826767871820
  342035944425044033) (cond (Nat.ble r 942) 342270937388482653 342505805716345976)))) (cond
  (Nat.ble r 951) (cond (Nat.ble r 947) (cond (Nat.ble r 945) (cond (Nat.ble r 944)
  342740549742328960 342975169532278236) (cond (Nat.ble r 946) 343209665410383466
  343444037449643082)) (cond (Nat.ble r 949) (cond (Nat.ble r 948) 343678285965276211
  343912411036930380) (cond (Nat.ble r 950) 344146412971356036 344380291854378822))) (cond
  (Nat.ble r 955) (cond (Nat.ble r 953) (cond (Nat.ble r 952) 344614047984751498
  344847681454036581) (cond (Nat.ble r 954) 345081192553431199 345314581379821391)) (cond
  (Nat.ble r 957) (cond (Nat.ble r 956) 345547848217263560 345780993167580059) (cond
  (Nat.ble r 958) 346014016508076023 346246918345147421)))))
/-- Tier-2 Bellman block 15 (`960 ≤ r ≤ 1024`) at `10^16` scale. -/
def solM1VTblB15 (r : ℕ) : ℤ :=
  cond (Nat.ble r 992) (cond (Nat.ble r 976) (cond (Nat.ble r 968) (cond (Nat.ble r 964)
  (cond (Nat.ble r 962) (cond (Nat.ble r 961) (cond (Nat.ble r 960) 346479698949713706
  346712358432404746) 346944897058097506) (cond (Nat.ble r 963) 347177314941337586
  347409612341281661)) (cond (Nat.ble r 966) (cond (Nat.ble r 965) 347641789376093093
  347873846299510774) (cond (Nat.ble r 967) 348105783233036799 348337600425276311))) (cond
  (Nat.ble r 972) (cond (Nat.ble r 970) (cond (Nat.ble r 969) 348569298000808867
  348800876203372573) (cond (Nat.ble r 971) 349032335160379820 349263675110952146)) (cond
  (Nat.ble r 974) (cond (Nat.ble r 973) 349494896185105756 349725998617580848) (cond
  (Nat.ble r 975) 349956982540783051 350187848185292161)))) (cond (Nat.ble r 984) (cond
  (Nat.ble r 980) (cond (Nat.ble r 978) (cond (Nat.ble r 977) 350418595685702556
  350649225268641164) (cond (Nat.ble r 979) 350879737070703297 351110131314757975)) (cond
  (Nat.ble r 982) (cond (Nat.ble r 981) 351340408139225683 351570567763400699) (cond
  (Nat.ble r 983) 351800610327364222 352030536047007893))) (cond (Nat.ble r 988) (cond
  (Nat.ble r 986) (cond (Nat.ble r 985) 352260345063919759 352490037590750553) (cond
  (Nat.ble r 987) 352719613770451234 352949073812583627)) (cond (Nat.ble r 990) (cond
  (Nat.ble r 989) 353178417861326972 353407646123297058) (cond (Nat.ble r 991)
  353636758743775503 353865755926566368))))) (cond (Nat.ble r 1008) (cond (Nat.ble r 1000)
  (cond (Nat.ble r 996) (cond (Nat.ble r 994) (cond (Nat.ble r 993) 354094637817935924
  354323404619002779) (cond (Nat.ble r 995) 354552056476907801 354780593590202885)) (cond
  (Nat.ble r 998) (cond (Nat.ble r 997) 355009016106800624 355237324222797874) (cond
  (Nat.ble r 999) 355465518086782816 355693597892502309))) (cond (Nat.ble r 1004) (cond
  (Nat.ble r 1002) (cond (Nat.ble r 1001) 355921563789130298 356149415968162467) (cond
  (Nat.ble r 1003) 356377154579274620 356604779811804249)) (cond (Nat.ble r 1006) (cond
  (Nat.ble r 1005) 356832291815850659 357059690778680658) (cond (Nat.ble r 1007)
  357286976850743892 357514150217318857)))) (cond (Nat.ble r 1016) (cond (Nat.ble r 1012)
  (cond (Nat.ble r 1010) (cond (Nat.ble r 1009) 357741211029137247 357968159469566801) (cond
  (Nat.ble r 1011) 358194995689557535 358421719870639461)) (cond (Nat.ble r 1014) (cond
  (Nat.ble r 1013) 358648332163921471 358874832749164635) (cond (Nat.ble r 1015)
  359101221777581283 359327499427228351))) (cond (Nat.ble r 1020) (cond (Nat.ble r 1018)
  (cond (Nat.ble r 1017) 359553665849369923 359779721220419873) (cond (Nat.ble r 1019)
  360005665691645874 360231499437876304)) (cond (Nat.ble r 1022) (cond (Nat.ble r 1021)
  360457222610337561 360682835382326803) (cond (Nat.ble r 1023) 360908337904987376
  321352771346859932)))))
/-- Certified `m = 1` Multi-pulse Bellman table `V(0..1024)` at `10^16` scale. -/
def solM1VTable16 (r : ℕ) : ℤ :=
  cond (Nat.ble r 511) (cond (Nat.ble r 255) (cond (Nat.ble r 127) (cond (Nat.ble r 63)
  (solM1VTblB0 r) (solM1VTblB1 r)) (cond (Nat.ble r 191) (solM1VTblB2 r) (solM1VTblB3 r)))
  (cond (Nat.ble r 383) (cond (Nat.ble r 319) (solM1VTblB4 r) (solM1VTblB5 r)) (cond
  (Nat.ble r 447) (solM1VTblB6 r) (solM1VTblB7 r)))) (cond (Nat.ble r 767) (cond (Nat.ble r
  639) (cond (Nat.ble r 575) (solM1VTblB8 r) (solM1VTblB9 r)) (cond (Nat.ble r 703)
  (solM1VTblB10 r) (solM1VTblB11 r))) (cond (Nat.ble r 895) (cond (Nat.ble r 831)
  (solM1VTblB12 r) (solM1VTblB13 r)) (cond (Nat.ble r 959) (solM1VTblB14 r) (solM1VTblB15
  r))))
/-- Chunk 0 of `solExplicitPulses_r2`. -/
def solExplicitPulses_r2_c0 : List (SolSparsePulse) := [⟨1, [4315], (-52)⟩, ⟨1, [4286], (-6)⟩, ⟨1,
  [4256], 2⟩, ⟨1, [4208], (-3)⟩, ⟨1, [4142], 0⟩, ⟨1, [4075], 0⟩, ⟨1, [3992], 0⟩, ⟨1, [3898], 0⟩,
  ⟨1, [3804], 0⟩, ⟨1, [3701], 0⟩, ⟨1, [3593], 0⟩, ⟨1, [3485], 0⟩]
/-- Chunk 1 of `solExplicitPulses_r2`. -/
def solExplicitPulses_r2_c1 : List (SolSparsePulse) := [⟨1, [3375], 0⟩, ⟨1, [3263], 0⟩, ⟨1, [3156],
  0⟩, ⟨1, [3046], 0⟩, ⟨1, [2943], 0⟩, ⟨1, [2845], 0⟩, ⟨1, [2746], 0⟩, ⟨1, [2655], 0⟩, ⟨1, [2572],
  0⟩, ⟨1, [2487], 0⟩, ⟨1, [2417], 4⟩, ⟨1, [2348], 0⟩]
/-- Chunk 2 of `solExplicitPulses_r2`. -/
def solExplicitPulses_r2_c2 : List (SolSparsePulse) := [⟨1, [2284], 0⟩, ⟨1, [1436], 14592⟩, ⟨1,
  [1345], 15055⟩, ⟨1, [1295], 15109⟩, ⟨1, [1256], 15154⟩, ⟨1, [1216], 15181⟩, ⟨1, [1173], 15229⟩,
  ⟨1, [1137], 15277⟩, ⟨1, [1106], 15291⟩, ⟨1, [1071], 15300⟩, ⟨1, [1037], 15347⟩, ⟨1, [1007],
  15364⟩]
/-- Chunk 3 of `solExplicitPulses_r2`. -/
def solExplicitPulses_r2_c3 : List (SolSparsePulse) := [⟨1, [976], 15420⟩, ⟨1, [952], 15386⟩, ⟨1,
  [921], 15454⟩, ⟨1, [898], 15392⟩, ⟨1, [865], 15503⟩, ⟨1, [845], 15455⟩, ⟨1, [824], 15469⟩, ⟨1,
  [797], 15528⟩, ⟨1, [777], 15512⟩, ⟨1, [756], 15538⟩, ⟨1, [738], 15483⟩, ⟨1, [714], 15535⟩]
/-- Chunk 4 of `solExplicitPulses_r2`. -/
def solExplicitPulses_r2_c4 : List (SolSparsePulse) := [⟨1, [694], 15533⟩, ⟨1, [674], 15558⟩, ⟨1,
  [662], 15493⟩, ⟨1, [638], 15564⟩, ⟨1, [629], 15519⟩, ⟨1, [607], 15532⟩, ⟨1, [600], 15568⟩, ⟨1,
  [566], 15502⟩, ⟨1, [565], 15576⟩, ⟨1, [553], 15492⟩, ⟨1, [541], 15351⟩, ⟨1, [515], 15568⟩]
/-- Chunk 5 of `solExplicitPulses_r2`. -/
def solExplicitPulses_r2_c5 : List (SolSparsePulse) := [⟨1, [507], 15504⟩, ⟨1, [492], 15491⟩, ⟨1,
  [503], 15323⟩, ⟨1, [475], 15274⟩, ⟨1, [442], 15439⟩, ⟨1, [461], 15371⟩, ⟨1, [431], 15431⟩, ⟨1,
  [472], 15104⟩, ⟨1, [418], 15127⟩, ⟨1, [399], 14908⟩, ⟨1, [430], 15001⟩, ⟨1, [431], 14873⟩]
/-- Chunk 6 of `solExplicitPulses_r2`. -/
def solExplicitPulses_r2_c6 : List (SolSparsePulse) := [⟨1, [403], 14921⟩, ⟨1, [427], 15254⟩, ⟨1,
  [359], 14975⟩, ⟨1, [429], 14657⟩, ⟨1, [456], 13002⟩, ⟨1, [396], 13899⟩, ⟨1, [357], 15300⟩, ⟨1,
  [0], (-96)⟩]
/-- Explicit rational pulses for `r = 2` (`L = 2`). -/
def solExplicitPulses_r2 : List (SolSparsePulse) := List.append (List.append
  (solExplicitPulses_r2_c0) (List.append (solExplicitPulses_r2_c1) (solExplicitPulses_r2_c2)))
  (List.append (List.append (solExplicitPulses_r2_c3) (solExplicitPulses_r2_c4)) (List.append
  (solExplicitPulses_r2_c5) (solExplicitPulses_r2_c6)))
/-- Stratum angle-ratio intervals for `r = 2`. -/
def solRatios_r2 : List (IvInt) := [(707106780, 707106783)]
/-- Stratum `(cosIv, sinIv)` intervals for `r = 2`. -/
def solTrigIvs_r2 : List (IvInt × IvInt) := [((996638891, 996638892), (81920205, 81920206) ),
  ((998318974, 998318975), (57958820, 57958821)) ]
/-- Certified suffix probability lower bounds for `r = 2`. -/
def solTailLbs_r2 : List (ℤ) := [999996034, 999064089]
/-- Stage specification for explicit `m = 1` conveyor at `r = 2`. -/
def solStage_r2 : PulseM1StageSpec :=
  ⟨2, 8201211, 100000000,
    solToSwLPulses 2 65536 solExplicitPulses_r2⟩
/-- Chunk 0 of `solWkb_rBulkQ_r1024`. -/
def solWkb_rBulkQ_r1024_c0 : List (ℤ) := [29, 11242, 38825, 67065, 79429, 80282, 81253, 82315,
  83296, 84141, 84975, 85898, 86904, 87990, 89043, 89855, 90854, 92695, 94108, 93776]
/-- Chunk 1 of `solWkb_rBulkQ_r1024`. -/
def solWkb_rBulkQ_r1024_c1 : List (ℤ) := [92634, 92451, 93156, 93402, 93290, 95411, 101655, 104103,
  94120, 88364, 101747, 108503, 89066, 90547, 120995, 87184, 104203, 100922, 98976, 101545]
/-- Chunk 2 of `solWkb_rBulkQ_r1024`. -/
def solWkb_rBulkQ_r1024_c2 : List (ℤ) := [102166, 101135, 99332, 97358, 95728, 94504, 93505, 92582,
  91685, 90811, 89965, 89143, 88338, 87541, 86749, 85964, 85185, 84416, 83659, 82917]
/-- Chunk 3 of `solWkb_rBulkQ_r1024`. -/
def solWkb_rBulkQ_r1024_c3 : List (ℤ) := [82188, 69540, 40381, 11724, 0]
/-- WKB bulk profile table for `r = 1024`. -/
def solWkb_rBulkQ_r1024 : List (ℤ) := List.append (List.append (solWkb_rBulkQ_r1024_c0)
  (solWkb_rBulkQ_r1024_c1)) (List.append (solWkb_rBulkQ_r1024_c2) (solWkb_rBulkQ_r1024_c3))
/-- Chunk 0 of `solWkb_uLnchQ_r1024`. -/
def solWkb_uLnchQ_r1024_c0 : List (ℤ) := [96907, 70691, 44291, 29983, 17651, 12955, 9442, 6489,
  4068, 2657, 1554, 623, 1609, 47095, 78261, 61362, 20793, 0, (-16366), 30873]
/-- Chunk 1 of `solWkb_uLnchQ_r1024`. -/
def solWkb_uLnchQ_r1024_c1 : List (ℤ) := [35302, 29082, 22487, 16734, 11488, 6468, 2236, (-423),
  (-2602), (-4467), (-5877), (-4787), 40914, 56890, 19184, 0, (-22477), (-2749), 13301, 21631]
/-- Chunk 2 of `solWkb_uLnchQ_r1024`. -/
def solWkb_uLnchQ_r1024_c2 : List (ℤ) := [22446, 20164, 16643, 12685, 9050, 5963, 2974, 75,
  (-2243), (-3902), (-2840), 34387, 19923, 0, (-32484), (-11608), 2459, 9498, 15697, 19204]
/-- Chunk 3 of `solWkb_uLnchQ_r1024`. -/
def solWkb_uLnchQ_r1024_c3 : List (ℤ) := [18566, 15861, 13144, 10466, 7706, 4881, 2426, 444,
  (-1304), (-155), 12709, 0, (-22683), (-25907), (-8954), 2397, 8461, 11633, 15211, 15280]
/-- Chunk 4 of `solWkb_uLnchQ_r1024`. -/
def solWkb_uLnchQ_r1024_c4 : List (ℤ) := [13867, 12147, 10389, 8465, 6438, 4390, 2331, 193, 437, 0,
  (-35588), (-21302), (-15722), (-7531), 2136, 7624, 9425, 13146, 13989, 13507]
/-- Chunk 5 of `solWkb_uLnchQ_r1024`. -/
def solWkb_uLnchQ_r1024_c5 : List (ℤ) := [12679, 11507, 9956, 8062, 6003, 3085, 539, 0, (-37293),
  (-21652), (-18671), (-10648), (-5346), 1388, 6876, 7792, 11530, 12792, 12561, 11652]
/-- Chunk 6 of `solWkb_uLnchQ_r1024`. -/
def solWkb_uLnchQ_r1024_c6 : List (ℤ) := [10567, 9269, 7853, 5133, 1374, 0, (-31577), (-27363),
  (-18218), (-18640), (-7376), (-3875), 1278, 6065, 6750, 9871, 10934, 10857, 10460, 9910]
/-- Chunk 7 of `solWkb_uLnchQ_r1024`. -/
def solWkb_uLnchQ_r1024_c7 : List (ℤ) := [9213, 6738, 2041, 0, (-29698), (-29965), (-24427),
  (-14348), (-16201), (-5992), (-2707), 1035, 5129, 5671, 8557, 10024, 10431, 10474, 10278, 7838]
/-- Chunk 8 of `solWkb_uLnchQ_r1024`. -/
def solWkb_uLnchQ_r1024_c8 : List (ℤ) := [2479, 0, (-31817), (-30514), (-27998), (-18715),
  (-14077), (-14103), (-4657), (-2137), 1193, 4209, 5705, 8018, 9440, 10042, 10100, 7807, 2536, 0]
/-- Chunk 9 of `solWkb_uLnchQ_r1024`. -/
def solWkb_uLnchQ_r1024_c9 : List (ℤ) := [(-33899), (-29597), (-26926), (-23640), (-15568),
  (-12771), (-10868), (-4094), (-1347), 1145, 3527, 4999, 7010, 8527, 8969, 7180, 2450, 0,
  (-34036), (-28441)]
/-- Chunk 10 of `solWkb_uLnchQ_r1024`. -/
def solWkb_uLnchQ_r1024_c10 : List (ℤ) := [(-23682), (-23847), (-19751), (-12525), (-12095),
  (-9199), (-3637), (-852), 1139, 3101, 4616, 6226, 7545, 6595, 2398, 0, (-33201), (-27837),
  (-22737), (-21937)]
/-- Chunk 11 of `solWkb_uLnchQ_r1024`. -/
def solWkb_uLnchQ_r1024_c11 : List (ℤ) := [(-21602), (-17090), (-11442), (-11847), (-7711),
  (-3179), (-861), 1215, 2921, 4220, 5726, 5836, 2242, 0, (-32527), (-28041), (-23848), (-21071),
  (-20522), (-19407)]
/-- Chunk 12 of `solWkb_uLnchQ_r1024`. -/
def solWkb_uLnchQ_r1024_c12 : List (ℤ) := [(-14465), (-10712), (-10571), (-5619), (-3161), (-849),
  1063, 2622, 4011, 4373, 1908, 1, (-32390), (-28806), (-25275), (-21972), (-19009), (-19428),
  (-17383), (-12757)]
/-- Chunk 13 of `solWkb_uLnchQ_r1024`. -/
def solWkb_uLnchQ_r1024_c13 : List (ℤ) := [(-9131), (-9136), (-5038), (-3130), (-1195), 329, 2309,
  2908, 1405, 36, (-20619), (-23449), (-20831), (-18023), (-15080), (-14195), (-14416), (-12531),
  (-8634), (-6952)]
/-- Chunk 14 of `solWkb_uLnchQ_r1024`. -/
def solWkb_uLnchQ_r1024_c14 : List (ℤ) := [(-6720), (-3490), (-2674), (-1522), (-178), 1655, 1019,
  34, 6709, (-6287), (-7178), (-6249), (-5348), (-4552), (-4224), (-4422), (-3536), (-2644),
  (-2507), (-2111)]
/-- Chunk 15 of `solWkb_uLnchQ_r1024`. -/
def solWkb_uLnchQ_r1024_c15 : List (ℤ) := [(-1130), (-1571), (-909), (-21), 655, 72, (-1), 0, 0,
  (-11), (-35), (-56), 10, (-120), 163, 66, (-2), (-257), 236, (-284)]
/-- Chunk 16 of `solWkb_uLnchQ_r1024`. -/
def solWkb_uLnchQ_r1024_c16 : List (ℤ) := [(-536), (-248), (-105), 133]
/-- WKB launch correction table for `r = 1024`. -/
def solWkb_uLnchQ_r1024 : List (ℤ) := List.append (List.append (List.append (List.append
  (solWkb_uLnchQ_r1024_c0) (solWkb_uLnchQ_r1024_c1)) (List.append (solWkb_uLnchQ_r1024_c2)
  (solWkb_uLnchQ_r1024_c3))) (List.append (List.append (solWkb_uLnchQ_r1024_c4)
  (solWkb_uLnchQ_r1024_c5)) (List.append (solWkb_uLnchQ_r1024_c6) (solWkb_uLnchQ_r1024_c7))))
  (List.append (List.append (List.append (solWkb_uLnchQ_r1024_c8) (solWkb_uLnchQ_r1024_c9))
  (List.append (solWkb_uLnchQ_r1024_c10) (solWkb_uLnchQ_r1024_c11))) (List.append (List.append
  (solWkb_uLnchQ_r1024_c12) (solWkb_uLnchQ_r1024_c13)) (List.append (solWkb_uLnchQ_r1024_c14)
  (List.append (solWkb_uLnchQ_r1024_c15) (solWkb_uLnchQ_r1024_c16)))))
/-- Chunk 0 of `solWkb_uLandQ_r1024`. -/
def solWkb_uLandQ_r1024_c0 : List (ℤ) := [(-84456), (-82385), (-80378), (-78289), (-76200),
  (-74099), (-38259), 4727, 5415, 5415, 5414, 5414, 5414, 5414, 5414, 4338, 1500, 0, 28727, 14290]
/-- Chunk 1 of `solWkb_uLandQ_r1024`. -/
def solWkb_uLandQ_r1024_c1 : List (ℤ) := [2404, (-5673), (-11691), (-8397), (-3768), 36346, 80938,
  80193, 78004, 75258, 72428, 69559, 66644, 50955, 16756, 0, 20397, 13710, 9401, 5488]
/-- Chunk 2 of `solWkb_uLandQ_r1024`. -/
def solWkb_uLandQ_r1024_c2 : List (ℤ) := [1799, 616, 472, 1869, 38888, 81147, 81563, 82133, 82258,
  81679, 80809, 63858, 21637, 0, 14071, 12932, 11639, 6757, 3707, 1644]
/-- Chunk 3 of `solWkb_uLandQ_r1024`. -/
def solWkb_uLandQ_r1024_c3 : List (ℤ) := [227, 628, 1855, 39992, 81209, 81237, 80970, 80722, 80847,
  64989, 22431, 0, 10400, 11001, 12026, 10171, 8562, 6816, 4381, 2734]
/-- Chunk 4 of `solWkb_uLandQ_r1024`. -/
def solWkb_uLandQ_r1024_c4 : List (ℤ) := [2311, 3047, 41055, 80575, 79638, 78998, 79132, 63935,
  22260, 1, 11280, 9825, 11315, 7829, 7092, 8795, 8549, 6744, 4846, 3887]
/-- Chunk 5 of `solWkb_uLandQ_r1024`. -/
def solWkb_uLandQ_r1024_c5 : List (ℤ) := [3796, 42003, 80031, 78823, 78401, 63066, 21948, 1, 8770,
  6172, 5932, 4395, 5858, 8512, 10309, 10391, 8898, 6719, 5467, 4806]
/-- Chunk 6 of `solWkb_uLandQ_r1024`. -/
def solWkb_uLandQ_r1024_c6 : List (ℤ) := [42930, 79653, 78540, 62687, 21690, 1, 6458, (-1903),
  (-2401), 228, 3257, 5269, 7742, 10126, 11171, 9743, 8006, 6642, 5519, 44012]
/-- Chunk 7 of `solWkb_uLandQ_r1024`. -/
def solWkb_uLandQ_r1024_c7 : List (ℤ) := [79814, 63032, 21655, 1, 5299, (-9093), (-6414), (-3860),
  (-1067), 2046, 4484, 7561, 10399, 11089, 10300, 8822, 7867, 6526, 45400, 64146]
/-- Chunk 8 of `solWkb_uLandQ_r1024`. -/
def solWkb_uLandQ_r1024_c8 : List (ℤ) := [21844, 4, 21636, 741, (-1934), (-5164), (-5340), (-2314),
  269, 3545, 7319, 10071, 10741, 9586, 9191, 8548, 6967, 37056, 22233, 6]
/-- Chunk 9 of `solWkb_uLandQ_r1024`. -/
def solWkb_uLandQ_r1024_c9 : List (ℤ) := [1484, 9262, 5067, (-460), (-3464), (-4499), (-3455),
  (-695), 3106, 7266, 9137, 8873, 9255, 9663, 9052, 5596, 13131, 4, (-18432), (-4275)]
/-- Chunk 10 of `solWkb_uLandQ_r1024`. -/
def solWkb_uLandQ_r1024_c10 : List (ℤ) := [5732, 5365, 1555, (-1338), (-3120), (-2812), (-1273),
  2481, 5946, 7413, 8330, 8951, 9237, 6466, 1984, 17, (-21439), (-16768), (-3985), 4306]
/-- Chunk 11 of `solWkb_uLandQ_r1024`. -/
def solWkb_uLandQ_r1024_c11 : List (ℤ) := [4126, 1431, (-383), (-1616), (-1842), (-261), 2552,
  5250, 6163, 6096, 6789, 5787, 2025, 15, (-16925), (-16053), (-12259), (-2754), 3261, 3095]
/-- Chunk 12 of `solWkb_uLandQ_r1024`. -/
def solWkb_uLandQ_r1024_c12 : List (ℤ) := [1072, (-573), (-1049), (-563), 671, 2872, 4029, 3631,
  4522, 4684, 1848, (-3), (-17030), (-16501), (-16702), (-10636), (-2157), 2462, 2106, 67]
/-- Chunk 13 of `solWkb_uLandQ_r1024`. -/
def solWkb_uLandQ_r1024_c13 : List (ℤ) := [(-1111), (-1143), (-249), 1140, 2225, 2733, 3531, 3300,
  1209, (-1), (-14612), (-14618), (-14517), (-10923), (-6950), (-1717), 1479, 1370, 294, (-859)]
/-- Chunk 14 of `solWkb_uLandQ_r1024`. -/
def solWkb_uLandQ_r1024_c14 : List (ℤ) := [(-612), 146, 747, 1573, 2527, 1718, 530, 9, (-5425),
  (-5110), (-4771), (-4039), (-3316), (-2388), (-763), 540, 742, 135, (-425), (-515)]
/-- Chunk 15 of `solWkb_uLandQ_r1024`. -/
def solWkb_uLandQ_r1024_c15 : List (ℤ) := [(-354), 32, 546, 493, 186, 7, 1, (-1), (-5), (-20),
  (-55), (-50), (-168), (-112), 280, 232, (-101), (-319), (-258), (-179)]
/-- Chunk 16 of `solWkb_uLandQ_r1024`. -/
def solWkb_uLandQ_r1024_c16 : List (ℤ) := [(-64), 1, (-6), (-1)]
/-- WKB landing correction table for `r = 1024`. -/
def solWkb_uLandQ_r1024 : List (ℤ) := List.append (List.append (List.append (List.append
  (solWkb_uLandQ_r1024_c0) (solWkb_uLandQ_r1024_c1)) (List.append (solWkb_uLandQ_r1024_c2)
  (solWkb_uLandQ_r1024_c3))) (List.append (List.append (solWkb_uLandQ_r1024_c4)
  (solWkb_uLandQ_r1024_c5)) (List.append (solWkb_uLandQ_r1024_c6) (solWkb_uLandQ_r1024_c7))))
  (List.append (List.append (List.append (solWkb_uLandQ_r1024_c8) (solWkb_uLandQ_r1024_c9))
  (List.append (solWkb_uLandQ_r1024_c10) (solWkb_uLandQ_r1024_c11))) (List.append (List.append
  (solWkb_uLandQ_r1024_c12) (solWkb_uLandQ_r1024_c13)) (List.append (solWkb_uLandQ_r1024_c14)
  (List.append (solWkb_uLandQ_r1024_c15) (solWkb_uLandQ_r1024_c16)))))
/-- Chunk 0 of `solWkb_vDrainQ_r1024`. -/
def solWkb_vDrainQ_r1024_c0 : List (ℤ) := [35158, 204958, 283176, 283634, 281889, 284444, 288310,
  294445, 305508, 320209, 336986, 339848, 291153, 131503, (-43313), (-43693), 11134, 11657,
  (-9364), (-11919)]
/-- Chunk 1 of `solWkb_vDrainQ_r1024`. -/
def solWkb_vDrainQ_r1024_c1 : List (ℤ) := [(-1391), 2307, 194, 0]
/-- WKB drain probe table for `r = 1024`. -/
def solWkb_vDrainQ_r1024 : List (ℤ) := List.append (solWkb_vDrainQ_r1024_c0)
  (solWkb_vDrainQ_r1024_c1)
/-- Compact pure-integer WKB spline schedule for `r = 1024` (`L = 512`). -/
def solWkbSched_r1024 : SolWkbSched where
  r := 1024
  L := 512
  K := 3100
  tauNum := 200923
  tauDen := 1000000
  uvDen := 100000
  vBulkQ := 995
  sOffQ := (-1763)
  accelQ := 12
  rBulkQ := solWkb_rBulkQ_r1024
  uLnchQ := solWkb_uLnchQ_r1024
  uLandQ := solWkb_uLandQ_r1024
  vDrainQ := solWkb_vDrainQ_r1024
/-- Chunk 0 of `solRatios_r1024`. -/
def solRatios_r1024_c0 : List (IvInt) := [(999511598, 999511601), (999022959, 999022962),
  (998534080, 998534083), (998044962, 998044965), (997555605, 997555608), (997066007, 997066010),
  (996576168, 996576171), (996086089, 996086092), (995595769, 995595772), (995105207, 995105210),
  (994614402, 994614405), (994123356, 994123359) ]
/-- Chunk 1 of `solRatios_r1024`. -/
def solRatios_r1024_c1 : List (IvInt) := [(993632067, 993632070), (993140535, 993140538),
  (992648759, 992648762), (992156740, 992156743), (991664477, 991664480), (991171969, 991171972),
  (990679216, 990679219), (990186218, 990186221), (989692975, 989692978), (989199485, 989199488),
  (988705750, 988705753), (988211767, 988211770) ]
/-- Chunk 2 of `solRatios_r1024`. -/
def solRatios_r1024_c2 : List (IvInt) := [(987717538, 987717541), (987223061, 987223064),
  (986728336, 986728339), (986233363, 986233366), (985738142, 985738145), (985242672, 985242675),
  (984746952, 984746955), (984250983, 984250986), (983754763, 983754766), (983258294, 983258297),
  (982761573, 982761576), (982264601, 982264604) ]
/-- Chunk 3 of `solRatios_r1024`. -/
def solRatios_r1024_c3 : List (IvInt) := [(981767378, 981767381), (981269903, 981269906),
  (980772175, 980772178), (980274195, 980274198), (979775961, 979775964), (979277474, 979277477),
  (978778734, 978778737), (978279739, 978279742), (977780489, 977780492), (977280984, 977280987),
  (976781224, 976781227), (976281208, 976281211) ]
/-- Chunk 4 of `solRatios_r1024`. -/
def solRatios_r1024_c4 : List (IvInt) := [(975780936, 975780939), (975280407, 975280410),
  (974779621, 974779624), (974278578, 974278581), (973777277, 973777280), (973275717, 973275720),
  (972773900, 972773903), (972271823, 972271826), (971769486, 971769489), (971266890, 971266893),
  (970764034, 970764037), (970260917, 970260920) ]
/-- Chunk 5 of `solRatios_r1024`. -/
def solRatios_r1024_c5 : List (IvInt) := [(969757539, 969757542), (969253900, 969253903),
  (968749999, 968750002), (968245835, 968245838), (967741409, 967741412), (967236720, 967236723),
  (966731767, 966731770), (966226551, 966226554), (965721070, 965721073), (965215324, 965215327),
  (964709314, 964709317), (964203037, 964203040) ]
/-- Chunk 6 of `solRatios_r1024`. -/
def solRatios_r1024_c6 : List (IvInt) := [(963696495, 963696498), (963189686, 963189689),
  (962682611, 962682614), (962175268, 962175271), (961667658, 961667661), (961159780, 961159783),
  (960651633, 960651636), (960143217, 960143220), (959634532, 959634535), (959125577, 959125580),
  (958616352, 958616355), (958106856, 958106859) ]
/-- Chunk 7 of `solRatios_r1024`. -/
def solRatios_r1024_c7 : List (IvInt) := [(957597089, 957597092), (957087050, 957087053),
  (956576740, 956576743), (956066157, 956066160), (955555302, 955555305), (955044173, 955044176),
  (954532770, 954532773), (954021094, 954021097), (953509142, 953509145), (952996916, 952996919),
  (952484414, 952484417), (951971637, 951971640) ]
/-- Chunk 8 of `solRatios_r1024`. -/
def solRatios_r1024_c8 : List (IvInt) := [(951458583, 951458586), (950945252, 950945255),
  (950431644, 950431647), (949917758, 949917761), (949403594, 949403597), (948889152, 948889155),
  (948374430, 948374433), (947859429, 947859432), (947344148, 947344151), (946828586, 946828589),
  (946312744, 946312747), (945796620, 945796623) ]
/-- Chunk 9 of `solRatios_r1024`. -/
def solRatios_r1024_c9 : List (IvInt) := [(945280215, 945280218), (944763527, 944763530),
  (944246557, 944246560), (943729303, 943729306), (943211766, 943211769), (942693944, 942693947),
  (942175838, 942175841), (941657447, 941657450), (941138770, 941138773), (940619807, 940619810),
  (940100558, 940100561), (939581022, 939581025) ]
/-- Chunk 10 of `solRatios_r1024`. -/
def solRatios_r1024_c10 : List (IvInt) := [(939061199, 939061202), (938541087, 938541090),
  (938020687, 938020690), (937499999, 937500002), (936979020, 936979023), (936457752, 936457755),
  (935936194, 935936197), (935414345, 935414348), (934892205, 934892208), (934369773, 934369776),
  (933847048, 933847051), (933324031, 933324034) ]
/-- Chunk 11 of `solRatios_r1024`. -/
def solRatios_r1024_c11 : List (IvInt) := [(932800721, 932800724), (932277117, 932277120),
  (931753218, 931753221), (931229025, 931229028), (930704537, 930704540), (930179753, 930179756),
  (929654672, 929654675), (929129295, 929129298), (928603621, 928603624), (928077649, 928077652),
  (927551378, 927551381), (927024809, 927024812) ]
/-- Chunk 12 of `solRatios_r1024`. -/
def solRatios_r1024_c12 : List (IvInt) := [(926497941, 926497944), (925970773, 925970776),
  (925443304, 925443307), (924915535, 924915538), (924387465, 924387468), (923859092, 923859095),
  (923330417, 923330420), (922801440, 922801443), (922272159, 922272162), (921742574, 921742577),
  (921212684, 921212687), (920682490, 920682493) ]
/-- Chunk 13 of `solRatios_r1024`. -/
def solRatios_r1024_c13 : List (IvInt) := [(920151990, 920151993), (919621184, 919621187),
  (919090072, 919090075), (918558652, 918558655), (918026925, 918026928), (917494889, 917494892),
  (916962545, 916962548), (916429892, 916429895), (915896929, 915896932), (915363656, 915363659),
  (914830072, 914830075), (914296176, 914296179) ]
/-- Chunk 14 of `solRatios_r1024`. -/
def solRatios_r1024_c14 : List (IvInt) := [(913761968, 913761971), (913227448, 913227451),
  (912692615, 912692618), (912157468, 912157471), (911622008, 911622011), (911086232, 911086235),
  (910550141, 910550144), (910013735, 910013738), (909477012, 909477015), (908939972, 908939975),
  (908402614, 908402617), (907864939, 907864942) ]
/-- Chunk 15 of `solRatios_r1024`. -/
def solRatios_r1024_c15 : List (IvInt) := [(907326945, 907326948), (906788632, 906788635),
  (906249999, 906250002), (905711045, 905711048), (905171771, 905171774), (904632175, 904632178),
  (904092257, 904092260), (903552017, 903552020), (903011453, 903011456), (902470566, 902470569),
  (901929354, 901929357), (901387817, 901387820) ]
/-- Chunk 16 of `solRatios_r1024`. -/
def solRatios_r1024_c16 : List (IvInt) := [(900845955, 900845958), (900303767, 900303770),
  (899761252, 899761255), (899218409, 899218412), (898675239, 898675242), (898131740, 898131743),
  (897587912, 897587915), (897043754, 897043757), (896499266, 896499269), (895954448, 895954451),
  (895409297, 895409300), (894863815, 894863818) ]
/-- Chunk 17 of `solRatios_r1024`. -/
def solRatios_r1024_c17 : List (IvInt) := [(894318000, 894318003), (893771851, 893771854),
  (893225369, 893225372), (892678552, 892678555), (892131400, 892131403), (891583912, 891583915),
  (891036088, 891036091), (890487927, 890487930), (889939428, 889939431), (889390590, 889390593),
  (888841414, 888841417), (888291899, 888291902) ]
/-- Chunk 18 of `solRatios_r1024`. -/
def solRatios_r1024_c18 : List (IvInt) := [(887742043, 887742046), (887191846, 887191849),
  (886641308, 886641311), (886090428, 886090431), (885539206, 885539209), (884987640, 884987643),
  (884435730, 884435733), (883883475, 883883478), (883330875, 883330878), (882777929, 882777932),
  (882224637, 882224640), (881670997, 881671000) ]
/-- Chunk 19 of `solRatios_r1024`. -/
def solRatios_r1024_c19 : List (IvInt) := [(881117010, 881117013), (880562674, 880562677),
  (880007989, 880007992), (879452953, 879452956), (878897568, 878897571), (878341831, 878341834),
  (877785743, 877785746), (877229301, 877229304), (876672507, 876672510), (876115359, 876115362),
  (875557856, 875557859), (874999999, 875000002) ]
/-- Chunk 20 of `solRatios_r1024`. -/
def solRatios_r1024_c20 : List (IvInt) := [(874441785, 874441788), (873883214, 873883217),
  (873324287, 873324290), (872765001, 872765004), (872205357, 872205360), (871645354, 871645357),
  (871084990, 871084993), (870524266, 870524269), (869963180, 869963183), (869401732, 869401735),
  (868839922, 868839925), (868277748, 868277751) ]
/-- Chunk 21 of `solRatios_r1024`. -/
def solRatios_r1024_c21 : List (IvInt) := [(867715210, 867715213), (867152306, 867152309),
  (866589037, 866589040), (866025402, 866025405), (865461400, 865461403), (864897030, 864897033),
  (864332291, 864332294), (863767184, 863767187), (863201706, 863201709), (862635857, 862635860),
  (862069638, 862069641), (861503046, 861503049) ]
/-- Chunk 22 of `solRatios_r1024`. -/
def solRatios_r1024_c22 : List (IvInt) := [(860936081, 860936084), (860368742, 860368745),
  (859801029, 859801032), (859232941, 859232944), (858664478, 858664481), (858095637, 858095640),
  (857526419, 857526422), (856956824, 856956827), (856386849, 856386852), (855816495, 855816498),
  (855245760, 855245763), (854674644, 854674647) ]
/-- Chunk 23 of `solRatios_r1024`. -/
def solRatios_r1024_c23 : List (IvInt) := [(854103147, 854103150), (853531266, 853531269),
  (852959002, 852959005), (852386355, 852386358), (851813322, 851813325), (851239903, 851239906),
  (850666098, 850666101), (850091905, 850091908), (849517325, 849517328), (848942355, 848942358),
  (848366996, 848366999), (847791246, 847791249) ]
/-- Chunk 24 of `solRatios_r1024`. -/
def solRatios_r1024_c24 : List (IvInt) := [(847215105, 847215108), (846638573, 846638576),
  (846061647, 846061650), (845484327, 845484330), (844906613, 844906616), (844328504, 844328507),
  (843749999, 843750002), (843171096, 843171099), (842591796, 842591799), (842012098, 842012101),
  (841432000, 841432003), (840851501, 840851504) ]
/-- Chunk 25 of `solRatios_r1024`. -/
def solRatios_r1024_c25 : List (IvInt) := [(840270602, 840270605), (839689301, 839689304),
  (839107597, 839107600), (838525490, 838525493), (837942978, 837942981), (837360061, 837360064),
  (836776738, 836776741), (836193009, 836193012), (835608871, 835608874), (835024324, 835024327),
  (834439369, 834439372), (833854003, 833854006) ]
/-- Chunk 26 of `solRatios_r1024`. -/
def solRatios_r1024_c26 : List (IvInt) := [(833268225, 833268228), (832682036, 832682039),
  (832095433, 832095436), (831508417, 831508420), (830920986, 830920989), (830333139, 830333142),
  (829744876, 829744879), (829156196, 829156199), (828567097, 828567100), (827977580, 827977583),
  (827387642, 827387645), (826797283, 826797286) ]
/-- Chunk 27 of `solRatios_r1024`. -/
def solRatios_r1024_c27 : List (IvInt) := [(826206503, 826206506), (825615299, 825615302),
  (825023672, 825023675), (824431621, 824431624), (823839144, 823839147), (823246241, 823246244),
  (822652910, 822652913), (822059151, 822059154), (821464963, 821464966), (820870345, 820870348),
  (820275295, 820275298), (819679814, 819679817) ]
/-- Chunk 28 of `solRatios_r1024`. -/
def solRatios_r1024_c28 : List (IvInt) := [(819083900, 819083903), (818487552, 818487555),
  (817890769, 817890772), (817293550, 817293553), (816695895, 816695898), (816097802, 816097805),
  (815499270, 815499273), (814900299, 814900302), (814300887, 814300890), (813701034, 813701037),
  (813100738, 813100741), (812499999, 812500002) ]
/-- Chunk 29 of `solRatios_r1024`. -/
def solRatios_r1024_c29 : List (IvInt) := [(811898815, 811898818), (811297185, 811297188),
  (810695109, 810695112), (810092586, 810092589), (809489614, 809489617), (808886193, 808886196),
  (808282321, 808282324), (807677997, 807678000), (807073222, 807073225), (806467992, 806467995),
  (805862308, 805862311), (805256169, 805256172) ]
/-- Chunk 30 of `solRatios_r1024`. -/
def solRatios_r1024_c30 : List (IvInt) := [(804649573, 804649576), (804042519, 804042522),
  (803435007, 803435010), (802827035, 802827038), (802218602, 802218605), (801609707, 801609710),
  (801000350, 801000353), (800390528, 800390531), (799780242, 799780245), (799169489, 799169492),
  (798558270, 798558273), (797946582, 797946585) ]
/-- Chunk 31 of `solRatios_r1024`. -/
def solRatios_r1024_c31 : List (IvInt) := [(797334425, 797334428), (796721797, 796721800),
  (796108699, 796108702), (795495127, 795495130), (794881082, 794881085), (794266563, 794266566),
  (793651567, 793651570), (793036095, 793036098), (792420144, 792420147), (791803715, 791803718),
  (791186805, 791186808), (790569414, 790569417) ]
/-- Chunk 32 of `solRatios_r1024`. -/
def solRatios_r1024_c32 : List (IvInt) := [(789951540, 789951543), (789333182, 789333185),
  (788714340, 788714343), (788095012, 788095015), (787475197, 787475200), (786854893, 786854896),
  (786234100, 786234103), (785612817, 785612820), (784991041, 784991044), (784368773, 784368776),
  (783746011, 783746014), (783122754, 783122757) ]
/-- Chunk 33 of `solRatios_r1024`. -/
def solRatios_r1024_c33 : List (IvInt) := [(782499000, 782499003), (781874749, 781874752),
  (781249999, 781250002), (780624748, 780624751), (779998997, 779999000), (779372743, 779372746),
  (778745986, 778745989), (778118723, 778118726), (777490955, 777490958), (776862679, 776862682),
  (776233895, 776233898), (775604601, 775604604) ]
/-- Chunk 34 of `solRatios_r1024`. -/
def solRatios_r1024_c34 : List (IvInt) := [(774974796, 774974799), (774344479, 774344482),
  (773713649, 773713652), (773082303, 773082306), (772450442, 772450445), (771818063, 771818066),
  (771185166, 771185169), (770551749, 770551752), (769917811, 769917814), (769283350, 769283353),
  (768648366, 768648369), (768012856, 768012859) ]
/-- Chunk 35 of `solRatios_r1024`. -/
def solRatios_r1024_c35 : List (IvInt) := [(767376821, 767376824), (766740258, 766740261),
  (766103166, 766103169), (765465543, 765465546), (764827389, 764827392), (764188702, 764188705),
  (763549481, 763549484), (762909724, 762909727), (762269431, 762269434), (761628599, 761628602),
  (760987227, 760987230), (760345315, 760345318) ]
/-- Chunk 36 of `solRatios_r1024`. -/
def solRatios_r1024_c36 : List (IvInt) := [(759702860, 759702863), (759059861, 759059864),
  (758416317, 758416320), (757772227, 757772230), (757127588, 757127591), (756482401, 756482404),
  (755836662, 755836665), (755190372, 755190375), (754543528, 754543531), (753896129, 753896132),
  (753248173, 753248176), (752599660, 752599663) ]
/-- Chunk 37 of `solRatios_r1024`. -/
def solRatios_r1024_c37 : List (IvInt) := [(751950587, 751950590), (751300954, 751300957),
  (750650758, 750650761), (749999999, 750000002), (749348674, 749348677), (748696783, 748696786),
  (748044324, 748044327), (747391295, 747391298), (746737695, 746737698), (746083523, 746083526),
  (745428776, 745428779), (744773454, 744773457) ]
/-- Chunk 38 of `solRatios_r1024`. -/
def solRatios_r1024_c38 : List (IvInt) := [(744117555, 744117558), (743461077, 743461080),
  (742804019, 742804022), (742146379, 742146382), (741488156, 741488159), (740829348, 740829351),
  (740169954, 740169957), (739509971, 739509974), (738849400, 738849403), (738188237, 738188240),
  (737526481, 737526484), (736864131, 736864134) ]
/-- Chunk 39 of `solRatios_r1024`. -/
def solRatios_r1024_c39 : List (IvInt) := [(736201185, 736201188), (735537642, 735537645),
  (734873500, 734873503), (734208756, 734208759), (733543411, 733543414), (732877461, 732877464),
  (732210906, 732210909), (731543743, 731543746), (730875971, 730875974), (730207589, 730207592),
  (729538594, 729538597), (728868985, 728868988) ]
/-- Chunk 40 of `solRatios_r1024`. -/
def solRatios_r1024_c40 : List (IvInt) := [(728198761, 728198764), (727527919, 727527922),
  (726856458, 726856461), (726184376, 726184379), (725511671, 725511674), (724838343, 724838346),
  (724164388, 724164391), (723489805, 723489808), (722814593, 722814596), (722138749, 722138752),
  (721462272, 721462275), (720785161, 720785164) ]
/-- Chunk 41 of `solRatios_r1024`. -/
def solRatios_r1024_c41 : List (IvInt) := [(720107412, 720107415), (719429026, 719429029),
  (718749999, 718750002), (718070329, 718070332), (717390016, 717390019), (716709057, 716709060),
  (716027451, 716027454), (715345195, 715345198), (714662288, 714662291), (713978727, 713978730),
  (713294512, 713294515), (712609639, 712609642) ]
/-- Chunk 42 of `solRatios_r1024`. -/
def solRatios_r1024_c42 : List (IvInt) := [(711924108, 711924111), (711237916, 711237919),
  (710551061, 710551064), (709863542, 709863545), (709175356, 709175359), (708486502, 708486505),
  (707796977, 707796980) ]
/-- Group 0 of `solRatios_r1024`. -/
def solRatios_r1024_g0 : List (IvInt) := List.append (List.append (List.append (List.append
  (List.append (solRatios_r1024_c0) (solRatios_r1024_c1)) (List.append (solRatios_r1024_c2)
  (solRatios_r1024_c3))) (List.append (List.append (solRatios_r1024_c4) (solRatios_r1024_c5))
  (List.append (solRatios_r1024_c6) (solRatios_r1024_c7)))) (List.append (List.append (List.append
  (solRatios_r1024_c8) (solRatios_r1024_c9)) (List.append (solRatios_r1024_c10)
  (solRatios_r1024_c11))) (List.append (List.append (solRatios_r1024_c12) (solRatios_r1024_c13))
  (List.append (solRatios_r1024_c14) (solRatios_r1024_c15))))) (List.append (List.append
  (List.append (List.append (solRatios_r1024_c16) (solRatios_r1024_c17)) (List.append
  (solRatios_r1024_c18) (solRatios_r1024_c19))) (List.append (List.append (solRatios_r1024_c20)
  (solRatios_r1024_c21)) (List.append (solRatios_r1024_c22) (solRatios_r1024_c23)))) (List.append
  (List.append (List.append (solRatios_r1024_c24) (solRatios_r1024_c25)) (List.append
  (solRatios_r1024_c26) (solRatios_r1024_c27))) (List.append (List.append (solRatios_r1024_c28)
  (solRatios_r1024_c29)) (List.append (solRatios_r1024_c30) (solRatios_r1024_c31)))))
/-- Group 1 of `solRatios_r1024`. -/
def solRatios_r1024_g1 : List (IvInt) := List.append (List.append (List.append
  (solRatios_r1024_c32) (solRatios_r1024_c33)) (List.append (solRatios_r1024_c34) (List.append
  (solRatios_r1024_c35) (solRatios_r1024_c36)))) (List.append (List.append (solRatios_r1024_c37)
  (List.append (solRatios_r1024_c38) (solRatios_r1024_c39))) (List.append (solRatios_r1024_c40)
  (List.append (solRatios_r1024_c41) (solRatios_r1024_c42))))
/-- Stratum angle-ratio intervals for WKB `r = 1024`. -/
def solRatios_r1024 : List (IvInt) := List.append (solRatios_r1024_g0) (solRatios_r1024_g1)
/-- Chunk 0 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c0 : List (IvInt × IvInt) := [((979882788, 979882789), (199573847, 199573848)
  ), ((979902368, 979902369), (199477689, 199477691)),
  ((979921947, 979921949), (199381482, 199381484)),
  ((979941527, 979941528), (199285227, 199285228)),
  ((979961107, 979961109), (199188922, 199188924)),
  ((979980687, 979980689), (199092568, 199092570)) ]
/-- Chunk 1 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c1 : List (IvInt × IvInt) := [((980000268, 980000269), (198996165, 198996167)
  ), ((980019848, 980019849), (198899712, 198899714)),
  ((980039429, 980039430), (198803211, 198803213)),
  ((980059009, 980059011), (198706660, 198706662)),
  ((980078590, 980078591), (198610059, 198610061)),
  ((980098171, 980098172), (198513408, 198513410)) ]
/-- Chunk 2 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c2 : List (IvInt × IvInt) := [((980117752, 980117753), (198416709, 198416711)
  ), ((980137333, 980137335), (198319959, 198319961)),
  ((980156915, 980156916), (198223160, 198223162)),
  ((980176496, 980176497), (198126310, 198126312)),
  ((980196078, 980196079), (198029411, 198029413)),
  ((980215659, 980215661), (197932462, 197932464)) ]
/-- Chunk 3 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c3 : List (IvInt × IvInt) := [((980235241, 980235242), (197835462, 197835464)
  ), ((980254823, 980254824), (197738413, 197738415)),
  ((980274405, 980274407), (197641313, 197641315)),
  ((980293988, 980293989), (197544163, 197544165)),
  ((980313570, 980313571), (197446963, 197446965)),
  ((980333152, 980333154), (197349712, 197349714)) ]
/-- Chunk 4 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c4 : List (IvInt × IvInt) := [((980352735, 980352736), (197252410, 197252412)
  ), ((980372318, 980372319), (197155058, 197155060)),
  ((980391901, 980391902), (197057656, 197057658)),
  ((980411484, 980411485), (196960202, 196960204)),
  ((980431067, 980431068), (196862698, 196862700)),
  ((980450650, 980450651), (196765143, 196765145)) ]
/-- Chunk 5 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c5 : List (IvInt × IvInt) := [((980470233, 980470235), (196667537, 196667539)
  ), ((980489817, 980489818), (196569879, 196569881)),
  ((980509401, 980509402), (196472171, 196472173)),
  ((980528984, 980528986), (196374411, 196374413)),
  ((980548568, 980548569), (196276600, 196276602)),
  ((980568152, 980568153), (196178738, 196178740)) ]
/-- Chunk 6 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c6 : List (IvInt × IvInt) := [((980587736, 980587738), (196080824, 196080826)
  ), ((980607321, 980607322), (195982859, 195982861)),
  ((980626905, 980626906), (195884842, 195884844)),
  ((980646490, 980646491), (195786774, 195786776)),
  ((980666074, 980666075), (195688654, 195688656)),
  ((980685659, 980685660), (195590481, 195590483)) ]
/-- Chunk 7 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c7 : List (IvInt × IvInt) := [((980705244, 980705245), (195492257, 195492259)
  ), ((980724829, 980724830), (195393982, 195393984)),
  ((980744414, 980744415), (195295654, 195295656)),
  ((980764000, 980764001), (195197273, 195197275)),
  ((980783585, 980783586), (195098841, 195098843)),
  ((980803171, 980803172), (195000356, 195000358)) ]
/-- Chunk 8 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c8 : List (IvInt × IvInt) := [((980822756, 980822758), (194901819, 194901821)
  ), ((980842342, 980842343), (194803230, 194803232)),
  ((980861928, 980861929), (194704587, 194704589)),
  ((980881514, 980881515), (194605893, 194605895)),
  ((980901100, 980901102), (194507145, 194507147)),
  ((980920687, 980920688), (194408345, 194408347)) ]
/-- Chunk 9 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c9 : List (IvInt × IvInt) := [((980940273, 980940274), (194309492, 194309494)
  ), ((980959860, 980959861), (194210586, 194210588)),
  ((980979447, 980979448), (194111627, 194111629)),
  ((980999034, 980999035), (194012615, 194012617)),
  ((981018621, 981018622), (193913549, 193913551)),
  ((981038208, 981038209), (193814431, 193814433)) ]
/-- Chunk 10 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c10 : List (IvInt × IvInt) := [((981057795, 981057796), (193715259, 193715261)
  ), ((981077382, 981077383), (193616034, 193616035)),
  ((981096970, 981096971), (193516755, 193516757)),
  ((981116557, 981116559), (193417422, 193417424)),
  ((981136145, 981136146), (193318036, 193318038)),
  ((981155733, 981155734), (193218596, 193218598)) ]
/-- Chunk 11 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c11 : List (IvInt × IvInt) := [((981175321, 981175322), (193119102, 193119104)
  ), ((981194909, 981194910), (193019555, 193019557)),
  ((981214498, 981214499), (192919953, 192919955)),
  ((981234086, 981234087), (192820297, 192820299)),
  ((981253675, 981253676), (192720587, 192720589)),
  ((981273263, 981273264), (192620823, 192620825)) ]
/-- Chunk 12 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c12 : List (IvInt × IvInt) := [((981292852, 981292853), (192521004, 192521006)
  ), ((981312441, 981312442), (192421131, 192421133)),
  ((981332030, 981332031), (192321204, 192321205)),
  ((981351619, 981351620), (192221221, 192221223)),
  ((981371209, 981371210), (192121185, 192121186)),
  ((981390798, 981390799), (192021093, 192021095)) ]
/-- Chunk 13 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c13 : List (IvInt × IvInt) := [((981410388, 981410389), (191920947, 191920948)
  ), ((981429977, 981429978), (191820745, 191820747)),
  ((981449567, 981449568), (191720489, 191720491)),
  ((981469157, 981469158), (191620177, 191620179)),
  ((981488747, 981488748), (191519810, 191519812)),
  ((981508337, 981508339), (191419388, 191419390)) ]
/-- Chunk 14 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c14 : List (IvInt × IvInt) := [((981527928, 981527929), (191318911, 191318913)
  ), ((981547518, 981547519), (191218378, 191218380)),
  ((981567109, 981567110), (191117789, 191117791)),
  ((981586700, 981586701), (191017145, 191017147)),
  ((981606290, 981606292), (190916445, 190916447)),
  ((981625881, 981625883), (190815690, 190815692)) ]
/-- Chunk 15 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c15 : List (IvInt × IvInt) := [((981645473, 981645474), (190714878, 190714880)
  ), ((981665064, 981665065), (190614011, 190614012)),
  ((981684655, 981684656), (190513087, 190513089)),
  ((981704247, 981704248), (190412107, 190412109)),
  ((981723838, 981723839), (190311071, 190311073)),
  ((981743430, 981743431), (190209979, 190209980)) ]
/-- Chunk 16 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c16 : List (IvInt × IvInt) := [((981763022, 981763023), (190108830, 190108832)
  ), ((981782614, 981782615), (190007624, 190007626)),
  ((981802206, 981802207), (189906362, 189906364)),
  ((981821798, 981821800), (189805044, 189805045)),
  ((981841391, 981841392), (189703668, 189703670)),
  ((981860983, 981860985), (189602235, 189602237)) ]
/-- Chunk 17 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c17 : List (IvInt × IvInt) := [((981880576, 981880577), (189500746, 189500748)
  ), ((981900169, 981900170), (189399200, 189399201)),
  ((981919762, 981919763), (189297596, 189297598)),
  ((981939355, 981939356), (189195935, 189195937)),
  ((981958948, 981958949), (189094217, 189094218)),
  ((981978541, 981978543), (188992441, 188992443)) ]
/-- Chunk 18 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c18 : List (IvInt × IvInt) := [((981998135, 981998136), (188890607, 188890609)
  ), ((982017728, 982017730), (188788717, 188788719)),
  ((982037322, 982037323), (188686768, 188686770)),
  ((982056916, 982056917), (188584762, 188584763)),
  ((982076510, 982076511), (188482697, 188482699)),
  ((982096104, 982096105), (188380575, 188380577)) ]
/-- Chunk 19 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c19 : List (IvInt × IvInt) := [((982115698, 982115699), (188278394, 188278396)
  ), ((982135293, 982135294), (188176156, 188176157)),
  ((982154887, 982154888), (188073859, 188073860)),
  ((982174482, 982174483), (187971503, 187971505)),
  ((982194076, 982194078), (187869089, 187869091)),
  ((982213671, 982213672), (187766617, 187766619)) ]
/-- Chunk 20 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c20 : List (IvInt × IvInt) := [((982233266, 982233267), (187664086, 187664088)
  ), ((982252861, 982252863), (187561496, 187561498)),
  ((982272457, 982272458), (187458847, 187458849)),
  ((982292052, 982292053), (187356139, 187356141)),
  ((982311648, 982311649), (187253373, 187253374)),
  ((982331243, 982331244), (187150546, 187150548)) ]
/-- Chunk 21 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c21 : List (IvInt × IvInt) := [((982350839, 982350840), (187047661, 187047663)
  ), ((982370435, 982370436), (186944717, 186944719)),
  ((982390031, 982390032), (186841713, 186841715)),
  ((982409627, 982409628), (186738649, 186738651)),
  ((982429223, 982429225), (186635526, 186635528)),
  ((982448820, 982448821), (186532343, 186532345)) ]
/-- Chunk 22 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c22 : List (IvInt × IvInt) := [((982468416, 982468418), (186429100, 186429102)
  ), ((982488013, 982488014), (186325797, 186325799)),
  ((982507610, 982507611), (186222435, 186222437)),
  ((982527207, 982527208), (186119012, 186119013)),
  ((982546804, 982546805), (186015528, 186015530)),
  ((982566401, 982566402), (185911985, 185911987)) ]
/-- Chunk 23 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c23 : List (IvInt × IvInt) := [((982585998, 982585999), (185808381, 185808383)
  ), ((982605596, 982605597), (185704716, 185704718)),
  ((982625193, 982625195), (185600991, 185600993)),
  ((982644791, 982644792), (185497205, 185497207)),
  ((982664389, 982664390), (185393358, 185393360)),
  ((982683987, 982683988), (185289450, 185289452)) ]
/-- Chunk 24 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c24 : List (IvInt × IvInt) := [((982703585, 982703586), (185185482, 185185483)
  ), ((982723183, 982723184), (185081452, 185081453)),
  ((982742782, 982742783), (184977360, 184977362)),
  ((982762380, 982762381), (184873208, 184873209)),
  ((982781979, 982781980), (184768994, 184768995)),
  ((982801577, 982801579), (184664718, 184664720)) ]
/-- Chunk 25 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c25 : List (IvInt × IvInt) := [((982821176, 982821177), (184560380, 184560382)
  ), ((982840775, 982840776), (184455981, 184455983)),
  ((982860374, 982860376), (184351520, 184351522)),
  ((982879974, 982879975), (184246997, 184246999)),
  ((982899573, 982899574), (184142412, 184142414)),
  ((982919173, 982919174), (184037765, 184037766)) ]
/-- Chunk 26 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c26 : List (IvInt × IvInt) := [((982938772, 982938773), (183933055, 183933057)
  ), ((982958372, 982958373), (183828283, 183828285)),
  ((982977972, 982977973), (183723448, 183723450)),
  ((982997572, 982997573), (183618551, 183618553)),
  ((983017172, 983017173), (183513591, 183513593)),
  ((983036772, 983036773), (183408568, 183408570)) ]
/-- Chunk 27 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c27 : List (IvInt × IvInt) := [((983056373, 983056374), (183303482, 183303484)
  ), ((983075973, 983075974), (183198333, 183198335)),
  ((983095574, 983095575), (183093121, 183093123)),
  ((983115175, 983115176), (182987846, 182987847)),
  ((983134776, 983134777), (182882507, 182882509)),
  ((983154377, 983154378), (182777105, 182777107)) ]
/-- Chunk 28 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c28 : List (IvInt × IvInt) := [((983173978, 983173979), (182671639, 182671641)
  ), ((983193579, 983193580), (182566109, 182566111)),
  ((983213181, 983213182), (182460516, 182460517)),
  ((983232782, 983232783), (182354858, 182354860)),
  ((983252384, 983252385), (182249137, 182249138)),
  ((983271986, 983271987), (182143351, 182143353)) ]
/-- Chunk 29 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c29 : List (IvInt × IvInt) := [((983291588, 983291589), (182037501, 182037503)
  ), ((983311190, 983311191), (181931587, 181931589)),
  ((983330792, 983330793), (181825608, 181825610)),
  ((983350394, 983350396), (181719565, 181719567)),
  ((983369997, 983369998), (181613456, 181613458)),
  ((983389600, 983389601), (181507283, 181507285)) ]
/-- Chunk 30 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c30 : List (IvInt × IvInt) := [((983409202, 983409203), (181401045, 181401047)
  ), ((983428805, 983428806), (181294742, 181294744)),
  ((983448408, 983448409), (181188374, 181188376)),
  ((983468011, 983468012), (181081941, 181081943)),
  ((983487615, 983487616), (180975442, 180975443)),
  ((983507218, 983507219), (180868877, 180868879)) ]
/-- Chunk 31 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c31 : List (IvInt × IvInt) := [((983526822, 983526823), (180762247, 180762249)
  ), ((983546425, 983546426), (180655551, 180655553)),
  ((983566029, 983566030), (180548789, 180548791)),
  ((983585633, 983585634), (180441961, 180441963)),
  ((983605237, 983605238), (180335067, 180335069)),
  ((983624841, 983624842), (180228107, 180228109)) ]
/-- Chunk 32 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c32 : List (IvInt × IvInt) := [((983644445, 983644446), (180121081, 180121083)
  ), ((983664050, 983664051), (180013988, 180013990)),
  ((983683654, 983683655), (179906828, 179906830)),
  ((983703259, 983703260), (179799602, 179799604)),
  ((983722864, 983722865), (179692309, 179692311)),
  ((983742469, 983742470), (179584949, 179584951)) ]
/-- Chunk 33 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c33 : List (IvInt × IvInt) := [((983762074, 983762075), (179477522, 179477523)
  ), ((983781679, 983781680), (179370027, 179370029)),
  ((983801284, 983801285), (179262466, 179262467)),
  ((983820890, 983820891), (179154836, 179154838)),
  ((983840495, 983840496), (179047140, 179047142)),
  ((983860101, 983860102), (178939376, 178939377)) ]
/-- Chunk 34 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c34 : List (IvInt × IvInt) := [((983879707, 983879708), (178831544, 178831545)
  ), ((983899313, 983899314), (178723644, 178723645)),
  ((983918919, 983918920), (178615675, 178615677)),
  ((983938525, 983938526), (178507639, 178507641)),
  ((983958132, 983958133), (178399535, 178399536)),
  ((983977738, 983977739), (178291362, 178291364)) ]
/-- Chunk 35 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c35 : List (IvInt × IvInt) := [((983997345, 983997346), (178183120, 178183122)
  ), ((984016951, 984016953), (178074810, 178074812)),
  ((984036558, 984036559), (177966431, 177966433)),
  ((984056165, 984056166), (177857983, 177857985)),
  ((984075772, 984075774), (177749466, 177749468)),
  ((984095380, 984095381), (177640880, 177640882)) ]
/-- Chunk 36 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c36 : List (IvInt × IvInt) := [((984114987, 984114988), (177532225, 177532227)
  ), ((984134595, 984134596), (177423500, 177423502)),
  ((984154202, 984154203), (177314706, 177314707)),
  ((984173810, 984173811), (177205842, 177205843)),
  ((984193418, 984193419), (177096908, 177096910)),
  ((984213026, 984213027), (176987904, 176987906)) ]
/-- Chunk 37 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c37 : List (IvInt × IvInt) := [((984232634, 984232635), (176878830, 176878832)
  ), ((984252242, 984252243), (176769686, 176769688)),
  ((984271851, 984271852), (176660472, 176660474)),
  ((984291459, 984291460), (176551187, 176551189)),
  ((984311068, 984311069), (176441832, 176441833)),
  ((984330677, 984330678), (176332405, 176332407)) ]
/-- Chunk 38 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c38 : List (IvInt × IvInt) := [((984350286, 984350287), (176222908, 176222910)
  ), ((984369895, 984369896), (176113341, 176113342)),
  ((984389504, 984389505), (176003701, 176003703)),
  ((984409113, 984409114), (175893991, 175893993)),
  ((984428723, 984428724), (175784209, 175784211)),
  ((984448332, 984448334), (175674356, 175674358)) ]
/-- Chunk 39 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c39 : List (IvInt × IvInt) := [((984467942, 984467943), (175564431, 175564433)
  ), ((984487552, 984487553), (175454435, 175454436)),
  ((984507162, 984507163), (175344366, 175344368)),
  ((984526772, 984526773), (175234225, 175234227)),
  ((984546382, 984546383), (175124012, 175124014)),
  ((984565993, 984565994), (175013727, 175013729)) ]
/-- Chunk 40 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c40 : List (IvInt × IvInt) := [((984585603, 984585604), (174903370, 174903372)
  ), ((984605214, 984605215), (174792940, 174792941)),
  ((984624824, 984624826), (174682436, 174682438)),
  ((984644435, 984644436), (174571861, 174571862)),
  ((984664046, 984664047), (174461212, 174461214)),
  ((984683657, 984683659), (174350490, 174350492)) ]
/-- Chunk 41 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c41 : List (IvInt × IvInt) := [((984703269, 984703270), (174239694, 174239696)
  ), ((984722880, 984722881), (174128826, 174128827)),
  ((984742492, 984742493), (174017883, 174017885)),
  ((984762103, 984762104), (173906867, 173906869)),
  ((984781715, 984781716), (173795777, 173795779)),
  ((984801327, 984801328), (173684613, 173684615)) ]
/-- Chunk 42 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c42 : List (IvInt × IvInt) := [((984820939, 984820940), (173573375, 173573377)
  ), ((984840551, 984840552), (173462063, 173462065)),
  ((984860163, 984860165), (173350676, 173350678)),
  ((984879776, 984879777), (173239215, 173239217)),
  ((984899388, 984899390), (173127679, 173127681)),
  ((984919001, 984919002), (173016068, 173016070)) ]
/-- Chunk 43 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c43 : List (IvInt × IvInt) := [((984938614, 984938615), (172904382, 172904384)
  ), ((984958227, 984958228), (172792621, 172792623)),
  ((984977840, 984977841), (172680785, 172680786)),
  ((984997453, 984997454), (172568873, 172568875)),
  ((985017067, 985017068), (172456885, 172456887)),
  ((985036680, 985036681), (172344822, 172344824)) ]
/-- Chunk 44 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c44 : List (IvInt × IvInt) := [((985056294, 985056295), (172232683, 172232685)
  ), ((985075907, 985075908), (172120468, 172120470)),
  ((985095521, 985095522), (172008177, 172008179)),
  ((985115135, 985115136), (171895809, 171895811)),
  ((985134749, 985134750), (171783365, 171783367)),
  ((985154363, 985154365), (171670844, 171670846)) ]
/-- Chunk 45 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c45 : List (IvInt × IvInt) := [((985173978, 985173979), (171558247, 171558249)
  ), ((985193592, 985193593), (171445572, 171445574)),
  ((985213207, 985213208), (171332821, 171332823)),
  ((985232822, 985232823), (171219992, 171219994)),
  ((985252437, 985252438), (171107086, 171107088)),
  ((985272052, 985272053), (170994102, 170994104)) ]
/-- Chunk 46 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c46 : List (IvInt × IvInt) := [((985291667, 985291668), (170881041, 170881043)
  ), ((985311282, 985311283), (170767902, 170767904)),
  ((985330897, 985330898), (170654684, 170654686)),
  ((985350513, 985350514), (170541389, 170541391)),
  ((985370128, 985370130), (170428015, 170428017)),
  ((985389744, 985389745), (170314563, 170314565)) ]
/-- Chunk 47 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c47 : List (IvInt × IvInt) := [((985409360, 985409361), (170201032, 170201034)
  ), ((985428976, 985428977), (170087423, 170087425)),
  ((985448592, 985448594), (169973734, 169973736)),
  ((985468209, 985468210), (169859967, 169859968)),
  ((985487825, 985487826), (169746119, 169746121)),
  ((985507442, 985507443), (169632193, 169632195)) ]
/-- Chunk 48 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c48 : List (IvInt × IvInt) := [((985527058, 985527060), (169518187, 169518189)
  ), ((985546675, 985546676), (169404101, 169404103)),
  ((985566292, 985566293), (169289936, 169289938)),
  ((985585909, 985585910), (169175690, 169175692)),
  ((985605526, 985605528), (169061364, 169061366)),
  ((985625144, 985625145), (168946958, 168946960)) ]
/-- Chunk 49 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c49 : List (IvInt × IvInt) := [((985644761, 985644762), (168832471, 168832473)
  ), ((985664379, 985664380), (168717904, 168717905)),
  ((985683997, 985683998), (168603255, 168603257)),
  ((985703614, 985703616), (168488525, 168488527)),
  ((985723232, 985723233), (168373715, 168373717)),
  ((985742850, 985742852), (168258823, 168258824)) ]
/-- Chunk 50 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c50 : List (IvInt × IvInt) := [((985762469, 985762470), (168143849, 168143851)
  ), ((985782087, 985782088), (168028793, 168028795)),
  ((985801706, 985801707), (167913656, 167913658)),
  ((985821324, 985821325), (167798437, 167798439)),
  ((985840943, 985840944), (167683135, 167683137)),
  ((985860562, 985860563), (167567751, 167567753)) ]
/-- Chunk 51 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c51 : List (IvInt × IvInt) := [((985880181, 985880182), (167452285, 167452286)
  ), ((985899800, 985899801), (167336735, 167336737)),
  ((985919419, 985919420), (167221103, 167221105)),
  ((985939039, 985939040), (167105388, 167105390)),
  ((985958658, 985958659), (166989589, 166989591)),
  ((985978278, 985978279), (166873708, 166873709)) ]
/-- Chunk 52 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c52 : List (IvInt × IvInt) := [((985997898, 985997899), (166757742, 166757744)
  ), ((986017518, 986017519), (166641693, 166641695)),
  ((986037138, 986037139), (166525560, 166525561)),
  ((986056758, 986056759), (166409342, 166409344)),
  ((986076378, 986076379), (166293040, 166293042)),
  ((986095998, 986096000), (166176654, 166176656)) ]
/-- Chunk 53 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c53 : List (IvInt × IvInt) := [((986115619, 986115620), (166060183, 166060185)
  ), ((986135240, 986135241), (165943628, 165943629)),
  ((986154861, 986154862), (165826987, 165826989)),
  ((986174481, 986174483), (165710261, 165710263)),
  ((986194103, 986194104), (165593450, 165593452)),
  ((986213724, 986213725), (165476553, 165476555)) ]
/-- Chunk 54 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c54 : List (IvInt × IvInt) := [((986233345, 986233346), (165359571, 165359572)
  ), ((986252967, 986252968), (165242502, 165242504)),
  ((986272588, 986272589), (165125348, 165125349)),
  ((986292210, 986292211), (165008107, 165008109)),
  ((986311832, 986311833), (164890780, 164890781)),
  ((986331454, 986331455), (164773366, 164773367)) ]
/-- Chunk 55 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c55 : List (IvInt × IvInt) := [((986351076, 986351077), (164655865, 164655867)
  ), ((986370698, 986370699), (164538277, 164538279)),
  ((986390320, 986390322), (164420602, 164420604)),
  ((986409943, 986409944), (164302840, 164302841)),
  ((986429566, 986429567), (164184990, 164184991)),
  ((986449188, 986449189), (164067052, 164067053)) ]
/-- Chunk 56 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c56 : List (IvInt × IvInt) := [((986468811, 986468812), (163949026, 163949028)
  ), ((986488434, 986488435), (163830912, 163830914)),
  ((986508057, 986508058), (163712710, 163712712)),
  ((986527681, 986527682), (163594419, 163594421)),
  ((986547304, 986547305), (163476039, 163476041)),
  ((986566928, 986566929), (163357571, 163357573)) ]
/-- Chunk 57 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c57 : List (IvInt × IvInt) := [((986586551, 986586552), (163239013, 163239015)
  ), ((986606175, 986606176), (163120367, 163120368)),
  ((986625799, 986625800), (163001630, 163001632)),
  ((986645423, 986645424), (162882804, 162882806)),
  ((986665047, 986665048), (162763888, 162763890)),
  ((986684671, 986684673), (162644882, 162644884)) ]
/-- Chunk 58 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c58 : List (IvInt × IvInt) := [((986704296, 986704297), (162525786, 162525788)
  ), ((986723920, 986723922), (162406599, 162406601)),
  ((986743545, 986743546), (162287321, 162287323)),
  ((986763170, 986763171), (162167953, 162167955)),
  ((986782795, 986782796), (162048493, 162048495)),
  ((986802420, 986802421), (161928943, 161928944)) ]
/-- Chunk 59 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c59 : List (IvInt × IvInt) := [((986822045, 986822046), (161809300, 161809302)
  ), ((986841671, 986841672), (161689566, 161689568)),
  ((986861296, 986861297), (161569740, 161569742)),
  ((986880922, 986880923), (161449822, 161449824)),
  ((986900547, 986900549), (161329812, 161329814)),
  ((986920173, 986920174), (161209709, 161209711)) ]
/-- Chunk 60 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c60 : List (IvInt × IvInt) := [((986939799, 986939800), (161089513, 161089515)
  ), ((986959425, 986959426), (160969225, 160969227)),
  ((986979052, 986979053), (160848843, 160848845)),
  ((986998678, 986998679), (160728368, 160728370)),
  ((987018304, 987018306), (160607800, 160607801)),
  ((987037931, 987037932), (160487137, 160487139)) ]
/-- Chunk 61 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c61 : List (IvInt × IvInt) := [((987057558, 987057559), (160366381, 160366383)
  ), ((987077185, 987077186), (160245530, 160245532)),
  ((987096812, 987096813), (160124585, 160124587)),
  ((987116439, 987116440), (160003546, 160003548)),
  ((987136066, 987136067), (159882411, 159882413)),
  ((987155694, 987155695), (159761182, 159761184)) ]
/-- Chunk 62 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c62 : List (IvInt × IvInt) := [((987175321, 987175322), (159639857, 159639859)
  ), ((987194949, 987194950), (159518437, 159518439)),
  ((987214577, 987214578), (159396921, 159396923)),
  ((987234204, 987234206), (159275309, 159275311)),
  ((987253833, 987253834), (159153601, 159153603)),
  ((987273461, 987273462), (159031797, 159031798)) ]
/-- Chunk 63 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c63 : List (IvInt × IvInt) := [((987293089, 987293090), (158909896, 158909897)
  ), ((987312717, 987312719), (158787898, 158787900)),
  ((987332346, 987332347), (158665803, 158665805)),
  ((987351975, 987351976), (158543611, 158543613)),
  ((987371604, 987371605), (158421321, 158421323)),
  ((987391233, 987391234), (158298934, 158298936)) ]
/-- Chunk 64 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c64 : List (IvInt × IvInt) := [((987410862, 987410863), (158176449, 158176451)
  ), ((987430491, 987430492), (158053865, 158053867)),
  ((987450120, 987450121), (157931184, 157931185)),
  ((987469750, 987469751), (157808403, 157808405)),
  ((987489379, 987489380), (157685524, 157685526)),
  ((987509009, 987509010), (157562546, 157562547)) ]
/-- Chunk 65 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c65 : List (IvInt × IvInt) := [((987528639, 987528640), (157439468, 157439470)
  ), ((987548269, 987548270), (157316291, 157316292)),
  ((987567899, 987567900), (157193014, 157193015)),
  ((987587529, 987587530), (157069636, 157069638)),
  ((987607160, 987607161), (156946159, 156946161)),
  ((987626790, 987626791), (156822581, 156822583)) ]
/-- Chunk 66 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c66 : List (IvInt × IvInt) := [((987646421, 987646422), (156698903, 156698905)
  ), ((987666052, 987666053), (156575123, 156575125)),
  ((987685682, 987685684), (156451243, 156451245)),
  ((987705313, 987705315), (156327261, 156327263)),
  ((987724945, 987724946), (156203177, 156203179)),
  ((987744576, 987744577), (156078991, 156078993)) ]
/-- Chunk 67 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c67 : List (IvInt × IvInt) := [((987764207, 987764208), (155954703, 155954705)
  ), ((987783839, 987783840), (155830313, 155830315)),
  ((987803471, 987803472), (155705820, 155705821)),
  ((987823102, 987823103), (155581224, 155581226)),
  ((987842734, 987842735), (155456525, 155456526)),
  ((987862366, 987862367), (155331722, 155331724)) ]
/-- Chunk 68 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c68 : List (IvInt × IvInt) := [((987881998, 987882000), (155206816, 155206818)
  ), ((987901631, 987901632), (155081806, 155081808)),
  ((987921263, 987921264), (154956692, 154956693)),
  ((987940896, 987940897), (154831473, 154831475)),
  ((987960529, 987960530), (154706150, 154706151)),
  ((987980161, 987980162), (154580721, 154580723)) ]
/-- Chunk 69 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c69 : List (IvInt × IvInt) := [((987999794, 987999795), (154455188, 154455190)
  ), ((988019427, 988019429), (154329549, 154329551)),
  ((988039061, 988039062), (154203805, 154203806)),
  ((988058694, 988058695), (154077954, 154077956)),
  ((988078327, 988078329), (153951997, 153951999)),
  ((988097961, 988097962), (153825934, 153825936)) ]
/-- Chunk 70 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c70 : List (IvInt × IvInt) := [((988117595, 988117596), (153699764, 153699766)
  ), ((988137229, 988137230), (153573487, 153573489)),
  ((988156863, 988156864), (153447103, 153447105)),
  ((988176497, 988176498), (153320611, 153320613)),
  ((988196131, 988196132), (153194012, 153194013)),
  ((988215765, 988215767), (153067304, 153067306)) ]
/-- Chunk 71 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c71 : List (IvInt × IvInt) := [((988235400, 988235401), (152940488, 152940490)
  ), ((988255035, 988255036), (152813564, 152813565)),
  ((988274669, 988274670), (152686530, 152686532)),
  ((988294304, 988294305), (152559388, 152559390)),
  ((988313939, 988313940), (152432136, 152432138)),
  ((988333574, 988333576), (152304774, 152304776)) ]
/-- Chunk 72 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c72 : List (IvInt × IvInt) := [((988353210, 988353211), (152177303, 152177304)
  ), ((988372845, 988372846), (152049721, 152049723)),
  ((988392481, 988392482), (151922028, 151922030)),
  ((988412116, 988412117), (151794225, 151794227)),
  ((988431752, 988431753), (151666311, 151666313)),
  ((988451388, 988451389), (151538285, 151538287)) ]
/-- Chunk 73 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c73 : List (IvInt × IvInt) := [((988471024, 988471025), (151410148, 151410150)
  ), ((988490660, 988490661), (151281899, 151281901)),
  ((988510297, 988510298), (151153538, 151153540)),
  ((988529933, 988529934), (151025064, 151025066)),
  ((988549570, 988549571), (150896477, 150896479)),
  ((988569206, 988569208), (150767778, 150767779)) ]
/-- Chunk 74 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c74 : List (IvInt × IvInt) := [((988588843, 988588844), (150638964, 150638966)
  ), ((988608480, 988608481), (150510038, 150510039)),
  ((988628117, 988628118), (150380997, 150380999)),
  ((988647755, 988647756), (150251842, 150251844)),
  ((988667392, 988667393), (150122573, 150122574)),
  ((988687029, 988687031), (149993188, 149993190)) ]
/-- Chunk 75 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c75 : List (IvInt × IvInt) := [((988706667, 988706668), (149863689, 149863691)
  ), ((988726305, 988726306), (149734074, 149734076)),
  ((988745943, 988745944), (149604343, 149604345)),
  ((988765581, 988765582), (149474497, 149474499)),
  ((988785219, 988785220), (149344534, 149344536)),
  ((988804857, 988804858), (149214454, 149214456)) ]
/-- Chunk 76 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c76 : List (IvInt × IvInt) := [((988824495, 988824497), (149084258, 149084259)
  ), ((988844134, 988844135), (148953944, 148953946)),
  ((988863773, 988863774), (148823513, 148823514)),
  ((988883411, 988883412), (148692964, 148692965)),
  ((988903050, 988903051), (148562296, 148562298)),
  ((988922689, 988922690), (148431510, 148431512)) ]
/-- Chunk 77 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c77 : List (IvInt × IvInt) := [((988942328, 988942330), (148300606, 148300607)
  ), ((988961968, 988961969), (148169582, 148169584)),
  ((988981607, 988981608), (148038438, 148038440)),
  ((989001247, 989001248), (147907176, 147907177)),
  ((989020886, 989020888), (147775793, 147775794)),
  ((989040526, 989040527), (147644289, 147644291)) ]
/-- Chunk 78 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c78 : List (IvInt × IvInt) := [((989060166, 989060167), (147512665, 147512667)
  ), ((989079806, 989079807), (147380920, 147380922)),
  ((989099446, 989099448), (147249053, 147249055)),
  ((989119087, 989119088), (147117065, 147117067)),
  ((989138727, 989138728), (146984955, 146984957)),
  ((989158368, 989158369), (146852722, 146852724)) ]
/-- Chunk 79 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c79 : List (IvInt × IvInt) := [((989178009, 989178010), (146720367, 146720369)
  ), ((989197649, 989197650), (146587889, 146587891)),
  ((989217290, 989217291), (146455287, 146455289)),
  ((989236931, 989236933), (146322562, 146322564)),
  ((989256573, 989256574), (146189713, 146189714)),
  ((989276214, 989276215), (146056739, 146056741)) ]
/-- Chunk 80 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c80 : List (IvInt × IvInt) := [((989295856, 989295857), (145923640, 145923642)
  ), ((989315497, 989315498), (145790417, 145790419)),
  ((989335139, 989335140), (145657068, 145657070)),
  ((989354781, 989354782), (145523594, 145523596)),
  ((989374423, 989374424), (145389993, 145389995)),
  ((989394065, 989394066), (145256266, 145256268)) ]
/-- Chunk 81 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c81 : List (IvInt × IvInt) := [((989413707, 989413708), (145122413, 145122414)
  ), ((989433350, 989433351), (144988432, 144988434)),
  ((989452992, 989452993), (144854323, 144854325)),
  ((989472635, 989472636), (144720087, 144720089)),
  ((989492278, 989492279), (144585723, 144585725)),
  ((989511920, 989511922), (144451230, 144451232)) ]
/-- Chunk 82 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c82 : List (IvInt × IvInt) := [((989531564, 989531565), (144316608, 144316610)
  ), ((989551207, 989551208), (144181857, 144181859)),
  ((989570850, 989570851), (144046977, 144046979)),
  ((989590493, 989590495), (143911966, 143911968)),
  ((989610137, 989610138), (143776825, 143776827)),
  ((989629781, 989629782), (143641553, 143641555)) ]
/-- Chunk 83 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c83 : List (IvInt × IvInt) := [((989649424, 989649426), (143506151, 143506152)
  ), ((989669068, 989669070), (143370616, 143370618)),
  ((989688713, 989688714), (143234950, 143234952)),
  ((989708357, 989708358), (143099152, 143099154)),
  ((989728001, 989728002), (142963221, 142963223)),
  ((989747646, 989747647), (142827157, 142827159)) ]
/-- Chunk 84 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c84 : List (IvInt × IvInt) := [((989767290, 989767291), (142690960, 142690962)
  ), ((989786935, 989786936), (142554629, 142554631)),
  ((989806580, 989806581), (142418164, 142418166)),
  ((989826225, 989826226), (142281565, 142281566)),
  ((989845870, 989845871), (142144830, 142144832)),
  ((989865515, 989865516), (142007961, 142007962)) ]
/-- Chunk 85 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_c85 : List (IvInt × IvInt) := [((989885160, 989885161), (141870955, 141870957)
  ), ((989904806, 989904807), (141733814, 141733815)) ]
/-- Group 0 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_g0 : List (IvInt × IvInt) := List.append (List.append (List.append
  (List.append (List.append (solTrigIvs_r1024_c0) (solTrigIvs_r1024_c1)) (List.append
  (solTrigIvs_r1024_c2) (solTrigIvs_r1024_c3))) (List.append (List.append (solTrigIvs_r1024_c4)
  (solTrigIvs_r1024_c5)) (List.append (solTrigIvs_r1024_c6) (solTrigIvs_r1024_c7)))) (List.append
  (List.append (List.append (solTrigIvs_r1024_c8) (solTrigIvs_r1024_c9)) (List.append
  (solTrigIvs_r1024_c10) (solTrigIvs_r1024_c11))) (List.append (List.append (solTrigIvs_r1024_c12)
  (solTrigIvs_r1024_c13)) (List.append (solTrigIvs_r1024_c14) (solTrigIvs_r1024_c15)))))
  (List.append (List.append (List.append (List.append (solTrigIvs_r1024_c16)
  (solTrigIvs_r1024_c17)) (List.append (solTrigIvs_r1024_c18) (solTrigIvs_r1024_c19))) (List.append
  (List.append (solTrigIvs_r1024_c20) (solTrigIvs_r1024_c21)) (List.append (solTrigIvs_r1024_c22)
  (solTrigIvs_r1024_c23)))) (List.append (List.append (List.append (solTrigIvs_r1024_c24)
  (solTrigIvs_r1024_c25)) (List.append (solTrigIvs_r1024_c26) (solTrigIvs_r1024_c27))) (List.append
  (List.append (solTrigIvs_r1024_c28) (solTrigIvs_r1024_c29)) (List.append (solTrigIvs_r1024_c30)
  (solTrigIvs_r1024_c31)))))
/-- Group 1 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_g1 : List (IvInt × IvInt) := List.append (List.append (List.append
  (List.append (List.append (solTrigIvs_r1024_c32) (solTrigIvs_r1024_c33)) (List.append
  (solTrigIvs_r1024_c34) (solTrigIvs_r1024_c35))) (List.append (List.append (solTrigIvs_r1024_c36)
  (solTrigIvs_r1024_c37)) (List.append (solTrigIvs_r1024_c38) (solTrigIvs_r1024_c39))))
  (List.append (List.append (List.append (solTrigIvs_r1024_c40) (solTrigIvs_r1024_c41))
  (List.append (solTrigIvs_r1024_c42) (solTrigIvs_r1024_c43))) (List.append (List.append
  (solTrigIvs_r1024_c44) (solTrigIvs_r1024_c45)) (List.append (solTrigIvs_r1024_c46)
  (solTrigIvs_r1024_c47))))) (List.append (List.append (List.append (List.append
  (solTrigIvs_r1024_c48) (solTrigIvs_r1024_c49)) (List.append (solTrigIvs_r1024_c50)
  (solTrigIvs_r1024_c51))) (List.append (List.append (solTrigIvs_r1024_c52) (solTrigIvs_r1024_c53))
  (List.append (solTrigIvs_r1024_c54) (solTrigIvs_r1024_c55)))) (List.append (List.append
  (List.append (solTrigIvs_r1024_c56) (solTrigIvs_r1024_c57)) (List.append (solTrigIvs_r1024_c58)
  (solTrigIvs_r1024_c59))) (List.append (List.append (solTrigIvs_r1024_c60) (solTrigIvs_r1024_c61))
  (List.append (solTrigIvs_r1024_c62) (solTrigIvs_r1024_c63)))))
/-- Group 2 of `solTrigIvs_r1024`. -/
def solTrigIvs_r1024_g2 : List (IvInt × IvInt) := List.append (List.append (List.append
  (List.append (solTrigIvs_r1024_c64) (solTrigIvs_r1024_c65)) (List.append (solTrigIvs_r1024_c66)
  (List.append (solTrigIvs_r1024_c67) (solTrigIvs_r1024_c68)))) (List.append (List.append
  (solTrigIvs_r1024_c69) (List.append (solTrigIvs_r1024_c70) (solTrigIvs_r1024_c71))) (List.append
  (solTrigIvs_r1024_c72) (List.append (solTrigIvs_r1024_c73) (solTrigIvs_r1024_c74)))))
  (List.append (List.append (List.append (solTrigIvs_r1024_c75) (solTrigIvs_r1024_c76))
  (List.append (solTrigIvs_r1024_c77) (List.append (solTrigIvs_r1024_c78) (solTrigIvs_r1024_c79))))
  (List.append (List.append (solTrigIvs_r1024_c80) (List.append (solTrigIvs_r1024_c81)
  (solTrigIvs_r1024_c82))) (List.append (solTrigIvs_r1024_c83) (List.append (solTrigIvs_r1024_c84)
  (solTrigIvs_r1024_c85)))))
/-- Stratum `(cosIv, sinIv)` intervals for WKB `r = 1024`. -/
def solTrigIvs_r1024 : List (IvInt × IvInt) := List.append (solTrigIvs_r1024_g0) (List.append
  (solTrigIvs_r1024_g1) (solTrigIvs_r1024_g2))
/-- Chunk 0 of `solTailLbs_r1024`. -/
def solTailLbs_r1024_c0 : List (ℤ) := [999936921, 999933616, 999933414, 999929336, 999923352,
  999920716, 999908461, 999906513, 999895776, 999883524, 999877317, 999858683, 999856540,
  999829424, 999819304, 999802356, 999775812, 999769206, 999736274, 999726238]
/-- Chunk 1 of `solTailLbs_r1024`. -/
def solTailLbs_r1024_c1 : List (ℤ) := [999636770, 999620640, 999535489, 999511374, 999473021,
  999449602, 999442993, 999408476, 999401848, 999328379, 999315474, 999200219, 999176326,
  999108229, 999064991, 999028003, 998989385, 998959411, 998950505, 998929494]
/-- Chunk 2 of `solTailLbs_r1024`. -/
def solTailLbs_r1024_c2 : List (ℤ) := [998918785, 998873719, 998853573, 998789011, 998748901,
  998709731, 998613182, 998590287, 998506909, 998503771, 998427785, 998425106, 998388360,
  998382655, 998356779, 998349186, 998320485, 998312121, 998291283, 998270791]
/-- Chunk 3 of `solTailLbs_r1024`. -/
def solTailLbs_r1024_c3 : List (ℤ) := [998249661, 998226939, 998223018, 998188775, 998187830,
  998168757, 998166137, 998153325, 998150237, 998147192, 998143686, 998140859, 998137824,
  998135272, 998131537, 998130993, 998117490, 998117241, 998112696, 998103514]
/-- Chunk 4 of `solTailLbs_r1024`. -/
def solTailLbs_r1024_c4 : List (ℤ) := [998097126, 998088096, 998087481, 998072565, 998070939,
  998054717, 998052907, 998044988, 998032784, 998027958, 998007666, 998007655, 997989013,
  997980754, 997966766, 997948593, 997947829, 997931744, 997930516, 997916749]
/-- Chunk 5 of `solTailLbs_r1024`. -/
def solTailLbs_r1024_c5 : List (ℤ) := [997912294, 997907829, 997902000, 997901668, 997892573,
  997891362, 997884951, 997882878, 997881486, 997876088, 997875026, 997870533, 997869748,
  997868775, 997867976, 997867871, 997865766, 997865089, 997863484, 997862324]
/-- Chunk 6 of `solTailLbs_r1024`. -/
def solTailLbs_r1024_c6 : List (ℤ) := [997861814, 997859930, 997859634, 997857636, 997855789,
  997854862, 997852958, 997852673, 997851343, 997851060, 997850334, 997849717, 997849141,
  997848244, 997847761, 997846888, 997846227, 997846192, 997845715, 997845517]
/-- Chunk 7 of `solTailLbs_r1024`. -/
def solTailLbs_r1024_c7 : List (ℤ) := [997845084, 997844600, 997844354, 997844015, 997843926,
  997843533, 997843461, 997843130, 997842548, 997842487, 997841575, 997840802, 997840576,
  997839689, 997839656, 997838890, 997838868, 997837981, 997837635, 997836914]
/-- Chunk 8 of `solTailLbs_r1024`. -/
def solTailLbs_r1024_c8 : List (ℤ) := [997835387, 997834851, 997833523, 997832662, 997832249,
  997831357, 997831117, 997829315, 997828847, 997827498, 997826351, 997826192, 997824641,
  997823944, 997823495, 997822946, 997822923, 997822304, 997821370, 997820869]
/-- Chunk 9 of `solTailLbs_r1024`. -/
def solTailLbs_r1024_c9 : List (ℤ) := [997819387, 997819374, 997819122, 997818717, 997818591,
  997818526, 997818439, 997818120, 997818046, 997817750, 997817712, 997817673, 997816892,
  997816892, 997816708, 997816535, 997815661, 997815270, 997815144, 997814350]
/-- Chunk 10 of `solTailLbs_r1024`. -/
def solTailLbs_r1024_c10 : List (ℤ) := [997813389, 997813375, 997812409, 997812108, 997811739,
  997810633, 997810343, 997809406, 997808905, 997808342, 997806910, 997806893, 997804391,
  997803795, 997803085, 997801172, 997801112, 997799606, 997798855, 997797433]
/-- Chunk 11 of `solTailLbs_r1024`. -/
def solTailLbs_r1024_c11 : List (ℤ) := [997795791, 997795438, 997793830, 997793263, 997792611,
  997791910, 997791638, 997788725, 997788600, 997786483, 997785155, 997784278, 997780620,
  997780301, 997778343, 997776479, 997775941, 997772778, 997772350, 997769873]
/-- Chunk 12 of `solTailLbs_r1024`. -/
def solTailLbs_r1024_c12 : List (ℤ) := [997766945, 997766447, 997761211, 997760956, 997757049,
  997753505, 997752661, 997746289, 997745556, 997740845, 997736038, 997735473, 997725821,
  997723835, 997718290, 997709885, 997709570, 997700147, 997694651, 997691597]
/-- Chunk 13 of `solTailLbs_r1024`. -/
def solTailLbs_r1024_c13 : List (ℤ) := [997680139, 997679549, 997670606, 997662452, 997660192,
  997644176, 997641894, 997632077, 997620032, 997619165, 997604431, 997598866, 997593208,
  997575493, 997574345, 997560507, 997550607, 997548252, 997531851, 997529238]
/-- Chunk 14 of `solTailLbs_r1024`. -/
def solTailLbs_r1024_c14 : List (ℤ) := [997517777, 997500810, 997499841, 997480540, 997472534,
  997466537, 997445439, 997443875, 997429914, 997415254, 997413619, 997392713, 997386035,
  997377823, 997358662, 997357552, 997341404, 997327902, 997325550, 997306902]
/-- Chunk 15 of `solTailLbs_r1024`. -/
def solTailLbs_r1024_c15 : List (ℤ) := [997302137, 997294673, 997277876, 997277060, 997262720,
  997252088, 997248811, 997229246, 997225743, 997214893, 997197569, 997196528, 997181319,
  997172743, 997170596, 997153128, 997148653, 997140713, 997123884, 997123157]
/-- Chunk 16 of `solTailLbs_r1024`. -/
def solTailLbs_r1024_c16 : List (ℤ) := [997113978, 997106812, 997106069, 997091455, 997088059,
  997082788, 997070581, 997070188, 997060091, 997050272, 997048910, 997035625, 997033002,
  997027250, 997020443, 997018808, 997016282, 997006264, 997005499, 996997093]
/-- Chunk 17 of `solTailLbs_r1024`. -/
def solTailLbs_r1024_c17 : List (ℤ) := [996994076, 996992192, 996986794, 996984328, 996980734,
  996976120, 996975807, 996974190, 996970634, 996969982, 996966793, 996965692, 996965299,
  996962100, 996962042, 996961743, 996959834, 996959818, 996958514, 996957443]
/-- Chunk 18 of `solTailLbs_r1024`. -/
def solTailLbs_r1024_c18 : List (ℤ) := [996957433, 996956563, 996956271, 996956248, 996955662,
  996955471, 996955363, 996954716, 996954619, 996954591, 996954421, 996954377, 996954260,
  996954244, 996954215, 996954208, 996954081, 996953984, 996953630, 996953500]
/-- Chunk 19 of `solTailLbs_r1024`. -/
def solTailLbs_r1024_c19 : List (ℤ) := [996953028, 996951816, 996951575, 996951238, 996949788,
  996949722, 996948843, 996948080, 996947935, 996946277, 996944677, 996944384, 996940992,
  996939072, 996938236, 996934127, 996932344, 996931365, 996926390, 996924750]
/-- Chunk 20 of `solTailLbs_r1024`. -/
def solTailLbs_r1024_c20 : List (ℤ) := [996923307, 996919497, 996919081, 996917109, 996914367,
  996914139, 996910810, 996908017, 996907630, 996903232, 996899564, 996899070, 996893286,
  996889601, 996888765, 996882238, 996879233, 996878032, 996871388, 996868847]
/-- Chunk 21 of `solTailLbs_r1024`. -/
def solTailLbs_r1024_c21 : List (ℤ) := [996867047, 996861334, 996859447, 996857568, 996851812,
  996850235, 996848138, 996842951, 996841649, 996839578, 996833713, 996833126, 996830728,
  996827476, 996827276, 996825425, 996822645, 996822134, 996818647, 996813714]
/-- Chunk 22 of `solTailLbs_r1024`. -/
def solTailLbs_r1024_c22 : List (ℤ) := [996813158, 996809574, 996803648, 996802836, 996799772,
  996794977, 996794391, 996791602, 996787163, 996786688, 996783524, 996779469, 996779067,
  996776155, 996772128, 996771319, 996768269, 996763773, 996763206, 996759714]
/-- Chunk 23 of `solTailLbs_r1024`. -/
def solTailLbs_r1024_c23 : List (ℤ) := [996754964, 996754450, 996751199, 996745959, 996745139,
  996741350, 996734789, 996733602, 996728561, 996716742, 996714464, 996709259, 996698190,
  996694784, 996691035, 996679364, 996676254, 996672805, 996662373, 996658929]
/-- Chunk 24 of `solTailLbs_r1024`. -/
def solTailLbs_r1024_c24 : List (ℤ) := [996655457, 996641272, 996634722, 996623091, 996574885,
  996548498, 996547756, 996544984, 996543761, 996542983, 996530885, 996513031, 996500582,
  996495374, 996489544, 996479826, 996470644, 996380188, 996299530, 996035360]
/-- Chunk 25 of `solTailLbs_r1024`. -/
def solTailLbs_r1024_c25 : List (ℤ) := [995924699, 995776152, 995346297, 995341922, 994184401,
  992364170, 990013355, 986915630, 984377198, 982030821, 978906226, 977898952]
/-- Certified suffix probability lower bounds for WKB `r = 1024`. -/
def solTailLbs_r1024 : List (ℤ) := List.append (List.append (List.append (List.append
  (solTailLbs_r1024_c0) (List.append (solTailLbs_r1024_c1) (solTailLbs_r1024_c2))) (List.append
  (solTailLbs_r1024_c3) (List.append (solTailLbs_r1024_c4) (solTailLbs_r1024_c5)))) (List.append
  (List.append (solTailLbs_r1024_c6) (List.append (solTailLbs_r1024_c7) (solTailLbs_r1024_c8)))
  (List.append (List.append (solTailLbs_r1024_c9) (solTailLbs_r1024_c10)) (List.append
  (solTailLbs_r1024_c11) (solTailLbs_r1024_c12))))) (List.append (List.append (List.append
  (solTailLbs_r1024_c13) (List.append (solTailLbs_r1024_c14) (solTailLbs_r1024_c15))) (List.append
  (solTailLbs_r1024_c16) (List.append (solTailLbs_r1024_c17) (solTailLbs_r1024_c18)))) (List.append
  (List.append (solTailLbs_r1024_c19) (List.append (solTailLbs_r1024_c20) (solTailLbs_r1024_c21)))
  (List.append (List.append (solTailLbs_r1024_c22) (solTailLbs_r1024_c23)) (List.append
  (solTailLbs_r1024_c24) (solTailLbs_r1024_c25)))))
/-- Stage specification for WKB Multi-pulse conveyor at `r = 1024`. -/
def solStage_r1024 : PulseM1StageSpec :=
  ⟨512, 200923, 1000000, solWkbToSwLPulses solWkbSched_r1024⟩
/-- Shared WKB midpoint checkpoint after pulse `2134` at `r = 1024`. -/
def solCkpt_r1024_s56 : List ℤ := List.append (List.append (List.append (List.append ([1685567,
  (-159042), (-1288438), (-651557), (-466047), 460778, 1606590, 1217631, (-185981), (-2595048),
  (-1998173), (-445084), (-36773), 3256266, 2267894, (-1458048), (-2029193), (-1846364),
  (-2251983), 3078499, 3062283, 1063836, 1833450, (-2719389), (-4258017), (-589918), 497456,
  3364480, 4364535, (-937583), (-1551748), (-3417098)]) (List.append ([(-4519755), 1777619,
  2437288, 2328277, 2755807, (-3873349), (-5948368), (-2899531), (-4839441), 6269430, 5527394,
  4796876, 4742198, (-5338169), (-4805234), (-3993550), (-2898082), 3949721, 3581001, 1998283,
  1348017, (-3712479), (-4330881), (-1898679), (-3338763), 4973228, 5510422, 4121784, 5635503,
  (-5881926), (-5148259), (-6280594)]) ([(-6735438), 2978736, 1380993, 6703833, 6533450, 629105,
  1136766, (-6547535), (-5366740), (-888309), (-510826), 4512606, 3468480, 232816, 1142856,
  (-3855562), (-4579648), (-1551358), (-2687737), 5545202, 6026475, 3102144, 4397376, (-4940580),
  (-3828784), (-5809884), (-7629837), 1861563, 982401, 8064392, 7121349, 643578]))) (List.append
  ([2415505, (-5951658), (-4204925), (-5002481), (-4894690), 3485690, 2185924, 4508972, 3679342,
  (-1062980), 185196, (-3908877), (-4356990), (-372531), (-362173), 4793096, 3225032, 782381,
  2129407, (-3333836), (-3450960), (-3308046), (-3307929), 3539070, 2064104, 3288636, 4043602,
  (-331930), 325279, (-4659978), (-3820724), (-848289)]) (List.append ([(-1632490), 2632349,
  1507497, 3070826, 2474222, (-1656725), (-708347), (-2146990), (-1607552), (-743694), (-539515),
  2029290, 2004222, 388832, 657376, (-356681), (-1252948), (-1339565), (-1579661), 1498843, 740997,
  808862, 2046423, 304811, 927190, (-2925317), (-1380683), (-689568), (-2273259), 724388, 948827,
  3171851]) ([1907400, (-69168), 1405008, (-2157192), (-2772292), (-1629436), (-1493983), 1744791,
  379773, 2694310, 3197003, (-863709), 113554, (-2463489), (-2459825), (-1990661), (-1812164),
  2447866, 1163996, 2522419, 3655767, 60630, 320373, (-3521540), (-2146428), (-2001147),
  (-3189306), 2307463, 985329, 3092434, 3246022, 1257479])))) (List.append (List.append ([1207546,
  (-3236455), (-1399961), (-1738943), (-2750026), 1334032, 917468, 2267111, 2003240, 1045732,
  938521, (-2550979), (-999779), (-1012863), (-2127797), 836931, 771828, 1866356, 1492108, 893981,
  1117023, (-2093126), (-684147), (-1020905), (-2188160), 422642, 159954, 1202034, 999818, 1408135,
  1009597, (-1173748)]) (List.append ([221835, (-861865), (-1267528), 139737, (-380704), (-84090),
  886466, 1100983, 145900, (-393935), 277046, (-1212358), (-807225), 177858, (-999645), 414196,
  837388, 851544, 999184, 486802, 154817, (-1390187), (-82297), (-954105), (-1188529), 645837,
  (-358677), 160480, 1405774, 204322, (-327077), (-64226)]) ([(-826602), (-807764), 191824, 545878,
  (-42262), 1106884, 439000, (-572281), 662314, (-738360), (-555921), 97085, (-997265), (-132817),
  541127, 101660, 197390, 617204, (-578845), (-128668), 120229, (-367188), 421827, 533901,
  (-355506), 310112, 18956, (-700816), 522752, (-191835), (-235282), 391537]))) (List.append
  ([(-587899), (-116227), 295601, (-195031), 351374, 26760, (-648465), (-53341), (-700631), 64300,
  239612, 729572, 757974, 694670, 137982, (-468021), (-202524), (-926683), (-120803), (-95745),
  14641, 870191, 138817, 192099, 334248, (-779287), (-162260), (-582925), (-779300), 483162,
  (-850678), 772337]) (List.append ([202409, 487739, 1296180, (-144577), 296936, (-612959),
  (-900270), (-348650), (-754286), 238244, 568821, 381549, 1159157, 11181, (-56809), (-705021),
  (-1060699), (-729873), (-812169), 284174, (-124188), 746041, 974800, 779384, 593891, (-138636),
  (-194988), (-936680), (-556673), (-318879), (-223632), 316084]) ([358538, 646467, 613098, 367290,
  394693, (-789430), (-900400), (-923141), (-242263), 36261, (-40415), 398139, 367178, 604193,
  95696, 57634, (-313821), (-287969), (-81986), 99, (-242583), (-195169), 425585, 397267, 118269,
  208006, 302647, 477793, 89028, (-143308), 196470, (-309063)]))))) (List.append (List.append
  (List.append ([(-439283), (-683039), (-176930), 80167, 14528, 407168, 956764, 134662, 180171,
  (-344169), 189505, (-592492), (-872048), (-306812), (-637865), 26615, (-121509), 746993, 564907,
  312449, 703767, (-485627), (-188911), (-547434), (-652990), (-3311), (-269429), 1024290, 316718,
  561278, 894665, 31753]) (List.append ([137734, (-793141), (-670231), (-663046), (-776051),
  322040, 239393, 1090939, 1124014, (-9466), 810373, (-655759), (-312801), (-970330), (-1052005),
  (-119997), (-162292), 890673, 471411, 925381, 1065181, (-462742), 117735, (-1203405), (-981015),
  (-173586), (-887394), 571805, 42395, 807208, 930733, 271954]) ([326234, (-495012), (-665918),
  (-554760), (-1018591), 140809, 224453, 1359734, 1128402, 394944, 674219, (-760860), (-549510),
  (-1258670), (-1239838), (-278513), (-697994), 1272859, 628397, 1155714, 1168161, 63024, 286288,
  (-1217387), (-875763), (-1000947), (-1015025), 621263, (-156448), 1304334, 1355731, 735268])))
  (List.append ([1186350, (-814177), (-516248), (-1536721), (-1655635), (-302153), (-648094),
  1434071, 979563, 1320151, 1766097, (-234332), 499947, (-1827382), (-1309497), (-1125801),
  (-1739342), 826679, (-126854), 1946110, 1596948, 829785, 1734987, (-1250172), (-402349),
  (-2315031), (-2280162), (-520722), (-1537325), 1682557, 781093, 2126643]) (List.append ([2179639,
  192812, 1399431, (-2040664), (-1129035), (-2296378), (-2458240), (-3670), (-979318), 2245368,
  1589664, 1835053, 2459214, (-539284), 566749, (-2676271), (-2159990), (-1771222), (-2656506),
  1267695, (-110208), 2885762, 2544217, 1298397, 2394241, (-1609266), (-324267), (-2810733),
  (-2643373), (-942660), (-2238039), 1900252]) ([699987, 3025982, 3013773, 716400, 2092288,
  (-2247034), (-1129984), (-2808665), (-2867608), (-296001), (-1467348), 2501582, 1612658, 2430194,
  3060475, (-260629), 1230767, (-3104939), (-2133064), (-2586385), (-3258101), 775185, (-940898),
  3059464, 2310296, 2288924, 3157904, (-994087), 691619, (-3319116), (-2570180), (-2008407)]))))
  (List.append (List.append ([(-3006046), 1165646, (-319771), 3266670, 2809962, 1816024, 3034793,
  (-1489340), (-19558), (-3341039), (-2877948), (-1534577), (-2652050), 1920932, 327302, 3294550,
  3017422, 1425418, 2612623, (-1997312), (-500052), (-3151773), (-2883221), (-976491), (-2365059),
  1988159, 610566, 3048126, 2930634, 817006, 2095914, (-2101298)]) (List.append ([(-971750),
  (-2963042), (-3147351), (-481436), (-1974793), 2508431, 1340149, 2866250, 3264153, 229062,
  1829380, (-2732403), (-1532403), (-2826022), (-3125707), (-236087), (-1464672), 2519666, 1250848,
  2540117, 3009706, 109309, 1511829, (-2607032), (-1392674), (-2763103), (-3194568), (-52669),
  (-1414275), 2679332, 1314803, 2208683]) ([2330235, 2131, 1348834, (-1935054), (-1413174),
  (-2301596), (-2778730), 335795, (-1156849), 2360259, 1433464, 2043876, 2693439, (-211140),
  837011, (-2461324), (-1534779), (-2082306), (-2843616), 256175, (-948664), 2630266, 1649054,
  1811797, 2442156, (-726241), 405635, (-2104490), (-1073554), (-1586407), (-1966851),
  (-269057)]))) (List.append (List.append ([(-1598494), 1252407, 428210, 2463163, 2353098, 299183,
  1035855, (-1952081), (-1320426), (-1267588), (-1571768), 56608, (-1121799), 1499737, 910212,
  1853530, 2039003, (-211253), 332711, (-1357389), (-600511), (-874735), (-1270694), (-285884),
  (-860273), 1474885, 1039265, 1058867, 1181798, 20172, 1026038, (-705489)]) ([(-569701),
  (-1629785), (-617162), (-1331524), (-994489), (-718078), 279618, (-18054), 483883, 731255,
  1310269, 232709, 440614, (-538404), (-1152036), (-2287668), (-2799796), (-3255137), (-4897189),
  (-4353572), (-5786488), (-5159678), (-7427238), (-5724644), (-8571665), (-6670476), (-9901081),
  (-6643063), (-10779219), (-6152114), (-8953304), (-3074810)])) (List.append ([(-3529539),
  5262071, 10929810, 21321722, 37412878, 47898129, 66310719, 67336742, 79091863, 74004575,
  105166127, 105701906, 151146109, 132797591, 150033979, 128198762, 198735222, 203725669,
  265173997, 212893738, 261931248, 239189092, 294745605, 252619224, 296129614, 249793224,
  282618060, 224184586, 224957774, 162585254, 143193388, 95027425]) ([75155569, 46708268, 34217909,
  20248407, 14030295, 7983339, 5272028, 2893708, 1830497, 972780, 590716, 304561, 178023, 89134,
  50329, 24499, 13357, 6298, 3306, 1483, 736, 288, 116, 25, 4, 0])))))
/-- Shared WKB terminal checkpoint after pulse `3100` at `r = 1024`. -/
def solCkptEnd_r1024 : List ℤ := List.append (List.append (List.append (List.append (List.append
  ([1202187, (-1192144), (-1373326), 445560, 56090, 652961, 1911548, (-640108), (-2361967),
  (-1090863), (-1203426), 1656059, 3085496, 1041371, (-930201), (-2530611), (-2083177), 1785216,
  3012254, 2339862, 858394, (-3126086), (-2979011), (-1371934), 511487, 4268163, 2986215,
  (-1627822), (-2734522), (-3528528), (-2123337), 3094504]) ([4121520, 2569322, 95521, (-3369288),
  (-4647863), 997393, 3007900, 5894319, 7401821, (-2817604), (-2864000), (-6734975), (-6312633),
  3336912, 3605124, 5103140, 3512485, (-3414913), (-3431259), (-2245710), (-1253187), 3745568,
  4528999, 1359989, 2186813, (-5576583), (-6513258), (-2220632), (-2825312), 7640243, 7547317,
  2998128])) (List.append ([3862765, (-6270436), (-5369012), (-4245260), (-5024529), 4223232,
  4379266, 4998448, 3696012, (-3991315), (-3750297), (-2561207), (-1533718), 3119656, 3360485,
  2208760, 2416251, (-4188278), (-5249351), (-3227610), (-3121376), 6016521, 5329960, 3916328,
  4980019, (-4859398), (-3947679), (-6789374), (-7107855), 3934199, 2726268, 6610251]) ([6304134,
  (-1230806), 1274927, (-6409439), (-5912608), (-1072032), (-1237694), 4855642, 3632370, 1213802,
  2058025, (-3328386), (-3849271), (-2074931), (-1814651), 4451062, 2984947, 1450191, 2503245,
  (-3063072), (-3386836), (-3373690), (-3020636), 3787275, 2608173, 2876304, 3803308, (-1412717),
  (-1388547), (-4460173), (-3791288), 971401]))) (List.append (List.append ([37334, 3097227,
  3081235, 1486091, 643289, (-2907350), (-2090102), (-861802), (-1532017), 888977, 1502380,
  1466922, 1164669, (-1676813), (-133814), (-735844), (-1579750), 932072, 1297840, 1748582, 825173,
  (-722765), 148275, (-2063687), (-3041915), (-404900), (-291567), 1515516, 1500578, 1854928,
  2397445, (-2283249)]) ([(-1085973), (-1569600), (-2563862), 232527, 749244, 3127182, 2268673,
  (-359735), 1223802, (-2430177), (-3213742), (-799207), (-1083029), 2215559, 1736475, 2645400,
  2283563, (-2015254), (-876602), (-2636115), (-3654757), (-104860), (-12637), 3536058, 2480229,
  1568529, 2409314, (-3113110), (-2075219), (-2495478), (-3458042), 399936])) (List.append
  ([777881, 3365654, 2183808, 463495, 1006847, (-2885916), (-2334234), (-730027), (-1981191),
  1086904, 1812961, 2025197, 1315949, (-541933), (-197295), (-2277957), (-1977894), 408642,
  (-1022204), 1407341, 2106040, 1092513, 938201, (-793770), (-873550), (-2050242), (-1094814),
  521460, (-889202), 1480476, 1518110, 303834]) ([832494, (-314613), (-935382), (-866725),
  (-219108), (-322506), 30843, 1413163, 331679, (-257774), 781428, (-967448), (-818826), (-113037),
  (-1071543), 150493, 698370, 968829, 972791, 537645, 85987, (-1396146), (-224368), (-930989),
  (-990411), 921254, (-281177), 274483, 1353091, (-432602), (-311827), 117749])))) (List.append
  (List.append (List.append ([(-1147753), (-135573), 514493, 264744, 810532, 754981, (-217356),
  (-687736), (-322225), (-938077), (-131050), 548894, (-426683), 911082, 209133, (-509312), 634127,
  (-133406), (-128882), 578771, (-377478), (-82416), 437694, (-520983), 402643, 245822, (-650962),
  260260, (-422433), (-362806), 455647, (-32218)]) ([297075, 520473, (-348948), (-60442),
  (-262971), (-234584), 524967, 384425, 659445, 245250, 21300, (-767604), (-568947), (-856351),
  (-201886), 444230, 167885, 933592, 126810, 87636, (-160178), (-855479), (-185183), (-147896),
  (-26387), 847532, 411793, 443343, 387064, (-831224), 172293, (-1135980)])) (List.append
  ([(-488178), (-201339), (-704101), 1097832, 351113, 583626, 721613, (-641319), 51702, (-789337),
  (-518525), 447509, (-200769), 1141695, 707173, (-13845), 683829, (-1090938), (-399650),
  (-762001), (-753573), 64397, (-393146), 1184521, 386895, 471445, 688858, (-663990), (-93092),
  (-634752), (-382609), 59437]) ([(-139952), 725875, 303380, 647098, 718988, (-511920), (-488831),
  (-1193290), (-242839), (-32059), (-109260), 384960, 323473, 628666, 97585, 54379, (-350514),
  (-241965), (-79542), 19827, (-294558), (-100829), 556456, 171237, 210396, 113958, 532464, 190705,
  (-35395), (-164968), (-110320), (-349217)]))) (List.append (List.append ([(-811918), (-17776),
  (-12203), 193863, 383099, 138700, 391830, (-883199), (-308152), (-236530), (-578506), (-228732),
  (-272971), 883224, 117954, 627437, 753846, (-66876), 96371, (-638318), (-748048), (-414182),
  (-360334), 453352, 404382, 512750, 918310, (-527692), 110490, (-634933), (-730974), (-516809)])
  ([(-484467), 642915, 387145, 859636, 832907, (-110550), (-68054), (-1114831), (-1123159),
  (-45206), (-771130), 701495, 467353, 906080, 1045765, (-165914), (-177499), (-887758), (-848057),
  (-599499), (-626562), 977842, 683156, 997664, 805159, (-586720), 91245, (-1051715), (-709606),
  (-387113), (-645950), 723181])) (List.append ([359020, 471762, 692132, (-521686), (-14767),
  (-1028187), (-1363054), 203209, (-289785), 1159878, 879333, 510171, 1033773, (-904172),
  (-244547), (-1246977), (-1451375), 30129, (-563455), 1188715, 739360, 906607, 1021475, (-721531),
  (-135338), (-1323105), (-1189074), 48134, (-652759), 1140023, 1086220, 1094920]) ([1315380,
  (-583166), (-398362), (-1571416), (-1664600), (-248016), (-440032), 1510935, 1275339, 1037263,
  1571801, (-838721), (-376181), (-1856825), (-1711351), (-231397), (-824763), 1740258, 1298156,
  1455432, 1640901, (-739098), (-139012), (-2133965), (-2259415), (-645184), (-1253367), 1974663,
  1284413, 1882701, 2206117, (-515459)]))))) (List.append (List.append (List.append (List.append
  ([221263, (-2176919), (-2165875), (-1196514), (-2016969), 1574779, 759389, 2338002, 2449401,
  (-34180), 768189, (-2303096), (-1909121), (-1641284), (-2337845), 1420613, 494208, 2749288,
  2910060, 442265, 1445256, (-2500208), (-1890216), (-2141485), (-2732596), 924635, (-114001),
  2827082, 2598532, 1059996, 2108406, (-2043137)]) ([(-1219805), (-2856358), (-3093313), 165725,
  (-1059001), 2881910, 2354205, 1903428, 2506987, (-1423343), (-575230), (-2842552), (-2886506),
  (-417909), (-1562391), 2644519, 2115609, 2584493, 3209204, (-969659), 171829, (-3344630),
  (-2851025), (-1455060), (-2427892), 2163790, 1148887, 3104920, 3387065, 150533, 1241975,
  (-3016123)])) (List.append ([(-2207945), (-2349460), (-3024850), 1274186, 115090, 3343732,
  3120974, 1299083, 2234904, (-2483569), (-1431715), (-2930492), (-3253909), 367917, (-987769),
  3159960, 2484688, 2227801, 2923781, (-1505526), (-295320), (-3177526), (-2926693), (-837271),
  (-2016720), 2340733, 1410747, 2770149, 3022546, (-346918), 834578, (-2848105)]) ([(-2497755),
  (-1866870), (-2674838), 1727041, 544263, 3145740, 3111834, 572574, 1782520, (-2744058),
  (-1824444), (-2735688), (-3138891), 694237, (-748309), 3043971, 2440035, 1593769, 2458238,
  (-1404958), (-417638), (-2982609), (-2929953), (-705360), (-1995096), 2365156, 1533834, 2802732,
  2997616, (-439691), 730964, (-2464304)]))) (List.append (List.append ([(-1764187), (-1522396),
  (-2203096), 842706, 184503, 2694509, 2713637, 685752, 1711196, (-1995216), (-1137485),
  (-2222243), (-2697710), 147023, (-609781), 2527233, 1928175, 1724421, 2617590, (-1140155),
  (-250982), (-2784836), (-2353681), (-679868), (-1470671), 2080559, 1194791, 1779298, 1909587,
  150572, 1269864, (-1525854)]) ([(-447171), (-1980834), (-2470215), (-385388), (-785715), 2238138,
  1844623, 1216968, 1240126, (-1346272), (-270091), (-1549425), (-1732570), (-711229), (-1400659),
  1517280, 1137686, 1705248, 1307465, (-493746), 263828, (-1027722), (-749420), (-1065254),
  (-1556962), 700853, 401731, 1423202, 1079775, 311322, 1002500, (-552329)])) (List.append
  ([(-295505), (-1424306), (-1082875), 65490, (-232575), 520556, 169754, 843878, 1094388,
  (-122079), (-34136), (-1069612), (-402013), (-602715), (-841399), 100644, (-8777), 889609,
  280994, 178477, 510622, 124856, (-84209), (-674215), (-363652), 128356, (-417588), 199722,
  261123, 760621, 263501, (-169831)]) ([260613, (-36750), (-161818), (-400026), 102213, 114876,
  (-174098), (-161177), 302647, (-6751), (-126840), (-82435), 148646, (-74835), (-33021), 150956,
  322888, (-232575), (-206921), (-215090), (-555121), (-154122), (-327277), 636177, 258881, 576566,
  938507, 165949, 461794, (-553899), (-176103), (-901091)])))) (List.append (List.append
  (List.append ([(-799352), (-25801), (-255580), 557134, 754728, 609013, 625859, (-357972), 131314,
  (-986953), (-827831), (-490244), (-1166523), 521127, 146135, 1361149, 1241916, 628352, 1235604,
  (-882820), (-237547), (-1395368), (-1471656), (-596845), (-1194712), 902843, 406373, 1640016,
  1512790, 382495, 1222883, (-1128161)]) ([(-413216), (-1392441), (-1369032), (-238541), (-599873),
  1051785, 930930, 1082207, 1254176, (-404400), 254156, (-1419177), (-1147593), (-842159),
  (-1444431), 589334, (-200169), 1594817, 1363000, 983825, 1643820, (-697923), 88189, (-1775604),
  (-1623548), (-999306), (-1639810), 912276, 63893, 1932795, 1672195, 823609])) (List.append
  ([1525938, (-1069469), (-241639), (-1890625), (-1753252), (-710071), (-1428002), 1270900, 431512,
  1721148, 1659633, 503191, 1278970, (-1304623), (-422083), (-1689853), (-1704303), (-393667),
  (-1193084), 1326802, 581482, 1583766, 1637760, 275152, 1107646, (-1282561), (-653825),
  (-1672154), (-1753082), 5004, (-766726), 1422985]) ([612248, 1272177, 1279027, 85479, 438629,
  (-1055530), (-859620), (-849531), (-1435347), 352543, (-622359), 1619307, 931484, 1445785,
  1687045, (-126151), 734820, (-1642281), (-943474), (-1626926), (-1811780), 87156, (-897513),
  1455515, 973423, 1469228, 1624989, (-74715), 762131, (-1453614), (-823451), (-1298587)])))
  (List.append (List.append ([(-1659844), 37114, (-688422), 1541029, 890221, 1272373, 1561443,
  (-75585), 630208, (-1443418), (-911384), (-1270459), (-1554350), 21241, (-899328), 1469826,
  944703, 1366947, 1622002, (-155118), 736842, (-1588101), (-986100), (-1383357), (-1685265),
  102228, (-709936), 1583249, 863712, 1444904, 1776664, 20850]) ([905583, (-1685023), (-975915),
  (-1600319), (-2001328), (-24006), (-1089661), 1919915, 1165370, 2193355, 2648936, 258771,
  1487568, (-2083270), (-931957), (-2266990), (-2436872), (-489994), (-1780097), 1814885, 676825,
  2429887, 2403178, 596120, 1660400, (-1739436), (-652050), (-2264911), (-2304382), (-668806),
  (-1732026), 1721314])) (List.append ([714789, 2420726, 2887138, 486733, 2513507, (-3179973),
  (-1236275), (-5312532), (-4474150), (-3616602), (-3650577), 68900, (-859180), 1144391, 1210255,
  1027507, 410041, (-867320), (-163159), (-3015638), (-1735616), (-3193865), (-2768804),
  (-1961792), (-2934173), 244968, (-2269919), 2395771, 306595, 2682416, 1590831, 2118768])
  ([(-2167757), 829182, (-9478160), 6402688, (-6302714), 16088129, (-2353733), 7355371, (-7526210),
  8998173, 8227541, 16181460, 12974691, 1626642, (-1316201), (-1962217), (-33979037), (-10299405),
  (-41420288), (-44526766), (-19241719), (-52420196), (-18785307), (-45285764), (-22147717),
  (-39179970), (-28539488), (-18304113), (-52873671), 5510721, (-31311432), 21140011])))))
/-- `L = 2` angle-ratio intervals on `[17, 20]`. -/
def solRatios_b17_20 : List (IvInt) := [(970142499, 974679436)]
/-- `L = 2` `(cosIv, sinIv)` intervals on `[17, 20]`. -/
def solTrigIvs_b17_20 : List (IvInt × IvInt) := [((996638891, 996638892), (81920205, 81920206) ),
  ((996806857, 996836500), (79479515, 79850418)) ]
/-- `L = 2` suffix probability lower bounds on `[17, 20]`. -/
def solTailLbs_b17_20 : List (ℤ) := [982220086, 956480161]
/-- `L = 2` angle-ratio intervals on `[21, 25]`. -/
def solRatios_b21_25 : List (IvInt) := [(975900071, 979795899)]
/-- `L = 2` `(cosIv, sinIv)` intervals on `[21, 25]`. -/
def solTrigIvs_b21_25 : List (IvInt × IvInt) := [((996638891, 996638892), (81920205, 81920206) ),
  ((996773263, 996798859), (79950203, 80268683)) ]
/-- `L = 2` suffix probability lower bounds on `[21, 25]`. -/
def solTailLbs_b21_25 : List (ℤ) := [981862628, 955133766]
/-- `L = 2` angle-ratio intervals on `[26, 31]`. -/
def solRatios_b26_31 : List (IvInt) := [(980580674, 983738755)]
/-- `L = 2` `(cosIv, sinIv)` intervals on `[26, 31]`. -/
def solTrigIvs_b26_31 : List (IvInt × IvInt) := [((996638891, 996638892), (81920205, 81920206) ),
  ((996747255, 996768096), (80332835, 80590997)) ]
/-- `L = 2` suffix probability lower bounds on `[26, 31]`. -/
def solTailLbs_b26_31 : List (ℤ) := [981769101, 954190703]
/-- `L = 2` angle-ratio intervals on `[34, 45]`. -/
def solRatios_b34_45 : List (IvInt) := [(985184365, 988826466)]
/-- `L = 2` `(cosIv, sinIv)` intervals on `[34, 45]`. -/
def solTrigIvs_b34_45 : List (IvInt × IvInt) := [((996638891, 996638892), (81920205, 81920206) ),
  ((996713541, 996737694), (80709167, 81006887)) ]
/-- `L = 2` suffix probability lower bounds on `[34, 45]`. -/
def solTailLbs_b34_45 : List (ℤ) := [980497106, 952298151]
/-- `L = 2` angle-ratio intervals on `[46, 63]`. -/
def solRatios_b46_63 : List (IvInt) := [(989070709, 992031747)]
/-- `L = 2` `(cosIv, sinIv)` intervals on `[46, 63]`. -/
def solTrigIvs_b46_63 : List (IvInt × IvInt) := [((996638891, 996638892), (81920205, 81920206) ),
  ((996692212, 996711919), (81026851, 81268892)) ]
/-- `L = 2` suffix probability lower bounds on `[46, 63]`. -/
def solTailLbs_b46_63 : List (ℤ) := [980466992, 951541762]
/-- `L = 2` angle-ratio intervals on `[66, 95]`. -/
def solRatios_b66_95 : List (IvInt) := [(992395325, 994722920)]
/-- `L = 2` `(cosIv, sinIv)` intervals on `[66, 95]`. -/
def solTrigIvs_b66_95 : List (IvInt × IvInt) := [((996638891, 996638892), (81920205, 81920206) ),
  ((996674251, 996689790), (81298610, 81488869)) ]
/-- `L = 2` suffix probability lower bounds on `[66, 95]`. -/
def solTailLbs_b66_95 : List (ℤ) := [980490537, 950930429]
/-- `L = 2` angle-ratio intervals on `[96, 127]`. -/
def solRatios_b96_127 : List (IvInt) := [(994778031, 996055213)]
/-- `L = 2` `(cosIv, sinIv)` intervals on `[96, 127]`. -/
def solTrigIvs_b96_127 : List (IvInt × IvInt) := [((996638891, 996638892), (81920205, 81920206) ),
  ((996665342, 996673884), (81493372, 81597769)) ]
/-- `L = 2` suffix probability lower bounds on `[96, 127]`. -/
def solTailLbs_b96_127 : List (ℤ) := [981103955, 950973579]
/-- `L = 2` angle-ratio intervals on `[130, 190]`. -/
def solRatios_b130_190 : List (IvInt) := [(996146420, 997364951)]
/-- `L = 2` `(cosIv, sinIv)` intervals on `[130, 190]`. -/
def solTrigIvs_b130_190 : List (IvInt × IvInt) := [((996638891, 996638892), (81920205, 81920206) ),
  ((996656571, 996664732), (81605223, 81704825)) ]
/-- `L = 2` suffix probability lower bounds on `[130, 190]`. -/
def solTailLbs_b130_190 : List (ℤ) := [980912894, 950556829]
/-- `L = 2` angle-ratio intervals on `[191, 255]`. -/
def solRatios_b191_255 : List (IvInt) := [(997378762, 998037291)]
/-- `L = 2` `(cosIv, sinIv)` intervals on `[191, 255]`. -/
def solTrigIvs_b191_255 : List (IvInt × IvInt) := [((996638891, 996638892), (81920205, 81920206) ),
  ((996652064, 996656480), (81705952, 81759780)) ]
/-- `L = 2` suffix probability lower bounds on `[191, 255]`. -/
def solTailLbs_b191_255 : List (ℤ) := [981250178, 950593922]
/-- `L = 2` angle-ratio intervals on `[258, 380]`. -/
def solRatios_b258_380 : List (IvInt) := [(998060132, 998683345)]
/-- `L = 2` `(cosIv, sinIv)` intervals on `[258, 380]`. -/
def solTrigIvs_b258_380 : List (IvInt × IvInt) := [((996638891, 996638892), (81920205, 81920206) ),
  ((996647731, 996651912), (81761646, 81812587)) ]
/-- `L = 2` suffix probability lower bounds on `[258, 380]`. -/
def solTailLbs_b258_380 : List (ℤ) := [981160889, 950390595]
/-- `L = 2` angle-ratio intervals on `[381, 511]`. -/
def solRatios_b381_511 : List (IvInt) := [(998686800, 999021049)]
/-- `L = 2` `(cosIv, sinIv)` intervals on `[381, 511]`. -/
def solTrigIvs_b381_511 : List (IvInt × IvInt) := [((996638891, 996638892), (81920205, 81920206) ),
  ((996645465, 996647709), (81812868, 81840190)) ]
/-- `L = 2` suffix probability lower bounds on `[381, 511]`. -/
def solTailLbs_b381_511 : List (ℤ) := [981337515, 950413224]
/-- `L = 2` angle-ratio intervals on `[514, 760]`. -/
def solRatios_b514_760 : List (IvInt) := [(999026762, 999341890)]
/-- `L = 2` `(cosIv, sinIv)` intervals on `[514, 760]`. -/
def solTrigIvs_b514_760 : List (IvInt × IvInt) := [((996638891, 996638892), (81920205, 81920206) ),
  ((996643311, 996645427), (81840656, 81866414)) ]
/-- `L = 2` suffix probability lower bounds on `[514, 760]`. -/
def solTailLbs_b514_760 : List (ℤ) := [981294421, 950312818]
/-- `L = 2` angle-ratio intervals on `[761, 1023]`. -/
def solRatios_b761_1023 : List (IvInt) := [(999342752, 999511123)]
/-- `L = 2` `(cosIv, sinIv)` intervals on `[761, 1023]`. -/
def solTrigIvs_b761_1023 : List (IvInt × IvInt) := [((996638891, 996638892), (81920205, 81920206)
  ), ((996642175, 996643306), (81866484, 81880247)) ]
/-- `L = 2` suffix probability lower bounds on `[761, 1023]`. -/
def solTailLbs_b761_1023 : List (ℤ) := [981384774, 950325176]
private abbrev _solAllCertsProp : Prop := (((((checkPulseExplicitStageTable 2 2 8201211 100000000
  65536 solRatios_r2 solTrigIvs_r2 solExplicitPulses_r2 3879 solTailLbs_r2 35113181000
  solM1VTable16 = true) ∧ ((checkPulseGrover1StepTable 33 solM1VTable16 = true) ∧
  (checkPulseGrover1StepTable 65 solM1VTable16 = true))) ∧ (((checkPulseGrover1StepTable 129
  solM1VTable16 = true) ∧ (checkPulseGrover1StepTable 257 solM1VTable16 = true)) ∧
  ((checkPulseGrover1StepTable 513 solM1VTable16 = true) ∧ (checkPulseL2RangeBucketTable 17 20
  4 8201211 100000000 65536 solRatios_b17_20 solTrigIvs_b17_20 solExplicitPulses_r2 12802229
  solTailLbs_b17_20 33744097473 solM1VTable16 = true)))) ∧ ((((checkPulseL2RangeBucketTable 21 25
  5 8201211 100000000 65536 solRatios_b21_25 solTrigIvs_b21_25 solExplicitPulses_r2 13769883
  solTailLbs_b21_25 33795162945 solM1VTable16 = true) ∧ (checkPulseL2RangeBucketTable 26 31 6
  8201211 100000000 65536 solRatios_b26_31 solTrigIvs_b26_31 solExplicitPulses_r2 14629694
  solTailLbs_b26_31 33830195848 solM1VTable16 = true)) ∧ ((checkPulseL2RangeBucketTable 34 45 12
  8201211 100000000 65536 solRatios_b34_45 solTrigIvs_b34_45 solExplicitPulses_r2 15276783
  solTailLbs_b34_45 33914188760 solM1VTable16 = true) ∧ (checkPulseL2RangeBucketTable 46 63 18
  8201211 100000000 65536 solRatios_b46_63 solTrigIvs_b46_63 solExplicitPulses_r2 16049858
  solTailLbs_b46_63 33943411315 solM1VTable16 = true))) ∧ (((checkPulseL2RangeBucketTable 66 95
  30 8201211 100000000 65536 solRatios_b66_95 solTrigIvs_b66_95 solExplicitPulses_r2 16739696
  solTailLbs_b66_95 33967170305 solM1VTable16 = true) ∧ (checkPulseL2RangeBucketTable 96 127 32
  8201211 100000000 65536 solRatios_b96_127 solTrigIvs_b96_127 solExplicitPulses_r2 17364360
  solTailLbs_b96_127 33960503358 solM1VTable16 = true)) ∧ ((checkPulseL2RangeBucketTable 130 190
  61 8201211 100000000 65536 solRatios_b130_190 solTrigIvs_b130_190 solExplicitPulses_r2 17618692
  solTailLbs_b130_190 33978824333 solM1VTable16 = true) ∧ (checkPulseL2RangeBucketTable 191 255
  65 8201211 100000000 65536 solRatios_b191_255 solTrigIvs_b191_255 solExplicitPulses_r2 17952973
  solTailLbs_b191_255 33974863512 solM1VTable16 = true))))) ∧ (((((checkPulseL2RangeBucketTable
  258 380 123 8201211 100000000 65536 solRatios_b258_380 solTrigIvs_b258_380 solExplicitPulses_r2
  18083202 solTailLbs_b258_380 33983839640 solM1VTable16 = true) ∧ (checkPulseL2RangeBucketTable
  381 511 131 8201211 100000000 65536 solRatios_b381_511 solTrigIvs_b381_511 solExplicitPulses_r2
  18256112 solTailLbs_b381_511 33981695987 solM1VTable16 = true)) ∧
  ((checkPulseL2RangeBucketTable 514 760 247 8201211 100000000 65536 solRatios_b514_760
  solTrigIvs_b514_760 solExplicitPulses_r2 18321996 solTailLbs_b514_760 33986138315 solM1VTable16 =
  true) ∧ (checkPulseL2RangeBucketTable 761 1023 263 8201211 100000000 65536 solRatios_b761_1023
  solTrigIvs_b761_1023 solExplicitPulses_r2 18409931 solTailLbs_b761_1023 33985024963 solM1VTable16
  = true))) ∧ (((solAllBelow 1025 0 (fun r ↦ solBleZ 0 (solM1VTable16 r)) = true) ∧ (solBleZ
  6426990820000000 (solM1VTable16 1) = true)) ∧ ((checkPulseRelCostM1 1 (solM1VTable16 2)
  94977285203 125000000000 = true) ∧ (checkPulseRelCostM1 2 (solM1VTable16 4) 179936242757
  250000000000 = true)))) ∧ ((((checkPulseRelCostM1 3 (solM1VTable16 8) 693944177707
  1000000000000 = true) ∧ (checkPulseRelCostM1 4 (solM1VTable16 16) 135807791521 200000000000 =
  true)) ∧ ((checkPulseRelCostM1 5 (solM1VTable16 32) 168366971699 250000000000 = true) ∧
  (checkPulseRelCostM1 6 (solM1VTable16 64) 132967045221 200000000000 = true))) ∧
  (((checkPulseRelCostM1 7 (solM1VTable16 128) 662863641537 1000000000000 = true) ∧
  (checkPulseRelCostM1 8 (solM1VTable16 256) 41251687977 62500000000 = true)) ∧
  ((checkPulseRelCostM1 9 (solM1VTable16 512) 10260007889 15625000000 = true) ∧
  (checkPulseRelCostM1 10 (solM1VTable16 1024) 654076085671 1000000000000 = true))))))
private theorem _solAllCerts_ok : _solAllCertsProp := by decide +kernel
theorem cert_solExplicit_r2 : checkPulseExplicitStageTable 2 2 8201211 100000000 65536
    solRatios_r2 solTrigIvs_r2 solExplicitPulses_r2 3879 solTailLbs_r2 35113181000 solM1VTable16 =
    true := _solAllCerts_ok.1.1.1.1
theorem cert_solGrover1_r33 : checkPulseGrover1StepTable 33 solM1VTable16 = true :=
    _solAllCerts_ok.1.1.1.2.1
theorem cert_solGrover1_r65 : checkPulseGrover1StepTable 65 solM1VTable16 = true :=
    _solAllCerts_ok.1.1.1.2.2
theorem cert_solGrover1_r129 : checkPulseGrover1StepTable 129 solM1VTable16 = true :=
    _solAllCerts_ok.1.1.2.1.1
theorem cert_solGrover1_r257 : checkPulseGrover1StepTable 257 solM1VTable16 = true :=
    _solAllCerts_ok.1.1.2.1.2
theorem cert_solGrover1_r513 : checkPulseGrover1StepTable 513 solM1VTable16 = true :=
    _solAllCerts_ok.1.1.2.2.1
theorem cert_solL2_b17_20 : checkPulseL2RangeBucketTable 17 20 4 8201211 100000000 65536
    solRatios_b17_20 solTrigIvs_b17_20 solExplicitPulses_r2 12802229 solTailLbs_b17_20 33744097473
    solM1VTable16 = true := _solAllCerts_ok.1.1.2.2.2
theorem cert_solL2_b21_25 : checkPulseL2RangeBucketTable 21 25 5 8201211 100000000 65536
    solRatios_b21_25 solTrigIvs_b21_25 solExplicitPulses_r2 13769883 solTailLbs_b21_25 33795162945
    solM1VTable16 = true := _solAllCerts_ok.1.2.1.1.1
theorem cert_solL2_b26_31 : checkPulseL2RangeBucketTable 26 31 6 8201211 100000000 65536
    solRatios_b26_31 solTrigIvs_b26_31 solExplicitPulses_r2 14629694 solTailLbs_b26_31 33830195848
    solM1VTable16 = true := _solAllCerts_ok.1.2.1.1.2
theorem cert_solL2_b34_45 : checkPulseL2RangeBucketTable 34 45 12 8201211 100000000 65536
    solRatios_b34_45 solTrigIvs_b34_45 solExplicitPulses_r2 15276783 solTailLbs_b34_45 33914188760
    solM1VTable16 = true := _solAllCerts_ok.1.2.1.2.1
theorem cert_solL2_b46_63 : checkPulseL2RangeBucketTable 46 63 18 8201211 100000000 65536
    solRatios_b46_63 solTrigIvs_b46_63 solExplicitPulses_r2 16049858 solTailLbs_b46_63 33943411315
    solM1VTable16 = true := _solAllCerts_ok.1.2.1.2.2
theorem cert_solL2_b66_95 : checkPulseL2RangeBucketTable 66 95 30 8201211 100000000 65536
    solRatios_b66_95 solTrigIvs_b66_95 solExplicitPulses_r2 16739696 solTailLbs_b66_95 33967170305
    solM1VTable16 = true := _solAllCerts_ok.1.2.2.1.1
theorem cert_solL2_b96_127 : checkPulseL2RangeBucketTable 96 127 32 8201211 100000000 65536
    solRatios_b96_127 solTrigIvs_b96_127 solExplicitPulses_r2 17364360 solTailLbs_b96_127
    33960503358 solM1VTable16 = true := _solAllCerts_ok.1.2.2.1.2
theorem cert_solL2_b130_190 : checkPulseL2RangeBucketTable 130 190 61 8201211 100000000 65536
    solRatios_b130_190 solTrigIvs_b130_190 solExplicitPulses_r2 17618692 solTailLbs_b130_190
    33978824333 solM1VTable16 = true := _solAllCerts_ok.1.2.2.2.1
theorem cert_solL2_b191_255 : checkPulseL2RangeBucketTable 191 255 65 8201211 100000000 65536
    solRatios_b191_255 solTrigIvs_b191_255 solExplicitPulses_r2 17952973 solTailLbs_b191_255
    33974863512 solM1VTable16 = true := _solAllCerts_ok.1.2.2.2.2
theorem cert_solL2_b258_380 : checkPulseL2RangeBucketTable 258 380 123 8201211 100000000 65536
    solRatios_b258_380 solTrigIvs_b258_380 solExplicitPulses_r2 18083202 solTailLbs_b258_380
    33983839640 solM1VTable16 = true := _solAllCerts_ok.2.1.1.1.1
theorem cert_solL2_b381_511 : checkPulseL2RangeBucketTable 381 511 131 8201211 100000000 65536
    solRatios_b381_511 solTrigIvs_b381_511 solExplicitPulses_r2 18256112 solTailLbs_b381_511
    33981695987 solM1VTable16 = true := _solAllCerts_ok.2.1.1.1.2
theorem cert_solL2_b514_760 : checkPulseL2RangeBucketTable 514 760 247 8201211 100000000 65536
    solRatios_b514_760 solTrigIvs_b514_760 solExplicitPulses_r2 18321996 solTailLbs_b514_760
    33986138315 solM1VTable16 = true := _solAllCerts_ok.2.1.1.2.1
theorem cert_solL2_b761_1023 : checkPulseL2RangeBucketTable 761 1023 263 8201211 100000000 65536
    solRatios_b761_1023 solTrigIvs_b761_1023 solExplicitPulses_r2 18409931 solTailLbs_b761_1023
    33985024963 solM1VTable16 = true := _solAllCerts_ok.2.1.1.2.2
theorem cert_solVTableNonneg : solAllBelow 1025 0 (fun r ↦ solBleZ 0 (solM1VTable16 r)) = true :=
    _solAllCerts_ok.2.1.2.1.1
theorem cert_solVTable_r1 : solBleZ 6426990820000000 (solM1VTable16 1) = true :=
    _solAllCerts_ok.2.1.2.1.2
theorem cert_solRelCost_k2 : checkPulseRelCostM1 1 (solM1VTable16 2) 94977285203 125000000000 =
    true := _solAllCerts_ok.2.1.2.2.1
theorem cert_solRelCost_k4 : checkPulseRelCostM1 2 (solM1VTable16 4) 179936242757 250000000000 =
    true := _solAllCerts_ok.2.1.2.2.2
theorem cert_solRelCost_k8 : checkPulseRelCostM1 3 (solM1VTable16 8) 693944177707 1000000000000 =
    true := _solAllCerts_ok.2.2.1.1.1
theorem cert_solRelCost_k16 : checkPulseRelCostM1 4 (solM1VTable16 16) 135807791521 200000000000
    = true := _solAllCerts_ok.2.2.1.1.2
theorem cert_solRelCost_k32 : checkPulseRelCostM1 5 (solM1VTable16 32) 168366971699 250000000000
    = true := _solAllCerts_ok.2.2.1.2.1
theorem cert_solRelCost_k64 : checkPulseRelCostM1 6 (solM1VTable16 64) 132967045221 200000000000
    = true := _solAllCerts_ok.2.2.1.2.2
theorem cert_solRelCost_k128 : checkPulseRelCostM1 7 (solM1VTable16 128) 662863641537
    1000000000000 = true := _solAllCerts_ok.2.2.2.1.1
theorem cert_solRelCost_k256 : checkPulseRelCostM1 8 (solM1VTable16 256) 41251687977 62500000000
    = true := _solAllCerts_ok.2.2.2.1.2
theorem cert_solRelCost_k512 : checkPulseRelCostM1 9 (solM1VTable16 512) 10260007889 15625000000
    = true := _solAllCerts_ok.2.2.2.2.1
theorem cert_solRelCost_k1024 : checkPulseRelCostM1 10 (solM1VTable16 1024) 654076085671
    1000000000000 = true := _solAllCerts_ok.2.2.2.2.2
end QuantumComputation.Specs.GroverFindAll.GroverM1PulseTable
end
