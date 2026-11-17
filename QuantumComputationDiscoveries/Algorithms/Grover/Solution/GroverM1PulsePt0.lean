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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.GroverM1PulsePt0Sub0
/-
# `m = 1` Multi-Pulse WKB Certificates Part 0 (`GroverM1PulsePt0`)
-/
@[expose] public section
namespace QuantumComputation.Specs.GroverFindAll.GroverM1PulsePt0
open QuantumComputation.Specs.GroverFindAll.SchurWeylLCert
  (IvInt swScale ceilDivScaleP ivAddIntP ivSubIntP headIvP)
open QuantumComputation.Specs.GroverFindAll.PulseM1
open QuantumComputation.Specs.GroverFindAll.GroverM1PulseTable
/-- Scalar-unpacked single-pulse WKB evaluator (`0` `SolWkbSched` unfolds in loop). -/
def solFastEvalWkbPulseRef (qR qL qTauNum qTauDen : ℕ)
    (qSOffQ qVBulkQ qAccelQ sMaxQ gTopQ phiTotQ km1Sq : ℤ)
    (sgArr : List (ℤ × ℤ)) (rbTree ulnTree uldTree vdTree : SolPairTree)
    (t : ℕ) : SolSparsePulse :=
  let tauNumZ := Int.ofNat qTauNum
  let tauDenZ := Int.ofNat qTauDen
  let rZ := Int.ofNat qR
  let tZ := Int.ofNat t
  solSeqInt (Int.ediv (Int.mul (Int.mul tZ tauNumZ) 1024) tauDenZ) fun phiQ ↦
    solSeqInt (Int.sub phiTotQ phiQ) fun dPhiQ ↦
      let accTerm := Int.ediv
        (Int.mul (Int.mul (Int.ediv (Int.mul qAccelQ sMaxQ) 1024) tZ) tZ) km1Sq
      solSeqInt (Int.add (Int.add qSOffQ (Int.ediv (Int.mul qVBulkQ phiQ) 1024)) accTerm)
        fun scQ ↦
          let hasLnch : Bool := solBleZ phiQ 36863
          let hasLand : Bool := solBleZ dPhiQ 36863
          let sLoQ : ℤ :=
            cond hasLnch 0
              (cond hasLand (solMinZ (Int.sub scQ 32768) (Int.sub sMaxQ 36864))
                (Int.sub scQ 32768))
          let sHiQ : ℤ :=
            cond hasLand sMaxQ
              (cond hasLnch (solMaxZ (Int.add scQ 32768) 37888)
                (Int.add scQ 32768))
          let lM1 := solMaxNat 1 (Nat.sub qL 1)
          let twoKR := Int.mul 2048 rZ
          let den4M := Int.mul 4194304 rZ
          let wLo : ℕ :=
            cond (solBleZ sLoQ 0) 1
              (cond (solBleZ twoKR sLoQ) lM1
                (let remLo := Int.sub twoKR sLoQ
                let qLo := Int.ediv (Int.mul remLo remLo) den4M
                let cand := Int.sub (Int.sub rZ qLo) 2
                solMinNat lM1 (solMaxNat 1 cand.toNat)))
          let wHi : ℕ :=
            cond (solBleZ sHiQ 0) 0
              (cond (solBleZ twoKR sHiQ) lM1
                (let remHi := Int.sub twoKR sHiQ
                let qHi := Int.ediv (Int.mul remHi remHi) den4M
                let cand := Int.add (Int.sub rZ qHi) 2
                solMinNat lM1 (solMaxNat 1 cand.toNat)))
          let (ilp, wlp) := cond hasLnch (solLinIdxFrac phiQ 36864 17) (0, 0)
          let (idp, wdp) := cond hasLand (solLinIdxFrac dPhiQ 36864 17) (0, 0)
          solLitNat wLo fun wLo' ↦
            solLitNat (cond (Nat.ble wLo' wHi) (Nat.sub (Nat.add wHi 1) wLo') 0)
              fun count ↦
                let vNum : ℤ :=
                  cond hasLand
                    (let (ivd, wvd) := solLinIdxFrac dPhiQ 36864 23
                    let rv := solLerp1024 (solLookupPair vdTree ivd) wvd
                    solSeqInt
                      (Int.ediv (Int.mul (Int.mul tauNumZ gTopQ) rv) (Int.mul 2048 tauDenZ))
                      fun thHv ↦
                        Int.add thHv (Int.ediv (Int.mul (Int.mul thHv thHv) thHv) 30000000000))
                    0
                solSeqInt vNum fun vNum' ↦
                  ⟨wLo',
                   solFastEvalWkbWindow tauNumZ tauDenZ scQ sMaxQ hasLnch hasLand
                     ilp wlp idp wdp rbTree ulnTree uldTree count (solDropSG wLo' sgArr),
                   vNum'⟩

private theorem solFastEvalWkbPulseRef_eq (q : SolWkbSched)
    (sMaxQ gTopQ phiTotQ km1Sq : ℤ) (sgArr : List (ℤ × ℤ))
    (rbTree ulnTree uldTree vdTree : SolPairTree) (t : ℕ) :
    solFastEvalWkbPulseRef q.r q.L q.tauNum q.tauDen q.sOffQ q.vBulkQ q.accelQ
        sMaxQ gTopQ phiTotQ km1Sq sgArr rbTree ulnTree uldTree vdTree t =
      solFastEvalWkbPulse q sMaxQ gTopQ phiTotQ km1Sq sgArr
        rbTree ulnTree uldTree vdTree t :=
  rfl

/-- Primitive-`Nat.rec` scalar-unpacked WKB evolution loop (`rem` first). -/
def solFastWkbEvolveLoopRef (qR qL qTauNum qTauDen qUvDen : ℕ)
    (qSOffQ qVBulkQ qAccelQ sMaxQ gTopQ phiTotQ km1Sq : ℤ)
    (sgArr : List (ℤ × ℤ)) (rbTree ulnTree uldTree vdTree : SolPairTree)
    (trigIvs : List (IvInt × IvInt)) :
    ℕ → ℕ → List ℤ → ℕ → ℕ → ℤ → List ℤ × ℕ × ℕ × ℤ
  | 0, _, cPref, hAct, rho, survUb => (cPref, hAct, rho, survUb)
  | rem + 1, t, cPref, hAct, rho, survUb =>
      match solFastEvalWkbPulseRef qR qL qTauNum qTauDen qSOffQ qVBulkQ qAccelQ
          sMaxQ gTopQ phiTotQ km1Sq sgArr rbTree ulnTree uldTree vdTree t with
      | ⟨wLo, uWin, vNum⟩ =>
          match solFastPulseStepL2 qL qUvDen trigIvs cPref hAct rho survUb
              ⟨wLo, uWin, vNum⟩ with
          | (cNext, hAct', rho', survUb') =>
              solSeqList cNext fun cNext' ↦
                solLitNat hAct' fun ha ↦
                  solLitNat rho' fun rh ↦
                    solSeqInt survUb' fun sv ↦
                      solLitNat (Nat.add t 1) fun tNext ↦
                        solFastWkbEvolveLoopRef qR qL qTauNum qTauDen qUvDen
                          qSOffQ qVBulkQ qAccelQ sMaxQ gTopQ phiTotQ km1Sq sgArr
                          rbTree ulnTree uldTree vdTree trigIvs rem tNext cNext' ha rh sv

private theorem solFastWkbEvolveLoopRef_eq (q : SolWkbSched)
    (sMaxQ gTopQ phiTotQ km1Sq : ℤ) (sgArr : List (ℤ × ℤ))
    (rbTree ulnTree uldTree vdTree : SolPairTree)
    (trigIvs : List (IvInt × IvInt)) :
    ∀ (rem t : ℕ) (cPref : List ℤ) (hAct rho : ℕ) (survUb : ℤ),
      solFastWkbEvolveLoopRef q.r q.L q.tauNum q.tauDen q.uvDen
          q.sOffQ q.vBulkQ q.accelQ sMaxQ gTopQ phiTotQ km1Sq sgArr
          rbTree ulnTree uldTree vdTree trigIvs rem t cPref hAct rho survUb =
        solFastWkbEvolveLoop q sMaxQ gTopQ phiTotQ km1Sq sgArr
          rbTree ulnTree uldTree vdTree trigIvs t rem cPref hAct rho survUb
  | 0, _, _, _, _, _ => rfl
  | rem + 1, t, cPref, hAct, rho, survUb => by
      unfold solFastWkbEvolveLoopRef solFastWkbEvolveLoop
      rw [solFastEvalWkbPulseRef_eq]
      rcases solFastEvalWkbPulse q sMaxQ gTopQ phiTotQ km1Sq sgArr
          rbTree ulnTree uldTree vdTree t with ⟨wLo, uWin, vNum⟩
      dsimp only
      rcases solFastPulseStepL2 q.L q.uvDen trigIvs cPref hAct rho survUb
          ⟨wLo, uWin, vNum⟩ with ⟨cNext, hAct', rho', survUb'⟩
      dsimp only
      simp only [solSeqList_eq, solLitNat_eq, solSeqInt_eq]
      exact solFastWkbEvolveLoopRef_eq q sMaxQ gTopQ phiTotQ km1Sq sgArr
        rbTree ulnTree uldTree vdTree trigIvs rem (Nat.add t 1) cNext hAct' rho' survUb'

/-- Scalar-unpacked boolean WKB slice checker (`= solFastCheckWkbSlice`). -/
def solFastCheckWkbSliceRef (q : SolWkbSched) (t len : ℕ)
    (trigIvs : List (IvInt × IvInt))
    (cIn : List ℤ) (hIn rhoIn : ℕ) (survIn : ℤ)
    (cOut : List ℤ) (hOut rhoOut : ℕ) (survOut : ℤ) : Bool :=
  solLitNat q.r fun qR ↦
    solLitNat q.L fun qL ↦
      solLitNat q.tauNum fun qTauNum ↦
        solLitNat q.tauDen fun qTauDen ↦
          solLitNat q.uvDen fun qUvDen ↦
            solSeqInt q.sOffQ fun qSOffQ ↦
              solSeqInt q.vBulkQ fun qVBulkQ ↦
                solSeqInt q.accelQ fun qAccelQ ↦
                  solWithTrigList trigIvs fun trigIvs' ↦
                    solWithIntList cIn fun cIn' ↦
                      solSeqList (solRevSGList (solBuildWkbSGRev qR 0 (Nat.add qL 1) []) [])
                        fun sgArr ↦
                        solSeqInt (sgArr.getD (Nat.sub qL 1) (0, 0)).1 fun sMaxQ ↦
                          let gTopNat := solFloorIsqrt
                            (Nat.div (Nat.mul 1048576 (Nat.sub qR (Nat.sub qL 1))) qR)
                          solSeqInt (Int.ofNat gTopNat) fun gTopQ ↦
                            let km1 := Int.ofNat (solMaxNat 1 (Nat.sub q.K 1))
                            solSeqInt (Int.mul km1 km1) fun km1Sq ↦
                              solSeqInt
                                (Int.ediv
                                  (Int.mul (Int.mul (Int.ofNat (Nat.sub q.K 1))
                                    (Int.ofNat qTauNum)) 1024)
                                  (Int.ofNat qTauDen))
                                fun phiTotQ ↦
                                  solWithPairTree (solBuildPairTree q.rBulkQ 8) fun rbTree ↦
                                    solWithPairTree (solBuildPairTree q.uLnchQ 10) fun ulnTree ↦
                                      solWithPairTree (solBuildPairTree q.uLandQ 10) fun uldTree ↦
                                        solWithPairTree (solBuildPairTree q.vDrainQ 6) fun vdTree ↦
                                          match solFastWkbEvolveLoopRef qR qL qTauNum qTauDen qUvDen
                                              qSOffQ qVBulkQ qAccelQ sMaxQ gTopQ phiTotQ km1Sq sgArr
                                              rbTree ulnTree uldTree vdTree trigIvs' len t
                                              cIn' hIn rhoIn survIn with
                                          | (c1, h1, rh1, sv1) =>
                                              solListIntBeq c1 cOut &&
                                              Nat.beq h1 hOut &&
                                              Nat.beq rh1 rhoOut &&
                                              solBeqZ sv1 survOut

private theorem solFastCheckWkbSliceRef_eq (q : SolWkbSched) (t len : ℕ)
    (trigIvs : List (IvInt × IvInt))
    (cIn : List ℤ) (hIn rhoIn : ℕ) (survIn : ℤ)
    (cOut : List ℤ) (hOut rhoOut : ℕ) (survOut : ℤ) :
    solFastCheckWkbSliceRef q t len trigIvs cIn hIn rhoIn survIn cOut hOut rhoOut survOut =
      solFastCheckWkbSlice q t len trigIvs cIn hIn rhoIn survIn cOut hOut rhoOut survOut := by
  unfold solFastCheckWkbSliceRef solFastCheckWkbSlice
  simp only [solLitNat_eq, solSeqInt_eq, solWithTrigList_eq, solWithIntList_eq,
    solSeqList_eq, solWithPairTree_eq, solFastWkbEvolveLoopRef_eq]

theorem solFastWkbStepRef_eq {q : SolWkbSched} {trigIvs : List (IvInt × IvInt)}
    {t len tNext : ℕ} {cIn : List ℤ} {hIn rhoIn : ℕ} {survIn : ℤ}
    {cOut : List ℤ} {hOut rhoOut : ℕ} {survOut : ℤ}
    (ht : t + len = tNext)
    (hprev : SolWkbRunPrefix q trigIvs t cIn hIn rhoIn survIn)
    (hfast : solFastCheckWkbSliceRef q t len trigIvs cIn hIn rhoIn survIn
      cOut hOut rhoOut survOut = true) :
    SolWkbRunPrefix q trigIvs tNext cOut hOut rhoOut survOut := by
  rw [solFastCheckWkbSliceRef_eq] at hfast
  exact solFastWkbStep_eq ht hprev hfast
/- ## Zero-Closure GMP WKB Slice Evaluator -/
/-- Zero-recheck WHNF `ℤ` unpacker (`1` `Int.casesOn` step). -/
def solKeepZ {α : Type*} (x : ℤ) (k : ℤ → α) : α :=
  @Int.casesOn (fun _ ↦ α) x (fun n ↦ k (Int.ofNat n)) (fun n ↦ k (Int.negSucc n))
private theorem solKeepZ_eq {α : Type*} (x : ℤ) (k : ℤ → α) : solKeepZ x k = k x := by
  cases x <;> rfl
/-- Zero-recheck WHNF `Prod` unpacker (`1` `Prod.casesOn` step). -/
def solForcePair {α β γ : Type*} (p : α × β) (k : α × β → γ) : γ :=
  @Prod.casesOn α β (fun _ ↦ γ) p fun a b ↦ k (a, b)
private theorem solForcePair_eq {α β γ : Type*} (p : α × β) (k : α × β → γ) :
    solForcePair p k = k p := by rcases p with ⟨a, b⟩; rfl
/-- Single-eval WHNF-forcing `IvInt` binder (`match` evaluates `iv` once). -/
def solBindIv {α : Type*} (iv : IvInt) (k : IvInt → α) : α :=
  match iv with | (lo, hi) => solKeepZ lo fun a ↦ solKeepZ hi fun b ↦ k (a, b)
private theorem solBindIv_eq {α : Type*} (iv : IvInt) (k : IvInt → α) : solBindIv iv k = k iv
    := by
  rcases iv with ⟨lo, hi⟩; simp only [solBindIv, solKeepZ_eq]
/-- Pure-GMP zero test on `ℤ` (`= solBeqZ x 0`, `0` `OfNat.ofNat`). -/
def solIsZeroZ : ℤ → Bool
  | .ofNat m => Nat.beq m 0
  | .negSucc _ => false
private theorem solIsZeroZ_eq (x : ℤ) : solIsZeroZ x = solBeqZ x 0 := by cases x <;> rfl
/-- Pure-GMP zero-interval test (`= solIvIsZero`, `0` `OfNat.ofNat`). -/
def solIvIsZeroZc : IvInt → Bool | (lo, hi) => solIsZeroZ lo && solIsZeroZ hi
private theorem solIvIsZero_eq (iv : IvInt) : solIvIsZeroZc iv = solIvIsZero iv := by
  rcases iv with ⟨lo, hi⟩; simp only [solIvIsZeroZc, solIvIsZero, solIsZeroZ_eq]
/-- Pure-GMP integer negation (`= Int.neg`). -/
def solGmpNegZ : ℤ → ℤ
  | .ofNat m => cond (Nat.ble m 0) (Int.ofNat 0) (solLitNat (Nat.sub m 1) Int.negSucc)
  | .negSucc m => solLitNat (Nat.add m 1) Int.ofNat
private theorem solGmpNegZ_eq (a : ℤ) : solGmpNegZ a = Int.neg a := by
  rcases a with (_ | k) | m
  · rfl
  · change cond false (Int.ofNat 0)
      (solLitNat (Nat.sub (k + 1) 1) Int.negSucc) = Int.negSucc k
    rw [Bool.cond_false, solLitNat_eq]; rfl
  · change solLitNat (Nat.add m 1) Int.ofNat = Int.ofNat (m + 1); rw [solLitNat_eq]
/-- Pure-GMP natural difference in `ℤ` (`= (m: ℤ) - (n: ℤ)`). -/
def solGmpSubNat (m n : ℕ) : ℤ :=
  cond (Nat.ble n m) (solLitNat (Nat.sub m n) Int.ofNat)
    (solLitNat (Nat.sub (Nat.sub n m) 1) Int.negSucc)
private theorem solGmpSubNat_eq (m n : ℕ) : solGmpSubNat m n = (m : ℤ) - (n : ℤ) := by
  unfold solGmpSubNat
  rw [natBle_eq_decide, solLitNat_eq, solLitNat_eq, solNatSub_eq, solNatSub_eq, solNatSub_eq]
  by_cases h : n ≤ m
  · rw [decide_eq_true h, Bool.cond_true, Int.ofNat_eq_natCast]; omega
  · rw [decide_eq_false h, Bool.cond_false]; omega
/-- Pure-GMP integer addition (`= Int.add`). -/
def solGmpAddZ : ℤ → ℤ → ℤ
  | .ofNat m, .ofNat n => solLitNat (Nat.add m n) Int.ofNat
  | .ofNat m, .negSucc n => solGmpSubNat m (Nat.add n 1)
  | .negSucc m, .ofNat n => solGmpSubNat n (Nat.add m 1)
  | .negSucc m, .negSucc n => solLitNat (Nat.add (Nat.add m n) 1) Int.negSucc
private theorem solGmpAddZ_eq (a b : ℤ) : solGmpAddZ a b = Int.add a b := by
  rw [solIntAdd_eq]
  rcases a with m | m <;> rcases b with n | n <;> dsimp only [solGmpAddZ] <;>
    simp only [solGmpSubNat_eq, solLitNat_eq, solNatAdd_eq, Int.ofNat_eq_natCast] <;> omega
/-- Single-pass pure-GMP integer subtraction (`= Int.sub`). -/
def solGmpSubZ : ℤ → ℤ → ℤ
  | .ofNat m, .ofNat n => solGmpSubNat m n
  | .ofNat m, .negSucc n => solLitNat (Nat.add (Nat.add m n) 1) Int.ofNat
  | .negSucc m, .ofNat n => solLitNat (Nat.add m n) Int.negSucc
  | .negSucc m, .negSucc n => solGmpSubNat n m
private theorem solGmpSubZ_eq (a b : ℤ) : solGmpSubZ a b = Int.sub a b := by
  rw [solIntSub_eq]
  rcases a with m | m <;> rcases b with n | n <;> dsimp only [solGmpSubZ] <;>
    simp only [solGmpSubNat_eq, solLitNat_eq, solNatAdd_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      <;> omega
/-- Pure-GMP integer multiplication (`= Int.mul`). -/
def solGmpMulZ : ℤ → ℤ → ℤ
  | .ofNat m, .ofNat n => solLitNat (Nat.mul m n) Int.ofNat
  | .ofNat m, .negSucc n => solGmpNegZ (solLitNat (Nat.mul m (Nat.add n 1)) Int.ofNat)
  | .negSucc m, .ofNat n => solGmpNegZ (solLitNat (Nat.mul (Nat.add m 1) n) Int.ofNat)
  | .negSucc m, .negSucc n => solLitNat (Nat.mul (Nat.add m 1) (Nat.add n 1)) Int.ofNat
private theorem solGmpMulZ_eq (a b : ℤ) : solGmpMulZ a b = Int.mul a b := by
  rw [solIntMul_eq]
  rcases a with m | m <;> rcases b with n | n <;> dsimp only [solGmpMulZ] <;>
    simp only [solGmpNegZ_eq, solIntNeg_eq, solLitNat_eq, solNatMul_eq, solNatAdd_eq,
      Int.ofNat_eq_natCast, Int.negSucc_eq] <;> push_cast <;> ring
/-- Pure-GMP Euclidean integer division (`= Int.ediv`). -/
def solGmpEdivZ : ℤ → ℤ → ℤ
  | .ofNat m, .ofNat n => solLitNat (Nat.div m n) Int.ofNat
  | .ofNat m, .negSucc n => solGmpNegZ (solLitNat (Nat.div m (Nat.add n 1)) Int.ofNat)
  | .negSucc m, .ofNat n => cond (Nat.ble n 0) (Int.ofNat 0) (solLitNat (Nat.div m n) Int.negSucc)
  | .negSucc m, .negSucc n => solLitNat (Nat.add (Nat.div m (Nat.add n 1)) 1) Int.ofNat
private theorem solGmpEdivZ_eq (a b : ℤ) : solGmpEdivZ a b = Int.ediv a b := by
  rcases a with m | m <;> rcases b with (_ | k) | n
  · exact solLitNat_eq (Nat.div m 0) Int.ofNat
  · exact solLitNat_eq (Nat.div m (k + 1)) Int.ofNat
  · exact (congrArg solGmpNegZ (solLitNat_eq _ Int.ofNat)).trans (solGmpNegZ_eq _)
  · exact rfl
  · exact solLitNat_eq (Nat.div m (k + 1)) Int.negSucc
  · exact solLitNat_eq (Nat.add (Nat.div m (Nat.add n 1)) 1) Int.ofNat
/-- Pure-GMP floor division by `swScale = 10^9` (`= Int.ediv a swScale`). -/
def solGmpDivScale : ℤ → ℤ
  | .ofNat m => solLitNat (Nat.div m 1000000000) Int.ofNat
  | .negSucc m => solLitNat (Nat.div m 1000000000) Int.negSucc
private theorem solGmpDivScale_eq (a : ℤ) : solGmpDivScale a = Int.ediv a swScale := by
  unfold swScale; rw [solIntEdiv_eq]
  rcases a with m | m <;> dsimp only [solGmpDivScale] <;>
    simp only [solLitNat_eq, solNatDiv_eq, Int.ofNat_eq_natCast, Int.negSucc_eq] <;> omega
/-- Single-pass pure-GMP ceiling division by `swScale = 10^9` (`= ceilDivScaleP`). -/
def solGmpCeilDivScale : ℤ → ℤ
  | .ofNat m => solLitNat (Nat.div (Nat.add m 999999999) 1000000000) Int.ofNat
  | .negSucc m =>
      cond (Nat.ble m 999999998) (Int.ofNat 0)
        (solLitNat (Nat.div (Nat.sub m 999999999) 1000000000) Int.negSucc)
private theorem solGmpCeilDivScale_eq (x : ℤ) : solGmpCeilDivScale x =
    SchurWeylLCert.ceilDivScaleP x := by
  unfold SchurWeylLCert.ceilDivScaleP swScale; rw [solIntNeg_eq, solIntNeg_eq, solIntEdiv_eq]
  rcases x with m | m
  · dsimp only [solGmpCeilDivScale]
    simp only [solLitNat_eq, solNatDiv_eq, solNatAdd_eq, Int.ofNat_eq_natCast]; omega
  · dsimp only [solGmpCeilDivScale]; rw [natBle_eq_decide]
    by_cases h : m ≤ 999999998
    · rw [decide_eq_true h, Bool.cond_true]; simp only [Int.ofNat_eq_natCast, Int.negSucc_eq]; omega
    · rw [decide_eq_false h, Bool.cond_false, solLitNat_eq, solNatDiv_eq, solNatSub_eq,
        Int.negSucc_eq]; omega
/-- Pure-GMP floor division by `2` (`= Int.ediv a 2`). -/
def solGmpDiv2 : ℤ → ℤ
  | .ofNat m => solLitNat (Nat.div m 2) Int.ofNat
  | .negSucc m => solLitNat (Nat.div m 2) Int.negSucc
private theorem solGmpDiv2_eq (a : ℤ) : solGmpDiv2 a = Int.ediv a 2 := by
  rw [solIntEdiv_eq]
  rcases a with m | m <;> dsimp only [solGmpDiv2] <;>
    simp only [solLitNat_eq, solNatDiv_eq, Int.ofNat_eq_natCast, Int.negSucc_eq] <;> omega
/-- Pure-GMP `10^9`-scale quotient interval (`= solFastScaleDivIv`). -/
def solFastScaleDivIvZc (loProd hiProd : ℤ) : IvInt :=
  solKeepZ (solGmpDivScale loProd) fun qLo ↦
    solKeepZ (solGmpCeilDivScale hiProd) fun qHi ↦ (qLo, qHi)
private theorem solFastScaleDivIvZc_eq (loProd hiProd : ℤ) : solFastScaleDivIvZc loProd hiProd =
    GroverM1PulsePt0.solFastScaleDivIv loProd hiProd := by
  unfold solFastScaleDivIvZc GroverM1PulsePt0.solFastScaleDivIv
  simp only [solKeepZ_eq, solSeqInt_eq, solGmpDivScale_eq, solGmpCeilDivScale_eq]
/-- Pure-GMP `10^9`-scale interval multiplication (`= solFastIvMul`). -/
def solFastIvMulZc : IvInt → IvInt → IvInt
  | (a1, a2), (b1, b2) =>
      cond (solBleZ a1 a2 && solBleZ b1 b2) (cond (solBleZ (Int.ofNat 0) a1)
          (cond (solBleZ (Int.ofNat 0) b1)
            (solFastScaleDivIvZc (solGmpMulZ a1 b1) (solGmpMulZ a2 b2))
            (cond (solBleZ b2 (Int.ofNat 0))
              (solFastScaleDivIvZc (solGmpMulZ a2 b1) (solGmpMulZ a1 b2))
              (solFastScaleDivIvZc (solGmpMulZ a2 b1) (solGmpMulZ a2 b2))))
          (cond (solBleZ a2 (Int.ofNat 0)) (cond (solBleZ (Int.ofNat 0) b1)
              (solFastScaleDivIvZc (solGmpMulZ a1 b2) (solGmpMulZ a2 b1))
              (cond (solBleZ b2 (Int.ofNat 0))
                (solFastScaleDivIvZc (solGmpMulZ a2 b2) (solGmpMulZ a1 b1))
                (solFastScaleDivIvZc (solGmpMulZ a1 b2) (solGmpMulZ a1 b1))))
            (solIvMul (a1, a2) (b1, b2))))
        (solIvMul (a1, a2) (b1, b2))
private theorem solFastIvMulZc_eq (a b : IvInt) : solFastIvMulZc a b =
    GroverM1PulsePt0.solFastIvMul a b := by
  rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩
  dsimp only [solFastIvMulZc, GroverM1PulsePt0.solFastIvMul]
  simp only [solFastScaleDivIvZc_eq, solGmpMulZ_eq]; rfl
/-- Direct pure-GMP floor of `-(p: ℤ) / 10^9` (`1` `solLitNat`, `0` intermediate `ℤ`). -/
def solScaleNegFloor (p : ℕ) : ℤ :=
  cond (Nat.ble p 0) (Int.ofNat 0) (solLitNat (Nat.div (Nat.sub p 1) 1000000000) Int.negSucc)
private theorem solScaleNegFloor_eq (p : ℕ) : solScaleNegFloor p = Int.ediv (-(p : ℤ)) swScale
    := by
  unfold swScale; rw [solIntEdiv_eq]
  rcases p with _ | k
  · rfl
  · change cond false (Int.ofNat 0)
      (solLitNat (Nat.div (Nat.sub (k + 1) 1) 1000000000) Int.negSucc) = _
    rw [Bool.cond_false, solLitNat_eq, solNatDiv_eq, solNatSub_eq, Int.negSucc_eq]; omega
/-- Direct pure-GMP ceiling of `-(p: ℤ) / 10^9` (`1` `solLitNat`, `0` intermediate `ℤ`). -/
def solScaleNegCeil (p : ℕ) : ℤ :=
  cond (Nat.ble p 999999999) (Int.ofNat 0)
    (solLitNat (Nat.div (Nat.sub p 1000000000) 1000000000) Int.negSucc)
private theorem solScaleNegCeil_eq (p : ℕ) : solScaleNegCeil p = SchurWeylLCert.ceilDivScaleP
    (-(p : ℤ)) := by
  unfold SchurWeylLCert.ceilDivScaleP swScale; rw [solIntNeg_eq, solIntNeg_eq, solIntEdiv_eq]
  dsimp only [solScaleNegCeil]; rw [natBle_eq_decide]
  by_cases h : p ≤ 999999999
  · rw [decide_eq_true h, Bool.cond_true, Int.ofNat_eq_natCast]; omega
  · rw [decide_eq_false h, Bool.cond_false, solLitNat_eq, solNatDiv_eq, solNatSub_eq,
      Int.negSucc_eq]; omega
/-- Fallback pure-GMP interval-by-scalar helper (`= solFastIvScaleZ`). -/
def solFastIvScaleZRef : IvInt → ℤ → IvInt
  | (a1, a2), c =>
      solKeepZ (solGmpMulZ a1 c) fun p1 ↦ solKeepZ (solGmpMulZ a2 c) fun p2 ↦
          cond (solBleZ p1 p2) (solFastScaleDivIvZc p1 p2) (solFastScaleDivIvZc p2 p1)
private theorem solFastIvScaleZRef_eq (a : IvInt) (c : ℤ) : solFastIvScaleZRef a c =
    GroverM1PulsePt0.solFastIvScaleZ a c := by
  rcases a with ⟨a1, a2⟩; dsimp only [solFastIvScaleZRef, GroverM1PulsePt0.solFastIvScaleZ]
  simp only [solKeepZ_eq, solSeqInt_eq, solGmpMulZ_eq, solFastScaleDivIvZc_eq]
/-- Fused 2-`solLitNat` pure-GMP `10^9`-scale interval-by-scalar multiplication. -/
def solFastIvScaleZZc : IvInt → ℤ → IvInt
  | (.ofNat m1, .ofNat m2), .ofNat n =>
      cond (Nat.ble m1 m2) (solLitNat (Nat.div (Nat.mul m1 n) 1000000000) fun q1 ↦
          solLitNat (Nat.div (Nat.add (Nat.mul m2 n) 999999999) 1000000000) fun q2 ↦
            (Int.ofNat q1, Int.ofNat q2))
        (solFastIvScaleZRef (.ofNat m1, .ofNat m2) (.ofNat n))
  | (.ofNat m1, .ofNat m2), .negSucc n =>
      cond (Nat.ble m1 m2) (solLitNat (Nat.add n 1) fun n1 ↦
          solKeepZ (solScaleNegFloor (Nat.mul m2 n1)) fun q1 ↦
            solKeepZ (solScaleNegCeil (Nat.mul m1 n1)) fun q2 ↦ (q1, q2))
        (solFastIvScaleZRef (.ofNat m1, .ofNat m2) (.negSucc n))
  | a, c => solFastIvScaleZRef a c
private theorem solFastIvScaleZZc_eq (a : IvInt) (c : ℤ) : solFastIvScaleZZc a c =
    GroverM1PulsePt0.solFastIvScaleZ a c := by
  rw [← solFastIvScaleZRef_eq]
  rcases a with ⟨m1 | m1, m2 | m2⟩
  · rcases c with n | n
    · dsimp only [solFastIvScaleZZc]; rw [natBle_eq_decide]
      by_cases h : m1 ≤ m2
      · rw [decide_eq_true h, Bool.cond_true]; dsimp only [solFastIvScaleZRef, solGmpMulZ]
        simp only [solLitNat_eq, solKeepZ_eq]; dsimp only [solBleZ]
        have hm : Nat.mul m1 n ≤ Nat.mul m2 n := by
          rw [solNatMul_eq, solNatMul_eq]; exact Nat.mul_le_mul_right n h
        rw [natBle_eq_decide, decide_eq_true hm, Bool.cond_true]
        dsimp only [solFastScaleDivIvZc, solGmpDivScale, solGmpCeilDivScale]
        simp only [solLitNat_eq, solKeepZ_eq]
      · rw [decide_eq_false h, Bool.cond_false]
    · dsimp only [solFastIvScaleZZc]; rw [natBle_eq_decide]
      by_cases h : m1 ≤ m2
      · have hfl (p : ℕ) :
            solScaleNegFloor p = solGmpDivScale (solGmpNegZ (Int.ofNat p)) := by
          rw [solScaleNegFloor_eq, solGmpDivScale_eq, solGmpNegZ_eq, solIntNeg_eq,
            Int.ofNat_eq_natCast]
        have hcl (p : ℕ) :
            solScaleNegCeil p = solGmpCeilDivScale (solGmpNegZ (Int.ofNat p)) := by
          rw [solScaleNegCeil_eq, solGmpCeilDivScale_eq, solGmpNegZ_eq, solIntNeg_eq,
            Int.ofNat_eq_natCast]
        rw [decide_eq_true h, Bool.cond_true, solLitNat_eq]
        dsimp only [solFastIvScaleZRef, solGmpMulZ, solFastScaleDivIvZc]
        simp only [solKeepZ_eq, solLitNat_eq, hfl, hcl]
        by_cases heq : m1 = m2
        · subst heq
          cases solBleZ (solGmpNegZ (Int.ofNat (Nat.mul m1 (Nat.add n 1))))
            (solGmpNegZ (Int.ofNat (Nat.mul m1 (Nat.add n 1)))) <;> rfl
        · have hm : m1 * (n + 1) < m2 * (n + 1) :=
            Nat.mul_lt_mul_of_pos_right (Nat.lt_of_le_of_ne h heq) (Nat.succ_pos n)
          have hlt : ¬ (solGmpNegZ (Int.ofNat (Nat.mul m1 (Nat.add n 1))) ≤
              solGmpNegZ (Int.ofNat (Nat.mul m2 (Nat.add n 1)))) := by
            simp only [solGmpNegZ_eq, solIntNeg_eq, solNatMul_eq, solNatAdd_eq,
              Int.ofNat_eq_natCast]; omega
          rw [solBleZ_eq_decide, decide_eq_false hlt, Bool.cond_false]
      · rw [decide_eq_false h, Bool.cond_false]
  · rfl
  · rfl
  · rfl
/-- WHNF-forced pure-GMP interval addition (`= ivAddIntP`). -/
def solIvAddGmp : IvInt → IvInt → IvInt
  | (alo, ahi), (blo, bhi) =>
      solKeepZ (solGmpAddZ alo blo) fun lo ↦
        solKeepZ (solGmpAddZ ahi bhi) fun hi ↦ (lo, hi)
private theorem solIvAddGmp_eq (a b : IvInt) : solIvAddGmp a b = SchurWeylLCert.ivAddIntP a b
    := by
  rcases a with ⟨alo, ahi⟩; rcases b with ⟨blo, bhi⟩
  dsimp only [solIvAddGmp, SchurWeylLCert.ivAddIntP]
  simp only [solKeepZ_eq, solGmpAddZ_eq]
/-- WHNF-forced pure-GMP interval subtraction (`= ivSubIntP`). -/
def solIvSubGmp : IvInt → IvInt → IvInt
  | (alo, ahi), (blo, bhi) =>
      solKeepZ (solGmpSubZ alo bhi) fun lo ↦
        solKeepZ (solGmpSubZ ahi blo) fun hi ↦ (lo, hi)
private theorem solIvSubGmp_eq (a b : IvInt) : solIvSubGmp a b = SchurWeylLCert.ivSubIntP a b
    := by
  rcases a with ⟨alo, ahi⟩; rcases b with ⟨blo, bhi⟩
  dsimp only [solIvSubGmp, SchurWeylLCert.ivSubIntP]
  simp only [solKeepZ_eq, solGmpSubZ_eq]
/-- Pure-GMP `10^9`-scale outward rational interval (`= solIvRatDiv`). -/
def solIvRatDivZc (num den : ℤ) : IvInt :=
  solKeepZ (solGmpMulZ num (Int.ofNat 1000000000)) fun sc ↦
    solKeepZ (solGmpEdivZ sc den) fun qLo ↦
      solKeepZ (solGmpNegZ (solGmpEdivZ (solGmpNegZ sc) den)) fun qHi ↦ (qLo, qHi)
private theorem solIvRatDivZc_eq (num den : ℤ) : solIvRatDivZc num den = solIvRatDiv num den := by
  unfold solIvRatDivZc solIvRatDiv swScale
  simp only [solKeepZ_eq, solSeqInt_eq, solGmpMulZ_eq, solGmpEdivZ_eq, solGmpNegZ_eq]
  rfl
/-- Pure-GMP `10^9`-scale Pythagorean `(cos, sin)` intervals (`= solIvPythag`). -/
def solIvPythagZc (uNum uDen : ℤ) : IvInt × IvInt :=
  solKeepZ (solGmpMulZ uDen uDen) fun dSq ↦ solKeepZ (solGmpMulZ uNum uNum) fun nSq ↦
      solKeepZ (solGmpAddZ dSq nSq) fun d ↦
        solForcePair (solIvRatDivZc (solGmpSubZ dSq nSq) d) fun cu ↦
          solForcePair (solIvRatDivZc (solGmpMulZ (solGmpMulZ (Int.ofNat 2) uNum) uDen) d)
            fun su ↦ (cu, su)
private theorem solIvPythagZc_eq (uNum uDen : ℤ) : solIvPythagZc uNum uDen = solIvPythag uNum uDen
    := by
  unfold solIvPythagZc solIvPythag
  simp only [solKeepZ_eq, solSeqInt_eq, solForcePair_eq, solSeqIv_eq, solGmpMulZ_eq,
    solGmpAddZ_eq, solGmpSubZ_eq, solIvRatDivZc_eq]; rfl
/-- Single-stratum WHNF-forced GMP Grover rotation step (`= solFastGroverStep`). -/
def solFastGroverStepZc (cw sw : IvInt) (ce co : ℤ) (rest : List IvInt) : List IvInt :=
  cond (solIsZeroZ ce && solIsZeroZ co)
    ((Int.ofNat 0, Int.ofNat 0) :: (Int.ofNat 0, Int.ofNat 0) :: rest)
    (solForcePair (solIvSubGmp (solFastIvScaleZZc cw ce) (solFastIvScaleZZc sw co)) fun e' ↦
        solForcePair (solIvAddGmp (solFastIvScaleZZc sw ce) (solFastIvScaleZZc cw co))
          fun o' ↦ e' :: o' :: rest)
private theorem solFastGroverStep_eq (cw sw : IvInt) (ce co : ℤ) (rest : List IvInt) :
    solFastGroverStepZc cw sw ce co rest = GroverM1PulsePt0.solFastGroverStep cw sw ce co rest
    := by
  unfold solFastGroverStepZc GroverM1PulsePt0.solFastGroverStep
  simp only [solIsZeroZ_eq, solForcePair_eq, solSeqIv_eq, solFastIvScaleZZc_eq,
    solIvSubGmp_eq, solIvAddGmp_eq]; rfl
/-- Multi-stratum WHNF-forced GMP Grover rotation walk (`= solFastGroverWalk`). -/
def solFastGroverWalkZc : ℕ → List (IvInt × IvInt) → List ℤ → List IvInt
  | 0, _, _ => []
  | k + 1, (cw, sw) :: ts', ce :: co :: cs' =>
      solFastGroverStepZc cw sw ce co (solFastGroverWalkZc k ts' cs')
  | k + 1, (cw, sw) :: ts', [ce] =>
      solFastGroverStepZc cw sw ce (Int.ofNat 0) (solFastGroverWalkZc k ts' [])
  | k + 1, _ :: ts', [] =>
      (Int.ofNat 0, Int.ofNat 0) :: (Int.ofNat 0, Int.ofNat 0) :: solFastGroverWalkZc k ts' []
  | k + 1, [], ce :: co :: cs' =>
      solFastGroverStepZc (Int.ofNat 0, Int.ofNat 0) (Int.ofNat 0, Int.ofNat 0) ce co
        (solFastGroverWalkZc k [] cs')
  | k + 1, [], [ce] =>
      solFastGroverStepZc (Int.ofNat 0, Int.ofNat 0) (Int.ofNat 0, Int.ofNat 0) ce (Int.ofNat 0)
        (solFastGroverWalkZc k [] [])
  | k + 1, [], [] =>
      (Int.ofNat 0, Int.ofNat 0) :: (Int.ofNat 0, Int.ofNat 0) :: solFastGroverWalkZc k [] []
private theorem solFastGroverWalkZc_eq : ∀ (k : ℕ) (ts : List (IvInt × IvInt)) (cs : List ℤ),
    solFastGroverWalkZc k ts cs = GroverM1PulsePt0.solFastGroverWalk k ts cs
  | 0, _, _ => rfl
  | k + 1, ts, cs => by
      rcases ts with _ | ⟨⟨cw, sw⟩, ts'⟩ <;> rcases cs with _ | ⟨ce, _ | ⟨co, cs'⟩⟩ <;>
        simp only [solFastGroverWalkZc, GroverM1PulsePt0.solFastGroverWalk,
          solFastGroverStep_eq, solFastGroverWalkZc_eq k] <;> rfl
/-- Single-stratum WHNF-forced GMP Pieri mixing step (`= solFastPieriPair`). -/
def solFastPieriPairZc (uvDenZ u : ℤ) (lv rv : IvInt) (rest : List IvInt) : List IvInt :=
  cond (solIsZeroZ u) (lv :: rv :: rest) (cond (solIvIsZeroZc lv && solIvIsZeroZc rv)
      ((Int.ofNat 0, Int.ofNat 0) :: (Int.ofNat 0, Int.ofNat 0) :: rest)
      (match solIvPythagZc u uvDenZ with
      | (cu, su) =>
          solForcePair (solIvSubGmp (solFastIvMulZc cu lv) (solFastIvMulZc su rv)) fun l' ↦
              solForcePair (solIvAddGmp (solFastIvMulZc su lv) (solFastIvMulZc cu rv))
                fun r' ↦ l' :: r' :: rest))
private theorem solFastPieriPairZc_eq (uvDenZ u : ℤ) (lv rv : IvInt) (rest : List IvInt) :
    solFastPieriPairZc uvDenZ u lv rv rest = GroverM1PulsePt0.solFastPieriPair uvDenZ u lv rv
    rest := by
  unfold solFastPieriPairZc GroverM1PulsePt0.solFastPieriPair; rw [solIvPythagZc_eq]
  rcases solIvPythag u uvDenZ with ⟨cu, su⟩
  simp only [solIsZeroZ_eq, solIvIsZero_eq, solForcePair_eq, solSeqIv_eq,
    solFastIvMulZc_eq, solIvSubGmp_eq, solIvAddGmp_eq]; rfl
/-- Auxiliary structural WHNF-forced GMP Pieri walk (`= solFastPieriWalkAux`). -/
def solFastPieriWalkAuxZc (uvDenZ : ℤ) (cv : IvInt) : ℕ → ℕ → List ℤ → List IvInt → List IvInt
  | 0, _, _, ss =>
      solBindIv (SchurWeylLCert.headIvP ss) fun lastIv ↦
        let sc := Int.ofNat 1000000000
        solBindIv
          (cond ((solBeqZ cv.1 sc && solBeqZ cv.2 sc) || solIvIsZeroZc lastIv) lastIv
            (solFastIvMulZc cv lastIv))
          fun outIv ↦ [outIv]
  | m + 1, s + 1, us, lv :: rv :: ss' => lv :: rv :: solFastPieriWalkAuxZc uvDenZ cv m s us ss'
  | m + 1, s + 1, us, [lv] =>
      lv :: (Int.ofNat 0, Int.ofNat 0) :: solFastPieriWalkAuxZc uvDenZ cv m s us []
  | m + 1, s + 1, us, [] =>
      (Int.ofNat 0, Int.ofNat 0) :: (Int.ofNat 0, Int.ofNat 0) ::
        solFastPieriWalkAuxZc uvDenZ cv m s us []
  | m + 1, 0, [], lv :: rv :: ss' => lv :: rv :: solFastPieriWalkAuxZc uvDenZ cv m 0 [] ss'
  | m + 1, 0, [], [lv] =>
      lv :: (Int.ofNat 0, Int.ofNat 0) :: solFastPieriWalkAuxZc uvDenZ cv m 0 [] []
  | m + 1, 0, [], [] =>
      (Int.ofNat 0, Int.ofNat 0) :: (Int.ofNat 0, Int.ofNat 0) ::
        solFastPieriWalkAuxZc uvDenZ cv m 0 [] []
  | m + 1, 0, u :: us', lv :: rv :: ss' =>
      solFastPieriPairZc uvDenZ u lv rv (solFastPieriWalkAuxZc uvDenZ cv m 0 us' ss')
  | m + 1, 0, u :: us', [lv] =>
      solFastPieriPairZc uvDenZ u lv (Int.ofNat 0, Int.ofNat 0)
        (solFastPieriWalkAuxZc uvDenZ cv m 0 us' [])
  | m + 1, 0, u :: us', [] =>
      solFastPieriPairZc uvDenZ u (Int.ofNat 0, Int.ofNat 0) (Int.ofNat 0, Int.ofNat 0)
        (solFastPieriWalkAuxZc uvDenZ cv m 0 us' [])
private theorem solFastPieriWalkAuxZc_eq (uvDenZ : ℤ) (cv : IvInt) : ∀ (m sk : ℕ) (us : List ℤ) (ss
    : List IvInt), solFastPieriWalkAuxZc uvDenZ cv m sk us ss =
    GroverM1PulsePt0.solFastPieriWalkAux uvDenZ cv m sk us ss
  | 0, _, _, ss => by
      unfold solFastPieriWalkAuxZc GroverM1PulsePt0.solFastPieriWalkAux swScale
      simp only [solBindIv_eq, solSeqIv_eq, solIvIsZero_eq, solFastIvMulZc_eq]; rfl
  | m + 1, sk, us, ss => by
      rcases sk with _ | s <;> rcases us with _ | ⟨u, us'⟩ <;>
        rcases ss with _ | ⟨lv, _ | ⟨rv, ss'⟩⟩ <;>
        simp only [solFastPieriWalkAuxZc, GroverM1PulsePt0.solFastPieriWalkAux,
          solFastPieriPairZc_eq, solFastPieriWalkAuxZc_eq uvDenZ cv m] <;> rfl
/-- Window-sparse WHNF-forced GMP Pieri walk (`= solFastPieriWalk`). -/
def solFastPieriWalkZc (hNext uvDen : ℕ) (cv : IvInt) (sp : SolSparsePulse) (naIv : List IvInt) :
    List IvInt :=
  match hNext, naIv with
  | 0, _ => []
  | m + 1, h0 :: ss =>
      h0 :: solFastPieriWalkAuxZc (Int.ofNat uvDen) cv m (Nat.sub sp.wLo 1) sp.uWin ss
  | m + 1, [] =>
      (Int.ofNat 0, Int.ofNat 0) ::
        solFastPieriWalkAuxZc (Int.ofNat uvDen) cv m (Nat.sub sp.wLo 1) sp.uWin []
private theorem solFastPieriWalkZc_eq (hNext uvDen : ℕ) (cv : IvInt) (sp : SolSparsePulse) (naIv :
    List IvInt) : solFastPieriWalkZc hNext uvDen cv sp naIv =
    GroverM1PulsePt0.solFastPieriWalk hNext uvDen cv sp naIv := by
  rcases hNext with _ | m <;> rcases naIv with _ | ⟨h0, ss⟩ <;>
    simp only [solFastPieriWalkZc, GroverM1PulsePt0.solFastPieriWalk,
      solFastPieriWalkAuxZc_eq]; rfl
/-- Direct 2-`solLitNat` pure-GMP midpoint and half-width (`= solIvMidRad`). -/
def solIvMidRadZc : IvInt → ℤ × ℕ
  | (.ofNat a, .ofNat b) =>
      cond (Nat.ble a b) (solLitNat (Nat.div (Nat.add a b) 2) fun m ↦
          solLitNat (Nat.div (Nat.add (Nat.sub b a) 1) 2) fun r ↦ (Int.ofNat m, r))
        (solIvMidRad (.ofNat a, .ofNat b))
  | (.negSucc a, .negSucc b) =>
      cond (Nat.ble b a) (solLitNat (Nat.div (Nat.add (Nat.add a b) 1) 2) fun m ↦
          solLitNat (Nat.div (Nat.add (Nat.sub a b) 1) 2) fun r ↦ (Int.negSucc m, r))
        (solIvMidRad (.negSucc a, .negSucc b))
  | (.negSucc a, .ofNat b) =>
      solKeepZ (solGmpDiv2 (solGmpSubNat b (Nat.add a 1))) fun mid ↦
        solLitNat (Nat.div (Nat.add (Nat.add b a) 2) 2) fun r ↦ (mid, r)
  | iv => solIvMidRad iv
private theorem solIvMidRadZc_eq (iv : IvInt) : solIvMidRadZc iv = solIvMidRad iv := by
  rcases iv with ⟨lo, hi⟩
  rcases lo with a | a <;> rcases hi with b | b
  · dsimp only [solIvMidRadZc]; rw [natBle_eq_decide]
    by_cases h : a ≤ b
    · rw [decide_eq_true h, Bool.cond_true]; unfold solIvMidRad
      simp only [solSeqInt_eq, solLitNat_eq, solMaxZ_eq, solIntAdd_eq, solIntEdiv_eq, solIntSub_eq,
        solNatDiv_eq, solNatAdd_eq, solNatSub_eq, Int.ofNat_eq_natCast]
      exact Prod.ext (by omega) (by omega)
    · rw [decide_eq_false h, Bool.cond_false]
  · rfl
  · dsimp only [solIvMidRadZc]; unfold solIvMidRad
    simp only [solKeepZ_eq, solGmpDiv2_eq, solGmpSubNat_eq, solSeqInt_eq, solLitNat_eq,
      solMaxZ_eq, solIntAdd_eq, solIntEdiv_eq, solIntSub_eq, solNatDiv_eq, solNatAdd_eq,
      Int.ofNat_eq_natCast, Int.negSucc_eq]
    exact Prod.ext (by omega) (by omega)
  · dsimp only [solIvMidRadZc]; rw [natBle_eq_decide]
    by_cases h : b ≤ a
    · rw [decide_eq_true h, Bool.cond_true]; unfold solIvMidRad
      simp only [solSeqInt_eq, solLitNat_eq, solMaxZ_eq, solIntAdd_eq, solIntEdiv_eq, solIntSub_eq,
        solNatDiv_eq, solNatAdd_eq, solNatSub_eq, Int.negSucc_eq]
      exact Prod.ext (by omega) (by omega)
    · rw [decide_eq_false h, Bool.cond_false]
/-- Pure-GMP recentering and squared-radius sum (`= solFastRecenterAndRadSq`). -/
def solFastRecenter : List IvInt → List ℤ × ℕ
  | [] => ([], 0)
  | iv :: ivs =>
      match solIvMidRadZc iv, solFastRecenter ivs with
      | (mid, rad), (cs, acc) =>
          solLitNat (Nat.add (Nat.mul rad rad) acc) fun acc' ↦ (mid :: cs, acc')
private theorem solFastRecenter_eq : ∀ (ivs : List IvInt), solFastRecenter ivs =
    GroverM1PulsePt0.solFastRecenterAndRadSq ivs
  | [] => rfl
  | iv :: ivs => by
      unfold solFastRecenter GroverM1PulsePt0.solFastRecenterAndRadSq
      rw [solIvMidRadZc_eq, solFastRecenter_eq ivs]
/-- Single-pulse WHNF-forced GMP `L2Ball` evolution step (`= solFastPulseStepL2`). -/
def solFastPulseStepL2Zc (L uvDen : ℕ) (trigIvs : List (IvInt × IvInt)) (cPref : List ℤ) (hAct rho
    : ℕ) (survUb : ℤ) (sp : SolSparsePulse) : List ℤ × ℕ × ℕ × ℤ :=
  solLitNat (solSumSqAbs cPref 0) fun normSqC ↦ solLitNat (solCeilIsqrt normSqC) fun normCUb ↦
      solLitNat (Nat.add normCUb rho) fun sumR ↦
        let sc := Int.ofNat 1000000000
        solKeepZ (solMinZ sc (solGmpCeilDivScale (Int.ofNat (Nat.mul sumR sumR))))
          fun oneMinusCumUb ↦ solKeepZ (solGmpAddZ survUb oneMinusCumUb) fun survUb' ↦
              solLitNat (solMinNat L (Nat.add hAct 1)) fun hNext ↦
                solBindIv
                  (cond (!Nat.beq hNext L || solIsZeroZ sp.vNum) (sc, sc)
                    ((solIvPythagZc sp.vNum (Int.ofNat uvDen)).1))
                  fun cv ↦
                    match solFastRecenter
                        (solFastPieriWalkZc hNext uvDen cv sp
                          (solFastGroverWalkZc hNext trigIvs cPref)) with
                    | (cNextRaw, radSqSum) =>
                        solSeqList
                          (solPadEmptyPair (GroverM1PulsePt0.solFastTrimZeroPairs cNextRaw))
                          fun cOut ↦ solLitNat (solMaxNat 1 (Nat.div cOut.length 2)) fun hAct' ↦
                              solLitNat (Nat.add rho (solCeilIsqrt radSqSum)) fun rho' ↦
                                (cOut, hAct', rho', survUb')
private theorem solFastPulseStepL2Zc_eq (L uvDen : ℕ) (trigIvs : List (IvInt × IvInt)) (cPref :
    List ℤ) (hAct rho : ℕ) (survUb : ℤ) (sp : SolSparsePulse) : solFastPulseStepL2Zc L uvDen
    trigIvs cPref hAct rho survUb sp = GroverM1PulsePt0.solFastPulseStepL2 L uvDen trigIvs
    cPref hAct rho survUb sp := by
  unfold solFastPulseStepL2Zc GroverM1PulsePt0.solFastPulseStepL2 swScale
  simp only [solLitNat_eq, solKeepZ_eq, solSeqInt_eq, solBindIv_eq, solSeqIv_eq,
    solSeqList_eq, solGmpCeilDivScale_eq, solGmpAddZ_eq, solIsZeroZ_eq,
    solIvPythagZc_eq, solFastRecenter_eq, solFastPieriWalkZc_eq, solFastGroverWalkZc_eq]; rfl
/-- Primitive-`Nat.rec` WHNF-forced GMP WKB evolution loop (`= solFastWkbEvolveLoopRef`). -/
def solFastWkbEvolveLoopZc (qR qL qTauNum qTauDen qUvDen : ℕ) (qSOffQ qVBulkQ qAccelQ sMaxQ gTopQ
    phiTotQ km1Sq : ℤ) (sgArr : List (ℤ × ℤ)) (rbTree ulnTree uldTree vdTree : SolPairTree) (trigIvs
    : List (IvInt × IvInt)) : ℕ → ℕ → List ℤ → ℕ → ℕ → ℤ → List ℤ × ℕ × ℕ × ℤ
  | 0, _, cPref, hAct, rho, survUb => (cPref, hAct, rho, survUb)
  | rem + 1, t, cPref, hAct, rho, survUb =>
      match GroverM1PulsePt0.solFastEvalWkbPulseRef qR qL qTauNum qTauDen
          qSOffQ qVBulkQ qAccelQ sMaxQ gTopQ phiTotQ km1Sq sgArr
          rbTree ulnTree uldTree vdTree t with
      | ⟨wLo, uWin, vNum⟩ =>
          match solFastPulseStepL2Zc qL qUvDen trigIvs cPref hAct rho survUb
              ⟨wLo, uWin, vNum⟩ with
          | (cNext, hAct', rho', survUb') =>
              solSeqList cNext fun cNext' ↦ solLitNat hAct' fun ha ↦
                  solLitNat rho' fun rh ↦ solKeepZ survUb' fun sv ↦
                      solLitNat (Nat.add t 1) fun tNext ↦
                        solFastWkbEvolveLoopZc qR qL qTauNum qTauDen qUvDen
                          qSOffQ qVBulkQ qAccelQ sMaxQ gTopQ phiTotQ km1Sq sgArr
                          rbTree ulnTree uldTree vdTree trigIvs rem tNext cNext' ha rh sv
private theorem solFastWkbEvolveLoopZc_eq (qR qL qTauNum qTauDen qUvDen : ℕ) (qSOffQ qVBulkQ
    qAccelQ sMaxQ gTopQ phiTotQ km1Sq : ℤ) (sgArr : List (ℤ × ℤ)) (rbTree ulnTree uldTree vdTree :
    SolPairTree) (trigIvs : List (IvInt × IvInt)) : ∀ (rem t : ℕ) (cPref : List ℤ) (hAct rho : ℕ)
    (survUb : ℤ), solFastWkbEvolveLoopZc qR qL qTauNum qTauDen qUvDen qSOffQ qVBulkQ qAccelQ sMaxQ
    gTopQ phiTotQ km1Sq sgArr rbTree ulnTree uldTree vdTree trigIvs rem t cPref hAct rho survUb =
    GroverM1PulsePt0.solFastWkbEvolveLoopRef qR qL qTauNum qTauDen qUvDen qSOffQ qVBulkQ qAccelQ
    sMaxQ gTopQ phiTotQ km1Sq sgArr rbTree ulnTree uldTree vdTree trigIvs rem t cPref hAct rho
    survUb
  | 0, _, _, _, _, _ => rfl
  | rem + 1, t, cPref, hAct, rho, survUb => by
      unfold solFastWkbEvolveLoopZc GroverM1PulsePt0.solFastWkbEvolveLoopRef
      rcases GroverM1PulsePt0.solFastEvalWkbPulseRef qR qL qTauNum qTauDen
          qSOffQ qVBulkQ qAccelQ sMaxQ gTopQ phiTotQ km1Sq sgArr
          rbTree ulnTree uldTree vdTree t with ⟨wLo, uWin, vNum⟩
      dsimp only; rw [solFastPulseStepL2Zc_eq]
      rcases GroverM1PulsePt0.solFastPulseStepL2 qL qUvDen trigIvs cPref hAct rho survUb
          ⟨wLo, uWin, vNum⟩ with ⟨cNext, hAct', rho', survUb'⟩
      dsimp only; simp only [solSeqList_eq, solLitNat_eq, solKeepZ_eq, solSeqInt_eq]
      exact solFastWkbEvolveLoopZc_eq qR qL qTauNum qTauDen qUvDen
        qSOffQ qVBulkQ qAccelQ sMaxQ gTopQ phiTotQ km1Sq sgArr
        rbTree ulnTree uldTree vdTree trigIvs rem (Nat.add t 1) cNext hAct' rho' survUb'
/-- Zero-closure pure-GMP boolean WKB slice checker (`= solFastCheckWkbSliceRef`). -/
def solFastCheckWkbSliceZc (q : SolWkbSched) (t len : ℕ) (trigIvs : List (IvInt × IvInt)) (cIn :
    List ℤ) (hIn rhoIn : ℕ) (survIn : ℤ) (cOut : List ℤ) (hOut rhoOut : ℕ) (survOut : ℤ) : Bool :=
  solLitNat q.r fun qR ↦ solLitNat q.L fun qL ↦
  solLitNat q.tauNum fun qTauNum ↦ solLitNat q.tauDen fun qTauDen ↦
  solLitNat q.uvDen fun qUvDen ↦ solSeqInt q.sOffQ fun qSOffQ ↦
  solSeqInt q.vBulkQ fun qVBulkQ ↦ solSeqInt q.accelQ fun qAccelQ ↦
  solWithTrigList trigIvs fun trigIvs' ↦ solWithIntList cIn fun cIn' ↦
  solSeqList (solRevSGList (solBuildWkbSGRev qR 0 (Nat.add qL 1) []) []) fun sgArr ↦
  solSeqInt (sgArr.getD (Nat.sub qL 1) (0, 0)).1 fun sMaxQ ↦
  let gTopNat := solFloorIsqrt (Nat.div (Nat.mul 1048576 (Nat.sub qR (Nat.sub qL 1))) qR)
  solSeqInt (Int.ofNat gTopNat) fun gTopQ ↦
  let km1 := Int.ofNat (solMaxNat 1 (Nat.sub q.K 1))
  solSeqInt (Int.mul km1 km1) fun km1Sq ↦
  solSeqInt (Int.ediv (Int.mul (Int.mul (Int.ofNat (Nat.sub q.K 1)) (Int.ofNat qTauNum)) 1024)
      (Int.ofNat qTauDen))
    fun phiTotQ ↦
  solWithPairTree (solBuildPairTree q.rBulkQ 8) fun rbTree ↦
  solWithPairTree (solBuildPairTree q.uLnchQ 10) fun ulnTree ↦
  solWithPairTree (solBuildPairTree q.uLandQ 10) fun uldTree ↦
  solWithPairTree (solBuildPairTree q.vDrainQ 6) fun vdTree ↦
  match solFastWkbEvolveLoopZc qR qL qTauNum qTauDen qUvDen
      qSOffQ qVBulkQ qAccelQ sMaxQ gTopQ phiTotQ km1Sq sgArr
      rbTree ulnTree uldTree vdTree trigIvs' len t cIn' hIn rhoIn survIn with
  | (c1, h1, rh1, sv1) =>
      solListIntBeq c1 cOut && Nat.beq h1 hOut && Nat.beq rh1 rhoOut && solBeqZ sv1 survOut
private theorem solFastCheckWkbSliceZc_eq (q : SolWkbSched) (t len : ℕ) (trigIvs : List (IvInt ×
    IvInt)) (cIn : List ℤ) (hIn rhoIn : ℕ) (survIn : ℤ) (cOut : List ℤ) (hOut rhoOut : ℕ) (survOut :
    ℤ) : solFastCheckWkbSliceZc q t len trigIvs cIn hIn rhoIn survIn cOut hOut rhoOut survOut =
    GroverM1PulsePt0.solFastCheckWkbSliceRef q t len trigIvs cIn hIn rhoIn survIn cOut hOut
    rhoOut survOut := by
  unfold solFastCheckWkbSliceZc GroverM1PulsePt0.solFastCheckWkbSliceRef
  simp only [solLitNat_eq, solSeqInt_eq, solWithTrigList_eq, solWithIntList_eq, solSeqList_eq,
    solWithPairTree_eq, solFastWkbEvolveLoopZc_eq]
/-- Soundness of `solFastCheckWkbSliceZc` (`0`-ULP equal to `solFastWkbStepRef_eq`). -/
theorem solFastWkbStepZc_eq {q : SolWkbSched} {trigIvs : List (IvInt × IvInt)} {t len tNext : ℕ}
    {cIn : List ℤ} {hIn rhoIn : ℕ} {survIn : ℤ} {cOut : List ℤ} {hOut rhoOut : ℕ} {survOut : ℤ} (ht
    : t + len = tNext) (hprev : SolWkbRunPrefix q trigIvs t cIn hIn rhoIn survIn) (hfast :
    solFastCheckWkbSliceZc q t len trigIvs cIn hIn rhoIn survIn cOut hOut rhoOut survOut = true) :
    SolWkbRunPrefix q trigIvs tNext cOut hOut rhoOut survOut := by
  rw [solFastCheckWkbSliceZc_eq] at hfast
  exact GroverM1PulsePt0.solFastWkbStepRef_eq ht hprev hfast
private def _wkbPair (q : SolWkbSched) (trg : List (IvInt × IvInt))
    (t0 d0 t1 d1 : ℕ) (c0 : List ℤ) (h0 r0 : ℕ) (s0 : ℤ)
    (c1 : List ℤ) (h1 r1 : ℕ) (s1 : ℤ) (c2 : List ℤ) (h2 r2 : ℕ) (s2 : ℤ) : Bool :=
  match solFastCheckWkbSliceZc q t0 d0 trg c0 h0 r0 s0 c1 h1 r1 s1 with
  | true => solFastCheckWkbSliceZc q t1 d1 trg c1 h1 r1 s1 c2 h2 r2 s2
  | false => false
private theorem _ws2 {q : SolWkbSched} {trg : List (IvInt × IvInt)}
    (t0 d0 t1 d1 t2 : ℕ) {c0 c1 c2 : List ℤ} {h0 r0 h1 r1 h2 r2 : ℕ} {s0 s1 s2 : ℤ}
    (ha : t0 + d0 = t1) (hb : t1 + d1 = t2) (hp : SolWkbRunPrefix q trg t0 c0 h0 r0 s0)
    (hc : _wkbPair q trg t0 d0 t1 d1 c0 h0 r0 s0 c1 h1 r1 s1 c2 h2 r2 s2 = true) :
    SolWkbRunPrefix q trg t2 c2 h2 r2 s2 := by
  unfold _wkbPair at hc; revert hc
  cases h1c : solFastCheckWkbSliceZc q t0 d0 trg c0 h0 r0 s0 c1 h1 r1 s1
  · intro hc; cases hc
  · intro hc; exact solFastWkbStepZc_eq hb (solFastWkbStepZc_eq ha hp h1c) hc
private def _cInit : List ℤ := [swScale, 0]
private def _uZg (u : ℕ) : ℤ :=
  match Nat.mod u 2 with
  | 0 => solLitNat (Nat.div u 2) Int.ofNat
  | _ => solLitNat (Nat.div u 2) Int.negSucc
private def _uStep (w : ℕ) (tl : List ℤ) : List ℤ :=
  match Nat.ble 287296000000000000 w with
  | true => solKeepZ (_uZg (Nat.sub w 287296000000000000)) fun z ↦ z :: tl
  | false => solKeepZ (_uZg (Nat.mod w 536000000)) fun a ↦
      solKeepZ (_uZg (Nat.div w 536000000)) fun b ↦ a :: b :: tl
private def _uPk : List ℕ → List ℤ
  | [] => []
  | w :: ws => _uStep w (_uPk ws)
/-- Chunk 0 of `solWkb_rBulkQ_r128`. -/
def solWkb_rBulkQ_r128_c0 : List (ℤ) :=
  [32, 11250, 38862, 67117, 79410, 80198, 81194, 82304, 83273, 84059, 84852, 85728, 86692, 87773,
  88846, 89757, 90820, 92462, 93726, 93694]
/-- Chunk 1 of `solWkb_rBulkQ_r128`. -/
def solWkb_rBulkQ_r128_c1 : List (ℤ) :=
  [92682, 92237, 92525, 92131, 91210, 92833, 100014, 104449, 94118, 85559, 97578, 107606, 90930,
  86929, 112007, 91597, 107290, 100180, 103277, 102988]
/-- Chunk 2 of `solWkb_rBulkQ_r128`. -/
def solWkb_rBulkQ_r128_c2 : List (ℤ) :=
  [99575, 97853, 97153, 96175, 95105, 94231, 93426, 92574, 91689, 90815, 89967, 89144, 88338,
  87541, 86749, 85964, 85185, 84416, 83659, 82917]
/-- Chunk 3 of `solWkb_rBulkQ_r128`. -/
def solWkb_rBulkQ_r128_c3 : List (ℤ) :=
  [82188, 69540, 40381, 11724, 0]
/-- WKB bulk profile table for `r = 128`. -/
def solWkb_rBulkQ_r128 : List (ℤ) :=
  List.append ( List.append ( solWkb_rBulkQ_r128_c0) ( solWkb_rBulkQ_r128_c1)) ( List.append (
  solWkb_rBulkQ_r128_c2) ( solWkb_rBulkQ_r128_c3))
/-- Chunk 0 of `solWkb_uLnchQ_r128`. -/
def solWkb_uLnchQ_r128_c0 : List (ℤ) :=
  [92220, 72470, 44249, 29983, 17651, 12955, 9442, 6489, 4068, 2657, 1554, 623, 1609, 47095,
  78261, 61362, 20793, 0, (-15438), 27158]
/-- Chunk 1 of `solWkb_uLnchQ_r128`. -/
def solWkb_uLnchQ_r128_c1 : List (ℤ) :=
  [35915, 29014, 22487, 16734, 11488, 6468, 2236, (-423), (-2602), (-4467), (-5877), (-4787),
  40914, 56890, 19184, 0, (-22401), (-1507), 12399, 21400]
/-- Chunk 2 of `solWkb_uLnchQ_r128`. -/
def solWkb_uLnchQ_r128_c2 : List (ℤ) :=
  [22368, 20160, 16643, 12685, 9050, 5963, 2974, 75, (-2243), (-3902), (-2840), 34387, 19923, 0,
  (-32333), (-9222), 1937, 9684, 15261, 19109]
/-- Chunk 3 of `solWkb_uLnchQ_r128`. -/
def solWkb_uLnchQ_r128_c3 : List (ℤ) :=
  [18559, 15861, 13144, 10466, 7706, 4881, 2426, 444, (-1304), (-155), 12709, 0, (-22467),
  (-24507), (-8318), 1927, 9295, 11188, 15083, 15269]
/-- Chunk 4 of `solWkb_uLnchQ_r128`. -/
def solWkb_uLnchQ_r128_c4 : List (ℤ) :=
  [13867, 12147, 10389, 8465, 6438, 4390, 2331, 193, 437, 0, (-36037), (-20256), (-15320),
  (-6803), 1937, 7981, 9042, 12978, 13975, 13507]
/-- Chunk 5 of `solWkb_uLnchQ_r128`. -/
def solWkb_uLnchQ_r128_c5 : List (ℤ) :=
  [12679, 11507, 9956, 8062, 6003, 3085, 539, 0, (-37656), (-21290), (-17958), (-10713), (-5191),
  1680, 7017, 7546, 11327, 12775, 12560, 11652]
/-- Chunk 6 of `solWkb_uLnchQ_r128`. -/
def solWkb_uLnchQ_r128_c6 : List (ℤ) :=
  [10567, 9269, 7853, 5133, 1374, 0, (-31767), (-27513), (-17692), (-18349), (-7600), (-3621),
  2064, 5976, 6601, 9649, 10914, 10856, 10460, 9910]
/-- Chunk 7 of `solWkb_uLnchQ_r128`. -/
def solWkb_uLnchQ_r128_c7 : List (ℤ) :=
  [9213, 6738, 2041, 0, (-29797), (-30143), (-24338), (-13983), (-16077), (-6105), (-2451), 1987,
  5045, 5515, 8330, 10000, 10430, 10474, 10278, 7838]
/-- Chunk 8 of `solWkb_uLnchQ_r128`. -/
def solWkb_uLnchQ_r128_c8 : List (ℤ) :=
  [2479, 0, (-31851), (-30695), (-28018), (-18574), (-13875), (-14046), (-4714), (-1753), 1877,
  4160, 5553, 7792, 9415, 10040, 10100, 7807, 2536, 0]
/-- Chunk 9 of `solWkb_uLnchQ_r128`. -/
def solWkb_uLnchQ_r128_c9 : List (ℤ) :=
  [(-33904), (-29714), (-27056), (-23544), (-15464), (-12634), (-10810), (-4129), (-1018), 1841,
  3606, 4870, 6782, 8501, 8966, 7180, 2450, 0, (-34034), (-28499)]
/-- Chunk 10 of `solWkb_uLnchQ_r128`. -/
def solWkb_uLnchQ_r128_c10 : List (ℤ) :=
  [(-23818), (-23849), (-19655), (-12473), (-11972), (-9166), (-3651), (-508), 1839, 3231, 4423,
  5996, 7514, 6592, 2398, 0, (-33201), (-27852), (-22842), (-22025)]
/-- Chunk 11 of `solWkb_uLnchQ_r128`. -/
def solWkb_uLnchQ_r128_c11 : List (ℤ) :=
  [(-21496), (-17048), (-11433), (-11694), (-7749), (-3242), (-635), 1690, 2966, 3947, 5512, 5802,
  2239, 0, (-32529), (-28041), (-23911), (-21163), (-20547), (-19253)]
/-- Chunk 12 of `solWkb_uLnchQ_r128`. -/
def solWkb_uLnchQ_r128_c12 : List (ℤ) :=
  [(-14480), (-10722), (-10438), (-5783), (-3363), (-864), 1299, 2699, 3762, 4199, 1881, (-1),
  (-32391), (-28806), (-25293), (-22066), (-19049), (-19399), (-17236), (-12812)]
/-- Chunk 13 of `solWkb_uLnchQ_r128`. -/
def solWkb_uLnchQ_r128_c13 : List (ℤ) :=
  [(-9169), (-9098), (-5331), (-3482), (-1343), 660, 2630, 2831, 1297, 19, (-20620), (-23452),
  (-20833), (-18079), (-15158), (-14200), (-14349), (-12438), (-8713), (-7043)]
/-- Chunk 14 of `solWkb_uLnchQ_r128`. -/
def solWkb_uLnchQ_r128_c14 : List (ℤ) :=
  [(-6801), (-3938), (-3036), (-1556), 348, 2188, 1029, (-71), 6709, (-6289), (-7181), (-6266),
  (-5426), (-4595), (-4206), (-4359), (-3499), (-2748), (-2671), (-2274)]
/-- Chunk 15 of `solWkb_uLnchQ_r128`. -/
def solWkb_uLnchQ_r128_c15 : List (ℤ) :=
  [(-1660), (-1839), (-1027), 197, 914, 344, 0, 0, (-1), (-12), (-64), (-95), 11, (-112), 193, 46,
  (-81), (-370), 138, (-665)]
/-- Chunk 16 of `solWkb_uLnchQ_r128`. -/
def solWkb_uLnchQ_r128_c16 : List (ℤ) :=
  [(-629), (-654), 323, 919]
/-- WKB launch correction table for `r = 128`. -/
def solWkb_uLnchQ_r128 : List (ℤ) :=
  List.append ( List.append ( List.append ( List.append ( solWkb_uLnchQ_r128_c0) (
  solWkb_uLnchQ_r128_c1)) ( List.append ( solWkb_uLnchQ_r128_c2) ( solWkb_uLnchQ_r128_c3))) (
  List.append ( List.append ( solWkb_uLnchQ_r128_c4) ( solWkb_uLnchQ_r128_c5)) ( List.append (
  solWkb_uLnchQ_r128_c6) ( solWkb_uLnchQ_r128_c7)))) ( List.append ( List.append ( List.append (
  solWkb_uLnchQ_r128_c8) ( solWkb_uLnchQ_r128_c9)) ( List.append ( solWkb_uLnchQ_r128_c10) (
  solWkb_uLnchQ_r128_c11))) ( List.append ( List.append ( solWkb_uLnchQ_r128_c12) (
  solWkb_uLnchQ_r128_c13)) ( List.append ( solWkb_uLnchQ_r128_c14) ( List.append (
  solWkb_uLnchQ_r128_c15) ( solWkb_uLnchQ_r128_c16)))))
/-- Chunk 0 of `solWkb_uLandQ_r128`. -/
def solWkb_uLandQ_r128_c0 : List (ℤ) :=
  [(-84455), (-82384), (-80387), (-78290), (-76211), (-74121), (-38272), 4720, 5416, 5417, 5416,
  5415, 5414, 5415, 5414, 4338, 1501, 0, 28781, 14342]
/-- Chunk 1 of `solWkb_uLandQ_r128`. -/
def solWkb_uLandQ_r128_c1 : List (ℤ) :=
  [2380, (-5697), (-11782), (-8475), (-3801), 36327, 80940, 80197, 78006, 75261, 72432, 69562,
  66645, 50955, 16757, 1, 20661, 13975, 9459, 5520]
/-- Chunk 2 of `solWkb_uLandQ_r128`. -/
def solWkb_uLandQ_r128_c2 : List (ℤ) :=
  [1679, 557, 454, 1870, 38895, 81153, 81564, 82132, 82258, 81678, 80808, 63858, 21637, 0, 15008,
  13083, 11481, 6786, 3755, 1633]
/-- Chunk 3 of `solWkb_uLandQ_r128`. -/
def solWkb_uLandQ_r128_c3 : List (ℤ) :=
  [240, 632, 1861, 40002, 81221, 81232, 80965, 80715, 80844, 64989, 22432, 1, 10791, 10696, 11694,
  9802, 8501, 6819, 4396, 2740]
/-- Chunk 4 of `solWkb_uLandQ_r128`. -/
def solWkb_uLandQ_r128_c4 : List (ℤ) :=
  [2320, 3051, 41074, 80582, 79628, 78992, 79123, 63933, 22261, 2, 10518, 7931, 9965, 7449, 7052,
  8775, 8540, 6761, 4856, 3893]
/-- Chunk 5 of `solWkb_uLandQ_r128`. -/
def solWkb_uLandQ_r128_c5 : List (ℤ) :=
  [3801, 42022, 80029, 78812, 78397, 63062, 21947, 3, 9834, 3465, 3987, 4342, 5918, 8569, 10293,
  10385, 8915, 6729, 5471, 4810]
/-- Chunk 6 of `solWkb_uLandQ_r128`. -/
def solWkb_uLandQ_r128_c6 : List (ℤ) :=
  [42944, 79640, 78536, 62689, 21692, 2, 7615, (-3653), (-2765), 933, 3447, 5372, 7831, 10104,
  11170, 9762, 8021, 6645, 5520, 44022]
/-- Chunk 7 of `solWkb_uLandQ_r128`. -/
def solWkb_uLandQ_r128_c7 : List (ℤ) :=
  [79802, 63036, 21664, 4, 3275, (-11203), (-5961), (-3115), (-278), 2324, 4604, 7634, 10380,
  11089, 10315, 8834, 7866, 6523, 45402, 64144]
/-- Chunk 8 of `solWkb_uLandQ_r128`. -/
def solWkb_uLandQ_r128_c8 : List (ℤ) :=
  [21854, 20, 19180, (-284), (-3365), (-4573), (-4197), (-1556), 493, 3642, 7345, 10050, 10740,
  9593, 9198, 8538, 6959, 37056, 22235, 24]
/-- Chunk 9 of `solWkb_uLandQ_r128`. -/
def solWkb_uLandQ_r128_c9 : List (ℤ) :=
  [1039, 8260, 3991, (-1440), (-2903), (-3509), (-2915), (-593), 3101, 7251, 9107, 8870, 9253,
  9655, 9033, 5587, 13132, 8, (-18815), (-4312)]
/-- Chunk 10 of `solWkb_uLandQ_r128`. -/
def solWkb_uLandQ_r128_c10 : List (ℤ) :=
  [5216, 4127, 471, (-860), (-2547), (-2615), (-1324), 2452, 5921, 7375, 8323, 8945, 9224, 6448,
  1979, 18, (-21511), (-16839), (-4189), 3772]
/-- Chunk 11 of `solWkb_uLandQ_r128`. -/
def solWkb_uLandQ_r128_c11 : List (ℤ) :=
  [2795, 491, (-295), (-1404), (-1752), (-318), 2510, 5207, 6113, 6093, 6793, 5779, 2009, 10,
  (-16925), (-16122), (-12369), (-2841), 3062, 2082]
/-- Chunk 12 of `solWkb_uLandQ_r128`. -/
def solWkb_uLandQ_r128_c12 : List (ℤ) :=
  [113, (-482), (-843), (-471), 559, 2806, 3964, 3585, 4524, 4696, 1842, (-19), (-17032),
  (-16502), (-16741), (-10644), (-2037), 2263, 1295, (-707)]
/-- Chunk 13 of `solWkb_uLandQ_r128`. -/
def solWkb_uLandQ_r128_c13 : List (ℤ) :=
  [(-912), (-986), (-278), 967, 2128, 2682, 3501, 3307, 1222, (-3), (-14612), (-14619), (-14517),
  (-10937), (-7099), (-1699), 1516, 687, (-295), (-778)]
/-- Chunk 14 of `solWkb_uLandQ_r128`. -/
def solWkb_uLandQ_r128_c14 : List (ℤ) :=
  [(-712), 9, 605, 1515, 2487, 1701, 537, 20, (-5425), (-5110), (-4771), (-4054), (-3386),
  (-2657), (-768), 452, 91, (-502), (-648), (-610)]
/-- Chunk 15 of `solWkb_uLandQ_r128`. -/
def solWkb_uLandQ_r128_c15 : List (ℤ) :=
  [(-378), (-94), 493, 469, 177, 11, 1, (-1), (-5), (-23), (-76), (-124), (-349), (-43), 265,
  (-379), (-419), (-365), (-240), (-237)]
/-- Chunk 16 of `solWkb_uLandQ_r128`. -/
def solWkb_uLandQ_r128_c16 : List (ℤ) :=
  [(-111), (-4), (-18), (-1)]
/-- WKB landing correction table for `r = 128`. -/
def solWkb_uLandQ_r128 : List (ℤ) :=
  List.append ( List.append ( List.append ( List.append ( solWkb_uLandQ_r128_c0) (
  solWkb_uLandQ_r128_c1)) ( List.append ( solWkb_uLandQ_r128_c2) ( solWkb_uLandQ_r128_c3))) (
  List.append ( List.append ( solWkb_uLandQ_r128_c4) ( solWkb_uLandQ_r128_c5)) ( List.append (
  solWkb_uLandQ_r128_c6) ( solWkb_uLandQ_r128_c7)))) ( List.append ( List.append ( List.append (
  solWkb_uLandQ_r128_c8) ( solWkb_uLandQ_r128_c9)) ( List.append ( solWkb_uLandQ_r128_c10) (
  solWkb_uLandQ_r128_c11))) ( List.append ( List.append ( solWkb_uLandQ_r128_c12) (
  solWkb_uLandQ_r128_c13)) ( List.append ( solWkb_uLandQ_r128_c14) ( List.append (
  solWkb_uLandQ_r128_c15) ( solWkb_uLandQ_r128_c16)))))
/-- Chunk 0 of `solWkb_vDrainQ_r128`. -/
def solWkb_vDrainQ_r128_c0 : List (ℤ) :=
  [35160, 204972, 283223, 283737, 282226, 285183, 288946, 294813, 306653, 322674, 339499, 340976,
  291204, 131410, (-43314), (-43689), 11134, 11657, (-9364), (-11919)]
/-- Chunk 1 of `solWkb_vDrainQ_r128`. -/
def solWkb_vDrainQ_r128_c1 : List (ℤ) :=
  [(-1391), 2307, 194, 0]
/-- WKB drain probe table for `r = 128`. -/
def solWkb_vDrainQ_r128 : List (ℤ) :=
  List.append ( solWkb_vDrainQ_r128_c0) ( solWkb_vDrainQ_r128_c1)
/-- Compact pure-integer WKB spline schedule for `r = 128` (`L = 64`). -/
def solWkbSched_r128 : SolWkbSched where
  r := 128
  L := 64
  K := 392
  tauNum := 238946
  tauDen := 1000000
  uvDen := 100000
  vBulkQ := 918
  sOffQ := (-1775)
  accelQ := 48
  rBulkQ := solWkb_rBulkQ_r128
  uLnchQ := solWkb_uLnchQ_r128
  uLandQ := solWkb_uLandQ_r128
  vDrainQ := solWkb_vDrainQ_r128
/-- Chunk 0 of `solRatios_r128`. -/
def solRatios_r128_c0 : List (IvInt) :=
  [(996086089, 996086092), (992156740, 992156743), (988211767, 988211770), (984250983, 984250986),
  (980274195, 980274198), (976281208, 976281211), (972271823, 972271826), (968245835, 968245838),
  (964203037, 964203040), (960143217, 960143220), (956066157, 956066160), (951971637, 951971640)]
/-- Chunk 1 of `solRatios_r128`. -/
def solRatios_r128_c1 : List (IvInt) :=
  [(947859429, 947859432), (943729303, 943729306), (939581022, 939581025), (935414345, 935414348),
  (931229025, 931229028), (927024809, 927024812), (922801440, 922801443), (918558652, 918558655),
  (914296176, 914296179), (910013735, 910013738), (905711045, 905711048), (901387817, 901387820)]
/-- Chunk 2 of `solRatios_r128`. -/
def solRatios_r128_c2 : List (IvInt) :=
  [(897043754, 897043757), (892678552, 892678555), (888291899, 888291902), (883883475, 883883478),
  (879452953, 879452956), (874999999, 875000002), (870524266, 870524269), (866025402, 866025405),
  (861503046, 861503049), (856956824, 856956827), (852386355, 852386358), (847791246, 847791249)]
/-- Chunk 3 of `solRatios_r128`. -/
def solRatios_r128_c3 : List (IvInt) :=
  [(843171096, 843171099), (838525490, 838525493), (833854003, 833854006), (829156196, 829156199),
  (824431621, 824431624), (819679814, 819679817), (814900299, 814900302), (810092586, 810092589),
  (805256169, 805256172), (800390528, 800390531), (795495127, 795495130), (790569414, 790569417)]
/-- Chunk 4 of `solRatios_r128`. -/
def solRatios_r128_c4 : List (IvInt) :=
  [(785612817, 785612820), (780624748, 780624751), (775604601, 775604604), (770551749, 770551752),
  (765465543, 765465546), (760345315, 760345318), (755190372, 755190375), (749999999, 750000002),
  (744773454, 744773457), (739509971, 739509974), (734208756, 734208759), (728868985, 728868988)]
/-- Chunk 5 of `solRatios_r128`. -/
def solRatios_r128_c5 : List (IvInt) :=
  [(723489805, 723489808), (718070329, 718070332), (712609639, 712609642)]
/-- Stratum angle-ratio intervals for WKB `r = 128`. -/
def solRatios_r128 : List (IvInt) :=
  List.append ( List.append ( solRatios_r128_c0) ( List.append ( solRatios_r128_c1) (
  solRatios_r128_c2))) ( List.append ( solRatios_r128_c3) ( List.append ( solRatios_r128_c4) (
  solRatios_r128_c5)))
/-- Chunk 0 of `solTrigIvs_r128`. -/
def solTrigIvs_r128_c0 : List (IvInt × IvInt) :=
  [((971587973, 971587974), (236678704, 236678705)), ((971808893, 971808895), (235769958,
  235769961)), ((972029830, 972029831), (234857421, 234857423)), ((972250783, 972250784),
  (233941047, 233941049)), ((972471752, 972471754), (233020791, 233020793)), ((972692738,
  972692740), (232096607, 232096609))]
/-- Chunk 1 of `solTrigIvs_r128`. -/
def solTrigIvs_r128_c1 : List (IvInt × IvInt) :=
  [((972913741, 972913742), (231168447, 231168449)), ((973134760, 973134761), (230236264,
  230236266)), ((973355795, 973355797), (229300008, 229300010)), ((973576847, 973576849),
  (228359629, 228359632)), ((973797916, 973797917), (227415077, 227415079)), ((974019001,
  974019002), (226466298, 226466300))]
/-- Chunk 2 of `solTrigIvs_r128`. -/
def solTrigIvs_r128_c2 : List (IvInt × IvInt) :=
  [((974240102, 974240104), (225513240, 225513242)), ((974461220, 974461222), (224555847,
  224555849)), ((974682355, 974682356), (223594064, 223594066)), ((974903506, 974903507),
  (222627835, 222627837)), ((975124673, 975124674), (221657100, 221657102)), ((975345857,
  975345858), (220681801, 220681803))]
/-- Chunk 3 of `solTrigIvs_r128`. -/
def solTrigIvs_r128_c3 : List (IvInt × IvInt) :=
  [((975567058, 975567059), (219701876, 219701878)), ((975788275, 975788276), (218717264,
  218717266)), ((976009508, 976009509), (217727900, 217727902)), ((976230758, 976230759),
  (216733720, 216733722)), ((976452024, 976452026), (215734657, 215734659)), ((976673307,
  976673309), (214730643, 214730645))]
/-- Chunk 4 of `solTrigIvs_r128`. -/
def solTrigIvs_r128_c4 : List (IvInt × IvInt) :=
  [((976894607, 976894608), (213721607, 213721609)), ((977115923, 977115924), (212707479,
  212707481)), ((977337255, 977337257), (211688185, 211688187)), ((977558604, 977558606),
  (210663650, 210663652)), ((977779970, 977779971), (209633798, 209633800)), ((978001352,
  978001353), (208598548, 208598550))]
/-- Chunk 5 of `solTrigIvs_r128`. -/
def solTrigIvs_r128_c5 : List (IvInt × IvInt) :=
  [((978222750, 978222751), (207557822, 207557824)), ((978444165, 978444166), (206511534,
  206511537)), ((978665597, 978665598), (205459602, 205459604)), ((978887045, 978887046),
  (204401937, 204401939)), ((979108509, 979108511), (203338450, 203338452)), ((979329990,
  979329992), (202269050, 202269052))]
/-- Chunk 6 of `solTrigIvs_r128`. -/
def solTrigIvs_r128_c6 : List (IvInt × IvInt) :=
  [((979551488, 979551489), (201193640, 201193642)), ((979773002, 979773003), (200112126,
  200112128)), ((979994533, 979994534), (199024407, 199024409)), ((980216080, 980216081),
  (197930381, 197930383)), ((980437643, 980437644), (196829942, 196829944)), ((980659223,
  980659225), (195722983, 195722985))]
/-- Chunk 7 of `solTrigIvs_r128`. -/
def solTrigIvs_r128_c7 : List (IvInt × IvInt) :=
  [((980880820, 980880821), (194609392, 194609394)), ((981102433, 981102434), (193489054,
  193489056)), ((981324063, 981324064), (192361852, 192361854)), ((981545709, 981545710),
  (191227664, 191227666)), ((981767372, 981767373), (190086365, 190086367)), ((981989051,
  981989052), (188937826, 188937828))]
/-- Chunk 8 of `solTrigIvs_r128`. -/
def solTrigIvs_r128_c8 : List (IvInt × IvInt) :=
  [((982210747, 982210748), (187781915, 187781916)), ((982432459, 982432460), (186618493,
  186618495)), ((982654188, 982654189), (185447420, 185447422)), ((982875933, 982875934),
  (184268550, 184268552)), ((983097695, 983097696), (183081732, 183081734)), ((983319473,
  983319475), (181886810, 181886812))]
/-- Chunk 9 of `solTrigIvs_r128`. -/
def solTrigIvs_r128_c9 : List (IvInt × IvInt) :=
  [((983541268, 983541269), (180683624, 180683626)), ((983763080, 983763081), (179472008,
  179472010)), ((983984908, 983984909), (178251788, 178251790)), ((984206752, 984206753),
  (177022788, 177022790)), ((984428613, 984428614), (175784823, 175784825)), ((984650491,
  984650492), (174537703, 174537705))]
/-- Chunk 10 of `solTrigIvs_r128`. -/
def solTrigIvs_r128_c10 : List (IvInt × IvInt) :=
  [((984872385, 984872386), (173281229, 173281231)), ((985094295, 985094296), (172015197,
  172015199)), ((985316222, 985316224), (170739393, 170739395)), ((985538166, 985538167),
  (169453598, 169453599))]
/-- Stratum `(cosIv, sinIv)` intervals for WKB `r = 128`. -/
def solTrigIvs_r128 : List (IvInt × IvInt) :=
  List.append ( List.append ( List.append ( solTrigIvs_r128_c0) ( solTrigIvs_r128_c1)) (
  List.append ( solTrigIvs_r128_c2) ( List.append ( solTrigIvs_r128_c3) ( solTrigIvs_r128_c4)))) (
  List.append ( List.append ( solTrigIvs_r128_c5) ( List.append ( solTrigIvs_r128_c6) (
  solTrigIvs_r128_c7))) ( List.append ( solTrigIvs_r128_c8) ( List.append ( solTrigIvs_r128_c9) (
  solTrigIvs_r128_c10))))
/-- Chunk 0 of `solTailLbs_r128`. -/
def solTailLbs_r128_c0 : List (ℤ) :=
  [999995208, 999992542, 999989732, 999984065, 999982538, 999980123, 999974486, 999973211,
  999963937, 999963796, 999954830, 999945467, 999930887, 999923163, 999918414, 999896189,
  999849480, 999759285, 999734834, 999682900]
/-- Chunk 1 of `solTailLbs_r128`. -/
def solTailLbs_r128_c1 : List (ℤ) :=
  [999658617, 999654515, 999582591, 999572485, 999481664, 999449822, 999390586, 999371424,
  999318166, 999305197, 999198336, 999169250, 999073340, 999011854, 998976424, 998937744,
  998937677, 998935725, 998935589, 998934539]
/-- Chunk 2 of `solTailLbs_r128`. -/
def solTailLbs_r128_c2 : List (ℤ) :=
  [998928295, 998898526, 998861803, 998844446, 998820432, 998799362, 998777210, 998759541,
  998744385, 998723051, 998572734, 998352889, 998319148, 998140289, 997893967, 997360528,
  996777717, 996595953, 996373055, 996105333]
/-- Chunk 3 of `solTailLbs_r128`. -/
def solTailLbs_r128_c3 : List (ℤ) :=
  [995972916, 995881094, 995328791, 995292425]
/-- Certified suffix probability lower bounds for WKB `r = 128`. -/
def solTailLbs_r128 : List (ℤ) :=
  List.append ( List.append ( solTailLbs_r128_c0) ( solTailLbs_r128_c1)) ( List.append (
  solTailLbs_r128_c2) ( solTailLbs_r128_c3))
/-- Stage specification for WKB Multi-pulse conveyor at `r = 128`. -/
def solStage_r128 : PulseM1StageSpec :=
  ⟨64, 238946, 1000000, solWkbToSwLPulses solWkbSched_r128⟩
/-- WKB `L2Ball` center checkpoint after pulse `392` at `r = 128`. -/
def solCkptEnd_r128 : List ℤ :=
  List.append ( List.append ( [1542705, 222526, (-1617738), (-61815), (-1675159), 1036770,
  2143101, 1168014, (-403252), (-1120115), (-1077409), 1100276, 2103965, 888273, 697428,
  (-2069274), (-2234550), (-305736), 219152, 1864691, 2343083, (-1968149), (-2343031), (-2448050),
  (-2930707), 2335426, 1506969, 742263, (-2049069), (-2340687), (-4092590), 5047155]) ( [4608777,
  6678477, 6753094, (-4645133), (-1696295), (-6845677), (-2253334), 1933190, 4533078, 1612018,
  1226334, (-5122509), (-6759683), (-1365203), (-2871073), 7196387, 6248580, 3883279, 4094692,
  (-5993978), (-4828683), (-3714017), (-2317590), 4607675, 5659893, 2574555, 2518333, (-6868927),
  (-7726176), (-3030232), (-4461833), 6945702])) ( List.append ( [6905060, 5119666, 5939988,
  (-4445663), (-3958719), (-5562185), (-2783373), (-83309), 245904, 1079064, 887885, 359954,
  (-78994), (-1012641), 157421, 1445105, 2038655, 3077991, 4505527, 794310, 6008040, (-1774118),
  3769953, (-4731096), 1278225, (-3161483), 3328348, 1740060, 4373538, 1647722, 3867340,
  (-3252740)]) ( [(-2139591), (-3343766), (-3186965), 8815871, 8521719, 11109667, 9821073,
  5549587, 1716994, (-561244), (-13363092), 4592192, (-15009121), 11762078, (-19879308), 3470241,
  (-23893199), (-6635553), (-11737704), (-8621425), (-12191111), (-10019030), (-12938803),
  (-11438040), (-1275722), 7371677, (-6124512), 21170086, (-10216588), 6027725, 245425,
  10587310]))

/-- Midpoint checkpoint `solCkpt_r256_s4`. -/
def solCkpt_r256_s4 : List ℤ :=
  List.append ( List.append ( List.append ( [(-1460429), 227306, 1826662, 660779, 936965,
  (-477977), (-1394010), (-2001323), (-472765), 1819111, 2182940, 611529, 375153, (-3280988),
  (-3492924), 534302, 904731, 3073506, 3338953, (-1459897), (-2672704), (-1381907), (-1813510),
  3842978, 5642308, 2610343, 3107360, (-3299943), (-2330345), (-1820391), 2404386, 1497244]) (
  [4410890, (-3641753), (-4231462), (-6296244), (-7005005), 1347701, 3409026, 5847098, 6222724,
  (-2006523), (-2287926), (-5447648), (-4786303), 2411230, 3749441, 4890166, 6274336, (-4144332),
  (-3190317), (-6120896), (-5780787), 3120053, 3244787, 6503519, 6859286, (-1378483), (-1720923),
  (-6048149), (-7266788), 1756063, 84105, 8119239])) ( List.append ( [7993849, 32449, 2615876,
  (-9111829), (-7559473), (-4627416), (-5263944), 6998842, 4824495, 7918682, 6772274, (-2713525),
  (-1184301), (-6947737), (-5371028), (-669545), 285029, 4914486, 4017942, 844990, (-601326),
  (-4478802), (-4950613), (-863516), (-437613), 5852029, 5849983, 2778962, 3869629, (-5939202),
  (-3415290), (-6241320)]) ( [(-6659408), 2287849, (-892571), 6413161, 5736975, 1613983, 3251643,
  (-3313258), (-2764857), (-3927853), (-2970067), 612594, (-587915), 3501486, 2126281, 435232,
  1705680, (-1646872), (-1294554), (-1895181), (-1264734), (-217818), (-879912), 2373444, 1299661,
  1170577, 2006001, (-127132), (-153757), (-2614033), (-1456863), (-17758)]))) ( List.append (
  List.append ( [(-1552598), 1646687, 1957029, 2098896, 2031917, (-1394384), 202776, (-2295979),
  (-2989420), (-1371676), (-1366942), 2899518, 1571672, 2433867, 3140173, (-471188), 830810,
  (-3352476), (-2640830), (-1542538), (-1874916), 981025, (-494709), 1981753, 2002917, 1240774,
  1064163, (-1389262), (-504339), (-673085), (-904184), (-908961)]) ( [(-998680), 621197, 884324,
  1231525, 1672545, 2345558, 2679721, 389108, (-2222721), (-4293941), (-7656175), (-7079791),
  (-9802951), (-4125630), (-3486682), 3533174, 3723832, 7927380, 7837934, 9535287, 8344464,
  8302312, 8781745, 9766128, 11342171, 9810349, 10397821, 8465584, 10831930, 9531143, 14640684,
  13452538])) ( List.append ( [21907208, 19470697, 30418725, 24529314, 37187886, 28238364,
  40124602, 29411369, 43785857, 36993593, 75306072, 77192813, 131436103, 113652808, 143726430,
  122570512, 217732255, 220007172, 282340037, 235305607, 332198521, 300282728, 363937736,
  295139992, 313288667, 236544282, 223946199, 153707195, 128623731, 81242772, 62117200, 36828684])
  ( [26426699, 14894109, 10109873, 5435822, 3496368, 1795872, 1095967, 538557, 313060, 147651,
  81910, 37133, 19695, 8563, 4347, 1789, 850, 309, 121, 24, 4, 0])))
/-- Chunk 0 of `solWkb_rBulkQ_r256`. -/
def solWkb_rBulkQ_r256_c0 : List (ℤ) :=
  [41, 11264, 38842, 67074, 79430, 80277, 81241, 82288, 83249, 84077, 84906, 85833, 86841, 87907,
  88907, 89629, 90523, 92333, 93864, 93718]
/-- Chunk 1 of `solWkb_rBulkQ_r256`. -/
def solWkb_rBulkQ_r256_c1 : List (ℤ) :=
  [92743, 92684, 93488, 93750, 93402, 94938, 100621, 103178, 93395, 87026, 100469, 108607, 89428,
  88726, 119377, 88522, 105178, 103757, 100720, 101442]
/-- Chunk 2 of `solWkb_rBulkQ_r256`. -/
def solWkb_rBulkQ_r256_c2 : List (ℤ) :=
  [100393, 98419, 96815, 95700, 94891, 94171, 93402, 92560, 91683, 90812, 89966, 89144, 88338,
  87541, 86749, 85964, 85185, 84416, 83659, 82917]
/-- Chunk 3 of `solWkb_rBulkQ_r256`. -/
def solWkb_rBulkQ_r256_c3 : List (ℤ) :=
  [82188, 69540, 40381, 11724, 0]
/-- WKB bulk profile table for `r = 256`. -/
def solWkb_rBulkQ_r256 : List (ℤ) :=
  List.append ( List.append ( solWkb_rBulkQ_r256_c0) ( solWkb_rBulkQ_r256_c1)) ( List.append (
  solWkb_rBulkQ_r256_c2) ( solWkb_rBulkQ_r256_c3))
/-- Chunk 0 of `solWkb_uLnchQ_r256`. -/
def solWkb_uLnchQ_r256_c0 : List (ℤ) :=
  [95687, 70033, 44300, 29983, 17651, 12955, 9442, 6489, 4068, 2657, 1554, 623, 1609, 47095,
  78261, 61362, 20793, 0, (-18166), 30435]
/-- Chunk 1 of `solWkb_uLnchQ_r256`. -/
def solWkb_uLnchQ_r256_c1 : List (ℤ) :=
  [35362, 29082, 22487, 16734, 11488, 6468, 2236, (-423), (-2602), (-4467), (-5877), (-4787),
  40914, 56890, 19184, 0, (-23234), (-2172), 13145, 21775]
/-- Chunk 2 of `solWkb_uLnchQ_r256`. -/
def solWkb_uLnchQ_r256_c2 : List (ℤ) :=
  [22436, 20164, 16643, 12685, 9050, 5963, 2974, 75, (-2243), (-3902), (-2840), 34387, 19923, 0,
  (-32590), (-12521), 2440, 9583, 15762, 19188]
/-- Chunk 3 of `solWkb_uLnchQ_r256`. -/
def solWkb_uLnchQ_r256_c3 : List (ℤ) :=
  [18566, 15861, 13144, 10466, 7706, 4881, 2426, 444, (-1304), (-155), 12709, 0, (-23320),
  (-26415), (-9114), 2393, 8259, 11541, 15190, 15280]
/-- Chunk 4 of `solWkb_uLnchQ_r256`. -/
def solWkb_uLnchQ_r256_c4 : List (ℤ) :=
  [13867, 12147, 10389, 8465, 6438, 4390, 2331, 193, 437, 0, (-35633), (-21756), (-15941),
  (-7748), 1962, 7212, 9263, 13125, 13989, 13507]
/-- Chunk 5 of `solWkb_uLnchQ_r256`. -/
def solWkb_uLnchQ_r256_c5 : List (ℤ) :=
  [12679, 11507, 9956, 8062, 6003, 3085, 539, 0, (-37286), (-21798), (-18864), (-10729), (-5584),
  1237, 6352, 7618, 11514, 12791, 12561, 11652]
/-- Chunk 6 of `solWkb_uLnchQ_r256`. -/
def solWkb_uLnchQ_r256_c6 : List (ℤ) :=
  [10567, 9269, 7853, 5133, 1374, 0, (-31578), (-27342), (-18330), (-18684), (-7314), (-4064),
  1044, 5556, 6640, 9874, 10934, 10857, 10460, 9910]
/-- Chunk 7 of `solWkb_uLnchQ_r256`. -/
def solWkb_uLnchQ_r256_c7 : List (ℤ) :=
  [9213, 6738, 2041, 0, (-29697), (-29964), (-24402), (-14363), (-16181), (-5851), (-2912), 905,
  4955, 5651, 8579, 10024, 10431, 10474, 10278, 7838]
/-- Chunk 8 of `solWkb_uLnchQ_r256`. -/
def solWkb_uLnchQ_r256_c8 : List (ℤ) :=
  [2479, 0, (-31816), (-30516), (-27984), (-18701), (-14003), (-14085), (-4492), (-2194), 1320,
  4342, 5734, 8049, 9440, 10042, 10100, 7807, 2536, 0]
/-- Chunk 9 of `solWkb_uLnchQ_r256`. -/
def solWkb_uLnchQ_r256_c9 : List (ℤ) :=
  [(-33899), (-29595), (-26929), (-23616), (-15560), (-12640), (-10861), (-3948), (-1246), 1464,
  3806, 5016, 7044, 8526, 8968, 7180, 2450, 0, (-34036), (-28440)]
/-- Chunk 10 of `solWkb_uLnchQ_r256`. -/
def solWkb_uLnchQ_r256_c10 : List (ℤ) :=
  [(-23681), (-23848), (-19726), (-12512), (-11957), (-9233), (-3561), (-588), 1539, 3312, 4601,
  6260, 7545, 6595, 2398, 0, (-33201), (-27837), (-22736), (-21939)]
/-- Chunk 11 of `solWkb_uLnchQ_r256`. -/
def solWkb_uLnchQ_r256_c11 : List (ℤ) :=
  [(-21592), (-17069), (-11422), (-11765), (-7766), (-3148), (-445), 1440, 3032, 4211, 5763, 5835,
  2242, 0, (-32527), (-28041), (-23848), (-21069), (-20523), (-19391)]
/-- Chunk 12 of `solWkb_uLnchQ_r256`. -/
def solWkb_uLnchQ_r256_c12 : List (ℤ) :=
  [(-14450), (-10683), (-10573), (-5645), (-3109), (-528), 1213, 2729, 4011, 4386, 1902, 1,
  (-32390), (-28806), (-25275), (-21972), (-19008), (-19427), (-17367), (-12750)]
/-- Chunk 13 of `solWkb_uLnchQ_r256`. -/
def solWkb_uLnchQ_r256_c13 : List (ℤ) :=
  [(-9093), (-9205), (-5021), (-3086), (-948), 482, 2152, 2808, 1400, 31, (-20619), (-23449),
  (-20831), (-18024), (-15079), (-14197), (-14414), (-12519), (-8634), (-6913)]
/-- Chunk 14 of `solWkb_uLnchQ_r256`. -/
def solWkb_uLnchQ_r256_c14 : List (ℤ) :=
  [(-6807), (-3442), (-2682), (-1452), (-366), 1267, 938, 50, 6709, (-6287), (-7178), (-6249),
  (-5348), (-4551), (-4227), (-4420), (-3531), (-2647), (-2470), (-2185)]
/-- Chunk 15 of `solWkb_uLnchQ_r256`. -/
def solWkb_uLnchQ_r256_c15 : List (ℤ) :=
  [(-1141), (-1690), (-947), (-315), 469, 125, 0, 0, 0, (-11), (-35), (-56), 10, (-123), 166, 71,
  (-3), (-253), 185, (-304)]
/-- Chunk 16 of `solWkb_uLnchQ_r256`. -/
def solWkb_uLnchQ_r256_c16 : List (ℤ) :=
  [(-581), (-222), (-70), 93]
/-- WKB launch correction table for `r = 256`. -/
def solWkb_uLnchQ_r256 : List (ℤ) :=
  List.append ( List.append ( List.append ( List.append ( solWkb_uLnchQ_r256_c0) (
  solWkb_uLnchQ_r256_c1)) ( List.append ( solWkb_uLnchQ_r256_c2) ( solWkb_uLnchQ_r256_c3))) (
  List.append ( List.append ( solWkb_uLnchQ_r256_c4) ( solWkb_uLnchQ_r256_c5)) ( List.append (
  solWkb_uLnchQ_r256_c6) ( solWkb_uLnchQ_r256_c7)))) ( List.append ( List.append ( List.append (
  solWkb_uLnchQ_r256_c8) ( solWkb_uLnchQ_r256_c9)) ( List.append ( solWkb_uLnchQ_r256_c10) (
  solWkb_uLnchQ_r256_c11))) ( List.append ( List.append ( solWkb_uLnchQ_r256_c12) (
  solWkb_uLnchQ_r256_c13)) ( List.append ( solWkb_uLnchQ_r256_c14) ( List.append (
  solWkb_uLnchQ_r256_c15) ( solWkb_uLnchQ_r256_c16)))))
/-- Chunk 0 of `solWkb_uLandQ_r256`. -/
def solWkb_uLandQ_r256_c0 : List (ℤ) :=
  [(-84448), (-82383), (-80378), (-78289), (-76200), (-74100), (-38259), 4727, 5414, 5415, 5415,
  5414, 5414, 5414, 5414, 4338, 1500, 0, 28746, 14305]
/-- Chunk 1 of `solWkb_uLandQ_r256`. -/
def solWkb_uLandQ_r256_c1 : List (ℤ) :=
  [2412, (-5671), (-11693), (-8403), (-3771), 36347, 80941, 80200, 78009, 75260, 72429, 69560,
  66644, 50955, 16756, 0, 20363, 13746, 9438, 5507]
/-- Chunk 2 of `solWkb_uLandQ_r256`. -/
def solWkb_uLandQ_r256_c2 : List (ℤ) :=
  [1797, 605, 466, 1875, 38898, 81160, 81572, 82137, 82261, 81681, 80810, 63859, 21637, 0, 13936,
  12848, 11682, 6804, 3710, 1639]
/-- Chunk 3 of `solWkb_uLandQ_r256`. -/
def solWkb_uLandQ_r256_c3 : List (ℤ) :=
  [237, 647, 1870, 40002, 81219, 81244, 80975, 80726, 80849, 64989, 22431, 0, 10097, 10715, 11990,
  10203, 8570, 6828, 4405, 2759]
/-- Chunk 4 of `solWkb_uLandQ_r256`. -/
def solWkb_uLandQ_r256_c4 : List (ℤ) :=
  [2332, 3055, 41063, 80586, 79646, 79002, 79133, 63935, 22260, 1, 11016, 9714, 11262, 7843, 7121,
  8815, 8569, 6763, 4864, 3901]
/-- Chunk 5 of `solWkb_uLandQ_r256`. -/
def solWkb_uLandQ_r256_c5 : List (ℤ) :=
  [3804, 42011, 80039, 78827, 78402, 63066, 21948, 1, 8809, 6171, 5878, 4427, 5914, 8533, 10322,
  10405, 8914, 6735, 5480, 4812]
/-- Chunk 6 of `solWkb_uLandQ_r256`. -/
def solWkb_uLandQ_r256_c6 : List (ℤ) :=
  [42935, 79655, 78540, 62687, 21690, 1, 6374, (-1964), (-2398), 264, 3361, 5301, 7752, 10132,
  11182, 9757, 8019, 6650, 5523, 44014]
/-- Chunk 7 of `solWkb_uLandQ_r256`. -/
def solWkb_uLandQ_r256_c7 : List (ℤ) :=
  [79814, 63032, 21655, 1, 5120, (-9115), (-6393), (-3806), (-984), 2075, 4488, 7564, 10405,
  11096, 10306, 8827, 7870, 6528, 45401, 64146]
/-- Chunk 8 of `solWkb_uLandQ_r256`. -/
def solWkb_uLandQ_r256_c8 : List (ℤ) :=
  [21844, 4, 21880, 698, (-1972), (-5098), (-5283), (-2268), 288, 3546, 7322, 10072, 10743, 9586,
  9192, 8550, 6970, 37058, 22232, 5]
/-- Chunk 9 of `solWkb_uLandQ_r256`. -/
def solWkb_uLandQ_r256_c9 : List (ℤ) :=
  [1537, 9351, 4979, (-505), (-3388), (-4457), (-3421), (-699), 3097, 7262, 9135, 8871, 9253,
  9663, 9054, 5597, 13130, 3, (-18491), (-4275)]
/-- Chunk 10 of `solWkb_uLandQ_r256`. -/
def solWkb_uLandQ_r256_c10 : List (ℤ) :=
  [5734, 5225, 1497, (-1292), (-3120), (-2843), (-1316), 2468, 5944, 7411, 8328, 8950, 9238, 6468,
  1984, 15, (-21465), (-16837), (-4038), 4248]
/-- Chunk 11 of `solWkb_uLandQ_r256`. -/
def solWkb_uLandQ_r256_c11 : List (ℤ) :=
  [3937, 1350, (-414), (-1700), (-1904), (-296), 2540, 5248, 6163, 6096, 6791, 5788, 2025, 13,
  (-16931), (-16079), (-12349), (-2789), 3174, 2847]
/-- Chunk 12 of `solWkb_uLandQ_r256`. -/
def solWkb_uLandQ_r256_c12 : List (ℤ) :=
  [878, (-645), (-1136), (-630), 629, 2860, 4029, 3632, 4524, 4685, 1847, (-5), (-17031),
  (-16502), (-16731), (-10679), (-2214), 2287, 1786, (-63)]
/-- Chunk 13 of `solWkb_uLandQ_r256`. -/
def solWkb_uLandQ_r256_c13 : List (ℤ) :=
  [(-1198), (-1246), (-316), 1100, 2210, 2729, 3529, 3299, 1207, (-3), (-14611), (-14619),
  (-14502), (-10915), (-6980), (-1775), 1334, 1089, 129, (-944)]
/-- Chunk 14 of `solWkb_uLandQ_r256`. -/
def solWkb_uLandQ_r256_c14 : List (ℤ) :=
  [(-702), 73, 699, 1556, 2522, 1718, 532, 8, (-5425), (-5108), (-4755), (-3997), (-3266),
  (-2380), (-805), 364, 441, 27, (-521), (-620)]
/-- Chunk 15 of `solWkb_uLandQ_r256`. -/
def solWkb_uLandQ_r256_c15 : List (ℤ) :=
  [(-423), (-3), 538, 495, 191, 8, 0, 0, 0, (-4), (-18), (-30), (-182), (-139), 156, 132, (-156),
  (-375), (-298), (-204)]
/-- Chunk 16 of `solWkb_uLandQ_r256`. -/
def solWkb_uLandQ_r256_c16 : List (ℤ) :=
  [(-73), 2, (-2), (-1)]
/-- WKB landing correction table for `r = 256`. -/
def solWkb_uLandQ_r256 : List (ℤ) :=
  List.append ( List.append ( List.append ( List.append ( solWkb_uLandQ_r256_c0) (
  solWkb_uLandQ_r256_c1)) ( List.append ( solWkb_uLandQ_r256_c2) ( solWkb_uLandQ_r256_c3))) (
  List.append ( List.append ( solWkb_uLandQ_r256_c4) ( solWkb_uLandQ_r256_c5)) ( List.append (
  solWkb_uLandQ_r256_c6) ( solWkb_uLandQ_r256_c7)))) ( List.append ( List.append ( List.append (
  solWkb_uLandQ_r256_c8) ( solWkb_uLandQ_r256_c9)) ( List.append ( solWkb_uLandQ_r256_c10) (
  solWkb_uLandQ_r256_c11))) ( List.append ( List.append ( solWkb_uLandQ_r256_c12) (
  solWkb_uLandQ_r256_c13)) ( List.append ( solWkb_uLandQ_r256_c14) ( List.append (
  solWkb_uLandQ_r256_c15) ( solWkb_uLandQ_r256_c16)))))
/-- Chunk 0 of `solWkb_vDrainQ_r256`. -/
def solWkb_vDrainQ_r256_c0 : List (ℤ) :=
  [35158, 204947, 283131, 283564, 281836, 284411, 288262, 294336, 305383, 320185, 337016, 339807,
  291123, 131510, (-43306), (-43679), 11133, 11655, (-9364), (-11918)]
/-- Chunk 1 of `solWkb_vDrainQ_r256`. -/
def solWkb_vDrainQ_r256_c1 : List (ℤ) :=
  [(-1391), 2307, 194, 0]
/-- WKB drain probe table for `r = 256`. -/
def solWkb_vDrainQ_r256 : List (ℤ) :=
  List.append ( solWkb_vDrainQ_r256_c0) ( solWkb_vDrainQ_r256_c1)
/-- Compact pure-integer WKB spline schedule for `r = 256` (`L = 128`). -/
def solWkbSched_r256 : SolWkbSched where
  r := 256
  L := 128
  K := 780
  tauNum := 216770
  tauDen := 1000000
  uvDen := 100000
  vBulkQ := 973
  sOffQ := (-1747)
  accelQ := 10
  rBulkQ := solWkb_rBulkQ_r256
  uLnchQ := solWkb_uLnchQ_r256
  uLandQ := solWkb_uLandQ_r256
  vDrainQ := solWkb_vDrainQ_r256
/-- Chunk 0 of `solTrigIvs_r256`. -/
def solTrigIvs_r256_c0 : List (IvInt × IvInt) :=
  [((976597238, 976597240), (215076341, 215076342)), ((976688299, 976688300), (214662446,
  214662448)), ((976779362, 976779363), (214247700, 214247702)), ((976870427, 976870429),
  (213832099, 213832101)), ((976961496, 976961497), (213415636, 213415638)), ((977052567,
  977052569), (212998308, 212998310))]
/-- Chunk 1 of `solTrigIvs_r256`. -/
def solTrigIvs_r256_c1 : List (IvInt × IvInt) :=
  [((977143641, 977143643), (212580108, 212580110)), ((977234718, 977234720), (212161032,
  212161034)), ((977325798, 977325799), (211741075, 211741077)), ((977416881, 977416882),
  (211320230, 211320232)), ((977507966, 977507967), (210898494, 210898496)), ((977599054,
  977599055), (210475860, 210475862))]
/-- Chunk 2 of `solTrigIvs_r256`. -/
def solTrigIvs_r256_c2 : List (IvInt × IvInt) :=
  [((977690145, 977690146), (210052324, 210052326)), ((977781239, 977781240), (209627879,
  209627881)), ((977872335, 977872337), (209202520, 209202522)), ((977963435, 977963436),
  (208776241, 208776243)), ((978054537, 978054538), (208349038, 208349040)), ((978145642,
  978145643), (207920904, 207920906))]
/-- Chunk 3 of `solTrigIvs_r256`. -/
def solTrigIvs_r256_c3 : List (IvInt × IvInt) :=
  [((978236749, 978236751), (207491833, 207491835)), ((978327860, 978327861), (207061819,
  207061821)), ((978418973, 978418974), (206630858, 206630860)), ((978510089, 978510090),
  (206198942, 206198944)), ((978601208, 978601209), (205766066, 205766068)), ((978692330,
  978692331), (205332224, 205332226))]
/-- Chunk 4 of `solTrigIvs_r256`. -/
def solTrigIvs_r256_c4 : List (IvInt × IvInt) :=
  [((978783454, 978783455), (204897409, 204897411)), ((978874581, 978874583), (204461615,
  204461617)), ((978965712, 978965713), (204024837, 204024839)), ((979056844, 979056846),
  (203587067, 203587069)), ((979147980, 979147981), (203148299, 203148301)), ((979239118,
  979239120), (202708528, 202708530))]
/-- Chunk 5 of `solTrigIvs_r256`. -/
def solTrigIvs_r256_c5 : List (IvInt × IvInt) :=
  [((979330260, 979330261), (202267745, 202267747)), ((979421404, 979421405), (201825945,
  201825947)), ((979512551, 979512552), (201383121, 201383123)), ((979603700, 979603701),
  (200939267, 200939269)), ((979694853, 979694854), (200494374, 200494376)), ((979786008,
  979786009), (200048437, 200048439))]
/-- Chunk 6 of `solTrigIvs_r256`. -/
def solTrigIvs_r256_c6 : List (IvInt × IvInt) :=
  [((979877166, 979877167), (199601448, 199601450)), ((979968327, 979968328), (199153401,
  199153403)), ((980059490, 980059492), (198704287, 198704289)), ((980150657, 980150658),
  (198254101, 198254103)), ((980241826, 980241827), (197802834, 197802836)), ((980332998,
  980332999), (197350479, 197350481))]
/-- Chunk 7 of `solTrigIvs_r256`. -/
def solTrigIvs_r256_c7 : List (IvInt × IvInt) :=
  [((980424173, 980424174), (196897029, 196897031)), ((980515350, 980515352), (196442475,
  196442477)), ((980606531, 980606532), (195986811, 195986813)), ((980697714, 980697715),
  (195530029, 195530031)), ((980788900, 980788901), (195072120, 195072122)), ((980880089,
  980880090), (194613078, 194613080))]
/-- Chunk 8 of `solTrigIvs_r256`. -/
def solTrigIvs_r256_c8 : List (IvInt × IvInt) :=
  [((980971280, 980971282), (194152892, 194152894)), ((981062475, 981062476), (193691557,
  193691559)), ((981153672, 981153673), (193229063, 193229064)), ((981244872, 981244873),
  (192765401, 192765403)), ((981336075, 981336076), (192300565, 192300567)), ((981427280,
  981427281), (191834544, 191834546))]
/-- Chunk 9 of `solTrigIvs_r256`. -/
def solTrigIvs_r256_c9 : List (IvInt × IvInt) :=
  [((981518489, 981518490), (191367330, 191367332)), ((981609700, 981609701), (190898915,
  190898917)), ((981700914, 981700915), (190429290, 190429292)), ((981792130, 981792132),
  (189958446, 189958448)), ((981883350, 981883351), (189486373, 189486375)), ((981974572,
  981974574), (189013062, 189013064))]
/-- Chunk 10 of `solTrigIvs_r256`. -/
def solTrigIvs_r256_c10 : List (IvInt × IvInt) :=
  [((982065797, 982065799), (188538505, 188538507)), ((982157025, 982157027), (188062691,
  188062693)), ((982248256, 982248257), (187585612, 187585614)), ((982339490, 982339491),
  (187107257, 187107259)), ((982430726, 982430727), (186627616, 186627618)), ((982521965,
  982521966), (186146680, 186146682))]
/-- Chunk 11 of `solTrigIvs_r256`. -/
def solTrigIvs_r256_c11 : List (IvInt × IvInt) :=
  [((982613207, 982613208), (185664439, 185664441)), ((982704452, 982704453), (185180881,
  185180883)), ((982795699, 982795700), (184695999, 184696000)), ((982886950, 982886951),
  (184209779, 184209781)), ((982978203, 982978204), (183722213, 183722214)), ((983069459,
  983069460), (183233288, 183233290))]
/-- Chunk 12 of `solTrigIvs_r256`. -/
def solTrigIvs_r256_c12 : List (IvInt × IvInt) :=
  [((983160717, 983160719), (182742995, 182742997)), ((983251979, 983251980), (182251322,
  182251324)), ((983343243, 983343244), (181758258, 181758260)), ((983434510, 983434512),
  (181263792, 181263794)), ((983525780, 983525781), (180767912, 180767914)), ((983617053,
  983617054), (180270607, 180270608))]
/-- Chunk 13 of `solTrigIvs_r256`. -/
def solTrigIvs_r256_c13 : List (IvInt × IvInt) :=
  [((983708328, 983708330), (179771864, 179771866)), ((983799607, 983799608), (179271671,
  179271673)), ((983890888, 983890889), (178770018, 178770019)), ((983982172, 983982173),
  (178266890, 178266892)), ((984073459, 984073460), (177762276, 177762278)), ((984164748,
  984164749), (177256163, 177256165))]
/-- Chunk 14 of `solTrigIvs_r256`. -/
def solTrigIvs_r256_c14 : List (IvInt × IvInt) :=
  [((984256040, 984256041), (176748538, 176748540)), ((984347335, 984347337), (176239388,
  176239389)), ((984438633, 984438635), (175728699, 175728701)), ((984529934, 984529935),
  (175216459, 175216461)), ((984621238, 984621239), (174702654, 174702655)), ((984712544,
  984712545), (174187269, 174187270))]
/-- Chunk 15 of `solTrigIvs_r256`. -/
def solTrigIvs_r256_c15 : List (IvInt × IvInt) :=
  [((984803853, 984803854), (173670291, 173670292)), ((984895165, 984895166), (173151705,
  173151707)), ((984986480, 984986481), (172631497, 172631499)), ((985077797, 985077798),
  (172109652, 172109654)), ((985169117, 985169118), (171586156, 171586158)), ((985260440,
  985260442), (171060993, 171060994))]
/-- Chunk 16 of `solTrigIvs_r256`. -/
def solTrigIvs_r256_c16 : List (IvInt × IvInt) :=
  [((985351766, 985351767), (170534147, 170534149)), ((985443095, 985443096), (170005603,
  170005605)), ((985534426, 985534428), (169475346, 169475348)), ((985625761, 985625762),
  (168943358, 168943360)), ((985717098, 985717099), (168409624, 168409626)), ((985808438,
  985808439), (167874127, 167874129))]
/-- Chunk 17 of `solTrigIvs_r256`. -/
def solTrigIvs_r256_c17 : List (IvInt × IvInt) :=
  [((985899780, 985899782), (167336851, 167336852)), ((985991126, 985991127), (166797776,
  166797778)), ((986082474, 986082475), (166256888, 166256890)), ((986173825, 986173826),
  (165714166, 165714168)), ((986265179, 986265180), (165169595, 165169596)), ((986356536,
  986356537), (164623154, 164623156))]
/-- Chunk 18 of `solTrigIvs_r256`. -/
def solTrigIvs_r256_c18 : List (IvInt × IvInt) :=
  [((986447895, 986447896), (164074826, 164074828)), ((986539258, 986539259), (163524591,
  163524593)), ((986630623, 986630624), (162972430, 162972432)), ((986721991, 986721992),
  (162418324, 162418326)), ((986813361, 986813362), (161862252, 161862254)), ((986904735,
  986904736), (161304194, 161304196))]
/-- Chunk 19 of `solTrigIvs_r256`. -/
def solTrigIvs_r256_c19 : List (IvInt × IvInt) :=
  [((986996111, 986996112), (160744130, 160744132)), ((987087490, 987087491), (160182039,
  160182040)), ((987178872, 987178873), (159617898, 159617899)), ((987270257, 987270258),
  (159051686, 159051688)), ((987361644, 987361645), (158483381, 158483383)), ((987453034,
  987453036), (157912961, 157912963))]
/-- Chunk 20 of `solTrigIvs_r256`. -/
def solTrigIvs_r256_c20 : List (IvInt × IvInt) :=
  [((987544428, 987544429), (157340402, 157340404)), ((987635823, 987635825), (156765681,
  156765683)), ((987727222, 987727223), (156188775, 156188776)), ((987818624, 987818625),
  (155609657, 155609659)), ((987910028, 987910029), (155028305, 155028307)), ((988001435,
  988001436), (154444693, 154444694))]
/-- Chunk 21 of `solTrigIvs_r256`. -/
def solTrigIvs_r256_c21 : List (IvInt × IvInt) :=
  [((988092845, 988092846), (153858794, 153858796)), ((988184258, 988184259), (153270583,
  153270585))]
/-- Stratum `(cosIv, sinIv)` intervals for WKB `r = 256`. -/
def solTrigIvs_r256 : List (IvInt × IvInt) :=
  List.append ( List.append ( List.append ( List.append ( solTrigIvs_r256_c0) (
  solTrigIvs_r256_c1)) ( List.append ( solTrigIvs_r256_c2) ( List.append ( solTrigIvs_r256_c3) (
  solTrigIvs_r256_c4)))) ( List.append ( List.append ( solTrigIvs_r256_c5) ( List.append (
  solTrigIvs_r256_c6) ( solTrigIvs_r256_c7))) ( List.append ( solTrigIvs_r256_c8) ( List.append (
  solTrigIvs_r256_c9) ( solTrigIvs_r256_c10))))) ( List.append ( List.append ( List.append (
  solTrigIvs_r256_c11) ( solTrigIvs_r256_c12)) ( List.append ( solTrigIvs_r256_c13) ( List.append
  ( solTrigIvs_r256_c14) ( solTrigIvs_r256_c15)))) ( List.append ( List.append (
  solTrigIvs_r256_c16) ( List.append ( solTrigIvs_r256_c17) ( solTrigIvs_r256_c18))) ( List.append
  ( solTrigIvs_r256_c19) ( List.append ( solTrigIvs_r256_c20) ( solTrigIvs_r256_c21)))))
private def _k0_0 : List ℤ := _uPk [701243462104774,6663331741347319,36449646621985614,
  16515565468865262,8719562277386332,17895646467424538,58091537553741638,137221020494364378,
  141470724470532230,287296000554213814,287296000457173920,287296001003568342,287296000738801948,
  287296000867439882,287296000475373104,287296000558274598,142421075916303534,51258900048219386,
  14745639827922710,3283191897140556,581175153788204,83786448280682,9870976036002,945504003774,
  64320000308,1072000010,287296000000000000]
private def _k0_1 : List ℤ := _uPk [468373418702051,2299673702571759,869639105960970,
  1015342129685065,13190588031116064,8918471322178588,5692727918227727,18447946184644538,
  4835722891050286,15125678277445671,2665279297584075,9084168766688048,12469712009953772,
  28067833036533316,18894347424464464,9290374438460696,52401202888695698,113504542693790332,
  113238178627656522,203249869016146142,287296000827737064,287296000649300630,287296000832363068,
  287296000551116340,287296000747190306,267712857761320178,148167815987217420,67610179326059110,
  24585234122539106,7503472595389142,1974314197466086,447207313330842,87140736279990,
  14603856050830,2073248007942,235840001028,11792000088,287296000000000000]
private def _k0_2 : List ℤ := _uPk [1887892234555337,1989278241315548,7299785205262,
  298990454884275,586010947542280,2008195293272345,5073350416965006,2475752384665264,
  5785721767800045,8726404821057872,7602747824564126,9079696918713629,13619951894713040,
  1859066714087858,10453915144613947,7809005447942785,15628418964046220,2214266406889230,
  1689087153811412,5829422380946022,5417536401006448,12451932872548212,26687893510057594,
  34736079335842396,25354340549500800,27171205800947834,68111357539012766,106635271718233006,
  121856056254476234,239584447140990698,287296000742708598,287296000568855776,287296000765154340,
  287296000601321134,287296000743883672,287296000505292294,287296000552864408,190105619192313350,
  94420196163085400,37891746110050720,12992895170831884,3835827195087952,983643619045538,
  221526656729396,43976656153872,7706608028616,1180272004678,140432000644,5360000050,
  287296000000000000]
private def _k0_3 : List ℤ := _uPk [702204490828697,850206418822692,218392131918952,
  2548015897109239,990340401501755,670719314814196,2383758697041314,788080268112339,
  2279308913515239,615886515717288,4027150777800757,1399517444827783,3173132876199894,
  9321807022451631,3794409398916805,2905616359840278,11654889597468007,2766540423780315,
  6206108187834918,13728284459012974,7458061074009395,11060148827328890,870708974731692,
  9878778563903369,3311888262357931,10472464497859202,8200649938969126,6147346495680512,
  4334623439529690,3370132174998050,6302660001220682,13245316860942502,30819191772122546,
  32634827481489720,20247355045193254,37844926490176062,83254527124037654,96616138868219218,
  161308483136988632,287296000580576452,287296000510014858,287296000689491314,287296000581892586,
  287296000787213044,287296000594353154,287296000687769612,277995079793968064,159383098274865344,
  72894834909393350,28365482409104588,9488803738410292,2766186664240472,711632194254732,
  162391920546050,33002592117512,5980688022532,947648003822,109344000534,3216000032,
  287296000000000000]
private def _k0_4 : List ℤ := _uPk [687861666840931,662812778992396,1581379562611452,
  886161836592953,1194432048838580,1025871306412974,1510840891594105,1742009650917279,
  1527403827496602,1691405354035312,437539486065329,3551160801427065,1735137062759720,
  1780368488504630,2572191107959913,4299469338224944,3968993718440906,8325823613238755,
  1368568277872397,3343838144954860,2810332160465428,9394944227706545,3031119678906789,
  9846251410650702,7515011052616596,3077382380531971,13103327232286142,604817600817732,
  11263399496562725,1734290186782795,6450676400321420,3616194225106324,5054451599035745,
  124752394564915,4935946825005060,7381011603799936,5781534004255506,6030210132760526,
  4042217221763998,1589025613150248,10824321700460666,26527769944429566,29539481074428336,
  20976796370981508,32543717108728382,68829244856804998,84592914866976786,147301648560681532,
  243233510542393026,287296000643071738,287296000576752790,287296000772757570,287296000619134968,
  287296000740237786,287296000561419036,287296000572487418,175606418286005222,82004980373657596,
  32549689237426892,11115768495516940,3323279338076812,877185442836982,205553856706528,
  42972192156702,8049648031030,1330352005478,171520000814,287296000000000066]
private def _k0_5 : List ℤ := _uPk [1601844576886901,1670229064879486,2058504248880235,
  1584517843884525,213980850347272,1621491656577879,1110188932070969,2106632225904220,
  1255475483854904,1533811706431403,3046440690269489,1449791030214090,3322217516213772,
  450885883252687,2258107972578380,5457386384076218,7560783312024583,3564326046983521,
  7554341120569417,1022005677623472,3782168766542053,3867320407675773,5702089144778182,
  3301700518218990,7818940201923883,107825526516759,6433594066090163,472228874277688,
  6591165737853644,1602029510592455,9740690483943791,9133016579440622,7877077978969362,
  4758907644113779,11872629417371892,5158105977235698,6155802953208621,1474015552355957,
  4947014149770218,4381489130634620,1015465403650724,4788068173610745,948337832236730,
  1481719484505200,3626917983270704,9080382455952994,7348851611756442,1300259902005008,
  4131939321195818,16809734013783488,26041850571028360,26649798938260708,23018051602410690,
  37729211601301742,68629179653995846,90239088485637690,171811719399804332,230443377753025268,
  287296000668245148,287296000616620096,287296000794989802,287296000704446276,287296000749224950,
  287296000584960612,164878916504183204,64527180269341426,22967089785229634]
private def _k0_6 : List ℤ := _uPk [1407155441680970,1403584073904307,813921899635705,
  2608956416369440,978676505528120,476916186948551,2446674912162490,147474508358614,
  2367119112918283,803476867442867,1922035972959432,2979681355876502,2730999869496595,
  1688283153168969,2328687916453612,4358117922138151,4625249069744393,7667962408004226,
  764264726033178,2765211674940061,4307237045292827,2833273497112328,6340420655092230,
  5786732659116075,4275357916364277,6906628006688876,2369829139353066,4826458637032373,
  3178928106930507,6803149991280008,3839804854972780,8679210555225497,708443009141065,
  7673240931904969,2705237037157478,1824118955703680,303778544767309,4387035655858779,
  5020032354219777,3127929841182506,6157812416769320,825184868920100,14447968466658777,
  1439783383143713,392859066960548,3547420056099403,833863777387894,5410447263445208,
  371995803430274,3681041641132064,1377930041753234,1957245273841998,1451411352869242,
  9809404624816788,9486816251956738,2263395087138794,8216140325904218,15140016811692458,
  21814940613237794,33299412784832694,29041219742996286,51274570475902686,100623975808820750,
  126389167833063722]
private theorem _c0_0 : _wkbPair solWkbSched_r128 solTrigIvs_r128 0 49 49 49 _cInit 1 0 0 _k0_0 23
  734 49000000000 _k0_1 35 1743 98000000000 = true := by decide +kernel
private theorem _c0_1 : _wkbPair solWkbSched_r128 solTrigIvs_r128 98 49 147 49 _k0_1 35 1743
  98000000000 _k0_2 46 2896 147000000000 _k0_3 56 4148 196000000000 = true := by decide +kernel
private theorem _c0_2 : _wkbPair solWkbSched_r128 solTrigIvs_r128 196 49 245 49 _k0_3 56 4148
  196000000000 _k0_4 64 5397 245000000000 _k0_5 64 6592 294000000000 = true := by decide +kernel
private theorem _c0_3 : _wkbPair solWkbSched_r128 solTrigIvs_r128 294 49 343 49 _k0_5 64 6592
  294000000000 _k0_6 64 7676 322586881915 solCkptEnd_r128 64 8679 323137279596 = true
  := by decide +kernel
private def _k1_0 : List ℤ := _uPk [8241830414332008,19957888219148450,64494219470277172,
  155777643929095764,287296000591282772,287296000343715548,287296000671861926,287296000435020362,
  287296001007330214,287296000754707152,287296000835150876,187754925828942790,65193299584136196,
  15744062041466212,2766917768260660,371539121234028,37965952141284,2969440012324,172592000818,
  4288000030,287296000000000000]
private def _k1_1 : List ℤ := _uPk [3117578621149373,8670215962881768,26538910665247087,
  9077877203265965,31253588677773218,21283128938029162,38421659296605548,29929259251335590,
  46266997001223516,150995302849564046,287296000539347096,287296000374241462,287296000538616390,
  287296000341267150,287296000725299378,287296000616180220,287296001005738680,287296000623527978,
  287296000590348678,175470763047688070,77282603791856234,26128064029372556,7364259458619610,
  1714573956756936,327214064998754,51751872172288,6882240024724,764336002982,58960000286,
  1072000008,287296000000000000]
private def _k1_2 : List ℤ := _uPk [1271296597291933,5416441339131014,7445998369580933,
  240162321995782,14833730880157735,16980836981024114,3949975931931254,22855467212823381,
  2828800597390035,10137424833141970,10314450634975958,30452626733395008,44451116891585402,
  30300646147123552,33276634988885412,111668267756129548,197781903639677886,170654211509550826,
  287296000563193886,287296000447262190,287296000926310460,287296000718960206,287296000764456072,
  257691932507557358,153250583923584022,70390622514614076,27181175388844756,9010592037850336,
  2518933078680178,599044321719986,123120272378110,22084272072174,3451840012040,454528001742,
  35376000192,287296000000000006]
private def _k1_3 : List ℤ := _uPk [3007664843993342,1929278406887731,2723602532495182,
  4133825496819531,6044180417657950,4988445344685360,5386443578938587,15040111779069560,
  7523313712319686,13194967698535153,15777786059902646,9140819701082926,12980742422117326,
  8849735743463541,830035140392782,37188773237918,11369597732812446,30779443106550272,
  41060923329878336,36612774047088442,34395632552114852,81787158544048584,176345650199000908,
  173190224746327344,190640321123216424,287296000773453352,287296000688419004,287296000871987762,
  287296000522118374,287296000572357978,218358196342251016,122494165275055636,57121952135377102,
  23218072852603856,8005170740081096,2341866550497520,590824225783856,130261936422644,
  25306704087494,4343744015896,643200002532,65392000326,1072000016,287296000000000000]
private def _k1_4 : List ℤ := _uPk [1959724272273193,984723659463268,2685338025853941,
  2934749010473319,333603728397134,3557251374205689,5479873185900294,3842288669230542,
  143066987282483,10714414898128440,8951716175550988,4054759088659475,17689996084780438,
  193783327901406,12601169737318467,9433013621065561,18636426314923740,4375368037490508,
  1540255508145740,1568417484369496,586344887170214,4059837681689942,19306798299205226,
  32310022189291194,46351234735004712,50021038085905466,46035752651212692,78412909862055318,
  165181196779260994,187032040926978824,186434311919715218,287296000643016406,287296000628223446,
  287296000892862834,287296000604477166,287296000608213590,259873381748478880,166207207980625836,
  87013814599098922,39735746906140992,15330070646320648,5022388621682842,1433786068182214,
  363582737122406,82635120268688,16870064057722,3076640011122,479184001888,46096000248,1072000008,
  287296000000000000]
private def _k1_5 : List ℤ := _uPk [931952850390587,69318739882846,659353433706536,
  2157870074754397,1836279185547239,1388860691731958,3092476123626692,2406539775252329,
  4851240592994570,856168352888712,3180081043174105,6402990613606680,6116699616600344,
  4558008409995553,12660032718166478,2823048240224602,12529858156619203,10887445333094487,
  13646110868150174,6526117857606776,4251501101123807,14241785862516914,16149089363030818,
  7445107562459274,6913675346294498,3026003022105156,380255021683020,6433298206482646,
  16847201494339682,28041842380020582,45112158159288654,50339081182568426,43487697620377348,
  66081091380985004,142143810601889114,183849770297067564,177308495969798712,287296000576681190,
  287296000563108576,287296000882191940,287296000642376926,287296000642505354,287296000452559576,
  287296000541056180,201943037697996892,114341298680640098,56741794140172674,23835837513535042,
  8506376838402268,2653645959478158,739718594201944,186192464582348,42410464139380,8732512030150,
  1606928005876,244416000986,17152000114,287296000000000002]
private def _k1_6 : List ℤ := _uPk [39018122955115,1298312067037448,1946754103680,2614370552061782,
  1048915555209535,2256439937683578,1349899390105736,3309547547437883,1626744997643471,
  3483114531300194,2716930939243208,2874747566592681,4512165929150539,4973174162691746,
  3567344248289920,1369532010634241,10644395058621830,2983018496056040,8364073666119253,
  12187864947776035,7124669609118072,13108693122183319,1512525024366797,16033317631444134,
  5615236792923256,8022153890751539,1623462542563891,11680658877916710,11319991993564692,
  10964459977616600,7515602281902078,426110365352316,1790772789262822,7964551583303228,
  13983808012920342,26476109187476928,41181562953175986,46746332131862900,43361798723567686,
  58294352448971254,123522420168208948,177291555128664678,172596718281616924,287296000539980882,
  287296000525374488,287296000856902172,287296000649009798,287296000659021648,287296000471905830,
  287296000578393438,228690474360281820,137149490176410030,72203793674541020,32151502331939636,
  12169293647367528,4037098411126644,1200854403495422,323881216989256,79448064254360,
  17727664059496,3580480012638,634624002392,76112000368,1072000018,287296000000000000]
private def _k1_7 : List ℤ := _uPk [993908554302077,2013593344990188,662507793702274,
  2119778698855490,103739051754101,2379335088922705,635423718497480,3783249336352660,
  174381710399529,3899393568440835,1503694941323704,4221755227192353,1688895276027863,
  4759690721823821,776252357734090,834776589446641,4529101383711939,6736080312500252,
  421464854244636,7579617275911285,1460478342042319,9653499366782828,1868144933838308,
  13005701808639359,4651059616999441,10702925205355576,7429333596897730,9576097238713089,
  9215781400927423,11005869190727226,2985994365826164,4710574375700369,3088028931961071,
  6853688363673912,11379495492966314,13084759134346962,5904788279988694,2331025418500506,
  2819277465860974,4409498350467268,12882827563687322,25202288037852504,35796539249942790,
  45093758363212460,44491891477120512,52843377164504034,113083530709245890,171202006579626380,
  169058921023074948,275095016448168756,287296000835417210,287296000633719192,287296000658060942,
  287296000484267684,287296000603252498,245866311379010830,153502049420225492,83964244737554974,
  38704552586558034,15190448006782540,5246835406290726,1631475732680820,461325553387846,
  118859072375096,27941680092352,5987120020738,1144896004206,172592000728,8576000072,
  287296000000000000]
private def _k1_8 : List ℤ := _uPk [1539291768700533,1932138497448873,1071577632654680,
  854031852610376,1220264570991275,1709926835221731,2418665700822914,3109386924036248,
  1925120653306587,3244038164060713,102029750014640,4523813736998142,1536966612098567,
  3785573973683329,2062715604490812,2015074316237661,2375610970546547,8007295426649272,
  2624167037400610,7187749817847380,3220894227613957,5507119141837947,3114057097007582,
  5762470078025536,5235750387434773,4452279723106043,8054395896793494,2277467766891362,
  14782718680118765,1983402097455687,11632872332088964,2016149542766180,13351699454354379,
  625290654136697,9038439371942272,1858819070694042,3750046286346293,1542653569613047,
  878160962865609,7115847031546672,12380109945869300,10296707966591936,6609888772715722,
  3566807727064380,708709931106842,5179479501063208,14935439568673790,22682621717462250,
  32869468970473072,44633359018045722,42444403637976938,51523738727757912,111953664142058986,
  165301755017651882,166812602901978636,287296000540415676,287296000528439158,287296000814520194,
  287296000602471806,287296000647288362,287296000497084266,287296000618613204,253902771650322176,
  162507782075099196,90487996159547434,42257487555106264,16883395435017244,5968283904192972,
  1906738533440406,554969041659618,147394640462300,35787648117506,7939232027300,1588704005758,
  261568001060,20368000136,287296000000000002]
private def _k1_9 : List ℤ := _uPk [1450448697189668,1086164339314639,1073877072641431,
  722403652688050,1911829993186727,471112916447931,3432735889614574,1492362830495524,
  3119640602680421,1697143238564623,1681128629135658,3706152172941582,4402677745334285,
  1973155368284291,2918303458309466,2799115818195361,216731075432837,7892008259660441,
  5242806826386076,6267623278819580,5286278032586361,4037848809104713,4576283318480402,
  4382709601221176,6899199583777689,2387427629066547,6854964035007758,674003398481590,
  7186282252005750,2147156515921375,7118723206867995,6570256923260176,4659163397648044,
  14151642992294821,6464808047395475,9378389862451628,2817292133064118,11330673923212057,
  6487692033692475,4821937472143437,3703569196260458,632078538496014,2511113372822733,
  3581592209250183,1484293347981955,9648150094131696,11336253161549542,10227455689663410,
  6661373720960550,1087140945073742,1589513368627654,9339370146301150,14474610356482926,
  19772602675943858,33155320987114274,44917093835499250,40205378336927214,51761740950500574,
  116139659064983484,160359931495423376,170865735199828292,287296000578682782,287296000566517964,
  287296000778312752,287296000553168508,287296000647071948,287296000512849442,287296000624193380,
  253060776759188586,163820865230266844,90848723090824292,42140384420036230,16868054043249562,
  6016832640363932,1946684469559860,574509457719796,154840752486122,38199648125500,8637104029666,
  1765584006396,301232001210,26800000160,287296000000000004]
private def _k1_10 : List ℤ := _uPk [763982778589686,189578379868873,668532433694053,
  2036037811060250,1937586937031112,924578028192995,3355126306107229,577335254984546,
  3412812232720172,316154783264425,2821424674916180,1971164127661906,6236732524382745,
  276214209050723,3164296368354301,3032721768278642,2769043010207077,6410183737336331,
  7012590917689938,4401067602762010,6609252524352891,2042747467185789,5487688067173202,
  2517072627394550,7860878987329481,166305805801371,7028980720798179,1477965342272148,
  6380488799355096,3654225570568205,6069313465764311,7494013256260644,3496039110596864,
  10151924152862043,3022208680806039,8152009000686689,8351468538057600,2333699525927894,
  8128792152348525,3245489123027389,9108353062492116,6131535574968670,8591884360742619,
  8489064571844983,324748471428467,3647104804846756,2239321173201598,1709320618587134,
  5911474862927101,1917376530614913,5267812289931312,8110087376744080,10551910424776116,
  11250703278534088,4979690871570556,548546699939162,4621881917902146,10954496810427280,
  13640621157310870,20748796964146966,35660126176116502,43376305020621520,37666878043862138,
  58128753098128516,127276107502810456,153277513720553808,183506868551590050,287296000644547152,
  287296000605743178,287296000710513796,287296000513985528,287296000659738088,287296000528115876,
  287296000617240086,244284069406786196,157082826374041080,84775166650489660,38448327437039576,
  15223681079502346,5413125118841288,1750836501037266,516591441559962,139371792440796,
  34461584114002,7811664027040,1610144005844,272288001108,20368000144,287296000000000002]
private def _k1_11 : List ℤ := _uPk [237262546922682,1390307354892257,9411090103609,
  2608973568319154,1288572410889860,2012390026541803,2210530469158887,2471908725354960,
  2719930395912696,2242573085967811,3225280304064471,251727048485792,6609366153595772,
  2464414911812899,2749310162944055,2669950538697860,4809809407095711,3818406125395597,
  7646974784072560,1869937317079356,7004019736491904,218375523810175,5738568224515941,
  372395124304710,8022965385457396,2070273749253505,6608836052536641,3516877180970972,
  5135489442198140,4936341856564461,4688095068126807,8279416197011706,1826398039620500,
  10055107546748256,4556227815555633,7295169051023993,9052040903662688,1356678726370150,
  7497767929737916,2793755825487761,4847149843892819,3025872229963398,4242591692362738,
  4266583054302721,3865484073356769,10053093798036904,6381329797711210,4680164943922022,
  6470150884453975,2480193682807387,861681105518553,3560348918850200,1356214006953626,
  5059332412492317,4579863267277045,1327729892131585,5208644324940256,9327801121281788,
  12822618685892180,8976946253836276,2433893473770094,3473945725836512,8004176996627836,
  10517282685678078,14149605688045326,24487317640135112,37717139815903732,39438474894296456,
  37907029620722056,71846535720786832,139735494005074142,148776996144694798,216421774204633476,
  287296000710054064,287296000588413456,287296000648224426,287296000512776200,287296000678480068,
  287296000533471266,287296000592111682,228607736344594782,141916631313826018,73022427558336984,
  31994297823347428,12403741120760832,4348903548084050,1388548740052480,404677857238538,
  107862496346110,26399072088514,5936736020780,1199568004442,191888000814,9648000088,
  287296000000000000]
private def _k1_12 : List ℤ := _uPk [1140752722051472,2040917016771231,653286985714635,
  2232788402538049,190799387742194,2430088392044201,362948118569937,3616686802101084,
  1241191085974742,3552679291031117,2787283619028289,2412311959209302,5433268527200362,
  4106881852844939,1760038548918833,1782142652586550,5962031450673521,565456431135351,
  7043249045556577,943555117421682,6415133693267618,2451058866896565,5298718052142999,
  1813563515850750,7368975710096018,4114445891473881,5630052887891627,5286769546677594,
  3536980932339190,5914578302033479,3050586125826347,8666015841521374,79936375987138,
  9592781822258668,5948806197822355,6247648173073163,9556681685101918,326260534578650,
  7336042795372026,3303051232899981,4643693892677083,3253193045531172,4097427884821552,
  4352734333921953,3837638873299905,6782850594764266,66221206176658,6476204463515796,
  5409459409822111,1567887916616569,6758887104487416,4775987273736818,1944532430793044,
  4997146763994681,3793077442094565,804606222986043,4064622005098904,2638986361431924,
  3312276857343175,4706212400835255,1659608767740729,1192313778824129,6859223096638296,
  13432125720682280,11042471566730530,5101756296325106,4332866432401400,5964009842400520,
  8470865771737288,11621960463753082,16547921611436464,29046664435366772,39305077343909322,
  35526022215756778,42271446067031454,95216174350334002,144743958442722242,155058008154940964,
  274122617028995700,287296000699182290,287296000519001652,287296000652377554,287296000548347328,
  287296000677018838,287296000518310694,287296000548109138,204550137431749558,118828652110612472,
  57472637656352338,24144213325570076,9090671512499366,3107953128809244,968361186880670,
  275394656860008,71785408234580,17193808058740,3776656013488,736464002800,97552000476,3216000030,
  287296000000000000]
private def _k1_13 : List ℤ := _uPk [1498762128958834,2030475736861862,965703161086007,
  1532717731951869,574500883603042,2273572105601388,892177902391557,3784579152298891,
  133555662402948,3882328936810327,2173290260446569,3418747365616682,4169172561700292,
  4642011386679079,1051980405579009,1155565085238652,6131344200143915,1135944279023333,
  6327799464010829,2233567756879274,5849417855204030,3324246818058927,4932719029495337,
  2607819035323298,6949700431619560,4708659778649007,5244479144767691,5687160473935660,
  3143886036704206,6052973501535155,2821840621994401,8678421025251290,56992359987478,
  9630301822054794,5758367542100277,6519876140601979,9396131462051538,855475846503804,
  7459528618238542,2828971025451367,4892002323692351,2858533030244160,4416445435713966,
  3815828495094725,4617161895971689,6401439429014430,1551658373878492,7177401804812782,
  4092341251833651,3145351995544055,6147192115246798,1396722744911390,4456618636812200,
  2724066171310215,563234167022813,2364279920256260,1907183412328858,924728107956594,
  3731278776697217,4621686274500543,761996367939467,3994454245789434,2393421176579532,
  2847305432739554,3136540686038615,3070518353151295,1726426527178147,6803610946763074,
  12152878099711642,11732181358476414,7586905288391606,4973963170705328,7316486852096680,
  8112665544095378,9687252382326452,15054734949028310,23630818584681800,35691799491964558,
  35959336404875002,35641084252615224,67879512880190082,132392116036090252,139821537065533274,
  214044282939428308,287296000666340408,287296000542123950,287296000625688990,287296000528743702,
  287296000698786204,287296000560841622,287296000619543892,246919804393253450,154542788847238944,
  79653747751773402,35220272791972610,13861874452755246,4941870701782170,1602679668700002,
  473922625458768,128184400413766,31870560107444,7284240025666,1501872005594,252992001052,
  17152000128,287296000000000002]
private def _k1_14 : List ℤ := _uPk [1575480880313755,1661194250342646,1117750280277033,
  594005924750379,1256131010939150,1808122571029380,2034510749405095,3508577746663807,
  988569462136626,3823873849491476,1359825573456727,4138252323552668,2586546803459100,
  4855866808327813,278329797891319,464474557598254,5996195018392834,2787562886252893,
  5369710186157901,3449389419909060,5117323328935534,4117560048979581,4468181766737897,
  3359595482611404,6440301041044292,5255694945717433,4819866377578479,6057716569141606,
  2740007893025682,6179311917025799,2590441918149295,8688407776980858,34048343987698,
  9666575085850140,5564200470369065,6781898668111073,9208488582983718,1380748342362162,
  7532786953089982,2328669697915137,5080545682662507,2419346422859878,4649981706534498,
  3189068688100427,5266654534418969,5807523559098148,2977118213043860,7558936249895428,
  2567130741243471,4528926649813611,5508886870036442,72984985283568,5001434762285024,
  2080006428661241,1698265622354939,2158423761620436,660666100578968,2186709018103928,
  1322139944709619,137829189056053,1746593521272489,2155705169616874,776232525098474,
  3289191337949083,5093741475251425,270268358252293,4307547923830388,1219054823346858,
  430848056675302,3080891020349573,4604174080794051,2139170116766037,4349968033399343,
  11944679616732936,11625922570472390,8712260872464128,6686834786900708,7987424853716610,
  8541841814774922,9210602588015290,13797039888701408,21127701795080478,31705432409138090,
  35723559647081956,32536779146232230,51847916874585136,112423407042585386,135352200748154126,
  172001580274190660,287296000589883926,287296000532855324,287296000615716830,287296000505463366,
  287296000694682844,287296000581601164,287296000668784914,281336981916572908,186704534119613384,
  101261259588637650,46628834498767544,19007733889746110,6996557027309920,2338958214794162,
  711909842172204,197931936633794,50525504169124,11865968041508,2543856009324,469536001872,
  52528000286,287296000000000010]
private def _k1_15 : List ℤ := _uPk [1356507729527461,998336987409422,1084180600577946,
  437194300809253,1754823265847216,1096993148045748,2919619339735265,2821041972716293,
  2003460805204682,3383163931644170,421547925966045,4510435713190468,806298916342410,
  4733656666046138,512677037836307,252548197645296,5563301052810770,4317011012857793,
  4205716507915463,4550630362543266,4239673714412878,4811925535684465,3914386567845853,
  4056651689726672,5847382130351740,5750067040688491,4359373770317965,6396495368299584,
  2326743317302510,6293346988506443,2356606558290875,8695970736710144,11103255987816,
  9701595181644732,5366430406628553,7033318043601217,8994299767895766,1899662806154382,
  7555323608065915,1806783650286993,5207010593600133,1942469367368718,4793520361305962,
  2487213136915385,5767833828685493,5020826712946226,4287498851705022,7603818745106343,
  911388149979871,5651694423518027,4513839320435180,1256027568983982,5144157624425851,
  1251102797598033,2667249637065715,1762377650833858,204770764726550,2443357608538866,
  1092303145560473,1153681044582261,1874142224108444,1505167330876662,1939540123785940,
  1232273113790419,272162044497855,3010587649180325,1018186676575022,1005804540317156,
  5113773930350331,3248258098044195,1062620005852501,2773891123863064,1887897059604640,
  55451346136624,2362656379770703,6103997491088745,3059776919575371,3376198613371635,
  11080392477481290,10540078758867602,9020314007339442,7459886147429496,8800355686684466,
  7922265479867788,9182919258044670,12292336736014830,20429213391287738,27832283540502088,
  34053217478506096,31959538234612756,42606438557837770,97743358610315770,130605927160041990,
  149827265601085250,267776110101481820,287296000605608792,287296000490023234,287296000680175852,
  287296000588909392,287296000698853082,287296000546624356,287296000573092302,212618659092644672,
  119539598234479970,56644920730181270,23668092029507890,8911283032442556,3043513064783518,
  944590658869702,267451136853260,69462384231820,16602064057888,3633008013268,696800002738,
  90048000448,2144000026,287296000000000000]
private def _k1_16 : List ℤ := _uPk [882947442454485,159046747873668,870569593336942,
  1400319836119331,1997941072486248,236805340512380,3435600809593191,1802626966215587,
  2801042739708182,2604257309432572,555418749927761,4504062673271635,1035553084282728,
  4283839036278486,1271714141417387,955471461377140,4854152686989820,5657257570899195,
  2880447933216121,5500717160827262,3241434819594048,5390669390204709,3282397544797097,
  4687635176683494,5178632083524938,6186829855572495,3866428506980637,6701709847414024,
  1905505205533730,6394845019978101,2120551086419011,8701110976439236,11842399987814,
  9735365325438596,5165183846878565,7273730123073215,8754182488785048,2409830821881428,
  7526990649221369,1268148674563481,5269859808518205,1435331895762770,4844277416052158,
  1726783505520399,6106591186820071,4067447802497328,5432147217913746,7310041436058849,
  790695422005417,6448993348789495,3226485242287668,2494158624034320,4873306107102495,
  311016686037339,3375439635281183,1177542691743722,1046266108321566,2389379193094705,
  711955402196287,1997744899426133,1700968129471978,749025699769346,2612400217916380,
  694313498610189,834640980250151,2963532209540032,283270108900278,2042998842592772,
  2877695563801057,1912940053325947,3105305280105004,1393396325794200,2514356173097142,
  3476408634935203,2152403949133775,835850195374069,1318552498693962,2213419506841112,
  182733659816736,3049707610728859,7490209268906523,3956233705557487,2949679830210163,
  9790308010205166,9887218964714336,8857128803712324,8550263444826010,9241713094087022,
  8754318649027058,8433950375476256,13700029247257246,19458246174204030,26778166639125542,
  32334767169255070,31757599156972522,40546486568435184,88194253806529974,126573493011358622,
  138822300108973256,248667895505207700,287296000587549222,287296000478678484,287296000668022732,
  287296000593264914,287296000716832958,287296000572624932,287296000606749872,230771884612616886,
  132289957685629084,63701475450939380,26999311670012614,10295848220208122,3554907450267652,
  1114382595386124,318368993016560,83401600278604,20088208070160,4435936016226,861888003382,
  121136000576,3216000042,287296000000000000]
private theorem _c1_0 : _wkbPair solWkbSched_r256 solTrigIvs_r256 0 32 32 32 _cInit 1 0 0 _k1_0 17
  420 32000000000 _k1_1 26 995 64000000000 = true := by decide +kernel
private theorem _c1_1 : _wkbPair solWkbSched_r256 solTrigIvs_r256 64 32 96 32 _k1_1 26 995
  64000000000 _k1_2 33 1653 96000000000 _k1_3 41 2381 128000000000 = true := by decide +kernel
private theorem _c1_2 : _wkbPair solWkbSched_r256 solTrigIvs_r256 128 32 160 32 _k1_3 41 2381
  128000000000 _k1_4 48 3168 160000000000 _k1_5 54 3999 192000000000 = true := by decide +kernel
private theorem _c1_3 : _wkbPair solWkbSched_r256 solTrigIvs_r256 192 32 224 32 _k1_5 54 3999
  192000000000 _k1_6 61 4829 224000000000 _k1_7 67 5669 256000000000 = true := by decide +kernel
private theorem _c1_4 : _wkbPair solWkbSched_r256 solTrigIvs_r256 256 32 288 32 _k1_7 67 5669
  256000000000 _k1_8 73 6512 288000000000 _k1_9 79 7365 320000000000 = true := by decide +kernel
private theorem _c1_5 : _wkbPair solWkbSched_r256 solTrigIvs_r256 320 32 352 32 _k1_9 79 7365
  320000000000 _k1_10 85 8217 352000000000 _k1_11 91 9073 384000000000 = true := by decide +kernel
private theorem _c1_6 : _wkbPair solWkbSched_r256 solTrigIvs_r256 384 32 416 31 _k1_11 91 9073
  384000000000 _k1_12 97 9938 416000000000 _k1_13 102 10777 447000000000 = true
  := by decide +kernel
private theorem _c1_7 : _wkbPair solWkbSched_r256 solTrigIvs_r256 447 31 478 31 _k1_13 102 10777
  447000000000 _k1_14 107 11621 478000000000 _k1_15 113 12468 509000000000 = true
  := by decide +kernel
private theorem _c1_8 : _wkbPair solWkbSched_r256 solTrigIvs_r256 509 31 540 31 _k1_15 113 12468
  509000000000 _k1_16 118 13321 540000000000 solCkpt_r256_s4 123 14173 571000000000 = true
  := by decide +kernel
theorem cert_solWkbTerm_r128 :
    checkPulseWkbTerminalTable 128 solWkbSched_r128 solRatios_r128 solTrigIvs_r128
      solCkptEnd_r128 8679 323137279596
      2353 solTailLbs_r128 323137279596 solM1VTable16 = true := by decide +kernel
theorem runPrefix_solWkb_r128 :
    SolWkbRunPrefix solWkbSched_r128 solTrigIvs_r128 392
      solCkptEnd_r128 64 8679 323137279596 := by
  have hp := solWkbRunPrefix_zero solWkbSched_r128 solTrigIvs_r128
  have hp := _ws2 0 49 49 49 98 rfl rfl hp _c0_0
  have hp := _ws2 98 49 147 49 196 rfl rfl hp _c0_1
  have hp := _ws2 196 49 245 49 294 rfl rfl hp _c0_2
  exact _ws2 294 49 343 49 392 rfl rfl hp _c0_3
theorem runPrefixSub2_solWkb_r256 :
    SolWkbRunPrefix solWkbSched_r256 solTrigIvs_r256 571
      solCkpt_r256_s4 123 14173 571000000000 := by
  have hp := solWkbRunPrefix_zero solWkbSched_r256 solTrigIvs_r256
  have hp := _ws2 0 32 32 32 64 rfl rfl hp _c1_0
  have hp := _ws2 64 32 96 32 128 rfl rfl hp _c1_1
  have hp := _ws2 128 32 160 32 192 rfl rfl hp _c1_2
  have hp := _ws2 192 32 224 32 256 rfl rfl hp _c1_3
  have hp := _ws2 256 32 288 32 320 rfl rfl hp _c1_4
  have hp := _ws2 320 32 352 32 384 rfl rfl hp _c1_5
  have hp := _ws2 384 32 416 31 447 rfl rfl hp _c1_6
  have hp := _ws2 447 31 478 31 509 rfl rfl hp _c1_7
  exact _ws2 509 31 540 31 571 rfl rfl hp _c1_8
/-- Chunk 0 of `solRatios_r256`. -/
def solRatios_r256_c0 : List (IvInt) := [(998044962,998044965),(996086089,996086092),(994123356,
  994123359),(992156740,992156743),(990186218,990186221),(988211767,988211770),(986233363,
  986233366),(984250983,984250986),(982264601,982264604),(980274195,980274198),(978279739,
  978279742),(976281208,976281211)]
/-- Chunk 1 of `solRatios_r256`. -/
def solRatios_r256_c1 : List (IvInt) := [(974278578,974278581),(972271823,972271826),(970260917,
  970260920),(968245835,968245838),(966226551,966226554),(964203037,964203040),(962175268,
  962175271),(960143217,960143220),(958106856,958106859),(956066157,956066160),(954021094,
  954021097),(951971637,951971640)]
/-- Chunk 2 of `solRatios_r256`. -/
def solRatios_r256_c2 : List (IvInt) := [(949917758,949917761),(947859429,947859432),(945796620,
  945796623),(943729303,943729306),(941657447,941657450),(939581022,939581025),(937499999,
  937500002),(935414345,935414348),(933324031,933324034),(931229025,931229028),(929129295,
  929129298),(927024809,927024812)]
/-- Chunk 3 of `solRatios_r256`. -/
def solRatios_r256_c3 : List (IvInt) := [(924915535,924915538),(922801440,922801443),(920682490,
  920682493),(918558652,918558655),(916429892,916429895),(914296176,914296179),(912157468,
  912157471),(910013735,910013738),(907864939,907864942),(905711045,905711048),(903552017,
  903552020),(901387817,901387820)]
/-- Chunk 4 of `solRatios_r256`. -/
def solRatios_r256_c4 : List (IvInt) := [(899218409,899218412),(897043754,897043757),(894863815,
  894863818),(892678552,892678555),(890487927,890487930),(888291899,888291902),(886090428,
  886090431),(883883475,883883478),(881670997,881671000),(879452953,879452956),(877229301,
  877229304),(874999999,875000002)]
/-- Chunk 5 of `solRatios_r256`. -/
def solRatios_r256_c5 : List (IvInt) := [(872765001,872765004),(870524266,870524269),(868277748,
  868277751),(866025402,866025405),(863767184,863767187),(861503046,861503049),(859232941,
  859232944),(856956824,856956827),(854674644,854674647),(852386355,852386358),(850091905,
  850091908),(847791246,847791249)]
/-- Chunk 6 of `solRatios_r256`. -/
def solRatios_r256_c6 : List (IvInt) := [(845484327,845484330),(843171096,843171099),(840851501,
  840851504),(838525490,838525493),(836193009,836193012),(833854003,833854006),(831508417,
  831508420),(829156196,829156199),(826797283,826797286),(824431621,824431624),(822059151,
  822059154),(819679814,819679817)]
/-- Chunk 7 of `solRatios_r256`. -/
def solRatios_r256_c7 : List (IvInt) := [(817293550,817293553),(814900299,814900302),(812499999,
  812500002),(810092586,810092589),(807677997,807678000),(805256169,805256172),(802827035,
  802827038),(800390528,800390531),(797946582,797946585),(795495127,795495130),(793036095,
  793036098),(790569414,790569417)]
/-- Chunk 8 of `solRatios_r256`. -/
def solRatios_r256_c8 : List (IvInt) := [(788095012,788095015),(785612817,785612820),(783122754,
  783122757),(780624748,780624751),(778118723,778118726),(775604601,775604604),(773082303,
  773082306),(770551749,770551752),(768012856,768012859),(765465543,765465546),(762909724,
  762909727),(760345315,760345318)]
/-- Chunk 9 of `solRatios_r256`. -/
def solRatios_r256_c9 : List (IvInt) := [(757772227,757772230),(755190372,755190375),(752599660,
  752599663),(749999999,750000002),(747391295,747391298),(744773454,744773457),(742146379,
  742146382),(739509971,739509974),(736864131,736864134),(734208756,734208759),(731543743,
  731543746),(728868985,728868988)]
/-- Chunk 10 of `solRatios_r256`. -/
def solRatios_r256_c10 : List (IvInt) := [(726184376,726184379),(723489805,723489808),(720785161,
  720785164),(718070329,718070332),(715345195,715345198),(712609639,712609642),(709863542,
  709863545)]
/-- Stratum angle-ratio intervals for WKB `r = 256`. -/
def solRatios_r256 : List (IvInt) := List.append (List.append (List.append (solRatios_r256_c0)
  (solRatios_r256_c1)) (List.append (solRatios_r256_c2) (List.append (solRatios_r256_c3)
  (solRatios_r256_c4)))) (List.append (List.append (solRatios_r256_c5) (List.append
  (solRatios_r256_c6) (solRatios_r256_c7))) (List.append (solRatios_r256_c8) (List.append
  (solRatios_r256_c9) (solRatios_r256_c10))))
/-- Chunk 0 of `solTailLbs_r256`. -/
def solTailLbs_r256_c0 : List (ℤ) := [999991877,999990028,999985580,999984033,999976083,999974817,
  999963816,999950523,999946112,999923756,999920161,999905632,999873187,999845000,999832458,
  999822618,999804875,999758278,999690663,999650486]
/-- Chunk 1 of `solTailLbs_r256`. -/
def solTailLbs_r256_c1 : List (ℤ) := [999612667,999567040,999550853,999490220,999488295,999386116,
  999385078,999289211,999288146,999200733,999200339,999079085,999078858,998927237,998917064,
  998777885,998741668,998651887,998605319,998572419]
/-- Chunk 2 of `solTailLbs_r256`. -/
def solTailLbs_r256_c2 : List (ℤ) := [998541366,998520837,998506906,998474494,998458228,998407501,
  998364362,998330571,998243624,998238231,998161055,998156318,998122745,998110874,998104859,
  998090801,998089739,998078882,998078097,998074275]
/-- Chunk 3 of `solTailLbs_r256`. -/
def solTailLbs_r256_c3 : List (ℤ) := [998068358,998067570,998056930,998056833,998051837,998046321,
  998037997,998030323,998029984,998009018,998007939,997994266,997982500,997976825,997964671,
  997963181,997958053,997953256,997951700,997950980]
/-- Chunk 4 of `solTailLbs_r256`. -/
def solTailLbs_r256_c4 : List (ℤ) := [997950363,997949294,997948052,997947148,997946423,997945927,
  997944935,997939015,997937985,997935352,997932690,997932419,997931197,997927569,997927186,
  997922532,997922112,997921011,997920370,997915015]
/-- Chunk 5 of `solTailLbs_r256`. -/
def solTailLbs_r256_c5 : List (ℤ) := [997912881,997912833,997911526,997911509,997909401,997904002,
  997897805,997891562,997884147,997873488,997865889,997861812,997847549,997812410,997759900,
  997659374,997653204,997411532,996621370,995669202]
/-- Chunk 6 of `solTailLbs_r256`. -/
def solTailLbs_r256_c6 : List (ℤ) := [994384184,993532662,992855131,992249654,992063300,992057531,
  991634595,991276693]
/-- Certified suffix probability lower bounds for WKB `r = 256`. -/
def solTailLbs_r256 : List (ℤ) := List.append (List.append (solTailLbs_r256_c0) (List.append
  (solTailLbs_r256_c1) (solTailLbs_r256_c2))) (List.append (List.append (solTailLbs_r256_c3)
  (solTailLbs_r256_c4)) (List.append (solTailLbs_r256_c5) (solTailLbs_r256_c6)))
/-- Stage specification for WKB Multi-pulse conveyor at `r = 256`. -/
def solStage_r256 : PulseM1StageSpec := ⟨128, 216770, 1000000, solWkbToSwLPulses solWkbSched_r256⟩
/-- WKB `L2Ball` center checkpoint after pulse `780` at `r = 256`. -/
def solCkptEnd_r256 : List ℤ := List.append (List.append (List.append ( [(-579062),(-1359854),
  (-20120),1942398,822100,656144,1056446,(-2198294),(-1766070),643149,923629,2070284,2591793,
  (-2046530),(-3017700),(-1838341),(-1016487),3038374,3623335,388989,(-1855803),(-2368332),
  (-2987051),3022405,4828715,3915735,3586018,(-2772334),(-2204404),(-1971034),2440621,1437421] ) (
  [3959806,(-4127743),(-5437642),(-5289602),(-6296730),3352256,5380214,4106511,4578612,(-4667405),
  (-4883734),(-3325746),(-2265013),4857198,6087088,958820,1002888,(-7452308),(-6831000),(-990387),
  (-238278),6564712,7265756,(-181983),1016225,(-6922230),(-6285935),169682,604591,7451468,8108902,
  418071] )) (List.append ( [(-228282),(-7990661),(-9370227),(-1437703),(-2847436),8393494,8292003,
  2816999,5318763,(-7595530),(-5666326),(-4595609),(-5045634),4920889,2948210,4539185,3233380,
  (-3711964),(-2599001),(-3178530),(-1957280),4073119,3978557,3070054,2615995,(-5253034),(-4810836),
  (-4336001),(-4934254),5089337,2810096,6536172] ) ( [6651599,(-2310420),237015,(-6470644),
  (-5943351),(-440866),(-2131561),4124001,4070998,2549403,2318248,(-1955073),(-1481239),(-3226770),
  (-1910329),1030107,(-15444),2370925,2288692,171636,869325,(-944071),(-1712184),(-1864389),
  (-1562836),785438,(-413809),1966967,2602616,288450,115767,(-1452373)] ))) (List.append
  (List.append ( [(-1699544),(-1494562),(-1811971),2225342,1836705,1643013,2230766,(-579909),
  (-50501),(-3288696),(-3186772),346785,(-979318),2726697,2498135,1960127,2815343,(-2000814),
  (-1293385),(-2771381),(-2115702),(-39428),(-1220212),1638056,1564078,1762045,1301180,(-1166497),
  (-442169),(-632163),(-565891),(-297802)] ) ( [(-727007),705122,756758,884743,677457,(-692511),
  (-651544),(-439090),(-729756),331820,(-621665),904898,416253,1568856,1859916,295212,971292,
  (-1486855),(-650101),(-1349469),(-917236),(-370955),(-366193),413628,1025086,958370,1646468,
  (-569568),240888,(-1857617),(-1097323),(-401999)] )) (List.append ( [(-508429),1049269,16046,
  174462,(-781655),(-883674),(-2139036),(-1429897),(-299091),(-221145),(-4206),1138167,(-108544),
  (-98835),84958,140358,(-1445076),(-526954),(-2263367),1180504,(-2191920),2027683,(-1460293),
  1384212,(-2345336),2739532,(-1776648),2595932,928229,1433862,(-1421985),2129351] ) ( [(-3119740),
  4869729,3381138,7233223,449657,(-5750759),(-8214438),(-715976),2378825,6805014,(-13979167),
  (-1506644),(-28072691),(-3819527),(-30623771),(-4735657),(-35537920),(-6529622),(-28445555),
  (-7363463),(-24970851),3293577,(-24389780),3501203,(-13197473),(-1279160),(-2033596),7722833,
  (-19065277),18519843,(-3885817),36011551] )))
private def _uZh (u : ℕ) : ℤ :=
  cond (Nat.ble (Nat.mod u 2) 0) (solLitNat (Nat.div u 2) Int.ofNat)
    (solLitNat (Nat.div u 2) Int.negSucc)
private def _uPl : List ℕ → List ℤ
  | [] => []
  | w :: ws =>
      cond (Nat.ble 287316000000000000 w) (_uZh (Nat.sub w 287316000000000000) :: _uPl ws)
        (cond (Nat.ble 141392000000000000 w)
          (let d := Nat.sub w 141392000000000000
           _uZh (Nat.mod d 382000000) :: _uZh (Nat.div d 382000000) :: _uPl ws)
          (cond (Nat.ble 784000000000000 w)
            (let d := Nat.sub w 784000000000000; let q := Nat.div d 520000
             _uZh (Nat.mod d 520000) :: _uZh (Nat.mod q 520000) ::
               _uZh (Nat.div q 520000) :: _uPl ws)
            (_uZh (Nat.mod w 28000000) :: _uZh (Nat.div w 28000000) :: _uPl ws)))
private def _wkbQuad (q : SolWkbSched) (trg : List (IvInt × IvInt))
    (t0 d0 t1 d1 t2 d2 t3 d3 : ℕ) (c0 : List ℤ) (h0 r0 : ℕ) (s0 : ℤ)
    (c1 : List ℤ) (h1 r1 : ℕ) (s1 : ℤ) (c2 : List ℤ) (h2 r2 : ℕ) (s2 : ℤ)
    (c3 : List ℤ) (h3 r3 : ℕ) (s3 : ℤ) (c4 : List ℤ) (h4 r4 : ℕ) (s4 : ℤ) : Bool :=
  match _wkbPair q trg t0 d0 t1 d1 c0 h0 r0 s0 c1 h1 r1 s1 c2 h2 r2 s2 with
  | true => _wkbPair q trg t2 d2 t3 d3 c2 h2 r2 s2 c3 h3 r3 s3 c4 h4 r4 s4
  | false => false
private theorem _ws4 {q : SolWkbSched} {trg : List (IvInt × IvInt)}
    (t0 d0 t1 d1 t2 d2 t3 d3 t4 : ℕ) {c0 c1 c2 c3 c4 : List ℤ}
    {h0 r0 h1 r1 h2 r2 h3 r3 h4 r4 : ℕ} {s0 s1 s2 s3 s4 : ℤ}
    (ha : t0 + d0 = t1) (hb : t1 + d1 = t2) (hc : t2 + d2 = t3) (hd : t3 + d3 = t4)
    (hp : SolWkbRunPrefix q trg t0 c0 h0 r0 s0)
    (hk : _wkbQuad q trg t0 d0 t1 d1 t2 d2 t3 d3 c0 h0 r0 s0
      c1 h1 r1 s1 c2 h2 r2 s2 c3 h3 r3 s3 c4 h4 r4 s4 = true) :
    SolWkbRunPrefix q trg t4 c4 h4 r4 s4 := by
  unfold _wkbQuad at hk; revert hk
  cases h12 : _wkbPair q trg t0 d0 t1 d1 c0 h0 r0 s0 c1 h1 r1 s1 c2 h2 r2 s2
  · intro hk; cases hk
  · intro hk; exact _ws2 t2 d2 t3 d3 t4 hc hd (_ws2 t0 d0 t1 d1 t2 ha hb hp h12) hk
private def _k256_578 : List ℤ := List.append (List.append (_uPl [80987956609879, 104215497113619,
  50790153065418, 84893399821232, 19770159692171, 124296760922255, 7867110598756, 192843253584195,
  63805621988913, 179819307446160, 155593734309264, 82614987970165, 327758036192371,
  156211895145358, 139623599179870, 142240618506909, 225053928140618, 272497999639532,
  381891976186077, 225941138868583, 333446237401338, 162852126286802, 249928873934371,
  242023888784893, 319334297803148, 221395031316088, 297798291713093, 229292124009905,
  369746836628362, 143314063487784, 388447001576445, 71814472035529 ]) (_uPl [442808298347272,
  66179866811870, 458785018764638, 228163251503883, 339000494047835, 348639991607208,
  131392561291878, 302730596538257, 64166545575067, 229842368222251, 78863716587900,
  281392356140797, 37810315658793, 351384435207981, 147601397160702, 256807078879034,
  339431211167409, 24652836919987, 333045944769579, 138768063851208, 198422986486202,
  154857838489637, 11239319089645, 121504600105680, 72022163983692, 95037575090262, 71712452168697,
  16311601028971, 86419257646687, 107204105225444, 44541200989664, 79230620695741 ])) (List.append
  (_uPl [60684375973837, 136137515049871, 89515387751178, 22970504536242, 181844573046238,
  29771538322371, 121973939820853, 161644450646340, 8013074901846, 166325685458622, 84787670956565,
  5747060079979, 127635089194081, 33868971279036, 36190364841032, 38670604218792, 56744662247591,
  34914881549059, 50857744789980, 152170931637842, 34975813538858, 202394727295605,
  401473731070685, 243116321040247, 154236049480185, 428869508350780, 529685926175062,
  458906295233620, 553715305128246, 550821957915134, 481114668695540, 518851557010990 ]) (_uPl
  [717982579564312, 155781171457935376, 159401934026865296, 161960985656315474, 163616475871652348,
  168380319184938764, 195231399487788354, 227011052257451890, 230836773884957676,
  287316000399703510, 287316000410496184, 287316000561811272, 287316000462378352,
  287316000642408886, 287316000591133966, 287316000733189800, 287316000603266782,
  287316000647456654, 287316000494361958, 287316000475301618, 248296070946530456,
  193955508070382112, 164068325338275010, 150175106765705306, 225289916448730, 71439484157030,
  20614273261710, 24744245120589310, 3630241145327226, 994913090964370, 787785638480318,
  287316000000000000 ]))
private def _k256_585 : List ℤ := List.append (List.append (_uPl [21375398855748, 25259895778813,
  32791585747545, 101499443264022, 104450668463620, 17280288491757, 184856168189796,
  58549266750668, 162261262734471, 110608574124921, 51483157729864, 229458966252056,
  87656000033189, 213634908895635, 75319725267004, 55860369301993, 249585959170613,
  295657834894722, 157590257109870, 277470853221635, 188150099217851, 267056054976954,
  194903276150928, 214377669657561, 312522066079281, 285632601301088, 253422941523214,
  302178893737973, 179500788437945, 298150334691936, 210660448921128, 433463272905131 ]) (_uPl
  [131760623279617, 530641160560988, 114980281244466, 465061777558870, 332659306239879,
  268095587010449, 344473086880426, 67182958555938, 252616647941673, 35074824115557,
  222039500335952, 56104645848956, 313435671527379, 20682352931905, 390224130600857,
  247597571148028, 265010406428234, 349035767508705, 48230123794249, 244194891184845,
  134807240313236, 101767096855556, 191113917958777, 30140324205147, 125007625598077,
  62249884015920, 21382286450478, 140657860628019, 23951119392007, 59431515414025, 124357578775202,
  38712886565050 ])) (List.append (_uPl [123028613087374, 47508753482915, 124726562109327,
  116453345988162, 20354242537892, 178479868686629, 69491609236029, 116001260813233,
  183242530210994, 8060282109884, 103651550051156, 107637797382201, 5570324707991, 97731256179699,
  11557281486684, 3790557271748, 56901348579774, 44051870400409, 23809465035547, 48276368381739,
  166059491826868, 63060093225272, 158810430450201, 401627115289385, 257741898127349,
  98580619925571, 400540561736060, 508872012849324, 455614893771976, 549208872703482,
  552527101230940, 486562068550806 ]) (_uPl [497892660635368, 675153554221406, 155075237748638898,
  158813226185591334, 161591939273456562, 163856230529173874, 167389489110315916,
  190278764891789106, 225054703418977770, 227620171912789836, 284763618472238214,
  287316000556605568, 287316000457813062, 287316000620405408, 287316000578396814,
  287316000735481628, 287316000613404712, 287316000666205130, 287316000514802446,
  287316000501973212, 257063308657115742, 199286420463037890, 166711857027376636,
  151318551189906856, 257656798153566, 82573852785310, 24063817467228, 29187475995849828,
  4198624055496158, 1046830131205290, 790489655120414, 287316000000000000 ]))
private def _k256_592 : List ℤ := List.append (List.append (_uPl [78705872914766, 107061892687796,
  46900309272713, 97536827414647, 6136987752686, 126655284309178, 18468638571715, 184151410586358,
  88867553566564, 162070696428981, 164165009355339, 43029960358676, 343409558043770,
  116773252049133, 153985050175605, 153230869463766, 174430293595035, 334268489363341,
  348005119005118, 287303612829226, 290684051950899, 225187320658271, 203236607887056,
  294701994411778, 240610816342093, 295111104915669, 230825514229820, 311024541376008,
  320080412069837, 227665937594517, 327533705312642, 199860290586548 ]) (_uPl [403061154956525,
  97220498639127, 494913049346249, 79110209285510, 447714941394188, 259332567274983,
  248321314956367, 279500204188266, 153119100187110, 217268718687025, 159874967005929,
  260564643797030, 156169926326784, 359327053758159, 4755702176165, 355068398454833,
  232553899373060, 167666895482332, 312972608139165, 35554997197329, 256274874918599,
  110524404604906, 95738306223596, 107982029992327, 15121656711097, 123779153236053,
  61700073316160, 50475184730776, 97948900013818, 78203582891373, 106043563617163, 59829281981244
  ])) (List.append (_uPl [1786656525980, 160576108229448, 24527920850217, 84421403487109,
  170968282447264, 66789161950896, 160034588953086, 97334081314765, 110830221661257,
  161748890010664, 25235564135048, 68314935276538, 124359285574375, 24261051385919, 43175776053526,
  32768568515796, 170718025574, 66302180337396, 18424758079297, 6961249107791, 62307057571509,
  177970971385672, 95072884570186, 129918069592361, 405572035443413, 286483114564303,
  36146502048821, 372948856587797, 476021067310438, 452198556531452, 539499256109850,
  545049700705270 ]) (List.append (_uPl [481326516721156, 464792404747884, 641512617397726,
  155060429898532774, 158809079954792712, 161087792478324766, 163762830763074876,
  166586499132492900, 185735470801892720, 221803263036667782, 225237637146904632,
  272667810768968998, 287316000543860268, 287316000455627326, 287316000598968074,
  287316000563116430, 287316000734064192, 287316000621721914, 287316000683541022,
  287316000533170680, 287316000527461586, 265892897935823216, 204817647544102552,
  169509417992910492, 152549175654350670, 292761128014610, 94806717471520, 27909169693186,
  34192600241597972, 4845964044386242, 1107940806806340, 793193674880516 ]) (_uPl
  [287316000000000002])))
private def _k256_599 : List ℤ := List.append (List.append (_uPl [29778282758087, 13195395856320,
  38354933596578, 89349543689371, 105251664026198, 6640533956, 182225037126039, 85887374366713,
  148535355594254, 136614833414236, 24152441955507, 236882240810059, 26338100398116,
  235192247409700, 45959289681829, 25712909589984, 284965665224456, 225820544850965,
  232422467603543, 213933843174210, 254216013410796, 214493812997931, 243591886261453,
  141961635233102, 373131282970342, 209470615602043, 314423878819755, 218053876273968,
  268064366205090, 233739725406391, 305368346228339, 374424297214030 ]) (_uPl [253348017181110,
  500704042300531, 40526489667475, 490416808018827, 186344385309942, 354483731254556,
  260182310599479, 163827841107727, 198699654824556, 112961723152306, 163709090892063,
  152833976439379, 254462663426982, 117307272256730, 388367310934017, 106685305709687,
  358798109841541, 280335896213482, 178488670071532, 259222796702559, 24827637565737,
  149915754849489, 148784332710476, 78586623311282, 131890500546305, 5099504586625, 50274001834173,
  116691402874270, 23200159398664, 97592182003132, 71912768564099, 68697105572121 ])) (List.append
  (_uPl [122121385210812, 35091929600942, 137506516417827, 71905151828261, 111710709230201,
  142345787906164, 18159153758034, 169962605866760, 121055793387517, 99903668968203,
  118150480324602, 67927555286796, 78697727782206, 83300925834223, 14415913454489, 23725296957957,
  53914056628820, 10423758298522, 54574604312475, 67005703437, 6424238192097, 74912322695661,
  173125234693068, 119644116199456, 121728068568411, 410066035176945, 315447434695049,
  26113908167339, 339496418440301, 440463753491048, 436643379561968, 517651247750810 ])
  (List.append (_uPl [524696164556066, 486522589126284, 483018611966058, 644281983058304,
  154898345004071864, 158550256616825426, 160559341315638938, 163339098789014102,
  165595498687639222, 181688488686914342, 218335314985697684, 224067345763746444,
  261558968830681460, 287316000525646218, 287316000455613918, 287316000577492838,
  287316000546159742, 287316000730117634, 287316000626886972, 287316000698679616,
  287316000550846222, 287316000551728792, 287316000397998362, 229032505441047640,
  183704220249000794, 159390095105317496, 148271079716635266, 173926491807954, 54413635863972,
  15494697147832, 21747105390551378, 2823906825874478 ]) (_uPl [957056752963684, 785081626000188
  ])))
private def _k256_606 : List ℤ := List.append (List.append (_uPl [75526781209223, 108548944253237,
  42350617462100, 108666798955078, 7600883749263, 126654304309652, 44429538411292, 171401079531525,
  111809493011421, 140149133297768, 168185948363850, 2164324498421, 348112352169988,
  73354856678594, 162748181092246, 158289768363959, 116630762654712, 381448122678446,
  298026717500251, 334614902358059, 232906530089762, 275253530558018, 144880269387089,
  329585707651509, 146619998097904, 349171177921424, 147731960032101, 370002982056181,
  245909170893502, 293795018933288, 239235288270211, 310465915864707 ]) (_uPl [326636306932742,
  251402300699004, 482179296205049, 78069449291547, 508613115737227, 141247805691600,
  336638043358460, 222852091337507, 223086141784019, 176773861250996, 219604200491358,
  203827994929979, 252260351522195, 314278390465020, 156388049030622, 397407501014016,
  87852673728921, 282531992116933, 238685896330918, 74009860900380, 266929405186501,
  45215497846245, 161521756140909, 72723955477946, 44911920462434, 126133756881639, 38158766175029,
  105882227366021, 86780737622256, 30581827868836, 141608517359944, 25400846769135 ])) (List.append
  (_uPl [63796995911155, 142524762651690, 47118320632520, 122364845466984, 111276009242011,
  143800667837591, 150088794200586, 3107950349688, 178754382638326, 105022152831683,
  42646971948549, 107800113365979, 78082483798434, 73807918294932, 34503700928501, 18335213098569,
  33336017638753, 57925953068610, 24876629721860, 37493764849015, 14331269774419, 28189479518803,
  72425251295435, 152901842009638, 137204148380872, 117434940327930, 409671234793835,
  351939498483981, 80310822161781, 290579019935621, 394218279959046, 410795402968696 ])
  (List.append (_uPl [507454039481862, 553597259354578, 523287875911602, 486685098923988,
  625877189513820, 154665325002049170, 158108148151112716, 159653467277984074, 162692919811591060,
  165427259774293734, 178644158779871916, 214478593311085532, 223350460876171268,
  251134414956809430, 287316000503900368, 287316000451310408, 287316000561395476,
  287316000527803964, 287316000722596392, 287316000630674034, 287316000711824986,
  287316000567160752, 287316000574567534, 287316000419423764, 235645199740133396,
  187659070084372170, 161302914273361798, 149076464836264212, 196484917260260, 62031596380508,
  17811417312690, 25151453223718980 ]) (_uPl [3185703608760282, 993290504804366, 786163238480242
  ])))
private def _k256_613 : List ℤ := List.append (List.append (_uPl [37841694628988, 963399884859,
  43378609423141, 75813476057474, 104259484515561, 17293588491689, 175895218039438,
  111332513842444, 131266048368287, 159103676564143, 3847738016086, 237255676656039,
  35819460367759, 248734081807561, 14927869890092, 5429989661589, 308621939063355, 146126134246262,
  296507717560684, 139934072580287, 307150375117621, 150245490528676, 278300320012628,
  60973792130369, 410064371419117, 119356789130238, 353465647640002, 117976641912015,
  336105567190943, 150620131367942, 374544106680358, 282712064718879 ]) (_uPl [351881441883135,
  423289843442662, 192032164346204, 465395369523143, 20127510531277, 401535850693641,
  145913165097250, 240885098570580, 120145796861249, 176331853269915, 83586448530736,
  228501145866760, 159203782267523, 237997377774017, 327307744021638, 51029538112108,
  394228548304746, 164570991539325, 277829222604217, 227941284464458, 89724133056554,
  169613164302648, 77369074541335, 111214433750895, 111447730577500, 53137816179560,
  68142228815700, 66416704472517, 64975346617733, 112515144115263, 1879029236670, 81426996184338
  ])) (List.append (_uPl [89726703196805, 108407044236903, 112956258831550, 7334940602374,
  171170750429152, 64547145982365, 100362812552771, 171685809653466, 20756966867882,
  159536862224704, 93647934593211, 5265264080817, 124612713548603, 39400427199234, 35172284895936,
  34879516289638, 33407445636893, 46451273633893, 37946497384740, 34236636987002, 43508948404075,
  55387725559043, 52153896290001, 56542251288689, 136231033231718, 151201404735440,
  120422709142424, 403161402086917, 400273378149607, 137363903430081, 233077493017981,
  364404270460370 ]) (List.append (_uPl [431540769332466, 525531565530204, 562243601919370,
  534974459444432, 485582906269254, 592073068239544, 154059684628908054, 157655200818235744,
  159477930635780996, 162414073560555028, 165149082024814314, 176051556098475304,
  209872415906019416, 222665917636927622, 242781165170289100, 287316000478202106,
  287316000445056058, 287316000546870934, 287316000509959130, 287316000712909170,
  287316000631980470, 287316000723242734, 287316000581824846, 287316000596210628,
  287316000439649086, 287316000394944392, 222385256888459490, 178721879767755688,
  156706885825310744, 414487102373672, 138167239878478, 41755786508874 ]) (_uPl [11514384725708,
  13410111662512174, 2169534999704142, 873773279442058 ])))
private def _k256_620 : List ℤ := List.append (List.append (_uPl [71486577489902, 108657556184531,
  37205085630915, 118110610449651, 21209079681972, 124293764922723, 69488726120739,
  154873212398862, 132084040336724, 114618874030145, 167545448637736, 38765812385246,
  341716510378325, 27436565012279, 165594520030822, 157221428749935, 54032815276055,
  411977611702029, 234268003556108, 365561199575940, 163098191707429, 310323164100457,
  78209050348382, 344568420670760, 43325786959167, 379974786532775, 54320852994058,
  401912814293306, 152911456883175, 336408131717103, 130934230201862, 393979412107530 ]) (_uPl
  [220487665914099, 381746021175469, 421840785341196, 227229395521364, 515190678318871,
  7489146588901, 386167210912697, 139559513609468, 265392206663766, 113562211140159,
  250100761378917, 119001409107904, 312379007644966, 222882110218467, 284180633898683,
  377156084586504, 71137457851822, 349963463388804, 123053767079577, 170353183013405,
  228424677073090, 28674273978086, 195729717248726, 22827256263485, 95640275289213,
  101599290811396, 6250610556988, 137418037242394, 55502638882401, 24321979925077, 142537753229900,
  15407198861520 ])) (List.append (_uPl [109358118287894, 86759880831165, 105972891157173,
  126235256961626, 19811462540020, 178721732601030, 95120120694137, 92073581433023,
  190401177215228, 14434734094902, 96451742458640, 110860821006123, 4806288709063, 97243048392043,
  13345305467468, 2883917274774, 53886476631820, 29035358084819, 48736632851167, 15322665473020,
  24660077339764, 53047933109878, 93820020876165, 60101752289373, 33963443185537, 120241408561138,
  160064525363428, 130665165839998, 404511840620435, 448445137600807, 170522120388959,
  221509127122913 ]) (List.append (_uPl [360944195409118, 426758311500414, 516516460345854,
  562980112824512, 529833603103590, 456863922465430, 560277779678196, 154062683327176372,
  157631292199816162, 159106595309776806, 161958387286099774, 164591040379566482,
  173980989271366794, 206480367437123938, 223240360825474972, 236433889065546502,
  287316000450225532, 287316000434558032, 287316000536602896, 287316000490759532,
  287316000701969658, 287316000629329910, 287316000733938954, 287316000594639378,
  287316000616377126, 287316000460489184, 287316000416695018, 228077118790976962,
  181706665811037842, 158049443931010282, 453817080827756, 152208120814350 ]) (_uPl
  [46263002826864, 12810112824430, 15287234814859528, 2315551864987092, 287316000000002762 ])))
private def _k256_627 : List ℤ := List.append (List.append (_uPl [45473850469917, 11280783864068,
  47791941229686, 61100792362617, 101491264996142, 34258368365746, 165995510911439,
  134324181189411, 110865277038112, 177495783596528, 31741365909911, 230568074102620,
  96834903943094, 253799084143820, 16646173884215, 36362625514046, 319581500776236, 60053323019711,
  346882879075749, 59090541371104, 344218760456786, 77810975485789, 297036601533509,
  23695824295192, 420978012349061, 21293033783901, 367821104206033, 9268630532304, 378414767626278,
  55444408419577, 412404274573831, 166329927113856 ]) (_uPl [418393897685804, 305738931499781,
  324578813411099, 392567906497766, 148238933773462, 404030622166173, 14831586085943,
  289141723247841, 26694761799226, 217041694710302, 7662825033833, 272678058485633, 41242947643938,
  323589201849898, 216353407886435, 200707484291911, 365539165281616, 21176804927856,
  329044045992920, 155938699428795, 187751878879459, 157121498301632, 9170651093446,
  121455852161927, 67914536074669, 100047642881499, 71069096381636, 1168165062428, 91693701230186,
  100646589800045, 68614452628411, 73705633249748 ])) (List.append (_uPl [34197244358546,
  153036605751744, 57740232476555, 59277852094927, 181756849065488, 32144426307534,
  152460029981796, 120640832665495, 86076710186019, 167732993236072, 38232380005806,
  59175959495978, 127438893220473, 18439291432419, 43200304013155, 33125120485874, 259282025552,
  64509900337228, 7301981919929, 43975904050737, 27603801264412, 12171154152274, 50013798710694,
  108089772360763, 62514567581647, 6699450932041, 104240136128256, 151912494520798,
  132707206661584, 387955271056451, 445373930178083, 176603722587807 ]) (List.append (_uPl
  [182247585317269, 330406217288178, 412593950010308, 489729419285678, 535268568504766,
  525739051331884, 469381993966822, 553859561810996, 153681962261597568, 157397632730243086,
  158457620092383376, 161363441384597136, 165013628641197636, 173252914838345468,
  203102534716300796, 222524152838639128, 229932175714636522, 287316000424010126,
  287316000418606274, 287316000529267192, 287316000473041262, 287316000688298098,
  287316000624922696, 287316000741034334, 287316000609587878, 287316000633505152,
  287316000483116250, 287316000436098620, 232928466859230176, 184076864279335198,
  159019666636935164, 480004307293380 ]) (_uPl [160761841725920, 48704827132302, 13497232912636,
  16972911617043278, 438368027622 ])))
private def _k256_634 : List ℤ := List.append (List.append (_uPl [66631685753593, 107386440619960,
  31536009776784, 125721709906218, 34456019551949, 119617961518598, 93137609705960,
  134932089169255, 149207691558571, 86137358607256, 162260869621635, 78542024022517,
  324426036510830, 19417029038832, 162420581152775, 150067401834798, 10787823433500,
  424524380564026, 159677153077619, 378628992618925, 84865100720356, 328485501419488,
  7049206715757, 338745794350494, 62717522871236, 385470149024563, 42884253048503, 404419793637342,
  48207333886536, 352094428203390, 11685842946095, 443113555642867 ]) (_uPl [94274727629282,
  475892180402628, 319854625555099, 353048148156811, 466745616127312, 127100385867312,
  391201749868669, 39580782732501, 274792168786784, 35756792111754, 247304821917079,
  17775166030641, 327953136752028, 98616516464966, 368652737257800, 297503341464665,
  218557315721775, 358640577908264, 13893695909030, 236263247873504, 147851740025389,
  97122316975407, 191675009887568, 31664168190834, 126553197434522, 55406040141823, 27028178378279,
  137972745161340, 11362459474596, 73434231046710, 108603911518921, 52345722235197 ])) (List.append
  (_uPl [126722848074727, 8037573732268, 136057796824716, 94955143122469, 77309685970673,
  161331074811460, 11617765779568, 158956086846502, 142103728686191, 80806605393035,
  118417824157135, 76462795038268, 70131967991382, 86275477649541, 12642729475381, 23035656979187,
  54045936614198, 11086966294562, 53327764356039, 12628729505267, 42394352527443, 60950736287600,
  55289530576674, 43404791432578, 100320500248890, 64446622402675, 29867294306643, 101217536269108,
  158232935333304, 84356190481690, 352622686966343, 467292722836413 ]) (List.append (_uPl
  [209097891569521, 136496595090819, 283731224593603, 370099805294788, 465904050763898,
  543942967455696, 539545458342458, 447021585765868, 519982137211662, 152973537912561586,
  156994469929654562, 158769800422318556, 161471834644752284, 164985569210318248,
  171647115951788162, 198470398124194500, 221811473768513484, 225829123640604276,
  287316000397304888, 287316000400227452, 287316000522344020, 287316000456927450,
  287316000670774602, 287316000619304026, 287316000747057576, 287316000621626194,
  287316000650492708, 287316000507386908, 287316000453905234, 236647611242004944,
  185260980252939578, 159237618270842742 ]) (_uPl [147908327165516344, 157039298457194,
  47404115307022, 13078856958278, 20385895821296376 ])))
private def _k256_641 : List ℤ := List.append (List.append (_uPl [52587390282702, 23381907794207,
  51532713018919, 45440084600066, 96993933459751, 50585028158471, 152726619724346, 154355688422008,
  87819457587747, 191317674536305, 58755121639934, 217018567486615, 154763011137655,
  250214553524828, 47615097664412, 65887701153057, 317393497542822, 28640627137552,
  381218688263642, 24643037507981, 363506641565737, 1137147817122, 298725309033617,
  106934587717613, 405179492095090, 78188865519482, 356487911242333, 100117430089439,
  391753320216008, 44169144477126, 415783397747897, 35433260189963 ]) (_uPl [446832848971065,
  159197546087206, 425080301151948, 279415346394047, 300773551117419, 361691406785616,
  117958777451646, 302827868463217, 70066313522181, 229859952197610, 97892068334386,
  279276677238039, 82599003359953, 361460177063071, 72418317939266, 318774492535770,
  277396206008937, 125772876145963, 323261514963598, 56078129065996, 251201919435398,
  114811288469105, 93917830258881, 107249578042156, 10310556727630, 125629252969172,
  58412845495287, 64343780511005, 97163360442440, 64812947286738, 122325422888098, 47471902369941
  ])) (List.append (_uPl [30149620396497, 157171113196946, 13150960906268, 109384494447244,
  140446632255897, 119427508786487, 158823113183674, 32516630243580, 165810935556608,
  121849816298325, 29803596096087, 103622401729885, 86199067567538, 69755478451280, 35594860874385,
  19111205081565, 32986969647733, 57614425089888, 26229197696056, 35948948906021, 367557603265,
  27404273965533, 86293033019963, 76287066600482, 26366959424890, 78931749020176, 59512180691447,
  36791414143255, 141880648199889, 181013398448518, 64436318332954, 351792709865687 ]) (List.append
  (_uPl [489114635040191, 254882820179659, 67224876017235, 242701145835971, 361569155855184,
  452163273188456, 509591782859022, 518788162824972, 411160418211070, 487896713253066,
  153207427342654200, 157326526482478222, 158552763300102498, 160326827843180526,
  163801907066241332, 170748991931194032, 195531063970622472, 220514511944820424,
  221785492433873654, 286167732057159460, 287316000514803942, 287316000442755300,
  287316000652282844, 287316000612701552, 287316000746599222, 287316000638707682,
  287316000663397682, 287316000534656414, 287316000470332318, 240240813280352488,
  185976847500595646, 159020631579059922 ]) (_uPl [147659305950582332, 150520898430746,
  45053683276560, 11776016952108, 287316000000290996 ])))
private def _k256_648 : List ℤ := List.append (List.append (_uPl [61017265997298, 104751613047517,
  25423133897647, 131381937333201, 47115855361422, 112713526086185, 114896101175367,
  112017197825732, 162771702695518, 55437907014235, 152479154560596, 115980795421030,
  296792082499525, 65608768757335, 153341666232816, 137104326848637, 75164779120569,
  418540586598594, 77702701994444, 373179326368355, 2248217076211, 328751025338820, 64515062468138,
  312469057229819, 164781301839689, 365291140513664, 137094368191648, 377340297448205,
  60187413826761, 339598339326608, 108539634440688, 453580597139675 ]) (_uPl [40516967922213,
  524913930833037, 186290120430734, 442601243543494, 368451481067755, 247586259606903,
  351161614434722, 65130278572336, 250120336139771, 46643808040917, 211588948957884,
  85900565571042, 296762177041779, 40192108873203, 396927384184586, 170994724852168,
  330429603685224, 307106274884957, 148434562675583, 259965608041605, 40049417499678,
  147138351028498, 150150256654867, 79781915274615, 131246416717384, 2598376589300, 54380397678098,
  107421191303239, 35410763261611, 105060929442885, 48106860947256, 76136789047472 ])) (List.append
  (_uPl [111413654157707, 72811597116557, 129205553731638, 37234236413850, 152357047696552,
  96718809401039, 75369565131273, 176983128614898, 49067430681802, 149994910952384,
  101294510196239, 16228944043819, 120819833893555, 44785219107550, 34055420949374, 34662068321216,
  33754141627797, 46920497616705, 36835401422480, 35478100929396, 42630420502575, 43156877563821,
  1333251245937, 93986649708339, 81524746034502, 201098995774, 34244589556016, 40036220437189,
  18812335809701, 146068272558847, 169675918477878, 47537702811134 ]) (List.append (_uPl
  [365639660759085, 529034682369485, 291666364072693, 34813421566141, 208899099920877,
  305732227041546, 396289553324186, 466795910964650, 508600195549270, 450552665522688,
  510127254807472, 152741744892694606, 156402089537758612, 157443951764824848, 159772728438515808,
  163992797811117948, 169833867380983668, 191847707657080800, 219212814849429092,
  219117033723088296, 277851302478198028, 287316000505220208, 287316000432229960,
  287316000630391308, 287316000602919944, 287316000745876234, 287316000653219526,
  287316000678798820, 287316000558210298, 287316000488623032, 243315490812135142,
  186334650866098552 ]) (_uPl [158631638689108802, 147450234293856240, 143228410143866,
  40211083198690, 287316000001061520 ])))
private def _k256_655 : List ℤ := List.append (List.append (_uPl [59101842069459, 35185895676164,
  54548452793826, 29074168766135, 90844321898492, 65969095873728, 136357680461665, 170985195557149,
  62678790004078, 200213301410780, 84140453213631, 197010300766850, 207757013977126,
  238102567141505, 76853061238677, 92862368592604, 302147695798405, 116084486594637,
  397927433254383, 107171552984228, 364017669406191, 75598667504621, 283269787541426,
  183716438432508, 363671483581269, 172463044354597, 320257790464256, 202179192615826,
  375099904041755, 140247531535969, 384398789923474, 98555171853304 ]) (_uPl [434610431832027,
  2439042959577, 483614491989243, 137560936811752, 421185222846820, 279215926652083,
  237157883267429, 280307276118894, 158139612064476, 213138999080131, 175090502525499,
  247387788791092, 194662477456078, 346025375880525, 82556165867197, 386635259435265,
  144135781108346, 251606749324918, 261483131406759, 53800889083583, 268388960641354,
  50712485788432, 160305184200782, 71455247511315, 49429860401093, 124429369149764, 32948778281072,
  115349054942572, 80117046012539, 13546767990823, 146116936441389, 9315154894896 ])) (List.append
  (_uPl [86722863300868, 119716775828913, 80472116004011, 129032568118107, 59035150231140,
  171754213864432, 117543303994067, 65601709902683, 193342632192546, 36680509974736,
  88001734834258, 113056076620711, 15153128681003, 96393472602917, 15108185445504, 1975373276980,
  53750732646400, 28431846095405, 49390488801633, 13398841496752, 27020253280390, 55426252950134,
  85418117109919, 13969679733193, 80983170061903, 79000489007064, 29245441680702, 17686508906492,
  75915253494079, 28897880106371, 141900696207929, 150911214453238 ]) (List.append (_uPl
  [51944792151510, 372284675211187, 529379418280627, 321055836711875, 41884850330823,
  132794484074981, 245924059117114, 360040977437030, 501739069745746, 550668905657074,
  430642032955918, 435033607256616, 738139105464600, 156123615357627710, 157886659966567900,
  158958862156209072, 162936193450385370, 169127799972677430, 188860227755616536,
  217420590025652202, 216546701645485426, 268058840946361088, 287316000496738506,
  287316000420880944, 287316000607447312, 287316000590886916, 287316000747039794,
  287316000660291302, 287316000694297516, 287316000584191104, 287316000510351890,
  287316000389894458 ]) (_uPl [216750853165622584, 172110503379519400, 152593544192620442,
  278359439240214, 100538876552578 ])))
private def _k256_662 : List ℤ := List.append (List.append (_uPl [54707382218239, 100786561461766,
  18952753991814, 135003652739500, 58972987113623, 103709482614906, 134322472539728,
  86633546353803, 172452673768165, 23311071240610, 138471063428579, 149967894598683,
  259695920281000, 109564540177388, 138688063231681, 118834075752214, 136449414350138,
  394287465647789, 7864430264179, 349478477239810, 80484752756618, 311105008024183,
  132376729619739, 267325079793360, 256389095929986, 320781923702135, 221729770483321,
  322655600860492, 163974368708442, 299919850590335, 219689916727893, 424467181822764 ]) (_uPl
  [171621618766244, 524162719005179, 34333421684187, 486689730155297, 230806424612548,
  340598028058504, 270660302259361, 162054377148111, 194435590979464, 123050234936750,
  147707091338719, 177738295792443, 223253416612592, 173073695382996, 364694657598827,
  17554866215485, 388558690398697, 204012826705754, 257263475592898, 237225999797727,
  75128713224437, 169230656506841, 79273102512198, 111840485699256, 108747102720661,
  60049084058433, 69809096609971, 52651652700422, 73978046292800, 111671364504501, 24156501165543,
  80805368403336 ])) (List.append (_uPl [67377971833810, 134394095146958, 87276367817885,
  30854548476175, 183902208366957, 3796750409726, 139748030943722, 140613959887311, 59416958573765,
  170822624440158, 50733707824642, 49488239683016, 129730244859029, 12549379466163, 43144136079807,
  33460392455634, 689530025430, 64603812313450, 5779845926527, 43994496021952, 25271289325158,
  7168394180744, 57381774517638, 103249244766935, 27271415415839, 53269106314163, 54222336406961,
  17712520905846, 60153101806022, 97236133170699, 30860175842759, 115863496886220 ]) (List.append
  (_uPl [144854198932430, 22991056922606, 374031538631921, 570966977374017, 387470043417981,
  112659834095889, 85756556333957, 262342641837124, 372373182923376, 466363980803910,
  486045634950890, 358102715100794, 411699472086740, 749253591294498, 155693740823468604,
  157133436951043938, 158369051099525536, 162458096764186578, 168818037699684016,
  186128491507450112, 214963499550454544, 214644501320988310, 258940956271735298,
  287316000487285230, 287316000406001486, 287316000588351098, 287316000575508820,
  287316000741659794, 287316000669367912, 287316000713399666, 287316000604629954,
  287316000532887720 ]) (_uPl [287316000407679092, 218961860773312080, 172388999715293890,
  152536225854339500, 311974389015288 ])))
private def _k256_669 : List ℤ := List.append (List.append (_uPl [64942557832634, 46543003511439,
  56796656557557, 12257340858260, 83146926304883, 80124243516821, 117221333108426, 183846350613894,
  36042810277181, 203953792248927, 107193664642828, 171138553905217, 254127112498507,
  217876068651118, 103296792622494, 116242395854373, 274471629897728, 198461241414666,
  396236373812869, 184458467825447, 345725300305482, 148215518565308, 251556961845977,
  249405248517473, 299087722586404, 255250390366834, 261660597234709, 289449842219269,
  329729463558070, 225100045671456, 320874605603791, 223943510133245 ]) (_uPl [382839080286418,
  163844342034194, 494402301567309, 18424017502525, 496613941417767, 165756765336512,
  329031339784972, 224272587282105, 226605013606835, 169027885566832, 228981567847966,
  181405987683881, 278967646203781, 279561192251852, 224945823681222, 393602190206281,
  12567926075723, 335199036938331, 154410434566912, 154068355478412, 236147664599989,
  23010798009229, 195354993321481, 21277932273698, 98928847162714, 96703911023597, 260150566699,
  140348992710731, 44505051116264, 40945103744646, 134170038113273, 31181418692763 ])) (List.append
  (_uPl [120935809354149, 50584133447716, 125946382014746, 112750990243911, 39232486427219,
  173808265603346, 41003373606348, 143557207747590, 160003903881081, 60315141724805,
  117150376636835, 84289466761576, 61132544175868, 88929093458743, 10845913493511, 22331064999797,
  54175016599536, 11748942290356, 53024748409717, 14564369482793, 43255744429035, 60080664465836,
  47765762761912, 54489207224686, 99253196226479, 42946206573367, 7828801958957, 29920072280855,
  26411282643346, 61593646702234, 105680652631241, 12638614401843 ]) (List.append (_uPl
  [123302257316752, 147542310616582, 40385778443996, 411350720350491, 594003471583589,
  413501194500767, 107633723211927, 85531719050363, 200705288945172, 276800391811830,
  385471366484540, 475910420211666, 390787562258216, 377515279083950, 675680119443606,
  155445456102932464, 157199555801861904, 157946857822126964, 161817776137977280,
  168253255283670286, 184105043616962558, 213113122865852788, 211651051529423082,
  250111020911980936, 287316000472902056, 287316000394658252, 287316000568899302,
  287316000553146240, 287316000739134622, 287316000674208822, 287316000731805254,
  287316000623441804 ]) (_uPl [287316000556279820, 287316000430826692, 220947294320729660,
  172559944713324060, 153692858436591510 ])))
private def _k256_676 : List ℤ := List.append (List.append (_uPl [47773882413904, 95541797857447,
  12215534057953, 136530632134325, 69825422812784, 92773271094911, 151022651811953, 59340686741850,
  178019604798632, 9415959280553, 120625012201538, 179491681579946, 214320045798451,
  149786119318753, 118992444113056, 95963872510541, 192120553153897, 352823808450458,
  93067953874354, 308685587854997, 159060171778077, 276509022490296, 192640988219246,
  206039661886323, 331728609263301, 254907082377604, 290879604042840, 244366119624565,
  255207634617187, 236235281326560, 312472029950914, 358313909997755 ]) (_uPl [287109100266557,
  473710224558442, 121012741191724, 480784671454291, 68510838383099, 395814387615877,
  158973148901908, 239602754630122, 114642508953765, 183643716941141, 64163072742656,
  245081624939956, 117909494955269, 280431600214093, 276867818159596, 138649881339902,
  383490103277965, 66668040729185, 321528875194965, 172106430958602, 176470707250370,
  159206126111005, 7101087096481, 121386888218142, 63716916160250, 104698582662400, 69930924591905,
  13988581037897, 95402216792675, 91691546331766, 90511488120406, 65178429752849 ])) (List.append
  (_uPl [5969632521419, 160414744344641, 21653412867644, 90351775292088, 162938359067411,
  90236501542289, 162205624126872, 61026957964956, 149195120396100, 136574791690789,
  16574044190527, 98484290077761, 93782251314578, 65443814598508, 36619492818639, 19875157063863,
  32636017656629, 57296513111050, 27560709668910, 34737164964421, 2518433600791, 31842217878277,
  88724216705349, 67120594905048, 39221591264114, 82336436572424, 48869436932463, 2952265099823,
  78577800037982, 49114355010690, 52665903239936, 64807204588647 ]) (List.append (_uPl
  [10874978210799, 87801394167048, 119155800203014, 40097996708826, 390648639000947,
  533511655420821, 390942100224925, 184047068025205, 21596266102083, 108442378471514,
  242157616348986, 404478381132756, 452903883589702, 340133099741534, 359113119549496,
  656485445926376, 155242888377465740, 157108223421145682, 157215635713479840, 161347384392418700,
  168897083429878458, 181978697150154056, 210500654657776552, 211403328347032834,
  240904786520561774, 287316000462103806, 287316000380322510, 287316000548692744,
  287316000526445916, 287316000739611470, 287316000666144366, 287316000748686880 ]) (_uPl
  [287316000649471122, 287316000583548122, 287316000447675248, 224509889741977842,
  176513744788487764 ])))
private def _k256_683 : List ℤ := List.append (List.append (_uPl [70043065574917, 57308975302134,
  58245852313446, 4749812874993, 74033122672014, 92786711094398, 95705825651503, 192655737613033,
  8547118400530, 202442940919325, 127275795943339, 140173774867838, 292395018748934,
  190224418002219, 125985219838251, 135122710966944, 235503667754413, 272175299649151,
  376223740796306, 252724062088320, 309574474982365, 212757169050367, 205406831815024,
  300034538088146, 215526232919805, 321036583688583, 184789203360218, 355545267075096,
  259115734495757, 291935175032805, 230521828481140, 329790087179896 ]) (_uPl [296229511986755,
  309713727398793, 456378894969122, 172516220395414, 519003324589907, 33903898541021,
  382993635405515, 141423305574656, 266973310454000, 103194819338141, 252391608658201,
  90424329517746, 323492766066844, 171869023406249, 333044999714551, 338577631500350,
  167227408753740, 362515580277337, 20590735896647, 226811988537243, 160416039711460,
  92367049089594, 192215437816147, 33182580175821, 127931329269059, 48363172252864, 32485574289532,
  133707197681345, 1420275497845, 85687674606819, 89406860151058, 63846357814306 ])) (List.append
  (_uPl [123967228941717, 31933501625005, 137228784521484, 65073459981102, 126298176788158,
  124988728601817, 47836661536857, 177390360440657, 76290878347728, 137864359629122,
  107627773770801, 27042375969345, 116279578226783, 50003411004318, 32874997001044, 34422276352596,
  34098989618605, 47384849599329, 35695297459088, 36643516869800, 41637764599387, 39405493685405,
  10452459224741, 98993217298507, 72977410413218, 12781806960800, 41243021321388, 27881084478757,
  28404714616857, 96197192581051, 66047298910494, 37800981907946 ]) (List.append (_uPl
  [58436477043699, 5667704087109, 82267251955428, 156577632912030, 53265024553028, 275199600997951,
  560071391402069, 485487514162183, 274713866457771, 55508353834607, 114624329006622,
  196597415043920, 342605717974582, 447948612210866, 346758347301456, 336075111252846,
  612680789028414, 154651186420721530, 157018791109286894, 157167326463921040, 160354739817863658,
  168628430471150286, 182219273107594008, 208320472926226570, 211271962367960990,
  235290268165688440, 287316000449071036, 287316000366422958, 287316000528853492,
  287316000506042636, 287316000724760392, 287316000655906908 ]) (_uPl [287316000776054388,
  287316000654522284, 287316000617587948, 287316000470825174, 245216830045312048 ])))
private def _k256_690 : List ℤ := List.append (List.append (_uPl [40295782582041, 89083850229550,
  5306338095140, 135938852472937, 79488418464025, 80108843517262, 164657503006808, 30739946981313,
  179339664189948, 41900411133038, 99435648858035, 203673740395151, 162111107003514,
  184903298210694, 94970656844901, 69379077094270, 239887683581066, 295959478884265,
  173968156842997, 252795882086024, 229419382191144, 226848140602791, 241849334347033,
  132313395382340, 386019122008836, 172053936361861, 339714373040645, 148199421538212,
  326902779713104, 153641639316259, 379128406341933, 260893373300314 ]) (_uPl [376469780650630,
  378340129300185, 264411631001955, 425492712709048, 101101662190312, 407108325227999,
  28968898057885, 288503771319421, 20634777817872, 220637118310548, 27922168982799,
  278649841406683, 4248087735754, 346433111833840, 146835233171631, 273017538363315,
  316048160421480, 81869464615550, 330098581756391, 76240396876347, 245312651941027,
  118967636328222, 92086938293488, 106499262091637, 5485512737897, 127028552698797, 54719169664000,
  77474912239566, 94718540891141, 49878783603807, 134728498067465, 33181010662116 ])) (List.append
  (_uPl [56977848043238, 143988182548867, 49848180595927, 124690217191311, 95451333625948,
  157857535052624, 136005495159413, 37317062209259, 192001824834397, 58293317751458,
  78410895173126, 114203516229545, 25406056623999, 95185608811557, 16842953420834, 1065485278364,
  53611908660942, 27825198105761, 50005032751473, 11446289517278, 29268429215720, 57428252783938,
  81865589410623, 1483471766015, 88111521647417, 73685249431546, 20669601835960, 22208900769160,
  58762733863505, 18661275420069, 99659057169099, 36276745945322 ]) (List.append (_uPl
  [48405085565012, 9485700083914, 64039192762166, 161617626800502, 247633294187266, 75355455302056,
  261980461910683, 551771797457935, 511576122244241, 275785875959049, 101194835120655,
  42126953766582, 174380478998146, 339229588811688, 428725044052960, 326890667735662,
  293020799663090, 576680796564330, 154686925574969866, 156562331668569850, 156154620016905498,
  160775284378974968, 168670261760358418, 181546706336263180, 208316259458228296,
  211333256557765478, 231159363707894110, 287316000432286596, 287316000355524964,
  287316000518206014, 287316000473150354, 287316000717581652 ]) (_uPl [287316000638870930,
  287316000785144184, 287316000671092152, 287316000609973378, 287316000601381012 ])))
private def _k256_696 : List ℤ := List.append (List.append (_uPl [80429468697784, 84115082463451,
  57897616387090, 50016992539090, 44302639409859, 116932257765321, 34407526489422, 196154868930867,
  56491406081893, 179087387494428, 159105101980714, 57741524244799, 342309914266799,
  110661384158532, 157976981773382, 156979200812081, 128538826478500, 381289306689998,
  287531309904237, 347498541405171, 198078562997676, 300656416934268, 90526054219493,
  344383648782409, 32972982992806, 383472069734696, 20505953117663, 406801360465225,
  93306653590264, 350185277323518, 37323650892379, 439461908169077 ]) (_uPl [96616815611028,
  481118156014030, 300132266118673, 378845219122277, 439663233867330, 178477585125432,
  377391760126807, 18683402804617, 263265130920624, 21499724175688, 223022832271091,
  67988769752977, 302668916572030, 32426448901112, 396922764197211, 162544240991275,
  339949911135963, 293202399618974, 175005134149198, 258417909012555, 3483517605949,
  158725898156647, 124058821549190, 96779342625864, 123309173758325, 34436588422401,
  65068921089743, 75621732282032, 62374174697238, 112530348094150, 4802061234287, 81569936066096
  ])) (List.append (_uPl [77716019575596, 126632943533760, 94161511603165, 24613292525227,
  183467256581755, 6653534406756, 139825982939008, 138648695976353, 65787294495929,
  169955128755532, 43244827940256, 58159055517684, 126565797331319, 24105147387323, 43043056132194,
  31092992634454, 9035461999710, 65100420126867, 5428529927833, 42754040371128, 15643097502828,
  8744822173398, 74484005860626, 92550109805617, 3469427549821, 71411593571661, 54855584278418,
  7455785072302, 74721164869236, 72998158311755, 22768259657025, 65367792112585 ]) (List.append
  (_uPl [12533810288552, 2943220334246, 50978705484491, 125746938410073, 143067008628622,
  188492424165394, 121530311289102, 210916302771905, 561413822073023, 508199154764683,
  319344130312347, 91514001603701, 53169145491020, 159491815049676, 332036670007138,
  394516772952134, 301027235666930, 318932782865160, 581418677018478, 154393421989955890,
  157246188833512378, 155855502553760654, 160702892325011398, 171767297730404674,
  184578533379031562, 210776907884118782, 212037065578975718, 234324139747832048,
  287316000439251028, 287316000356713692, 287316000534370466, 287316000467809892 ]) (_uPl
  [287316000731043044, 287316000635020928, 287316000734783702, 287316000744333126 ])))
private def _k256_702 : List ℤ := List.append (List.append (_uPl [2637518954516, 43770975556615,
  26167233884715, 108503530962716, 104007092576882, 14818416502947, 184038904648620,
  80720394452368, 146960495675899, 145433965112847, 6665910012934, 237627740453055, 40878444347717,
  251075665332115, 281825914168, 26054341587963, 318672817158491, 60350823018188, 353080090673346,
  34587545480155, 354794555230087, 35035515750752, 300058332224187, 90862195889377,
  407553443782730, 80321177503520, 353313607658805, 123643813849097, 389727353437380,
  83918392214118, 404637663836449, 41697056170921 ]) (_uPl [443486906177778, 42165610899874,
  475656697064676, 156910756594175, 415049891144393, 278749362667652, 244382247068772,
  274875192562021, 172757935672403, 204732979737338, 194050673801282, 227654481908577,
  232830032282861, 321776285976082, 157037985020654, 398299748350186, 52264113958631,
  310903830664007, 192483097737232, 128313508074846, 248088319712797, 8330902057861,
  192231425813999, 27869020225074, 95345855300096, 98688438940661, 827990566539, 140503944670587,
  42402531153438, 45098791683270, 130650158378009, 36527514605631 ])) (List.append (_uPl
  [123804296968651, 34428021606212, 131814397459420, 103133886771877, 66204998138545,
  163755650626604, 11312117780352, 161700534642020, 132631385027907, 95993525065581,
  117900832424982, 60782683460646, 91528223393994, 72785190336205, 23387729297277, 30294488681947,
  45069417229674, 34075581985134, 44813917092035, 29669249160371, 44396800237666, 48923729329746,
  9023227230242, 89530533990362, 84680709862825, 2680414994255, 34173161557613, 29703800308760,
  16758590742052, 92841365070890, 76397134567195, 30867090060969 ]) (List.append (_uPl
  [61348448798312, 6471416263348, 8549046339701, 11937189129711, 25193786107241, 147170410927502,
  199030390945730, 176181775434806, 161803965140147, 596973430328979, 534433753615597,
  288591562143907, 96114513073955, 26583482457312, 142588551726248, 332214415341138,
  401574284830420, 269990298453478, 272190703945168, 638418558656830, 155250866065355830,
  156039854227357064, 156523222509155840, 162413198001565596, 172806809886666058,
  187455389901624088, 211402731617009624, 214727069853787516, 243065917137100512,
  287316000456613106, 287316000347800092, 287316000529660354 ]) (_uPl [287316000525436368,
  287316000657796540, 287316000710991052 ])))
private def _k256_708 : List ℤ := List.append (List.append (_uPl [79021544879342, 107694468547494,
  43672973411631, 109533258913981, 13258759729124, 125206340748945, 69259798124063,
  150287316597274, 140724559974982, 95009410450251, 162991753525262, 81991259978390,
  318068945055387, 39475024955099, 157807161792576, 141139742585047, 66784939188567,
  418581690590138, 67586974061266, 369217551059565, 26491093042179, 323008394562464,
  102414070075340, 285500970922417, 233193756522365, 330610119152400, 213806694691194,
  324176868789369, 169101364622459, 293256438962340, 239230920270308, 410751466965369 ]) (_uPl
  [211002750100435, 510580677191990, 34653573683398, 490086884642147, 143290549825151,
  378950773453387, 200381732144102, 219191595476840, 136358356556717, 172949005411025,
  78475552592434, 238741921321230, 126830854827423, 277103072356937, 276698866165470,
  144448513261180, 380504183695229, 50340568824547, 326364530492309, 156849679404304,
  194188098647670, 152044454701775, 31116687013513, 119422128806878, 45343932456854,
  115653246002350, 65754725035903, 41485140840955, 97939016052311, 74466003014598, 115763175214648,
  50353886292831 ])) (List.append (_uPl [28740884408521, 156419425316618, 20581096873566,
  114937790097620, 125132928827025, 138506596078425, 149913962215770, 6415002346542,
  185481661958458, 82811209354111, 64418371552175, 113989960338971, 42002748467034, 91742701216340,
  21183373344709, 2614613275517, 51646280837119, 32699802014434, 48282276883562, 14221845487031,
  27292889272981, 56324408880185, 83308513298420, 4505483762950, 87206085707764, 74076661405543,
  20690461835665, 22403584761925, 57783153902176, 21346167399980, 100821421034178, 33662134004381
  ]) (List.append (_uPl [50818993464161, 9661736060841, 60345348960509, 115766703063655,
  39282909740991, 60803905273807, 93842843773340, 176095198769944, 207251696692076,
  177105742981476, 597232542034833, 527322762354233, 301923537104577, 106399527669819,
  9123803265752, 169113679874444, 338056615500564, 337787933843144, 262375474704760,
  328075622090476, 604874223819786, 156074471056721928, 156880980788234380, 155460835431397542,
  163399410459782086, 173559136734844600, 190398920707448022, 217883647352617064,
  212681935059422352, 259277813029581258, 287316000414786004, 287316000398248176 ]) (_uPl
  [287316000482858258, 287316000610822872 ])))
private def _k256_714 : List ℤ := List.append (List.append (_uPl [44819322485123, 14244359851552,
  49908013117344, 48422392561093, 96669161486956, 55091880084768, 145025640098241, 166117619840069,
  66301541954232, 200360469383838, 88370133123593, 189414181144612, 229493133349878,
  227470688022783, 95431956833331, 111858464016416, 277738305699301, 198301893417673,
  395182034085850, 197259255558930, 338026785025049, 171037114115949, 234205166702718,
  275879051403346, 255258175960889, 297906232796291, 211520074749052, 340273507975638,
  275869533936229, 282858807490975, 241132148222746, 324518975374936 ]) (_uPl [297127191958383,
  314595527272039, 451266207381594, 190536068138928, 517368629583929, 6212458589657,
  389521946272593, 114985482016014, 272925773386698, 76795691740093, 252506576599174,
  48585217899788, 328615308105770, 111069040330645, 368871109238243, 286964785870974,
  242987903091318, 350227391353855, 64154227697063, 252469842213871, 93363265009524,
  130270983891032, 167112935847535, 69157763569507, 132424096344324, 3510420588518, 53630893708590,
  105927223364239, 39743147197307, 107949633138887, 32332501108212, 79559284646206 ])) (List.append
  (_uPl [99090574822145, 100902932467095, 113898794782956, 2471564608968, 176461685885366,
  40977418241897, 122377587804387, 155945555051554, 34757890795332, 171170356205066,
  59076111668717, 43920579772005, 130334624733102, 12469215466526, 43187004040430, 32752356517103,
  3759282021129, 65168152069705, 1356629936952, 43346044269669, 18001957468761, 5853178185749,
  72449105960443, 93961337710134, 1553023551548, 70974485596714, 54858860277621, 7182925074673,
  75160456819505, 71149514384136, 26609775623792, 65443812002132 ]) (List.append (_uPl
  [8869198310307, 3559248326515, 54432869337224, 133762133912702, 56325724181882, 24234086205835,
  19782953649980, 11100940710368, 57390935484224, 267193705883184, 149492312708706,
  651590453435615, 545851201018441, 296364023821103, 87001070715819, 11620226799568,
  140390720934628, 343232585444494, 372170420424360, 203835369355546, 329485648095330,
  745341094334954, 155790505245133214, 155834988390452660, 154678940257917616, 164182291959618708,
  178617344659867246, 191151835830667686, 220364735076809516, 225909177052520770,
  281967308096159510, 287316000348257510 ]) (_uPl [287316000488081756])))
private def _k256_720 : List ℤ := List.append (List.append (_uPl [55096862205903, 100020985527346,
  16542626019022, 136093972412138, 66759114906187, 94445347029722, 150951279815562, 55894866779303,
  178726464562201, 20822515250272, 111465568512685, 193373100953189, 181979682599862,
  175496194549586, 100266296706841, 73136789026774, 237018747695306, 296045662881273,
  178584124761929, 245350514317892, 240447461861540, 213890189016231, 253009853765433,
  106719267720102, 399898888710890, 134548384941519, 354083523562579, 96790582119048,
  354847449932282, 101369392044097, 404035747916509, 187304726797554 ]) (_uPl [417101641805642,
  290761563863113, 352272548487943, 355006524083832, 226144452694122, 383418761039321,
  81755533790175, 303067912170641, 64130957575376, 229757836314627, 109615080146109,
  275183554104146, 121346270907302, 361559269019201, 5698966175725, 365628765653047,
  191957764301532, 223238718204692, 275916626705697, 42996137156725, 268578072530936,
  47566853822394, 166015727907658, 63233495706993, 62940756175291, 118542201773818, 21336898450980,
  129773030036942, 64604542629415, 16645611975843, 143223137123758, 17636334845070 ])) (List.append
  (_uPl [113946869981818, 69120273181463, 119728450451043, 117102385938908, 30350690488252,
  174830797454665, 40780801608431, 146316019608953, 154114132174050, 72578833540272,
  118364820202026, 73647423125731, 78413555789715, 80155378005020, 19181709382496, 28174300789410,
  48091989073745, 29265434080711, 46985008968668, 27463045227696, 44702420147455, 50632037245511,
  12456223215653, 87896370081199, 85670313804192, 3506330993172, 34155549558108, 29624084318375,
  18182194730455, 93647512977243, 73634850668162, 33559822006568 ]) (List.append (_uPl
  [59977988921623, 5966604278141, 3534330356160, 24577873070480, 22047453732596, 75434156422333,
  35825525124124, 63496137356432, 7874585455110, 5067107766850, 250840698991452, 176694988092688,
  649740605546337, 541661785038965, 264178639237361, 117219117589035, 918180194078,
  210445712632492, 331417761049772, 321649853984014, 294070463082392, 321462077692502,
  711374242344650, 155767036695640228, 154529708143481476, 157050594130893274, 165725805739128418,
  176113675416828882, 202618676685012124, 232110759850864376, 245644966352798850,
  287316000248916820 ]) (_uPl [287316000405920576])))
private def _k256_726 : List ℤ := List.append (List.append (_uPl [74230157307602, 68125963028765,
  58900688019785, 26227632787158, 59722127095347, 107826434393091, 59996166247514, 197878660012107,
  36138878276467, 188322626807668, 153362582492372, 75704364057251, 337407003064165,
  122528791939260, 155887677995336, 156320976960447, 132462858415982, 381236218693850,
  283936670035641, 351324853079907, 185833883266980, 307494464363778, 71517638409933,
  345037728191790, 5909555037502, 386456700279066, 23303013111693, 404953305459352, 36946573930502,
  351626100679547, 35011382899531, 453487217186113 ]) (_uPl [7809495985400, 517760968187918,
  203322996171103, 442217671572101, 355886677504624, 269537670965444, 330305059715859,
  106087754140487, 225815637647306, 93165443507352, 170854802667161, 157817360321563,
  236972128131652, 163858391555652, 364508121614305, 5153610228099, 391937393545949,
  175845051325232, 281121770424026, 218435817034251, 120634312586485, 168419776778540,
  33099647001928, 120532972557692, 80956431758509, 94045171128735, 71302448321346, 2235665061988,
  93929948991902, 93900494216803, 89307012153799, 64487529785152 ])) (List.append (_uPl
  [1110092526268, 160704460015797, 9676832916553, 100086506910877, 149719195831550,
  114000240952422, 158744909197073, 24683490289197, 173839515028431, 105282580824450,
  49010727853204, 111568212900922, 57888128234427, 86955849603301, 25258521251734, 6267073259192,
  49227613005954, 37340997908735, 46286465010653, 16935465450318, 25229765326154, 55094172974458,
  84630757184337, 7523743756791, 86268281767477, 74461017379408, 20711265835370, 22596252754632,
  56783581940195, 24014035377199, 101840648897793, 30972090058960 ]) (_uPl [53068205358574,
  9753716037756, 58121561121870, 107974779407298, 26202793611456, 61556910245584, 74278206291960,
  15092425616448, 40291080586450, 100646985872510, 104241565966012, 282961794036720,
  184714804730444, 682808885145677, 534397520492145, 264862061123597, 66983701301829,
  14344122860494, 189510002670920, 422298201306930, 321320570456144, 183244616771610,
  320271855359448, 151206043012427264, 157516443897272256, 154856420512285090, 152668840978570342,
  172285084197373424, 186279124764715396, 219871203188990706, 245657733547569952,
  260548027824211398 ]))
private def _k256_732 : List ℤ := List.append (List.append (_uPl [15472690903906, 63321415158951,
  15476218029777, 121707546213708, 99811517193104, 34239440365931, 184746632296393, 56545026772428,
  158012823035275, 129695053627109, 22044181965916, 237889764215260, 18102460416909,
  248765105802125, 6273517909934, 21896565610669, 318209137311051, 60469655017576, 355456786510420,
  24739273507773, 358072290730025, 17714939800230, 298996180928239, 116880131595813,
  396039397109872, 119790985125180, 338629177132907, 173817685143845, 379723963447290,
  137168119583102, 380106754266763, 124942735614247 ]) (_uPl [422518437282448, 71016670789358,
  495379277106086, 41496605452065, 480270903050935, 189570428925538, 321000828201452,
  225681883226347, 230013565426909, 160839677868122, 236883839179778, 156811852345769,
  300312548766109, 236962441806050, 284756453877566, 369600985313371, 112165941501107,
  360599681358015, 54856043757244, 215901873171800, 172459091372475, 87506389198001,
  192734921744528, 34695952160100, 129139837101910, 41146760348647, 37716954184839,
  127909714182106, 14178615461368, 95899470104822, 67374752651583, 72746521319499 ])) (List.append
  (_uPl [114901361910228, 69917769167798, 128151997828747, 29446792488249, 162270979112207,
  73776197844708, 100784016540912, 168459958033167, 2768870907081, 168155513160587, 73609931316590,
  28831295953264, 131896436122475, 650779494931, 42789880212549, 34065752394296, 1549690024820,
  64771140265794, 2723085935111, 43749440167038, 20302745429974, 2948542193202, 70309430057418,
  95295285613241, 363975551963, 70530713621619, 54862024276836, 6909449076962, 75573876769486,
  69244590454627, 30413323585411, 65373448108332 ]) (_uPl [5176082324584, 4159484317340,
  57126497185275, 137866121495507, 43502256182920, 924199522990, 48847488307744, 14901435926882,
  58832570610336, 41445242318450, 101623848658624, 185216446260795, 261716569529980,
  200260685578092, 702942565528793, 490952271810393, 216841837379551, 105326004145413,
  89102387507694, 272775448221212, 320030219158918, 279151956543280, 157728999865284,
  414064519700342, 153693423785240532, 153824741656581694, 156052882718311842, 163787389493336018,
  185305693992800488, 199480724618862372, 231979376953296810, 239453287255938838 ]))
private def _k256_738 : List ℤ := List.append (List.append (_uPl [82489456242510, 102237381327036,
  50487613083613, 92986435572891, 4482803755654, 126944412044661, 44069990414471, 165748243860378,
  126706864536746, 113343698060799, 166215896986190, 64182588183834, 326672280299053,
  26225929016877, 159670393568074, 143009358450481, 62576651219563, 418602074585912,
  62511638091182, 366859559402171, 40810572994965, 318796299164534, 120739397813066,
  269294347706379, 264556947700321, 307618424359030, 247877093707620, 288800606242667,
  218726043609399, 258573568537338, 294800110616432, 367458149565037 ]) (_uPl [285265692321287,
  468139064940888, 145344460949610, 471636680800525, 12941702539453, 405874617669551,
  97798749656300, 270711704869214, 56849501633871, 212145083166463, 5598525035758, 275434630061780,
  10169863731119, 344043172099191, 146506485176302, 279719310132780, 304902340930233,
  105836484386039, 324257922821306, 47536001128058, 258046350712248, 98239432947361,
  122482309593687, 92343722822264, 24642776659558, 127907444450023, 40064726130867,
  108845523243251, 82037649911304, 12959523993312, 146528452203216, 2319270912777 ])) (List.append
  (_uPl [97691274883697, 100213012486868, 101877639324654, 125875989019923, 6739354573771,
  179398744228574, 68868133246542, 126444168465218, 171340879204921, 47370517878041,
  116228840824603, 85085786730272, 63971184121268, 86351021644463, 14735505450393, 25756584888539,
  50692712908412, 24246406161468, 48890380839817, 25137281289677, 44864456056768, 52226777158488,
  15870851196412, 86189854170330, 86628221744881, 4332022991797, 34138105558599, 29542016327966,
  19599526717922, 94379628882830, 70768014765339, 36177513947681 ]) (_uPl [58413321041952,
  5435416291700, 1500690358929, 36675860976393, 19001193078699, 53437050501016, 33913940813776,
  25991311681104, 3997959380140, 6033362480272, 9710321272294, 138097824853304, 248504009989771,
  249062471990270, 211072493645244, 664610343175527, 494536103571341, 168383859300975,
  15771366649971, 23544307513378, 251283044672300, 335044827269378, 301852171946096,
  284737107428106, 269960951077128, 154099573071809150, 164494600619935096, 165345133538966084,
  179473487556124030, 193803825653722734, 196652253745008724, 230300270775883104 ]))
private def _k256_744 : List ℤ := List.append (List.append (_uPl [28560562774453, 8245947873828,
  42921621440716, 70702608173503, 102292456885410, 36641168340992, 159922479316817,
  150727588578853, 85388469635592, 195220902123260, 74871781390895, 200148540597100,
  211819029867576, 233082671589715, 90000012964461, 108837040120934, 279854153565737,
  198195605419671, 394397306267406, 205626719371410, 332240921495231, 185670697781321,
  221359775238128, 291394634601750, 223261288751169, 322244447623833, 174240539570864,
  366807370299230, 232453127264033, 312580189791511, 178621925522700, 377955181028266 ]) (_uPl
  [224647177828969, 398122268542041, 393080082823718, 292869906048740, 489512050187451,
  102329598126259, 391837937690034, 28210738778202, 271774693650055, 3907268210483,
  232713491550904, 49779165892216, 307993088093469, 24645836923051, 396917920209848,
  154004997123294, 348754762571700, 277925628317311, 200124913538705, 253529642053632,
  33146997533544, 166294773230206, 93863202259937, 109722313867103, 108989330708264,
  64115887978300, 70899108420022, 37189632885281, 82987353858275, 106837529265610, 57071648824178,
  74728389169721 ])) (List.append (_uPl [30898536389863, 156620129285851, 39468860722810,
  80795207595002, 168209190680055, 85250429642091, 162198848137830, 55025270038972,
  157396712014776, 125151968175551, 32526428069589, 106985257445423, 72793451930122,
  80894997966772, 29017213143073, 9853397229565, 46377633165961, 41716417789434, 44028797132028,
  19575501407289, 23085441375073, 53740289066541, 85830473068556, 10536067747550, 85298389826536,
  74838149353137, 20731957835071, 22787184747273, 55764521977540, 26663087351750, 102715396760134,
  28212942108933 ]) (_uPl [55145665248587, 9802520014503, 55560149276715, 99385415725779,
  18572429074465, 63122024134484, 76885426985154, 20614753788860, 44885909393304, 46686646557742,
  9119634474290, 48864989175070, 155438056341660, 305240413083439, 284802340978790,
  249633644406822, 689623974423385, 364446480089751, 199446947944387, 91241109149032,
  90892204272318, 306820709006302, 454188913219706, 195951352834994, 163581001635632,
  155240055435651198, 166012335489924478, 176282607191424406, 172657767161957887,
  180924788069467186, 186510755785256182, 208000809067058324 ]))
private def _k256_750 : List ℤ := List.append (List.append (_uPl [67243765723523, 106679496759806,
  27155129866794, 131768141283646, 52129619265635, 106485290468500, 134152680546140,
  80100866462207, 175648873306599, 483063288292, 122560120129473, 181876413480593, 201063754150524,
  165602842870328, 105404800561403, 76843372955748, 234107307808164, 296131734878281,
  183170412678745, 237738210542740, 251104821516722, 200342053404815, 263075629158887,
  80458067984604, 410365343372728, 95539009376517, 363430930033987, 43683262452104,
  375239344025194, 46524224466205, 416881585374173, 107218119781428 ]) (_uPl [441089742728982,
  189956861704459, 422009849331449, 264006918760374, 336602042121210, 332280292489881,
  186016052432177, 291289938992964, 142794212421750, 215035494907161, 178945486390705,
  238097613357922, 222432820639648, 325302745727409, 157362981015651, 398419896017895,
  34286238029536, 322937585888990, 166889446322089, 153148639502483, 231635548883888,
  35129505933990, 198251788540460, 3197744339221, 113764618444983, 75142707724008, 18654974478734,
  139842164828515, 12432423469917, 77213362925115, 98057627893954, 61542685913144 ])) (List.append
  (_uPl [124260276891057, 35291597599361, 136234616786490, 55115652168424, 141472552212328,
  103828961229965, 75776741123629, 175808024952428, 29296966828090, 160984574087438,
  86526806891607, 13183524057937, 131224968490221, 11177211472142, 41856612382008, 35019236267313,
  6844966010763, 63912520459979, 6787425922332, 43962492063677, 22538573386595, 37130195721,
  68068058151403, 96551113515018, 2280771551056, 70079829646368, 54865132276039, 6635469079155,
  75961200719205, 67284954523184, 34173695541952, 65156980218549 ]) (_uPl [1465998331331,
  4741240306755, 59488325026432, 140952029067272, 32245500035479, 24972193732195, 37087064911176,
  65267278066876, 40933484267166, 61323813619584, 75142151082734, 12924021067282, 114208757401486,
  92549159178656, 356135064642907, 249099260993742, 205234266744184, 661731497772233,
  446938620294475, 149179721266189, 37775108420539, 219516251547628, 321951738820024,
  311832270108092, 746106268494352, 156298410887762873, 165928594983204889, 176396178080337495,
  173601328559237890, 165945620712785850, 188067689960319484, 185204528928418658 ]))
private def _k256_756 : List ℤ := List.append (List.append (_uPl [64455581854434, 49222435464515,
  57683192425913, 1574864877610, 73442014692731, 96098354962673, 84355437877612, 196243124906860,
  15287950384495, 195500202090228, 146333126983114, 93199211819867, 331049771848319,
  134056839697982, 153554046214160, 155553049108151, 136363090351590, 381183186697696,
  280294878165381, 354912212751189, 173302427518908, 313484839781238, 52199934555333,
  343535025164794, 44741970953844, 385121661179675, 66781580919773, 395998627358322,
  20199857974240, 344141478665361, 106300950461897, 451779945837996 ]) (_uPl [81309579721902,
  530851804171304, 96052925391565, 480037379584385, 249156336270924, 341301556020436,
  257103430694869, 184271144594975, 166879111836614, 155163042059938, 99417956311307,
  228365373873483, 140007234618310, 272003852567972, 276445046174275, 153080381137081,
  375358988314514, 25663636917490, 331358805421910, 132302891992315, 217709413642159,
  138120811528874, 66172154696214, 112320349658385, 15962720707553, 125955368913589,
  55448793632898, 79365640194736, 93414861052101, 41667951734461, 140351961517045, 22134786804672
  ])) (List.append (_uPl [75950423623660, 126086495558607, 79121620038181, 129065552055700,
  43555238391606, 177288861006020, 94623008706951, 102694541184535, 183835962147290,
  20991410070548, 111539709429068, 94875790281921, 48445548383033, 91281793259812, 10104501500116,
  23066372978278, 52849188735113, 19054842226811, 50519336706216, 22702149346054, 44882348034098,
  53704085068857, 19262519172545, 84412554257675, 87553705684930, 5157434990130, 34120325559092,
  29457428337529, 21010138704447, 95037376787719, 67800882858590, 38714341884442 ]) (_uPl
  [56659541158907, 4880260303963, 6527222347996, 48502808845574, 12712812874696, 31934477697919,
  11629940299386, 105732482606208, 55626596977216, 65493180566476, 113148061205236, 88813598647830,
  85152931009398, 161695076376462, 96538769211986, 310960819679985, 270863266114978,
  359370291517296, 654574919545561, 336131701173087, 76905897959811, 27521875404307,
  129257302432668, 746224595569330, 158980380164275859, 160818714684808129, 165558806778044557,
  165140587058714379, 171316513974545432, 171952507320114338, 169830936604052647,
  176122864759299564 ]))
private def _k256_762 : List ℤ := List.append (List.append (_uPl [32837282713430, 80163246626145,
  4201850098323, 130904425391822, 92775117775378, 52827744122739, 181669321235335, 31409538977512,
  166886246352791, 112539006079891, 37237485868844, 236680556882256, 4751416432575,
  245765186267147, 12819189896436, 17723277629437, 317688225463375, 60588599016962,
  357774570346420, 14874313526207, 360797866225747, 345195817172, 296640541628279, 142167491229763,
  381145022393400, 157921832600132, 319142186534219, 220941124207921, 361638541383820,
  186935934658066, 344228844509989, 203853846515879 ]) (_uPl [384690440176334, 180968301824154,
  489615702909417, 76315305301517, 514516018502709, 86820398258084, 372240376685706,
  156873061262577, 265382210665029, 100255071389944, 253001364199662, 66811173763353,
  328169184620475, 118472828242440, 369001729226502, 280431966107623, 256973482681685,
  342984772201476, 93675327440210, 257874597176068, 58169029379441, 145902795103819,
  144835380864944, 88059078991838, 126817517404437, 28513580475853, 64578361126339, 73692812324730,
  65918750587472, 112381948226843, 21143309182379, 80458784483692 ])) (List.append (_uPl
  [58952044006974, 144379174520528, 67360416301671, 57919908119645, 179849769419426,
  53327714121744, 160159132926086, 83679265603547, 136607412890247, 141928475423466,
  15327568196592, 100329909961922, 86465879559269, 73648906301427, 32412129020096, 13335561186946,
  43121205315756, 45794309657381, 41522153246997, 22130417358144, 20867085419572, 52265837156234,
  86905924951217, 13539487735225, 84296801884907, 75207889326734, 20752593834772, 22976100739862,
  54725974014201, 29291083323655, 103444264621397, 25390850154194 ]) (_uPl [57044541134562,
  9807756008811, 52676009424146, 90062396016756, 15874320799828, 59556420121796, 8653204295080,
  39474120721407, 95058267976492, 91372068015956, 99190451528722, 178667724800126, 100915476119752,
  68905258883402, 293615788153676, 78895184829804, 438891418572547, 239856627539928,
  314037335152448, 588758738073507, 239273709518949, 149406185884079, 295048937854545,
  156618104398276241, 161802482345201181, 166254674778353583, 161346776986716561,
  157807013701507043, 164301119888669917, 175038543964531856, 156751342960219788,
  169366644653838908 ]))
private def _k256_768 : List ℤ := List.append (List.append (_uPl [81984280405999, 92406414049808,
  55399092714745, 73378484114173, 22096875675294, 125595316660702, 17977126573467, 178395339057944,
  110941857035948, 130439377605117, 168045192438840, 45976596338664, 333867383524189,
  12904033053675, 161283361341108, 144778510314193, 58357163248533, 418622346581680,
  57426166118758, 364252423742461, 55067164927711, 313705059757870, 138542469508336,
  251404308442167, 293661994778411, 281188217472230, 278432092586372, 248355671516209,
  263695274349253, 217327161895624, 341568508645640, 311416879832865 ]) (_uPl [348145738050485,
  404402724283066, 248557947343800, 425933684681513, 118241722058023, 403741690233804,
  12516434088808, 298702349838376, 28068833794319, 229325824593297, 89041324460036,
  278477333449565, 107833051086909, 362089896741100, 6052522175544, 369225617346554,
  175960496602965, 242258137635511, 257696999574124, 71821044923244, 264057333831185,
  21106210018147, 183088026769067, 40775172089160, 87737359559130, 102489774769863, 1964006565747,
  140786800590175, 38125867222330, 53184575543002, 122394862884351, 46624314391319 ])) (List.append
  (_uPl [126642208178145, 1172477739320, 137757956293640, 78339383663681, 114913461140923,
  130016940420560, 48202985532816, 177764300157518, 60553562560533, 149835450962693,
  97543210403114, 2719588084008, 128331645094614, 22841367398479, 40398904546671, 35602560137514,
  12080321979090, 62598452650890, 10813237898667, 43984416039959, 24701881338768, 2874314193326,
  65728070242288, 97727365415551, 4196671548819, 69622225670947, 54868240275254, 6361097081264,
  76322148668680, 65272118589745, 37885683493463, 64795024328278 ]) (_uPl [2248654330538,
  5301996294818, 61504744861627, 142997400631155, 24295152023367, 28428709958324, 9340352108115,
  23692340882733, 93023672231714, 125206370660300, 127123250591658, 164608585246926,
  154311196522140, 137840643238228, 89200384638453, 240334031619772, 47886195751940,
  327806126833531, 271713065870906, 308625436503680, 565355051361099, 99200066900803,
  682951269448711, 156771254333864531, 162033218767364269, 163270126366585515, 157004953517340963,
  157804978404496735, 158801894504004159, 155576613478342609, 165307596719648486,
  161555219096069830 ]))
private def _k256_774 : List ℤ := List.append (List.append (_uPl [10926106930151, 30383587730378,
  34317165709784, 90655015648523, 105004368258662, 17299608491652, 171543038467435,
  132778469239901, 103297773239238, 187948182839478, 60745053612967, 209644964021150,
  193231734342736, 238048807146701, 84426949087807, 105739456222556, 281919321431169,
  198089205421667, 393546946448588, 213854519176164, 325942601956935, 199792217419727,
  207556615742220, 305088369758878, 189358721432611, 342980854366155, 134490004228574,
  386903696512262, 184089568352091, 334367099945031, 110779606418960, 418279098368390 ]) (_uPl
  [143203187147737, 463538889241529, 314670901708990, 378280655146766, 430083678391899,
  203545788651555, 363174565519050, 61015678603584, 244763096529805, 69386583828825,
  186674998102174, 142062124676100, 246731555752589, 156858027678911, 364368149625904,
  4151658228520, 393509956902418, 153745351728235, 296315829484283, 201023765887242,
  152226459920394, 162830165722755, 2959495100227, 121187640330476, 55073708314778,
  112858566196368, 66205020998649, 43649708816623, 97896792115242, 67493107217206, 125093278732700,
  40614422527285 ])) (List.append (_uPl [49944892160157, 145393754445016, 52555920557278,
  126529396910996, 78597545949181, 168580330203165, 117173004007942, 75795473744856,
  191254477030355, 5906410113027, 104400690002147, 102827985789364, 32099904570588, 94874892856709,
  5347105531047, 20132729057677, 54542544555374, 13727366276282, 51862300568625, 20168345396571,
  44756264124853, 55061216976836, 22626523144088, 82565870343164, 88446653624347, 5982118988169,
  34102769559579, 29370488347062, 22413470690038, 95619860691986, 64737542947789, 41164705816997 ])
  (_uPl [54722473272118, 4303376314888, 11515898323421, 59971972678967, 8527064680689,
  33388937917250, 28867285528855827, 75137356468377, 21272749418150, 2193860747986, 15246033916314,
  31753796175062, 33519367095926, 55608622895222, 42388752561720, 149152308987344, 179342199220644,
  522997862822877, 92856968832027, 52584653413066, 153101257686914603, 159051788566713700,
  161946968881963982, 164880340011128732, 162065745683611572, 153467905122606028,
  153845189720230072, 150935323060508240, 100307166876904, 148537377028890, 155835785253267534,
  287316000060761580 ]))
private theorem _c256_0 : _wkbQuad solWkbSched_r256 solTrigIvs_r256 571 7 578 7 585 7 592 7
  solCkpt_r256_s4 123 14173 571000000000 _k256_578 124 14365 578000000000 _k256_585 125 14559
  585000000000 _k256_592 126 14751 592000000000 _k256_599 127 14946 599000000000 = true := by
  decide +kernel
private theorem _c256_1 : _wkbQuad solWkbSched_r256 solTrigIvs_r256 599 7 606 7 613 7 620 7
  _k256_599 127 14946 599000000000 _k256_606 128 15139 606000000000 _k256_613 128 15331
  613000000000 _k256_620 128 15522 620000000000 _k256_627 128 15711 627000000000 = true := by
  decide +kernel
private theorem _c256_2 : _wkbQuad solWkbSched_r256 solTrigIvs_r256 627 7 634 7 641 7 648 7
  _k256_627 128 15711 627000000000 _k256_634 128 15898 634000000000 _k256_641 128 16081
  641000000000 _k256_648 128 16265 648000000000 _k256_655 128 16450 655000000000 = true := by
  decide +kernel
private theorem _c256_3 : _wkbQuad solWkbSched_r256 solTrigIvs_r256 655 7 662 7 669 7 676 7
  _k256_655 128 16450 655000000000 _k256_662 128 16631 662000000000 _k256_669 128 16812
  669000000000 _k256_676 128 16992 676000000000 _k256_683 128 17168 682999708385 = true := by
  decide +kernel
private theorem _c256_4 : _wkbQuad solWkbSched_r256 solTrigIvs_r256 683 7 690 6 696 6 702 6
  _k256_683 128 17168 682999708385 _k256_690 128 17342 689959443081 _k256_696 128 17491
  695452552404 _k256_702 128 17635 699680057487 _k256_708 128 17782 702455025810 = true := by
  decide +kernel
private theorem _c256_5 : _wkbQuad solWkbSched_r256 solTrigIvs_r256 708 6 714 6 720 6 726 6
  _k256_708 128 17782 702455025810 _k256_714 128 17924 704155767834 _k256_720 128 18067
  705207540481 _k256_726 128 18208 705862941400 _k256_732 128 18348 706294198717 = true := by
  decide +kernel
private theorem _c256_6 : _wkbQuad solWkbSched_r256 solTrigIvs_r256 732 6 738 6 744 6 750 6
  _k256_732 128 18348 706294198717 _k256_738 128 18486 706584066589 _k256_744 128 18625
  706767266532 _k256_750 128 18764 706889254001 _k256_756 128 18902 706983702798 = true := by
  decide +kernel
private theorem _c256_7 : _wkbQuad solWkbSched_r256 solTrigIvs_r256 756 6 762 6 768 6 774 6
  _k256_756 128 18902 706983702798 _k256_762 128 19040 707061907131 _k256_768 128 19178
  707129709279 _k256_774 128 19315 707192623749 solCkptEnd_r256 128 19447 707253143071 = true := by
  decide +kernel
theorem cert_solWkbTerm_r256 : checkPulseWkbTerminalTable 256 solWkbSched_r256
    solRatios_r256 solTrigIvs_r256 solCkptEnd_r256 19447 707253143071 313 solTailLbs_r256
    707253143071 solM1VTable16 = true := by decide +kernel
theorem runPrefix_solWkb_r256 : SolWkbRunPrefix solWkbSched_r256 solTrigIvs_r256 780
    solCkptEnd_r256 128 19447 707253143071 := by
  have hp := runPrefixSub2_solWkb_r256
  have hp := _ws4 571 7 578 7 585 7 592 7 599 rfl rfl rfl rfl hp _c256_0
  have hp := _ws4 599 7 606 7 613 7 620 7 627 rfl rfl rfl rfl hp _c256_1
  have hp := _ws4 627 7 634 7 641 7 648 7 655 rfl rfl rfl rfl hp _c256_2
  have hp := _ws4 655 7 662 7 669 7 676 7 683 rfl rfl rfl rfl hp _c256_3
  have hp := _ws4 683 7 690 6 696 6 702 6 708 rfl rfl rfl rfl hp _c256_4
  have hp := _ws4 708 6 714 6 720 6 726 6 732 rfl rfl rfl rfl hp _c256_5
  have hp := _ws4 732 6 738 6 744 6 750 6 756 rfl rfl rfl rfl hp _c256_6
  exact _ws4 756 6 762 6 768 6 774 6 780 rfl rfl rfl rfl hp _c256_7
end QuantumComputation.Specs.GroverFindAll.GroverM1PulsePt0
end
