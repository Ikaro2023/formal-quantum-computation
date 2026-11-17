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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.Stage4SubCoinSplice
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.MidTap29Coul18Stage4K2

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section

/-!
# `K=2` Potential Slice Bridge (`SubCoin62` / `SubCoin61` / `SubCoin60`)

Instantiates `PhotochemistrySolution.Stage4SubCoinSplice.wrapStage4PortBSubCoin` over the `24` -coin
`K=2`
Port-B potential oracle (`Stage4Coul18K2`), providing:
1. `PhotochemistrySolution.Stage4SubCoinK2Bridge`:
   - `ofCoin24InPlace`: zero-overhead adapter from `Stage4ReflCoin24PotOraclePortBInPlace` to
     `Stage4ReflCoinPotOraclePortBInPlace 24`.
   - `wrapStage4PortBK2Sub`: generic `(kCtrl ≥ 17, K_sp ≤ 6)` coin-splicing oracle constructor
     over `owK2PhaseBit3` and `owK2CoinSwap3` (using `owK2CoinSwap3_lo` on `z24[0..7]`).
   - `SubCoin61` (`K_sp = 2, kCtrl = 17, mCoin = 61`): `rW19Sub41_k2`,
     `masksSub61` (`[5527, 1115]`), `potExpectK2Sub61`.
   - `SubCoin60` (`K_sp = 3, kCtrl = 20, mCoin = 60`): `rW23Sub41_k2`,
     `masksSub60` (`[1265, 5782, 1971]`), `potExpectK2Sub60`.
-/

noncomputable section
set_option autoImplicit false
set_option exponentiation.threshold 8192

open Operator QProg Matrix Circuit Qubit PrimitiveGate
  QuantumComputation.Specs.PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring (PotExpectFn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage4Ulp (word512DualLegLo6
    v1Fin8DualLeg v2Fin8DualLeg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coulomb18K2 (ySampleK2)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Stage4 (ReflPotSliceSpec24)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DeferMux2Wp198Opt
    (Stage4ReflCoin24PotOraclePortBInPlace)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4Coul18K2 (owK2CoinSwap3
    owK2PhaseBit3 owK2CoinSwap3_lo owK2CoinSwap3_invol owK2PhaseBit3_coinSwap)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4Coul18K2 (owK2PhaseBit3_avg_coin24
    owK2ReflPotSliceSpec24 potExpectK2DualLegK17)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage25PolyMCoin (ReflPotSliceSpecN
    Stage4ReflCoinPotOraclePortBInPlace Stage4ReflCoin23PotOraclePortBInPlace)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4SubCoinSplice (splicedZ24
    subPhaseBit3 potExpectSub wrapStage4PortBSubCoin)
open scoped BigOperators

namespace QuantumComputation.Specs.PhotochemistrySolution.Instances
scoped instance : NeZero 2 := ⟨two_ne_zero⟩
scoped instance {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
end QuantumComputation.Specs.PhotochemistrySolution.Instances
open scoped QuantumComputation.Specs.PhotochemistrySolution.Instances

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage4SubCoinK2Bridge

/-- Converts a `24`-coin `ReflPotSliceSpec24` into `ReflPotSliceSpecN 24`. -/
def reflPotSliceSpecN24Of24 {pe : PotExpectFn} (s : ReflPotSliceSpec24 pe) :
    ReflPotSliceSpecN 24 pe where
  phaseBit := s.phaseBit
  coinSwap := s.coinSwap
  coinSwap_invol := s.coinSwap_invol
  phaseBit_coinSwap := s.phaseBit_coinSwap
  phaseBit_port := s.phaseBit_port
  coinSwap_port := s.coinSwap_port
  avg_coinN := s.avg_coin24

/-- Transports the expectation of `ReflPotSliceSpecN` without wrapping `phaseBit`/`coinSwap`. -/
def ReflPotSliceSpecN.congrExpect {nInner : ℕ} {pe₁ pe₂ : PotExpectFn}
    (s : ReflPotSliceSpecN nInner pe₁) (h : pe₁ = pe₂) :
    ReflPotSliceSpecN nInner pe₂ where
  phaseBit := s.phaseBit
  coinSwap := s.coinSwap
  coinSwap_invol := s.coinSwap_invol
  phaseBit_coinSwap := s.phaseBit_coinSwap
  phaseBit_port := s.phaseBit_port
  coinSwap_port := s.coinSwap_port
  avg_coinN isScreen isNN sp1 sp2 nA nB eA eB := by
    rw [← h]
    exact s.avg_coinN isScreen isNN sp1 sp2 nA nB eA eB

/-- Transports `potExpectK` on `Stage4ReflCoinPotOraclePortBInPlace` with zero `Eq.rec`. -/
def congrPotOracleExpect {nInner kCoin Wp tPotU tPotC : ℕ}
    {pe₁ pe₂ : BitAssignment kCoin → PotExpectFn}
    (o : Stage4ReflCoinPotOraclePortBInPlace nInner kCoin Wp tPotU tPotC pe₁)
    (h : pe₁ = pe₂) :
    Stage4ReflCoinPotOraclePortBInPlace nInner kCoin Wp tPotU tPotC pe₂ where
  sliceSpec γ := ReflPotSliceSpecN.congrExpect (o.sliceSpec γ) (congrFun h γ)
  pCsel := o.pCsel
  pUsel := o.pUsel
  step_and_counts := o.step_and_counts
  dynWires := o.dynWires

/-- Zero-overhead adapter from `Stage4ReflCoin24PotOraclePortBInPlace` to `nInner = 24`. -/
def ofCoin24InPlace {kCoin Wp tPotU tPotC : ℕ} {pe : BitAssignment kCoin → PotExpectFn}
    (o24 : Stage4ReflCoin24PotOraclePortBInPlace kCoin Wp tPotU tPotC pe) :
    Stage4ReflCoinPotOraclePortBInPlace 24 kCoin Wp tPotU tPotC pe where
  sliceSpec γ := reflPotSliceSpecN24Of24 (o24.sliceSpec γ)
  pCsel := o24.pCsel
  pUsel := o24.pUsel
  step_and_counts := o24.step_and_counts
  dynWires := o24.dynWires

/-- Parametric `(kCtrl ≥ 17, K_sp ≤ 6)` coin-splicing wrapper over `Stage4Coul18K2`. -/
def wrapStage4PortBK2Sub {kCtrl K_sp Wp tPotU tPotC : ℕ}
    (hk17 : 17 ≤ kCtrl) (hK6 : K_sp ≤ 6) (masks : Fin K_sp → List (Fin (kCtrl + 2)))
    (o24 : Stage4ReflCoin24PotOraclePortBInPlace 17 Wp tPotU tPotC potExpectK2DualLegK17)
    (hSlice : o24.sliceSpec =
      owK2ReflPotSliceSpec24 v1Fin8DualLeg v2Fin8DualLeg (ySampleK2 word512DualLegLo6)) :
    Stage4ReflCoinPotOraclePortBInPlace (24 - K_sp) (kCtrl + K_sp) Wp tPotU tPotC
      (potExpectSub hk17 (Nat.le_trans hK6 (by omega)) masks
        (owK2PhaseBit3 v1Fin8DualLeg v2Fin8DualLeg (ySampleK2 word512DualLegLo6))) :=
  wrapStage4PortBSubCoin
    hk17
    (Nat.le_trans hK6 (by omega))
    masks
    (owK2PhaseBit3 v1Fin8DualLeg v2Fin8DualLeg (ySampleK2 word512DualLegLo6))
    (owK2CoinSwap3 v1Fin8DualLeg v2Fin8DualLeg (ySampleK2 word512DualLegLo6))
    (owK2CoinSwap3_invol v1Fin8DualLeg v2Fin8DualLeg (ySampleK2 word512DualLegLo6))
    (owK2PhaseBit3_coinSwap v1Fin8DualLeg v2Fin8DualLeg (ySampleK2 word512DualLegLo6))
    (owK2PhaseBit3_avg_coin24 v1Fin8DualLeg v2Fin8DualLeg (ySampleK2 word512DualLegLo6))
    (fun γ17 s nn sp1 sp2 nA pB eA z24 {_} hk ↦
      owK2CoinSwap3_lo v1Fin8DualLeg v2Fin8DualLeg (ySampleK2 word512DualLegLo6)
        γ17 s nn sp1 sp2 nA pB eA z24 (by omega))
    (ofCoin24InPlace o24)
    (fun γ17 ↦ by
      change reflPotSliceSpecN24Of24 (o24.sliceSpec γ17) = _
      rw [hSlice]
      rfl)
/-! ### `SubCoin61` (`K_sp = 2, kCtrl = 17, mCoin = 61`) -/
/-! ### `SubCoin60` (`K_sp = 3, kCtrl = 20, mCoin = 60`) -/

end QuantumComputation.Specs.PhotochemistrySolution.Stage4SubCoinK2Bridge

namespace QuantumComputation.Specs.PhotochemistrySolution.SubCoin62Stage4

open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4SubCoinK2Bridge
    (congrPotOracleExpect wrapStage4PortBK2Sub)

/-- `18`-wire Stage-1 outer-coin index map into `Fin 41` for `SubCoin62` (`K_sp = 1`). -/
def sub18Sub62Idx : Fin 18 → Fin 41
  | ⟨0, _⟩ => ⟨0, by omega⟩
  | ⟨1, _⟩ => ⟨1, by omega⟩
  | ⟨2, _⟩ => ⟨2, by omega⟩
  | ⟨3, _⟩ => ⟨3, by omega⟩
  | ⟨4, _⟩ => ⟨4, by omega⟩
  | ⟨5, _⟩ => ⟨11, by omega⟩
  | ⟨6, _⟩ => ⟨12, by omega⟩
  | ⟨7, _⟩ => ⟨13, by omega⟩
  | ⟨8, _⟩ => ⟨14, by omega⟩
  | ⟨9, _⟩ => ⟨31, by omega⟩
  | ⟨10, _⟩ => ⟨32, by omega⟩
  | ⟨11, _⟩ => ⟨25, by omega⟩
  | ⟨12, _⟩ => ⟨15, by omega⟩
  | ⟨13, _⟩ => ⟨20, by omega⟩
  | ⟨14, _⟩ => ⟨26, by omega⟩
  | ⟨15, _⟩ => ⟨16, by omega⟩
  | ⟨16, _⟩ => ⟨21, by omega⟩
  | ⟨_ + 17, _⟩ => ⟨5, by omega⟩

theorem sub18Sub62Idx_inj : Function.Injective sub18Sub62Idx := fun a b h ↦
    (by decide : ∀ a b : Fin 18,
  sub18Sub62Idx a = sub18Sub62Idx b → a = b) a b h

/-- `18`-wire Stage-1 outer-coin subregister for `SubCoin62`. -/
def rW18Sub41_k2 : QRegister 18 41 := ⟨⟨sub18Sub62Idx, sub18Sub62Idx_inj⟩⟩

/-- Prefix `17` bits of an `18`-bit outer-coin assignment. -/
def take17Of18 (γ18 : BitAssignment 18) : BitAssignment 17 :=
  fun j ↦ γ18 ⟨j.val, by omega⟩

/-- `SubCoin62` GF(2) whitening mask (`7483` plus `γ18[11, 12, 13]`). -/
def otpDeltaSub62 (γ18 : BitAssignment 18) (u0 u1 : ZMod 2) : ZMod 2 :=
  γ18 ⟨11, by omega⟩ + (γ18 ⟨12, by omega⟩ + (γ18 ⟨13, by omega⟩ +
    (γ18 ⟨0, by omega⟩ + (γ18 ⟨1, by omega⟩ + (γ18 ⟨3, by omega⟩ +
      (γ18 ⟨4, by omega⟩ + (γ18 ⟨5, by omega⟩ + (γ18 ⟨8, by omega⟩ +
        (γ18 ⟨10, by omega⟩ + (u0 + (u1 + 0)))))))))))

/-- Splices `γ18[17] + otpDeltaSub62` into bit `2` of `z24`. -/
def splicedZ24Sub62 (γ18 : BitAssignment 18) (z23 : BitAssignment 23) : BitAssignment 24 :=
  fun ⟨kv, _⟩ ↦
    if _hk2 : kv < 2 then z23 ⟨kv, by omega⟩
    else if _hkEq : kv = 2 then
      γ18 ⟨17, by omega⟩ + otpDeltaSub62 γ18 (z23 ⟨0, by omega⟩) (z23 ⟨1, by omega⟩)
    else z23 ⟨kv - 1, by omega⟩

/-- Drops bit `2` of `z24` to form `z23`. -/
def unspliceZ23Of24 (z24 : BitAssignment 24) : BitAssignment 23 :=
  fun ⟨iv, _⟩ ↦
    if iv < 2 then z24 ⟨iv, by omega⟩
    else z24 ⟨iv + 1, by omega⟩

theorem unsplice_splicedZ24Sub62 (γ18 : BitAssignment 18) (z23 : BitAssignment 23) : unspliceZ23Of24
    (splicedZ24Sub62 γ18 z23) = z23 := funext fun ⟨iv, hiv⟩ ↦ by
  unfold unspliceZ23Of24 splicedZ24Sub62
  by_cases hi : iv < 2
  · simp only [hi, ↓reduceIte, ↓reduceDIte]
  · simpa only [hi, show ¬ iv + 1 < 2 by omega, show iv + 1 ≠ 2 by omega, ↓reduceIte,
        ↓reduceDIte] using congrArg z23
      (Fin.ext (Nat.add_sub_cancel iv 1))

theorem spliced_unsplice_of_eq_at2 (γ18 : BitAssignment 18) (z24 : BitAssignment 24)
    (h2 : z24 ⟨2, by omega⟩ = γ18
  ⟨17, by omega⟩ + otpDeltaSub62 γ18 (z24 ⟨0, by omega⟩) (z24 ⟨1, by omega⟩)) :
    splicedZ24Sub62 γ18 (unspliceZ23Of24 z24) = z24 := funext fun ⟨kv, hkv⟩ ↦ by
  unfold splicedZ24Sub62 unspliceZ23Of24
  dsimp only
  by_cases hk2 : kv < 2
  · simp only [hk2, ↓reduceIte, ↓reduceDIte]
  · by_cases hkEq : kv = 2
    · subst hkEq
      simpa only [show ¬ (2 : ℕ) < 2 by omega, ↓reduceDIte, show (0 : ℕ) < 2 by omega,
          show (1 : ℕ) < 2 by omega,
        ↓reduceIte] using h2.symm
    · simpa only [hk2, hkEq, show ¬ kv - 1 < 2 by omega, ↓reduceIte,
          ↓reduceDIte] using congrArg z24 (Fin.ext
        (Nat.sub_add_cancel (by omega)))

/-- `SubCoin62` `3`-port potential phase bit on `23` inner coin bits. -/
def owK2Sub62PhaseBit3 (γ18 : BitAssignment 18) (s nn : Bool) (sp1 sp2 : Fin 4)
    (nA pB eA : Fin 3 → Fin 256) (z23 : BitAssignment 23) : ZMod 2 :=
  owK2PhaseBit3 v1Fin8DualLeg v2Fin8DualLeg (ySampleK2 word512DualLegLo6)
    (take17Of18 γ18) s nn sp1 sp2 nA pB eA (splicedZ24Sub62 γ18 z23)

/-- `SubCoin62` conditional potential expectation over `23` inner coin bits. -/
def potExpectK2Sub62 (γ18 : BitAssignment 18) : PotExpectFn :=
  fun s nn sp1 sp2 nA nB eA eB ↦
    (2 ^ 23 : ℝ)⁻¹ * ∑ z23 : BitAssignment 23,
      if owK2Sub62PhaseBit3 γ18 s nn sp1 sp2 nA (if nn then nB else eB) eA z23 = 1 then
        (-1 : ℝ)
      else 1

/-- Control list for `K_sp = 1` (`SubCoin62`) matching `otpDeltaSub62`. -/
def masksSub62 : Fin 1 → List (Fin 19) :=
  fun _ ↦
    [⟨11, by omega⟩, ⟨12, by omega⟩, ⟨13, by omega⟩,
     ⟨0, by omega⟩, ⟨1, by omega⟩, ⟨3, by omega⟩,
     ⟨4, by omega⟩, ⟨5, by omega⟩, ⟨8, by omega⟩, ⟨10, by omega⟩,
     ⟨17, by omega⟩, ⟨18, by omega⟩]

theorem potExpectSub_masksSub62_eq :
    potExpectSub (kCtrl := 17) (K_sp := 1) le_rfl (by omega) masksSub62
      (owK2PhaseBit3 v1Fin8DualLeg v2Fin8DualLeg (ySampleK2 word512DualLegLo6)) =
    potExpectK2Sub62 := by
  funext γ18 s nn sp1 sp2 nA nB eA eB
  unfold potExpectSub potExpectK2Sub62 subPhaseBit3 owK2Sub62PhaseBit3
  refine congrArg ((2 ^ 23 : ℝ)⁻¹ * ·) (Finset.sum_congr rfl fun z23 _ ↦ ?_)
  have hSp : splicedZ24 (kCtrl := 17) (K_sp := 1) (by omega) masksSub62 γ18 z23 =
      splicedZ24Sub62 γ18 z23 := funext fun ⟨kv, hkv⟩ ↦ by
    unfold splicedZ24 splicedZ24Sub62
    by_cases hk2 : kv < 2
    · simp only [hk2, ↓reduceDIte]
    · by_cases hkEq : kv = 2
      · subst hkEq
        simp only [hk2, show (2 : ℕ) < 2 + 1 by omega, ↓reduceDIte]
        rfl
      · simp only [hk2, show ¬ kv < 2 + 1 by omega, hkEq, ↓reduceDIte]
  rw [hSp]
  rfl

/-- `SubCoin62` (`K_sp = 1`) Stage-4 Port-B oracle from `wrapStage4PortBK2Sub`. -/
def wstateStg4Mux2_csa180_wp198_sbMid62
    {Wp tPotU tPotC : ℕ}
    (o24 : Stage4ReflCoin24PotOraclePortBInPlace 17 Wp tPotU tPotC potExpectK2DualLegK17)
    (hSlice : o24.sliceSpec =
      owK2ReflPotSliceSpec24 v1Fin8DualLeg v2Fin8DualLeg (ySampleK2 word512DualLegLo6)) :
    Stage4ReflCoin23PotOraclePortBInPlace 18 Wp tPotU tPotC potExpectK2Sub62 :=
  congrPotOracleExpect
    (wrapStage4PortBK2Sub (kCtrl := 17) (K_sp := 1) le_rfl (by omega) masksSub62 o24 hSlice)
    potExpectSub_masksSub62_eq

end QuantumComputation.Specs.PhotochemistrySolution.SubCoin62Stage4
end
