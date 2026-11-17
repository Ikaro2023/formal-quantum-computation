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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.Mux48CtrlSafeOracleBase
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section

set_option allowUnsafeReducibility true
open scoped BigOperators
open QuantumComputation.Specs.PhotochemistrySolution.OuterW11Bridge
  QuantumComputation.Specs.PhotochemistrySolution.Stage1ZeroNEremSpec
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
  QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
  QuantumComputation.Specs.PhotochemistrySolution.ZHi30
  QuantumComputation.Specs.PhotochemistrySolution.Stage4Sh14P5
  QuantumComputation.Specs.PhotochemistrySolution.Stage5StackCerts
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec (ZeroNEremSector
    nucSpecies)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Cartesian254 (sum_a8_a10_cart254
    b11Z2OfHX cart254V23 w11NatOfCoin b2Spec b6Spec b2Spec_255 b2Spec_lt255 b6Spec_1023
    b6Spec_lt1023 b11Ext192 b11ExtInv192 b11Ext192_spec b11ExtInv192_spec ultraToPinned192)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Cartesian254 (pinnedToUltra192
    ultraToPinned192_spec pinnedToUltra192_spec foldSum_perm)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.FermatInverse (decodeUltraNuc192 phiU1
    outW wBit wPack testBit_wPack allTree allTree_zero b2_testBit_mod_pow nat_xor_eq
    decodePinnedNuc192 eeCellFermat nnCellFermat count_fermat_ee eqSec eqSec_iff foldSum_cond_const)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.FermatInverse (foldSum2_cond_and
    ultraNucCnt_eq pinnedNucCnt_eq mkFin187_of_lt nnPair_beq_false_of_ge fin47_beq_val
    foldSum_add_split foldSum_mul3)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Tier1K3708 (tier1CoinOf5
    tier1CoinOf5_digits w11NatOfCoin_tier1CoinOf5 tier1_sum_coin41_split5 tier1_sum_rev_fin
    tier1_sum_lo10_c5_u15 tier1_sum_lo8_lo10_c5_w11 tier1_cond_kin_or_idle tier1FbKin tier1EeTag)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Tier1K3708 (tier1NnTag tier1EnTag
    tier1_nat_beq_eq_false_of_ne tier1_sum_fin_blt_min tier1_sum_fin_blt_val
    tier1_sum_lo1_lo2_w11_v23 tier1_sum_h1_h2_lo1_lo2 tier1_mul_cond_eqSec tier1EeTag_eq_eeCell
    tier1_xor_bit)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Tier1K3708 (tier1_cond_snd_le
    tier1_cond_idle_zero tier1IsNucOrIdle tier1_sum_fin_blt_eqSec tier1_cond_shift tier1FbKin_eq_ax
    tier1_sum2_add4 tier1_speciesZ_eq_mSp tier1_card_filter_eq_sum_w11Nat)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ScreenFermatCore (alphaFermatCoin
    denomEEFermatCoin denomNNFermatCoinVal denomENFermatCoin pairOpenDistSq_comm_fermatCoin_u
    pairOpenDistSq_mod8_ne7_u pairOpenDistSq_lt_189_u pairOpenDistSq_lagrange_u bin_range_ultra
    boxOkUltra_of_lagrange)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ScreenFermatCore (fin8Bin_of_ge48_ultra)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ParametricTelescope (rEEScaledGen
    rNNScaledGen rENScaledGen)
set_option autoImplicit false
set_option exponentiation.threshold 256
section
namespace QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc
set_option maxRecDepth 4096
open QuantumComputation.Specs
  PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.ScreenFermatCore
/-- `256`-slot Gray-code `.kinNuc` sub-table `(s8, ax) ↦ (sec, thr15)` for the `p = 155` regime. -/
def tier1WalkKinNucS8 (s8 : ℕ) (ax : Fin 3) : ZeroNEremSector × ℕ :=
  let z := (s8 / 16) % 16; let s0 := s8 % 2; let s1 := (s8 / 2) % 2; let s2 := (s8 / 4) % 2;
  let s3 := (s8 / 8) % 2; let na10 := 2 * s1 + Nat.xor s0 s1;
  let naH16 := cond (s3 == 0) (24 + 4 * s2 + na10) (32 + 4 * s2 + na10);
  let naH4 := cond ((s1 == 1) && (s0 == 0)) 23 (40 + na10)
  cond (Nat.blt z 10) (.kin (mkFin234 naH16) ax, 32768)
    (cond (Nat.blt z 12)
      (let u5 := 4 * (z % 2) + 2 * s3 + s2
       cond (Nat.blt u5 5) (.kin (mkFin234 (4 * u5 + na10)) ax, 29235)
         (cond (u5 == 5)
           (cond ((s1 == 1) && (s0 == 0))
             (.kin (mkFin234 43) ax, 25053)
             (.kin (mkFin234 (20 + na10)) ax, 29235))
           (cond (u5 == 6) (.idle, 0)
             (cond ((s1 == 1) && (s0 == 0)) (.idle, 0)
               (cond ((s1 == 1) && (s0 == 1))
                 (.kin (mkFin234 46) ax, 21933)
                 (.kin (mkFin234 (44 + na10)) ax, 25053))))))
      (cond (z == 15) (.kin (mkFin234 naH16) ax, 20509)
        (cond (Nat.blt z 14 || (s3 == 0)) (.kin (mkFin234 naH4) ax, 32768)
          (cond (s2 == 0) (.kin (mkFin234 naH4) ax, 20509) (.idle, 0)))))

/-- `1024`-slice `.kinNuc` table on `hi10 < 1024` (`isX = true`) for the `p = 155` regime. -/
def tier1WalkKinNucBlk (hi10 : ℕ) : ZeroNEremSector × ℕ :=
  cond (Nat.ble 768 hi10) (.idle, 0)
    (tier1WalkKinNucS8 (hi10 % 256) (mkFin3 (hi10 / 256)))

/--
Factored interior tile decoder for the `p = 155` regime (`w_ke = 639,327,744`, `1,592-T` `Sub4EN` ).
-/
def tier1WalkIntCell (u1 h1 h2 q5 q31 lo1 lo2 w11 : ℕ) : ZeroNEremSector :=
  let fbKin := ZeroNEremSector.kin (mkFin234 (47 + u1)) (mkFin3 h1);
  let kinAx0 := ZeroNEremSector.kin (mkFin234 (47 + u1)) (mkFin3 0);
  let d1 := decodeUltraNuc192 (64 * h1 + lo1); let d2 := decodeUltraNuc192 (64 * h2 + lo2);
  let z2 := b11Z2OfHX h2 lo2; let v23 := cart254V23 lo1 lo2 w11
  cond (Nat.blt q31 16 || (Nat.beq q31 24 && Nat.beq q5 4) ||
        (Nat.beq q31 25 && Nat.beq q5 4 && Nat.blt w11 1452))
    (cond (d1.1 && d2.1 && Bool.not (Nat.beq u1 z2))
      (let cE := Nat.blt z2 u1
       .ee d1.2 (mkFin187 (cond cE z2 u1)) (mkFin187 (cond cE u1 z2)))
      fbKin)
    (let cN := Nat.blt d2.2.val d1.2.val
     cond ((Nat.ble 16 q31 && Nat.blt q31 24) ||
           (Nat.beq q31 26 && Nat.beq q5 4 && Nat.blt w11 1750))
       (cond (d1.1 && d2.1 && Bool.not (Nat.beq d1.2.val d2.2.val))
         (.nn (cond cN d2.2 d1.2) (cond cN d1.2 d2.2) (mkFin187 u1))
         fbKin)
       (let enHit := Nat.ble 28 q31 ||
          (Nat.beq q31 27 && Nat.beq q5 4 &&
            (Nat.blt lo2 56 || (Nat.blt lo2 60 && Nat.blt w11 1351)))
        cond enHit
          (cond d1.1 (.en d1.2 (mkFin187 u1)) fbKin)
          (cond (Nat.beq q31 27 && (Nat.beq q5 2 || Nat.beq q5 3) && Nat.beq h2 0)
            kinAx0
            (cond (Nat.beq q31 26 && Nat.beq q5 3)
              (cond (Nat.beq h1 1 && Nat.beq h2 0 && Nat.blt v23 3431948)
                kinAx0
                (cond (Nat.beq h1 2 && Nat.beq h2 0 && Nat.blt v23 2779112)
                  kinAx0
                  (cond (Nat.beq h1 2 && Nat.beq h2 2 && Nat.blt v23 1824216)
                    .idle fbKin)))
              fbKin))))

/--
`p = 155` (`M = 5,578`, `w_ke = 639,327,744` ) coin decoder.
-/
def decodeTier1WalkCoin (c : Fin (2 ^ 41)) : ZeroNEremSector :=
  let c5 := c.val % 32; let y20 := (c.val / 32) % 1048576; let x16 := c.val / 33554432;
  let lo8 := x16 % 256; let hi8 := x16 / 256; let lo10 := y20 % 1024; let hi10 := y20 / 1024;
  let a8 := cond (hi8 == 255) (255 - lo8) hi8; let b8 := cond (hi8 == 255) 0 lo8;
  let px := b2Spec a8; let py := b6Spec hi10
  cond px.2.2.2
    (let p := tier1WalkKinNucBlk hi10
     let u15 := (lo10 % 64) + 64 * c5 + 2048 * (lo10 / 64)
     cond (Nat.blt u15 p.2) p.1 .idle)
    (cond py.2.2.2 .idle
      (let u1 := phiU1 py.1 px.1
       cond (hi8 == 255)
         (.kin (mkFin234 (47 + u1)) (mkFin3 px.2.1))
         (let w11 := c5 + 32 * (lo10 / 64) + 512 * (b8 / 64)
          tier1WalkIntCell u1 px.2.1 py.2.1 px.2.2.1 py.2.2.1 (b8 % 64) (lo10 % 64) w11)))
end QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc

end

noncomputable section
set_option maxRecDepth 16384
namespace QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc
open PhotochemistrySolution.Stage1AsymRevEngine PhotochemistrySolution.Tier1K3708
open _root_.QuantumComputation.Specs.PhotochemistrySolution.FermatInverse (oddBits_and_xor bitAt
    bitAt_eq_testBit)
theorem mr_revT1_wBit_xor (e a b : ℕ) : wBit e (Nat.xor a b) = xor (wBit e a) (wBit e b) := by
  unfold wBit; rw [nat_xor_eq]; exact oddBits_and_xor e a b 376
theorem mr_revT1_wBit_outW (e : ℕ) (ms : List ℕ) (q : ℕ) : wBit e (outW ms q) =
    (wPack e ms).testBit q := (testBit_wPack e ms q).symm
theorem mr_wPack_cons_zero_t1 (e m : ℕ) (ms : List ℕ) : (wPack e (m :: ms)).testBit 0 = wBit e m :=
    testBit_wPack e (m :: ms) 0
theorem mr_wPack_cons_succ_t1 (e m : ℕ) (ms : List ℕ) (k : ℕ) : (wPack e (m :: ms)).testBit (k +
    1) = (wPack e ms).testBit k := by rw [testBit_wPack, testBit_wPack]; rfl

private def mr_strictNatP {α : Type} (v : ℕ) (k : ℕ → α) : α :=
  match v + 1 with
  | 0 => k 0
  | n + 1 => k n
private theorem mr_strictNatP_eq {α : Type} (v : ℕ) (k : ℕ → α) : mr_strictNatP v k =
    k v := by
  cases v <;> rfl
private theorem mr_allTree_congr_all :
    ∀ (fuel base len : ℕ) {p q : ℕ → Bool},
      (∀ r, p r = q r) → allTree fuel base len p = allTree fuel base len q
  | 0, _, _, _, _, _ => rfl
  | _ + 1, _, 0, _, _, _ => rfl
  | _ + 1, base, 1, _, _, h => h base
  | fuel + 1, base, len + 2, _, _, h => by
      dsimp only [allTree];
      rw [mr_allTree_congr_all fuel base ((len + 2) / 2) h,
          mr_allTree_congr_all fuel (base + (len + 2) / 2) (len + 2 - (len + 2) / 2) h]
private theorem mr_at_dbl (k : ℕ) {f : ℕ} {p : ℕ → Bool}
    (h : ∀ b, allTree f b (k + 1) p = true) (b : ℕ) : allTree (f + 1) b (2 * k + 2) p = true := by
  dsimp only [allTree]
  rw [show (2 * k + 2) / 2 = k + 1 by omega, show 2 * k + 2 - (k + 1) = k + 1 by omega, h, h]; rfl
private theorem mr_at1024 {p : ℕ → Bool} (h : ∀ r, p r = true) (b : ℕ) : allTree 11 b 1024 p =
    true :=
  mr_at_dbl 511 (mr_at_dbl 255 (mr_at_dbl 127 (mr_at_dbl 63 (mr_at_dbl 31
    (mr_at_dbl 15 (mr_at_dbl 7 (mr_at_dbl 3 (mr_at_dbl 1 (mr_at_dbl 0 (f :=
        1) h))))))))) b
private theorem mr_at2048 {p : ℕ → Bool} (h : ∀ r, p r = true) : allTree 12 0 2048 p = true :=
    mr_at_dbl 1023 (mr_at1024 h) 0
private theorem mr_testBit_two_mul_zero (x : ℕ) : (2 * x).testBit 0 = false := by
  rw [← b2_testBit_mod_pow (2 * x) 1 0 (by omega), show (2 * x) % 2 ^ 1 = 0 by omega]
  rfl

theorem mr_revT1_cert_f20_props :
    allTree 12 0 2048 (fun r ↦
      Bool.or (Bool.not (careTier1_20 r))
        (let s := specTier1_20 r
         let d0 := s.testBit 0; let d1 := s.testBit 1; let d2 := s.testBit 2;
         let pot := xor (xor d0 d1) d2;
         let anyIn :=
             Bool.or (bitAt r 0) (Bool.or (bitAt r 1) (Bool.or (bitAt r 2) (Bool.or (bitAt r 3)
             (Bool.or (bitAt r 4) (bitAt r 5)))))
         Bool.and (Nat.ble (cond d0 1 0 + cond d1 1 0 + cond d2 1 0) 1)
           (Bool.and (Bool.or (Bool.not d0) pot)
             (Bool.and (Bool.or (Bool.not d1) pot)
               (Bool.or (Bool.not pot) anyIn))))) = true := by
  rw [mr_allTree_congr_all 12 0 2048 (q := fun r ↦ cond (careTier1_20 r)
      (mr_strictNatP (specTier1_20 r)
      fun s ↦
          Bool.and (Nat.ble (cond (bitAt s 0) 1 0 + cond (bitAt s 1) 1 0 + cond (bitAt s 2) 1 0) 1)
        (Bool.and (Bool.or (Bool.not (bitAt s 0)) (xor (xor (bitAt s 0) (bitAt s 1)) (bitAt s 2)))
          (Bool.and (Bool.or (Bool.not (bitAt s 1)) (xor (xor (bitAt s 0) (bitAt s 1)) (bitAt s 2)))
            (Bool.or (Bool.not (xor (xor (bitAt s 0) (bitAt s 1)) (bitAt s 2)))
              (Bool.or (bitAt r 0) (Bool.or (bitAt r 1) (Bool.or (bitAt r 2)
                (Bool.or (bitAt r 3) (Bool.or (bitAt r 4) (bitAt r 5)))))))))) true)
    fun r ↦
        by cases careTier1_20 r <;> simp only [Bool.not_false, Bool.not_true, Bool.true_or,
             Bool.false_or,
      cond, mr_strictNatP_eq, bitAt_eq_testBit]]
  decide +kernel

theorem mr_revT1_cert_f22_sw : allTree 12 0 2048 (fun r ↦
    Bool.or (Bool.not ((specTier1_22 r).testBit 0)) (bitAt r 1)) = true := by
  exact mr_at2048 fun r ↦ by
    cases h1 : bitAt r 1
    · have hs : specTier1_22 r = 2 * cond (bitAt r 0) ((r / 8) % 16) 0 := by
        dsimp only [specTier1_22]; rw [h1]; (cases bitAt r 0 <;> simp only [Bool.false_and, cond]);
        try omega
      rw [hs, mr_testBit_two_mul_zero]; rfl
    · exact Bool.or_true _
theorem mr_revT1_cert_f24_sw : allTree 12 0 2048 (fun r ↦
    Bool.or (Bool.not ((specTier1_24 r).testBit 0)) (bitAt r 1)) = true := by
  exact mr_at2048 fun r ↦ by
    cases h1 : bitAt r 1
    · rw [show specTier1_24 r = 2 * (cond (bitAt r 0) ((r / 8) % 4) 0 + 16 * cond (bitAt r 0)
          ((r / 128) % 4) 0) by
          dsimp only [specTier1_24]; rw [h1]; (cases bitAt r 0 <;> simp only [Bool.false_and,
              cond]); omega,
        mr_testBit_two_mul_zero]; rfl
    · exact Bool.or_true _
theorem mr_listXor_singleton_t1 (f : ℕ → Bool) (u : ℕ) : listXorBool f [u] = f u :=
    Bool.xor_false (f u)
theorem mr_listXor_two_t1 (f : ℕ → Bool) (u v : ℕ) : listXorBool f [u, v] = xor (f u) (f v) :=
    congrArg (xor (f u)) (Bool.xor_false (f v))

theorem mr_xor_cancel_left_t1 (p k : Bool) : xor (xor p k) p = k := by cases p <;> cases k <;> rfl
theorem mr_evalBilinear_two_b0_t1 (f : ℕ → Bool) (a1 b1 a2 b2 : List ℕ) :
    evalBilinearBool f [(a1, b1), (a2, b2)] = xor (Bool.and (listXorBool f a1) (listXorBool f b1))
    (Bool.and (listXorBool f a2) (listXorBool f b2)) := congrArg (xor _) (Bool.xor_false _)
theorem mr_evalBilinear_two_t1 (f : ℕ → Bool) (a1 b1 a2 b2 : List ℕ) : evalBilinearBool f [(a1, b1),
    (a2, b2)] = xor (Bool.and (listXorBool f a1) (listXorBool f b1)) (Bool.and (listXorBool f a2)
    (listXorBool f b2)) := by dsimp only [evalBilinearBool]; rw [Bool.xor_false]
theorem mr_evalBilinear_three_t1 (f : ℕ → Bool) (a1 b1 a2 b2 a3 b3 : List ℕ) :
    evalBilinearBool f [(a1, b1), (a2, b2), (a3, b3)] = xor (xor (Bool.and (listXorBool f a1)
    (listXorBool f b1)) (Bool.and (listXorBool f a2) (listXorBool f b2)))
    (Bool.and (listXorBool f a3) (listXorBool f b3))
    := by dsimp only [evalBilinearBool]; rw [Bool.xor_false, ← Bool.xor_assoc]
private theorem mr_xor5 (a b c d e : Bool) : xor a (xor b (xor c (xor d e))) =
    xor (xor (xor a b) (xor d e)) c := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl
theorem mr_evalBilinear_five_t1 (f : ℕ → Bool) (a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 : List ℕ) :
    evalBilinearBool f [(a1, b1), (a2, b2), (a3, b3), (a4, b4), (a5, b5)] =
    xor (xor (xor (Bool.and (listXorBool f a1) (listXorBool f b1)) (Bool.and (listXorBool f a2)
    (listXorBool f b2))) (xor (Bool.and (listXorBool f a4) (listXorBool f b4))
    (Bool.and (listXorBool f a5) (listXorBool f b5)))) (Bool.and (listXorBool f a3)
    (listXorBool f b3))
    := by dsimp only [evalBilinearBool]; rw [Bool.xor_false]; exact mr_xor5 _ _ _ _ _

theorem mr_xor_mid_swap_t1 (x y z : Bool) : xor (xor x y) z = xor (xor x z) y := by
  cases x <;> cases y <;> cases z <;> rfl
theorem mr_ble_false_of_gt_t1 {a b : ℕ} (h : b < a) : Nat.ble a b = false :=
    Bool.eq_false_iff.mpr fun hab ↦ Nat.not_le_of_gt h (Nat.le_of_ble_eq_true hab)
private abbrev mr_bf := @mr_ble_false_of_gt_t1
theorem mr_mid32OutIdx_lt8_t1 (j : Fin 32) (h : j.val < 8) : mid32OutIdx j = 24 + j.val := by
  dsimp only [mid32OutIdx]; rw [Nat.ble_eq_true_of_le (by omega)]; simp only [↓reduceIte]
theorem mr_mid32OutIdx_8_16_t1 (j : Fin 32) (h1 : 8 ≤ j.val) (h2 : j.val < 16) : mid32OutIdx j =
    16 + (j.val - 8) := by
  dsimp only [mid32OutIdx]; rw [mr_bf (by omega), Nat.ble_eq_true_of_le (by omega)]
  simp only [Bool.false_eq_true, ↓reduceIte]; omega
theorem mr_mid32OutIdx_16_22_t1 (j : Fin 32) (h1 : 16 ≤ j.val) (h2 : j.val < 22) : mid32OutIdx j =
    8 + (j.val - 16) := by
  dsimp only [mid32OutIdx];
  rw [mr_bf (by omega), mr_bf (by omega), Nat.ble_eq_true_of_le (by omega)]
  simp only [Bool.false_eq_true, ↓reduceIte]; omega
theorem mr_mid32OutIdx_22_28_t1 (j : Fin 32) (h1 : 22 ≤ j.val) (h2 : j.val < 28) : mid32OutIdx j =
    2 + (j.val - 22) := by
  dsimp only [mid32OutIdx];
  rw [mr_bf (by omega), mr_bf (by omega), mr_bf (by omega),
      Nat.ble_eq_true_of_le (by omega)]
  simp only [Bool.false_eq_true, ↓reduceIte]; omega
theorem mr_mid32OutIdx_ge28_t1 (j : Fin 32) (h1 : 28 ≤ j.val) : mid32OutIdx j = 8 + j.val := by
  dsimp only [mid32OutIdx];
  rw [mr_bf (by omega), mr_bf (by omega), mr_bf (by omega), mr_bf (by omega)]
  simp only [Bool.false_eq_true, ↓reduceIte]
private theorem mr_tb_lo {x y w i : ℕ} (hx : x < 2 ^ w)
    (hi : i < w) : (x + 2 ^ w * y).testBit i =
    x.testBit i
    := by rw [← b2_testBit_mod_pow _ w i hi, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
private theorem mr_tb_hi {x y w k : ℕ} (hx : x < 2 ^ w) : (x + 2 ^ w * y).testBit (w + k) =
    y.testBit k := by
  rw [Nat.add_comm w k, ← Nat.testBit_div_two_pow,
      Nat.add_mul_div_left x y (by positivity), Nat.div_eq_of_lt hx, Nat.zero_add]
private theorem mr_tb_step {x y w m k : ℕ} (hx : x < 2 ^ w)
    (hm : m = w + k) : (x + 2 ^ w * y).testBit m = y.testBit k := hm ▸ mr_tb_hi hx
private theorem mr_tb_cond (b : Bool) (x y i : ℕ) :
    (cond b x y).testBit i = cond b (x.testBit i) (y.testBit i) := by cases b <;> rfl
private theorem mr_cond_lt {b : Bool} {x y m : ℕ} (hx : x < m) (hy : y < m) : cond b x y <
    m := by
  cases b <;> assumption
private theorem mr_tb0_sw (b : Bool) (z : ℕ) : (cond b 1 0 + 2 ^ 1 * z).testBit 0 = b := by
  rw [mr_tb_lo (mr_cond_lt (by omega) (by omega)) (by omega)]; cases b <;> rfl
private theorem mr_mux_lt {s p : Bool} {a b w : ℕ} (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    cond s b (cond p a 0) < 2 ^ w := mr_cond_lt hb (mr_cond_lt ha (by positivity))
private theorem mr_sub_lt (r d m w : ℕ) (hm : m = 2 ^ w) : (r / d) % m < 2 ^ w := by
  subst hm; exact Nat.mod_lt _ (by positivity)
private theorem mr_tb_sub (r d m s w i : ℕ) (hd : d = 2 ^ s) (hm : m = 2 ^ w)
    (hi : i < w) : ((r / d) % m).testBit i = bitAt r (s + i)
    := by subst hd hm; rw [b2_testBit_mod_pow _ w i hi, Nat.testBit_div_two_pow, Nat.add_comm i s,
            ← bitAt_eq_testBit]
private theorem mr_pack144 (a b c : ℕ) : a + 2 * b + 32 * c = a + 2 ^ 1 * (b + 2 ^ 4 * c) := by
  omega
private theorem mr_pack12222 (a b c d e : ℕ) :
    a + 2 * b + 8 * c + 32 * d + 128 * e =
      a + 2 ^ 1 * (b + 2 ^ 2 * (c + 2 ^ 2 * (d + 2 ^ 2 * e))) := by omega
private theorem mr_muxOk {p d s u z : Bool} (h1 : Bool.or (Bool.not d) p = true)
    (h2 : Bool.or (Bool.not s) d = true) : Bool.and (BEq.beq (xor (Bool.and d z)
    (Bool.and s (xor u z))) (cond d (cond s u z) false))
    (BEq.beq (xor (Bool.and p u) (Bool.and d z)) (xor (cond s z (cond p u false))
    (cond d (cond s u z) false))) = true := by
  cases p <;> cases d <;> cases s <;> cases u <;> cases z <;>
    first | rfl | exact Bool.noConfusion h1 | exact Bool.noConfusion h2
/-- Per-bit First-pass bilinear check for `F22` (`i < 4`). -/
def mr_f22MidBitOkT1 (r i : ℕ) : Bool :=
  let s := specTier1_22 r; let u := bitAt r (3 + i); let z := bitAt r (7 + i)
  Bool.and (BEq.beq (xor (Bool.and (bitAt r 1) z) (Bool.and (s.testBit 0) (xor u z)))
      (s.testBit (5 + i)))
    (BEq.beq (xor (Bool.and (bitAt r 0) u) (Bool.and (bitAt r 1) z)) (xor (s.testBit (1 + i))
        (s.testBit (5 + i))))
private theorem mr_f22_ok {r i : ℕ} (hc : careTier1_22 r = true)
    (hi : i < 4) : mr_f22MidBitOkT1 r i = true := by
  dsimp only [mr_f22MidBitOkT1, specTier1_22]; rw [mr_pack144]
  let sw := Bool.and (bitAt r 1) (Bool.not (bitAt r 2))
  have h0 : cond sw 1 0 < 2 ^ 1 := mr_cond_lt (by omega) (by omega)
  have he1 :=
      mr_mux_lt (s := sw) (p := bitAt r 0) (mr_sub_lt r 8 16 4 rfl)
      (mr_sub_lt r 128 16 4 rfl)
  rw [mr_tb0_sw, mr_tb_hi h0, mr_tb_step h0 (show 5 + i = 1 + (4 + i) by omega),
      mr_tb_lo he1 hi, mr_tb_hi he1]
  simp only [mr_tb_cond, Nat.zero_testBit, mr_tb_sub r 8 16 3 4 i rfl rfl hi,
      mr_tb_sub r 128 16 7 4 i rfl rfl hi]
  exact mr_muxOk hc (by cases bitAt r 1 <;> cases bitAt r 2 <;> rfl)
theorem mr_revT1_cert_mid_f22 : allTree 12 0 2048 (fun r ↦ Bool.or (Bool.not (careTier1_22 r))
    (Bool.and (BEq.beq ((specTier1_22 r).testBit 0) (Bool.and (bitAt r 1) (Bool.not (bitAt r 2))))
    (Bool.and (mr_f22MidBitOkT1 r 0) (Bool.and (mr_f22MidBitOkT1 r 1)
    (Bool.and (mr_f22MidBitOkT1 r 2) (mr_f22MidBitOkT1 r 3)))))) = true :=
  mr_at2048 fun r ↦ by
    cases hc : careTier1_22 r
    · rfl
    · rw [mr_f22_ok hc (by omega), mr_f22_ok hc (by omega), mr_f22_ok hc (by omega),
          mr_f22_ok hc (by omega)]
      dsimp only [specTier1_22]; rw [mr_pack144, mr_tb0_sw]
      simp only [Bool.not_true, Bool.false_or, Bool.and_true, beq_self_eq_true]
/-- Per-bit First-pass bilinear check for `F23` (`d < 4`). -/
def mr_f23MidBitOkT1 (r d : ℕ) : Bool :=
  let s := specTier1_23 r; let u := bitAt r (3 + d); let z := bitAt r (7 + d)
  Bool.and (BEq.beq (xor (Bool.and (bitAt r 1) z) (Bool.and (bitAt r 2) (xor u z)))
      (s.testBit (4 + d)))
    (BEq.beq (xor (Bool.and (bitAt r 0) u) (Bool.and (bitAt r 1) z)) (xor (s.testBit d)
        (s.testBit (4 + d))))
private theorem mr_f23_ok {r d : ℕ} (hc : careTier1_23 r = true)
    (hd : d < 4) : mr_f23MidBitOkT1 r d = true := by
  dsimp only [mr_f23MidBitOkT1, specTier1_23]
  have he1 := mr_mux_lt (s := bitAt r 2) (p := bitAt r 0)
    (mr_sub_lt r 8 16 4 rfl) (mr_sub_lt r 128 16 4 rfl)
  rw [show ∀ a b, a + 16 * b = a + 2 ^ 4 * b from fun _ _ ↦ rfl,
    mr_tb_lo he1 hd, mr_tb_hi he1]
  simp only [mr_tb_cond, Nat.zero_testBit,
    mr_tb_sub r 8 16 3 4 d rfl rfl hd, mr_tb_sub r 128 16 7 4 d rfl rfl hd]
  exact mr_muxOk (Bool.and_eq_true_iff.mp hc).1 (Bool.and_eq_true_iff.mp hc).2
theorem mr_revT1_cert_mid_f23 : allTree 12 0 2048 (fun r ↦ Bool.or (Bool.not (careTier1_23 r))
    (Bool.and (mr_f23MidBitOkT1 r 0) (Bool.and (mr_f23MidBitOkT1 r 1)
    (Bool.and (mr_f23MidBitOkT1 r 2) (mr_f23MidBitOkT1 r 3))))) = true :=
  mr_at2048 fun r ↦ by
    cases hc : careTier1_23 r
    · rfl
    · rw [mr_f23_ok hc (by omega), mr_f23_ok hc (by omega), mr_f23_ok hc (by omega),
          mr_f23_ok hc (by omega)]; rfl
/-- Per-bit First-pass bilinear check for `F24` (`i < 2`). -/
def mr_f24MidBitOkT1 (r i : ℕ) : Bool :=
  let s := specTier1_24 r; let sw := s.testBit 0
  let a := bitAt r (3 + i); let b := bitAt r (5 + i); let s1 := bitAt r (7 + i);
  let s2 := bitAt r (9 + i)
  Bool.and (BEq.beq (xor (Bool.and (bitAt r 1) b) (Bool.and sw (xor a b))) (s.testBit (3 + i)))
    (Bool.and (BEq.beq (xor (Bool.and (bitAt r 0) a) (Bool.and (bitAt r 1) b))
        (xor (s.testBit (1 + i)) (s.testBit (3 + i))))
      (Bool.and (BEq.beq (xor (Bool.and (bitAt r 0) s1) (Bool.and sw (xor s1 s2)))
          (s.testBit (5 + i)))
        (BEq.beq (xor (Bool.and (bitAt r 1) s2) (Bool.and sw (xor s1 s2))) (s.testBit (7 + i)))))

private theorem mr_f24_ok {r i : ℕ} (hc : careTier1_24 r = true)
    (hi : i < 2) : mr_f24MidBitOkT1 r i = true := by
  dsimp only [mr_f24MidBitOkT1, specTier1_24]; rw [mr_pack12222]
  let sw := Bool.and (bitAt r 1) (Bool.not (bitAt r 2))
  have h0 : cond sw 1 0 < 2 ^ 1 := mr_cond_lt (by omega) (by omega)
  have hn1 :=
      mr_mux_lt (s := sw) (p := bitAt r 0) (mr_sub_lt r 8 4 2 rfl)
      (mr_sub_lt r 32 4 2 rfl)
  have hn2 :=
      mr_cond_lt (b := bitAt r 1) (y := 0) (mr_cond_lt (b := sw) (mr_sub_lt r 8 4 2 rfl)
      (mr_sub_lt r 32 4 2 rfl)) (by positivity)
  have hsp1 :=
      mr_mux_lt (s := sw) (p := bitAt r 0) (mr_sub_lt r 128 4 2 rfl)
      (mr_sub_lt r 512 4 2 rfl)
  rw [mr_tb0_sw, mr_tb_hi h0, mr_tb_lo hn1 hi,
      mr_tb_step h0 (show 3 + i = 1 + (2 + i) by omega), mr_tb_hi hn1, mr_tb_lo hn2 hi,
      mr_tb_step h0 (show 5 + i = 1 + (2 + (2 + i)) by omega), mr_tb_hi hn1,
          mr_tb_hi hn2, mr_tb_lo hsp1 hi,
      mr_tb_step h0 (show 7 + i = 1 + (2 + (2 + (2 + i))) by omega), mr_tb_hi hn1,
          mr_tb_hi hn2, mr_tb_hi hsp1]
  simp only [mr_tb_cond, Nat.zero_testBit, mr_tb_sub r 8 4 3 2 i rfl rfl hi,
      mr_tb_sub r 32 4 5 2 i rfl rfl hi, mr_tb_sub r 128 4 7 2 i rfl rfl hi,
      mr_tb_sub r 512 4 9 2 i rfl rfl hi]
  have hmn := mr_muxOk (s := sw) (u := bitAt r (3 + i)) (z := bitAt r (5 + i)) hc (by
    dsimp only [sw]
    cases bitAt r 1 <;> cases bitAt r 2 <;> rfl)
  have hc' : Bool.or (Bool.not (bitAt r 1)) (bitAt r 0) = true := hc
  exact Bool.and_eq_true_iff.mpr ⟨(Bool.and_eq_true_iff.mp hmn).1, Bool.and_eq_true_iff.mpr
    ⟨(Bool.and_eq_true_iff.mp hmn).2, by
      dsimp only [sw]
      generalize bitAt r 0 = p, bitAt r 1 = d, bitAt r 2 = r2,
        bitAt r (7 + i) = s1, bitAt r (9 + i) = s2 at hc' ⊢
      cases p <;> cases d <;> cases r2 <;> cases s1 <;> cases s2 <;>
        first | rfl | exact Bool.noConfusion hc'⟩⟩
theorem mr_revT1_cert_mid_f24 : allTree 12 0 2048 (fun r ↦ Bool.or (Bool.not (careTier1_24 r))
    (Bool.and (BEq.beq ((specTier1_24 r).testBit 0) (Bool.and (bitAt r 1) (Bool.not (bitAt r 2))))
    (Bool.and (mr_f24MidBitOkT1 r 0) (mr_f24MidBitOkT1 r 1)))) = true :=
  mr_at2048 fun r ↦ by
    cases hc : careTier1_24 r
    · rfl
    · rw [mr_f24_ok hc (by omega), mr_f24_ok hc (by omega)]
      dsimp only [specTier1_24]; rw [mr_pack12222, mr_tb0_sw]
      simp only [Bool.not_true, Bool.false_or, Bool.and_true, beq_self_eq_true]
/-- Per-bit First-pass bilinear check for `F25` (`d < 4`). -/
def mr_f25MidBitOkT1 (r d : ℕ) : Bool :=
  let s := specTier1_23 r; let a := bitAt r (3 + d); let b := bitAt r (7 + d)
  Bool.and (BEq.beq (xor (Bool.and (bitAt r 1) b) (Bool.and (bitAt r 2) (xor a b)))
      (s.testBit (4 + d)))
    (BEq.beq (xor (Bool.and (bitAt r 0) a) (Bool.and (bitAt r 1) b)) (xor (s.testBit d)
        (s.testBit (4 + d))))
theorem mr_revT1_cert_mid_f25 : allTree 12 0 2048 (fun r ↦ Bool.or (Bool.not (careTier1_23 r))
    (Bool.and (mr_f25MidBitOkT1 r 0) (Bool.and (mr_f25MidBitOkT1 r 1)
    (Bool.and (mr_f25MidBitOkT1 r 2) (mr_f25MidBitOkT1 r 3))))) = true := mr_revT1_cert_mid_f23
end QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc
set_option maxRecDepth 4096
set_option exponentiation.threshold 8192
open scoped Matrix Matrix.Norms.L2Operator
open Real Operator QProg DynamicCircuit Matrix QuantumComputation.Specs PhotochemistrySolution
  PhotochemistrySolution.SelectApprox PhotochemistrySolution.QubitizationWalkSem
  PhotochemistrySolution.ClusterPotSlice
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.KinNormSlice PhotochemistrySolution.ZeroNEremSpec
  PhotochemistrySolution.TelescopeSlice PhotochemistrySolution.BlockApprox
  PhotochemistrySolution.GenWeightsSelect PhotochemistrySolution.ScreenFermatCore
open PhotochemistrySolution.ParametricTelescope
def wEESpeciesTier1Walk (s : Fin 4) : ℕ := 2 * speciesZ s * 167340
/-- Per-item 41-bit coin slot counts on `.nn` (`0` on vacuous `(O, O)`) for the `p = 155` regime. -/
def wNNSpeciesTier1Walk (s1 s2 : Fin 4) : ℕ :=
  if s1.val = 3 ∧ s2.val = 3 then 0 else speciesZ s1 * speciesZ s2 * 167340
/--
Per-item 41-bit coin slot counts on `.en` (`6,258,516 = 3 * 2,086,172` per proton,
uniform `gain = 10` across all four species) for the `p = 155` regime.
-/
def wENSpeciesTier1Walk (s : Fin 4) : ℕ := speciesZ s * 6258516
/-- Electron kinetic per-axis 41-bit coin slot count (`561` axes, `1,592-T` full-regime variant). -/
abbrev wKinElecTier1Walk : ℕ := 639327744
/--
Nuclear kinetic per-axis 41-bit coin slot counts (`0=H, 1=C, 2=N, 3=O`) for the `p = 155` regime.
-/
def wKinNucSpeciesTier1Walk : Fin 4 → ℕ
  | 0 => 348189
  | 1 => 29235
  | 2 => 25053
  | 3 => 21933
/--
Unified per-particle 41-bit kinetic coin slot function on `Particle_frozen` for the `p = 155`
regime.
-/
def wKinTier1Walk (i : Particle_frozen) : ℕ :=
  if h : i.val < 47 then wKinNucSpeciesTier1Walk (nucSpecies ⟨i.val, h⟩) else wKinElecTier1Walk
/--
Residual `.idle` 41-bit coin slots (`2^41 - totPot - totKin`) for the `p = 155` regime (`w_ke =
639,327,744`).
-/
abbrev totalSlotsIdleTier1Walk : ℕ := 2498933873
/-- Canonical `p = 155` (`w_ke = 639,327,744`) 41-bit coin multiplicity contract. -/
abbrev ValidTier1WalkCoin (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) : Prop :=
    ValidGenZeroNEremCoin wEESpeciesTier1Walk wNNSpeciesTier1Walk wENSpeciesTier1Walk wKinTier1Walk
    totalSlotsIdleTier1Walk decodeCoin
theorem wEESpeciesTier1Walk_eq_factor (s : Fin 4) : wEESpeciesTier1Walk s = (2 * mSpCart254 s) *
    167340 := by
  fin_cases s <;> rfl
theorem wNNSpeciesTier1Walk_eq_factor (s1 s2 : Fin 4) (h33 : ¬(s1.val = 3 ∧ s2.val = 3)) :
    wNNSpeciesTier1Walk s1 s2 = (mSpCart254 s1 * mSpCart254 s2) * 167340 := by
  fin_cases s1 <;> fin_cases s2 <;> simp_all [wNNSpeciesTier1Walk, speciesZ, mSpCart254]
theorem wENSpeciesTier1Walk_eq_factor (s : Fin 4) : wENSpeciesTier1Walk s = mSpCart254 s *
    6258516 := by
  fin_cases s <;> rfl
/-- Stage-4 (`p = 155`) `.ee` denominator `denomEEFermatCoin * (100000 / 100155)`. -/
def denomEETier1Walk : ℝ := denomEEFermatCoin * (100000 / 100155)
/-- Stage-4 (`p = 155`) `.nn` denominator `denomNNFermatCoinVal * (100000 / 100155)`. -/
def denomNNTier1WalkVal : ℝ := denomNNFermatCoinVal * (100000 / 100155)
/-- Stage-4 (`p = 155`) `.en` denominator `denomENFermatCoin 1 * (100000 / 100155)`. -/
def denomENTier1Walk : ℝ := denomENFermatCoin 1 * (100000 / 100155)
theorem mul_alphaTier1WalkFull_of_mul_eq {a b : ℕ} (hnat : a * 167085 = b * 167340) : (a : ℝ) *
    alphaTier1WalkFull = ((b : ℝ) * alphaFermatCoin) * (100000 / 100155) := by
  have hr : (a : ℝ) * 167085 = (b : ℝ) * 167340 := by exact_mod_cast hnat
  unfold alphaTier1WalkFull
  calc (a : ℝ) * (alphaFermatCoin * (167085 / 167340) * (100000 / 100155))
      = ((a : ℝ) * 167085) * (alphaFermatCoin / 167340 * (100000 / 100155)) := by ring
    _ = ((b : ℝ) * 167340) * (alphaFermatCoin / 167340 * (100000 / 100155)) := by rw [hr]
    _ = ((b : ℝ) * alphaFermatCoin) * (100000 / 100155) := by ring
/--
Tight per-particle 1D kinetic error numerators in `10^-11` Ha (`433, 819, 119, 492, 2377`,
summing across all `702` axes to `1,415,061 * 10^-11` Ha for `w_ke = 639,327,744`).
-/
def kinAxisErrNumTier1Walk (i : Particle_frozen) : ℕ :=
    if i.val < 23 then 433 else if i.val < 43 then 819 else if i.val < 46 then 119 else if i.val <
    47 then 492 else 2377
/-- Canonical `p = 155` (`w_ke = 639,327,744`) block-encoded operator `aImplGenZeroNEremOf`. -/
def aImplTier1WalkOf (vEE : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 187 → Fin 187 → ℝ)
    (vNN : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 47 → Fin 187 → ℝ)
    (vEN : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 187 → ℝ) : OpSys :=
    aImplGenZeroNEremOf wEESpeciesTier1Walk wNNSpeciesTier1Walk wENSpeciesTier1Walk wKinTier1Walk
    totalSlotsIdleTier1Walk vEE vNN vEN
abbrev epsBlockTier1WalkOf (εEE εNN εEN : ℝ) : ℝ :=
    epsBlockGenOf alphaTier1WalkFull (((1415061 : ℕ) : ℝ) / ((10 ^ 11 : ℕ) : ℝ)) εEE εNN εEN
def shiftTier1WalkParametric (midEE : ℝ) (midNN : ℕ → ℕ → ℝ) (midEN0 : Fin 4 → ℝ) : ℝ :=
    shiftGenParametricOf alphaTier1WalkFull totalSlotsIdleTier1Walk midEE midNN midEN0
/--
Turnkey `p = 155` (`p = 155`, `w_ke = 639,327,744`) parametric `BlockApproxSpecGen` theorem
explicitly naming `w_ke = 639,327,744`.
-/
theorem blockApproxSpecGen_tier1Walk_wke744_parametric
    (gEE : ℕ → ℝ) (gNN : ℕ → ℕ → ℝ) (midEE : ℝ) (midNN : ℕ → ℕ → ℝ) (midEN0 : Fin 4 → ℝ)
    {εEE εNN εEN : ℝ}
    (hEE0 : 0 ≤ εEE) (hNN0 : 0 ≤ εNN) (hEN0 : 0 ≤ εEN)
    (hCap : 4231872 * epsBlockTier1WalkOf εEE εNN εEN ≤ 100)
    (vEE : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 187 → Fin 187 → ℝ)
    (vNN : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 47 → Fin 187 → ℝ)
    (vEN : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 187 → ℝ)
    (hEE : ∀ x n1 e1 e2, e1 < e2 → |vEE x n1 e1 e2| ≤ 1)
    (hNN : ∀ x n1 n2 e1, n1 < n2 → |vNN x n1 n2 e1| ≤ 1)
    (hEN : ∀ x n1 e1, |vEN x n1 e1| ≤ 1)
    (hEEErr : ∀ x n1 e1 e2, e1 < e2 →
      |denomEETier1Walk * vEE x n1 e1 e2 - rEEScaledGen gEE midEE x n1 e1 e2| ≤ εEE)
    (hNNErr : ∀ x n1 n2 e1, n1 < n2 →
      |denomNNTier1WalkVal * vNN x n1 n2 e1 - rNNScaledGen gNN midNN x n1 n2 e1| ≤ εNN)
    (hENErr : ∀ x n1 e1,
      |denomENTier1Walk * vEN x n1 e1 - rENScaledGen gEE gNN midEN0 x n1 e1| ≤ εEN) :
    BlockApproxSpecGen hamiltonian_frozen alphaTier1WalkFull (shiftTier1WalkParametric midEE midNN
        midEN0)
      (epsBlockTier1WalkOf εEE εNN εEN) (aImplTier1WalkOf vEE vNN vEN) := by
  have ht : ‖kineticEnergy_frozen - (shiftKin : ℂ) • (1 : OpSys) -
      tImplOf 41 wKinTier1Walk alphaTier1WalkFull‖ ≤ (1415061 : ℝ) / 10 ^ 11 := by
    rw [kin_sum_sub_eq_kin]
    refine ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ ↦ ?_))).trans (le_of_eq
        (show (∑ i : Particle_frozen, ∑ _w : Fin 3, (kinAxisErrNumTier1Walk i : ℝ) / 10 ^ 11) = _ by
          simp_rw [← Finset.sum_div]
          rw [
            show (∑ i : Particle_frozen, ∑ _w : Fin 3, (kinAxisErrNumTier1Walk i : ℝ)) =
                ((∑ i : Particle_frozen, ∑ _w : Fin 3, kinAxisErrNumTier1Walk i : ℕ) : ℝ) by
              push_cast
              rfl,
            show (∑ i : Particle_frozen, ∑ _w : Fin 3, kinAxisErrNumTier1Walk i) = 1415061 by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
              rw [sum_fin_eq_sumTreeW 234 8 (by norm_num)]
              rfl]
          norm_num))
    refine (opNorm_embedMatrix_le _ _).trans
      (opNorm_conj_qft_diagReal_le _ (div_nonneg (Nat.cast_nonneg _) (by norm_num)) fun k ↦ ?_)
    rw [abs_mul]
    refine (mul_le_mul_of_nonneg_left (tc_sq_le k) (abs_nonneg _)).trans ?_
    rw [
      mul_comm _ (8192 : ℝ), show (8192 : ℝ) = |8192| by norm_num, ← abs_mul, abs_le]
    obtain ⟨hlo, hhi⟩ := pi_sq_bounds_kin
    unfold alphaTier1WalkFull alphaFermatCoin boxWidth_frozen
    rw [gridSpacing_eq_rat]
    rcases m_spec_kin i with ⟨h1, hm⟩ | ⟨h1, h2, hm⟩ | ⟨h1, h2, h3, hm⟩ |
        ⟨h1, h2, h3, h4, hm⟩ | ⟨h1, h2, h3, h4, hm⟩ <;>
      simp only [wKinTier1Walk, nucSpecies, wKinNucSpeciesTier1Walk, wKinElecTier1Walk,
        kinAxisErrNumTier1Walk, meR_kin, atomicMass_frozen,
        show i.val < 23 → i.val < 47 by omega, show i.val < 43 → i.val < 47 by omega,
        show i.val < 46 → i.val < 47 by omega, *, ↓reduceDIte, ↓reduceIte] <;>
      norm_num <;> constructor <;> linarith
  exact blockApproxSpecGen_genWeights_parametric gEE gNN midEE midNN midEN0
    (by
      unfold alphaTier1WalkFull
      exact mul_pos (mul_pos alphaFermatCoin_pos (by norm_num)) (by norm_num))
    (hs_tier1Walk_full_le_sMax.trans (by
      unfold sMax_tier1Walk_full
      norm_num))
    (by rw [sum_fin_eq_sumTreeW 47 6 (by norm_num)])
    (by
      simp_rw [sum_fin_eq_sumTreeW 47 6 (by norm_num)]
      rfl)
    (by rw [sum_fin_eq_sumTreeW 47 6 (by norm_num)])
    (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      rw [sum_fin_eq_sumTreeW 234 8 (by norm_num)])
    (Nat.le_of_eq rfl) (by norm_num) hEE0 hNN0 hEN0 (ht.trans (by norm_num))
    hCap vEE vNN vEN hEE hNN hEN
    (fun x n1 e1 e2 hlt ↦ by
      rw [show denomGenEE wEESpeciesTier1Walk alphaTier1WalkFull (nucSpecies n1) =
          denomEETier1Walk by
        refine Eq.trans (b := denomGenEE wEESpeciesFermatCoin alphaFermatCoin (nucSpecies n1) *
            (100000 / 100155)) ?_ ((congrArg (· * _) (denomGenEE_fermatCoin_eq _)).trans rfl)
        unfold denomGenEE
        rw [mul_alphaTier1WalkFull_of_mul_eq (b := wEESpeciesFermatCoin (nucSpecies n1)) (by
          generalize nucSpecies n1 = s
          fin_cases s <;> rfl)]
        ring]
      exact hEEErr x n1 e1 e2 hlt)
    (fun x n1 n2 e1 hlt ↦ by
      rw [show denomGenNN wNNSpeciesTier1Walk alphaTier1WalkFull (nucSpecies n1) (nucSpecies n2) =
          denomNNTier1WalkVal by
        refine Eq.trans (b := denomGenNN wNNSpeciesFermatCoin alphaFermatCoin
            (nucSpecies n1) (nucSpecies n2) * (100000 / 100155))
          ?_ ((congrArg (· * _) (denomGenNN_fermatCoin_of_lt hlt)).trans rfl)
        unfold denomGenNN
        rw [mul_alphaTier1WalkFull_of_mul_eq
          (b := wNNSpeciesFermatCoin (nucSpecies n1) (nucSpecies n2)) (by
            generalize nucSpecies n1 = s1, nucSpecies n2 = s2
            fin_cases s1 <;> fin_cases s2 <;> rfl)]
        ring]
      exact hNNErr x n1 n2 e1 hlt)
    (fun x n1 e1 ↦ by
      rw [show denomGenEN wENSpeciesTier1Walk alphaTier1WalkFull (nucSpecies n1) =
          denomENTier1Walk by
        have hg : gridSpacing_frozen ≠ 0 := ne_of_gt gridSpacing_pos
        unfold denomGenEN denomENTier1Walk alphaTier1WalkFull alphaFermatCoin denomENFermatCoin
        generalize nucSpecies n1 = s
        fin_cases s <;> simp only [wENSpeciesTier1Walk, speciesZ] <;> field_simp [hg] <;> norm_num]
      exact hENErr x n1 e1)
end QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc

section
open QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec
  QuantumComputation.Specs.PhotochemistrySolution.ScreenFermatCore
namespace QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc
set_option maxRecDepth 8192
theorem decodeTier1WalkCoin_coinOf5 {hi8 lo8 hi10 lo10 c5 : ℕ}
    (h1 : hi8 < 256) (h2 : lo8 < 256) (h3 : hi10 < 1024) (h4 : lo10 < 1024) (h5 : c5 < 32) :
    decodeTier1WalkCoin (tier1CoinOf5 hi8 lo8 hi10 lo10 c5) =
      let a8 := cond (hi8 == 255) (255 - lo8) hi8; let b8 := cond (hi8 == 255) 0 lo8;
      let px := b2Spec a8; let py := b6Spec hi10
      cond px.2.2.2
        (let p := tier1WalkKinNucBlk hi10
         let u15 := (lo10 % 64) + 64 * c5 + 2048 * (lo10 / 64)
         cond (Nat.blt u15 p.2) p.1 .idle)
        (cond py.2.2.2 .idle
          (let u1 := phiU1 py.1 px.1
           cond (hi8 == 255)
             (.kin (mkFin234 (47 + u1)) (mkFin3 px.2.1))
             (tier1WalkIntCell u1 px.2.1 py.2.1 px.2.2.1 py.2.2.1 (b8 % 64) (lo10 % 64)
               (c5 + 32 * (lo10 / 64) + 512 * (b8 / 64))))) := by
  obtain ⟨dc5, dlo10, dhi10, dlo8, dhi8, _⟩ :=
      tier1CoinOf5_digits h1 h2 h3 h4 h5; unfold decodeTier1WalkCoin; dsimp only; rw [dc5,
      dlo10, dhi10, dlo8, dhi8]
theorem card_decodeTier1WalkCoin_pot_w11 {s : ZeroNEremSector} (hIdle : s ≠ .idle)
    (hKin : ∀ i ax, s ≠ .kin i ax) {w : ℕ}
    (hw : w < 2048) : ((Finset.univ : Finset (Fin (2 ^ 41))).filter (fun c ↦
    decodeTier1WalkCoin c = s ∧ w11NatOfCoin c = w)).card = ∑ u1 : Fin 187, ∑ h1 : Fin 3,
    ∑ h2 : Fin 3, ∑ q5 : Fin 5, ∑ q31 : Fin 31, ∑ lo1 : Fin 64, ∑ lo2 : Fin 64,
    cond (eqSec (tier1WalkIntCell u1.val h1.val h2.val q5.val q31.val lo1.val lo2.val w) s) 1 0
    := by
  let H (c : Fin (2 ^ 41)) :=
      cond (eqSec (decodeTier1WalkCoin c) s && (w11NatOfCoin c == w)) 1 0
  have hNonPot0 (sec : ZeroNEremSector) (hsec : sec = .idle ∨ ∃ i ax, sec = .kin i ax) :
      eqSec sec s = false := Bool.eq_false_iff.mpr fun he ↦ by
    rcases hsec with rfl | ⟨i, ax, rfl⟩
    · exact hIdle ((eqSec_iff _ _).mp he).symm
    · exact hKin i ax ((eqSec_iff _ _).mp he).symm
  trans ∑ c : Fin (2 ^ 41), H c
  · rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    dsimp only [H]
    cases hs : eqSec (decodeTier1WalkCoin c) s
    · simp [mt (eqSec_iff _ _).mpr (Bool.eq_false_iff.mp hs)]
    · cases hw0 : (w11NatOfCoin c == w)
      · simp [beq_eq_false_iff_ne.mp hw0]
      · simp [(eqSec_iff _ _).mp hs, beq_iff_eq.mp hw0]
  rw [tier1_sum_coin41_split5 H,
    show (256 : ℕ) = 255 + 1 from rfl,
    sum_fin_add (M := 255) (N := 1) (fun hi8 ↦ ∑ lo8 : Fin 256, ∑ hi10 : Fin 1024,
      ∑ lo10 : Fin 1024, ∑ c5 : Fin 32, H (tier1CoinOf5 hi8 lo8.val hi10.val lo10.val c5.val)),
    Fin.sum_univ_one, show (∑ lo8 : Fin 256, ∑ hi10 : Fin 1024, ∑ lo10 : Fin 1024, ∑ c5 : Fin 32,
      H (tier1CoinOf5 (255 + (0 : Fin 1).val) lo8.val hi10.val lo10.val c5.val)) = 0 from
      Finset.sum_eq_zero fun lo8 _ ↦ Finset.sum_eq_zero fun hi10 _ ↦
        Finset.sum_eq_zero fun lo10 _ ↦ Finset.sum_eq_zero fun c5 _ ↦ by
          dsimp only [H, Fin.val_zero, Nat.add_zero]
          rw [hNonPot0 _ (by
            rw [decodeTier1WalkCoin_coinOf5 (by omega) lo8.isLt hi10.isLt lo10.isLt c5.isLt]
            dsimp only
            rw [show (255 == 255) = true from rfl, Bool.cond_true]
            cases (b2Spec (255 - lo8.val)).2.2.2
            · rw [Bool.cond_false]
              cases (b6Spec hi10.val).2.2.2 <;>
                first | exact Or.inr ⟨_, _, rfl⟩ | exact Or.inl rfl
            · rw [Bool.cond_true]
              cases Nat.blt ((lo10.val % 64) + 64 * c5.val + 2048 * (lo10.val / 64))
                (tier1WalkKinNucBlk hi10.val).2
              · exact Or.inl rfl
              · rw [Bool.cond_true]
                unfold tier1WalkKinNucBlk tier1WalkKinNucS8
                dsimp only
                let K {c : Bool} {p q : ZeroNEremSector × ℕ} := @tier1_cond_kin_or_idle c p q
                exact K (Or.inl rfl) (K (Or.inr ⟨_, _, rfl⟩) (K (K (Or.inr ⟨_, _, rfl⟩)
                  (K (K (Or.inr ⟨_, _, rfl⟩) (Or.inr ⟨_, _, rfl⟩)) (K (Or.inl rfl)
                    (K (Or.inl rfl) (K (Or.inr ⟨_, _, rfl⟩) (Or.inr ⟨_, _, rfl⟩))))))
                  (K (Or.inr ⟨_, _, rfl⟩) (K (Or.inr ⟨_, _, rfl⟩)
                    (K (Or.inr ⟨_, _, rfl⟩) (Or.inl rfl)))))))]
          rfl, Nat.add_zero]
  refine (Finset.sum_congr rfl fun a8 _ ↦ ?_).trans
    (sum_a8_a10_cart254 fun u1 h1 h2 q5 q31 ↦ ∑ lo1 : Fin 64, ∑ lo2 : Fin 64,
      cond (eqSec (tier1WalkIntCell u1 h1 h2 q5 q31 lo1.val lo2.val w) s) 1 0)
  have hne8 : (a8.val == 255) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_lt a8.isLt)
  have hb2f := (b2Spec_lt255 a8.isLt).2.2.2.1
  rw [Finset.sum_comm,
    show (1024 : ℕ) = 1023 + 1 from rfl,
    sum_fin_add (M := 1023) (N := 1) (fun hi10 ↦ ∑ lo8 : Fin 256, ∑ lo10 : Fin 1024,
      ∑ c5 : Fin 32, H (tier1CoinOf5 a8.val lo8.val hi10 lo10.val c5.val)),
    Fin.sum_univ_one, show (∑ lo8 : Fin 256, ∑ lo10 : Fin 1024, ∑ c5 : Fin 32,
      H (tier1CoinOf5 a8.val lo8.val (1023 + (0 : Fin 1).val) lo10.val c5.val)) = 0 from
      Finset.sum_eq_zero fun lo8 _ ↦ Finset.sum_eq_zero fun lo10 _ ↦
        Finset.sum_eq_zero fun c5 _ ↦ by
          dsimp only [H, Fin.val_zero, Nat.add_zero]
          rw [decodeTier1WalkCoin_coinOf5 (Nat.lt_succ_of_lt a8.isLt) lo8.isLt
            (by omega) lo10.isLt c5.isLt]
          simp only [hne8, hb2f, b6Spec_1023, Bool.cond_false, Bool.cond_true,
            hNonPot0 .idle (Or.inl rfl), Bool.false_and], Nat.add_zero]
  refine Finset.sum_congr rfl fun a10 _ ↦ ?_
  refine (Finset.sum_congr rfl fun lo8 _ ↦ Finset.sum_congr rfl fun lo10 _ ↦
    Finset.sum_congr rfl fun c5 _ ↦ ?_).trans ((tier1_sum_lo8_lo10_c5_w11 fun lo1 lo2 w11 ↦
      cond (eqSec (tier1WalkIntCell (phiU1 (b6Spec a10.val).1 (b2Spec a8.val).1)
        (b2Spec a8.val).2.1 (b6Spec a10.val).2.1
        (b2Spec a8.val).2.2.1 (b6Spec a10.val).2.2.1 lo1 lo2 w11) s && (w11 == w)) 1 0).trans
    (Finset.sum_congr rfl fun lo1 _ ↦ Finset.sum_congr rfl fun lo2 _ ↦ ?_))
  · dsimp only [H]
    rw [decodeTier1WalkCoin_coinOf5 (Nat.lt_succ_of_lt a8.isLt) lo8.isLt
          (Nat.lt_succ_of_lt a10.isLt) lo10.isLt c5.isLt,
        w11NatOfCoin_tier1CoinOf5 (Nat.lt_succ_of_lt a8.isLt) lo8.isLt
          (Nat.lt_succ_of_lt a10.isLt) lo10.isLt c5.isLt]
    simp only [hne8, hb2f, (b6Spec_lt1023 a10.isLt).2.2.2.1, Bool.cond_false]
  · rw [Finset.sum_eq_single ⟨w, hw⟩
      (fun u _ hne ↦ by simp [beq_eq_false_iff_ne.mpr (Fin.val_ne_of_ne hne)])
      (fun h ↦ absurd (Finset.mem_univ _) h)]
    simp only [beq_self_eq_true, Bool.and_true]

theorem sum_decodeTier1WalkCoin_sec (f : ZeroNEremSector → ℕ) : (∑ c : Fin (2 ^ 41),
    f (decodeTier1WalkCoin c)) = (∑ u1 : Fin 187, ∑ h1 : Fin 3, ∑ h2 : Fin 3,
    (5079040 * f (.kin (mkFin234 (47 + u1.val)) (mkFin3 h1.val)) + ∑ q5 : Fin 5, ∑ q31 : Fin 31,
    ∑ lo1 : Fin 64, ∑ lo2 : Fin 64, ∑ w11 : Fin 2048,
    f (tier1WalkIntCell u1.val h1.val h2.val q5.val q31.val lo1.val lo2.val w11.val))) +
    2147450880 * f .idle + ∑ hi10 : Fin 1024, ∑ u15 : Fin 32768,
    f (cond (Nat.blt u15.val (tier1WalkKinNucBlk hi10.val).2)
    (tier1WalkKinNucBlk hi10.val).1 .idle) := by
  rw [tier1_sum_coin41_split5 (fun c ↦ f (decodeTier1WalkCoin c)),
      show (256 : ℕ) = 255 + 1 from rfl,
      sum_fin_add (M := 255) (N := 1)
        (fun hi8 ↦ ∑ lo8 : Fin 256, ∑ hi10 : Fin 1024, ∑ lo10 : Fin 1024, ∑ c5 : Fin 32,
          f (decodeTier1WalkCoin (tier1CoinOf5 hi8 lo8.val hi10.val lo10.val c5.val))),
      Fin.sum_univ_one]
  simp only [Fin.val_zero, Nat.add_zero]
  have hTop8 : (∑ lo8 : Fin 256, ∑ hi10 : Fin 1024, ∑ lo10 : Fin 1024, ∑ c5 : Fin 32,
      f (decodeTier1WalkCoin (tier1CoinOf5 255 lo8.val hi10.val lo10.val c5.val))) =
      (∑ hi10 : Fin 1024, ∑ u15 : Fin 32768,
      f (cond (Nat.blt u15.val (tier1WalkKinNucBlk hi10.val).2)
      (tier1WalkKinNucBlk hi10.val).1 .idle)) + (8355840 * f .idle + ∑ a8 : Fin 255,
      ∑ a10 : Fin 1023, 32768 * f (.kin (mkFin234 (47 + phiU1 (b6Spec a10.val).1 (b2Spec a8.val).1))
      (mkFin3 (b2Spec a8.val).2.1))) := by
    rw [show (256 : ℕ) = 1 + 255 from rfl,
        sum_fin_add (M := 1) (N := 255)
          (fun lo8 ↦ ∑ hi10 : Fin 1024, ∑ lo10 : Fin 1024, ∑ c5 : Fin 32,
            f (decodeTier1WalkCoin (tier1CoinOf5 255 lo8 hi10.val lo10.val c5.val))),
        Fin.sum_univ_one]
    simp only [Fin.val_zero]; refine congrArg₂ HAdd.hAdd ?_ ?_
    · refine Finset.sum_congr rfl fun hi10 _ ↦ ?_
      rw [← tier1_sum_lo10_c5_u15 (fun u15 ↦
        f (cond (Nat.blt u15 (tier1WalkKinNucBlk hi10.val).2)
          (tier1WalkKinNucBlk hi10.val).1 .idle))]
      refine Finset.sum_congr rfl fun lo10 _ ↦ Finset.sum_congr rfl fun c5 _ ↦ ?_
      rw [decodeTier1WalkCoin_coinOf5 (by omega) (by omega) hi10.isLt lo10.isLt c5.isLt]
      simp only [show (255 == 255) = true from rfl, Nat.sub_zero, b2Spec_255, Bool.cond_true]
    · have sum10_5 {g : Fin 1024 → Fin 32 → ℕ} {v : ℕ} (hg : ∀ x y, g x y = v) :
          (∑ x : Fin 1024, ∑ y : Fin 32, g x y) = 32768 * v := by
        simp only [hg, Finset.sum_const, Finset.card_fin, smul_eq_mul, ← Nat.mul_assoc]
      trans ∑ r8 : Fin 255, (32768 * f .idle + ∑ a10 : Fin 1023,
        32768 * f (.kin (mkFin234 (47 + phiU1 (b6Spec a10.val).1 (b2Spec (255 - 1 - r8.val)).1))
          (mkFin3 (b2Spec (255 - 1 - r8.val)).2.1)))
      · refine Finset.sum_congr rfl fun r8 _ ↦ ?_
        have hr8lt : r8.val < 255 := r8.isLt
        have hb2f := (b2Spec_lt255 (by omega : 255 - (1 + r8.val) < 255)).2.2.2.1
        rw [
          show (1024 : ℕ) = 1023 + 1 from rfl,
          sum_fin_add (M := 1023) (N := 1) (fun hi10 ↦ ∑ lo10 : Fin 1024, ∑ c5 : Fin 32,
            f (decodeTier1WalkCoin (tier1CoinOf5 255 (1 + r8.val) hi10 lo10.val c5.val))),
          Fin.sum_univ_one, Fin.val_zero, Nat.add_zero]
        refine (congrArg₂ HAdd.hAdd (Finset.sum_congr rfl fun a10 _ ↦ sum10_5 fun lo10 c5 ↦
            congrArg f ?_) (sum10_5 fun lo10 c5 ↦ congrArg f ?_)).trans (add_comm _ _)
        · rw [decodeTier1WalkCoin_coinOf5 (by omega) (by omega)
                (Nat.lt_succ_of_lt a10.isLt) lo10.isLt c5.isLt]
          simp only [show (255 == 255) = true from rfl, hb2f,
            (b6Spec_lt1023 a10.isLt).2.2.2.1, Bool.cond_true, Bool.cond_false]
          rw [show 255 - (1 + r8.val) = 255 - 1 - r8.val by omega]
        · rw [decodeTier1WalkCoin_coinOf5 (by omega) (by omega) (by omega) lo10.isLt c5.isLt]
          simp only [show (255 == 255) = true from rfl, hb2f, b6Spec_1023,
            Bool.cond_true, Bool.cond_false]
      · rw [Finset.sum_add_distrib,
          tier1_sum_rev_fin (N := 255) (fun a8 ↦ ∑ a10 : Fin 1023,
          32768 * f (.kin (mkFin234 (47 + phiU1 (b6Spec a10.val).1 (b2Spec a8).1))
            (mkFin3 (b2Spec a8).2.1)))]
        simp only [Finset.sum_const, Finset.card_fin, smul_eq_mul]
        ring
  have ha8Step (a8 : Fin 255) :
      (∑ lo8 : Fin 256, ∑ hi10 : Fin 1024, ∑ lo10 : Fin 1024, ∑ c5 : Fin 32,
        f (decodeTier1WalkCoin (tier1CoinOf5 a8.val lo8.val hi10.val lo10.val c5.val))) =
      8388608 * f .idle +
      ∑ a10 : Fin 1023, ∑ lo1 : Fin 64, ∑ lo2 : Fin 64, ∑ w11 : Fin 2048,
        f (tier1WalkIntCell (phiU1 (b6Spec a10.val).1 (b2Spec a8.val).1)
          (b2Spec a8.val).2.1 (b6Spec a10.val).2.1
          (b2Spec a8.val).2.2.1 (b6Spec a10.val).2.2.1 lo1.val lo2.val w11.val) := by
    have hne8 : (a8.val == 255) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_lt a8.isLt)
    have hb2f := (b2Spec_lt255 a8.isLt).2.2.2.1
    rw [Finset.sum_comm,
        show (1024 : ℕ) = 1023 + 1 from rfl,
        sum_fin_add (M := 1023) (N := 1) (fun hi10 ↦ ∑ lo8 : Fin 256, ∑ lo10 : Fin 1024,
          ∑ c5 : Fin 32,
            f (decodeTier1WalkCoin (tier1CoinOf5 a8.val lo8.val hi10 lo10.val c5.val))),
        Fin.sum_univ_one, Fin.val_zero, Nat.add_zero]
    refine (congrArg₂ HAdd.hAdd (Finset.sum_congr rfl fun a10 _ ↦ ?_) ?_).trans (add_comm _ _)
    · rw [← tier1_sum_lo8_lo10_c5_w11 (fun lo1 lo2 w11 ↦
        f (tier1WalkIntCell (phiU1 (b6Spec a10.val).1 (b2Spec a8.val).1)
          (b2Spec a8.val).2.1 (b6Spec a10.val).2.1
          (b2Spec a8.val).2.2.1 (b6Spec a10.val).2.2.1 lo1 lo2 w11))]
      refine Finset.sum_congr rfl fun lo8 _ ↦ Finset.sum_congr rfl fun lo10 _ ↦
        Finset.sum_congr rfl fun c5 _ ↦ congrArg f ?_
      rw [decodeTier1WalkCoin_coinOf5 (Nat.lt_succ_of_lt a8.isLt) lo8.isLt
            (Nat.lt_succ_of_lt a10.isLt) lo10.isLt c5.isLt]
      simp only [hne8, hb2f, (b6Spec_lt1023 a10.isLt).2.2.2.1, Bool.cond_false]
    · simp only [show ∀ (lo8 : Fin 256) (lo10 : Fin 1024) (c5 : Fin 32),
          f (decodeTier1WalkCoin (tier1CoinOf5 a8.val lo8.val 1023 lo10.val c5.val)) = f .idle
          from fun lo8 lo10 c5 ↦ congrArg f <| by
            rw [decodeTier1WalkCoin_coinOf5 (Nat.lt_succ_of_lt a8.isLt) lo8.isLt
                  (by omega) lo10.isLt c5.isLt]
            simp only [hne8, hb2f, b6Spec_1023, Bool.cond_false, Bool.cond_true],
        Finset.sum_const, Finset.card_fin, smul_eq_mul, ← Nat.mul_assoc]
  rw [Finset.sum_congr rfl fun a8 _ ↦ ha8Step a8, Finset.sum_add_distrib, hTop8]
  have hComb := sum_a8_a10_cart254 fun u1 h1 h2 q5 q31 ↦
    32768 * f (.kin (mkFin234 (47 + u1)) (mkFin3 h1)) +
    ∑ lo1 : Fin 64, ∑ lo2 : Fin 64, ∑ w11 : Fin 2048,
      f (tier1WalkIntCell u1 h1 h2 q5 q31 lo1.val lo2.val w11.val)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, smul_eq_mul,
    ← Finset.mul_sum, ← Nat.mul_assoc] at hComb ⊢
  omega

/-- `9`-class tile classifier on `(q5, q31) ∈ Fin 5 × Fin 31` for the `p = 155` regime. -/
def tier1WalkTileKind (q5 q31 : ℕ) : ℕ :=
  cond (Nat.blt q31 16 || (Nat.beq q31 24 && Nat.beq q5 4)) 0
    (cond (Nat.beq q31 25 && Nat.beq q5 4) 1
      (cond (Nat.ble 16 q31 && Nat.blt q31 24) 2
        (cond (Nat.beq q31 26 && Nat.beq q5 4) 3
          (cond (Nat.ble 28 q31) 4
            (cond (Nat.beq q31 27 && Nat.beq q5 4) 5
              (cond (Nat.beq q31 27 && (Nat.beq q5 2 || Nat.beq q5 3)) 6
                (cond (Nat.beq q31 26 && Nat.beq q5 3) 7 8)))))))
/--
Sector decoded by tile class `k ∈ 0..8` at `(u1, h1, h2, lo1, lo2, w11)` for the `p = 155` regime.
-/
def tier1WalkByKind : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ZeroNEremSector
  | 0, u1, h1, h2, lo1, lo2, _ => tier1EeTag u1 h1 h2 lo1 lo2
  | 1, u1, h1, h2, lo1, lo2, w11 =>
      cond (Nat.blt w11 1452) (tier1EeTag u1 h1 h2 lo1 lo2) (tier1FbKin u1 h1)
  | 2, u1, h1, h2, lo1, lo2, _ => tier1NnTag u1 h1 h2 lo1 lo2
  | 3, u1, h1, h2, lo1, lo2, w11 =>
      cond (Nat.blt w11 1750) (tier1NnTag u1 h1 h2 lo1 lo2) (tier1FbKin u1 h1)
  | 4, u1, h1, _, lo1, _, _ => tier1EnTag u1 h1 lo1
  | 5, u1, h1, _, lo1, lo2, w11 =>
      cond (Nat.blt lo2 56 || (Nat.blt lo2 60 && Nat.blt w11 1351))
        (tier1EnTag u1 h1 lo1) (tier1FbKin u1 h1)
  | 6, u1, h1, h2, _, _, _ =>
      cond (Nat.beq h2 0) (tier1FbKin u1 0) (tier1FbKin u1 h1)
  | 7, u1, h1, h2, lo1, lo2, w11 =>
      let v23 := cart254V23 lo1 lo2 w11
      cond (Nat.beq h1 1 && Nat.beq h2 0 && Nat.blt v23 3431948) (tier1FbKin u1 0)
        (cond (Nat.beq h1 2 && Nat.beq h2 0 && Nat.blt v23 2779112) (tier1FbKin u1 0)
          (cond (Nat.beq h1 2 && Nat.beq h2 2 && Nat.blt v23 1824216) .idle (tier1FbKin u1 h1)))
  | _, u1, h1, _, _, _, _ => tier1FbKin u1 h1
theorem tier1Walk_cond_lt9 {c : Bool} {a b : ℕ} (ha : a < 9) (hb : b < 9) : cond c a b < 9 := by
  cases c <;> assumption
theorem tier1WalkTileKind_lt9 (q5 q31 : ℕ) : tier1WalkTileKind q5 q31 < 9 := by
  unfold tier1WalkTileKind
  exact tier1Walk_cond_lt9 (by omega) (tier1Walk_cond_lt9 (by omega) (tier1Walk_cond_lt9 (by omega)
    (tier1Walk_cond_lt9 (by omega) (tier1Walk_cond_lt9 (by omega) (tier1Walk_cond_lt9 (by omega)
      (tier1Walk_cond_lt9 (by omega) (tier1Walk_cond_lt9 (by omega) (by omega))))))))
theorem tier1WalkIntCell_eq_raw (u1 h1 h2 q5 q31 lo1 lo2 w11 : ℕ) :
    tier1WalkIntCell u1 h1 h2 q5 q31 lo1 lo2 w11 =
      let v23 := cart254V23 lo1 lo2 w11
      cond (Nat.blt q31 16 || (Nat.beq q31 24 && Nat.beq q5 4) ||
            (Nat.beq q31 25 && Nat.beq q5 4 && Nat.blt w11 1452))
        (tier1EeTag u1 h1 h2 lo1 lo2)
        (cond ((Nat.ble 16 q31 && Nat.blt q31 24) ||
               (Nat.beq q31 26 && Nat.beq q5 4 && Nat.blt w11 1750))
          (tier1NnTag u1 h1 h2 lo1 lo2)
          (cond (Nat.ble 28 q31 ||
                 (Nat.beq q31 27 && Nat.beq q5 4 &&
                   (Nat.blt lo2 56 || (Nat.blt lo2 60 && Nat.blt w11 1351))))
            (tier1EnTag u1 h1 lo1)
            (cond (Nat.beq q31 27 && (Nat.beq q5 2 || Nat.beq q5 3) && Nat.beq h2 0)
              (tier1FbKin u1 0)
              (cond (Nat.beq q31 26 && Nat.beq q5 3)
                (cond (Nat.beq h1 1 && Nat.beq h2 0 && Nat.blt v23 3431948)
                  (tier1FbKin u1 0)
                  (cond (Nat.beq h1 2 && Nat.beq h2 0 && Nat.blt v23 2779112)
                    (tier1FbKin u1 0)
                    (cond (Nat.beq h1 2 && Nat.beq h2 2 && Nat.blt v23 1824216)
                      .idle (tier1FbKin u1 h1))))
                (tier1FbKin u1 h1))))) := rfl
theorem eqSec_cond_false {c : Bool} {a b s : ZeroNEremSector}
    (ha : eqSec a s = false) (hb : eqSec b s = false) :
    eqSec (cond c a b) s = false := by cases c <;> assumption
theorem eqSec_tier1WalkByKind_eq_false {k u1 h1 h2 a b w : ℕ} (hk9 : k < 9)
    {s : ZeroNEremSector}
    (hE : (k ≠ 0 ∧ k ≠ 1) ∨ ∀ n1 e1 e2, eqSec (.ee n1 e1 e2) s = false)
    (hN : (k ≠ 2 ∧ k ≠ 3) ∨ ∀ n1 n2 e1, eqSec (.nn n1 n2 e1) s = false)
    (hEN : (k ≠ 4 ∧ k ≠ 5) ∨ ∀ n1, eqSec (.en n1 (mkFin187 u1)) s = false)
    (hI : k ≠ 7 ∨ eqSec .idle s = false)
    (hF : ∀ m, eqSec (tier1FbKin u1 m) s = false) :
    eqSec (tier1WalkByKind k u1 h1 h2 a b w) s = false := by
  have hee (h : ∀ n1 e1 e2, eqSec (.ee n1 e1 e2) s = false) :
      eqSec (tier1EeTag u1 h1 h2 a b) s = false := eqSec_cond_false (h _ _ _) (hF h1)
  have hnn (h : ∀ n1 n2 e1, eqSec (.nn n1 n2 e1) s = false) :
      eqSec (tier1NnTag u1 h1 h2 a b) s = false := eqSec_cond_false (h _ _ _) (hF h1)
  have hen (h : ∀ n1, eqSec (.en n1 (mkFin187 u1)) s = false) :
      eqSec (tier1EnTag u1 h1 a) s = false := eqSec_cond_false (h _) (hF h1)
  rcases (by omega :
      (k = 0 ∨ k = 1) ∨ (k = 2 ∨ k = 3) ∨ (k = 4 ∨ k = 5) ∨ k = 6 ∨ k = 7 ∨ k = 8) with
    hk01 | hk23 | hk45 | rfl | rfl | rfl
  · rcases hE with ⟨_, _⟩ | hE0 <;> first | omega |
      (rcases hk01 with rfl | rfl <;>
        first | exact hee hE0 | exact eqSec_cond_false (hee hE0) (hF h1))
  · rcases hN with ⟨_, _⟩ | hN0 <;> first | omega |
      (rcases hk23 with rfl | rfl <;>
        first | exact hnn hN0 | exact eqSec_cond_false (hnn hN0) (hF h1))
  · rcases hEN with ⟨_, _⟩ | hEN0 <;> first | omega |
      (rcases hk45 with rfl | rfl <;>
        first | exact hen hEN0 | exact eqSec_cond_false (hen hEN0) (hF h1))
  · exact eqSec_cond_false (hF 0) (hF h1)
  · rcases hI with _ | hI0 <;> first | omega |
      exact eqSec_cond_false (hF 0) (eqSec_cond_false (hF 0) (eqSec_cond_false hI0 (hF h1)))
  · exact hF h1
theorem sum2_byKind_zero [Fintype (Fin 64)] {k u1 h1 h2 w : ℕ} (hk9 : k < 9) {s : ZeroNEremSector}
    (hE : (k ≠ 0 ∧ k ≠ 1) ∨ ∀ n1 e1 e2, eqSec (.ee n1 e1 e2) s = false)
    (hN : (k ≠ 2 ∧ k ≠ 3) ∨ ∀ n1 n2 e1, eqSec (.nn n1 n2 e1) s = false)
    (hEN : (k ≠ 4 ∧ k ≠ 5) ∨ ∀ n1, eqSec (.en n1 (mkFin187 u1)) s = false)
    (hI : k ≠ 7 ∨ eqSec .idle s = false)
    (hF : ∀ m, eqSec (tier1FbKin u1 m) s = false) :
    (∑ a : Fin 64, ∑ b : Fin 64,
        cond (eqSec (tier1WalkByKind k u1 h1 h2 a.val b.val w) s) 1 0) =
      0 :=
  Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun b _ ↦ by
    rw [eqSec_tier1WalkByKind_eq_false (a := a.val) (b := b.val) hk9 hE hN hEN hI hF]
    rfl
theorem tier1WalkIntCell_eq_byKind (u1 h1 h2 lo1 lo2 w11 : ℕ) (q5 : Fin 5) (q31 : Fin 31) :
    tier1WalkIntCell u1 h1 h2 q5.val q31.val lo1 lo2 w11 =
      tier1WalkByKind (tier1WalkTileKind q5.val q31.val) u1 h1 h2 lo1 lo2 w11 := by
  rw [tier1WalkIntCell_eq_raw]
  dsimp only
  rcases Nat.lt_or_ge q31.val 16 with h16 | h16
  · unfold tier1WalkTileKind
    rw [Nat.blt_eq.mpr h16]
    simp only [Bool.true_or, Bool.cond_true, tier1WalkByKind]
  · have hb16 : Nat.blt q31.val 16 = false :=
      Bool.eq_false_iff.mpr fun h ↦ Nat.not_lt.mpr h16 (Nat.blt_eq.mp h)
    rcases Nat.lt_or_ge q31.val 24 with h24 | h24
    · unfold tier1WalkTileKind
      rw [hb16, tier1_nat_beq_eq_false_of_ne (by omega : q31.val ≠ 24),
          tier1_nat_beq_eq_false_of_ne (by omega : q31.val ≠ 25),
          Nat.ble_eq.mpr h16, Nat.blt_eq.mpr h24]
      simp only [Bool.false_and, Bool.false_or, Bool.true_and, Bool.true_or,
        Bool.cond_true, Bool.cond_false, tier1WalkByKind]
    · rcases Nat.lt_or_ge q31.val 28 with h28 | h28
      · have hq5 := q5.isLt
        rcases (by omega : q31.val = 24 ∨ q31.val = 25 ∨ q31.val = 26 ∨ q31.val = 27) with
            r31 | r31 | r31 | r31 <;>
          rcases (by omega : q5.val = 0 ∨ q5.val = 1 ∨ q5.val = 2 ∨ q5.val = 3 ∨ q5.val = 4) with
            r5 | r5 | r5 | r5 | r5
        all_goals
          rw [r31, r5]
          rfl
      · have hblt24 : Nat.blt q31.val 24 = false :=
          Bool.eq_false_iff.mpr fun h ↦ Nat.not_lt.mpr h24 (Nat.blt_eq.mp h)
        unfold tier1WalkTileKind
        rw [hb16, tier1_nat_beq_eq_false_of_ne (by omega : q31.val ≠ 24),
            tier1_nat_beq_eq_false_of_ne (by omega : q31.val ≠ 25),
            Nat.ble_eq.mpr h16, hblt24,
            tier1_nat_beq_eq_false_of_ne (by omega : q31.val ≠ 26), Nat.ble_eq.mpr h28]
        simp only [Bool.false_and, Bool.false_or, Bool.true_and, Bool.true_or,
          Bool.cond_true, Bool.cond_false, tier1WalkByKind]
theorem eqSec_tier1WalkIntCell_eq_false {u1 h1 h2 lo1 lo2 w11 : ℕ} (q5 : Fin 5) (q31 : Fin 31)
    {s : ZeroNEremSector} (hI : eqSec .idle s = false)
    (hF : ∀ m, eqSec (tier1FbKin u1 m) s = false)
    (hE : ∀ n1 e1 e2, eqSec (.ee n1 e1 e2) s = false)
    (hN : ∀ n1 n2 e1, eqSec (.nn n1 n2 e1) s = false)
    (hEN : ∀ n1, eqSec (.en n1 (mkFin187 u1)) s = false) :
    eqSec (tier1WalkIntCell u1 h1 h2 q5.val q31.val lo1 lo2 w11) s = false := by
  rw [tier1WalkIntCell_eq_byKind]
  exact eqSec_tier1WalkByKind_eq_false (tier1WalkTileKind_lt9 _ _)
    (Or.inr hE) (Or.inr hN) (Or.inr hEN) (Or.inr hI) hF
/-- Multiplicity `[81, 1, 40, 1, 15, 1, 2, 1, 13]` of each tile class across `5 × 31 = 155`. -/
def tier1WalkTileKindMult : ℕ → ℕ
  | 0 => 81 | 1 => 1 | 2 => 40 | 3 => 1 | 4 => 15
  | 5 => 1 | 6 => 2 | 7 => 1 | _ => 13
/-- Row count of tile class `k` across `q31 < 31` at fixed `q5` for the `p = 155` regime. -/
def tier1WalkTileCnt31 (k q5 : ℕ) : ℕ := foldSum 31 fun q31 ↦
    cond (Nat.beq (tier1WalkTileKind q5 q31) k) 1 0
theorem check_tier1WalkTileKindMult :
    (allTree 5 0 9 fun k ↦
      Nat.beq (foldSum 5 (tier1WalkTileCnt31 k)) (tier1WalkTileKindMult k)) = true := rfl
theorem sum_9_tier1WalkTileKindMult (V : ℕ → ℕ) :
    (∑ k : Fin 9, tier1WalkTileKindMult k.val * V k.val) = 81 * V 0 + V 1 + 40 * V 2 + V 3 +
    15 * V 4 + V 5 + 2 * V 6 + V 7 + 13 *
    V 8 := by simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
                tier1WalkTileKindMult]; ring
end QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc

namespace QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc
set_option maxRecDepth 8192
attribute [local irreducible] foldSum tier1WalkTileCnt31
theorem sum_q5_q31_tier1WalkTileKind (V : ℕ → ℕ) :
    (∑ q5 : Fin 5, ∑ q31 : Fin 31, V (tier1WalkTileKind q5.val q31.val)) =
      81 * V 0 + V 1 + 40 * V 2 + V 3 + 15 * V 4 + V 5 + 2 * V 6 + V 7 + 13 * V 8 := by
  simp only [show ∀ (q5 : Fin 5) (q31 : Fin 31), V (tier1WalkTileKind q5.val q31.val) =
      ∑ k : Fin 9, cond (Nat.beq (tier1WalkTileKind q5.val q31.val) k.val) 1 0 * V k.val
      from fun q5 q31 ↦ ((Finset.sum_eq_single ⟨_, tier1WalkTileKind_lt9 q5.val q31.val⟩
        (fun k _ hne ↦ by
          rw [tier1_nat_beq_eq_false_of_ne fun hv ↦ hne (Fin.ext hv.symm)]
          exact zero_mul _)
        (fun h ↦ absurd (Finset.mem_univ _) h)).trans (by
          dsimp only
          rw [Nat.beq_eq.mpr rfl]
          exact one_mul _)).symm]
  rw [Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm, Finset.sum_comm]
  refine (Finset.sum_congr rfl fun k _ ↦ ?_).trans (sum_9_tier1WalkTileKindMult V)
  simp only [← Finset.sum_mul]
  refine congrArg (· * V k.val) ?_
  trans ∑ q5 : Fin 5, tier1WalkTileCnt31 k.val q5.val
  · refine Finset.sum_congr rfl fun q5 _ ↦ ?_
    unfold tier1WalkTileCnt31
    exact sum_fin_eq_foldSum 31 fun q31 ↦
        cond (Nat.beq (tier1WalkTileKind q5.val q31) k.val) 1 0
  · exact (sum_fin_eq_foldSum 5 (tier1WalkTileCnt31 k.val)).trans
      (Nat.beq_eq.mp (allTree_zero check_tier1WalkTileKindMult k.isLt))
end QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc

namespace QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc
set_option maxRecDepth 8192
attribute [local irreducible] foldSum
/--
Closed-form `.ee` `W11` fiber multiplicity on `w < 2048` (`0x000` polarity) for the `p = 155`
regime.
-/
theorem fib_ee_tier1Walk_w11Nat (n1 : Fin 47) (e1 e2 : Fin 187) {w : ℕ}
    (hw : w < 2048) : ((Finset.univ : Finset (Fin (2 ^ 41))).filter (fun c ↦
    decodeTier1WalkCoin c = .ee n1 e1 e2 ∧ w11NatOfCoin c = w)).card = if e1 < e2 then 2 *
    speciesZ (nucSpecies n1) * (81 + if w < 1452 then 1 else 0) else 0 := by
  rw [card_decodeTier1WalkCoin_pot_w11 (by intro h; cases h) (by intro _ _ h; cases h) hw]
  trans ∑ u1 : Fin 187, ∑ h1 : Fin 3, ∑ h2 : Fin 3, (81 + if w < 1452 then 1 else 0) *
      ∑ lo1 : Fin 64, ∑ lo2 : Fin 64,
        cond (eqSec (tier1EeTag u1.val h1.val h2.val lo1.val lo2.val) (.ee n1 e1 e2)) 1 0
  · refine Finset.sum_congr rfl fun u1 _ ↦ Finset.sum_congr rfl fun h1 _ ↦
      Finset.sum_congr rfl fun h2 _ ↦ ?_
    simp only [tier1WalkIntCell_eq_byKind]
    let Z (k : ℕ) := ∑ lo1 : Fin 64, ∑ lo2 : Fin 64,
      cond (eqSec (tier1WalkByKind k u1.val h1.val h2.val lo1.val lo2.val w)
          (.ee n1 e1 e2)) 1 0
    have hz (k : ℕ) (hk : 2 ≤ k ∧ k < 9) : Z k = 0 :=
      sum2_byKind_zero hk.2 (Or.inl (by omega)) (Or.inr fun _ _ _ ↦ rfl)
        (Or.inr fun _ ↦ rfl) (Or.inr rfl) fun _ ↦ rfl
    rw [sum_q5_q31_tier1WalkTileKind Z, hz 2 (by decide), hz 3 (by decide), hz 4 (by decide),
        hz 5 (by decide), hz 6 (by decide), hz 7 (by decide), hz 8 (by decide)]
    dsimp only [Z]
    simp only [tier1WalkByKind]
    by_cases hlt : w < 1452
    · simp only [hlt, ↓reduceIte, Nat.blt_eq.mpr hlt, Bool.cond_true]
      ring
    · simp only [hlt, ↓reduceIte, Bool.eq_false_iff.mpr fun h ↦ hlt (Nat.blt_eq.mp h),
        Bool.cond_false, show eqSec (tier1FbKin u1.val h1.val) (.ee n1 e1 e2) = false from rfl,
        Finset.sum_const_zero]
      ring
  simp only [← Finset.mul_sum]
  have hsum : (∑ u1 : Fin 187, ∑ h1 : Fin 3, ∑ h2 : Fin 3, ∑ lo1 : Fin 64, ∑ lo2 : Fin 64,
      cond (eqSec (tier1EeTag u1.val h1.val h2.val lo1.val lo2.val) (.ee n1 e1 e2)) 1 0) = if e1 <
      e2 then 2 * speciesZ (nucSpecies n1) else 0 := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos 167084); rw [Finset.mul_sum]
    trans ∑ u1 : Fin 187, PhotochemistrySolution.FermatInverse.fermatPerU1 u1.val (.ee n1 e1 e2)
    · refine Finset.sum_congr rfl fun u1 _ ↦ ?_
      rw [PhotochemistrySolution.FermatInverse.fermatPerU1_ee n1 e1 e2 u1]
      simp only [Finset.mul_sum]
      refine (Finset.sum_congr rfl fun h1 _ ↦ Finset.sum_congr rfl fun h2 _ ↦
        Finset.sum_congr rfl fun lo1 _ ↦ Finset.sum_congr rfl fun lo2 _ ↦ ?_).trans
        ((tier1_sum_h1_h2_lo1_lo2 fun z1 raw2 ↦
          cond (eqSec (eeCellFermat u1.val z1 (b11Ext192 raw2)).1 (.ee n1 e1 e2))
            (eeCellFermat u1.val z1 (b11Ext192 raw2)).2 0).trans
          (foldSum_congr fun z1 _ ↦ foldSum_perm 192 b11Ext192 b11ExtInv192
            (fun r hr ↦ ⟨(b11Ext192_spec hr).1, (b11Ext192_spec hr).2.1⟩)
            (fun z hz ↦ b11ExtInv192_spec hz) fun z2 ↦
            cond (eqSec (eeCellFermat u1.val z1 z2).1 (.ee n1 e1 e2))
              (eeCellFermat u1.val z1 z2).2 0))
      simpa only [show eqSec (tier1FbKin u1.val h1.val) (.ee n1 e1 e2) = false from rfl,
        show eqSec (.kin (mkFin234 (47 + u1.val))
          (mkFin3 ((64 * h1.val + lo1.val) / 64))) (.ee n1 e1 e2) = false from rfl,
        Bool.cond_false, mul_zero, add_zero] using
        tier1EeTag_eq_eeCell (u1 := u1.val) h1.isLt h2.isLt lo1.isLt lo2.isLt (.ee n1 e1 e2)
    have hmaster := FermatInverse.card_decodeFermatCanon_master (.ee n1 e1 e2)
    rw [foldSum_zero_of_forall fun b _ ↦ by
        rw [FermatInverse.kinNucBlkFermat_eq_zero_of_not_kin b (.ee n1 e1 e2)
          fun _ _ h ↦ by cases h]
        rfl] at hmaster
    simp only [show cond (eqSec .idle (.ee n1 e1 e2)) 2097120 0 = 0 from rfl, add_zero] at hmaster
    rw [← hmaster, count_fermat_ee]
    split_ifs
    · generalize nucSpecies n1 = sp
      fin_cases sp <;> rfl
    · rfl
  rw [hsum]
  split_ifs <;> ring
/--
Closed-form `.nn` `W11` fiber multiplicity on `w < 2048` (`0x000` polarity) for the `p = 155`
regime.
-/
theorem fib_nn_tier1Walk_w11Nat (n1 n2 : Fin 47) (e1 : Fin 187) {w : ℕ}
    (hw : w < 2048) : ((Finset.univ : Finset (Fin (2 ^ 41))).filter (fun c ↦
    decodeTier1WalkCoin c = .nn n1 n2 e1 ∧ w11NatOfCoin c = w)).card = if n1 <
    n2 then if (nucSpecies n1).val = 3 ∧ (nucSpecies n2).val =
    3 then 0 else speciesZ (nucSpecies n1) * speciesZ (nucSpecies n2) * (80 + 2 * if w <
    1750 then 1 else 0) else 0 := by
  rw [card_decodeTier1WalkCoin_pot_w11 (by intro h; cases h) (by intro _ _ h; cases h) hw]
  have hu1 (u1 : Fin 187) :
      (∑ h1 : Fin 3, ∑ h2 : Fin 3, ∑ q5 : Fin 5, ∑ q31 : Fin 31, ∑ lo1 : Fin 64, ∑ lo2 : Fin 64,
        cond (eqSec (tier1WalkIntCell u1.val h1.val h2.val q5.val q31.val lo1.val lo2.val w)
          (.nn n1 n2 e1)) 1 0) =
      foldSum 192 fun z1 ↦ foldSum 192 fun z2 ↦ (40 + cond (Nat.blt w 1750) 1 0) *
        cond (eqSec (nnCellFermat u1.val z1 z2).1 (.nn n1 n2 e1)) 1 0 := by
    trans ∑ h1 : Fin 3, ∑ h2 : Fin 3, ∑ lo1 : Fin 64, ∑ lo2 : Fin 64,
      (40 + cond (Nat.blt w 1750) 1 0) *
        cond (eqSec (nnCellFermat u1.val (64 * h1.val + lo1.val)
          (ultraToPinned192 (64 * h2.val + lo2.val))).1 (.nn n1 n2 e1)) 1 0
    · refine Finset.sum_congr rfl fun h1 _ ↦ Finset.sum_congr rfl fun h2 _ ↦ ?_
      simp only [tier1WalkIntCell_eq_byKind]
      let Z (k : ℕ) := ∑ lo1 : Fin 64, ∑ lo2 : Fin 64,
        cond (eqSec (tier1WalkByKind k u1.val h1.val h2.val lo1.val lo2.val w)
          (.nn n1 n2 e1)) 1 0
      have hz (k : ℕ) (hk : (k ≠ 2 ∧ k ≠ 3) ∧ k < 9) : Z k = 0 :=
        sum2_byKind_zero hk.2 (Or.inr fun _ _ _ ↦ rfl) (Or.inl hk.1)
          (Or.inr fun _ ↦ rfl) (Or.inr rfl) fun _ ↦ rfl
      rw [sum_q5_q31_tier1WalkTileKind Z, hz 0 (by decide), hz 1 (by decide),
          hz 4 (by decide), hz 5 (by decide), hz 6 (by decide), hz 7 (by decide),
          hz 8 (by decide), show 81 * 0 + 0 + 40 * Z 2 + Z 3 + 15 * 0 + 0 + 2 * 0 + 0 +
            13 * 0 = 40 * Z 2 + Z 3 by omega]
      dsimp only [Z]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun lo1 _ ↦ Finset.sum_congr rfl fun lo2 _ ↦ ?_
      have htag : eqSec (tier1NnTag u1.val h1.val h2.val lo1.val lo2.val) (.nn n1 n2 e1) =
          eqSec (nnCellFermat u1.val (64 * h1.val + lo1.val)
            (ultraToPinned192 (64 * h2.val + lo2.val))).1 (.nn n1 n2 e1) := by
        have _ := h2.isLt
        have _ := lo2.isLt
        dsimp only [tier1NnTag, nnCellFermat, tier1FbKin]
        rw [(ultraToPinned192_spec (by omega)).2.2,
          show Bool.not (Nat.beq (decodeUltraNuc192 (64 * h1.val + lo1.val)).2.val
              (decodeUltraNuc192 (64 * h2.val + lo2.val)).2.val) =
            (((decodeUltraNuc192 (64 * h1.val + lo1.val)).2 ==
              (decodeUltraNuc192 (64 * h2.val + lo2.val)).2) == false) by
            rw [fin47_beq_val]
            by_cases h : (decodeUltraNuc192 (64 * h1.val + lo1.val)).2.val =
                (decodeUltraNuc192 (64 * h2.val + lo2.val)).2.val
            · simp [h]
            · simp [tier1_nat_beq_eq_false_of_ne h, beq_eq_false_iff_ne.mpr h]]
        cases (decodeUltraNuc192 (64 * h1.val + lo1.val)).1 &&
          (decodeUltraNuc192 (64 * h2.val + lo2.val)).1 &&
          (((decodeUltraNuc192 (64 * h1.val + lo1.val)).2 ==
            (decodeUltraNuc192 (64 * h2.val + lo2.val)).2) == false) <;> rfl
      simp only [tier1WalkByKind]
      cases Nat.blt w 1750 <;>
        simp only [Bool.cond_false, Bool.cond_true, htag,
          show cond (eqSec (tier1FbKin u1.val h1.val) (.nn n1 n2 e1)) 1 0 = 0 from rfl] <;>
        omega
    · exact (tier1_sum_h1_h2_lo1_lo2 fun z1 raw2 ↦ (40 + cond (Nat.blt w 1750) 1 0) *
        cond (eqSec (nnCellFermat u1.val z1 (ultraToPinned192 raw2)).1 (.nn n1 n2 e1)) 1 0).trans
        (foldSum_congr fun z1 _ ↦ foldSum_perm 192 ultraToPinned192 pinnedToUltra192
          (fun r hr ↦ ⟨(ultraToPinned192_spec hr).1, (ultraToPinned192_spec hr).2.1⟩)
          (fun z hz ↦ pinnedToUltra192_spec hz) fun z2 ↦ (40 + cond (Nat.blt w 1750) 1 0) *
            cond (eqSec (nnCellFermat u1.val z1 z2).1 (.nn n1 n2 e1)) 1 0)
  rw [Finset.sum_congr rfl fun u1 _ ↦ hu1 u1,
      Finset.sum_eq_single e1
        (fun u1 _ hne ↦ foldSum_zero_of_forall fun z1 _ ↦ foldSum_zero_of_forall fun z2 _ ↦ by
          unfold nnCellFermat; dsimp only
          cases (decodeUltraNuc192 z1).1 && (decodePinnedNuc192 z2).1 &&
            (((decodeUltraNuc192 z1).2 == (decodePinnedNuc192 z2).2) == false)
          · exact Nat.mul_zero _
          · dsimp only [cond, eqSec]
            have hf : (mkFin187 u1.val == e1) = false := by
              rw [mkFin187_of_lt u1.isLt]; exact beq_eq_false_iff_ne.mpr hne
            rw [hf, Bool.and_false]; exact Nat.mul_zero _)
        (fun h ↦ absurd (Finset.mem_univ _) h)]
  have he1 : (mkFin187 e1.val == e1) = true := beq_iff_eq.mpr (mkFin187_of_lt e1.isLt)
  by_cases hlt : n1 < n2
  · simp only [hlt, ↓reduceIte]
    by_cases h33 : (nucSpecies n1).val = 3 ∧ (nucSpecies n2).val = 3
    · exact False.elim (nucSpecies_pair_not_both_three hlt ⟨Fin.ext h33.1, Fin.ext h33.2⟩)
    · simp only [h33, ↓reduceIte]
      have hbw : cond (Nat.blt w 1750) 1 0 = (if w < 1750 then 1 else 0) := by
        by_cases hw2 : w < 1750 <;> simp [hw2, Nat.blt_eq]
      trans foldSum 192 fun z1 ↦ foldSum 192 fun z2 ↦
        cond (((decodeUltraNuc192 z1).1 && ((decodeUltraNuc192 z1).2 == n1)) &&
            ((decodePinnedNuc192 z2).1 && ((decodePinnedNuc192 z2).2 == n2)))
            (40 + if w < 1750 then 1 else 0) 0 +
          cond (((decodeUltraNuc192 z1).1 && ((decodeUltraNuc192 z1).2 == n2)) &&
            ((decodePinnedNuc192 z2).1 && ((decodePinnedNuc192 z2).2 == n1)))
            (40 + if w < 1750 then 1 else 0) 0
      · refine foldSum_congr fun z1 _ ↦ foldSum_congr fun z2 _ ↦ ?_
        unfold nnCellFermat
        dsimp only
        cases (decodeUltraNuc192 z1).1 <;> cases (decodePinnedNuc192 z2).1 <;>
          simp only [Bool.false_and, Bool.true_and, Bool.and_false, Bool.cond_false] <;>
          try exact Nat.mul_zero _
        set a := (decodeUltraNuc192 z1).2
        set b := (decodePinnedNuc192 z2).2
        by_cases hab : a = b
        · rw [hab, beq_self_eq_true, show (true == false) = false from rfl, Bool.cond_false]
          dsimp only [eqSec, cond]
          rw [Nat.mul_zero]
          by_cases hb1 : b = n1
          · rw [hb1, beq_self_eq_true, beq_eq_false_iff_ne.mpr (ne_of_lt hlt)]
            rfl
          · rw [beq_eq_false_iff_ne.mpr hb1, Bool.false_and, Bool.and_false]
            rfl
        · rw [beq_eq_false_iff_ne.mpr hab,
            show (false == false) = true from rfl, Bool.cond_true]
          have hexcl {x y : Fin 47} (hxy : x.val ≤ y.val) : ((x == n2) && (y == n1)) = false :=
            Bool.eq_false_iff.mpr fun h ↦ by
              rcases Bool.and_eq_true_iff.mp h with ⟨hx, hy⟩
              rw [beq_iff_eq.mp hx, beq_iff_eq.mp hy] at hxy
              exact Nat.not_lt.mpr hxy hlt
          cases hc : Nat.blt b.val a.val
          · rw [Bool.cond_false, Bool.cond_false]
            dsimp only [eqSec]
            rw [he1, Bool.and_true,
              hexcl (Nat.not_lt.mp fun h ↦ Bool.noConfusion (hc.symm.trans (Nat.blt_eq.mpr h))),
              Bool.cond_false, Nat.add_zero, hbw]
            cases (a == n1) && (b == n2) <;> first | exact Nat.mul_zero _ | exact Nat.mul_one _
          · rw [Bool.cond_true, Bool.cond_true]
            dsimp only [eqSec]
            rw [he1, Bool.and_true, Bool.and_comm (a == n1) (b == n2),
              hexcl (Nat.le_of_lt (Nat.blt_eq.mp hc)),
              Bool.cond_false, Nat.zero_add, Bool.and_comm (b == n1) (a == n2), hbw]
            cases (a == n2) && (b == n1) <;>
              first | exact Nat.mul_zero _ | exact Nat.mul_one _
      · rw [foldSum_congr fun z1 _ ↦ foldSum_add_distrib 192 _ _, foldSum_add_distrib 192 _ _,
          foldSum2_cond_and, foldSum2_cond_and, ultraNucCnt_eq, pinnedNucCnt_eq,
          ultraNucCnt_eq, pinnedNucCnt_eq]
        ring
  · simp only [hlt, ↓reduceIte]; have hgele : n2.val ≤ n1.val := Nat.not_lt.mp hlt
    refine foldSum_zero_of_forall fun z1 _ ↦ foldSum_zero_of_forall fun z2 _ ↦ ?_
    have h0 :=
        nnPair_beq_false_of_ge (decodeUltraNuc192 z1).2 (decodePinnedNuc192 z2).2 n1 n2 e1 e1 hgele
    unfold nnCellFermat; dsimp only
    cases (decodeUltraNuc192 z1).1 <;> cases (decodePinnedNuc192 z2).1 <;>
      try exact Nat.mul_zero _
    simp only [Bool.true_and]
    cases hne : ((decodeUltraNuc192 z1).2 == (decodePinnedNuc192 z2).2) == false
    · exact Nat.mul_zero _
    · rw [hne] at h0
      dsimp only [cond] at h0 ⊢
      cases hc : eqSec _ (.nn n1 n2 e1)
      · exact Nat.mul_zero _
      · rw [hc] at h0
        dsimp only [cond] at h0
        cases hb : Nat.blt (decodePinnedNuc192 z2).2.val (decodeUltraNuc192 z1).2.val <;>
          rw [hb] at h0 <;> cases h0
end QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc

namespace QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc
set_option maxRecDepth 8192
/-- `Nat.xor`-free mirror of `tier1WalkKinNucS8` for kernel `rfl` evaluation. -/
def tier1WalkKinNucS8Pure (s8 : ℕ) (ax : Fin 3) : ZeroNEremSector × ℕ :=
  let z := (s8 / 16) % 16; let s0 := s8 % 2; let s1 := (s8 / 2) % 2; let s2 := (s8 / 4) % 2;
  let s3 := (s8 / 8) % 2; let na10 := 2 * s1 + cond (Nat.beq s0 s1) 0 1;
  let naH16 := cond (s3 == 0) (24 + 4 * s2 + na10) (32 + 4 * s2 + na10);
  let naH4 := cond ((s1 == 1) && (s0 == 0)) 23 (40 + na10)
  cond (Nat.blt z 10) (.kin (mkFin234 naH16) ax, 32768)
    (cond (Nat.blt z 12)
      (let u5 := 4 * (z % 2) + 2 * s3 + s2
       cond (Nat.blt u5 5) (.kin (mkFin234 (4 * u5 + na10)) ax, 29235)
         (cond (u5 == 5)
           (cond ((s1 == 1) && (s0 == 0))
             (.kin (mkFin234 43) ax, 25053)
             (.kin (mkFin234 (20 + na10)) ax, 29235))
           (cond (u5 == 6) (.idle, 0)
             (cond ((s1 == 1) && (s0 == 0)) (.idle, 0)
               (cond ((s1 == 1) && (s0 == 1))
                 (.kin (mkFin234 46) ax, 21933)
                 (.kin (mkFin234 (44 + na10)) ax, 25053))))))
      (cond (z == 15) (.kin (mkFin234 naH16) ax, 20509)
        (cond (Nat.blt z 14 || (s3 == 0)) (.kin (mkFin234 naH4) ax, 32768)
          (cond (s2 == 0) (.kin (mkFin234 naH4) ax, 20509) (.idle, 0)))))
theorem tier1WalkKinNucS8_eq_pure (s8 : ℕ) (ax : Fin 3) : tier1WalkKinNucS8 s8 ax =
    tier1WalkKinNucS8Pure s8 ax := by
  have hx : Nat.xor (s8 % 2) ((s8 / 2) % 2) = cond (Nat.beq (s8 % 2) ((s8 / 2) % 2)) 0 1 :=
    tier1_xor_bit (by omega) (by omega)
  unfold tier1WalkKinNucS8 tier1WalkKinNucS8Pure; dsimp only; rw [hx]
theorem check_tier1Walk_knuc_idle_sum :
    (bSum 10 1024 0 fun b ↦ 32768 - (tier1WalkKinNucBlk b).2) = 10354601 := by decide +kernel
theorem check_tier1WalkKinNucS8_nuc :
    (allTree 9 0 256 fun s8 ↦
      tier1IsNucOrIdle (tier1WalkKinNucS8Pure s8 0).1 &&
      tier1IsNucOrIdle (tier1WalkKinNucS8Pure s8 1).1 &&
      tier1IsNucOrIdle (tier1WalkKinNucS8Pure s8 2).1) = true := by decide +kernel
/-- `256`-slot per-axis nuclear `.kin` slot sum for nucleus `n < 47` in the `p = 155` regime. -/
def tier1WalkKinNucSum256 (n : ℕ) : ℕ := bSum 8 256 0 fun s8 ↦
    cond (eqSec (tier1WalkKinNucS8Pure s8 (mkFin3 0)).1 (.kin (mkFin234 n) (mkFin3 0)))
    (tier1WalkKinNucS8Pure s8 (mkFin3 0)).2 0
private def kE_tier1Walk (s : ℕ) : ℕ × ℕ :=
  match tier1WalkKinNucS8Pure s (mkFin3 0) with
  | (.kin q ax, wt) => (cond (ax == mkFin3 0) q.val 255, wt)
  | _ => (255, 0)
private def kL_tier1Walk : ℕ → List (ℕ × ℕ) | 0 => [] | m + 1 => kE_tier1Walk m :: kL_tier1Walk m
private def sKL_tier1Walk (n : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | p :: tl => sKL_tier1Walk n tl + cond (Nat.beq p.1 n) p.2 0
private def cKF_tier1Walk (tbl : List (ℕ × ℕ)) : Bool := allTree 7 0 47 fun n ↦
    Nat.beq (sKL_tier1Walk n tbl) (wKinNucSpeciesTier1Walk (nucSpecies (mkFin47 n)))
theorem check_tier1WalkKinNuc : (allTree 7 0 47 fun n ↦ Nat.beq (tier1WalkKinNucSum256 n)
    (wKinNucSpeciesTier1Walk (nucSpecies (mkFin47 n)))) = true := by
  have ha (f : ℕ) : ∀ (b l : ℕ) (p q : ℕ → Bool), (∀ x < b + l, p x = q x) →
      allTree f b l p = allTree f b l q := by
    induction f with
    | zero => exact fun _ _ _ _ _ ↦ rfl
    | succ f ih =>
      rintro b (_ | _ | l) p q h
      · rfl
      · exact h b (Nat.lt_succ_self b)
      · dsimp only [allTree]
        rw [ih b ((l + 2) / 2) p q fun _ _ ↦ h _ (by omega),
          ih (b + (l + 2) / 2) (l + 2 - (l + 2) / 2) p q fun _ _ ↦ h _ (by omega)]
  rw [ha 7 0 47 _ _ fun n hn ↦ by
    have hs (m : ℕ) : sKL_tier1Walk n (kL_tier1Walk m) = foldSum m fun s ↦
        cond (eqSec (tier1WalkKinNucS8Pure s (mkFin3 0)).1 (.kin (mkFin234 n) (mkFin3 0)))
          (tier1WalkKinNucS8Pure s (mkFin3 0)).2 0 := by
      induction m with
      | zero => rfl
      | succ m ih =>
        dsimp only [kL_tier1Walk, sKL_tier1Walk]
        rw [foldSum_succ, ih]
        refine congrArg (HAdd.hAdd _) ?_
        unfold kE_tier1Walk
        have h255 : Nat.beq 255 n = false := tier1_nat_beq_eq_false_of_ne (by omega)
        rcases tier1WalkKinNucS8Pure m (mkFin3 0) with ⟨sec, wt⟩
        cases sec with
        | kin q ax =>
          dsimp only [eqSec]; cases ax == mkFin3 0 <;> dsimp only [cond]
          · rw [h255, Bool.and_false]
          · rw [Bool.and_true]
            have hm : (mkFin234 n).val = n := Nat.mod_eq_of_lt (by omega)
            cases hq : Nat.beq q.val n
            · rw [beq_eq_false_iff_ne.mpr fun e ↦
                Bool.noConfusion (hq.symm.trans (Nat.beq_eq.mpr (hm ▸ congrArg Fin.val e)))]
            · rw [beq_iff_eq.mpr (Fin.ext (hm.symm ▸ Nat.beq_eq.mp hq))]
        | _ => dsimp only [eqSec]; rw [h255]; rfl
    rw [show tier1WalkKinNucSum256 n = sKL_tier1Walk n (kL_tier1Walk 256) from
      (foldSum_eq_bSum 8 256 _).symm.trans (hs 256).symm]]
  exact (by decide +kernel : cKF_tier1Walk (kL_tier1Walk 256) = true)
theorem tier1WalkKinNucSum256_eq (n : Fin 47) : tier1WalkKinNucSum256 n.val =
    wKinNucSpeciesTier1Walk (nucSpecies n)
    := by have hmk : mkFin47 n.val = n :=
            Fin.ext (Nat.mod_eq_of_lt n.isLt); have h :=
                                                 Nat.beq_eq.mp (allTree_zero
                                                 check_tier1WalkKinNuc n.isLt); rw [hmk] at h;
                                                 exact h
end QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc

namespace QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc
set_option maxRecDepth 8192
attribute [local irreducible] foldSum tier1WalkKinNucSum256
theorem card_decodeTier1WalkCoin_sec (s : ZeroNEremSector) :
    ((Finset.univ : Finset (Fin (2 ^ 41))).filter (fun c ↦ decodeTier1WalkCoin c = s)).card =
    (∑ u1 : Fin 187, ∑ h1 : Fin 3, ∑ h2 : Fin 3,
    (5079040 * cond (eqSec (.kin (mkFin234 (47 + u1.val)) (mkFin3 h1.val)) s) 1 0 + ∑ q5 : Fin 5,
    ∑ q31 : Fin 31, ∑ lo1 : Fin 64, ∑ lo2 : Fin 64, ∑ w11 : Fin 2048,
    cond (eqSec (tier1WalkIntCell u1.val h1.val h2.val q5.val q31.val lo1.val lo2.val w11.val)
    s) 1 0)) + 2147450880 * cond (eqSec .idle s) 1 0 + foldSum 1024 fun b ↦
    cond (eqSec (tier1WalkKinNucBlk b).1 s) (tier1WalkKinNucBlk b).2 0 +
    cond (eqSec .idle s) (32768 - (tier1WalkKinNucBlk b).2) 0 := by
  let f (sec : ZeroNEremSector) := cond (eqSec sec s) 1 0
  trans ∑ c : Fin (2 ^ 41), f (decodeTier1WalkCoin c)
  · rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    dsimp only [f]
    cases hs : eqSec (decodeTier1WalkCoin c) s
    · simp [mt (eqSec_iff _ _).mpr (Bool.eq_false_iff.mp hs)]
    · simp [(eqSec_iff _ _).mp hs]
  rw [sum_decodeTier1WalkCoin_sec f]
  refine congrArg₂ HAdd.hAdd (congrArg₂ HAdd.hAdd rfl rfl)
    ((Finset.sum_congr rfl fun hi10 _ ↦ ?_).trans
      (sum_fin_eq_foldSum 1024 fun b ↦
        cond (eqSec (tier1WalkKinNucBlk b).1 s) (tier1WalkKinNucBlk b).2 0 +
        cond (eqSec .idle s) (32768 - (tier1WalkKinNucBlk b).2) 0))
  rw [tier1_sum_fin_blt_val 32768 _ _ _ f, Nat.min_eq_right (by
    unfold tier1WalkKinNucBlk tier1WalkKinNucS8
    dsimp only
    let L {c : Bool} {p q : ZeroNEremSector × ℕ} := @tier1_cond_snd_le c p q
    have h29 : 29235 ≤ 32768 := by decide
    have h25 : 25053 ≤ 32768 := by decide
    have h21 : 21933 ≤ 32768 := by decide
    have h20 : 20509 ≤ 32768 := by decide
    exact L (Nat.zero_le _) (L (Nat.le_refl _) (L (L h29 (L (L h25 h29)
      (L (Nat.zero_le _) (L (Nat.zero_le _) (L h21 h25)))))
      (L h20 (L (Nat.le_refl _) (L h20 (Nat.zero_le _)))))))]
  dsimp only [f]
  rw [tier1_mul_cond_eqSec, tier1_mul_cond_eqSec]
/-- Exact `.idle` count (`2,498,933,873`) for `decodeTier1WalkCoin`. -/
theorem count_tier1Walk_idle : ((Finset.univ : Finset (Fin (2 ^ 41))).filter (fun c ↦
    decodeTier1WalkCoin c = .idle)).card = totalSlotsIdleTier1Walk := by
  have hid : eqSec .idle .idle = true := rfl
  have hu1 (u1 : Fin 187) : (∑ h1 : Fin 3, ∑ h2 : Fin 3,
      (5079040 * cond (eqSec (.kin (mkFin234 (47 + u1.val)) (mkFin3 h1.val)) .idle) 1 0 +
       ∑ q5 : Fin 5, ∑ q31 : Fin 31, ∑ lo1 : Fin 64, ∑ lo2 : Fin 64, ∑ w11 : Fin 2048,
         cond (eqSec (tier1WalkIntCell u1.val h1.val h2.val q5.val q31.val
           lo1.val lo2.val w11.val) .idle) 1 0)) = 1824216 := by
    trans ∑ h1 : Fin 3, ∑ h2 : Fin 3, ∑ v23 : Fin 8388608, cond (eqSec
        (cond (Nat.beq h1.val 1 && Nat.beq h2.val 0 && Nat.blt v23.val 3431948)
          (tier1FbKin u1.val 0)
          (cond (Nat.beq h1.val 2 && Nat.beq h2.val 0 && Nat.blt v23.val 2779112)
            (tier1FbKin u1.val 0)
            (cond (Nat.beq h1.val 2 && Nat.beq h2.val 2 && Nat.blt v23.val 1824216)
              .idle (tier1FbKin u1.val h1.val)))) .idle) 1 0
    · refine Finset.sum_congr rfl fun h1 _ ↦ Finset.sum_congr rfl fun h2 _ ↦ ?_
      simp only [show cond (eqSec (.kin (mkFin234 (47 + u1.val)) (mkFin3 h1.val)) .idle) 1 0 = 0
        from rfl, Nat.mul_zero, Nat.zero_add, tier1WalkIntCell_eq_byKind]
      let Z (k : ℕ) := ∑ lo1 : Fin 64, ∑ lo2 : Fin 64, ∑ w11 : Fin 2048,
        cond (eqSec (tier1WalkByKind k u1.val h1.val h2.val lo1.val lo2.val w11.val) .idle) 1 0
      have hz (k : ℕ) (hk : k ≠ 7 ∧ k < 9) : Z k = 0 :=
        Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun b _ ↦ Finset.sum_eq_zero fun _ _ ↦ by
          rw [eqSec_tier1WalkByKind_eq_false (a := a.val) (b := b.val) hk.2
            (Or.inr fun _ _ _ ↦ rfl) (Or.inr fun _ _ _ ↦ rfl) (Or.inr fun _ ↦ rfl)
            (Or.inl hk.1) fun _ ↦ rfl]
          rfl
      rw [sum_q5_q31_tier1WalkTileKind Z, hz 0 (by decide), hz 1 (by decide), hz 2 (by decide),
        hz 3 (by decide), hz 4 (by decide), hz 5 (by decide), hz 6 (by decide), hz 8 (by decide)]
      simpa only [Z, tier1WalkByKind, zero_add, add_zero, mul_zero] using
        tier1_sum_lo1_lo2_w11_v23 fun v23 ↦ cond (eqSec
          (cond (Nat.beq h1.val 1 && Nat.beq h2.val 0 && Nat.blt v23 3431948)
            (tier1FbKin u1.val 0)
            (cond (Nat.beq h1.val 2 && Nat.beq h2.val 0 && Nat.blt v23 2779112)
              (tier1FbKin u1.val 0)
              (cond (Nat.beq h1.val 2 && Nat.beq h2.val 2 && Nat.blt v23 1824216)
                .idle (tier1FbKin u1.val h1.val)))) .idle) 1 0
    · have hnb : Nat.beq 0 0 = true ∧ Nat.beq 0 1 = false ∧ Nat.beq 0 2 = false ∧
          Nat.beq 1 0 = false ∧ Nat.beq 1 1 = true ∧ Nat.beq 1 2 = false ∧
          Nat.beq 2 0 = false ∧ Nat.beq 2 1 = false ∧ Nat.beq 2 2 = true := by decide
      simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, show (2 : Fin 3).val = 2 from rfl,
        hnb, Bool.true_and, Bool.false_and, Bool.cond_false, tier1_sum_fin_blt_eqSec,
        show min 8388608 1824216 = 1824216 by omega, Finset.sum_const, Finset.card_fin,
        smul_eq_mul, show ∀ m, cond (eqSec (tier1FbKin u1.val m) .idle) 1 0 = 0 from fun _ ↦ rfl,
        hid, Bool.cond_true]
      omega
  rw [card_decodeTier1WalkCoin_sec .idle, Finset.sum_congr rfl fun u1 _ ↦ hu1 u1,
    (foldSum_congr fun b _ ↦ by
      rw [show cond (eqSec (tier1WalkKinNucBlk b).1 .idle) (tier1WalkKinNucBlk b).2 0 =
          0 by
          unfold tier1WalkKinNucBlk tier1WalkKinNucS8
          dsimp only
          let Z {c : Bool} {p q : ZeroNEremSector × ℕ} := @tier1_cond_idle_zero c p q
          exact Z rfl (Z rfl (Z (Z rfl (Z (Z rfl rfl) (Z rfl (Z rfl (Z rfl rfl)))))
            (Z rfl (Z rfl (Z rfl rfl))))),
        hid, Bool.cond_true, Nat.zero_add]).trans
      ((foldSum_eq_bSum 10 1024 _).trans check_tier1Walk_knuc_idle_sum), hid]
  simp only [Finset.sum_const, Finset.card_fin, smul_eq_mul, Bool.cond_true,
      totalSlotsIdleTier1Walk]
end QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc

namespace QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc
set_option maxRecDepth 8192
/--
Per-cell `.nn` kinetic fallback summand for a valid first nuclear index value `v1` in the `p = 155`
regime .
-/
def tier1WalkNnRowRemCell (v1 z2 : ℕ) : ℕ :=
  let d2 := decodeUltraNuc192 z2
  cond (d2.1 && Bool.not (Nat.beq v1 d2.2.val)) 298 83968
/-- Row `.nn` kinetic fallback sum across `z2 < 192` in the `p = 155` regime. -/
def tier1WalkNnRowRem (d1 : Bool × Fin 47) : ℕ :=
  cond d1.1 (bSum 8 192 0 (tier1WalkNnRowRemCell d1.2.val)) 16121856
/--
Electronic `.kin` fallback sum from `.ee` tiles (`k ∈ {0, 1}`) on axis `ax` in the `p = 155` regime.
-/
def tier1WalkEeSliceSum (ax : ℕ) : ℕ :=
  bSum 6 64 0 fun lo1 ↦
    cond (decodeUltraNuc192 (64 * ax + lo1)).1 1118472 32243712
/--
Electronic `.kin` fallback sum from `.nn` tiles (`k ∈ {2, 3}`) on axis `ax` in the `p = 155` regime.
-/
def tier1WalkNnSliceSum (ax : ℕ) : ℕ :=
  bSum 6 64 0 fun lo1 ↦ tier1WalkNnRowRem (decodeUltraNuc192 (64 * ax + lo1))
/--
Electronic `.kin` fallback sum from `.en` tiles (`k ∈ {4, 5}`) on axis `ax` in the `p = 155` regime.
-/
def tier1WalkEnSliceSum (ax : ℕ) : ℕ :=
  bSum 6 64 0 fun lo1 ↦
    cond (decodeUltraNuc192 (64 * ax + lo1)).1 32940 6291456
/--
Electronic `.kin` count from boundary + tiles `k ∈ {6, 7, 8}` on axis `ax` in the `p = 155` regime.
-/
def tier1WalkTopSpill : ℕ → ℕ
  | 0 => 457655796
  | 1 => 397681140
  | _ => 396509760
private def d2LTier1Walk : ℕ → List (Bool × ℕ)
  | 0 => []
  | m + 1 => let d := decodeUltraNuc192 m; (d.1, d.2.val) :: d2LTier1Walk m
private def sNLTier1Walk (v1 : ℕ) : List (Bool × ℕ) → ℕ
  | [] => 0
  | p :: tl => sNLTier1Walk v1 tl + cond (p.1 && Bool.not (Nat.beq v1 p.2)) 298 83968
private theorem sNLeqTier1Walk (v1 m : ℕ) : sNLTier1Walk v1 (d2LTier1Walk m) =
    foldSum m (tier1WalkNnRowRemCell v1) := by
  induction m with
  | zero => rfl
  | succ m ih => dsimp only [d2LTier1Walk, sNLTier1Walk]; rw [foldSum_succ, ih]; rfl
private def nnFCTier1Walk (tbl : List (Bool × ℕ)) (d1 : Bool × Fin 47) : ℕ :=
    cond d1.1 (sNLTier1Walk d1.2.val tbl) 16121856
private def nnFTier1Walk (tbl : List (Bool × ℕ)) (ax : ℕ) : ℕ := bSum 6 64 0 fun a ↦
    nnFCTier1Walk tbl (decodeUltraNuc192 (64 * ax + a))
private def cSlTier1Walk (tbl : List (Bool × ℕ)) : Bool :=
    (tier1WalkEeSliceSum 0 == 102707448) && (tier1WalkEeSliceSum 1 == 133832688) &&
    (tier1WalkEeSliceSum 2 == 133832688) && (nnFTier1Walk tbl 0 == 70597824) &&
    (nnFTier1Walk tbl 1 == 93188724) && (nnFTier1Walk tbl 2 == 94360104) &&
    (tier1WalkEnSliceSum 0 == 8366676) && (tier1WalkEnSliceSum 1 == 14625192) &&
    (tier1WalkEnSliceSum 2 == 14625192)
private theorem chkTier1Walk : cSlTier1Walk (d2LTier1Walk 192) = true := by decide +kernel
private theorem fEe0tier1Walk (u0 m : ℕ) : foldSum m (fun z ↦
    cond (Bool.not (Nat.beq u0 z)) 596 167936) = if u0 < m then 167936 + (m - 1) * 596 else m *
    596 := by
  induction m with
  | zero => simp [foldSum]
  | succ m ih =>
    rw [foldSum_succ, ih]
    by_cases he : u0 = m
    · subst he
      rw [Nat.beq_eq.mpr rfl]
      dsimp only [Bool.not, cond]
      split_ifs <;> omega
    · rw [tier1_nat_beq_eq_false_of_ne he]
      dsimp only [Bool.not, cond]
      split_ifs <;> omega
end QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc

namespace QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc
set_option maxRecDepth 8192
attribute [local irreducible] foldSum bSum
theorem check_tier1Walk_elec_kin_slices :
    ((tier1WalkEeSliceSum 0 == 102707448) && (tier1WalkEeSliceSum 1 == 133832688) &&
      (tier1WalkEeSliceSum 2 == 133832688) && (tier1WalkNnSliceSum 0 == 70597824) &&
      (tier1WalkNnSliceSum 1 == 93188724) && (tier1WalkNnSliceSum 2 == 94360104) &&
      (tier1WalkEnSliceSum 0 == 8366676) && (tier1WalkEnSliceSum 1 == 14625192) &&
      (tier1WalkEnSliceSum 2 == 14625192)) = true := by
  have hSeq (ax : ℕ) : tier1WalkNnSliceSum ax = nnFTier1Walk (d2LTier1Walk 192) ax :=
    (foldSum_eq_bSum 6 64 _).symm.trans ((foldSum_congr fun a _ ↦ by
      unfold tier1WalkNnRowRem nnFCTier1Walk
      rcases decodeUltraNuc192 (64 * ax + a) with ⟨_ | _, n1⟩
      · dsimp only
        rw [Bool.cond_false, Bool.cond_false]
      · dsimp only
        rw [Bool.cond_true, Bool.cond_true]
        exact (foldSum_eq_bSum 8 192 (tier1WalkNnRowRemCell n1.val)).symm.trans
          (sNLeqTier1Walk n1.val 192).symm).trans (foldSum_eq_bSum 6 64 _))
  rw [hSeq 0, hSeq 1, hSeq 2]
  exact chkTier1Walk
private abbrev UfTier1Walk (n : ℕ) : Finset (Fin n) := @Finset.univ (Fin n) (Fin.fintype n)
private theorem sfTier1Walk {n : ℕ} [inst : Fintype (Fin n)] {f g : Fin n → ℕ}
    (h : ∀ x, f x = g x) : (@Finset.sum (Fin n) ℕ _ (@Finset.univ (Fin n) inst) f) =
    (UfTier1Walk n).sum g := by
  obtain rfl := Subsingleton.elim inst (Fin.fintype n)
  exact Finset.sum_congr rfl fun x _ ↦ h x
theorem msaTier1Walk {α : Type} [Fintype α] (c : ℕ) (f g : α → ℕ) :
    c * (∑ x : α, f x) + (∑ x : α, g x) = ∑ x : α, (c * f x + g x) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
end QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc

namespace QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc
set_option maxRecDepth 8192
attribute [local irreducible] foldSum bSum
local instance (priority := 200000) (n : ℕ) : Fintype (Fin n) := Fin.fintype n
private theorem mcTier1Walk (h a : ℕ) : 64 * h + a = h * 64 + a := by omega
private theorem eeRcTier1Walk {u0 : ℕ} (hu0 : u0 < 187) (ax : Fin 3)
    (lo1 : Fin 64) : (∑ h2 : Fin 3, ∑ lo2 : Fin 64,
    cond ((decodeUltraNuc192 (64 * ax.val + lo1.val)).1 && (decodeUltraNuc192 (64 * h2.val +
    lo2.val)).1 && Bool.not (Nat.beq u0 (b11Z2OfHX h2.val lo2.val))) 596 167936) =
    cond (decodeUltraNuc192 (64 * ax.val + lo1.val)).1 1118472 32243712 := by
  generalize (decodeUltraNuc192 (64 * ax.val + lo1.val)).1 = ok1
  cases ok1
  · simp only [Bool.cond_false, Bool.false_and, Finset.sum_const, Finset.card_fin, smul_eq_mul]
  · rw [Bool.cond_true]
    let g1 (r : ℕ) := cond (Nat.blt (b11Ext192 r) 187 && Bool.not (Nat.beq u0 (b11Ext192 r)))
      596 167936
    let F (z : ℕ) := cond (Nat.blt z 187 && Bool.not (Nat.beq u0 z)) 596 167936
    have hs (n : ℕ) (hn : Nat.blt n 187 = false) : foldSum (n + 1) F = foldSum n F + 167936 := by
      rw [foldSum_succ]
      dsimp only [F]
      rw [hn, Bool.false_and, Bool.cond_false]
    rw [Finset.sum_congr rfl fun h2 _ ↦ Finset.sum_congr rfl fun b _ ↦
        (show _ = g1 (h2.val * 64 + b.val) by
          have _ := h2.isLt
          have _ := b.isLt
          dsimp only [g1]
          obtain ⟨_, _, hbLt, hbEq⟩ := b11Ext192_spec (raw := h2.val * 64 + b.val) (by omega)
          rw [Bool.true_and, mcTier1Walk h2.val b.val]
          generalize (decodeUltraNuc192 (h2.val * 64 + b.val)).1 = ok2 at hbLt hbEq ⊢
          cases ok2
          · rw [hbLt, Bool.false_and, Bool.false_and]
          · rw [hbLt, hbEq rfl, show (h2.val * 64 + b.val) / 64 = h2.val by omega,
              show (h2.val * 64 + b.val) % 64 = b.val by omega]),
      ← sum_fin_mul (A := 3) (B := 64) (Nat.succ_pos _) g1, sum_fin_eq_foldSum 192 g1,
      foldSum_perm 192 b11Ext192 b11ExtInv192
        (fun r hr ↦ ⟨(b11Ext192_spec hr).1, (b11Ext192_spec hr).2.1⟩)
        (fun z hz ↦ b11ExtInv192_spec hz) F,
      hs 191 rfl, hs 190 rfl, hs 189 rfl, hs 188 rfl, hs 187 rfl,
      foldSum_congr (g := fun z ↦ cond (Bool.not (Nat.beq u0 z)) 596 167936) fun z hz ↦ by
        dsimp only [F]
        rw [Nat.blt_eq.mpr hz, Bool.true_and],
      fEe0tier1Walk u0 187]
    simp only [hu0, ↓reduceIte]
theorem nnRETier1Walk (d1 : Bool × Fin 47) : (∑ h2 : Fin 3, ∑ b : Fin 64,
    cond (d1.1 && (decodeUltraNuc192 (64 * h2.val + b.val)).1 &&
      Bool.not (Nat.beq d1.2.val (decodeUltraNuc192 (64 * h2.val + b.val)).2.val)) 298 83968) =
    tier1WalkNnRowRem d1 := by
  rcases d1 with ⟨_ | _, n1⟩
  · simp only [tier1WalkNnRowRem, Bool.cond_false, Bool.false_and, Finset.sum_const,
      Finset.card_fin, smul_eq_mul]
  · simp only [tier1WalkNnRowRem, Bool.cond_true, Bool.true_and, mcTier1Walk]
    exact (sum_fin_mul (A := 3) (B := 64) (Nat.succ_pos _)
      (tier1WalkNnRowRemCell n1.val)).symm.trans
      ((sum_fin_eq_foldSum 192 _).trans (foldSum_eq_bSum 8 192 _))
end QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc

namespace QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc
set_option maxRecDepth 8192
attribute [local irreducible] foldSum bSum
private abbrev eeBTier1Walk (u1 h1 h2 a b : ℕ) : Bool :=
    (decodeUltraNuc192 (64 * h1 + a)).1 && (decodeUltraNuc192 (64 * h2 + b)).1 &&
    Bool.not (Nat.beq u1 (b11Z2OfHX h2 b))
private abbrev nnBTier1Walk (h1 h2 a b : ℕ) : Bool :=
    (decodeUltraNuc192 (64 * h1 + a)).1 && (decodeUltraNuc192 (64 * h2 + b)).1 &&
    Bool.not (Nat.beq (decodeUltraNuc192 (64 * h1 + a)).2.val (decodeUltraNuc192 (64 * h2 +
    b)).2.val)
theorem pSlTier1Walk (c vF kA kB : ℕ) (K : ℕ → ℕ) (hK : ∀ y, K y ≤ 2048) (hF : c * 2048 + 2048 = vF)
    (tag : ℕ → ℕ → ℕ → ℕ → ZeroNEremSector) (b : ℕ → ℕ → ℕ → ℕ → Bool) (row : ℕ → ℕ)
    {u0 : Fin 187} {i : Particle_frozen} (ax : Fin 3) (hpi : mkFin234 (47 + u0.val) = i)
    (hkA : ∀ h1 h2 x y w, tier1WalkByKind kA u0.val h1 h2 x y w = tag h1 h2 x y)
    (hkB : ∀ h1 h2 x y {w}, w < 2048 → tier1WalkByKind kB u0.val h1 h2 x y w =
      cond (Nat.blt w (K y)) (tag h1 h2 x y) (tier1FbKin u0.val h1))
    (htag : ∀ h1 h2 x y, cond (eqSec (tag h1 h2 x y) (.kin i ax)) 1 0 =
      cond (b h1 h2 x y) 0 (cond (eqSec (tier1FbKin u0.val h1) (.kin i ax)) 1 0))
    (hrow : ∀ a : Fin 64,
      (∑ h2 : Fin 3, ∑ y : Fin 64, cond (b ax.val h2.val a.val y.val) (2048 - K y.val) vF) =
        row a.val) :
    (∑ h1 : Fin 3, ∑ h2 : Fin 3,
      (c * (∑ x : Fin 64, ∑ y : Fin 64, ∑ w : Fin 2048,
        cond (eqSec (tier1WalkByKind kA u0.val h1.val h2.val x.val y.val w.val)
            (.kin i ax)) 1 0) +
       (∑ x : Fin 64, ∑ y : Fin 64, ∑ w : Fin 2048,
        cond (eqSec (tier1WalkByKind kB u0.val h1.val h2.val x.val y.val w.val)
          (.kin i ax)) 1 0))) = bSum 6 64 0 row := by
  trans ∑ h1 : Fin 3, ∑ h2 : Fin 3,
    cond (h1 == ax) (∑ x : Fin 64, ∑ y : Fin 64,
      cond (b h1.val h2.val x.val y.val) (2048 - K y.val) vF) 0
  · refine Finset.sum_congr rfl fun h1 _ ↦ Finset.sum_congr rfl fun h2 _ ↦ ?_
    simp only [hkA]
    have hfb := tier1FbKin_eq_ax ax hpi h1.isLt
    simp only [Fin.eta] at hfb
    trans ∑ x : Fin 64, ∑ y : Fin 64,
      cond (h1 == ax) (cond (b h1.val h2.val x.val y.val) (2048 - K y.val) vF) 0
    · rw [msaTier1Walk]
      refine Finset.sum_congr rfl fun x _ ↦
        (msaTier1Walk c _ _).trans (Finset.sum_congr rfl fun y _ ↦ ?_)
      have hk := hK y.val
      rw [Finset.sum_const, Finset.card_fin, smul_eq_mul,
        Finset.sum_congr rfl fun w _ ↦ by rw [hkB h1.val h2.val x.val y.val w.isLt],
        tier1_sum_fin_blt_eqSec, Nat.min_eq_right hk, htag h1.val h2.val x.val y.val, hfb]
      generalize b h1.val h2.val x.val y.val = bx, (h1 == ax) = hx, K y.val = ky at hk ⊢
      cases bx <;> cases hx <;> dsimp only [cond] <;> omega
    · cases (h1 == ax)
      · exact Finset.sum_eq_zero fun _ _ ↦ Finset.sum_eq_zero fun _ _ ↦ rfl
      · rfl
  · rw [Finset.sum_eq_single ax (fun h1 _ hne ↦ Finset.sum_eq_zero fun _ _ ↦ by
        rw [beq_eq_false_iff_ne.mpr hne]
        rfl) (fun h ↦ absurd (Finset.mem_univ _) h)]
    exact (Finset.sum_congr rfl fun _ _ ↦ by rw [beq_self_eq_true, Bool.cond_true]).trans
      (Finset.sum_comm.trans ((Finset.sum_congr rfl fun a _ ↦ hrow a).trans
        ((sum_fin_eq_foldSum 64 row).trans (foldSum_eq_bSum 6 64 row))))
theorem tier1Walk_int_kin_elec {u0 : Fin 187} {i : Particle_frozen} (ax : Fin 3)
    (hpi : mkFin234 (47 + u0.val) = i) :
    (∑ h1 : Fin 3, ∑ h2 : Fin 3,
      (5079040 * cond (eqSec (.kin (mkFin234 (47 + u0.val)) (mkFin3 h1.val)) (.kin i ax)) 1 0 +
       ∑ q5 : Fin 5, ∑ q31 : Fin 31, ∑ lo1 : Fin 64, ∑ lo2 : Fin 64, ∑ w11 : Fin 2048,
         cond (eqSec (tier1WalkIntCell u0.val h1.val h2.val q5.val q31.val lo1.val lo2.val
             w11.val)
           (.kin i ax)) 1 0)) = wKinElecTier1Walk := by
  let f (sec : ZeroNEremSector) := cond (eqSec sec (.kin i ax)) 1 0
  let B (k : ℕ) (h1 h2 : Fin 3) := ∑ lo1 : Fin 64, ∑ lo2 : Fin 64, ∑ w11 : Fin 2048,
    f (tier1WalkByKind k u0.val h1.val h2.val lo1.val lo2.val w11.val)
  let E (h1 h2 : Fin 3) := 81 * B 0 h1 h2 + B 1 h1 h2
  let N (h1 h2 : Fin 3) := 40 * B 2 h1 h2 + B 3 h1 h2
  let EN (h1 h2 : Fin 3) := 15 * B 4 h1 h2 + B 5 h1 h2
  let TS (h1 h2 : Fin 3) :=
    5079040 * f (tier1FbKin u0.val h1.val) + 2 * B 6 h1 h2 + B 7 h1 h2 + 13 * B 8 h1 h2
  have hts : (∑ h1 : Fin 3, ∑ h2 : Fin 3, TS h1 h2) = tier1WalkTopSpill ax.val := by
    dsimp only [TS, B, f, tier1WalkByKind]
    have hw7 (h1 h2 : Fin 3) := tier1_sum_lo1_lo2_w11_v23 fun v23 ↦ cond (eqSec
      (cond (Nat.beq h1.val 1 && Nat.beq h2.val 0 && Nat.blt v23 3431948) (tier1FbKin u0.val 0)
        (cond (Nat.beq h1.val 2 && Nat.beq h2.val 0 && Nat.blt v23 2779112) (tier1FbKin u0.val 0)
          (cond (Nat.beq h1.val 2 && Nat.beq h2.val 2 && Nat.blt v23 1824216) .idle
            (tier1FbKin u0.val h1.val)))) (.kin i ax)) 1 0
    have hnb : Nat.beq 0 0 = true ∧ Nat.beq 0 1 = false ∧ Nat.beq 0 2 = false ∧
        Nat.beq 1 0 = false ∧ Nat.beq 1 1 = true ∧ Nat.beq 1 2 = false ∧
        Nat.beq 2 0 = false ∧ Nat.beq 2 1 = false ∧ Nat.beq 2 2 = true := by decide
    have hf (m : ℕ) (hm : m < 3) :
        cond (eqSec (tier1FbKin u0.val m) (.kin i ax)) 1 0 = cond (Nat.beq m ax.val) 1 0 := by
      rw [tier1FbKin_eq_ax ax hpi hm]
      cases h : Nat.beq m ax.val
      · rw [beq_eq_false_iff_ne.mpr fun he ↦
          Bool.noConfusion (h.symm.trans (Nat.beq_eq.mpr (congrArg Fin.val he)))]
      · rw [beq_iff_eq.mpr (Fin.ext (Nat.beq_eq.mp h))]
    simp only [hw7, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, show (2 : Fin 3).val = 2 from
      rfl, hnb, Bool.true_and, Bool.false_and, Bool.cond_true, Bool.cond_false,
      tier1_sum_fin_blt_eqSec, show min 8388608 3431948 = 3431948 by omega,
      show min 8388608 2779112 = 2779112 by omega, show min 8388608 1824216 = 1824216 by omega,
      Finset.sum_const, Finset.card_fin, smul_eq_mul, show cond (eqSec .idle (.kin i ax)) 1 0 = 0
        from rfl, hf 0 (by omega), hf 1 (by omega), hf 2 (by omega)]
    have _ := ax.isLt
    rcases (by omega : ax.val = 0 ∨ ax.val = 1 ∨ ax.val = 2) with hv | hv | hv <;>
      rw [hv] <;> simp only [hnb, Bool.cond_true, Bool.cond_false, tier1WalkTopSpill] <;>
          norm_num
  rw [Finset.sum_congr rfl fun h1 _ ↦ Finset.sum_congr rfl fun h2 _ ↦
        (show _ = E h1 h2 + N h1 h2 + EN h1 h2 + TS h1 h2 by
          dsimp only [E, N, EN, TS, B]
          simp only [tier1WalkIntCell_eq_byKind]
          rw [sum_q5_q31_tier1WalkTileKind (fun k ↦ B k h1 h2)]
          unfold tier1FbKin
          ring),
      tier1_sum2_add4 E N EN TS, hts]
  dsimp only [E, N, EN, B, f]
  rw [pSlTier1Walk 81 167936 0 1 (fun _ ↦ 1452) (fun _ ↦ by decide) rfl (tier1EeTag u0.val)
        (eeBTier1Walk u0.val)
            (fun a ↦ cond (decodeUltraNuc192 (64 * ax.val + a)).1 1118472 32243712)
        ax hpi (fun _ _ _ _ _ ↦ rfl) (fun _ _ _ _ {_} _ ↦ rfl)
        (fun h1 h2 x y ↦ by
          unfold tier1EeTag eeBTier1Walk
          dsimp only
          cases _ && _ && _ <;> rfl)
        (fun a ↦ (sfTier1Walk fun _ ↦ sfTier1Walk fun _ ↦ rfl).trans (eeRcTier1Walk u0.isLt ax a)),
      pSlTier1Walk 40 83968 2 3 (fun _ ↦ 1750)
          (fun _ ↦ by decide) rfl (tier1NnTag u0.val) nnBTier1Walk
        (fun a ↦ tier1WalkNnRowRem (decodeUltraNuc192 (64 * ax.val + a)))
        ax hpi (fun _ _ _ _ _ ↦ rfl) (fun _ _ _ _ {_} _ ↦ rfl)
        (fun h1 h2 x y ↦ by
          unfold tier1NnTag nnBTier1Walk
          dsimp only
          cases _ && _ && _ <;> rfl)
        (fun a ↦ (sfTier1Walk fun _ ↦ sfTier1Walk fun _ ↦ rfl).trans
          (nnRETier1Walk (decodeUltraNuc192 (64 * ax.val + a.val)))),
      pSlTier1Walk 15 32768 4 5 (fun y ↦ cond (Nat.blt y 56) 2048 (cond (Nat.blt y 60) 1351 0))
        (fun y ↦ by cases Nat.blt y 56 <;> cases Nat.blt y 60 <;> decide) rfl
        (fun h1 _ x _ ↦ tier1EnTag u0.val h1 x)
        (fun h1 _ x _ ↦ (decodeUltraNuc192 (64 * h1 + x)).1)
        (fun a ↦ cond (decodeUltraNuc192 (64 * ax.val + a)).1 32940 6291456)
        ax hpi (fun _ _ _ _ _ ↦ rfl)
        (fun _ _ _ y {_} hw ↦ by
          dsimp only [tier1WalkByKind]
          refine congrArg (fun c ↦ cond c _ _) ?_
          cases Nat.blt y 56 <;> dsimp only [cond, Bool.true_or, Bool.false_or]
          · cases Nat.blt y 60 <;> dsimp only [cond, Bool.true_and, Bool.false_and]
            · exact (Bool.eq_false_iff.mpr fun h ↦ Nat.not_lt_zero _ (Nat.blt_eq.mp h)).symm
            · rfl
          · exact (Nat.blt_eq.mpr hw).symm)
        (fun h1 _ x _ ↦ by
          dsimp only [tier1EnTag]
          cases (decodeUltraNuc192 (64 * h1 + x)).1 <;> rfl)
        (fun a ↦ by
          cases (decodeUltraNuc192 (64 * ax.val + a.val)).1 <;>
            simp only [Bool.cond_true, Bool.cond_false, Finset.sum_const, Finset.card_fin,
              smul_eq_mul]
          decide)]
  change tier1WalkEeSliceSum ax.val + tier1WalkNnSliceSum ax.val +
      tier1WalkEnSliceSum ax.val + tier1WalkTopSpill ax.val = wKinElecTier1Walk
  have hchk := check_tier1Walk_elec_kin_slices
  simp only [Bool.and_eq_true, beq_iff_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨⟨⟨⟨e0, e1s⟩, e2s⟩, n0⟩, n1s⟩, n2s⟩, en0⟩, en1⟩, en2⟩
  have _ := ax.isLt
  rcases (by omega : ax.val = 0 ∨ ax.val = 1 ∨ ax.val = 2) with hv | hv | hv <;>
    simp only [hv, e0, e1s, e2s, n0, n1s, n2s, en0, en1, en2] <;> rfl
end QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc

namespace QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc
attribute [local irreducible] foldSum
local instance (priority := 200000) (n : ℕ) : Fintype (Fin n) := Fin.fintype n
private theorem fib_en_tier1Walk_w11Nat_core (n1 : Fin 47) (e1 : Fin 187) {w : ℕ}
    (hw : w < 2048) : ((Finset.univ : Finset (Fin (2 ^ 41))).filter (fun c ↦
    decodeTier1WalkCoin c = .en n1 e1 ∧ w11NatOfCoin c = w)).card = speciesZ (nucSpecies n1) *
    (3048 + 12 * if w < 1351 then 1 else 0) := by
  rw [card_decodeTier1WalkCoin_pot_w11 (by rintro ⟨⟩) (by rintro _ _ ⟨⟩) hw,
    Finset.sum_eq_single e1 (fun u1 _ hne ↦ Finset.sum_eq_zero fun _ _ ↦
      Finset.sum_eq_zero fun _ _ ↦ Finset.sum_eq_zero fun q5 _ ↦ Finset.sum_eq_zero fun q31 _ ↦
        Finset.sum_eq_zero fun _ _ ↦ Finset.sum_eq_zero fun _ _ ↦ by
          rw [eqSec_tier1WalkIntCell_eq_false q5 q31 rfl (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)
            (fun _ _ _ ↦ rfl) fun _ ↦ by
              dsimp only [eqSec]
              rw [mkFin187_of_lt u1.isLt, beq_eq_false_iff_ne.mpr hne, Bool.and_false]]
          rfl) (fun h ↦ absurd (Finset.mem_univ _) h)]
  have he1 : (mkFin187 e1.val == e1) = true := beq_iff_eq.mpr (mkFin187_of_lt e1.isLt)
  let K := 1016 + 4 * if w < 1351 then 1 else 0
  trans ∑ h1 : Fin 3, ∑ h2 : Fin 3, ∑ lo1 : Fin 64,
    cond ((decodeUltraNuc192 (h1.val * 64 + lo1.val)).1 &&
      ((decodeUltraNuc192 (h1.val * 64 + lo1.val)).2 == n1)) K 0
  · refine Finset.sum_congr rfl fun h1 _ ↦ Finset.sum_congr rfl fun h2 _ ↦ ?_
    simp only [tier1WalkIntCell_eq_byKind]
    let Z (k : ℕ) := ∑ lo1 : Fin 64, ∑ lo2 : Fin 64,
      cond (eqSec (tier1WalkByKind k e1.val h1.val h2.val lo1.val lo2.val w) (.en n1 e1)) 1 0
    have hz (k : ℕ) (hk : (k ≠ 4 ∧ k ≠ 5) ∧ k < 9) : Z k = 0 :=
      sum2_byKind_zero hk.2 (Or.inr fun _ _ _ ↦ rfl) (Or.inr fun _ _ _ ↦ rfl)
        (Or.inl hk.1) (Or.inr rfl) fun _ ↦ rfl
    rw [sum_q5_q31_tier1WalkTileKind Z, hz 0 (by decide), hz 1 (by decide), hz 2 (by decide),
      hz 3 (by decide), hz 6 (by decide), hz 7 (by decide), hz 8 (by decide),
      show 81 * 0 + 0 + 40 * 0 + 0 + 15 * Z 4 + Z 5 + 2 * 0 + 0 + 13 * 0 =
        15 * Z 4 + Z 5 by omega]
    dsimp only [Z]
    simp only [tier1WalkByKind, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun lo1 _ ↦ ?_
    unfold tier1EnTag tier1FbKin
    dsimp only
    rw [show 64 * h1.val + lo1.val = h1.val * 64 + lo1.val by ring]
    cases (decodeUltraNuc192 (h1.val * 64 + lo1.val)).1
    · simp only [Bool.false_and, Bool.cond_false]
      exact Finset.sum_eq_zero fun lo2 _ ↦ by cases Nat.blt lo2.val 56 || _ <;> rfl
    · simp only [Bool.true_and, Bool.cond_true]
      cases hn : ((decodeUltraNuc192 (h1.val * 64 + lo1.val)).2 == n1)
      · simp only [Bool.cond_false]
        exact Finset.sum_eq_zero fun x _ ↦ by cases Nat.blt x.val 56 || _ <;> simp [eqSec, hn]
      · rw [beq_iff_eq.mp hn]
        have hfe : cond (eqSec (.en n1 (mkFin187 e1.val)) (.en n1 e1)) 1 0 = 1 := by
          simp [eqSec, he1]
        simp only [Bool.cond_true, Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin,
          smul_eq_mul, hfe, mul_one]
        rw [Finset.sum_congr
            (g := fun lo2 : Fin 64 ↦ cond (Nat.blt lo2.val (cond (Nat.blt w 1351) 60 56)) 1 0)
            rfl fun lo2 _ ↦ by
              cases Nat.blt w 1351 <;> simp only [Bool.and_false, Bool.or_false, Bool.and_true,
                Bool.cond_false, Bool.cond_true]
              · cases Nat.blt lo2.val 56 <;> first | rfl | exact hfe
              · cases hb1 : Nat.blt lo2.val 56
                · rw [Bool.false_or]
                  cases Nat.blt lo2.val 60 <;> first | rfl | exact hfe
                · rw [Bool.true_or, Nat.blt_eq.mpr (Nat.lt_trans (Nat.blt_eq.mp hb1) (by decide))]
                  exact hfe,
          tier1_sum_fin_blt_min]
        dsimp only [K]
        by_cases hw1351 : w < 1351 <;> simp [hw1351, Nat.blt_eq]
  rw [
    Finset.sum_comm, Finset.sum_congr rfl fun _ _ ↦
      (show _ = speciesZ (nucSpecies n1) * K by
        let fn (z1 : ℕ) :=
          cond ((decodeUltraNuc192 z1).1 && ((decodeUltraNuc192 z1).2 == n1)) K 0
        rw [← sum_fin_mul (A := 3) (B := 64) (Nat.succ_pos _) fn,
          sum_fin_eq_foldSum 192 fn, foldSum_cond_const, ultraNucCnt_eq]),
    Fin.sum_univ_three]
  dsimp only [K]
  ring
end QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc

namespace QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc
attribute [local irreducible] foldSum
/--
Closed-form `.en` `W11` fiber multiplicity on `w < 2048` (`0x000` polarity) for the `p = 155`
regime.
-/
theorem fib_en_tier1Walk_w11Nat (n1 : Fin 47) (e1 : Fin 187) {w : ℕ} (hw : w < 2048) :
    ((Finset.univ : Finset (Fin (2 ^ 41))).filter
      (fun c ↦ decodeTier1WalkCoin c = .en n1 e1 ∧ w11NatOfCoin c = w)).card =
      speciesZ (nucSpecies n1) * (3048 + 12 * if w < 1351 then 1 else 0) := by
  rw [congrArg (@Finset.univ (Fin (2 ^ 41))) (Subsingleton.elim _ (Fin.fintype (2 ^ 41)))]
  exact fib_en_tier1Walk_w11Nat_core n1 e1 hw
/--
Closed-form `.ee` `W11` fiber count on integer fiber `w < 2048` (`0x000` polarity) for the `p = 155`
regime .
-/
def cntEE2048Tier1Walk (s : Fin 4) (w : ℕ) : ℕ :=
  2 * mSpCart254 s * (81 + if w < 1452 then 1 else 0)
/--
Closed-form `.nn` `W11` fiber count on integer fiber `w < 2048` (`0x000` polarity) for the `p = 155`
regime .
-/
def cntNN2048Tier1Walk (s1 s2 : Fin 4) (w : ℕ) : ℕ :=
  if s1.val = 3 ∧ s2.val = 3 then 0
  else mSpCart254 s1 * mSpCart254 s2 * (80 + 2 * if w < 1750 then 1 else 0)
private theorem fin4_cases_tier1Walk (s : Fin 4) : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by
  rcases s with ⟨_ | _ | _ | _ | n, hn⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))
  · omega
private theorem sum_fin_const_tier1Walk (M c : ℕ) : (∑ _ : Fin M, c) = M * c := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
private theorem sum_ee_gen_tier1Walk {M t : ℕ} (ht : t ≤ M)
    (m c : ℕ) : (∑ u : Fin M, m * (c + if u.val < t then 1 else 0)) = m * (M * c + t)
    := by rw [← Finset.mul_sum, Finset.sum_add_distrib, sum_fin_const_tier1Walk, sum_fin_lt_nat ht]
private theorem sum_lin_lt_tier1Walk {M t : ℕ} (ht : t ≤ M)
    (m c k : ℕ) : (∑ u : Fin M, m * (c + k * if u.val < t then 1 else 0)) = m * (M * c + k * t)
    := by rw [← Finset.mul_sum, Finset.sum_add_distrib, sum_fin_const_tier1Walk, ← Finset.mul_sum,
            sum_fin_lt_nat ht]
theorem sum_cntEE2048Tier1Walk (s : Fin 4) : (∑ u : Fin 2048,
    cntEE2048Tier1Walk s u.val) = wEESpeciesTier1Walk s :=
  (Finset.sum_congr rfl fun _ _ ↦ rfl).trans
    ((sum_ee_gen_tier1Walk (Nat.le_of_lt (Nat.blt_eq.mp rfl)) (2 * mSpCart254 s) 81).trans
      (by rcases fin4_cases_tier1Walk s with rfl | rfl | rfl | rfl <;> rfl))
theorem sum_cntNN2048Tier1Walk (s1 s2 : Fin 4) : (∑ u : Fin 2048,
    cntNN2048Tier1Walk s1 s2 u.val) = wNNSpeciesTier1Walk s1 s2 := by
  by_cases h33 : s1.val = 3 ∧ s2.val = 3
  · refine (Finset.sum_eq_zero fun _ _ ↦ ite_eq_left h33).trans ?_
    unfold wNNSpeciesTier1Walk
    exact (ite_eq_left h33).symm
  · refine (Finset.sum_congr rfl fun _ _ ↦ ite_eq_right h33).trans
      ((sum_lin_lt_tier1Walk (Nat.le_of_lt (Nat.blt_eq.mp rfl))
        (mSpCart254 s1 * mSpCart254 s2) 80 2).trans ?_)
    rcases fin4_cases_tier1Walk s1 with rfl | rfl | rfl | rfl <;>
      rcases fin4_cases_tier1Walk s2 with rfl | rfl | rfl | rfl <;>
      first | (exfalso; exact h33 ⟨rfl, rfl⟩) | rfl
end QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc
end

namespace QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc
open QuantumComputation.Specs
  PhotochemistrySolution.ZeroNEremSpec
open _root_.QuantumComputation.Specs.PhotochemistrySolution.GenWeightsSelect (ValidGenZeroNEremCoin)
attribute [local irreducible] foldSum
/-- Exact `2 ^ 41` multiplicity certificate for `decodeTier1WalkCoin`. -/
theorem validTier1WalkCoin_decodeTier1WalkCoin : ValidTier1WalkCoin decodeTier1WalkCoin :=
    fun s ↦ by
  rw [Finset.filter_congr_decidable (p := fun c ↦ decodeTier1WalkCoin c = s)]
  cases s with
  | idle => exact count_tier1Walk_idle
  | ee n1 e1 e2 =>
    rw [tier1_card_filter_eq_sum_w11Nat]
    refine (Finset.sum_congr rfl fun u _ ↦ (fib_ee_tier1Walk_w11Nat n1 e1 e2 u.isLt).trans
      (show _ = if e1 < e2 then cntEE2048Tier1Walk (nucSpecies n1) u.val else 0 by
        unfold cntEE2048Tier1Walk
        rw [tier1_speciesZ_eq_mSp])).trans ?_
    by_cases h : e1 < e2 <;>
      simp only [h, ↓reduceIte, Finset.sum_const_zero, sum_cntEE2048Tier1Walk]
  | nn n1 n2 e1 =>
    rw [tier1_card_filter_eq_sum_w11Nat]
    refine (Finset.sum_congr rfl fun u _ ↦ (fib_nn_tier1Walk_w11Nat n1 n2 e1 u.isLt).trans
      (show _ = if n1 < n2 then cntNN2048Tier1Walk (nucSpecies n1)
          (nucSpecies n2) u.val else 0 by
        unfold cntNN2048Tier1Walk
        rw [tier1_speciesZ_eq_mSp, tier1_speciesZ_eq_mSp])).trans ?_
    by_cases h : n1 < n2 <;>
      simp only [h, ↓reduceIte, Finset.sum_const_zero, sum_cntNN2048Tier1Walk]
  | en n1 e1 =>
    rw [tier1_card_filter_eq_sum_w11Nat]
    exact (Finset.sum_congr rfl fun u _ ↦ (fib_en_tier1Walk_w11Nat n1 e1 u.isLt).trans
      (show _ = mSpCart254 (nucSpecies n1) * (3048 + 12 * if u.val < 1351 then 1 else 0) by
        rw [tier1_speciesZ_eq_mSp])).trans
      ((sum_lin_lt_tier1Walk (t := 1351) (by decide) (mSpCart254 (nucSpecies n1)) 3048 12).trans
        (by
          dsimp only
          rcases fin4_cases_tier1Walk (nucSpecies n1) with h | h | h | h <;> rw [h] <;> rfl))
  | kin i ax =>
    rw [card_decodeTier1WalkCoin_sec (.kin i ax),
      show cond (eqSec .idle (.kin i ax)) 1 0 = 0 from rfl, Nat.mul_zero, Nat.add_zero]
    have hidb (b : ℕ) : cond (eqSec .idle (.kin i ax)) (32768 - (tier1WalkKinNucBlk b).2) 0 =
        0 :=
      rfl
    have hzero_u1 (u1 : Fin 187) (h1 h2 : Fin 3) (hne : mkFin234 (47 + u1.val) ≠ i) :
        5079040 * cond (eqSec (.kin (mkFin234 (47 + u1.val)) (mkFin3 h1.val)) (.kin i ax)) 1 0 +
        (∑ q5 : Fin 5, ∑ q31 : Fin 31, ∑ lo1 : Fin 64, ∑ lo2 : Fin 64, ∑ w11 : Fin 2048,
          cond (eqSec (tier1WalkIntCell u1.val h1.val h2.val q5.val q31.val
            lo1.val lo2.val w11.val) (.kin i ax)) 1 0) = 0 := by
      have hfb (m : ℕ) : eqSec (tier1FbKin u1.val m) (.kin i ax) = false := by
        unfold tier1FbKin
        dsimp only [eqSec]
        rw [beq_eq_false_iff_ne.mpr hne, Bool.false_and]
      rw [show ZeroNEremSector.kin (mkFin234 (47 + u1.val)) (mkFin3 h1.val) =
            tier1FbKin u1.val h1.val from rfl,
          hfb h1.val, Bool.cond_false, Nat.mul_zero, Nat.zero_add]
      exact Finset.sum_eq_zero fun q5 _ ↦ Finset.sum_eq_zero fun q31 _ ↦
        Finset.sum_eq_zero fun _ _ ↦ Finset.sum_eq_zero fun _ _ ↦ Finset.sum_eq_zero fun _ _ ↦ by
          rw [eqSec_tier1WalkIntCell_eq_false q5 q31 rfl hfb (fun _ _ _ ↦ rfl)
            (fun _ _ _ ↦ rfl) fun _ ↦ rfl]
          rfl
    rcases lt_or_ge i.val 47 with hi47 | hi47
    · rw [Finset.sum_eq_zero (fun u1 _ ↦ Finset.sum_eq_zero fun h1 _ ↦ Finset.sum_eq_zero
          fun h2 _ ↦ hzero_u1 u1 h1 h2 fun hm ↦ by
            have hv := congrArg Fin.val hm
            dsimp only [mkFin234] at hv
            rw [Nat.mod_eq_of_lt (by omega)] at hv
            omega),
        Nat.zero_add]
      let g (b : ℕ) := cond (eqSec (tier1WalkKinNucBlk b).1 (.kin i ax))
        (tier1WalkKinNucBlk b).2 0
      rw [show (1024 : ℕ) = 768 + 256 from rfl,
        foldSum_congr (g := g) (fun b _ ↦ by rw [hidb b, Nat.add_zero]),
        foldSum_add_split 768 256 g, foldSum_zero_of_forall (M := 256) (fun r _ ↦ by
          dsimp only [g]
          unfold tier1WalkKinNucBlk
          rw [Nat.ble_eq.mpr (Nat.le_add_right 768 r)]
          rfl),
        Nat.add_zero, foldSum_mul3 256 g]
      have hsl (ax0 : Fin 3) : (foldSum 256 fun s8 ↦ g (ax0.val * 256 + s8)) =
          cond (ax0.val == ax.val) (tier1WalkKinNucSum256 i.val) 0 := by
        have hax := ax0.isLt
        rw [foldSum_congr (g := fun s8 ↦ cond (ax0.val == ax.val)
            (cond (eqSec (tier1WalkKinNucS8Pure s8 0).1 (.kin i 0))
              (tier1WalkKinNucS8Pure s8 0).2 0) 0) fun s8 hs8 ↦ by
          dsimp only [g]
          unfold tier1WalkKinNucBlk
          rw [Bool.eq_false_iff.mpr fun h ↦ absurd (Nat.ble_eq.mp h) (by omega), Bool.cond_false,
            show (ax0.val * 256 + s8) / 256 = ax0.val by omega,
            show (ax0.val * 256 + s8) % 256 = s8 by omega,
            show mkFin3 ax0.val = ax0 from Fin.ext (Nat.mod_eq_of_lt hax),
            tier1WalkKinNucS8_eq_pure]
          have hid0 : cond (eqSec (ZeroNEremSector.idle, 0).1 (.kin i ax)) 0 0 =
              cond (ax0.val == ax.val)
                (cond (eqSec (ZeroNEremSector.idle, 0).1 (.kin i 0)) 0 0) 0 := by
            cases (ax0.val == ax.val) <;> rfl
          have hc (p : Particle_frozen) (t : ℕ) :
              cond (eqSec (.kin p ax0) (.kin i ax)) t 0 =
              cond (ax0.val == ax.val) (cond (eqSec (.kin p 0) (.kin i 0)) t 0) 0 := by
            dsimp only [eqSec]
            rw [
              show ((0 : Fin 3) == 0) = true from rfl, Bool.and_true]
            cases (ax0.val == ax.val)
            · rw [Bool.and_false]
              rfl
            · rw [Bool.and_true]
              rfl
          let S {c : Bool} {px p0 qx q0 : ZeroNEremSector × ℕ} :=
            @tier1_cond_shift c px p0 qx q0 ax0 ax i
          unfold tier1WalkKinNucS8Pure
          dsimp only
          exact S (hc _ _) (S (S (hc _ _) (S (S (hc _ _) (hc _ _))
            (S hid0 (S hid0 (S (hc _ _) (hc _ _))))))
            (S (hc _ _) (S (hc _ _) (S (hc _ _) hid0))))]
        cases (ax0.val == ax.val)
        · exact foldSum_zero_of_forall fun _ _ ↦ rfl
        · rw [Bool.cond_true]
          unfold tier1WalkKinNucSum256
          rw [show mkFin234 i.val = i from Fin.ext (Nat.mod_eq_of_lt i.isLt)]
          exact foldSum_eq_bSum 8 256 _
      rcases (⟨hsl 0, hsl 1, hsl 2⟩ : _ ∧ _ ∧ _) with ⟨hr0, hr1, hr2⟩
      simp only [Fin.val_zero, Nat.zero_mul, Nat.zero_add, Fin.val_one, Nat.one_mul,
        show (2 : Fin 3).val = 2 from rfl] at hr0 hr1 hr2
      rw [hr0, hr1, hr2]
      unfold wKinTier1Walk
      simp only [hi47, ↓reduceDIte, tier1WalkKinNucSum256_eq ⟨i.val, hi47⟩]
      rcases ax with ⟨_ | _ | _ | _, _⟩ <;> first | rfl | exact Nat.zero_add _ | omega
    · rw [foldSum_zero_of_forall fun b _ ↦ by
          rw [hidb b, Nat.add_zero]
          have hok : tier1IsNucOrIdle (tier1WalkKinNucBlk b).1 = true := by
            unfold tier1WalkKinNucBlk
            cases Nat.ble 768 b
            · rw [Bool.cond_false, tier1WalkKinNucS8_eq_pure]
              have h012 := allTree_zero check_tier1WalkKinNucS8_nuc (Nat.mod_lt b (by omega))
              simp only [Bool.and_eq_true] at h012
              rcases h012 with ⟨⟨h0, h1⟩, h2⟩
              generalize mkFin3 (b / 256) = ax0
              fin_cases ax0 <;> assumption
            · rfl
          cases hs : (tier1WalkKinNucBlk b).1 <;> rw [hs] at hok <;> try cases hok
          · rfl
          · rename_i p _w
            have hp47 : p.val < 47 := Nat.blt_eq.mp hok
            dsimp only [eqSec]
            rw [beq_eq_false_iff_ne.mpr fun he ↦ absurd (congrArg Fin.val he) (by omega)]; rfl,
        Nat.add_zero]
      let u0 : Fin 187 := ⟨i.val - 47, by omega⟩
      rw [Finset.sum_eq_single u0 (fun u1 _ hne ↦ Finset.sum_eq_zero fun h1 _ ↦
          Finset.sum_eq_zero fun h2 _ ↦ hzero_u1 u1 h1 h2 fun hm ↦ hne <| Fin.ext <| by
            have hv := congrArg Fin.val hm
            dsimp only [mkFin234, u0] at hv ⊢
            rw [Nat.mod_eq_of_lt (by omega)] at hv
            omega)
        (fun h ↦ absurd (Finset.mem_univ _) h)]
      rw [tier1Walk_int_kin_elec ax (Fin.ext (by
        unfold mkFin234
        dsimp only [u0]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega))]
      unfold wKinTier1Walk
      simp only [not_lt_of_ge hi47, ↓reduceDIte]
end QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc

namespace QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc
open DynamicCircuit PhotochemistrySolution.FineLegendre
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
/-- `.ee` `W11` fiber counts (`0x000` polarity) for the `p = 155` regime. -/
def cntEETier1Walk (s : Fin 4) (ω : BitAssignment 11) : ℕ :=
  cntEE2048Tier1Walk s (natOfZModBits 11 ω)
/-- `.nn` `W11` fiber counts (`0x000` polarity) for the `p = 155` regime. -/
def cntNNTier1Walk (s1 s2 : Fin 4) (ω : BitAssignment 11) : ℕ :=
    cntNN2048Tier1Walk s1 s2 (natOfZModBits 11 ω)
theorem fib_ee_tier1Walk_w11Nat_eq_cntEE2048 (n1 : Fin 47) (e1 e2 : Fin 187) {w : ℕ}
    (hw : w < 2048) : ((Finset.univ : Finset (Fin (2 ^ 41))).filter (fun c ↦
    decodeTier1WalkCoin c = .ee n1 e1 e2 ∧ w11NatOfCoin c = w)).card = if e1 <
    e2 then cntEE2048Tier1Walk (nucSpecies n1) w else 0
    := by unfold cntEE2048Tier1Walk; rw [fib_ee_tier1Walk_w11Nat n1 e1 e2 hw,
            tier1_speciesZ_eq_mSp]
theorem fib_nn_tier1Walk_w11Nat_eq_cntNN2048 (n1 n2 : Fin 47) (e1 : Fin 187) {w : ℕ}
    (hw : w < 2048) : ((Finset.univ : Finset (Fin (2 ^ 41))).filter (fun c ↦
    decodeTier1WalkCoin c = .nn n1 n2 e1 ∧ w11NatOfCoin c = w)).card = if n1 <
    n2 then cntNN2048Tier1Walk (nucSpecies n1)
    (nucSpecies n2) w else 0
    := by unfold cntNN2048Tier1Walk; rw [fib_nn_tier1Walk_w11Nat n1 n2 e1 hw,
            tier1_speciesZ_eq_mSp, tier1_speciesZ_eq_mSp]
end QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc

namespace QuantumComputation.Specs.PhotochemistrySolution.WStateStage4Ulp
set_option exponentiation.threshold 8192
open Real Operator QProg DynamicCircuit Matrix QuantumComputation.Specs PhotochemistrySolution
  PhotochemistrySolution.ClusterPotSlice PhotochemistrySolution.ZeroNEremSpec
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.TelescopeSlice PhotochemistrySolution.EvenOctB70
  PhotochemistrySolution.OuterW11Alt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinNormSlice (OpSys)
/-- `512`-word `36`-bit PopBernstein knot table for `p = 155` (`p = 155`). -/
abbrev word512DualLeg := PhotochemistrySolution.CtrlSafeOracleBase.Qrom.word512DualLeg

/-- `512`-word `36`-bit `p = 155` table with low `6` bits zeroed (`Bf80`). -/
def word512DualLegLo6 (i : ℕ) : ℕ := (word512DualLeg i / 64) * 64

theorem nat_div_def (a b : Nat) : Nat.div a b = a / b := rfl

def clbGam6 (w : ℕ) : ℕ :=
  let wp := w ^^^ 1365
  ((wp / 1024) % 2) + 2 * ((wp / 512) % 2) + 4 * ((wp / 256) % 2) +
  8 * ((wp / 128) % 2) + 16 * ((wp / 64) % 2) + 32 * ((wp / 32) % 2)

theorem clbGam6_lt (w : ℕ) : clbGam6 w < 64 := by unfold clbGam6; dsimp only; omega

def bitRev6 (g : ℕ) : ℕ :=
  (g % 2) * 32 + ((g / 2) % 2) * 16 + ((g / 4) % 2) * 8 +
  ((g / 8) % 2) * 4 + ((g / 16) % 2) * 2 + (g / 32) % 2

/-- Reconstruct `w < 2048` from `(u5, g6) ∈ Fin 32 × Fin 64`. -/
def wOfU5Gam (u5 g6 : ℕ) : ℕ := (u5 + 32 * bitRev6 g6) ^^^ 1365

/-- Extract `u5 = (w ^^^ 1365) % 32 < 32`. -/
def u5OfW (w : ℕ) : ℕ := (w ^^^ 1365) % 32

theorem u5OfW_lt (w : ℕ) : u5OfW w < 32 := Nat.mod_lt _ (by omega)

theorem wOfU5Gam_lt : ∀ (u5 : Fin 32) (g6 : Fin 64), wOfU5Gam u5.val g6.val < 2048 := by
  decide +kernel
theorem equivW11CLB_left : ∀ p : Fin 32 × Fin 64,
    ((⟨u5OfW (wOfU5Gam p.1.val p.2.val), u5OfW_lt _⟩ : Fin 32),
    (⟨clbGam6 (wOfU5Gam p.1.val p.2.val), clbGam6_lt _⟩ : Fin 64)) = p := by decide +kernel
theorem equivW11CLB_right : ∀ w : Fin 2048, (⟨wOfU5Gam (u5OfW w.val)
    (clbGam6 w.val), wOfU5Gam_lt ⟨u5OfW w.val, u5OfW_lt _⟩ ⟨clbGam6 w.val, clbGam6_lt _⟩⟩ :
    Fin 2048) = w := by decide +kernel
/-- Bijection `Fin 32 × Fin 64 ≃ Fin 2048` separating `(u5, γ_6)` in `CLB(6, 5)`. -/
def equivW11CLB : Fin 32 × Fin 64 ≃ Fin 2048 where
  toFun p := ⟨wOfU5Gam p.1.val p.2.val, wOfU5Gam_lt p.1 p.2⟩
  invFun w := (⟨u5OfW w.val, u5OfW_lt _⟩, ⟨clbGam6 w.val, clbGam6_lt _⟩)
  left_inv := equivW11CLB_left
  right_inv := equivW11CLB_right

def zKnotLo6 (ch : ChW11) (k i7 j : ℕ) : ℕ := chFnFast ch (word512DualLegLo6 (4 * i7 + j) / (2 ^ k))
def wOfU5GamF (u5 g6 : Nat) : Nat :=
  Nat.add
    (Nat.add (Nat.sub 1 (Nat.mod u5 2))
      (Nat.add (Nat.mul 2 (Nat.mod (Nat.div u5 2) 2))
        (Nat.add (Nat.mul 4 (Nat.sub 1 (Nat.mod (Nat.div u5 4) 2)))
          (Nat.add (Nat.mul 8 (Nat.mod (Nat.div u5 8) 2))
            (Nat.mul 16 (Nat.sub 1 (Nat.mod (Nat.div u5 16) 2)))))))
    (Nat.add (Nat.mul 32 (Nat.mod (Nat.div g6 32) 2))
      (Nat.add (Nat.mul 64 (Nat.sub 1 (Nat.mod (Nat.div g6 16) 2)))
        (Nat.add (Nat.mul 128 (Nat.mod (Nat.div g6 8) 2))
          (Nat.add (Nat.mul 256 (Nat.sub 1 (Nat.mod (Nat.div g6 4) 2)))
            (Nat.add (Nat.mul 512 (Nat.mod (Nat.div g6 2) 2))
              (Nat.mul 1024 (Nat.sub 1 (Nat.mod g6 2))))))))

/-- Fast `Nat`-primitive equivalent of `word512DualLegLo6`. -/
def word512DualLegLo6T (i : Nat) : Nat := Nat.mul (Nat.div (word512DualLeg i) 64) 64
inductive NList : Type
  | nil : NList
  | cons : Nat → Nat → NList → NList

inductive NLTree : Type
  | leaf : NList → NLTree
  | node : Nat → NLTree → NLTree → NLTree

inductive STList : Type
  | nil : STList
  | cons : Nat → SumTree → STList → STList

inductive J4Pack : Type
  | mk : NList → NList → NList → NList → NLTree → NLTree → NLTree → NLTree → J4Pack

inductive RList : Type
  | nil : RList
  | cons : Nat → Nat → Nat → Bool → RList → RList

theorem zKnotLo6_fastJ (ch : ChW11) (k i7 j : Nat) : chFnFast ch (word512DualLegLo6T (4 * i7 + j) /
    2 ^ k) = zKnotLo6 ch k i7 j := by rw [← nat_div_def, ← Nat.add_eq, ← Nat.mul_eq]; rfl
def mEEDualLegPre5 (b : Fin 6) : ℤ :=
  match b.val with
  | 0 => 0
  | 1 => 116
  | 2 => 91
  | 3 => 64
  | 4 => 48
  | _ => 24

/-- Hardware-pinned `m_nn` integer profile `[0, 175, 84, 38, 0, 0]` (`nn_unit = 187`). -/
def mNNDualLegPre5 (b : Fin 6) : ℤ :=
  match b.val with
  | 0 => 0
  | 1 => 175
  | 2 => 84
  | 3 => 38
  | _ => 0

/-- Scaled `187 * m_ee` `.ee` radial increments for `0`-ULP Bezout cancellation. -/
def dEEDualLegPre5 (b : Fin 6) : ℤ := 187 * mEEDualLegPre5 b

/-- Scaled `187 * m_nn` `.nn` radial increments (`nn_unit = 187`) for uniform `gain = 10`. -/
def dNNDualLegPre5 (b : Fin 6) : ℤ := 187 * mNNDualLegPre5 b

/-- Exact uniform-`EN10` (`gain = 10`) radial increments cancelling `.ee` and `.nn` to `0` ULP. -/
def dENDualLegPre5 (sp : Fin 4) (b : Fin 6) : ℤ :=
    (10 * (372 * dEEDualLegPre5 b + (187 - (speciesZ sp : ℤ)) * dNNDualLegPre5 b)) / 374
theorem dENDualLegPre5_bezout_exact : ∀ (sp : Fin 4) (b : Fin 6), 374 * dENDualLegPre5 sp b = 10 *
    (372 * dEEDualLegPre5 b + (187 - (speciesZ sp : ℤ)) * dNNDualLegPre5 b) := by decide +kernel
/-- Uniform `.en` DC offset `33,757` across `(H, C, N, O)` at `S = 14`. -/
def qEN0DualLegPre5 : ℤ := 33757

/-- Leg-1 `.ee` signed table `cEE1[b] = (5580 + d_ee[b]) * 2^14`. -/
def cEE1Sh14P5DualLeg (b : Fin 6) : ℤ := (5580 + dEEDualLegPre5 b) * 16384

/-- Leg-2 `.ee` signed table `cEE2[b] = (5580 + d_ee[b]) * 2^14` (`dc_ee = 0`). -/
def cEE2Sh14P5DualLeg (b : Fin 6) : ℤ := (5580 + dEEDualLegPre5 b) * 16384

/-- Shared `.nn` signed table `cNN[b] = (-865 + d_nn[b]) * 2^14`. -/
def cNNSh14P5DualLeg (b : Fin 6) : ℤ := (-865 + dNNDualLegPre5 b) * 16384

/-- Uniform-`EN10` `.en` signed table `cEN[sp][b] = (33757 + d_en[sp][b]) * 2^14`. -/
def cENSh14P5DualLeg (sp : Fin 4) (b : Fin 6) : ℤ :=
    (qEN0DualLegPre5 + dENDualLegPre5 sp b) * 16384

/-- Canonical `Fin 8` Leg-1 `.ee` table on `fin8Bin` for the `p = 155` regime. -/
def cEE1Fin8DualLeg (b : Fin 8) : ℤ := cEE1Sh14P5DualLeg (pre5OfFin8 b)

/-- Canonical `Fin 8` Leg-2 `.ee` table on `fin8Bin` for the `p = 155` regime. -/
def cEE2Fin8DualLeg (b : Fin 8) : ℤ := cEE2Sh14P5DualLeg (pre5OfFin8 b)

/-- Canonical `Fin 8` `.nn` table on `fin8Bin` for the `p = 155` regime. -/
def cNNFin8DualLeg (b : Fin 8) : ℤ := cNNSh14P5DualLeg (pre5OfFin8 b)

/-- Canonical `Fin 8` `.en` table on `fin8Bin` for the `p = 155` regime. -/
def cENFin8DualLeg (sp : Fin 4) (b : Fin 8) : ℤ := cENSh14P5DualLeg sp (pre5OfFin8 b)

/-- `ℕ`-indexed Leg-1 `.ee` table for the `p = 155` regime. -/
def cEE1NatDualLeg (b : ℕ) : ℤ := cEE1Sh14P5DualLeg (pre5OfNat b)

/-- `ℕ`-indexed Leg-2 `.ee` table for the `p = 155` regime. -/
def cEE2NatDualLeg (b : ℕ) : ℤ := cEE2Sh14P5DualLeg (pre5OfNat b)

/-- `ℕ`-indexed `.nn` table for the `p = 155` regime. -/
def cNNNatDualLeg (b : ℕ) : ℤ := cNNSh14P5DualLeg (pre5OfNat b)

/-- `ℕ`-indexed `.en` table (`sp < 4`) for the `p = 155` regime. -/
def cENNatDualLeg (sp b : ℕ) : ℤ :=
  match sp with
  | 0 => cENSh14P5DualLeg 0 (pre5OfNat b)
  | 1 => cENSh14P5DualLeg 1 (pre5OfNat b)
  | 2 => cENSh14P5DualLeg 2 (pre5OfNat b)
  | 3 => cENSh14P5DualLeg 3 (pre5OfNat b)
  | _ => 0

/-- Full `31`-bit modular Leg-1 shift `(2^29 - tbl1) mod 2^31` for the `p = 155` regime. -/
def leg1Shift31DualLegPre5 (s0 n0 : Bool) (sp : Fin 4) (b5 : Fin 6) : ℕ :=
  cond (Bool.not s0) (mod31OfInt ((536870912 : ℤ) - cENSh14P5DualLeg sp b5))
    (cond (Bool.not n0) (mod31OfInt ((536870912 : ℤ) - cEE1Sh14P5DualLeg b5))
      (mod31OfInt ((536870912 : ℤ) - cNNSh14P5DualLeg b5)))

/-- Full `31`-bit modular Leg-2 shift `(-tbl2) mod 2^31` for the `p = 155` regime. -/
def leg2Shift31DualLegPre5 (s0 n0 : Bool) (_sp : Fin 4) (b5 : Fin 6) : ℕ :=
  cond (Bool.not s0) 0
    (cond (Bool.not n0) (mod31OfInt (-cEE2Sh14P5DualLeg b5))
      (mod31OfInt (-cNNSh14P5DualLeg b5)))

/-- `17`-bit (`col_0..16`, bits `14..30`) Leg-1 target word for the `p = 155` regime. -/
def v1DualLegPre5 (s0 n0 : Bool) (sp : Fin 4) (b5 : Fin 6) : ℕ :=
  leg1Shift31DualLegPre5 s0 n0 sp b5 >>> 14

/-- `17`-bit (`col_0..16`, bits `14..30`) Leg-2 target word for the `p = 155` regime. -/
def v2DualLegPre5 (s0 n0 : Bool) (sp : Fin 4) (b5 : Fin 6) : ℕ :=
  leg2Shift31DualLegPre5 s0 n0 sp b5 >>> 14

/-- `Fin 8` Leg-1 `17`-bit target word on `fin8Bin` for the `p = 155` regime. -/
def v1Fin8DualLeg (s0 n0 : Bool) (sp : Fin 4) (b : Fin 8) : ℕ :=
  v1DualLegPre5 s0 n0 sp (pre5OfFin8 b)

/-- `Fin 8` Leg-2 `17`-bit target word on `fin8Bin` for the `p = 155` regime. -/
def v2Fin8DualLeg (s0 n0 : Bool) (sp : Fin 4) (b : Fin 8) : ℕ :=
    v2DualLegPre5 s0 n0 sp (pre5OfFin8 b)
/-- Exact signed `2 ^ 29`-scale numerator `u30DualLeg` across `.ee`, `.nn`, and uniform `.en`. -/
def u30DualLeg (isScr isNN : Bool) (sp1 _sp2 : Fin 4) (b1 b2 : Fin 8) (y36 : ℕ) : ℤ :=
  if isScr then
    if isNN then
      ((y36 >>> 5 : ℕ) : ℤ) - cNNFin8DualLeg b1 - cNNFin8DualLeg b2
    else
      ((y36 >>> 6 : ℕ) : ℤ) - cEE1Fin8DualLeg b1 - cEE2Fin8DualLeg b2
  else
    (fnEN10_30 y36 : ℤ) - cENFin8DualLeg sp1 b1

abbrev PopBernNonWrap30DualLeg (ySample : Bool → ℕ → (Fin 3 → Fin 2048) → ℕ) : Prop :=
  (∀ x n1 e1 e2 c,
    |u30DualLeg true false (nucSpecies n1) 0
      (fin8Bin (pairOpenDistSq x (nucP n1) (elecP e1)))
      (fin8Bin (pairOpenDistSq x (nucP n1) (elecP e2)))
      (ySample false (pairOpenDistSq x (elecP e1) (elecP e2)) c)| ≤ 2 ^ 29) ∧
  (∀ x {n1 n2 : Fin 47}, n1 < n2 → ∀ e1 c,
    |u30DualLeg true true (nucSpecies n1) (nucSpecies n2)
      (fin8Bin (pairOpenDistSq x (nucP n1) (elecP e1)))
      (fin8Bin (pairOpenDistSq x (nucP n2) (elecP e1)))
      (ySample true (pairOpenDistSq x (nucP n1) (nucP n2)) c)| ≤ 2 ^ 29) ∧
  (∀ x n1 e1 c,
    |u30DualLeg false false (nucSpecies n1) 0
      (fin8Bin (pairOpenDistSq x (nucP n1) (elecP e1))) 0
      (ySample false (pairOpenDistSq x (nucP n1) (elecP e1)) c)| ≤ 2 ^ 29)

/-- Unclamped endpoint far-field + near-field (`C < 189`, `d2 < 48`) `|u30DualLeg| ≤ 2^29` check. -/
def checkPopBernNonWrap30DualLeg (word512 : ℕ → ℕ) (yLoF yHiF yHiF48 yLoT yHiT : ℕ) : Bool :=
  checkPopBernCtrlRangesNoClamp word512 yLoF yHiF yHiF48 yLoT yHiT &&
  allRange 3 8 (fun b ↦
    chkCap29Fast (((yLoF >>> 6 : ℕ) : ℤ) - (cEE1NatDualLeg b + cEE2NatDualLeg 0)) &&
    chkCap29Fast (((yHiF >>> 6 : ℕ) : ℤ) - (cEE1NatDualLeg b + cEE2NatDualLeg 0)) &&
    chkCap29Fast (((yLoF >>> 6 : ℕ) : ℤ) - (cEE1NatDualLeg 0 + cEE2NatDualLeg b)) &&
    chkCap29Fast (((yHiF >>> 6 : ℕ) : ℤ) - (cEE1NatDualLeg 0 + cEE2NatDualLeg b)) &&
    chkCap29Fast (((yLoT >>> 5 : ℕ) : ℤ) - (cNNNatDualLeg b + cNNNatDualLeg 0)) &&
    chkCap29Fast (((yHiT >>> 5 : ℕ) : ℤ) - (cNNNatDualLeg b + cNNNatDualLeg 0)) &&
    chkCap29Fast (((yLoT >>> 5 : ℕ) : ℤ) - (cNNNatDualLeg 0 + cNNNatDualLeg b)) &&
    chkCap29Fast (((yHiT >>> 5 : ℕ) : ℤ) - (cNNNatDualLeg 0 + cNNNatDualLeg b))) &&
  (chkCap29Fast ((fnEN10_30 yLoF : ℤ) - cENNatDualLeg 0 0) &&
   chkCap29Fast ((fnEN10_30 yHiF48 : ℤ) - cENNatDualLeg 0 0) &&
   chkCap29Fast ((fnEN10_30 yLoF : ℤ) - cENNatDualLeg 1 0) &&
   chkCap29Fast ((fnEN10_30 yHiF48 : ℤ) - cENNatDualLeg 1 0) &&
   chkCap29Fast ((fnEN10_30 yLoF : ℤ) - cENNatDualLeg 2 0) &&
   chkCap29Fast ((fnEN10_30 yHiF48 : ℤ) - cENNatDualLeg 2 0) &&
   chkCap29Fast ((fnEN10_30 yLoF : ℤ) - cENNatDualLeg 3 0) &&
   chkCap29Fast ((fnEN10_30 yHiF48 : ℤ) - cENNatDualLeg 3 0)) &&
  allRange 6 48 (fun d ↦
    cond (Nat.beq (d % 8) 7) true
      (let p := evenOctPartsFast false d
       let fb := fin8BinFast d
       allRange 2 4 fun j ↦
         cond (Nat.beq (t11OfParts p) 0 && natLtB 0 j) true
           (let y := (word512 (4 * idx7OfParts p + j)) >>> p.2.2
            chkCap29Fast ((fnEN10_30 y : ℤ) - cENNatDualLeg 0 fb) &&
            chkCap29Fast ((fnEN10_30 y : ℤ) - cENNatDualLeg 1 fb) &&
            chkCap29Fast ((fnEN10_30 y : ℤ) - cENNatDualLeg 2 fb) &&
            chkCap29Fast ((fnEN10_30 y : ℤ) - cENNatDualLeg 3 fb)))) &&
  allRange 8 189 (fun c ↦
    cond (Nat.beq (c % 8) 7) true
      (let pf := evenOctPartsFast false c
       let pt := evenOctPartsFast true c
       allRange 2 4 fun j ↦
         (cond (Nat.beq (t11OfParts pf) 0 && natLtB 0 j) true
           (let yf := (word512 (4 * idx7OfParts pf + j)) >>> pf.2.2
            allRange 3 8 fun b1 ↦ allRange 3 8 fun b2 ↦
              cond (Nat.beq b1 0 || Nat.beq b2 0 || Bool.not (boxOkFast b1 b2 c)) true
                (chkCap29Fast (((yf >>> 6 : ℕ) : ℤ) - (cEE1NatDualLeg b1 + cEE2NatDualLeg b2))))) &&
         (cond (Nat.beq (t11OfParts pt) 0 && natLtB 0 j) true
           (let yt := (word512 (4 * idx7OfParts pt + j)) >>> pt.2.2
            allRange 3 8 fun b1 ↦ allRange 3 8 fun b2 ↦
              cond (Nat.beq b1 0 || Nat.beq b2 0 || Bool.not (boxOkFast b1 b2 c)) true
                (chkCap29Fast (((yt >>> 5 : ℕ) : ℤ) - (cNNNatDualLeg b1 + cNNNatDualLeg b2)))))))

theorem popBernNonWrap30DualLeg_of_check {word512 : ℕ → ℕ} {yLoF yHiF yHiF48 yLoT yHiT : ℕ}
    (hchk : checkPopBernNonWrap30DualLeg word512 yLoF yHiF yHiF48 yLoT yHiT = true) :
    PopBernNonWrap30DualLeg (y36PopBernNoClampS14 word512) := by
  have hp29 : (2 ^ 29 : ℤ) = 536870912 := by norm_num
  unfold checkPopBernNonWrap30DualLeg at hchk
  simp only [Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨⟨⟨hcr, hfar⟩, henF⟩, henN⟩, hpairN⟩
  obtain ⟨hbF, hbF48, hbT⟩ := ctrl_bounds_of_ranges_noClamp hcr
  have hpC {C : ℕ} (j : Fin 4) (hC : C < 189) (hm7 : ¬ C % 8 = 7) := by
    have h1 := allRange_eq_true (by norm_num) hpairN hC
    rw [cond_false_of_not (mt Nat.beq_eq.mp hm7), evenOctPartsFast_eq, evenOctPartsFast_eq] at h1
    exact Bool.and_eq_true_iff.mp (allRange_eq_true (by norm_num) h1 j.isLt)
  have ht11 {p : ℕ × ℕ × ℕ} {c : Fin 3 → Fin 2048} {x : Bool}
      (h : cond (Nat.beq (t11OfParts p) 0 && natLtB 0 (popBernJ (t11OfParts p) c)) true x = true) :
      x = true := by
    rwa [cond_false_of_not (by
      simp only [Bool.and_eq_true, Nat.beq_eq, natLtB_eq_true]
      rintro ⟨h0, hj⟩
      rw [h0, popBernJ_zero_of_t11_zero] at hj
      omega)] at h
  have hscr (x : Fin (2 ^ systemQubits_frozen)) (p0 p1 p2 : Particle_frozen)
      (c : Fin 3 → Fin 2048) (isNN : Bool) (sh : ℕ) (c1 c2 : ℕ → ℤ) (yLo yHi : ℕ)
      (hyB : Is3DBoxDistSq (pairOpenDistSq x p1 p2) →
        yLo ≤ y36PopBernNoClampS14 word512 isNN (pairOpenDistSq x p1 p2) c ∧
        y36PopBernNoClampS14 word512 isNN (pairOpenDistSq x p1 p2) c ≤ yHi)
      (hsel : ∀ j : Fin 4, pairOpenDistSq x p1 p2 < 189 → ¬ (pairOpenDistSq x p1 p2 % 8 = 7) →
        cond (Nat.beq (t11OfParts (evenOctIdxT10K isNN (pairOpenDistSq x p1 p2))) 0 &&
          natLtB 0 j.val) true (allRange 3 8 fun b1 ↦ allRange 3 8 fun b2 ↦
            cond (Nat.beq b1 0 || Nat.beq b2 0 ||
              Bool.not (boxOkFast b1 b2 (pairOpenDistSq x p1 p2))) true
              (chkCap29Fast ((((word512 (4 * idx7OfParts
                (evenOctIdxT10K isNN (pairOpenDistSq x p1 p2)) + j.val) >>>
                  (evenOctIdxT10K isNN (pairOpenDistSq x p1 p2)).2.2) >>> sh : ℕ) : ℤ) -
                (c1 b1 + c2 b2)))) = true)
      (hfB : ∀ b : Fin 8, chkCap29Fast (((yLo >>> sh : ℕ) : ℤ) - (c1 b.val + c2 0)) = true ∧
        chkCap29Fast (((yHi >>> sh : ℕ) : ℤ) - (c1 b.val + c2 0)) = true)
      (hfA : ∀ b : Fin 8, chkCap29Fast (((yLo >>> sh : ℕ) : ℤ) - (c1 0 + c2 b.val)) = true ∧
        chkCap29Fast (((yHi >>> sh : ℕ) : ℤ) - (c1 0 + c2 b.val)) = true) :
      |((y36PopBernNoClampS14 word512 isNN (pairOpenDistSq x p1 p2) c >>> sh : ℕ) : ℤ) -
        c1 (fin8Bin (pairOpenDistSq x p1 p0)).val -
        c2 (fin8Bin (pairOpenDistSq x p2 p0)).val| ≤ 536870912 := by
    set A := pairOpenDistSq x p1 p0
    set B := pairOpenDistSq x p2 p0
    set C := pairOpenDistSq x p1 p2
    have h3d : Is3DBoxDistSq C := is3DBoxDistSq_pairOpenDistSq x p1 p2
    by_cases hA : A < 48
    · by_cases hB : B < 48
      · rcases bin_range_ultra ⟨A, hA⟩ with h7 | hAr
        · exact absurd h7 (pairOpenDistSq_mod8_ne7_u x _ _)
        rcases bin_range_ultra ⟨B, hB⟩ with h7 | hBr
        · exact absurd h7 (pairOpenDistSq_mod8_ne7_u x _ _)
        let p := evenOctIdxT10K isNN C
        let j : Fin 4 := ⟨popBernJ (t11OfParts p) c, popBernJ_lt_four (t11OfParts p) c⟩
        have h3 := allRange_eq_true (by norm_num) (allRange_eq_true (by norm_num)
          (ht11 (hsel j (pairOpenDistSq_lt_189_u hA hB) (pairOpenDistSq_mod8_ne7_u _ _ _)))
          (fin8Bin A).isLt) (fin8Bin B).isLt
        rw [cond_false_of_not (by
          dsimp only at hAr hBr
          rw [boxOkFast_of_boxOkUltra (boxOkUltra_of_lagrange hAr.2 hBr.2
            (pairOpenDistSq_lagrange_u x p0 p1 p2))]
          simp only [Bool.not_true, Bool.or_false, Bool.or_eq_true, Nat.beq_eq]
          omega)] at h3
        have hc : |((y36PopBernNoClampS14 word512 isNN C c >>> sh : ℕ) : ℤ) -
            (c1 (fin8Bin A).val + c2 (fin8Bin B).val)| ≤ 536870912 := chkCap29Fast_abs h3
        rw [abs_le] at hc ⊢
        omega
      · rw [fin8Bin_of_ge48_ultra (Nat.le_of_not_lt hB), sub_sub]
        exact cap29_of_mono (Int.ofNat_le.mpr (shr_mono_nat (hyB h3d).1 sh))
          (Int.ofNat_le.mpr (shr_mono_nat (hyB h3d).2 sh)) (hfB (fin8Bin A)).1 (hfB (fin8Bin A)).2
    · rw [fin8Bin_of_ge48_ultra (Nat.le_of_not_lt hA), sub_sub]
      exact cap29_of_mono (Int.ofNat_le.mpr (shr_mono_nat (hyB h3d).1 sh))
        (Int.ofNat_le.mpr (shr_mono_nat (hyB h3d).2 sh)) (hfA (fin8Bin B)).1 (hfA (fin8Bin B)).2
  have hfarB (b : Fin 8) := by
    have hf := allRange_eq_true (by norm_num) hfar b.isLt
    simpa only [Bool.and_eq_true] using hf
  refine ⟨fun x n1 e1 e2 c ↦ ?_, fun x n1 n2 _ e1 c ↦ ?_, fun x n1 e1 c ↦ ?_⟩
  · rw [hp29]
    unfold u30DualLeg
    simp only [Bool.false_eq_true, ↓reduceIte, pairOpenDistSq_comm_fermatCoin_u x (nucP n1),
      show ∀ b : Fin 8, cEE1Fin8DualLeg b = cEE1NatDualLeg b.val from fun _ ↦ rfl,
      show ∀ b : Fin 8, cEE2Fin8DualLeg b = cEE2NatDualLeg b.val from fun _ ↦ rfl]
    exact hscr x (nucP n1) (elecP e1) (elecP e2) c false 6 cEE1NatDualLeg cEE2NatDualLeg yLoF yHiF
      (fun h3d ↦ hbF h3d c) (fun j hC hm7 ↦ (hpC j hC hm7).1)
      (fun b ↦ ⟨(hfarB b).1.1.1.1.1.1.1, (hfarB b).1.1.1.1.1.1.2⟩)
      (fun b ↦ ⟨(hfarB b).1.1.1.1.1.2, (hfarB b).1.1.1.1.2⟩)
  · rw [hp29]
    unfold u30DualLeg
    simp only [↓reduceIte, show ∀ b : Fin 8, cNNFin8DualLeg b = cNNNatDualLeg b.val from fun _ ↦
        rfl]
    exact hscr x (elecP e1) (nucP n1) (nucP n2) c true 5 cNNNatDualLeg cNNNatDualLeg yLoT yHiT
      (fun h3d ↦ hbT h3d c) (fun j hC hm7 ↦ (hpC j hC hm7).2)
      (fun b ↦ ⟨(hfarB b).1.1.1.2, (hfarB b).1.1.2⟩) (fun b ↦ ⟨(hfarB b).1.2, (hfarB b).2⟩)
  · rw [hp29]
    set d2 := pairOpenDistSq x (nucP n1) (elecP e1)
    unfold u30DualLeg
    simp only [Bool.false_eq_true, ↓reduceIte,
      show ∀ (sp : Fin 4) (b : Fin 8), cENFin8DualLeg sp b = cENNatDualLeg sp.val b.val from
        fun sp _ ↦ by fin_cases sp <;> rfl]
    by_cases hd : d2 < 48
    · let p := evenOctIdxT10K false d2
      let j : Fin 4 := ⟨popBernJ (t11OfParts p) c, popBernJ_lt_four (t11OfParts p) c⟩
      have h1 := allRange_eq_true (by norm_num) henN hd
      rw [cond_false_of_not (mt Nat.beq_eq.mp (pairOpenDistSq_mod8_ne7_u x _ _)),
        evenOctPartsFast_eq, fin8BinFast_eq ⟨d2, hd⟩] at h1
      have h2 := ht11 (allRange_eq_true (by norm_num) h1 j.isLt)
      simp only [Bool.and_eq_true] at h2
      exact chkCap29Fast_abs (match nucSpecies n1 with
        | ⟨0, _⟩ => h2.1.1.1 | ⟨1, _⟩ => h2.1.1.2
        | ⟨2, _⟩ => h2.1.2 | ⟨3, _⟩ => h2.2 | ⟨_ + 4, h⟩ => absurd h (by omega))
    · rw [fin8Bin_of_ge48_ultra (Nat.le_of_not_lt hd)]
      have hy := hbF48 (is3DBoxDistSq_pairOpenDistSq x (nucP n1) (elecP e1)) (by omega) c
      have hlo := Int.ofNat_le.mpr (fnEN30_mono hy.1 (1 : Fin 4))
      have hhi := Int.ofNat_le.mpr (fnEN30_mono hy.2 (1 : Fin 4))
      exact match nucSpecies n1 with
        | ⟨0, _⟩ => cap29_of_mono hlo hhi henF.1.1.1.1.1.1.1 henF.1.1.1.1.1.1.2
        | ⟨1, _⟩ => cap29_of_mono hlo hhi henF.1.1.1.1.1.2 henF.1.1.1.1.2
        | ⟨2, _⟩ => cap29_of_mono hlo hhi henF.1.1.1.2 henF.1.1.2
        | ⟨3, _⟩ => cap29_of_mono hlo hhi henF.1.2 henF.2
        | ⟨_ + 4, h⟩ => absurd h (by omega)

/-- Kernel-verified unclamped `|u30DualLeg| ≤ 2^29` non-wrap certificate on `word512DualLegLo6`. -/
theorem popBernNonWrap30_dualLeg_lo6 : PopBernNonWrap30DualLeg (y36PopBernNoClamp word512DualLegLo6)
    :=
  popBernNonWrap30DualLeg_of_check
    (yLoF := 103794294) (yHiF := 46022909632) (yHiF48 := 6642834816)
    (yLoT := 103794294) (yHiT := 16271555744) (by decide +kernel)

/-- Exact `p = 155` `.ee` short-range screening profile (`0`-ULP Bezout, `p = 155`). -/
def gEETier1Walk (b : ℕ) : ℝ :=
  ((273022058496 : ℝ) / 5714023029) * ((cEE1NatDualLeg b : ℝ) - (cEE1NatDualLeg 0 : ℝ))

/-- Optimal `.ee` DC midpoint for the `p = 155` regime (`dc = -21732 / 1000`). -/
def midEETier1Walk : ℝ :=
  ((273022058496 : ℝ) / 5714023029) * ((cEE1NatDualLeg 0 : ℝ) + (cEE2NatDualLeg 0 : ℝ)) -
      (-21732 : ℝ) / 1000

/-- Exact `p = 155` `.nn` short-range screening profile (`0`-ULP Bezout, `p = 155`). -/
def gNNTier1Walk (_s b : ℕ) : ℝ :=
  ((136511029248 : ℝ) / 5714023029) * ((cNNNatDualLeg b : ℝ) - (cNNNatDualLeg 0 : ℝ))

/-- Optimal `.nn` DC midpoint for the `p = 155` regime (`dc = -7496 / 1000`). -/
def midNNTier1Walk (_s1 _s2 : ℕ) : ℝ :=
  ((136511029248 : ℝ) / 5714023029) * (2 * (cNNNatDualLeg 0 : ℝ)) - (-7496 : ℝ) / 1000

/-- Optimal uniform-`EN10` `.en` DC midpoint for the `p = 155` regime (`dc = -2061 / 1000`). -/
def midENTier1Walk (s : Fin 4) : ℝ :=
    ((denomENFermatCoin 1 * (100000 / 100155)) / (2 ^ 29 : ℝ)) * (cENFin8DualLeg s 0 : ℝ) -
    (-2061 : ℝ) / 1000
theorem short_table_eq_ee_tier1Walk (b1 b2 : Fin 8) : ((denomEEFermatCoin * (100000 / 100155)) /
    (2 ^ 29 : ℝ)) * ((cEE1Fin8DualLeg b1 : ℝ) + (cEE2Fin8DualLeg b2 : ℝ)) = midEETier1Walk +
    gEETier1Walk b1.val + gEETier1Walk b2.val + (-21732 : ℝ) / 1000 := by
  have hd : (cEE2Fin8DualLeg b2 : ℝ) - (cEE2NatDualLeg 0 : ℝ) = (cEE1NatDualLeg b2.val : ℝ) -
      (cEE1NatDualLeg 0 : ℝ) := by
    unfold cEE2Fin8DualLeg cEE2NatDualLeg cEE2Sh14P5DualLeg cEE1NatDualLeg cEE1Sh14P5DualLeg
        pre5OfFin8
    push_cast; ring
  have h1 : (cEE1Fin8DualLeg b1 : ℝ) = (cEE1NatDualLeg b1.val : ℝ) :=
      rfl; unfold denomEEFermatCoin midEETier1Walk gEETier1Walk
  rw [h1]; norm_num at hd ⊢; linarith

theorem short_table_eq_nn_tier1Walk (s1 s2 : ℕ)
    (b1 b2 : Fin 8) : ((denomNNFermatCoinVal * (100000 / 100155)) / (2 ^ 29 : ℝ)) *
    ((cNNFin8DualLeg b1 : ℝ) + (cNNFin8DualLeg b2 : ℝ)) = midNNTier1Walk s1 s2 +
    gNNTier1Walk s1 b1.val + gNNTier1Walk s2 b2.val + (-7496 : ℝ) / 1000 := by
  have h1 : (cNNFin8DualLeg b1 : ℝ) = (cNNNatDualLeg b1.val : ℝ) := rfl;
  have h2 : (cNNFin8DualLeg b2 : ℝ) = (cNNNatDualLeg b2.val : ℝ) :=
      rfl; unfold denomNNFermatCoinVal midNNTier1Walk gNNTier1Walk
  rw [h1, h2]; norm_num; linarith

theorem short_table_eq_en_tier1Walk (s : Fin 4)
    (b : Fin 8) : ((denomENFermatCoin 1 * (100000 / 100155)) / (2 ^ 29 : ℝ)) *
    (cENFin8DualLeg s b : ℝ) = midENTier1Walk s + ((186 : ℝ) * gEETier1Walk b.val +
    (187 - (speciesZ s : ℝ)) * gNNTier1Walk s.val b.val) / 187 + (-2061 : ℝ) / 1000 := by
  have hbez : ((374 * dENDualLegPre5 s (pre5OfFin8 b) : ℤ) : ℝ) =
      ((10 * (372 * dEEDualLegPre5 (pre5OfFin8 b) + (187 - (speciesZ s : ℤ)) *
      dNNDualLegPre5 (pre5OfFin8 b)) : ℤ) : ℝ) :=
      congrArg Int.cast (dENDualLegPre5_bezout_exact s (pre5OfFin8 b))
  have hcEN : (cENFin8DualLeg s b : ℝ) - (cENFin8DualLeg s 0 : ℝ) =
      (dENDualLegPre5 s (pre5OfFin8 b) : ℝ) * 16384 := by
    unfold cENFin8DualLeg cENSh14P5DualLeg
    have h0 : dENDualLegPre5 s (pre5OfFin8 0) = 0 := by fin_cases s <;> decide
    rw [h0]; push_cast; ring
  have hcEE : (cEE1NatDualLeg b.val : ℝ) - (cEE1NatDualLeg 0 : ℝ) =
      (dEEDualLegPre5 (pre5OfFin8 b) : ℝ) * 16384 := by
    unfold cEE1NatDualLeg cEE1Sh14P5DualLeg pre5OfFin8;
    have h0 : dEEDualLegPre5 (pre5OfNat 0) = 0 := rfl
    rw [h0]; push_cast; ring
  have hcNN : (cNNNatDualLeg b.val : ℝ) - (cNNNatDualLeg 0 : ℝ) =
      (dNNDualLegPre5 (pre5OfFin8 b) : ℝ) * 16384 := by
    unfold cNNNatDualLeg cNNSh14P5DualLeg pre5OfFin8;
    have h0 : dNNDualLegPre5 (pre5OfNat 0) = 0 := rfl
    rw [h0]; push_cast; ring
  push_cast at hbez; unfold midENTier1Walk gEETier1Walk gNNTier1Walk denomENFermatCoin;
  rw [hcEE, hcNN]; norm_num at hbez hcEN ⊢; linarith
/-- `.ee` `W11`-stratified weight (`82` for `w < 1452`, `81` otherwise; sum `167,340`). -/
def wgtEETier1Walk (w : ℕ) : ℕ := if w < 1452 then 82 else 81

/-- `.nn` `W11`-stratified weight (`82` for `w < 1750`, `80` otherwise; sum `167,340`). -/
def wgtNNTier1Walk (w : ℕ) : ℕ := if w < 1750 then 82 else 80

theorem sum_wgtEETier1Walk : (∑ w : Fin 2048, wgtEETier1Walk w.val) = 167340 := by decide +kernel

theorem sum_wgtNNTier1Walk : (∑ w : Fin 2048, wgtNNTier1Walk w.val) = 167340 := by decide +kernel

inductive ChDualLeg : Type
  | ee : ChDualLeg
  | nn : ChDualLeg
  | en : ChDualLeg

abbrev alphaWState : ℝ := alphaTier1WalkFull

theorem alphaWState_le : alphaWState ≤ alphaTier1WalkFull := le_rfl
end QuantumComputation.Specs.PhotochemistrySolution.WStateStage4Ulp
end

end
