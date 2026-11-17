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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.BiGqspZeroCacheA

set_option linter.style.longLine false
set_option Elab.async false

@[expose] public section
set_option compiler.extract_closed false

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section Gqsp0e_RootUnpackLowMem

section
namespace GqspWronskian62592
section ZeroCacheTournamentAndRootUnpack
set_option maxRecDepth 600000
set_option exponentiation.threshold 2048
open Real TFreeLaurentGQSP CatalyzedLaurentGQSPBridge
open scoped BigOperators
open TFreeLaurentGQSPPresets (defaultGate)
open TFreeLaurentGQSPPresets.FastRecurrenceVerifier
  TFreeLaurentGQSPPresets.FastIntervalRecurrenceVerifier
open BidirectionalCatalyzedGQSPBridge BidirectionalIntervalRecurrenceVerifier
  TwoAngleBiGqspVerifierBridge
open GeneralBetaAndAlphaTopEndpoint (GeneralBetaSegmentCert)
/-- Zero-cache binary word splitter into `≤ 64`-lane chunks (`0` `DefinitionVal`s inside
  recursion). -/
noncomputable def gqsp_zwSplitWords64Aux (k : ℕ) : ℕ → ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) :=
  @Nat.rec (fun _ ↦ ℕ → ℕ → List (ℕ × ℕ) → List (ℕ × ℕ))
    (fun n w acc ↦
      @Nat.rec (fun _ ↦ List (ℕ × ℕ)) [] (fun w0 _ ↦ (n, w0) :: acc) (Nat.add 1 w))
    (fun _ ih n w acc ↦
      @Bool.rec (fun _ ↦ List (ℕ × ℕ))
        (let h := Nat.div n 2
         let sh := Nat.mul 768 h
         @Nat.rec (fun _ ↦ List (ℕ × ℕ)) [] (fun w_hi _ ↦
           @Nat.rec (fun _ ↦ List (ℕ × ℕ)) [] (fun w_lo _ ↦
             ih h w_lo (ih (Nat.sub n h) w_hi acc))
             (Nat.add 1 (Nat.sub w (Nat.shiftLeft w_hi sh))))
           (Nat.add 1 (Nat.shiftRight w sh)))
        (@Nat.rec (fun _ ↦ List (ℕ × ℕ)) [] (fun w0 _ ↦ (n, w0) :: acc) (Nat.add 1 w))
        (Nat.ble n 64))
    k
theorem gqsp_zwSplitWords64Aux_eq (k : ℕ) : ∀ (s n w : ℕ) (acc : List (ℕ × ℕ)),
    gqsp_zwSplitWords64Aux k n w acc = gqsp_splitWords64Aux k s n w acc := by
  unfold gqsp_zwSplitWords64Aux gqsp_splitWords64Aux
  induction k with
  | zero =>
      intro s n w acc
      rw [← Nat.zero_eq]
      dsimp only
      rw [gqsp_zwForce_eq, gqsp_splitLeaf64_eq]
  | succ k ih =>
      intro s n w acc
      dsimp only
      unfold gqsp_splitWords64Split
      cases hb : Nat.ble n 64
      · unfold gqsp_splitWords64Split at ih
        unfold gqsp_splitStepFast gqsp_splitStepHi gqsp_splitStepLo at ih ⊢
        simp only [Bool.false_eq_true, ↓reduceIte, gqsp_zwForce_eq, gqsp_stfPairs_eq,
          sched_idSalt_eq] at ih ⊢
        rw [ih (Nat.add 1 (Nat.mul 2 s)) (Nat.sub n (Nat.div n 2)) _ acc,
          ih (Nat.mul 2 s) (Nat.div n 2) _ _]
      · simp only [↓reduceIte, gqsp_zwForce_eq, gqsp_splitLeaf64_eq]
private theorem shr_add_eq (w a b : ℕ) : Nat.shiftRight w (a + b) =
    Nat.shiftRight (Nat.shiftRight w a) b := by
  simp only [Nat.shiftRight_eq, Nat.shiftRight_eq_div_pow, Nat.pow_add, Nat.div_div_eq_div_mul]
/-- Zero-cache indexed `768`-bit lane peeler (`0` `DefinitionVal`s, `0` `@Nat.rec (Nat.add 1
  ...)`). -/
noncomputable def gqsp_zwPeelIdxStep (m768 n0 w k0 : ℕ) : List ℕ → List ℕ :=
  @Nat.rec (fun _ ↦ List ℕ → List ℕ)
    (fun racc ↦ racc)
    (fun rem ih racc ↦
      let j := Nat.sub n0 (Nat.add 1 rem)
      let v := Nat.shiftRight (Nat.land (Nat.shiftRight w (Nat.mul 768 j)) m768) 256
      ih (v :: racc))
    k0
private theorem zwPeelIdxStep_eq (n0 w : ℕ) : ∀ (k : ℕ) (racc : List ℕ), k ≤ n0 →
    gqsp_zwPeelIdxStep gqsp_mask768 n0 w k racc =
      gqsp_zwPeel1Shr256Aux k (Nat.shiftRight w (768 * (n0 - k))) racc := by
  intro k
  unfold gqsp_zwPeelIdxStep
  induction k with
  | zero => exact fun _ _ ↦ rfl
  | succ rem ih =>
      intro racc hk
      dsimp only
      rw [show Nat.sub n0 (Nat.add 1 rem) = n0 - (rem + 1) from
          congrArg (n0 - ·) (Nat.add_comm 1 rem),
        Nat.mul_eq, ih _ (Nat.le_of_succ_le hk),
        show 768 * (n0 - rem) = 768 * (n0 - (rem + 1)) + 768 by omega, shr_add_eq,
        ← gqsp_zwPeel1Shr256Aux_succ]
private theorem zwPeelIdxStep_self_eq (n w : ℕ) (racc : List ℕ) :
    gqsp_zwPeelIdxStep gqsp_mask768 n w n racc = gqsp_zwPeel1Shr256Aux n w racc := by
  simpa only [Nat.sub_self, Nat.mul_zero, Nat.shiftRight_eq, Nat.shiftRight_zero] using
    zwPeelIdxStep_eq n w n racc le_rfl
/-- Zero-cache chunk list peeler using indexed shift extraction on `≤ 64`-lane chunks. -/
noncomputable def gqsp_zwPeelChunksIdx (m768 : ℕ) (chunks0 : List (ℕ × ℕ)) (racc0 : List ℕ) :
    List ℕ := @List.rec (ℕ × ℕ) (fun _ ↦ List ℕ → List ℕ) (fun racc ↦ racc) (fun p _ ih racc ↦
    @Prod.rec ℕ ℕ (fun _ ↦ List ℕ) (fun n w ↦ ih (gqsp_zwPeelIdxStep m768 n w n racc)) p)
    chunks0 racc0
private theorem zwPeelChunksIdx_eq :
    ∀ (chunks : List (ℕ × ℕ)) (racc : List ℕ),
      gqsp_zwPeelChunksIdx gqsp_mask768 chunks racc = gqsp_zwPeelWords64RevTR chunks racc
  | [], _ => rfl
  | (n, w) :: chunks, racc => by
      dsimp only [gqsp_zwPeelChunksIdx, gqsp_zwPeelWords64RevTR]
      rw [zwPeelIdxStep_self_eq]
      exact zwPeelChunksIdx_eq chunks _
/-- Zero-cache 2-term real dot-product + unpacker (`0` `sched_stfList` / split cache entries). -/
noncomputable def gqsp_zwFinishRootVec2Real
    (d n_lanes rep_bcomb : ℕ) (c1 x1 c3 x3 : PolyPN) : List ℕ :=
  @PolyPN.rec (fun _ ↦ List ℕ) (fun c1p c1n ↦
    @PolyPN.rec (fun _ ↦ List ℕ) (fun x1p x1n ↦
      @PolyPN.rec (fun _ ↦ List ℕ) (fun c3p c3n ↦
        @PolyPN.rec (fun _ ↦ List ℕ) (fun x3p x3n ↦
          let up0 := Nat.add (Nat.add (Nat.mul c1p x1p) (Nat.mul c1n x1n))
                             (Nat.add (Nat.mul c3p x3p) (Nat.mul c3n x3n))
          let un0 := Nat.add (Nat.add (Nat.mul c1p x1n) (Nat.mul c1n x1p))
                             (Nat.add (Nat.mul c3p x3n) (Nat.mul c3n x3p))
          @Nat.rec (fun _ ↦ List ℕ) [] (fun m768 _ ↦
            @Nat.rec (fun _ ↦ List ℕ) [] (fun up _ ↦
              @Nat.rec (fun _ ↦ List ℕ) [] (fun un _ ↦
                @Nat.rec (fun _ ↦ List ℕ) [] (fun w _ ↦
                  gqsp_zwRevNatTR
                    (gqsp_zwPeelChunksIdx m768 (gqsp_zwSplitWords64Aux (Nat.sub d 6) n_lanes w [])
                      []) [])
                  (Nat.add 1 (Nat.sub (Nat.add up rep_bcomb) un)))
                (Nat.add 1 un0))
              (Nat.add 1 up0))
            (Nat.add 1 gqsp_mask768))
          x3) c3) x1) c1
theorem gqsp_zwFinishRootVec2Real_eq (s d n_lanes rep_bcomb : ℕ) (c1 x1 c3 x3 : PolyPN) :
    gqsp_zwFinishRootVec2Real d n_lanes rep_bcomb c1 x1 c3 x3 =
    gqsp_finishRootVec2RealFast gqsp_sunpackShr256Chunked s
    d n_lanes rep_bcomb c1 x1 c3 x3 := by
  rcases c1, x1, c3, x3 with ⟨⟨c1p, c1n⟩, ⟨x1p, x1n⟩, ⟨c3p, c3n⟩, ⟨x3p, x3n⟩⟩
  unfold gqsp_zwFinishRootVec2Real gqsp_finishRootVec2RealFast mulAdd2Pos mulAdd2Neg
  dsimp only
  simp only [gqsp_zwForce_eq, sched_stfList_eq, zwPeelChunksIdx_eq]
  rw [← gqsp_zwSunpackShr256Chunked_eq]
  unfold gqsp_zwSunpackShr256Chunked
  rw [gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwSplitWords64Aux_eq (Nat.sub d 6) _ n_lanes _ []]
/-! ## 2. Zero-Cache Binary-Tree SWAR `768`-Bit Lane Reversal (`gqsp_zwFastRev4Swar`) -/
private theorem mul_pow768_eq_shl (x : ℕ) :
    Nat.mul 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 x =
      Nat.shiftLeft x 768 := by
  have hc : (0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℕ) = 2 ^ 768 := rfl
  rw [Nat.mul_eq, hc, Nat.mul_comm]
  exact (Nat.shiftLeft_eq x 768).symm
noncomputable def gqsp_zwRevLeaf1 (r0 : ℕ) : ℕ → ℕ → ℕ :=
  @Nat.rec (fun _ ↦ ℕ → ℕ → ℕ)
    (fun _ acc ↦ acc)
    (fun _ ih w acc ↦
      let m768 := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
      let p768 := 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
      @Nat.rec (fun _ ↦ ℕ) 0 (fun w' _ ↦
        @Nat.rec (fun _ ↦ ℕ) 0 (fun acc' _ ↦
          ih w' acc')
          (Nat.add 1 (Nat.add (Nat.land w m768) (Nat.mul p768 acc))))
        (Nat.add 1 (Nat.shiftRight w 768)))
    r0
private theorem zwRevLeaf1_zero (w acc : ℕ) : gqsp_zwRevLeaf1 0 w acc = acc := rfl
private theorem zwRevLeaf1_succ (r w acc : ℕ) : gqsp_zwRevLeaf1 (r + 1) w acc =
    gqsp_zwRevLeaf1 r (Nat.shiftRight w 768)
    (Nat.add (Nat.land w gqsp_mask768) (Nat.shiftLeft acc 768)) := by
  dsimp only [gqsp_zwRevLeaf1]
  simp only [gqsp_zwForce_eq, gqsp_zwMask768_eq, mul_pow768_eq_shl]
private theorem nat_shl_eq_mul_pow (a b : ℕ) : Nat.shiftLeft a b = a * 2 ^ b :=
  Nat.shiftLeft_eq a b
private theorem nat_shr_eq_div_pow (a b : ℕ) : Nat.shiftRight a b = a / 2 ^ b :=
  Nat.shiftRight_eq_div_pow a b
private theorem zwRevLeaf1_eq (r : ℕ) : ∀ (s w acc : ℕ),
    gqsp_zwRevLeaf1 r w acc = gqsp_revPow2LeafAux r s w acc := by
  unfold gqsp_zwRevLeaf1 gqsp_revPow2LeafAux
  induction r with
  | zero => exact fun _ _ _ ↦ rfl
  | succ r ih =>
      intro s w acc
      dsimp only at ih ⊢
      unfold gqsp_srev1Step at ih ⊢
      simp only [gqsp_zwForce_eq, sched_stfNat_eq, sched_idSalt_eq, gqsp_zwMask768_eq,
        mul_pow768_eq_shl] at ih ⊢
      exact ih (Nat.add 6 s) _ _
private theorem land_mask768_eq_mod (u : ℕ) : Nat.land u gqsp_mask768 = u % 2 ^ 768 := by
  change u &&& gqsp_mask768 = u % 2 ^ 768
  rw [show gqsp_mask768 = 2 ^ 768 - 1 from rfl]
  exact Nat.and_two_pow_sub_one_eq_mod u 768
private theorem zwRevLeaf1_acc :
    ∀ (m w acc : ℕ), gqsp_zwRevLeaf1 m w acc = gqsp_zwRevLeaf1 m w 0 + Nat.shiftLeft acc (768 * m)
  | 0, w, acc => by
      rw [zwRevLeaf1_zero, zwRevLeaf1_zero, Nat.mul_zero, nat_shl_eq_mul_pow, Nat.pow_zero,
        Nat.mul_one, Nat.zero_add]
  | m + 1, w, acc => by
      rw [zwRevLeaf1_succ, zwRevLeaf1_succ, show Nat.shiftLeft 0 768 = 0 from rfl,
        zwRevLeaf1_acc m _ (Nat.add (Nat.land w gqsp_mask768) (Nat.shiftLeft acc 768)),
        zwRevLeaf1_acc m _ (Nat.add (Nat.land w
          gqsp_mask768) 0)]
      simp (config := { ground := false }) only [Nat.add_eq, nat_shl_eq_mul_pow, Nat.add_zero]
      rw [show 2 ^ (768 * (m + 1)) = 2 ^ 768 * 2 ^ (768 * m) by
        rw [show 768 * (m + 1) = 768 + 768 * m by omega, Nat.pow_add]]
      ring
private theorem zwRevLeaf1_mod :
    ∀ (h w : ℕ), gqsp_zwRevLeaf1 h (w % 2 ^ (768 * h)) 0 = gqsp_zwRevLeaf1 h w 0
  | 0, _ => rfl
  | h + 1, w => by
      rw [zwRevLeaf1_succ, zwRevLeaf1_succ, show Nat.shiftLeft 0 768 = 0 from rfl,
        zwRevLeaf1_acc h _ (Nat.add (Nat.land (w % 2 ^ (768 * (h + 1))) gqsp_mask768) 0),
        zwRevLeaf1_acc h _ (Nat.add (Nat.land w
          gqsp_mask768) 0)]
      have hpow : 2 ^ (768 * (h + 1)) = 2 ^ 768 * 2 ^ (768 * h) := by
        rw [show 768 * (h + 1) = 768 + 768 * h by omega, Nat.pow_add]
      rw [land_mask768_eq_mod, land_mask768_eq_mod w, hpow,
        Nat.mod_mod_of_dvd w (Nat.dvd_mul_right _ _), nat_shr_eq_div_pow,
        Nat.mod_mul_right_div_self, ← nat_shr_eq_div_pow, zwRevLeaf1_mod h]
private theorem zwRevLeaf1_add :
    ∀ (h h_hi w : ℕ), gqsp_zwRevLeaf1 (h + h_hi) w 0 =
      gqsp_zwRevLeaf1 h_hi (Nat.shiftRight w (768 * h)) 0 +
        Nat.shiftLeft (gqsp_zwRevLeaf1 h w 0) (768 * h_hi)
  | 0, h_hi, w => by
      rw [Nat.zero_add, Nat.mul_zero,
        show Nat.shiftRight w 0 = w by simp only [Nat.shiftRight_eq, Nat.shiftRight_zero],
        zwRevLeaf1_zero, nat_shl_eq_mul_pow, Nat.zero_mul, Nat.add_zero]
  | h + 1, h_hi, w => by
      have h0 : Nat.shiftLeft 0 768 = 0 := rfl
      rw [show h + 1 + h_hi = (h + h_hi) + 1 by omega, zwRevLeaf1_succ, h0,
        zwRevLeaf1_acc (h + h_hi) _ (Nat.add (Nat.land w gqsp_mask768) 0),
        zwRevLeaf1_add h h_hi (Nat.shiftRight w 768), zwRevLeaf1_succ h w 0, h0,
        zwRevLeaf1_acc h _ (Nat.add (Nat.land w gqsp_mask768) 0),
        show 768 * (h + 1) = 768 + 768 * h by omega, shr_add_eq]
      simp (config := { ground := false }) only [Nat.add_eq, nat_shl_eq_mul_pow, Nat.add_zero]
      rw [show 2 ^ (768 * (h + h_hi)) = 2 ^ (768 * h) * 2 ^ (768 * h_hi) by
        rw [Nat.mul_add, Nat.pow_add]]
      ring
private theorem add_div2_sub (m : ℕ) : Nat.div m 2 + Nat.sub m (Nat.div m 2) = m :=
  Nat.add_sub_of_le (Nat.div_le_self m 2)
private theorem sub_shl_shr_eq_mod (w sh : ℕ) :
    Nat.sub w (Nat.shiftLeft (Nat.shiftRight w sh) sh) = w % 2 ^ sh := by
  rw [nat_shl_eq_mul_pow, nat_shr_eq_div_pow, Nat.sub_eq, Nat.mul_comm]
  exact (Nat.mod_def w (2 ^ sh)).symm
private theorem revPow2Leaf4SaltAux_eq_leaf1 (rem : ℕ) :
    ∀ (q s w acc : ℕ),
      gqsp_revPow2Leaf4SaltAux q rem s w acc = gqsp_zwRevLeaf1 (4 * q + rem) w acc
  | 0, s, w, acc => by
      rw [Nat.mul_zero, Nat.zero_add]
      exact (zwRevLeaf1_eq rem s w acc).symm
  | q + 1, s, w, acc => by
      have h4 : 4 * (q + 1) + rem = (((4 * q + rem) + 1) + 1) + 1 + 1 := by omega
      have h1536 : (1536 : ℕ) = 768 + 768 := rfl
      have h3072 : (3072 : ℕ) = ((768 + 768) + 768) + 768 := rfl
      change gqsp_srev4Step (gqsp_revPow2Leaf4SaltAux q rem) s w acc = _
      unfold gqsp_srev4Step gqsp_srev4Op gqsp_srev2Op gqsp_srev1Op
      simp only [sched_stfNat_eq, sched_idSalt_eq]
      rw [h4, zwRevLeaf1_succ, zwRevLeaf1_succ, zwRevLeaf1_succ, zwRevLeaf1_succ]
      simp only [h1536, h3072, shr_add_eq]
      exact revPow2Leaf4SaltAux_eq_leaf1 rem q (Nat.add 16 s) _ _
private theorem revPow2SaltAux_eq_leaf1 (k : ℕ) : ∀ (s m w : ℕ),
    gqsp_revPow2SaltAux k s m w = gqsp_zwRevLeaf1 m w 0 := by
  unfold gqsp_revPow2SaltAux
  induction k with
  | zero =>
      intro s m w
      rw [← Nat.zero_eq]
      dsimp only
      unfold gqsp_srevLeaf64
      rw [sched_stfNat_eq, revPow2Leaf4SaltAux_eq_leaf1,
        show 4 * m.div 4 + m.mod 4 = m from Nat.div_add_mod m 4]
  | succ k ih =>
      intro s m w
      dsimp only
      unfold gqsp_srevSplit
      cases hb : Nat.ble m 64
      · unfold gqsp_srevSplit at ih
        unfold gqsp_srevStepFast at ih ⊢
        simp only [Bool.false_eq_true, ↓reduceIte, sched_stfNat_eq, sched_idSalt_eq] at ih ⊢
        rw [ih (Nat.add 1 (Nat.mul 2 s)) (Nat.sub m (Nat.div m 2)) _,
          ih (Nat.mul 2 s) (Nat.div m 2) _, sub_shl_shr_eq_mod, Nat.mul_eq, zwRevLeaf1_mod,
          Nat.mul_eq]
        simpa only [Nat.add_eq, add_div2_sub] using
          (zwRevLeaf1_add (Nat.div m 2) (Nat.sub m (Nat.div m 2)) w).symm
      · simp only [↓reduceIte, gqsp_srevLeaf64, sched_stfNat_eq, revPow2Leaf4SaltAux_eq_leaf1]
        rw [show 4 * m.div 4 + m.mod 4 = m from Nat.div_add_mod m 4]
/-- Flat `7`-lane `768`-bit reversal (`0` recursors). -/
noncomputable def gqsp_zwRev7 (m768 w : ℕ) : ℕ :=
  let l0 := Nat.land w m768
  let w1 := Nat.shiftRight w 768
  let l1 := Nat.land w1 m768
  let w2 := Nat.shiftRight w1 768
  let l2 := Nat.land w2 m768
  let w3 := Nat.shiftRight w2 768
  let l3 := Nat.land w3 m768
  let w4 := Nat.shiftRight w3 768
  let l4 := Nat.land w4 m768
  let w5 := Nat.shiftRight w4 768
  let l5 := Nat.land w5 m768
  let w6 := Nat.shiftRight w5 768
  let l6 := Nat.land w6 m768
  Nat.add l6 (Nat.shiftLeft (Nat.add l5 (Nat.shiftLeft (Nat.add l4 (Nat.shiftLeft
    (Nat.add l3
      (Nat.shiftLeft (Nat.add l2 (Nat.shiftLeft (Nat.add l1 (Nat.shiftLeft l0 768)) 768)) 768))
    768)) 768)) 768)
private theorem zwRev7_eq (w : ℕ) : gqsp_zwRev7 gqsp_mask768 w = gqsp_zwRevLeaf1 7 w 0 := by
  rw [zwRevLeaf1_succ, zwRevLeaf1_succ, zwRevLeaf1_succ, zwRevLeaf1_succ, zwRevLeaf1_succ,
    zwRevLeaf1_succ, zwRevLeaf1_succ, zwRevLeaf1_zero, show Nat.shiftLeft 0 768 = 0 from rfl,
    show ∀ x, Nat.add x 0 = x from Nat.add_zero]
  rfl
/-- Flat `8`-lane `768`-bit reversal (`0` recursors). -/
noncomputable def gqsp_zwRev8 (m768 w : ℕ) : ℕ :=
  let l0 := Nat.land w m768
  let w1 := Nat.shiftRight w 768
  let l1 := Nat.land w1 m768
  let w2 := Nat.shiftRight w1 768
  let l2 := Nat.land w2 m768
  let w3 := Nat.shiftRight w2 768
  let l3 := Nat.land w3 m768
  let w4 := Nat.shiftRight w3 768
  let l4 := Nat.land w4 m768
  let w5 := Nat.shiftRight w4 768
  let l5 := Nat.land w5 m768
  let w6 := Nat.shiftRight w5 768
  let l6 := Nat.land w6 m768
  let w7 := Nat.shiftRight w6 768
  let l7 := Nat.land w7 m768
  Nat.add l7 (Nat.shiftLeft (Nat.add l6 (Nat.shiftLeft (Nat.add l5 (Nat.shiftLeft (Nat.add l4
    (Nat.shiftLeft (Nat.add l3 (Nat.shiftLeft (Nat.add l2 (Nat.shiftLeft
      (Nat.add l1 (Nat.shiftLeft l0 768)) 768)) 768)) 768)) 768)) 768)) 768)
private theorem zwRev8_eq (w : ℕ) : gqsp_zwRev8 gqsp_mask768 w = gqsp_zwRevLeaf1 8 w 0 := by
  rw [zwRevLeaf1_succ, zwRevLeaf1_succ, zwRevLeaf1_succ, zwRevLeaf1_succ, zwRevLeaf1_succ,
    zwRevLeaf1_succ, zwRevLeaf1_succ, zwRevLeaf1_succ, zwRevLeaf1_zero,
    show Nat.shiftLeft 0 768 = 0 from rfl, show ∀ x, Nat.add x 0 = x from Nat.add_zero]
  rfl
/-- Binary-tree `768`-bit lane reversal down to `m ≤ 8` with flat `7`/`8`-lane leaves (`0` inner
  `@Nat.rec`s). -/
noncomputable def gqsp_zwRevPow2Bin (m768 k : ℕ) : ℕ → ℕ → ℕ :=
  @Nat.rec (fun _ ↦ ℕ → ℕ → ℕ)
    (fun m w ↦ gqsp_zwRevLeaf1 m w 0)
    (fun _ ih m w ↦
      @Bool.rec (fun _ ↦ ℕ)
        (let h := Nat.div m 2
         let h_hi := Nat.sub m h
         let sh_lo := Nat.mul 768 h
         let sh_hi := Nat.mul 768 h_hi
         let w_hi := Nat.shiftRight w sh_lo
         let w_lo := Nat.sub w (Nat.shiftLeft w_hi sh_lo)
         Nat.add (ih h_hi w_hi) (Nat.shiftLeft (ih h w_lo) sh_hi))
        (@Bool.rec (fun _ ↦ ℕ)
          (@Bool.rec (fun _ ↦ ℕ)
            (gqsp_zwRevLeaf1 m w 0)
            (gqsp_zwRev7 m768 w)
            (Nat.beq m 7))
          (gqsp_zwRev8 m768 w)
          (Nat.beq m 8))
        (Nat.ble m 8))
    k
private theorem zwRevPow2Bin_eq_leaf1 (k : ℕ) : ∀ (m w : ℕ),
    gqsp_zwRevPow2Bin gqsp_mask768 k m w = gqsp_zwRevLeaf1 m w 0 := by
  unfold gqsp_zwRevPow2Bin
  induction k with
  | zero => exact fun _ _ ↦ rfl
  | succ k ih =>
      intro m w
      dsimp only
      cases hb : Nat.ble m 8
      · dsimp only
        rw [ih, ih, sub_shl_shr_eq_mod, Nat.mul_eq, zwRevLeaf1_mod, Nat.mul_eq]
        simpa only [Nat.add_eq, add_div2_sub] using
          (zwRevLeaf1_add (Nat.div m 2) (Nat.sub m (Nat.div m 2)) w).symm
      · cases h8 : Nat.beq m 8
        · cases h7 : Nat.beq m 7
          · rfl
          · exact Nat.beq_eq.mp h7 ▸ zwRev7_eq w
        · exact Nat.beq_eq.mp h8 ▸ zwRev8_eq w
/-- Zero-cache binary-tree SWAR `768`-bit lane reversal (`0` `DefinitionVal`s). -/
noncomputable def gqsp_zwFastRev4Swar (d n w : ℕ) : ℕ := @Nat.rec (fun _ ↦ ℕ) 0
    (fun m768 _ ↦ gqsp_zwRevPow2Bin m768 d n w) (Nat.add 1 gqsp_mask768)
theorem gqsp_zwFastRev4Swar_eq (c_idx salt d n w : ℕ) :
    gqsp_zwFastRev4Swar d n w = gqsp_fastRevSwarSalt c_idx salt d n w := by
  unfold gqsp_zwFastRev4Swar gqsp_fastRevSwarSalt gqsp_fastRevGo
  rw [gqsp_zwForce_eq, zwRevPow2Bin_eq_leaf1, sched_tfNat_eq]
  by_cases h3 : Nat.beq n 3 = true
  · obtain rfl := Nat.beq_eq.mp h3
    simpa only [h3, ↓reduceIte, gqsp_frev3_eq] using zwRevLeaf1_eq 3 _ w 0
  · by_cases h5 : Nat.beq n 5 = true
    · obtain rfl := Nat.beq_eq.mp h5
      simpa only [h3, h5, Bool.false_eq_true, ↓reduceIte, gqsp_frev5_eq] using
        (revPow2Leaf4SaltAux_eq_leaf1 1 1 _ w 0).symm
    · simpa only [h3, h5, Bool.false_eq_true, ↓reduceIte, gqsp_frevPow2Aux_eq_revPow2] using
        (revPow2SaltAux_eq_leaf1 (Nat.sub d 6) _ n w).symm
/-! ## 3. Per-Pair 2-Channel Real Tournament (`gqsp_zwEvalTournamentReal`) -/
/-- Per-pair 2-channel real SWAR node merge supporting unbalanced `(l.deg, r.deg)`. -/
noncomputable def gqsp_zwMergeNodesReal (l r : TreeNodeC) : Option TreeNodeC :=
  gqsp_mergeWithMasksR (gqsp_swarDepth r.deg) (gqsp_mkLevelMasksR l r) l r
theorem gqsp_zwMergeNodesReal_spec (gs_l gs_r : List DyadicSu2Gate) (l r out : TreeNodeC)
    (hl : TreeNodeCValid gs_l l) (hr : TreeNodeCValid gs_r r) (hlen : (gs_l ++ gs_r).length ≤
    262144) (hm :
    gqsp_zwMergeNodesReal l r = some out) : TreeNodeCValid (gs_l ++ gs_r) out := by
  have hr_le : r.deg ≤ 262144 := by
    have hr_deg : r.deg = gs_r.length := hr.1
    rw [List.length_append] at hlen
    omega
  rcases gqsp_swarDepth_bounds r.deg hr_le with ⟨_, hd⟩
  exact gqsp_mergeWithMasksR_self_spec (gqsp_swarDepth r.deg) gs_l gs_r l r out hl hr hlen hd hm
/-- Zero-cache tail-recursive `List TreeNodeC` reversal (`0` `DefinitionVal`s). -/
noncomputable def gqsp_zwRevNodesTR (xs0 acc0 : List TreeNodeC) : List TreeNodeC := @List.rec
    TreeNodeC (fun _ ↦ List TreeNodeC → List TreeNodeC) (fun acc ↦ acc)
    (fun x _ ih acc ↦ ih (x :: acc)) xs0 acc0
theorem gqsp_zwRevNodesTR_eq :
    ∀ (xs acc : List TreeNodeC), gqsp_zwRevNodesTR xs acc = xs.reverse ++ acc
  | [], _ => rfl
  | x :: xs, acc => by
      change gqsp_zwRevNodesTR xs (x :: acc) = (x :: xs).reverse ++ acc
      rw [gqsp_zwRevNodesTR_eq xs (x :: acc), List.reverse_cons, List.append_assoc,
        List.singleton_append]
/-- Zero-cache pairwise tournament pass using per-pair `gqsp_zwMergeNodesReal`. -/
noncomputable def gqsp_zwMergePairsStepReal (nds0 : List TreeNodeC) (st0 : Option TreeNodeC)
    (acc0 : List TreeNodeC) : Option (List TreeNodeC) := @List.rec TreeNodeC (fun _ ↦ Option
    TreeNodeC → List TreeNodeC → Option (List TreeNodeC)) (fun st acc ↦ @Option.rec TreeNodeC
    (fun _ ↦ Option (List TreeNodeC)) (some (gqsp_zwRevNodesTR acc [])) (fun x ↦ some
    (gqsp_zwRevNodesTR (x :: acc) [])) st) (fun z _ ih st acc ↦ @Option.rec TreeNodeC (fun _
    ↦ Option (List TreeNodeC)) (ih (some z) acc) (fun x ↦ @Option.rec TreeNodeC (fun _ ↦
    Option (List TreeNodeC)) none (fun xy ↦ ih none (xy :: acc)) (gqsp_zwMergeNodesReal x z))
    st) nds0 st0 acc0
theorem gqsp_zwMergePairsStepReal_spec (nds : List TreeNodeC) : ∀ (acc next : List TreeNodeC)
    (gss_nds gss_acc : List (List DyadicSu2Gate)),
    (List.Forall₂ TreeNodeCValid gss_nds nds → List.Forall₂
    TreeNodeCValid gss_acc acc → (gss_acc.reverse.flatten ++ gss_nds.flatten).length ≤ 262144 →
      gqsp_zwMergePairsStepReal nds none acc = some next → ∃ gss_next,
      List.Forall₂ TreeNodeCValid gss_next next ∧
    gss_next.flatten = gss_acc.reverse.flatten ++ gss_nds.flatten) ∧
      (∀ (x : TreeNodeC) (gs_x : List DyadicSu2Gate),
      TreeNodeCValid gs_x x → List.Forall₂ TreeNodeCValid gss_nds nds → List.Forall₂ TreeNodeCValid
    gss_acc acc → (gss_acc.reverse.flatten ++ (gs_x ++ gss_nds.flatten)).length ≤ 262144 →
      gqsp_zwMergePairsStepReal nds (some x) acc = some next → ∃ gss_next,
      List.Forall₂ TreeNodeCValid gss_next next ∧
    gss_next.flatten = gss_acc.reverse.flatten ++ (gs_x ++ gss_nds.flatten)) := by
  induction nds with
  | nil =>
      refine fun acc next gss_nds gss_acc ↦ ⟨fun hf2_nds hf2_acc _ h ↦ ?_,
        fun x gs_x hx hf2_nds hf2_acc _ h ↦ ?_⟩
      · rcases sched_forall2_nil_right hf2_nds with rfl
        cases h
        rw [gqsp_zwRevNodesTR_eq, List.append_nil]
        exact ⟨gss_acc.reverse, sched_forall2_reverse hf2_acc,
          by simp only [List.flatten_nil, List.append_nil]⟩
      · rcases sched_forall2_nil_right hf2_nds with rfl
        cases h
        rw [gqsp_zwRevNodesTR_eq, List.append_nil, List.reverse_cons]
        exact ⟨gss_acc.reverse ++ [gs_x], sched_forall2_append (sched_forall2_reverse hf2_acc)
          (List.Forall₂.cons hx List.Forall₂.nil),
          by simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]⟩
  | cons z rest ih =>
      refine fun acc next gss_nds gss_acc ↦ ⟨fun hf2_nds hf2_acc hlen h ↦ ?_,
        fun x gs_x hx hf2_nds hf2_acc hlen h ↦ ?_⟩
      · rcases sched_forall2_cons_right hf2_nds with ⟨gs_z, gss_rest, rfl, hz, hf2_rest⟩
        rcases (ih acc next gss_rest gss_acc).2 z gs_z hz hf2_rest hf2_acc
          (by simpa only [List.flatten_cons] using hlen) h with ⟨gss_next, hf2_next, hflat_next⟩
        exact ⟨gss_next, hf2_next, by simpa only [List.flatten_cons] using hflat_next⟩
      · rcases sched_forall2_cons_right hf2_nds with ⟨gs_y, gss_rest, rfl, hy, hf2_rest⟩
        dsimp only [gqsp_zwMergePairsStepReal] at h
        cases hxy : gqsp_zwMergeNodesReal x z with
        | none => simp [hxy] at h
        | some xy =>
          rw [hxy] at h
          dsimp only at h
          have hflat_eq : ((gs_x ++ gs_y) :: gss_acc).reverse.flatten ++ gss_rest.flatten =
              gss_acc.reverse.flatten ++ (gs_x ++ (gs_y :: gss_rest).flatten) := by
            simp only [List.reverse_cons, List.flatten_append, List.flatten_cons, List.flatten_nil,
              List.append_nil, List.append_assoc]
          have hxy_len : (gs_x ++ gs_y).length ≤ 262144 :=
            sched_len_mid_le (by simpa only [List.flatten_cons] using hlen)
          have hxy_val := gqsp_zwMergeNodesReal_spec gs_x gs_y x z xy hx hy hxy_len hxy
          rcases (ih (xy :: acc) next gss_rest ((gs_x ++ gs_y) :: gss_acc)).1
              hf2_rest (List.Forall₂.cons hxy_val hf2_acc) (hflat_eq.symm ▸ hlen) h with
            ⟨gss_next, hf2_next, hflat_next⟩
          exact ⟨gss_next, hf2_next, hflat_next.trans hflat_eq⟩
/-- Zero-cache per-pair real tournament evaluator (`0` `mergeNodesCGo` fallback on unbalanced
  shards). -/
noncomputable def gqsp_zwEvalTournamentReal (fuel : ℕ) : List TreeNodeC → Option TreeNodeC :=
    @Nat.rec (fun _ ↦ List TreeNodeC → Option TreeNodeC) (fun nds ↦ @List.rec TreeNodeC (fun _
    ↦ Option TreeNodeC) none (fun x rest1 _ ↦ @List.rec TreeNodeC (fun _ ↦ Option TreeNodeC)
    (some x) (fun _ _ _ ↦ none) rest1) nds) (fun _ ih nds ↦ @List.rec TreeNodeC (fun _ ↦
    Option TreeNodeC) none (fun x rest1 _ ↦ @List.rec TreeNodeC (fun _ ↦ Option TreeNodeC)
    (some x) (fun y rest _ ↦ @Option.rec (List TreeNodeC) (fun _ ↦ Option TreeNodeC) none ih
    (gqsp_zwMergePairsStepReal (x :: y :: rest) none [])) rest1) nds) fuel
theorem gqsp_zwEvalTournamentReal_spec (fuel : ℕ) : ∀ (nds : List TreeNodeC)
    (gss : List (List DyadicSu2Gate)) (root : TreeNodeC),
    List.Forall₂ TreeNodeCValid gss nds → gss.flatten.length ≤ 262144 →
    gqsp_zwEvalTournamentReal fuel nds = some root → TreeNodeCValid gss.flatten root := by
  have h1 {r : TreeNodeC} {gss : List (List DyadicSu2Gate)} {root : TreeNodeC}
      (hf2 : List.Forall₂ TreeNodeCValid gss [r]) (h : some r = some root) :
      TreeNodeCValid gss.flatten root := by
    cases h
    rcases sched_forall2_cons_right hf2 with ⟨_, _, rfl, hr, hf2_0⟩
    rcases sched_forall2_nil_right hf2_0 with rfl
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using hr
  induction fuel with
  | zero =>
      rintro (_ | ⟨r, _ | ⟨_, _⟩⟩) gss root hf2 _ h
      · cases h
      · exact h1 hf2 h
      · cases h
  | succ fuel ih =>
      rintro (_ | ⟨x, _ | ⟨y, rest⟩⟩) gss root hf2 hlen h
      · cases h
      · exact h1 hf2 h
      · dsimp only [gqsp_zwEvalTournamentReal] at h
        cases hmp : gqsp_zwMergePairsStepReal (x :: y :: rest) none [] with
        | none => simp [hmp] at h
        | some next =>
          rw [hmp] at h
          dsimp only at h
          rcases (gqsp_zwMergePairsStepReal_spec (x :: y :: rest) [] next gss []).1
              hf2 List.Forall₂.nil
              (by simpa only [List.reverse_nil, List.flatten_nil, List.nil_append] using hlen) hmp
            with ⟨gss_next, hf2_next, hflat_next⟩
          have hflat' : gss_next.flatten = gss.flatten := by
            simpa only [List.reverse_nil, List.flatten_nil, List.nil_append] using hflat_next
          exact hflat' ▸ ih next gss_next root hf2_next (hflat'.symm ▸ hlen) h
/-! ## 4. Zero-Cache Single-Pass `pqM` Root Split & Turnkey Base Segment Constructor -/
/-- Forces a `List ℕ` to `cons` WHNF before continuing (`1` outer call, `O(1)`). -/
noncomputable def gqsp_zwForceNonEmptyNat (xs : List ℕ) (f : List ℕ → Bool) : Bool :=
  @List.rec ℕ (fun _ ↦ Bool) false (fun x xt _ ↦ f (x :: xt)) xs
/-- Forces a `List PQPair` to `cons` WHNF before continuing (`1` outer call, `O(1)`). -/
noncomputable def gqsp_zwForceNonEmptyPQ (xs : List PQPair) (f : List PQPair → Bool) : Bool :=
  @List.rec PQPair (fun _ ↦ Bool) false (fun x xt _ ↦ f (x :: xt)) xs
/-- Closure-free 1-angle `(ep, eq, op, oq)` reversed interleaver (`0` `@Nat.rec` closures). -/
noncomputable def gqsp_zwInterleaveFast (B2 BIAS : ℕ) (uP0 uQ0 ruP0 ruQ0 : List ℕ)
    (acc0 : List PQPair) : List PQPair := @List.rec ℕ
    (fun _ ↦ List ℕ → List ℕ → List ℕ → List PQPair → List PQPair) (fun _ _ _ a ↦ a) (fun up _
    ih luq lrup lruq a ↦ @List.rec ℕ (fun _ ↦ List PQPair) a (fun uq uqt _ ↦ @List.rec ℕ (fun
    _ ↦ List PQPair) a (fun rup rupt _ ↦ @List.rec ℕ (fun _ ↦ List PQPair) a (fun ruq ruqt _ ↦
    ih uqt rupt ruqt (PQPair.mk (Nat.sub B2 (Nat.add ruq BIAS)) (Nat.add rup BIAS) ::
    PQPair.mk (Nat.add up BIAS) (Nat.add uq BIAS) :: a)) lruq) lrup) luq) uP0 uQ0 ruP0 ruQ0
    acc0
private theorem zwInterleaveFast_eq (B2 BIAS : ℕ) :
    ∀ (uP uQ ruP ruQ : List ℕ) (acc : List PQPair),
      gqsp_zwInterleaveFast B2 BIAS uP uQ ruP ruQ acc =
        gqsp_zwInterleave1AngleRevTR B2 BIAS uP uQ ruP ruQ acc
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, _, _ => rfl
  | _ :: _, _ :: _, [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, [], _ => rfl
  | up :: upt, uq :: uqt, rup :: rupt, ruq :: ruqt, acc => by
      dsimp only [gqsp_zwInterleaveFast, gqsp_zwInterleave1AngleRevTR]
      rw [gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwForce_eq]
      exact zwInterleaveFast_eq B2 BIAS upt uqt rupt ruqt _
/-- Closure-free `.p`-only reversed outer Hadamard pass (`0` `@Nat.rec` closures). -/
noncomputable def gqsp_zwHadamardFast (B : ℕ) (pq0 : List PQPair) (q0 : ℕ) (acc0 : List ℕ) :
    List ℕ := @List.rec PQPair (fun _ ↦ ℕ → List ℕ → List ℕ)
    (fun q_prev acc ↦ Nat.shiftRight (Nat.add B q_prev) 1 :: acc) (fun h _ ih q_prev acc ↦
    @PQPair.rec (fun _ ↦ List ℕ) (fun ph qh ↦ ih qh (Nat.shiftRight (Nat.add ph q_prev) 1 ::
    acc)) h) pq0 q0 acc0
private theorem zwHadamardFast_eq (B : ℕ) :
    ∀ (pq : List PQPair) (q_prev : ℕ) (acc : List ℕ),
      gqsp_zwHadamardFast B pq q_prev acc = gqsp_zwHadamardRevPOnly B pq q_prev acc
  | [], _, _ => by
      dsimp only [gqsp_zwHadamardFast, gqsp_zwHadamardRevPOnly]
      rw [gqsp_zwForce_eq]
  | ⟨ph, qh⟩ :: t, q_prev, acc => by
      dsimp only [gqsp_zwHadamardFast, gqsp_zwHadamardRevPOnly]
      rw [gqsp_zwForce_eq]
      exact zwHadamardFast_eq B t qh _
/-- Zero-cache 1-angle root unpack + outer Hadamard + split CPS wrapper (`0` `O(M)` cache,
`pqM` forced once before `p_fin` so `uPre, ruP, uQre, ruQ` are freed first). -/
noncomputable def gqsp_zwWithRootSplit1Angle
    (d M : ℕ) (g0 : DyadicSu2Gate) (root : TreeNodeC)
    (cont : List PQPair → List ℕ → ℕ → List ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) : Bool :=
  @TreeNodeC.rec (fun _ ↦ Bool)
    (fun rdeg _ rrep1 rprp rprn _ _ rqrp rqrn _ _ rerr ↦
      @Nat.rec (fun _ ↦ Bool) false (fun n_lanes _ ↦
        @Nat.rec (fun _ ↦ Bool) false (fun rep_bcomb _ ↦
          let c_ar := smToPolyPN g0.sar g0.mar
          let c_br := smToPolyPN g0.sbr g0.mbr
          let nc_br := negPolyPN c_br
          @Nat.rec (fun _ ↦ Bool) false (fun rqrp_rev _ ↦
            @Nat.rec (fun _ ↦ Bool) false (fun rqrn_rev _ ↦
              gqsp_zwForceNonEmptyNat
                (gqsp_zwFinishRootVec2Real d n_lanes rep_bcomb
                  c_ar ⟨rprp, rprn⟩ nc_br ⟨rqrp_rev, rqrn_rev⟩)
                (fun uPre ↦
                  gqsp_zwForceNonEmptyNat (gqsp_zwRevNatTR uPre []) (fun ruP ↦
                    @Nat.rec (fun _ ↦ Bool) false (fun rprp_rev _ ↦
                      @Nat.rec (fun _ ↦ Bool) false (fun rprn_rev _ ↦
                        gqsp_zwForceNonEmptyNat
                          (gqsp_zwFinishRootVec2Real d n_lanes rep_bcomb
                            c_ar ⟨rqrp, rqrn⟩ c_br ⟨rprp_rev, rprn_rev⟩)
                          (fun uQre ↦
                            gqsp_zwForceNonEmptyNat (gqsp_zwRevNatTR uQre []) (fun ruQ ↦
                              let B :=
                                0x1000000000000000000000000000000000000000000000000000000000000
                              let B2 :=
                                0x2000000000000000000000000000000000000000000000000000000000000
                              let Bw := 0x1000000000000000000000000000000000000000000000000
                              let shift0 := 0x1000000000000000000000000
                              let bias_out :=
                                0xfffffffffffffffffffffc00000000000000000000000000000000000000
                              gqsp_zwForceNonEmptyPQ
                                (gqsp_zwRevPQTR
                                  (gqsp_zwInterleaveFast B2 bias_out uPre uQre ruP ruQ []) [])
                                (fun pqM ↦
                                  @Nat.rec (fun _ ↦ Bool) false (fun R_final _ ↦
                                    @Nat.rec (fun _ ↦ Bool) false (fun M1 _ ↦
                                      let p_fin :=
                                        gqsp_zwRevNatTR (gqsp_zwHadamardFast B pqM B []) []
                                      @Prod.rec (List ℕ) (ℕ × List ℕ) (fun _ ↦
                                        Bool) (fun neg_re p2_re ↦
                                        @Prod.rec ℕ (List ℕ) (fun _ ↦ Bool) (fun pc_re pos_re ↦
                                          cont pqM neg_re pc_re pos_re R_final M1 B B2 Bw shift0)
                                          p2_re)
                                        (gqsp_zwSplitPRev B M1 p_fin []))
                                      (Nat.add 1 (Nat.add 1 M)))
                                    (Nat.add 1 (Nat.add 3 (Nat.shiftRight rerr 206)))))))
                        (Nat.add 1 (gqsp_zwFastRev4Swar d n_lanes rprn)))
                      (Nat.add 1 (gqsp_zwFastRev4Swar d n_lanes rprp)))))
              (Nat.add 1 (gqsp_zwFastRev4Swar d n_lanes rqrn)))
            (Nat.add 1 (gqsp_zwFastRev4Swar d n_lanes rqrp)))
          (Nat.add 1 (Nat.mul ta_B_COMB rrep1)))
        (Nat.add 1 (Nat.add 1 rdeg)))
    root
private theorem hex_eq_ta_shift0 : (0x1000000000000000000000000 : ℕ) = ta_shift0 := rfl
private theorem hex_eq_ta_Bw :
    (0x1000000000000000000000000000000000000000000000000 : ℕ) = ta_Bw := rfl
private theorem hex_eq_ta_B :
    (0x1000000000000000000000000000000000000000000000000000000000000 : ℕ) = ta_B := rfl
private theorem hex_eq_ta_B2 :
    (0x2000000000000000000000000000000000000000000000000000000000000 : ℕ) = ta_B2 := rfl
private theorem hex_eq_ta_BIAS_OUT :
    (0xfffffffffffffffffffffc00000000000000000000000000000000000000 : ℕ) = ta_BIAS_OUT := rfl
private theorem zwForce_imp_tfBool {f1 f2 : ℕ → Bool} {x1 x2 : ℕ} (h : @Nat.rec (fun _ ↦ Bool)
    false (fun v _ ↦ f1 v) (Nat.add 1 x1) = true) (hx : x1 = x2)
    (hf : ∀ v, f1 v = true → f2 v = true) : ta_tfBool f2 x2 = true := by
  subst hx
  rw [gqsp_zwForce_eq] at h
  rw [ta_tfBool_eq]
  exact hf x1 h
private theorem zwForceNonEmptyNat_imp_forceListBool {xs1 xs2 : List ℕ} {f1 f2 : List ℕ →
    Bool} (h : gqsp_zwForceNonEmptyNat xs1 f1 = true) (hxs : xs1 = xs2) (hf : ∀ ys,
    f1 ys = true → f2 ys = true) :
    gqsp_forceListBool xs2 f2 = true := by
  subst hxs
  cases xs1 with
  | nil => cases h
  | cons x xt =>
    rw [gqsp_forceListBool_eq]
    exact hf (x :: xt) h
private theorem zwForceNonEmptyPQ_true_imp {xs : List PQPair} {f : List PQPair →
    Bool} (h : gqsp_zwForceNonEmptyPQ xs f = true) : f xs = true := by
  cases xs with
  | nil => cases h
  | cons _ _ => exact h
private theorem prodSplit_rec_imp_casesOn {p : List ℕ × ℕ × List ℕ}
    {c : List ℕ → ℕ → List ℕ → Bool} (h : @Prod.rec (List ℕ) (ℕ × List ℕ) (fun _ ↦ Bool) (fun
    a p2 ↦ @Prod.rec ℕ (List ℕ) (fun _ ↦ Bool) (c a) p2) p = true) : @Prod.casesOn _ _
    (fun _ ↦ Bool) p (fun a p2 ↦ @Prod.casesOn _ _ (fun _ ↦ Bool) p2 (c a)) = true := by
  rcases p with ⟨a, b, d⟩
  exact h
private theorem ta_tfBool_imp2' {f1 f2 f3 : ℕ → Bool} {x : ℕ} (h1 : ta_tfBool f1 x =
    true) (h2 : ta_tfBool f2 x = true) (h : ∀ v,
    f1 v = true → f2 v = true → f3 v = true) : ta_tfBool f3 x = true := by
  rw [ta_tfBool_eq] at h1 h2 ⊢
  exact h x h1 h2
private theorem forceListBool_imp2' {xs : List ℕ} {f1 f2 f3 : List ℕ →
    Bool} (h1 : gqsp_forceListBool xs f1 = true) (h2 : gqsp_forceListBool xs f2 = true) (h : ∀ ys,
    f1 ys = true → f2 ys = true → f3 ys =
    true) : gqsp_forceListBool xs f3 = true := by
  rw [gqsp_forceListBool_eq] at h1 h2 ⊢
  exact h xs h1 h2
theorem gqsp_zwWithRootSplit1Angle_imp_lowMem (d M : ℕ) (g0 : DyadicSu2Gate) (root : TreeNodeC)
    (cont : List PQPair → List ℕ → ℕ → List ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ →
    Bool) (h : gqsp_zwWithRootSplit1Angle d M g0
    root cont = true) : gqsp_withRootSplit1AngleLowMem d M g0 root cont = true := by
  rcases root with ⟨rdeg, rsalt, rrep1, rprp, rprn, rpip, rpin, rqrp, rqrn, rqip, rqin, rerr⟩
  unfold gqsp_zwWithRootSplit1Angle at h
  unfold gqsp_withRootSplit1AngleLowMem
  have hR_eq : Nat.add 3 (Nat.shiftRight rerr 206) =
      Nat.add (Nat.add (Nat.shiftRight rerr 206) 2) 1 := by
    change 3 + _ = (_ + 2) + 1
    omega
  refine zwForce_imp_tfBool h rfl fun n_lanes h ↦
    zwForce_imp_tfBool h (Nat.mul_comm ta_B_COMB rrep1) fun rep_bcomb h ↦
    zwForce_imp_tfBool h (gqsp_zwFastRev4Swar_eq 8 rsalt d n_lanes rqrp) fun rqrp_rev h ↦
    zwForce_imp_tfBool h (gqsp_zwFastRev4Swar_eq 8 rsalt d n_lanes rqrn) fun rqrn_rev h ↦
    zwForceNonEmptyNat_imp_forceListBool h
      (by rw [gqsp_zwFinishRootVec2Real_eq 0x410001, ← gqsp_zwSunpackShr256Chunked_fun_eq])
      fun uPre h ↦ zwForceNonEmptyNat_imp_forceListBool h rfl fun ruP h ↦
    zwForce_imp_tfBool h (gqsp_zwFastRev4Swar_eq 8 rsalt d n_lanes rprp) fun rprp_rev h ↦
    zwForce_imp_tfBool h (gqsp_zwFastRev4Swar_eq 8 rsalt d n_lanes rprn) fun rprn_rev h ↦
    zwForceNonEmptyNat_imp_forceListBool h
      (by rw [gqsp_zwFinishRootVec2Real_eq 0x420001, ← gqsp_zwSunpackShr256Chunked_fun_eq])
      fun uQre h ↦ zwForceNonEmptyNat_imp_forceListBool h rfl fun ruQ hleaf ↦
    zwForce_imp_tfBool (zwForceNonEmptyPQ_true_imp hleaf) hR_eq fun R_final hstep ↦
    zwForce_imp_tfBool hstep (Nat.add_comm 1 M) fun M1 hfin ↦ ?_
  rw [ta_tfBool_eq, ta_tfBool_eq, ta_tfBool_eq, ta_tfBool_eq]
  have hpq_eq : gqsp_zwRevPQTR (gqsp_zwInterleaveFast
      0x2000000000000000000000000000000000000000000000000000000000000
      0xfffffffffffffffffffffc00000000000000000000000000000000000000 uPre uQre ruP ruQ []) [] =
      gqsp_zwRevPQTR (gqsp_zwInterleave1AngleRevTR ta_B2 ta_BIAS_OUT uPre uQre ruP ruQ []) [] := by
    rw [zwInterleaveFast_eq, hex_eq_ta_B2, hex_eq_ta_BIAS_OUT]
  dsimp only at hfin
  rw [hpq_eq, zwHadamardFast_eq, hex_eq_ta_B, hex_eq_ta_B2, hex_eq_ta_Bw, hex_eq_ta_shift0] at hfin
  exact @prodSplit_rec_imp_casesOn _ (fun neg_re pc_re pos_re ↦ cont _ neg_re pc_re pos_re
    R_final M1 ta_B ta_B2 ta_Bw ta_shift0) hfin
/-- Per-pair zero-cache upper-tree + 1-angle post-root check. -/
noncomputable def gqsp_upperRealTreePostChunks2Ble
    (d fuel M N_rec W_err_d0 W_err_dpos pad : ℕ) (ry_g0 : DyadicRyGate)
    (subNodes : List TreeNodeC) (ws_unpad : List ℕ) : Bool := @Option.rec TreeNodeC
    (fun _ ↦ Bool) false (fun root ↦ gqsp_oneAnglePostRootRealFastBle d M N_rec W_err_d0
    W_err_dpos pad (ryToSu2Gate ry_g0) root ws_unpad)
    (gqsp_zwEvalTournamentReal fuel subNodes)
/-- Zero-cache split `t1`-only post-root bound (`chebL1 ≤ N_rec_1 * shift0`). -/
noncomputable def gqsp_upperRealTreePostT1LowMem2Ble
    (d fuel M N_rec_1 W_err_d0 W_err_dpos pad : ℕ)
    (ry_g0 : DyadicRyGate) (subNodes : List TreeNodeC) (ws_unpad : List ℕ) : Bool :=
  @Option.rec TreeNodeC (fun _ ↦ Bool)
    false
    (fun root ↦
      gqsp_zwWithRootSplit1Angle d M (ryToSu2Gate ry_g0) root
        (fun _ neg_re pc_re pos_re R_final M1 B B2 Bw shift0 ↦
          let t1 := gqsp_zwChebL1POnly M1 B B2 Bw R_final W_err_d0 W_err_dpos pad
            neg_re pc_re pos_re ws_unpad
          Nat.ble t1 (Nat.mul N_rec_1 shift0)))
    (gqsp_zwEvalTournamentReal fuel subNodes)
/-- Zero-cache split `t2 + t3` post-root bound (`asymDefect + qResid ≤ N_rec_23 * shift0`). -/
noncomputable def gqsp_upperRealTreePostT23LowMem2Ble (d fuel M N_rec_23 : ℕ)
    (ry_g0 : DyadicRyGate) (subNodes : List TreeNodeC) : Bool :=
  @Option.rec TreeNodeC (fun _ ↦ Bool)
    false
    (fun root ↦
      gqsp_zwWithRootSplit1Angle d M (ryToSu2Gate ry_g0) root
        (fun pqM neg_re _ pos_re R_final M1 B B2 _ shift0 ↦
          let t2 := gqsp_zwAsymDefectPOnly M1 B B2 R_final neg_re pos_re
          let t3 := gqsp_zwQResidHadamard B B2 R_final pqM B 0
          Nat.ble (Nat.add t2 t3) (Nat.mul N_rec_23 shift0)))
    (gqsp_zwEvalTournamentReal fuel subNodes)
private theorem prodSplit_imp2 {p : List ℕ × ℕ × List ℕ}
    {c1 c2 c3 : List ℕ → ℕ → List ℕ → Bool}
    (h1 : @Prod.casesOn _ _ (fun _ ↦ Bool) p (fun a p2 ↦
      @Prod.casesOn _ _ (fun _ ↦ Bool) p2 (c1 a)) = true)
    (h2 : @Prod.casesOn _ _ (fun _ ↦ Bool) p (fun a p2 ↦
      @Prod.casesOn _ _ (fun _ ↦ Bool) p2 (c2 a)) = true)
    (h : ∀ a b c, c1 a b c = true → c2 a b c = true → c3 a b c = true) :
    @Prod.casesOn _ _ (fun _ ↦ Bool) p (fun a p2 ↦
      @Prod.casesOn _ _ (fun _ ↦ Bool) p2 (c3 a)) = true := by
  rcases p with ⟨a, b, c⟩
  exact h a b c h1 h2
private theorem withRootSplit1AngleLowMem_imp2' (d M : ℕ) (g0 : DyadicSu2Gate) (root : TreeNodeC)
    (c1 c2 c3 : List PQPair → List ℕ → ℕ → List ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ →
    Bool) (himp : ∀ pqM neg_re pc_re pos_re
    R_final M1 B B2 Bw shift0,
      c1 pqM neg_re pc_re pos_re R_final M1 B B2 Bw shift0 = true →
      c2 pqM neg_re pc_re pos_re R_final M1 B B2 Bw shift0 = true →
      c3 pqM neg_re pc_re pos_re R_final M1 B B2 Bw shift0 =
    true) (h1 : gqsp_withRootSplit1AngleLowMem d M g0 root c1 =
      true) (h2 : gqsp_withRootSplit1AngleLowMem d M g0 root c2 =
      true) : gqsp_withRootSplit1AngleLowMem d M g0 root c3 = true := by
  rcases root with ⟨rdeg, rsalt, rrep1, rprp, rprn, rpip, rpin, rqrp, rqrn, rqip, rqin, rerr⟩
  unfold gqsp_withRootSplit1AngleLowMem at h1 h2 ⊢
  exact ta_tfBool_imp2' h1 h2 fun n_lanes h1 h2 ↦ ta_tfBool_imp2' h1 h2 fun rep_bcomb h1 h2 ↦
    ta_tfBool_imp2' h1 h2 fun rqrp_rev h1 h2 ↦ ta_tfBool_imp2' h1 h2 fun rqrn_rev h1 h2 ↦
    forceListBool_imp2' h1 h2 fun uPre h1 h2 ↦ forceListBool_imp2' h1 h2 fun ruP h1 h2 ↦
    ta_tfBool_imp2' h1 h2 fun rprp_rev h1 h2 ↦ ta_tfBool_imp2' h1 h2 fun rprn_rev h1 h2 ↦
    forceListBool_imp2' h1 h2 fun uQre h1 h2 ↦ forceListBool_imp2' h1 h2 fun ruQ h1 h2 ↦
    ta_tfBool_imp2' h1 h2 fun R_final h1 h2 ↦ ta_tfBool_imp2' h1 h2 fun M1 h1 h2 ↦
    ta_tfBool_imp2' h1 h2 fun B h1 h2 ↦ ta_tfBool_imp2' h1 h2 fun B2 h1 h2 ↦
    ta_tfBool_imp2' h1 h2 fun Bw h1 h2 ↦ ta_tfBool_imp2' h1 h2 fun shift0 h1' h2' ↦
    prodSplit_imp2 h1' h2' (fun neg_re pc_re pos_re ↦
      himp _ neg_re pc_re pos_re R_final M1 B B2 Bw shift0)
private theorem ble_add_of_ble_split' {t1 t2 t3 n1 n23 n sh : ℕ} (hN : n1 + n23 ≤ n)
    (h1 : Nat.ble t1 (Nat.mul n1 sh) = true)
    (h23 : Nat.ble (Nat.add t2 t3) (Nat.mul n23 sh) = true) :
    Nat.ble (Nat.add (Nat.add t1 t2) t3) (Nat.mul n sh) = true :=
  Nat.ble_eq.mpr <| (Nat.add_assoc t1 t2 t3).trans_le <|
    (Nat.add_le_add (Nat.ble_eq.mp h1) (Nat.ble_eq.mp h23)).trans <|
      (Nat.add_mul n1 n23 sh).symm.trans_le (Nat.mul_le_mul_right sh hN)
theorem gqsp_upperRealTreePostChunks2Ble_of_split
    (d fuel M N_rec_1 N_rec_23 N_rec W_err_d0 W_err_dpos pad : ℕ) (ry_g0 : DyadicRyGate)
    (subNodes : List TreeNodeC) (ws_unpad : List ℕ) (hN : N_rec_1 + N_rec_23 ≤
    N_rec)
      (ht1 : gqsp_upperRealTreePostT1LowMem2Ble d fuel M N_rec_1 W_err_d0 W_err_dpos pad ry_g0
      subNodes ws_unpad =
      true) (ht23 : gqsp_upperRealTreePostT23LowMem2Ble d fuel M N_rec_23 ry_g0 subNodes =
    true) : gqsp_upperRealTreePostChunks2Ble d fuel M N_rec W_err_d0 W_err_dpos pad ry_g0 subNodes
      ws_unpad = true := by
  unfold gqsp_upperRealTreePostChunks2Ble
  unfold gqsp_upperRealTreePostT1LowMem2Ble at ht1
  unfold gqsp_upperRealTreePostT23LowMem2Ble at ht23
  cases hup : gqsp_zwEvalTournamentReal fuel subNodes with
  | none => simp [hup] at ht1
  | some root =>
      rw [hup] at ht1 ht23
      dsimp only at ht1 ht23 ⊢
      rw [← gqsp_oneAnglePostRootRealLowMemBle_eq]
      exact withRootSplit1AngleLowMem_imp2' d M (ryToSu2Gate ry_g0) root _ _ _
        (fun _ _ _ _ _ _ _ _ _ _ h1' h2' ↦ ble_add_of_ble_split' hN h1' h2')
        (gqsp_zwWithRootSplit1Angle_imp_lowMem d M (ryToSu2Gate ry_g0) root _ ht1)
        (gqsp_zwWithRootSplit1Angle_imp_lowMem d M (ryToSu2Gate ry_g0) root _ ht23)
/-- Turnkey chunked + sub-sharded base `GeneralBetaSegmentCert` constructor using per-pair
`gqsp_zwEvalTournamentReal` (`gqsp_upperRealTreePostChunks2Ble`). -/
noncomputable def gqsp_mkBaseGeneralBetaSegmentCertRealChunkShards2
    (d fuel M K β_nat N_rec N_tay N_cat N_base W_err_d0 W_err_dpos pad : ℕ)
    (C_orig_list : List ℕ) (ry_g0 : DyadicRyGate) (ry_chs : List (List DyadicRyGate))
    (subNodes : List TreeNodeC) (gss_shards : List (List DyadicSu2Gate))
    (ws_unpad : List ℕ)
    (hM_cap : M ≤ 262144)
    (hMK : M + 1 ≤ K) (hβ_lt : β_nat < K + 2)
    (hunpad_gt : M + 1 < ws_unpad.length)
    (hpad : ws_unpad.length + pad = K + 1)
    (hws_err : ∀ k < K + 1,
      let scale0 := 2 ^ 48 * powMulFast (2 ^ 48) 2 1
      let Bw := powMulFast (2 ^ 48) 1 1 * scale0
      |(scale0 : ℝ) * chebTaylorWeight (β_nat : ℝ) K k -
          (((ws_unpad ++ List.replicate pad ta_Bw).getD k Bw : ℝ) - (Bw : ℝ))| ≤
        (if k = 0 then (W_err_d0 : ℝ) else (W_err_dpos : ℝ)))
    (h_tay_nat : β_nat ^ (K + 1) * (K + 2) * 2 ^ 48 ≤ N_tay * (K + 1).factorial * (K + 2 - β_nat))
    (hN_sum : N_rec + N_tay + N_cat ≤ N_base)
    (h_co : gqsp_codeOrigLoop (Nat.add M 1) C_orig_list 0 = true)
    (h_ry : gqsp_ryLenContrChunksLoop (Nat.add M 1) 0x1000000000000000000000000 ([ry_g0] :: ry_chs)
      0 = true)
    (h_cat_ble : biCatBridgeCheckBle M N_cat C_orig_list (ry_g0 :: ry_chs.flatten) = true)
    (hf2_shards : List.Forall₂ TreeNodeCValid gss_shards subNodes)
    (hflat_shards : gss_shards.flatten = ry_chs.flatten.map ryToSu2Gate)
    (h_upper_post : gqsp_upperRealTreePostChunks2Ble d fuel M N_rec W_err_d0 W_err_dpos pad
      ry_g0 subNodes ws_unpad = true) :
    GeneralBetaSegmentCert β_nat M N_base where
  C := fun i ↦ Fin.ofNat (2 ^ 42) (C_orig_list.getD i.val 0)
  h_seg_bound := by
    intro k m_BE α A U_BE τ hα hτ hBE hβ_eq hnorm_A sys anc
    let ry_gs := ry_chs.flatten
    have h_ry_flat : gqsp_ryLenContrLoop (Nat.add M 1) 0x1000000000000000000000000 (ry_g0 :: ry_gs)
      0 = true := by
      rwa [gqsp_ryLenContrChunksLoop_eq, List.flatten_cons, List.singleton_append] at h_ry
    have hC_len : C_orig_list.length = M + 1 := by
      simpa [Nat.add_eq] using (gqsp_codeOrigLoop_spec (Nat.add M 1) C_orig_list 0 h_co).1
    rcases gqsp_ryLenContrLoop_spec (Nat.add M 1) 0x1000000000000000000000000 (ry_g0 :: ry_gs) 0
      h_ry_flat
      with ⟨hg_len0, hg_contr_aux⟩
    have hg_len : (ry_g0 :: ry_gs).length = M + 1 := by simpa [Nat.add_eq] using hg_len0
    have hgs_len : ry_gs.length = M := Nat.succ.inj hg_len
    have hcs_int := gates_contraction_of_ble 48 (ry_g0 :: ry_gs)
      (fun s ↦ (ry_g0 :: ry_gs).getD s defaultGate) (fun _ ↦ rfl)
      (by simpa [gatesContractionBle, forceNatFast_eq] using hg_contr_aux)
    rw [hg_len] at hcs_int
    have hg0_sq : (gateSM ry_g0).1.2 * (gateSM ry_g0).1.2 + (gateSM ry_g0).2.2 *
      (gateSM ry_g0).2.2 ≤ 2 ^ 96 := by
      simpa [List.getD_eq_getElem?_getD] using
        gatesContractionBleAux_true_imp 0x1000000000000000000000000 (ry_g0 :: ry_gs) 0 hg_contr_aux
          (by simp)
    unfold gqsp_upperRealTreePostChunks2Ble at h_upper_post
    cases hup : gqsp_zwEvalTournamentReal fuel subNodes with
    | none => simp [hup] at h_upper_post
    | some root =>
      rw [hup] at h_upper_post
      dsimp only at h_upper_post
      rw [gqsp_oneAnglePostRootRealFastBle_eq] at h_upper_post
      have hvalid : TreeNodeCValid (ry_gs.map ryToSu2Gate) root := by
        simpa only [hflat_shards] using gqsp_zwEvalTournamentReal_spec fuel subNodes gss_shards root
          hf2_shards
          (by rw [hflat_shards, List.length_map, hgs_len]; exact hM_cap) hup
      have h_rec_three := gqsp_oneAnglePostRootFastBleOf_spec
        (gqsp_fastRevSwarSalt 8 root.salt) gqsp_sunpackShr256Chunked d M K β_nat N_rec W_err_d0
          W_err_dpos pad
        ry_g0 ry_gs hgs_len root ws_unpad hunpad_gt hpad hws_err hvalid
        (gqsp_fastRevSwarSalt_spec 8 root.salt d (M + 1))
        (gqsp_sunpackShr256Chunked_spec d (M + 1)) hg0_sq h_upper_post
      have hbound0 := norm_biCatSegment_sub_exp_mul_proj_le_of_rec_bound
        (m := m_BE + 1) le_rfl τ hα hτ hBE M K β_nat N_rec N_tay N_cat hMK hβ_lt hβ_eq hnorm_A
        C_orig_list hC_len (fun i ↦ Fin.ofNat (2 ^ 42) (C_orig_list.getD i.val 0)) (fun _ ↦ rfl)
        (ry_g0 :: ry_gs) hg_len (fun s ↦ (ry_g0 :: ry_gs).getD s defaultGate) (fun _ ↦ rfl)
        hcs_int h_rec_three h_tay_nat h_cat_ble
      dsimp only at hbound0
      exact hbound0.trans (div_le_div_of_nonneg_right (by exact_mod_cast hN_sum) (by positivity))
end ZeroCacheTournamentAndRootUnpack
end GqspWronskian62592
end
end Gqsp0e_RootUnpackLowMem

end QuantumComputation.Specs.StoppingPowerSolution
end
