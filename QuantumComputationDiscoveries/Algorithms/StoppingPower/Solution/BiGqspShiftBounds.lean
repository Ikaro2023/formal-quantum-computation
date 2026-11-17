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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Slot3Qutrit216
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.BiGqspSu2PolyData

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section TwoAngleBiGqspVerifierBridge_aux_p2
local instance (priority := 1000000) instNeZeroTwoPow_TwoAngleBiGqspVerifierBridge_aux_p2 (k :
    ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

namespace TwoAngleBiGqspVerifierBridge

section ConfigTwoAngleBiGqspVerifierBridge

section ConfigSec3B_TwoAngleRootAndCertStitch
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 2048

open scoped Matrix Matrix.Norms.L2Operator BigOperators
open Real Operator Matrix Circuit TFreeLaurentGQSP
open CatalyzedLaurentGQSP TFreeLaurentGQSPPresets
open TFreeLaurentGQSPPresets.FastRecurrenceVerifier
open TFreeLaurentGQSPPresets.FastIntervalRecurrenceVerifier
open BidirectionalCatalyzedGQSP
open BidirectionalCatalyzedGQSPBridge
open BidirectionalIntervalRecurrenceVerifier

/-- `96`-bit inner recurrence shift `2 ^ 96`. -/
def ta_shift0 : ℕ := Nat.shiftLeft 1 96
/-- `144`-bit post-root fixed-point scale `2 ^ 144`. -/
def ta_scale0 : ℕ := Nat.shiftLeft 1 144
/-- `240`-bit `PQPair` midpoint bias `2 ^ 240`. -/
def ta_B : ℕ := Nat.shiftLeft 1 240
/-- Doubled `PQPair` bias `2 * ta_B = 2 ^ 241`. -/
def ta_B2 : ℕ := Nat.mul 2 ta_B
/-- `192`-bit Chebyshev target weight bias `2 ^ 192`. -/
def ta_Bw : ℕ := Nat.shiftLeft 1 192
/-- `410`-bit root lane bias `2 ^ 410` (absorbs `4` products `< 2 ^ 403` without borrow). -/
def ta_B_COMB : ℕ := Nat.shiftLeft 1 410
/-- Post-`shr 256` output offset `2 ^ 240 - 2 ^ 154` re-centering `ta_B_COMB >>> 256` to `ta_B`. -/
def ta_BIAS_OUT : ℕ := Nat.sub ta_B (Nat.shiftLeft 1 154)

theorem ta_B2_eq : ta_B2 = 2 * ta_B := rfl

theorem ta_ite_pos {c : Prop} {_h : Decidable c} (hc : c) {α : Sort*} {t e : α} :
    @ite α c _h t e = t := by
  cases _h with
  | isTrue _ => rfl
  | isFalse hnc => exact absurd hc hnc

private theorem ta_ite_neg {c : Prop} {_h : Decidable c} (hnc : ¬c) {α : Sort*} {t e : α} :
    @ite α c _h t e = e := by
  cases _h with
  | isTrue hc => exact absurd hc hnc
  | isFalse _ => rfl

theorem map_getD_lt (f : ℕ → ℕ) :
    ∀ (xs : List ℕ) (m : ℕ), m < xs.length → (xs.map f).getD m 0 = f (xs.getD m 0)
  | [], _, hm => by cases hm
  | _ :: _, 0, _ => rfl
  | _ :: xt, m + 1, hm => map_getD_lt f xt m (Nat.lt_of_succ_lt_succ hm)

theorem zipWith_getD_lt (f : ℕ → ℕ → ℕ) :
    ∀ (as bs : List ℕ) (m : ℕ), as.length = bs.length → m < as.length →
      (List.zipWith f as bs).getD m 0 = f (as.getD m 0) (bs.getD m 0)
  | [], _, _, _, hm => by cases hm
  | _ :: _, [], _, hlen, _ => by cases hlen
  | _ :: _, _ :: _, 0, _, _ => rfl
  | _ :: at_, _ :: bt, m + 1, hlen, hm =>
      zipWith_getD_lt f at_ bt m (Nat.succ.inj hlen) (Nat.lt_of_succ_lt_succ hm)

private theorem pack768_bias_sub (b : ℕ) :
    ∀ (n : ℕ) (us ns : List ℕ), us.length = n → ns.length = n →
      (∀ i < n, ns.getD i 0 ≤ us.getD i 0 + b) →
      pack768 ns ≤ pack768 us + pack768 (List.replicate n b) ∧
      (pack768 us + pack768 (List.replicate n b)) - pack768 ns =
        pack768 (List.zipWith (fun u v ↦ u + b - v) us ns)
  | 0, [], [], _, _, _ => ⟨le_rfl, rfl⟩
  | 0, _ :: _, _, hu, _, _ => by cases hu
  | _ + 1, [], _, hu, _, _ => by cases hu
  | _ + 1, _ :: _, [], _, hv, _ => by cases hv
  | k + 1, u :: ut, v :: vt, hu, hv, hle => by
      rcases pack768_bias_sub b k ut vt (Nat.succ.inj hu) (Nat.succ.inj hv)
        (fun i hi ↦ hle (i + 1) (Nat.succ_lt_succ hi)) with ⟨ih_le, ih_eq⟩
      rw [List.replicate_succ, List.zipWith_cons_cons]
      simp only [sched_pack768_cons, sched_shiftLeft_768_eq, ← ih_eq,
        Nat.mul_sub_left_distrib, Nat.left_distrib]
      have h0 : v ≤ u + b := hle 0 (Nat.zero_lt_succ k)
      have hm := Nat.mul_le_mul_left sched_pow768 ih_le
      rw [Nat.left_distrib] at hm
      generalize sched_pow768 * pack768 ut = U, sched_pow768 * pack768 (List.replicate k b) = B,
        sched_pow768 * pack768 vt = V at hm ⊢
      exact ⟨by omega, by omega⟩

/-- Single-term unsigned `pos` lane `(c.pos * xp + c.neg * xn)`. -/
private def lanePos1 (c : PolyPN) (xp xn : ℕ) : ℕ := c.pos * xp + c.neg * xn

private theorem lanePos1_pack768 (c : PolyPN) :
    ∀ (xp xn : List ℕ), xp.length = xn.length →
      c.pos * pack768 xp + c.neg * pack768 xn = pack768 (List.zipWith (lanePos1 c) xp xn)
  | [], [], _ => by simp [sched_pack768_nil]
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: at_, b :: bt, h => by
      rw [List.zipWith_cons_cons]
      simp only [sched_pack768_cons, sched_shiftLeft_768_eq,
        ← lanePos1_pack768 c at_ bt (Nat.succ.inj h), lanePos1]
      ring

private def rootLane2Pos (c1 c2 : PolyPN) (xp1 xn1 xp2 xn2 : ℕ) : ℕ :=
  lanePos1 c1 xp1 xn1 + lanePos1 c2 xp2 xn2

private def rootList2 (c1 c2 : PolyPN) (xp1 xn1 xp2 xn2 : List ℕ) : List ℕ :=
  List.zipWith Nat.add (List.zipWith (lanePos1 c1) xp1 xn1) (List.zipWith (lanePos1 c2) xp2 xn2)

private theorem rootList2_spec (K : ℕ) (c1 c2 : PolyPN) (xp1 xn1 xp2 xn2 : List ℕ)
    (hc1 : c1.pos + c1.neg ≤ 2 ^ 48) (hc2 : c2.pos + c2.neg ≤ 2 ^ 48)
    (h1p : xp1.length = K) (h1n : xn1.length = K) (h2p : xp2.length = K) (h2n : xn2.length = K)
    (hb1p : ∀ v ∈ xp1, v < 2 ^ 353) (hb1n : ∀ v ∈ xn1, v < 2 ^ 353)
    (hb2p : ∀ v ∈ xp2, v < 2 ^ 353) (hb2n : ∀ v ∈ xn2, v < 2 ^ 353) :
    let rl := rootList2 c1 c2 xp1 xn1 xp2 xn2
    rl.length = K ∧
    (∀ m < K, rl.getD m 0 = rootLane2Pos c1 c2
        (xp1.getD m 0) (xn1.getD m 0) (xp2.getD m 0) (xn2.getD m 0) ∧
      rl.getD m 0 ≤ 2 ^ 402) ∧
    mulAdd2Pos c1 ⟨pack768 xp1, pack768 xn1⟩ c2 ⟨pack768 xp2, pack768 xn2⟩ = pack768 rl := by
  intro rl
  have hl1 : (List.zipWith (lanePos1 c1) xp1 xn1).length = K := by simp [h1p, h1n]
  have hl2 : (List.zipWith (lanePos1 c2) xp2 xn2).length = K := by simp [h2p, h2n]
  refine ⟨by simp [rl, rootList2, hl1, hl2], fun m hm ↦ ?_, ?_⟩
  · have hge : rl.getD m 0 = rootLane2Pos c1 c2
        (xp1.getD m 0) (xn1.getD m 0) (xp2.getD m 0) (xn2.getD m 0) := by
      dsimp only [rl, rootList2, rootLane2Pos]
      rw [zipWith_getD_lt _ _ _ m (hl1.trans hl2.symm) (hl1.symm ▸ hm),
        zipWith_getD_lt _ _ _ m (h1p.trans h1n.symm) (h1p.symm ▸ hm),
        zipWith_getD_lt _ _ _ m (h2p.trans h2n.symm) (h2p.symm ▸ hm), Nat.add_eq]
    have h1 {xs : List ℕ} (hl : xs.length = K) (hb : ∀ v ∈ xs, v < 2 ^ 353) :
        xs.getD m 0 ≤ 2 ^ 353 := by
      have hm' : m < xs.length := hl.symm ▸ hm
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm', Option.getD_some]
      exact (hb xs[m] (List.getElem_mem hm')).le
    have hle1 (cp cn x y : ℕ) (hc : cp + cn ≤ 2 ^ 48) (hx : x ≤ 2 ^ 353) (hy : y ≤ 2 ^ 353) :
        cp * x + cn * y ≤ 2 ^ 401 :=
      ((Nat.add_le_add (Nat.mul_le_mul_left cp hx) (Nat.mul_le_mul_left cn hy)).trans_eq
        (Nat.add_mul cp cn (2 ^ 353)).symm).trans
        ((Nat.mul_le_mul_right (2 ^ 353) hc).trans_eq rfl)
    refine ⟨hge, hge.le.trans ((Nat.add_le_add
      (hle1 _ _ _ _ hc1 (h1 h1p hb1p) (h1 h1n hb1n))
      (hle1 _ _ _ _ hc2 (h1 h2p hb2p) (h1 h2n hb2n))).trans_eq rfl)⟩
  · unfold mulAdd2Pos
    dsimp only [rl, rootList2]
    simp only [Nat.add_eq, Nat.mul_eq]
    rw [lanePos1_pack768 c1 xp1 xn1 (h1p.trans h1n.symm),
      lanePos1_pack768 c2 xp2 xn2 (h2p.trans h2n.symm),
      ← sched_pack768_zipAdd _ _ (hl1.trans hl2.symm)]

/-- Symbolic-`(d : ℕ)` 4-term `768`-bit root dot-product + `shr 256` unpacker. -/
def finishRootVec4Of (unpackShr256 : ℕ → ℕ → ℕ → List ℕ) (d n_lanes rep_bcomb : ℕ)
    (c1 x1 c2 x2 c3 x3 c4 x4 : PolyPN) : List ℕ := forceNatFast
    (mulAdd4Pos c1 x1 c2 x2 c3 x3 c4 x4) fun up ↦ forceNatFast
    (mulAdd4Neg c1 x1 c2 x2 c3 x3 c4 x4) fun un ↦ forceNatFast
    (Nat.sub (Nat.add up rep_bcomb) un) fun w ↦ unpackShr256 d n_lanes w

set_option maxHeartbeats 400000 in
-- root 4-term dot-product unpack verification
theorem finishRootVec4Of_spec
    (unpackShr256 : ℕ → ℕ → ℕ → List ℕ) (d L err rep1 : ℕ)
    (hunpack : ∀ (zs : List ℕ), zs.length = L + 1 → (∀ z ∈ zs, z < 2 ^ 768) →
      unpackShr256 d (L + 1) (pack768 zs) = zs.map (fun z ↦ Nat.shiftRight z 256))
    (hrep1 : rep1 = pack768 (List.replicate (L + 1) 1))
    (c1 c2 c3 c4 x1 x2 x3 x4 : PolyPN)
    (f1_hat f2_hat f3_hat f4_hat f1_ex f2_ex f3_ex f4_ex : ℕ → ℝ)
    (hc1 : c1.pos + c1.neg ≤ 2 ^ 48) (hc2 : c2.pos + c2.neg ≤ 2 ^ 48)
    (hc3 : c3.pos + c3.neg ≤ 2 ^ 48) (hc4 : c4.pos + c4.neg ≤ 2 ^ 48)
    (hx1 : PolyPNValid L x1 f1_hat) (hx2 : PolyPNValid L x2 f2_hat)
    (hx3 : PolyPNValid L x3 f3_hat) (hx4 : PolyPNValid L x4 f4_hat)
    (hf1 : ∀ m ≤ L, |f1_hat m - f1_ex m| ≤ (err : ℝ) / (2 ^ 352 : ℝ))
    (hf2 : ∀ m ≤ L, |f2_hat m - f2_ex m| ≤ (err : ℝ) / (2 ^ 352 : ℝ))
    (hf3 : ∀ m ≤ L, |f3_hat m - f3_ex m| ≤ (err : ℝ) / (2 ^ 352 : ℝ))
    (hf4 : ∀ m ≤ L, |f4_hat m - f4_ex m| ≤ (err : ℝ) / (2 ^ 352 : ℝ)) :
    let out := finishRootVec4Of unpackShr256 d (L + 1) (Nat.mul rep1 ta_B_COMB)
      c1 x1 c2 x2 c3 x3 c4 x4
    let c1_r : ℝ := ((c1.pos : ℝ) - (c1.neg : ℝ)) / (2 ^ 48 : ℝ)
    let c2_r : ℝ := ((c2.pos : ℝ) - (c2.neg : ℝ)) / (2 ^ 48 : ℝ)
    let c3_r : ℝ := ((c3.pos : ℝ) - (c3.neg : ℝ)) / (2 ^ 48 : ℝ)
    let c4_r : ℝ := ((c4.pos : ℝ) - (c4.neg : ℝ)) / (2 ^ 48 : ℝ)
    let r_l2 := Nat.add (Nat.shiftRight err 206) 2
    out.length = L + 1 ∧
    ∀ m < L + 1,
      let val := Nat.add (out.getD m 0) ta_BIAS_OUT
      |(val : ℤ) - (ta_B : ℤ)| ≤ (ta_B : ℤ) ∧
      |(ta_scale0 : ℝ) * (c1_r * f1_ex m + c2_r * f2_ex m + c3_r * f3_ex m + c4_r * f4_ex m) -
          ((val : ℝ) - (ta_B : ℝ))| ≤ (r_l2 : ℝ) := by
  intro out c1_r c2_r c3_r c4_r r_l2
  rcases hx1 with ⟨xp1, xn1, hp1_l, hn1_l, hp1_b, hn1_b, hp1_k, hn1_k, hf1_def⟩
  rcases hx2 with ⟨xp2, xn2, hp2_l, hn2_l, hp2_b, hn2_b, hp2_k, hn2_k, hf2_def⟩
  rcases hx3 with ⟨xp3, xn3, hp3_l, hn3_l, hp3_b, hn3_b, hp3_k, hn3_k, hf3_def⟩
  rcases hx4 with ⟨xp4, xn4, hp4_l, hn4_l, hp4_b, hn4_b, hp4_k, hn4_k, hf4_def⟩
  rcases rootList2_spec (L + 1) c1 c2 xp1 xn1 xp2 xn2 hc1 hc2 hp1_l hn1_l hp2_l hn2_l
    hp1_b hn1_b hp2_b hn2_b with ⟨hp12_l, hp12_g, hp12_k⟩
  rcases rootList2_spec (L + 1) c3 c4 xp3 xn3 xp4 xn4 hc3 hc4 hp3_l hn3_l hp4_l hn4_l
    hp3_b hn3_b hp4_b hn4_b with ⟨hp34_l, hp34_g, hp34_k⟩
  rcases rootList2_spec (L + 1) c1 c2 xn1 xp1 xn2 xp2 hc1 hc2 hn1_l hp1_l hn2_l hp2_l
    hn1_b hp1_b hn2_b hp2_b with ⟨hn12_l, hn12_g, hn12_k⟩
  rcases rootList2_spec (L + 1) c3 c4 xn3 xp3 xn4 xp4 hc3 hc4 hn3_l hp3_l hn4_l hp4_l
    hn3_b hp3_b hn4_b hp4_b with ⟨hn34_l, hn34_g, hn34_k⟩
  let up_list := List.zipWith Nat.add (rootList2 c1 c2 xp1 xn1 xp2 xn2) (rootList2 c3 c4 xp3 xn3 xp4
    xn4)
  let un_list := List.zipWith Nat.add (rootList2 c1 c2 xn1 xp1 xn2 xp2) (rootList2 c3 c4 xn3 xp3 xn4
    xp4)
  have hup_len : up_list.length = L + 1 := by simp [up_list, hp12_l, hp34_l]
  have hun_len : un_list.length = L + 1 := by simp [un_list, hn12_l, hn34_l]
  let z_list := List.zipWith (fun u v ↦ u + ta_B_COMB - v) up_list un_list
  have hz_len : z_list.length = L + 1 := by simp [z_list, hup_len, hun_len]
  have hlane (m : ℕ) (hm : m < L + 1) :
      let val := Nat.add (Nat.shiftRight (z_list.getD m 0) 256) ta_BIAS_OUT
      un_list.getD m 0 ≤ up_list.getD m 0 + ta_B_COMB ∧ z_list.getD m 0 < 2 ^ 768 ∧
      (|(val : ℤ) - (ta_B : ℤ)| ≤ (ta_B : ℤ) ∧
       |(ta_scale0 : ℝ) * (c1_r * f1_ex m + c2_r * f2_ex m + c3_r * f3_ex m + c4_r * f4_ex m) -
          ((val : ℝ) - (ta_B : ℝ))| ≤ (r_l2 : ℝ)) := by
    intro val
    let up := up_list.getD m 0
    let un := un_list.getD m 0
    let z := z_list.getD m 0
    have hshr_eq (x n : ℕ) : Nat.shiftRight x n = x / 2 ^ n := Nat.shiftRight_eq_div_pow x n
    have hup_eq : up = rootLane2Pos c1 c2 (xp1.getD m 0) (xn1.getD m 0) (xp2.getD m 0) (xn2.getD m
        0) +
        rootLane2Pos c3 c4 (xp3.getD m 0) (xn3.getD m 0) (xp4.getD m 0) (xn4.getD m 0) := by
      dsimp only [up, up_list]
      rw [zipWith_getD_lt _ _ _ m (hp12_l.trans hp34_l.symm) (hp12_l.symm ▸ hm),
        (hp12_g m hm).1, (hp34_g m hm).1, Nat.add_eq]
    have hun_eq : un = rootLane2Pos c1 c2 (xn1.getD m 0) (xp1.getD m 0) (xn2.getD m 0) (xp2.getD m
        0) +
        rootLane2Pos c3 c4 (xn3.getD m 0) (xp3.getD m 0) (xn4.getD m 0) (xp4.getD m 0) := by
      dsimp only [un, un_list]
      rw [zipWith_getD_lt _ _ _ m (hn12_l.trans hn34_l.symm) (hn12_l.symm ▸ hm),
        (hn12_g m hm).1, (hn34_g m hm).1, Nat.add_eq]
    have hz_eq : z = up + ta_B_COMB - un :=
      zipWith_getD_lt _ _ _ m (hup_len.trans hun_len.symm) (hup_len.symm ▸ hm)
    have hup_le : up ≤ 2 ^ 403 := by
      rw [hup_eq, ← (hp12_g m hm).1, ← (hp34_g m hm).1]
      exact (Nat.add_le_add (hp12_g m hm).2 (hp34_g m hm).2).trans_eq rfl
    have hun_le : un ≤ 2 ^ 403 := by
      rw [hun_eq, ← (hn12_g m hm).1, ← (hn34_g m hm).1]
      exact (Nat.add_le_add (hn12_g m hm).2 (hn34_g m hm).2).trans_eq rfl
    have hun_sum : un ≤ up + ta_B_COMB :=
      (hun_le.trans (Nat.ble_eq.mp rfl : 2 ^ 403 ≤ ta_B_COMB)).trans (Nat.le_add_left ta_B_COMB up)
    have hz_lt411 : z < 2 ^ 411 := by
      rw [hz_eq]
      exact Nat.lt_of_le_of_lt ((Nat.sub_le (up + ta_B_COMB) un).trans
        (Nat.add_le_add_right hup_le ta_B_COMB)) (Nat.lt_iff_add_one_le.mpr (Nat.ble_eq.mp rfl))
    have hshr_lt : Nat.shiftRight z 256 < 2 ^ 155 := by
      rw [hshr_eq]
      refine Nat.div_lt_of_lt_mul ?_
      rw [show 2 ^ 256 * 2 ^ 155 = 2 ^ 411 from rfl]
      exact hz_lt411
    have hval_le_2B : val ≤ 2 * ta_B :=
      (Nat.add_le_add_right hshr_lt.le ta_BIAS_OUT).trans (Nat.ble_eq.mp rfl)
    refine ⟨hun_sum, Nat.lt_trans hz_lt411 (Nat.lt_iff_add_one_le.mpr (Nat.ble_eq.mp rfl)), ?_, ?_⟩
    · have hv0 : (0 : ℤ) ≤ (val : ℤ) := Nat.cast_nonneg (α := ℤ) val
      have hv2 : (val : ℤ) ≤ 2 * (ta_B : ℤ) := by exact_mod_cast hval_le_2B
      generalize (ta_B : ℤ) = bz at hv2 ⊢
      exact abs_le.mpr ⟨by omega, by omega⟩
    · let fh (xp xn : List ℕ) : ℝ := ((xp.getD m 0 : ℝ) - (xn.getD m 0 : ℝ)) / (2 ^ 352 : ℝ)
      let hat_term : ℝ :=
        (ta_scale0 : ℝ) * (c1_r * fh xp1 xn1 + c2_r * fh xp2 xn2 + c3_r * fh xp3 xn3 + c4_r * fh xp4
          xn4)
      let exact_term : ℝ :=
        (ta_scale0 : ℝ) * (c1_r * f1_ex m + c2_r * f2_ex m + c3_r * f3_ex m + c4_r * f4_ex m)
      have hscale_r : (ta_scale0 : ℝ) = (2 : ℝ) ^ 144 := by
        simp only [show ta_scale0 = 2 ^ 144 from rfl, Nat.cast_pow, Nat.cast_ofNat]
      have hhat_mul : hat_term * (2 : ℝ) ^ 256 = (up : ℝ) - (un : ℝ) := by
        rw [hup_eq, hun_eq]
        dsimp only [hat_term, c1_r, c2_r, c3_r, c4_r, fh, rootLane2Pos, lanePos1]
        rw [hscale_r, show (2 : ℝ) ^ 144 = (2 : ℝ) ^ 48 * (2 : ℝ) ^ 96 by rw [← pow_add],
          show (2 : ℝ) ^ 352 = (2 : ℝ) ^ 96 * (2 : ℝ) ^ 256 by rw [← pow_add]]
        have h48 : (2 : ℝ) ^ 48 ≠ 0 := by positivity
        have h96 : (2 : ℝ) ^ 96 ≠ 0 := by positivity
        have h256 : (2 : ℝ) ^ 256 ≠ 0 := by positivity
        generalize (2 : ℝ) ^ 48 = A, (2 : ℝ) ^ 96 = B, (2 : ℝ) ^ 256 = C at h48 h96 h256 ⊢
        push_cast
        field_simp
        ring
      let q := Nat.shiftRight z 256
      let rem := z % 2 ^ 256
      have hz_nat : z + un = up + 2 ^ 410 := by
        rw [hz_eq, show (2 : ℕ) ^ 410 = ta_B_COMB from rfl]
        exact Nat.sub_add_cancel hun_sum
      have hq_nat : 2 ^ 256 * q + rem = z := by
        dsimp only [q, rem]
        rw [hshr_eq]
        exact Nat.div_add_mod z (2 ^ 256)
      have hval_nat : val + 2 ^ 154 = q + ta_B := by
        change q + ta_BIAS_OUT + 2 ^ 154 = q + ta_B
        rw [Nat.add_assoc, show ta_BIAS_OUT + 2 ^ 154 = ta_B from rfl]
      have hz_r : (z : ℝ) + (un : ℝ) = (up : ℝ) + (2 : ℝ) ^ 410 := by
        simpa only [Nat.cast_add, Nat.cast_pow,
          Nat.cast_ofNat] using congrArg (Nat.cast (R := ℝ)) hz_nat
      have hq_r : (2 : ℝ) ^ 256 * (q : ℝ) + (rem : ℝ) = (z : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
          Nat.cast_ofNat] using congrArg (Nat.cast (R := ℝ)) hq_nat
      have hval_r : (val : ℝ) + (2 : ℝ) ^ 154 = (q : ℝ) + (ta_B : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_pow,
          Nat.cast_ofNat] using congrArg (Nat.cast (R := ℝ)) hval_nat
      have hval_mul : ((val : ℝ) - (ta_B : ℝ)) * (2 : ℝ) ^ 256 = (up : ℝ) - (un : ℝ) - (rem : ℝ) :=
        by
        have hq_sub : (val : ℝ) - (ta_B : ℝ) = (q : ℝ) - (2 : ℝ) ^ 154 := by linarith only [hval_r]
        rw [hq_sub, sub_mul, show (2 : ℝ) ^ 154 * (2 : ℝ) ^ 256 = (2 : ℝ) ^ 410 by rw [← pow_add]]
        linarith only [hz_r, hq_r]
      have hdiff_hat : |hat_term - ((val : ℝ) - (ta_B : ℝ))| ≤ 1 := by
        have hp256 : (0 : ℝ) < (2 : ℝ) ^ 256 := by positivity
        have heq_div : hat_term - ((val : ℝ) - (ta_B : ℝ)) = (rem : ℝ) / (2 : ℝ) ^ 256 := by
          rw [eq_div_iff (ne_of_gt hp256), sub_mul, hhat_mul, hval_mul]
          ring
        have hc : (rem : ℝ) ≤ ((2 ^ 256 : ℕ) : ℝ) := by
          exact_mod_cast (Nat.mod_lt z (Nat.two_pow_pos 256)).le
        rw [heq_div, abs_div, abs_of_nonneg (Nat.cast_nonneg rem), abs_of_pos hp256,
          div_le_one hp256]
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using hc
      have hdiff_ex : |exact_term - hat_term| ≤ (err : ℝ) / (2 : ℝ) ^ 206 := by
        rw [show exact_term - hat_term = (2 : ℝ) ^ 144 * (c1_r * (f1_ex m - fh xp1 xn1) +
              c2_r * (f2_ex m - fh xp2 xn2) + c3_r * (f3_ex m - fh xp3 xn3) +
              c4_r * (f4_ex m - fh xp4 xn4)) by
            dsimp only [exact_term, hat_term]
            rw [hscale_r]
            ring,
          abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ 144)]
        have hm_le : m ≤ L := Nat.le_of_lt_succ hm
        have hm_i (c : PolyPN) (hc : c.pos + c.neg ≤ 2 ^ 48) (xp xn : List ℕ) (f_hat f_ex : ℕ → ℝ)
            (hf_def : ∀ k, f_hat k = if k ≤ L then ((xp.getD k 0 : ℝ) - (xn.getD k 0 : ℝ)) / (2 ^
              352 : ℝ) else 0)
            (hf : ∀ k ≤ L, |f_hat k - f_ex k| ≤ (err : ℝ) / (2 ^ 352 : ℝ)) :
            |(((c.pos : ℝ) - (c.neg : ℝ)) / (2 ^ 48 : ℝ)) * (f_ex m - fh xp xn)| ≤
              (err : ℝ) / (2 : ℝ) ^ 352 := by
          have hpos : (0 : ℝ) < (2 : ℝ) ^ 48 := by positivity
          have hc_r : (c.pos : ℝ) + (c.neg : ℝ) ≤ (2 : ℝ) ^ 48 := by
            simpa only [Nat.cast_add, Nat.cast_pow,
              Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr hc
          have hc_le1 : |((c.pos : ℝ) - (c.neg : ℝ)) / (2 ^ 48 : ℝ)| ≤ 1 := by
            rw [abs_div, abs_of_pos hpos, div_le_one hpos]
            exact abs_le.mpr
              ⟨by linarith [Nat.cast_nonneg (α := ℝ) c.pos],
                by linarith [Nat.cast_nonneg (α := ℝ) c.neg]⟩
          have h := hf m hm_le
          rw [hf_def m, ta_ite_pos hm_le] at h
          rw [abs_mul, abs_sub_comm (f_ex m), ← one_mul ((err : ℝ) / (2 : ℝ) ^ 352)]
          exact mul_le_mul hc_le1 h (abs_nonneg _) (by positivity)
        let t1 := c1_r * (f1_ex m - fh xp1 xn1)
        let t2 := c2_r * (f2_ex m - fh xp2 xn2)
        let t3 := c3_r * (f3_ex m - fh xp3 xn3)
        let t4 := c4_r * (f4_ex m - fh xp4 xn4)
        have h1 : |t1| ≤ (err : ℝ) / (2 : ℝ) ^ 352 := hm_i c1 hc1 xp1 xn1 f1_hat f1_ex hf1_def hf1
        have h2 : |t2| ≤ (err : ℝ) / (2 : ℝ) ^ 352 := hm_i c2 hc2 xp2 xn2 f2_hat f2_ex hf2_def hf2
        have h3 : |t3| ≤ (err : ℝ) / (2 : ℝ) ^ 352 := hm_i c3 hc3 xp3 xn3 f3_hat f3_ex hf3_def hf3
        have h4 : |t4| ≤ (err : ℝ) / (2 : ℝ) ^ 352 := hm_i c4 hc4 xp4 xn4 f4_hat f4_ex hf4_def hf4
        have hsum4 : |t1 + t2 + t3 + t4| ≤ 4 * ((err : ℝ) / (2 : ℝ) ^ 352) := by
          linarith only [abs_add_le (t1 + t2 + t3) t4, abs_add_le (t1 + t2) t3, abs_add_le t1 t2,
            h1, h2, h3, h4]
        have hcancel : (2 : ℝ) ^ 144 * (4 * ((err : ℝ) / (2 : ℝ) ^ 352)) =
            (err : ℝ) / (2 : ℝ) ^ 206 := by
          rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
            ← show (2 : ℝ) ^ 144 * (2 : ℝ) ^ 2 * (2 : ℝ) ^ 206 = (2 : ℝ) ^ 352 by rw [← pow_add,
              ← pow_add]]
          field_simp [show ((2 : ℝ) ^ 206) ≠ 0 by positivity]
        exact (mul_le_mul_of_nonneg_left hsum4 (by positivity)).trans hcancel.le
      have herr_div : (err : ℝ) / (2 : ℝ) ^ 206 ≤ ((Nat.shiftRight err 206 : ℕ) : ℝ) + 1 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ 206)]
        have hdm : 2 ^ 206 * (err / 2 ^ 206) + err % 2 ^ 206 = err := Nat.div_add_mod err (2 ^ 206)
        have hle_nat : err ≤ (Nat.shiftRight err 206 + 1) * 2 ^ 206 := by
          have h1 : 2 ^ 206 * (err / 2 ^ 206) + err % 2 ^ 206 ≤ 2 ^ 206 * (err / 2 ^ 206) + 2 ^ 206
            :=
            Nat.add_le_add_left (Nat.mod_lt err (Nat.two_pow_pos 206)).le _
          rw [hdm] at h1
          rw [hshr_eq, Nat.add_mul, Nat.one_mul, Nat.mul_comm (err / 2 ^ 206)]
          exact h1
        have hle_r : (err : ℝ) ≤ (((Nat.shiftRight err 206 + 1) * 2 ^ 206 : ℕ) : ℝ) := by
          exact_mod_cast hle_nat
        simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow,
          Nat.cast_ofNat] using hle_r
      dsimp only [r_l2]
      simp only [Nat.add_eq, Nat.cast_add, Nat.cast_ofNat]
      linarith [abs_sub_le exact_term hat_term ((val : ℝ) - (ta_B : ℝ)), hdiff_ex, hdiff_hat,
        herr_div]
  have hw_eq : (mulAdd4Pos c1 x1 c2 x2 c3 x3 c4 x4 + Nat.mul rep1 ta_B_COMB) -
      mulAdd4Neg c1 x1 c2 x2 c3 x3 c4 x4 = pack768 z_list := by
    rw [← hp1_k, ← hn1_k, ← hp2_k, ← hn2_k] at hp12_k hn12_k
    rw [← hp3_k, ← hn3_k, ← hp4_k, ← hn4_k] at hp34_k hn34_k
    have hmul4_pos : mulAdd4Pos c1 x1 c2 x2 c3 x3 c4 x4 = pack768 up_list := by
      unfold mulAdd4Pos
      rw [Nat.add_eq, show mulAdd2Pos c1 x1 c2 x2 = pack768 _ from hp12_k,
        show mulAdd2Pos c3 x3 c4 x4 = pack768 _ from hp34_k,
        ← sched_pack768_zipAdd _ _ (hp12_l.trans hp34_l.symm)]
    have hmul4_neg : mulAdd4Neg c1 x1 c2 x2 c3 x3 c4 x4 = pack768 un_list := by
      unfold mulAdd4Neg
      rw [Nat.add_eq, show mulAdd2Neg c1 x1 c2 x2 = pack768 _ from hn12_k,
        show mulAdd2Neg c3 x3 c4 x4 = pack768 _ from hn34_k,
        ← sched_pack768_zipAdd _ _ (hn12_l.trans hn34_l.symm)]
    rw [hmul4_pos, hmul4_neg, hrep1, sched_pack768_rep_mul]
    exact (pack768_bias_sub ta_B_COMB (L + 1) up_list un_list hup_len hun_len fun i hi ↦ (hlane i
      hi).1).2
  have hout_eq : out = z_list.map (fun z ↦ Nat.shiftRight z 256) := by
    dsimp only [out, finishRootVec4Of]
    simp only [forceNatFast_eq]
    rw [Nat.add_eq, Nat.sub_eq, hw_eq]
    refine hunpack z_list hz_len fun z hz ↦ ?_
    rcases List.mem_iff_getElem.mp hz with ⟨i, hi, rfl⟩
    have hi' : i < L + 1 := hz_len ▸ hi
    rw [show z_list[i] = z_list.getD i 0 by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]]
    exact (hlane i hi').2.1
  refine ⟨by rw [hout_eq, List.length_map, hz_len], fun m hm ↦ ?_⟩
  dsimp only
  rw [hout_eq, map_getD_lt _ z_list m (hz_len.symm ▸ hm)]
  exact (hlane m hm).2.2

/-- Convert a sign-magnitude pair `(s, m)` into an unsigned `PolyPN`. -/
def smToPolyPN (s : Bool) (m : ℕ) : PolyPN := if s then ⟨0, m⟩ else ⟨m, 0⟩

/-- Swap `(pos, neg)` to negate a `PolyPN` identically. -/
def negPolyPN (p : PolyPN) : PolyPN := ⟨p.neg, p.pos⟩

theorem smToPolyPN_add_eq (s : Bool) (m : ℕ) :
    (smToPolyPN s m).pos + (smToPolyPN s m).neg = m := by
  cases s <;> simp [smToPolyPN]

theorem smToPolyPN_sub_eq (s : Bool) (m : ℕ) :
    ((smToPolyPN s m).pos : ℝ) - ((smToPolyPN s m).neg : ℝ) = (smToInt s m : ℝ) := by
  cases s <;> simp [smToPolyPN, smToInt]

theorem negPolyPN_add_eq (p : PolyPN) : (negPolyPN p).pos + (negPolyPN p).neg = p.pos + p.neg
    := Nat.add_comm p.neg p.pos

theorem negPolyPN_sub_eq (p : PolyPN) :
    ((negPolyPN p).pos : ℝ) - ((negPolyPN p).neg : ℝ) = -((p.pos : ℝ) - (p.neg : ℝ)) := by
  dsimp only [negPolyPN]
  ring

theorem gateSu2_magnitudes_le_of_contraction (g0 : DyadicSu2Gate)
    (h_sum : (g0.mar * g0.mar + g0.mai * g0.mai) + (g0.mbr * g0.mbr + g0.mbi * g0.mbi) ≤ 2 ^ 96) :
    g0.mar ≤ 2 ^ 48 ∧ g0.mai ≤ 2 ^ 48 ∧ g0.mbr ≤ 2 ^ 48 ∧ g0.mbi ≤ 2 ^ 48 := by
  have hsq (m : ℕ) (hm : m * m ≤ 2 ^ 96) : m ≤ 2 ^ 48 :=
    Nat.le_of_not_lt fun h ↦ absurd (hm.trans_lt (Nat.lt_of_lt_of_le
      (Nat.lt_iff_add_one_le.mpr (Nat.ble_eq.mp rfl) : 2 ^ 96 < (2 ^ 48 + 1) * (2 ^ 48 + 1))
      (Nat.mul_le_mul h h))) (lt_irrefl _)
  exact ⟨hsq _ (by omega), hsq _ (by omega), hsq _ (by omega), hsq _ (by omega)⟩

theorem rootLoopP_re_im_eq (M : ℕ) (a0 b0 : ℂ) (P_gs Q_gs : PolyC) (m : ℕ) (hm : m ≤ M) :
    (rootLoopP M a0 b0 P_gs Q_gs m).re = a0.re * P_gs.re m + (-a0.im) * P_gs.im m + (-b0.re) *
    Q_gs.re (M - m) + (-b0.im) * Q_gs.im (M - m) ∧ (rootLoopP M a0 b0 P_gs Q_gs m).im = a0.re
    * P_gs.im m + a0.im * P_gs.re m + (-b0.im) * Q_gs.re (M - m) + b0.re * Q_gs.im (M - m) := by
  unfold rootLoopP PolyC.toC
  rw [ta_ite_pos hm]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, star_add,
    star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I, Complex.neg_re, Complex.neg_im]
  exact ⟨by ring, by ring⟩

theorem rootLoopQ_re_im_eq (M : ℕ) (a0 b0 : ℂ) (P_gs Q_gs : PolyC) (m : ℕ) (hm : m ≤ M) :
    (rootLoopQ M a0 b0 P_gs Q_gs m).re = a0.re * Q_gs.re m + (-a0.im) * Q_gs.im m + b0.re *
    P_gs.re (M - m) + b0.im * P_gs.im (M - m) ∧ (rootLoopQ M a0 b0 P_gs Q_gs m).im = a0.re *
    Q_gs.im m + a0.im * Q_gs.re m + b0.im * P_gs.re (M - m) + (-b0.re) * P_gs.im (M - m) := by
  unfold rootLoopQ PolyC.toC
  rw [ta_ite_pos hm]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, star_add, star_mul, Complex.star_def,
    Complex.conj_ofReal, Complex.conj_I, Complex.neg_re, Complex.neg_im]
  exact ⟨by ring, by ring⟩

theorem list_reverse_getD_lt (xs : List ℕ) (L m : ℕ) (hlen : xs.length = L + 1) (hm : m < L + 1) :
    xs.reverse.getD m 0 = xs.getD (L - m) 0 := by
  have hm_rev : m < xs.reverse.length := by rw [List.length_reverse, hlen]; exact hm
  have hsub_lt : L - m < xs.length := by rw [hlen]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm_rev, Option.getD_some,
    List.getElem_reverse]
  have hidx : xs.length - 1 - m = L - m := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hsub_lt, Option.getD_some, hidx]

theorem flipBiased_spec (val R : ℕ) (Y : ℝ)
    (hmag : |(val : ℤ) - (ta_B : ℤ)| ≤ (ta_B : ℤ))
    (herr : |(ta_scale0 : ℝ) * Y - ((val : ℝ) - (ta_B : ℝ))| ≤ (R : ℝ)) :
    let fval := Nat.sub ta_B2 val
    |(fval : ℤ) - (ta_B : ℤ)| ≤ (ta_B : ℤ) ∧
    |(ta_scale0 : ℝ) * (-Y) - ((fval : ℝ) - (ta_B : ℝ))| ≤ (R : ℝ) := by
  intro fval
  have hval_le : val ≤ ta_B2 := by
    have h2 : (val : ℤ) - (ta_B : ℤ) ≤ (ta_B : ℤ) := (abs_le.mp hmag).2
    have hle_z : (val : ℤ) ≤ 2 * (ta_B : ℤ) := by omega
    rw [ta_B2_eq]
    exact_mod_cast hle_z
  have hf_int : (fval : ℤ) - (ta_B : ℤ) = -((val : ℤ) - (ta_B : ℤ)) := by
    dsimp only [fval]
    rw [Nat.sub_eq, Int.ofNat_sub hval_le, ta_B2_eq]
    push_cast
    ring
  have hf_real : (ta_scale0 : ℝ) * (-Y) - ((fval : ℝ) - (ta_B : ℝ)) =
      -((ta_scale0 : ℝ) * Y - ((val : ℝ) - (ta_B : ℝ))) := by
    dsimp only [fval]
    rw [Nat.sub_eq, Nat.cast_sub hval_le, ta_B2_eq]
    push_cast
    ring
  exact ⟨by rw [hf_int, abs_neg]; exact hmag, by rw [hf_real, abs_neg]; exact herr⟩

/-- Generic `O(M)` interleaver emitting `[⟨ep_0, eq_0⟩, ⟨op_0, oq_0⟩, ...]` via `mkPQConsLazy`. -/
def interleaveFourPQ : List ℕ → List ℕ → List ℕ → List ℕ → List PQPair
  | ep :: ept, eq :: eqt, op :: opt, oq :: oqt =>
      mkPQConsLazy ep eq (mkPQConsLazy op oq (interleaveFourPQ ept eqt opt oqt))
  | _, _, _, _ => []

theorem interleaveFourPQ_length :
    ∀ (n : ℕ) (ep eq op oq : List ℕ),
      ep.length = n → eq.length = n → op.length = n → oq.length = n →
      (interleaveFourPQ ep eq op oq).length = 2 * n
  | 0, [], _, _, _, _, _, _, _ => rfl
  | 0, _ :: _, _, _, _, h1, _, _, _ => by cases h1
  | _ + 1, [], _, _, _, h1, _, _, _ => by cases h1
  | _ + 1, _ :: _, [], _, _, _, h2, _, _ => by cases h2
  | _ + 1, _ :: _, _ :: _, [], _, _, _, h3, _ => by cases h3
  | _ + 1, _ :: _, _ :: _, _ :: _, [], _, _, _, h4 => by cases h4
  | n + 1, _ :: ept, _ :: eqt, _ :: opt, _ :: oqt, h1, h2, h3, h4 => by
      simp only [interleaveFourPQ, mkPQConsLazy_eq, List.length_cons]
      rw [interleaveFourPQ_length n ept eqt opt oqt
        (Nat.succ.inj h1) (Nat.succ.inj h2) (Nat.succ.inj h3) (Nat.succ.inj h4)]
      omega

theorem interleaveFourPQ_getD :
    ∀ (n : ℕ) (ep eq op oq : List ℕ) (m : ℕ),
      ep.length = n → eq.length = n → op.length = n → oq.length = n → m < n →
      (interleaveFourPQ ep eq op oq).getD (2 * m) ⟨ta_B, ta_B⟩ = ⟨ep.getD m 0, eq.getD m 0⟩ ∧
      (interleaveFourPQ ep eq op oq).getD (2 * m + 1) ⟨ta_B, ta_B⟩ = ⟨op.getD m 0, oq.getD m 0⟩
  | 0, _, _, _, _, _, _, _, _, _, hm => by cases hm
  | _ + 1, [], _, _, _, _, h1, _, _, _, _ => by cases h1
  | _ + 1, _ :: _, [], _, _, _, _, h2, _, _, _ => by cases h2
  | _ + 1, _ :: _, _ :: _, [], _, _, _, _, h3, _, _ => by cases h3
  | _ + 1, _ :: _, _ :: _, _ :: _, [], _, _, _, _, h4, _ => by cases h4
  | _ + 1, _ :: _, _ :: _, _ :: _, _ :: _, 0, _, _, _, _, _ => by
      simp [interleaveFourPQ, mkPQConsLazy_eq, List.getD_eq_getElem?_getD]
  | n + 1, _ :: ept, _ :: eqt, _ :: opt, _ :: oqt, m + 1, h1, h2, h3, h4, _ => by
      rw [show 2 * (m + 1) = (2 * m) + 1 + 1 by omega]
      simp only [interleaveFourPQ, mkPQConsLazy_eq, List.getD_eq_getElem?_getD,
        List.getElem?_cons_succ]
      simpa only [List.getD_eq_getElem?_getD] using
        interleaveFourPQ_getD n ept eqt opt oqt m
          (Nat.succ.inj h1) (Nat.succ.inj h2) (Nat.succ.inj h3) (Nat.succ.inj h4) (by omega)

def revPolyPNOf (revFn : ℕ → ℕ → ℕ → ℕ) (d n_lanes : ℕ) (p : PolyPN) : PolyPN :=
  ⟨revFn d n_lanes p.pos, revFn d n_lanes p.neg⟩

theorem revPolyPNOf_valid (revFn : ℕ → ℕ → ℕ → ℕ) (d L : ℕ) (hrev : ∀ (xs : List ℕ), xs.length
    = L + 1 → (∀ x ∈ xs, x < 2 ^ 768) → revFn d (L + 1) (pack768 xs) = pack768 xs.reverse)
    (p : PolyPN) (f_hat : ℕ → ℝ) (hp : PolyPNValid L p f_hat) : PolyPNValid L
    (revPolyPNOf revFn d (L + 1) p) (fun m ↦ if m ≤ L then f_hat (L - m) else 0) := by
  rcases hp with ⟨vp, vn, hpl, hnl, hpb, hnb, hpk, hnk, hf⟩
  have hlt768 : 2 ^ 353 < 2 ^ 768 := Nat.lt_iff_add_one_le.mpr (Nat.ble_eq.mp rfl)
  refine ⟨vp.reverse, vn.reverse, by simp [hpl], by simp [hnl],
    fun v hv ↦ hpb v (List.mem_reverse.mp hv), fun v hv ↦ hnb v (List.mem_reverse.mp hv),
    by dsimp only [revPolyPNOf]; rw [hpk]; exact hrev vp hpl (fun x hx ↦ (hpb x hx).trans hlt768),
    by dsimp only [revPolyPNOf]; rw [hnk]; exact hrev vn hnl (fun x hx ↦ (hnb x hx).trans hlt768),
    fun m ↦ ?_⟩
  dsimp only
  by_cases hm : m ≤ L
  · rw [ta_ite_pos hm, ta_ite_pos hm, hf (L - m), ta_ite_pos (by omega),
      list_reverse_getD_lt vp L m hpl (by omega), list_reverse_getD_lt vn L m hnl (by omega)]
  · rw [ta_ite_neg hm, ta_ite_neg hm]

theorem gateSu2Pair_re_im (g0 : DyadicSu2Gate) : (gateSu2Pair 48 g0).1.re = gateSu2ARe 48 g0 ∧
    (gateSu2Pair 48 g0).1.im = gateSu2AIm 48 g0 ∧ (gateSu2Pair 48 g0).2.re = gateSu2BRe 48 g0
    ∧ (gateSu2Pair 48 g0).2.im = gateSu2BIm 48 g0 := by
  dsimp only [gateSu2Pair]
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]

open SpecsAux.Slim.BiGqspChunkedMillerLinearRecPQ2a
open SpecsAux.SpecMirror.BiGqspTrueAnglesFinalSumS4805

/-- Non-recursor `DefinitionVal` trampoline breaking C++ `whnf_core` recursion in `@List.rec`. -/
def ta_tramp {α : Type} (x : α) : α := x

/-- Zero-cost GMP cache-salting wrapper preventing `n mod 2 ^ 64 == 0` `m_whnf_cache` collisions. -/
def ta_idSalt (_s x : ℕ) : ℕ := x

/-- Strict `ℕ` evaluation barrier (`1` on the left so symbolic proofs block while GMP forces
    literals). -/
def ta_tfNat (f : ℕ → ℕ) (x : ℕ) : ℕ := @Nat.casesOn (fun _ ↦ ℕ) (Nat.add 1 x) 0 f

theorem ta_tfNat_eq (f : ℕ → ℕ) (x : ℕ) : ta_tfNat f x = f x := by
  change @Nat.casesOn (fun _ ↦ ℕ) (1 + x) 0 f = f x
  rw [Nat.one_add]

/-- Fallback `ℕ → ℕ` branch for `ta_tfNatFn`. -/
def ta_constZeroNat (_ : ℕ) : ℕ := 0

/-- Arity-2 strict `ℕ` evaluation barrier. -/
def ta_tfNatFn (f : ℕ → ℕ → ℕ) (x : ℕ) : ℕ → ℕ :=
  @Nat.casesOn (fun _ ↦ ℕ → ℕ) (Nat.add 1 x) ta_constZeroNat f

theorem ta_tfNatFn_eq (f : ℕ → ℕ → ℕ) (x : ℕ) : ta_tfNatFn f x = f x := by
  change @Nat.casesOn (fun _ ↦ ℕ → ℕ) (1 + x) ta_constZeroNat f = f x
  rw [Nat.one_add]

/-- Salted strict `ℕ → List ℕ` evaluation barrier. -/
def ta_stfList (s : ℕ) (f : ℕ → List ℕ) (x : ℕ) : List ℕ :=
  @Nat.casesOn (fun _ ↦ List ℕ) (Nat.add 1 (ta_idSalt s x)) [] f

theorem ta_stfList_eq (s : ℕ) (f : ℕ → List ℕ) (x : ℕ) : ta_stfList s f x = f x := by
  change @Nat.casesOn (fun _ ↦ List ℕ) (1 + x) [] f = f x
  rw [Nat.one_add]

/-- Fallback `ℕ → List ℕ` branch for `ta_tfListFn`. -/
def ta_constNilNat (_ : ℕ) : List ℕ := []

/-- Arity-2 strict `ℕ → ℕ → List ℕ` evaluation barrier. -/
def ta_tfListFn (f : ℕ → ℕ → List ℕ) (x : ℕ) : ℕ → List ℕ :=
  @Nat.casesOn (fun _ ↦ ℕ → List ℕ) (Nat.add 1 x) ta_constNilNat f

/-- Strict `ℕ → List ℕ` evaluation barrier forcing `35 Mbit` root packed words once
before unpack. -/
def ta_tfList (f : ℕ → List ℕ) (x : ℕ) : List ℕ :=
  @Nat.casesOn (fun _ ↦ List ℕ) (Nat.add 1 x) [] f

theorem ta_tfList_eq (f : ℕ → List ℕ) (x : ℕ) : ta_tfList f x = f x := by
  change @Nat.casesOn (fun _ ↦ List ℕ) (1 + x) [] f = f x
  rw [Nat.one_add]

/-- Fallback `List PQPair` branches for strict `PQPair` interleaving. -/
def ta_constPQ1 (_ : ℕ) : List PQPair := []
/-- Arity-2 fallback `List PQPair` branch. -/
def ta_constPQ2 (_ _ : ℕ) : List PQPair := []
/-- Arity-3 fallback `List PQPair` branch. -/
def ta_constPQ3 (_ _ _ : ℕ) : List PQPair := []
/-- Arity-4 fallback `List PQPair` branch. -/
def ta_constPQ4 (_ _ _ _ : ℕ) : List PQPair := []

/-- Salted strict `List PQPair` barrier (stage 0). -/
def ta_stfPQ0 (s : ℕ) (f : ℕ → List PQPair) (x : ℕ) : List PQPair :=
  @Nat.casesOn (fun _ ↦ List PQPair) (Nat.add 1 (ta_idSalt s x)) [] f

theorem ta_stfPQ0_eq (s : ℕ) (f : ℕ → List PQPair) (x : ℕ) : ta_stfPQ0 s f x = f x := by
  change @Nat.casesOn (fun _ ↦ List PQPair) (1 + x) [] f = f x; rw [Nat.one_add]

/-- Salted strict `List PQPair` barrier (stage 1). -/
def ta_stfPQ1 (s : ℕ) (f : ℕ → ℕ → List PQPair) (x : ℕ) : ℕ → List PQPair :=
  @Nat.casesOn (fun _ ↦ ℕ → List PQPair) (Nat.add 1 (ta_idSalt s x)) ta_constPQ1 f

theorem ta_stfPQ1_eq (s : ℕ) (f : ℕ → ℕ → List PQPair) (x : ℕ) : ta_stfPQ1 s f x = f x := by
  change @Nat.casesOn (fun _ ↦ ℕ → List PQPair) (1 + x) ta_constPQ1 f = f x; rw [Nat.one_add]

/-- Salted strict `List PQPair` barrier (stage 2). -/
def ta_stfPQ2 (s : ℕ) (f : ℕ → ℕ → ℕ → List PQPair) (x : ℕ) : ℕ → ℕ → List PQPair :=
  @Nat.casesOn (fun _ ↦ ℕ → ℕ → List PQPair) (Nat.add 1 (ta_idSalt s x)) ta_constPQ2 f

theorem ta_stfPQ2_eq (s : ℕ) (f : ℕ → ℕ → ℕ → List PQPair) (x : ℕ) : ta_stfPQ2 s f x = f x := by
  change @Nat.casesOn (fun _ ↦ ℕ → ℕ → List PQPair) (1 + x) ta_constPQ2 f = f x; rw [Nat.one_add]

/-- Salted strict `List PQPair` barrier (stage 3). -/
def ta_stfPQ3 (s : ℕ) (f : ℕ → ℕ → ℕ → ℕ → List PQPair) (x : ℕ) : ℕ → ℕ → ℕ → List PQPair :=
  @Nat.casesOn (fun _ ↦ ℕ → ℕ → ℕ → List PQPair) (Nat.add 1 (ta_idSalt s x)) ta_constPQ3 f

theorem ta_stfPQ3_eq (s : ℕ) (f : ℕ → ℕ → ℕ → ℕ → List PQPair) (x : ℕ) : ta_stfPQ3 s f x = f x := by
  change @Nat.casesOn (fun _ ↦ ℕ → ℕ → ℕ → List PQPair) (1 + x) ta_constPQ3 f = f x
  rw [Nat.one_add]

/-- Strict salt-counter barrier (stage 4) for `ta_interleaveChanRevTR`. -/
def ta_tfPQ4 (f : ℕ → ℕ → ℕ → ℕ → ℕ → List PQPair) (x : ℕ) : ℕ → ℕ → ℕ → ℕ → List PQPair :=
  @Nat.casesOn (fun _ ↦ ℕ → ℕ → ℕ → ℕ → List PQPair) (Nat.add 1 x) ta_constPQ4 f

theorem ta_tfPQ4_eq (f : ℕ → ℕ → ℕ → ℕ → ℕ → List PQPair) (x : ℕ) : ta_tfPQ4 f x = f x := by
  change @Nat.casesOn (fun _ ↦ ℕ → ℕ → ℕ → ℕ → List PQPair) (1 + x) ta_constPQ4 f = f x
  rw [Nat.one_add]

/-- Trampolined `O(1)`-stack `List ℕ` reverse (`List.reverse` overflows `8 MiB` above `~13.5k`
    items). -/
def ta_revNatTR (xs acc : List ℕ) : List ℕ := @List.rec ℕ (fun _ ↦ List ℕ → List ℕ)
    (fun a ↦ a) (fun x _ ih a ↦ ta_tramp (ih (x :: a))) xs acc

theorem ta_revNatTR_cons (x : ℕ) (xs acc : List ℕ) :
    ta_revNatTR (x :: xs) acc = ta_revNatTR xs (x :: acc) := rfl

theorem ta_revNatTR_eq : ∀ (xs acc : List ℕ), ta_revNatTR xs acc = xs.reverse ++ acc
  | [], _ => rfl
  | x :: xs, acc => by
      rw [ta_revNatTR_cons, ta_revNatTR_eq xs (x :: acc)]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

/-- Trampolined `O(1)`-stack `List PQPair` reverse. -/
def ta_revPQTR (xs acc : List PQPair) : List PQPair := @List.rec PQPair
    (fun _ ↦ List PQPair → List PQPair) (fun a ↦ a) (fun x _ ih a ↦ ta_tramp (ih (x :: a))) xs
    acc

theorem ta_revPQTR_cons (x : PQPair) (xs acc : List PQPair) :
    ta_revPQTR (x :: xs) acc = ta_revPQTR xs (x :: acc) := rfl

theorem ta_revPQTR_eq : ∀ (xs acc : List PQPair), ta_revPQTR xs acc = xs.reverse ++ acc
  | [], _ => rfl
  | x :: xs, acc => by
      rw [ta_revPQTR_cons, ta_revPQTR_eq xs (x :: acc)]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

/-- Inner continuation for `ta_interleaveChanRevTR`. -/
def ta_interleaveChanStepGo (ih : ℕ → List ℕ → List ℕ → List ℕ → List PQPair → List PQPair)
    (uqt rupt ruqt : List ℕ) (a : List PQPair) (k k2 k' op' oq' eq' ep' : ℕ) : List PQPair :=
    ta_tramp (ih k' uqt rupt ruqt (PQPair.mk (ta_idSalt k2 op') oq' :: PQPair.mk (ta_idSalt k
    ep') eq' :: a))

def finishRootVec4FastOf (unpackShr256 : ℕ → ℕ → ℕ → List ℕ) (d n_lanes rep_bcomb : ℕ)
    (c1 x1 c2 x2 c3 x3 c4 x4 : PolyPN) : List ℕ :=
  let up := mulAdd4Pos c1 x1 c2 x2 c3 x3 c4 x4
  let un := mulAdd4Neg c1 x1 c2 x2 c3 x3 c4 x4
  let w := Nat.sub (Nat.add up rep_bcomb) un
  ta_tfList (unpackShr256 d n_lanes) w

theorem finishRootVec4FastOf_eq (unpackShr256 : ℕ → ℕ → ℕ → List ℕ)
    (d n_lanes rep_bcomb : ℕ) (c1 x1 c2 x2 c3 x3 c4 x4 : PolyPN) :
    finishRootVec4FastOf unpackShr256 d n_lanes rep_bcomb c1 x1 c2 x2 c3 x3 c4 x4 =
      finishRootVec4Of unpackShr256 d n_lanes rep_bcomb c1 x1 c2 x2 c3 x3 c4 x4 := by
  unfold finishRootVec4FastOf finishRootVec4Of
  simp only [ta_tfList_eq, forceNatFast_eq]

theorem ta_shift0_pos : 0 < ta_shift0 := Nat.lt_iff_add_one_le.mpr (Nat.ble_eq.mp rfl)

set_option maxHeartbeats 400000 in
-- Chebyshev L1 biased sum verification
theorem ta_chebL1SumBiased_spec_target
    (M scale0 B B2 Bw R_final W_err_d0 W_err_dpos : ℕ)
    (w_target : ℕ → ℝ)
    (hB2 : B2 = 2 * B)
    (pq : List PQPair) (p : Fin (2 * M + 1) → ℝ)
    (hpq : ∀ k (hk : k < 2 * M + 1),
      let pk := (pq.getD k ⟨B, B⟩).p
      |(pk : ℤ) - (B : ℤ)| ≤ (B : ℤ) ∧
      |(scale0 : ℝ) * p ⟨k, hk⟩ - ((pk : ℝ) - (B : ℝ))| ≤ (R_final : ℝ)) :
    ∀ (ws_rem : List ℕ) (d_start acc : ℕ),
      (∀ j < ws_rem.length,
        |(scale0 : ℝ) * w_target (d_start + j) -
          ((ws_rem.getD j Bw : ℝ) - (Bw : ℝ))| ≤
          (if d_start + j = 0 then (W_err_d0 : ℝ) else (W_err_dpos : ℝ))) →
      (acc : ℝ) + (∑ j ∈ Finset.range ws_rem.length,
        (scale0 : ℝ) * |laurentChebWeight M p (d_start + j) - w_target (d_start + j)|) ≤
        (chebL1SumBiased M B B2 Bw R_final W_err_d0 W_err_dpos pq d_start ws_rem acc : ℝ)
  | [], _, acc, _ => by
      simp only [List.length_nil, Finset.range_zero, Finset.sum_empty, add_zero,
        chebL1SumBiased, le_refl]
  | w :: wt, d, acc, hws => by
    unfold chebL1SumBiased
    simp only [forceNatFast_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
    have hw0 := hws 0 (Nat.zero_lt_succ _)
    rw [Nat.add_zero] at hw0
    change |(scale0 : ℝ) * w_target d - ((w : ℝ) - (Bw : ℝ))| ≤ _ at hw0
    have hws_tail (j : ℕ) (hj : j < wt.length) :
        |(scale0 : ℝ) * w_target ((d + 1) + j) - ((wt.getD j Bw : ℝ) - (Bw : ℝ))| ≤
          (if (d + 1) + j = 0 then (W_err_d0 : ℝ) else (W_err_dpos : ℝ)) := by
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
        show d + (j + 1) = (d + 1) + j by omega] using hws (j + 1) (Nat.succ_lt_succ hj)
    let term := if Nat.beq d 0 = true then natAbsDiff ((pq.getD M ⟨B, B⟩).p + Bw) (w + B) +
        (R_final + W_err_d0) else if Nat.ble d M = true then natAbsDiff (uParityFlip d B2
        (pq.getD (M + d) ⟨B, B⟩).p + (pq.getD (M - d) ⟨B, B⟩).p + Bw) (w + B2) +
        (2 * R_final + W_err_dpos) else natAbsDiff w Bw + W_err_dpos
    have h_term : (scale0 : ℝ) * |laurentChebWeight M p d - w_target d| ≤ (term : ℝ) := by
      rw [show (scale0 : ℝ) * |laurentChebWeight M p d - w_target d| =
          |(scale0 : ℝ) * laurentChebWeight M p d - (scale0 : ℝ) * w_target d| by
        rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) scale0)]]
      by_cases hd0 : d = 0
      · subst hd0
        dsimp only [term]
        simp only [show Nat.beq 0 0 = true from rfl, ↓reduceIte, Nat.cast_add] at hw0 ⊢
        have hM_lt : M < 2 * M + 1 := by omega
        rcases hpq M hM_lt with ⟨_, hpM_err⟩
        let pM := (pq.getD M ⟨B, B⟩).p
        rw [show laurentChebWeight M p 0 = p ⟨M, hM_lt⟩ by simp only [laurentChebWeight,
          ↓reduceIte],
          show (scale0 : ℝ) * p ⟨M, hM_lt⟩ - (scale0 : ℝ) * w_target 0 =
            ((scale0 : ℝ) * p ⟨M, hM_lt⟩ - ((pM : ℝ) - (B : ℝ))) -
            ((scale0 : ℝ) * w_target 0 - ((w : ℝ) - (Bw : ℝ))) +
            (((pM + Bw : ℕ) : ℝ) - ((w + B : ℕ) : ℝ)) by
            simp only [Nat.cast_add]
            ring]
        linarith [abs_sub_add_le_three ((scale0 : ℝ) * p ⟨M, hM_lt⟩ - ((pM : ℝ) - (B : ℝ)))
          ((scale0 : ℝ) * w_target 0 - ((w : ℝ) - (Bw : ℝ)))
          (((pM + Bw : ℕ) : ℝ) - ((w + B : ℕ) : ℝ)),
          hpM_err, hw0, natAbsDiff_cast_real (pM + Bw) (w + B)]
      · have hbeq0 : Nat.beq d 0 = false := Bool.eq_false_iff.mpr (fun ht ↦ hd0 (Nat.beq_eq.mp ht))
        simp only [hd0, ↓reduceIte] at hw0
        by_cases hdM : d ≤ M
        · dsimp only [term]
          simp only [hbeq0, Nat.ble_eq.mpr hdM, Bool.false_eq_true, ↓reduceIte,
            Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
          have hpos_lt : M + d < 2 * M + 1 := by omega
          have hneg_lt : M - d < 2 * M + 1 := by omega
          rcases hpq (M + d) hpos_lt with ⟨hpos_mag, hpos_err⟩
          rcases hpq (M - d) hneg_lt with ⟨_, hneg_err⟩
          let p_pos := uParityFlip d B2 (pq.getD (M + d) ⟨B, B⟩).p
          let p_neg := (pq.getD (M - d) ⟨B, B⟩).p
          have hflip := uParityFlip_spec d B B2 (pq.getD (M + d) ⟨B, B⟩).p
            ((scale0 : ℝ) * p ⟨M + d, hpos_lt⟩) (R_final : ℝ) hB2 hpos_mag hpos_err
          rw [show laurentChebWeight M p d = (-1 : ℝ) ^ d * p ⟨M + d, hpos_lt⟩ + p ⟨M - d,
              hneg_lt⟩ by
              simp only [laurentChebWeight, hd0, hdM, ↓reduceIte, ↓reduceDIte],
            mul_add,
            show (scale0 : ℝ) * ((-1 : ℝ) ^ d * p ⟨M + d, hpos_lt⟩) +
                (scale0 : ℝ) * p ⟨M - d, hneg_lt⟩ - (scale0 : ℝ) * w_target d =
              ((-1 : ℝ) ^ d * ((scale0 : ℝ) * p ⟨M + d, hpos_lt⟩) - ((p_pos : ℝ) - (B : ℝ))) +
              ((scale0 : ℝ) * p ⟨M - d, hneg_lt⟩ - ((p_neg : ℝ) - (B : ℝ))) -
              ((scale0 : ℝ) * w_target d - ((w : ℝ) - (Bw : ℝ))) +
              (((p_pos + p_neg + Bw : ℕ) : ℝ) - ((w + B2 : ℕ) : ℝ)) by
              rw [hB2]
              simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
              ring]
          linarith [abs_add_sub_add_le_four
            ((-1 : ℝ) ^ d * ((scale0 : ℝ) * p ⟨M + d, hpos_lt⟩) - ((p_pos : ℝ) - (B : ℝ)))
            ((scale0 : ℝ) * p ⟨M - d, hneg_lt⟩ - ((p_neg : ℝ) - (B : ℝ)))
            ((scale0 : ℝ) * w_target d - ((w : ℝ) - (Bw : ℝ)))
            (((p_pos + p_neg + Bw : ℕ) : ℝ) - ((w + B2 : ℕ) : ℝ)),
            hflip, hneg_err, hw0, natAbsDiff_cast_real (p_pos + p_neg + Bw) (w + B2)]
        · have hbleM : Nat.ble d M = false := Bool.eq_false_iff.mpr (fun ht ↦ hdM (Nat.ble_eq.mp
            ht))
          dsimp only [term]
          simp only [hbeq0, hbleM, Bool.false_eq_true, ↓reduceIte, Nat.cast_add]
          rw [show laurentChebWeight M p d = 0 by
              simp only [laurentChebWeight, hd0, hdM, ↓reduceIte, ↓reduceDIte],
            mul_zero, zero_sub, abs_neg,
            show (scale0 : ℝ) * w_target d =
              ((scale0 : ℝ) * w_target d - ((w : ℝ) - (Bw : ℝ))) + ((w : ℝ) - (Bw : ℝ)) by ring]
          linarith [abs_add_le ((scale0 : ℝ) * w_target d - ((w : ℝ) - (Bw : ℝ)))
            ((w : ℝ) - (Bw : ℝ)), hw0, natAbsDiff_cast_real w Bw]
    have ih := ta_chebL1SumBiased_spec_target M scale0 B B2 Bw R_final W_err_d0 W_err_dpos
      w_target hB2 pq p hpq wt (d + 1) (acc + term) hws_tail
    rw [List.length_cons, Finset.sum_range_succ', Nat.add_zero,
      Finset.sum_congr rfl fun j _ ↦ by rw [show d + (j + 1) = (d + 1) + j by omega]]
    rw [Nat.cast_add] at ih
    linarith only [h_term, ih]

/- ## Section 3B.6: `O(1)`-Stack `.p`-Only Hadamard, Split, `chebL1`, `chebAbs`, & `asymDefect` -/

/-- Closed 0-capture step trampoline for 1-accumulator `@List.rec` loops. -/
def ta_stepAcc1 (ih : ℕ → ℕ) (a : ℕ) : ℕ := ta_tramp (ih a)

/-- Closed 0-capture step trampoline for `(rem, par, neg, pos, acc)` `@List.rec` loops. -/
def ta_stepBoolList2 (ih : ℕ → Bool → List ℕ → List ℕ → ℕ → ℕ) (rem : ℕ) (par : Bool)
    (xs ys : List ℕ) (a : ℕ) : ℕ := ta_tramp (ih rem par xs ys a)

/-- Closed 0-capture step trampoline for `(k, par, pos, acc)` `@List.rec` loops. -/
def ta_stepBoolList1 (ih : ℕ → Bool → List ℕ → ℕ → ℕ) (k : ℕ) (par : Bool) (xs : List ℕ)
    (a : ℕ) : ℕ := ta_tramp (ih k par xs a)

/-- Base-case cons helper for `ta_hadamardRevPOnlyFast`. -/
def ta_hadamardNilGo (acc : List ℕ) (s np : ℕ) : List ℕ := ta_idSalt s np :: acc

/-- Step helper for `ta_hadamardRevPOnlyFast` (`O(1)` C++ stack via `ta_tramp`). -/
def ta_hadamardStepGo (ih : ℕ → ℕ → List ℕ → List ℕ) (qh : ℕ) (acc : List ℕ) (s1 s' np : ℕ) :
    List ℕ := ta_tramp (ih s' qh (ta_idSalt s1 np :: acc))

/-- `O(1)`-stack `.p`-only reversed outer Hadamard pass (`0` `.q` arithmetic). -/
def ta_hadamardRevPOnlyFast (B : ℕ) (pq : List PQPair) (s0 q0 : ℕ) (acc0 : List ℕ) : List ℕ :=
    @List.rec PQPair (fun _ ↦ ℕ → ℕ → List ℕ → List ℕ) (fun s q_prev acc ↦ ta_stfList s
    (ta_hadamardNilGo acc s) (Nat.shiftRight (Nat.add B q_prev) 1)) (fun h _ ih s q_prev acc ↦
    @PQPair.casesOn (fun _ ↦ List ℕ) h (fun ph qh ↦ ta_stfList (Nat.add 1 s) (ta_tfListFn
    (ta_hadamardStepGo ih qh acc (Nat.add 1 s)) (Nat.add 2 s)) (Nat.shiftRight (Nat.add ph
    q_prev) 1))) pq s0 q0 acc0

theorem ta_hadamardRevPOnlyFast_cons (B ph qh : ℕ) (t : List PQPair) (s q_prev : ℕ) (acc : List ℕ) :
    ta_hadamardRevPOnlyFast B (⟨ph, qh⟩ :: t) s q_prev acc =
      ta_hadamardRevPOnlyFast B t (Nat.add 2 s) qh (Nat.shiftRight (Nat.add ph q_prev) 1 :: acc) :=
        by
  dsimp only [ta_hadamardRevPOnlyFast]
  rw [ta_stfList_eq, show ta_tfListFn (ta_hadamardStepGo _ qh acc (Nat.add 1 s)) (Nat.add 2 s) =
      ta_hadamardStepGo _ qh acc (Nat.add 1 s) (Nat.add 2 s) by
    rw [ta_tfListFn, Nat.add_eq, Nat.one_add]]
  rfl

private theorem ta_hadamardRevPOnlyFast_eq_map (B B2 : ℕ) :
    ∀ (pq : List PQPair) (s q_prev : ℕ) (acc : List PQPair),
      ta_hadamardRevPOnlyFast B pq s q_prev (acc.map PQPair.p) =
        (biHadamardRevAcc B B2 pq q_prev acc).map PQPair.p
  | [], s, q_prev, acc => by
      dsimp only [ta_hadamardRevPOnlyFast, biHadamardRevAcc]
      simp only [ta_stfList_eq, ta_hadamardNilGo, ta_idSalt,
        show ∀ a : ℕ, Nat.shiftRight a 1 = Nat.div a 2 from fun a ↦ Nat.shiftRight_eq_div_pow a 1,
        mkPQConsStrict_true_eq, mkPQConsLazy_eq, List.map_cons]
  | ⟨ph, qh⟩ :: t, s, q_prev, acc => by
      rw [ta_hadamardRevPOnlyFast_cons]
      unfold biHadamardRevAcc
      simp only [show ∀ a : ℕ,
        Nat.shiftRight a 1 = Nat.div a 2 from fun a ↦ Nat.shiftRight_eq_div_pow a 1,
        withHeadStrictPQ_true_eq, mkPQConsStrict_true_eq, mkPQConsLazy_eq]
      exact ta_hadamardRevPOnlyFast_eq_map B B2 t (Nat.add 2 s) qh
        (⟨Nat.div (Nat.add ph q_prev) 2, Nat.div (Nat.add ph (Nat.sub B2 q_prev)) 2⟩ :: acc)

theorem ta_hadamardFinishPOnlyFast_eq_map (B B2 : ℕ) (pq : List PQPair) (q_prev : ℕ) :
    ta_revNatTR (ta_hadamardRevPOnlyFast B pq 1 q_prev []) [] =
      (biHadamardFinishPair B B2 pq q_prev).map PQPair.p := by
  have h := ta_hadamardRevPOnlyFast_eq_map B B2 pq 1 q_prev []
  dsimp only [List.map] at h
  rw [ta_revNatTR_eq, List.append_nil, h, ← List.map_reverse, biHadamardRevAcc_eq,
    List.append_nil, List.reverse_reverse]

/-- Empty-input padding fallback for `ta_splitPRevFast`. -/
def ta_splitPRevNil (B : ℕ) : ℕ → List ℕ → List ℕ × ℕ × List ℕ
  | 0, neg_acc => (neg_acc, B, [])
  | m + 1, neg_acc => ta_splitPRevNil B m (B :: neg_acc)

private theorem ta_splitPRevNil_eq_map (B : ℕ) :
    ∀ (m : ℕ) (neg_acc : List ℕ),
      ta_splitPRevNil B m neg_acc =
        let r := splitPQRevStrict_true B m [] neg_acc
        (r.1, r.2.1, r.2.2.map PQPair.p)
  | 0, _ => rfl
  | m + 1, [] => by
      unfold ta_splitPRevNil splitPQRevStrict_true; exact ta_splitPRevNil_eq_map B m [B]
  | m + 1, _ :: _ => by
      unfold ta_splitPRevNil splitPQRevStrict_true; exact ta_splitPRevNil_eq_map B m _

/-- `O(1)`-stack `.p`-only splitter into `(neg_rev, p_center, pos_tail_p)`. -/
def ta_splitPRevFast (B m0 : ℕ) (ps0 neg0 : List ℕ) : List ℕ × ℕ × List ℕ := @List.rec ℕ
    (fun _ ↦ ℕ → List ℕ → List ℕ × ℕ × List ℕ) (fun m neg_acc ↦ ta_splitPRevNil B m neg_acc)
    (fun p ps ih m neg_acc ↦ @Nat.casesOn (fun _ ↦ List ℕ × ℕ × List ℕ) m (neg_acc, p, ps)
    (fun m' ↦ ta_tramp (ih m' (p :: neg_acc)))) ps0 m0 neg0

theorem ta_splitPRevFast_eq_map (B : ℕ) :
    ∀ (m : ℕ) (pq : List PQPair) (neg_acc : List ℕ),
      ta_splitPRevFast B m (pq.map PQPair.p) neg_acc =
        let r := splitPQRevStrict_true B m pq neg_acc
        (r.1, r.2.1, r.2.2.map PQPair.p)
  | m, [], neg_acc => ta_splitPRevNil_eq_map B m neg_acc
  | 0, ⟨_, _⟩ :: _, _ => rfl
  | m + 1, ⟨p, _⟩ :: xs, [] => by
      change ta_splitPRevFast B m (xs.map PQPair.p) [p] = _
      unfold splitPQRevStrict_true
      exact ta_splitPRevFast_eq_map B m xs [p]
  | m + 1, ⟨p, _⟩ :: xs, _ :: _ => by
      change ta_splitPRevFast B m (xs.map PQPair.p) (p :: _ :: _) = _
      unfold splitPQRevStrict_true
      exact ta_splitPRevFast_eq_map B m xs _

/-- Parity-bit sign flip on `B`-biased `ℕ` (`Bool.casesOn`, zero auxiliary matchers). -/
def ta_parFlip (par : Bool) (B2 u : ℕ) : ℕ := @Bool.casesOn (fun _ ↦ ℕ) par u (Nat.sub B2 u)

theorem ta_parFlip_eq (d B2 u : ℕ) :
    ta_parFlip (Nat.beq (Nat.mod d 2) 1) B2 u = uParityFlip d B2 u := by
  unfold ta_parFlip uParityFlip
  cases Nat.beq (Nat.mod d 2) 1 <;> rfl

theorem ta_not_par_eq_succ (d : ℕ) :
    Bool.not (Nat.beq (Nat.mod d 2) 1) = Nat.beq (Nat.mod (Nat.add d 1) 2) 1 := by
  change Bool.not (Nat.beq (d % 2) 1) = Nat.beq ((d + 1) % 2) 1
  rw [Nat.add_mod d 1 2]
  rcases Nat.mod_two_eq_zero_or_one d with h | h <;> rw [h] <;> rfl

private theorem ta_chebL1SumPosStrict_replicate_Bw (M1 B B2 Bw W_err_dpos err_d_in : ℕ) :
    ∀ (pad d : ℕ) (neg_cur : List ℕ) (pos_cur : List PQPair) (acc : ℕ),
      M1 < d →
      chebL1SumPosStrict_true M1 B B2 Bw W_err_dpos err_d_in d neg_cur pos_cur
        (List.replicate pad Bw) acc = Nat.add acc (Nat.mul pad W_err_dpos)
  | 0, _, _, _, acc, _ => by simp [chebL1SumPosStrict_true]
  | pad + 1, d, neg_cur, pos_cur, acc, hgt => by
      have h0 : natAbsDiff Bw Bw = 0 := by
        exact_mod_cast (by simp [natAbsDiff_cast_real] : (natAbsDiff Bw Bw : ℝ) = (0 : ℕ))
      have hble : Nat.ble d M1 = false :=
        Bool.eq_false_iff.mpr (fun h ↦ Nat.lt_irrefl M1 (Nat.lt_of_lt_of_le hgt (Nat.ble_eq.mp h)))
      rw [List.replicate_succ]
      unfold chebL1SumPosStrict_true
      simp only [forceNatFast_eq, stepListNat_true_eq, stepListPQP_true_eq, hble,
        Bool.false_eq_true, ↓reduceIte, h0, Nat.add_eq, Nat.mul_eq, Nat.zero_add]
      rw [ta_chebL1SumPosStrict_replicate_Bw M1 B B2 Bw W_err_dpos err_d_in pad (d + 1) _ _ _ (by
        omega)]
      simp only [Nat.add_eq, Nat.mul_eq]
      ring

/-- `O(1)`-stack tail accumulator for `d > M1` (`ws` tail + `pad` zero-weight tail). -/
def ta_chebTailFast (Bw W_err_dpos pad : ℕ) (ws : List ℕ) (acc0 : ℕ) : ℕ := @List.rec ℕ
    (fun _ ↦ ℕ → ℕ) (fun acc ↦ Nat.add acc (Nat.mul pad W_err_dpos)) (fun w _ ih acc ↦
    ta_tfNat (ta_stepAcc1 ih) (Nat.add acc (Nat.add (natAbsDiff w Bw) W_err_dpos))) ws acc0

theorem ta_chebTailFast_cons (Bw W_err_dpos pad w : ℕ) (wt : List ℕ) (acc : ℕ) :
    ta_chebTailFast Bw W_err_dpos pad (w :: wt) acc = ta_chebTailFast Bw W_err_dpos pad wt
    (Nat.add acc (Nat.add (natAbsDiff w Bw) W_err_dpos)) := by
  dsimp only [ta_chebTailFast]
  simp only [ta_tfNat_eq, ta_stepAcc1, ta_tramp]

private theorem ta_chebTailFast_eq (M1 B B2 Bw W_err_dpos err_d_in pad : ℕ) :
    ∀ (ws : List ℕ) (d : ℕ) (neg_cur : List ℕ) (pos_cur : List PQPair) (acc : ℕ),
      M1 < d →
      ta_chebTailFast Bw W_err_dpos pad ws acc =
        chebL1SumPosStrict_true M1 B B2 Bw W_err_dpos err_d_in d neg_cur pos_cur
          (ws ++ List.replicate pad Bw) acc
  | [], d, neg_cur, pos_cur, acc, hgt => by
      dsimp only [ta_chebTailFast, List.nil_append]
      exact (ta_chebL1SumPosStrict_replicate_Bw M1 B B2 Bw W_err_dpos err_d_in pad d neg_cur pos_cur
        acc hgt).symm
  | w :: wt, d, neg_cur, pos_cur, acc, hgt => by
      have hble : Nat.ble d M1 = false :=
        Bool.eq_false_iff.mpr (fun h ↦ Nat.lt_irrefl M1 (Nat.lt_of_lt_of_le hgt (Nat.ble_eq.mp h)))
      rw [ta_chebTailFast_cons, List.cons_append]
      unfold chebL1SumPosStrict_true
      simp only [forceNatFast_eq, stepListNat_true_eq, stepListPQP_true_eq, hble,
        Bool.false_eq_true, ↓reduceIte]
      exact ta_chebTailFast_eq M1 B B2 Bw W_err_dpos err_d_in pad wt (Nat.add d 1) _ _ _
        (by simp only [Nat.add_eq]; omega)

/-- `O(1)`-stack `.p`-only positive-index Chebyshev L1 loop with `Bool` parity. -/
def ta_chebL1PosBoolPar (B B2 Bw W_err_dpos err_d_in pad : ℕ)
    (ws0 : List ℕ) (rem0 : ℕ) (par0 : Bool) (neg0 pos0 : List ℕ) (acc0 : ℕ) : ℕ :=
  @List.rec ℕ (fun _ ↦ ℕ → Bool → List ℕ → List ℕ → ℕ → ℕ)
    (fun _ _ _ _ acc ↦ Nat.add acc (Nat.mul pad W_err_dpos))
    (fun w wt ih rem par neg_cur pos_cur acc ↦
      @Nat.casesOn (fun _ ↦ ℕ) rem
        (ta_tfNat (ta_chebTailFast Bw W_err_dpos pad wt)
          (Nat.add acc (Nat.add (natAbsDiff w Bw) W_err_dpos)))
        (fun rem' ↦
          @List.casesOn ℕ (fun _ ↦ ℕ) neg_cur
            (@List.casesOn ℕ (fun _ ↦ ℕ) pos_cur
              (let p_pos := ta_parFlip par B2 B
               ta_tfNat (ta_stepBoolList2 ih rem' (Bool.not par) [] [])
                 (Nat.add acc (Nat.add (natAbsDiff (Nat.add (Nat.add p_pos B) Bw) (Nat.add w B2))
                   err_d_in)))
              (fun p_pos_raw pt ↦
                let p_pos := ta_parFlip par B2 p_pos_raw
                ta_tfNat (ta_stepBoolList2 ih rem' (Bool.not par) [] pt)
                  (Nat.add acc (Nat.add (natAbsDiff (Nat.add (Nat.add p_pos B) Bw) (Nat.add w B2))
                    err_d_in))))
            (fun p_neg nt ↦
              @List.casesOn ℕ (fun _ ↦ ℕ) pos_cur
                (let p_pos := ta_parFlip par B2 B
                 ta_tfNat (ta_stepBoolList2 ih rem' (Bool.not par) nt [])
                   (Nat.add acc (Nat.add (natAbsDiff (Nat.add (Nat.add p_pos p_neg) Bw) (Nat.add w
                     B2)) err_d_in)))
                (fun p_pos_raw pt ↦
                  let p_pos := ta_parFlip par B2 p_pos_raw
                  ta_tfNat (ta_stepBoolList2 ih rem' (Bool.not par) nt pt)
                    (Nat.add acc (Nat.add (natAbsDiff (Nat.add (Nat.add p_pos p_neg) Bw) (Nat.add w
                      B2)) err_d_in))))))
    ws0 rem0 par0 neg0 pos0 acc0

theorem ta_chebL1PosBoolPar_cons_succ (B B2 Bw W_err_dpos err_d_in pad w : ℕ) (wt : List ℕ)
    (rem' : ℕ) (par : Bool) (neg_cur pos_cur : List ℕ) (acc : ℕ) :
    ta_chebL1PosBoolPar B B2 Bw W_err_dpos err_d_in pad (w :: wt) (rem' + 1) par neg_cur pos_cur acc
      =
      let p_neg := neg_cur.headD B
      let p_pos := ta_parFlip par B2 (pos_cur.headD B)
      ta_chebL1PosBoolPar B B2 Bw W_err_dpos err_d_in pad wt rem' (Bool.not par) neg_cur.tail
        pos_cur.tail
        (Nat.add acc (Nat.add (natAbsDiff (Nat.add (Nat.add p_pos p_neg) Bw) (Nat.add w B2))
          err_d_in)) := by
  rcases neg_cur with _ | ⟨_, _⟩ <;> rcases pos_cur with _ | ⟨_, _⟩ <;>
    (dsimp only [ta_chebL1PosBoolPar, List.headD, List.tail];
     simp only [ta_tfNat_eq, ta_stepBoolList2, ta_tramp])

private theorem stepListPQP_map_p (B : ℕ) :
    ∀ (xs : List PQPair) (f : ℕ → List PQPair → ℕ),
      stepListPQP_true B xs f = f ((xs.map PQPair.p).headD B) xs.tail
  | [], _ => rfl
  | ⟨_, _⟩ :: _, _ => rfl

private theorem map_p_tail : ∀ (xs : List PQPair), (xs.map PQPair.p).tail = xs.tail.map PQPair.p
  | [] => rfl
  | _ :: _ => rfl

private theorem ta_chebL1PosBoolPar_eq_map (M1 B B2 Bw W_err_dpos err_d_in pad : ℕ) :
    ∀ (ws : List ℕ) (rem d : ℕ) (neg_cur : List ℕ) (pos_cur : List PQPair) (acc : ℕ),
      d + rem = M1 + 1 →
      M1 < d + ws.length →
      ta_chebL1PosBoolPar B B2 Bw W_err_dpos err_d_in pad ws rem
        (Nat.beq (Nat.mod d 2) 1) neg_cur (pos_cur.map PQPair.p) acc =
        chebL1SumPosStrict_true M1 B B2 Bw W_err_dpos err_d_in d neg_cur pos_cur
          (ws ++ List.replicate pad Bw) acc
  | [], _, d, neg_cur, pos_cur, acc, _, hlen =>
      ta_chebTailFast_eq M1 B B2 Bw W_err_dpos err_d_in pad [] d neg_cur pos_cur acc (by simpa using
        hlen)
  | w :: wt, 0, d, neg_cur, pos_cur, acc, hdrem, _ => by
      have hgt : M1 < d := by omega
      have hble : Nat.ble d M1 = false :=
        Bool.eq_false_iff.mpr (fun h ↦ Nat.lt_irrefl M1 (Nat.lt_of_lt_of_le hgt (Nat.ble_eq.mp h)))
      dsimp only [List.cons_append, ta_chebL1PosBoolPar]
      simp only [ta_tfNat_eq]
      unfold chebL1SumPosStrict_true
      simp only [forceNatFast_eq, stepListNat_true_eq, stepListPQP_true_eq,
        hble, Bool.false_eq_true, ↓reduceIte]
      exact ta_chebTailFast_eq M1 B B2 Bw W_err_dpos err_d_in pad wt (Nat.add d 1) _ _ _
        (by simp only [Nat.add_eq]; omega)
  | w :: wt, rem' + 1, d, neg_cur, pos_cur, acc, hdrem, hlen => by
      have hble : Nat.ble d M1 = true := Nat.ble_eq.mpr (by omega)
      have hstepN : ∀ (xs : List ℕ) (f : ℕ → List ℕ → ℕ),
        stepListNat_true B xs f = f (xs.headD B) xs.tail
        | [], _ => rfl
        | _ :: _, _ => rfl
      rw [ta_chebL1PosBoolPar_cons_succ]
      dsimp only [List.cons_append]
      simp only [ta_parFlip_eq, ta_not_par_eq_succ, map_p_tail]
      unfold chebL1SumPosStrict_true
      simp only [hstepN, stepListPQP_map_p, hble, ↓reduceIte, forceNatFast_eq]
      exact ta_chebL1PosBoolPar_eq_map M1 B B2 Bw W_err_dpos err_d_in pad wt rem' (Nat.add d 1)
        neg_cur.tail pos_cur.tail _ (by simp only [Nat.add_eq]; omega)
        (by simp only [List.length_cons, Nat.add_eq] at hlen ⊢; omega)

/-- Closed start helper for `ta_chebL1POnlyFast`. -/
def ta_chebL1StartGo (M1 B B2 Bw W_err_dpos pad : ℕ)
    (wt neg_rev pos_tail : List ℕ) (err_d_in term0 : ℕ) : ℕ :=
  ta_chebL1PosBoolPar B B2 Bw W_err_dpos err_d_in pad wt M1 true neg_rev pos_tail term0

/-- `O(1)`-stack `.p`-only Chebyshev L1 sum against `ws_unpad ++ replicate pad Bw`. -/
def ta_chebL1POnlyFast (M1 B B2 Bw R_final W_err_d0 W_err_dpos pad : ℕ) (neg_rev : List ℕ)
    (p_center : ℕ) (pos_tail ws_unpad : List ℕ) : ℕ := @List.casesOn ℕ (fun _ ↦ ℕ) ws_unpad 0
    (fun w0 wt ↦ ta_tfNat (ta_tfNatFn (ta_chebL1StartGo M1 B B2 Bw W_err_dpos pad wt neg_rev
    pos_tail) (Nat.add (Nat.mul 2 R_final) W_err_dpos)) (Nat.add (natAbsDiff (Nat.add p_center
    Bw) (Nat.add w0 B)) (Nat.add R_final W_err_d0)))

theorem ta_chebL1POnlyFast_eq_map (M1 B B2 Bw R_final W_err_d0 W_err_dpos pad : ℕ)
    (neg_rev : List ℕ) (p_center : ℕ) (pos_tail : List PQPair) (ws_unpad : List ℕ)
    (hlen : M1 < ws_unpad.length) : ta_chebL1POnlyFast M1 B B2 Bw R_final W_err_d0 W_err_dpos
    pad neg_rev p_center (pos_tail.map PQPair.p) ws_unpad = chebL1SumStrict_true M1 B B2 Bw
    R_final W_err_d0 W_err_dpos neg_rev p_center pos_tail (ws_unpad ++ List.replicate pad Bw) := by
  rcases ws_unpad with _ | ⟨w0, wt⟩
  · cases hlen
  · unfold ta_chebL1POnlyFast chebL1SumStrict_true
    simp only [List.cons_append, ta_tfNat_eq, ta_tfNatFn_eq, ta_chebL1StartGo, forceNatFast_eq]
    exact ta_chebL1PosBoolPar_eq_map M1 B B2 Bw W_err_dpos _ pad wt M1 1 neg_rev pos_tail _
      (Nat.add_comm 1 M1) (by simp only [List.length_cons] at hlen; omega)

/-- Empty-`neg_cur` fallback for `ta_asymDefectLoopPOnlyFast` (`0` steps at runtime). -/
def ta_asymDefectEmptyPOnly (B B2 two_Rf : ℕ) : ℕ → Bool → List ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | k + 1, par, [], acc =>
      let p_pos := ta_parFlip par B2 B
      ta_tfNat (ta_asymDefectEmptyPOnly B B2 two_Rf k (Bool.not par) [])
        (Nat.add acc (Nat.add (natAbsDiff p_pos B) two_Rf))
  | k + 1, par, p_pos_raw :: pt, acc =>
      let p_pos := ta_parFlip par B2 p_pos_raw
      ta_tfNat (ta_asymDefectEmptyPOnly B B2 two_Rf k (Bool.not par) pt)
        (Nat.add acc (Nat.add (natAbsDiff p_pos B) two_Rf))

private theorem ta_asymDefectEmptyPOnly_eq_map (B B2 two_Rf : ℕ) :
    ∀ (k d : ℕ) (pos_cur : List PQPair) (acc : ℕ),
      ta_asymDefectEmptyPOnly B B2 two_Rf k (Nat.beq (Nat.mod d 2) 1) (pos_cur.map PQPair.p) acc =
        asymDefectSumStrictLoop_true B B2 two_Rf k d [] pos_cur acc
  | 0, _, _, _ => rfl
  | k + 1, d, pos_cur, acc => by
      unfold asymDefectSumStrictLoop_true
      rcases pos_cur with _ | ⟨⟨_, _⟩, pt⟩
      · simpa only [List.map, ta_asymDefectEmptyPOnly, ta_tfNat_eq, ta_parFlip_eq,
          ta_not_par_eq_succ, stepListNat_true, stepListPQP_true, forceNatFast_eq] using
          ta_asymDefectEmptyPOnly_eq_map B B2 two_Rf k (Nat.add d 1) [] _
      · simpa only [List.map, ta_asymDefectEmptyPOnly, ta_tfNat_eq, ta_parFlip_eq,
          ta_not_par_eq_succ, stepListNat_true, stepListPQP_true, forceNatFast_eq] using
          ta_asymDefectEmptyPOnly_eq_map B B2 two_Rf k (Nat.add d 1) pt _

/-- `O(1)`-stack `.p`-only asymmetry defect loop over `neg0`. -/
def ta_asymDefectLoopPOnlyFast (B B2 two_Rf : ℕ)
    (k0 : ℕ) (par0 : Bool) (neg0 pos0 : List ℕ) (acc0 : ℕ) : ℕ :=
  @List.rec ℕ (fun _ ↦ ℕ → Bool → List ℕ → ℕ → ℕ)
    (fun k par pos_cur acc ↦ ta_asymDefectEmptyPOnly B B2 two_Rf k par pos_cur acc)
    (fun p_neg _ ih k par pos_cur acc ↦
      @Nat.casesOn (fun _ ↦ ℕ) k acc (fun k' ↦
        @List.casesOn ℕ (fun _ ↦ ℕ) pos_cur
          (let p_pos := ta_parFlip par B2 B
           ta_tfNat (ta_stepBoolList1 ih k' (Bool.not par) [])
             (Nat.add acc (Nat.add (natAbsDiff p_pos p_neg) two_Rf)))
          (fun p_pos_raw pt ↦
            let p_pos := ta_parFlip par B2 p_pos_raw
            ta_tfNat (ta_stepBoolList1 ih k' (Bool.not par) pt)
              (Nat.add acc (Nat.add (natAbsDiff p_pos p_neg) two_Rf)))))
    neg0 k0 par0 pos0 acc0

theorem ta_asymDefectLoopPOnlyFast_cons (B B2 two_Rf k' : ℕ) (par : Bool)
    (p_neg : ℕ) (nt pos_cur : List ℕ) (acc : ℕ) :
    ta_asymDefectLoopPOnlyFast B B2 two_Rf (k' + 1) par (p_neg :: nt) pos_cur acc =
      let p_pos := ta_parFlip par B2 (pos_cur.headD B)
      ta_asymDefectLoopPOnlyFast B B2 two_Rf k' (Bool.not par) nt pos_cur.tail
        (Nat.add acc (Nat.add (natAbsDiff p_pos p_neg) two_Rf)) := by
  rcases pos_cur with _ | ⟨_, _⟩ <;>
    (dsimp only [ta_asymDefectLoopPOnlyFast, List.headD, List.tail];
     simp only [ta_tfNat_eq, ta_stepBoolList1, ta_tramp])

private theorem ta_asymDefectLoopPOnlyFast_eq_map (B B2 two_Rf : ℕ) :
    ∀ (k d : ℕ) (neg_cur : List ℕ) (pos_cur : List PQPair) (acc : ℕ),
      ta_asymDefectLoopPOnlyFast B B2 two_Rf k (Nat.beq (Nat.mod d 2) 1) neg_cur
          (pos_cur.map PQPair.p) acc =
        asymDefectSumStrictLoop_true B B2 two_Rf k d neg_cur pos_cur acc
  | k, d, [], pos_cur, acc => ta_asymDefectEmptyPOnly_eq_map B B2 two_Rf k d pos_cur acc
  | 0, _, _ :: _, _, _ => rfl
  | k + 1, d, p_neg :: nt, pos_cur, acc => by
      rw [ta_asymDefectLoopPOnlyFast_cons]
      simp only [ta_parFlip_eq, ta_not_par_eq_succ, map_p_tail]
      unfold asymDefectSumStrictLoop_true
      dsimp only [stepListNat_true]
      simp only [stepListPQP_map_p, forceNatFast_eq]
      exact ta_asymDefectLoopPOnlyFast_eq_map B B2 two_Rf k (Nat.add d 1) nt pos_cur.tail _

/-- Closed start helper for `ta_asymDefectPOnlyFast`. -/
def ta_asymDefectStartGo (M1 B B2 : ℕ) (neg_rev pos_tail : List ℕ) (two_Rf : ℕ) : ℕ :=
  ta_asymDefectLoopPOnlyFast B B2 two_Rf M1 true neg_rev pos_tail 0

/-- `O(1)`-stack `.p`-only asymmetry defect sum equivalent to `asymDefectSumStrict_true`. -/
def ta_asymDefectPOnlyFast (M1 B B2 R_final : ℕ) (neg_rev pos_tail : List ℕ) : ℕ :=
  ta_tfNat (ta_asymDefectStartGo M1 B B2 neg_rev pos_tail) (Nat.mul 2 R_final)

theorem ta_asymDefectPOnlyFast_eq_map (M1 B B2 R_final : ℕ) (neg_rev : List ℕ)
    (pos_tail : List PQPair) : ta_asymDefectPOnlyFast M1 B B2 R_final neg_rev
    (pos_tail.map PQPair.p) = asymDefectSumStrict_true M1 B B2 R_final neg_rev pos_tail := by
  unfold ta_asymDefectPOnlyFast asymDefectSumStrict_true
  simp only [ta_tfNat_eq, ta_asymDefectStartGo, forceNatFast_eq]
  exact ta_asymDefectLoopPOnlyFast_eq_map B B2 (Nat.mul 2 R_final) M1 1 neg_rev pos_tail 0

def ta_tfBool (f : ℕ → Bool) (x : ℕ) : Bool :=
  @Nat.casesOn (fun _ ↦ Bool) (Nat.add 1 x) false f

theorem ta_tfBool_eq (f : ℕ → Bool) (x : ℕ) : ta_tfBool f x = f x := by
  change @Nat.casesOn (fun _ ↦ Bool) (1 + x) false f = f x
  rw [Nat.one_add]

theorem ta_scale0_eq_D_mul_shift0 : ta_scale0 = 2 ^ 48 * ta_shift0 := rfl

set_option exponentiation.threshold 256
end ConfigSec3B_TwoAngleRootAndCertStitch

end ConfigTwoAngleBiGqspVerifierBridge

end TwoAngleBiGqspVerifierBridge
end
set_option exponentiation.threshold 256
end TwoAngleBiGqspVerifierBridge_aux_p2

section PosPostPrep80FastBounds
local instance (priority := 1000000) instNeZeroTwoPow_PosPostPrep80FastBounds (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

-- Fast Position Post-Preparation Sub-Probability Witness L1, BHMT Keep Algebra,
-- Zero-Subwire Coin-01 Support, and Leaf Perturbation Bounds

public section

namespace PosPostPrep80FastBounds

section ConfigPosPostPrep80FastBounds

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 256

local instance (priority := 1000000)
    instLoc_PosPostPrep80FastBounds_1InstNeZeroTwoPowPos (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator

open FullSysPrepare6Slot (coinSelOutcome)
open FullSysFullPrepareAndTopConcrete (selWiresSym coreWiresSym
    selCoin3Sym coreAncSym)
open FullSysMomSlots0135Concrete (momCoreWires momCoinProj
    momCoinProj_eq_diagonal coinBitFin2 iSlot0Mom iSlot1Mom iSlot2Mom)
open PosSlots24SemanticOracleConcrete80 (ancIdx86)

-- ============================================================================
-- Section 1: Sub-Probability Witness-Support L1 & 1-Round BHMT Keep Algebra
-- ============================================================================

set_option exponentiation.threshold 4100 in
open Classical in
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Coin-`{0, 1}` support preservation (`hSuppPost01` required by `ZeroSubwireGridPert80`),
proved directly from `(hVeff, hSupp0, hSupp1)` via `Matrix.diagonal` homomorphisms. -/
theorem posPostFast_hSuppPost01_of_veff (W_post : Unitary (2 ^ (coreWiresSym 80)))
    (V_eff : Unitary (2 ^ (selWiresSym 80)))
    (hVeff : W_post = (coreAncSym 80).embedUnitary V_eff)
    (hSupp0 : ∀ x ∉ Set.range (ancIdx86 false),
      V_eff.1 x (coinSelOutcome (selCoin3Sym 80) 0) = 0)
    (hSupp1 : ∀ x ∉ Set.range (ancIdx86 true),
      V_eff.1 x (coinSelOutcome (selCoin3Sym 80) 1) = 0)
    (c : Fin 8) (hc : c.val < 2) :
    momCoinProj 80 c *
        (W_post.1 * (coreAncSym 80).basisOutcomeProjector
          (coinSelOutcome (selCoin3Sym 80) c)) =
      W_post.1 * (coreAncSym 80).basisOutcomeProjector
        (coinSelOutcome (selCoin3Sym 80) c) := by
  have hMom : momCoinProj 80 c =
      (coreAncSym 80).embedMatrix ((selCoin3Sym 80).basisOutcomeProjector c) := by
    rw [momCoinProj_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
      QRegister.embedMatrix_diagonal]
    refine congrArg Matrix.diagonal (funext fun x ↦ ?_)
    have hb (j : Fin 3) :
        basisBits 3 ((selCoin3Sym 80).extractIndex ((coreAncSym 80).extractIndex x)) j =
          basisBits (momCoreWires 80) x ((coreAncSym 80) (selCoin3Sym 80 j)) := by
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
    have h0 : basisBits (momCoreWires 80) x (iSlot0Mom 80) =
        basisBits 3 ((selCoin3Sym 80).extractIndex ((coreAncSym 80).extractIndex x)) 0 := by
      rw [hb 0, show (coreAncSym 80) (selCoin3Sym 80 0) = iSlot0Mom 80 from Fin.ext rfl]
    have h1 : basisBits (momCoreWires 80) x (iSlot1Mom 80) =
        basisBits 3 ((selCoin3Sym 80).extractIndex ((coreAncSym 80).extractIndex x)) 1 := by
      rw [hb 1, show (coreAncSym 80) (selCoin3Sym 80 1) = iSlot1Mom 80 from Fin.ext rfl]
    have h2 : basisBits (momCoreWires 80) x (iSlot2Mom 80) =
        basisBits 3 ((selCoin3Sym 80).extractIndex ((coreAncSym 80).extractIndex x)) 2 := by
      rw [hb 2, show (coreAncSym 80) (selCoin3Sym 80 2) = iSlot2Mom 80 from Fin.ext rfl]
    rw [h0, h1, h2]
    generalize (selCoin3Sym 80).extractIndex ((coreAncSym 80).extractIndex x) = y
    by_cases hEq : y = c
    · simp [hEq, coinBitFin2]
    · simp only [hEq, ↓reduceIte]
      by_contra hnz
      refine hEq ((basisBitsEquiv 3).injective (funext fun j ↦ ?_))
      change basisBits 3 y j = basisBits 3 c j
      fin_cases j
      · exact ZMod.val_injective 2 (Classical.byContradiction
          fun (h : (basisBits 3 y 0).val ≠ (coinBitFin2 c 0).val) ↦ hnz (by simp [h]))
      · exact ZMod.val_injective 2 (Classical.byContradiction
          fun (h : (basisBits 3 y 1).val ≠ (coinBitFin2 c 1).val) ↦ hnz (by simp [h]))
      · exact ZMod.val_injective 2 (Classical.byContradiction
          fun (h : (basisBits 3 y 2).val ≠ (coinBitFin2 c 2).val) ↦ hnz (by simp [h]))
  have hext (b : Bool) (p : BitAssignment 80) :
      (selCoin3Sym 80).extractIndex (ancIdx86 b p) = if b then 1 else 0 := by
    refine (basisBitsEquiv 3).injective (funext fun j ↦ ?_)
    change basisBits 3 ((selCoin3Sym 80).extractIndex (ancIdx86 b p)) j =
      basisBits 3 (if b then 1 else 0) j
    rw [QRegister.basisBits_extractIndex]
    change (basisBitsEquiv (selWiresSym 80)) (ancIdx86 b p) (selCoin3Sym 80 j) =
      basisBits 3 (if b then 1 else 0) j
    unfold ancIdx86
    rw [Equiv.apply_symm_apply]
    cases b
    · fin_cases j
      · simp [Bool.false_eq_true, show basisBits 3 0 0 = 0 by decide]
      · simp [Bool.false_eq_true, show basisBits 3 0 1 = 0 by decide]
      · simp [Bool.false_eq_true, show basisBits 3 0 2 = 0 by decide]
    · fin_cases j
      · simp [show basisBits 3 1 0 = 1 by decide]
      · simp [show basisBits 3 1 1 = 0 by decide]
      · simp [show basisBits 3 1 2 = 0 by decide]
  let o : Fin (2 ^ (selWiresSym 80)) := coinSelOutcome (selCoin3Sym 80) c
  let D_o : Operator (2 ^ (selWiresSym 80)) :=
    Matrix.diagonal (fun y ↦ if y = o then (1 : ℂ) else 0)
  have hProjEmbed : (coreAncSym 80).basisOutcomeProjector o = (coreAncSym 80).embedMatrix D_o := by
    dsimp only [D_o]
    rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.embedMatrix_diagonal]
  change momCoinProj 80 c * (W_post.1 * (coreAncSym 80).basisOutcomeProjector o) =
    W_post.1 * (coreAncSym 80).basisOutcomeProjector o
  rw [hVeff, hMom, hProjEmbed,
    QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul]
  refine congrArg (coreAncSym 80).embedMatrix ?_
  rw [QRegister.basisOutcomeProjector_eq_diagonal]
  dsimp only [D_o]
  ext x y
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hy : y = o
  · subst hy
    simp only [↓reduceIte, mul_one]
    by_cases hnz : V_eff.1 x o = 0
    · simp [hnz]
    · have hExt : (selCoin3Sym 80).extractIndex x = c := by
        rcases c with ⟨v, hv⟩
        interval_cases v
        · rcases (show x ∈ Set.range (ancIdx86 false) by by_contra h; exact hnz (hSupp0 x h))
            with ⟨p, rfl⟩
          exact hext false p
        · rcases (show x ∈ Set.range (ancIdx86 true) by by_contra h; exact hnz (hSupp1 x h))
            with ⟨p, rfl⟩
          exact hext true p
      simp [hExt]
  · simp [hy]

set_option maxRecDepth 512

end ConfigPosPostPrep80FastBounds

end PosPostPrep80FastBounds
end
set_option exponentiation.threshold 256
end PosPostPrep80FastBounds

set_option exponentiation.threshold 256

end QuantumComputation.Specs.StoppingPowerSolution
