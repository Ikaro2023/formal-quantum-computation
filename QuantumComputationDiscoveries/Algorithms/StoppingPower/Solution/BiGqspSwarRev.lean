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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.BiGqspWronskBase

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section Gqsp0b_CatAndTree

section
set_option compiler.extract_closed false
namespace GqspWronskian62592
section FastKernelHelpers
set_option maxRecDepth 600000
set_option exponentiation.threshold 2048
open List (length)
local instance (priority := 1000000)
    auxLocInstB_TwoAngleStage2Cert_gqsp_Common_1InstNe (k
    : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Real Operator Matrix Circuit SpecsAux
open SpecsAux.SpecMirror PhaseGradSignalRot
open TFreeLaurentGQSP TFreeLaurentGQSPPresets
    CatalyzedLaurentGQSPBridge
open TFreeLaurentGQSPPresets.FastRecurrenceVerifier
    TFreeLaurentGQSPPresets.FastIntervalRecurrenceVerifier
open BidirectionalCatalyzedGQSP
    BidirectionalCatalyzedGQSPBridge
    BidirectionalIntervalRecurrenceVerifier
open SpecsAux.SpecMirror.BiGqspChunkedMillerCore
open SpecsAux.SpecMirror.BiGqspChunkedMillerCert
    TwoAngleBiGqspVerifierBridge
open scoped Matrix Matrix.Norms.L2Operator BigOperators
noncomputable def gqsp_srevStepFast (hSalt w : ℕ) (rec_lo rec_hi : ℕ → ℕ) (sh_lo sh_hi : ℕ) : ℕ :=
  sched_stfNat hSalt (fun w_hi =>
    let r_hi := sched_stfNat (Nat.add 2 hSalt) rec_hi w_hi
    let w_lo := Nat.sub (sched_idSalt (Nat.add 3 hSalt) w)
      (Nat.shiftLeft (sched_idSalt (Nat.add 4 hSalt) w_hi) sh_lo)
    let r_lo := sched_stfNat (Nat.add 5 hSalt) rec_lo w_lo
    Nat.add r_hi (Nat.shiftLeft (sched_idSalt (Nat.add 6 hSalt) r_lo) sh_hi))
    (Nat.shiftRight (sched_idSalt (Nat.add 1 hSalt) w) sh_lo)
theorem gqsp_srevStepFast_pack (hSalt h lo hi : ℕ) (rec_lo rec_hi : ℕ → ℕ) (sh_hi : ℕ) (hlt : lo <
    1 <<< (768 * h)) : gqsp_srevStepFast hSalt (lo + (hi <<< (768 * h))) rec_lo rec_hi (Nat.mul 768
    h) sh_hi =
    Nat.add (rec_hi hi) (Nat.shiftLeft (rec_lo lo) sh_hi) := by
  have hshr : Nat.shiftRight (lo + (hi <<< (768 * h))) (768 * h) = hi := by
    change (lo + (hi <<< (768 * h))) >>> (768 * h) = hi
    rw [Nat.shiftRight_eq_div_pow]
    exact (sched_mod_div_768_mul_add h lo hi hlt).2
  unfold gqsp_srevStepFast
  simp only [sched_stfNat_eq, sched_idSalt_eq, Nat.mul_eq]
  rw [hshr]
  have hsub : Nat.sub (lo + (hi <<< (768 * h))) (Nat.shiftLeft hi (768 * h)) = lo := by
    change (lo + (hi <<< (768 * h))) - (hi <<< (768 * h)) = lo
    exact Nat.add_sub_cancel_right lo (hi <<< (768 * h))
  rw [hsub]
noncomputable def gqsp_srev1Step (ih : ℕ → ℕ → ℕ → ℕ) (s w acc : ℕ) : ℕ := sched_stfNat s (fun
    w' => sched_stfNat (Nat.add 1 s) (ih (Nat.add 6 s) w') (Nat.add (Nat.land (sched_idSalt
    (Nat.add 2 s) w) gqsp_mask768) (Nat.shiftLeft (sched_idSalt (Nat.add 3 s) acc) 768)))
    (Nat.shiftRight (sched_idSalt (Nat.add 4 s) w) 768)
noncomputable def gqsp_revPow2LeafAux (n0 : ℕ) : ℕ → ℕ → ℕ → ℕ := @Nat.rec
    (fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc) (fun _ ih => gqsp_srev1Step ih) n0
theorem gqsp_revPow2LeafAux_eq :
    ∀ (r s : ℕ) (xs ys : List ℕ), xs.length = r → (∀ x ∈ xs, x < 2 ^ 768) →
      gqsp_revPow2LeafAux r s (pack768 xs) (pack768 ys) = pack768 (xs.reverse ++ ys)
  | 0, _, xs, _, hlen, _ => by
      cases xs with
      | nil => rfl
      | cons _ _ => simp at hlen
  | r + 1, s, xs, ys, hlen, hxs => by
      cases xs with
      | nil => simp at hlen
      | cons x xt =>
          have hx : x < 2 ^ 768 := hxs x List.mem_cons_self
          have hxt : ∀ a ∈ xt, a < 2 ^ 768 := fun a ha ↦ hxs a (List.mem_cons_of_mem x ha)
          rcases gqsp_land_mask768_pack x xt hx with ⟨hlo, hhi⟩
          change gqsp_srev1Step (gqsp_revPow2LeafAux r) s (pack768 (x :: xt)) (pack768 ys) =
            pack768 ((x :: xt).reverse ++ ys)
          unfold gqsp_srev1Step
          simp only [sched_stfNat_eq, sched_idSalt_eq]
          rw [hhi, hlo]
          have hpack_cons : Nat.add x (Nat.shiftLeft (pack768 ys) 768) = pack768 (x :: ys) := rfl
          rw [hpack_cons,
            gqsp_revPow2LeafAux_eq r (Nat.add 6 s) xt (x :: ys) (Nat.succ.inj hlen) hxt]
          simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
noncomputable def gqsp_srev1Op (s w acc : ℕ) : ℕ :=
  Nat.add (Nat.land (sched_idSalt s w) gqsp_mask768)
    (Nat.shiftLeft (sched_idSalt (Nat.add 1 s) acc) 768)
noncomputable def gqsp_srev2Op (s w acc : ℕ) : ℕ := gqsp_srev1Op (Nat.add 3 s)
    (Nat.shiftRight (sched_idSalt (Nat.add 2 s) w) 768) (gqsp_srev1Op s w acc)
noncomputable def gqsp_srev4Op (s w acc : ℕ) : ℕ := sched_stfNat (Nat.add 5 s) (fun w2 =>
    sched_stfNat (Nat.add 6 s) (fun a2 => gqsp_srev2Op (Nat.add 7 s) w2 a2) (gqsp_srev2Op s w
    acc)) (Nat.shiftRight (sched_idSalt (Nat.add 12 s) w) 1536)
theorem gqsp_srev1Op_eq (s w acc : ℕ) : gqsp_srev1Op s w acc = gqsp_rev1Acc w acc := by
  unfold gqsp_srev1Op gqsp_rev1Acc
  rw [sched_idSalt_eq, sched_idSalt_eq]
theorem gqsp_srev2Op_eq (s w acc : ℕ) : gqsp_srev2Op s w acc = gqsp_rev2Acc w acc := by
  unfold gqsp_srev2Op gqsp_rev2Acc
  rw [gqsp_srev1Op_eq, gqsp_srev1Op_eq, sched_idSalt_eq]
theorem gqsp_srev4Op_eq (s w acc : ℕ) : gqsp_srev4Op s w acc = gqsp_rev4Acc w acc := by
  unfold gqsp_srev4Op gqsp_rev4Acc
  rw [sched_stfNat_eq, sched_stfNat_eq, gqsp_srev2Op_eq, gqsp_srev2Op_eq, sched_idSalt_eq]
noncomputable def gqsp_srev4Step (ih : ℕ → ℕ → ℕ → ℕ) (s w acc : ℕ) : ℕ := sched_stfNat
    (Nat.add 13 s) (fun w' => sched_stfNat (Nat.add 14 s) (ih (Nat.add 16 s) w') (gqsp_srev4Op
    s w acc)) (Nat.shiftRight (sched_idSalt (Nat.add 15 s) w) 3072)
noncomputable def gqsp_revPow2Leaf4SaltAux (q0 rem : ℕ) : ℕ → ℕ → ℕ → ℕ := @Nat.rec
    (fun _ => ℕ → ℕ → ℕ → ℕ) (gqsp_revPow2LeafAux rem) (fun _ ih => gqsp_srev4Step ih) q0
theorem gqsp_revPow2Leaf4SaltAux_eq (rem : ℕ) :
    ∀ (q s : ℕ) (xs ys : List ℕ), xs.length = 4 * q + rem → (∀ x ∈ xs, x < 2 ^ 768) →
      gqsp_revPow2Leaf4SaltAux q rem s (pack768 xs) (pack768 ys) = pack768 (xs.reverse ++ ys)
  | 0, s, xs, ys, hlen, hxs => by
      rw [Nat.mul_zero, Nat.zero_add] at hlen
      exact gqsp_revPow2LeafAux_eq rem s xs ys hlen hxs
  | q + 1, s, xs, ys, hlen, hxs => by
      have hsp : xs.take 4 ++ xs.drop 4 = xs := List.take_append_drop 4 xs
      have hl1 : (xs.take 4).length = 4 := by rw [List.length_take]; omega
      have hl2 : (xs.drop 4).length = 4 * q + rem := by rw [List.length_drop]; omega
      have hx1 : ∀ a ∈ xs.take 4, a < 2 ^ 768 := fun a ha ↦ hxs a (List.mem_of_mem_take ha)
      have hx2 : ∀ a ∈ xs.drop 4, a < 2 ^ 768 := fun a ha ↦ hxs a (List.mem_of_mem_drop ha)
      rcases gqsp_rev4Acc_pack (xs.take 4) (xs.drop 4) ys hl1 hx1 with ⟨hr4, hs4⟩
      rw [hsp] at hr4 hs4
      change gqsp_srev4Step (gqsp_revPow2Leaf4SaltAux q rem) s (pack768 xs) (pack768 ys) =
        pack768 (xs.reverse ++ ys)
      unfold gqsp_srev4Step
      simp only [sched_stfNat_eq, sched_idSalt_eq, gqsp_srev4Op_eq]
      rw [hs4, hr4, gqsp_revPow2Leaf4SaltAux_eq rem q (Nat.add 16 s) (xs.drop 4) ((xs.take
        4).reverse ++ ys) hl2 hx2]
      rw [← List.append_assoc, ← List.reverse_append, hsp]
noncomputable def gqsp_srevLeaf64 (s n w : ℕ) : ℕ :=
  sched_stfNat (Nat.add 8 (Nat.mul 512 s)) (fun w0 =>
    gqsp_revPow2Leaf4SaltAux (Nat.div n 4) (Nat.mod n 4) (Nat.add 16 (Nat.mul 512 s)) w0 0) w
theorem gqsp_srevLeaf64_eq (s n : ℕ) (xs : List ℕ) (hlen : xs.length = n) (hxs : ∀ x ∈ xs,
    x < 2 ^ 768) : gqsp_srevLeaf64 s n (pack768 xs) = pack768 xs.reverse := by
  have hlen4 : xs.length = 4 * (Nat.div n 4) + Nat.mod n 4 := by
    change xs.length = 4 * (n / 4) + n % 4
    omega
  unfold gqsp_srevLeaf64
  rw [sched_stfNat_eq]
  change gqsp_revPow2Leaf4SaltAux (Nat.div n 4) (Nat.mod n 4) (Nat.add 16 (Nat.mul 512 s))
      (pack768 xs) (pack768 []) = pack768 xs.reverse
  simpa only [List.append_nil] using
    gqsp_revPow2Leaf4SaltAux_eq (Nat.mod n 4) (Nat.div n 4) (Nat.add 16 (Nat.mul 512 s)) xs []
      hlen4 hxs
noncomputable def gqsp_srevSplit (ih : ℕ → ℕ → ℕ → ℕ) (s n w : ℕ) : ℕ :=
  if Nat.ble n 64 then
    gqsp_srevLeaf64 s n w
  else
    let h := Nat.div n 2
    let h_hi := Nat.sub n h
    gqsp_srevStepFast (Nat.mul 512 s) w
      (ih (Nat.mul 2 s) h)
      (ih (Nat.add 1 (Nat.mul 2 s)) h_hi)
      (Nat.mul 768 h) (Nat.mul 768 h_hi)
noncomputable def gqsp_revPow2SaltAux (d : ℕ) : ℕ → ℕ → ℕ → ℕ := @Nat.rec
    (fun _ => ℕ → ℕ → ℕ → ℕ) gqsp_srevLeaf64 (fun _ ih => gqsp_srevSplit ih) d
set_option maxHeartbeats 800000 in
-- SWAR bit-reversal recurrence verification
theorem gqsp_revPow2SaltAux_eq (d : ℕ) : ∀ (s n : ℕ) (xs : List ℕ), xs.length = n → (∀ x ∈ xs,
    x < 2 ^ 768) → gqsp_revPow2SaltAux d s n (pack768 xs) = pack768 xs.reverse := by
  induction d with
  | zero =>
      intro s n xs hlen hxs
      exact gqsp_srevLeaf64_eq s n xs hlen hxs
  | succ d ih =>
      intro s n xs hlen hxs
      change gqsp_srevSplit (gqsp_revPow2SaltAux d) s n (pack768 xs) = pack768 xs.reverse
      unfold gqsp_srevSplit
      by_cases hb : Nat.ble n 64 = true
      · simp only [hb, ↓reduceIte]
        exact gqsp_srevLeaf64_eq s n xs hlen hxs
      · have hbf : Nat.ble n 64 = false := Bool.eq_false_iff.mpr hb
        simp only [hbf, Bool.false_eq_true, ↓reduceIte]
        let h := n / 2
        have hsp : xs.take h ++ xs.drop h = xs := List.take_append_drop h xs
        have hl1 : (xs.take h).length = h := by rw [List.length_take]; omega
        have hl2 : (xs.drop h).length = n - h := by rw [List.length_drop]; omega
        have hx1 : ∀ a ∈ xs.take h, a < 2 ^ 768 := fun a ha ↦ hxs a (List.mem_of_mem_take ha)
        have hx2 : ∀ a ∈ xs.drop h, a < 2 ^ 768 := fun a ha ↦ hxs a (List.mem_of_mem_drop ha)
        have hx1p : ∀ a ∈ xs.take h, a < sched_pow768 :=
          fun a ha ↦ sched_pow768_eq_pow.symm ▸ hx1 a ha
        have hp : pack768 xs = pack768 (xs.take h) + (pack768 (xs.drop h) <<< (768 * h)) := by
          conv_lhs => rw [← hsp]
          rw [sched_pack768_append, hl1]
        have hlt1 : pack768 (xs.take h) < 1 <<< (768 * h) := by
          simpa only [hl1] using sched_pack768_lt (xs.take h) hx1p
        change gqsp_srevStepFast (Nat.mul 512 s) (pack768 xs)
          (gqsp_revPow2SaltAux d (Nat.mul 2 s) h)
          (gqsp_revPow2SaltAux d (Nat.add 1 (Nat.mul 2 s)) (Nat.sub n h)) (Nat.mul 768 h)
          (Nat.mul 768 (Nat.sub n h)) = pack768 xs.reverse
        rw [hp, gqsp_srevStepFast_pack (Nat.mul 512 s) h (pack768 (xs.take h)) (pack768 (xs.drop
            h)) (gqsp_revPow2SaltAux d (Nat.mul 2 s) h) (gqsp_revPow2SaltAux d (Nat.add 1 (Nat.mul
            2 s)) (Nat.sub n h))
            (Nat.mul 768 (Nat.sub n h)) hlt1]
        simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq]
        rw[ih (1 + 2 * s) (n - h) (xs.drop h) hl2 hx2, ih (2 * s) h (xs.take h) hl1 hx1]
        have hrev_len : (xs.drop h).reverse.length = n - h := by rw [List.length_reverse, hl2]
        change pack768 (xs.drop h).reverse + (pack768 (xs.take h).reverse <<< (768 * (n - h))) =
          pack768 xs.reverse
        rw [← hrev_len, ← sched_pack768_append, ← List.reverse_append, hsp]
noncomputable def gqsp_speelConsFlip (racc : List ℕ) (v : ℕ) : List ℕ := v :: racc
noncomputable def gqsp_speel1StepGo (ih : ℕ → ℕ → List ℕ → List ℕ) (s : ℕ) (racc : List ℕ) (w' v :
    ℕ) : List ℕ :=
  ih (Nat.add 5 s) w' (v :: racc)
noncomputable def gqsp_speel1StepHi (ih : ℕ → ℕ → List ℕ → List ℕ) (s w : ℕ) (racc : List ℕ) (w' :
    ℕ) : List ℕ :=
  sched_stfList (Nat.add 1 s) (gqsp_speel1StepGo ih s racc w')
    (Nat.shiftRight (Nat.land (sched_idSalt (Nat.add 2 s) w) gqsp_mask768) 256)
noncomputable def gqsp_speel1Step (ih : ℕ → ℕ → List ℕ → List ℕ) (s w : ℕ) (racc : List ℕ) : List ℕ
    :=
  sched_stfList s (gqsp_speel1StepHi ih s w racc)
    (Nat.shiftRight (sched_idSalt (Nat.add 3 s) w) 768)
noncomputable def gqsp_unpackPow2LeafAux (n0 : ℕ) : ℕ → ℕ → List ℕ → List ℕ := @Nat.rec
    (fun _ => ℕ → ℕ → List ℕ → List ℕ) (fun _ _ racc => racc)
    (fun _ ih => gqsp_speel1Step ih) n0
theorem gqsp_unpackPow2LeafAux_eq :
    ∀ (r s : ℕ) (zs racc : List ℕ), zs.length = r → (∀ z ∈ zs, z < 2 ^ 768) →
      gqsp_unpackPow2LeafAux r s (pack768 zs) racc =
        (zs.map (fun z ↦ Nat.shiftRight z 256)).reverse ++ racc
  | 0, _, zs, _, hlen, _ => by
      cases zs with
      | nil => rfl
      | cons _ _ => simp at hlen
  | r + 1, s, zs, racc, hlen, hzs => by
      cases zs with
      | nil => simp at hlen
      | cons z zt =>
          have hz : z < 2 ^ 768 := hzs z List.mem_cons_self
          have hzt : ∀ a ∈ zt, a < 2 ^ 768 := fun a ha ↦ hzs a (List.mem_cons_of_mem z ha)
          rcases gqsp_land_mask768_pack z zt hz with ⟨hlo, hhi⟩
          change gqsp_speel1Step (gqsp_unpackPow2LeafAux r) s (pack768 (z :: zt)) racc =
            ((z :: zt).map (fun u ↦ Nat.shiftRight u 256)).reverse ++ racc
          unfold gqsp_speel1Step gqsp_speel1StepHi gqsp_speel1StepGo
          simp only [sched_stfList_eq, sched_idSalt_eq]
          rw [hhi, hlo, gqsp_unpackPow2LeafAux_eq r (Nat.add 5 s) zt (Nat.shiftRight z 256 :: racc)
            (Nat.succ.inj hlen) hzt, List.map_cons, List.reverse_cons, List.append_assoc,
            List.singleton_append]
noncomputable def gqsp_speel1Op (s w : ℕ) (racc : List ℕ) : List ℕ :=
  sched_stfList s (gqsp_speelConsFlip racc)
    (Nat.shiftRight (Nat.land (sched_idSalt (Nat.add 1 s) w) gqsp_mask768) 256)
theorem gqsp_speel1Op_pack (s z : ℕ) (zt racc : List ℕ) (hz : z < 2 ^ 768) : gqsp_speel1Op s
    (pack768 (z :: zt)) racc = Nat.shiftRight z 256 :: racc := by
  unfold gqsp_speel1Op gqsp_speelConsFlip
  rw [sched_stfList_eq, sched_idSalt_eq, (gqsp_land_mask768_pack z zt hz).1]
noncomputable def gqsp_speel4Op3 (s : ℕ) (r3 : List ℕ) (w3 : ℕ) : List ℕ :=
  gqsp_speel1Op (Nat.add 9 s) w3 r3
noncomputable def gqsp_speel4Op2 (s : ℕ) (r2 : List ℕ) (w2 : ℕ) : List ℕ :=
  let r3 := gqsp_speel1Op (Nat.add 6 s) w2 r2
  sched_stfList (Nat.add 8 s) (gqsp_speel4Op3 s r3)
    (Nat.shiftRight (sched_idSalt (Nat.add 10 s) w2) 768)
noncomputable def gqsp_speel4Op1 (s : ℕ) (r1 : List ℕ) (w1 : ℕ) : List ℕ :=
  let r2 := gqsp_speel1Op (Nat.add 3 s) w1 r1
  sched_stfList (Nat.add 5 s) (gqsp_speel4Op2 s r2)
    (Nat.shiftRight (sched_idSalt (Nat.add 11 s) w1) 768)
noncomputable def gqsp_speel4Op (s w : ℕ) (racc : List ℕ) : List ℕ :=
  let r1 := gqsp_speel1Op s w racc
  sched_stfList (Nat.add 2 s) (gqsp_speel4Op1 s r1)
    (Nat.shiftRight (sched_idSalt (Nat.add 12 s) w) 768)
theorem gqsp_speel4Op_pack (s z0 z1 z2 z3 : ℕ) (zt racc : List ℕ) (h0 : z0 < 2 ^ 768) (h1 : z1 < 2
    ^ 768) (h2 : z2 < 2 ^ 768) (h3 : z3 < 2 ^ 768) : gqsp_speel4Op s (pack768 (z0 :: z1 :: z2 :: z3
    :: zt)) racc
    = Nat.shiftRight z3 256 :: Nat.shiftRight z2 256 :: Nat.shiftRight z1 256 :: Nat.shiftRight z0
      256 :: racc ∧ Nat.shiftRight (pack768 (z0 :: z1 :: z2 :: z3 :: zt)) 3072 = pack768 zt := by
  rcases gqsp_land_mask768_pack z0 (z1 :: z2 :: z3 :: zt) h0 with ⟨_, hs0⟩
  rcases gqsp_land_mask768_pack z1 (z2 :: z3 :: zt) h1 with ⟨_, hs1⟩
  rcases gqsp_land_mask768_pack z2 (z3 :: zt) h2 with ⟨_, hs2⟩
  refine ⟨?_, (gqsp_peel4Shr256_pack z0 z1 z2 z3 zt racc h0 h1 h2 h3).2⟩
  unfold gqsp_speel4Op gqsp_speel4Op1 gqsp_speel4Op2 gqsp_speel4Op3
  dsimp only
  simp only [sched_stfList_eq, sched_idSalt_eq]
  rw[gqsp_speel1Op_pack s z0 _ racc h0, hs0, gqsp_speel1Op_pack _ z1 _ _ h1, hs1,
    gqsp_speel1Op_pack _ z2 _ _ h2, hs2, gqsp_speel1Op_pack _ z3 zt _ h3]
noncomputable def gqsp_speel4StepGo (ih : ℕ → ℕ → List ℕ → List ℕ) (s w : ℕ) (racc : List ℕ) (w' :
    ℕ) : List ℕ :=
  ih (Nat.add 16 s) w' (gqsp_speel4Op s w racc)
noncomputable def gqsp_speel4Step (ih : ℕ → ℕ → List ℕ → List ℕ) (s w : ℕ) (racc : List ℕ) : List ℕ
    :=
  sched_stfList (Nat.add 13 s) (gqsp_speel4StepGo ih s w racc)
    (Nat.shiftRight (sched_idSalt (Nat.add 14 s) w) 3072)
noncomputable def gqsp_unpackPow2Leaf4SaltAux (q0 rem : ℕ) : ℕ → ℕ → List ℕ → List ℕ :=
    @Nat.rec (fun _ => ℕ → ℕ → List ℕ → List ℕ) (gqsp_unpackPow2LeafAux rem)
    (fun _ ih => gqsp_speel4Step ih) q0
set_option maxHeartbeats 800000 in
-- SWAR bit-reversal recurrence verification
theorem gqsp_unpackPow2Leaf4SaltAux_eq (rem : ℕ) :
    ∀ (q s : ℕ) (zs racc : List ℕ), zs.length = 4 * q + rem → (∀ z ∈ zs, z < 2 ^ 768) →
      gqsp_unpackPow2Leaf4SaltAux q rem s (pack768 zs) racc =
        (zs.map (fun z ↦ Nat.shiftRight z 256)).reverse ++ racc
  | 0, s, zs, racc, hlen, hzs => gqsp_unpackPow2LeafAux_eq rem s zs racc (by simpa using hlen) hzs
  | q + 1, s, zs, racc, hlen, hzs => by
      rcases zs with _ | ⟨z0, _ | ⟨z1, _ | ⟨z2, _ | ⟨z3, zt⟩⟩⟩⟩
      · simp only [List.length_nil] at hlen; omega
      · simp only [List.length_cons, List.length_nil] at hlen; omega
      · simp only [List.length_cons, List.length_nil] at hlen; omega
      · simp only [List.length_cons, List.length_nil] at hlen; omega
      · rcases List.forall_mem_cons.mp hzs with ⟨h0, hzs1⟩
        rcases List.forall_mem_cons.mp hzs1 with ⟨h1, hzs2⟩
        rcases List.forall_mem_cons.mp hzs2 with ⟨h2, hzs3⟩
        rcases List.forall_mem_cons.mp hzs3 with ⟨h3, hzt⟩
        have hl_zt : zt.length = 4 * q + rem := by simp only [List.length_cons] at hlen; omega
        rcases gqsp_speel4Op_pack s z0 z1 z2 z3 zt racc h0 h1 h2 h3 with ⟨hp4, hs4⟩
        change gqsp_speel4Step (gqsp_unpackPow2Leaf4SaltAux q rem) s
            (pack768 (z0 :: z1 :: z2 :: z3 :: zt)) racc = _
        unfold gqsp_speel4Step gqsp_speel4StepGo
        simp only [sched_stfList_eq, sched_idSalt_eq]
        rw [hs4, hp4, gqsp_unpackPow2Leaf4SaltAux_eq rem q (Nat.add 16 s) zt _ hl_zt hzt]
        simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append]
noncomputable def gqsp_frev1Go (ih : ℕ → ℕ → ℕ → ℕ) (s w acc w' : ℕ) : ℕ := sched_stfNat
    (Nat.add 1 s) (ih (Nat.add 6 s) w') (Nat.add (Nat.land (sched_idSalt (Nat.add 2 s) w)
    gqsp_mask768) (Nat.shiftLeft (sched_idSalt (Nat.add 3 s) acc) 768))
noncomputable def gqsp_frev1Step (ih : ℕ → ℕ → ℕ → ℕ) (s w acc : ℕ) : ℕ := sched_stfNat s
    (gqsp_frev1Go ih s w acc) (Nat.shiftRight (sched_idSalt (Nat.add 4 s) w) 768)
noncomputable def gqsp_frevLeafAux (n0 : ℕ) : ℕ → ℕ → ℕ → ℕ := @Nat.rec
    (fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc) (fun _ ih => gqsp_frev1Step ih) n0
theorem gqsp_frevLeafAux_eq_revPow2 :
    ∀ (r s w acc : ℕ), gqsp_frevLeafAux r s w acc = gqsp_revPow2LeafAux r s w acc
  | 0, _, _, _ => rfl
  | r + 1, s, w, acc => by
      change gqsp_frev1Step (gqsp_frevLeafAux r) s w acc =
        gqsp_srev1Step (gqsp_revPow2LeafAux r) s w acc
      unfold gqsp_frev1Step gqsp_frev1Go gqsp_srev1Step
      simp only [sched_stfNat_eq, sched_idSalt_eq]
      exact gqsp_frevLeafAux_eq_revPow2 r _ _ _
noncomputable def gqsp_frev4Op2 (s a2 w2 : ℕ) : ℕ := gqsp_srev2Op (Nat.add 7 s) w2 a2
noncomputable def gqsp_frev4Op1 (s w a2 : ℕ) : ℕ := sched_stfNat (Nat.add 5 s)
    (gqsp_frev4Op2 s a2) (Nat.shiftRight (sched_idSalt (Nat.add 12 s) w) 1536)
noncomputable def gqsp_frev4Op (s w acc : ℕ) : ℕ :=
  sched_stfNat (Nat.add 6 s) (gqsp_frev4Op1 s w) (gqsp_srev2Op s w acc)
theorem gqsp_frev4Op_eq_srev4Op (s w acc : ℕ) : gqsp_frev4Op s w acc = gqsp_srev4Op s w acc := by
  unfold gqsp_frev4Op gqsp_frev4Op1 gqsp_frev4Op2 gqsp_srev4Op
  simp only [sched_stfNat_eq, sched_idSalt_eq]
noncomputable def gqsp_frev4Go (ih : ℕ → ℕ → ℕ → ℕ) (s w acc w' : ℕ) : ℕ :=
  sched_stfNat (Nat.add 14 s) (ih (Nat.add 16 s) w') (gqsp_frev4Op s w acc)
noncomputable def gqsp_frev4Step (ih : ℕ → ℕ → ℕ → ℕ) (s w acc : ℕ) : ℕ :=
  sched_stfNat (Nat.add 13 s) (gqsp_frev4Go ih s w acc)
    (Nat.shiftRight (sched_idSalt (Nat.add 15 s) w) 3072)
noncomputable def gqsp_frevLeaf4Aux (q0 rem : ℕ) : ℕ → ℕ → ℕ → ℕ := @Nat.rec
    (fun _ => ℕ → ℕ → ℕ → ℕ) (gqsp_frevLeafAux rem) (fun _ ih => gqsp_frev4Step ih) q0
theorem gqsp_frevLeaf4Aux_eq_revPow2 (rem : ℕ) :
    ∀ (q s w acc : ℕ),
      gqsp_frevLeaf4Aux q rem s w acc = gqsp_revPow2Leaf4SaltAux q rem s w acc
  | 0, s, w, acc => gqsp_frevLeafAux_eq_revPow2 rem s w acc
  | q + 1, s, w, acc => by
      change gqsp_frev4Step (gqsp_frevLeaf4Aux q rem) s w acc =
        gqsp_srev4Step (gqsp_revPow2Leaf4SaltAux q rem) s w acc
      unfold gqsp_frev4Step gqsp_frev4Go gqsp_srev4Step
      simp only [sched_stfNat_eq, sched_idSalt_eq, gqsp_frev4Op_eq_srev4Op]
      exact gqsp_frevLeaf4Aux_eq_revPow2 rem q _ _ _
noncomputable def gqsp_frev3 (s w : ℕ) : ℕ := gqsp_srev1Op (Nat.add 8 s)
    (Nat.shiftRight (sched_idSalt (Nat.add 7 s) w) 1536) (gqsp_srev2Op s w 0)
theorem gqsp_frev3_eq (s w : ℕ) : gqsp_frev3 s w = gqsp_revPow2LeafAux 3 s w 0 := by
  have hsh : Nat.shiftRight w 1536 = Nat.shiftRight (Nat.shiftRight w 768) 768 := by
    simp only [Nat.shiftRight_eq, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]
  change gqsp_frev3 s w =
    gqsp_srev1Step (gqsp_srev1Step (gqsp_srev1Step (fun _ _ acc => acc))) s w 0
  unfold gqsp_frev3 gqsp_srev2Op gqsp_srev1Op gqsp_srev1Step
  simp only [sched_stfNat_eq, sched_idSalt_eq]
  rw [hsh]
noncomputable def gqsp_frev5 (s w : ℕ) : ℕ := gqsp_srev1Op (Nat.add 16 s)
    (Nat.shiftRight (sched_idSalt (Nat.add 15 s) w) 3072) (gqsp_frev4Op s w 0)
theorem gqsp_frev5_eq (s w : ℕ) : gqsp_frev5 s w = gqsp_revPow2Leaf4SaltAux 1 1 s w 0 := by
  change gqsp_frev5 s w = gqsp_srev4Step (gqsp_srev1Step (fun _ _ acc => acc)) s w 0
  unfold gqsp_frev5 gqsp_srev1Op gqsp_srev4Step gqsp_srev1Step
  simp only [sched_stfNat_eq, sched_idSalt_eq, gqsp_frev4Op_eq_srev4Op]
noncomputable def gqsp_frevLeaf64Go (s n w0 : ℕ) : ℕ :=
  gqsp_frevLeaf4Aux (Nat.div n 4) (Nat.mod n 4) (Nat.add 16 (Nat.mul 512 s)) w0 0
noncomputable def gqsp_frevLeaf64 (s n w : ℕ) : ℕ :=
  sched_stfNat (Nat.add 8 (Nat.mul 512 s)) (gqsp_frevLeaf64Go s n) w
theorem gqsp_frevLeaf64_eq_srev (s n w : ℕ) : gqsp_frevLeaf64 s n w = gqsp_srevLeaf64 s n w := by
  unfold gqsp_frevLeaf64 gqsp_frevLeaf64Go gqsp_srevLeaf64
  simp only [sched_stfNat_eq, gqsp_frevLeaf4Aux_eq_revPow2]
noncomputable def gqsp_frevStepJoin (hSalt sh_hi r_hi r_lo : ℕ) : ℕ :=
  Nat.add r_hi (Nat.shiftLeft (sched_idSalt (Nat.add 6 hSalt) r_lo) sh_hi)
noncomputable def gqsp_frevStepCallLo (hSalt : ℕ) (rec_lo : ℕ → ℕ) (sh_hi r_hi w_lo : ℕ) : ℕ :=
  sched_stfNat (Nat.add 7 hSalt) (gqsp_frevStepJoin hSalt sh_hi r_hi) (rec_lo w_lo)
noncomputable def gqsp_frevStepLo (hSalt w : ℕ) (rec_lo : ℕ → ℕ) (sh_lo sh_hi w_hi r_hi : ℕ) : ℕ :=
  sched_stfNat (Nat.add 5 hSalt) (gqsp_frevStepCallLo hSalt rec_lo sh_hi r_hi)
    (Nat.sub (sched_idSalt (Nat.add 3 hSalt) w)
      (Nat.shiftLeft (sched_idSalt (Nat.add 4 hSalt) w_hi) sh_lo))
noncomputable def gqsp_frevStepHi (hSalt w : ℕ) (rec_lo rec_hi : ℕ → ℕ) (sh_lo sh_hi w_hi : ℕ) : ℕ
    :=
  sched_stfNat (Nat.add 2 hSalt) (gqsp_frevStepLo hSalt w rec_lo sh_lo sh_hi w_hi)
    (rec_hi w_hi)
noncomputable def gqsp_frevStepFast (hSalt w : ℕ) (rec_lo rec_hi : ℕ → ℕ) (sh_lo sh_hi : ℕ) : ℕ :=
  sched_stfNat hSalt (gqsp_frevStepHi hSalt w rec_lo rec_hi sh_lo sh_hi)
    (Nat.shiftRight (sched_idSalt (Nat.add 1 hSalt) w) sh_lo)
theorem gqsp_frevStepFast_eq_srev (hSalt w : ℕ) (rec_lo rec_hi : ℕ → ℕ) (sh_lo sh_hi : ℕ) :
    gqsp_frevStepFast hSalt w rec_lo rec_hi sh_lo sh_hi = gqsp_srevStepFast hSalt w rec_lo rec_hi
    sh_lo sh_hi := by
  unfold gqsp_frevStepFast gqsp_frevStepHi gqsp_frevStepLo gqsp_frevStepCallLo
    gqsp_frevStepJoin gqsp_srevStepFast
  simp only [sched_stfNat_eq, sched_idSalt_eq]
noncomputable def gqsp_frevSplit (ih : ℕ → ℕ → ℕ → ℕ) (s n w : ℕ) : ℕ :=
  if Nat.ble n 64 then
    gqsp_frevLeaf64 s n w
  else
    let h := Nat.div n 2
    let h_hi := Nat.sub n h
    gqsp_frevStepFast (Nat.mul 512 s) w
      (ih (Nat.mul 2 s) h)
      (ih (Nat.add 1 (Nat.mul 2 s)) h_hi)
      (Nat.mul 768 h) (Nat.mul 768 h_hi)
noncomputable def gqsp_frevPow2Aux (d : ℕ) : ℕ → ℕ → ℕ → ℕ := @Nat.rec
    (fun _ => ℕ → ℕ → ℕ → ℕ) gqsp_frevLeaf64 (fun _ ih => gqsp_frevSplit ih) d
set_option maxHeartbeats 800000 in
-- SWAR bit-reversal recurrence verification
theorem gqsp_frevPow2Aux_eq_revPow2 :
    ∀ (d s n w : ℕ), gqsp_frevPow2Aux d s n w = gqsp_revPow2SaltAux d s n w
  | 0, s, n, w => gqsp_frevLeaf64_eq_srev s n w
  | d + 1, s, n, w => by
      change gqsp_frevSplit (gqsp_frevPow2Aux d) s n w =
        gqsp_srevSplit (gqsp_revPow2SaltAux d) s n w
      unfold gqsp_frevSplit gqsp_srevSplit
      by_cases hb : Nat.ble n 64 = true
      · simp only [hb, ↓reduceIte, gqsp_frevLeaf64_eq_srev]
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, gqsp_frevStepFast_eq_srev]
        have ih_lo : gqsp_frevPow2Aux d (Nat.mul 2 s) (Nat.div n 2) =
            gqsp_revPow2SaltAux d (Nat.mul 2 s) (Nat.div n 2) :=
          funext fun x => gqsp_frevPow2Aux_eq_revPow2 d _ _ x
        have ih_hi : gqsp_frevPow2Aux d (Nat.add 1 (Nat.mul 2 s)) (Nat.sub n (Nat.div n 2)) =
            gqsp_revPow2SaltAux d (Nat.add 1 (Nat.mul 2 s)) (Nat.sub n (Nat.div n 2)) :=
          funext fun x => gqsp_frevPow2Aux_eq_revPow2 d _ _ x
        rw [ih_lo, ih_hi]
noncomputable def gqsp_fastRevGo (d n w s0 : ℕ) : ℕ := if Nat.beq n 3 then gqsp_frev3 s0 w
    else if Nat.beq n 5 then gqsp_frev5 s0 w else gqsp_frevPow2Aux (Nat.sub d 6) s0 n w
noncomputable def gqsp_fastRevSwarSalt (c_idx salt d n w : ℕ) : ℕ :=
  sched_tfNat (gqsp_fastRevGo d n w)
    (Nat.add (Nat.mul 0x1000000000 (Nat.add 8 c_idx)) (Nat.land salt 0xfffffffff))
theorem gqsp_fastRevSwarSalt_spec (c_idx salt d n : ℕ) (xs : List ℕ) (hxl : xs.length = n) (hxb : ∀
    x ∈ xs, x < 2 ^ 768) : gqsp_fastRevSwarSalt c_idx salt d n (pack768 xs) = pack768 xs.reverse :=
    by
  unfold gqsp_fastRevSwarSalt gqsp_fastRevGo
  rw [sched_tfNat_eq]
  by_cases h3 : Nat.beq n 3 = true
  · simp only [h3, ↓reduceIte, gqsp_frev3_eq]
    have hn : xs.length = 3 := hxl.trans (Nat.beq_eq.mp h3)
    simpa only [sched_pack768_nil, List.append_nil] using
      gqsp_revPow2LeafAux_eq 3 _ xs [] hn hxb
  · simp only [h3, Bool.false_eq_true, ↓reduceIte]
    by_cases h5 : Nat.beq n 5 = true
    · simp only [h5, ↓reduceIte, gqsp_frev5_eq]
      have hn : xs.length = 4 * 1 + 1 := hxl.trans (Nat.beq_eq.mp h5)
      simpa only [sched_pack768_nil, List.append_nil] using
        gqsp_revPow2Leaf4SaltAux_eq 1 1 _ xs [] hn hxb
    · simp only [h5, Bool.false_eq_true, ↓reduceIte, gqsp_frevPow2Aux_eq_revPow2]
      exact gqsp_revPow2SaltAux_eq (Nat.sub d 6) _ n xs hxl hxb
theorem gqsp_nat_shl_eq (a b : ℕ) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b
theorem gqsp_forall2_le_rep {B : ℕ} : ∀ (xs : List ℕ),
    (∀ x ∈ xs, x ≤ B) → List.Forall₂ (· ≤ ·) xs (List.replicate xs.length B)
  | [], _ => List.Forall₂.nil
  | x :: xt, hxs =>
      List.Forall₂.cons (hxs x List.mem_cons_self)
        (gqsp_forall2_le_rep xt (fun a ha => hxs a (List.mem_cons_of_mem x ha)))
theorem gqsp_polyPNValid_le_b353 {deg : ℕ} {pn : PolyPN} {f : ℕ → ℝ} (h : PolyPNValid deg pn f) :
    pn.pos ≤ pack768 (List.replicate (deg + 1) 1) * 2 ^ 353 ∧ pn.neg ≤ pack768 (List.replicate (deg
    + 1) 1) * 2 ^
    353 := by
  rcases h with ⟨vp, vn, hvp_len, hvn_len, hvp_lt, hvn_lt, hpos, hneg, _⟩
  have hsh : pack768 (List.replicate (deg + 1) 1) * 2 ^ 353 =
      pack768 (List.replicate (deg + 1) (2 ^ 353)) :=
    (@Nat.mul_eq _ _).symm.trans (sched_pack768_rep_mul (deg + 1) (2 ^ 353))
  rw [hsh, hpos, hneg]
  refine ⟨?_, ?_⟩
  · have hf2 := gqsp_forall2_le_rep vp (fun x hx => Nat.le_of_lt (hvp_lt x hx))
    rw [hvp_len] at hf2
    exact sched_pack768_mono vp _ hf2
  · have hf2 := gqsp_forall2_le_rep vn (fun x hx => Nat.le_of_lt (hvn_lt x hx))
    rw [hvn_len] at hf2
    exact sched_pack768_mono vn _ hf2
theorem gqsp_rep1_bounds : ∀ (n : ℕ),
    2 ^ (768 * n) ≤ pack768 (List.replicate (n + 1) 1) ∧
    pack768 (List.replicate (n + 1) 1) < 2 * 2 ^ (768 * n)
  | 0 => by
      simp only [Nat.mul_zero, Nat.pow_zero, List.replicate, sched_pack768_cons, sched_pack768_nil]
      decide
  | n + 1 => by
      rcases gqsp_rep1_bounds n with ⟨hlo, hhi⟩
      have hmul : 768 * (n + 1) = 768 + 768 * n := by omega
      rw [hmul, Nat.pow_add, List.replicate_succ, sched_pack768_cons, sched_shiftLeft_768_eq,
        sched_pow768_eq_pow]
      have h1 : 2 ^ 768 * 2 ^ (768 * n) ≤ 2 ^ 768 * pack768 (List.replicate (n + 1) 1) :=
        Nat.mul_le_mul_left (2 ^ 768) hlo
      have h2 : 2 ^ 768 * (pack768 (List.replicate (n + 1) 1) + 1) ≤ 2 ^ 768 *
          (2 * 2 ^ (768 * n)) := Nat.mul_le_mul_left (2 ^ 768) hhi
      have hp768 : 2 ≤ (2 : ℕ) ^ 768 := by norm_num
      omega
theorem gqsp_eight_rl_le_rb (ldeg rdeg : ℕ) :
    let lrep1 := pack768 (List.replicate (ldeg + 1) 1)
    let rrep1 := pack768 (List.replicate (rdeg + 1) 1)
    let rep1 := pack768 (List.replicate (rdeg + ldeg + 1) 1)
    8 * ((rrep1 * 2 ^ 353) * (lrep1 * 2 ^ 353)) ≤ Nat.mul rep1 sched_bMid := by
  dsimp only
  rcases gqsp_rep1_bounds ldeg with ⟨_, hl_hi⟩
  rcases gqsp_rep1_bounds rdeg with ⟨_, hr_hi⟩
  rcases gqsp_rep1_bounds (rdeg + ldeg) with ⟨hrep_lo, _⟩
  rw [@Nat.mul_eq _ sched_bMid, sched_bMid_eq]
  have hprod : pack768 (List.replicate (rdeg + 1) 1) * pack768 (List.replicate (ldeg + 1) 1) ≤
      4 * 2 ^ (768 * (rdeg + ldeg)) := by
    refine Nat.le_of_lt ((Nat.mul_lt_mul_of_lt_of_lt hr_hi hl_hi).trans_eq ?_)
    rw [show 768 * (rdeg + ldeg) = 768 * rdeg + 768 * ldeg by omega, Nat.pow_add]
    ring
  calc 8 * ((pack768 (List.replicate (rdeg + 1) 1) * 2 ^ 353) * (pack768 (List.replicate (ldeg + 1)
    1) * 2 ^ 353))
    _ = 8 * ((pack768 (List.replicate (rdeg + 1) 1) * pack768 (List.replicate (ldeg + 1) 1)) * (2 ^
      353 * 2 ^ 353)) := by ring
    _ ≤ 8 * ((4 * 2 ^ (768 * (rdeg + ldeg))) * (2 ^ 353 * 2 ^ 353)) := by gcongr
    _ = (8 * (4 * (2 ^ 353 * 2 ^ 353))) * 2 ^ (768 * (rdeg + ldeg)) := by ring
    _ ≤ 2 ^ 736 * 2 ^ (768 * (rdeg + ldeg)) := Nat.mul_le_mul_right _ (by norm_num)
    _ ≤ pack768 (List.replicate (rdeg + ldeg + 1) 1) * 2 ^ 736 := by
          rw [Nat.mul_comm _ (2 ^ 736)]
          exact Nat.mul_le_mul_left _ hrep_lo
theorem gqsp_zipWith_reverse (fn : ℕ → ℕ → ℕ) :
    ∀ (xs ys : List ℕ), xs.length = ys.length →
      (List.zipWith fn xs ys).reverse = List.zipWith fn xs.reverse ys.reverse
  | [], [], _ => rfl
  | x :: xt, y :: yt, hlen => by
      have ih := gqsp_zipWith_reverse fn xt yt (Nat.succ.inj hlen)
      have hlr : xt.reverse.length = yt.reverse.length := by
        rw [List.length_reverse, List.length_reverse]
        exact Nat.succ.inj hlen
      simp only [List.zipWith_cons_cons, List.reverse_cons, ih]
      rw [List.zipWith_append hlr]; rfl
theorem gqsp_bias_sub_f2 : ∀ (n : ℕ) (vp vn : List ℕ),
    vp.length = n → vn.length = n → (∀ y ∈ vn, y < 2 ^ 353) →
    List.Forall₂ (· ≤ ·) vn (List.zipWith Nat.add vp (List.replicate n (2 ^ 353)))
  | 0, [], [], _, _, _ => List.Forall₂.nil
  | n + 1, u :: ut, v :: vt, hu, hv, hvs =>
      List.Forall₂.cons
        (by
          simp only [Nat.add_eq]
          exact Nat.le_trans (Nat.le_of_lt (hvs v List.mem_cons_self)) (Nat.le_add_left _ _))
        (gqsp_bias_sub_f2 n ut vt (Nat.succ.inj hu) (Nat.succ.inj hv)
          (fun a ha => hvs a (List.mem_cons_of_mem v ha)))
theorem gqsp_bias_mem_lt : ∀ (n : ℕ) (vp vn : List ℕ),
    vp.length = n → vn.length = n → (∀ x ∈ vp, x < 2 ^ 353) →
    ∀ w ∈ List.zipWith Nat.sub (List.zipWith Nat.add vp (List.replicate n (2 ^ 353))) vn,
      w < 2 ^ 768
  | 0, [], [], _, _, _, _, hw => nomatch hw
  | n + 1, u :: ut, v :: vt, hu, hv, hus, w, hw => by
      have hp : (2 : ℕ) ^ 353 + 2 ^ 353 ≤ 2 ^ 768 := by norm_num
      simp only [List.replicate_succ, List.zipWith_cons_cons, List.mem_cons] at hw
      rcases hw with rfl | hmem
      · simp only [Nat.sub_eq, Nat.add_eq]
        have hu_lt := hus u List.mem_cons_self
        omega
      · exact gqsp_bias_mem_lt n ut vt (Nat.succ.inj hu) (Nat.succ.inj hv)
          (fun a ha => hus a (List.mem_cons_of_mem u ha)) w hmem
set_option maxHeartbeats 800000 in
-- SWAR bit-reversal recurrence verification
theorem gqsp_srev_bias_eq_of_valid (c salt d deg : ℕ) (pn : PolyPN) (f : ℕ → ℝ)
    (hpn : PolyPNValid deg pn f) (hd : deg + 1 ≤ 2 ^ d) :
    let rrep1 := pack768 (List.replicate (deg + 1) 1)
    let rb353 := Nat.shiftLeft rrep1 353
    gqsp_fastRevSwarSalt c salt d (Nat.add deg 1)
      (Nat.sub (Nat.add pn.pos rb353) pn.neg) =
      (revBin768 d (deg + 1) pn.pos + rrep1 * 2 ^ 353) - revBin768 d (deg + 1) pn.neg := by
  dsimp only
  rcases hpn with ⟨vp, vn, hvp_len, hvn_len, hvp_lt, hvn_lt, hpos, hneg, _⟩
  have h353_768 : (2 : ℕ) ^ 353 < 2 ^ 768 := by norm_num
  have hbp : ∀ x ∈ vp, x < 2 ^ 768 := fun x hx => Nat.lt_trans (hvp_lt x hx) h353_768
  have hbn : ∀ x ∈ vn, x < 2 ^ 768 := fun x hx => Nat.lt_trans (hvn_lt x hx) h353_768
  have hrb_mul : pack768 (List.replicate (deg + 1) 1) * 2 ^ 353 =
      pack768 (List.replicate (deg + 1) (2 ^ 353)) :=
    (@Nat.mul_eq _ _).symm.trans (sched_pack768_rep_mul (deg + 1) (2 ^ 353))
  have hrb_pack : Nat.shiftLeft (pack768 (List.replicate (deg + 1) 1)) 353 = pack768
      (List.replicate (deg + 1) (2 ^ 353)) := (gqsp_nat_shl_eq _ 353).trans hrb_mul
  let ws := List.zipWith Nat.sub (List.zipWith Nat.add vp (List.replicate (deg + 1) (2 ^ 353))) vn
  have hws_pack : Nat.sub (Nat.add pn.pos (Nat.shiftLeft (pack768 (List.replicate (deg + 1) 1))
      353)) pn.neg =
      pack768 ws := by
    rw [hpos, hneg, hrb_pack, Nat.add_eq,
      ← sched_pack768_zipAdd vp _ (by rw [hvp_len, List.length_replicate]),
      Nat.sub_eq, ← sched_pack768_sub _ _ (gqsp_bias_sub_f2 (deg + 1) vp vn hvp_len hvn_len hvn_lt)]
  have hws_len : ws.length = deg + 1 := by
    simp only [ws, List.length_zipWith, List.length_replicate, hvp_len, hvn_len, sched_min_self_nat]
  have hws_lt : ∀ w ∈ ws, w < 2 ^ 768 :=
    gqsp_bias_mem_lt (deg + 1) vp vn hvp_len hvn_len hvp_lt
  rw [hws_pack, @Nat.add_eq deg 1, gqsp_fastRevSwarSalt_spec c salt d (deg + 1) ws hws_len hws_lt]
  have hadd_len : (List.zipWith Nat.add vp (List.replicate (deg + 1) (2 ^ 353))).length = vn.length
    := by
    simp only [List.length_zipWith, List.length_replicate, hvp_len, hvn_len, sched_min_self_nat]
  have hrep_len : vp.length = (List.replicate (deg + 1) (2 ^ 353)).length := by
    rw [hvp_len, List.length_replicate]
  have hws_rev : ws.reverse =
      List.zipWith Nat.sub (List.zipWith Nat.add vp.reverse (List.replicate (deg + 1) (2 ^ 353)))
        vn.reverse := by
    dsimp only [ws]
    rw [gqsp_zipWith_reverse Nat.sub _ vn hadd_len, gqsp_zipWith_reverse Nat.add vp _ hrep_len,
      List.reverse_replicate]
  have hvp_rlen : vp.reverse.length = deg + 1 := by rw [List.length_reverse, hvp_len]
  have hvn_rlen : vn.reverse.length = deg + 1 := by rw [List.length_reverse, hvn_len]
  have hvn_rlt : ∀ y ∈ vn.reverse, y < 2 ^ 353 := fun y hy => hvn_lt y (List.mem_reverse.mp hy)
  rw [hws_rev, sched_pack768_sub _ _ (gqsp_bias_sub_f2 (deg + 1) vp.reverse vn.reverse hvp_rlen
    hvn_rlen hvn_rlt),
    sched_pack768_zipAdd vp.reverse _ (by rw [hvp_rlen, List.length_replicate]),
    ← hrb_mul, hpos, hneg,
    revBin768_spec d (deg + 1) vp hd hvp_len hbp,
    revBin768_spec d (deg + 1) vn hd hvn_len hbn]
theorem gqsp_neg_bias_eq {ap an R : ℕ} (hap : ap ≤ R) (han : an ≤ R) : Nat.sub (2 * R) ((ap + R) -
    an) = (an + R) - ap := by
  rw [Nat.sub_eq]; omega
theorem gqsp_sub_eq_sub_of_add {A B C D : ℕ} (h1 : B ≤ A) (h2 : A + D = C + B) :
    A - B = C - D := by omega
inductive gqsp_Pair2 where
  | empty : gqsp_Pair2
  | pair (s pos neg : ℕ) : gqsp_Pair2
noncomputable def gqsp_mkPairPN1 (s w_neg pos : ℕ) : gqsp_Pair2 :=
  @Nat.casesOn (fun _ => gqsp_Pair2) (Nat.add 1 (sched_idSalt (Nat.add 1 s) w_neg))
    gqsp_Pair2.empty (gqsp_Pair2.pair s pos)
noncomputable def gqsp_mkPairPN (s w_pos w_neg : ℕ) : gqsp_Pair2 :=
  @Nat.casesOn (fun _ => gqsp_Pair2) (Nat.add 1 (sched_idSalt s w_pos))
    gqsp_Pair2.empty (gqsp_mkPairPN1 s w_neg)
theorem gqsp_mkPairPN_eq (s w_pos w_neg : ℕ) : gqsp_mkPairPN s w_pos w_neg = gqsp_Pair2.pair s
    w_pos w_neg := by
  simp only [gqsp_mkPairPN, gqsp_mkPairPN1, Nat.add_eq, Nat.one_add, sched_idSalt_eq]
noncomputable def gqsp_withPNOpt {α : Type} (p : gqsp_Pair2) (f : ℕ → ℕ → Option α) : Option α :=
  @gqsp_Pair2.casesOn (fun _ => Option α) p none (fun _ a b => f a b)
theorem gqsp_withPNOpt_mkPairPN {α : Type} (s a b : ℕ) (f : ℕ → ℕ → Option α) : gqsp_withPNOpt
    (gqsp_mkPairPN s a b) f = f a b := by
  rw [gqsp_mkPairPN_eq]; rfl
inductive gqsp_Quad4 where
  | empty : gqsp_Quad4
  | quad (s a b c d : ℕ) : gqsp_Quad4
noncomputable def gqsp_mkQ4_2 (s d a b c : ℕ) : gqsp_Quad4 :=
  @Nat.casesOn (fun _ => gqsp_Quad4) (Nat.add 1 (sched_idSalt (Nat.add 3 s) d))
    gqsp_Quad4.empty (gqsp_Quad4.quad s a b c)
noncomputable def gqsp_mkQ4_1 (s c d a b : ℕ) : gqsp_Quad4 :=
  @Nat.casesOn (fun _ => gqsp_Quad4) (Nat.add 1 (sched_idSalt (Nat.add 2 s) c))
    gqsp_Quad4.empty (gqsp_mkQ4_2 s d a b)
noncomputable def gqsp_mkQ4_0 (s b c d a : ℕ) : gqsp_Quad4 :=
  @Nat.casesOn (fun _ => gqsp_Quad4) (Nat.add 1 (sched_idSalt (Nat.add 1 s) b))
    gqsp_Quad4.empty (gqsp_mkQ4_1 s c d a)
noncomputable def gqsp_forceQ4 (s a b c d : ℕ) : gqsp_Quad4 :=
  @Nat.casesOn (fun _ => gqsp_Quad4) (Nat.add 1 (sched_idSalt s a))
    gqsp_Quad4.empty (gqsp_mkQ4_0 s b c d)
theorem gqsp_forceQ4_eq (s a b c d : ℕ) : gqsp_forceQ4 s a b c d = gqsp_Quad4.quad s a b c d :=
    by
  simp only [gqsp_forceQ4, gqsp_mkQ4_0, gqsp_mkQ4_1, gqsp_mkQ4_2, Nat.add_eq, Nat.one_add,
    sched_idSalt_eq]
noncomputable def gqsp_withQ4 {α : Type} (q : gqsp_Quad4) (f : ℕ → ℕ → ℕ → ℕ → Option α) : Option
    α :=
  @gqsp_Quad4.casesOn (fun _ => Option α) q none (fun _ a b c d => f a b c d)
theorem gqsp_withQ4_forceQ4 {α : Type} (s a b c d : ℕ) (f : ℕ → ℕ → ℕ → ℕ → Option α) :
    gqsp_withQ4 (gqsp_forceQ4 s a b c d) f = f a b c d := by
  rw [gqsp_forceQ4_eq]; rfl
noncomputable def gqsp_roundSplitZ (s rk rbq rm rc z_w : ℕ) : Option SaltedPN := sched_stfOpt
    s (sched_roundSplit768Step1 s rbq rm rc) (sched_shrLimb (Nat.land (sched_idSalt s z_w) rk))
theorem gqsp_roundSplitZ_eq_masks (s rb rk rbq rm rc u_pos u_neg z_w : ℕ) (hz : z_w = (u_pos + rb)
    - u_neg) : gqsp_roundSplitZ s rk rbq rm rc z_w = sched_roundSplit768Masks s rb rk rbq rm rc
    u_pos u_neg := by
  have hzw : z_w = Nat.sub (Nat.add u_pos rb) u_neg := hz
  rw [hzw]
  unfold gqsp_roundSplitZ sched_roundSplit768Masks
  simp only [sched_stfOpt_eq, sched_idSalt_eq]
noncomputable def gqsp_swarDepth (rdeg : ℕ) : ℕ := if Nat.ble rdeg 63 then 6 else if Nat.ble
    rdeg 255 then 8 else if Nat.ble rdeg 1023 then 10 else if Nat.ble rdeg 4095 then 12 else
    if Nat.ble rdeg 16383 then 14 else if Nat.ble rdeg 65535 then 16 else if Nat.ble rdeg
    131071 then 17 else if Nat.ble rdeg 262143 then 18 else 19
theorem gqsp_swarDepth_bounds (rdeg : ℕ) (h : rdeg ≤ 262144) : gqsp_swarDepth rdeg ≤ 19 ∧ rdeg + 1
    ≤ 2 ^ (gqsp_swarDepth rdeg) := by
  unfold gqsp_swarDepth
  have p6 : (64 : ℕ) = 2 ^ 6 := rfl
  have p8 : (256 : ℕ) = 2 ^ 8 := rfl
  have p10 : (1024 : ℕ) = 2 ^ 10 := rfl
  have p12 : (4096 : ℕ) = 2 ^ 12 := rfl
  have p14 : (16384 : ℕ) = 2 ^ 14 := rfl
  have p16 : (65536 : ℕ) = 2 ^ 16 := rfl
  have p17 : (131072 : ℕ) = 2 ^ 17 := rfl
  have p18 : (262144 : ℕ) = 2 ^ 18 := rfl
  have p19 : (524288 : ℕ) = 2 ^ 19 := rfl
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;>
    simp only [Nat.ble_eq] at * <;> omega
noncomputable def gqsp_pushMergedNodeC
    (ih : Option TreeNodeC → List TreeNodeC → Option (List TreeNodeC)) (a : List TreeNodeC)
    (xy : TreeNodeC) : Option (List TreeNodeC) := ih none (xy :: a)
end FastKernelHelpers
end GqspWronskian62592
end
end Gqsp0b_CatAndTree

end QuantumComputation.Specs.StoppingPowerSolution
end
