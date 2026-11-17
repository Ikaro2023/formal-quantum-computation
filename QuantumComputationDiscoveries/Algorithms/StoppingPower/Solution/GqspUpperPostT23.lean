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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.GqspSubShards01
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.GqspSubShards23
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.GqspSubShards45
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.GqspSubShards67

set_option linter.style.longLine false

/-!
# Split `t2` & `t3` Upper `8 → 4 → 2 → 1` Post-Root Bound (`GqspUpperPostT23_135598`)

Provides direct forward `512`-bit binary-tree lane unpacking (`m ≤ 9` inline) and `4`-step unrolled
zero-cache post-root loops (`gqsp_*`, fuel `70000`),
  then certifies `t3` (`qResid ≤ 5583037192 * shift0`).
-/

@[expose] public section
set_option compiler.extract_closed false
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

namespace GqspUpperPostT23_135598

section UpperPostT23
set_option maxRecDepth 6000000
set_option exponentiation.threshold 2048

open TFreeLaurentGQSP
open TFreeLaurentGQSPPresets.FastRecurrenceVerifier
open TFreeLaurentGQSPPresets.FastIntervalRecurrenceVerifier
open BidirectionalIntervalRecurrenceVerifier
open TwoAngleBiGqspVerifierBridge
open GqspWronskian62592
open GqspTreeBaseHelpers135598
open GqspTreeSubShards01_135598
open GqspTreeSubShards23_135598
open GqspTreeSubShards45_135598
open GqspTreeSubShards67_135598

/-- `512`-bit mask `2 ^ 512 - 1` for direct `shr 256` lane extraction. -/
def gqsp_mask512 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

/-- Forward `768`-bit lane `shr 256` peeler specification (`0` `DefinitionVal`s). -/
noncomputable def gqsp_peel1Fwd (n0 : ℕ) : ℕ → List ℕ → List ℕ := @Nat.rec
    (fun _ ↦ ℕ → List ℕ → List ℕ) (fun _ acc ↦ acc) (fun _ ih w acc ↦ Nat.shiftRight (Nat.land
    w gqsp_mask768) 256 :: ih (Nat.shiftRight w 768) acc) n0

private theorem gqsp_shr_eq_div_pow' (w sh : ℕ) : Nat.shiftRight w sh = w / 2 ^ sh := by
  rw [Nat.shiftRight_eq, Nat.shiftRight_eq_div_pow]

private theorem gqsp_shl_eq_mul_pow' (w sh : ℕ) : Nat.shiftLeft w sh = w * 2 ^ sh := by
  have h : w.shiftLeft sh = w <<< sh := rfl
  rw [h, Nat.shiftLeft_eq]

private theorem gqsp_shr_add_eq' (w a b : ℕ) :
    Nat.shiftRight w (a + b) = Nat.shiftRight (Nat.shiftRight w a) b := by
  simp only [gqsp_shr_eq_div_pow', Nat.pow_add, Nat.div_div_eq_div_mul]

private theorem gqsp_land_mask768_eq_mod' (u : ℕ) : Nat.land u gqsp_mask768 = u % 2 ^ 768 := by
  rw [Nat.land_eq, show gqsp_mask768 = 2 ^ 768 - 1 from rfl]
  exact Nat.and_two_pow_sub_one_eq_mod u 768

private theorem gqsp_sub_shl_shr_eq_mod' (w sh : ℕ) :
    Nat.sub w (Nat.shiftLeft (Nat.shiftRight w sh) sh) = w % 2 ^ sh := by
  rw [gqsp_shr_eq_div_pow', gqsp_shl_eq_mul_pow', Nat.sub_eq]
  have hdm := Nat.div_add_mod w (2 ^ sh)
  have hmul : (w / 2 ^ sh) * 2 ^ sh = 2 ^ sh * (w / 2 ^ sh) := Nat.mul_comm _ _
  omega

private theorem gqsp_add_div2_sub' (m : ℕ) : Nat.div m 2 + Nat.sub m (Nat.div m 2) = m := by
  have hd : m.div 2 = m / 2 := rfl
  rw [hd, Nat.sub_eq]
  omega

private theorem gqsp_shr256_land768_eq (u : ℕ) : Nat.shiftRight (Nat.land u gqsp_mask768)
    256 = Nat.land (Nat.shiftRight u 256) gqsp_mask512 := by
  have hm512 : Nat.land (Nat.shiftRight u 256) gqsp_mask512 = (Nat.shiftRight u 256) % 2 ^ 512 :=
    by
    rw [Nat.land_eq, show gqsp_mask512 = 2 ^ 512 - 1 from rfl]
    exact Nat.and_two_pow_sub_one_eq_mod _ 512
  rw [gqsp_land_mask768_eq_mod', hm512, gqsp_shr_eq_div_pow', gqsp_shr_eq_div_pow',
      show (2 : ℕ) ^ 768 = 2 ^ 256 * 2 ^ 512 from rfl]
  exact Nat.mod_mul_right_div_self u (2 ^ 256) (2 ^ 512)

private theorem gqsp_peel1Fwd_succ (r w : ℕ) (acc : List ℕ) : gqsp_peel1Fwd (r + 1) w acc =
    Nat.shiftRight (Nat.land w gqsp_mask768) 256 :: gqsp_peel1Fwd r (Nat.shiftRight w 768)
    acc := rfl

private theorem gqsp_rev_peel1_eq :
    ∀ (n w : ℕ) (racc acc : List ℕ),
      gqsp_zwRevNatTR (gqsp_zwPeel1Shr256Aux n w racc) acc =
        gqsp_zwRevNatTR racc (gqsp_peel1Fwd n w acc)
  | 0, _, _, _ => rfl
  | n + 1, w, racc, acc => by
      rw [gqsp_zwPeel1Shr256Aux_succ, gqsp_rev_peel1_eq n]
      rfl

private theorem gqsp_peel1Fwd_mod :
    ∀ (h w : ℕ) (acc : List ℕ),
      gqsp_peel1Fwd h (w % 2 ^ (768 * h)) acc = gqsp_peel1Fwd h w acc
  | 0, _, _ => rfl
  | h + 1, w, acc => by
      rw [gqsp_peel1Fwd_succ, gqsp_peel1Fwd_succ]
      have hpow : 2 ^ (768 * (h + 1)) = 2 ^ 768 * 2 ^ (768 * h) := by
        rw [← Nat.pow_add]; congr 1; omega
      have hland : Nat.land (w % 2 ^ (768 * (h + 1))) gqsp_mask768 = Nat.land w gqsp_mask768 := by
        rw [gqsp_land_mask768_eq_mod', gqsp_land_mask768_eq_mod', hpow]
        exact Nat.mod_mod_of_dvd w (Nat.dvd_mul_right (2 ^ 768) (2 ^ (768 * h)))
      have hshr : Nat.shiftRight (w % 2 ^ (768 * (h + 1))) 768 =
          (Nat.shiftRight w 768) % 2 ^ (768 * h) := by
        rw [gqsp_shr_eq_div_pow', gqsp_shr_eq_div_pow', hpow]
        exact Nat.mod_mul_right_div_self w (2 ^ 768) (2 ^ (768 * h))
      rw [hland, hshr, gqsp_peel1Fwd_mod h (Nat.shiftRight w 768) acc]

private theorem gqsp_peel1Fwd_add :
    ∀ (h h_hi w : ℕ) (acc : List ℕ),
      gqsp_peel1Fwd (h + h_hi) w acc =
        gqsp_peel1Fwd h w (gqsp_peel1Fwd h_hi (Nat.shiftRight w (768 * h)) acc)
  | 0, _, w, _ => by
      have h0 : Nat.shiftRight w 0 = w := by
        simp only [gqsp_shr_eq_div_pow', Nat.pow_zero, Nat.div_one]
      rw [Nat.zero_add, Nat.mul_zero, h0]
      rfl
  | h + 1, h_hi, w, acc => by
      have hadd : h + 1 + h_hi = (h + h_hi) + 1 := by omega
      have hsh : 768 * (h + 1) = 768 + 768 * h := by omega
      rw [hadd, gqsp_peel1Fwd_succ, gqsp_peel1Fwd_succ, hsh, gqsp_shr_add_eq',
          gqsp_peel1Fwd_add h h_hi (Nat.shiftRight w 768) acc]

private noncomputable def gqsp_peelChunksFwd : List (ℕ × ℕ) → List ℕ → List ℕ
  | [], acc => acc
  | (n, w) :: cs, acc => gqsp_peel1Fwd n w (gqsp_peelChunksFwd cs acc)

private theorem gqsp_zwPeelWords64RevTR_cons (p : ℕ × ℕ) (cs : List (ℕ × ℕ)) (racc : List ℕ)
    : gqsp_zwPeelWords64RevTR (p :: cs) racc = gqsp_zwPeelWords64RevTR cs
    (gqsp_zwPeel1Shr256Aux p.1 p.2 racc) := rfl

private theorem gqsp_rev_peelWords64_eq :
    ∀ (cs : List (ℕ × ℕ)) (racc acc : List ℕ),
      gqsp_zwRevNatTR (gqsp_zwPeelWords64RevTR cs racc) acc =
        gqsp_zwRevNatTR racc (gqsp_peelChunksFwd cs acc)
  | [], _, _ => rfl
  | (n, w) :: cs, racc, acc => by
      rw [gqsp_zwPeelWords64RevTR_cons, gqsp_rev_peelWords64_eq cs, gqsp_rev_peel1_eq]
      rfl

private theorem gqsp_peelChunksFwd_splitWords64 (k : ℕ) : ∀ (n w : ℕ) (cs : List (ℕ × ℕ))
    (acc : List ℕ), gqsp_peelChunksFwd (gqsp_zwSplitWords64Aux k n w cs) acc =
    gqsp_peel1Fwd n w (gqsp_peelChunksFwd cs acc) := by
  unfold gqsp_zwSplitWords64Aux
  induction k with
  | zero =>
      intro n w cs acc
      rw [← Nat.zero_eq]
      dsimp only
      rw [gqsp_zwForce_eq]
      rfl
  | succ k ih =>
      intro n w cs acc
      dsimp only
      cases hb : Nat.ble n 64
      · dsimp only
        rw [gqsp_zwForce_eq, gqsp_zwForce_eq, ih, ih]
        have hm1 : Nat.mul 768 (Nat.div n 2) = 768 * Nat.div n 2 := rfl
        rw [gqsp_sub_shl_shr_eq_mod', hm1, gqsp_peel1Fwd_mod, ← gqsp_peel1Fwd_add]
        simp only [gqsp_add_div2_sub']
      · dsimp only
        rw [gqsp_zwForce_eq]
        rfl

private theorem gqsp_peel7_eq (w : ℕ) (acc : List ℕ) : Nat.land (Nat.shiftRight w 256)
    gqsp_mask512 :: Nat.land (Nat.shiftRight w 1024) gqsp_mask512 :: Nat.land
    (Nat.shiftRight w 1792) gqsp_mask512 :: Nat.land (Nat.shiftRight w 2560) gqsp_mask512 ::
    Nat.land (Nat.shiftRight w 3328) gqsp_mask512 :: Nat.land (Nat.shiftRight w 4096)
    gqsp_mask512 :: Nat.land (Nat.shiftRight w 4864) gqsp_mask512 :: acc = gqsp_peel1Fwd 7
    w acc := by
  rw [gqsp_peel1Fwd_succ, gqsp_peel1Fwd_succ, gqsp_peel1Fwd_succ, gqsp_peel1Fwd_succ,
      gqsp_peel1Fwd_succ, gqsp_peel1Fwd_succ, gqsp_peel1Fwd_succ]
  simp only [gqsp_shr256_land768_eq, ← gqsp_shr_add_eq']
  rfl

private theorem gqsp_peel8_eq (w : ℕ) (acc : List ℕ) : Nat.land (Nat.shiftRight w 256)
    gqsp_mask512 :: Nat.land (Nat.shiftRight w 1024) gqsp_mask512 :: Nat.land
    (Nat.shiftRight w 1792) gqsp_mask512 :: Nat.land (Nat.shiftRight w 2560) gqsp_mask512 ::
    Nat.land (Nat.shiftRight w 3328) gqsp_mask512 :: Nat.land (Nat.shiftRight w 4096)
    gqsp_mask512 :: Nat.land (Nat.shiftRight w 4864) gqsp_mask512 :: Nat.land
    (Nat.shiftRight w 5632) gqsp_mask512 :: acc = gqsp_peel1Fwd 8 w acc := by
  rw [gqsp_peel1Fwd_succ, gqsp_peel1Fwd_succ, gqsp_peel1Fwd_succ, gqsp_peel1Fwd_succ,
      gqsp_peel1Fwd_succ, gqsp_peel1Fwd_succ, gqsp_peel1Fwd_succ, gqsp_peel1Fwd_succ]
  simp only [gqsp_shr256_land768_eq, ← gqsp_shr_add_eq']
  rfl

private theorem gqsp_peel9_eq (w : ℕ) (acc : List ℕ) : Nat.land (Nat.shiftRight w 256)
    gqsp_mask512 :: Nat.land (Nat.shiftRight w 1024) gqsp_mask512 :: Nat.land
    (Nat.shiftRight w 1792) gqsp_mask512 :: Nat.land (Nat.shiftRight w 2560) gqsp_mask512 ::
    Nat.land (Nat.shiftRight w 3328) gqsp_mask512 :: Nat.land (Nat.shiftRight w 4096)
    gqsp_mask512 :: Nat.land (Nat.shiftRight w 4864) gqsp_mask512 :: Nat.land
    (Nat.shiftRight w 5632) gqsp_mask512 :: Nat.land (Nat.shiftRight w 6400) gqsp_mask512 ::
    acc = gqsp_peel1Fwd 9 w acc := by
  rw [gqsp_peel1Fwd_succ, gqsp_peel1Fwd_succ, gqsp_peel1Fwd_succ, gqsp_peel1Fwd_succ,
      gqsp_peel1Fwd_succ, gqsp_peel1Fwd_succ, gqsp_peel1Fwd_succ, gqsp_peel1Fwd_succ,
      gqsp_peel1Fwd_succ]
  simp only [gqsp_shr256_land768_eq, ← gqsp_shr_add_eq']
  rfl

/-- Binary-tree direct forward `shr 256` lane unpacker down to `m ≤ 9`
(`0` leaf recursors / `DefinitionVal`s). -/
noncomputable def gqsp_splitPeelBin (m512 k : ℕ) : ℕ → ℕ → List ℕ → List ℕ :=
  @Nat.rec (fun _ ↦ ℕ → ℕ → List ℕ → List ℕ)
    gqsp_peel1Fwd
    (fun _ ih m w acc ↦
      @Bool.rec (fun _ ↦ List ℕ)
        (let h := Nat.div m 2
         let sh := Nat.mul 768 h
         let w_hi := Nat.shiftRight w sh
         let w_lo := Nat.sub w (Nat.shiftLeft w_hi sh)
         ih h w_lo (ih (Nat.sub m h) w_hi acc))
        (@Bool.rec (fun _ ↦ List ℕ)
          (@Bool.rec (fun _ ↦ List ℕ)
            (@Bool.rec (fun _ ↦ List ℕ)
              (gqsp_peel1Fwd m w acc)
              (Nat.land (Nat.shiftRight w 256) m512 ::
               Nat.land (Nat.shiftRight w 1024) m512 ::
               Nat.land (Nat.shiftRight w 1792) m512 ::
               Nat.land (Nat.shiftRight w 2560) m512 ::
               Nat.land (Nat.shiftRight w 3328) m512 ::
               Nat.land (Nat.shiftRight w 4096) m512 ::
               Nat.land (Nat.shiftRight w 4864) m512 :: acc)
              (Nat.beq m 7))
            (Nat.land (Nat.shiftRight w 256) m512 ::
             Nat.land (Nat.shiftRight w 1024) m512 ::
             Nat.land (Nat.shiftRight w 1792) m512 ::
             Nat.land (Nat.shiftRight w 2560) m512 ::
             Nat.land (Nat.shiftRight w 3328) m512 ::
             Nat.land (Nat.shiftRight w 4096) m512 ::
             Nat.land (Nat.shiftRight w 4864) m512 ::
             Nat.land (Nat.shiftRight w 5632) m512 :: acc)
            (Nat.beq m 8))
          (Nat.land (Nat.shiftRight w 256) m512 ::
           Nat.land (Nat.shiftRight w 1024) m512 ::
           Nat.land (Nat.shiftRight w 1792) m512 ::
           Nat.land (Nat.shiftRight w 2560) m512 ::
           Nat.land (Nat.shiftRight w 3328) m512 ::
           Nat.land (Nat.shiftRight w 4096) m512 ::
           Nat.land (Nat.shiftRight w 4864) m512 ::
           Nat.land (Nat.shiftRight w 5632) m512 ::
           Nat.land (Nat.shiftRight w 6400) m512 :: acc)
          (Nat.beq m 9))
        (Nat.ble m 9))
    k

private theorem gqsp_splitPeelBin_eq (k : ℕ) : ∀ (m w : ℕ) (acc : List ℕ), gqsp_splitPeelBin
    gqsp_mask512 k m w acc = gqsp_peel1Fwd m w acc := by
  unfold gqsp_splitPeelBin
  induction k with
  | zero =>
      intro _ _ _
      rfl
  | succ k ih =>
      intro m w acc
      dsimp only
      cases hb : Nat.ble m 9
      · dsimp only
        rw [ih, ih]
        have hm1 : Nat.mul 768 (Nat.div m 2) = 768 * Nat.div m 2 := rfl
        rw [gqsp_sub_shl_shr_eq_mod', hm1, gqsp_peel1Fwd_mod, ← gqsp_peel1Fwd_add]
        simp only [gqsp_add_div2_sub']
      · dsimp only
        cases h9 : Nat.beq m 9
        · dsimp only
          cases h8 : Nat.beq m 8
          · dsimp only
            cases h7 : Nat.beq m 7
            · rfl
            · dsimp only
              rw [Nat.beq_eq.mp h7]
              exact gqsp_peel7_eq w acc
          · dsimp only
            rw [Nat.beq_eq.mp h8]
            exact gqsp_peel8_eq w acc
        · dsimp only
          rw [Nat.beq_eq.mp h9]
          exact gqsp_peel9_eq w acc

/-- Direct forward binary-tree 2-term real dot-product + unpacker
(`0` reversal / chunk-list pass). -/
noncomputable def gqsp_finishRootVec2RealFastAux
    (d n_lanes rep_bcomb : ℕ) (c1 x1 c3 x3 : PolyPN) : List ℕ :=
  @PolyPN.rec (fun _ ↦ List ℕ) (fun c1p c1n ↦
    @PolyPN.rec (fun _ ↦ List ℕ) (fun x1p x1n ↦
      @PolyPN.rec (fun _ ↦ List ℕ) (fun c3p c3n ↦
        @PolyPN.rec (fun _ ↦ List ℕ) (fun x3p x3n ↦
          let up0 := Nat.add (Nat.add (Nat.mul c1p x1p) (Nat.mul c1n x1n))
                             (Nat.add (Nat.mul c3p x3p) (Nat.mul c3n x3n))
          let un0 := Nat.add (Nat.add (Nat.mul c1p x1n) (Nat.mul c1n x1p))
                             (Nat.add (Nat.mul c3p x3n) (Nat.mul c3n x3p))
          @Nat.rec (fun _ ↦ List ℕ) [] (fun m512 _ ↦
            @Nat.rec (fun _ ↦ List ℕ) [] (fun up _ ↦
              @Nat.rec (fun _ ↦ List ℕ) [] (fun un _ ↦
                @Nat.rec (fun _ ↦ List ℕ) [] (fun w _ ↦
                  gqsp_splitPeelBin m512 d n_lanes w [])
                  (Nat.add 1 (Nat.sub (Nat.add up rep_bcomb) un)))
                (Nat.add 1 un0))
              (Nat.add 1 up0))
            (Nat.add 1 gqsp_mask512))
          x3) c3) x1) c1

theorem gqsp_finishRootVec2RealFast_eq (d n_lanes rep_bcomb : ℕ) (c1 x1 c3 x3 : PolyPN) :
    gqsp_finishRootVec2RealFastAux d n_lanes rep_bcomb c1 x1 c3 x3 = gqsp_zwFinishRootVec2Real
    d n_lanes rep_bcomb c1 x1 c3 x3 := by
  rw [gqsp_zwFinishRootVec2Real_eq 0]
  rcases c1 with ⟨c1p, c1n⟩
  rcases x1 with ⟨x1p, x1n⟩
  rcases c3 with ⟨c3p, c3n⟩
  rcases x3 with ⟨x3p, x3n⟩
  unfold gqsp_finishRootVec2RealFastAux gqsp_finishRootVec2RealFast mulAdd2Pos mulAdd2Neg
  dsimp only
  simp only [gqsp_zwForce_eq, sched_stfList_eq, gqsp_splitPeelBin_eq]
  rw [← gqsp_zwSunpackShr256Chunked_eq]
  unfold gqsp_zwSunpackShr256Chunked
  rw [gqsp_zwForce_eq, gqsp_zwForce_eq, ← gqsp_zwSplitWords64Aux_eq (Nat.sub d 6) _ n_lanes _ [],
      gqsp_rev_peelWords64_eq, gqsp_peelChunksFwd_splitWords64]
  rfl

/-- 4-step unrolled zero-cache `List ℕ` reversal. -/
noncomputable def gqsp_revNat4 (fuel : ℕ) : List ℕ → List ℕ → List ℕ := @Nat.rec
    (fun _ ↦ List ℕ → List ℕ → List ℕ) gqsp_zwRevNatTR (fun _ ih xs acc ↦ @List.rec ℕ (fun _
    ↦ List ℕ) acc (fun x0 r1 _ ↦ @List.rec ℕ (fun _ ↦ List ℕ) (x0 :: acc) (fun x1 r2 _ ↦
    @List.rec ℕ (fun _ ↦ List ℕ) (x1 :: x0 :: acc) (fun x2 r3 _ ↦ @List.rec ℕ (fun _ ↦ List ℕ)
    (x2 :: x1 :: x0 :: acc) (fun x3 r4 _ ↦ ih r4 (x3 :: x2 :: x1 :: x0 :: acc)) r3) r2) r1)
    xs) fuel

theorem gqsp_revNat4_eq :
    ∀ (fuel : ℕ) (xs acc : List ℕ), gqsp_revNat4 fuel xs acc = gqsp_zwRevNatTR xs acc
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | _ + 1, [_], _ => rfl
  | _ + 1, [_, _], _ => rfl
  | _ + 1, [_, _, _], _ => rfl
  | fuel + 1, x0 :: x1 :: x2 :: x3 :: r4, acc =>
      gqsp_revNat4_eq fuel r4 (x3 :: x2 :: x1 :: x0 :: acc)

private theorem gqsp_zwSplitPRev_cons_succ (B m p : ℕ) (ps neg_acc : List ℕ) :
    gqsp_zwSplitPRev B (m + 1) (p :: ps) neg_acc = gqsp_zwSplitPRev B m ps (p :: neg_acc) :=
  rfl

private theorem gqsp_zwQResid_cons (B B2 R_final ph qh : ℕ) (t : List PQPair) (q_prev acc : ℕ) :
    gqsp_zwQResidHadamard B B2 R_final (⟨ph, qh⟩ :: t) q_prev acc =
      let q_cur := Nat.shiftRight (Nat.add ph (Nat.sub B2 q_prev)) 1
      let diff := Nat.add (Nat.sub q_cur B) (Nat.sub B q_cur)
      gqsp_zwQResidHadamard B B2 R_final t qh (Nat.add acc (Nat.add diff R_final)) := by
  dsimp only [gqsp_zwQResidHadamard]
  rw [gqsp_zwForce_eq]

private theorem gqsp_zwAsymDefect_cons_true (B B2 two_Rf k' n0 p0 : ℕ) (nt pt : List ℕ) (acc : ℕ) :
    gqsp_zwAsymDefectLoop B B2 two_Rf (k' + 1) true (n0 :: nt) (p0 :: pt) acc =
      let pp := Nat.sub B2 p0
      let diff := Nat.add (Nat.sub pp n0) (Nat.sub n0 pp)
      gqsp_zwAsymDefectLoop B B2 two_Rf k' false nt pt (Nat.add acc (Nat.add diff two_Rf)) := by
  dsimp only [gqsp_zwAsymDefectLoop]
  rw [gqsp_zwForce_eq]

private theorem gqsp_zwAsymDefect_cons_false (B B2 two_Rf k' n0 p0 : ℕ) (nt pt : List ℕ) (acc : ℕ)
    :
    gqsp_zwAsymDefectLoop B B2 two_Rf (k' + 1) false (n0 :: nt) (p0 :: pt) acc =
      let diff := Nat.add (Nat.sub p0 n0) (Nat.sub n0 p0)
      gqsp_zwAsymDefectLoop B B2 two_Rf k' true nt pt (Nat.add acc (Nat.add diff two_Rf)) := by
  dsimp only [gqsp_zwAsymDefectLoop]
  rw [gqsp_zwForce_eq]

/-- 4-step unrolled `.p`-only asymmetry defect auxiliary loop (`0` parity/headD/tail recursors). -/
noncomputable def gqsp_asymDefect4Aux (B B2 two_Rf rem q : ℕ) : List ℕ → List ℕ → ℕ → ℕ :=
  @Nat.rec (fun _ ↦ List ℕ → List ℕ → ℕ → ℕ)
    (gqsp_zwAsymDefectLoop B B2 two_Rf rem true)
    (fun q' ih neg pos acc ↦
      let fb := gqsp_zwAsymDefectLoop B B2 two_Rf (4 * (q' + 1) + rem) true neg pos acc
      @List.rec ℕ (fun _ ↦ ℕ) fb (fun n0 nr1 _ ↦
        @List.rec ℕ (fun _ ↦ ℕ) fb (fun n1 nr2 _ ↦
          @List.rec ℕ (fun _ ↦ ℕ) fb (fun n2 nr3 _ ↦
            @List.rec ℕ (fun _ ↦ ℕ) fb (fun n3 nr4 _ ↦
              @List.rec ℕ (fun _ ↦ ℕ) fb (fun p0 pr1 _ ↦
                @List.rec ℕ (fun _ ↦ ℕ) fb (fun p1 pr2 _ ↦
                  @List.rec ℕ (fun _ ↦ ℕ) fb (fun p2 pr3 _ ↦
                    @List.rec ℕ (fun _ ↦ ℕ) fb (fun p3 pr4 _ ↦
                      let pp0 := Nat.sub B2 p0
                      let d0 := Nat.add (Nat.sub pp0 n0) (Nat.sub n0 pp0)
                      let a1 := Nat.add acc (Nat.add d0 two_Rf)
                      let d1 := Nat.add (Nat.sub p1 n1) (Nat.sub n1 p1)
                      let a2 := Nat.add a1 (Nat.add d1 two_Rf)
                      let pp2 := Nat.sub B2 p2
                      let d2 := Nat.add (Nat.sub pp2 n2) (Nat.sub n2 pp2)
                      let a3 := Nat.add a2 (Nat.add d2 two_Rf)
                      let d3 := Nat.add (Nat.sub p3 n3) (Nat.sub n3 p3)
                      let a4 := Nat.add a3 (Nat.add d3 two_Rf)
                      @Nat.rec (fun _ ↦ ℕ) 0 (fun acc' _ ↦ ih nr4 pr4 acc') (Nat.add 1 a4))
                      pr3)
                    pr2)
                  pr1)
                pos)
              nr3)
            nr2)
          nr1)
        neg)
    q

private theorem gqsp_asymDefect4Aux_eq (B B2 two_Rf rem : ℕ) : ∀ (q : ℕ) (neg pos : List ℕ)
    (acc : ℕ), gqsp_asymDefect4Aux B B2 two_Rf rem q neg pos acc = gqsp_zwAsymDefectLoop B
    B2 two_Rf (4 * q + rem) true neg pos acc := by
  intro q
  induction q with
  | zero =>
      intro neg pos acc
      rw [Nat.mul_zero, Nat.zero_add]
      rfl
  | succ q ih =>
      intro neg pos acc
      rcases neg with _ | ⟨n0, _ | ⟨n1, _ | ⟨n2, _ | ⟨n3, nr4⟩⟩⟩⟩
      · rfl
      · rfl
      · rfl
      · rfl
      rcases pos with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, pr4⟩⟩⟩⟩
      · rfl
      · rfl
      · rfl
      · rfl
      dsimp only [gqsp_asymDefect4Aux]
      have h4 : 4 * (q + 1) + rem = (((4 * q + rem) + 1) + 1) + 1 + 1 := by omega
      rw [gqsp_zwForce_eq, h4, gqsp_zwAsymDefect_cons_true, gqsp_zwAsymDefect_cons_false,
          gqsp_zwAsymDefect_cons_true, gqsp_zwAsymDefect_cons_false]
      exact ih nr4 pr4 _

/-- 4-step unrolled `.p`-only asymmetry defect sum. -/
noncomputable def gqsp_asymDefect4 (M1 B B2 R_final : ℕ) (neg_rev pos_tail : List ℕ) : ℕ :=
    @Nat.rec (fun _ ↦ ℕ) 0 (fun two_Rf _ ↦ gqsp_asymDefect4Aux B B2 two_Rf (Nat.mod M1 4)
    (Nat.div M1 4) neg_rev pos_tail 0) (Nat.add 1 (Nat.mul 2 R_final))

theorem gqsp_asymDefect4_eq (M1 B B2 R_final : ℕ) (neg_rev pos_tail : List ℕ) :
    gqsp_asymDefect4 M1 B B2 R_final neg_rev pos_tail =
      gqsp_zwAsymDefectPOnly M1 B B2 R_final neg_rev pos_tail := by
  unfold gqsp_asymDefect4 gqsp_zwAsymDefectPOnly
  rw [gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_asymDefect4Aux_eq]
  have hdm : 4 * Nat.div M1 4 + Nat.mod M1 4 = M1 := Nat.div_add_mod M1 4
  rw [hdm]

private theorem gqsp_zwChebL1Pos_cons_true (B B2 Bw W_err_dpos err_d_in pad rem' w0 n0 p0 : ℕ)
    (wt nt pt : List ℕ) (acc : ℕ) :
    gqsp_zwChebL1Pos B B2 Bw W_err_dpos err_d_in pad (w0 :: wt) (rem' +
      1) true (n0 :: nt) (p0 :: pt) acc =
      let pp := Nat.sub B2 p0
      let a := Nat.add (Nat.add pp n0) Bw
      let b := Nat.add w0 B2
      let diff := Nat.add (Nat.sub a b) (Nat.sub b a)
      gqsp_zwChebL1Pos B B2 Bw W_err_dpos err_d_in pad wt rem' false nt pt
        (Nat.add acc (Nat.add diff err_d_in)) := by
  dsimp only [gqsp_zwChebL1Pos]
  rw [gqsp_zwForce_eq]

private theorem gqsp_zwChebL1Pos_cons_false (B B2 Bw W_err_dpos err_d_in pad rem' w0 n0 p0 : ℕ)
    (wt nt pt : List ℕ) (acc : ℕ) :
    gqsp_zwChebL1Pos B B2 Bw W_err_dpos err_d_in pad (w0 :: wt) (rem' +
      1) false (n0 :: nt) (p0 :: pt) acc =
      let a := Nat.add (Nat.add p0 n0) Bw
      let b := Nat.add w0 B2
      let diff := Nat.add (Nat.sub a b) (Nat.sub b a)
      gqsp_zwChebL1Pos B B2 Bw W_err_dpos err_d_in pad wt rem' true nt pt
        (Nat.add acc (Nat.add diff err_d_in)) := by
  dsimp only [gqsp_zwChebL1Pos]
  rw [gqsp_zwForce_eq]

/-- 4-step unrolled `.p`-only positive-index Chebyshev L1 loop. -/
noncomputable def gqsp_chebL1Pos4Aux (B B2 Bw W_err_dpos err_d_in pad rem q : ℕ) :
    List ℕ → List ℕ → List ℕ → ℕ → ℕ :=
  @Nat.rec (fun _ ↦ List ℕ → List ℕ → List ℕ → ℕ → ℕ)
    (fun ws neg pos acc ↦ gqsp_zwChebL1Pos B B2 Bw W_err_dpos err_d_in pad ws rem true neg pos acc)
    (fun q' ih ws neg pos acc ↦
      let fb :=
        gqsp_zwChebL1Pos B B2 Bw W_err_dpos err_d_in pad ws (4 * (q' + 1) + rem) true neg pos acc
      @List.rec ℕ (fun _ ↦ ℕ) fb (fun w0 wr1 _ ↦
        @List.rec ℕ (fun _ ↦ ℕ) fb (fun w1 wr2 _ ↦
          @List.rec ℕ (fun _ ↦ ℕ) fb (fun w2 wr3 _ ↦
            @List.rec ℕ (fun _ ↦ ℕ) fb (fun w3 wr4 _ ↦
              @List.rec ℕ (fun _ ↦ ℕ) fb (fun n0 nr1 _ ↦
                @List.rec ℕ (fun _ ↦ ℕ) fb (fun n1 nr2 _ ↦
                  @List.rec ℕ (fun _ ↦ ℕ) fb (fun n2 nr3 _ ↦
                    @List.rec ℕ (fun _ ↦ ℕ) fb (fun n3 nr4 _ ↦
                      @List.rec ℕ (fun _ ↦ ℕ) fb (fun p0 pr1 _ ↦
                        @List.rec ℕ (fun _ ↦ ℕ) fb (fun p1 pr2 _ ↦
                          @List.rec ℕ (fun _ ↦ ℕ) fb (fun p2 pr3 _ ↦
                            @List.rec ℕ (fun _ ↦ ℕ) fb (fun p3 pr4 _ ↦
                              let pp0 := Nat.sub B2 p0
                              let a0 := Nat.add (Nat.add pp0 n0) Bw
                              let b0 := Nat.add w0 B2
                              let d0 := Nat.add (Nat.sub a0 b0) (Nat.sub b0 a0)
                              let acc1 := Nat.add acc (Nat.add d0 err_d_in)
                              let a1 := Nat.add (Nat.add p1 n1) Bw
                              let b1 := Nat.add w1 B2
                              let d1 := Nat.add (Nat.sub a1 b1) (Nat.sub b1 a1)
                              let acc2 := Nat.add acc1 (Nat.add d1 err_d_in)
                              let pp2 := Nat.sub B2 p2
                              let a2 := Nat.add (Nat.add pp2 n2) Bw
                              let b2 := Nat.add w2 B2
                              let d2 := Nat.add (Nat.sub a2 b2) (Nat.sub b2 a2)
                              let acc3 := Nat.add acc2 (Nat.add d2 err_d_in)
                              let a3 := Nat.add (Nat.add p3 n3) Bw
                              let b3 := Nat.add w3 B2
                              let d3 := Nat.add (Nat.sub a3 b3) (Nat.sub b3 a3)
                              let acc4 := Nat.add acc3 (Nat.add d3 err_d_in)
                              @Nat.rec (fun _ ↦ ℕ) 0 (fun acc' _ ↦
                                ih wr4 nr4 pr4 acc') (Nat.add 1 acc4))
                              pr3)
                            pr2)
                          pr1)
                        pos)
                      nr3)
                    nr2)
                  nr1)
                neg)
              wr3)
            wr2)
          wr1)
        ws)
    q

private theorem gqsp_chebL1Pos4Aux_eq (B B2 Bw W_err_dpos err_d_in pad rem : ℕ) :
    ∀ (q : ℕ) (ws neg pos : List ℕ) (acc : ℕ),
      gqsp_chebL1Pos4Aux B B2 Bw W_err_dpos err_d_in pad rem q ws neg pos acc =
        gqsp_zwChebL1Pos B B2 Bw W_err_dpos err_d_in pad ws (4 * q + rem) true neg pos acc := by
  intro q
  induction q with
  | zero =>
      intro ws neg pos acc
      rw [Nat.mul_zero, Nat.zero_add]
      rfl
  | succ q ih =>
      intro ws neg pos acc
      rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, wr4⟩⟩⟩⟩
      · rfl
      · rfl
      · rfl
      · rfl
      rcases neg with _ | ⟨n0, _ | ⟨n1, _ | ⟨n2, _ | ⟨n3, nr4⟩⟩⟩⟩
      · rfl
      · rfl
      · rfl
      · rfl
      rcases pos with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, pr4⟩⟩⟩⟩
      · rfl
      · rfl
      · rfl
      · rfl
      dsimp only [gqsp_chebL1Pos4Aux]
      have h4 : 4 * (q + 1) + rem = (((4 * q + rem) + 1) + 1) + 1 + 1 := by omega
      rw [gqsp_zwForce_eq, h4, gqsp_zwChebL1Pos_cons_true, gqsp_zwChebL1Pos_cons_false,
          gqsp_zwChebL1Pos_cons_true, gqsp_zwChebL1Pos_cons_false]
      exact ih wr4 nr4 pr4 _

/-- 4-step unrolled `.p`-only Chebyshev L1 sum. -/
noncomputable def gqsp_chebL1POnly4 (M1 B B2 Bw R_final W_err_d0 W_err_dpos pad : ℕ)
    (neg_rev : List ℕ) (p_center : ℕ) (pos_tail ws_unpad : List ℕ) : ℕ :=
  @List.rec ℕ (fun _ ↦ ℕ) 0
    (fun w0 wt _ ↦
      let a0 := Nat.add p_center Bw
      let b0 := Nat.add w0 B
      let diff0 := Nat.add (Nat.sub a0 b0) (Nat.sub b0 a0)
      let term0_raw := Nat.add diff0 (Nat.add R_final W_err_d0)
      let err_d_raw := Nat.add (Nat.mul 2 R_final) W_err_dpos
      @Nat.rec (fun _ ↦ ℕ) 0 (fun term0 _ ↦
        @Nat.rec (fun _ ↦ ℕ) 0 (fun err_d_in _ ↦
          gqsp_chebL1Pos4Aux B B2 Bw W_err_dpos err_d_in pad (Nat.mod M1 4) (Nat.div M1 4)
            wt neg_rev pos_tail term0)
          (Nat.add 1 err_d_raw))
        (Nat.add 1 term0_raw))
    ws_unpad

theorem gqsp_chebL1POnly4_eq (M1 B B2 Bw R_final W_err_d0 W_err_dpos pad : ℕ)
    (neg_rev : List ℕ) (p_center : ℕ) (pos_tail ws_unpad : List ℕ) :
    gqsp_chebL1POnly4 M1 B B2 Bw R_final W_err_d0 W_err_dpos pad neg_rev p_center pos_tail ws_unpad
      =
      gqsp_zwChebL1POnly M1 B B2 Bw R_final W_err_d0 W_err_dpos pad neg_rev p_center pos_tail
        ws_unpad := by
  rcases ws_unpad with _ | ⟨w0, wt⟩
  · rfl
  · unfold gqsp_chebL1POnly4 gqsp_zwChebL1POnly
    dsimp only
    rw [gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwForce_eq,
      gqsp_chebL1Pos4Aux_eq]
    have hdm : 4 * Nat.div M1 4 + Nat.mod M1 4 = M1 := Nat.div_add_mod M1 4
    rw [hdm]

/-- Zero-inner-`@Nat.rec` binary-tree `768`-bit lane reversal down to `m ≤ 9`. -/
noncomputable def gqsp_revPow2Bin0 (m768 k : ℕ) : ℕ → ℕ → ℕ :=
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
            (@Bool.rec (fun _ ↦ ℕ)
              (gqsp_zwRevLeaf1 m w 0)
              (Nat.add (Nat.land (Nat.shiftRight w 4608) m768)
                (Nat.shiftLeft (Nat.add (Nat.land (Nat.shiftRight w 3840) m768)
                  (Nat.shiftLeft (Nat.add (Nat.land (Nat.shiftRight w 3072) m768)
                    (Nat.shiftLeft (Nat.add (Nat.land (Nat.shiftRight w 2304) m768)
                      (Nat.shiftLeft (Nat.add (Nat.land (Nat.shiftRight w 1536) m768)
                        (Nat.shiftLeft (Nat.add (Nat.land (Nat.shiftRight w 768) m768)
                          (Nat.shiftLeft (Nat.land w m768) 768)) 768)) 768)) 768)) 768)) 768))
              (Nat.beq m 7))
            (Nat.add (Nat.land (Nat.shiftRight w 5376) m768)
              (Nat.shiftLeft (Nat.add (Nat.land (Nat.shiftRight w 4608) m768)
                (Nat.shiftLeft (Nat.add (Nat.land (Nat.shiftRight w 3840) m768)
                  (Nat.shiftLeft (Nat.add (Nat.land (Nat.shiftRight w 3072) m768)
                    (Nat.shiftLeft (Nat.add (Nat.land (Nat.shiftRight w 2304) m768)
                      (Nat.shiftLeft (Nat.add (Nat.land (Nat.shiftRight w 1536) m768)
                        (Nat.shiftLeft (Nat.add (Nat.land (Nat.shiftRight w 768) m768)
                          (Nat.shiftLeft (Nat.land w m768) 768)) 768)) 768)) 768)) 768)) 768)) 768))
            (Nat.beq m 8))
          (Nat.add (Nat.land (Nat.shiftRight w 6144) m768)
            (Nat.shiftLeft (Nat.add (Nat.land (Nat.shiftRight w 5376) m768)
              (Nat.shiftLeft (Nat.add (Nat.land (Nat.shiftRight w 4608) m768)
                (Nat.shiftLeft (Nat.add (Nat.land (Nat.shiftRight w 3840) m768)
                  (Nat.shiftLeft (Nat.add (Nat.land (Nat.shiftRight w 3072) m768)
                    (Nat.shiftLeft (Nat.add (Nat.land (Nat.shiftRight w 2304) m768)
                      (Nat.shiftLeft (Nat.add (Nat.land (Nat.shiftRight w 1536) m768)
                        (Nat.shiftLeft (Nat.add (Nat.land (Nat.shiftRight w 768) m768)
                          (Nat.shiftLeft (Nat.land w m768) 768)) 768)) 768)) 768)) 768)) 768)) 768))
                            768))
          (Nat.beq m 9))
        (Nat.ble m 9))
    k

private theorem gqsp_revPow2Bin0_eq (m768 k : ℕ) :
    ∀ (m w : ℕ), gqsp_revPow2Bin0 m768 k m w = gqsp_revPow2Bin m768 k m w := by
  unfold gqsp_revPow2Bin0 gqsp_revPow2Bin
  induction k with
  | zero => intro _ _; rfl
  | succ k ih =>
      intro m w
      dsimp only
      cases Nat.ble m 9
      · dsimp only
        rw [gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwForce_eq, ih, ih]
      · rfl

private theorem gqsp_revPow2Bin0_fun_eq : gqsp_revPow2Bin0 = gqsp_revPow2Bin := by
  funext m768 k m w
  exact gqsp_revPow2Bin0_eq m768 k m w

/-- Top-forced zero-inner-`@Nat.rec` binary-tree SWAR `768`-bit lane reversal (`O(n log n)`). -/
noncomputable def gqsp_fastRev4Swar0 (d n w : ℕ) : ℕ :=
  @Nat.rec (fun _ ↦ ℕ) 0 (fun w0 _ ↦
    gqsp_revPow2Bin0 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff d n w0)
    (Nat.add 1 w)

theorem gqsp_fastRev4Swar0_eq (d n w : ℕ) :
    gqsp_fastRev4Swar0 d n w = gqsp_zwFastRev4Swar d n w := by
  unfold gqsp_fastRev4Swar0
  rw [gqsp_zwForce_eq, gqsp_revPow2Bin0_fun_eq]
  change gqsp_fastRev4Swar d n w = gqsp_zwFastRev4Swar d n w
  exact gqsp_fastRev4Swar_eq d n w

/-- Zero-inner-`@Nat.rec` 2-channel real SWAR node merge auxiliary. -/
noncomputable def gqsp_mergeNodesRealAux0 (z : ℕ) (l r : TreeNodeC) : Option TreeNodeC :=
  @TreeNodeC.rec (fun _ ↦ Option TreeNodeC)
    (fun ldeg lsalt lrep1 lprp lprn lpip lpin lqrp lqrn lqip lqin lerr ↦
      @TreeNodeC.rec (fun _ ↦ Option TreeNodeC)
        (fun rdeg rsalt rrep1 rprp rprn rpip rpin rqrp rqrn rqip rqin rerr ↦
          @Bool.rec (fun _ ↦ Option TreeNodeC)
            (mergeNodesCGo (gqsp_swarDepth rdeg)
              ⟨ldeg, lsalt, lrep1, lprp, lprn, lpip, lpin, lqrp, lqrn, lqip, lqin, lerr⟩
              ⟨rdeg, rsalt, rrep1, rprp, rprn, rpip, rpin, rqrp, rqrn, rqip, rqin, rerr⟩)
            (@Nat.rec (fun _ ↦ Option TreeNodeC) none (fun d _ ↦
              @Nat.rec (fun _ ↦ Option TreeNodeC) none (fun rep1 _ ↦
                @Nat.rec (fun _ ↦ Option TreeNodeC) none (fun rb _ ↦
                  @Nat.rec (fun _ ↦ Option TreeNodeC) none (fun rk _ ↦
                    @Nat.rec (fun _ ↦ Option TreeNodeC) none (fun rbq _ ↦
                      @Nat.rec (fun _ ↦ Option TreeNodeC) none (fun rm _ ↦
                        @Nat.rec (fun _ ↦ Option TreeNodeC) none (fun rc _ ↦
                          @Nat.rec (fun _ ↦ Option TreeNodeC) none (fun lb353 _ ↦
                            @Nat.rec (fun _ ↦ Option TreeNodeC) none (fun rb353 _ ↦
                              @Nat.rec (fun _ ↦ Option TreeNodeC) none (fun rb354 _ ↦
                                @Nat.rec (fun _ ↦ Option TreeNodeC) none (fun rbReal _ ↦
                                  @Nat.rec (fun _ ↦ Option TreeNodeC) none (fun salt _ ↦
                                    @Nat.rec (fun _ ↦ Option TreeNodeC) none (fun ar _ ↦
                                      @Nat.rec (fun _ ↦ Option TreeNodeC) none (fun cr _ ↦
                                        @Nat.rec (fun _ ↦ Option TreeNodeC) none (fun yl _ ↦
                                          @Nat.rec (fun _ ↦ Option TreeNodeC) none (fun zl _ ↦
                                            @Nat.rec (fun _ ↦
                                              Option TreeNodeC) none (fun r_lanes _ ↦
                                              @Nat.rec (fun _ ↦ Option TreeNodeC) none (fun rar _ ↦
                                                @Nat.rec (fun _ ↦
                                                  Option TreeNodeC) none (fun ncr _ ↦
                                                  @Nat.rec (fun _ ↦
                                                    Option TreeNodeC) none (fun ys _ ↦
                                                    @Nat.rec (fun _ ↦
                                                      Option TreeNodeC) none (fun p_aryl _ ↦
                                                      @Nat.rec (fun _ ↦
                                                        Option TreeNodeC) none (fun sub_pr _ ↦
                                                        @Nat.rec (fun _ ↦
                                                          Option TreeNodeC) none (fun sub_qr _ ↦
                                                          @Nat.rec (fun _ ↦
                                                            Option TreeNodeC) none (fun z_pr _ ↦
                                                            @Nat.rec (fun _ ↦
                                                              Option TreeNodeC) none (fun z_qr _ ↦
                                                              @Nat.rec (fun _ ↦
                                                                Option TreeNodeC) none (fun q_pr _ ↦
                                                                @Nat.rec (fun _ ↦
                                                                  Option TreeNodeC) none (fun mp_pr
                                                                  _ ↦
                                                                  @Nat.rec (fun _ ↦
                                                                    Option TreeNodeC) none (fun
                                                                    mn_pr _ ↦
                                                                    @Nat.rec (fun _ ↦
                                                                      Option TreeNodeC) none (fun
                                                                      fp_pr _ ↦
                                                                      @Nat.rec (fun _ ↦
                                                                        Option TreeNodeC) none (fun
                                                                        fn_pr _ ↦
                                                                        @Bool.rec (fun _ ↦
                                                                          Option TreeNodeC)
                                                                          none
                                                                          (@Nat.rec (fun _ ↦
                                                                            Option TreeNodeC) none
                                                                            (fun q_qr _ ↦
                                                                            @Nat.rec (fun _ ↦
                                                                              Option TreeNodeC) none
                                                                              (fun mp_qr _ ↦
                                                                              @Nat.rec (fun _ ↦
                                                                                Option TreeNodeC)
                                                                                none (fun mn_qr _ ↦
                                                                                @Nat.rec (fun _ ↦
                                                                                  Option TreeNodeC)
                                                                                  none (fun fp_qr _
                                                                                  ↦
                                                                                  @Nat.rec (fun _ ↦
                                                                                    Option
                                                                                    TreeNodeC) none
                                                                                    (fun fn_qr _ ↦
                                                                                    @Bool.rec (fun _
                                                                                      ↦
                                                                                      Option
                                                                                      TreeNodeC)
                                                                                      none
                                                                                      (@Nat.rec (fun
                                                                                        _ ↦
                                                                                        Option
                                                                                        TreeNodeC)
                                                                                        none (fun
                                                                                        min_deg _ ↦
                                                                                        @Nat.rec
                                                                                          (fun _ ↦
                                                                                          Option
                                                                                          TreeNodeC)
                                                                                          none (fun
                                                                                          err_out _
                                                                                          ↦
                                                                                          @Bool.rec
                                                                                            (fun _ ↦
                                                                                            Option
                                                                                          TreeNodeC)
                                                                                            none
                                                                                            (some
                                                                                          ⟨Nat.add
                                                                                              ldeg
                                                                                              rdeg,
                                                                                              salt,
                                                                                              rep1,
                                                                                              fp_pr,
                                                                                              fn_pr,
                                                                                              0, 0,
                                                                                              fp_qr,
                                                                                              fn_qr,
                                                                                              0, 0,
                                                                                          err_out⟩)
                                                                                            (Nat.ble err_out 0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
                                                                                          (Nat.add 1
                                                                                            (Nat.add
                                                                                            1
                                                                                            (Nat.mul
                                                                                            (Nat.mul
                                                                                            4
                                                                                            (Nat.add
                                                                                            1
                                                                                          min_deg))
                                                                                            (Nat.add
                                                                                            (Nat.mul
                                                                                            3 rerr)
                                                                                            (Nat.mul
                                                                                            2
                                                                                          lerr))))))
                                                                                        (Nat.add 1
                                                                                          (@Bool.rec
                                                                                          (fun _ ↦
                                                                                          ℕ) rdeg
                                                                                          ldeg
                                                                                          (Nat.ble
                                                                                          ldeg
                                                                                          rdeg))))
                                                                                      (Nat.beq
                                                                                        (Nat.add
                                                                                        (Nat.land
                                                                                        fp_qr rc)
                                                                                        (Nat.land
                                                                                        fn_qr rc))
                                                                                        0))
                                                                                    (Nat.add 1
                                                                                      (Nat.sub
                                                                                      (Nat.land rbq
                                                                                      mn_qr)
                                                                                      (Nat.land q_qr
                                                                                      mn_qr))))
                                                                                  (Nat.add 1
                                                                                    (Nat.sub
                                                                                    (Nat.land q_qr
                                                                                    mp_qr) (Nat.land
                                                                                    rbq mp_qr))))
                                                                                (Nat.add 1 (Nat.sub
                                                                                  rm mp_qr)))
                                                                              (Nat.add 1 (Nat.mul 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff (Nat.shiftRight (Nat.land q_qr rbq) (Nat.add 384 z)))))
                                                                            (Nat.add 1
                                                                              (Nat.shiftRight
                                                                              (Nat.land z_qr rk)
                                                                              (Nat.add 352 z))))
                                                                          (Nat.beq (Nat.add
                                                                            (Nat.land fp_pr rc)
                                                                            (Nat.land fn_pr rc)) 0))
                                                                        (Nat.add 1 (Nat.sub
                                                                          (Nat.land rbq mn_pr)
                                                                          (Nat.land q_pr mn_pr))))
                                                                      (Nat.add 1 (Nat.sub (Nat.land
                                                                        q_pr mp_pr) (Nat.land rbq
                                                                        mp_pr))))
                                                                    (Nat.add 1 (Nat.sub rm mp_pr)))
                                                                  (Nat.add 1 (Nat.mul 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff (Nat.shiftRight (Nat.land q_pr rbq) (Nat.add 384 z)))))
                                                                (Nat.add 1 (Nat.shiftRight (Nat.land
                                                                  z_pr rk) (Nat.add 352 z))))
                                                            (Nat.add 1 (Nat.sub (Nat.add rbReal
                                                              (Nat.add (Nat.mul cr yl) (Nat.mul rar
                                                              zl))) (Nat.shiftLeft sub_qr (Nat.add
                                                              353 z)))))
                                                          (Nat.add 1 (Nat.sub (Nat.add rbReal
                                                            (Nat.add p_aryl (Nat.mul ncr zl)))
                                                            (Nat.shiftLeft sub_pr (Nat.add 353
                                                            z)))))
                                                        (Nat.add 1 (@Bool.rec (fun _ ↦ ℕ)
                                                          (Nat.add (Nat.mul (Nat.add cr rar) lrep1)
                                                            (Nat.mul ys rrep1))
                                                          (Nat.mul (Nat.add (Nat.add cr rar) ys)
                                                            lrep1)
                                                          (Nat.beq ldeg rdeg))))
                                                      (Nat.add 1 (@Bool.rec (fun _ ↦ ℕ)
                                                        (Nat.add (Nat.mul (Nat.add ar ncr) lrep1)
                                                          (Nat.mul ys rrep1))
                                                        (Nat.mul (Nat.add (Nat.add ar ncr) ys)
                                                          lrep1)
                                                        (Nat.beq ldeg rdeg))))
                                                    (Nat.add 1 (Nat.mul ar yl)))
                                                  (Nat.add 1 (Nat.add yl zl)))
                                                (Nat.add 1 (Nat.sub rb354 (gqsp_revPow2Bin0 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff d r_lanes cr))))
                                              (Nat.add 1 (gqsp_revPow2Bin0 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff d r_lanes ar)))
                                            (Nat.add 1 (Nat.add 1 rdeg)))
                                          (Nat.add 1 (Nat.sub (Nat.add lqrp lb353) lqrn)))
                                        (Nat.add 1 (Nat.sub (Nat.add lprp lb353) lprn)))
                                      (Nat.add 1 (Nat.sub (Nat.add rqrp rb353) rqrn)))
                                    (Nat.add 1 (Nat.sub (Nat.add rprp rb353) rprn)))
                                  (Nat.add 1 (Nat.land (Nat.add (Nat.add 1 (Nat.xor (Nat.mul
                                    0x9e3779b97f4a7c15 lsalt) (Nat.mul 0xbf58476d1ce4e5b9 rsalt)))
                                    z) 0xfffffffffffffff)))
                                (Nat.add 1 (Nat.add rb (Nat.shiftLeft (Nat.mul rrep1 lrep1) (Nat.add
                                  707 z)))))
                              (Nat.add 1 (Nat.shiftLeft rrep1 (Nat.add 354 z))))
                            (Nat.add 1 (Nat.shiftLeft rrep1 (Nat.add 353 z))))
                          (Nat.add 1 (Nat.shiftLeft lrep1 (Nat.add 353 z))))
                        (Nat.add 1 (Nat.mul 0x1fffffffe0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 rep1)))
                      (Nat.add 1 (Nat.mul 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff rep1)))
                    (Nat.add 1 (Nat.mul 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 rep1)))
                  (Nat.add 1 (Nat.mul 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 rep1)))
                (Nat.add 1 (Nat.mul 0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 rep1)))
              (Nat.add 1 (Nat.add lrep1 (Nat.shiftLeft (Nat.shiftRight rrep1 (Nat.add 768 z))
                (Nat.add (Nat.mul 768 (Nat.add ldeg 1)) z)))))
            (Nat.add 1 (@Bool.rec (fun _ ↦ ℕ)
              (@Bool.rec (fun _ ↦ ℕ)
                (@Bool.rec (fun _ ↦ ℕ)
                  (@Bool.rec (fun _ ↦ ℕ)
                    (@Bool.rec (fun _ ↦ ℕ)
                      (@Bool.rec (fun _ ↦ ℕ)
                        (@Bool.rec (fun _ ↦ ℕ)
                          (@Bool.rec (fun _ ↦ ℕ) 19 18 (Nat.ble rdeg 262143))
                          17 (Nat.ble rdeg 131071))
                        16 (Nat.ble rdeg 65535))
                      14 (Nat.ble rdeg 16383))
                    12 (Nat.ble rdeg 4095))
                  10 (Nat.ble rdeg 1023))
                8 (Nat.ble rdeg 255))
              6 (Nat.ble rdeg 63))))
            (Nat.beq (Nat.add (Nat.add (Nat.add lpip lpin) (Nat.add lqip lqin))
                              (Nat.add (Nat.add rpip rpin) (Nat.add rqip rqin))) 0))
        r)
    l

/-- Zero-inner-`@Nat.rec` per-pair 2-channel real SWAR node merge. -/
noncomputable def gqsp_mergeNodesReal0 (l r : TreeNodeC) : Option TreeNodeC :=
  gqsp_mergeNodesRealAux0 0 l r

theorem gqsp_mergeNodesReal0_eq (l r : TreeNodeC) :
    gqsp_mergeNodesReal0 l r = gqsp_zwMergeNodesReal l r := by
  unfold gqsp_mergeNodesReal0 gqsp_mergeNodesRealAux0
  rw [gqsp_revPow2Bin0_fun_eq]
  change gqsp_mergeNodesReal l r = gqsp_zwMergeNodesReal l r
  exact gqsp_mergeNodesReal_eq l r

noncomputable def gqsp_mergePairsStepReal0 (nds0 : List TreeNodeC) (st0 : Option TreeNodeC)
    (acc0 : List TreeNodeC) : Option (List TreeNodeC) := @List.rec TreeNodeC (fun _ ↦ Option
    TreeNodeC → List TreeNodeC → Option (List TreeNodeC)) (fun st acc ↦ @Option.rec TreeNodeC
    (fun _ ↦ Option (List TreeNodeC)) (some (gqsp_zwRevNodesTR acc [])) (fun x ↦ some
    (gqsp_zwRevNodesTR (x :: acc) [])) st) (fun z _ ih st acc ↦ @Option.rec TreeNodeC (fun _
    ↦ Option (List TreeNodeC)) (ih (some z) acc) (fun x ↦ @Option.rec TreeNodeC (fun _ ↦
    Option (List TreeNodeC)) none (fun xy ↦ ih none (xy :: acc)) (gqsp_mergeNodesReal0 x z))
    st) nds0 st0 acc0

theorem gqsp_mergePairsStepReal0_eq :
    ∀ (nds : List TreeNodeC) (st : Option TreeNodeC) (acc : List TreeNodeC),
      gqsp_mergePairsStepReal0 nds st acc = gqsp_zwMergePairsStepReal nds st acc
  | [], none, _ => rfl
  | [], some _, _ => rfl
  | z :: rest, none, acc => gqsp_mergePairsStepReal0_eq rest (some z) acc
  | z :: rest, some x, acc => by
      dsimp only [gqsp_mergePairsStepReal0, gqsp_zwMergePairsStepReal]
      rw [gqsp_mergeNodesReal0_eq x z]
      cases gqsp_zwMergeNodesReal x z with
      | none => rfl
      | some xy => exact gqsp_mergePairsStepReal0_eq rest none (xy :: acc)

/-- Zero-WHNF-cache per-pair real tournament evaluator (`0` `DefinitionVal`s on runtime bigints). -/
noncomputable def gqsp_evalTournamentReal0 (fuel : ℕ) : List TreeNodeC → Option TreeNodeC :=
    @Nat.rec (fun _ ↦ List TreeNodeC → Option TreeNodeC) (fun nds ↦ @List.rec TreeNodeC (fun _
    ↦ Option TreeNodeC) none (fun x rest1 _ ↦ @List.rec TreeNodeC (fun _ ↦ Option TreeNodeC)
    (some x) (fun _ _ _ ↦ none) rest1) nds) (fun _ ih nds ↦ @List.rec TreeNodeC (fun _ ↦
    Option TreeNodeC) none (fun x rest1 _ ↦ @List.rec TreeNodeC (fun _ ↦ Option TreeNodeC)
    (some x) (fun y rest _ ↦ @Option.rec (List TreeNodeC) (fun _ ↦ Option TreeNodeC) none ih
    (gqsp_mergePairsStepReal0 (x :: y :: rest) none [])) rest1) nds) fuel

theorem gqsp_evalTournamentReal0_eq :
    ∀ (fuel : ℕ) (nds : List TreeNodeC),
      gqsp_evalTournamentReal0 fuel nds = gqsp_zwEvalTournamentReal fuel nds
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | _ + 1, [_] => rfl
  | fuel + 1, x :: y :: rest => by
      dsimp only [gqsp_evalTournamentReal0, gqsp_zwEvalTournamentReal]
      rw [gqsp_mergePairsStepReal0_eq]
      cases gqsp_zwMergePairsStepReal (x :: y :: rest) none [] with
      | none => rfl
      | some next => exact gqsp_evalTournamentReal0_eq fuel next

private noncomputable def gqsp_interleaveFwd (B2 BIAS : ℕ) :
    List ℕ → List ℕ → List ℕ → List ℕ → List PQPair → List PQPair
  | [], _, _, _, tail => tail
  | _ :: _, [], _, _, tail => tail
  | _ :: _, _ :: _, [], _, tail => tail
  | _ :: _, _ :: _, _ :: _, [], tail => tail
  | up :: upt, uq :: uqt, rup :: rupt, ruq :: ruqt, tail =>
      ⟨Nat.add up BIAS, Nat.add uq BIAS⟩ ::
      ⟨Nat.sub B2 (Nat.add ruq BIAS), Nat.add rup BIAS⟩ ::
      gqsp_interleaveFwd B2 BIAS upt uqt rupt ruqt tail

private theorem gqsp_rev_interleaveFast_eq (B2 BIAS : ℕ) :
    ∀ (uP uQ ruP ruQ : List ℕ) (acc tail : List PQPair),
      gqsp_zwRevPQTR (gqsp_zwInterleaveFast B2 BIAS uP uQ ruP ruQ acc) tail =
        gqsp_zwRevPQTR acc (gqsp_interleaveFwd B2 BIAS uP uQ ruP ruQ tail)
  | [], _, _, _, _, _ => rfl
  | _ :: _, [], _, _, _, _ => rfl
  | _ :: _, _ :: _, [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, [], _, _ => rfl
  | _ :: upt, _ :: uqt, _ :: rupt, _ :: ruqt, _, tail =>
      gqsp_rev_interleaveFast_eq B2 BIAS upt uqt rupt ruqt _ tail

/-- Fused `.q`-residual sum specification directly from `(uP, uQ, ruP, ruQ)` (`0` `PQPair` list). -/
noncomputable def gqsp_zwQResidFromU (B B2 BIAS R_final : ℕ)
    (uP0 uQ0 ruP0 ruQ0 : List ℕ) (q_prev0 acc0 : ℕ) : ℕ :=
  let finish := fun q_prev acc ↦
    let q_last := Nat.shiftRight (Nat.add B (Nat.sub B2 q_prev)) 1
    Nat.add acc (Nat.add (Nat.add (Nat.sub q_last B) (Nat.sub B q_last)) R_final)
  @List.rec ℕ (fun _ ↦ List ℕ → List ℕ → List ℕ → ℕ → ℕ → ℕ)
    (fun _ _ _ q_prev acc ↦ finish q_prev acc)
    (fun up _ ih luq lrup lruq q_prev acc ↦
      @List.rec ℕ (fun _ ↦ ℕ) (finish q_prev acc) (fun uq uqt _ ↦
        @List.rec ℕ (fun _ ↦ ℕ) (finish q_prev acc) (fun rup rupt _ ↦
          @List.rec ℕ (fun _ ↦ ℕ) (finish q_prev acc) (fun ruq ruqt _ ↦
            let pA := Nat.add up BIAS
            let qA := Nat.add uq BIAS
            let pB := Nat.sub B2 (Nat.add ruq BIAS)
            let qB := Nat.add rup BIAS
            let qcA := Nat.shiftRight (Nat.add pA (Nat.sub B2 q_prev)) 1
            let dA := Nat.add (Nat.sub qcA B) (Nat.sub B qcA)
            let acc1 := Nat.add acc (Nat.add dA R_final)
            let qcB := Nat.shiftRight (Nat.add pB (Nat.sub B2 qA)) 1
            let dB := Nat.add (Nat.sub qcB B) (Nat.sub B qcB)
            let acc2 := Nat.add acc1 (Nat.add dB R_final)
            @Nat.rec (fun _ ↦ ℕ) 0 (fun qB' _ ↦
              @Nat.rec (fun _ ↦ ℕ) 0 (fun acc' _ ↦
                ih uqt rupt ruqt qB' acc')
                (Nat.add 1 acc2))
              (Nat.add 1 qB))
            lruq)
          lrup)
        luq)
    uP0 uQ0 ruP0 ruQ0 q_prev0 acc0

private theorem gqsp_zwQResidFromU_cons (B B2 BIAS R_final up uq rup ruq : ℕ)
    (upt uqt rupt ruqt : List ℕ) (q_prev acc : ℕ) :
    gqsp_zwQResidFromU B B2 BIAS R_final
      (up :: upt) (uq :: uqt) (rup :: rupt) (ruq :: ruqt) q_prev acc =
      let pA := Nat.add up BIAS
      let qA := Nat.add uq BIAS
      let pB := Nat.sub B2 (Nat.add ruq BIAS)
      let qB := Nat.add rup BIAS
      let qcA := Nat.shiftRight (Nat.add pA (Nat.sub B2 q_prev)) 1
      let dA := Nat.add (Nat.sub qcA B) (Nat.sub B qcA)
      let acc1 := Nat.add acc (Nat.add dA R_final)
      let qcB := Nat.shiftRight (Nat.add pB (Nat.sub B2 qA)) 1
      let dB := Nat.add (Nat.sub qcB B) (Nat.sub B qcB)
      let acc2 := Nat.add acc1 (Nat.add dB R_final)
      gqsp_zwQResidFromU B B2 BIAS R_final upt uqt rupt ruqt qB acc2 := by
  dsimp only [gqsp_zwQResidFromU]
  rw [gqsp_zwForce_eq, gqsp_zwForce_eq]

private theorem gqsp_zwQResidFromU_eq (B B2 BIAS R_final : ℕ) :
    ∀ (uP uQ ruP ruQ : List ℕ) (q_prev acc : ℕ),
      gqsp_zwQResidFromU B B2 BIAS R_final uP uQ ruP ruQ q_prev acc =
        gqsp_zwQResidHadamard B B2 R_final
          (gqsp_interleaveFwd B2 BIAS uP uQ ruP ruQ []) q_prev acc
  | [], _, _, _, _, _ => rfl
  | _ :: _, [], _, _, _, _ => rfl
  | _ :: _, _ :: _, [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, [], _, _ => rfl
  | up :: upt, uq :: uqt, rup :: rupt, ruq :: ruqt, q_prev, acc => by
      rw [gqsp_zwQResidFromU_cons]
      dsimp only [gqsp_interleaveFwd]
      rw [gqsp_zwQResid_cons, gqsp_zwQResid_cons]
      exact gqsp_zwQResidFromU_eq B B2 BIAS R_final upt uqt rupt ruqt _ _

/-- 4-step `@Nat.rec`-unrolled fused `.q`-residual sum
(`≤ 34,000` C++ stack frames at `M = 135,867`). -/
noncomputable def gqsp_qResidFromU4 (B B2 BIAS R_final fuel : ℕ) :
    List ℕ → List ℕ → List ℕ → List ℕ → ℕ → ℕ → ℕ :=
  @Nat.rec (fun _ ↦ List ℕ → List ℕ → List ℕ → List ℕ → ℕ → ℕ → ℕ)
    (gqsp_zwQResidFromU B B2 BIAS R_final)
    (fun _ ih uP uQ ruP ruQ q_prev acc ↦
      let fb := gqsp_zwQResidFromU B B2 BIAS R_final uP uQ ruP ruQ q_prev acc
      @List.rec ℕ (fun _ ↦ ℕ) fb (fun up0 ups1 _ ↦
      @List.rec ℕ (fun _ ↦ ℕ) fb (fun up1 ups2 _ ↦
      @List.rec ℕ (fun _ ↦ ℕ) fb (fun up2 ups3 _ ↦
      @List.rec ℕ (fun _ ↦ ℕ) fb (fun up3 upt _ ↦
      @List.rec ℕ (fun _ ↦ ℕ) fb (fun uq0 uqs1 _ ↦
      @List.rec ℕ (fun _ ↦ ℕ) fb (fun uq1 uqs2 _ ↦
      @List.rec ℕ (fun _ ↦ ℕ) fb (fun uq2 uqs3 _ ↦
      @List.rec ℕ (fun _ ↦ ℕ) fb (fun uq3 uqt _ ↦
      @List.rec ℕ (fun _ ↦ ℕ) fb (fun rup0 rups1 _ ↦
      @List.rec ℕ (fun _ ↦ ℕ) fb (fun rup1 rups2 _ ↦
      @List.rec ℕ (fun _ ↦ ℕ) fb (fun rup2 rups3 _ ↦
      @List.rec ℕ (fun _ ↦ ℕ) fb (fun rup3 rupt _ ↦
      @List.rec ℕ (fun _ ↦ ℕ) fb (fun ruq0 ruqs1 _ ↦
      @List.rec ℕ (fun _ ↦ ℕ) fb (fun ruq1 ruqs2 _ ↦
      @List.rec ℕ (fun _ ↦ ℕ) fb (fun ruq2 ruqs3 _ ↦
      @List.rec ℕ (fun _ ↦ ℕ) fb (fun ruq3 ruqt _ ↦
            let pA0 := Nat.add up0 BIAS
            let qA0 := Nat.add uq0 BIAS
            let pB0 := Nat.sub B2 (Nat.add ruq0 BIAS)
            let qB0 := Nat.add rup0 BIAS
            let qcA0 := Nat.shiftRight (Nat.add pA0 (Nat.sub B2 q_prev)) 1
            let dA0 := Nat.add (Nat.sub qcA0 B) (Nat.sub B qcA0)
            let acc1_0 := Nat.add acc (Nat.add dA0 R_final)
            let qcB0 := Nat.shiftRight (Nat.add pB0 (Nat.sub B2 qA0)) 1
            let dB0 := Nat.add (Nat.sub qcB0 B) (Nat.sub B qcB0)
            let acc2_0 := Nat.add acc1_0 (Nat.add dB0 R_final)
            let pA1 := Nat.add up1 BIAS
            let qA1 := Nat.add uq1 BIAS
            let pB1 := Nat.sub B2 (Nat.add ruq1 BIAS)
            let qB1 := Nat.add rup1 BIAS
            let qcA1 := Nat.shiftRight (Nat.add pA1 (Nat.sub B2 qB0)) 1
            let dA1 := Nat.add (Nat.sub qcA1 B) (Nat.sub B qcA1)
            let acc1_1 := Nat.add acc2_0 (Nat.add dA1 R_final)
            let qcB1 := Nat.shiftRight (Nat.add pB1 (Nat.sub B2 qA1)) 1
            let dB1 := Nat.add (Nat.sub qcB1 B) (Nat.sub B qcB1)
            let acc2_1 := Nat.add acc1_1 (Nat.add dB1 R_final)
            let pA2 := Nat.add up2 BIAS
            let qA2 := Nat.add uq2 BIAS
            let pB2 := Nat.sub B2 (Nat.add ruq2 BIAS)
            let qB2 := Nat.add rup2 BIAS
            let qcA2 := Nat.shiftRight (Nat.add pA2 (Nat.sub B2 qB1)) 1
            let dA2 := Nat.add (Nat.sub qcA2 B) (Nat.sub B qcA2)
            let acc1_2 := Nat.add acc2_1 (Nat.add dA2 R_final)
            let qcB2 := Nat.shiftRight (Nat.add pB2 (Nat.sub B2 qA2)) 1
            let dB2 := Nat.add (Nat.sub qcB2 B) (Nat.sub B qcB2)
            let acc2_2 := Nat.add acc1_2 (Nat.add dB2 R_final)
            let pA3 := Nat.add up3 BIAS
            let qA3 := Nat.add uq3 BIAS
            let pB3 := Nat.sub B2 (Nat.add ruq3 BIAS)
            let qB3 := Nat.add rup3 BIAS
            let qcA3 := Nat.shiftRight (Nat.add pA3 (Nat.sub B2 qB2)) 1
            let dA3 := Nat.add (Nat.sub qcA3 B) (Nat.sub B qcA3)
            let acc1_3 := Nat.add acc2_2 (Nat.add dA3 R_final)
            let qcB3 := Nat.shiftRight (Nat.add pB3 (Nat.sub B2 qA3)) 1
            let dB3 := Nat.add (Nat.sub qcB3 B) (Nat.sub B qcB3)
            let acc2_3 := Nat.add acc1_3 (Nat.add dB3 R_final)
            @Nat.rec (fun _ ↦ ℕ) 0 (fun qB3' _ ↦
              @Nat.rec (fun _ ↦ ℕ) 0 (fun acc4' _ ↦
                ih upt uqt rupt ruqt qB3' acc4')
                (Nat.add 1 acc2_3))
              (Nat.add 1 qB3))
        ruqs3) ruqs2) ruqs1) ruQ) rups3) rups2) rups1) ruP) uqs3) uqs2) uqs1) uQ) ups3) ups2) ups1)
          uP)
    fuel

private theorem gqsp_qResidFromU4_eq (B B2 BIAS R_final : ℕ) : ∀ (fuel : ℕ)
    (uP uQ ruP ruQ : List ℕ) (q_prev acc : ℕ), gqsp_qResidFromU4 B B2 BIAS R_final fuel uP uQ
    ruP ruQ q_prev acc = gqsp_zwQResidFromU B B2 BIAS R_final uP uQ ruP ruQ q_prev acc := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _; rfl
  | succ fuel ih =>
      intro uP uQ ruP ruQ q_prev acc
      unfold gqsp_qResidFromU4
      dsimp only
      rcases uP with _ | ⟨up0, _ | ⟨up1, _ | ⟨up2, _ | ⟨up3, upt⟩⟩⟩⟩ <;> try rfl
      rcases uQ with _ | ⟨uq0, _ | ⟨uq1, _ | ⟨uq2, _ | ⟨uq3, uqt⟩⟩⟩⟩ <;> try rfl
      rcases ruP with _ | ⟨rup0, _ | ⟨rup1, _ | ⟨rup2, _ | ⟨rup3, rupt⟩⟩⟩⟩ <;> try rfl
      rcases ruQ with _ | ⟨ruq0, _ | ⟨ruq1, _ | ⟨ruq2, _ | ⟨ruq3, ruqt⟩⟩⟩⟩ <;> try rfl
      dsimp only
      rw [gqsp_zwForce_eq, gqsp_zwForce_eq]
      change gqsp_qResidFromU4 B B2 BIAS R_final fuel upt uqt rupt ruqt _ _ = _
      rw [ih, gqsp_zwQResidFromU_cons, gqsp_zwQResidFromU_cons,
          gqsp_zwQResidFromU_cons, gqsp_zwQResidFromU_cons]

private noncomputable def gqsp_hadamardFwdAux (B : ℕ) : List PQPair → ℕ → List ℕ → List ℕ
  | [], q_prev, tail => Nat.shiftRight (Nat.add B q_prev) 1 :: tail
  | ⟨ph, qh⟩ :: t, q_prev, tail =>
      Nat.shiftRight (Nat.add ph q_prev) 1 :: gqsp_hadamardFwdAux B t qh tail

private theorem gqsp_rev_hadamardFast_eq (B : ℕ) :
    ∀ (pq : List PQPair) (q_prev : ℕ) (hacc tail : List ℕ),
      gqsp_zwRevNatTR (gqsp_zwHadamardFast B pq q_prev hacc) tail =
        gqsp_zwRevNatTR hacc (gqsp_hadamardFwdAux B pq q_prev tail)
  | [], _, _, _ => rfl
  | ⟨_, qh⟩ :: t, _, _, tail => gqsp_rev_hadamardFast_eq B t qh _ tail

/-- Tail-recursive Hadamard accumulator specification on `(uP, uQ, ruP, ruQ)`. -/
noncomputable def gqsp_zwHadamardRevFromU (B B2 BIAS : ℕ)
    (uP0 uQ0 ruP0 ruQ0 : List ℕ) (q_prev0 : ℕ) (racc0 : List ℕ) : List ℕ :=
  let finish := fun q_prev racc ↦ Nat.shiftRight (Nat.add B q_prev) 1 :: racc
  @List.rec ℕ (fun _ ↦ List ℕ → List ℕ → List ℕ → ℕ → List ℕ → List ℕ)
    (fun _ _ _ q_prev racc ↦ finish q_prev racc)
    (fun up _ ih luq lrup lruq q_prev racc ↦
      @List.rec ℕ (fun _ ↦ List ℕ) (finish q_prev racc) (fun uq uqt _ ↦
        @List.rec ℕ (fun _ ↦ List ℕ) (finish q_prev racc) (fun rup rupt _ ↦
          @List.rec ℕ (fun _ ↦ List ℕ) (finish q_prev racc) (fun ruq ruqt _ ↦
            let pA := Nat.add up BIAS
            let qA := Nat.add uq BIAS
            let pB := Nat.sub B2 (Nat.add ruq BIAS)
            let qB := Nat.add rup BIAS
            let hA := Nat.shiftRight (Nat.add pA q_prev) 1
            let hB := Nat.shiftRight (Nat.add pB qA) 1
            @Nat.rec (fun _ ↦ List ℕ) [] (fun qB' _ ↦
              @Nat.rec (fun _ ↦ List ℕ) [] (fun hA' _ ↦
                @Nat.rec (fun _ ↦ List ℕ) [] (fun hB' _ ↦
                  ih uqt rupt ruqt qB' (hB' :: hA' :: racc))
                  (Nat.add 1 hB))
                (Nat.add 1 hA))
              (Nat.add 1 qB))
            lruq)
          lrup)
        luq)
    uP0 uQ0 ruP0 ruQ0 q_prev0 racc0

private theorem gqsp_zwHadamardRevFromU_cons (B B2 BIAS up uq rup ruq : ℕ)
    (upt uqt rupt ruqt : List ℕ) (q_prev : ℕ) (racc : List ℕ) :
    gqsp_zwHadamardRevFromU B B2 BIAS
      (up :: upt) (uq :: uqt) (rup :: rupt) (ruq :: ruqt) q_prev racc =
      let pA := Nat.add up BIAS
      let qA := Nat.add uq BIAS
      let pB := Nat.sub B2 (Nat.add ruq BIAS)
      let qB := Nat.add rup BIAS
      let hA := Nat.shiftRight (Nat.add pA q_prev) 1
      let hB := Nat.shiftRight (Nat.add pB qA) 1
      gqsp_zwHadamardRevFromU B B2 BIAS upt uqt rupt ruqt qB (hB :: hA :: racc) := by
  dsimp only [gqsp_zwHadamardRevFromU]
  rw [gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwForce_eq]

private theorem gqsp_rev_hadamardRevFromU_eq (B B2 BIAS : ℕ) :
    ∀ (uP uQ ruP ruQ : List ℕ) (q_prev : ℕ) (racc tail : List ℕ),
      gqsp_zwRevNatTR (gqsp_zwHadamardRevFromU B B2 BIAS uP uQ ruP ruQ q_prev racc) tail =
        gqsp_zwRevNatTR racc
          (gqsp_hadamardFwdAux B (gqsp_interleaveFwd B2 BIAS uP uQ ruP ruQ []) q_prev tail)
  | [], _, _, _, _, _, _ => rfl
  | _ :: _, [], _, _, _, _, _ => rfl
  | _ :: _, _ :: _, [], _, _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, [], _, _, _ => rfl
  | up :: upt, uq :: uqt, rup :: rupt, ruq :: ruqt, q_prev, racc, tail => by
      rw [gqsp_zwHadamardRevFromU_cons]
      dsimp only [gqsp_interleaveFwd, gqsp_hadamardFwdAux]
      exact gqsp_rev_hadamardRevFromU_eq B B2 BIAS upt uqt rupt ruqt _ (_ :: _ :: racc) tail

/-- 4-step `@Nat.rec`-unrolled Hadamard accumulator (`≤ 17,000` C++ stack frames on second half). -/
noncomputable def gqsp_hadamardRevFromU4 (B B2 BIAS fuel : ℕ) :
    List ℕ → List ℕ → List ℕ → List ℕ → ℕ → List ℕ → List ℕ :=
  @Nat.rec (fun _ ↦ List ℕ → List ℕ → List ℕ → List ℕ → ℕ → List ℕ → List ℕ)
    (gqsp_zwHadamardRevFromU B B2 BIAS)
    (fun _ ih uP uQ ruP ruQ q_prev racc ↦
      let fb := gqsp_zwHadamardRevFromU B B2 BIAS uP uQ ruP ruQ q_prev racc
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun up0 ups1 _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun up1 ups2 _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun up2 ups3 _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun up3 upt _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun uq0 uqs1 _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun uq1 uqs2 _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun uq2 uqs3 _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun uq3 uqt _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun rup0 rups1 _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun rup1 rups2 _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun rup2 rups3 _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun rup3 rupt _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun ruq0 ruqs1 _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun ruq1 ruqs2 _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun ruq2 ruqs3 _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun ruq3 ruqt _ ↦
            let pA0 := Nat.add up0 BIAS
            let qA0 := Nat.add uq0 BIAS
            let pB0 := Nat.sub B2 (Nat.add ruq0 BIAS)
            let qB0 := Nat.add rup0 BIAS
            let hA0 := Nat.shiftRight (Nat.add pA0 q_prev) 1
            let hB0 := Nat.shiftRight (Nat.add pB0 qA0) 1
            let pA1 := Nat.add up1 BIAS
            let qA1 := Nat.add uq1 BIAS
            let pB1 := Nat.sub B2 (Nat.add ruq1 BIAS)
            let qB1 := Nat.add rup1 BIAS
            let hA1 := Nat.shiftRight (Nat.add pA1 qB0) 1
            let hB1 := Nat.shiftRight (Nat.add pB1 qA1) 1
            let pA2 := Nat.add up2 BIAS
            let qA2 := Nat.add uq2 BIAS
            let pB2 := Nat.sub B2 (Nat.add ruq2 BIAS)
            let qB2 := Nat.add rup2 BIAS
            let hA2 := Nat.shiftRight (Nat.add pA2 qB1) 1
            let hB2 := Nat.shiftRight (Nat.add pB2 qA2) 1
            let pA3 := Nat.add up3 BIAS
            let qA3 := Nat.add uq3 BIAS
            let pB3 := Nat.sub B2 (Nat.add ruq3 BIAS)
            let qB3 := Nat.add rup3 BIAS
            let hA3 := Nat.shiftRight (Nat.add pA3 qB2) 1
            let hB3 := Nat.shiftRight (Nat.add pB3 qA3) 1
            @Nat.rec (fun _ ↦ List ℕ) [] (fun qB3' _ ↦
              @Nat.rec (fun _ ↦ List ℕ) [] (fun hA0' _ ↦
              @Nat.rec (fun _ ↦ List ℕ) [] (fun hB0' _ ↦
              @Nat.rec (fun _ ↦ List ℕ) [] (fun hA1' _ ↦
              @Nat.rec (fun _ ↦ List ℕ) [] (fun hB1' _ ↦
              @Nat.rec (fun _ ↦ List ℕ) [] (fun hA2' _ ↦
              @Nat.rec (fun _ ↦ List ℕ) [] (fun hB2' _ ↦
              @Nat.rec (fun _ ↦ List ℕ) [] (fun hA3' _ ↦
              @Nat.rec (fun _ ↦ List ℕ) [] (fun hB3' _ ↦
              ih upt uqt rupt ruqt qB3' (hB3' :: hA3' :: hB2' :: hA2' :: hB1' :: hA1' :: hB0' ::
                hA0' :: racc))
              (Nat.add 1 hB3))
              (Nat.add 1 hA3))
              (Nat.add 1 hB2))
              (Nat.add 1 hA2))
              (Nat.add 1 hB1))
              (Nat.add 1 hA1))
              (Nat.add 1 hB0))
              (Nat.add 1 hA0))
              (Nat.add 1 qB3))
        ruqs3) ruqs2) ruqs1) ruQ) rups3) rups2) rups1) ruP) uqs3) uqs2) uqs1) uQ) ups3) ups2) ups1)
          uP)
    fuel

private theorem gqsp_hadamardRevFromU4_eq (B B2 BIAS : ℕ) :
    ∀ (fuel : ℕ) (uP uQ ruP ruQ : List ℕ) (q_prev : ℕ) (racc : List ℕ),
      gqsp_hadamardRevFromU4 B B2 BIAS fuel uP uQ ruP ruQ q_prev racc =
        gqsp_zwHadamardRevFromU B B2 BIAS uP uQ ruP ruQ q_prev racc := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _; rfl
  | succ fuel ih =>
      intro uP uQ ruP ruQ q_prev racc
      unfold gqsp_hadamardRevFromU4
      dsimp only
      rcases uP with _ | ⟨up0, _ | ⟨up1, _ | ⟨up2, _ | ⟨up3, upt⟩⟩⟩⟩ <;> try rfl
      rcases uQ with _ | ⟨uq0, _ | ⟨uq1, _ | ⟨uq2, _ | ⟨uq3, uqt⟩⟩⟩⟩ <;> try rfl
      rcases ruP with _ | ⟨rup0, _ | ⟨rup1, _ | ⟨rup2, _ | ⟨rup3, rupt⟩⟩⟩⟩ <;> try rfl
      rcases ruQ with _ | ⟨ruq0, _ | ⟨ruq1, _ | ⟨ruq2, _ | ⟨ruq3, ruqt⟩⟩⟩⟩ <;> try rfl
      dsimp only
      rw [gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwForce_eq,
          gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwForce_eq,
          gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwForce_eq]
      change gqsp_hadamardRevFromU4 B B2 BIAS fuel upt uqt rupt ruqt _ _ = _
      rw [ih, gqsp_zwHadamardRevFromU_cons, gqsp_zwHadamardRevFromU_cons,
          gqsp_zwHadamardRevFromU_cons, gqsp_zwHadamardRevFromU_cons]

private theorem gqsp_splitHadFallback_eq (rf B B2 BIAS k : ℕ) (uP uQ ruP ruQ : List ℕ)
    (q_prev : ℕ) (neg_acc : List ℕ) : gqsp_tf_shareHeadList (gqsp_revNat4 rf
    (gqsp_hadamardRevFromU4 B B2 BIAS rf uP uQ ruP ruQ q_prev []) [])
    (fun ps_rem ↦ some (gqsp_zwSplitPRev B k ps_rem neg_acc)) = some (gqsp_zwSplitPRev B k
    (gqsp_hadamardFwdAux B (gqsp_interleaveFwd B2 BIAS uP uQ ruP ruQ []) q_prev []) neg_acc)
    := by
  rw [gqsp_tf_shareHeadList_eq, gqsp_revNat4_eq, gqsp_hadamardRevFromU4_eq,
    gqsp_rev_hadamardRevFromU_eq]
  rfl

/-- Consumes `quads` 4-tuples of `(uP, uQ, ruP, ruQ)` (`8 * quads` Hadamard outputs) directly into
`neg_acc` (`≤ 17,000` frames), shares the remaining half once,
  and returns `some (...)` so `@Option.rec`
evaluates the `135,868`-step Hadamard loop exactly `1x` instead of `3x`. -/
noncomputable def gqsp_splitHadamardQuads (rf B B2 BIAS rem quads : ℕ) :
    List ℕ → List ℕ → List ℕ → List ℕ → ℕ → List ℕ → Option (List ℕ × ℕ × List ℕ) :=
  @Nat.rec (fun _ ↦ List ℕ → List ℕ → List ℕ → List ℕ → ℕ → List ℕ → Option (List ℕ × ℕ × List ℕ))
    (fun uP uQ ruP ruQ q_prev neg_acc ↦
      gqsp_tf_shareHeadList
        (gqsp_revNat4 rf (gqsp_hadamardRevFromU4 B B2 BIAS rf uP uQ ruP ruQ q_prev []) [])
        (fun ps_rem ↦ some (gqsp_zwSplitPRev B rem ps_rem neg_acc)))
    (fun q' ih uP uQ ruP ruQ q_prev neg_acc ↦
      let fb := gqsp_tf_shareHeadList (gqsp_revNat4 rf (gqsp_hadamardRevFromU4 B B2 BIAS rf
          uP uQ ruP ruQ q_prev []) []) (fun ps_rem ↦ some (gqsp_zwSplitPRev B (8 * (q' + 1) +
          rem) ps_rem neg_acc))
      @List.rec ℕ (fun _ ↦ Option (List ℕ × ℕ × List ℕ)) fb (fun up0 ups1 _ ↦
      @List.rec ℕ (fun _ ↦ Option (List ℕ × ℕ × List ℕ)) fb (fun up1 ups2 _ ↦
      @List.rec ℕ (fun _ ↦ Option (List ℕ × ℕ × List ℕ)) fb (fun up2 ups3 _ ↦
      @List.rec ℕ (fun _ ↦ Option (List ℕ × ℕ × List ℕ)) fb (fun up3 upt _ ↦
      @List.rec ℕ (fun _ ↦ Option (List ℕ × ℕ × List ℕ)) fb (fun uq0 uqs1 _ ↦
      @List.rec ℕ (fun _ ↦ Option (List ℕ × ℕ × List ℕ)) fb (fun uq1 uqs2 _ ↦
      @List.rec ℕ (fun _ ↦ Option (List ℕ × ℕ × List ℕ)) fb (fun uq2 uqs3 _ ↦
      @List.rec ℕ (fun _ ↦ Option (List ℕ × ℕ × List ℕ)) fb (fun uq3 uqt _ ↦
      @List.rec ℕ (fun _ ↦ Option (List ℕ × ℕ × List ℕ)) fb (fun rup0 rups1 _ ↦
      @List.rec ℕ (fun _ ↦ Option (List ℕ × ℕ × List ℕ)) fb (fun rup1 rups2 _ ↦
      @List.rec ℕ (fun _ ↦ Option (List ℕ × ℕ × List ℕ)) fb (fun rup2 rups3 _ ↦
      @List.rec ℕ (fun _ ↦ Option (List ℕ × ℕ × List ℕ)) fb (fun rup3 rupt _ ↦
      @List.rec ℕ (fun _ ↦ Option (List ℕ × ℕ × List ℕ)) fb (fun ruq0 ruqs1 _ ↦
      @List.rec ℕ (fun _ ↦ Option (List ℕ × ℕ × List ℕ)) fb (fun ruq1 ruqs2 _ ↦
      @List.rec ℕ (fun _ ↦ Option (List ℕ × ℕ × List ℕ)) fb (fun ruq2 ruqs3 _ ↦
      @List.rec ℕ (fun _ ↦ Option (List ℕ × ℕ × List ℕ)) fb (fun ruq3 ruqt _ ↦
            let pA0 := Nat.add up0 BIAS
            let qA0 := Nat.add uq0 BIAS
            let pB0 := Nat.sub B2 (Nat.add ruq0 BIAS)
            let qB0 := Nat.add rup0 BIAS
            let hA0 := Nat.shiftRight (Nat.add pA0 q_prev) 1
            let hB0 := Nat.shiftRight (Nat.add pB0 qA0) 1
            let pA1 := Nat.add up1 BIAS
            let qA1 := Nat.add uq1 BIAS
            let pB1 := Nat.sub B2 (Nat.add ruq1 BIAS)
            let qB1 := Nat.add rup1 BIAS
            let hA1 := Nat.shiftRight (Nat.add pA1 qB0) 1
            let hB1 := Nat.shiftRight (Nat.add pB1 qA1) 1
            let pA2 := Nat.add up2 BIAS
            let qA2 := Nat.add uq2 BIAS
            let pB2 := Nat.sub B2 (Nat.add ruq2 BIAS)
            let qB2 := Nat.add rup2 BIAS
            let hA2 := Nat.shiftRight (Nat.add pA2 qB1) 1
            let hB2 := Nat.shiftRight (Nat.add pB2 qA2) 1
            let pA3 := Nat.add up3 BIAS
            let qA3 := Nat.add uq3 BIAS
            let pB3 := Nat.sub B2 (Nat.add ruq3 BIAS)
            let qB3 := Nat.add rup3 BIAS
            let hA3 := Nat.shiftRight (Nat.add pA3 qB2) 1
            let hB3 := Nat.shiftRight (Nat.add pB3 qA3) 1
            @Nat.rec (fun _ ↦ Option (List ℕ × ℕ × List ℕ)) none (fun qB3' _ ↦
              @Nat.rec (fun _ ↦ Option (List ℕ × ℕ × List ℕ)) none (fun hA0' _ ↦
              @Nat.rec (fun _ ↦ Option (List ℕ × ℕ × List ℕ)) none (fun hB0' _ ↦
              @Nat.rec (fun _ ↦ Option (List ℕ × ℕ × List ℕ)) none (fun hA1' _ ↦
              @Nat.rec (fun _ ↦ Option (List ℕ × ℕ × List ℕ)) none (fun hB1' _ ↦
              @Nat.rec (fun _ ↦ Option (List ℕ × ℕ × List ℕ)) none (fun hA2' _ ↦
              @Nat.rec (fun _ ↦ Option (List ℕ × ℕ × List ℕ)) none (fun hB2' _ ↦
              @Nat.rec (fun _ ↦ Option (List ℕ × ℕ × List ℕ)) none (fun hA3' _ ↦
              @Nat.rec (fun _ ↦ Option (List ℕ × ℕ × List ℕ)) none (fun hB3' _ ↦
              ih upt uqt rupt ruqt qB3' (hB3' :: hA3' :: hB2' :: hA2' :: hB1' :: hA1' :: hB0' ::
                hA0' :: neg_acc))
              (Nat.add 1 hB3))
              (Nat.add 1 hA3))
              (Nat.add 1 hB2))
              (Nat.add 1 hA2))
              (Nat.add 1 hB1))
              (Nat.add 1 hA1))
              (Nat.add 1 hB0))
              (Nat.add 1 hA0))
              (Nat.add 1 qB3))
        ruqs3) ruqs2) ruqs1) ruQ) rups3) rups2) rups1) ruP) uqs3) uqs2) uqs1) uQ) ups3) ups2) ups1)
          uP)
    quads

private theorem gqsp_splitHadamardQuads_eq (rf B B2 BIAS rem : ℕ) : ∀ (quads : ℕ)
    (uP uQ ruP ruQ : List ℕ) (q_prev : ℕ) (neg_acc : List ℕ), gqsp_splitHadamardQuads rf B B2
    BIAS rem quads uP uQ ruP ruQ q_prev neg_acc = some (gqsp_zwSplitPRev B (8 * quads + rem)
    (gqsp_hadamardFwdAux B (gqsp_interleaveFwd B2 BIAS uP uQ ruP ruQ []) q_prev []) neg_acc)
    := by
  unfold gqsp_splitHadamardQuads
  intro quads
  induction quads with
  | zero =>
      intro uP uQ ruP ruQ q_prev neg_acc
      rw [Nat.mul_zero, Nat.zero_add]
      exact gqsp_splitHadFallback_eq rf B B2 BIAS rem uP uQ ruP ruQ q_prev neg_acc
  | succ q' ih =>
      intro uP uQ ruP ruQ q_prev neg_acc
      dsimp only
      rcases uP with _ | ⟨up0, _ | ⟨up1, _ | ⟨up2, _ | ⟨up3, upt⟩⟩⟩⟩ <;>
        try exact gqsp_splitHadFallback_eq rf B B2 BIAS (8 * (q' + 1) + rem) _ _ _ _ q_prev neg_acc
      rcases uQ with _ | ⟨uq0, _ | ⟨uq1, _ | ⟨uq2, _ | ⟨uq3, uqt⟩⟩⟩⟩ <;>
        try exact gqsp_splitHadFallback_eq rf B B2 BIAS (8 * (q' + 1) + rem) _ _ _ _ q_prev neg_acc
      rcases ruP with _ | ⟨rup0, _ | ⟨rup1, _ | ⟨rup2, _ | ⟨rup3, rupt⟩⟩⟩⟩ <;>
        try exact gqsp_splitHadFallback_eq rf B B2 BIAS (8 * (q' + 1) + rem) _ _ _ _ q_prev neg_acc
      rcases ruQ with _ | ⟨ruq0, _ | ⟨ruq1, _ | ⟨ruq2, _ | ⟨ruq3, ruqt⟩⟩⟩⟩ <;>
        try exact gqsp_splitHadFallback_eq rf B B2 BIAS (8 * (q' + 1) + rem) _ _ _ _ q_prev neg_acc
      dsimp only [gqsp_interleaveFwd, gqsp_hadamardFwdAux]
      rw [gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwForce_eq,
          gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwForce_eq,
          gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwForce_eq, ih]
      congr 1
      have h8 : 8 * (q' + 1) + rem = (8 * q' + rem) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := by omega
      rw[h8, gqsp_zwSplitPRev_cons_succ, gqsp_zwSplitPRev_cons_succ,
          gqsp_zwSplitPRev_cons_succ, gqsp_zwSplitPRev_cons_succ,
          gqsp_zwSplitPRev_cons_succ, gqsp_zwSplitPRev_cons_succ,
          gqsp_zwSplitPRev_cons_succ, gqsp_zwSplitPRev_cons_succ]

noncomputable def gqsp_splitHadamardFromU4 (rf B B2 BIAS M1 : ℕ)
    (uP uQ ruP ruQ : List ℕ) (q_prev : ℕ) (neg_acc : List ℕ) : Option (List ℕ × ℕ × List ℕ) :=
  gqsp_splitHadamardQuads rf B B2 BIAS (Nat.mod M1 8) (Nat.div M1 8) uP uQ ruP ruQ q_prev neg_acc

private theorem gqsp_splitHadamardFromU4_eq (rf B B2 BIAS M1 : ℕ) (uP uQ ruP ruQ : List ℕ)
    (q_prev : ℕ) (neg_acc : List ℕ) : gqsp_splitHadamardFromU4 rf B B2 BIAS M1 uP uQ ruP ruQ
    q_prev neg_acc = some (gqsp_zwSplitPRev B M1 (gqsp_hadamardFwdAux B (gqsp_interleaveFwd
    B2 BIAS uP uQ ruP ruQ []) q_prev []) neg_acc) := by
  unfold gqsp_splitHadamardFromU4
  rw [gqsp_splitHadamardQuads_eq]
  have hdm : 8 * Nat.div M1 8 + Nat.mod M1 8 = M1 := Nat.div_add_mod M1 8
  rw [hdm]

private theorem gqsp_zwForceNonEmptyNat_congr_cons {xs1 xs2 : List ℕ} {f1 f2 : List ℕ → Bool}
    (hxs : xs1 = xs2) (hf : ∀ x xt, f1 (x :: xt) = f2 (x :: xt)) :
    gqsp_zwForceNonEmptyNat xs1 f1 = gqsp_zwForceNonEmptyNat xs2 f2 := by
  subst hxs
  cases xs1
  · rfl
  · dsimp only [gqsp_zwForceNonEmptyNat]
    exact hf _ _

private theorem gqsp_forceNonEmptyPQ_interleaveFwd (B2 BIAS up0 uq0 rup0 ruq0 : ℕ)
    (upt uqt rupt ruqt : List ℕ) (f : List PQPair → Bool) : gqsp_zwForceNonEmptyPQ
    (gqsp_interleaveFwd B2 BIAS (up0 :: upt) (uq0 :: uqt) (rup0 :: rupt) (ruq0 :: ruqt) []) f
    = f (gqsp_interleaveFwd B2 BIAS (up0 :: upt) (uq0 :: uqt) (rup0 :: rupt) (ruq0 :: ruqt)
    []) := rfl

/-- Zero-`pqM`, zero-`p_fin` fused 1-angle root unpack + outer Hadamard + split CPS wrapper
(max flat `List` spine length `≤ M + 5`, `≤ 34,000` C++ stack frames at `M = 135,867`,
  `1x` Hadamard eval). -/
noncomputable def gqsp_withRootFused1AngleAux (rf d M : ℕ) (g0 : DyadicSu2Gate)
    (root : TreeNodeC) (useQResid : Bool)
    (cont : ℕ → List ℕ → ℕ → List ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) : Bool :=
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
                (gqsp_finishRootVec2RealFastAux d n_lanes rep_bcomb
                  c_ar ⟨rprp, rprn⟩ nc_br ⟨rqrp_rev, rqrn_rev⟩)
                (fun uPre ↦
                  gqsp_zwForceNonEmptyNat (gqsp_revNat4 rf uPre []) (fun ruP ↦
                    @Nat.rec (fun _ ↦ Bool) false (fun rprp_rev _ ↦
                      @Nat.rec (fun _ ↦ Bool) false (fun rprn_rev _ ↦
                        gqsp_zwForceNonEmptyNat
                          (gqsp_finishRootVec2RealFastAux d n_lanes rep_bcomb
                            c_ar ⟨rqrp, rqrn⟩ c_br ⟨rprp_rev, rprn_rev⟩)
                          (fun uQre ↦
                            gqsp_zwForceNonEmptyNat (gqsp_revNat4 rf uQre []) (fun ruQ ↦
                              let B := 0x1000000000000000000000000000000000000000000000000000000000000
                              let B2 := 0x2000000000000000000000000000000000000000000000000000000000000
                              let Bw := 0x1000000000000000000000000000000000000000000000000
                              let shift0 := 0x1000000000000000000000000
                              let bias_out := 0xfffffffffffffffffffffc00000000000000000000000000000000000000
                              @Nat.rec (fun _ ↦ Bool) false (fun R_final _ ↦
                                @Nat.rec (fun _ ↦ Bool) false (fun M1 _ ↦
                                  let t3_raw := @Bool.rec (fun _ ↦ ℕ) 0
                                    (gqsp_qResidFromU4 B B2 bias_out R_final rf uPre uQre ruP ruQ B
                                      0)
                                    useQResid
                                  @Nat.rec (fun _ ↦ Bool) false (fun t3 _ ↦
                                    @Option.rec (List ℕ × ℕ × List ℕ) (fun _ ↦ Bool) false
                                      (@Prod.rec (List ℕ) (ℕ × List ℕ) (fun _ ↦
                                        Bool) (fun neg_re p2_re ↦
                                        @Prod.rec ℕ (List ℕ) (fun _ ↦ Bool) (fun pc_re pos_re ↦
                                          cont t3 neg_re pc_re pos_re R_final M1 B B2 Bw shift0)
                                          p2_re))
                                      (gqsp_splitHadamardFromU4 rf B B2 bias_out M1 uPre uQre ruP
                                        ruQ B []))
                                    (Nat.add 1 t3_raw))
                                  (Nat.add 1 (Nat.add 1 M)))
                                (Nat.add 1 (Nat.add 3 (Nat.shiftRight rerr 206))))))
                        (Nat.add 1 (gqsp_fastRev4Swar0 d n_lanes rprn)))
                      (Nat.add 1 (gqsp_fastRev4Swar0 d n_lanes rprp)))))
              (Nat.add 1 (gqsp_fastRev4Swar0 d n_lanes rqrn)))
            (Nat.add 1 (gqsp_fastRev4Swar0 d n_lanes rqrp)))
          (Nat.add 1 (Nat.mul ta_B_COMB rrep1)))
        (Nat.add 1 (Nat.add 1 rdeg)))
    root

theorem gqsp_withRootFused1AngleAux_eq (rf d M : ℕ) (g0 : DyadicSu2Gate) (root : TreeNodeC)
    (useQResid : Bool) (cont : ℕ → List ℕ → ℕ → List ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) :
    gqsp_withRootFused1AngleAux rf d M g0 root useQResid cont = gqsp_zwWithRootSplit1Angle d
    M g0 root (fun pqM neg_re pc_re pos_re R_final M1 B B2 Bw shift0 ↦ cont (@Bool.rec (fun _
    ↦ ℕ) 0 (gqsp_zwQResidHadamard B B2 R_final pqM B 0) useQResid) neg_re pc_re pos_re
    R_final M1 B B2 Bw shift0) := by
  rcases root with ⟨rdeg, rsalt, rrep1, rprp, rprn, rpip, rpin, rqrp, rqrn, rqip, rqin, rerr⟩
  unfold gqsp_withRootFused1AngleAux gqsp_zwWithRootSplit1Angle
  dsimp only
  simp only [gqsp_zwForce_eq, gqsp_fastRev4Swar0_eq]
  apply gqsp_zwForceNonEmptyNat_congr_cons (gqsp_finishRootVec2RealFast_eq _ _ _ _ _ _ _)
  intro up0 upt
  apply gqsp_zwForceNonEmptyNat_congr_cons (gqsp_revNat4_eq rf _ [])
  intro rup0 rupt
  apply gqsp_zwForceNonEmptyNat_congr_cons (gqsp_finishRootVec2RealFast_eq _ _ _ _ _ _ _)
  intro uq0 uqt
  apply gqsp_zwForceNonEmptyNat_congr_cons (gqsp_revNat4_eq rf _ [])
  intro ruq0 ruqt
  rw [gqsp_rev_interleaveFast_eq]
  dsimp only [gqsp_zwRevPQTR]
  rw [gqsp_forceNonEmptyPQ_interleaveFwd]
  rw [gqsp_rev_hadamardFast_eq]
  dsimp only [gqsp_zwRevNatTR]
  rw [gqsp_splitHadamardFromU4_eq, gqsp_qResidFromU4_eq, gqsp_zwQResidFromU_eq]

/-- Fused single-pass `t2 + t3` (`asymDefect + qResid ≤ N_rec_23 * shift0`) post-root check. -/
noncomputable def gqsp_upperRealTreePostT23FastBle
    (rf d fuel M N_rec_23 : ℕ) (ry_g0 : DyadicRyGate) (subNodes : List TreeNodeC) : Bool :=
  @Option.rec TreeNodeC (fun _ ↦ Bool)
    false
    (fun root ↦
      gqsp_withRootFused1AngleAux rf d M (ryToSu2Gate ry_g0) root true
        (fun t3 neg_re _ pos_re R_final M1 B B2 _ shift0 ↦
          let t2 := gqsp_asymDefect4 M1 B B2 R_final neg_re pos_re
          Nat.ble (Nat.add t2 t3) (Nat.mul N_rec_23 shift0)))
    (gqsp_evalTournamentReal0 fuel subNodes)

theorem gqsp_upperRealTreePostT23FastBle_eq (rf d fuel M N_rec_23 : ℕ) (ry_g0 : DyadicRyGate)
    (subNodes : List TreeNodeC) : gqsp_upperRealTreePostT23FastBle rf d fuel M N_rec_23 ry_g0
    subNodes = gqsp_upperRealTreePostT23LowMem2Ble d fuel M N_rec_23 ry_g0 subNodes := by
  unfold gqsp_upperRealTreePostT23FastBle gqsp_upperRealTreePostT23LowMem2Ble
  rw [gqsp_evalTournamentReal0_eq]
  cases gqsp_zwEvalTournamentReal fuel subNodes
  · rfl
  · dsimp only
    rw [gqsp_withRootFused1AngleAux_eq]
    congr 1
    funext pqM neg_re pc_re pos_re R_final M1 B B2 Bw shift0
    dsimp only
    rw [gqsp_asymDefect4_eq]

/-- Fused split `t1`-only (`chebL1 ≤ N_rec_1 * shift0`) post-root auxiliary check. -/
noncomputable def gqsp_upperRealTreePostT1BleAux
    (rf d fuel M N_rec_1 W_err_d0 W_err_dpos pad : ℕ) (ry_g0 : DyadicRyGate)
    (subNodes : List TreeNodeC) (ws_unpad : List ℕ) : Bool := @Option.rec TreeNodeC
    (fun _ ↦ Bool) false (fun root ↦ gqsp_withRootFused1AngleAux rf d M (ryToSu2Gate ry_g0)
    root false (fun _ neg_re pc_re pos_re R_final M1 B B2 Bw shift0 ↦ Nat.ble
    (gqsp_chebL1POnly4 M1 B B2 Bw R_final W_err_d0 W_err_dpos pad neg_re pc_re pos_re
    ws_unpad) (Nat.mul N_rec_1 shift0))) (gqsp_evalTournamentReal0 fuel subNodes)

private theorem gqsp_upperRealTreePostT1BleAux_eq
    (rf d fuel M N_rec_1 W_err_d0 W_err_dpos pad : ℕ)
    (ry_g0 : DyadicRyGate) (subNodes : List TreeNodeC) (ws_unpad : List ℕ) :
    gqsp_upperRealTreePostT1BleAux rf d fuel M N_rec_1 W_err_d0 W_err_dpos pad ry_g0 subNodes
      ws_unpad =
      gqsp_upperRealTreePostT1LowMem2Ble d fuel M N_rec_1 W_err_d0 W_err_dpos pad ry_g0 subNodes
        ws_unpad := by
  unfold gqsp_upperRealTreePostT1BleAux gqsp_upperRealTreePostT1LowMem2Ble
  rw [gqsp_evalTournamentReal0_eq]
  cases gqsp_zwEvalTournamentReal fuel subNodes
  · rfl
  · dsimp only
    rw [gqsp_withRootFused1AngleAux_eq]
    congr 1
    funext pqM neg_re pc_re pos_re R_final M1 B B2 Bw shift0
    rw [gqsp_chebL1POnly4_eq]

/-- Fused split `t1`-only (`chebL1 ≤ N_rec_1 * shift0`) post-root check (`≤ M+5` list spine). -/
noncomputable def gqsp_upperRealTreePostT1Ble (d fuel M N_rec_1 W_err_d0 W_err_dpos pad : ℕ)
    (ry_g0 : DyadicRyGate) (subNodes : List TreeNodeC) (ws_unpad : List ℕ) : Bool :=
    gqsp_upperRealTreePostT1BleAux (Nat.add 16 (Nat.div M 4)) d fuel M N_rec_1 W_err_d0
    W_err_dpos pad ry_g0 subNodes ws_unpad

theorem gqsp_upperRealTreePostT1Ble_eq (d fuel M N_rec_1 W_err_d0 W_err_dpos pad : ℕ)
    (ry_g0 : DyadicRyGate) (subNodes : List TreeNodeC) (ws_unpad : List ℕ) :
    gqsp_upperRealTreePostT1Ble d fuel M N_rec_1 W_err_d0 W_err_dpos pad ry_g0 subNodes
    ws_unpad = gqsp_upperRealTreePostT1LowMem2Ble d fuel M N_rec_1 W_err_d0 W_err_dpos pad
    ry_g0 subNodes ws_unpad := gqsp_upperRealTreePostT1BleAux_eq (Nat.add 16 (Nat.div M 4)) d
    fuel M N_rec_1 W_err_d0 W_err_dpos pad ry_g0 subNodes ws_unpad

set_option maxHeartbeats 4800000 in
-- Packed 8-shard upper post-root certificate kernel evaluation.
theorem aux_b135598_m135867_upper_t23_fast : gqsp_upperRealTreePostT23FastBle 34000 18 20
    135867 5601697873 b135598_m135867_ry_g0 [b135598_m135867_shard_0_node,
    b135598_m135867_shard_1_node, b135598_m135867_shard_2_node, b135598_m135867_shard_3_node,
    b135598_m135867_shard_4_node, b135598_m135867_shard_5_node, b135598_m135867_shard_6_node,
    b135598_m135867_shard_7_node] = true := by
  decide +kernel

/-- Single-pass `t2 + t3` post-root bound at `β = 135,598, M = 135,867`
(`N_rec_23 = 5601697873`). -/
theorem gqsp_b135598_m135867_upper_t23_ok_g0 : gqsp_upperRealTreePostT23LowMem2Ble 18 20
    135867 5601697873 b135598_m135867_ry_g0 [b135598_m135867_shard_0_node,
    b135598_m135867_shard_1_node, b135598_m135867_shard_2_node, b135598_m135867_shard_3_node,
    b135598_m135867_shard_4_node, b135598_m135867_shard_5_node, b135598_m135867_shard_6_node,
    b135598_m135867_shard_7_node] = true := by
  rw [← gqsp_upperRealTreePostT23FastBle_eq 34000]
  exact aux_b135598_m135867_upper_t23_fast

end UpperPostT23
end GqspUpperPostT23_135598
end QuantumComputation.Specs.StoppingPowerSolution
end
