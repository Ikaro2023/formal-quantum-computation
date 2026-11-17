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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.GqspCatCodesH2

@[expose] public section
set_option compiler.extract_closed false
set_option exponentiation.threshold 2048
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

namespace GqspBaseTree135598
export GqspCatCheck135598
  (b135598_m135867_C_orig_list gqsp_b135598_m135867_co_ok)

section BaseCert135598
set_option maxRecDepth 4000000
open TFreeLaurentGQSP (DyadicRyGate)
open GeneralBetaAndAlphaTopEndpoint (GeneralBetaSegmentCert)
open GqspWronskian62592
open GqspWronskianUV135598
open GqspWronskian135598
open GqspTreeBaseHelpers135598
open GqspTreeShardMerge135598
open GqspTreeSubShards01_135598
open GqspTreeSubShards23_135598
open GqspTreeSubShards45_135598
open GqspTreeSubShards67_135598
open GqspUpperPost135598
open GqspCatData135598
open GqspCatCheck135598

theorem gqsp_mapRyChunksSlices8_eq
    (ry_all s0 s1 s2 s3 s4 s5 s6 s7 : List (List DyadicRyGate))
    (hry : ry_all = [s0, s1, s2, s3, s4, s5, s6, s7].flatten) : [(gqsp_mapRyChunksToSu2
    s0).flatten, (gqsp_mapRyChunksToSu2 s1).flatten, (gqsp_mapRyChunksToSu2 s2).flatten,
    (gqsp_mapRyChunksToSu2 s3).flatten, (gqsp_mapRyChunksToSu2 s4).flatten,
    (gqsp_mapRyChunksToSu2 s5).flatten, (gqsp_mapRyChunksToSu2 s6).flatten,
    (gqsp_mapRyChunksToSu2 s7).flatten].flatten = ry_all.flatten.map ryToSu2Gate := by
  subst hry
  exact gqsp_mapRyChunksSlices_flatten [s0, s1, s2, s3, s4, s5, s6, s7]

/-- Certified unrounded base `GeneralBetaSegmentCert 135598 135867 27343005582`. -/
noncomputable def gqsp_BaseCert : GeneralBetaSegmentCert 135598 135867 27343005582 :=
  gqsp_mkBaseGeneralBetaSegmentCertRealChunkShards2 18 20 135867 409600 135598
    27342870269 1 135312 27343005582
    gqsp_b135598_k409600_W_err_d0 gqsp_b135598_k409600_W_err_dpos 272802
    b135598_m135867_C_orig_list b135598_m135867_ry_g0 b135598_m135867_ry_chs
    [b135598_m135867_shard_0_node, b135598_m135867_shard_1_node, b135598_m135867_shard_2_node,
      b135598_m135867_shard_3_node, b135598_m135867_shard_4_node, b135598_m135867_shard_5_node,
      b135598_m135867_shard_6_node, b135598_m135867_shard_7_node]
    [(gqsp_mapRyChunksToSu2 b135598_m135867_ry_chs_0).flatten,
     (gqsp_mapRyChunksToSu2 b135598_m135867_ry_chs_1).flatten,
     (gqsp_mapRyChunksToSu2 b135598_m135867_ry_chs_2).flatten,
     (gqsp_mapRyChunksToSu2 b135598_m135867_ry_chs_3).flatten,
     (gqsp_mapRyChunksToSu2 b135598_m135867_ry_chs_4).flatten,
     (gqsp_mapRyChunksToSu2 b135598_m135867_ry_chs_5).flatten,
     (gqsp_mapRyChunksToSu2 b135598_m135867_ry_chs_6).flatten,
     (gqsp_mapRyChunksToSu2 b135598_m135867_ry_chs_7).flatten]
    gqsp_b135598_k409600_ws_unpad
    (by decide) (by decide) (by decide)
    (by rw [gqsp_b135598_k409600_ws_unpad_len]; decide)
    (by rw [gqsp_b135598_k409600_ws_unpad_len])
    (fun k hk ↦ by
      rw [gqsp_b135598_k409600_ws_unpad_append_eq]
      exact gqsp_b135598_k409600_ws_hws_err k hk)
    gqsp_b135598_k409600_tay_nat
    (by decide)
    gqsp_b135598_m135867_co_ok
    gqsp_b135598_m135867_ry_ok
    aux_b135598_m135867_cat_ble
    (List.Forall₂.cons b135598_m135867_shard_0_valid (List.Forall₂.cons
      b135598_m135867_shard_1_valid (List.Forall₂.cons b135598_m135867_shard_2_valid
      (List.Forall₂.cons b135598_m135867_shard_3_valid (List.Forall₂.cons
      b135598_m135867_shard_4_valid (List.Forall₂.cons b135598_m135867_shard_5_valid
      (List.Forall₂.cons b135598_m135867_shard_6_valid (List.Forall₂.cons
      b135598_m135867_shard_7_valid List.Forall₂.nil))))))))
    (gqsp_mapRyChunksSlices8_eq b135598_m135867_ry_chs b135598_m135867_ry_chs_0
      b135598_m135867_ry_chs_1 b135598_m135867_ry_chs_2 b135598_m135867_ry_chs_3
      b135598_m135867_ry_chs_4 b135598_m135867_ry_chs_5 b135598_m135867_ry_chs_6
      b135598_m135867_ry_chs_7 rfl)
    gqsp_b135598_m135867_upper_post_ok

theorem gqsp_BaseCert_C (i : Fin (135867 + 1)) : gqsp_BaseCert.C i = Fin.ofNat (2 ^ 42)
    (b135598_m135867_C_orig_list.getD i.val 0) := rfl

end BaseCert135598

section TiersFast8_135598
set_option maxRecDepth 4000000
open GqspWronskian62592
open GqspTreeBaseHelpers135598

/-- 8-step `@Nat.rec`-unrolled zero-cache `List ℕ` reversal (`≤ 17,000` frames at `M = 135,867`). -/
noncomputable def gqsp_revNat8 (fuel : ℕ) : List ℕ → List ℕ → List ℕ := @Nat.rec
    (fun _ ↦ List ℕ → List ℕ → List ℕ) gqsp_zwRevNatTR (fun _ ih xs acc ↦ @List.rec ℕ (fun _
    ↦ List ℕ) acc (fun x0 r1 _ ↦ @List.rec ℕ (fun _ ↦ List ℕ) (x0 :: acc) (fun x1 r2 _ ↦
    @List.rec ℕ (fun _ ↦ List ℕ) (x1 :: x0 :: acc) (fun x2 r3 _ ↦ @List.rec ℕ (fun _ ↦ List ℕ)
    (x2 :: x1 :: x0 :: acc) (fun x3 r4 _ ↦ @List.rec ℕ (fun _ ↦ List ℕ) (x3 :: x2 :: x1 :: x0
    :: acc) (fun x4 r5 _ ↦ @List.rec ℕ (fun _ ↦ List ℕ) (x4 :: x3 :: x2 :: x1 :: x0 :: acc)
    (fun x5 r6 _ ↦ @List.rec ℕ (fun _ ↦ List ℕ) (x5 :: x4 :: x3 :: x2 :: x1 :: x0 :: acc) (fun
    x6 r7 _ ↦ @List.rec ℕ (fun _ ↦ List ℕ) (x6 :: x5 :: x4 :: x3 :: x2 :: x1 :: x0 :: acc)
    (fun x7 r8 _ ↦ ih r8 (x7 :: x6 :: x5 :: x4 :: x3 :: x2 :: x1 :: x0 :: acc)) r7) r6) r5)
    r4) r3) r2) r1) xs) fuel

/-- 8-step `@Nat.rec`-unrolled strict-element `List ℕ` reversal (`≤ 17,000` frames). -/
noncomputable def gqsp_strictRev8 (fuel : ℕ) : List ℕ → List ℕ → List ℕ :=
  @Nat.rec (fun _ ↦ List ℕ → List ℕ → List ℕ)
    gqsp_zwStrictRevNatTR
    (fun _ ih xs acc ↦
      let fb := gqsp_zwStrictRevNatTR xs acc
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun x0 r1 _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun x1 r2 _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun x2 r3 _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun x3 r4 _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun x4 r5 _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun x5 r6 _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun x6 r7 _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun x7 r8 _ ↦
        @Nat.rec (fun _ ↦ List ℕ) [] (fun x0' _ ↦
        @Nat.rec (fun _ ↦ List ℕ) [] (fun x1' _ ↦
        @Nat.rec (fun _ ↦ List ℕ) [] (fun x2' _ ↦
        @Nat.rec (fun _ ↦ List ℕ) [] (fun x3' _ ↦
        @Nat.rec (fun _ ↦ List ℕ) [] (fun x4' _ ↦
        @Nat.rec (fun _ ↦ List ℕ) [] (fun x5' _ ↦
        @Nat.rec (fun _ ↦ List ℕ) [] (fun x6' _ ↦
        @Nat.rec (fun _ ↦ List ℕ) [] (fun x7' _ ↦
          ih r8 (x7' :: x6' :: x5' :: x4' :: x3' :: x2' :: x1' :: x0' :: acc))
          (Nat.add 1 x7)) (Nat.add 1 x6)) (Nat.add 1 x5)) (Nat.add 1 x4))
          (Nat.add 1 x3)) (Nat.add 1 x2)) (Nat.add 1 x1)) (Nat.add 1 x0))
        r7) r6) r5) r4) r3) r2) r1) xs)
    fuel

/-- Evaluates `xs` strictly in `≤ 17,000` frames and shares the strict `List ℕ` spine across `k`. -/
noncomputable def gqsp_withStrictList8 {α : Type} (fuel : ℕ) (xs : List ℕ) (k : List ℕ → α) : α :=
  gqsp_tf_shareHeadList (gqsp_revNat8 fuel (gqsp_strictRev8 fuel xs []) []) k

/-- Fast `7`-bit delta block unpacker with 8-step unrolled output reversal. -/
noncomputable def gqsp_fastDecDelta7Blocks8 (fuel : ℕ) (c_orig : List ℕ)
    (bss0 : List (List (ℕ × ℕ))) : List ℕ := @List.rec (List (ℕ × ℕ))
    (fun _ ↦ List ℕ → List ℕ → List ℕ) (fun _ acc ↦ gqsp_revNat8 fuel acc []) (fun ws _ ih cs
    acc ↦ @Prod.rec (List ℕ) (List ℕ) (fun _ ↦ List ℕ) (fun cs' acc' ↦ ih cs' acc') (@List.rec
    (ℕ × ℕ) (fun _ ↦ List ℕ → List ℕ → List ℕ × List ℕ) (fun cs1 acc1 ↦ (cs1, acc1)) (fun hw _
    ihw cs1 acc1 ↦ @Prod.rec ℕ ℕ (fun _ ↦ List ℕ × List ℕ) (fun cnt w ↦ @Prod.rec (List ℕ)
    (List ℕ) (fun _ ↦ List ℕ × List ℕ) (fun cs2 acc2 ↦ ihw cs2 acc2)
    (gqsp_tf_fastDecDelta7Word cnt w cs1 acc1)) hw) ws cs acc)) bss0 c_orig []

/-- Fast sparse tier patch block unpacker with 8-step unrolled output reversal. -/
noncomputable def gqsp_fastDecPatchBlocks8 (fuel : ℕ) (c_orig c_prev : List ℕ)
    (bss0 : List (List (ℕ × ℕ))) : List ℕ := @List.rec (List (ℕ × ℕ))
    (fun _ ↦ List ℕ → List ℕ → List ℕ → List ℕ) (fun _ _ acc ↦ gqsp_revNat8 fuel acc []) (fun
    ws _ ih cs ps acc ↦ @Prod.rec (List ℕ) (List ℕ × List ℕ) (fun _ ↦ List ℕ) (fun cs' p_pa ↦
    @Prod.rec (List ℕ) (List ℕ) (fun _ ↦ List ℕ) (fun ps' acc' ↦ ih cs' ps' acc') p_pa)
    (@List.rec (ℕ × ℕ) (fun _ ↦ List ℕ → List ℕ → List ℕ → List ℕ × (List ℕ × List ℕ)) (fun
    cs1 ps1 acc1 ↦ (cs1, (ps1, acc1))) (fun hw _ ihw cs1 ps1 acc1 ↦ @Prod.rec ℕ ℕ (fun _ ↦
    List ℕ × (List ℕ × List ℕ)) (fun cnt w ↦ @Prod.rec (List ℕ) (List ℕ × List ℕ) (fun _ ↦
    List ℕ × (List ℕ × List ℕ)) (fun cs2 p_pa2 ↦ @Prod.rec (List ℕ) (List ℕ) (fun _ ↦ List ℕ ×
    (List ℕ × List ℕ)) (fun ps2 acc2 ↦ ihw cs2 ps2 acc2) p_pa2) (gqsp_tf_fastDecPatchWord cnt
    w cs1 ps1 acc1)) hw) ws cs ps acc)) bss0 c_orig c_prev []

/-- Public `k0`-step inner tier chunk step (must NOT be `private` under `module` so `13c1..c3`
reduce it). -/
noncomputable abbrev tierStepK (n_exp d_exp rot_exp k0 : ℕ) :
    List ℕ → ℕ → List ℕ → Sum Bool (ℕ × List ℕ × List ℕ) :=
  @Nat.rec (fun _ ↦ List ℕ → ℕ → List ℕ → Sum Bool (ℕ × List ℕ × List ℕ))
    (fun cr acc co ↦ Sum.inr (acc, cr, co))
    (fun _ ihk cr0 acc0 co0 ↦
      @List.rec ℕ (fun _ ↦ ℕ → List ℕ → Sum Bool (ℕ × List ℕ × List ℕ))
        (fun acc co ↦
          Sum.inl
            (@List.rec ℕ (fun _ ↦ Bool)
              (Bool.and (Nat.beq (Nat.land acc 0xffffffffffffffff) n_exp)
                (Bool.and (Nat.beq (Nat.land (Nat.shiftRight acc 64) 0xffffffffffffffff) d_exp)
                  (Nat.beq (Nat.shiftRight acc 128) rot_exp)))
              (fun _ _ _ ↦ false)
              co))
        (fun cr crt _ acc co ↦
          @List.rec ℕ (fun _ ↦ ℕ → List ℕ → ℕ → Sum Bool (ℕ × List ℕ × List ℕ))
            (fun _ _ _ ↦ Sum.inl false)
            (fun coh cot _ cr1 crt1 acc1 ↦
              @Bool.rec (fun _ ↦ ℕ → ℕ → List ℕ → List ℕ → ℕ → Sum Bool (ℕ × List ℕ × List ℕ))
                (fun _ _ _ _ _ ↦ Sum.inl false)
                (fun cr2 coh2 crt2 cot2 acc2 ↦
                  @Nat.rec (fun _ ↦ Sum Bool (ℕ × List ℕ × List ℕ)) (Sum.inl false)
                    (fun acc' _ ↦ ihk crt2 acc' cot2)
                    (Nat.add 1
                    (Nat.add acc2
                      (Nat.add 1
                        (Nat.add (Nat.shiftLeft (Nat.add (Nat.sub cr2 coh2) (Nat.sub coh2 cr2)) 64)
                          (Nat.shiftLeft (Nat.mul 2 (Nat.sub (Nat.sub 42 (@Bool.rec (fun _ ↦ ℕ →
                            ℕ) (fun y42 : ℕ ↦ (@Bool.rec (fun _ ↦ ℕ → ℕ) (fun y32 : ℕ ↦ (@Bool.rec
                            (fun _ ↦ ℕ → ℕ) (fun y16 : ℕ ↦ (@Bool.rec (fun _ ↦ ℕ → ℕ) (fun y8 : ℕ
                            ↦ (@Bool.rec (fun _ ↦ ℕ → ℕ) (fun y4 : ℕ ↦ (@Bool.rec (fun _ ↦ ℕ → ℕ)
                            (fun y2 : ℕ ↦ (@Bool.rec (fun _ ↦ ℕ) 0 1 (Nat.beq (Nat.land (Nat.land
                            y2 1) 1) 0))) (fun y2 : ℕ ↦ Nat.add 1 (@Bool.rec (fun _ ↦ ℕ) 0 1
                            (Nat.beq (Nat.land (Nat.shiftRight y2 1) 1) 0))) (Nat.beq (Nat.land
                            (Nat.land y4 3) 1) 0) (Nat.land y4 3))) (fun y4 : ℕ ↦ Nat.add 2
                            (@Bool.rec (fun _ ↦ ℕ → ℕ) (fun y2 : ℕ ↦ (@Bool.rec (fun _ ↦ ℕ) 0 1
                            (Nat.beq (Nat.land (Nat.land y2 1) 1) 0))) (fun y2 : ℕ ↦ Nat.add 1
                            (@Bool.rec (fun _ ↦ ℕ) 0 1 (Nat.beq (Nat.land (Nat.shiftRight y2 1) 1)
                            0))) (Nat.beq (Nat.land (Nat.shiftRight y4 2) 1) 0) (Nat.shiftRight y4
                            2))) (Nat.beq (Nat.land (Nat.land y8 15) 3) 0) (Nat.land y8 15))) (fun
                            y8 : ℕ ↦ Nat.add 4 (@Bool.rec (fun _ ↦ ℕ → ℕ) (fun y4 : ℕ ↦ (@Bool.rec
                            (fun _ ↦ ℕ → ℕ) (fun y2 : ℕ ↦ (@Bool.rec (fun _ ↦ ℕ) 0 1 (Nat.beq
                            (Nat.land (Nat.land y2 1) 1) 0))) (fun y2 : ℕ ↦ Nat.add 1 (@Bool.rec
                            (fun _ ↦ ℕ) 0 1 (Nat.beq (Nat.land (Nat.shiftRight y2 1) 1) 0)))
                            (Nat.beq (Nat.land (Nat.land y4 3) 1) 0) (Nat.land y4 3))) (fun y4 : ℕ
                            ↦ Nat.add 2 (@Bool.rec (fun _ ↦ ℕ → ℕ) (fun y2 : ℕ ↦ (@Bool.rec (fun _
                            ↦ ℕ) 0 1 (Nat.beq (Nat.land (Nat.land y2 1) 1) 0))) (fun y2 : ℕ ↦
                            Nat.add 1 (@Bool.rec (fun _ ↦ ℕ) 0 1 (Nat.beq (Nat.land
                            (Nat.shiftRight y2 1) 1) 0))) (Nat.beq (Nat.land (Nat.shiftRight y4 2)
                            1) 0) (Nat.shiftRight y4 2))) (Nat.beq (Nat.land (Nat.shiftRight y8 4)
                            3) 0) (Nat.shiftRight y8 4))) (Nat.beq (Nat.land (Nat.land y16 255)
                            15) 0) (Nat.land y16 255))) (fun y16 : ℕ ↦ Nat.add 8 (@Bool.rec (fun _
                            ↦ ℕ → ℕ) (fun y8 : ℕ ↦ (@Bool.rec (fun _ ↦ ℕ → ℕ) (fun y4 : ℕ ↦
                            (@Bool.rec (fun _ ↦ ℕ → ℕ) (fun y2 : ℕ ↦ (@Bool.rec (fun _ ↦ ℕ) 0 1
                            (Nat.beq (Nat.land (Nat.land y2 1) 1) 0))) (fun y2 : ℕ ↦ Nat.add 1
                            (@Bool.rec (fun _ ↦ ℕ) 0 1 (Nat.beq (Nat.land (Nat.shiftRight y2 1) 1)
                            0))) (Nat.beq (Nat.land (Nat.land y4 3) 1) 0) (Nat.land y4 3))) (fun
                            y4 : ℕ ↦ Nat.add 2 (@Bool.rec (fun _ ↦ ℕ → ℕ) (fun y2 : ℕ ↦ (@Bool.rec
                            (fun _ ↦ ℕ) 0 1 (Nat.beq (Nat.land (Nat.land y2 1) 1) 0))) (fun y2 : ℕ
                            ↦ Nat.add 1 (@Bool.rec (fun _ ↦ ℕ) 0 1 (Nat.beq (Nat.land
                            (Nat.shiftRight y2 1) 1) 0))) (Nat.beq (Nat.land (Nat.shiftRight y4 2)
                            1) 0) (Nat.shiftRight y4 2))) (Nat.beq (Nat.land (Nat.land y8 15) 3)
                            0) (Nat.land y8 15))) (fun y8 : ℕ ↦ Nat.add 4 (@Bool.rec (fun _ ↦ ℕ →
                            ℕ) (fun y4 : ℕ ↦ (@Bool.rec (fun _ ↦ ℕ → ℕ) (fun y2 : ℕ ↦ (@Bool.rec
                            (fun _ ↦ ℕ) 0 1 (Nat.beq (Nat.land (Nat.land y2 1) 1) 0))) (fun y2 : ℕ
                            ↦ Nat.add 1 (@Bool.rec (fun _ ↦ ℕ) 0 1 (Nat.beq (Nat.land
                            (Nat.shiftRight y2 1) 1) 0))) (Nat.beq (Nat.land (Nat.land y4 3) 1) 0)
                            (Nat.land y4 3))) (fun y4 : ℕ ↦ Nat.add 2 (@Bool.rec (fun _ ↦ ℕ → ℕ)
                            (fun y2 : ℕ ↦ (@Bool.rec (fun _ ↦ ℕ) 0 1 (Nat.beq (Nat.land (Nat.land
                            y2 1) 1) 0))) (fun y2 : ℕ ↦ Nat.add 1 (@Bool.rec (fun _ ↦ ℕ) 0 1
                            (Nat.beq (Nat.land (Nat.shiftRight y2 1) 1) 0))) (Nat.beq (Nat.land
                            (Nat.shiftRight y4 2) 1) 0) (Nat.shiftRight y4 2))) (Nat.beq (Nat.land
                            (Nat.shiftRight y8 4) 3) 0) (Nat.shiftRight y8 4))) (Nat.beq (Nat.land
                            (Nat.shiftRight y16 8) 15) 0) (Nat.shiftRight y16 8))) (Nat.beq
                            (Nat.land (Nat.land y32 65535) 255) 0) (Nat.land y32 65535))) (fun y32
                            : ℕ ↦ Nat.add 16 (@Bool.rec (fun _ ↦ ℕ → ℕ) (fun y16 : ℕ ↦ (@Bool.rec
                            (fun _ ↦ ℕ → ℕ) (fun y8 : ℕ ↦ (@Bool.rec (fun _ ↦ ℕ → ℕ) (fun y4 : ℕ ↦
                            (@Bool.rec (fun _ ↦ ℕ → ℕ) (fun y2 : ℕ ↦ (@Bool.rec (fun _ ↦ ℕ) 0 1
                            (Nat.beq (Nat.land (Nat.land y2 1) 1) 0))) (fun y2 : ℕ ↦ Nat.add 1
                            (@Bool.rec (fun _ ↦ ℕ) 0 1 (Nat.beq (Nat.land (Nat.shiftRight y2 1) 1)
                            0))) (Nat.beq (Nat.land (Nat.land y4 3) 1) 0) (Nat.land y4 3))) (fun
                            y4 : ℕ ↦ Nat.add 2 (@Bool.rec (fun _ ↦ ℕ → ℕ) (fun y2 : ℕ ↦ (@Bool.rec
                            (fun _ ↦ ℕ) 0 1 (Nat.beq (Nat.land (Nat.land y2 1) 1) 0))) (fun y2 : ℕ
                            ↦ Nat.add 1 (@Bool.rec (fun _ ↦ ℕ) 0 1 (Nat.beq (Nat.land
                            (Nat.shiftRight y2 1) 1) 0))) (Nat.beq (Nat.land (Nat.shiftRight y4 2)
                            1) 0) (Nat.shiftRight y4 2))) (Nat.beq (Nat.land (Nat.land y8 15) 3)
                            0) (Nat.land y8 15))) (fun y8 : ℕ ↦ Nat.add 4 (@Bool.rec (fun _ ↦ ℕ →
                            ℕ) (fun y4 : ℕ ↦ (@Bool.rec (fun _ ↦ ℕ → ℕ) (fun y2 : ℕ ↦ (@Bool.rec
                            (fun _ ↦ ℕ) 0 1 (Nat.beq (Nat.land (Nat.land y2 1) 1) 0))) (fun y2 : ℕ
                            ↦ Nat.add 1 (@Bool.rec (fun _ ↦ ℕ) 0 1 (Nat.beq (Nat.land
                            (Nat.shiftRight y2 1) 1) 0))) (Nat.beq (Nat.land (Nat.land y4 3) 1) 0)
                            (Nat.land y4 3))) (fun y4 : ℕ ↦ Nat.add 2 (@Bool.rec (fun _ ↦ ℕ → ℕ)
                            (fun y2 : ℕ ↦ (@Bool.rec (fun _ ↦ ℕ) 0 1 (Nat.beq (Nat.land (Nat.land
                            y2 1) 1) 0))) (fun y2 : ℕ ↦ Nat.add 1 (@Bool.rec (fun _ ↦ ℕ) 0 1
                            (Nat.beq (Nat.land (Nat.shiftRight y2 1) 1) 0))) (Nat.beq (Nat.land
                            (Nat.shiftRight y4 2) 1) 0) (Nat.shiftRight y4 2))) (Nat.beq (Nat.land
                            (Nat.shiftRight y8 4) 3) 0) (Nat.shiftRight y8 4))) (Nat.beq (Nat.land
                            (Nat.land y16 255) 15) 0) (Nat.land y16 255))) (fun y16 : ℕ ↦ Nat.add
                            8 (@Bool.rec (fun _ ↦ ℕ → ℕ) (fun y8 : ℕ ↦ (@Bool.rec (fun _ ↦ ℕ → ℕ)
                            (fun y4 : ℕ ↦ (@Bool.rec (fun _ ↦ ℕ → ℕ) (fun y2 : ℕ ↦ (@Bool.rec (fun
                            _ ↦ ℕ) 0 1 (Nat.beq (Nat.land (Nat.land y2 1) 1) 0))) (fun y2 : ℕ ↦
                            Nat.add 1 (@Bool.rec (fun _ ↦ ℕ) 0 1 (Nat.beq (Nat.land
                            (Nat.shiftRight y2 1) 1) 0))) (Nat.beq (Nat.land (Nat.land y4 3) 1) 0)
                            (Nat.land y4 3))) (fun y4 : ℕ ↦ Nat.add 2 (@Bool.rec (fun _ ↦ ℕ → ℕ)
                            (fun y2 : ℕ ↦ (@Bool.rec (fun _ ↦ ℕ) 0 1 (Nat.beq (Nat.land (Nat.land
                            y2 1) 1) 0))) (fun y2 : ℕ ↦ Nat.add 1 (@Bool.rec (fun _ ↦ ℕ) 0 1
                            (Nat.beq (Nat.land (Nat.shiftRight y2 1) 1) 0))) (Nat.beq (Nat.land
                            (Nat.shiftRight y4 2) 1) 0) (Nat.shiftRight y4 2))) (Nat.beq (Nat.land
                            (Nat.land y8 15) 3) 0) (Nat.land y8 15))) (fun y8 : ℕ ↦ Nat.add 4
                            (@Bool.rec (fun _ ↦ ℕ → ℕ) (fun y4 : ℕ ↦ (@Bool.rec (fun _ ↦ ℕ → ℕ)
                            (fun y2 : ℕ ↦ (@Bool.rec (fun _ ↦ ℕ) 0 1 (Nat.beq (Nat.land (Nat.land
                            y2 1) 1) 0))) (fun y2 : ℕ ↦ Nat.add 1 (@Bool.rec (fun _ ↦ ℕ) 0 1
                            (Nat.beq (Nat.land (Nat.shiftRight y2 1) 1) 0))) (Nat.beq (Nat.land
                            (Nat.land y4 3) 1) 0) (Nat.land y4 3))) (fun y4 : ℕ ↦ Nat.add 2
                            (@Bool.rec (fun _ ↦ ℕ → ℕ) (fun y2 : ℕ ↦ (@Bool.rec (fun _ ↦ ℕ) 0 1
                            (Nat.beq (Nat.land (Nat.land y2 1) 1) 0))) (fun y2 : ℕ ↦ Nat.add 1
                            (@Bool.rec (fun _ ↦ ℕ) 0 1 (Nat.beq (Nat.land (Nat.shiftRight y2 1) 1)
                            0))) (Nat.beq (Nat.land (Nat.shiftRight y4 2) 1) 0) (Nat.shiftRight y4
                            2))) (Nat.beq (Nat.land (Nat.shiftRight y8 4) 3) 0) (Nat.shiftRight y8
                            4))) (Nat.beq (Nat.land (Nat.shiftRight y16 8) 15) 0) (Nat.shiftRight
                            y16 8))) (Nat.beq (Nat.land (Nat.shiftRight y32 16) 255) 0)
                            (Nat.shiftRight y32 16))) (Nat.beq (Nat.land (Nat.land y42 4294967295)
                            65535) 0) (Nat.land y42 4294967295))) (fun y42 : ℕ ↦ Nat.add 32
                            (@Bool.rec (fun _ ↦ ℕ → ℕ) (fun y10 : ℕ ↦ (@Bool.rec (fun _ ↦ ℕ → ℕ)
                            (fun y8 : ℕ ↦ (@Bool.rec (fun _ ↦ ℕ → ℕ) (fun y4 : ℕ ↦ (@Bool.rec (fun
                            _ ↦ ℕ → ℕ) (fun y2 : ℕ ↦ (@Bool.rec (fun _ ↦ ℕ) 0 1 (Nat.beq (Nat.land
                            (Nat.land y2 1) 1) 0))) (fun y2 : ℕ ↦ Nat.add 1 (@Bool.rec (fun _ ↦ ℕ)
                            0 1 (Nat.beq (Nat.land (Nat.shiftRight y2 1) 1) 0))) (Nat.beq
                            (Nat.land (Nat.land y4 3) 1) 0) (Nat.land y4 3))) (fun y4 : ℕ ↦
                            Nat.add 2 (@Bool.rec (fun _ ↦ ℕ → ℕ) (fun y2 : ℕ ↦ (@Bool.rec (fun _ ↦
                            ℕ) 0 1 (Nat.beq (Nat.land (Nat.land y2 1) 1) 0))) (fun y2 : ℕ ↦
                            Nat.add 1 (@Bool.rec (fun _ ↦ ℕ) 0 1 (Nat.beq (Nat.land
                            (Nat.shiftRight y2 1) 1) 0))) (Nat.beq (Nat.land (Nat.shiftRight y4 2)
                            1) 0) (Nat.shiftRight y4 2))) (Nat.beq (Nat.land (Nat.land y8 15) 3)
                            0) (Nat.land y8 15))) (fun y8 : ℕ ↦ Nat.add 4 (@Bool.rec (fun _ ↦ ℕ →
                            ℕ) (fun y4 : ℕ ↦ (@Bool.rec (fun _ ↦ ℕ → ℕ) (fun y2 : ℕ ↦ (@Bool.rec
                            (fun _ ↦ ℕ) 0 1 (Nat.beq (Nat.land (Nat.land y2 1) 1) 0))) (fun y2 : ℕ
                            ↦ Nat.add 1 (@Bool.rec (fun _ ↦ ℕ) 0 1 (Nat.beq (Nat.land
                            (Nat.shiftRight y2 1) 1) 0))) (Nat.beq (Nat.land (Nat.land y4 3) 1) 0)
                            (Nat.land y4 3))) (fun y4 : ℕ ↦ Nat.add 2 (@Bool.rec (fun _ ↦ ℕ → ℕ)
                            (fun y2 : ℕ ↦ (@Bool.rec (fun _ ↦ ℕ) 0 1 (Nat.beq (Nat.land (Nat.land
                            y2 1) 1) 0))) (fun y2 : ℕ ↦ Nat.add 1 (@Bool.rec (fun _ ↦ ℕ) 0 1
                            (Nat.beq (Nat.land (Nat.shiftRight y2 1) 1) 0))) (Nat.beq (Nat.land
                            (Nat.shiftRight y4 2) 1) 0) (Nat.shiftRight y4 2))) (Nat.beq (Nat.land
                            (Nat.shiftRight y8 4) 3) 0) (Nat.shiftRight y8 4))) (Nat.beq (Nat.land
                            (Nat.land y10 255) 15) 0) (Nat.land y10 255))) (fun y10 : ℕ ↦ Nat.add
                            8 (@Bool.rec (fun _ ↦ ℕ → ℕ) (fun y2 : ℕ ↦ (@Bool.rec (fun _ ↦ ℕ) 0 1
                            (Nat.beq (Nat.land (Nat.land y2 1) 1) 0))) (fun y2 : ℕ ↦ Nat.add 1
                            (@Bool.rec (fun _ ↦ ℕ) 0 1 (Nat.beq (Nat.land (Nat.shiftRight y2 1) 1)
                            0))) (Nat.beq (Nat.land (Nat.shiftRight y10 8) 1) 0) (Nat.shiftRight
                            y10 8))) (Nat.beq (Nat.land (Nat.shiftRight y42 32) 255) 0)
                            (Nat.shiftRight y42 32))) (Nat.beq (Nat.land cr2 4294967295) 0) cr2))
                            2)) 128))))))
                (@Bool.rec (fun _ ↦ Bool) false (Nat.ble (Nat.add (Nat.land acc1
                  0xffffffffffffffff) 1) 0x100000) (@Bool.rec (fun _ ↦ Bool) false (Nat.beq
                  (Nat.land cr1 63) 0) (@Bool.rec (fun _ ↦ Bool) false (Nat.ble (Nat.add coh 1)
                  4398046511104) (Nat.ble (Nat.add cr1 1) 4398046511104))))
                cr1 coh crt1 cot acc1)
            co cr crt acc)
        cr0 acc0 co0)
    k0

/-- 32-step `@Sum.rec` chunk-unrolled zero-`DefinitionVal` `tz ≥ 6` tier verifier (`≤ 4,400` stack
frames). -/
noncomputable def gqsp_zwCodeTierTz63Fast8 (fuel n_exp d_exp rot_exp : ℕ) : List ℕ → ℕ → List
    ℕ → Bool := @Nat.rec (fun _ ↦ List ℕ → ℕ → List ℕ → Bool)
    (gqsp_tf_zwCodeTierTz63Fast n_exp d_exp rot_exp) (fun _ ih cr acc co ↦ @Sum.rec Bool (ℕ ×
    List ℕ × List ℕ) (fun _ ↦ Bool) (fun b ↦ b) (@Prod.rec ℕ (List ℕ × List ℕ) (fun _ ↦ Bool)
    (fun acc8 p8 ↦ @Prod.rec (List ℕ) (List ℕ) (fun _ ↦ Bool) (fun cr8 co8 ↦ ih cr8 acc8 co8)
    p8)) (tierStepK n_exp d_exp rot_exp 32 cr acc co)) fuel

/-- Chunk-unrolled low-memory `tz ≥ 6` tier check (`=` to `gqsp_tierCheck64LowMemBle`). -/
noncomputable def gqsp_tierCheck64Fast8 (fuel M N_base distSum N_dist N_tier rotSum : ℕ)
    (C_tier_list C_orig_list : List ℕ) : Bool := Bool.and (gqsp_zwCodeTierTz63Fast8 fuel
    (Nat.add M 1) distSum rotSum C_tier_list 0 C_orig_list) (Bool.and (Nat.ble (Nat.mul
    (Nat.mul (Nat.mul 2 31416) distSum) 64) (Nat.mul N_dist 10000)) (Nat.ble (Nat.add N_base
    N_dist) N_tier))

theorem gqsp_revNat8_eq :
    ∀ (fuel : ℕ) (xs acc : List ℕ), gqsp_revNat8 fuel xs acc = gqsp_zwRevNatTR xs acc
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | _ + 1, [_], _ => rfl
  | _ + 1, [_, _], _ => rfl
  | _ + 1, [_, _, _], _ => rfl
  | _ + 1, [_, _, _, _], _ => rfl
  | _ + 1, [_, _, _, _, _], _ => rfl
  | _ + 1, [_, _, _, _, _, _], _ => rfl
  | _ + 1, [_, _, _, _, _, _, _], _ => rfl
  | fuel + 1, x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: r8, acc =>
      gqsp_revNat8_eq fuel r8 (x7 :: x6 :: x5 :: x4 :: x3 :: x2 :: x1 :: x0 :: acc)

private theorem zwStrictRevNatTR_cons (x : ℕ) (xs acc : List ℕ) :
    gqsp_zwStrictRevNatTR (x :: xs) acc = gqsp_zwStrictRevNatTR xs (x :: acc) := by
  dsimp only [gqsp_zwStrictRevNatTR]
  rw [gqsp_zwForce_eq]

theorem gqsp_strictRev8_eq :
    ∀ (fuel : ℕ) (xs acc : List ℕ), gqsp_strictRev8 fuel xs acc = gqsp_zwStrictRevNatTR xs acc
      := by
  intro fuel
  induction fuel with
  | zero => intro _ _; rfl
  | succ fuel ih =>
      intro xs acc
      unfold gqsp_strictRev8
      dsimp only
      rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, _ | ⟨x7,
        r8⟩⟩⟩⟩⟩⟩⟩⟩ <;> try rfl
      dsimp only
      rw [gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwForce_eq,
          gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwForce_eq]
      change gqsp_strictRev8 fuel r8 _ = _
      rw[ih, zwStrictRevNatTR_cons, zwStrictRevNatTR_cons,
          zwStrictRevNatTR_cons, zwStrictRevNatTR_cons, zwStrictRevNatTR_cons,
          zwStrictRevNatTR_cons, zwStrictRevNatTR_cons, zwStrictRevNatTR_cons]

theorem gqsp_withStrictList8_eq {α : Type} (fuel : ℕ) (xs : List ℕ) (k : List ℕ → α) :
    gqsp_withStrictList8 fuel xs k = k xs := by
  unfold gqsp_withStrictList8
  rw [gqsp_tf_shareHeadList_eq, gqsp_revNat8_eq, gqsp_strictRev8_eq]
  change k (gqsp_zwStrictNatList xs) = k xs
  rw [gqsp_zwStrictNatList_eq]

theorem gqsp_fastDecDelta7Blocks8_eq (fuel : ℕ) (c_orig : List ℕ) (bss0 : List (List (ℕ × ℕ))) :
    gqsp_fastDecDelta7Blocks8 fuel c_orig bss0 = gqsp_zwDecTierDelta7Blocks c_orig bss0 := by
  unfold gqsp_fastDecDelta7Blocks8
  have hrev : (fun (_ : List ℕ) (acc : List ℕ) ↦ gqsp_revNat8 fuel acc []) =
      (fun (_ : List ℕ) (acc : List ℕ) ↦ gqsp_zwRevNatTR acc []) := by
    funext _ acc
    exact gqsp_revNat8_eq fuel acc []
  rw [hrev]
  exact gqsp_tf_fastDecDelta7Blocks_eq c_orig bss0

theorem gqsp_fastDecPatchBlocks8_eq (fuel : ℕ) (c_orig c_prev : List ℕ) (bss0 : List (List (ℕ ×
      ℕ))) :
    gqsp_fastDecPatchBlocks8 fuel c_orig c_prev bss0 = gqsp_zwDecTierPatchBlocks c_orig c_prev
      bss0 := by
  unfold gqsp_fastDecPatchBlocks8
  have hrev : (fun (_ _ : List ℕ) (acc : List ℕ) ↦ gqsp_revNat8 fuel acc []) =
      (fun (_ _ : List ℕ) (acc : List ℕ) ↦ gqsp_zwRevNatTR acc []) := by
    funext _ _ acc
    exact gqsp_revNat8_eq fuel acc []
  rw [hrev]
  exact gqsp_tf_fastDecPatchBlocks_eq c_orig c_prev bss0

private theorem tierStepK_bind (n_exp d_exp rot_exp : ℕ)
    (cont : List ℕ → ℕ → List ℕ → Bool)
    (hcont : ∀ cr acc co, cont cr acc co = gqsp_tf_zwCodeTierTz63Fast n_exp d_exp rot_exp cr acc
      co) :
    ∀ (k : ℕ) (cr : List ℕ) (acc : ℕ) (co : List ℕ),
      @Sum.rec Bool (ℕ × List ℕ × List ℕ) (fun _ ↦ Bool)
        (fun b ↦ b)
        (@Prod.rec ℕ (List ℕ × List ℕ) (fun _ ↦ Bool) (fun acc8 p8 ↦
          @Prod.rec (List ℕ) (List ℕ) (fun _ ↦ Bool) (fun cr8 co8 ↦
            cont cr8 acc8 co8)
            p8))
        (tierStepK n_exp d_exp rot_exp k cr acc co) =
      gqsp_tf_zwCodeTierTz63Fast n_exp d_exp rot_exp cr acc co
  | 0, cr, acc, co => hcont cr acc co
  | _ + 1, [], _, _ => rfl
  | _ + 1, _ :: _, _, [] => rfl
  | k + 1, cr1 :: crt, acc1, coh :: cot => by
      dsimp only [tierStepK, gqsp_tf_zwCodeTierTz63Fast]
      cases (@Bool.rec (fun _ ↦ Bool) false (Nat.ble (Nat.add (Nat.land acc1 0xffffffffffffffff)
        1) 0x100000) (@Bool.rec (fun _ ↦ Bool) false (Nat.beq (Nat.land cr1 63) 0) (@Bool.rec (fun
        _ ↦ Bool) false (Nat.ble (Nat.add coh 1) 4398046511104) (Nat.ble (Nat.add cr1 1)
        4398046511104))))
      · rfl
      · dsimp only
        rw [gqsp_zwForce_eq, gqsp_zwForce_eq]
        exact tierStepK_bind n_exp d_exp rot_exp cont hcont k crt _ cot

private theorem gqsp_zwCodeTierTz63Fast8_eq_tf (n_exp d_exp rot_exp : ℕ) : ∀ (fuel : ℕ)
    (cr : List ℕ) (acc : ℕ) (co : List ℕ), gqsp_zwCodeTierTz63Fast8 fuel n_exp d_exp rot_exp
    cr acc co = gqsp_tf_zwCodeTierTz63Fast n_exp d_exp rot_exp cr acc co := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _; rfl
  | succ fuel ih =>
      intro cr acc co
      unfold gqsp_zwCodeTierTz63Fast8
      dsimp only
      change @Sum.rec Bool (ℕ × List ℕ × List ℕ) (fun _ ↦ Bool) (fun b ↦ b) (@Prod.rec ℕ (List
        ℕ × List ℕ) (fun _ ↦ Bool) (fun acc8 p8 ↦ @Prod.rec (List ℕ) (List ℕ) (fun _ ↦ Bool)
        (fun cr8 co8 ↦ gqsp_zwCodeTierTz63Fast8 fuel n_exp d_exp rot_exp cr8 acc8 co8) p8))
        (tierStepK n_exp d_exp rot_exp 32 cr acc co) = gqsp_tf_zwCodeTierTz63Fast n_exp
        d_exp rot_exp cr acc co
      exact tierStepK_bind n_exp d_exp rot_exp
        (gqsp_zwCodeTierTz63Fast8 fuel n_exp d_exp rot_exp) ih 32 cr acc co

theorem gqsp_tierCheck64Fast8_eq
    (fuel M N_base distSum N_dist N_tier rotSum : ℕ) (C_tier_list C_orig_list : List ℕ) :
    gqsp_tierCheck64Fast8 fuel M N_base distSum N_dist N_tier rotSum C_tier_list C_orig_list =
      gqsp_tierCheck64LowMemBle M N_base distSum N_dist N_tier rotSum C_tier_list C_orig_list := by
  unfold gqsp_tierCheck64Fast8
  rw [gqsp_zwCodeTierTz63Fast8_eq_tf]
  change gqsp_tf_tierCheckLowMemBle M N_base distSum N_dist N_tier rotSum C_tier_list C_orig_list
      = _
  exact gqsp_tf_tierCheckLowMemBle_eq M N_base distSum N_dist N_tier rotSum C_tier_list C_orig_list

end TiersFast8_135598
end GqspBaseTree135598
end QuantumComputation.Specs.StoppingPowerSolution
end
