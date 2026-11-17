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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.BiGqspRyToSu2

set_option Elab.async false

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution
noncomputable section Gqsp0c_RealTree
section
set_option compiler.extract_closed false
namespace GqspWronskian62592
section RealTournamentHelpers
set_option maxRecDepth 600000
set_option exponentiation.threshold 2048
open Real Operator Matrix Circuit
open scoped Matrix Matrix.Norms.L2Operator BigOperators
open SpecsAux SpecsAux.SpecMirror
open PhaseGradSignalRot TFreeLaurentGQSP
open CatalyzedLaurentGQSP TFreeLaurentGQSPPresets
open TFreeLaurentGQSPPresets.FastRecurrenceVerifier
open TFreeLaurentGQSPPresets.FastIntervalRecurrenceVerifier
open CatalyzedLaurentGQSPBridge BidirectionalCatalyzedGQSP
open BidirectionalCatalyzedGQSPBridge
  TwoAngleBiGqspVerifierBridge
open BidirectionalIntervalRecurrenceVerifier
theorem gqsp_pack768_replicate_zero : ∀ (n : ℕ), pack768 (List.replicate n 0) = 0
  | 0 => rfl
  | n + 1 => by
      simp only [List.replicate_succ, sched_pack768_cons, gqsp_pack768_replicate_zero n,
        Nat.zero_shiftLeft, Nat.add_zero]
private theorem gqsp_roundSplit768_zero (n : ℕ) :
    roundSplit768 (pack768 (List.replicate n 1)) 0 0 = some ⟨0, 0⟩ := by
  have hmem {c b : ℕ} (hb : c < b) : ∀ x ∈ List.replicate n c, x < b :=
    fun _ hx ↦ (List.mem_replicate.mp hx).2 ▸ hb
  refine sched_roundSplit768Masks_spec_bridge 0 _ 0 0 ⟨0, 0, 0⟩ ?_
  rw [sched_pack768_rep_mul n sched_bMid, sched_pack768_rep_mul n sched_keepLane,
    sched_pack768_rep_mul n sched_bQ, sched_pack768_rep_mul n schedAux,
    sched_pack768_rep_mul n sched_clampHiLane]
  unfold sched_roundSplit768Masks sched_roundSplit768Step1 sched_roundSplit768Step1b
    sched_roundSplit768Step1c sched_roundSplit768Step2 sched_roundSplit768Finish
  simp only [sched_stfOpt_eq, sched_idSalt_eq, sched_shrLimb_eq, sched_shr384_eq,
    show Nat.sub (Nat.add 0 (pack768 (List.replicate n sched_bMid))) 0 =
      pack768 (List.replicate n sched_bMid) by simp]
  have hqw : Nat.shiftRight (Nat.land (pack768 (List.replicate n sched_bMid))
      (pack768 (List.replicate n sched_keepLane))) 352 = pack768 (List.replicate n sched_bQ) := by
    simpa only [List.length_replicate, List.map_replicate, show sched_bMid >>> 352 = sched_bQ from
      rfl]
      using sched_pack768_and_rep_shift sched_keepLane 352
        (Nat.ble_eq.mp rfl : sched_keepLane < sched_pow768) (List.replicate n sched_bMid)
        (hmem (Nat.ble_eq.mp rfl : sched_bMid < sched_pow768))
        (fun x hx ↦ sched_mask_keep_lane x (hmem (Nat.ble_eq.mp rfl : sched_bMid < 2 ^ 738) x hx))
  have hsbits : Nat.shiftRight (Nat.land (pack768 (List.replicate n sched_bQ))
      (pack768 (List.replicate n sched_bQ))) 384 =
      pack768 ((List.replicate n sched_bQ).map (· >>> 384)) := by
    simpa only [List.length_replicate] using sched_pack768_and_rep_shift sched_bQ 384
      (Nat.ble_eq.mp rfl : sched_bQ < sched_pow768) (List.replicate n sched_bQ)
      (hmem (Nat.ble_eq.mp rfl : sched_bQ < sched_pow768))
      (fun q hq ↦ sched_mask_bq_lane q (hmem (Nat.ble_eq.mp rfl : sched_bQ < 2 ^ 385) q hq))
  rcases sched_roundSplitFinish_lists (List.replicate n sched_bQ)
    (hmem (Nat.ble_eq.mp rfl : sched_bQ < 2 ^ 385)) with ⟨hfp, hfn⟩
  rw [List.length_replicate] at hfp hfn
  rw [hqw, hsbits, hfp, hfn, List.map_replicate, List.map_replicate,
    show sched_fpLane sched_bQ = 0 by decide, show sched_fnLane sched_bQ = 0 by decide,
    gqsp_pack768_replicate_zero]
  simp only [show ∀ rc, Nat.land 0 rc = 0 from Nat.zero_and]
  rfl
/-- Algebraic 2-channel real Kronecker identity with `rbReal = rb + 2 * (R * L)`. -/
private theorem gqsp_real_conv2_eq (arp arn brp brn y1rp y1rn y2rp y2rn rrep1 lrep1 rb : ℕ)
    (harn : arn ≤ rrep1 * 2 ^ 353) (harp : arp ≤ rrep1 * 2 ^ 353)
    (hbrn : brn ≤ rrep1 * 2 ^ 353) (hbrp : brp ≤ rrep1 * 2 ^ 353)
    (hy1rn : y1rn ≤ lrep1 * 2 ^ 353) (hy1rp : y1rp ≤ lrep1 * 2 ^ 353)
    (hy2rn : y2rn ≤ lrep1 * 2 ^ 353) (hy2rp : y2rp ≤ lrep1 * 2 ^ 353)
    (hrb : 8 * ((rrep1 * 2 ^ 353) * (lrep1 * 2 ^ 353)) ≤ rb) :
    let R := rrep1 * 2 ^ 353
    let L := lrep1 * 2 ^ 353
    let Ar := (arp + R) - arn
    let Br := (brp + R) - brn
    let Y1r := (y1rp + L) - y1rn
    let Y2r := (y2rp + L) - y2rn
    (mulAdd4Pos ⟨arp, arn⟩ ⟨y1rp, y1rn⟩ ⟨0, 0⟩ ⟨0, 0⟩ ⟨brp, brn⟩ ⟨y2rp, y2rn⟩ ⟨0, 0⟩ ⟨0, 0⟩ + rb) -
      mulAdd4Neg ⟨arp, arn⟩ ⟨y1rp, y1rn⟩ ⟨0, 0⟩ ⟨0, 0⟩ ⟨brp, brn⟩ ⟨y2rp, y2rn⟩ ⟨0, 0⟩ ⟨0, 0⟩ =
      ((rb + 2 * (R * L)) + (Ar * Y1r + Br * Y2r)) -
        (((Ar + Br) * lrep1 + (Y1r + Y2r) * rrep1) * 2 ^ 353) := by
  dsimp only [mulAdd4Pos, mulAdd4Neg, mulAdd2Pos, mulAdd2Neg]
  simp only [Nat.add_eq, Nat.mul_eq, Nat.mul_zero, Nat.add_zero]
  have := And.intro (Nat.mul_le_mul harp hy1rn) (And.intro (Nat.mul_le_mul harn hy1rp)
    (And.intro (Nat.mul_le_mul hbrp hy2rn) (Nat.mul_le_mul hbrn hy2rp)))
  refine gqsp_sub_eq_sub_of_add (by omega) ?_
  zify [harn.trans (Nat.le_add_left _ _), hbrn.trans (Nat.le_add_left _ _),
    hy1rn.trans (Nat.le_add_left _ _), hy2rn.trans (Nat.le_add_left _ _)]
  ring
/-- Pre-multiplied level-shared masks for 2-channel real tournament levels. -/
inductive gqsp_LevelMasksR where
  | empty : gqsp_LevelMasksR
  | mk (ldeg rdeg lrep1 rrep1 rep1 rb rk rbq rm rc lb353 rb353 rb354 rbReal : ℕ) : gqsp_LevelMasksR
noncomputable def gqsp_tfLMR (f : ℕ → gqsp_LevelMasksR) (x : ℕ) : gqsp_LevelMasksR :=
  @Nat.casesOn (fun _ => gqsp_LevelMasksR) (Nat.add 1 x) gqsp_LevelMasksR.empty f
theorem gqsp_tfLMR_eq (f : ℕ → gqsp_LevelMasksR) (x : ℕ) : gqsp_tfLMR f x = f x := by
  change @Nat.casesOn (fun _ => gqsp_LevelMasksR) (1 + x) gqsp_LevelMasksR.empty f = f x
  rw [Nat.one_add]
noncomputable def gqsp_mkLMR8 (ldeg rdeg lrep1 rrep1 rp rb rk rbq rm rc lb353 rb353 rb354 : ℕ) :
    gqsp_LevelMasksR :=
  gqsp_tfLMR (gqsp_LevelMasksR.mk ldeg rdeg lrep1 rrep1 rp rb rk rbq rm rc lb353 rb353 rb354)
    (Nat.add rb (Nat.shiftLeft (Nat.mul rrep1 lrep1) 707))
noncomputable def gqsp_mkLMR7 (ldeg rdeg lrep1 rrep1 rp rb rk rbq rm rc lb353 rb353 : ℕ) :
    gqsp_LevelMasksR :=
  gqsp_tfLMR (gqsp_mkLMR8 ldeg rdeg lrep1 rrep1 rp rb rk rbq rm rc lb353 rb353)
    (Nat.shiftLeft rrep1 354)
noncomputable def gqsp_mkLMR6 (ldeg rdeg lrep1 rrep1 rp rb rk rbq rm rc lb353 : ℕ) :
    gqsp_LevelMasksR := gqsp_tfLMR
    (gqsp_mkLMR7 ldeg rdeg lrep1 rrep1 rp rb rk rbq rm rc lb353) (Nat.shiftLeft rrep1 353)
noncomputable def gqsp_mkLMR5 (ldeg rdeg lrep1 rrep1 rp rb rk rbq rm rc : ℕ) :
    gqsp_LevelMasksR := gqsp_tfLMR (gqsp_mkLMR6 ldeg rdeg lrep1 rrep1 rp rb rk rbq rm rc)
    (Nat.shiftLeft lrep1 353)
noncomputable def gqsp_mkLMR4 (ldeg rdeg lrep1 rrep1 rp rb rk rbq rm : ℕ) : gqsp_LevelMasksR
    := gqsp_tfLMR (gqsp_mkLMR5 ldeg rdeg lrep1 rrep1 rp rb rk rbq rm)
    (Nat.mul rp sched_clampHiLane)
noncomputable def gqsp_mkLMR3 (ldeg rdeg lrep1 rrep1 rp rb rk rbq : ℕ) : gqsp_LevelMasksR :=
    gqsp_tfLMR (gqsp_mkLMR4 ldeg rdeg lrep1 rrep1 rp rb rk rbq) (Nat.mul rp schedAux)
noncomputable def gqsp_mkLMR2 (ldeg rdeg lrep1 rrep1 rp rb rk : ℕ) : gqsp_LevelMasksR :=
    gqsp_tfLMR (gqsp_mkLMR3 ldeg rdeg lrep1 rrep1 rp rb rk) (Nat.mul rp sched_bQ)
noncomputable def gqsp_mkLMR1 (ldeg rdeg lrep1 rrep1 rp rb : ℕ) : gqsp_LevelMasksR :=
    gqsp_tfLMR (gqsp_mkLMR2 ldeg rdeg lrep1 rrep1 rp rb) (Nat.mul rp sched_keepLane)
noncomputable def gqsp_mkLMR0 (ldeg rdeg lrep1 rrep1 rp : ℕ) : gqsp_LevelMasksR :=
    gqsp_tfLMR (gqsp_mkLMR1 ldeg rdeg lrep1 rrep1 rp) (Nat.mul rp sched_bMid)
noncomputable def gqsp_mkLevelMasksR (l r : TreeNodeC) : gqsp_LevelMasksR :=
  let rep1 := Nat.add l.rep1 (sched_shlDyn (sched_shr768 r.rep1) (Nat.mul 768 (Nat.add l.deg 1)))
  gqsp_tfLMR (gqsp_mkLMR0 l.deg r.deg l.rep1 r.rep1) rep1
theorem gqsp_mkLevelMasksR_eq (x y : TreeNodeC) : gqsp_mkLevelMasksR x y =
    gqsp_LevelMasksR.mk x.deg y.deg x.rep1 y.rep1 (Nat.add x.rep1 (sched_shlDyn (sched_shr768
    y.rep1) (Nat.mul 768 (Nat.add x.deg 1)))) (Nat.mul (Nat.add x.rep1 (sched_shlDyn
    (sched_shr768 y.rep1) (Nat.mul 768 (Nat.add x.deg 1)))) sched_bMid) (Nat.mul (Nat.add x.rep1
    (sched_shlDyn (sched_shr768 y.rep1) (Nat.mul 768 (Nat.add x.deg 1)))) sched_keepLane)
    (Nat.mul (Nat.add x.rep1 (sched_shlDyn (sched_shr768 y.rep1) (Nat.mul 768 (Nat.add x.deg
    1)))) sched_bQ) (Nat.mul (Nat.add x.rep1 (sched_shlDyn (sched_shr768 y.rep1) (Nat.mul 768
    (Nat.add x.deg 1)))) schedAux) (Nat.mul (Nat.add x.rep1 (sched_shlDyn (sched_shr768 y.rep1)
    (Nat.mul 768 (Nat.add x.deg 1)))) sched_clampHiLane) (Nat.shiftLeft x.rep1 353)
    (Nat.shiftLeft y.rep1 353) (Nat.shiftLeft y.rep1 354) (Nat.add (Nat.mul (Nat.add x.rep1
    (sched_shlDyn (sched_shr768 y.rep1) (Nat.mul 768 (Nat.add x.deg 1)))) sched_bMid)
    (Nat.shiftLeft (Nat.mul y.rep1 x.rep1) 707)) := by
  unfold gqsp_mkLevelMasksR gqsp_mkLMR0 gqsp_mkLMR1 gqsp_mkLMR2 gqsp_mkLMR3
    gqsp_mkLMR4 gqsp_mkLMR5 gqsp_mkLMR6 gqsp_mkLMR7 gqsp_mkLMR8
  simp only [gqsp_tfLMR_eq]
noncomputable def gqsp_isRealNode (nd : TreeNodeC) : Bool :=
  Bool.and (Bool.and (Nat.beq nd.pip 0) (Nat.beq nd.pin 0))
    (Bool.and (Nat.beq nd.qip 0) (Nat.beq nd.qin 0))
noncomputable def gqsp_finishRealStep4 (ldeg lerr rdeg rerr rep1 salt : ℕ)
    (pr_s qr_s : SaltedPN) : Option TreeNodeC :=
  sched_mergeNodesCStep4 ldeg lerr rdeg rerr rep1 salt pr_s ⟨0, 0, 0⟩ qr_s ⟨0, 0, 0⟩
theorem gqsp_finishRealStep4_eq (ldeg lerr rdeg rerr rep1 salt : ℕ) (pr_s qr_s : SaltedPN) :
    gqsp_finishRealStep4 ldeg lerr rdeg rerr rep1 salt pr_s qr_s = if Nat.ble (Nat.add 1
    (Nat.mul (Nat.mul 4 (Nat.add 1 (if Nat.ble ldeg rdeg then ldeg else rdeg))) (Nat.add
    (Nat.mul 3 rerr) (Nat.mul 2 lerr)))) sched_sTree then some ⟨Nat.add ldeg rdeg, salt, rep1,
    pr_s.pos, pr_s.neg, 0, 0, qr_s.pos, qr_s.neg, 0, 0, Nat.add 1 (Nat.mul (Nat.mul 4 (Nat.add
    1 (if Nat.ble ldeg rdeg then ldeg else rdeg))) (Nat.add (Nat.mul 3 rerr) (Nat.mul 2
    lerr)))⟩ else none := by
  unfold gqsp_finishRealStep4 sched_mergeNodesCStep4 sched_mergeNodesCStep5 sched_mkMergedNodeC
  simp only [sched_stfOpt_eq]
noncomputable def gqsp_realS3Qr (ldeg lerr rdeg rerr rep1 rk rbq rm rc salt z_qr : ℕ)
    (pr_s : SaltedPN) : Option TreeNodeC := sched_optBind
    (gqsp_roundSplitZ (Nat.add 48 salt) rk rbq rm rc z_qr)
    (gqsp_finishRealStep4 ldeg lerr rdeg rerr rep1 salt pr_s)
noncomputable def gqsp_realS3Pr (ldeg lerr rdeg rerr rep1 rk rbq rm rc salt z_pr z_qr : ℕ) :
    Option TreeNodeC := sched_optBind (gqsp_roundSplitZ (Nat.add 16 salt) rk rbq rm rc z_pr)
    (gqsp_realS3Qr ldeg lerr rdeg rerr rep1 rk rbq rm rc salt z_qr)
noncomputable def gqsp_realS2 (ldeg lerr rdeg rerr lrep1 rrep1 rep1 rk rbq rm rc rbReal salt
    ar cr yl zl rar ncr ys p_aryl : ℕ) : Option TreeNodeC :=
  let sub_pr := if Nat.beq ldeg rdeg then Nat.mul
      (Nat.add (Nat.add (sched_idSalt (Nat.add 161 salt) ar) ncr) ys) lrep1 else Nat.add
      (Nat.mul (Nat.add (sched_idSalt (Nat.add 161 salt) ar) ncr) lrep1) (Nat.mul ys rrep1)
  let sub_qr := if Nat.beq ldeg rdeg then Nat.mul
      (Nat.add (Nat.add (sched_idSalt (Nat.add 221 salt) cr) rar) ys) lrep1 else Nat.add
      (Nat.mul (Nat.add (sched_idSalt (Nat.add 221 salt) cr) rar) lrep1) (Nat.mul ys rrep1)
  let z_pr := Nat.sub (Nat.add (sched_idSalt (Nat.add 201 salt) rbReal) (Nat.add p_aryl
      (Nat.mul (sched_idSalt (Nat.add 182 salt) ncr) zl))) (Nat.shiftLeft sub_pr 353)
  let z_qr := Nat.sub (Nat.add (sched_idSalt (Nat.add 261 salt) rbReal) (Nat.add (Nat.mul
      (sched_idSalt (Nat.add 241 salt) cr) yl) (Nat.mul (sched_idSalt (Nat.add 242 salt) rar)
      zl))) (Nat.shiftLeft sub_qr 353)
  gqsp_withPNOpt (gqsp_mkPairPN (Nat.add 113 salt) z_pr z_qr)
    (gqsp_realS3Pr ldeg lerr rdeg rerr rep1 rk rbq rm rc salt)
theorem gqsp_realS2_unfold (ldeg lerr rdeg rerr lrep1 rrep1 rep1 rk rbq rm rc rbReal salt ar
    cr yl zl rar ncr ys p_aryl : ℕ) : gqsp_realS2 ldeg lerr rdeg rerr lrep1 rrep1 rep1 rk rbq
    rm rc rbReal salt ar cr yl zl rar ncr ys p_aryl = gqsp_realS3Pr ldeg lerr rdeg rerr rep1
    rk rbq rm rc salt (Nat.sub (Nat.add rbReal (Nat.add p_aryl (Nat.mul ncr zl)))
    (Nat.shiftLeft (if Nat.beq ldeg rdeg then Nat.mul (Nat.add (Nat.add ar ncr) ys) lrep1 else
    Nat.add (Nat.mul (Nat.add ar ncr) lrep1) (Nat.mul ys rrep1)) 353)) (Nat.sub (Nat.add
    rbReal (Nat.add (Nat.mul cr yl) (Nat.mul rar zl))) (Nat.shiftLeft (if Nat.beq ldeg rdeg
    then Nat.mul (Nat.add (Nat.add cr rar) ys) lrep1 else Nat.add (Nat.mul (Nat.add cr rar)
    lrep1) (Nat.mul ys rrep1)) 353)) := by
  unfold gqsp_realS2
  rw [gqsp_withPNOpt_mkPairPN]
  simp only [sched_idSalt_eq]
noncomputable def gqsp_realS1 (d : ℕ) (ldeg lerr rdeg rerr lrep1 rrep1 rep1 rk rbq rm rc
    rb354 rbReal salt : ℕ) (ar cr yl zl : ℕ) : Option TreeNodeC := gqsp_withQ4 (gqsp_forceQ4
    (Nat.add 105 salt) (gqsp_fastRevSwarSalt 0 salt d (Nat.add rdeg 1) ar) (Nat.sub
    (sched_idSalt (Nat.add 130 salt) rb354) (gqsp_fastRevSwarSalt 4 salt d (Nat.add rdeg 1)
    cr)) (Nat.add (sched_idSalt (Nat.add 141 salt) yl) zl) (Nat.mul (sched_idSalt (Nat.add 181
    salt) ar) yl)) (gqsp_realS2 ldeg lerr rdeg rerr lrep1 rrep1 rep1 rk rbq rm rc rbReal salt
    ar cr yl zl)
theorem gqsp_realS1_unfold (d : ℕ) (ldeg lerr rdeg rerr lrep1 rrep1 rep1 rk rbq rm rc rb354
    rbReal salt : ℕ) (ar cr yl zl : ℕ) : gqsp_realS1 d ldeg lerr rdeg rerr lrep1 rrep1 rep1
    rk rbq rm rc rb354 rbReal salt ar cr yl zl = gqsp_realS2 ldeg lerr rdeg rerr lrep1 rrep1
    rep1 rk rbq rm rc rbReal salt ar cr yl zl (gqsp_fastRevSwarSalt 0 salt d (Nat.add rdeg 1) ar)
    (Nat.sub rb354 (gqsp_fastRevSwarSalt 4 salt d (Nat.add rdeg 1) cr)) (Nat.add yl zl)
    (Nat.mul ar yl) := by
  unfold gqsp_realS1
  rw [gqsp_withQ4_forceQ4]
  simp only [sched_idSalt_eq]
noncomputable def gqsp_mergeRealCore (d : ℕ) (ldeg lprp lprn lqrp lqrn lerr : ℕ)
    (rdeg rprp rprn rqrp rqrn rerr : ℕ)
    (lrep1 rrep1 rep1 rk rbq rm rc lb353 rb353 rb354 rbReal salt : ℕ) : Option TreeNodeC :=
    gqsp_withQ4 (gqsp_forceQ4 (Nat.add 101 salt) (Nat.sub (Nat.add (sched_idSalt (Nat.add 101
    salt) rprp) rb353) rprn) (Nat.sub (Nat.add (sched_idSalt (Nat.add 103 salt) rqrp) rb353)
    rqrn) (Nat.sub (Nat.add (sched_idSalt (Nat.add 134 salt) lprp) lb353) lprn) (Nat.sub
    (Nat.add (sched_idSalt (Nat.add 136 salt) lqrp) lb353) lqrn)) (gqsp_realS1 d ldeg lerr
    rdeg rerr lrep1 rrep1 rep1 rk rbq rm rc rb354 rbReal salt)
theorem gqsp_mergeRealCore_unfold (d : ℕ) (ldeg lprp lprn lqrp lqrn lerr : ℕ)
    (rdeg rprp rprn rqrp rqrn rerr : ℕ)
    (lrep1 rrep1 rep1 rk rbq rm rc lb353 rb353 rb354 rbReal salt : ℕ) : gqsp_mergeRealCore d
    ldeg lprp lprn lqrp lqrn lerr rdeg rprp rprn rqrp rqrn rerr lrep1 rrep1 rep1 rk rbq rm rc
    lb353 rb353 rb354 rbReal salt = gqsp_realS1 d ldeg lerr rdeg rerr lrep1 rrep1 rep1 rk rbq
    rm rc rb354 rbReal salt (Nat.sub (Nat.add rprp rb353) rprn)
    (Nat.sub (Nat.add rqrp rb353) rqrn) (Nat.sub (Nat.add lprp lb353) lprn)
    (Nat.sub (Nat.add lqrp lb353) lqrn) := by
  unfold gqsp_mergeRealCore
  rw [gqsp_withQ4_forceQ4]
  simp only [sched_idSalt_eq]
noncomputable def gqsp_mergeWithMasksFieldsR (d : ℕ)
    (lrep1 rrep1 rep1 rk rbq rm rc lb353 rb353 rb354 rbReal : ℕ)
    (l r : TreeNodeC) : Option TreeNodeC :=
  match l, r with
  | ⟨ldeg, lsalt, _, lprp, lprn, _, _, lqrp, lqrn, _, _, lerr⟩,
    ⟨rdeg, rsalt, _, rprp, rprn, _, _, rqrp, rqrn, _, _, rerr⟩ =>
    let salt' := Nat.land (Nat.add 1 (Nat.xor (Nat.mul lsalt 0x9e3779b97f4a7c15) (Nat.mul
        rsalt 0xbf58476d1ce4e5b9))) 0xfffffffffffffff
    sched_stfOpt (Nat.add 99 salt') (gqsp_mergeRealCore d
      ldeg lprp lprn lqrp lqrn lerr
      rdeg rprp rprn rqrp rqrn rerr
      lrep1 rrep1 rep1 rk rbq rm rc lb353 rb353 rb354 rbReal) salt'
noncomputable def gqsp_mergeWithMasksR (d : ℕ) (m : gqsp_LevelMasksR) (l r : TreeNodeC) :
    Option TreeNodeC := @gqsp_LevelMasksR.casesOn (fun _ => Option TreeNodeC) m none (fun
    mldeg mrdeg lrep1 rrep1 rep1 _rb rk rbq rm rc lb353 rb353 rb354 rbReal => if Bool.and
    (Bool.and (Nat.beq l.deg mldeg) (Nat.beq r.deg mrdeg)) (Bool.and (gqsp_isRealNode l)
    (gqsp_isRealNode r)) then gqsp_mergeWithMasksFieldsR d lrep1 rrep1 rep1 rk rbq rm rc
    lb353 rb353 rb354 rbReal l r else mergeNodesCGo d l r)
theorem gqsp_mergeWithMasksR_mk (d mldeg mrdeg lrep1 rrep1 rep1 rb rk rbq rm rc lb353 rb353
    rb354 rbReal : ℕ) (l r : TreeNodeC) : gqsp_mergeWithMasksR d (gqsp_LevelMasksR.mk mldeg
    mrdeg lrep1 rrep1 rep1 rb rk rbq rm rc lb353 rb353 rb354 rbReal) l r = if Bool.and
    (Bool.and (Nat.beq l.deg mldeg) (Nat.beq r.deg mrdeg))
    (Bool.and (gqsp_isRealNode l) (gqsp_isRealNode r)) then gqsp_mergeWithMasksFieldsR d
    lrep1 rrep1 rep1 rk rbq rm rc lb353 rb353 rb354 rbReal l r else mergeNodesCGo d l r := rfl
noncomputable def gqsp_mergeNodesRealFast (m : gqsp_LevelMasksR) (l r : TreeNodeC) : Option
    TreeNodeC :=
  gqsp_mergeWithMasksR (gqsp_swarDepth r.deg) m l r
theorem gqsp_mergeWithMasksR_self_spec (d : ℕ) (gs_l gs_r : List DyadicSu2Gate)
    (l r out : TreeNodeC) (hl : TreeNodeCValid gs_l l) (hr : TreeNodeCValid gs_r r)
    (hlen : (gs_l ++ gs_r).length ≤ 262144) (hd : r.deg + 1 ≤ 2 ^ d) (hm :
    gqsp_mergeWithMasksR d (gqsp_mkLevelMasksR l r) l r = some out) : TreeNodeCValid
    (gs_l ++ gs_r) out := by
  rw [gqsp_mkLevelMasksR_eq l r, gqsp_mergeWithMasksR_mk] at hm
  by_cases hcond : Bool.and (Bool.and (Nat.beq l.deg l.deg) (Nat.beq r.deg r.deg))
      (Bool.and (gqsp_isRealNode l) (gqsp_isRealNode r)) = true
  · rw [ite_eq_left hcond] at hm
    have hreal := ((Bool.and_eq_true _ _).mp hcond).2
    rcases l with ⟨ldeg, lsalt, lrep1, lprp, lprn, lpip, lpin, lqrp, lqrn, lqip, lqin, lerr⟩
    rcases r with ⟨rdeg, rsalt, rrep1, rprp, rprn, rpip, rpin, rqrp, rqrn, rqip, rqin, rerr⟩
    simp only [gqsp_isRealNode, Bool.and_eq_true, Nat.beq_eq] at hreal
    rcases hreal with ⟨ ⟨ ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩, ⟨ ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩⟩
    rcases hl with ⟨hldeg, hl1, hl_err, hl_rep, PL_hat, QL_hat, hl_pr, hl_pi, hl_qr, hl_qi, hl_P,
      hl_Q⟩
    rcases hr with ⟨hrdeg, hr1, hr_err, hr_rep, PR_hat, QR_hat, hr_pr, hr_pi, hr_qr, hr_qi, hr_P,
      hr_Q⟩
    dsimp only [TreeNodeC.deg, TreeNodeC.rep1, TreeNodeC.pr, TreeNodeC.pi, TreeNodeC.qr,
      TreeNodeC.qi] at *
    have hpr_rev := revPN_valid hd hr_pr
    have hqr_rev := revPN_valid hd hr_qr
    rcases gqsp_polyPNValid_le_b353 hl_pr with ⟨hl_prp, hl_prn⟩
    rcases gqsp_polyPNValid_le_b353 hl_qr with ⟨hl_qrp, hl_qrn⟩
    rcases gqsp_polyPNValid_le_b353 hr_pr with ⟨hr_prp, hr_prn⟩
    rcases gqsp_polyPNValid_le_b353 hr_qr with ⟨hr_qrp, hr_qrn⟩
    rcases gqsp_polyPNValid_le_b353 hpr_rev with ⟨hprv_p, hprv_n⟩
    rcases gqsp_polyPNValid_le_b353 hqr_rev with ⟨hqrv_p, hqrv_n⟩
    dsimp only [revPN] at hprv_p hprv_n hqrv_p hqrv_n
    let rp := Nat.add (pack768 (List.replicate (ldeg + 1) 1))
      (sched_shlDyn (sched_shr768 (pack768 (List.replicate (rdeg +
        1) 1))) (Nat.mul 768 (Nat.add ldeg 1)))
    have hrep_out : rp = pack768 (List.replicate (rdeg + ldeg + 1) 1) := by
      dsimp only [rp]
      rw [sched_shlDyn_eq, sched_shr768_eq, sched_rep1_merge_eq ldeg rdeg _ _ hr1 rfl rfl]
      exact congrArg (fun n ↦ pack768 (List.replicate n 1)) (by omega)
    have hrb_bound : 8 * ((pack768 (List.replicate (rdeg + 1) 1) * 2 ^ 353) *
        (pack768 (List.replicate (ldeg + 1) 1) * 2 ^ 353)) ≤ Nat.mul rp sched_bMid :=
      hrep_out.symm ▸ gqsp_eight_rl_le_rb ldeg rdeg
    let s := Nat.land (Nat.add 1 (Nat.xor (Nat.mul lsalt 0x9e3779b97f4a7c15)
      (Nat.mul rsalt 0xbf58476d1ce4e5b9))) 0xfffffffffffffff
    have hrev_pr := gqsp_srev_bias_eq_of_valid 0 s d rdeg ⟨rprp, rprn⟩ PR_hat.re hr_pr hd
    have hrev_qr := gqsp_srev_bias_eq_of_valid 4 s d rdeg ⟨rqrp, rqrn⟩ QR_hat.re hr_qr hd
    dsimp only at hrev_pr hrev_qr
    have hrbReal_eq : Nat.add (Nat.mul rp sched_bMid) (Nat.shiftLeft (Nat.mul
        (pack768 (List.replicate (rdeg + 1) 1)) (pack768 (List.replicate (ldeg + 1) 1))) 707) =
        Nat.mul rp sched_bMid + 2 * ((pack768 (List.replicate (rdeg + 1) 1) * 2 ^ 353) *
          (pack768 (List.replicate (ldeg + 1) 1) * 2 ^ 353)) := by
      rw [gqsp_nat_shl_eq, show (2 : ℕ) ^ 707 = 2 * (2 ^ 353 * 2 ^ 353) by norm_num]
      simp only [Nat.add_eq, Nat.mul_eq]
      ring
    have hsh354 : Nat.shiftLeft (pack768 (List.replicate (rdeg + 1) 1)) 354 =
        2 * (pack768 (List.replicate (rdeg + 1) 1) * 2 ^ 353) := by
      rw [gqsp_nat_shl_eq, show (2 : ℕ) ^ 354 = 2 * 2 ^ 353 by norm_num]
      ring
    have hsub_eq (a b ys : ℕ) : (if Nat.beq ldeg rdeg then Nat.mul (Nat.add (Nat.add a b) ys)
        (pack768 (List.replicate (ldeg + 1) 1)) else Nat.add (Nat.mul (Nat.add a b)
        (pack768 (List.replicate (ldeg + 1) 1))) (Nat.mul ys (pack768 (List.replicate (rdeg +
          1) 1)))) =
        (a + b) * pack768 (List.replicate (ldeg + 1) 1) + ys * pack768 (List.replicate (rdeg +
          1) 1) := by
      cases hbeq : Nat.beq ldeg rdeg
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_eq, Nat.mul_eq]
      · simp only [↓reduceIte, Nat.beq_eq.mp hbeq, Nat.add_eq, Nat.mul_eq, Nat.add_mul]
    simp only [gqsp_mergeWithMasksFieldsR, sched_stfOpt_eq] at hm
    rw [hl_rep, hr_rep, gqsp_mergeRealCore_unfold, gqsp_realS1_unfold, gqsp_realS2_unfold] at hm
    rcases sched_optBind_eq_some hm with ⟨pr_s, hpr_m, hm1⟩
    rcases sched_optBind_eq_some hm1 with ⟨qr_s, hqr_m, hm2⟩
    have hz_pr := gqsp_real_conv2_eq rprp rprn (revBin768 d (rdeg + 1) rqrn)
      (revBin768 d (rdeg + 1) rqrp) lprp lprn lqrp lqrn
      (pack768 (List.replicate (rdeg + 1) 1)) (pack768 (List.replicate (ldeg + 1) 1))
      (Nat.mul rp sched_bMid) hr_prn hr_prp hqrv_p hqrv_n hl_prn hl_prp hl_qrn hl_qrp hrb_bound
    have hz_qr := gqsp_real_conv2_eq rqrp rqrn (revBin768 d (rdeg + 1) rprp)
      (revBin768 d (rdeg + 1) rprn) lprp lprn lqrp lqrn
      (pack768 (List.replicate (rdeg + 1) 1)) (pack768 (List.replicate (ldeg + 1) 1))
      (Nat.mul rp sched_bMid) hr_qrn hr_qrp hprv_n hprv_p hl_prn hl_prp hl_qrn hl_qrp hrb_bound
    dsimp only at hz_pr hz_qr
    rw [hrev_qr, hsh354, gqsp_neg_bias_eq hqrv_p hqrv_n, hrbReal_eq,
      gqsp_nat_shl_eq (pack768 (List.replicate (ldeg + 1) 1)) 353,
      gqsp_nat_shl_eq (pack768 (List.replicate (rdeg + 1) 1)) 353, hsub_eq, gqsp_nat_shl_eq _ 353,
      gqsp_roundSplitZ_eq_masks _ (Nat.mul rp sched_bMid) _ _ _ _
        (mulAdd4Pos ⟨rprp, rprn⟩ ⟨lprp, lprn⟩ ⟨0, 0⟩ ⟨0, 0⟩
          ⟨revBin768 d (rdeg + 1) rqrn, revBin768 d (rdeg + 1) rqrp⟩ ⟨lqrp, lqrn⟩ ⟨0, 0⟩ ⟨0, 0⟩)
        (mulAdd4Neg ⟨rprp, rprn⟩ ⟨lprp, lprn⟩ ⟨0, 0⟩ ⟨0, 0⟩
          ⟨revBin768 d (rdeg + 1) rqrn, revBin768 d (rdeg + 1) rqrp⟩ ⟨lqrp, lqrn⟩ ⟨0, 0⟩ ⟨0, 0⟩)
        _ (by simp only [Nat.sub_eq, Nat.add_eq, Nat.mul_eq]; exact hz_pr.symm)] at hpr_m
    rw [hrev_pr, hrbReal_eq, gqsp_nat_shl_eq (pack768 (List.replicate (ldeg + 1) 1)) 353,
      gqsp_nat_shl_eq (pack768 (List.replicate (rdeg + 1) 1)) 353, hsub_eq, gqsp_nat_shl_eq _ 353,
      gqsp_roundSplitZ_eq_masks _ (Nat.mul rp sched_bMid) _ _ _ _
        (mulAdd4Pos ⟨rqrp, rqrn⟩ ⟨lprp, lprn⟩ ⟨0, 0⟩ ⟨0, 0⟩
          ⟨revBin768 d (rdeg + 1) rprp, revBin768 d (rdeg + 1) rprn⟩ ⟨lqrp, lqrn⟩ ⟨0, 0⟩ ⟨0, 0⟩)
        (mulAdd4Neg ⟨rqrp, rqrn⟩ ⟨lprp, lprn⟩ ⟨0, 0⟩ ⟨0, 0⟩
          ⟨revBin768 d (rdeg + 1) rprp, revBin768 d (rdeg + 1) rprn⟩ ⟨lqrp, lqrn⟩ ⟨0, 0⟩ ⟨0, 0⟩)
        _ (by simp only [Nat.sub_eq, Nat.add_eq, Nat.mul_eq]; exact hz_qr.symm)] at hqr_m
    rw [gqsp_finishRealStep4_eq] at hm2
    cases herr_ble : Nat.ble
        (Nat.add 1 (Nat.mul (Nat.mul 4 (Nat.add 1 (if Nat.ble ldeg rdeg then ldeg else rdeg)))
          (Nat.add (Nat.mul 3 rerr) (Nat.mul 2 lerr)))) sched_sTree with
    | false => simp only [herr_ble, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hm2
    | true =>
      simp only [herr_ble, ↓reduceIte, Option.some.injEq] at hm2
      subst hm2
      have hr_le : rdeg ≤ 262144 := by rw [List.length_append] at hlen; omega
      have hrev0 : revBin768 d (rdeg + 1) 0 = 0 := by
        conv_lhs => rw [← gqsp_pack768_replicate_zero (rdeg + 1)]
        rw [revBin768_spec d (rdeg + 1) _ hd List.length_replicate
          (fun _ hx ↦ (List.mem_replicate.mp hx).2 ▸ Nat.two_pow_pos 768),
          List.reverse_replicate, gqsp_pack768_replicate_zero]
      have hpi_rev0 : PolyPNValid rdeg ⟨0, 0⟩ (ta_polyRev rdeg PR_hat.im) := by
        simpa only [revPN, hrev0] using revPN_valid hd hr_pi
      have hqi_rev0 : PolyPNValid rdeg ⟨0, 0⟩ (ta_polyRev rdeg QR_hat.im) := by
        simpa only [revPN, hrev0] using revPN_valid hd hr_qi
      have hz0_rs : roundSplit768 rp 0 0 = some ⟨0, 0⟩ :=
        hrep_out.symm ▸ gqsp_roundSplit768_zero (rdeg + ldeg + 1)
      rcases mulAdd4_roundSplit_spec hr_le hrep_out hr_pr hl_pr (negPN_valid hr_pi) hl_pi
        (negPN_valid hqr_rev) hl_qr (negPN_valid hqi_rev0) hl_qi
        (sched_roundSplit768Masks_spec_bridge (Nat.add 16 s) rp _ _ pr_s hpr_m) with ⟨fpr, hfpr_v,
          hfpr_e⟩
      rcases mulAdd4_roundSplit_spec hr_le hrep_out hr_pr hl_pi hr_pi hl_pr
        (negPN_valid hqr_rev) hl_qi hqi_rev0 hl_qr
        (by simpa [mulAdd4Pos, mulAdd2Pos, mulAdd4Neg, mulAdd2Neg] using hz0_rs) with ⟨fpi, hfpi_v,
          hfpi_e⟩
      rcases mulAdd4_roundSplit_spec hr_le hrep_out hr_qr hl_pr (negPN_valid hr_qi) hl_pi
        hpr_rev hl_qr hpi_rev0 hl_qi
        (sched_roundSplit768Masks_spec_bridge (Nat.add 48 s) rp _ _ qr_s hqr_m) with ⟨fqr, hfqr_v,
          hfqr_e⟩
      rcases mulAdd4_roundSplit_spec hr_le hrep_out hr_qr hl_pi hr_qi hl_pr hpr_rev hl_qi
        (negPN_valid hpi_rev0) hl_qr
        (by simpa [mulAdd4Pos, mulAdd2Pos, mulAdd4Neg, mulAdd2Neg, negPN] using hz0_rs) with ⟨fqi,
          hfqi_v, hfqi_e⟩
      have hcongr {x y : ℝ} (h : |y| ≤ 1 / (2 ^ 352 : ℝ)) (hxy : x = y) : |x| ≤ 1 / (2 ^ 352 : ℝ) :=
        hxy ▸ h
      have hPQ_rnd : PolyCApprox ⟨fpr,
        fpi⟩ (cdMul rdeg PR_hat QR_hat PL_hat QL_hat).1 (1 / (2 ^ 352 : ℝ)) ∧
          PolyCApprox ⟨fqr, fqi⟩ (cdMul rdeg PR_hat QR_hat PL_hat QL_hat).2 (1 / (2 ^ 352 : ℝ)) :=
            by
        refine ⟨ ⟨fun m ↦ hcongr (hfpr_e m) ?_, fun m ↦ hcongr (hfpi_e m) ?_⟩,
                ⟨fun m ↦ hcongr (hfqr_e m) ?_, fun m ↦ hcongr (hfqi_e m) ?_⟩⟩
        all_goals
          simp only [cdMul, polySubC, polyAddC, polyMulC, polyConjRev, ta_polySub, ta_polyAdd,
            sched_polyConv_neg_left]
          ring
      have hEL_le1 : (lerr : ℝ) / (2 ^ 352 : ℝ) ≤ 1 := by
        have hc : (lerr : ℝ) ≤ ((2 ^ 352 : ℕ) : ℝ) := by exact_mod_cast hl_err
        rw [Nat.cast_pow, Nat.cast_ofNat] at hc
        exact (div_le_one (sched_two_pow_pos_real 352)).mpr hc
      have hbPL := polyCAbsBound_of_approx
        ⟨sched_polyPNValid_abs_le_two hl_pr, sched_polyPNValid_abs_le_two hl_pi⟩ hl_P
      have hbQL := polyCAbsBound_of_approx
        ⟨sched_polyPNValid_abs_le_two hl_qr, sched_polyPNValid_abs_le_two hl_qi⟩ hl_Q
      rcases gateListTransferPQ_supp 48 gs_r with ⟨hPR_s, hQR_s⟩
      rcases gateListTransferPQ_supp 48 gs_l with ⟨hPL_s, hQL_s⟩
      have hbil := cdMul_bilinear_err (BR := 2) (BL := 3)
        (ER := (rerr : ℝ) / (2 ^ 352 : ℝ)) (EL := (lerr : ℝ) / (2 ^ 352 : ℝ))
        (by norm_num) (by norm_num)
        (div_nonneg (Nat.cast_nonneg _) (le_of_lt (sched_two_pow_pos_real 352)))
        (div_nonneg (Nat.cast_nonneg _) (le_of_lt (sched_two_pow_pos_real 352)))
        ⟨sched_polyPNValid_supp hr_pr, sched_polyPNValid_supp hr_pi⟩ (hrdeg ▸ hPR_s)
        ⟨sched_polyPNValid_supp hr_qr, sched_polyPNValid_supp hr_qi⟩ (hrdeg ▸ hQR_s)
        ⟨sched_polyPNValid_supp hl_pr, sched_polyPNValid_supp hl_pi⟩ (hldeg ▸ hPL_s)
        ⟨sched_polyPNValid_supp hl_qr, sched_polyPNValid_supp hl_qi⟩ (hldeg ▸ hQL_s)
        ⟨sched_polyPNValid_abs_le_two hr_pr, sched_polyPNValid_abs_le_two hr_pi⟩
        ⟨sched_polyPNValid_abs_le_two hr_qr, sched_polyPNValid_abs_le_two hr_qi⟩
        ⟨fun m ↦ by linarith [hbPL.1 m], fun m ↦ by linarith [hbPL.2 m]⟩
        ⟨fun m ↦ by linarith [hbQL.1 m], fun m ↦ by linarith [hbQL.2 m]⟩
        hr_P hr_Q hl_P hl_Q
      have hlmin_eq : (if Nat.ble ldeg rdeg then ldeg else rdeg) = min rdeg ldeg := by
        cases hle : Nat.ble ldeg rdeg <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · exact (Nat.min_eq_left (Nat.le_of_not_le (mt Nat.ble_eq.mpr (by simp [hle])))).symm
        · exact (Nat.min_eq_right (Nat.ble_eq.mp hle)).symm
      have herr_eq : 1 / (2 ^ 352 : ℝ) + 4 * ((min rdeg ldeg + 1 : ℕ) : ℝ) *
          (2 * ((lerr : ℝ) / (2 ^ 352 : ℝ)) + 3 * ((rerr : ℝ) / (2 ^ 352 : ℝ))) =
          ((Nat.add 1 (Nat.mul (Nat.mul 4 (Nat.add 1 (if Nat.ble ldeg rdeg then ldeg else rdeg)))
            (Nat.add (Nat.mul 3 rerr) (Nat.mul 2 lerr))) : ℕ) : ℝ) / (2 ^ 352 : ℝ) := by
        rw [hlmin_eq]
        simp only [Nat.add_eq, Nat.mul_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
        generalize (2 : ℝ) ^ 352 = S
        ring
      have hPQ_app := hrdeg ▸ gateListTransferPQ_append 48 gs_l gs_r
      have hdeg_comm : rdeg + ldeg = Nat.add ldeg rdeg := Nat.add_comm rdeg ldeg
      exact ⟨by simp [List.length_append, hldeg, hrdeg], by simp only [Nat.add_eq]; omega,
        by rw [← sched_sTree_eq]; exact Nat.ble_eq.mp herr_ble,
        hrep_out.trans (congrArg (fun n ↦
          pack768 (List.replicate n 1)) (by simp only [Nat.add_eq]; omega)),
        ⟨fpr, fpi⟩, ⟨fqr, fqi⟩,
        sched_polyPNValid_cast_deg hdeg_comm hfpr_v, sched_polyPNValid_cast_deg hdeg_comm hfpi_v,
        sched_polyPNValid_cast_deg hdeg_comm hfqr_v, sched_polyPNValid_cast_deg hdeg_comm hfqi_v,
        by rw [hPQ_app, ← herr_eq]; exact sched_polyCApprox_trans hPQ_rnd.1 hbil.1,
        by rw [hPQ_app, ← herr_eq]; exact sched_polyCApprox_trans hPQ_rnd.2 hbil.2⟩
  · rw [ite_eq_right hcond] at hm
    exact mergeNodesCGo_spec d gs_l gs_r l r out hl hr hlen hd hm
noncomputable def gqsp_pairStepSomeReal (m : gqsp_LevelMasksR)
    (ih : Option TreeNodeC → List TreeNodeC → Option (List TreeNodeC))
    (z : TreeNodeC) (a : List TreeNodeC) (x : TreeNodeC) : Option (List TreeNodeC) :=
  sched_optBind (gqsp_mergeNodesRealFast m x z) (gqsp_pushMergedNodeC ih a)
noncomputable def gqsp_mergePairsStepReal (m : gqsp_LevelMasksR) (nds : List TreeNodeC)
    (st : Option TreeNodeC) (acc : List TreeNodeC) : Option (List TreeNodeC) := @List.rec
    TreeNodeC (fun _ => Option TreeNodeC → List TreeNodeC → Option (List TreeNodeC)) (fun s a
    => @Option.casesOn TreeNodeC (fun _ => Option (List TreeNodeC)) s (some (sched_revNodesTR a
    [])) (sched_finishMergePairsSomeC a)) (fun z _ ih s a => @Option.casesOn TreeNodeC (fun _
    => Option (List TreeNodeC)) s (sched_tramp (ih (some z) a)) (sched_tramp
    (gqsp_pairStepSomeReal m ih z a))) nds st acc
noncomputable def gqsp_mergePairsRevReal (nds acc : List TreeNodeC) : Option (List TreeNodeC)
    := @List.casesOn TreeNodeC (fun _ => Option (List TreeNodeC)) nds
    (some (sched_revNodesTR acc [])) (fun x rest1 => @List.casesOn TreeNodeC (fun _ => Option
    (List TreeNodeC)) rest1 (some (sched_revNodesTR (x :: acc) [])) (fun y rest =>
    gqsp_mergePairsStepReal (gqsp_mkLevelMasksR x y) (x :: y :: rest) none acc))
private theorem gqsp_mergePairsStepReal_spec (gs_x0 gs_y0 : List DyadicSu2Gate) (x0 y0 : TreeNodeC)
    (hx0 : TreeNodeCValid gs_x0 x0) (hy0 : TreeNodeCValid gs_y0 y0) (nds : List TreeNodeC) :
    ∀ (acc next : List TreeNodeC) (gss_nds gss_acc : List (List DyadicSu2Gate)),
      (List.Forall₂ TreeNodeCValid gss_nds nds → List.Forall₂ TreeNodeCValid gss_acc acc →
       (gss_acc.reverse.flatten ++ gss_nds.flatten).length ≤ 262144 →
       gqsp_mergePairsStepReal (gqsp_mkLevelMasksR x0 y0) nds none acc = some next →
       ∃ gss_next, List.Forall₂ TreeNodeCValid gss_next next ∧
         gss_next.flatten = gss_acc.reverse.flatten ++ gss_nds.flatten) ∧
      (∀ (x : TreeNodeC) (gs_x : List DyadicSu2Gate), TreeNodeCValid gs_x x →
       List.Forall₂ TreeNodeCValid gss_nds nds → List.Forall₂ TreeNodeCValid gss_acc acc →
       (gss_acc.reverse.flatten ++ (gs_x ++ gss_nds.flatten)).length ≤ 262144 →
       gqsp_mergePairsStepReal (gqsp_mkLevelMasksR x0 y0) nds (some x) acc = some next →
       ∃ gss_next, List.Forall₂ TreeNodeCValid gss_next next ∧
         gss_next.flatten = gss_acc.reverse.flatten ++ (gs_x ++ gss_nds.flatten)) := by
  have hrev {acc next : List TreeNodeC} {gss_acc : List (List DyadicSu2Gate)}
      (hf2 : List.Forall₂ TreeNodeCValid gss_acc acc)
      (h : some (sched_revNodesTR acc []) = some next) :
      ∃ gss_next, List.Forall₂ TreeNodeCValid gss_next next ∧
        gss_next.flatten = gss_acc.reverse.flatten := by
    injection h with heq; subst heq
    rw [sched_revNodesTR_eq, List.append_nil]
    exact ⟨gss_acc.reverse, sched_forall2_reverse hf2, rfl⟩
  induction nds with
  | nil =>
    intro acc next gss_nds gss_acc
    refine ⟨fun hf2_nds hf2_acc _ h ↦ ?_, fun x gs_x hx hf2_nds hf2_acc _ h ↦ ?_⟩
    · rcases sched_forall2_nil_right hf2_nds with rfl
      simpa only [List.flatten_nil, List.append_nil] using hrev hf2_acc h
    · rcases sched_forall2_nil_right hf2_nds with rfl
      simpa only [List.reverse_cons, List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil] using hrev (List.Forall₂.cons hx hf2_acc) h
  | cons z rest ih =>
    intro acc next gss_nds gss_acc
    refine ⟨fun hf2_nds hf2_acc hlen h ↦ ?_, fun x gs_x hx hf2_nds hf2_acc hlen h ↦ ?_⟩
    · rcases sched_forall2_cons_right hf2_nds with ⟨gs_z, gss_rest, rfl, hz, hf2_rest⟩
      rcases (ih acc next gss_rest gss_acc).2 z gs_z hz hf2_rest hf2_acc
        (by simpa only [List.flatten_cons] using hlen) h with ⟨gss_next, hf2_next, hflat⟩
      exact ⟨gss_next, hf2_next, by simpa only [List.flatten_cons] using hflat⟩
    · rcases sched_forall2_cons_right hf2_nds with ⟨gs_y, gss_rest, rfl, hy, hf2_rest⟩
      change sched_optBind (gqsp_mergeNodesRealFast _ x z)
        (fun xy => gqsp_mergePairsStepReal _ rest none (xy :: acc)) = some next at h
      rcases sched_optBind_eq_some h with ⟨xy, hxy, h⟩
      have hflat_eq : ((gs_x ++ gs_y) :: gss_acc).reverse.flatten ++ gss_rest.flatten =
          gss_acc.reverse.flatten ++ (gs_x ++ (gs_y :: gss_rest).flatten) := by
        simp only [List.reverse_cons, List.flatten_append, List.flatten_cons,
          List.flatten_nil, List.append_nil, List.append_assoc]
      have hlen_xy : (gs_x ++ gs_y).length ≤ 262144 :=
        sched_len_mid_le (by simpa only [List.flatten_cons] using hlen)
      have hxy_val : TreeNodeCValid (gs_x ++ gs_y) xy := by
        have hr_le : z.deg ≤ 262144 := by have := hy.1; rw [List.length_append] at hlen_xy; omega
        rcases gqsp_swarDepth_bounds z.deg hr_le with ⟨_, hd⟩
        unfold gqsp_mergeNodesRealFast at hxy
        cases hdeg : Bool.and (Nat.beq x.deg x0.deg) (Nat.beq z.deg y0.deg)
        · rw [gqsp_mkLevelMasksR_eq x0 y0, gqsp_mergeWithMasksR_mk,
            ite_eq_right (by rw [hdeg]; simp)] at hxy
          exact mergeNodesCGo_spec (gqsp_swarDepth z.deg) gs_x gs_y x z xy hx hy hlen_xy hd hxy
        · rcases (Bool.and_eq_true _ _).mp hdeg with ⟨hld, hrd⟩
          rw [Nat.beq_eq] at hld hrd
          have hmk : gqsp_mkLevelMasksR x0 y0 = gqsp_mkLevelMasksR x z := by
            unfold gqsp_mkLevelMasksR
            rw [hld, hrd, hx.2.2.2.1, hx0.2.2.2.1, hy.2.2.2.1, hy0.2.2.2.1, hld, hrd]
          rw [hmk] at hxy
          exact gqsp_mergeWithMasksR_self_spec (gqsp_swarDepth z.deg) gs_x gs_y x z xy hx hy hlen_xy
            hd hxy
      rcases (ih (xy :: acc) next gss_rest ((gs_x ++ gs_y) :: gss_acc)).1 hf2_rest
        (List.Forall₂.cons hxy_val hf2_acc) (hflat_eq.symm ▸ hlen) h with ⟨gss_next, hf2_next,
          hflat⟩
      exact ⟨gss_next, hf2_next, hflat.trans hflat_eq⟩
noncomputable def gqsp_evalTournamentReal (fuel : ℕ) : List TreeNodeC → Option TreeNodeC :=
    @Nat.rec (fun _ => List TreeNodeC → Option TreeNodeC) sched_evalTournamentBaseC (fun _ ih
    nds => @List.casesOn TreeNodeC (fun _ => Option TreeNodeC) nds none (fun x rest1 =>
    @List.casesOn TreeNodeC (fun _ => Option TreeNodeC) rest1 (some x) (fun y rest =>
    sched_optBind (gqsp_mergePairsRevReal (x :: y :: rest) []) ih))) fuel
private theorem gqsp_evalTournamentReal_spec (fuel : ℕ) : ∀ (nds : List TreeNodeC)
    (gss : List (List DyadicSu2Gate)) (root : TreeNodeC), List.Forall₂ TreeNodeCValid gss nds →
    gss.flatten.length ≤ 262144 → gqsp_evalTournamentReal fuel nds = some root →
    TreeNodeCValid gss.flatten root := by
  have hsingle {r root : TreeNodeC} {gss : List (List DyadicSu2Gate)}
      (hf2 : List.Forall₂ TreeNodeCValid gss [r]) (h : some r = some root) :
      TreeNodeCValid gss.flatten root := by
    injection h with heq; subst heq
    rcases sched_forall2_cons_right hf2 with ⟨gs_r, gss_0, rfl, hr, hf2_0⟩
    rcases sched_forall2_nil_right hf2_0 with rfl
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using hr
  induction fuel with
  | zero =>
    intro nds gss root hf2 _ h
    rcases nds with _ | ⟨r, _ | ⟨_, _⟩⟩
    · cases h
    · exact hsingle hf2 h
    · cases h
  | succ fuel ih =>
    intro nds gss root hf2 hlen h
    rcases nds with _ | ⟨x, _ | ⟨y, rest⟩⟩
    · cases h
    · exact hsingle hf2 h
    · change sched_optBind (gqsp_mergePairsRevReal (x :: y :: rest) [])
        (gqsp_evalTournamentReal fuel) = some root at h
      rcases sched_optBind_eq_some h with ⟨next, hmp, h⟩
      rcases sched_forall2_cons_right hf2 with ⟨gs_x, gss_1, rfl, hx, hf2_1⟩
      rcases sched_forall2_cons_right hf2_1 with ⟨gs_y, gss_rest, rfl, hy, _⟩
      rcases (gqsp_mergePairsStepReal_spec gs_x gs_y x y hx hy (x :: y :: rest) [] next
        (gs_x :: gs_y :: gss_rest) []).1 hf2 List.Forall₂.nil
        (by simpa only [List.reverse_nil, List.flatten_nil, List.nil_append] using hlen) hmp with
        ⟨gss_next, hf2_next, hflat⟩
      rw [List.reverse_nil, List.flatten_nil, List.nil_append] at hflat
      exact hflat ▸ ih next gss_next root hf2_next (hflat.symm ▸ hlen) h
/-- Evaluate a chunked `DyadicSu2Gate` list via the 2-channel real tournament tree. -/
noncomputable def gqsp_evalSubTreeReal (fuel : ℕ) (chs : List (List DyadicSu2Gate)) : Option
    TreeNodeC :=
  sched_optBind (leavesChunksRevC chs []) (gqsp_evalTournamentReal fuel)
theorem gqsp_evalSubTreeReal_spec (fuel : ℕ) (chs : List (List DyadicSu2Gate))
    (root : TreeNodeC) (hlen : chs.flatten.length ≤ 262144)
    (h : gqsp_evalSubTreeReal fuel chs = some root) : TreeNodeCValid chs.flatten root := by
  unfold gqsp_evalSubTreeReal at h
  rcases sched_optBind_eq_some h with ⟨leaves, hl, ht⟩
  rcases leavesChunksRevC_spec chs leaves hl with ⟨gss, hf2, hflat⟩
  exact hflat ▸ gqsp_evalTournamentReal_spec fuel leaves gss root hf2 (hflat.symm ▸ hlen) ht
noncomputable def gqsp_srevNatStepGo (ih : ℕ → List ℕ →
    List ℕ) (x : ℕ) (acc : List ℕ) (s s1 : ℕ) : List ℕ :=
  ta_tramp (ih s1 (ta_idSalt s x :: acc))
noncomputable def gqsp_srevNatTR (xs : List ℕ) (s0 : ℕ) (acc0 : List ℕ) : List ℕ := @List.rec
    ℕ (fun _ => ℕ → List ℕ → List ℕ) (fun _ a => a) (fun x _ ih s a => ta_tfList
    (gqsp_srevNatStepGo ih x a s) (Nat.add 1 s)) xs s0 acc0
theorem gqsp_srevNatTR_eq : ∀ (xs : List ℕ) (s : ℕ) (acc : List ℕ),
    gqsp_srevNatTR xs s acc = ta_revNatTR xs acc
  | [], _, _ => rfl
  | x :: xs, s, acc => by
      change ta_tfList (gqsp_srevNatStepGo (gqsp_srevNatTR xs) x acc s) (Nat.add 1 s) = _
      simp only [ta_tfList_eq, gqsp_srevNatStepGo, ta_tramp, ta_idSalt, ta_revNatTR_cons]
      exact gqsp_srevNatTR_eq xs (Nat.add 1 s) (x :: acc)
noncomputable def gqsp_tfPQ (f : ℕ → List PQPair) (x : ℕ) : List PQPair :=
  @Nat.casesOn (fun _ => List PQPair) (Nat.add 1 x) [] f
theorem gqsp_tfPQ_eq (f : ℕ → List PQPair) (x : ℕ) : gqsp_tfPQ f x = f x := by
  change @Nat.casesOn (fun _ => List PQPair) (1 + x) [] f = f x
  rw [Nat.one_add]
noncomputable def gqsp_srevPQStepGo (ih : ℕ → List PQPair → List PQPair)
    (ph qh : ℕ) (acc : List PQPair) (s s1 : ℕ) : List PQPair :=
  ta_tramp (ih s1 (PQPair.mk (ta_idSalt s ph) qh :: acc))
noncomputable def gqsp_srevPQTR (xs : List PQPair) (s0 : ℕ) (acc0 : List PQPair) : List
    PQPair := @List.rec PQPair (fun _ => ℕ → List PQPair → List PQPair) (fun _ a => a) (fun h
    _ ih s a => @PQPair.casesOn (fun _ => List PQPair) h (fun ph qh => gqsp_tfPQ
    (gqsp_srevPQStepGo ih ph qh a s) (Nat.add 1 s))) xs s0 acc0
theorem gqsp_srevPQTR_eq : ∀ (xs : List PQPair) (s : ℕ) (acc : List PQPair),
    gqsp_srevPQTR xs s acc = ta_revPQTR xs acc
  | [], _, _ => rfl
  | ⟨ph, qh⟩ :: xs, s, acc => by
      change gqsp_tfPQ (gqsp_srevPQStepGo (gqsp_srevPQTR xs) ph qh acc s) (Nat.add 1 s) = _
      simp only [gqsp_tfPQ_eq, gqsp_srevPQStepGo, ta_tramp, ta_idSalt, ta_revPQTR_cons]
      exact gqsp_srevPQTR_eq xs (Nat.add 1 s) (⟨ph, qh⟩ :: acc)
noncomputable def gqsp_ssplitPRevFast (B m0 : ℕ) (ps0 neg0 : List ℕ) : List ℕ × ℕ × List ℕ :=
    @List.rec ℕ (fun _ => ℕ → List ℕ → List ℕ × ℕ × List ℕ)
    (fun m neg_acc => ta_splitPRevNil B m neg_acc) (fun p ps ih m neg_acc => @Nat.casesOn (fun
    _ => List ℕ × ℕ × List ℕ) m (neg_acc, p, ps) (fun m' => ta_tramp (ih m' (ta_idSalt m' p ::
    neg_acc)))) ps0 m0 neg0
theorem gqsp_ssplitPRevFast_eq (B : ℕ) : ∀ (ps : List ℕ) (m : ℕ) (neg_acc : List ℕ),
      gqsp_ssplitPRevFast B m ps neg_acc = ta_splitPRevFast B m ps neg_acc
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | p :: ps, m + 1, neg_acc =>
      gqsp_ssplitPRevFast_eq B ps m (p :: neg_acc)
noncomputable def gqsp_stepNotPar1 (ih : ℕ → Bool → List ℕ → ℕ → ℕ) (k' : ℕ) (par : Bool)
    (pt : List ℕ) (acc' : ℕ) : ℕ := @Bool.casesOn (fun _ => ℕ) par
    (ta_tramp (ih k' true pt acc')) (ta_tramp (ih k' false pt acc'))
noncomputable def gqsp_stepNotPar2 (ih : ℕ → Bool → List ℕ → List ℕ → ℕ → ℕ) (rem' : ℕ)
    (par : Bool) (nt pt : List ℕ) (acc' : ℕ) : ℕ := @Bool.casesOn (fun _ => ℕ) par
    (ta_tramp (ih rem' true nt pt acc')) (ta_tramp (ih rem' false nt pt acc'))
noncomputable def gqsp_chebL1PosBoolPar (B B2 Bw W_err_dpos err_d_in pad : ℕ)
    (ws0 : List ℕ) (rem0 : ℕ) (par0 : Bool) (neg0 pos0 : List ℕ) (acc0 : ℕ) : ℕ :=
  @List.rec ℕ (fun _ => ℕ → Bool → List ℕ → List ℕ → ℕ → ℕ)
    (fun _ _ _ _ acc => Nat.add acc (Nat.mul pad W_err_dpos))
    (fun w wt ih rem par neg_cur pos_cur acc =>
      @Nat.casesOn (fun _ => ℕ) rem
        (ta_tfNat (ta_chebTailFast Bw W_err_dpos pad wt)
          (Nat.add acc (Nat.add (natAbsDiff w Bw) W_err_dpos)))
        (fun rem' =>
          @List.casesOn ℕ (fun _ => ℕ) neg_cur
            (@List.casesOn ℕ (fun _ => ℕ) pos_cur
              (let p_pos := ta_parFlip par B2 B
               ta_tfNat (gqsp_stepNotPar2 ih rem' par [] [])
                 (Nat.add acc (Nat.add (natAbsDiff (Nat.add (Nat.add p_pos B) Bw) (Nat.add w B2))
                   err_d_in)))
              (fun p_pos_raw pt =>
                let p_pos := ta_parFlip par B2 p_pos_raw
                ta_tfNat (gqsp_stepNotPar2 ih rem' par [] pt)
                  (Nat.add acc (Nat.add (natAbsDiff (Nat.add (Nat.add p_pos B) Bw) (Nat.add w B2))
                    err_d_in))))
            (fun p_neg nt =>
              @List.casesOn ℕ (fun _ => ℕ) pos_cur
                (let p_pos := ta_parFlip par B2 B
                 ta_tfNat (gqsp_stepNotPar2 ih rem' par nt [])
                   (Nat.add acc (Nat.add (natAbsDiff (Nat.add (Nat.add p_pos p_neg) Bw) (Nat.add w
                     B2)) err_d_in)))
                (fun p_pos_raw pt =>
                  let p_pos := ta_parFlip par B2 p_pos_raw
                  ta_tfNat (gqsp_stepNotPar2 ih rem' par nt pt)
                    (Nat.add acc (Nat.add (natAbsDiff (Nat.add (Nat.add p_pos p_neg) Bw) (Nat.add w
                      B2)) err_d_in))))))
    ws0 rem0 par0 neg0 pos0 acc0
theorem gqsp_chebL1PosBoolPar_cons_succ (B B2 Bw W_err_dpos err_d_in pad w : ℕ) (wt : List ℕ)
    (rem' : ℕ) (par : Bool) (neg_cur pos_cur : List ℕ) (acc : ℕ) :
    gqsp_chebL1PosBoolPar B B2 Bw W_err_dpos err_d_in pad (w :: wt) (rem' +
      1) par neg_cur pos_cur acc =
      let p_neg := neg_cur.headD B
      let p_pos := ta_parFlip par B2 (pos_cur.headD B)
      gqsp_chebL1PosBoolPar B B2 Bw W_err_dpos err_d_in pad wt rem' (Bool.not par) neg_cur.tail
        pos_cur.tail
        (Nat.add acc (Nat.add (natAbsDiff (Nat.add (Nat.add p_pos p_neg) Bw) (Nat.add w B2))
          err_d_in)) := by
  cases par <;> rcases neg_cur with _ | ⟨_, _⟩ <;> rcases pos_cur with _ | ⟨_, _⟩ <;>
    exact ta_tfNat_eq _ _
private theorem gqsp_chebL1PosBoolPar_eq (B B2 Bw W_err_dpos err_d_in pad : ℕ) :
    ∀ (ws : List ℕ) (rem : ℕ) (par : Bool) (neg_cur pos_cur : List ℕ) (acc : ℕ),
      gqsp_chebL1PosBoolPar B B2 Bw W_err_dpos err_d_in pad ws rem par neg_cur pos_cur acc =
        ta_chebL1PosBoolPar B B2 Bw W_err_dpos err_d_in pad ws rem par neg_cur pos_cur acc
  | [], _, _, _, _, _ => rfl
  | _ :: _, 0, _, _, _, _ => rfl
  | w :: wt, rem' + 1, par, neg_cur, pos_cur, acc => by
      rw [gqsp_chebL1PosBoolPar_cons_succ, ta_chebL1PosBoolPar_cons_succ]
      exact gqsp_chebL1PosBoolPar_eq B B2 Bw W_err_dpos err_d_in pad wt rem' _ _ _ _
noncomputable def gqsp_chebL1StartGo (M1 B B2 Bw W_err_dpos pad : ℕ)
    (wt neg_rev pos_tail : List ℕ) (err_d_in term0 : ℕ) : ℕ :=
  gqsp_chebL1PosBoolPar B B2 Bw W_err_dpos err_d_in pad wt M1 true neg_rev pos_tail term0
noncomputable def gqsp_chebL1POnlyFast (M1 B B2 Bw R_final W_err_d0 W_err_dpos pad : ℕ)
    (neg_rev : List ℕ) (p_center : ℕ) (pos_tail ws_unpad : List ℕ) : ℕ := @List.casesOn ℕ
    (fun _ => ℕ) ws_unpad 0 (fun w0 wt => ta_tfNat (ta_tfNatFn (gqsp_chebL1StartGo M1 B B2 Bw
    W_err_dpos pad wt neg_rev pos_tail) (Nat.add (Nat.mul 2 R_final) W_err_dpos)) (Nat.add
    (natAbsDiff (Nat.add p_center Bw) (Nat.add w0 B)) (Nat.add R_final W_err_d0)))
noncomputable def gqsp_asymDefectLoopPOnlyFast (B B2 two_Rf : ℕ)
    (k0 : ℕ) (par0 : Bool) (neg0 pos0 : List ℕ) (acc0 : ℕ) : ℕ :=
  @List.rec ℕ (fun _ => ℕ → Bool → List ℕ → ℕ → ℕ)
    (fun k par pos_cur acc => ta_asymDefectEmptyPOnly B B2 two_Rf k par pos_cur acc)
    (fun p_neg _ ih k par pos_cur acc =>
      @Nat.casesOn (fun _ => ℕ) k acc (fun k' =>
        @List.casesOn ℕ (fun _ => ℕ) pos_cur
          (let p_pos := ta_parFlip par B2 B
           ta_tfNat (gqsp_stepNotPar1 ih k' par [])
             (Nat.add acc (Nat.add (natAbsDiff p_pos p_neg) two_Rf)))
          (fun p_pos_raw pt =>
            let p_pos := ta_parFlip par B2 p_pos_raw
            ta_tfNat (gqsp_stepNotPar1 ih k' par pt)
              (Nat.add acc (Nat.add (natAbsDiff p_pos p_neg) two_Rf)))))
    neg0 k0 par0 pos0 acc0
theorem gqsp_asymDefectLoopPOnlyFast_cons (B B2 two_Rf k' : ℕ) (par : Bool)
    (p_neg : ℕ) (nt pos_cur : List ℕ) (acc : ℕ) :
    gqsp_asymDefectLoopPOnlyFast B B2 two_Rf (k' + 1) par (p_neg :: nt) pos_cur acc =
      let p_pos := ta_parFlip par B2 (pos_cur.headD B)
      gqsp_asymDefectLoopPOnlyFast B B2 two_Rf k' (Bool.not par) nt pos_cur.tail
        (Nat.add acc (Nat.add (natAbsDiff p_pos p_neg) two_Rf)) := by
  cases par <;> rcases pos_cur with _ | ⟨_, _⟩ <;> exact ta_tfNat_eq _ _
private theorem gqsp_asymDefectLoopPOnlyFast_eq (B B2 two_Rf : ℕ) :
    ∀ (neg_cur : List ℕ) (k : ℕ) (par : Bool) (pos_cur : List ℕ) (acc : ℕ),
      gqsp_asymDefectLoopPOnlyFast B B2 two_Rf k par neg_cur pos_cur acc =
        ta_asymDefectLoopPOnlyFast B B2 two_Rf k par neg_cur pos_cur acc
  | [], _, _, _, _ => rfl
  | _ :: _, 0, _, _, _ => rfl
  | p_neg :: nt, k' + 1, par, pos_cur, acc => by
      rw [gqsp_asymDefectLoopPOnlyFast_cons, ta_asymDefectLoopPOnlyFast_cons]
      exact gqsp_asymDefectLoopPOnlyFast_eq B B2 two_Rf nt k' _ _ _
noncomputable def gqsp_asymDefectStartGo (M1 B B2 : ℕ) (neg_rev pos_tail : List ℕ) (two_Rf : ℕ) : ℕ
    :=
  gqsp_asymDefectLoopPOnlyFast B B2 two_Rf M1 true neg_rev pos_tail 0
noncomputable def gqsp_asymDefectPOnlyFast (M1 B B2 R_final : ℕ) (neg_rev pos_tail : List ℕ) : ℕ :=
  ta_tfNat (gqsp_asymDefectStartGo M1 B B2 neg_rev pos_tail) (Nat.mul 2 R_final)
noncomputable def gqsp_forceListBool (xs : List ℕ) (k : List ℕ → Bool) : Bool :=
  @List.casesOn ℕ (fun _ => Bool) xs (k []) (fun h t => k (h :: t))
theorem gqsp_forceListBool_eq (xs : List ℕ) (k : List ℕ → Bool) :
    gqsp_forceListBool xs k = k xs := by
  cases xs <;> rfl
/-- 2-term real root dot-product + unpacker avoiding `0 * root.pi` and `0 * root.qi`. -/
noncomputable def gqsp_finishRootVec2RealFast (unpackShr256 : ℕ → ℕ → ℕ → List ℕ)
    (s d n_lanes rep_bcomb : ℕ) (c1 x1 c3 x3 : PolyPN) : List ℕ := sched_stfList s (fun up =>
    sched_stfList (Nat.add 1 s) (fun un => sched_stfList (Nat.add 2 s) (fun w => unpackShr256 d
    n_lanes w) (Nat.sub (Nat.add up rep_bcomb) un)) (mulAdd2Neg c1 x1 c3 x3))
    (mulAdd2Pos c1 x1 c3 x3)
/-- Chunked `64`-lane `pack768` splitter (`≤ 2,048` pairs instead of `125,496` list elements in
  tree closures). -/
noncomputable def gqsp_stfPairs (s : ℕ) (f : ℕ → List (ℕ × ℕ)) (x : ℕ) : List (ℕ × ℕ) :=
  @Nat.casesOn (fun _ => List (ℕ × ℕ)) (Nat.add 1 (sched_idSalt s x)) [] f
theorem gqsp_stfPairs_eq (s : ℕ) (f : ℕ → List (ℕ × ℕ)) (x : ℕ) : gqsp_stfPairs s f x = f x := by
  change @Nat.casesOn (fun _ => List (ℕ × ℕ)) (1 + sched_idSalt s x) [] f = f x
  rw [sched_idSalt_eq, Nat.one_add]
noncomputable def gqsp_splitLeaf64Go (s n : ℕ) (acc : List (ℕ × ℕ)) (w0 : ℕ) : List (ℕ × ℕ) :=
  (sched_idSalt (Nat.add 7 (Nat.mul 512 s)) n, w0) :: acc
noncomputable def gqsp_splitLeaf64 (s n w : ℕ) (acc : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  gqsp_stfPairs (Nat.add 8 (Nat.mul 512 s)) (gqsp_splitLeaf64Go s n acc) w
theorem gqsp_splitLeaf64_eq (s n w : ℕ) (acc : List (ℕ × ℕ)) :
    gqsp_splitLeaf64 s n w acc = (n, w) :: acc := by
  unfold gqsp_splitLeaf64 gqsp_splitLeaf64Go
  rw [gqsp_stfPairs_eq, sched_idSalt_eq]
noncomputable def gqsp_splitStepLo (rec_lo : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ))
    (acc1 : List (ℕ × ℕ)) (lo : ℕ) : List (ℕ × ℕ) := rec_lo lo acc1
noncomputable def gqsp_splitStepHi (hSalt w : ℕ)
    (rec_lo rec_hi : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ))
    (acc : List (ℕ × ℕ)) (sh w_hi : ℕ) : List (ℕ × ℕ) :=
  let acc1 := rec_hi w_hi acc
  let w_lo := Nat.sub (sched_idSalt (Nat.add 2 hSalt) w)
    (Nat.shiftLeft (sched_idSalt (Nat.add 3 hSalt) w_hi) sh)
  gqsp_stfPairs (Nat.add 4 hSalt) (gqsp_splitStepLo rec_lo acc1) w_lo
noncomputable def gqsp_splitStepFast (hSalt w : ℕ)
    (rec_lo rec_hi : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)) (acc : List (ℕ × ℕ)) (sh : ℕ) : List
    (ℕ × ℕ) := gqsp_stfPairs hSalt (gqsp_splitStepHi hSalt w rec_lo rec_hi acc sh)
    (Nat.shiftRight (sched_idSalt (Nat.add 1 hSalt) w) sh)
noncomputable def gqsp_splitWords64Split (ih : ℕ → ℕ → ℕ → List (ℕ × ℕ) → List (ℕ × ℕ))
    (s n w : ℕ) (acc : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  if Nat.ble n 64 then
    gqsp_splitLeaf64 s n w acc
  else
    let h := Nat.div n 2
    gqsp_splitStepFast (Nat.mul 512 s) w
      (ih (Nat.mul 2 s) h)
      (ih (Nat.add 1 (Nat.mul 2 s)) (Nat.sub n h))
      acc (Nat.mul 768 h)
noncomputable def gqsp_splitWords64Aux (d : ℕ) : ℕ → ℕ → ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) :=
    @Nat.rec (fun _ => ℕ → ℕ → ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)) gqsp_splitLeaf64
    (fun _ ih => gqsp_splitWords64Split ih) d
noncomputable def gqsp_peelWords64StepGo (ih : ℕ → List ℕ → List ℕ)
    (n w s : ℕ) (racc : List ℕ) (s' : ℕ) : List ℕ :=
  gqsp_tramp (ih s' (gqsp_unpackPow2Leaf4SaltAux (Nat.div n 4) (Nat.mod n 4) (Nat.add 16 s) w racc))
noncomputable def gqsp_peelWords64RevTR (chunks0 : List (ℕ × ℕ)) (s0 : ℕ) (racc0 : List ℕ) :
    List ℕ := @List.rec (ℕ × ℕ) (fun _ => ℕ → List ℕ → List ℕ) (fun _ racc => racc) (fun p _
    ih s racc => @Prod.casesOn _ _ (fun _ => List ℕ) p fun n w => sched_stfList s
    (gqsp_peelWords64StepGo ih n w s racc) (Nat.add 512 s)) chunks0 s0 racc0
theorem gqsp_peelWords64RevTR_cons (n w : ℕ) (chunks : List (ℕ × ℕ)) (s : ℕ) (racc : List ℕ) :
    gqsp_peelWords64RevTR ((n, w) :: chunks) s racc =
      gqsp_peelWords64RevTR chunks (Nat.add 512 s)
        (gqsp_unpackPow2Leaf4SaltAux (Nat.div n 4) (Nat.mod n 4) (Nat.add 16 s) w racc) := by
  dsimp only [gqsp_peelWords64RevTR]
  simp only [sched_stfList_eq, gqsp_peelWords64StepGo, gqsp_tramp]
private theorem gqsp_splitWords64Aux_peel_eq (d : ℕ) : ∀ (s n : ℕ) (zs : List ℕ)
    (acc : List (ℕ × ℕ)), zs.length = n → (∀ z ∈ zs, z < 2 ^ 768) → ∀ (sp : ℕ)
    (racc : List ℕ), ∃ sp' : ℕ, gqsp_peelWords64RevTR
    (gqsp_splitWords64Aux d s n (pack768 zs) acc) sp racc = gqsp_peelWords64RevTR acc sp'
    ((zs.map (fun z ↦ Nat.shiftRight z 256)).reverse ++ racc) := by
  have hleaf {s n : ℕ} {zs : List ℕ} {acc : List (ℕ × ℕ)} {sp : ℕ} {racc : List ℕ}
      (hlen : zs.length = n) (hzs : ∀ z ∈ zs, z < 2 ^ 768) :
      ∃ sp', gqsp_peelWords64RevTR (gqsp_splitLeaf64 s n (pack768 zs) acc) sp racc =
        gqsp_peelWords64RevTR acc sp' ((zs.map (fun z ↦ Nat.shiftRight z 256)).reverse ++ racc) :=
    ⟨Nat.add 512 sp, by
      rw [gqsp_splitLeaf64_eq, gqsp_peelWords64RevTR_cons,
        gqsp_unpackPow2Leaf4SaltAux_eq (Nat.mod n 4) (Nat.div n 4) (Nat.add 16 sp) zs racc
          (by change zs.length = 4 * (n / 4) + n % 4; omega) hzs]⟩
  induction d with
  | zero => exact fun _ _ _ _ hlen hzs _ _ ↦ hleaf hlen hzs
  | succ d ih =>
    intro s n zs acc hlen hzs sp racc
    change ∃ sp', gqsp_peelWords64RevTR
      (gqsp_splitWords64Split (gqsp_splitWords64Aux d) s n (pack768 zs) acc) sp racc = _
    unfold gqsp_splitWords64Split
    cases hb : Nat.ble n 64
    · simp only [Bool.false_eq_true, ↓reduceIte]
      let h := n / 2
      have hsp := List.take_append_drop h zs
      have hl1 : (zs.take h).length = h := by rw [List.length_take]; omega
      have hl2 : (zs.drop h).length = n - h := by rw [List.length_drop]; omega
      have hz1 : ∀ a ∈ zs.take h, a < 2 ^ 768 := fun a ha ↦ hzs a (List.mem_of_mem_take ha)
      have hz2 : ∀ a ∈ zs.drop h, a < 2 ^ 768 := fun a ha ↦ hzs a (List.mem_of_mem_drop ha)
      have hp : pack768 zs = pack768 (zs.take h) + (pack768 (zs.drop h) <<< (768 * h)) := by
        conv_lhs => rw [← hsp]
        rw [sched_pack768_append, hl1]
      have hlt1 : pack768 (zs.take h) < 1 <<< (768 * h) := by
        simpa only [hl1] using sched_pack768_lt _ (fun a ha ↦ sched_pow768_eq_pow.symm ▸ hz1 a ha)
      have hpack : gqsp_splitStepFast (Nat.mul 512 s) (pack768 zs)
          (gqsp_splitWords64Aux d (Nat.mul 2 s) h)
          (gqsp_splitWords64Aux d (Nat.add 1 (Nat.mul 2 s)) (Nat.sub n h)) acc (Nat.mul 768 h) =
          gqsp_splitWords64Aux d (2 * s) h (pack768 (zs.take h))
            (gqsp_splitWords64Aux d (1 + 2 * s) (n - h) (pack768 (zs.drop h)) acc) := by
        rw [hp]
        unfold gqsp_splitStepFast gqsp_splitStepHi gqsp_splitStepLo
        simp only [gqsp_stfPairs_eq, sched_idSalt_eq, Nat.add_eq, Nat.sub_eq, Nat.mul_eq,
          show ∀ a b : ℕ, Nat.shiftLeft a b = a <<< b from fun _ _ ↦ rfl]
        rw [show Nat.shiftRight (pack768 (zs.take h) + (pack768 (zs.drop h) <<< (768 * h))) (768 *
          h) =
          pack768 (zs.drop h) from (Nat.shiftRight_eq_div_pow _ _).trans
            (sched_mod_div_768_mul_add h _ _ hlt1).2, Nat.add_sub_cancel_right]
      change ∃ sp', gqsp_peelWords64RevTR (gqsp_splitStepFast (Nat.mul 512 s) (pack768 zs)
        (gqsp_splitWords64Aux d (Nat.mul 2 s) h)
        (gqsp_splitWords64Aux d (Nat.add 1 (Nat.mul 2 s)) (Nat.sub n h)) acc (Nat.mul 768 h))
        sp racc = _
      rw [hpack]
      rcases ih (2 * s) h (zs.take h) _ hl1 hz1 sp racc with ⟨sp1, hpeel1⟩
      rcases ih (1 + 2 * s) (n - h) (zs.drop h) acc hl2 hz2 sp1 _ with ⟨sp2, hpeel2⟩
      exact ⟨sp2, by rw [hpeel1, hpeel2, ← List.append_assoc, ← List.reverse_append,
        ← List.map_append, hsp]⟩
    · simp only [↓reduceIte]
      exact hleaf hlen hzs
noncomputable def gqsp_sunpackShr256ChunkedGo (d n w0 s0 : ℕ) : List ℕ := gqsp_srevNatTR
    (gqsp_peelWords64RevTR (gqsp_splitWords64Aux (Nat.sub d 6) s0 n w0 []) (Nat.add 1 s0)
    []) (Nat.add 2 s0) []
noncomputable def gqsp_sunpackShr256ChunkedSalt (d n w0 : ℕ) : List ℕ := sched_tfList
    (gqsp_sunpackShr256ChunkedGo d n w0) (Nat.add 0x10000000000 (Nat.land (Nat.xor (Nat.mul
    0x9e3779b9 n) (Nat.xor (Nat.xor (Nat.xor (Nat.shiftRight w0 256) (Nat.shiftRight w0 1024))
    (Nat.xor (Nat.shiftRight w0 4096) (Nat.shiftRight w0 16384))) (Nat.xor (Nat.xor
    (Nat.shiftRight w0 65536) (Nat.shiftRight w0 524288)) (Nat.xor (Nat.shiftRight w0 4194304)
    (Nat.shiftRight w0 33554432))))) 0xfffffffff))
noncomputable def gqsp_sunpackShr256Chunked (d n w : ℕ) : List ℕ :=
  ta_tfList (gqsp_sunpackShr256ChunkedSalt d n) w
theorem gqsp_sunpackShr256Chunked_spec (d n : ℕ) (zs : List ℕ)
    (hzl : zs.length = n) (hzb : ∀ z ∈ zs, z < 2 ^ 768) :
    gqsp_sunpackShr256Chunked d n (pack768 zs) = zs.map (fun z ↦ Nat.shiftRight z 256) := by
  unfold gqsp_sunpackShr256Chunked gqsp_sunpackShr256ChunkedSalt gqsp_sunpackShr256ChunkedGo
  rw [ta_tfList_eq, sched_tfList_eq]
  rcases gqsp_splitWords64Aux_peel_eq (Nat.sub d 6) _ n zs [] hzl hzb _ [] with ⟨sp', hpeel⟩
  rw [hpeel]
  dsimp only [gqsp_peelWords64RevTR]
  rw [gqsp_srevNatTR_eq, ta_revNatTR_eq, List.append_nil, List.append_nil, List.reverse_reverse]
/-- Decode `256`-gate blocks directly into `List (List DyadicRyGate)` without flattening. -/
noncomputable def gqsp_decRyGatesChunksAcc (baseSalt : ℕ) (bss0 : List (List (ℕ × ℕ)))
    (tail0 : List (List DyadicRyGate)) : List (List DyadicRyGate) := @List.rec (List (ℕ × ℕ))
    (fun _ => ℕ → List (List DyadicRyGate)) (fun _ => tail0) (fun ws _ ih s => @Nat.casesOn
    (fun _ => List (List DyadicRyGate)) (Nat.add 1 (sched_idSalt s (Nat.add 131072 s))) [] (fun
    s' => gqsp_decRyGatesFast8WordsAcc ws (Nat.add 16 s) [] :: ih s')) bss0 baseSalt
noncomputable def gqsp_tfOptNat (f : ℕ → Option ℕ) (x : ℕ) : Option ℕ :=
  @Nat.casesOn (fun _ => Option ℕ) (Nat.add 1 x) none f
/-- Chunk-wise `DyadicRyGate` length and contraction checker (`≤ 256` gates per inner
  `List.rec`). -/
noncomputable def gqsp_ryLenContrChunkStep (D2 : ℕ) (gs0 : List DyadicRyGate) (cnt0 : ℕ) : Option ℕ
    :=
  @List.rec DyadicRyGate (fun _ => ℕ → Option ℕ)
    (fun cnt => some cnt)
    (fun g _ ih cnt =>
      let gsm := gateSM g
      match Nat.ble (Nat.add (Nat.mul gsm.1.2 gsm.1.2) (Nat.mul gsm.2.2 gsm.2.2)) D2 with
      | true => gqsp_tfOptNat (fun cnt' => gqsp_tramp (ih cnt')) (Nat.add 1 cnt)
      | false => none)
    gs0 cnt0
noncomputable def gqsp_ryLenContrChunksLoop (n_exp D2 : ℕ)
    (chs0 : List (List DyadicRyGate)) (cnt0 : ℕ) : Bool :=
  @List.rec (List DyadicRyGate) (fun _ => ℕ → Bool)
    (fun cnt => Nat.beq cnt n_exp)
    (fun ch _ ih cnt =>
      match gqsp_ryLenContrChunkStep D2 ch cnt with
      | some cnt' => gqsp_applyNat0Bool ih cnt'
      | none => false)
    chs0 cnt0
private theorem gqsp_ryLenContrChunkStep_bind_eq (n_exp D2 : ℕ) (ih_outer : ℕ → Bool)
    (rest : List DyadicRyGate)
    (h_outer : ∀ cnt, ih_outer cnt = gqsp_ryLenContrLoop n_exp D2 rest cnt) :
    ∀ (ch : List DyadicRyGate) (cnt : ℕ), (match gqsp_ryLenContrChunkStep D2 ch cnt with
       | some cnt' => gqsp_applyNat0Bool ih_outer cnt'
       | none => false) = gqsp_ryLenContrLoop n_exp D2 (ch ++ rest) cnt
  | [], cnt => by
      change gqsp_applyNat0Bool ih_outer cnt = gqsp_ryLenContrLoop n_exp D2 rest cnt
      rw [gqsp_applyNat0Bool_eq, h_outer]
  | g :: gs, cnt => by
      have htf (f : ℕ → Option ℕ) (x : ℕ) : gqsp_tfOptNat f x = f x := by
        change @Nat.casesOn (fun _ => Option ℕ) (1 + x) none f = f x
        rw [Nat.one_add]
      dsimp only [gqsp_ryLenContrChunkStep, List.cons_append]
      conv_rhs => rw [gqsp_ryLenContrLoop]
      dsimp only
      cases Nat.ble (Nat.add (Nat.mul (gateSM g).1.2 (gateSM g).1.2)
        (Nat.mul (gateSM g).2.2 (gateSM g).2.2)) D2
      · rfl
      · dsimp only
        rw [htf, gqsp_applyNat0Bool_eq]
        exact gqsp_ryLenContrChunkStep_bind_eq n_exp D2 ih_outer rest h_outer gs (Nat.add 1 cnt)
theorem gqsp_ryLenContrChunksLoop_eq (n_exp D2 : ℕ) :
    ∀ (chs : List (List DyadicRyGate)) (cnt : ℕ),
      gqsp_ryLenContrChunksLoop n_exp D2 chs cnt = gqsp_ryLenContrLoop n_exp D2 chs.flatten cnt
  | [], _ => rfl
  | ch :: chs, cnt => by
      rw [List.flatten_cons]
      exact gqsp_ryLenContrChunkStep_bind_eq n_exp D2
        (gqsp_ryLenContrChunksLoop n_exp D2 chs) chs.flatten
        (gqsp_ryLenContrChunksLoop_eq n_exp D2 chs) ch cnt
theorem gqsp_biCatBridgeCheckBle_of_memoChunks (M N_cat ana_u cap_u : ℕ)
    (C_orig_list : List ℕ) (ry_g0 : DyadicRyGate) (ry_chs : List (List DyadicRyGate))
    (h_ana : Nat.mul (Nat.add M 1) (Nat.mul (Nat.factorial 29) (Nat.pow 2 1458)) = 2 ^ 1412 * ana_u)
    (h_cap : Nat.mul N_cat (Nat.mul (Nat.factorial 29) (Nat.pow 2 1460)) = 2 ^ 1412 * cap_u)
    (h_ble : Nat.ble (Nat.add (gqsp_catUpperMemoChunks C_orig_list ([ry_g0] :: ry_chs) 0) ana_u)
      cap_u = true) :
    biCatBridgeCheckBle M N_cat C_orig_list (ry_g0 :: ry_chs.flatten) = true := by
  rw [gqsp_catUpperMemoChunks_eq, List.flatten_cons, List.singleton_append] at h_ble
  unfold biCatBridgeCheckBle
  simp only [forceNatFast_eq]
  rw [h_ana, h_cap, Nat.ble_eq]
  have hble := Nat.ble_eq.mp h_ble
  rw [Nat.add_eq] at hble ⊢
  have hpoly := gqsp_catUpperList_spec (Nat.factorial 29)
    (Nat.mul (Nat.factorial 29) (Nat.pow 2 1460)) rfl rfl C_orig_list (ry_g0 :: ry_chs.flatten) 0 0
      (Nat.zero_le _)
  exact (Nat.add_le_add_right hpoly _).trans
    ((Nat.mul_add _ _ _).symm ▸ Nat.mul_le_mul_left (2 ^ 1412) hble)
/-- Map each `DyadicRyGate` chunk independently to `DyadicSu2Gate` (`≤ 256` gates per
  `List.rec`). -/
noncomputable def gqsp_mapRyChunksToSu2 (chs0 : List (List DyadicRyGate)) : List
    (List DyadicSu2Gate) := @List.rec (List DyadicRyGate) (fun _ => List (List DyadicSu2Gate))
    [] (fun ch _ ih => gqsp_mapRyToSu2Fast ch :: ih) chs0
theorem gqsp_mapRyChunksToSu2_flatten : ∀ (chs : List (List DyadicRyGate)),
      (gqsp_mapRyChunksToSu2 chs).flatten = chs.flatten.map ryToSu2Gate
  | [] => rfl
  | ch :: chs => by
      have hcons : gqsp_mapRyChunksToSu2 (ch :: chs) =
          gqsp_mapRyToSu2Fast ch :: gqsp_mapRyChunksToSu2 chs := rfl
      rw [hcons, List.flatten_cons, gqsp_mapRyToSu2Fast_eq, gqsp_mapRyChunksToSu2_flatten chs,
        List.flatten_cons, List.map_append]
/-- Low-memory salted 1-angle post-root verifier destructuring `root` upfront and unpacking
  `64`-lane chunks. -/
noncomputable def gqsp_oneAnglePostRootRealFastBle (d M N_rec W_err_d0 W_err_dpos pad : ℕ)
    (g0 : DyadicSu2Gate) (root : TreeNodeC) (ws_unpad : List ℕ) : Bool :=
  @TreeNodeC.casesOn (fun _ => Bool) root
    (fun rdeg rsalt rrep1 rprp rprn _ _ rqrp rqrn _ _ rerr =>
      ta_tfBool (fun n_lanes =>
        ta_tfBool (fun rep_bcomb =>
          let c_ar := smToPolyPN g0.sar g0.mar
          let c_br := smToPolyPN g0.sbr g0.mbr
          let nc_br := negPolyPN c_br
          ta_tfBool (fun rqrp_rev =>
            ta_tfBool (fun rqrn_rev =>
              gqsp_forceListBool
                (gqsp_finishRootVec2RealFast gqsp_sunpackShr256Chunked 0x410001
                  d n_lanes rep_bcomb c_ar ⟨rprp, rprn⟩ nc_br ⟨rqrp_rev, rqrn_rev⟩)
                (fun uPre =>
                  gqsp_forceListBool (gqsp_srevNatTR uPre 1 []) (fun ruP =>
                    ta_tfBool (fun rprp_rev =>
                      ta_tfBool (fun rprn_rev =>
                        gqsp_forceListBool
                          (gqsp_finishRootVec2RealFast gqsp_sunpackShr256Chunked 0x420001
                            d n_lanes rep_bcomb c_ar ⟨rqrp, rqrn⟩ c_br ⟨rprp_rev, rprn_rev⟩)
                          (fun uQre =>
                            gqsp_forceListBool (gqsp_srevNatTR uQre 1 []) (fun ruQ =>
                              let pqM := gqsp_srevPQTR
                                (gqsp_interleave1AngleRevTR ta_B2 ta_BIAS_OUT 1 uPre uQre ruP ruQ
                                  []) 1 []
                              ta_tfBool (fun R_final =>
                                ta_tfBool (fun M1 =>
                                  ta_tfBool (fun B =>
                                    ta_tfBool (fun B2 =>
                                      ta_tfBool (fun Bw =>
                                        ta_tfBool (fun shift0 =>
                                          let p_fin :=
                                            gqsp_srevNatTR (ta_hadamardRevPOnlyFast B pqM 1 B []) 1
                                            []
                                          @Prod.casesOn _ _ (fun _ =>
                                            Bool) (gqsp_ssplitPRevFast B M1 p_fin [])
                                            fun neg_re p2_re =>
                                            @Prod.casesOn _ _ (fun _ =>
                                              Bool) p2_re fun pc_re pos_re =>
                                              let t1 :=
                                                gqsp_chebL1POnlyFast M1 B B2 Bw R_final W_err_d0
                                                W_err_dpos pad
                                                neg_re pc_re pos_re ws_unpad
                                              let t2 :=
                                                gqsp_asymDefectPOnlyFast M1 B B2 R_final neg_re
                                                pos_re
                                              let t3 := gqsp_qResidHadamardFast B B2 R_final pqM B 0
                                              Nat.ble (Nat.add (Nat.add t1 t2) t3) (Nat.mul N_rec
                                                shift0))
                                        ta_shift0)
                                      ta_Bw)
                                    ta_B2)
                                  ta_B)
                                (Nat.add M 1))
                              (Nat.add (Nat.add (Nat.shiftRight rerr 206) 2) 1))))
                      (gqsp_fastRevSwarSalt 8 rsalt d n_lanes rprn))
                    (gqsp_fastRevSwarSalt 8 rsalt d n_lanes rprp))))
            (gqsp_fastRevSwarSalt 8 rsalt d n_lanes rqrn))
          (gqsp_fastRevSwarSalt 8 rsalt d n_lanes rqrp))
        (Nat.mul rrep1 ta_B_COMB))
      (Nat.add 1 rdeg))
theorem gqsp_oneAnglePostRootRealFastBle_eq (d M N_rec W_err_d0 W_err_dpos pad : ℕ)
    (g0 : DyadicSu2Gate) (root : TreeNodeC) (ws_unpad : List ℕ) :
    gqsp_oneAnglePostRootRealFastBle d M N_rec W_err_d0 W_err_dpos pad g0 root ws_unpad =
    gqsp_oneAnglePostRootFastBleOf (gqsp_fastRevSwarSalt 8 root.salt)
    gqsp_sunpackShr256Chunked d M N_rec W_err_d0 W_err_dpos pad g0 root ws_unpad := by
  rcases root with ⟨rdeg, rsalt, rrep1, rprp, rprn, rpip, rpin, rqrp, rqrn, rqip, rqin, rerr⟩
  have hcheb (M1 B B2 Bw Rf nr pc pt) :
      gqsp_chebL1POnlyFast M1 B B2 Bw Rf W_err_d0 W_err_dpos pad nr pc pt ws_unpad =
        ta_chebL1POnlyFast M1 B B2 Bw Rf W_err_d0 W_err_dpos pad nr pc pt ws_unpad := by
    rcases ws_unpad with _ | ⟨w0, wt⟩
    · rfl
    · simp only [gqsp_chebL1POnlyFast, ta_chebL1POnlyFast, ta_tfNat_eq, ta_tfNatFn_eq,
        gqsp_chebL1StartGo, ta_chebL1StartGo, gqsp_chebL1PosBoolPar_eq]
  have hfin (s : ℕ) (c1 x1 x2 c3 x3 x4 : PolyPN) :
      gqsp_finishRootVec2RealFast gqsp_sunpackShr256Chunked s d (Nat.add 1 rdeg)
          (Nat.mul rrep1 ta_B_COMB) c1 x1 c3 x3 =
        finishRootVec4FastOf gqsp_sunpackShr256Chunked d (Nat.add 1 rdeg)
          (Nat.mul rrep1 ta_B_COMB) c1 x1 ⟨0, 0⟩ x2 c3 x3 ⟨0, 0⟩ x4 := by
    unfold gqsp_finishRootVec2RealFast
    rw [finishRootVec4FastOf_eq]
    simp only [finishRootVec4Of, sched_stfList_eq, forceNatFast_eq, mulAdd4Pos, mulAdd4Neg,
      mulAdd2Pos, mulAdd2Neg, Nat.mul_eq, Nat.add_eq, Nat.zero_mul, Nat.add_zero]
  unfold gqsp_oneAnglePostRootRealFastBle gqsp_oneAnglePostRootFastBleOf gqsp_buildOneAnglePqmFastOf
  dsimp only [TreeNodeC.deg, TreeNodeC.salt, TreeNodeC.rep1,
    TreeNodeC.pr, TreeNodeC.pi, TreeNodeC.qr, TreeNodeC.qi, TreeNodeC.err, revPolyPNOf]
  simp only [ta_tfBool_eq, gqsp_tfPqm1_eq, gqsp_forceListBool_eq, gqsp_srevNatTR_eq,
    gqsp_srevPQTR_eq, gqsp_ssplitPRevFast_eq, hcheb, gqsp_asymDefectPOnlyFast,
    ta_asymDefectPOnlyFast, ta_tfNat_eq, gqsp_asymDefectStartGo, ta_asymDefectStartGo,
    gqsp_asymDefectLoopPOnlyFast_eq, hfin 0x410001 _ _ ⟨rpip, rpin⟩ _ _ ⟨rqip, rqin⟩,
    hfin 0x420001 _ _ ⟨rqip, rqin⟩ _ _ ⟨rpip, rpin⟩]
theorem gqsp_zipAnd_rep (c : ℕ) : ∀ (n : ℕ) (xs : List ℕ), xs.length = n →
      List.zipWith (· &&& ·) xs (List.replicate n c) = xs.map (· &&& c)
  | 0, [], _ => rfl
  | n + 1, x :: xs, h => by
      simp only [List.replicate_succ, List.zipWith_cons_cons, List.map_cons]
      exact congrArg _ (gqsp_zipAnd_rep c n xs (Nat.succ.inj h))
theorem gqsp_forall2_lt768_rep {c : ℕ} (hc : c < sched_pow768) :
    ∀ (n : ℕ) (xs : List ℕ), xs.length = n → (∀ x ∈ xs, x < sched_pow768) →
      List.Forall₂ (fun x m ↦ x < sched_pow768 ∧ m < sched_pow768) xs (List.replicate n c)
  | 0, [], _, _ => List.Forall₂.nil
  | n + 1, x :: xs, hl, hx =>
      List.Forall₂.cons ⟨hx x List.mem_cons_self, hc⟩
        (gqsp_forall2_lt768_rep hc n xs (Nat.succ.inj hl) (fun a ha ↦
          hx a (List.mem_cons_of_mem x ha)))
theorem gqsp_map_and_getD (c : ℕ) :
    ∀ (xs : List ℕ) (m : ℕ), (xs.map (· &&& c)).getD m 0 = xs.getD m 0 &&& c
  | [], _ => by simp [List.getD_eq_getElem?_getD]
  | _ :: _, 0 => by simp [List.getD_eq_getElem?_getD]
  | _ :: xs, m + 1 => by
      rw [List.map_cons, sched_getD_cons_succ, sched_getD_cons_succ]
      exact gqsp_map_and_getD c xs m
/-- Strict WHNF-forcing `let`-binder via `Nat.casesOn (Nat.add x 1)`. -/
def gqsp_natCasesSucc {α : Type} (x : ℕ) (f : ℕ → α) (dflt : α) : α :=
  @Nat.casesOn (fun _ => α) (Nat.add x 1) dflt f
theorem gqsp_natCasesSucc_eq {α : Type} (x : ℕ) (f : ℕ → α) (dflt : α) : gqsp_natCasesSucc x
    f dflt = f x := rfl
/-- Binary-doubling constructor for `pack768 (List.replicate n 1)` in `O(log n)` shifts. -/
noncomputable def gqsp_rep1Fuel : ℕ → ℕ → ℕ :=
  @Nat.rec (fun _ => ℕ → ℕ)
    (fun _ => 0)
    (fun fuel ih n =>
      @Bool.casesOn (fun _ => ℕ) (Nat.beq n 0)
        (let h := Nat.div n 2
         sched_stfNat fuel
           (fun r =>
             let r2 := Nat.add r (Nat.shiftLeft r (Nat.mul 768 h))
             @Bool.casesOn (fun _ => ℕ) (Nat.beq (Nat.mod n 2) 0)
               (Nat.add 1 (Nat.shiftLeft r2 768))
               r2)
           (ih h))
        0)
/-- Intermediate `(laneCount, posWord, negWord)` segment for binary-tournament `PolyPN`
  unpacking. -/
inductive BiGqspUnpackSeg226 where
  | mk (len pos neg : ℕ) : BiGqspUnpackSeg226
theorem gqsp_mapRyChunksSlices_flatten : ∀ (slices : List (List (List DyadicRyGate))),
      (slices.map (fun s ↦ (gqsp_mapRyChunksToSu2 s).flatten)).flatten =
        slices.flatten.flatten.map ryToSu2Gate
  | [] => rfl
  | s :: ss => by
      rw [List.map_cons, List.flatten_cons, gqsp_mapRyChunksToSu2_flatten,
        gqsp_mapRyChunksSlices_flatten ss, List.flatten_cons, List.flatten_append, List.map_append]
end RealTournamentHelpers
end GqspWronskian62592
end
end Gqsp0c_RealTree
end QuantumComputation.Specs.StoppingPowerSolution
end
