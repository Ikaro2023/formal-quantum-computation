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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.BiGqspSwarRev

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section GqspWronskian62592

section
set_option compiler.extract_closed false
namespace GqspWronskian62592
section OneAngleTurnkeyCertStitch
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 2048
open Real Operator Matrix Circuit
open scoped Matrix Matrix.Norms.L2Operator BigOperators
open SpecsAux SpecsAux.SpecMirror
open PhaseGradSignalRot TFreeLaurentGQSP
open CatalyzedLaurentGQSP TFreeLaurentGQSPPresets
open TFreeLaurentGQSPPresets.FastRecurrenceVerifier
open TFreeLaurentGQSPPresets.FastIntervalRecurrenceVerifier
open BidirectionalCatalyzedGQSP
open BidirectionalCatalyzedGQSPBridge
open BidirectionalIntervalRecurrenceVerifier
open TwoAngleBiGqspVerifierBridge
open SpecsAux.Slim.BiGqspChunkedMillerLinearRecPQ2a
open SpecsAux.SpecMirror.BiGqspTrueAnglesFinalSumS4805
theorem gqsp_abs_sub_le_natDist (a b : ℕ) :
    |(a : ℝ) - (b : ℝ)| ≤ (natDist a b : ℝ) := by
  unfold natDist
  rcases le_total a b with h | h
  · rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h, abs_sub_comm,
        abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]
  · rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h,
        abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]
theorem gqsp_zipWith_fst_self {α β : Type*} (f : α → β) :
    ∀ xs : List α, List.zipWith (fun a _ ↦ f a) xs xs = xs.map f
  | [] => rfl
  | _ :: xs => congrArg (_ :: ·) (gqsp_zipWith_fst_self f xs)
/-- Embed a real 1-angle `DyadicRyGate` `(c, s)` into `DyadicSu2Gate` with `(a, b) = (c, s)` (`im
  = 0`). -/
def ryToSu2Gate (g : DyadicRyGate) : DyadicSu2Gate :=
  let gsm := gateSM g
  ⟨gsm.1.2, 0, gsm.2.2, 0, gsm.1.1, false, gsm.2.1, false⟩
theorem ryToSu2Gate_su2Pair (b : ℕ) (g : DyadicRyGate) :
    gateSu2Pair b (ryToSu2Gate g) = ((gateCos b g : ℂ), (gateSin b g : ℂ)) := by
  have hD : 2 ^ b = 2 ^ b := rfl
  unfold gateSu2Pair gateSu2ARe gateSu2AIm gateSu2BRe gateSu2BIm ryToSu2Gate
  rw [gateCos_eq_smToInt_div b (2 ^ b) hD g, gateSin_eq_smToInt_div b (2 ^ b) hD g]
  simp [smToInt]
theorem ryToSu2Gate_contraction_sq (g : DyadicRyGate) :
    ((ryToSu2Gate g).mar * (ryToSu2Gate g).mar + (ryToSu2Gate g).mai * (ryToSu2Gate g).mai) +
      ((ryToSu2Gate g).mbr * (ryToSu2Gate g).mbr + (ryToSu2Gate g).mbi * (ryToSu2Gate g).mbi) =
    (gateSM g).1.2 * (gateSM g).1.2 + (gateSM g).2.2 * (gateSM g).2.2 := by
  simp [ryToSu2Gate]
/-- `O(1)`-stack list map `gs.map ryToSu2Gate` via `@List.rec` + tail-recursive reverse. -/
noncomputable def gqsp_revSu2TR (xs0 acc0 : List DyadicSu2Gate) : List DyadicSu2Gate :=
    @List.rec DyadicSu2Gate (fun _ => List DyadicSu2Gate → List DyadicSu2Gate)
    (fun acc => acc) (fun x _ ih acc => gqsp_tramp (ih (x :: acc))) xs0 acc0
theorem gqsp_revSu2TR_eq :
    ∀ (xs acc : List DyadicSu2Gate), gqsp_revSu2TR xs acc = xs.reverse ++ acc
  | [], _ => rfl
  | x :: xs, acc => by
      change gqsp_tramp (gqsp_revSu2TR xs (x :: acc)) = (x :: xs).reverse ++ acc
      unfold gqsp_tramp
      rw [gqsp_revSu2TR_eq xs (x :: acc), List.reverse_cons, List.append_assoc,
          List.singleton_append]
noncomputable def gqsp_mapRyToSu2RevTR (gs0 : List DyadicRyGate) (acc0 : List DyadicSu2Gate)
    : List DyadicSu2Gate := @List.rec DyadicRyGate
    (fun _ => List DyadicSu2Gate → List DyadicSu2Gate) (fun acc => acc)
    (fun g _ ih acc => gqsp_tramp (ih (ryToSu2Gate g :: acc))) gs0 acc0
theorem gqsp_mapRyToSu2RevTR_eq :
    ∀ (gs : List DyadicRyGate) (acc : List DyadicSu2Gate),
      gqsp_mapRyToSu2RevTR gs acc = (gs.map ryToSu2Gate).reverse ++ acc
  | [], _ => rfl
  | g :: gs, acc => by
      change gqsp_tramp (gqsp_mapRyToSu2RevTR gs (ryToSu2Gate g :: acc)) =
        ((g :: gs).map ryToSu2Gate).reverse ++ acc
      unfold gqsp_tramp
      rw [gqsp_mapRyToSu2RevTR_eq gs (ryToSu2Gate g :: acc), List.map_cons, List.reverse_cons,
        List.append_assoc, List.singleton_append]
noncomputable def gqsp_mapRyToSu2Fast (gs : List DyadicRyGate) : List DyadicSu2Gate :=
  gqsp_revSu2TR (gqsp_mapRyToSu2RevTR gs []) []
theorem gqsp_mapRyToSu2Fast_eq (gs : List DyadicRyGate) :
    gqsp_mapRyToSu2Fast gs = gs.map ryToSu2Gate := by
  unfold gqsp_mapRyToSu2Fast
  rw [gqsp_revSu2TR_eq, gqsp_mapRyToSu2RevTR_eq, List.append_nil, List.append_nil,
      List.reverse_reverse]
/-- Exact step-by-step embedding of real `biGqspRunLoop` inside complex `biGqspTwoAngleRunLoop`. -/
theorem biGqspTwoAngleRunLoop_eq_of_real (M : ℕ) (cs : ℕ → ℝ × ℝ) (ab : ℕ → ℂ × ℂ)
    (hab : ∀ s, ab s = (((cs s).1 : ℂ), ((cs s).2 : ℂ))) :
    ∀ (t : ℕ) (i : Fin (2 * (M + 1) + 1)),
      (biGqspTwoAngleRunLoop M ab t).1 i = ((biGqspRunLoop M cs t).1 i : ℂ) ∧
      (biGqspTwoAngleRunLoop M ab t).2 i = ((biGqspRunLoop M cs t).2 i : ℂ)
  | 0, i => by
      unfold biGqspTwoAngleRunLoop biGqspRunLoop gqspSu2Step gqspRotStep
        biGqspTwoAnglePreInit biGqspPreInit
      rw [hab 0]
      dsimp only
      rw [Complex.star_def, Complex.conj_ofReal, Complex.conj_ofReal]
      by_cases h1 : i.val = M + 1 <;> by_cases h2 : i.val = M + 2 <;>
        simp [h1, h2]
  | t + 1, i => by
      have ih := biGqspTwoAngleRunLoop_eq_of_real M cs ab hab t
      unfold biGqspTwoAngleRunLoop biGqspRunLoop biGqspTwoAngleStep biGqspStep
        gqspSu2Step gqspRotStep
      rw [hab (t + 1)]
      dsimp only
      rw [Complex.star_def, Complex.conj_ofReal, Complex.conj_ofReal]
      have hsr : shiftRightC (M + 1) (biGqspTwoAngleRunLoop M ab t).1 i =
          ((shiftRight (M + 1) (biGqspRunLoop M cs t).1 i : ℝ) : ℂ) := by
        unfold shiftRightC shiftRight
        split_ifs with hz
        · simp
        · exact (ih ⟨i.val - 1, by omega⟩).1
      have hsl : shiftLeftC (M + 1) (biGqspTwoAngleRunLoop M ab t).2 i =
          ((shiftLeft (M + 1) (biGqspRunLoop M cs t).2 i : ℝ) : ℂ) := by
        unfold shiftLeftC shiftLeft
        split_ifs with hlt
        · exact (ih ⟨i.val + 1, by omega⟩).2
        · simp
      rw [hsr, hsl]
      push_cast
      exact ⟨rfl, rfl⟩
theorem getD_map_ryToSu2Gate (g0 : DyadicRyGate) (gs : List DyadicRyGate) (s : ℕ) :
    ((ryToSu2Gate g0 :: gs.map ryToSu2Gate).getD s defaultSu2Gate) =
      ryToSu2Gate ((g0 :: gs).getD s defaultGate) := by
  rw [← List.map_cons, List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases (g0 :: gs)[s]? with
  | none => rfl
  | some g => rfl
/-- Parity-decomposed real `biGqspRunLoop` entries at `t = M` from `cdMat` transfer polynomials. -/
theorem biGqspRunLoop_entries_of_ryGates (M : ℕ) (g0 : DyadicRyGate) (gs : List DyadicRyGate)
    (hlen : gs.length = M) (m : ℕ) (hm : m ≤ M) :
    let cs := fun s ↦ gatePair 48 ((g0 :: gs).getD s defaultGate)
    let su2_g0 := ryToSu2Gate g0
    let su2_gs := gs.map ryToSu2Gate
    let pq := gateListTransferPQ 48 su2_gs
    let ab0 := gateSu2Pair 48 su2_g0
    let P_loop := rootLoopP M ab0.1 ab0.2 pq.1 pq.2
    let Q_loop := rootLoopQ M ab0.1 ab0.2 pq.1 pq.2
    (biGqspRunLoop M cs M).1 ⟨1 + 2 * m, by omega⟩ = (P_loop m).re ∧
    (biGqspRunLoop M cs M).2 ⟨1 + 2 * m, by omega⟩ = (Q_loop m).re ∧
    (biGqspRunLoop M cs M).1 ⟨1 + (2 * m + 1), by omega⟩ = -(Q_loop (M - m)).re ∧
    (biGqspRunLoop M cs M).2 ⟨1 + (2 * m + 1), by omega⟩ = (P_loop (M - m)).re := by
  intro cs su2_g0 su2_gs pq ab0 P_loop Q_loop
  let ab := fun s ↦ gateSu2Pair 48 ((su2_g0 :: su2_gs).getD s defaultSu2Gate)
  have hab : ∀ s, ab s = (((cs s).1 : ℂ), ((cs s).2 : ℂ)) := by
    intro s
    dsimp only [ab, cs, su2_g0, su2_gs]
    rw [getD_map_ryToSu2Gate, ryToSu2Gate_su2Pair]
    rfl
  have hlen_su2 : su2_gs.length = M := by simp [su2_gs, hlen]
  have hmat := runLoopMatC_eq_cdMat_mul_init M 48 su2_g0 su2_gs hlen_su2
  rcases gateListTransferPQ_supp 48 su2_gs with ⟨hP0, hQ0⟩
  have hP : PolyCSupp M pq.1 := hlen_su2 ▸ hP0
  have hQ : PolyCSupp M pq.2 := hlen_su2 ▸ hQ0
  rcases cdMat_mul_init_entries ab0.1 ab0.2 hP hQ m with ⟨ha, hb, hc, hd⟩
  rw [← hmat] at ha hb hc hd
  have hcond : m ≤ M ∧ M ≤ M := ⟨hm, le_rfl⟩
  have hidx_e : (M + 1) - M + 2 * m = 1 + 2 * m := by omega
  have hidx_o : (M + 1) - M + 2 * m + 1 = 1 + (2 * m + 1) := by omega
  unfold runLoopMatC at ha hb hc hd
  simp only [PolyC.ofC_toC, hcond, and_self, ↓reduceDIte, ↓reduceIte] at ha hb hc hd
  have he1 := (biGqspTwoAngleRunLoop_eq_of_real M cs ab hab M ⟨1 + 2 * m, by omega⟩).1
  have he2 := (biGqspTwoAngleRunLoop_eq_of_real M cs ab hab M ⟨1 + 2 * m, by omega⟩).2
  have ho1 := (biGqspTwoAngleRunLoop_eq_of_real M cs ab hab M ⟨1 + (2 * m + 1), by omega⟩).1
  have ho2 := (biGqspTwoAngleRunLoop_eq_of_real M cs ab hab M ⟨1 + (2 * m + 1), by omega⟩).2
  have hfe1 : (⟨(M + 1) - M + 2 * m, by omega⟩ : Fin (2 * (M + 1) + 1)) = ⟨1 + 2 * m, by omega⟩ :=
      by
    ext; exact hidx_e
  have hfo1 : (⟨(M + 1) - M + 2 * m + 1, by omega⟩ : Fin (2 * (M + 1) + 1)) = ⟨1 + (2 * m + 1),
      by omega⟩ := by
    ext; exact hidx_o
  rw [hfe1] at ha hc
  rw [hfo1] at hb hd
  dsimp only [ab] at he1 he2 ho1 ho2
  rw [he1] at ha
  rw [he2] at hc
  rw [ho1] at hb
  rw [ho2] at hd
  have ha_re := congrArg Complex.re ha
  have hc_re := congrArg Complex.re hc
  have hb_re := congrArg Complex.re hb
  have hd_re := congrArg Complex.re hd
  simp only [Complex.ofReal_re, Complex.neg_re, Complex.star_def,
      Complex.conj_re] at ha_re hc_re hb_re hd_re
  exact ⟨ha_re, hc_re, hb_re, hd_re⟩
/-- Fused 1-angle `(a, c, b, d)` interleaver matching `biGqspRunLoop` (`ep = P`, `eq = Q`, `op =
  -revQ`, `oq = revP`). -/
def gqsp_interleave1AngleRaw (B2 BIAS : ℕ) : List ℕ → List ℕ → List ℕ → List ℕ → List PQPair
  | up :: upt, uq :: uqt, rup :: rupt, ruq :: ruqt =>
      let ep := Nat.add up BIAS
      let eq := Nat.add uq BIAS
      let op := Nat.sub B2 (Nat.add ruq BIAS)
      let oq := Nat.add rup BIAS
      mkPQConsLazy ep eq (mkPQConsLazy op oq (gqsp_interleave1AngleRaw B2 BIAS upt uqt rupt ruqt))
  | _, _, _, _ => []
theorem gqsp_interleave1AngleRaw_eq (B2 BIAS : ℕ) :
    ∀ (uP uQ ruP ruQ : List ℕ),
      uP.length = uQ.length → uQ.length = ruP.length → ruP.length = ruQ.length →
      gqsp_interleave1AngleRaw B2 BIAS uP uQ ruP ruQ =
        interleaveFourPQ
          (uP.map (fun x ↦ Nat.add x BIAS))
          (uQ.map (fun x ↦ Nat.add x BIAS))
          (ruQ.map (fun x ↦ Nat.sub B2 (Nat.add x BIAS)))
          (ruP.map (fun x ↦ Nat.add x BIAS))
  | [], [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, h1, _, _ => by simp at h1
  | _ :: _, [], _, _, h1, _, _ => by simp at h1
  | _ :: _, _ :: _, [], _, _, h2, _ => by simp at h2
  | _ :: _, _ :: _, _ :: _, [], _, _, h3 => by simp at h3
  | _ :: upt, _ :: uqt, _ :: rupt, _ :: ruqt, h1, h2, h3 => by
      simp only [gqsp_interleave1AngleRaw, interleaveFourPQ, List.map_cons]
      rw [gqsp_interleave1AngleRaw_eq B2 BIAS upt uqt rupt ruqt
        (Nat.succ.inj h1) (Nat.succ.inj h2) (Nat.succ.inj h3)]
/-- `O(1)`-stack reversed 1-angle interleaver via `ta_interleaveChanStepGo`. -/
def gqsp_interleave1AngleRevTR (B2 BIAS s0 : ℕ)
    (uP0 uQ0 ruP0 ruQ0 : List ℕ) (acc0 : List PQPair) : List PQPair :=
  @List.rec ℕ (fun _ ↦ ℕ → List ℕ → List ℕ → List ℕ → List PQPair → List PQPair)
    (fun _ _ _ _ a ↦ a)
    (fun up _ ih k luq lrup lruq a ↦
      @List.casesOn ℕ (fun _ ↦ List PQPair) luq a fun uq uqt ↦
      @List.casesOn ℕ (fun _ ↦ List PQPair) lrup a fun rup rupt ↦
      @List.casesOn ℕ (fun _ ↦ List PQPair) lruq a fun ruq ruqt ↦
        let ep := Nat.add up BIAS
        let eq := Nat.add uq BIAS
        let op := Nat.sub B2 (Nat.add ruq BIAS)
        let oq := Nat.add rup BIAS
        ta_stfPQ0 k
          (ta_stfPQ1 (Nat.add 1 k)
            (ta_stfPQ2 (Nat.add 3 k)
              (ta_stfPQ3 (Nat.add 2 k)
                (ta_tfPQ4 (ta_interleaveChanStepGo ih uqt rupt ruqt a k (Nat.add 2 k)) (Nat.add 4
                    k))
                op)
              oq)
            eq)
          ep)
    uP0 s0 uQ0 ruP0 ruQ0 acc0
theorem gqsp_interleave1AngleRevTR_cons (B2 BIAS s up : ℕ) (upt : List ℕ)
    (uq : ℕ) (uqt : List ℕ) (rup : ℕ) (rupt : List ℕ) (ruq : ℕ) (ruqt : List ℕ)
    (acc : List PQPair) :
    gqsp_interleave1AngleRevTR B2 BIAS s (up :: upt) (uq :: uqt) (rup :: rupt) (ruq :: ruqt) acc =
      let ep := Nat.add up BIAS
      let eq := Nat.add uq BIAS
      let op := Nat.sub B2 (Nat.add ruq BIAS)
      let oq := Nat.add rup BIAS
      gqsp_interleave1AngleRevTR B2 BIAS (Nat.add 4 s) upt uqt rupt ruqt
        (⟨op, oq⟩ :: ⟨ep, eq⟩ :: acc) := by
  dsimp only [gqsp_interleave1AngleRevTR]
  simp only [ta_stfPQ0_eq, ta_stfPQ1_eq, ta_stfPQ2_eq, ta_stfPQ3_eq, ta_tfPQ4_eq,
    ta_interleaveChanStepGo, ta_tramp, ta_idSalt]
theorem gqsp_interleave1AngleRevTR_eq (B2 BIAS : ℕ) :
    ∀ (uP : List ℕ) (s : ℕ) (uQ ruP ruQ : List ℕ) (acc : List PQPair),
      gqsp_interleave1AngleRevTR B2 BIAS s uP uQ ruP ruQ acc =
        (gqsp_interleave1AngleRaw B2 BIAS uP uQ ruP ruQ).reverse ++ acc
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, [], _, _, _ => rfl
  | _ :: _, _, _ :: _, [], _, _ => rfl
  | _ :: _, _, _ :: _, _ :: _, [], _ => rfl
  | up :: upt, s, uq :: uqt, rup :: rupt, ruq :: ruqt, acc => by
      rw [gqsp_interleave1AngleRevTR_cons]
      dsimp only [gqsp_interleave1AngleRaw]
      rw [mkPQConsLazy_eq, mkPQConsLazy_eq,
        gqsp_interleave1AngleRevTR_eq B2 BIAS upt (Nat.add 4 s) uqt rupt ruqt,
        List.reverse_cons, List.reverse_cons, List.append_assoc, List.append_assoc,
        List.singleton_append, List.singleton_append]
/-- Strict `ℕ → (List PQPair × ℕ)` evaluation barrier. -/
def gqsp_tfPqm1 (f : ℕ → List PQPair × ℕ) (x : ℕ) : List PQPair × ℕ :=
  @Nat.casesOn (fun _ ↦ List PQPair × ℕ) (Nat.add 1 x) ([], 0) f
theorem gqsp_tfPqm1_eq (f : ℕ → List PQPair × ℕ) (x : ℕ) : gqsp_tfPqm1 f x = f x := by
  change @Nat.casesOn (fun _ ↦ List PQPair × ℕ) (1 + x) ([], 0) f = f x
  rw [Nat.one_add]
/-- Core 1-angle post-root builder parameterized by evaluated `(n_lanes, rep_bcomb)`. -/
def gqsp_buildOneAnglePqmCore
    (revFn : ℕ → ℕ → ℕ → ℕ) (unpackShr256 : ℕ → ℕ → ℕ → List ℕ)
    (B2 BIAS d n_lanes rep_bcomb : ℕ) (g0 : DyadicSu2Gate) (root : TreeNodeC) : List PQPair × ℕ :=
  let c_ar := smToPolyPN g0.sar g0.mar
  let c_br := smToPolyPN g0.sbr g0.mbr
  let nc_br := negPolyPN c_br
  let zeroPN : PolyPN := ⟨0, 0⟩
  let rpr := revPolyPNOf revFn d n_lanes root.pr
  let rqr := revPolyPNOf revFn d n_lanes root.qr
  let uPre := finishRootVec4Of unpackShr256 d n_lanes rep_bcomb
    c_ar root.pr zeroPN root.pi nc_br rqr zeroPN root.qi
  let uQre := finishRootVec4Of unpackShr256 d n_lanes rep_bcomb
    c_ar root.qr zeroPN root.qi c_br rpr zeroPN root.pi
  let pqM := gqsp_interleave1AngleRaw B2 BIAS uPre uQre uPre.reverse uQre.reverse
  let r_l2 := Nat.add (Nat.shiftRight root.err 206) 2
  (pqM, r_l2)
/-- Specification 1-angle post-root builder (`2` calls to `finishRootVec4Of` instead of `4`). -/
def gqsp_buildOneAnglePqmOf (revFn : ℕ → ℕ → ℕ → ℕ) (unpackShr256 : ℕ → ℕ → ℕ → List ℕ)
    (d : ℕ) (g0 : DyadicSu2Gate) (root : TreeNodeC) : List PQPair × ℕ := forceNatFast
    (Nat.add root.deg 1) fun n_lanes ↦ forceNatFast (Nat.mul root.rep1 ta_B_COMB) fun
    rep_bcomb ↦ gqsp_buildOneAnglePqmCore revFn unpackShr256 ta_B2 ta_BIAS_OUT d n_lanes
    rep_bcomb g0 root
theorem gqsp_buildOneAnglePqmOf_eq_core (revFn : ℕ → ℕ → ℕ → ℕ)
    (unpackShr256 : ℕ → ℕ → ℕ → List ℕ) (B_COMB B2 BIAS d : ℕ) (g0 : DyadicSu2Gate)
    (root : TreeNodeC) : (forceNatFast (Nat.add root.deg 1) fun n_lanes ↦ forceNatFast
    (Nat.mul root.rep1 B_COMB) fun rep_bcomb ↦ gqsp_buildOneAnglePqmCore revFn unpackShr256
    B2 BIAS d n_lanes rep_bcomb g0 root) = gqsp_buildOneAnglePqmCore revFn unpackShr256 B2
    BIAS d (Nat.add root.deg 1) (Nat.mul root.rep1 B_COMB) g0 root := by
  rw [forceNatFast_eq, forceNatFast_eq]
/-- `O(1)`-stack fast 1-angle post-root builder. -/
def gqsp_buildOneAnglePqmFastOf (revFn : ℕ → ℕ → ℕ → ℕ) (unpackShr256 : ℕ → ℕ → ℕ → List ℕ)
    (d : ℕ) (g0 : DyadicSu2Gate) (root : TreeNodeC) : List PQPair × ℕ :=
  gqsp_tfPqm1 (fun n_lanes ↦
    gqsp_tfPqm1 (fun rep_bcomb ↦
      let c_ar := smToPolyPN g0.sar g0.mar
      let c_br := smToPolyPN g0.sbr g0.mbr
      let nc_br := negPolyPN c_br
      let zeroPN : PolyPN := ⟨0, 0⟩
      let rpr := revPolyPNOf revFn d n_lanes root.pr
      let rqr := revPolyPNOf revFn d n_lanes root.qr
      let uPre := finishRootVec4FastOf unpackShr256 d n_lanes rep_bcomb
        c_ar root.pr zeroPN root.pi nc_br rqr zeroPN root.qi
      let uQre := finishRootVec4FastOf unpackShr256 d n_lanes rep_bcomb
        c_ar root.qr zeroPN root.qi c_br rpr zeroPN root.pi
      let pqM := ta_revPQTR
        (gqsp_interleave1AngleRevTR ta_B2 ta_BIAS_OUT 1 uPre uQre (ta_revNatTR uPre [])
            (ta_revNatTR uQre []) []) []
      let r_l2 := Nat.add (Nat.shiftRight root.err 206) 2
      gqsp_tfPqm1 (fun r ↦ (pqM, r)) r_l2)
    (Nat.mul root.rep1 ta_B_COMB))
  (Nat.add 1 root.deg)
theorem gqsp_buildOneAnglePqmFastCore_eq
    (revFn : ℕ → ℕ → ℕ → ℕ) (unpackShr256 : ℕ → ℕ → ℕ → List ℕ)
    (B_COMB B2 BIAS d : ℕ) (g0 : DyadicSu2Gate) (root : TreeNodeC) :
    (gqsp_tfPqm1 (fun n_lanes ↦
      gqsp_tfPqm1 (fun rep_bcomb ↦
        let c_ar := smToPolyPN g0.sar g0.mar
        let c_br := smToPolyPN g0.sbr g0.mbr
        let nc_br := negPolyPN c_br
        let zeroPN : PolyPN := ⟨0, 0⟩
        let rpr := revPolyPNOf revFn d n_lanes root.pr
        let rqr := revPolyPNOf revFn d n_lanes root.qr
        let uPre := finishRootVec4FastOf unpackShr256 d n_lanes rep_bcomb
          c_ar root.pr zeroPN root.pi nc_br rqr zeroPN root.qi
        let uQre := finishRootVec4FastOf unpackShr256 d n_lanes rep_bcomb
          c_ar root.qr zeroPN root.qi c_br rpr zeroPN root.pi
        let pqM := ta_revPQTR
          (gqsp_interleave1AngleRevTR B2 BIAS 1 uPre uQre (ta_revNatTR uPre []) (ta_revNatTR uQre
              []) []) []
        let r_l2 := Nat.add (Nat.shiftRight root.err 206) 2
        gqsp_tfPqm1 (fun r ↦ (pqM, r)) r_l2)
      (Nat.mul root.rep1 B_COMB))
    (Nat.add 1 root.deg)) =
      gqsp_buildOneAnglePqmCore revFn unpackShr256 B2 BIAS d
        (Nat.add root.deg 1) (Nat.mul root.rep1 B_COMB) g0 root := by
  have hd1 : Nat.add 1 root.deg = Nat.add root.deg 1 := Nat.add_comm 1 root.deg
  rw [gqsp_tfPqm1_eq, gqsp_tfPqm1_eq, hd1, gqsp_tfPqm1_eq]
  unfold gqsp_buildOneAnglePqmCore
  simp only [finishRootVec4FastOf_eq]
  generalize finishRootVec4Of unpackShr256 d (Nat.add root.deg 1) (Nat.mul root.rep1 B_COMB)
    (smToPolyPN g0.sar g0.mar) root.pr ⟨0, 0⟩ root.pi
    (negPolyPN (smToPolyPN g0.sbr g0.mbr)) (revPolyPNOf revFn d (Nat.add root.deg 1) root.qr)
    ⟨0, 0⟩ root.qi = uPre
  generalize finishRootVec4Of unpackShr256 d (Nat.add root.deg 1) (Nat.mul root.rep1 B_COMB)
    (smToPolyPN g0.sar g0.mar) root.qr ⟨0, 0⟩ root.qi
    (smToPolyPN g0.sbr g0.mbr) (revPolyPNOf revFn d (Nat.add root.deg 1) root.pr)
    ⟨0, 0⟩ root.pi = uQre
  simp only [ta_revNatTR_eq, ta_revPQTR_eq, gqsp_interleave1AngleRevTR_eq,
    List.append_nil, List.reverse_reverse]
theorem gqsp_buildOneAnglePqmFastOf_eq (revFn : ℕ → ℕ → ℕ → ℕ)
    (unpackShr256 : ℕ → ℕ → ℕ → List ℕ) (d : ℕ) (g0 : DyadicSu2Gate) (root : TreeNodeC) :
    gqsp_buildOneAnglePqmFastOf revFn unpackShr256 d g0 root = gqsp_buildOneAnglePqmOf revFn
    unpackShr256 d g0 root := by
  unfold gqsp_buildOneAnglePqmFastOf gqsp_buildOneAnglePqmOf
  rw [gqsp_buildOneAnglePqmFastCore_eq, gqsp_buildOneAnglePqmOf_eq_core]
theorem gqsp_interleaveFour_spec (M r_val : ℕ)
    (P_re Q_re : ℕ → ℝ)
    (run1 run2 : Fin (2 * (M + 1) + 1) → ℝ)
    (hrun : ∀ m (hm : m ≤ M),
      run1 ⟨1 + 2 * m, by omega⟩ = P_re m ∧
      run2 ⟨1 + 2 * m, by omega⟩ = Q_re m ∧
      run1 ⟨1 + (2 * m + 1), by omega⟩ = -Q_re (M - m) ∧
      run2 ⟨1 + (2 * m + 1), by omega⟩ = P_re (M - m))
    (ep eq op oq : List ℕ)
    (hep_l : ep.length = M + 1) (heq_l : eq.length = M + 1)
    (hop_l : op.length = M + 1) (hoq_l : oq.length = M + 1)
    (hep : ∀ m < M + 1, |(ep.getD m 0 : ℤ) - (ta_B : ℤ)| ≤ (ta_B : ℤ) ∧
      |(ta_scale0 : ℝ) * P_re m - ((ep.getD m 0 : ℝ) - (ta_B : ℝ))| ≤ (r_val : ℝ))
    (heq : ∀ m < M + 1, |(eq.getD m 0 : ℤ) - (ta_B : ℤ)| ≤ (ta_B : ℤ) ∧
      |(ta_scale0 : ℝ) * Q_re m - ((eq.getD m 0 : ℝ) - (ta_B : ℝ))| ≤ (r_val : ℝ))
    (hop : ∀ m < M + 1, |(op.getD m 0 : ℤ) - (ta_B : ℤ)| ≤ (ta_B : ℤ) ∧
      |(ta_scale0 : ℝ) * (-Q_re (M - m)) - ((op.getD m 0 : ℝ) - (ta_B : ℝ))| ≤ (r_val : ℝ))
    (hoq : ∀ m < M + 1, |(oq.getD m 0 : ℤ) - (ta_B : ℤ)| ≤ (ta_B : ℤ) ∧
      |(ta_scale0 : ℝ) * P_re (M - m) - ((oq.getD m 0 : ℝ) - (ta_B : ℝ))| ≤ (r_val : ℝ)) :
    let pqM := interleaveFourPQ ep eq op oq
    pqM.length = 2 * (M + 1) ∧
    ∀ k (hk : k < 2 * (M + 1)),
      let pk := (pqM.getD k ⟨ta_B, ta_B⟩).p
      let qk := (pqM.getD k ⟨ta_B, ta_B⟩).q
      let idx : Fin (2 * (M + 1) + 1) := ⟨1 + k, by omega⟩
      |(pk : ℤ) - (ta_B : ℤ)| ≤ (ta_B : ℤ) ∧
      |(qk : ℤ) - (ta_B : ℤ)| ≤ (ta_B : ℤ) ∧
      |(ta_scale0 : ℝ) * run1 idx - ((pk : ℝ) - (ta_B : ℝ))| ≤ (r_val : ℝ) ∧
      |(ta_scale0 : ℝ) * run2 idx - ((qk : ℝ) - (ta_B : ℝ))| ≤ (r_val : ℝ) := by
  intro pqM
  refine ⟨interleaveFourPQ_length (M + 1) ep eq op oq hep_l heq_l hop_l hoq_l, fun k hk ↦ ?_⟩
  let m := k / 2
  have hm_lt : m < M + 1 := by omega
  have hm_le : m ≤ M := by omega
  rcases hrun m hm_le with ⟨hrun_e1, hrun_e2, hrun_o1, hrun_o2⟩
  rcases interleaveFourPQ_getD (M + 1) ep eq op oq m hep_l heq_l hop_l hoq_l hm_lt with ⟨hget_e,
      hget_o⟩
  by_cases hpar : k % 2 = 0
  · have hk_eq : k = 2 * m := by omega
    have hfin : (⟨1 + k, by omega⟩ : Fin (2 * (M + 1) + 1)) = ⟨1 + 2 * m, by omega⟩ := by
      ext; exact congrArg (1 + ·) hk_eq
    have hget_k : pqM.getD k ⟨ta_B, ta_B⟩ = ⟨ep.getD m 0, eq.getD m 0⟩ := by
      dsimp only [pqM]; rw [hk_eq]; exact hget_e
    dsimp only
    rw [hfin, hget_k, hrun_e1, hrun_e2]
    exact ⟨(hep m hm_lt).1, (heq m hm_lt).1, (hep m hm_lt).2, (heq m hm_lt).2⟩
  · have hk_eq : k = 2 * m + 1 := by omega
    have hfin : (⟨1 + k, by omega⟩ : Fin (2 * (M + 1) + 1)) = ⟨1 + (2 * m + 1), by omega⟩ := by
      ext; exact congrArg (1 + ·) hk_eq
    have hget_k : pqM.getD k ⟨ta_B, ta_B⟩ = ⟨op.getD m 0, oq.getD m 0⟩ := by
      dsimp only [pqM]; rw [hk_eq]; exact hget_o
    dsimp only
    rw [hfin, hget_k, hrun_o1, hrun_o2]
    exact ⟨(hop m hm_lt).1, (hoq m hm_lt).1, (hop m hm_lt).2, (hoq m hm_lt).2⟩
set_option maxHeartbeats 800000 in
-- Multi-component post-root builder soundness proof.
/-- Soundness of `gqsp_buildOneAnglePqmOf`: produces `(pqM, r_l2)` satisfying all hypotheses of
`biHadamardFinishPair_spec` for 1-angle `Ry` gates! -/
theorem gqsp_buildOneAnglePqmOf_spec
    (revFn : ℕ → ℕ → ℕ → ℕ) (unpackShr256 : ℕ → ℕ → ℕ → List ℕ)
    (d M : ℕ) (ry_g0 : DyadicRyGate) (ry_gs : List DyadicRyGate)
    (hlen_gs : ry_gs.length = M)
    (root : TreeNodeC)
    (hvalid : TreeNodeCValid (ry_gs.map ryToSu2Gate) root)
    (hrev : ∀ (xs : List ℕ), xs.length = M + 1 → (∀ x ∈ xs, x < 2 ^ 768) →
      revFn d (M + 1) (pack768 xs) = pack768 xs.reverse)
    (hunpack : ∀ (zs : List ℕ), zs.length = M + 1 → (∀ z ∈ zs, z < 2 ^ 768) →
      unpackShr256 d (M + 1) (pack768 zs) = zs.map (fun z ↦ Nat.shiftRight z 256))
    (hg0 : (gateSM ry_g0).1.2 * (gateSM ry_g0).1.2 + (gateSM ry_g0).2.2 * (gateSM ry_g0).2.2 ≤ 2 ^
        96) :
    let g0 := ryToSu2Gate ry_g0
    let cs := fun s ↦ gatePair 48 ((ry_g0 :: ry_gs).getD s defaultGate)
    let res := gqsp_buildOneAnglePqmOf revFn unpackShr256 d g0 root
    let pqM := res.1
    let r_l2 := res.2
    pqM.length = 2 * (M + 1) ∧
    ∀ k (hk : k < 2 * (M + 1)),
      let pk := (pqM.getD k ⟨ta_B, ta_B⟩).p
      let qk := (pqM.getD k ⟨ta_B, ta_B⟩).q
      let idx : Fin (2 * (M + 1) + 1) := ⟨1 + k, by omega⟩
      |(pk : ℤ) - (ta_B : ℤ)| ≤ (ta_B : ℤ) ∧
      |(qk : ℤ) - (ta_B : ℤ)| ≤ (ta_B : ℤ) ∧
      |(ta_scale0 : ℝ) * (biGqspRunLoop M cs M).1 idx - ((pk : ℝ) - (ta_B : ℝ))| ≤ (r_l2 : ℝ) ∧
      |(ta_scale0 : ℝ) * (biGqspRunLoop M cs M).2 idx - ((qk : ℝ) - (ta_B : ℝ))| ≤ (r_l2 : ℝ) := by
  intro g0 cs res pqM r_l2
  have hsu2_len : (ry_gs.map ryToSu2Gate).length = M := by rw [List.length_map, hlen_gs]
  rcases hvalid with ⟨hdeg0, _, _, hrep10, P_hat, Q_hat, hpr0, hpi0, hqr0, hqi0, ⟨hPre_err,
      hPim_err⟩, ⟨hQre_err, hQim_err⟩⟩
  let pr_hat := P_hat.re
  let pi_hat := P_hat.im
  let qr_hat := Q_hat.re
  let qi_hat := Q_hat.im
  have hdeg : root.deg = M := hdeg0.trans hsu2_len
  have hrep1 : root.rep1 = pack768 (List.replicate (M + 1) 1) := hdeg ▸ hrep10
  have hpr : PolyPNValid M root.pr pr_hat := hdeg ▸ hpr0
  have hpi : PolyPNValid M root.pi pi_hat := hdeg ▸ hpi0
  have hqr : PolyPNValid M root.qr qr_hat := hdeg ▸ hqr0
  have hqi : PolyPNValid M root.qi qi_hat := hdeg ▸ hqi0
  let pq_gs := gateListTransferPQ 48 (ry_gs.map ryToSu2Gate)
  have herr : ∀ m ≤ M,
      |pr_hat m - pq_gs.1.re m| ≤ (root.err : ℝ) / (2 ^ 352 : ℝ) ∧
      |pi_hat m - pq_gs.1.im m| ≤ (root.err : ℝ) / (2 ^ 352 : ℝ) ∧
      |qr_hat m - pq_gs.2.re m| ≤ (root.err : ℝ) / (2 ^ 352 : ℝ) ∧
      |qi_hat m - pq_gs.2.im m| ≤ (root.err : ℝ) / (2 ^ 352 : ℝ) :=
    fun m _ ↦ ⟨hPre_err m, hPim_err m, hQre_err m, hQim_err m⟩
  have hg0_su2 : (g0.mar * g0.mar + g0.mai * g0.mai) + (g0.mbr * g0.mbr +
      g0.mbi * g0.mbi) ≤ 2 ^ 96 := by
    dsimp only [g0]; rw [ryToSu2Gate_contraction_sq]; exact hg0
  rcases gateSu2_magnitudes_le_of_contraction g0 hg0_su2 with ⟨hmar, _, hmbr, _⟩
  let c_ar := smToPolyPN g0.sar g0.mar
  let c_br := smToPolyPN g0.sbr g0.mbr
  let nc_br := negPolyPN c_br
  let zeroPN : PolyPN := ⟨0, 0⟩
  have hcar : c_ar.pos + c_ar.neg ≤ 2 ^ 48 := by dsimp [c_ar]; rw [smToPolyPN_add_eq]; exact hmar
  have hcbr : c_br.pos + c_br.neg ≤ 2 ^ 48 := by dsimp [c_br]; rw [smToPolyPN_add_eq]; exact hmbr
  have hncbr : nc_br.pos + nc_br.neg ≤ 2 ^ 48 := by dsimp [nc_br]; rw [negPolyPN_add_eq]; exact hcbr
  have hzero : zeroPN.pos + zeroPN.neg ≤ 2 ^ 48 := Nat.zero_le _
  have hrpr := revPolyPNOf_valid revFn d M hrev root.pr pr_hat hpr
  have hrqr := revPolyPNOf_valid revFn d M hrev root.qr qr_hat hqr
  have hrpr_err : ∀ m ≤ M, |(if m ≤ M then pr_hat (M - m) else 0) - pq_gs.1.re (M - m)| ≤
      (root.err : ℝ) / (2 ^ 352 : ℝ) := fun m hm ↦ by rw [ta_ite_pos hm]; exact (herr (M - m) (by
          omega)).1
  have hrqr_err : ∀ m ≤ M, |(if m ≤ M then qr_hat (M - m) else 0) - pq_gs.2.re (M - m)| ≤
      (root.err : ℝ) / (2 ^ 352 : ℝ) := fun m hm ↦ by rw [ta_ite_pos hm]; exact (herr (M - m) (by
          omega)).2.2.1
  let rpr := revPolyPNOf revFn d (M + 1) root.pr
  let rqr := revPolyPNOf revFn d (M + 1) root.qr
  let rep_bcomb := Nat.mul root.rep1 ta_B_COMB
  let uPre := finishRootVec4Of unpackShr256 d (M + 1) rep_bcomb c_ar root.pr zeroPN root.pi nc_br
      rqr zeroPN root.qi
  let uQre := finishRootVec4Of unpackShr256 d (M + 1) rep_bcomb c_ar root.qr zeroPN root.qi c_br rpr
      zeroPN root.pi
  rcases finishRootVec4Of_spec unpackShr256 d M root.err root.rep1 hunpack hrep1
    c_ar zeroPN nc_br zeroPN root.pr root.pi rqr root.qi pr_hat pi_hat _ qi_hat
    pq_gs.1.re pq_gs.1.im (fun m ↦ pq_gs.2.re (M - m)) pq_gs.2.im
    hcar hzero hncbr hzero hpr hpi hrqr hqi
    (fun m hm ↦ (herr m hm).1) (fun m hm ↦ (herr m hm).2.1) hrqr_err (fun m hm ↦ (herr m hm).2.2.2)
    with ⟨huPre_l, huPre_b⟩
  rcases finishRootVec4Of_spec unpackShr256 d M root.err root.rep1 hunpack hrep1
    c_ar zeroPN c_br zeroPN root.qr root.qi rpr root.pi qr_hat qi_hat _ pi_hat
    pq_gs.2.re pq_gs.2.im (fun m ↦ pq_gs.1.re (M - m)) pq_gs.1.im
    hcar hzero hcbr hzero hqr hqi hrpr hpi
    (fun m hm ↦ (herr m hm).2.2.1) (fun m hm ↦ (herr m hm).2.2.2) hrpr_err (fun m hm ↦
        (herr m hm).2.1)
    with ⟨huQre_l, huQre_b⟩
  change uPre.length = M + 1 at huPre_l
  change uQre.length = M + 1 at huQre_l
  let ab0 := gateSu2Pair 48 g0
  let P_loop := rootLoopP M ab0.1 ab0.2 pq_gs.1 pq_gs.2
  let Q_loop := rootLoopQ M ab0.1 ab0.2 pq_gs.1 pq_gs.2
  let r_val := Nat.add (Nat.shiftRight root.err 206) 2
  have hab0_im : ab0.1.im = 0 ∧ ab0.2.im = 0 := by
    dsimp only [ab0, g0]
    rw [ryToSu2Gate_su2Pair]
    exact ⟨Complex.ofReal_im _, Complex.ofReal_im _⟩
  have hcar_r : ((c_ar.pos : ℝ) - (c_ar.neg : ℝ)) / (2 ^ 48 : ℝ) = ab0.1.re := by
    dsimp only [c_ar, ab0]; rw [smToPolyPN_sub_eq, (gateSu2Pair_re_im g0).1]; rfl
  have hcbr_r : ((c_br.pos : ℝ) - (c_br.neg : ℝ)) / (2 ^ 48 : ℝ) = ab0.2.re := by
    dsimp only [c_br, ab0]; rw [smToPolyPN_sub_eq, (gateSu2Pair_re_im g0).2.2.1]; rfl
  have hncbr_r : ((nc_br.pos : ℝ) - (nc_br.neg : ℝ)) / (2 ^ 48 : ℝ) = -ab0.2.re := by
    dsimp only [nc_br]; rw [negPolyPN_sub_eq, neg_div, hcbr_r]
  have hzero_r : ((zeroPN.pos : ℝ) - (zeroPN.neg : ℝ)) / (2 ^ 48 : ℝ) = 0 := by
    dsimp only [zeroPN]; rw [Nat.cast_zero, sub_self, zero_div]
  have hdeg_add : Nat.add root.deg 1 = M + 1 := congrArg (Nat.add · 1) hdeg
  have hres_core : res = gqsp_buildOneAnglePqmCore revFn unpackShr256 ta_B2 ta_BIAS_OUT d (M +
      1) rep_bcomb g0 root :=
    (gqsp_buildOneAnglePqmOf_eq_core revFn unpackShr256 ta_B_COMB ta_B2 ta_BIAS_OUT d g0
        root).trans
      (congrArg (fun nl ↦ gqsp_buildOneAnglePqmCore revFn unpackShr256 ta_B2 ta_BIAS_OUT d nl
          rep_bcomb g0 root) hdeg_add)
  have hpqM_eq : pqM = gqsp_interleave1AngleRaw ta_B2 ta_BIAS_OUT uPre uQre uPre.reverse
      uQre.reverse :=
    congrArg Prod.fst hres_core
  have hr_eq : r_l2 = r_val := congrArg Prod.snd hres_core
  dsimp only
  rw [hpqM_eq, hr_eq]
  clear hres_core hpqM_eq hr_eq pqM r_l2 res
  have hP_re : ∀ j ≤ M, (P_loop j).re = ab0.1.re * pq_gs.1.re j +
      (-ab0.2.re) * pq_gs.2.re (M - j) := by
    intro j hj
    rw [(rootLoopP_re_im_eq M ab0.1 ab0.2 pq_gs.1 pq_gs.2 j hj).1, hab0_im.1, hab0_im.2]
    ring
  have hQ_re : ∀ j ≤ M, (Q_loop j).re = ab0.1.re * pq_gs.2.re j + ab0.2.re * pq_gs.1.re (M - j) :=
      by
    intro j hj
    rw [(rootLoopQ_re_im_eq M ab0.1 ab0.2 pq_gs.1 pq_gs.2 j hj).1, hab0_im.1, hab0_im.2]
    ring
  have huPre_m : ∀ j < M + 1,
      let val := Nat.add (uPre.getD j 0) ta_BIAS_OUT
      |(val : ℤ) - (ta_B : ℤ)| ≤ (ta_B : ℤ) ∧
      |(ta_scale0 : ℝ) * (P_loop j).re - ((val : ℝ) - (ta_B : ℝ))| ≤ (r_val : ℝ) := by
    intro j hj
    rcases huPre_b j hj with ⟨hb1, hb2⟩
    dsimp only at hb2 ⊢
    rw [hcar_r, hzero_r, hncbr_r] at hb2
    have hlin : ab0.1.re * pq_gs.1.re j + 0 * pq_gs.1.im j +
        -ab0.2.re * pq_gs.2.re (M - j) + 0 * pq_gs.2.im j = (P_loop j).re := by
      rw [hP_re j (by omega)]; ring
    rw [hlin] at hb2
    exact ⟨hb1, hb2⟩
  have huQre_m : ∀ j < M + 1,
      let val := Nat.add (uQre.getD j 0) ta_BIAS_OUT
      |(val : ℤ) - (ta_B : ℤ)| ≤ (ta_B : ℤ) ∧
      |(ta_scale0 : ℝ) * (Q_loop j).re - ((val : ℝ) - (ta_B : ℝ))| ≤ (r_val : ℝ) := by
    intro j hj
    rcases huQre_b j hj with ⟨hb1, hb2⟩
    dsimp only at hb2 ⊢
    rw [hcar_r, hzero_r, hcbr_r] at hb2
    have hlin : ab0.1.re * pq_gs.2.re j + 0 * pq_gs.2.im j +
        ab0.2.re * pq_gs.1.re (M - j) + 0 * pq_gs.1.im j = (Q_loop j).re := by
      rw [hQ_re j (by omega)]; ring
    rw [hlin] at hb2
    exact ⟨hb1, hb2⟩
  clear huPre_b huQre_b
  generalize uPre = vPre at huPre_l huPre_m ⊢
  generalize uQre = vQre at huQre_l huQre_m ⊢
  clear uPre uQre rep_bcomb
  rw [gqsp_interleave1AngleRaw_eq ta_B2 ta_BIAS_OUT vPre vQre vPre.reverse vQre.reverse
    (huPre_l.trans huQre_l.symm)
    (by rw [List.length_reverse, huQre_l, huPre_l])
    (by rw [List.length_reverse, List.length_reverse, huPre_l, huQre_l])]
  exact gqsp_interleaveFour_spec M r_val (fun m ↦ (P_loop m).re) (fun m ↦ (Q_loop m).re)
    (biGqspRunLoop M cs M).1 (biGqspRunLoop M cs M).2
    (fun m hm ↦ biGqspRunLoop_entries_of_ryGates M ry_g0 ry_gs hlen_gs m hm)
    _ _ _ _
    (by rw [List.length_map, huPre_l])
    (by rw [List.length_map, huQre_l])
    (by rw [List.length_map, List.length_reverse, huQre_l])
    (by rw [List.length_map, List.length_reverse, huPre_l])
    (fun m hm ↦ by rw [map_getD_lt _ vPre m (huPre_l.symm ▸ hm)]; exact huPre_m m hm)
    (fun m hm ↦ by rw [map_getD_lt _ vQre m (huQre_l.symm ▸ hm)]; exact huQre_m m hm)
    (fun m hm ↦ by
      rw [map_getD_lt _ vQre.reverse m (by rw [List.length_reverse, huQre_l]; exact hm),
          list_reverse_getD_lt vQre M m huQre_l hm]
      have hsub : M - m < M + 1 := Nat.sub_lt_succ M m
      exact flipBiased_spec _ r_val _ (huQre_m (M - m) hsub).1 (huQre_m (M - m) hsub).2)
    (fun m hm ↦ by
      rw [map_getD_lt _ vPre.reverse m (by rw [List.length_reverse, huPre_l]; exact hm),
          list_reverse_getD_lt vPre M m huPre_l hm]
      exact huPre_m (M - m) (Nat.sub_lt_succ M m))
/-- `O(1)`-stack `.q`-residual sum directly over `pqM` (`0` intermediate `pq_final` list). -/
def gqsp_qResidStepGo (ih : ℕ → ℕ → ℕ) (qh acc' : ℕ) : ℕ := ta_tramp (ih qh acc')
def gqsp_qResidHadamardFast (B B2 R_final : ℕ) (pq0 : List PQPair) (q_prev0 acc0 : ℕ) : ℕ :=
  @List.rec PQPair (fun _ ↦ ℕ → ℕ → ℕ)
    (fun q_prev acc ↦
      let q_last := Nat.shiftRight (Nat.add B (Nat.sub B2 q_prev)) 1
      Nat.add acc (Nat.add (natAbsDiff q_last B) R_final))
    (fun h _ ih q_prev acc ↦
      @PQPair.casesOn (fun _ ↦ ℕ) h fun ph qh ↦
        let q_cur := Nat.shiftRight (Nat.add ph (Nat.sub B2 q_prev)) 1
        ta_tfNat (gqsp_qResidStepGo ih qh)
          (Nat.add acc (Nat.add (natAbsDiff q_cur B) R_final)))
    pq0 q_prev0 acc0
theorem gqsp_qResidHadamardFast_cons (B B2 R_final ph qh : ℕ) (t : List PQPair) (q_prev acc : ℕ) :
    gqsp_qResidHadamardFast B B2 R_final (⟨ph, qh⟩ :: t) q_prev acc =
      let q_cur := Nat.shiftRight (Nat.add ph (Nat.sub B2 q_prev)) 1
      gqsp_qResidHadamardFast B B2 R_final t qh
        (Nat.add acc (Nat.add (natAbsDiff q_cur B) R_final)) := by
  dsimp only [gqsp_qResidHadamardFast]
  simp only [ta_tfNat_eq, gqsp_qResidStepGo, ta_tramp]
theorem gqsp_qResidSumBiased_nil (B R_final acc : ℕ) :
    qResidSumBiased B R_final [] acc = acc := rfl
theorem gqsp_qResidSumBiased_cons (B R_final p q : ℕ) (rest : List PQPair) (acc : ℕ) :
    qResidSumBiased B R_final (⟨p, q⟩ :: rest) acc =
      qResidSumBiased B R_final rest (Nat.add acc (Nat.add (natAbsDiff q B) R_final)) := by
  conv_lhs => unfold qResidSumBiased
  rw [forceNatFast_eq]
theorem gqsp_qResidHadamardFast_eq (B B2 R_final : ℕ) :
    ∀ (pq : List PQPair) (q_prev acc : ℕ),
      gqsp_qResidHadamardFast B B2 R_final pq q_prev acc =
        qResidSumBiased B R_final (biHadamardFinishPair B B2 pq q_prev) acc
  | [], q_prev, acc => by
      have hshr : ∀ a : ℕ, Nat.shiftRight a 1 = Nat.div a 2 :=
        fun a ↦ Nat.shiftRight_eq_div_pow a 1
      dsimp only [gqsp_qResidHadamardFast, biHadamardFinishPair]
      rw [mkPQConsLazy_eq, gqsp_qResidSumBiased_cons, gqsp_qResidSumBiased_nil, hshr]
  | ⟨ph, qh⟩ :: t, q_prev, acc => by
      have hshr : ∀ a : ℕ, Nat.shiftRight a 1 = Nat.div a 2 :=
        fun a ↦ Nat.shiftRight_eq_div_pow a 1
      rw [gqsp_qResidHadamardFast_cons]
      dsimp only [biHadamardFinishPair]
      rw [mkPQConsLazy_eq, gqsp_qResidSumBiased_cons, hshr]
      exact gqsp_qResidHadamardFast_eq B B2 R_final t qh _
/-- Combined `O(1)`-stack 1-angle post-root `Bool` verifier (`chebL1 + asymDefect + qResid ≤
  N_rec * shift0`). -/
def gqsp_oneAnglePostRootFastBleOf (revFn : ℕ → ℕ → ℕ → ℕ)
    (unpackShr256 : ℕ → ℕ → ℕ → List ℕ) (d M N_rec W_err_d0 W_err_dpos pad : ℕ)
    (g0 : DyadicSu2Gate) (root : TreeNodeC) (ws_unpad : List ℕ) : Bool :=
  @Prod.casesOn _ _ (fun _ ↦ Bool) (gqsp_buildOneAnglePqmFastOf revFn unpackShr256 d g0 root)
    fun pqM r_l2 ↦
      ta_tfBool (fun R_final ↦
        ta_tfBool (fun M1 ↦
          ta_tfBool (fun B ↦
            ta_tfBool (fun B2 ↦
              ta_tfBool (fun Bw ↦
                ta_tfBool (fun shift0 ↦
                  let p_fin := ta_revNatTR (ta_hadamardRevPOnlyFast B pqM 1 B []) []
                  @Prod.casesOn _ _ (fun _ ↦ Bool) (ta_splitPRevFast B M1 p_fin [])
                    fun neg_re p2_re ↦
                    @Prod.casesOn _ _ (fun _ ↦ Bool) p2_re fun pc_re pos_re ↦
                      let t1 := ta_chebL1POnlyFast M1 B B2 Bw R_final W_err_d0 W_err_dpos pad
                        neg_re pc_re pos_re ws_unpad
                      let t2 := ta_asymDefectPOnlyFast M1 B B2 R_final neg_re pos_re
                      let t3 := gqsp_qResidHadamardFast B B2 R_final pqM B 0
                      Nat.ble (Nat.add (Nat.add t1 t2) t3) (Nat.mul N_rec shift0))
                  ta_shift0)
                ta_Bw)
              ta_B2)
            ta_B)
          (Nat.add M 1))
        (Nat.add r_l2 1)
set_option maxHeartbeats 800000 in
-- Combined Chebyshev L1, asymmetry, and residual soundness proof.
theorem gqsp_oneAnglePostRootFastBleOf_spec
    (revFn : ℕ → ℕ → ℕ → ℕ) (unpackShr256 : ℕ → ℕ → ℕ → List ℕ)
    (d M K β_nat N_rec W_err_d0 W_err_dpos pad : ℕ)
    (ry_g0 : DyadicRyGate) (ry_gs : List DyadicRyGate)
    (hlen_gs : ry_gs.length = M)
    (root : TreeNodeC) (ws_unpad : List ℕ)
    (hunpad_gt : M + 1 < ws_unpad.length)
    (hpad : ws_unpad.length + pad = K + 1)
    (hws_err : ∀ k < K + 1,
      let scale0 := 2 ^ 48 * powMulFast (2 ^ 48) 2 1
      let Bw := powMulFast (2 ^ 48) 1 1 * scale0
      |(scale0 : ℝ) * chebTaylorWeight (β_nat : ℝ) K k -
          (((ws_unpad ++ List.replicate pad ta_Bw).getD k Bw : ℝ) - (Bw : ℝ))| ≤
        (if k = 0 then (W_err_d0 : ℝ) else (W_err_dpos : ℝ)))
    (hvalid : TreeNodeCValid (ry_gs.map ryToSu2Gate) root)
    (hrev : ∀ (xs : List ℕ), xs.length = M + 1 → (∀ x ∈ xs, x < 2 ^ 768) →
      revFn d (M + 1) (pack768 xs) = pack768 xs.reverse)
    (hunpack : ∀ (zs : List ℕ), zs.length = M + 1 → (∀ z ∈ zs, z < 2 ^ 768) →
      unpackShr256 d (M + 1) (pack768 zs) = zs.map (fun z ↦ Nat.shiftRight z 256))
    (hg0 : (gateSM ry_g0).1.2 * (gateSM ry_g0).1.2 + (gateSM ry_g0).2.2 * (gateSM ry_g0).2.2 ≤ 2 ^
        96)
    (h_post : gqsp_oneAnglePostRootFastBleOf revFn unpackShr256 d M N_rec W_err_d0 W_err_dpos
      pad (ryToSu2Gate ry_g0) root ws_unpad = true) :
    let cs := fun s ↦ gatePair 48 ((ry_g0 :: ry_gs).getD s defaultGate)
    let res := biGqspRecurrence M cs
    (∑ k ∈ Finset.range (K + 1), |laurentChebWeight (M +
        1) res.1 k - chebTaylorWeight (β_nat : ℝ) K k|) +
      (∑ j : Fin (M + 1), laurentAsymDefect (M + 1) res.1 j) +
      (∑ i : Fin (2 * (M + 1) + 1), |res.2 i|) ≤ (N_rec : ℝ) / 2 ^ 48 := by
  intro cs res
  have hpqm_spec := gqsp_buildOneAnglePqmOf_spec revFn unpackShr256 d M ry_g0 ry_gs hlen_gs root
    hvalid hrev hunpack hg0
  dsimp only at hpqm_spec
  have hpost' := h_post
  unfold gqsp_oneAnglePostRootFastBleOf at hpost'
  rw [gqsp_buildOneAnglePqmFastOf_eq] at hpost'
  rcases hbuild : gqsp_buildOneAnglePqmOf revFn unpackShr256 d (ryToSu2Gate ry_g0) root with ⟨pqM,
      r_l2⟩
  rw [hbuild] at hpqm_spec hpost'
  dsimp only at hpqm_spec hpost'
  rcases hpqm_spec with ⟨hpqM_len, hpqM_b⟩
  rcases biHadamardFinishPair_spec M ta_B ta_B2 r_l2 (ta_scale0 : ℝ) ta_B2_eq cs pqM hpqM_len hpqM_b
    with ⟨hfin_len, hfin_b⟩
  let pq_final := biHadamardFinishPair ta_B ta_B2 pqM ta_B
  let R_final := r_l2 + 1
  let ws := ws_unpad ++ List.replicate pad ta_Bw
  have hws_len : ws.length = K + 1 := by dsimp [ws]; rw [List.length_append, List.length_replicate,
      hpad]
  simp only [ta_tfBool_eq, Nat.add_eq, Nat.mul_eq] at hpost'
  rw [ta_hadamardFinishPOnlyFast_eq_map ta_B ta_B2 pqM ta_B,
      ta_splitPRevFast_eq_map ta_B (M + 1) pq_final [],
      gqsp_qResidHadamardFast_eq ta_B ta_B2 R_final pqM ta_B 0] at hpost'
  dsimp only at hpost'
  rcases hsp : splitPQRevStrict_true ta_B (M + 1) pq_final [] with ⟨neg_re, pc_re, pos_re⟩
  rw [hsp] at hpost'
  dsimp only at hpost'
  rw [ta_chebL1POnlyFast_eq_map (M + 1) ta_B ta_B2 ta_Bw R_final W_err_d0 W_err_dpos
        pad neg_re pc_re pos_re ws_unpad hunpad_gt,
      ta_asymDefectPOnlyFast_eq_map (M + 1) ta_B ta_B2 R_final neg_re pos_re] at hpost'
  have hc := chebL1SumLinear_eq_chebL1SumBiased (M + 1) ta_B ta_B2 ta_Bw R_final W_err_d0 W_err_dpos
    pq_final ws
  have ha := asymDefectSumLinear_eq_asymDefectSumBiased (M + 1) ta_B ta_B2 R_final pq_final
  rw [← splitPQRevStrict_true_eq, hsp] at hc ha
  dsimp only [ws] at hc ha hpost'
  rw [chebL1SumStrict_true_eq, asymDefectSumStrict_true_eq, hc, ha] at hpost'
  have h_tot_nat := Nat.ble_eq.mp hpost'
  have h_tot_real : (chebL1SumBiased (M + 1) ta_B ta_B2 ta_Bw R_final W_err_d0 W_err_dpos
      pq_final 0 ws 0 : ℝ) + (asymDefectSumBiased (M + 1) ta_B ta_B2 R_final pq_final (M + 1)
      0 : ℝ) + (qResidSumBiased ta_B R_final pq_final 0 : ℝ) ≤ (N_rec : ℝ) * (ta_shift0 : ℝ)
      := by
    dsimp only [ws]; exact_mod_cast h_tot_nat
  have hpq_p :
      ∀ k (hk : k < 2 * (M + 1) + 1),
        let pk := (pq_final.getD k ⟨ta_B, ta_B⟩).p
        |(pk : ℤ) - (ta_B : ℤ)| ≤ (ta_B : ℤ) ∧
        |(ta_scale0 : ℝ) * res.1 ⟨k, hk⟩ - ((pk : ℝ) - (ta_B : ℝ))| ≤ (R_final : ℝ) :=
    fun k hk ↦ ⟨(hfin_b k hk).1, (hfin_b k hk).2.2.1⟩
  have hscale0_eq : 2 ^ 48 * powMulFast (2 ^ 48) 2 1 = ta_scale0 := rfl
  have hBw_eq : powMulFast (2 ^ 48) 1 1 * ta_scale0 = ta_Bw := rfl
  have ht1 := ta_chebL1SumBiased_spec_target (M + 1) ta_scale0 ta_B ta_B2 ta_Bw R_final
    W_err_d0 W_err_dpos (fun k ↦ chebTaylorWeight (β_nat : ℝ) K k) ta_B2_eq
    pq_final res.1 hpq_p ws 0 0
    (fun j hj ↦ by
      rw [Nat.zero_add]
      have hw := hws_err j (hws_len ▸ hj)
      dsimp only at hw
      rwa [hscale0_eq, hBw_eq] at hw)
  rw [Nat.cast_zero, zero_add, hws_len] at ht1
  have ht1' : (ta_scale0 : ℝ) * (∑ k ∈ Finset.range (K + 1),
      |laurentChebWeight (M + 1) res.1 k - chebTaylorWeight (β_nat : ℝ) K k|) ≤
      (chebL1SumBiased (M + 1) ta_B ta_B2 ta_Bw R_final W_err_d0 W_err_dpos pq_final 0 ws 0 : ℝ) :=
          by
    rw [Finset.mul_sum]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun j _ ↦ ?_)) ht1
    rw [Nat.zero_add]
  have ht2 := asymDefectSumBiased_spec (M + 1) ta_scale0 ta_B ta_B2 R_final ta_B2_eq
    pq_final res.1 hpq_p (M + 1) le_rfl 0
  rw [Nat.cast_zero, zero_add] at ht2
  have ht2' : (ta_scale0 : ℝ) * (∑ j : Fin (M + 1), laurentAsymDefect (M + 1) res.1 j) ≤
      (asymDefectSumBiased (M + 1) ta_B ta_B2 R_final pq_final (M + 1) 0 : ℝ) := by
    rw [Finset.mul_sum]
    have h_eq : (∑ j : Fin (M + 1), (ta_scale0 : ℝ) * laurentAsymDefect (M + 1) res.1 j) =
        (∑ j ∈ Finset.range (M + 1),
          (ta_scale0 : ℝ) * (if hj : j < M + 1 then laurentAsymDefect (M + 1) res.1 ⟨j,
              hj⟩ else 0)) := by
      rw [← Fin.sum_univ_eq_sum_range]
      exact Finset.sum_congr rfl fun j _ ↦ by simp only [j.isLt, ↓reduceDIte]
    rw [h_eq]; exact ht2
  let q_fn : ℕ → ℝ := fun k ↦ if hk : k < 2 * (M + 1) + 1 then res.2 ⟨k, hk⟩ else 0
  have ht3 := qResidSumBiased_spec ta_scale0 ta_B R_final pq_final q_fn 0
    (fun k hk ↦ by
      have hk' : k < 2 * (M + 1) + 1 := hfin_len ▸ hk
      dsimp only [q_fn]; rw [dite_eq_left hk']
      exact (hfin_b k hk').2.2.2)
  rw [Nat.cast_zero, zero_add, hfin_len] at ht3
  have ht3' : (ta_scale0 : ℝ) * (∑ i : Fin (2 * (M + 1) + 1), |res.2 i|) ≤
      (qResidSumBiased ta_B R_final pq_final 0 : ℝ) := by
    rw [Finset.mul_sum]
    have h_eq : (∑ i : Fin (2 * (M + 1) + 1), (ta_scale0 : ℝ) * |res.2 i|) =
        (∑ k ∈ Finset.range (2 * (M + 1) + 1), (ta_scale0 : ℝ) * |q_fn k|) := by
      rw [← Fin.sum_univ_eq_sum_range]
      exact Finset.sum_congr rfl fun i _ ↦ by dsimp only [q_fn]; rw [dite_eq_left i.isLt]
    rw [h_eq]; exact ht3
  let E_tot : ℝ :=
    (∑ k ∈ Finset.range (K + 1), |laurentChebWeight (M +
        1) res.1 k - chebTaylorWeight (β_nat : ℝ) K k|) +
      (∑ j : Fin (M + 1), laurentAsymDefect (M + 1) res.1 j) +
      (∑ i : Fin (2 * (M + 1) + 1), |res.2 i|)
  have h_scale_E : (ta_scale0 : ℝ) * E_tot ≤ (N_rec : ℝ) * (ta_shift0 : ℝ) := by
    have hexp : (ta_scale0 : ℝ) * E_tot =
        (ta_scale0 : ℝ) * (∑ k ∈ Finset.range (K + 1), |laurentChebWeight (M +
            1) res.1 k - chebTaylorWeight (β_nat : ℝ) K k|) +
          (ta_scale0 : ℝ) * (∑ j : Fin (M + 1), laurentAsymDefect (M + 1) res.1 j) +
          (ta_scale0 : ℝ) * (∑ i : Fin (2 * (M + 1) + 1), |res.2 i|) := by
      dsimp [E_tot]; ring
    rw [hexp]
    linarith only [ht1', ht2', ht3', h_tot_real]
  have h2_48_pos : (0 : ℝ) < (2 : ℝ) ^ 48 := pow_pos (by norm_num : (0 : ℝ) < 2) 48
  have hshift_pos : (0 : ℝ) < (ta_shift0 : ℝ) := by exact_mod_cast ta_shift0_pos
  have hscale_cast : (ta_scale0 : ℝ) = (2 : ℝ) ^ 48 * (ta_shift0 : ℝ) := by
    rw [ta_scale0_eq_D_mul_shift0]; simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [hscale_cast] at h_scale_E
  change E_tot ≤ (N_rec : ℝ) / 2 ^ 48
  rw [le_div_iff₀ h2_48_pos]
  have h_mul : E_tot * (2 : ℝ) ^ 48 * (ta_shift0 : ℝ) ≤ (N_rec : ℝ) * (ta_shift0 : ℝ) := by
    linarith only [h_scale_E]
  exact le_of_mul_le_mul_right h_mul hshift_pos
theorem gqsp_biCode_list_natDist_sum_le
    (M : ℕ) (cr co : List ℕ)
    (hlen_r : cr.length = M + 1) (hlen_o : co.length = M + 1)
    (hlt_r : cr.all (· < 4398046511104) = true)
    (hlt_o : co.all (· < 4398046511104) = true) :
    let C_r : Fin (M + 1) → Fin (2 ^ 42) := fun i ↦ Fin.ofNat (2 ^ 42) (cr.getD i.val 0)
    let C_o : Fin (M + 1) → Fin (2 ^ 42) := fun i ↦ Fin.ofNat (2 ^ 42) (co.getD i.val 0)
    (∑ j ∈ Finset.range (M + 1), natDist (biCode M C_r j).val (biCode M C_o j).val) =
      (List.zipWith natDist cr co).sum := by
  intro C_r C_o
  have hget_lt : ∀ (xs : List ℕ) (j : ℕ), xs.length = M + 1 → xs.all (· < 4398046511104) = true →
      j < M + 1 → xs.getD j 0 < 2 ^ 42 := by
    intro xs j hxl hxall hj
    have hj' : j < xs.length := hxl ▸ hj
    have hmem : xs.getD j 0 ∈ xs := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]
      exact List.getElem_mem hj'
    have hlt := List.all_eq_true.mp hxall _ hmem
    simpa [show (4398046511104 : ℕ) = 2 ^ 42 from rfl] using hlt
  have hterm : ∀ j ∈ Finset.range (M + 1),
      natDist (biCode M C_r j).val (biCode M C_o j).val = (List.zipWith natDist cr co).getD j 0 :=
          by
    intro j hj
    have hj_lt : j < M + 1 := Finset.mem_range.mp hj
    have hb_r : (biCode M C_r j).val = cr.getD j 0 := by
      simp only [biCode, hj_lt, ↓reduceDIte, C_r]
      exact Nat.mod_eq_of_lt (hget_lt cr j hlen_r hlt_r hj_lt)
    have hb_o : (biCode M C_o j).val = co.getD j 0 := by
      simp only [biCode, hj_lt, ↓reduceDIte, C_o]
      exact Nat.mod_eq_of_lt (hget_lt co j hlen_o hlt_o hj_lt)
    rw [hb_r, hb_o, zipWith_getD_lt natDist cr co j (hlen_r.trans hlen_o.symm) (hlen_r.symm ▸
        hj_lt)]
  rw [Finset.sum_congr rfl hterm]
  have hzw_len : M + 1 = (List.zipWith natDist cr co).length := by
    simp [List.length_zipWith, hlen_r, hlen_o]
  rw [hzw_len]
  generalize List.zipWith natDist cr co = zs
  clear hterm hget_lt C_r C_o hlen_r hlen_o hlt_r hlt_o hzw_len
  induction zs with
  | nil => simp
  | cons z zt ih =>
      rw [List.length_cons, Finset.sum_range_succ', List.sum_cons]
      have h0 : (z :: zt).getD 0 0 = z := rfl
      have hs : (∑ k ∈ Finset.range zt.length, (z :: zt).getD (k + 1) 0) =
          ∑ k ∈ Finset.range zt.length, zt.getD k 0 :=
        Finset.sum_congr rfl fun k _ ↦ sched_getD_cons_succ z zt k 0
      rw [h0, hs, ih, Nat.add_comm]
end OneAngleTurnkeyCertStitch
end GqspWronskian62592
end
end GqspWronskian62592

end QuantumComputation.Specs.StoppingPowerSolution
end
