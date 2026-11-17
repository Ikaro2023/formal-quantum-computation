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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.WronskianMin135598
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.WronskianFact135598


@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section GqspWronskian135598
set_option maxRecDepth 4000000

section
set_option compiler.extract_closed false
namespace GqspWronskian135598
export GqspWronskianUV135598 (gqsp_b135598_k409600_cheb_scale0 gqsp_b135598_k409600_cheb_Bw
  gqsp_b135598_k409600_u_beta_off gqsp_b135598_k409600_W_err_d0 gqsp_b135598_k409600_W_err_dpos
  gqsp_u_c0 gqsp_u_c1 gqsp_u_c2 gqsp_b135598_k409600_u_biased gqsp_v_c0 gqsp_v_c1 gqsp_v_c2
  gqsp_b135598_k409600_v_biased)
section WronskianChebCert_b135598_k409600
set_option exponentiation.threshold 256
open Real
open scoped BigOperators
open TFreeLaurentGQSP
open TFreeLaurentGQSPPresets.FastRecurrenceVerifier
open TFreeLaurentGQSPPresets.FastIntervalRecurrenceVerifier
open SpecsAux.SpecMirror.BiGqspChunkedMillerCore
open SpecsAux.SpecMirror.BiGqspChebWeightCertS4805
open SpecsAux.SpecMirror.BiGqspChunkedMillerCert
open TwoAngleBiGqspVerifierBridge (ta_Bw ta_revNatTR_eq)
open GqspWronskian62592 (evenTailPosNegLoop evenTailPosNegLoop_spec StrictListBind_eq
  buildChebWsFromBiasedU_length gqsp_zwForce_eq gqsp_zwRevNatTR gqsp_zwRevNatTR_eq
  gqsp_zwDoubleBiasedRevTR gqsp_zwLenEq_spec gqsp_zwGetD_eq gqsp_zwDrop_eq gqsp_zwMaxMagLoop_eq
  gqsp_zwMillerResLoop_eq gqsp_zwWronskianMinBle_eq gqsp_zwEvenTailPosNeg_eq gqsp_zwDoubleGeBle_eq
  gqsp_buildChebWsUnpadLowMem gqsp_buildChebWsUnpadLowMem_append_eq)
open GqspWronskianUV135598
open GqspWronskianChecks135598
open GqspWronskianFact135598
private lemma wsGetD_drop (dflt n : ℕ) (xs : List ℕ) (k : ℕ) :
    (xs.drop n).getD k dflt = xs.getD (n + k) dflt := by
  simp [List.getD_eq_getElem?_getD]
private lemma wsDrop_last1 {xs : List ℕ} {n b dflt : ℕ}
    (hlen : xs.length = n + 1) (hb : xs.getD n dflt = b) : xs.drop n = [b] := by
  have hl : (xs.drop n).length = 1 := by rw [List.length_drop, hlen]; omega
  rcases hd : xs.drop n with _ | ⟨x0, _ | _⟩ <;> simp [hd] at hl
  simpa [hd, List.getD_eq_getElem?_getD] using (wsGetD_drop dflt n xs 0).trans hb
private lemma wsDrop_last2 {xs : List ℕ} {n a b dflt : ℕ} (hlen : xs.length = n + 2)
    (ha : xs.getD n dflt = a) (hb : xs.getD (n + 1) dflt = b) : xs.drop n = [a, b] := by
  have hl : (xs.drop n).length = 2 := by rw [List.length_drop, hlen]; omega
  rcases hd : xs.drop n with _ | ⟨x0, _ | ⟨x1, _ | _⟩⟩ <;> simp [hd] at hl
  have h0 : x0 = a := by
    simpa [hd, List.getD_eq_getElem?_getD] using (wsGetD_drop dflt n xs 0).trans ha
  have h1 : x1 = b := by
    simpa [hd, List.getD_eq_getElem?_getD] using (wsGetD_drop dflt n xs 1).trans hb
  rw [h0, h1]
private lemma wsGetD_append_left {xs ys : List ℕ} {k dflt : ℕ} (hk : k < xs.length) :
    (xs ++ ys).getD k dflt = xs.getD k dflt := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
private lemma wsGetD_append_right {xs ys : List ℕ} {n k dflt : ℕ} (hn : xs.length = n) :
    (xs ++ ys).getD (n + k) dflt = ys.getD k dflt := by
  subst hn; simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _)]
private lemma wsDrop_append_le :
    ∀ {n : ℕ} {xs ys : List ℕ}, n ≤ xs.length → (xs ++ ys).drop n = xs.drop n ++ ys
  | 0, _, _, _ => rfl
  | _ + 1, [], _, h => by simp at h
  | n + 1, _ :: xt, ys, h => @wsDrop_append_le n xt ys (by simpa using h)
private lemma wsMaxMag_append (Bw : ℕ) :
    ∀ (xs ys : List ℕ) (acc : ℕ),
      wsMaxMagLoop Bw (xs ++ ys) acc = wsMaxMagLoop Bw ys (wsMaxMagLoop Bw xs acc)
  | [], _, _ => rfl
  | w :: wt, ys, acc => by
      simp only [List.cons_append, wsMaxMagLoop, forceNatFast_eq]
      exact wsMaxMag_append Bw wt ys _
private lemma wsMaxMag_max (Bw : ℕ) :
    ∀ (xs : List ℕ) (a b : ℕ), wsMaxMagLoop Bw xs (Nat.max a b) = Nat.max a (wsMaxMagLoop Bw xs b)
  | [], _, _ => rfl
  | w :: wt, a, b => by
      simp only [wsMaxMagLoop, forceNatFast_eq, Nat.max_assoc]
      exact wsMaxMag_max Bw wt a _
private lemma doubleGe_append (Bw : ℕ) :
    ∀ (xs ys : List ℕ),
      doubleBiasedAllGeBle Bw (xs ++ ys) = (doubleBiasedAllGeBle Bw xs &&
      doubleBiasedAllGeBle Bw ys)
  | [], _ => rfl
  | u :: ut, ys => by
      simp only [List.cons_append, doubleBiasedAllGeBle]
      cases Nat.ble Bw (2 * u)
      · rfl
      · exact doubleGe_append Bw ut ys
private lemma millerRes_add (β Bw dflt : ℕ) :
    ∀ (k d : ℕ) (js : List ℕ) (a b : ℕ),
      millerResCountLoop β Bw dflt k d js (a + b) = a + millerResCountLoop β Bw dflt k d js b
  | 0, _, _, _, _ => rfl
  | _ + 1, _, [], _, _ => rfl
  | k + 1, d, j0 :: rest, a, b => by
      simp only [millerResCountLoop, forceNatFast_eq, Nat.add_eq, Nat.add_assoc]
      exact millerRes_add β Bw dflt k (d + 1) rest a _
private lemma millerRes_append (β Bw dflt : ℕ) :
    ∀ (m1 m2 d : ℕ) (xs ys : List ℕ) (acc : ℕ), m1 + 2 ≤ xs.length →
      millerResCountLoop β Bw dflt (m1 + m2) d (xs ++ ys) acc =
        millerResCountLoop β Bw dflt m2 (d + m1) (xs.drop m1 ++ ys)
          (millerResCountLoop β Bw dflt m1 d xs acc)
  | 0, _, _, _, _, _, _ => by simp [millerResCountLoop]
  | _ + 1, _, _, [], _, _, hlen => by simp at hlen
  | _ + 1, _, _, [_], _, _, hlen => by simp at hlen
  | _ + 1, _, _, [_, _], _, _, hlen => by simp at hlen
  | k + 1, m2, d, _ :: j1 :: j2 :: xt, ys, acc, hlen => by
      rw [show k + 1 + m2 = (k + m2) + 1 by omega, List.cons_append, List.drop_succ_cons]
      simp only [millerResCountLoop, forceNatFast_eq, Nat.add_eq]
      rw [show d + (k + 1) = d + 1 + k by omega]
      exact millerRes_append β Bw dflt k m2 (d + 1) (j1 :: j2 :: xt) ys _
        (by simp at hlen ⊢; omega)
private lemma wronskianMin_append (Bw W_min : ℕ) :
    ∀ (m1 m2 : ℕ) (xs ys vs ws : List ℕ), m1 + 1 ≤ xs.length → m1 + 1 ≤ vs.length →
      wronskianMinCheckBle Bw W_min (xs ++ ys) (vs ++ ws) (m1 + m2) =
        (wronskianMinCheckBle Bw W_min xs vs m1 &&
         wronskianMinCheckBle Bw W_min (xs.drop m1 ++ ys) (vs.drop m1 ++ ws) m2)
  | 0, _, _, _, _, _, _, _ => by simp [wronskianMinCheckBle]
  | _ + 1, _, [], _, _, _, hux, _ => by simp at hux
  | _ + 1, _, [_], _, _, _, hux, _ => by simp at hux
  | _ + 1, _, _ :: _ :: _, _, [], _, _, hvx => by simp at hvx
  | _ + 1, _, _ :: _ :: _, _, [_], _, _, hvx => by simp at hvx
  | k + 1, m2, u0 :: u1 :: ur, ys, v0 :: v1 :: vr, ws, hux, hvx => by
      rw [show k + 1 + m2 = (k + m2) + 1 by omega]
      simp only [List.cons_append, List.drop_succ_cons, wronskianMinCheckBle]
      cases Nat.ble W_min (wronskianStepNat Bw u0 u1 v0 v1)
      · rfl
      · exact wronskianMin_append Bw W_min k m2 (u1 :: ur) ys (v1 :: vr) ws
          (by simp at hux ⊢; omega) (by simp at hvx ⊢; omega)
private lemma evenTail_add (Bw : ℕ) :
    ∀ (xs : List ℕ) (p0 n0 p n : ℕ),
      evenTailPosNegLoop Bw xs (p0 + p) (n0 + n) =
        (p0 + (evenTailPosNegLoop Bw xs p n).1, n0 + (evenTailPosNegLoop Bw xs p n).2)
  | [], _, _, _, _ => rfl
  | [_], _, _, _, _ => rfl
  | _ :: ue :: rest, p0, n0, p, n => by
      unfold evenTailPosNegLoop
      cases Nat.blt ue Bw
      · simp only [Bool.false_eq_true, ↓reduceIte, forceNatFast_eq, Nat.add_eq, Nat.add_assoc]
        exact evenTail_add Bw rest p0 n0 _ n
      · simp only [↓reduceIte, forceNatFast_eq, Nat.add_eq, Nat.add_assoc]
        exact evenTail_add Bw rest p0 n0 p _
private lemma evenTail_zero (Bw : ℕ) (xs : List ℕ) (p0 n0 : ℕ) :
    evenTailPosNegLoop Bw xs p0 n0 =
      (p0 + (evenTailPosNegLoop Bw xs 0 0).1, n0 + (evenTailPosNegLoop Bw xs 0 0).2) :=
  evenTail_add Bw xs p0 n0 0 0
private lemma evenTail_append_even (Bw : ℕ) :
    ∀ (k : ℕ) (xs ys : List ℕ) (p n : ℕ), xs.length = 2 * k →
      evenTailPosNegLoop Bw (xs ++ ys) p n =
        let pn := evenTailPosNegLoop Bw xs p n
        evenTailPosNegLoop Bw ys pn.1 pn.2
  | 0, [], _, _, _, _ => rfl
  | 0, _ :: _, _, _, _, hlen => by simp at hlen
  | _ + 1, [], _, _, _, hlen => by simp at hlen
  | _ + 1, [_], _, _, _, hlen => by simp at hlen; omega
  | k + 1, _ :: ue :: rest, ys, p, n, hlen => by
      simp only [List.cons_append, evenTailPosNegLoop]
      cases Nat.blt ue Bw <;> simp only [Bool.false_eq_true, ↓reduceIte, forceNatFast_eq] <;>
        exact evenTail_append_even Bw k rest ys _ _ (by simp at hlen; omega)
noncomputable def gqsp_uBiasedAt (d : ℕ) : ℕ :=
  gqsp_b135598_k409600_u_biased.getD d gqsp_b135598_k409600_cheb_Bw
noncomputable def gqsp_uRealAt (d : ℕ) : ℝ :=
  (gqsp_uBiasedAt d : ℝ) - (gqsp_b135598_k409600_cheb_Bw : ℝ)
noncomputable def gqsp_vBiasedAt (d : ℕ) : ℕ :=
  gqsp_b135598_k409600_v_biased.getD d gqsp_b135598_k409600_cheb_Bw
noncomputable def gqsp_vRealAt (d : ℕ) : ℝ :=
  (gqsp_vBiasedAt d : ℝ) - (gqsp_b135598_k409600_cheb_Bw : ℝ)
noncomputable def gqsp_b135598_k409600_ws : List ℕ :=
  buildChebWsFromBiasedU gqsp_b135598_k409600_cheb_Bw 272802 gqsp_b135598_k409600_u_biased
private lemma uc_parsed :
    gqsp_u_c0.length = 45201 ∧ gqsp_u_c0.getD 0 gqsp_b135598_k409600_cheb_Bw =
      6277101735386680811119783831958774888695941699086909615866 ∧
    gqsp_u_c0.getD 45199 gqsp_b135598_k409600_cheb_Bw =
      6277101735386680731988786961672437354510355985583955838516 ∧
      gqsp_u_c0.getD 45200 gqsp_b135598_k409600_cheb_Bw =
      6277101735386680717167157431483421496742838707710520271826 ∧
    wsMaxMagLoop gqsp_b135598_k409600_cheb_Bw gqsp_u_c0 0 ≤
      292946331321408785259096771508397088968859 ∧
    millerResCountLoop 135598 gqsp_b135598_k409600_cheb_Bw gqsp_b135598_k409600_cheb_Bw 45199 1
      gqsp_u_c0 0 = 2553018200 ∧
    evenTailPosNegLoop gqsp_b135598_k409600_cheb_Bw (gqsp_u_c0.drop 1) 0 0 =
      (704684483198167131608844494039641956536227664,
      704784545188476977559764696730107320389304484) ∧
    doubleBiasedAllGeBle gqsp_b135598_k409600_cheb_Bw (gqsp_u_c0.drop 1) = true ∧
    gqsp_u_c1.length = 45200 ∧
    gqsp_u_c1.getD 45198 gqsp_b135598_k409600_cheb_Bw =
      6277101735386680728082659535261138800208213290465823079480 ∧
      gqsp_u_c1.getD 45199 gqsp_b135598_k409600_cheb_Bw =
      6277101735386680707903924446019345471410010446009742807390 ∧
    wsMaxMagLoop gqsp_b135598_k409600_cheb_Bw gqsp_u_c1 0 ≤
      292946331321408785259096771508397088968859 ∧
    millerResCountLoop 135598 gqsp_b135598_k409600_cheb_Bw gqsp_b135598_k409600_cheb_Bw 45200 45200
      (6277101735386680731988786961672437354510355985583955838516 ::
      6277101735386680717167157431483421496742838707710520271826 :: gqsp_u_c1) 0 = 3542840924 ∧
    evenTailPosNegLoop gqsp_b135598_k409600_cheb_Bw gqsp_u_c1 0 0 =
      (751732118376361498410898107102235033816887008,
      751733431560733410195512754821896863526155994) ∧
    doubleBiasedAllGeBle gqsp_b135598_k409600_cheb_Bw gqsp_u_c1 = true ∧
    gqsp_u_c2.length = 46398 ∧ gqsp_u_c2.getD 46397 gqsp_b135598_k409600_cheb_Bw =
      gqsp_b135598_k409600_cheb_Bw ∧
    gqsp_u_c2.getD 45197 gqsp_b135598_k409600_cheb_Bw = gqsp_b135598_k409600_cheb_Bw +
      gqsp_b135598_k409600_u_beta_off ∧
    wsMaxMagLoop gqsp_b135598_k409600_cheb_Bw gqsp_u_c2 0 ≤
      292946331321408785259096771508397088968859 ∧
    millerResCountLoop 135598 gqsp_b135598_k409600_cheb_Bw gqsp_b135598_k409600_cheb_Bw 45199 90400
      (6277101735386680728082659535261138800208213290465823079480 ::
      6277101735386680707903924446019345471410010446009742807390 :: gqsp_u_c2) 0 = 3986439504 ∧
    millerResCountLoop 135598 gqsp_b135598_k409600_cheb_Bw gqsp_b135598_k409600_cheb_Bw 1200 135599
      (gqsp_u_c2.drop 45197) 0 = 90192196 ∧
    evenTailPosNegLoop gqsp_b135598_k409600_cheb_Bw gqsp_u_c2 0 0 =
      (1059902298516973368640052749423976382690852620,
      1037547462138169738871454774327455450500971088) ∧
    doubleBiasedAllGeBle gqsp_b135598_k409600_cheb_Bw gqsp_u_c2 = true := by
  have h0 := gqsp_uC0Bundle; have h1 := gqsp_uC1Bundle; have h2 := gqsp_uC2Bundle
  rw [StrictListBind_eq] at h0 h1 h2
  unfold gqsp_uC0Checks at h0; unfold gqsp_uC1Checks at h1; unfold gqsp_uC2Checks at h2
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, gqsp_zwGetD_eq, gqsp_zwDrop_eq,
    gqsp_zwMaxMagLoop_eq, gqsp_zwMillerResLoop_eq, gqsp_zwDoubleGeBle_eq, Nat.add_eq] at h0 h1 h2
  have hl0 : gqsp_u_c0.length = 45201 := by
    have x := gqsp_zwLenEq_spec _ _ _ h0.1.1.1.1.1.1.1; omega
  have hl1 : gqsp_u_c1.length = 45200 := by have x := gqsp_zwLenEq_spec _ _ _ h1.1.1.1.1.1.1; omega
  have hl2 : gqsp_u_c2.length = 46398 := by
    have x := gqsp_zwLenEq_spec _ _ _ h2.1.1.1.1.1.1.1; omega
  have he0 : evenTailPosNegLoop gqsp_b135598_k409600_cheb_Bw (gqsp_u_c0.drop 1) 0 0 =
    (704684483198167131608844494039641956536227664,
    704784545188476977559764696730107320389304484) := by
    have hp :=
      h0.1.2; rw [gqsp_zwEvenTailPosNeg_eq gqsp_b135598_k409600_cheb_Bw 22600 _ 0 0 (by rw
      [List.length_drop, hl0])] at hp
    exact Prod.ext hp.1 hp.2
  have he1 : evenTailPosNegLoop gqsp_b135598_k409600_cheb_Bw gqsp_u_c1 0 0 =
    (751732118376361498410898107102235033816887008,
    751733431560733410195512754821896863526155994) := by
    have hp :=
      h1.1.2; rw [gqsp_zwEvenTailPosNeg_eq gqsp_b135598_k409600_cheb_Bw 22600 _ 0 0 (by rw [hl1])]
      at hp
    exact Prod.ext hp.1 hp.2
  have he2 : evenTailPosNegLoop gqsp_b135598_k409600_cheb_Bw gqsp_u_c2 0 0 =
    (1059902298516973368640052749423976382690852620,
    1037547462138169738871454774327455450500971088) := by
    have hp :=
      h2.1.2; rw [gqsp_zwEvenTailPosNeg_eq gqsp_b135598_k409600_cheb_Bw 23199 _ 0 0 (by rw [hl2])]
      at hp
    exact Prod.ext hp.1 hp.2
  exact ⟨hl0, h0.1.1.1.1.1.1.2, h0.1.1.1.1.1.2, h0.1.1.1.1.2, h0.1.1.1.2, h0.1.1.2, he0, h0.2,
    hl1, h1.1.1.1.1.1.2, h1.1.1.1.1.2, h1.1.1.1.2, h1.1.1.2, he1, h1.2,
    hl2, h2.1.1.1.1.1.1.2, h2.1.1.1.1.1.2, h2.1.1.1.1.2, h2.1.1.1.2, h2.1.1.2, he2, h2.2⟩
private lemma vc_parsed :
    gqsp_v_c0.length = 45201 ∧ gqsp_v_c0.getD 45199 gqsp_b135598_k409600_cheb_Bw =
      6277101735386853975512926850978760124971226014122491520119 ∧
      gqsp_v_c0.getD 45200 gqsp_b135598_k409600_cheb_Bw =
      6277101735386798624050786705747500416602554407669458119791 ∧
    wsMaxMagLoop gqsp_b135598_k409600_cheb_Bw gqsp_v_c0 0 ≤
      1010286984355221450013431795359437313032315913 ∧
    millerResCountLoop 135598 gqsp_b135598_k409600_cheb_Bw gqsp_b135598_k409600_cheb_Bw 45199 1
      gqsp_v_c0 0 = 3070301018 ∧
    gqsp_v_c1.length = 45200 ∧ gqsp_v_c1.getD 45198 gqsp_b135598_k409600_cheb_Bw =
      6277101735386875464315395722952600666423885149350380352061 ∧
      gqsp_v_c1.getD 45199 gqsp_b135598_k409600_cheb_Bw =
      6277101735386864241575976988302854741604850110498276281552 ∧
    wsMaxMagLoop gqsp_b135598_k409600_cheb_Bw gqsp_v_c1 0 ≤
      1010286984355221450013431795359437313032315913 ∧
    millerResCountLoop 135598 gqsp_b135598_k409600_cheb_Bw gqsp_b135598_k409600_cheb_Bw 45200 45200
      (6277101735386853975512926850978760124971226014122491520119 ::
      6277101735386798624050786705747500416602554407669458119791 :: gqsp_v_c1) 0 = 3063669512 ∧
    gqsp_v_c2.length = 45199 ∧ gqsp_v_c2.getD 45197 gqsp_b135598_k409600_cheb_Bw =
      gqsp_b135598_k409600_cheb_Bw ∧
    wsMaxMagLoop gqsp_b135598_k409600_cheb_Bw gqsp_v_c2 0 ≤
      1010286984355221450013431795359437313032315913 ∧
    millerResCountLoop 135598 gqsp_b135598_k409600_cheb_Bw gqsp_b135598_k409600_cheb_Bw 45199 90400
      (6277101735386875464315395722952600666423885149350380352061 ::
      6277101735386864241575976988302854741604850110498276281552 :: gqsp_v_c2) 0 = 3082572214 := by
  have h0 := gqsp_vC0Bundle; have h1 := gqsp_vC1Bundle; have h2 := gqsp_vC2Bundle
  rw [StrictListBind_eq] at h0 h1 h2
  unfold gqsp_vC0Checks at h0; unfold gqsp_vC1Checks at h1; unfold gqsp_vC2Checks at h2
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, gqsp_zwGetD_eq, gqsp_zwMaxMagLoop_eq,
    gqsp_zwMillerResLoop_eq] at h0 h1 h2
  have hl0 : gqsp_v_c0.length = 45201 := by have x := gqsp_zwLenEq_spec _ _ _ h0.1.1.1.1; omega
  have hl1 : gqsp_v_c1.length = 45200 := by have x := gqsp_zwLenEq_spec _ _ _ h1.1.1.1.1; omega
  have hl2 : gqsp_v_c2.length = 45199 := by have x := gqsp_zwLenEq_spec _ _ _ h2.1.1.1; omega
  exact ⟨hl0, h0.1.1.1.2, h0.1.1.2, h0.1.2, h0.2, hl1, h1.1.1.1.2, h1.1.1.2, h1.1.2, h1.2, hl2,
    h2.1.1.2, h2.1.2, h2.2⟩
theorem gqsp_b135598_k409600_u_len : gqsp_b135598_k409600_u_biased.length = 136799 := by
  rcases uc_parsed with ⟨hl0, _, _, _, _, _, _, _, hl1, _, _, _, _, _, _, hl2, _⟩
  unfold gqsp_b135598_k409600_u_biased; simp [hl0, hl1, hl2]
theorem gqsp_b135598_k409600_u_top_eq : gqsp_b135598_k409600_u_biased.getD 136798
    gqsp_b135598_k409600_cheb_Bw = gqsp_b135598_k409600_cheb_Bw := by
  rcases uc_parsed with ⟨hl0, _, _, _, _, _, _, _, hl1, _, _, _, _, _, _, _, htop, _⟩
  unfold gqsp_b135598_k409600_u_biased
  rw [show (136798 : ℕ) = 45201 + (45200 + 46397) by rfl, wsGetD_append_right hl0,
    wsGetD_append_right hl1, htop]
theorem gqsp_b135598_k409600_u_beta_eq :
    gqsp_b135598_k409600_u_biased.getD 135598 gqsp_b135598_k409600_cheb_Bw =
      gqsp_b135598_k409600_cheb_Bw + gqsp_b135598_k409600_u_beta_off := by
  rcases uc_parsed with ⟨hl0, _, _, _, _, _, _, _, hl1, _, _, _, _, _, _, _, _, hbeta, _⟩
  unfold gqsp_b135598_k409600_u_biased
  rw [show (135598 : ℕ) = 45201 + (45200 + 45197) by rfl, wsGetD_append_right hl0,
    wsGetD_append_right hl1, hbeta]
private lemma wsMaxMag3_le {Bw M : ℕ} {c0 c1 c2 : List ℕ}
    (hm0 : wsMaxMagLoop Bw c0 0 ≤ M) (hm1 : wsMaxMagLoop Bw c1 0 ≤ M)
    (hm2 : wsMaxMagLoop Bw c2 0 ≤ M) : wsMaxMagLoop Bw (c0 ++ (c1 ++ c2)) 0 ≤ M := by
  rw [wsMaxMag_append, wsMaxMag_append,
    show wsMaxMagLoop Bw c0 0 = Nat.max (wsMaxMagLoop Bw c0 0) 0 by simp, wsMaxMag_max,
    show Nat.max (wsMaxMagLoop Bw c0 0) (wsMaxMagLoop Bw c1 0) =
      Nat.max (Nat.max (wsMaxMagLoop Bw c0 0) (wsMaxMagLoop Bw c1 0)) 0 by simp,
    wsMaxMag_max]
  exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hm0, hm1⟩, hm2⟩
private lemma millerRes3_eq {Bw b00 b01 b10 b11 r0 r1 r2 R : ℕ} {c0 c1 c2 : List ℕ}
    (hl0 : c0.length = 45201) (hb00 : c0.getD 45199 Bw = b00) (hb01 : c0.getD 45200 Bw = b01)
    (hr0 : millerResCountLoop 135598 Bw Bw 45199 1 c0 0 = r0)
    (hl1 : c1.length = 45200) (hb10 : c1.getD 45198 Bw = b10) (hb11 : c1.getD 45199 Bw = b11)
    (hr1 : millerResCountLoop 135598 Bw Bw 45200 45200 (b00 :: b01 :: c1) 0 = r1)
    (hr2 : millerResCountLoop 135598 Bw Bw 45199 90400 (b10 :: b11 :: c2) 0 = r2)
    (hR : r0 + r1 + r2 = R) :
    millerResCountLoop 135598 Bw Bw 135598 1 (c0 ++ (c1 ++ c2)) 0 = R := by
  rw [show (135598 : ℕ) = 45199 + (45200 + 45199) by rfl,
    millerRes_append 135598 Bw Bw 45199 (45200 + 45199) 1 c0 _ 0 (by omega),
    wsDrop_last2 hl0 hb00 hb01, hr0]
  change millerResCountLoop 135598 Bw Bw (45200 + 45199) 45200
    ((b00 :: b01 :: c1) ++ c2) (r0 + 0) = R
  rw [millerRes_append 135598 Bw Bw 45200 45199 45200
    (b00 :: b01 :: c1) c2 _ (by simp [hl1]), millerRes_add, hr1]
  change millerResCountLoop 135598 Bw Bw 45199 90400
    (c1.drop 45198 ++ c2) ((r0 + r1) + 0) = R
  rw [wsDrop_last2 hl1 hb10 hb11, List.cons_append, List.cons_append, List.nil_append,
    millerRes_add, hr2, hR]
theorem gqsp_b135598_k409600_u_max_le : wsMaxMagLoop gqsp_b135598_k409600_cheb_Bw
    gqsp_b135598_k409600_u_biased 0 ≤ 292946331321408785259096771508397088968859 := by
  rcases uc_parsed with ⟨_, _, _, _, hm0, _, _, _, _, _, _, hm1, _, _, _, _, _, _, hm2, _⟩
  exact wsMaxMag3_le hm0 hm1 hm2
theorem gqsp_b135598_k409600_u_res_osc_eq :
    millerResCountLoop 135598 gqsp_b135598_k409600_cheb_Bw gqsp_b135598_k409600_cheb_Bw 135598 1
      gqsp_b135598_k409600_u_biased 0 = 10082298628 := by
  rcases uc_parsed with
    ⟨hl0, _, hb00, hb01, _, hr0, _, _, hl1, hb10, hb11, _, hr1, _, _, _, _, _, _, hr2, _⟩
  exact millerRes3_eq hl0 hb00 hb01 hr0 hl1 hb10 hb11 hr1 hr2 rfl
theorem gqsp_b135598_k409600_u_res_forb_eq :
    millerResCountLoop 135598 gqsp_b135598_k409600_cheb_Bw gqsp_b135598_k409600_cheb_Bw 1200 135599
      (gqsp_b135598_k409600_u_biased.drop 135598) 0 = 90192196 := by
  rcases uc_parsed with ⟨hl0, _, _, _, _, _, _, _, hl1, _, _, _, _, _, _, _, _, _, _, _, hrf,
    _⟩
  have hdrop : gqsp_b135598_k409600_u_biased.drop 135598 = gqsp_u_c2.drop 45197 := by
    unfold gqsp_b135598_k409600_u_biased
    rw [show (135598 : ℕ) = 45201 + (45200 + 45197) by rfl, ← List.drop_drop,
      wsDrop_append_le (by omega), show gqsp_u_c0.drop 45201 = [] by simp [hl0], List.nil_append,
      ← List.drop_drop, wsDrop_append_le (by omega),
        show gqsp_u_c1.drop 45200 = [] by simp [hl1], List.nil_append]
  rw [hdrop, hrf]
theorem gqsp_b135598_k409600_v_len : gqsp_b135598_k409600_v_biased.length = 135600 := by
  rcases vc_parsed with ⟨hl0, _, _, _, _, hl1, _, _, _, _, hl2, _⟩
  unfold gqsp_b135598_k409600_v_biased; simp [hl0, hl1, hl2]
theorem gqsp_b135598_k409600_v_beta_eq : gqsp_b135598_k409600_v_biased.getD 135598
    gqsp_b135598_k409600_cheb_Bw = gqsp_b135598_k409600_cheb_Bw := by
  rcases vc_parsed with ⟨hl0, _, _, _, _, hl1, _, _, _, _, _, hvb, _⟩
  unfold gqsp_b135598_k409600_v_biased
  rw [show (135598 : ℕ) = 45201 + (45200 + 45197) by rfl, wsGetD_append_right hl0,
    wsGetD_append_right hl1, hvb]
theorem gqsp_b135598_k409600_v_max_le : wsMaxMagLoop gqsp_b135598_k409600_cheb_Bw
    gqsp_b135598_k409600_v_biased 0 ≤ 1010286984355221450013431795359437313032315913 := by
  rcases vc_parsed with ⟨_, _, _, hm0, _, _, _, _, hm1, _, _, _, hm2, _⟩
  exact wsMaxMag3_le hm0 hm1 hm2
theorem gqsp_b135598_k409600_v_res_osc_eq :
    millerResCountLoop 135598 gqsp_b135598_k409600_cheb_Bw gqsp_b135598_k409600_cheb_Bw 135598 1
      gqsp_b135598_k409600_v_biased 0 = 9216542744 := by
  rcases vc_parsed with ⟨hl0, vb00, vb01, _, vr0, hl1, vb10, vb11, _, vr1, _, _, _, vr2⟩
  exact millerRes3_eq hl0 vb00 vb01 vr0 hl1 vb10 vb11 vr1 vr2 rfl
theorem gqsp_b135598_k409600_wronskian_min_ble :
    wronskianMinCheckBle gqsp_b135598_k409600_cheb_Bw
      4330057459860444291978438505329115870146009785808438613592383458752120353373623639516
      gqsp_b135598_k409600_u_biased gqsp_b135598_k409600_v_biased 135599 = true := by
  rcases uc_parsed with ⟨hul0, _, _, hub01, _, _, _, _, hul1, _, hub11, _, _, _, _, _, _⟩
  rcases vc_parsed with ⟨hvl0, _, hvb01, _, _, hvl1, _, hvb11, _, _, _, _⟩
  have hw0 := gqsp_wmin_0; have hw1 := gqsp_wmin_1; have hw2 := gqsp_wmin_2
  rw [StrictListBind_eq, StrictListBind_eq, gqsp_zwWronskianMinBle_eq] at hw0 hw1 hw2
  unfold gqsp_b135598_k409600_u_biased gqsp_b135598_k409600_v_biased
  rw [show (135599 : ℕ) = 45200 + (45200 + 45199) by rfl,
    wronskianMin_append _ _ 45200 (45200 + 45199) gqsp_u_c0 _ gqsp_v_c0 _
      (by omega) (by omega),
    hw0, Bool.true_and, wsDrop_last1 hul0 hub01, wsDrop_last1 hvl0 hvb01,
    List.singleton_append, List.singleton_append, ← List.cons_append, ← List.cons_append,
    wronskianMin_append _ _ 45200 45199 (_ :: gqsp_u_c1) gqsp_u_c2
      (_ :: gqsp_v_c1) gqsp_v_c2 (by simp [hul1]) (by simp [hvl1]),
    hw1, Bool.true_and, List.drop_succ_cons, List.drop_succ_cons,
    wsDrop_last1 hul1 hub11, wsDrop_last1 hvl1 hvb11]
  exact hw2
theorem gqsp_b135598_k409600_u_even_sum_eq_int :
    ((gqsp_b135598_k409600_u_biased.getD 0 gqsp_b135598_k409600_cheb_Bw : ℤ) -
      (gqsp_b135598_k409600_cheb_Bw : ℤ)) +
      evenTailBiasedLoop gqsp_b135598_k409600_cheb_Bw (gqsp_b135598_k409600_u_biased.drop 1) 0 =
        22300745198530623141535718272648361502638696 := by
  rcases uc_parsed with ⟨hl0, hu0, _, _, _, _, he0, _, hl1, _, _, _, _, he1, _, hl2, _, _, _,
    _, _, he2, _⟩
  have hg0 : gqsp_b135598_k409600_u_biased.getD 0 gqsp_b135598_k409600_cheb_Bw =
    6277101735386680811119783831958774888695941699086909615866 := by
    unfold gqsp_b135598_k409600_u_biased; rw [wsGetD_append_left (by omega), hu0]
  have hd1 : gqsp_b135598_k409600_u_biased.drop 1 = (gqsp_u_c0.drop 1) ++ (gqsp_u_c1 ++
    gqsp_u_c2) := by
    unfold gqsp_b135598_k409600_u_biased; exact wsDrop_append_le (by omega)
  have het : evenTailPosNegLoop gqsp_b135598_k409600_cheb_Bw (gqsp_b135598_k409600_u_biased.drop 1)
    0 0 =
      (2516318900091501998659795350565853373043967292,
        2494065438887380126626732225879459634416431566) := by
    rw [hd1, evenTail_append_even _ 22600 (gqsp_u_c0.drop 1) _ 0 0
      (by rw [List.length_drop, hl0]), he0,
      evenTail_append_even _ 22600 gqsp_u_c1 gqsp_u_c2 _ _ (by rw [hl1]),
      evenTail_zero _ gqsp_u_c1, he1, evenTail_zero _ gqsp_u_c2, he2]
    rfl
  have hspec :=
    evenTailPosNegLoop_spec gqsp_b135598_k409600_cheb_Bw (gqsp_b135598_k409600_u_biased.drop 1) 0 0
  rw [het] at hspec; simp only [Nat.cast_zero, sub_self] at hspec
  rw [hg0, ← hspec]; unfold gqsp_b135598_k409600_cheb_Bw; norm_num
theorem gqsp_b135598_k409600_double_ge_ble : doubleBiasedAllGeBle gqsp_b135598_k409600_cheb_Bw
    (gqsp_b135598_k409600_u_biased.drop 1) = true := by
  rcases uc_parsed with ⟨hl0, _, _, _, _, _, _, hd0, _, _, _, _, _, _, hd1, _, _, _, _, _, _,
    _, hd2⟩
  unfold gqsp_b135598_k409600_u_biased; rw [wsDrop_append_le (by omega), doubleGe_append,
    doubleGe_append, hd0, hd1, hd2]; rfl
theorem gqsp_b135598_k409600_ws_length : gqsp_b135598_k409600_ws.length = 409600 + 1 := by
  unfold gqsp_b135598_k409600_ws
  rw [buildChebWsFromBiasedU_length _ _ _ (by rw [gqsp_b135598_k409600_u_len]; omega),
    gqsp_b135598_k409600_u_len]
lemma uRealAt_abs_le (d : ℕ) : |gqsp_uRealAt d| ≤
    (292946331321408785259096771508397088968859 : ℝ) :=
  (wsMaxMagLoop_real_le gqsp_b135598_k409600_cheb_Bw gqsp_b135598_k409600_u_biased d).trans (by
    exact_mod_cast gqsp_b135598_k409600_u_max_le)
lemma vRealAt_abs_le (d : ℕ) : |gqsp_vRealAt d| ≤
    (1010286984355221450013431795359437313032315913 : ℝ) :=
  (wsMaxMagLoop_real_le gqsp_b135598_k409600_cheb_Bw gqsp_b135598_k409600_v_biased d).trans (by
    exact_mod_cast gqsp_b135598_k409600_v_max_le)
lemma uBiasedAt_eq_Bw_of_ge {d : ℕ} (hd : 136798 ≤ d) : gqsp_uBiasedAt d =
    gqsp_b135598_k409600_cheb_Bw := by
  unfold gqsp_uBiasedAt
  rcases eq_or_lt_of_le hd with rfl | hlt
  · exact gqsp_b135598_k409600_u_top_eq
  · rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_none (by rw [gqsp_b135598_k409600_u_len]; omega)]; rfl
lemma uRealAt_eq_zero_of_ge {d : ℕ} (hd : 136798 ≤ d) : gqsp_uRealAt d = 0 := by
  unfold gqsp_uRealAt; rw [uBiasedAt_eq_Bw_of_ge hd, sub_self]
lemma uRealAt_beta_eq : gqsp_uRealAt 135598 = (gqsp_b135598_k409600_u_beta_off : ℝ) := by
  unfold gqsp_uRealAt gqsp_uBiasedAt; rw [gqsp_b135598_k409600_u_beta_eq]; push_cast; ring
lemma vRealAt_beta_eq : gqsp_vRealAt 135598 = 0 := by
  unfold gqsp_vRealAt gqsp_vBiasedAt; rw [gqsp_b135598_k409600_v_beta_eq, sub_self]
lemma gqsp_b135598_k409600_wronskian_min_all_osc (k : ℕ) (hk : k < 135599) :
    (4330057459860444291978438505329115870146009785808438613592383458752120353373623639516 : ℝ) ≤
      |gqsp_uRealAt k * gqsp_vRealAt (k + 1) - gqsp_uRealAt (k + 1) * gqsp_vRealAt k| := by
  unfold gqsp_uRealAt gqsp_vRealAt gqsp_uBiasedAt gqsp_vBiasedAt
  rw [← wronskianStepNat_real_eq]
  have h :=
    wronskianMinCheckBle_spec gqsp_b135598_k409600_cheb_Bw
      4330057459860444291978438505329115870146009785808438613592383458752120353373623639516 135599
    gqsp_b135598_k409600_u_biased gqsp_b135598_k409600_v_biased
      gqsp_b135598_k409600_wronskian_min_ble k hk
  exact_mod_cast h
lemma gqsp_b135598_k409600_threeTermRes_chebSingleScaled_s (a M_len : ℕ) :
    ∑ k ∈ Finset.range M_len,
      |threeTermRes 135598 (chebSingleScaled 135598 gqsp_b135598_k409600_cheb_scale0 409600) (a +
      k)| ≤
      (271196 : ℝ) := by
  have h :=
    threeTermRes_chebSingleScaled_sum_le_of_fact_bound 135598 gqsp_b135598_k409600_cheb_scale0
      409600 0 a M_len gqsp_b135598_k409600_fact_bound_nat
  rw [show ((135598 : ℕ) : ℝ) = (135598 : ℝ) by norm_num] at h
  exact h.trans_eq (by push_cast; norm_num)
private lemma res_osc_real {js : List ℕ} {R : ℕ} (hlen : 135598 ≤ js.length)
    (hloop : millerResCountLoop 135598 gqsp_b135598_k409600_cheb_Bw
      gqsp_b135598_k409600_cheb_Bw 135598 1 js 0 = R) :
    ∑ k ∈ Finset.range 135598,
      |threeTermRes 135598 (fun d ↦ (js.getD d gqsp_b135598_k409600_cheb_Bw : ℝ) -
        (gqsp_b135598_k409600_cheb_Bw : ℝ)) k| = (R : ℝ) := by
  have h := millerResCountLoop_real_eq_sum 135598 gqsp_b135598_k409600_cheb_Bw 135598 0 js R
    (by simpa using hlen) (by simpa using hloop)
  rw [show ((135598 : ℕ) : ℝ) = (135598 : ℝ) by norm_num] at h
  simpa only [Nat.zero_add] using h
lemma gqsp_b135598_k409600_u_res_osc_real :
    ∑ k ∈ Finset.range 135598, |threeTermRes 135598 gqsp_uRealAt k| = (10082298628 : ℝ) := by
  exact (res_osc_real
    (by rw [gqsp_b135598_k409600_u_len]; omega) gqsp_b135598_k409600_u_res_osc_eq).trans
    (by norm_num)
lemma gqsp_b135598_k409600_u_res_forb_part_real :
    ∑ k ∈ Finset.range 1200, |threeTermRes 135598 gqsp_uRealAt (135598 + k)| = (90192196 : ℝ) := by
  have h := millerResCountLoop_real_eq_sum 135598 gqsp_b135598_k409600_cheb_Bw 1200 135598
    gqsp_b135598_k409600_u_biased 90192196
    (by rw [List.length_drop, gqsp_b135598_k409600_u_len]; omega) gqsp_b135598_k409600_u_res_forb_eq
  rw [show ((135598 : ℕ) : ℝ) = (135598 : ℝ) by norm_num,
      show ((90192196 : ℕ) : ℝ) = (90192196 : ℝ) by norm_num] at h
  exact h
lemma gqsp_b135598_k409600_u_res_forb_real :
    ∑ k ∈ Finset.range 274002, |threeTermRes 135598 gqsp_uRealAt (135598 + k)| = (90192196 : ℝ) :=
      by
  rw [show (274002 : ℕ) = 1200 + 272802 by rfl, Finset.sum_range_add,
    gqsp_b135598_k409600_u_res_forb_part_real]
  have hzero : ∑ x ∈ Finset.range 272802,
    |threeTermRes 135598 gqsp_uRealAt (135598 + (1200 + x))| = 0 := by
    refine Finset.sum_eq_zero fun x _ ↦ ?_; unfold threeTermRes
    rw [uRealAt_eq_zero_of_ge (by omega), uRealAt_eq_zero_of_ge (by omega),
      uRealAt_eq_zero_of_ge (by omega)]; simp
  linarith
lemma gqsp_b135598_k409600_v_res_osc_real :
    ∑ k ∈ Finset.range 135598, |threeTermRes 135598 gqsp_vRealAt k| = (9216542744 : ℝ) := by
  exact (res_osc_real
    (by rw [gqsp_b135598_k409600_v_len]; omega) gqsp_b135598_k409600_v_res_osc_eq).trans
    (by norm_num)
lemma gqsp_b135598_k409600_ws_getD_real (d : ℕ) :
    (gqsp_b135598_k409600_ws.getD d gqsp_b135598_k409600_cheb_Bw : ℝ) -
      (gqsp_b135598_k409600_cheb_Bw : ℝ) = (wMult d : ℝ) * gqsp_uRealAt d :=
  buildChebWsFromBiasedU_getD_real gqsp_b135598_k409600_cheb_Bw 272802 gqsp_b135598_k409600_u_biased
    (by rw [gqsp_b135598_k409600_u_len]; omega) gqsp_b135598_k409600_double_ge_ble d
noncomputable def gqsp_eErr (d : ℕ) : ℝ :=
  chebSingleScaled 135598 gqsp_b135598_k409600_cheb_scale0 409600 d - gqsp_uRealAt d
noncomputable def gqsp_zCross (d : ℕ) : ℝ :=
  gqsp_uRealAt 135598 * gqsp_eErr d - gqsp_eErr 135598 * gqsp_uRealAt d
lemma zCross_beta : gqsp_zCross 135598 = 0 := by unfold gqsp_zCross; ring
lemma zCross_eq_zero_of_ge {d : ℕ} (hd : 409601 ≤ d) : gqsp_zCross d = 0 := by
  unfold gqsp_zCross
  have he0 : gqsp_eErr d = 0 := by
    unfold gqsp_eErr
    rw [chebSingleScaled_eq_zero_of_lt (by omega : 409600 < d), uRealAt_eq_zero_of_ge (by omega),
      sub_self]
  have hu0 : gqsp_uRealAt d = 0 := uRealAt_eq_zero_of_ge (by omega)
  rw [he0, hu0]; ring
lemma threeTermRes_zCross_le (d : ℕ) :
    |threeTermRes 135598 gqsp_zCross d| ≤
      (gqsp_b135598_k409600_u_beta_off : ℝ) *
        |threeTermRes 135598 (chebSingleScaled 135598 gqsp_b135598_k409600_cheb_scale0 409600) d| +
      ((gqsp_b135598_k409600_u_beta_off : ℝ) + |gqsp_eErr 135598|) *
        |threeTermRes 135598 gqsp_uRealAt d| := by
  have hid : threeTermRes 135598 gqsp_zCross d =
      gqsp_uRealAt 135598 *
        threeTermRes 135598 (chebSingleScaled 135598 gqsp_b135598_k409600_cheb_scale0 409600) d -
      (gqsp_uRealAt 135598 + gqsp_eErr 135598) * threeTermRes 135598 gqsp_uRealAt d := by
    unfold threeTermRes gqsp_zCross gqsp_eErr; ring
  rw [hid]; refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul, uRealAt_beta_eq,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (gqsp_b135598_k409600_u_beta_off : ℝ))]
  gcongr
  exact (abs_add_le _ _).trans (by rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤
    (gqsp_b135598_k409600_u_beta_off : ℝ))])
private lemma zCross_res_sum_le (a M_len : ℕ) :
    ∑ k ∈ Finset.range M_len, |threeTermRes 135598 gqsp_zCross (a + k)| ≤
      (gqsp_b135598_k409600_u_beta_off : ℝ) * ((271196 : ℝ) +
        ∑ k ∈ Finset.range M_len, |threeTermRes 135598 gqsp_uRealAt (a + k)|) +
      (∑ k ∈ Finset.range M_len, |threeTermRes 135598 gqsp_uRealAt (a + k)|) *
        |gqsp_eErr 135598| := by
  have h1 : ∑ k ∈ Finset.range M_len, |threeTermRes 135598 gqsp_zCross (a + k)| ≤
      (gqsp_b135598_k409600_u_beta_off : ℝ) * (∑ k ∈ Finset.range M_len,
        |threeTermRes 135598
          (chebSingleScaled 135598 gqsp_b135598_k409600_cheb_scale0 409600) (a + k)|) +
      ((gqsp_b135598_k409600_u_beta_off : ℝ) + |gqsp_eErr 135598|) *
        ∑ k ∈ Finset.range M_len, |threeTermRes 135598 gqsp_uRealAt (a + k)| := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun k _ ↦ threeTermRes_zCross_le (a + k)
  have hY := gqsp_b135598_k409600_threeTermRes_chebSingleScaled_s a M_len
  have hpos : (0 : ℝ) ≤ (gqsp_b135598_k409600_u_beta_off : ℝ) := by positivity
  nlinarith
lemma gqsp_b135598_k409600_zCross_forb_sum_le :
    2 * ∑ k ∈ Finset.range 274002, |gqsp_zCross (135599 + k)| ≤
      (17564959461520110199368082964496593952728851261920 : ℝ) + (90192196 : ℝ) *
        |gqsp_eErr 135598| := by
  have hdiag := forbiddenZone_diagDom_sum_le 135598 (by positivity) 135598 274002 (by decide)
    (by norm_num) gqsp_zCross zCross_beta (zCross_eq_zero_of_ge (by omega))
  have hres := zCross_res_sum_le 135598 274002
  rw [gqsp_b135598_k409600_u_res_forb_real] at hres
  unfold gqsp_b135598_k409600_u_beta_off at hres
  push_cast at hres
  linarith
lemma gqsp_b135598_k409600_zCross_osc_max_le (k : ℕ) (hk : k < 135599) :
    |gqsp_zCross k| ≤ (1982437592665960321844038765134328154254877328120 : ℝ) + (10209724 : ℝ) *
      |gqsp_eErr 135598| := by
  obtain ⟨k0, hk0_mem, hk0_max⟩ := Finset.exists_max_image (Finset.range 135599) (fun j ↦
    |gqsp_zCross j|) ⟨0, by simp⟩
  have hk0 : k0 < 135599 := Finset.mem_range.mp hk0_mem
  have hmax : ∀ j < 135599, |gqsp_zCross j| ≤ |gqsp_zCross k0| := fun j hj ↦
    hk0_max j (Finset.mem_range.mpr hj)
  have hOv0 : omegaWronskian 135598 gqsp_vRealAt gqsp_zCross 135598 = 0 := by
    unfold omegaWronskian; rw [vRealAt_beta_eq, zCross_beta]; ring
  have hOu0 : omegaWronskian 135598 gqsp_uRealAt gqsp_zCross 136798 = 0 := by
    unfold omegaWronskian; rw [uRealAt_eq_zero_of_ge le_rfl, uRealAt_eq_zero_of_ge (by omega)]; ring
  have hres_osc := zCross_res_sum_le 0 135598
  simp only [Nat.zero_add, gqsp_b135598_k409600_u_res_osc_real] at hres_osc
  have hunt : ∑ d ∈ Finset.range 136798, |threeTermRes 135598 gqsp_uRealAt d| =
      (10082298628 : ℝ) + (90192196 : ℝ) := by
    rw [show (136798 : ℕ) = 135598 + 1200 by rfl, Finset.sum_range_add,
      gqsp_b135598_k409600_u_res_osc_real, gqsp_b135598_k409600_u_res_forb_part_real]
  have hres_nt := zCross_res_sum_le 0 136798
  simp only [Nat.zero_add, hunt, ← add_assoc] at hres_nt
  have hOv : |omegaWronskian 135598 gqsp_vRealAt gqsp_zCross k0| ≤
      (9216542744 : ℝ) * |gqsp_zCross k0| + (1010286984355221450013431795359437313032315913 : ℝ) *
        ∑ d ∈ Finset.range 135598, |threeTermRes 135598 gqsp_zCross d| := by
    have hb := abelWronskian_bound_le_full_sum 135598 gqsp_vRealAt gqsp_zCross 135598 k0 (by omega)
    rw [hOv0, abs_zero, zero_add, Finset.sum_add_distrib] at hb
    refine hb.trans (add_le_add ?_ ?_)
    · rw [← gqsp_b135598_k409600_v_res_osc_real, Finset.sum_mul]
      refine Finset.sum_le_sum fun d hd ↦ ?_
      rw [mul_comm |gqsp_zCross (d + 1)|]
      exact mul_le_mul_of_nonneg_left (hmax (d +
        1) (by rw [Finset.mem_range] at hd; omega)) (abs_nonneg _)
    · rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun d _ ↦
        mul_le_mul_of_nonneg_right (vRealAt_abs_le (d + 1)) (abs_nonneg _)
  have hOu : |omegaWronskian 135598 gqsp_uRealAt gqsp_zCross k0| ≤
      (10082298628 : ℝ) * |gqsp_zCross k0| + (90192196 : ℝ) * (∑ j ∈ Finset.range 274002,
        |gqsp_zCross (135599 + j)|) +
      (292946331321408785259096771508397088968859 : ℝ) * (∑ d ∈ Finset.range 136798,
        |threeTermRes 135598 gqsp_zCross d|) := by
    have hb := abelWronskian_bound_le_full_sum 135598 gqsp_uRealAt gqsp_zCross 136798 k0 (by omega)
    rw [hOu0, abs_zero, zero_add, Finset.sum_add_distrib] at hb
    have hsplit : ∑ d ∈ Finset.range 136798,
      |gqsp_zCross (d + 1)| * |threeTermRes 135598 gqsp_uRealAt d| =
        (∑ d ∈ Finset.range 135598, |gqsp_zCross (d + 1)| * |threeTermRes 135598 gqsp_uRealAt d|) +
        (∑ j ∈ Finset.range 1200,
          |gqsp_zCross (135598 + j + 1)| * |threeTermRes 135598 gqsp_uRealAt (135598 + j)|) := by
      rw [show (136798 : ℕ) = 135598 + 1200 by rfl, Finset.sum_range_add]
    have h1 : ∑ d ∈ Finset.range 135598,
      |gqsp_zCross (d + 1)| * |threeTermRes 135598 gqsp_uRealAt d| ≤ (10082298628 : ℝ) *
      |gqsp_zCross k0| := by
      rw [← gqsp_b135598_k409600_u_res_osc_real, Finset.sum_mul]
      refine Finset.sum_le_sum fun d hd ↦ ?_
      rw [mul_comm |gqsp_zCross (d + 1)|]
      exact mul_le_mul_of_nonneg_left (hmax (d +
        1) (by rw [Finset.mem_range] at hd; omega)) (abs_nonneg _)
    have h2 : ∑ j ∈ Finset.range 1200,
      |gqsp_zCross (135598 + j + 1)| * |threeTermRes 135598 gqsp_uRealAt (135598 + j)| ≤
         (90192196 : ℝ) * ∑ j ∈ Finset.range 274002, |gqsp_zCross (135599 + j)| := by
      rw [← gqsp_b135598_k409600_u_res_forb_part_real, Finset.sum_mul]
      refine Finset.sum_le_sum fun j hj ↦ ?_
      rw [mul_comm |gqsp_zCross (135598 + j + 1)|, show 135598 + j + 1 = 135599 + j by omega]
      exact mul_le_mul_of_nonneg_left (Finset.single_le_sum
        (f := fun i ↦ |gqsp_zCross (135599 + i)|) (fun _ _ ↦ abs_nonneg _)
        (Finset.mem_range.mpr (by rw [Finset.mem_range] at hj; omega))) (abs_nonneg _)
    have h3 : ∑ d ∈ Finset.range 136798,
      |gqsp_uRealAt (d + 1)| * |threeTermRes 135598 gqsp_zCross d| ≤
        (292946331321408785259096771508397088968859 : ℝ) * ∑ d ∈ Finset.range 136798,
          |threeTermRes 135598 gqsp_zCross d| := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun d _ ↦
        mul_le_mul_of_nonneg_right (uRealAt_abs_le (d + 1)) (abs_nonneg _)
    linarith
  have hcramer :
    (587147131442156525103692304445617453760058634936052659125900012239870015676756618271090568 : ℝ)
    * |gqsp_zCross k0| ≤
      (292946331321408785259096771508397088968859 : ℝ) *
        |omegaWronskian 135598 gqsp_vRealAt gqsp_zCross k0| +
      (1010286984355221450013431795359437313032315913 : ℝ) *
        |omegaWronskian 135598 gqsp_uRealAt gqsp_zCross k0| := by
    have hc := congrArg abs (cramer_elim_eq 135598 gqsp_uRealAt gqsp_vRealAt gqsp_zCross k0)
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 135598)] at hc
    have hW := gqsp_b135598_k409600_wronskian_min_all_osc k0 hk0
    have hlhs :
      (587147131442156525103692304445617453760058634936052659125900012239870015676756618271090568 :
      ℝ) * |gqsp_zCross k0| ≤
        (135598 : ℝ) * |gqsp_uRealAt k0 * gqsp_vRealAt (k0 + 1) - gqsp_uRealAt (k0 + 1) *
          gqsp_vRealAt k0| * |gqsp_zCross k0| := by
      nlinarith [abs_nonneg (gqsp_zCross k0)]
    have hrhs : |gqsp_vRealAt k0 * omegaWronskian 135598 gqsp_uRealAt gqsp_zCross k0 -
      gqsp_uRealAt k0 * omegaWronskian 135598 gqsp_vRealAt gqsp_zCross k0| ≤
        (292946331321408785259096771508397088968859 : ℝ) *
          |omegaWronskian 135598 gqsp_vRealAt gqsp_zCross k0| +
        (1010286984355221450013431795359437313032315913 : ℝ) *
          |omegaWronskian 135598 gqsp_uRealAt gqsp_zCross k0| := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_mul, add_comm]
      exact add_le_add (mul_le_mul_of_nonneg_right (uRealAt_abs_le k0) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (vRealAt_abs_le k0) (abs_nonneg _))
    linarith
  have hk0_le : |gqsp_zCross k0| ≤ (1982437592665960321844038765134328154254877328120 : ℝ) +
    (10209724 : ℝ) * |gqsp_eErr 135598| := by
    unfold gqsp_b135598_k409600_u_beta_off at hres_osc hres_nt; push_cast at hres_osc hres_nt
    linarith [gqsp_b135598_k409600_zCross_forb_sum_le, abs_nonneg (gqsp_eErr 135598)]
  exact (hmax k hk).trans hk0_le
lemma gqsp_b135598_k409600_uRealAt_even_sum_eq : gqsp_uRealAt 0 + ∑ m ∈ Finset.range 204800,
    2 * gqsp_uRealAt (2 * (m + 1)) = (22300745198530623141535718272648361502638696 : ℝ) := by
  have hpart : gqsp_uRealAt 0 + ∑ m ∈ Finset.range 68399, 2 * gqsp_uRealAt (2 * (m + 1)) =
      (22300745198530623141535718272648361502638696 : ℝ) := by
    have h :=
      evenTailBiasedLoop_real_eq_sum gqsp_b135598_k409600_cheb_Bw 68399
      gqsp_b135598_k409600_u_biased
      22300745198530623141535718272648361502638696
      (by rw [List.length_drop, gqsp_b135598_k409600_u_len]) gqsp_b135598_k409600_u_even_sum_eq_int
    rw [show ((22300745198530623141535718272648361502638696 : ℤ) : ℝ) =
      (22300745198530623141535718272648361502638696 : ℝ) by norm_num] at h
    exact h
  rw [show (204800 : ℕ) = 68399 + 136401 by rfl, Finset.sum_range_add]
  have hzero : ∑ x ∈ Finset.range 136401, 2 * gqsp_uRealAt (2 * (68399 + x + 1)) = 0 :=
    Finset.sum_eq_zero fun x _ ↦ by rw [uRealAt_eq_zero_of_ge (by omega)]; ring
  rw [hzero, add_zero]
  exact hpart
lemma gqsp_b135598_k409600_eErr_beta_abs_le :
    |gqsp_eErr 135598| ≤ (12054967973 : ℝ) := by
  have hY_even := chebSingleScaled_even_sum_eq_scale0 135598 gqsp_b135598_k409600_cheb_scale0 409600
  have hu_even := gqsp_b135598_k409600_uRealAt_even_sum_eq
  have he_even : gqsp_eErr 0 + ∑ m ∈ Finset.range 204800,
    2 * gqsp_eErr (2 * (m + 1)) = (3341720 : ℝ) := by
    have hdiff : (chebSingleScaled 135598 gqsp_b135598_k409600_cheb_scale0 409600 0 -
      gqsp_uRealAt 0) +
        ∑ m ∈ Finset.range 204800,
          2 * (chebSingleScaled 135598 gqsp_b135598_k409600_cheb_scale0 409600 (2 * (m + 1)) -
          gqsp_uRealAt (2 * (m + 1))) =
        (gqsp_b135598_k409600_cheb_scale0 : ℝ) -
          (22300745198530623141535718272648361502638696 : ℝ) := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]; linarith
    unfold gqsp_eErr; rw [hdiff]; unfold gqsp_b135598_k409600_cheb_scale0; norm_num
  have hz_rel : ∀ d,
    (gqsp_b135598_k409600_u_beta_off : ℝ) * gqsp_eErr d = gqsp_zCross d + gqsp_eErr 135598 *
    gqsp_uRealAt d := by
    intro d; unfold gqsp_zCross; rw [uRealAt_beta_eq]; ring
  have h_ident : (22300745198530623141535718272648361502638696 : ℝ) * gqsp_eErr 135598 =
      (gqsp_b135598_k409600_u_beta_off : ℝ) * (3341720 : ℝ) - (gqsp_zCross 0 +
        ∑ m ∈ Finset.range 204800, 2 * gqsp_zCross (2 * (m + 1))) := by
    have hmul := congrArg ((gqsp_b135598_k409600_u_beta_off : ℝ) * ·) he_even
    rw [mul_add, Finset.mul_sum] at hmul
    have hsum_eq : ∑ m ∈ Finset.range 204800,
      (gqsp_b135598_k409600_u_beta_off : ℝ) * (2 * gqsp_eErr (2 * (m + 1))) =
        (∑ m ∈ Finset.range 204800, 2 * gqsp_zCross (2 * (m + 1))) +
        gqsp_eErr 135598 * (∑ m ∈ Finset.range 204800, 2 * gqsp_uRealAt (2 * (m + 1))) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      have hz := hz_rel (2 * (m + 1)); linarith
    rw [hz_rel 0, hsum_eq] at hmul
    linear_combination hmul - gqsp_eErr 135598 * hu_even
  have h_abs : (22300745198530623141535718272648361502638696 : ℝ) * |gqsp_eErr 135598| ≤
      (gqsp_b135598_k409600_u_beta_off : ℝ) * (3341720 : ℝ) + |gqsp_zCross 0| +
        ∑ m ∈ Finset.range 204800, 2 * |gqsp_zCross (2 * (m + 1))| := by
    have h1 := congrArg abs h_ident
    rw [abs_mul, abs_of_nonneg (by positivity)] at h1
    have h2 : |(gqsp_b135598_k409600_u_beta_off : ℝ) * (3341720 : ℝ) - (gqsp_zCross 0 +
      ∑ m ∈ Finset.range 204800, 2 * gqsp_zCross (2 * (m + 1)))| ≤
        (gqsp_b135598_k409600_u_beta_off : ℝ) * (3341720 : ℝ) + |gqsp_zCross 0| +
          ∑ m ∈ Finset.range 204800, 2 * |gqsp_zCross (2 * (m + 1))| := by
      refine (abs_sub _ _).trans ?_
      have head_abs : |(gqsp_b135598_k409600_u_beta_off : ℝ) * (3341720 : ℝ)| =
        (gqsp_b135598_k409600_u_beta_off : ℝ) * (3341720 : ℝ) := by
        unfold gqsp_b135598_k409600_u_beta_off; norm_num
      rw [head_abs, add_assoc]
      refine add_le_add le_rfl ((abs_add_le _ _).trans (add_le_add le_rfl ?_))
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ ↦ ?_)
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2)]
    linarith
  rw [show (204800 : ℕ) = 67799 + 137001 by rfl, Finset.sum_range_add] at h_abs
  have h_osc_sum : |gqsp_zCross 0| + ∑ m ∈ Finset.range 67799, 2 * |gqsp_zCross (2 * (m + 1))| ≤
      135599 * ((1982437592665960321844038765134328154254877328120 : ℝ) + (10209724 : ℝ) *
        |gqsp_eErr 135598|) := by
    have hz0 := gqsp_b135598_k409600_zCross_osc_max_le 0 (by decide)
    have hzm : ∑ m ∈ Finset.range 67799, 2 * |gqsp_zCross (2 * (m + 1))| ≤
        ∑ _m ∈ Finset.range 67799,
          2 * ((1982437592665960321844038765134328154254877328120 : ℝ) + (10209724 : ℝ) *
          |gqsp_eErr 135598|) :=
      Finset.sum_le_sum fun m hm ↦ mul_le_mul_of_nonneg_left
        (gqsp_b135598_k409600_zCross_osc_max_le (2 * (m +
          1)) (by rw [Finset.mem_range] at hm; omega)) (by positivity)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hzm
    push_cast at hzm
    linarith
  have h_forb_sum : ∑ j ∈ Finset.range 137001, 2 * |gqsp_zCross (2 * (67799 + j + 1))| ≤
      (17564959461520110199368082964496593952728851261920 : ℝ) + (90192196 : ℝ) *
        |gqsp_eErr 135598| := by
    have hrew : ∑ j ∈ Finset.range 137001, 2 * |gqsp_zCross (2 * (67799 + j + 1))| =
        2 * ∑ j ∈ Finset.range 137001, |gqsp_zCross (135599 + (2 * j + 1))| := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [show 2 * (67799 + j + 1) = 135599 + (2 * j + 1) by omega]
    have hodd := sum_odd_le_sum_two_mul (fun k ↦ |gqsp_zCross (135599 + k)|) (fun _ ↦
      abs_nonneg _) 137001
    rw [show 2 * 137001 = 274002 by rfl] at hodd
    linarith [gqsp_b135598_k409600_zCross_forb_sum_le]
  unfold gqsp_b135598_k409600_u_beta_off at h_abs; push_cast at h_abs
  linarith
lemma gqsp_b135598_k409600_eErr_abs_le_all (d : ℕ) (hd : d < 409600 + 1) :
    |gqsp_eErr d| ≤ (2 ^ 93 : ℝ) := by
  have heb := gqsp_b135598_k409600_eErr_beta_abs_le
  have hz_eq : (gqsp_b135598_k409600_u_beta_off : ℝ) * gqsp_eErr d = gqsp_zCross d +
    gqsp_eErr 135598 * gqsp_uRealAt d := by
    unfold gqsp_zCross; rw [uRealAt_beta_eq]; ring
  have hz_abs : (gqsp_b135598_k409600_u_beta_off : ℝ) * |gqsp_eErr d| ≤ |gqsp_zCross d| +
    (292946331321408785259096771508397088968859 : ℝ) * |gqsp_eErr 135598| := by
    have h1 := congrArg abs hz_eq
    rw [abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (gqsp_b135598_k409600_u_beta_off : ℝ))] at h1
    have h2 : |gqsp_zCross d + gqsp_eErr 135598 * gqsp_uRealAt d| ≤ |gqsp_zCross d| +
      (292946331321408785259096771508397088968859 : ℝ) * |gqsp_eErr 135598| := by
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (uRealAt_abs_le d) (abs_nonneg _)
    linarith
  by_cases hd_osc : d < 135599
  · have hz_bound := gqsp_b135598_k409600_zCross_osc_max_le d hd_osc
    unfold gqsp_b135598_k409600_u_beta_off at hz_abs; push_cast at hz_abs
    linarith
  · have hforb : 2 * |gqsp_zCross d| ≤ 2 * ∑ k ∈ Finset.range 274002, |gqsp_zCross (135599 + k)| :=
    by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [show d = 135599 + (d - 135599) by omega]
      exact Finset.single_le_sum (f := fun k ↦ |gqsp_zCross (135599 + k)|) (fun _ _ ↦ abs_nonneg _)
        (Finset.mem_range.mpr (by omega))
    have hz_bound := hforb.trans gqsp_b135598_k409600_zCross_forb_sum_le
    unfold gqsp_b135598_k409600_u_beta_off at hz_abs; push_cast at hz_abs
    linarith
theorem aux_b135598_k409600_hscale0 : 2 ^ 48 * powMulFast (2 ^ 48) 2 1 =
    gqsp_b135598_k409600_cheb_scale0 := by decide +kernel
theorem aux_b135598_k409600_hBw : powMulFast (2 ^ 48) 1 1 * gqsp_b135598_k409600_cheb_scale0 =
    gqsp_b135598_k409600_cheb_Bw := by decide +kernel
theorem gqsp_b135598_k409600_ws_hws_err :
    ∀ d < 409600 + 1,
      let scale0 := 2 ^ 48 * powMulFast (2 ^ 48) 2 1
      let Bw := powMulFast (2 ^ 48) 1 1 * scale0
      |(scale0 : ℝ) * chebTaylorWeight (135598 : ℝ) 409600 d -
        ((gqsp_b135598_k409600_ws.getD d Bw : ℝ) - (Bw : ℝ))| ≤
        (if d = 0 then (gqsp_b135598_k409600_W_err_d0 : ℝ) else
          (gqsp_b135598_k409600_W_err_dpos : ℝ)) := by
  intro d hd
  have hscale0 : 2 ^ 48 * powMulFast (2 ^ 48) 2 1 = gqsp_b135598_k409600_cheb_scale0 :=
    aux_b135598_k409600_hscale0
  have hBw : powMulFast (2 ^ 48) 1 1 * gqsp_b135598_k409600_cheb_scale0 =
    gqsp_b135598_k409600_cheb_Bw := aux_b135598_k409600_hBw
  dsimp only
  rw [hscale0, hBw, gqsp_b135598_k409600_ws_getD_real d]
  have hw_ne : (wMult d : ℝ) ≠ 0 := by
    rcases wMult_pos d with ⟨h1, _⟩
    have : (1 : ℝ) ≤ (wMult d : ℝ) := by exact_mod_cast h1
    linarith
  have hdiff : (gqsp_b135598_k409600_cheb_scale0 : ℝ) * chebTaylorWeight (135598 : ℝ) 409600 d -
    (wMult d : ℝ) * gqsp_uRealAt d =
      (wMult d : ℝ) * gqsp_eErr d := by
    unfold gqsp_eErr chebSingleScaled
    rw [show ((135598 : ℕ) : ℝ) = (135598 : ℝ) by norm_num]
    field_simp [hw_ne]
  rw [hdiff, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (wMult d : ℝ))]
  have he := gqsp_b135598_k409600_eErr_abs_le_all d hd
  unfold gqsp_b135598_k409600_W_err_d0 gqsp_b135598_k409600_W_err_dpos
  rcases d with _ | k
  · simp only [↓reduceIte, wMult, Nat.cast_one, one_mul]; exact_mod_cast he
  · simp only [show k + 1 ≠ 0 by omega, ↓reduceIte, wMult, Nat.cast_ofNat]; linarith
private lemma doubleBiasedRev_map (Bw : ℕ) :
    ∀ (xs acc : List ℕ), gqsp_zwDoubleBiasedRevTR Bw xs acc =
      (xs.map (fun u ↦ Nat.sub (Nat.mul 2 u) Bw)).reverse ++ acc
  | [], _ => rfl
  | u :: ut, acc => by
      dsimp only [gqsp_zwDoubleBiasedRevTR]; rw [gqsp_zwForce_eq]
      change gqsp_zwDoubleBiasedRevTR Bw ut (_ :: acc) = _
      rw [doubleBiasedRev_map Bw ut, List.map_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append]
noncomputable def gqsp_ws_c0 : List ℕ :=
  gqsp_buildChebWsUnpadLowMem gqsp_b135598_k409600_cheb_Bw gqsp_u_c0
noncomputable def gqsp_ws_c1 : List ℕ :=
  gqsp_zwRevNatTR (gqsp_zwDoubleBiasedRevTR gqsp_b135598_k409600_cheb_Bw gqsp_u_c1 []) []
noncomputable def gqsp_ws_c2 : List ℕ :=
  gqsp_zwRevNatTR (gqsp_zwDoubleBiasedRevTR gqsp_b135598_k409600_cheb_Bw gqsp_u_c2 []) []
noncomputable def gqsp_b135598_k409600_ws_unpad : List ℕ := gqsp_ws_c0 ++ (gqsp_ws_c1 ++ gqsp_ws_c2)
theorem gqsp_ws_unpad_eq_lowMem :
    gqsp_b135598_k409600_ws_unpad =
      gqsp_buildChebWsUnpadLowMem gqsp_b135598_k409600_cheb_Bw gqsp_b135598_k409600_u_biased := by
  have hl0 := uc_parsed.1
  rcases hc0 : gqsp_u_c0 with _ | ⟨u0, ut0⟩
  · simp [hc0] at hl0
  · unfold gqsp_b135598_k409600_ws_unpad gqsp_ws_c0 gqsp_ws_c1 gqsp_ws_c2
      gqsp_b135598_k409600_u_biased
    rw [hc0]; dsimp only [gqsp_buildChebWsUnpadLowMem, List.cons_append]
    simp only [gqsp_zwRevNatTR_eq, ta_revNatTR_eq, doubleBiasedRev_map,
      List.append_nil, List.reverse_reverse, List.map_append]
theorem gqsp_b135598_k409600_ws_unpad_append_eq :
    gqsp_b135598_k409600_ws_unpad ++ List.replicate 272802 ta_Bw = gqsp_b135598_k409600_ws := by
  rw [gqsp_ws_unpad_eq_lowMem]
  exact gqsp_buildChebWsUnpadLowMem_append_eq _ _ _ (by rw [gqsp_b135598_k409600_u_len]; omega)
theorem gqsp_b135598_k409600_ws_unpad_len : gqsp_b135598_k409600_ws_unpad.length = 136799 := by
  have hl := gqsp_b135598_k409600_ws_length
  rw [← gqsp_b135598_k409600_ws_unpad_append_eq, List.length_append,
    List.length_replicate] at hl; omega
theorem aux_b135598_k409600_tay_step :
    135598 * (409600 + 2) * 2 ^ 48 ≤ gqsp_b135598_k409600_cheb_scale0 * (409600 + 1) * (409600 + 2 -
      135598) := by
  decide +kernel
private lemma tay_algebra (S B K K1 K2 Z ONE SH : ℕ) (hK1 : K1 = K + 1)
    (hK2 : K2 = K + 2) (hZ : Z = 0) (hONE : ONE = 1) (hSH : SH = 48)
    (hfact : S * B ^ K ≤ 2 ^ Z * K.factorial)
    (hstep : B * (K + 2) * 2 ^ SH ≤ S * (K + 1) * (K + 2 - B)) : B ^ K1 * K2 * 2 ^ SH ≤ ONE *
    K1.factorial * (K2 - B) := by
  subst hK1 hK2 hZ hONE hSH
  rw [Nat.pow_succ, Nat.factorial_succ]
  calc (B ^ K * B) * (K + 2) * 2 ^ 48
    _ = B ^ K * (B * (K + 2) * 2 ^ 48) := by ring
    _ ≤ B ^ K * (S * (K + 1) * (K + 2 - B)) := Nat.mul_le_mul_left _ hstep
    _ = (S * B ^ K) * ((K + 1) * (K + 2 - B)) := by ring
    _ ≤ (2 ^ 0 * K.factorial) * ((K + 1) * (K + 2 - B)) := Nat.mul_le_mul_right _ hfact
    _ = 1 * ((K + 1) * K.factorial) * (K + 2 - B) := by ring
theorem gqsp_b135598_k409600_tay_nat : 135598 ^ (409600 + 1) * (409600 + 2) * 2 ^ 48 ≤ 1 *
    (409600 + 1).factorial * (409600 + 2 - 135598) := tay_algebra
    gqsp_b135598_k409600_cheb_scale0 135598 409600 (409600 + 1) (409600 + 2) 0 1 48 rfl rfl
    rfl rfl rfl gqsp_b135598_k409600_fact_bound_nat aux_b135598_k409600_tay_step
end WronskianChebCert_b135598_k409600
end GqspWronskian135598
end
end GqspWronskian135598

end QuantumComputation.Specs.StoppingPowerSolution
end
