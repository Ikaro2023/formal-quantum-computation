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
public import Mathlib.Tactic.IrreducibleDef
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.PipelinedFuseCertDefs
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.SchurWeylHdistLCertDefs
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.SchurWeylHdistLQHL
/-
Long-Horizon T = 2700 (3 x 900) H_dist(L = 2) Certificate for (m = 1, k = 2)
(LongTailM1K2Only).
Certifies coprime relCost(1, 2) = 379666241046199 / 500000000000000
(759332482092398 / 1000000000000000)
-/
namespace QuantumComputation.Specs.GroverFindAll
open Operator Matrix Real QProg QProg.Notation ResourceCounting
open QuantumComputation.Specs.GroverFindAll.SchurWeylLCert
open QuantumComputation.Specs.GroverFindAll.PipeFuseCert
open QuantumComputation.Specs.GroverFindAll.TensorConveyorCert
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open scoped InnerProductSpace QHLExpectation BigOperators
public section
/-- Base `10^60` used to split `> 60`-digit integer endpoints across `<= 100`-column lines. -/
def ltM1K2Dec60 : ℕ := Nat.pow 10 60
/-- Natural-number `10^100` amplitude scale matching `tcAmpScale`. -/
def ltM1K2AmpNat : ℕ := Nat.pow 10 100
/-- Scale ratio `10^91 = tcAmpScale / swScale` projecting `10^100` intervals to `10^9`. -/
def ltM1K2Div91 : ℤ := Int.ofNat (Nat.pow 10 91)
theorem ltM1K2Div91_pos : (0 : ℤ) < ltM1K2Div91 := by
  unfold ltM1K2Div91; simp only [Nat.pow_eq, Int.ofNat_eq_natCast]; norm_num
theorem ltM1K2_tcAmpScale_eq : tcAmpScale = swScale * ltM1K2Div91 := by
  unfold tcAmpScale swScale ltM1K2Div91; simp only [Nat.pow_eq, Int.ofNat_eq_natCast]; norm_num
/-- Outward-rounded projection from a `10^100`-scale `TcIv` to a `10^9`-scale `IvInt`. -/
def ltM1K2Iv100To9 (iv : TcIv) : IvInt :=
  tcWithForcedInt ltM1K2Div91 fun d91 ↦
    (Int.ediv iv.1 d91, Int.neg (Int.ediv (Int.neg iv.2) d91))
theorem ltM1K2_memIvInt_of_tcMemAmpIv {x : ℝ} {iv : TcIv} (hx : tcMemAmpIv x iv) :
    memIvInt x (ltM1K2Iv100To9 iv) := by
  have hS : (0 : ℝ) < (swScale : ℝ) := (by unfold swScale; norm_num)
  have hD_pos : (0 : ℤ) < ltM1K2Div91 := ltM1K2Div91_pos
  have hD_r : (0 : ℝ) < (ltM1K2Div91 : ℝ) := Int.cast_pos.2 hD_pos
  have hmul_r : (tcAmpScale : ℝ) = (swScale : ℝ) * (ltM1K2Div91 : ℝ) := by
    exact_mod_cast ltM1K2_tcAmpScale_eq
  unfold ltM1K2Iv100To9 memIvInt; unfold tcMemAmpIv at hx
  simp only [tcWithForcedInt_eq, tcInt_ediv_eq, tcInt_neg_eq]; constructor
  · have h1 := div_le_div_of_nonneg_right (tc_ediv_pos_le_real iv.1 ltM1K2Div91 hD_pos) hS.le
    have h2 : (iv.1 : ℝ) / (ltM1K2Div91 : ℝ) / (swScale : ℝ) = (iv.1 : ℝ) / (tcAmpScale : ℝ) := by
      rw [hmul_r]; field_simp [hS.ne', hD_r.ne']
    exact (h1.trans_eq h2).trans hx.1
  · have h1 := div_le_div_of_nonneg_right
      (tc_real_le_neg_ediv_neg_pos iv.2 ltM1K2Div91 hD_pos) hS.le
    have h2 : (iv.2 : ℝ) / (tcAmpScale : ℝ) = (iv.2 : ℝ) / (ltM1K2Div91 : ℝ) / (swScale : ℝ) := by
      rw [hmul_r]; field_simp [hS.ne', hD_r.ne']
    exact hx.2.trans (h2.trans_le h1)
theorem ltM1K2_tcMemAmpIv_one : tcMemAmpIv 1 (tcAmpScale, tcAmpScale) := by
  have hS : (tcAmpScale : ℝ) ≠ 0 := tcAmpScale_pos_real.ne'; unfold tcMemAmpIv; dsimp only
  rw [div_self hS]; exact ⟨le_rfl, le_rfl⟩
theorem ltM1K2_tcMemAmpIv_zero : tcMemAmpIv 0 (Int.ofNat 0, Int.ofNat 0) := by
  unfold tcMemAmpIv; simp only [tcInt_ofNat_eq, Nat.cast_zero, Int.cast_zero, zero_div]
  exact ⟨le_rfl, le_rfl⟩
/-- Constructor-level negation `-(n: ℤ)` avoiding `Int.neg` in kernel reduction. -/
def ltM1K2NegNat : ℕ → ℤ
  | 0 => Int.ofNat 0
  | Nat.succ m => Int.negSucc m
private theorem ltM1K2NegNat_eq (n : ℕ) : ltM1K2NegNat n = -((n : ℕ) : ℤ) := by
  cases n with
  | zero => rfl
  | succ m => simp only [ltM1K2NegNat, Int.negSucc_eq, Nat.cast_succ]
private theorem ltM1K2_nat_mul_eq (a b : ℕ) : Nat.mul a b = a * b := rfl
private theorem ltM1K2_nat_add_eq (a b : ℕ) : Nat.add a b = a + b := rfl
private theorem ltM1K2_nat_sub_eq (a b : ℕ) : Nat.sub a b = a - b := rfl
private theorem ltM1K2_nat_div_eq (a b : ℕ) : Nat.div a b = a / b := rfl
private theorem ltM1K2AmpNat_cast : ((ltM1K2AmpNat : ℕ) : ℝ) = (tcAmpScale : ℝ) := by
  unfold ltM1K2AmpNat tcAmpScale; rw [tcInt_ofNat_eq, Int.cast_natCast]
/-- Outward-rounded `(⌊x / d⌋, ⌈x / d⌉)` for `x, d: ℕ` via pure `Nat.div`. -/
def ltM1K2DivPairPos (x d : ℕ) : TcIv :=
  (Int.ofNat (Nat.div x d), Int.ofNat (Nat.div (Nat.add x (Nat.sub d 1)) d))
/-- Outward-rounded `(⌊-x / d⌋, ⌈-x / d⌉)` for `x, d: ℕ` via pure `Nat.div`. -/
def ltM1K2DivPairNeg (x d : ℕ) : TcIv :=
  (ltM1K2NegNat (Nat.div (Nat.add x (Nat.sub d 1)) d), ltM1K2NegNat (Nat.div x d))
private theorem ltM1K2DivPairPos_mem {x0 d : ℕ} (hd : 0 < d) :
    tcMemAmpIv ((x0 : ℝ) / (d : ℝ)) (ltM1K2DivPairPos (Nat.mul x0 ltM1K2AmpNat) d) := by
  have hd_r : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.2 hd
  have hS_r : (0 : ℝ) < (tcAmpScale : ℝ) := tcAmpScale_pos_real; unfold ltM1K2DivPairPos tcMemAmpIv
  simp only [ltM1K2_nat_mul_eq, ltM1K2_nat_add_eq, ltM1K2_nat_sub_eq, ltM1K2_nat_div_eq,
    tcInt_ofNat_eq, Int.cast_natCast]; set x : ℕ := x0 * ltM1K2AmpNat
  have hx_r : (x : ℝ) = (x0 : ℝ) * (tcAmpScale : ℝ) := by
    dsimp [x]; rw [Nat.cast_mul, ltM1K2AmpNat_cast]
  constructor
  · rw [div_le_div_iff₀ hS_r hd_r]; have hlo_nat : (x / d) * d ≤ x := Nat.div_mul_le_self x d
    have hlo_r : (((x / d) * d : ℕ) : ℝ) ≤ (x : ℝ) := Nat.cast_le.2 hlo_nat
    rw [Nat.cast_mul, hx_r] at hlo_r; linarith [hlo_r]
  · rw [div_le_div_iff₀ hd_r hS_r]; set q : ℕ := (x + (d - 1)) / d
    have hdiv : d * q + (x + (d - 1)) % d = x + (d - 1) := Nat.div_add_mod (x + (d - 1)) d
    have hmod : (x + (d - 1)) % d < d := Nat.mod_lt (x + (d - 1)) hd
    have hhi_dq : x ≤ d * q := (by omega)
    calc (x0 : ℝ) * (tcAmpScale : ℝ) = (x : ℝ) := hx_r.symm
      _ ≤ ((d * q : ℕ) : ℝ) := Nat.cast_le.2 hhi_dq
      _ = (d : ℝ) * (q : ℝ) := Nat.cast_mul d q
      _ = (q : ℝ) * (d : ℝ) := mul_comm (d : ℝ) (q : ℝ)
private theorem ltM1K2DivPairNeg_mem {x0 d : ℕ} (hd : 0 < d) :
    tcMemAmpIv (-((x0 : ℝ) / (d : ℝ))) (ltM1K2DivPairNeg (Nat.mul x0 ltM1K2AmpNat) d) := by
  have hpos := ltM1K2DivPairPos_mem (x0 := x0) hd; unfold ltM1K2DivPairPos tcMemAmpIv at hpos
  simp only [tcInt_ofNat_eq, Int.cast_natCast] at hpos; unfold ltM1K2DivPairNeg tcMemAmpIv
  simp only [ltM1K2NegNat_eq, Int.cast_neg, Int.cast_natCast, neg_div]
  exact ⟨neg_le_neg hpos.2, neg_le_neg hpos.1⟩
/-- Pure-`Nat` `10^100`-scale Pythagorean cosine interval `(den^2 - a^2) / (den^2 + a^2)`. -/
def ltM1K2CosPairNat (a den : ℕ) : TcIv :=
  let d2 := Nat.mul den den
  let n2 := Nat.mul a a
  let sumSq := Nat.add d2 n2
  if Nat.ble n2 d2 then
    ltM1K2DivPairPos (Nat.mul (Nat.sub d2 n2) ltM1K2AmpNat) sumSq
  else
    ltM1K2DivPairNeg (Nat.mul (Nat.sub n2 d2) ltM1K2AmpNat) sumSq
private theorem ltM1K2CosPairNat_mem (a : ℕ) {den : ℕ} (hden : 0 < den) : tcMemAmpIv (((den : ℝ) ^
    2 - (a : ℝ) ^ 2) / ((den : ℝ) ^ 2 + (a : ℝ) ^ 2)) (ltM1K2CosPairNat a den) := by
  have hsum_pos : 0 < den * den + a * a := Nat.add_pos_left (Nat.mul_pos hden hden) _
  have hadd : ((den * den + a * a : ℕ) : ℝ) = (den : ℝ) ^ 2 + (a : ℝ) ^ 2 := (by push_cast; ring)
  unfold ltM1K2CosPairNat
  simp only [ltM1K2_nat_mul_eq, ltM1K2_nat_add_eq, ltM1K2_nat_sub_eq, Nat.ble_eq]
  split_ifs with hle
  · have hsub : ((den * den - a * a : ℕ) : ℝ) = (den : ℝ) ^ 2 - (a : ℝ) ^ 2 := by
      rw [Nat.cast_sub hle]; push_cast; ring
    have hm := ltM1K2DivPairPos_mem (x0 := den * den - a * a) hsum_pos
    simp only [ltM1K2_nat_mul_eq] at hm; rwa [hsub, hadd] at hm
  · have hle' : den * den ≤ a * a := (by omega)
    have hsub : -(((a * a - den * den : ℕ) : ℝ) / ((den * den + a * a : ℕ) : ℝ)) =
        ((den : ℝ) ^ 2 - (a : ℝ) ^ 2) / ((den : ℝ) ^ 2 + (a : ℝ) ^ 2) := by
      rw [Nat.cast_sub hle', hadd]; push_cast; ring
    have hm := ltM1K2DivPairNeg_mem (x0 := a * a - den * den) hsum_pos
    simp only [ltM1K2_nat_mul_eq] at hm; rwa [hsub] at hm
/-- Pure-`Nat` constructor-matched `10^100`-scale Pythagorean `(cos, sin)` pair (`0`
  `Int.*`). -/
def ltM1K2PythagPair (num : ℤ) (den : ℕ) : TcIv × TcIv :=
  match num with
  | Int.ofNat a =>
      let sumSq := Nat.add (Nat.mul den den) (Nat.mul a a)
      let sNat := Nat.mul (Nat.mul (Nat.mul 2 a) den) ltM1K2AmpNat
      (ltM1K2CosPairNat a den, ltM1K2DivPairPos sNat sumSq)
  | Int.negSucc m =>
      let a := Nat.add m 1
      let sumSq := Nat.add (Nat.mul den den) (Nat.mul a a)
      let sNat := Nat.mul (Nat.mul (Nat.mul 2 a) den) ltM1K2AmpNat
      (ltM1K2CosPairNat a den, ltM1K2DivPairNeg sNat sumSq)
/-- Outward-rounded `10^100`-scale Pythagorean `(cos, sin)` CPS generator (`WHNF = 0`). -/
def ltM1K2IvPythag100 {α : Type*} (num : ℤ) (den : ℕ) (k : TcIv → TcIv → α) : α :=
  match ltM1K2PythagPair num den with
  | (cIv, sIv) =>
      tcWithForcedIv cIv fun cF ↦
        tcWithForcedIv sIv fun sF ↦
          k cF sF
private theorem ltM1K2IvPythag100_eq {α : Type*} (num : ℤ) (den : ℕ) (k : TcIv → TcIv → α) :
    ltM1K2IvPythag100 num den k = k (ltM1K2PythagPair num den).1 (ltM1K2PythagPair num den).2 := by
  unfold ltM1K2IvPythag100
  cases ltM1K2PythagPair num den with
  | mk cIv sIv => simp only [tcWithForcedIv_eq]
theorem ltM1K2_pythag100_sound (num : ℤ) {den : ℕ} (hden : 0 < den) :
    tcMemAmpIv (swLCayleyCos num den) (ltM1K2PythagPair num den).1 ∧
    tcMemAmpIv (swLCayleySin num den) (ltM1K2PythagPair num den).2 := by
  cases num with
  | ofNat a =>
      have hsum_pos : 0 < den * den + a * a := Nat.add_pos_left (Nat.mul_pos hden hden) _
      unfold ltM1K2PythagPair swLCayleyCos swLCayleySin
      simp only [Int.ofNat_eq_natCast, Int.cast_natCast]; refine ⟨ltM1K2CosPairNat_mem a hden, ?_⟩
      have hm := ltM1K2DivPairPos_mem (x0 := 2 * a * den) hsum_pos
      have hs : ((2 * a * den : ℕ) : ℝ) / ((den * den + a * a : ℕ) : ℝ) =
          (2 * (a : ℝ) * (den : ℝ)) / ((den : ℝ) ^ 2 + (a : ℝ) ^ 2) := by
        push_cast; ring
      simpa only [ltM1K2_nat_mul_eq, ltM1K2_nat_add_eq, hs] using hm
  | negSucc m =>
      set a : ℕ := m + 1
      have hsum_pos : 0 < den * den + a * a := Nat.add_pos_left (Nat.mul_pos hden hden) _
      have hcast : ((Int.negSucc m : ℤ) : ℝ) = -(a : ℝ) := (by simp [a, Int.negSucc_eq])
      have hsq : ((Int.negSucc m : ℤ) : ℝ) ^ 2 = (a : ℝ) ^ 2 := (by rw [hcast]; ring)
      unfold ltM1K2PythagPair swLCayleyCos swLCayleySin; simp only [ltM1K2_nat_add_eq]
      refine ⟨?_, ?_⟩
      · rw [hsq]; exact ltM1K2CosPairNat_mem (m + 1) hden
      · have hm := ltM1K2DivPairNeg_mem (x0 := 2 * a * den) hsum_pos
        have hs : -(((2 * a * den : ℕ) : ℝ) / ((den * den + a * a : ℕ) : ℝ)) = (2 * ((Int.negSucc m
          : ℤ) : ℝ) * (den : ℝ)) / ((den : ℝ) ^ 2 + ((Int.negSucc m : ℤ) : ℝ) ^ 2) := by
          rw [hcast]; push_cast; ring
        simpa only [ltM1K2_nat_mul_eq, ltM1K2_nat_add_eq, hs] using hm
/-- Build an `L = 2` `SwLPulseRat 2` from `(u0, v)` over common denominator `10^9`. -/
def ltM1K2MkPulse (uv : ℤ × ℤ) : SwLPulseRat 2 := ⟨fun _ ↦ uv.1, uv.2, 1000000000⟩
/-- Six-interval `10^100`-scale `(s0, s1, s2, s3, cum, surv)` state tuple. -/
abbrev LtM1K2State100 : Type := TcIv × TcIv × TcIv × TcIv × TcIv × TcIv
/-- One `10^100`-scale `L = 2` conveyor pulse with CPS-forced `TcIv` state components. -/
def ltM1K2PulseStep100 {α : Type*} (cs0 cs1 : TcIv × TcIv) (s0 s1 s2 s3 cum surv : TcIv) (uv : ℤ ×
    ℤ) (k : TcIv → TcIv → TcIv → TcIv → TcIv → TcIv → α) : α :=
  tcWithForcedIv (tcIvSub (tcIvMul cs0.1 s0) (tcIvMul cs0.2 s1)) fun na0 ↦
    tcWithForcedIv (tcIvAdd (tcIvMul cs0.2 s0) (tcIvMul cs0.1 s1)) fun na1 ↦
      tcWithForcedIv (tcIvSub (tcIvMul cs1.1 s2) (tcIvMul cs1.2 s3)) fun na2 ↦
        tcWithForcedIv (tcIvAdd (tcIvMul cs1.2 s2) (tcIvMul cs1.1 s3)) fun na3 ↦
          ltM1K2IvPythag100 uv.1 1000000000 fun cu su ↦
            ltM1K2IvPythag100 uv.2 1000000000 fun cv sv ↦
              tcWithForcedIv (tcIvSub (tcIvMul cu na1) (tcIvMul su na2)) fun nxt1 ↦
                tcWithForcedIv (tcIvAdd (tcIvMul su na1) (tcIvMul cu na2)) fun nxt2 ↦
                  tcWithForcedIv (tcIvMul cv na3) fun nxt3 ↦
                    tcWithForcedIv (tcIvAdd cum (tcIvSq (tcIvMul sv na3))) fun ncum ↦
                      tcWithForcedIv
                        (tcIvAdd surv (tcIvSub (tcAmpScale, tcAmpScale) cum)) fun nsurv ↦
                        k na0 nxt1 nxt2 nxt3 ncum nsurv
/-- Multi-pulse `10^100`-scale `L = 2` trajectory evolution from `(s0, s1, s2, s3, cum,
  surv)`. -/
def ltM1K2Evol100Aux (cs0 cs1 : TcIv × TcIv) :
    TcIv → TcIv → TcIv → TcIv → TcIv → TcIv → List (ℤ × ℤ) → LtM1K2State100
  | s0, s1, s2, s3, cum, surv, [] => (s0, s1, s2, s3, cum, surv)
  | s0, s1, s2, s3, cum, surv, uv :: ps =>
      ltM1K2PulseStep100 cs0 cs1 s0 s1 s2 s3 cum surv uv fun ns0 ns1 ns2 ns3 ncum nsurv ↦
        ltM1K2Evol100Aux cs0 cs1 ns0 ns1 ns2 ns3 ncum nsurv ps
/-- Tuple-curried `10^100`-scale `L = 2` trajectory evolution from checkpoint `st`. -/
def ltM1K2EvolFrom100 (csPair : (TcIv × TcIv) × (TcIv × TcIv))
    (st : LtM1K2State100) (ps : List (ℤ × ℤ)) : LtM1K2State100 :=
  ltM1K2Evol100Aux csPair.1 csPair.2 st.1 st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2.1 st.2.2.2.2.2 ps
private theorem ltM1K2Evol100Aux_append (cs0 cs1 : TcIv × TcIv) (ps qs : List (ℤ × ℤ)) (s0 s1 s2 s3
    cum surv : TcIv) : ltM1K2Evol100Aux cs0 cs1 s0 s1 s2 s3 cum surv (ps ++ qs) = ltM1K2EvolFrom100
    (cs0, cs1) (ltM1K2Evol100Aux cs0 cs1 s0 s1 s2 s3 cum surv ps) qs := by
  induction ps generalizing s0 s1 s2 s3 cum surv with
  | nil => rfl
  | cons uv rest ih =>
      simp only [List.cons_append, ltM1K2Evol100Aux]; unfold ltM1K2PulseStep100
      simp only [tcWithForcedIv_eq, ltM1K2IvPythag100_eq]; exact ih _ _ _ _ _ _
private theorem ltM1K2EvolFrom100_append (csPair : (TcIv × TcIv) × (TcIv × TcIv)) (st :
    LtM1K2State100) (ps qs : List (ℤ × ℤ)) : ltM1K2EvolFrom100 csPair st (ps ++ qs) =
    ltM1K2EvolFrom100 csPair (ltM1K2EvolFrom100 csPair st ps) qs := by
  rcases st with ⟨s0, s1, s2, s3, cum, surv⟩
  exact ltM1K2Evol100Aux_append csPair.1 csPair.2 ps qs s0 s1 s2 s3 cum surv
theorem ltM1K2PulseStep100_sound {cs : Fin 2 → ℝ × ℝ} {cs0 cs1 : TcIv × TcIv} (hcs0 : tcMemAmpIv (cs
    ⟨0, by decide⟩).1 cs0.1 ∧ tcMemAmpIv (cs ⟨0, by decide⟩).2 cs0.2) (hcs1 : tcMemAmpIv (cs ⟨1, by
    decide⟩).1 cs1.1 ∧ tcMemAmpIv (cs ⟨1, by decide⟩).2 cs1.2) {st : Fin 4 → ℝ} {s0 s1 s2 s3 cum
    surv : TcIv} {cumR survR : ℝ} (uv : ℤ × ℤ) (hst0 : tcMemAmpIv (st ⟨0, by decide⟩) s0) (hst1 :
    tcMemAmpIv (st ⟨1, by decide⟩) s1) (hst2 : tcMemAmpIv (st ⟨2, by decide⟩) s2) (hst3 : tcMemAmpIv
    (st ⟨3, by decide⟩) s3) (hcum : tcMemAmpIv cumR cum) (hsurv : tcMemAmpIv survR surv) :
    let outR := swLPulseStepReal 2 (by omega) cs st cumR survR (ltM1K2MkPulse uv)
    ltM1K2PulseStep100 cs0 cs1 s0 s1 s2 s3 cum surv uv fun ns0 ns1 ns2 ns3 ncum nsurv ↦ tcMemAmpIv
      (outR.1 ⟨0, by omega⟩) ns0 ∧ tcMemAmpIv (outR.1 ⟨1, by omega⟩) ns1 ∧ tcMemAmpIv (outR.1 ⟨2, by
      omega⟩) ns2 ∧ tcMemAmpIv (outR.1 ⟨3, by omega⟩) ns3 ∧ tcMemAmpIv outR.2.1 ncum ∧ tcMemAmpIv
      outR.2.2 nsurv := by
  intro outR; unfold ltM1K2PulseStep100; simp only [tcWithForcedIv_eq, ltM1K2IvPythag100_eq]
  rcases ltM1K2_pythag100_sound uv.1 (by omega : 0 < 1000000000) with ⟨hcu, hsu⟩
  rcases ltM1K2_pythag100_sound uv.2 (by omega : 0 < 1000000000) with ⟨hcv, hsv⟩
  have hna0 : tcMemAmpIv (swLGroverRotVec 2 cs st ⟨0, by omega⟩)
      (tcIvSub (tcIvMul cs0.1 s0) (tcIvMul cs0.2 s1)) := by
    change tcMemAmpIv ((cs ⟨0, by omega⟩).1 * st ⟨0, by omega⟩ - (cs ⟨0, by omega⟩).2 * st ⟨1, by
      omega⟩) _; exact tcMemAmpIv_sub (tcMemAmpIv_mul hcs0.1 hst0) (tcMemAmpIv_mul hcs0.2 hst1)
  have hna1 : tcMemAmpIv (swLGroverRotVec 2 cs st ⟨1, by omega⟩)
      (tcIvAdd (tcIvMul cs0.2 s0) (tcIvMul cs0.1 s1)) := by
    change tcMemAmpIv ((cs ⟨0, by omega⟩).2 * st ⟨0, by omega⟩ + (cs ⟨0, by omega⟩).1 * st ⟨1, by
      omega⟩) _; exact tcMemAmpIv_add (tcMemAmpIv_mul hcs0.2 hst0) (tcMemAmpIv_mul hcs0.1 hst1)
  have hna2 : tcMemAmpIv (swLGroverRotVec 2 cs st ⟨2, by omega⟩)
      (tcIvSub (tcIvMul cs1.1 s2) (tcIvMul cs1.2 s3)) := by
    change tcMemAmpIv ((cs ⟨1, by omega⟩).1 * st ⟨2, by omega⟩ - (cs ⟨1, by omega⟩).2 * st ⟨3, by
      omega⟩) _; exact tcMemAmpIv_sub (tcMemAmpIv_mul hcs1.1 hst2) (tcMemAmpIv_mul hcs1.2 hst3)
  have hna3 : tcMemAmpIv (swLGroverRotVec 2 cs st ⟨3, by omega⟩)
      (tcIvAdd (tcIvMul cs1.2 s2) (tcIvMul cs1.1 s3)) := by
    change tcMemAmpIv ((cs ⟨1, by omega⟩).2 * st ⟨2, by omega⟩ + (cs ⟨1, by omega⟩).1 * st ⟨3, by
      omega⟩) _; exact tcMemAmpIv_add (tcMemAmpIv_mul hcs1.2 hst2) (tcMemAmpIv_mul hcs1.1 hst3)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change tcMemAmpIv (swLGroverRotVec 2 cs st ⟨0, by omega⟩) _; exact hna0
  · change tcMemAmpIv (swLCayleyCos uv.1 1000000000 * swLGroverRotVec 2 cs st ⟨1, by omega⟩ -
      swLCayleySin uv.1 1000000000 * swLGroverRotVec 2 cs st ⟨2, by omega⟩) _
    exact tcMemAmpIv_sub (tcMemAmpIv_mul hcu hna1) (tcMemAmpIv_mul hsu hna2)
  · change tcMemAmpIv (swLCayleySin uv.1 1000000000 * swLGroverRotVec 2 cs st ⟨1, by omega⟩ +
      swLCayleyCos uv.1 1000000000 * swLGroverRotVec 2 cs st ⟨2, by omega⟩) _
    exact tcMemAmpIv_add (tcMemAmpIv_mul hsu hna1) (tcMemAmpIv_mul hcu hna2)
  · change tcMemAmpIv (swLCayleyCos uv.2 1000000000 * swLGroverRotVec 2 cs st ⟨3, by omega⟩) _
    exact tcMemAmpIv_mul hcv hna3
  · change tcMemAmpIv (cumR + (swLCayleySin uv.2 1000000000 * swLGroverRotVec 2 cs st ⟨3, by omega⟩)
      ^ 2) _; exact tcMemAmpIv_add hcum (tcMemAmpIv_sq (tcMemAmpIv_mul hsv hna3))
  · change tcMemAmpIv (survR + (1 - cumR)) _
    exact tcMemAmpIv_add hsurv (tcMemAmpIv_sub ltM1K2_tcMemAmpIv_one hcum)
theorem ltM1K2Evol100Aux_sound {cs : Fin 2 → ℝ × ℝ} {cs0 cs1 : TcIv × TcIv} (hcs0 : tcMemAmpIv (cs
    ⟨0, by decide⟩).1 cs0.1 ∧ tcMemAmpIv (cs ⟨0, by decide⟩).2 cs0.2) (hcs1 : tcMemAmpIv (cs ⟨1, by
    decide⟩).1 cs1.1 ∧ tcMemAmpIv (cs ⟨1, by decide⟩).2 cs1.2) (ps : List (ℤ × ℤ)) {st : Fin 4 → ℝ}
    {s0 s1 s2 s3 cum surv : TcIv} {cumR survR : ℝ} (hst0 : tcMemAmpIv (st ⟨0, by decide⟩) s0) (hst1
    : tcMemAmpIv (st ⟨1, by decide⟩) s1) (hst2 : tcMemAmpIv (st ⟨2, by decide⟩) s2) (hst3 :
    tcMemAmpIv (st ⟨3, by decide⟩) s3) (hcum : tcMemAmpIv cumR cum) (hsurv : tcMemAmpIv survR surv)
    :
    let outR := swLEvolutionRealAux 2 (by omega) cs st cumR survR (ps.map ltM1K2MkPulse)
    let outIv := ltM1K2Evol100Aux cs0 cs1 s0 s1 s2 s3 cum surv ps
    tcMemAmpIv (outR.1 ⟨0, by omega⟩) outIv.1 ∧ tcMemAmpIv (outR.1 ⟨1, by omega⟩) outIv.2.1 ∧
      tcMemAmpIv (outR.1 ⟨2, by omega⟩) outIv.2.2.1 ∧ tcMemAmpIv (outR.1 ⟨3, by omega⟩)
      outIv.2.2.2.1 ∧ tcMemAmpIv outR.2.1 outIv.2.2.2.2.1 ∧ tcMemAmpIv outR.2.2
      outIv.2.2.2.2.2 := by
  induction ps generalizing st s0 s1 s2 s3 cum surv cumR survR with
  | nil => exact ⟨hst0, hst1, hst2, hst3, hcum, hsurv⟩
  | cons uv rest ih =>
      simp only [List.map_cons, swLEvolutionRealAux, ltM1K2Evol100Aux]
      have hstep := ltM1K2PulseStep100_sound hcs0 hcs1 uv hst0 hst1 hst2 hst3 hcum hsurv
      unfold ltM1K2PulseStep100 at hstep ⊢
      simp only [tcWithForcedIv_eq, ltM1K2IvPythag100_eq] at hstep ⊢
      rcases hstep with ⟨h0, h1, h2, h3, hc, hs⟩; exact ih h0 h1 h2 h3 hc hs
theorem ltM1K2_arcsin_bounds {x : ℝ} (hx0 : 0 < x) (hx_ub : x ≤ 1 / 199000000000000) : 0 <
    Real.arcsin x ∧ Real.arcsin x ≤ 1 / 190000000000000 ∧ x ≤ Real.arcsin x ∧ (1 - 1 /
    100000000000000000000) * Real.arcsin x ≤ x := by
  have hx1 : x ≤ 1 := (by linarith)
  have hsin_x : Real.sin (Real.arcsin x) = x := Real.sin_arcsin (by linarith) hx1
  have hα_pos : 0 < Real.arcsin x := Real.arcsin_pos.2 hx0
  have hα_lb : x ≤ Real.arcsin x := self_le_arcsin hx0.le hx1; set u : ℝ := 1 / 190000000000000
  have hu_pos : 0 < u := (by dsimp [u]; norm_num)
  have hx_le_sinu : x ≤ Real.sin u := by
    have hcube := (Real.sin_gt_sub_cube hu_pos).le
    have hnum : (1 : ℝ) / 199000000000000 ≤ u - u ^ 3 / 6 := (by dsimp [u]; norm_num); linarith
  have hα_le : Real.arcsin x ≤ u := by
    have h1 := Real.arcsin_le_arcsin hx_le_sinu
    have h2 : Real.arcsin (Real.sin u) = u :=
      Real.arcsin_sin (by dsimp [u]; linarith [Real.pi_gt_three])
        (by dsimp [u]; linarith [Real.pi_gt_three])
    linarith
  have hα_ub : (1 - 1 / 100000000000000000000) * Real.arcsin x ≤ x := by
    have hcube := (Real.sin_gt_sub_cube hα_pos).le; rw [hsin_x] at hcube
    have hsq : (Real.arcsin x) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hα_pos.le hα_le 2
    have hu_sq : u ^ 2 / 6 ≤ 1 / 100000000000000000000 := (by dsimp [u]; norm_num)
    have hmul : (Real.arcsin x) ^ 3 / 6 ≤ (1 / 100000000000000000000) * Real.arcsin x := by
      have h1 : (Real.arcsin x) ^ 3 / 6 = ((Real.arcsin x) ^ 2 / 6) * Real.arcsin x := (by ring)
      rw [h1]; exact mul_le_mul_of_nonneg_right
        ((div_le_div_of_nonneg_right hsq (by norm_num)).trans hu_sq) hα_pos.le
    linarith
  exact ⟨hα_pos, hα_le, hα_lb, hα_ub⟩
/-- `10^100`-scale `(cos, sin)` intervals for planes `w = 0, 1` at `r = 2`, `n >= 96`. -/
def ltM1K2TrigPair100 : (TcIv × TcIv) × (TcIv × TcIv) :=
  (tcTrigIv100 (Int.ofNat 5000000) (Int.ofNat 1000000000)
     (Int.ofNat 250000000001000000000) (Int.ofNat 50000000000000000000000),
   tcTrigIv100 (Int.ofNat 353553390593265000000) (Int.ofNat 100000000000000000000000)
     (Int.ofNat 17677669529734960678118657000000000)
     (Int.ofNat 5000000000000000000000000000000000000))
theorem ltM1K2_yHi0_le : -((-(((250000000001000000000 : ℤ)) * tcAmpScale)) / (((2 : ℤ) ^
    tcTrigHalvings) * ((50000000000000000000000 : ℤ)))) ≤ tcAmpScale := by
  exact (bleZ_eq_true_iff _ _).mp rfl
theorem ltM1K2_yHi1_le : -((-(((17677669529734960678118657000000000 : ℤ)) * tcAmpScale)) / (((2 : ℤ)
    ^ tcTrigHalvings) * ((5000000000000000000000000000000000000 : ℤ)))) ≤ tcAmpScale := by
  exact (bleZ_eq_true_iff _ _).mp rfl
theorem ltM1K2TrigPair100_sound {n : ℕ} (hn96 : 96 ≤ n) :
    let K_blk := swLKBlk n 2 5000000 1000000000; let N : ℕ := 2 ^ n
    let cs : Fin 2 → ℝ × ℝ := fun w ↦
      (Real.cos ((K_blk : ℝ) * swLThetaShiftReal N 2 w.1),
       Real.sin ((K_blk : ℝ) * swLThetaShiftReal N 2 w.1))
    (tcMemAmpIv (cs ⟨0, by omega⟩).1 ltM1K2TrigPair100.1.1 ∧ tcMemAmpIv (cs ⟨0, by omega⟩).2
      ltM1K2TrigPair100.1.2) ∧ (tcMemAmpIv (cs ⟨1, by omega⟩).1 ltM1K2TrigPair100.2.1 ∧ tcMemAmpIv
      (cs ⟨1, by omega⟩).2 ltM1K2TrigPair100.2.2) := by
  intro K_blk N cs; unfold ltM1K2TrigPair100; simp only [tcInt_ofNat_eq, Nat.cast_ofNat]
  have hN96 : (79228162514264337593543950336 : ℝ) ≤ (N : ℝ) := by
    have hpow : 2 ^ 96 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn96
    have hpow_r : ((2 ^ 96 : ℕ) : ℝ) ≤ (N : ℝ) := (by dsimp [N]; exact_mod_cast hpow)
    have hval : ((2 ^ 96 : ℕ) : ℝ) = 79228162514264337593543950336 := (by norm_num); linarith
  have hN_pos : (0 : ℝ) < (N : ℝ) := (by linarith); set c₁ : ℝ := (N : ℝ) / (2 : ℕ)
  have hc1_ge : (199000000000000 : ℝ) ^ 2 ≤ c₁ := by
    dsimp [c₁]; norm_num; linarith
  have hsqrt_c1_ge : (199000000000000 : ℝ) ≤ √c₁ := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 199000000000000)]; exact Real.sqrt_le_sqrt hc1_ge
  have hx0_pos : 0 < 1 / √c₁ := (by positivity)
  have hx0_ub : 1 / √c₁ ≤ 1 / 199000000000000 := one_div_le_one_div_of_le (by norm_num) hsqrt_c1_ge
  rcases ltM1K2_arcsin_bounds hx0_pos hx0_ub with ⟨hα_pos, hα_le, hα_lb, hα_ub⟩
  set α₀ : ℝ := Real.arcsin (1 / √c₁); set tauR : ℝ := (5000000 : ℝ) / (1000000000 : ℝ)
  have htau_nn : 0 ≤ tauR := (by dsimp [tauR]; norm_num)
  have hK_eq : K_blk = (round (tauR / (2 * α₀))).toNat + 1 := by
    simp only [K_blk, swLKBlk, tauR, α₀, c₁, N, Nat.cast_pow, Nat.cast_ofNat]
  rcases odd_round_div_sub_mem_Icc hα_pos htau_nn with ⟨hodd_lo, hodd_hi⟩
  have hφ0_lo : tauR ≤ 2 * (K_blk : ℝ) * α₀ := (by rw [hK_eq, Nat.cast_add, Nat.cast_one]; linarith)
  have hφ0_hi : 2 * (K_blk : ℝ) * α₀ ≤ tauR + 3 * α₀ := by
    rw [hK_eq, Nat.cast_add, Nat.cast_one]; linarith
  have hφ0_hi_q1 : 2 * (K_blk : ℝ) * α₀ ≤
      ((250000000001000000000 : ℤ) : ℝ) / ((50000000000000000000000 : ℤ) : ℝ) := by
    have hq1 : ((250000000001000000000 : ℤ) : ℝ) / ((50000000000000000000000 : ℤ) : ℝ) =
        tauR + 1 / (50000000000000 : ℝ) := by
      dsimp [tauR]; norm_num
    rw [hq1]
    have hnum : (3 : ℝ) * (1 / 190000000000000) ≤ 1 / (50000000000000 : ℝ) := (by norm_num)
    have h3α : 3 * α₀ ≤ 1 / (50000000000000 : ℝ) := le_trans (mul_le_mul_of_nonneg_left hα_le (by
      norm_num)) hnum; exact le_trans hφ0_hi (add_le_add (le_refl tauR) h3α)
  have hθ0_eq : swLThetaShiftReal N 2 0 = 2 * α₀ := by
    unfold swLThetaShiftReal; simp only [Nat.cast_zero, mul_zero, sub_zero, Nat.cast_ofNat, α₀, c₁]
    congr 2; rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_div hN_pos.le, one_div_div]
  have hφ0_eq : (K_blk : ℝ) * swLThetaShiftReal N 2 0 = 2 * (K_blk : ℝ) * α₀ := by rw [hθ0_eq]; ring
  constructor
  · dsimp only [cs]; rw [hφ0_eq]; exact tcTrigIv100_sound (a := 5000000) (d := 1000000000)
      (b := 250000000001000000000) (e := 50000000000000000000000)
      (by norm_num) (by norm_num) (by norm_num)
      (by simpa [tauR] using hφ0_lo) hφ0_hi_q1 ltM1K2_yHi0_le
  · have hN2_pos : (0 : ℝ) < (N : ℝ) - 2 := (by linarith); set x1 : ℝ := √(1 / ((N : ℝ) - 2))
    have hx1_pos : 0 < x1 := Real.sqrt_pos.2 (div_pos one_pos hN2_pos)
    have hx1_sq : x1 ^ 2 = 1 / ((N : ℝ) - 2) := Real.sq_sqrt (div_nonneg zero_le_one hN2_pos.le)
    have hx1_ub : x1 ≤ 1 / 199000000000000 := by
      have hsq : x1 ^ 2 ≤ (1 / 199000000000000 : ℝ) ^ 2 := by
        rw [hx1_sq, div_le_iff₀ hN2_pos]; linarith
      rw [← Real.sqrt_sq hx1_pos.le, ← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 199000000000000)]
      exact Real.sqrt_le_sqrt hsq
    rcases ltM1K2_arcsin_bounds hx1_pos hx1_ub with ⟨_, _, hβ_lb, hβ_ub⟩
    set β : ℝ := Real.arcsin x1
    have hθ1_eq : swLThetaShiftReal N 2 1 = 2 * β := by
      unfold swLThetaShiftReal; dsimp only [β, x1]; norm_num
    have hx0_sq : (1 / √c₁) ^ 2 = 2 / (N : ℝ) := by
      dsimp [c₁]; rw [div_pow, one_pow, Real.sq_sqrt (by positivity), one_div_div]
    have hlo_sq : ((70710678118654 : ℝ) / (100000000000000 : ℝ)) ^ 2 * (1 / √c₁) ^ 2 ≤ x1 ^ 2 := by
      rw [hx0_sq, hx1_sq]; have h1 :
          ((70710678118654 : ℝ) / (100000000000000 : ℝ)) ^ 2 * (2 / (N : ℝ)) ≤ 1 / (N : ℝ) := by
        have hnum : ((70710678118654 : ℝ) / (100000000000000 : ℝ)) ^ 2 * 2 ≤ 1 := (by norm_num)
        rw [mul_div_assoc', div_le_div_iff₀ hN_pos hN_pos]; nlinarith
      have h2 : 1 / (N : ℝ) ≤ 1 / ((N : ℝ) - 2) := one_div_le_one_div_of_le hN2_pos (by linarith)
      exact h1.trans h2
    have hxk_ge : ((70710678118654 : ℝ) / (100000000000000 : ℝ)) * (1 / √c₁) ≤ x1 := by
      have hnn : (0 : ℝ) ≤
          ((70710678118654 : ℝ) / (100000000000000 : ℝ)) * (1 / √c₁) := by positivity
      rw [← Real.sqrt_sq hnn, ← Real.sqrt_sq hx1_pos.le]; exact Real.sqrt_le_sqrt (by rwa [mul_pow])
    have hβ_ge : ((70710678118653 : ℝ) / (100000000000000 : ℝ)) * α₀ ≤ β := by
      have hrat : ((70710678118653 : ℝ) / (100000000000000 : ℝ)) ≤
          ((70710678118654 : ℝ) / (100000000000000 : ℝ)) *
            (1 - 1 / 100000000000000000000) := by norm_num
      have h1 : ((70710678118653 : ℝ) / (100000000000000 : ℝ)) * α₀ ≤ ((70710678118654 : ℝ) /
        (100000000000000 : ℝ)) * ((1 - 1 / 100000000000000000000) * α₀) := by
        rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hrat hα_pos.le
      have h2 : ((70710678118654 : ℝ) / (100000000000000 : ℝ)) * ((1 - 1 / 100000000000000000000) *
        α₀) ≤ ((70710678118654 : ℝ) / (100000000000000 : ℝ)) * (1 / √c₁) :=
        mul_le_mul_of_nonneg_left hα_ub (by norm_num)
      exact ((h1.trans h2).trans hxk_ge).trans hβ_lb
    have hhi_sq : x1 ^ 2 ≤ ((70710678118656 : ℝ) / (100000000000000 : ℝ)) ^ 2 * (1 / √c₁) ^ 2 := by
      rw [hx0_sq, hx1_sq]; rw [mul_div_assoc', div_le_div_iff₀ hN2_pos hN_pos]; nlinarith
    have hxk_le : x1 ≤ ((70710678118656 : ℝ) / (100000000000000 : ℝ)) * (1 / √c₁) := by
      have hnn : (0 : ℝ) ≤
          ((70710678118656 : ℝ) / (100000000000000 : ℝ)) * (1 / √c₁) := by positivity
      rw [← Real.sqrt_sq hx1_pos.le, ← Real.sqrt_sq hnn]; exact Real.sqrt_le_sqrt (by rwa [mul_pow])
    have hβ_le : β ≤ ((70710678118657 : ℝ) / (100000000000000 : ℝ)) * α₀ := by
      have h1 : x1 ≤ ((70710678118656 : ℝ) / (100000000000000 : ℝ)) * α₀ :=
        hxk_le.trans (mul_le_mul_of_nonneg_left hα_lb (by norm_num))
      have hrat : ((70710678118656 : ℝ) / (100000000000000 : ℝ)) ≤
          (1 - 1 / 100000000000000000000) *
            ((70710678118657 : ℝ) / (100000000000000 : ℝ)) := by norm_num
      have h2 : ((70710678118656 : ℝ) / (100000000000000 : ℝ)) * α₀ ≤ (1 - 1 /
        100000000000000000000) * (((70710678118657 : ℝ) / (100000000000000 : ℝ)) * α₀) := by
        rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hrat hα_pos.le
      exact le_of_mul_le_mul_left ((hβ_ub.trans h1).trans h2) (by norm_num)
    have hφ1_lo : (((353553390593265000000 : ℤ) : ℝ) / ((100000000000000000000000 : ℤ) : ℝ)) ≤
        (K_blk : ℝ) * swLThetaShiftReal N 2 1 := by
      rw [hθ1_eq]
      have hm1 : (K_blk : ℝ) * (((70710678118653 : ℝ) / (100000000000000 : ℝ)) * (2 * α₀)) ≤ (K_blk
        : ℝ) * (2 * β) := mul_le_mul_of_nonneg_left (by linarith [hβ_ge]) (Nat.cast_nonneg K_blk)
      have hm2 : ((70710678118653 : ℝ) / (100000000000000 : ℝ)) * tauR ≤
          ((70710678118653 : ℝ) / (100000000000000 : ℝ)) * (2 * (K_blk : ℝ) * α₀) :=
        mul_le_mul_of_nonneg_left hφ0_lo (by norm_num)
      have hval : (((353553390593265000000 : ℤ) : ℝ) / ((100000000000000000000000 : ℤ) : ℝ)) =
          ((70710678118653 : ℝ) / (100000000000000 : ℝ)) * tauR := by
        dsimp [tauR]; norm_num
      linarith
    have hφ1_hi : (K_blk : ℝ) * swLThetaShiftReal N 2 1 ≤ (((17677669529734960678118657000000000 :
      ℤ) : ℝ) / ((5000000000000000000000000000000000000 : ℤ) : ℝ)) := by
      rw [hθ1_eq]
      have hm1 : (K_blk : ℝ) * (2 * β) ≤ (K_blk : ℝ) * (((70710678118657 : ℝ) / (100000000000000 :
        ℝ)) * (2 * α₀)) := mul_le_mul_of_nonneg_left (by linarith [hβ_le]) (Nat.cast_nonneg K_blk)
      have hm2 : ((70710678118657 : ℝ) / (100000000000000 : ℝ)) * (2 * (K_blk : ℝ) * α₀) ≤
        ((70710678118657 : ℝ) / (100000000000000 : ℝ)) * (((250000000001000000000 : ℤ) : ℝ) /
        ((50000000000000000000000 : ℤ) : ℝ)) := mul_le_mul_of_nonneg_left hφ0_hi_q1 (by norm_num)
      have hval : (((17677669529734960678118657000000000 : ℤ) : ℝ) /
            ((5000000000000000000000000000000000000 : ℤ) : ℝ)) =
          ((70710678118657 : ℝ) / (100000000000000 : ℝ)) *
            (((250000000001000000000 : ℤ) : ℝ) / ((50000000000000000000000 : ℤ) : ℝ)) := by
        norm_num
      linarith
    dsimp only [cs]
    exact tcTrigIv100_sound (a := 353553390593265000000) (d := 100000000000000000000000)
      (b := 17677669529734960678118657000000000) (e := 5000000000000000000000000000000000000)
      (by norm_num) (by norm_num) (by norm_num) hφ1_lo hφ1_hi ltM1K2_yHi1_le
/-- Pulse chunk 0 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk0 : List (ℤ × ℤ) := [
  (4013615, 0), (4013743, 0), (4013907, 0), (4014098, 0), (4014103, 0), (4014062, 0), (4013959, 0),
  (4013842, 0), (4013599, 0), (4013268, 0), (4012813, 0), (4012307, 0), (4011752, 0), (4011071, 0),
  (4010269, 0), (4009390, 0), (4008416, 0), (4007376, 0), (4006265, 0), (4005064, 0), (4003752, 0),
  (4002373, 0), (4000908, 0), (3999384, 0), (3997807, 0), (3996185, 0), (3994506, 0), (3992782, 0),
  (3991021, 0), (3989210, 0), (3987382, 0), (3985538, 0), (3983679, 0), (3981814, 0), (3979952, 0),
  (3978070, 0), (3976191, 0), (3974315, 0), (3972427, 0), (3970544, 0), (3968657, 0), (3966767, 0),
  (3964868, 0), (3962959, 0), (3961035, 0), (3959091, 0), (3957131, 0), (3955141, 0), (3953121, 0),
  (3951070, 0), (3948977, 0), (3946840, 0), (3944651, 0), (3942407, 0), (3940099, 0), (3937727, 0),
  (3935287, 0), (3932768, 0), (3930178, 0), (3927513, 0), (3924755, 0), (3921921, 0), (3919015, 0),
  (3915997, 0), (3912908, 0), (3909761, 0), (3906481, 0), (3903145, 0), (3899762, 0), (3896249, 0),
  (3892689, 0), (3889088, 0), (3885379, 0), (3881627, 0), (3877837, 0), (3873971, 0), (3870067, 0),
  (3866131, 0), (3862151, 0), (3858147, 0), (3854121, 0), (3850077, 0), (3846028, 0), (3841968, 0),
  (3837909, 0), (3833860, 0), (3829810, 0), (3825771, 0), (3821748, 0), (3817730, 0) ]
/-- Pulse chunk 1 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk1 : List (ℤ × ℤ) := [
  (3813724, 0), (3809729, 0), (3805737, 0), (3801754, 0), (3797761, 0), (3793766, 0), (3789769, 0),
  (3785735, 0), (3781688, 0), (3777625, 0), (3773499, 0), (3769344, 0), (3765155, 0), (3760891, 0),
  (3756581, 0), (3752219, 0), (3747780, 0), (3743281, 0), (3738715, 0), (3734077, 0), (3729373, 0),
  (3724593, 0), (3719748, 0), (3714839, 0), (3709855, 0), (3704814, 0), (3699715, 0), (3694555, 0),
  (3689349, 0), (3684093, 0), (3678796, 0), (3673469, 0), (3668095, 0), (3662706, 0), (3657304, 0),
  (3651853, 0), (3646409, 0), (3640969, 0), (3635481, 0), (3630011, 0), (3624554, 0), (3619060, 0),
  (3613588, 0), (3608124, 0), (3602649, 0), (3597189, 0), (3591730, 0), (3586282, 0), (3580843, 0),
  (3575398, 0), (3569975, 0), (3564557, 0), (3559127, 0), (3553715, 0), (3548302, 0), (3542875, 0),
  (3537452, 0), (3532017, 0), (3526566, 0), (3521103, 0), (3515610, 0), (3510101, 0), (3504567, 0),
  (3498980, 0), (3493377, 0), (3487743, 0), (3482035, 0), (3476311, 0), (3470553, 0), (3464713, 0),
  (3458855, 0), (3452961, 0), (3446994, 0), (3441005, 0), (3434973, 0), (3428901, 0), (3422800, 0),
  (3416650, 0), (3410496, 0), (3404311, 0), (3398080, 0), (3391868, 0), (3385632, 0), (3379362, 0),
  (3373116, 0), (3366859, 0), (3360584, 0), (3354330, 0), (3348072, 0), (3341817, 0) ]
/-- Pulse chunk 2 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk2 : List (ℤ × ℤ) := [
  (3335574, 0), (3329328, 0), (3323104, 0), (3316889, 0), (3310665, 0), (3304475, 0), (3298298, 0),
  (3292104, 0), (3285951, 0), (3279812, 0), (3273660, 0), (3267543, 0), (3261439, 0), (3255335, 0),
  (3249254, 0), (3243173, 0), (3237113, 0), (3231057, 0), (3224985, 0), (3218947, 0), (3212894, 0),
  (3206818, 0), (3200764, 0), (3194685, 0), (3188580, 0), (3182474, 0), (3176338, 0), (3170179, 0),
  (3163997, 0), (3157782, 0), (3151550, 0), (3145285, 0), (3138987, 0), (3132682, 0), (3126347, 0),
  (3119987, 0), (3113628, 0), (3107253, 0), (3100870, 0), (3094495, 0), (3088119, 0), (3081760, 0),
  (3075413, 0), (3069076, 0), (3062783, 0), (3056502, 0), (3050237, 0), (3044032, 0), (3037838, 0),
  (3031661, 0), (3025543, 0), (3019435, 0), (3013345, 0), (3007292, 0), (3001249, 0), (2995223, 0),
  (2989206, 0), (2983194, 0), (2977195, 0), (2971186, 0), (2965174, 0), (2959167, 0), (2953141, 0),
  (2947107, 0), (2941071, 0), (2935017, 0), (2928955, 0), (2922886, 0), (2916807, 0), (2910725, 0),
  (2904635, 0), (2898541, 0), (2892456, 0), (2886363, 0), (2880270, 0), (2874194, 0), (2868113, 0),
  (2862036, 0), (2855973, 0), (2849908, 0), (2843853, 0), (2837798, 0), (2831747, 0), (2825713, 0),
  (2819660, 0), (2813617, 0), (2807593, 0), (2801541, 0), (2795503, 0), (2789481, 0) ]
/-- Pulse chunk 3 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk3 : List (ℤ × ℤ) := [
  (2783440, 0), (2777412, 0), (2771397, 0), (2765380, 0), (2759383, 0), (2753391, 0), (2747422, 0),
  (2741484, 0), (2735550, 0), (2729655, 0), (2723812, 0), (2717974, 0), (2712184, 0), (2706464, 0),
  (2700756, 0), (2695100, 0), (2689515, 0), (2683954, 0), (2678443, 0), (2672986, 0), (2667559, 0),
  (2662182, 0), (2656821, 0), (2651493, 0), (2646209, 0), (2640897, 0), (2635615, 0), (2630360, 0),
  (2625053, 0), (2619758, 0), (2614463, 0), (2609117, 0), (2603761, 0), (2598378, 0), (2592957, 0),
  (2587512, 0), (2582020, 0), (2576507, 0), (2570971, 0), (2565382, 0), (2559787, 0), (2554185, 0),
  (2548540, 0), (2542905, 0), (2537283, 0), (2531643, 0), (2526029, 0), (2520444, 0), (2514877, 0),
  (2509356, 0), (2503864, 0), (2498427, 0), (2493063, 0), (2487716, 0), (2482456, 0), (2477290, 0),
  (2472131, 0), (2467077, 0), (2462125, 0), (2457180, 0), (2452340, 0), (2447576, 0), (2442851, 0),
  (2438202, 0), (2433590, 0), (2429044, 0), (2424546, 0), (2420048, 0), (2415627, 0), (2411237, 0),
  (2406824, 0), (2402477, 0), (2398156, 0), (2393802, 0), (2389489, 0), (2385192, 0), (2380861, 0),
  (2376544, 0), (2372224, 0), (2367874, 0), (2363521, 0), (2359132, 0), (2354730, 0), (2350326, 0),
  (2345847, 0), (2341377, 0), (2336914, 0), (2332348, 0), (2327808, 0), (2323278, 0) ]
/-- Pulse chunk 4 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk4 : List (ℤ × ℤ) := [
  (2318656, 0), (2314066, 0), (2309481, 0), (2304859, 0), (2300268, 0), (2295676, 0), (2291117, 0),
  (2286593, 0), (2282062, 0), (2277626, 0), (2273240, 0), (2268851, 0), (2264593, 0), (2260400, 0),
  (2256224, 0), (2252165, 0), (2248176, 0), (2244217, 0), (2240343, 0), (2236527, 0), (2232752, 0),
  (2229044, 0), (2225354, 0), (2221715, 0), (2218116, 0), (2214466, 0), (2210871, 0), (2207288, 0),
  (2203656, 0), (2200075, 0), (2196520, 0), (2192930, 0), (2189374, 0), (2185818, 0), (2182264, 0),
  (2178762, 0), (2175259, 0), (2171915, 0), (2168589, 0), (2165270, 0), (2162008, 0), (2158755, 0),
  (2155451, 0), (2152214, 0), (2148844, 0), (2145289, 0), (2141560, 0), (2137770, 0), (2133881,
  989), (2129933, 5737), (2125775, 19801), (2121949, -48126), (2118953, -367043), (2116942,
  -981770), (2116473, -222479), (2117363, 3922577), (2032477, 16360762), (1871247, 30494674),
  (1615203, 44442842), (1424561, 52176638), (1298089, 56816535), (1256536, 58128907), (1269733,
  57599248), (1289888, 56815638), (1313001, 55909893), (1326037, 55350131), (1333217, 55002871),
  (1334583, 54867878), (1327918, 55035992), (1318985, 55286778), (1307988, 55612582), (1296389,
  55963326), (1285647, 56281058), (1275770, 56566031), (1268230, 56766207), (1262362, 56904102),
  (1257855, 56992395), (1255354, 57007370), (1253933, 56982473), (1253247, 56931939), (1253227,
  56855698), (1253284, 56774764), (1253349, 56695159), (1253033, 56626690), (1252183, 56575788),
  (1251015, 56537849), (1249241, 56520182), (1246837, 56525150), (1244099, 56542661), (1240906,
  56576021) ]
/-- Pulse chunk 5 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk5 : List (ℤ × ℤ) := [
  (1237314, 56624576), (1233540, 56679260), (1229563, 56740676), (1225561, 56805412), (1221561,
  56869280), (1217573, 56931873), (1213874, 56988595), (1210273, 57040524), (1206782, 57087516),
  (1203729, 57123649), (1200792, 57153870), (1198006, 57178294), (1195579, 57192138), (1193254,
  57201064), (1191070, 57205479), (1189055, 57203050), (1187107, 57197558), (1185257, 57189635),
  (1183410, 57178965), (1181560, 57167670), (1179755, 57156103), (1177846, 57145123), (1175869,
  57135617), (1173897, 57127330), (1171788, 57121486), (1169583, 57118378), (1167359, 57117112),
  (1165023, 57118753), (1162616, 57123257), (1160177, 57129619), (1157659, 57138810), (1155123,
  57150803), (1152551, 57164038), (1149950, 57178769), (1147413, 57195100), (1144841, 57211971),
  (1142258, 57229482), (1139797, 57247575), (1137301, 57265661), (1134800, 57283761), (1132437,
  57301432), (1130051, 57318469), (1127674, 57334890), (1125415, 57349435), (1123141, 57363227),
  (1120896, 57376291), (1118676, 57387676), (1116466, 57397985), (1114307, 57407339), (1112118,
  57414917), (1109943, 57421464), (1107828, 57427199), (1105654, 57431613), (1103486, 57435330),
  (1101377, 57438535), (1099220, 57440851), (1097065, 57442686), (1094959, 57444265), (1092827,
  57445540), (1090704, 57446660), (1088612, 57447749), (1086518, 57448849), (1084456, 57450156),
  (1082400, 57451659), (1080350, 57453469), (1078360, 57455847), (1076354, 57458584), (1074350,
  57461787), (1072437, 57465502), (1070493, 57469639), (1068540, 57474316), (1066675, 57479883),
  (1064774, 57485868), (1062860, 57492292), (1061014, 57499513), (1059137, 57507069), (1057257,
  57514964), (1055395, 57523506), (1053516, 57532316), (1051649, 57541388), (1049752, 57550896),
  (1047850, 57560585), (1045972, 57570432), (1044040, 57580487), (1042107, 57590606), (1040200,
  57600772), (1038245, 57610933), (1036285, 57621020), (1034350, 57631050), (1032385, 57640907) ]
/-- Pulse chunk 6 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk6 : List (ℤ × ℤ) := [
  (1030416, 57650550), (1028466, 57660058), (1026502, 57669298), (1024543, 57678233), (1022592,
  57687006), (1020642, 57695513), (1018706, 57703742), (1016769, 57711801), (1014835, 57719572),
  (1012938, 57726866), (1011032, 57733897), (1009129, 57740565), (1007282, 57746512), (1005423,
  57752188), (1003565, 57757564), (1001741, 57763195), (999906, 57768611), (998075, 57773750),
  (996289, 57778291), (994500, 57782625), (992722, 57786749), (990964, 57790505), (989209,
  57794230), (987469, 57797918), (985730, 57801438), (983999, 57804891), (982286, 57808301),
  (980567, 57811699), (978849, 57815351), (977143, 57819085), (975437, 57822551), (973736,
  57825889), (972043, 57829155), (970345, 57832398), (968648, 57835723), (966945, 57839172),
  (965231, 57842940), (963515, 57846876), (961785, 57850888), (960045, 57855015), (958303,
  57859390), (956540, 57863911), (954762, 57868646), (952990, 57873411), (951199, 57878195),
  (949398, 57883033), (947591, 57888220), (945768, 57893571), (943937, 57899109), (942095,
  57905082), (940245, 57911152), (938399, 57917315), (936542, 57923575), (934690, 57929899),
  (932854, 57936289), (931002, 57942910), (929162, 57949642), (927342, 57956470), (925510,
  57963503), (923692, 57970636), (921897, 57977843), (920101, 57985191), (918321, 57992594),
  (916563, 58000017), (914813, 58007453), (913082, 58014820), (911364, 58022143), (909658,
  58029431), (907966, 58036905), (906275, 58044475), (904592, 58052142), (902933, 58059787),
  (901268, 58067324), (899611, 58074640), (897981, 58081793), (896336, 58088919), (894687,
  58096039), (893066, 58103122), (891427, 58110193), (889780, 58117243), (888155, 58124155),
  (886516, 58130995), (884873, 58137758), (883246, 58144299), (881610, 58150748), (879980,
  58157107), (878346, 58163215), (876715, 58169211), (875101, 58175107), (873473, 58180748) ]
/-- Pulse chunk 7 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk7 : List (ℤ × ℤ) := [
  (871853, 58186258), (870259, 58191663), (868647, 58196832), (867046, 58201863), (865475,
  58206803), (863889, 58211556), (862310, 58216206), (860758, 58220799), (859197, 58225269),
  (857641, 58229620), (856109, 58233887), (854576, 58237973), (853056, 58241603), (851552,
  58245037), (850053, 58248273), (848559, 58251502), (847069, 58254733), (845577, 58257939),
  (844103, 58261065), (842623, 58264152), (841138, 58267182), (839685, 58270025), (838221,
  58272742), (836749, 58275309), (835324, 58277574), (833885, 58279672), (832432, 58281595),
  (831029, 58283495), (829605, 58285608), (828165, 58287913), (826768, 58290272), (825366,
  58292549), (823963, 58294732), (822601, 58296642), (821249, 58298269), (819905, 58299775),
  (818576, 58301706), (817253, 58303851), (815942, 58306123), (814647, 58308532), (813364,
  58310925), (812104, 58313227), (810863, 58315302), (809631, 58317357), (808422, 58319416),
  (807225, 58321555), (806039, 58323760), (804872, 58325995), (803705, 58328299), (802531,
  58331202), (801372, 58334275), (800215, 58337480), (799055, 58340680), (797909, 58343842),
  (796767, 58346971), (795610, 58350114), (794456, 58353283), (793298, 58356492), (792125,
  58360023), (790953, 58363661), (789775, 58367404), (788574, 58371373), (787366, 58375419),
  (786145, 58379536), (784907, 58383820), (783657, 58388171), (782393, 58392575), (781126,
  58397112), (779846, 58401726), (778551, 58406396), (777244, 58411198), (775927, 58416109),
  (774599, 58421100), (773264, 58426253), (771919, 58431576), (770566, 58436977), (769210,
  58442448), (767851, 58447847), (766489, 58453154), (765126, 58458302), (763763, 58463389),
  (762401, 58468527), (761038, 58473809), (759678, 58479364), (758315, 58485093), (756944,
  58491035), (755585, 58496899), (754227, 58502766), (752868, 58508650), (751518, 58514232) ]
/-- Pulse chunk 8 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk8 : List (ℤ × ℤ) := [
  (750176, 58519641), (748840, 58524875), (747519, 58529793), (746200, 58534656), (744878,
  58539479), (743563, 58544508), (742244, 58549658), (740920, 58554908), (739608, 58560155),
  (738298, 58565308), (736983, 58570390), (735680, 58575332), (734383, 58579905), (733083,
  58584226), (731794, 58588237), (730507, 58592124), (729214, 58595974), (727924, 58599834),
  (726631, 58603931), (725329, 58608167), (724025, 58612516), (722734, 58616283), (721441,
  58619735), (720155, 58622802), (718873, 58625651), (717588, 58628387), (716305, 58630972),
  (715023, 58633446), (713738, 58635915), (712453, 58638381), (711164, 58640856), (709873,
  58643362), (708582, 58645898), (707285, 58648272), (706000, 58650062), (704730, 58651239),
  (703451, 58652364), (702175, 58653593), (700906, 58654924), (699624, 58656418), (698345,
  58657929), (697072, 58659414), (695791, 58660509), (694518, 58661338), (693259, 58661969),
  (692006, 58662354), (690761, 58662654), (689529, 58662888), (688284, 58663002), (687045,
  58663455), (685817, 58664098), (684580, 58664902), (683343, 58665763), (682124, 58666625),
  (680927, 58667437), (679742, 58667949), (678570, 58668241), (677400, 58668233), (676228,
  58668233), (675073, 58668242), (673933, 58668262), (672813, 58668350), (671695, 58668750),
  (670568, 58669581), (669459, 58670669), (668370, 58671771), (667298, 58672869), (666222,
  58673873), (665156, 58674779), (664096, 58675582), (663070, 58676150), (662038, 58676796),
  (660998, 58677514), (659972, 58678409), (658959, 58679567), (657952, 58680977), (656962,
  58682977), (655964, 58685159), (654950, 58687421), (653931, 58689617), (652919, 58691731),
  (651905, 58693780), (650929, 58695764), (649963, 58697727), (648979, 58699710), (647975,
  58701801), (646977, 58704276), (645971, 58707030), (644975, 58710203), (643980, 58713705) ]
/-- Pulse chunk 9 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk9 : List (ℤ × ℤ) := [
  (642969, 58717316), (641954, 58721014), (640952, 58724588), (639940, 58728059), (638925,
  58731407), (637920, 58734759), (636914, 58738131), (635913, 58741536), (634933, 58745119),
  (633942, 58749028), (632941, 58753288), (631926, 58758106), (630913, 58762966), (629904,
  58767862), (628902, 58772678), (627916, 58777378), (626949, 58781971), (626007, 58786350),
  (625064, 58790774), (624125, 58795236), (623152, 58799763), (622183, 58804310), (621233,
  58808867), (620311, 58813416), (619405, 58817960), (618517, 58822572), (617617, 58827421),
  (616706, 58832476), (615801, 58837646), (614887, 58842935), (613966, 58848203), (613069,
  58853310), (612202, 58858073), (611347, 58862297), (610500, 58866369), (609643, 58870349),
  (608757, 58874304), (607881, 58878287), (607017, 58882308), (606164, 58886562), (605307,
  58890935), (604442, 58895429), (603546, 58899829), (602647, 58904053), (601741, 58908088),
  (600874, 58911548), (600001, 58914759), (599121, 58917750), (598240, 58920614), (597342,
  58923383), (596430, 58926065), (595542, 58928550), (594654, 58930890), (593756, 58933125),
  (592849, 58935222), (591928, 58937392), (590994, 58939670), (590062, 58942206), (589141,
  58944731), (588215, 58947142), (587280, 58949196), (586357, 58950559), (585430, 58951617),
  (584498, 58952427), (583583, 58953086), (582667, 58953661), (581749, 58954130), (580826,
  58954452), (579906, 58954685), (578993, 58954805), (578090, 58954740), (577189, 58954564),
  (576290, 58954264), (575363, 58953739), (574438, 58953091), (573519, 58952314), (572614,
  58951291), (571729, 58950187), (570865, 58949005), (570011, 58947770), (569141, 58946571),
  (568255, 58945414), (567299, 58944438), (566365, 58943733), (565446, 58943086), (564535,
  58941612), (563676, 58939875), (562846, 58937958), (562010, 58935866), (561137, 58933713) ]
/-- Pulse chunk 10 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk10 : List (ℤ × ℤ) := [
  (560240, 58931526), (559309, 58929331), (558369, 58927148), (557433, 58924969), (556526,
  58922804), (555658, 58920660), (554785, 58918527), (553884, 58916414), (553008, 58914333),
  (552111, 58912271), (551175, 58910239), (550248, 58908273), (549316, 58906342), (548381,
  58904458), (547454, 58902678), (546525, 58900956), (545598, 58899299), (544698, 58897800),
  (543796, 58896382), (542893, 58895045), (541974, 58893909), (541051, 58892844), (540125,
  58891827), (539178, 58890605), (538239, 58889209), (537308, 58887682), (536394, 58886186),
  (535493, 58884861), (534605, 58883710), (533746, 58883016), (532867, 58882825), (531977,
  58882927), (531071, 58883244), (530145, 58883695), (529213, 58884240), (528277, 58884949),
  (527369, 58885842), (526486, 58886848), (525632, 58888020), (524790, 58889214), (523946,
  58890358), (523080, 58891405), (522169, 58892345), (521271, 58893273), (520396, 58894227),
  (519527, 58895931), (518665, 58898050), (517807, 58900637), (516967, 58903624), (516111,
  58906750), (515232, 58910009), (514319, 58913411), (513410, 58916785), (512504, 58920126),
  (511618, 58923292), (510748, 58926489), (509891, 58929747), (509030, 58933472), (508160,
  58937684), (507280, 58942289), (506379, 58947373), (505475, 58952217), (504570, 58956887),
  (503672, 58961372), (502781, 58965832), (501890, 58970309), (501005, 58974907), (500122,
  58979653), (499233, 58984580), (498340, 58989885), (497443, 58995808), (496537, 59002044),
  (495630, 59008602), (494733, 59015147), (493836, 59021537), (492948, 59027636), (492082,
  59033461), (491216, 59039245), (490354, 59045033), (489502, 59050878), (488638, 59056757),
  (487766, 59062674), (486895, 59068622), (486031, 59074601), (485177, 59080615), (484346,
  59086972), (483528, 59093558), (482726, 59100372), (481925, 59107557), (481103, 59114758) ]
/-- Pulse chunk 11 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk11 : List (ℤ × ℤ) := [
  (480269, 59121915), (479464, 59128490), (478646, 59134833), (477825, 59141007), (477028,
  59146996), (476258, 59152945), (475496, 59158874), (474676, 59164778), (473910, 59170646),
  (473167, 59176488), (472404, 59182276), (471635, 59188001), (470881, 59193688), (470157,
  59199308), (469399, 59204848), (468641, 59210340), (467887, 59215757), (467122, 59221068),
  (466351, 59226305), (465561, 59231440), (464797, 59236293), (464026, 59240722), (463232,
  59244577), (462473, 59247937), (461754, 59251265), (461079, 59254597), (460402, 59258076),
  (459697, 59261663), (458963, 59265356), (458177, 59269067), (457391, 59272635), (456603,
  59276067), (455797, 59279243), (455006, 59282276), (454227, 59285183), (453467, 59287835),
  (452725, 59290161), (452002, 59292183), (451345, 59293535), (450667, 59294460), (449967,
  59295128), (449227, 59295558), (448466, 59296048), (447707, 59296666), (446993, 59297591),
  (446274, 59298415), (445550, 59299153), (444828, 59299734), (444127, 59299994), (443425,
  59299987), (442718, 59299587), (442099, 59298424), (441500, 59296959), (440913, 59295198),
  (440300, 59293529), (439677, 59291955), (439046, 59290492), (438383, 59289062), (437734,
  59287358), (437107, 59285341), (436562, 59282539), (436016, 59279621), (435470, 59276605),
  (434930, 59273746), (434364, 59271086), (433780, 59268567), (433219, 59265841), (432706,
  59262647), (432224, 59259072), (431733, 59254979), (431230, 59250627), (430721, 59246101),
  (430197, 59241402), (429673, 59236641), (429156, 59231918), (428646, 59227436), (428143,
  59223295), (427649, 59219295), (427158, 59215349), (426668, 59211090), (426184, 59206530),
  (425700, 59201484), (425210, 59196091), (424723, 59190571), (424233, 59184947), (423728,
  59179324), (423222, 59173765), (422711, 59168304), (422177, 59163263), (421639, 59158506) ]
/-- Pulse chunk 12 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk12 : List (ℤ × ℤ) := [
  (421097, 59154062), (420540, 59149344), (419985, 59144402), (419432, 59139232), (418872,
  59133684), (418318, 59128043), (417768, 59122318), (417220, 59116598), (416677, 59110907),
  (416138, 59105243), (415587, 59099641), (415009, 59094081), (414400, 59088555), (413700,
  59083093), (413084, 59077680), (412509, 59072330), (411929, 59067167), (411354, 59062263),
  (410779, 59057575), (410206, 59053267), (409568, 59049480), (408919, 59045872), (408299,
  59042307), (407748, 59038478), (407216, 59034502), (406695, 59030369), (406158, 59026222),
  (405599, 59022127), (405013, 59018130), (404412, 59014337), (403802, 59010660), (403186,
  59007117), (402577, 59003803), (401967, 59000610), (401359, 58997545), (400796, 58994727),
  (400260, 58992034), (399751, 58989466), (399312, 58987156), (398875, 58984986), (398433,
  58982948), (397936, 58981162), (397461, 58979530), (397006, 58978031), (396604, 58976770),
  (396160, 58975681), (395680, 58974730), (395150, 58974009), (394616, 58973477), (394116,
  58973083), (393759, 58972909), (393285, 58972940), (392759, 58973114), (392213, 58973502),
  (391696, 58974114), (391202, 58974872), (390751, 58975832), (390337, 58977027), (389936,
  58978364), (389550, 58979886), (389163, 58981657), (388769, 58983571), (388366, 58985656),
  (387933, 58987999), (387470, 58990482), (386971, 58993118), (386395, 58996015), (385819,
  58999050), (385248, 59002223), (384694, 59005668), (384170, 59009250), (383674, 59012966),
  (383183, 59016934), (382644, 59021045), (382066, 59025287), (381450, 59029764), (380827,
  59034391), (380200, 59039143), (379562, 59044105), (378919, 59049216), (378285, 59054443),
  (377692, 59059855), (377105, 59065422), (376521, 59071102), (375934, 59076949), (375332,
  59082953), (374694, 59089062), (373972, 59095317), (373220, 59101723), (372458, 59108225) ]
/-- Pulse chunk 13 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk13 : List (ℤ × ℤ) := [
  (371689, 59114853), (370914, 59121626), (370143, 59128485), (369382, 59135449), (368682,
  59142550), (368000, 59149727), (367334, 59156991), (366629, 59164386), (365899, 59171852),
  (365141, 59179390), (364331, 59187048), (363554, 59194764), (362811, 59202536), (362132,
  59210404), (361455, 59218320), (360779, 59226284), (360078, 59234323), (359341, 59242403),
  (358575, 59250519), (357784, 59258683), (357051, 59266877), (356365, 59275095), (355770,
  59283344), (355185, 59291613), (354583, 59299897), (353912, 59308196), (353165, 59316499),
  (352410, 59324804), (351733, 59333106), (351112, 59341398), (350519, 59349682), (349957,
  59357951), (349413, 59366191), (348874, 59374411), (348341, 59382600), (347809, 59390738),
  (347274, 59398846), (346735, 59406913), (346194, 59414909), (345651, 59422863), (345105,
  59430769), (344563, 59438579), (344028, 59446336), (343501, 59454039), (343005, 59461625),
  (342538, 59469148), (342102, 59476610), (341746, 59483939), (341429, 59491191), (341112,
  59498371), (340456, 59505406), (339837, 59512345), (339255, 59519202), (338757, 59525906),
  (338315, 59532495), (337916, 59538992), (337562, 59545329), (337203, 59551529), (336841,
  59557629), (336469, 59563568), (336106, 59569354), (335741, 59575031), (335354, 59580548),
  (334623, 59585888), (333888, 59591110), (333352, 59596171), (332939, 59601032), (332571,
  59605770), (332234, 59610349), (331857, 59614707), (331411, 59618935), (330868, 59623009),
  (330180, 59626839), (329491, 59630532), (328814, 59634078), (328303, 59637357), (327922,
  59640494), (327669, 59643488), (327117, 59646200), (326520, 59648762), (325884, 59651178),
  (325242, 59653318), (324610, 59655292), (323987, 59657116), (323378, 59658670), (322782,
  59660039), (322197, 59661253), (321611, 59662205), (321023, 59662954), (320432, 59663546) ]
/-- Pulse chunk 14 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk14 : List (ℤ × ℤ) := [
  (319830, 59663887), (319217, 59664007), (318596, 59663968), (317963, 59663689), (317319,
  59663171), (316669, 59662510), (316007, 59661667), (315334, 59660709), (314655, 59659730),
  (313967, 59658761), (313274, 59658140), (312582, 59657581), (311896, 59657017), (311217,
  59655608), (310549, 59653740), (309892, 59651366), (309273, 59648459), (308684, 59645349),
  (308130, 59642042), (307624, 59638451), (307113, 59634714), (306590, 59630830), (305935,
  59626676), (305158, 59622408), (304290, 59618059), (303530, 59613846), (302923, 59609913),
  (302427, 59606145), (301992, 59602159), (301574, 59597844), (301167, 59593238), (300774,
  59588083), (300382, 59582475), (299971, 59576566), (299498, 59570308), (298853, 59563853),
  (298143, 59557266), (297436, 59550499), (296933, 59543548), (296562, 59536475), (296366,
  59529237), (296086, 59522238), (295741, 59515373), (295307, 59508664), (294802, 59502014),
  (294280, 59495304), (293752, 59488487), (293367, 59481133), (293139, 59473300), (293100,
  59464905), (292841, 59456225), (292473, 59447464), (291998, 59438629), (291464, 59429760),
  (291014, 59421085), (290648, 59412600), (290463, 59404429), (290289, 59396201), (290117,
  59387895), (289875, 59379244), (289531, 59370232), (289091, 59360902), (288451, 59350999),
  (288152, 59341775), (288045, 59332915), (288007, 59324111), (287939, 59315099), (287835,
  59305889), (287647, 59296304), (287344, 59286392), (286987, 59276391), (286582, 59266453),
  (286178, 59256804), (285775, 59247310), (285371, 59237992), (285006, 59228600), (284803,
  59218775), (284873, 59208205), (284817, 59197374), (284659, 59186475), (284375, 59175529),
  (283929, 59164623), (283426, 59153798), (282868, 59143070), (282389, 59132844), (282038,
  59122983), (281815, 59113482), (281613, 59104155), (281414, 59094854), (281216, 59085570) ]
/-- Pulse chunk 15 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk15 : List (ℤ × ℤ) := [
  (281006, 59076226), (280671, 59066563), (280228, 59056620), (279608, 59046234), (278961,
  59035784), (278306, 59025325), (277691, 59015024), (277171, 59005011), (276752, 58995256),
  (276553, 58985989), (276328, 58976347), (276095, 58966447), (275866, 58956199), (275560,
  58945966), (275168, 58935883), (274623, 58926170), (273904, 58917038), (273156, 58908141),
  (272434, 58899442), (271812, 58890869), (271259, 58882318), (270790, 58873773), (270425,
  58865075), (270043, 58856088), (269622, 58846731), (269152, 58837198), (268664, 58827877),
  (268160, 58818807), (267634, 58810369), (267102, 58802243), (266562, 58794417), (266010,
  58786872), (265452, 58779408), (264889, 58772019), (264315, 58764774), (263735, 58757622),
  (263147, 58750542), (262546, 58743561), (261924, 58736488), (261283, 58729290), (260608,
  58721733), (259953, 58714104), (259329, 58706496), (258785, 58699085), (258365, 58692093),
  (258037, 58685428), (257847, 58679276), (257607, 58673485), (257271, 58667863), (256747,
  58662402), (256080, 58657109), (255368, 58651919), (254630, 58646860), (253878, 58641986),
  (253157, 58637222), (252487, 58632585), (251993, 58628145), (251595, 58623817), (251296,
  58619609), (251125, 58615617), (250967, 58611742), (250817, 58607985), (250672, 58604432),
  (250429, 58600746), (250088, 58596928), (249563, 58592849), (248955, 58588697), (248290,
  58584520), (247654, 58580632), (247191, 58577297), (246854, 58574391), (246655, 58572051),
  (246493, 58569999), (246343, 58568135), (246170, 58566463), (245983, 58564959), (245786,
  58563579), (245579, 58562383), (245368, 58561368), (245155, 58560477), (244939, 58559757),
  (244721, 58559230), (244498, 58558829), (244267, 58558590), (244020, 58558561), (243764,
  58558657), (243500, 58558906), (243235, 58559370), (242992, 58559960), (242781, 58560689) ]
/-- Pulse chunk 16 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk16 : List (ℤ × ℤ) := [
  (242890, 58561650), (243090, 58562737), (243372, 58563956), (243508, 58565412), (243547,
  58566993), (243491, 58568698), (243275, 58570639), (242989, 58572712), (242648, 58574912),
  (242333, 58577337), (242058, 58579901), (241829, 58582588), (241726, 58585484), (241755,
  58588557), (241892, 58591819), (242189, 58595545), (242459, 58599881), (242711, 58604611),
  (242934, 58609779), (243055, 58615067), (243075, 58620348), (242910, 58625477), (242544,
  58630264), (242155, 58634979), (241850, 58639762), (241684, 58644715), (241598, 58649782),
  (241602, 58654997), (241666, 58660403), (241715, 58665926), (241727, 58671583), (241684,
  58677440), (241614, 58683410), (241514, 58689501), (241359, 58695795), (241176, 58702196),
  (240965, 58708705), (240688, 58715424), (240394, 58722287), (240088, 58729305), (239852,
  58736804), (239721, 58744709), (239688, 58752991), (239843, 58761945), (239917, 58770890),
  (239902, 58779777), (239627, 58788322), (239233, 58796754), (238757, 58805121), (238184,
  58813466), (237574, 58821883), (236962, 58830372), (236387, 58839001), (235949, 58847762),
  (235610, 58856622), (235416, 58865634), (235218, 58875008), (234949, 58884691), (234529,
  58894842), (233880, 58905547), (233183, 58916402), (232475, 58927331), (231927, 58937976),
  (231453, 58948445), (231054, 58958713), (230638, 58968795), (230075, 58978928), (229334,
  58989142), (228337, 58999532), (227413, 59010291), (226574, 59021434), (225928, 59033207),
  (225357, 59045168), (224852, 59057281), (224372, 59069282), (223880, 59081012), (223364,
  59092524), (222712, 59103806), (221905, 59115056), (220963, 59126309), (219779, 59137681),
  (218510, 59149204), (217267, 59160997), (216301, 59173590), (215448, 59186436), (214653,
  59199382), (213902, 59212330), (213138, 59225075), (212359, 59237636), (211555, 59249890) ]
/-- Pulse chunk 17 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk17 : List (ℤ × ℤ) := [
  (210730, 59261959), (209893, 59274010), (209040, 59286111), (208174, 59298415), (207301,
  59310908), (206420, 59323655), (205540, 59337145), (204661, 59350738), (203781, 59364361),
  (202905, 59377722), (202030, 59390926), (201156, 59403969), (200293, 59416840), (199437,
  59429884), (198590, 59443128), (197765, 59457299), (196950, 59471338), (196145, 59485237),
  (195361, 59498706), (194592, 59511951), (193835, 59525077), (193106, 59538392), (192397,
  59552067), (191703, 59565978), (191034, 59580080), (190387, 59594121), (189755, 59608047),
  (189150, 59621657), (188577, 59634735), (188026, 59647843), (187510, 59661566), (187025,
  59675591), (186561, 59689707), (186125, 59703839), (185723, 59717721), (185345, 59731372),
  (184999, 59744691), (184698, 59757971), (184421, 59771397), (184170, 59785054), (183968,
  59799128), (183791, 59813333), (183643, 59827657), (183557, 59840899), (183501, 59854056),
  (183477, 59867168), (183508, 59880524), (183554, 59894044), (183613, 59907722), (183657,
  59921613), (183616, 59935407), (183489, 59949064), (183141, 59962121), (182740, 59974993),
  (182336, 59987801), (182108, 60000898), (182155, 60014524), (182361, 60028450), (182663,
  60042522), (182986, 60056582), (183317, 60070600), (183654, 60084491), (183995, 60098112),
  (184339, 60111494), (184689, 60124482), (185052, 60136850), (185427, 60149129), (185817,
  60161542), (186223, 60174466), (186639, 60187539), (187066, 60200706), (187508, 60213504),
  (187953, 60226038), (188403, 60238258), (188786, 60250258), (189081, 60262326), (189277,
  60274490), (189239, 60287071), (189105, 60299902), (188889, 60312970), (189000, 60325948),
  (189275, 60338877), (189689, 60351723), (190180, 60364019), (190674, 60375964), (191165,
  60387619), (191609, 60398895), (191967, 60410116), (192237, 60421368), (192305, 60432932) ]
/-- Pulse chunk 18 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk18 : List (ℤ × ℤ) := [
  (192222, 60444788), (192090, 60456815), (192032, 60468978), (192237, 60481048), (192570,
  60493026), (192994, 60504832), (193206, 60516014), (193293, 60526872), (193227, 60537392),
  (193036, 60547741), (192792, 60558078), (192495, 60568462), (192203, 60579202), (191932,
  60590141), (191692, 60601308), (191880, 60612426), (192216, 60623423), (192689, 60634265),
  (193073, 60644667), (193347, 60654702), (193504, 60664358), (193498, 60673671), (193470,
  60683010), (193424, 60692384), (193399, 60701981), (193416, 60711757), (193473, 60721685),
  (193609, 60731773), (193809, 60741782), (194065, 60751723), (194414, 60761548), (194841,
  60771284), (195335, 60780942), (195939, 60790454), (196654, 60799659), (197454, 60808571),
  (198378, 60816917), (199411, 60824768), (200513, 60832329), (201705, 60839564), (202690,
  60846393), (202853, 60852428), (201344, 60856964), (199994, 60861369), (198737, 60865693),
  (197587, 60869916), (196563, 60874000), (195605, 60878000), (194721, 60881904), (193931,
  60885658), (193189, 60889327), (192494, 60892906), (191868, 60896323), (191273, 60899655),
  (190709, 60902900), (190189, 60905979), (189688, 60908967), (189206, 60911868), (188747,
  60914609), (188299, 60917249), (187859, 60919801), (187428, 60922198), (186999, 60924486),
  (186571, 60926684), (186142, 60928735), (185708, 60930667), (185270, 60932508), (184822,
  60934208), (184365, 60935781), (183899, 60937262), (183421, 60938609), (182926, 60939820),
  (182422, 60940938), (181902, 60941929), (181363, 60942776), (180811, 60943530), (180243,
  60944164), (179653, 60944645), (179050, 60945032), (178432, 60945307), (177789, 60945420),
  (177133, 60945440), (176462, 60945355), (175766, 60945101), (175057, 60944752), (174335,
  60944307), (173588, 60943683), (172828, 60942965), (172056, 60942153), (171261, 60941168) ]
/-- Pulse chunk 19 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk19 : List (ℤ × ℤ) := [
  (170453, 60940081), (169634, 60938900), (168796, 60937554), (167945, 60936099), (167084,
  60934550), (166206, 60932843), (165318, 60931020), (164420, 60929103), (163509, 60927038),
  (162587, 60924848), (161658, 60922565), (160719, 60920142), (159771, 60917587), (158817,
  60914939), (157855, 60912159), (156886, 60909240), (155914, 60906228), (154936, 60903094),
  (153954, 60899814), (152968, 60896441), (151980, 60892954), (150990, 60889313), (149999,
  60885582), (149007, 60881744), (148015, 60877746), (147024, 60873658), (146034, 60869473),
  (145048, 60865120), (144063, 60860679), (143081, 60856147), (142105, 60851444), (141133,
  60846652), (140165, 60841770), (139205, 60836727), (138251, 60831586), (137302, 60826358),
  (136364, 60820977), (135433, 60815493), (134509, 60809921), (133597, 60804206), (132695,
  60798381), (131801, 60792470), (130920, 60786425), (130052, 60780263), (129192, 60774016),
  (128347, 60767644), (127517, 60761149), (126697, 60754571), (125891, 60747876), (125103,
  60741053), (124326, 60734146), (123564, 60727133), (122821, 60719985), (122091, 60712755),
  (121375, 60705427), (120683, 60697960), (120003, 60690411), (119337, 60682772), (118697,
  60674990), (118070, 60667128), (117456, 60659182), (116871, 60651089), (116300, 60642917),
  (115742, 60634667), (115214, 60626272), (114700, 60617796), (114201, 60609242), (113730,
  60600553), (113276, 60591777), (112837, 60582925), (112426, 60573946), (112033, 60564875),
  (111655, 60555730), (111304, 60546466), (110974, 60537105), (110659, 60527672), (110369,
  60518128), (110101, 60508484), (109849, 60498767), (109621, 60488949), (109417, 60479025),
  (109228, 60469031), (109061, 60458943), (108920, 60448746), (108795, 60438479), (108690,
  60428127), (108612, 60417661), (108550, 60407128), (108506, 60396516), (108490, 60385788) ]
/-- Pulse chunk 20 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk20 : List (ℤ × ℤ) := [
  (108490, 60374994), (108507, 60364128), (108552, 60353142), (108613, 60342092), (108690,
  60330977), (108796, 60319739), (108916, 60308439), (109052, 60297075), (109216, 60285597),
  (109395, 60274052), (109588, 60262445), (109807, 60250731), (110043, 60238947), (110292,
  60227102), (110565, 60215158), (110855, 60203141), (111158, 60191064), (111482, 60178896),
  (111824, 60166650), (112179, 60154347), (112552, 60141960), (112944, 60129492), (113347,
  60116969), (113767, 60104368), (114206, 60091684), (114655, 60078945), (115120, 60066136),
  (115602, 60053241), (116094, 60040294), (116600, 60027282), (117123, 60014182), (117655,
  60001030), (118199, 59987820), (118760, 59974521), (119329, 59961172), (119908, 59947771),
  (120503, 59934278), (121106, 59920737), (121716, 59907147), (122342, 59893468), (122974,
  59879740), (123614, 59865966), (124267, 59852108), (124926, 59838199), (125591, 59824245),
  (126267, 59810214), (126949, 59796131), (127636, 59782003), (128332, 59767804), (129033,
  59753551), (129738, 59739255), (130450, 59724894), (131167, 59710477), (131887, 59696018),
  (132611, 59681500), (133339, 59666925), (134070, 59652309), (134804, 59637640), (135540,
  59622911), (136278, 59608144), (137018, 59593328), (137758, 59578452), (138500, 59563539),
  (139242, 59548582), (139983, 59533563), (140724, 59518509), (141464, 59503416), (142202,
  59488262), (142939, 59473073), (143675, 59457849), (144407, 59442563), (145136, 59427244),
  (145863, 59411892), (146585, 59396482), (147304, 59381039), (148019, 59365564), (148728,
  59350036), (149432, 59334474), (150132, 59318881), (150824, 59303240), (151511, 59287563),
  (152193, 59271858), (152866, 59256109), (153531, 59240323), (154192, 59224511), (154842,
  59208658), (155484, 59192769), (156119, 59176854), (156745, 59160903), (157360, 59144915) ]
/-- Pulse chunk 21 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk21 : List (ℤ × ℤ) := [
  (157968, 59128903), (158566, 59112858), (159151, 59096777), (159728, 59080672), (160296,
  59064538), (160849, 59048368), (161393, 59032176), (161927, 59015960), (162445, 58999706),
  (162954, 58983431), (163453, 58967134), (163934, 58950801), (164406, 58934449), (164868,
  58918078), (165309, 58901671), (165741, 58885245), (166162, 58868802), (166563, 58852328),
  (166953, 58835835), (167331, 58819324), (167691, 58802786), (168037, 58786229), (168371,
  58769657), (168687, 58753060), (168988, 58736444), (169277, 58719814), (169547, 58703162),
  (169801, 58686492), (170043, 58669808), (170267, 58653106), (170473, 58636386), (170667,
  58619654), (170843, 58602905), (171000, 58586140), (171145, 58569363), (171273, 58552573),
  (171379, 58535766), (171474, 58518950), (171553, 58502122), (171609, 58485278), (171653,
  58468425), (171681, 58451563), (171687, 58434687), (171679, 58417803), (171658, 58400910),
  (171611, 58384006), (171552, 58367094), (171480, 58350176), (171382, 58333247), (171271,
  58316312), (171146, 58299371), (170999, 58282422), (170836, 58265468), (170660, 58248509),
  (170462, 58231544), (170247, 58214574), (170020, 58197600), (169771, 58180622), (169505,
  58163641), (169227, 58146656), (168929, 58129669), (168613, 58112680), (168284, 58095689),
  (167936, 58078697), (167570, 58061703), (167191, 58044709), (166795, 58027715), (166380,
  58010721), (165952, 57993727), (165509, 57976734), (165046, 57959744), (164570, 57942755),
  (164080, 57925767), (163570, 57908782), (163047, 57891800), (162512, 57874820), (161956,
  57857846), (161388, 57840876), (160809, 57823908), (160208, 57806948), (159596, 57789991),
  (158973, 57773038), (158330, 57756094), (157675, 57739155), (157010, 57722221), (156327,
  57705297), (155631, 57688379), (154925, 57671467), (154202, 57654565), (153467, 57637671) ]
/-- Pulse chunk 22 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk22 : List (ℤ × ℤ) := [
  (152723, 57620783), (151963, 57603907), (151191, 57587040), (150409, 57570181), (149614,
  57553333), (148806, 57536497), (147990, 57519668), (147161, 57502852), (146319, 57486048),
  (145469, 57469254), (144609, 57452471), (143736, 57435705), (142856, 57418947), (141965,
  57402202), (141063, 57385474), (140153, 57368756), (139236, 57352051), (138306, 57335365),
  (137369, 57318689), (136426, 57302026), (135472, 57285384), (134511, 57268754), (133544,
  57252136), (132567, 57235540), (131584, 57218959), (130595, 57202389), (129598, 57185842),
  (128595, 57169311), (127588, 57152792), (126573, 57136297), (125552, 57119818), (124527,
  57103353), (123497, 57086911), (122461, 57070488), (121422, 57054079), (120378, 57037693),
  (119329, 57021327), (118278, 57004976), (117223, 56988647), (116164, 56972342), (115103,
  56956052), (114039, 56939784), (112972, 56923541), (111903, 56907314), (110833, 56891108),
  (109761, 56874929), (108687, 56858767), (107612, 56842626), (106536, 56826514), (105460,
  56810420), (104383, 56794345), (103306, 56778301), (102229, 56762276), (101152, 56746270),
  (100077, 56730297), (99002, 56714343), (97927, 56698408), (96855, 56682507), (95784, 56666627),
  (94715, 56650766), (93648, 56634938), (92584, 56619133), (91521, 56603347), (90462, 56587595),
  (89406, 56571866), (88353, 56556158), (87304, 56540482), (86258, 56524833), (85216, 56509204),
  (84179, 56493606), (83146, 56478038), (82118, 56462490), (81094, 56446972), (80076, 56431486),
  (79063, 56416021), (78055, 56400584), (77054, 56385182), (76058, 56369801), (75068, 56354447),
  (74086, 56339131), (73109, 56323836), (72138, 56308567), (71176, 56293337), (70220, 56278130),
  (69270, 56262947), (68331, 56247806), (67398, 56232687), (66470, 56217591), (65555, 56202540),
  (64647, 56187512) ]
/-- Pulse chunk 23 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk23 : List (ℤ × ℤ) := [
  (63744, 56172507), (62854, 56157544), (61972, 56142608), (61096, 56127695), (60232, 56112823),
  (59378, 56097980), (58530, 56083160), (57694, 56068380), (56868, 56053630), (56050, 56038905),
  (55244, 56024218), (54449, 56009564), (53662, 55994935), (52886, 55980341), (52123, 55965784),
  (51367, 55951251), (50624, 55936754), (49893, 55922294), (49171, 55907859), (48460, 55893458),
  (47764, 55879097), (47076, 55864761), (46400, 55850457), (45738, 55836196), (45086, 55821960),
  (44444, 55807753), (43819, 55793593), (43203, 55779459), (42597, 55765351), (42009, 55751292),
  (41430, 55737260), (40862, 55723254), (40311, 55709296), (39770, 55695366), (39239, 55681463),
  (38726, 55667607), (38224, 55653781), (37732, 55639982), (37257, 55626227), (36795, 55612505),
  (36342, 55598811), (35906, 55585159), (35483, 55571542), (35070, 55557953), (34673, 55544405),
  (34291, 55530895), (33918, 55517411), (33561, 55503967), (33219, 55490563), (32887, 55477186),
  (32569, 55463846), (32268, 55450550), (31977, 55437280), (31699, 55424046), (31439, 55410857),
  (31189, 55397695), (30951, 55384567), (30732, 55371486), (30523, 55358433), (30326, 55345410),
  (30148, 55332438), (29981, 55319494), (29823, 55306579), (29686, 55293716), (29560, 55280881),
  (29444, 55268075), (29347, 55255320), (29261, 55242595), (29186, 55229899), (29129, 55217252),
  (29084, 55204637), (29050, 55192051), (29032, 55179512), (29028, 55167008), (29033, 55154532),
  (29056, 55142101), (29091, 55129709), (29137, 55117345), (29198, 55105023), (29274, 55092741),
  (29359, 55080488), (29458, 55068275), (29573, 55056105), (29697, 55043963), (29835, 55031859),
  (29988, 55019801), (30151, 55007771), (30326, 54995776), (30518, 54983830), (30719, 54971913) ]
/-- Pulse chunk 24 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk24 : List (ℤ × ℤ) := [
  (30931, 54960027), (31160, 54948193), (31398, 54936388), (31646, 54924612), (31912, 54912890),
  (32186, 54901197), (32470, 54889532), (32772, 54877921), (33083, 54866341), (33402, 54854789),
  (33738, 54843288), (34084, 54831819), (34438, 54820379), (34808, 54808988), (35188, 54797632),
  (35576, 54786305), (35979, 54775024), (36392, 54763781), (36814, 54752566), (37248, 54741395),
  (37693, 54730263), (38147, 54719161), (38612, 54708100), (39090, 54697081), (39574, 54686091),
  (40069, 54675140), (40577, 54664234), (41092, 54653356), (41616, 54642514), (42153, 54631720),
  (42697, 54620955), (43250, 54610223), (43815, 54599541), (44387, 54588887), (44967, 54578265),
  (45559, 54567695), (46159, 54557153), (46765, 54546640), (47384, 54536182), (48009, 54525752),
  (48640, 54515351), (49283, 54505002), (49933, 54494684), (50589, 54484394), (51256, 54474154),
  (51929, 54463947), (52608, 54453768), (53297, 54443637), (53992, 54433541), (54694, 54423473),
  (55404, 54413450), (56121, 54403465), (56844, 54393508), (57574, 54383593), (58311, 54373718),
  (59053, 54363872), (59802, 54354065), (60558, 54344300), (61319, 54334564), (62086, 54324865),
  (62860, 54315210), (63638, 54305583), (64422, 54295991), (65212, 54286446), (66007, 54276929),
  (66806, 54267443), (67612, 54258007), (68421, 54248599), (69235, 54239221), (70055, 54229893),
  (70878, 54220594), (71705, 54211321), (72538, 54202102), (73375, 54192911), (74214, 54183747),
  (75058, 54174633), (75906, 54165549), (76756, 54156493), (77611, 54147485), (78469, 54138508),
  (79330, 54129559), (80194, 54120656), (81061, 54111786), (81930, 54102944), (82803, 54094145),
  (83678, 54085382), (84556, 54076646), (85435, 54067950), (86317, 54059293), (87201, 54050663) ]
/-- Pulse chunk 25 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk25 : List (ℤ × ℤ) := [
  (88087, 54042071), (88975, 54033519), (89864, 54024995), (90755, 54016504), (91647, 54008058),
  (92541, 53999638), (93436, 53991251), (94332, 53982908), (95229, 53974593), (96127, 53966307),
  (97025, 53958068), (97925, 53949856), (98824, 53941672), (99725, 53933537), (100625, 53925428),
  (101526, 53917345), (102426, 53909312), (103327, 53901306), (104228, 53893325), (105128,
  53885391), (106028, 53877487), (106927, 53869609), (107826, 53861774), (108724, 53853972),
  (109622, 53846194), (110518, 53838459), (111413, 53830756), (112308, 53823080), (113201,
  53815442), (114093, 53807840), (114984, 53800263), (115873, 53792723), (116761, 53785221),
  (117647, 53777743), (118531, 53770300), (119413, 53762896), (120293, 53755518), (121172,
  53748170), (122048, 53740865), (122922, 53733585), (123794, 53726333), (124663, 53719125),
  (125530, 53711942), (126394, 53704785), (127255, 53697674), (128114, 53690587), (128971,
  53683526), (129824, 53676511), (130674, 53669520), (131522, 53662554), (132365, 53655632),
  (133206, 53648737), (134045, 53641866), (134879, 53635037), (135709, 53628236), (136537,
  53621460), (137361, 53614723), (138181, 53608016), (138998, 53601334), (139811, 53594688),
  (140620, 53588075), (141426, 53581485), (142227, 53574930), (143024, 53568409), (143818,
  53561912), (144607, 53555447), (145392, 53549017), (146173, 53542611), (146950, 53536236),
  (147721, 53529898), (148489, 53523582), (149253, 53517295), (150011, 53511047), (150766,
  53504822), (151516, 53498623), (152261, 53492465), (153002, 53486329), (153739, 53480217),
  (154468, 53474148), (155195, 53468100), (155917, 53462076), (156632, 53456093), (157344,
  53450134), (158052, 53444198), (158752, 53438300), (159449, 53432428), (160142, 53426578),
  (160827, 53420765), (161508, 53414980), (162185, 53409216) ]
/-- Pulse chunk 26 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk26 : List (ℤ × ℤ) := [
  (162856, 53403488), (163521, 53397787), (164182, 53392109), (164837, 53386463), (165487,
  53380848), (166132, 53375254), (166771, 53369691), (167404, 53364159), (168034, 53358649),
  (168657, 53353169), (169274, 53347720), (169887, 53342293), (170494, 53336893), (171094,
  53331527), (171691, 53326183), (172282, 53320863), (172866, 53315579), (173445, 53310316),
  (174020, 53305075), (174587, 53299872), (175150, 53294690), (175708, 53289528), (176259,
  53284405), (176805, 53279303), (177346, 53274221), (177881, 53269176), (178410, 53264152),
  (178934, 53259149), (179452, 53254181), (179964, 53249236), (180473, 53244311), (180974,
  53239419), (181469, 53234552), (181960, 53229704), (182445, 53224887), (182924, 53220097),
  (183398, 53215326), (183866, 53210584), (184329, 53205869), (184787, 53201174), (185238,
  53196506), (185684, 53191867), (186125, 53187246), (186561, 53182651), (186990, 53178086),
  (187415, 53173540), (187835, 53169018), (188248, 53164527), (188656, 53160054), (189061,
  53155603), (189457, 53151185), (189850, 53146785), (190238, 53142405), (190619, 53138059),
  (190995, 53133731), (191368, 53129421), (191733, 53125146), (192095, 53120889), (192452,
  53116650), (192801, 53112444), (193147, 53108257), (193488, 53104089), (193824, 53099951),
  (194154, 53095834), (194480, 53091734), (194801, 53087664), (195116, 53083616), (195428,
  53079585), (195734, 53075581), (196035, 53071601), (196332, 53067638), (196624, 53063700),
  (196910, 53059787), (197194, 53055891), (197471, 53052019), (197744, 53048172), (198013,
  53044343), (198277, 53040535), (198536, 53036754), (198792, 53032989), (199044, 53029245),
  (199289, 53025530), (199531, 53021830), (199770, 53018148), (200003, 53014497), (200233,
  53010861), (200459, 53007242), (200679, 53003654), (200897, 53000082), (201111, 52996525) ]
/-- Pulse chunk 27 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk27 : List (ℤ × ℤ) := [
  (201319, 52992998), (201524, 52989488), (201726, 52985994), (201924, 52982528), (202117,
  52979080), (202308, 52975647), (202494, 52972240), (202676, 52968853), (202856, 52965481),
  (203031, 52962133), (203203, 52958806), (203372, 52955494), (203538, 52952204), (203699,
  52948936), (203858, 52945684), (204013, 52942452), (204165, 52939243), (204314, 52936049),
  (204460, 52932874), (204603, 52929723), (204743, 52926586), (204880, 52923467), (205013,
  52920373), (205145, 52917293), (205273, 52914230), (205399, 52911192), (205522, 52908169),
  (205643, 52905161), (205760, 52902179), (205875, 52899210), (205988, 52896256), (206098,
  52893329), (206206, 52890416), (206312, 52887516), (206415, 52884642), (206516, 52881783),
  (206616, 52878937), (206713, 52876116), (206807, 52873310), (206901, 52870518), (206991,
  52867748), (207080, 52864994), (207168, 52862255), (207254, 52859536), (207338, 52856834),
  (207420, 52854146), (207501, 52851477), (207580, 52848827), (207658, 52846189), (207734,
  52843570), (207809, 52840971), (207883, 52838384), (207955, 52835814), (208026, 52833264),
  (208096, 52830727), (208165, 52828205), (208232, 52825704), (208299, 52823216), (208365,
  52820742), (208430, 52818290), (208495, 52815850), (208558, 52813423), (208621, 52811019),
  (208683, 52808626), (208744, 52806245), (208806, 52803888), (208866, 52801543), (208926,
  52799209), (208986, 52796896), (209045, 52794597), (209104, 52792310), (209163, 52790042),
  (209222, 52787788), (209281, 52785546), (209339, 52783323), (209398, 52781114), (209457,
  52778916), (209515, 52776737), (209574, 52774572), (209634, 52772419), (209693, 52770282),
  (209753, 52768161), (209813, 52766051), (209873, 52763957), (209934, 52761879), (209996,
  52759812), (210058, 52757759), (210121, 52755723), (210184, 52753698), (210248, 52751686) ]
/-- Pulse chunk 28 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk28 : List (ℤ × ℤ) := [
  (210313, 52749692), (210379, 52747709), (210446, 52745737), (210513, 52743784), (210582,
  52741842), (210652, 52739911), (210722, 52737998), (210794, 52736096), (210867, 52734204),
  (210942, 52732331), (211017, 52730469), (211094, 52728617), (211172, 52726781), (211252,
  52724958), (211333, 52723145), (211416, 52721348), (211500, 52719563), (211586, 52717788),
  (211673, 52716029), (211763, 52714282), (211853, 52712544), (211946, 52710821), (212041,
  52709112), (212137, 52707411), (212236, 52705724), (212336, 52704051), (212438, 52702388),
  (212542, 52700736), (212649, 52699099), (212758, 52697472), (212868, 52695855), (212981,
  52694254), (213096, 52692661), (213213, 52691079), (213334, 52689513), (213456, 52687956),
  (213580, 52686407), (213708, 52684876), (213838, 52683352), (213969, 52681838), (214104,
  52680339), (214241, 52678850), (214381, 52677369), (214524, 52675903), (214670, 52674447),
  (214817, 52672999), (214968, 52671566), (215122, 52670142), (215278, 52668727), (215438,
  52667324), (215600, 52665933), (215765, 52664549), (215934, 52663178), (216105, 52661818),
  (216279, 52660466), (216457, 52659125), (216638, 52657796), (216821, 52656475), (217008,
  52655165), (217198, 52653866), (217391, 52652575), (217588, 52651294), (217788, 52650025),
  (217991, 52648764), (218197, 52647512), (218408, 52646273), (218621, 52645041), (218837,
  52643818), (219058, 52642608), (219282, 52641405), (219508, 52640210), (219740, 52639028),
  (219974, 52637854), (220211, 52636687), (220453, 52635533), (220698, 52634386), (220946,
  52633246), (221199, 52632119), (221455, 52631000), (221714, 52629887), (221978, 52628787),
  (222246, 52627694), (222517, 52626609), (222792, 52625534), (223070, 52624468), (223352,
  52623409), (223639, 52622359), (223929, 52621319), (224223, 52620286), (224521, 52619261) ]
/-- Pulse chunk 29 (`90` `(u0, v)` pairs over `10^9`) for `(1, 2)`. -/
def ltM1K2RawChunk29 : List (ℤ × ℤ) := [
  (224823, 52618247), (225128, 52617239), (225438, 52616240), (225752, 52615250), (226069,
  52614267), (226390, 52613292), (226717, 52612327), (227046, 52611368), (227379, 52610417),
  (227718, 52609476), (228059, 52608541), (228404, 52607613), (228755, 52606696), (229109,
  52605785), (229465, 52604880), (229829, 52603987), (230195, 52603098), (230564, 52602216),
  (230939, 52601345), (231318, 52600480), (231700, 52599620), (232087, 52598771), (232478,
  52597928), (232872, 52597091), (233272, 52596262), (233675, 52595441), (234082, 52594626),
  (234494, 52593819), (234910, 52593020), (235330, 52592226), (235754, 52591439), (236183,
  52590661), (236615, 52589888), (237051, 52589123), (237493, 52588365), (237937, 52587612),
  (238386, 52586867), (238840, 52586129), (239297, 52585397), (239758, 52584671), (240225,
  52583953), (240695, 52583240), (241168, 52582534), (241647, 52581836), (242130, 52581143),
  (242616, 52580455), (243107, 52579776), (243602, 52579102), (244100, 52578432), (244604,
  52577772), (245112, 52577117), (245622, 52576466), (246139, 52575824), (246658, 52575187),
  (247181, 52574555), (247709, 52573930), (248241, 52573311), (248777, 52572697), (249317,
  52572089), (249861, 52571488), (250409, 52570891), (250961, 52570300), (251518, 52569716),
  (252077, 52569136), (252641, 52568563), (253210, 52567996), (253781, 52567433), (254357,
  52566875), (254937, 52566324), (255521, 52565778), (256108, 52565237), (256700, 52564702),
  (257295, 52564171), (257894, 52563646), (258498, 52563127), (259105, 52562613), (259715,
  52562103), (260330, 52561600), (260949, 52561100), (261570, 52560605), (262197, 52560118),
  (262826, 52559634), (263459, 52559153), (264096, 52558680), (264737, 52558211), (265381,
  52557746), (266029, 52557287), (266681, 52556833), (267336, 52556382), (267994, 52555937) ]
/-- Part 0 (`900` `(u0, v)` pairs) of the `T = 2,700` `(1, 2)` schedule. -/
def ltM1K2Part0 : List (ℤ × ℤ) :=
  ltM1K2RawChunk0 ++ ltM1K2RawChunk1 ++ ltM1K2RawChunk2 ++ ltM1K2RawChunk3 ++
  ltM1K2RawChunk4 ++ ltM1K2RawChunk5 ++ ltM1K2RawChunk6 ++ ltM1K2RawChunk7 ++
  ltM1K2RawChunk8 ++ ltM1K2RawChunk9
/-- Part 1 (`900` `(u0, v)` pairs) of the `T = 2,700` `(1, 2)` schedule. -/
def ltM1K2Part1 : List (ℤ × ℤ) :=
  ltM1K2RawChunk10 ++ ltM1K2RawChunk11 ++ ltM1K2RawChunk12 ++ ltM1K2RawChunk13 ++
  ltM1K2RawChunk14 ++ ltM1K2RawChunk15 ++ ltM1K2RawChunk16 ++ ltM1K2RawChunk17 ++
  ltM1K2RawChunk18 ++ ltM1K2RawChunk19
/-- Part 2 (`900` `(u0, v)` pairs) of the `T = 2,700` `(1, 2)` schedule. -/
def ltM1K2Part2 : List (ℤ × ℤ) :=
  ltM1K2RawChunk20 ++ ltM1K2RawChunk21 ++ ltM1K2RawChunk22 ++ ltM1K2RawChunk23 ++
  ltM1K2RawChunk24 ++ ltM1K2RawChunk25 ++ ltM1K2RawChunk26 ++ ltM1K2RawChunk27 ++
  ltM1K2RawChunk28 ++ ltM1K2RawChunk29
/-- Full `2,700`-pulse `(u0, v)` schedule assembled from three `900`-pulse parts. -/
def ltM1K2RawPairs : List (ℤ × ℤ) := ltM1K2Part0 ++ (ltM1K2Part1 ++ ltM1K2Part2)
theorem ltM1K2MapPulses_valid (ps : List (ℤ × ℤ)) :
    (ps.map ltM1K2MkPulse).all swLPulseValid = true := by
  rw [List.all_map]; refine List.all_eq_true.2 fun uv _ ↦ ?_
  simp [ltM1K2MkPulse, swLPulseValid]
/-- Initial `10^100`-scale `(1, 0, 0, 0, 0, 0)` conveyor state tuple. -/
def ltM1K2Init100 : LtM1K2State100 :=
  let zIv : TcIv := (Int.ofNat 0, Int.ofNat 0)
  ((tcAmpScale, tcAmpScale), zIv, zIv, zIv, zIv, zIv)
/-- Full `10^100`-scale `L = 2` trajectory evolution starting from `(1, 0, 0, 0, 0, 0)`. -/
def ltM1K2Evol100 (csPair : (TcIv × TcIv) × (TcIv × TcIv)) (ps : List (ℤ × ℤ)) : LtM1K2State100 :=
  ltM1K2EvolFrom100 csPair ltM1K2Init100 ps
/-- Pre-evaluated `10^100`-scale `(cos, sin)` intervals for `w = 0, 1`. -/
def ltM1K2TrigPairLit : (TcIv × TcIv) × (TcIv × TcIv) :=
  (((Int.ofNat
        (Nat.add (Nat.mul 9999875000260415449655850844427276280454 ltM1K2Dec60)
          588020179353530107694465030269593730629622751248953297708436),
     Int.ofNat
        (Nat.add (Nat.mul 9999875000260416449654065132933601956670 ltM1K2Dec60)
          78374779953827630164738606709446799366358209668094947423389)),
    (Int.ofNat
        (Nat.add (Nat.mul 49999791666927081511660569689486861309 ltM1K2Dec60)
          349659832881169924594537742483969604647614199852669117890234),
     Int.ofNat
        (Nat.add (Nat.mul 49999791667127082344991571678752036837 ltM1K2Dec60)
          771647497558316674031608139754837282820470921025522511391798))),
   ((Int.ofNat
        (Nat.add (Nat.mul 9999937500065103635567522581747295470714 ltM1K2Dec60)
          165694422515630645271394340414505251524743390878868021986163),
     Int.ofNat
        (Nat.add (Nat.mul 9999937500065104142638137652720152506210 ltM1K2Dec60)
          157013401888500710560686886816023267554415246926586201929345)),
    (Int.ofNat
        (Nat.add (Nat.mul 35355265402416161393220033471531964232 ltM1K2Dec60)
          365170267596835293386950964347101859516753613208447082812304),
     Int.ofNat
        (Nat.add (Nat.mul 35355265402559583048251421677380553821 ltM1K2Dec60)
          438680636672280609943121474974448267434775082496863358781062))))
/-- Chained `10^100`-scale state checkpoint at pulse `900`. -/
def ltM1K2Ckpt0 : LtM1K2State100 :=
  ((Int.ofNat
      (Nat.add (Nat.mul 162284910926071640346191520346474852907 ltM1K2Dec60)
        642094570032776641300837813259520602583754041300889545395295),
   Int.ofNat
      (Nat.add (Nat.mul 162284915333138252088754666586666945788 ltM1K2Dec60)
        642331666201372292743407844951132266738904044700306448459509)),
  (Int.ofNat
      (Nat.add (Nat.mul 161460212362522486877445447052682642491 ltM1K2Dec60)
        475909782224913366758126772367790013611780107199234713312033),
   Int.ofNat
      (Nat.add (Nat.mul 161460217094879304750968984450965166012 ltM1K2Dec60)
        267593677185114900931132602876661322683063593422576611956243)),
  (Int.ofNat
      (Nat.add (Nat.mul 1453995059275736407390756426325363410793 ltM1K2Dec60)
        212639494193951504229170677616286016770315728465603762607466),
   Int.ofNat
      (Nat.add (Nat.mul 1453995061370651730187586817349866023920 ltM1K2Dec60)
        432325680271202376515996381072944935577660165009428009974771)),
  (Int.ofNat
      (Nat.add (Nat.mul 1448366372207612715176617581088623438682 ltM1K2Dec60)
        810322158373305686603756217111449711009620947546337684403661),
   Int.ofNat
      (Nat.add (Nat.mul 1448366372903211066321431268308756581300 ltM1K2Dec60)
        7481059968627754171184398126509330813572716521821486231499)),
  (Int.ofNat
      (Nat.add (Nat.mul 9573572741521640241051950776676704010041 ltM1K2Dec60)
        117389282417540265712608822024959491342889155234787927864187),
   Int.ofNat
      (Nat.add (Nat.mul 9573572742765701243157113523271411106741 ltM1K2Dec60)
        12784047413074977848340969527667502904990627581030946912319)),
  (Int.ofNat
      (Nat.add (Nat.mul 5697332792370715447879083654122757345886634 ltM1K2Dec60)
        737912816053689863789036217658500164882738318130797861664819),
   Int.ofNat
      (Nat.add (Nat.mul 5697332792661110788655549930528244359765413 ltM1K2Dec60)
        913355227412949057866982661900457579563949016116470460596016)))
/-- Chained `10^100`-scale state checkpoint at pulse `1800`. -/
def ltM1K2Ckpt1 : LtM1K2State100 :=
  ((Int.ofNat
      (Nat.add (Nat.mul 1858001686645973296599738534943930940 ltM1K2Dec60)
        643821320663541659766590398875251813607360449164581321728898),
   Int.ofNat
      (Nat.add (Nat.mul 1858435723831743603381672674419672078 ltM1K2Dec60)
        101173003051053925324360160943210021255715399503252672558265)),
  (Int.ofNat
      (Nat.add (Nat.mul 1870109353342845515098435163945441652 ltM1K2Dec60)
        97947654584357811399390917178699772557216702175731104798073),
   Int.ofNat
      (Nat.add (Nat.mul 1870545411100029686722816554385627011 ltM1K2Dec60)
        50203005730860508218087064546685729781995051323447964176084)),
  (Int.ofNat
      (Nat.add (Nat.mul 62878901376542645900395777625349419951 ltM1K2Dec60)
        851642448447266376937320421247025492513561785776432819709981),
   Int.ofNat
      (Nat.add (Nat.mul 62878953152095249811563415961209157095 ltM1K2Dec60)
        944902465261375059368723633710666220167942867411092198273497)),
  (Int.ofNat
      (Nat.add (Nat.mul 59712190766479533653725785406660893211 ltM1K2Dec60)
        824031017485293596461397882076058738926509626468628674466083),
   Int.ofNat
      (Nat.add (Nat.mul 59712207841603438549781066734230154777 ltM1K2Dec60)
        667114951956659334445040018957906362749757889511386418580932)),
  (Int.ofNat
      (Nat.add (Nat.mul 9999247372277716411897179643058457752816 ltM1K2Dec60)
        591786121253114229385309953706441932796108979881323822654283),
   Int.ofNat
      (Nat.add (Nat.mul 9999247376254101564813637587156919412477 ltM1K2Dec60)
        933664069237577618011403549713286475967005328471473890530970)),
  (Int.ofNat
      (Nat.add (Nat.mul 5759025891480550761046139475917589990815297 ltM1K2Dec60)
        119018506607691296258518055689835632945532680621836350004667),
   Int.ofNat
      (Nat.add (Nat.mul 5759025894098607306106990104526233198914399 ltM1K2Dec60)
        902157062116921996886119782219491331665922079692398571823457)))
/-- Chained `10^100`-scale state checkpoint at pulse `2700`. -/
def ltM1K2Ckpt2 : LtM1K2State100 :=
  ((Int.ofNat
      (Nat.add (Nat.mul 90208404035787201984510098212261362 ltM1K2Dec60)
        512638847484615885934624678977721910679984097570156110039613),
   Int.ofNat
      (Nat.add (Nat.mul 128851306489618273519131370485104242 ltM1K2Dec60)
        255139268342067353822894363223800777544672066612181272773562)),
  (Int.ofNat
      (Nat.add (Nat.mul 11191610831119081604444654545365563 ltM1K2Dec60)
        844900069682526020438836254348635547087663745879856747624313),
   Int.ofNat
      (Nat.add (Nat.mul 49994953153463412965541321664842525 ltM1K2Dec60)
        442376249799309408047382068653385630295381000139413844956927)),
  (ltM1K2NegNat
      (Nat.add (Nat.mul 31773623263427183463699385815339160 ltM1K2Dec60)
        600517642349636264208795030212233721779471258770017864353140),
   ltM1K2NegNat
      (Nat.add (Nat.mul 27889432777039619966378557064734550 ltM1K2Dec60)
        953762182597213342980894718634934534600309154507004323863379)),
  (Int.ofNat
      (Nat.add (Nat.mul 2588530038097050993245979192765477442 ltM1K2Dec60)
        530811657273218938998664836042722166457508455423614600095194),
   Int.ofNat
      (Nat.add (Nat.mul 2589690440501665376902807888255991855 ltM1K2Dec60)
        307594757801976017022780674377071777902695074296598693258001)),
  (Int.ofNat
      (Nat.add (Nat.mul 9999999324521303728359772565350349086692 ltM1K2Dec60)
        744270614562747001879698983253328811530050843312585015624060),
   Int.ofNat
      (Nat.add (Nat.mul 9999999332015859824557153122758678142762 ltM1K2Dec60)
        938364473846112490665658676788018114354639703295521311504625)),
  (Int.ofNat
      (Nat.add (Nat.mul 5759138653738824833805481276819211120653899 ltM1K2Dec60)
        453770690257658322606204388515590122103586828299914759534928),
   Int.ofNat
      (Nat.add (Nat.mul 5759138661275140353767395120391746721201095 ltM1K2Dec60)
        437662864381835002813396691790610222627642882082185055892420)))
/-- Concrete `10^9`-scale terminal state interval list `[s0, s1, s2, s3]`. -/
abbrev ltM1K2CertStIvs9 : List IvInt :=
  [(9020, 12886), (1119, 5000), (-3178, -2788), (258853, 258970)]
/-- Concrete `10^9`-scale terminal cumulative click probability interval. -/
def ltM1K2CertCumIv9 : IvInt := (999999932, 999999934)
/-- Concrete `10^9`-scale terminal expected survival-pulse interval. -/
def ltM1K2CertSurvIv9 : IvInt := (575913865373, 575913866128)
/-- Certified `10^9`-scale hit-tail lower bounds `[P(H >= 1), P(H >= 2)]`. -/
def ltM1K2TailLbs : List ℤ := [999999998, 999999997]
/-- Certified `10^9`-scale upper bound on expected survival pulses per attempt. -/
def ltM1K2SurvUb : ℤ := 575913866128
/-- Certified `10^16`-scale potential `V_2 * 10^16 / sqrt(2^n)` at `(m = 1, k = 2)`. -/
def ltM1K2V2_16 : ℤ := 10180815029781141
/-- Coprime numerator of `relCost(1, 2)`. -/
def ltM1K2RelNum : ℕ := 379666241046199
/-- Coprime denominator of `relCost(1, 2)`. -/
def ltM1K2RelDen : ℕ := 500000000000000
/-- Constructor-level `IvInt` equality check avoiding Mathlib `DecidableEq` in `decide
  +kernel`. -/
def ltM1K2BeqIv (a b : IvInt) : Bool := beqZ a.1 b.1 && beqZ a.2 b.2
theorem ltM1K2BeqIv_eq_true_iff (a b : IvInt) : ltM1K2BeqIv a b = true ↔ a = b := by
  unfold ltM1K2BeqIv; rw [Bool.and_eq_true, beqZ_eq_true_iff, beqZ_eq_true_iff]
  cases a; cases b; simp
/-- Constructor-level equality check on `(TcIv × TcIv) × (TcIv × TcIv)`. -/
def ltM1K2BeqTrigPair (a b : (TcIv × TcIv) × (TcIv × TcIv)) : Bool :=
  ltM1K2BeqIv a.1.1 b.1.1 && ltM1K2BeqIv a.1.2 b.1.2 &&
  ltM1K2BeqIv a.2.1 b.2.1 && ltM1K2BeqIv a.2.2 b.2.2
private theorem ltM1K2BeqTrigPair_eq_true_iff (a b : (TcIv × TcIv) × (TcIv × TcIv)) :
    ltM1K2BeqTrigPair a b = true ↔ a = b := by
  unfold ltM1K2BeqTrigPair; simp only [Bool.and_eq_true, ltM1K2BeqIv_eq_true_iff]
  rcases a with ⟨⟨a00, a01⟩, ⟨a10, a11⟩⟩; rcases b with ⟨⟨b00, b01⟩, ⟨b10, b11⟩⟩
  simp only [Prod.mk.injEq, and_assoc]
/-- Constructor-level equality check on `LtM1K2State100`. -/
def ltM1K2BeqState100 (a b : LtM1K2State100) : Bool :=
  ltM1K2BeqIv a.1 b.1 &&
  ltM1K2BeqIv a.2.1 b.2.1 &&
  ltM1K2BeqIv a.2.2.1 b.2.2.1 &&
  ltM1K2BeqIv a.2.2.2.1 b.2.2.2.1 &&
  ltM1K2BeqIv a.2.2.2.2.1 b.2.2.2.2.1 &&
  ltM1K2BeqIv a.2.2.2.2.2 b.2.2.2.2.2
private theorem ltM1K2BeqState100_eq_true_iff (a b : LtM1K2State100) :
    ltM1K2BeqState100 a b = true ↔ a = b := by
  unfold ltM1K2BeqState100; simp only [Bool.and_eq_true, ltM1K2BeqIv_eq_true_iff]
  rcases a with ⟨a0, a1, a2, a3, a4, a5⟩; rcases b with ⟨b0, b1, b2, b3, b4, b5⟩
  simp only [Prod.mk.injEq, and_assoc]
/-- Check one `900`-pulse `10^100`-scale trajectory segment from `stIn` to `stOut`. -/
def ltM1K2CheckPart100 (csPair : (TcIv × TcIv) × (TcIv × TcIv))
    (stIn : LtM1K2State100) (ps : List (ℤ × ℤ)) (stOut : LtM1K2State100) : Bool :=
  ltM1K2BeqState100 (ltM1K2EvolFrom100 csPair stIn ps) stOut
/-- Check `10^100 -> 10^9` outward projection of terminal state `st` against `10^9`
  intervals. -/
def ltM1K2CheckProj9 (st : LtM1K2State100) (i0 i1 i2 i3 icum isurv : IvInt) : Bool :=
  match st with
  | (s0, s1, s2, s3, cum, surv) =>
      ltM1K2BeqIv (ltM1K2Iv100To9 s0) i0 &&
      ltM1K2BeqIv (ltM1K2Iv100To9 s1) i1 &&
      ltM1K2BeqIv (ltM1K2Iv100To9 s2) i2 &&
      ltM1K2BeqIv (ltM1K2Iv100To9 s3) i3 &&
      ltM1K2BeqIv (ltM1K2Iv100To9 cum) icum &&
      ltM1K2BeqIv (ltM1K2Iv100To9 surv) isurv
/-- Pure-primitive `10^100` trajectory enclosure check against `10^9`-scale target
  intervals. -/
def ltM1K2CheckEvol9 (csPair : (TcIv × TcIv) × (TcIv × TcIv)) (ps : List (ℤ × ℤ))
    (i0 i1 i2 i3 icum isurv : IvInt) : Bool :=
  ltM1K2CheckProj9 (ltM1K2Evol100 csPair ps) i0 i1 i2 i3 icum isurv
theorem ltM1K2CheckEvol9_sound {cs : Fin 2 → ℝ × ℝ} {csPair : (TcIv × TcIv) × (TcIv × TcIv)} (hcs :
    (tcMemAmpIv (cs ⟨0, by decide⟩).1 csPair.1.1 ∧ tcMemAmpIv (cs ⟨0, by decide⟩).2 csPair.1.2) ∧
    (tcMemAmpIv (cs ⟨1, by decide⟩).1 csPair.2.1 ∧ tcMemAmpIv (cs ⟨1, by decide⟩).2 csPair.2.2)) (ps
    : List (ℤ × ℤ)) {i0 i1 i2 i3 icum isurv : IvInt} (hchk : ltM1K2CheckEvol9 csPair ps i0 i1 i2 i3
    icum isurv = true) :
    let out := swLEvolutionReal 2 (by omega) cs (ps.map ltM1K2MkPulse)
    memIvIntVec out.1 [i0, i1, i2, i3] ∧ memIvInt out.2.1 icum ∧ memIvInt out.2.2 isurv := by
  intro out
  have hevol := ltM1K2Evol100Aux_sound (cs := cs) hcs.1 hcs.2 ps (st := fun j : Fin 4 ↦ if j.1 = 0
    then 1 else 0) (cumR := 0) (survR := 0) ltM1K2_tcMemAmpIv_one ltM1K2_tcMemAmpIv_zero
    ltM1K2_tcMemAmpIv_zero ltM1K2_tcMemAmpIv_zero ltM1K2_tcMemAmpIv_zero ltM1K2_tcMemAmpIv_zero
  rcases hevol with ⟨h0, h1, h2, h3, hcum, hsurv⟩
  unfold ltM1K2CheckEvol9 ltM1K2CheckProj9 ltM1K2Evol100 ltM1K2EvolFrom100 ltM1K2Init100 at hchk
  simp only [Bool.and_eq_true, ltM1K2BeqIv_eq_true_iff] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨hs0, hs1⟩, hs2⟩, hs3⟩, hcum_eq⟩, hsurv_eq⟩
  have hm0 : memIvInt (out.1 ⟨0, by omega⟩) i0 := hs0 ▸ ltM1K2_memIvInt_of_tcMemAmpIv h0
  have hm1 : memIvInt (out.1 ⟨1, by omega⟩) i1 := hs1 ▸ ltM1K2_memIvInt_of_tcMemAmpIv h1
  have hm2 : memIvInt (out.1 ⟨2, by omega⟩) i2 := hs2 ▸ ltM1K2_memIvInt_of_tcMemAmpIv h2
  have hm3 : memIvInt (out.1 ⟨3, by omega⟩) i3 := hs3 ▸ ltM1K2_memIvInt_of_tcMemAmpIv h3
  have hmcum : memIvInt out.2.1 icum := hcum_eq ▸ ltM1K2_memIvInt_of_tcMemAmpIv hcum
  have hmsurv : memIvInt out.2.2 isurv := hsurv_eq ▸ ltM1K2_memIvInt_of_tcMemAmpIv hsurv
  refine ⟨⟨rfl, fun j ↦ ?_⟩, hmcum, hmsurv⟩
  fin_cases j
  · exact hm0
  · exact hm1
  · exact hm2
  · exact hm3
private theorem ltM1K2_proj9_cert :
    ltM1K2CheckProj9 ltM1K2Ckpt2
      (9020, 12886) (1119, 5000) (-3178, -2788) (258853, 258970)
      ltM1K2CertCumIv9 ltM1K2CertSurvIv9 = true := rfl
/-- Stage value table `0 -> 0, 1 -> 6426990820000000, r >= 2 -> ltM1K2V2_16` at `10^16`
  scale. -/
def ltM1K2VTable : ℕ → ℤ
  | 0 => 0
  | 1 => 6426990820000000
  | _ => ltM1K2V2_16
/-- Pure-integer `10^9`-scale hit-tail clamping check for `(m = 1, k = 2)`. -/
def ltM1K2CheckClamp : Bool :=
  let p0Iv := ivAddInt (swLOrbSqIv ltM1K2CertStIvs9 0) (ivMulInt ltM1K2CertCumIv9 (0, swOrbPad))
  let t1Iv := ivSubInt (swScale, swScale) p0Iv
  let tailIvs := t1Iv :: swLTailSuffixIvs 2 ltM1K2CertStIvs9 ltM1K2CertCumIv9 1
  let certLbs := swLClampTailLbs tailIvs
  decide (ltM1K2CertSurvIv9.2 ≤ ltM1K2SurvUb) &&
  decide (certLbs.length = 2) &&
  (List.range 2).all fun i ↦ decide (ltM1K2TailLbs.getD i 0 ≤ certLbs.getD i 0)
private def ltM1K2Base18 : ℕ := 1000000000000000000
private def ltM1K2Tbl18 : List ℕ → ℕ
  | [] => 0
  | d :: ds => Nat.add d (Nat.mul ltM1K2Base18 (ltM1K2Tbl18 ds))
private def ltM1K2Mid0 : LtM1K2State100 :=
  ((Int.ofNat (ltM1K2Tbl18 [991077246977143633, 159572227015595730, 136613438417509834,
      517586855878458997, 990022718149375389, 1540465705]),
    Int.ofNat (ltM1K2Tbl18 [102312669854514581, 881440405160991919, 988443445327022641,
      552991136979157236, 305243750684844150, 1540465706])),
   (Int.ofNat (ltM1K2Tbl18 [880040041566065777, 221945426450201159, 199809896879144090,
      647327522804137568, 920969765927980435, 1532267317]),
    Int.ofNat (ltM1K2Tbl18 [492898352717961575, 698341375275129986, 546663252100998912,
      793894157247566948, 350867687673341883, 1532267318])),
   (Int.ofNat (ltM1K2Tbl18 [362867484340495481, 779929316216760701, 754612486896641243,
      109250439235694860, 698720219177622081, 6252399724]),
    Int.ofNat (ltM1K2Tbl18 [193037200360831029, 24357909837302902, 223021330140160831,
      584277573864836056, 41092910192987880, 6252399725])),
   (Int.ofNat (ltM1K2Tbl18 [423004782622880024, 938756736120599188, 155977668588454128,
      615301372924290078, 344220902832193584, 6232435150]),
    Int.ofNat (ltM1K2Tbl18 [335779057897543895, 974889904533822958, 717768718392283244,
      680271218797210532, 494938842631841556, 6232435150])),
   (Int.ofNat (ltM1K2Tbl18 [821193028702985739, 411463594247857290, 714162246651035723,
      344663435419730644, 982798108443360473, 1734337204]),
    Int.ofNat (ltM1K2Tbl18 [686621835845812748, 566223242319231230, 341663249012910187,
      237769027689559289, 60565576299279985, 1734337205])),
   (Int.ofNat (ltM1K2Tbl18 [567475176376811622, 521247916958190629, 145314111689881513,
      577054188423289840, 649260091712071713, 4472444707179]),
    Int.ofNat (ltM1K2Tbl18 [327026687077602844, 769475739660054755, 454319792466692487,
      122316551378442523, 853442994594810545, 4472444707180])))
private def ltM1K2Mid1 : LtM1K2State100 :=
  ((Int.ofNat (ltM1K2Tbl18 [381669982208964855, 708841319272028308, 306735951988105775,
      126154868402744084, 838866140299215378, 16954149]),
    Int.ofNat (ltM1K2Tbl18 [465962031655173657, 959087939797832147, 309663411603868291,
      993217878011988856, 46630852024902506, 16954195])),
   (Int.ofNat (ltM1K2Tbl18 [629847839625313171, 721301586506170638, 375066454270869266,
      147742277314991709, 17449721173054783, 17001884]),
    Int.ofNat (ltM1K2Tbl18 [835983103508317587, 609365939121891738, 363885680936330325,
      454328296461715394, 65865599200446725, 17001930])),
   (Int.ofNat (ltM1K2Tbl18 [73485221203597050, 750395242047392543, 307066128007958180,
      130329513965494774, 776150179957588288, 305703582]),
    Int.ofNat (ltM1K2Tbl18 [39044187134419656, 296594917077452138, 814218096534201607,
      846033758807319965, 468809443262915591, 305703593])),
   (Int.ofNat (ltM1K2Tbl18 [189600919649101913, 387645369821392507, 196596405191147895,
      362257063737720230, 726804401033546778, 303062041]),
    Int.ofNat (ltM1K2Tbl18 [940188552336812447, 527071100949429692, 701226429094636462,
      722917856952717968, 262354366289501464, 303062045])),
   (Int.ofNat (ltM1K2Tbl18 [944843247054100960, 473516658419962012, 561002403494866328,
      300862317440166241, 231101730947465543, 9981412219]),
    Int.ofNat (ltM1K2Tbl18 [327907995708053139, 223922888130008684, 718128105568087548,
      346677830625688462, 808030124949040768, 9981412221])),
   (Int.ofNat (ltM1K2Tbl18 [865656420812774391, 145445126741712886, 727541019483883722,
      969471939305834192, 314748971061048329, 5756472427644]),
    Int.ofNat (ltM1K2Tbl18 [818428357065914008, 855023865724321006, 948616385523535034,
      432827226505966573, 840096150898319059, 5756472428789])))
private def ltM1K2Mid2 : LtM1K2State100 :=
  ((Int.ofNat (ltM1K2Tbl18 [309306899309961055, 468872161816193022, 988621592341358470,
      202918952551591276, 927865910726790417, 342252]),
    Int.ofNat (ltM1K2Tbl18 [422840148009938996, 957739068969026557, 210886021729775944,
      221100267282082387, 995714739192938903, 346349])),
   (Int.ofNat (ltM1K2Tbl18 [716335839283131282, 322777439028458961, 275474646684915275,
      626886860088683119, 806480515671773597, 332357]),
    Int.ofNat (ltM1K2Tbl18 [691034660922738236, 42883161844727682, 279751468525857279,
      141879349771753447, 862389927803318021, 336458])),
   (Int.ofNat (ltM1K2Tbl18 [435088320683891412, 910706086684382190, 662735215584763275,
      724406480312471107, 532842233322418926, 12335432]),
    Int.ofNat (ltM1K2Tbl18 [536011808138987482, 37448933200623840, 841099205863812437,
      874286395923640125, 410945071841324599, 12335668])),
   (Int.ofNat (ltM1K2Tbl18 [92422453861037759, 467747083267476376, 725800453831224269,
      282549853289689392, 835842454880049410, 15215034]),
    Int.ofNat (ltM1K2Tbl18 [402494712097418658, 454811338299312932, 841127609804639315,
      483053113782898984, 884657074160983513, 15215124])),
   (Int.ofNat (ltM1K2Tbl18 [693804590095301821, 799677206957532320, 431845097497890788,
      89012854299091305, 833435269993010573, 9999961607]),
    Int.ofNat (ltM1K2Tbl18 [329371180889930104, 586919339141565535, 123001005845980166,
      287708424523995797, 199959634974168655, 9999961613])),
   (Int.ofNat (ltM1K2Tbl18 [951393687252414290, 629663392168731962, 523643415404028942,
      144072954741458020, 456061077956019174, 5759133854442]),
    Int.ofNat (ltM1K2Tbl18 [463390486149317610, 317885359992097680, 16248846063268441,
      372470580507278756, 19263442812239414, 5759133859154])))
private def ltM1K2Seg0a : List (ℤ × ℤ) :=
  ltM1K2RawChunk0 ++ ltM1K2RawChunk1 ++ ltM1K2RawChunk2 ++
  ltM1K2RawChunk3 ++ ltM1K2RawChunk4
private def ltM1K2Seg0b : List (ℤ × ℤ) :=
  ltM1K2RawChunk5 ++ ltM1K2RawChunk6 ++ ltM1K2RawChunk7 ++
  ltM1K2RawChunk8 ++ ltM1K2RawChunk9
private def ltM1K2Seg1a : List (ℤ × ℤ) :=
  ltM1K2RawChunk10 ++ ltM1K2RawChunk11 ++ ltM1K2RawChunk12 ++
  ltM1K2RawChunk13 ++ ltM1K2RawChunk14
private def ltM1K2Seg1b : List (ℤ × ℤ) :=
  ltM1K2RawChunk15 ++ ltM1K2RawChunk16 ++ ltM1K2RawChunk17 ++
  ltM1K2RawChunk18 ++ ltM1K2RawChunk19
private def ltM1K2Seg2a : List (ℤ × ℤ) :=
  ltM1K2RawChunk20 ++ ltM1K2RawChunk21 ++ ltM1K2RawChunk22 ++
  ltM1K2RawChunk23 ++ ltM1K2RawChunk24
private def ltM1K2Seg2b : List (ℤ × ℤ) :=
  ltM1K2RawChunk25 ++ ltM1K2RawChunk26 ++ ltM1K2RawChunk27 ++
  ltM1K2RawChunk28 ++ ltM1K2RawChunk29
private theorem ltM1K2_part0_eq : ltM1K2Part0 = ltM1K2Seg0a ++ ltM1K2Seg0b := by
  simp only [ltM1K2Part0, ltM1K2Seg0a, ltM1K2Seg0b, List.append_assoc]
private theorem ltM1K2_part1_eq : ltM1K2Part1 = ltM1K2Seg1a ++ ltM1K2Seg1b := by
  simp only [ltM1K2Part1, ltM1K2Seg1a, ltM1K2Seg1b, List.append_assoc]
private theorem ltM1K2_part2_eq : ltM1K2Part2 = ltM1K2Seg2a ++ ltM1K2Seg2b := by
  simp only [ltM1K2Part2, ltM1K2Seg2a, ltM1K2Seg2b, List.append_assoc]
private def ltM1K2CheckMetaAndStep : Bool :=
  ltM1K2BeqTrigPair ltM1K2TrigPair100 ltM1K2TrigPairLit &&
  (ltM1K2CheckClamp &&
   checkSwLM1StepTable 2 2 5000000 1000000000 2
     ltM1K2TailLbs ltM1K2SurvUb multiUnitScale ltM1K2VTable)
private def ltM1K2CheckAll7 : Bool :=
  ltM1K2CheckPart100 ltM1K2TrigPairLit ltM1K2Init100 ltM1K2Seg0a ltM1K2Mid0 &&
  (ltM1K2CheckPart100 ltM1K2TrigPairLit ltM1K2Mid0 ltM1K2Seg0b ltM1K2Ckpt0 &&
  (ltM1K2CheckPart100 ltM1K2TrigPairLit ltM1K2Ckpt0 ltM1K2Seg1a ltM1K2Mid1 &&
  (ltM1K2CheckPart100 ltM1K2TrigPairLit ltM1K2Mid1 ltM1K2Seg1b ltM1K2Ckpt1 &&
  (ltM1K2CheckPart100 ltM1K2TrigPairLit ltM1K2Ckpt1 ltM1K2Seg2a ltM1K2Mid2 &&
  (ltM1K2CheckPart100 ltM1K2TrigPairLit ltM1K2Mid2 ltM1K2Seg2b ltM1K2Ckpt2 &&
   ltM1K2CheckMetaAndStep)))))
private theorem ltM1K2_all7_cert : ltM1K2CheckAll7 = true := by decide +kernel
private theorem ltM1K2_meta_step_cert : ltM1K2CheckMetaAndStep = true :=
  ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp
    ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp
      ((Bool.and_eq_true _ _).mp ltM1K2_all7_cert).2).2).2).2).2).2
theorem ltM1K2_traj100_cert : ltM1K2CheckEvol9 ltM1K2TrigPair100 ltM1K2RawPairs (9020, 12886) (1119,
    5000) (-3178, -2788) (258853, 258970) ltM1K2CertCumIv9 ltM1K2CertSurvIv9 = true := by
  have c1 := (Bool.and_eq_true _ _).mp ltM1K2_all7_cert
  have c2 := (Bool.and_eq_true _ _).mp c1.2
  have c3 := (Bool.and_eq_true _ _).mp c2.2
  have c4 := (Bool.and_eq_true _ _).mp c3.2
  have c5 := (Bool.and_eq_true _ _).mp c4.2
  have c6 := (Bool.and_eq_true _ _).mp c5.2
  have htrig : ltM1K2TrigPair100 = ltM1K2TrigPairLit :=
    (ltM1K2BeqTrigPair_eq_true_iff _ _).1 ((Bool.and_eq_true _ _).mp c6.2).1
  have hs0a := (ltM1K2BeqState100_eq_true_iff _ _).1 c1.1
  have hs0b := (ltM1K2BeqState100_eq_true_iff _ _).1 c2.1
  have hp0 : ltM1K2EvolFrom100 ltM1K2TrigPairLit ltM1K2Init100 ltM1K2Part0 = ltM1K2Ckpt0 := by
    rw [ltM1K2_part0_eq, ltM1K2EvolFrom100_append, hs0a, hs0b]
  have hs1a := (ltM1K2BeqState100_eq_true_iff _ _).1 c3.1
  have hs1b := (ltM1K2BeqState100_eq_true_iff _ _).1 c4.1
  have hp1 : ltM1K2EvolFrom100 ltM1K2TrigPairLit ltM1K2Ckpt0 ltM1K2Part1 = ltM1K2Ckpt1 := by
    rw [ltM1K2_part1_eq, ltM1K2EvolFrom100_append, hs1a, hs1b]
  have hs2a := (ltM1K2BeqState100_eq_true_iff _ _).1 c5.1
  have hs2b := (ltM1K2BeqState100_eq_true_iff _ _).1 c6.1
  have hp2 : ltM1K2EvolFrom100 ltM1K2TrigPairLit ltM1K2Ckpt1 ltM1K2Part2 = ltM1K2Ckpt2 := by
    rw [ltM1K2_part2_eq, ltM1K2EvolFrom100_append, hs2a, hs2b]
  have hev : ltM1K2Evol100 ltM1K2TrigPair100 ltM1K2RawPairs = ltM1K2Ckpt2 := by
    rw [htrig]; change ltM1K2EvolFrom100 ltM1K2TrigPairLit ltM1K2Init100
      (ltM1K2Part0 ++ (ltM1K2Part1 ++ ltM1K2Part2)) = ltM1K2Ckpt2
    rw [ltM1K2EvolFrom100_append, hp0, ltM1K2EvolFrom100_append, hp1, hp2]
  unfold ltM1K2CheckEvol9; rw [hev]; exact ltM1K2_proj9_cert
private theorem ltM1K2_cs_pair :
    (ltM1K2CheckClamp && checkSwLM1StepTable 2 2 5000000 1000000000 2
      ltM1K2TailLbs ltM1K2SurvUb multiUnitScale ltM1K2VTable) = true :=
  ((Bool.and_eq_true _ _).mp ltM1K2_meta_step_cert).2
theorem ltM1K2_clamp_cert : ltM1K2CheckClamp = true := ((Bool.and_eq_true _ _).mp ltM1K2_cs_pair).1
theorem ltM1K2_step_cert : checkSwLM1StepTable 2 2 5000000 1000000000 2 ltM1K2TailLbs ltM1K2SurvUb
    multiUnitScale ltM1K2VTable = true := ((Bool.and_eq_true _ _).mp ltM1K2_cs_pair).2
/-- Pure-integer `10^16`-scale relative-cost inequality check for `(m = 1, k = 2)`. -/
def ltM1K2CheckRelCost16 : Bool :=
  Nat.ble 1 ltM1K2RelDen &&
  bleZ (ltM1K2V2_16 * 10000000000000000 * (ltM1K2RelDen : ℤ))
    (7853981633974483 * 17071067811865475 * (ltM1K2RelNum : ℤ))
theorem ltM1K2_relCost16_cert : ltM1K2CheckRelCost16 = true := by
  unfold ltM1K2CheckRelCost16 ltM1K2V2_16 ltM1K2RelDen ltM1K2RelNum
  rw [Bool.and_eq_true, Nat.ble_eq, bleZ_eq_true_iff]; norm_num
theorem ltM1K2_relCost16_sound (n : ℕ) : ((ltM1K2V2_16 : ℝ) / (multiUnitScale : ℝ)) * √(2 ^ n : ℝ) ≤
    ((ltM1K2RelNum : ℝ) / (ltM1K2RelDen : ℝ)) * ((π / 4) * (∑ r ∈ Finset.Icc (1 : ℕ) 2, 1 / √(r :
    ℝ)) * √((2 ^ n : ℝ) / (1 : ℝ))) := by
  have hcert := ltM1K2_relCost16_cert; unfold ltM1K2CheckRelCost16 at hcert
  rw [Bool.and_eq_true, Nat.ble_eq, bleZ_eq_true_iff] at hcert; rcases hcert with ⟨hden_pos, hineq⟩
  have hpi4 : (7853981633974483 : ℝ) / 10000000000000000 ≤ π / 4 := (by linarith [Real.pi_gt_d20])
  have hinv_sqrt2 : (7071067811865475 : ℝ) / 10000000000000000 ≤ 1 / √(2 : ℝ) := by
    rw [div_le_div_iff₀ (by norm_num) (Real.sqrt_pos.2 (by positivity))]
    rw [one_mul, ← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 7071067811865475),
      ← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 10000000000000000), ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsum2 : (17071067811865475 : ℝ) / 10000000000000000 ≤
      ∑ r ∈ Finset.Icc (1 : ℕ) 2, 1 / √(r : ℝ) := by
    have hicc : Finset.Icc (1 : ℕ) 2 = {1, 2} := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
    rw [hicc, Finset.sum_pair (by omega)]
    simp only [Nat.cast_one, Real.sqrt_one, div_one, Nat.cast_ofNat]; linarith [hinv_sqrt2]
  have hprod : (7853981633974483 / 10000000000000000 : ℝ) * (17071067811865475 / 10000000000000000 :
    ℝ) ≤ (π / 4) * (∑ r ∈ Finset.Icc (1 : ℕ) 2, 1 / √(r : ℝ)) := mul_le_mul hpi4 hsum2 (by norm_num)
    (by positivity); have hden_r : (0 : ℝ) < (ltM1K2RelDen : ℝ) := Nat.cast_pos.2 hden_pos
  have hcast : (ltM1K2V2_16 : ℝ) * 10000000000000000 * (ltM1K2RelDen : ℝ) ≤
      7853981633974483 * 17071067811865475 * (ltM1K2RelNum : ℝ) := by
    exact_mod_cast hineq
  have hcoef : (ltM1K2V2_16 : ℝ) / (multiUnitScale : ℝ) ≤ ((ltM1K2RelNum : ℝ) / (ltM1K2RelDen :
    ℝ)) * ((7853981633974483 / 10000000000000000 : ℝ) * (17071067811865475 / 10000000000000000 :
    ℝ)) := by
    unfold SchurWeylLCert.multiUnitScale; push_cast; rw [div_le_iff₀ (by norm_num)]
    have hrw : ((ltM1K2RelNum : ℝ) / (ltM1K2RelDen : ℝ)) * ((7853981633974483 / 10000000000000000 :
      ℝ) * (17071067811865475 / 10000000000000000 : ℝ)) * 10000000000000000 = (7853981633974483 *
      17071067811865475 * (ltM1K2RelNum : ℝ)) / (10000000000000000 * (ltM1K2RelDen : ℝ)) := by
      field_simp [hden_r.ne']
    rw [hrw, le_div_iff₀ (by positivity)]; linarith [hcast]
  have hcoef2 : (ltM1K2V2_16 : ℝ) / (multiUnitScale : ℝ) ≤ ((ltM1K2RelNum : ℝ) / (ltM1K2RelDen :
    ℝ)) * ((π / 4) * (∑ r ∈ Finset.Icc (1 : ℕ) 2, 1 / √(r : ℝ))) := hcoef.trans
    (mul_le_mul_of_nonneg_left hprod (by positivity)); rw [div_one]
  calc ((ltM1K2V2_16 : ℝ) / (multiUnitScale : ℝ)) * √(2 ^ n : ℝ) ≤ (((ltM1K2RelNum : ℝ) /
        (ltM1K2RelDen : ℝ)) * ((π / 4) * (∑ r ∈ Finset.Icc (1 : ℕ) 2, 1 / √(r : ℝ)))) * √(2 ^ n : ℝ)
        := mul_le_mul_of_nonneg_right hcoef2 (Real.sqrt_nonneg _)
    _ = ((ltM1K2RelNum : ℝ) / (ltM1K2RelDen : ℝ)) *
          ((π / 4) * (∑ r ∈ Finset.Icc (1 : ℕ) 2, 1 / √(r : ℝ)) * √(2 ^ n : ℝ)) := by ring
theorem ltM1K2_bellman_of_enclosure {n : ℕ} (hn96 : 96 ≤ n) (M : Fin (2 * 2) → Fin (2 * 2) → ℝ) (hM
    : IsValidSwLOverlap M) (out : (Fin (2 * 2) → ℝ) × ℝ × ℝ) (hcons : swLNormSq out.1 + out.2.1 = 1)
    (hcum0 : 0 ≤ out.2.1) (hst_mem : memIvIntVec out.1 ltM1K2CertStIvs9) (hcum_mem : memIvInt
    out.2.1 ltM1K2CertCumIv9) (hsurv_mem : memIvInt out.2.2 ltM1K2CertSurvIv9) :
    let K_blk := hdistLKBlk n 2 5000000 1000000000
    let p : ℕ → ℝ := swLAttemptProbReal 2 (by omega) M out.1 out.2.1
    let pSucc : ℝ := ∑ h ∈ Finset.Icc 1 2, p h
    let V : ℕ → ℝ := fun j ↦ ((ltM1K2VTable j : ℝ) / (multiUnitScale : ℝ)) * √(2 ^ n : ℝ)
    0 < pSucc ∧ (out.2.2 * (K_blk : ℝ) + (2 : ℝ) + ∑ h ∈ Finset.Icc 1 2, p h * V (2 - h)) / pSucc ≤
      V 2 := by
  intro K_blk p pSucc V; have hS : (0 : ℝ) < (swScale : ℝ) := (by unfold swScale; norm_num)
  have hcl_cert := ltM1K2_clamp_cert; unfold ltM1K2CheckClamp at hcl_cert
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hcl_cert
  rcases hcl_cert with ⟨⟨hsurv_ub, _⟩, htl_le⟩
  have hsurv_le : out.2.2 ≤ (ltM1K2SurvUb : ℝ) / (swScale : ℝ) :=
    le_trans hsurv_mem.2 (div_le_div_of_nonneg_right (Int.cast_le.2 hsurv_ub) hS.le)
  have hp_nn : ∀ h : ℕ, 0 ≤ p h := fun h ↦ swLAttemptProbReal_nonneg (by omega) M out.1 hcum0 h
  have hp_sum1 : ∑ h ∈ Finset.range 3, p h = 1 := swLAttemptProbReal_sum_one (by omega) hM hcons
  have hp0_mem : memIvInt (p 0)
      (ivAddInt (swLOrbSqIv ltM1K2CertStIvs9 0) (ivMulInt ltM1K2CertCumIv9 (0, swOrbPad))) := by
    dsimp [p]; unfold swLAttemptProbReal; simp only [↓reduceIte]
    have ho0 : memIvInt ((swLOrbitProj M out.1 ⟨0, by omega⟩) ^ 2) (swLOrbSqIv ltM1K2CertStIvs9 0)
      := memIvInt_swLOrbSqIv hM hst_mem ⟨0, by omega⟩
    have hoff0 : |M ⟨0, by omega⟩ ⟨2 * 2 - 1, by omega⟩| ≤ (1 : ℝ) / 10 ^ 9 :=
      hM.2.2.2 _ _ (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
    have hsq0 : (M ⟨0, by omega⟩ ⟨2 * 2 - 1, by omega⟩) ^ 2 ≤ (1 : ℝ) / 10 ^ 18 := by
      rw [← sq_abs]; exact (pow_le_pow_left₀ (abs_nonneg _) hoff0 2).trans_eq (by norm_num)
    have hpad0 : memIvInt ((M ⟨0, by omega⟩ ⟨2 * 2 - 1, by omega⟩) ^ 2) (0, swOrbPad) := by
      unfold memIvInt swScale swOrbPad; dsimp only
      exact ⟨by linarith [sq_nonneg (M ⟨0, by omega⟩ ⟨2 * 2 - 1, by omega⟩)], by linarith⟩
    exact memIvInt_ivAddInt ho0 (memIvInt_ivMulInt hcum_mem hpad0)
  have ht1_eq : ∑ h ∈ Finset.Icc 1 2, p h = 1 - p 0 := by
    have hsplit : ∑ h ∈ Finset.range 3, p h = p 0 + ∑ h ∈ Finset.Icc 1 2, p h := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < 3),
        show Finset.Ico (0 + 1) 3 = Finset.Icc 1 2 from Finset.Ico_add_one_right_eq_Icc 1 2]
    linarith [hp_sum1, hsplit]
  have ht1_mem : memIvInt (∑ h ∈ Finset.Icc 1 2, p h) (ivSubInt (swScale, swScale) (ivAddInt
    (swLOrbSqIv ltM1K2CertStIvs9 0) (ivMulInt ltM1K2CertCumIv9 (0, swOrbPad)))) := by
    rw [ht1_eq]; exact memIvInt_ivSubInt memIvInt_one hp0_mem
  rcases memIvInt_swLTailSuffixIvs (L := 2) (by omega) hM hst_mem hcum_mem 1 le_rfl with
    ⟨hsfx_len, hsfx⟩
  set tailIvs := ivSubInt (swScale, swScale) (ivAddInt (swLOrbSqIv ltM1K2CertStIvs9 0) (ivMulInt
    ltM1K2CertCumIv9 (0, swOrbPad))) :: swLTailSuffixIvs 2 ltM1K2CertStIvs9 ltM1K2CertCumIv9 1
  have htailIvs_len : tailIvs.length = 2 := (by dsimp [tailIvs]; simp [hsfx_len])
  set tReal : ℕ → ℝ := fun c ↦ ∑ h ∈ Finset.Icc c 2, p h
  have hclamp := swLClampTailLbs_sound tailIvs tReal 1
    (fun i hi ↦ by
      rw [htailIvs_len] at hi; have ht0 : 0 ≤ tReal (1 + i) := Finset.sum_nonneg fun h _ ↦ hp_nn h
      have ht1 : tReal (1 + i) ≤ 1 := by
        have hsub : Finset.Icc (1 + i) 2 ⊆ Finset.range 3 := fun h hh ↦ by
          rw [Finset.mem_Icc] at hh; rw [Finset.mem_range]; omega
        exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun h _ _ ↦ hp_nn h).trans_eq hp_sum1
      refine ⟨ht0, ht1, ?_⟩
      rcases i with _ | i'
      · simpa [tailIvs, tReal] using ht1_mem.1
      · have hi' : i' < 1 := (by omega); have hmem := hsfx i' hi'
        have hcc_eq : 2 + 1 - 1 + i' = 1 + (i' + 1) := (by omega); rw [hcc_eq] at hmem
        simpa [tailIvs, tReal] using hmem.1)
    (fun i hi ↦ by
      rw [htailIvs_len] at hi; dsimp [tReal]; exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_left (by omega)) fun h _ _ ↦ hp_nn h)
  have htail_lbs : ∀ c ∈ Finset.Icc 1 2,
      ((ltM1K2TailLbs.getD (c - 1) 0 : ℤ) : ℝ) / (swScale : ℝ) ≤ ∑ h ∈ Finset.Icc c 2, p h := by
    intro c hc; rw [Finset.mem_Icc] at hc; have hidx : c - 1 < 2 := (by omega)
    have hle_cert := htl_le (c - 1) hidx
    have hcert_real := hclamp.2 (c - 1) (by rw [htailIvs_len]; exact hidx)
    rw [show 1 + (c - 1) = c by omega] at hcert_real
    exact (div_le_div_of_nonneg_right (by exact_mod_cast hle_cert) hS.le).trans hcert_real
  have hstep := ltM1K2_step_cert; unfold checkSwLM1StepTable checkSwLM1Step at hstep
  simp only [withForcedInt_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hstep
  rcases hstep with ⟨⟨⟨_, _, _, _, htau, hden, _, _, hsurv0, hvsc_pos, htl0_pos, _, _, _,
    hrem0, hsq_ineq⟩, _⟩, hchain_mono⟩
  have hvsc_r : (0 : ℝ) < (multiUnitScale : ℝ) := (by exact_mod_cast hvsc_pos)
  have hbden_r : (0 : ℝ) < (swBden49 : ℝ) := (by unfold swBden49; norm_num)
  set N : ℝ := (2 ^ n : ℝ); have hsqrtN_pos : 0 < √N := (by dsimp [N]; positivity)
  have hsqrtN_ge : (swBden49 : ℝ) / 2 ≤ √N := by
    have hpow : 2 ^ 96 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn96
    have hpow_r : ((2 ^ 96 : ℕ) : ℝ) ≤ N := (by dsimp [N]; exact_mod_cast hpow)
    have h1 : (281474976710656 : ℝ) ^ 2 ≤ N := by
      have : ((2 ^ 96 : ℕ) : ℝ) = (281474976710656 : ℝ) ^ 2 := (by norm_num); linarith
    have h2 : (281474976710656 : ℝ) ≤ √N := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 281474976710656)]; exact Real.sqrt_le_sqrt h1
    have h3 : (swBden49 : ℝ) / 2 = 281474976710656 := (by unfold swBden49; norm_num); linarith
  have hpSucc_pos : 0 < pSucc := by
    have hlb1 := htail_lbs 1 (by rw [Finset.mem_Icc]; omega)
    have hpos : 0 < ((ltM1K2TailLbs.getD 0 0 : ℤ) : ℝ) / (swScale : ℝ) := div_pos (by exact_mod_cast
      htl0_pos) hS; exact hpos.trans_le hlb1
  refine ⟨hpSucc_pos, ?_⟩
  set chain : List ℤ := ltM1K2VTable 2 :: (List.range 2).map fun i ↦ ltM1K2VTable (2 - (i + 1))
  have hchain_eq : ∀ c ≤ 2, chain.getD c 0 = ltM1K2VTable (2 - c) := by
    intro c hc; rcases c with _ | c'
    · simp [chain]
    · have hc' : c' < 2 := (by omega); simp [chain, List.getD_eq_getElem?_getD, hc']
  set rhsInt : ℤ := ∑ c ∈ Finset.range 2,
    ltM1K2TailLbs.getD c 0 * (chain.getD c 0 - chain.getD (c + 1) 0)
  have hfold_eq : (List.range 2).foldl (fun acc c ↦ acc + ltM1K2TailLbs.getD c 0 * (chain.getD c 0 -
    chain.getD (c + 1) 0)) 0 = rhsInt := foldl_range_add_eq_sum 2 _; rw [hfold_eq] at hrem0 hsq_ineq
  have hgain_ge : ((rhsInt : ℝ) / ((swScale : ℝ) * (multiUnitScale : ℝ))) * √N ≤
      ∑ h ∈ Finset.Icc 1 2, p h * (V 2 - V (2 - h)) := by
    have habel := sum_Icc_abel 2 p (fun k ↦ V (2 - k)); simp only [Nat.sub_zero] at habel
    rw [habel, show ((rhsInt : ℝ) / ((swScale : ℝ) * (multiUnitScale : ℝ))) * √N =
      ∑ c ∈ Finset.range 2,
        (((ltM1K2TailLbs.getD c 0 : ℤ) : ℝ) / (swScale : ℝ)) *
          ((((chain.getD c 0 - chain.getD (c + 1) 0 : ℤ) : ℝ) / (multiUnitScale : ℝ)) * √N) by
      dsimp [rhsInt]; push_cast; rw [sum_div_const, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring]
    refine Finset.sum_le_sum fun c hc ↦ ?_
    rw [Finset.mem_range] at hc; have hmono_c := hchain_mono c hc
    have hdiff_nn : 0 ≤ (((chain.getD c 0 - chain.getD (c + 1) 0 : ℤ) : ℝ) / (multiUnitScale : ℝ)) *
      √N := mul_nonneg (div_nonneg (by exact_mod_cast sub_nonneg.2 hmono_c) hvsc_r.le) hsqrtN_pos.le
    have hV_eq : (((chain.getD c 0 - chain.getD (c + 1) 0 : ℤ) : ℝ) / (multiUnitScale : ℝ)) * √N =
        V (2 - c) - V (2 - (c + 1)) := by
      rw [hchain_eq c (by omega), hchain_eq (c + 1) (by omega)]; dsimp [V]; push_cast; ring
    have htl_c := htail_lbs (c + 1) (by rw [Finset.mem_Icc]; omega)
    simp only [Nat.add_sub_cancel] at htl_c; rw [← hV_eq]
    exact mul_le_mul_of_nonneg_right htl_c hdiff_nn
  have hK_ub := kBlk_le_main_add_three_halves (r := 2) (tauNum := 5000000) (tauDen := 1000000000)
    hn96 (by omega) (by omega) htau hden
  set bNum : ℤ := 3 * ltM1K2SurvUb + 2 * swScale * (2 : ℤ)
  have hcost_ub : out.2.2 * (K_blk : ℝ) + (2 : ℝ) ≤ (((ltM1K2SurvUb : ℝ) * (5000000 : ℝ)) / (2 *
    (swScale : ℝ) * (1000000000 : ℝ) * √(2 : ℝ)) + (bNum : ℝ) / ((swScale : ℝ) * (swBden49 : ℝ))) *
    √N := by
    have h1 : out.2.2 * (K_blk : ℝ) ≤ ((ltM1K2SurvUb : ℝ) / (swScale : ℝ)) * (((5000000 : ℝ) / (2 *
      (1000000000 : ℝ) * √(2 : ℝ))) * √N + 3 / 2) := mul_le_mul hsurv_le hK_ub (Nat.cast_nonneg
      K_blk) (div_nonneg (by exact_mod_cast hsurv0) hS.le)
    have hbNum_nn : 0 ≤ (bNum : ℝ) := by
      dsimp [bNum]; unfold swScale
      exact_mod_cast (by omega : (0 : ℤ) ≤ 3 * ltM1K2SurvUb + 2 * 1000000000 * (2 : ℤ))
    have hoverh : (bNum : ℝ) / (2 * (swScale : ℝ)) ≤
        ((bNum : ℝ) / ((swScale : ℝ) * (swBden49 : ℝ))) * √N := by
      have hmul := mul_le_mul_of_nonneg_left hsqrtN_ge (div_nonneg hbNum_nn (mul_pos hS hbden_r).le)
      refine (?_ : (bNum : ℝ) / (2 * (swScale : ℝ)) =
        ((bNum : ℝ) / ((swScale : ℝ) * (swBden49 : ℝ))) * ((swBden49 : ℝ) / 2)).trans_le hmul
      field_simp [hS.ne', hbden_r.ne']
    have halg : ((ltM1K2SurvUb : ℝ) / (swScale : ℝ)) * (((5000000 : ℝ) / (2 * (1000000000 : ℝ) * √(2
      : ℝ))) * √N + 3 / 2) + (2 : ℝ) = (((ltM1K2SurvUb : ℝ) * (5000000 : ℝ)) / (2 * (swScale : ℝ) *
      (1000000000 : ℝ) * √(2 : ℝ))) * √N + (bNum : ℝ) / (2 * (swScale : ℝ)) := by
      dsimp [bNum]; push_cast; field_simp [hS.ne']; ring
    linarith
  set rem : ℤ := rhsInt * swBden49 - multiUnitScale * bNum
  have hcoef_le : ((ltM1K2SurvUb : ℝ) * (5000000 : ℝ)) / (2 * (swScale : ℝ) * (1000000000 : ℝ) * √(2
    : ℝ)) + (bNum : ℝ) / ((swScale : ℝ) * (swBden49 : ℝ)) ≤ (rhsInt : ℝ) / ((swScale : ℝ) *
    (multiUnitScale : ℝ)) := by
    have hr_pos : (0 : ℝ) < (2 : ℝ) := (by norm_num)
    have hsqrt_r_pos : 0 < √(2 : ℝ) := Real.sqrt_pos.2 hr_pos
    have hden_r : (0 : ℝ) < (1000000000 : ℝ) := (by norm_num)
    have hrem_r : (0 : ℝ) ≤ (rem : ℝ) := (by exact_mod_cast hrem0); have hlhs_nn : 0 ≤
        (ltM1K2SurvUb : ℝ) * (5000000 : ℝ) * (multiUnitScale : ℝ) * (swBden49 : ℝ) := by
      have : (0 : ℝ) ≤ (ltM1K2SurvUb : ℝ) := (by exact_mod_cast hsurv0); positivity
    have hrhs_nn : 0 ≤ 2 * (1000000000 : ℝ) * √(2 : ℝ) * (rem : ℝ) := (by positivity)
    have hsq_r : ((ltM1K2SurvUb : ℝ) * (5000000 : ℝ) * (multiUnitScale : ℝ) * (swBden49 : ℝ)) ^ 2 ≤
      (2 * (1000000000 : ℝ) * √(2 : ℝ) * (rem : ℝ)) ^ 2 := by
      have hcast : ((ltM1K2SurvUb * (5000000 : ℤ) * multiUnitScale * swBden49) ^ 2 : ℝ) ≤
          ((4 * ((1000000000 : ℤ) ^ 2) * (2 : ℤ) * (rem ^ 2) : ℤ) : ℝ) := by
        exact_mod_cast hsq_ineq
      push_cast at hcast; have hsq_rhs : (2 * (1000000000 : ℝ) * √(2 : ℝ) * (rem : ℝ)) ^ 2 =
          4 * (1000000000 : ℝ) ^ 2 * (2 : ℝ) * (rem : ℝ) ^ 2 := by
        calc (2 * (1000000000 : ℝ) * √(2 : ℝ) * (rem : ℝ)) ^ 2
          _ = 4 * (1000000000 : ℝ) ^ 2 * (√(2 : ℝ)) ^ 2 * (rem : ℝ) ^ 2 := by ring
          _ = 4 * (1000000000 : ℝ) ^ 2 * (2 : ℝ) * (rem : ℝ) ^ 2 := by rw [Real.sq_sqrt hr_pos.le]
      linarith
    have hroot : (ltM1K2SurvUb : ℝ) * (5000000 : ℝ) * (multiUnitScale : ℝ) * (swBden49 : ℝ) ≤ 2 *
      (1000000000 : ℝ) * √(2 : ℝ) * (rem : ℝ) := by
      rw [← Real.sqrt_sq hlhs_nn, ← Real.sqrt_sq hrhs_nn]; exact Real.sqrt_le_sqrt hsq_r
    have hrem_def :
        (rem : ℝ) = (rhsInt : ℝ) * (swBden49 : ℝ) - (multiUnitScale : ℝ) * (bNum : ℝ) := by
      dsimp [rem]; push_cast; rfl
    rw [hrem_def] at hroot; have hpos_prod : 0 < 2 * (swScale : ℝ) * (1000000000 : ℝ) * √(2 : ℝ) *
        (multiUnitScale : ℝ) * (swBden49 : ℝ) := by positivity
    rw [← sub_nonneg]
    have hdiff : (rhsInt : ℝ) / ((swScale : ℝ) * (multiUnitScale : ℝ)) - (((ltM1K2SurvUb : ℝ) *
      (5000000 : ℝ)) / (2 * (swScale : ℝ) * (1000000000 : ℝ) * √(2 : ℝ)) + (bNum : ℝ) / ((swScale :
      ℝ) * (swBden49 : ℝ))) = (2 * (1000000000 : ℝ) * √(2 : ℝ) * ((rhsInt : ℝ) * (swBden49 : ℝ) -
      (multiUnitScale : ℝ) * (bNum : ℝ)) - (ltM1K2SurvUb : ℝ) * (5000000 : ℝ) * (multiUnitScale :
      ℝ) * (swBden49 : ℝ)) / (2 * (swScale : ℝ) * (1000000000 : ℝ) * √(2 : ℝ) * (multiUnitScale :
      ℝ) * (swBden49 : ℝ)) := by
      field_simp [hS.ne', hden_r.ne', hsqrt_r_pos.ne', hvsc_r.ne', hbden_r.ne']; ring
    rw [hdiff]; exact div_nonneg (by linarith) hpos_prod.le
  have hnet : out.2.2 * (K_blk : ℝ) + (2 : ℝ) ≤ ∑ h ∈ Finset.Icc 1 2, p h * (V 2 - V (2 - h)) :=
    (hcost_ub.trans (mul_le_mul_of_nonneg_right hcoef_le hsqrtN_pos.le)).trans hgain_ge
  have hexpand : ∑ h ∈ Finset.Icc 1 2, p h * (V 2 - V (2 - h)) =
      pSucc * V 2 - ∑ h ∈ Finset.Icc 1 2, p h * V (2 - h) := by
    dsimp [pSucc]; rw [Finset.sum_mul]; have hsub : ∀ h ∈ Finset.Icc 1 2, p h * (V 2 - V (2 - h)) =
        p h * V 2 - p h * V (2 - h) := fun _ _ ↦ mul_sub _ _ _
    rw [Finset.sum_congr rfl hsub, Finset.sum_sub_distrib]
  rw [div_le_iff₀ hpSucc_pos]; linarith [hnet, hexpand]
theorem ltM1K2_stage2_of_certs {n : ℕ} (hn96 : 96 ≤ n) (ps : List (ℤ × ℤ)) (htraj : ltM1K2CheckEvol9
    ltM1K2TrigPair100 ps (9020, 12886) (1119, 5000) (-3178, -2788) (258853, 258970) ltM1K2CertCumIv9
    ltM1K2CertSurvIv9 = true) : ∀ (M : Fin (2 * 2) → Fin (2 * 2) → ℝ), IsValidSwLOverlap M →
      let K_blk := hdistLKBlk n 2 5000000 1000000000
      let cs : Fin 2 → ℝ × ℝ := fun w ↦
        (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) 2 w.1),
         Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) 2 w.1))
      let out := hdistLEvolutionReal 2 (by omega) cs (ps.map ltM1K2MkPulse)
      let p : ℕ → ℝ := swLAttemptProbReal 2 (by omega) M out.1 out.2.1
      let pSucc : ℝ := ∑ h ∈ Finset.Icc 1 2, p h
      let V : ℕ → ℝ := fun j ↦ ((ltM1K2VTable j : ℝ) / (multiUnitScale : ℝ)) * √(2 ^ n : ℝ)
      0 < pSucc ∧ (out.2.2 * (K_blk : ℝ) + (2 : ℝ) + ∑ h ∈ Finset.Icc 1 2, p h * V (2 - h)) / pSucc
        ≤ V 2 := by
  intro M hM K_blk cs out p pSucc V
  have hcs_unit : ∀ w : Fin 2, (cs w).1 ^ 2 + (cs w).2 ^ 2 = 1 := fun w ↦ Real.cos_sq_add_sin_sq _
  rcases swLEvolutionReal_normSq_add_cum (by omega : 2 ≤ 2) hcs_unit
    (ps.map ltM1K2MkPulse) (ltM1K2MapPulses_valid ps) with ⟨hcons, hcum0, _, _⟩
  have hcs_mem : (tcMemAmpIv (cs ⟨0, by omega⟩).1 ltM1K2TrigPair100.1.1 ∧ tcMemAmpIv (cs ⟨0, by
    omega⟩).2 ltM1K2TrigPair100.1.2) ∧ (tcMemAmpIv (cs ⟨1, by omega⟩).1 ltM1K2TrigPair100.2.1 ∧
    tcMemAmpIv (cs ⟨1, by omega⟩).2 ltM1K2TrigPair100.2.2) := ltM1K2TrigPair100_sound hn96
  rcases ltM1K2CheckEvol9_sound (cs := cs) hcs_mem ps htraj with
    ⟨hst_mem, hcum_mem, hsurv_mem⟩
  exact ltM1K2_bellman_of_enclosure hn96 M hM (swLEvolutionReal 2 (by omega) cs (ps.map
    ltM1K2MkPulse)) hcons hcum0 hst_mem hcum_mem hsurv_mem
theorem ltM1K2_stage2_sound {n : ℕ} (hn96 : 96 ≤ n) : ∀ (M : Fin (2 * 2) → Fin (2 * 2) → ℝ),
    IsValidSwLOverlap M →
      let K_blk := hdistLKBlk n 2 5000000 1000000000
      let cs : Fin 2 → ℝ × ℝ := fun w ↦
        (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) 2 w.1),
         Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) 2 w.1))
      let out := hdistLEvolutionReal 2 (by omega) cs (ltM1K2RawPairs.map ltM1K2MkPulse)
      let p : ℕ → ℝ := swLAttemptProbReal 2 (by omega) M out.1 out.2.1
      let pSucc : ℝ := ∑ h ∈ Finset.Icc 1 2, p h
      let V : ℕ → ℝ := fun j ↦ ((ltM1K2VTable j : ℝ) / (multiUnitScale : ℝ)) * √(2 ^ n : ℝ)
      0 < pSucc ∧ (out.2.2 * (K_blk : ℝ) + (2 : ℝ) + ∑ h ∈ Finset.Icc 1 2, p h * V (2 - h)) / pSucc
        ≤ V 2 := ltM1K2_stage2_of_certs hn96 ltM1K2RawPairs ltM1K2_traj100_cert
/-- Opaque `2,700`-pulse `SwLPulseRat 2` schedule preventing kernel spine unfolding. -/
def ltM1K2SchedPulses : List (SwLPulseRat 2) := ltM1K2RawPairs.map ltM1K2MkPulse
/-- Certified `SwLM1CertBundle` (`kMax = 2`) for `(m = 1, k = 2)`. -/
def longTailM1K2OnlyBundle : SwLM1CertBundle where
  kMax := 2
  vScale := multiUnitScale
  vTable := ltM1K2VTable
  useSwL := fun r ↦ r == 2
  stageOfR := fun _ ↦ ⟨2, 5000000, 1000000000, ltM1K2SchedPulses⟩
  hKMax := by omega
  hScalePos := by
    unfold SchurWeylLCert.multiUnitScale; omega
  hV0 := rfl
  hMono := by
    intro r hr; rcases r with _ | _ | r
    · exact (bleZ_eq_true_iff _ _).mp rfl
    · exact (bleZ_eq_true_iff _ _).mp rfl
    · omega
  hStageSound := by
    intro n r hn96 _ _ huse; have hr2 : r = 2 := by simpa using huse
    subst hr2; simp only [ltM1K2SchedPulses]
    exact ⟨by omega, by omega, by omega, ltM1K2MapPulses_valid ltM1K2RawPairs,
      ltM1K2_stage2_sound hn96⟩
theorem ltM1K2_useSwL (r : ℕ) (h2 : 2 ≤ r) (hle : r ≤ longTailM1K2OnlyBundle.kMax) :
    longTailM1K2OnlyBundle.useSwL r = true := by
  change (r == 2) = true; have hr2 : r = 2 := (by change r ≤ 2 at hle; omega); subst hr2; rfl
end
@[expose] public section
/-- Cell selector claiming `(m = 1, k = 2)` only. -/
abbrev isLongTailM1K2OnlyCell (m k : ℕ) : Bool := m == 1 && k == 2
/-- Certified coprime relative cost at `(m = 1, k = 2)` (`379666241046199 /
  500000000000000`). -/
def relCostLongTailM1K2Only (m k : ℕ) : ℚ≥0 :=
  if m == 1 && k == 2 then (379666241046199 : ℚ≥0) / 500000000000000 else 1
/-- Standalone `FindAllCostProfile` for `(m = 1, k = 2)` (`n₀ = 100`). -/
def longTailM1K2OnlyProfile : FindAllCostProfile where
  validCell := isLongTailM1K2OnlyCell
  relCost := relCostLongTailM1K2Only
  n0 _ _ := 100
end
public section
/-- Native-`findAllQubits` circuit for `(m = 1, k = 2)` dispatching
  `hdistLM1FromSetCircuit`. -/
noncomputable def longTailM1K2OnlyCircuit {Var : Type} (res : Var) (n : ℕ) : ∀ (m k : ℕ),
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m)
  | 1, 2 =>
      if 100 ≤ n then
        hdistLM1FromSetCircuit res longTailM1K2OnlyBundle n 2 2 ∅
      else
        findAllCircuit res (fun _ _ _ ↦ 0) n 1 2
  | _, _ => .skip
/-- End-to-end `ValidFindAllFamily` certificate for `longTailM1K2OnlyCircuit`. -/
theorem validFamily_longTailM1K2Only {Var : Type} [DecidableEq Var] (res : Var) :
    ValidFindAllFamily res longTailM1K2OnlyProfile (longTailM1K2OnlyCircuit res) where
  correctness {n m k S} _ _ hvalid hkN hS := by
    simp only [longTailM1K2OnlyProfile, isLongTailM1K2OnlyCell, Bool.and_eq_true,
      beq_iff_eq] at hvalid
    rcases hvalid with ⟨rfl, rfl⟩; have hScard : S.card = 2 := (Finset.mem_powersetCard.1 hS).2
    by_cases hn100 : 100 ≤ n
    · intro Δ; dsimp only [longTailM1K2OnlyCircuit]
      rw [ite_eq_left hn100, expect_top, interp_qSeq, QMonad.Q.toStateFun_bind,
        interp_qSet, QMonad.Q.toStateFun_qSet]
      have hsupp : SupportedOn (· = (0 : Fin (2 ^ findAllQubits n 1 2))) Δ.qSet :=
        supportedOn_qSet (pred := (· = (0 : Fin (2 ^ findAllQubits n 1 2)))) rfl Δ
      have hcorr := (hdistLM1FromSet_correct_and_cost res longTailM1K2OnlyBundle rfl ltM1K2_useSwL
        le_rfl hn100 le_rfl le_rfl le_rfl hScard (Finset.empty_subset S) (by simpa using hScard)
        hsupp).1
      exact (hcorr.trans (congrArg ((↑) : ℝ≥0 → ℝ) (CQState.trace_qSet Δ))).symm.le
    · dsimp only [longTailM1K2OnlyCircuit]; rw [ite_eq_right hn100]
      exact findAllProgram_correctness res (fun _ _ _ ↦ 0) le_rfl hScard hkN
        (fun r hr1 hrk ↦ p_succ_set_zero_pos hr1 (hrk.trans hkN))
  costBound_uniform {m k} _ hvalid n hn0 hkN := by
    simp only [longTailM1K2OnlyProfile, isLongTailM1K2OnlyCell, Bool.and_eq_true,
      beq_iff_eq] at hvalid
    rcases hvalid with ⟨rfl, rfl⟩; change 100 ≤ n at hn0
    set cVal : ℝ := ((ltM1K2V2_16 : ℝ) / (multiUnitScale : ℝ)) * √(2 ^ n : ℝ)
    have hcVal_nn : 0 ≤ cVal := by
      dsimp [cVal]; unfold ltM1K2V2_16 SchurWeylLCert.multiUnitScale; positivity
    let cNN : ℝ≥0 := ⟨cVal, hcVal_nn⟩; refine ⟨fun _ ↦ cNN, ?_, ?_⟩
    · intro S hS Δ; have hScard : S.card = 2 := (Finset.mem_powersetCard.1 hS).2
      dsimp only [longTailM1K2OnlyCircuit]
      rw [ite_eq_left hn0, expectedCost_qSeq, expectedCost_qSet,
        CostModel.ofEmbeddedOracle_resetCost, Nat.cast_zero, mul_zero, zero_add,
        interp_qSet, QMonad.Q.toStateFun_qSet]
      have hsupp : SupportedOn (· = (0 : Fin (2 ^ findAllQubits n 1 2))) Δ.qSet :=
        supportedOn_qSet (pred := (· = (0 : Fin (2 ^ findAllQubits n 1 2)))) rfl Δ
      have hmass_eq : stateMass Δ.qSet = stateMass Δ :=
        congrArg ENNReal.ofNNReal (CQState.trace_qSet Δ)
      have hcb := (hdistLM1FromSet_correct_and_cost res longTailM1K2OnlyBundle rfl ltM1K2_useSwL
        le_rfl hn0 le_rfl le_rfl le_rfl hScard (Finset.empty_subset S) (by simpa using hScard)
        hsupp).2; rw [hmass_eq] at hcb; refine hcb.trans ?_
      have hcNN : (cNN : ℝ≥0∞) = ENNReal.ofReal cVal := ENNReal.ofReal_coe_nnreal.symm
      rw [hcNN]; exact le_rfl
    · have hcard_pos : 0 < ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard 2).card := by
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]; exact Nat.choose_pos hkN
      have hcard_r : (0 : ℝ) < (((Finset.univ : Finset (Fin (2 ^ n))).powersetCard 2).card : ℝ) :=
        Nat.cast_pos.2 hcard_pos
      rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel_left₀ _ hcard_r.ne']
      have hrel_eq : ((longTailM1K2OnlyProfile.relCost 1 2 : ℚ≥0) : ℝ) =
          (ltM1K2RelNum : ℝ) / (ltM1K2RelDen : ℝ) := by
        unfold longTailM1K2OnlyProfile relCostLongTailM1K2Only ltM1K2RelNum ltM1K2RelDen
        simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte]; push_cast; norm_num
      rw [hrel_eq]; change cVal ≤ _; simpa only [Nat.cast_one] using ltM1K2_relCost16_sound n
end
end QuantumComputation.Specs.GroverFindAll
