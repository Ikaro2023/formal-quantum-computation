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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.FastUniform
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.AliasTreeSwap
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SelectRawOps

/-!
# Ancilla-Free Factored `L = 30` Splitters (`81`/`86`/`96`/`97 T`) & `32 T` Dyadic Coin (`b = 9`)

Provides three compact, zero-`TOFF` primitive families for `wInner2 = 21` (`mMidUB 21 = 27`) inner
`PREP_mid` in ``FactoredMag30AndCoin9``:

1. **Odd-`T` `U(2)` (`det = ω_8`) Magnitude Synthesis Bridge & `10-T` Factored `30 = 2 × 5 × 3`
   Post-Product Tree (`Section 1`):**
   - Extends `su2MagUnitary` (`FastUniform`) to odd-`T` `Clifford+T` words (`det = ω_8`) via
     left-cancellation against `T⁻¹ = Z · S · T`, and factors `L = 15 = 5 × 3` into two independent
     `1`-qubit magnitude splitters followed by `4-T` clean-target relative `AND` (`rccx3`) + `2`
     CNOTs + three `2-T` `zeroCtrlH` cascades (`10 T`, `0` scratch wires, `0 TOFF`).
2. **`81-T`, `86-T`, `96-T` (`Med`), & `97-T` (`Tight`) Ancilla-Free (`0`-Scratch) Factored `L = 30`
   Splitters (`Section 2`):**
   - `factoredMag30Tuned81Circuit` / `factoredMag30Tuned81Dyn` (`81 T`, `0 TOFF`, `0` scratch,
     `‖factoredMag30Tuned81Impl.1 - factoredMag30Tuned81Unitary.1‖ ≤ 3059 / 10 ^ 14`),
   - `factoredMag30Tuned86Circuit` / `factoredMag30Tuned86Dyn` (`86 T`, `0 TOFF`, `0` scratch,
     `‖factoredMag30Tuned86Impl.1 - factoredMag30Tuned86Unitary.1‖ ≤ 1505 / 10 ^ 14`),
   - `factoredMag30MedCircuit` / `factoredMag30MedDyn` (`96 T`, `0 TOFF`, `0` scratch,
     `‖factoredMag30MedImpl.1 - factoredMag30MedUnitary.1‖ ≤ 531 / 10 ^ 15`),
   - `factoredMag30TightCircuit` / `factoredMag30TightDyn` (`97 T`, `0 TOFF`, `0` scratch,
     `‖factoredMag30TightImpl.1 - factoredMag30TightUnitary.1‖ ≤ 345 / 10 ^ 15`),
   - Exact column-`0` magnitude uniformity `Complex.normSq (U.1 x 0) = 1 / 30` on `x < 30` (`0` on
     `x ≥ 30`) plus both `CleanDyn.CleanRealizes` and `CleanDyn.CleanRealizes` on arbitrary
     `rScr : QRegister s N` (including `s = 0`).
3. **`32-T` Exact `4`-Qubit Dyadic Packet Coin (`b = 9`, `δ = 0`) & `36-T` `pktMux9Dyn`
   (`Section 3`):**
   - `dyadicCoin9Dyn` / `dyadicCoin9InvDyn` (`32 T`, `0 TOFF`, `2 ≤ s` scratch wires) realizing
     `dyadicCoin9Unitary` / `dyadicCoin9Unitary⁻¹` with exact dyadic weights `coin9Weight`
     summing to `512`,
   - `pktMux9Dyn` (`36 T`, `0 TOFF`, `20 ≤ s` temp wires) realizing self-inverse
     `pktMux9Unitary` with `∑ pkt, (if ¬ mux9Bit pkt keep then coin9Weight pkt else 0) =
     keep.val`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OptFactoredMag30AndCoin9
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real QuantumComputation.Specs Solution
open QuantumComputation.Specs.P450 Solution CoherentAlias Solution.CleanDyn AliasPrep FastUniform
open Solution.BlockEncodingCore Solution.BlockEncodingCircuit
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

local instance (priority := 1000000) instNeZeroTwoPowOptMag30 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

/-! ## Section 1: Odd-`T` (`det = ω`) `U(2)` Bridge & `10-T` Factored `L = 15` Tree -/

private lemma qubit_H_zero_zero : Qubit.H.1 0 0 = (√2 : ℂ)⁻¹ := by
  simp [Qubit.H, Complex.real_smul]

private lemma qubit_H_one_zero : Qubit.H.1 1 0 = (√2 : ℂ)⁻¹ := by
  simp [Qubit.H, Complex.real_smul]

private lemma normSq_inv_sqrt2 : Complex.normSq ((√2 : ℂ)⁻¹) = 1 / 2 := by
  rw [map_inv₀, Complex.normSq_ofReal, ← sq, Real.sq_sqrt (by norm_num)]
  norm_num

private lemma singleton_replaceIndex_eq {n : ℕ} (w : Wire n) (k k' : Fin (2 ^ n)) (b : Fin 2)
    (h : ∀ q : Wire n, basisBits n k' q = if q = w then basisBits 1 b 0 else basisBits n k q) :
    (QRegister.singleton w).replaceIndex k b = k' := by
  apply (basisBits n).injective
  funext q
  rw [h q]
  by_cases hqw : q = w
  · subst hqw
    simpa using (QRegister.singleton q).basisBits_replaceIndex_apply k b 0
  · rw [ite_eq_right hqw]
    exact (QRegister.singleton w).basisBits_replaceIndex_of_not_mem k b q
      (by rintro ⟨_, hi⟩; exact hqw hi.symm)

private lemma pair_replaceIndex_eq {n : ℕ} (c t : Wire n) (hct : c ≠ t)
    (k k' : Fin (2 ^ n)) (b : Fin 4)
    (h : ∀ q : Wire n, basisBits n k' q =
      if q = c then basisBits 2 b 0
      else if q = t then basisBits 2 b 1
      else basisBits n k q) :
    (QRegister.pair c t hct).replaceIndex k b = k' := by
  let r := QRegister.pair c t hct
  apply (basisBits n).injective
  funext q
  change basisBits n (r.replaceIndex k b) q = basisBits n k' q
  rw [h q]
  by_cases hqc : q = c
  · subst hqc
    simpa [r] using r.basisBits_replaceIndex_apply k b 0
  · by_cases hqt : q = t
    · subst hqt
      simpa [r, hqc] using r.basisBits_replaceIndex_apply k b 1
    · rw [ite_eq_right hqc, ite_eq_right hqt]
      refine r.basisBits_replaceIndex_of_not_mem k b q ?_
      rintro ⟨i, hi⟩
      fin_cases i
      · exact hqc hi.symm
      · exact hqt hi.symm

private lemma mulVec_two_single_zero (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A *ᵥ (Pi.single (0 : Fin 2) 1) = A 0 0 • Pi.single 0 1 + A 1 0 • Pi.single 1 1 := by
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private lemma singleton_embedUnitary_mulVec_of_zero {n : ℕ} (w : Wire n)
    (U : Unitary 2) (k k1 : Fin (2 ^ n))
    (hex : (QRegister.singleton w).extractIndex k = 0)
    (h1 : ∀ q : Wire n, basisBits n k1 q =
      if q = w then basisBits 1 (1 : Fin 2) 0 else basisBits n k q) :
    ((QRegister.singleton w).embedUnitary U).1 *ᵥ (Pi.single k 1) =
      U.1 0 0 • Pi.single k 1 + U.1 1 0 • Pi.single k1 1 := by
  let r := QRegister.singleton w
  have hr0 : r.replaceIndex k 0 = k := by rw [← hex, r.replaceIndex_extractIndex]
  have hr1 : r.replaceIndex k 1 = k1 := singleton_replaceIndex_eq w k k1 1 h1
  rw [QRegister.embedUnitary_val, r.embedMatrix_mulVec_single_factors, hex,
    mulVec_two_single_zero, r.tensorState_add_left, r.tensorState_smul_left,
    r.tensorState_smul_left, r.tensorState_single_replaceIndex,
    r.tensorState_single_replaceIndex, hr0, hr1]

private lemma zeroCtrlH_pair_mulVec_of_one {n : ℕ} (c t : Wire n) (hct : c ≠ t)
    (k : Fin (2 ^ n))
    (hex : (QRegister.pair c t hct).extractIndex k = 1 ∨
           (QRegister.pair c t hct).extractIndex k = 3) :
    ((QRegister.pair c t hct).embedUnitary Catalyst.zeroCtrlH.eval).1 *ᵥ (Pi.single k 1) =
      Pi.single k 1 := by
  let r := QRegister.pair c t hct
  rw [QRegister.embedUnitary_val, Catalyst.zeroCtrlH_eval_eq]
  have hloc :
      !![Qubit.H.1 0 0, 0, Qubit.H.1 0 1, 0;
         0, 1, 0, 0;
         Qubit.H.1 1 0, 0, Qubit.H.1 1 1, 0;
         0, 0, 0, 1] *ᵥ (Pi.single (r.extractIndex k) 1) = Pi.single (r.extractIndex k) 1 := by
    rcases hex with h1 | h3
    · rw [h1]
      funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    · rw [h3]
      funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  rw [r.embedMatrix_mulVec_single_factors, hloc, r.tensorState_single_factors]

private lemma zeroCtrlH_pair_mulVec_of_zero {n : ℕ} (c t : Wire n) (hct : c ≠ t)
    (k k2 : Fin (2 ^ n))
    (hex : (QRegister.pair c t hct).extractIndex k = 0)
    (h2 : ∀ x : Wire n, basisBits n k2 x =
      if x = c then basisBits 2 (2 : Fin 4) 0
      else if x = t then basisBits 2 (2 : Fin 4) 1
      else basisBits n k x) :
    ((QRegister.pair c t hct).embedUnitary Catalyst.zeroCtrlH.eval).1 *ᵥ (Pi.single k 1) =
      (√2 : ℂ)⁻¹ • (Pi.single k 1 + Pi.single k2 1) := by
  let r := QRegister.pair c t hct
  rw [QRegister.embedUnitary_val, Catalyst.zeroCtrlH_eval_eq]
  have hr0 : r.replaceIndex k 0 = k := by rw [← hex, r.replaceIndex_extractIndex]
  have hr2 : r.replaceIndex k 2 = k2 := pair_replaceIndex_eq c t hct k k2 2 h2
  have hloc :
      !![Qubit.H.1 0 0, 0, Qubit.H.1 0 1, 0;
         0, 1, 0, 0;
         Qubit.H.1 1 0, 0, Qubit.H.1 1 1, 0;
         0, 0, 0, 1] *ᵥ (Pi.single (0 : Fin 4) 1) =
      (√2 : ℂ)⁻¹ • Pi.single 0 1 + (√2 : ℂ)⁻¹ • Pi.single 2 1 := by
    funext i
    fin_cases i <;>
      simp [qubit_H_zero_zero, qubit_H_one_zero, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  rw [r.embedMatrix_mulVec_single_factors, hex, hloc, r.tensorState_add_left,
    r.tensorState_smul_left, r.tensorState_smul_left, r.tensorState_single_replaceIndex,
    r.tensorState_single_replaceIndex, hr0, hr2, ← smul_add]

private lemma cnot_pair_mulVec_of_zero {n : ℕ} (c t : Wire n) (hct : c ≠ t)
    (k : Fin (2 ^ n))
    (hex : (QRegister.pair c t hct).extractIndex k = 0 ∨
           (QRegister.pair c t hct).extractIndex k = 2) :
    (Circuit.CNOT c t hct).eval.1 *ᵥ (Pi.single k 1) = Pi.single k 1 := by
  let r := QRegister.pair c t hct
  have hev : (Circuit.CNOT c t hct).eval =
      r.embedUnitary (Circuit.CNOT (0 : Fin 2) 1 (by decide)).eval := by
    simp [Circuit.CNOT, Circuit.eval_gate, QRegister.pair_zero_one_eq_whole,
      QRegister.whole_embedUnitary, r]
  rw [hev, QRegister.embedUnitary_val, CliffordT.cnot01_eval]
  have hloc :
      !![(1 : ℂ), 0, 0, 0;
         0, 0, 0, 1;
         0, 0, 1, 0;
         0, 1, 0, 0] *ᵥ (Pi.single (r.extractIndex k) 1) = Pi.single (r.extractIndex k) 1 := by
    rcases hex with h0 | h2
    · rw [h0]; funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    · rw [h2]; funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  rw [r.embedMatrix_mulVec_single_factors, hloc, r.tensorState_single_factors]

private lemma cnot_pair_mulVec_of_one_zero {n : ℕ} (c t : Wire n) (hct : c ≠ t)
    (k k3 : Fin (2 ^ n))
    (hex : (QRegister.pair c t hct).extractIndex k = 1)
    (h3 : ∀ x : Wire n, basisBits n k3 x =
      if x = c then basisBits 2 (3 : Fin 4) 0
      else if x = t then basisBits 2 (3 : Fin 4) 1
      else basisBits n k x) :
    (Circuit.CNOT c t hct).eval.1 *ᵥ (Pi.single k 1) = Pi.single k3 1 := by
  let r := QRegister.pair c t hct
  have hev : (Circuit.CNOT c t hct).eval =
      r.embedUnitary (Circuit.CNOT (0 : Fin 2) 1 (by decide)).eval := by
    simp [Circuit.CNOT, Circuit.eval_gate, QRegister.pair_zero_one_eq_whole,
      QRegister.whole_embedUnitary, r]
  rw [hev, QRegister.embedUnitary_val, CliffordT.cnot01_eval]
  have hr3 : r.replaceIndex k 3 = k3 := pair_replaceIndex_eq c t hct k k3 3 h3
  have hloc :
      !![(1 : ℂ), 0, 0, 0;
         0, 0, 0, 1;
         0, 0, 1, 0;
         0, 1, 0, 0] *ᵥ (Pi.single (1 : Fin 4) 1) = Pi.single 3 1 := by
    funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  rw [r.embedMatrix_mulVec_single_factors, hex, hloc, r.tensorState_single_replaceIndex, hr3]

private lemma cnot_pair_mulVec_of_one_one {n : ℕ} (c t : Wire n) (hct : c ≠ t)
    (k k1 : Fin (2 ^ n))
    (hex : (QRegister.pair c t hct).extractIndex k = 3)
    (h1 : ∀ x : Wire n, basisBits n k1 x =
      if x = c then basisBits 2 (1 : Fin 4) 0
      else if x = t then basisBits 2 (1 : Fin 4) 1
      else basisBits n k x) :
    (Circuit.CNOT c t hct).eval.1 *ᵥ (Pi.single k 1) = Pi.single k1 1 := by
  let r := QRegister.pair c t hct
  have hev : (Circuit.CNOT c t hct).eval =
      r.embedUnitary (Circuit.CNOT (0 : Fin 2) 1 (by decide)).eval := by
    simp [Circuit.CNOT, Circuit.eval_gate, QRegister.pair_zero_one_eq_whole,
      QRegister.whole_embedUnitary, r]
  rw [hev, QRegister.embedUnitary_val, CliffordT.cnot01_eval]
  have hr1 : r.replaceIndex k 1 = k1 := pair_replaceIndex_eq c t hct k k1 1 h1
  have hloc :
      !![(1 : ℂ), 0, 0, 0;
         0, 0, 0, 1;
         0, 0, 1, 0;
         0, 1, 0, 0] *ᵥ (Pi.single (3 : Fin 4) 1) = Pi.single 1 1 := by
    funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  rw [r.embedMatrix_mulVec_single_factors, hex, hloc, r.tensorState_single_replaceIndex, hr1]

private lemma reverse_prod_cons_mulVec {d : ℕ} (u : Unitary d) (us : List (Unitary d))
    (v : Fin d → ℂ) :
    (u :: us).reverse.prod.1 *ᵥ v = us.reverse.prod.1 *ᵥ (u.1 *ᵥ v) := by
  rw [List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil, mul_one,
    Submonoid.coe_mul, ← Matrix.mulVec_mulVec]

/-- `4-T`, `0-TOFF` relative-phase clean-target `AND` (`rccx3`) on `3` wires `(c₀=0, c₁=1, t=2)`. -/
def rccx3 : Circuit 3 :=
  Circuit.sequence [
    (CliffordT.Gate1.wordCircuit [.H, .T]).onRegister (QRegister.singleton 2),
    Circuit.CNOT 1 2 (by decide),
    (CliffordT.Gate1.wordCircuit [.T, .S, .Z]).onRegister (QRegister.singleton 2),
    Circuit.CNOT 0 2 (by decide),
    (CliffordT.Gate1.wordCircuit [.T]).onRegister (QRegister.singleton 2),
    Circuit.CNOT 1 2 (by decide),
    (CliffordT.Gate1.wordCircuit [.T, .S, .Z, .H]).onRegister (QRegister.singleton 2)
  ]

@[simp]
theorem rccx3_count_toff : rccx3.count PrimitiveGate.TOFF = 0 := by
  simp [rccx3]

@[simp]
theorem rccx3_count_t : rccx3.count PrimitiveGate.T = 4 := by
  simp [rccx3]

private lemma mulVec_two_single_one (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A *ᵥ (Pi.single (1 : Fin 2) 1) = A 0 1 • Pi.single 0 1 + A 1 1 • Pi.single 1 1 := by
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private lemma singleton_embedUnitary_mulVec_of_one {n : ℕ} (w : Wire n)
    (U : Unitary 2) (k1 k : Fin (2 ^ n))
    (hex : (QRegister.singleton w).extractIndex k1 = 1)
    (h0 : ∀ q : Wire n, basisBits n k q =
      if q = w then basisBits 1 (0 : Fin 2) 0 else basisBits n k1 q) :
    ((QRegister.singleton w).embedUnitary U).1 *ᵥ (Pi.single k1 1) =
      U.1 0 1 • Pi.single k 1 + U.1 1 1 • Pi.single k1 1 := by
  let r := QRegister.singleton w
  have hr1 : r.replaceIndex k1 1 = k1 := by rw [← hex, r.replaceIndex_extractIndex]
  have hr0 : r.replaceIndex k1 0 = k := singleton_replaceIndex_eq w k1 k 0 h0
  rw [QRegister.embedUnitary_val, r.embedMatrix_mulVec_single_factors, hex,
    mulVec_two_single_one, r.tensorState_add_left, r.tensorState_smul_left,
    r.tensorState_smul_left, r.tensorState_single_replaceIndex,
    r.tensorState_single_replaceIndex, hr0, hr1]

private lemma wordX_eval_entries :
    let U := (CliffordT.Gate1.wordCircuit [.X]).eval
    U.1 0 0 = 0 ∧ U.1 1 0 = 1 ∧ U.1 0 1 = 1 ∧ U.1 1 1 = 0 := by
  intro U
  let MX : CliffordT.CyclotomicMat2 :=
    ⟨0, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩
  have hM : U.1 = MX.toMatrix :=
    CliffordT.GateTrace.eval_toCircuit_of_checkFrom (.leaf [.X] MX 0) MX rfl
  rw [hM]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [MX, CliffordT.CyclotomicMat2.toMatrix, CliffordT.CyclotomicEight.toComplex]

private lemma wordX_singleton_on_pair {n : ℕ} (w : Wire n) (k k4 : Fin (2 ^ n))
    (hex0 : (QRegister.singleton w).extractIndex k = 0)
    (hex1 : (QRegister.singleton w).extractIndex k4 = 1)
    (h4 : ∀ q : Wire n, basisBits n k4 q =
      if q = w then basisBits 1 (1 : Fin 2) 0 else basisBits n k q)
    (h0 : ∀ q : Wire n, basisBits n k q =
      if q = w then basisBits 1 (0 : Fin 2) 0 else basisBits n k4 q) :
    ((QRegister.singleton w).embedUnitary (CliffordT.Gate1.wordCircuit [.X]).eval).1 *ᵥ
      (Pi.single k 1) = Pi.single k4 1 ∧
    ((QRegister.singleton w).embedUnitary (CliffordT.Gate1.wordCircuit [.X]).eval).1 *ᵥ
      (Pi.single k4 1) = Pi.single k 1 := by
  have ⟨hx00, hx10, hx01, hx11⟩ := wordX_eval_entries
  constructor
  · rw [singleton_embedUnitary_mulVec_of_zero w _ k k4 hex0 h4, hx00, hx10,
      zero_smul, one_smul, zero_add]
  · rw [singleton_embedUnitary_mulVec_of_one w _ k4 k hex1 h0, hx01, hx11,
      one_smul, zero_smul, add_zero]

private lemma span2_mem_word {n : ℕ} (w0 : Wire n) (w : List CliffordT.Gate1)
    (k k4 : Fin (2 ^ n))
    (hex0 : (QRegister.singleton w0).extractIndex k = 0)
    (hex1 : (QRegister.singleton w0).extractIndex k4 = 1)
    (h4 : ∀ q : Wire n, basisBits n k4 q =
      if q = w0 then basisBits 1 (1 : Fin 2) 0 else basisBits n k q)
    (h0 : ∀ q : Wire n, basisBits n k q =
      if q = w0 then basisBits 1 (0 : Fin 2) 0 else basisBits n k4 q)
    (α β : ℂ) :
    ∃ α' β' : ℂ,
      ((QRegister.singleton w0).embedUnitary (CliffordT.Gate1.wordCircuit w).eval).1 *ᵥ
        (α • Pi.single k 1 + β • Pi.single k4 1) =
      α' • Pi.single k 1 + β' • Pi.single k4 1 := by
  let U := (CliffordT.Gate1.wordCircuit w).eval
  refine ⟨α * U.1 0 0 + β * U.1 0 1, α * U.1 1 0 + β * U.1 1 1, ?_⟩
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    singleton_embedUnitary_mulVec_of_zero w0 U k k4 hex0 h4,
    singleton_embedUnitary_mulVec_of_one w0 U k4 k hex1 h0]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private lemma wordCircuit_append_eval (w₁ w₂ : List CliffordT.Gate1) :
    (CliffordT.Gate1.wordCircuit (w₁ ++ w₂)).eval =
      (CliffordT.Gate1.wordCircuit w₂).eval * (CliffordT.Gate1.wordCircuit w₁).eval := by
  induction w₁ with
  | nil => simp [CliffordT.Gate1.wordCircuit]
  | cons g gs ih =>
    simp [CliffordT.Gate1.wordCircuit, Circuit.eval_seq, ih, mul_assoc]

private lemma cycMat_Z_toMatrix_col0 :
    let M := (⟨0, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩⟩ :
        CliffordT.CyclotomicMat2).toMatrix
    M 0 0 = 1 ∧ M 1 0 = 0 := by
  intro M
  constructor <;>
    simp [M, CliffordT.CyclotomicMat2.toMatrix, CliffordT.CyclotomicEight.toComplex]

private lemma cycMat_iX_toMatrix_col0 :
    let M := (⟨0, ⟨0, 0, 0, 0⟩, ⟨0, 0, -1, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩⟩ :
        CliffordT.CyclotomicMat2).toMatrix
    M 0 0 = 0 ∧ M 1 0 = Complex.I := by
  intro M
  constructor
  · simp [M, CliffordT.CyclotomicMat2.toMatrix, CliffordT.CyclotomicEight.toComplex]
  · suffices (((1 + Complex.I) / √2 : ℂ) ^ 2) = Complex.I by
      simpa [M, CliffordT.CyclotomicMat2.toMatrix, CliffordT.CyclotomicEight.toComplex,
        CliffordT.omega8] using this
    have hsq : ((√2 : ℂ)) ^ 2 = 2 := by norm_cast; exact Real.sq_sqrt (by norm_num)
    have hnum : (1 + Complex.I) ^ 2 = 2 * Complex.I := by
      calc (1 + Complex.I) ^ 2 = 1 + 2 * Complex.I + Complex.I ^ 2 := by ring
        _ = 2 * Complex.I := by rw [Complex.I_sq]; ring
    rw [div_pow, hnum, hsq]
    ring

private lemma rccx3_mulVec_zero :
    rccx3.eval.1 *ᵥ (Pi.single (0 : Fin (2 ^ 3)) 1) = Pi.single 0 1 ∧
    rccx3.eval.1 *ᵥ (Pi.single (1 : Fin (2 ^ 3)) 1) = Pi.single 1 1 ∧
    rccx3.eval.1 *ᵥ (Pi.single (2 : Fin (2 ^ 3)) 1) = Pi.single 2 1 ∧
    rccx3.eval.1 *ᵥ (Pi.single (3 : Fin (2 ^ 3)) 1) = Complex.I • Pi.single 7 1 := by
  have hseq2 (w₁ w₂ : List CliffordT.Gate1) (v : Fin (2 ^ 3) → ℂ) :
      ((QRegister.singleton (2 : Wire 3)).embedUnitary
        (CliffordT.Gate1.wordCircuit w₂).eval).1 *ᵥ
      (((QRegister.singleton (2 : Wire 3)).embedUnitary
        (CliffordT.Gate1.wordCircuit w₁).eval).1 *ᵥ v) =
      ((QRegister.singleton (2 : Wire 3)).embedUnitary
        (CliffordT.Gate1.wordCircuit (w₁ ++ w₂)).eval).1 *ᵥ v := by
    rw [Matrix.mulVec_mulVec, ← Submonoid.coe_mul, ← QRegister.embedUnitary_mul,
      ← wordCircuit_append_eval]
  have hcnot_id {c : Wire 3} (hc2 : c ≠ 2) {k k4 : Fin (2 ^ 3)}
      (hk : (QRegister.pair c 2 hc2).extractIndex k = 0)
      (hk4 : (QRegister.pair c 2 hc2).extractIndex k4 = 2) (α β : ℂ) :
      (Circuit.CNOT c 2 hc2).eval.1 *ᵥ (α • Pi.single k 1 + β • Pi.single k4 1) =
        α • Pi.single k 1 + β • Pi.single k4 1 := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      cnot_pair_mulVec_of_zero c 2 hc2 k (Or.inl hk),
      cnot_pair_mulVec_of_zero c 2 hc2 k4 (Or.inr hk4)]
  have hcnot_x {c : Wire 3} (hc2 : c ≠ 2) {k k4 : Fin (2 ^ 3)}
      (hex0 : (QRegister.singleton (2 : Wire 3)).extractIndex k = 0)
      (hex1 : (QRegister.singleton (2 : Wire 3)).extractIndex k4 = 1)
      (h4 : ∀ q : Wire 3, basisBits 3 k4 q =
        if q = 2 then basisBits 1 (1 : Fin 2) 0 else basisBits 3 k q)
      (h0 : ∀ q : Wire 3, basisBits 3 k q =
        if q = 2 then basisBits 1 (0 : Fin 2) 0 else basisBits 3 k4 q)
      (hk : (QRegister.pair c 2 hc2).extractIndex k = 1)
      (hk4 : (QRegister.pair c 2 hc2).extractIndex k4 = 3)
      (hb3 : ∀ x : Wire 3, basisBits 3 k4 x =
        if x = c then basisBits 2 (3 : Fin 4) 0
        else if x = 2 then basisBits 2 (3 : Fin 4) 1
        else basisBits 3 k x)
      (hb1 : ∀ x : Wire 3, basisBits 3 k x =
        if x = c then basisBits 2 (1 : Fin 4) 0
        else if x = 2 then basisBits 2 (1 : Fin 4) 1
        else basisBits 3 k4 x)
      (α β : ℂ) :
      (Circuit.CNOT c 2 hc2).eval.1 *ᵥ (α • Pi.single k 1 + β • Pi.single k4 1) =
        ((QRegister.singleton (2 : Wire 3)).embedUnitary
          (CliffordT.Gate1.wordCircuit [.X]).eval).1 *ᵥ
          (α • Pi.single k 1 + β • Pi.single k4 1) := by
    have ⟨hX0, hX1⟩ := wordX_singleton_on_pair (2 : Wire 3) k k4 hex0 hex1 h4 h0
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      cnot_pair_mulVec_of_one_zero c 2 hc2 k k4 hk hb3,
      cnot_pair_mulVec_of_one_one c 2 hc2 k4 k hk4 hb1, hX0, hX1]
  have hrun (k k4 : Fin (2 ^ 3))
      (hex0 : (QRegister.singleton (2 : Wire 3)).extractIndex k = 0)
      (hex1 : (QRegister.singleton (2 : Wire 3)).extractIndex k4 = 1)
      (h4 : ∀ q : Wire 3, basisBits 3 k4 q =
        if q = 2 then basisBits 1 (1 : Fin 2) 0 else basisBits 3 k q)
      (h0 : ∀ q : Wire 3, basisBits 3 k q =
        if q = 2 then basisBits 1 (0 : Fin 2) 0 else basisBits 3 k4 q)
      (wc1 wc0 : List CliffordT.Gate1)
      (hc1 : ∀ α β : ℂ,
        (Circuit.CNOT 1 2 (by decide)).eval.1 *ᵥ (α • Pi.single k 1 + β • Pi.single k4 1) =
          ((QRegister.singleton (2 : Wire 3)).embedUnitary
            (CliffordT.Gate1.wordCircuit wc1).eval).1 *ᵥ
            (α • Pi.single k 1 + β • Pi.single k4 1))
      (hc0 : ∀ α β : ℂ,
        (Circuit.CNOT 0 2 (by decide)).eval.1 *ᵥ (α • Pi.single k 1 + β • Pi.single k4 1) =
          ((QRegister.singleton (2 : Wire 3)).embedUnitary
            (CliffordT.Gate1.wordCircuit wc0).eval).1 *ᵥ
            (α • Pi.single k 1 + β • Pi.single k4 1)) :
      rccx3.eval.1 *ᵥ (Pi.single k 1) =
        ((QRegister.singleton (2 : Wire 3)).embedUnitary (CliffordT.Gate1.wordCircuit
          ([.H, .T] ++ wc1 ++ [.T, .S, .Z] ++ wc0 ++ [.T] ++ wc1 ++ [.T, .S, .Z, .H])).eval).1 *ᵥ
          (Pi.single k 1) := by
    have hinit : (Pi.single k (1 : ℂ)) = (1 : ℂ) • Pi.single k 1 + (0 : ℂ) • Pi.single k4 1 := by
      simp
    simp only [rccx3, Circuit.sequence, Circuit.eval_seq, Circuit.eval_identity,
      Circuit.eval_onRegister, one_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    obtain ⟨a1, b1, hs1⟩ := span2_mem_word 2 [.H, .T] k k4 hex0 hex1 h4 h0 1 0
    have hs1' : ((QRegister.singleton (2 : Wire 3)).embedUnitary
        (CliffordT.Gate1.wordCircuit [.H, .T]).eval).1 *ᵥ Pi.single k 1 =
        a1 • Pi.single k 1 + b1 • Pi.single k4 1 := by rw [← hs1, ← hinit]
    rw [hs1', hc1 a1 b1, ← hs1', hseq2, hseq2]
    simp only [← List.append_assoc]
    obtain ⟨a2, b2, hs2⟩ := span2_mem_word 2 ([.H, .T] ++ wc1 ++ [.T, .S, .Z]) k k4
      hex0 hex1 h4 h0 1 0
    have hs2' : ((QRegister.singleton (2 : Wire 3)).embedUnitary
        (CliffordT.Gate1.wordCircuit ([.H, .T] ++ wc1 ++ [.T, .S, .Z])).eval).1 *ᵥ
        Pi.single k 1 = a2 • Pi.single k 1 + b2 • Pi.single k4 1 := by rw [← hs2, ← hinit]
    rw [hs2', hc0 a2 b2, ← hs2', hseq2, hseq2]
    simp only [← List.append_assoc]
    obtain ⟨a3, b3, hs3⟩ := span2_mem_word 2
      ([.H, .T] ++ wc1 ++ [.T, .S, .Z] ++ wc0 ++ [.T]) k k4 hex0 hex1 h4 h0 1 0
    have hs3' : ((QRegister.singleton (2 : Wire 3)).embedUnitary
        (CliffordT.Gate1.wordCircuit
          ([.H, .T] ++ wc1 ++ [.T, .S, .Z] ++ wc0 ++ [.T])).eval).1 *ᵥ
        Pi.single k 1 = a3 • Pi.single k 1 + b3 • Pi.single k4 1 := by rw [← hs3, ← hinit]
    rw [hs3', hc1 a3 b3, ← hs3', hseq2, hseq2]
    simp only [← List.append_assoc]
  have hid_word (α β : ℂ) (k k4 : Fin (2 ^ 3)) :
      α • Pi.single k 1 + β • Pi.single k4 1 =
        ((QRegister.singleton (2 : Wire 3)).embedUnitary
          (CliffordT.Gate1.wordCircuit []).eval).1 *ᵥ
          (α • Pi.single k 1 + β • Pi.single k4 1) := by
    simp [CliffordT.Gate1.wordCircuit]
  have heval_col0 (w : List CliffordT.Gate1) (M : CliffordT.CyclotomicMat2)
      (hm : (CliffordT.GateTrace.leaf w M 2).checkFrom .one = some M)
      (k k4 : Fin (2 ^ 3))
      (hex0 : (QRegister.singleton (2 : Wire 3)).extractIndex k = 0)
      (h4 : ∀ q : Wire 3, basisBits 3 k4 q =
        if q = 2 then basisBits 1 (1 : Fin 2) 0 else basisBits 3 k q) :
      ((QRegister.singleton (2 : Wire 3)).embedUnitary
        (CliffordT.Gate1.wordCircuit w).eval).1 *ᵥ (Pi.single k 1) =
        M.toMatrix 0 0 • Pi.single k 1 + M.toMatrix 1 0 • Pi.single k4 1 := by
    have hM : (CliffordT.Gate1.wordCircuit w).eval.1 = M.toMatrix :=
      CliffordT.GateTrace.eval_toCircuit_of_checkFrom (.leaf w M 2) M hm
    rw [singleton_embedUnitary_mulVec_of_zero 2 (CliffordT.Gate1.wordCircuit w).eval
      k k4 hex0 h4, hM]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hrun 0 4 (by decide) (by decide) (by decide) (by decide) [] []
      (fun α β ↦ (hcnot_id (by decide) (by decide) (by decide) α β).trans (hid_word α β 0 4))
      (fun α β ↦ (hcnot_id (by decide) (by decide) (by decide) α β).trans (hid_word α β 0 4)),
      heval_col0 _ .one rfl 0 4 (by decide) (by decide),
      CliffordT.CyclotomicMat2.toMatrix_one]
    simp
  · rw [hrun 1 5 (by decide) (by decide) (by decide) (by decide) [] [.X]
      (fun α β ↦ (hcnot_id (by decide) (by decide) (by decide) α β).trans (hid_word α β 1 5))
      (fun α β ↦ hcnot_x (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) α β),
      heval_col0 _ ⟨0, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩⟩ rfl 1 5
        (by decide) (by decide),
      cycMat_Z_toMatrix_col0.1, cycMat_Z_toMatrix_col0.2, one_smul, zero_smul, add_zero]
  · rw [hrun 2 6 (by decide) (by decide) (by decide) (by decide) [.X] []
      (fun α β ↦ hcnot_x (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) α β)
      (fun α β ↦ (hcnot_id (by decide) (by decide) (by decide) α β).trans (hid_word α β 2 6)),
      heval_col0 _ .one rfl 2 6 (by decide) (by decide),
      CliffordT.CyclotomicMat2.toMatrix_one]
    simp
  · rw [hrun 3 7 (by decide) (by decide) (by decide) (by decide) [.X] [.X]
      (fun α β ↦ hcnot_x (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) α β)
      (fun α β ↦ hcnot_x (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) α β),
      heval_col0 _ ⟨0, ⟨0, 0, 0, 0⟩, ⟨0, 0, -1, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩⟩ rfl 3 7
        (by decide) (by decide),
      cycMat_iX_toMatrix_col0.1, cycMat_iX_toMatrix_col0.2, zero_smul, zero_add]

/-- Exact `10-T` post-product tree circuit on `4` wires (`4 T` `rccx3` + `2` CNOTs + `6 T`
`zeroCtrlH`). -/
def postFactor15Circuit : Circuit 4 :=
  Circuit.sequence [
    rccx3.onRegister (QRegister.triple 2 3 1 (by decide) (by decide) (by decide)),
    Circuit.CNOT 2 3 (by decide),
    Circuit.CNOT 1 3 (by decide),
    Catalyst.zeroCtrlH.onRegister (QRegister.pair 1 0 (by decide)),
    Catalyst.zeroCtrlH.onRegister (QRegister.pair 2 1 (by decide)),
    Catalyst.zeroCtrlH.onRegister (QRegister.pair 3 2 (by decide))
  ]

@[simp]
theorem postFactor15Circuit_count_toff : postFactor15Circuit.count PrimitiveGate.TOFF = 0 := by
  simp [postFactor15Circuit]

@[simp]
theorem postFactor15Circuit_count_t : postFactor15Circuit.count PrimitiveGate.T = 10 := by
  simp [postFactor15Circuit]

private lemma triple231_rccx3_mulVec :
    let r := QRegister.triple (2 : Wire 4) 3 1 (by decide) (by decide) (by decide)
    (rccx3.onRegister r).eval.1 *ᵥ (Pi.single 0 1) = Pi.single 0 1 ∧
    (rccx3.onRegister r).eval.1 *ᵥ (Pi.single 8 1) = Pi.single 8 1 ∧
    (rccx3.onRegister r).eval.1 *ᵥ (Pi.single 4 1) = Pi.single 4 1 ∧
    (rccx3.onRegister r).eval.1 *ᵥ (Pi.single 12 1) = Complex.I • Pi.single 14 1 := by
  intro r
  have hrep (k : Fin 16) (b : Fin (2 ^ 3)) (k' : Fin 16)
      (h : ∀ q : Wire 4, basisBits 4 k' q =
        if q = 2 then basisBits 3 b 0
        else if q = 3 then basisBits 3 b 1
        else if q = 1 then basisBits 3 b 2
        else basisBits 4 k q) :
      r.replaceIndex k b = k' := by
    apply (basisBits 4).injective
    funext q
    rw [h q]
    by_cases hq2 : q = 2
    · subst hq2; simpa [r] using r.basisBits_replaceIndex_apply k b 0
    · by_cases hq3 : q = 3
      · subst hq3; simpa [r, hq2] using r.basisBits_replaceIndex_apply k b 1
      · by_cases hq1 : q = 1
        · subst hq1; simpa [r, hq2, hq3] using r.basisBits_replaceIndex_apply k b 2
        · rw [ite_eq_right hq2, ite_eq_right hq3, ite_eq_right hq1]
          refine r.basisBits_replaceIndex_of_not_mem k b q ?_
          rintro ⟨i, hi⟩
          fin_cases i
          · exact hq2 hi.symm
          · exact hq3 hi.symm
          · exact hq1 hi.symm
  have ⟨hr0, hr1, hr2, hr3⟩ := rccx3_mulVec_zero
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Circuit.eval_onRegister, QRegister.embedUnitary_val, r.embedMatrix_mulVec_single_factors,
      show r.extractIndex (0 : Fin 16) = 0 by decide, hr0, r.tensorState_single_replaceIndex,
      hrep 0 0 0 (by decide)]
  · rw [Circuit.eval_onRegister, QRegister.embedUnitary_val, r.embedMatrix_mulVec_single_factors,
      show r.extractIndex (8 : Fin 16) = 2 by decide, hr2, r.tensorState_single_replaceIndex,
      hrep 8 2 8 (by decide)]
  · rw [Circuit.eval_onRegister, QRegister.embedUnitary_val, r.embedMatrix_mulVec_single_factors,
      show r.extractIndex (4 : Fin 16) = 1 by decide, hr1, r.tensorState_single_replaceIndex,
      hrep 4 1 4 (by decide)]
  · rw [Circuit.eval_onRegister, QRegister.embedUnitary_val, r.embedMatrix_mulVec_single_factors,
      show r.extractIndex (12 : Fin 16) = 3 by decide, hr3, r.tensorState_smul_left,
      r.tensorState_single_replaceIndex, hrep 12 7 14 (by decide)]

/-- Ideal per-stage unitaries for the `4`-qubit factored `L = 15 = 5 × 3` splitter. -/
noncomputable def idealFactoredMag15Steps (U5 U3 : Unitary 2) : List (Unitary (2 ^ 4)) :=
  [ (QRegister.singleton 2).embedUnitary U5,
    (QRegister.singleton 3).embedUnitary U3,
    postFactor15Circuit.eval ]

/-- Ideal `4`-qubit unitary corresponding to the factored `L = 15 = 5 × 3` splitter. -/
noncomputable def idealFactoredMag15Of (U5 U3 : Unitary 2) : Unitary (2 ^ 4) :=
  (idealFactoredMag15Steps U5 U3).reverse.prod

theorem normSq_idealFactoredMag15Of (U5 U3 : Unitary 2)
    (h5_0 : Complex.normSq (U5.1 0 0) = 4 / 5)
    (h5_1 : Complex.normSq (U5.1 1 0) = 1 / 5)
    (h3_0 : Complex.normSq (U3.1 0 0) = 2 / 3)
    (h3_1 : Complex.normSq (U3.1 1 0) = 1 / 3)
    (x : Fin (2 ^ 4)) :
    Complex.normSq (((idealFactoredMag15Of U5 U3).1 *ᵥ basisState 0) x) =
      if x.val < 15 then 1 / (15 : ℝ) else 0 := by
  let β0 : ℂ := (U5.1 0 0 * U3.1 0 0) * ((√2 : ℂ)⁻¹ * ((√2 : ℂ)⁻¹ * (√2 : ℂ)⁻¹))
  let β8 : ℂ := (U5.1 0 0 * U3.1 1 0) * ((√2 : ℂ)⁻¹ * (√2 : ℂ)⁻¹)
  let β12 : ℂ := (U5.1 1 0 * U3.1 0 0) * (√2 : ℂ)⁻¹
  let β14 : ℂ := (U5.1 1 0 * U3.1 1 0) * Complex.I
  have ⟨hr0, hr8, hr4, hr12⟩ := triple231_rccx3_mulVec
  have hvec : (idealFactoredMag15Of U5 U3).1 *ᵥ basisState 0 =
      β0 • (Pi.single 0 1 + Pi.single 4 1 + (Pi.single 2 1 + Pi.single 6 1) +
        (Pi.single 1 1 + Pi.single 5 1 + (Pi.single 3 1 + Pi.single 7 1))) +
      β8 • (Pi.single 8 1 + Pi.single 10 1 + (Pi.single 9 1 + Pi.single 11 1)) +
      β12 • (Pi.single 12 1 + Pi.single 13 1) +
      β14 • Pi.single 14 1 := by
    rw [idealFactoredMag15Of, idealFactoredMag15Steps, basisState]
    rw [reverse_prod_cons_mulVec]
    conv_lhs =>
      enter [2]
      rw [singleton_embedUnitary_mulVec_of_zero 2 U5 0 4 (by decide) (by decide)]
    rw [reverse_prod_cons_mulVec]
    conv_lhs =>
      enter [2]
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        singleton_embedUnitary_mulVec_of_zero 3 U3 0 8 (by decide) (by decide),
        singleton_embedUnitary_mulVec_of_zero 3 U3 4 12 (by decide) (by decide),
        smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
    rw [reverse_prod_cons_mulVec]
    simp only [List.reverse_nil, List.prod_nil, OneMemClass.coe_one, Matrix.one_mulVec]
    simp only [postFactor15Circuit, Circuit.sequence, Circuit.eval_seq, Circuit.eval_identity,
      one_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hr0, hr8, hr4, hr12, smul_smul]
    rw [cnot_pair_mulVec_of_zero 2 3 (by decide) 0 (Or.inl (by decide)),
      cnot_pair_mulVec_of_zero 2 3 (by decide) 8 (Or.inr (by decide)),
      cnot_pair_mulVec_of_one_zero 2 3 (by decide) 4 12 (by decide) (by decide),
      cnot_pair_mulVec_of_one_one 2 3 (by decide) 14 6 (by decide) (by decide)]
    rw [cnot_pair_mulVec_of_zero 1 3 (by decide) 0 (Or.inl (by decide)),
      cnot_pair_mulVec_of_zero 1 3 (by decide) 8 (Or.inr (by decide)),
      cnot_pair_mulVec_of_zero 1 3 (by decide) 12 (Or.inr (by decide)),
      cnot_pair_mulVec_of_one_zero 1 3 (by decide) 6 14 (by decide) (by decide)]
    simp only [Circuit.eval_onRegister]
    rw [zeroCtrlH_pair_mulVec_of_zero 1 0 (by decide) 0 1 (by decide) (by decide),
      zeroCtrlH_pair_mulVec_of_zero 1 0 (by decide) 8 9 (by decide) (by decide),
      zeroCtrlH_pair_mulVec_of_zero 1 0 (by decide) 12 13 (by decide) (by decide),
      zeroCtrlH_pair_mulVec_of_one 1 0 (by decide) 14 (Or.inl (by decide))]
    simp only [smul_add, Matrix.mulVec_add, Matrix.mulVec_smul]
    rw [zeroCtrlH_pair_mulVec_of_zero 2 1 (by decide) 0 2 (by decide) (by decide),
      zeroCtrlH_pair_mulVec_of_zero 2 1 (by decide) 1 3 (by decide) (by decide),
      zeroCtrlH_pair_mulVec_of_zero 2 1 (by decide) 8 10 (by decide) (by decide),
      zeroCtrlH_pair_mulVec_of_zero 2 1 (by decide) 9 11 (by decide) (by decide),
      zeroCtrlH_pair_mulVec_of_one 2 1 (by decide) 12 (Or.inl (by decide)),
      zeroCtrlH_pair_mulVec_of_one 2 1 (by decide) 13 (Or.inl (by decide)),
      zeroCtrlH_pair_mulVec_of_one 2 1 (by decide) 14 (Or.inr (by decide))]
    simp only [smul_add, Matrix.mulVec_add, Matrix.mulVec_smul]
    rw [zeroCtrlH_pair_mulVec_of_zero 3 2 (by decide) 0 4 (by decide) (by decide),
      zeroCtrlH_pair_mulVec_of_zero 3 2 (by decide) 2 6 (by decide) (by decide),
      zeroCtrlH_pair_mulVec_of_zero 3 2 (by decide) 1 5 (by decide) (by decide),
      zeroCtrlH_pair_mulVec_of_zero 3 2 (by decide) 3 7 (by decide) (by decide),
      zeroCtrlH_pair_mulVec_of_one 3 2 (by decide) 8 (Or.inl (by decide)),
      zeroCtrlH_pair_mulVec_of_one 3 2 (by decide) 10 (Or.inl (by decide)),
      zeroCtrlH_pair_mulVec_of_one 3 2 (by decide) 9 (Or.inl (by decide)),
      zeroCtrlH_pair_mulVec_of_one 3 2 (by decide) 11 (Or.inl (by decide)),
      zeroCtrlH_pair_mulVec_of_one 3 2 (by decide) 12 (Or.inr (by decide)),
      zeroCtrlH_pair_mulVec_of_one 3 2 (by decide) 13 (Or.inr (by decide)),
      zeroCtrlH_pair_mulVec_of_one 3 2 (by decide) 14 (Or.inr (by decide))]
    dsimp only [β0, β8, β12, β14]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hns0 : Complex.normSq β0 = 1 / 15 := by
    dsimp only [β0]
    rw [map_mul, map_mul, map_mul, map_mul, h5_0, h3_0, normSq_inv_sqrt2]
    norm_num
  have hns8 : Complex.normSq β8 = 1 / 15 := by
    dsimp only [β8]
    rw [map_mul, map_mul, map_mul, h5_0, h3_1, normSq_inv_sqrt2]
    norm_num
  have hns12 : Complex.normSq β12 = 1 / 15 := by
    dsimp only [β12]
    rw [map_mul, map_mul, h5_1, h3_0, normSq_inv_sqrt2]
    norm_num
  have hns14 : Complex.normSq β14 = 1 / 15 := by
    dsimp only [β14]
    rw [map_mul, map_mul, h5_1, h3_1, Complex.normSq_I]
    norm_num
  rw [hvec]
  fin_cases x <;>
    simp [Pi.add_apply, Pi.smul_apply, hns0, hns8, hns12, hns14]

/-! ## Section 2: `81`/`86`/`96`/`97-T` Ancilla-Free Factored `L = 30` Splitters -/

attribute [local irreducible] postFactor15Circuit

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OptFactoredMag30AndCoin9
