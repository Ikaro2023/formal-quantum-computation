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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TailShiftWindow46847

/-!
# Rational Two-Gear Error-Budget Companion `(M = 47,487, m1 = 7)`
Provides `0`-`decide` rational `RefStaticBox 47487`, `BaseRayQuantBox 47487`, and
`TailShiftRayQuantSuperBox 47487 45 10 7` bounds for `deep63` (`-130.1526` Ha) across
`dh ≤ 4000 / 10 ^ 10`.

## References
- A. Luis and J. Peřina, *Phys. Rev. A* **54**, 4564 (1996), DOI: 10.1103/PhysRevA.54.4564.
- M. Möttönen et al., *Phys. Rev. Lett.* **93**, 130502 (2004), DOI: 10.1103/PhysRevLett.93.130502.
- R. Babbush et al., *Phys. Rev. X* **8**, 041015 (2018), DOI: 10.1103/PhysRevX.8.041015.
- J. Lee et al., *PRX Quantum* **2**, 030305 (2021), DOI: 10.1103/PRXQuantum.2.030305.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TailShiftBox
open QuantumComputation.Specs QuantumComputation.Specs.P450
open Solution.TwoGearBox

/-- Quantization error shift `4000 / 10 ^ 10`. -/
noncomputable abbrev dh4000 : ℝ := 4000 / 10 ^ 10
/-- Certified reference energy upper bound `-130.1526` Ha (`TightGapDeep63Cert`). -/
noncomputable abbrev e_deep63 : ℝ := -130152600 / 10 ^ 6
/-- Energy-gap upper bound `2417421 / 500000` Ha for `e_deep63`. -/
noncomputable abbrev g_deep63 : ℝ := 2417421 / 500000
/-- Effective spectral-gap factor `15151897709 / 500000000` for `e_deep63`. -/
noncomputable abbrev f_deep63 : ℝ := 15151897709 / 500000000
/-- Clamped-estimator slope factor `99487 / 100000` for `M = 47,487`. -/
noncomputable abbrev kp487 : ℝ := 99487 / 100000

theorem dhBounds_4000 : (0 : ℝ) ≤ dh4000 ∧ dh4000 ≤ 2 / 1000 := by
  unfold dh4000
  norm_num

theorem eRef_deep63_le : (-130.1526 : ℝ) ≤ e_deep63 := by
  unfold e_deep63
  norm_num

theorem refStatic_47487_deep63 :
    RefStaticBox 47487 e_deep63 g_deep63 f_deep63 kp487
      (473568969361167567073350488000273701 / 474880000000000000000000000000000000000) := by
  unfold RefStaticBox e_deep63 g_deep63 f_deep63 kp487
  norm_num

theorem uTS_47487_10 {ci d dS dT dM dh e g f kp : ℝ}
    (hb : BaseRayQuantBox 47487 ci w5 (d15 d) dh e g f kp)
    (h : d15 dS ≤ (1024 : ℝ) * d15 d ∧ d15 dT ≤ (384 : ℝ) * d15 d ∧
      d15 dM ≤ (2 ^ 7 : ℝ) * d15 d) :
    TailShiftRayQuantSuperBox 47487 45 10 7 ci w5
      (d15 dS) (d15 dT) (d15 dM) (d15 d) dh e g f kp :=
  tailShiftRayQuantSuperBox_of_baseBox (lStd := 1024) (lTail := 384)
    (by decide) hb h.1 h.2.1 h.2.2 le_rfl

theorem tailShiftBox_fast_47487_10_7_deep63_dh5700 {dh : ℝ}
    (hdh0 : 0 ≤ dh) (hdhUb : dh ≤ 5700 / 10 ^ 10) :
    TailShiftRayQuantSuperBox 47487 45 10 7 cFa w5 0 0 0 0 dh
      e_deep63 g_deep63 f_deep63 kp487 := by
  have hBase : BaseRayQuantBox 47487 cFa w5 (d15 0) dh e_deep63 g_deep63 f_deep63 kp487 :=
    baseRayQuantBox_of_refStatic refStatic_47487_deep63 ⟨hdh0, by linarith⟩ (by
      unfold cFa w5 d15 g_deep63
      norm_num
      linarith)
  simpa only [d15, zero_div] using
    uTS_47487_10 (d := 0) (dS := 0) (dT := 0) (dM := 0) hBase (by norm_num [d15])

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TailShiftBox
end
