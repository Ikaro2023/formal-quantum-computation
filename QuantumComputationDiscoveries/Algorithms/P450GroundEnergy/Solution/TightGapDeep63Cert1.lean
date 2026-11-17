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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TightGapDeep63Base

/-!
# Quartet (`33`/`30`, `D = 3,000`) Kernel Certificates (Part 1)

Kernel certificate module (`15` `decide +kernel` checks) for the
`-130.1526` Ha variational bound on `thcHamiltonian P450.dfthc`.

## References

* B. Huron, J. P. Malrieu, and P. Rancurel, "Iterative perturbation calculations of ground and
  excited state energies from multiconfigurational zeroth-order wavefunctions," *J. Chem. Phys.*
  **58**(12), 5745–5759 (1973), https://doi.org/10.1063/1.1679199.
* G. H. Low et al., "Fast Quantum Simulation of Electronic Structure by Spectral Amplification,"
  *Phys. Rev. X* **15**(4), 041016 (2025), https://doi.org/10.1103/pb2g-j9cw.
* J. J. Goings et al., "Reliably assessing the electronic structure of cytochrome P450 on today's
  classical computers and tomorrow's quantum computers," *Proc. Natl. Acad. Sci. U.S.A.*
  **119**(38), e2203533119 (2022), https://doi.org/10.1073/pnas.2203533119.
-/

set_option maxRecDepth 100000

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63Cert1
open QuantumComputation.Specs QuantumComputation.Specs.P450

open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63DataA
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63DataB
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63DataC

lemma cayley_r0_ok : checkCayleyRange0Cert = true := by
  decide +kernel

lemma cayley_r1_ok : checkCayleyRange1Cert = true := by
  decide +kernel

lemma cayley_r2_ok : checkCayleyRange2Cert = true := by
  decide +kernel

lemma rot_ob_0_ok : checkRotObLeavesRangeCert 0 20 = true := by
  decide +kernel

lemma rot_ob_1_ok : checkRotObLeavesRangeCert 20 19 = true := by
  decide +kernel

lemma rot_ob_2_ok : checkRotObLeavesRangeCert 39 19 = true := by
  decide +kernel

lemma diag_e0_ok :
    checkDiagEighthCert deepDetsE0 (List.replicate 116 0) wireWE0Cert
      diagQuadsE0Cert = true := by
  decide +kernel

lemma diag_e1_ok :
    checkDiagEighthCert deepDetsE1 wireWE0Cert wireWE1Cert
      diagQuadsE1Cert = true := by
  decide +kernel

lemma modes7_cert_0a_ok : checkBlockModesSliceCert 0 0 7 0 112852375908234998 = true := by
  decide +kernel

lemma modes7_cert_0b_ok : checkBlockModesSliceCert 0 7 7 0 107543156899494064 = true := by
  decide +kernel

lemma modes7_cert_1a_ok : checkBlockModesSliceCert 1 0 7 0 177901251113850966 = true := by
  decide +kernel

lemma modes7_cert_1b_ok : checkBlockModesSliceCert 1 7 7 0 79353092224761196 = true := by
  decide +kernel

lemma s12_slice_0_ok : checkPhase12SliceCert 0 90 s12Slice0Cert = true := by
  decide +kernel

lemma s12_slice_1_ok : checkPhase12SliceCert 90 103 s12Slice1Cert = true := by
  decide +kernel

lemma s12_slice_2_ok : checkPhase12SliceCert 193 105 s12Slice2Cert = true := by
  decide +kernel

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63Cert1
