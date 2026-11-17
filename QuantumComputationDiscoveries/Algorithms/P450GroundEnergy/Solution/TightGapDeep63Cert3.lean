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
# Quartet (`33`/`30`, `D = 3,000`) Kernel Certificates (Part 3)

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

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63Cert3
open QuantumComputation.Specs QuantumComputation.Specs.P450

open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63DataA
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63DataB
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63DataC

lemma rot_blk_6_ok : checkRotBlkLeavesCert 131 22 = true := by
  decide +kernel

lemma rot_blk_7_ok : checkRotBlkLeavesCert 153 21 = true := by
  decide +kernel

lemma rot_blk_8_ok : checkRotBlkLeavesCert 174 22 = true := by
  decide +kernel

lemma rot_blk_9_ok : checkRotBlkLeavesCert 196 22 = true := by
  decide +kernel

lemma rot_blk_10_ok : checkRotBlkLeavesCert 218 22 = true := by
  decide +kernel

lemma rot_blk_11_ok : checkRotBlkLeavesCert 240 21 = true := by
  decide +kernel

lemma diag_e4_ok :
    checkDiagEighthCert deepDetsE4 wireWE3Cert wireWE4Cert
      diagQuadsE4Cert = true := by
  decide +kernel

lemma diag_e5_ok :
    checkDiagEighthCert deepDetsE5 wireWE4Cert wireWE5Cert
      diagQuadsE5Cert = true := by
  decide +kernel

lemma modes7_cert_4a_ok : checkBlockModesSliceCert 4 0 7 0 140264275746310694 = true := by
  decide +kernel

lemma modes7_cert_4b_ok : checkBlockModesSliceCert 4 7 7 0 74073717900299902 = true := by
  decide +kernel

lemma modes7_cert_5a_ok : checkBlockModesSliceCert 5 0 7 0 53901277417771916 = true := by
  decide +kernel

lemma modes7_cert_5b_ok : checkBlockModesSliceCert 5 7 7 0 75550622118016998 = true := by
  decide +kernel

lemma s12_slice_6_ok : checkPhase12SliceCert 630 120 s12Slice6Cert = true := by
  decide +kernel

lemma s12_slice_7_ok : checkPhase12SliceCert 750 130 s12Slice7Cert = true := by
  decide +kernel

lemma s12_slice_8_ok : checkPhase12SliceCert 880 135 s12Slice8Cert = true := by
  decide +kernel

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63Cert3
