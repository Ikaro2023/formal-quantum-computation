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
# Quartet (`33`/`30`, `D = 3,000`) Kernel Certificates (`TightGapDeep63Cert2`)

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

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63Cert2
open QuantumComputation.Specs QuantumComputation.Specs.P450

open TightGapDeep63DataA
open TightGapDeep63DataB
open TightGapDeep63DataC

lemma rot_blk_0_ok : checkRotBlkLeavesCert 0 22 = true := by
  decide +kernel

lemma rot_blk_1_ok : checkRotBlkLeavesCert 22 22 = true := by
  decide +kernel

lemma rot_blk_2_ok : checkRotBlkLeavesCert 44 22 = true := by
  decide +kernel

lemma rot_blk_3_ok : checkRotBlkLeavesCert 66 21 = true := by
  decide +kernel

lemma rot_blk_4_ok : checkRotBlkLeavesCert 87 22 = true := by
  decide +kernel

lemma rot_blk_5_ok : checkRotBlkLeavesCert 109 22 = true := by
  decide +kernel

lemma diag_e2_ok :
    checkDiagEighthCert deepDetsE2 wireWE1Cert wireWE2Cert
      diagQuadsE2Cert = true := by
  decide +kernel

lemma diag_e3_ok :
    checkDiagEighthCert deepDetsE3 wireWE2Cert wireWE3Cert
      diagQuadsE3Cert = true := by
  decide +kernel

lemma modes7_cert_2a_ok : checkBlockModesSliceCert 2 0 7 0 62876677076031126 = true := by
  decide +kernel

lemma modes7_cert_2b_ok : checkBlockModesSliceCert 2 7 7 0 55712353702942466 = true := by
  decide +kernel

lemma modes7_cert_3a_ok : checkBlockModesSliceCert 3 0 7 0 52799178385930882 = true := by
  decide +kernel

lemma modes7_cert_3b_ok : checkBlockModesSliceCert 3 7 7 0 55426764890255132 = true := by
  decide +kernel

lemma s12_slice_3_ok : checkPhase12SliceCert 298 105 s12Slice3Cert = true := by
  decide +kernel

lemma s12_slice_4_ok : checkPhase12SliceCert 403 107 s12Slice4Cert = true := by
  decide +kernel

lemma s12_slice_5_ok : checkPhase12SliceCert 510 120 s12Slice5Cert = true := by
  decide +kernel

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63Cert2
