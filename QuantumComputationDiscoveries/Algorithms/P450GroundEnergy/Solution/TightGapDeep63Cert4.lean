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
# Quartet (`33`/`30`, `D = 3,000`) Kernel Certificates (Part 4)

Kernel certificate module (`10` `decide +kernel` checks) for the
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

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63Cert4
open QuantumComputation.Specs QuantumComputation.Specs.P450

open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63DataA
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63DataB
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63DataC

lemma diag_e6_ok :
    checkDiagEighthCert deepDetsE6 wireWE5Cert wireWE6Cert
      diagQuadsE6Cert = true := by
  decide +kernel

lemma diag_e7_ok :
    checkDiagEighthCert deepDetsE7 wireWE6Cert wireWE7Cert
      diagQuadsE7Cert = true := by
  decide +kernel

lemma s12_merge_ok : checkPhase12MergeCert = true := by
  decide +kernel

lemma modes7_cert_6a_ok : checkBlockModesSliceCert 6 0 7 0 76628909804683484 = true := by
  decide +kernel

lemma modes7_cert_6b_ok : checkBlockModesSliceCert 6 7 7 0 72300328432691594 = true := by
  decide +kernel

lemma modes7_cert_7a_ok : checkBlockModesSliceCert 7 0 7 0 82413563130943130 = true := by
  decide +kernel

lemma s12_slice_9_ok : checkPhase12SliceCert 1015 149 s12Slice9Cert = true := by
  decide +kernel

lemma s12_slice_10_ok : checkPhase12SliceCert 1164 160 s12Slice10Cert = true := by
  decide +kernel

lemma s12_slice_11_ok : checkPhase12SliceCert 1324 176 s12Slice11Cert = true := by
  decide +kernel

lemma s12_slice_12_ok : checkPhase12SliceCert 1500 201 s12Slice12Cert = true := by
  decide +kernel

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TightGapDeep63Cert4
