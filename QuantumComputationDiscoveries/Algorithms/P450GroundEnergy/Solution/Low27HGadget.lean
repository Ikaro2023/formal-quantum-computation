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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Keep9Symp14Data
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Inner18HadWSuperLegsA

/-! # `33`-Scratch (`390 T`) Keep-9 `HGadget` Symplectic QROM Loader
Exports `mainKeep9HGadget400LoadCirc` and `mainKeep9HGadget400LoadBundle` (`33` scratch, `390 T`)
on `keep9Hot24BoolTable` via `SelectSwapQROM.monoSandwichDyn` (`s = 5`,
`26` ANF scratch wires + `1` `wG` wire) around `HGadgetSympQromAux.midDyn` (Gidney, *Quantum* **2**,
74, 2018; Babbush *et al.*, *Phys. Rev. X* **8**, 041015, 2018; Low, Kliuchnikov, and Schaeffer,
*Quantum* **8**, 1375, 2024). -/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.MainLow27HGadget
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix Circuit Real HermitianMat BlockEncodingCore BlockEncodingCircuit
  QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution CoherentAlias AliasPrep
  Solution.Mobius126OneHot MidReflCtxRetain StepBound148Borrow
  Tuned162ScheduledSympQrom21 Tuned162StepSympAnfQrom21 StepAnfAndCoin14Core
  StepKeep9Symp14Data HGadgetSympQrom OptKeep9Symp14Data Inner18HadWSuperLegsA
open Solution.StepOuter8Pi145Outer (predProj_mulVec_ket)
open _root_.Function (update update_of_ne update_self update_idem update_eq_self)
open Solution.GroupUnary (predProj predProj_conjTranspose)
open Solution.SelectSwapQROM (zeroProjOn zeroProjOn_mulVec_ket
  zeroProjOn_conjTranspose bitSign bitSign_add basisBits_symm monoEval monoEval_zero anfScratchWidth
  allMonoReg allMonoReg_image_subset allMonoReg_apply_lt allMonoReg_apply_eq allMonoReg_apply_ge
  xorAndRegBits xorAndRegBits_apply_of_not_mem xorAndRegBits_apply_dst andSandwichDyn
  regAndWithWireSandwichDyn monoSandwichDyn count_monoSandwichDyn_toff count_monoSandwichDyn_t
  singleton_projector_zero_mulVec_ket disjoint_image_of_disjointWires)
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

local instance (priority := 1000000) instNeZeroTwoPowLow27 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

/-- Computable `390-T` (`33` scratch, `0 TOFF`) H-gadget `symp_14` `OneHot14LoadCirc2`. -/
def mainKeep9HGadget400LoadCirc (Var : Type) : OneHot14LoadCirc2 Var 33 390 :=
  OneHot14LoadCirc2.ofHGadgetPlan Var optSymp14Plan

/-- `390-T` (`33` scratch, `0 TOFF`) H-gadget `symp_14` `OneHot14LoadBundle_3` on `Unit`. -/
def mainKeep9HGadget400LoadBundle : OneHot14LoadBundle_3 Unit 33 390 keep9Hot24BoolTable :=
  OneHot14LoadBundle_3.ofHGadgetPlan Unit optSymp14Plan keep9Hot24BoolTable
    optSymp14Plan_targetBoolTable_eq

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.MainLow27HGadget
