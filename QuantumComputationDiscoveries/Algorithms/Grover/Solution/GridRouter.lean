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

public import QuantumComputation.QuantumHoareLogic.ResourceCounting.CostBounds
public import QuantumComputation.QuantumHoareLogic.ResourceCounting.PowerLawCost
public import QuantumComputation.Circuits.DynamicCircuit
public import Mathlib.Data.Finset.Powerset
public import QuantumComputation.QuantumHoareLogic.WP
public import QuantumComputation.Maths.Trigonometry
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.BaselineRouter
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Warm2M2MultiStage
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.LongTailM1K2Only
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.GroverM1PulseCerts
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.GaussianHammingMidPZoomCerts
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonP01
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMux
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.SchurWeylL2BallM1K32Only
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.GaussianHammingZoomK2GH96Certs
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.MpzGHZoomCertsB
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kHiM1024F256KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kHiM128K128KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kHiM128K256KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kHiM256K256KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kHiM512F256KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kHiM512M1024K128KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kLowM2K128KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kLowM2K256KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kLowM4K128KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kLowM4K256KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kLowM8K128KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kLowM8K256KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM16K128KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM16K256KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM32K128KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM32L64HiCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM64K128KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM64K256KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.GroverM1PulseK64Cert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kHiM256K512KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM32K512KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kLowM4K512L248KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM16K512KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kHiM256CoCert

/-
# Unified 121-Cell Master Router (`GridRouter`)
-/

@[expose] public section

namespace QuantumComputation.Specs.GroverFindAll
open Rk128kHiM1024F256KrCert
  Rk128kHiM128K128KrCert
  Rk128kHiM128K256KrCert
  Rk128kHiM256CoCert
  Rk128kHiM256K256KrCert
  Rk128kHiM256K512KrCert
  Rk128kHiM512F256KrCert
  Rk128kHiM512M1024K128KrCert
  Rk128kLowM2K128KrCert
  Rk128kLowM2K256KrCert
  Rk128kLowM4K128KrCert
  Rk128kLowM4K256KrCert
  Rk128kLowM4K512L248KrCert
  Rk128kLowM8K128KrCert
  Rk128kLowM8K256KrCert
  Rk128kMidM16K128KrCert
  Rk128kMidM16K256KrCert
  Rk128kMidM16K512KrCert
  Rk128kMidM32K128KrCert
  Rk128kMidM32K512KrCert
  Rk128kMidM32L64HiCert
  Rk128kMidM64K128KrCert
  Rk128kMidM64K256KrCert GroverM1PulseK64Cert

open Operator ResourceCounting Real
open scoped NNReal NNRat

/-- Computable membership test for `groverGrid = {2^0,..., 2^10}`. -/
def gridElem (x : ℕ) : Bool :=
  x == 1 || x == 2 || x == 4 || x == 8 || x == 16 || x == 32 ||
    x == 64 || x == 128 || x == 256 || x == 512 || x == 1024

/-- Computable cell selector claiming all `121` cells of `groverGrid × groverGrid`. -/
def gridCell (m k : ℕ) : Bool :=
  gridElem m && gridElem k

theorem gridElem_iff (x : ℕ) :
    gridElem x = true ↔ ∃ i ∈ Finset.range 11, 2 ^ i = x := by
  unfold gridElem; simp only [Bool.or_eq_true, beq_iff_eq, Finset.mem_range]
  constructor
  · rintro ((((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨1, by omega, rfl⟩
    · exact ⟨2, by omega, rfl⟩
    · exact ⟨3, by omega, rfl⟩
    · exact ⟨4, by omega, rfl⟩
    · exact ⟨5, by omega, rfl⟩
    · exact ⟨6, by omega, rfl⟩
    · exact ⟨7, by omega, rfl⟩
    · exact ⟨8, by omega, rfl⟩
    · exact ⟨9, by omega, rfl⟩
    · exact ⟨10, by omega, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    interval_cases i <;> simp

/-- Subset marking oracle on `n + 1` qubits matching `groverSetMarkingOracle`. -/
noncomputable abbrev gridSetMarkingOracle {n : ℕ} (S : Finset (Fin (2 ^ n))) :
    Unitary (2 ^ (n + 1)) :=
  permutationUnitary (tableAddPerm fun x ↦ if x ∈ S then (1 : Fin (2 ^ 1)) else 0)

/-- Synchronous `m`-slot parallel marking oracle matching `groverParallelMarkingOracle`. -/
noncomputable abbrev gridMarkingOracle {n : ℕ} (m : ℕ)
    (S : Finset (Fin (2 ^ n))) : Unitary (2 ^ ((n + 1) * m)) :=
  (List.ofFn fun i : Fin m ↦
    (QRegister.block (i.val * (n + 1)) (n + 1) (by nlinarith [i.isLt])).embedUnitary
      (gridSetMarkingOracle S)).prod

/-- Base-`2 ^ n` target-set decoder matching `decodeTargets`. -/
def gridDecodeTargets (n k : ℕ) (z : ℤ) : Finset (Fin (2 ^ n)) :=
  (Finset.range k).image fun i ↦
    ⟨(z.toNat / (2 ^ n) ^ i) % 2 ^ n, Nat.mod_lt _ (by positivity)⟩

/-- Selector for `11` `k = 1` cells. -/
def isArmK1Boundary (m k : ℕ) : Bool :=
  (m == 1 && k == 1) || (m == 2 && k == 1) || (m == 4 && k == 1) ||
    (m == 8 && k == 1) || (m == 16 && k == 1) || (m == 32 && k == 1) ||
    (m == 64 && k == 1) || (m == 128 && k == 1) || (m == 256 && k == 1) ||
    (m == 512 && k == 1) || (m == 1024 && k == 1)

/-- `1` `WarmJP01M2` cells. -/
def isArmWarmJP01M2 (m k : ℕ) : Bool :=
  (m == 2 && k == 4)

/-- `1` `LongTailM1K2Only` cells. -/
def isArmLongTailM1K2Only (m k : ℕ) : Bool :=
  (m == 1 && k == 2)

/-- `4` `GroverM1` cells. -/
def isArmGroverM1Pulse (m k : ℕ) : Bool :=
  (m == 1 && k == 128) || (m == 1 && k == 256) || (m == 1 && k == 512) ||
    (m == 1 && k == 1024)

/-- `1` `GaussianHammingMidPZoom` cells. -/
def isArmGaussianHammingMidPZoom (m k : ℕ) : Bool :=
  (m == 1024 && k == 4)

/-- `2` `JohnsonP01K2` cells. -/
def isArmJohnsonP01K2 (m k : ℕ) : Bool :=
  (m == 2 && k == 2) || (m == 4 && k == 2)

/-- `9` `JohnsonRampKickMux` cells. -/
def isArmJohnsonRampKickMux (m k : ℕ) : Bool :=
  (m == 2 && k == 512) || (m == 2 && k == 1024) || (m == 4 && k == 1024) ||
    (m == 8 && k == 512) || (m == 8 && k == 1024) || (m == 16 && k == 1024) ||
    (m == 32 && k == 1024) || (m == 64 && k == 512) || (m == 64 && k == 1024)

/-- `7` `JohnsonRampKickMuxHi` cells. -/
def isArmJohnsonRampKickMuxHi (m k : ℕ) : Bool :=
  (m == 128 && k == 512) || (m == 128 && k == 1024) || (m == 256 && k == 1024) ||
    (m == 512 && k == 512) || (m == 512 && k == 1024) || (m == 1024 && k == 512) ||
    (m == 1024 && k == 1024)

/-- `4` `SchurWeylL2BallM1K32Only` cells. -/
def isArmSchurWeylM1K32Only (m k : ℕ) : Bool :=
  (m == 1 && k == 4) || (m == 1 && k == 8) || (m == 1 && k == 16) ||
    (m == 1 && k == 32)

/-- `8` `GaussianHammingZoomK2GH96` cells. -/
def isArmGaussianHammingZoomK2GH96 (m k : ℕ) : Bool :=
  (m == 8 && k == 2) || (m == 16 && k == 2) || (m == 32 && k == 2) ||
    (m == 64 && k == 2) || (m == 128 && k == 2) || (m == 256 && k == 2) ||
    (m == 512 && k == 2) || (m == 1024 && k == 2)

/-- `6` `MpzGHMidP` cells. -/
def isArmMpzGHMidP (m k : ℕ) : Bool :=
  (m == 64 && k == 4) || (m == 128 && k == 4) || (m == 256 && k == 4) ||
    (m == 512 && k == 4) || (m == 512 && k == 8) || (m == 1024 && k == 8)

/-- `1` `Rkm128k` cells. -/
def isArmRkm128kC13 (m k : ℕ) : Bool :=
  (m == 1024 && k == 256)

/-- `5` `Rkm128k` cells. -/
def isArmRkm128kC08 (m k : ℕ) : Bool :=
  (m == 128 && k == 8) || (m == 128 && k == 16) || (m == 128 && k == 32) ||
    (m == 128 && k == 64) || (m == 128 && k == 128)

/-- `1` `Rkm128k` cells. -/
def isArmRkm128kC06 (m k : ℕ) : Bool :=
  (m == 128 && k == 256)

/-- `1` `Rkm128k` cells. -/
def isArmRkm128kC15 (m k : ℕ) : Bool :=
  (m == 256 && k == 256)

/-- `1` `Rkm128k` cells. -/
def isArmRkm128kC09 (m k : ℕ) : Bool :=
  (m == 512 && k == 256)

/-- `8` `Rkm128k` cells. -/
def isArmRkm128kC17 (m k : ℕ) : Bool :=
  (m == 512 && k == 16) || (m == 512 && k == 32) || (m == 512 && k == 64) ||
    (m == 512 && k == 128) || (m == 1024 && k == 16) || (m == 1024 && k == 32) ||
    (m == 1024 && k == 64) || (m == 1024 && k == 128)

/-- `5` `Rkm128k` cells. -/
def isArmRkm128kC07 (m k : ℕ) : Bool :=
  (m == 2 && k == 8) || (m == 2 && k == 16) || (m == 2 && k == 32) ||
    (m == 2 && k == 64) || (m == 2 && k == 128)

/-- `1` `Rkm128k` cells. -/
def isArmRkm128kC11 (m k : ℕ) : Bool :=
  (m == 2 && k == 256)

/-- `6` `Rkm128k` cells. -/
def isArmRkm128kC23 (m k : ℕ) : Bool :=
  (m == 4 && k == 4) || (m == 4 && k == 8) || (m == 4 && k == 16) ||
    (m == 4 && k == 32) || (m == 4 && k == 64) || (m == 4 && k == 128)

/-- `1` `Rkm128k` cells. -/
def isArmRkm128kC01 (m k : ℕ) : Bool :=
  (m == 4 && k == 256)

/-- `6` `Rkm128k` cells. -/
def isArmRkm128kC20 (m k : ℕ) : Bool :=
  (m == 8 && k == 4) || (m == 8 && k == 8) || (m == 8 && k == 16) ||
    (m == 8 && k == 32) || (m == 8 && k == 64) || (m == 8 && k == 128)

/-- `1` `Rkm128k` cells. -/
def isArmRkm128kC04 (m k : ℕ) : Bool :=
  (m == 8 && k == 256)

/-- `6` `Rkm128k` cells. -/
def isArmRkm128kC18 (m k : ℕ) : Bool :=
  (m == 16 && k == 4) || (m == 16 && k == 8) || (m == 16 && k == 16) ||
    (m == 16 && k == 32) || (m == 16 && k == 64) || (m == 16 && k == 128)

/-- `1` `Rkm128k` cells. -/
def isArmRkm128kC05 (m k : ℕ) : Bool :=
  (m == 16 && k == 256)

/-- `6` `Rkm128k` cells. -/
def isArmRkm128kC02 (m k : ℕ) : Bool :=
  (m == 32 && k == 4) || (m == 32 && k == 8) || (m == 32 && k == 16) ||
    (m == 32 && k == 32) || (m == 32 && k == 64) || (m == 32 && k == 128)

/-- `1` `Rkm128k` cells. -/
def isArmRkm128kC16 (m k : ℕ) : Bool :=
  (m == 32 && k == 256)

/-- `5` `Rkm128k` cells. -/
def isArmRkm128kC21 (m k : ℕ) : Bool :=
  (m == 64 && k == 8) || (m == 64 && k == 16) || (m == 64 && k == 32) ||
    (m == 64 && k == 64) || (m == 64 && k == 128)

/-- `1` `Rkm128k` cells. -/
def isArmRkm128kC22 (m k : ℕ) : Bool :=
  (m == 64 && k == 256)

/-- `1` `M1K64` cells. -/
def isArmPulseM1K64 (m k : ℕ) : Bool :=
  (m == 1 && k == 64)

/-- `1` `Rkm128k` cells. -/
def isArmRkm128kC14 (m k : ℕ) : Bool :=
  (m == 256 && k == 512)

/-- `1` `Rkm128k` cells. -/
def isArmRkm128kC12 (m k : ℕ) : Bool :=
  (m == 32 && k == 512)

/-- `1` `Rkm128k` cells. -/
def isArmRkm128kC19 (m k : ℕ) : Bool :=
  (m == 4 && k == 512)

/-- `1` `Rkm128k` cells. -/
def isArmRkm128kC03 (m k : ℕ) : Bool :=
  (m == 16 && k == 512)

/-- `5` `Rkm128k` cells. -/
def isArmRkm128kC10 (m k : ℕ) : Bool :=
  (m == 256 && k == 8) || (m == 256 && k == 16) || (m == 256 && k == 32) ||
    (m == 256 && k == 64) || (m == 256 && k == 128)

/-- Certified `k = 1` relative cost via Mathlib's `Real.pi_gt_d20`. -/
def boundaryRelCost : ℚ≥0 :=
  514159265358979323847 / 628318530717958647692

/-- Exact coprime `121`-cell relative cost table on `groverGrid × groverGrid`. -/
def gridRelCost (m k : ℕ) : ℚ≥0 :=
  if m == 1 then
    if k == 1 then boundaryRelCost
    else if k == 2 then NNRat.divNat 379666241046199 500000000000000
    else if k == 4 then NNRat.divNat 1798014765956261 2500000000000000
    else if k == 8 then NNRat.divNat 173143829619399 250000000000000
    else if k == 16 then NNRat.divNat 6751273712926893 10000000000000000
    else if k == 32 then NNRat.divNat 1328876209066213 2000000000000000
    else if k == 64 then NNRat.divNat 1641721138905847 2500000000000000
    else if k == 128 then NNRat.divNat 6564251612151231 10000000000000000
    else if k == 256 then NNRat.divNat 409036472074287 625000000000000
    else if k == 512 then NNRat.divNat 261102099301103 400000000000000
    else if k == 1024 then NNRat.divNat 3256773370679057 5000000000000000
    else 1
  else if m == 2 then
    if k == 1 then boundaryRelCost
    else if k == 2 then NNRat.divNat 6667024075121291 10000000000000000
    else if k == 4 then NNRat.divNat 635653074817 1000000000000
    else if k == 8 then NNRat.divNat 29359515018607 50000000000000
    else if k == 16 then NNRat.divNat 138280842621027 250000000000000
    else if k == 32 then NNRat.divNat 524680560022403 1000000000000000
    else if k == 64 then NNRat.divNat 506001440881489 1000000000000000
    else if k == 128 then NNRat.divNat 98552131503687 200000000000000
    else if k == 256 then NNRat.divNat 483770197151367 1000000000000000
    else if k == 512 then NNRat.divNat 484442444873 1000000000000
    else if k == 1024 then NNRat.divNat 480439805247 1000000000000
    else 1
  else if m == 4 then
    if k == 1 then boundaryRelCost
    else if k == 2 then NNRat.divNat 2956868632351389 5000000000000000
    else if k == 4 then NNRat.divNat 98193933431639 200000000000000
    else if k == 8 then NNRat.divNat 219351823974601 500000000000000
    else if k == 16 then NNRat.divNat 100885823733429 250000000000000
    else if k == 32 then NNRat.divNat 189624273570189 500000000000000
    else if k == 64 then NNRat.divNat 72666217410757 200000000000000
    else if k == 128 then NNRat.divNat 352006510827783 1000000000000000
    else if k == 256 then NNRat.divNat 173119777922821 500000000000000
    else if k == 512 then NNRat.divNat 42044243815911 125000000000000
    else if k == 1024 then NNRat.divNat 34091235799 100000000000
    else 1
  else if m == 8 then
    if k == 1 then boundaryRelCost
    else if k == 2 then NNRat.divNat 964677786 1707106781
    else if k == 4 then NNRat.divNat 394478990346047 1000000000000000
    else if k == 8 then NNRat.divNat 165617643496611 500000000000000
    else if k == 16 then NNRat.divNat 295827281048903 1000000000000000
    else if k == 32 then NNRat.divNat 273808992547581 1000000000000000
    else if k == 64 then NNRat.divNat 129786223141919 500000000000000
    else if k == 128 then NNRat.divNat 50073041844323 200000000000000
    else if k == 256 then NNRat.divNat 245114394396743 1000000000000000
    else if k == 512 then NNRat.divNat 123027425577 500000000000
    else if k == 1024 then NNRat.divNat 60563025103 250000000000
    else 1
  else if m == 16 then
    if k == 1 then boundaryRelCost
    else if k == 2 then NNRat.divNat 919063107 1707106781
    else if k == 4 then NNRat.divNat 366972263893023 1000000000000000
    else if k == 8 then NNRat.divNat 131157306716427 500000000000000
    else if k == 16 then NNRat.divNat 55574575590339 250000000000000
    else if k == 32 then NNRat.divNat 39978056717363 200000000000000
    else if k == 64 then NNRat.divNat 93291456077201 500000000000000
    else if k == 128 then NNRat.divNat 89292582836643 500000000000000
    else if k == 256 then NNRat.divNat 34749072739993 200000000000000
    else if k == 512 then NNRat.divNat 85405926376537 500000000000000
    else if k == 1024 then NNRat.divNat 172398243679 1000000000000
    else 1
  else if m == 32 then
    if k == 1 then boundaryRelCost
    else if k == 2 then NNRat.divNat 895540993 1707106781
    else if k == 4 then NNRat.divNat 356512242573879 1000000000000000
    else if k == 8 then NNRat.divNat 240096513766043 1000000000000000
    else if k == 16 then NNRat.divNat 43893601346917 250000000000000
    else if k == 32 then NNRat.divNat 75118094154941 500000000000000
    else if k == 64 then NNRat.divNat 68317558069959 500000000000000
    else if k == 128 then NNRat.divNat 25702048974707 200000000000000
    else if k == 256 then NNRat.divNat 24981916805399 200000000000000
    else if k == 512 then NNRat.divNat 121373469087091 1000000000000000
    else if k == 1024 then NNRat.divNat 122445401453 1000000000000
    else 1
  else if m == 64 then
    if k == 1 then boundaryRelCost
    else if k == 2 then NNRat.divNat 882921566 1707106781
    else if k == 4 then NNRat.divNat 971953019 2784457050
    else if k == 8 then NNRat.divNat 28990925704537 125000000000000
    else if k == 16 then NNRat.divNat 159525410088939 1000000000000000
    else if k == 32 then NNRat.divNat 59353029202209 500000000000000
    else if k == 64 then NNRat.divNat 10235536019277 100000000000000
    else if k == 128 then NNRat.divNat 9384494941081 100000000000000
    else if k == 256 then NNRat.divNat 89475475950707 1000000000000000
    else if k == 512 then NNRat.divNat 88634562849 1000000000000
    else if k == 1024 then NNRat.divNat 43561692353 500000000000
    else 1
  else if m == 128 then
    if k == 1 then boundaryRelCost
    else if k == 2 then NNRat.divNat 875993251 1707106781
    else if k == 4 then NNRat.divNat 156832149 464076175
    else if k == 8 then NNRat.divNat 11419214186997 50000000000000
    else if k == 16 then NNRat.divNat 38426409743409 250000000000000
    else if k == 32 then NNRat.divNat 107566698366869 1000000000000000
    else if k == 64 then NNRat.divNat 81067657171691 1000000000000000
    else if k == 128 then NNRat.divNat 14113582515393 200000000000000
    else if k == 256 then NNRat.divNat 405547717793 6250000000000
    else if k == 512 then NNRat.divNat 12679764911 200000000000
    else if k == 1024 then NNRat.divNat 31168173827 500000000000
    else 1
  else if m == 256 then
    if k == 1 then boundaryRelCost
    else if k == 2 then NNRat.divNat 872139413 1707106781
    else if k == 4 then NNRat.divNat 462221306 1392228525
    else if k == 8 then NNRat.divNat 56685214054921 250000000000000
    else if k == 16 then NNRat.divNat 6047258346089 40000000000000
    else if k == 32 then NNRat.divNat 51771084026387 500000000000000
    else if k == 64 then NNRat.divNat 73425717276763 1000000000000000
    else if k == 128 then NNRat.divNat 436301823401 7812500000000
    else if k == 256 then NNRat.divNat 48827154462093 1000000000000000
    else if k == 512 then NNRat.divNat 45375054238433 1000000000000000
    else if k == 1024 then NNRat.divNat 22139803841 500000000000
    else 1
  else if m == 512 then
    if k == 1 then boundaryRelCost
    else if k == 2 then NNRat.divNat 869996454 1707106781
    else if k == 4 then NNRat.divNat 183092327 556891410
    else if k == 8 then NNRat.divNat 484469487 2185718399
    else if k == 16 then NNRat.divNat 3750175009181 25000000000000
    else if k == 32 then NNRat.divNat 101792234239951 1000000000000000
    else if k == 64 then NNRat.divNat 70660484805033 1000000000000000
    else if k == 128 then NNRat.divNat 12650158017091 250000000000000
    else if k == 256 then NNRat.divNat 309925658397 8000000000000
    else if k == 512 then NNRat.divNat 17133448611 500000000000
    else if k == 1024 then NNRat.divNat 8067483513 250000000000
    else 1
  else if m == 1024 then
    if k == 1 then boundaryRelCost
    else if k == 2 then NNRat.divNat 868800736 1707106781
    else if k == 4 then NNRat.divNat 303528513 928152350
    else if k == 8 then NNRat.divNat 951881197 4371436798
    else if k == 16 then NNRat.divNat 74721135940909 500000000000000
    else if k == 32 then NNRat.divNat 12621924588223 125000000000000
    else if k == 64 then NNRat.divNat 34727173440933 500000000000000
    else if k == 128 then NNRat.divNat 2434837676117 50000000000000
    else if k == 256 then NNRat.divNat 35121342710887 1000000000000000
    else if k == 512 then NNRat.divNat 6756116497 250000000000
    else if k == 1024 then NNRat.divNat 12103877367 500000000000
    else 1
  else 1

/-- Shared `WeakDicke` register width `m * (n + 1) + k * n`. -/
abbrev masterWDZoomQubits (n m k : ℕ) : ℕ := m * (n + 1) + k * n

/-- Workspace factor for `JohnsonRampKickMux`. -/
def masterRampKickLMax (m k : ℕ) : ℕ :=
  if m == 2 && k == 2 then 2
  else if m == 2 && k == 4 then 3
  else if m == 2 && k == 8 then 6
  else if m == 2 && k == 16 then 12
  else if m == 2 && k == 32 then 30
  else if m == 2 && k == 64 then 58
  else if m == 2 && k == 128 then 112
  else if m == 2 && k == 256 then 224
  else if m == 2 && k == 512 then 448
  else if m == 2 && k == 1024 then 992
  else if m == 4 && k == 2 then 2
  else if m == 4 && k == 4 then 2
  else if m == 4 && k == 8 then 3
  else if m == 4 && k == 16 then 7
  else if m == 4 && k == 32 then 14
  else if m == 4 && k == 64 then 29
  else if m == 4 && k == 128 then 59
  else if m == 4 && k == 256 then 112
  else if m == 4 && k == 512 then 224
  else if m == 4 && k == 1024 then 496
  else if m == 8 && k == 2 then 2
  else if m == 8 && k == 4 then 2
  else if m == 8 && k == 8 then 2
  else if m == 8 && k == 16 then 3
  else if m == 8 && k == 32 then 7
  else if m == 8 && k == 64 then 15
  else if m == 8 && k == 128 then 30
  else if m == 8 && k == 256 then 56
  else if m == 8 && k == 512 then 112
  else if m == 8 && k == 1024 then 248
  else if m == 16 && k == 2 then 2
  else if m == 16 && k == 4 then 2
  else if m == 16 && k == 8 then 2
  else if m == 16 && k == 16 then 2
  else if m == 16 && k == 32 then 4
  else if m == 16 && k == 64 then 7
  else if m == 16 && k == 128 then 15
  else if m == 16 && k == 256 then 28
  else if m == 16 && k == 512 then 56
  else if m == 16 && k == 1024 then 124
  else if m == 32 && k == 2 then 2
  else if m == 32 && k == 4 then 2
  else if m == 32 && k == 8 then 2
  else if m == 32 && k == 16 then 2
  else if m == 32 && k == 32 then 2
  else if m == 32 && k == 64 then 4
  else if m == 32 && k == 128 then 7
  else if m == 32 && k == 256 then 14
  else if m == 32 && k == 512 then 28
  else if m == 32 && k == 1024 then 62
  else if m == 64 && k == 2 then 2
  else if m == 64 && k == 4 then 2
  else if m == 64 && k == 8 then 2
  else if m == 64 && k == 16 then 2
  else if m == 64 && k == 32 then 2
  else if m == 64 && k == 64 then 2
  else if m == 64 && k == 128 then 4
  else if m == 64 && k == 256 then 7
  else if m == 64 && k == 512 then 14
  else if m == 64 && k == 1024 then 31
  else if m == 512 && k == 64 then 2
  else if m == 512 && k == 128 then 2
  else if m == 1024 && k == 64 then 2
  else if m == 1024 && k == 128 then 2
  else 2

/-- Workspace factor for `JohnsonRampKickMuxHi`. -/
def masterRampKickHiLMax (m k : ℕ) : ℕ :=
  if m == 128 && k == 2 then 2
  else if m == 128 && k == 4 then 2
  else if m == 128 && k == 8 then 2
  else if m == 128 && k == 16 then 2
  else if m == 128 && k == 32 then 2
  else if m == 128 && k == 64 then 2
  else if m == 128 && k == 128 then 2
  else if m == 128 && k == 256 then 3
  else if m == 128 && k == 512 then 7
  else if m == 128 && k == 1024 then 16
  else if m == 256 && k == 2 then 2
  else if m == 256 && k == 4 then 2
  else if m == 256 && k == 8 then 2
  else if m == 256 && k == 16 then 2
  else if m == 256 && k == 32 then 2
  else if m == 256 && k == 64 then 2
  else if m == 256 && k == 128 then 2
  else if m == 256 && k == 256 then 2
  else if m == 256 && k == 512 then 4
  else if m == 256 && k == 1024 then 8
  else if m == 512 && k == 2 then 2
  else if m == 512 && k == 4 then 2
  else if m == 512 && k == 8 then 2
  else if m == 512 && k == 16 then 2
  else if m == 512 && k == 32 then 2
  else if m == 512 && k == 64 then 2
  else if m == 512 && k == 128 then 2
  else if m == 512 && k == 256 then 2
  else if m == 512 && k == 512 then 2
  else if m == 512 && k == 1024 then 4
  else if m == 1024 && k == 2 then 2
  else if m == 1024 && k == 4 then 2
  else if m == 1024 && k == 8 then 2
  else if m == 1024 && k == 16 then 2
  else if m == 1024 && k == 32 then 2
  else if m == 1024 && k == 64 then 2
  else if m == 1024 && k == 128 then 2
  else if m == 1024 && k == 256 then 2
  else if m == 1024 && k == 512 then 2
  else if m == 1024 && k == 1024 then 2
  else 1

/-- Workspace factor for `Rkm128k`. -/
def mRkm128kC13LMax (m k : ℕ) : ℕ :=
  if m == 1024 && k == 256 then 2
  else 1

/-- Workspace factor for `Rkm128k`. -/
def mRkm128kC08LMax (m k : ℕ) : ℕ :=
  if m == 128 && k == 8 then 2
  else if m == 128 && k == 16 then 2
  else if m == 128 && k == 32 then 2
  else if m == 128 && k == 64 then 2
  else if m == 128 && k == 128 then 2
  else 1

/-- Workspace factor for `Rkm128k`. -/
def mRkm128kC06LMax (m k : ℕ) : ℕ :=
  if m == 128 && k == 256 then 5
  else 1

/-- Workspace factor for `Rkm128k`. -/
def mRkm128kC15LMax (m k : ℕ) : ℕ :=
  if m == 256 && k == 256 then 2
  else 1

/-- Workspace factor for `Rkm128k`. -/
def mRkm128kC09LMax (m k : ℕ) : ℕ :=
  if m == 512 && k == 256 then 2
  else 1

/-- Workspace factor for `Rkm128k`. -/
def mRkm128kC17LMax (m k : ℕ) : ℕ :=
  if m == 512 && k == 16 then 2
  else if m == 512 && k == 32 then 2
  else if m == 512 && k == 64 then 2
  else if m == 512 && k == 128 then 2
  else if m == 1024 && k == 16 then 2
  else if m == 1024 && k == 32 then 2
  else if m == 1024 && k == 64 then 2
  else if m == 1024 && k == 128 then 2
  else 1

/-- Workspace factor for `Rkm128k`. -/
def mRkm128kC07LMax (m k : ℕ) : ℕ :=
  if m == 2 && k == 8 then 7
  else if m == 2 && k == 16 then 15
  else if m == 2 && k == 32 then 31
  else if m == 2 && k == 64 then 62
  else if m == 2 && k == 128 then 124
  else 1

/-- Workspace factor for `Rkm128k`. -/
def mRkm128kC11LMax (m k : ℕ) : ℕ :=
  if m == 2 && k == 256 then 250
  else 1

/-- Workspace factor for `Rkm128k`. -/
def mRkm128kC23LMax (m k : ℕ) : ℕ :=
  if m == 4 && k == 4 then 2
  else if m == 4 && k == 8 then 4
  else if m == 4 && k == 16 then 8
  else if m == 4 && k == 32 then 16
  else if m == 4 && k == 64 then 31
  else if m == 4 && k == 128 then 62
  else 1

/-- Workspace factor for `Rkm128k`. -/
def mRkm128kC01LMax (m k : ℕ) : ℕ :=
  if m == 4 && k == 256 then 120
  else 1

/-- Workspace factor for `Rkm128k`. -/
def mRkm128kC20LMax (m k : ℕ) : ℕ :=
  if m == 8 && k == 4 then 2
  else if m == 8 && k == 8 then 2
  else if m == 8 && k == 16 then 4
  else if m == 8 && k == 32 then 8
  else if m == 8 && k == 64 then 16
  else if m == 8 && k == 128 then 32
  else 1

/-- Workspace factor for `Rkm128k`. -/
def mRkm128kC04LMax (m k : ℕ) : ℕ :=
  if m == 8 && k == 256 then 63
  else 1

/-- Workspace factor for `Rkm128k`. -/
def mRkm128kC18LMax (m k : ℕ) : ℕ :=
  if m == 16 && k == 4 then 2
  else if m == 16 && k == 8 then 2
  else if m == 16 && k == 16 then 2
  else if m == 16 && k == 32 then 4
  else if m == 16 && k == 64 then 8
  else if m == 16 && k == 128 then 16
  else 1

/-- Workspace factor for `Rkm128k`. -/
def mRkm128kC05LMax (m k : ℕ) : ℕ :=
  if m == 16 && k == 256 then 32
  else 1

/-- Workspace factor for `Rkm128k`. -/
def mRkm128kC02LMax (m k : ℕ) : ℕ :=
  if m == 32 && k == 4 then 2
  else if m == 32 && k == 8 then 2
  else if m == 32 && k == 16 then 2
  else if m == 32 && k == 32 then 2
  else if m == 32 && k == 64 then 4
  else if m == 32 && k == 128 then 8
  else 1

/-- Workspace factor for `Rkm128k`. -/
def mRkm128kC16LMax (m k : ℕ) : ℕ :=
  if m == 32 && k == 256 then 14
  else 1

/-- Workspace factor for `Rkm128k`. -/
def mRkm128kC21LMax (m k : ℕ) : ℕ :=
  if m == 64 && k == 8 then 2
  else if m == 64 && k == 16 then 2
  else if m == 64 && k == 32 then 2
  else if m == 64 && k == 64 then 2
  else if m == 64 && k == 128 then 4
  else 1

/-- Workspace factor for `Rkm128k`. -/
def mRkm128kC22LMax (m k : ℕ) : ℕ :=
  if m == 64 && k == 256 then 8
  else 1

/-- Workspace factor for `Rkm128k`. -/
def mRkm128kC14LMax (m k : ℕ) : ℕ :=
  if m == 256 && k == 512 then 4
  else 1

/-- Workspace factor for `Rkm128k`. -/
def mRkm128kC12LMax (m k : ℕ) : ℕ :=
  if m == 32 && k == 512 then 32
  else 1

/-- Workspace factor for `Rkm128k`. -/
def mRkm128kC19LMax (m k : ℕ) : ℕ :=
  if m == 4 && k == 512 then 248
  else 1

/-- Workspace factor for `Rkm128k`. -/
def mRkm128kC03LMax (m k : ℕ) : ℕ :=
  if m == 16 && k == 512 then 62
  else 1

/-- Workspace factor for `Rkm128k`. -/
def mRkm128kC10LMax (m k : ℕ) : ℕ :=
  if m == 256 && k == 8 then 2
  else if m == 256 && k == 16 then 2
  else if m == 256 && k == 32 then 2
  else if m == 256 && k == 64 then 2
  else if m == 256 && k == 128 then 2
  else if m == 256 && k == 256 then 2
  else 1

/-- Total qubit count across all `121` cells. -/
def gridQubits (n m k : ℕ) : ℕ :=
  if isArmK1Boundary m k then
    (n + 1) * m + n * k + 1
  else if isArmWarmJP01M2 m k then
    (n + 1) * m + n * k + 1
  else if isArmLongTailM1K2Only m k then
    (n + 1) * m + n * k + 1
  else if isArmGroverM1Pulse m k then
    (n + 1) * m + n * k + 1
  else if isArmGaussianHammingMidPZoom m k then
    masterWDZoomQubits n m k
  else if isArmJohnsonP01K2 m k then
    masterWDZoomQubits n m k
  else if isArmJohnsonRampKickMux m k then
    (masterRampKickLMax m k * m) * (n + 1) + k * n
  else if isArmJohnsonRampKickMuxHi m k then
    (masterRampKickHiLMax m k * m) * (n + 1) + k * n
  else if isArmSchurWeylM1K32Only m k then
    (n + 1) * m + n * k + 1
  else if isArmGaussianHammingZoomK2GH96 m k then
    masterWDZoomQubits n m k
  else if isArmMpzGHMidP m k then
    masterWDZoomQubits n m k
  else if isArmRkm128kC13 m k then
    (mRkm128kC13LMax m k * m) * (n + 1) + k * n
  else if isArmRkm128kC08 m k then
    (mRkm128kC08LMax m k * m) * (n + 1) + k * n
  else if isArmRkm128kC06 m k then
    (mRkm128kC06LMax m k * m) * (n + 1) + k * n
  else if isArmRkm128kC15 m k then
    (mRkm128kC15LMax m k * m) * (n + 1) + k * n
  else if isArmRkm128kC09 m k then
    (mRkm128kC09LMax m k * m) * (n + 1) + k * n
  else if isArmRkm128kC17 m k then
    (mRkm128kC17LMax m k * m) * (n + 1) + k * n
  else if isArmRkm128kC07 m k then
    (mRkm128kC07LMax m k * m) * (n + 1) + k * n
  else if isArmRkm128kC11 m k then
    (mRkm128kC11LMax m k * m) * (n + 1) + k * n
  else if isArmRkm128kC23 m k then
    (mRkm128kC23LMax m k * m) * (n + 1) + k * n
  else if isArmRkm128kC01 m k then
    (mRkm128kC01LMax m k * m) * (n + 1) + k * n
  else if isArmRkm128kC20 m k then
    (mRkm128kC20LMax m k * m) * (n + 1) + k * n
  else if isArmRkm128kC04 m k then
    (mRkm128kC04LMax m k * m) * (n + 1) + k * n
  else if isArmRkm128kC18 m k then
    (mRkm128kC18LMax m k * m) * (n + 1) + k * n
  else if isArmRkm128kC05 m k then
    (mRkm128kC05LMax m k * m) * (n + 1) + k * n
  else if isArmRkm128kC02 m k then
    (mRkm128kC02LMax m k * m) * (n + 1) + k * n
  else if isArmRkm128kC16 m k then
    (mRkm128kC16LMax m k * m) * (n + 1) + k * n
  else if isArmRkm128kC21 m k then
    (mRkm128kC21LMax m k * m) * (n + 1) + k * n
  else if isArmRkm128kC22 m k then
    (mRkm128kC22LMax m k * m) * (n + 1) + k * n
  else if isArmPulseM1K64 m k then
    (n + 1) * m + n * k + 1
  else if isArmRkm128kC14 m k then
    (mRkm128kC14LMax m k * m) * (n + 1) + k * n
  else if isArmRkm128kC12 m k then
    (mRkm128kC12LMax m k * m) * (n + 1) + k * n
  else if isArmRkm128kC19 m k then
    (mRkm128kC19LMax m k * m) * (n + 1) + k * n
  else if isArmRkm128kC03 m k then
    (mRkm128kC03LMax m k * m) * (n + 1) + k * n
  else if isArmRkm128kC10 m k then
    (mRkm128kC10LMax m k * m) * (n + 1) + k * n
  else
    (n + 1) * m + n * k + 1

end QuantumComputation.Specs.GroverFindAll
end

section
namespace QuantumComputation.Specs.GroverFindAll
open Rk128kHiM1024F256KrCert
  Rk128kHiM128K128KrCert
  Rk128kHiM128K256KrCert
  Rk128kHiM256CoCert
  Rk128kHiM256K256KrCert
  Rk128kHiM256K512KrCert
  Rk128kHiM512F256KrCert
  Rk128kHiM512M1024K128KrCert
  Rk128kLowM2K128KrCert
  Rk128kLowM2K256KrCert
  Rk128kLowM4K128KrCert
  Rk128kLowM4K256KrCert
  Rk128kLowM4K512L248KrCert
  Rk128kLowM8K128KrCert
  Rk128kLowM8K256KrCert
  Rk128kMidM16K128KrCert
  Rk128kMidM16K256KrCert
  Rk128kMidM16K512KrCert
  Rk128kMidM32K128KrCert
  Rk128kMidM32K512KrCert
  Rk128kMidM32L64HiCert
  Rk128kMidM64K128KrCert
  Rk128kMidM64K256KrCert GroverM1PulseK64Cert
open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open QuantumComputation.Specs

theorem grid_pos_and_covered {m k : ℕ} (hmk : isGridCell m k = true) :
    1 ≤ m ∧ 1 ≤ k ∧
      (isArmK1Boundary m k || isArmWarmJP01M2 m k || isArmLongTailM1K2Only m k ||
        isArmGroverM1Pulse m k || isArmGaussianHammingMidPZoom m k ||
        isArmJohnsonP01K2 m k || isArmJohnsonRampKickMux m k ||
        isArmJohnsonRampKickMuxHi m k || isArmSchurWeylM1K32Only m k ||
        isArmGaussianHammingZoomK2GH96 m k || isArmMpzGHMidP m k ||
        isArmRkm128kC13 m k || isArmRkm128kC08 m k ||
        isArmRkm128kC06 m k || isArmRkm128kC15 m k ||
        isArmRkm128kC09 m k || isArmRkm128kC17 m k ||
        isArmRkm128kC07 m k || isArmRkm128kC11 m k ||
        isArmRkm128kC23 m k || isArmRkm128kC01 m k ||
        isArmRkm128kC20 m k || isArmRkm128kC04 m k ||
        isArmRkm128kC18 m k || isArmRkm128kC05 m k ||
        isArmRkm128kC02 m k || isArmRkm128kC16 m k ||
        isArmRkm128kC21 m k || isArmRkm128kC22 m k ||
        isArmPulseM1K64 m k || isArmRkm128kC14 m k ||
        isArmRkm128kC12 m k || isArmRkm128kC19 m k ||
        isArmRkm128kC03 m k || isArmRkm128kC10 m k) = true := by
  rw [isGridCell, Bool.and_eq_true] at hmk
  obtain ⟨i, hi, rfl⟩ := (isGridElem_iff m).1 hmk.1
  obtain ⟨j, hj, rfl⟩ := (isGridElem_iff k).1 hmk.2
  revert i j; decide

theorem boundary_rat_eq : boundaryRelCost = relCostBoundary := rfl

theorem arm1_valid {m k : ℕ} (h : isArmK1Boundary m k = true) :
    boundaryProfile.validCell m k = true := by
  unfold isArmK1Boundary at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals decide

theorem arm1_rc {m k : ℕ} (h : isArmK1Boundary m k = true) :
    gridRelCost m k = boundaryProfile.relCost m k := by
  unfold isArmK1Boundary at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals conv_lhs => simp [gridRelCost]
  all_goals dsimp only [boundaryProfile]
  all_goals exact boundary_rat_eq

theorem arm2_valid {m k : ℕ} (h : isArmWarmJP01M2 m k = true) :
    warmJP01Profile.validCell m k = true := by
  unfold isArmWarmJP01M2 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm2_rc {m k : ℕ} (h : isArmWarmJP01M2 m k = true) :
    gridRelCost m k = warmJP01Profile.relCost m k := by
  dsimp only [warmJP01Profile, Warm2.relCostWarmJP01]
  unfold isArmWarmJP01M2 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm3_valid {m k : ℕ} (h : isArmLongTailM1K2Only m k = true) :
    longTailM1K2OnlyProfile.validCell m k = true := by
  unfold isArmLongTailM1K2Only at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm3_rc {m k : ℕ} (h : isArmLongTailM1K2Only m k = true) :
    gridRelCost m k = longTailM1K2OnlyProfile.relCost m k := by
  unfold isArmLongTailM1K2Only at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals conv_lhs => simp [gridRelCost]
  all_goals rw [NNRat.divNat_eq_div]
  all_goals conv_rhs => simp [longTailM1K2OnlyProfile, relCostLongTailM1K2Only]
  all_goals norm_num

theorem arm4_valid {m k : ℕ} (h : isArmGroverM1Pulse m k = true) :
    groverM1PulseProfile.validCell m k = true := by
  unfold isArmGroverM1Pulse at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals decide

theorem arm4_rc {m k : ℕ} (h : isArmGroverM1Pulse m k = true) :
    gridRelCost m k = groverM1PulseProfile.relCost m k := by
  unfold isArmGroverM1Pulse at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals conv_lhs => simp [gridRelCost]
  all_goals rw [NNRat.divNat_eq_div]
  all_goals conv_rhs => simp [groverM1PulseProfile, relCostGroverM1Pulse]
  all_goals norm_num

theorem arm5_valid {m k : ℕ} (h : isArmGaussianHammingMidPZoom m k = true) :
    GaussianHammingMidPZoom.isGaussianHammingMidPZoomCell m k = true := by
  unfold isArmGaussianHammingMidPZoom at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm5_rc {m k : ℕ} (h : isArmGaussianHammingMidPZoom m k = true) :
    gridRelCost m k = GaussianHammingMidPZoom.relCostGaussianHammingMidPZoom m k := by
  unfold isArmGaussianHammingMidPZoom at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm6_valid {m k : ℕ} (h : isArmJohnsonP01K2 m k = true) :
    FindAllJohnsonP01.isJohnsonP01K2Cell m k = true := by
  unfold isArmJohnsonP01K2 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals decide

theorem arm6_rc {m k : ℕ} (h : isArmJohnsonP01K2 m k = true) :
    gridRelCost m k = FindAllJohnsonP01.relCostJohnsonP01K2 m k := by
  unfold isArmJohnsonP01K2 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals decide

theorem arm7_valid {m k : ℕ} (h : isArmJohnsonRampKickMux m k = true) :
    FindAllJohnsonRampKickMux.isJohnsonRampKickMuxCell m k = true := by
  unfold isArmJohnsonRampKickMux at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals decide

theorem arm7_q {n m k : ℕ} (h : isArmJohnsonRampKickMux m k = true) :
    FindAllJohnsonRampKickMux.johnsonRampKickMuxQubits n m k =
      (masterRampKickLMax m k * m) * (n + 1) + k * n := by
  unfold isArmJohnsonRampKickMux at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals rfl

theorem arm7_rc {m k : ℕ} (h : isArmJohnsonRampKickMux m k = true) :
    gridRelCost m k = FindAllJohnsonRampKickMux.relCostJohnsonRampKickMux m k := by
  unfold isArmJohnsonRampKickMux at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals decide

theorem arm8_valid {m k : ℕ} (h : isArmJohnsonRampKickMuxHi m k = true) :
    FindAllJohnsonRampKickMuxHi.isJohnsonRampKickMuxHiCell m k = true := by
  unfold isArmJohnsonRampKickMuxHi at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals decide

theorem arm8_q {n m k : ℕ} (h : isArmJohnsonRampKickMuxHi m k = true) :
    FindAllJohnsonRampKickMuxHi.johnsonRampKickMuxHiQubits n m k =
      (masterRampKickHiLMax m k * m) * (n + 1) + k * n := by
  unfold isArmJohnsonRampKickMuxHi at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals rfl

theorem arm8_rc {m k : ℕ} (h : isArmJohnsonRampKickMuxHi m k = true) :
    gridRelCost m k = FindAllJohnsonRampKickMuxHi.relCostJohnsonRampKickMuxHi m k := by
  unfold isArmJohnsonRampKickMuxHi at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals decide

theorem arm9_valid {m k : ℕ} (h : isArmSchurWeylM1K32Only m k = true) :
    schurWeylL2BallM1K32OnlyProfile.validCell m k = true := by
  unfold isArmSchurWeylM1K32Only at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals decide

theorem arm9_rc {m k : ℕ} (h : isArmSchurWeylM1K32Only m k = true) :
    gridRelCost m k = schurWeylL2BallM1K32OnlyProfile.relCost m k := by
  unfold isArmSchurWeylM1K32Only at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals conv_lhs => simp [gridRelCost]
  all_goals rw [NNRat.divNat_eq_div]
  all_goals conv_rhs => simp [schurWeylL2BallM1K32OnlyProfile,
    relCostSchurWeylL2BallM1K32Only]
  all_goals norm_num

theorem arm10_valid {m k : ℕ} (h : isArmGaussianHammingZoomK2GH96 m k = true) :
    GaussianHammingZoomK2GH96.isGaussianHammingZoomK2GH96Cell m k = true := by
  unfold isArmGaussianHammingZoomK2GH96 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals decide

theorem arm10_rc {m k : ℕ} (h : isArmGaussianHammingZoomK2GH96 m k = true) :
    gridRelCost m k = GaussianHammingZoomK2GH96.relCostGaussianHammingZoomK2GH96 m k := by
  unfold isArmGaussianHammingZoomK2GH96 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals decide

theorem arm11_valid {m k : ℕ} (h : isArmMpzGHMidP m k = true) :
    MpzGHMidP.isMpzGHMidPCell m k = true := by
  unfold isArmMpzGHMidP at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  all_goals decide

theorem arm11_rc {m k : ℕ} (h : isArmMpzGHMidP m k = true) :
    gridRelCost m k = MpzGHMidP.relCostMpzGHMidP m k := by
  unfold isArmMpzGHMidP at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  all_goals decide

theorem arm12_valid {m k : ℕ} (h : isArmRkm128kC13 m k = true) :
    isHiTailM1024Full256KrotovCertCell m k = true := by
  unfold isArmRkm128kC13 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm12_q {n m k : ℕ} (h : isArmRkm128kC13 m k = true) :
    hiTailM1024Full256KrotovCertQubits n m k =
      (mRkm128kC13LMax m k * m) * (n + 1) + k * n := by
  unfold isArmRkm128kC13 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals rfl

theorem arm12_rc {m k : ℕ} (h : isArmRkm128kC13 m k = true) :
    gridRelCost m k = relCostHiTailM1024Full256KrotovCert m k := by
  unfold isArmRkm128kC13 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm13_valid {m k : ℕ} (h : isArmRkm128kC08 m k = true) :
    isHiTailM128K128KrotovCertCell m k = true := by
  unfold isArmRkm128kC08 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals decide

theorem arm13_q {n m k : ℕ} (h : isArmRkm128kC08 m k = true) :
    hiTailM128K128KrotovCertQubits n m k =
      (mRkm128kC08LMax m k * m) * (n + 1) + k * n := by
  unfold isArmRkm128kC08 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals rfl

theorem arm13_rc {m k : ℕ} (h : isArmRkm128kC08 m k = true) :
    gridRelCost m k = relCostHiTailM128K128KrotovCert m k := by
  unfold isArmRkm128kC08 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals decide

theorem arm14_valid {m k : ℕ} (h : isArmRkm128kC06 m k = true) :
    isHiTailM128K256KrotovCertCell m k = true := by
  unfold isArmRkm128kC06 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm14_q {n m k : ℕ} (h : isArmRkm128kC06 m k = true) :
    hiTailM128K256KrotovCertQubits n m k =
      (mRkm128kC06LMax m k * m) * (n + 1) + k * n := by
  unfold isArmRkm128kC06 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals rfl

theorem arm14_rc {m k : ℕ} (h : isArmRkm128kC06 m k = true) :
    gridRelCost m k = relCostHiTailM128K256KrotovCert m k := by
  unfold isArmRkm128kC06 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm15_valid {m k : ℕ} (h : isArmRkm128kC15 m k = true) :
    isHiTailM256K256KrotovCertCell m k = true := by
  unfold isArmRkm128kC15 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm15_q {n m k : ℕ} (h : isArmRkm128kC15 m k = true) :
    hiTailM256K256KrotovCertQubits n m k =
      (mRkm128kC15LMax m k * m) * (n + 1) + k * n := by
  unfold isArmRkm128kC15 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals rfl

theorem arm15_rc {m k : ℕ} (h : isArmRkm128kC15 m k = true) :
    gridRelCost m k = relCostHiTailM256K256KrotovCert m k := by
  unfold isArmRkm128kC15 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm16_valid {m k : ℕ} (h : isArmRkm128kC09 m k = true) :
    isHiTailM512Full256KrotovCertCell m k = true := by
  unfold isArmRkm128kC09 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm16_q {n m k : ℕ} (h : isArmRkm128kC09 m k = true) :
    hiTailM512Full256KrotovCertQubits n m k =
      (mRkm128kC09LMax m k * m) * (n + 1) + k * n := by
  unfold isArmRkm128kC09 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals rfl

theorem arm16_rc {m k : ℕ} (h : isArmRkm128kC09 m k = true) :
    gridRelCost m k = relCostHiTailM512Full256KrotovCert m k := by
  unfold isArmRkm128kC09 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm17_valid {m k : ℕ} (h : isArmRkm128kC17 m k = true) :
    isHiTailM512M1024K128KrotovCertCell m k = true := by
  unfold isArmRkm128kC17 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals decide

theorem arm17_q {n m k : ℕ} (h : isArmRkm128kC17 m k = true) :
    hiTailM512M1024K128KrotovCertQubits n m k =
      (mRkm128kC17LMax m k * m) * (n + 1) + k * n := by
  unfold isArmRkm128kC17 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals rfl

theorem arm17_rc {m k : ℕ} (h : isArmRkm128kC17 m k = true) :
    gridRelCost m k = relCostHiTailM512M1024K128KrotovCert m k := by
  unfold isArmRkm128kC17 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals decide

theorem arm18_valid {m k : ℕ} (h : isArmRkm128kC07 m k = true) :
    isLowM2K128KrotovCertCell m k = true := by
  unfold isArmRkm128kC07 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals decide

theorem arm18_q {n m k : ℕ} (h : isArmRkm128kC07 m k = true) :
    lowM2K128KrotovCertQubits n m k =
      (mRkm128kC07LMax m k * m) * (n + 1) + k * n := by
  unfold isArmRkm128kC07 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals rfl

theorem arm18_rc {m k : ℕ} (h : isArmRkm128kC07 m k = true) :
    gridRelCost m k = relCostLowM2K128KrotovCert m k := by
  unfold isArmRkm128kC07 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals decide

theorem arm19_valid {m k : ℕ} (h : isArmRkm128kC11 m k = true) :
    isLowM2K256KrotovCertCell m k = true := by
  unfold isArmRkm128kC11 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm19_q {n m k : ℕ} (h : isArmRkm128kC11 m k = true) :
    lowM2K256KrotovCertQubits n m k =
      (mRkm128kC11LMax m k * m) * (n + 1) + k * n := by
  unfold isArmRkm128kC11 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals rfl

theorem arm19_rc {m k : ℕ} (h : isArmRkm128kC11 m k = true) :
    gridRelCost m k = relCostLowM2K256KrotovCert m k := by
  unfold isArmRkm128kC11 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm20_valid {m k : ℕ} (h : isArmRkm128kC23 m k = true) :
    isLowM4K128KrotovCertCell m k = true := by
  unfold isArmRkm128kC23 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  all_goals decide

theorem arm20_q {n m k : ℕ} (h : isArmRkm128kC23 m k = true) :
    lowM4K128KrotovCertQubits n m k =
      (mRkm128kC23LMax m k * m) * (n + 1) + k * n := by
  unfold isArmRkm128kC23 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  all_goals rfl

theorem arm20_rc {m k : ℕ} (h : isArmRkm128kC23 m k = true) :
    gridRelCost m k = relCostLowM4K128KrotovCert m k := by
  unfold isArmRkm128kC23 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  all_goals decide

theorem arm21_valid {m k : ℕ} (h : isArmRkm128kC01 m k = true) :
    isLowM4K256KrotovCertCell m k = true := by
  unfold isArmRkm128kC01 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm21_q {n m k : ℕ} (h : isArmRkm128kC01 m k = true) :
    lowM4K256KrotovCertQubits n m k =
      (mRkm128kC01LMax m k * m) * (n + 1) + k * n := by
  unfold isArmRkm128kC01 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals rfl

theorem arm21_rc {m k : ℕ} (h : isArmRkm128kC01 m k = true) :
    gridRelCost m k = relCostLowM4K256KrotovCert m k := by
  unfold isArmRkm128kC01 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm22_valid {m k : ℕ} (h : isArmRkm128kC20 m k = true) :
    isLowM8K128KrotovCertCell m k = true := by
  unfold isArmRkm128kC20 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  all_goals decide

theorem arm22_q {n m k : ℕ} (h : isArmRkm128kC20 m k = true) :
    lowM8K128KrotovCertQubits n m k =
      (mRkm128kC20LMax m k * m) * (n + 1) + k * n := by
  unfold isArmRkm128kC20 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  all_goals rfl

theorem arm22_rc {m k : ℕ} (h : isArmRkm128kC20 m k = true) :
    gridRelCost m k = relCostLowM8K128KrotovCert m k := by
  unfold isArmRkm128kC20 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  all_goals decide

theorem arm23_valid {m k : ℕ} (h : isArmRkm128kC04 m k = true) :
    isLowM8K256KrotovCertCell m k = true := by
  unfold isArmRkm128kC04 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm23_q {n m k : ℕ} (h : isArmRkm128kC04 m k = true) :
    lowM8K256KrotovCertQubits n m k =
      (mRkm128kC04LMax m k * m) * (n + 1) + k * n := by
  unfold isArmRkm128kC04 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals rfl

theorem arm23_rc {m k : ℕ} (h : isArmRkm128kC04 m k = true) :
    gridRelCost m k = relCostLowM8K256KrotovCert m k := by
  unfold isArmRkm128kC04 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm24_valid {m k : ℕ} (h : isArmRkm128kC18 m k = true) :
    isMidM16K128KrotovCertCell m k = true := by
  unfold isArmRkm128kC18 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  all_goals decide

theorem arm24_q {n m k : ℕ} (h : isArmRkm128kC18 m k = true) :
    midM16K128KrotovCertQubits n m k =
      (mRkm128kC18LMax m k * m) * (n + 1) + k * n := by
  unfold isArmRkm128kC18 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  all_goals rfl

theorem arm24_rc {m k : ℕ} (h : isArmRkm128kC18 m k = true) :
    gridRelCost m k = relCostMidM16K128KrotovCert m k := by
  unfold isArmRkm128kC18 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  all_goals decide

theorem arm25_valid {m k : ℕ} (h : isArmRkm128kC05 m k = true) :
    isMidM16K256KrotovCertCell m k = true := by
  unfold isArmRkm128kC05 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm25_q {n m k : ℕ} (h : isArmRkm128kC05 m k = true) :
    midM16K256KrotovCertQubits n m k =
      (mRkm128kC05LMax m k * m) * (n + 1) + k * n := by
  unfold isArmRkm128kC05 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals rfl

theorem arm25_rc {m k : ℕ} (h : isArmRkm128kC05 m k = true) :
    gridRelCost m k = relCostMidM16K256KrotovCert m k := by
  unfold isArmRkm128kC05 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm26_valid {m k : ℕ} (h : isArmRkm128kC02 m k = true) :
    isMidM32K128KrotovCertCell m k = true := by
  unfold isArmRkm128kC02 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  all_goals decide

theorem arm26_q {n m k : ℕ} (h : isArmRkm128kC02 m k = true) :
    midM32K128KrotovCertQubits n m k =
      (mRkm128kC02LMax m k * m) * (n + 1) + k * n := by
  unfold isArmRkm128kC02 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  all_goals rfl

theorem arm26_rc {m k : ℕ} (h : isArmRkm128kC02 m k = true) :
    gridRelCost m k = relCostMidM32K128KrotovCert m k := by
  unfold isArmRkm128kC02 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  all_goals decide

theorem arm27_valid {m k : ℕ} (h : isArmRkm128kC16 m k = true) :
    isMidM32L64HiCertCell m k = true := by
  unfold isArmRkm128kC16 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm27_q {n m k : ℕ} (h : isArmRkm128kC16 m k = true) :
    midM32L64HiCertQubits n m k =
      (mRkm128kC16LMax m k * m) * (n + 1) + k * n := by
  unfold isArmRkm128kC16 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals rfl

theorem arm27_rc {m k : ℕ} (h : isArmRkm128kC16 m k = true) :
    gridRelCost m k = relCostMidM32L64HiCert m k := by
  unfold isArmRkm128kC16 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm28_valid {m k : ℕ} (h : isArmRkm128kC21 m k = true) :
    isMidM64K128KrotovCertCell m k = true := by
  unfold isArmRkm128kC21 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals decide

theorem arm28_q {n m k : ℕ} (h : isArmRkm128kC21 m k = true) :
    midM64K128KrotovCertQubits n m k =
      (mRkm128kC21LMax m k * m) * (n + 1) + k * n := by
  unfold isArmRkm128kC21 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals rfl

theorem arm28_rc {m k : ℕ} (h : isArmRkm128kC21 m k = true) :
    gridRelCost m k = relCostMidM64K128KrotovCert m k := by
  unfold isArmRkm128kC21 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals decide

theorem arm29_valid {m k : ℕ} (h : isArmRkm128kC22 m k = true) :
    isMidM64K256KrotovCertCell m k = true := by
  unfold isArmRkm128kC22 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm29_q {n m k : ℕ} (h : isArmRkm128kC22 m k = true) :
    midM64K256KrotovCertQubits n m k =
      (mRkm128kC22LMax m k * m) * (n + 1) + k * n := by
  unfold isArmRkm128kC22 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals rfl

theorem arm29_rc {m k : ℕ} (h : isArmRkm128kC22 m k = true) :
    gridRelCost m k = relCostMidM64K256KrotovCert m k := by
  unfold isArmRkm128kC22 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm30_valid {m k : ℕ} (h : isArmPulseM1K64 m k = true) :
    groverM1PulseK64CertProfile.validCell m k = true := by
  unfold isArmPulseM1K64 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm30_rc {m k : ℕ} (h : isArmPulseM1K64 m k = true) :
    gridRelCost m k = groverM1PulseK64CertProfile.relCost m k := by
  dsimp only [groverM1PulseK64CertProfile, relCostGroverM1PulseK64Cert]
  unfold isArmPulseM1K64 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm31_valid {m k : ℕ} (h : isArmRkm128kC14 m k = true) :
    isHiTailM256K512KrotovCertCell m k = true := by
  unfold isArmRkm128kC14 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm31_q {n m k : ℕ} (h : isArmRkm128kC14 m k = true) :
    hiTailM256K512KrotovCertQubits n m k =
      (mRkm128kC14LMax m k * m) * (n + 1) + k * n := by
  unfold isArmRkm128kC14 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals rfl

theorem arm31_rc {m k : ℕ} (h : isArmRkm128kC14 m k = true) :
    gridRelCost m k = relCostHiTailM256K512KrotovCert m k := by
  unfold isArmRkm128kC14 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm32_valid {m k : ℕ} (h : isArmRkm128kC12 m k = true) :
    isMidM32K512KrotovCertCell m k = true := by
  unfold isArmRkm128kC12 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm32_q {n m k : ℕ} (h : isArmRkm128kC12 m k = true) :
    midM32K512KrotovCertQubits n m k =
      (mRkm128kC12LMax m k * m) * (n + 1) + k * n := by
  unfold isArmRkm128kC12 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals rfl

theorem arm32_rc {m k : ℕ} (h : isArmRkm128kC12 m k = true) :
    gridRelCost m k = relCostMidM32K512KrotovCert m k := by
  unfold isArmRkm128kC12 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm33_valid {m k : ℕ} (h : isArmRkm128kC19 m k = true) :
    isLowM4K512L248KrotovCertCell m k = true := by
  unfold isArmRkm128kC19 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm33_q {n m k : ℕ} (h : isArmRkm128kC19 m k = true) :
    lowM4K512L248KrotovCertQubits n m k =
      (mRkm128kC19LMax m k * m) * (n + 1) + k * n := by
  unfold isArmRkm128kC19 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals rfl

theorem arm33_rc {m k : ℕ} (h : isArmRkm128kC19 m k = true) :
    gridRelCost m k = relCostLowM4K512L248KrotovCert m k := by
  unfold isArmRkm128kC19 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm34_valid {m k : ℕ} (h : isArmRkm128kC03 m k = true) :
    isMidM16K512KrotovCertCell m k = true := by
  unfold isArmRkm128kC03 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm34_q {n m k : ℕ} (h : isArmRkm128kC03 m k = true) :
    midM16K512KrotovCertQubits n m k =
      (mRkm128kC03LMax m k * m) * (n + 1) + k * n := by
  unfold isArmRkm128kC03 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals rfl

theorem arm34_rc {m k : ℕ} (h : isArmRkm128kC03 m k = true) :
    gridRelCost m k = relCostMidM16K512KrotovCert m k := by
  unfold isArmRkm128kC03 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩
  all_goals decide

theorem arm35_valid {m k : ℕ} (h : isArmRkm128kC10 m k = true) :
    isHiTailM256CoCertCell m k = true := by
  unfold isArmRkm128kC10 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals decide

theorem arm35_q {n m k : ℕ} (h : isArmRkm128kC10 m k = true) :
    hiTailM256CoCertQubits n m k =
      (mRkm128kC10LMax m k * m) * (n + 1) + k * n := by
  unfold isArmRkm128kC10 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals rfl

theorem arm35_rc {m k : ℕ} (h : isArmRkm128kC10 m k = true) :
    gridRelCost m k = relCostHiTailM256CoCert m k := by
  unfold isArmRkm128kC10 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals decide

end QuantumComputation.Specs.GroverFindAll
end

public section
namespace QuantumComputation.Specs.GroverFindAll
open Rk128kHiM1024F256KrCert
  Rk128kHiM128K128KrCert
  Rk128kHiM128K256KrCert
  Rk128kHiM256CoCert
  Rk128kHiM256K256KrCert
  Rk128kHiM256K512KrCert
  Rk128kHiM512F256KrCert
  Rk128kHiM512M1024K128KrCert
  Rk128kLowM2K128KrCert
  Rk128kLowM2K256KrCert
  Rk128kLowM4K128KrCert
  Rk128kLowM4K256KrCert
  Rk128kLowM4K512L248KrCert
  Rk128kLowM8K128KrCert
  Rk128kLowM8K256KrCert
  Rk128kMidM16K128KrCert
  Rk128kMidM16K256KrCert
  Rk128kMidM16K512KrCert
  Rk128kMidM32K128KrCert
  Rk128kMidM32K512KrCert
  Rk128kMidM32L64HiCert
  Rk128kMidM64K128KrCert
  Rk128kMidM64K256KrCert GroverM1PulseK64Cert
open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open QuantumComputation.Specs

/-- Cast an `OracleDynamicCircuit` across propositionally equal register/slot widths. -/
def masterCastCircuit {Var : Type} {n Q₁ Q₂ m₁ m₂ : ℕ} (hQ : Q₁ = Q₂) (hm : m₁ = m₂)
    (c : OracleDynamicCircuit (Unitary (2 ^ Q₁)) Var Q₁ ((n + 1) * m₁)) :
    OracleDynamicCircuit (Unitary (2 ^ Q₂)) Var Q₂ ((n + 1) * m₂) := hQ ▸ hm ▸ c

/-- Unified `121`-cell `OracleDynamicCircuit` router across active specialist arms. -/
noncomputable def findAllGridCircuit {Var : Type} [DecidableEq Var]
    (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ gridQubits n m k)) Var
      (gridQubits n m k) ((n + 1) * m) :=
  if h1 : isArmK1Boundary m k = true then
    masterCastCircuit (by
      simp only [gridQubits, h1, ↓reduceIte]
      rfl) rfl
      (findAllBoundaryCircuit res n m k)
  else if h2 : isArmWarmJP01M2 m k = true then
    masterCastCircuit (by
      simp only [gridQubits, h1, h2, Bool.false_eq_true, ↓reduceIte]
      rfl) rfl
      (Warm2.findAllWarmJP01M2Circuit res n m k)
  else if h3 : isArmLongTailM1K2Only m k = true then
    masterCastCircuit (by
      simp only [gridQubits, h1, h2, h3, Bool.false_eq_true, ↓reduceIte]
      rfl) rfl
      (longTailM1K2OnlyCircuit res n m k)
  else if h4 : isArmGroverM1Pulse m k = true then
    masterCastCircuit (by
      simp only [gridQubits, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte]
      rfl) rfl
      (groverM1PulseCircuit res n m k)
  else if h5 : isArmGaussianHammingMidPZoom m k = true then
    masterCastCircuit (by
      simp only [gridQubits, h1, h2, h3, h4, h5, Bool.false_eq_true,
        ↓reduceIte]) rfl
      (GaussianHammingMidPZoom.findAllGaussianHammingMidPZoomCircuit res n m k)
  else if h6 : isArmJohnsonP01K2 m k = true then
    masterCastCircuit (by
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, Bool.false_eq_true,
        ↓reduceIte]) rfl
      (FindAllJohnsonP01.findAllJohnsonP01K2Circuit res n m k)
  else if h7 : isArmJohnsonRampKickMux m k = true then
    masterCastCircuit (by
      rw [arm7_q h7]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, Bool.false_eq_true,
        ↓reduceIte]) rfl
      (FindAllJohnsonRampKickMux.findAllJohnsonRampKickMuxCircuit res n m k)
  else if h8 : isArmJohnsonRampKickMuxHi m k = true then
    masterCastCircuit (by
      rw [arm8_q h8]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8,
        Bool.false_eq_true, ↓reduceIte]) rfl
      (FindAllJohnsonRampKickMuxHi.findAllJohnsonRampKickMuxHiCircuit res n m k)
  else if h9 : isArmSchurWeylM1K32Only m k = true then
    masterCastCircuit (by
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9,
        Bool.false_eq_true, ↓reduceIte]
      rfl) rfl
      (schurWeylL2BallM1K32OnlyCircuit res n m k)
  else if h10 : isArmGaussianHammingZoomK2GH96 m k = true then
    masterCastCircuit (by
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
        Bool.false_eq_true, ↓reduceIte]) rfl
      (GaussianHammingZoomK2GH96.findAllGaussianHammingZoomK2GH96Circuit res n m k)
  else if h11 : isArmMpzGHMidP m k = true then
    masterCastCircuit (by
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        Bool.false_eq_true, ↓reduceIte]) rfl
      (MpzGHMidP.findAllMpzGHMidPCircuit res n m k)
  else if h12 : isArmRkm128kC13 m k = true then
    masterCastCircuit (by
      rw [arm12_q h12]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, Bool.false_eq_true, ↓reduceIte]) rfl
      (findAllJohnsonRampKick128kHiTailM1024Full256KrotovCertCircuit res n m k)
  else if h13 : isArmRkm128kC08 m k = true then
    masterCastCircuit (by
      rw [arm13_q h13]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, Bool.false_eq_true, ↓reduceIte]) rfl
      (findAllJohnsonRampKick128kHiTailM128K128KrotovCertCircuit res n m k)
  else if h14 : isArmRkm128kC06 m k = true then
    masterCastCircuit (by
      rw [arm14_q h14]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, Bool.false_eq_true, ↓reduceIte]) rfl
      (findAllJohnsonRampKick128kHiTailM128K256KrotovCertCircuit res n m k)
  else if h15 : isArmRkm128kC15 m k = true then
    masterCastCircuit (by
      rw [arm15_q h15]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, Bool.false_eq_true, ↓reduceIte]) rfl
      (findAllJohnsonRampKick128kHiTailM256K256KrotovCertCircuit res n m k)
  else if h16 : isArmRkm128kC09 m k = true then
    masterCastCircuit (by
      rw [arm16_q h16]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, Bool.false_eq_true, ↓reduceIte]) rfl
      (findAllJohnsonRampKick128kHiTailM512Full256KrotovCertCircuit res n m k)
  else if h17 : isArmRkm128kC17 m k = true then
    masterCastCircuit (by
      rw [arm17_q h17]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, Bool.false_eq_true, ↓reduceIte]) rfl
      (findAllJohnsonRampKick128kHiTailM512M1024K128KrotovCertCircuit res n m k)
  else if h18 : isArmRkm128kC07 m k = true then
    masterCastCircuit (by
      rw [arm18_q h18]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, Bool.false_eq_true, ↓reduceIte]) rfl
      (findAllJohnsonRampKick128kLowM2K128KrotovCertCircuit res n m k)
  else if h19 : isArmRkm128kC11 m k = true then
    masterCastCircuit (by
      rw [arm19_q h19]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, Bool.false_eq_true, ↓reduceIte]) rfl
      (findAllJohnsonRampKick128kLowM2K256KrotovCertCircuit res n m k)
  else if h20 : isArmRkm128kC23 m k = true then
    masterCastCircuit (by
      rw [arm20_q h20]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, Bool.false_eq_true,
        ↓reduceIte]) rfl
      (findAllJohnsonRampKick128kLowM4K128KrotovCertCircuit res n m k)
  else if h21 : isArmRkm128kC01 m k = true then
    masterCastCircuit (by
      rw [arm21_q h21]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, Bool.false_eq_true,
        ↓reduceIte]) rfl
      (findAllJohnsonRampKick128kLowM4K256KrotovCertCircuit res n m k)
  else if h22 : isArmRkm128kC20 m k = true then
    masterCastCircuit (by
      rw [arm22_q h22]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, Bool.false_eq_true,
        ↓reduceIte]) rfl
      (findAllJohnsonRampKick128kLowM8K128KrotovCertCircuit res n m k)
  else if h23 : isArmRkm128kC04 m k = true then
    masterCastCircuit (by
      rw [arm23_q h23]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23,
        Bool.false_eq_true, ↓reduceIte]) rfl
      (findAllJohnsonRampKick128kLowM8K256KrotovCertCircuit res n m k)
  else if h24 : isArmRkm128kC18 m k = true then
    masterCastCircuit (by
      rw [arm24_q h24]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24,
        Bool.false_eq_true, ↓reduceIte]) rfl
      (findAllJohnsonRampKick128kMidM16K128KrotovCertCircuit res n m k)
  else if h25 : isArmRkm128kC05 m k = true then
    masterCastCircuit (by
      rw [arm25_q h25]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25,
        Bool.false_eq_true, ↓reduceIte]) rfl
      (findAllJohnsonRampKick128kMidM16K256KrotovCertCircuit res n m k)
  else if h26 : isArmRkm128kC02 m k = true then
    masterCastCircuit (by
      rw [arm26_q h26]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26,
        Bool.false_eq_true, ↓reduceIte]) rfl
      (findAllJohnsonRampKick128kMidM32K128KrotovCertCircuit res n m k)
  else if h27 : isArmRkm128kC16 m k = true then
    masterCastCircuit (by
      rw [arm27_q h27]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26,
        h27, Bool.false_eq_true, ↓reduceIte]) rfl
      (findAllJohnsonRampKick128kMidM32L64HiCertCircuit res n m k)
  else if h28 : isArmRkm128kC21 m k = true then
    masterCastCircuit (by
      rw [arm28_q h28]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26,
        h27, h28, Bool.false_eq_true, ↓reduceIte]) rfl
      (findAllJohnsonRampKick128kMidM64K128KrotovCertCircuit res n m k)
  else if h29 : isArmRkm128kC22 m k = true then
    masterCastCircuit (by
      rw [arm29_q h29]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26,
        h27, h28, h29, Bool.false_eq_true, ↓reduceIte]) rfl
      (findAllJohnsonRampKick128kMidM64K256KrotovCertCircuit res n m k)
  else if h30 : isArmPulseM1K64 m k = true then
    masterCastCircuit (by
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26,
        h27, h28, h29, h30, Bool.false_eq_true, ↓reduceIte]
      rfl) rfl
      (groverM1PulseK64CertCircuit res n m k)
  else if h31 : isArmRkm128kC14 m k = true then
    masterCastCircuit (by
      rw [arm31_q h31]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26,
        h27, h28, h29, h30, h31, Bool.false_eq_true, ↓reduceIte]) rfl
      (findAllJohnsonRampKick128kHiTailM256K512KrotovCertCircuit res n m k)
  else if h32 : isArmRkm128kC12 m k = true then
    masterCastCircuit (by
      rw [arm32_q h32]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26,
        h27, h28, h29, h30, h31, h32, Bool.false_eq_true, ↓reduceIte]) rfl
      (findAllJohnsonRampKick128kMidM32K512KrotovCertCircuit res n m k)
  else if h33 : isArmRkm128kC19 m k = true then
    masterCastCircuit (by
      rw [arm33_q h33]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26,
        h27, h28, h29, h30, h31, h32, h33, Bool.false_eq_true, ↓reduceIte]) rfl
      (findAllJohnsonRampKick128kLowM4K512L248KrotovCertCircuit res n m k)
  else if h34 : isArmRkm128kC03 m k = true then
    masterCastCircuit (by
      rw [arm34_q h34]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26,
        h27, h28, h29, h30, h31, h32, h33, h34, Bool.false_eq_true, ↓reduceIte]) rfl
      (findAllJohnsonRampKick128kMidM16K512KrotovCertCircuit res n m k)
  else if h35 : isArmRkm128kC10 m k = true then
    masterCastCircuit (by
      rw [arm35_q h35]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26,
        h27, h28, h29, h30, h31, h32, h33, h34, h35, Bool.false_eq_true,
        ↓reduceIte]) rfl
      (findAllJohnsonRampKick128kHiTailM256CoCertCircuit res n m k)
  else
    .skip

end QuantumComputation.Specs.GroverFindAll
end

section
namespace QuantumComputation.Specs.GroverFindAll
open Rk128kHiM1024F256KrCert
  Rk128kHiM128K128KrCert
  Rk128kHiM128K256KrCert
  Rk128kHiM256CoCert
  Rk128kHiM256K256KrCert
  Rk128kHiM256K512KrCert
  Rk128kHiM512F256KrCert
  Rk128kHiM512M1024K128KrCert
  Rk128kLowM2K128KrCert
  Rk128kLowM2K256KrCert
  Rk128kLowM4K128KrCert
  Rk128kLowM4K256KrCert
  Rk128kLowM4K512L248KrCert
  Rk128kLowM8K128KrCert
  Rk128kLowM8K256KrCert
  Rk128kMidM16K128KrCert
  Rk128kMidM16K256KrCert
  Rk128kMidM16K512KrCert
  Rk128kMidM32K128KrCert
  Rk128kMidM32K512KrCert
  Rk128kMidM32L64HiCert
  Rk128kMidM64K128KrCert
  Rk128kMidM64K256KrCert GroverM1PulseK64Cert
open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open QuantumComputation.Specs

theorem master_triple_cast {Var : Type} [DecidableEq Var]
    {n Q₁ Q₂ m₁ m₂ : ℕ} (hQ : Q₁ = Q₂) (hm : m₁ = m₂)
    (c : OracleDynamicCircuit (Unitary (2 ^ Q₁)) Var Q₁ ((n + 1) * m₁))
    (S : Finset (Fin (2 ^ n))) (P : Store Var → Prop)
    (h : ⦃ (⊤ : CQAssertion (Store Var) (2 ^ Q₁)) ⦄
      (QProg.qSet ;; c.compile QProg.qAssign (parallelMarkingOracle m₁ S))
      ⦃ liftPureProp P ⦄) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ Q₂)) ⦄
      (QProg.qSet ;; (masterCastCircuit hQ hm c).compile QProg.qAssign
        (parallelMarkingOracle m₂ S))
      ⦃ liftPureProp P ⦄ := by subst hQ; subst hm; exact h

theorem master_cost_cast {Var : Type} [DecidableEq Var]
    {n m₁ m₂ k Q₁ Q₂ : ℕ} (hQ : Q₁ = Q₂) (hm : m₁ = m₂)
    (c : OracleDynamicCircuit (Unitary (2 ^ Q₁)) Var Q₁ ((n + 1) * m₁)) (cost : ℝ)
    (h : ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
      (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k,
        CostBound (CostModel.ofEmbeddedOracle (parallelMarkingOracle m₁ S))
          (QProg.qSet ;; c.compile QProg.qAssign (parallelMarkingOracle m₁ S)) (q S)) ∧
      (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, (q S : ℝ)) /
          ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤ cost) :
    ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
      (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k,
        CostBound (CostModel.ofEmbeddedOracle (parallelMarkingOracle m₂ S))
          (QProg.qSet ;; (masterCastCircuit hQ hm c).compile QProg.qAssign
            (parallelMarkingOracle m₂ S)) (q S)) ∧
      (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, (q S : ℝ)) /
          ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤ cost := by
  subst hQ; subst hm; exact h

end QuantumComputation.Specs.GroverFindAll
end

public section
namespace QuantumComputation.Specs.GroverFindAll
open Rk128kHiM1024F256KrCert
  Rk128kHiM128K128KrCert
  Rk128kHiM128K256KrCert
  Rk128kHiM256CoCert
  Rk128kHiM256K256KrCert
  Rk128kHiM256K512KrCert
  Rk128kHiM512F256KrCert
  Rk128kHiM512M1024K128KrCert
  Rk128kLowM2K128KrCert
  Rk128kLowM2K256KrCert
  Rk128kLowM4K128KrCert
  Rk128kLowM4K256KrCert
  Rk128kLowM4K512L248KrCert
  Rk128kLowM8K128KrCert
  Rk128kLowM8K256KrCert
  Rk128kMidM16K128KrCert
  Rk128kMidM16K256KrCert
  Rk128kMidM16K512KrCert
  Rk128kMidM32K128KrCert
  Rk128kMidM32K512KrCert
  Rk128kMidM32L64HiCert
  Rk128kMidM64K128KrCert
  Rk128kMidM64K256KrCert GroverM1PulseK64Cert
open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open QuantumComputation.Specs

/-- Exact recovery of `S` with probability `1` across all `121` grid cells. -/
theorem findAllGrid_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} {S : Finset (Fin (2 ^ n))} (hn : 1 ≤ n)
    (hmk : gridCell m k = true) (hkN : k ≤ 2 ^ n)
    (hS : S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ gridQubits n m k)) ⦄
    (QProg.qSet ;; (findAllGridCircuit res n m k).compile QProg.qAssign
      (gridMarkingOracle m S))
    ⦃ fun σ ↦ ⌜gridDecodeTargets n k (σ res) = S⌝ ⦄ := by
  obtain ⟨_, _, hcov⟩ := grid_pos_and_covered hmk
  unfold findAllGridCircuit
  by_cases h1 : isArmK1Boundary m k = true
  · simp only [h1, ↓reduceDIte]
    exact master_triple_cast _ rfl _ _ _
      ((validFamily_boundary res).correctness hn hmk
        (arm1_valid h1) hkN hS)
  by_cases h2 : isArmWarmJP01M2 m k = true
  · simp only [h1, h2, ↓reduceDIte, Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      ((validFamily_warmJP01 res).correctness hn hmk
        (arm2_valid h2) hkN hS)
  by_cases h3 : isArmLongTailM1K2Only m k = true
  · simp only [h1, h2, h3, ↓reduceDIte, Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      ((validFamily_longTailM1K2Only res).correctness hn hmk
        (arm3_valid h3) hkN hS)
  by_cases h4 : isArmGroverM1Pulse m k = true
  · simp only [h1, h2, h3, h4, ↓reduceDIte, Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      ((validFamily_groverM1Pulse res).correctness hn hmk
        (arm4_valid h4) hkN hS)
  by_cases h5 : isArmGaussianHammingMidPZoom m k = true
  · simp only [h1, h2, h3, h4, h5, ↓reduceDIte, Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (GaussianHammingMidPZoom.gaussianHammingMidPZoom_correctness res hn
        (arm5_valid h5) hkN hS)
  by_cases h6 : isArmJohnsonP01K2 m k = true
  · simp only [h1, h2, h3, h4, h5, h6, ↓reduceDIte, Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (FindAllJohnsonP01.johnsonP01K2_correctness res hn
        (arm6_valid h6) hkN hS)
  by_cases h7 : isArmJohnsonRampKickMux m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, ↓reduceDIte, Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (FindAllJohnsonRampKickMux.johnsonRampKickMux_correctness res hn
        (arm7_valid h7) hkN hS)
  by_cases h8 : isArmJohnsonRampKickMuxHi m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, ↓reduceDIte, Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (FindAllJohnsonRampKickMuxHi.johnsonRampKickMuxHi_correctness res hn
        (arm8_valid h8) hkN hS)
  by_cases h9 : isArmSchurWeylM1K32Only m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, ↓reduceDIte, Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      ((validFamily_schurWeylL2BallM1K32Only res).correctness hn hmk
        (arm9_valid h9) hkN hS)
  by_cases h10 : isArmGaussianHammingZoomK2GH96 m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ↓reduceDIte,
      Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (GaussianHammingZoomK2GH96.gaussianHammingZoomK2GH96_correctness res hn
        (arm10_valid h10) hkN hS)
  by_cases h11 : isArmMpzGHMidP m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ↓reduceDIte,
      Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (MpzGHMidP.mpzGHMidP_correctness res hn
        (arm11_valid h11) hkN hS)
  by_cases h12 : isArmRkm128kC13 m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, ↓reduceDIte,
      Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (hiTailM1024Full256KrotovCert_correctness res hn
        (arm12_valid h12) hkN hS)
  by_cases h13 : isArmRkm128kC08 m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, ↓reduceDIte,
      Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (hiTailM128K128KrotovCert_correctness res hn
        (arm13_valid h13) hkN hS)
  by_cases h14 : isArmRkm128kC06 m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
      ↓reduceDIte, Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (hiTailM128K256KrotovCert_correctness res hn
        (arm14_valid h14) hkN hS)
  by_cases h15 : isArmRkm128kC15 m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      ↓reduceDIte, Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (hiTailM256K256KrotovCert_correctness res hn
        (arm15_valid h15) hkN hS)
  by_cases h16 : isArmRkm128kC09 m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, ↓reduceDIte, Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (hiTailM512Full256KrotovCert_correctness res hn
        (arm16_valid h16) hkN hS)
  by_cases h17 : isArmRkm128kC17 m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, ↓reduceDIte, Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (hiTailM512M1024K128KrotovCert_correctness res hn
        (arm17_valid h17) hkN hS)
  by_cases h18 : isArmRkm128kC07 m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, ↓reduceDIte, Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (lowM2K128KrotovCert_correctness res hn
        (arm18_valid h18) hkN hS)
  by_cases h19 : isArmRkm128kC11 m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, ↓reduceDIte, Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (lowM2K256KrotovCert_correctness res hn
        (arm19_valid h19) hkN hS)
  by_cases h20 : isArmRkm128kC23 m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, ↓reduceDIte, Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (lowM4K128KrotovCert_correctness res hn
        (arm20_valid h20) hkN hS)
  by_cases h21 : isArmRkm128kC01 m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, ↓reduceDIte, Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (lowM4K256KrotovCert_correctness res hn
        (arm21_valid h21) hkN hS)
  by_cases h22 : isArmRkm128kC20 m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, ↓reduceDIte, Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (lowM8K128KrotovCert_correctness res hn
        (arm22_valid h22) hkN hS)
  by_cases h23 : isArmRkm128kC04 m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, ↓reduceDIte, Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (lowM8K256KrotovCert_correctness res hn
        (arm23_valid h23) hkN hS)
  by_cases h24 : isArmRkm128kC18 m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, h24, ↓reduceDIte, Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (midM16K128KrotovCert_correctness res hn
        (arm24_valid h24) hkN hS)
  by_cases h25 : isArmRkm128kC05 m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, ↓reduceDIte,
      Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (midM16K256KrotovCert_correctness res hn
        (arm25_valid h25) hkN hS)
  by_cases h26 : isArmRkm128kC02 m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, ↓reduceDIte,
      Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (midM32K128KrotovCert_correctness res hn
        (arm26_valid h26) hkN hS)
  by_cases h27 : isArmRkm128kC16 m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, ↓reduceDIte,
      Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (midM32L64HiCert_correctness res hn
        (arm27_valid h27) hkN hS)
  by_cases h28 : isArmRkm128kC21 m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, ↓reduceDIte,
      Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (midM64K128KrotovCert_correctness res hn
        (arm28_valid h28) hkN hS)
  by_cases h29 : isArmRkm128kC22 m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
      ↓reduceDIte, Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (midM64K256KrotovCert_correctness res hn
        (arm29_valid h29) hkN hS)
  by_cases h30 : isArmPulseM1K64 m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30,
      ↓reduceDIte, Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      ((validFamily_groverM1PulseK64Cert res).correctness hn hmk
        (arm30_valid h30) hkN hS)
  by_cases h31 : isArmRkm128kC14 m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30,
      h31, ↓reduceDIte, Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (hiTailM256K512KrotovCert_correctness res hn
        (arm31_valid h31) hkN hS)
  by_cases h32 : isArmRkm128kC12 m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30,
      h31, h32, ↓reduceDIte, Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (midM32K512KrotovCert_correctness res hn
        (arm32_valid h32) hkN hS)
  by_cases h33 : isArmRkm128kC19 m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30,
      h31, h32, h33, ↓reduceDIte, Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (lowM4K512L248KrotovCert_correctness res hn
        (arm33_valid h33) hkN hS)
  by_cases h34 : isArmRkm128kC03 m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30,
      h31, h32, h33, h34, ↓reduceDIte, Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (midM16K512KrotovCert_correctness res hn
        (arm34_valid h34) hkN hS)
  by_cases h35 : isArmRkm128kC10 m k = true
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30,
      h31, h32, h33, h34, h35, ↓reduceDIte, Bool.false_eq_true]
    exact master_triple_cast _ rfl _ _ _
      (hiTailM256CoCert_correctness res hn
        (arm35_valid h35) hkN hS)
  · exfalso; simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
      h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
      h30, h31, h32, h33, h34, h35] at hcov

/-- Asymptotic uniform-average relative cost bound across all `121` grid cells. -/
theorem findAllGrid_rel_cost {Var : Type} [DecidableEq Var] (res : Var)
    {m k : ℕ} (hmk : gridCell m k = true) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
      ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
        (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k,
          CostBound (CostModel.ofEmbeddedOracle (gridMarkingOracle m S))
            (QProg.qSet ;; (findAllGridCircuit res n m k).compile QProg.qAssign
              (gridMarkingOracle m S)) (q S)) ∧
        (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, (q S : ℝ)) /
            ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤
          ((gridRelCost m k : ℚ≥0) : ℝ) *
            ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) := by
  obtain ⟨_, _, hcov⟩ := grid_pos_and_covered hmk
  by_cases h1 : isArmK1Boundary m k = true
  · refine ⟨boundaryProfile.n0 m k, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      simp only [gridQubits, h1, ↓reduceIte]
      rfl) rfl _ _
      ((validFamily_boundary res).costBound_uniform hmk
        (arm1_valid h1) n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, ↓reduceDIte]
    rwa [arm1_rc h1]
  by_cases h2 : isArmWarmJP01M2 m k = true
  · refine ⟨warmJP01Profile.n0 m k, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      simp only [gridQubits, h1, h2, Bool.false_eq_true, ↓reduceIte]
      rfl) rfl _ _
      ((validFamily_warmJP01 res).costBound_uniform hmk
        (arm2_valid h2) n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, ↓reduceDIte, Bool.false_eq_true]
    rwa [arm2_rc h2]
  by_cases h3 : isArmLongTailM1K2Only m k = true
  · refine ⟨longTailM1K2OnlyProfile.n0 m k, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      simp only [gridQubits, h1, h2, h3, Bool.false_eq_true, ↓reduceIte]
      rfl) rfl _ _
      ((validFamily_longTailM1K2Only res).costBound_uniform hmk
        (arm3_valid h3) n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, ↓reduceDIte, Bool.false_eq_true]
    rwa [arm3_rc h3]
  by_cases h4 : isArmGroverM1Pulse m k = true
  · refine ⟨groverM1PulseProfile.n0 m k, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      simp only [gridQubits, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte]
      rfl) rfl _ _
      ((validFamily_groverM1Pulse res).costBound_uniform hmk
        (arm4_valid h4) n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, ↓reduceDIte, Bool.false_eq_true]
    rwa [arm4_rc h4]
  by_cases h5 : isArmGaussianHammingMidPZoom m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      GaussianHammingMidPZoom.gaussianHammingMidPZoom_relCost (Var := Var) res
        (arm5_valid h5)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      simp only [gridQubits, h1, h2, h3, h4, h5, Bool.false_eq_true,
        ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, ↓reduceDIte, Bool.false_eq_true]
    rwa [arm5_rc h5]
  by_cases h6 : isArmJohnsonP01K2 m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      FindAllJohnsonP01.johnsonP01K2_relCost (Var := Var) res
        (arm6_valid h6)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, Bool.false_eq_true,
        ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, ↓reduceDIte, Bool.false_eq_true]
    rwa [arm6_rc h6]
  by_cases h7 : isArmJohnsonRampKickMux m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      FindAllJohnsonRampKickMux.johnsonRampKickMux_relCost (Var := Var) res
        (arm7_valid h7)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      rw [arm7_q h7]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, Bool.false_eq_true,
        ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, ↓reduceDIte, Bool.false_eq_true]
    rwa [arm7_rc h7]
  by_cases h8 : isArmJohnsonRampKickMuxHi m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      FindAllJohnsonRampKickMuxHi.johnsonRampKickMuxHi_relCost (Var := Var) res
        (arm8_valid h8)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      rw [arm8_q h8]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8,
        Bool.false_eq_true, ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, ↓reduceDIte, Bool.false_eq_true]
    rwa [arm8_rc h8]
  by_cases h9 : isArmSchurWeylM1K32Only m k = true
  · refine ⟨schurWeylL2BallM1K32OnlyProfile.n0 m k, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9,
        Bool.false_eq_true, ↓reduceIte]
      rfl) rfl _ _
      ((validFamily_schurWeylL2BallM1K32Only res).costBound_uniform hmk
        (arm9_valid h9) n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, ↓reduceDIte, Bool.false_eq_true]
    rwa [arm9_rc h9]
  by_cases h10 : isArmGaussianHammingZoomK2GH96 m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      GaussianHammingZoomK2GH96.gaussianHammingZoomK2GH96_relCost (Var := Var) res
        (arm10_valid h10)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
        Bool.false_eq_true, ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ↓reduceDIte,
      Bool.false_eq_true]
    rwa [arm10_rc h10]
  by_cases h11 : isArmMpzGHMidP m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      MpzGHMidP.mpzGHMidP_relCost (Var := Var) res
        (arm11_valid h11)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        Bool.false_eq_true, ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ↓reduceDIte,
      Bool.false_eq_true]
    rwa [arm11_rc h11]
  by_cases h12 : isArmRkm128kC13 m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      hiTailM1024Full256KrotovCert_relCost (Var := Var) res
        (arm12_valid h12)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      rw [arm12_q h12]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, Bool.false_eq_true, ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, ↓reduceDIte,
      Bool.false_eq_true]
    rwa [arm12_rc h12]
  by_cases h13 : isArmRkm128kC08 m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      hiTailM128K128KrotovCert_relCost (Var := Var) res
        (arm13_valid h13)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      rw [arm13_q h13]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, Bool.false_eq_true, ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, ↓reduceDIte,
      Bool.false_eq_true]
    rwa [arm13_rc h13]
  by_cases h14 : isArmRkm128kC06 m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      hiTailM128K256KrotovCert_relCost (Var := Var) res
        (arm14_valid h14)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      rw [arm14_q h14]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, Bool.false_eq_true, ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
      ↓reduceDIte, Bool.false_eq_true]
    rwa [arm14_rc h14]
  by_cases h15 : isArmRkm128kC15 m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      hiTailM256K256KrotovCert_relCost (Var := Var) res
        (arm15_valid h15)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      rw [arm15_q h15]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, Bool.false_eq_true, ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      ↓reduceDIte, Bool.false_eq_true]
    rwa [arm15_rc h15]
  by_cases h16 : isArmRkm128kC09 m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      hiTailM512Full256KrotovCert_relCost (Var := Var) res
        (arm16_valid h16)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      rw [arm16_q h16]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, Bool.false_eq_true, ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, ↓reduceDIte, Bool.false_eq_true]
    rwa [arm16_rc h16]
  by_cases h17 : isArmRkm128kC17 m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      hiTailM512M1024K128KrotovCert_relCost (Var := Var) res
        (arm17_valid h17)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      rw [arm17_q h17]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, Bool.false_eq_true, ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, ↓reduceDIte, Bool.false_eq_true]
    rwa [arm17_rc h17]
  by_cases h18 : isArmRkm128kC07 m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      lowM2K128KrotovCert_relCost (Var := Var) res
        (arm18_valid h18)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      rw [arm18_q h18]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, Bool.false_eq_true, ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, ↓reduceDIte, Bool.false_eq_true]
    rwa [arm18_rc h18]
  by_cases h19 : isArmRkm128kC11 m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      lowM2K256KrotovCert_relCost (Var := Var) res
        (arm19_valid h19)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      rw [arm19_q h19]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, Bool.false_eq_true, ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, ↓reduceDIte, Bool.false_eq_true]
    rwa [arm19_rc h19]
  by_cases h20 : isArmRkm128kC23 m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      lowM4K128KrotovCert_relCost (Var := Var) res
        (arm20_valid h20)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      rw [arm20_q h20]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, Bool.false_eq_true,
        ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, ↓reduceDIte, Bool.false_eq_true]
    rwa [arm20_rc h20]
  by_cases h21 : isArmRkm128kC01 m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      lowM4K256KrotovCert_relCost (Var := Var) res
        (arm21_valid h21)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      rw [arm21_q h21]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, Bool.false_eq_true,
        ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, ↓reduceDIte, Bool.false_eq_true]
    rwa [arm21_rc h21]
  by_cases h22 : isArmRkm128kC20 m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      lowM8K128KrotovCert_relCost (Var := Var) res
        (arm22_valid h22)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      rw [arm22_q h22]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, Bool.false_eq_true,
        ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, ↓reduceDIte, Bool.false_eq_true]
    rwa [arm22_rc h22]
  by_cases h23 : isArmRkm128kC04 m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      lowM8K256KrotovCert_relCost (Var := Var) res
        (arm23_valid h23)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      rw [arm23_q h23]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23,
        Bool.false_eq_true, ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, ↓reduceDIte, Bool.false_eq_true]
    rwa [arm23_rc h23]
  by_cases h24 : isArmRkm128kC18 m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      midM16K128KrotovCert_relCost (Var := Var) res
        (arm24_valid h24)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      rw [arm24_q h24]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24,
        Bool.false_eq_true, ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, h24, ↓reduceDIte, Bool.false_eq_true]
    rwa [arm24_rc h24]
  by_cases h25 : isArmRkm128kC05 m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      midM16K256KrotovCert_relCost (Var := Var) res
        (arm25_valid h25)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      rw [arm25_q h25]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25,
        Bool.false_eq_true, ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, ↓reduceDIte,
      Bool.false_eq_true]
    rwa [arm25_rc h25]
  by_cases h26 : isArmRkm128kC02 m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      midM32K128KrotovCert_relCost (Var := Var) res
        (arm26_valid h26)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      rw [arm26_q h26]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26,
        Bool.false_eq_true, ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, ↓reduceDIte,
      Bool.false_eq_true]
    rwa [arm26_rc h26]
  by_cases h27 : isArmRkm128kC16 m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      midM32L64HiCert_relCost (Var := Var) res
        (arm27_valid h27)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      rw [arm27_q h27]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26,
        h27, Bool.false_eq_true, ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, ↓reduceDIte,
      Bool.false_eq_true]
    rwa [arm27_rc h27]
  by_cases h28 : isArmRkm128kC21 m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      midM64K128KrotovCert_relCost (Var := Var) res
        (arm28_valid h28)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      rw [arm28_q h28]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26,
        h27, h28, Bool.false_eq_true, ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, ↓reduceDIte,
      Bool.false_eq_true]
    rwa [arm28_rc h28]
  by_cases h29 : isArmRkm128kC22 m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      midM64K256KrotovCert_relCost (Var := Var) res
        (arm29_valid h29)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      rw [arm29_q h29]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26,
        h27, h28, h29, Bool.false_eq_true, ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
      ↓reduceDIte, Bool.false_eq_true]
    rwa [arm29_rc h29]
  by_cases h30 : isArmPulseM1K64 m k = true
  · refine ⟨groverM1PulseK64CertProfile.n0 m k, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26,
        h27, h28, h29, h30, Bool.false_eq_true, ↓reduceIte]
      rfl) rfl _ _
      ((validFamily_groverM1PulseK64Cert res).costBound_uniform hmk
        (arm30_valid h30) n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30,
      ↓reduceDIte, Bool.false_eq_true]
    rwa [arm30_rc h30]
  by_cases h31 : isArmRkm128kC14 m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      hiTailM256K512KrotovCert_relCost (Var := Var) res
        (arm31_valid h31)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      rw [arm31_q h31]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26,
        h27, h28, h29, h30, h31, Bool.false_eq_true, ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30,
      h31, ↓reduceDIte, Bool.false_eq_true]
    rwa [arm31_rc h31]
  by_cases h32 : isArmRkm128kC12 m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      midM32K512KrotovCert_relCost (Var := Var) res
        (arm32_valid h32)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      rw [arm32_q h32]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26,
        h27, h28, h29, h30, h31, h32, Bool.false_eq_true, ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30,
      h31, h32, ↓reduceDIte, Bool.false_eq_true]
    rwa [arm32_rc h32]
  by_cases h33 : isArmRkm128kC19 m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      lowM4K512L248KrotovCert_relCost (Var := Var) res
        (arm33_valid h33)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      rw [arm33_q h33]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26,
        h27, h28, h29, h30, h31, h32, h33, Bool.false_eq_true, ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30,
      h31, h32, h33, ↓reduceDIte, Bool.false_eq_true]
    rwa [arm33_rc h33]
  by_cases h34 : isArmRkm128kC03 m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      midM16K512KrotovCert_relCost (Var := Var) res
        (arm34_valid h34)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      rw [arm34_q h34]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26,
        h27, h28, h29, h30, h31, h32, h33, h34, Bool.false_eq_true, ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30,
      h31, h32, h33, h34, ↓reduceDIte, Bool.false_eq_true]
    rwa [arm34_rc h34]
  by_cases h35 : isArmRkm128kC10 m k = true
  · obtain ⟨n₀, hn₀⟩ :=
      hiTailM256CoCert_relCost (Var := Var) res
        (arm35_valid h35)
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩
    have hcost := master_cost_cast (Q₂ := gridQubits n m k) (by
      rw [arm35_q h35]
      simp only [gridQubits, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26,
        h27, h28, h29, h30, h31, h32, h33, h34, h35, Bool.false_eq_true,
        ↓reduceIte]) rfl _ _
      (hn₀ n hn hkN)
    unfold findAllGridCircuit
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30,
      h31, h32, h33, h34, h35, ↓reduceDIte, Bool.false_eq_true]
    rwa [arm35_rc h35]
  · exfalso; simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
      h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
      h30, h31, h32, h33, h34, h35] at hcov

end QuantumComputation.Specs.GroverFindAll
end
