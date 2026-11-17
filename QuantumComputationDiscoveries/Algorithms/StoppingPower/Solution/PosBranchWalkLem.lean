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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Slot5MatScaleCert
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.DynSeqRegComb

@[expose] public section
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section PosSlots24BranchConcrete
local instance (priority := 1000000) instNeZeroTwoPow_PosSlots24BranchConcrete (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-!
# Concrete Zero-`TOFF` Position-Space `SELECT` (`Slot 2 (U_en)` & `Slot 4 (V_ee)`)

Implements the concrete `Var`-polymorphic dynamic circuit `dPosPhaseDyn` and exact
computational-basis diagonal `±1` unitary `uPosPhase` on the `4,034`-wire core register
(`fullSysCoreWires 80 = 3954 + 80 = 4034`):

1. **Zero `.TOFF` and Zero `.Rz` Gates Unconditionally**:
   - `count_dPosPhaseDyn_toff`: `(dPosPhaseDyn ...).count .TOFF = 0`.
   - `count_dPosPhaseDyn_t_le`: `(dPosPhaseDyn ...).count .T ≤ posPhaseTBound m s`, evaluating to
     `89,464` `.T` gates (`22,366` Toffoli-equivalents, `-5,328` `.T` via `swapFetch219Circuit`)
     at `(m := 10, s := 4)` and `117,312` `.T` gates at `(m := 11, s := 3)`.
2. **Exact 1-Pass Real Self-Adjoint `±1` Phase Action (`uPosPhase`)**:
   - Preserves all `4,034` core wires (`rElec`, `rProj`, all `6` control flags `[3948..3954)`, and
     all `80` `rSubPayload` wires `[3954..4034)`) bit-for-bit across all `8` coin states:
     * `coin = 0` (`(0, 0, 0)`, `Slot 2 = U_en`): streams all `218` slots against `d_head / 2` via
       `StreamingBchComparator.streamingSyndromeOracleDyn` (`N = 218, k = 17, m = 16, wMax = 129`)
       and `GF(2^8)*` cubic BCH decoding (`wIsHead = 1`), and evaluates the `47,905`-orbit QROM
       keep-reject comparator (`wIsHead = 0`) at `d_w = 2 * ySlot2_w + b1_w` (supporting both
       `slot2SwappedTo0 = true` and `slot2SwappedTo0 = false`).
     * `coin = 1` (`(0, 0, 1)`, `Slot 4 = V_ee`): evaluates the exact `anchorSubTarget1D` dual shift
       `(y0_w + ((b0_w + 128 - d_head_w) % 128) / 2) % 64` while masking anchor slot `0` cleanly via
       `firstCtrl 0 = wSlot0Core` (`wIsHead = 1`), and routes partner slot `(m % 217) + 1` via a
       pruned `swapFetch219Circuit 18` to evaluate
       `(2 * y0_w + b0_w + 128 - (2 * y1_w + b1_w)) % 128` in the shared `47,905`-orbit QROM
       (`wIsHead = 0`).
     * `coin = 2` (`(0, 1, 0)`, `+I` slack): exact `+1` (`posPhaseBit = false`).
     * `coin = 3` (`(0, 1, 1)`, `-I` slack): exact `-1` (`posPhaseBit = true`).
     * `coins 4..7` (`iSlot2 = 1`, `MomSlots`): exact `+1` (`posPhaseBit = false`).
     * Out-of-bounds `(l ≥ 216, i ≥ 218, m ≥ 217)` or `wSubReject = 1` on `coins 0, 1`: kicks
       `(-1)^{wRejectZero}`, cancelling identically to `0` over uniform `wRejectZero ∈ |+⟩`.
-/

set_option maxRecDepth 65536

public section

namespace PosSlots24BranchConcrete

open Operator QProg Matrix HermitianMat
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation
open OctahedralOrbit Dyadic128CoulombMath
open StreamingBchComparator

/-! ## Section 1: Generic Clean-Workspace & Compute–Phase–Uncompute Bridges -/

section CleanCircuitBridges

variable {Var : Type} {n : ℕ}

@[simp] theorem support_Z_eq (w : Wire n) : (Circuit.Z w).support = {w} := by
  simp [Circuit.Z]

theorem PreservesStoreConst.substToffoliCircuit [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)]
    (v : Var) (anc : Wire n) (c : Circuit n) (hanc : anc ∉ c.support) :
    PreservesStoreConst (DynCircuitExt.substToffoliCircuit v anc c hanc) := by
  induction c with
  | identity => exact PreservesStoreConst.identity
  | gate g r =>
      cases g with
      | toffoli =>
          dsimp only [DynCircuitExt.substToffoliCircuit, DynamicCircuit.jonesToffoli]
          exact PreservesStoreConst.seq (PreservesStoreConst.circuit _)
            (PreservesStoreConst.seq (PreservesStoreConst.circuit _)
              (PreservesStoreConst.andUncompute v (r 0) (r 1) anc _))
      | x | y | z | h | s | t | cnot | swap => exact PreservesStoreConst.circuit _
  | seq c₁ c₂ ih₁ ih₂ =>
      exact PreservesStoreConst.seq (ih₁ (fun h ↦ hanc (Finset.mem_union_left _ h)))
        (ih₂ (fun h ↦ hanc (Finset.mem_union_right _ h)))

end CleanCircuitBridges

/-! ## Section 2: Locked `4034`-Wire Core Layout, Arithmetic Gadgets & Exact `anchorSubTarget1D` -/

/-! ## Section 4: Concrete Phase 1 (`headPhaseDyn`) & Phase 2 (`tailAndSlackDyn`) Circuits -/

end PosSlots24BranchConcrete
end
end PosSlots24BranchConcrete

section BridgeDuhamel
local instance (priority := 1000000) instNeZeroTwoPow_BridgeDuhamel (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-!
# Duhamel Time-Evolution Perturbation & Sector Bridges (`BridgeDuhamel`)

Duhamel spectral-norm perturbation bounds for matrix exponentials and `ApproximatesTimeEvolution`
sector bridges:
1. `norm_exp_sub_exp_le_of_isHermitian`: Duhamel's inequality
   `‖exp(-i t A) - exp(-i t B)‖ ≤ t * ‖A - B‖` for Hermitian `A, B` and `0 ≤ t`.
2. `norm_exp_sub_exp_mul_projector_le`: Subspace-restricted Duhamel perturbation bound when `A` and
   `B` commute with an orthogonal projector `P`.
3. `ApproximatesTimeEvolution.of_perturbation` and `of_perturbation_direct`: Perturbation bridges
   combining simulation error and effective-Hamiltonian sector error.
4. `fin10_time_evol_of_sector_and_sim_general` and `fin10_time_evol_of_gridBlock_and_sim_general`:
   10-segment (`t = j.val + 1 ≤ 10`) Duhamel error budget bridges for both `Heff - E₀ • 1` and
   `Heff - E₀ • gridProjector` block encodings.
-/

public section

namespace SpecsAux

open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt SpecsAux.SpecMirror
open scoped Matrix

namespace BridgeDuhamel

open FullScaleBESector SubmatrixOpNorm

theorem ApproximatesTimeEvolution.mono {k m : ℕ} {H : Operator (2 ^ k)} {t ε₁ ε₂ : ℝ}
    {P : Operator (2 ^ k)} {W : Unitary (2 ^ (k + m))}
    (h : ApproximatesTimeEvolution H t ε₁ P W) (hle : ε₁ ≤ ε₂) : ApproximatesTimeEvolution H t
    ε₂ P W := approximatesTimeEvolution_mono h hle

end BridgeDuhamel

end SpecsAux
end
end BridgeDuhamel

section DyadicQft64WalkCircuit220
local instance (priority := 1000000) instNeZeroTwoPow_DyadicQft64WalkCircuit220 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-!
# Parametric `mWork ≥ 206` & Concrete `mWork = 220` Core `QFT_64` Butterfly
(`DyadicQft64WalkCircuit220`)

Re-batches the `c_in[0]` + apex-`T` `654`-axis Karatsuba Hadamard butterfly stages
(`stageD5..stageD2`) over `DyadicQft64WalkCircuit288`'s polymorphic `ApexButterflyEngine` so the
core `QFT_64` bundle fits in any clean workspace `mWork ≥ 206` (concretely `mWork = 220` on
`nCanon4154 = 3934 + 220 = 4154`) at **zero `T`-gate penalty** (`23,439 T` one-way =
`46,878 T/walk`, `+0 T/walk` vs `mWork = 288`):

- **Zero-Batch-Overhead Law**: whenever `2 ^ (4 - s) ∣ L`, peeling `c_in[0]` removes `4 - s`
  Wallace CSA steps (`-4 * (4 - s)` `T` gates) and `1` final carry (`-1` `T` gate), canceling the
  `4 * (4 - s) + 1` `T` gates of the `(4 - s)`-bit Gidney apex chain identically.
- **Exact `mWork ≤ 206 ≤ 220` Stage Partitions**:
  - `stageD5CanonStageM` (`s = 0`, `[64, ..., 64, 14]`, peak `197`): **`9,288 T`**,
  - `stageD4CanonStageM` (`s = 1`, `[96, 96, 96, 96, 96, 96, 78]`, peak `205`): **`6,791 T`**,
  - `stageD3CanonStageM` (`s = 2`, `[164, 164, 164, 162]`, peak `206`): **`4,417 T`**,
  - `stageD2CanonStageM` (`s = 3`, `[328, 326]`, peak `165`): **`2,289 T`**,
  - `stageD1CanonStageM` (`ofCanon168 stageD1CanonStage`, peak `168`): **`654 T`**,
  - `stageH654CanonStageM` (`ofCanon168 (stageH654CanonStage kf)`, peak `168`): **`0 T`**,
  totaling **`23,439 T` one-way (`46,878 T` round-trip)** with `uQft654 = coreQftHadamardIdeal654`
  by `rfl` and `count .TOFF = 0`.
-/

public section

namespace DyadicQft64WalkCircuit220

open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt DyadicQft64
open DyadicQft64WalkCircuit
  (bit5Flip654 preDiag654 qft64Ideal654Unitary stageD654 stageH654)
open scoped Matrix BigOperators

section ConfigDyadicQft64WalkCircuit220
set_option maxRecDepth 65536

/-- High-priority `O(1)` `NeZero (2 ^ k)` local instance avoiding unary WHNF reduction of
`2 ^ 3934`. -/
local instance (priority := 1000000)
    instLoc_DyadicQft64WalkCircuit220_1InstNeZeroTwoPowQ (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

/-! ## Section 1: Parametric `(3934 + mWork)`-Wire Canonical Stage Record & `168 → mWork` Lift -/

noncomputable def coreQftHadamardIdeal654 : Unitary (2 ^ (3924 + 3)) := stageH654 0 *
    (stageD654 1 * stageH654 1) * (stageD654 2 * stageH654 2) * (stageD654 3 * stageH654 3) *
    (stageD654 4 * stageH654 4) * (stageD654 5 * stageH654 5)

/-- Exact operator factorization
`qft64Ideal654Unitary = coreQftHadamardIdeal654 * (preDiag654 * bit5Flip654)`. -/
theorem qft64Ideal654Unitary_eq_coreIdeal_mul_preDiag :
    qft64Ideal654Unitary = coreQftHadamardIdeal654 * (preDiag654 * bit5Flip654) := by
  have hdef : qft64Ideal654Unitary =
      (coreQftHadamardIdeal654 * preDiag654) * bit5Flip654 := rfl
  rw [hdef, _root_.mul_assoc]

set_option maxRecDepth 2000

end ConfigDyadicQft64WalkCircuit220

end DyadicQft64WalkCircuit220
end
end DyadicQft64WalkCircuit220

section MomSlots35Coulomb
local instance (priority := 1000000) instNeZeroTwoPow_MomSlots35Coulomb (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-!
# Shared Reversible Classical, `CH`-Gate, Clean-Block, and Unsigned Arithmetic Primitives
(`MomSlots35Coulomb`)

Shared zero-`.TOFF` clean-workspace circuit and arithmetic primitive library supporting
the concrete momentum Coulomb channel modules (`MomSlots35Slot3ProjNuclear` and
`MomSlots35Slot5ElecProj`):
- **Section 1**: `RevProg` reversible classical basis evaluation and composition, `2`-`T`
  single-ancilla Hadamard-test `chGate` (`W⁻¹ Z W = H`), and `CleanBlockExtraction`
  (`cleanBlockUnitary`, `realizesCleanBlock_fwd_and_inv`) extracting forward and inverse
  `Unitary (2 ^ kAct)` witnesses automatically from clean-ancilla preservation.
- **Section 2**: Exact unsigned multi-bit reversible arithmetic (`regValBits`, `xorConstProg`,
  `incByCtrlProg`, `addRegModProg`, `notCopyProg`, `ltRegProg`, `mulRegProg`) with proven wire
  bounds and clean workspace restoration.
-/

public section

namespace MomSlots35Coulomb

open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real
open SpecsAux.SpecMirror SpecsAux.FullScaleBESector
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.PhaseGradCatalystCore
open MeasureBranchHadamardSem
open StreamingBchComparator
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-! ## Section 1: Compositional `RevProg K`, Exact `CH`, & Clean-Subspace Lowering -/

section ClassicalAndGatePrimitives

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_eq_or x with rfl | rfl <;> rfl

namespace RevProg

/-- Lower a reversible classical program to a pure quantum `Circuit K`. -/
def toCircuit {K : ℕ} : RevProg K → Circuit K
  | .nil => .identity
  | .x t => Circuit.X t
  | .cnot c t h => Circuit.CNOT c t h
  | .toff c₁ c₂ t h₁₂ h₁t h₂t => Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t
  | .seq p₁ p₂ => p₁.toCircuit.seq p₂.toCircuit

/-- Syntactic inverse of a reversible classical program. -/
def inv {K : ℕ} : RevProg K → RevProg K
  | .nil => .nil
  | .x t => .x t
  | .cnot c t h => .cnot c t h
  | .toff c₁ c₂ t h₁₂ h₁t h₂t => .toff c₁ c₂ t h₁₂ h₁t h₂t
  | .seq p₁ p₂ => .seq p₂.inv p₁.inv

@[simp] theorem toCircuit_inv {K : ℕ} (p : RevProg K) :
    p.inv.toCircuit = p.toCircuit.inverse := by
  induction p with
  | nil => rfl
  | x _ => rfl
  | cnot _ _ _ => rfl
  | toff _ _ _ _ _ _ => rfl
  | seq p₁ p₂ ih₁ ih₂ => simp [inv, toCircuit, Circuit.inverse_seq, ih₁, ih₂]

@[simp] theorem count_t_zero {K : ℕ} (p : RevProg K) :
    p.toCircuit.count PrimitiveGate.T = 0 := by
  induction p <;> simp_all [toCircuit]

@[simp] theorem eval_inv_left {K : ℕ} (p : RevProg K) (β : BitAssignment K) :
    p.inv.eval (p.eval β) = β := by
  have hc (γ : BitAssignment K) (t : Wire K) (d : ZMod 2) :
      Function.update (Function.update γ t (γ t + d)) t (γ t + d + d) = γ := by
    funext w; by_cases hw : w = t
    · subst hw; simp only [Function.update_self, add_assoc, zmod2_add_self, add_zero]
    · simp [Function.update_of_ne hw]
  induction p generalizing β with
  | nil => rfl
  | x t => simpa only [inv, eval, Function.update_self] using hc β t 1
  | cnot c t h =>
      simpa only [inv, eval, Function.update_self, Function.update_of_ne h] using hc β t (β c)
  | toff c₁ c₂ t _ h₁t h₂t =>
      simpa only [inv, eval, Function.update_self, Function.update_of_ne h₁t,
        Function.update_of_ne h₂t] using hc β t (β c₁ * β c₂)
  | seq p₁ p₂ ih₁ ih₂ => simp [inv, eval, ih₂, ih₁]

@[simp] theorem inv_inv {K : ℕ} (p : RevProg K) : p.inv.inv = p := by
  induction p <;> simp_all [inv]

@[simp] theorem eval_inv_right {K : ℕ} (p : RevProg K) (β : BitAssignment K) :
    p.eval (p.inv.eval β) = β := by
  simpa using eval_inv_left p.inv β

end RevProg

end ClassicalAndGatePrimitives

/-! ### Clean-Ancilla Subspace Unitary Extraction (`cleanBlockUnitary`) -/

/-! ## Section 2: Exact Multi-Bit Unsigned Arithmetic
(`regValBits`, `addRegMod`, `ltReg`, `mulReg`) -/

end MomSlots35Coulomb
end
end MomSlots35Coulomb

section MomSlots35Slot3Helpers
local instance (priority := 1000000) instNeZeroTwoPow_MomSlots35Slot3Helpers (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-!
# Slot 3 (`U_pn(cfg)`, Coin `c = 6`) Concrete Clean-Workspace `DynamicCircuit` Oracle
(`MomSlots35Slot3ProjNuclear`)

Complete verified concrete
clean-workspace `DynamicCircuit` oracle, 48-wire phase-gradient catalyst intertwining proof,
Hadamard top-block extraction, spectral-norm cap `alphaSlot3 ≤ 20150 ≤ 20310` Ha, `permElectron`
symmetry proof, and fermionic-sector intrinsic error bound `≤ 3 / 10 ^ 6 ≤ 5 / 1000000` Ha for
**Slot 3 (`U_pn(cfg)`, `fullSysCoinIdx 3 = 6 = (0, 1, 1)_LSB`)**.
-/

public section

namespace MomSlots35Slot3ProjNuclear

open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open MomSlots35Coulomb
open SpecsAux.DyadicSubgridToeplitz512AndShift
open scoped Matrix BigOperators Matrix.Norms.L2Operator

namespace Slot3CleanPrim

open DyadicQft64WalkCircuit

section Slot1CleanCircuit

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_eq_or x with rfl | rfl <;> rfl

namespace RevProg

/-- Lower a reversible classical program to a pure quantum `Circuit K`. -/
def toCircuit {K : ℕ} : RevProg K → Circuit K
  | .nil => .identity
  | .x t => Circuit.X t
  | .cnot c t h => Circuit.CNOT c t h
  | .toff c₁ c₂ t h₁₂ h₁t h₂t => Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t
  | .seq p₁ p₂ => p₁.toCircuit.seq p₂.toCircuit

/-- Syntactic inverse of a reversible classical program. -/
def inv {K : ℕ} : RevProg K → RevProg K
  | .nil => .nil
  | .x t => .x t
  | .cnot c t h => .cnot c t h
  | .toff c₁ c₂ t h₁₂ h₁t h₂t => .toff c₁ c₂ t h₁₂ h₁t h₂t
  | .seq p₁ p₂ => .seq p₂.inv p₁.inv

@[simp] theorem count_t_zero {K : ℕ} (p : RevProg K) :
    p.toCircuit.count PrimitiveGate.T = 0 := by
  induction p <;> simp_all [toCircuit]

@[simp] theorem eval_inv_left {K : ℕ} (p : RevProg K) (β : BitAssignment K) :
    p.inv.eval (p.eval β) = β := by
  have hc (γ : BitAssignment K) (t : Wire K) (d : ZMod 2) :
      Function.update (Function.update γ t (γ t + d)) t (γ t + d + d) = γ := by
    funext w; by_cases hw : w = t
    · subst hw; simp only [Function.update_self, add_assoc, zmod2_add_self, add_zero]
    · simp [Function.update_of_ne hw]
  induction p generalizing β with
  | nil => rfl
  | x t => simpa only [inv, eval, Function.update_self] using hc β t 1
  | cnot c t h =>
      simpa only [inv, eval, Function.update_self, Function.update_of_ne h] using hc β t (β c)
  | toff c₁ c₂ t _ h₁t h₂t =>
      simpa only [inv, eval, Function.update_self, Function.update_of_ne h₁t,
        Function.update_of_ne h₂t] using hc β t (β c₁ * β c₂)
  | seq p₁ p₂ ih₁ ih₂ => simp [inv, eval, ih₂, ih₁]

/-- Syntactic Toffoli gate count of a `RevProg K`. -/
def countToff {K : ℕ} : RevProg K → ℕ
  | .nil => 0
  | .x _ => 0
  | .cnot _ _ _ => 0
  | .toff _ _ _ _ _ _ => 1
  | .seq p₁ p₂ => p₁.countToff + p₂.countToff

@[simp] theorem countToff_inv {K : ℕ} (p : RevProg K) : p.inv.countToff = p.countToff := by
  induction p <;> simp_all [inv, countToff]
  omega

@[simp] theorem toCircuit_count_toff {K : ℕ} (p : RevProg K) :
    p.toCircuit.count PrimitiveGate.TOFF = p.countToff := by
  induction p <;> simp_all [toCircuit, countToff]

end RevProg

@[simp] theorem countToff_inv_s3 {K : ℕ} (p : RevProg K) : p.inv.countToff = p.countToff := by
  induction p with
  | seq p₁ p₂ ih₁ ih₂ => dsimp [RevProg.inv, RevProg.countToff]; omega
  | _ => rfl

@[simp] theorem slice_apply_eq {K m offset len : ℕ} (r : QRegister m K) (h : offset + len ≤ m)
    (j : Fin len) :
    (r.slice offset len h) j = r ⟨offset + j.val, by omega⟩ :=
  congrArg r (Fin.ext (by
    dsimp [MomSlots35Slot3HelpersAlt.qreg_block_apply,
      MomSlots35Slot3HelpersAlt.qreg_block_wires_apply,
      MomSlots35Slot3HelpersAlt.qreg_whole_wires,
      MomSlots35Slot3HelpersAlt.emb_trans_apply,
      MomSlots35Slot3HelpersAlt.emb_refl_apply,
      MomSlots35Slot3HelpersAlt.emb_mk_apply]))

end Slot1CleanCircuit

end Slot3CleanPrim

end MomSlots35Slot3ProjNuclear
end
end MomSlots35Slot3Helpers

section MomSlots35Slot5Part1
local instance (priority := 1000000) instNeZeroTwoPow_MomSlots35Slot5Part1 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-!
# Slot 5 (`V_ep`, Coin `7`) Pure-Momentum Coulomb Block-Encoding Oracle

Zero-`.TOFF`, clean-workspace `MomSingleSlotOracle 80 48 5` instantiation
realizing `bUnitTwosSlot5` with scale `alphaSlot5` (`≤ 4957` Ha), zero energy shift (`eShift = 0`),
and intrinsic fermionic-sector error `1 / 10 ^ 6 ≤ 5 / 1000000` Ha.
-/

public section

namespace MomSlots35Slot5ElecProj

open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real
open SpecsAux.SpecMirror SpecsAux.FullScaleBESector
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open scoped Matrix BigOperators Matrix.Norms.L2Operator

namespace Slot5Internal

section ClassicalAndGatePrimitives

theorem zmod2_eq_or (x : ZMod 2) : x = 0 ∨ x = 1 := by
  match x with
  | 0 => exact Or.inl rfl
  | 1 => exact Or.inr rfl

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_eq_or x with rfl | rfl <;> rfl

namespace RevProg

/-- Lower a reversible classical program to a pure quantum `Circuit K`. -/
def toCircuit {K : ℕ} : RevProg K → Circuit K
  | .nil => .identity
  | .x t => Circuit.X t
  | .cnot c t h => Circuit.CNOT c t h
  | .toff c₁ c₂ t h₁₂ h₁t h₂t => Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t
  | .seq p₁ p₂ => p₁.toCircuit.seq p₂.toCircuit

/-- Syntactic inverse of a reversible classical program. -/
def inv {K : ℕ} : RevProg K → RevProg K
  | .nil => .nil
  | .x t => .x t
  | .cnot c t h => .cnot c t h
  | .toff c₁ c₂ t h₁₂ h₁t h₂t => .toff c₁ c₂ t h₁₂ h₁t h₂t
  | .seq p₁ p₂ => .seq p₂.inv p₁.inv

/-- Classical computational-basis action of a `RevProg K` on `BitAssignment K`. -/
def eval {K : ℕ} : RevProg K → BitAssignment K → BitAssignment K
  | .nil, β => β
  | .x t, β => Function.update β t (β t + 1)
  | .cnot c t _, β => Function.update β t (β t + β c)
  | .toff c₁ c₂ t _ _ _, β => Function.update β t (β t + β c₁ * β c₂)
  | .seq p₁ p₂, β => p₂.eval (p₁.eval β)

@[simp] theorem toCircuit_inv {K : ℕ} (p : RevProg K) :
    p.inv.toCircuit = p.toCircuit.inverse := by
  induction p with
  | nil => rfl
  | x _ => rfl
  | cnot _ _ _ => rfl
  | toff _ _ _ _ _ _ => rfl
  | seq p₁ p₂ ih₁ ih₂ => simp [inv, toCircuit, Circuit.inverse_seq, ih₁, ih₂]

@[simp] theorem count_t_zero {K : ℕ} (p : RevProg K) :
    p.toCircuit.count PrimitiveGate.T = 0 := by
  induction p <;> simp_all [toCircuit]

@[simp] theorem eval_inv_left {K : ℕ} (p : RevProg K) (β : BitAssignment K) :
    p.inv.eval (p.eval β) = β := by
  have hc (γ : BitAssignment K) (t : Wire K) (d : ZMod 2) :
      Function.update (Function.update γ t (γ t + d)) t (γ t + d + d) = γ := by
    funext w; by_cases hw : w = t
    · subst hw; simp only [Function.update_self, add_assoc, zmod2_add_self, add_zero]
    · simp [Function.update_of_ne hw]
  induction p generalizing β with
  | nil => rfl
  | x t => simpa only [inv, eval, Function.update_self] using hc β t 1
  | cnot c t h =>
      simpa only [inv, eval, Function.update_self, Function.update_of_ne h] using hc β t (β c)
  | toff c₁ c₂ t _ h₁t h₂t =>
      simpa only [inv, eval, Function.update_self, Function.update_of_ne h₁t,
        Function.update_of_ne h₂t] using hc β t (β c₁ * β c₂)
  | seq p₁ p₂ ih₁ ih₂ => simp [inv, eval, ih₂, ih₁]

@[simp] theorem inv_inv {K : ℕ} (p : RevProg K) : p.inv.inv = p := by
  induction p <;> simp_all [inv]

@[simp] theorem eval_inv_right {K : ℕ} (p : RevProg K) (β : BitAssignment K) :
    p.eval (p.inv.eval β) = β := by
  simpa using eval_inv_left p.inv β

end RevProg

end ClassicalAndGatePrimitives

/-! ## Section 2: Exact Multi-Bit Unsigned Arithmetic
(`regValBits`, `addRegMod`, `ltReg`, `mulReg`) -/

section UnsignedArithmetic

@[simp] theorem fin_one_add_eq_succ {m : ℕ} (j : Fin m) (h : 1 + j.val < m + 1) :
    (⟨1 + j.val, h⟩ : Fin (m + 1)) = j.succ := Fin.ext (Nat.add_comm 1 j.val)

@[simp] theorem slice_one_succ {K m : ℕ} (r : QRegister (m + 1) K) (h : 1 + m ≤ m + 1)
    (j : Fin m) : (r.slice 1 m h) j = r j.succ := by
  simp

end UnsignedArithmetic

end Slot5Internal
end MomSlots35Slot5ElecProj
end
end MomSlots35Slot5Part1

end QuantumComputation.Specs.StoppingPowerSolution
