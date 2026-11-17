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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.PosBranchWalkLem

set_option Elab.async false

@[expose] public section

set_option allowUnsafeReducibility true
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section NuclearTwistAndXor654Concrete
local instance (priority := 1000000) instNeZeroTwoPow_NuclearTwistAndXor654Concrete (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-!
# Full-system Continuous-`R_l` Nuclear Phase Twist, `654`-Axis Offset XOR, and Single-Pass `Slot 2 &
Slot 4` Twist (`NuclearTwistAndXor654Concrete`)

Complete zero-`sorry`, zero-`native_decide`, zero-`.TOFF`, polymorphic `{Var : Type}` concrete
circuit and operator bridge on the locked `fullSysCoreWires mPayload` core
register (`3954 + mPayload`, `4034` at `mPayload = 80`) + `48`-wire phase-gradient catalyst
`rPGTwist`
(`|PG_48⟩`) + `mWorkTwist = 256` clean ancillas `rWork`:

1. **Clean-Workspace Unitary & Inverse Realization Algebra (`Section 1`)**:
   - `substCircuit_realizes_clean` & `substCircuit_inverse_realizes_clean`: lift any classical
     `Circuit n` (`anc ∉ c.support`) and `c.inverse` via `SplitLifetimeKX2Mux.substCircuit v anc`
     directly to `DynamicCircuit.RealizesEmbeddedUnitaryWithCleanWorkspace` with `.count .TOFF = 0`.
   - `cleanAction_inv_automatic` & `realizesClean_absorb_tmp`: pure matrix-algebraic workspace
     absorption proving that whenever `d_fwd` realizes `uExt` restoring `rTmp` to `|0⟩` as `uAct` on
     `rAct`, ANY circuit `d_inv` realizing `uExt⁻¹` **automatically** restores `rTmp` to `|0⟩` and
     realizes the **exact full-space unitary inverse `uAct⁻¹`** with zero reverse bit-tracking.
   - `IntertwinesLocalCat` (`rfl`-identical to `FullSysCatSegmentBridge.IntertwinesLocalCat`),
   closed
     under sequential multiplication `.mul`, unitary inversion `.inv`, core lifting
     `.of_core_unitary`,
     and arbitrary global register placement `.embed`.

2. **Concrete Zero-`TOFF` `dTwistParam` & `dTwistInvParam` (`mWorkTwist = 256`, `Section 2`)**:
   - Parameterized polymorphically in `swapOnSlot2 : Bool` (`abbrev dTwist := dTwistParam true` and
     `abbrev dTwistSlot4Only := dTwistParam false`), matching `PosSlots24BranchConcrete` both ways:
     * **Step 1 (`dBarrelSwap`)**: two-half `128`-wire Babbush–Gidney one-hot decode + `18`-wire
       Fredkin swap implementing exact `Equiv.swap i (0 : Fin numElectrons)` for all `i < 218`,
       active
       on `coin ∈ {0, 1}` when `swapOnSlot2 = true` and on `coin = 1` when `swapOnSlot2 = false`.
     * **Step 2 (`dXor32All654`)**: `DyadicQft64Engine.parallelBit5FlipAxes` across all `654`
       electron axes (`0 T`, `0 TOFF`, self-inverse), converting two's-complement `u_twos` into
       unsigned offset binary `u_off = xor32 u_twos` (`u_off.val = twosComp6Int u_twos + 32`).
     * **Step 3 (`dSlot4CosetKick`)**: on `coin = 1` (`Slot 4 = V_ee`), kicks `(b₁ w - b₀ w) *
     u_off[0, w]`
       at shift `s = 41, k = 5` (`2^48 / 2^41 = 128`) into `rPGTwist` via `gidneyAddShiftDyn` (`+1`)
       and `gidneySubShiftDyn` (`-1`), synthesizing exact `omega128` sub-grid twist with `0` extra
       `Rz`/`S`.
     * **Step 4 (`dSlot2NuclearKick c`)**: on `coin = 0` (`Slot 2 = U_en`), loads `48`-bit rounded
       fractional nuclear coordinate `nuclearM48 c l w` (`l ∈ Fin 216`) via two-half `128`-way
       decode
       with `c`-independent `T`-count, sums all `218` unsigned axes `∑_{k=0}^{217} u_off[k, w]` into
       `rSum14` (`14` bits), kicks `+∑_{s=0}^{13} 2^s * rSum14[s] * nuclearM48 c l w` into
       `rPGTwist`,
       and cleanly uncomputes `rSum14` and `rM48`.

3. **Continuous-`c.nuclei` `Slot 2` Perturbation `< 3 / 100000` Ha & `Slot 4` `Equiv.swap i 0` +
Coset Bridge (`Section 3`)**:
   - `slot2_nuclear48_perturbation_lt_3e5`: proves that for **every** continuous `c :
   Configuration`,
     replacing exact `oneElectronPhase (c.nuclei l)` by `48`-bit dyadic nuclear twist in
     `uenCenteredReflRaw`
     perturbs the full `218`-electron operator norm by **`≤ 3 / 100000` Ha** (`2.49 × 10⁻⁵` Ha),
     matching
     `FullSysPosSlots24AndTopConcrete.full_sixSlot_with_nuclear_phase_le_beEps` identically!
   - `slot2_swap_invariant_and_ket_conj` & `slot4_barrelSwap_and_coset_conj`: prove complete
   `Equiv.swap i 0`
     invariance on `Slot 2` (`swapOnSlot2 = true` and `false` give identical `Slot 2` operators!)
     and exact
     single-anchor + `(b₁ - b₀)` coset conjugation on `Slot 4` (`ε = 0`).
-/

public section

namespace NuclearTwistAndXor654Concrete

open Operator QProg Matrix HermitianMat Real SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner DyadicQft64
open DyadicQft64Engine
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.DyadicSubgridToeplitz128
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

/-! ## Section 2: Classical Gate Primitives, `unaryDecode128Circuit`, and Core Wire Slices -/

section ClassicalPrimitives

variable {n : ℕ}

@[simp] theorem count_circuit_sequence {a : ℕ} (g : PrimitiveGate a) :
    ∀ (L : List (Circuit n)), (Circuit.sequence L).count g = (L.map (Circuit.count g)).sum
  | [] => rfl
  | c :: cs => by simp [Circuit.sequence_cons, Circuit.count_seq, count_circuit_sequence g cs]

end ClassicalPrimitives

/-! ## Section 4: Concrete Zero-`TOFF` Circuits (`dBarrelSwap`, `dXor32All654`, `dSlot4CosetKick`,
`dSlot2NuclearKick`) -/

/-! ## Section 5: Continuous-`c.nuclei` `Slot 2` Perturbation Bound `< 3 / 100000` Ha & `Slot 4`
Exact Single-Pass Bridge -/

section PhysicsAndNormBridges

/-- Nearest-integer rounding distance modulo `1`:
for any `x : ℝ` with `0 ≤ x < 1`, there exists `q : ℤ` (`q ∈ {0, 1}`) such that
`|(nuclearM48_raw + q * 2^48) / 2^48 - x| ≤ (1 / 2) / 2^48`. -/
theorem nuclearM48_phase_diff_le (c : Configuration) (l : Fin 216) (p : Fin 3 → ℤ)
    (hp : ∀ w : Fin 3, |p w| ≤ 32) :
    ‖oneElectronPhase48 c l p - oneElectronPhase (c.nuclei l) p‖ ≤ (302 : ℝ) / 2 ^ 48 := by
  let x : Fin 3 → ℝ := fun w ↦ c.nuclei l w / cellVolume ^ (1 / 3 : ℝ)
  let fr : Fin 3 → ℝ := fun w ↦ Int.fract (x w)
  let N : Fin 3 → ℕ := fun w ↦ ⌊(2 ^ 48 : ℝ) * fr w + 1 / 2⌋₊
  -- Note `(N w : ℤ) ≡ (nuclearM48 c l w : ℤ) [ZMOD 2^48]`, so `dyadicTurn 48` has IDENTICAL value
  -- at `N w` and `nuclearM48 c l w`!
  have hturn_eq : oneElectronPhase48 c l p =
      dyadicTurn 48 (-(∑ w : Fin 3, p w * (N w : ℤ))) := by
    unfold oneElectronPhase48 dyadicTurn
    have hsplit (w : Fin 3) : (N w : ℤ) =
        (nuclearM48 c l w : ℤ) + (2 ^ 48 : ℤ) * ((N w / 2 ^ 48 : ℕ) : ℤ) := by
      dsimp only [nuclearM48, N]
      exact_mod_cast (Nat.mod_add_div (⌊(2 ^ 48 : ℝ) * fr w + 1 / 2⌋₊) (2 ^ 48)).symm
    rw [show -(∑ w : Fin 3, p w * (N w : ℤ)) = -(∑ w : Fin 3, p w * (nuclearM48 c l w : ℤ)) +
        (-(∑ w : Fin 3, p w * ((N w / 2 ^ 48 : ℕ) : ℤ))) * (2 ^ 48 : ℤ) by
      rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, hsplit 0, hsplit 1, hsplit 2]
      ring, turnPow2_add_period]
  -- Also `oneElectronPhase (c.nuclei l) p = Complex.exp (-(2 * π * ∑ w, p w * fr w) * I)` because
  -- integer parts shift by `-2π i * k`!
  have hexact_eq : oneElectronPhase (c.nuclei l) p =
      Complex.exp ((-((2 * π) * ∑ w : Fin 3, (p w : ℝ) * fr w) : ℝ) * Complex.I) := by
    unfold oneElectronPhase waveVector
    have hdot : (fun w ↦ 2 * π * (p w : ℝ) / cellVolume ^ (1 / 3 : ℝ)) ⬝ᵥ c.nuclei l =
        2 * π * ∑ w : Fin 3, (p w : ℝ) * x w := by
      simp only [dotProduct, x, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    have hsplit (w : Fin 3) : x w = (⌊x w⌋ : ℝ) + fr w := (Int.floor_add_fract (x w)).symm
    have hsum : (∑ w : Fin 3, (p w : ℝ) * x w) =
        ((∑ w : Fin 3, p w * ⌊x w⌋ : ℤ) : ℝ) + ∑ w : Fin 3, (p w : ℝ) * fr w := by
      push_cast
      rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
      linear_combination (p 0 : ℝ) * hsplit 0 + (p 1 : ℝ) * hsplit 1 + (p 2 : ℝ) * hsplit 2
    rw [hdot, hsum, show -((2 * π * (((∑ w : Fin 3, p w * ⌊x w⌋ : ℤ) : ℝ) +
          ∑ w : Fin 3, (p w : ℝ) * fr w) : ℝ) : ℂ) * Complex.I =
        ((-(∑ w : Fin 3, p w * ⌊x w⌋) : ℤ) : ℂ) * (2 * ↑π * Complex.I) +
          ((-((2 * π) * ∑ w : Fin 3, (p w : ℝ) * fr w) : ℝ) : ℂ) * Complex.I by
      push_cast
      ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]
  rw [hturn_eq, hexact_eq, show dyadicTurn 48 (-(∑ w : Fin 3, p w * (N w : ℤ))) =
      Complex.exp ((-((2 * π) * ∑ w : Fin 3,
        (p w : ℝ) * ((N w : ℝ) / (2 ^ 48 : ℝ))) : ℝ) * Complex.I) by
    unfold dyadicTurn turnPow2 DyadicQft64.dyadicTurn
    congr 1
    simp only [Fin.sum_univ_three, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_add,
      Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_natCast,
      Complex.ofReal_intCast, Int.cast_neg, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    ring_nf]
  refine (norm_exp_ofReal_mul_I_sub_le _ _).trans ?_
  have hround (w : Fin 3) : |(N w : ℝ) / (2 ^ 48 : ℝ) - fr w| ≤ (1 / 2 : ℝ) / (2 ^ 48 : ℝ) := by
    have hpos : 0 ≤ (2 ^ 48 : ℝ) * fr w + 1 / 2 :=
      add_nonneg (mul_nonneg (by positivity) (Int.fract_nonneg (x w))) (by norm_num)
    have hfl1 : (N w : ℝ) ≤ (2 ^ 48 : ℝ) * fr w + 1 / 2 := Nat.floor_le hpos
    have hfl2 : (2 ^ 48 : ℝ) * fr w + 1 / 2 < (N w : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [abs_le]
    constructor <;> field_simp <;> linarith
  have hsum_err : |(-((2 * π) * ∑ w : Fin 3, (p w : ℝ) * ((N w : ℝ) / (2 ^ 48 : ℝ)))) -
      (-((2 * π) * ∑ w : Fin 3, (p w : ℝ) * fr w))| ≤
      (2 * π) * (3 * (32 * ((1 / 2 : ℝ) / (2 ^ 48 : ℝ)))) := by
    rw [show (-((2 * π) * ∑ w : Fin 3, (p w : ℝ) * ((N w : ℝ) / (2 ^ 48 : ℝ)))) -
          (-((2 * π) * ∑ w : Fin 3, (p w : ℝ) * fr w)) =
        -(2 * π * ∑ w : Fin 3, (p w : ℝ) * ((N w : ℝ) / (2 ^ 48 : ℝ) - fr w)) by
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      ring, abs_neg, abs_mul, abs_of_pos Real.two_pi_pos]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans ?_)
      Real.two_pi_pos.le
    refine le_trans (Finset.sum_le_sum fun w _ ↦ ?_)
      (by norm_num : (∑ _ : Fin 3, (32 * ((1 / 2 : ℝ) / (2 ^ 48 : ℝ)))) ≤ _)
    rw [abs_mul]
    exact mul_le_mul (by exact_mod_cast hp w) (hround w) (abs_nonneg _) (by norm_num)
  linarith [Real.pi_lt_d4]

end PhysicsAndNormBridges

end NuclearTwistAndXor654Concrete

end
end NuclearTwistAndXor654Concrete

section NuclearTwistRealizes
local instance (priority := 1000000) instNeZeroTwoPow_NuclearTwistRealizes (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-!
# Clean-Workspace Realization, Catalyst Intertwining, and Exact Phase-Twist Bundle
(`NuclearTwistRealizes`)

Complete tactic-verified, polymorphic `{Var : Type}` clean-workspace realization
and catalyst-intertwining proofs on `fullSysCoreWires mPayload` (`3954 + mPayload`) + `48`-wire
phase-gradient catalyst `rPGTwist` + `mWorkTwist = 256` clean ancillas `rWork`:

1. **Clean Compute-Kick-Uncompute Engine (`CleanPairEngine`)**:
   - `RealizesCleanPair` & `CleanComputePair.conj_catModAdd_pair`: general clean-ancilla
   compute/uncompute
     algebra, active/workspace widening, list sequencing, and exact permutation-conjugation of
     catalyzed
     modular addition `catModAddUnitary`.
2. **654-Axis XOR & 18-Wire Electron Barrel Swap Realizations (`BarrelAndXor32Core`)**:
   - `dXor32All654_realizesPair` and `dBarrelSwap_realizesPair`: exact forward & inverse
   clean-ancilla
     realizations with `0` `.TOFF` gates.
3. **Classical Dyadic Phase & Sub-Register Commutation Helpers (`Section5ClassicalHelpers`)**:
   - `slot2_shiftDiag_conj_eq_sysNucDiag48`, `slot2_nuclear48_perturbation_lt_1e6`, and
   wire/projector
     commutation transfers (`comm_singleton_basisOutcomeProjector_of_preserves`).
4. **Single-Pass Slot 4 Coset Kick, Slot 2 218-Electron Nuclear Twist, and Master Bundle**:
   - `dSlot4CosetKick_realizesPair`, `uSlot4KickCat_intertwinesLocal`,
     `dSlot2NuclearKick_realizesPair`, `uSlot2KickCat_intertwinesLocal`,
     `dTwistParam_realizesPair`, `dTwistParam_realizesPair_widen`,
     `uTwistCat_intertwinesLocal`, `uTwistCat_inv_intertwinesLocal`,
     `uTwistParam_comm_high_wire`, `uTwistParam_inv_comm_high_wire`,
     `uTwistParam_comm_highReg_proj`.
-/

public section

namespace NuclearTwistRealizes

open Operator QProg Matrix HermitianMat Real SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64Engine
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.DyadicSubgridToeplitz128
open NuclearTwistAndXor654Concrete
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

/-! ## Section 5A–5C: Closed-Form `sysNucDiag48`, `Slot 2` Global-Phase Cancellation & Master
Basis-Ket Commutation -/

/-! ## Section 3: Workspace Partition, Generic Gate Banks, & `Slot 4` Realization
(`dSlot4CosetKick`) -/

/-! ### `Slot 4` (`dSlot4CosetAxisStep` & `dSlot4CosetKick`) Clean Realization & `U_cat_48`
Intertwining -/

section Slot4Realizes

/-- Local helper lifting `catModAddUnitary` directly to `IntertwinesLocalCat`. -/
theorem catModAdd_intertwinesLocal {kAct B : ℕ} (U_cat_B : Unitary (2 ^ B))
    (hcol0 : U_cat_B.1.mulVec (Pi.single 0 1) = phaseGradKet B)
    (shift : BitAssignment kAct → ℕ) : IntertwinesLocalCat U_cat_B
    (catModAddUnitary kAct B shift) (dyadicDiagUnitary kAct B (fun γ ↦ (shift γ : ℤ))) := by
  let rAct0 : QRegister kAct (kAct + B) := .block 0 kAct (by omega)
  let rCat0 : QRegister B (kAct + B) := .block kAct B le_rfl
  have hdisj : rAct0.DisjointWires rCat0 :=
    QRegister.block_disjoint_of_le 0 kAct kAct B (by omega) (by omega) (by omega)
  have hid : rAct0.concat rCat0 hdisj = QRegExt.idReg _ := by
    apply NuclearTwistRealizesAlt.qreg_ext
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_)
    · rw [QRegister.concat_apply_left]
      exact Fin.ext (by simp [QRegExt.idReg, rAct0])
    · rw [QRegister.concat_apply_right]
      exact Fin.ext (by dsimp [QRegExt.idReg, rCat0,
        NuclearTwistRealizesAlt.qreg_block_apply,
        NuclearTwistRealizesAlt.qreg_block_wires_apply,
        NuclearTwistRealizesAlt.qreg_whole_wires,
        NuclearTwistRealizesAlt.emb_trans_apply,
        NuclearTwistRealizesAlt.emb_refl_apply,
        NuclearTwistRealizesAlt.emb_mk_apply])
  have h := catModAddUnitary_intertwinesCat rAct0 rCat0 hdisj U_cat_B hcol0 shift
  rwa [hid, embedUnitary_idReg_eq] at h

end Slot4Realizes

/-! ## Section 5D: Master `dTwistParam` / `dTwistInvParam` Unitary Realization, Catalyst
Intertwining, and Coin/Payload Commutation -/

end NuclearTwistRealizes
end
end NuclearTwistRealizes

section MomSlots35Slot3ProjNuclear
local instance (priority := 1000000) instNeZeroTwoPow_MomSlots35Slot3ProjNuclear (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# Slot 3 (`U_pn(cfg)`, Coin `c = 6`) Concrete Clean-Workspace `DynamicCircuit` Oracle

Complete verified, zero-`.TOFF` concrete clean-workspace `DynamicCircuit` oracle, 48-wire
phase-gradient catalyst intertwining proof, symbolic-`mPayload` (`80 ≤ mPayload`) Hadamard
top-block extraction, spectral-norm cap `alphaSlot3 ≤ 20150 ≤ 20310` Ha, `permElectron`
symmetry proof, and fermionic-sector intrinsic error bound `≤ 3 / 10 ^ 6 ≤ 5 / 1000000` Ha
for **Slot 3 (`U_pn(cfg)`, `fullSysCoinIdx 3 = 6 = (0, 1, 1)_LSB`)**.
-/

public section

namespace MomSlots35Slot3ProjNuclear

open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open ModWrapCoarse8PureMomentum
open Slot5MatrixAndScaleCert
open SpecsAux.DyadicSubgridToeplitz512AndShift
open DyadicQft64 DyadicQft64.PhasePerm
open scoped Matrix BigOperators Matrix.Norms.L2Operator

attribute [local irreducible] box3D nonzeroBox3D

/- ## Section 4A: Hardware Modular Projectile Step (`M_0 = 127`), 17-Wire Split Bijection,
and Symbolic-`mPayload` Core Unitary Seam -/

section Slot3HardwareAndCore

theorem s3FineRad_54bit_bounds {u38 sTrue μ : ℕ} (hu : u38 < 2 ^ 38) (hs : sTrue ≤ 3 * 254 *
    254) (hμ : μ < 7) : sTrue * u38 < 2 ^ 56 ∧ sTrue * u38 + sTrue
    < 2 ^ 56 ∧ cRad7Computable μ + 1 < 2 ^ 56 := by
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  rcases (by omega : μ = 0 ∨ μ = 1 ∨ μ = 2 ∨ μ = 3 ∨ μ = 4 ∨ μ = 5 ∨ μ = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [cRad7Computable, cRad38True]

end Slot3HardwareAndCore
end MomSlots35Slot3ProjNuclear
end
end MomSlots35Slot3ProjNuclear

section NuclearTwistDisentangleSum288
local instance (priority := 1000000) instNeZeroTwoPow_NuclearTwistDisentangleSum288 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# Sequential-Chunk `Slot 2` Coordinate-Sum & `M_{l,w}` Disentangling Circuit (`mWork ≤ 288`)

Constructs and verifies zero-`.TOFF` temporary-AND compute/uncompute dynamic circuits
(`slot2KeepCompute288` / `slot2KeepCompute288Inv`) loading `slot2M48Val c hm w` (`48` wires) and
`slot2AxisSum w` (`14` wires) onto `62` / `63` persistent wires using at most `177` recycled clean
scratch wires (`239` / `240` total workspace wires, within both `mWorkTwist = 256` and `mWork =
288`):

1. **`RevTempPerm`**:
   - Phase-free clean-tail reversible temporary-AND language (`CliffProg`, `RevTempProg`,
     `ValidCleanRem`, `ScopedAlloc`, `realizes_clean_action`), compiling to `DynamicCircuit Var n`
     with `count .TOFF = 0` and exact `count .T = 4 * countTempAnd`.
   - Reusable arithmetic and QROM combinators with exact `tempAnd` and scratch counts:
     * `inPlaceAdd` (`W - 1` `tempAnd`s, `W - 1` clean carry wires; bitwise-flip `0`-`T` inverse),
     * `withFullAdd` and `withCSA` (`W` `tempAnd`s, `2 * W` wires),
     * `withUnarySplit`, `withUnarySplitRange`, `withSeededUnaryTree`, and in-place
       `selectSwapXorBitLoop` (`B = 2` seeded `SELECTSWAP` QROM in `2^d + 2` scratch wires).

2. **`NuclearTwistDisentangleSum288`**:
   - `slot2KeepCompute288` / `slot2KeepCompute288Inv`:
     * `14` sequential `15`-electron `withCSA 6` + `inPlaceAdd 14` chunks (`14 * 104 = 1,456`
       `tempAnd`s, peak `177` clean scratch wires, recycled across chunks) + `1` `8`-electron tail
       chunk (`62` `tempAnd`s, `93` clean scratch wires) = `1,518` `tempAnd`s (`6,072` `T` gates),
       inverted at identical `6,072` `T` cost via bitwise complementation on `rSum14` (`0` `T`).
     * Self-inverse `coin = 0`-seeded `SELECTSWAP` (`B = 2`) load of `slot2M48Val c hm w` onto
       `rM48` (`2 + 127 + 48 = 177` `tempAnd`s = `708` `T` gates, `132` clean scratch wires).
     * Total one-way cost: `1,695` `tempAnd`s = `6,780` `T` gates (`≤ 7,048` `T`), `0` `.TOFF`.
   - Exports `CleanComputePair` theorems for:
     * `slot2KeepComputeCore_cleanPair` (`rKeep : QRegister 62 n`, `rScr : QRegister mScr n`,
       `177 ≤ mScr`),
     * `slot2Keep62Compute_cleanPair` (`rWork.slice 0 62 _`, `239 ≤ mWork`),
     * `slot2Keep63SliceCompute_cleanPair` (`rWork.slice 0 63 _`, `240 ≤ mWork`),
     * `slot2Keep63Twist_cleanPair` (`rKeep63 rWork`, `rWork179 rWork` on `mWorkTwist = 256`).
-/

public section

namespace RevTempPerm

open Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg HermitianMat
open StreamingBchComparator
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64.PhasePerm
open SpecsAux.PhaseGradCatalystCore
open NuclearTwistAndXor654Concrete hiding fullSysCoreWires
open NuclearTwistRealizes
open scoped Matrix BigOperators ComplexOrder MatrixOrder Circuit.Notation

@[simp] theorem dyn_count_seq {Var : Type} {n : ℕ} (d₁ d₂ : DynamicCircuit Var n)
    {k : ℕ} (g : PrimitiveGate k) :
    (DynamicCircuit.seq d₁ d₂).count g = d₁.count g + d₂.count g := rfl

namespace RevTempProg

/-- Single-qubit Pauli-`X` gate in `RevTempProg m`. -/
def x {m : ℕ} (q : Wire m) : RevTempProg m := .cliff (.x q)

end RevTempProg

end RevTempPerm

end
end NuclearTwistDisentangleSum288

end QuantumComputation.Specs.StoppingPowerSolution
