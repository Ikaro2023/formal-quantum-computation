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

public import
  QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.ZeroCmp20OuterAnfParam
public import
  QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.AnfAndCoin14Core

@[expose] public section

/-!
# Compact `2,504-T` Context-Borrowing `wInner2 = 20` Inner `PREP_mid`
Exact (`δ = 0` extra error beyond `uIdx`) `2,504-T` inner base for the `(wOuter, 20, kZeroOut, 16)`
outer-parameterized walk reflection on `163 ≤ sUb`:
1. **Leg 4 Cold `(6, 4, 2)` L-Tromino Unloader (`212 T`, `0 TOFF`, `66 ≤ sScr`):** expands
   `rA6` (`6` context bits) into `rHotA64` (`124 T`), `rB4` (`b_1..b_4`) into `rHotB16` ANF
   (`28 T`), `rC2` (`b_0, rc_6`) into `rAllC` (`4 T`), and covers all `14 × 3 = 42` active
   bilinear `(uB, uC)` monomials in `14` in-place L-steps (`56 T`), borrowing the `16` freed
   X-measured alias wires so `66 + 16 = 82` scratch wires suffice (`66 ≤ sUb` on Step 4).
2. **Compact `74-T` Zero-`wCmp` Packet Mux-Swap:** combines the `14-T` dyadic `4`-qubit coin
   `optCoin9Unitary` with the `60-T` `9`-AND `pktMuxSwapDyn` (`19 ≤ s`).
3. **Assembled `2,504-T` Inner Engine + Splitter-Parametric API + All `6` `uIdx` Tiers:**
   combines Part 1 (`708 T` Legs 1 and 3), Part 2 (`44 T` Leg 2), Part 3
   (`212 T` Leg 4), and Part 4 (`74 T × 4`), exporting both a general `5`-qubit `L = 30`
   splitter-parametric API (`(mag30Fwd, mag30Bwd, mag30Impl, mag30Ideal, tMag30, δIdx)` plus
   `Circuit 5` wrappers) and turnkey closures for `Clean100` (`2,904 T`), `Clean98` (`2,896 T`),
   `Tight97` (`2,892 T`), `Med96` (`2,888 T`), `Opt86` (`2,848 T`), and `Opt81` (`2,828 T`)
   (Babbush et al., *Phys. Rev. X* **8**, 041015, 2018, DOI: `10.1103/PhysRevX.8.041015`;
   Gidney, *Quantum* **2**, 74, 2018, DOI: `10.22331/q-2018-06-18-74`;
   Berry et al., *Quantum* **3**, 208, 2019, DOI: `10.22331/q-2019-12-02-208`;
   Low et al., *Quantum* **8**, 1375, 2024, DOI: `10.22331/q-2024-06-17-1375`;
   Kliuchnikov, Maslov, and Mosca, *Quantum Inf. Comput.* **13**, 607, 2013).
-/

namespace
  QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactStepCompact2504ZeroCmp20
open QuantumComputation.Specs QuantumComputation.Specs.P450

section Core2504

set_option exponentiation.threshold 512

open Operator QProg Matrix Circuit Real HermitianMat
open QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution
open BlockEncodingCore BlockEncodingCircuit
open Solution.CoherentAlias
open Solution.AliasPrep
open Solution.Phase2MidSandwich
open Solution.CompactBilinearPrep
open Solution.MidReflCtxRetain
open Solution.OptFactoredMag30AndCoin9
open Solution.Cat11CompactPhase2Bridge
open Solution.ReordOuter13Bridge
open Solution.ZeroRcHotPrepMid21Fast
open Solution.OptXMeasUnload21
open Solution.Tuned162ScheduledSympQrom21
open Solution.Tuned162StepSympAnfQrom21
open Solution.OptStepSympAnfQrom21
open Solution.OptU2Grover184PrepOut13
open Solution.TopIntegrationBridge
open Solution.MobiusOptSubcube163Walk
open Solution.CompactTuned162StepWalk
open Solution.CompactTuned162StepZeroCmp20
open Solution.CompactZeroCmp20OuterParam
open Solution.CompactStepZeroCmp20OuterParam
open Solution.StepAnfAndCoin14Core
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

local instance (priority := 1000000) instNeZeroTwoPow2504 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

/-! ## Section 1: Leg 4 Cold `(6, 4, 2)` L-Tromino Unloader (`212 T`, `0 TOFF`, `66 ≤ sScr`) -/

/-- `2`-wire index map `[0, 11]` (`b_0, rc_6`) inside `12`-wire `rIdx`. -/
def c2In12Idx : Fin 2 → Fin 12
  | ⟨0, _⟩ => ⟨0, by decide⟩
  | ⟨1, _⟩ => ⟨11, by decide⟩

theorem c2In12Idx_injective : Function.Injective c2In12Idx := by decide

/-- `2`-wire subregister `[rIdx 0, rIdx 11]` of `12`-wire `rIdx`. -/
def c2In12Reg : QRegister 2 12 := ⟨⟨c2In12Idx, c2In12Idx_injective⟩⟩

/-- `12`-bit address built from `zA = rc_0..rc_5`, `zB = b_1..b_4`, `zC = (b_0, rc_6)`. -/
def cubeAddr642 (zA : Fin (2 ^ 6)) (zB : Fin (2 ^ 4)) (zC : Fin (2 ^ 2)) : Fin (2 ^ 12) :=
  ⟨(zC.val % 2) + 2 * zB.val + 32 * zA.val + 2048 * (zC.val / 2),
    by have := zA.isLt; have := zB.isLt; have := zC.isLt; omega⟩

private theorem cubeAddr642_div32 (zA : Fin (2 ^ 6)) (zB : Fin (2 ^ 4))
    (zC : Fin (2 ^ 2)) :
    (cubeAddr642 zA zB zC).val / 32 = zA.val + 64 * (zC.val / 2) := by
  have h1 : (cubeAddr642 zA zB zC).val =
      ((zC.val % 2) + 2 * zB.val) + 32 * (zA.val + 64 * (zC.val / 2)) := by
    dsimp [cubeAddr642]; ring
  have h2 : (zC.val % 2) + 2 * zB.val < 32 := by
    have := Nat.mod_lt zC.val (by decide : 0 < 2)
    have := zB.isLt; omega
  rw [h1, Nat.add_mul_div_left _ _ (by decide : 0 < 32), Nat.div_eq_of_lt h2, zero_add]

private theorem basisBits12_cubeAddr642_a (zA : Fin (2 ^ 6)) (zB : Fin (2 ^ 4))
    (zC : Fin (2 ^ 2)) (i : Fin 6) :
    basisBits 12 (cubeAddr642 zA zB zC) ⟨5 + i.val, by omega⟩ = basisBits 6 zA i := by
  rw [_root_.basisBits_eq_div_mod, _root_.basisBits_eq_div_mod]
  refine congrArg ((↑) : ℕ → ZMod 2) ?_
  have hp : (2 : ℕ) ^ (5 + i.val) = 32 * 2 ^ i.val := Nat.pow_add 2 5 i.val
  have h64 : (64 : ℕ) = 2 ^ i.val * (2 * 2 ^ (5 - i.val)) := by
    have hi : i.val + (1 + (5 - i.val)) = 6 := by have := i.isLt; omega
    calc (64 : ℕ) = 2 ^ 6 := rfl
      _ = 2 ^ (i.val + (1 + (5 - i.val))) := by rw [hi]
      _ = 2 ^ i.val * (2 ^ 1 * 2 ^ (5 - i.val)) := by rw [Nat.pow_add, Nat.pow_add]
      _ = 2 ^ i.val * (2 * 2 ^ (5 - i.val)) := rfl
  dsimp only
  rw [hp, ← Nat.div_div_eq_div_mul, cubeAddr642_div32, h64, Nat.mul_assoc (2 ^ i.val),
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos i.val), Nat.mul_assoc 2,
    Nat.add_mul_mod_self_left]

private theorem basisBits12_cubeAddr642_b (zA : Fin (2 ^ 6)) (zB : Fin (2 ^ 4))
    (zC : Fin (2 ^ 2)) (i : Fin 4) :
    basisBits 12 (cubeAddr642 zA zB zC) ⟨1 + i.val, by omega⟩ = basisBits 4 zB i := by
  rw [_root_.basisBits_eq_div_mod, _root_.basisBits_eq_div_mod]
  refine congrArg ((↑) : ℕ → ZMod 2) ?_
  have hzA : zA.val < 64 := zA.isLt
  have hzB : zB.val < 16 := zB.isLt
  have hzC : zC.val < 4 := zC.isLt
  rcases i with ⟨_ | _ | _ | _ | _, hi⟩
  · dsimp [cubeAddr642]; omega
  · dsimp [cubeAddr642]; omega
  · dsimp [cubeAddr642]; omega
  · dsimp [cubeAddr642]; omega
  · omega

private theorem basisBits12_cubeAddr642_c (zA : Fin (2 ^ 6)) (zB : Fin (2 ^ 4))
    (zC : Fin (2 ^ 2)) (i : Fin 2) :
    basisBits 12 (cubeAddr642 zA zB zC) (c2In12Idx i) = basisBits 2 zC i := by
  rw [_root_.basisBits_eq_div_mod, _root_.basisBits_eq_div_mod]
  refine congrArg ((↑) : ℕ → ZMod 2) ?_
  have hzA : zA.val < 64 := zA.isLt
  have hzB : zB.val < 16 := zB.isLt
  have hzC : zC.val < 4 := zC.isLt
  rcases i with ⟨_ | _ | _, hi⟩
  · dsimp [cubeAddr642, c2In12Idx]; omega
  · dsimp only [c2In12Idx]
    rw [show (2 ^ 11 : ℕ) = 32 * 64 from rfl, ← Nat.div_div_eq_div_mul, cubeAddr642_div32,
      Nat.add_mul_div_left _ _ (by decide : 0 < 64), Nat.div_eq_of_lt hzA, zero_add, Nat.pow_one]
  · omega

private theorem symm12_eq_cubeAddr642 (x : Fin 12 → ZMod 2) :
    (basisBits 12).symm x =
      cubeAddr642
        ((basisBits 6).symm (fun i ↦ x ⟨5 + i.val, by omega⟩))
        ((basisBits 4).symm (fun i ↦ x ⟨1 + i.val, by omega⟩))
        ((basisBits 2).symm (fun i ↦ x (c2In12Idx i))) := by
  apply (basisBits 12).injective
  funext q
  rw [SelectSwapQROM.basisBits_symm]
  by_cases hq0 : q.val = 0
  · have hq : q = c2In12Idx ⟨0, by decide⟩ := Fin.ext hq0
    rw [hq, basisBits12_cubeAddr642_c]; dsimp; rw [SelectSwapQROM.basisBits_symm]
  · by_cases hq5 : q.val < 5
    · let i : Fin 4 := ⟨q.val - 1, by omega⟩
      have hq : q = ⟨1 + i.val, by omega⟩ := Fin.ext (by dsimp [i]; omega)
      rw [hq, basisBits12_cubeAddr642_b]; dsimp; rw [SelectSwapQROM.basisBits_symm]
    · by_cases hq11 : q.val < 11
      · let i : Fin 6 := ⟨q.val - 5, by omega⟩
        have hq : q = ⟨5 + i.val, by omega⟩ := Fin.ext (by dsimp [i]; omega)
        rw [hq, basisBits12_cubeAddr642_a]; dsimp; rw [SelectSwapQROM.basisBits_symm]
      · have hq11e : q.val = 11 := by have := q.isLt; omega
        have hq : q = c2In12Idx ⟨1, by decide⟩ := Fin.ext hq11e
        rw [hq, basisBits12_cubeAddr642_c]; dsimp; rw [SelectSwapQROM.basisBits_symm]

/-! ### Local `(4, 2)` ANF Linearity & Orthogonality Helpers -/

private theorem anfCoeffs_add2 (s : ℕ) :
    ∀ (f g : Fin (2 ^ s) → ZMod 2) (m : Fin (2 ^ s)),
      SelectSwapQROM.anfCoeffs s (fun u ↦ f u + g u) m =
        SelectSwapQROM.anfCoeffs s f m + SelectSwapQROM.anfCoeffs s g m := by
  induction s with
  | zero => intro _ _ _; rfl
  | succ s ih =>
      intro f g m; simp only [SelectSwapQROM.anfCoeffs]
      split_ifs with hm
      · exact ih _ _ _
      · refine (congrArg (fun h ↦ SelectSwapQROM.anfCoeffs s h _) (funext fun u ↦ ?_)).trans
          (ih _ _ _)
        ring

private theorem anfCoeffs_smul2 (s : ℕ) (c : ZMod 2) :
    ∀ (f : Fin (2 ^ s) → ZMod 2) (m : Fin (2 ^ s)),
      SelectSwapQROM.anfCoeffs s (fun u ↦ c * f u) m =
        c * SelectSwapQROM.anfCoeffs s f m := by
  induction s with
  | zero => intro _ _; rfl
  | succ s ih =>
      intro f m; simp only [SelectSwapQROM.anfCoeffs]
      split_ifs with hm
      · exact ih _ _
      · refine (congrArg (fun h ↦ SelectSwapQROM.anfCoeffs s h _) (funext fun u ↦ ?_)).trans
          (ih _ _)
        ring

private theorem anfCoeffs_zero_fn2 (s : ℕ) :
    ∀ (m : Fin (2 ^ s)), SelectSwapQROM.anfCoeffs s (fun _ ↦ (0 : ZMod 2)) m = 0 := by
  induction s with
  | zero => intro _; rfl
  | succ s ih =>
      intro m; simp only [SelectSwapQROM.anfCoeffs, add_zero]
      split_ifs <;> exact ih _

private theorem anfCoeffs_zero (s : ℕ) :
    ∀ (h : Fin (2 ^ s) → ZMod 2),
      SelectSwapQROM.anfCoeffs s h ⟨0, Nat.two_pow_pos s⟩ = h ⟨0, Nat.two_pow_pos s⟩ := by
  induction s with
  | zero => intro _; rfl
  | succ s ih =>
      intro h
      have h0 : (0 : ℕ) < 2 ^ s := Nat.two_pow_pos s
      simp only [SelectSwapQROM.anfCoeffs, h0, ↓reduceDIte]
      exact ih _

private theorem anfCoeffs_sum_fin2 (n s : ℕ) :
    ∀ (F : Fin n → Fin (2 ^ s) → ZMod 2) (m : Fin (2 ^ s)),
      SelectSwapQROM.anfCoeffs s (fun u ↦ ∑ i : Fin n, F i u) m =
        ∑ i : Fin n, SelectSwapQROM.anfCoeffs s (F i) m := by
  induction n with
  | zero => intro _ m; simp [anfCoeffs_zero_fn2]
  | succ n ih =>
      intro F m; simp_rw [Fin.sum_univ_castSucc]
      rw [anfCoeffs_add2, ih]

private theorem anfCoeffs_const_pos2 (s : ℕ) (c : ZMod 2) :
    ∀ (m : Fin (2 ^ s)), 0 < m.val → SelectSwapQROM.anfCoeffs s (fun _ ↦ c) m = 0 := by
  induction s with
  | zero => intro m hm; have := m.isLt; omega
  | succ s ih =>
      intro m hm; simp only [SelectSwapQROM.anfCoeffs]
      split_ifs with hlt
      · exact ih ⟨m.val, hlt⟩ hm
      · simp_rw [CharTwo.add_self_eq_zero]
        exact anfCoeffs_zero_fn2 s _

private theorem anfCoeffs_monoEval2_2 (m₀ m : Fin (2 ^ 2)) :
    SelectSwapQROM.anfCoeffs 2
      (fun z ↦ SelectSwapQROM.monoEval 2 (basisBits 2 z) m₀) m =
      if m = m₀ then 1 else 0 := by
  revert m₀ m; decide

private theorem anfCoeffs_monoEval4 (m₀ m : Fin (2 ^ 4)) :
    SelectSwapQROM.anfCoeffs 4
      (fun z ↦ SelectSwapQROM.monoEval 4 (basisBits 4 z) m₀) m =
      if m = m₀ then 1 else 0 := by
  revert m₀ m; decide

private theorem anfCoeffs4_optMono4_pos (jp : Option (Fin 14)) (uB : Fin 14) :
    SelectSwapQROM.anfCoeffs 4 (fun zB ↦ optMono4 zB jp) ⟨uB.val + 1, by omega⟩ =
      if jp = some uB then 1 else 0 := by
  revert jp uB; decide

private theorem anfCoeffs2_optMono2_pos2 (kp : Option (Fin 3)) (uC : Fin 3) :
    SelectSwapQROM.anfCoeffs 2 (fun zC ↦ optMono2 zC kp) ⟨uC.val + 1, by omega⟩ =
      if kp = some uC then 1 else 0 := by
  revert kp uC; decide

/-- Point indicator on `Fin (2 ^ 4)` for `anfCoeffs 4 _ 15`. -/
private def delta4Anf (z₀ z : Fin (2 ^ 4)) : ZMod 2 := if z = z₀ then 1 else 0

private theorem anfCoeffs4_delta4Anf_15 (z₀ : Fin (2 ^ 4)) :
    SelectSwapQROM.anfCoeffs 4 (delta4Anf z₀) ⟨15, by decide⟩ = 1 := by
  revert z₀; decide

private theorem anfCoeffs4_15_eq_sum (f : Fin (2 ^ 4) → ZMod 2) :
    SelectSwapQROM.anfCoeffs 4 f ⟨15, by decide⟩ = ∑ z₀ : Fin (2 ^ 4), f z₀ := by
  have hf : f = fun z ↦ ∑ z₀ : Fin (2 ^ 4), f z₀ * delta4Anf z₀ z :=
    funext fun z ↦ by simp [delta4Anf]
  conv_lhs => rw [hf]
  rw [anfCoeffs_sum_fin2 (2 ^ 4) 4 (fun z₀ z ↦ f z₀ * delta4Anf z₀ z)]
  refine Finset.sum_congr rfl fun z₀ _ ↦ ?_
  rw [anfCoeffs_smul2 4, anfCoeffs4_delta4Anf_15, mul_one]

private theorem anf_expand_1d2 (s : ℕ) (f : Fin (2 ^ s) → ZMod 2) (z : Fin (2 ^ s)) :
    f z = ∑ m : Fin (2 ^ s),
      SelectSwapQROM.anfCoeffs s f m * SelectSwapQROM.monoEval s (basisBits s z) m := by
  have h := (SelectSwapQROM.sum_anfCoeffs_mul_monoEval s f (basisBits s z)).symm
  rwa [SelectSwapQROM.symm_basisBits] at h

/-- `2D` `(4, 2)` ANF coefficients with `anfCoeffs 4` innermost. -/
def anf2DCoeffs42 (g : Fin (2 ^ 4) → Fin (2 ^ 2) → ZMod 2)
    (mB : Fin (2 ^ 4)) (mC : Fin (2 ^ 2)) : ZMod 2 :=
  SelectSwapQROM.anfCoeffs 2
    (fun zC ↦ SelectSwapQROM.anfCoeffs 4 (fun zB ↦ g zB zC) mB) mC

private theorem anf2DCoeffs42_add (f g : Fin (2 ^ 4) → Fin (2 ^ 2) → ZMod 2)
    (mB : Fin (2 ^ 4)) (mC : Fin (2 ^ 2)) :
    anf2DCoeffs42 (fun zB zC ↦ f zB zC + g zB zC) mB mC =
      anf2DCoeffs42 f mB mC + anf2DCoeffs42 g mB mC := by
  dsimp only [anf2DCoeffs42]
  have h1 (zC : Fin (2 ^ 2)) :=
    anfCoeffs_add2 4 (fun zB ↦ f zB zC) (fun zB ↦ g zB zC) mB
  simp_rw [h1]
  exact anfCoeffs_add2 2 _ _ mC

private theorem anf2DCoeffs42_sum_fin (n : ℕ) :
    ∀ (F : Fin n → Fin (2 ^ 4) → Fin (2 ^ 2) → ZMod 2)
      (mB : Fin (2 ^ 4)) (mC : Fin (2 ^ 2)),
      anf2DCoeffs42 (fun zB zC ↦ ∑ t : Fin n, F t zB zC) mB mC =
        ∑ t : Fin n, anf2DCoeffs42 (F t) mB mC := by
  induction n with
  | zero =>
      intro _ mB mC; dsimp only [anf2DCoeffs42]
      simp_rw [Fin.sum_univ_zero, anfCoeffs_zero_fn2]
  | succ n ih =>
      intro F mB mC; simp_rw [Fin.sum_univ_castSucc]
      rw [anf2DCoeffs42_add, ih]

private theorem anf2DCoeffs42_sep (fB : Fin (2 ^ 4) → ZMod 2) (fC : Fin (2 ^ 2) → ZMod 2)
    (mB : Fin (2 ^ 4)) (mC : Fin (2 ^ 2)) :
    anf2DCoeffs42 (fun zB zC ↦ fB zB * fC zC) mB mC =
      SelectSwapQROM.anfCoeffs 4 fB mB * SelectSwapQROM.anfCoeffs 2 fC mC := by
  dsimp only [anf2DCoeffs42]
  have h1 (zC : Fin (2 ^ 2)) :
      SelectSwapQROM.anfCoeffs 4 (fun zB ↦ fB zB * fC zC) mB =
        fC zC * SelectSwapQROM.anfCoeffs 4 fB mB := by
    have hf : (fun zB ↦ fB zB * fC zC) = (fun zB ↦ fC zC * fB zB) :=
      funext fun _ ↦ mul_comm _ _
    rw [hf, anfCoeffs_smul2 4]
  simp_rw [h1]
  have h2 : (fun zC ↦ fC zC * SelectSwapQROM.anfCoeffs 4 fB mB) =
      (fun zC ↦ SelectSwapQROM.anfCoeffs 4 fB mB * fC zC) :=
    funext fun _ ↦ mul_comm _ _
  rw [h2, anfCoeffs_smul2 2]

private theorem split_pow4_14 (f : Fin (2 ^ 4) → ZMod 2) :
    (∑ m : Fin (2 ^ 4), f m) =
      f ⟨0, by decide⟩ + (∑ u : Fin 14, f ⟨u.val + 1, by omega⟩) + f ⟨15, by decide⟩ := by
  let e : Fin (2 ^ 4) ≃ Fin ((14 + 1) + 1) := finCongr rfl
  rw [← Equiv.sum_comp e.symm, Fin.sum_univ_succ, Fin.sum_univ_castSucc, ← add_assoc]
  rfl

private theorem split_pow2_3_2 (f : Fin (2 ^ 2) → ZMod 2) :
    (∑ m : Fin (2 ^ 2), f m) =
      f ⟨0, by decide⟩ + ∑ u : Fin 3, f ⟨u.val + 1, by omega⟩ := by
  let e : Fin (2 ^ 2) ≃ Fin (3 + 1) := finCongr rfl
  rw [← Equiv.sum_comp e.symm, Fin.sum_univ_succ]
  rfl

/-! ### `14`-Step L-Tromino Cover of `Fin 14 × Fin 3` (`canonLeg4_642`) -/

/-- Exact `14`-step L-triple partition of `Fin 14 × Fin 3` avoiding XOR `15` on `B`. -/
def canonLeg4_642 : Fin 14 → Fin 14 × Fin 3 × Option (Fin 14) × Option (Fin 3)
  | ⟨0, _⟩  => (⟨0, by decide⟩,  ⟨0, by decide⟩, some ⟨1, by decide⟩,  some ⟨1, by decide⟩)
  | ⟨1, _⟩  => (⟨1, by decide⟩,  ⟨2, by decide⟩, some ⟨0, by decide⟩,  some ⟨1, by decide⟩)
  | ⟨2, _⟩  => (⟨2, by decide⟩,  ⟨0, by decide⟩, some ⟨5, by decide⟩,  some ⟨1, by decide⟩)
  | ⟨3, _⟩  => (⟨5, by decide⟩,  ⟨2, by decide⟩, some ⟨2, by decide⟩,  some ⟨1, by decide⟩)
  | ⟨4, _⟩  => (⟨4, by decide⟩,  ⟨0, by decide⟩, some ⟨6, by decide⟩,  some ⟨1, by decide⟩)
  | ⟨5, _⟩  => (⟨6, by decide⟩,  ⟨2, by decide⟩, some ⟨4, by decide⟩,  some ⟨1, by decide⟩)
  | ⟨6, _⟩  => (⟨3, by decide⟩,  ⟨0, by decide⟩, some ⟨11, by decide⟩, some ⟨1, by decide⟩)
  | ⟨7, _⟩  => (⟨11, by decide⟩, ⟨2, by decide⟩, some ⟨3, by decide⟩,  some ⟨1, by decide⟩)
  | ⟨8, _⟩  => (⟨7, by decide⟩,  ⟨0, by decide⟩, some ⟨10, by decide⟩, some ⟨1, by decide⟩)
  | ⟨9, _⟩  => (⟨10, by decide⟩, ⟨2, by decide⟩, some ⟨7, by decide⟩,  some ⟨1, by decide⟩)
  | ⟨10, _⟩ => (⟨8, by decide⟩,  ⟨0, by decide⟩, some ⟨12, by decide⟩, some ⟨1, by decide⟩)
  | ⟨11, _⟩ => (⟨12, by decide⟩, ⟨2, by decide⟩, some ⟨8, by decide⟩,  some ⟨1, by decide⟩)
  | ⟨12, _⟩ => (⟨9, by decide⟩,  ⟨0, by decide⟩, some ⟨13, by decide⟩, some ⟨1, by decide⟩)
  | ⟨13, _⟩ => (⟨13, by decide⟩, ⟨2, by decide⟩, some ⟨9, by decide⟩,  some ⟨1, by decide⟩)
  | ⟨_ + 14, h⟩ => absurd h (by omega)

theorem canonLeg4_642_j_ne_jp (t : Fin 14) :
    ∀ j' : Fin 14, (canonLeg4_642 t).2.2.1 = some j' → (canonLeg4_642 t).1 ≠ j' := by
  revert t; decide

theorem canonLeg4_642_k_ne_kp (t : Fin 14) :
    ∀ k' : Fin 3, (canonLeg4_642 t).2.2.2 = some k' → (canonLeg4_642 t).2.1 ≠ k' := by
  revert t; decide

/-- `ZMod 2` indicator of the `3` pairs in `Fin 14 × Fin 3` covered by step `t : Fin 14`. -/
def stepCoverZMod642 (t : Fin 14) (uB : Fin 14) (uC : Fin 3) : ZMod 2 :=
  let s := canonLeg4_642 t
  (if uB = s.1 ∧ uC = s.2.1 then 1 else 0) +
  (if s.2.2.1 = some uB ∧ uC = s.2.1 then 1 else 0) +
  (if uB = s.1 ∧ s.2.2.2 = some uC then 1 else 0)

private theorem sum_stepCoverZMod642_eq_one (uB : Fin 14) (uC : Fin 3) :
    (∑ t : Fin 14, stepCoverZMod642 t uB uC) = 1 := by
  revert uB uC; decide

/-- Cubic background phase term `b_j(zB) * g_k(zC) * (bp_{jp}(zB) + gp_{kp}(zC))` at step `t`. -/
def bg642Cube (t : Fin 14) (zB : Fin (2 ^ 4)) (zC : Fin (2 ^ 2)) : ZMod 2 :=
  let j := (canonLeg4_642 t).1
  let k := (canonLeg4_642 t).2.1
  let jp := (canonLeg4_642 t).2.2.1
  let kp := (canonLeg4_642 t).2.2.2
  SelectSwapQROM.monoEval 4 (basisBits 4 zB) ⟨j.val + 1, by omega⟩ *
    SelectSwapQROM.monoEval 2 (basisBits 2 zC) ⟨k.val + 1, by omega⟩ *
    (optMono4 zB jp + optMono2 zC kp)

/-- Sum of the `14` slice-independent cubic background terms `bg642Cube t`. -/
def bg642Sum (zB : Fin (2 ^ 4)) (zC : Fin (2 ^ 2)) : ZMod 2 :=
  ∑ t : Fin 14, bg642Cube t zB zC

/-- `2D` bilinear `CZ` coefficients cancelling `bg642Sum` on `rZ14 × rAllC` (`0 T`). -/
def bg642Coeff (uB : Fin 14) (uC : Fin 3) : ZMod 2 :=
  anf2DCoeffs42 bg642Sum ⟨uB.val + 1, by omega⟩ ⟨uC.val + 1, by omega⟩

private theorem bg642Sum_zero_left (zC : Fin (2 ^ 2)) :
    bg642Sum ⟨0, by decide⟩ zC = 0 := by
  revert zC; decide

private theorem bg642Sum_zero_right (zB : Fin (2 ^ 4)) :
    bg642Sum zB ⟨0, by decide⟩ = 0 := by
  revert zB; decide

private theorem sum_zB_bg642Cube_eq_zero (t : Fin 14) (zC : Fin (2 ^ 2)) :
    (∑ zB : Fin (2 ^ 4), bg642Cube t zB zC) = 0 := by
  revert t zC; decide

private theorem bg642Sum_eq_bilinear (zB : Fin (2 ^ 4)) (zC : Fin (2 ^ 2)) :
    bg642Sum zB zC =
      ∑ uB : Fin 14, SelectSwapQROM.monoEval 4 (basisBits 4 zB) ⟨uB.val + 1, by omega⟩ *
        ∑ uC : Fin 3, bg642Coeff uB uC *
          SelectSwapQROM.monoEval 2 (basisBits 2 zC) ⟨uC.val + 1, by omega⟩ := by
  refine ((anf_expand_1d2 4 (fun y ↦ bg642Sum y zC) zB).trans (split_pow4_14 _)).trans ?_
  have h0B : SelectSwapQROM.anfCoeffs 4 (fun y ↦ bg642Sum y zC) ⟨0, by decide⟩ = 0 :=
    (anfCoeffs_zero 4 (fun y ↦ bg642Sum y zC)).trans (bg642Sum_zero_left zC)
  have h15B : SelectSwapQROM.anfCoeffs 4 (fun y ↦ bg642Sum y zC) ⟨15, by decide⟩ = 0 := by
    rw [anfCoeffs4_15_eq_sum]
    dsimp only [bg642Sum]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun t _ ↦ sum_zB_bg642Cube_eq_zero t zC
  rw [h0B, zero_mul, zero_add, h15B, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun uB _ ↦ ?_
  rw [mul_comm (SelectSwapQROM.anfCoeffs 4 _ _)]
  refine congrArg (SelectSwapQROM.monoEval 4 (basisBits 4 zB) ⟨uB.val + 1, by omega⟩ * ·) ?_
  refine ((anf_expand_1d2 2
    (fun w ↦ SelectSwapQROM.anfCoeffs 4 (fun y ↦ bg642Sum y w) ⟨uB.val + 1, by omega⟩) zC).trans
    (split_pow2_3_2 _)).trans ?_
  have h0C :
      SelectSwapQROM.anfCoeffs 2
        (fun w ↦ SelectSwapQROM.anfCoeffs 4 (fun y ↦ bg642Sum y w) ⟨uB.val + 1, by omega⟩)
        ⟨0, by decide⟩ = 0 := by
    refine (anfCoeffs_zero 2 _).trans ?_
    change SelectSwapQROM.anfCoeffs 4
      (fun y ↦ bg642Sum y ⟨0, Nat.two_pow_pos 2⟩) ⟨uB.val + 1, by omega⟩ = 0
    have hfn : (fun y ↦ bg642Sum y ⟨0, Nat.two_pow_pos 2⟩) = fun _ ↦ (0 : ZMod 2) :=
      funext fun y ↦ bg642Sum_zero_right y
    rw [hfn, anfCoeffs_zero_fn2 4]
  rw [h0C, zero_mul, zero_add]
  rfl

/-- Per-slice L-step masks `(c1, c2, c3)` on `Fin 64` (`zA`) for step `t : Fin 14`. -/
def leg642Masks (P_slice : Fin (2 ^ 6) → Fin (2 ^ 4) → Fin (2 ^ 2) → ZMod 2)
    (t : Fin 14) : (Fin (2 ^ 6) → ZMod 2) × (Fin (2 ^ 6) → ZMod 2) × (Fin (2 ^ 6) → ZMod 2) :=
  let j := (canonLeg4_642 t).1
  let k := (canonLeg4_642 t).2.1
  let jp := (canonLeg4_642 t).2.2.1
  let kp := (canonLeg4_642 t).2.2.2
  (fun c ↦ match jp with
    | none => 0
    | some j' => anf2DCoeffs42 (P_slice c) ⟨j'.val + 1, by omega⟩ ⟨k.val + 1, by omega⟩,
   fun c ↦ match kp with
    | none => 0
    | some k' => anf2DCoeffs42 (P_slice c) ⟨j.val + 1, by omega⟩ ⟨k'.val + 1, by omega⟩,
   fun c ↦ anf2DCoeffs42 (P_slice c) ⟨j.val + 1, by omega⟩ ⟨k.val + 1, by omega⟩)

/-- Per-slice residual phase term at step `t` after subtracting `bg642Cube t`. -/
def lin642Term (a1 a2 a3 : ZMod 2) (t : Fin 14) (zB : Fin (2 ^ 4)) (zC : Fin (2 ^ 2)) : ZMod 2 :=
  let j := (canonLeg4_642 t).1
  let k := (canonLeg4_642 t).2.1
  let jp := (canonLeg4_642 t).2.2.1
  let kp := (canonLeg4_642 t).2.2.2
  (SelectSwapQROM.monoEval 4 (basisBits 4 zB) ⟨j.val + 1, by omega⟩ + a1) *
    (SelectSwapQROM.monoEval 2 (basisBits 2 zC) ⟨k.val + 1, by omega⟩ + a2) *
    (a3 + optMono4 zB jp + optMono2 zC kp) +
  bg642Cube t zB zC

private theorem sum_zB_canon642_b (t : Fin 14) :
    (∑ zB : Fin (2 ^ 4),
      SelectSwapQROM.monoEval 4 (basisBits 4 zB)
        ⟨(canonLeg4_642 t).1.val + 1, by omega⟩) = 0 := by
  revert t; decide

private theorem sum_zB_canon642_bp (t : Fin 14) :
    (∑ zB : Fin (2 ^ 4), optMono4 zB (canonLeg4_642 t).2.2.1) = 0 := by
  revert t; decide

private theorem sum_zB_canon642_b_bp (t : Fin 14) :
    (∑ zB : Fin (2 ^ 4),
      SelectSwapQROM.monoEval 4 (basisBits 4 zB)
        ⟨(canonLeg4_642 t).1.val + 1, by omega⟩ *
        optMono4 zB (canonLeg4_642 t).2.2.1) = 0 := by
  revert t; decide

private theorem sum_fin16_const_zmod2 (c : ZMod 2) :
    (∑ _ : Fin (2 ^ 4), c) = 0 := by
  revert c; decide

private theorem lin642_poly_decomp (b bp g gp a1 a2 a3 : ZMod 2) :
    (b + a1) * (g + a2) * (a3 + bp + gp) + b * g * (bp + gp) =
      (g + g + a2) * (b * bp) +
      (g * a3 + (g + g) * gp + a2 * (a3 + gp)) * b +
      (a1 * (g + a2)) * bp +
      a1 * (g + a2) * (a3 + gp) := by
  ring

private theorem anf2DCoeffs42_lin642Term_15 (a1 a2 a3 : ZMod 2) (t : Fin 14)
    (mC : Fin (2 ^ 2)) :
    anf2DCoeffs42 (lin642Term a1 a2 a3 t) ⟨15, by decide⟩ mC = 0 := by
  dsimp only [anf2DCoeffs42]
  have hIn (zC : Fin (2 ^ 2)) :
      SelectSwapQROM.anfCoeffs 4
        (fun zB ↦ lin642Term a1 a2 a3 t zB zC) ⟨15, by decide⟩ = 0 := by
    rw [anfCoeffs4_15_eq_sum]
    let g := SelectSwapQROM.monoEval 2 (basisBits 2 zC)
      ⟨(canonLeg4_642 t).2.1.val + 1, by omega⟩
    let gp := optMono2 zC (canonLeg4_642 t).2.2.2
    have hTerm (zB : Fin (2 ^ 4)) :
        lin642Term a1 a2 a3 t zB zC =
          (g + g + a2) *
            (SelectSwapQROM.monoEval 4 (basisBits 4 zB)
              ⟨(canonLeg4_642 t).1.val + 1, by omega⟩ *
              optMono4 zB (canonLeg4_642 t).2.2.1) +
          (g * a3 + (g + g) * gp + a2 * (a3 + gp)) *
            SelectSwapQROM.monoEval 4 (basisBits 4 zB)
              ⟨(canonLeg4_642 t).1.val + 1, by omega⟩ +
          (a1 * (g + a2)) * optMono4 zB (canonLeg4_642 t).2.2.1 +
          a1 * (g + a2) * (a3 + gp) := by
      dsimp only [lin642Term, bg642Cube, g, gp]
      exact lin642_poly_decomp _ _ _ _ _ _ _
    simp_rw [hTerm, Finset.sum_add_distrib, sum_fin16_const_zmod2, ← Finset.mul_sum,
      sum_zB_canon642_b_bp t, sum_zB_canon642_b t, sum_zB_canon642_bp t,
      mul_zero, add_zero]
  simp_rw [hIn]
  exact anfCoeffs_zero_fn2 2 mC

private theorem lStep_zmod2_decomp2 (b g a1 a2 a3 bp gp : ZMod 2) :
    (b + a1) * (g + a2) * (a3 + bp + gp) =
      ((a3 * b * g + a1 * bp * g) + a2 * b * gp) +
      ((b * g * (bp + gp) + (b * (a3 + bp) + a1 * bp) * a2) +
       a1 * (g + a2) * (a3 + gp)) := by
  ring

private theorem anf2DCoeffs42_lin642Term_bilinear
    (P_slice : Fin (2 ^ 6) → Fin (2 ^ 4) → Fin (2 ^ 2) → ZMod 2) (c : Fin (2 ^ 6))
    (t : Fin 14) (uB : Fin 14) (uC : Fin 3) :
    let msk := leg642Masks P_slice t
    anf2DCoeffs42 (lin642Term (msk.1 c) (msk.2.1 c) (msk.2.2 c) t)
      ⟨uB.val + 1, by omega⟩ ⟨uC.val + 1, by omega⟩ =
      stepCoverZMod642 t uB uC *
        anf2DCoeffs42 (P_slice c) ⟨uB.val + 1, by omega⟩ ⟨uC.val + 1, by omega⟩ := by
  intro msk
  let a1 := msk.1 c; let a2 := msk.2.1 c; let a3 := msk.2.2 c
  let b (zB : Fin (2 ^ 4)) :=
    SelectSwapQROM.monoEval 4 (basisBits 4 zB) ⟨(canonLeg4_642 t).1.val + 1, by omega⟩
  let bp (zB : Fin (2 ^ 4)) := optMono4 zB (canonLeg4_642 t).2.2.1
  let g (zC : Fin (2 ^ 2)) :=
    SelectSwapQROM.monoEval 2 (basisBits 2 zC) ⟨(canonLeg4_642 t).2.1.val + 1, by omega⟩
  let gp (zC : Fin (2 ^ 2)) := optMono2 zC (canonLeg4_642 t).2.2.2
  let mB : Fin (2 ^ 4) := ⟨uB.val + 1, by omega⟩
  let mC : Fin (2 ^ 2) := ⟨uC.val + 1, by omega⟩
  have hDecomp : lin642Term a1 a2 a3 t = fun zB zC ↦
      ((a3 * b zB) * g zC + (a1 * bp zB) * g zC + (a2 * b zB) * gp zC) +
      ((b zB * (a3 + bp zB) + a1 * bp zB) * a2) +
      (a1 * (g zC + a2) * (a3 + gp zC)) := by
    funext zB zC
    dsimp only [lin642Term, bg642Cube, b, bp, g, gp]
    have hL := lStep_zmod2_decomp2 (b zB) (g zC) a1 a2 a3 (bp zB) (gp zC)
    rw [hL]
    have hR (x y z w : ZMod 2) : x + ((y + z) + w) + y = (y + y) + (x + z + w) := by ring
    rw [hR, CharTwo.add_self_eq_zero, zero_add]
  rw [hDecomp, anf2DCoeffs42_add, anf2DCoeffs42_add, anf2DCoeffs42_add, anf2DCoeffs42_add]
  have hzC : anf2DCoeffs42 (fun zB _ ↦ (b zB * (a3 + bp zB) + a1 * bp zB) * a2) mB mC = 0 :=
    anfCoeffs_const_pos2 2 _ mC (by dsimp [mC]; omega)
  have hzB : anf2DCoeffs42 (fun _ zC ↦ a1 * (g zC + a2) * (a3 + gp zC)) mB mC = 0 := by
    dsimp only [anf2DCoeffs42]
    have h0 (zC : Fin (2 ^ 2)) :
        SelectSwapQROM.anfCoeffs 4
          (fun _ ↦ a1 * (g zC + a2) * (a3 + gp zC)) mB = 0 :=
      anfCoeffs_const_pos2 4 _ mB (by dsimp [mB]; omega)
    simp_rw [h0]; exact anfCoeffs_zero_fn2 2 mC
  rw [hzC, hzB, add_zero, add_zero, anf2DCoeffs42_sep, anf2DCoeffs42_sep, anf2DCoeffs42_sep,
    anfCoeffs_smul2 4, anfCoeffs_smul2 4, anfCoeffs_smul2 4]
  dsimp only [b, bp, g, gp, mB, mC]
  rw [anfCoeffs_monoEval4, anfCoeffs_monoEval2_2, anfCoeffs4_optMono4_pos,
    anfCoeffs2_optMono2_pos2]
  have hbEq : ((⟨uB.val + 1, by omega⟩ : Fin 16) = ⟨(canonLeg4_642 t).1.val + 1, by omega⟩) ↔
      uB = (canonLeg4_642 t).1 :=
    ⟨fun h ↦ Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega), fun h ↦ by subst h; rfl⟩
  have hgEq : ((⟨uC.val + 1, by omega⟩ : Fin 4) = ⟨(canonLeg4_642 t).2.1.val + 1, by omega⟩) ↔
      uC = (canonLeg4_642 t).2.1 :=
    ⟨fun h ↦ Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega), fun h ↦ by subst h; rfl⟩
  simp only [hbEq, hgEq]
  have hT1 : a3 * (if uB = (canonLeg4_642 t).1 then 1 else 0) *
      (if uC = (canonLeg4_642 t).2.1 then 1 else 0) =
      (if uB = (canonLeg4_642 t).1 ∧ uC = (canonLeg4_642 t).2.1 then 1 else 0) *
        anf2DCoeffs42 (P_slice c) ⟨uB.val + 1, by omega⟩ ⟨uC.val + 1, by omega⟩ := by
    dsimp only [a3, msk, leg642Masks]
    by_cases hB : uB = (canonLeg4_642 t).1 <;> by_cases hC : uC = (canonLeg4_642 t).2.1 <;>
      simp [hB, hC, mul_comm]
  have hT2 : a1 * (if (canonLeg4_642 t).2.2.1 = some uB then 1 else 0) *
      (if uC = (canonLeg4_642 t).2.1 then 1 else 0) =
      (if (canonLeg4_642 t).2.2.1 = some uB ∧ uC = (canonLeg4_642 t).2.1 then 1 else 0) *
        anf2DCoeffs42 (P_slice c) ⟨uB.val + 1, by omega⟩ ⟨uC.val + 1, by omega⟩ := by
    dsimp only [a1, msk, leg642Masks]
    cases hjp : (canonLeg4_642 t).2.2.1 with
    | none => simp
    | some j' =>
      by_cases hj' : j' = uB <;> by_cases hC : uC = (canonLeg4_642 t).2.1 <;>
        simp [hj', hC, mul_comm]
  have hT3 : a2 * (if uB = (canonLeg4_642 t).1 then 1 else 0) *
      (if (canonLeg4_642 t).2.2.2 = some uC then 1 else 0) =
      (if uB = (canonLeg4_642 t).1 ∧ (canonLeg4_642 t).2.2.2 = some uC then 1 else 0) *
        anf2DCoeffs42 (P_slice c) ⟨uB.val + 1, by omega⟩ ⟨uC.val + 1, by omega⟩ := by
    dsimp only [a2, msk, leg642Masks]
    cases hkp : (canonLeg4_642 t).2.2.2 with
    | none => simp
    | some k' =>
      by_cases hB : uB = (canonLeg4_642 t).1 <;> by_cases hk' : k' = uC <;>
        simp [hB, hk', mul_comm]
  rw [hT1, hT2, hT3]
  dsimp only [stepCoverZMod642]; ring

private theorem anf2DCoeffs42_def (g : Fin (2 ^ 4) → Fin (2 ^ 2) → ZMod 2)
    (mB : Fin (2 ^ 4)) (mC : Fin (2 ^ 2)) :
    anf2DCoeffs42 g mB mC =
      SelectSwapQROM.anfCoeffs 2
        (fun zC ↦ SelectSwapQROM.anfCoeffs 4 (fun zB ↦ g zB zC) mB) mC := rfl

attribute [irreducible] anf2DCoeffs42 leg642Masks bg642Coeff

/-- Residual `(4, 2)` phase slice on `c : Fin 64` after `14` L-steps + `bg642Sum`. -/
def hotRes642Cube (P_slice : Fin (2 ^ 6) → Fin (2 ^ 4) → Fin (2 ^ 2) → ZMod 2)
    (c : Fin (2 ^ 6)) (zB : Fin (2 ^ 4)) (zC : Fin (2 ^ 2)) : ZMod 2 :=
  P_slice c zB zC +
    ∑ t : Fin 14,
      let msk := leg642Masks P_slice t
      lin642Term (msk.1 c) (msk.2.1 c) (msk.2.2 c) t zB zC

private theorem anf2DCoeffs42_hotRes642Cube_15
    (P_slice : Fin (2 ^ 6) → Fin (2 ^ 4) → Fin (2 ^ 2) → ZMod 2)
    (c : Fin (2 ^ 6)) (hSum0 : ∀ zC : Fin (2 ^ 2), (∑ zB : Fin (2 ^ 4), P_slice c zB zC) = 0)
    (mC : Fin (2 ^ 2)) :
    anf2DCoeffs42 (hotRes642Cube P_slice c) ⟨15, by decide⟩ mC = 0 := by
  change anf2DCoeffs42
    (fun zB zC ↦ P_slice c zB zC +
      ∑ t : Fin 14,
        lin642Term ((leg642Masks P_slice t).1 c) ((leg642Masks P_slice t).2.1 c)
          ((leg642Masks P_slice t).2.2 c) t zB zC)
    ⟨15, by decide⟩ mC = 0
  rw [anf2DCoeffs42_add, anf2DCoeffs42_sum_fin 14
    (fun t ↦ lin642Term ((leg642Masks P_slice t).1 c) ((leg642Masks P_slice t).2.1 c)
      ((leg642Masks P_slice t).2.2 c) t)]
  have hP : anf2DCoeffs42 (P_slice c) ⟨15, by decide⟩ mC = 0 := by
    rw [anf2DCoeffs42_def]
    have hIn (zC : Fin (2 ^ 2)) :
        SelectSwapQROM.anfCoeffs 4 (fun zB ↦ P_slice c zB zC) ⟨15, by decide⟩ = 0 := by
      rw [anfCoeffs4_15_eq_sum, hSum0 zC]
    simp_rw [hIn]
    exact anfCoeffs_zero_fn2 2 mC
  have hS : (∑ t : Fin 14,
      anf2DCoeffs42 (lin642Term ((leg642Masks P_slice t).1 c) ((leg642Masks P_slice t).2.1 c)
        ((leg642Masks P_slice t).2.2 c) t) ⟨15, by decide⟩ mC) = 0 := by
    refine Finset.sum_eq_zero fun t _ ↦ anf2DCoeffs42_lin642Term_15 _ _ _ t mC
  rw [hP, hS, add_zero]

private theorem anf2DCoeffs42_hotRes642Cube_bilinear
    (P_slice : Fin (2 ^ 6) → Fin (2 ^ 4) → Fin (2 ^ 2) → ZMod 2)
    (c : Fin (2 ^ 6)) (uB : Fin 14) (uC : Fin 3) :
    anf2DCoeffs42 (hotRes642Cube P_slice c) ⟨uB.val + 1, by omega⟩ ⟨uC.val + 1, by omega⟩ = 0 := by
  change anf2DCoeffs42
    (fun zB zC ↦ P_slice c zB zC +
      ∑ t : Fin 14,
        lin642Term ((leg642Masks P_slice t).1 c) ((leg642Masks P_slice t).2.1 c)
          ((leg642Masks P_slice t).2.2 c) t zB zC)
    ⟨uB.val + 1, by omega⟩ ⟨uC.val + 1, by omega⟩ = 0
  rw [anf2DCoeffs42_add, anf2DCoeffs42_sum_fin 14
    (fun t ↦ lin642Term ((leg642Masks P_slice t).1 c) ((leg642Masks P_slice t).2.1 c)
      ((leg642Masks P_slice t).2.2 c) t)]
  simp_rw [anf2DCoeffs42_lin642Term_bilinear P_slice c _ uB uC, ← Finset.sum_mul,
    sum_stepCoverZMod642_eq_one uB uC, one_mul, CharTwo.add_self_eq_zero]

private theorem anf2DCoeffs42_eval_residual (R : Fin (2 ^ 4) → Fin (2 ^ 2) → ZMod 2)
    (h15 : ∀ mC : Fin (2 ^ 2), anf2DCoeffs42 R ⟨15, by decide⟩ mC = 0)
    (hBi : ∀ (uB : Fin 14) (uC : Fin 3),
      anf2DCoeffs42 R ⟨uB.val + 1, by omega⟩ ⟨uC.val + 1, by omega⟩ = 0)
    (zB : Fin (2 ^ 4)) (zC : Fin (2 ^ 2)) :
    R zB zC =
      anf2DCoeffs42 R ⟨0, by decide⟩ ⟨0, by decide⟩ +
      (∑ uB : Fin 14, anf2DCoeffs42 R ⟨uB.val + 1, by omega⟩ ⟨0, by decide⟩ *
        SelectSwapQROM.monoEval 4 (basisBits 4 zB) ⟨uB.val + 1, by omega⟩) +
      (∑ uC : Fin 3, anf2DCoeffs42 R ⟨0, by decide⟩ ⟨uC.val + 1, by omega⟩ *
        SelectSwapQROM.monoEval 2 (basisBits 2 zC) ⟨uC.val + 1, by omega⟩) := by
  refine ((anf_expand_1d2 4 (fun y ↦ R y zC) zB).trans (split_pow4_14 _)).trans ?_
  have hm0B : SelectSwapQROM.monoEval 4 (basisBits 4 zB) ⟨0, by decide⟩ = 1 :=
    SelectSwapQROM.monoEval_zero 4 _
  have hm0C : SelectSwapQROM.monoEval 2 (basisBits 2 zC) ⟨0, by decide⟩ = 1 :=
    SelectSwapQROM.monoEval_zero 2 _
  have hExpC (mB : Fin (2 ^ 4)) :
      SelectSwapQROM.anfCoeffs 4 (fun y ↦ R y zC) mB =
        anf2DCoeffs42 R mB ⟨0, by decide⟩ +
          ∑ uC : Fin 3, anf2DCoeffs42 R mB ⟨uC.val + 1, by omega⟩ *
            SelectSwapQROM.monoEval 2 (basisBits 2 zC) ⟨uC.val + 1, by omega⟩ := by
    refine ((anf_expand_1d2 2
      (fun w ↦ SelectSwapQROM.anfCoeffs 4 (fun y ↦ R y w) mB) zC).trans
      (split_pow2_3_2 _)).trans ?_
    rw [hm0C, mul_one]
    simp_rw [← anf2DCoeffs42_def]
  have h15z : SelectSwapQROM.anfCoeffs 4 (fun y ↦ R y zC) ⟨15, by decide⟩ = 0 := by
    rw [hExpC ⟨15, by decide⟩, h15 ⟨0, by decide⟩, zero_add]
    refine Finset.sum_eq_zero fun uC _ ↦ by rw [h15 _, zero_mul]
  have hMid (uB : Fin 14) :
      SelectSwapQROM.anfCoeffs 4 (fun y ↦ R y zC) ⟨uB.val + 1, by omega⟩ =
        anf2DCoeffs42 R ⟨uB.val + 1, by omega⟩ ⟨0, by decide⟩ := by
    rw [hExpC ⟨uB.val + 1, by omega⟩]
    have hZ : (∑ uC : Fin 3, anf2DCoeffs42 R ⟨uB.val + 1, by omega⟩ ⟨uC.val + 1, by omega⟩ *
        SelectSwapQROM.monoEval 2 (basisBits 2 zC) ⟨uC.val + 1, by omega⟩) = 0 :=
      Finset.sum_eq_zero fun uC _ ↦ by rw [hBi uB uC, zero_mul]
    rw [hZ, add_zero]
  rw [hm0B, mul_one, h15z, zero_mul, add_zero, hExpC ⟨0, by decide⟩]
  simp_rw [hMid]
  ring

/-! ### `212-T` (`66 ≤ sScr`) `(6, 4, 2)` Cold QROM Unloader Circuit & Proof -/

private theorem option_map_eq_some {α β : Type*} {f : α → β} {o : Option α} {w : β}
    (h : o.map f = some w) : ∃ a, o = some a ∧ f a = w := by
  cases o with
  | none => cases h
  | some a => exact ⟨a, rfl, Option.some.inj h⟩

private theorem optWireBit_map_eq_optMono4 {N : ℕ} (γ : BitAssignment N) (r : QRegister 14 N)
    (zB : Fin (2 ^ 4))
    (h : ∀ u : Fin 14,
      γ (r u) = SelectSwapQROM.monoEval 4 (basisBits 4 zB) ⟨u.val + 1, by omega⟩)
    (jp : Option (Fin 14)) : optWireBit γ (jp.map r) = optMono4 zB jp := by
  cases jp with
  | none => rfl
  | some u => exact h u

private theorem optWireBit_map_eq_optMono2 {N : ℕ} (γ : BitAssignment N) (r : QRegister 3 N)
    (zC : Fin (2 ^ 2))
    (h : ∀ u : Fin 3,
      γ (r u) = SelectSwapQROM.monoEval 2 (basisBits 2 zC) ⟨u.val + 1, by omega⟩)
    (kp : Option (Fin 3)) : optWireBit γ (kp.map r) = optMono2 zC kp := by
  cases kp with
  | none => rfl
  | some u => exact h u

/-- Sequential `14`-step L-triple phase loop (`56 T`, `0 TOFF`, `1` clean ancilla `wAnc`) for
Leg 4. -/
def lStepLoop14 {Var : Type} {N : ℕ} (v : Var)
    (P_slice : Fin (2 ^ 6) → Fin (2 ^ 4) → Fin (2 ^ 2) → ZMod 2)
    (rHotA64 : QRegister (2 ^ 6) N) (rZ14 : QRegister 14 N) (rAllC : QRegister 3 N) (wAnc : Wire N)
    (hAB : rHotA64.DisjointWires rZ14) (hAC : rHotA64.DisjointWires rAllC)
    (hBC : rZ14.DisjointWires rAllC)
    (hAncA : ∀ c, wAnc ≠ rHotA64 c) (hAncB : ∀ j, wAnc ≠ rZ14 j) (hAncC : ∀ k, wAnc ≠ rAllC k) :
    (s : ℕ) → s ≤ 14 → DynamicCircuit Var N
  | 0, _ => .identity
  | s + 1, hs =>
      let t : Fin 14 := ⟨s, hs⟩
      let j := (canonLeg4_642 t).1
      let k := (canonLeg4_642 t).2.1
      let jp := (canonLeg4_642 t).2.2.1
      let kp := (canonLeg4_642 t).2.2.2
      let msk := leg642Masks P_slice t
      .seq (lStepLoop14 v P_slice rHotA64 rZ14 rAllC wAnc hAB hAC hBC hAncA hAncB hAncC s
          (Nat.le_of_lt hs))
        (lStepInPlaceDyn v rHotA64 (rZ14 j) (rAllC k) wAnc (jp.map rZ14) (kp.map rAllC)
          msk.1 msk.2.1 msk.2.2
          (hBC.ne j k) (hAncB j).symm (hAncC k).symm
          (fun c ↦ hAB.ne c j) (fun c ↦ hAC.ne c k) hAncA
          (option_map_ne_of_ne rZ14 jp wAnc hAncB)
          (option_map_ne_of_ne rAllC kp wAnc hAncC))

private theorem count_lStepLoop14_toff {Var : Type} {N : ℕ} (v : Var)
    (P_slice : Fin (2 ^ 6) → Fin (2 ^ 4) → Fin (2 ^ 2) → ZMod 2)
    (rHotA64 : QRegister (2 ^ 6) N) (rZ14 : QRegister 14 N) (rAllC : QRegister 3 N) (wAnc : Wire N)
    (hAB : rHotA64.DisjointWires rZ14) (hAC : rHotA64.DisjointWires rAllC)
    (hBC : rZ14.DisjointWires rAllC)
    (hAncA : ∀ c, wAnc ≠ rHotA64 c) (hAncB : ∀ j, wAnc ≠ rZ14 j) (hAncC : ∀ k, wAnc ≠ rAllC k)
    (s : ℕ) (hs : s ≤ 14) :
    (lStepLoop14 v P_slice rHotA64 rZ14 rAllC wAnc hAB hAC hBC hAncA hAncB hAncC s hs).count
      .TOFF = 0 := by
  induction s with
  | zero => rfl
  | succ s ih =>
      dsimp only [lStepLoop14, DynamicCircuit.count]
      rw [ih (Nat.le_of_lt hs), count_lStepInPlaceDyn_toff, add_zero]

private theorem count_lStepLoop14_t {Var : Type} {N : ℕ} (v : Var)
    (P_slice : Fin (2 ^ 6) → Fin (2 ^ 4) → Fin (2 ^ 2) → ZMod 2)
    (rHotA64 : QRegister (2 ^ 6) N) (rZ14 : QRegister 14 N) (rAllC : QRegister 3 N) (wAnc : Wire N)
    (hAB : rHotA64.DisjointWires rZ14) (hAC : rHotA64.DisjointWires rAllC)
    (hBC : rZ14.DisjointWires rAllC)
    (hAncA : ∀ c, wAnc ≠ rHotA64 c) (hAncB : ∀ j, wAnc ≠ rZ14 j) (hAncC : ∀ k, wAnc ≠ rAllC k)
    (s : ℕ) (hs : s ≤ 14) :
    (lStepLoop14 v P_slice rHotA64 rZ14 rAllC wAnc hAB hAC hBC hAncA hAncB hAncC s hs).count .T =
      4 * s := by
  induction s with
  | zero => rfl
  | succ s ih =>
      dsimp only [lStepLoop14, DynamicCircuit.count]
      rw [ih (Nat.le_of_lt hs), count_lStepInPlaceDyn_t]; omega

/-- Single-step ket phase polynomial for step `t : Fin 14` of `lStepLoop14`. -/
private def lStep642KetPhase {N : ℕ}
    (P_slice : Fin (2 ^ 6) → Fin (2 ^ 4) → Fin (2 ^ 2) → ZMod 2)
    (rHotA64 : QRegister (2 ^ 6) N) (rZ14 : QRegister 14 N) (rAllC : QRegister 3 N) (t : Fin 14)
    (γ : BitAssignment N) : ZMod 2 :=
  let j := (canonLeg4_642 t).1
  let k := (canonLeg4_642 t).2.1
  let jp := (canonLeg4_642 t).2.2.1
  let kp := (canonLeg4_642 t).2.2.2
  let msk := leg642Masks P_slice t
  lStepPhase rHotA64 (rZ14 j) (rAllC k) (jp.map rZ14) (kp.map rAllC) msk.1 msk.2.1 msk.2.2 γ

private theorem cleanRealizesSet_lStepLoop14 {Var : Type} [Fintype Var] [DecidableEq Var]
    {N : ℕ} [NeZero (2 ^ N)] (v : Var) (S₀ : Finset (Wire N))
    (P_slice : Fin (2 ^ 6) → Fin (2 ^ 4) → Fin (2 ^ 2) → ZMod 2)
    (rHotA64 : QRegister (2 ^ 6) N) (rZ14 : QRegister 14 N) (rAllC : QRegister 3 N) (wAnc : Wire N)
    (hAB : rHotA64.DisjointWires rZ14) (hAC : rHotA64.DisjointWires rAllC)
    (hBC : rZ14.DisjointWires rAllC)
    (hAncA : ∀ c, wAnc ≠ rHotA64 c) (hAncB : ∀ j, wAnc ≠ rZ14 j) (hAncC : ∀ k, wAnc ≠ rAllC k)
    (hAncS : wAnc ∈ S₀) (hBNotS : ∀ j, rZ14 j ∉ S₀) (hCNotS : ∀ k, rAllC k ∉ S₀)
    (s : ℕ) (hs : s ≤ 14) :
    SelectSwapQROM.CleanRealizesSet v S₀
      (diagKetUnitary (fun γ ↦ ∑ i : Fin s,
        lStep642KetPhase P_slice rHotA64 rZ14 rAllC ⟨i.val, Nat.lt_of_lt_of_le i.isLt hs⟩ γ))
      (lStepLoop14 v P_slice rHotA64 rZ14 rAllC wAnc hAB hAC hBC hAncA hAncB hAncC s hs) := by
  induction s with
  | zero =>
      dsimp only [lStepLoop14]; simp_rw [Fin.sum_univ_zero]
      rw [diagKetUnitary_zero]; exact SelectSwapQROM.CleanRealizesSet.identity v S₀
  | succ s ih =>
      dsimp only [lStepLoop14]
      let t : Fin 14 := ⟨s, hs⟩
      have hPrev := ih (Nat.le_of_lt hs)
      have hStep := cleanRealizesSet_lStepInPlaceDyn v S₀ rHotA64 (rZ14 (canonLeg4_642 t).1)
        (rAllC (canonLeg4_642 t).2.1) wAnc ((canonLeg4_642 t).2.2.1.map rZ14)
        ((canonLeg4_642 t).2.2.2.map rAllC) (leg642Masks P_slice t).1 (leg642Masks P_slice t).2.1
        (leg642Masks P_slice t).2.2 (hBC.ne _ _) (hAncB _).symm (hAncC _).symm
        (fun c ↦ hAB.ne c _) (fun c ↦ hAC.ne c _) hAncA
        (option_map_ne_of_ne rZ14 _ wAnc hAncB)
        (option_map_ne_of_ne rAllC _ wAnc hAncC)
        (fun w hw hEq ↦ by
          obtain ⟨j', hj', rfl⟩ := option_map_eq_some hw
          exact canonLeg4_642_j_ne_jp t j' hj' (rZ14.wires.injective hEq))
        (fun w hw ↦ by
          obtain ⟨j', _, rfl⟩ := option_map_eq_some hw
          exact (hBC.ne j' _).symm)
        (fun w hw ↦ by
          obtain ⟨k', _, rfl⟩ := option_map_eq_some hw
          exact hBC.ne _ k')
        (fun w hw hEq ↦ by
          obtain ⟨k', hk', rfl⟩ := option_map_eq_some hw
          exact canonLeg4_642_k_ne_kp t k' hk' (rAllC.wires.injective hEq))
        hAncS (hBNotS _) (hCNotS _)
      have hComb := hPrev.seq hStep
      rw [diagKetUnitary_mul] at hComb
      refine hComb.congr_unitary fun γ _ ↦ ?_
      rw [diagKetUnitary_mulVec_ket, diagKetUnitary_mulVec_ket, Fin.sum_univ_castSucc, add_comm]
      rfl

/-- `0-T`, `0-TOFF` Clifford residual circuit (`bg642Coeff` bilinear `CZ` + `hotCtxPhaseLoop` on
`rHotA64 × rZ14` and `rHotA64 × rAllC`). -/
def hot642ResidualClifford {N : ℕ}
    (P_slice : Fin (2 ^ 6) → Fin (2 ^ 4) → Fin (2 ^ 2) → ZMod 2)
    (rHotA64 : QRegister (2 ^ 6) N) (rZ14 : QRegister 14 N) (rAllC : QRegister 3 N)
    (hAB : rHotA64.DisjointWires rZ14) (hAC : rHotA64.DisjointWires rAllC)
    (hBC : rZ14.DisjointWires rAllC) : Circuit N :=
  .seq (FreeAltInnerPrepMid.czBilinearCircuit 14 3 rZ14 rAllC hBC bg642Coeff)
  (.seq (MidReflCtxRetain.hotCtxPhaseLoop 14 (2 ^ 6) rHotA64 rZ14 (fun c u ↦ hAB.ne c u)
      (fun c ↦ anf2DCoeffs42 (hotRes642Cube P_slice c) ⟨0, by decide⟩ ⟨0, by decide⟩)
      (fun c uB ↦ anf2DCoeffs42 (hotRes642Cube P_slice c) ⟨uB.val + 1, by omega⟩ ⟨0, by decide⟩)
      (2 ^ 6) le_rfl)
    (MidReflCtxRetain.hotCtxPhaseLoop 3 (2 ^ 6) rHotA64 rAllC (fun c u ↦ hAC.ne c u)
      (fun _ ↦ 0)
      (fun c uC ↦ anf2DCoeffs42 (hotRes642Cube P_slice c) ⟨0, by decide⟩ ⟨uC.val + 1, by omega⟩)
      (2 ^ 6) le_rfl))

@[simp] theorem count_hot642ResidualClifford_toff {N : ℕ}
    (P_slice : Fin (2 ^ 6) → Fin (2 ^ 4) → Fin (2 ^ 2) → ZMod 2)
    (rHotA64 : QRegister (2 ^ 6) N) (rZ14 : QRegister 14 N) (rAllC : QRegister 3 N)
    (hAB : rHotA64.DisjointWires rZ14) (hAC : rHotA64.DisjointWires rAllC)
    (hBC : rZ14.DisjointWires rAllC) :
    (hot642ResidualClifford P_slice rHotA64 rZ14 rAllC hAB hAC hBC).count .TOFF = 0 := by
  simp [hot642ResidualClifford, count_hotCtxPhaseLoop_toff2]

@[simp] theorem count_hot642ResidualClifford_t {N : ℕ}
    (P_slice : Fin (2 ^ 6) → Fin (2 ^ 4) → Fin (2 ^ 2) → ZMod 2)
    (rHotA64 : QRegister (2 ^ 6) N) (rZ14 : QRegister 14 N) (rAllC : QRegister 3 N)
    (hAB : rHotA64.DisjointWires rZ14) (hAC : rHotA64.DisjointWires rAllC)
    (hBC : rZ14.DisjointWires rAllC) :
    (hot642ResidualClifford P_slice rHotA64 rZ14 rAllC hAB hAC hBC).count .T = 0 := by
  simp [hot642ResidualClifford, count_hotCtxPhaseLoop_t2]

private theorem ket_hot642ResidualClifford {N : ℕ}
    (P_slice : Fin (2 ^ 6) → Fin (2 ^ 4) → Fin (2 ^ 2) → ZMod 2)
    (rHotA64 : QRegister (2 ^ 6) N) (rZ14 : QRegister 14 N) (rAllC : QRegister 3 N)
    (hAB : rHotA64.DisjointWires rZ14) (hAC : rHotA64.DisjointWires rAllC)
    (hBC : rZ14.DisjointWires rAllC) (γ : BitAssignment N) :
    (hot642ResidualClifford P_slice rHotA64 rZ14 rAllC hAB hAC hBC).eval.1.mulVec
        (SelectSwapQROM.ket γ) =
      SelectSwapQROM.bitSign
        ((∑ uB : Fin 14, γ (rZ14 uB) * ∑ uC : Fin 3, bg642Coeff uB uC * γ (rAllC uC)) +
         (∑ c : Fin (2 ^ 6), γ (rHotA64 c) *
           (anf2DCoeffs42 (hotRes642Cube P_slice c) ⟨0, by decide⟩ ⟨0, by decide⟩ +
             ∑ uB : Fin 14,
               anf2DCoeffs42 (hotRes642Cube P_slice c) ⟨uB.val + 1, by omega⟩ ⟨0, by decide⟩ *
                 γ (rZ14 uB))) +
         (∑ c : Fin (2 ^ 6), γ (rHotA64 c) *
           (0 + ∑ uC : Fin 3,
             anf2DCoeffs42 (hotRes642Cube P_slice c) ⟨0, by decide⟩ ⟨uC.val + 1, by omega⟩ *
               γ (rAllC uC)))) •
        SelectSwapQROM.ket γ := by
  dsimp only [hot642ResidualClifford]
  rw [SelectSwapQROM.eval_seq_mulVec, FreeAltInnerPrepMid.ket_czBilinearCircuit,
    Matrix.mulVec_smul, SelectSwapQROM.eval_seq_mulVec, ket_hotCtxPhaseLoop,
    Matrix.mulVec_smul, ket_hotCtxPhaseLoop, smul_smul, smul_smul,
    ← SelectSwapQROM.bitSign_add, ← SelectSwapQROM.bitSign_add]

/-- `3D` `(6, 4, 2)` phase slice extracted from a `12`-bit Boolean table `P : ℕ → Bool`. -/
def phaseCube642 (P : ℕ → Bool) (zA : Fin (2 ^ 6)) (zB : Fin (2 ^ 4))
    (zC : Fin (2 ^ 2)) : ZMod 2 :=
  if P (cubeAddr642 zA zB zC).val then 1 else 0

/-- `StepPow2Layout 5 N` (`64` one-hot wires `rScr82[0..64)` + `qEnc = rScr82 81`) for `rA6`. -/
def stepLayoutA64 {N : ℕ} (rIdx : QRegister (6 + 6) N) (rScr82 : QRegister 82 N)
    (hIdxScr : rIdx.DisjointWires rScr82) : StepPow2Layout 5 N where
  rCtx := rIdx.slice 5 6 (by decide)
  rHot := rScr82.slice 0 64 (by decide)
  qEnc := rScr82 ⟨81, by decide⟩
  hCtxHot := (hIdxScr.compose_left _).compose_right _
  hCtxEnc := fun i ↦ (hIdxScr.compose_left (QRegister.block 5 6 (by decide))).ne i ⟨81, by decide⟩
  hHotEnc := fun g hEq ↦ by
    have hv := congrArg Fin.val (rScr82.wires.injective hEq)
    have := g.isLt
    simp at hv
    omega

/-- `StepPow2Layout 3 N` (`16` ANF wires `rScr82[64..80)` + `qEnc = rScr82 81`) for `rB4`. -/
def stepLayoutB16 {N : ℕ} (rIdx : QRegister (6 + 6) N) (rScr82 : QRegister 82 N)
    (hIdxScr : rIdx.DisjointWires rScr82) : StepPow2Layout 3 N where
  rCtx := rIdx.slice 1 4 (by decide)
  rHot := rScr82.slice 64 16 (by decide)
  qEnc := rScr82 ⟨81, by decide⟩
  hCtxHot := (hIdxScr.compose_left _).compose_right _
  hCtxEnc := fun i ↦ (hIdxScr.compose_left (QRegister.block 1 4 (by decide))).ne i ⟨81, by decide⟩
  hHotEnc := fun g hEq ↦ by
    have hv := congrArg Fin.val (rScr82.wires.injective hEq)
    have := g.isLt
    simp at hv
    omega

/-- `64`-wire one-hot register `rScr82[0..64)` typed at `QRegister (2 ^ 6) N`. -/
abbrev rHotA64Of {N : ℕ} (rIdx : QRegister (6 + 6) N) (rScr82 : QRegister 82 N)
    (hIdxScr : rIdx.DisjointWires rScr82) : QRegister (2 ^ 6) N :=
  (stepLayoutA64 rIdx rScr82 hIdxScr).rHot

/-- `14`-wire non-zero, non-top ANF register `rScr82[65..79)` typed at `QRegister 14 N`. -/
abbrev rZ14Of {N : ℕ} (rIdx : QRegister (6 + 6) N) (rScr82 : QRegister 82 N)
    (hIdxScr : rIdx.DisjointWires rScr82) : QRegister 14 N :=
  (stepLayoutB16 rIdx rScr82 hIdxScr).rHot.slice 1 14 (by decide)

/-- `3`-wire non-zero `2`-bit ANF register on `c2In12Reg` + `rScr82[80..81)`. -/
abbrev rAllCOf {N : ℕ} (rIdx : QRegister (6 + 6) N) (rScr82 : QRegister 82 N)
    (hIdxScr : rIdx.DisjointWires rScr82) : QRegister 3 N :=
  SelectSwapQROM.allMonoReg 2 (rIdx.compose c2In12Reg)
    (rScr82.slice 80 (SelectSwapQROM.anfScratchWidth 2) (by decide))
    ((hIdxScr.compose_left _).compose_right _)

theorem hotA64_disjoint_z14 {N : ℕ} (rIdx : QRegister (6 + 6) N)
    (rScr82 : QRegister 82 N) (hIdxScr : rIdx.DisjointWires rScr82) :
    (rHotA64Of rIdx rScr82 hIdxScr).DisjointWires (rZ14Of rIdx rScr82 hIdxScr) :=
  (rScr82.slice_disjoint_of_le 0 64 64 16 (by decide) (by decide) le_rfl).compose_right _

theorem hotA64_disjoint_allC3 {N : ℕ} (rIdx : QRegister (6 + 6) N)
    (rScr82 : QRegister 82 N) (hIdxScr : rIdx.DisjointWires rScr82) :
    (rHotA64Of rIdx rScr82 hIdxScr).DisjointWires (rAllCOf rIdx rScr82 hIdxScr) := by
  refine OptXMeasUnload21.disjointWires_of_disjoint_image (Disjoint.mono_right
    (SelectSwapQROM.allMonoReg_image_subset _ _ _) (Finset.disjoint_union_right.mpr ⟨?_, ?_⟩))
  · exact Disjoint.mono (rScr82.image_compose_subset _) (rIdx.image_compose_subset _)
      (SelectSwapQROM.disjoint_image_of_disjointWires hIdxScr).symm
  · exact SelectSwapQROM.disjoint_image_of_disjointWires
      (rScr82.slice_disjoint_of_le 0 64 80 (SelectSwapQROM.anfScratchWidth 2)
        (by decide) (by decide) (by decide))

theorem z14_disjoint_allC3 {N : ℕ} (rIdx : QRegister (6 + 6) N)
    (rScr82 : QRegister 82 N) (hIdxScr : rIdx.DisjointWires rScr82) :
    (rZ14Of rIdx rScr82 hIdxScr).DisjointWires (rAllCOf rIdx rScr82 hIdxScr) := by
  refine OptXMeasUnload21.disjointWires_of_disjoint_image (Disjoint.mono_right
    (SelectSwapQROM.allMonoReg_image_subset _ _ _) (Finset.disjoint_union_right.mpr ⟨?_, ?_⟩))
  · exact Disjoint.mono
      (((rScr82.slice 64 16 (by decide)).image_compose_subset _).trans
        (rScr82.image_compose_subset _))
      (rIdx.image_compose_subset _)
      (SelectSwapQROM.disjoint_image_of_disjointWires hIdxScr).symm
  · exact Disjoint.mono_left ((rScr82.slice 64 16 (by decide)).image_compose_subset _)
      (SelectSwapQROM.disjoint_image_of_disjointWires
        (rScr82.slice_disjoint_of_le 64 16 80 (SelectSwapQROM.anfScratchWidth 2)
          (by decide) (by decide) (by decide)))

theorem wAnc81_ne_hotA64 {N : ℕ} (rIdx : QRegister (6 + 6) N)
    (rScr82 : QRegister 82 N) (hIdxScr : rIdx.DisjointWires rScr82) (c : Fin (2 ^ 6)) :
    rScr82 ⟨81, by decide⟩ ≠ rHotA64Of rIdx rScr82 hIdxScr c :=
  ((stepLayoutA64 rIdx rScr82 hIdxScr).hHotEnc c).symm

theorem wAnc81_ne_z14 {N : ℕ} (rIdx : QRegister (6 + 6) N)
    (rScr82 : QRegister 82 N) (hIdxScr : rIdx.DisjointWires rScr82) (j : Fin 14) :
    rScr82 ⟨81, by decide⟩ ≠ rZ14Of rIdx rScr82 hIdxScr j :=
  ((stepLayoutB16 rIdx rScr82 hIdxScr).hHotEnc _).symm

theorem wAnc81_ne_allC3 {N : ℕ} (rIdx : QRegister (6 + 6) N)
    (rScr82 : QRegister 82 N) (hIdxScr : rIdx.DisjointWires rScr82) (k : Fin 3) :
    rScr82 ⟨81, by decide⟩ ≠ rAllCOf rIdx rScr82 hIdxScr k := by
  intro hEq
  have hmem := SelectSwapQROM.allMonoReg_image_subset (rIdx.compose c2In12Reg)
    (rScr82.slice 80 (SelectSwapQROM.anfScratchWidth 2) (by decide))
    ((hIdxScr.compose_left _).compose_right _)
    ((QRegister.mem_image _ _).mpr ⟨k, hEq.symm⟩)
  rcases Finset.mem_union.mp hmem with hC | hM
  · exact Finset.disjoint_right.mp (SelectSwapQROM.disjoint_image_of_disjointWires hIdxScr)
      ((QRegister.mem_image rScr82 _).mpr ⟨⟨81, by decide⟩, rfl⟩)
      (rIdx.image_compose_subset _ hC)
  · obtain ⟨j, hj⟩ := (QRegister.mem_image _ _).mp hM
    have hjv := congrArg Fin.val (rScr82.wires.injective hj)
    have hjLt : j.val < 1 := j.isLt
    simp at hjv
    omega

/-- `212-T` (`124 + 28 + 4 + 56`), `0-TOFF`, `82`-scratch-wire `(6, 4, 2)` phase fixup circuit for
any `4096`-entry Boolean table `P` whose `16`-element even/odd column parities vanish. -/
def ext24W642PhaseFixupDyn {Var : Type} {N : ℕ} (v : Var) (P : ℕ → Bool)
    (rIdx : QRegister (6 + 6) N) (rScr82 : QRegister 82 N)
    (hIdxScr : rIdx.DisjointWires rScr82) : DynamicCircuit Var N :=
  let L_A := stepLayoutA64 rIdx rScr82 hIdxScr
  let L_B := stepLayoutB16 rIdx rScr82 hIdxScr
  let rHotA64 := rHotA64Of rIdx rScr82 hIdxScr
  let rZ14 := rZ14Of rIdx rScr82 hIdxScr
  let rC2 := rIdx.compose c2In12Reg
  let rMC := rScr82.slice 80 (SelectSwapQROM.anfScratchWidth 2) (by decide)
  let hCM : rC2.DisjointWires rMC := (hIdxScr.compose_left _).compose_right _
  let rAllC := rAllCOf rIdx rScr82 hIdxScr
  let wAnc := rScr82 ⟨81, by decide⟩
  let hAB := hotA64_disjoint_z14 rIdx rScr82 hIdxScr
  let hAC := hotA64_disjoint_allC3 rIdx rScr82 hIdxScr
  let hBC := z14_disjoint_allC3 rIdx rScr82 hIdxScr
  let hAncA := wAnc81_ne_hotA64 rIdx rScr82 hIdxScr
  let hAncB := wAnc81_ne_z14 rIdx rScr82 hIdxScr
  let hAncC := wAnc81_ne_allC3 rIdx rScr82 hIdxScr
  let P_slice := phaseCube642 P
  withStepOneHotPow2Dyn v L_A
    (withStepAnfPow2Dyn v L_B
      (SelectSwapQROM.monoSandwichDyn v 2 rC2 rMC hCM
        (.seq (lStepLoop14 v P_slice rHotA64 rZ14 rAllC wAnc hAB hAC hBC hAncA hAncB hAncC
            14 le_rfl)
          (.circuit (hot642ResidualClifford P_slice rHotA64 rZ14 rAllC hAB hAC hBC)))))

@[simp] theorem count_ext24W642PhaseFixupDyn_toff {Var : Type} {N : ℕ} (v : Var) (P : ℕ → Bool)
    (rIdx : QRegister (6 + 6) N) (rScr82 : QRegister 82 N)
    (hIdxScr : rIdx.DisjointWires rScr82) :
    (ext24W642PhaseFixupDyn v P rIdx rScr82 hIdxScr).count .TOFF = 0 := by
  dsimp only [ext24W642PhaseFixupDyn]
  rw [count_withStepOneHotPow2Dyn_toff, count_withStepAnfPow2Dyn_toff,
    SelectSwapQROM.count_monoSandwichDyn_toff, DynamicCircuit.count,
    count_lStepLoop14_toff, DynamicCircuit.count, count_hot642ResidualClifford_toff, add_zero]

@[simp] theorem count_ext24W642PhaseFixupDyn_t {Var : Type} {N : ℕ} (v : Var) (P : ℕ → Bool)
    (rIdx : QRegister (6 + 6) N) (rScr82 : QRegister 82 N)
    (hIdxScr : rIdx.DisjointWires rScr82) :
    (ext24W642PhaseFixupDyn v P rIdx rScr82 hIdxScr).count .T = 212 := by
  dsimp only [ext24W642PhaseFixupDyn]
  rw [count_withStepOneHotPow2Dyn_t, count_withStepAnfPow2Dyn_t,
    SelectSwapQROM.count_monoSandwichDyn_t, DynamicCircuit.count,
    count_lStepLoop14_t, DynamicCircuit.count, count_hot642ResidualClifford_t]
  decide

private theorem scr82_parts_union_eq {N : ℕ} (rScr82 : QRegister 82 N)
    (S_extra : Finset (Wire N)) :
    (rScr82.slice 0 64 (by decide)).image ∪
      ((rScr82.slice 64 16 (by decide)).image ∪
        ((rScr82.slice 80 (SelectSwapQROM.anfScratchWidth 2) (by decide)).image ∪
          ({rScr82 ⟨81, by decide⟩} ∪ S_extra))) =
      rScr82.image ∪ S_extra := by
  ext w; simp only [Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro (hA | hB | hM | rfl | hE)
    · exact Or.inl (rScr82.image_compose_subset _ hA)
    · exact Or.inl (rScr82.image_compose_subset _ hB)
    · exact Or.inl (rScr82.image_compose_subset _ hM)
    · exact Or.inl ((QRegister.mem_image rScr82 _).mpr ⟨⟨81, by decide⟩, rfl⟩)
    · exact Or.inr hE
  · rintro (hS | hE)
    · obtain ⟨i, rfl⟩ := (QRegister.mem_image rScr82 w).mp hS
      by_cases h64 : i.val < 64
      · exact Or.inl ((QRegister.mem_image _ _).mpr ⟨⟨i.val, h64⟩, by simp [QRegister.slice]⟩)
      · by_cases h80 : i.val < 80
        · exact Or.inr (Or.inl ((QRegister.mem_image _ _).mpr
            ⟨⟨i.val - 64, by omega⟩,
              congrArg rScr82 (Fin.ext (by simp; omega))⟩))
        · by_cases h81 : i.val = 80
          · exact Or.inr (Or.inr (Or.inl ((QRegister.mem_image _ _).mpr
              ⟨⟨0, by decide⟩,
                congrArg rScr82 (Fin.ext (by simp [h81]))⟩)))
          · have h81e : i.val = 81 := by have := i.isLt; omega
            exact Or.inr (Or.inr (Or.inr (Or.inl (congrArg rScr82 (Fin.ext h81e)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hE)))

theorem wpZeroSet_ext24W642PhaseFixupDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {N : ℕ} [NeZero (2 ^ N)] (v : Var) (S : Finset (Wire N))
    (P : ℕ → Bool)
    (hPar16 : ∀ (rc : Fin 128) (b₀ : Fin 2),
      (∑ u : Fin 16, if P (32 * rc.val + 2 * u.val + b₀.val) then (1 : ZMod 2) else 0) = 0)
    (rIdx : QRegister (6 + 6) N) (rScr82 : QRegister 82 N)
    (hIdxScr : rIdx.DisjointWires rScr82)
    (hScrSubS : rScr82.image ⊆ S) (hDisjIdxS : Disjoint rIdx.image S) :
    WpZeroSet v S (rIdx.embedUnitary (SelectSwapQROM.diagPhaseUnitary (6 + 6) 4096 P))
      (ext24W642PhaseFixupDyn v P rIdx rScr82 hIdxScr) := by
  let L_A := stepLayoutA64 rIdx rScr82 hIdxScr
  let L_B := stepLayoutB16 rIdx rScr82 hIdxScr
  let rHotA64 := rHotA64Of rIdx rScr82 hIdxScr
  let rHotB16 := L_B.rHot
  let rZ14 := rZ14Of rIdx rScr82 hIdxScr
  let rC2 := rIdx.compose c2In12Reg
  let rMC := rScr82.slice 80 (SelectSwapQROM.anfScratchWidth 2) (by decide)
  let hCM : rC2.DisjointWires rMC := (hIdxScr.compose_left _).compose_right _
  let rAllC := rAllCOf rIdx rScr82 hIdxScr
  let wAnc := rScr82 ⟨81, by decide⟩
  let hAB := hotA64_disjoint_z14 rIdx rScr82 hIdxScr
  let hAC := hotA64_disjoint_allC3 rIdx rScr82 hIdxScr
  let hBC := z14_disjoint_allC3 rIdx rScr82 hIdxScr
  let hAncA := wAnc81_ne_hotA64 rIdx rScr82 hIdxScr
  let hAncB := wAnc81_ne_z14 rIdx rScr82 hIdxScr
  let hAncC := wAnc81_ne_allC3 rIdx rScr82 hIdxScr
  let P_slice := phaseCube642 P
  let S_extra := S \ rScr82.image
  let S₃ : Finset (Wire N) := {wAnc} ∪ S_extra
  let S₂ : Finset (Wire N) := rMC.image ∪ S₃
  let S₁ : Finset (Wire N) := rHotB16.image ∪ S₂
  have hDisjScrExtra : Disjoint rScr82.image S_extra := _root_.disjoint_sdiff_self_right
  have hDisjIdxExtra : Disjoint rIdx.image S_extra :=
    Disjoint.mono_right Finset.sdiff_subset hDisjIdxS
  have hAncInScr : wAnc ∈ rScr82.image := (QRegister.mem_image rScr82 _).mpr ⟨⟨81, by decide⟩, rfl⟩
  have hBNotS₃ (j : Fin 14) : rZ14 j ∉ S₃ := by
    simp only [S₃, Finset.mem_union, Finset.mem_singleton]
    rintro (hEq | hEx)
    · exact hAncB j hEq.symm
    · exact Finset.disjoint_left.mp hDisjScrExtra
        (rScr82.image_compose_subset _ (rHotB16.image_compose_subset _
          ((QRegister.mem_image rZ14 _).mpr ⟨j, rfl⟩))) hEx
  have hDisjMC_S₃ : Disjoint rMC.image S₃ := by
    rw [Finset.disjoint_union_right, Finset.disjoint_singleton_right]
    refine ⟨?_, Disjoint.mono_left (rScr82.image_compose_subset _) hDisjScrExtra⟩
    rintro hmem; obtain ⟨i, hi⟩ := (QRegister.mem_image rMC _).mp hmem
    have hv := congrArg Fin.val (rScr82.wires.injective hi)
    have hiLt : i.val < 1 := i.isLt
    simp at hv
    omega
  have hCNotS₃ (k : Fin 3) : rAllC k ∉ S₃ := by
    simp only [S₃, Finset.mem_union, Finset.mem_singleton]
    rintro (hEq | hEx)
    · exact hAncC k hEq.symm
    · have hm := SelectSwapQROM.allMonoReg_image_subset rC2 rMC hCM
        ((QRegister.mem_image rAllC _).mpr ⟨k, rfl⟩)
      rcases Finset.mem_union.mp hm with hC | hM
      · exact Finset.disjoint_left.mp hDisjIdxExtra (rIdx.image_compose_subset _ hC) hEx
      · exact Finset.disjoint_left.mp hDisjScrExtra (rScr82.image_compose_subset _ hM) hEx
  have hLoop := cleanRealizesSet_lStepLoop14 v S₃ P_slice rHotA64 rZ14 rAllC wAnc
    hAB hAC hBC hAncA hAncB hAncC (Finset.mem_union_left _ (Finset.mem_singleton_self _))
    hBNotS₃ hCNotS₃ 14 le_rfl
  let cliff := hot642ResidualClifford P_slice rHotA64 rZ14 rAllC hAB hAC hBC
  have hCliff : SelectSwapQROM.CleanRealizesSet v S₃ cliff.eval (.circuit cliff) := by
    refine SelectSwapQROM.CleanRealizesSet.ofCircuit v S₃ cliff
      (count_hot642ResidualClifford_toff _ _ _ _ _ _ _) fun γ hγ ↦ ?_
    rw [ket_hot642ResidualClifford, Matrix.mulVec_smul, SelectSwapQROM.zeroProjOn_mulVec_ket,
      ite_eq_left hγ]
  have hInnerSet := hLoop.seq hCliff
  have hS₂_sdiff : S₂ \ rMC.image = S₃ := Finset.union_sdiff_cancel_left hDisjMC_S₃
  let cliffExp (γ : BitAssignment N) : ZMod 2 :=
    (∑ uB : Fin 14, γ (rZ14 uB) * ∑ uC : Fin 3, bg642Coeff uB uC * γ (rAllC uC)) +
    (∑ c : Fin (2 ^ 6), γ (rHotA64 c) *
      (anf2DCoeffs42 (hotRes642Cube P_slice c) ⟨0, by decide⟩ ⟨0, by decide⟩ +
        ∑ uB : Fin 14,
          anf2DCoeffs42 (hotRes642Cube P_slice c) ⟨uB.val + 1, by omega⟩ ⟨0, by decide⟩ *
            γ (rZ14 uB))) +
    (∑ c : Fin (2 ^ 6), γ (rHotA64 c) *
      (0 + ∑ uC : Fin 3,
        anf2DCoeffs42 (hotRes642Cube P_slice c) ⟨0, by decide⟩ ⟨uC.val + 1, by omega⟩ *
          γ (rAllC uC)))
  let innerPhi (γ : BitAssignment N) : ZMod 2 :=
    (∑ t : Fin 14, lStep642KetPhase P_slice rHotA64 rZ14 rAllC t γ) + cliffExp γ
  have hkInner (γ : BitAssignment N) :
      (cliff.eval * diagKetUnitary
        (fun δ ↦ ∑ t : Fin 14, lStep642KetPhase P_slice rHotA64 rZ14 rAllC t δ)).1.mulVec
        (SelectSwapQROM.ket γ) =
      SelectSwapQROM.bitSign (innerPhi γ) • SelectSwapQROM.ket γ := by
    rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, diagKetUnitary_mulVec_ket, Matrix.mulVec_smul,
      ket_hot642ResidualClifford, smul_smul, ← SelectSwapQROM.bitSign_add]
  have hDisjC2_S₂ : Disjoint rC2.image S₂ := by
    refine Disjoint.mono_left (rIdx.image_compose_subset _) ?_
    refine Disjoint.mono_right ?_ hDisjIdxS
    refine Finset.union_subset ((rScr82.image_compose_subset _).trans hScrSubS) ?_
    exact Finset.union_subset (Finset.singleton_subset_iff.mpr (hScrSubS hAncInScr))
      Finset.sdiff_subset
  obtain ⟨U_C, popC, hCrC, hkC⟩ :=
    SelectSwapQROM.cleanRealizesSet_monoSandwichDyn_diag v S₂ rC2 rMC hCM
      Finset.subset_union_left hDisjC2_S₂ (hS₂_sdiff.symm ▸ hInnerSet) (fun γ _ ↦ hkInner γ)
  have hWpC := WpZeroSet.of_cleanRealizesSet hCrC
  have hDisjB_S₂ : Disjoint rHotB16.image S₂ := by
    refine Finset.disjoint_union_right.mpr ⟨?_, Finset.disjoint_union_right.mpr ⟨?_, ?_⟩⟩
    · exact SelectSwapQROM.disjoint_image_of_disjointWires
        (rScr82.slice_disjoint_of_le 64 16 80 (SelectSwapQROM.anfScratchWidth 2)
          (by decide) (by decide) (by decide))
    · rw [Finset.disjoint_singleton_right]
      rintro hm; obtain ⟨g, hg⟩ := (QRegister.mem_image rHotB16 _).mp hm
      exact L_B.hHotEnc g hg
    · exact Disjoint.mono_left (rScr82.image_compose_subset _) hDisjScrExtra
  have hAncInS₂ : L_B.qEnc ∈ S₂ :=
    Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_singleton_self _))
  have hWpB := WpZeroSet.withStepAnfPow2_diag (K := 3) (by decide) (by decide) L_B S₂
    hAncInS₂ hDisjB_S₂ hWpC (fun γ hγ ↦ (hkC γ hγ).1)
  have hDisjA_S₁ : Disjoint L_A.rHot.image S₁ := by
    refine Finset.disjoint_union_right.mpr ⟨?_, Finset.disjoint_union_right.mpr
      ⟨?_, Finset.disjoint_union_right.mpr ⟨?_, ?_⟩⟩⟩
    · exact SelectSwapQROM.disjoint_image_of_disjointWires
        (rScr82.slice_disjoint_of_le 0 64 64 16 (by decide) (by decide) le_rfl)
    · exact SelectSwapQROM.disjoint_image_of_disjointWires
        (rScr82.slice_disjoint_of_le 0 64 80 (SelectSwapQROM.anfScratchWidth 2)
          (by decide) (by decide) (by decide))
    · rw [Finset.disjoint_singleton_right]
      rintro hm; obtain ⟨g, hg⟩ := (QRegister.mem_image L_A.rHot _).mp hm
      exact L_A.hHotEnc g hg
    · exact Disjoint.mono_left (rScr82.image_compose_subset _) hDisjScrExtra
  have hAncInS₁ : L_A.qEnc ∈ S₁ := Finset.mem_union_right _ hAncInS₂
  have hWpA := WpZeroSet.withStepOneHotPow2_diag (K := 5) (by decide) (by decide) L_A S₁
    hAncInS₁ hDisjA_S₁ hWpB (fun γ _ ↦ diagKetUnitary_mulVec_ket _ γ)
  have hSEq : L_A.rHot.image ∪ S₁ = S :=
    (scr82_parts_union_eq rScr82 S_extra).trans (Finset.union_sdiff_of_subset hScrSubS)
  rw [hSEq] at hWpA
  refine WpZeroSet.congr_unitary hWpA fun β hβ ↦ ?_
  have hket (γ : BitAssignment N) : Solution.XMeasCircuit.ket γ = SelectSwapQROM.ket γ := rfl
  rw [hket β, diagKetUnitary_mulVec_ket, SelectSwapQROM.embed_diagPhaseUnitary_mulVec_ket]
  let β₁ := oneHotEncAssign2 L_A β
  let β₂ := anfEncAssign2 L_B β₁
  have hβ₁_S₁ (w : Wire N) (hw : w ∈ S₁) : β₁ w = 0 := by
    dsimp only [β₁]
    rw [oneHotEncAssign2_apply_of_not_mem L_A β (Finset.disjoint_right.mp hDisjA_S₁ hw)]
    exact hβ w (hSEq ▸ Finset.mem_union_right _ hw)
  have hβ₂_S₂ (w : Wire N) (hw : w ∈ S₂) : β₂ w = 0 := by
    dsimp only [β₂]
    rw [anfEncAssign2_apply_of_not_mem L_B β₁ (Finset.disjoint_right.mp hDisjB_S₂ hw)]
    exact hβ₁_S₁ w (Finset.mem_union_right _ hw)
  obtain ⟨_, hOutC, hAllC⟩ := hkC β₂ hβ₂_S₂
  let δ := popC β₂
  let zA : Fin (2 ^ 6) := Solution.CircuitModular.UnsignedGivens.localIdx L_A.rCtx β
  let zB : Fin (2 ^ 4) := (basisBits 4).symm (fun i ↦ β (L_B.rCtx i))
  let zC : Fin (2 ^ 2) := (basisBits 2).symm (fun i ↦ β (rC2 i))
  have hzA (i : Fin 6) : basisBits 6 zA i = β (L_A.rCtx i) :=
    congrFun (SelectSwapQROM.basisBits_symm _) i
  have hzB (i : Fin 4) : basisBits 4 zB i = β (L_B.rCtx i) :=
    congrFun (SelectSwapQROM.basisBits_symm _) i
  have hzC (i : Fin 2) : basisBits 2 zC i = β (rC2 i) :=
    congrFun (SelectSwapQROM.basisBits_symm _) i
  have hIdxNotHotA {w : Wire N} (hw : w ∈ rIdx.image) : w ∉ L_A.rHot.image :=
    Finset.disjoint_left.mp (Disjoint.mono_right (rScr82.image_compose_subset _)
      (SelectSwapQROM.disjoint_image_of_disjointWires hIdxScr)) hw
  have hIdxNotHotB {w : Wire N} (hw : w ∈ rIdx.image) : w ∉ rHotB16.image :=
    Finset.disjoint_left.mp (Disjoint.mono_right (rScr82.image_compose_subset _)
      (SelectSwapQROM.disjoint_image_of_disjointWires hIdxScr)) hw
  have hδA (c : Fin (2 ^ 6)) : δ (rHotA64 c) = if c = zA then 1 else 0 := by
    have hnMC : rHotA64 c ∉ rMC.image :=
      (rScr82.slice_disjoint_of_le 0 64 80 (SelectSwapQROM.anfScratchWidth 2)
        (by decide) (by decide) (by decide)).apply_not_mem_right ⟨c.val, c.isLt⟩
    have hnB : rHotA64 c ∉ rHotB16.image :=
      (rScr82.slice_disjoint_of_le 0 64 64 16 (by decide) (by decide) le_rfl).apply_not_mem_right
        ⟨c.val, c.isLt⟩
    dsimp only [δ]
    rw [hOutC _ hnMC]
    dsimp only [β₂]
    rw [anfEncAssign2_apply_of_not_mem L_B β₁ hnB]
    exact (oneHotEncAssign2_apply_reg L_A β c).trans (by simp [zA, Fin.ext_iff])
  have hδB (uB : Fin 14) :
      δ (rZ14 uB) = SelectSwapQROM.monoEval 4 (basisBits 4 zB) ⟨uB.val + 1, by omega⟩ := by
    have hnMC : rZ14 uB ∉ rMC.image := fun hm ↦
      Finset.disjoint_left.mp hDisjB_S₂
        (rHotB16.image_compose_subset _ ((QRegister.mem_image rZ14 _).mpr ⟨uB, rfl⟩))
        (Finset.mem_union_left _ hm)
    have hZeq : rZ14 uB = L_B.rHot ⟨uB.val + 1, by omega⟩ :=
      congrArg rHotB16 (Fin.ext (by
        simp
        omega))
    dsimp only [δ]
    rw [hOutC _ hnMC, hZeq]
    dsimp only [β₂]
    rw [anfEncAssign2_apply_hot L_B β₁]
    refine congrArg (fun f ↦ SelectSwapQROM.monoEval 4 f _) (funext fun i ↦ ?_)
    dsimp only [β₁]
    rw [oneHotEncAssign2_apply_of_not_mem L_A β
      (hIdxNotHotA (rIdx.image_compose_subset _ ((QRegister.mem_image L_B.rCtx _).mpr ⟨i, rfl⟩))),
      ← hzB i]
  have hδC (uC : Fin 3) :
      δ (rAllC uC) = SelectSwapQROM.monoEval 2 (basisBits 2 zC) ⟨uC.val + 1, by omega⟩ := by
    refine (hAllC uC).trans
      (congrArg (fun f ↦ SelectSwapQROM.monoEval 2 f _) (funext fun i ↦ ?_))
    have hmIdx := rIdx.image_compose_subset _ ((QRegister.mem_image rC2 _).mpr ⟨i, rfl⟩)
    dsimp only [β₂]
    rw [anfEncAssign2_apply_of_not_mem L_B β₁ (hIdxNotHotB hmIdx)]
    dsimp only [β₁]
    rw [oneHotEncAssign2_apply_of_not_mem L_A β (hIdxNotHotA hmIdx), ← hzC i]
  have hSumHot (f : Fin (2 ^ 6) → ZMod 2) : (∑ c : Fin (2 ^ 6), f c * δ (rHotA64 c)) = f zA := by
    simp_rw [hδA]; simp
  have hSumHotL (f : Fin (2 ^ 6) → ZMod 2) : (∑ c : Fin (2 ^ 6), δ (rHotA64 c) * f c) = f zA := by
    simp_rw [hδA]; simp
  have hStepEq (t : Fin 14) :
      lStep642KetPhase P_slice rHotA64 rZ14 rAllC t δ =
        lin642Term ((leg642Masks P_slice t).1 zA) ((leg642Masks P_slice t).2.1 zA)
          ((leg642Masks P_slice t).2.2 zA) t zB zC + bg642Cube t zB zC := by
    dsimp only [lStep642KetPhase, lStepPhase, lin642Term]
    rw [hδB, hδC, optWireBit_map_eq_optMono4 δ rZ14 zB hδB,
      optWireBit_map_eq_optMono2 δ rAllC zC hδC,
      hSumHot (leg642Masks P_slice t).1, hSumHot (leg642Masks P_slice t).2.1,
      hSumHot (leg642Masks P_slice t).2.2]
    set T :=
      (SelectSwapQROM.monoEval 4 (basisBits 4 zB) ⟨(canonLeg4_642 t).1.val + 1, by omega⟩ +
          (leg642Masks P_slice t).1 zA) *
        (SelectSwapQROM.monoEval 2 (basisBits 2 zC) ⟨(canonLeg4_642 t).2.1.val + 1, by omega⟩ +
          (leg642Masks P_slice t).2.1 zA) *
        ((leg642Masks P_slice t).2.2 zA + optMono4 zB (canonLeg4_642 t).2.2.1 +
          optMono2 zC (canonLeg4_642 t).2.2.2)
    rw [add_assoc T, CharTwo.add_self_eq_zero, add_zero]
  have hSlicePar (zC' : Fin (2 ^ 2)) : (∑ y : Fin (2 ^ 4), P_slice zA y zC') = 0 := by
    let rc : Fin 128 := ⟨zA.val + 64 * (zC'.val / 2),
      by have := zA.isLt; have := zC'.isLt; omega⟩
    let b₀ : Fin 2 := ⟨zC'.val % 2, Nat.mod_lt _ (by decide)⟩
    refine (Finset.sum_congr rfl fun y _ ↦ ?_).trans (hPar16 rc b₀)
    dsimp only [P_slice, phaseCube642, cubeAddr642, rc, b₀]
    exact congrArg (fun idx ↦ if P idx then (1 : ZMod 2) else 0) (by omega)
  have hResExp := anf2DCoeffs42_eval_residual (hotRes642Cube P_slice zA)
    (anf2DCoeffs42_hotRes642Cube_15 P_slice zA hSlicePar)
    (anf2DCoeffs42_hotRes642Cube_bilinear P_slice zA) zB zC
  have hCliffVal : cliffExp δ = bg642Sum zB zC + hotRes642Cube P_slice zA zB zC := by
    dsimp only [cliffExp]
    rw [hSumHotL, hSumHotL, zero_add]
    simp_rw [hδB, hδC]
    rw [← bg642Sum_eq_bilinear zB zC, hResExp]
    ring
  have hPhiVal : innerPhi δ = P_slice zA zB zC := by
    dsimp only [innerPhi]
    simp_rw [hStepEq]
    rw [Finset.sum_add_distrib, ← bg642Sum, hCliffVal]
    dsimp only [hotRes642Cube]
    set S_lin := ∑ t : Fin 14,
      lin642Term ((leg642Masks P_slice t).1 zA) ((leg642Masks P_slice t).2.1 zA)
        ((leg642Masks P_slice t).2.2 zA) t zB zC
    have hR (a b p : ZMod 2) : (a + b) + (b + (p + a)) = (a + a) + (b + b) + p := by ring
    rw [hR, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, zero_add, zero_add]
  change SelectSwapQROM.bitSign (innerPhi δ) • SelectSwapQROM.ket β = _
  rw [hPhiVal]
  have hAddr : (basisBits (6 + 6)).symm (fun q ↦ β (rIdx q)) = cubeAddr642 zA zB zC :=
    symm12_eq_cubeAddr642 (fun q ↦ β (rIdx q))
  refine congrArg (· • SelectSwapQROM.ket β) ?_
  change SelectSwapQROM.bitSign (phaseCube642 P zA zB zC) =
    if ((basisBits (6 + 6)).symm (fun q ↦ β (rIdx q))).val < 4096 ∧
      P ((basisBits (6 + 6)).symm (fun q ↦ β (rIdx q))).val then -1 else 1
  rw [hAddr]
  have hlt : (cubeAddr642 zA zB zC).val < 4096 := (cubeAddr642 zA zB zC).isLt
  dsimp only [phaseCube642]
  cases P (cubeAddr642 zA zB zC).val <;> simp [hlt, SelectSwapQROM.bitSign]

attribute [irreducible] ext24W642PhaseFixupDyn

/-- Single-shot `M`-qubit X-measurement QROM unload followed by `ext24W642PhaseFixupDyn`
(`212 T`, `0 TOFF`, `82` scratch wires). -/
def qromExt24W642XMeasUnloadDyn {Var : Type} {N : ℕ} (v : Var)
    (M : ℕ) (T : ℕ → (Fin M → Bool))
    (rIdx : QRegister 12 N) (rMeas : QRegister M N) (rScr82 : QRegister 82 N)
    (hIdxScr : rIdx.DisjointWires rScr82) : DynamicCircuit Var N :=
  SelectSwapQROM.measureXResetAndBranch v M rMeas fun m ↦
    ext24W642PhaseFixupDyn v (SelectSwapQROM.parityPhaseTable M T m) rIdx rScr82 hIdxScr

@[simp] theorem count_qromExt24W642XMeasUnloadDyn_toff {Var : Type} {N : ℕ} (v : Var)
    (M : ℕ) (T : ℕ → (Fin M → Bool))
    (rIdx : QRegister 12 N) (rMeas : QRegister M N) (rScr82 : QRegister 82 N)
    (hIdxScr : rIdx.DisjointWires rScr82) :
    (qromExt24W642XMeasUnloadDyn v M T rIdx rMeas rScr82 hIdxScr).count .TOFF = 0 :=
  SelectSwapQROM.count_measureXResetAndBranch_toff v M rMeas _ fun _ ↦
    count_ext24W642PhaseFixupDyn_toff _ _ _ _ _

@[simp] theorem count_qromExt24W642XMeasUnloadDyn_t {Var : Type} {N : ℕ} (v : Var)
    (M : ℕ) (T : ℕ → (Fin M → Bool))
    (rIdx : QRegister 12 N) (rMeas : QRegister M N) (rScr82 : QRegister 82 N)
    (hIdxScr : rIdx.DisjointWires rScr82) :
    (qromExt24W642XMeasUnloadDyn v M T rIdx rMeas rScr82 hIdxScr).count .T = 212 :=
  SelectSwapQROM.count_measureXResetAndBranch_t_eq v M 212 rMeas _ fun _ ↦
    count_ext24W642PhaseFixupDyn_t _ _ _ _ _

attribute [irreducible] qromExt24W642XMeasUnloadDyn

open Operator QProg Matrix Circuit HermitianMat Real
open Solution.BlockEncodingCircuit
open Solution.FastUniform
open Solution.CoherentAlias
open Solution.AliasPrep
open Solution.Phase2MidSandwich
open Solution.CompactBilinearPrep
open Solution.DyadicPacketInnerPrep
open Solution.RankReducedPrepMid
open Solution.MidReflCtxRetain
open Solution.Cat11CompactPhase2Bridge
open Solution.ReordOuter13Bridge
open Solution.ZeroRcHotPrepMid21Fast
open Solution.OptXMeasUnload21
open Solution.OptStepSympAnfQrom21
open Solution.OptU2Grover184PrepOut13
open Solution.TopIntegrationBridge
open Solution.MobiusOptSubcube163Walk
open Solution.CompactTuned162StepWalk
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

section ParamUniformClosures

variable {Var : Type} [Fintype Var] [DecidableEq Var]
  {wOuter kZeroOut : ℕ} (hkOut : kZeroOut ≤ wOuter) {mLow sUb : ℕ} (hUb : 163 ≤ sUb) {v : Var}
  {σ : Equiv.Perm (Fin (2 ^ 8))}
  {prepOutIdeal prepOutImpl : Unitary (2 ^ mOutUB wOuter)}
  {uIdx uIdxIdeal : Unitary (2 ^ 5)}
  {δOut δIdx δSelFwd δSelBwd δStep eRef : ℝ}
  {selectPure : Unitary (2 ^ nUB wOuter 20)}
  {selFwdImpl selBwdImpl : Unitary (2 ^ (nUB wOuter 20 + 11))}
  {pSelFwd pSelBwd : DynamicCircuit Var (combQubits wOuter 20 kZeroOut 16 mLow sUb)}

end ParamUniformClosures

/-! ### Subsection 4B: `0`-Scratch `Circuit 5` Specialization (`Quant56` / `Quant46`) -/

section Circuit5UniformClosures

variable {Var : Type} [Fintype Var] [DecidableEq Var]
  {wOuter kZeroOut : ℕ} (hkOut : kZeroOut ≤ wOuter) {mLow sUb : ℕ} (hUb : 163 ≤ sUb) {v : Var}
  {σ : Equiv.Perm (Fin (2 ^ 8))}
  {prepOutIdeal prepOutImpl : Unitary (2 ^ mOutUB wOuter)}
  {cMag30 : Circuit 5} {uIdxIdeal : Unitary (2 ^ 5)}
  {δOut δIdx δSelFwd δSelBwd δStep eRef : ℝ}
  {selectPure : Unitary (2 ^ nUB wOuter 20)}
  {selFwdImpl selBwdImpl : Unitary (2 ^ (nUB wOuter 20 + 11))}
  {pSelFwd pSelBwd : DynamicCircuit Var (combQubits wOuter 20 kZeroOut 16 mLow sUb)}

end Circuit5UniformClosures

section Circuit5Opt932Closures

variable {Var : Type} [Fintype Var] [DecidableEq Var] {mLow sUb : ℕ} (hUb : 163 ≤ sUb) {v : Var}
  {cMag30 : Circuit 5} {uIdxIdeal : Unitary (2 ^ 5)}
  {selectPure : Unitary (2 ^ nUB 13 20)} {selFwdImpl selBwdImpl : Unitary (2 ^ (nUB 13 20 + 11))}
  {pSelFwd pSelBwd : DynamicCircuit Var (combQubits 13 20 8 16 mLow sUb)}
  {δIdx δSelFwd δSelBwd δStep eRef : ℝ}

end Circuit5Opt932Closures

/-! ### Additional Form-B `hBE` & `Param` `Opt932` Constructors + Width `@[simp]` Lemmas -/

section ParamOpt932Closures

variable {Var : Type} [Fintype Var] [DecidableEq Var] {mLow sUb : ℕ} (hUb : 163 ≤ sUb) {v : Var}
  {uIdx uIdxIdeal : Unitary (2 ^ 5)}
  {selectPure : Unitary (2 ^ nUB 13 20)} {selFwdImpl selBwdImpl : Unitary (2 ^ (nUB 13 20 + 11))}
  {pSelFwd pSelBwd : DynamicCircuit Var (combQubits 13 20 8 16 mLow sUb)}
  {δIdx δSelFwd δSelBwd δStep eRef : ℝ}

end ParamOpt932Closures

/-! ## Section 5: Concrete `uIdx` Tiers (`2,828..2,904 T` Inner / `3,760..3,836 T` `Opt932`) -/

/-! ### Tier `Clean100` (`100 T` `uIdx` → `2904 T` Inner / `3836 T` `Opt932`) -/

section Clean100Closures

variable {Var : Type} [Fintype Var] [DecidableEq Var]
  {wOuter kZeroOut : ℕ} (hkOut : kZeroOut ≤ wOuter) {mLow sUb : ℕ} (hUb : 163 ≤ sUb) {v : Var}
  {σ : Equiv.Perm (Fin (2 ^ 8))}
  {prepOutIdeal prepOutImpl : Unitary (2 ^ mOutUB wOuter)}
  {δOut δSelFwd δSelBwd δStep eRef : ℝ}
  {selectPure : Unitary (2 ^ nUB wOuter 20)}
  {selFwdImpl selBwdImpl : Unitary (2 ^ (nUB wOuter 20 + 11))}
  {pSelFwd pSelBwd : DynamicCircuit Var (combQubits wOuter 20 kZeroOut 16 mLow sUb)}

end Clean100Closures

section Clean100Opt932Closures

variable {Var : Type} [Fintype Var] [DecidableEq Var] {mLow sUb : ℕ} (hUb : 163 ≤ sUb) {v : Var}
  {selectPure : Unitary (2 ^ nUB 13 20)} {selFwdImpl selBwdImpl : Unitary (2 ^ (nUB 13 20 + 11))}
  {pSelFwd pSelBwd : DynamicCircuit Var (combQubits 13 20 8 16 mLow sUb)}
  {δSelFwd δSelBwd δStep eRef : ℝ}

end Clean100Opt932Closures

/-! ### Tier `Clean98` (`98 T` `uIdx` → `2896 T` Inner / `3828 T` `Opt932`) -/

section Clean98Closures

variable {Var : Type} [Fintype Var] [DecidableEq Var]
  {wOuter kZeroOut : ℕ} (hkOut : kZeroOut ≤ wOuter) {mLow sUb : ℕ} (hUb : 163 ≤ sUb) {v : Var}
  {σ : Equiv.Perm (Fin (2 ^ 8))}
  {prepOutIdeal prepOutImpl : Unitary (2 ^ mOutUB wOuter)}
  {δOut δSelFwd δSelBwd δStep eRef : ℝ}
  {selectPure : Unitary (2 ^ nUB wOuter 20)}
  {selFwdImpl selBwdImpl : Unitary (2 ^ (nUB wOuter 20 + 11))}
  {pSelFwd pSelBwd : DynamicCircuit Var (combQubits wOuter 20 kZeroOut 16 mLow sUb)}

end Clean98Closures

section Clean98Opt932Closures

variable {Var : Type} [Fintype Var] [DecidableEq Var] {mLow sUb : ℕ} (hUb : 163 ≤ sUb) {v : Var}
  {selectPure : Unitary (2 ^ nUB 13 20)} {selFwdImpl selBwdImpl : Unitary (2 ^ (nUB 13 20 + 11))}
  {pSelFwd pSelBwd : DynamicCircuit Var (combQubits 13 20 8 16 mLow sUb)}
  {δSelFwd δSelBwd δStep eRef : ℝ}

end Clean98Opt932Closures

/-! ### Tier `Tight97` (`97 T` `uIdx` → `2892 T` Inner / `3824 T` `Opt932`) -/

section Tight97Closures

variable {Var : Type} [Fintype Var] [DecidableEq Var]
  {wOuter kZeroOut : ℕ} (hkOut : kZeroOut ≤ wOuter) {mLow sUb : ℕ} (hUb : 163 ≤ sUb) {v : Var}
  {σ : Equiv.Perm (Fin (2 ^ 8))}
  {prepOutIdeal prepOutImpl : Unitary (2 ^ mOutUB wOuter)}
  {δOut δSelFwd δSelBwd δStep eRef : ℝ}
  {selectPure : Unitary (2 ^ nUB wOuter 20)}
  {selFwdImpl selBwdImpl : Unitary (2 ^ (nUB wOuter 20 + 11))}
  {pSelFwd pSelBwd : DynamicCircuit Var (combQubits wOuter 20 kZeroOut 16 mLow sUb)}

end Tight97Closures

section Tight97Opt932Closures

variable {Var : Type} [Fintype Var] [DecidableEq Var] {mLow sUb : ℕ} (hUb : 163 ≤ sUb) {v : Var}
  {selectPure : Unitary (2 ^ nUB 13 20)} {selFwdImpl selBwdImpl : Unitary (2 ^ (nUB 13 20 + 11))}
  {pSelFwd pSelBwd : DynamicCircuit Var (combQubits 13 20 8 16 mLow sUb)}
  {δSelFwd δSelBwd δStep eRef : ℝ}

end Tight97Opt932Closures

/-! ### Tier `Med96` (`96 T` `uIdx` → `2888 T` Inner / `3820 T` `Opt932`) -/

section Med96Closures

variable {Var : Type} [Fintype Var] [DecidableEq Var]
  {wOuter kZeroOut : ℕ} (hkOut : kZeroOut ≤ wOuter) {mLow sUb : ℕ} (hUb : 163 ≤ sUb) {v : Var}
  {σ : Equiv.Perm (Fin (2 ^ 8))}
  {prepOutIdeal prepOutImpl : Unitary (2 ^ mOutUB wOuter)}
  {δOut δSelFwd δSelBwd δStep eRef : ℝ}
  {selectPure : Unitary (2 ^ nUB wOuter 20)}
  {selFwdImpl selBwdImpl : Unitary (2 ^ (nUB wOuter 20 + 11))}
  {pSelFwd pSelBwd : DynamicCircuit Var (combQubits wOuter 20 kZeroOut 16 mLow sUb)}

end Med96Closures

section Med96Opt932Closures

variable {Var : Type} [Fintype Var] [DecidableEq Var] {mLow sUb : ℕ} (hUb : 163 ≤ sUb) {v : Var}
  {selectPure : Unitary (2 ^ nUB 13 20)} {selFwdImpl selBwdImpl : Unitary (2 ^ (nUB 13 20 + 11))}
  {pSelFwd pSelBwd : DynamicCircuit Var (combQubits 13 20 8 16 mLow sUb)}
  {δSelFwd δSelBwd δStep eRef : ℝ}

end Med96Opt932Closures

/-! ### Tier `Opt86` (`86 T` `uIdx` → `2848 T` Inner / `3780 T` `Opt932`) -/

section Opt86Closures

variable {Var : Type} [Fintype Var] [DecidableEq Var]
  {wOuter kZeroOut : ℕ} (hkOut : kZeroOut ≤ wOuter) {mLow sUb : ℕ} (hUb : 163 ≤ sUb) {v : Var}
  {σ : Equiv.Perm (Fin (2 ^ 8))}
  {prepOutIdeal prepOutImpl : Unitary (2 ^ mOutUB wOuter)}
  {δOut δSelFwd δSelBwd δStep eRef : ℝ}
  {selectPure : Unitary (2 ^ nUB wOuter 20)}
  {selFwdImpl selBwdImpl : Unitary (2 ^ (nUB wOuter 20 + 11))}
  {pSelFwd pSelBwd : DynamicCircuit Var (combQubits wOuter 20 kZeroOut 16 mLow sUb)}

end Opt86Closures

section Opt86Opt932Closures

variable {Var : Type} [Fintype Var] [DecidableEq Var] {mLow sUb : ℕ} (hUb : 163 ≤ sUb) {v : Var}
  {selectPure : Unitary (2 ^ nUB 13 20)} {selFwdImpl selBwdImpl : Unitary (2 ^ (nUB 13 20 + 11))}
  {pSelFwd pSelBwd : DynamicCircuit Var (combQubits 13 20 8 16 mLow sUb)}
  {δSelFwd δSelBwd δStep eRef : ℝ}

end Opt86Opt932Closures

/-! ### Tier `Opt81` (`81 T` `uIdx` → `2828 T` Inner / `3760 T` `Opt932`) -/

section Opt81Closures

variable {Var : Type} [Fintype Var] [DecidableEq Var]
  {wOuter kZeroOut : ℕ} (hkOut : kZeroOut ≤ wOuter) {mLow sUb : ℕ} (hUb : 163 ≤ sUb) {v : Var}
  {σ : Equiv.Perm (Fin (2 ^ 8))}
  {prepOutIdeal prepOutImpl : Unitary (2 ^ mOutUB wOuter)}
  {δOut δSelFwd δSelBwd δStep eRef : ℝ}
  {selectPure : Unitary (2 ^ nUB wOuter 20)}
  {selFwdImpl selBwdImpl : Unitary (2 ^ (nUB wOuter 20 + 11))}
  {pSelFwd pSelBwd : DynamicCircuit Var (combQubits wOuter 20 kZeroOut 16 mLow sUb)}

end Opt81Closures

section Opt81Opt932Closures

variable {Var : Type} [Fintype Var] [DecidableEq Var] {mLow sUb : ℕ} (hUb : 163 ≤ sUb) {v : Var}
  {selectPure : Unitary (2 ^ nUB 13 20)} {selFwdImpl selBwdImpl : Unitary (2 ^ (nUB 13 20 + 11))}
  {pSelFwd pSelBwd : DynamicCircuit Var (combQubits 13 20 8 16 mLow sUb)}
  {δSelFwd δSelBwd δStep eRef : ℝ}

end Opt81Opt932Closures

end Core2504

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactStepCompact2504ZeroCmp20
