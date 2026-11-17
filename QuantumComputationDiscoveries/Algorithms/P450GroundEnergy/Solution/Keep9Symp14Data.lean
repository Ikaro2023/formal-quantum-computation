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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.HGadgetSympQrom

/-!
# Symplectic `HGadget` Witness Plans for `keep_9` (`262 T` Core) & `symp_14` (`330 T` Core)

Drop-in `HGadgetSymp14Plan` witnesses for the `9`-plane `keep_0..8` reloader (`R = 118, G = 13`,
`2 * R + 2 * G = 262 T` diagonal core, `322 T` at `33 ≤ sScr`, `366 T` at
`27 ≤ sScr`) and the `14`-plane `(alt : 5, keep : 9)` inner QROM loader (`R = 147, G = 18`,
`2 * R + 2 * G = 330 T` diagonal core, `390 T` at `33 ≤ sScr`, `434 T` at
`27 ≤ sScr`) on unrotated `P450.dfthc`.

## References
- A. Lempel, "Matrix factorization over GF(2) and trace-orthogonal bases of GF(2^n),"
  *SIAM J. Comput.* **4**(2), 175-186 (1975), DOI: 10.1137/0204014.
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  "Encoding Electronic Spectra in Quantum Circuits with Linear T Complexity,"
  *Phys. Rev. X* **8**, 041015 (2018), DOI: 10.1103/PhysRevX.8.041015.
- G. H. Low, V. Kliuchnikov, and L. Schaeffer, "Trading T gates for dirty qubits in state
  preparation and unitary synthesis," *Quantum* **8**, 1375 (2024),
  DOI: 10.22331/q-2024-06-17-1375.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OptKeep9Symp14Data
open QuantumComputation.Specs QuantumComputation.Specs.P450

section OptWitnesses

open Operator QProg Matrix Circuit Real HermitianMat BlockEncodingCore BlockEncodingCircuit
  QuantumComputation QuantumComputation.Specs QuantumComputation.Specs.P450
  CoherentAlias AliasPrep Mobius126OneHot MidReflCtxRetain
  StepBound148Borrow Tuned162ScheduledSympQrom21 Tuned162StepSympAnfQrom21
  StepAnfAndCoin14Core StepKeep9Symp14Data HGadgetSympQrom
open _root_.Function (update)
open scoped BigOperators

local instance (priority := 1000000) instNeZeroTwoPowOpt (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

/-! ## Section 1: Generic Array-Backed `Symp14Spec` Kernel Equivalence Helpers -/

/-- Single `32`-bit step term from packed step arrays `(sA, sB, sC, sD, sW)` at `(r, k, idx)`. -/
def arrRow32StepTerm (sA sB sC sD sW : Array ℕ) (r : ℕ) (k : Fin 14) (idx : ℕ) : ℕ :=
  if (sW.getD idx 0).testBit k.val then
    (bcast32_14 ((sA.getD idx 0).testBit r) ^^^ extMask32_14 (sC.getD idx 0)) &&&
      (bcast32_14 ((sB.getD idx 0).testBit r) ^^^ extMask32_14 (sD.getD idx 0))
  else 0

/-- Full `32`-bit plane word evaluated from `(rd, cd, sA, sB, sC, sD, sW)` at `(r, k)`. -/
def arrEvalRow32AtNat (R : ℕ) (rd cd sA sB sC sD sW : Array ℕ) (r : ℕ) (k : Fin 14) : ℕ :=
  bcast32_14 ((rd.getD k.val 0).testBit r) ^^^
    extMask32_14 (cd.getD k.val 0) ^^^
    foldRangeXor14 (arrRow32StepTerm sA sB sC sD sW r k) 0 R

/-- Word-parallel `14`-plane `32`-bit row evaluator over packed arrays. -/
def arrEvalAllPlanesRow32 (rd cd sA sB sC sD sW : Array ℕ) (r : ℕ) : List ℕ :=
  withForced14NatList (cd.toList.map extMask32_14) fun cd32L ↦
  withForced14NatList (initRowAccs32_14 r rd.toList cd32L) fun initAccs ↦
    row32AllLoop_14 r initAccs sA.toList sB.toList
      (sC.toList.map extMask32_14) (sD.toList.map extMask32_14) sW.toList

/-- Single `32`-bit `none`-sector (`rc ∈ {126, 127}`) step term at `(k, idx)`. -/
def arrNone32StepTerm (sC sD sW : Array ℕ) (k : Fin 14) (idx : ℕ) : ℕ :=
  if (sW.getD idx 0).testBit k.val then
    extMask32_14 (sC.getD idx 0) &&& extMask32_14 (sD.getD idx 0)
  else 0

/-- Kernel `none`-sector checker verifying `0` output across all `14` planes and `32` columns. -/
def arrCheckNone14 (cd sC sD sW : Array ℕ) : Bool :=
  withForced14NatList (cd.toList.map extMask32_14) fun cd32L ↦
  withForced14NatList (sC.toList.map extMask32_14) fun c32L ↦
  withForced14NatList (sD.toList.map extMask32_14) fun d32L ↦
  withForced14NatList sW.toList fun wL ↦
    allLt14Data 14 fun k ↦ Nat.beq (none32Loop_14 k (nthZero14 cd32L k) c32L d32L wL) 0

/-- Zero planes `0..4` of a `14`-plane `32`-bit word list (`keep_9` mask). -/
def maskKeep9Words : List ℕ → ℕ → List ℕ
  | [], _ => []
  | w :: ws, i => (if i < 5 then 0 else w) :: maskKeep9Words ws (i + 1)

/-- Pure Boolean equality on `List ℕ` (avoids `Decidable` proof terms in kernel WHNF). -/
def listNatBeq : List ℕ → List ℕ → Bool
  | [], [] => true
  | x :: xs, y :: ys => Nat.beq x y && listNatBeq xs ys
  | _, _ => false

theorem listNatBeq_eq_true : ∀ {xs ys : List ℕ}, listNatBeq xs ys = true → xs = ys
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
      rw [listNatBeq, Bool.and_eq_true, Nat.beq_eq] at h
      exact congrArg₂ List.cons h.1 (listNatBeq_eq_true h.2)

/-- Check rows `[lo, lo + cnt)` with `toList` and `extMask32_14` hoisted once per chunk. -/
def checkRowsChunk (lo cnt : ℕ) (rd cd sA sB sC sD sW : Array ℕ) (mask5 : Bool) : Bool :=
  OuterWeights.withForcedList rd.toList fun rd1L ↦
  withForced14NatList (cd.toList.map extMask32_14) fun cd1L ↦
  OuterWeights.withForcedList sA.toList fun a1L ↦
  OuterWeights.withForcedList sB.toList fun b1L ↦
  withForced14NatList (sC.toList.map extMask32_14) fun c1L ↦
  withForced14NatList (sD.toList.map extMask32_14) fun d1L ↦
  withForced14NatList sW.toList fun w1L ↦
  OuterWeights.withForcedList keep9RowDiagMasks.toList fun rd2L ↦
  withForced14NatList (keep9ColDiagMasks.toList.map extMask32_14) fun cd2L ↦
  OuterWeights.withForcedList keep9StepAMasks.toList fun a2L ↦
  OuterWeights.withForcedList keep9StepBMasks.toList fun b2L ↦
  withForced14NatList (keep9StepCMasks.toList.map extMask32_14) fun c2L ↦
  withForced14NatList (keep9StepDMasks.toList.map extMask32_14) fun d2L ↦
  withForced14NatList keep9StepWMasks.toList fun w2L ↦
    allLt14Data cnt fun d ↦
      let r := lo + d
      withForced14NatList (initRowAccs32_14 r rd1L cd1L) fun acc1 ↦
      withForced14NatList (row32AllLoop_14 r acc1 a1L b1L c1L d1L w1L) fun out1 ↦
      withForced14NatList (initRowAccs32_14 r rd2L cd2L) fun acc2 ↦
      withForced14NatList (row32AllLoop_14 r acc2 a2L b2L c2L d2L w2L) fun out2 ↦
        listNatBeq out1 (if mask5 then maskKeep9Words out2 0 else out2)

theorem checkRowsChunk_spec {lo cnt : ℕ} {rd cd sA sB sC sD sW : Array ℕ} {mask5 : Bool}
    (hok : checkRowsChunk lo cnt rd cd sA sB sC sD sW mask5 = true)
    {r : ℕ} (hlo : lo ≤ r) (hhi : r < lo + cnt) :
    arrEvalAllPlanesRow32 rd cd sA sB sC sD sW r =
      if mask5 then maskKeep9Words (evalAllPlanesRow32_14 r) 0
      else evalAllPlanesRow32_14 r := by
  unfold checkRowsChunk at hok
  simp only [withForcedList_eq_14data, withForced14NatList_eq] at hok
  have hd := allLt14Data_spec hok (r - lo) (by omega)
  simp only [show lo + (r - lo) = r by omega] at hd
  have heq := listNatBeq_eq_true hd
  simpa only [arrEvalAllPlanesRow32, evalAllPlanesRow32_14, withForced14NatList_eq] using heq

theorem checkRows126_of_parts6 {rd cd sA sB sC sD sW : Array ℕ} {mask5 : Bool}
    (h0 : checkRowsChunk 0 21 rd cd sA sB sC sD sW mask5 = true)
    (h1 : checkRowsChunk 21 21 rd cd sA sB sC sD sW mask5 = true)
    (h2 : checkRowsChunk 42 21 rd cd sA sB sC sD sW mask5 = true)
    (h3 : checkRowsChunk 63 21 rd cd sA sB sC sD sW mask5 = true)
    (h4 : checkRowsChunk 84 21 rd cd sA sB sC sD sW mask5 = true)
    (h5 : checkRowsChunk 105 21 rd cd sA sB sC sD sW mask5 = true)
    (rc : Fin 126) :
    arrEvalAllPlanesRow32 rd cd sA sB sC sD sW rc.val =
      if mask5 then maskKeep9Words (evalAllPlanesRow32_14 rc.val) 0
      else evalAllPlanesRow32_14 rc.val := by
  have hlt := rc.isLt
  by_cases c1 : rc.val < 21
  · exact checkRowsChunk_spec h0 (Nat.zero_le _) c1
  · by_cases c2 : rc.val < 42
    · exact checkRowsChunk_spec h1 (by omega) c2
    · by_cases c3 : rc.val < 63
      · exact checkRowsChunk_spec h2 (by omega) c3
      · by_cases c4 : rc.val < 84
        · exact checkRowsChunk_spec h3 (by omega) c4
        · by_cases c5 : rc.val < 105
          · exact checkRowsChunk_spec h4 (by omega) c5
          · exact checkRowsChunk_spec h5 (by omega) (by omega)

theorem arrInitRowAccs32_eq_ofFn {rd cd : Array ℕ} (hrd : rd.size = 14) (hcd : cd.size = 14)
    (r : ℕ) :
    ∀ (n p : ℕ), p + n = 14 →
      initRowAccs32_14 r (rd.toList.drop p) ((cd.toList.drop p).map extMask32_14) =
      List.ofFn (fun i : Fin n ↦
        bcast32_14 ((rd.getD (p + i.val) 0).testBit r) ^^^
          extMask32_14 (cd.getD (p + i.val) 0))
  | 0, p, hp => by
      have hp14 : p = 14 := by omega
      subst hp14
      have hL : rd.toList.length = 14 := hrd
      rw [List.drop_eq_nil_of_le (by omega)]
      rfl
  | n + 1, p, hp => by
      have hlt : p < 14 := by omega
      rw [array_toList_drop_succ_14 rd (hrd.symm ▸ hlt),
        array_toList_drop_succ_14 cd (hcd.symm ▸ hlt), List.map_cons]
      dsimp only [initRowAccs32_14]
      rw [withForced14Nat_eq, arrInitRowAccs32_eq_ofFn hrd hcd r n (p + 1) (by omega),
        List.ofFn_succ]
      refine congrArg₂ List.cons (by simp) (congrArg List.ofFn (funext fun i ↦ ?_))
      dsimp only [Fin.val_succ]
      rw [show p + 1 + i.val = p + (i.val + 1) by omega]

theorem arrRow32AllLoop_eq {R : ℕ} {sA sB sC sD sW : Array ℕ}
    (hsA : sA.size = R) (hsB : sB.size = R) (hsC : sC.size = R)
    (hsD : sD.size = R) (hsW : sW.size = R) (r : ℕ) :
    ∀ (cnt off : ℕ) (f : Fin 14 → ℕ), off + cnt = R →
      row32AllLoop_14 r (List.ofFn f)
        (sA.toList.drop off) (sB.toList.drop off)
        ((sC.toList.drop off).map extMask32_14)
        ((sD.toList.drop off).map extMask32_14)
        (sW.toList.drop off) =
      List.ofFn (fun k : Fin 14 ↦
        f k ^^^ foldRangeXor14 (arrRow32StepTerm sA sB sC sD sW r k) off cnt)
  | 0, off, f, hob => by
      have hL : sA.toList.length = R := hsA
      rw [List.drop_eq_nil_of_le (by omega)]
      dsimp only [row32AllLoop_14, foldRangeXor14]
      simp only [Nat.xor_zero]
  | m + 1, off, f, hob => by
      have hlt : off < R := by omega
      rw [array_toList_drop_succ_14 sA (hsA.symm ▸ hlt),
        array_toList_drop_succ_14 sB (hsB.symm ▸ hlt),
        array_toList_drop_succ_14 sC (hsC.symm ▸ hlt),
        array_toList_drop_succ_14 sD (hsD.symm ▸ hlt),
        array_toList_drop_succ_14 sW (hsW.symm ▸ hlt),
        List.map_cons, List.map_cons]
      dsimp only [row32AllLoop_14]
      rw [withForced14Nat_eq, withForced14NatList_eq, xorMask14List_ofFn]
      have hacc : (fun k : Fin 14 ↦
          if (sW.getD off 0).testBit (0 + k.val) then
            f k ^^^ ((bcast32_14 ((sA.getD off 0).testBit r) ^^^
                extMask32_14 (sC.getD off 0)) &&&
              (bcast32_14 ((sB.getD off 0).testBit r) ^^^
                extMask32_14 (sD.getD off 0)))
          else f k) = (fun k : Fin 14 ↦ f k ^^^ arrRow32StepTerm sA sB sC sD sW r k off) := by
        funext k
        rw [Nat.zero_add]
        dsimp only [arrRow32StepTerm]
        split_ifs <;> simp
      rw [hacc, arrRow32AllLoop_eq hsA hsB hsC hsD hsW r m (off + 1) _ (by omega)]
      congr 1
      funext k
      rw [Nat.xor_assoc, ← foldRangeXor14_succ_left]

theorem arrEvalAllPlanesRow32_eq_ofFn {R : ℕ} {rd cd sA sB sC sD sW : Array ℕ}
    (hrd : rd.size = 14) (hcd : cd.size = 14)
    (hsA : sA.size = R) (hsB : sB.size = R) (hsC : sC.size = R)
    (hsD : sD.size = R) (hsW : sW.size = R) (r : ℕ) :
    arrEvalAllPlanesRow32 rd cd sA sB sC sD sW r =
      List.ofFn (arrEvalRow32AtNat R rd cd sA sB sC sD sW r) := by
  dsimp only [arrEvalAllPlanesRow32]
  rw [withForced14NatList_eq, withForced14NatList_eq]
  have hinit : initRowAccs32_14 r rd.toList (cd.toList.map extMask32_14) =
      List.ofFn (fun i : Fin 14 ↦
        bcast32_14 ((rd.getD i.val 0).testBit r) ^^^ extMask32_14 (cd.getD i.val 0)) := by
    simpa only [List.drop_zero, Nat.zero_add] using arrInitRowAccs32_eq_ofFn hrd hcd r 14 0 rfl
  have hloop := arrRow32AllLoop_eq hsA hsB hsC hsD hsW r R 0
    (fun i : Fin 14 ↦
      bcast32_14 ((rd.getD i.val 0).testBit r) ^^^ extMask32_14 (cd.getD i.val 0))
    (Nat.zero_add R)
  simp only [List.drop_zero] at hloop
  rw [hinit, hloop]
  rfl

theorem arrNone32Loop_eq {R : ℕ} {sC sD sW : Array ℕ}
    (hsC : sC.size = R) (hsD : sD.size = R) (hsW : sW.size = R) (k : Fin 14) :
    ∀ (cnt off acc : ℕ), off + cnt = R →
      none32Loop_14 k.val acc
        ((sC.toList.drop off).map extMask32_14)
        ((sD.toList.drop off).map extMask32_14)
        (sW.toList.drop off) =
      acc ^^^ foldRangeXor14 (arrNone32StepTerm sC sD sW k) off cnt
  | 0, off, acc, hob => by
      have hL : sC.toList.length = R := hsC
      rw [List.drop_eq_nil_of_le (by omega), foldRangeXor14, Nat.xor_zero]
      rfl
  | m + 1, off, acc, hob => by
      have hlt : off < R := by omega
      rw [array_toList_drop_succ_14 sC (hsC.symm ▸ hlt),
        array_toList_drop_succ_14 sD (hsD.symm ▸ hlt),
        array_toList_drop_succ_14 sW (hsW.symm ▸ hlt),
        List.map_cons, List.map_cons]
      dsimp only [none32Loop_14]
      rw [withForced14Nat_eq]
      have hacc : (if (sW.getD off 0).testBit k.val then
          acc ^^^ (extMask32_14 (sC.getD off 0) &&& extMask32_14 (sD.getD off 0))
        else acc) = acc ^^^ arrNone32StepTerm sC sD sW k off := by
        dsimp only [arrNone32StepTerm]
        split_ifs <;> simp
      rw [hacc, arrNone32Loop_eq hsC hsD hsW k m (off + 1) _ (by omega),
        Nat.xor_assoc, ← foldRangeXor14_succ_left]

theorem arrCheckPivot_drop {R : ℕ} {sW sP : Array ℕ} (hsW : sW.size = R) (hsP : sP.size = R) :
    ∀ (cnt off : ℕ), off + cnt = R →
      checkPivot14List (sW.toList.drop off) (sP.toList.drop off) = true →
      ∀ i, off ≤ i → i < R → (sW.getD i 0).testBit ((sP.getD i 0) % 14) = true
  | 0, _, _, _, _, hlo, hhi => absurd hhi (by omega)
  | m + 1, off, hob, h, i, hlo, hhi => by
      have hlt : off < R := by omega
      rw [array_toList_drop_succ_14 sW (hsW.symm ▸ hlt),
        array_toList_drop_succ_14 sP (hsP.symm ▸ hlt),
        checkPivot14List, Bool.and_eq_true] at h
      by_cases heq : i = off
      · subst heq
        exact h.1
      · exact arrCheckPivot_drop hsW hsP m (off + 1) (by omega) h.2 i (by omega) hhi

/-- Construct `Symp14Spec R` from packed integer arrays and a kernel pivot check. -/
def symp14SpecOfArrays (R : ℕ) (rd cd sA sB sC sD sW sP : Array ℕ)
    (hsW : sW.size = R) (hsP : sP.size = R)
    (hpiv : OuterWeights.withForcedList sW.toList (fun wL ↦
      OuterWeights.withForcedList sP.toList (fun pL ↦ checkPivot14List wL pL)) = true) :
    Symp14Spec R where
  rowDiag k rc := (rd.getD k.val 0).testBit rc.val
  colDiag k b := (cd.getD k.val 0).testBit b.val
  stepA m rc := (sA.getD m.val 0).testBit rc.val
  stepB m rc := (sB.getD m.val 0).testBit rc.val
  stepC m b := (sC.getD m.val 0).testBit b.val
  stepD m b := (sD.getD m.val 0).testBit b.val
  stepW m k := (sW.getD m.val 0).testBit k.val
  stepPivot m := ⟨(sP.getD m.val 0) % 14, Nat.mod_lt _ (by decide)⟩
  stepW_pivot m := by
    have hok := hpiv
    rw [withForcedList_eq_14data, withForcedList_eq_14data] at hok
    exact arrCheckPivot_drop hsW hsP R 0 (Nat.zero_add R)
      (by simpa only [List.drop_zero] using hok) m.val (Nat.zero_le _) m.isLt

theorem testBit_foldRangeXor14_arrRow32 {R : ℕ} (rd cd sA sB sC sD sW sP : Array ℕ)
    (hsW : sW.size = R) (hsP : sP.size = R) (hpiv)
    (rc : Fin 126) (k : Fin 14) (x : Fin (2 ^ 5)) :
    ∀ (m : ℕ) (hm : m ≤ R),
      (foldRangeXor14 (arrRow32StepTerm sA sB sC sD sW rc.val k) 0 m).testBit x.val =
        (symp14SpecOfArrays R rd cd sA sB sC sD sW sP hsW hsP hpiv).stepXorBool
          k (some rc) x m hm
  | 0, _ => Nat.zero_testBit x.val
  | m + 1, hm => by
      rw [foldRangeXor14, Nat.zero_add, Nat.testBit_xor,
        testBit_foldRangeXor14_arrRow32 rd cd sA sB sC sD sW sP hsW hsP hpiv rc k x m
          (Nat.le_of_succ_le hm),
        Symp14Spec.stepXorBool]
      dsimp only [arrRow32StepTerm]
      have hW : (symp14SpecOfArrays R rd cd sA sB sC sD sW sP hsW hsP hpiv).stepW ⟨m, hm⟩ k =
          (sW.getD m 0).testBit k.val := rfl
      rw [hW]
      by_cases hw : (sW.getD m 0).testBit k.val = true
      · simp only [hw, ↓reduceIte]
        dsimp only [symp14SpecOfArrays]
        rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_xor,
          testBit_bcast32_14, testBit_bcast32_14, testBit_extMask32_14, testBit_extMask32_14]
      · simp only [hw, Bool.false_eq_true, ↓reduceIte, Nat.zero_testBit, Bool.xor_false]

theorem testBit_arrEvalRow32AtNat {R : ℕ} (rd cd sA sB sC sD sW sP : Array ℕ)
    (hsW : sW.size = R) (hsP : sP.size = R) (hpiv)
    (rc : Fin 126) (k : Fin 14) (x : Fin (2 ^ 5)) :
    (arrEvalRow32AtNat R rd cd sA sB sC sD sW rc.val k).testBit x.val =
      (symp14SpecOfArrays R rd cd sA sB sC sD sW sP hsW hsP hpiv).evalBool k (some rc) x := by
  unfold arrEvalRow32AtNat Symp14Spec.evalBool
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_bcast32_14, testBit_extMask32_14,
    testBit_foldRangeXor14_arrRow32 rd cd sA sB sC sD sW sP hsW hsP hpiv rc k x R le_rfl]
  rfl

theorem testBit_foldRangeXor14_arrNone32 {R : ℕ} (rd cd sA sB sC sD sW sP : Array ℕ)
    (hsW : sW.size = R) (hsP : sP.size = R) (hpiv)
    (k : Fin 14) (x : Fin (2 ^ 5)) :
    ∀ (m : ℕ) (hm : m ≤ R),
      (foldRangeXor14 (arrNone32StepTerm sC sD sW k) 0 m).testBit x.val =
        (symp14SpecOfArrays R rd cd sA sB sC sD sW sP hsW hsP hpiv).stepXorBool k none x m hm
  | 0, _ => Nat.zero_testBit x.val
  | m + 1, hm => by
      rw [foldRangeXor14, Nat.zero_add, Nat.testBit_xor,
        testBit_foldRangeXor14_arrNone32 rd cd sA sB sC sD sW sP hsW hsP hpiv k x m
          (Nat.le_of_succ_le hm),
        Symp14Spec.stepXorBool]
      dsimp only [arrNone32StepTerm]
      have hW : (symp14SpecOfArrays R rd cd sA sB sC sD sW sP hsW hsP hpiv).stepW ⟨m, hm⟩ k =
          (sW.getD m 0).testBit k.val := rfl
      rw [hW]
      by_cases hw : (sW.getD m 0).testBit k.val = true
      · simp only [hw, ↓reduceIte]
        dsimp only [symp14SpecOfArrays]
        rw [Nat.testBit_and, testBit_extMask32_14, testBit_extMask32_14,
          Bool.false_xor, Bool.false_xor]
      · simp only [hw, Bool.false_eq_true, ↓reduceIte, Nat.zero_testBit, Bool.xor_false]

theorem symp14SpecOfArrays_evalBool_none {R : ℕ} (rd cd sA sB sC sD sW sP : Array ℕ)
    (hcd : cd.size = 14) (hsC : sC.size = R) (hsD : sD.size = R)
    (hsW : sW.size = R) (hsP : sP.size = R) (hpiv)
    (hnone : arrCheckNone14 cd sC sD sW = true) (k : Fin 14) (x : Fin (2 ^ 5)) :
    (symp14SpecOfArrays R rd cd sA sB sC sD sW sP hsW hsP hpiv).evalBool k none x = false := by
  have hok := hnone
  unfold arrCheckNone14 at hok
  rw [withForced14NatList_eq, withForced14NatList_eq, withForced14NatList_eq,
    withForced14NatList_eq] at hok
  have hk := allLt14Data_spec hok k.val k.isLt
  rw [Nat.beq_eq] at hk
  have hcd_eq : nthZero14 (cd.toList.map extMask32_14) k.val = extMask32_14 (cd.getD k.val 0) :=
    (nthZero14_map extMask32_14 cd.toList (by
      have hL : cd.toList.length = 14 := hcd
      have := k.isLt
      omega)).trans
      (congrArg extMask32_14 (nthZero14_toList cd (hcd.symm ▸ k.isLt)))
  rw [hcd_eq] at hk
  have hloop := arrNone32Loop_eq hsC hsD hsW k R 0 (extMask32_14 (cd.getD k.val 0))
    (Nat.zero_add R)
  simp only [List.drop_zero] at hloop
  rw [hloop] at hk
  have hbit := congrArg (fun n ↦ n.testBit x.val) hk
  rw [Nat.testBit_xor, testBit_extMask32_14,
    testBit_foldRangeXor14_arrNone32 rd cd sA sB sC sD sW sP hsW hsP hpiv k x R le_rfl,
    Nat.zero_testBit] at hbit
  unfold Symp14Spec.evalBool
  dsimp only [symp14SpecOfArrays]
  rw [Bool.false_xor]
  exact hbit

/-! ## Section 2: `keep_9` Reloader Witness (`R = 118, G = 13, 2R + 2G = 262 T`) -/

/-! ## Section 3: `symp_14` Full Loader Witness (`R = 147, G = 18, 2R + 2G = 330 T`) -/

/-- `14` `126`-bit row-diagonal masks for `optSymp14`. -/
def optSymp14RowDiag : Array ℕ := #[
  0xb9a4ff1c2433b2ef6b7dc2a1817f6d7, 0x19c1eeeb4621649532b597b8981e7f32,
  0x15ff9e899f52be75c6e56318bb07a738, 0x55a7df6164e04d641fe0cfb7f197b6,
  0x30ac36dc21a9cd48e4a78c926afde5b8, 0x2de26a7a291deb24b5cc1e8cb3ebff71,
  0x3404c32f2b759adc7659fa09880751d, 0x2edff4be1f49a84fd6f2fb17128fc5bd,
  0x2a82f0a6af544b783f3be14a5e366f94, 0x257d65fdaf70d42979054100c25d1f92,
  0x408a3ca0bf9aa4910c509d06a5684fb, 0xe3e0f37c9065d29fd525d8482c827e3,
  0x48ce79ba2d2e1ff90b547fd129360d5, 0x31bb599058d47b0fd832ed9feacf771d
]

/-- `14` `30`-bit column-diagonal masks for `optSymp14`. -/
def optSymp14ColDiag : Array ℕ := #[
  854245294, 289411074, 580959526, 525000, 318276524, 465309696, 967615706, 203134532, 591547480,
  0, 574885854, 584253440, 945069004, 636899970
]

/-- `147` `126`-bit `A` row masks for `optSymp14`. -/
def optSymp14StepA : Array ℕ := #[
  0x12231827ec958d43d91fb13b0f602dd6, 0x3810ed95cff4c0069e53e5d69ee07131,
  0x12040011120d2c6d560e290764a18438, 0x762c20fa106c5b6e67451e79469c3c,
  0x207fce160d7b75baa831dd9a80b07fc6, 0x3a68e7a8760e14a9be3f935d95fa2fed,
  0x2e0bba294910244aa39e97a583ccaa4, 0x366225a387a0890fc0319b1a0cc85ba9,
  0x6de238cead00b5b1a9193e63d6ebd86, 0x4cff8a9b455e803aa94f1b4ba9cdfab,
  0xb64b3b4cb4baf9192f5851711c48d3b, 0x372cf5ba0d4a0ec1aaee2dc1cb405f0a,
  0x1ce7de9b9f6ed2ce26124053d81ab45c, 0x2e3dc3940ccae43972ed5ef268155dc6,
  0x1e12d315c0613ccd31fc5d7f06ccdf04, 0x2f07e1129075344dfac5d5cd9bd9d429,
  0x11a4ab07a89122481d4a4f318d487fe2, 0x3be3118f55e900d41d1b0dcd45745b05,
  0x2e84a9bf8229c99d4734f9cd815e1ef6, 0x18243c923d099d62d7a1720c3f549771,
  0x34b555892988fed4ed593cd20f89944e, 0x2e2f0b1f20e5a6b521bd3b1bcc5f6d30,
  0x2b811062aa2e96a39b5589da2233b21, 0x16811902f0ad8f235b4e8341814eff34,
  0x18ae89b4dbec3d4b6f35b782ff127cb9, 0x2284bab9d21d38210d36bf10491e9196,
  0x3d8cc00bdc43ac7dfa0b01da8196de0b, 0x2b96f13604cb52add6dfe2555803ae07,
  0x379a41a44a2625592978598855e517fa, 0x25d59dde144576c13f08aa3d7f8d171c,
  0x2aab3a26e0d6cbed2ecf10cfa97bd15a, 0x21e1e8f062860a96706005ada9bbf821,
  0x20f6b0fb501beb946c61eb1dcafdda9d, 0x4686a216963e5784670cb121294dfb3,
  0x23a360d84c085438202e18f7a705501, 0x182ef33c5c41796f8c666dc2eb57a474,
  0xdf7beebba885133932887fd53dd9b45, 0x203ddc03a4f97f8660524796db3aed66,
  0x3a24af62de8e20b3ea00f286e4689d13, 0x26a545f65d4b944d9c6309071a39aff9,
  0x212831e7fba892b12da7c6ef51e7cd2d, 0x9a79ea875c7a24cb506524a7fda665b,
  0x3cb9bfac21936664c348d53c0a8b4870, 0x150aa80876ee67ee7ea53626ae3a519a,
  0x232858291097f96fbff4cafb67df593d, 0x286a7f1db91f8b7210ce1ce40e233ed6,
  0x2cb104a9c219d2b28e9d00b46e7d3bfe, 0x2dc00714105ff2f13bfdae5d7ad600c4,
  0x2b150c05a970b451edd114f018af5566, 0x16c2550b7c8d45efadf97947f772e438,
  0x2cedecc4f4fc416e3da60c3aa0a781d5, 0x1e34d4f0e02b507a9449971b3e83370e,
  0x2db1dc58caeca67cb609d5fc9265dd42, 0xc1e477bd966d21c0a62a0e65b7843c6,
  0x362a5103eb228a40b1ae1842782ec718, 0x2f3d58cbabce507fc050700abfd651b9,
  0x21d056bb6108756042ced4654b4c95d5, 0x1359792ee4a65405abb49ab7b72c033a,
  0x256d8b5236e4cbd3667be26414f0dfa0, 0x3b01825fcc64ec12d6a3a58a752ae4c6,
  0x97d009a0455b0cb18c8378c403aa46f, 0x26a67f55eff4f2696e8d49abec3501c9,
  0x3d22fb37da04698d76bfac19c98acc22, 0x2b23028ceadcb33dbefe80b23295167b,
  0x20c2a571dffe180b1f71a1b47d84dd19, 0x33a908456b8d5e9b9b51974bec8a40b0,
  0x5411bc14e69633708503e30b023496b, 0x15cdca55e0c08ecbb5109cbb28555a0f,
  0x15cf5047a3f7c8a0c7a4fd6b74c96222, 0x1ccd25b10d33a5259b1348d954916b11,
  0x334a5da5d9049ddda7169d0d49fe6085, 0xf341747e4192e4708f2d591e4b6caa8,
  0x3e5ff47330eb5ad2f341a15c0a998e9d, 0x3f26346ffae20164159fd9f84404e6e9,
  0x60bf76079de9751c3fc4d641838a044, 0x2297930c8c3b1130d40d02d443988261,
  0xc9a394fd320b035096d051558d5eb26, 0x1eaacd26b753a4314d6900c6dd70104f,
  0x108ada750f9cdf0457277dd5fee7f173, 0xe04cd26357bb443bd23620f7523bfbd,
  0x3113baad6b170585e22e4c4147e2084a, 0x1d4fde56b2aec5ab03704afe1dd03447,
  0x33dd245449c3a4e54a2931093be2035e, 0x2b0bfaa0e00356e401da85573a2255a,
  0x581f0de86df3805445de50158ff6f53, 0xb5bd096960a042150702006bb73e44f,
  0x30d557228632f80560cdd5115b6119c2, 0xa1d9da0039a2c51d6a99fdc5fc7787c,
  0x1616d90caf376f8a34674b0b901d9b6a, 0xbdb6a05b24f1e800876c584adfe9385,
  0x29a664bf19b92df4bbc202b139e7f27e, 0x33d9efb7b1698eeeea614dbca479abda,
  0x1c0e3b5f43207db9c3602809354f7977, 0x7661a8ab81b57833b09bbba5d01390a,
  0x294ce90d1c6f05a2c26ae1806f7489b3, 0x3b52738adafc86b87addf412949442fb,
  0x242480bd6b662e5f71234a597c90116b, 0x1eebee59a77a42d5eb3fc2dff2fcedbb,
  0x210bb90a23e7c5dc647806fa03250be1, 0x288298152387fab79c25e5fb475149fb,
  0x1791f363c8dfd04dbf43450400cea7c2, 0x1eb6f9f189c873dffadc14ca766b7246,
  0x193ee2fff568cda27e74b5a138205c2c, 0x2e4c99893c68c1ffe9c660dcee65d8d4,
  0x337d45145b51d81c5c51e09a14743d16, 0x31ecb979ae03781180c72dcc265c801e,
  0x3b4f98d5b4eef3adbffd4a4f19895781, 0x156abe05db252da50c8993cc261a5323,
  0x2c4372572e2773442e0265c28c83797d, 0x168b9b5599366fb51c0948631fdd516d,
  0xdcfdac279d777b20b40e51b5a1462f6, 0x32aa1669f5717d2c8088a59dc9966807,
  0x17d04760dad434a72d757b0f28279685, 0x1bbe497eab81fa43b454312b7bbffa45,
  0x1b1d5405111da0bb2e5b47942c5a4092, 0x2ed5ea53689abe83b413a6925dd8d2b5,
  0x42cbeefb12a6617cf29e2ac5965135b, 0x207282d98bae6684bfdb0b542918f405,
  0x5b9733139c77254902e39650971b401, 0x34a339146b816a2e655ab7e1f76788e1,
  0x26072065dec516591e6d039df54e0923, 0xbf4cc40b76d59680add25e1bbe068fb,
  0x98aa1dcefa55b133087e2ef1439619f, 0x1288cf76ff8a6a803d1eea53e310267e,
  0x9b69281d11f32590ae52190e61a51ad, 0x12fda981384a04b33e72302f973e8c99,
  0x2433ed5e214c563588a4bfb7631f1c0f, 0x8e20c0d4bf1bdd28e52eca22d63b842,
  0x2dbede88eee1e0d40a8026af2a21ecc9, 0x86b9912288beda1ad338ac91fbe5bd3,
  0x324afda083c1ca297b04682ec8afaa66, 0x1b6a70d942028f09a12ecbbce9b52211,
  0xac0e49512ecdbebd15e2c602c3de044, 0x3a6490447524dcad8ea39d944bad9c40,
  0x136487548a54e9ef9bd3f74653fac9a2, 0x27be34de29e60a265db3e22a5f094842,
  0x3269100512b85188172d2e218ddb13bf, 0x265b6ca86fee6df8bf8390537cd5f367,
  0x23c870ce8a15161b466df42e14787387, 0x331d3f542745b9d99a064ee955ec914f,
  0x3df27d1550251df0a7ac5467b8d3540b, 0x66d7d8c8b8c400b5d5ca86e8ac63dc,
  0x3142973d83777001db0aebfb3fbd433f, 0x3473ee58ff1336ca4e0933400626ace7,
  0x162b471375ec52144aea7b5112c023c8, 0x196f99679e693069086453e436b30349,
  0x1a310d1d4b1b6fa33ea0268878b21016
]

/-- `147` `126`-bit `B` row masks for `optSymp14`. -/
def optSymp14StepB : Array ℕ := #[
  0x303cd60e75fa78aa745ee8ac1e662a3c, 0x2a19daa67c0ebcf0851d6f3ec693cc37,
  0x200f4797d85bb1c2bb78cac2d0fda3d5, 0x1865e8bec57d052881055896137aff08,
  0x204d472c5aaa9cc38165bd5e81025dc2, 0x102d891b8ca374d0e85335d0f6da61cf,
  0x210a38beb63b0bced2d3967a3e368f93, 0x254f502bbc20c20110f2b001df5d4a6a,
  0x21d21082ed50234248593b4266e7147a, 0x294fe48cd444cc1b58359302e101aefc,
  0x127ed5062a74065c02b0795c32b16b0d, 0x1bb72806c1c18e46a08042ed323b45f0,
  0x2858e9bc170fe2551779ce11bcf1617a, 0x29cf60b0abbe97c35a14adf2eab6a0fd,
  0x33254e3d5a54e39a96501a565ce82a6c, 0x2f17602c0164d63565ee7db8f7e17f78,
  0x1233989e992f9625e4592c7eac9ae64e, 0x27c86e233880ea27b6f5fd540dd24674,
  0x1e85250390a3a76b5665e1fe930b81c5, 0x1729009b8ebb848bdbe2d3f0ac959f01,
  0x1f349481f826671a8f915eea417b59d4, 0x3a30489dd2846768935cda8dab75e66c,
  0x18acc89f09a3b87c2fc212a403e038a2, 0x251a7bb25ad76c2a19c9f44c38084949,
  0x23e220054320c5198e00568a52c72cb3, 0x314cbbb4c39d37105d38381d7972c564,
  0x9fd9d1273b99e95dcdf69d78fed3565, 0x397d09128b5bd7e34219190d3e32bbb4,
  0x22b1b41ac13cf43b960822000fdb840c, 0x3d53f7bdacebc1f37abb808208925d1d,
  0x2262b58558b06bfc8ad296d1588ff2cb, 0x1b6dde865a2d7376b81cb7bd5f93d883,
  0x352fdab32b5f6105696c70edd71bce0d, 0x2414c745d1c324fc0a24ba5b4f7169b6,
  0x1d9a3b915874b3b26a22c3ae21edd80a, 0x3edff5193115d5d6485ae35fff4523b9,
  0xe918e601cd62de32c713d709dbe3c30, 0x23716db408024059b084aeefd7957df7,
  0x3202281f98742819681d453f22512b19, 0x1acfff8057d203f70ced29f857edee36,
  0xea6d07d7368226608aabb010ea90bf9, 0x2cfcbfe9f0c305848e09a8eca3229f48,
  0x3ee0c551bd9b716a4f97bbefa9ebed9a, 0x8a34ff3da4da4c44e038e3efab26d0c,
  0x24776ca96745aaa67483fb55c2bec91f, 0x1a38cb474bcbeb3e1086c1c59c07b611,
  0x3a000516634fe40f57a7548074f99247, 0x388b3f37be72f7dadbf872eb8cfa9add,
  0x1118b047904db30fb0ea209193a12287, 0x234405dceb1bdef7a2439b14f97efac0,
  0x30d83ed9e9051afc52d7025eb08b8c05, 0x219a11ccffd80c107cd239804b793e67,
  0xc01c7c3a11a365d253fae52ddf41c09, 0x2f6a286dc3adbc49be8883dffea44c27,
  0x110fdbfa8bb9435c9c27880a2a3998c, 0x34f6f5cdd0fb4a96f328300a1a157cbf,
  0x3f812452f0184035fffebf593bfa7e3a, 0x2e40d2cb762b93a3ddbd320657f31314,
  0x3207e5de4dd9def3bd217ad6699150de, 0x168e5f6dd97e1d8ba78d9962a5550fe6,
  0x3982a0ce885794c02c18b2052f5d9d1, 0x30db42c89a8a32135384e37fda1c0ca9,
  0xc8471ef908a283ba7f6d253a0e562c3, 0x2a9fca15b8ca39c8a317ebbd06be9f68,
  0x12919895d87bcbc03a72d49effc259c2, 0x34d06ca8c111dac3e61e965c3dd24064,
  0x17604e84af666b791e8fddf2d21f677e, 0xfd9d7a06a59d3ae19d24746ef440802,
  0xe37d9452154da1dc9879303314175da, 0x2fec60f9f092563d3188b456ac3e1133,
  0x1c51873a5bb3e7f6c93e31570a3e3307, 0x264689b6cad8ef1273eccb53e1fccf46,
  0x1a0e1f498c468fc7d4a97859b44b87d3, 0xc64bdc87d1da8d63c6c91e3673bb760,
  0x20999ca7fa1b6d27d8b5bd371a5d1a8f, 0x33e5d66e2c66967124840e5d0428214e,
  0x37023e062f515048f1c19fc385926a7d, 0x83ff322b122014533cbb81c1f62127,
  0xa0c5a471332b4a8e89d31d553436dc7, 0x4c31f87dd6d2e95da1de0515e4c118f,
  0x1403572eca5ea26f47a1c7d0fde4dbdc, 0x34deff1d411c5d1d23f62be030e32c4c,
  0x289ca61e2538052f607fc8255b7ab34e, 0x117229a6454662a15984886c51e7efde,
  0x888460f0d3135c44947e942966e264f, 0x23834b70ce160711a6a4d14552a6315e,
  0x22b36e154da034c172d51025517e623d, 0x348b52467359122b2c3e6ca100c82b63,
  0xf8fe9b3ff05b24be107d3a0585d5938, 0x1c67f26750524a9e52e7e1624794c24e,
  0xd9c339cde62dea14fe23b3563d0b096, 0xfe2acae6009170878f61d625c6491c9,
  0x3a2451588ac56f5c794c8d8e4fd526f4, 0xfe133ab199eb9bb8f3e1835982e858b,
  0x1ffd9d9657bf5c424d5fa04737ed69ad, 0x1ed394753b9ddd88744ba4eeb6e45ecf,
  0x274fc83210ee5109a522211b7b978644, 0xdbb44b93bdfbb6b70725ab2a7887e78,
  0x486e1e1e5fbb2f5a6dba20e18daf952, 0xfd82acb6645a84b3d40d00079d2a166,
  0x345af535d7d2b82da535bce7bc05bbb6, 0x1cd70c417e422ce3c523705c73314b65,
  0x1621af29ce75ff71c00b4fc49b492cd3, 0x273ff6b1dd31979b6b9322233a635ae5,
  0x8dc5580eddcae4cdb5a9fde515b8a87, 0x2dced02a8bf51ffd6a4da886170764f7,
  0xf9008834df684e1adc2cc2be8626397, 0x2fc31f80545bb0b683171efd844111f9,
  0x1b8d2f3c1a9c0b07609c7a8882142e56, 0x15ac5a79538b9a6a70f0e6084fe83e22,
  0x21b6d4e86e2ceecc3fc670d42baa4b96, 0x3ba488a39d130b7823a6a315f6d101e9,
  0xffceba793a65e2c33dcee493acfdb24, 0x312254548bc4fbf786c2fb56b0cea944,
  0x5e26e8aeb4ade3e0ac87f8ee7ce9f46, 0x34668e4def48e38a76133ded4f851b71,
  0x2166dd1663f4d69b7a2eb09847f43cee, 0xfac2c6eb84c6345f41faa0c21722058,
  0xc2f38b6da1f446b5df4b999808814ff, 0x3d33a445144ed6f504781268206c57da,
  0x25805cf42a496a2a1a6941786eb3ec30, 0x49665fa6d33667a381a4706dc063230,
  0x2d320f41ff0a910644739ec1ff9514b3, 0x101370b0d2a0a03db90ad1155f172dae,
  0x1d63dcd4fcab01a81b2f6726348e6049, 0x39f0d847613ff002b5a2d90252ff2a76,
  0x8fb944d24d01a671301082b80658cab, 0x77fa7c105f01d543e74289001d14064,
  0x79d67c0bb4bbda78c094937b70ccb6f, 0x18bc183a3c7a266226745f9b5b794ace,
  0xebcb20ee6893efc8fd5fbb64aa13c33, 0x2dc47f815b31c085950a5d52ddb2528f,
  0x26470677d5e02f4c03d7a69888def1ff, 0x2a9a47d2652e352747513656934b9941,
  0xafa8bf9c7322b5cc0956b1727309f61, 0x166e55eb7dd06476b15eba2ee52e8aeb,
  0x778fedb3a96b8ef7824bdef4734814c, 0xee1ea4096017544f34297ffaccc10aa,
  0x251b775e30b9c6313687f62f8c7acd7, 0xc97e5e2859eba99836a347de7c9bb91,
  0x7ae3d0f1ff2365da07a7bc1cc4cf66d, 0x2bf813236528f1f8fdc0fe99c951e1e3,
  0x1de2496da867c2b3c8450ece0db80965, 0xaece5116c40641671167d5fab35b210,
  0x8e49add7dd5fb1fd2ceccaa46528c0e, 0x750cbf704396c79ed10c7f403d6ca,
  0x2851ee1e2baf0d8625e2611828bcda48
]

/-- `147` `30`-bit `C` col masks for `optSymp14`. -/
def optSymp14StepC : Array ℕ := #[
  33591334, 1004908460, 17112, 135593984, 821719000, 33587236, 844168310, 977644580, 554725016,
  944061506, 28316618, 34656374, 168792166, 51548846, 989314342, 581484462, 136270554, 168661678,
  581484526, 564801480, 458063908, 458588908, 954674496, 273154048, 553663490, 821046528,
  871034812, 570485812, 810561160, 62102182, 156667128, 286699146, 711242496, 1066972366,
  692200538, 235840154, 310910980, 704970768, 907804736, 447152384, 621356032, 523112448,
  580157440, 638713866, 604110856, 305303852, 570688200, 14016328, 580921728, 446017650,
  909521892, 576334792, 646575232, 839196022, 436574526, 780341440, 688319904, 883162202,
  256506224, 796189644, 363010962, 476355928, 139430930, 681603024, 949911748, 572522500,
  355467280, 1572928, 57147648, 873989120, 367005696, 851460096, 267976704, 348389376, 2, 8, 32,
  536871040, 536871424, 536872960, 8192, 536903680, 131072, 537395200, 538968064, 545259520,
  570425344, 671088640, 620288916, 272177200, 235267338, 424942458, 301720964, 1038892872,
  727824568, 676824684, 565889516, 413532164, 536088592, 177471552, 523239680, 721032192,
  30285824, 291799040, 290652164, 234160144, 981336128, 839647488, 1061028864, 540676096,
  97402880, 110008250, 317998926, 281280944, 617748582, 303039236, 553916022, 34560, 915284616,
  139329928, 615907614, 140771720, 545263650, 776112328, 714084396, 338426090, 786528662,
  20260914, 264837686, 693898634, 176937544, 447567016, 65204778, 577568768, 568328196, 282656784,
  435224640, 553648384, 932186112, 839909380, 747110416, 1022361664, 361758976, 249562112,
  351277056, 569917440, 26345472
]

/-- `147` `30`-bit `D` col masks for `optSymp14`. -/
def optSymp14StepD : Array ℕ := #[
  955596034, 135610384, 425000960, 1006485422, 838483850, 1004907812, 944204880, 162878362,
  565325120, 135610384, 978168868, 152916050, 33587236, 33607734, 548416768, 169202366, 871415726,
  16908352, 597863716, 698712026, 184909924, 273285120, 408224392, 564690258, 860548860,
  306888756, 335053092, 826945160, 300942216, 1028741606, 256094438, 648898898, 501191318,
  547137228, 614872036, 911232786, 749412354, 706945032, 137494560, 78446720, 396042752,
  848570368, 322846720, 590905600, 171984172, 64, 380808186, 604022160, 674539428, 75748488,
  645531788, 591175936, 347376314, 541731208, 6302400, 1009813252, 831910716, 239289848,
  915449908, 413844240, 30138626, 517539814, 166125758, 491914922, 72450016, 285736962, 14155784,
  187170848, 181928064, 871367168, 39323648, 624959488, 330334208, 70909952, 4, 16, 536870976,
  536871168, 1024, 4096, 16384, 65536, 537133056, 537919488, 541065216, 16777216, 603979776,
  268435456, 504676068, 729647010, 625000830, 784163908, 48743188, 277828514, 161292274,
  448569242, 787483806, 478810114, 159387656, 629800992, 32903296, 292553216, 403441664,
  743194624, 572456962, 186515464, 418316320, 458031232, 107807232, 631900160, 914366464,
  407669448, 193858832, 27135972, 776114120, 776083690, 541095688, 176819148, 807469056,
  852232772, 819727424, 12599296, 763375104, 604901818, 694419502, 222043894, 672410080,
  674923758, 62290378, 533611784, 580618604, 784351216, 354804708, 51531844, 555745282, 690552840,
  202899488, 285802624, 593495040, 975175682, 415236104, 898629664, 347603072, 941097472,
  423626752, 250617856, 896040960
]

/-- `147` `14`-bit `W` plane masks for `optSymp14`. -/
def optSymp14StepW : Array ℕ := #[
  1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 8, 8, 8, 8, 8, 8, 16, 16, 16, 16, 16, 64,
  64, 64, 64, 64, 64, 64, 96, 96, 96, 96, 96, 96, 96, 128, 128, 128, 128, 128, 128, 128, 128, 128,
  128, 128, 128, 128, 256, 256, 256, 256, 256, 256, 256, 256, 256, 288, 288, 288, 288, 288, 288,
  288, 288, 288, 512, 512, 512, 512, 512, 512, 512, 512, 512, 512, 512, 512, 512, 512, 1024, 1024,
  1024, 1024, 1024, 1024, 1024, 1024, 1024, 1056, 1056, 1056, 1056, 1056, 1056, 1056, 2080, 2080,
  2080, 2080, 2080, 2080, 2080, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096,
  4096, 4096, 4096, 8192, 8192, 8192, 8192, 8192, 8192, 8192, 8192, 8192, 9216, 9216, 9216, 9216,
  9216, 10240, 10240, 10240, 10240, 10240, 10240, 10240, 10240
]

/-- `147` pivot indices `k₀ ∈ 0..13` for `optSymp14`. -/
def optSymp14StepPiv : Array ℕ := #[
  0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 6, 6, 6,
  6, 6, 6, 6, 5, 5, 5, 5, 5, 5, 5, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8,
  8, 5, 5, 5, 5, 5, 5, 5, 5, 5, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10,
  10, 10, 10, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
  12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 13, 13, 13, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11,
  11, 11
]

/-- `18` group lengths (`∑ = 147`) for `optSymp14`. -/
def optSymp14GroupLens : Array ℕ := #[
  6, 6, 6, 6, 5, 7, 7, 13, 9, 9, 14, 9, 7, 7, 14, 9, 5, 8
]

/-- `18` group `14`-bit `W` masks for `optSymp14`. -/
def optSymp14GroupWMasks : Array ℕ := #[
  1, 2, 4, 8, 16, 64, 96, 128, 256, 288, 512, 1024, 1056, 2080, 4096, 8192, 9216, 10240
]

theorem optSymp14RowDiag_size : optSymp14RowDiag.size = 14 := by decide +kernel
theorem optSymp14ColDiag_size : optSymp14ColDiag.size = 14 := by decide +kernel
theorem optSymp14StepA_size : optSymp14StepA.size = 147 := by decide +kernel
theorem optSymp14StepB_size : optSymp14StepB.size = 147 := by decide +kernel
theorem optSymp14StepC_size : optSymp14StepC.size = 147 := by decide +kernel
theorem optSymp14StepD_size : optSymp14StepD.size = 147 := by decide +kernel
theorem optSymp14StepW_size : optSymp14StepW.size = 147 := by decide +kernel
theorem optSymp14StepPiv_size : optSymp14StepPiv.size = 147 := by decide +kernel

theorem optSymp14Pivot_ok :
    OuterWeights.withForcedList optSymp14StepW.toList (fun wL ↦
      OuterWeights.withForcedList optSymp14StepPiv.toList
        (fun pL ↦ checkPivot14List wL pL)) = true := by
  decide +kernel

theorem optSymp14None_ok :
    arrCheckNone14 optSymp14ColDiag optSymp14StepC optSymp14StepD optSymp14StepW =
      true := by
  decide +kernel

theorem optSymp14Rows0_ok :
    checkRowsChunk 0 21 optSymp14RowDiag optSymp14ColDiag optSymp14StepA
      optSymp14StepB optSymp14StepC optSymp14StepD optSymp14StepW false = true := by
  decide +kernel
theorem optSymp14Rows1_ok :
    checkRowsChunk 21 21 optSymp14RowDiag optSymp14ColDiag optSymp14StepA
      optSymp14StepB optSymp14StepC optSymp14StepD optSymp14StepW false = true := by
  decide +kernel
theorem optSymp14Rows2_ok :
    checkRowsChunk 42 21 optSymp14RowDiag optSymp14ColDiag optSymp14StepA
      optSymp14StepB optSymp14StepC optSymp14StepD optSymp14StepW false = true := by
  decide +kernel
theorem optSymp14Rows3_ok :
    checkRowsChunk 63 21 optSymp14RowDiag optSymp14ColDiag optSymp14StepA
      optSymp14StepB optSymp14StepC optSymp14StepD optSymp14StepW false = true := by
  decide +kernel
theorem optSymp14Rows4_ok :
    checkRowsChunk 84 21 optSymp14RowDiag optSymp14ColDiag optSymp14StepA
      optSymp14StepB optSymp14StepC optSymp14StepD optSymp14StepW false = true := by
  decide +kernel
theorem optSymp14Rows5_ok :
    checkRowsChunk 105 21 optSymp14RowDiag optSymp14ColDiag optSymp14StepA
      optSymp14StepB optSymp14StepC optSymp14StepD optSymp14StepW false = true := by
  decide +kernel

/-- Certified `147`-step `Symp14Spec` for `optSymp14`. -/
def optSymp14Spec : Symp14Spec 147 :=
  symp14SpecOfArrays 147 optSymp14RowDiag optSymp14ColDiag optSymp14StepA optSymp14StepB
    optSymp14StepC optSymp14StepD optSymp14StepW optSymp14StepPiv
    optSymp14StepW_size optSymp14StepPiv_size optSymp14Pivot_ok

theorem optSymp14Spec_evalBool_eq (k : Fin 14) (rc : Fin 128) (x : Fin (2 ^ 5)) :
    optSymp14Spec.evalBool k (if h : rc.val < 126 then some ⟨rc.val, h⟩ else none) x =
      keep9Hot24BoolTable rc x k := by
  by_cases hrc : rc.val < 126
  · simp only [hrc, ↓reduceDIte]
    let rcFin : Fin 126 := ⟨rc.val, hrc⟩
    have hr := checkRows126_of_parts6 optSymp14Rows0_ok optSymp14Rows1_ok optSymp14Rows2_ok
      optSymp14Rows3_ok optSymp14Rows4_ok optSymp14Rows5_ok rcFin
    simp only [Bool.false_eq_true, ↓reduceIte] at hr
    rw [arrEvalAllPlanesRow32_eq_ofFn optSymp14RowDiag_size optSymp14ColDiag_size
      optSymp14StepA_size optSymp14StepB_size optSymp14StepC_size optSymp14StepD_size
      optSymp14StepW_size] at hr
    have hsome : optSymp14Spec.evalBool k (some rcFin) x =
        keep9Hot24BoolTable ⟨rcFin.val, by omega⟩ x k := by
      have htab := sp14EvalBool_eqKeep9Hot24BoolTable k ⟨rcFin.val, by omega⟩ x
      simp only [rcFin.isLt, ↓reduceDIte] at htab
      dsimp only [optSymp14Spec]
      rw [evalAllPlanesRow32_14_eq_ofFn] at hr
      have hnth := congrArg (fun L ↦ nthZero14 L k.val) hr
      rw [nthZero14_ofFn, nthZero14_ofFn] at hnth
      have hbit := congrArg (fun n ↦ n.testBit x.val) hnth
      rw [testBit_arrEvalRow32AtNat optSymp14RowDiag optSymp14ColDiag optSymp14StepA
        optSymp14StepB optSymp14StepC optSymp14StepD optSymp14StepW optSymp14StepPiv
        optSymp14StepW_size optSymp14StepPiv_size optSymp14Pivot_ok rcFin k x,
        testBitEvalRow32AtNat_14 rcFin k x, htab] at hbit
      exact hbit
    simpa only [rcFin, Fin.eta] using hsome
  · simp only [hrc, ↓reduceDIte]
    have hnone := symp14SpecOfArrays_evalBool_none optSymp14RowDiag optSymp14ColDiag
      optSymp14StepA optSymp14StepB optSymp14StepC optSymp14StepD optSymp14StepW
      optSymp14StepPiv optSymp14ColDiag_size optSymp14StepC_size optSymp14StepD_size
      optSymp14StepW_size optSymp14StepPiv_size optSymp14Pivot_ok optSymp14None_ok k x
    change (symp14SpecOfArrays _ _ _ _ _ _ _ _ _ _ _ _).evalBool k none x = _
    rw [hnone]
    have htab := sp14EvalBool_eqKeep9Hot24BoolTable k rc x
    simp only [hrc, ↓reduceDIte] at htab
    rw [sp14EvalBool_none_eq k x] at htab
    exact htab

theorem optSymp14GroupLens_sum : (∑ g : Fin 18, optSymp14GroupLens.getD g.val 0) = 147 := by
  decide

theorem optSymp14StepW_group_eq (g : Fin 18) (j : Fin (optSymp14GroupLens.getD g.val 0)) :
    optSymp14StepW.getD
      (prefLen (fun i : Fin 18 ↦ optSymp14GroupLens.getD i.val 0) g.val
        (Nat.le_of_lt g.isLt) + j.val) 0 =
      optSymp14GroupWMasks.getD g.val 0 := by
  revert g j
  decide +kernel

/-- Certified `HGadgetSymp14Plan 147 18` (`2R + 2G = 330 T` diagonal core). -/
def optSymp14Plan : HGadgetSymp14Plan 147 18 :=
  HGadgetSymp14Plan.ofSymp14Spec optSymp14Spec
    (fun g ↦ optSymp14GroupLens.getD g.val 0) optSymp14GroupLens_sum
    (fun g k ↦ (optSymp14GroupWMasks.getD g.val 0).testBit k.val) (Equiv.refl (Fin 147))

theorem optSymp14Plan_targetBoolTable_eq :
    optSymp14Plan.targetBoolTable = keep9Hot24BoolTable := by
  funext rc x k
  have hW : ∀ (g : Fin 18) (j : Fin (optSymp14GroupLens.getD g.val 0)) (p : Fin 14),
      optSymp14Spec.stepW ((Equiv.refl (Fin 147)) (optSymp14Plan.stepIdx g j)) p =
        (optSymp14GroupWMasks.getD g.val 0).testBit p.val := by
    intro g j p
    dsimp only [optSymp14Spec, optSymp14Plan, symp14SpecOfArrays,
      HGadgetSymp14Plan.ofSymp14Spec, HGadgetSymp14Plan.stepIdx, Equiv.refl_apply]
    exact congrArg (fun n ↦ n.testBit p.val) (optSymp14StepW_group_eq g j)
  rw [optSymp14Plan, HGadgetSymp14Plan.ofSymp14Spec_targetBoolTable_eq _ _ _ _ _ hW,
    optSymp14Spec_evalBool_eq]

attribute [irreducible] optSymp14RowDiag optSymp14ColDiag optSymp14StepA optSymp14StepB
  optSymp14StepC optSymp14StepD optSymp14StepW optSymp14StepPiv optSymp14GroupLens
  optSymp14GroupWMasks optSymp14Spec optSymp14Plan

end OptWitnesses

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OptKeep9Symp14Data
