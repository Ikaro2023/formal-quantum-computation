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

public import QuantumComputationDiscoveries.Primitives.Arcsin.Solution.SliceTables

@[expose] public section

namespace QuantumComputation.Specs.ArcsinImpl

open Function Operator

def isSq9Wire (q : Nat) : Bool :=
  (Nat.ble 31 q && Nat.blt q 41) || clean_4_2.elem q

def trSq9Init (u15 : Bool) : WTree :=
  if u15 then trSq9InitTrue else trSq9InitFalse

def checkSq9InitInputs (u15 : Bool) (tr0 : WTree) : Nat → Bool
  | 0 => true
  | d9 + 1 =>
      (List.range 9).all (fun j => (sGet tr0 (31 + j)).testBit d9 == xor (d9.testBit j) (!u15)) &&
      ((sGet tr0 40).testBit d9 == u15) &&
      checkSq9InitInputs u15 tr0 d9

theorem checkSq9InitInputs_sound (u15 : Bool) (tr0 : WTree) :
    ∀ (n : Nat), checkSq9InitInputs u15 tr0 n = true →
      ∀ d9 < n,
        (∀ j < 9, (sGet tr0 (31 + j)).testBit d9 = xor (d9.testBit j) (!u15)) ∧
        (sGet tr0 40).testBit d9 = u15
  | 0, _, _, hd9 => absurd hd9 (Nat.not_lt_zero _)
  | n + 1, h, d9, hd9 => by
    dsimp only [checkSq9InitInputs] at h
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
    by_cases hdn : d9 = n
    · subst hdn; exact ⟨h.1.1, h.1.2⟩
    · exact checkSq9InitInputs_sound u15 tr0 n h.2 d9 (by omega)

def checkSq9Cert (u15 : Bool) : Bool :=
  let tr0 := trSq9Init u15
  checkWTreeWF 7 tr0 &&
  checkSq9InitInputs u15 tr0 512 &&
  clean_4_2.all (fun w => Nat.beq (sGet tr0 w) 0) &&
  s4_2Ops.all (Op102.inSub isSq9Wire) &&
  match runBitPar512 s4_2Ops tr0 with
  | some trf =>
      checkNonOutSym sq9_w tr0 trf 100 &&
      checkExtraSym trf (sq9_w.zip sq9Words)
  | none => false

theorem s4_2_cert_false : checkSq9Cert false = true := by decide +kernel
theorem s4_2_cert_true : checkSq9Cert true = true := by decide +kernel

theorem s4_2_cert (u15 : Bool) : checkSq9Cert u15 = true := by
  cases u15
  · exact s4_2_cert_false
  · exact s4_2_cert_true

def d9FromBits (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) : Nat :=
  let raw9 := (cond b0 1 0) + 2 * ((cond b1 1 0) + 2 * ((cond b2 1 0) +
    2 * ((cond b3 1 0) + 2 * ((cond b4 1 0) + 2 * ((cond b5 1 0) +
    2 * ((cond b6 1 0) + 2 * ((cond b7 1 0) + 2 * (cond b8 1 0))))))))
  cond b9 raw9 (511 - raw9)

theorem d9Val_eq_d9FromBits (u s4 : Nat) :
    d9Val u s4 = d9FromBits (uRotBit u s4 6) (uRotBit u s4 7) (uRotBit u s4 8)
      (uRotBit u s4 9) (uRotBit u s4 10) (uRotBit u s4 11) (uRotBit u s4 12)
      (uRotBit u s4 13) (uRotBit u s4 14) (uRotBit u s4 15) := by
  unfold d9Val d9FromBits
  have hraw : evalBits (uRotBit u s4) 6 9 =
      (cond (uRotBit u s4 6) 1 0) + 2 * ((cond (uRotBit u s4 7) 1 0) +
      2 * ((cond (uRotBit u s4 8) 1 0) + 2 * ((cond (uRotBit u s4 9) 1 0) +
      2 * ((cond (uRotBit u s4 10) 1 0) + 2 * ((cond (uRotBit u s4 11) 1 0) +
      2 * ((cond (uRotBit u s4 12) 1 0) + 2 * ((cond (uRotBit u s4 13) 1 0) +
      2 * (cond (uRotBit u s4 14) 1 0)))))))) := by
    simp only [evalBits, shiftLeft_eq_mul_pow]
    ring
  rw [hraw]

theorem d9FromBits_lt (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) :
    d9FromBits b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 < 512 := by
  revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9; decide +kernel

theorem d9Val_lt (u s4 : Nat) : d9Val u s4 < 512 := by
  rw [d9Val_eq_d9FromBits]; exact d9FromBits_lt _ _ _ _ _ _ _ _ _ _

theorem d9FromBits_bit (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) (j : Fin 9) :
    xor ((d9FromBits b0 b1 b2 b3 b4 b5 b6 b7 b8 b9).testBit j.val) (!b9) =
      [b0, b1, b2, b3, b4, b5, b6, b7, b8].getD j.val false := by
  revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 j; decide +kernel

theorem d9Val_bit (u s4 : Nat) {j : Nat} (hj : j < 9) :
    xor ((d9Val u s4).testBit j) (!uRotBit u s4 15) = uRotBit u s4 (6 + j) := by
  rw [d9Val_eq_d9FromBits]
  have h := d9FromBits_bit (uRotBit u s4 6) (uRotBit u s4 7) (uRotBit u s4 8)
    (uRotBit u s4 9) (uRotBit u s4 10) (uRotBit u s4 11) (uRotBit u s4 12)
    (uRotBit u s4 13) (uRotBit u s4 14) (uRotBit u s4 15) ⟨j, hj⟩
  dsimp only at h
  rw [h]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem checkExtraSym_all (trf : WTree) :
    ∀ (zs : List (Nat × Nat)),
      checkExtraSym trf zs = true →
      (zs.all (fun q => Nat.beq (sGet trf q.1) q.2)) = true
  | [], _ => rfl
  | (w, m) :: qs, h => by
    dsimp only [checkExtraSym] at h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    simp only [List.all_cons, Bool.and_eq_true, Nat.beq_eq]
    exact ⟨h.1.2, checkExtraSym_all trf qs h.2⟩

theorem exec_s4_2Ops {m0 : Fin 100 → Bool} {u s4 : Nat}
    (hu : ∀ (k : Nat) (hk : k < 10), m0 ⟨31 + k, by omega⟩ = uRotBit u s4 (6 + k))
    (hclean : ∀ w : Fin 100, w.val ∈ clean_4_2 → m0 w = false) :
    ∃ mf : Fin 100 → Bool,
      execList102 s4_2Ops m0 = some mf ∧
      (∀ w : Fin 100, w.val ∉ sq9_w → mf w = m0 w) ∧
      (∀ p ∈ sq9_w.zip sq9Words, ∀ hw : p.1 < 100, mf ⟨p.1, hw⟩ = p.2.testBit (d9Val u s4)) ∧
      targVal sq9_w mf = sq9Val (d9Val u s4) := by
  set u15 := m0 ⟨40, by decide⟩
  set d9 := d9Val u s4
  have hd9_lt : d9 < 512 := d9Val_lt u s4
  have hu15_eq : u15 = uRotBit u s4 15 := hu 9 (by decide)
  have hcert := s4_2_cert u15
  unfold checkSq9Cert at hcert
  dsimp only at hcert
  set tr0 := trSq9Init u15
  simp only [Bool.and_eq_true] at hcert
  obtain ⟨⟨⟨⟨hwf, hinp⟩, hcl0⟩, hsub⟩, hrun⟩ := hcert
  have hcl0' : ∀ x ∈ clean_4_2, sGet tr0 x = 0 := by
    intro x hx; exact Nat.beq_eq.mp (List.all_eq_true.mp hcl0 x hx)
  cases hbp : runBitPar512 s4_2Ops tr0 with
  | none => rw [hbp] at hrun; cases hrun
  | some trf =>
    rw [hbp] at hrun; dsimp only at hrun
    simp only [Bool.and_eq_true] at hrun
    obtain ⟨hnon, hext⟩ := hrun
    set m_sq9_0 : Fin 100 → Bool := fun w => (sGet tr0 w.val).testBit d9
    have hI0 : BitPar512Inv d9 tr0 m_sq9_0 := ⟨checkWTreeWF_sound 7 tr0 hwf, hd9_lt, fun _ => rfl⟩
    obtain ⟨m_sq9_f, hex_sq9, hIf⟩ := runBitPar512_sound s4_2Ops hI0 hbp
    obtain ⟨hinp_j, hinp_40⟩ := checkSq9InitInputs_sound u15 tr0 512 hinp d9 hd9_lt
    have hin : ∀ w : Fin 100, isSq9Wire w.val = true → m0 w = m_sq9_0 w := by
      intro w hw
      unfold isSq9Wire at hw
      simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hw
      rcases hw with ⟨h31, h41⟩ | hmem_b
      · by_cases hw40 : w.val = 40
        · have hw_fin : w = ⟨40, by decide⟩ := Fin.ext hw40
          rw [hw_fin]; dsimp only [m_sq9_0]; rw [hinp_40]
        · have hj : w.val - 31 < 9 := by omega
          have hw_eq : w = ⟨31 + (w.val - 31), by omega⟩ := Fin.ext (by dsimp; omega)
          rw [hw_eq, hu (w.val - 31) (by omega)]
          dsimp only [m_sq9_0]
          rw [hinp_j (w.val - 31) hj, hu15_eq, d9Val_bit u s4 hj]
      · have hmem := List.mem_of_elem_eq_true hmem_b
        rw [hclean w hmem]
        dsimp only [m_sq9_0]
        rw [hcl0' w.val hmem, Nat.zero_testBit]
    obtain ⟨mf, hexf, hout_sub, hin_sub⟩ := execList102_congr_sub isSq9Wire s4_2Ops hsub hex_sq9 hin
    have hnon_mf : ∀ w : Fin 100, w.val ∉ sq9_w → mf w = m0 w := by
      intro w hw_not
      cases hsw : isSq9Wire w.val
      · exact hout_sub w hsw
      · rw [hin_sub w hsw, hIf.hWire w,
            checkNonOutSym_sound sq9_w tr0 trf 100 hnon w.val w.isLt hw_not,
            ← hI0.hWire w, ← hin w hsw]
    have hzip : ∀ p ∈ sq9_w.zip sq9Words, ∀ hw : p.1 < 100, mf ⟨p.1, hw⟩ = p.2.testBit d9 := by
      intro p hp hw
      have hsw : isSq9Wire p.1 = true := by
        revert p hp; decide +kernel
      rw [hin_sub ⟨p.1, hw⟩ hsw, hIf.hWire ⟨p.1, hw⟩]
      have h_all := checkExtraSym_all trf (sq9_w.zip sq9Words) hext
      have hget := Nat.beq_eq.mp (List.all_eq_true.mp h_all p hp)
      rw [hget]
    refine ⟨mf, hexf, hnon_mf, hzip, ?_⟩
    have h0 := hzip (68, sq9Words.getD 0 0) (by decide +kernel) (by decide)
    have h1 := hzip (67, sq9Words.getD 1 0) (by decide +kernel) (by decide)
    have h2 := hzip (66, sq9Words.getD 2 0) (by decide +kernel) (by decide)
    have h3 := hzip (65, sq9Words.getD 3 0) (by decide +kernel) (by decide)
    have h4 := hzip (64, sq9Words.getD 4 0) (by decide +kernel) (by decide)
    have h5 := hzip (63, sq9Words.getD 5 0) (by decide +kernel) (by decide)
    have h6 := hzip (62, sq9Words.getD 6 0) (by decide +kernel) (by decide)
    have h7 := hzip (50, sq9Words.getD 7 0) (by decide +kernel) (by decide)
    have h8 := hzip (51, sq9Words.getD 8 0) (by decide +kernel) (by decide)
    simp only [sq9_w, targVal, sq9Val, evalBits, Nat.zero_add, shiftLeft_eq_mul_pow,
      dite_eq_left (by decide : 68 < 100), dite_eq_left (by decide : 67 < 100),
      dite_eq_left (by decide : 66 < 100), dite_eq_left (by decide : 65 < 100),
      dite_eq_left (by decide : 64 < 100), dite_eq_left (by decide : 63 < 100),
      dite_eq_left (by decide : 62 < 100), dite_eq_left (by decide : 50 < 100),
      dite_eq_left (by decide : 51 < 100),
      h0, h1, h2, h3, h4, h5, h6, h7, h8]
    ring

theorem isSq9Wire_ge25 (w : Fin 100) (hw : isSq9Wire w.val = true) : 25 ≤ w.val := by
  revert w hw; decide +kernel

def checkSq9RoundTrip (u15 : Bool) : Bool :=
  let tr0 := trSq9Init u15
  checkWTreeWF 7 tr0 &&
  checkSq9InitInputs u15 tr0 512 &&
  clean_4_2.all (fun w => Nat.beq (sGet tr0 w) 0) &&
  s4_2Ops.all (Op102.inSub isSq9Wire) &&
  s5_2CoreOps.all (Op102.inSub isSq9Wire) &&
  match runBitPar512 s4_2Ops tr0 with
  | some tr1 =>
      match runBitPar512 s5_2CoreOps tr1 with
      | some tr2 => checkNonOutSym [] tr0 tr2 100
      | none => false
  | none => false

theorem sq9_roundtrip_cert_false : checkSq9RoundTrip false = true := by decide +kernel
theorem sq9_roundtrip_cert_true : checkSq9RoundTrip true = true := by decide +kernel

theorem sq9_roundtrip_cert (u15 : Bool) : checkSq9RoundTrip u15 = true := by
  cases u15
  · exact sq9_roundtrip_cert_false
  · exact sq9_roundtrip_cert_true

theorem s5_2CoreOps_ge25 : (s5_2CoreOps.all Op102.ge25) = true := by decide +kernel

theorem exec_s5_2CoreOps {m0 m1 m2 : Fin 100 → Bool} {u s4 : Nat}
    (hu : ∀ (k : Nat) (hk : k < 10), m0 ⟨31 + k, by omega⟩ = uRotBit u s4 (6 + k))
    (hclean : ∀ w : Fin 100, w.val ∈ clean_4_2 → m0 w = false)
    (hfwd : execList102 s4_2Ops m0 = some m1)
    (hhigh : ∀ w : Fin 100, 25 ≤ w.val → m2 w = m1 w) :
    ∃ m2', execList102 s5_2CoreOps m2 = some m2' ∧
      (∀ w : Fin 100, w.val < 25 → m2' w = m2 w) ∧
      (∀ w : Fin 100, 25 ≤ w.val → m2' w = m0 w) := by
  set u15 := m0 ⟨40, by decide⟩
  set d9 := d9Val u s4
  have hd9_lt : d9 < 512 := d9Val_lt u s4
  have hu15_eq : u15 = uRotBit u s4 15 := hu 9 (by decide)
  have hcert := sq9_roundtrip_cert u15
  unfold checkSq9RoundTrip at hcert
  dsimp only at hcert
  set tr0 := trSq9Init u15
  simp only [Bool.and_eq_true] at hcert
  obtain ⟨⟨⟨⟨⟨hwf, hinp⟩, hcl0⟩, hsub_fwd⟩, hsub_un⟩, hrun⟩ := hcert
  have hcl0' : ∀ x ∈ clean_4_2, sGet tr0 x = 0 := by
    intro x hx; exact Nat.beq_eq.mp (List.all_eq_true.mp hcl0 x hx)
  cases hbp1 : runBitPar512 s4_2Ops tr0 with
  | none => rw [hbp1] at hrun; cases hrun
  | some tr1 =>
    rw [hbp1] at hrun; dsimp only at hrun
    cases hbp2 : runBitPar512 s5_2CoreOps tr1 with
    | none => rw [hbp2] at hrun; cases hrun
    | some tr2 =>
      rw [hbp2] at hrun; dsimp only at hrun
      set m_sq9_0 : Fin 100 → Bool := fun w => (sGet tr0 w.val).testBit d9
      have hI0 : BitPar512Inv d9 tr0 m_sq9_0 := ⟨checkWTreeWF_sound 7 tr0 hwf, hd9_lt, fun _ => rfl⟩
      obtain ⟨m_sq9_1, hex_sq9_1, hI1⟩ := runBitPar512_sound s4_2Ops hI0 hbp1
      obtain ⟨m_sq9_2, hex_sq9_2, hI2⟩ := runBitPar512_sound s5_2CoreOps hI1 hbp2
      obtain ⟨hinp_j, hinp_40⟩ := checkSq9InitInputs_sound u15 tr0 512 hinp d9 hd9_lt
      have hin0 : ∀ w : Fin 100, isSq9Wire w.val = true → m0 w = m_sq9_0 w := by
        intro w hw
        unfold isSq9Wire at hw
        simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hw
        rcases hw with ⟨h31, h41⟩ | hmem_b
        · by_cases hw40 : w.val = 40
          · have hw_fin : w = ⟨40, by decide⟩ := Fin.ext hw40
            rw [hw_fin]; dsimp only [m_sq9_0]; rw [hinp_40]
          · have hj : w.val - 31 < 9 := by omega
            have hw_eq : w = ⟨31 + (w.val - 31), by omega⟩ := Fin.ext (by dsimp; omega)
            rw [hw_eq, hu (w.val - 31) (by omega)]
            dsimp only [m_sq9_0]
            rw [hinp_j (w.val - 31) hj, hu15_eq, d9Val_bit u s4 hj]
        · have hmem := List.mem_of_elem_eq_true hmem_b
          rw [hclean w hmem]
          dsimp only [m_sq9_0]
          rw [hcl0' w.val hmem, Nat.zero_testBit]
      obtain ⟨m1', hexf1, hout1, hin1⟩ :=
        execList102_congr_sub isSq9Wire s4_2Ops hsub_fwd hex_sq9_1 hin0
      have hm1_eq : m1' = m1 := Option.some.inj (hexf1.symm.trans hfwd)
      subst hm1_eq
      have hin2 : ∀ w : Fin 100, isSq9Wire w.val = true → m2 w = m_sq9_1 w := by
        intro w hw
        rw [hhigh w (isSq9Wire_ge25 w hw), hin1 w hw]
      obtain ⟨m2', hexf2, hout2, hin2_out⟩ :=
        execList102_congr_sub isSq9Wire s5_2CoreOps hsub_un hex_sq9_2 hin2
      refine ⟨m2', hexf2, fun w hw => ?_, fun w hw => ?_⟩
      · cases hsw : isSq9Wire w.val
        · exact hout2 w hsw
        · exact absurd hw (not_lt_of_ge (isSq9Wire_ge25 w hsw))
      · cases hsw : isSq9Wire w.val
        · rw [hout2 w hsw, hhigh w hw, hout1 w hsw]
        · rw [hin2_out w hsw, hI2.hWire w,
              checkNonOutSym_sound [] tr0 tr2 100 hrun w.val w.isLt (by intro hm; cases hm),
              ← hI0.hWire w, ← hin0 w hsw]

-- ============================================================================
-- Bag Construction & Evaluation Lemmas (addMasksAt, evalMasksVal)
-- ============================================================================

def wMask (w : Nat) : Nat := Nat.shiftLeft 1 (w + 1)

def aMask (k : Nat) : Nat := Nat.shiftLeft 1 (103 + k)

def wireMasks : List Nat → List Nat
  | [] => []
  | w :: ws => wMask w :: wireMasks ws

def xorMasks : List Nat → Nat → List Nat
  | [], _ => []
  | w :: ws, ctrlM => (wMask w ^^^ ctrlM) :: xorMasks ws ctrlM

def evalMasksVal (N : Nat) (env : Nat → Bool) : List Nat → Nat
  | [] => 0
  | m :: ms => (cond (evalSymMask N env m) 1 0) + 2 * evalMasksVal N env ms

def addMasksZero : List Nat → List (List Nat) → List (List Nat)
  | [], bag => bag
  | m :: ms, [] => [m] :: addMasksZero ms []
  | m :: ms, c :: cs => (m :: c) :: addMasksZero ms cs

def addMasksAt : Nat → List Nat → List (List Nat) → List (List Nat)
  | 0, ms, bag => addMasksZero ms bag
  | sh + 1, ms, [] => [] :: addMasksAt sh ms []
  | sh + 1, ms, c :: cs => c :: addMasksAt sh ms cs

theorem evalBag_addMasksZero (N : Nat) (env : Nat → Bool) :
    ∀ (ms : List Nat) (bag : List (List Nat)),
      evalBag N env (addMasksZero ms bag) =
        evalBag N env bag + evalMasksVal N env ms
  | [], bag => by simp [addMasksZero, evalMasksVal]
  | m :: ms, [] => by
    dsimp only [addMasksZero, evalBag, evalCol, evalMasksVal]
    rw [evalBag_addMasksZero N env ms []]
    dsimp only [evalBag]
    omega
  | m :: ms, c :: cs => by
    dsimp only [addMasksZero, evalBag, evalCol, evalMasksVal]
    rw [evalBag_addMasksZero N env ms cs]
    omega

theorem evalBag_addMasksAt (N : Nat) (env : Nat → Bool) :
    ∀ (sh : Nat) (ms : List Nat) (bag : List (List Nat)),
      evalBag N env (addMasksAt sh ms bag) =
        evalBag N env bag + 2 ^ sh * evalMasksVal N env ms
  | 0, ms, bag => by
    dsimp only [addMasksAt]
    rw [Nat.pow_zero, Nat.one_mul]
    exact evalBag_addMasksZero N env ms bag
  | sh + 1, ms, [] => by
    dsimp only [addMasksAt, evalBag, evalCol]
    rw [evalBag_addMasksAt N env sh ms []]
    dsimp only [evalBag]
    have hpow : 2 ^ (sh + 1) = 2 * 2 ^ sh := by ring
    rw [hpow]; ring
  | sh + 1, ms, c :: cs => by
    dsimp only [addMasksAt, evalBag]
    rw [evalBag_addMasksAt N env sh ms cs]
    have hpow : 2 ^ (sh + 1) = 2 * 2 ^ sh := by ring
    rw [hpow]; ring

theorem evalBag_replicate_nil (N : Nat) (env : Nat → Bool) :
    ∀ k : Nat, evalBag N env (List.replicate k []) = 0
  | 0 => rfl
  | k + 1 => by simp [List.replicate_succ, evalBag, evalCol, evalBag_replicate_nil N env k]

theorem evalSymMask_wMask {N : Nat} {m0 : Fin 100 → Bool} {defs : List (Nat × Nat)}
    (hN : 103 ≤ N) {w : Nat} (hw : w < 100) :
    evalSymMask N (buildSymEnv N m0 defs) (wMask w) = m0 ⟨w, hw⟩ := by
  unfold wMask
  rw [evalSymMask_shiftLeft_one _ (by omega)]
  unfold buildSymEnv
  rw [buildSymEnvAux_lt N 103 defs (baseSymEnv m0) (by omega)]
  unfold baseSymEnv
  rw [ite_eq_right (by omega), dite_eq_left (by omega)]
  congr 1

theorem evalMasksVal_wireMasks {N : Nat} {m0 : Fin 100 → Bool} {defs : List (Nat × Nat)}
    (hN : 103 ≤ N) :
    ∀ (ws : List Nat),
      (∀ w ∈ ws, w < 100) →
      evalMasksVal N (buildSymEnv N m0 defs) (wireMasks ws) = targVal ws m0
  | [], _ => rfl
  | w :: ws, hws => by
    have hw : w < 100 := hws w (List.mem_cons_self ..)
    have hrest : ∀ x ∈ ws, x < 100 := fun x hx => hws x (List.mem_cons_of_mem _ hx)
    dsimp only [wireMasks, evalMasksVal, targVal]
    rw [dite_eq_left hw, evalMasksVal_wireMasks hN ws hrest, evalSymMask_wMask hN hw]

theorem xorMasks_length : ∀ (ws : List Nat) (ctrlM : Nat), (xorMasks ws ctrlM).length = ws.length
  | [], _ => rfl
  | _ :: ws, ctrlM => by simp [xorMasks, xorMasks_length ws ctrlM]

theorem evalMasksVal_xorMasks {N : Nat} {m0 : Fin 100 → Bool} {defs : List (Nat × Nat)}
    (hN : 103 ≤ N) (ctrlM : Nat) :
    ∀ (ws : List Nat),
      (∀ w ∈ ws, w < 100) →
      evalMasksVal N (buildSymEnv N m0 defs) (xorMasks ws ctrlM) =
        let c := evalSymMask N (buildSymEnv N m0 defs) ctrlM
        cond c ((2 ^ ws.length - 1) - targVal ws m0) (targVal ws m0)
  | [], _ => by
    dsimp only [xorMasks, evalMasksVal, List.length_nil, targVal]
    cases evalSymMask N (buildSymEnv N m0 defs) ctrlM <;> rfl
  | w :: ws, hws => by
    have hw : w < 100 := hws w (List.mem_cons_self ..)
    have hrest : ∀ x ∈ ws, x < 100 := fun x hx => hws x (List.mem_cons_of_mem _ hx)
    dsimp only [xorMasks, evalMasksVal, targVal, List.length_cons]
    rw [dite_eq_left hw, evalSymMask_xor, evalSymMask_wMask hN hw,
        evalMasksVal_xorMasks hN ctrlM ws hrest]
    dsimp only
    have hlt := targVal_lt ws m0
    have hpow : 2 ^ (ws.length + 1) = 2 * 2 ^ ws.length := by ring
    rw [hpow]
    cases evalSymMask N (buildSymEnv N m0 defs) ctrlM <;>
      cases m0 ⟨w, hw⟩ <;> [
        (change 0 + 2 * targVal ws m0 = 0 + 2 * targVal ws m0; rfl);
        (change 1 + 2 * targVal ws m0 = 1 + 2 * targVal ws m0; rfl);
        (change 1 + 2 * (2 ^ ws.length - 1 - targVal ws m0) =
          2 * 2 ^ ws.length - 1 - (0 + 2 * targVal ws m0); omega);
        (change 0 + 2 * (2 ^ ws.length - 1 - targVal ws m0) =
          2 * 2 ^ ws.length - 1 - (1 + 2 * targVal ws m0); omega)
      ]


theorem rangeList_length : ∀ (sout M : Nat), (rangeList sout M).length = M
  | _, 0 => rfl
  | sout, M + 1 => by simp [rangeList, rangeList_length (sout + 1) M]

theorem mem_rangeList_iff : ∀ {sout M w : Nat}, w ∈ rangeList sout M ↔ sout ≤ w ∧ w < sout + M
  | _, 0, _ => by simp [rangeList]
  | sout, M + 1, w => by
    simp only [rangeList, List.mem_cons, mem_rangeList_iff]
    omega

theorem rangeList_succ (sout n : Nat) :
    rangeList sout (n + 1) = rangeList sout n ++ [sout + n] := by
  induction n generalizing sout with
  | zero => rfl
  | succ n ih =>
    change sout :: rangeList (sout + 1) (n + 1) =
      sout :: (rangeList (sout + 1) n ++ [sout + (n + 1)])
    rw [ih (sout + 1), show sout + 1 + n = sout + (n + 1) by omega]

theorem targVal_append : ∀ (l1 l2 : List Nat) (m : Fin 100 → Bool),
    targVal (l1 ++ l2) m = targVal l1 m + 2 ^ l1.length * targVal l2 m
  | [], l2, m => by simp [targVal]
  | w :: l1, l2, m => by
    dsimp only [List.cons_append, targVal, List.length_cons]
    rw [targVal_append l1 l2 m]
    have hpow : 2 ^ (l1.length + 1) = 2 * 2 ^ l1.length := by ring
    rw [hpow]; ring

theorem targVal_drop (ws : List Nat) (k : Nat) (m : Fin 100 → Bool) :
    targVal (ws.drop k) m = targVal ws m / 2 ^ k := by
  by_cases hk : k ≤ ws.length
  · have hsp := targVal_append (ws.take k) (ws.drop k) m
    rw [List.take_append_drop, List.length_take_of_le hk] at hsp
    have hlt : targVal (ws.take k) m < 2 ^ k := by
      have := targVal_lt (ws.take k) m
      rwa [List.length_take_of_le hk] at this
    rw [hsp, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, Nat.zero_add]
  · have hge : ws.length ≤ k := by omega
    rw [List.drop_of_length_le hge, targVal, Nat.div_eq_of_lt]
    exact lt_of_lt_of_le (targVal_lt ws m) (Nat.pow_le_pow_right (by decide) hge)

theorem targVal_rangeList_eq_evalBits {m : Fin 100 → Bool} {g : Nat → Bool}
    (hg : ∀ (k : Nat) (hk : k < 16), m ⟨25 + k, by omega⟩ = g k) :
    ∀ (b_min len : Nat), b_min + len ≤ 16 →
      targVal (rangeList (25 + b_min) len) m = evalBits g b_min len
  | _, 0, _ => rfl
  | b_min, len + 1, hle => by
    rw [rangeList_succ, targVal_append, rangeList_length,
        targVal_rangeList_eq_evalBits hg b_min len (by omega)]
    dsimp only [targVal, evalBits]
    have hlt102 : 25 + b_min + len < 100 := by omega
    have hlt16 : b_min + len < 16 := by omega
    rw [dite_eq_left hlt102, shiftLeft_eq_mul_pow]
    have hm : m ⟨25 + b_min + len, hlt102⟩ = g (b_min + len) := by
      have hfin : (⟨25 + b_min + len, hlt102⟩ : Fin 100) = ⟨25 + (b_min + len), by omega⟩ :=
        Fin.ext (by dsimp; omega)
      rw [hfin, hg (b_min + len) hlt16]
    rw [hm]; ring

theorem evalSymMask_one {N : Nat} {m0 : Fin 100 → Bool} {defs : List (Nat × Nat)}
    (hN : 1 ≤ N) :
    evalSymMask N (buildSymEnv N m0 defs) 1 = true := by
  have h1 : (1 : Nat) = Nat.shiftLeft 1 0 := rfl
  rw [h1, evalSymMask_shiftLeft_one _ hN]
  unfold buildSymEnv
  rw [buildSymEnvAux_lt N 103 defs (baseSymEnv m0) (by omega)]
  rfl

theorem evalMasksVal_slopeSlice {N : Nat} {m0 : Fin 100 → Bool} {defs : List (Nat × Nat)}
    (hN : 103 ≤ N) {kv s4 u : Nat}
    (hu : ∀ (k : Nat) (hk : k < 16), m0 ⟨25 + k, by omega⟩ = uRotBit u s4 k)
    {bit_idx b_min len sh_out : Nat} (hb : bit_idx < 15) (hlen : b_min + len ≤ 16)
    (hkv_bit : m0 ⟨72 + bit_idx, by omega⟩ = kv.testBit bit_idx) :
    2 ^ sh_out * evalMasksVal N (buildSymEnv N m0 defs)
      (xorMasks (rangeList (25 + b_min) len) (wMask (72 + bit_idx) ^^^ 1)) +
      slopeTermNeg27 kv bit_idx b_min len (2 ^ sh_out) s4 u =
    slopeTermPos27 kv bit_idx b_min len (2 ^ sh_out) s4 u +
      slopeTermConst27 kv bit_idx len sh_out := by
  have hr_lt : ∀ w ∈ rangeList (25 + b_min) len, w < 100 := by
    intro w hw; have := mem_rangeList_iff.mp hw; omega
  rw [evalMasksVal_xorMasks hN _ _ hr_lt, rangeList_length,
      targVal_rangeList_eq_evalBits hu b_min len hlen,
      evalSymMask_xor, evalSymMask_wMask hN (by omega), evalSymMask_one (by omega),
      xor_true_eq_not, hkv_bit]
  dsimp only [slopeTermPos27, slopeTermNeg27, slopeTermConst27]
  have hev_lt : evalBits (uRotBit u s4) b_min len < 2 ^ len := by
    rw [← targVal_rangeList_eq_evalBits hu b_min len hlen]
    have := targVal_lt (rangeList (25 + b_min) len) m0
    rwa [rangeList_length] at this
  have hle : evalBits (uRotBit u s4) b_min len ≤ 2 ^ len - 1 := Nat.le_sub_one_of_lt hev_lt
  cases kv.testBit bit_idx
  · change 2 ^ sh_out * (2 ^ len - 1 - evalBits (uRotBit u s4) b_min len) +
        evalBits (uRotBit u s4) b_min len * 2 ^ sh_out =
      0 + (2 ^ len - 1) * 2 ^ sh_out
    have hsub := Nat.sub_add_cancel hle
    calc 2 ^ sh_out * (2 ^ len - 1 - evalBits (uRotBit u s4) b_min len) +
          evalBits (uRotBit u s4) b_min len * 2 ^ sh_out
      _ = (2 ^ len - 1 - evalBits (uRotBit u s4) b_min len +
            evalBits (uRotBit u s4) b_min len) * 2 ^ sh_out := by ring
      _ = 0 + (2 ^ len - 1) * 2 ^ sh_out := by rw [hsub, Nat.zero_add]
  · change 2 ^ sh_out * evalBits (uRotBit u s4) b_min len + 0 =
      evalBits (uRotBit u s4) b_min len * 2 ^ sh_out + 0
    ring

theorem evalMasksVal_curvSlice {N : Nat} {m0 : Fin 100 → Bool} {defs : List (Nat × Nat)}
    (hN : 103 ≤ N) {lv sq9 : Nat}
    (hsq9 : targVal sq9_w m0 = sq9)
    {c_idx b_min ctrlM : Nat} (_hb : b_min ≤ 9)
    (hctrl : evalSymMask N (buildSymEnv N m0 defs) ctrlM = lv.testBit c_idx) :
    evalMasksVal N (buildSymEnv N m0 defs) (xorMasks (sq9_w.drop b_min) ctrlM) =
      curvTerm lv c_idx (2 ^ b_min) (2 ^ (9 - b_min) - 1) sq9 := by
  have hsq_lt : ∀ w ∈ sq9_w.drop b_min, w < 100 := by
    intro w hw
    have hmem := List.mem_of_mem_drop hw
    have hall : ∀ x ∈ sq9_w, x < 100 := by decide
    exact hall w hmem
  rw [evalMasksVal_xorMasks hN _ _ hsq_lt, List.length_drop,
      show sq9_w.length = 9 from rfl, targVal_drop, hsq9, hctrl]
  rfl

theorem evalBag_append (N : Nat) (env : Nat → Bool) :
    ∀ (b1 b2 : List (List Nat)),
      evalBag N env (b1 ++ b2) = evalBag N env b1 + 2 ^ b1.length * evalBag N env b2
  | [], b2 => by simp [evalBag]
  | c :: b1, b2 => by
    dsimp only [List.cons_append, evalBag, List.length_cons]
    rw [evalBag_append N env b1 b2]
    have hpow : 2 ^ (b1.length + 1) = 2 * 2 ^ b1.length := by ring
    rw [hpow]; ring

theorem evalBag_take_four (N : Nat) (env : Nat → Bool) (B : List (List Nat)) (hB : 4 ≤ B.length) :
    evalBag N env B = evalBag N env (B.take 4) + 16 * evalBag N env (B.drop 4) := by
  have h := evalBag_append N env (B.take 4) (B.drop 4)
  rw [List.take_append_drop, List.length_take_of_le hB] at h
  exact h

def maskDisjoint (badW : List Nat) (m : Nat) : Bool :=
  Nat.beq (Nat.shiftRight m 103) 0 && badW.all (fun w => !(m.testBit (w + 1)))

def bagDisjoint (badW : List Nat) (bag : List (List Nat)) : Bool :=
  bag.all (fun col => col.all (maskDisjoint badW))

theorem evalSymMask_add_of_shiftRight_zero (env : Nat → Bool) {m b : Nat}
    (hsh : Nat.shiftRight m b = 0) :
    ∀ d : Nat, evalSymMask (b + d) env m = evalSymMask b env m
  | 0 => rfl
  | d + 1 => by
    rw [show b + (d + 1) = (b + d) + 1 by omega]
    dsimp only [evalSymMask]
    rw [testBit_eq_false_of_shiftRight_zero hsh (Nat.le_add_right b d),
        Bool.false_and, Bool.xor_false]
    exact evalSymMask_add_of_shiftRight_zero env hsh d

theorem evalSymMask_congr_disjoint {N1 N2 : Nat} {m1 m2 : Fin 100 → Bool}
    {defs1 defs2 : List (Nat × Nat)} {badW : List Nat} {m : Nat}
    (h1 : 103 ≤ N1) (h2 : 103 ≤ N2)
    (hdisj : maskDisjoint badW m = true)
    (heq : ∀ w : Fin 100, w.val ∉ badW → m1 w = m2 w) :
    evalSymMask N1 (buildSymEnv N1 m1 defs1) m =
      evalSymMask N2 (buildSymEnv N2 m2 defs2) m := by
  unfold maskDisjoint at hdisj
  simp only [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, Bool.not_eq_true'] at hdisj
  obtain ⟨hsh, hbad⟩ := hdisj
  have hev1 : evalSymMask N1 (buildSymEnv N1 m1 defs1) m = evalSymMask 103 (baseSymEnv m1) m := by
    unfold buildSymEnv
    rw [evalSymMask_buildSymEnvAux N1 103 defs1 (baseSymEnv m1) hsh,
        show N1 = 103 + (N1 - 103) by omega,
        evalSymMask_add_of_shiftRight_zero (baseSymEnv m1) hsh (N1 - 103)]
  have hev2 : evalSymMask N2 (buildSymEnv N2 m2 defs2) m = evalSymMask 103 (baseSymEnv m2) m := by
    unfold buildSymEnv
    rw [evalSymMask_buildSymEnvAux N2 103 defs2 (baseSymEnv m2) hsh,
        show N2 = 103 + (N2 - 103) by omega,
        evalSymMask_add_of_shiftRight_zero (baseSymEnv m2) hsh (N2 - 103)]
  rw [hev1, hev2]
  refine evalSymMask_congr (baseSymEnv m1) (baseSymEnv m2) m 103 (fun i hi htb => ?_)
  unfold baseSymEnv
  by_cases hi0 : i = 0
  · subst hi0; rfl
  · rw [ite_eq_right hi0, ite_eq_right hi0]
    by_cases hlt : i - 1 < 100
    · rw [dite_eq_left hlt, dite_eq_left hlt]
      exact heq ⟨i - 1, hlt⟩ (fun hmem => by
        have hf := hbad (i - 1) hmem
        rw [show i - 1 + 1 = i by omega, htb] at hf; cases hf)
    · rw [dite_eq_right hlt, dite_eq_right hlt]

theorem evalCol_congr_disjoint {N1 N2 : Nat} {m1 m2 : Fin 100 → Bool}
    {defs1 defs2 : List (Nat × Nat)} {badW : List Nat}
    (h1 : 103 ≤ N1) (h2 : 103 ≤ N2)
    (heq : ∀ w : Fin 100, w.val ∉ badW → m1 w = m2 w) :
    ∀ (col : List Nat), col.all (maskDisjoint badW) = true →
      evalCol N1 (buildSymEnv N1 m1 defs1) col = evalCol N2 (buildSymEnv N2 m2 defs2) col
  | [], _ => rfl
  | m :: ms, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    dsimp only [evalCol]
    rw [evalSymMask_congr_disjoint h1 h2 h.1 heq, evalCol_congr_disjoint h1 h2 heq ms h.2]

theorem evalBag_congr_disjoint {N1 N2 : Nat} {m1 m2 : Fin 100 → Bool}
    {defs1 defs2 : List (Nat × Nat)} {badW : List Nat}
    (h1 : 103 ≤ N1) (h2 : 103 ≤ N2)
    (heq : ∀ w : Fin 100, w.val ∉ badW → m1 w = m2 w) :
    ∀ (bag : List (List Nat)), bagDisjoint badW bag = true →
      evalBag N1 (buildSymEnv N1 m1 defs1) bag = evalBag N2 (buildSymEnv N2 m2 defs2) bag
  | [], _ => rfl
  | col :: cols, h => by
    dsimp only [bagDisjoint] at h
    simp only [List.all_cons, Bool.and_eq_true] at h
    dsimp only [evalBag]
    rw [evalCol_congr_disjoint h1 h2 heq col h.1, evalBag_congr_disjoint h1 h2 heq cols h.2]

-- ============================================================================
-- Arithmetic Combination into deltaPos25
-- ============================================================================

theorem div16_split_combine {b_lo4 W_val N_val : Nat} :
    (b_lo4 + W_val) / 16 + ((b_lo4 + W_val) % 16 + N_val) / 16 =
      (b_lo4 + W_val + N_val) / 16 := by
  omega

theorem wWide_carry_split {b_lo4 W_val Z : Nat} (hb : b_lo4 < 16) :
    let x := (b_lo4 + W_val) % 16
    let tot := ((15 - x) + 16 * Z + W_val) % 536870912
    tot % 16 = 15 - b_lo4 ∧
    tot / 16 = (Z + (b_lo4 + W_val) / 16) % 33554432 := by
  dsimp only
  omega

theorem stages45_arith_combine {b_base kv lv s4 u b_res19 b_lo4 u18_u N_val W_val : Nat}
    {q19_4 : Bool}
    (hz_le : zNeg27 kv s4 u ≤ zPos27 b_base kv lv s4 u)
    (hd_lt : deltaPos25 b_base kv lv s4 u < 16777216)
    (hbase_eq : 16 * b_res19 + 4194304 * u18_u + b_lo4 + slopeConst27 kv + 1024 =
      b_base + 536870912 * (cond q19_4 1 0))
    (hNW_eq : N_val + W_val + negSlope27 kv s4 u =
      curvVal27 lv (d9Val u s4) + posSlope27 kv s4 u + slopeConst27 kv + 4194304 * u18_u) :
    let x := (b_lo4 + W_val) % 16
    (u + b_res19 + (x + N_val) / 16 + (b_lo4 + W_val) / 16) % 33554432 =
      deltaPos25 b_base kv lv s4 u := by
  dsimp only
  unfold zPos27 zNeg27 at hz_le
  unfold deltaPos25 diff27 zPos27 zNeg27 at hd_lt ⊢
  cases q19_4 <;> dsimp only [cond] at hbase_eq ⊢ <;> omega

-- ============================================================================
-- CSA Stage Certificates (s4_1, s4_3, s4_4, s5_3) & Bag Identities
-- ============================================================================


theorem s4_1_cert :
    checkStageSymModExtra 120 clean_4_1 out_4_1 extra_4_1 s4_1Ops defs_4_1 bag_4_1 steps_4_1 =
      true := by
  decide +kernel

theorem s4_3_cert :
    checkStageSymExact 210 clean_4_3 out_4_3 s4_3Ops defs_4_3 bag_4_3 steps_4_3 = true := by
  decide +kernel

theorem s4_4_cert :
    checkStageSymMod 135 clean_4_4 out_4_4 s4_4Ops defs_4_4 bag_4_4 steps_4_4 = true := by
  decide +kernel

theorem s5_3_cert :
    checkStageSymModExtra 274 clean_5_3 out_5_3 extra_5_3 s5_3PreOps defs_5_3 bag_5_3 steps_5_3 =
      true := by
  decide +kernel

theorem s5_1_cert :
    checkStageSymUncomp 210 clean_4_3 s4_3Ops s5_1Ops defs_4_3 = true := by
  decide +kernel

theorem exec_s5_1Ops {m0 m1 m2 : Fin 100 → Bool}
    (hclean : ∀ w : Fin 100, w.val ∈ clean_4_3 → m0 w = false)
    (hfwd : execList102 s4_3Ops m0 = some m1)
    (hhigh : ∀ w : Fin 100, 25 ≤ w.val → m2 w = m1 w) :
    ∃ m2', execList102 s5_1Ops m2 = some m2' ∧
      (∀ w : Fin 100, w.val < 25 → m2' w = m2 w) ∧
      (∀ w : Fin 100, 25 ≤ w.val → m2' w = m0 w) :=
  checkStageSymUncomp_sound s5_1_cert hclean hfwd hhigh

def nNarrowBag : List (List Nat) :=
  addMasksAt 0 (xorMasks (sq9_w.drop 7) l8_0_m) (
  addMasksAt 0 (xorMasks (sq9_w.drop 6) (wMask 87)) (
  addMasksAt 0 (xorMasks (sq9_w.drop 5) (wMask 88)) (
  addMasksAt 0 (xorMasks (sq9_w.drop 4) (wMask 89)) (
  addMasksAt 0 (xorMasks (sq9_w.drop 3) (wMask 90)) (
  addMasksAt 0 (xorMasks (sq9_w.drop 2) (wMask 91)) (
  addMasksAt 0 (xorMasks (sq9_w.drop 1) (wMask 92)) (
  addMasksAt 0 (xorMasks (sq9_w.drop 0) (wMask 93)) (
  addMasksAt 1 (wireMasks sq9_w) (
  addMasksAt 0 (xorMasks (rangeList 38 3) (wMask 72 ^^^ 1)) (
  addMasksAt 0 (xorMasks (rangeList 37 4) (wMask 73 ^^^ 1)) (
  addMasksAt 0 (xorMasks (rangeList 36 5) (wMask 74 ^^^ 1)) (
  addMasksAt 0 (xorMasks (rangeList 35 6) (wMask 75 ^^^ 1)) (
  addMasksAt 0 (xorMasks (rangeList 34 7) (wMask 76 ^^^ 1)) (
  addMasksAt 0 (xorMasks (rangeList 33 8) (wMask 77 ^^^ 1)) (
  addMasksAt 0 (xorMasks (rangeList 32 9) (wMask 78 ^^^ 1)) (
  addMasksAt 0 (xorMasks (rangeList 31 10) (wMask 79 ^^^ 1)) (
  List.replicate 12 [])))))))))))))))))

def wWideBag : List (List Nat) :=
  addMasksAt 0 (xorMasks (rangeList 30 11) (wMask 80 ^^^ 1)) (
  addMasksAt 0 (xorMasks (rangeList 29 12) (wMask 81 ^^^ 1)) (
  addMasksAt 0 (xorMasks (rangeList 28 13) (wMask 82 ^^^ 1)) (
  addMasksAt 0 (xorMasks (rangeList 27 14) (wMask 83 ^^^ 1)) (
  addMasksAt 0 (xorMasks (rangeList 26 15) (wMask 84 ^^^ 1)) (
  addMasksAt 0 (xorMasks (rangeList 25 16) (wMask 85 ^^^ 1)) (
  addMasksAt 1 (xorMasks (rangeList 25 16) (wMask 86 ^^^ 1)) (
  addMasksAt 2 (wireMasks (rangeList 25 16)) (
  addMasksAt 22 [cin0_m] (
  addMasksAt 22 [q0_m, q19_0_m, q19_1_m, q19_2_m, q19_3_m, q19_4_m, q19_4_m] (
  List.replicate 29 []))))))))))

def bagTakeCols : List Nat → List (List Nat) → List (List Nat)
  | k :: ks, col :: cols => (col.take k) :: bagTakeCols ks cols
  | _, _ => []

def bagDropCols : List Nat → List (List Nat) → List (List Nat)
  | k :: ks, col :: cols => (col.drop k) :: bagDropCols ks cols
  | _, cols => cols

theorem evalCol_append (N : Nat) (env : Nat → Bool) :
    ∀ (c1 c2 : List Nat), evalCol N env (c1 ++ c2) = evalCol N env c1 + evalCol N env c2
  | [], _ => by simp [evalCol]
  | m :: c1, c2 => by
    dsimp only [List.cons_append, evalCol]
    rw [evalCol_append N env c1 c2]; omega

theorem evalCol_take_add_drop (N : Nat) (env : Nat → Bool) (k : Nat) (col : List Nat) :
    evalCol N env (col.take k) + evalCol N env (col.drop k) = evalCol N env col := by
  rw [← evalCol_append N env (col.take k) (col.drop k), List.take_append_drop]

theorem evalBag_bagTakeCols_add_bagDropCols (N : Nat) (env : Nat → Bool) :
    ∀ (ks : List Nat) (bag : List (List Nat)),
      evalBag N env (bagTakeCols ks bag) + evalBag N env (bagDropCols ks bag) = evalBag N env bag
  | [], bag => by simp [bagTakeCols, bagDropCols, evalBag]
  | _ :: _, [] => by simp [bagTakeCols, bagDropCols, evalBag]
  | k :: ks, col :: cols => by
    dsimp only [bagTakeCols, bagDropCols, evalBag]
    have ih := evalBag_bagTakeCols_add_bagDropCols N env ks cols
    have hcol := evalCol_take_add_drop N env k col
    omega

def colTake02 : List Nat → List Nat
  | x0 :: _ :: x2 :: _ => [x0, x2]
  | _ => []

def colDrop02 : List Nat → List Nat
  | _ :: x1 :: _ :: rest => x1 :: rest
  | col => col

theorem evalCol_colTake02_add_colDrop02 (N : Nat) (env : Nat → Bool) :
    ∀ (col : List Nat),
      evalCol N env (colTake02 col) + evalCol N env (colDrop02 col) = evalCol N env col
  | [] => by simp [colTake02, colDrop02, evalCol]
  | [_] => by simp [colTake02, colDrop02, evalCol]
  | [_, _] => by simp [colTake02, colDrop02, evalCol]
  | x0 :: x1 :: x2 :: rest => by dsimp only [colTake02, colDrop02, evalCol]; omega

def movedMask_c1_0 : Nat := wMask 31 ^^^ wMask 80 ^^^ 1
def movedMask_c1_2 : Nat := wMask 29 ^^^ wMask 82 ^^^ 1
def movedMask_c2_0 : Nat := wMask 32 ^^^ wMask 80 ^^^ 1
def movedMask_c2_2 : Nat := wMask 30 ^^^ wMask 82 ^^^ 1
def movedMask_c4 : Nat := wMask 34 ^^^ wMask 80 ^^^ 1

def wWideBagTake02 : List (List Nat) → List (List Nat)
  | _ :: c1 :: c2 :: _ :: c4 :: _ =>
      [[], colTake02 c1, colTake02 c2, [], c4.take 1]
  | _ => []

def wWideBagDrop02 : List (List Nat) → List (List Nat)
  | c0 :: c1 :: c2 :: c3 :: c4 :: rest =>
      c0 :: colDrop02 c1 :: colDrop02 c2 :: c3 :: c4.drop 1 :: rest
  | bag => bag

def wWideBag53 : List (List Nat) := wWideBagDrop02 wWideBag

theorem evalBag_wWideBagTake02_add_Drop02 (N : Nat) (env : Nat → Bool) :
    ∀ (bag : List (List Nat)),
      evalBag N env (wWideBagTake02 bag) + evalBag N env (wWideBagDrop02 bag) = evalBag N env bag
  | c0 :: c1 :: c2 :: c3 :: c4 :: rest => by
    dsimp only [wWideBagTake02, wWideBagDrop02, evalBag, evalCol]
    have h1 := evalCol_colTake02_add_colDrop02 N env c1
    have h2 := evalCol_colTake02_add_colDrop02 N env c2
    have h4 := evalCol_take_add_drop N env 1 c4
    omega
  | [] => by simp [wWideBagTake02, wWideBagDrop02, evalBag]
  | [_] => by simp [wWideBagTake02, wWideBagDrop02, evalBag]
  | [_, _] => by simp [wWideBagTake02, wWideBagDrop02, evalBag]
  | [_, _, _] => by simp [wWideBagTake02, wWideBagDrop02, evalBag]
  | [_, _, _, _] => by simp [wWideBagTake02, wWideBagDrop02, evalBag]

theorem evalBag_wWideBag_split (N : Nat) (env : Nat → Bool) :
    evalBag N env wWideBag =
      evalBag N env wWideBag53 +
      2 * (cond (evalSymMask N env movedMask_c1_0) 1 0) +
      2 * (cond (evalSymMask N env movedMask_c1_2) 1 0) +
      4 * (cond (evalSymMask N env movedMask_c2_0) 1 0) +
      4 * (cond (evalSymMask N env movedMask_c2_2) 1 0) +
      16 * (cond (evalSymMask N env movedMask_c4) 1 0) := by
  have h := (evalBag_wWideBagTake02_add_Drop02 N env wWideBag).symm
  have htake : wWideBagTake02 wWideBag =
      [[], [movedMask_c1_0, movedMask_c1_2], [movedMask_c2_0, movedMask_c2_2],
        [], [movedMask_c4]] := rfl
  change evalBag N env wWideBag =
    evalBag N env (wWideBagTake02 wWideBag) + evalBag N env wWideBag53 at h
  rw [htake] at h
  dsimp only [evalBag, evalCol] at h
  omega

def nNarrowSplit4 : List Nat := [0, 0, 2, 1, 1, 1]
def nNarrowSplit : List Nat := [0, 0, 0, 0] ++ nNarrowSplit4
def nNarrowBag43 : List (List Nat) :=
  addMasksAt 1 [movedMask_c1_0, movedMask_c2_0] (
  addMasksAt 1 [movedMask_c1_2, movedMask_c2_2] (
  bagDropCols nNarrowSplit nNarrowBag))
def nNarrowBag44 : List (List Nat) :=
  addMasksAt 0 [movedMask_c4] (bagTakeCols nNarrowSplit4 (nNarrowBag.drop 4))

theorem evalBag_nNarrowBag_split (N : Nat) (env : Nat → Bool) :
    16 * evalBag N env nNarrowBag44 + evalBag N env nNarrowBag43 =
      evalBag N env nNarrowBag +
      2 * (cond (evalSymMask N env movedMask_c1_0) 1 0) +
      2 * (cond (evalSymMask N env movedMask_c1_2) 1 0) +
      4 * (cond (evalSymMask N env movedMask_c2_0) 1 0) +
      4 * (cond (evalSymMask N env movedMask_c2_2) 1 0) +
      16 * (cond (evalSymMask N env movedMask_c4) 1 0) := by
  unfold nNarrowBag43 nNarrowBag44
  rw [evalBag_addMasksAt, evalBag_addMasksAt, evalBag_addMasksAt]
  have h := (evalBag_bagTakeCols_add_bagDropCols N env nNarrowSplit nNarrowBag).symm
  have htake : bagTakeCols nNarrowSplit nNarrowBag =
    [] :: [] :: [] :: [] :: bagTakeCols nNarrowSplit4 (nNarrowBag.drop 4) := rfl
  rw [htake] at h
  dsimp only [evalBag, evalCol, evalMasksVal] at h ⊢
  omega

theorem bag_4_1_eq : bag_4_1 = addMasksAt 0 b_lo4_init (wWideBag53.take 4) := rfl
theorem bag_4_3_eq : bag_4_3 = addMasksAt 0 (wireMasks b_lo4_w) nNarrowBag43 := rfl
theorem bag_4_4_eq : bag_4_4 =
  addMasksAt 0 (wireMasks z_w) (
  addMasksAt 0 (wireMasks (hi_qs_w.take 7)) (
  addMasksAt 6 [wMask 60] (
  nNarrowBag44 ++ List.replicate 19 []))) := rfl
theorem bag_5_3_eq :
    bag_5_3 =
      addMasksAt 0 (xorMasks b_lo4_w 1) (addMasksAt 4 (wireMasks z_w) wWideBag53) := rfl

def negSlopeNarrow (kv s4 u : Nat) : Nat :=
  slopeTermNeg27 kv 0 13 3 1 s4 u + slopeTermNeg27 kv 1 12 4 1 s4 u +
  slopeTermNeg27 kv 2 11 5 1 s4 u + slopeTermNeg27 kv 3 10 6 1 s4 u +
  slopeTermNeg27 kv 4 9 7 1 s4 u + slopeTermNeg27 kv 5 8 8 1 s4 u +
  slopeTermNeg27 kv 6 7 9 1 s4 u + slopeTermNeg27 kv 7 6 10 1 s4 u

def posSlopeNarrow (kv s4 u : Nat) : Nat :=
  slopeTermPos27 kv 0 13 3 1 s4 u + slopeTermPos27 kv 1 12 4 1 s4 u +
  slopeTermPos27 kv 2 11 5 1 s4 u + slopeTermPos27 kv 3 10 6 1 s4 u +
  slopeTermPos27 kv 4 9 7 1 s4 u + slopeTermPos27 kv 5 8 8 1 s4 u +
  slopeTermPos27 kv 6 7 9 1 s4 u + slopeTermPos27 kv 7 6 10 1 s4 u

def slopeConstNarrow (kv : Nat) : Nat :=
  slopeTermConst27 kv 0 3 0 + slopeTermConst27 kv 1 4 0 +
  slopeTermConst27 kv 2 5 0 + slopeTermConst27 kv 3 6 0 +
  slopeTermConst27 kv 4 7 0 + slopeTermConst27 kv 5 8 0 +
  slopeTermConst27 kv 6 9 0 + slopeTermConst27 kv 7 10 0

def negSlopeWide (kv s4 u : Nat) : Nat :=
  slopeTermNeg27 kv 8 5 11 1 s4 u + slopeTermNeg27 kv 9 4 12 1 s4 u +
  slopeTermNeg27 kv 10 3 13 1 s4 u + slopeTermNeg27 kv 11 2 14 1 s4 u +
  slopeTermNeg27 kv 12 1 15 1 s4 u + slopeTermNeg27 kv 13 0 16 1 s4 u +
  slopeTermNeg27 kv 14 0 16 2 s4 u

def posSlopeWide (kv s4 u : Nat) : Nat :=
  4 * evalBits (uRotBit u s4) 0 16 +
  slopeTermPos27 kv 8 5 11 1 s4 u + slopeTermPos27 kv 9 4 12 1 s4 u +
  slopeTermPos27 kv 10 3 13 1 s4 u + slopeTermPos27 kv 11 2 14 1 s4 u +
  slopeTermPos27 kv 12 1 15 1 s4 u + slopeTermPos27 kv 13 0 16 1 s4 u +
  slopeTermPos27 kv 14 0 16 2 s4 u

def slopeConstWide (kv : Nat) : Nat :=
  slopeTermConst27 kv 8 11 0 + slopeTermConst27 kv 9 12 0 +
  slopeTermConst27 kv 10 13 0 + slopeTermConst27 kv 11 14 0 +
  slopeTermConst27 kv 12 15 0 + slopeTermConst27 kv 13 16 0 +
  slopeTermConst27 kv 14 16 1

def u18SymVal (env : Nat → Bool) : Nat :=
  evalMasksVal 274 env [cin0_m] +
  evalMasksVal 274 env [q0_m, q19_0_m, q19_1_m, q19_2_m, q19_3_m, q19_4_m, q19_4_m]

theorem evalBag_nNarrowBag {N : Nat} {m0 : Fin 100 → Bool} {defs : List (Nat × Nat)}
    (hN : 103 ≤ N) {kv lv s4 u : Nat}
    (hu : ∀ (k : Nat) (hk : k < 16), m0 ⟨25 + k, by omega⟩ = uRotBit u s4 k)
    (hkv : ∀ (b : Nat) (hb : b < 8), m0 ⟨72 + b, by omega⟩ = kv.testBit b)
    (hlv0 : evalSymMask N (buildSymEnv N m0 defs) l8_0_m = lv.testBit 0)
    (hlv : ∀ (j : Nat) (hj : j < 7), m0 ⟨87 + j, by omega⟩ = lv.testBit (1 + j))
    (hsq9 : targVal sq9_w m0 = sq9Val (d9Val u s4)) :
    evalBag N (buildSymEnv N m0 defs) nNarrowBag + negSlopeNarrow kv s4 u =
      curvVal27 lv (d9Val u s4) + posSlopeNarrow kv s4 u + slopeConstNarrow kv := by
  unfold nNarrowBag
  repeat rw [evalBag_addMasksAt]
  rw [evalBag_replicate_nil]
  have hsq_all : ∀ w ∈ sq9_w, w < 100 := by decide
  have hsq_base := (evalMasksVal_wireMasks (defs := defs) hN sq9_w hsq_all).trans hsq9
  have hc0 := evalMasksVal_curvSlice hN hsq9 (by decide : 7 ≤ 9) hlv0
  have hc1 := evalMasksVal_curvSlice hN hsq9 (by decide : 6 ≤ 9)
    ((evalSymMask_wMask (defs := defs) hN (by decide : 87 < 100)).trans (hlv 0 (by decide)))
  have hc2 := evalMasksVal_curvSlice hN hsq9 (by decide : 5 ≤ 9)
    ((evalSymMask_wMask (defs := defs) hN (by decide : 88 < 100)).trans (hlv 1 (by decide)))
  have hc3 := evalMasksVal_curvSlice hN hsq9 (by decide : 4 ≤ 9)
    ((evalSymMask_wMask (defs := defs) hN (by decide : 89 < 100)).trans (hlv 2 (by decide)))
  have hc4 := evalMasksVal_curvSlice hN hsq9 (by decide : 3 ≤ 9)
    ((evalSymMask_wMask (defs := defs) hN (by decide : 90 < 100)).trans (hlv 3 (by decide)))
  have hc5 := evalMasksVal_curvSlice hN hsq9 (by decide : 2 ≤ 9)
    ((evalSymMask_wMask (defs := defs) hN (by decide : 91 < 100)).trans (hlv 4 (by decide)))
  have hc6 := evalMasksVal_curvSlice hN hsq9 (by decide : 1 ≤ 9)
    ((evalSymMask_wMask (defs := defs) hN (by decide : 92 < 100)).trans (hlv 5 (by decide)))
  have hc7 := evalMasksVal_curvSlice hN hsq9 (by decide : 0 ≤ 9)
    ((evalSymMask_wMask (defs := defs) hN (by decide : 93 < 100)).trans (hlv 6 (by decide)))
  have hs0 := evalMasksVal_slopeSlice (defs := defs) hN hu
    (bit_idx := 0) (b_min := 13) (len := 3) (sh_out := 0) (by decide) (by decide)
    (hkv 0 (by decide))
  have hs1 := evalMasksVal_slopeSlice (defs := defs) hN hu
    (bit_idx := 1) (b_min := 12) (len := 4) (sh_out := 0) (by decide) (by decide)
    (hkv 1 (by decide))
  have hs2 := evalMasksVal_slopeSlice (defs := defs) hN hu
    (bit_idx := 2) (b_min := 11) (len := 5) (sh_out := 0) (by decide) (by decide)
    (hkv 2 (by decide))
  have hs3 := evalMasksVal_slopeSlice (defs := defs) hN hu
    (bit_idx := 3) (b_min := 10) (len := 6) (sh_out := 0) (by decide) (by decide)
    (hkv 3 (by decide))
  have hs4 := evalMasksVal_slopeSlice (defs := defs) hN hu
    (bit_idx := 4) (b_min := 9) (len := 7) (sh_out := 0) (by decide) (by decide)
    (hkv 4 (by decide))
  have hs5 := evalMasksVal_slopeSlice (defs := defs) hN hu
    (bit_idx := 5) (b_min := 8) (len := 8) (sh_out := 0) (by decide) (by decide)
    (hkv 5 (by decide))
  have hs6 := evalMasksVal_slopeSlice (defs := defs) hN hu
    (bit_idx := 6) (b_min := 7) (len := 9) (sh_out := 0) (by decide) (by decide)
    (hkv 6 (by decide))
  have hs7 := evalMasksVal_slopeSlice (defs := defs) hN hu
    (bit_idx := 7) (b_min := 6) (len := 10) (sh_out := 0) (by decide) (by decide)
    (hkv 7 (by decide))
  dsimp only [Nat.reduceAdd, Nat.reducePow, Nat.reduceSub]
    at hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 ⊢
  rw [hsq_base, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7]
  unfold curvVal27 curvFromSq9 negSlopeNarrow posSlopeNarrow slopeConstNarrow
  omega

theorem evalBag_wWideBag {m0 : Fin 100 → Bool} {kv s4 u : Nat}
    (hu : ∀ (k : Nat) (hk : k < 16), m0 ⟨25 + k, by omega⟩ = uRotBit u s4 k)
    (hkv : ∀ (b : Nat) (hb1 : 8 ≤ b) (hb2 : b < 15), m0 ⟨72 + b, by omega⟩ = kv.testBit b) :
    let env := buildSymEnv 274 m0 defs_5_3
    evalBag 274 env wWideBag + negSlopeWide kv s4 u =
      posSlopeWide kv s4 u + slopeConstWide kv + 4194304 * u18SymVal env := by
  dsimp only
  have hN : 103 ≤ 274 := by decide
  unfold wWideBag u18SymVal
  repeat rw [evalBag_addMasksAt]
  rw [evalBag_replicate_nil]
  have hr_all : ∀ w ∈ rangeList 25 16, w < 100 := by
    intro w hw; have := mem_rangeList_iff.mp hw; omega
  have hbase := (evalMasksVal_wireMasks (defs := defs_5_3) hN (rangeList 25 16) hr_all).trans
    (targVal_rangeList_eq_evalBits hu 0 16 (by decide))
  have hs8 := evalMasksVal_slopeSlice (defs := defs_5_3) hN hu
    (bit_idx := 8) (b_min := 5) (len := 11) (sh_out := 0) (by decide) (by decide)
    (hkv 8 (by decide) (by decide))
  have hs9 := evalMasksVal_slopeSlice (defs := defs_5_3) hN hu
    (bit_idx := 9) (b_min := 4) (len := 12) (sh_out := 0) (by decide) (by decide)
    (hkv 9 (by decide) (by decide))
  have hs10 := evalMasksVal_slopeSlice (defs := defs_5_3) hN hu
    (bit_idx := 10) (b_min := 3) (len := 13) (sh_out := 0) (by decide) (by decide)
    (hkv 10 (by decide) (by decide))
  have hs11 := evalMasksVal_slopeSlice (defs := defs_5_3) hN hu
    (bit_idx := 11) (b_min := 2) (len := 14) (sh_out := 0) (by decide) (by decide)
    (hkv 11 (by decide) (by decide))
  have hs12 := evalMasksVal_slopeSlice (defs := defs_5_3) hN hu
    (bit_idx := 12) (b_min := 1) (len := 15) (sh_out := 0) (by decide) (by decide)
    (hkv 12 (by decide) (by decide))
  have hs13 := evalMasksVal_slopeSlice (defs := defs_5_3) hN hu
    (bit_idx := 13) (b_min := 0) (len := 16) (sh_out := 0) (by decide) (by decide)
    (hkv 13 (by decide) (by decide))
  have hs14 := evalMasksVal_slopeSlice (defs := defs_5_3) hN hu
    (bit_idx := 14) (b_min := 0) (len := 16) (sh_out := 1) (by decide) (by decide)
    (hkv 14 (by decide) (by decide))
  dsimp only [Nat.reduceAdd, Nat.reducePow] at hbase hs8 hs9 hs10 hs11 hs12 hs13 hs14 ⊢
  rw [hbase]
  unfold negSlopeWide posSlopeWide slopeConstWide
  omega


end QuantumComputation.Specs.ArcsinImpl
