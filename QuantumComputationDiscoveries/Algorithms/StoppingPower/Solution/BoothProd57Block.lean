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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.WeightedCsa3Gen
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.K6SweepAndLoad273
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.MomSlot3WrapKern

@[expose] public section
set_option allowUnsafeReducibility true
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

local instance (priority := 1000000) instNeZeroTwoPow_aux (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

namespace MomSlot0LocalAndMomCombine288
section MomSlot0
open Real Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg HermitianMat
open MomSlots01Slot1ProjKinetic hiding padZeroBits phaseDiagUnitary
open MeasureBranchHadamardSem hiding ket matrix_ext_ket
open StreamingBchComparator
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
attribute [local irreducible] withLtCompLoop

def withCliffAllocCz {M : ℕ} (c : CliffProg M) (body : TempCzProg M) : TempCzProg M :=
  .seq (.cliff c) (.seq body (.cliff c.inv))

@[simp] theorem withCliffAllocCz_countTempAnd {M : ℕ} (c : CliffProg M) (body : TempCzProg M) :
    (withCliffAllocCz c body).countTempAnd = body.countTempAnd := by
  simp [withCliffAllocCz, TempCzProg.countTempAnd]

def withTempBitCz {M : ℕ} (c₁ c₂ anc : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc)
    (h₂a : c₂ ≠ anc) (body : TempCzProg M) : TempCzProg M :=
  .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body

@[simp] theorem withTempBitCz_countTempAnd {M : ℕ} (c₁ c₂ anc : Wire M) (h₁₂ : c₁ ≠ c₂)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (body : TempCzProg M) :
    (withTempBitCz c₁ c₂ anc h₁₂ h₁a h₂a body).countTempAnd = 1 + body.countTempAnd := rfl
end MomSlot0
end MomSlot0LocalAndMomCombine288

namespace Prod57BoothHoist
section ConfigProd57BoothHoist
set_option maxRecDepth 512
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real HermitianMat
open MeasureBranchHadamardSem
open BchCubeDecoder StreamingBchComparator
open scoped Matrix BigOperators Matrix.Norms.L2Operator

theorem TempCtxLiftEx.ltCompLoop {M : ℕ} (W cur : ℕ) (hcur : cur + W + 1 ≤ M)
    (a b : Fin W → Wire M) (hab : ∀ j, a j ≠ b j)
    (ha : ∀ j, (a j).val < cur) (hb : ∀ j, (b j).val < cur) :
    TempCtxLiftEx cur (cur + W + 1) (ctxLtCompLoop W cur hcur a b hab ha hb) :=
  fun {leaf body sBody} hBody ↦ by
    obtain ⟨s, h, _⟩ := ScopedBlock.withLtCompLoop_block W cur hcur a b hab ha hb leaf body sBody
      hBody
    rw [← ctxLtCompLoop_plug] at h
    exact ⟨fun β ↦ sBody (s β), validCleanRem_mono (by omega) h.valid,
      fun β hβ ↦ h.bits β (cleanRem_anti (by omega) hβ),
      fun β hβ ↦ h.sign β (cleanRem_anti (by omega) hβ)⟩

attribute [local irreducible] inPlaceAddMod1 msbClearStatic cleanMsbSubStatic dCleanMsbSub

private theorem p57Out_val_eq {a b : Fin 57} (h : p57OutW a = p57OutW b) : a.val = b.val :=
  congrArg Fin.val (p57OutW_injective h)

private theorem bitsVal_acc20_eq_acc19_msb (m : ℕ) (hm : m ≤ 37) (γ : BitAssignment 437) :
    bitsVal (fun j : Fin 20 ↦ γ (p57Acc20 m hm j)) =
      bitsVal (fun j : Fin 19 ↦ γ (p57Acc19 m hm j)) + 2 ^ 19 * (γ (p57AccMsb m hm)).val :=
  bitsVal_castSucc_split (fun j : Fin 20 ↦ γ (p57Acc20 m hm j))

/-- Clean-tail `[275..437)` program mutating only `p57OutW` with zero phase sign. -/
def p57OutBlock (p : TempPhaseProg 437) : Prop :=
  ValidCleanRem 437 (437 - 275) p ∧
    (∀ β : BitAssignment 437, cleanRem 437 (437 - 275) β → p.evalSign β = 0) ∧
    (∀ β : BitAssignment 437, cleanRem 437 (437 - 275) β →
      cleanRem 437 (437 - 275) (p.evalBits β) ∧
      (∀ q : Wire 437, (∀ k : Fin 57, q ≠ p57OutW k) → p.evalBits β q = β q))

private def p57Block278 (p : TempPhaseProg 437) : Prop :=
  ValidCleanRem 437 (437 - 278) p ∧
    (∀ η, cleanRem 437 (437 - 278) η → p.evalSign η = 0) ∧
    (∀ η, cleanRem 437 (437 - 278) η →
      ∀ u : Wire 437, (∀ k : Fin 57, u ≠ p57OutW k) → p.evalBits η u = η u)

private theorem p57OutW_cleanRem {β δ : BitAssignment 437} (hβ : cleanRem 437 (437 - 275) β)
    (hNon : ∀ q : Wire 437, (∀ k : Fin 57, q ≠ p57OutW k) → δ q = β q) :
    cleanRem 437 (437 - 275) δ :=
  fun w hw ↦ (hNon w fun k ↦ wire_ne_of_gt (lt_of_lt_of_le (p57OutW_lt_275 k) hw)).trans (hβ w hw)

private theorem p57OutBlock_of_278 {p : TempPhaseProg 437} (h : p57Block278 p) : p57OutBlock p :=
  ⟨validCleanRem_mono (by decide) h.1, fun γ hγ ↦ h.2.1 γ (cleanRem_anti (by decide) hγ),
   fun γ hγ ↦ ⟨p57OutW_cleanRem hγ (h.2.2 γ (cleanRem_anti (by decide) hγ)),
     h.2.2 γ (cleanRem_anti (by decide) hγ)⟩⟩

private theorem p57NonOut_sTrue_u38 {β δ : BitAssignment 437}
    (hNon : ∀ q : Wire 437, (∀ k : Fin 57, q ≠ p57OutW k) → δ q = β q) :
    (fun j ↦ δ (sTrue18WDefault j)) = (fun j ↦ β (sTrue18WDefault j)) ∧
      (fun k ↦ δ (p57U38W k)) = (fun k ↦ β (p57U38W k)) :=
  ⟨funext fun j ↦ hNon _ fun k ↦ validSTrueMap_default.2.2.2.2.2.2.1 j k,
   funext fun j ↦ hNon _ fun k hl ↦ by
     have hv := congrArg Fin.val hl
     dsimp [p57U38W, p57OutW] at hv
     split_ifs at hv
     all_goals dsimp at hv
     all_goals omega⟩

private theorem p57OutBlock_seq {p₁ p₂ : TempPhaseProg 437}
    (h₁ : p57OutBlock p₁) (h₂ : p57OutBlock p₂) : p57OutBlock (.seq p₁ p₂) :=
  ⟨⟨437 - 275, by decide, h₁.1, h₂.1, fun β hβ ↦ (h₁.2.2 β hβ).1⟩,
   fun β hβ ↦ by
     dsimp [TempPhaseProg.evalSign]
     rw [h₁.2.1 β hβ, h₂.2.1 _ (h₁.2.2 β hβ).1, zero_add],
   fun β hβ ↦ ⟨(h₂.2.2 _ (h₁.2.2 β hβ).1).1,
     fun q hq ↦ ((h₂.2.2 _ (h₁.2.2 β hβ).1).2 q hq).trans ((h₁.2.2 β hβ).2 q hq)⟩⟩

private theorem p57Slice20_eq {m s₀ s₁ : ℕ} (hm : m ≤ 37) {g₀ g₁ : Fin 57 → ZMod 2}
    (hout : ∀ k : Fin 57, (k.val < m ∨ m + 20 ≤ k.val) → g₁ k = g₀ k)
    (hs₀ : bitsVal (fun j : Fin 20 ↦ g₀ ⟨m + j.val, by omega⟩) = s₀)
    (hs₁ : bitsVal (fun j : Fin 20 ↦ g₁ ⟨m + j.val, by omega⟩) = s₁) :
    bitsVal g₁ + 2 ^ m * s₀ = bitsVal g₀ + 2 ^ m * s₁ := by
  obtain ⟨hlin, _⟩ := bitsVal_slice_linear (N := 57) (W := 20) (k := m) (by omega) g₀ g₁ hout
  rwa [hs₀, hs₁] at hlin

attribute [local irreducible] cBoothRowSetup

private theorem p57WithBoothRowSetup_spec (m : ℕ) (hm : m < 37) {pIn : TempPhaseProg 437}
    (hIn : p57Block278 pIn) :
    let p := withCliffAlloc (cBoothRowSetup m hm) pIn
    p57OutBlock p ∧
      ∀ β : BitAssignment 437, cleanRem 437 (437 - 275) β →
        cleanRem 437 (437 - 278) ((cBoothRowSetup m hm).eval β) ∧
        (∀ k : Fin 57, (cBoothRowSetup m hm).eval β (p57OutW k) = β (p57OutW k)) ∧
        (∀ k : Fin 57, p.evalBits β (p57OutW k) =
          pIn.evalBits ((cBoothRowSetup m hm).eval β) (p57OutW k)) := by
  obtain ⟨hvWrap, hevWrap⟩ := withCliffAlloc_valid_and_eval (M := 437) (rem := 437 - 275)
    (remIn := 437 - 278) (by decide) (by decide) (cBoothRowSetup m hm)
    (cBoothRowSetup_supportsBelow m hm) pIn hIn.1
  have hDisjOut := cBoothRowSetup_disjoint_out m hm
  have hDisjInv := CliffDisjoint.inv hDisjOut
  have hNonAll : ∀ β, cleanRem 437 (437 - 275) β → ∀ q : Wire 437,
      (∀ k : Fin 57, q ≠ p57OutW k) →
      (withCliffAlloc (cBoothRowSetup m hm) pIn).evalBits β q = β q := fun β hβ q hq ↦ by
    obtain ⟨hcη, _, hev1⟩ := hevWrap β hβ
    rw [hev1, hDisjInv.eval_congr_nonMut (fun u hu ↦ hIn.2.2 _ hcη u fun k hk ↦ hu ⟨k, hk⟩)
      q (fun ⟨k, hk⟩ ↦ hq k hk), cliffInv_comp_eval]
  refine ⟨⟨hvWrap, fun β hβ ↦ (hevWrap β hβ).2.1.trans (hIn.2.1 _ (hevWrap β hβ).1),
    fun β hβ ↦ ⟨p57OutW_cleanRem hβ (hNonAll β hβ), hNonAll β hβ⟩⟩, fun β hβ ↦ ?_⟩
  obtain ⟨hcη, _, hev1⟩ := hevWrap β hβ
  exact ⟨hcη, fun k ↦ hDisjOut.eval_mut β ⟨k, rfl⟩,
    fun k ↦ (hev1 ▸ hDisjInv.eval_mut _ ⟨k, rfl⟩)⟩

private theorem p57InPlaceAdd_at_spec (m : ℕ) (hm : m ≤ 37) :
    let pAdd := inPlaceAddMod1 19 278 (by decide) p57B20Row (p57Acc20 m hm) p57CinW
      (fun j ↦ p57OutW_ne_b20Row _ j) (fun j ↦ wire_ne_of_lt (p57OutW_lt_275 _))
      p57B20Row_ne_cin p57B20Row_lt_278
      (fun j ↦ lt_trans (p57OutW_lt_275 _) (by decide)) (by decide)
    p57Block278 pAdd ∧
      ∀ η P R, cleanRem 437 (437 - 278) η → P < 2 ^ (m + 19) → R < 2 ^ 19 →
        bitsVal (fun j ↦ η (p57B20Row j)) + (η p57CinW).val = R →
        bitsVal (fun k ↦ η (p57OutW k)) = P →
        bitsVal (fun k ↦ pAdd.evalBits η (p57OutW k)) = P + 2 ^ m * R := by
  intro pAdd
  obtain ⟨hvAdd, hsAdd, hAdd⟩ := inPlaceAddMod1_spec 19 278 (by decide) p57B20Row (p57Acc20 m hm)
    p57CinW (fun i j ↦ p57OutW_ne_b20Row _ j) (fun j ↦ wire_ne_of_lt (p57OutW_lt_275 _))
    p57B20Row_ne_cin p57B20Row_injective
    (fun i j h ↦ Fin.ext (by have hv := p57Out_val_eq h; dsimp at hv; omega))
    p57B20Row_lt_278 (fun j ↦ lt_trans (p57OutW_lt_275 _) (by decide)) (by decide)
  refine ⟨⟨hvAdd, hsAdd, fun η hcη u hu ↦ (hAdd η hcη).2.1 u fun j ↦ hu ⟨m + j.val, by omega⟩⟩,
    fun η P R hcη hP_lt hR_lt hB20 hP_eq ↦ ?_⟩
  obtain ⟨_, hnonIn, hvalIn⟩ := hAdd η hcη
  let g₀ : Fin 57 → ZMod 2 := fun k ↦ η (p57OutW k)
  let g₁ : Fin 57 → ZMod 2 := fun k ↦ pAdd.evalBits η (p57OutW k)
  have hdiv_lt : P / 2 ^ m < 2 ^ 19 :=
    Nat.div_lt_of_lt_mul (by rwa [show 2 ^ m * 2 ^ 19 = 2 ^ (m + 19) by ring])
  have hsl₀ : bitsVal (fun j : Fin 20 ↦ g₀ ⟨m + j.val, by omega⟩) = P / 2 ^ m := by
    rw [bitsVal_slice_eq_div_mod (by omega) g₀, hP_eq,
      Nat.mod_eq_of_lt (lt_trans hdiv_lt (by decide : 2 ^ 19 < 2 ^ 20))]
  have hlin := p57Slice20_eq (g₁ := g₁) hm
    (fun k _ ↦ hnonIn (p57OutW k) fun j hj ↦ by have hv := p57Out_val_eq hj; dsimp at hv; omega)
    hsl₀ (s₁ := P / 2 ^ m + R) (by
      change bitsVal (fun j : Fin 20 ↦ pAdd.evalBits η (p57Acc20 m hm j)) = _
      rw [hvalIn]
      change (bitsVal (fun j : Fin 20 ↦ g₀ ⟨m + j.val, by omega⟩) + _ + _) % 2 ^ 20 = _
      rw [hsl₀, Nat.add_assoc, hB20, Nat.mod_eq_of_lt (by omega : P / 2 ^ m + R < 2 ^ 20)])
  rw [hP_eq, mul_add] at hlin
  change bitsVal g₁ = _
  omega

private theorem p57CleanMsbSub_at_spec (m : ℕ) (hm : m ≤ 37) :
    let pSub := cleanMsbSubStatic 18 278 (by decide) p57B19Row (p57Acc19 m hm) (p57AccMsb m hm)
      p57CinW (fun j ↦ p57OutW_ne_b19Row _ j) (fun j ↦ wire_ne_of_lt (p57OutW_lt_275 _))
      p57B19Row_ne_cin (wire_ne_of_lt (p57OutW_lt_275 _)) p57B19Row_lt_278
      (fun j ↦ lt_trans (p57OutW_lt_275 _) (by decide))
      (lt_trans (p57OutW_lt_275 _) (by decide)) (by decide)
    p57Block278 pSub ∧
      ∀ η P R, cleanRem 437 (437 - 278) η → P < 2 ^ (m + 19) → R < 2 ^ 19 →
        bitsVal (fun j ↦ η (p57B19Row j)) + (η p57CinW).val = R →
        bitsVal (fun k ↦ η (p57OutW k)) = P + 2 ^ m * R →
        bitsVal (fun k ↦ pSub.evalBits η (p57OutW k)) = P := by
  intro pSub
  obtain ⟨hvSub, hUncondSub, hSumSub⟩ := ctxCleanMsbSub_spec 18 278 (by decide) p57B19Row
    (p57Acc19 m hm) (p57AccMsb m hm) p57CinW
    (fun i j ↦ p57OutW_ne_b19Row _ j) (fun j ↦ wire_ne_of_lt (p57OutW_lt_275 _)) p57B19Row_ne_cin
    (fun j h ↦ by have hv := p57Out_val_eq h; dsimp at hv; omega)
    (fun j ↦ (p57OutW_ne_b19Row _ j).symm) (wire_ne_of_lt (p57OutW_lt_275 _)) p57B19Row_injective
    (fun i j h ↦ Fin.ext (by have hv := p57Out_val_eq h; dsimp at hv; omega))
    p57B19Row_lt_278 (fun j ↦ lt_trans (p57OutW_lt_275 _) (by decide))
    (lt_trans (p57OutW_lt_275 _) (by decide)) (by decide)
  refine ⟨⟨hvSub, fun η hcη ↦ (hUncondSub η hcη).1,
    fun η hcη u hu ↦ (hUncondSub η hcη).2.2 u
      (fun j ↦ hu ⟨m + j.val, by omega⟩) (hu ⟨m + 19, by omega⟩)⟩,
    fun η P R hcη hP_lt hR_lt hB19 hOut ↦ ?_⟩
  let g₀ : Fin 57 → ZMod 2 := fun k ↦ η (p57OutW k)
  let g₁ : Fin 57 → ZMod 2 := fun k ↦ pSub.evalBits η (p57OutW k)
  have hdiv_lt : P / 2 ^ m < 2 ^ 19 :=
    Nat.div_lt_of_lt_mul (by rwa [show 2 ^ m * 2 ^ 19 = 2 ^ (m + 19) by ring])
  have hsl₀ : bitsVal (fun j : Fin 20 ↦ g₀ ⟨m + j.val, by omega⟩) = P / 2 ^ m + R := by
    rw [bitsVal_slice_eq_div_mod (by omega) g₀, hOut, mul_comm (2 ^ m),
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos m),
      Nat.mod_eq_of_lt (by omega : P / 2 ^ m + R < 2 ^ 20)]
  let aOrig : Fin 19 → ZMod 2 := fun j ↦ if (P / 2 ^ m).testBit j.val then 1 else 0
  have haOrig_val : bitsVal aOrig = P / 2 ^ m := bitsVal_eq_of_testBit aOrig _ hdiv_lt fun _ ↦ rfl
  obtain ⟨_, hAcc19_out, hMsb_out⟩ := hSumSub η aOrig hcη (by
    rw [← bitsVal_acc20_eq_acc19_msb m hm η]
    change bitsVal (fun j : Fin 20 ↦ g₀ ⟨m + j.val, by omega⟩) = _
    rw [hsl₀, haOrig_val, Nat.add_assoc, hB19])
  have hlin := p57Slice20_eq (g₁ := g₁) hm
    (fun k _ ↦ (hUncondSub η hcη).2.2 (p57OutW k)
      (fun j hj ↦ by have hv := p57Out_val_eq hj; dsimp at hv; omega)
      (fun hm' ↦ by have hv := p57Out_val_eq hm'; dsimp at hv; omega))
    hsl₀ (s₁ := P / 2 ^ m) (by
      change bitsVal (fun j : Fin 20 ↦ pSub.evalBits η (p57Acc20 m hm j)) = _
      rw [bitsVal_acc20_eq_acc19_msb m hm (pSub.evalBits η),
        show (fun j : Fin 19 ↦ pSub.evalBits η (p57Acc19 m hm j)) = aOrig from funext hAcc19_out,
        hMsb_out, haOrig_val]
      rfl)
  rw [hOut, mul_add] at hlin
  change bitsVal g₁ = _
  omega

private theorem boothAddRows57_countTempAnd :
    ∀ (m : ℕ) (hm : m ≤ 37), (boothAddRows57 m hm).countTempAnd = 18 + 19 * m
  | 0, _ => xorAndVecStatic_countTempAnd _ _ _ _ _ _ _ _ _ _
  | m + 1, _ => by
      simp only [boothAddRows57, boothAddRow57, TempPhaseProg.countTempAnd,
        boothAddRows57_countTempAnd m, withCliffAlloc_countTempAnd, inPlaceAddMod1_countTempAnd]
      omega

private theorem p57B19Row_val_of_clean {γ : BitAssignment 437} (hγ : cleanRem 437 (437 - 275) γ) :
    bitsVal (fun j ↦ γ (p57B19Row j)) + (γ p57CinW).val =
      bitsVal (fun j ↦ γ (sTrue18WDefault j)) := by
  rw [bitsVal_castSucc_split (fun j ↦ γ (p57B19Row j)),
    show (fun j : Fin 18 ↦ γ (p57B19Row j.castSucc)) = fun j ↦ γ (sTrue18WDefault j) from
      funext fun _ ↦ by simp [p57B19Row, Fin.snoc_castSucc],
    show γ (p57B19Row (Fin.last 18)) = 0 from by
      simp only [p57B19Row, Fin.snoc_last]
      exact hγ p57B18W (by decide),
    hγ p57CinW (by decide)]
  simp only [ZMod.val_zero, mul_zero, add_zero]

private theorem p57MulBit_bitsVal (c : ZMod 2) (s : Fin 18 → ZMod 2) :
    bitsVal (fun i : Fin 18 ↦ c * s i) = c.val * bitsVal s := by
  rcases bit_cases c with rfl | rfl
  · simpa only [ZMod.val_zero, zero_mul] using bitsVal_zero 18
  · simp only [show (1 : ZMod 2).val = 1 from rfl, one_mul]

private theorem p57XorInit18_spec :
    let p0 := xorAndVecStatic 18 275 (by decide) (p57U38W 0) sTrue18WDefault p57AccInit18
      (fun j ↦ (validSTrueMap_default.2.2.2.2.2.1 j 0).symm)
      (by dsimp [p57U38W]; decide) validSTrueMap_default.2.1 (fun j ↦ p57OutW_lt_275 _)
    p57OutBlock p0 ∧
      (∀ γ : BitAssignment 437, cleanRem 437 (437 - 275) γ →
        (∀ i : Fin 18, p0.evalBits γ (p57AccInit18 i) =
          γ (p57AccInit18 i) + γ (p57U38W 0) * γ (sTrue18WDefault i)) ∧
        (∀ k : Fin 57, 18 ≤ k.val → p0.evalBits γ (p57OutW k) = γ (p57OutW k))) := by
  obtain ⟨hv0, hs0, h0⟩ := xorAndVecStatic_spec 18 275 (by decide)
    (p57U38W 0) sTrue18WDefault p57AccInit18
    (fun j ↦ (validSTrueMap_default.2.2.2.2.2.1 j 0).symm)
    (fun j ↦ wire_ne_val (by dsimp [p57U38W, p57AccInit18, p57OutW]; omega))
    (fun i j ↦ validSTrueMap_default.2.2.2.2.2.2.1 i ⟨j.val, by omega⟩)
    (fun i j h ↦ Fin.ext (by have hv := p57Out_val_eq h; dsimp at hv; omega))
    (by dsimp [p57U38W]; decide) validSTrueMap_default.2.1 (fun j ↦ p57OutW_lt_275 _)
  refine ⟨⟨hv0, hs0, fun γ hγ ↦ ⟨(h0 γ hγ).1,
    fun q hq ↦ (h0 γ hγ).2.1 q fun j ↦ hq ⟨j.val, by omega⟩⟩⟩, fun γ hγ ↦
    ⟨(h0 γ hγ).2.2, fun k hk ↦ (h0 γ hγ).2.1 (p57OutW k) fun j hj ↦ by
      have hv := p57Out_val_eq hj; dsimp at hv; omega⟩⟩

private theorem boothAddRows57_spec :
    ∀ (m : ℕ) (hm : m ≤ 37),
      let p := boothAddRows57 m hm
      p57OutBlock p ∧
        ∀ β : BitAssignment 437, cleanRem 437 (437 - 275) β →
          (∀ k : Fin 57, β (p57OutW k) = 0) →
          bitsVal (fun k ↦ p.evalBits β (p57OutW k)) =
            boothRad2PrefixVal (bitsVal (fun j ↦ β (sTrue18WDefault j)))
              (fun k ↦ β (p57U38W k)) m hm
  | 0, _ => by
      dsimp only [boothAddRows57]
      obtain ⟨hB0, h0⟩ := p57XorInit18_spec
      refine ⟨hB0, fun β hβ hZero ↦ ?_⟩
      obtain ⟨hacc, hhi⟩ := h0 β hβ
      let g₁ : Fin 57 → ZMod 2 := fun k ↦ (boothAddRows57 0 (by decide)).evalBits β (p57OutW k)
      change bitsVal g₁ = _
      rw [bitsVal_split_at 18 39 g₁,
        show (fun j : Fin 39 ↦ g₁ ⟨18 + j.val, by omega⟩) = fun _ ↦ 0 from
          funext fun j ↦ (hhi ⟨18 + j.val, by omega⟩ (by dsimp; omega)).trans (hZero _),
        bitsVal_zero,
        show (fun i : Fin 18 ↦ g₁ ⟨i.val, by omega⟩) =
            fun i : Fin 18 ↦ β (p57U38W 0) * β (sTrue18WDefault i) from funext fun i ↦ by
          dsimp only [g₁, boothAddRows57]
          exact (show _ = β (p57OutW _) + _ from hacc i).trans
            (by rw [hZero ⟨i.val, by omega⟩, zero_add]),
        p57MulBit_bitsVal]
      simp only [boothRad2PrefixVal, mul_zero, add_zero]
  | m + 1, hm => by
      dsimp only [boothAddRows57, boothAddRow57]
      obtain ⟨hB₁, hval₁⟩ := boothAddRows57_spec m (by omega)
      obtain ⟨hAddB, hvalAdd⟩ := p57InPlaceAdd_at_spec m (by omega)
      obtain ⟨hB₂, hWrap⟩ := p57WithBoothRowSetup_spec m (by omega) hAddB
      refine ⟨p57OutBlock_seq hB₁ hB₂, fun β hβ hZero ↦ ?_⟩
      obtain ⟨hcl₁, hnon₁⟩ := hB₁.2.2 β hβ
      obtain ⟨hS₁, hu₁⟩ := p57NonOut_sTrue_u38 hnon₁
      let β₁ := (boothAddRows57 m (by omega)).evalBits β
      obtain ⟨hcη, hη_out, hp_out⟩ := hWrap β₁ hcl₁
      dsimp only [TempPhaseProg.evalBits]
      rw [show (fun k ↦ (withCliffAlloc (cBoothRowSetup m _) _).evalBits β₁ (p57OutW k)) =
          _ from funext hp_out,
        hvalAdd _ _ _ hcη (boothRad2PrefixVal_lt _ (bitsVal_lt_two_pow _) _ m (by omega))
          (boothRad2RowVal_lt _ (bitsVal_lt_two_pow _) _)
          (cBoothRowSetup_val m (by omega) β₁ hcl₁).2.2
          ((congrArg bitsVal (funext hη_out)).trans (hval₁ β hβ hZero)), hS₁,
        show β₁ (p57U38W ⟨m + 1, by omega⟩) = β (p57U38W ⟨m + 1, by omega⟩) from
          congrFun hu₁ ⟨m + 1, by omega⟩]
      rfl

attribute [local irreducible] boothAddRow57

theorem boothAdd57_275_spec : ValidCleanRem 437 (437 - 275) boothAdd57_275 ∧
    boothAdd57_275.countTempAnd = 740 ∧
    (∀ β : BitAssignment 437, cleanRem 437 (437 - 275) β → boothAdd57_275.evalSign β = 0) ∧
    (∀ β : BitAssignment 437, cleanRem 437 (437 - 275) β →
      cleanRem 437 (437 - 275) (boothAdd57_275.evalBits β) ∧
      (∀ q : Wire 437, (∀ m : Fin 57, q ≠ p57OutW m) → boothAdd57_275.evalBits β q = β q) ∧
      ((∀ m : Fin 57, β (p57OutW m) = 0) →
        bitsVal (fun m ↦ boothAdd57_275.evalBits β (p57OutW m)) =
          bitsVal (fun j ↦ β (sTrue18WDefault j)) *
            (bitsVal (fun k ↦ β (p57U38W k)) + 1) + boothConst57)) := by
  have hCnt740 : boothAdd57_275.countTempAnd = 740 := by
    dsimp only [boothAdd57_275, boothAddTop57, TempPhaseProg.countTempAnd]
    rw [boothAddRows57_countTempAnd 37 (by decide), inPlaceAddMod1_countTempAnd]
  dsimp only [boothAdd57_275]
  obtain ⟨hB₁, hval₁⟩ := boothAddRows57_spec 37 (by decide)
  obtain ⟨hTop278, hvalTop⟩ := p57InPlaceAdd_at_spec 37 (by decide)
  have hBSeq := p57OutBlock_seq hB₁ (p57OutBlock_of_278 hTop278)
  refine ⟨hBSeq.1, hCnt740, hBSeq.2.1, fun β hβ ↦
    ⟨(hBSeq.2.2 β hβ).1, (hBSeq.2.2 β hβ).2, fun hZero ↦ ?_⟩⟩
  obtain ⟨hcl₁, hnon₁⟩ := hB₁.2.2 β hβ
  obtain ⟨hS₁, _⟩ := p57NonOut_sTrue_u38 hnon₁
  let β₁ := (boothAddRows57 37 (by decide)).evalBits β
  set S := bitsVal (fun j ↦ β (sTrue18WDefault j))
  have hS_lt : S < 2 ^ 18 := bitsVal_lt_two_pow _
  have hB20_top : bitsVal (fun j ↦ β₁ (p57B20Row j)) + (β₁ p57CinW).val = S := by
    rw [bitsVal_castSucc_split (fun j ↦ β₁ (p57B20Row j)),
      show (fun j : Fin 19 ↦ β₁ (p57B20Row j.castSucc)) = fun j ↦ β₁ (p57B19Row j) from
        funext fun _ ↦ congrArg β₁ (Fin.snoc_castSucc _ _ _),
      show β₁ (p57B20Row (Fin.last 19)) = 0 from
        (congrArg β₁ (Fin.snoc_last _ _)).trans (hcl₁ p57Z19W (by decide)),
      show ZMod.val (0 : ZMod 2) = 0 from rfl, mul_zero, add_zero,
      p57B19Row_val_of_clean (γ := β₁) hcl₁, hS₁]
  dsimp only [TempPhaseProg.evalBits, boothAddTop57]
  rw [hvalTop β₁ _ S (cleanRem_anti (by decide) hcl₁)
    (boothRad2PrefixVal_lt S hS_lt _ 37 (by decide))
    (lt_trans hS_lt (by decide : 2 ^ 18 < 2 ^ 19)) hB20_top (hval₁ β hβ hZero),
    (boothRad2PrefixVal_37_add_top S hS_lt (fun k ↦ β (p57U38W k))).1]

attribute [local irreducible] boothAddTop57 boothAddRows57 boothAdd57_275

private theorem boothSubRows57_countTempAnd :
    ∀ (m : ℕ) (hm : m ≤ 37), (boothSubRows57 m hm).countTempAnd = 18 + 19 * m
  | 0, _ => xorAndVecStatic_countTempAnd _ _ _ _ _ _ _ _ _ _
  | m + 1, _ => by
      simp only [boothSubRows57, boothSubRow57, TempPhaseProg.countTempAnd,
        withCliffAlloc_countTempAnd, cleanMsbSubStatic_countTempAnd, boothSubRows57_countTempAnd m]
      omega

private theorem boothSubRows57_spec :
    ∀ (m : ℕ) (hm : m ≤ 37),
      let p := boothSubRows57 m hm
      p57OutBlock p ∧
        ∀ γ : BitAssignment 437, cleanRem 437 (437 - 275) γ →
          bitsVal (fun k ↦ γ (p57OutW k)) =
            boothRad2PrefixVal (bitsVal (fun j ↦ γ (sTrue18WDefault j)))
              (fun k ↦ γ (p57U38W k)) m hm →
          ∀ k : Fin 57, p.evalBits γ (p57OutW k) = 0
  | 0, _ => by
      dsimp only [boothSubRows57]
      obtain ⟨hB0, h0⟩ := p57XorInit18_spec
      refine ⟨hB0, fun γ hγ hInv k ↦ ?_⟩
      obtain ⟨hacc, hhi⟩ := h0 γ hγ
      let g₀ : Fin 57 → ZMod 2 := fun l ↦ γ (p57OutW l)
      have hsplit := bitsVal_split_at 18 39 g₀
      dsimp only [boothRad2PrefixVal, mul_zero, add_zero] at hInv
      change bitsVal g₀ = _ at hInv
      rw [← p57MulBit_bitsVal] at hInv
      have hrhs_lt := bitsVal_lt_two_pow (fun i : Fin 18 ↦ γ (p57U38W 0) * γ (sTrue18WDefault i))
      by_cases hk : k.val < 18
      · have hlo_fn := congrFun (bitsVal_injective (show
          bitsVal (fun i : Fin 18 ↦ g₀ ⟨i.val, by omega⟩) =
            bitsVal (fun i : Fin 18 ↦ γ (p57U38W 0) * γ (sTrue18WDefault i)) by omega)) ⟨k.val, hk⟩
        change _ = (0 : ZMod 2)
        rw [show p57OutW k = p57AccInit18 ⟨k.val, hk⟩ from rfl, hacc ⟨k.val, hk⟩,
          show γ (p57AccInit18 ⟨k.val, hk⟩) = _ from hlo_fn, CharTwo.add_self_eq_zero]
      · have hhi_fn : (fun j : Fin 39 ↦ g₀ ⟨18 + j.val, by omega⟩) = fun _ ↦ 0 :=
          bitsVal_injective (by
            rw [show bitsVal (fun j : Fin 39 ↦ g₀ ⟨18 + j.val, by omega⟩) = 0 by omega,
              bitsVal_zero])
        have h := congrFun hhi_fn ⟨k.val - 18, by omega⟩
        dsimp [g₀] at h
        rw [hhi k (by omega)]
        rwa [show (⟨18 + (k.val - 18), by omega⟩ : Fin 57) = k from Fin.ext (by dsimp; omega)] at h
  | m + 1, hm => by
      dsimp only [boothSubRows57, boothSubRow57]
      obtain ⟨hSubB, hvalSub⟩ := p57CleanMsbSub_at_spec m (by omega)
      obtain ⟨hB₁, hWrap⟩ := p57WithBoothRowSetup_spec m (by omega) hSubB
      obtain ⟨hB₂, hval₂⟩ := boothSubRows57_spec m (by omega)
      refine ⟨p57OutBlock_seq hB₁ hB₂, fun γ hγ hInv ↦ ?_⟩
      obtain ⟨hcl₁, hnon₁⟩ := hB₁.2.2 γ hγ
      obtain ⟨hS₁, hu₁⟩ := p57NonOut_sTrue_u38 hnon₁
      obtain ⟨hcη, hη_out, hp_out⟩ := hWrap γ hγ
      refine hval₂ _ hcl₁ ?_
      rw [hS₁, hu₁, show (fun k ↦ (withCliffAlloc (cBoothRowSetup m _) _).evalBits γ (p57OutW k)) =
        _ from funext hp_out]
      exact hvalSub _ _ _ hcη
        (boothRad2PrefixVal_lt _ (bitsVal_lt_two_pow _) _ m (by omega))
        (boothRad2RowVal_lt _ (bitsVal_lt_two_pow _) _) (cBoothRowSetup_val m (by omega) γ hγ).2.1
        ((congrArg bitsVal (funext hη_out)).trans hInv)

attribute [local irreducible] boothSubRow57 boothSubRows57

theorem boothSub57_275_spec : ValidCleanRem 437 (437 - 275) boothSub57_275 ∧
    boothSub57_275.countTempAnd = 740 ∧
    (∀ γ : BitAssignment 437, cleanRem 437 (437 - 275) γ → boothSub57_275.evalSign γ = 0) ∧
    (∀ γ : BitAssignment 437, cleanRem 437 (437 - 275) γ →
      cleanRem 437 (437 - 275) (boothSub57_275.evalBits γ) ∧
      (∀ q : Wire 437, (∀ m : Fin 57, q ≠ p57OutW m) → boothSub57_275.evalBits γ q = γ q) ∧
      (bitsVal (fun m ↦ γ (p57OutW m)) =
        bitsVal (fun j ↦ γ (sTrue18WDefault j)) * (bitsVal (fun k ↦ γ (p57U38W k)) + 1) +
          boothConst57 → ∀ m : Fin 57, boothSub57_275.evalBits γ (p57OutW m) = 0)) := by
  have hCnt740 : boothSub57_275.countTempAnd = 740 := by
    dsimp only [boothSub57_275, boothSubTop57, TempPhaseProg.countTempAnd]
    rw [cleanMsbSubStatic_countTempAnd, boothSubRows57_countTempAnd 37 (by decide)]
  obtain ⟨hTop278, hvalTop⟩ := p57CleanMsbSub_at_spec 37 (by decide)
  have hBTop : p57OutBlock boothSubTop57 := p57OutBlock_of_278 hTop278
  obtain ⟨hBRows, hvalRows⟩ := boothSubRows57_spec 37 (by decide)
  dsimp only [boothSub57_275]
  have hBSeq := p57OutBlock_seq hBTop hBRows
  refine ⟨hBSeq.1, hCnt740, hBSeq.2.1, fun γ hγ ↦
    ⟨(hBSeq.2.2 γ hγ).1, (hBSeq.2.2 γ hγ).2, fun hInit ↦ ?_⟩⟩
  obtain ⟨hclTop, hnonTop'⟩ := hBTop.2.2 γ hγ
  obtain ⟨hS₁, hu₁⟩ := p57NonOut_sTrue_u38 hnonTop'
  set S := bitsVal (fun j ↦ γ (sTrue18WDefault j))
  have hS_lt : S < 2 ^ 18 := bitsVal_lt_two_pow _
  refine hvalRows _ hclTop ?_
  rw [hS₁, hu₁]
  exact hvalTop γ _ S (cleanRem_anti (by decide) hγ)
    (boothRad2PrefixVal_lt S hS_lt _ 37 (by decide))
    (lt_trans hS_lt (by decide : 2 ^ 18 < 2 ^ 19)) (p57B19Row_val_of_clean hγ)
    (hInit.trans (boothRad2PrefixVal_37_add_top S hS_lt (fun k ↦ γ (p57U38W k))).1.symm)
attribute [local irreducible] boothSubTop57 boothSub57_275
end
end ConfigProd57BoothHoist
end Prod57BoothHoist

namespace StepBBlock0
section ConfigStepBBlock0
set_option maxRecDepth 512
set_option backward.isDefEq.respectTransparency false
open SpecsAux.DyadicSubgridToeplitz512AndShift DyadicQft64 Operator
open Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open TempPhaseProg (cnot seq tempAnd x)
open scoped Matrix BigOperators Matrix.Norms.L2Operator

theorem cliffDisjoint_eval_congr_outside {M : ℕ} {mutW : Wire M → Prop} :
    ∀ {c : CliffProg M}, CliffDisjoint mutW c →
      ∀ {γ₁ γ₂ : BitAssignment M}, (∀ u, ¬ mutW u → γ₁ u = γ₂ u) →
      ∀ w, ¬ mutW w → c.eval γ₁ w = c.eval γ₂ w
  | .nil, _, _, _, hEq, w, hw => hEq w hw
  | .x q, hq, _, _, hEq, w, hw => by
      dsimp [CliffProg.eval]
      rcases eq_or_ne w q with rfl | hwq
      · simp [Function.update_self, hEq w hq]
      · simp [Function.update_of_ne hwq, hEq w hw]
  | .cnot c₁ t₁ _, ⟨hc₁, ht₁⟩, _, _, hEq, w, hw => by
      dsimp [CliffProg.eval]
      rcases eq_or_ne w t₁ with rfl | hwt
      · simp [Function.update_self, hEq w ht₁, hEq c₁ hc₁]
      · simp [Function.update_of_ne hwt, hEq w hw]
  | .seq _ _, ⟨hd₁, hd₂⟩, _, _, hEq, w, hw =>
      cliffDisjoint_eval_congr_outside hd₂ (cliffDisjoint_eval_congr_outside hd₁ hEq) w hw

/-- Clean-tail version of `TempCtx.plug_evalBits_split`: only requires `hBodyNonMut` on
`cleanRem M (M - curHole)` states, allowing `body` itself to use `.tempAnd` scratch wires in
`[curHole .. M)`. -/
theorem plug_evalBits_split_clean {M : ℕ} {mutW : Wire M → Prop} {curHole : ℕ} {K : TempCtx M}
    (hDisj : K.DisjointFrom mutW) (hSupp : K.SupportsBelowCtx curHole)
    {body : TempPhaseProg M}
    (hBodyNonMut : ∀ γ, cleanRem M (M - curHole) γ → ∀ w, ¬ mutW w → body.evalBits γ w = γ w)
    (q₀ : Wire M) :
    ∀ (β : BitAssignment M), cleanRem M (M - curHole) β →
      (∀ w, mutW w → (K.plug body).evalBits β w = body.evalBits (K.fwdBits β) w) ∧
      (∀ w, ¬ mutW w → (K.plug body).evalBits β w = (K.plug (.z q₀)).evalBits β w) := by
  induction K with
  | hole => exact fun β hβ ↦ ⟨fun _ _ ↦ rfl, hBodyNonMut β hβ⟩
  | seqPre c _ ih =>
      exact fun β hβ ↦ ih hDisj.2 hSupp.2 (c.eval β) fun w hw ↦
        (c.eval_outside hSupp.1 β w (by omega)).trans (hβ w hw)
  | seqPost _ _ ih =>
      exact fun β hβ ↦ ⟨fun w hw ↦ (hDisj.2.eval_mut _ hw).trans ((ih hDisj.1 hSupp.1 β hβ).1 w hw),
        cliffDisjoint_eval_congr_outside hDisj.2 (ih hDisj.1 hSupp.1 β hβ).2⟩
  | tempAnd c₁ c₂ anc _ _ _ K₁ ih =>
      intro β hβ
      obtain ⟨hM, hN⟩ := ih hDisj.2.2.2 hSupp.2 (Function.update β anc (β anc + β c₁ * β c₂))
        fun w hw ↦ by
          rw [Function.update_of_ne (wire_ne_of_gt (s3LtLe hSupp.1 (by omega)))]
          exact hβ w hw
      refine ⟨fun w hw ↦ (Function.update_of_ne
        (fun heq : w = anc ↦ hDisj.2.2.1 (heq ▸ hw)) _ _).trans (hM w hw), fun w hw ↦ ?_⟩
      dsimp only [TempCtx.plug, TempPhaseProg.evalBits]
      rcases eq_or_ne w anc with rfl | hwa
      · rw [Function.update_self, Function.update_self,
          hN w hDisj.2.2.1, hN c₁ hDisj.1, hN c₂ hDisj.2.1]
      · rw [Function.update_of_ne hwa, Function.update_of_ne hwa, hN w hw]

theorem plug_validCleanRem_clean {M : ℕ} {mutW : Wire M → Prop} {curHole : ℕ} {K : TempCtx M}
    (hDisj : K.DisjointFrom mutW) (hSupp : K.SupportsBelowCtx curHole)
    {body : TempPhaseProg M} (hBodyValid : ValidCleanRem M (M - curHole) body)
    (hBodyNonMut : ∀ γ, cleanRem M (M - curHole) γ → ∀ w, ¬ mutW w → body.evalBits γ w = γ w)
    (q₀ : Wire M) :
    ∀ {rem : ℕ}, M - curHole ≤ rem → ValidCleanRem M rem (K.plug (.z q₀)) →
      ValidCleanRem M rem (K.plug body) := by
  induction K with
  | hole => exact fun hle _ ↦ validCleanRem_mono hle hBodyValid
  | seqPre c K₁ ih =>
      intro rem _ ⟨remMid, hmid, _, hv₁, hpres₁⟩
      refine ⟨max remMid (M - curHole), by omega, trivial,
        ih hDisj.2 hSupp.2 (Nat.le_max_right _ _) (validCleanRem_mono (Nat.le_max_left _ _) hv₁),
        fun β hβ w hw ↦ ?_⟩
      by_cases hw1 : M - remMid ≤ w.val
      · exact hpres₁ β hβ w hw1
      · exact (c.eval_outside hSupp.1 β w (by omega)).trans (hβ w (by omega))
  | seqPost K₁ c ih =>
      exact fun hle ⟨_, _, hv₁, _, _⟩ ↦ ⟨0, Nat.zero_le M, ih hDisj.1 hSupp.1 hle hv₁, trivial,
        fun _ _ _ hw ↦ absurd hw (by omega)⟩
  | tempAnd c₁ c₂ anc _ _ _ K₁ ih =>
      intro rem _ ⟨hanc_lo, hv₁, hpres₁⟩
      have hrem' : M - curHole ≤ M - (anc.val + 1) := by have := hSupp.1; omega
      refine ⟨hanc_lo, ih hDisj.2.2.2 hSupp.2 hrem' hv₁, fun β₁ hβ₁ ↦ ?_⟩
      obtain ⟨_, hN⟩ := plug_evalBits_split_clean hDisj.2.2.2 hSupp.2 hBodyNonMut q₀ β₁
        (cleanRem_anti hrem' hβ₁)
      rw [hN c₁ hDisj.1, hN c₂ hDisj.2.1, hN anc hDisj.2.2.1]
      exact hpres₁ β₁ hβ₁

/-- General mutating-body grafting theorem allowing `body` itself to use `.tempAnd` clean scratch
wires in `[curHole .. M)`: zero `T`-gate uncomputation of `K` around ANY clean-tail mutating `body`.
-/
theorem ScopedBlock.graft_mutating_clean {M rem curHole : ℕ} [NeZero M] (mutW : Wire M → Prop)
    [DecidablePred mutW] (K : TempCtx M) (hDisj : K.DisjointFrom mutW)
    (hSupp : K.SupportsBelowCtx curHole) (hle : M - curHole ≤ rem)
    (setup : BitAssignment M → BitAssignment M)
    (hProbe : ∀ q : Wire M, ScopedBlock M rem setup (.z q) (K.plug (.z q)))
    (body : TempPhaseProg M) (hBodyValid : ValidCleanRem M (M - curHole) body)
    (hBodyNonMut : ∀ γ, cleanRem M (M - curHole) γ → ∀ w, ¬ mutW w → body.evalBits γ w = γ w) :
    ValidCleanRem M rem (K.plug body) ∧
      (K.plug body).countTempAnd = K.countTempAnd + body.countTempAnd ∧
      (∀ β : BitAssignment M, cleanRem M rem β →
        (K.plug body).evalSign β = body.evalSign (setup β)) ∧
      (∀ β : BitAssignment M, cleanRem M rem β → ∀ w : Wire M,
        (K.plug body).evalBits β w = if mutW w then body.evalBits (setup β) w else β w) := by
  let q₀ : Wire M := ⟨0, NeZero.pos M⟩
  have hFwd : ∀ β : BitAssignment M, cleanRem M rem β → K.fwdBits β = setup β := fun β hβ ↦
    funext fun q ↦ (K.plug_evalSign (.z q) β).symm.trans ((hProbe q).sign β hβ)
  refine ⟨plug_validCleanRem_clean hDisj hSupp hBodyValid hBodyNonMut q₀ hle (hProbe q₀).valid,
    K.plug_countTempAnd body, fun β hβ ↦ by rw [K.plug_evalSign, hFwd β hβ], fun β hβ w ↦ ?_⟩
  obtain ⟨hM, hN⟩ := plug_evalBits_split_clean hDisj hSupp hBodyNonMut q₀ β (cleanRem_anti hle hβ)
  by_cases hw : mutW w
  · simp only [hw, ↓reduceIte, hM w hw, hFwd β hβ]
  · simp only [hw, ↓reduceIte, hN w hw, (hProbe q₀).bits β hβ]

/-- Distinct wire indices imply distinct `Wire M` values. -/
theorem wire_ne_val {M : ℕ} (a b : Wire M) (h : a.val ≠ b.val) : a ≠ b :=
  fun heq ↦ h (congrArg Fin.val heq)
end ConfigStepBBlock0
end StepBBlock0

namespace StepBOuter
section ConfigStepBOuter
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real HermitianMat
open _root_.QuantumComputation.Specs.StoppingPowerSolution (cleanRem)
open MomSlots35Slot3ProjNuclear (cRad7Computable s3FineRad_54bit_bounds)
open StepBBlock0 (s3ItePos s3IteNeg s3DitePos s3DiteNeg
  zmod2_eq_zero_or_one bitsVal_castSucc_mod bitsVal_eq_of_testBit bitsVal_injective cnotVec
  xorBlock_of_ctx ctxRippleAddCarry ctxRippleAddCarry_countTempAnd ctxRippleAddCarry_props
  ctxRippleAddCarry_scoped ctxLtCompLoop ctxLtCompLoop_countTempAnd ctxLtCompLoop_props
  ctxLtCompLoop_scoped TempCtxLiftEx IsMutBlock)
open Prod57BoothHoist (boothConst57 p57ProjW p57S3W p57MW p57OutW
  sTrue18FwdPBuf275 sTrue18RevPBuf275 boothAdd57_275 boothSub57_275)
open scoped Matrix BigOperators

def axCtx275 (w : Fin 3) : TempCtx 437 :=
  (ctxCliffAlloc (axPrepCliff w)).append
    ((ctxLtCompLoop 8 299 (by decide) axAW axBW
      (fun b ↦ wire_ne_of_lt (by dsimp [axAW, axBW]; omega))
      (fun b ↦ by dsimp [axAW]; omega) (fun b ↦ by dsimp [axBW]; omega)).append
    (ctxRippleAddCarry 8 308 (by decide) (p57ProjW w) axBAddW axLtW
      (fun b ↦ wire_ne_of_lt (by dsimp [p57ProjW, axBAddW]; omega))
      (fun b ↦ wire_ne_of_lt (by dsimp [p57ProjW, axLtW]; omega))
      (fun b ↦ wire_ne_of_lt (by dsimp [axBAddW, axLtW]; omega))
      (fun b ↦ by dsimp [p57ProjW]; omega)
      (fun b ↦ by dsimp [axBAddW]; omega) (by dsimp [axLtW]; omega)))

/-- Single-axis stepped-projectile XOR `pBufW w ⊕= axisFastVal p_w m_w s_w` (`16` `tempAnd`s). -/
def axisStep1_275 (w : Fin 3) : TempPhaseProg 437 :=
  let src8 : Fin 8 → Wire 437 := fun b ↦ rippleAddCarryWires 8 308 (by decide) axLtW b.castSucc
  let hne : ∀ b : Fin 8, src8 b ≠ pBufW w b := fun b ↦ by
    have hb := (rippleAddCarryWires_bounds (M := 437) 8 308 (by decide) axLtW (by decide)).2
      b.castSucc
    exact wire_ne_of_gt (by dsimp [src8, pBufW, axLtW] at hb ⊢; omega)
  (axCtx275 w).plug (.cliff (cnotVec 8 src8 (pBufW w) hne))

private theorem axisStep1_275_spec (w : Fin 3) : IsMutBlock 437 (437 - 275)
    (fun q ↦ ∃ b, q = pBufW w b) (axisStep1_275 w) ∧
    (axisStep1_275 w).countTempAnd = 16 ∧
    (∀ β, cleanRem 437 (437 - 275) β → ∀ b : Fin 8,
      (axisStep1_275 w).evalBits β (pBufW w b) = β (pBufW w b) +
        if (axisFastVal ⟨bitsVal (fun j ↦ β (p57ProjW w j)), bitsVal_lt_two_pow _⟩
          (bitsVal (fun j ↦ β (p57MW w j))) (β (p57S3W w)).val).testBit b.val then 1 else 0) := by
  obtain ⟨hsP, hdP, hpresP, hvalP⟩ := axPrepCliff_props w
  obtain ⟨hdLt, hsLt⟩ := ctxLtCompLoop_props (mutW := fun q ↦ ∃ b, q = pBufW w b)
    8 299 (by decide) axAW axBW _ _ _
    (fun b ⟨k, h⟩ ↦ by have hv := congrArg Fin.val h; dsimp [axAW, pBufW] at hv; omega)
    (fun b ⟨k, h⟩ ↦ by have hv := congrArg Fin.val h; dsimp [axBW, pBufW] at hv; omega)
    (fun q hq ⟨k, h⟩ ↦ by subst h; dsimp [pBufW] at hq; omega)
  obtain ⟨hdAdd, hsAdd⟩ := ctxRippleAddCarry_props (mutW := fun q ↦ ∃ b, q = pBufW w b)
    8 308 (by decide) (p57ProjW w) axBAddW axLtW _ _ _ _ _ _
    (fun b ⟨k, h⟩ ↦ by have hv := congrArg Fin.val h; dsimp [p57ProjW, pBufW] at hv; omega)
    (fun b ⟨k, h⟩ ↦ by have hv := congrArg Fin.val h; dsimp [axBAddW, pBufW] at hv; omega)
    (fun ⟨k, h⟩ ↦ by have hv := congrArg Fin.val h; dsimp [axLtW, pBufW] at hv; omega)
    (fun q hq ⟨k, h⟩ ↦ by subst h; dsimp [pBufW] at hq; omega)
  have hLift : TempCtxLiftEx 275 324 (axCtx275 w) := TempCtxLiftEx.append
    (TempCtxLiftEx.mono (cur₀ := 275) (next₁ := 299) (by decide) le_rfl (by decide)
      (TempCtxLiftEx.cliff (cur := 299) (by decide) (axPrepCliff w) hsP))
    (TempCtxLiftEx.append (TempCtxLiftEx.ltCompLoop 8 299 (by decide) axAW axBW _ _ _)
      (TempCtxLiftEx.rippleAddCarry 8 308 (by decide) (p57ProjW w) axBAddW axLtW _ _ _ _ _ _))
  let src8 : Fin 8 → Wire 437 := fun b ↦ rippleAddCarryWires 8 308 (by decide) axLtW b.castSucc
  have hinjOut : Function.Injective (pBufW w) :=
    fun i j h ↦ Fin.ext (by have hv := congrArg Fin.val h; dsimp [pBufW] at hv; omega)
  obtain ⟨hv, hcnt, hsgn, hbits⟩ := xorBlock_of_ctx (M := 437) (curStart := 275) (curEnd := 324)
    (W := 8) (by decide) (by decide) (pBufW w) (fun b ↦ by dsimp [pBufW]; omega) hinjOut
    src8 (fun b ↦ by
      have hb := (rippleAddCarryWires_bounds (M := 437) 8 308 (by decide) axLtW (by decide)).2
        b.castSucc
      dsimp [src8, axLtW] at hb ⊢
      omega) (axCtx275 w)
    (TempCtx.disjointFrom_append (ctxCliffAlloc_disjoint hdP)
      (TempCtx.disjointFrom_append hdLt hdAdd))
    (TempCtx.supportsBelowCtx_append le_rfl
      (StepBBlock0.TempCtx.supportsBelowCtx_mono (by decide)
        (ctxCliffAlloc_supports hsP))
      (TempCtx.supportsBelowCtx_append le_rfl
        (StepBBlock0.TempCtx.supportsBelowCtx_mono (by decide) hsLt)
        hsAdd)) _ hLift.probe
  have hnon : ∀ β, cleanRem 437 (437 - 275) β → ∀ q, ¬(∃ b, q = pBufW w b) →
      (axisStep1_275 w).evalBits β q = β q := fun β hβ q hq ↦ by
    dsimp only [axisStep1_275]
    rw [hbits β hβ q, s3DiteNeg hq]
  refine ⟨⟨hv, hsgn, fun β hβ u hu ↦
    (hnon β hβ u fun ⟨b, hb⟩ ↦ by subst hb; dsimp [pBufW] at hu; omega).trans (hβ u hu), hnon⟩,
    hcnt.trans (by
      dsimp only [axCtx275]
      rw [StepBBlock0.TempCtx.append_countTempAnd,
        StepBBlock0.TempCtx.append_countTempAnd,
        ctxLtCompLoop_countTempAnd, ctxRippleAddCarry_countTempAnd]
      rfl),
    fun β hβ b ↦ ?_⟩
  let γ₁ := (axPrepCliff w).eval β
  let γ₂ := (ctxLtCompLoop 8 299 (by decide) axAW axBW
    (fun b ↦ wire_ne_of_lt (by dsimp [axAW, axBW]; omega))
    (fun b ↦ by dsimp [axAW]; omega) (fun b ↦ by dsimp [axBW]; omega)).fwdBits γ₁
  let γ₃ := (ctxRippleAddCarry 8 308 (by decide) (p57ProjW w) axBAddW axLtW
    (fun b ↦ wire_ne_of_lt (by dsimp [p57ProjW, axBAddW]; omega))
    (fun b ↦ wire_ne_of_lt (by dsimp [p57ProjW, axLtW]; omega))
    (fun b ↦ wire_ne_of_lt (by dsimp [axBAddW, axLtW]; omega))
    (fun b ↦ by dsimp [p57ProjW]; omega)
    (fun b ↦ by dsimp [axBAddW]; omega) (by dsimp [axLtW]; omega)).fwdBits γ₂
  have hcl₁ : cleanRem 437 (437 - 299) γ₁ :=
    cliff_cleanRem (by decide) hsP (cleanRem_anti (by decide) hβ)
  have hcl₂ : cleanRem 437 (437 - 308) γ₂ :=
    ctx_fwdBits_clean (by decide) hsLt (cleanRem_anti (by decide) hcl₁)
  obtain ⟨hdLtKeep, _⟩ := ctxLtCompLoop_props
    (mutW := fun q : Wire 437 ↦ q.val < 275 ∨ (291 ≤ q.val ∧ q.val < 299))
    8 299 (by decide) axAW axBW _ _ _
    (fun b h ↦ by dsimp [axAW] at h; omega) (fun b h ↦ by dsimp [axBW] at h; omega)
    (fun q hq h ↦ by omega)
  obtain ⟨_, hLtSpec⟩ := ctxLtCompLoop_scoped 8 299 (by decide) axAW axBW _ _ _
  obtain ⟨_, hAddSpec⟩ := ctxRippleAddCarry_scoped 8 308 (by decide) (p57ProjW w) axBAddW axLtW
    _ _ _ _ _ _
  obtain ⟨hVA, hVB, hVBA⟩ := hvalP β hβ
  have hLtVal : (γ₂ axLtW).val = if 255 - (if bitsVal (fun j ↦ β (p57ProjW w j)) < 128 then
      bitsVal (fun j ↦ β (p57ProjW w j)) + 128 else bitsVal (fun j ↦ β (p57ProjW w j)) - 128) <
      (if (β (p57S3W w)).val = 1 then 255 - bitsVal (fun j ↦ β (p57MW w j))
        else bitsVal (fun j ↦ β (p57MW w j))) then 1 else 0 := by
    have hiff := hLtSpec γ₁ hcl₁
    change (γ₂ axLtW = 1) ↔ _ at hiff
    rw [hVA, hVB] at hiff
    rcases zmod2_eq_zero_or_one (γ₂ axLtW) with hz | ho
    · rw [hz, s3IteNeg fun hc ↦ absurd (hiff.mpr hc) (by rw [hz]; decide)]
      rfl
    · rw [ho, s3ItePos (hiff.mp ho)]
      rfl
  have hSum8 : bitsVal (fun j : Fin 8 ↦ γ₃ (src8 j)) =
      axisFastVal ⟨bitsVal (fun j ↦ β (p57ProjW w j)), bitsVal_lt_two_pow _⟩
        (bitsVal (fun j ↦ β (p57MW w j))) (β (p57S3W w)).val := by
    have hmod := bitsVal_castSucc_mod
      (fun k : Fin 9 ↦ γ₃ (rippleAddCarryWires 8 308 (by decide) axLtW k))
    change bitsVal (fun j : Fin 8 ↦ γ₃ (src8 j)) = _ at hmod
    rw [hmod, (hAddSpec γ₂ hcl₂).2.2,
      show (fun j ↦ γ₂ (p57ProjW w j)) = fun j ↦ β (p57ProjW w j) from funext fun j ↦
        (ctx_fwdBits_pres hdLtKeep γ₁ (Or.inl (by dsimp [p57ProjW]; omega))).trans
          (hpresP β (p57ProjW w j) (by dsimp [p57ProjW]; omega)),
      show (fun j ↦ γ₂ (axBAddW j)) = fun j ↦ γ₁ (axBAddW j) from funext fun j ↦
        ctx_fwdBits_pres hdLtKeep γ₁
          (Or.inr ⟨by dsimp [axBAddW]; omega, by dsimp [axBAddW]; omega⟩), hVBA, hLtVal]
    rfl
  have hex : ∃ k : Fin 8, pBufW w b = pBufW w k := ⟨b, rfl⟩
  dsimp only [axisStep1_275]
  rw [hbits β hβ (pBufW w b), s3DitePos hex, hinjOut hex.choose_spec.symm,
    show (axCtx275 w).fwdBits β (src8 b) = γ₃ (src8 b) from by
      dsimp only [axCtx275]
      rw [StepBBlock0.TempCtx.append_fwdBits,
        StepBBlock0.TempCtx.append_fwdBits]
      rfl,
    congrFun (bitsVal_injective (hSum8.trans (bitsVal_eq_of_testBit (fun j ↦
      if (axisFastVal ⟨bitsVal (fun k ↦ β (p57ProjW w k)), bitsVal_lt_two_pow _⟩
        (bitsVal (fun k ↦ β (p57MW w k))) (β (p57S3W w)).val).testBit j.val then 1 else 0) _
      (axisFastVal_lt _ _ _) fun _ ↦ rfl).symm)) b]

/-- Stage 6 & 13: 3-axis stepped-projectile XOR `pBufW ⊕= axisFastVal` (`48` `tempAnd`s). -/
def axisStep3_275 : TempPhaseProg 437 :=
  .seq (axisStep1_275 0) (.seq (axisStep1_275 1) (axisStep1_275 2))

theorem axisStep3_275_spec : IsMutBlock 437 (437 - 275) (fun q ↦ ∃ w b, q = pBufW w b)
    axisStep3_275 ∧ axisStep3_275.countTempAnd = 48 ∧
    (∀ β, cleanRem 437 (437 - 275) β → ∀ (w : Fin 3) (b : Fin 8),
      axisStep3_275.evalBits β (pBufW w b) = β (pBufW w b) +
        if (axisFastVal ⟨bitsVal (fun j ↦ β (p57ProjW w j)), bitsVal_lt_two_pow _⟩
          (bitsVal (fun j ↦ β (p57MW w j))) (β (p57S3W w)).val).testBit b.val then 1 else 0) := by
  have h1 := axisStep1_275_spec
  have hWiden : ∀ u : Fin 3, IsMutBlock 437 (437 - 275) (fun q ↦ ∃ w b, q = pBufW w b)
      (axisStep1_275 u) := fun u ↦
    ⟨(h1 u).1.1, (h1 u).1.2.1, (h1 u).1.2.2.1,
      fun β hβ q hq ↦ (h1 u).1.2.2.2 β hβ q fun ⟨b, hb⟩ ↦ hq ⟨u, b, hb⟩⟩
  have hCnt : axisStep3_275.countTempAnd = 48 := by
    change (axisStep1_275 0).countTempAnd +
      ((axisStep1_275 1).countTempAnd + (axisStep1_275 2).countTempAnd) = 48
    rw [(h1 0).2.1, (h1 1).2.1, (h1 2).2.1]
  have hStepPres : ∀ (u : Fin 3) (γ : BitAssignment 437), cleanRem 437 (437 - 275) γ →
      let γ' := (axisStep1_275 u).evalBits γ
      cleanRem 437 (437 - 275) γ' ∧
        (∀ w b, w ≠ u → γ' (pBufW w b) = γ (pBufW w b)) ∧
        (∀ w, axisFastVal ⟨bitsVal (fun j ↦ γ' (p57ProjW w j)), bitsVal_lt_two_pow _⟩
            (bitsVal (fun j ↦ γ' (p57MW w j))) (γ' (p57S3W w)).val =
          axisFastVal ⟨bitsVal (fun j ↦ γ (p57ProjW w j)), bitsVal_lt_two_pow _⟩
            (bitsVal (fun j ↦ γ (p57MW w j))) (γ (p57S3W w)).val) := fun u γ hγ ↦ by
    have hnon := (h1 u).1.2.2.2 γ hγ
    have hOut : ∀ q : Wire 437, (q.val < 150 ∨ 174 ≤ q.val) →
        (axisStep1_275 u).evalBits γ q = γ q := fun q hq ↦
      hnon q fun ⟨k, hk⟩ ↦ by
        have hv := congrArg Fin.val hk
        dsimp [pBufW] at hv
        exact hq.elim (fun _ ↦ by omega) (fun _ ↦ by omega)
    refine ⟨(h1 u).1.2.2.1 γ hγ,
      fun w b hne ↦ hnon (pBufW w b) fun ⟨k, hk⟩ ↦ hne (Fin.ext (by
        have hv := congrArg Fin.val hk; dsimp [pBufW] at hv; omega)), fun w ↦ ?_⟩
    simp only [funext fun j ↦ hOut (p57ProjW w j) (Or.inl (by dsimp [p57ProjW]; omega)),
      funext fun j ↦ hOut (p57MW w j) (Or.inr (by dsimp [p57MW]; omega)),
      hOut (p57S3W w) (Or.inl (by dsimp [p57S3W]; omega))]
  refine ⟨StepBBlock0.IsMutBlock.seq (by decide) (hWiden 0)
    (StepBBlock0.IsMutBlock.seq (by decide) (hWiden 1) (hWiden 2)),
    hCnt, fun β hβ w b ↦ ?_⟩
  obtain ⟨hcl₁, hb₁, hv₁⟩ := hStepPres 0 β hβ
  obtain ⟨hcl₂, hb₂, hv₂⟩ := hStepPres 1 _ hcl₁
  obtain ⟨_, hb₃, _⟩ := hStepPres 2 _ hcl₂
  change (axisStep1_275 2).evalBits ((axisStep1_275 1).evalBits
    ((axisStep1_275 0).evalBits β)) (pBufW w b) = _
  rcases (by decide : ∀ u : Fin 3, u = 0 ∨ u = 1 ∨ u = 2) w with rfl | rfl | rfl
  · rw [hb₃ 0 b (by decide), hb₂ 0 b (by decide), (h1 0).2.2 β hβ b]
  · rw [hb₃ 1 b (by decide), (h1 1).2.2 _ hcl₁ b, hb₁ 1 b (by decide), hv₁ 1]
  · rw [(h1 2).2.2 _ hcl₂ b, hb₂ 2 b (by decide), hb₁ 2 b (by decide), hv₂ 2, hv₁ 2]

/-- Shifted 57-bit radial threshold table `cRad7Computable μ + 1 + boothConst57`. -/
def cRadBoothTable (t : Fin (2 ^ (2 + 1))) : ℕ :=
  if t.val < 7 then cRad7Computable t.val + 1 + boothConst57 else 0

theorem cRadBoothTable_lt (t : Fin (2 ^ (2 + 1))) : cRadBoothTable t < 2 ^ 57 := by
  dsimp [cRadBoothTable]
  by_cases ht : t.val < 7
  · rw [s3ItePos ht]
    have hb := (s3FineRad_54bit_bounds (u38 := 0) (sTrue := 0) (by decide) (by decide) ht).2.2
    have hc : boothConst57 < 2 ^ 56 := by decide
    omega
  · rw [s3IteNeg ht]
    positivity

/-- 57-bit radial threshold scratch wires `[283..340)` in `accXor275`. -/
def accThrW (j : Fin 57) : Wire 437 := ⟨283 + j.val, by omega⟩

/-- Pure-Clifford 57-bit constant table load onto `accThrW[0..n)` (`0` `tempAnd`s). -/
def accLoadThrCliff : (n : ℕ) → n ≤ 57 → CliffProg 437
  | 0, _ => .nil
  | n + 1, _ => .seq (accLoadThrCliff n (by omega))
      (accMaskCliff1 (accThrW ⟨n, by omega⟩) (by dsimp [accThrW]; omega)
        (fun a ↦ (cRadBoothTable ⟨a.val, by omega⟩).testBit n) 7 le_rfl)

private theorem accLoadThrCliff_props {mutW : Wire 437 → Prop}
    (hns : ∀ a, ¬ mutW (accSel7W a)) (hnt : ∀ q : Wire 437, 283 ≤ q.val → ¬ mutW q) :
    ∀ (n : ℕ) (hn : n ≤ 57),
      CliffDisjoint mutW (accLoadThrCliff n hn) ∧
        (accLoadThrCliff n hn).SupportsBelow 340 ∧
        (∀ (γ : BitAssignment 437) (q : Wire 437), ¬(283 ≤ q.val ∧ q.val < 283 + n) →
          (accLoadThrCliff n hn).eval γ q = γ q) ∧
        (∀ (γ : BitAssignment 437) (j : Fin 57), j.val < n →
          (accLoadThrCliff n hn).eval γ (accThrW j) = γ (accThrW j) + ∑ a : Fin 7,
            if (cRadBoothTable ⟨a.val, by omega⟩).testBit j.val then γ (accSel7W a) else 0)
  | 0, _ => ⟨trivial, trivial, fun _ _ _ ↦ rfl, fun _ _ hj ↦ absurd hj (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
      obtain ⟨hdP, hsP, hnonP, hevP⟩ := accLoadThrCliff_props hns hnt n (by omega)
      obtain ⟨hdM, hsM, hnonM, hevM⟩ := accMaskCliff1_props
        (accThrW ⟨n, by omega⟩) (by dsimp [accThrW]; omega)
        (fun a ↦ (cRadBoothTable ⟨a.val, by omega⟩).testBit n)
        hns (hnt _ (by dsimp [accThrW]; omega)) 7 le_rfl
      dsimp only [accLoadThrCliff]
      refine ⟨⟨hdP, hdM⟩, ⟨hsP, CliffProg.supportsBelow_mono (by dsimp [accThrW]; omega) hsM⟩,
        fun γ q hq ↦ (hnonM _ q fun he ↦ by subst he; dsimp [accThrW] at hq; omega).trans
          (hnonP γ q (by omega)), fun γ j hj ↦ ?_⟩
      by_cases hjn : j.val < n
      · exact (hnonM _ _ (wire_ne_of_lt (by change 283 + j.val < 283 + n; omega))).trans
          (hevP γ j hjn)
      · obtain rfl : j = ⟨n, Nat.lt_of_succ_le hn⟩ := Fin.ext (by dsimp; omega)
        change (accMaskCliff1 _ _ _ 7 _).eval ((accLoadThrCliff n _).eval γ) (accThrW ⟨n, _⟩) = _
        rw [hevM _, hnonP γ (accThrW ⟨n, _⟩) (by dsimp [accThrW]; omega)]
        refine congrArg (γ (accThrW ⟨n, _⟩) + ·) (Finset.sum_congr rfl fun a _ ↦ ?_)
        rw [hnonP γ (accSel7W a) (by
          have := Slot3MicroEngineAux.mu3Sel7Slots_bounds11 a
          dsimp [accSel7W]; omega)]

/-- 5-wire conjunction input `[validStatic, radOk, ne128_0, ne128_1, ne128_2]`. -/
def accAnd5InW : Fin 5 → Wire 437 :=
  ![validStaticW, ⟨397, by decide⟩, ⟨404, by decide⟩, ⟨411, by decide⟩, ⟨418, by decide⟩]

theorem accAnd5InW_inj : Function.Injective accAnd5InW := fun i j h ↦ by
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; revert h; decide)

/-- Single `TempCtx 437` computing full acceptance bit onto wire `422` in `88` `tempAnd`s
  (`[275..423)`). -/
def accXor275Ctx : TempCtx 437 :=
  let k1 := Slot3MicroEngineAux.ctxMicro muW muW_inj 275 8 6
    (fun i ↦ by dsimp [muW]; omega)
    Slot3MicroEngineAux.mu3OneHot7Ops Slot3MicroEngineAux.mu3OneHot7_meta3 (by decide)
  let k2 := ctxCliffAlloc (accLoadThrCliff 57 le_rfl)
  let k3 := Slot3MicroEngineAux.ctxLtCompLoop 57 340 (by decide) p57OutW accThrW
    (fun j ↦ wire_ne_of_lt (by dsimp [p57OutW, accThrW]; omega))
    (fun j ↦ by dsimp [p57OutW]; omega) (fun j ↦ by dsimp [accThrW]; omega)
  let k5 := Slot3MicroEngineAux.ctxMicro accAnd5InW accAnd5InW_inj 419 4 4
    (fun i ↦ by fin_cases i <;> decide)
    Slot3MicroEngineAux.and5Ops Slot3MicroEngineAux.and5_meta (by decide)
  k1.append (k2.append (k3.append ((ctxAccNe128Loop 3 le_rfl).append k5)))

/-- Stage 7 & 12: XOR full acceptance bit into `accWAux[149]` (`88` `tempAnd`s). -/
def accXor275 : TempPhaseProg 437 :=
  xorBlock1Prog accWAux ⟨422, by decide⟩ (by decide) (by decide) accXor275Ctx

theorem accXor275_spec : IsMutBlock 437 (437 - 275) accMutW accXor275 ∧
    accXor275.countTempAnd = 88 ∧
    (∀ β, cleanRem 437 (437 - 275) β → ∀ μ : ℕ, μ < 7 → bitsVal (fun i ↦ β (muW i)) = μ →
      accXor275.evalBits β accWAux = β accWAux + β validStaticW *
        (if bitsVal (fun j ↦ β (p57OutW j)) < cRad7Computable μ + 1 + boothConst57 then 1 else 0) *
        (if (∀ w : Fin 3, bitsVal (fun b ↦ β (p57ProjW w b)) ≠ 128) then 1 else 0)) := by
  let mut1 : Wire 437 → Prop := fun q ↦ ∃ _ : Fin 1, q = accWAux
  have hnot_ge150 : ∀ q : Wire 437, 150 ≤ q.val → ¬ mut1 q :=
    fun q hq ⟨_, h⟩ ↦ by subst h; dsimp [accWAux] at hq; omega
  have hnot_keep : ∀ (q : Wire 437), 201 ≤ q.val → q.val ≠ validStaticW.val →
      ¬(q.val < 201 ∨ q = validStaticW) :=
    fun _ hge hne h ↦ h.elim (fun _ ↦ by omega) (fun heq ↦ hne (congrArg Fin.val heq))
  let hin1 : ∀ i, (muW i).val < 275 := fun i ↦ by dsimp [muW]; omega
  let hin5 : ∀ i, (accAnd5InW i).val < 419 := fun i ↦ by fin_cases i <;> decide
  obtain ⟨hCnt1, hProps1, hLift1, hEval1⟩ := Slot3MicroEngineAux.ctxMicro_scoped muW muW_inj
    275 8 6 hin1 Slot3MicroEngineAux.mu3OneHot7Ops Slot3MicroEngineAux.mu3OneHot7_meta3 (by decide)
  obtain ⟨hdC, hsC, hnonC, hevC⟩ := accLoadThrCliff_props (mutW := mut1)
    (fun a ↦ hnot_ge150 (accSel7W a) (by dsimp [accSel7W]; omega))
    (fun q hq ↦ hnot_ge150 q (by omega)) 57 le_rfl
  have hLift2 : Slot3MicroEngineAux.TempCtxLiftEx 283 340
      (ctxCliffAlloc (accLoadThrCliff 57 le_rfl)) :=
    Slot3MicroEngineAux.TempCtxLiftEx.mono
      (Slot3MicroEngineAux.TempCtxLiftEx.cliff 340 (by decide) _ hsC) (by decide) le_rfl (by decide)
  have hneL3 : ∀ j, p57OutW j ≠ accThrW j :=
    fun j ↦ wire_ne_of_lt (by dsimp [p57OutW, accThrW]; omega)
  have haL3 : ∀ j, (p57OutW j).val < 340 := fun j ↦ by dsimp [p57OutW]; omega
  have hbL3 : ∀ j, (accThrW j).val < 340 := fun j ↦ by dsimp [accThrW]; omega
  have hCnt3 := Slot3MicroEngineAux.ctxLtCompLoop_countTempAnd (M := 437) 57 340 (by decide)
    p57OutW accThrW hneL3 haL3 hbL3
  obtain ⟨hd3, hs3⟩ := Slot3MicroEngineAux.ctxLtCompLoop_props (mutW := mut1) 57 340 (by decide)
    p57OutW accThrW hneL3 haL3 hbL3
    (fun j ↦ hnot_ge150 (p57OutW j) (by dsimp [p57OutW]; omega))
    (fun j ↦ hnot_ge150 (accThrW j) (by dsimp [accThrW]; omega))
    (fun q hq ↦ hnot_ge150 q (by omega))
  obtain ⟨hd3Keep, _⟩ := Slot3MicroEngineAux.ctxLtCompLoop_props
    (mutW := fun q : Wire 437 ↦ q.val < 201 ∨ q = validStaticW)
    57 340 (by decide) p57OutW accThrW hneL3 haL3 hbL3
    (fun j ↦ hnot_keep (p57OutW j) (by dsimp [p57OutW]; omega)
      (by dsimp [p57OutW, validStaticW]; omega))
    (fun j ↦ hnot_keep (accThrW j) (by dsimp [accThrW]; omega)
      (by dsimp [accThrW, validStaticW]; omega))
    (fun u hu ↦ hnot_keep u (by omega) (by dsimp [validStaticW]; omega))
  obtain ⟨hLift3, hEval3⟩ := Slot3MicroEngineAux.ctxLtCompLoop_scoped (M := 437) 57 340 (by decide)
    p57OutW accThrW hneL3 haL3 hbL3
  obtain ⟨hCnt4, hProps4, hLift4, hEval4⟩ := ctxAccNe128Loop_scoped 3 le_rfl
  obtain ⟨hCnt5, hProps5, hLift5, hEval5⟩ := Slot3MicroEngineAux.ctxMicro_scoped accAnd5InW
    accAnd5InW_inj 419 4 4 hin5 Slot3MicroEngineAux.and5Ops Slot3MicroEngineAux.and5_meta
      (by decide)
  obtain ⟨hd1, hs1⟩ := hProps1 (mutW := mut1)
    (fun i ↦ hnot_ge150 (muW i) (by dsimp [muW]; omega))
    (fun q hq ↦ hnot_ge150 q (by omega))
  obtain ⟨hd4, hs4⟩ := hProps4 (mutW := mut1)
    (fun w b ⟨_, h⟩ ↦ by have hv := congrArg Fin.val h; dsimp [p57ProjW, accWAux] at hv; omega)
    (fun q hq ↦ hnot_ge150 q (by omega))
  obtain ⟨hd5, hs5⟩ := hProps5 (mutW := mut1)
    (fun i ⟨_, h⟩ ↦ by revert h; fin_cases i <;> decide) (fun q hq ↦ hnot_ge150 q (by omega))
  obtain ⟨hB, hCnt, hEv⟩ := xorBlock1_275_spec (curEnd := 423) (by decide) (by decide)
    accWAux ⟨422, by decide⟩ (by decide) (by decide) accXor275Ctx
    (TempCtx.disjointFrom_append hd1 (TempCtx.disjointFrom_append (ctxCliffAlloc_disjoint hdC)
      (TempCtx.disjointFrom_append hd3 (TempCtx.disjointFrom_append hd4 hd5))))
    (TempCtx.supportsBelowCtx_append (by decide) hs1 (TempCtx.supportsBelowCtx_append (by decide)
      (ctxCliffAlloc_supports hsC) (TempCtx.supportsBelowCtx_append (by decide) hs3
        (TempCtx.supportsBelowCtx_append (by decide) hs4 hs5))))
    (Slot3MicroEngineAux.TempCtxLiftEx.append hLift1 (Slot3MicroEngineAux.TempCtxLiftEx.append
      hLift2
      (Slot3MicroEngineAux.TempCtxLiftEx.append hLift3
        (Slot3MicroEngineAux.TempCtxLiftEx.append hLift4 hLift5))))
  refine ⟨hB, hCnt.trans (by
    dsimp only [accXor275Ctx]
    repeat rw [Slot3MicroEngineAux.TempCtx.append_countTempAnd]
    rw [hCnt1, hCnt3, hCnt4, hCnt5]
    rfl), fun β hβ μ hμ7 hmuEq ↦ ?_⟩
  dsimp only [accXor275]
  rw [hEv β hβ]
  refine congrArg (β accWAux + ·) ?_
  obtain ⟨hcl1, hpres1, hsOut1⟩ := hEval1 β hβ
  have hchk1 := (Slot3MicroEngineAux.allBelow_iff 8 Slot3MicroEngineAux.mu3OneHot7Check).mp
    Slot3MicroEngineAux.mu3OneHot7_eval_ok _ (bitsVal_lt_two_pow (fun i ↦ β (muW i)))
  dsimp only [Slot3MicroEngineAux.mu3OneHot7Check] at hchk1
  simp only [Bool.and_eq_true] at hchk1
  set β₁ := (Slot3MicroEngineAux.ctxMicro muW muW_inj 275 8 6 hin1
    Slot3MicroEngineAux.mu3OneHot7Ops Slot3MicroEngineAux.mu3OneHot7_meta3 (by decide)).fwdBits β
  have hsel_β₁ : ∀ a : Fin 7, β₁ (accSel7W a) = if μ = a.val then 1 else 0 := fun a ↦ by
    have hb := Slot3MicroEngineAux.mu3Sel7Slots_bounds11 a
    have ha := (Slot3MicroEngineAux.allBelow_iff 7 _).mp hchk1.2 a.val a.isLt
    simp only [beq_iff_eq] at ha
    dsimp only [accSel7W]
    rw [hsOut1 _ hb.1 hb.2, ha, hmuEq]
    by_cases he : μ = a.val <;> simp [Slot3MicroEngineAux.boolToZMod2, he]
  have hcl1_340 : cleanRem 437 (437 - 340) β₁ := cleanRem_anti (by decide) hcl1
  have hfwd2 := Slot3MicroEngineAux.ctxCliffAlloc_fwdBits 340 (by decide)
    (accLoadThrCliff 57 le_rfl) hsC β₁ hcl1_340
  set β₂ := (accLoadThrCliff 57 le_rfl).eval β₁
  have hthr_val : bitsVal (fun j : Fin 57 ↦ β₂ (accThrW j)) =
      cRad7Computable μ + 1 + boothConst57 := by
    rw [show cRad7Computable μ + 1 + boothConst57 = cRadBoothTable ⟨μ, by omega⟩ from
      (s3ItePos hμ7).symm]
    refine bitsVal_eq_of_testBit _ _ (cRadBoothTable_lt ⟨μ, by omega⟩) fun j ↦ ?_
    dsimp only [β₂]
    rw [hevC β₁ j j.isLt, hcl1 (accThrW j) (by dsimp [accThrW]; omega), zero_add,
      Finset.sum_eq_single ⟨μ, hμ7⟩]
    · rw [hsel_β₁ ⟨μ, hμ7⟩, s3ItePos rfl]
    · intro a _ hne
      rw [hsel_β₁ a, s3IteNeg (show μ ≠ a.val from fun he ↦ hne (Fin.ext he.symm))]
      simp
    · exact fun habs ↦ absurd (Finset.mem_univ _) habs
  obtain ⟨hcl3, hlt_iff⟩ := hEval3 β₂ fun q hq ↦ (hnonC β₁ q (by omega)).trans (hcl1_340 q hq)
  let k3 := Slot3MicroEngineAux.ctxLtCompLoop 57 340 (by decide) p57OutW accThrW hneL3 haL3 hbL3
  set β₃ := k3.fwdBits β₂
  have hw397_β₃ : decide (β₃ ⟨397, by decide⟩ = 1) =
      decide (bitsVal (fun j ↦ β (p57OutW j)) < cRad7Computable μ + 1 + boothConst57) := by
    rw [show (fun j ↦ β₂ (p57OutW j)) = fun j ↦ β (p57OutW j) from funext fun j ↦
      (hnonC β₁ (p57OutW j) (by dsimp [p57OutW]; omega)).trans
        (hpres1 hchk1.1 (p57OutW j) (by dsimp [p57OutW]; omega)), hthr_val] at hlt_iff
    exact decide_eq_decide.mpr hlt_iff
  have hpres_k3 : ∀ q : Wire 437, q.val < 201 ∨ q = validStaticW → β₃ q = β q := fun q hq ↦
    have hlt275 : q.val < 275 :=
      hq.elim (fun _ ↦ by omega) (fun h ↦ h ▸ (by decide : validStaticW.val < 275))
    (Slot3MicroEngineAux.TempCtx.fwdBits_mut hd3Keep β₂ hq).trans
      ((hnonC β₁ q (by omega)).trans (hpres1 hchk1.1 q hlt275))
  obtain ⟨hcl4, hpres4, hout4⟩ := hEval4 β₃ hcl3
  set β₄ := (ctxAccNe128Loop 3 le_rfl).fwdBits β₃
  have hne128_β₄ : ∀ w : Fin 3, β₄ (accNe128OutW w) =
      Slot3MicroEngineAux.boolToZMod2 (decide (bitsVal (fun b ↦ β (p57ProjW w b)) ≠ 128)) := fun w ↦
        by
    rw [hout4 w w.isLt, show (fun b ↦ β₃ (p57ProjW w b)) = fun b ↦ β (p57ProjW w b) from
      funext fun b ↦ hpres_k3 (p57ProjW w b) (Or.inl (by dsimp [p57ProjW]; omega))]
  obtain ⟨_, _, hsOut5⟩ := hEval5 β₄ hcl4
  have hchk5 := (Slot3MicroEngineAux.allBelow_iff 32 Slot3MicroEngineAux.and5Check).mp
    Slot3MicroEngineAux.and5_eval_ok (bitsVal (fun i ↦ β₄ (accAnd5InW i)))
    (bitsVal_lt_two_pow (fun i ↦ β₄ (accAnd5InW i)))
  dsimp only [Slot3MicroEngineAux.and5Check] at hchk5
  simp only [Bool.and_eq_true, beq_iff_eq] at hchk5
  have hAllFwd : accXor275Ctx.fwdBits β =
      (Slot3MicroEngineAux.ctxMicro accAnd5InW accAnd5InW_inj 419 4 4 hin5
        Slot3MicroEngineAux.and5Ops Slot3MicroEngineAux.and5_meta (by decide)).fwdBits β₄ := by
    dsimp only [accXor275Ctx]
    repeat rw [Slot3MicroEngineAux.TempCtx.append_fwdBits]
    exact congrArg (fun x ↦ (Slot3MicroEngineAux.ctxMicro accAnd5InW accAnd5InW_inj 419 4 4 hin5
      Slot3MicroEngineAux.and5Ops Slot3MicroEngineAux.and5_meta (by decide)).fwdBits
      ((ctxAccNe128Loop 3 le_rfl).fwdBits (k3.fwdBits x))) hfwd2
  have ht := Slot3MicroEngineAux.bitsVal_testBit_eq (fun j ↦ β₄ (accAnd5InW j))
  rw [hAllFwd, show (⟨422, by decide⟩ : Wire 437) = ⟨419 + (8 - 5), by decide⟩ from rfl,
    hsOut5 8 (by decide) (by decide), hchk5.2,
    show (bitsVal (fun j ↦ β₄ (accAnd5InW j))).testBit 0 = _ from ht 0,
    show (bitsVal (fun j ↦ β₄ (accAnd5InW j))).testBit 1 = _ from ht 1,
    show (bitsVal (fun j ↦ β₄ (accAnd5InW j))).testBit 2 = _ from ht 2,
    show (bitsVal (fun j ↦ β₄ (accAnd5InW j))).testBit 3 = _ from ht 3,
    show (bitsVal (fun j ↦ β₄ (accAnd5InW j))).testBit 4 = _ from ht 4,
    show β₄ (accAnd5InW 0) = β validStaticW from
      (hpres4 validStaticW (by decide)).trans (hpres_k3 validStaticW (Or.inr rfl)),
    show decide (β₄ (accAnd5InW 1) = 1) = _ from
      (congrArg (fun x ↦ decide (x = 1)) (hpres4 ⟨397, by decide⟩ (by decide))).trans hw397_β₃,
    show accAnd5InW 2 = accNe128OutW 0 from rfl, show accAnd5InW 3 = accNe128OutW 1 from rfl,
    show accAnd5InW 4 = accNe128OutW 2 from rfl, hne128_β₄ 0, hne128_β₄ 1, hne128_β₄ 2]
  simp only [Slot3MicroEngineAux.boolToZMod2_decide_eq_one,
    show (∀ w : Fin 3, bitsVal (fun b ↦ β (p57ProjW w b)) ≠ 128) ↔
      (bitsVal (fun b ↦ β (p57ProjW 0 b)) ≠ 128 ∧ bitsVal (fun b ↦ β (p57ProjW 1 b)) ≠ 128 ∧
        bitsVal (fun b ↦ β (p57ProjW 2 b)) ≠ 128) from
      ⟨fun h ↦ ⟨h 0, h 1, h 2⟩, fun ⟨h0, h1, h2⟩ w ↦ by fin_cases w <;> assumption⟩]
  exact accBool5_eq _ _ _ _ _

attribute [local irreducible]
  sTrue18FwdPBuf275 sTrue18RevPBuf275 boothAdd57_275 boothSub57_275 axisStep3_275 accXor275
set_option backward.isDefEq.respectTransparency true
end
end ConfigStepBOuter
end StepBOuter

namespace OraAndPrepBundle
open Operator NuclearTwistRealizes

theorem castNatUnitary_symm_cancel {a b : ℕ} (h : a = b) (U : Unitary (2 ^ a)) :
    castNatUnitary h.symm (castNatUnitary h U) = U := by
  subst h
  rfl
end OraAndPrepBundle

end QuantumComputation.Specs.StoppingPowerSolution
