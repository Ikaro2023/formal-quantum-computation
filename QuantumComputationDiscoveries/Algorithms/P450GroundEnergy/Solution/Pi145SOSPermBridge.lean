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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.QuantizedFactoredMag30

@[expose] public section

/-!
# Permuted-Two-Body `P_τ`-Absorption SOS Operator Bridge & `π145` Instantiation

Proves the symbolic `(σ, π128)` `P_τ`-absorption operator bridge on `ubDirectXo7PureUnitary`
without re-proving the P450 DFTHC sum-of-squares algebra, and instantiates it on the concrete
`wOuter = 8` drop-4 `π145` outer permutation (`pi145Perm184`, `pi145XoEquiv`, `pi128Equiv`).

## References
- D. W. Berry, C. Gidney, M. Motta, J. R. McClean, and R. Babbush, *Quantum* **3**, 208 (2019),
  DOI: `10.22331/q-2019-12-02-208` ("Qubitization of Arbitrary Basis Quantum Chemistry
  Leveraging Sparsity and Low Rank Factorization").
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  *Phys. Rev. X* **8**, 041015 (2018), DOI: `10.1103/PhysRevX.8.041015` ("Encoding Electronic
  Spectra in Quantum Circuits with Linear T Complexity").
- J. Lee, D. W. Berry, C. Gidney, W. J. Huggins, J. R. McClean, N. Wiebe, and R. Babbush,
  *PRX Quantum* **2**, 030305 (2021), DOI: `10.1103/PRXQuantum.2.030305` ("Even More Efficient
  Quantum Computations of Chemistry Through Tensor Hypercontraction").
-/

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Pi145SOSPermBridge
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real QuantumComputation.Specs
open QuantumComputation.Specs.P450 CoherentAlias CleanDyn
open BlockEncodingCore BlockEncodingCircuit
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TopIntegrationBridge
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.ZeroRcHotPrepMid21Fast
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.ReordOuter13Bridge
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.MobiusOptSubcube163Walk
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactTuned162StepWalk
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.QuantizedFactoredMag30
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

local instance (priority := 1000000) instNeZeroTwoPowPi145 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

/-! ## Section 1: Concrete `π145` Outer & `7`-Bit Fragment Permutations -/

/-- Forward `ℕ` lookup for `pi128Equiv` (`0..125`, identity on `≥ 126`). -/
def pi128FwdNat (k : ℕ) : ℕ :=
  if k < 126 then
    let w := if k < 64 then
        if k < 32 then 0x7277121514131a181617111b190e100f767d0002090301070b0c0d05060a0804
        else 0x7475352b2f30322e33342a2d36312c37707c1d1c1e292228272623201f252421
      else if k < 96 then 0x787a46534849514b4f4a504e4d52474c7b7143413e40423f443b393c45383d3a
        else 0x64626c6d6566636f6b68696e6a6779735f555b54615c595d5756605a5e58
    (w >>> (8 * (k % 32))) % 256
  else k

/-- Inverse `ℕ` lookup for `pi128Equiv` (`0..125`, identity on `≥ 126`). -/
def pi128InvNat (k : ℕ) : ℕ :=
  if k < 126 then
    let w := if k < 64 then
        if k < 32 then 0x232b2d2c1419131816171c1b1a1d15111012050607020b01080304000a0c090d
        else 0x484b41444640454230333d363739323a3b3834313c352a282726222125292024
      else if k < 96 then 0x6d6166686b62676065646c6a5c5259555754535058565a5b515d43474d494c4a
        else 0xe2e4f5e6f5f1e0f3e3f6e1f4e2f76727a7b757173747078797d777c6963
    (w >>> (8 * (k % 32))) % 256
  else k

/-- Forward one-body orbital lookup `k ↦ (pi145Perm184 (126 + k)).val` (`k ∈ 0..57`). -/
def pi145OneBodyAt (k : ℕ) : ℕ :=
  if k < 58 then
    let w := if k < 32 then 0x1806082902071c2e2c010c302a15250f240d1120191d21090a1b16101e0e3704
      else 0xb2f1228270536031300381f261a14223531233933342b17322d
    (w >>> (8 * (k % 32))) % 256
  else 0

/-- Inverse one-body offset `j ↦ (pi145Perm184.symm j).val - 126` (`j ∈ 0..57`). -/
def pi145InvOneBodyAt (k : ℕ) : ℕ :=
  if k < 58 then
    let w := if k < 32 then 0x2e030a19062c0b1f2205122b31370d0410020e153907081d1a1e3400321b1630
      else 0x262f01332924252128143818201723131c36352d110f272a090c
    (w >>> (8 * (k % 32))) % 256
  else 0

/-- Forward `ℕ` map underlying `pi145Perm184` (`k < 126 ↦ 58 + pi128FwdNat k`). -/
def pi145ToFunNat (k : ℕ) : ℕ :=
  if k < 126 then 58 + pi128FwdNat k else pi145OneBodyAt (k - 126)

/-- Inverse `ℕ` map underlying `pi145Perm184` (`58 ≤ k ↦ pi128InvNat (k - 58)`). -/
def pi145InvFunNat (k : ℕ) : ℕ :=
  if k < 58 then 126 + pi145InvOneBodyAt k else pi128InvNat (k - 58)

theorem pi128_ok :
    BlockEncodingCircuit.allPow2 7 0 (fun x ↦
      decide (pi128FwdNat x < 2 ^ 7 ∧ pi128InvNat x < 2 ^ 7 ∧
        pi128InvNat (pi128FwdNat x) = x ∧ pi128FwdNat (pi128InvNat x) = x)) = true := by decide

theorem pi128_spec (x : ℕ) (hx : x < 2 ^ 7) :
    pi128FwdNat x < 2 ^ 7 ∧ pi128InvNat x < 2 ^ 7 ∧
      pi128InvNat (pi128FwdNat x) = x ∧ pi128FwdNat (pi128InvNat x) = x :=
  of_decide_eq_true (BlockEncodingCircuit.allPow2_zero_true pi128_ok x hx)

/-- `7`-bit fragment permutation `π128 : Equiv.Perm (Fin (2 ^ 7))` for `π145`, fixing `126, 127`. -/
def pi128Equiv : Equiv.Perm (Fin (2 ^ 7)) where
  toFun k := ⟨pi128FwdNat k.val, (pi128_spec k.val k.isLt).1⟩
  invFun k := ⟨pi128InvNat k.val, (pi128_spec k.val k.isLt).2.1⟩
  left_inv k := Fin.ext (pi128_spec k.val k.isLt).2.2.1
  right_inv k := Fin.ext (pi128_spec k.val k.isLt).2.2.2

theorem pi145_ok :
    BlockEncodingCircuit.allPow2 8 0 (fun x ↦
      decide (x < 184 → pi145ToFunNat x < 184 ∧ pi145InvFunNat x < 184 ∧
        pi145InvFunNat (pi145ToFunNat x) = x ∧ pi145ToFunNat (pi145InvFunNat x) = x ∧
        (126 ≤ x → pi145ToFunNat x < 58))) = true := by decide

theorem pi145_spec (x : ℕ) (hx : x < 184) :
    pi145ToFunNat x < 184 ∧ pi145InvFunNat x < 184 ∧
      pi145InvFunNat (pi145ToFunNat x) = x ∧ pi145ToFunNat (pi145InvFunNat x) = x ∧
      (126 ≤ x → pi145ToFunNat x < 58) :=
  (of_decide_eq_true (BlockEncodingCircuit.allPow2_zero_true pi145_ok x (by omega))) hx

/-- Concrete `wOuter = 8` drop-4 `π145` outer permutation of `Fin 184`. -/
def pi145Perm184 : Equiv.Perm (Fin 184) where
  toFun k := ⟨pi145ToFunNat k.val, (pi145_spec k.val k.isLt).1⟩
  invFun k := ⟨pi145InvFunNat k.val, (pi145_spec k.val k.isLt).2.1⟩
  left_inv k := Fin.ext (pi145_spec k.val k.isLt).2.2.1
  right_inv k := Fin.ext (pi145_spec k.val k.isLt).2.2.2.1

/-- `256`-slot extension of `pi145Perm184` fixing padding indices `184..255`. -/
abbrev pi145XoEquiv : Equiv.Perm (Fin (2 ^ 8)) :=
  ReordOuter13Bridge.extPerm256 pi145Perm184

theorem pi128Equiv_hfix126 :
    pi128Equiv ⟨126, by decide⟩ = ⟨126, by decide⟩ ∧
      pi128Equiv ⟨127, by decide⟩ = ⟨127, by decide⟩ := ⟨Fin.ext rfl, Fin.ext rfl⟩

theorem pi145XoEquiv_hpi (x : Fin (2 ^ 8)) (hx : x.val < 126) :
    (pi145XoEquiv x).val = 58 + (pi128Equiv ⟨x.val, by omega⟩).val := by
  rw [extPerm256_lt pi145Perm184 x (by omega)]
  change pi145ToFunNat x.val = 58 + pi128FwdNat x.val; exact ite_eq_left hx

theorem pi145XoEquiv_h1B (x : Fin (2 ^ 8)) (h126 : 126 ≤ x.val) (h184 : x.val < 184) :
    (pi145XoEquiv x).val < 58 := by
  rw [extPerm256_lt pi145Perm184 x h184]; exact (pi145_spec x.val h184).2.2.2.2 h126

theorem pi145XoEquiv_hpad (x : Fin (2 ^ 8)) (h184 : 184 ≤ x.val) :
    pi145XoEquiv x = x := extPerm256_ge pi145Perm184 x h184

/-! ## Section 2: `tauPerm256`, `IsZeroRcOuterPerm` & `PrepOut` Permutation Transport -/

/-- Extends `π128 : Equiv.Perm (Fin (2 ^ 7))` to `Fin (2 ^ 8)` on `< 128`, fixing `128..255`. -/
def tauPerm256 (π128 : Equiv.Perm (Fin (2 ^ 7))) : Equiv.Perm (Fin (2 ^ 8)) where
  toFun x := if h : x.val < 2 ^ 7 then ⟨(π128 ⟨x.val, h⟩).val, by omega⟩ else x
  invFun x := if h : x.val < 2 ^ 7 then ⟨(π128.symm ⟨x.val, h⟩).val, by omega⟩ else x
  left_inv x := by
    dsimp only; by_cases h : x.val < 2 ^ 7
    · rw [dite_eq_left h, dite_eq_left (π128 ⟨x.val, h⟩).isLt]; simp
    · rw [dite_eq_right h, dite_eq_right h]
  right_inv x := by
    dsimp only; by_cases h : x.val < 2 ^ 7
    · rw [dite_eq_left h, dite_eq_left (π128.symm ⟨x.val, h⟩).isLt]; simp
    · rw [dite_eq_right h, dite_eq_right h]

theorem tauPerm256_lt128 (π128 : Equiv.Perm (Fin (2 ^ 7))) (x : Fin (2 ^ 8)) (h : x.val < 2 ^ 7) :
    (tauPerm256 π128 x).val = (π128 ⟨x.val, h⟩).val := by
  dsimp only [tauPerm256, Equiv.coe_fn_mk]; rw [dite_eq_left h]

theorem tauPerm256_ge128 (π128 : Equiv.Perm (Fin (2 ^ 7))) (x : Fin (2 ^ 8)) (h : 128 ≤ x.val) :
    tauPerm256 π128 x = x := by
  have hn : ¬ x.val < 2 ^ 7 := by omega
  dsimp only [tauPerm256, Equiv.coe_fn_mk]; exact dite_eq_right hn

@[simp] theorem tauPerm256_inv_eq (π128 : Equiv.Perm (Fin (2 ^ 7))) :
    (tauPerm256 π128)⁻¹ = tauPerm256 π128.symm := by ext x; rfl

theorem tauPerm256_of_ge126 {π128 : Equiv.Perm (Fin (2 ^ 7))}
    (hfix126 : π128 ⟨126, by decide⟩ = ⟨126, by decide⟩ ∧
      π128 ⟨127, by decide⟩ = ⟨127, by decide⟩)
    (x : Fin (2 ^ 8)) (hx : 126 ≤ x.val) : tauPerm256 π128 x = x := by
  by_cases h126 : x.val = 126
  · apply Fin.ext; rw [tauPerm256_lt128 π128 x (by omega),
      show (⟨x.val, _⟩ : Fin (2 ^ 7)) = ⟨126, by decide⟩ from Fin.ext h126, hfix126.1]
    exact h126.symm
  · by_cases h127 : x.val = 127
    · apply Fin.ext; rw [tauPerm256_lt128 π128 x (by omega),
        show (⟨x.val, _⟩ : Fin (2 ^ 7)) = ⟨127, by decide⟩ from Fin.ext h127, hfix126.2]
      exact h127.symm
    · exact tauPerm256_ge128 π128 x (by omega)

theorem tauPerm256_inv_of_ge126 {π128 : Equiv.Perm (Fin (2 ^ 7))}
    (hfix126 : π128 ⟨126, by decide⟩ = ⟨126, by decide⟩ ∧
      π128 ⟨127, by decide⟩ = ⟨127, by decide⟩)
    (x : Fin (2 ^ 8)) (hx : 126 ≤ x.val) : (tauPerm256 π128)⁻¹ x = x := by
  rw [tauPerm256_inv_eq]; exact tauPerm256_of_ge126
    ⟨π128.symm_apply_eq.mpr hfix126.1.symm, π128.symm_apply_eq.mpr hfix126.2.symm⟩ x hx

/-- `(a)` Absorbing `(tauPerm256 π128)⁻¹` on the right converts `σ` into `IsZeroRcOuterPerm`. -/
theorem isZeroRcOuterPerm_comp_tau_symm {σ : Equiv.Perm (Fin (2 ^ 8))}
    {π128 : Equiv.Perm (Fin (2 ^ 7))}
    (hπ : ∀ (x : Fin (2 ^ 8)) (hx : x.val < 126), (σ x).val = 58 + (π128 ⟨x.val, by omega⟩).val)
    (hfix126 : π128 ⟨126, by decide⟩ = ⟨126, by decide⟩ ∧
      π128 ⟨127, by decide⟩ = ⟨127, by decide⟩)
    (h1B : ∀ x : Fin (2 ^ 8), 126 ≤ x.val → x.val < 184 → (σ x).val < 58)
    (hpad : ∀ x : Fin (2 ^ 8), 184 ≤ x.val → σ x = x) :
    IsZeroRcOuterPerm (σ * (tauPerm256 π128)⁻¹) := by
  have hlt126 (xo' : Fin (2 ^ 8)) (h : xo'.val < 126) :
      ((σ * (tauPerm256 π128)⁻¹) xo').val = xo'.val + 58 := by
    let y := (tauPerm256 π128)⁻¹ xo'
    have hy : y.val < 126 := by
      by_contra hge; have hfix := tauPerm256_of_ge126 hfix126 y (by omega)
      have happ : tauPerm256 π128 y = xo' := (tauPerm256 π128).apply_symm_apply xo'
      rw [hfix] at happ; rw [happ] at hge; omega
    have hy_eq : (⟨y.val, by omega⟩ : Fin (2 ^ 7)) = π128.symm ⟨xo'.val, by omega⟩ := by
      apply Fin.ext; dsimp only [y]
      rw [tauPerm256_inv_eq, tauPerm256_lt128 π128.symm xo' (by omega)]
    rw [Equiv.Perm.mul_apply, hπ y hy, hy_eq, π128.apply_symm_apply]; dsimp; omega
  refine ⟨hlt126, fun xo' h ↦ ?_, fun xo' ↦ ?_⟩
  · rw [Equiv.Perm.mul_apply, tauPerm256_inv_of_ge126 hfix126 xo' h]
    by_cases h184 : xo'.val < 184
    · exact Or.inl (h1B xo' h h184)
    · rw [hpad xo' (by omega)]; exact Or.inr (by omega)
  · by_cases h126 : xo'.val < 126
    · rw [hlt126 xo' h126]; omega
    · rw [Equiv.Perm.mul_apply, tauPerm256_inv_of_ge126 hfix126 xo' (by omega)]
      by_cases h184 : xo'.val < 184
      · have := h1B xo' (by omega) h184; omega
      · rw [hpad xo' (by omega)]

/-- Embedding `Operator.permutationUnitary ρ` on `rXoLoc wOuter` equals
`Operator.permutationUnitary (outPermEquiv ρ wOuter)`. -/
theorem embedUnitary_rXoLoc_permutationUnitary (ρ : Equiv.Perm (Fin (2 ^ 8))) (wOuter : ℕ) :
    (rXoLoc wOuter).embedUnitary (Operator.permutationUnitary ρ) =
      Operator.permutationUnitary (outPermEquiv ρ wOuter) := by
  apply Subtype.ext; ext i j
  have h : ((rXoLoc wOuter).embedUnitary (Operator.permutationUnitary ρ)).1 *ᵥ Pi.single j 1 =
      (Operator.permutationUnitary (outPermEquiv ρ wOuter)).1 *ᵥ Pi.single j 1 := by
    rw [QRegister.embedUnitary_val, (rXoLoc wOuter).embedMatrix_mulVec_single_factors,
      Operator.permutationUnitary_mulVec_single, (rXoLoc wOuter).tensorState_single_replaceIndex,
      Operator.permutationUnitary_mulVec_single]
    rfl
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun h i

theorem mul_embedUnitary_rXoLoc_permutationUnitary_apply (ρ : Equiv.Perm (Fin (2 ^ 8))) {wOuter : ℕ}
    (u : Unitary (2 ^ mOutUB wOuter)) (o k : Fin (2 ^ mOutUB wOuter)) :
    (((rXoLoc wOuter).embedUnitary (Operator.permutationUnitary ρ)) * u).1 o k =
      u.1 ((outPermEquiv ρ wOuter).symm o) k := by
  rw [embedUnitary_rXoLoc_permutationUnitary]; exact toOrigPrepOutOf_apply ρ u o k

theorem extract_rXoLoc_outPermEquiv_symm (ρ : Equiv.Perm (Fin (2 ^ 8))) {wOuter : ℕ}
    (o : Fin (2 ^ mOutUB wOuter)) :
    (rXoLoc wOuter).extractIndex ((outPermEquiv ρ wOuter).symm o) =
      ρ.symm ((rXoLoc wOuter).extractIndex o) :=
  ρ.injective (by
    rw [← extract_rXoLoc_outPermEquiv, Equiv.apply_symm_apply, Equiv.apply_symm_apply])

theorem mul_embedUnitary_rXoLoc_perm_vanish_ge184 {ρ : Equiv.Perm (Fin (2 ^ 8))}
    (hρ_pad : ∀ x : Fin (2 ^ 8), 184 ≤ x.val → ρ x = x) {wOuter : ℕ}
    {u : Unitary (2 ^ mOutUB wOuter)}
    (hu0 : ∀ o' : Fin (2 ^ mOutUB wOuter), 184 ≤ ((rXoLoc wOuter).extractIndex o').val → u.1 o' 0 =
      0)
    (o' : Fin (2 ^ mOutUB wOuter)) (hge : 184 ≤ ((rXoLoc wOuter).extractIndex o').val) :
    (((rXoLoc wOuter).embedUnitary (Operator.permutationUnitary ρ)) * u).1 o' 0 = 0 := by
  rw [mul_embedUnitary_rXoLoc_permutationUnitary_apply]
  have hsymm : ρ.symm ((rXoLoc wOuter).extractIndex o') = (rXoLoc wOuter).extractIndex o' :=
    ρ.injective ((ρ.apply_symm_apply _).trans (hρ_pad _ hge).symm)
  exact hu0 _ (by rw [extract_rXoLoc_outPermEquiv_symm, hsymm]; exact hge)

/-- `(b)` Left-multiplying `prepOutIdeal` by `(rXoLoc wOuter).embedUnitary (permutationUnitary ρ)`
transports `PrepOutQuantPerm256 σ qOut` to `PrepOutQuantPerm256 (σ * ρ⁻¹) qOut`. -/
theorem prepOutQuantPerm256_mul_perm {σ ρ : Equiv.Perm (Fin (2 ^ 8))}
    (hρ_pad : ∀ x : Fin (2 ^ 8), 184 ≤ x.val → ρ x = x) {qOut : Fin 184 → ℝ} {wOuter : ℕ}
    {prepOutIdeal : Unitary (2 ^ mOutUB wOuter)} (hOut : PrepOutQuantPerm256 σ qOut prepOutIdeal) :
    PrepOutQuantPerm256 (σ * ρ⁻¹) qOut
      ((rXoLoc wOuter).embedUnitary (Operator.permutationUnitary ρ) * prepOutIdeal) := by
  refine ⟨mul_embedUnitary_rXoLoc_perm_vanish_ge184 hρ_pad hOut.1, fun xo' so ↦ ?_⟩
  let x8 : Fin (2 ^ 8) := ⟨xo'.val, by omega⟩
  have hy_lt : (ρ.symm x8).val < 184 := by
    by_contra hge; have hfix := congrArg Fin.val (hρ_pad (ρ.symm x8) (by omega))
    rw [ρ.apply_symm_apply] at hfix; have := xo'.isLt; change xo'.val = (ρ.symm x8).val at hfix
    omega
  let y : Fin 184 := ⟨(ρ.symm x8).val, hy_lt⟩
  have hbij :
      (∑ o' ∈ Finset.univ.filter (fun o' : Fin (2 ^ mOutUB wOuter) ↦
          ((rXoLoc wOuter).extractIndex o').val = xo'.val ∧ (rSigOutLoc wOuter).extractIndex o' =
            so),
        Complex.normSq
          ((((rXoLoc wOuter).embedUnitary (Operator.permutationUnitary ρ)) * prepOutIdeal).1 o' 0))
            =
      ∑ o'' ∈ Finset.univ.filter (fun o'' : Fin (2 ^ mOutUB wOuter) ↦
          ((rXoLoc wOuter).extractIndex o'').val = y.val ∧ (rSigOutLoc wOuter).extractIndex o'' =
            so),
        Complex.normSq (prepOutIdeal.1 o'' 0) := by
    refine Finset.sum_bij (fun o' _ ↦ (outPermEquiv ρ wOuter).symm o')
      (fun o' ho' ↦ ?_) (fun _ _ _ _ h ↦ (outPermEquiv ρ wOuter).symm.injective h)
      (fun o'' ho'' ↦ ⟨outPermEquiv ρ wOuter o'', ?_, (outPermEquiv ρ wOuter).symm_apply_apply o''⟩)
      (fun o' _ ↦ by rw [mul_embedUnitary_rXoLoc_permutationUnitary_apply])
    · rcases (Finset.mem_filter.mp ho').2 with ⟨hxo, hso⟩
      have hx8 : (rXoLoc wOuter).extractIndex o' = x8 := Fin.ext hxo
      have hs := extract_rSigOutLoc_outPermEquiv ρ ((outPermEquiv ρ wOuter).symm o')
      rw [Equiv.apply_symm_apply] at hs
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        by rw [extract_rXoLoc_outPermEquiv_symm, hx8], hs.symm.trans hso⟩
    · rcases (Finset.mem_filter.mp ho'').2 with ⟨hyo, hso⟩
      have hy8 : (rXoLoc wOuter).extractIndex o'' = ρ.symm x8 := Fin.ext hyo
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        by rw [extract_rXoLoc_outPermEquiv, hy8, ρ.apply_symm_apply],
        by rw [extract_rSigOutLoc_outPermEquiv, hso]⟩
  have hσy : σ ⟨y.val, by omega⟩ = (σ * ρ⁻¹) ⟨xo'.val, by omega⟩ := congrArg σ (Fin.ext rfl)
  rw [hbij, hOut.2 y so, hσy]

theorem prepOutQuantPerm256_mul_tauPerm256 {σ : Equiv.Perm (Fin (2 ^ 8))}
    (π128 : Equiv.Perm (Fin (2 ^ 7))) {qOut : Fin 184 → ℝ} {wOuter : ℕ}
    {prepOutIdeal : Unitary (2 ^ mOutUB wOuter)} (hOut : PrepOutQuantPerm256 σ qOut prepOutIdeal) :
    PrepOutQuantPerm256 (σ * (tauPerm256 π128)⁻¹) qOut
      ((rXoLoc wOuter).embedUnitary (Operator.permutationUnitary (tauPerm256 π128)) * prepOutIdeal)
        :=
  prepOutQuantPerm256_mul_perm (fun x _ ↦ tauPerm256_ge128 π128 x (by omega)) hOut

/-- Permuted symmetric reference `SELECT` unitary (`rfl`-equal to `SFAsymTwoPassWalkSplicer`). -/
noncomputable abbrev balRefSelectPureUnitary (σ : Equiv.Perm (Fin (2 ^ 8))) (wOuter wInner2 : ℕ) :
    Unitary (2 ^ nUB wOuter wInner2) :=
  muxUnitary (rAllUB wOuter wInner2) (rSysUB wOuter wInner2) (disjoint_rAllUB_rSysUB wOuter wInner2)
    (fun a ↦ let ⟨xo', so, b, si⟩ := decodeSelectCtrl a; selectBranchUnitary (σ xo') so b si)

/-- Spin-`1 / 2` marginal condition on all `128` `rc` slices (`rfl`-equal to `PrepMidHalfSpin`). -/
abbrev PrepMidHalfSpin {wInner2 : ℕ} (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2))
    : Prop :=
  ∀ (rc : Fin (2 ^ 7)) (si : Fin 2),
    (∑ m ∈ Finset.univ.filter (fun m : Fin (2 ^ mMidUB wInner2) ↦ (rSigInLoc wInner2).extractIndex m
      = si),
      Complex.normSq ((prepMid rc).1 m 0)) = 1 / 2

/-- Active-support branch action for `selectPure` under `(σ, M)` (`xo' < 184`). -/
abbrev SelectActiveOn (σ : Equiv.Perm (Fin (2 ^ 8))) {wOuter wInner2 : ℕ}
    (M : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2))
    (selectPure : Unitary (2 ^ nUB wOuter wInner2)) : Prop :=
  ∀ (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter)) (m : Fin (2 ^ mMidUB wInner2)),
    ((rXoLoc wOuter).extractIndex o').val < 184 → (M ((rXo7Loc wOuter).extractIndex o')).1 m 0 ≠ 0 →
    selectPure.1 *ᵥ embedKet ψ o' m =
      embedKet ((selectBranchUnitary (σ ((rXoLoc wOuter).extractIndex o'))
        ((rSigOutLoc wOuter).extractIndex o')
        ((rBLoc wInner2).extractIndex m) ((rSigInLoc wInner2).extractIndex m)).1 *ᵥ ψ) o' m

/-- `< 184`-support branch action for `selectPure` under `σ` (independent of `M`, e.g. `1` on
`184 ≤ xo'`). Implies `SelectActiveOn σ M selectPure` for any `M`. -/
abbrev SelectOnLt184 (σ : Equiv.Perm (Fin (2 ^ 8))) {wOuter wInner2 : ℕ}
    (selectPure : Unitary (2 ^ nUB wOuter wInner2)) : Prop :=
  ∀ (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter)) (m : Fin (2 ^ mMidUB wInner2)),
    ((rXoLoc wOuter).extractIndex o').val < 184 →
    selectPure.1 *ᵥ embedKet ψ o' m =
      embedKet ((selectBranchUnitary (σ ((rXoLoc wOuter).extractIndex o'))
        ((rSigOutLoc wOuter).extractIndex o')
        ((rBLoc wInner2).extractIndex m) ((rSigInLoc wInner2).extractIndex m)).1 *ᵥ ψ) o' m

theorem balRefSelectPureUnitary_mulVec_embedKet (σ : Equiv.Perm (Fin (2 ^ 8))) {wOuter wInner2 : ℕ}
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter)) (m : Fin (2 ^ mMidUB wInner2)) :
    (balRefSelectPureUnitary σ wOuter wInner2).1 *ᵥ embedKet ψ o' m =
      embedKet ((selectBranchUnitary (σ ((rXoLoc wOuter).extractIndex o'))
        ((rSigOutLoc wOuter).extractIndex o')
        ((rBLoc wInner2).extractIndex m) ((rSigInLoc wInner2).extractIndex m)).1 *ᵥ ψ) o' m := by
  let a₀ : Fin (2 ^ mAncUB wOuter wInner2) :=
      (splitBlockEquiv (mOutUB wOuter) (mMidUB wInner2)).symm (o', m)
  have ha₀ (g : Fin (2 ^ nUB wOuter wInner2)) (h : (rAllUB wOuter wInner2).extractIndex g ≠ a₀) :
      embedKet ψ o' m g = 0 := by
    dsimp [embedKet]; by_contra hnz
    have hc : (rOutUB wOuter wInner2).extractIndex g = o' ∧ (rMidUB wOuter wInner2).extractIndex g =
        m := by
      by_contra hc; simp [hc] at hnz
    apply h; apply (splitBlockEquiv (mOutUB wOuter) (mMidUB wInner2)).injective
    rw [Equiv.apply_symm_apply]; apply Prod.ext
    · rw [splitBlockEquiv_fst, ← QRegister.extractIndex_compose,
        show (rAllUB wOuter wInner2).compose
          (QRegister.block 0 (mOutUB wOuter) (by dsimp [mAncUB]; omega)) =
          rOutUB wOuter wInner2 by ext i; simp [rAllUB, rOutUB], hc.1]
    · rw [splitBlockEquiv_snd, ← QRegister.extractIndex_compose,
        show (rAllUB wOuter wInner2).compose
          (QRegister.block (mOutUB wOuter) (mMidUB wInner2) (by dsimp [mAncUB]; omega)) =
          rMidUB wOuter wInner2 by ext j; simp [rAllUB, rMidUB]; omega, hc.2]
  unfold balRefSelectPureUnitary
  rw [muxUnitary_mulVec_of_proj _ _ _ _ a₀ _ ha₀, embedMatrix_rSysUB_mulVec_embedKet,
    show decodeSelectCtrl a₀ =
      ((rXoLoc wOuter).extractIndex o', (rSigOutLoc wOuter).extractIndex o',
       (rBLoc wInner2).extractIndex m, (rSigInLoc wInner2).extractIndex m) by simp
         [decodeSelectCtrl, a₀]]

theorem extract_rXo7Loc_of_lt128 {wOuter : ℕ} (o' : Fin (2 ^ mOutUB wOuter))
    (h128 : ((rXoLoc wOuter).extractIndex o').val < 2 ^ 7) :
    (rXo7Loc wOuter).extractIndex o' = ⟨((rXoLoc wOuter).extractIndex o').val, h128⟩ := by
  rw [show rXo7Loc wOuter = (rXoLoc wOuter).compose (QRegister.block 0 7 (by decide)) from rfl,
    QRegister.extractIndex_compose]
  apply (basisBits 7).injective; funext i
  rw [QRegister.basisBits_extractIndex, basisBits_eq_testBit, basisBits_eq_testBit]
  simp only [QRegister.block_apply_val, Nat.zero_add]

theorem embedUnitary_rOutUB_perm_mulVec_embedKet (ρ : Equiv.Perm (Fin (2 ^ 8))) {wOuter wInner2 : ℕ}
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter)) (m : Fin (2 ^ mMidUB wInner2)) :
    ((rOutUB wOuter wInner2).embedUnitary
        ((rXoLoc wOuter).embedUnitary (Operator.permutationUnitary ρ))).1 *ᵥ embedKet ψ o' m =
      embedKet ψ (outPermEquiv ρ wOuter o') m := by
  rw [embedUnitary_rXoLoc_permutationUnitary, QRegister.embedUnitary_val,
    embedMatrix_rOutUB_mulVec_embedKet]
  have hsingle (o : Fin (2 ^ mOutUB wOuter)) :
      (Operator.permutationUnitary (outPermEquiv ρ wOuter)).1 o o' =
        if o = outPermEquiv ρ wOuter o' then 1 else 0 := by
    simpa [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] using
      congrFun (Operator.permutationUnitary_mulVec_single (outPermEquiv ρ wOuter) o' 1) o
  simp_rw [hsingle]; rw [Finset.sum_eq_single (outPermEquiv ρ wOuter o')] <;> simp +contextual

theorem prepMidDirectXo7Mux_mulVec_embedKet_loc {wOuter wInner2 : ℕ}
    (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2))
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter)) (m : Fin (2 ^ mMidUB wInner2)) :
    (prepMidDirectXo7MuxUnitary wOuter wInner2 prepMid).1 *ᵥ embedKet ψ o' m =
      ∑ m' : Fin (2 ^ mMidUB wInner2),
        ((prepMid ((rXo7Loc wOuter).extractIndex o')).1 m' m) • embedKet ψ o' m' := by
  have hxo (g : Fin (2 ^ nUB wOuter wInner2))
      (hne : (rXo7UB wOuter wInner2).extractIndex g ≠ (rXo7Loc wOuter).extractIndex o') :
      embedKet ψ o' m g = 0 := by
    dsimp [embedKet]
    by_cases hc : (rOutUB wOuter wInner2).extractIndex g =
        o' ∧ (rMidUB wOuter wInner2).extractIndex g = m
    · exact absurd (by rw [show rXo7UB wOuter wInner2 = (rOutUB wOuter wInner2).compose (rXo7Loc
        wOuter) from rfl,
        QRegister.extractIndex_compose, hc.1]) hne
    · simp [hc]
  unfold prepMidDirectXo7MuxUnitary
  rw [muxUnitary_mulVec_of_proj _ _ _ _ ((rXo7Loc wOuter).extractIndex o') _ hxo,
    embedMatrix_rMidUB_mulVec_embedKet]

theorem projMid_core_selectPure_embedKet {wOuter wInner2 : ℕ} (ρ : Equiv.Perm (Fin (2 ^ 8)))
    (M : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)) (selectPure : Unitary (2 ^ nUB wOuter wInner2))
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter))
    (hSel : ∀ m : Fin (2 ^ mMidUB wInner2), (M ((rXo7Loc wOuter).extractIndex o')).1 m 0 ≠ 0 →
      selectPure.1 *ᵥ embedKet ψ o' m =
        embedKet ((selectBranchUnitary (ρ ((rXoLoc wOuter).extractIndex o'))
          ((rSigOutLoc wOuter).extractIndex o')
          ((rBLoc wInner2).extractIndex m) ((rSigInLoc wInner2).extractIndex m)).1 *ᵥ ψ) o' m) :
    (rMidUB wOuter wInner2).basisOutcomeProjector 0 *ᵥ
        (((prepMidDirectXo7MuxUnitary wOuter wInner2 M)⁻¹ * selectPure *
          prepMidDirectXo7MuxUnitary wOuter wInner2 M).1 *ᵥ embedKet ψ o' 0) =
      embedKet (w_gi := wInner2) ((∑ m : Fin (2 ^ mMidUB wInner2),
        (Complex.normSq ((M ((rXo7Loc wOuter).extractIndex o')).1 m 0) : ℂ) •
          (selectBranchUnitary (ρ ((rXoLoc wOuter).extractIndex o'))
            ((rSigOutLoc wOuter).extractIndex o')
            ((rBLoc wInner2).extractIndex m)
            ((rSigInLoc wInner2).extractIndex m)).1) *ᵥ ψ) o' 0 := by
  let rc7 := (rXo7Loc wOuter).extractIndex o'
  rw [show (prepMidDirectXo7MuxUnitary wOuter wInner2 M)⁻¹ =
      prepMidDirectXo7MuxUnitary wOuter wInner2 (fun r ↦ (M r)⁻¹) from muxUnitary_inv _ _ _ _]
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, prepMidDirectXo7Mux_mulVec_embedKet_loc,
    Matrix.mulVec_sum, Matrix.mulVec_smul]
  have hterm (m : Fin (2 ^ mMidUB wInner2)) :
      ((M rc7).1 m 0) • ((rMidUB wOuter wInner2).basisOutcomeProjector 0 *ᵥ
        ((prepMidDirectXo7MuxUnitary wOuter wInner2 fun r ↦ (M r)⁻¹).1 *ᵥ
          (selectPure.1 *ᵥ embedKet ψ o' m))) =
      embedKet (w_gi := wInner2) (((Complex.normSq ((M rc7).1 m 0) : ℂ) •
        (selectBranchUnitary (ρ ((rXoLoc wOuter).extractIndex o'))
          ((rSigOutLoc wOuter).extractIndex o')
          ((rBLoc wInner2).extractIndex m) ((rSigInLoc wInner2).extractIndex m)).1) *ᵥ ψ) o' 0 := by
    by_cases hnz : (M rc7).1 m 0 = 0
    · rw [hnz, Complex.normSq_zero, Complex.ofReal_zero, zero_smul, zero_smul, Matrix.zero_mulVec]
      ext g; simp [embedKet]
    · rw [hSel m hnz, prepMidDirectXo7Mux_mulVec_embedKet_loc, Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, projMid_mulVec_embedKet]
      rw [Finset.sum_eq_single 0]
      · have hadj : ((M rc7)⁻¹).1 0 m = star ((M rc7).1 m 0) := rfl
        rw [ite_eq_left rfl, hadj, smul_smul, Complex.star_def, Complex.mul_conj,
          ← embedKet_smul, Matrix.smul_mulVec]
      · intro x _ hx; rw [ite_eq_right hx, smul_zero]
      · intro h0; exact (h0 (Finset.mem_univ 0)).elim
  exact (Finset.sum_congr rfl fun m _ ↦ hterm m).trans (by rw [← embedKet_sum, Matrix.sum_mulVec])

theorem projMid_core_oneBody_eq_of_halfSpin {wOuter wInner2 : ℕ} (ρ : Equiv.Perm (Fin (2 ^ 8)))
    {M : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)} (hHalf : PrepMidHalfSpin M)
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter))
    (h1b : (ρ ((rXoLoc wOuter).extractIndex o')).val < 58) :
    (rMidUB wOuter wInner2).basisOutcomeProjector 0 *ᵥ
        (((prepMidDirectXo7MuxUnitary wOuter wInner2 M)⁻¹ * balRefSelectPureUnitary ρ wOuter wInner2
          *
          prepMidDirectXo7MuxUnitary wOuter wInner2 M).1 *ᵥ embedKet ψ o' 0) =
      embedKet (w_gi := wInner2)
        ((((1 / 2 : ℝ) : ℂ) •
            (selectBranchUnitary (ρ ((rXoLoc wOuter).extractIndex o'))
              ((rSigOutLoc wOuter).extractIndex o') 0 0).1 +
          ((1 / 2 : ℝ) : ℂ) •
            (selectBranchUnitary (ρ ((rXoLoc wOuter).extractIndex o'))
              ((rSigOutLoc wOuter).extractIndex o') 0 1).1) *ᵥ ψ) o' 0 := by
  let xo := ρ ((rXoLoc wOuter).extractIndex o'); let so := (rSigOutLoc wOuter).extractIndex o'
  have hxo : xo.val < 58 := h1b
  have hbr (b : Fin (2 ^ 5)) (si : Fin 2) :
      (selectBranchUnitary xo so b si).1 = (selectBranchUnitary xo so 0 si).1 := by
    have his1 : isOneBodyXo xo = true := decide_eq_true hxo
    have hneg : negPhaseOf xo b si = negPhaseOf xo 0 si := by simp [negPhaseOf, his1]
    have hen : enROf xo b si = enROf xo 0 si := by simp [enROf, his1]
    have hrow : rowIdxOf xo b = rowIdxOf xo 0 := by
      dsimp only [rowIdxOf]; rw [dite_eq_left hxo, dite_eq_left hxo]
    change (if negPhaseOf xo b si then (-1 : ℂ) else 1) •
        (if enROf xo b si then (blockedRowReflectionUnitary (rowIdxOf xo b) (sigSelOf xo so si)).1
         else 1) =
      (if negPhaseOf xo 0 si then (-1 : ℂ) else 1) •
        (if enROf xo 0 si then (blockedRowReflectionUnitary (rowIdxOf xo 0) (sigSelOf xo so si)).1
         else 1)
    rw [hneg, hen, hrow]
  rw [projMid_core_selectPure_embedKet ρ M _ ψ o'
    (fun m _ ↦ balRefSelectPureUnitary_mulVec_embedKet ρ ψ o' m)]
  refine congrArg (fun Φ ↦ embedKet (w_gi := wInner2) Φ o' 0) (congrArg (· *ᵥ ψ) ?_)
  rw [Finset.sum_congr rfl fun m _ ↦
      congrArg _ (hbr ((rBLoc wInner2).extractIndex m) ((rSigInLoc wInner2).extractIndex m)),
    ← Finset.sum_fiberwise_of_maps_to (g := (rSigInLoc wInner2).extractIndex)
      (fun _ _ ↦ Finset.mem_univ _)]
  have hfib (si : Fin 2) :
      (∑ m ∈ Finset.univ.filter (fun m : Fin (2 ^ mMidUB wInner2) ↦
          (rSigInLoc wInner2).extractIndex m = si),
        (Complex.normSq ((M ((rXo7Loc wOuter).extractIndex o')).1 m 0) : ℂ) •
          (selectBranchUnitary xo so 0 ((rSigInLoc wInner2).extractIndex m)).1) =
      ((1 / 2 : ℝ) : ℂ) • (selectBranchUnitary xo so 0 si).1 := by
    rw [← hHalf ((rXo7Loc wOuter).extractIndex o') si, Complex.ofReal_sum, Finset.sum_smul]
    exact Finset.sum_congr rfl fun m hm ↦ by rw [(Finset.mem_filter.mp hm).2]
  exact (Finset.sum_congr rfl fun si _ ↦ hfib si).trans (Fin.sum_univ_two _)

/-- `(c)` Exact half-step `P_τ`-absorption identity bridging `(σ, fun rc ↦ prepMid (π128 rc))`
at `prepOutIdeal` to `(σ * (tauPerm256 π128)⁻¹, prepMid)` at `P_τ * prepOutIdeal`. -/
theorem ubDirectXo7PureUnitary_pi128_halfStep_eq {σ : Equiv.Perm (Fin (2 ^ 8))}
    {π128 : Equiv.Perm (Fin (2 ^ 7))} {wOuter wInner2 : ℕ}
    (h128_1B : ∀ x : Fin (2 ^ 8), 128 ≤ x.val → x.val < 184 → (σ x).val < 58)
    {prepOutIdeal : Unitary (2 ^ mOutUB wOuter)}
    (hOut0 : ∀ o' : Fin (2 ^ mOutUB wOuter),
      184 ≤ ((rXoLoc wOuter).extractIndex o').val → prepOutIdeal.1 o' 0 = 0)
    {prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)} (hHalf : PrepMidHalfSpin prepMid)
    (ψ : Fin (2 ^ systemQubits_local) → ℂ) :
    let P_τ := (rXoLoc wOuter).embedUnitary (Operator.permutationUnitary (tauPerm256 π128))
    let U_τ := (rOutUB wOuter wInner2).embedUnitary P_τ
    U_τ.1 *ᵥ
        (QubitisedWalk.projMid (rMidInWalk (mOutUB wOuter) (mMidUB wInner2)) *ᵥ
          ((ubDirectXo7PureUnitary prepOutIdeal (fun rc ↦ prepMid (π128 rc))
              (balRefSelectPureUnitary σ wOuter wInner2)).1 *ᵥ
            (rSysInWalk (mOutUB wOuter) (mMidUB wInner2)).tensorState ψ (Pi.single 0 1))) =
      QubitisedWalk.projMid (rMidInWalk (mOutUB wOuter) (mMidUB wInner2)) *ᵥ
        ((ubDirectXo7PureUnitary (P_τ * prepOutIdeal) prepMid
            (balRefSelectPureUnitary (σ * (tauPerm256 π128)⁻¹) wOuter wInner2)).1 *ᵥ
          (rSysInWalk (mOutUB wOuter) (mMidUB wInner2)).tensorState ψ (Pi.single 0 1)) := by
  intro P_τ U_τ; let τ := tauPerm256 π128
  change U_τ.1 *ᵥ ((rMidUB wOuter wInner2).basisOutcomeProjector 0 *ᵥ
      ((ubDirectXo7PureUnitary prepOutIdeal (fun rc ↦ prepMid (π128 rc))
        (balRefSelectPureUnitary σ wOuter wInner2)).1 *ᵥ
        (rSysUB wOuter wInner2).tensorState ψ (Pi.single 0 1))) =
    (rMidUB wOuter wInner2).basisOutcomeProjector 0 *ᵥ
      ((ubDirectXo7PureUnitary (P_τ * prepOutIdeal) prepMid
        (balRefSelectPureUnitary (σ * τ⁻¹) wOuter wInner2)).1 *ᵥ
        (rSysUB wOuter wInner2).tensorState ψ (Pi.single 0 1))
  rw [← embedKet_zero_zero_eq_tensorState]
  dsimp only [ubDirectXo7PureUnitary]
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, QRegister.embedUnitary_val,
    embedMatrix_rOutUB_mulVec_embedKet, Matrix.mulVec_sum, Matrix.mulVec_smul]
  refine Finset.sum_bij (fun o' _ ↦ outPermEquiv τ wOuter o') (fun _ _ ↦ Finset.mem_univ _)
    (fun _ _ _ _ h ↦ (outPermEquiv τ wOuter).injective h)
    (fun o _ ↦ ⟨(outPermEquiv τ wOuter).symm o, Finset.mem_univ _,
      (outPermEquiv τ wOuter).apply_symm_apply o⟩) fun o' _ ↦ ?_
  rw [show P_τ.1 * prepOutIdeal.1 = (P_τ * prepOutIdeal).1 from rfl,
    mul_embedUnitary_rXoLoc_permutationUnitary_apply, Equiv.symm_apply_apply]
  let xo' := (rXoLoc wOuter).extractIndex o'
  by_cases h184 : 184 ≤ xo'.val
  · rw [hOut0 o' h184, zero_smul, zero_smul]
  · refine congrArg (prepOutIdeal.1 o' 0 • ·) ?_
    by_cases h128 : xo'.val < 2 ^ 7
    · let o'' := outPermEquiv τ wOuter o'
      have hxo_o'' : (rXoLoc wOuter).extractIndex o'' = τ xo' := extract_rXoLoc_outPermEquiv τ o'
      have h128_o'' : ((rXoLoc wOuter).extractIndex o'').val < 2 ^ 7 := by
        rw [hxo_o'', tauPerm256_lt128 π128 xo' h128]; exact (π128 _).isLt
      have hrc : (rXo7Loc wOuter).extractIndex o'' = π128 ((rXo7Loc wOuter).extractIndex o') := by
        rw [extract_rXo7Loc_of_lt128 o'' h128_o'', extract_rXo7Loc_of_lt128 o' h128]
        apply Fin.ext
        change ((rXoLoc wOuter).extractIndex o'').val = (π128 ⟨xo'.val, h128⟩).val
        rw [hxo_o'']; exact tauPerm256_lt128 π128 xo' h128
      have hσ : (σ * τ⁻¹) ((rXoLoc wOuter).extractIndex o'') = σ xo' := by
        rw [hxo_o'', Equiv.Perm.mul_apply]; exact congrArg σ (τ.symm_apply_apply xo')
      have hso : (rSigOutLoc wOuter).extractIndex o'' = (rSigOutLoc wOuter).extractIndex o' :=
        extract_rSigOutLoc_outPermEquiv τ o'
      have hL := projMid_core_selectPure_embedKet σ (fun rc ↦ prepMid (π128 rc)) _ ψ o'
        (fun m _ ↦ balRefSelectPureUnitary_mulVec_embedKet σ ψ o' m)
      have hR := projMid_core_selectPure_embedKet (σ * τ⁻¹) prepMid _ ψ o''
        (fun m _ ↦ balRefSelectPureUnitary_mulVec_embedKet (σ * τ⁻¹) ψ o'' m)
      simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec] at hL hR
      rw [hL, hR, show U_τ.1 = ((rOutUB wOuter wInner2).embedUnitary P_τ).1 from rfl,
        embedUnitary_rOutUB_perm_mulVec_embedKet, hrc, hσ, hso]
    · have hτ : τ xo' = xo' := tauPerm256_ge128 π128 xo' (by omega)
      have hτi : τ⁻¹ xo' = xo' := by
        rw [tauPerm256_inv_eq]; exact tauPerm256_ge128 π128.symm xo' (by omega)
      have ho'' : outPermEquiv τ wOuter o' = o' := by
        dsimp [outPermEquiv]; rw [show τ ((rXoLoc wOuter).extractIndex o') = xo' from hτ]
        exact (rXoLoc wOuter).replaceIndex_extractIndex o'
      have hσ_eq : (σ * τ⁻¹) xo' = σ xo' := by rw [Equiv.Perm.mul_apply, hτi]
      have h1b : (σ xo').val < 58 := h128_1B xo' (by omega) (by omega)
      have hL := projMid_core_oneBody_eq_of_halfSpin σ (fun rc si ↦ hHalf (π128 rc) si) ψ o' h1b
      have hR := projMid_core_oneBody_eq_of_halfSpin (σ * τ⁻¹) hHalf ψ o' (by rw [hσ_eq]; exact h1b)
      simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec] at hL hR
      rw [ho'', hL, hR, show U_τ.1 = ((rOutUB wOuter wInner2).embedUnitary P_τ).1 from rfl,
        embedUnitary_rOutUB_perm_mulVec_embedKet, ho'', hσ_eq]

theorem ubDirectXo7PureUnitary_selectPure_halfStep_eq_balRef {σ : Equiv.Perm (Fin (2 ^ 8))}
    {wOuter wInner2 : ℕ} {prepOutPerm : Unitary (2 ^ mOutUB wOuter)}
    (hOut0 : ∀ o' : Fin (2 ^ mOutUB wOuter),
      184 ≤ ((rXoLoc wOuter).extractIndex o').val → prepOutPerm.1 o' 0 = 0)
    (M : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)) (selectPure : Unitary (2 ^ nUB wOuter wInner2))
    (hSelAct : SelectActiveOn σ M selectPure) (ψ : Fin (2 ^ systemQubits_local) → ℂ) :
    QubitisedWalk.projMid (rMidInWalk (mOutUB wOuter) (mMidUB wInner2)) *ᵥ
        ((ubDirectXo7PureUnitary prepOutPerm M selectPure).1 *ᵥ
          (rSysInWalk (mOutUB wOuter) (mMidUB wInner2)).tensorState ψ (Pi.single 0 1)) =
      QubitisedWalk.projMid (rMidInWalk (mOutUB wOuter) (mMidUB wInner2)) *ᵥ
        ((ubDirectXo7PureUnitary prepOutPerm M (balRefSelectPureUnitary σ wOuter wInner2)).1 *ᵥ
          (rSysInWalk (mOutUB wOuter) (mMidUB wInner2)).tensorState ψ (Pi.single 0 1)) := by
  change (rMidUB wOuter wInner2).basisOutcomeProjector 0 *ᵥ _ =
    (rMidUB wOuter wInner2).basisOutcomeProjector 0 *ᵥ _
  rw [← embedKet_zero_zero_eq_tensorState]; dsimp only [ubDirectXo7PureUnitary]
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, QRegister.embedUnitary_val,
    embedMatrix_rOutUB_mulVec_embedKet, Matrix.mulVec_sum, Matrix.mulVec_smul]
  refine Finset.sum_congr rfl fun o' _ ↦ ?_
  by_cases hlt : ((rXoLoc wOuter).extractIndex o').val < 184
  · have h1 := projMid_core_selectPure_embedKet σ M selectPure ψ o' (hSelAct ψ o' · hlt)
    have h2 := projMid_core_selectPure_embedKet σ M (balRefSelectPureUnitary σ wOuter wInner2) ψ o'
      (fun m _ ↦ balRefSelectPureUnitary_mulVec_embedKet σ ψ o' m)
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec] at h1 h2; rw [h1, h2]
  · rw [hOut0 o' (by omega), zero_smul, zero_smul]

/-- `(c)` Master `PulledSOSBlockEncoding` equivalence for ANY `(H_tilde_blk, eLB, lam)`. -/
theorem pulledSOSBlockEncoding_ubDirectXo7Pure_pi128_iff {σ : Equiv.Perm (Fin (2 ^ 8))}
    {π128 : Equiv.Perm (Fin (2 ^ 7))} {wOuter wInner2 : ℕ}
    (h128_1B : ∀ x : Fin (2 ^ 8), 128 ≤ x.val → x.val < 184 → (σ x).val < 58)
    {prepOutIdeal : Unitary (2 ^ mOutUB wOuter)}
    (hOut0 : ∀ o' : Fin (2 ^ mOutUB wOuter),
      184 ≤ ((rXoLoc wOuter).extractIndex o').val → prepOutIdeal.1 o' 0 = 0)
    {prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)} (hHalf : PrepMidHalfSpin prepMid)
    (H_tilde_blk : Operator (2 ^ systemQubits_local)) (eLB lam : ℝ) :
    let P_τ := (rXoLoc wOuter).embedUnitary (Operator.permutationUnitary (tauPerm256 π128))
    PulledSOSBlockEncoding (mOutUB wOuter) (mMidUB wInner2) H_tilde_blk eLB lam
        (ubDirectXo7PureUnitary prepOutIdeal (fun rc ↦ prepMid (π128 rc))
          (balRefSelectPureUnitary σ wOuter wInner2)) ↔
      PulledSOSBlockEncoding (mOutUB wOuter) (mMidUB wInner2) H_tilde_blk eLB lam
        (ubDirectXo7PureUnitary (P_τ * prepOutIdeal) prepMid
          (balRefSelectPureUnitary (σ * (tauPerm256 π128)⁻¹) wOuter wInner2)) := by
  intro P_τ; let U_τ := (rOutUB wOuter wInner2).embedUnitary P_τ
  have hH := ubDirectXo7PureUnitary_pi128_halfStep_eq (σ := σ) (π128 := π128) h128_1B hOut0 hHalf
  refine ⟨fun hL ↦ pulledSOSBlockEncoding_of_halfStep_unitary_eq (U_walk := U_τ⁻¹) hL fun φ ↦ ?_,
    fun hR ↦ pulledSOSBlockEncoding_of_halfStep_unitary_eq (U_walk := U_τ) hR hH⟩
  rw [← hH φ, Matrix.mulVec_mulVec, ← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one,
    Matrix.one_mulVec]

/-! ## Section 4: Turnkey `PulledSOSBlockEncoding` Corollaries & `π145` Specializations -/

/-- `(d)` Jointly-quantized `PulledSOSBlockEncoding` for `(σ, π128)` with active `selectPure`. -/
theorem pulledSOSBlockEncoding_ubDirectXo7Pure_pi128_quantJoint {σ : Equiv.Perm (Fin (2 ^ 8))}
    {π128 : Equiv.Perm (Fin (2 ^ 7))} {wOuter wInner2 : ℕ}
    (hπ : ∀ (x : Fin (2 ^ 8)) (hx : x.val < 126), (σ x).val = 58 + (π128 ⟨x.val, by omega⟩).val)
    (hfix126 : π128 ⟨126, by decide⟩ = ⟨126, by decide⟩ ∧
      π128 ⟨127, by decide⟩ = ⟨127, by decide⟩)
    (h1B : ∀ x : Fin (2 ^ 8), 126 ≤ x.val → x.val < 184 → (σ x).val < 58)
    (hpad : ∀ x : Fin (2 ^ 8), 184 ≤ x.val → σ x = x)
    {qOut : Fin 184 → ℝ} {pIn : Fin 126 → Fin 30 → ℝ}
    {prepOutIdeal : Unitary (2 ^ mOutUB wOuter)} (hOut : PrepOutQuantPerm256 σ qOut prepOutIdeal)
    {prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)} (hMid : PrepMidQuant128 pIn prepMid)
    (selectPure : Unitary (2 ^ nUB wOuter wInner2))
    (hSelAct : SelectActiveOn σ (fun rc ↦ prepMid (π128 rc)) selectPure) :
    PulledSOSBlockEncoding (mOutUB wOuter) (mMidUB wInner2) (quantJointP450HBlocked qOut pIn)
      dfthcLowerBound 97.3864
      (ubDirectXo7PureUnitary prepOutIdeal (fun rc ↦ prepMid (π128 rc)) selectPure) := by
  have hBal := (pulledSOSBlockEncoding_ubDirectXo7Pure_pi128_iff
      (fun x h128 h184 ↦ h1B x (by omega) h184) hOut.1 hMid.2.2 _ _ _).mpr
      (pulledSOSBlockEncoding_ubDirectXo7Pure_quantJoint
        (isZeroRcOuterPerm_comp_tau_symm hπ hfix126 h1B hpad)
        (prepOutQuantPerm256_mul_tauPerm256 π128 hOut) hMid _
        fun ψ o' m _ _ ↦ balRefSelectPureUnitary_mulVec_embedKet _ ψ o' m)
  refine pulledSOSBlockEncoding_of_halfStep_unitary_eq (U_walk := 1) hBal fun φ ↦ ?_
  rw [OneMemClass.coe_one, Matrix.one_mulVec]
  exact ubDirectXo7PureUnitary_selectPure_halfStep_eq_balRef hOut.1 _ selectPure hSelAct φ

/-- `(d)` Inner-quantized `PulledSOSBlockEncoding` for `(σ, π128)` with active `selectPure`. -/
theorem pulledSOSBlockEncoding_ubDirectXo7Pure_pi128_quantInner {σ : Equiv.Perm (Fin (2 ^ 8))}
    {π128 : Equiv.Perm (Fin (2 ^ 7))} {wOuter wInner2 : ℕ}
    (hπ : ∀ (x : Fin (2 ^ 8)) (hx : x.val < 126), (σ x).val = 58 + (π128 ⟨x.val, by omega⟩).val)
    (hfix126 : π128 ⟨126, by decide⟩ = ⟨126, by decide⟩ ∧
      π128 ⟨127, by decide⟩ = ⟨127, by decide⟩)
    (h1B : ∀ x : Fin (2 ^ 8), 126 ≤ x.val → x.val < 184 → (σ x).val < 58)
    (hpad : ∀ x : Fin (2 ^ 8), 184 ≤ x.val → σ x = x) {pIn : Fin 126 → Fin 30 → ℝ}
    {prepOutIdeal : Unitary (2 ^ mOutUB wOuter)} (hOut : PrepOutValidPerm256 σ prepOutIdeal)
    {prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)} (hMid : PrepMidQuant128 pIn prepMid)
    (selectPure : Unitary (2 ^ nUB wOuter wInner2))
    (hSelAct : SelectActiveOn σ (fun rc ↦ prepMid (π128 rc)) selectPure) :
    PulledSOSBlockEncoding (mOutUB wOuter) (mMidUB wInner2) (quantInnerP450HBlocked pIn)
      dfthcLowerBound 97.3864
      (ubDirectXo7PureUnitary prepOutIdeal (fun rc ↦ prepMid (π128 rc)) selectPure) :=
  pulledSOSBlockEncoding_ubDirectXo7Pure_pi128_quantJoint hπ hfix126 h1B hpad
    (prepOutQuantPerm256_of_validPerm256 hOut) hMid selectPure hSelAct

/-- Concrete `π145` inner-quantized `PulledSOSBlockEncoding` with active `selectPure`. -/
theorem pulledSOSBlockEncoding_pi145_quantInner {wOuter wInner2 : ℕ}
    {pIn : Fin 126 → Fin 30 → ℝ} {prepOutIdeal : Unitary (2 ^ mOutUB wOuter)}
    (hOut : PrepOutValidPerm256 pi145XoEquiv prepOutIdeal)
    {prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)} (hMid : PrepMidQuant128 pIn prepMid)
    (selectPure : Unitary (2 ^ nUB wOuter wInner2))
    (hSelAct : SelectActiveOn pi145XoEquiv (fun rc ↦ prepMid (pi128Equiv rc)) selectPure) :
    PulledSOSBlockEncoding (mOutUB wOuter) (mMidUB wInner2) (quantInnerP450HBlocked pIn)
      dfthcLowerBound 97.3864
      (ubDirectXo7PureUnitary prepOutIdeal (fun rc ↦ prepMid (pi128Equiv rc)) selectPure) :=
  pulledSOSBlockEncoding_ubDirectXo7Pure_pi128_quantInner pi145XoEquiv_hpi
    pi128Equiv_hfix126 pi145XoEquiv_h1B pi145XoEquiv_hpad hOut hMid selectPure hSelAct

/-- Generic `AgreesOnElectronSector 58 η` bound for `quantInnerP450HBlocked pIn` from per-slice
`L¹` error `εIn`. -/
theorem agreesOnElectronSector_quantInner_of_l1 {pIn : Fin 126 → Fin 30 → ℝ}
    (hp0 : ∀ rc b, 0 ≤ pIn rc b) (hp1 : ∀ rc, (∑ b : Fin 30, pIn rc b) = 1)
    {εIn δH : ℝ}
    (hl1 : ∀ rc : Fin 126, (∑ b : Fin 30, |pIn rc b - p450ExactInnerProb rc b|) ≤ εIn)
    (hδ : (4 * 97.3864 * 144553 / 188416) * εIn ≤ δH) (η : ℕ) :
    AgreesOnElectronSector 58 η (quantInnerP450HBlocked pIn) BlockEncodingCore.p450HBlocked δH :=
  agreesOnElectronSector_of_comm_and_opNorm
    (quantJointP450HBlocked_comm_electronSectorProjector p450ExactOuterProb pIn η)
    ((norm_quantInnerP450HBlocked_sub_le hp0 hp1 hl1).trans hδ)

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Pi145SOSPermBridge

end
