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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.WronskianCert135598
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.GqspUpperPostT23Re

/-!
# Upper `8 → 4 → 2 → 1` Real Tournament Merge & Post-Root Check (`GqspUpperPost135598`)

Proves the `t1` (`chebL1 ≤ 807906351 * shift0`) half of the `135,868`-gate post-root check via
`gqsp_upperRealTreePostT1Ble` and combines it with `upperRealTreePostT23Ok` (`45809523903`) via
`gqsp_upperRealTreePostChunks2Ble_of_split` (`807906351 + 45809523903 = 46617430254`).
-/

@[expose] public section
set_option compiler.extract_closed false
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

namespace GqspUpperPost135598

section UpperPost135598
set_option maxRecDepth 6000000
set_option exponentiation.threshold 2048

open TFreeLaurentGQSP
open TFreeLaurentGQSPPresets.FastRecurrenceVerifier
open GqspWronskian62592
open GqspWronskianUV135598
open GqspWronskian135598
open GqspTreeBaseHelpers135598
open GqspTreeSubShards01_135598
open GqspTreeSubShards23_135598
open GqspTreeSubShards45_135598
open GqspTreeSubShards67_135598
open GqspUpperPostT23_135598
open GqspUpperPostT1Data_135598

/-- Zero-WHNF-cache 29th-degree Taylor interval upper bound for a single catalyst gate (`0` inner
`DefinitionVal`s). -/
noncomputable abbrev gqsp_zwGateUpper (c_raw : ℕ) (g : DyadicRyGate) : ℕ :=
  @DyadicRyGate.rec (fun _ ↦ ℕ)
    (fun t0 t1 neg_c neg_s ↦
      @Nat.rec (fun _ ↦ ℕ) 0 (fun c_val _ ↦
        let is_le := Nat.ble c_val 0x20000000000
        let mag := @Bool.rec (fun _ ↦ ℕ) (Nat.sub 0x40000000000 c_val) c_val is_le
        @Nat.rec (fun _ ↦ ℕ) 0 (fun nx _ ↦
          let p0 := 0x1000000000000000000000000
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p1 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p2 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p3 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p4 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p5 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p6 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p7 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p8 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p9 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p10 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p11 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p12 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p13 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p14 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p15 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p16 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p17 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p18 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p19 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p20 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p21 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p22 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p23 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p24 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p25 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p26 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p27 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p28 _ ↦
          @Nat.rec (fun _ ↦ ℕ) 0 (fun p29 _ ↦
            let cP := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0
                (Nat.mul 0x6f99461a1e9e1432dcb6000000 p0)) (Nat.mul
                0x4a662ebc146962cc932400000 p4)) (Nat.mul 0xb5646830f4d02dd5840000 p8))
                (Nat.mul 0x3e8a65c6c052cf28000 p12)) (Nat.mul 0x5dd576018094400 p16)) (Nat.mul
                0x34e29e21380 p20)) (Nat.mul 0xd97268 p24)) (Nat.mul 0x1d p28)
            let cN := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul
                0x37cca30d0f4f0a196e5b000000 p2)) (Nat.mul 0x27adf6cab58d8a06b4e00000 p6))
                (Nat.mul 0x203f5c7a7b2ab2d0a0000 p10)) (Nat.mul 0x57f81ea1688afc000 p14))
                (Nat.mul 0x4e8062b94f200 p18)) (Nat.mul 0x1d4deb040 p22)) (Nat.mul 0x55a4 p26)
            let sP := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0
                (Nat.mul 0x6f99461a1e9e1432dcb6000000 p1)) (Nat.mul 0xee13c8c041513c283d400000
                p5)) (Nat.mul 0x142799cc8cfaafc2640000 p9)) (Nat.mul 0x4cf91acd3b799c8000
                p13)) (Nat.mul 0x58506f10790400 p17)) (Nat.mul 0x284b232580 p21)) (Nat.mul
                0x8b2a8 p25)) (Nat.mul 0x1 p29)
            let sN := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul
                0x12998baf051a58b324c9000000 p3)) (Nat.mul 0x5ab234187a6816eac200000 p7))
                (Nat.mul 0x2ee7cc55103e1b5e0000 p11)) (Nat.mul 0x5dd5760180944000 p15))
                (Nat.mul 0x421b45a98600 p19)) (Nat.mul 0x1462b9c0 p23)) (Nat.mul 0x32c p27)
            @Nat.rec (fun _ ↦ ℕ) 0 (fun cP_15 _ ↦
            @Nat.rec (fun _ ↦ ℕ) 0 (fun cN_15 _ ↦
            @Nat.rec (fun _ ↦ ℕ) 0 (fun sP_15 _ ↦
            @Nat.rec (fun _ ↦ ℕ) 0 (fun sN_15 _ ↦
              let cPHi := Nat.add cP_15 0x1c904eb8afd9b17db2e982c3ca9
              let cNHi := Nat.add cN_15 0x1f56ef9e3c3afc44231a350c2b4
              let sPHi := Nat.add sP_15 0x1c80028f50f8489257ac45e369d
              let sNHi := Nat.add sN_15 0x20374aa0ae5949e9f9946f5d45c
              let gc_u := Nat.mul t0 0x6f99461a1e9e1432dcb6000000000000000000
              let gs_u := Nat.mul (Nat.sub t1 t0) 0x6f99461a1e9e1432dcb6000000000000000000
              let dc := @Bool.rec (fun _ ↦ ℕ)
                (let a := Nat.sub (Nat.add gc_u cNHi) cP_15
                 let b := Nat.sub cPHi (Nat.add cN_15 gc_u)
                 Nat.add a (Nat.sub b a))
                (let a := Nat.sub cNHi (Nat.add cP_15 gc_u)
                 let b := Nat.sub (Nat.add cPHi gc_u) cN_15
                 Nat.add a (Nat.sub b a))
                neg_c
              let neg_s' := @Bool.rec (fun _ ↦ Bool) neg_s (@Bool.rec (fun _ ↦
                Bool) true false neg_s) neg_c
              let sLo := @Bool.rec (fun _ ↦ ℕ) sP_15 sN_15 is_le
              let sHi := @Bool.rec (fun _ ↦ ℕ) sPHi sNHi is_le
              let nLo := @Bool.rec (fun _ ↦ ℕ) sN_15 sP_15 is_le
              let nHi := @Bool.rec (fun _ ↦ ℕ) sNHi sPHi is_le
              let ds := @Bool.rec (fun _ ↦ ℕ)
                (let a := Nat.sub (Nat.add gs_u nHi) sLo
                 let b := Nat.sub sHi (Nat.add nLo gs_u)
                 Nat.add a (Nat.sub b a))
                (let a := Nat.sub nHi (Nat.add sLo gs_u)
                 let b := Nat.sub (Nat.add sHi gs_u) nLo
                 Nat.add a (Nat.sub b a))
                neg_s'
              Nat.add dc ds)
              (Nat.add 1 sN))
              (Nat.add 1 sP))
              (Nat.add 1 cN))
              (Nat.add 1 cP))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p28 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p27 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p26 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p25 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p24 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p23 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p22 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p21 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p20 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p19 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p18 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p17 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p16 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p15 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p14 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p13 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p12 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p11 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p10 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p9 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p8 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p7 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p6 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p5 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p4 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p3 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p2 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p1 nx) 52)))
            (Nat.add 1 (Nat.shiftRight (Nat.mul p0 nx) 52)))
          (Nat.add 1 (Nat.shiftRight (Nat.mul 0x3243f6a8885a308d3 mag) 53)))
        (Nat.add 1 (Nat.land c_raw 0x3ffffffffff)))
    g

private theorem gqsp_zwCatRatNx_eq (c_val : ℕ) : Nat.shiftRight (Nat.mul 0x3243f6a8885a308d3
    (@Bool.rec (fun _ ↦ ℕ) (Nat.sub 0x40000000000 c_val) c_val (Nat.ble c_val 0x20000000000)))
    53 = gqsp_catRatNx c_val := by
  unfold gqsp_catRatNx
  cases Nat.ble c_val 0x20000000000 <;> rfl

private theorem gqsp_zwFinishGate_eq (c_val t0 t1 : ℕ) (neg_c neg_s : Bool)
    (cP_15 cN_15 sP_15 sN_15 : ℕ) :
    (let is_le := Nat.ble c_val 0x20000000000
     let cPHi := Nat.add cP_15 0x1c904eb8afd9b17db2e982c3ca9
     let cNHi := Nat.add cN_15 0x1f56ef9e3c3afc44231a350c2b4
     let sPHi := Nat.add sP_15 0x1c80028f50f8489257ac45e369d
     let sNHi := Nat.add sN_15 0x20374aa0ae5949e9f9946f5d45c
     let gc_u := Nat.mul t0 0x6f99461a1e9e1432dcb6000000000000000000
     let gs_u := Nat.mul (Nat.sub t1 t0) 0x6f99461a1e9e1432dcb6000000000000000000
     let dc := @Bool.rec (fun _ ↦ ℕ)
       (let a := Nat.sub (Nat.add gc_u cNHi) cP_15
        let b := Nat.sub cPHi (Nat.add cN_15 gc_u)
        Nat.add a (Nat.sub b a))
       (let a := Nat.sub cNHi (Nat.add cP_15 gc_u)
        let b := Nat.sub (Nat.add cPHi gc_u) cN_15
        Nat.add a (Nat.sub b a))
       neg_c
     let neg_s' := @Bool.rec (fun _ ↦ Bool) neg_s (@Bool.rec (fun _ ↦ Bool) true false neg_s) neg_c
     let sLo := @Bool.rec (fun _ ↦ ℕ) sP_15 sN_15 is_le
     let sHi := @Bool.rec (fun _ ↦ ℕ) sPHi sNHi is_le
     let nLo := @Bool.rec (fun _ ↦ ℕ) sN_15 sP_15 is_le
     let nHi := @Bool.rec (fun _ ↦ ℕ) sNHi sPHi is_le
     let ds := @Bool.rec (fun _ ↦ ℕ)
       (let a := Nat.sub (Nat.add gs_u nHi) sLo
        let b := Nat.sub sHi (Nat.add nLo gs_u)
        Nat.add a (Nat.sub b a))
       (let a := Nat.sub nHi (Nat.add sLo gs_u)
        let b := Nat.sub (Nat.add sHi gs_u) nLo
        Nat.add a (Nat.sub b a))
       neg_s'
     Nat.add dc ds) =
    gqsp_tayFinishEval c_val
      (Nat.mul t0 0x6f99461a1e9e1432dcb6000000000000000000)
      (Nat.mul (Nat.sub t1 t0) 0x6f99461a1e9e1432dcb6000000000000000000)
      neg_c neg_s cP_15 cN_15 sP_15 sN_15 := by
  unfold gqsp_tayFinishEval
  dsimp only
  cases neg_c <;> cases neg_s <;> cases Nat.ble c_val 0x20000000000 <;> rfl

theorem gqsp_zwGateUpper_eq (c_raw : ℕ) (g : DyadicRyGate) :
    gqsp_zwGateUpper c_raw g = gqsp_gateUpper c_raw g := by
  rcases g with ⟨t0, t1, neg_c, neg_s⟩
  unfold gqsp_zwGateUpper gqsp_gateUpper gqsp_gateUpperAux gqsp_tayRun15
  dsimp only
  rw [gqsp_applyNatCat_eq, gqsp_applyNatCat_eq]
  generalize Nat.land c_raw 0x3ffffffffff = c_val
  rw [gqsp_zwForce_eq, gqsp_zwCatRatNx_eq c_val]
  generalize gqsp_catRatNx c_val = nx
  rw [gqsp_zwForce_eq]
  have hp1 : Nat.shiftRight (Nat.mul 0x1000000000000000000000000 nx) 52 = gqsp_pLo_1 nx :=
    rfl; rw [hp1, gqsp_zwForce_eq]
  have hp2 : Nat.shiftRight (Nat.mul (gqsp_pLo_1 nx) nx) 52 = gqsp_pLo_2 nx :=
    rfl; rw [hp2, gqsp_zwForce_eq]
  have hp3 : Nat.shiftRight (Nat.mul (gqsp_pLo_2 nx) nx) 52 = gqsp_pLo_3 nx :=
    rfl; rw [hp3, gqsp_zwForce_eq]
  have hp4 : Nat.shiftRight (Nat.mul (gqsp_pLo_3 nx) nx) 52 = gqsp_pLo_4 nx :=
    rfl; rw [hp4, gqsp_zwForce_eq]
  have hp5 : Nat.shiftRight (Nat.mul (gqsp_pLo_4 nx) nx) 52 = gqsp_pLo_5 nx :=
    rfl; rw [hp5, gqsp_zwForce_eq]
  have hp6 : Nat.shiftRight (Nat.mul (gqsp_pLo_5 nx) nx) 52 = gqsp_pLo_6 nx :=
    rfl; rw [hp6, gqsp_zwForce_eq]
  have hp7 : Nat.shiftRight (Nat.mul (gqsp_pLo_6 nx) nx) 52 = gqsp_pLo_7 nx :=
    rfl; rw [hp7, gqsp_zwForce_eq]
  have hp8 : Nat.shiftRight (Nat.mul (gqsp_pLo_7 nx) nx) 52 = gqsp_pLo_8 nx :=
    rfl; rw [hp8, gqsp_zwForce_eq]
  have hp9 : Nat.shiftRight (Nat.mul (gqsp_pLo_8 nx) nx) 52 = gqsp_pLo_9 nx :=
    rfl; rw [hp9, gqsp_zwForce_eq]
  have hp10 : Nat.shiftRight (Nat.mul (gqsp_pLo_9 nx) nx) 52 = gqsp_pLo_10 nx :=
    rfl; rw [hp10, gqsp_zwForce_eq]
  have hp11 : Nat.shiftRight (Nat.mul (gqsp_pLo_10 nx) nx) 52 = gqsp_pLo_11 nx :=
    rfl; rw [hp11, gqsp_zwForce_eq]
  have hp12 : Nat.shiftRight (Nat.mul (gqsp_pLo_11 nx) nx) 52 = gqsp_pLo_12 nx :=
    rfl; rw [hp12, gqsp_zwForce_eq]
  have hp13 : Nat.shiftRight (Nat.mul (gqsp_pLo_12 nx) nx) 52 = gqsp_pLo_13 nx :=
    rfl; rw [hp13, gqsp_zwForce_eq]
  have hp14 : Nat.shiftRight (Nat.mul (gqsp_pLo_13 nx) nx) 52 = gqsp_pLo_14 nx :=
    rfl; rw [hp14, gqsp_zwForce_eq]
  have hp15 : Nat.shiftRight (Nat.mul (gqsp_pLo_14 nx) nx) 52 = gqsp_pLo_15 nx :=
    rfl; rw [hp15, gqsp_zwForce_eq]
  have hp16 : Nat.shiftRight (Nat.mul (gqsp_pLo_15 nx) nx) 52 = gqsp_pLo_16 nx :=
    rfl; rw [hp16, gqsp_zwForce_eq]
  have hp17 : Nat.shiftRight (Nat.mul (gqsp_pLo_16 nx) nx) 52 = gqsp_pLo_17 nx :=
    rfl; rw [hp17, gqsp_zwForce_eq]
  have hp18 : Nat.shiftRight (Nat.mul (gqsp_pLo_17 nx) nx) 52 = gqsp_pLo_18 nx :=
    rfl; rw [hp18, gqsp_zwForce_eq]
  have hp19 : Nat.shiftRight (Nat.mul (gqsp_pLo_18 nx) nx) 52 = gqsp_pLo_19 nx :=
    rfl; rw [hp19, gqsp_zwForce_eq]
  have hp20 : Nat.shiftRight (Nat.mul (gqsp_pLo_19 nx) nx) 52 = gqsp_pLo_20 nx :=
    rfl; rw [hp20, gqsp_zwForce_eq]
  have hp21 : Nat.shiftRight (Nat.mul (gqsp_pLo_20 nx) nx) 52 = gqsp_pLo_21 nx :=
    rfl; rw [hp21, gqsp_zwForce_eq]
  have hp22 : Nat.shiftRight (Nat.mul (gqsp_pLo_21 nx) nx) 52 = gqsp_pLo_22 nx :=
    rfl; rw [hp22, gqsp_zwForce_eq]
  have hp23 : Nat.shiftRight (Nat.mul (gqsp_pLo_22 nx) nx) 52 = gqsp_pLo_23 nx :=
    rfl; rw [hp23, gqsp_zwForce_eq]
  have hp24 : Nat.shiftRight (Nat.mul (gqsp_pLo_23 nx) nx) 52 = gqsp_pLo_24 nx :=
    rfl; rw [hp24, gqsp_zwForce_eq]
  have hp25 : Nat.shiftRight (Nat.mul (gqsp_pLo_24 nx) nx) 52 = gqsp_pLo_25 nx :=
    rfl; rw [hp25, gqsp_zwForce_eq]
  have hp26 : Nat.shiftRight (Nat.mul (gqsp_pLo_25 nx) nx) 52 = gqsp_pLo_26 nx :=
    rfl; rw [hp26, gqsp_zwForce_eq]
  have hp27 : Nat.shiftRight (Nat.mul (gqsp_pLo_26 nx) nx) 52 = gqsp_pLo_27 nx :=
    rfl; rw [hp27, gqsp_zwForce_eq]
  have hp28 : Nat.shiftRight (Nat.mul (gqsp_pLo_27 nx) nx) 52 = gqsp_pLo_28 nx :=
    rfl; rw [hp28, gqsp_zwForce_eq]
  have hp29 : Nat.shiftRight (Nat.mul (gqsp_pLo_28 nx) nx) 52 = gqsp_pLo_29 nx :=
    rfl; rw [hp29, gqsp_zwForce_eq]
  change @Nat.rec (fun _ ↦ ℕ) 0 (fun cP_15 _ ↦ @Nat.rec (fun _ ↦ ℕ) 0 (fun cN_15 _ ↦ @Nat.rec
    (fun _ ↦ ℕ) 0 (fun sP_15 _ ↦ @Nat.rec (fun _ ↦ ℕ) 0 (fun sN_15 _ ↦ _) (Nat.add 1
    (gqsp_sinN15 nx))) (Nat.add 1 (gqsp_sinP15 nx))) (Nat.add 1 (gqsp_cosN15 nx)))
    (Nat.add 1 (gqsp_cosP15 nx)) = _
  iterate 4 rw [gqsp_zwForce_eq]
  exact gqsp_zwFinishGate_eq c_val t0 t1 neg_c neg_s
    (gqsp_cosP15 nx) (gqsp_cosN15 nx) (gqsp_sinP15 nx) (gqsp_sinN15 nx)

noncomputable def gqsp_zwCatDropChunks (k0 : ℕ) (cs0 : List ℕ)
    (chs0 : List (List DyadicRyGate)) (acc0 : ℕ) : ℕ := @List.rec (List DyadicRyGate)
    (fun _ ↦ ℕ → List ℕ → ℕ → ℕ) (fun _ _ acc ↦ acc) (fun ch _ ih_chs k1 cs1 acc1 ↦ @List.rec
    DyadicRyGate (fun _ ↦ ℕ → List ℕ → ℕ → ℕ) (fun k cs acc ↦ ih_chs k cs acc) (fun g _ ih_g k
    cs acc ↦ @List.rec ℕ (fun _ ↦ ℕ) acc (fun c_raw cs' _ ↦ @Nat.rec (fun _ ↦ ℕ)
    (@DyadicRyGate.rec (fun _ ↦ ℕ) (fun t0_raw t1 neg_c neg_s ↦ @Nat.rec (fun _ ↦ ℕ) 0 (fun c
    _ ↦ @Nat.rec (fun _ ↦ ℕ) 0 (fun t0 _ ↦ @Nat.rec (fun _ ↦ ℕ) 0 (fun acc' _ ↦ ih_g 0 cs'
    acc') (Nat.add 1 (Nat.add acc (gqsp_zwGateUpper c ⟨t0, t1, neg_c, neg_s⟩)))) (Nat.add 1
    t0_raw)) (Nat.add 1 c_raw)) g) (fun k' _ ↦ ih_g k' cs' acc) k) cs) ch k1 cs1 acc1) chs0 k0
    cs0 acc0

private noncomputable def gqsp_aux_catDropList : List DyadicRyGate → ℕ → List ℕ → ℕ → ℕ
  | [], _, _, acc => acc
  | _ :: _, _, [], acc => acc
  | g :: gs, 0, c_raw :: cs, acc =>
      gqsp_aux_catDropList gs 0 cs (Nat.add acc (gqsp_gateUpper c_raw g))
  | _ :: gs, k + 1, _ :: cs, acc =>
      gqsp_aux_catDropList gs k cs acc

private theorem gqsp_aux_catDropList_zero :
    ∀ (gs : List DyadicRyGate) (cs : List ℕ) (acc : ℕ),
      gqsp_aux_catDropList gs 0 cs acc = gqsp_catUpperList cs gs acc
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | g :: gs, c_raw :: cs, acc => by
      dsimp only [gqsp_aux_catDropList, gqsp_catUpperList]
      rw [gqsp_forceLitCat_eq]
      exact gqsp_aux_catDropList_zero gs cs (Nat.add acc (gqsp_gateUpper c_raw g))

private theorem gqsp_zwCatDropChunks_eq :
    ∀ (chs : List (List DyadicRyGate)) (k : ℕ) (cs : List ℕ) (acc : ℕ),
      gqsp_zwCatDropChunks k cs chs acc = gqsp_aux_catDropList chs.flatten k cs acc := by
  unfold gqsp_zwCatDropChunks
  intro chs
  induction chs with
  | nil =>
      intro _ _ _
      rfl
  | cons ch chs ih =>
      intro k1 cs1 acc1
      rw [List.flatten_cons]
      dsimp only
      induction ch generalizing k1 cs1 acc1 with
      | nil => exact ih k1 cs1 acc1
      | cons g ch' ih_ch =>
          cases cs1 with
          | nil => rfl
          | cons c_raw cs' =>
              cases k1 with
              | zero =>
                  rcases g with ⟨t0_raw, t1, neg_c, neg_s⟩
                  dsimp only [List.cons_append, gqsp_aux_catDropList]
                  rw [gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwGateUpper_eq]
                  exact ih_ch 0 cs' _
              | succ k' =>
                  dsimp only [List.cons_append, gqsp_aux_catDropList]
                  exact ih_ch k' cs' acc1

noncomputable def gqsp_zwCatExactChunks (cs0 : List ℕ) (chs0 : List (List DyadicRyGate))
    (acc0 : ℕ) : Option ℕ := @List.rec (List DyadicRyGate) (fun _ ↦ List ℕ → ℕ → Option ℕ)
    (fun cs acc ↦ @List.rec ℕ (fun _ ↦ Option ℕ) (some acc) (fun _ _ _ ↦ none) cs) (fun ch _
    ih_chs cs1 acc1 ↦ @List.rec DyadicRyGate (fun _ ↦ List ℕ → ℕ → Option ℕ) (fun cs acc ↦
    ih_chs cs acc) (fun g _ ih_g cs acc ↦ @List.rec ℕ (fun _ ↦ Option ℕ) none (fun c_raw cs' _
    ↦ @DyadicRyGate.rec (fun _ ↦ Option ℕ) (fun t0_raw t1 neg_c neg_s ↦ @Nat.rec (fun _ ↦
    Option ℕ) none (fun c _ ↦ @Nat.rec (fun _ ↦ Option ℕ) none (fun t0 _ ↦ @Nat.rec (fun _ ↦
    Option ℕ) none (fun acc' _ ↦ ih_g cs' acc') (Nat.add 1 (Nat.add acc (gqsp_zwGateUpper c
    ⟨t0, t1, neg_c, neg_s⟩)))) (Nat.add 1 t0_raw)) (Nat.add 1 c_raw)) g) cs) ch cs1 acc1) chs0
    cs0 acc0

private theorem gqsp_catExact_append : ∀ (chs1 : List (List DyadicRyGate))
    (gs2 : List DyadicRyGate) (cs1 cs2 : List ℕ) (acc mid : ℕ), gqsp_zwCatExactChunks cs1
    chs1 acc = some mid → gqsp_catUpperList (cs1 ++ cs2) (chs1.flatten ++ gs2) acc =
    gqsp_catUpperList cs2 gs2 mid := by
  unfold gqsp_zwCatExactChunks
  intro chs1
  induction chs1 with
  | nil =>
      intro gs2 cs1 cs2 acc mid h
      cases cs1 with
      | nil =>
          cases h
          rfl
      | cons _ _ =>
          cases h
  | cons ch chs ih =>
      intro gs2 cs1 cs2 acc mid h
      rw [List.flatten_cons, List.append_assoc]
      dsimp only at h
      induction ch generalizing cs1 acc with
      | nil =>
          exact ih gs2 cs1 cs2 acc mid h
      | cons g ch' ih_ch =>
          cases cs1 with
          | nil =>
              cases h
          | cons c_raw cs' =>
              rcases g with ⟨t0_raw, t1, neg_c, neg_s⟩
              dsimp only at h
              dsimp only [List.cons_append, gqsp_catUpperList]
              rw [gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwGateUpper_eq] at h
              rw [gqsp_forceLitCat_eq]
              exact ih_ch cs' _ h

theorem gqsp_ry_chs_split_flatten (g0 : DyadicRyGate)
    (s0 s1 s2 s3 s4 s5 s6 s7 : List (List DyadicRyGate)) :
    ([g0] :: [s0, s1, s2, s3, s4, s5, s6, s7].flatten).flatten =
      ([g0] :: [s0, s1, s2, s3].flatten).flatten ++ ([s4, s5, s6, s7].flatten).flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.flatten_append, List.nil_append,
    List.append_nil, List.append_assoc, List.cons_append]

theorem gqsp_catUpperMemoChunks_ble_of_exact_split (mid ana_u cap_u : ℕ) (cs1 cs2 : List ℕ)
    (chs1 chs2 chs_all : List (List DyadicRyGate))
    (hchs : chs_all.flatten = chs1.flatten ++ chs2.flatten)
    (h1 : gqsp_zwCatExactChunks cs1 chs1 0 = some mid) (h2 : Nat.ble (Nat.add
    (gqsp_zwCatDropChunks 0 cs2 chs2 mid) ana_u) cap_u = true) : Nat.ble
    (Nat.add (gqsp_catUpperMemoChunks (cs1 ++ cs2) chs_all 0) ana_u) cap_u = true := by
  rw [gqsp_catUpperMemoChunks_eq, hchs, gqsp_catExact_append chs1 chs2.flatten cs1 cs2 0 mid h1,
      ← gqsp_aux_catDropList_zero chs2.flatten cs2 mid,
      ← gqsp_zwCatDropChunks_eq chs2 0 cs2 mid]
  exact h2

theorem gqsp_catUpperMemoChunks_ble_of_ry_chs_split (mid ana_u cap_u : ℕ)
    (cs_all cs1 cs2 : List ℕ) (g0 : DyadicRyGate)
    (ry_all s0 s1 s2 s3 s4 s5 s6 s7 : List (List DyadicRyGate)) (hcs : cs_all = cs1 ++ cs2)
    (hry : ry_all = [s0, s1, s2, s3, s4, s5, s6, s7].flatten) (h1 : gqsp_zwCatExactChunks cs1
    ([g0] :: [s0, s1, s2, s3].flatten) 0 = some mid) (h2 : Nat.ble (Nat.add
    (gqsp_zwCatDropChunks 0 cs2 [s4, s5, s6, s7].flatten mid) ana_u) cap_u = true) : Nat.ble
    (Nat.add (gqsp_catUpperMemoChunks cs_all ([g0] :: ry_all) 0) ana_u) cap_u = true := by
  subst hcs
  subst hry
  exact gqsp_catUpperMemoChunks_ble_of_exact_split mid ana_u cap_u cs1 cs2
    ([g0] :: [s0, s1, s2, s3].flatten) ([s4, s5, s6, s7].flatten)
    ([g0] :: [s0, s1, s2, s3, s4, s5, s6, s7].flatten)
    (gqsp_ry_chs_split_flatten g0 s0 s1 s2 s3 s4 s5 s6 s7) h1 h2

private noncomputable def revNat8 (fuel : ℕ) : List ℕ → List ℕ → List ℕ := @Nat.rec
    (fun _ ↦ List ℕ → List ℕ → List ℕ) gqsp_zwRevNatTR (fun _ ih xs acc ↦ @List.rec ℕ (fun _
    ↦ List ℕ) acc (fun x0 r1 _ ↦ @List.rec ℕ (fun _ ↦ List ℕ) (x0 :: acc) (fun x1 r2 _ ↦
    @List.rec ℕ (fun _ ↦ List ℕ) (x1 :: x0 :: acc) (fun x2 r3 _ ↦ @List.rec ℕ (fun _ ↦ List ℕ)
    (x2 :: x1 :: x0 :: acc) (fun x3 r4 _ ↦ @List.rec ℕ (fun _ ↦ List ℕ) (x3 :: x2 :: x1 :: x0
    :: acc) (fun x4 r5 _ ↦ @List.rec ℕ (fun _ ↦ List ℕ) (x4 :: x3 :: x2 :: x1 :: x0 :: acc)
    (fun x5 r6 _ ↦ @List.rec ℕ (fun _ ↦ List ℕ) (x5 :: x4 :: x3 :: x2 :: x1 :: x0 :: acc) (fun
    x6 r7 _ ↦ @List.rec ℕ (fun _ ↦ List ℕ) (x6 :: x5 :: x4 :: x3 :: x2 :: x1 :: x0 :: acc)
    (fun x7 r8 _ ↦ ih r8 (x7 :: x6 :: x5 :: x4 :: x3 :: x2 :: x1 :: x0 :: acc)) r7) r6) r5)
    r4) r3) r2) r1) xs) fuel

private theorem revNat8_eq :
    ∀ (fuel : ℕ) (xs acc : List ℕ), revNat8 fuel xs acc = gqsp_zwRevNatTR xs acc
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | _ + 1, [_], _ => rfl
  | _ + 1, [_, _], _ => rfl
  | _ + 1, [_, _, _], _ => rfl
  | _ + 1, [_, _, _, _], _ => rfl
  | _ + 1, [_, _, _, _, _], _ => rfl
  | _ + 1, [_, _, _, _, _, _], _ => rfl
  | _ + 1, [_, _, _, _, _, _, _], _ => rfl
  | fuel + 1, x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: r8, acc =>
      revNat8_eq fuel r8 (x7 :: x6 :: x5 :: x4 :: x3 :: x2 :: x1 :: x0 :: acc)

private theorem zwStrictRevNatTR_cons (x : ℕ) (xs acc : List ℕ) :
    gqsp_zwStrictRevNatTR (x :: xs) acc = gqsp_zwStrictRevNatTR xs (x :: acc) := by
  dsimp only [gqsp_zwStrictRevNatTR]
  rw [gqsp_zwForce_eq]

private noncomputable def strictRev8 (fuel : ℕ) : List ℕ → List ℕ → List ℕ :=
  @Nat.rec (fun _ ↦ List ℕ → List ℕ → List ℕ)
    gqsp_zwStrictRevNatTR
    (fun _ ih xs acc ↦
      let fb := gqsp_zwStrictRevNatTR xs acc
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun x0 r1 _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun x1 r2 _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun x2 r3 _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun x3 r4 _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun x4 r5 _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun x5 r6 _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun x6 r7 _ ↦
      @List.rec ℕ (fun _ ↦ List ℕ) fb (fun x7 r8 _ ↦
        @Nat.rec (fun _ ↦ List ℕ) [] (fun x0' _ ↦
        @Nat.rec (fun _ ↦ List ℕ) [] (fun x1' _ ↦
        @Nat.rec (fun _ ↦ List ℕ) [] (fun x2' _ ↦
        @Nat.rec (fun _ ↦ List ℕ) [] (fun x3' _ ↦
        @Nat.rec (fun _ ↦ List ℕ) [] (fun x4' _ ↦
        @Nat.rec (fun _ ↦ List ℕ) [] (fun x5' _ ↦
        @Nat.rec (fun _ ↦ List ℕ) [] (fun x6' _ ↦
        @Nat.rec (fun _ ↦ List ℕ) [] (fun x7' _ ↦
          ih r8 (x7' :: x6' :: x5' :: x4' :: x3' :: x2' :: x1' :: x0' :: acc))
          (Nat.add 1 x7)) (Nat.add 1 x6)) (Nat.add 1 x5)) (Nat.add 1 x4))
          (Nat.add 1 x3)) (Nat.add 1 x2)) (Nat.add 1 x1)) (Nat.add 1 x0))
        r7) r6) r5) r4) r3) r2) r1) xs)
    fuel

private theorem strictRev8_eq :
    ∀ (fuel : ℕ) (xs acc : List ℕ), strictRev8 fuel xs acc = gqsp_zwStrictRevNatTR xs acc :=
      by
  intro fuel
  induction fuel with
  | zero => intro _ _; rfl
  | succ fuel ih =>
      intro xs acc
      unfold strictRev8
      dsimp only
      rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, _ | ⟨x7,
        r8⟩⟩⟩⟩⟩⟩⟩⟩ <;> try rfl
      dsimp only
      rw [gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwForce_eq,
          gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwForce_eq]
      change strictRev8 fuel r8 _ = _
      rw[ih, zwStrictRevNatTR_cons, zwStrictRevNatTR_cons,
          zwStrictRevNatTR_cons, zwStrictRevNatTR_cons, zwStrictRevNatTR_cons,
          zwStrictRevNatTR_cons, zwStrictRevNatTR_cons, zwStrictRevNatTR_cons]

private noncomputable def withStrictList8 {α : Type} (fuel : ℕ) (xs : List ℕ) (k : List ℕ →
    α) : α :=
  gqsp_tf_shareHeadList (revNat8 fuel (strictRev8 fuel xs []) []) k

private theorem withStrictList8_eq {α : Type} (fuel : ℕ) (xs : List ℕ) (k : List ℕ → α) :
    withStrictList8 fuel xs k = k xs := by
  unfold withStrictList8
  rw [gqsp_tf_shareHeadList_eq, revNat8_eq, strictRev8_eq]
  change k (gqsp_zwStrictNatList xs) = k xs
  rw [gqsp_zwStrictNatList_eq]

private theorem aux_b135598_m135867_upper_t1_ok_fast : withStrictList8 6000 gqsp_ws_c0
    (fun wc0 ↦ withStrictList8 6000 gqsp_ws_c1 (fun wc1 ↦ withStrictList8 6000
    gqsp_ws_c2 (fun wc2 ↦ gqsp_upperRealTreePostT1Ble 18 20 135867 21741172396
    gqsp_b135598_k409600_W_err_d0 gqsp_b135598_k409600_W_err_dpos 272802
    b135598_m135867_ry_g0 [b135598_m135867_shard_0_node, b135598_m135867_shard_1_node,
    b135598_m135867_shard_2_node, b135598_m135867_shard_3_node, b135598_m135867_shard_4_node,
    b135598_m135867_shard_5_node, b135598_m135867_shard_6_node, b135598_m135867_shard_7_node]
    (wc0 ++ (wc1 ++ wc2))))) = true := by
  decide +kernel

theorem aux_b135598_m135867_upper_t1_ok : gqsp_upperRealTreePostT1LowMem2Ble 18 20 135867
    21741172396 gqsp_b135598_k409600_W_err_d0 gqsp_b135598_k409600_W_err_dpos 272802
    b135598_m135867_ry_g0 [b135598_m135867_shard_0_node, b135598_m135867_shard_1_node,
    b135598_m135867_shard_2_node, b135598_m135867_shard_3_node, b135598_m135867_shard_4_node,
    b135598_m135867_shard_5_node, b135598_m135867_shard_6_node, b135598_m135867_shard_7_node]
    gqsp_b135598_k409600_ws_unpad = true := by
  have h := aux_b135598_m135867_upper_t1_ok_fast
  rw [withStrictList8_eq] at h
  rw [withStrictList8_eq] at h
  rw [withStrictList8_eq] at h
  change gqsp_upperRealTreePostT1Ble 18 20 135867 21741172396 gqsp_b135598_k409600_W_err_d0
    gqsp_b135598_k409600_W_err_dpos 272802 b135598_m135867_ry_g0
    [b135598_m135867_shard_0_node, b135598_m135867_shard_1_node, b135598_m135867_shard_2_node,
    b135598_m135867_shard_3_node, b135598_m135867_shard_4_node, b135598_m135867_shard_5_node,
    b135598_m135867_shard_6_node, b135598_m135867_shard_7_node] gqsp_b135598_k409600_ws_unpad
    = true at h
  rw [← gqsp_upperRealTreePostT1Ble_eq]
  exact h

theorem gqsp_b135598_m135867_upper_post_ok :
    gqsp_upperRealTreePostChunks2Ble 18 20 135867 27342870269
      gqsp_b135598_k409600_W_err_d0 gqsp_b135598_k409600_W_err_dpos 272802
      b135598_m135867_ry_g0 [b135598_m135867_shard_0_node, b135598_m135867_shard_1_node,
        b135598_m135867_shard_2_node, b135598_m135867_shard_3_node,
       b135598_m135867_shard_4_node, b135598_m135867_shard_5_node, b135598_m135867_shard_6_node,
         b135598_m135867_shard_7_node] gqsp_b135598_k409600_ws_unpad = true :=
  gqsp_upperRealTreePostChunks2Ble_of_split 18 20 135867 21741172396 5601697873 27342870269
    gqsp_b135598_k409600_W_err_d0 gqsp_b135598_k409600_W_err_dpos 272802
    b135598_m135867_ry_g0 [b135598_m135867_shard_0_node, b135598_m135867_shard_1_node,
      b135598_m135867_shard_2_node, b135598_m135867_shard_3_node,
       b135598_m135867_shard_4_node, b135598_m135867_shard_5_node, b135598_m135867_shard_6_node,
         b135598_m135867_shard_7_node] gqsp_b135598_k409600_ws_unpad
    (by decide) aux_b135598_m135867_upper_t1_ok gqsp_b135598_m135867_upper_t23_ok

end UpperPost135598
end GqspUpperPost135598
end QuantumComputation.Specs.StoppingPowerSolution
end
