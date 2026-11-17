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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.BiGqspZeroCacheB
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.SpectatorSum217

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section GqspWronskianUV135598

section
set_option compiler.extract_closed false
namespace GqspWronskianUV135598
section WronskianUV135598
set_option maxRecDepth 4000000
set_option exponentiation.threshold 500000
open GqspWronskian62592 (StrictListBind gqsp_zwMillerDownU
    gqsp_zwMillerDownV gqsp_zwLenEq gqsp_zwGetD gqsp_zwDrop gqsp_zwMaxMagLoop
    gqsp_zwMillerResLoop gqsp_zwEvenTailPosNeg gqsp_zwDoubleGeBle)
def gqsp_b135598_k409600_cheb_scale0 : ℕ := 0x1000000000000000000000000000000000000
def gqsp_b135598_k409600_cheb_Bw : ℕ := 0x1000000000000000000000000000000000000000000000000
def gqsp_b135598_k409600_cheb_Bw2 : ℕ := 0x2000000000000000000000000000000000000000000000000
def gqsp_b135598_k409600_cheb_Bw_hi : ℕ :=
    0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def gqsp_b135598_k409600_cheb_Bw2_hi : ℕ :=
    0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def gqsp_b135598_k409600_cheb_Bw_plus_s0 : ℕ := 0x1000000000001000000000000000000000000000000000000
def gqsp_b135598_k409600_j_top_hi : ℕ :=
    0x1000000000000000000000000000000000000000000000000000045aa1f039d4b187277180ffef3d7053b
def gqsp_b135598_k409600_j_top1_hi : ℕ :=
    0x100000000000000000000000000000000000000000000000000003cfa62c2b950c9c60d73819fe0df189f
def gqsp_b135598_k409600_u_beta_off : ℕ := 0x23a9aa2139bfc3216c4da65f9abaefb8823
def gqsp_b135598_k409600_W_err_d0 : ℕ := 0x200000000000000000000000
def gqsp_b135598_k409600_W_err_dpos : ℕ := 0x400000000000000000000000
noncomputable def gqsp_zwMillerDownURange (β_nat Bw_hi Bw2_hi Bw d_off steps : ℕ) :
    ℕ → ℕ → List ℕ → List ℕ :=
  @Nat.rec (fun _ ↦ ℕ → ℕ → List ℕ → List ℕ)
    (fun j0 _ acc ↦
      let u0 := @Bool.rec (fun _ ↦ ℕ) (Nat.add Bw (Nat.shiftRight (Nat.sub j0 Bw_hi) 144))
          (Nat.sub Bw (Nat.shiftRight (Nat.sub Bw_hi j0) 144)) (Nat.ble (Nat.add j0 1) Bw_hi)
      @Nat.rec (fun _ ↦ List ℕ) [] (fun u0' _ ↦ u0' :: acc) (Nat.add 1 u0))
    (fun d ih jd jd1 acc ↦
      let d1 := Nat.add d (Nat.add d_off 1)
      let jprev0 := @Bool.rec (fun _ ↦ ℕ) (Nat.sub (Nat.add Bw2_hi (Nat.div (Nat.mul (Nat.mul
          2 d1) (Nat.sub jd Bw_hi)) β_nat)) jd1) (Nat.sub (Nat.sub Bw2_hi (Nat.div (Nat.mul
          (Nat.mul 2 d1) (Nat.sub Bw_hi jd)) β_nat)) jd1) (Nat.ble (Nat.add jd 1) Bw_hi)
      let ud0 := @Bool.rec (fun _ ↦ ℕ) (Nat.add Bw (Nat.shiftRight (Nat.sub jd Bw_hi) 144))
          (Nat.sub Bw (Nat.shiftRight (Nat.sub Bw_hi jd) 144)) (Nat.ble (Nat.add jd 1) Bw_hi)
      @Nat.rec (fun _ ↦ List ℕ) [] (fun jprev _ ↦
        @Nat.rec (fun _ ↦ List ℕ) [] (fun ud _ ↦ ih jprev jd (ud :: acc)) (Nat.add 1 ud0))
        (Nat.add 1 jprev0))
    steps
noncomputable def gqsp_zwMillerDownVRange (β_nat Bw Bw2 d_off steps : ℕ) :
    ℕ → ℕ → List ℕ → List ℕ :=
  @Nat.rec (fun _ ↦ ℕ → ℕ → List ℕ → List ℕ)
    (fun j0 _ acc ↦ @Nat.rec (fun _ ↦ List ℕ) [] (fun v0 _ ↦ v0 :: acc) (Nat.add 1 j0))
    (fun d ih jd jd1 acc ↦
      let d1 := Nat.add d (Nat.add d_off 1)
      let jprev0 := @Bool.rec (fun _ ↦ ℕ) (Nat.sub (Nat.add Bw2 (Nat.div (Nat.mul (Nat.mul 2
          d1) (Nat.sub jd Bw)) β_nat)) jd1) (Nat.sub (Nat.sub Bw2 (Nat.div (Nat.mul (Nat.mul 2
          d1) (Nat.sub Bw jd)) β_nat)) jd1) (Nat.ble (Nat.add jd 1) Bw)
      @Nat.rec (fun _ ↦ List ℕ) [] (fun jprev _ ↦
        @Nat.rec (fun _ ↦ List ℕ) [] (fun vd _ ↦ ih jprev jd (vd :: acc)) (Nat.add 1 jd))
        (Nat.add 1 jprev0))
    steps
/-- Chunk 0 (`0..45200`, `45,201` items) of biased `u` at `β = 135,598, K = 409,600`. -/
noncomputable def gqsp_u_c0 : List ℕ :=
  gqsp_zwMillerDownU 135598 gqsp_b135598_k409600_cheb_Bw_hi gqsp_b135598_k409600_cheb_Bw2_hi
    gqsp_b135598_k409600_cheb_Bw 45200
    0xffffffffffffff76da6c6b1950731cd0502a2c75d2c923d18cfb62637adacb1d6aa4c4a1adfc72ab74d6
    0x10000000000000002284acd01d69fa82dc7c1f170e6acd1a18622b54409861fc4daf008d9f760b49a6994 []
/-- Chunk 1 (`45201..90400`, `45,200` items) of biased `u` at `β = 135,598, K = 409,600`. -/
noncomputable def gqsp_u_c1 : List ℕ :=
  gqsp_zwMillerDownURange 135598 gqsp_b135598_k409600_cheb_Bw_hi gqsp_b135598_k409600_cheb_Bw2_hi
    gqsp_b135598_k409600_cheb_Bw 45201 45199
    0xffffffffffffff5ba18aa3b6554166f404dd0b448b92515da6048d91eed61a9ae8ce2dacce9f05afe162
    0xffffffffffffff8de83a057ecf5f01bbfd41fac787b3736f54f765c0404730e1eb6717f7c6625930f3c3 []
/-- Chunk 2 (`90401..136798`, `46,398` items) of biased `u` at `β = 135,598, K = 409,600`. -/
noncomputable def gqsp_u_c2 : List ℕ :=
  gqsp_zwMillerDownURange 135598 gqsp_b135598_k409600_cheb_Bw_hi gqsp_b135598_k409600_cheb_Bw2_hi
    gqsp_b135598_k409600_cheb_Bw 90401 46397
    gqsp_b135598_k409600_j_top_hi gqsp_b135598_k409600_j_top1_hi []
/-- Full `136,799`-entry biased inhomogeneous Miller sequence `u` (`3` chunks `≤ 46,398`). -/
noncomputable def gqsp_b135598_k409600_u_biased : List ℕ :=
  gqsp_u_c0 ++ (gqsp_u_c1 ++ gqsp_u_c2)
/-- Chunk 0 (`0..45200`, `45,201` items) of biased `v` at `β = 135,598`. -/
noncomputable def gqsp_v_c0 : List ℕ :=
  gqsp_zwMillerDownV 135598 gqsp_b135598_k409600_cheb_Bw gqsp_b135598_k409600_cheb_Bw2 45200
    0x100000000000548f80ad384b60358982b136db49d97f5ac6f
    0xfffffffffffbc19ebb0e2b52f81b1fb42e6e7c61562915f2 []
/-- Chunk 1 (`45201..90400`, `45,200` items) of biased `v` at `β = 135,598`. -/
noncomputable def gqsp_v_c1 : List ℕ :=
  gqsp_zwMillerDownVRange 135598 gqsp_b135598_k409600_cheb_Bw gqsp_b135598_k409600_cheb_Bw2 45201
    45199 0x10000000000083a389e2392c37a424e905d45e6ca98a68cd0
    0x10000000000023d48cf31f0d5447ddf6ced906aebbe67da6d []
/-- Chunk 2 (`90401..135599`, `45,199` items) of biased `v` at `β = 135,598`. -/
noncomputable def gqsp_v_c2 : List ℕ :=
  gqsp_zwMillerDownVRange 135598 gqsp_b135598_k409600_cheb_Bw gqsp_b135598_k409600_cheb_Bw2 90401
    45197 gqsp_b135598_k409600_cheb_Bw gqsp_b135598_k409600_cheb_Bw_plus_s0
    [gqsp_b135598_k409600_cheb_Bw_plus_s0]
/-- Full `135,600`-entry biased homogeneous Bessel sequence `v` (`3` chunks `≤ 45,201`). -/
noncomputable def gqsp_b135598_k409600_v_biased : List ℕ :=
  gqsp_v_c0 ++ (gqsp_v_c1 ++ gqsp_v_c2)
noncomputable def gqsp_uC0Checks (c0 : List ℕ) : Bool :=
  gqsp_zwLenEq 45201 c0 0 &&
  Nat.beq (gqsp_zwGetD gqsp_b135598_k409600_cheb_Bw 0 c0)
    6277101735386680811119783831958774888695941699086909615866 &&
  Nat.beq (gqsp_zwGetD gqsp_b135598_k409600_cheb_Bw 45199 c0)
    6277101735386680731988786961672437354510355985583955838516 &&
  Nat.beq (gqsp_zwGetD gqsp_b135598_k409600_cheb_Bw 45200 c0)
    6277101735386680717167157431483421496742838707710520271826 &&
  Nat.ble (gqsp_zwMaxMagLoop gqsp_b135598_k409600_cheb_Bw c0 0)
    292946331321408785259096771508397088968859 &&
  Nat.beq (gqsp_zwMillerResLoop 135598 gqsp_b135598_k409600_cheb_Bw 45199 1 c0 0) 2553018200 &&
  (let pn := gqsp_zwEvenTailPosNeg gqsp_b135598_k409600_cheb_Bw 22600 (gqsp_zwDrop 1 c0) 0 0
   Nat.beq pn.1 704684483198167131608844494039641956536227664 && Nat.beq pn.2
     704784545188476977559764696730107320389304484) &&
  gqsp_zwDoubleGeBle gqsp_b135598_k409600_cheb_Bw (gqsp_zwDrop 1 c0)
noncomputable def gqsp_uC1Checks (c1 : List ℕ) : Bool :=
  gqsp_zwLenEq 45200 c1 0 &&
  Nat.beq (gqsp_zwGetD gqsp_b135598_k409600_cheb_Bw 45198 c1)
    6277101735386680728082659535261138800208213290465823079480 &&
  Nat.beq (gqsp_zwGetD gqsp_b135598_k409600_cheb_Bw 45199 c1)
    6277101735386680707903924446019345471410010446009742807390 &&
  Nat.ble (gqsp_zwMaxMagLoop gqsp_b135598_k409600_cheb_Bw c1 0)
    292946331321408785259096771508397088968859 &&
  Nat.beq (gqsp_zwMillerResLoop 135598 gqsp_b135598_k409600_cheb_Bw 45200 45200
    (6277101735386680731988786961672437354510355985583955838516 ::
    6277101735386680717167157431483421496742838707710520271826 :: c1) 0) 3542840924 &&
  (let pn := gqsp_zwEvenTailPosNeg gqsp_b135598_k409600_cheb_Bw 22600 c1 0 0
   Nat.beq pn.1 751732118376361498410898107102235033816887008 && Nat.beq pn.2
     751733431560733410195512754821896863526155994) &&
  gqsp_zwDoubleGeBle gqsp_b135598_k409600_cheb_Bw c1
noncomputable def gqsp_uC2Checks (c2 : List ℕ) : Bool :=
  gqsp_zwLenEq 46398 c2 0 &&
  Nat.beq (gqsp_zwGetD gqsp_b135598_k409600_cheb_Bw 46397 c2) gqsp_b135598_k409600_cheb_Bw &&
  Nat.beq (gqsp_zwGetD gqsp_b135598_k409600_cheb_Bw 45197 c2) (Nat.add
    gqsp_b135598_k409600_cheb_Bw gqsp_b135598_k409600_u_beta_off) &&
  Nat.ble (gqsp_zwMaxMagLoop gqsp_b135598_k409600_cheb_Bw c2 0)
    292946331321408785259096771508397088968859 &&
  Nat.beq (gqsp_zwMillerResLoop 135598 gqsp_b135598_k409600_cheb_Bw 45199 90400
    (6277101735386680728082659535261138800208213290465823079480 ::
    6277101735386680707903924446019345471410010446009742807390 :: c2) 0) 3986439504 &&
  Nat.beq (gqsp_zwMillerResLoop 135598 gqsp_b135598_k409600_cheb_Bw 1200 135599 (gqsp_zwDrop
    45197 c2) 0) 90192196 &&
  (let pn := gqsp_zwEvenTailPosNeg gqsp_b135598_k409600_cheb_Bw 23199 c2 0 0
   Nat.beq pn.1 1059902298516973368640052749423976382690852620 && Nat.beq pn.2
     1037547462138169738871454774327455450500971088) &&
  gqsp_zwDoubleGeBle gqsp_b135598_k409600_cheb_Bw c2
set_option maxHeartbeats 4800000 in
-- kernel Wronskian chunk u verification
theorem gqsp_uC0Bundle : StrictListBind gqsp_u_c0 gqsp_uC0Checks = true := by decide +kernel
set_option maxHeartbeats 4800000 in
-- kernel Wronskian chunk u verification
theorem gqsp_uC1Bundle : StrictListBind gqsp_u_c1 gqsp_uC1Checks = true := by decide +kernel
set_option maxHeartbeats 4800000 in
-- kernel Wronskian chunk u verification
theorem gqsp_uC2Bundle : StrictListBind gqsp_u_c2 gqsp_uC2Checks = true := by decide +kernel
end WronskianUV135598
end GqspWronskianUV135598
end
end GqspWronskianUV135598

end QuantumComputation.Specs.StoppingPowerSolution
end
