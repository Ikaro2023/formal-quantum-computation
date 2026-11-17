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

public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHiBase

/-
# Low-`m` High-`r` Krotov Trajectory Part `8` (`FindAllJohnsonRampKickMuxLowHiT8`)

Certifies multi-segment sawtooth `rkmEvalT16Lo12` trajectories for
`(m, r) ∈ {(16, 384), (32, 384)}`.
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Sign-kick mask segment `0` for `(m = 16, r = 384)`. -/
def rkmMkPack_m16_r384_s0 : List Bool :=
  [true, false, false, true, true, false, false, true, true, false, false, true, false, false,
    true]
/-- Sign-kick mask segment `1` for `(m = 16, r = 384)`. -/
def rkmMkPack_m16_r384_s1 : List Bool :=
  [false, false, false, false, false, true, false, false, false, true, true, true, false,
    false, true]
/-- Sign-kick mask segment `2` for `(m = 16, r = 384)`. -/
def rkmMkPack_m16_r384_s2 : List Bool :=
  [true, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, true, false, false, false, true, false, false,
    false, false, false, false, false, false, false, false, false, true, false, false, false,
    false, false, false, false, true, false, false, false, true, false, false, false, true]
/-- Sign-kick mask segment `3` for `(m = 16, r = 384)`. -/
def rkmMkPack_m16_r384_s3 : List Bool :=
  [true, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, true, false,
    false, false, false, false, false, false, true, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, true, false, false, false, false, false, false, false, true]
/-- Sign-kick mask segment `4` for `(m = 16, r = 384)`. -/
def rkmMkPack_m16_r384_s4 : List Bool :=
  [false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, true, false, false, false, false, false, false,
    false, true, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, true]
/-- Sign-kick mask segment `5` for `(m = 16, r = 384)`. -/
def rkmMkPack_m16_r384_s5 : List Bool :=
  [false, false, false, false, false, false, false, false, true, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, true, false, false, false,
    false, false, false, false, true, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, true]
/-- Sign-kick mask segment `6` for `(m = 16, r = 384)`. -/
def rkmMkPack_m16_r384_s6 : List Bool :=
  [true, false, false, false, false, false, false, false, true, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, true, false, false, false, false, false,
    false, false, true, false, false, false, false, false, false, false, true, false, false,
    false, false, false, false, false, true, false, false, false, false, false, false, false,
    true, false, false, false, false, false, false, false, true, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, true]
/-- Multi-segment sign-kick masks for `(m = 16, r = 384)`. -/
def rkmMasksPack_m16_r384 : List (List Bool) :=
  [rkmMkPack_m16_r384_s0, rkmMkPack_m16_r384_s1, rkmMkPack_m16_r384_s2, rkmMkPack_m16_r384_s3,
    rkmMkPack_m16_r384_s4, rkmMkPack_m16_r384_s5, rkmMkPack_m16_r384_s6, []]
/-- Hit-row chunk `0` for `(m = 16, r = 384)`. -/
def rkmRowPack_m16_r384_p0 : List ℕ :=
  [77749643, 1552126, 84653, 16985074, 220719025, 66913996, 33044339, 4465310, 48576061,
    693515, 85818188, 5330045, 32878374, 17354157, 18282996, 4905972, 8066535, 3192691,
    10857337, 93, 356747, 22113259, 2602005, 45120960, 72297383, 3812998, 84219612, 4079,
    430197, 19877669, 419946634, 16670043]
/-- Hit-row chunk `1` for `(m = 16, r = 384)`. -/
def rkmRowPack_m16_r384_p1 : List ℕ :=
  [3432789, 57446208, 25859670, 146637343, 12746889, 77435531, 33399, 5692760, 13306357, 23129,
    12771088, 11005506, 10817013, 8656321, 30657388, 2354535, 158853491, 376894, 171001945,
    1839912, 93278594, 77054299, 206509826, 213109881, 647024, 1404386, 283411271, 246822354,
    13603523, 74462784, 349078705, 133670483]
/-- Hit-row chunk `2` for `(m = 16, r = 384)`. -/
def rkmRowPack_m16_r384_p2 : List ℕ :=
  [1251315, 12464903, 23918814, 32231973, 186755182, 92597263, 42788069, 191518618, 481542315,
    477021151, 320257094, 218259619, 85332704, 31405, 44288386, 65592566, 68306909, 124262211,
    235960614, 302566151, 221210021, 44175117, 28251719, 200956340, 184311692, 35111049,
    1231300, 22768195, 119926105, 85920024, 4867977, 210205255]
/-- Hit-row chunk `3` for `(m = 16, r = 384)`. -/
def rkmRowPack_m16_r384_p3 : List ℕ :=
  [331291908, 189013118, 94289217, 150323119, 339570176, 399605296, 157183068, 114333,
    124244509, 243808536, 249081949, 300291143, 616327048, 1543403924, 3496514283, 6824836913,
    11934156431, 19431818804, 29906151658, 43360663657, 58752231369, 74130635508, 87354029229,
    96770650939, 101364072803, 100513035927, 93899077498, 81828908680, 65676279399,
    47878535994, 31243393746, 17941117687]
/-- Hit-row chunk `4` for `(m = 16, r = 384)`. -/
def rkmRowPack_m16_r384_p4 : List ℕ :=
  [8846426064, 3582153275, 1074117866, 168611653, 88313, 69850533, 158627397, 203385357,
    205657718, 182924924, 150153405, 116228460, 85448995, 59592764, 39211342, 24177372,
    13878822, 7373895, 3603706, 1604616, 638316, 216650, 55511, 6774, 250, 5591, 11198, 13762,
    13357, 11149, 8322, 5679]
/-- Hit-row chunk `5` for `(m = 16, r = 384)`. -/
def rkmRowPack_m16_r384_p5 : List ℕ :=
  [3595, 2134, 1197, 638, 325, 159, 74, 33, 14, 5, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0]
/-- Hit-row chunk `6` for `(m = 16, r = 384)`. -/
def rkmRowPack_m16_r384_p6 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0]
/-- Hit-row chunk `7` for `(m = 16, r = 384)`. -/
def rkmRowPack_m16_r384_p7 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0]
/-- Hit-row chunk `8` for `(m = 16, r = 384)`. -/
def rkmRowPack_m16_r384_p8 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0]
/-- Hit-row chunk `9` for `(m = 16, r = 384)`. -/
def rkmRowPack_m16_r384_p9 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0]
/-- Hit-row chunk `10` for `(m = 16, r = 384)`. -/
def rkmRowPack_m16_r384_p10 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0]
/-- Hit-row chunk `11` for `(m = 16, r = 384)`. -/
def rkmRowPack_m16_r384_p11 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0]
/-- Certified `10 ^ 12`-scaled hit row for `(m = 16, r = 384)`. -/
def rkmRowPack_m16_r384 : List ℕ :=
  rkmRowPack_m16_r384_p0 ++ rkmRowPack_m16_r384_p1 ++ rkmRowPack_m16_r384_p2
    ++ rkmRowPack_m16_r384_p3 ++ rkmRowPack_m16_r384_p4 ++ rkmRowPack_m16_r384_p5
    ++ rkmRowPack_m16_r384_p6 ++ rkmRowPack_m16_r384_p7 ++ rkmRowPack_m16_r384_p8
    ++ rkmRowPack_m16_r384_p9 ++ rkmRowPack_m16_r384_p10 ++ rkmRowPack_m16_r384_p11

/-- Sign-kick mask segment `0` for `(m = 32, r = 384)`. -/
def rkmMkPack_m32_r384_s0 : List Bool :=
  [false, false, false, false, false, true, false, true, false, true, false, false, true,
    false, false, false, true, false, false, true, false, false, true, true]
/-- Sign-kick mask segment `1` for `(m = 32, r = 384)`. -/
def rkmMkPack_m32_r384_s1 : List Bool :=
  [false, false, false, false, false, false, false, false, true, false, false, true, true,
    true, false, false, true, true, false, true, false, false, true, true, true]
/-- Sign-kick mask segment `2` for `(m = 32, r = 384)`. -/
def rkmMkPack_m32_r384_s2 : List Bool :=
  [false, true, false, false, false, false, false, false, false, false, false, false, true,
    true, true, true, true, true, true, false, false, true, false, false, true, true, true,
    true, true, false, true, true]
/-- Sign-kick mask segment `3` for `(m = 32, r = 384)`. -/
def rkmMkPack_m32_r384_s3 : List Bool :=
  [false, true, true, true, false, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, true, false, false, true, true, true, true, false, false,
    false, false, true]
/-- Sign-kick mask segment `4` for `(m = 32, r = 384)`. -/
def rkmMkPack_m32_r384_s4 : List Bool :=
  [false, false, false, false, false, false, false, false, true, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, true, false, false, false, false, false, false, false, true]
/-- Sign-kick mask segment `5` for `(m = 32, r = 384)`. -/
def rkmMkPack_m32_r384_s5 : List Bool :=
  [false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, true, false, false, false, false, false, false, false, true, false, false, false,
    false, false, false, false, true]
/-- Sign-kick mask segment `6` for `(m = 32, r = 384)`. -/
def rkmMkPack_m32_r384_s6 : List Bool :=
  [false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, true, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, true, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    true, false, false, false, false, false, false, false, true]
/-- Multi-segment sign-kick masks for `(m = 32, r = 384)`. -/
def rkmMasksPack_m32_r384 : List (List Bool) :=
  [rkmMkPack_m32_r384_s0, rkmMkPack_m32_r384_s1, rkmMkPack_m32_r384_s2, rkmMkPack_m32_r384_s3,
    rkmMkPack_m32_r384_s4, rkmMkPack_m32_r384_s5, rkmMkPack_m32_r384_s6, []]
/-- Hit-row chunk `0` for `(m = 32, r = 384)`. -/
def rkmRowPack_m32_r384_p0 : List ℕ :=
  [10249352, 45420419, 20762933, 20194522, 29899096, 5674817, 36444376, 68642, 24153312,
    788151, 44129640, 51897814, 7539366, 2637590, 110324534, 185248521, 281778862, 6622825,
    100531958, 1742212, 69352508, 8037502, 194886918, 39269638, 27791526, 7189623, 95175762,
    8770648, 41108131, 224792741, 58606642, 6670271]
/-- Hit-row chunk `1` for `(m = 32, r = 384)`. -/
def rkmRowPack_m32_r384_p1 : List ℕ :=
  [40621153, 118969551, 78440530, 12964502, 87823168, 11421746, 3150457, 49442313, 36068652,
    26613226, 92327153, 95658621, 2761585, 2372585, 317996489, 1689377, 402628908, 329005656,
    50742648, 152771842, 32276458, 24120536, 269301816, 6827316, 215669222, 136802366,
    70851377, 1520726508, 807820542, 225605181, 142600284, 455041248]
/-- Hit-row chunk `2` for `(m = 32, r = 384)`. -/
def rkmRowPack_m32_r384_p2 : List ℕ :=
  [787733084, 69323456, 168596853, 49947792, 125870333, 24218, 63378792, 71063196, 33158977,
    105952580, 39324854, 43287989, 711731887, 942881846, 224497810, 229924274, 741405867,
    509324119, 152372408, 360744993, 656952697, 132102065, 22326714, 34371, 176189023,
    170951157, 48454670, 141209590, 424995768, 205386340, 15251422, 139008967]
/-- Hit-row chunk `3` for `(m = 32, r = 384)`. -/
def rkmRowPack_m32_r384_p3 : List ℕ :=
  [94354, 347728558, 822372523, 1151338931, 2124524720, 4192627607, 5767714646, 4801105596,
    2505080532, 1055435762, 615523649, 552030657, 447213275, 292671480, 378534920, 1424366220,
    5562489310, 15275509963, 30320834971, 47447002220, 63449872959, 77214233829, 88849622941,
    97853985308, 102427574367, 100428632155, 91058585351, 75809871017, 57898214098,
    40733114885, 26609997068, 16315412562]
/-- Hit-row chunk `4` for `(m = 32, r = 384)`. -/
def rkmRowPack_m32_r384_p4 : List ℕ :=
  [9504820974, 5328169123, 2907553538, 1558528687, 825053466, 431974530, 223256989, 113429914,
    56368390, 27264027, 12780923, 5787941, 2525932, 1060444, 427694, 165515, 61383, 21782,
    7380, 2381, 728, 210, 56, 13, 2, 0, 0, 0, 0, 0, 0, 0]
/-- Hit-row chunk `5` for `(m = 32, r = 384)`. -/
def rkmRowPack_m32_r384_p5 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0]
/-- Hit-row chunk `6` for `(m = 32, r = 384)`. -/
def rkmRowPack_m32_r384_p6 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0]
/-- Hit-row chunk `7` for `(m = 32, r = 384)`. -/
def rkmRowPack_m32_r384_p7 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0]
/-- Hit-row chunk `8` for `(m = 32, r = 384)`. -/
def rkmRowPack_m32_r384_p8 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0]
/-- Hit-row chunk `9` for `(m = 32, r = 384)`. -/
def rkmRowPack_m32_r384_p9 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0]
/-- Hit-row chunk `10` for `(m = 32, r = 384)`. -/
def rkmRowPack_m32_r384_p10 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0]
/-- Hit-row chunk `11` for `(m = 32, r = 384)`. -/
def rkmRowPack_m32_r384_p11 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0]
/-- Certified `10 ^ 12`-scaled hit row for `(m = 32, r = 384)`. -/
def rkmRowPack_m32_r384 : List ℕ :=
  rkmRowPack_m32_r384_p0 ++ rkmRowPack_m32_r384_p1 ++ rkmRowPack_m32_r384_p2
    ++ rkmRowPack_m32_r384_p3 ++ rkmRowPack_m32_r384_p4 ++ rkmRowPack_m32_r384_p5
    ++ rkmRowPack_m32_r384_p6 ++ rkmRowPack_m32_r384_p7 ++ rkmRowPack_m32_r384_p8
    ++ rkmRowPack_m32_r384_p9 ++ rkmRowPack_m32_r384_p10 ++ rkmRowPack_m32_r384_p11

end

public section

private abbrev bZ : ℕ := 2000000000000000
private theorem hbZ0 : Nat.ble bZ 0 = false := rfl
private abbrev fN {α : Type} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β :=
  HighDForce.withForcedList xs k
private def pCat : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | x :: xs, ys => x :: pCat xs ys
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := by rw [Nat.add_eq]; exact Nat.add_comm 1 x
private theorem hzMul0 (z : ℕ) : Nat.mul 0 z = 0 := by rw [Nat.mul_eq]; omega
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private theorem nmod (x y : ℕ) : Nat.mod x y = x % y := rfl
private def uC (x : ℕ) (xs : List ℕ) : List ℕ :=
  match Nat.add 1 x with
  | 0 => xs
  | v + 1 =>
    match xs with
    | [] => [v]
    | h :: t => v :: h :: t
private theorem uC_eq (x : ℕ) (xs : List ℕ) : uC x xs = x :: xs := by
  unfold uC; rw [n1a]; cases xs <;> rfl
private def uOfHb : List ℕ → List ℤ
  | [] => []
  | n :: ns => Int.ofNat n :: uOfHb ns
private def bCZ (x : ℤ) (xs : List ℤ) : List ℤ :=
  match x with
  | Int.ofNat v =>
    match xs with
    | [] => [Int.ofNat v]
    | h :: t => Int.ofNat v :: h :: t
  | Int.negSucc v =>
    match xs with
    | [] => [Int.negSucc v]
    | h :: t => Int.negSucc v :: h :: t
private theorem bCZ_eq (x : ℤ) (xs : List ℤ) : bCZ x xs = x :: xs := by
  cases x <;> cases xs <;> rfl
private theorem bOfF_eq (x : ℕ) : primOfNatForced x = Int.ofNat x := by
  simp [primOfNatForced, Nat.one_add]
private theorem bNsF_eq (x : ℕ) : primNegSuccForced x = Int.negSucc x := by
  simp [primNegSuccForced, Nat.one_add]
private theorem bSub_eq (u z : ℕ) : rkmForcedSubNatNat u z = (u : ℤ) - (z : ℤ) := by
  unfold rkmForcedSubNatNat; rw [bOfF_eq, Nat.sub_eq]; cases h : z - u with
  | zero => dsimp only; rw [Nat.sub_eq, Int.ofNat_eq_natCast]; omega
  | succ k => dsimp only; rw [Int.negSucc_eq]; omega
private def bDec (z : ℕ) : List ℕ → List ℤ
  | [] => []
  | u :: us => bCZ (rkmForcedSubNatNat u z) (bDec z us)
private theorem bDec_nil (z : ℕ) : bDec z [] = [] := rfl
private theorem bDec_cons (z u : ℕ) (us : List ℕ) :
    bDec z (u :: us) = ((u : ℤ) - (z : ℤ)) :: bDec z us := by
  rw [bDec, bCZ_eq, bSub_eq]
private theorem bZ0 (z : ℕ) : ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [Int.ofNat_eq_natCast]; omega
private theorem bM0 (z : ℕ) :
    muxRawIntMul (Int.ofNat 0) ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [bZ0]; rfl
private def bNL : List ℕ → ℕ
  | [] => 0
  | _ :: us => Nat.add (bNL us) 1
private theorem bNL_eq (z : ℕ) : ∀ (us : List ℕ), bNL us = altIntLen (bDec z us)
  | [] => rfl
  | _ :: us => by dsimp only [bNL]; rw [bDec_cons]; dsimp only [altIntLen]; rw [bNL_eq z us]
private def zTd : ℤ → ℕ → ℤ
  | Int.ofNat m, d => Int.ofNat (m / d)
  | Int.negSucc k, d => -(((k + 1) / d : ℕ) : ℤ)
private theorem bNeg_eq : ∀ (n : ℕ), muxRawNegOfNat n = -(n : ℤ)
  | 0 => by dsimp only [muxRawNegOfNat]; rw [Int.ofNat_eq_natCast]; omega
  | k + 1 => by dsimp only [muxRawNegOfNat]; rw [Int.negSucc_eq]; omega
private theorem bTdN_eq : ∀ (x : ℤ) (d : ℕ), muxRawIntTdivNat x d = zTd x d
  | Int.ofNat _, _ => rfl
  | Int.negSucc _, _ => by
    dsimp only [muxRawIntTdivNat, zTd]; rw [bNeg_eq, ndiv, Nat.add_eq]
private theorem bSubNTd_eq (m n d : ℕ) :
    rkmUltraSubNatTdiv m n d = zTd ((m : ℤ) - (n : ℤ)) d := by
  unfold rkmUltraSubNatTdiv; simp only [Nat.sub_eq, ndiv, Nat.add_eq]; cases h : n - m with
  | zero =>
    have hm : (m : ℤ) - (n : ℤ) = Int.ofNat (m - n) := by rw [Int.ofNat_eq_natCast]; omega
    rw [hm]; rfl
  | succ k =>
    dsimp only; have hm : (m : ℤ) - (n : ℤ) = Int.negSucc k := by rw [Int.negSucc_eq]; omega
    rw [hm]; dsimp only [zTd]; rw [bNeg_eq]
private theorem bSubTd_eq (a b : ℤ) (d : ℕ) : rkmUltraSubTdiv a b d = zTd (a - b) d := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => exact bSubNTd_eq m n d
    | negSucc n =>
      have hm : Int.ofNat m - Int.negSucc n = Int.ofNat (m + (n + 1)) := by
        rw [Int.ofNat_eq_natCast, Int.negSucc_eq, Int.ofNat_eq_natCast]; omega
      rw [hm]; rfl
  | negSucc m =>
    cases b with
    | ofNat n =>
      have hm : Int.negSucc m - Int.ofNat n = Int.negSucc (m + n) := by
        rw [Int.negSucc_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]; omega
      dsimp only [rkmUltraSubTdiv]; rw [hm]; dsimp only [zTd]
      rw [bNeg_eq, ndiv, Nat.add_eq, Nat.add_eq]
      exact congrArg (fun t : ℕ => -(((t / d : ℕ) : ℤ))) (by omega)
    | negSucc n =>
      dsimp only [rkmUltraSubTdiv]; rw [bSubNTd_eq, Nat.add_eq, Nat.add_eq]
      exact congrArg (fun t => zTd t d) (by simp only [Int.negSucc_eq]; omega)
private theorem bMul_eq (a b : ℤ) : muxRawIntMul a b = a * b := by
  cases a <;> cases b <;>
    simp only [muxRawIntMul, bNeg_eq, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast,
      Int.negSucc_eq] <;> push_cast <;> ring
private theorem bFAdd_eq (a b : ℤ) : rkmForcedIntAdd a b = a + b := by
  cases a <;> cases b <;>
    simp only [rkmForcedIntAdd, bOfF_eq, bNsF_eq, bSub_eq, Nat.add_eq,
      Int.ofNat_eq_natCast, Int.negSucc_eq] <;> omega
private theorem bAC_eq (a b : ℤ) (xs : List ℤ) : rkmUltraAddCons a b xs = (a + b) :: xs := by
  unfold rkmUltraAddCons; rw [bFAdd_eq]; cases a + b <;> cases xs <;> rfl
private theorem bBle : ∀ {a b : ℕ}, Nat.ble a b = true → a ≤ b
  | 0, _, _ => Nat.zero_le _
  | _ + 1, 0, h => Bool.noConfusion h
  | _ + 1, _ + 1, h => Nat.succ_le_succ (bBle h)
private theorem bBleOfLe {a b : ℕ} (h : a ≤ b) : Nat.ble a b = true := Nat.ble_eq_true_of_le h
private abbrev bStepVal (v P Q d : ℕ) : ℕ :=
  Nat.sub (Nat.add v (Nat.div (Nat.sub P Q) d)) (Nat.div (Nat.sub Q P) d)
private theorem bStepVal_eq (z v P Q d : ℕ) (hv : 0 < bStepVal v P Q d) :
    ((bStepVal v P Q d : ℤ) - (z : ℤ)) =
      ((v : ℤ) - (z : ℤ)) + zTd ((P : ℤ) - (Q : ℤ)) d := by
  rw [← bSubNTd_eq]; unfold bStepVal at hv ⊢; unfold rkmUltraSubNatTdiv
  simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢; revert hv
  cases hd : Q - P with
  | zero =>
    intro _; dsimp only; rw [Nat.zero_div, Nat.sub_zero, Int.ofNat_eq_natCast]; push_cast; ring
  | succ k =>
    intro hv; dsimp only at hv ⊢
    have hpq : P - Q = 0 := by omega
    rw [hpq, Nat.zero_div, Nat.add_zero] at hv ⊢; rw [bNeg_eq]
    generalize (k + 1) / d = q at hv ⊢; omega
private theorem bStepVal_same (z P d : ℕ) : bStepVal z P P d = z := by
  unfold bStepVal
  simp only [Nat.sub_eq, Nat.add_eq, ndiv, Nat.sub_self, Nat.zero_div, Nat.add_zero, Nat.sub_zero]
private theorem bStepVal_comm (z A B d : ℕ) :
    bStepVal z (Nat.add A B) (Nat.add B A) d = z := by
  have hc : Nat.add B A = Nat.add A B := by simp only [Nat.add_eq]; omega
  rw [hc]; exact bStepVal_same z (Nat.add A B) d
private abbrev bCV (z d b0 c0 b v c1 : ℕ) : ℕ :=
  bStepVal v (Nat.add (Nat.mul b0 c0) (Nat.mul b z)) (Nat.add (Nat.mul b c1) (Nat.mul b0 z)) d
private theorem bC_hb (z d b0 c0 b v c1 : ℕ) {rest : List ℕ} {tZ : List ℤ}
    (hv : 0 < bCV z d b0 c0 b v c1) (ht : bDec z rest = tZ) :
    bDec z (uC (bCV z d b0 c0 b v c1) rest) =
      rkmUltraAddCons ((v : ℤ) - (z : ℤ))
        (rkmUltraSubTdiv (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
          (muxRawIntMul (Int.ofNat b) ((c1 : ℤ) - (z : ℤ))) d) tZ := by
  rw [uC_eq, bDec_cons, ht, bAC_eq, bSubTd_eq, bMul_eq, bMul_eq]
  refine congrArg (· :: tZ) ?_
  have hpq : ((Nat.add (Nat.mul b0 c0) (Nat.mul b z) : ℕ) : ℤ) -
      ((Nat.add (Nat.mul b c1) (Nat.mul b0 z) : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) - (Int.ofNat b) * ((c1 : ℤ) - (z : ℤ)) := by
    simp only [Nat.add_eq, Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  unfold bCV at hv ⊢; rw [bStepVal_eq z v _ _ d hv, hpq]
private theorem bC_nil (z d b0 c0 v : ℕ) {rest : List ℕ} {tZ : List ℤ}
    (hv : 0 < bStepVal v (Nat.mul b0 c0) (Nat.mul b0 z) d) (ht : bDec z rest = tZ) :
    bDec z (uC (bStepVal v (Nat.mul b0 c0) (Nat.mul b0 z) d) rest) =
      rkmUltraAddCons ((v : ℤ) - (z : ℤ))
        (muxRawIntTdivNat (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ))) d) tZ := by
  rw [uC_eq, bDec_cons, ht, bAC_eq, bTdN_eq, bMul_eq]
  refine congrArg (· :: tZ) ?_
  have hpq : ((Nat.mul b0 c0 : ℕ) : ℤ) - ((Nat.mul b0 z : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) := by
    simp only [Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  rw [bStepVal_eq z v _ _ d hv, hpq]
private def bAllPos : List ℕ → Bool
  | [] => true
  | x :: xs => cond (Nat.ble x 0) false (bAllPos xs)
private theorem bAllPos_uC {x : ℕ} {xs : List ℕ} (h : bAllPos (uC x xs) = true) :
    0 < x ∧ bAllPos xs = true := by
  rw [uC_eq] at h
  cases x with
  | zero => exact Bool.noConfusion h
  | succ k => exact ⟨Nat.succ_pos k, h⟩
private def bHO (z : ℕ) : List ℕ → ℕ
  | [] => z
  | x :: _ => x
private def bTN : List ℕ → List ℕ
  | [] => []
  | _ :: xs => xs
private theorem bHOe (z : ℕ) : ∀ (cs : List ℕ),
    ((bHO z cs : ℤ) - (z : ℤ)) =
      (match bDec z cs with
       | cn :: _ => cn
       | [] => Int.ofNat 0)
  | [] => by unfold bHO; rw [bDec_nil, bZ0]
  | _ :: _ => by unfold bHO; rw [bDec_cons]
private theorem bTNe (z : ℕ) : ∀ (xs : List ℕ),
    bDec z (bTN xs) =
      (match bDec z xs with
       | _ :: t => t
       | [] => [])
  | [] => rfl
  | _ :: _ => by unfold bTN; rw [bDec_cons]
private def zPad (z : ℕ) : ℕ → List ℕ → List ℕ
  | 0, xs => xs
  | k + 1, [] => uC z (zPad z k [])
  | k + 1, x :: xs => uC x (zPad z k xs)
private theorem zPad_uC (z r x : ℕ) (xs : List ℕ) :
    zPad z (r + 1) (uC x xs) = uC x (zPad z r xs) := by
  rw [uC_eq]; rfl
private theorem zPad_hd (z : ℕ) : ∀ (k : ℕ) (xs : List ℕ), bHO z (zPad z k xs) = bHO z xs
  | 0, _ => rfl
  | _ + 1, [] => by dsimp only [zPad]; rw [uC_eq]; rfl
  | _ + 1, _ :: _ => by dsimp only [zPad]; rw [uC_eq]; rfl
private theorem zPad_tl (z : ℕ) :
    ∀ (k : ℕ) (xs : List ℕ), bTN (zPad z k xs) = zPad z (k - 1) (bTN xs)
  | 0, _ => rfl
  | _ + 1, [] => by dsimp only [zPad]; rw [uC_eq]; rfl
  | _ + 1, _ :: _ => by dsimp only [zPad]; rw [uC_eq]; rfl
private theorem zPad_bNL (z : ℕ) :
    ∀ (k : ℕ) (xs : List ℕ), Nat.ble (bNL xs) k = true → bNL (zPad z k xs) = k
  | 0, [], _ => rfl
  | 0, _ :: xs, h => by
    dsimp only [bNL] at h; rw [Nat.add_eq] at h; have h1 := bBle h; omega
  | k + 1, [], _ => by
    dsimp only [zPad]; rw [uC_eq]; dsimp only [bNL]; rw [zPad_bNL z k [] rfl, Nat.add_eq]
  | k + 1, _ :: xs, h => by
    have hk : Nat.ble (bNL xs) k = true := by
      have h1 := bBle h; dsimp only [bNL] at h1; rw [Nat.add_eq] at h1
      exact bBleOfLe (by omega)
    dsimp only [zPad]; rw [uC_eq]; dsimp only [bNL]; rw [zPad_bNL z k xs hk, Nat.add_eq]
private theorem bAllPos_zPad {z : ℕ} (hz : Nat.ble z 0 = false) :
    ∀ (k : ℕ) (xs : List ℕ), bAllPos xs = true → bAllPos (zPad z k xs) = true
  | 0, _, h => h
  | k + 1, [], _ => by
    dsimp only [zPad]; rw [uC_eq]; dsimp only [bAllPos]; rw [hz]; dsimp only [cond]
    exact bAllPos_zPad hz k [] rfl
  | k + 1, x :: xs, h => by
    dsimp only [bAllPos] at h; dsimp only [zPad]; rw [uC_eq]; dsimp only [bAllPos]
    revert h
    cases Nat.ble x 0 with
    | true => intro h; dsimp only [cond] at h; cases h
    | false => intro h; dsimp only [cond] at h ⊢; exact bAllPos_zPad hz k xs h
private def bEqN (a b : ℕ) : Bool := cond (Nat.ble a b) (Nat.ble b a) false
private theorem bEqN_self (a : ℕ) : bEqN a a = true := by
  have hle : Nat.ble a a = true := bBleOfLe (Nat.le_refl a)
  unfold bEqN; rw [hle]; rfl
private theorem bEqN_eq (a b : ℕ) (h : bEqN a b = true) : a = b := by
  unfold bEqN at h; revert h
  cases hab : Nat.ble a b with
  | false => intro h; dsimp only [cond] at h; cases h
  | true =>
    cases hba : Nat.ble b a with
    | false => intro h; dsimp only [cond] at h; cases h
    | true => intro _; exact Nat.le_antisymm (bBle hab) (bBle hba)
private def bCT (z x : ℕ) (xs : List ℕ) : List ℕ :=
  match xs with
  | h :: t => x :: h :: t
  | [] => cond (bEqN x z) [] [x]
private def bTrim (z : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: xs => bCT z x (bTrim z xs)
private theorem bTrim_zPad (z : ℕ) : ∀ (k : ℕ) (xs : List ℕ), bTrim z (zPad z k xs) = bTrim z xs
  | 0, _ => rfl
  | k + 1, [] => by
    dsimp only [zPad]; rw [uC_eq]; dsimp only [bTrim]; rw [bTrim_zPad z k []]
    dsimp only [bTrim, bCT]; rw [bEqN_self z]; rfl
  | k + 1, x :: xs => by
    dsimp only [zPad]; rw [uC_eq]; dsimp only [bTrim]; rw [bTrim_zPad z k xs]
private theorem zPad_bTrim_len (z : ℕ) : ∀ (xs : List ℕ), zPad z (bNL xs) (bTrim z xs) = xs
  | [] => rfl
  | x :: t => by
    have hal : bNL (x :: t) = bNL t + 1 := rfl
    rw [hal]; dsimp only [bTrim]; have ih := zPad_bTrim_len z t; revert ih
    cases bTrim z t with
    | cons _ _ => intro ih; dsimp only [bCT, zPad]; rw [uC_eq, ih]
    | nil =>
      intro ih; dsimp only [bCT]
      cases he : bEqN x z with
      | true => dsimp only [cond, zPad]; rw [uC_eq, bEqN_eq x z he, ih]
      | false => dsimp only [cond, zPad]; rw [uC_eq, ih]
private def bSl (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, b0, c0, [], vs, cs =>
    uC (bStepVal (bHO z vs) (Nat.mul b0 c0) (Nat.mul b0 z) d)
      (bSl z d rem 0 z [] (bTN vs) (bTN cs))
  | rem + 1, b0, c0, b :: bR, vs, cs =>
    uC (bCV z d b0 c0 b (bHO z vs) (bHO z (bTN cs)))
      (bSl z d rem b (bHO z cs) bR (bTN vs) (bTN cs))
private theorem bSl_len (z d : ℕ) :
    ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ), bNL (bSl z d rem b0 c0 bns vs cs) = rem
  | 0, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, [], vs, cs => by
    dsimp only [bSl]; rw [uC_eq]; dsimp only [bNL]
    rw [bSl_len z d rem 0 z [] (bTN vs) (bTN cs), Nat.add_eq]
  | rem + 1, b0, c0, b :: bR, vs, cs => by
    dsimp only [bSl]; rw [uC_eq]; dsimp only [bNL]
    rw [bSl_len z d rem b (bHO z cs) bR (bTN vs) (bTN cs), Nat.add_eq]
private theorem bSl_zPad (z d : ℕ) : ∀ (rem b0 c0 kv kc : ℕ) (bns vs cs : List ℕ),
    bSl z d rem b0 c0 bns (zPad z kv vs) (zPad z kc cs) = bSl z d rem b0 c0 bns vs cs
  | 0, _, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, kv, kc, [], vs, cs => by
    dsimp only [bSl]; rw [zPad_hd z kv vs, zPad_tl z kv vs, zPad_tl z kc cs]
    rw [bSl_zPad z d rem 0 z (kv - 1) (kc - 1) [] (bTN vs) (bTN cs)]
  | rem + 1, b0, c0, kv, kc, b :: bR, vs, cs => by
    dsimp only [bSl]
    rw [zPad_hd z kv vs, zPad_tl z kc cs, zPad_hd z (kc - 1) (bTN cs), zPad_hd z kc cs,
      zPad_tl z kv vs]
    rw [bSl_zPad z d rem b (bHO z cs) (kv - 1) (kc - 1) bR (bTN vs) (bTN cs)]
private theorem bSl_zero (z d : ℕ) :
    ∀ (rem b0 : ℕ) (bns : List ℕ), bSl z d rem b0 z bns [] [] = zPad z rem []
  | 0, _, _ => rfl
  | rem + 1, b0, [] => by
    dsimp only [bSl, bHO, bTN, zPad]; rw [bStepVal_same z (Nat.mul b0 z) d, bSl_zero z d rem 0 []]
  | rem + 1, b0, b :: bR => by
    dsimp only [bSl, bCV, bHO, bTN, zPad]
    rw [bStepVal_comm z (Nat.mul b0 z) (Nat.mul b z) d, bSl_zero z d rem b bR]
private theorem bSl_sound (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bAllPos (bSl z d rem b0 c0 bns vs cs) = true →
      bDec z (bSl z d rem b0 c0 bns vs cs) =
        rkmUltraSlideLoopAux d rem (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
          (uOfHb bns) (bDec z vs) (bDec z cs)
  | 0, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, [], vs, cs, h => by
    dsimp only [bSl, uOfHb, rkmUltraSlideLoopAux] at h ⊢
    have hp := bAllPos_uC h
    have hi := bSl_sound z d rem 0 z [] (bTN vs) (bTN cs) hp.2
    rw [bM0 z, uOfHb, bTNe z vs, bTNe z cs] at hi
    have hc := bC_nil z d b0 c0 (bHO z vs) hp.1 hi
    rw [bHOe z vs] at hc; exact hc
  | rem + 1, b0, c0, b :: bR, [], [], h => by
    dsimp only [bSl, bHO, bTN, uOfHb] at h ⊢; rw [bDec_nil]
    dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uC h
    have hi := bSl_sound z d rem b z bR [] [] hp.2
    rw [bZ0 z, bDec_nil] at hi
    have hc := bC_hb z d b0 c0 b z z hp.1 hi; rw [bZ0 z] at hc; exact hc
  | rem + 1, b0, c0, b :: bR, [], c :: cT, h => by
    dsimp only [bSl, bHO, bTN, uOfHb] at h ⊢
    rw [bDec_nil, bDec_cons z c cT]; dsimp only [rkmUltraSlideLoopAux]
    have hp := bAllPos_uC h
    have hi := bSl_sound z d rem b c bR [] cT hp.2; rw [bDec_nil] at hi
    have hc := bC_hb z d b0 c0 b z (bHO z cT) hp.1 hi
    rw [bHOe z cT, bZ0 z] at hc; exact hc
  | rem + 1, b0, c0, b :: bR, v :: vT, [], h => by
    dsimp only [bSl, bHO, bTN, uOfHb] at h ⊢
    rw [bDec_cons z v vT, bDec_nil]; dsimp only [rkmUltraSlideLoopAux]
    have hp := bAllPos_uC h
    have hi := bSl_sound z d rem b z bR vT [] hp.2; rw [bZ0 z, bDec_nil] at hi
    have hc := bC_hb z d b0 c0 b v z hp.1 hi; rw [bZ0 z] at hc; exact hc
  | rem + 1, b0, c0, b :: bR, v :: vT, c :: cT, h => by
    dsimp only [bSl, bHO, bTN, uOfHb] at h ⊢
    rw [bDec_cons z v vT, bDec_cons z c cT]; dsimp only [rkmUltraSlideLoopAux]
    have hp := bAllPos_uC h
    have hi := bSl_sound z d rem b c bR vT cT hp.2
    have hc := bC_hb z d b0 c0 b v (bHO z cT) hp.1 hi
    rw [bHOe z cT] at hc; exact hc
private def mkHbZ (z : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: bs => uC b (uC (Nat.mul b z) (mkHbZ z bs))
private def bSlZ (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, p0, q0, hbz, vs, cs =>
    match hbz with
    | [] =>
      match vs, cs with
      | [], [] => uC (bStepVal z p0 q0 d) []
      | _, _ => uC (bStepVal (bHO z vs) p0 q0 d) (bSlZ z d rem 0 0 [] (bTN vs) (bTN cs))
    | [_] => []
    | b :: bz :: bR =>
      match vs, cs with
      | [], [] => uC (bStepVal z (Nat.add p0 bz) (Nat.add bz q0) d) []
      | v :: vT, c :: cT =>
        uC (bStepVal v (Nat.add p0 bz) (Nat.add (Nat.mul b (bHO z cT)) q0) d)
          (bSlZ z d rem (Nat.mul b c) bz bR vT cT)
      | v :: vT, [] =>
        uC (bStepVal v (Nat.add p0 bz) (Nat.add bz q0) d) (bSlZ z d rem bz bz bR vT [])
      | [], c :: cT =>
        uC (bStepVal z (Nat.add p0 bz) (Nat.add (Nat.mul b (bHO z cT)) q0) d)
          (bSlZ z d rem (Nat.mul b c) bz bR [] cT)
private theorem bSlZ_zPad (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    zPad z rem (bSlZ z d rem (Nat.mul b0 c0) (Nat.mul b0 z) (mkHbZ z bns) vs cs) =
      bSl z d rem b0 c0 bns vs cs
  | 0, _, _, _, _, _ => rfl
  | rem + 1, _, _, bns, vs, cs => by
    cases bns with
    | nil =>
      cases vs with
      | nil =>
        cases cs with
        | nil => dsimp only [mkHbZ, bSlZ, bSl, bHO, bTN]; rw [zPad_uC, bSl_zero z d rem 0 []]
        | cons _ cT =>
          have hrec := bSlZ_zPad z d rem 0 z [] [] cT
          dsimp only [mkHbZ] at hrec; rw [hzMul0 z] at hrec
          dsimp only [mkHbZ, bSlZ, bSl, bHO, bTN]; rw [zPad_uC, hrec]
      | cons _ vT =>
        cases cs with
        | nil =>
          have hrec := bSlZ_zPad z d rem 0 z [] vT []
          dsimp only [mkHbZ] at hrec; rw [hzMul0 z] at hrec
          dsimp only [mkHbZ, bSlZ, bSl, bHO, bTN]; rw [zPad_uC, hrec]
        | cons _ cT =>
          have hrec := bSlZ_zPad z d rem 0 z [] vT cT
          dsimp only [mkHbZ] at hrec; rw [hzMul0 z] at hrec
          dsimp only [mkHbZ, bSlZ, bSl, bHO, bTN]; rw [zPad_uC, hrec]
    | cons b bR =>
      dsimp only [mkHbZ]; rw [uC_eq, uC_eq]; cases vs with
      | nil =>
        cases cs with
        | nil => dsimp only [bSlZ, bSl, bCV, bHO, bTN]; rw [zPad_uC, bSl_zero z d rem b bR]
        | cons c cT =>
          dsimp only [bSlZ, bSl, bCV, bHO, bTN]; rw [zPad_uC, bSlZ_zPad z d rem b c bR [] cT]
      | cons v vT =>
        cases cs with
        | nil => dsimp only [bSlZ, bSl, bCV, bHO, bTN]; rw [zPad_uC, bSlZ_zPad z d rem b z bR vT []]
        | cons c cT =>
          dsimp only [bSlZ, bSl, bCV, bHO, bTN]; rw [zPad_uC, bSlZ_zPad z d rem b c bR vT cT]
private theorem bSlZ_pfx (z d : ℕ) : ∀ (rem : ℕ) (l t : List ℕ) (p0 q0 : ℕ) (vs cs : List ℕ),
    2 * rem ≤ l.length → bSlZ z d rem p0 q0 (l ++ t) vs cs = bSlZ z d rem p0 q0 l vs cs
  | 0, _, _, _, _, _, _, _ => rfl
  | rem + 1, [], _, _, _, _, _, h => by change 2 * (rem + 1) ≤ 0 at h; omega
  | rem + 1, [_], _, _, _, _, _, h => by change 2 * (rem + 1) ≤ 1 at h; omega
  | rem + 1, b :: bz :: l, t, p0, q0, vs, cs, h => by
    change 2 * (rem + 1) ≤ l.length + 2 at h
    have hl : 2 * rem ≤ l.length := by omega
    have ha : (b :: bz :: l) ++ t = b :: bz :: (l ++ t) := rfl
    rw [ha]; cases vs with
    | nil =>
      cases cs with
      | nil => rfl
      | cons c cT => dsimp only [bSlZ]; rw [bSlZ_pfx z d rem l t (Nat.mul b c) bz [] cT hl]
    | cons v vT =>
      cases cs with
      | nil => dsimp only [bSlZ]; rw [bSlZ_pfx z d rem l t bz bz vT [] hl]
      | cons c cT => dsimp only [bSlZ]; rw [bSlZ_pfx z d rem l t (Nat.mul b c) bz vT cT hl]
private inductive HbZ4 : Type
  | tail : List ℕ → HbZ4
  | c4 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → HbZ4 → HbZ4
private abbrev hbz4P (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) : List ℕ := [b1, z1, b2, z2, b3, z3, b4, z4]
private abbrev hbz4C (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) (t : List ℕ) : List ℕ :=
  b1 :: z1 :: b2 :: z2 :: b3 :: z3 :: b4 :: z4 :: t
private theorem hbz4C_app (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) (t : List ℕ) :
    hbz4C b1 z1 b2 z2 b3 z3 b4 z4 t = hbz4P b1 z1 b2 z2 b3 z3 b4 z4 ++ t := rfl
private theorem hbz4P_len (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) :
    (hbz4P b1 z1 b2 z2 b3 z3 b4 z4).length = 8 := rfl
private def hbz4L : HbZ4 → List ℕ
  | HbZ4.tail l => l
  | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r => hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L r)
private def fH4 {α : Type} (h : HbZ4) (k : HbZ4 → α) : α :=
  match h with
  | HbZ4.tail l => fL l fun lF => k (HbZ4.tail lF)
  | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r => k (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r)
private theorem fH4e {α : Type} (h : HbZ4) (k : HbZ4 → α) : fH4 h k = k h := by
  cases h with
  | tail _ => dsimp only [fH4, fL]; rw [rkmb_forceList_eq]
  | c4 _ _ _ _ _ _ _ _ _ => rfl
private def toH4 : List ℕ → HbZ4
  | b1 :: z1 :: b2 :: z2 :: b3 :: z3 :: b4 :: z4 :: bs =>
    match toH4 bs with
    | HbZ4.tail l => HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 (HbZ4.tail l)
    | HbZ4.c4 a1 w1 a2 w2 a3 w3 a4 w4 t =>
      HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 (HbZ4.c4 a1 w1 a2 w2 a3 w3 a4 w4 t)
  | bs => HbZ4.tail bs
private theorem hbz4L_toH4 : ∀ (xs : List ℕ), hbz4L (toH4 xs) = xs
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | [_, _, _, _] => rfl
  | [_, _, _, _, _] => rfl
  | [_, _, _, _, _, _] => rfl
  | [_, _, _, _, _, _, _] => rfl
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: bs => by
    dsimp only [toH4]; cases h : toH4 bs with
    | tail _ => have ih := hbz4L_toH4 bs; rw [h] at ih; dsimp only [hbz4L, hbz4C] at ih ⊢; rw [ih]
    | c4 _ _ _ _ _ _ _ _ _ =>
      have ih := hbz4L_toH4 bs; rw [h] at ih; dsimp only [hbz4L, hbz4C] at ih ⊢; rw [ih]
private def takeH4 : ℕ → HbZ4 → List ℕ
  | 0, _ => []
  | _ + 1, HbZ4.tail l => l
  | k + 1, HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r =>
    hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (takeH4 k r)
private theorem takeH4_spec : ∀ (k : ℕ) (hbz : HbZ4),
    takeH4 k hbz = hbz4L hbz ∨
      ∃ t, hbz4L hbz = takeH4 k hbz ++ t ∧ 8 * k ≤ (takeH4 k hbz).length
  | 0, hbz => Or.inr ⟨hbz4L hbz, rfl, Nat.zero_le _⟩
  | _ + 1, HbZ4.tail _ => Or.inl rfl
  | k + 1, HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r => by
    dsimp only [takeH4, hbz4L]
    rcases takeH4_spec k r with heq | ⟨t, happ, hlen⟩
    · exact Or.inl (congrArg (hbz4C b1 z1 b2 z2 b3 z3 b4 z4) heq)
    · refine Or.inr ⟨t, ?_, ?_⟩
      · rw [hbz4C_app, hbz4C_app, happ, List.append_assoc]
      · rw [hbz4C_app, List.length_append, hbz4P_len]; omega
private theorem bSlZ_takeH4 (z d k : ℕ) (hbz : HbZ4) (rem p0 q0 : ℕ)
    (vs cs : List ℕ) (h : rem ≤ 4 * k) :
    bSlZ z d rem p0 q0 (takeH4 k hbz) vs cs = bSlZ z d rem p0 q0 (hbz4L hbz) vs cs := by
  rcases takeH4_spec k hbz with heq | ⟨t, happ, hlen⟩
  · rw [heq]
  · rw [happ]; exact (bSlZ_pfx z d rem (takeH4 k hbz) t p0 q0 vs cs (by omega)).symm
private inductive Q4 : Type
  | tail : List ℕ → Q4
  | c4 : ℕ → ℕ → ℕ → ℕ → Q4 → Q4
private def q4L : Q4 → List ℕ
  | Q4.tail xs => xs
  | Q4.c4 x1 x2 x3 x4 r => x1 :: x2 :: x3 :: x4 :: q4L r
private def q4S (x1 x2 x3 x4 : ℕ) (r : Q4) : Q4 :=
  match Nat.add 1 x1 with
  | 0 => r
  | v1 + 1 =>
    match Nat.add 1 x2 with
    | 0 => r
    | v2 + 1 =>
      match Nat.add 1 x3 with
      | 0 => r
      | v3 + 1 =>
        match Nat.add 1 x4 with
        | 0 => r
        | v4 + 1 =>
          match r with
          | Q4.tail xs => Q4.c4 v1 v2 v3 v4 (Q4.tail xs)
          | Q4.c4 y1 y2 y3 y4 yr => Q4.c4 v1 v2 v3 v4 (Q4.c4 y1 y2 y3 y4 yr)
private theorem q4S_eq (x1 x2 x3 x4 : ℕ) (r : Q4) : q4S x1 x2 x3 x4 r = Q4.c4 x1 x2 x3 x4 r := by
  unfold q4S; rw [n1a x1, n1a x2, n1a x3, n1a x4]; cases r <;> rfl
private def toQ4 : List ℕ → Q4
  | x1 :: x2 :: x3 :: x4 :: xs => q4S x1 x2 x3 x4 (toQ4 xs)
  | [] => Q4.tail []
  | [x1] => fN x1 fun y1 => Q4.tail [y1]
  | [x1, x2] => fN x1 fun y1 => fN x2 fun y2 => Q4.tail [y1, y2]
  | [x1, x2, x3] => fN x1 fun y1 => fN x2 fun y2 => fN x3 fun y3 => Q4.tail [y1, y2, y3]
private theorem q4L_toQ4 : ∀ (xs : List ℕ), q4L (toQ4 xs) = xs
  | [] => rfl
  | [_] => by dsimp only [toQ4, fN]; rw [rkmb_forceNat_eq]; rfl
  | [_, _] => by dsimp only [toQ4, fN]; rw [rkmb_forceNat_eq, rkmb_forceNat_eq]; rfl
  | [_, _, _] =>
    by dsimp only [toQ4, fN]; rw [rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceNat_eq]; rfl
  | x1 :: x2 :: x3 :: x4 :: xs => by
    dsimp only [toQ4]; rw [q4S_eq]; dsimp only [q4L]; rw [q4L_toQ4 xs]
private def fQ4 {α : Type} (v : Q4) (k : Q4 → α) : α :=
  match v with
  | Q4.tail xs => k (Q4.tail xs)
  | Q4.c4 x1 x2 x3 x4 r => k (Q4.c4 x1 x2 x3 x4 r)
private theorem fQ4e {α : Type} (v : Q4) (k : Q4 → α) : fQ4 v k = k v := by
  cases v <;> rfl
private def q4Hd (z : ℕ) : Q4 → ℕ
  | Q4.c4 x _ _ _ _ => x
  | Q4.tail xs => bHO z xs
private theorem q4Hd_eq (z : ℕ) (w : Q4) : q4Hd z w = bHO z (q4L w) := by
  cases w <;> rfl
private def q4AP : Q4 → Bool
  | Q4.tail xs => bAllPos xs
  | Q4.c4 x1 x2 x3 x4 r =>
    match Nat.add (Nat.add (Nat.sub 1 x1) (Nat.sub 1 x2))
        (Nat.add (Nat.sub 1 x3) (Nat.sub 1 x4)) with
    | 0 => q4AP r
    | _ + 1 => false
private theorem pos1_false {x : ℕ} (h : (1 - x) = 0) : Nat.ble x 0 = false := by
  cases x with
  | zero => cases h
  | succ _ => rfl
private theorem q4AP_pos : ∀ (w : Q4), q4AP w = true → bAllPos (q4L w) = true
  | Q4.tail _, h => h
  | Q4.c4 x1 x2 x3 x4 r, h => by
    dsimp only [q4AP] at h; revert h
    cases hs : Nat.add (Nat.add (Nat.sub 1 x1) (Nat.sub 1 x2))
        (Nat.add (Nat.sub 1 x3) (Nat.sub 1 x4)) with
    | succ _ => intro h; dsimp only at h; cases h
    | zero =>
      intro h; dsimp only at h; simp only [Nat.add_eq, Nat.sub_eq] at hs
      have h1 : 1 - x1 = 0 := by omega
      have h2 : 1 - x2 = 0 := by omega
      have h3 : 1 - x3 = 0 := by omega
      have h4 : 1 - x4 = 0 := by omega
      dsimp only [q4L, bAllPos]
      rw [pos1_false h1, pos1_false h2, pos1_false h3, pos1_false h4]
      exact q4AP_pos r h
private def bChkV (out : Q4) : Option Q4 :=
  match out with
  | Q4.tail xs => cond (bAllPos xs) (some (Q4.tail xs)) none
  | Q4.c4 x1 x2 x3 x4 r =>
    cond (q4AP (Q4.c4 x1 x2 x3 x4 r)) (some (Q4.c4 x1 x2 x3 x4 r)) none
private theorem bChkV_eq (out : Q4) : bChkV out = cond (q4AP out) (some out) none := by
  cases out <;> rfl
private theorem cond_some_eq {α : Type} {b : Bool} {x y : α}
    (h : cond b (some x) none = some y) : b = true ∧ x = y := by
  cases b with
  | false => cases h
  | true => dsimp only [cond] at h; injection h with h'; exact ⟨rfl, h'⟩
private def bSlQ4 (z d rT : ℕ) : ℕ → ℕ → ℕ → HbZ4 → Q4 → Q4 → Q4
  | 0, p0, q0, hbz, vs, cs => toQ4 (bSlZ z d rT p0 q0 (takeH4 1 hbz) (q4L vs) (q4L cs))
  | q + 1, p0, q0, hbz, vs, cs =>
    match hbz with
    | HbZ4.tail l =>
      toQ4 (bSlZ z d (Nat.add (Nat.mul 4 (Nat.add q 1)) rT) p0 q0 l (q4L vs) (q4L cs))
    | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR =>
      match vs with
      | Q4.tail [] =>
        match cs with
        | Q4.tail [] =>
          fN (bStepVal z (Nat.add p0 z1) (Nat.add z1 q0) d) fun y => Q4.tail [y]
        | Q4.tail (c1 :: cxs) =>
          toQ4 (bSlZ z d (Nat.add (Nat.mul 4 (Nat.add q 1)) rT) p0 q0
            (takeH4 (Nat.add q 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR)) [] (c1 :: cxs))
        | Q4.c4 c1 c2 c3 c4 cR =>
          match Nat.add 1 (Nat.mul b4 c4) with
          | 0 => Q4.tail []
          | bc4 + 1 =>
            q4S (bStepVal z (Nat.add p0 z1) (Nat.add (Nat.mul b1 c2) q0) d)
              (bStepVal z (Nat.add (Nat.mul b1 c1) z2) (Nat.add (Nat.mul b2 c3) z1) d)
              (bStepVal z (Nat.add (Nat.mul b2 c2) z3) (Nat.add (Nat.mul b3 c4) z2) d)
              (bStepVal z (Nat.add (Nat.mul b3 c3) z4) (Nat.add (Nat.mul b4 (q4Hd z cR)) z3) d)
              (bSlQ4 z d rT q bc4 z4 bR (Q4.tail []) cR)
      | Q4.tail (v1 :: vt1) =>
        match cs with
        | Q4.tail cxs =>
          toQ4 (bSlZ z d (Nat.add (Nat.mul 4 (Nat.add q 1)) rT) p0 q0
            (takeH4 (Nat.add q 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR)) (v1 :: vt1) cxs)
        | Q4.c4 c1 c2 c3 c4 cR =>
          match vt1 with
          | [] =>
            match Nat.add 1 (Nat.mul b4 c4) with
            | 0 => Q4.tail []
            | bc4 + 1 =>
              q4S (bStepVal v1 (Nat.add p0 z1) (Nat.add (Nat.mul b1 c2) q0) d)
                (bStepVal z (Nat.add (Nat.mul b1 c1) z2) (Nat.add (Nat.mul b2 c3) z1) d)
                (bStepVal z (Nat.add (Nat.mul b2 c2) z3) (Nat.add (Nat.mul b3 c4) z2) d)
                (bStepVal z (Nat.add (Nat.mul b3 c3) z4)
                  (Nat.add (Nat.mul b4 (q4Hd z cR)) z3) d)
                (bSlQ4 z d rT q bc4 z4 bR (Q4.tail []) cR)
          | v2 :: vt2 =>
            match vt2 with
            | [] =>
              match Nat.add 1 (Nat.mul b4 c4) with
              | 0 => Q4.tail []
              | bc4 + 1 =>
                q4S (bStepVal v1 (Nat.add p0 z1) (Nat.add (Nat.mul b1 c2) q0) d)
                  (bStepVal v2 (Nat.add (Nat.mul b1 c1) z2) (Nat.add (Nat.mul b2 c3) z1) d)
                  (bStepVal z (Nat.add (Nat.mul b2 c2) z3) (Nat.add (Nat.mul b3 c4) z2) d)
                  (bStepVal z (Nat.add (Nat.mul b3 c3) z4)
                    (Nat.add (Nat.mul b4 (q4Hd z cR)) z3) d)
                  (bSlQ4 z d rT q bc4 z4 bR (Q4.tail []) cR)
            | v3 :: vt3 =>
              match vt3 with
              | [] =>
                match Nat.add 1 (Nat.mul b4 c4) with
                | 0 => Q4.tail []
                | bc4 + 1 =>
                  q4S (bStepVal v1 (Nat.add p0 z1) (Nat.add (Nat.mul b1 c2) q0) d)
                    (bStepVal v2 (Nat.add (Nat.mul b1 c1) z2) (Nat.add (Nat.mul b2 c3) z1) d)
                    (bStepVal v3 (Nat.add (Nat.mul b2 c2) z3) (Nat.add (Nat.mul b3 c4) z2) d)
                    (bStepVal z (Nat.add (Nat.mul b3 c3) z4)
                      (Nat.add (Nat.mul b4 (q4Hd z cR)) z3) d)
                    (bSlQ4 z d rT q bc4 z4 bR (Q4.tail []) cR)
              | v4 :: vt4 =>
                toQ4 (bSlZ z d (Nat.add (Nat.mul 4 (Nat.add q 1)) rT) p0 q0
                  (takeH4 (Nat.add q 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR))
                  (v1 :: v2 :: v3 :: v4 :: vt4) (c1 :: c2 :: c3 :: c4 :: q4L cR))
      | Q4.c4 v1 v2 v3 v4 vR =>
        match cs with
        | Q4.tail cxs =>
          toQ4 (bSlZ z d (Nat.add (Nat.mul 4 (Nat.add q 1)) rT) p0 q0
            (takeH4 (Nat.add q 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR))
            (v1 :: v2 :: v3 :: v4 :: q4L vR) cxs)
        | Q4.c4 c1 c2 c3 c4 cR =>
          match Nat.add 1 (Nat.mul b4 c4) with
          | 0 => Q4.tail []
          | bc4 + 1 =>
            q4S (bStepVal v1 (Nat.add p0 z1) (Nat.add (Nat.mul b1 c2) q0) d)
              (bStepVal v2 (Nat.add (Nat.mul b1 c1) z2) (Nat.add (Nat.mul b2 c3) z1) d)
              (bStepVal v3 (Nat.add (Nat.mul b2 c2) z3) (Nat.add (Nat.mul b3 c4) z2) d)
              (bStepVal v4 (Nat.add (Nat.mul b3 c3) z4) (Nat.add (Nat.mul b4 (q4Hd z cR)) z3) d)
              (bSlQ4 z d rT q bc4 z4 bR vR cR)
private theorem bSlQ4_eq (z d rT : ℕ) (hr : rT ≤ 4) :
    ∀ (q p0 q0 : ℕ) (hbz : HbZ4) (vs cs : Q4),
    q4L (bSlQ4 z d rT q p0 q0 hbz vs cs) =
      bSlZ z d (4 * q + rT) p0 q0 (hbz4L hbz) (q4L vs) (q4L cs)
  | 0, p0, q0, hbz, vs, cs => by
    dsimp only [bSlQ4]; rw [q4L_toQ4]
    have h0 : 4 * 0 + rT = rT := by omega
    rw [h0]; exact bSlZ_takeH4 z d 1 hbz rT p0 q0 (q4L vs) (q4L cs) hr
  | q + 1, p0, q0, hbz, vs, cs => by
    have hrem : Nat.add (Nat.mul 4 (Nat.add q 1)) rT = 4 * (q + 1) + rT := by
      simp only [Nat.add_eq, Nat.mul_eq]
    have hq2 : Nat.add q 2 = q + 2 := by rw [Nat.add_eq]
    have hle : 4 * (q + 1) + rT ≤ 4 * (q + 2) := by omega
    have h4 : 4 * (q + 1) + rT = ((((4 * q + rT) + 1) + 1) + 1) + 1 := by omega
    cases hbz with
    | tail l => dsimp only [bSlQ4, hbz4L]; rw [q4L_toQ4, hrem]
    | c4 b1 z1 b2 z2 b3 z3 b4 z4 bR =>
      cases vs with
      | tail vxs =>
        cases vxs with
        | nil =>
          cases cs with
          | tail cxs =>
            cases cxs with
            | nil =>
              dsimp only [bSlQ4, fN]; rw [rkmb_forceNat_eq, h4]
              dsimp only [hbz4L, hbz4C, q4L, bSlZ]; rw [uC_eq]
            | cons c1 ct =>
              dsimp only [bSlQ4]; rw [q4L_toQ4, hrem, hq2]
              exact bSlZ_takeH4 z d (q + 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR)
                (4 * (q + 1) + rT) p0 q0 [] (c1 :: ct) hle
          | c4 c1 c2 c3 c4 cR =>
            dsimp only [bSlQ4]; rw [n1a (Nat.mul b4 c4)]; dsimp only; rw [q4S_eq, q4Hd_eq, h4]
            dsimp only [hbz4L, hbz4C, q4L, bSlZ, bHO]
            rw [uC_eq, uC_eq, uC_eq, uC_eq]
            rw [bSlQ4_eq z d rT hr q (Nat.mul b4 c4) z4 bR (Q4.tail []) cR]; rfl
        | cons v1 vt1 =>
          cases cs with
          | tail cxs =>
            dsimp only [bSlQ4, q4L]; rw [q4L_toQ4, hrem, hq2]
            exact bSlZ_takeH4 z d (q + 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR)
              (4 * (q + 1) + rT) p0 q0 (v1 :: vt1) cxs hle
          | c4 c1 c2 c3 c4 cR =>
            cases vt1 with
            | nil =>
              dsimp only [bSlQ4]; rw [n1a (Nat.mul b4 c4)]; dsimp only; rw [q4S_eq, q4Hd_eq, h4]
              dsimp only [hbz4L, hbz4C, q4L, bSlZ, bHO]
              rw [uC_eq, uC_eq, uC_eq, uC_eq]
              rw [bSlQ4_eq z d rT hr q (Nat.mul b4 c4) z4 bR (Q4.tail []) cR]; rfl
            | cons v2 vt2 =>
              cases vt2 with
              | nil =>
                dsimp only [bSlQ4]; rw [n1a (Nat.mul b4 c4)]; dsimp only; rw [q4S_eq, q4Hd_eq, h4]
                dsimp only [hbz4L, hbz4C, q4L, bSlZ, bHO]
                rw [uC_eq, uC_eq, uC_eq, uC_eq]
                rw [bSlQ4_eq z d rT hr q (Nat.mul b4 c4) z4 bR (Q4.tail []) cR]; rfl
              | cons v3 vt3 =>
                cases vt3 with
                | nil =>
                  dsimp only [bSlQ4]; rw [n1a (Nat.mul b4 c4)]; dsimp only; rw [q4S_eq, q4Hd_eq, h4]
                  dsimp only [hbz4L, hbz4C, q4L, bSlZ, bHO]
                  rw [uC_eq, uC_eq, uC_eq, uC_eq]
                  rw [bSlQ4_eq z d rT hr q (Nat.mul b4 c4) z4 bR (Q4.tail []) cR]; rfl
                | cons v4 vt4 =>
                  dsimp only [bSlQ4, q4L]; rw [q4L_toQ4, hrem, hq2]
                  exact bSlZ_takeH4 z d (q + 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR)
                    (4 * (q + 1) + rT) p0 q0 (v1 :: v2 :: v3 :: v4 :: vt4)
                    (c1 :: c2 :: c3 :: c4 :: q4L cR) hle
      | c4 v1 v2 v3 v4 vR =>
        cases cs with
        | tail cxs =>
          dsimp only [bSlQ4]; rw [q4L_toQ4, hrem, hq2]
          exact bSlZ_takeH4 z d (q + 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR)
            (4 * (q + 1) + rT) p0 q0 (v1 :: v2 :: v3 :: v4 :: q4L vR) cxs hle
        | c4 c1 c2 c3 c4 cR =>
          dsimp only [bSlQ4]; rw [n1a (Nat.mul b4 c4)]; dsimp only; rw [q4S_eq, q4Hd_eq, h4]
          dsimp only [hbz4L, hbz4C, q4L, bSlZ, bHO]
          rw [uC_eq, uC_eq, uC_eq, uC_eq]
          rw [bSlQ4_eq z d rT hr q (Nat.mul b4 c4) z4 bR vR cR]
private def bStg (z dg mL cL : ℕ) (h4 : HbZ4) (vs cs : Q4) : Option Q4 :=
  fN (rkmNextLen mL cL) fun nL => fN (Nat.div nL 4) fun q4 => fN (Nat.mod nL 4) fun rT =>
    fN (Nat.mul dg wdScale) fun d => bChkV (bSlQ4 z d rT q4 0 0 h4 vs cs)
private theorem bStg_zPad {z dg mL cL : ℕ} {b : List ℕ} {vs cs out : Q4}
    (h : bStg z dg mL cL (toH4 (mkHbZ z b)) vs cs = some out) :
    bAllPos (q4L out) = true ∧
      zPad z (rkmNextLen mL cL) (q4L out) =
        bSl z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b (q4L vs) (q4L cs) := by
  unfold bStg at h; dsimp only [fN] at h
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceNat_eq, bChkV_eq] at h
  rcases cond_some_eq h with ⟨hv, rfl⟩
  have hp := q4AP_pos _ hv
  refine ⟨hp, ?_⟩
  have hr : Nat.mod (rkmNextLen mL cL) 4 ≤ 4 := by rw [nmod]; omega
  have hqr : 4 * Nat.div (rkmNextLen mL cL) 4 + Nat.mod (rkmNextLen mL cL) 4 =
      rkmNextLen mL cL := by rw [ndiv, nmod]; omega
  have hsl := bSlZ_zPad z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b (q4L vs) (q4L cs)
  rw [hzMul0 z] at hsl
  rw [bSlQ4_eq _ _ _ hr, hqr, hbz4L_toH4]
  exact hsl
private theorem bStg_sound {z : ℕ} (hz : Nat.ble z 0 = false) (dg mL vL cL : ℕ)
    (b : List ℕ) (vs cs out : Q4)
    (h : bStg z dg mL cL (toH4 (mkHbZ z b)) vs cs = some out) :
    bDec z (zPad z (rkmNextLen mL cL) (q4L out)) =
      rkmUltraHornerStage dg mL cL (uOfHb b)
        (bDec z (zPad z vL (q4L vs))) (bDec z (zPad z cL (q4L cs))) := by
  rcases bStg_zPad h with ⟨hp, hsl⟩
  have hpos : bAllPos (bSl z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b
      (zPad z vL (q4L vs)) (zPad z cL (q4L cs))) = true := by
    rw [bSl_zPad, ← hsl]; exact bAllPos_zPad hz _ _ hp
  unfold rkmUltraHornerStage
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, hsl,
    ← bSl_zPad z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z vL cL b (q4L vs) (q4L cs)]
  have hs := bSl_sound z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b
    (zPad z vL (q4L vs)) (zPad z cL (q4L cs)) hpos
  rw [bM0 z] at hs; exact hs
private def bStg1 (z mL cL : ℕ) (h4 : HbZ4) (vs cs : Q4) : Option Q4 :=
  match bStg z 1 mL cL h4 vs cs with
  | none => none
  | some raw => fL (bTrim z (q4L raw)) fun tr => some (toQ4 tr)
private theorem bStg1_sound {z : ℕ} (hz : Nat.ble z 0 = false) (mL vL cL : ℕ)
    (b : List ℕ) (vs cs out : Q4)
    (h : bStg1 z mL cL (toH4 (mkHbZ z b)) vs cs = some out) :
    bDec z (zPad z (rkmNextLen mL cL) (q4L out)) =
      rkmUltraHornerStage 1 mL cL (uOfHb b)
        (bDec z (zPad z vL (q4L vs))) (bDec z (zPad z cL (q4L cs))) := by
  unfold bStg1 at h; revert h
  cases hd : bStg z 1 mL cL (toH4 (mkHbZ z b)) vs cs with
  | none => intro h; dsimp only at h; cases h
  | some raw =>
    intro h; dsimp only [fL] at h; rw [rkmb_forceList_eq] at h
    injection h with h'; subst h'; rw [q4L_toQ4]
    rcases bStg_zPad hd with ⟨_, hsl⟩
    have hpad := zPad_bTrim_len z
      (bSl z (Nat.mul 1 wdScale) (rkmNextLen mL cL) 0 z b (q4L vs) (q4L cs))
    rw [bSl_len] at hpad
    rw [← bTrim_zPad z (rkmNextLen mL cL) (q4L raw), hsl, hpad, ← hsl]
    exact bStg_sound hz 1 mL vL cL b vs cs raw hd
private def bBdD (z g m c : ℕ) (h4 : HbZ4) (vs cs : Q4)
    (k : ℕ → Q4 → Option Q4) : Option Q4 :=
  fN (rkmNextLen m c) fun n =>
    match bStg z g m c h4 vs cs with
    | none => none
    | some o => k n o
private theorem bBdD_sound {z : ℕ} (hz : Nat.ble z 0 = false) {endL g m vL c : ℕ}
    {b : List ℕ} {vs cs out : Q4} {kB : ℕ → Q4 → Option Q4} {kU : ℕ → List ℤ → List ℤ}
    (h : bBdD z g m c (toH4 (mkHbZ z b)) vs cs kB = some out)
    (hk : ∀ (m0 : Q4), kB (rkmNextLen m c) m0 = some out →
      bDec z (zPad z endL (q4L out)) =
        kU (rkmNextLen m c) (bDec z (zPad z (rkmNextLen m c) (q4L m0)))) :
    bDec z (zPad z endL (q4L out)) =
      (HighDForce.withForcedNat (rkmNextLen m c) fun nL => HighDForce.withForcedList
        (rkmUltraHornerStage g m c (uOfHb b)
          (bDec z (zPad z vL (q4L vs))) (bDec z (zPad z c (q4L cs)))) (kU nL)) := by
  unfold bBdD at h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h; revert h
  cases hs : bStg z g m c (toH4 (mkHbZ z b)) vs cs with
  | none => intro h; dsimp only at h; cases h
  | some mid =>
    intro h; rw [rkmb_forceNat_eq, rkmb_forceList_eq, ← bStg_sound hz g m vL c b vs cs mid hs]
    exact hk mid h
private def bSpD (z m c : ℕ) (h4 : HbZ4) (vs : Q4) : Option Q4 :=
  bBdD z 16 m c h4 vs vs fun l x => bBdD z 15 m l h4 vs x fun l x =>
  bBdD z 14 m l h4 vs x fun l x => bBdD z 13 m l h4 vs x fun l x =>
  bBdD z 12 m l h4 vs x fun l x => bBdD z 11 m l h4 vs x fun l x =>
  bBdD z 10 m l h4 vs x fun l x => bBdD z 9 m l h4 vs x fun l x =>
  bBdD z 8 m l h4 vs x fun l x => bBdD z 7 m l h4 vs x fun l x =>
  bBdD z 6 m l h4 vs x fun l x => bBdD z 5 m l h4 vs x fun l x =>
  bBdD z 4 m l h4 vs x fun l x => bBdD z 3 m l h4 vs x fun l x =>
  bBdD z 2 m l h4 vs x fun l x => bStg1 z m l h4 vs x
private theorem bSpD_sound {z : ℕ} (hz : Nat.ble z 0 = false) (mL cL : ℕ)
    (b : List ℕ) (vs out : Q4)
    (h : bSpD z mL cL (toH4 (mkHbZ z b)) vs = some out) :
    bDec z (zPad z (rkmNextLen16 mL cL) (q4L out)) =
      rkmUltraHornerT16Step mL cL (uOfHb b) (bDec z (zPad z cL (q4L vs))) := by
  unfold bSpD at h; unfold rkmUltraHornerT16Step
  refine bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => ?_
  refine bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => ?_
  refine bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => ?_
  refine bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => ?_
  refine bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => ?_
  unfold rkmNextLen16; exact bStg1_sound hz mL cL _ b vs _ out h
private def bItD (z : ℕ) : ℕ → ℕ → ℕ → HbZ4 → Q4 → Option (ℕ × Q4)
  | 0, _, c, _, vs => some (c, vs)
  | k + 1, m, c, h4, vs =>
    match bSpD z m c h4 vs with
    | none => none
    | some vN => fN (rkmNextLen16 m c) fun nL => bItD z k m nL h4 vN
private theorem bItD_sound {z : ℕ} (hz : Nat.ble z 0 = false) :
    ∀ (k m c : ℕ) (b : List ℕ) (vs : Q4) (endL : ℕ) (outV : Q4),
      bItD z k m c (toH4 (mkHbZ z b)) vs = some (endL, outV) →
        bDec z (zPad z endL (q4L outV)) =
          muxUltraIterFullT16Rkm k m c (uOfHb b) (bDec z (zPad z c (q4L vs)))
  | 0, _, _, _, _, _, _, h => by
    injection h with h'; injection h' with hc hv; subst hc; subst hv; rfl
  | k + 1, m, c, b, vs, endL, outV, h => by
    unfold bItD at h; revert h
    cases hs : bSpD z m c (toH4 (mkHbZ z b)) vs with
    | none => intro h; dsimp only at h; cases h
    | some vN =>
      intro h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h
      unfold muxUltraIterFullT16Rkm
      rw [rkmb_forceList_eq, rkmb_forceNat_eq, ← bSpD_sound hz m c b vs vN hs]
      exact bItD_sound hz k m _ b vN endL outV h
private theorem u2f {s m : ℕ} {b u v : List ℤ}
    (h : muxUltraIterFullT16Rkm s m (altIntLen u) b u = v) :
    muxFastIterFullT16 s m b u = v := by
  have hc : muxUltraIterFullT16HiChk s 0 m b u v = true := by
    unfold muxUltraIterFullT16HiChk; dsimp only
    rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceNat_eq, h]
    exact muxIntListEq_eq_true.mpr rfl
  exact muxUltraIterFullT16HiChk_sound hc
private def bWalkOk (k mL : ℕ) (bns : List ℕ) (l0 : ℕ) (uT : List ℕ) (l1 : ℕ) (vT : List ℕ) :
    Prop :=
  muxFastIterFullT16 k mL (uOfHb bns) (bDec bZ (zPad bZ l0 uT)) = bDec bZ (zPad bZ l1 vT)
private def bSlideChk (steps mL : ℕ) (bns : List ℕ) (l0 : ℕ) (uT : List ℕ)
    (l1 : ℕ) (vT : List ℕ) : Bool :=
  fL bns fun bF => fL uT fun uF => fL vT fun vF =>
    cond (Nat.ble (bNL uF) l0)
      (fH4 (toH4 (mkHbZ bZ bF)) fun h4 =>
        fQ4 (toQ4 uF) fun uV =>
          match bItD bZ steps mL l0 h4 uV with
          | none => false
          | some (endL, outV) =>
            cond (muxNatListEq [endL] [l1]) (muxNatListEq (q4L outV) vF) false)
      false
private theorem bSlideChk_s {steps mL : ℕ} {bns : List ℕ} {l0 : ℕ} {uT : List ℕ}
    {l1 : ℕ} {vT : List ℕ} (h : bSlideChk steps mL bns l0 uT l1 vT = true) :
    bWalkOk steps mL bns l0 uT l1 vT := by
  unfold bSlideChk at h; unfold bWalkOk; dsimp only [fL] at h
  rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq] at h
  revert h; cases hle : Nat.ble (bNL uT) l0 with
  | false => intro h; dsimp only [cond] at h; exact Bool.noConfusion h
  | true =>
    intro h; dsimp only [cond] at h; rw [fH4e, fQ4e] at h; revert h
    cases hi : bItD bZ steps mL l0 (toH4 (mkHbZ bZ bns)) (toQ4 uT) with
    | none => intro h; dsimp only at h; exact Bool.noConfusion h
    | some p =>
      cases p with
      | mk endL outV =>
        intro h; dsimp only at h; revert h
        cases he : muxNatListEq [endL] [l1] with
        | false => intro h; dsimp only [cond] at h; exact Bool.noConfusion h
        | true =>
          intro h; dsimp only [cond] at h
          have hl1 : endL = l1 := (List.cons.inj (muxNatListEq_eq_true.mp he)).1
          have hot : q4L outV = vT := muxNatListEq_eq_true.mp h
          have hit := bItD_sound hbZ0 steps mL l0 bns (toQ4 uT) endL outV hi
          rw [q4L_toQ4, hl1, hot] at hit
          have hln : altIntLen (bDec bZ (zPad bZ l0 uT)) = l0 := by
            rw [← bNL_eq bZ]; exact zPad_bNL bZ l0 uT hle
          exact u2f (by rw [hln]; exact hit.symm)
private theorem bWalk1 {k mL : ℕ} {bns : List ℕ} {l0 : ℕ} {v0 : List ℕ} {l1 : ℕ} {v1 : List ℕ}
    (h : bSlideChk k mL bns l0 v0 l1 v1 = true) : bWalkOk k mL bns l0 v0 l1 v1 :=
  bSlideChk_s h
private theorem bChn {a b ab mL : ℕ} {bns : List ℕ} {l0 : ℕ} {v0 : List ℕ}
    {l1 : ℕ} {v1 : List ℕ} {l2 : ℕ} {v2 : List ℕ} (hab : a + b = ab)
    (h1 : bWalkOk a mL bns l0 v0 l1 v1) (h2 : bSlideChk b mL bns l1 v1 l2 v2 = true) :
    bWalkOk ab mL bns l0 v0 l2 v2 := by
  unfold bWalkOk at h1 ⊢; subst hab
  exact (muxFastIterFullT16_add a b mL (uOfHb bns) (bDec bZ (zPad bZ l0 v0))).trans
    ((congrArg (muxFastIterFullT16 b mL (uOfHb bns)) h1).trans (bSlideChk_s h2))
private theorem bSeg_mk {n d ml : ℕ} {bns : List ℕ} {l0 : ℕ} {v0 : List ℕ} {l1 : ℕ} {v1 : List ℕ}
    (hd : d = ml) (hw : bWalkOk n ml bns l0 v0 l1 v1) :
    muxFastIterFullT16 n d (uOfHb bns) (bDec bZ (zPad bZ l0 v0)) = bDec bZ (zPad bZ l1 v1) := by
  subst hd; exact hw
private theorem rkmHd {b : Bool} {bs : List Bool} (h : rkmAllTrueF (b :: bs) = true) :
    b = true := (rkmAllTrueF_cons h).1
private theorem rkmTl {b : Bool} {bs : List Bool} (h : rkmAllTrueF (b :: bs) = true) :
    rkmAllTrueF bs = true := (rkmAllTrueF_cons h).2
private def phb_m16_r384_0 : List ℕ :=
  [334412648353966, 457316747485019, 540397608446410, 600511393058614, 644205628838479,
    674758966652287, 693988080953667, 702900763459942, 701967915320366, 691228674077414,
    670293272543055, 638244576122125, 593376350916034, 532560181208607, 449488496024057,
    327816090109404]
private def pvn_m16_r384_0_0 : List ℕ := [3000000000000000]
private def pvn_m16_r384_0_1 : List ℕ :=
  [2798711685294403, 2539433924279555, 2249100596106117, 2090615024578584, 2027471263644304,
    2007147171370440, 2001622992608582, 2000324892235211, 2000057636296356, 2000009076270130,
    2000001266629627, 2000000155821072, 2000000016730940, 2000000001541627, 2000000000118378,
    2000000000007159, 2000000000000295]
private def phb_m16_r384_1 : List ℕ :=
  [304101577969256, 415865683389939, 491416117985527, 546081205709498, 585815007987076,
    613598999672618, 631085192347398, 639190031764920, 638341736723907, 628575897350758,
    609538074848065, 580394263447885, 539592881822481, 484289072994954, 408746982486322,
    298102929947982]
private def pvn_m16_r384_1_0 : List ℕ :=
  [1201288314705597, 2539433924279555, 2249100596106117, 1909384975421416, 1972528736355696,
    2007147171370440, 2001622992608582, 1999675107764789, 1999942363703644, 2000009076270130,
    2000001266629627, 1999999844178928, 2000000016730940, 2000000001541627, 1999999999881622,
    2000000000007159, 2000000000000295]
private def pvn_m16_r384_1_1 : List ℕ :=
  [1817895213396263, 1562919181751827, 1402215694470361, 1470974412852551, 1720486959952879,
    1984512056311552, 2135550042693720, 2158834274382794, 2112824849097868, 2057976142265401,
    2022097051638316, 2005903115043215, 2000815889426066, 1999873794099034, 1999891537197652,
    1999968723500323, 1999995302502664]
private def phb_m16_r384_2_p0 : List ℕ :=
  [118926083354427, 167529756866786, 204376048976836, 235063000437240, 261768036183361,
    285612310952293, 307264425811266, 327161674659589, 345608948310443, 362829064053032,
    378990852222099, 394225957016372, 408639447518033, 422316819116953, 435328782764303,
    447734641549801, 459584733346333, 470922237466914, 481784536992547, 492204263646484,
    502210111342582, 511827478187618, 521078979258618, 529984860652235, 538563337136791,
    546830869996533, 554802397556316, 562491527901578, 569910701123898, 577071326797302,
    583983901167808, 590658107608940, 597102903182127, 603326593587707, 609336898359978,
    615141007819250, 620745633023577, 626157049746909, 631381137336666, 636423413163066,
    641289063258082, 645982969648094, 650509734807152, 654873703593947, 659078982982493,
    663129459852255, 667028817066320, 670780548034908, 674387969935121, 677854235735400,
    681182345154042, 684375154664858, 687435386649033, 690365637780267, 693168386719862,
    695846001189496, 698400744481606, 700834781460572, 703150184101953, 705348936611909,
    707432940164388, 709404017289704, 711263915944631, 713014313291055]
private def phb_m16_r384_2_p1 : List ℕ :=
  [714656819207485, 716192979555336, 717624279219708, 718952144942518, 720177947964111,
    721303006487964, 722328587981746, 723255911326759, 724086148826706, 724820428085739,
    725459833764855, 726005409224905, 726458158063759, 726819045554500, 727088999990948,
    727268913946250, 727359645449787, 727362019087196, 727276827027899, 727104829984135,
    726846758105167, 726503311809994, 726075162561615, 725562953585606, 724967300535542,
    724288792107514, 723527990605826, 722685432461690, 721761628706588, 720757065401768,
    719672204025141, 718507481816729, 717263312083594, 715940084465073, 714538165158953,
    713057897109100, 711499600154885, 709863571142634, 708150083999154, 706359389767269,
    704491716603137, 702547269734975, 700526231382672, 698428760637603, 696254993301806,
    694005041685497, 691678994361743, 689276915876897, 686798846415235, 684244801415972,
    681614771140668, 678908720188734, 676126586958524, 673268283051192, 670333692614191,
    667322671620961, 664235047082958, 661070616189818, 657829145372958, 654510369287465,
    651113989706563, 647639674322373, 644087055446009, 640455728599317]
private def phb_m16_r384_2_p2 : List ℕ :=
  [636745250989770, 632955139859105, 629084870695289, 625133875296237, 621101539672483,
    616987201774513, 612790149028896, 608509615665511, 604144779816112, 599694760362128,
    595158613506940, 590535329044859, 585823826295552, 581022949668725, 576131463819325,
    571148048348269, 566071291997734, 560899686282993, 555631618494743, 550265363996396,
    544799077729833, 539230784830188, 533558370235085, 527779567155848, 521891944257033,
    515892891365403, 509779603499438, 503549062974376, 497198019294387, 490722966490904,
    484120117502265, 477385375111666, 470514298864391, 463502067266544, 456343434419690,
    449032680060777, 441563551743234, 433929197598509, 426122087737357, 418133921859366,
    409955519999376, 401576692497159, 392986084156186, 384170986049499, 375117106376628,
    365808288939335, 356226163830246, 346349709270506, 336154695332814, 325612968167321,
    314691515041308, 303351222165001, 291545192178969, 279216414119823, 266294452583416,
    252690598885079, 238290509195077, 222942527332204, 206438128554985, 188476813031239,
    168596992483780, 146021102542389, 119232166732352, 84312148925798]
private def phb_m16_r384_2 : List ℕ :=
  pCat phb_m16_r384_2_p0
    (pCat phb_m16_r384_2_p1
      phb_m16_r384_2_p2)
private def pvn_m16_r384_2_0 : List ℕ :=
  [1817895213396263, 1562919181751827, 1402215694470361, 1470974412852551, 1720486959952879,
    2015487943688448, 2135550042693720, 2158834274382794, 2112824849097868, 1942023857734599,
    1977902948361684, 1994096884956785, 2000815889426066, 1999873794099034, 2000108462802348,
    1999968723500323, 1999995302502664]
private def pvn_m16_r384_2_1 : List ℕ :=
  [1997144819321036, 1989725573135746, 1924264490218253, 1830455527725516, 1747439909871874,
    1546877769050385, 1511497719480242, 1551939590714904, 1611282059839877, 1740330675690125,
    1919970065035387, 2062636403059779, 2117296086752976, 2101148144460429, 2058918664021656,
    2022768014154026, 2002721968775436, 1995563469017025, 1994996990301870, 1996517730469978,
    1998055661591076, 1999059947957553, 1999591774744242, 1999837030488223, 1999939099329877,
    1999978352046171, 1999992570715448, 1999997506245806, 1999999173474665, 1999999728288322,
    1999999911464383, 1999999971532131, 1999999991021801, 1999999997238840, 1999999999175733,
    1999999999761893, 1999999999933558, 1999999999982107, 1999999999995350, 1999999999998835,
    1999999999999720, 1999999999999936, 1999999999999987, 1999999999999999]
private def pvn_m16_r384_2_2 : List ℕ :=
  [1995857711949919, 1995252465156556, 2034917973606576, 1965545764029332, 1961406948814070,
    1962763331809665, 1876756802135934, 1751712701277840, 1660908401334963, 1608185127681754,
    1572278528378340, 1563300249476103, 1609788476506871, 1716861299979549, 1853827366958360,
    1976572145871533, 2055278179451893, 2085138695321094, 2079609490563994, 2057499468966364,
    2033524710261553, 2015198713926872, 2004163726566241, 1998971020106139, 1997363021614998,
    1997470218973815, 1998139049353093, 1998817176218572, 1999320488493122, 1999638948800221,
    1999820044460851, 1999915033443778, 1999961710759884, 1999983429776187, 1999993076746194,
    1999997194173354, 1999998892404009, 1999999572610241, 1999999838319380, 1999999939905808,
    1999999978023469, 1999999992087348, 1999999997195074, 1999999999021546, 1999999999664398,
    1999999999886933, 1999999999962620, 1999999999987885, 1999999999996157, 1999999999998809,
    1999999999999640, 1999999999999895, 1999999999999972, 1999999999999994]
private def pvn_m16_r384_2_3 : List ℕ :=
  [2007941696287848, 1968459555932867, 2013917380399138, 2031889124406799, 1995811286650337,
    1973555829211975, 1990188008705101, 1999947641716989, 1961362509327882, 1883785110746334,
    1802044977768615, 1734764625249092, 1677351072093908, 1623897738401480, 1584347559867612,
    1579574580567090, 1623747667418400, 1712104849294266, 1822782720678073, 1928488410349815,
    2008555223260996, 2054830069098273, 2070577681876042, 2065436543065360, 2050076494483009,
    2032758056763390, 2018201482527001, 2008069195551425, 2002103986495610, 1999220825673917,
    1998238388272720, 1998228135242868, 1998594988321106, 1999022441754342, 1999378279226950,
    1999630989251797, 1999793059410784, 1999889438687935, 1999943386943943, 1999972087131286,
    1999986698126611, 1999993853366233, 1999997238182877, 1999998790337282, 1999999482384695,
    1999999783191708, 1999999910954113, 1999999964087085, 1999999985760415, 1999999994444233,
    1999999997865668, 1999999999192375, 1999999999698945, 1999999999889452, 1999999999960021,
    1999999999985768, 1999999999995017, 1999999999998286, 1999999999999422, 1999999999999812,
    1999999999999941, 1999999999999983, 1999999999999997]
private def pvn_m16_r384_2_4_p0 : List ℕ :=
  [2021250812474980, 1981213774377581, 1974472116939838, 2007574369458664, 2029787505738902,
    2014377096394358, 1986226281626157, 1980239805528743, 1998198027401681, 2011514576757024,
    1994315408449645, 1945649961852009, 1883158971948574, 1822882693427890, 1767827310245534,
    1712913385681348, 1657168655524477, 1610307292915960, 1588760770431868, 1605677198760173,
    1662813231960455, 1749198235199294, 1846156985880911, 1934839503101835, 2002207481008482,
    2043397201224979, 2060663001364017, 2060445290990274, 2050256105976137, 2036469242044318,
    2023329813538774, 2012950301847842, 2005847150082048, 2001613685638599, 1999481005751935,
    1998675966018961, 1998590030380341, 1998817850800850, 1999127712609656, 1999409479056119,
    1999625575707552, 1999774946844737, 1999870754212718, 1999928686060228, 1999962035511516,
    1999980435732674, 1999990213761693, 1999995237452299, 1999997740516216, 1999998953111575,
    1999999525532612, 1999999789355535, 1999999908274673, 1999999960778999, 1999999983515730,
    1999999993184314, 1999999997225782, 1999999998887752, 1999999999560594, 1999999999828904,
    1999999999934326, 1999999999975152, 1999999999990736, 1999999999996599]
private def pvn_m16_r384_2_4_p1 : List ℕ :=
  [1999999999998772, 1999999999999565, 1999999999999852, 1999999999999951, 1999999999999986,
    1999999999999998]
private def pvn_m16_r384_2_4 : List ℕ :=
  pCat pvn_m16_r384_2_4_p0
      pvn_m16_r384_2_4_p1
private def phb_m16_r384_3_p0 : List ℕ :=
  [24309504000000, 34289302047583, 41885997617950, 48239172000000, 53791477365768,
    58770543711863, 63311950484340, 67504265649811, 71409168000000, 75071681082982,
    78525881117861, 81798309484270, 84910126804562, 87878533497558, 90717740974552,
    93439656000000, 96054375502609, 98570552361329, 100995671086241, 103336259150029,
    105598051447934, 107786120013171, 109904977570170, 111958661108088, 113950800000000,
    115884672028574, 117763249847328, 119589239803754, 121365114607842, 123093141000248,
    124775403326674, 126413823736782, 128010179581411, 129566118469931, 131083171362116,
    132562764000000, 134006226930584, 135414804326568, 136789661777166, 138131893192687,
    139442526943373, 140722531334118, 141972819501056, 143194253803158, 144387649771273,
    145553779668075, 146693375704950, 147807132955491, 148895712000000, 149959741330815,
    150999819544509, 152016517343652, 153010379368063, 153981925873035, 154931654269945,
    155860040542839, 156767540553034, 157654591242421, 158521611744949, 159369004414754,
    160197155778474, 161006437418517, 161797206793314, 162569808000000]
private def phb_m16_r384_3_p1 : List ℕ :=
  [163324572484412, 164061819702799, 164781857739218, 165484983882212, 166171485164021,
    166841638865263, 167495712987780, 168133966698072, 168756650743534, 169364007843529,
    169956273057130, 170533674129227, 171096431816539, 171644760194951, 172178866949469,
    172698953647994, 173205216000000, 173697844101142, 174177022664715, 174642931240814,
    175095744424015, 175535632050279, 175962759383782, 176377287294280, 176779372425608,
    177169167355838, 177546820749609, 177912477503093, 178266278882022, 178608362653194,
    178938863209818, 179257911691066, 179565636096145, 179862161393198, 180147609623329,
    180422100000000, 180685749004072, 180938670474709, 181180975696363, 181412773482057,
    181634170253154, 181845270115785, 182046174934116, 182236984400613, 182417796103453,
    182588705591213, 182749806434998, 182901190288094, 183042946943306, 183175164388058,
    183297928857382, 183411324884885, 183515435351796, 183610341534170, 183696123148348,
    183772858394736, 183840624000000, 183899495257716, 183949546067585, 183990848973231,
    184023475198682, 184047494683565, 184062976117087, 184069986970839]
private def phb_m16_r384_3_p2 : List ℕ :=
  [184068593530486, 184058860926381, 184040853163147, 184014633148278, 183980262719793,
    183937802672977, 183887312786255, 183828851846228, 183762477671908, 183688247138176,
    183606216198505, 183516439906963, 183418972439533, 183313867114780, 183201176413872,
    183080952000000, 182953244737206, 182818104708646, 182675581234309, 182525722888210,
    182368577515074, 182204192246542, 182032613516894, 181853887078330, 181668058015804,
    181475170761445, 181275269108563, 181068396225266, 180854594667700, 180633906392914,
    180406372771378, 180172034599157, 179930932109756, 179683104985639, 179428592369448,
    179167432874916, 178899664597494, 178625325124699, 178344451546189, 178057080463579,
    177763248000000, 177462989809416, 177156341085702, 176843336571491, 176524010566796,
    176198396937423, 175866529123167, 175528440145807, 175184162616907, 174833728745421,
    174477170345119, 174114518841830, 173745805280505, 173371060332127, 172990314300436,
    172603597128514, 172210938405201, 171812367371367, 171407912926043, 170997603632397,
    170581467723586, 170159533108465, 169731827377173, 169298377806587]
private def phb_m16_r384_3_p3 : List ℕ :=
  [168859211365652, 168414354720604, 167963834240058, 167507676000000, 167045905788655,
    166578549111265, 166105631194743, 165627176992243, 165143211187622, 164653758199807,
    164158842187076, 163658487051234, 163152716441719, 162641553759602, 162125022161521,
    161603144563522, 161075943644821, 160543441851497, 160005661400095, 159462624281174,
    158914352262762, 158360866893759, 157802189507262, 157238341223824, 156669342954653,
    156095215404739, 155515979075932, 154931654269945, 154342261091310, 153747819450268,
    153148349065610, 152543869467459, 151934400000000, 151319959824154, 150700567920212,
    150076243090404, 149447003961432, 148812868986949, 148173856449995, 147529984465385,
    146881270982053, 146227733785359, 145569390499342, 144906258588941, 144238355362177,
    143565697972284, 142888303419815, 142206188554703, 141519370078286, 140827864545296,
    140131688365814, 139430857807190, 138725388995929, 138015297919543, 137300600428374,
    136581312237380, 135857448927898, 135129025949368, 134396058621032, 133658562133607,
    132916551550922, 132170041811533, 131419047730311, 130663584000000]
private def phb_m16_r384_3_p4 : List ℕ :=
  [129903665192747, 129139305761620, 128370520042080, 127597322253446, 126819726500329,
    126037746774041, 125251396953985, 124460690809019, 123665641998802, 122866264075112,
    122062570483151, 121254574562820, 120442289549984, 119625728577706, 118804904677469,
    117979830780378, 117150519718341, 116316984225231, 115479236938031, 114637290397964,
    113791157051601, 112940849251954, 112086379259554, 111227759243508, 110365001282545,
    109498117366041, 108627119395034, 107752019183221, 106872828457938, 105989558861128,
    105102221950296, 104210829199444, 103315392000000, 102415921661726, 101512429413621,
    100604926404799, 99693423705365, 98777932307274, 97858463125178, 96935026997261,
    96007634686058, 95076296879271, 94141024190567, 93201827160362, 92258716256603,
    91311701875531, 90360794342439, 89406003912410, 88447340771059, 87484815035253,
    86518436753822, 85548215908269, 84574162413461, 83596286118313, 82614596806465,
    81629104196947, 80639817944837, 79646747641908, 78649902817269, 77649292937996,
    76644927409750, 75636815577397, 74624966725612, 73609390079472]
private def phb_m16_r384_3_p5 : List ℕ :=
  [72590094805055, 71567090010014, 70540384744153, 69509988000000, 68475908713356,
    67438155763859, 66396737975519, 65351664117261, 64302942903456, 63250582994443,
    62194592997049, 61134981465098, 60071756899917, 59004927750831, 57934502415659,
    56860489241195, 55782896523691, 54701732509330, 53617005394688, 52528723327204,
    51436894405630, 50341526680482, 49242628154486, 48140206783019, 47034270474538,
    45924827091010, 44811884448338, 43695450316778, 42575532421349, 41452138442244,
    40325276015234, 39194952732062, 38061176140841, 36923953746441, 35783293010873,
    34639201353666, 33491686152249, 32340754742314, 31186414418188, 30028672433192,
    28867536000000, 27703012290989, 26535108438597, 25363831535658, 24189188635752,
    23011186753536, 21829832865083, 20645133908208, 19457096782796, 18265728351122,
    17071035438173, 15873024831960, 14671703283832, 13467077508782, 12259154185750,
    11047939957929, 9833441433059, 8615665183721, 7394617747631, 6170305627924, 4942735293443,
    3711913179018, 2477845685742, 1240539181253]
private def phb_m16_r384_3 : List ℕ :=
  pCat phb_m16_r384_3_p0
    (pCat phb_m16_r384_3_p1
    (pCat phb_m16_r384_3_p2
    (pCat phb_m16_r384_3_p3
    (pCat phb_m16_r384_3_p4
      phb_m16_r384_3_p5))))
private def pvn_m16_r384_3_0_p0 : List ℕ :=
  [1978749187525020, 1981213774377581, 1974472116939838, 2007574369458664, 2029787505738902,
    2014377096394358, 1986226281626157, 1980239805528743, 1998198027401681, 2011514576757024,
    1994315408449645, 1945649961852009, 1883158971948574, 1822882693427890, 1767827310245534,
    1712913385681348, 1657168655524477, 1610307292915960, 1588760770431868, 1605677198760173,
    1662813231960455, 1749198235199294, 1846156985880911, 1934839503101835, 2002207481008482,
    2043397201224979, 2060663001364017, 2060445290990274, 2050256105976137, 2036469242044318,
    2023329813538774, 2012950301847842, 1994152849917952, 2001613685638599, 1999481005751935,
    1998675966018961, 2001409969619659, 1998817850800850, 1999127712609656, 1999409479056119,
    1999625575707552, 1999774946844737, 1999870754212718, 1999928686060228, 1999962035511516,
    1999980435732674, 1999990213761693, 1999995237452299, 2000002259483784, 1999998953111575,
    1999999525532612, 1999999789355535, 1999999908274673, 1999999960778999, 1999999983515730,
    1999999993184314, 2000000002774218, 1999999998887752, 1999999999560594, 1999999999828904,
    2000000000065674, 1999999999975152, 1999999999990736, 1999999999996599]
private def pvn_m16_r384_3_0_p1 : List ℕ :=
  [2000000000001228, 1999999999999565, 1999999999999852, 1999999999999951, 1999999999999986,
    1999999999999998]
private def pvn_m16_r384_3_0 : List ℕ :=
  pCat pvn_m16_r384_3_0_p0
      pvn_m16_r384_3_0_p1
private def pvn_m16_r384_3_1_p0 : List ℕ :=
  [1979201336759454, 1981593835405865, 1973569687725115, 2005060712272143, 2029255430350516,
    2016712315242499, 1988412455520253, 1979631107240382, 1996015364118159, 2011551014754530,
    1999100780887100, 1954522243696975, 1893673765485439, 1833352900822750, 1778269648169185,
    1723859669805881, 1667908009588449, 1618333970813304, 1590872863474537, 1599796300345537,
    1649224363117659, 1730517806367854, 1826229458494583, 1917296394734774, 1989400255497765,
    2036038937245646, 2058103742269388, 2061275583425356, 2052918984787509, 2039685844216808,
    2026170271571057, 2016676391281520, 1995857773180835, 2001012038248746, 1999838357845268,
    1998447727325012, 2001356474528328, 1999126348364901, 1999073965140631, 1999341190444497,
    1999573138261668, 1999738906244414, 1999847686074542, 1999914732119272, 1999953986734636,
    1999975978685519, 1999987885888784, 1999993350295784, 2000001546442195, 1999999319443960,
    1999999433631527, 1999999726066872, 1999999878529416, 1999999947523813, 1999999977807480,
    1999999989859339, 2000000001600445, 1999999999316962, 1999999999455161, 1999999999741604,
    2000000000034728, 1999999999985115, 1999999999988297, 1999999999994726]
private def pvn_m16_r384_3_1_p1 : List ℕ :=
  [2000000000000582, 1999999999999745, 1999999999999807, 1999999999999926, 1999999999999977,
    1999999999999996]
private def pvn_m16_r384_3_1 : List ℕ :=
  pCat pvn_m16_r384_3_1_p0
      pvn_m16_r384_3_1_p1
private def phb_m16_r384_4_p0 : List ℕ :=
  [92076031999488, 129876071209572, 158649738678375, 182713375998984, 203743597205037,
    222602586356383, 239803871718078, 255682918255921, 270473343998496, 284345682645439,
    297429003183125, 309823835220074, 321610327908685, 332853630513779, 343607570968710,
    353917247998032, 363820905291572, 373351316975822, 382536831798236, 391402173578098,
    399969064124203, 408256714552195, 416282217508592, 424060863718493, 431606399997600,
    438931241458203, 446046647488417, 452962868800815, 459689271169549, 466234440227836,
    472606270759612, 478812043206049, 484858489560224, 490751850399206, 496497924471540,
    502102111997208, 507569452630179, 512904658868296, 518112145562227, 523196056067608,
    528160285496880, 533008501455615, 537744162589116, 542370535216287, 546890708287205,
    551307606867017, 555624004320363, 559842533346728, 563965695996864, 567995872783380,
    571935330984012, 575786232223613, 579550639410313, 583230523092054, 586827767291884,
    590344174873496, 593781472482622, 597141315104717, 600425290274882, 603634921972059,
    606771674226088, 609836954463201, 612832116612868, 615758463996576]
private def phb_m16_r384_4_p1 : List ℕ :=
  [618617252017047, 621409690664571, 624136946855489, 626800146616458, 629400377126777,
    631938688629970, 634416096224749, 636833581544590, 639192094334301, 641492553931267,
    643735850658330, 645922847134726, 648054379510907, 650131258632623, 652154271139179,
    654124180500383, 656041727996352, 657907633643982, 659722597073633, 661487298359259,
    663202398805001, 664868541691014, 666486352981095, 668056441994501, 669579402044145,
    671055811043236, 672486232082250, 673871213977998, 675211291796441, 676506987350776,
    677758809676216, 678967255482795, 680132809587438, 681255945326454, 682337124949522,
    683376799996200, 684375411655888, 685333391112142, 686251159872155, 687129130082202,
    687967704829762, 688767278433018, 689528236718365, 690250957286545, 690935809767967,
    691583156067754, 692193350601029, 692766740518894, 693303665925576, 693804460087147,
    694269449632218, 694698954744993, 695093289351029, 695452761296044, 695777672518089,
    696068319213389, 696324991996128, 696547976052462, 696737551289006, 696893992476039,
    697017569385654, 697108546925085, 697167185265397, 697193739965749]
private def phb_m16_r384_4_p2 : List ℕ :=
  [697188462093420, 697151598339760, 697083391132250, 696984078742822, 696853895392598,
    696693071353187, 696501833044684, 696280403130497, 696029000609136, 695747840903073,
    695437135944794, 695097094260156, 694727921049137, 694329818264099, 693902984685641,
    693447615996144, 692963904851087, 692452040948226, 691912211094696, 691344599272140,
    690749386699914, 690126751896439, 689476870738787, 688799916520536, 688096060007973,
    687365469494704, 686608310854711, 685824747593930, 685014940900384, 684179049692930,
    683317230668670, 682429638349054, 681516425124741, 680577741299250, 679613735131429,
    678624552876805, 677610338827833, 676571235353085, 675507382935417, 674418920209146,
    673305983996256, 672168709341689, 671007229547725, 669821676207496, 668612179237647,
    667378866910189, 666121865883552, 664841301232867, 663537296479511, 662209973619915,
    660859453153687, 659485854111042, 658089294079577, 656669889230406, 655227754343672,
    653763002833453, 652275746772092, 650766096913942, 649234162718574, 647680052373441,
    646103872816020, 644505729755449, 642885727693672, 641243969946104]
private def phb_m16_r384_4_p3 : List ℕ :=
  [639580558661837, 637895594843380, 636189178365974, 634461407996472, 632712381411801,
    630942195217029, 629150944963021, 627338725163733, 625505629313116, 623651749901662,
    621777178432605, 619882005437761, 617966320493051, 616030212233684, 614073768369029,
    612097075697175, 610100220119190, 608083286653087, 606046359447500, 603989521795085,
    601912856145646, 599816444118994, 597700366517555, 595564703338714, 593409533786925,
    591234936285568, 589040988488587, 586827767291884, 584595348844501, 582343808559581,
    580073221125116, 577783660514485, 575475199996800, 573147912147039, 570801868856004,
    568437141340071, 566053800150774, 563651915184200, 561231555690207, 558792790281478,
    556335686942401, 553860313037789, 551366735321436, 548855019944524, 546325232463869,
    543777437850022, 541211700495225, 538628084221222, 536026652286929, 533407467395974,
    530770591704094, 528116086826410, 525444013844570, 522754433313767, 520047405269638,
    517322989235037, 514581244226701, 511822228761790, 509046000864322, 506252618071499,
    503442137439921, 500614615551697, 497770108520455, 494908671997248]
private def phb_m16_r384_4_p4 : List ℕ :=
  [492030361176362, 489135230801033, 486223335169056, 483294728138318, 480349463132225,
    477387593145053, 474409170747201, 471414248090364, 468402876912625, 465375108543457,
    462330993908654, 459270583535171, 456193927555904, 453101075714376, 449992077369360,
    446866981499431, 443725836707433, 440568691224895, 437395592916360, 434206589283663,
    431001727470129, 427781054264716, 424544616106092, 421292459086646, 418024628956443,
    414741171127116, 411442130675699, 408127552348406, 404797480564348, 401451959419201,
    398091032688810, 394714743832749, 391323135997824, 387916252021523, 384494134435420,
    381056825468526, 377604367050587, 374136800815346, 370654168103746, 367156509967092,
    363643867170168, 360116280194308, 356573789240423, 353016434231987, 349444254817978,
    345857290375779, 342255580014038, 338639162575487, 335008076639726, 331362360525959,
    327702052295704, 324027189755453, 320337810459308, 316633951711570, 312915650569297,
    309182943844830, 305435868108281, 301674459689984, 297898754682924, 294108788945119,
    290304598101985, 286486217548652, 282653682452269, 278807027754261]
private def phb_m16_r384_4_p5 : List ℕ :=
  [274946288172567, 271071498203841, 267182692125634, 263279903998536, 259363167668294,
    255432516767911, 251487984719703, 247529604737339, 243557409827856, 239571432793637,
    235571706234379, 231558262549023, 227531133937666, 223490352403447, 219435949754410,
    215367957605340, 211286407379582, 207191330310833, 203082757444909, 198960719641500,
    194825247575889, 190676371740663, 186514122447394, 182338529828304, 178149623837908,
    173947434254635, 169731990682433, 165503322552352, 161261459124109, 157006429487631,
    152738262564587, 148456987109889, 144162631713189, 139855224800349, 135534794634897,
    131201369319460, 126854976797194, 122495644853180, 118123401115812, 113738273058175,
    109340287999392, 104929473105966, 100505855393107, 96069461726035, 91620318821279,
    87158453247948, 82683891429003, 78196659642498, 73696784022820, 69184290561909,
    64659205110464, 60121553379135, 55571360939704, 51008653226252, 46433455536312,
    41845793032006, 37245690741179, 32633173558507, 28008266246603, 23370993437110,
    18721379631774, 14059449203512, 9385226397470, 4698735332060]
private def phb_m16_r384_4 : List ℕ :=
  pCat phb_m16_r384_4_p0
    (pCat phb_m16_r384_4_p1
    (pCat phb_m16_r384_4_p2
    (pCat phb_m16_r384_4_p3
    (pCat phb_m16_r384_4_p4
      phb_m16_r384_4_p5))))
private def pvn_m16_r384_4_0_p0 : List ℕ :=
  [2020798663240546, 1981593835405865, 1973569687725115, 2005060712272143, 2029255430350516,
    2016712315242499, 1988412455520253, 1979631107240382, 1996015364118159, 2011551014754530,
    1999100780887100, 1954522243696975, 1893673765485439, 1833352900822750, 1778269648169185,
    1723859669805881, 1667908009588449, 1618333970813304, 1590872863474537, 1599796300345537,
    1649224363117659, 1730517806367854, 1826229458494583, 1917296394734774, 2010599744502235,
    2036038937245646, 2058103742269388, 2061275583425356, 2052918984787509, 2039685844216808,
    2026170271571057, 2016676391281520, 2004142226819165, 2001012038248746, 1999838357845268,
    1998447727325012, 2001356474528328, 1999126348364901, 1999073965140631, 1999341190444497,
    1999573138261668, 1999738906244414, 1999847686074542, 1999914732119272, 1999953986734636,
    1999975978685519, 1999987885888784, 1999993350295784, 2000001546442195, 1999999319443960,
    1999999433631527, 1999999726066872, 1999999878529416, 1999999947523813, 1999999977807480,
    1999999989859339, 1999999998399555, 1999999999316962, 1999999999455161, 1999999999741604,
    2000000000034728, 1999999999985115, 1999999999988297, 1999999999994726]
private def pvn_m16_r384_4_0_p1 : List ℕ :=
  [1999999999999418, 1999999999999745, 1999999999999807, 1999999999999926, 1999999999999977,
    1999999999999996]
private def pvn_m16_r384_4_0 : List ℕ :=
  pCat pvn_m16_r384_4_0_p0
      pvn_m16_r384_4_0_p1
private def pvn_m16_r384_4_1_p0 : List ℕ :=
  [2017163728027903, 2019420821079563, 2005312810869140, 1984327593973364, 1973844502188712,
    1983291811577154, 2005426159712320, 2022761865987732, 2022495950818895, 2006489583898516,
    1988578592945869, 1982752004240307, 1992585942015987, 2009045275610759, 2019174944637989,
    2010087316461845, 1989265734188457, 1944856195883328, 1917831110557014, 1863942957950004,
    1830051530796272, 1788599903753645, 1726633520553812, 1676977426064449, 1640870224237055,
    1618831880289797, 1614097079549376, 1644076058244257, 1708975914682690, 1784242090345443,
    1864772379987207, 1935363266716609, 1988012533431781, 2024003572445081, 2043991621446040,
    2051043232223306, 2049844554961127, 2043019759376306, 2032498414113848, 2021328604529300,
    2012375602279545, 2006614205898061, 2003390896246512, 2001614584782807, 2000547833183729,
    1999887947729645, 1999529962958391, 1999401534262235, 1999425168509211, 1999526506216123,
    1999647706612421, 1999755463064641, 1999838475065311, 1999897818500797, 1999938330014140,
    1999964721141318, 1999980914408222, 1999990181717537, 1999995129781318, 1999997622535081,
    1999998833133480, 1999999416313102, 1999999702592028, 1999999847565925]
private def pvn_m16_r384_4_1_p1 : List ℕ :=
  [1999999922674076, 1999999961674597, 1999999981576097, 1999999991433244, 1999999996146563,
    1999999998320120, 1999999999288012, 1999999999705314, 1999999999880219, 1999999999951880,
    1999999999980778, 1999999999992332, 1999999999996938, 1999999999998775, 1999999999999512,
    1999999999999808, 1999999999999927, 1999999999999975, 1999999999999993, 1999999999999999]
private def pvn_m16_r384_4_1 : List ℕ :=
  pCat pvn_m16_r384_4_1_p0
      pvn_m16_r384_4_1_p1
private def phb_m16_r384_5_p0 : List ℕ :=
  [94603622400000, 133441315103308, 163004852032189, 187729063200000, 209336587576995,
    228713277142957, 246386757090067, 262701701273875, 277898140800000, 292151290709496,
    305593763077249, 318328847162339, 330438892301338, 341990836179493, 353039984367331,
    363632673600000, 373808197399530, 383600229578961, 393037897090677, 402146602450544,
    410948663755383, 419463819487521, 427709631505803, 435701810282889, 443454480000000,
    450980396578189, 458291128488408, 465397207836794, 472308257498510, 479033098792038,
    485579843221992, 491955971085825, 498168399177375, 504223539384559, 510127349638074,
    515885378400000, 521502803668463, 526984467304661, 532334905351865, 537558374905474,
    542658878003136, 547640182930312, 552505843275999, 557259215023219, 561903471917198,
    566441619319400, 570876506726440, 575210839108356, 579447187200000, 583587996861725,
    587635597610585, 591592210410461, 595459954798624, 599240855416771, 602936848006495,
    606549784922121, 610081440207744, 613533514280027, 616907638253690, 620205377942608,
    623428237565883, 626577663185176, 629655045896840, 632661724800000]
private def phb_m16_r384_5_p1 : List ℕ :=
  [635598989759591, 638468083981494, 641270206415215, 644006513998103, 646678123753751,
    649286114756045, 651831529969298, 654315377973923, 656738634586291, 659102244380630,
    661407122120142, 663654154103930, 665844199435713, 667978091219867, 670056637689829,
    672080623273511, 674050809600000, 675967936451463, 677832722663900, 679645866980057,
    681408048857616, 683119929235494, 684782151260898, 686395340979580, 687960107991559,
    689477046074412, 690946733776079, 692369734979008, 693746599437321, 695077863288573,
    696364049541565, 697605668541579, 698803218414309, 699957185489676, 701068044706630,
    702136260000000, 703162284670328, 704146561737642, 705089524279982, 705991595757499,
    706853190322877, 707674713118776, 708456560562957, 709199120621727, 709902773072263,
    710567889754392, 711194834812329, 711783964926862, 712335629538463, 712850171061730,
    713327925091596, 713769220601681, 714174380135151, 714543719988434, 714877550388121,
    715176175661352, 715439894400000, 715668999618899, 715863778908417, 716024514581582,
    716151483816037, 716244958791015, 716305206819568, 716332490476243]
private def phb_m16_r384_5_p2 : List ℕ :=
  [716327067720396, 716289192015332, 716219112443438, 716117073817477, 715983316788206,
    715818077948446, 715621589933779, 715394081519973, 715135777717292, 714846899861797,
    714527665703759, 714178289493303, 713798982063378, 713389950910164, 712951400271010,
    712483531200000, 711986541641220, 711460626499843, 710905977711069, 710322784307045,
    709711232481799, 709071505654286, 708403784529600, 707708247158421, 706985068994763,
    706234422952081, 705456479457783, 704651406506226, 703819369710226, 702960532351142,
    702075055427584, 701163097702792, 700224815750720, 699260364000885, 698269894782009,
    697253558364495, 696211503001789, 695143874970640, 694050818610317, 692932476360803,
    691788988800000, 690620494679984, 689427130962335, 688209032852560, 686966333833664,
    685699165698870, 684407658583521, 683091940996204, 681752139849093, 680388380487560,
    679000786719062, 677589480841327, 676154583669864, 674696214564813, 673214491457162,
    671709530874333, 670181447965179, 668630356524385, 667056369016311, 665459596598276,
    663840149143311, 662198135262388, 660533662326147, 658846836486129]
private def phb_m16_r384_5_p3 : List ℕ :=
  [657137762695529, 655406544729491, 653653285204944, 651878085600000, 650081046272929,
    648262266480714, 646421844397202, 644559877130861, 642676460742155, 640771690260547,
    638845659701133, 636898462080933, 634930189434826, 632940932831156, 630930782387014,
    628899827283193, 626848155778842, 624775855225815, 622683012082719, 620569711928687,
    618436039476862, 616282078587613, 614107912281480, 611913622751869, 609699291377483,
    607464998734513, 605210824608590, 602936848006495, 600643147167647, 598329799575365,
    595996881967908, 593644470349310, 591272640000000, 588881465487222, 586471020675261,
    584041378735462, 581592612156079, 579124792751922, 576637991673839, 574132279418006,
    571607725835060, 569064400139052, 566502370916244, 563921706133741, 561322473147968,
    558704738712991, 556068568988690, 553414029548789, 550741185388731, 548050100933429,
    545340840044865, 542613466029565, 539868041645935, 537104629111478, 534323290109875,
    531524085797951, 528707076812517, 525872323277094, 523019884808527, 520149820523476,
    517262189044811, 514357048507882, 511434456566699, 508494470400000]
private def phb_m16_r384_5_p4 : List ℕ :=
  [505537146717216, 502562541764344, 499570711329718, 496561710749681, 493535594914173,
    490492418272223, 487432234837345, 484355098192857, 481261061497112, 478150177488633,
    475022498491184, 471878076418743, 468716962780408, 465539208685220, 462344864846905,
    459133981588553, 455906608847213, 452662796178422, 449402592760660, 446126047399739,
    442833208533123, 439524124234178, 436198842216366, 432857409837363, 429499874103126,
    426126281671886, 422736678858095, 419331111636300, 415909625644966, 412472266190244,
    409019078249676, 405550106475850, 402065395200000, 398564988435551, 395048929881618,
    391517262926443, 387970030650793, 384407275831302, 380829040943770, 377235368166405,
    373626299383031, 370001876186240, 366362139880504, 362707131485239, 359036891737833,
    355351461096622, 351650879743830, 347935187588468, 344204424269186, 340458629157095,
    336697841358544, 332922099717856, 329131442820035, 325325908993426, 321505536312346,
    317670362599676, 313820425429417, 309955762129215, 306076409782844, 302182405232668,
    298273785082057, 294350585697781, 290412843212365, 286460593526414]
private def phb_m16_r384_5_p5 : List ℕ :=
  [282493872310915, 278512715009494, 274517156840659, 270507232800000, 266482977662370,
    262444425984033, 258391612104788, 254324570150055, 250243334032950, 246147937456321,
    242038413914762, 237914796696600, 233777118885863, 229625413364210, 225459712812852,
    221280049714437, 217086456354914, 212878964825381, 208657607023898, 204422414657284,
    200173419242897, 195910652110378, 191634144403386, 187343927081306, 183040030920937,
    178722486518162, 174391324289588, 170046574474182, 165688267134872, 161316432160138,
    156931099265578, 152532297995462, 148120057724258, 143694407658151, 139255376836532,
    134802994133481, 130337288259221, 125858287761566, 121366021027342, 116860516283798,
    112341801600000, 107809904888201, 103264853905209, 98706676253725, 94135399383675,
    89551050593523, 84953657031566, 80343245697222, 75719843442298, 71083476972239,
    66434172847376, 61771957484145, 57096857156302, 52408897996123, 47708105995585,
    42994507007540, 38268126746874, 33528990791651, 28777124584247, 24012553432467,
    19235302510660, 14445396860808, 9642861393611, 4827720889561]
private def phb_m16_r384_5 : List ℕ :=
  pCat phb_m16_r384_5_p0
    (pCat phb_m16_r384_5_p1
    (pCat phb_m16_r384_5_p2
    (pCat phb_m16_r384_5_p3
    (pCat phb_m16_r384_5_p4
      phb_m16_r384_5_p5))))
private def pvn_m16_r384_5_0_p0 : List ℕ :=
  [2017163728027903, 2019420821079563, 2005312810869140, 1984327593973364, 1973844502188712,
    1983291811577154, 2005426159712320, 2022761865987732, 2022495950818895, 2006489583898516,
    1988578592945869, 1982752004240307, 1992585942015987, 2009045275610759, 2019174944637989,
    2010087316461845, 1989265734188457, 1944856195883328, 1917831110557014, 1863942957950004,
    1830051530796272, 1788599903753645, 1726633520553812, 1676977426064449, 1640870224237055,
    1618831880289797, 1614097079549376, 1644076058244257, 1708975914682690, 1784242090345443,
    1864772379987207, 1935363266716609, 2011987466568219, 2024003572445081, 2043991621446040,
    2051043232223306, 2049844554961127, 2043019759376306, 2032498414113848, 2021328604529300,
    1987624397720455, 2006614205898061, 2003390896246512, 2001614584782807, 2000547833183729,
    1999887947729645, 1999529962958391, 1999401534262235, 1999425168509211, 1999526506216123,
    1999647706612421, 1999755463064641, 1999838475065311, 1999897818500797, 1999938330014140,
    1999964721141318, 1999980914408222, 1999990181717537, 1999995129781318, 1999997622535081,
    1999998833133480, 1999999416313102, 1999999702592028, 1999999847565925]
private def pvn_m16_r384_5_0_p1 : List ℕ :=
  [1999999922674076, 1999999961674597, 1999999981576097, 1999999991433244, 1999999996146563,
    1999999998320120, 1999999999288012, 1999999999705314, 2000000000119781, 1999999999951880,
    1999999999980778, 1999999999992332, 1999999999996938, 1999999999998775, 1999999999999512,
    1999999999999808, 1999999999999927, 1999999999999975, 1999999999999993, 1999999999999999]
private def pvn_m16_r384_5_0 : List ℕ :=
  pCat pvn_m16_r384_5_0_p0
      pvn_m16_r384_5_0_p1
private def pvn_m16_r384_5_1_p0 : List ℕ :=
  [2008277914581002, 2015963853732620, 2018621319241185, 2011785286976082, 1996786089129455,
    1981404022381156, 1975218019153681, 1982834824497819, 2000274450641992, 2016937091895148,
    2023599412650262, 2014988628504014, 2002339003265163, 1983210802871417, 1989888784898922,
    1986458262852532, 2012025519428466, 2019652623134221, 2012870346210240, 2008508896764049,
    1981061112481751, 1944894547280825, 1915235007842127, 1887391265233206, 1850253462026470,
    1797928659385290, 1756653787681587, 1705315777605309, 1675464968816255, 1623624813516841,
    1622225626704280, 1641822036861701, 1670231966795933, 1730799338573860, 1804464057423744,
    1892584615413408, 1936960357906114, 1998469110636348, 2022327905686406, 2030100519523087,
    2048370454178697, 2056531904960966, 2044977742722002, 2026946868214652, 2014062548490988,
    2007735615135522, 2004977034944227, 2003420346744400, 2002185157442859, 2001148839627694,
    2000361861487714, 1999845772409203, 1999571158157033, 1999478406754765, 1999500356015542,
    1999579083346674, 1999674246771113, 1999763228162808, 1999836492009710, 1999892140746821,
    1999931893050979, 1999958790636388, 1999976067048958, 1999986614444889]
private def pvn_m16_r384_5_1_p1 : List ℕ :=
  [1999992751073579, 1999996170499859, 1999998009557924, 1999998973425388, 1999999471725289,
    1999999727963235, 1999999860022092, 1999999928492968, 1999999963885783, 1999999981965055,
    1999999991143737, 1999999995795733, 1999999998107706, 1999999999199213, 1999999999678031,
    1999999999873310, 1999999999949266, 1999999999978753, 1999999999990708, 1999999999995848,
    1999999999998153, 1999999999999194, 1999999999999658, 1999999999999861, 1999999999999947,
    1999999999999981, 1999999999999995]
private def pvn_m16_r384_5_1 : List ℕ :=
  pCat pvn_m16_r384_5_1_p0
      pvn_m16_r384_5_1_p1
private def pvn_m16_r384_5_2_p0 : List ℕ :=
  [2002822593598016, 2007341941611342, 2012947777505162, 2017074581430939, 2016517390078466,
    2009355019486239, 1997171088467894, 1983772406188947, 1977744491218256, 1976854575606414,
    1994366620279375, 2000570137740335, 2024331079022192, 2018233631970535, 2013198520940643,
    2006576134565081, 1985169264410434, 1983156286224199, 1993423658809337, 2000241763343381,
    2011404228368517, 2018429953151667, 2025712367256839, 1998335152770810, 1985425078638464,
    1951362886769864, 1938890695052960, 1910893400266411, 1862537716377233, 1836898313755569,
    1793349328337778, 1755023194824419, 1691313062302757, 1668331378204172, 1644948598952042,
    1624995980007788, 1645286648725175, 1685427826235146, 1735840856558842, 1806380152509331,
    1880805693409244, 1935613743055446, 1971846355651729, 2002523389367496, 2030146690045653,
    2047637720304758, 2050811331397610, 2043091896445638, 2031320937286506, 2020681059159568,
    2013106500118973, 2008330157496922, 2005383760914391, 2003452458021057, 2002079984058365,
    2001072754087402, 2000359127453786, 1999898681480508, 1999646003726418, 1999547069120498,
    1999547798279849, 1999602696702548, 1999678990921836, 1999756369598046]
private def pvn_m16_r384_5_2_p1 : List ℕ :=
  [1999824300785819, 1999878801283172, 1999919713165115, 1999948785854960, 1999968467637014,
    1999981212932977, 1999989134659756, 1999993877378967, 1999996623780524, 1999998169573162,
    1999999020004009, 1999999480032437, 1999999725979036, 1999999856427858, 1999999925231013,
    1999999961365403, 1999999980262557, 1999999990081738, 1999999995125388, 1999999997667974,
    1999999998916750, 1999999999511126, 1999999999784780, 1999999999906928, 1999999999960115,
    1999999999982918, 1999999999992643, 1999999999996809, 1999999999998611, 1999999999999398,
    1999999999999743, 1999999999999893, 1999999999999959, 1999999999999987, 1999999999999997]
private def pvn_m16_r384_5_2 : List ℕ :=
  pCat pvn_m16_r384_5_2_p0
      pvn_m16_r384_5_2_p1
private def pvn_m16_r384_5_3_p0 : List ℕ :=
  [2000721350358291, 2002264791720459, 2005078657669254, 2008954141171886, 2013579846199073,
    2015557852117031, 2017702773320941, 2007766239383630, 2006815671187343, 1984949101536187,
    1984893865544164, 1977829347070327, 1976520830623839, 1996043592793107, 2005414349891510,
    2011788111366180, 2023922307408293, 2017123415284791, 2008544840372972, 1986795484495552,
    1995084967361051, 1983199871954083, 1991953030666166, 2002865373845351, 2008397606770957,
    2032268950210683, 2015145121729678, 2007037980684473, 1985313697994884, 1981607340628406,
    1957412340996669, 1919086294067223, 1903856505375990, 1878586896209874, 1832668943711625,
    1793179683359093, 1756153125717756, 1710842344123100, 1671790204120122, 1649868691798291,
    1640210607857337, 1644712119732593, 1674645488128071, 1730311934887408, 1795888857529298,
    1855313255403734, 1904390509101970, 1946959646141134, 1985306130349487, 2016782828647145,
    2037268706375459, 2045412090739613, 2043624028139531, 2036263997390655, 2027354882140084,
    2019372816724880, 2013234905167829, 2008881476931658, 2005879197410272, 2003790083485347,
    2002306024763516, 2001246408368055, 2000509742995309, 2000029551782960]
private def pvn_m16_r384_5_3_p1 : List ℕ :=
  [1999750024082549, 1999618565317695, 1999587104463771, 1999615453431605, 1999673317209469,
    1999740221858096, 1999803964943753, 1999858477567812, 1999901756188756, 1999934187056360,
    1999957339433260, 1999973178312207, 1999983605155427, 1999990232879401, 1999994313718147,
    1999996755616934, 1999998180535406, 1999998994261845, 1999999450644057, 1999999702876600,
    1999999840663078, 1999999915241837, 1999999955303726, 1999999976671331, 1999999987976932,
    1999999993897806, 1999999996957574, 1999999998512639, 1999999999287639, 1999999999665650,
    1999999999845980, 1999999999930185, 1999999999968756, 1999999999986145, 1999999999993894,
    1999999999997318, 1999999999998827, 1999999999999492, 1999999999999784, 1999999999999911,
    1999999999999966, 1999999999999990, 1999999999999998]
private def pvn_m16_r384_5_3 : List ℕ :=
  pCat pvn_m16_r384_5_3_p0
      pvn_m16_r384_5_3_p1
private def phb_m16_r384_6_p0 : List ℕ :=
  [94271616000000, 132973009878679, 162432795141208, 187070238000000, 208601931915123,
    227910620015776, 245522075821487, 261779763573170, 276922872000000, 291126001235128,
    304521297958390, 317211688940684, 329279234517949, 340790637461173, 351801009248912,
    362356524000000, 372496337337931, 382254004899284, 391658551416946, 400735290258001,
    409506461195090, 417991733439383, 426208607217313, 434172737866466, 441898200000000,
    449397704772737, 456682780056695, 463763920996142, 470650716695270, 477351957514610,
    483875726491884, 490229477672833, 496420103577178, 502453993590651, 508337084734910,
    514074906000000, 519672617212137, 525135043240263, 530466704208647, 535671842272637,
    540754445424941, 545718268726421, 550566853294944, 555303543335887, 559931501456385,
    564453722470744, 568873045875423, 573192167147510, 577413648000000, 581539925709629,
    585573321618132, 589516048895039, 593370219639214, 597137851386982, 600820873086554,
    604421130591515, 607940391720047, 611380350921290, 614742633585654, 618028800031873,
    621240349200072, 624378722077034, 627445304877134, 630441432000000]
private def phb_m16_r384_6_p1 : List ℕ :=
  [633368388783854, 636227414071611, 639019702605128, 641746407261545, 644408641144317,
    647007479540380, 649543961753817, 652019092825482, 654433845147173, 656789159978180,
    659085948871395, 661325095015500, 663507454499236, 665633857503244, 667705109424507,
    669721991938029, 671685264000000, 673595662796362, 675453904640396, 677260685822650,
    679016683416283, 680722556040684, 682378944585966, 683986472900809, 685545748445874,
    687057362914904, 688521892825456, 689939900081065, 691311932506518, 692638524357825,
    693920196808314, 695157458412237, 696350805547144, 697500722836206, 698607683551600,
    699672150000000, 700694573891114, 701675396690215, 702615049955478, 703513955660943,
    704372526505848, 705191166211024, 705970269803028, 706710223886618, 707411406906164,
    708074189396541, 708698934224016, 709285996817630, 709835725391507, 710348461158562,
    710824538535976, 711264285342851, 711668022990407, 712036066665046, 712368725504633,
    712666302768292, 712929096000000, 713157397186273, 713351492908195, 713511664488032,
    713638188130687, 713731335060193, 713791371651483, 713818559557610]
private def phb_m16_r384_6_p2 : List ℕ :=
  [713813155832638, 713775413050353, 713705579419003, 713603898892194, 713470611276129,
    713305952333322, 713110153882930, 712883443897847, 712626046598675, 712338182544707,
    712020068722032, 711671918628874, 711293942358276, 710886346678220, 710449335109297,
    709983108000000, 709487862599743, 708963793129687, 708411090851448, 707829944133773,
    707220538517253, 706583056777144, 705917678984364, 705224582564734, 704503942356522,
    703755930666352, 702980717323526, 702178469732834, 701349352925882, 700493529611001,
    699611160221788, 698702402964309, 697767413863030, 696806346805508, 695819353585872,
    694806583947162, 693768185622536, 692704304375391, 691615084038447, 690500666551799,
    689361192000000, 688196798648183, 687007622977267, 685793799718264, 684555461885728,
    683292740810359, 682005766170798, 680694666024636, 679359566838658, 678000593518342,
    676617869436650, 675211516462111, 673781654986239, 672328403950288, 670851880871370,
    669352201867962, 667829481684808, 666283833717237, 664715370034921, 663124201405079,
    661510437315146, 659874185994932, 658215554438264, 656534648424151]
private def phb_m16_r384_6_p3 : List ℕ :=
  [654831572537460, 653106430189141, 651359323635993, 649590354000000, 647799621287227,
    645987224406320, 644153261186591, 642297828395710, 640421021757022, 638522935966490,
    636603664709269, 634663300675940, 632701935578390, 630719660165365, 628716564237694,
    626692736663194, 624648265391276, 622583237467233, 620497739046253, 618391855407133,
    616265670965720, 614119269288078, 611952733103393, 609766144316616, 607559584020856,
    605333132509528, 603086869288256, 600820873086554, 598535221869263, 596229992847777,
    593905262491047, 591561106536376, 589197600000000, 586814817187473, 584412831703855,
    581991716463703, 579551543700876, 577092384978155, 574614311196686, 572117392605243,
    569601698809326, 567067298780084, 564514260863078, 561942652786886, 559352541671550,
    556743994036865, 554117075810528, 551471852336133, 548808388381028, 546126748144028,
    543426995262995, 540709192822284, 537973403360056, 535219688875462, 532448110835709,
    529658730182995, 526851607341328, 524026802223231, 521184374236326, 518324382289806,
    515446884800806, 512551939700655, 509639604441029, 506709936000000]
private def phb_m16_r384_6_p4 : List ℕ :=
  [503762990887979, 500798825153573, 497817494389327, 494819053737386, 491803557895057,
    488771061120281, 485721617237016, 482655279640533, 479572101302625, 476472134776736,
    473355432203000, 470222045313208, 467072025435687, 463905423500114, 460722290042239,
    457522675208546, 454306628760832, 451074200080720, 447825438174103, 444560391675510,
    441279108852416, 437981637609478, 434668025492709, 431338319693586, 427992567053101,
    424630814065740, 421253106883417, 417859491319334, 414450012851791, 411024716627938,
    407583647467471, 404126849866273, 400654368000000, 397166245727613, 393662526594868,
    390143253837737, 386608470385799, 383058218865566, 379492541603770, 375911480630598,
    372315077682884, 368703374207252, 365076411363220, 361434230026249, 357776870790759,
    354104373973102, 350416779614483, 346714127483854, 342996457080757, 339263807638132,
    335516218125085, 331753727249618, 327976373461322, 324184194954031, 320377229668444,
    316555515294702, 312719089274944, 308867988805814, 305002250840946, 301121912093405,
    297227009038105, 293317577914187, 289393654727372, 285455275252274]
private def phb_m16_r384_6_p5 : List ℕ :=
  [281502475034694, 277535289393871, 273553753424714, 269557902000000, 265547769772540,
    261523391177326, 257484800433641, 253432031547146, 249365118311939, 245284094312591,
    241188992926147, 237079847324112, 232956690474406, 228819555143293, 224668473897290,
    220503479105048, 216324602939213, 212131877378258, 207925334208300, 203705005024885,
    199470921234760, 195223114057619, 190961614527823, 186686453496107, 182397661631261,
    178095269421790, 173779307177560, 169449805031414, 165106792940776, 160750300689232,
    156380357888098, 151996993977957, 147600238230192, 143190119748487, 138766667470324,
    134329910168448, 129879876452327, 125416594769587, 120940093407433, 116450400494051,
    111947544000000, 107431551739577, 102902451372179, 98360270403636, 93805036187541,
    89236775926554, 84655516673698, 80061285333638, 75454108663945, 70834013276343,
    66201025637951, 61555172072498, 56896478761534, 52224971745624, 47540676925528,
    42843620063370, 38133826783790, 33411322575087, 28676132790347, 23928282648562,
    19167797235730, 14394701505951, 9609020282501, 4810778258908]
private def phb_m16_r384_6 : List ℕ :=
  pCat phb_m16_r384_6_p0
    (pCat phb_m16_r384_6_p1
    (pCat phb_m16_r384_6_p2
    (pCat phb_m16_r384_6_p3
    (pCat phb_m16_r384_6_p4
      phb_m16_r384_6_p5))))
private def pvn_m16_r384_6_0_p0 : List ℕ :=
  [2000721350358291, 2002264791720459, 2005078657669254, 2008954141171886, 2013579846199073,
    2015557852117031, 2017702773320941, 2007766239383630, 1993184328812657, 1984949101536187,
    1984893865544164, 1977829347070327, 1976520830623839, 1996043592793107, 2005414349891510,
    2011788111366180, 2023922307408293, 2017123415284791, 2008544840372972, 1986795484495552,
    1995084967361051, 1983199871954083, 1991953030666166, 2002865373845351, 2008397606770957,
    2032268950210683, 2015145121729678, 2007037980684473, 1985313697994884, 1981607340628406,
    1957412340996669, 1919086294067223, 1903856505375990, 1878586896209874, 1832668943711625,
    1793179683359093, 1756153125717756, 1710842344123100, 1671790204120122, 1649868691798291,
    1640210607857337, 1644712119732593, 1674645488128071, 1730311934887408, 1795888857529298,
    1855313255403734, 1904390509101970, 1946959646141134, 2014693869650513, 2016782828647145,
    2037268706375459, 2045412090739613, 2043624028139531, 2036263997390655, 2027354882140084,
    2019372816724880, 1986765094832171, 2008881476931658, 2005879197410272, 2003790083485347,
    2002306024763516, 2001246408368055, 2000509742995309, 2000029551782960]
private def pvn_m16_r384_6_0_p1 : List ℕ :=
  [1999750024082549, 1999618565317695, 1999587104463771, 1999615453431605, 1999673317209469,
    1999740221858096, 1999803964943753, 1999858477567812, 1999901756188756, 1999934187056360,
    1999957339433260, 1999973178312207, 1999983605155427, 1999990232879401, 1999994313718147,
    1999996755616934, 2000001819464594, 1999998994261845, 1999999450644057, 1999999702876600,
    1999999840663078, 1999999915241837, 1999999955303726, 1999999976671331, 1999999987976932,
    1999999993897806, 1999999996957574, 1999999998512639, 1999999999287639, 1999999999665650,
    1999999999845980, 1999999999930185, 1999999999968756, 1999999999986145, 1999999999993894,
    1999999999997318, 1999999999998827, 1999999999999492, 1999999999999784, 1999999999999911,
    1999999999999966, 1999999999999990, 1999999999999998]
private def pvn_m16_r384_6_0 : List ℕ :=
  pCat pvn_m16_r384_6_0_p0
      pvn_m16_r384_6_0_p1
private def pvn_m16_r384_6_1_p0 : List ℕ :=
  [2000125853047491, 2000269655465711, 2001391288249861, 2001270273960889, 2005438917139733,
    2006435786289808, 2009043334789667, 2013745043670165, 2019581404512424, 2016727049450515,
    2001415901918049, 1998344543649902, 1998403188699128, 1980679442866154, 1981217812152814,
    1974788522905201, 1990333037732765, 1985939069464026, 2000384794909215, 2020719884406126,
    2013511836707762, 2024630052470578, 2004413829133808, 2003043811008928, 1994387653206095,
    1988626716119600, 1986141423297781, 1983541002032740, 2005747148194038, 2024071503689625,
    2015395953035815, 2011739953125519, 2017831348016624, 2007481829945341, 1985861176211349,
    1971179789088708, 1957346784401384, 1934293397934132, 1908935437909551, 1882102459310658,
    1855039211067540, 1805792237339354, 1779700088750650, 1722757911473743, 1705244090223050,
    1670316345189090, 1633554319184615, 1644699635545362, 1671235893748041, 1715152070340553,
    1742514054738226, 1815874607110040, 1862438112459640, 1911712616065073, 1967735460897048,
    1996500641015265, 2011902658924176, 2032544389675355, 2047633086931627, 2045842154283752,
    2032780548024898, 2019612028685312, 2011586170476661, 2007964054387486]
private def pvn_m16_r384_6_1_p1 : List ℕ :=
  [2006344732471534, 2005179574288995, 2003990572904611, 2002813453807589, 2001778407080648,
    2000960520602733, 2000372022192511, 1999985813236823, 1999763745483318, 1999657449494530,
    1999635424840150, 1999657228763746, 1999705692927096, 1999763545161473, 1999816813281552,
    1999864110186025, 1999904397183958, 1999934559033920, 1999955270521013, 1999970046067186,
    1999981201190941, 1999989227837489, 1999994307491156, 1999997094966022, 1999998469278280,
    1999999129305680, 1999999471989646, 1999999673545574, 1999999801379089, 1999999882844977,
    1999999933108686, 1999999962882829, 1999999979886225, 1999999989314739, 1999999994422374,
    1999999997136228, 1999999998553313, 1999999999280950, 1999999999648337, 1999999999830701,
    1999999999919708, 1999999999962447, 1999999999982652, 1999999999992074, 1999999999996416,
    1999999999998395, 1999999999999288, 1999999999999692, 1999999999999871, 1999999999999949,
    1999999999999981, 1999999999999995]
private def pvn_m16_r384_6_1 : List ℕ :=
  pCat pvn_m16_r384_6_1_p0
      pvn_m16_r384_6_1_p1
private def pvn_m16_r384_6_2_p0 : List ℕ :=
  [2000184716586382, 1999492404353823, 2001267884651064, 1999551914143303, 2000813358037667,
    2002574312316741, 2004102862092727, 2005478892952805, 2004056733281412, 2011032915718879,
    2024620847173178, 2010278218957549, 2013091653978780, 2002594205361011, 2006506658169429,
    1997088256905295, 1978145083091230, 1991309229093484, 1975072837328660, 1982277819401549,
    1983376407635247, 1991720968616152, 2008034969549200, 2013785718877110, 2020156658549716,
    2015983772801200, 2005558195585027, 2008242709964120, 2003583653449699, 1982266246603000,
    1976600539128396, 1993202249586284, 2005228489653521, 2004858617308377, 2013339184170485,
    2017355289331316, 2026350478551371, 2003581248587812, 2011441210215209, 1987587529687203,
    1977421759199532, 1967472036975947, 1934113798482172, 1929566617176553, 1900349501025990,
    1872237699087963, 1820913055353862, 1805470918837815, 1773172260909213, 1715337736142880,
    1682906987692274, 1661763599026243, 1646769597584351, 1658978672227099, 1687983016535684,
    1718534453584330, 1760307322024713, 1817956256375893, 1875505501283304, 1919770946276535,
    1954244550771961, 1986623526859741, 2016093154568764, 2035986512361009]
private def pvn_m16_r384_6_2_p1 : List ℕ :=
  [2042637202707364, 2038654676062866, 2029850735688899, 2021085215529163, 2014565948483920,
    2010376120257806, 2007752290176897, 2005938036446259, 2004492132226608, 2003254263358848,
    2002197732179678, 2001336930998524, 2000682707289194, 2000221339342968, 1999922599710132,
    1999753374940413, 1999679697079800, 1999668377385926, 1999693045972537, 1999736354311659,
    1999786730041795, 1999835651827225, 1999877789175060, 1999911423174701, 1999937331571741,
    1999957026037551, 1999971722947333, 1999982262795719, 1999989387882362, 1999993891228853,
    1999996562864940, 1999998072680875, 1999998904865946, 1999999364732826, 1999999625186395,
    1999999777436265, 1999999868490404, 1999999923315577, 1999999956075130, 1999999975326260,
    1999999986407491, 1999999992650402, 1999999996095470, 1999999997960098, 1999999998951190,
    1999999999469026, 1999999999735181, 1999999999869820, 1999999999936890, 1999999999969806,
    1999999999985730, 1999999999993336, 1999999999996925, 1999999999998599, 1999999999999371,
    1999999999999724, 1999999999999883, 1999999999999954, 1999999999999985, 1999999999999996]
private def pvn_m16_r384_6_2 : List ℕ :=
  pCat pvn_m16_r384_6_2_p0
      pvn_m16_r384_6_2_p1
private def pvn_m16_r384_6_3_p0 : List ℕ :=
  [2000578008880241, 1998929281596415, 2000731034519608, 2000512191842728, 1999598529022027,
    2000315724902841, 2000285627609089, 2000350769838141, 2010245307227438, 1994997187596518,
    2004742792693804, 2008542402205505, 2014139691968362, 2023130635452840, 2002176505963896,
    2017135224204650, 2010633214026692, 2003178597289220, 1999905770857324, 1989914232660129,
    1988733567907627, 1983944395046039, 1977471315626150, 1981037170526426, 1983654655116482,
    1989712931014091, 2008233994996945, 2017089764704498, 2011099443276374, 2008011282813023,
    2023216598950289, 2011331273450521, 2004133632372630, 1976667429489239, 1991850053075693,
    1989677327676089, 1986927573789370, 2007470253535894, 1999971197126366, 2020335311548108,
    2017139286577570, 2020375887882002, 2008934070109776, 2010204095713305, 2004797868920694,
    1973739751990386, 1967547383524032, 1969213110104134, 1940602389715060, 1909430803998530,
    1891117773422813, 1865929130696016, 1832853541963339, 1799681415494885, 1759579289348695,
    1713730738713729, 1679493168360455, 1664952341944482, 1661855565166862, 1665561815637548,
    1683242661627040, 1720201365515432, 1769752123911520, 1819990302134955]
private def pvn_m16_r384_6_3_p1 : List ℕ :=
  [1864912790482989, 1905942550878842, 1945538407397450, 1982243203160819, 2011547640795550,
    2029814412691260, 2036837452269452, 2035504845794262, 2029825695240971, 2023114286469532,
    2017229714676560, 2012753011187439, 2009539697779209, 2007210747105078, 2005431319851636,
    2003998835544850, 2002820688328459, 2001862195220832, 2001108734733409, 2000546758013276,
    2000155514421191, 1999906014930063, 1999765587505237, 1999703629859521, 1999694580102745,
    1999718009151990, 1999758003846704, 1999803052823302, 1999846005989550, 1999883412808414,
    1999914286373984, 1999938865364425, 1999957816722424, 1999971912463261, 1999981964263767,
    1999988807872641, 1999993254290142, 1999996021185308, 1999997682540040, 1999998655297044,
    1999999217583794, 1999999542224231, 1999999730991622, 1999999841848779, 1999999907439212,
    1999999946314067, 1999999969246395, 1999999982637919, 1999999990350601, 1999999994722442,
    1999999997159223, 1999999998494604, 1999999999214299, 1999999999595934, 1999999999795149,
    1999999999897567, 1999999999949458, 1999999999975380, 1999999999988157, 1999999999994372,
    1999999999997357, 1999999999998779, 1999999999999446, 1999999999999753]
private def pvn_m16_r384_6_3_p2 : List ℕ :=
  [1999999999999895, 1999999999999959, 1999999999999987, 1999999999999997]
private def pvn_m16_r384_6_3 : List ℕ :=
  pCat pvn_m16_r384_6_3_p0
    (pCat pvn_m16_r384_6_3_p1
      pvn_m16_r384_6_3_p2)
private def pvn_m16_r384_6_4_p0 : List ℕ :=
  [2000970736479878, 1999106231974475, 1999696089452733, 2000759615473380, 2000390177959302,
    1998543028590340, 2004526374121643, 1992095916531685, 2005339223547540, 2005439327313556,
    1998204418522831, 2006298077541834, 1991536121058977, 2012781623485280, 2016221774649781,
    2009454079922942, 2014016136538245, 2012307758433693, 2012855843604039, 2011418207959406,
    2002220217516767, 1998809485660830, 1996486476623859, 1986957731271627, 1984714087231625,
    1982579069673030, 1979842240745674, 1971001028324283, 1997804342416905, 2000163709275633,
    2012616989632642, 2001672983151712, 2010365001087272, 2031948817236845, 2008272235355294,
    2010813020757474, 1991860184004912, 1990753360699676, 1986262858347762, 1989492853071341,
    1993086751885803, 1992773041434907, 2012696261240859, 2018532111789528, 2007259558405272,
    2018004522550431, 2027461423710387, 2008865769082609, 1992285273745190, 1992028716979239,
    1986121198776300, 1969148593909428, 1951715322814909, 1932519170405067, 1908564305551892,
    1885996638139913, 1864567656796267, 1833383522257638, 1789492115565551, 1744850390982844,
    1710876664096418, 1687189891312215, 1669327604553883, 1659764045528361]
private def pvn_m16_r384_6_4_p1 : List ℕ :=
  [1666107348412979, 1691448213900631, 1730412398350106, 1774277891024184, 1817690121880795,
    1860109416025748, 1902449367123819, 1943624116840603, 1980114931615555, 2008035031901271,
    2025383033493553, 2032834733738406, 2033000652773506, 2029058062349206, 2023649959912861,
    2018416778124894, 2014064761772292, 2010691607960059, 2008122795005859, 2006134521113445,
    2004552424259825, 2003270046604196, 2002232447029070, 2001411928170051, 2000788342371447,
    2000338679355436, 2000035268291944, 1999848490699014, 1999749889971749, 1999713956631736,
    1999718927217749, 1999747299614062, 1999786158357738, 1999827015129365, 1999865055160223,
    1999898046262318, 1999925301660705, 1999946944283182, 1999963494682465, 1999975670625389,
    1999984277248661, 1999990122086823, 1999993942409468, 1999996354853801, 1999997834942745,
    1999998723459257, 1999999249449471, 1999999558797400, 1999999740589844, 1999999847668648,
    1999999910893667, 1999999948232591, 1999999970211004, 1999999983057379, 1999999990489798,
    1999999994736217, 1999999997128427, 1999999998456131, 1999999999181876, 1999999999572580,
    1999999999779783, 1999999999888066, 1999999999943848, 1999999999972187]
private def pvn_m16_r384_6_4_p2 : List ℕ :=
  [1999999999986397, 1999999999993430, 1999999999996866, 1999999999998526, 1999999999999316,
    1999999999999692, 1999999999999867, 1999999999999947, 1999999999999981, 1999999999999995]
private def pvn_m16_r384_6_4 : List ℕ :=
  pCat pvn_m16_r384_6_4_p0
    (pCat pvn_m16_r384_6_4_p1
      pvn_m16_r384_6_4_p2)
private def phb_m16_r384_7_p0 : List ℕ :=
  [97109193142272, 136975499592771, 167322024860661, 192701055141696, 214880853386419,
    234770733306269, 252912294212081, 269659338623889, 285258254855424, 299888898506624,
    313687393874489, 326759765827364, 339190544718604, 351048441073664, 362390225227483,
    373263461140608, 383708483021423, 393759856531701, 403447480049252, 412797428873911,
    421832612195831, 430573291269751, 439037493079198, 447241344187668, 455199342854400,
    462924582840178, 470428939006152, 477723222400598, 484817310759897, 491720259034574,
    498440393561913, 504985392754552, 511362356597164, 517577866796093, 523638039077445,
    529548568853952, 535314771262682, 540941616401209, 546433760449614, 551795573252188,
    557031162840284, 562144397302157, 567138924343375, 572018188829952, 576785448563547,
    581443788502426, 585996133611935, 590445260503066, 594793807996416, 599044286730789,
    603199087920345, 607260491351049, 611230672695977, 615111710219328, 618905590930685,
    622614216243857, 626239407188379, 629782909216339, 633246396642423, 636631476750985,
    639939693600269, 643172531550787, 646331418541985, 649417729138944]
private def phb_m16_r384_7_p1 : List ℕ :=
  [652432787368585, 655377869363016, 658254205825841, 661062984335821, 663805351500844,
    666482414973998, 669095245342436, 671644877898760, 674132314303772, 676558524148686,
    678924446424148, 681230990902835, 683479039441772, 685669447210050, 687803043847114,
    689880634556399, 691903001138688, 693870902969231, 695785077922351, 697646243246952,
    699455096396108, 701212315813657, 702918561680520, 704574476623230, 706180686387022,
    707737800475632, 709246412759806, 710707102056381, 712120432679682, 713486954966830,
    714807205778481, 716081708976378, 717310975879042, 718495505696809, 719635785947359,
    720732292852800, 721785491719312, 722795837300279, 723763774143784, 724689736925294,
    725574150766297, 726417431539631, 727219986162157, 727982212875442, 728704501515038,
    729387233768925, 730030783425653, 730635516612679, 731201792025382, 731729961147187,
    732220368461239, 732673351654002, 733089241811176, 733468363606280, 733811035482234,
    734117569826266, 734388273138432, 734623446194046, 734823384200288, 734988376947228,
    735118708953540, 735214659607107, 735276503300750, 735304509563285]
private def phb_m16_r384_7_p2 : List ℕ :=
  [735298943186105, 735260064345473, 735188128720708, 735083387608423, 734946088032993,
    734776472853386, 734574780866521, 734341246907278, 734076101945303, 733779573178728,
    733451884124927, 733093254708423, 732703901346062, 732284037029549, 731833871405444,
    731353610852736, 730843458558047, 730303614588600, 729734275962988, 729135636719860,
    728507887984583, 727851218033948, 727165812359013, 726451853726119, 725709522236169,
    724938995382217, 724140448105432, 723314052849489, 722459979613449, 721578396003168,
    720669467281293, 719733356415897, 718770224127787, 717780228936534, 716763527205276,
    715720273184319, 714650619053591, 713554714963972, 712432709077547, 711284747606811,
    710110974852864, 708911533242622, 707686563365081, 706436204006660, 705160592185652,
    703859863185813, 702534150589115, 701183586307683, 699808300614954, 698408422176064,
    696984078077501, 695535393856042, 694062493526985, 692565499611717, 691044533164620,
    689499713799337, 687931159714430, 686338987718431, 684723313254310, 683084250423380,
    681421912008651, 679736409497652, 678027853104725, 676296351792829]
private def phb_m16_r384_7_p3 : List ℕ :=
  [674542013294838, 672764944134373, 670965249646164, 669143033995968, 667298400200034,
    665431450144161, 663542284602324, 661631003254902, 659697704706514, 657742486503471,
    655765445150856, 653766676129236, 651746273911028, 649704331976516, 647640942829535,
    645556198012826, 643450188123078, 641323002825649, 639174730868999, 637005460098819,
    634815277471874, 632604269069567, 630372520111235, 628120114967169, 625847137171381,
    623553669434119, 621239793654130, 618905590930685, 616551141575369, 614176525123641,
    611781820346167, 609367105259945, 606932457139200, 604477952526085, 602003667241174,
    599509676393753, 596996054391921, 594462874952500, 591910211110761, 589338135229968,
    586746719010748, 584136033500281, 581506149101332, 578857135581111, 576189062079972,
    573501997119958, 570796008613192, 568071163870109, 565327529607557, 562565171956735,
    559784156471007, 556984548133568, 554166411364976, 551329810030561, 548474807447691,
    545601466392927, 542709849109041, 539800017311923, 536872032197364, 533925954447727,
    530961844238503, 527979761244754, 524979764647453, 521961913139712]
private def phb_m16_r384_7_p4 : List ℕ :=
  [518926264932908, 515872877762711, 512801808895002, 509713115131707, 506606852816522,
    503483077840552, 500341845647857, 497183211240908, 494007229185950, 490813953618285,
    487603438247466, 484375736362411, 481130900836433, 477868984132192, 474590038306564,
    471294115015443, 467981265518457, 464651540683619, 461304990991896, 457941666541721,
    454561617053419, 451164891873577, 447751539979345, 444321609982665, 440875150134441,
    437412208328647, 433932832106367, 430437068659784, 426924964836093, 423396567141376,
    419851921744403, 416291074480381, 412714070854656, 409120956046344, 405511774911929,
    401886571988787, 398245391498677, 394588277351170, 390915273147033, 387226422181563,
    383521767447873, 379801351640132, 376065217156758, 372313406103565, 368545960296867,
    364762921266537, 360964330259023, 357150228240321, 353320655898911, 349475653648644,
    345615261631598, 341739519720886, 337848467523432, 333942144382706, 330020589381420,
    326083841344193, 322131938840169, 318164920185615, 314182823446467, 310185686440855,
    306173546741589, 302146441678609, 298104408341407, 294047483581416]
private def phb_m16_r384_7_p5 : List ℕ :=
  [289975704014363, 285889106022599, 281787725757390, 277671599141184, 273540761869841,
    269395249414849, 265235097025490, 261060339730997, 256871012342672, 252667149455979,
    248448785452615, 244215954502547, 239968690566030, 235707027395593, 231430998538006,
    227140637336217, 222835976931268, 218517050264186, 214183890077849, 209836528918832,
    205474999139224, 201099332898432, 196709562164952, 192305718718126, 187887834149877,
    183455939866413, 179010067089928, 174550246860263, 170076510036562, 165588887298898,
    161087409149886, 156572105916273, 152043007750509, 147500144632303, 142943546370151,
    138373242602862, 133789262801048, 129191636268608, 124580392144193, 119955559402649,
    115317166856448, 110665243157098, 105999816796544, 101320916108543, 96628569270031,
    91922804302468, 87203649073174, 82471131296644, 77725278535853, 72966118203539,
    68193677563481, 63407983731752, 58609063677968, 53796944226515, 48971652057768,
    44133213709288, 39281655577019, 34417003916458, 29539284843820, 24648524337189,
    19744748237650, 14827982250423, 9898251945967, 4955582761082]
private def phb_m16_r384_7 : List ℕ :=
  pCat phb_m16_r384_7_p0
    (pCat phb_m16_r384_7_p1
    (pCat phb_m16_r384_7_p2
    (pCat phb_m16_r384_7_p3
    (pCat phb_m16_r384_7_p4
      phb_m16_r384_7_p5))))
private def pvn_m16_r384_7_0_p0 : List ℕ :=
  [1999029263520122, 1999106231974475, 1999696089452733, 2000759615473380, 2000390177959302,
    1998543028590340, 2004526374121643, 1992095916531685, 1994660776452460, 2005439327313556,
    1998204418522831, 2006298077541834, 1991536121058977, 2012781623485280, 2016221774649781,
    2009454079922942, 2014016136538245, 2012307758433693, 2012855843604039, 2011418207959406,
    2002220217516767, 1998809485660830, 1996486476623859, 1986957731271627, 1984714087231625,
    1982579069673030, 1979842240745674, 1971001028324283, 1997804342416905, 2000163709275633,
    2012616989632642, 2001672983151712, 2010365001087272, 2031948817236845, 2008272235355294,
    2010813020757474, 1991860184004912, 1990753360699676, 1986262858347762, 1989492853071341,
    1993086751885803, 1992773041434907, 2012696261240859, 2018532111789528, 2007259558405272,
    2018004522550431, 2027461423710387, 2008865769082609, 1992285273745190, 1992028716979239,
    1986121198776300, 1969148593909428, 1951715322814909, 1932519170405067, 1908564305551892,
    1885996638139913, 1864567656796267, 1833383522257638, 1789492115565551, 1744850390982844,
    1710876664096418, 1687189891312215, 1669327604553883, 1659764045528361]
private def pvn_m16_r384_7_0_p1 : List ℕ :=
  [1666107348412979, 1691448213900631, 1730412398350106, 1774277891024184, 1817690121880795,
    1860109416025748, 1902449367123819, 1943624116840603, 2019885068384445, 2008035031901271,
    2025383033493553, 2032834733738406, 2033000652773506, 2029058062349206, 2023649959912861,
    2018416778124894, 1985935238227708, 2010691607960059, 2008122795005859, 2006134521113445,
    2004552424259825, 2003270046604196, 2002232447029070, 2001411928170051, 1999211657628553,
    2000338679355436, 2000035268291944, 1999848490699014, 1999749889971749, 1999713956631736,
    1999718927217749, 1999747299614062, 2000213841642262, 1999827015129365, 1999865055160223,
    1999898046262318, 1999925301660705, 1999946944283182, 1999963494682465, 1999975670625389,
    2000015722751339, 1999990122086823, 1999993942409468, 1999996354853801, 1999997834942745,
    1999998723459257, 1999999249449471, 1999999558797400, 2000000259410156, 1999999847668648,
    1999999910893667, 1999999948232591, 1999999970211004, 1999999983057379, 1999999990489798,
    1999999994736217, 1999999997128427, 1999999998456131, 1999999999181876, 1999999999572580,
    1999999999779783, 1999999999888066, 1999999999943848, 1999999999972187]
private def pvn_m16_r384_7_0_p2 : List ℕ :=
  [2000000000013603, 1999999999993430, 1999999999996866, 1999999999998526, 1999999999999316,
    1999999999999692, 1999999999999867, 1999999999999947, 1999999999999981, 1999999999999995]
private def pvn_m16_r384_7_0 : List ℕ :=
  pCat pvn_m16_r384_7_0_p0
    (pCat pvn_m16_r384_7_0_p1
      pvn_m16_r384_7_0_p2)
private def pvn_m16_r384_7_1_p0 : List ℕ :=
  [1999378451977481, 1999172095031836, 1999146598680417, 1998947983350367, 2003372799341321,
    1995516458972447, 2002002513922487, 2006832468533083, 1990816971489606, 2000992585547700,
    1990736568314176, 2005901385632242, 2004649437020013, 1991928933161905, 2000090775013893,
    2006857534009995, 2009286756872152, 2012615089347625, 2010547465389633, 2010887612022858,
    2016689686896616, 2011719783692183, 2009702196133427, 2003655063515211, 2008679880923955,
    1987248185975552, 1997495175755059, 1989462462148704, 1983223745225524, 1978763595503274,
    1964503180434217, 1999118111641466, 1994608713393602, 1997390378562480, 2000438049996125,
    2010798953432147, 2020527537634763, 2017643344665907, 2017862305124383, 2004716876376028,
    1992010006252904, 1997699778360584, 1990813237651713, 1977821386400950, 1990849630855880,
    2006565124352319, 2001590762299613, 2001472484924853, 2017527739034398, 2025731096544847,
    2018194499705756, 2009959895313571, 2005721730824764, 1999605953920892, 1991922864601975,
    1983780951200520, 1969838457681870, 1948668137807819, 1928321147982081, 1913699878352204,
    1897383888181470, 1869339091192631, 1830354097723462, 1789102968346907]
private def pvn_m16_r384_7_1_p1 : List ℕ :=
  [1754605228186863, 1719098602904218, 1699634638505233, 1658116022888969, 1676385485222370,
    1656960297049214, 1689420167807640, 1740274313214145, 1761533808963579, 1793013005117965,
    1837606413767987, 1909438580021896, 1936126450142621, 1988408772292728, 2008516038249275,
    2011225690854466, 2028877634214938, 2040824048797359, 2032484033620767, 2018748883744419,
    2008713333802233, 2007274145982988, 2007290107830942, 2006514871278376, 2006279855225189,
    2005661156491509, 2004308885994123, 2002373215830121, 2001481383311052, 2000581234587182,
    2000244021944789, 2000233386058901, 1999961793463956, 1999674424892804, 1999677688488822,
    1999798421907722, 1999913843448032, 1999908061702047, 1999888898983773, 1999895559083721,
    1999896557726990, 1999901937349336, 1999926093265002, 1999955980481525, 1999977745696351,
    1999987773233865, 1999991795491631, 1999994043632770, 1999995510037071, 1999996680715634,
    1999997825046866, 1999998792507848, 1999999410935280, 1999999715214021, 1999999841706747,
    1999999897145999, 1999999929800744, 1999999953475763, 1999999970696022, 1999999982343603,
    1999999989747839, 1999999994179237, 1999999996761803, 1999999998241457]
private def pvn_m16_r384_7_1_p2 : List ℕ :=
  [1999999999051859, 1999999999486778, 1999999999729496, 1999999999867327, 1999999999940325,
    1999999999974503, 1999999999988822, 1999999999994632, 1999999999997196, 1999999999998502,
    1999999999999220, 1999999999999613, 1999999999999819, 1999999999999922, 1999999999999969,
    1999999999999990, 1999999999999998]
private def pvn_m16_r384_7_1 : List ℕ :=
  pCat pvn_m16_r384_7_1_p0
    (pCat pvn_m16_r384_7_1_p1
      pvn_m16_r384_7_1_p2)
private def pvn_m16_r384_7_2_p0 : List ℕ :=
  [1999678531943177, 1999170900498274, 2000562157182088, 1995769236048970, 2002827698206229,
    2002598984438740, 1990807203986554, 2008569682080814, 1998050473915064, 2003717565494140,
    1999118483332997, 1988516959658654, 2000030673826429, 2005652641594311, 1998730374219664,
    1996537036533737, 1997863999758841, 1999632894512551, 2009495683855319, 2007172139183202,
    2011467163195134, 2004700492615566, 2021471429746771, 2008027586470306, 2011500030510782,
    2016735999144818, 2002323771929645, 2011554486844427, 1988326687473975, 2001616727310018,
    2001034253552269, 1983265386901967, 1973782519472959, 1974866742204704, 1988199861488467,
    1989301072112496, 1989075079123580, 1998512699370715, 2000110828664540, 2008045569021317,
    2024927750385588, 2020439668663267, 2006069580440640, 2009166279982054, 2009440386445610,
    1991002339500956, 1980543951887112, 1989876743191375, 1996432551967423, 1992263088129586,
    1993613236993966, 2005276286491416, 2015613328758884, 2019122403115490, 2019045721046339,
    2015907544224807, 2009608611992433, 2003751921833311, 2002676531921965, 1995531152713532,
    1987117238485113, 1957593770649247, 1957854127528685, 1924866229081786]
private def pvn_m16_r384_7_2_p1 : List ℕ :=
  [1935716582454305, 1899127116154400, 1864524944722366, 1847517029823386, 1794263798079938,
    1764192558593589, 1731568746574722, 1712826922093735, 1659418347707094, 1659748618676182,
    1682861204197342, 1691407289242542, 1715965467819454, 1747902370371382, 1776873872005347,
    1826320699865137, 1886133125791794, 1932630150698489, 1961584752911485, 1985876116766099,
    2011879385895045, 2030208672063237, 2034633088370851, 2028687359915850, 2020818990052082,
    2014206855305482, 2009928738989405, 2008184180814282, 2007548114019679, 2006958024247177,
    2006145446490791, 2004804910386201, 2003236356390322, 2001981043199333, 2001241180209831,
    2000788190667879, 2000361044043535, 1999990049635620, 1999801037356772, 1999773648973875,
    1999810924387251, 1999853226202625, 1999882103689729, 1999892030482099, 1999887763978031,
    1999884609059172, 1999894466551436, 1999916275208598, 1999941349324536, 1999962444344645,
    1999976998393233, 1999985751866331, 1999990645261037, 1999993491645516, 1999995426152452,
    1999996916884101, 1999998059436425, 1999998859452181, 1999999360354348, 1999999644941207,
    1999999797370313, 1999999878838709, 1999999924800008, 1999999952711666]
private def pvn_m16_r384_7_2_p2 : List ℕ :=
  [1999999970505295, 1999999981975373, 1999999989261145, 1999999993761091, 1999999996451713,
    1999999998015277, 1999999998907046, 1999999999410265, 1999999999690773, 1999999999843479,
    1999999999923549, 1999999999963671, 1999999999982940, 1999999999991936, 1999999999996113,
    1999999999998088, 1999999999999049, 1999999999999533, 1999999999999777, 1999999999999898,
    1999999999999956, 1999999999999984, 1999999999999996]
private def pvn_m16_r384_7_2 : List ℕ :=
  pCat pvn_m16_r384_7_2_p0
    (pCat pvn_m16_r384_7_2_p1
      pvn_m16_r384_7_2_p2)
private def pvn_m16_r384_7_3_p0 : List ℕ :=
  [2000158248108393, 1998205458159009, 2002473897841342, 1997940507901992, 1993607656964926,
    2010100641630213, 1993567048882145, 1999367417209511, 2001370155389766, 1997052500752860,
    2006558895118431, 2004749402592386, 1992739413209974, 1992861908049215, 2001126525957416,
    1999867306289754, 2004260465072459, 1994331736105786, 2000252972988774, 1991422825520705,
    2008484548942876, 2006593880488070, 1998886270254928, 2017392249048906, 2003080185659217,
    2017931684986411, 2009304959222205, 2009311186575801, 2020149643737191, 2010205962653252,
    2000822548241984, 1999004833266747, 2006331724386833, 2006087752414950, 1987389184750416,
    1978828634747533, 1981848378659648, 1978795288819707, 1983082372197119, 1992887383611015,
    1987991607336742, 1985410323519245, 2003821615132657, 2018310186250579, 2013014829538771,
    2010548952320590, 2019400286894576, 2018237742107042, 2002039658474119, 1990592405023253,
    1991707364952836, 1993008431461227, 1990053810351978, 1987081163461427, 1994629364385168,
    1996613032277545, 2014413414935305, 2007377789068504, 2030717086552755, 2007087642228911,
    2016512416174735, 2011016518771758, 2000344269769216, 2018968140811709]
private def pvn_m16_r384_7_3_p1 : List ℕ :=
  [1989641808270992, 1979180367967660, 1964346802192292, 1964588706617470, 1937041769268949,
    1929742181315287, 1921259460026655, 1872159774283881, 1838911054062524, 1824579887201365,
    1785184563129908, 1739810627415948, 1705533892381568, 1679281022049846, 1669701026684803,
    1679100759296223, 1693086834257237, 1702854981715779, 1722242184772768, 1762716127857196,
    1815849103000868, 1864404672827271, 1903488544876843, 1939325168207103, 1973985809595892,
    2002854316531597, 2021514379322526, 2028965662680479, 2027901203221659, 2022742906688894,
    2017062927974256, 2012678856839504, 2010039584018339, 2008740611652435, 2007926121685292,
    2006860933226242, 2005432531689285, 2003997821679830, 2002839734450037, 2001953510805980,
    2001233845765693, 2000649175071151, 2000224976117154, 1999969358870072, 1999853520364747,
    1999829555796444, 1999847790853254, 1999870020121534, 1999879175936690, 1999878093074650,
    1999877909486567, 1999886441755641, 1999904077564263, 1999926239131631, 1999947614621464,
    1999964843621882, 1999977035071249, 1999984960746006, 1999989962726901, 1999993207957831,
    1999995432003365, 1999997007715828, 1999998112233454, 1999998853280026]
private def pvn_m16_r384_7_3_p2 : List ℕ :=
  [1999999323124129, 1999999605750259, 1999999769607644, 1999999863307698, 1999999917435747,
    1999999949529816, 1999999969093356, 1999999981220870, 1999999988750350, 1999999993375060,
    1999999996167290, 1999999997822162, 1999999998785765, 1999999999337160, 1999999999646624,
    1999999999816335, 1999999999906913, 1999999999953859, 1999999999977507, 1999999999989135,
    1999999999994764, 1999999999997473, 1999999999998776, 1999999999999409, 1999999999999719,
    1999999999999870, 1999999999999944, 1999999999999979, 1999999999999994, 1999999999999999]
private def pvn_m16_r384_7_3 : List ℕ :=
  pCat pvn_m16_r384_7_3_p0
    (pCat pvn_m16_r384_7_3_p1
      pvn_m16_r384_7_3_p2)
private def pvn_m16_r384_7_4_p0 : List ℕ :=
  [2000803755744118, 1997490451592809, 2001060115181194, 2004439237887499, 1988626567400224,
    2005619779427382, 2001764010268534, 1995976864415746, 2002203759648597, 1997459625335807,
    1996347887628046, 2005754423694459, 2007796609855474, 1995256062894383, 1997143925156799,
    1991741837806182, 2004504998056557, 1996828771241736, 2005042587362826, 1999013524014612,
    1986595596464115, 2008746962808115, 1994786718326841, 2006671880901370, 2004906507094462,
    2003094126087851, 2015056806019980, 2009619118855299, 2006834763528691, 2012926465122971,
    2018286796000018, 2015764547857061, 2001601858823067, 1999463988917127, 2011180824214791,
    2007850128635394, 1995568188002094, 1991514234817432, 1983719531364077, 1974778664872708,
    1982551455115924, 1992063802424763, 1984076040248740, 1978332853253024, 1992620774412105,
    2007459504235754, 2007327796709338, 2006726510058112, 2017391032900354, 2022526733003133,
    2016963552319102, 1999792793802898, 2002333490237815, 1988521566837440, 2002149934283462,
    1979089389821272, 1995403253445173, 1988338389228829, 1988989716523050, 2014424822610337,
    2002526675134951, 2024237784441382, 2016389826793444, 2012150514370876]
private def pvn_m16_r384_7_4_p1 : List ℕ :=
  [2005188242996429, 2020395902446760, 2015391693149540, 1993143548254622, 1996774866011255,
    1984595732861962, 1956446229519543, 1959277302254950, 1958977623188770, 1930040127134619,
    1901241958707720, 1880432834226525, 1854959070477698, 1822546866921476, 1785592931961115,
    1742164036179910, 1702629624785014, 1682915761290518, 1682272745480582, 1684986160294453,
    1684685782798449, 1693418725009893, 1722007671380668, 1765031090232597, 1810628540588612,
    1853202133582894, 1893559055404557, 1932915198908129, 1969238465638004, 1998287844921728,
    2016946819287319, 2025260378140980, 2025892925777461, 2022339345282755, 2017606328535709,
    2013647227126679, 2011131705533587, 2009652115453992, 2008454713241905, 2007127497696482,
    2005708241658623, 2004380634044619, 2003236776602676, 2002272623206827, 2001469950774713,
    2000831350446033, 2000366546982340, 2000071695629567, 1999920205090453, 1999866837851551,
    1999862329221117, 1999869902325763, 1999873173649692, 1999872283316988, 1999873933837588,
    1999883054306166, 1999899750263284, 1999920569788362, 1999941254978160, 1999958789830569,
    1999972027940326, 1999981263330290, 1999987447404291, 1999991568129501]
private def pvn_m16_r384_7_4_p2 : List ℕ :=
  [1999994362662110, 1999996290234564, 1999997618222932, 1999998513168732, 1999999095290368,
    1999999459494240, 1999999679780468, 1999999810046864, 1999999886461881, 1999999931538921,
    1999999958501547, 1999999974862112, 1999999984872882, 1999999990997888, 1999999994717802,
    1999999996949696, 1999999998269124, 1999999999036377, 1999999999474482, 1999999999719601,
    1999999999853675, 1999999999925248, 1999999999962528, 1999999999981501, 1999999999990965,
    1999999999995616, 1999999999997883, 1999999999998981, 1999999999999513, 1999999999999773,
    1999999999999899, 1999999999999958, 1999999999999985, 1999999999999996]
private def pvn_m16_r384_7_4 : List ℕ :=
  pCat pvn_m16_r384_7_4_p0
    (pCat pvn_m16_r384_7_4_p1
      pvn_m16_r384_7_4_p2)
private def pvn_m16_r384_7_5_p0 : List ℕ :=
  [2001472641865608, 1998277224269438, 1996343915435361, 2009824354613560, 1992410409588356,
    1996160415362001, 2004876155432892, 1998238798357352, 1999340758178173, 2002386795351424,
    1997528936577195, 1992596517410900, 2006739267761748, 2002666255290515, 2007584082041297,
    1992526797143226, 1997274495048651, 1998652892572590, 1990847470103239, 2013823492420851,
    1994125857400874, 1997526873413782, 1998338426672946, 1993883722581018, 2004465767776774,
    2001260442071181, 1999524843680681, 2007548885215462, 2010664766661811, 2009150846336515,
    2004788872255025, 2009120833645048, 2021667975176159, 2017422754127030, 2002632552464648,
    2003858235513604, 2010594348950744, 2006833373276088, 2004543717356987, 2003707872937344,
    1990055882885767, 1976392626269660, 1982108087449147, 1991381275125020, 1985153082013499,
    1975056060408226, 1984324495179293, 1993789875044863, 2003638808488915, 1993185129463133,
    2015911320085734, 2009985985716418, 2030038984792422, 2010101458427554, 2005546957694197,
    2010866959888507, 1986789263680101, 2004226124064142, 1986555189563951, 1988077774320884,
    1987436546211813, 1993220724565942, 1994163375111573, 2007142602282243]
private def pvn_m16_r384_7_5_p1 : List ℕ :=
  [2024998324241558, 2009647954746576, 2004770441836400, 2022898327495554, 2015002015792719,
    2006660707760623, 2016820165566186, 2007017676781358, 1982112975228629, 1973769917856583,
    1975731666503122, 1966977409333242, 1949388258459479, 1929465490559078, 1907180440015885,
    1884823049843668, 1862243266188446, 1830490751539032, 1784780717740048, 1738111619602942,
    1708634027640312, 1696762562885194, 1689024375473122, 1680004430792753, 1678002498645549,
    1692067076268547, 1721925492797834, 1760439462138048, 1801248393411804, 1842357717274205,
    1884036511469690, 1925229209782530, 1962537924080384, 1992068141692958, 2011640880763286,
    2021515464080218, 2023840688936762, 2021684980552213, 2017979190205719, 2014621818629089,
    2012205002354773, 2010467345134786, 2008980542868274, 2007531806745694, 2006119364386174,
    2004806083126100, 2003631774391079, 2002608429628255, 2001742698996549, 2001046691030804,
    2000531185767501, 2000191710411885, 2000000842579290, 1999913803154598, 1999883571811007,
    1999875188229165, 1999871337250401, 1999868761695109, 1999870496779971, 1999879331033532,
    1999895014643190, 1999914715736012, 1999934850505682, 1999952654150730]
private def pvn_m16_r384_7_5_p2 : List ℕ :=
  [1999966805213799, 1999977230465418, 1999984553559480, 1999989585190025, 1999993028997788,
    1999995391684788, 1999997008109981, 1999998099048963, 1999998818264941, 1999999278998942,
    1999999565845292, 1999999740262981, 1999999844697438, 1999999906858806, 1999999943941322,
    1999999966214803, 1999999979687011, 1999999987864959, 1999999992822108, 1999999995808023,
    1999999997588181, 1999999998635458, 1999999999241963, 1999999999586988, 1999999999779435,
    1999999999884534, 1999999999940689, 1999999999970052, 1999999999985097, 1999999999992671,
    1999999999996428, 1999999999998273, 1999999999999172, 1999999999999609, 1999999999999821,
    1999999999999922, 1999999999999968, 1999999999999990, 1999999999999998]
private def pvn_m16_r384_7_5 : List ℕ :=
  pCat pvn_m16_r384_7_5_p0
    (pCat pvn_m16_r384_7_5_p1
      pvn_m16_r384_7_5_p2)
private def pvn_m16_r384_7_6_p0 : List ℕ :=
  [2001578659453538, 2001351406510999, 1991307384254592, 2008248017249531, 2002292868833812,
    1992310306526162, 2000030069964350, 2001790886255442, 1998402413013891, 1998685927473540,
    2006877620818066, 1992991797405734, 1998868474546599, 1994854063897979, 2006668991549595,
    2008637598988761, 1993254765893654, 2008679432910725, 1988019488934292, 1995183021345406,
    2004913652573947, 1998449117303369, 2003067165640150, 1997613110673793, 1993080339995654,
    1999879138767262, 2000775333929611, 1998710235134078, 1999208219372876, 2003847977804872,
    2011706050531483, 2008447614715918, 1999641001927383, 2007904828209437, 2021252017560515,
    2016524430815117, 2007148293185579, 2008353338138409, 2008403475036963, 2004350469678555,
    2009249226898977, 2012833816302687, 2001662827633909, 1981393420780290, 1986125808521069,
    1986479222144604, 1995253502276158, 1969441274860933, 1986338722568404, 1980361956613583,
    1994327961939476, 1996257042432783, 1986080612360814, 2019063563575037, 2008134727203384,
    2022247945310736, 2017368032867975, 2010259903894275, 2004551487355725, 2003947152145517,
    1999539226929175, 1987404279818676, 1993970833776611, 1991449420282578]
private def pvn_m16_r384_7_6_p1 : List ℕ :=
  [1975668721193677, 1994279831587902, 2014244000162151, 2004997951843220, 2007145959100376,
    2019077664712334, 2013203623577947, 2007457181518611, 2018404276032104, 2023037185606841,
    2009281981449979, 1993784279782127, 1986662209182260, 1982805576626197, 1977317358384930,
    1967568478205708, 1950495789663628, 1928777452387175, 1911051217841989, 1896907205838349,
    1872484692848042, 1830236006643517, 1782032552636385, 1744856152541412, 1722138165077270,
    1705449661905823, 1689023322453682, 1676735409819356, 1676400416142023, 1691388921046087,
    1718658456192430, 1752878789392966, 1790720526936672, 1831298806023977, 1873853290147563,
    1916006796597458, 1954103129531572, 1984678174353399, 2005737779560118, 2017335175523047,
    2021385502405727, 2020784332733740, 2018240241254711, 2015475031717906, 2013140302210012,
    2011236360204270, 2009579047985706, 2008044457489299, 2006602110863181, 2005265237181921,
    2004051065139393, 2002972790337191, 2002046178729154, 2001290916874340, 2000720988968803,
    2000332032114570, 2000096719154789, 1999972091699888, 1999913622682869, 1999887291041766,
    1999874177984093, 1999867795045253, 1999868028669858, 1999875763618684]
private def pvn_m16_r384_7_6_p2 : List ℕ :=
  [1999890218949559, 1999908838147839, 1999928450912030, 1999946455668988, 1999961393644648,
    1999972898675659, 1999981314017296, 1999987276229316, 1999991429873744, 1999994298655758,
    1999996264730130, 1999997596101853, 1999998481764126, 1999999057968303, 1999999424032262,
    1999999651506506, 1999999790373496, 1999999874162806, 1999999924450643, 1999999954626453,
    1999999972781068, 1999999983732714, 1999999990342924, 1999999994321714, 1999999996701375,
    1999999998110831, 1999999998935164, 1999999999410077, 1999999999679051, 1999999999828586,
    1999999999910106, 1999999999953669, 1999999999976502, 1999999999988252, 1999999999994196,
    1999999999997166, 1999999999998630, 1999999999999346, 1999999999999696, 1999999999999864,
    1999999999999942, 1999999999999978, 1999999999999993, 1999999999999999]
private def pvn_m16_r384_7_6 : List ℕ :=
  pCat pvn_m16_r384_7_6_p0
    (pCat pvn_m16_r384_7_6_p1
      pvn_m16_r384_7_6_p2)
private def pvn_m16_r384_7_7_p0 : List ℕ :=
  [2000562169536344, 2005633910367687, 1990518661247301, 1999946949579076, 2008312961292141,
    1998178850564240, 1995399001410789, 1999141230184115, 2003400291266718, 1992716415669398,
    2005550112972528, 1999931879893668, 2001560629272177, 1997861471794557, 1987369505767138,
    2011353329956692, 1997561638983786, 2004177077845333, 2008728882467907, 1993065424118957,
    1995671225831007, 1997421706999843, 1997380210317311, 2004283124371539, 2001891152370157,
    1995998254302366, 1996262292018816, 1998329887097245, 2000749274903349, 1998458791871266,
    1994397324340381, 2002526695433481, 2012792967482487, 2006029265125630, 1997445725386078,
    2006046377560609, 2016923591647603, 2014230183392953, 2012328223183268, 2011770079507115,
    2010759627296471, 1997894522968303, 2013210380046474, 2010492878265161, 2020234142437114,
    1986598170867602, 1991957187011447, 1992305563342511, 1986395248990370, 1994682528481900,
    1966180208326530, 1989131399043602, 1985180116747073, 1984942940785100, 1989342086568757,
    1994085322188180, 2002128872429809, 2011159739228292, 2021827274687909, 2014449538381580,
    2009566028542457, 2017860674672654, 2003361958202447, 1992850816271896]
private def pvn_m16_r384_7_7_p1 : List ℕ :=
  [2006238369450721, 1997232470429690, 1976512479987753, 1983618116490543, 1997047901603814,
    1995558794795580, 2000427954817992, 2013692160542419, 2013855817041726, 2006010001605234,
    2009302306457698, 2020053479923797, 2023058362757102, 2015792748226315, 2005049532662777,
    1995277255005518, 1989067658433671, 1987071829888272, 1982425652661041, 1967326024343755,
    1946614144084507, 1932254444624777, 1924157505811528, 1908142261527822, 1874437148709733,
    1829705552551769, 1788299327800964, 1757245330403993, 1733073045746495, 1710358636577063,
    1689592309070660, 1676589305081646, 1676507939441461, 1689835517589371, 1713453769814636,
    1744022066600120, 1779765662299807, 1819782145081061, 1862560454115658, 1905305066433851,
    1944359862154811, 1976285921796920, 1999014279827348, 2012495544224084, 2018480359669967,
    2019586554264803, 2018249217654352, 2016104683844958, 2013941565953051, 2011987944242054,
    2010233707852127, 2008626840765745, 2007138619891765, 2005762268059961, 2004501189080182,
    2003366713977254, 2002379404288291, 2001563859794021, 2000936371394848, 2000493455399921,
    2000209328618477, 2000043644022131, 1999954163548561, 1999907294263677]
private def pvn_m16_r384_7_7_p2 : List ℕ :=
  [1999882372073227, 1999869947809450, 1999867078106476, 1999872821182152, 1999885685836638,
    1999903116318999, 1999922144883418, 1999940248125684, 1999955842883750, 1999968318044241,
    1999977770514304, 1999984666324474, 1999989572500254, 1999993005560172, 1999995376791384,
    1999996992838586, 1999998076756376, 1999998790219898, 1999999250340270, 1999999541147380,
    1999999721666534, 1999999832136330, 1999999899083935, 1999999939441251, 1999999963723757,
    1999999978333022, 1999999987121757, 1999999992400537, 1999999995558333, 1999999997434365,
    1999999998538120, 1999999999179582, 1999999999547016, 1999999999754103, 1999999999868796,
    1999999999931173, 1999999999964476, 1999999999981944, 1999999999990950, 1999999999995522,
    1999999999997812, 1999999999998944, 1999999999999502, 1999999999999772, 1999999999999899,
    1999999999999958, 1999999999999986, 1999999999999997]
private def pvn_m16_r384_7_7 : List ℕ :=
  pCat pvn_m16_r384_7_7_p0
    (pCat pvn_m16_r384_7_7_p1
      pvn_m16_r384_7_7_p2)
private def pvn_m16_r384_7_8_p0 : List ℕ :=
  [1998433641242341, 2008514835526626, 1995712234578634, 1992144292751545, 2004458366710057,
    2004962477134650, 2000094072002178, 1992604329622767, 2005654971558583, 1995326722287162,
    1998675789524315, 2001709440777254, 1996236194580634, 2012951729814739, 1990196379856393,
    1994710571618345, 2003292903353962, 1994433492302197, 2004552685102960, 2008363506326019,
    2000698812608704, 1999594124227548, 1995858155128933, 1993764292340321, 1999804698386903,
    2003051916128380, 2001512361052960, 1998241985952339, 1995040930411962, 1998663064022595,
    2003173296099540, 1996264998043996, 1990896983518878, 2001254791195878, 2011903930816870,
    2003851390295241, 1999297774391043, 2001059781109230, 2015020588326517, 2004655998053030,
    2020350274029822, 2009401577878964, 2018994674055967, 1997926155456133, 2000907963303260,
    2023174703047336, 2007586331024876, 2017894612356344, 1988377935252717, 1995037496432870,
    2000059342606831, 1988508006253056, 1982870321603696, 1981950114468123, 1984378951490881,
    1981968205773553, 1985842126465838, 1988158665838725, 1983165181051512, 1999935989823209,
    2014650072747609, 2006395389698548, 2014288246859074, 2025449023735071]
private def pvn_m16_r384_7_8_p1 : List ℕ :=
  [2009306655400699, 1999636840618651, 2011547217045217, 2008945676544791, 1990657177071767,
    1985813809014553, 1989592467792697, 1986485818712575, 1987453846749026, 2000300465833683,
    2010313447768897, 2008140432717307, 2004102816279936, 2008022336266497, 2016269165993027,
    2021783520493736, 2021488917898757, 2014021532731515, 2002309912018150, 1995005652138484,
    1995398908091020, 1994128441871185, 1981564529093537, 1962270664812802, 1948739344660461,
    1943611981306310, 1935562061787641, 1912860515820116, 1875931221242632, 1835108314530796,
    1799328044653659, 1769534084980413, 1741952333389749, 1715047601112870, 1692169809163223,
    1678545285181655, 1677148345656284, 1687515313341986, 1707410074606479, 1734815523402592,
    1768545876722366, 1807601055473693, 1850220813759390, 1893440000859362, 1933483595961229,
    1966834414591667, 1991376122074180, 2006946733409225, 2015041835201128, 2017954557397351,
    2017893342823777, 2016466945944818, 2014598795851460, 2012702652733168, 2010913726272856,
    2009255077890579, 2007719042876546, 2006295702246320, 2004982647575881, 2003790356908539,
    2002742012579999, 2001864927740065, 2001177057661898, 2000676501314797]
private def pvn_m16_r384_7_8_p2 : List ℕ :=
  [2000339935677276, 2000129972833969, 2000006507246930, 1999936191773062, 1999896701081431,
    1999875900532047, 1999868242596064, 1999870980142288, 1999881745783926, 1999897752441873,
    1999916052069000, 1999934113591560, 1999950223175147, 1999963552419248, 1999973975220968,
    1999981790385374, 1999987473918375, 1999991515710964, 1999994339854877, 1999996282167543,
    1999997596530678, 1999998470566273, 1999999041124700, 1999999406694451, 1999999636847372,
    1999999779548655, 1999999866959201, 1999999920039094, 1999999952095541, 1999999971395195,
    1999999982992119, 1999999989946352, 1999999994103016, 1999999996574632, 1999999998033263,
    1999999998885591, 1999999999377649, 1999999999657776, 1999999999814806, 1999999999901390,
    1999999999948325, 1999999999973339, 1999999999986447, 1999999999993203, 1999999999996637,
    1999999999998362, 1999999999999214, 1999999999999631, 1999999999999832, 1999999999999929,
    1999999999999973, 1999999999999991, 1999999999999998]
private def pvn_m16_r384_7_8 : List ℕ :=
  pCat pvn_m16_r384_7_8_p0
    (pCat pvn_m16_r384_7_8_p1
      pvn_m16_r384_7_8_p2)
private def pvn_m16_r384_7_9_p0 : List ℕ :=
  [1995955542328835, 2007828598764061, 2003609042724385, 1991767249412633, 1996586247941008,
    2001768432180007, 2009154932066665, 1993485846807739, 2000480273326466, 2001784494783712,
    1993786680352504, 2006434459982979, 1989220690797998, 2003260831115008, 2010057513995825,
    1993981305025063, 1998686312106323, 1999403570895970, 1993041113083642, 1999900115213115,
    2004837151356087, 2004104011287559, 2004825466714036, 2000662153233399, 1994897490448813,
    1995089445082059, 1998017197685702, 2001860456015453, 2003801473582075, 1997862387595626,
    1994006917420302, 2000129541469948, 2005937742862853, 1993453369074679, 1992149716482264,
    1994562461598636, 2014503681906297, 1996790035542206, 2006719487406543, 1996586429583062,
    2008159234016551, 2008103854267399, 2000913085385031, 2030072687841999, 2007300844079253,
    2011461316618431, 1999922753657307, 2004213909223510, 2022336662871847, 2015441807872515,
    2003500842454986, 1999660426245451, 2002501435505843, 1997253695750341, 1988667089701962,
    1989987438869478, 1982340648936038, 1978994367094752, 1991248299433859, 1983974494867948,
    1973816438403230, 1990092919814654, 1999568391677374, 1993794363432067]
private def pvn_m16_r384_7_9_p1 : List ℕ :=
  [2006330258703409, 2023728201576257, 2016228507088657, 2005265271213089, 2011864638845743,
    2015813101530575, 2005863210284685, 1997853690862145, 1996089114483178, 1989859770704142,
    1981822561957342, 1984525700302438, 1996361772522339, 2004402931683651, 2004548072988870,
    2002975386476180, 2004472401804192, 2010040209413673, 2018619954434511, 2024394404752953,
    2020257825757739, 2008552921830956, 2000618060723618, 2001674513288285, 2003080478286584,
    1994175909225581, 1976732742740447, 1962251583648709, 1956976179187595, 1954288945631366,
    1942323986341641, 1916076304480283, 1880652306931865, 1844484508772743, 1811673775730287,
    1780985118844113, 1750371890397960, 1720933130319308, 1696711053642552, 1681793014524460,
    1678050318817029, 1685046553625741, 1701328189662245, 1725622479379069, 1757118403729490,
    1794892545730025, 1837094798833314, 1880608347545385, 1921545185137146, 1956343369608963,
    1982823527180049, 2000634915972119, 2010960060509648, 2015774222008745, 2017095415574185,
    2016517324833670, 2015077142602217, 2013345156514241, 2011587792327020, 2009907614676977,
    2008331815481878, 2006860624757186, 2005493627262335, 2004242687362350]
private def pvn_m16_r384_7_9_p2 : List ℕ :=
  [2003132827559926, 2002192935314480, 2001442380023879, 2000881295791811, 2000489292919249,
    2000232084991356, 2000071636363935, 1999974853976403, 1999917942818898, 1999886357115953,
    1999872132174991, 1999870722942302, 1999878741636874, 1999892970789542, 1999910318442731,
    1999928157861253, 1999944622762188, 1999958678875102, 1999969991362017, 1999978694049320,
    1999985161790284, 1999989842073012, 1999993157216731, 1999995462428039, 1999997037743594,
    1999998095704238, 1999998793737125, 1999999246195303, 1999999534508664, 1999999715380894,
    1999999827336441, 1999999895889507, 1999999937527492, 1999999962673092, 1999999977797180,
    1999999986863593, 1999999992279444, 1999999995499827, 1999999997402864, 1999999998518297,
    1999999999165492, 1999999999536526, 1999999999746361, 1999999999863295, 1999999999927446,
    1999999999962074, 1999999999980467, 1999999999990084, 1999999999995039, 1999999999997553,
    1999999999998811, 1999999999999434, 1999999999999739, 1999999999999885, 1999999999999953,
    1999999999999983, 1999999999999995]
private def pvn_m16_r384_7_9 : List ℕ :=
  pCat pvn_m16_r384_7_9_p0
    (pCat pvn_m16_r384_7_9_p1
      pvn_m16_r384_7_9_p2)
private def pvn_m16_r384_7_10_p0 : List ℕ :=
  [1994218677100894, 2003651644147583, 2008799247149696, 1997855883536393, 1995546966866809,
    1991635227457579, 2008370899657353, 2003137305902349, 1995042989330936, 2006709447007343,
    1991444090810856, 2004447895242805, 2002052730961271, 1988204083294878, 2002586049267750,
    2006530161407391, 1998354848017528, 2001419377481886, 2000179148888781, 1994164993095949,
    1996090941531048, 1999314742367322, 2001439843479574, 2005549275262841, 2005760335961395,
    2001237004701467, 1997717727173808, 1994319164836846, 1995915372845531, 2001294290129748,
    2006949174964740, 1993928324753511, 1997815751621917, 1995744978260803, 2013474988675472,
    1989258544195278, 1994734796918104, 1994500542609501, 2000569375045496, 2011828169723617,
    1988663694254194, 2013220437341273, 1998901600681089, 1999358149125258, 2007140143736710,
    2009398507183249, 2021868636265022, 2015391906559387, 2000781306089267, 2000800997002039,
    2013375763452432, 2019491282709030, 2009259323844248, 2007359529983072, 2008659025955392,
    1998244409229948, 1999915398433048, 2000519974347106, 1982961745492161, 1981389820710732,
    1994131534939743, 1985497258938645, 1973973622989098, 1984323901785016]
private def pvn_m16_r384_7_10_p1 : List ℕ :=
  [1990155958340477, 1982211993006905, 1989377648474542, 2009866755726867, 2015491508374473,
    2009036047707521, 2010467771202846, 2016197613991993, 2013820222525045, 2008122624473861,
    2006758483151924, 2003487881432342, 1992758913114846, 1982953900304625, 1983277588087827,
    1990956668991452, 1998339605833119, 2001996978162042, 2001824357811350, 2000252525134060,
    2003097165661112, 2013209872270490, 2023501929433499, 2023653504907921, 2013908981803967,
    2005489056988712, 2005898264701793, 2009384791828009, 2004973277244662, 1990508757270039,
    1974869588960719, 1967010962739586, 1965865437644177, 1961910015123579, 1946868968222093,
    1920412783831418, 1888240274383972, 1855687606079443, 1824052350411750, 1792060978026646,
    1759385925092907, 1728331303441733, 1702764185332247, 1685987530870150, 1679461140336159,
    1682966063038175, 1695605036460398, 1716662284917487, 1745696264890487, 1781911879288401,
    1823407966986692, 1866970578109249, 1908662084273459, 1944892191114169, 1973373583602235,
    1993509997588077, 2006149882805608, 2012963193671184, 2015790874238153, 2016204199217826,
    2015330625541746, 2013874190484350, 2012222409902786, 2010560888152583]
private def pvn_m16_r384_7_10_p2 : List ℕ :=
  [2008962681706379, 2007449453705037, 2006030164959704, 2004721118305635, 2003549657859800,
    2002546057083644, 2001731151888112, 2001107393149612, 2000657540488113, 2000350453485393,
    2000150165181373, 2000023945705678, 1999946775015642, 1999901971600167, 1999879329485952,
    1999872520689279, 1999877020256243, 1999889011144332, 1999905110131406, 1999922505578203,
    1999939144958907, 1999953786461847, 1999965892899564, 1999975433695380, 1999982674540649,
    1999988007598223, 1999991840520113, 1999994538234193, 1999996401340317, 1999997665048000,
    1999998507172602, 1999999058682238, 1999999413847769, 1999999638999162, 1999999779725420,
    1999999866622024, 1999999919749151, 1999999951977850, 1999999971411413, 1999999983072928,
    1999999990039798, 1999999994182314, 1999999996631499, 1999999998069298, 1999999998906017,
    1999999999387903, 1999999999662135, 1999999999816140, 1999999999901397, 1999999999947890,
    1999999999972865, 1999999999986074, 1999999999992953, 1999999999996487, 1999999999998274,
    1999999999999170, 1999999999999610, 1999999999999822, 1999999999999924, 1999999999999970,
    1999999999999991, 1999999999999998]
private def pvn_m16_r384_7_10 : List ℕ :=
  pCat pvn_m16_r384_7_10_p0
    (pCat pvn_m16_r384_7_10_p1
      pvn_m16_r384_7_10_p2)
private def pvn_m16_r384_7_11_p0 : List ℕ :=
  [1993960160986597, 1998117664471612, 2008732961678310, 2003116141070991, 2002989474581324,
    1989197672423613, 1995353207604492, 2009559388684249, 1994502819874606, 2006743258634697,
    1999704145416166, 1992516651534000, 2007499561588336, 2001056346063671, 1990306365316319,
    1999206988468647, 2002948671884429, 1999864425453800, 2002700153885008, 2002565605557999,
    1997775031408916, 1996280112640797, 1996223216342710, 1996448479739478, 2001184285194144,
    2004280054431728, 2006195761233452, 2002395747628326, 2003525336431895, 1989103321420767,
    1999594970004488, 1995595622909037, 2012482932556175, 1991579226479643, 1994184688554966,
    2005248767146619, 1998156279920118, 2010890505162253, 1981150232384127, 1999148178826950,
    2001615255094802, 1995171284520095, 2004518918031542, 2001956212168886, 2003380625107056,
    2001974414235515, 1996057967512396, 2002580363441600, 2016384747818287, 2022256913458746,
    2008402862089389, 1998406696728173, 2009769550165829, 2012526424190608, 2009749069944727,
    2016976898150337, 2011143975060140, 1999963457728387, 2008363032972854, 2009986795374467,
    1990955091442147, 1985907130440753, 1996146745698960, 1990293239346594]
private def pvn_m16_r384_7_11_p1 : List ℕ :=
  [1978176595923509, 1983249868814314, 1989044608624304, 1980122666066833, 1976174805308590,
    1989558616732035, 2003063891100859, 2005473644152117, 2006853663434145, 2012676953039629,
    2015046595267193, 2012026025804076, 2011195780345369, 2013118471696987, 2009721886089808,
    1999051472430421, 1988414356854596, 1984008927083566, 1986317933959670, 1992992027593588,
    1999532927025956, 2000656740070332, 1996901918906094, 1996619120251563, 2005884482276142,
    2018901473002338, 2023912299843024, 2017743840952310, 2009414385698397, 2008342770019816,
    2012887146499547, 2013135336252586, 2003205383830498, 1987834036270221, 1976560700688532,
    1973366318750850, 1973132279878926, 1967227719224322, 1951067804157528, 1926337998050149,
    1897494286754712, 1867419741064804, 1836261904946305, 1803327139379119, 1769346679697907,
    1737051796664944, 1710029535934920, 1691132815321682, 1681650940074757, 1681581801436173,
    1690497508733009, 1708182108533857, 1734538731182663, 1768904372204664, 1809375344429418,
    1852716931228266, 1894994090511306, 1932586143129451, 1963062049893042, 1985550555861072,
    2000560704349132, 2009464218418654, 2013924657466607, 2015475335028920]
private def pvn_m16_r384_7_11_p2 : List ℕ :=
  [2015309912550108, 2014245585503410, 2012781594759435, 2011188710871675, 2009594584159378,
    2008051915334172, 2006586028215338, 2005221392937275, 2003989199363860, 2002921692195717,
    2002041512513190, 2001353663304531, 2000844149809614, 2000484977170143, 2000242277560441,
    2000083840644118, 1999983688315048, 1999923279238862, 1999890344127685, 1999876805430979,
    1999876915102659, 1999886116642817, 1999900604512501, 1999917294072943, 1999933904340216,
    1999948974060050, 1999961763305520, 1999972075651248, 1999980060856965, 1999986045067110,
    1999990409977304, 1999993521010716, 1999995693252731, 1999997181428961, 1999998182661991,
    1999998844616170, 1999999274971946, 1999999550354023, 1999999724014053, 1999999832109811,
    1999999898644165, 1999999939215240, 1999999963765467, 1999999978527272, 1999999987354356,
    1999999992604550, 1999999995709415, 1999999997533446, 1999999998596649, 1999999999210679,
    1999999999561533, 1999999999759634, 1999999999870034, 1999999999930713, 1999999999963587,
    1999999999981133, 1999999999990364, 1999999999995150, 1999999999997597, 1999999999998828,
    1999999999999441, 1999999999999744, 1999999999999886, 1999999999999954]
private def pvn_m16_r384_7_11_p3 : List ℕ := [1999999999999983, 1999999999999995]
private def pvn_m16_r384_7_11 : List ℕ :=
  pCat pvn_m16_r384_7_11_p0
    (pCat pvn_m16_r384_7_11_p1
    (pCat pvn_m16_r384_7_11_p2
      pvn_m16_r384_7_11_p3))
private def pvn_m16_r384_7_12_p0 : List ℕ :=
  [1995213984768172, 1993579699800987, 2005231271289582, 2002919800993128, 2008751216000260,
    2000980725693505, 1985199494607277, 2004521720965313, 1998293934112396, 1998479930664260,
    2009344522249425, 1996854641531363, 1993969484290362, 2006708830177437, 2002732760464382,
    1993716081012443, 1996981072078139, 1999663191276887, 1998838702525822, 2001674092673592,
    2003669190661096, 2001052236199527, 2000062117855693, 1996652036962107, 1996658321857375,
    1993118160614197, 2003901527073787, 1996254841154446, 2011354456584897, 2000668741967387,
    2008597741975128, 1992093297330382, 1989152962328033, 2010388537134395, 1994408582758980,
    2007870298383183, 1987044260617545, 1998302619243495, 2012119165779987, 1996878739181563,
    1996785804804609, 1996143739678289, 1995009006881833, 1998781575841892, 1997948397611079,
    2000693162748090, 2005136103546644, 2005201215558539, 1997033573489322, 1990365852863813,
    2007025742154017, 2021602453165835, 2011619447256264, 2006589320445936, 2009634380417101,
    2003314320731904, 2006643387012852, 2019977463477331, 2013825995766402, 2001859607192808,
    2010711873152597, 2016913042473915, 2002088382009078, 1993028920693694]
private def pvn_m16_r384_7_12_p1 : List ℕ :=
  [1999380125357132, 1996955052680998, 1984574610969763, 1983627538302965, 1990747508279199,
    1986883768476316, 1976289763830263, 1976425286663767, 1986302905476672, 1993525582972604,
    1997519373749239, 2004317265481717, 2011004106950090, 2011899076951272, 2010381449996070,
    2012447628835008, 2015975785022462, 2014717478081480, 2007232870621089, 1996815138790081,
    1987682134123903, 1984252804602977, 1988788407660217, 1996805661858035, 1999686296977583,
    1995195514837935, 1991645026364176, 1997848015533552, 2011354035452367, 2020792924007644,
    2019361472429468, 2012250305268039, 2009445028702078, 2013654104499085, 2017750990894780,
    2013551319511336, 2000923183184347, 1987437725617470, 1980225685682972, 1979330312449010,
    1978556300938169, 1971405744520417, 1955685294687249, 1933365580985265, 1907398061914492,
    1879163674695789, 1848430285603620, 1815007165937126, 1780195334833145, 1746869855325339,
    1718381728112274, 1697283031374976, 1684777711720722, 1681088790501345, 1686224714954180,
    1700419374199396, 1723884737796838, 1756101859072412, 1795224226006006, 1838064246024902,
    1880725175134507, 1919553015081013, 1951954308708195, 1976771780619873]
private def pvn_m16_r384_7_12_p2 : List ℕ :=
  [1994176363754114, 2005244401372265, 2011454946646546, 2014284104367715, 2014967339049038,
    2014414956387658, 2013228029782564, 2011762764066368, 2010207872533971, 2008655111302056,
    2007152719340677, 2005737540557844, 2004446932871253, 2003316327580489, 2002370806673743,
    2001618216693129, 2001047880167779, 2000634937057462, 2000347664224081, 2000154543278660,
    2000028908018603, 1999950630683450, 1999905563579437, 1999883935693825, 1999878722199859,
    1999884516795023, 1999896978327347, 1999912665393658, 1999929021670566, 1999944347195659,
    1999957693432900, 1999968694639127, 1999977378557156, 1999983996393772, 1999988894127529,
    1999992429136845, 1999994924792183, 1999996651585302, 1999997824141155, 1999998606272393,
    1999999119184872, 1999999450179648, 1999999660601872, 1999999792558174, 1999999874309185,
    1999999924425049, 1999999954872307, 1999999973228932, 1999999984222387, 1999999990765705,
    1999999994636440, 1999999996911148, 1999999998238041, 1999999999005494, 1999999999445094,
    1999999999694173, 1999999999833623, 1999999999910696, 1999999999952718, 1999999999975317,
    1999999999987294, 1999999999993552, 1999999999996777, 1999999999998415]
private def pvn_m16_r384_7_12_p3 : List ℕ :=
  [1999999999999237, 1999999999999644, 1999999999999838, 1999999999999931, 1999999999999974,
    1999999999999992, 1999999999999999]
private def pvn_m16_r384_7_12 : List ℕ :=
  pCat pvn_m16_r384_7_12_p0
    (pCat pvn_m16_r384_7_12_p1
    (pCat pvn_m16_r384_7_12_p2
      pvn_m16_r384_7_12_p3))
private def pvn_m16_r384_7_13_p0 : List ℕ :=
  [1997489622401388, 1991182412132878, 2001245856099625, 2000290965974748, 2004121307388508,
    2014856627591465, 1991819890370466, 1994251567298814, 2002113140422014, 1993030335032947,
    2000832788122789, 2009263822737029, 1997691298626711, 1994266021214196, 2004165844220672,
    2004275874178408, 1997785044754305, 1997159823116002, 1998213177290069, 1996704940482112,
    2000009755789619, 2000597296406995, 2004702485897844, 1998386914314749, 2006717225833966,
    1991497201110716, 2001952702375727, 1990822863508674, 1999936112785683, 2000655907286097,
    1995541549816255, 2020492611537056, 1995917091415631, 2001852791001952, 1992420660202719,
    1994914747417268, 2012109402778492, 1996429709266953, 1991200241824902, 2000182770283882,
    2002385962870358, 2003647800217914, 1999847899682745, 1996426321836819, 1996682533084103,
    1996711064919827, 1997057825071313, 1994463076481713, 2001534461954325, 2012603721487065,
    2000613930075776, 1986923216753605, 1998643553747484, 2009658096494390, 2008778069882556,
    2014370461804916, 2014598295545889, 2000804391006328, 2001185080512645, 2016834835213374,
    2015710593011057, 2003688307610230, 2008629194200408, 2018683660106047]
private def pvn_m16_r384_7_13_p1 : List ℕ :=
  [2011561607259605, 2001118634587248, 2003530579161268, 2004890698621062, 1994322666949468,
    1986334147958885, 1990377240746621, 1993458728928454, 1986160962746807, 1978055915525829,
    1978159174073433, 1982104259575146, 1985226375703799, 1990762417695633, 1999822768094665,
    2006654964142948, 2008098935848109, 2008264811516073, 2011147308224442, 2015361021578042,
    2017394440777618, 2014873142887689, 2006646448504469, 1994684753278625, 1985824080922458,
    1986423843723170, 1994074530140530, 1998890347754622, 1995228384855893, 1989048910114278,
    1990730682419013, 2002206361544912, 2014498469046088, 2018201438036601, 2013748216222255,
    2009710275593177, 2012260644967111, 2018427442026479, 2019990142010145, 2012537279245906,
    1999661853594874, 1988853485819824, 1984385618402328, 1984217657678251, 1982671077338051,
    1975174052969639, 1960713808170113, 1940868657173519, 1917387416828431, 1890756423275617,
    1860601929164319, 1827066036268555, 1791767753075528, 1757611392199209, 1727730570853352,
    1704442837461178, 1688920173572136, 1681622738798486, 1682962078700808, 1693570424308886,
    1713942461119274, 1743726151247584, 1781188342974722, 1823241978987007]
private def pvn_m16_r384_7_13_p2 : List ℕ :=
  [1866055530515747, 1905944546547258, 1940148895465426, 1967226250520411, 1987014932952854,
    2000297189101866, 2008357675197089, 2012594748947640, 2014261335859243, 2014340783253168,
    2013524986135126, 2012253721922531, 2010780942485208, 2009243874628294, 2007719647052120,
    2006261908190678, 2004917061275331, 2003725441251588, 2002715504032873, 2001898355355736,
    2001266746976977, 2000798959741694, 2000465470310434, 2000235623921652, 2000082326966473,
    1999984131875414, 1999925204340974, 1999894158922037, 1999882672078493, 1999884406998387,
    1999894393204138, 1999908756497231, 1999924617467730, 1999940013782006, 1999953778520192,
    1999965371509527, 1999974692850632, 1999981911387989, 1999987329098269, 1999991287649415,
    1999994112677287, 1999996086376371, 1999997438533032, 1999998348012085, 1999998949209978,
    1999999340160836, 1999999590517979, 1999999748585235, 1999999847108314, 1999999907817695,
    1999999944851796, 1999999967245764, 1999999980682548, 1999999988688254, 1999999993426020,
    1999999996210659, 1999999997835359, 1999999998775633, 1999999999314890, 1999999999621044,
    1999999999792940, 1999999999888304, 1999999999940540, 1999999999968773]
private def pvn_m16_r384_7_13_p3 : List ℕ :=
  [1999999999983823, 1999999999991737, 1999999999995844, 1999999999997942, 1999999999999000,
    1999999999999525, 1999999999999782, 1999999999999905, 1999999999999962, 1999999999999987,
    1999999999999997]
private def pvn_m16_r384_7_13 : List ℕ :=
  pCat pvn_m16_r384_7_13_p0
    (pCat pvn_m16_r384_7_13_p1
    (pCat pvn_m16_r384_7_13_p2
      pvn_m16_r384_7_13_p3))
private def pwalks_m16_r384 : List RkmSegWalk := [
  ⟨uOfHb phb_m16_r384_0, bDec bZ (zPad bZ 1 pvn_m16_r384_0_0),
    bDec bZ (zPad bZ 17 pvn_m16_r384_0_1)⟩,
  ⟨uOfHb phb_m16_r384_1, bDec bZ (zPad bZ 17 pvn_m16_r384_1_0),
    bDec bZ (zPad bZ 17 pvn_m16_r384_1_1)⟩,
  ⟨uOfHb phb_m16_r384_2, bDec bZ (zPad bZ 17 pvn_m16_r384_2_0),
    bDec bZ (zPad bZ 193 pvn_m16_r384_2_4)⟩,
  ⟨uOfHb phb_m16_r384_3, bDec bZ (zPad bZ 193 pvn_m16_r384_3_0),
    bDec bZ (zPad bZ 209 pvn_m16_r384_3_1)⟩,
  ⟨uOfHb phb_m16_r384_4, bDec bZ (zPad bZ 209 pvn_m16_r384_4_0),
    bDec bZ (zPad bZ 353 pvn_m16_r384_4_1)⟩,
  ⟨uOfHb phb_m16_r384_5, bDec bZ (zPad bZ 353 pvn_m16_r384_5_0),
    bDec bZ (zPad bZ 385 pvn_m16_r384_5_3)⟩,
  ⟨uOfHb phb_m16_r384_6, bDec bZ (zPad bZ 385 pvn_m16_r384_6_0),
    bDec bZ (zPad bZ 385 pvn_m16_r384_6_4)⟩,
  ⟨uOfHb phb_m16_r384_7, bDec bZ (zPad bZ 385 pvn_m16_r384_7_0),
    bDec bZ (zPad bZ 385 pvn_m16_r384_7_13)⟩
  ]
private def phb_m32_r384_0 : List ℕ :=
  [241669030822211, 335950762239263, 404234461805363, 458323242246803, 502847407277873,
    540203646338796, 571823491523269, 598640468366247, 621299776099034, 640265278804028,
    655879237580299, 668397913267794, 678013814974863, 684870046312640, 689069683790079,
    690681834988367, 689745316815259, 686270472419508, 680239364092615, 671604357524994,
    660284893519822, 646161970942411, 629069461054138, 608780699896156, 584987582292820,
    557266988958135, 525024318239014, 487392144228558, 443031282261041, 389686921387002,
    322981669309035, 231708913574472]
private def pvn_m32_r384_0_1 : List ℕ :=
  [2478962317108799, 2588466631325337, 2502504896553865, 2344190223254322, 2200461005879522,
    2102468160123357, 2046887962598151, 2019465466746380, 2007402079773821, 2002596561746207,
    2000844730481742, 2000255907068731, 2000072417312189, 2000019187448963, 2000004768155254,
    2000001112624599, 2000000243953170, 2000000050271222, 2000000009733941, 2000000001769767,
    2000000000301780, 2000000000048178, 2000000000007183, 2000000000000996, 2000000000000127,
    2000000000000014, 2000000000000001]
private def phb_m32_r384_1 : List ℕ :=
  [217237710554232, 301988112417667, 363368730825597, 411989453099330, 452012486430416,
    485592229026733, 514015493491295, 538121431407851, 558490016153142, 575538217874007,
    589573697081687, 600826808149621, 609470598645453, 615633705245341, 619408784028306,
    620857956204782, 620016114521028, 616892556494181, 611471157812765, 603709099716248,
    593533967069676, 580838789054465, 565474231572188, 547236545059579, 525848771965480,
    500930567879736, 471947441885703, 438119659743340, 398243420494773, 350291861340385,
    290330118646010, 208284502688130]
private def pvn_m32_r384_1_0 : List ℕ :=
  [2478962317108799, 2588466631325337, 2502504896553865, 2344190223254322, 2200461005879522,
    1897531839876643, 2046887962598151, 1980534533253620, 2007402079773821, 1997403438253793,
    2000844730481742, 2000255907068731, 1999927582687811, 2000019187448963, 2000004768155254,
    2000001112624599, 1999999756046830, 2000000050271222, 2000000009733941, 1999999998230233,
    2000000000301780, 2000000000048178, 1999999999992817, 1999999999999004, 2000000000000127,
    2000000000000014, 2000000000000001]
private def pvn_m32_r384_1_1 : List ℕ :=
  [2172770779655236, 2320573625409250, 2489476655526772, 2383038298444853, 2544114005808364,
    2375337320489165, 2193608113977260, 2077114541968560, 2025434914566659, 2007626714020179,
    2001700385553390, 2000245478694490, 2000185985344514, 2000217239901340, 2000149397525760,
    2000075055080147, 2000032047169991, 2000012485751511, 2000004475068203, 2000001452244736,
    2000000421956509, 2000000109670398, 2000000025639189, 2000000005433760, 2000000001050708,
    2000000000185596, 2000000000029734, 2000000000004254, 2000000000000531, 2000000000000055,
    2000000000000004]
private def phb_m32_r384_2 : List ℕ :=
  [232663198007241, 323431506509660, 389170603731852, 441243757627500, 484108722945923,
    520072876134550, 550514403028104, 576332041191942, 598146946410886, 616405696802470,
    631437799054384, 643489964407796, 652747528090152, 659348260934975, 663391398289595,
    664943472430782, 664041853748380, 660696499952148, 654890141784993, 646576920037046,
    635679277562084, 622082647820616, 605627092886472, 586094395467357, 563187931973377,
    536500350722428, 505459207981536, 469229402600809, 426521654832692, 375165179597200,
    310945708779872, 223074246028156]
private def pvn_m32_r384_2_0 : List ℕ :=
  [2172770779655236, 2320573625409250, 2489476655526772, 2383038298444853, 2544114005808364,
    2375337320489165, 2193608113977260, 2077114541968560, 1974565085433341, 2007626714020179,
    2001700385553390, 1999754521305510, 1999814014655486, 1999782760098660, 2000149397525760,
    2000075055080147, 1999967952830009, 1999987514248489, 2000004475068203, 1999998547755264,
    2000000421956509, 2000000109670398, 1999999974360811, 1999999994566240, 1999999998949292,
    2000000000185596, 2000000000029734, 2000000000004254, 2000000000000531, 2000000000000055,
    2000000000000004]
private def pvn_m32_r384_2_1 : List ℕ :=
  [2070529732698052, 1955778015612721, 2160335333233254, 2244036136146283, 2220539182110927,
    2320757773386522, 2390755083160680, 2448125168769450, 2449557916628736, 2359740335244582,
    2229837336534001, 2121423625690011, 2055492517135043, 2023004981082791, 2008803298915353,
    2002979218005166, 2000851712497872, 2000228981272484, 2000082381201632, 2000038671605361,
    2000015129833255, 2000003267541485, 1999999579220682, 1999999332191172, 1999999715821096,
    1999999933188754, 1999999993412604, 2000000001093435, 2000000000439965, 2000000000019516,
    1999999999980346, 1999999999994332, 1999999999999346]
private def phb_m32_r384_3 : List ℕ :=
  [240784659536273, 334721373406931, 402755193445693, 456646039695272, 501007271590268,
    538226808049852, 569730942573957, 596449784524703, 619026172070945, 637922271816202,
    653479092378468, 665951956828676, 675532669801262, 682363811229488, 686548080420871,
    688154332062135, 687221241013215, 683759112572820, 677750074674266, 669146667322466,
    657868626121467, 643797385413093, 626767424395472, 606552908571013, 582846860253881,
    555227708534164, 523103027662848, 485608566018801, 441410039590968, 388260888756310,
    321799739985077, 230860990656240]
private def pvn_m32_r384_3_0 : List ℕ :=
  [2070529732698052, 2044221984387279, 2160335333233254, 2244036136146283, 2220539182110927,
    2320757773386522, 2390755083160680, 2448125168769450, 2449557916628736, 2359740335244582,
    2229837336534001, 2121423625690011, 1944507482864957, 1976995018917209, 1991196701084647,
    1997020781994834, 1999148287502128, 1999771018727516, 1999917618798368, 2000038671605361,
    2000015129833255, 1999996732458515, 1999999579220682, 1999999332191172, 2000000284178904,
    2000000066811246, 2000000006587396, 1999999998906565, 1999999999560035, 2000000000019516,
    2000000000019654, 2000000000005668, 1999999999999346]
private def pvn_m32_r384_3_1 : List ℕ :=
  [1997840775859350, 2053309069738602, 2045906134512920, 2019491402268276, 1963259209593762,
    2030618121806842, 2015241504999922, 2056130076482842, 2119326037517441, 2111050688086740,
    2109259595935603, 2158597721830700, 2206772542071710, 2244386745307585, 2312623041528811,
    2405812194696474, 2460811666393172, 2430641606284484, 2328583521422858, 2205116208479244,
    2103898709089841, 2040999622618634, 2010717768149007, 1999972951378475, 1997900552906966,
    1998452752729294, 1999242258542863, 1999710602811218, 1999910239699801, 1999977291997386,
    1999995413690153, 1999999305248050, 1999999933741966]
private def phb_m32_r384_4_p0 : List ℕ :=
  [93600877714176, 132026912925097, 161277093147358, 185739241714068, 207117738600432,
    226289046258194, 243775197352060, 259917212390400, 274952578285392, 289054652898135,
    302354642690811, 314954742114999, 326936427651055, 338365927482768, 349297960973016,
    359778373713864, 369846042738316, 379534284936114, 388871918530482, 397884076785042,
    406592841237458, 415017741153352, 423176152245836, 431083618465479, 438754114285200,
    446200260420532, 453433502723202, 460464261665003, 467302058124083, 473955619917957,
    480432972573896, 486741517102446, 492888096983360, 498879056142179, 504720289358920,
    510417286285116, 515975170035051, 521398731148943, 526692457590581, 531860561332569,
    536907001993229, 541835507916334, 546649595024856, 551352583730304, 555947614138003,
    560437659754295, 564825539872747, 569113930792250, 573305375999328, 577402295429602,
    581406993908566, 585321668859148, 589148417352725, 592889242570942, 596546059737631,
    600120701573211, 603614923317919, 607030407364966, 610368767540182, 613631553060704,
    616820252201765, 619936295697593, 622981059899710, 625955869713552]
private def phb_m32_r384_4_p1 : List ℕ :=
  [628862001332217, 631700684784308, 634473106311148, 637180410587208, 639823702796264,
    642404050574632, 644922485831795, 647380006457786, 649777577925878, 652116134798347,
    654396582142424, 656619796862946, 658786628957620, 660897902700388, 662954417757873,
    664956950243494, 666906253713504, 668803060108799, 670648080646124, 672442006661950,
    674185510412094, 675879245829894, 677523849245562, 679119940069121, 680668121439177,
    682168980839600, 683623090686050, 685031008884143, 686393279360919, 687710432571179,
    688982985980127, 690211444523675, 691396301047669, 692538036727206, 693637121467156,
    694694014284900, 695709163676252, 696683007965481, 697615975640243, 698508485672253,
    699360947824413, 700173762945097, 700947323250268, 701682012594006, 702378206728068,
    703036273550990, 703656573347263, 704239459017064, 704785276296992, 705294363972245,
    705767054080641, 706203672108867, 706604537181313, 706969962241846, 707300254228829,
    707595714243710, 707856637713456, 708083314547110, 708276029286746, 708435061253034,
    708560684685691, 708653168879005, 708712778312662, 708739772778066]
private def phb_m32_r384_4_p2 : List ℕ :=
  [708734407500353, 708696933256258, 708627596488038, 708526639413580, 708394300132877,
    708230812731004, 708036407377735, 707811310423946, 707555744494921, 707269928580682,
    706954078123474, 706608405102489, 706233118115967, 705828422460748, 705394520209380,
    704931610284888, 704439888533263, 703919547793794, 703370777967277, 702793766082225,
    702188696359116, 701555750272767, 700895106612900, 700206941542961, 699491428657251,
    698748739036438, 697979041301499, 697182501666145, 696359283987790, 695509549817104,
    694633458446203, 693731166955525, 692802830259432, 691848601150574, 690868630343074,
    689863066514556, 688832056347063, 687775744566894, 686694273983404, 685587785526790,
    684456418284912, 683300309539151, 682119594799371, 680914407837979, 679684880723136,
    678431143851131, 677153325977946, 675851554250050, 674525954234420, 673176649947839,
    671803763885475, 670407417048769, 668987728972654, 667544817752122, 666078800068157,
    664589791213058, 663077905115165, 661543254363005, 659985950228878, 658406102691900,
    656803820460509, 655179210994464, 653532380526335, 651863434082518]
private def phb_m32_r384_4_p3 : List ℕ :=
  [650172475503765, 648459607465260, 646724931496252, 644968547999244, 643190556268763,
    641391054509726, 639570139855391, 637727908384933, 635864455140630, 633979874144685,
    632074258415689, 630147699984733, 628200289911179, 626232118298099, 624243274307393,
    622233846174589, 620203921223340, 618153585879617, 616082925685617, 613992025313382,
    611880968578145, 609749838451401, 607598717073721, 605427685767307, 603236825048293,
    601026214638809, 598795933478804, 596546059737631, 594276670825416, 591987843404199,
    589679653398857, 587352176007824, 585005485713600, 582639656293058, 580254760827563,
    577850871712886, 575428060668946, 572986398749359, 570525956350812, 568046803222262,
    565549008473968, 563032640586353, 560497767418704, 557944456217712, 555372773625863,
    552782785689666, 550174557867747, 547548155038782, 544903641509302, 542241081021351,
    539560536760012, 536862071360795, 534145746916905, 531411624986374, 528659766599071,
    525890232263593, 523103081974035, 520298375216644, 517476170976359, 514636527743239,
    511779503518782, 508905155822138, 506013541696218, 503104717713696]
private def phb_m32_r384_4_p4 : List ℕ :=
  [500178739982916, 497235664153700, 494275545423056, 491298438540794, 488304397815053,
    485293477117730, 482265729889829, 479221209146716, 476159967483293, 473082057079086,
    469987529703256, 466876436719524, 463748829091020, 460604757385057, 457444271777825,
    454267422059019, 451074257636383, 447864827540192, 444639180427664, 441397364587296,
    438139427943142, 434865418059019, 431575382142653, 428269367049755, 424947419288045,
    421609585021205, 418255910072778, 414886439930008, 411501219747619, 408100294351541,
    404683708242581, 401251505600034, 397803730285248, 394340425845131, 390861635515612,
    387367402225043, 383857768597558, 380332776956385, 376792469327102, 373236887440854,
    369666072737520, 366080066368833, 362478909201461, 358862641820039, 355231304530161,
    351584937361328, 347923580069854, 344247272141738, 340556052795484, 336849960984890,
    333129035401800, 329393314478810, 325642836391943, 321877639063288, 318097760163594,
    314303237114842, 310494107092770, 306670407029370, 302832173615352, 298979443302570,
    295112252306420, 291230636608204, 287334631957462, 283424273874276]
private def phb_m32_r384_4_p5 : List ℕ :=
  [279499597651538, 275560638357193, 271607430836452, 267640009713972, 263658409396012,
    259662664072561, 255652807719433, 251628874100340, 247590896768937, 243538909070841,
    239472944145622, 235393034928772, 231299214153643, 227191514353371, 223069967862764,
    218934606820169, 214785463169327, 210622568661186, 206445954855704, 202255653123628,
    198051694648247, 193834110427128, 189602931273825, 185358187819569, 181099910514945,
    176828129631534, 172542875263548, 168244177329434, 163932065573473, 159606569567343,
    155267718711674, 150915542237582, 146550069208185, 142171328520096, 137779348904908,
    133374158930649, 128955787003233, 124524261367881, 120079610110536, 115621861159254,
    111151042285584, 106667181105926, 102170305082881, 97660441526578, 93137617595989,
    88601860300228, 84053196499838, 79491652908057, 74917256092078, 70330032474285,
    65730008333483, 61117209806109, 56491662887433, 51853393432743, 47202427158515,
    42538789643578, 37862506330252, 33173602525489, 28472103401991, 23758033999314,
    19031419224974, 14292283855520, 9540652537615, 4776549789091]
private def phb_m32_r384_4 : List ℕ :=
  pCat phb_m32_r384_4_p0
    (pCat phb_m32_r384_4_p1
    (pCat phb_m32_r384_4_p2
    (pCat phb_m32_r384_4_p3
    (pCat phb_m32_r384_4_p4
      phb_m32_r384_4_p5))))
private def pvn_m32_r384_4_0 : List ℕ :=
  [1997840775859350, 1946690930261398, 1954093865487080, 1980508597731724, 1963259209593762,
    1969381878193158, 1984758495000078, 1943869923517158, 1880673962482559, 1888949311913260,
    1890740404064397, 1841402278169300, 1793227457928290, 1755613254692415, 1687376958471189,
    1594187805303526, 1539188333606828, 1569358393715516, 1671416478577142, 1794883791520756,
    1896101290910159, 2040999622618634, 2010717768149007, 2000027048621525, 2002099447093034,
    2001547247270706, 2000757741457137, 1999710602811218, 1999910239699801, 1999977291997386,
    1999995413690153, 2000000694751950, 1999999933741966]
private def pvn_m32_r384_4_1 : List ℕ :=
  [2012635228988363, 1975730381476576, 1948371544613222, 1970164167318213, 1976634705515797,
    1961175875696691, 1967238499289698, 2002279163080190, 1977381496740585, 1920233305259897,
    1906146299643621, 1915220075077991, 1896941285754369, 1860395534066645, 1835098358443952,
    1811676292869325, 1749687955319753, 1674200486101848, 1556372222562706, 1585448869429603,
    1585778392731484, 1652894517902247, 1798661052949520, 1919911431524306, 1979220492708284,
    1997916228175104, 2002189417529358, 2002589338899238, 2001774275912284, 2000841412748384,
    2000267453472556, 2000037896426522, 1999983649416194, 1999984450789258, 1999992496280384,
    1999997262704076, 1999999168232220, 1999999780159542, 1999999948171448, 1999999988913791,
    1999999997821096, 1999999999602582, 1999999999932188, 1999999999989104, 1999999999998343,
    1999999999999762, 1999999999999968, 1999999999999997]
private def pvn_m32_r384_4_2 : List ℕ :=
  [2016172819992923, 1998428937077743, 1960555527039818, 1959819100868338, 1976732252184059,
    1976544450502279, 1952902425559169, 1971917066301443, 2006344173042863, 1989295793687949,
    1941905271813732, 1921576388295441, 1925467624421885, 1919491790123126, 1884541573546387,
    1878456909954687, 1832500265438583, 1855949364537931, 1759292513749024, 1664917685218621,
    1623863998048127, 1577707580808383, 1565195165037461, 1634240568044818, 1755441375939570,
    1868280524645336, 1941942510088777, 1979531146805314, 1995340460709018, 2000663378394772,
    2001672778902460, 2001275646246415, 2000687481723585, 2000285835641903, 2000088406130551,
    2000014950577336, 1999996093144027, 1999994866826783, 1999996988672516, 1999998646094715,
    1999999480779666, 1999999822738824, 1999999944891992, 1999999984176822, 1999999995762534,
    1999999998933836, 1999999999746526, 1999999999942794, 1999999999987697, 1999999999997471,
    1999999999999503, 1999999999999908, 1999999999999985, 1999999999999998]
private def phb_m32_r384_5_p0 : List ℕ :=
  [97409088000000, 137398510500733, 167838752610286, 193296159000000, 215544453410985,
    235495757718329, 253693343812393, 270492106834342, 286139196000000, 300815022343531,
    314656130544140, 327768872898622, 340238040808928, 352132556993947, 363509367108082,
    374416182000000, 384893460439123, 394975874833702, 404693415894407, 414072239447419,
    423135325431582, 431902997672910, 440393338826277, 448622525257608, 456605100000000,
    464354197250693, 471881728543057, 479198538312298, 486314534799452, 493238800918751,
    499979688721066, 506544900331687, 512941557661624, 519176262743000, 525255150188645,
    531183933000000, 536967942728460, 542612164820370, 548121269835133, 553499641112097,
    558751399369130, 563880424640007, 568890375895225, 573784708639314, 578566690734750,
    583239416666839, 587805820433874, 592268687221639, 596630664000000, 600894269161173,
    605061901303919, 609135847254694, 613118289405536, 617011312438788, 620816909500363,
    624536987876058, 628173374219155, 631727819372087, 635202002820199, 638597536811495,
    641915970172618, 645158791848114, 648327434187227, 651423276000000]
private def phb_m32_r384_5_p1 : List ℕ :=
  [654447645402246, 657401822467051, 660287041698710, 663104494343490, 665855330550260,
    668540661392789, 671161560764442, 673719067155034, 676214185318721, 678647887841029,
    681021116612419, 683334784215147, 685589775229610, 687786947465852, 689927133125430,
    692011139898427, 694039752000000, 696013731150521, 697933817503032, 699800730521463,
    701615169812777, 703377815916001, 705089331050838, 706750359828398, 708361529926356,
    709923452730733, 711436723946277, 712901924177343, 714319619480985, 715690361893887,
    717014689934650, 718293129082819, 719526192235982, 720714380146147, 721858181836556,
    722958075000000, 724014526379626, 725027992133200, 725998918181667, 726927740542868,
    727814885651164, 728660770663699, 729465803753984, 730230384393446, 730954903621535,
    731639744304970, 732285281386642, 732891882124692, 733459906322229, 733989706548140,
    734481628349410, 734936010455352, 735353184974135, 735733477581941, 736077207705113,
    736384688695600, 736656228000000, 736892127322487, 737092682781907, 737258185063267,
    737388919563897, 737485166534494, 737547201215263, 737575293967386]
private def phb_m32_r384_5_p2 : List ℕ :=
  [737569710399991, 737530711492823, 737458553714796, 737353489138585, 737215765551428,
    737045626562298, 736843311705571, 736609056541351, 736343092752568, 736045648238993,
    735716947208272, 735357210264104, 734966654491679, 734545493540465, 734093937704462,
    733612194000000, 733100466241188, 732558955113100, 731987858242768, 731387370268075,
    730757682904625, 730098985010651, 729411462650048, 728695299153580, 727950675178342,
    727177768765527, 726376755396560, 725547808047662, 724691097242889, 723806791105699,
    722895055409109, 721956053624474, 720989946968941, 719996894451626, 718977052918551,
    717930577096382, 716857619635012, 715758331149020, 714632860258049, 713481353626131,
    712303956000000, 711100810246417, 709872057388551, 708617836641421, 707338285446465,
    706033539505225, 704703732812204, 703348997686901, 701969464805066, 700565263229183,
    699136520438211, 697683362356610, 696205913382669, 694704296416146, 693178632885266,
    691629042773066, 690055644643133, 688458555664727, 686837891637333, 685193767014634,
    683526294927941, 681835587209078, 680121754412757, 678384905838436]
private def phb_m32_r384_5_p3 : List ℕ :=
  [676625149551693, 674842592405118, 673037340058740, 671209497000000, 669359166563286,
    667486450949043, 665591451242457, 663674267431743, 661734998426034, 659773742072886,
    657790595175410, 655785653509038, 653759011837940, 651710763931088, 649641002577989,
    647549819604089, 645437305885858, 643303551365562, 641148645065737, 638972675103360,
    636775728703737, 634557892214111, 632319251116995, 630059890043234, 627779892784812,
    625479342307405, 623158320762680, 620816909500363, 618455189080057, 616073239282845,
    613671139122655, 611248966857418, 608806800000000, 606344715328932, 603862788898941,
    601361096051264, 598839711423791, 596298708960998, 593738161923705, 591158142898651,
    588558723807887, 585939975918006, 583301969849191, 580644775584108, 577968462476634,
    575273099260422, 572558754057323, 569825494385642, 567073387168262, 564302498740612,
    561512894858498, 558704640705797, 555877800902015, 553032439509709, 550168620041788,
    547286405468679, 544385858225374, 541467040218355, 538530012832401, 535574836937275,
    532601572894302, 529610280562835, 526601019306611, 523573848000000]
private def phb_m32_r384_5_p4 : List ℕ :=
  [520528825034148, 517466008323025, 514385455309363, 511287222970504, 508171367824147,
    505037945934000, 501887012915349, 498718623940522, 495532833744277, 492329696629100,
    489109266470409, 485871596721692, 482616740419546, 479344750188645, 476055678246632,
    472749576408923, 469426496093450, 466086488325314, 462729603741382, 459355892594800,
    455965404759441, 452558189734286, 449134296647737, 445693774261859, 442236670976568,
    438763034833744, 435272913521290, 431766354377125, 428243404393123, 424704110218985,
    421148518166061, 417576674211107, 413988624000000, 410384412851379, 406764085760255,
    403127687401545, 399475262133575, 395806854001519, 392122506740791, 388422263780396,
    384706168246218, 380974262964275, 377226590463922, 373463192981004, 369684112460973,
    365889390561956, 362079068657779, 358253187840951, 354411788925605, 350554912450402,
    346682598681384, 342794887614805, 338891818979901, 334973432241645, 331039766603446,
    327090861009818, 323126754149020, 319147484455645, 315153090113187, 311143609056566,
    307119078974625, 303079537312587, 299025021274486, 294955567825559]
private def phb_m32_r384_5_p5 : List ℕ :=
  [290871213694611, 286771995376350, 282657949133685, 278529111000000, 274385516781393,
    270227202058895, 266054202190646, 261866552314057, 257664287347934, 253447441994582,
    249216050741874, 244970147865302, 240709767429999, 236434943292729, 232145709103860,
    227842098309313, 223524144152476, 219191879676105, 214845337724196, 210484550943833,
    206109551787018, 201720372512471, 197317045187417, 192899601689338, 188468073707718,
    184022492745758, 179562890122070, 175089296972355, 170601744251056, 166100262732994,
    161584883014981, 157055635517421, 152512550485882, 147955657992655, 143384987938294,
    138800570053137, 134202433898809, 129590608869705, 124965124194464, 120326008937412,
    115673292000000, 111007002122219, 106327167884003, 101633817706611, 96926979853993,
    92206682434149, 87472953400457, 82725820553002, 77965311539878, 73191453858482,
    68404274856786, 63603801734608, 58790061544849, 53963081194736, 49122887447038,
    44269506921271, 39402966094895, 34523291304490, 29630508746923, 24724644480505,
    19805724426124, 14873774368384, 9928819956709, 4970886706455]
private def phb_m32_r384_5 : List ℕ :=
  pCat phb_m32_r384_5_p0
    (pCat phb_m32_r384_5_p1
    (pCat phb_m32_r384_5_p2
    (pCat phb_m32_r384_5_p3
    (pCat phb_m32_r384_5_p4
      phb_m32_r384_5_p5))))
private def pvn_m32_r384_5_0 : List ℕ :=
  [2016172819992923, 1998428937077743, 1960555527039818, 1959819100868338, 1976732252184059,
    1976544450502279, 1952902425559169, 1971917066301443, 1993655826957137, 1989295793687949,
    1941905271813732, 1921576388295441, 1925467624421885, 1919491790123126, 1884541573546387,
    1878456909954687, 1832500265438583, 1855949364537931, 1759292513749024, 1664917685218621,
    1623863998048127, 1577707580808383, 1565195165037461, 1634240568044818, 1755441375939570,
    1868280524645336, 1941942510088777, 1979531146805314, 1995340460709018, 2000663378394772,
    2001672778902460, 2001275646246415, 2000687481723585, 2000285835641903, 2000088406130551,
    2000014950577336, 1999996093144027, 1999994866826783, 1999996988672516, 1999998646094715,
    2000000519220334, 1999999822738824, 1999999944891992, 1999999984176822, 1999999995762534,
    1999999998933836, 1999999999746526, 1999999999942794, 2000000000012303, 1999999999997471,
    1999999999999503, 1999999999999908, 1999999999999985, 1999999999999998]
private def pvn_m32_r384_5_1 : List ℕ :=
  [2008741071837633, 2019789071547211, 2005648769997710, 1983237573812490, 1959627868835057,
    1975598676306710, 1982644168482408, 1978140033886130, 1954915530977790, 1960709585028039,
    1981889808990111, 2015046488149886, 1967067940079664, 1978048764828004, 1934400904526284,
    1938362908077344, 1958033146125272, 1911913530523681, 1882250271775388, 1901824434013659,
    1903724145667416, 1865734131834126, 1819345520445435, 1771544519339734, 1704910759264143,
    1626681603314622, 1574307434189506, 1578705795857313, 1638858206708380, 1728908566210844,
    1819595724462370, 1892644707801041, 1942785184158480, 1972978903749160, 1989086634590723,
    1996627307121356, 1999601849858257, 2000460162784715, 2000508627573426, 2000344555618005,
    2000186486532399, 2000084946639534, 2000032456404805, 2000009904789644, 2000001986102246,
    1999999886866416, 1999999612718991, 1999999731044924, 1999999856447159, 1999999931388656,
    1999999969228883, 1999999986886540, 1999999994691033, 1999999997965118, 1999999999263510,
    1999999999748485, 1999999999918867, 1999999999975216, 1999999999992804, 1999999999998007,
    1999999999999472, 1999999999999866, 1999999999999969, 1999999999999994]
private def pvn_m32_r384_5_2_p0 : List ℕ :=
  [1999214278923448, 2011017100872669, 2012547599048608, 2021999286264335, 2002199804004254,
    1984962277505920, 1965827957127283, 1981709050353262, 1974120141332571, 2007170270483324,
    1954441631944585, 1955645318682938, 1974303374275503, 1970911203700072, 1999294303631932,
    2010418292996634, 1971415455983147, 1949503263776778, 1968209143482988, 1973315081680022,
    1943295980066000, 1915382783507618, 1913738138237213, 1920641542953021, 1915160516353672,
    1899818784629031, 1883514637142146, 1860008997577471, 1814079095473134, 1742654959789045,
    1663649339943064, 1605062412911905, 1587442193989676, 1614233084133217, 1673861192134590,
    1748314697762462, 1821354601310964, 1882772020421649, 1928723668124008, 1959900565344510,
    1979261178155747, 1990290795919402, 1996027875532599, 1998711345721870, 1999798348167548,
    2000140218860934, 2000183986405782, 2000137557937582, 2000082823804221, 2000043364475760,
    2000020244777670, 2000008458410863, 2000003113801636, 2000000956124709, 2000000197105357,
    1999999981312752, 1999999946791300, 1999999958952401, 1999999975588443, 1999999987198688,
    1999999993802376, 1999999997171571, 1999999998770099, 1999999999487405]
private def pvn_m32_r384_5_2_p1 : List ℕ :=
  [1999999999794517, 1999999999920600, 1999999999970380, 1999999999989322, 1999999999996276,
    1999999999998743, 1999999999999592, 1999999999999874, 1999999999999965, 1999999999999992,
    1999999999999999]
private def pvn_m32_r384_5_2 : List ℕ :=
  pCat pvn_m32_r384_5_2_p0
      pvn_m32_r384_5_2_p1
private def phb_m32_r384_6_p0 : List ℕ :=
  [97855023157248, 138027515736731, 168607112134785, 194181061577664, 216531207847345,
    236573848478704, 254854742440473, 271730409570485, 287449130524416, 302192142251391,
    316096614527043, 329269386525000, 341795637819074, 353744606653782, 365173499378599,
    376130245260672, 386655488288154, 396784059598281, 406546087198075, 415967846654110,
    425072423106529, 433880233423060, 442409443040295, 450676302378956, 458695421049600,
    466479993377331, 474041985426073, 481392291276450, 488540864529054, 495496829679358,
    502268577013610, 508863843917141, 515289784904803, 521553032232575, 527659748597314,
    533615673154368, 539426161862775, 545096222992066, 550630548483291, 556033541742560,
    561309342352234, 566461848108738, 571494734733199, 576411473549315, 581215347379716,
    585909464876146, 590496773468630, 594980071093432, 599362016838144, 603645140624088,
    607831852030721, 611924448353504, 615925121975385, 619835967122304, 623658986064721,
    627396094819916, 631049128403523, 634619845673264, 638109933803106, 641521012421863,
    644854637446650, 648112304638345, 651295452903432, 654405467364096]
private def phb_m32_r384_6_p1 : List ℕ :=
  [657443682216213, 660411383392999, 663309811050259, 666140161887743, 668903591319660,
    671601215506230, 674234113257063, 676803327816142, 679309868537349, 681754712458671,
    684138805782507, 686463065268882, 688728379547768, 690935610356231, 693085593705617,
    695179140983582, 697217039995392, 699200055948545, 701128932384479, 703004392060799,
    704827137787244, 706597853218324, 708317203605359, 709985836510462, 711604382484797,
    713173455713283, 714693654627786, 716165562490644, 717589747950297, 718966765570636,
    720297156335579, 721581448130296, 722820156200400, 724013783590324, 725162821562041,
    726267749995200, 727329037769682, 728347143131525, 729322514043084, 730255588518274,
    731146794943655, 731996552386102, 732805270887729, 733573351748727, 734301187798712,
    734989163657151, 735637655983410, 736247033716924, 736817658307967, 737349883939473,
    737844057740328, 738300519990536, 738719604318645, 739101637891768, 739446941598573,
    739755830225521, 740028612626688, 740265591887440, 740467065482243, 740633325426849,
    740764658425128, 740861346010752, 740923664683966, 740951886043657]
private def phb_m32_r384_6_p2 : List ℕ :=
  [740946276914899, 740907099472195, 740834611358563, 740729065800655, 740590711720074,
    740419793841023, 740216552794458, 739981225218867, 739714043857819, 739415237654399,
    739085031842668, 738723648036240, 738331304314114, 737908215303837, 737454592262126,
    736970643153024, 736456572723695, 735912582577940, 735338871247521, 734735634261366,
    734103064212745, 733441350824479, 732750681012254, 732031238946117, 731283206110204,
    730506761360773, 729702080982598, 728869338743779, 728008705949021, 727120351491449,
    726204441902982, 725261141403339, 724290611947714, 723293013273161, 722268502943737,
    721217236394441, 720139366973991, 719035045986475, 717904422731909, 716747644545750,
    715564856837376, 714356203127587, 713121825085149, 711861862562405, 710576453629993,
    709265734610692, 707929840112427, 706568903060450, 705183054728741, 703772424770625,
    702337141248657, 700877330663775, 699393117983756, 697884626670991, 696351978709597,
    694795294631890, 693214693544235, 691610293152291, 689982209785668, 688330558422013,
    686655452710547, 684957004995059, 683235326336373, 681490526534317]
private def phb_m32_r384_6_p3 : List ℕ :=
  [679722714149190, 677931996522749, 676118479798729, 674282268942912, 672423467762747,
    670542178926548, 668638503982266, 666712543375858, 664764396469260, 662794161557969,
    660801935888258, 658787815674015, 656751896113237, 654694271404167, 652615034761098,
    650514278429851, 648392093702924, 646248570934336, 644083799554164, 641897868082781,
    639690864144808, 637462874482783, 635213984970553, 632944280626401, 630653845625908,
    628342763314562, 626011116220120, 623658986064721, 621286453776768, 618893599502580,
    616480502617807, 614047241738641, 611593894732800, 609120538730304, 606627250134055,
    604114104630202, 601581177198321, 599028542121404, 596456272995658, 593864442740119,
    591253123606096, 588622387186438, 585972304424624, 583302945623698, 580614380455036,
    577906677966952, 575179906593154, 572434134161047, 569669427899883, 566885854448770,
    564083479864545, 561262369629492, 558422588658943, 555564201308731, 552687271382526,
    549791862139029, 546878036299059, 543945856052504, 540995383065158, 538026678485444,
    535039802951020, 532034816595273, 529011779053704, 525970749470208]
private def phb_m32_r384_6_p4 : List ℕ :=
  [522911786503243, 519834948331908, 516740292661905, 513627876731417, 510497757316876,
    507349990738652, 504184632866632, 501001739125723, 497801364501257, 494583563544311,
    491348390376948, 488095898697360, 484826141784945, 481539172505292, 478235043315092,
    474913806266971, 471575513014251, 468220214815624, 464847962539770, 461458806669892,
    458052797308184, 454629984180232, 451190416639345, 447734143670820, 444261213896144,
    440771675577133, 437265576620003, 433742964579384, 430203886662277, 426648389731944,
    423076520311745, 419488324588918, 415883848418304, 412263137326010, 408626236513030,
    404973190858804, 401304044924727, 397618842957611, 393917628893089, 390200446358982,
    386467338678602, 382718348874025, 378953519669302, 375172893493633, 371376512484494,
    367564418490722, 363736653075550, 359893257519608, 356034272823874, 352159739712593,
    348269698636146, 344364189773884, 340443253036925, 336506928070911, 332555254258721,
    328588270723159, 324606016329593, 320608529688571, 316595849158388, 312568012847631,
    308525058617679, 304467024085178, 300393946624481, 296305863370051]
private def phb_m32_r384_6_p5 : List ℕ :=
  [292202811218836, 288084826832615, 283951946640307, 279804206840256, 275641643402479,
    271464292070895, 267272188365513, 263065367584601, 258843864806823, 254607714893348,
    250356952489935, 246091612028989, 241811727731588, 237517333609494, 233208463467125,
    228885150903515, 224547429314240, 220195331893324, 215828891635121, 211448141336173,
    207053113597046, 202643840824139, 198220355231479, 193782688842483, 189330873491708,
    184864940826575, 180384922309072, 175890849217438, 171382752647823, 166860663515935,
    162324612558658, 157774630335658, 153210747230966, 148632993454544, 144041399043829,
    139435993865264, 134816807615804, 130183869824414, 125537209853537, 120876856900556,
    116202839999232, 111515188021126, 106813929677010, 102099093518255, 97370707938202,
    92628801173527, 87873401305580, 83104536261712, 78322233816590, 73526521593492,
    68717427065590, 63894977557218, 59059200245127, 54210122159725, 49347770186297,
    44472171066224, 39583351398180, 34681337639310, 29766156106412, 24837832977088,
    19896394290895, 14941865950473, 9974273722672, 4993643239656]
private def phb_m32_r384_6 : List ℕ :=
  pCat phb_m32_r384_6_p0
    (pCat phb_m32_r384_6_p1
    (pCat phb_m32_r384_6_p2
    (pCat phb_m32_r384_6_p3
    (pCat phb_m32_r384_6_p4
      phb_m32_r384_6_p5))))
private def pvn_m32_r384_6_0_p0 : List ℕ :=
  [1999214278923448, 2011017100872669, 2012547599048608, 2021999286264335, 2002199804004254,
    1984962277505920, 1965827957127283, 1981709050353262, 1974120141332571, 2007170270483324,
    1954441631944585, 1955645318682938, 1974303374275503, 1970911203700072, 1999294303631932,
    2010418292996634, 1971415455983147, 1949503263776778, 1968209143482988, 1973315081680022,
    1943295980066000, 1915382783507618, 1913738138237213, 1920641542953021, 1915160516353672,
    1899818784629031, 1883514637142146, 1860008997577471, 1814079095473134, 1742654959789045,
    1663649339943064, 1605062412911905, 1587442193989676, 1614233084133217, 1673861192134590,
    1748314697762462, 1821354601310964, 1882772020421649, 1928723668124008, 1959900565344510,
    2020738821844253, 1990290795919402, 1996027875532599, 1998711345721870, 1999798348167548,
    2000140218860934, 2000183986405782, 2000137557937582, 1999917176195779, 2000043364475760,
    2000020244777670, 2000008458410863, 2000003113801636, 2000000956124709, 2000000197105357,
    1999999981312752, 2000000053208700, 1999999958952401, 1999999975588443, 1999999987198688,
    1999999993802376, 1999999997171571, 1999999998770099, 1999999999487405]
private def pvn_m32_r384_6_0_p1 : List ℕ :=
  [1999999999794517, 1999999999920600, 1999999999970380, 1999999999989322, 1999999999996276,
    1999999999998743, 1999999999999592, 1999999999999874, 1999999999999965, 1999999999999992,
    1999999999999999]
private def pvn_m32_r384_6_0 : List ℕ :=
  pCat pvn_m32_r384_6_0_p0
      pvn_m32_r384_6_0_p1
private def pvn_m32_r384_6_1_p0 : List ℕ :=
  [1995025331496365, 2004801447573773, 1998941829164485, 2012719176047166, 2010141734047767,
    2031699755927962, 1994721206544334, 2009444443785661, 1977237055312587, 1959382925252904,
    1993754278898376, 1996827830262017, 1978362058778694, 1979399436079263, 1971705401038743,
    1950621698194245, 1959336173265948, 1996352435571236, 2011372617756119, 1989476612503534,
    1967627491531963, 1971564392508555, 1983889744201563, 1978536181482464, 1956568620377767,
    1937480707708854, 1931115682062956, 1930240086064981, 1925613062116103, 1917693734914551,
    1913630020358333, 1909828256309938, 1904506208061943, 1862174597243025, 1824711391683823,
    1723380293989208, 1679132594572634, 1622611460326808, 1591881921327679, 1628444434837637,
    1681706510582759, 1726829045909261, 1780804008754591, 1847084799200132, 1908050314698072,
    1950777816999625, 1975152787377207, 1987352538162398, 1993370267059897, 1996616820109603,
    1998450404914078, 1999402076887839, 1999820399446981, 1999972180716476, 2000016851320302,
    2000025344860067, 2000022475480671, 2000016396827622, 2000010399455380, 2000005857605659,
    2000002973926056, 2000001372888034, 2000000574387345, 2000000211849290]
private def pvn_m32_r384_6_1_p1 : List ℕ :=
  [2000000062749798, 2000000009140945, 1999999994161362, 1999999992670216, 1999999994672951,
    1999999996804313, 1999999998278483, 1999999999137866, 1999999999591313, 1999999999814655,
    1999999999919039, 1999999999965787, 1999999999985975, 1999999999994414, 1999999999997834,
    1999999999999186, 1999999999999705, 1999999999999897, 1999999999999968, 1999999999999992,
    1999999999999999]
private def pvn_m32_r384_6_1 : List ℕ :=
  pCat pvn_m32_r384_6_1_p0
      pvn_m32_r384_6_1_p1
private def pvn_m32_r384_6_2_p0 : List ℕ :=
  [1992837174605743, 2004609401794584, 1993104517898574, 2011649867396811, 1986826242254514,
    2021387575732825, 2017520314441618, 2005565543468377, 2025154194270611, 2012623548659130,
    1975619250807232, 1972650723135401, 1989173509166573, 1988341061509981, 1984189983001944,
    1992979783127308, 1992088471190536, 1967168491007843, 1946256575251889, 1958262273747271,
    1989648916172046, 2005109176441794, 1994089922060421, 1977322731395839, 1975750551418045,
    1984212302910557, 1990356874434975, 1974983548455557, 1968296412290716, 1938925305533804,
    1955707655448104, 1927661586665341, 1934769459039630, 1929144580025358, 1909651531103584,
    1926550297044022, 1933977664549388, 1909176109618527, 1879996884508065, 1838766372467738,
    1766202383112420, 1686471048539660, 1636893052758141, 1624070088533844, 1633412892964766,
    1656322431552098, 1694387227624045, 1747860824080001, 1809424091901861, 1868037625144462,
    1915460269317241, 1949090044092193, 1970682669678667, 1983652070519774, 1991143329868902,
    1995366054200380, 1997685905039845, 1998913462770612, 1999530567590880, 1999821699386212,
    1999948579477197, 1999997779527226, 2000012754998284, 2000014098345925]
private def pvn_m32_r384_6_2_p1 : List ℕ :=
  [2000011039485493, 2000007389482305, 2000004458776603, 2000002476568740, 2000001276947645,
    2000000611622495, 2000000270116818, 2000000107696164, 2000000036685110, 2000000008800043,
    1999999999558426, 1999999997513562, 1999999997778922, 1999999998504447, 1999999999118160,
    1999999999521361, 1999999999755247, 1999999999880567, 1999999999943942, 1999999999974557,
    1999999999988795, 1999999999995202, 1999999999998000, 1999999999999188, 1999999999999681,
    1999999999999880, 1999999999999959, 1999999999999988, 1999999999999998]
private def pvn_m32_r384_6_2 : List ℕ :=
  pCat pvn_m32_r384_6_2_p0
      pvn_m32_r384_6_2_p1
private def pvn_m32_r384_6_3_p0 : List ℕ :=
  [1989944374447543, 2007909541331367, 1985352624229492, 2013404756172618, 1997806064656849,
    1986810207435956, 2011069854128756, 2014294309083665, 2000639041060987, 2012782148982267,
    2031545876504316, 2019123949814231, 1991631006381842, 1982781866193981, 1987806269454637,
    1985313263630332, 1979519375914741, 1987189706353965, 2002275544223711, 2000102023232791,
    1976370396158684, 1950236279297864, 1954804531234397, 1968927082118156, 2002825288885295,
    1986645885734064, 1997683714909633, 1971485116429637, 1981401294541691, 1996547158622302,
    1982583173864988, 1985154243421748, 1978217698643086, 1954206943498695, 1952438651668172,
    1957335549333362, 1939938395146486, 1922740767682926, 1925774474832751, 1931972102484150,
    1930016197244667, 1930487598325288, 1933072976201448, 1916638552632056, 1867353260240758,
    1796831337103195, 1728843009259171, 1678703174328119, 1648647535857032, 1636227924775213,
    1641269880036976, 1665159420040883, 1706614886858928, 1759785090722480, 1816142499923237,
    1867893035990462, 1910295636323930, 1942000141421598, 1964036920067860, 1978497184119080,
    1987563450982063, 1993038710568432, 1996236367899815, 1998043223158772]
private def pvn_m32_r384_6_3_p1 : List ℕ :=
  [1999029016220814, 1999546211236796, 1999805411874106, 1999928044496230, 1999981542972676,
    2000001910896711, 2000007564673713, 2000007453254889, 2000005627823185, 2000003721894345,
    2000002251395145, 2000001268445467, 2000000670636825, 2000000333122237, 2000000154731302,
    2000000066327048, 2000000025443526, 2000000008039886, 2000000001439483, 1999999999401661,
    1999999999071981, 1999999999255657, 1999999999511908, 1999999999712358, 1999999999841995,
    1999999999917620, 1999999999958807, 1999999999980115, 1999999999990693, 1999999999995764,
    1999999999998122, 1999999999999191, 1999999999999662, 1999999999999865, 1999999999999949,
    1999999999999984, 1999999999999996]
private def pvn_m32_r384_6_3 : List ℕ :=
  pCat pvn_m32_r384_6_3_p0
      pvn_m32_r384_6_3_p1
private def pvn_m32_r384_6_4_p0 : List ℕ :=
  [1986050515076816, 2011638181557551, 1986485020423724, 1997555210551305, 2013179814474337,
    1995676183874391, 1986628554370688, 2004522311028293, 2012794014885262, 2000429859779687,
    1998859847016401, 2018550819255964, 2031349017693480, 2019271424571868, 1999520524264744,
    1992046475213795, 1993117397533689, 1985869638776093, 1979378450032494, 1976022753303432,
    2002311814443446, 1999403184479508, 2009869265405957, 1964601802274741, 1958241558459035,
    1957754965730629, 1964774039139273, 1996732509986646, 1994433155760396, 1979955358183922,
    1986310623850955, 1985010993261118, 1981032267656764, 1993541938993374, 1996713397989787,
    1977940149946468, 1965697466825226, 1969277918051584, 1966076951668874, 1949580739319105,
    1936880251090645, 1934441177856967, 1931979390397297, 1926458876196488, 1928031900224198,
    1940504824604887, 1949949870380742, 1937218309709573, 1896043206334251, 1836364884786370,
    1773865772818049, 1719580256785381, 1677950726840664, 1650713320434939, 1640094188680283,
    1648384079303063, 1675567538228220, 1717924137172142, 1768831013832519, 1820970782420245,
    1868445120284374, 1907835323881830, 1938136913562175, 1960036835398293]
private def pvn_m32_r384_6_4_p1 : List ℕ :=
  [1975063548375116, 1984932206207887, 1991172477583931, 1994986499266777, 1997244207746041,
    1998539025246480, 1999257607438682, 1999642347972160, 1999839983656460, 1999936419154425,
    1999980287450053, 1999998168634786, 2000004030114652, 2000004871108408, 2000003984113354,
    2000002777296056, 2000001756822173, 2000001034035559, 2000000572709143, 2000000299775602,
    2000000148206456, 2000000068807616, 2000000029584752, 2000000011417226, 2000000003638256,
    2000000000657383, 1999999999721012, 1999999999561740, 1999999999642531, 1999999999761157,
    1999999999856352, 1999999999919359, 1999999999956977, 1999999999977961, 1999999999989089,
    1999999999994760, 1999999999997552, 1999999999998887, 1999999999999510, 1999999999999792,
    1999999999999916, 1999999999999968, 1999999999999990, 1999999999999998]
private def pvn_m32_r384_6_4 : List ℕ :=
  pCat pvn_m32_r384_6_4_p0
      pvn_m32_r384_6_4_p1
private def pvn_m32_r384_6_5_p0 : List ℕ :=
  [1981619750845115, 2009482761212390, 1999494067385316, 1985680402721306, 2000039683250951,
    2012463345879942, 1999812806928574, 1986805721791389, 1995863309883645, 2009967062851754,
    2006535495170198, 1994632681952085, 1998082220911772, 2015992661706457, 2029878023363377,
    2020054101257880, 2012022866855902, 1993879242860983, 2008724833505626, 1984273107504816,
    1990117031778789, 1971477365101096, 1978175269993995, 2007969413371853, 2004922481552978,
    2000266573696354, 1985895533668611, 1954427960694718, 1953080167258814, 1975456502418878,
    1982601816871714, 1984254148819054, 1991664118668873, 1987385059215191, 1976321911449877,
    1982033975438155, 1997134080712332, 1996872747166424, 1983643424185244, 1977296601796140,
    1979252129509325, 1975458126135020, 1963000587057877, 1952148225269233, 1947266152305262,
    1941526510100556, 1930907358827910, 1923034819539517, 1927990384916636, 1944488018342697,
    1958529817967307, 1954599290917015, 1926673185155912, 1879843591057828, 1824296080814983,
    1768972231290074, 1719529979245947, 1679812888851215, 1653553959144194, 1644284732399923,
    1653834920721783, 1681002091487433, 1721512821482676, 1769262034516917]
private def pvn_m32_r384_6_5_p1 : List ℕ :=
  [1818048424968569, 1862973735996033, 1901087107083007, 1931314790655392, 1953967946493071,
    1970142492419924, 1981216563312707, 1988522792421711, 1993184591901610, 1996068155924639,
    1997799475366738, 1998808675359430, 1999379231405408, 1999691320267765, 1999855743512499,
    1999938531312201, 1999977820676922, 1999994929157667, 2000001349157821, 2000003017488117,
    2000002839093146, 2000002131482830, 2000001423261185, 2000000878175331, 2000000509242999,
    2000000279710145, 2000000145906735, 2000000072177551, 2000000033653549, 2000000014588383,
    2000000005705327, 2000000001861892, 2000000000363994, 1999999999878501, 1999999999785896,
    1999999999819562, 1999999999876568, 1999999999924161, 1999999999956525, 1999999999976312,
    1999999999987602, 1999999999993728, 1999999999996923, 1999999999998532, 1999999999999321,
    1999999999999696, 1999999999999869, 1999999999999948, 1999999999999982, 1999999999999995]
private def pvn_m32_r384_6_5 : List ℕ :=
  pCat pvn_m32_r384_6_5_p0
      pvn_m32_r384_6_5_p1
private def pvn_m32_r384_6_6_p0 : List ℕ :=
  [1979799164627685, 1998783040723089, 2009177130704076, 1996215796085558, 1986118554578556,
    1996825449123956, 2010820631911484, 2006623517505250, 1991892932683537, 1988510826691787,
    2001121379528918, 2008705262392633, 2005986690986033, 1988910539231977, 2000745608841238,
    2000851178796662, 2033397629334999, 2016608870146307, 2017594023884924, 2011169614959254,
    1998517372657157, 2009915606504246, 1996067090257990, 1973655644457686, 1978167228727297,
    1984035353005408, 1992317309549999, 2012954018479015, 2012458879240255, 1983691094347361,
    1964353500067271, 1964615157596271, 1966061995204116, 1970264891696241, 1984664241796756,
    1993680908677452, 1985178979452924, 1975289311366664, 1981142776814325, 1993698647931529,
    1995805467662723, 1988612323145648, 1984582963021422, 1985995788305739, 1984227142805556,
    1975456339182342, 1965848865382920, 1960842380532107, 1956885812323151, 1947219588874220,
    1932556937725491, 1922397155139078, 1925700299223123, 1941621847166871, 1959284414269868,
    1965449965883244, 1952456344497115, 1920683634382603, 1875766023122123, 1824464144264987,
    1772446424586215, 1724393686297813, 1684866578124990, 1658413582989161]
private def pvn_m32_r384_6_6_p1 : List ℕ :=
  [1648622227369506, 1656860379421189, 1681625383262885, 1718902089366713, 1763297074604236,
    1809387877435702, 1852777989967618, 1890614013759716, 1921592229694337, 1945636839063279,
    1963457789018256, 1976141139995059, 1984847421122624, 1990630963102799, 1994358322365885,
    1996692782500577, 1998114918388505, 1998957681466711, 1999443109741157, 1999714350753049,
    1999860864597367, 1999936923316276, 1999974494881609, 1999991842651925, 1999999059785913,
    2000001516166682, 2000001939618473, 2000001634201180, 2000001170406141, 2000000762082768,
    2000000463476700, 2000000266638572, 2000000145965567, 2000000076165650, 2000000037815281,
    2000000017756486, 2000000007784015, 2000000003098835, 2000000001045290, 2000000000228406,
    1999999999953256, 1999999999893300, 1999999999905640, 1999999999933628, 1999999999958302,
    1999999999975609, 1999999999986454, 1999999999992775, 1999999999996277, 1999999999998142,
    1999999999999099, 1999999999999576, 1999999999999808, 1999999999999919, 1999999999999968,
    1999999999999990, 1999999999999998]
private def pvn_m32_r384_6_6 : List ℕ :=
  pCat pvn_m32_r384_6_6_p0
      pvn_m32_r384_6_6_p1
private def pvn_m32_r384_6_7_p0 : List ℕ :=
  [1982677417426990, 1987310721498531, 2002748726835749, 2008436746748181, 1998033217282416,
    1987064868709383, 1991223884946790, 2004707959221212, 2011772751109320, 2000454789171023,
    1993660323636502, 1984549480217846, 2009028859914188, 1999603974591623, 2012899551621256,
    1990284820307189, 1988022210179291, 2007338204403387, 2008784952318082, 2022506211000446,
    2025593537263091, 2007181718678133, 2008683833020058, 2017317302859705, 2005570222288379,
    1993548471907133, 1987931639604331, 1975118674283913, 1971925912619875, 1993818032535161,
    2014498865262364, 2010076734893892, 1994038255803879, 1982556265736422, 1971477672219727,
    1960900009960240, 1963749655429359, 1980000644074245, 1990655403436847, 1985448471809233,
    1976687088272890, 1978679172660353, 1988139192829484, 1992914461699005, 1990342580513444,
    1987826321042451, 1989467426861966, 1990558815307365, 1985811379806200, 1977321738715022,
    1971333126036307, 1969411906161324, 1966048243846849, 1955376850692295, 1938770891071775,
    1924957485103318, 1922883858047992, 1934374563452142, 1952647379910872, 1966814764659154,
    1967966785776533, 1952553775603489, 1921997123594516, 1880310838193232]
private def pvn_m32_r384_6_7_p1 : List ℕ :=
  [1832063053467936, 1781718315495590, 1733902608604410, 1693573711132708, 1665503379538065,
    1653228474872573, 1658071764998047, 1678769831200398, 1711867669273860, 1752660193120548,
    1796282048136527, 1838591216885208, 1876662414698599, 1908885862212348, 1934782173600632,
    1954678943300959, 1969371440587307, 1979842041286646, 1987066797377899, 1991905697601820,
    1995057504584080, 1997056537451672, 1998291998723727, 1999036077123688, 1999472506898152,
    1999721431164403, 1999859129507615, 1999932686017876, 1999970364411794, 1999988652573994,
    1999996879930202, 2000000149083753, 2000001142041753, 2000001200488006, 2000000952293059,
    2000000662900589, 2000000425002408, 2000000256284693, 2000000146855208, 2000000080346709,
    2000000042023689, 2000000020972397, 2000000009930160, 2000000004408101, 2000000001789697,
    2000000000626113, 2000000000153191, 1999999999987421, 1999999999946554, 1999999999949514,
    1999999999963327, 1999999999976428, 1999999999985945, 1999999999992057, 1999999999995695,
    1999999999997746, 1999999999998858, 1999999999999440, 1999999999999736, 1999999999999880,
    1999999999999950, 1999999999999982, 1999999999999995]
private def pvn_m32_r384_6_7 : List ℕ :=
  pCat pvn_m32_r384_6_7_p0
      pvn_m32_r384_6_7_p1
private def pvn_m32_r384_6_8_p0 : List ℕ :=
  [1987053203349024, 1983796774019517, 1992687714952532, 2005108170819745, 2007845994713248,
    1997921381975967, 1988516950994311, 1987878187137876, 2004131727652629, 2005071940540252,
    2014641520760313, 1986286451092483, 1997110019464788, 1990065374595385, 2002154667344702,
    2015719036000768, 1996246330572926, 1992337298761736, 1996248800075621, 1993984185706711,
    2011175407246974, 2026232595195685, 2015654037388434, 2008969317871526, 2016417877926107,
    2015109595383676, 2007551029784520, 2005800533395674, 1996523463036232, 1975586867586135,
    1968209459730174, 1985453468269609, 2005042864036319, 2009206056117659, 2004495999195345,
    1997790630276074, 1984399400409639, 1966673867630969, 1959817755838515, 1970294895268047,
    1984444563486496, 1986906379441302, 1979946021649749, 1976689213914901, 1982038353660305,
    1988775258553222, 1990097080850293, 1988215418448341, 1988821248862744, 1991994623051957,
    1992400192780236, 1987042829539534, 1979445378152375, 1975178021587887, 1974815049115821,
    1972789170528255, 1963249263381851, 1946550978775923, 1930019018894877, 1922628448133505,
    1928509281983181, 1944292970525938, 1961454068389837, 1971048934399881]
private def pvn_m32_r384_6_8_p1 : List ℕ :=
  [1967406062727147, 1949094595350271, 1917774938905269, 1876573024493989, 1829166692889359,
    1779699563480619, 1732913676567922, 1693888095683674, 1667238443173697, 1656101688802187,
    1661392886180304, 1681660243476240, 1713560140724270, 1752723205639954, 1794690102789766,
    1835652788401378, 1872870733798419, 1904764154644162, 1930770874623177, 1951080623235216,
    1966345403016842, 1977429846781112, 1985229898370893, 1990561818768809, 1994108921295425,
    1996408505182052, 1997862556224744, 1998759607509558, 1999299463304715, 1999616128735114,
    1999796879041906, 1999897002596060, 1999950594904088, 1999978123540109, 1999991537601123,
    1999997607667543, 2000000044219532, 2000000802913479, 2000000865857408, 2000000695307412,
    2000000488588610, 2000000316038011, 2000000192341158, 2000000111330486, 2000000061607730,
    2000000032651266, 2000000016554904, 2000000007995033, 2000000003643742, 2000000001538055,
    2000000000576717, 2000000000170177, 2000000000017301, 1999999999971849, 1999999999966884,
    1999999999974025, 1999999999982563, 1999999999989281, 1999999999993792, 1999999999996564,
    1999999999998170, 1999999999999058, 1999999999999531, 1999999999999775]
private def pvn_m32_r384_6_8_p2 : List ℕ :=
  [1999999999999897, 1999999999999958, 1999999999999985, 1999999999999996]
private def pvn_m32_r384_6_8 : List ℕ :=
  pCat pvn_m32_r384_6_8_p0
    (pCat pvn_m32_r384_6_8_p1
      pvn_m32_r384_6_8_p2)
private def pvn_m32_r384_6_9_p0 : List ℕ :=
  [1991691429288792, 1985293352335048, 1986047174273233, 1994923057097104, 2005821147073021,
    2006754077441696, 2002306772121225, 1985314313057854, 1994604048338226, 1987115140478669,
    2015606835269134, 2005152697477032, 2001080060148501, 1998830687293171, 1983211060254001,
    1997174342537835, 2011432434135084, 2002716772304997, 2000692881903383, 1998277353046597,
    1986510897405819, 1993087228838233, 2014226221024212, 2018568321904175, 2011762675518018,
    2014106918205432, 2017096670494212, 2012050514998515, 2011320732841693, 2015574119264783,
    2006331275958516, 1983121968010068, 1969771850799608, 1977701576017305, 1992846447045691,
    2001880286785574, 2006571025660515, 2008472495780234, 2000432137352866, 1981230037082669,
    1964571967850565, 1963904284147774, 1975414960912159, 1984039793125787, 1982566180113342,
    1977665389009322, 1978089449402066, 1983551399674285, 1987631394018278, 1987553047283530,
    1986926975769952, 1989477830283679, 1993439948339329, 1993758215596626, 1988557850096407,
    1981633690149506, 1978200353451400, 1978950237719465, 1978860665934842, 1971834140470423,
    1956561106026473, 1938349274128870, 1925687331601378, 1924644795848609]
private def pvn_m32_r384_6_9_p1 : List ℕ :=
  [1935286381822836, 1952045610493696, 1966961884307715, 1973217974511928, 1967049925215392,
    1947735362034665, 1916587057925922, 1876042746996835, 1829334508785754, 1780529150557198,
    1734447963930172, 1696152072635132, 1670056944478757, 1659016510343830, 1663749600483608,
    1682809978475913, 1713064688039384, 1750472222009022, 1790899559152501, 1830770218950363,
    1867440432699001, 1899302903669948, 1925684674428813, 1946629938869547, 1962650093249120,
    1974497974012160, 1982995127524438, 1988918545115087, 1992939490328761, 1995601069526606,
    1997320655202300, 1998405629641881, 1999074243561908, 1999476524236832, 1999712608366959,
    1999847521325350, 1999922392650615, 1999962574073459, 1999983289640161, 1999993436626692,
    1999998065072404, 1999999949355611, 2000000556747779, 2000000627671678, 2000000513172316,
    2000000364942040, 2000000238457030, 2000000146544665, 2000000085684306, 2000000047940963,
    2000000025726642, 2000000013235880, 2000000006507339, 2000000003035222, 2000000001323984,
    2000000000524071, 2000000000174348, 2000000000035480, 1999999999988975, 1999999999979247,
    1999999999981899, 1999999999987202, 1999999999991864, 1999999999995169]
private def pvn_m32_r384_6_9_p2 : List ℕ :=
  [1999999999997273, 1999999999998522, 1999999999999225, 1999999999999610, 1999999999999813,
    1999999999999915, 1999999999999963, 1999999999999987, 1999999999999998]
private def pvn_m32_r384_6_9 : List ℕ :=
  pCat pvn_m32_r384_6_9_p0
    (pCat pvn_m32_r384_6_9_p1
      pvn_m32_r384_6_9_p2)
private def phb_m32_r384_7_p0 : List ℕ :=
  [96419897806080, 136003227349673, 166134348517704, 191333234708940, 213355597483415,
    233104296110098, 251117085548257, 267745256975597, 283233449805360, 297760242995981,
    311460794614179, 324440376948188, 336782920342481, 348556647605098, 359817926106792,
    370613982192120, 380984863771323, 390964891154022, 400583750494945, 409867332007613,
    418838382269379, 427517018717612, 435921140377661, 444066759344304, 451968270966000,
    459638676062095, 467089765204227, 474332272702263, 481376006178956, 488229956311462,
    494902390335498, 501400932161199, 507732631376502, 513904022969834, 519921179256974,
    525789755223780, 531515028279693, 537101933243805, 542555093245944, 547878847112605,
    553077273715731, 558154213687315, 563113288840976, 567957919590562, 572691340613378,
    577316614970200, 581836646864542, 586254193198602, 590571874062240, 594792182273377,
    598917492072981, 602950067064764, 606892067478553, 610745556826723, 614512508014770,
    618194808959986, 621794267765975, 625312617495345, 628751520578254, 632112572890311,
    635397307529812, 638607198321056, 641743663067767, 644808066578160]
private def phb_m32_r384_7_p1 : List ℕ :=
  [647801723481019, 650725900850276, 653581820653823, 656370662040811, 659093563480337,
    661751624763204, 664345908877380, 666877443766807, 669347223982353, 671756212232929,
    674105340844090, 676395513130810, 678627604690564, 680802464622327, 682920916676642,
    684983760341491, 686991771868320, 688945705242222, 690846293099979, 692694247599357,
    694490261242805, 696235007658469, 697929142341207, 699573303356093, 701168112006733,
    702714173470516, 704212077402802, 705662398511905, 707065697106562, 708422519617522,
    709733399094724, 710998855681462, 712219397066845, 713395518917740, 714527705291353,
    715616429029500, 716662152135548, 717665326134975, 718626392420397, 719545782581888,
    720423918723364, 721261213765736, 722058071737507, 722814888053469, 723532049782064,
    724209935901994, 724848917548602, 725449358250520, 726011614157052, 726536034256746,
    727022960587551, 727472728438985, 727885666546652, 728262097279492, 728602336820069,
    728906695338240, 729175477158480, 729408980921155, 729607499738020, 729771321342175,
    729900728232737, 729995997814452, 730057402532461, 730085210002425]
private def phb_m32_r384_7_p2 : List ℕ :=
  [730079683136209, 730041080263307, 729969655248186, 729865657603722, 729729332600873,
    729560921374759, 729360661027282, 729128784726432, 728865521802396, 728571097840621,
    728245734771921, 727889650959764, 727503061284838, 727086177226998, 726639206944706,
    726162355352040, 725655824193375, 725119812115825, 724554514739519, 723960124725789,
    723336831843367, 722684823032628, 722004282467987, 721295391618481, 720558329306632,
    719793271765622, 719000392694861, 718179863313995, 717331852415406, 716456526415258,
    715554049403140, 714624583190355, 713668287356887, 712685319297115, 711675834264286,
    710639985413817, 709577923845439, 708489798644238, 707375756920625, 706235943849255,
    705070502706960, 703879574909687, 702663300048511, 701421815924725, 700155258584045,
    698863762349964, 697547459856269, 696206482078754, 694840958366155, 693451016470325,
    692036782575673, 690598381327897, 689135935862017, 687649567829744, 686139397426199,
    684605543415990, 683048123158688, 681467252633701, 679863046464567, 678235617942691,
    676585079050535, 674911540484270, 673215111675923, 671495900815016]
private def phb_m32_r384_7_p3 : List ℕ :=
  [669754014869720, 667989559607535, 666202639615511, 664393358320020, 662561818006087,
    660708119836310, 658832363869356, 656934649078058, 655015073367125, 653073733590470,
    651110725568168, 649126144103052, 647120082996958, 645092635066636, 643043892159313,
    640973945167947, 638882884046158, 636770797822846, 634637774616523, 632483901649336,
    630309265260819, 628113950921357, 625898043245387, 623661626004327, 621404782139254,
    619127593773325, 616830142223958, 614512508014770, 612174770887281, 609817009812396,
    607439303001657, 605041727918284, 602624361288000, 600187279109649, 597730556665619,
    595254268532061, 592758488588913, 590243290029744, 587708745371412, 585154926463534,
    582581904497795, 579989750017073, 577378532924404, 574748322491778, 572099187368783,
    569431195591081, 566744414588745, 564038911194432, 561314751651421, 558572001621505,
    555810726192740, 553030989887059, 550232856667755, 547416389946832, 544581652592223,
    541728706934889, 538857614775797, 535968437392766, 533061235547212, 530136069490764,
    527192998971780, 524232083241739, 521253381061539, 518256950707680]
private def phb_m32_r384_7_p4 : List ℕ :=
  [515242849978345, 512211136199388, 509161866230210, 506095096469546, 503010882861157,
    499909280899425, 496790345634862, 493654131679520, 490500693212326, 487330083984321,
    484142357323822, 480937566141493, 477715762935344, 474476999795647, 471221328409772,
    467948800066951, 464659465662964, 461353375704754, 458030580314970, 454691129236435,
    451335071836554, 447962457111645, 444573333691210, 441167749842136, 437745753472835,
    434307392137324, 430852713039233, 427381763035766, 423894588641593, 420391236032686,
    416871751050103, 413336179203708, 409784565675840, 406216955324930, 402633392689061,
    399033921989479, 395418587134050, 391787431720667, 388140499040613, 384477832081869,
    380799473532377, 377105465783255, 373395850931972, 369670670785468, 365929966863240,
    362173780400374, 358402152350545, 354615123388968, 350812733915308, 346995024056555,
    343162033669849, 339313802345282, 335450369408639, 331571773924126, 327678054697040,
    323769250276416, 319845398957630, 315906538784973, 311952707554184, 307983942814956,
    304000281873399, 300001761794481, 295988419404428, 291960291293094]
private def phb_m32_r384_7_p5 : List ℕ :=
  [287917413816305, 283859823098162, 279787555033326, 275700645289260, 271599129308452,
    267483042310606, 263352419294802, 259207295041628, 255047704115290, 250873680865690,
    246685259430478, 242482473737078, 238265357504690, 234033944246262, 229788267270444,
    225528359683511, 221254254391266, 216965984100915, 212663581322922, 208347078372841,
    204016507373123, 199671900254901, 195313288759755, 190940704441453, 186554178667671,
    182153742621695, 177739427304097, 173311263534393, 168869281952684, 164413513021273,
    159943987026261, 155460734079131, 150963784118309, 146453166910701, 141928912053220,
    137391048974292, 132839606935344, 128274615032272, 123696102196895, 119104097198392,
    114498628644720, 109879724984014, 105247414505980, 100601725343257, 95942685472776,
    91270322717099, 86584664745737, 81885739076466, 77173573076613, 72448193964337,
    67709628809895, 62957904536885, 58193047923490, 53415085603693, 48624044068485,
    43819949667063, 39002828608006, 34172706960447, 29329610655225, 24473565486024,
    19604597110511, 14722731051442, 9827992697774, 4920407305754]
private def phb_m32_r384_7 : List ℕ :=
  pCat phb_m32_r384_7_p0
    (pCat phb_m32_r384_7_p1
    (pCat phb_m32_r384_7_p2
    (pCat phb_m32_r384_7_p3
    (pCat phb_m32_r384_7_p4
      phb_m32_r384_7_p5))))
private def pvn_m32_r384_7_0_p0 : List ℕ :=
  [1991691429288792, 1985293352335048, 1986047174273233, 1994923057097104, 2005821147073021,
    2006754077441696, 2002306772121225, 1985314313057854, 1994604048338226, 1987115140478669,
    2015606835269134, 2005152697477032, 2001080060148501, 1998830687293171, 1983211060254001,
    1997174342537835, 2011432434135084, 2002716772304997, 2000692881903383, 1998277353046597,
    1986510897405819, 1993087228838233, 2014226221024212, 2018568321904175, 2011762675518018,
    2014106918205432, 2017096670494212, 2012050514998515, 2011320732841693, 2015574119264783,
    2006331275958516, 1983121968010068, 1969771850799608, 1977701576017305, 1992846447045691,
    2001880286785574, 2006571025660515, 2008472495780234, 2000432137352866, 1981230037082669,
    1964571967850565, 1963904284147774, 1975414960912159, 1984039793125787, 1982566180113342,
    1977665389009322, 1978089449402066, 1983551399674285, 2012368605981722, 1987553047283530,
    1986926975769952, 1989477830283679, 1993439948339329, 1993758215596626, 1988557850096407,
    1981633690149506, 1978200353451400, 1978950237719465, 1978860665934842, 1971834140470423,
    1956561106026473, 1938349274128870, 1925687331601378, 1924644795848609]
private def pvn_m32_r384_7_0_p1 : List ℕ :=
  [1935286381822836, 1952045610493696, 1966961884307715, 1973217974511928, 1967049925215392,
    1947735362034665, 1916587057925922, 1876042746996835, 1829334508785754, 1780529150557198,
    1734447963930172, 1696152072635132, 1670056944478757, 1659016510343830, 1663749600483608,
    1682809978475913, 1713064688039384, 1750472222009022, 1790899559152501, 1830770218950363,
    1867440432699001, 1899302903669948, 1925684674428813, 1946629938869547, 2037349906750880,
    1974497974012160, 1982995127524438, 1988918545115087, 1992939490328761, 1995601069526606,
    1997320655202300, 1998405629641881, 1999074243561908, 1999476524236832, 1999712608366959,
    1999847521325350, 1999922392650615, 1999962574073459, 1999983289640161, 1999993436626692,
    2000001934927596, 1999999949355611, 2000000556747779, 2000000627671678, 2000000513172316,
    2000000364942040, 2000000238457030, 2000000146544665, 1999999914315694, 2000000047940963,
    2000000025726642, 2000000013235880, 2000000006507339, 2000000003035222, 2000000001323984,
    2000000000524071, 2000000000174348, 2000000000035480, 1999999999988975, 1999999999979247,
    1999999999981899, 1999999999987202, 1999999999991864, 1999999999995169]
private def pvn_m32_r384_7_0_p2 : List ℕ :=
  [1999999999997273, 1999999999998522, 1999999999999225, 1999999999999610, 1999999999999813,
    1999999999999915, 1999999999999963, 1999999999999987, 1999999999999998]
private def pvn_m32_r384_7_0 : List ℕ :=
  pCat pvn_m32_r384_7_0_p0
    (pCat pvn_m32_r384_7_0_p1
      pvn_m32_r384_7_0_p2)
private def pvn_m32_r384_7_1_p0 : List ℕ :=
  [1996323685024543, 1990923660264430, 1986615169365467, 1985288033857010, 1994410201471043,
    1997148920471374, 2014738701498826, 1996959856958822, 2005584014300947, 1985422052074155,
    1985218506081313, 2002541246580104, 2000526383558489, 2008188304837958, 2011536145132664,
    1992163980933755, 1986415922224457, 1998282983091728, 2000842217862240, 2002104260669041,
    2009641772441536, 2003628155556066, 1986988971498338, 1986637519212525, 2001376757055107,
    2008992241441397, 2009072713095365, 2013632713403180, 2017582431689241, 2012542193509941,
    2008605923832162, 2016083650672312, 2023269342795643, 2013645056223210, 1992309709592095,
    1977916915271938, 1977287056510641, 1982917276934683, 1989847180023246, 2000028380070546,
    2011424093004054, 2011659061548954, 2000744263671906, 1973237303843907, 1976543362506016,
    1960230803254937, 1982269017904722, 1988127892920449, 1972140411342152, 1969967197073977,
    1983004435885859, 1993802626788306, 1994880541729338, 1990595491705558, 1988165985764307,
    1990506688971368, 1994551884633402, 1995148594469267, 1990541299100195, 1984104663904144,
    1980839691915581, 1982274598241899, 1984636649138353, 1981820102319850]
private def pvn_m32_r384_7_1_p1 : List ℕ :=
  [1970417944502118, 1952684037576964, 1935374406713353, 1925684147878374, 1927268330199654,
    1938693364452730, 1954653571179988, 1968606633400408, 1975111684814360, 1970914896045241,
    1954877143859644, 1927414636661627, 1890135044592653, 1845557714174378, 1797957096717076,
    1750080857982650, 1713105411249635, 1673833270982475, 1679106771059620, 1639115729364862,
    1706311388357638, 1684470297375926, 1724646960899778, 1798276224802274, 1814253193046655,
    1824299721095325, 1871245795993485, 1927710070173307, 1963537057482461, 1977711073491355,
    1981984215266633, 1984541256463389, 1987665810271134, 1990986225970111, 1993858203906894,
    1996018410915771, 1997516100527604, 1998492405710183, 1999109330023036, 1999489019010580,
    1999713425225058, 1999842941553127, 1999917514478901, 1999959775630858, 1999982018756056,
    1999992962977716, 1999997760145337, 1999999594912042, 2000000296821424, 2000000512926564,
    2000000447830357, 2000000283577313, 2000000149989157, 2000000077709016, 2000000045221129,
    2000000029227954, 2000000018959920, 2000000011569752, 2000000006524983, 2000000003405125,
    2000000001648650, 2000000000736912, 2000000000297446, 2000000000101439]
private def pvn_m32_r384_7_1_p2 : List ℕ :=
  [2000000000022258, 1999999999995094, 1999999999988965, 1999999999990090, 1999999999992894,
    1999999999995436, 1999999999997268, 1999999999998450, 1999999999999158, 1999999999999559,
    1999999999999780, 1999999999999896, 1999999999999954, 1999999999999982, 1999999999999995]
private def pvn_m32_r384_7_1 : List ℕ :=
  pCat pvn_m32_r384_7_1_p0
    (pCat pvn_m32_r384_7_1_p1
      pvn_m32_r384_7_1_p2)
private def pvn_m32_r384_7_2_p0 : List ℕ :=
  [1998831712826064, 1995598954362660, 1993490198479723, 1984362350657017, 1992661912270083,
    1980269365187912, 2004320451941331, 1999823643349920, 2004950077757131, 2012393777989767,
    1993255848449653, 1987418520734044, 1994212528325220, 1990729493368767, 1997447957199689,
    2013689411846969, 2010143524432156, 1995426474082478, 1993414046162451, 1995546576423547,
    1992514907456155, 1997649853207644, 2010767110267612, 2010904113201232, 1996101729545609,
    1987560564648576, 1992622647609391, 1998482852666048, 2000374765188084, 2006331318751490,
    2015405162854849, 2016182918127108, 2008473022407634, 2006446470072997, 2016480803835931,
    2025567940910400, 2021883344955455, 2003996641123361, 1994194375887392, 1977761386974084,
    1987193734980788, 1971481700947352, 1991234534790103, 2004967777519274, 2007727248645658,
    2015577574259132, 2002791428846440, 1976296944848946, 1968849840692684, 1979316132866357,
    1984343249951535, 1977413435915161, 1970352792262713, 1972668090959693, 1981981356411636,
    1989994520386688, 1991815749638057, 1989393298166232, 1988017751948206, 1990547602020908,
    1994870606807362, 1996445574705531, 1992996847692224, 1986800725761892]
private def pvn_m32_r384_7_2_p1 : List ℕ :=
  [1982613213503888, 1983322071535288, 1987189264855854, 1988897021031376, 1983418271878409,
    1969629617067451, 1951414154463951, 1935039063782582, 1927257248251185, 1928010192943969,
    1942024120813720, 1949877528080932, 1977762746098904, 1961059462590672, 1996363352405639,
    1940270547747255, 1955833140310481, 1907059355677245, 1848892976368425, 1835225843358831,
    1772887839487440, 1710799649736626, 1702086165055056, 1688052065305690, 1655523723628336,
    1656605800143320, 1697749174678249, 1737522295023877, 1757529635893668, 1776106561089656,
    1811359888382204, 1859944155700971, 1906891563733174, 1941529383621004, 1962525067775870,
    1974011421001479, 1980611358217816, 1985193690550030, 1988915184208113, 1992022831789580,
    1994501129805104, 1996358835436400, 1997673829103370, 1998559622425315, 1999132089063841,
    1999490015454344, 1999708066192397, 1999838013989455, 1999913585371287, 1999956059175212,
    1999978885954981, 1999990569801421, 1999996265489370, 1999998874367702, 1999999937090210,
    2000000264148104, 2000000284605682, 2000000212809229, 2000000138087941, 2000000084825095,
    2000000051639009, 2000000031588158, 2000000019228511, 2000000011439375]
private def pvn_m32_r384_7_2_p2 : List ℕ :=
  [2000000006549910, 2000000003573919, 2000000001846260, 2000000000896923, 2000000000405036,
    2000000000165806, 2000000000057681, 2000000000013317, 1999999999997773, 1999999999994078,
    1999999999994555, 1999999999996051, 1999999999997449, 1999999999998468, 1999999999999129,
    1999999999999529, 1999999999999755, 1999999999999879, 1999999999999945, 1999999999999979,
    1999999999999994, 1999999999999999]
private def pvn_m32_r384_7_2 : List ℕ :=
  pCat pvn_m32_r384_7_2_p0
    (pCat pvn_m32_r384_7_2_p1
      pvn_m32_r384_7_2_p2)
private def pvn_m32_r384_7_3_p0 : List ℕ :=
  [2000178972017142, 1996770396822088, 2001497763621038, 1985836868136558, 1999165060072425,
    1981657513187514, 1985868093302786, 1997265458474781, 1991800825263882, 2001687176875239,
    2013984017764086, 2003976385846577, 1995109601240580, 1996955344958768, 1990752462265177,
    1984434947696340, 1996059477179249, 2010511523051447, 2008729177109339, 2001352233402846,
    2000512358703850, 1997622988302751, 1989267993759013, 1989707253861784, 2003179970148449,
    2012551040613269, 2006659308389805, 1996158401415724, 1993236209287244, 1994308432922694,
    1993334453001725, 1993926430068746, 2004526814357159, 2012228961814034, 2017953340184661,
    2001353959731815, 2010714959017969, 2005318684816690, 2027102292497678, 2026409234948441,
    2011915313330060, 2011022655080045, 1997481201255365, 1981269985944481, 1980143782071882,
    1980188440415184, 1982147953345180, 1999211724008285, 2018282114567599, 2016429117100153,
    1996848744932307, 1981201220395779, 1979681522114729, 1983943073361910, 1983018799334339,
    1976179614281614, 1970683041895040, 1972203702513780, 1979437380887255, 1986526392962035,
    1989112976059375, 1987872549258902, 1986921948806758, 1989257785092504]
private def pvn_m32_r384_7_3_p1 : List ℕ :=
  [1994026309489014, 1996987612127143, 1995948449994113, 1989372394683287, 1986349075609977,
    1979818378025815, 1992811773916405, 1980892771638564, 2007428947153836, 1965843068952441,
    1990303311911309, 1938661636791755, 1938688170185506, 1939741510532613, 1913391906633377,
    1947104338290385, 1960786817945885, 1951518646920093, 1980928669687410, 1990948969617254,
    1960051972886697, 1945949662068624, 1938062970408659, 1891161229928373, 1828350395948029,
    1790225753523591, 1763527764689574, 1720999413321905, 1675169874450035, 1656800682945288,
    1670789385666965, 1696080808425303, 1715549274510702, 1731317289059990, 1754898124835471,
    1791913215207623, 1837642624012595, 1882594194127918, 1919404430714436, 1945646149095901,
    1962740117635362, 1973561055095364, 1980684295972386, 1985758180705000, 1989614793826356,
    1992609127660853, 1994898075294062, 1996588545540049, 1997787694535514, 1998605589166928,
    1999144217345381, 1999488327127646, 1999702279503936, 1999831818405745, 1999908066692239,
    1999951591402394, 1999975626850166, 1999988423281365, 1999994944597110, 1999998079745909,
    1999999463294555, 1999999993874147, 2000000145461809, 2000000151868313]
private def pvn_m32_r384_7_3_p2 : List ℕ :=
  [2000000117004955, 2000000080035698, 2000000051668378, 2000000032286781, 2000000019689616,
    2000000011708100, 2000000006756482, 2000000003762725, 2000000002011121, 2000000001025584,
    2000000000495091, 2000000000223285, 2000000000091633, 2000000000032081, 2000000000007544,
    1999999999998878, 1999999999996775, 1999999999997008, 1999999999997823, 1999999999998592,
    1999999999999153, 1999999999999520, 1999999999999743, 1999999999999870, 1999999999999941,
    1999999999999975, 1999999999999992, 1999999999999999]
private def pvn_m32_r384_7_3 : List ℕ :=
  pCat pvn_m32_r384_7_3_p0
    (pCat pvn_m32_r384_7_3_p1
      pvn_m32_r384_7_3_p2)
private def pvn_m32_r384_7_4_p0 : List ℕ :=
  [2001782415697961, 1994442051355844, 2007753449840190, 1989352224858915, 1998249924265875,
    1997814128259679, 1983103017099328, 1987929639792638, 1993748586033408, 1986996592822203,
    1991984342935101, 2007375651566803, 2008951751355940, 2001813617981809, 2002480932574730,
    2001956438086374, 1990373104861943, 1982856914715953, 1991648218943449, 2003689142500660,
    2005532537018012, 2003765428042565, 2006003071900617, 2004727454005455, 1994366385374840,
    1985919701558830, 1991721385962636, 2003853080790064, 2010502076173683, 2002987737848699,
    2003247366675462, 1993623286102429, 2002104927155472, 1983899479234132, 1993697340242945,
    1998650054797058, 2006148810719283, 2018379906775119, 2005444020467503, 1998442303635382,
    2010643532258118, 2016112958900490, 2018350478183213, 2024941640714578, 2021642018324969,
    2008450956807568, 1999582955332606, 1992940683041346, 1980190097602448, 1970916831045404,
    1979870182756607, 2001831509359426, 2016490336502881, 2012955424930951, 1999090661370704,
    1988689517638421, 1986641155499121, 1987544404649744, 1984869476131136, 1977834019243965,
    1972151496478944, 1970957070840917, 1977785034029310, 1980770786824497]
private def pvn_m32_r384_7_4_p1 : List ℕ :=
  [1990577138563284, 1979135086531063, 1996064663442104, 1971958549520087, 2009467943804698,
    1978566987558913, 2010226494947325, 1991124838318362, 1979744811696028, 1998467154394113,
    1973272380983177, 1988435724251269, 2006501330030547, 1983196713951319, 1986780683465667,
    1985863186078379, 1947126138165832, 1933222747320120, 1943160728831233, 1930773162616101,
    1924625662109228, 1952850076188666, 1975515623423144, 1970370353299532, 1968976651127074,
    1982175815407862, 1977835744330875, 1941058926602260, 1896397007491712, 1864034389212259,
    1832883061065913, 1786100996969157, 1730254615353511, 1688109326190184, 1672778003059253,
    1677786521167595, 1688929546676998, 1699251054095773, 1712232072900641, 1734700909073420,
    1769196768215731, 1811982391344367, 1856026849259263, 1895060136602241, 1925828383358528,
    1948093276442152, 1963405170686932, 1973801041350169, 1981010976869362, 1986206424239427,
    1990072480280605, 1992983513847418, 1995156141032343, 1996741362031251, 1997864717489408,
    1998636631452954, 1999151412968679, 1999485105658052, 1999695605004369, 1999824886788056,
    1999902174957481, 1999947111317060, 1999972474975015, 1999986327300173]
private def pvn_m32_r384_7_4_p2 : List ℕ :=
  [1999993606890793, 1999997255455671, 1999998975480036, 1999999720354527, 2000000002549533,
    2000000083396831, 2000000087376338, 2000000068653158, 2000000047896649, 2000000031298984,
    2000000019583574, 2000000011838251, 2000000006931542, 2000000003928367, 2000000002149698,
    2000000001131736, 2000000000570251, 2000000000272824, 2000000000122247, 2000000000049921,
    2000000000017393, 2000000000004045, 1999999999999352, 1999999999998229, 1999999999998364,
    1999999999998813, 1999999999999235, 1999999999999546, 1999999999999747, 1999999999999868,
    1999999999999937, 1999999999999973, 1999999999999990, 1999999999999998]
private def pvn_m32_r384_7_4 : List ℕ :=
  pCat pvn_m32_r384_7_4_p0
    (pCat pvn_m32_r384_7_4_p1
      pvn_m32_r384_7_4_p2)
private def pvn_m32_r384_7_5_p0 : List ℕ :=
  [2003788185486710, 1991721367821821, 2008680889485315, 1996167905133316, 1993026273107966,
    2002991759970481, 1995021998754466, 1984971313195691, 1990807656976986, 1993052962177674,
    1985224401662580, 1987655672884214, 2001417618398481, 2006822174505112, 2002800695211485,
    2003778902961592, 2007418648172682, 2000442516897137, 1987294179305731, 1984611587353120,
    1993624642394512, 2000679070793987, 2001466547406426, 2003443245903132, 2009350271586540,
    2006546545595235, 1998015308210175, 1983688343311468, 1994270319598554, 1994392435326517,
    2012517169672349, 2000562641265537, 2003737573505978, 2005633208715123, 1994853466495415,
    1995408677028715, 1988695476720871, 1986651974615735, 2005229173859374, 2013848972086750,
    2005393419877577, 2002885348847095, 2005825140070730, 2006219227517023, 2012021830204691,
    2022813387383864, 2025097734932770, 2018067377889404, 2012702350503319, 2008867957969921,
    1996808765779894, 1978352238119505, 1969290252881313, 1979197722183887, 1999362297379560,
    2012530309271575, 2011718362929634, 2001096678890581, 1994585934092797, 1988764498714631,
    1994649852367372, 1981123820676137, 1990594577146429, 1960235358233441]
private def pvn_m32_r384_7_5_p1 : List ℕ :=
  [1988181563679712, 1957638326890540, 1994312240491163, 1978302417817413, 1980775464355374,
    1996129182807078, 1971413589197375, 1994416291585265, 2000483501542701, 1984880894079831,
    2004470871011230, 1996203760886433, 1973394199282318, 1989308518194233, 1994214699238089,
    1981059015186161, 1996060664391976, 2007661851104292, 1982792611127675, 1962395511147540,
    1962479716973420, 1948045816402162, 1922589500934211, 1923779329997648, 1946971441216450,
    1957741086695570, 1955644092303384, 1965845017222434, 1987106255107671, 1991946372518514,
    1969418960396448, 1937014708557629, 1910820921708409, 1884561760340790, 1843491471562438,
    1787543946902276, 1733429439031525, 1697861060127997, 1684011476241142, 1683433425215141,
    1687027372649323, 1692687688597026, 1704499589745037, 1727092030657099, 1761104857528641,
    1802609285524391, 1845496483356317, 1884355712310388, 1916112017851133, 1940126657248257,
    1957378099717639, 1969479852740713, 1977985734188067, 1984079732953192, 1988544771656241,
    1991860419834790, 1994320824865756, 1996122592946853, 1997414067030791, 1998316428252726,
    1998930162911734, 1999336504795907, 1999598519866726, 1999763139110908]
private def pvn_m32_r384_7_5_p2 : List ℕ :=
  [1999863929201600, 1999924044963820, 1999958937747272, 1999978606427432, 1999989337782352,
    1999994976516781, 1999997808812838, 1999999153524384, 1999999745570750, 1999999978059619,
    2000000051193017, 2000000061012105, 2000000050226108, 2000000035920410, 2000000023792519,
    2000000014977467, 2000000009064256, 2000000005298928, 2000000002995786, 2000000001636357,
    2000000000861331, 2000000000435020, 2000000000209327, 2000000000094807, 2000000000039483,
    2000000000014336, 2000000000003813, 1999999999999965, 1999999999998922, 1999999999998909,
    1999999999999184, 1999999999999467, 1999999999999681, 1999999999999825, 1999999999999909,
    1999999999999958, 1999999999999984, 1999999999999995]
private def pvn_m32_r384_7_5 : List ℕ :=
  pCat pvn_m32_r384_7_5_p0
    (pCat pvn_m32_r384_7_5_p1
      pvn_m32_r384_7_5_p2)
private def pvn_m32_r384_7_6_p0 : List ℕ :=
  [2006447306443992, 1990290188535606, 2004762879442088, 2004216290878843, 1992652146789164,
    1997670373274735, 2003936067812561, 1994664071509549, 1987291332216583, 1992462182497208,
    1994049891714893, 1985870420724224, 1984074303381701, 1994606925582924, 2002909931478231,
    2001778027040293, 2001729739429800, 2007830136382069, 2009167692169469, 1998768614567630,
    1987699024115490, 1986658020945604, 1994413655705658, 1995543772061347, 2000394415743877,
    1998451187208596, 2015466829960861, 2004270247470016, 2004906474631711, 1987224932384292,
    1986794753882095, 2000697247300833, 1998437641193902, 2003621551752893, 2007049479143907,
    2001238289340460, 2004397947074676, 2002076753773974, 1986442247445944, 1984013434960612,
    1997836878826558, 2005718732445385, 2005584884263598, 2006534088531614, 2005313134444462,
    2001078288673004, 2003767142451264, 2014672325961130, 2021978015516737, 2020521846722904,
    2018362823449257, 2019432220524568, 2016311907697887, 1999971781974795, 1981054676756553,
    1967951646873219, 1981117237744631, 1989042562018882, 2016860875179979, 1997446203268698,
    2018939137881017, 1980652301586591, 2009382392446250, 1985368036293566]
private def pvn_m32_r384_7_6_p1 : List ℕ :=
  [1991056637134126, 1993539862986600, 1963702887207554, 1982575084250348, 1973540581278997,
    1968520990099492, 1994110434159964, 1979946203792191, 1974954791599405, 1994052963386005,
    1982826713629916, 1982001055837101, 2006118414887263, 2000025186495601, 1983801573310972,
    1993444159577472, 1993179677017487, 1975695624136227, 1982748762501337, 2004876364712577,
    2002027956791557, 1986260446061586, 1985511231488688, 1982750973054167, 1956919224611804,
    1930145761151403, 1929110509175659, 1941587911785830, 1943988218610652, 1941588526501171,
    1954040752257000, 1978998742884026, 1993576506186240, 1985394274849954, 1964868129155342,
    1946264821375039, 1928276032720961, 1898200577221029, 1849922962764039, 1792559050710985,
    1742432151257500, 1709851569675876, 1693936259456739, 1687583958605032, 1685424640337131,
    1687594291580208, 1697889691820919, 1719530020081032, 1752266528416807, 1792307010290282,
    1834209515769036, 1873073006046638, 1905854207658403, 1931561399863937, 1950705251778484,
    1964535294386909, 1974425923008797, 1981538007212707, 1986717216881252, 1990529221600652,
    1993342087351681, 1995402998528125, 1996890311554956, 1997941958934026]
private def pvn_m32_r384_7_6_p2 : List ℕ :=
  [1998668400186680, 1999158007477023, 1999479868598442, 1999686258158899, 1999815362688941,
    1999894133161784, 1999940981384158, 1999968107860223, 1999983368513728, 1999991684302271,
    1999996054394612, 1999998255374775, 1999999307658662, 1999999777512046, 1999999967115962,
    2000000030604955, 2000000042512476, 2000000036568057, 2000000026708673, 2000000017886953,
    2000000011317565, 2000000006858742, 2000000004006500, 2000000002261401, 2000000001233403,
    2000000000648907, 2000000000328128, 2000000000158478, 2000000000072319, 2000000000030552,
    2000000000011426, 2000000000003314, 2000000000000262, 1999999999999365, 1999999999999288,
    1999999999999449, 1999999999999636, 1999999999999784, 1999999999999883, 1999999999999942,
    1999999999999974, 1999999999999991, 1999999999999998]
private def pvn_m32_r384_7_6 : List ℕ :=
  pCat pvn_m32_r384_7_6_p0
    (pCat pvn_m32_r384_7_6_p1
      pvn_m32_r384_7_6_p2)
private def pvn_m32_r384_7_7_p0 : List ℕ :=
  [2009097620956283, 1991991023463985, 1997831307845790, 2007322490171928, 1999728633202374,
    1992968747907631, 1999968629031181, 2004291828731734, 1995934516015092, 1989244344308784,
    1993256677592340, 1995969164527588, 1988898527778767, 1982885095161897, 1988283284060154,
    1997589765272226, 1999873944010062, 1998307156117117, 2003148870643510, 2009725696316614,
    2010816798034180, 1996785489565687, 1993113945386054, 1984441460412558, 1998837212055244,
    1988689961268295, 1997353396864161, 2000057263278406, 2005474950416292, 2016778832344190,
    2002674377156211, 1991587840724451, 1993543951422264, 1991113744635086, 1996034631547136,
    2004347866855836, 2001003991581880, 2001096672429654, 2010201379490636, 2007353299463860,
    1992249228271627, 1985878659173142, 1991099675054033, 1996647774404763, 2001319406595758,
    2006969194247246, 2007666890907697, 2001362517128862, 1998711942384139, 2004747689170014,
    2015443862712154, 2015739015214646, 2019845271580866, 2014677305833186, 2032737820885837,
    2011163817653791, 2020060218146212, 1968910697355087, 1987535783815121, 1964860744268027,
    1993339774148633, 2007829246880788, 1995639998721916, 2016476715827819]
private def pvn_m32_r384_7_7_p1 : List ℕ :=
  [1994280775921637, 1993377418341095, 2008605372387313, 1985766082915984, 1988937210273160,
    1991014138342654, 1965419352425411, 1973344378241842, 1986345077802064, 1972274437594319,
    1978922480261532, 1992625494453679, 1977497732914131, 1973923058230723, 1995129007061039,
    1997576095187577, 1987435588509617, 1996727809653397, 2003320779576231, 1985299101684579,
    1973797887988174, 1988072860563219, 1999723955970730, 1993275500966953, 1990917086179979,
    2000583240987461, 1997782108333447, 1971744081446174, 1945830515984659, 1939736609081386,
    1942829845320963, 1938179921876344, 1931260678529662, 1939247133832984, 1963021910422450,
    1984415821068559, 1988704869631652, 1979336306934012, 1968406908371932, 1959155753171967,
    1942351072346561, 1907993086956757, 1857044391785028, 1801400313111354, 1754437158713975,
    1722381770625103, 1703203471765889, 1691657285536969, 1684799509323903, 1683827571926744,
    1692131001080707, 1712081523907858, 1743044115089425, 1781470119580891, 1822418291913052,
    1861313047531377, 1895076738758492, 1922401557608410, 1943393396667310, 1958971381145641,
    1970324386597406, 1978562164348215, 1984564344804213, 1988964636507388]
private def pvn_m32_r384_7_7_p2 : List ℕ :=
  [1992199015340695, 1994567274698205, 1996283075772364, 1997506387885515, 1998361517693336,
    1998946317794042, 1999337149275401, 1999592290931224, 1999754960217390, 1999856230861801,
    1999917768820330, 1999954239665002, 1999975293419193, 1999987108993458, 1999993537900173,
    1999996916404397, 1999998621861192, 1999999441867103, 1999999811994056, 1999999964367094,
    2000000017617685, 2000000029488499, 2000000026446253, 2000000019669039, 2000000013291010,
    2000000008443332, 2000000005121975, 2000000002989672, 2000000001684781, 2000000000917381,
    2000000000482119, 2000000000243802, 2000000000117977, 2000000000054097, 2000000000023078,
    2000000000008812, 2000000000002705, 2000000000000366, 1999999999999642, 1999999999999544,
    1999999999999638, 1999999999999761, 1999999999999859, 1999999999999923, 1999999999999964,
    1999999999999986, 1999999999999996]
private def pvn_m32_r384_7_7 : List ℕ :=
  pCat pvn_m32_r384_7_7_p0
    (pCat pvn_m32_r384_7_7_p1
      pvn_m32_r384_7_7_p2)
private def pvn_m32_r384_7_8_p0 : List ℕ :=
  [2010756107089680, 1996975540412007, 1992710735793957, 2002757950715294, 2006351126912663,
    1997834962102477, 1993668396381352, 2000472531727277, 2004731923804415, 1998148056572413,
    1991074592536181, 1993202766259540, 1997522592924170, 1993468349843179, 1985248023522006,
    1984046071767340, 1991995007061025, 1996183078497881, 1997995154413947, 1993782291889274,
    2007631013289114, 2005938350228842, 2015579011661355, 1996259141334058, 1994038610058633,
    1993641117889264, 1988941209511616, 1995788131989213, 1990787154138695, 1992104360416601,
    2009261714232310, 2012312220300147, 2005673761700223, 2002323813056790, 1993717744948854,
    1988453463754563, 1996299098145998, 2000718640197732, 1995897119595932, 1998781489912643,
    2009846996815985, 2011271266185120, 2001178426271387, 1992559718653251, 1990363427763185,
    1989676246038226, 1994430287362620, 2000679048233673, 2010683752993424, 2000808307714914,
    2005195030801361, 1989241364730358, 2018613003212086, 1997121467575738, 2027864046933438,
    2000568119505570, 2026942892667925, 2029136065282115, 2018951370841982, 2025538775101971,
    1982534875006534, 1978270253375421, 1982936083157719, 1973707151956072]
private def pvn_m32_r384_7_8_p1 : List ℕ :=
  [2003339092624877, 2007301695623396, 1993258035528708, 2008731557946362, 2002736350430071,
    1989645604631804, 2005134347370073, 1999306616049935, 1976567990804501, 1981555699051708,
    1983502386163880, 1967900591754705, 1974676847843026, 1991041009914766, 1981038165556783,
    1970729686340298, 1983864445795283, 1991010308361482, 1982464912434264, 1987704496709932,
    2005077316149933, 2002714970309140, 1983957876314075, 1979737784823514, 1990479293995329,
    1992279199244547, 1985455014864339, 1990585984115117, 2006185303958263, 2007906300161744,
    1987527927615831, 1964343338519587, 1954774848511116, 1951745340591425, 1941784086264608,
    1928448172908492, 1927597049585050, 1944947414033094, 1968159340253004, 1981470844873359,
    1981803130116276, 1977664757199125, 1975508190479270, 1970933021309707, 1953277127279433,
    1916686552282852, 1865955752838690, 1812855330507857, 1767924506253725, 1735125413448223,
    1712465790409333, 1696336947951642, 1685367445337328, 1681294914859882, 1687183070651529,
    1704921358131097, 1733753375225478, 1770407597144682, 1810339529943039, 1849199264806539,
    1883847533340691, 1912691403047903, 1935474602503612, 1952806712995278]
private def pvn_m32_r384_7_8_p2 : List ℕ :=
  [1965683940138626, 1975141326824486, 1982067241765668, 1987145810026267, 1990873070828069,
    1993601048617228, 1995582174970832, 1997002834032489, 1998004878594315, 1998698193973834,
    1999167972931687, 1999479406868073, 1999681302515288, 1999809250009879, 1999888485957413,
    1999936410509674, 1999964696042455, 1999980966091438, 1999990070605282, 1999995014886609,
    1999997611734801, 1999998924336299, 1999999557908803, 1999999846072179, 1999999966375034,
    2000000009664076, 2000000020354235, 2000000018977655, 2000000014330923, 2000000009750960,
    2000000006211074, 2000000003768529, 2000000002196829, 2000000001235450, 2000000000671213,
    2000000000352073, 2000000000177834, 2000000000086066, 2000000000039553, 2000000000016974,
    2000000000006572, 2000000000002095, 2000000000000361, 1999999999999810, 1999999999999717,
    1999999999999769, 1999999999999846, 1999999999999911, 1999999999999955, 1999999999999981,
    1999999999999994, 1999999999999999]
private def pvn_m32_r384_7_8 : List ℕ :=
  pCat pvn_m32_r384_7_8_p0
    (pCat pvn_m32_r384_7_8_p1
      pvn_m32_r384_7_8_p2)
private def pvn_m32_r384_7_9_p0 : List ℕ :=
  [2010724741540674, 2003201471921890, 1993260521935532, 1995443352958137, 2004493842434556,
    2005468017480372, 1997617801524753, 1993963071432920, 1999737990733055, 2004914612778028,
    2000887790525759, 1993356974826142, 1992795975458368, 1997254198341546, 1998375922942950,
    1989496440556796, 1986389385967957, 1983213719182772, 1997426504089946, 1989973426558353,
    1998680059847042, 1991672173856631, 2002835059919248, 2013960201232405, 2006266559961839,
    2005271777771558, 1997318641763778, 1990244182644533, 1997038460999747, 1993588426882137,
    1985006899448798, 1992344491708470, 2002582697828772, 2006373483439558, 2010907327197059,
    2008856676649940, 1996399363786542, 1990628587577832, 1996620381637249, 1998225036243668,
    1992968466373097, 1993994270869906, 2005158811672843, 2009608712719083, 2009780533327855,
    1998338186984052, 2001540331000104, 1982167533189147, 1998700228299352, 1979934374185482,
    2018138523816792, 1992876601751915, 2012360101461200, 1994318751762810, 1995088722908995,
    2016410428676090, 1997387075629109, 2014685691635746, 2011696265155278, 2008417336808044,
    2038996504272975, 2028422194732859, 2015020169941320, 2011941546885918]
private def pvn_m32_r384_7_9_p1 : List ℕ :=
  [1978668293389387, 1971933406211338, 1991673918316675, 1987015504144914, 1992932614003894,
    2011219205621410, 1999844362469980, 1992038909375578, 2008429909765338, 2005758394079928,
    1989706662249459, 1993729035975198, 1993420628336700, 1973321685580305, 1969293608053050,
    1985016738262186, 1984836735144232, 1972771220152303, 1977431778879178, 1987656067292735,
    1981006701141100, 1974368900767877, 1988506422963109, 2004725126131827, 1999814590558639,
    1986726367912746, 1986925160079143, 1993039050261450, 1988116825059284, 1979384563762313,
    1985668682944637, 2003905317809755, 2011790217181905, 1999692815095812, 1981352507962713,
    1971322950998835, 1966068603628383, 1953907422398474, 1935249486514010, 1924054517740323,
    1930709978471182, 1949949209733843, 1967512518414762, 1975190240181309, 1976504656590508,
    1978852571542855, 1982892345327818, 1980544015352109, 1962259212640294, 1925417891486113,
    1876405855257587, 1825871200811486, 1782176661276896, 1748107407092515, 1722125496331447,
    1701923450546945, 1687183772771797, 1679956907228118, 1683095221001320, 1698240838046523,
    1724664065327233, 1759379511972164, 1798175523748925, 1836874279870370]
private def pvn_m32_r384_7_9_p2 : List ℕ :=
  [1872268189936091, 1902507317882649, 1927005680427039, 1946078253962722, 1960521784046925,
    1971276245303220, 1979215992264124, 1985058202549443, 1989349641151224, 1992492100647617,
    1994778492481346, 1996424947323020, 1997594174916646, 1998410670758445, 1998970209888261,
    1999346004827523, 1999593151970433, 1999752230207123, 1999852398078483, 1999914071995234,
    1999951178818582, 1999972976000407, 1999985461668024, 1999992424238929, 1999996195573885,
    1999998173534375, 1999999173351517, 1999999656883899, 1999999877815963, 1999999970883258,
    2000000005018838, 2000000013996228, 2000000013503626, 2000000010319325, 2000000007053979,
    2000000004498077, 2000000002726569, 2000000001585955, 2000000000889357, 2000000000481687,
    2000000000251910, 2000000000126926, 2000000000061327, 2000000000028177, 2000000000012122,
    2000000000004731, 2000000000001550, 2000000000000309, 1999999999999904, 1999999999999828,
    1999999999999858, 1999999999999907, 1999999999999949, 1999999999999977, 1999999999999992,
    1999999999999998]
private def pvn_m32_r384_7_9 : List ℕ :=
  pCat pvn_m32_r384_7_9_p0
    (pCat pvn_m32_r384_7_9_p1
      pvn_m32_r384_7_9_p2)
private def pwalks_m32_r384 : List RkmSegWalk := [
  ⟨uOfHb phb_m32_r384_0, bDec bZ (zPad bZ 1 pvn_m16_r384_0_0),
    bDec bZ (zPad bZ 33 pvn_m32_r384_0_1)⟩,
  ⟨uOfHb phb_m32_r384_1, bDec bZ (zPad bZ 33 pvn_m32_r384_1_0),
    bDec bZ (zPad bZ 33 pvn_m32_r384_1_1)⟩,
  ⟨uOfHb phb_m32_r384_2, bDec bZ (zPad bZ 33 pvn_m32_r384_2_0),
    bDec bZ (zPad bZ 33 pvn_m32_r384_2_1)⟩,
  ⟨uOfHb phb_m32_r384_3, bDec bZ (zPad bZ 33 pvn_m32_r384_3_0),
    bDec bZ (zPad bZ 33 pvn_m32_r384_3_1)⟩,
  ⟨uOfHb phb_m32_r384_4, bDec bZ (zPad bZ 33 pvn_m32_r384_4_0),
    bDec bZ (zPad bZ 145 pvn_m32_r384_4_2)⟩,
  ⟨uOfHb phb_m32_r384_5, bDec bZ (zPad bZ 145 pvn_m32_r384_5_0),
    bDec bZ (zPad bZ 337 pvn_m32_r384_5_2)⟩,
  ⟨uOfHb phb_m32_r384_6, bDec bZ (zPad bZ 337 pvn_m32_r384_6_0),
    bDec bZ (zPad bZ 385 pvn_m32_r384_6_9)⟩,
  ⟨uOfHb phb_m32_r384_7, bDec bZ (zPad bZ 385 pvn_m32_r384_7_0),
    bDec bZ (zPad bZ 385 pvn_m32_r384_7_9)⟩
  ]
private abbrev pdP_0 : Prop := rkmAllTrueF [
    bSlideChk 9 385 phb_m16_r384_4 209 pvn_m16_r384_4_0 353 pvn_m16_r384_4_1,
    rkmCheckRowFromWalks 16 24 384
      [1, 1, 12, 24, 24, 24, 24, 24]
      [4266356, 11638964, 5255840, 31653, 1079016, 1847727, 2454990, 5310659]
      [2, 6, 24, 1, 9, 15, 20, 42]
      rkmMasksPack_m16_r384 pwalks_m16_r384 rkmRowPack_m16_r384,
    bSlideChk 3 385 phb_m32_r384_4 97 pvn_m32_r384_4_1 145 pvn_m32_r384_4_2
  ] = true
private theorem pdk_0 : pdP_0 := by
  decide +kernel
private abbrev pdP_1 : Prop := rkmAllTrueF [
    bSlideChk 6 385 phb_m16_r384_6 385 pvn_m16_r384_6_0 385 pvn_m16_r384_6_1,
    bSlideChk 4 385 phb_m32_r384_4 33 pvn_m32_r384_4_0 97 pvn_m32_r384_4_1,
    rkmCheckRowFromWalks 32 12 384
      [1, 1, 1, 1, 12, 12, 12, 12]
      [5450300, 2939584, 4197755, 7602497, 853133, 1522017, 4841785, 3891949]
      [5, 3, 4, 7, 7, 12, 38, 31]
      rkmMasksPack_m32_r384 pwalks_m32_r384 rkmRowPack_m32_r384
  ] = true
private theorem pdk_1 : pdP_1 := by
  decide +kernel
private abbrev pdP_2 : Prop := rkmAllTrueF [
    bSlideChk 5 385 phb_m16_r384_6 385 pvn_m16_r384_6_2 385 pvn_m16_r384_6_3,
    bSlideChk 7 33 phb_m32_r384_3 33 pvn_m32_r384_3_0 33 pvn_m32_r384_3_1,
    bSlideChk 4 33 phb_m32_r384_2 33 pvn_m32_r384_2_0 33 pvn_m32_r384_2_1
  ] = true
private theorem pdk_2 : pdP_2 := by
  decide +kernel
private abbrev pdP_3 : Prop := rkmAllTrueF [
    bSlideChk 4 385 phb_m32_r384_7 385 pvn_m32_r384_7_3 385 pvn_m32_r384_7_4,
    bSlideChk 4 193 phb_m16_r384_2 193 pvn_m16_r384_2_3 193 pvn_m16_r384_2_4,
    bSlideChk 6 17 phb_m16_r384_1 17 pvn_m16_r384_1_0 17 pvn_m16_r384_1_1
  ] = true
private theorem pdk_3 : pdP_3 := by
  decide +kernel
private abbrev pdP_4 : Prop := rkmAllTrueF [
    bSlideChk 4 385 phb_m16_r384_7 385 pvn_m16_r384_7_2 385 pvn_m16_r384_7_3,
    bSlideChk 5 193 phb_m16_r384_2 193 pvn_m16_r384_2_2 193 pvn_m16_r384_2_3,
    bSlideChk 3 33 phb_m32_r384_1 33 pvn_m32_r384_1_0 33 pvn_m32_r384_1_1
  ] = true
private theorem pdk_4 : pdP_4 := by
  decide +kernel
private abbrev pdP_5 : Prop := rkmAllTrueF [
    bSlideChk 4 385 phb_m32_r384_7 385 pvn_m32_r384_7_2 385 pvn_m32_r384_7_3,
    bSlideChk 6 193 phb_m16_r384_2 161 pvn_m16_r384_2_1 193 pvn_m16_r384_2_2,
    bSlideChk 5 33 phb_m32_r384_0 1 pvn_m16_r384_0_0 33 pvn_m32_r384_0_1
  ] = true
private theorem pdk_5 : pdP_5 := by
  decide +kernel
private abbrev pdP_6 : Prop := rkmAllTrueF [
    bSlideChk 3 385 phb_m16_r384_7 385 pvn_m16_r384_7_12 385 pvn_m16_r384_7_13,
    bSlideChk 9 193 phb_m16_r384_2 17 pvn_m16_r384_2_0 161 pvn_m16_r384_2_1,
    bSlideChk 1 385 phb_m16_r384_3 193 pvn_m16_r384_3_0 209 pvn_m16_r384_3_1
  ] = true
private theorem pdk_6 : pdP_6 := by
  decide +kernel
private abbrev pdP_7 : Prop := rkmAllTrueF [
    bSlideChk 5 385 phb_m16_r384_6 385 pvn_m16_r384_6_1 385 pvn_m16_r384_6_2,
    bSlideChk 6 385 phb_m32_r384_5 145 pvn_m32_r384_5_0 241 pvn_m32_r384_5_1,
    bSlideChk 2 17 phb_m16_r384_0 1 pvn_m16_r384_0_0 17 pvn_m16_r384_0_1
  ] = true
private theorem pdk_7 : pdP_7 := by
  decide +kernel
private abbrev pdP_8 : Prop := rkmAllTrueF [
    bSlideChk 4 385 phb_m16_r384_7 385 pvn_m16_r384_7_1 385 pvn_m16_r384_7_2,
    bSlideChk 3 385 phb_m32_r384_6 385 pvn_m32_r384_6_7 385 pvn_m32_r384_6_8
  ] = true
private theorem pdk_8 : pdP_8 := by
  decide +kernel
private abbrev pdP_9 : Prop := rkmAllTrueF [
    bSlideChk 3 385 phb_m16_r384_7 385 pvn_m16_r384_7_11 385 pvn_m16_r384_7_12,
    bSlideChk 3 385 phb_m32_r384_6 385 pvn_m32_r384_6_8 385 pvn_m32_r384_6_9
  ] = true
private theorem pdk_9 : pdP_9 := by
  decide +kernel
private abbrev pdP_10 : Prop := rkmAllTrueF [
    bSlideChk 4 385 phb_m32_r384_7 385 pvn_m32_r384_7_1 385 pvn_m32_r384_7_2,
    bSlideChk 6 385 phb_m32_r384_5 241 pvn_m32_r384_5_1 337 pvn_m32_r384_5_2
  ] = true
private theorem pdk_10 : pdP_10 := by
  decide +kernel
private abbrev pdP_11 : Prop := rkmAllTrueF [
    bSlideChk 3 385 phb_m16_r384_7 385 pvn_m16_r384_7_10 385 pvn_m16_r384_7_11,
    bSlideChk 4 385 phb_m32_r384_6 385 pvn_m32_r384_6_3 385 pvn_m32_r384_6_4
  ] = true
private theorem pdk_11 : pdP_11 := by
  decide +kernel
private abbrev pdP_12 : Prop := rkmAllTrueF [
    bSlideChk 4 385 phb_m16_r384_7 385 pvn_m16_r384_7_0 385 pvn_m16_r384_7_1,
    bSlideChk 5 385 phb_m16_r384_5 353 pvn_m16_r384_5_0 385 pvn_m16_r384_5_1
  ] = true
private theorem pdk_12 : pdP_12 := by
  decide +kernel
private abbrev pdP_13 : Prop := rkmAllTrueF [
    bSlideChk 3 385 phb_m16_r384_7 385 pvn_m16_r384_7_9 385 pvn_m16_r384_7_10,
    bSlideChk 5 385 phb_m32_r384_6 385 pvn_m32_r384_6_1 385 pvn_m32_r384_6_2
  ] = true
private theorem pdk_13 : pdP_13 := by
  decide +kernel
private abbrev pdP_14 : Prop := rkmAllTrueF [
    bSlideChk 4 385 phb_m32_r384_7 385 pvn_m32_r384_7_0 385 pvn_m32_r384_7_1,
    bSlideChk 4 385 phb_m32_r384_6 385 pvn_m32_r384_6_4 385 pvn_m32_r384_6_5
  ] = true
private theorem pdk_14 : pdP_14 := by
  decide +kernel
private abbrev pdP_15 : Prop := rkmAllTrueF [
    bSlideChk 3 385 phb_m16_r384_7 385 pvn_m16_r384_7_8 385 pvn_m16_r384_7_9,
    bSlideChk 4 385 phb_m32_r384_6 385 pvn_m32_r384_6_5 385 pvn_m32_r384_6_6
  ] = true
private theorem pdk_15 : pdP_15 := by
  decide +kernel
private abbrev pdP_16 : Prop := rkmAllTrueF [
    bSlideChk 3 385 phb_m32_r384_7 385 pvn_m32_r384_7_8 385 pvn_m32_r384_7_9,
    bSlideChk 5 385 phb_m16_r384_5 385 pvn_m16_r384_5_1 385 pvn_m16_r384_5_2
  ] = true
private theorem pdk_16 : pdP_16 := by
  decide +kernel
private abbrev pdP_17 : Prop := rkmAllTrueF [
    bSlideChk 4 385 phb_m16_r384_6 385 pvn_m16_r384_6_3 385 pvn_m16_r384_6_4,
    bSlideChk 6 385 phb_m32_r384_6 337 pvn_m32_r384_6_0 385 pvn_m32_r384_6_1
  ] = true
private theorem pdk_17 : pdP_17 := by
  decide +kernel
private abbrev pdP_18 : Prop := rkmAllTrueF [
    bSlideChk 3 385 phb_m16_r384_7 385 pvn_m16_r384_7_7 385 pvn_m16_r384_7_8,
    bSlideChk 3 385 phb_m16_r384_7 385 pvn_m16_r384_7_3 385 pvn_m16_r384_7_4
  ] = true
private theorem pdk_18 : pdP_18 := by
  decide +kernel
private abbrev pdP_19 : Prop := rkmAllTrueF [
    bSlideChk 3 385 phb_m32_r384_7 385 pvn_m32_r384_7_7 385 pvn_m32_r384_7_8,
    bSlideChk 5 385 phb_m32_r384_6 385 pvn_m32_r384_6_2 385 pvn_m32_r384_6_3
  ] = true
private theorem pdk_19 : pdP_19 := by
  decide +kernel
private abbrev pdP_20 : Prop := rkmAllTrueF [
    bSlideChk 3 385 phb_m16_r384_7 385 pvn_m16_r384_7_6 385 pvn_m16_r384_7_7,
    bSlideChk 3 385 phb_m32_r384_7 385 pvn_m32_r384_7_4 385 pvn_m32_r384_7_5
  ] = true
private theorem pdk_20 : pdP_20 := by
  decide +kernel
private abbrev pdP_21 : Prop := rkmAllTrueF [
    bSlideChk 3 385 phb_m32_r384_7 385 pvn_m32_r384_7_6 385 pvn_m32_r384_7_7,
    bSlideChk 3 385 phb_m16_r384_7 385 pvn_m16_r384_7_4 385 pvn_m16_r384_7_5
  ] = true
private theorem pdk_21 : pdP_21 := by
  decide +kernel
private abbrev pdP_22 : Prop := rkmAllTrueF [
    bSlideChk 5 385 phb_m16_r384_5 385 pvn_m16_r384_5_2 385 pvn_m16_r384_5_3,
    bSlideChk 4 385 phb_m32_r384_6 385 pvn_m32_r384_6_6 385 pvn_m32_r384_6_7
  ] = true
private theorem pdk_22 : pdP_22 := by
  decide +kernel
private abbrev pdP_23 : Prop := rkmAllTrueF [
    bSlideChk 3 385 phb_m16_r384_7 385 pvn_m16_r384_7_5 385 pvn_m16_r384_7_6,
    bSlideChk 3 385 phb_m32_r384_7 385 pvn_m32_r384_7_5 385 pvn_m32_r384_7_6
  ] = true
private theorem pdk_23 : pdP_23 := by
  decide +kernel
private theorem pdim_m16_r384_l1 :
    Nat.add (highdNatMin (Nat.mul 1 16) 384) 1 = 17 :=
  rfl
private theorem pdim_m16_r384_l12 :
    Nat.add (highdNatMin (Nat.mul 12 16) 384) 1 = 193 :=
  rfl
private theorem pdim_m16_r384_l24 :
    Nat.add (highdNatMin (Nat.mul 24 16) 384) 1 = 385 :=
  rfl
private theorem pdim_m32_r384_l1 :
    Nat.add (highdNatMin (Nat.mul 1 32) 384) 1 = 33 :=
  rfl
private theorem pdim_m32_r384_l12 :
    Nat.add (highdNatMin (Nat.mul 12 32) 384) 1 = 385 :=
  rfl
private theorem pwalk_m16_r384_0 :
    bWalkOk 2 17 phb_m16_r384_0 1 pvn_m16_r384_0_0 17 pvn_m16_r384_0_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl
      pdk_7)))
private theorem pwalk_m16_r384_1 :
    bWalkOk 6 17 phb_m16_r384_1 17 pvn_m16_r384_1_0 17 pvn_m16_r384_1_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl
      pdk_3)))
private theorem pw_m16_r384_2_0 :
    bWalkOk 9 193 phb_m16_r384_2 17 pvn_m16_r384_2_0 161 pvn_m16_r384_2_1 :=
  bWalk1
    (rkmHd
      (rkmTl
      pdk_6))
private theorem pw_m16_r384_2_1 :
    bWalkOk 15 193 phb_m16_r384_2 17 pvn_m16_r384_2_0 193 pvn_m16_r384_2_2 :=
  bChn (rfl : 9 + 6 = 15) pw_m16_r384_2_0
    (rkmHd
      (rkmTl
      pdk_5))
private theorem pw_m16_r384_2_2 :
    bWalkOk 20 193 phb_m16_r384_2 17 pvn_m16_r384_2_0 193 pvn_m16_r384_2_3 :=
  bChn (rfl : 15 + 5 = 20) pw_m16_r384_2_1
    (rkmHd
      (rkmTl
      pdk_4))
private theorem pwalk_m16_r384_2 :
    bWalkOk 24 193 phb_m16_r384_2 17 pvn_m16_r384_2_0 193 pvn_m16_r384_2_4 :=
  bChn (rfl : 20 + 4 = 24) pw_m16_r384_2_2
    (rkmHd
      (rkmTl
      pdk_3))
private theorem pwalk_m16_r384_3 :
    bWalkOk 1 385 phb_m16_r384_3 193 pvn_m16_r384_3_0 209 pvn_m16_r384_3_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl
      pdk_6)))
private theorem pwalk_m16_r384_4 :
    bWalkOk 9 385 phb_m16_r384_4 209 pvn_m16_r384_4_0 353 pvn_m16_r384_4_1 :=
  bWalk1
    (rkmHd
      pdk_0)
private theorem pw_m16_r384_5_0 :
    bWalkOk 5 385 phb_m16_r384_5 353 pvn_m16_r384_5_0 385 pvn_m16_r384_5_1 :=
  bWalk1
    (rkmHd
      (rkmTl
      pdk_12))
private theorem pw_m16_r384_5_1 :
    bWalkOk 10 385 phb_m16_r384_5 353 pvn_m16_r384_5_0 385 pvn_m16_r384_5_2 :=
  bChn (rfl : 5 + 5 = 10) pw_m16_r384_5_0
    (rkmHd
      (rkmTl
      pdk_16))
private theorem pwalk_m16_r384_5 :
    bWalkOk 15 385 phb_m16_r384_5 353 pvn_m16_r384_5_0 385 pvn_m16_r384_5_3 :=
  bChn (rfl : 10 + 5 = 15) pw_m16_r384_5_1
    (rkmHd
      pdk_22)
private theorem pw_m16_r384_6_0 :
    bWalkOk 6 385 phb_m16_r384_6 385 pvn_m16_r384_6_0 385 pvn_m16_r384_6_1 :=
  bWalk1
    (rkmHd
      pdk_1)
private theorem pw_m16_r384_6_1 :
    bWalkOk 11 385 phb_m16_r384_6 385 pvn_m16_r384_6_0 385 pvn_m16_r384_6_2 :=
  bChn (rfl : 6 + 5 = 11) pw_m16_r384_6_0
    (rkmHd
      pdk_7)
private theorem pw_m16_r384_6_2 :
    bWalkOk 16 385 phb_m16_r384_6 385 pvn_m16_r384_6_0 385 pvn_m16_r384_6_3 :=
  bChn (rfl : 11 + 5 = 16) pw_m16_r384_6_1
    (rkmHd
      pdk_2)
private theorem pwalk_m16_r384_6 :
    bWalkOk 20 385 phb_m16_r384_6 385 pvn_m16_r384_6_0 385 pvn_m16_r384_6_4 :=
  bChn (rfl : 16 + 4 = 20) pw_m16_r384_6_2
    (rkmHd
      pdk_17)
private theorem pw_m16_r384_7_0 :
    bWalkOk 4 385 phb_m16_r384_7 385 pvn_m16_r384_7_0 385 pvn_m16_r384_7_1 :=
  bWalk1
    (rkmHd
      pdk_12)
private theorem pw_m16_r384_7_1 :
    bWalkOk 8 385 phb_m16_r384_7 385 pvn_m16_r384_7_0 385 pvn_m16_r384_7_2 :=
  bChn (rfl : 4 + 4 = 8) pw_m16_r384_7_0
    (rkmHd
      pdk_8)
private theorem pw_m16_r384_7_2 :
    bWalkOk 12 385 phb_m16_r384_7 385 pvn_m16_r384_7_0 385 pvn_m16_r384_7_3 :=
  bChn (rfl : 8 + 4 = 12) pw_m16_r384_7_1
    (rkmHd
      pdk_4)
private theorem pw_m16_r384_7_3 :
    bWalkOk 15 385 phb_m16_r384_7 385 pvn_m16_r384_7_0 385 pvn_m16_r384_7_4 :=
  bChn (rfl : 12 + 3 = 15) pw_m16_r384_7_2
    (rkmHd
      (rkmTl
      pdk_18))
private theorem pw_m16_r384_7_4 :
    bWalkOk 18 385 phb_m16_r384_7 385 pvn_m16_r384_7_0 385 pvn_m16_r384_7_5 :=
  bChn (rfl : 15 + 3 = 18) pw_m16_r384_7_3
    (rkmHd
      (rkmTl
      pdk_21))
private theorem pw_m16_r384_7_5 :
    bWalkOk 21 385 phb_m16_r384_7 385 pvn_m16_r384_7_0 385 pvn_m16_r384_7_6 :=
  bChn (rfl : 18 + 3 = 21) pw_m16_r384_7_4
    (rkmHd
      pdk_23)
private theorem pw_m16_r384_7_6 :
    bWalkOk 24 385 phb_m16_r384_7 385 pvn_m16_r384_7_0 385 pvn_m16_r384_7_7 :=
  bChn (rfl : 21 + 3 = 24) pw_m16_r384_7_5
    (rkmHd
      pdk_20)
private theorem pw_m16_r384_7_7 :
    bWalkOk 27 385 phb_m16_r384_7 385 pvn_m16_r384_7_0 385 pvn_m16_r384_7_8 :=
  bChn (rfl : 24 + 3 = 27) pw_m16_r384_7_6
    (rkmHd
      pdk_18)
private theorem pw_m16_r384_7_8 :
    bWalkOk 30 385 phb_m16_r384_7 385 pvn_m16_r384_7_0 385 pvn_m16_r384_7_9 :=
  bChn (rfl : 27 + 3 = 30) pw_m16_r384_7_7
    (rkmHd
      pdk_15)
private theorem pw_m16_r384_7_9 :
    bWalkOk 33 385 phb_m16_r384_7 385 pvn_m16_r384_7_0 385 pvn_m16_r384_7_10 :=
  bChn (rfl : 30 + 3 = 33) pw_m16_r384_7_8
    (rkmHd
      pdk_13)
private theorem pw_m16_r384_7_10 :
    bWalkOk 36 385 phb_m16_r384_7 385 pvn_m16_r384_7_0 385 pvn_m16_r384_7_11 :=
  bChn (rfl : 33 + 3 = 36) pw_m16_r384_7_9
    (rkmHd
      pdk_11)
private theorem pw_m16_r384_7_11 :
    bWalkOk 39 385 phb_m16_r384_7 385 pvn_m16_r384_7_0 385 pvn_m16_r384_7_12 :=
  bChn (rfl : 36 + 3 = 39) pw_m16_r384_7_10
    (rkmHd
      pdk_9)
private theorem pwalk_m16_r384_7 :
    bWalkOk 42 385 phb_m16_r384_7 385 pvn_m16_r384_7_0 385 pvn_m16_r384_7_13 :=
  bChn (rfl : 39 + 3 = 42) pw_m16_r384_7_11
    (rkmHd
      pdk_6)
private theorem pwalks_snd_m16_r384 :
    RkmSegWalksSound 16 384 [1, 1, 12, 24, 24, 24, 24, 24]
      [2, 6, 24, 1, 9, 15, 20, 42] pwalks_m16_r384 := by
  dsimp only [RkmSegWalksSound, pwalks_m16_r384]
  exact ⟨bSeg_mk pdim_m16_r384_l1 pwalk_m16_r384_0,
    ⟨bSeg_mk pdim_m16_r384_l1 pwalk_m16_r384_1,
    ⟨bSeg_mk pdim_m16_r384_l12 pwalk_m16_r384_2,
    ⟨bSeg_mk pdim_m16_r384_l24 pwalk_m16_r384_3,
    ⟨bSeg_mk pdim_m16_r384_l24 pwalk_m16_r384_4,
    ⟨bSeg_mk pdim_m16_r384_l24 pwalk_m16_r384_5,
    ⟨bSeg_mk pdim_m16_r384_l24 pwalk_m16_r384_6,
    ⟨bSeg_mk pdim_m16_r384_l24 pwalk_m16_r384_7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Multi-segment trajectory soundness for `(m = 16, r = 384)`. -/
theorem rkmTrajPack_m16_r384 :
    rkmEvalT16Lo12 16 24 384 [1, 1, 12, 24, 24, 24, 24, 24]
      [4266356, 11638964, 5255840, 31653, 1079016, 1847727, 2454990, 5310659]
      [2, 6, 24, 1, 9, 15, 20, 42]
      rkmMasksPack_m16_r384 = rkmRowPack_m16_r384 :=
  rkmCheckRowFromWalks_sound pwalks_snd_m16_r384
    (rkmHd
      (rkmTl
      pdk_0))

private theorem pwalk_m32_r384_0 :
    bWalkOk 5 33 phb_m32_r384_0 1 pvn_m16_r384_0_0 33 pvn_m32_r384_0_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl
      pdk_5)))
private theorem pwalk_m32_r384_1 :
    bWalkOk 3 33 phb_m32_r384_1 33 pvn_m32_r384_1_0 33 pvn_m32_r384_1_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl
      pdk_4)))
private theorem pwalk_m32_r384_2 :
    bWalkOk 4 33 phb_m32_r384_2 33 pvn_m32_r384_2_0 33 pvn_m32_r384_2_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl
      pdk_2)))
private theorem pwalk_m32_r384_3 :
    bWalkOk 7 33 phb_m32_r384_3 33 pvn_m32_r384_3_0 33 pvn_m32_r384_3_1 :=
  bWalk1
    (rkmHd
      (rkmTl
      pdk_2))
private theorem pw_m32_r384_4_0 :
    bWalkOk 4 385 phb_m32_r384_4 33 pvn_m32_r384_4_0 97 pvn_m32_r384_4_1 :=
  bWalk1
    (rkmHd
      (rkmTl
      pdk_1))
private theorem pwalk_m32_r384_4 :
    bWalkOk 7 385 phb_m32_r384_4 33 pvn_m32_r384_4_0 145 pvn_m32_r384_4_2 :=
  bChn (rfl : 4 + 3 = 7) pw_m32_r384_4_0
    (rkmHd
      (rkmTl (rkmTl
      pdk_0)))
private theorem pw_m32_r384_5_0 :
    bWalkOk 6 385 phb_m32_r384_5 145 pvn_m32_r384_5_0 241 pvn_m32_r384_5_1 :=
  bWalk1
    (rkmHd
      (rkmTl
      pdk_7))
private theorem pwalk_m32_r384_5 :
    bWalkOk 12 385 phb_m32_r384_5 145 pvn_m32_r384_5_0 337 pvn_m32_r384_5_2 :=
  bChn (rfl : 6 + 6 = 12) pw_m32_r384_5_0
    (rkmHd
      (rkmTl
      pdk_10))
private theorem pw_m32_r384_6_0 :
    bWalkOk 6 385 phb_m32_r384_6 337 pvn_m32_r384_6_0 385 pvn_m32_r384_6_1 :=
  bWalk1
    (rkmHd
      (rkmTl
      pdk_17))
private theorem pw_m32_r384_6_1 :
    bWalkOk 11 385 phb_m32_r384_6 337 pvn_m32_r384_6_0 385 pvn_m32_r384_6_2 :=
  bChn (rfl : 6 + 5 = 11) pw_m32_r384_6_0
    (rkmHd
      (rkmTl
      pdk_13))
private theorem pw_m32_r384_6_2 :
    bWalkOk 16 385 phb_m32_r384_6 337 pvn_m32_r384_6_0 385 pvn_m32_r384_6_3 :=
  bChn (rfl : 11 + 5 = 16) pw_m32_r384_6_1
    (rkmHd
      (rkmTl
      pdk_19))
private theorem pw_m32_r384_6_3 :
    bWalkOk 20 385 phb_m32_r384_6 337 pvn_m32_r384_6_0 385 pvn_m32_r384_6_4 :=
  bChn (rfl : 16 + 4 = 20) pw_m32_r384_6_2
    (rkmHd
      (rkmTl
      pdk_11))
private theorem pw_m32_r384_6_4 :
    bWalkOk 24 385 phb_m32_r384_6 337 pvn_m32_r384_6_0 385 pvn_m32_r384_6_5 :=
  bChn (rfl : 20 + 4 = 24) pw_m32_r384_6_3
    (rkmHd
      (rkmTl
      pdk_14))
private theorem pw_m32_r384_6_5 :
    bWalkOk 28 385 phb_m32_r384_6 337 pvn_m32_r384_6_0 385 pvn_m32_r384_6_6 :=
  bChn (rfl : 24 + 4 = 28) pw_m32_r384_6_4
    (rkmHd
      (rkmTl
      pdk_15))
private theorem pw_m32_r384_6_6 :
    bWalkOk 32 385 phb_m32_r384_6 337 pvn_m32_r384_6_0 385 pvn_m32_r384_6_7 :=
  bChn (rfl : 28 + 4 = 32) pw_m32_r384_6_5
    (rkmHd
      (rkmTl
      pdk_22))
private theorem pw_m32_r384_6_7 :
    bWalkOk 35 385 phb_m32_r384_6 337 pvn_m32_r384_6_0 385 pvn_m32_r384_6_8 :=
  bChn (rfl : 32 + 3 = 35) pw_m32_r384_6_6
    (rkmHd
      (rkmTl
      pdk_8))
private theorem pwalk_m32_r384_6 :
    bWalkOk 38 385 phb_m32_r384_6 337 pvn_m32_r384_6_0 385 pvn_m32_r384_6_9 :=
  bChn (rfl : 35 + 3 = 38) pw_m32_r384_6_7
    (rkmHd
      (rkmTl
      pdk_9))
private theorem pw_m32_r384_7_0 :
    bWalkOk 4 385 phb_m32_r384_7 385 pvn_m32_r384_7_0 385 pvn_m32_r384_7_1 :=
  bWalk1
    (rkmHd
      pdk_14)
private theorem pw_m32_r384_7_1 :
    bWalkOk 8 385 phb_m32_r384_7 385 pvn_m32_r384_7_0 385 pvn_m32_r384_7_2 :=
  bChn (rfl : 4 + 4 = 8) pw_m32_r384_7_0
    (rkmHd
      pdk_10)
private theorem pw_m32_r384_7_2 :
    bWalkOk 12 385 phb_m32_r384_7 385 pvn_m32_r384_7_0 385 pvn_m32_r384_7_3 :=
  bChn (rfl : 8 + 4 = 12) pw_m32_r384_7_1
    (rkmHd
      pdk_5)
private theorem pw_m32_r384_7_3 :
    bWalkOk 16 385 phb_m32_r384_7 385 pvn_m32_r384_7_0 385 pvn_m32_r384_7_4 :=
  bChn (rfl : 12 + 4 = 16) pw_m32_r384_7_2
    (rkmHd
      pdk_3)
private theorem pw_m32_r384_7_4 :
    bWalkOk 19 385 phb_m32_r384_7 385 pvn_m32_r384_7_0 385 pvn_m32_r384_7_5 :=
  bChn (rfl : 16 + 3 = 19) pw_m32_r384_7_3
    (rkmHd
      (rkmTl
      pdk_20))
private theorem pw_m32_r384_7_5 :
    bWalkOk 22 385 phb_m32_r384_7 385 pvn_m32_r384_7_0 385 pvn_m32_r384_7_6 :=
  bChn (rfl : 19 + 3 = 22) pw_m32_r384_7_4
    (rkmHd
      (rkmTl
      pdk_23))
private theorem pw_m32_r384_7_6 :
    bWalkOk 25 385 phb_m32_r384_7 385 pvn_m32_r384_7_0 385 pvn_m32_r384_7_7 :=
  bChn (rfl : 22 + 3 = 25) pw_m32_r384_7_5
    (rkmHd
      pdk_21)
private theorem pw_m32_r384_7_7 :
    bWalkOk 28 385 phb_m32_r384_7 385 pvn_m32_r384_7_0 385 pvn_m32_r384_7_8 :=
  bChn (rfl : 25 + 3 = 28) pw_m32_r384_7_6
    (rkmHd
      pdk_19)
private theorem pwalk_m32_r384_7 :
    bWalkOk 31 385 phb_m32_r384_7 385 pvn_m32_r384_7_0 385 pvn_m32_r384_7_9 :=
  bChn (rfl : 28 + 3 = 31) pw_m32_r384_7_7
    (rkmHd
      pdk_16)
private theorem pwalks_snd_m32_r384 :
    RkmSegWalksSound 32 384 [1, 1, 1, 1, 12, 12, 12, 12]
      [5, 3, 4, 7, 7, 12, 38, 31] pwalks_m32_r384 := by
  dsimp only [RkmSegWalksSound, pwalks_m32_r384]
  exact ⟨bSeg_mk pdim_m32_r384_l1 pwalk_m32_r384_0,
    ⟨bSeg_mk pdim_m32_r384_l1 pwalk_m32_r384_1,
    ⟨bSeg_mk pdim_m32_r384_l1 pwalk_m32_r384_2,
    ⟨bSeg_mk pdim_m32_r384_l1 pwalk_m32_r384_3,
    ⟨bSeg_mk pdim_m32_r384_l12 pwalk_m32_r384_4,
    ⟨bSeg_mk pdim_m32_r384_l12 pwalk_m32_r384_5,
    ⟨bSeg_mk pdim_m32_r384_l12 pwalk_m32_r384_6,
    ⟨bSeg_mk pdim_m32_r384_l12 pwalk_m32_r384_7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Multi-segment trajectory soundness for `(m = 32, r = 384)`. -/
theorem rkmTrajPack_m32_r384 :
    rkmEvalT16Lo12 32 12 384 [1, 1, 1, 1, 12, 12, 12, 12]
      [5450300, 2939584, 4197755, 7602497, 853133, 1522017, 4841785, 3891949]
      [5, 3, 4, 7, 7, 12, 38, 31]
      rkmMasksPack_m32_r384 = rkmRowPack_m32_r384 :=
  rkmCheckRowFromWalks_sound pwalks_snd_m32_r384
    (rkmHd
      (rkmTl (rkmTl
      pdk_1)))

/-- Module export witness for `FindAllJohnsonRampKickMuxLowHiT8`. -/
theorem laneWitness_FindAllJohnsonRampKickMuxLowHiT8 : True := trivial

end

end QuantumComputation.Specs.DickeSol
