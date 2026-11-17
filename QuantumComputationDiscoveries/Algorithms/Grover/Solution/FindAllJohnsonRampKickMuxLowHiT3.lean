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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxLowHiT2

/-
# Low-`m` High-`r` Krotov Trajectory Part `3` (`FindAllJohnsonRampKickMuxLowHiT3`)

Certifies multi-segment sawtooth `rkmEvalT16Lo12` trajectories for
`(m, r) ∈ {(8, 192), (8, 384), (8, 512)}`.
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Sign-kick mask segment `0` for `(m = 8, r = 192)`. -/
def rkmMkPack_m8_r192_s0 : List Bool :=
  [false, true, false, true, false, false, false, true]
/-- Sign-kick mask segment `1` for `(m = 8, r = 192)`. -/
def rkmMkPack_m8_r192_s1 : List Bool :=
  [true, true, true, false, false, true, true, true]
/-- Sign-kick mask segment `2` for `(m = 8, r = 192)`. -/
def rkmMkPack_m8_r192_s2 : List Bool := [false, false, false, false, false, true]
/-- Sign-kick mask segment `3` for `(m = 8, r = 192)`. -/
def rkmMkPack_m8_r192_s3 : List Bool := [false, false, false, false, true]
/-- Sign-kick mask segment `4` for `(m = 8, r = 192)`. -/
def rkmMkPack_m8_r192_s4 : List Bool :=
  [false, false, false, false, false, false, false, false, false, false, false, false, true,
    false, false, false, false, false, false, false, false, false, false, false, true, false,
    false, false, true, false, false, false, true, false, false, false, true]
/-- Sign-kick mask segment `5` for `(m = 8, r = 192)`. -/
def rkmMkPack_m8_r192_s5 : List Bool :=
  [true, false, false, false, false, false, false, false, true, false, false, false, true,
    false, false, false, false, false, false, false, false, false, false, false, true, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, true, false, false, false,
    true]
/-- Sign-kick mask segment `6` for `(m = 8, r = 192)`. -/
def rkmMkPack_m8_r192_s6 : List Bool :=
  [true, false, false, false, false, false, false, false, true, false, false, false, false,
    false, false, false, false, false, false, false, true, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, true, false, false, false, true, false, false, false,
    true]
/-- Multi-segment sign-kick masks for `(m = 8, r = 192)`. -/
def rkmMasksPack_m8_r192 : List (List Bool) :=
  [rkmMkPack_m8_r192_s0, rkmMkPack_m8_r192_s1, rkmMkPack_m8_r192_s2, rkmMkPack_m8_r192_s3,
    rkmMkPack_m8_r192_s4, rkmMkPack_m8_r192_s5, rkmMkPack_m8_r192_s6, []]
/-- Hit-row chunk `0` for `(m = 8, r = 192)`. -/
def rkmRowPack_m8_r192_p0 : List ℕ :=
  [128598310, 142498117, 656701, 28530355, 515511690, 283989914, 131976159, 494158390,
    490488501, 832054, 359789547, 760279385, 1407885809, 2556392043, 2528658747, 967147672,
    84081330, 57418, 3020809, 83287366, 638013496, 1638753347, 2137185563, 1819568794,
    1073588126, 218978303, 230599349, 2909169962, 7640450854, 9680216608, 6199004173,
    1283363570]
/-- Hit-row chunk `1` for `(m = 8, r = 192)`. -/
def rkmRowPack_m8_r192_p1 : List ℕ :=
  [129658140, 1839476669, 2227127546, 624173850, 171865651, 2676388728, 5808883192, 5881249135,
    2545880240, 6292442, 3115693015, 12077196821, 21305094070, 24078557053, 18546955448,
    9109537464, 2037594800, 81960, 784474786, 893062536, 15865351, 2081105395, 12197785008,
    32378603628, 59462371476, 86462989797, 106016297030, 113571791723, 108704203555,
    94390164420, 75175354160, 55366899423]
/-- Hit-row chunk `2` for `(m = 8, r = 192)`. -/
def rkmRowPack_m8_r192_p2 : List ℕ :=
  [37947845639, 24324693570, 14641487787, 8303563658, 4449746538, 2258793696, 1088462163,
    498787609, 217666122, 90547846, 35929664, 13603345, 4914393, 1693803, 556835, 174569,
    52183, 14873, 4042, 1047, 258, 60, 12, 2, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Hit-row chunk `3` for `(m = 8, r = 192)`. -/
def rkmRowPack_m8_r192_p3 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0]
/-- Hit-row chunk `4` for `(m = 8, r = 192)`. -/
def rkmRowPack_m8_r192_p4 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0]
/-- Hit-row chunk `5` for `(m = 8, r = 192)`. -/
def rkmRowPack_m8_r192_p5 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0]
/-- Certified `10 ^ 12`-scaled hit row for `(m = 8, r = 192)`. -/
def rkmRowPack_m8_r192 : List ℕ :=
  rkmRowPack_m8_r192_p0 ++ rkmRowPack_m8_r192_p1 ++ rkmRowPack_m8_r192_p2 ++ rkmRowPack_m8_r192_p3
    ++ rkmRowPack_m8_r192_p4 ++ rkmRowPack_m8_r192_p5

/-- Sign-kick mask segment `0` for `(m = 8, r = 384)`. -/
def rkmMkPack_m8_r384_s0 : List Bool :=
  [false, false, true, true, false, true, true]
/-- Sign-kick mask segment `1` for `(m = 8, r = 384)`. -/
def rkmMkPack_m8_r384_s1 : List Bool := [true, false, true, true, true, true]
/-- Sign-kick mask segment `2` for `(m = 8, r = 384)`. -/
def rkmMkPack_m8_r384_s2 : List Bool :=
  [true, true, true, false, true, false, false, true]
/-- Sign-kick mask segment `3` for `(m = 8, r = 384)`. -/
def rkmMkPack_m8_r384_s3 : List Bool := [false, false, true]
/-- Sign-kick mask segment `4` for `(m = 8, r = 384)`. -/
def rkmMkPack_m8_r384_s4 : List Bool :=
  [false, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, true, true, true, true, false, true, true, true, true, true,
    true, true, true, true, true, true, true, true, true, true, false, true, true, true, true,
    true, true, true, false, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, false, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, true, true, true, true, true, true]
/-- Sign-kick mask segment `5` for `(m = 8, r = 384)`. -/
def rkmMkPack_m8_r384_s5 : List Bool :=
  [false, false, false, false, false, false, false, false, true, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, true]
/-- Sign-kick mask segment `6` for `(m = 8, r = 384)`. -/
def rkmMkPack_m8_r384_s6 : List Bool :=
  [false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, true, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, true, false, false, false, false, false, false, false, true,
    false, false, false, false, false, false, false, true]
/-- Multi-segment sign-kick masks for `(m = 8, r = 384)`. -/
def rkmMasksPack_m8_r384 : List (List Bool) :=
  [rkmMkPack_m8_r384_s0, rkmMkPack_m8_r384_s1, rkmMkPack_m8_r384_s2, rkmMkPack_m8_r384_s3,
    rkmMkPack_m8_r384_s4, rkmMkPack_m8_r384_s5, rkmMkPack_m8_r384_s6, []]
/-- Hit-row chunk `0` for `(m = 8, r = 384)`. -/
def rkmRowPack_m8_r384_p0 : List ℕ :=
  [461, 158237, 837521, 2840887, 8998130, 19568929, 22360785, 10232122, 59256, 6371490,
    12300129, 2082845, 3877995, 10159485, 1630985, 9412268, 2232311, 2719027, 32923946,
    6407439, 12443714, 87734425, 73534831, 36810177, 102206820, 149731631, 56514780, 28087293,
    51688994, 17334097, 6933147, 19762068]
/-- Hit-row chunk `1` for `(m = 8, r = 384)`. -/
def rkmRowPack_m8_r384_p1 : List ℕ :=
  [10859866, 38420337, 88750727, 37057765, 7765, 3469868, 7674355, 64065181, 191138687,
    193573348, 110913994, 92817524, 101513413, 43696211, 21822, 11642612, 9461115, 15535695,
    68223747, 141504479, 134198944, 108042611, 159398549, 281580283, 311660544, 189593023,
    74865467, 21848047, 431812, 110267337, 535388577, 1102088210]
/-- Hit-row chunk `2` for `(m = 8, r = 384)`. -/
def rkmRowPack_m8_r384_p2 : List ℕ :=
  [1421255088, 1481770260, 1467103926, 1328409623, 910287597, 379139214, 77324502, 11260360,
    22473897, 117785489, 384005827, 980236868, 2217643781, 4279788872, 6619098151, 8006362718,
    7643167320, 5873808018, 3609032477, 1578269309, 273363019, 59923685, 845777778, 1773292640,
    1823230630, 907143424, 49777006, 493068619, 2887752290, 7164151224, 12623615854,
    17892500474]
/-- Hit-row chunk `3` for `(m = 8, r = 384)`. -/
def rkmRowPack_m8_r384_p3 : List ℕ :=
  [21094049645, 20682801518, 16558979991, 10384884488, 4611603869, 1025935475, 884530,
    759689140, 2088544997, 2918044310, 2658320568, 1424446555, 162590441, 485347885,
    4080982687, 11895807549, 23567713753, 37482911095, 51402664952, 63250624096, 71644001421,
    76016843805, 76450670592, 73421008412, 67603667923, 59772557176, 50748185177, 41345603273,
    32300592718, 24188685407, 17367998983, 11968482019]
/-- Hit-row chunk `4` for `(m = 8, r = 384)`. -/
def rkmRowPack_m8_r384_p4 : List ℕ :=
  [7928380612, 5059823344, 3119049508, 1862431556, 1080351685, 610476298, 336855621, 181863067,
    96204100, 49908799, 25401968, 12684292, 6212409, 2983154, 1403875, 647231, 292251, 129229,
    55959, 23731, 9858, 4011, 1599, 624, 238, 89, 32, 10, 3, 0, 0, 0]
/-- Hit-row chunk `5` for `(m = 8, r = 384)`. -/
def rkmRowPack_m8_r384_p5 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0]
/-- Hit-row chunk `6` for `(m = 8, r = 384)`. -/
def rkmRowPack_m8_r384_p6 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0]
/-- Hit-row chunk `7` for `(m = 8, r = 384)`. -/
def rkmRowPack_m8_r384_p7 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0]
/-- Hit-row chunk `8` for `(m = 8, r = 384)`. -/
def rkmRowPack_m8_r384_p8 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0]
/-- Hit-row chunk `9` for `(m = 8, r = 384)`. -/
def rkmRowPack_m8_r384_p9 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0]
/-- Hit-row chunk `10` for `(m = 8, r = 384)`. -/
def rkmRowPack_m8_r384_p10 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0]
/-- Hit-row chunk `11` for `(m = 8, r = 384)`. -/
def rkmRowPack_m8_r384_p11 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0]
/-- Certified `10 ^ 12`-scaled hit row for `(m = 8, r = 384)`. -/
def rkmRowPack_m8_r384 : List ℕ :=
  rkmRowPack_m8_r384_p0 ++ rkmRowPack_m8_r384_p1 ++ rkmRowPack_m8_r384_p2 ++ rkmRowPack_m8_r384_p3
    ++ rkmRowPack_m8_r384_p4 ++ rkmRowPack_m8_r384_p5 ++ rkmRowPack_m8_r384_p6
    ++ rkmRowPack_m8_r384_p7 ++ rkmRowPack_m8_r384_p8 ++ rkmRowPack_m8_r384_p9
    ++ rkmRowPack_m8_r384_p10 ++ rkmRowPack_m8_r384_p11

/-- Sign-kick mask segment `0` for `(m = 8, r = 512)`. -/
def rkmMkPack_m8_r512_s0 : List Bool :=
  [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true]
/-- Sign-kick mask segment `1` for `(m = 8, r = 512)`. -/
def rkmMkPack_m8_r512_s1 : List Bool :=
  [false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, true,
    true, true, true]
/-- Sign-kick mask segment `2` for `(m = 8, r = 512)`. -/
def rkmMkPack_m8_r512_s2 : List Bool :=
  [true, false, true, true, true, true, true, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, true, false, false, false, false, false, false,
    false, false, false, false, false, true]
/-- Sign-kick mask segment `3` for `(m = 8, r = 512)`. -/
def rkmMkPack_m8_r512_s3 : List Bool :=
  [true, false, true, false, false, false, false, false, true, true, true, false, false, false,
    false, true, true, false, false, true, true, false, true, true, true, false, false, false,
    true, false, false, false, true, false, true, true, true, true, true, false, true, true,
    true, true, true, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, true, true, true, true, false, false, false, false,
    false, false, false, false, false, true, false, false, false, false, false, false, true,
    false, true]
/-- Sign-kick mask segment `4` for `(m = 8, r = 512)`. -/
def rkmMkPack_m8_r512_s4 : List Bool :=
  [true, true, false, true, false, false, true, true, false, true, true, false, false, true,
    true, true, true, true, false, true, true, true, false, false, true, false, true, true,
    true, true, true, true, true, true, true, true, true, false, true, false, true, true, true,
    false, false, false, true, true, true, true, true, true, false, true, true, false, true,
    false, true, false, true, true, false, false, true, false, false, true, false, false, true,
    false, true, false, false, false, true, true, false, false, false, true, true, true, false,
    true, true, false, false, false, true, false, false, false, true, true, false, true, false,
    false, false, true, false, true, true, false, true, true, false, false, true, false, false,
    true, true, true, true, true, false, false, true, true, true, true, true, false, true,
    true, false, true, true, true, true, true, true, true, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, true, true,
    true, true, true, false, false, false, false, false, true, true, true, true, true, false,
    false, false, false, true, true, true, true, false, false, false, false, true, true]
/-- Sign-kick mask segment `5` for `(m = 8, r = 512)`. -/
def rkmMkPack_m8_r512_s5 : List Bool :=
  [true, false, false, true, true, true, false, false, false, false, true, true, true, false,
    false, true, false, false, false, false, true, false, false, false, true, true, false,
    false, false, false, true, false, false, false, false, false, false, true, true, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    true, true, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, true, false, false, false, true, true, true, true,
    false, false, false, false, false, false, false, false, false, true, true, false, false,
    false, false, false, false, false, false, false, false, false, true, false, true, false,
    true, false, false, false, true, false, false, false, false, false, false, false, true,
    false, false, false, false, true, false, false, false, false, false, false, false, false,
    false, true, false, false, false, true, false, false, false, false, false, false, true,
    false, false, false, true, false, false, true, true, false, false, false, false, false,
    false, false, false, true, true, true, false, false, true, true, true, false, false, true,
    true, false, false, false, true, true, false, false, false, false, false, true, true,
    false, false, false, true, true, false, true, true, false, false, false, false, false,
    true, true, false, false, false, true, true, true, false, false, false, false, false, true,
    true, true, false, false, true, false, false, true, true, true, false, false, false, true,
    false, false, false, false, false, true, false, false, false, false, false, true, true,
    true, false, false, false, true, false, false, true, true, true, false, false, true, true,
    false, false, true, false, false, false, false, false, false, false, false, true, true,
    true, true, false, false, false, false, true, false, false, false, false, false, true,
    true, true, true, true, false, false, false, false, false, true, true, true, true, true,
    true, false, false, false, false, false, false, true, true, true, true, true, true, true,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, true, true, true, true, false,
    false, false, false, true, true, false, false, true, true, true, false, false, false,
    false, false, true, true, true, true, true, false, false, false, false, false, true]
/-- Sign-kick mask segment `6` for `(m = 8, r = 512)`. -/
def rkmMkPack_m8_r512_s6 : List Bool :=
  [true, true, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, true, false, false, false, false, false, false, false, false,
    false, true, false, false, false, false, false, false, false, false, false, true, false,
    false, false, false, false, false, false, false, false, true, false, false, false, false,
    false, false, false, false, false, true, false, false, false, false, false, false, false,
    false, false, true, false, false, false, false, false, false, false, false, false, true,
    false, false, false, false, false, false, false, false, false, true, false, false, false,
    false, false, false, false, false, false, true, false, false, false, false, false, false,
    false, false, false, true, false, false, false, false, false, false, false, false, false,
    true, false, false, false, false, false, false, false, false, false, true, false, false,
    false, false, false, false, false, false, false, true, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, true, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, true, false, false, false, false,
    false, false, false, false, false, true, false, false, false, false, false, false, false,
    false, false, true, false, false, false, false, false, false, false, false, false, true,
    false, false, false, false, false, false, false, false, false, true, false, false, false,
    false, false, false, false, false, false, true, false, false, false, false, false, false,
    false, false, false, true, false, false, false, false, false, false, false, false, false,
    true, false, false, false, false, false, false, false, false, false, true, false, false,
    false, false, false, false, false, false, false, true, false, false, false, false, false,
    false, false, false, false, true, false, false, false, false, false, false, false, false,
    false, true, false, false, false, false, false, false, false, false, false, true, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, true, false, false, false, false, false, false, false,
    false, false, true, false, false, false, false, false, false, false, false, false, true,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, true, false, false, false, false, false, false,
    false, false, false, true, false, false, false, false, false, false, false, false, false,
    true, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, true, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, true, false, false, false, false,
    false, false, false, false, false, true, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, true]
/-- Multi-segment sign-kick masks for `(m = 8, r = 512)`. -/
def rkmMasksPack_m8_r512 : List (List Bool) :=
  [rkmMkPack_m8_r512_s0, rkmMkPack_m8_r512_s1, rkmMkPack_m8_r512_s2, rkmMkPack_m8_r512_s3,
    rkmMkPack_m8_r512_s4, rkmMkPack_m8_r512_s5, rkmMkPack_m8_r512_s6, []]
/-- Hit-row chunk `0` for `(m = 8, r = 512)`. -/
def rkmRowPack_m8_r512_p0 : List ℕ :=
  [5710, 39331, 6303, 20979, 24118, 6907, 20020, 37978, 184, 42, 223, 418, 749, 5550, 75787,
    112559, 45337, 6773, 424, 6470, 11616, 4219, 5343, 131044, 140813, 124606, 137625, 155268,
    1433, 56602, 353008, 30510]
/-- Hit-row chunk `1` for `(m = 8, r = 512)`. -/
def rkmRowPack_m8_r512_p1 : List ℕ :=
  [3485, 0, 6911, 1795, 55199, 92390, 2739, 43273, 92995, 3808, 20326, 138458, 184083, 104792,
    5712, 16587, 7514, 625, 420013, 73946, 11318, 82564, 246658, 145315, 14661, 40966, 12949,
    84025, 336884, 618793, 122704, 51231]
/-- Hit-row chunk `2` for `(m = 8, r = 512)`. -/
def rkmRowPack_m8_r512_p2 : List ℕ :=
  [221, 57566, 229551, 47207, 37478, 171784, 65789, 284502, 3649, 261851, 445274, 134102,
    15478, 70136, 11231, 21085, 151213, 732505, 136492, 20453, 170386, 454460, 270894, 6138,
    27125, 205287, 279503, 1053258, 619984, 13563, 539821, 408685]
/-- Hit-row chunk `3` for `(m = 8, r = 512)`. -/
def rkmRowPack_m8_r512_p3 : List ℕ :=
  [134914, 3020, 6427, 52802, 230450, 458991, 281357, 61630, 233411, 365771, 56190, 10790,
    10103, 208, 86383, 294661, 58837, 0, 102970, 62363, 6639, 1230, 21457, 4773, 21259, 152267,
    24256, 75, 21565, 51030, 31450, 53]
/-- Hit-row chunk `4` for `(m = 8, r = 512)`. -/
def rkmRowPack_m8_r512_p4 : List ℕ :=
  [24129, 57850, 12145, 140513, 68083, 9048, 57681, 222268, 78633, 20502, 599, 3970, 17140,
    497195, 15594, 61464, 247912, 105099, 156, 26289, 228042, 142959, 2043, 751157, 405784,
    695546, 77408, 358031, 912435, 496, 353226, 652519]
/-- Hit-row chunk `5` for `(m = 8, r = 512)`. -/
def rkmRowPack_m8_r512_p5 : List ℕ :=
  [54471, 632325, 845874, 7329, 1039372, 1067876, 77924, 92, 220848, 504160, 37549, 2286914,
    1049730, 847179, 146769, 424199, 1086168, 38957, 545186, 1002786, 26801, 1126184, 865182,
    34659, 1535405, 562425, 8472, 106087, 502207, 776968, 1853, 1737588]
/-- Hit-row chunk `6` for `(m = 8, r = 512)`. -/
def rkmRowPack_m8_r512_p6 : List ℕ :=
  [2200746, 949170, 4436, 1976443, 1336082, 33355, 534397, 199086, 4068, 3761622, 28153,
    1421217, 1586797, 64346, 955359, 159197, 1856480, 2176909, 44395, 319450, 2304264, 84433,
    1596299, 781441, 969, 56904, 590384, 1330693, 45221, 980567, 2470468, 449715]
/-- Hit-row chunk `7` for `(m = 8, r = 512)`. -/
def rkmRowPack_m8_r512_p7 : List ℕ :=
  [133806, 1799339, 722065, 11933, 25119, 26617, 1431, 3195669, 597276, 1263828, 493150,
    1031168, 2431517, 120643, 951446, 449978, 17307, 3448716, 1407, 1332867, 1220097, 124011,
    2131713, 202777, 1369416, 1937638, 131646, 1968569, 531191, 887913, 1916482, 738]
/-- Hit-row chunk `8` for `(m = 8, r = 512)`. -/
def rkmRowPack_m8_r512_p8 : List ℕ :=
  [1773032, 247763, 1476597, 1701059, 79038, 936879, 875228, 352723, 1681401, 105358, 855058,
    444777, 1448291, 2042175, 68756, 439501, 1785557, 343593, 1883642, 230211, 1116981, 533866,
    1355042, 2497188, 117010, 589872, 1532140, 392798, 2237897, 36283, 1522758, 334905]
/-- Hit-row chunk `9` for `(m = 8, r = 512)`. -/
def rkmRowPack_m8_r512_p9 : List ℕ :=
  [1202066, 1981089, 102081, 1075861, 740920, 564531, 1921391, 15194, 2354194, 516419, 621534,
    1596319, 114521, 2471157, 30973, 1357272, 1081125, 758207, 3158080, 416953, 92672, 84497,
    5589, 3774430, 781297, 2474745, 1922, 2506296, 300095, 1616139, 664788, 197637]
/-- Hit-row chunk `10` for `(m = 8, r = 512)`. -/
def rkmRowPack_m8_r512_p10 : List ℕ :=
  [1445670, 3754, 937393, 528061, 481073, 1189705, 9653, 132065, 289978, 1812220, 48660, 80649,
    1991790, 10752, 1255636, 604372, 280212, 951162, 1055322, 3932094, 88530, 1704516, 2000429,
    2882431, 3233185, 1559621, 9717698, 1822895, 19675, 1331602, 14027, 9080867]
/-- Hit-row chunk `11` for `(m = 8, r = 512)`. -/
def rkmRowPack_m8_r512_p11 : List ℕ :=
  [12243823, 3493618, 5346552, 8479292, 2681773, 14147888, 1031941, 17078688, 10421, 18362423,
    899834, 17910491, 4056235, 18830575, 15557559, 405840, 2938972, 40310810, 1174956, 301314,
    36076409, 3283502, 28378627, 781567, 46691679, 11768859, 414956, 9149175, 318280, 27129364,
    50060526, 5055562]
/-- Hit-row chunk `12` for `(m = 8, r = 512)`. -/
def rkmRowPack_m8_r512_p12 : List ℕ :=
  [33524043, 8622076, 41850949, 42500821, 7128, 178376, 67343, 56804767, 36707653, 25593032,
    26518290, 31463903, 27754456, 32602380, 26886373, 35114457, 27365996, 38079521, 31353779,
    36676562, 33932023, 32535916, 50394395, 81548826, 1116670, 1784475, 621678, 65880586,
    67563675, 17152788, 63553404, 11450754]
/-- Hit-row chunk `13` for `(m = 8, r = 512)`. -/
def rkmRowPack_m8_r512_p13 : List ℕ :=
  [70336310, 6056291, 77411023, 2008623, 86150119, 1089, 92846055, 3002052, 92861479, 14546940,
    81355055, 34226069, 63903924, 64886493, 36809381, 97340651, 10726287, 110978132, 685092,
    130517049, 8267684, 115941051, 43250544, 76038277, 95350020, 29675417, 145224669, 1372828,
    176800471, 20834147, 139292512, 113255961]
/-- Hit-row chunk `14` for `(m = 8, r = 512)`. -/
def rkmRowPack_m8_r512_p14 : List ℕ :=
  [65994401, 156094086, 4757732, 240838900, 42728417, 163444988, 192855387, 34784710,
    348550866, 13613248, 174609780, 453987638, 17087516, 448659981, 44509379, 365462443,
    438836103, 30807145, 741708990, 231423748, 309853516, 951338338, 35807019, 868667995,
    1078769719, 11662286, 1647240333, 1241404636, 89368051, 3776787622, 2054059, 5271131995]
/-- Hit-row chunk `15` for `(m = 8, r = 512)`. -/
def rkmRowPack_m8_r512_p15 : List ℕ :=
  [441102382, 2012474757, 142918668, 5796776535, 6587478601, 180132373, 6222966544,
    15265179612, 6343478445, 1028279508, 20514185173, 33183871563, 13416048167, 1286249357,
    46875189938, 133197735521, 195566156404, 194899475790, 145592803770, 85494410114,
    40485424540, 15676012333, 4995106821, 1311060597, 282325554, 49431918, 6931219, 760092,
    62804, 3672, 133, 1]
/-- Certified `10 ^ 12`-scaled hit row for `(m = 8, r = 512)`. -/
def rkmRowPack_m8_r512 : List ℕ :=
  rkmRowPack_m8_r512_p0 ++ rkmRowPack_m8_r512_p1 ++ rkmRowPack_m8_r512_p2 ++ rkmRowPack_m8_r512_p3
    ++ rkmRowPack_m8_r512_p4 ++ rkmRowPack_m8_r512_p5 ++ rkmRowPack_m8_r512_p6
    ++ rkmRowPack_m8_r512_p7 ++ rkmRowPack_m8_r512_p8 ++ rkmRowPack_m8_r512_p9
    ++ rkmRowPack_m8_r512_p10 ++ rkmRowPack_m8_r512_p11 ++ rkmRowPack_m8_r512_p12
    ++ rkmRowPack_m8_r512_p13 ++ rkmRowPack_m8_r512_p14 ++ rkmRowPack_m8_r512_p15

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
private def phb_m8_r192_0 : List ℕ :=
  [324811197247959, 428564393783918, 484672565448757, 509543521702579, 508193735168041,
    480830978595516, 422917712400180, 318835185215798]
private def pvn_m8_r192_0_0 : List ℕ := [3000000000000000]
private def pvn_m8_r192_0_1 : List ℕ :=
  [2808191179834082, 2534807119817249, 2233439024370504, 2076811979509468, 2019925843306905,
    2004123638994724, 2000672766929560, 2000082737706677, 2000006711181191]
private def phb_m8_r192_1 : List ℕ :=
  [450344626773823, 594196485842919, 671989412445982, 706472526348873, 704601072660481,
    666663124398340, 586367468118728, 442058998288655]
private def pvn_m8_r192_1_0 : List ℕ :=
  [2808191179834082, 1465192880182751, 2233439024370504, 1923188020490532, 2019925843306905,
    2004123638994724, 2000672766929560, 1999917262293323, 2000006711181191]
private def pvn_m8_r192_1_1 : List ℕ :=
  [2502632463096912, 2621308403980005, 2495538901178395, 2300990255708214, 2147995321144815,
    2055292368721667, 2013339962600636, 2004563806089386, 2004888100320194]
private def phb_m8_r192_2 : List ℕ :=
  [467986028264609, 617473012635884, 698313330436172, 734147255297709, 732202490940274,
    692778395098615, 609337307906365, 459375825908631]
private def pvn_m8_r192_2_0 : List ℕ :=
  [1497367536903088, 1378691596019995, 1504461098821605, 2300990255708214, 2147995321144815,
    1944707631278333, 1986660037399364, 1995436193910614, 2004888100320194]
private def pvn_m8_r192_2_1 : List ℕ :=
  [1982445822139922, 1867546388222104, 1775021566715318, 1905609497961732, 2209096305181368,
    2167368264714537, 1631115397502997, 1286454680404266, 1546494922523276]
private def phb_m8_r192_3 : List ℕ :=
  [2317961941554, 3058379645509, 3458786428376, 3636273936611, 3626641405951, 3431371572618,
    3018083028106, 2275315109886]
private def pvn_m8_r192_3_0 : List ℕ :=
  [1982445822139922, 1867546388222104, 1775021566715318, 1905609497961732, 2209096305181368,
    1832631735285463, 1631115397502997, 1286454680404266, 1546494922523276]
private def pvn_m8_r192_3_1 : List ℕ :=
  [1982752093905139, 1868194239517686, 1774946601663390, 1904070410710509, 2209353594598684,
    1834653589617805, 1632698222633294, 1286377456848172, 1544871292615797]
private def phb_m8_r192_4_p0 : List ℕ :=
  [123915120000000, 174329722228302, 212391582794473, 243957892500000, 271310076931709,
    295624419180961, 317603322725703, 337706791751162, 356255970000000, 373485858745595,
    389574752699579, 404661857745260, 418858424029943, 432255095887996, 444926942220761,
    456937005000000, 468338867673496, 479178555863135, 489495971376398, 499325992650912,
    508699332029792, 517643212633116, 526181909275434, 534337185471470, 542128650000000,
    549574050467890, 556689517008672, 563489766126247, 569988272398537, 576197414047573,
    582128597096836, 587792361858779, 593198474744397, 598356007804548, 603273407957673,
    607958557500000, 612418827209643, 616661123128515, 620691927922811, 624517337574602,
    628143094036316, 631574614380969, 634817016899613, 637875144530080, 640753585945101,
    643456694581089, 645988605849677, 648353252741024, 650554380000000, 652595557032651,
    654480189680158, 656211530980245, 657792691021216, 659226645981074, 660516246433199,
    661664224990564, 662673203352250, 663545698808835, 664284130256980, 664890823768104,
    665368017751204, 665717867745700, 665942450876474, 666043770000000]
private def phb_m8_r192_4_p1 : List ℕ :=
  [666023757567563, 665884279229033, 665627137198345, 665254073399853, 664766772412897,
    664166864230328, 663455926845295, 662635488679307, 661707030863419, 660671989383383,
    659531757098628, 658287685644122, 656941087223400, 655493236300347, 653945371196713,
    652298695601769, 650554380000000, 648713563022266, 646777352725450, 644746827805202,
    642623038746065, 640407008912926, 638099735587461, 635702190952950, 633215323030620,
    630640056570431, 627977293899014, 625227915727280, 622392781920069, 619472732229993,
    616468586997540, 613381147819321, 610211198186250, 606959504093304, 603626814622425,
    600213862500000, 596721364630295, 593150022606111, 589500523197839, 585773538822063,
    581969727990738, 578089735741947, 574134194053145, 570103722237797, 565998927326188,
    561820404431223, 557568737099907, 553244497651225, 548848247501046, 544380537474677,
    539841908107640, 535232889935212, 530554003771262, 525805760976849, 520988663719061,
    516103205220525, 511149870000000, 506129134104446, 501041465332954, 495887323452860,
    490667160408410, 485381420522275, 480030540690216, 474614950569200]
private def phb_m8_r192_4_p2 : List ℕ :=
  [469135072759228, 463591322979128, 457984110236584, 452313836992603, 446580899320669,
    440785687060786, 434928583968609, 429009967859864, 423030210750236, 416989678990902,
    410888733399876, 404727729389325, 398507017089012, 392226941466007, 385887842440807,
    379490055000000, 373033909305599, 366519730801166, 359947840314844, 353318554159409,
    346632184229447, 339889038095757, 333089419097087, 326233626429279, 319321955231929,
    312354696672645, 305332138028976, 298254562768104, 291122250624362, 283935477674671,
    276694516411934, 269399635816495, 262051101425684, 254649175401552, 247194116596818,
    239686180619120, 232125619893591, 224512683723842, 216847618351388, 209130667013566,
    201362070000000, 193542064707650, 185670885694496, 177748764731891, 169775930855637,
    161752610415801, 153679027125340, 145555402107535, 137381953942303, 129158898711398,
    120886450042542, 112564819152517, 104194214889251, 95774843772919, 87306910036096,
    78790615662990, 70226160427767, 61613741932013, 52953555641348, 44245794921210,
    35490651071846, 26688313362517, 17838969064957, 8942803486083]
private def phb_m8_r192_4 : List ℕ :=
  pCat phb_m8_r192_4_p0
    (pCat phb_m8_r192_4_p1
      phb_m8_r192_4_p2)
private def pvn_m8_r192_4_0 : List ℕ :=
  [1982752093905139, 1868194239517686, 1774946601663390, 1904070410710509, 1790646405401316,
    1834653589617805, 1632698222633294, 1286377456848172, 1544871292615797]
private def pvn_m8_r192_4_1 : List ℕ :=
  [1977455150223744, 2094649590315519, 1968178853784680, 1873781674533993, 1942159946959148,
    1928591297737928, 1731593976215342, 1861281467768486, 2075840611688395, 1992666517725000,
    1705342568233557, 1495550182060968, 1479232547185191, 1595489479380171, 1742318825956867,
    1859068712851195, 1931912826376366, 1970373607620849, 1988225230555232, 1995679733312234,
    1998524381493858, 1999527662757308, 1999857527547336, 1999959318160138, 1999988960608821,
    1999997143684103, 1999999293306554, 1999999832386857, 1999999961806043, 1999999991622033,
    1999999998227871, 1999999999637974, 1999999999928472, 1999999999986317, 1999999999997464,
    1999999999999546, 1999999999999922, 1999999999999988, 1999999999999999]
private def phb_m8_r192_5_p0 : List ℕ :=
  [1042176000000, 1466183082363, 1786298638861, 2051784000000, 2281826872591, 2486320270555,
    2671171689661, 2840249950127, 2996256000000, 3141166294509, 3276480363892, 3403368985621,
    3522767818179, 3635439216878, 3742014541372, 3843024000000, 3938918251110, 4030084388694,
    4116858003003, 4199532435726, 4278365990021, 4353587623278, 4425401496452, 4493990649453,
    4559520000000, 4622138812603, 4681982748174, 4739175578431, 4793830629992, 4846052008685,
    4895935643753, 4943570183465, 4989037767265, 5032414694750, 5073772007901, 5113176000000,
    5150688662255, 5186368077257, 5220268766837, 5252442000654, 5282936070839, 5311796537154,
    5339066446486, 5364786529890, 5388995379949, 5411729610815, 5433024002962, 5452911634420,
    5471424000000, 5488591119841, 5504441638438, 5519002915147, 5532301107062, 5544361245035,
    5555207303537, 5564862264942, 5573348178792, 5580686216514, 5586896722003, 5591999258454,
    5596012651788, 5598955030957, 5600843865418, 5601696000000]
private def phb_m8_r192_5_p1 : List ℕ :=
  [5601527687393, 5600354618466, 5598191950561, 5595054333963, 5590955936661, 5585910467553,
    5579931198193, 5573030983223, 5565222279550, 5556517164391, 5546927352255, 5536464210936,
    5525138776592, 5512961767979, 5499943599879, 5486094395804, 5471424000000, 5455941988808,
    5439657681435, 5422580150144, 5404718229932, 5386080527709, 5366675431017, 5346511116307,
    5325595556819, 5303936530072, 5281541624997, 5258418248725, 5234573633066, 5210014840679,
    5184748770955, 5158782165644, 5132121614222, 5104773559013, 5076744300097, 5048040000000,
    5018666688172, 4988630265294, 4957936507378, 4926591069721, 4894599490671, 4861967195259,
    4828699498669, 4794801609576, 4760278633350, 4725135575130, 4689377342779, 4653008749732,
    4616034517721, 4578459279410, 4540287580918, 4501523884261, 4462172569693, 4422237937967,
    4381724212509, 4340635541521, 4298976000000, 4256749591691, 4213960250975, 4170611844678,
    4126708173835, 4082252975377, 4037249923773, 3991702632611]
private def phb_m8_r192_5_p2 : List ℕ :=
  [3945614656128, 3898989490686, 3851830576203, 3804141297539, 3755924985832, 3707184919792,
    3657924326959, 3608146384915, 3557854222461, 3507050920759, 3455739514433, 3403922992642,
    3351604300118, 3298786338174, 3245471965677, 3191664000000, 3137365217936, 3082578356599,
    3027306114281, 2971551151301, 2915316090816, 2858603519622, 2801415988919, 2743756015065,
    2685626080302, 2627028633467, 2567966090679, 2508440836012, 2448455222144, 2388011570993,
    2327112174334, 2265759294400, 2203955164465, 2141701989420, 2079001946319, 2015857184925,
    1952269828235, 1888241972993, 1823775690189, 1758873025547, 1693536000000, 1627766610150,
    1561566828725, 1494938605016, 1427883865305, 1360404513288, 1292502430481, 1224179476619,
    1155437490047, 1086278288101, 1016703667474, 946715404585, 876315255930, 805504958425,
    734286229749, 662660768671, 590630255371, 518196351758, 445360701777, 372124931709,
    298490650466, 224459449879, 150032904977, 75212574267]
private def phb_m8_r192_5 : List ℕ :=
  pCat phb_m8_r192_5_p0
    (pCat phb_m8_r192_5_p1
      phb_m8_r192_5_p2)
private def pvn_m8_r192_5_0 : List ℕ :=
  [1977455150223744, 2094649590315519, 1968178853784680, 1873781674533993, 1942159946959148,
    1928591297737928, 1731593976215342, 1861281467768486, 2075840611688395, 1992666517725000,
    1705342568233557, 1495550182060968, 2520767452814809, 1595489479380171, 1742318825956867,
    1859068712851195, 1931912826376366, 1970373607620849, 1988225230555232, 1995679733312234,
    1998524381493858, 1999527662757308, 1999857527547336, 1999959318160138, 2000011039391179,
    1999997143684103, 1999999293306554, 1999999832386857, 2000000038193957, 1999999991622033,
    1999999998227871, 1999999999637974, 2000000000071528, 1999999999986317, 1999999999997464,
    1999999999999546, 2000000000000078, 1999999999999988, 1999999999999999]
private def pvn_m8_r192_5_1 : List ℕ :=
  [1977356496734562, 2094672431834913, 1968543052379636, 1873843931945446, 1942063369703338,
    1929126308601750, 1731788882128119, 1860349893570506, 2075465542116864, 1993816196926071,
    1706978641481578, 1492815563250037, 2520466082560233, 1598261988005002, 1741381974123459,
    1858365187608190, 1931487004323728, 1970152238318185, 1988123261242628, 1995637279476137,
    1998508182427104, 1999521939289871, 1999855640293046, 1999958634267575, 2000010867935288,
    1999997196923739, 1999999281020559, 1999999828870060, 2000000037431003, 1999999991811987,
    1999999998189528, 1999999999628855, 2000000000069784, 1999999999986682, 1999999999997399,
    1999999999999533, 2000000000000076, 1999999999999988, 1999999999999999]
private def phb_m8_r192_6_p0 : List ℕ :=
  [132368201142528, 186221921401012, 226880236667799, 260599895999352, 289817956317931,
    315790942871124, 339269174787476, 360744036221856, 380558578284768, 398963833262049,
    416150258543013, 432266556177596, 447431565431545, 461742114097012, 475278392028412,
    488107741713072, 500287401885009, 511866537882363, 522887773482431, 533388366414916,
    543401124117777, 552955126782629, 562076305171879, 570787907435508, 579110879998560,
    587064181151158, 594665041371390, 601929181074555, 608870994029878, 615503702860907,
    621839491672458, 627889619802365, 633664519893998, 639173882863628, 644426731850638,
    649431486855528, 654196021466607, 658727712833208, 663033485847652, 667119852339819,
    670992945959210, 674658553313709, 678122141847319, 681388884867132, 684463684070008,
    687351189869451, 690055819781245, 692581775091177, 694933055998272, 697113475401694,
    699126671477888, 700976119176088, 702665140744576, 704196915386411, 705574488131693,
    706800778003248, 707878585543831, 708810599765284, 709599404573430, 710247484716615,
    710757231300721, 711130946908962, 711370850360838, 711479081141088]
private def phb_m8_r192_6_p1 : List ℕ :=
  [711457703526458, 711308710435303, 711034027022656, 710635514041207, 710114970986748,
    709474139044873, 708714703854222, 707838298100182, 706846503951689, 705740855352711,
    704522840178956, 703193902269476, 701755443342007, 700208824800161, 698555369439917,
    696796363062261, 694933055998272, 692966664552456, 690898372369685, 688729331730671,
    686460664780551, 684093464694792, 681628796786340, 679067699557615, 676411185700728,
    673660243049033, 670815835482910, 667878903792468, 664850366499692, 661731120642349,
    658522042521852, 655223988417092, 651837795266151, 648364281317660, 644804246753460,
    641158474284120, 637427729718752, 633612762510505, 629714306278984, 625733079310815,
    621669785039472, 617525112505406, 613299736797495, 608994319476724, 604609508982988,
    600145941025829, 595604238959909, 590985014145927, 586288866297692, 581516383815999,
    576668144109921, 571744713906105, 566746649546624, 561674497275905, 556528793517220,
    551310065139217, 546018829712928, 540655595759669, 535220862990242, 529715122535797,
    524138857170727, 518492541527930, 512776642306758, 506991618473959]
private def phb_m8_r192_6_p2 : List ℕ :=
  [501137921457914, 495215995336420, 489226277018316, 483169196419174, 477045176631305,
    470854634088314, 464597978724402, 458275614128639, 451887937694393, 445435340764113,
    438918208769627, 432336921368149, 425691852574143, 418983370887192, 412211839416052,
    405377615998992, 398481053320588, 391522499025090, 384502295826481, 377420781615350,
    370278289562704, 363075148220811, 355811681621186, 348488209369826, 341105046739779,
    333662504761146, 326160890308605, 318600506186534, 310981651211822, 303304620294445,
    295569704515877, 287777191205412, 279927364014464, 272020502988913, 264056884639560,
    256036782010751, 247960464747231, 239828199159282, 231640248286203, 223396871958182,
    215098326856608, 206744866572880, 198336741665749, 189874199717249, 181357485387246,
    172786840466666, 164162503929424, 155484711983103, 146753698118424, 137969693157524,
    129132925301104, 120243620174461, 111302000872437, 102308288003336, 93262699731805,
    84165451820749, 75016757672268, 65816828367681, 56565872706624, 47264097245290,
    37911706333798, 28508902152735, 19055884748895, 9552852070223]
private def phb_m8_r192_6 : List ℕ :=
  pCat phb_m8_r192_6_p0
    (pCat phb_m8_r192_6_p1
      phb_m8_r192_6_p2)
private def pvn_m8_r192_6_0 : List ℕ :=
  [2022643503265438, 2094672431834913, 1968543052379636, 1873843931945446, 1942063369703338,
    1929126308601750, 1731788882128119, 1860349893570506, 1924534457883136, 1993816196926071,
    1706978641481578, 1492815563250037, 1479533917439767, 1598261988005002, 1741381974123459,
    1858365187608190, 1931487004323728, 1970152238318185, 1988123261242628, 1995637279476137,
    1998508182427104, 1999521939289871, 1999855640293046, 1999958634267575, 1999989132064712,
    1999997196923739, 1999999281020559, 1999999828870060, 2000000037431003, 1999999991811987,
    1999999998189528, 1999999999628855, 2000000000069784, 1999999999986682, 1999999999997399,
    1999999999999533, 2000000000000076, 1999999999999988, 1999999999999999]
private def pvn_m8_r192_6_1_p0 : List ℕ :=
  [1959065683919641, 2042676551591961, 1918249818287578, 1953527721173105, 2038911339873591,
    2077959173795452, 2087336274418793, 2062477025361564, 1995169585040386, 1940064357719980,
    1957428034584629, 2024768506418501, 2056880456341043, 2001303623834956, 1889963224947678,
    1803284836245967, 1799080165032497, 1873081522621497, 1971587584433968, 2032540353392130,
    2021041915205377, 1940910493798906, 1824061135000087, 1710401990741543, 1630706856309475,
    1598666127086151, 1611838167803125, 1657676996699284, 1720451971378632, 1786368423417502,
    1846040359456005, 1894749659159433, 1931433099826960, 1957273871626708, 1974455899252438,
    1985310030639882, 1991856095562953, 1995639442572201, 1997741303393308, 1998866554960035,
    1999448286264421, 1999739219821198, 1999880188692380, 1999946452304185, 1999976702643525,
    1999990127017255, 1999995922686425, 1999998358451078, 1999999355493361, 1999999753161198,
    1999999907760195, 1999999966360848, 1999999988024324, 1999999995837060, 1999999998586563,
    1999999999531106, 1999999999847961, 1999999999951794, 1999999999985051, 1999999999995465,
    1999999999998656, 1999999999999613, 1999999999999894, 1999999999999972]
private def pvn_m8_r192_6_1_p1 : List ℕ := [1999999999999994]
private def pvn_m8_r192_6_1 : List ℕ :=
  pCat pvn_m8_r192_6_1_p0
      pvn_m8_r192_6_1_p1
private def phb_m8_r192_7_p0 : List ℕ :=
  [136307859692160, 191764421627229, 233632845348855, 268356098768940, 298443772636273,
    325189790005406, 349366801661161, 371480816764789, 391885096614960, 410838144940670,
    428536087691173, 445132052717293, 460748416283281, 475484888055002, 489424044567679,
    502635232614840, 515177394519927, 527101158923012, 538450418207654, 549263539000801,
    559574305184165, 569412662459543, 578805313363443, 587776197977687, 596346886153200,
    604536900433371, 612363984124895, 619844325527866, 626992746811499, 633822864142665,
    640347224260198, 646577421612228, 652524199347607, 658197536812161, 663606725699864,
    668760436614660, 673666777485502, 678333345026914, 682767270235939, 686975258753251,
    690963626783410, 694738333160402, 698305008055095, 701668978747085, 704835292821838,
    707808739102541, 710593866582963, 713195001591243, 715616263383840, 717861578342768,
    719934692927072, 721839185510474, 723578477220925, 725155841883714, 726574415157801,
    727837202944528, 728947089138862, 729906842785375, 730719124694363, 731386493567431,
    731911411676652, 732296250136745, 732543293805660, 732654745845360]
private def phb_m8_r192_7_p1 : List ℕ :=
  [732632731971405, 732479304417137, 732196445635739, 731786071761259, 731250035847661,
    730590130903229, 729808092736064, 728905602624965, 727884289828769, 726745733946030,
    725491467135920, 724122976210294, 722641704606042, 721049054246064, 719346387296555,
    717535027827637, 715616263383840, 713591346470392, 711461495960842, 709227898431093,
    706891709424549, 704454054652725, 701916031135345, 699278708283649, 696543128930380,
    693710310309656, 690781244989708, 687756901761268, 684638226484176, 681426142894628,
    678121553375285, 674725339690363, 671238363687629, 667661467969148, 663995476532476,
    660241195383900, 656399413125215, 652470901515451, 648456416008845, 644356696270300,
    640172466669492, 635904436754700, 631553301707391, 627119742778507, 622604427707379,
    618008011124096, 613331134936148, 608574428700087, 603738509978931, 598823984685977,
    593831447415651, 588761481762017, 583614660625490, 578391546508301, 573092691799223,
    567718639048031, 562269921230160, 556747062001984, 551150575947137, 545480968814243,
    539738737746452, 533924371503103, 528038350673861, 522081147885650]
private def phb_m8_r192_7_p2 : List ℕ :=
  [516053228002653, 509955048319704, 503787058749304, 497549702002550, 491243413764199,
    484868622862117, 478425751431327, 471915215072870, 465337423007685, 458692778225698,
    451981677630297, 445204512178390, 438361667016182, 431453521610870, 424480449878367,
    417442820307240, 410340996078973, 403175335184710, 395946190538586, 388653910087789,
    381298836919453, 373881309364505, 366401661098572, 358860221240045, 351257314445404,
    343593261001903, 335868376917691, 328082974009477, 320237359987800, 312331838540006,
    304366709410991, 296342268481794, 288258807846114, 280116615884800, 271915977338412,
    263657173377880, 255340481673352, 246966176461272, 238534528609745, 230045805682252,
    221500271999760, 212898188701276, 204239813802903, 195525402255426, 186755206000495,
    177929474025427, 169048452416690, 160112384412086, 151121510451688, 142076068227567,
    132976292732333, 123822416306539, 114614668684974, 105353277041878, 96038466035107,
    86670457849290, 77249472237990, 67775726564909, 58249435844164, 48670812779655,
    39040067803546, 29357409113903, 19623042711486, 9837172435741]
private def phb_m8_r192_7 : List ℕ :=
  pCat phb_m8_r192_7_p0
    (pCat phb_m8_r192_7_p1
      phb_m8_r192_7_p2)
private def pvn_m8_r192_7_0_p0 : List ℕ :=
  [2040934316080359, 2042676551591961, 1918249818287578, 1953527721173105, 2038911339873591,
    2077959173795452, 2087336274418793, 2062477025361564, 2004830414959614, 1940064357719980,
    1957428034584629, 2024768506418501, 2056880456341043, 2001303623834956, 1889963224947678,
    1803284836245967, 1799080165032497, 1873081522621497, 1971587584433968, 2032540353392130,
    1978958084794623, 1940910493798906, 1824061135000087, 1710401990741543, 1630706856309475,
    1598666127086151, 1611838167803125, 1657676996699284, 1720451971378632, 1786368423417502,
    1846040359456005, 1894749659159433, 1931433099826960, 1957273871626708, 1974455899252438,
    1985310030639882, 1991856095562953, 1995639442572201, 1997741303393308, 1998866554960035,
    1999448286264421, 1999739219821198, 1999880188692380, 1999946452304185, 2000023297356475,
    1999990127017255, 1999995922686425, 1999998358451078, 2000000644506639, 1999999753161198,
    1999999907760195, 1999999966360848, 2000000011975676, 1999999995837060, 1999999998586563,
    1999999999531106, 1999999999847961, 1999999999951794, 1999999999985051, 1999999999995465,
    1999999999998656, 1999999999999613, 1999999999999894, 1999999999999972]
private def pvn_m8_r192_7_0_p1 : List ℕ := [1999999999999994]
private def pvn_m8_r192_7_0 : List ℕ :=
  pCat pvn_m8_r192_7_0_p0
      pvn_m8_r192_7_0_p1
private def pvn_m8_r192_7_1_p0 : List ℕ :=
  [1988264891307059, 1973053751400925, 1980966516731697, 2000387129978585, 2024913405055324,
    2054734142745008, 2051389784001776, 2050392740338239, 1996246134135273, 1990195417142318,
    1969958772467876, 1954735496577914, 1968728453478506, 1967605291238340, 1968613823071917,
    2008475559222364, 2059260086654446, 2084776958837740, 2087230459471374, 2071840312518097,
    2031347263160268, 1976445758400666, 1942772403456099, 1956329788156099, 2006851250367737,
    2058754346761190, 2080242693253334, 2060141964423973, 2006892091391263, 1939035462784833,
    1877514887648746, 1840185530379096, 1837261342512150, 1868204947177186, 1921404459165298,
    1977946107513477, 2018162656333550, 2027887345033022, 2002239216117000, 1946045719873151,
    1871212500667905, 1792561175861122, 1723849288541631, 1674962914420994, 1650636784195702,
    1650665772729528, 1671169555584024, 1706248250432749, 1749504281017401, 1795183119888564,
    1838857891750626, 1877665891558090, 1910187585112175, 1936123666682992, 1955921748965353,
    1970445188596175, 1980717184393044, 1987742933586553, 1992403225413686, 1995408098911330,
    1997294147869038, 1998446915357542, 1999132597440496, 1999529036133827]
private def pvn_m8_r192_7_1_p1 : List ℕ :=
  [1999751539939962, 1999872648730891, 1999936549049934, 1999969239425574, 1999985469055423,
    1999993299653178, 1999996978324397, 1999998664598498, 1999999420537014, 1999999752682043,
    1999999896013636, 1999999956871122, 1999999982334482, 1999999992847252, 1999999997134789,
    1999999998863846, 1999999999553874, 1999999999826539, 1999999999933249, 1999999999974601,
    1999999999990457, 1999999999996467, 1999999999998716, 1999999999999544, 1999999999999845,
    1999999999999950, 1999999999999986, 1999999999999998]
private def pvn_m8_r192_7_1 : List ℕ :=
  pCat pvn_m8_r192_7_1_p0
      pvn_m8_r192_7_1_p1
private def pvn_m8_r192_7_2_p0 : List ℕ :=
  [1998575603676078, 2011340121733828, 1988062740236221, 2000810374045388, 1994658616330569,
    1977295115289295, 1983147997480620, 1988511910059065, 1977770324167973, 1977853022809383,
    1999087827230401, 2018968121439771, 2027573166411637, 2037521806639276, 2050560777918448,
    2050285773004602, 2031099000113418, 2009169589462758, 1999760375006913, 1998261949796626,
    1990873806548329, 1974741068760078, 1959518479225412, 1953770293472427, 1957343593911975,
    1967234343132309, 1985202082300111, 2015185500188108, 2053936724014719, 2087409674719867,
    2098388093975664, 2078733757157554, 2035824066306809, 1988613244918490, 1957110877169532,
    1952807545602640, 1975016526260730, 2013109756284095, 2051733827947454, 2076216031937079,
    2076689304791798, 2050456718687925, 2002508476427882, 1944181604655502, 1890103697514995,
    1854037351679120, 1844827329313561, 1863812790465965, 1904556100874699, 1954860272519904,
    2000286290518524, 2028008479233942, 2029884154122686, 2003983135625078, 1954380863726534,
    1889556414901187, 1820059442007247, 1756150922625116, 1705954100393869, 1674398558901587,
    1662995855830383, 1670296792573201, 1692770174371570, 1725818754559048]
private def pvn_m8_r192_7_2_p1 : List ℕ :=
  [1764698277850604, 1805197929973890, 1844036240593109, 1878997982189283, 1908876106014673,
    1933293577300151, 1952473229608363, 1967008147858753, 1977666444363902, 1985246485580051,
    1990484334553792, 1994005861878534, 1996311726323007, 1997783154455618, 1998698535449153,
    1999253782821350, 1999582180978317, 1999771558507242, 1999878035954715, 1999936407522743,
    1999967611654847, 1999983881729126, 1999992158920549, 1999996269377174, 1999998263042603,
    1999999208080197, 1999999646197978, 1999999844995758, 1999999933356829, 1999999971860136,
    1999999988322167, 1999999995233674, 1999999998085423, 1999999999242667, 1999999999704849,
    1999999999886625, 1999999999957066, 1999999999983974, 1999999999994106, 1999999999997867,
    1999999999999243, 1999999999999740, 1999999999999916, 1999999999999975, 1999999999999994]
private def pvn_m8_r192_7_2 : List ℕ :=
  pCat pvn_m8_r192_7_2_p0
      pvn_m8_r192_7_2_p1
private def pwalks_m8_r192 : List RkmSegWalk := [
  ⟨uOfHb phb_m8_r192_0, bDec bZ (zPad bZ 1 pvn_m8_r192_0_0),
    bDec bZ (zPad bZ 9 pvn_m8_r192_0_1)⟩,
  ⟨uOfHb phb_m8_r192_1, bDec bZ (zPad bZ 9 pvn_m8_r192_1_0),
    bDec bZ (zPad bZ 9 pvn_m8_r192_1_1)⟩,
  ⟨uOfHb phb_m8_r192_2, bDec bZ (zPad bZ 9 pvn_m8_r192_2_0),
    bDec bZ (zPad bZ 9 pvn_m8_r192_2_1)⟩,
  ⟨uOfHb phb_m8_r192_3, bDec bZ (zPad bZ 9 pvn_m8_r192_3_0),
    bDec bZ (zPad bZ 9 pvn_m8_r192_3_1)⟩,
  ⟨uOfHb phb_m8_r192_4, bDec bZ (zPad bZ 9 pvn_m8_r192_4_0),
    bDec bZ (zPad bZ 137 pvn_m8_r192_4_1)⟩,
  ⟨uOfHb phb_m8_r192_5, bDec bZ (zPad bZ 137 pvn_m8_r192_5_0),
    bDec bZ (zPad bZ 153 pvn_m8_r192_5_1)⟩,
  ⟨uOfHb phb_m8_r192_6, bDec bZ (zPad bZ 153 pvn_m8_r192_6_0),
    bDec bZ (zPad bZ 193 pvn_m8_r192_6_1)⟩,
  ⟨uOfHb phb_m8_r192_7, bDec bZ (zPad bZ 193 pvn_m8_r192_7_0),
    bDec bZ (zPad bZ 193 pvn_m8_r192_7_2)⟩
  ]
private def phb_m8_r384_0 : List ℕ :=
  [216435295293779, 285943931539822, 323806388845434, 340874854040897, 340427217795202,
    322532391555864, 284071325073086, 214453504621324]
private def pvn_m8_r384_0_1 : List ℕ :=
  [2976827277777315, 2211841099028999, 2030347445636916, 2003282041053529, 2000280242092391,
    2000019117834511, 2000001029694801, 2000000041868007, 2000000001124518]
private def phb_m8_r384_1 : List ℕ :=
  [458820175786556, 606171210458624, 686435657590928, 722619017568138, 721670075572984,
    683734916662519, 602201480719855, 454618986957932]
private def pvn_m8_r384_1_0 : List ℕ :=
  [2976827277777315, 2211841099028999, 1969652554363084, 1996717958946471, 2000280242092391,
    1999980882165489, 1999998970305199, 2000000041868007, 2000000001124518]
private def pvn_m8_r384_1_1 : List ℕ :=
  [2071160977057562, 2225837352804399, 2416574431915570, 2538221850680358, 2521539186518211,
    2388277747818618, 2220972683225659, 2092259100674177, 2024762605529182]
private def phb_m8_r384_2 : List ℕ :=
  [419873406035221, 554716606216018, 628167837394334, 661279787123627, 660411395695652,
    625696347794982, 551083845421227, 416028833464174]
private def pvn_m8_r384_2_0 : List ℕ :=
  [1928839022942438, 2225837352804399, 1583425568084430, 1461778149319642, 1478460813481789,
    1611722252181382, 2220972683225659, 2092259100674177, 2024762605529182]
private def pvn_m8_r384_2_1 : List ℕ :=
  [2120967755643897, 2163074303517250, 1929197476822008, 1718755122347016, 2084539880281268,
    1710375459484088, 1521034508935525, 2666434012692132, 1668201424955220]
private def phb_m8_r384_3 : List ℕ :=
  [44891209692131, 59308113187006, 67161229325289, 70701428483528, 70608583494711,
    66896987398409, 58919712720922, 44480163145761]
private def pvn_m8_r384_3_0 : List ℕ :=
  [1879032244356103, 1836925696482750, 2070802523177992, 1718755122347016, 1915460119718732,
    1710375459484088, 1521034508935525, 1333565987307868, 1668201424955220]
private def pvn_m8_r384_3_1 : List ℕ :=
  [1886570438552259, 1827203279659147, 2079365332250840, 1729774671080710, 1915507303913305,
    1735762244514263, 1542154320604453, 1321377748597249, 1638277716583486]
private def phb_m8_r384_4_p0 : List ℕ :=
  [98309021538048, 138667894397208, 169389364833020, 195081964614564, 217535804388060,
    237671432850805, 256037141020271, 272991102808080, 288782750768016, 303594162698028,
    317563144772926, 330797031846683, 343381398683746, 355385804759468, 366867721832183,
    377875301536872, 388449376429472, 398624939246282, 408432257773212, 417897729482326,
    427044546617276, 435893220769848, 444462001655177, 452767215087813, 460823538459600,
    468644227310714, 476241303221632, 483625710816067, 490807449874340, 497795687225020,
    504598852081089, 511224717725477, 517680471866408, 523972777530212, 530107826005579,
    536091383074668, 541928829545489, 547625196923439, 553185198917829, 558613259364372,
    563913537051022, 569089947858028, 574146184560027, 579085734585924, 583911895989004,
    588627791843600, 593236383254339, 597740481138511, 602142756920544, 606445752259331,
    610651887913572, 614763471837030, 618782706584215, 622711696097228, 626552451936061,
    630306899007359, 633976880840309, 637564164452855, 641070444846606, 644497349164645,
    647846440542764, 651119221681423, 654317138162915, 657441581535696]
private def phb_m8_r384_4_p1 : List ℕ :=
  [660493892185647, 663475362012068, 666387236924469, 669230719174689, 672006969537479,
    674717109351487, 677362222431458, 679943356861506, 682461526678411, 684917713453128,
    687312867777961, 689647910666244, 691923734870746, 694141206126565, 696301164323719,
    698404424614299, 700451778458592, 702443994614277, 704381820072452, 706265980943957,
    708097183299216, 709876113964554, 711603441277725, 713279815805207, 714905871023603,
    716482223967347, 718009475844727, 719488212624127, 720919005592234, 722302411885834,
    723638974998742, 724929225265252, 726173680321459, 727372845545669, 728527214479066,
    729637269227700, 730703480846821, 731726309708499, 732706205853411, 733643609327637,
    734538950505237, 735392650397345, 736205120948467, 736976765320627, 737707978165972,
    738399145888412, 739050646894825, 739662851836339, 740236123840177, 740770818732505,
    741267285252713, 741725865259536, 742146893929388, 742530699947277, 742877605690633,
    743187927406368, 743461975381488, 743700054107523, 743902462439070, 744069493746691,
    744201436064417, 744298572232094, 744361180032794, 744389532325483]
private def phb_m8_r384_4_p2 : List ℕ :=
  [744383897173172, 744344537966723, 744271713544486, 744165678307962, 744026682333623,
    743854971481070, 743650787497668, 743414368119788, 743145947170813, 742845754656010,
    742514016854412, 742150956407811, 741756792406983, 741331740475239, 740876012849422,
    740389818458424, 739873362999333, 739326849011293, 738750475947151, 738144440242993,
    737508935385626, 736844151978089, 736150277803265, 735427497885656, 734675994551394,
    733895947486541, 733087533793745, 732250928047300, 731386302346684, 730493826368599,
    729573667417587, 728625990475268, 727650958248225, 726648731214613, 725619467669506,
    724563323769046, 723480453573410, 722371009088663, 721235140307498, 720072995248933,
    718884719996976, 717670458738290, 716430353798913, 715164545680034, 713873173092869,
    712556372992666, 711214280611864, 709847029492423, 708454751517367, 707037576941548,
    705595634421667, 704129051045563, 702637952360802, 701122462402578, 699582703720954,
    698018797407454, 696430863121040, 694819019113463, 693183382254046, 691524068053875,
    689841190689446, 688134863025767, 686405196638928, 684652301838176]
private def phb_m8_r384_4_p3 : List ℕ :=
  [682876287687473, 681077262026588, 679255331491711, 677410601535612, 675543176447355,
    673653159371584, 671740652327381, 669805756226723, 667848570892535, 665869195076356,
    663867726475632, 661844261750638, 659798896541040, 657731725482113, 655642842220621,
    653532339430356, 651400308827370, 649246841184878, 647072026347869, 644875953247405,
    642658709914642, 640420383494561, 638161060259419, 635880825621942, 633579764148244,
    631257959570495, 628915494799337, 626552451936061, 624168912284538, 621764956362923,
    619340663915132, 616896113922096, 614431384612800, 611946553475109, 609441697266396,
    606916892023955, 604372213075231, 601807735047853, 599223531879475, 596619676827442,
    593996242478275, 591353300756974, 588690922936163, 586009179645057, 583308140878271,
    580587876004470, 577848453774860, 575089942331530, 572312409215642, 569515921375479,
    566700545174345, 563866346398332, 561013390263945, 558141741425597, 555251463982973,
    552342621488266, 549415276953286, 546469492856451, 543505331149654, 540522853265016,
    537522120121524, 534503192131553, 531466129207284, 528410990767008]
private def phb_m8_r384_4_p4 : List ℕ :=
  [525337835741331, 522246722579273, 519137709254262, 516010853270036, 512866211666445,
    509703841025153, 506523797475258, 503326136698810, 500110913936245, 496878183991732,
    493628001238430, 490360419623666, 487075492674027, 483773273500372, 480453814802764,
    477117168875330, 473763387611034, 470392522506385, 467004624666068, 463599744807501,
    460177933265330, 456739239995841, 453283714581317, 449811406234324, 446322363801929,
    442816635769856, 439294270266583, 435755315067371, 432199817598236, 428627824939863,
    425039383831458, 421434540674544, 417813341536704, 414175832155265, 410522057940931,
    406852063981360, 403165895044690, 399463595583015, 395745209735809, 392010781333301,
    388260353899806, 384493970656998, 380711674527146, 376913508136301, 373099513817437,
    369269733613547, 365424209280698, 361562982291040, 357686093835777, 353793584828092,
    349885495906036, 345961867435373, 342022739512389, 338068151966660, 334098144363784,
    330112756008073, 326112025945214, 322095992964885, 318064695603347, 314018172145991,
    309956460629853, 305879598846103, 301787624342492, 297680574425766]
private def phb_m8_r384_4_p5 : List ℕ :=
  [293558486164060, 289421396389242, 285269341699246, 281102358460356, 276920482809473,
    272723750656349, 268512197685789, 264285859359827, 260044770919874, 255788967388838,
    251518483573218, 247233354065165, 242933613244529, 238619295280868, 234290434135435,
    229947063563148, 225589217114521, 221216928137582, 216830229779763, 212429154989765,
    208013736519403, 203584006925428, 199139998571322, 194681743629075, 190209274080941,
    185722621721168, 181221818157714, 176706894813931, 172177882930242, 167634813565787,
    163077717600053, 158506625734490, 153921568494094, 149322576228986, 144709679115962,
    140082907160030, 135442290195925, 130787857889611, 126119639739758, 121437665079211,
    116741963076432, 112032562736932, 107309492904688, 102572782263532, 97822459338539,
    93058552497388, 88281089951711, 83490099758431, 78685609821072, 73867647891073,
    69036241569066, 64191418306157, 59333205405185, 54461630021962, 49576719166511,
    44678499704278, 39766998357340, 34842241705593, 29904256187930, 24953068103404,
    19988703612383, 15011188737682, 10020549365696, 5016811247510]
private def phb_m8_r384_4 : List ℕ :=
  pCat phb_m8_r384_4_p0
    (pCat phb_m8_r384_4_p1
    (pCat phb_m8_r384_4_p2
    (pCat phb_m8_r384_4_p3
    (pCat phb_m8_r384_4_p4
      phb_m8_r384_4_p5))))
private def pvn_m8_r384_4_0 : List ℕ :=
  [1886570438552259, 1827203279659147, 1920634667749160, 1729774671080710, 1915507303913305,
    1735762244514263, 1542154320604453, 1321377748597249, 1638277716583486]
private def pvn_m8_r384_4_1 : List ℕ :=
  [2109673275471366, 1870362485419659, 1942582059041560, 1948431288405005, 1932726088466139,
    1969421312507094, 1854668516783030, 1772527961674474, 1889569354319901, 2041968528049938,
    2021535458142028, 1831535023516897, 1621132688357282, 1513020563199618, 1529845636542515,
    1625457731691926, 1741873342926493, 1841659520824259, 1911888504652158, 1954911744581909,
    1978564916296376, 1990457154398078, 1995996003702607, 1998408366722217, 1999397968343589,
    1999782517037960, 1999924727838096, 1999974971381334, 1999991985555475, 1999997523367734,
    1999999260027002, 1999999785876422, 1999999939901772, 1999999983616812, 1999999995656788,
    1999999998879048, 1999999999718050, 1999999999930823, 1999999999983431, 1999999999996124,
    1999999999999115, 1999999999999804, 1999999999999960, 1999999999999993, 1999999999999999]
private def phb_m8_r384_5_p0 : List ℕ :=
  [93437875200000, 131796992872302, 160996234972692, 185415783600000, 206757050613879,
    225894972138684, 243350671738278, 259464576046255, 274473758400000, 288551274764219,
    301828103109827, 314406259920492, 326367079788254, 337776675562934, 348689671315636,
    359151832800000, 369201969346094, 378873339823511, 388194712269591, 397191176179295,
    405884774636095, 414295002896108, 422439206413276, 430332902068945, 437990040000000,
    445423218943457, 452643864818511, 459662379950082, 466488268636056, 473130243494774,
    479596316077344, 485893874505720, 492029750341985, 498010276463966, 503841337386137,
    509528413200000, 515076618098124, 520490734278177, 525775241888321, 530934345566164,
    535971998034497, 540891921144318, 545697624695749, 550392423317920, 554979451647782,
    559461678013421, 563841916798707, 568122839641855, 572306985600000, 576396770394533,
    580394494837179, 584302352524133, 588122436874801, 591856747582358, 595507196535344,
    599075613262563, 602563749947565, 605973286053733, 609305832596480, 612562936095037,
    615746082232861, 618856699252608, 621896161108934, 624865790400000]
private def phb_m8_r384_5_p1 : List ℕ :=
  [627766861096460, 630600601084869, 633368194540752, 636070784145173, 638709473157268,
    641285327354106, 643799376848135, 646252617791602, 648646013976441, 650980498337421,
    653256974365635, 655476317438819, 657639376074441, 659746973111002, 661799906822531,
    663798951970877, 665744860800000, 667638363976149, 669480171477511, 671270973436619,
    673011440938581, 674702226777935, 676343966176747, 677937277466359, 679482762735033,
    680981008443558, 682432586010754, 683838052370662, 685197950503096, 686512809939087,
    687783147242693, 689009466470500, 690192259610078, 691332006998577, 692429177722545,
    693484230000000, 694497611545718, 695469759920640, 696401102866229, 697292058624576,
    698143036244993, 698954435877795, 699726649055912, 700460058964958, 701155040702332,
    701811961525886, 702431181092691, 703013051688361, 703557918447406, 704066119565043,
    704537986500858, 704973844174715, 705374011155260, 705738799841380, 706068516636916,
    706363462118959, 706623931200000, 706850213284217, 707042592418163, 707201347436083,
    707326752100115, 707419075235580, 707478580861582, 707505528317110]
private def phb_m8_r384_5_p2 : List ℕ :=
  [707500172382832, 707462763398766, 707393547377999, 707292766116603, 707160657299931,
    706997454605404, 706803387801966, 706578682846312, 706323561976029, 706038243799779,
    705722943384620, 705377872340592, 705003238902668, 704599248010169, 704166101383745,
    703703997600000, 703213132163869, 702693697578816, 702145883414934, 701569876375032,
    700965860358774, 700334016524946, 699674523351914, 698987556696341, 698273289850221,
    697531893596291, 696763536261881, 695968383771246, 695146599696448, 694298345306823,
    693423779617087, 692523059434127, 691596339402526, 690643772048852, 689665507824766,
    688661695148976, 687632480448080, 686578008196344, 685498420954425, 684393859407096,
    683264462400000, 682110366975447, 680931708407316, 679728620235055, 678501234296833,
    677249680761856, 675974088161885, 674674583421967, 673351291890409, 672004337368024,
    670633842136657, 669239926987032, 667822711245914, 666382312802638, 664918848134992,
    663432432334499, 661923179131095, 660391200917239, 658836608771455, 657259512481333,
    655660020566000, 654038240298077, 652394277725136, 650728237690671]
private def phb_m8_r384_5_p3 : List ℕ :=
  [649040223854600, 647330338713303, 645598683619218, 643845358800000, 642070463377260,
    640274095384894, 638456351787007, 636617328495454, 634757120387001, 632875821320115,
    630973524151398, 629050320751673, 627106302021725, 625141557907714, 623156177416269,
    621150248629259, 619123858718264, 617077093958751, 615010039743945, 612922780598437,
    610815400191498, 608687981350130, 606540606071861, 604373355537272, 602186310122282,
    599979549410188, 597753152203467, 595507196535344, 593241759681137, 590956918169382,
    588652747792737, 586329323618679, 583986720000000, 581625010585094, 579244268328055,
    576844565498583, 574425973691697, 571988563837276, 569532406209414, 567057570435603,
    564564125505750, 562052139781019, 559521681002525, 556972816299850, 554405612199424,
    551820134632741, 549216448944431, 546594619900187, 543954711694553, 541296787958567,
    538620911767278, 535927145647120, 533215551583163, 530486191026239, 527739124899935,
    524974413607476, 522192117038478, 519392294575595, 516575005101047, 513740307003033,
    510888258182044, 508018916057064, 505132337571664, 502228579200000]
private def phb_m8_r384_5_p4 : List ℕ :=
  [499307696952705, 496369746382688, 493414782590834, 490442860231609, 487454033518576,
    484448356229815, 481425881713266, 478386662891969, 475330752269235, 472258201933722,
    469169063564435, 466063388435648, 462941227421740, 459802631001964, 456647649265130,
    453476331914224, 450288728270950, 447084887280198, 443864857514452, 440628687178115,
    437376424111784, 434108115796446, 430823809357614, 427523551569404, 424207388858543,
    420875367308322, 417527532662483, 414163930329055, 410784605384128, 407389602575569,
    403978966326687, 400552740739842, 397110969600000, 393653696378232, 390180964235173,
    386692816024416, 383189294295870, 379670441299055, 376136298986366, 372586909016273,
    369022312756488, 365442551287083, 361847665403555, 358237695619864, 354612682171413,
    350972665017992, 347317683846683, 343647778074720, 339962986852309, 336263349065413,
    332548903338494, 328819688037220, 325075741271133, 321317100896279, 317543804517807,
    313755889492528, 309953392931440, 306136351702220, 302304802431682, 298458781508200,
    294598325084103, 290723469078032, 286834249177271, 282930700840046]
private def phb_m8_r384_5_p5 : List ℕ :=
  [279012859297785, 275080759557367, 271134436403318, 267173924400000, 263199257893753,
    259210471015027, 255207597680466, 251190671594986, 247159726253809, 243114794944481,
    239055910748862, 234983106545086, 230896415009504, 226795868618594, 222681499650854,
    218553340188666, 214411422120140, 210255777140931, 206086436756037, 201903432281574,
    197706794846527, 193496555394480, 189272744685327, 185035393296958, 180784531626927,
    176520189894099, 172242398140277, 167951186231809, 163646583861174, 159328620548554,
    154997325643377, 150652728325857, 146294857608497, 141923742337590, 137539411194691,
    133141892698080, 128731215204203, 124307406909092, 119870495849780, 115420509905687,
    110957476800000, 106481424101025, 101992379223537, 97490369430107, 92975421832410,
    88447563392525, 83906820924217, 79353221094206, 74786790423418, 70207555288223,
    65615541921662, 61010776414659, 56393284717212, 51763092639582, 47120225853464,
    42464709893139, 37796570156622, 33115831906795, 28422520272518, 23716660249748,
    18998276702619, 14267394364538, 9524037839243, 4768231601871]
private def phb_m8_r384_5 : List ℕ :=
  pCat phb_m8_r384_5_p0
    (pCat phb_m8_r384_5_p1
    (pCat phb_m8_r384_5_p2
    (pCat phb_m8_r384_5_p3
    (pCat phb_m8_r384_5_p4
      phb_m8_r384_5_p5))))
private def pvn_m8_r384_5_0 : List ℕ :=
  [2109673275471366, 2129637514580341, 2057417940958440, 2051568711594995, 2067273911533861,
    2030578687492906, 2145331483216970, 2227472038325526, 2110430645680099, 1958031471950062,
    1978464541857972, 2168464976483103, 2378867311642718, 2486979436800382, 2470154363457485,
    2374542268308074, 2258126657073507, 2158340479175741, 2088111495347842, 2045088255418091,
    2021435083703624, 2009542845601922, 2004003996297393, 2001591633277783, 1999397968343589,
    2000217482962040, 2000075272161904, 2000025028618666, 2000008014444525, 2000002476632266,
    2000000739972998, 2000000214123578, 2000000060098228, 2000000016383188, 2000000004343212,
    2000000001120952, 2000000000281950, 2000000000069177, 2000000000016569, 2000000000003876,
    1999999999999115, 2000000000000196, 2000000000000040, 2000000000000007, 2000000000000001]
private def pvn_m8_r384_5_1 : List ℕ :=
  [2011004843545732, 2051764965787215, 2112581586769212, 2078082268753572, 2047978837693293,
    2079379451228125, 2089852018102849, 2030605230377632, 1974493500430340, 2008155453718852,
    2116609876470160, 2202647979209287, 2190071535355854, 2089601078278705, 1978430322279546,
    1935094663010003, 1987852248488276, 2112871066492960, 2254064295112604, 2364858805127641,
    2417395179648893, 2410758325263205, 2362174344180050, 2292003503428413, 2217771874828276,
    2151954377572333, 2100362763711087, 2063193648348110, 2037928472590510, 2021590899354864,
    2011598263666459, 2005871604260163, 2002812566703903, 2001286736429775, 2000569884723596,
    2000248069210520, 2000107508064726, 2000046702003635, 2000020321008128, 2000008801613690,
    2000003764083446, 2000001578179999, 2000000645613257, 2000000257056422, 2000000099544631,
    2000000037509209, 2000000013767836, 2000000004929351, 2000000001723808, 2000000000589452,
    2000000000197247, 2000000000064617, 2000000000020724, 2000000000006504, 2000000000001995,
    2000000000000596, 2000000000000171, 2000000000000046, 2000000000000010, 2000000000000001]
private def phb_m8_r384_6_p0 : List ℕ :=
  [95741150608128, 135045833579544, 164964846930317, 189986345738004, 211853682243363,
    231463360043836, 249349348576407, 265860466106988, 281239629911376, 295664161842675,
    309268268523336, 322156481178053, 334412139324228, 346102985515917, 357284990326161,
    368005047649992, 378302923480668, 388212696530231, 397763843977928, 406982073783302,
    415889972399335, 424507515646836, 432852476551088, 440940754489842, 448786643475600,
    456403052808532, 463801690060629, 470993213977658, 477987363141682, 484793064940045,
    491418528411317, 497871323797172, 504158451060021, 510286399185285, 516261197742720,
    522088461909948, 527773431946125, 533321007931718, 538735780452065, 544022057790522,
    549183890105840, 554225090993913, 559149256772626, 563959783777848, 568659883916395,
    573252598686650, 577740811848005, 582127260895464, 586414547474784, 590605146855710,
    594701416565760, 598705604274021, 602619855003398, 606446217740184, 610186651501622,
    613843030915023, 617417151355858, 620910733686854, 624325428635501, 627662820843255,
    630924432616177, 634111727403589, 637226113028597, 640268944691856]
private def phb_m8_r384_6_p1 : List ℕ :=
  [643241527767831, 646145120410898, 648980935986912, 651750145344412, 654453878938250,
    657093228817259, 659669250486512, 662182964653746, 664635358868695, 667027389063287,
    669359980999977, 671634031634862, 673850410401653, 676009960422099, 678113499647957,
    680161821939218, 682155698082912, 684095876756459, 685983085439251, 687818031275823,
    689601401893757, 691333866179200, 693016075012657, 694648661967550, 696232243973820,
    697767421948713, 699254781396718, 700694892980492, 702088313064482, 703435584232841,
    704737235783108, 705993784197032, 707205733589847, 708373576139178, 709497792494712,
    710578852169700, 711617213915238, 712613326078295, 713567626944305, 714480545065168,
    715352499573403, 716183900483165, 716975148978803, 717726637691589, 718438750965198,
    719111865110516, 719746348650280, 720342562554066, 720900860464067, 721421588912127,
    721905087528424, 722351689242205, 722761720474944, 723135501326266, 723473345752971,
    723775561741476, 724042451473968, 724274311488535, 724471432833574, 724634101216688,
    724762597148347, 724857196080506, 724918168540432, 724945780259905]
private def phb_m8_r384_6_p2 : List ℕ :=
  [724940292300025, 724901961171777, 724831038952552, 724727773398781, 724592408054838,
    724425182358376, 724226331742218, 723996087732969, 723734678046451, 723442326680100,
    723119254002453, 722765676839808, 722381808560201, 721967859154778, 721524035316670,
    721050540517464, 720547575081356, 720015336257087, 719454018287718, 718863812478343,
    718244907261818, 717597488262554, 716921738358470, 716217837741154, 715485963974307,
    714726292050520, 713938994446446, 713124241176433, 712282199844648, 711413035695771,
    710516911664285, 709593988422420, 708644424426801, 707668375963828, 706665997193845,
    705637440194132, 704582855000756, 703502389649318, 702396190214646, 701264400849441,
    700107163821936, 698924619552583, 697716906649808, 696484161944850, 695226520525734,
    693944115770383, 692637079378909, 691305541405104, 689949630287154, 688569472877603,
    687165194472586, 685736918840359, 684284768249133, 682808863494255, 681309323924730,
    679786267469125, 678239810660860, 676670068662904, 675077155291906, 673461183041757,
    671822263106618, 670160505403415, 668476018593829, 666768910105784]
private def phb_m8_r384_6_p3 : List ℕ :=
  [665039286154448, 663287251762772, 661512910781566, 659716365909132, 657897718710461,
    656057069636019, 654194518040108, 652310162198844, 650404099327737, 648476425598897,
    646527236157873, 644556625140135, 642564685687204, 640551509962442, 638517189166523,
    636461813552563, 634385472440952, 632288254233875, 630170246429532, 628031535636071,
    625872207585240, 623692347145756, 621492038336412, 619271364338919, 617030407510490,
    614769249396176, 612487970740963, 610186651501622, 607865370858333, 605524207226087,
    603163238265855, 600782540895555, 598382191300800, 595962264945441, 593522836581918,
    591063980261401, 588585769343751, 586088276507293, 583571573758401, 581035732440909,
    578480823245348, 575906916218009, 573314080769847, 570702385685212, 568071899130434,
    565422688662239, 562754821236025, 560068363213982, 557363380373070, 554639937912855,
    551898100463207, 549137932091857, 546359496311831, 543562856088741, 540748073847963,
    537915211481682, 535064330355814, 532195491316815, 529308754698371, 526404180327971,
    523481827533373, 520541755148958, 517584021521975, 514608684518688]
private def phb_m8_r384_6_p4 : List ℕ :=
  [511615801530410, 508605429479450, 505577624824947, 502532443568618, 499469941260409,
    496390173004050, 493293193462522, 490179056863440, 487047817004336, 483899527257873,
    480734240576962, 477552009499803, 474352886154848, 471136922265678, 467904169155811,
    464654677753429, 461388498596032, 458105681835019, 454806277240200, 451490334204236,
    448157901747008, 444809028519927, 441443762810166, 438062152544839, 434664245295108,
    431250088280231, 427819728371550, 424373212096419, 420910585642065, 417431894859409,
    413937185266807, 410426502053759, 406899890084544, 403357393901810, 399799057730117,
    396224925479414, 392635040748477, 389029446828295, 385408186705401, 381771303065161,
    378118838295016, 374450834487674, 370767333444257, 367068376677407, 363354005414342,
    359624260599878, 355879182899394, 352118812701772, 348343190122285, 344552355005449,
    340746346927831, 336925205200826, 333088968873389, 329237676734731, 325371367316980,
    321490078897806, 317593849503004, 313682716909054, 309756718645632, 305815891998098,
    301860274009948, 297889901485231, 293904810990934, 289905038859338]
private def phb_m8_r384_6_p5 : List ℕ :=
  [285890621190343, 281861593853753, 277817992491550, 273759852520116, 269687209132442,
    265600097300302, 261498551776401, 257382607096489, 253252297581459, 249107657339406,
    244948720267667, 240775520054836, 236588090182746, 232386463928431, 228170674366065,
    223940754368872, 219696736611014, 215438653569456, 211166537525804, 206880420568127,
    202580334592750, 198266311306027, 193938382226094, 189596578684596, 185240931828398,
    180871472621269, 176488231845553, 172091240103814, 167680527820461, 163256125243357,
    158818062445406, 154366369326122, 149901075613177, 145422210863934, 140929804466959,
    136423885643518, 131904483449051, 127371626774634, 122825344348421, 118265664737070,
    113692616347152, 109106227426543, 104506526065802, 99893540199531, 95267297607716,
    90627825917061, 85975152602300, 81309304987497, 76630310247326, 71938195408346,
    67232987350250, 62514712807111, 57783398368605, 53039070481225, 48281755449481,
    43511479437082, 38728268468115, 33932148428198, 29123145065629, 24301283992520,
    19466590685919, 14619090488915, 9758808611741, 4885770132851]
private def phb_m8_r384_6 : List ℕ :=
  pCat phb_m8_r384_6_p0
    (pCat phb_m8_r384_6_p1
    (pCat phb_m8_r384_6_p2
    (pCat phb_m8_r384_6_p3
    (pCat phb_m8_r384_6_p4
      phb_m8_r384_6_p5))))
private def pvn_m8_r384_6_0 : List ℕ :=
  [2011004843545732, 2051764965787215, 2112581586769212, 2078082268753572, 2047978837693293,
    2079379451228125, 2089852018102849, 2030605230377632, 2025506499569660, 2008155453718852,
    2116609876470160, 2202647979209287, 2190071535355854, 2089601078278705, 1978430322279546,
    1935094663010003, 1987852248488276, 2112871066492960, 2254064295112604, 2364858805127641,
    2417395179648893, 2410758325263205, 2362174344180050, 2292003503428413, 2217771874828276,
    2151954377572333, 2100362763711087, 2063193648348110, 2037928472590510, 2021590899354864,
    2011598263666459, 2005871604260163, 2002812566703903, 2001286736429775, 2000569884723596,
    2000248069210520, 2000107508064726, 2000046702003635, 2000020321008128, 2000008801613690,
    2000003764083446, 2000001578179999, 2000000645613257, 2000000257056422, 2000000099544631,
    2000000037509209, 2000000013767836, 2000000004929351, 1999999998276192, 2000000000589452,
    2000000000197247, 2000000000064617, 2000000000020724, 2000000000006504, 2000000000001995,
    2000000000000596, 2000000000000171, 2000000000000046, 2000000000000010, 2000000000000001]
private def pvn_m8_r384_6_1_p0 : List ℕ :=
  [2010000099552688, 1993223007768313, 1991845542731925, 1972479450833641, 2044029296926708,
    2064705030940839, 2059312840581532, 2060364172759197, 2051306657279576, 2041742726363139,
    2052981550087993, 2081712956853353, 2094533247436825, 2069386593422024, 2019071063972047,
    1978235947731067, 1978698406219088, 2027878737630980, 2103068225696921, 2166475974610392,
    2187499999252159, 2156669579445620, 2087400664178743, 2008490799064770, 1951397459426630,
    1937784935499097, 1972920708227487, 2046792144233662, 2140333383797266, 2232679817795775,
    2306748180263676, 2352285415192096, 2366518235933854, 2352910377259374, 2318788378996095,
    2272743926351273, 2222580410157099, 2174172751047085, 2131186172135330, 2095356174932761,
    2067004276657170, 2045563345664466, 2030005656947634, 2019148495660258, 2011849909144298,
    2007117684278679, 2004154516161949, 2002359966564008, 2001306972823374, 2000707103000510,
    2000374552588416, 2000194692785355, 2000099532348319, 2000050146799675, 2000024942493589,
    2000012264185723, 2000005966648117, 2000002873296640, 2000001369265217, 2000000645136598,
    2000000300045074, 2000000137468185, 2000000061908870, 2000000027353636]
private def pvn_m8_r384_6_1_p1 : List ℕ :=
  [2000000011842793, 2000000005022796, 2000000002088490, 2000000000852929, 2000000000343042,
    2000000000136302, 2000000000053668, 2000000000020991, 2000000000008166, 2000000000003159,
    2000000000001211, 2000000000000456, 2000000000000167, 2000000000000058, 2000000000000019,
    2000000000000005]
private def pvn_m8_r384_6_1 : List ℕ :=
  pCat pvn_m8_r384_6_1_p0
      pvn_m8_r384_6_1_p1
private def pvn_m8_r384_6_2_p0 : List ℕ :=
  [2015831846610328, 1989484457754741, 2013171603421515, 2017295050933197, 1987971716019064,
    1969911162452848, 1979553580289849, 2001450899888725, 2019657829009818, 2033583611497679,
    2047697970468113, 2057666223074100, 2055274592350504, 2041787934709067, 2029472940343482,
    2031101249847558, 2049739156800526, 2076076307937881, 2093542015480051, 2088220397251736,
    2057946368322563, 2014618231278506, 1978236858708486, 1966861152516156, 1988369991661190,
    2037457622075629, 2098067950408219, 2149607180624954, 2174481946628304, 2164237423467563,
    2122090549227060, 2061173573088832, 1999639283835690, 1954862731167128, 1938833419501893,
    1955862627195970, 2002669708493395, 2070234126501064, 2146560851101396, 2219546099978109,
    2279305264801605, 2319573216718419, 2338073035134504, 2336013471488908, 2317047987830931,
    2286070315520183, 2248148635456064, 2207767891233477, 2168418436753849, 2132478622939043,
    2101298979849326, 2075395145299891, 2054677052467949, 2038667475190033, 2026685041107608,
    2017982438316744, 2011840270782607, 2007622413448679, 2004801185898938, 2002961179230367,
    2001789805346654, 2001061122229798, 2000617678095717, 2000353373442398]
private def pvn_m8_r384_6_2_p1 : List ℕ :=
  [2000198897493835, 2000110255036439, 2000060253344740, 2000032493330471, 2000017306800246,
    2000009111183209, 2000004743789205, 2000002443673529, 2000001245692472, 2000000628371794,
    2000000313589274, 2000000154764984, 2000000075497202, 2000000036382715, 2000000017311494,
    2000000008129344, 2000000003766383, 2000000001721412, 2000000000776182, 2000000000345363,
    2000000000151707, 2000000000065826, 2000000000028230, 2000000000011971, 2000000000005022,
    2000000000002084, 2000000000000852, 2000000000000343, 2000000000000134, 2000000000000049,
    2000000000000015, 2000000000000004]
private def pvn_m8_r384_6_2 : List ℕ :=
  pCat pvn_m8_r384_6_2_p0
      pvn_m8_r384_6_2_p1
private def phb_m8_r384_7_p0 : List ℕ :=
  [98980704000000, 139615323140219, 170546693670389, 196414834500000, 219022086952652,
    239295289244199, 257786478512813, 274856275842624, 290755818000000, 305668426803651,
    319732849969552, 333057155701860, 345727503442475, 357813927922013, 369374293566452,
    380457081000000, 391103401761246, 401348487669402, 411222813310738, 420752956514305,
    429962267981475, 438871399446579, 447498725313345, 455860682940136, 463972050000000,
    471846172599711, 479495154455492, 486930014968647, 494160822241578, 501196805733915,
    508046452250040, 514717588182739, 521217450349234, 527552747300037, 533729712624944,
    539754151500000, 545631481496826, 551366768497866, 556964758418182, 562429905318718,
    567766396401757, 572978174302246, 578068957025181, 583042255826830, 587901391293961,
    592649507838869, 597289586797511, 601824458292369, 606256812000000, 610589206944822,
    614824080425026, 618963756163142, 623010451762321, 626966285539551, 630833282798523,
    634613381597533, 638308438061420, 641920231281028, 645450467838825, 648900785995119,
    652272759565604, 655567901517729, 658787667310523, 661933458000000]
private def phb_m8_r384_7_p1 : List ℕ :=
  [665006623130037, 668008463426654, 670940233311862, 673803143251712, 676598361951787,
    679327018412121, 681990203852471, 684588973517836, 687124348373259, 689597316696139,
    692008835573569, 694359832311574, 696651205762532, 698883827576550, 701058543382079,
    703176173900620, 705237516000000, 707243343690326, 709194409066407, 711091443200132,
    712935156986053, 714726241943135, 716465370975458, 718153199094402, 719790364104711,
    721377487256617, 722915173866079, 724404013905028, 725844582563384, 727237440784495,
    728583135775517, 729882201494180, 731135159113253, 732342517463968, 733504773459560,
    734622412500000, 735695908858956, 736725726053924, 737712317200422, 738656125351080,
    739557583820431, 740417116496106, 741235138137164, 742012054660176, 742748263413694,
    743444153441678, 744100105736416, 744716493481460, 745293682285048, 745832030404477,
    746331888961848, 746793602151599, 747217507440190, 747603935758322, 747953211686022,
    748265653630915, 748541574000000, 748781279365201, 748985070622998, 749153243148364,
    749286086943283, 749383886780065, 749446922339693, 749475468345405]
private def phb_m8_r384_7_p2 : List ℕ :=
  [749469794691715, 749430166569063, 749356844584279, 749250084877024, 749110139232381,
    748937255189756, 748731676148214, 748493641468429, 748223386571348, 747921143033717,
    747587138680588, 747221597674921, 746824740604399, 746396784565550, 745937943245294,
    745448427000000, 744928442932153, 744378194964715, 743797883913269, 743187707556021,
    742547860701750, 741878535255763, 741179920283942, 740452202074944, 739695564200618,
    738910187574706, 738096250509884, 737253928773201, 736383395639979, 735484821946213,
    734558376139530, 733604224328763, 732622530332164, 731613455724333, 730577159881873,
    729513800027839, 728423531275005, 727306506667993, 726162877224303, 724992791974270,
    723796398000000, 722573840473291, 721325262692606, 720050806119085, 718750610411670,
    717424813461337, 716073551424481, 714696958755469, 713295168238396, 711868311018063,
    710416516630199, 708939913030953, 707438626625676, 705912782297016, 704362503432341,
    702787911950518, 701189128328058, 699566271624654, 697919459508120, 696248808278756,
    694554432893153, 692836446987451, 691094962900071, 689330091693930]
private def phb_m8_r384_7_p3 : List ℕ :=
  [687541943178155, 685730625929315, 683896247312176, 682038913500000, 680158729494391,
    678255799144713, 676330225167081, 674382109162937, 672411551637233, 670418652016213,
    668403508664829, 666366218903771, 664306879026150, 662225584313826, 660122429053387,
    657997506551809, 655850909151778, 653682728246707, 651493054295435, 649281976836636,
    647049584502925, 644795965034688, 642521205293627, 640225391276037, 637908608125817,
    635570940147227, 633212470817383, 630833282798523, 628433457950013, 626013077340139,
    623572221257655, 621110969223117, 618629400000000, 616127591605594, 613605621321704,
    611063565705140, 608501500598011, 605919501137827, 603317641767412, 600695996244632,
    598054637651943, 595393638405764, 592713070265679, 590013004343466, 587293511111970,
    584554660413805, 581796521469913, 579019162887952, 576222652670551, 573407058223406,
    570572446363240, 567718883325618, 564846434772629, 561955165800427, 559045140946650,
    556116424197702, 553169078995911, 550203168246572, 547218754324854, 544215899082606,
    541194663855033, 538155109467270, 535097296240839, 532021284000000]
private def phb_m8_r384_7_p4 : List ℕ :=
  [528927132077992, 525814899323181, 522684644105089, 519536424320341, 516370297398503,
    513186320307827, 509984549560902, 506765041220220, 503527850903640, 500273033789770,
    497000644623269, 493710737720049, 490403366972411, 487078585854086, 483736447425204,
    480377004337183, 477000308837538, 473606412774621, 470195367602282, 466767224384461,
    463322033799705, 459859846145621, 456380711343256, 452884678941414, 449371798120901,
    445842117698715, 442295686132164, 438732551522927, 435152761621052, 431556363828894,
    427943405205000, 424313932467924, 420667992000000, 417005629851048, 413326891742035,
    409631823068674, 405920468904973, 402192874006741, 398449082815027, 394689139459526,
    390913087761925, 387120971239204, 383312833106893, 379488716282280, 375648663387571,
    371792716753014, 367920918419966, 364033310143932, 360129933397547, 356210829373529,
    352276038987583, 348325602881266, 344359561424815, 340377954719937, 336380822602556,
    332368204645525, 328340140161306, 324296668204602, 320237827574966, 316163656819369,
    312074194234731, 307969477870424, 303849545530737, 299714434777313]
private def phb_m8_r384_7_p5 : List ℕ :=
  [295564182931546, 291398827076955, 287218404061522, 283022950500000, 278812502776190,
    274587097045192, 270346769235623, 266091555051806, 261821489975933, 257536609270203,
    253236947978923, 248922540930593, 244593422739956, 240249627810029, 235891190334102,
    231518144297717, 227130523480618, 222728361458678, 218311691605804, 213880547095815,
    209434960904299, 204974965810445, 200500594398854, 196011879061328, 191508851998633,
    186991545222249, 182459990556088, 177914219638201, 173354263922454, 168780154680194,
    164191923001892, 159589599798756, 154973215804342, 150342801576135, 145698387497108,
    141040003777274, 136367680455211, 131681447399570, 126981334310568, 122267370721460,
    117539586000000, 112798009349874, 108042669812131, 103273596266582, 98490817433195,
    93694361873468, 88884257991784, 84060534036760, 79223218102570, 74372338130258,
    69507921909034, 64629997077561, 59738591125219, 54833731393360, 49915445076547,
    44983759223783, 40038700739718, 35080296385851, 30108572781717, 25123556406052,
    20125273597960, 15113750558056, 10089013349599, 5051087899613]
private def phb_m8_r384_7 : List ℕ :=
  pCat phb_m8_r384_7_p0
    (pCat phb_m8_r384_7_p1
    (pCat phb_m8_r384_7_p2
    (pCat phb_m8_r384_7_p3
    (pCat phb_m8_r384_7_p4
      phb_m8_r384_7_p5))))
private def pvn_m8_r384_7_0_p0 : List ℕ :=
  [2015831846610328, 1989484457754741, 2013171603421515, 2017295050933197, 1987971716019064,
    1969911162452848, 1979553580289849, 2001450899888725, 2019657829009818, 2033583611497679,
    2047697970468113, 2057666223074100, 2055274592350504, 2041787934709067, 2029472940343482,
    2031101249847558, 2049739156800526, 2076076307937881, 2093542015480051, 2088220397251736,
    2057946368322563, 2014618231278506, 1978236858708486, 1966861152516156, 1988369991661190,
    2037457622075629, 2098067950408219, 2149607180624954, 2174481946628304, 2164237423467563,
    2122090549227060, 2061173573088832, 2000360716164310, 1954862731167128, 1938833419501893,
    1955862627195970, 2002669708493395, 2070234126501064, 2146560851101396, 2219546099978109,
    2279305264801605, 2319573216718419, 2338073035134504, 2336013471488908, 2317047987830931,
    2286070315520183, 2248148635456064, 2207767891233477, 2168418436753849, 2132478622939043,
    2101298979849326, 2075395145299891, 2054677052467949, 2038667475190033, 2026685041107608,
    2017982438316744, 1988159729217393, 2007622413448679, 2004801185898938, 2002961179230367,
    2001789805346654, 2001061122229798, 2000617678095717, 2000353373442398]
private def pvn_m8_r384_7_0_p1 : List ℕ :=
  [1999801102506165, 2000110255036439, 2000060253344740, 2000032493330471, 2000017306800246,
    2000009111183209, 2000004743789205, 2000002443673529, 1999998754307528, 2000000628371794,
    2000000313589274, 2000000154764984, 2000000075497202, 2000000036382715, 2000000017311494,
    2000000008129344, 2000000003766383, 2000000001721412, 2000000000776182, 2000000000345363,
    2000000000151707, 2000000000065826, 2000000000028230, 2000000000011971, 2000000000005022,
    2000000000002084, 2000000000000852, 2000000000000343, 2000000000000134, 2000000000000049,
    2000000000000015, 2000000000000004]
private def pvn_m8_r384_7_0 : List ℕ :=
  pCat pvn_m8_r384_7_0_p0
      pvn_m8_r384_7_0_p1
private def pvn_m8_r384_7_1_p0 : List ℕ :=
  [2005652371608121, 2011932223492234, 2014542656509126, 2010497193726505, 2001769913248095,
    1993883523385940, 1991946979649983, 1997387879091405, 2007162350082639, 2015552835263316,
    2017530891712137, 2011725922230603, 2001080496686282, 1990540111881691, 1984072361373549,
    1982154833832934, 1983801146518355, 1986266998984679, 1990428593223817, 1995935092689299,
    2005023880372163, 2017442158421761, 2030775423098498, 2042549754956239, 2048964875805764,
    2047470328145106, 2039201907497259, 2027783494654355, 2018079425694352, 2015713072345152,
    2023395975091484, 2041278530517144, 2061480986093538, 2082862466129573, 2088161944910410,
    2090955716104407, 2062785056785129, 2044442883768443, 2000578506589064, 1979446052040344,
    1964984712046251, 1962657940351493, 1993872790329311, 2027858575053434, 2068998771737472,
    2119183926362850, 2146767015477909, 2155010402686639, 2153385353020191, 2126392904402647,
    2079105231565942, 2034560526097693, 1995713109804798, 1959256544592439, 1938745077103647,
    1945991438219626, 1973528587781926, 2010440384779828, 2057414534787692, 2116266746032183,
    2177631397265717, 2228177231520309, 2263559639332682, 2287933429925677]
private def pvn_m8_r384_7_1_p1 : List ℕ :=
  [2304110217485395, 2309352911678635, 2300211233954499, 2278018561520617, 2248631296824815,
    2218149802817456, 2189622940253381, 2163008805119078, 2137148804040185, 2111565766198539,
    2086992089058132, 2064839511741705, 2046362796087528, 2032112160633394, 2021858548199347,
    2014856133491565, 2010199067692649, 2007089580092646, 2004954412082248, 2003439227282861,
    2002344930589140, 2001559133721282, 2001008683156387, 2000636304149448, 2000393423236148,
    2000239973459647, 2000145248054655, 2000087536861115, 2000052541395048, 2000031330508020,
    2000018491440000, 2000010765626208, 2000006170609177, 2000003481878795, 2000001937512251,
    2000001066390719, 2000000582558740, 2000000316861589, 2000000171945791, 2000000093143920,
    2000000050326063, 2000000027070966, 2000000014463989, 2000000007658938, 2000000004011737,
    2000000002075846, 2000000001060234, 2000000000534311, 2000000000265680, 2000000000130376,
    2000000000063160, 2000000000030216, 2000000000014280, 2000000000006667, 2000000000003075,
    2000000000001399, 2000000000000625, 2000000000000273, 2000000000000115, 2000000000000044,
    2000000000000015, 2000000000000004]
private def pvn_m8_r384_7_1 : List ℕ :=
  pCat pvn_m8_r384_7_1_p0
      pvn_m8_r384_7_1_p1
private def pvn_m8_r384_7_2_p0 : List ℕ :=
  [2000020886021736, 2000199582400396, 2000776952120105, 2002015595022462, 2004086572938883,
    2006693307749129, 2009512999378349, 2011200831718841, 2011784440851088, 2009663185101094,
    2006132895401386, 2001166143295102, 1996121303774132, 1993088993461078, 1992558556002925,
    1995289518929816, 2000735836700354, 2007768777902242, 2012103465603771, 2016621509947346,
    2012481366659191, 2013240993156670, 1999596625604281, 2002607121791161, 1987802351841132,
    1992190970965858, 1986420538632700, 1983714427689702, 1989638986242459, 1982858620549026,
    1986543918821026, 1992646515392051, 1991698874186194, 2003856399588762, 2016664405724838,
    2022271959464975, 2036017352653527, 2046356192062901, 2042741906802481, 2039666857663985,
    2036042052530276, 2022304486087780, 2011015734422919, 2011817683318909, 2015463952026730,
    2021173514606902, 2038408224635728, 2061794498580626, 2077365817414785, 2084421596555297,
    2087766541142688, 2081594864889260, 2059473179472630, 2028819282573465, 2001780833236100,
    1981025416762211, 1965029836075975, 1959409863178569, 1972341148474593, 2002405431412063,
    2039263347512447, 2074959157008480, 2108022737756950, 2136490081818850]
private def pvn_m8_r384_7_2_p1 : List ℕ :=
  [2153085302086298, 2150522106516769, 2129061167050389, 2096114643285243, 2059345022206616,
    2022366076502581, 1987063166408144, 1957777504049164, 1941371303244025, 1943124540668824,
    1963176357785341, 1996972862719778, 2038697082345667, 2084195657189062, 2131257764016851,
    2177957406726486, 2221208877928182, 2256923498210593, 2281482329359994, 2293242570855917,
    2293017015377724, 2283374217338171, 2267369867095011, 2247488524367641, 2225237174433133,
    2201354932555830, 2176303365129594, 2150679666372967, 2125361675170541, 2101394635395615,
    2079752220068277, 2061119391474405, 2045786710191663, 2033669719199622, 2024413643155027,
    2017526434195078, 2012494328508758, 2008857234855087, 2006242479945456, 2004367813472389,
    2003027825905276, 2002075294809535, 2001404237641665, 2000937231253687, 2000616937150948,
    2000400698081104, 2000256997461717, 2000162924020187, 2000102178779787, 2000063435352239,
    2000038998374425, 2000023743170310, 2000014314011559, 2000008543600948, 2000005048112432,
    2000002952855212, 2000001710343263, 2000000981391397, 2000000558184299, 2000000314908475,
    2000000176341204, 2000000098069383, 2000000054186796, 2000000029751321]
private def pvn_m8_r384_7_2_p2 : List ℕ :=
  [2000000016230835, 2000000008795749, 2000000004732656, 2000000002526936, 2000000001338075,
    2000000000702276, 2000000000365129, 2000000000187979, 2000000000095790, 2000000000048300,
    2000000000024092, 2000000000011883, 2000000000005795, 2000000000002790, 2000000000001323,
    2000000000000616, 2000000000000281, 2000000000000122, 2000000000000049, 2000000000000017,
    2000000000000004]
private def pvn_m8_r384_7_2 : List ℕ :=
  pCat pvn_m8_r384_7_2_p0
    (pCat pvn_m8_r384_7_2_p1
      pvn_m8_r384_7_2_p2)
private def pvn_m8_r384_7_3_p0 : List ℕ :=
  [2000025971436649, 1999915318709272, 2000140862299870, 1999820584181409, 2000049298742650,
    2000079466776623, 1999839950464822, 2000453730812652, 2000191577001351, 2002091178604163,
    2000287383163946, 2006480598305804, 2001071757002834, 2011459957892332, 2004179825560704,
    2012381639733975, 2010692973829089, 2007013517422469, 2012097145992631, 2004437116365053,
    2001322789166805, 2002325810976035, 1993561897558191, 1992300813262012, 1995928773488028,
    1992183910041623, 1995253978362126, 2004623422329082, 2006049705632148, 2008030155257083,
    2015413430471921, 2015178231387513, 2009480928874335, 2009232453755641, 2007726585323745,
    1999311594988908, 1994312278972052, 1995533209616493, 1993095522342856, 1987292351405832,
    1986894314607747, 1989324652593426, 1986697022774074, 1982750419474427, 1985017051809011,
    1990345680361739, 1992925583296233, 1996721534594927, 2007584106267243, 2021364183534924,
    2030376504319429, 2035088091657262, 2040120404689836, 2043619758391583, 2039628701174402,
    2028681492812885, 2018184548725501, 2012586777120140, 2009713388002336, 2007941450102264,
    2011266151441222, 2023952665864214, 2043417754015617, 2062117994380539]
private def pvn_m8_r384_7_3_p1 : List ℕ :=
  [2075239435400303, 2083225365678871, 2086819286756599, 2082995075726144, 2067904083850173,
    2042627303062891, 2013952197403457, 1989321698567392, 1972252302480628, 1963008614841139,
    1962351104564038, 1972925680905146, 1996521503629600, 2030639295495029, 2068439556654458,
    2102211096669063, 2126946767429882, 2141043126472729, 2144397479496493, 2136531333751200,
    2116748733697645, 2085928425746701, 2047937878041311, 2009149176228112, 1976300629542722,
    1954247153421543, 1945011008023793, 1948380415677272, 1963209863778332, 1988334560063777,
    2022588399398894, 2064204625905522, 2110286060662384, 2156875933642195, 2199677781797470,
    2235047274749726, 2260758158022173, 2276228894762655, 2282210148368258, 2280176314537324,
    2271730944685627, 2258241939973585, 2240759117061374, 2220130711287129, 2197179414747392,
    2172821282819234, 2148076052264206, 2123982743724776, 2101472399465569, 2081254313906446,
    2063753013406772, 2049106223369381, 2037212037561123, 2027802595577397, 2020521456983321,
    2014988508375401, 2010844927191159, 2007778005043213, 2005529973316970, 2003896429416905,
    2002719436179794, 2001878926245019, 2001284505045171, 2000868549591751]
private def pvn_m8_r384_7_3_p2 : List ℕ :=
  [2000580764106577, 2000384006995867, 2000251108464621, 2000162426218167, 2000103952144586,
    2000065842364673, 2000041283202762, 2000025628398148, 2000015754923700, 2000009592058563,
    2000005784382452, 2000003455449905, 2000002045119889, 2000001199444163, 2000000697247150,
    2000000401839638, 2000000229668633, 2000000130214226, 2000000073255376, 2000000040901862,
    2000000022669431, 2000000012472996, 2000000006812962, 2000000003694054, 2000000001987962,
    2000000001061597, 2000000000562398, 2000000000295485, 2000000000153926, 2000000000079473,
    2000000000040656, 2000000000020601, 2000000000010334, 2000000000005126, 2000000000002510,
    2000000000001214, 2000000000000574, 2000000000000264, 2000000000000117, 2000000000000048,
    2000000000000016, 2000000000000005]
private def pvn_m8_r384_7_3 : List ℕ :=
  pCat pvn_m8_r384_7_3_p0
    (pCat pvn_m8_r384_7_3_p1
      pvn_m8_r384_7_3_p2)
private def pvn_m8_r384_7_4_p0 : List ℕ :=
  [2000169025437390, 1999978486589146, 1999602196240289, 2000915174812134, 1998314494176708,
    2002999700792964, 1995576309364417, 2004728731582886, 1996801218653225, 2000243441799094,
    2002524193628656, 1996492833569913, 2001443219286939, 2001969275150383, 1996812592885829,
    2001277113091842, 2003067954408338, 1998505895136954, 2001648960023361, 2005737951515533,
    2002531304532578, 2003527577338250, 2009366677942687, 2008575257569148, 2006067151488337,
    2010109751154127, 2012236499987520, 2007517643581995, 2005299757011096, 2007189518162714,
    2004163436152405, 1997366900584081, 1995554532888367, 1996704556467144, 1993801573546144,
    1990579227255800, 1993912478704691, 1999911861149992, 2001862770711728, 2002770275115390,
    2008004085099414, 2013825303859812, 2013913076223858, 2010531583577382, 2009634197476461,
    2010075398780369, 2006610323310101, 2000147739947350, 1996587860429080, 1996924095022318,
    1996058453010612, 1991740220931141, 1988104422197392, 1988415560929888, 1989605632935429,
    1987374673912286, 1983219633637536, 1982346077571174, 1986230709497176, 1991347504378300,
    1995325798192588, 2000657137444983, 2010500837821252, 2023138477571788]
private def pvn_m8_r384_7_4_p1 : List ℕ :=
  [2033197726179338, 2037699549222928, 2038493781349543, 2038302804918957, 2036447366371491,
    2030170985002734, 2019471509732454, 2008793447503953, 2003355658502920, 2004740676619969,
    2010852914644393, 2019596078897130, 2031308746942479, 2047091877579336, 2065420107563107,
    2081357852367776, 2089478292943589, 2087425222102810, 2076640784797126, 2060075235729456,
    2039727449988059, 2016533705710153, 1992258948685313, 1970917728925769, 1957889506398264,
    1957300682959016, 1969881165988960, 1992944705516352, 2022205160747601, 2053737822861038,
    2084641321444719, 2112354877968110, 2133762863857584, 2145237919285344, 2143815176654851,
    2128681712531029, 2101906265662962, 2067908803044107, 2032030239772892, 1999059492503069,
    1972437528848567, 1954299386042787, 1945981062274725, 1948441083887578, 1962258146845962,
    1987248892017224, 2022030624708872, 2063882581749239, 2109067915620738, 2153517808443587,
    2193605051152510, 2226721570430543, 2251496779796830, 2267663983322717, 2275711535031574,
    2276497156144029, 2270963124871407, 2260007065833729, 2244484279977846, 2225273590746154,
    2203336195124965, 2179723668766718, 2155527133364051, 2131787716450896]
private def pvn_m8_r384_7_4_p2 : List ℕ :=
  [2109400569908494, 2089041466697509, 2071132447484936, 2055848463501923, 2043155910519508,
    2032868715984559, 2024707830823863, 2018353639173858, 2013485673812891, 2009808381159717,
    2007064628309523, 2005040048862739, 2003561513749813, 2002492483071348, 2001727193485923,
    2001184865178829, 2000804519718402, 2000540615658758, 2000359498667333, 2000236571648619,
    2000154066434627, 2000099305559014, 2000063359285027, 2000040019744840, 2000025027819812,
    2000015499320015, 2000009506002520, 2000005774746822, 2000003475144655, 2000002071934230,
    2000001224066766, 2000000716685815, 2000000415930680, 2000000239309219, 2000000136528595,
    2000000077248672, 2000000043354411, 2000000024138612, 2000000013334479, 2000000007308965,
    2000000003975253, 2000000002145338, 2000000001148737, 2000000000610236, 2000000000321564,
    2000000000168056, 2000000000087087, 2000000000044734, 2000000000022771, 2000000000011480,
    2000000000005728, 2000000000002825, 2000000000001373, 2000000000000656, 2000000000000305,
    2000000000000137, 2000000000000056, 2000000000000021, 2000000000000006, 2000000000000001]
private def pvn_m8_r384_7_4 : List ℕ :=
  pCat pvn_m8_r384_7_4_p0
    (pCat pvn_m8_r384_7_4_p1
      pvn_m8_r384_7_4_p2)
private def pwalks_m8_r384 : List RkmSegWalk := [
  ⟨uOfHb phb_m8_r384_0, bDec bZ (zPad bZ 1 pvn_m8_r192_0_0),
    bDec bZ (zPad bZ 9 pvn_m8_r384_0_1)⟩,
  ⟨uOfHb phb_m8_r384_1, bDec bZ (zPad bZ 9 pvn_m8_r384_1_0),
    bDec bZ (zPad bZ 9 pvn_m8_r384_1_1)⟩,
  ⟨uOfHb phb_m8_r384_2, bDec bZ (zPad bZ 9 pvn_m8_r384_2_0),
    bDec bZ (zPad bZ 9 pvn_m8_r384_2_1)⟩,
  ⟨uOfHb phb_m8_r384_3, bDec bZ (zPad bZ 9 pvn_m8_r384_3_0),
    bDec bZ (zPad bZ 9 pvn_m8_r384_3_1)⟩,
  ⟨uOfHb phb_m8_r384_4, bDec bZ (zPad bZ 9 pvn_m8_r384_4_0),
    bDec bZ (zPad bZ 217 pvn_m8_r384_4_1)⟩,
  ⟨uOfHb phb_m8_r384_5, bDec bZ (zPad bZ 217 pvn_m8_r384_5_0),
    bDec bZ (zPad bZ 377 pvn_m8_r384_5_1)⟩,
  ⟨uOfHb phb_m8_r384_6, bDec bZ (zPad bZ 377 pvn_m8_r384_6_0),
    bDec bZ (zPad bZ 385 pvn_m8_r384_6_2)⟩,
  ⟨uOfHb phb_m8_r384_7, bDec bZ (zPad bZ 385 pvn_m8_r384_7_0),
    bDec bZ (zPad bZ 385 pvn_m8_r384_7_4)⟩
  ]
private def phb_m8_r512_0 : List ℕ :=
  [321983935181544, 440463889500004, 520653707533006, 578761715225359, 621078811693093,
    650751502488321, 669519931617526, 678345845209889, 677673882840694, 667532238171429,
    647534718070984, 616784882000318, 573622140891735, 515008207246167, 434825025206293,
    317232313010314]
private def pvn_m8_r512_0_1 : List ℕ :=
  [2429736302046248, 2574058127533554, 2524455341760493, 2377538520552058, 2226557710272966,
    2116704087695544, 2052484765239334, 2020813003255188, 2007316185848876, 2002283518559153,
    2000631787693013, 2000154130544103, 2000032827754599, 2000006001731350, 2000000914678189,
    2000000109837362, 2000000009020253]
private def phb_m8_r512_1 : List ℕ :=
  [253601682285568, 352653708560897, 424471467984479, 481426559916829, 528369858115470,
    567810798303075, 601247263718547, 629655276929529, 653708759310988, 673891643556301,
    690560450614105, 703981576828389, 714354585175424, 721827214031378, 726505177958891,
    728458486008186, 727725261377480, 724313603801334, 718201740511294, 709336477797452,
    697629733494390, 682952642179072, 665126296554050, 643907473323842, 618966392775074,
    589851020459941, 555927045107610, 516270188215600, 469454856225556, 413082674878391,
    342500748049993, 245804419907292]
private def pvn_m8_r512_1_0 : List ℕ :=
  [1570263697953752, 1425941872466446, 1475544658239507, 1622461479447942, 1773442289727034,
    1883295912304456, 1947515234760666, 1979186996744812, 1992683814151124, 1997716481440847,
    1999368212306987, 1999845869455897, 1999967172245401, 1999993998268650, 1999999085321811,
    1999999890162638, 2000000009020253]
private def pvn_m8_r512_1_1 : List ℕ :=
  [1993701031008409, 1977764909884055, 1945646241955952, 1893822625200884, 1824318496418056,
    1745896463530420, 1672347117759779, 1618325032480647, 1594545510173291, 1604482576077915,
    1643863471641414, 1702835798303141, 1769544692928610, 1833530806911547, 1887821917280474,
    1929410332334753, 1958499644888068, 1977203978089398, 1988305345223507, 1994401608457518,
    1997502521089709, 1998963708075770, 1999601060282694, 1999857981425307, 1999953447745268,
    1999986027138080, 1999996187459725, 1999999063565899, 1999999795750549, 1999999961221636,
    1999999993792355, 1999999999209743, 1999999999930690]
private def phb_m8_r512_2 : List ℕ :=
  [180711163494092, 253311984468739, 307469169479725, 351814568082137, 389719824318114,
    422927207949504, 452478856053331, 479058030836445, 503141975999712, 525079849237792,
    545136291843796, 563517536044804, 580387920186349, 595880801568685, 610106030422550,
    623155224262745, 635105585529175, 646022725358343, 655962791506799, 664974097874886,
    673098389744802, 680371837841058, 686825827108509, 692487587638577, 697380702390088,
    701525517332992, 704939473168750, 707637373052522, 709631597228652, 710932272831612,
    711547405050166, 711482974226257, 710743002133978, 709329589561585, 707242926325634,
    704481273917759, 701040920064784, 696916103515599, 692098906292512, 686579109388937,
    680344006368584, 673378167404162, 665663143821519, 657177099956460, 647894354751869,
    637784809529880, 626813230028376, 614938338959451, 602111658254613, 588276014961163,
    573363586764852, 557293304411755, 539967335039618, 521266217511688, 501041960875420,
    479107956117268, 455223692571168, 429070572442250, 400211507551304, 368018578047464,
    331531001203412, 289137723718839, 237712239759440, 169228370285826]
private def pvn_m8_r512_2_0 : List ℕ :=
  [1993701031008409, 1977764909884055, 1945646241955952, 1893822625200884, 1824318496418056,
    1745896463530420, 1672347117759779, 1618325032480647, 1594545510173291, 1604482576077915,
    1643863471641414, 1702835798303141, 1769544692928610, 1833530806911547, 1887821917280474,
    1929410332334753, 1958499644888068, 1977203978089398, 1988305345223507, 1994401608457518,
    1997502521089709, 1998963708075770, 1999601060282694, 1999857981425307, 1999953447745268,
    2000013972861920, 2000003812540275, 2000000936434101, 2000000204249451, 1999999961221636,
    1999999993792355, 1999999999209743, 1999999999930690]
private def pvn_m8_r512_2_1 : List ℕ :=
  [2000000001504071, 1999999964437424, 1999999769191579, 1999999105752977, 1999996062047860,
    1999987882868996, 1999959561136720, 1999893926035504, 1999715976334540, 1999341400214975,
    1998521394425958, 1996945038413721, 1994034268902904, 1989010086948876, 1980880270707066,
    1968446261073484, 1950545810988935, 1926288882673032, 1895329632592862, 1858230576688558,
    1816683512370786, 1773482425148454, 1732299479086778, 1697229110306007, 1672109759454859,
    1659815718635993, 1661734035921443, 1677525840118054, 1705202996571120, 1741518199832078,
    1782584447993556, 1824552183868992, 1864168498091273, 1899118149093928, 1928130752206372,
    1950891184681939, 1967816487835707, 1979774496653453, 1987815793990249, 1992968957294712,
    1996117764267993, 1997952033807261, 1998969768993417, 1999506818186846, 1999775832982138,
    1999903475910322, 1999960717578548, 1999984925282362, 1999994558091454, 1999998156649448,
    1999999415723586, 1999999827250229, 1999999952532379, 1999999987932985, 1999999997177983,
    1999999999397348, 1999999999883650, 1999999999979982, 1999999999996997, 1999999999999621,
    1999999999999961, 1999999999999998]
private def phb_m8_r512_3_p0 : List ℕ :=
  [137551483586048, 193576494978876, 235915405453059, 271062354851012, 301545612943580,
    328668039440773, 353207167007793, 375671874018189, 396417172525575, 415702644056421,
    433725062626837, 450637916640357, 466563743105647, 481602269062716, 495835982645574,
    509334062237467, 522155219823892, 534349804719236, 545961390405120, 557027991965833,
    567583014263113, 577656000373892, 587273229521573, 596458199985163, 605232022974510,
    613613746782827, 621620625756574, 629268345163295, 636571210495623, 643542307858041,
    650193640659500, 656536246752300, 662580299326209, 668335194222344, 673809625827619,
    679011653313661, 683948758669048, 688627897721860, 693055545146831, 697237734287300,
    701180092488447, 704887872528787, 708365980646709, 711619001584190, 714651221007707,
    717466645614473, 720069021188552, 722461848834667, 724648399586384, 726631727558932,
    728414681794267, 729999916926664, 731389902780373, 732586932996497, 733593132773651,
    734410465796034, 735040740412944, 735485615125252, 735746603426861, 735825078042408,
    735722274596438, 735439294743773, 734977108785727, 734336557792210]
private def phb_m8_r512_3_p1 : List ℕ :=
  [733518355245324, 732523088215950, 731351218080839, 730003080783783, 728478886640667,
    726778719684258, 724902536540697, 722850164825529, 720621301042853, 718215507966559,
    715632211477748, 712870696827012, 709930104284418, 706809424133427, 703507490957691,
    700022977161387, 696354385654368, 692500041622711, 688458083292930, 684226451583945,
    679802878524451, 675184874294164, 670369712724980, 665354415071771, 660135731831367,
    654710122351418, 649073731926853, 643222366029037, 637151461249489, 630856052463541,
    624330735626471, 617569625501216, 610566307477475, 603313782469884, 595804403668989,
    588029803650915, 579980810014063, 571647347282564, 563018322267524, 554081489368784,
    544823291377215, 535228670123509, 525280839705481, 514961012855319, 504248068053169,
    493118140915698, 481544117678442, 469495000465764, 456935102274270, 443823012213416,
    430110245305844, 415739450553249, 400641986408452, 384734566829344, 367914500776747,
    350052728019595, 330983257378928, 310486432732166, 288260939681449, 263873610249969,
    236660718428380, 205507036238214, 168242543046683, 119278086439073]
private def phb_m8_r512_3 : List ℕ :=
  pCat phb_m8_r512_3_p0
      phb_m8_r512_3_p1
private def pvn_m8_r512_3_0 : List ℕ :=
  [1999999998495929, 1999999964437424, 2000000230808421, 2000000894247023, 2000003937952140,
    2000012117131004, 2000040438863280, 1999893926035504, 1999715976334540, 1999341400214975,
    1998521394425958, 1996945038413721, 1994034268902904, 1989010086948876, 1980880270707066,
    1968446261073484, 1950545810988935, 1926288882673032, 1895329632592862, 1858230576688558,
    1816683512370786, 1773482425148454, 1732299479086778, 1697229110306007, 1672109759454859,
    1659815718635993, 1661734035921443, 1677525840118054, 1705202996571120, 1741518199832078,
    1782584447993556, 1824552183868992, 1864168498091273, 1899118149093928, 1928130752206372,
    1950891184681939, 1967816487835707, 1979774496653453, 1987815793990249, 1992968957294712,
    1996117764267993, 1997952033807261, 1998969768993417, 1999506818186846, 1999775832982138,
    1999903475910322, 2000039282421452, 1999984925282362, 1999994558091454, 1999998156649448,
    1999999415723586, 1999999827250229, 1999999952532379, 1999999987932985, 1999999997177983,
    1999999999397348, 1999999999883650, 1999999999979982, 2000000000003003, 1999999999999621,
    1999999999999961, 1999999999999998]
private def pvn_m8_r512_3_1_p0 : List ℕ :=
  [2000018567730372, 1999990468773130, 1999984024019917, 2000008154368947, 2000019804773960,
    1999998534248227, 1999978480086219, 1999989274083073, 2000012737639232, 2000018767907579,
    2000007024624171, 1999993835630343, 1999985311545008, 1999981310867110, 1999987166229557,
    2000004916283388, 2000023605805661, 2000030738245534, 2000028042366879, 2000024202431909,
    2000023328065704, 2000013399743564, 2000001935034529, 1999968211019696, 1999948648402794,
    1999851601550467, 1999736923827658, 1999413690917299, 1998930952503000, 1998014151435308,
    1996484352102207, 1994026448840815, 1990117398244906, 1984296720275308, 1975907716946792,
    1964227023021217, 1948707744940319, 1928895276020644, 1904613063301666, 1876223841624482,
    1844583629922587, 1811035648500838, 1777484306312188, 1746213532027481, 1719546773328943,
    1699604089872968, 1688083154779417, 1685977747580729, 1693391388467092, 1709569123918520,
    1733061972040510, 1761918312956213, 1793909632018740, 1826810286557441, 1858669433312508,
    1887988371859363, 1913778637360363, 1935537132911822, 1953179939044390, 1966952563716382,
    1977322920282064, 1984870021152535, 1990187963175842, 1993819807918827]
private def pvn_m8_r512_3_1_p1 : List ℕ :=
  [1996223808259372, 1997764672171773, 1998719599079815, 1999290901824631, 1999620441542159,
    1999803591166891, 1999901670497297, 1999952315742885, 1999977566029140, 1999989742878173,
    1999995434552976, 1999998018670727, 1999999160571219, 1999999652529660, 1999999859425864,
    1999999944422847, 1999999978537826, 1999999991910875, 1999999997027143, 1999999998935705,
    1999999999629192, 1999999999874385, 1999999999958659, 1999999999986792, 1999999999995909,
    1999999999998774, 1999999999999648, 1999999999999904, 1999999999999976, 1999999999999995]
private def pvn_m8_r512_3_1 : List ℕ :=
  pCat pvn_m8_r512_3_1_p0
      pvn_m8_r512_3_1_p1
private def pvn_m8_r512_3_2_p0 : List ℕ :=
  [2000001773696498, 2000004994810445, 2000009650576450, 2000014018541096, 2000014966548817,
    2000009324647435, 1999998651431579, 1999985894252611, 1999985383511049, 1999985986797848,
    2000012516209114, 2000003270346950, 2000031406054085, 1999988754245093, 2000007745120887,
    1999982779262998, 1999982965031976, 2000006081100314, 1999987240481586, 2000006559118970,
    2000020478243248, 2000003120684120, 2000015152939709, 2000010349674310, 1999978118808265,
    1999982026329967, 1999992450180174, 1999980726217852, 1999991554816406, 2000012816729856,
    2000006118075821, 2000005901025924, 2000030484545784, 2000035470328262, 2000017596516330,
    2000017116362787, 2000026247387502, 2000015663514390, 2000003397397406, 2000010573505158,
    2000011445407551, 1999985487920541, 1999954093672972, 1999923244711121, 1999844074425688,
    1999654697237482, 1999303821996821, 1998696142644885, 1997639393292343, 1995853301684050,
    1992985889569555, 1988586415201943, 1982081844661023, 1972820304147457, 1960166743112373,
    1943598127759997, 1922792177572301, 1897740495367577, 1868880433663269, 1837185755764923,
    1804159398074992, 1771723189571154, 1742036556722315, 1717273177359644]
private def pvn_m8_r512_3_2_p1 : List ℕ :=
  [1699371593045018, 1689784537335400, 1689273908943208, 1697803578581195, 1714557850139324,
    1738075486295579, 1766461652702418, 1797632508828853, 1829552940826503, 1860437008058559,
    1888889210837296, 1913974439877977, 1935216866996021, 1952540833659070, 1966175670697520,
    1976548486392881, 1984184738650527, 1989628776827920, 1993388804858118, 1995904996734950,
    1997536358355793, 1998560911805378, 1999184080807351, 1999551095028186, 1999760367529892,
    1999875892893034, 1999937638046093, 1999969594053120, 1999985612642089, 1999993391984267,
    1999997053414489, 1999998724112352, 1999999463430532, 1999999780814266, 1999999913025210,
    1999999966476221, 1999999987450391, 1999999995438421, 1999999998390670, 1999999999449190,
    1999999999817227, 1999999999941248, 1999999999981724, 1999999999994506, 1999999999998409,
    1999999999999559, 1999999999999884, 1999999999999973, 1999999999999996]
private def pvn_m8_r512_3_2 : List ℕ :=
  pCat pvn_m8_r512_3_2_p0
      pvn_m8_r512_3_2_p1
private def phb_m8_r512_4_p0 : List ℕ :=
  [105655476062037, 148981583558337, 181928032084650, 209452812067680, 233482415011019,
    255007828845276, 274619473903986, 292703155345772, 309527622166132, 325289104729748,
    340136158722923, 354184520178064, 367526483739678, 380237088176413, 392378345813672,
    404002223225407, 415152796633846, 425867845480498, 436180053601946, 446117930144172,
    455706526316230, 464968000790035, 473922071121174, 482586378116644, 490976782860234,
    499107611035085, 506991855560880, 514641345937889, 522066890761591, 529278398437375,
    536284980045936, 543095037489771, 549716339421617, 556156086967825, 562420970878601,
    568517221436897, 574450652219579, 580226698614230, 585850451841910, 591326689112317,
    596659900437003, 601854312543726, 606913910267120, 611842455734694, 616643505620482,
    621320426699725, 625876409905281, 630314483059002, 634637522428038, 638848263236381,
    642949309245134, 646943141500699, 650832126337788, 654618522713609, 658304488940466,
    661892088876169, 665383297624800, 668780006794447, 672084029353379, 675297104121560,
    678420899930482, 681457019480809, 684407002924241, 687272331193349]
private def phb_m8_r512_4_p1 : List ℕ :=
  [690054429100702, 692754668226522, 695374369612226, 697914806275533, 700377205561340,
    702762751341250, 705072586073436, 707307812733479, 709469496625870, 711558667084980,
    713576319073591, 715523414686327, 717400884564749, 719209629230280, 720950520340632,
    722624401874952, 724232091252452, 725774380388949, 727252036695363, 728665804021914,
    730016403551483, 731304534645316, 732530875644036, 733696084626679, 734800800130306,
    735845641832515, 736831211199047, 737758092098497, 738626851386016, 739438039457737,
    740192190777564, 740889824377834, 741531444335247, 742117540223393, 742648587543096,
    743125048131712, 743547370552448, 743915990464710, 744231330976385, 744493802978955,
    744703805466225, 744861725837449, 744967940185547, 745022813571082, 745026700282612,
    744979944084005, 744882878449244, 744735826785245, 744539102643141, 744293009918482,
    743997843040768, 743653887152680, 743261418279378, 742820703488191, 742332001039008,
    741795560525652, 741211623008494, 740580421138562, 739902179273348, 739177113584529,
    738405432157783, 737587335084856, 736723014548045, 735812654897218]
private def phb_m8_r512_4_p2 : List ℕ :=
  [734856432719489, 733854516901647, 732807068685433, 731714241715716, 730576182081640,
    729393028350773, 728164911596276, 726891955417119, 725574275951313, 724211981882164,
    722805174437494, 721353947381779, 719858387001152, 718318572081165, 716734573877232,
    715106456077620, 713434274758860, 711718078333433, 709957907489540, 708153795122786,
    706305766259560, 704413837971867, 702478019283373, 700498311066373, 698474705929384,
    696407188095022, 694295733267822, 692140308491589, 689940871995881, 687697373031150,
    685409751692075, 683077938728523, 680701855343604, 678281412978178, 675816513081167,
    673307046864948, 670752895045064, 668153927563425, 665510003294104, 662820969730763,
    660086662654681, 657306905782258, 654481510390795, 651610274921241, 648692984556513,
    645729410773855, 642719310869612, 639662427454626, 636558487918344, 633407203859549,
    630208270481455, 626961365948721, 623666150703708, 620322266739105, 616929336823757,
    613486963678276, 609994729096689, 606452193010041, 602858892487504, 599214340670088,
    595518025631639, 591769409161240, 587967925460593, 584112979749301]
private def phb_m8_r512_4_p3 : List ℕ :=
  [580203946770269, 576240169186629, 572220955860716, 568145580004613, 564013277190660,
    559823243209044, 555574631758185, 551266551951986, 546898065626209, 542468184424163,
    537975866639517, 533420013791380, 528799466903711, 524113002457609, 519359327980994,
    514537077235550, 509644804955429, 504680981086040, 499643984464002, 494532095871015,
    489343490384560, 484076228936922, 478728248980517, 473297354141619, 467781202725740,
    462177294915523, 456482958475300, 450695332744378, 444811350662585, 438827718524840,
    432740893104784, 426547055718047, 420242082710400, 413821511750508, 407280503175725,
    400613795474886, 393815653784703, 386879810012802, 379799392862905, 372566845601662,
    365173828838266, 357611104839799, 349868398909979, 341934232019700, 333795717053384,
    325438308516233, 316845492018279, 307998394826353, 298875291493046, 289450967809517,
    279695890072200, 269575101488487, 259046727500736, 248059906045797, 236551846798090,
    224443524616962, 211633141424905, 197985756178284, 183315918697900, 167356495990775,
    149697303788291, 129647580335339, 105860024237265, 74855478762976]
private def phb_m8_r512_4 : List ℕ :=
  pCat phb_m8_r512_4_p0
    (pCat phb_m8_r512_4_p1
    (pCat phb_m8_r512_4_p2
      phb_m8_r512_4_p3))
private def pvn_m8_r512_4_0_p0 : List ℕ :=
  [1999998226303502, 2000004994810445, 1999990349423550, 2000014018541096, 2000014966548817,
    2000009324647435, 1999998651431579, 1999985894252611, 2000014616488951, 2000014013202152,
    1999987483790886, 2000003270346950, 2000031406054085, 1999988754245093, 2000007745120887,
    2000017220737002, 2000017034968024, 2000006081100314, 1999987240481586, 1999993440881030,
    1999979521756752, 2000003120684120, 1999984847060291, 1999989650325690, 2000021881191735,
    1999982026329967, 1999992450180174, 1999980726217852, 2000008445183594, 2000012816729856,
    2000006118075821, 2000005901025924, 1999969515454216, 2000035470328262, 1999982403483670,
    1999982883637213, 1999973752612498, 1999984336485610, 1999996602602594, 2000010573505158,
    1999988554592449, 2000014512079459, 2000045906327028, 2000076755288879, 2000155925574312,
    1999654697237482, 1999303821996821, 1998696142644885, 1997639393292343, 1995853301684050,
    1992985889569555, 1988586415201943, 1982081844661023, 1972820304147457, 1960166743112373,
    1943598127759997, 1922792177572301, 1897740495367577, 1868880433663269, 1837185755764923,
    1804159398074992, 1771723189571154, 1742036556722315, 1717273177359644]
private def pvn_m8_r512_4_0_p1 : List ℕ :=
  [1699371593045018, 1689784537335400, 1689273908943208, 1697803578581195, 1714557850139324,
    1738075486295579, 1766461652702418, 1797632508828853, 1829552940826503, 1860437008058559,
    1888889210837296, 1913974439877977, 1935216866996021, 1952540833659070, 1966175670697520,
    1976548486392881, 1984184738650527, 1989628776827920, 1993388804858118, 1995904996734950,
    1997536358355793, 1998560911805378, 2000815919192649, 2000448904971814, 2000239632470108,
    2000124107106966, 1999937638046093, 1999969594053120, 1999985612642089, 1999993391984267,
    1999997053414489, 1999998724112352, 1999999463430532, 1999999780814266, 1999999913025210,
    2000000033523779, 1999999987450391, 1999999995438421, 1999999998390670, 1999999999449190,
    1999999999817227, 1999999999941248, 2000000000018276, 1999999999994506, 2000000000001591,
    1999999999999559, 1999999999999884, 1999999999999973, 1999999999999996]
private def pvn_m8_r512_4_0 : List ℕ :=
  pCat pvn_m8_r512_4_0_p0
      pvn_m8_r512_4_0_p1
private def pvn_m8_r512_4_1_p0 : List ℕ :=
  [1999995264533918, 1999986147097056, 2000000447379260, 1999997680744235, 2000012887838082,
    1999998563303829, 1999986795230022, 2000019116221178, 2000002212667491, 1999977893150115,
    1999993387892457, 1999986805953076, 2000031867221185, 2000024493847957, 1999981886195528,
    2000020939376367, 1999984136329397, 2000021761788461, 1999996063380241, 2000003342998624,
    2000010881168798, 1999976416818289, 2000012659474891, 1999993403464452, 2000051775735265,
    1999937712372315, 2000057293636408, 1999969897911971, 1999988983939495, 2000054260819375,
    1999974306638006, 2000014436454510, 2000038427461562, 1999976259705650, 2000019375805536,
    2000047018749844, 1999964483459132, 1999953951930469, 2000021854028369, 2000012781345387,
    1999968914752911, 1999997148169337, 2000029446920956, 1999987754101090, 1999949292115526,
    1999989803976342, 2000041946463145, 2000017718956328, 1999954548899419, 1999949911847076,
    2000016507103673, 2000065873423056, 2000042313622190, 1999962315601365, 1999947233235548,
    1999950255254145, 2000082047937315, 1999988822156532, 2000137174458083, 1999788851808025,
    2000124511261518, 1999679920645893, 2000176276126022, 1999883361088408]
private def pvn_m8_r512_4_1_p1 : List ℕ :=
  [2000066663078289, 2000257795737158, 1999914833279321, 2000302382962179, 2000093338720802,
    1999890031065107, 2000202168408264, 1999839167380454, 1999584193375505, 1999547850034816,
    1998593318389865, 1997196268608706, 1995408483357106, 1991933249315623, 1986534997387064,
    1979292746885325, 1969036744226855, 1954916167050048, 1937231957341452, 1915988980057771,
    1890801196271834, 1862308448136230, 1832142417538681, 1801737110025578, 1772282059702507,
    1745534965060679, 1723691147332290, 1708378166014746, 1700246138212976, 1699475651224839,
    1706174255054913, 1720072066367409, 1740083677587792, 1764440151493538, 1791291152403565,
    1819159946643537, 1846929668659253, 1873593137563923, 1898151627708758, 1919772403813221,
    1938016993682422, 1952917211129918, 1964847356134361, 1974304160485079, 1981734798519283,
    1987476277536920, 1991781907663029, 1994874184928447, 1996978343159401, 1998324395484018,
    1999129408860222, 1999577489592980, 1999808622884493, 1999918613221253, 1999966704019817,
    1999986035708081, 1999993330593252, 1999996133922742, 1999997436297593, 1999998245413907,
    1999998835266906, 1999999266758859, 1999999563978027, 1999999754444988]
private def pvn_m8_r512_4_1_p2 : List ℕ :=
  [1999999868446579, 1999999932643853, 1999999966899337, 1999999984327120, 1999999992825484,
    1999999996815272, 1999999998625553, 1999999999421981, 1999999999762679, 1999999999904729,
    1999999999962563, 1999999999985591, 1999999999994565, 1999999999997993, 1999999999999278,
    1999999999999748, 1999999999999916, 1999999999999974, 1999999999999993, 1999999999999999]
private def pvn_m8_r512_4_1 : List ℕ :=
  pCat pvn_m8_r512_4_1_p0
    (pCat pvn_m8_r512_4_1_p1
      pvn_m8_r512_4_1_p2)
private def pvn_m8_r512_4_2_p0 : List ℕ :=
  [2000008043502603, 2000005455502254, 1999993181276947, 1999989498598564, 2000010930872150,
    2000002918482264, 1999956731021454, 2000015610870117, 1999994483595401, 1999988232809730,
    2000037590972735, 1999966262861164, 2000029895669857, 1999948472358444, 2000039392109619,
    2000000982288124, 2000000879539774, 2000041519005071, 1999948462966306, 1999976287244506,
    2000034729857252, 1999967471322331, 1999982897383027, 2000047760173685, 2000004633094894,
    1999981183851163, 2000024387479913, 2000007703367657, 1999976186896326, 2000016403002448,
    2000036725190924, 1999988591074015, 1999980619209267, 2000013984523066, 2000019626797331,
    1999958972993278, 2000016604936673, 1999993256960366, 2000093530962611, 1999870326996475,
    2000115256722920, 1999844887675790, 2000227351714653, 1999805559020543, 2000113687572811,
    1999950437120817, 1999973992536097, 2000157373256791, 1999815411704812, 2000132079817197,
    2000032135716860, 1999920179347090, 2000160462008944, 1999846891980645, 1999943444930592,
    2000170557684347, 1999896243500867, 2000023969310998, 2000086362061445, 1999801902183439,
    2000016128376468, 2000167370450517, 1999900340385995, 1999985784219672]
private def pvn_m8_r512_4_2_p1 : List ℕ :=
  [2000091533592464, 1999837582144854, 1999917437611584, 2000187521301750, 2000021985095635,
    1999892184573176, 2000085248028989, 2000032351355353, 1999822088508650, 1999981516781587,
    2000177846829619, 2000009854931190, 1999906361792494, 2000090755691262, 2000094831369951,
    1999840645515566, 1999813464754418, 2000029403786703, 2000044195310404, 1999887350677571,
    1999961960351292, 2000203430626100, 2000203739326810, 1999994363200829, 1999973219726204,
    2000173368537052, 2000231324977911, 2000048449551229, 1999948162616255, 2000102684357851,
    2000225725549523, 1999983834097733, 1999384879626328, 1998511140119954, 1997027469033125,
    1994192927695912, 1989314168153883, 1981983931858414, 1971845254113162, 1958320673874377,
    1940769449767602, 1918950516010690, 1893299211156229, 1864785708119709, 1834600765667440,
    1804026203701475, 1774539862357982, 1747897605083753, 1725961491885459, 1710319032721162,
    1701943447464120, 1701095334468104, 1707456766678200, 1720335156272458, 1738789252591710,
    1761655050517909, 1787553336512331, 1814966199869629, 1842399002800439, 1868570548028935,
    1892552113996383, 1913808423926949, 1932146345729123, 1947613819925273]
private def pvn_m8_r512_4_2_p2 : List ℕ :=
  [1960397111779236, 1970746561423684, 1978936955220528, 1985252259812556, 1989980094479978,
    1993405632648440, 1995801634484983, 1997416498984402, 1998464011960400, 1999117578453482,
    1999509756091654, 1999736178331024, 1999862084994584, 1999929645939669, 1999964740467095,
    1999982477548338, 1999991267174326, 1999995584618262, 1999997715561846, 1999998787385759,
    1999999342441179, 1999999639065056, 1999999801592176, 1999999891812173, 1999999941902325,
    1999999969421928, 1999999984271687, 1999999992105493, 1999999996135551, 1999999998155114,
    1999999999140754, 1999999999609369, 1999999999826543, 1999999999924722, 1999999999968052,
    1999999999986735, 1999999999994609, 1999999999997857, 1999999999999170, 1999999999999688,
    1999999999999887, 1999999999999963, 1999999999999990, 1999999999999999]
private def pvn_m8_r512_4_2 : List ℕ :=
  pCat pvn_m8_r512_4_2_p0
    (pCat pvn_m8_r512_4_2_p1
      pvn_m8_r512_4_2_p2)
private def pvn_m8_r512_4_3_p0 : List ℕ :=
  [1999998938292827, 2000009086288640, 1999988178753239, 2000003308502502, 2000061694492095,
    1999938566731848, 2000019459732846, 1999993905707673, 1999988437034536, 2000035472339802,
    1999980822368051, 1999981059774451, 2000029663614017, 1999980757972569, 1999956571853930,
    2000016954328488, 2000013348553704, 1999966709694117, 2000007427126582, 2000042620513926,
    2000001025021767, 1999937788458018, 2000022423404595, 1999981534122658, 2000067673402094,
    1999885600136155, 2000164532541315, 1999856632322290, 2000169696190655, 1999815814923948,
    2000113613158293, 1999982295397981, 1999894339094973, 2000119946035898, 1999863828382423,
    2000117310319753, 2000025168730942, 1999853884902287, 2000151682083857, 1999954070361250,
    1999954411211813, 2000121359510607, 1999873553654205, 2000027437346033, 2000157013750654,
    1999867232595745, 1999987054957537, 2000095937483577, 1999888653435110, 2000037390926874,
    2000118469294073, 1999863501431386, 1999975426486204, 2000150900496019, 1999933903770267,
    1999927490837362, 2000113986650810, 1999971308490324, 1999905589213995, 2000121480985236,
    2000051965881041, 1999837109996644, 1999989494512123, 2000142779358801]
private def pvn_m8_r512_4_3_p1 : List ℕ :=
  [1999983607064834, 1999957704827339, 2000114570048638, 2000015083133998, 1999844716524506,
    2000003618932487, 2000168313285491, 2000005323037338, 1999878057916548, 2000015509942951,
    2000060110503059, 1999911009626443, 1999934590111322, 2000132737814762, 2000107473741700,
    1999883487317868, 1999865932961970, 2000049526813236, 2000068859613806, 1999924896998293,
    1999943838342885, 2000113199446564, 2000105226119951, 1999906824610451, 1999851270520017,
    2000018468317263, 2000110157351072, 1999990643490296, 1999909453563989, 2000042781626588,
    2000178237776975, 2000071576827207, 1999854039892085, 1999823727927524, 1999983657494029,
    2000061640653986, 1999946951581802, 1999849725106084, 1999963126838104, 2000165546104573,
    2000199994118916, 2000044408234965, 1999935040239006, 2000029783133795, 2000195316665850,
    2000199968135312, 2000034760331038, 1999936957680613, 2000098677130656, 2000432516837130,
    2000658724428125, 2000562772600489, 2000079700774244, 1999091462772278, 1997164498644461,
    1993514791219719, 1987238025818746, 1977588068561600, 1964088295391050, 1946473198046451,
    1924633555505833, 1898708062778292, 1869287009678544, 1837558264661765]
private def pvn_m8_r512_4_3_p2 : List ℕ :=
  [1805252122018427, 1774386362254525, 1746940328676611, 1724601774060755, 1708646164870624,
    1699910699986193, 1698788473497203, 1705201649446326, 1718571559100861, 1737836348430316,
    1761552959666958, 1788076948867243, 1815774036091705, 1843204823020683, 1869240746886026,
    1893100418657750, 1914322867472893, 1932707004119018, 1948244352746808, 1961061284834071,
    1971375414320414, 1979463444649271, 1985635637683172, 1990213515938127, 1993509945253197,
    1995812568035173, 1997372021484802, 1998395752449904, 1999047186466666, 1999449108870853,
    1999689670874030, 1999829459295971, 1999908411387285, 1999951819449232, 1999975099328457,
    1999987310562214, 1999993596844009, 1999996786244581, 1999998388824296, 1999999190455731,
    1999999591583389, 1999999793120049, 1999999894973800, 1999999946729888, 1999999973107186,
    1999999986538275, 1999999993341260, 1999999996754456, 1999999998444583, 1999999999268210,
    1999999999662376, 1999999999847355, 1999999999932398, 1999999999970683, 1999999999987555,
    1999999999994830, 1999999999997901, 1999999999999171, 1999999999999684, 1999999999999885,
    1999999999999963, 1999999999999989, 1999999999999998]
private def pvn_m8_r512_4_3 : List ℕ :=
  pCat pvn_m8_r512_4_3_p0
    (pCat pvn_m8_r512_4_3_p1
      pvn_m8_r512_4_3_p2)
private def pvn_m8_r512_4_4_p0 : List ℕ :=
  [2000010796634665, 1999947517390539, 2000044984398093, 2000033009189256, 1999954913403194,
    1999979527861015, 2000025878779538, 2000003108010725, 1999997762734722, 2000028197140800,
    2000030841729780, 1999953017375880, 2000006709998142, 1999964523341536, 2000112646296608,
    1999847714715902, 2000139533447773, 1999847433328942, 2000187020904878, 1999891253977459,
    1999968349374640, 2000099999782716, 1999877042458330, 2000116834624651, 1999920152204710,
    1999898529073963, 2000160516873369, 1999915618384222, 1999988115800572, 2000106308875727,
    1999880548695037, 2000043421208695, 2000079567656009, 1999838254635238, 2000035573163254,
    2000110363174674, 1999886782963564, 2000023465142446, 2000092011839974, 1999899287650281,
    2000032356585451, 2000126473878260, 1999879467950135, 1999921595604835, 2000123799145083,
    1999971767376313, 1999902137392660, 2000084453594433, 2000014603808312, 1999889632342168,
    2000072127728192, 2000113006484660, 1999885876616846, 1999921912934847, 2000120427487145,
    2000027106118681, 1999912921778578, 2000056492259611, 2000080485450599, 1999903986429399,
    1999948326500479, 2000127529578212, 2000032304318167, 1999866504397515]
private def pvn_m8_r512_4_4_p1 : List ℕ :=
  [1999987621448361, 2000124196990522, 1999996959418406, 1999907114715403, 2000038730960557,
    2000073905088353, 1999922834521856, 1999927922478370, 2000113879185651, 2000108894680602,
    1999903864774129, 1999875264900190, 2000048136965354, 2000084665828968, 1999961266457501,
    1999968968769004, 2000099723928767, 2000067764528371, 1999896769429012, 1999901127611295,
    2000094369522459, 2000150050049175, 1999982530692424, 1999881749242540, 1999989060083228,
    2000075889624814, 1999983556687796, 1999902393036485, 2000010286927646, 2000139723592432,
    2000060162830277, 1999877196486862, 1999866454580858, 2000029245778670, 2000103237405321,
    1999990331589669, 1999899466643181, 1999994441177988, 2000127508023970, 2000074332059931,
    1999888771390841, 1999829225686930, 1999979045670652, 2000132001747832, 2000096395360619,
    1999959580242344, 1999940938436867, 2000067252461748, 2000138020151108, 2000015867868468,
    1999826318237657, 1999795481278697, 1999953823704705, 2000100487426520, 2000064591610833,
    1999918705794836, 1999879228710066, 2000031580013169, 2000223284766110, 2000245169306847,
    2000073349814628, 1999890171419851, 1999875342131067, 2000017830722566]
private def pvn_m8_r512_4_4_p2 : List ℕ :=
  [2000156790892637, 2000192099258663, 2000222632978967, 2000456539903818, 2000974751157944,
    2001561425071564, 2001726757896476, 2000855178390264, 1998314930821044, 1993442114066792,
    1985466520782179, 1973523197233160, 1956828901016692, 1934965709391665, 1908125769194636,
    1877194986557594, 1843654995379849, 1809376078201963, 1776397451841346, 1746748548170060,
    1722305393254310, 1704648761741365, 1694908426863095, 1693617096631577, 1700623744474670,
    1715109425026921, 1735714702740363, 1760748116485075, 1788420911514821, 1817053497639002,
    1845218608010095, 1871812198563767, 1896063832402480, 1917507840671245, 1935935770470347,
    1951344171883486, 1963884610127582, 1973817945292250, 1981473033287530, 1987210106002199,
    1991389791231844, 1994349040131506, 1996384828688071, 1997745604881082, 1998629485826819,
    1999187522649371, 1999530101803339, 1999734706003651, 1999853669758011, 1999921064371836,
    1999958303122971, 1999978397450497, 1999989002813405, 1999994487433544, 1999997272708435,
    1999998665059979, 1999999352037238, 1999999687490719, 1999999850022114, 1999999928327713,
    1999999965897228, 1999999983857782, 1999999992410261, 1999999996461933]
private def pvn_m8_r512_4_4_p3 : List ℕ :=
  [1999999998368088, 1999999999256726, 1999999999666326, 1999999999852593, 1999999999936009,
    1999999999972733, 1999999999988610, 1999999999995343, 1999999999998140, 1999999999999278,
    1999999999999731, 1999999999999905, 1999999999999969, 1999999999999993, 1999999999999999]
private def pvn_m8_r512_4_4 : List ℕ :=
  pCat pvn_m8_r512_4_4_p0
    (pCat pvn_m8_r512_4_4_p1
    (pCat pvn_m8_r512_4_4_p2
      pvn_m8_r512_4_4_p3))
private def phb_m8_r512_5_p0 : List ℕ :=
  [85854078923776, 121178862168587, 148122753191082, 170702055360164, 190475747583107,
    208244987597348, 224486644897751, 239512036771571, 253537826821776, 266722072685429,
    279184325759542, 291017644504832, 302296175554107, 313080151848281, 323419308793221,
    333355290821224, 342923390924317, 352153836243350, 361072756711397, 369702927395559,
    378064346037786, 386174688459255, 394049672017061, 401703348856424, 409148344871120,
    416396056187761, 423456812063918, 430340010969997, 437054235067822, 443607347141093,
    450006573162228, 456258573018320, 462369501411048, 468345060551949, 474190545967203,
    479910886484076, 485510679279269, 490994220716056, 496365533573815, 501628391173789,
    506786338823732, 511842712937606, 516800658131874, 521663142554682, 526432971666699,
    531112800661015, 535705145683266, 540212393991006, 544636813172704, 548980559530879,
    553245685720445, 557434147721775, 561547811218171, 565588457438953, 569557788522028,
    573457432443544, 577288947556704, 581053826777083, 584753501447641, 588389344912968,
    591962675829175, 595474761232991, 598926819391233, 602320022449616]
private def phb_m8_r512_5_p1 : List ℕ :=
  [605655498897967, 608934335867220, 612157581272065, 615326245811778, 618441304840601,
    621503700117935, 624514341447713, 627474108215424, 630383850830532, 633244392081348,
    636056528408766, 638821031104779, 641538647441133, 644210101733062, 646836096342636,
    649417312625870, 651954411827424, 654448035926396, 656898808436483, 659307335163457,
    661674204922752, 663999990219697, 666285247894760, 668530519735982, 670736333060641,
    672903201268011, 675031624364966, 677122089466052, 679175071269533, 681191032510815,
    683170424394554, 685113687006662, 687021249707365, 688893531506351, 690730941421019,
    692533878818740, 694302733744016, 696037887231333, 697739711604475, 699408570763017,
    701044820456654, 702648808548011, 704220875264513, 705761353439863, 707270568745674,
    708748839913714, 710196478949258, 711613791335953, 713001076232630, 714358626662433,
    715686729694642, 716985666619526, 718255713116560, 719497139416303, 720710210456238,
    721895186030848, 723052320936176, 724181865109134, 725284063761785, 726359157510816,
    727407382502419, 728428970532774, 729424149164331, 730393141838059]
private def phb_m8_r512_5_p2 : List ℕ :=
  [731336167981840, 732253443115166, 733145178950300, 734011583490039, 734852861122219,
    735669212711103, 736460835685768, 737227924125615, 737970668843120, 738689257463928,
    739383874504403, 740054701446722, 740701916811621, 741325696228867, 741926212505563,
    742503635692344, 743058133147568, 743589869599556, 744099007206967, 744585705617366,
    745050122024064, 745492411221278, 745912725657682, 746311215488406, 746688028625529,
    747043310787131, 747377205544950, 747689854370683, 747981396681000, 748251969881290,
    748501709408206, 748730748771026, 748939219591890, 749127251644945, 749294972894422,
    749442509531705, 749569986011396, 749677525086436, 749765247842291, 749833273730251,
    749881720599856, 749910704730484, 749920340862132, 749910742225400, 749882020570722,
    749834286196855, 749767647978654, 749682213394149, 749578088550957, 749455378212036,
    749314185820812, 749154613525687, 748976762203960, 748780731485167, 748566619773858,
    748334524271837, 748084540999871, 747816764818889, 747531289450682, 747228207498118,
    746907610464895, 746569588774833, 746214231790722, 745841627832744]
private def phb_m8_r512_5_p3 : List ℕ :=
  [745451864196475, 745045027170479, 744621202053509, 744180473171324, 743722923893127,
    743248636647650, 742757692938873, 742250173361405, 741726157615533, 741185724521940,
    740628952036109, 740055917262414, 739466696467916, 738861365095862, 738239997778902,
    737602668352023, 736949449865220, 736280414595899, 735595634061020, 734895179028998,
    734179119531351, 733447524874119, 732700463649044, 731938003744527, 731160212356365,
    730367155998272, 729558900512191, 728735511078403, 727897052225430, 727043587839753,
    726175181175334, 725291894862951, 724393790919360, 723480930756268, 722553375189150,
    721611184445880, 720654418175211, 719683135455087, 718697394800805, 717697254173013,
    716682770985571, 715654002113258, 714611003899336, 713553832162980, 712482542206566,
    711397188822829, 710297826301888, 709184508438147, 708057288537072, 706916219421836,
    705761353439863, 704592742469240, 703410437925019, 702214490765416, 701004951497887,
    699781870185111, 698545296450859, 697295279485764, 696031868052996, 694755110493830,
    693465054733126, 692161748284712, 690845238256678, 689515571356576]
private def phb_m8_r512_5_p4 : List ℕ :=
  [688172793896532, 686816951798284, 685448090598114, 684066255451721, 682671491138995,
    681263842068720, 679843352283200, 678410065462809, 676964024930462, 675505273656014,
    674033854260599, 672549809020879, 671053179873242, 669544008417924, 668022335923067,
    666488203328713, 664941651250732, 663382719984694, 661811449509672, 660227879491992,
    658632049288923, 657023997952305, 655403764232125, 653771386580040, 652126903152841,
    650470351815864, 648801770146354, 647121195436771, 645428664698050, 643724214662815,
    642007881788534, 640279702260636, 638539711995584, 636787946643885, 635024441593081,
    633249231970671, 631462352647006, 629663838238137, 627853723108617, 626032041374271,
    624198826904915, 622354113327046, 620497934026486, 618630322150991, 616751310612824,
    614860932091283, 612959219035209, 611046203665441, 609121917977246, 607186393742715,
    605239662513122, 603281755621249, 601312704183685, 599332539103087, 597341291070408,
    595338990567105, 593325667867304, 591301353039941, 589266075950875, 587219866264973,
    585162753448159, 583094766769445, 581015935302927, 578926287929760]
private def phb_m8_r512_5_p5 : List ℕ :=
  [576825853340104, 574714660035042, 572592736328476, 570460110348996, 568316810041722,
    566162863170131, 563998297317845, 561823139890410, 559637418117040, 557441159052352,
    555234389578060, 553017136404667, 550789426073120, 548551284956451, 546302739261394,
    544043815029985, 541774538141139, 539494934312203, 537205029100500, 534904847904841,
    532594415967031, 530273758373341, 527942900055975, 525601865794514, 523250680217339,
    520889367803038, 518517952881800, 516136459636786, 513744912105486, 511343334181060,
    508931749613658, 506510182011732, 504078654843324, 501637191437345, 499185814984830,
    496724548540192, 494253415022443, 491772437216418, 489281637773969, 486781039215157,
    484270663929424, 481750534176748, 479220672088796, 476681099670047, 474131838798916,
    471572911228861, 469004338589468, 466426142387541, 463838344008161, 461240964715746,
    458634025655090, 456017547852400, 453391552216309, 450756059538886, 448111090496631,
    445456665651464, 442792805451691, 440119530232973, 437436860219275, 434744815523807,
    432043416149954, 429332681992199, 426612632837028, 423883288363834]
private def phb_m8_r512_5_p6 : List ℕ :=
  [421144668145804, 418396791650800, 415639678242230, 412873347179907, 410097817620899,
    407313108620375, 404519239132435, 401716228010932, 398904094010292, 396082855786312,
    393252531896965, 390413140803184, 387564700869644, 384707230365532, 381840747465312,
    378965270249480, 376080816705311, 373187404727601, 370285052119393, 367373776592707,
    364453595769253, 361524527181139, 358586588271577, 355639796395571, 352684168820609,
    349719722727338, 346746475210241, 343764443278302, 340773643855662, 337774093782272,
    334765809814543, 331748808625978, 328723106807809, 325688720869620, 322645667239971,
    319593962267004, 316533622219057, 313464663285262, 310387101576141, 307300953124191,
    304206233884474, 301102959735188, 297991146478242, 294870809839820, 291741965470944,
    288604628948024, 285458815773413, 282304541375945, 279141821111479, 275970670263429,
    272791104043292, 269603137591172, 266406785976298, 263202064197537, 259988987183898,
    256767569795042, 253537826821776, 250299772986543, 247053422943918, 243798791281088,
    240535892518330, 237264741109490, 233985351442447, 230697737839586]
private def phb_m8_r512_5_p7 : List ℕ :=
  [227401914558254, 224097895791222, 220785695667133, 217465328250952, 214136807544412,
    210800147486455, 207455361953662, 204102464760695, 200741469660715, 197372390345813,
    193995240447429, 190610033536764, 187216783125198, 183815502664698, 180406205548219,
    176988905110109, 173563614626507, 170130347315734, 166689116338685, 163239934799218,
    159782815744535, 156317772165562, 152844816997327, 149363963119333, 145875223355928,
    142378610476669, 138874137196691, 135361816177060, 131841660025135, 128313681294923,
    124777892487424, 121234306050982, 117682934381630, 114123789823432, 110556884668818,
    106982231158924, 103399841483920, 99809727783344, 96211902146428, 92606376612421,
    88993163170908, 85372273762135, 81743720277318, 78107514558961, 74463668401163,
    70812193549929, 67153101703470, 63486404512513, 59812113580594, 56130240464360,
    52440796673860, 48743793672842, 45039242879039, 41327155664460, 37607543355671,
    33880417234082, 30145788536224, 26403668454029, 22654068135106, 18896998683013,
    15132471157529, 11360496574924, 7581085908221, 3794250087470]
private def phb_m8_r512_5 : List ℕ :=
  pCat phb_m8_r512_5_p0
    (pCat phb_m8_r512_5_p1
    (pCat phb_m8_r512_5_p2
    (pCat phb_m8_r512_5_p3
    (pCat phb_m8_r512_5_p4
    (pCat phb_m8_r512_5_p5
    (pCat phb_m8_r512_5_p6
      phb_m8_r512_5_p7))))))
private def pvn_m8_r512_5_0_p0 : List ℕ :=
  [1999989203365335, 2000052482609461, 2000044984398093, 1999966990810744, 1999954913403194,
    1999979527861015, 1999974121220462, 1999996891989275, 1999997762734722, 1999971802859200,
    1999969158270220, 1999953017375880, 2000006709998142, 2000035476658464, 1999887353703392,
    2000152285284098, 1999860466552227, 2000152566671058, 2000187020904878, 2000108746022541,
    2000031650625360, 1999900000217284, 1999877042458330, 2000116834624651, 2000079847795290,
    1999898529073963, 1999839483126631, 2000084381615778, 2000011884199428, 1999893691124273,
    2000119451304963, 1999956578791305, 1999920432343991, 2000161745364762, 1999964426836746,
    1999889636825326, 2000113217036436, 2000023465142446, 1999907988160026, 1999899287650281,
    1999967643414549, 1999873526121740, 2000120532049865, 1999921595604835, 2000123799145083,
    1999971767376313, 2000097862607340, 1999915546405567, 1999985396191688, 2000110367657832,
    1999927872271808, 1999886993515340, 1999885876616846, 2000078087065153, 1999879572512855,
    2000027106118681, 2000087078221422, 2000056492259611, 1999919514549401, 1999903986429399,
    2000051673499521, 1999872470421788, 2000032304318167, 1999866504397515]
private def pvn_m8_r512_5_0_p1 : List ℕ :=
  [2000012378551639, 2000124196990522, 1999996959418406, 2000092885284597, 2000038730960557,
    2000073905088353, 2000077165478144, 1999927922478370, 1999886120814349, 2000108894680602,
    1999903864774129, 1999875264900190, 1999951863034646, 1999915334171032, 1999961266457501,
    1999968968769004, 2000099723928767, 1999932235471629, 2000103230570988, 2000098872388705,
    2000094369522459, 1999849949950825, 2000017469307576, 1999881749242540, 1999989060083228,
    2000075889624814, 2000016443312204, 1999902393036485, 2000010286927646, 2000139723592432,
    1999939837169723, 2000122803513138, 1999866454580858, 1999970754221330, 2000103237405321,
    1999990331589669, 1999899466643181, 2000005558822012, 2000127508023970, 1999925667940069,
    2000111228609159, 1999829225686930, 2000020954329348, 1999867998252168, 2000096395360619,
    1999959580242344, 2000059061563133, 2000067252461748, 2000138020151108, 1999984132131532,
    2000173681762343, 2000204518721303, 2000046176295295, 1999899512573480, 2000064591610833,
    1999918705794836, 2000120771289934, 1999968419986831, 1999776715233890, 1999754830693153,
    1999926650185372, 1999890171419851, 2000124657868933, 1999982169277434]
private def pvn_m8_r512_5_0_p2 : List ℕ :=
  [2000156790892637, 1999807900741337, 1999777367021033, 1999543460096182, 1999025248842056,
    1998438574928436, 1998273242103524, 1999144821609736, 1998314930821044, 1993442114066792,
    1985466520782179, 1973523197233160, 1956828901016692, 1934965709391665, 1908125769194636,
    1877194986557594, 1843654995379849, 1809376078201963, 1776397451841346, 1746748548170060,
    1722305393254310, 1704648761741365, 1694908426863095, 1693617096631577, 1700623744474670,
    1715109425026921, 1735714702740363, 1760748116485075, 1788420911514821, 1817053497639002,
    1845218608010095, 1871812198563767, 1896063832402480, 1917507840671245, 1935935770470347,
    1951344171883486, 1963884610127582, 1973817945292250, 1981473033287530, 1987210106002199,
    1991389791231844, 1994349040131506, 1996384828688071, 1997745604881082, 1998629485826819,
    1999187522649371, 1999530101803339, 1999734706003651, 1999853669758011, 1999921064371836,
    2000041696877029, 2000021602549503, 2000010997186595, 2000005512566456, 2000002727291565,
    1999998665059979, 1999999352037238, 1999999687490719, 1999999850022114, 1999999928327713,
    2000000034102772, 2000000016142218, 2000000007589739, 2000000003538067]
private def pvn_m8_r512_5_0_p3 : List ℕ :=
  [2000000001631912, 1999999999256726, 1999999999666326, 1999999999852593, 1999999999936009,
    2000000000027267, 2000000000011390, 2000000000004657, 2000000000001860, 1999999999999278,
    1999999999999731, 1999999999999905, 1999999999999969, 2000000000000007, 2000000000000001]
private def pvn_m8_r512_5_0 : List ℕ :=
  pCat pvn_m8_r512_5_0_p0
    (pCat pvn_m8_r512_5_0_p1
    (pCat pvn_m8_r512_5_0_p2
      pvn_m8_r512_5_0_p3))
private def pvn_m8_r512_5_1_p0 : List ℕ :=
  [1999993364964754, 1999980630960106, 1999967308561829, 1999994228874356, 2000027015218763,
    2000079772786641, 1999947126875503, 2000161319428487, 1999867731387794, 2000043113965960,
    2000040051843438, 1999890980608214, 1999951159988555, 2000076238844773, 1999942506076259,
    1999980005691466, 2000024443114456, 1999986127914574, 1999976575710812, 1999920694100089,
    2000011912858682, 2000005288235938, 1999923263658803, 2000091727758224, 2000093670603465,
    1999695395568114, 1999927998014464, 2000117237285164, 2000246342362096, 1999960138440863,
    2000241505314662, 1999976083947128, 1999933313343557, 2000053908792263, 2000059237420395,
    2000086300065070, 1999866716243707, 2000029794817397, 1999962432765682, 2000009840452818,
    1999955718505585, 1999951587195385, 1999993404118800, 1999925374681642, 2000141810744531,
    1999942851225591, 1999964099862164, 1999954957415479, 2000053530479207, 2000099155517867,
    1999870011191403, 2000095438420062, 2000101610937493, 1999924375727146, 1999875034097212,
    1999944735340844, 1999925251347676, 2000030905082642, 1999963347805173, 1999918180951653,
    2000136851088608, 1999932571034102, 2000037381359739, 1999988104547471]
private def pvn_m8_r512_5_1_p1 : List ℕ :=
  [2000093131391838, 1999998315870013, 2000113290010232, 1999872101002235, 1999879480237388,
    1999948665238472, 2000032363256294, 1999960371346480, 1999865967361068, 2000124948273986,
    2000017474572030, 2000024000963405, 1999921910257541, 2000070252944825, 1999921557083662,
    1999893670174458, 2000088644965860, 1999807915765731, 1999967811849626, 1999980943221002,
    2000142553139316, 1999898806454730, 2000215349162735, 1999934303743218, 2000060181707708,
    2000089782587491, 2000067269569727, 1999945023518152, 2000024087688901, 1999916529561238,
    1999976214208910, 1999960854227761, 1999995754797816, 1999776129038558, 1999891798212142,
    1999963793981540, 2000184005545653, 1999985569736905, 2000021898251291, 2000029163835481,
    2000063539347264, 1999931555867965, 2000165989631901, 1999802105070505, 1999954663182852,
    2000069152019846, 1999971679406064, 1999995205168725, 1999947038422241, 2000064928080600,
    2000042925043665, 1999968900483955, 2000116475754360, 1999893366586189, 2000043045809114,
    1999982909716506, 1999869668175894, 2000113372456384, 2000048719385861, 2000024634940663,
    2000071562111347, 1999823320973638, 1999921559763417, 2000216288980859]
private def pvn_m8_r512_5_1_p2 : List ℕ :=
  [1999953587764753, 1999736946503801, 2000045860696057, 2000111989704918, 1999841156791547,
    2000012345257900, 2000406299431144, 2000200411663721, 1999714465000451, 1999849489753490,
    2000409965643731, 2000457252990537, 1999898546401982, 1999580316115436, 1999939073794368,
    2000400490466622, 2000250662641510, 1999591605640387, 1999176820464868, 1999514020173257,
    2000351005819665, 2000974509186350, 2000876625943218, 2000092203959746, 1999106759874410,
    1998418404213069, 1998386830024064, 1998998234550896, 2000190653819982, 2001565579709439,
    2002728399412707, 2002865549421518, 2001020640680291, 1996104153032059, 1987006164045972,
    1973009149643751, 1953731431020682, 1929270743576230, 1900320138071262, 1867959812356955,
    1833698908234721, 1799460404470003, 1767287964038674, 1739208007362291, 1717095649727875,
    1702342609785059, 1695680651465818, 1697223261265533, 1706468182550827, 1722335264365938,
    1743389073664995, 1768084092984047, 1794881623497786, 1822330890226373, 1849192827036430,
    1874526455965111, 1897675318278294, 1918213161964529, 1935919838911247, 1950776826346009,
    1962936665788693, 1972660175476254, 1980254406993596, 1986037133605573]
private def pvn_m8_r512_5_1_p3 : List ℕ :=
  [1990323947173609, 1993419806388297, 1995605088826358, 1997119804321548, 1998154284283740,
    1998850115750776, 1999308724755414, 1999602287312568, 1999782886437732, 1999888544559356,
    1999946740535980, 1999976615451869, 1999990744807593, 1999996805079724, 1999999102757579,
    1999999834872471, 2000000006224719, 2000000018608003, 2000000005200445, 1999999997272796,
    1999999995864527, 1999999997114520, 1999999998588007, 1999999999518523, 1999999999936712,
    2000000000062787, 2000000000069538, 2000000000045854, 2000000000024242, 2000000000011136,
    2000000000004626, 2000000000001792, 2000000000000670, 2000000000000250, 2000000000000096,
    2000000000000036, 2000000000000011, 2000000000000002]
private def pvn_m8_r512_5_1 : List ℕ :=
  pCat pvn_m8_r512_5_1_p0
    (pCat pvn_m8_r512_5_1_p1
    (pCat pvn_m8_r512_5_1_p2
      pvn_m8_r512_5_1_p3))
private def pvn_m8_r512_5_2_p0 : List ℕ :=
  [1999977174824565, 2000068508479194, 1999876600187365, 2000122764256500, 1999979932097818,
    1999897320001483, 1999993186843345, 2000066461612532, 1999929408180517, 1999924969625006,
    2000104074969992, 2000059002055506, 1999989295831111, 1999992528618557, 2000064467608463,
    1999980099244483, 2000153283812876, 1999843052861757, 2000033441302450, 1999992113648880,
    2000042997459471, 1999885869822747, 1999895264514390, 2000220431548506, 1999896993405322,
    1999892798219056, 2000016646763778, 2000135388005272, 2000030439321470, 1999779568226301,
    1999972389709023, 1999952641953395, 2000090105914236, 2000035175402220, 2000011317224007,
    2000079941089464, 1999804055505935, 1999870801622812, 1999921624252601, 2000034542326569,
    2000128624348242, 2000077274398929, 2000063072489678, 2000070043466036, 2000051408166899,
    1999934778540614, 2000257416879065, 1999966771448014, 1999960588565834, 1999983033294485,
    2000109878973582, 2000005424982077, 1999992514947106, 1999918338276051, 1999922858560988,
    2000108706737384, 1999905393456092, 1999974791530477, 1999946709087101, 2000094737385684,
    1999997119919613, 1999909630622528, 2000034055863328, 1999876873498304]
private def pvn_m8_r512_5_2_p1 : List ℕ :=
  [2000117914854140, 1999945269496541, 2000188933633360, 1999911009409913, 2000045919739199,
    1999993424041589, 2000083547820705, 1999770794336326, 1999900465292488, 2000095974967316,
    2000000993509431, 1999858462287754, 2000060783017850, 1999890016390556, 1999995230251259,
    2000040883499065, 2000117623332298, 1999934813315868, 2000110427347957, 2000005929992650,
    2000030321644653, 1999918571244397, 2000009068697188, 1999836703632321, 2000012757089352,
    1999953400309353, 2000008858997867, 2000011664997500, 1999889168085738, 2000122432856652,
    2000031856051871, 1999904563873315, 2000140894818284, 1999893712557932, 1999879732336014,
    1999920050084791, 2000006217197787, 2000035904587737, 1999857090515348, 2000012613528846,
    2000022307526224, 1999993735331175, 2000212275993626, 2000044719685196, 1999895570704538,
    2000066347173515, 2000059740696734, 2000076168246598, 2000097578008363, 1999884842942072,
    1999886220511977, 2000019471311844, 1999879105672701, 1999849084732778, 2000004603622385,
    1999947782934513, 1999937693869993, 2000129373461046, 2000070443147403, 1999899881102548,
    2000061322844542, 2000161876506742, 1999897686548084, 1999834779019544]
private def pvn_m8_r512_5_2_p2 : List ℕ :=
  [2000136659606333, 2000129153997520, 1999796955808660, 1999801100107041, 2000166128166382,
    2000173328232076, 1999917433390304, 1999901152791253, 2000153751294901, 2000074982007090,
    1999798369835944, 1999855999599238, 2000195785635562, 2000257926142111, 1999867900135020,
    1999673798491243, 2000009447191083, 2000376429694254, 2000246030375496, 1999750380457950,
    1999562320378239, 1999926626606868, 2000309061754472, 2000231935125913, 1999828372963633,
    1999614758666636, 1999903592738223, 2000376432774057, 2000479873777048, 2000122578187125,
    1999692918256309, 1999626834389406, 2000034912099633, 2000559617077614, 2000696538016098,
    2000300471985902, 1999653425617623, 1999171701079907, 1999158010669449, 1999637477494579,
    2000328507795726, 2000862866748916, 2001020926125821, 2000743014564281, 2000071417123805,
    1999171262018280, 1998318127130938, 1997814561718238, 1997943062581025, 1998928996964312,
    2000809586380835, 2003283191821390, 2005690445603440, 2007112237631493, 2006473095728026,
    2002639157133902, 1994562825591839, 1981448562971515, 1962869063272008, 1938831973445659,
    1909847709268095, 1876990819548009, 1841881341808476, 1806543206268745]
private def pvn_m8_r512_5_2_p3 : List ℕ :=
  [1773177748842896, 1743920263772774, 1720616672344087, 1704631882527906, 1696712572439916,
    1696940089822013, 1704788041438030, 1719257561559672, 1739040549639395, 1762672733807454,
    1788664464245197, 1815611587014976, 1842285848809934, 1867696889813110, 1891118597929793,
    1912081732812115, 1930343852228531, 1945849829243998, 1958691849843657, 1969071714251208,
    1977264948361576, 1983586505656270, 1988359710018832, 1991891200531563, 1994454028212074,
    1996279273550984, 1997554756591009, 1998428432482856, 1999014063668651, 1999397393041347,
    1999641837527558, 1999793347919757, 1999884429069604, 1999937434689982, 1999967249537724,
    1999983437614396, 1999991913068631, 1999996188743745, 1999998266115056, 1999999238051490,
    1999999676108040, 1999999866496976, 1999999946451486, 1999999979002531, 1999999991911557,
    1999999996928951, 1999999998852209, 1999999999582082, 1999999999855627, 1999999999955491,
    1999999999989859, 2000000000000209, 2000000000002329, 2000000000002040, 2000000000001329,
    2000000000000751, 2000000000000388, 2000000000000185, 2000000000000081, 2000000000000032,
    2000000000000010, 2000000000000002]
private def pvn_m8_r512_5_2 : List ℕ :=
  pCat pvn_m8_r512_5_2_p0
    (pCat pvn_m8_r512_5_2_p1
    (pCat pvn_m8_r512_5_2_p2
      pvn_m8_r512_5_2_p3))
private def pvn_m8_r512_5_3_p0 : List ℕ :=
  [1999854734126695, 2000062755005385, 2000073974772746, 1999981835205471, 1999925456963895,
    1999951766648776, 2000116495704501, 2000031479158252, 2000007895397683, 1999808928784898,
    2000134756632345, 1999968051546099, 1999987542814070, 2000007607424572, 1999865337775694,
    2000050943904115, 1999945613784376, 2000082774872169, 2000107626500000, 1999843287139546,
    2000023994065817, 2000074299251605, 2000136205388838, 1999959754548569, 1999864136809498,
    2000162484604349, 2000059668850396, 1999990769858266, 1999898149712086, 1999901661316468,
    2000120946692889, 2000040615839034, 1999955694078454, 1999826791721690, 2000071713534179,
    1999926039685738, 2000125430308339, 2000018846387425, 1999964904524160, 2000023562262316,
    1999935372793610, 1999856143136295, 1999878111008506, 2000178245058978, 1999999182862198,
    2000063050870600, 2000079610132977, 1999922424804843, 1999943425116782, 1999734000498138,
    2000051627246518, 1999897189602835, 2000194138059944, 1999939938845030, 2000019614263174,
    1999992521406929, 2000185427987932, 2000084644978559, 2000026241723490, 1999970794963578,
    2000082850856184, 2000053706724644, 2000090532876423, 1999903021324973]
private def pvn_m8_r512_5_3_p1 : List ℕ :=
  [2000132983948570, 1999967867016137, 1999973374624184, 2000005614251603, 2000099499394381,
    1999767741164722, 1999970972905408, 2000081018559777, 2000075658385538, 1999876624750191,
    1999991790380089, 2000037520228071, 1999913140742818, 2000031649257470, 1999951918997751,
    1999913871741294, 2000123089034907, 1999998799458889, 2000152239172696, 2000016577083179,
    1999873578958786, 2000071411823277, 1999925443208054, 1999953517195839, 2000047092555034,
    1999937134345475, 1999931982521325, 1999918926221384, 2000013518751215, 2000006218891581,
    1999853808874981, 2000043909080310, 2000123926453979, 1999946177929126, 2000077984473277,
    2000132253819632, 1999931273802767, 1999965266233973, 2000005616431279, 1999918456784851,
    2000001215209444, 2000003451242701, 1999864359722141, 1999935098211661, 2000039980918215,
    2000008204694306, 2000080270173041, 2000066367019793, 1999882030906894, 1999909623209606,
    2000131227530519, 2000013974136612, 1999844839287116, 1999902877132948, 1999975031607795,
    1999896501307213, 2000010354993945, 2000144823471162, 1999972964931944, 1999877971655351,
    2000081043073880, 2000185833313551, 1999970210814758, 1999920789239598]
private def pvn_m8_r512_5_3_p2 : List ℕ :=
  [2000189244675759, 2000190994938231, 1999889939231976, 1999839562818664, 2000069039742310,
    2000076501492739, 1999781416738434, 1999727547193801, 2000038259251434, 2000154624325168,
    1999933331553570, 1999843425109463, 2000051001253128, 2000189132316566, 2000019085060831,
    1999849198066235, 2000008669514680, 2000212231785933, 2000043919611224, 1999727408636630,
    1999763818905161, 2000131526715084, 2000328773879764, 2000074496046090, 1999709199358343,
    1999753985403563, 2000160313931379, 2000362494727597, 2000087634939296, 1999700313717573,
    1999678353468609, 2000039259839368, 2000359050434255, 2000265954274322, 1999876269762643,
    1999661783317030, 1999869086169400, 2000233072284710, 2000326413065117, 2000039635795067,
    1999655284070392, 1999551649033592, 1999854173812289, 2000307352250560, 2000498046927921,
    2000251774907034, 1999794036619448, 1999519641330657, 1999651147444502, 2000103768456259,
    2000582254260603, 2000776334942218, 2000548908682191, 2000019993935047, 1999476098655047,
    1999177250090493, 1999231970531127, 1999606805427053, 2000183273873136, 2000782484948953,
    2001184310903950, 2001187919239400, 2000690918344486, 1999737933445437]
private def pvn_m8_r512_5_3_p3 : List ℕ :=
  [1998531771614253, 1997420282951245, 1996841985202219, 1997207193914754, 1998743847388485,
    2001381509547169, 2004719639363817, 2008060955286456, 2010465503336601, 2010812529701936,
    2007892228853948, 2000544078801639, 1987827015708780, 1969188128430326, 1944601910804990,
    1914661259222853, 1880599261972504, 1844217863200652, 1807714294443016, 1773428793642367,
    1743566755603353, 1719954673286867, 1703870646641962, 1695962488776052, 1696246055343602,
    1704168434910342, 1718719631343388, 1738575443687876, 1762251758701340, 1788249527387725,
    1815173396011385, 1841814911464776, 1867199986440809, 1890606320112715, 1911558398580781,
    1929806686335779, 1945295815867008, 1958125528843338, 1968508077105796, 1976726091717715,
    1983094782530606, 1987931400243716, 1991533389933073, 1994165093505238, 1996051677739421,
    1997378386975147, 1998293196734402, 1998911275222175, 1999320119489426, 1999584660549662,
    1999751952249123, 1999855265423264, 1999917529099408, 1999954127455771, 1999975099551155,
    1999986811705314, 1999993184966427, 1999996563931838, 1999998309433099, 1999999188126879,
    1999999619300070, 1999999825613834, 1999999921926107, 1999999965816831]
private def pvn_m8_r512_5_3_p4 : List ℕ :=
  [1999999985355714, 1999999993858859, 1999999997478891, 1999999998987315, 1999999999602592,
    1999999999848120, 1999999999943800, 1999999999980078, 1999999999993370, 1999999999998016,
    1999999999999524, 1999999999999953, 2000000000000040, 2000000000000037, 2000000000000020,
    2000000000000009, 2000000000000002]
private def pvn_m8_r512_5_3 : List ℕ :=
  pCat pvn_m8_r512_5_3_p0
    (pCat pvn_m8_r512_5_3_p1
    (pCat pvn_m8_r512_5_3_p2
    (pCat pvn_m8_r512_5_3_p3
      pvn_m8_r512_5_3_p4)))
private def pvn_m8_r512_5_4_p0 : List ℕ :=
  [1999909891963656, 1999873048976147, 1999971900879759, 1999913643745627, 2000143429960667,
    1999976132618956, 2000102732715234, 2000003169712594, 1999777739020324, 2000046693859098,
    2000047505054258, 2000021060859615, 2000124278963102, 1999883986279570, 1999980899075121,
    2000039441554832, 1999920456287805, 2000051940571326, 1999992730196728, 2000043132342968,
    2000008544720388, 1999774124213860, 1999997747033026, 2000047297859780, 2000152528379999,
    1999882666944430, 1999980416417125, 1999934487572215, 2000063313257879, 2000190824873747,
    1999927312294850, 1999936177583176, 1999973796986918, 2000148133698057, 2000058155127416,
    2000015245256190, 2000051475016511, 1999753063709549, 2000156447469512, 1999976837145325,
    2000109038143837, 1999845697438148, 2000054236144266, 1999967652082227, 1999930601652086,
    1999903312967951, 2000050665661635, 2000038006121178, 2000107639658570, 1999974253571072,
    2000044132298850, 1999846144683898, 2000003569995873, 1999858394167224, 1999951191336865,
    1999982071085087, 2000175540048953, 2000076274622499, 2000101658590669, 1999858190800606,
    1999823583449050, 2000028645529613, 2000001211196382, 1999892545764290]
private def pvn_m8_r512_5_4_p1 : List ℕ :=
  [1999902304169404, 2000038446201040, 2000051891260478, 1999876851465008, 2000195924339457,
    2000122160802274, 1999896581029518, 2000093340025915, 2000048806286857, 2000113959511216,
    2000077827507652, 1999894871431403, 2000076529466308, 2000089204434139, 2000014007450119,
    2000084884364999, 1999967738143159, 1999924409624624, 1999994073273469, 1999999659237124,
    2000019069699520, 1999929592490324, 1999938901366156, 2000101854330113, 1999996531701436,
    1999916783249376, 2000067465958707, 1999939950530722, 1999806454101651, 2000036120855787,
    2000120716511026, 1999976689876787, 2000043792428379, 2000062238851511, 1999985607146897,
    2000006500071641, 2000039844990839, 1999937276762990, 1999993473059363, 2000024011090484,
    1999919781227540, 1999946616127977, 2000025608883105, 1999940397162100, 1999863868532759,
    1999987410595709, 2000006449289901, 1999942484512117, 2000088949319125, 2000157048637650,
    1999965663936548, 1999895301801652, 2000082069039707, 2000138156509132, 1999949357881820,
    1999899384755830, 1999983560113674, 1999908881673911, 1999882001516826, 2000068983609233,
    2000113178649499, 1999899090961306, 1999841529326770, 2000094772820048]
private def pvn_m8_r512_5_4_p2 : List ℕ :=
  [2000209288368100, 1999962632046525, 1999822026806474, 2000018132590491, 2000090684027785,
    1999860051904740, 1999776404780223, 2000013639287339, 2000158360694433, 1999972107622948,
    1999802668333545, 1999970926159576, 2000193264124746, 2000086795794164, 1999876032307215,
    1999971229325501, 2000216545048619, 2000197670096628, 1999961187673780, 1999884261806518,
    2000039568125406, 2000105642234915, 1999902293873062, 1999713596069753, 1999860903574256,
    2000152662376589, 2000142109194444, 1999836758711307, 1999707725577991, 1999982982815721,
    2000319436154510, 2000281957968753, 1999911428681734, 1999665874578472, 1999846274983722,
    2000213597951594, 2000288570560827, 1999973246392066, 1999674248862030, 1999768099934219,
    2000137510353057, 2000349235487495, 2000174330426642, 1999817770318601, 1999668018002821,
    1999881686691921, 2000223086497439, 2000317433755636, 2000060222003948, 1999733543407867,
    1999693957808986, 1999991142630235, 2000332923700441, 2000390329779234, 2000098822407240,
    1999695285453762, 1999509828680332, 1999699506671102, 2000121317919910, 2000443815056530,
    2000415435238785, 2000063047041390, 1999653126511436, 1999473173454040]
private def pvn_m8_r512_5_4_p3 : List ℕ :=
  [1999637378638989, 2000049101336725, 2000491060437468, 2000746430275356, 2000691369755390,
    2000340036814396, 1999831022283740, 1999361349960491, 1999107730196531, 1999177300087370,
    1999589831233875, 2000264898650244, 2001010471379666, 2001547204347262, 2001594659262857,
    2000992322053495, 1999789795680157, 1998258509692195, 1996828418982958, 1995986042655628,
    1996165753376070, 1997647486384662, 2000467359609842, 2004353022639359, 2008696892189789,
    2012572251179486, 2014790005152308, 2013996652211987, 2008820025463736, 1998063658278086,
    1980928510380460, 1957215300224718, 1927451375395659, 1892901843525590, 1855457374851568,
    1817423458890531, 1781254849459041, 1749282130139043, 1723470327203042, 1705238714958557,
    1695359377891257, 1693939847254048, 1700482449251893, 1714001899513838, 1733176058386029,
    1756504315301578, 1782453029734443, 1809575115354896, 1836598213746633, 1862481134423459,
    1886441110690825, 1907955757580667, 1926744386919139, 1942734030659238, 1956016079399322,
    1966799521289551, 1975366122869735, 1982031571694283, 1987114905747287, 1990916888632979,
    1993706678879439, 1995715342208052, 1997134451660592, 1998118086195440]
private def pvn_m8_r512_5_4_p4 : List ℕ :=
  [1998786813808253, 1999232593069658, 1999523857833202, 1999710321642151, 1999827242061332,
    1999899028716907, 1999942175236794, 1999967556503698, 1999982167832406, 1999990398685093,
    1999994935737689, 1999997383085580, 1999998675053600, 1999999342634189, 1999999680334839,
    1999999847610752, 1999999928766578, 1999999967342250, 1999999985312103, 1999999993518342,
    1999999997193159, 1999999998807237, 1999999999502702, 1999999999796665, 1999999999918535,
    1999999999968065, 1999999999987776, 1999999999995447, 1999999999998356, 1999999999999429,
    1999999999999811, 1999999999999941, 1999999999999984, 1999999999999997]
private def pvn_m8_r512_5_4 : List ℕ :=
  pCat pvn_m8_r512_5_4_p0
    (pCat pvn_m8_r512_5_4_p1
    (pCat pvn_m8_r512_5_4_p2
    (pCat pvn_m8_r512_5_4_p3
      pvn_m8_r512_5_4_p4)))
private def pvn_m8_r512_5_5_p0 : List ℕ :=
  [2000056765403449, 1999850767487152, 2000010626150744, 1999964900708426, 1999801008716489,
    1999983834930482, 2000028061342980, 1999824854498859, 2000028382364497, 2000146096635059,
    2000003202701690, 2000101433274017, 2000017149246996, 1999826655893976, 2000009670988132,
    1999892786853152, 2000099909963595, 2000021104955700, 2000048689813467, 1999982916851981,
    1999978187607458, 2000129873943106, 1999877638788004, 1999913433879593, 2000017183406737,
    2000030891604625, 2000168710763018, 1999889179934804, 2000093800122148, 1999683623655964,
    2000024553351617, 2000069957055363, 2000101629372995, 1999927900487941, 1999943485439791,
    1999929683195974, 2000034171567641, 1999998010896792, 2000191432008994, 1999937191357366,
    1999957872188174, 1999871855730450, 2000142008130089, 2000085474030610, 2000060590686852,
    1999963469745442, 2000048518974981, 1999980893872647, 1999977454430197, 2000036512692272,
    1999955355126908, 2000024880822320, 2000101230177844, 1999948880993924, 1999990127157406,
    1999902270814596, 1999930259834586, 1999986079867826, 1999962327288784, 2000132587874252,
    1999947894112455, 1999966405653434, 2000274859242384, 1999969323346225]
private def pvn_m8_r512_5_5_p1 : List ℕ :=
  [1999753872027423, 1999899489679131, 1999917891674320, 2000021401589444, 2000055505990466,
    2000027987781091, 2000129869194623, 2000015228041117, 1999887843532745, 2000007751060364,
    2000028014395101, 1999947893831359, 1999899700691655, 1999860360766325, 1999978655372595,
    2000037185240831, 1999970467015490, 2000018126949912, 2000057124446516, 1999926642353249,
    2000077432063365, 2000205817206403, 2000007539587785, 1999919102986577, 2000104559624921,
    2000080704135921, 1999971816215643, 2000100891286064, 2000103062244367, 1999974304189713,
    1999996356040162, 2000050742803063, 2000008360585275, 1999983436363201, 1999979553233811,
    1999907565894409, 1999955965495757, 2000100525942243, 2000039276863387, 1999942092481817,
    2000006762823698, 1999992511471861, 1999879283925763, 1999922545898010, 2000051879806288,
    2000012659366196, 1999937428929008, 2000052326469043, 2000111755229856, 1999966505497214,
    1999958561427855, 2000109947135078, 2000052504976577, 1999877227108350, 1999937159136621,
    2000106494710586, 2000056002298964, 1999891124715778, 1999901952766967, 1999978679719437,
    1999904747862848, 1999884330116971, 2000071751634911, 2000127482785851]
private def pvn_m8_r512_5_5_p2 : List ℕ :=
  [1999907429493218, 1999837702751145, 2000100339983468, 2000259695626320, 2000051357921813,
    1999835736760228, 1999947460765339, 2000127804669983, 2000016679635579, 1999814887708546,
    1999900185102292, 2000104821424565, 2000036166241030, 1999827187548845, 1999885651613163,
    2000145395788753, 2000191768005157, 1999967890889710, 1999837035415227, 1999976649661274,
    2000114381854145, 1999991875923586, 1999797940722993, 1999859655513531, 2000085041998574,
    2000104278697995, 1999890925799157, 1999807352975511, 2000003700153546, 2000180993504563,
    2000076351746634, 1999869134997491, 1999906545187538, 2000187625959561, 2000340329778556,
    2000123623790017, 1999781500039853, 1999744812494018, 2000047730967797, 2000263288321005,
    2000075059393382, 1999704038562294, 1999613508492177, 1999914667926681, 2000250187685942,
    2000248062105960, 1999948601192639, 1999727281025917, 1999850283677314, 2000174149743389,
    2000315374063435, 2000095908661587, 1999753773668687, 1999670078914120, 1999933816625402,
    2000252563826343, 2000290355844622, 2000024725710467, 1999743486163571, 1999732316047337,
    1999997983224927, 2000277425702757, 2000293469097432, 2000015669157133]
private def pvn_m8_r512_5_5_p3 : List ℕ :=
  [1999694467368751, 1999634482559215, 1999910965704039, 2000295926616340, 2000463110133252,
    2000272814543010, 1999876644372487, 1999574256955840, 1999575780802514, 1999864903221120,
    2000235179564710, 2000440034265143, 2000348216260766, 2000016861204462, 1999647266180768,
    1999456808952766, 1999553417099402, 1999891577790996, 2000320141348763, 2000665969389917,
    2000794830888722, 2000639061634966, 2000215140535770, 1999638946299143, 1999114302854074,
    1998871337581841, 1999069446950067, 1999714095497428, 2000632859257193, 2001521562904731,
    2002038407578403, 2001912178646201, 2001034430418874, 1999512395612614, 1997667303872991,
    1995976778020259, 1994977824600832, 1995156981632026, 1996848216418912, 2000143714902081,
    2004814169867560, 2010243535924306, 2015401619762225, 2018888410311295, 2019073456058109,
    2014324077273585, 2003283003203686, 1985135756725993, 1959808419433107, 1928053975754170,
    1891411142747106, 1852044968457917, 1812498685651398, 1775399374195555, 1743164963439913,
    1717756445578952, 1700507541488781, 1692047188071015, 1692312484083927, 1700635566525767,
    1715880009892516, 1736600970535047, 1761206671940228, 1788104453842492]
private def pvn_m8_r512_5_5_p4 : List ℕ :=
  [1815820461572509, 1843087110071884, 1868896557703877, 1892521774788764, 1913509529905281,
    1931651656050833, 1946942083341663, 1959527190358333, 1969656098820915, 1977635903125937,
    1983794896691762, 1988455027233055, 1991913361973831, 1994431392953281, 1996230545171488,
    1997492163194030, 1998360411575694, 1998946808790861, 1999335432743779, 1999588132975105,
    1999749333574169, 1999850203718456, 1999912112368268, 1999949377353213, 1999971375795007,
    1999984111343343, 1999991342114703, 1999995368469652, 1999997567499537, 1999998745604878,
    1999999364794061, 1999999684102256, 1999999845691751, 1999999925953352, 1999999965089149,
    1999999983825944, 1999999992635522, 1999999996704029, 1999999998549948, 1999999999372861,
    1999999999733364, 1999999999888571, 1999999999954238, 1999999999981537, 1999999999992688,
    1999999999997161, 1999999999998922, 1999999999999602, 1999999999999859, 1999999999999955,
    1999999999999987, 1999999999999997]
private def pvn_m8_r512_5_5 : List ℕ :=
  pCat pvn_m8_r512_5_5_p0
    (pCat pvn_m8_r512_5_5_p1
    (pCat pvn_m8_r512_5_5_p2
    (pCat pvn_m8_r512_5_5_p3
      pvn_m8_r512_5_5_p4)))
private def pvn_m8_r512_5_6_p0 : List ℕ :=
  [2000120258730879, 2000057516742297, 1999901714641842, 1999898201273361, 2000090019092354,
    2000032456961709, 1999811254308895, 1999891595358610, 2000102950351977, 1999829103561719,
    1999981869380784, 1999913291596107, 1999918720576535, 2000002456235445, 1999965574809281,
    2000139694594799, 2000079278215943, 1999998246452413, 2000166464389954, 1999783675501045,
    2000031260312380, 1999816505994706, 2000133856904892, 1999992934842982, 1999940863791513,
    1999996451060816, 2000114101347695, 1999976649565349, 2000106293361111, 1999943933003913,
    2000018936771768, 1999790430244263, 2000000268954903, 2000088339639382, 2000166959427408,
    2000001956950266, 1999937633072043, 1999912303697575, 1999921501763153, 1999978645145649,
    2000019665277951, 2000088354702585, 2000055747098847, 1999802884941102, 1999923351532691,
    2000037657665128, 2000026873126060, 2000130006069533, 1999974558735122, 1999947040845477,
    1999990722735788, 1999938084244362, 2000103503947914, 2000028601688563, 1999942744161148,
    2000165990364147, 2000034303358620, 1999905834246159, 2000108296485082, 2000003618668623,
    1999861414989215, 2000027710919425, 2000118636791101, 2000074908871108]
private def pvn_m8_r512_5_6_p1 : List ℕ :=
  [1999976716909697, 1999879761792865, 2000021824260644, 2000068009842265, 1999899765834750,
    1999845755257252, 1999975067441656, 2000022301963118, 2000100583647683, 2000093155443686,
    2000043180274766, 2000059781532045, 1999933430679822, 1999772536050653, 1999892276837032,
    2000072817793288, 1999979340794656, 1999969578984082, 2000107240262849, 2000004680615727,
    1999934575437318, 2000108518625979, 2000113520639140, 1999893578761725, 1999853678197952,
    1999984321266779, 1999972712684810, 1999926508618381, 1999982642816880, 1999958852707125,
    1999925185868083, 2000015642037412, 2000053752388304, 2000028950500096, 2000074177432123,
    2000076423191621, 1999977579960437, 1999979800459863, 2000115106058486, 2000118919971388,
    1999978574739721, 1999994565431174, 2000115734316888, 2000063523473942, 1999986698800509,
    2000071678040471, 2000073285334849, 1999909104304088, 1999884429992333, 2000034296457539,
    2000060825097517, 1999952040538262, 1999977336164973, 2000101339383241, 2000033763420515,
    1999855245228287, 1999899849325659, 2000063530346142, 2000010656728139, 1999872958079251,
    1999952202678374, 2000093133116995, 2000042446015573, 1999962680926508]
private def pvn_m8_r512_5_6_p2 : List ℕ :=
  [2000049321729526, 2000110582442908, 1999963346491839, 1999847365576239, 2000018835808729,
    2000226362576500, 2000089117712829, 1999792535975481, 1999809519472562, 2000073945491116,
    2000109080668595, 1999877257995215, 1999801286771226, 1999989823999892, 2000096177378364,
    1999969360395840, 1999890536615059, 2000048362179526, 2000203160664297, 2000089693074203,
    1999873761136508, 1999897331318013, 2000111525896266, 2000144644760680, 1999918356243050,
    1999780761829116, 1999929103373358, 2000100504408245, 2000027840663168, 1999867736478454,
    1999916625958663, 2000124880423499, 2000179163748665, 1999986125489255, 1999815794455526,
    1999907543089255, 2000115447612270, 2000110807570424, 1999869219432431, 1999732832611720,
    1999921598535381, 2000190770626496, 2000157778923163, 1999847689513821, 1999676116313021,
    1999893061150667, 2000254113066963, 2000338396496592, 2000070946909052, 1999796713813514,
    1999851251660626, 2000161683090987, 2000339706133279, 2000146225565427, 1999778915631872,
    1999640574425980, 1999863894538891, 2000163927947664, 2000187288863908, 1999924543151517,
    1999700587547427, 1999786404327452, 2000100640802166, 2000315680040936]
private def pvn_m8_r512_5_6_p3 : List ℕ :=
  [2000213243533916, 1999901867503982, 1999695312143425, 1999796058737904, 2000097811559267,
    2000293979434534, 2000184076207875, 1999875241579525, 1999676164654388, 1999790150654862,
    2000116747625592, 2000353044404309, 2000280594798154, 1999957312693069, 1999653448509849,
    1999616921464849, 1999879460349735, 2000245323008528, 2000446863242799, 2000339911527284,
    2000001471622643, 1999667909195909, 1999563848873958, 1999748679771782, 2000089411622624,
    2000366366324589, 2000419067309791, 2000227630695284, 1999896574608413, 1999583644614010,
    1999431019582384, 1999521136856136, 1999850128991585, 2000317072747800, 2000744230073140,
    2000938341378629, 2000774843165838, 2000264363561988, 1999566059849956, 1998939209047380,
    1998651587069987, 1998877474965922, 1999620525184184, 2000690805062896, 2001749808357013,
    2002412150689259, 2002368028520656, 2001482179250497, 1999840076243498, 1997739743988528,
    1995647344479622, 1994133913637421, 1993795127838661, 1995143940711999, 1998471648490182,
    2003695166569396, 2010232095812105, 2016953851515843, 2022253681351205, 2024236312584740,
    2021001908563175, 2010970994933814, 1993185667646434, 1967526677905826]
private def pvn_m8_r512_5_6_p4 : List ℕ :=
  [1934803232446954, 1896698039790191, 1855578661230279, 1814211373026682, 1775429872507058,
    1741814929953649, 1715432728821554, 1697662797195209, 1689126599842537, 1689710202676757,
    1698662167238891, 1714741803039879, 1736392111574992, 1761914457036580, 1789626588078256,
    1817991026445994, 1845706405145762, 1871759660484206, 1895441650845910, 1916332370169651,
    1934264117967997, 1949271670340119, 1961537828509425, 1971341086396024, 1979010044151873,
    1984887060618754, 1989301821715619, 1992554180782203, 1994904831746841, 1996572036253973,
    1997732621846996, 1998525673269258, 1999057645309615, 1999407955350357, 1999634418187043,
    1999778139773395, 1999867681904611, 1999922448431771, 1999955332959793, 1999974718081779,
    1999985937341269, 1999992312682440, 1999995869959736, 1999997819108021, 1999998867994890,
    1999999422388396, 1999999710239028, 1999999857075411, 1999999930675582, 1999999966930439,
    1999999984483827, 1999999992838488, 1999999996748109, 1999999998547145, 1999999999361298,
    1999999999723698, 1999999999882376, 1999999999950727, 1999999999979695, 1999999999991773,
    1999999999996724, 1999999999998721, 1999999999999513, 1999999999999822]
private def pvn_m8_r512_5_6_p5 : List ℕ := [1999999999999938, 1999999999999981, 1999999999999996]
private def pvn_m8_r512_5_6 : List ℕ :=
  pCat pvn_m8_r512_5_6_p0
    (pCat pvn_m8_r512_5_6_p1
    (pCat pvn_m8_r512_5_6_p2
    (pCat pvn_m8_r512_5_6_p3
    (pCat pvn_m8_r512_5_6_p4
      pvn_m8_r512_5_6_p5))))
private def pvn_m8_r512_5_7_p0 : List ℕ :=
  [2000030523466051, 2000059420592049, 2000131472103520, 2000086855870483, 2000025541864097,
    1999743410412355, 2000023713179067, 2000135929443944, 1999958405569114, 1999973960951827,
    1999948162456369, 1999851073881995, 2000136772542337, 1999760212274096, 2000091544754199,
    1999905757002437, 1999951494453128, 1999907238218408, 1999929560777040, 1999896087005430,
    2000084376711030, 1999863620067043, 2000106382793066, 2000101013562727, 2000168108860726,
    1999984624006181, 1999937528163542, 1999967948277962, 1999990291556397, 1999964683133410,
    1999952960780160, 2000002714005582, 2000021193376818, 1999911047265825, 2000002693881176,
    2000067348898848, 2000098172006114, 2000152953328765, 1999895412912643, 1999852421498005,
    2000002526535529, 1999922522012824, 2000021317346468, 2000119983108759, 2000060878447574,
    2000096129621943, 1999926615074934, 1999800011505455, 2000008900236179, 2000014982459557,
    1999990800067790, 2000142802973572, 1999987934673173, 1999780677733990, 1999976743563467,
    2000046637115710, 1999971476781104, 2000012612573516, 2000072563530502, 2000008764788284,
    1999973150201284, 1999935900341395, 1999997291604891, 2000089068775887]
private def pvn_m8_r512_5_7_p1 : List ℕ :=
  [1999966489024506, 1999920276372384, 2000086482939926, 2000160417036419, 2000048938028208,
    1999951865470986, 1999931147400255, 1999977170270250, 2000101747645945, 2000059303066052,
    1999903253217967, 2000006049001118, 2000133695106222, 1999999641600019, 1999939579170411,
    2000060948086493, 2000006972216903, 1999814206889124, 1999858686882061, 2000023678804855,
    2000011043637234, 2000032050221499, 2000180895750176, 2000126312257607, 1999917796049674,
    1999881803041436, 1999954080047052, 1999964271408702, 1999961551729714, 1999965594378367,
    1999937506738215, 1999955537162474, 2000065006906212, 2000109250127057, 2000020357166499,
    1999990350252717, 2000043495976531, 1999976806897655, 1999883250687623, 1999976806416432,
    2000058525509874, 1999925324341126, 1999828073776365, 1999945389087261, 2000041964150968,
    1999983778378498, 1999968691058506, 2000065418420375, 2000069201962658, 1999959911578017,
    1999985184362264, 2000134980655604, 2000111578224769, 1999945435197580, 1999964872125225,
    2000126339935143, 2000111591040951, 1999984987521626, 2000030745745151, 2000150458611992,
    2000069822954229, 1999892977273813, 1999905668305685, 2000048538019896]
private def pvn_m8_r512_5_7_p2 : List ℕ :=
  [2000052864270001, 1999945578241608, 1999972893064932, 2000097720068412, 2000052039402974,
    1999882173165786, 1999906842518751, 2000093680833847, 2000068697333119, 1999821245209101,
    1999778316840216, 2000055753193151, 2000233649799594, 2000055462498182, 1999830993898359,
    1999903898897518, 2000120305732795, 2000130593548766, 1999961097013081, 1999926598240156,
    2000076781614089, 2000120154563082, 1999946201676426, 1999835653618034, 1999976600107176,
    2000122218008776, 2000000483593839, 1999781745858059, 1999807761461175, 2000042658767043,
    2000143173825975, 1999998751801576, 1999874740313238, 1999980452938220, 2000157394110286,
    2000137095255009, 1999951901337793, 1999883656359483, 2000031114525223, 2000147272530391,
    2000010045988062, 1999780991489199, 1999790306472192, 2000044191549234, 2000196171185133,
    2000043151224436, 1999819490767160, 1999860944039427, 2000127422078419, 2000254943886467,
    2000049383668014, 1999749804559712, 1999726746502893, 2000013481825566, 2000257657761926,
    2000150110218143, 1999806913482225, 1999635521011785, 1999841571415687, 2000179426708388,
    2000255085018997, 2000004893269660, 1999760603851586, 1999836690808476]
private def pvn_m8_r512_5_7_p3 : List ℕ :=
  [2000158149212736, 2000364512187009, 2000233483312497, 1999918497655488, 1999756401854676,
    1999894128866628, 2000145140684309, 2000205984867278, 1999985974376621, 1999704723973338,
    1999661298848727, 1999917385848649, 2000226768858326, 2000287221643687, 2000050622352126,
    1999767012664578, 1999724012344214, 1999959672016335, 2000236976471307, 2000285382018982,
    2000056756476271, 1999758833840413, 1999659230168306, 1999851607918446, 2000181528799453,
    2000378651442082, 2000277489629926, 1999949596412006, 1999645999609063, 1999599222162346,
    1999844586059847, 2000200924283657, 2000416546413851, 2000354348316909, 2000073293938941,
    1999764018901374, 1999611567862405, 1999690886342700, 1999946957396346, 2000241991301283,
    2000425540692807, 2000397115753854, 2000148151441565, 1999772698088893, 1999436818828020,
    1999310922090364, 1999491184772430, 1999946616928152, 2000517935637764, 2000971586123532,
    2001090497205773, 2000768975245811, 2000073733522690, 1999239817062099, 1998593184686698,
    1998425718534541, 1998875286691364, 1999863821410274, 2001117177156883, 2002250351362916,
    2002876743114129, 2002703618154350, 2001598673302429, 1999632768938914]
private def pvn_m8_r512_5_7_p4 : List ℕ :=
  [1997105860302266, 1994548856506937, 1992679331224042, 1992289538055953, 1994065263817423,
    1998364551495121, 2005010944171772, 2013164435800222, 2021320892105952, 2027461562825643,
    2029337448447624, 2024838928596816, 2012378133955128, 1991205954719136, 1961598832991980,
    1924879018934042, 1883267921249516, 1839605830027769, 1796994303369069, 1758425569754444,
    1726456944763790, 1702971802979875, 1689047946823860, 1684934516220369, 1690123235342230,
    1703490077854793, 1723479136724498, 1748300661549259, 1776118744419326, 1805209903509465,
    1834080790495189, 1861540414331545, 1886728680378760, 1909107934693078, 1928427148522482,
    1944669336226777, 1957992078311672, 1968669151867796, 1977038851997493, 1983462147159689,
    1988291720675049, 1991851402879688, 1994424531426363, 1996249322261409, 1997519267850582,
    1998386767461618, 1998968517271571, 1999351554419631, 1999599197919140, 1999756426196929,
    1999854461840651, 1999914498559004, 1999950611203984, 1999971948630845, 1999984333694001,
    1999991396275788, 1999995353369983, 1999997531974740, 1999998710704098, 1999999337506246,
    1999999665131327, 1999999833478477, 1999999918527574, 1999999960777267]
private def pvn_m8_r512_5_7_p5 : List ℕ :=
  [1999999981417884, 1999999991335861, 1999999996023775, 1999999998203731, 1999999999201152,
    1999999999650234, 1999999999849223, 1999999999936008, 1999999999973261, 1999999999989004,
    1999999999995554, 1999999999998235, 1999999999999314, 1999999999999743, 1999999999999908,
    1999999999999969, 1999999999999992, 1999999999999999]
private def pvn_m8_r512_5_7 : List ℕ :=
  pCat pvn_m8_r512_5_7_p0
    (pCat pvn_m8_r512_5_7_p1
    (pCat pvn_m8_r512_5_7_p2
    (pCat pvn_m8_r512_5_7_p3
    (pCat pvn_m8_r512_5_7_p4
      pvn_m8_r512_5_7_p5))))
private def pvn_m8_r512_5_8_p0 : List ℕ :=
  [2000026866213426, 1999957564009601, 2000090078910847, 1999964433533162, 2000040060168597,
    2000231101393847, 2000193493448310, 1999782630392561, 2000087977310486, 1999774344096837,
    2000053617932999, 2000074700310090, 2000031718919962, 1999914499654624, 2000083236517821,
    1999856177810665, 2000034068096298, 1999927655108757, 1999929289540644, 1999968172870220,
    2000008137316400, 1999975352318319, 1999903744137885, 1999906218140025, 1999986372361856,
    1999947911455509, 1999918332824016, 1999870354002078, 1999928553285269, 2000132984457914,
    2000078892305590, 2000044682672219, 2000118274095399, 1999990442113946, 2000002534019743,
    2000037278759888, 1999872952743022, 1999965701424405, 2000103935393841, 1999960852621313,
    1999930232273646, 1999927221387272, 1999904200754026, 2000080812970079, 2000159200626500,
    1999986570044591, 2000071576225788, 2000099546448183, 1999877978062165, 1999838451016892,
    1999995544488463, 1999981038515486, 1999999246658137, 2000170534353707, 2000128224743787,
    1999959335204740, 1999878479982152, 1999895164655981, 2000008749213467, 2000069852290721,
    2000006697369144, 1999982114144611, 2000040286728671, 1999976184928568]
private def pvn_m8_r512_5_8_p1 : List ℕ :=
  [1999845734691896, 1999932909645636, 2000072008022799, 2000035963398225, 1999992727608113,
    1999981351809258, 1999960791211875, 2000045921031103, 2000104633928973, 1999941499825863,
    1999815668155896, 1999994780027477, 2000173612714557, 2000054494330367, 1999951242899950,
    2000070856087656, 2000079129313897, 1999935234408916, 1999970068590497, 2000086320968578,
    2000020770405038, 1999936658450320, 2000003831482298, 2000061331472933, 2000022355417708,
    2000024804105108, 2000084018189973, 2000047989567931, 1999925765709263, 1999864390474308,
    1999864199040131, 1999896057951353, 2000030781690915, 2000162120326391, 2000092931655895,
    1999965448952625, 2000007044327629, 2000067927421691, 1999972654315258, 1999896402617496,
    1999965216524315, 1999991144119228, 1999890469256298, 1999881031077769, 2000045676315119,
    2000134344083776, 2000024015294926, 1999951161411043, 2000038126623451, 2000064816809675,
    1999957995130086, 1999949356252772, 2000052509202839, 2000005515913547, 1999837382271499,
    1999849775491536, 2000022713340710, 2000049582621778, 1999918279710889, 1999906437755480,
    2000047624567884, 2000089536312012, 1999980650784557, 1999960367674433]
private def pvn_m8_r512_5_8_p2 : List ℕ :=
  [2000093507312668, 2000130613273292, 1999981983739152, 1999914522435028, 2000060644931195,
    2000160943799924, 2000055244086304, 1999982663960230, 2000101796142097, 2000163253907817,
    1999983625910366, 1999826699206785, 1999958025504916, 2000165052306442, 2000100192002082,
    1999863487482131, 1999845442008504, 2000090987956540, 2000218609889288, 2000024104907511,
    1999799108791082, 1999857792148950, 2000051227546077, 2000053760660023, 1999908691478991,
    1999911237353760, 2000071624973271, 2000104462591104, 1999940427458266, 1999858229995473,
    2000017126901079, 2000185766808932, 2000107470771771, 1999901433779507, 1999876085002998,
    2000062011354508, 2000172513315643, 2000034294323482, 1999840955107083, 1999858378741785,
    2000026788931235, 2000060582677827, 1999896317481999, 1999798295480026, 1999948243144259,
    2000150200592757, 2000116886742670, 1999907589194499, 1999849385508904, 2000055219431600,
    2000250370111250, 2000155597669356, 1999877136050529, 1999765783417767, 1999949255066998,
    2000165777527872, 2000110525720049, 1999840215377660, 1999711590485568, 1999923614242631,
    2000244435166939, 2000285034581098, 1999987782399590, 1999709004990938]
private def pvn_m8_r512_5_8_p3 : List ℕ :=
  [1999781711739806, 2000107236805456, 2000284423890638, 2000101810736130, 1999779797250539,
    1999688943953060, 1999912748105054, 2000171851492392, 2000164789922239, 1999909292953889,
    1999708265392030, 1999803867767807, 2000111307033067, 2000315503564453, 2000215882373476,
    1999942000822719, 1999806871058090, 1999960539056349, 2000225139044470, 2000291161177845,
    2000056025560447, 1999735712632056, 1999637364175631, 1999845264961486, 2000146112550051,
    2000251292204209, 2000075957755624, 1999805564838575, 1999707895354944, 1999882812411663,
    2000176255503738, 2000322830885758, 2000182824181200, 1999866703960917, 1999641867631246,
    1999703826867965, 2000009695698051, 2000315539484017, 2000380141640343, 2000157236242526,
    1999819870231602, 1999613672676341, 1999673276489061, 1999943229121858, 2000239729665790,
    2000382195093369, 2000297053051766, 2000042810309513, 1999764517616474, 1999614800263133,
    1999679274450310, 1999935108119657, 2000259332995244, 2000484751057635, 2000479309362853,
    2000212558114050, 1999778804824360, 1999365911445349, 1999179942978831, 1999352407141123,
    1999867115577799, 2000543722032208, 2001097365170930, 2001258569934818]
private def pvn_m8_r512_5_8_p4 : List ℕ :=
  [2000901116506931, 2000113402290782, 1999174325066321, 1998444783796900, 1998228477740519,
    1998664260139258, 1999685780436021, 2001045474109526, 2002376176378547, 2003265441004132,
    2003334526696081, 2002326199263642, 2000200671556253, 1997220520048688, 1993987865571281,
    1991395040881869, 1990468767518857, 1992121706471074, 1996861253535828, 2004529950163407,
    2014155421942820, 2023967718859618, 2031602999858789, 2034465347803324, 2030176744480534,
    2017021199968254, 1994289561901795, 1962455666439341, 1923154104214710, 1878972983842256,
    1833110271355731, 1788962266720730, 1749715760900067, 1718004306733055, 1695669305609062,
    1683644047330980, 1681958034293735, 1689842722258782, 1705909483760443, 1728366262452840,
    1755240398403857, 1784580324877926, 1814616795157143, 1843873372587055, 1871224567387908,
    1895907009098753, 1917493680250531, 1935843334338692, 1951037086283540, 1963312412378443,
    1973002155541448, 1980483266085111, 1986137415038263, 1990323586298539, 1993361386328814,
    1995523066674377, 1997032014686670, 1998065580532291, 1998760428789514, 1999219011985280,
    1999516176449914, 1999705275722440, 1999823458212584, 1999896008227090]
private def pvn_m8_r512_5_8_p5 : List ℕ :=
  [1999939759466656, 1999965680789236, 1999980770553148, 1999989402537902, 1999994255273794,
    1999996936639109, 1999998392986971, 1999999170596330, 1999999578815485, 1999999789537515,
    1999999896507252, 1999999949914042, 1999999976142159, 1999999988813513, 1999999994836529,
    1999999997653549, 1999999998950122, 1999999999537455, 1999999999799330, 1999999999914270,
    1999999999963938, 1999999999985068, 1999999999993917, 1999999999997563, 1999999999999046,
    1999999999999635, 1999999999999867, 1999999999999956, 1999999999999987, 1999999999999997]
private def pvn_m8_r512_5_8 : List ℕ :=
  pCat pvn_m8_r512_5_8_p0
    (pCat pvn_m8_r512_5_8_p1
    (pCat pvn_m8_r512_5_8_p2
    (pCat pvn_m8_r512_5_8_p3
    (pCat pvn_m8_r512_5_8_p4
      pvn_m8_r512_5_8_p5))))
private def pvn_m8_r512_5_9_p0 : List ℕ :=
  [2000081755122983, 1999946875060721, 1999992274182025, 1999958028808314, 2000248197525547,
    1999754876546280, 1999992839674558, 2000081341956872, 2000168308436356, 2000047224167949,
    2000261522921099, 1999975800396924, 1999912259902948, 1999945854505700, 1999942976577366,
    1999980366593679, 2000039266711504, 2000024474458300, 2000013403882529, 1999970023877807,
    1999996805710009, 2000036937595096, 1999932660210391, 1999928597516639, 1999959212611542,
    1999934147770342, 2000048486888317, 2000016355217909, 1999844820417907, 1999945625404996,
    2000038082034978, 1999928825377784, 1999972680990747, 1999943883698347, 1999807829411461,
    1999893464577531, 2000049098009701, 1999960893160833, 2000008992085205, 2000108121430694,
    2000058505804922, 2000083167841801, 2000109233538498, 1999936258210896, 1999862686608306,
    2000074300482615, 2000105072329327, 1999934425162793, 1999955687669000, 2000001117283396,
    1999909747542151, 1999890647139173, 1999986696792637, 2000056895585048, 2000072626357521,
    2000086574999637, 2000077174937439, 2000046054382211, 1999992065576501, 1999853476851177,
    1999805234186843, 2000004379062219, 2000152046046882, 2000074026530093]
private def pvn_m8_r512_5_9_p1 : List ℕ :=
  [2000020999790183, 2000048042197359, 1999992314377018, 1999914606340467, 1999936873008881,
    1999986689371974, 2000012467071012, 2000078985670609, 2000090448466421, 1999917535171924,
    1999815232155665, 2000003826654995, 2000131411913137, 1999949239652145, 1999832614555745,
    1999995854316437, 2000111827912097, 2000030227957234, 1999981448370838, 2000022851064144,
    1999986992756440, 1999903388981851, 1999946086127553, 2000056194975573, 2000055500043878,
    2000004588833552, 2000033515817202, 2000054991318049, 2000006288094403, 2000003975743198,
    2000045869217469, 2000015831157404, 1999977270767714, 2000015799821790, 2000013760364652,
    1999936288551785, 1999972355369183, 2000144595433632, 2000194208891550, 2000026339763685,
    1999879615171939, 1999905612777274, 1999943383384999, 1999887106114320, 1999905746058062,
    2000062944663007, 2000122320968423, 1999999002514794, 1999952531394177, 2000078942676436,
    2000119051915229, 1999977969946919, 1999897232562005, 1999962254451162, 1999969117776609,
    1999877754360597, 1999900360990900, 2000060779350214, 2000109907150030, 1999974713978811,
    1999905106481498, 2000035239372533, 2000141439817536, 2000040747881050]
private def pvn_m8_r512_5_9_p2 : List ℕ :=
  [1999916785695092, 1999972465620771, 2000052821407182, 1999955355985815, 1999837009223679,
    1999921297940488, 2000058820842628, 1999997140056054, 1999857111870748, 1999912658406266,
    2000086810210501, 2000093955989751, 1999953715511694, 1999946383352224, 2000104068738673,
    2000142612255143, 1999959674264840, 1999846565613858, 2000026057740042, 2000259269633669,
    2000196420527115, 1999937540073995, 1999883031408228, 2000094492884173, 2000206657601524,
    2000028893021502, 1999838733435318, 1999910349810786, 2000090668116052, 2000094228810516,
    1999967350751768, 1999959804452144, 2000079674579029, 2000089278301787, 1999919595203594,
    1999806843839423, 1999929574883960, 2000118710171788, 2000097124833597, 1999895658274244,
    1999816249265782, 1999984150425118, 2000157480339793, 2000089550130688, 1999900195144718,
    1999888310610253, 2000073167543297, 2000170931430585, 2000036303300554, 1999882764719072,
    1999948608739888, 2000128732942369, 2000129755434690, 1999909418282145, 1999750602026151,
    1999866425064262, 2000099167191156, 2000130584984519, 1999914566360635, 1999747960819462,
    1999879965034483, 2000172228330520, 2000264992337131, 2000045609202607]
private def pvn_m8_r512_5_9_p3 : List ℕ :=
  [1999805543332569, 1999864995347740, 2000147999506075, 2000271530950502, 2000042074265453,
    1999714890194359, 1999680019748890, 1999979293057664, 2000260551267570, 2000208262203310,
    1999909619063340, 1999729433945352, 1999873610988690, 2000162968581261, 2000257851727137,
    2000051523004658, 1999782923174072, 1999755589271736, 1999990800686558, 2000206662829313,
    2000142458828116, 1999857709592826, 1999666249307292, 1999782653807730, 2000084011327214,
    2000252105074678, 2000126829571692, 1999873794613097, 1999792654662884, 1999990886000133,
    2000274499257302, 2000354578059814, 2000140076341327, 1999822429423554, 1999684694901016,
    1999833252834297, 2000105830487321, 2000231562330739, 2000086559216544, 1999808091424295,
    1999664935828021, 1999806059647821, 2000120522403200, 2000336405227593, 2000264515164275,
    1999963253694455, 1999682178401499, 1999646774537155, 1999878792732503, 2000195088020542,
    2000363301996909, 2000273575162919, 1999999955757056, 1999730110564792, 1999634480574752,
    1999765759100686, 2000039519620783, 2000292432743275, 2000377410225562, 2000243639530745,
    1999961912424445, 1999685465123259, 1999569636596008, 1999692167192125]
private def pvn_m8_r512_5_9_p4 : List ℕ :=
  [2000011405536084, 2000379366349863, 2000604253590303, 2000539761861965, 2000165916031700,
    1999621219742788, 1999158282068429, 1999029981930483, 1999356587532584, 2000046240148571,
    2000819660292397, 2001332805205757, 2001334806489565, 2000780508087753, 1999847284457749,
    1998860634227426, 1998175015039486, 1998063144919293, 1998644210019835, 1999853055783313,
    2001439636644505, 2002994419250013, 2004008365564169, 2003979054018623, 2002559839606976,
    1999722471035196, 1995879800130684, 1991908708536542, 1989031429431926, 1988552965767980,
    1991501062764881, 1998256188804702, 2008276523492987, 2020008569747977, 2031030096445953,
    2038411610014133, 2039224344193240, 2031084700640139, 2012617582722358, 1983744050428637,
    1945742835753777, 1901086338019063, 1853096125659324, 1805491540147976, 1761914524363715,
    1725506247846290, 1698591581108386, 1682502083774144, 1677542467248514, 1683083673936095,
    1697750402491994, 1719663200962471, 1746694905033894, 1776706895315519, 1807740338913671,
    1838148932453081, 1866670508623309, 1892443575628918, 1914980538513545, 1934111861645124,
    1949915224512451, 1962641598854358, 1972647030462987, 1980335537780333]
private def pvn_m8_r512_5_9_p5 : List ℕ :=
  [1986115518526705, 1990369712388210, 1993437208395212, 1995605155871795, 1997107591490837,
    1998128952577339, 1998810237345619, 1999256257220812, 1999542906471659, 1999723790993725,
    1999835884300087, 1999904110670730, 1999944903191293, 1999968865131471, 1999982695420937,
    1999990539846006, 1999994912678735, 1999997308679269, 1999998599253595, 1999999282693783,
    1999999638561291, 1999999820780918, 1999999912544267, 1999999957996842, 1999999980143604,
    1999999990759862, 1999999995766978, 1999999998090808, 1999999999152177, 1999999999629284,
    1999999999840386, 1999999999932330, 1999999999971752, 1999999999988392, 1999999999995310,
    1999999999998141, 1999999999999280, 1999999999999730, 1999999999999904, 1999999999999969,
    1999999999999993]
private def pvn_m8_r512_5_9 : List ℕ :=
  pCat pvn_m8_r512_5_9_p0
    (pCat pvn_m8_r512_5_9_p1
    (pCat pvn_m8_r512_5_9_p2
    (pCat pvn_m8_r512_5_9_p3
    (pCat pvn_m8_r512_5_9_p4
      pvn_m8_r512_5_9_p5))))
private def pvn_m8_r512_5_10_p0 : List ℕ :=
  [2000112231354351, 1999933533978004, 2000210049481646, 1999796711291592, 1999950337005062,
    2000043782739612, 2000213010306394, 1999902328918879, 1999918798057673, 2000015690397032,
    1999961726899969, 1999973547908286, 2000114906644793, 2000164656595273, 2000152367865158,
    2000109351274503, 2000012120285368, 1999989605865810, 1999948377848625, 1999891599799172,
    1999997962641999, 2000041903708341, 1999967959443668, 2000012562261184, 2000036762325397,
    1999938450431806, 2000041173982465, 2000092741873585, 1999927596648840, 1999863159832440,
    2000009375163366, 1999984476798753, 1999949564570339, 2000043651834818, 1999968212691052,
    1999859648663185, 1999958498899781, 2000053311220765, 1999973849588795, 1999947759289330,
    1999981679634212, 1999865566809830, 1999837281216552, 1999995146316747, 1999983248488651,
    1999854734297354, 1999942564091895, 2000133712764021, 2000144766595401, 2000041633368797,
    2000018295717693, 2000023881276095, 1999988456953721, 1999994534507471, 2000021018621776,
    2000021698256530, 2000045395921466, 2000014214268728, 1999897947193066, 1999890976280337,
    1999990489500941, 1999974320405016, 1999898143632376, 1999987713696160]
private def pvn_m8_r512_5_10_p1 : List ℕ :=
  [2000165195425309, 2000181300612771, 2000053528355282, 1999969747395529, 1999926553156974,
    1999870226575520, 1999914924151426, 2000038399360847, 2000040088127791, 1999996726288467,
    2000100840151399, 2000156059530338, 1999954629090230, 1999786630633664, 1999933083699047,
    2000139470070251, 2000090007349906, 1999933913536719, 1999942140766217, 2000033619168437,
    2000014328481340, 1999957145049820, 1999980334292418, 1999982593819031, 1999914915326888,
    1999926839386114, 2000032898504254, 2000066808911770, 2000021404793968, 2000010823701878,
    2000002361158952, 1999943576690053, 1999932167478941, 2000004168273679, 2000031308397052,
    1999981681944752, 1999990626618513, 2000077018985263, 2000077680981280, 1999965016882437,
    1999944503697432, 2000084664313839, 2000146750277680, 1999998233300499, 1999870664100968,
    1999943806273735, 2000040613826226, 2000014393547433, 2000024612137957, 2000150885178286,
    2000171858053824, 1999989487944161, 1999849175874779, 1999911119379568, 1999994081773017,
    1999942711573202, 1999895661301669, 1999986889453920, 2000079993597936, 2000028747852145,
    1999964262026136, 2000054221449069, 2000160245730027, 2000056635521572]
private def pvn_m8_r512_5_10_p2 : List ℕ :=
  [1999857389994750, 1999852764161942, 2000007485461972, 2000032894703755, 1999909384576336,
    1999897319865591, 2000035506659015, 2000076809299655, 1999963259617533, 1999935096815292,
    2000077659504041, 2000151562520974, 2000014852035800, 1999878702464017, 1999948484150791,
    2000074995952757, 2000012487079128, 1999845120286629, 1999854125651982, 2000033639415033,
    2000077736273226, 1999896583972899, 1999800344331928, 1999997909958638, 2000222486394545,
    2000136114520727, 1999873745718056, 1999833047351101, 2000054100248279, 2000188456159166,
    2000066145524022, 1999928329873131, 2000004123485777, 2000159592810819, 2000148732689318,
    2000007568382862, 1999966365986673, 2000063571080669, 2000093069811976, 1999957369601724,
    1999852368638319, 1999971195908196, 2000176701027619, 2000173771670739, 1999951299721467,
    1999816915568485, 1999946631998134, 2000125239231241, 2000076178428243, 1999876767798759,
    1999828724209798, 1999996456942714, 2000120732082030, 2000020627166970, 1999861595679420,
    1999897685554777, 2000089436471863, 2000161298413789, 2000004995439292, 1999844115990751,
    1999924688521546, 2000162003703181, 2000237585870038, 2000028304562501]
private def pvn_m8_r512_5_10_p3 : List ℕ :=
  [1999788794137467, 1999824023392596, 2000076973218873, 2000192665286945, 1999991271365918,
    1999720121843762, 1999735505234770, 2000030572595073, 2000238552037389, 2000108342410868,
    1999827018485272, 1999775350395961, 2000041721298097, 2000311907624473, 2000257176752848,
    1999929786101008, 1999694442321710, 1999798250377490, 2000094313370395, 2000228243716165,
    2000053432668185, 1999791436267459, 1999762099492679, 2000006122333427, 2000240316554828,
    2000192806450175, 1999921434434368, 1999743190025489, 1999862942684398, 2000138343244879,
    2000248227482111, 2000059446133435, 1999771075684804, 1999686468311724, 1999882712018239,
    2000139214828811, 2000184107836598, 1999980876364345, 1999758746821507, 1999771094252034,
    2000036453327775, 2000318092859222, 2000354841243538, 2000114012949809, 1999822022200107,
    1999745682072580, 1999937268347380, 2000189230737753, 2000239002212374, 2000022401904235,
    1999732655979207, 1999636061298034, 1999826652240677, 2000147020338088, 2000333816838385,
    2000242538222047, 1999955340400805, 1999699018998716, 1999662445624892, 1999863898397024,
    2000154661020793, 2000334753767890, 2000288240984187, 2000050740558752]
private def pvn_m8_r512_5_10_p4 : List ℕ :=
  [1999776967810703, 1999638898229616, 1999721290966124, 1999975633360499, 2000253595605082,
    2000393710091939, 2000309579999622, 2000035235858235, 1999710386071569, 1999514992375503,
    1999579851148803, 1999910155193529, 2000361828493348, 2000695876793286, 2000698256304854,
    2000307512967087, 1999673249130019, 1999099034891811, 1998891364157630, 1999196881825603,
    1999919909540261, 2000763974907494, 2001368888850664, 2001467094638675, 2000985585666857,
    2000061438788177, 1998985807109280, 1998114142020642, 1997774281836932, 1998184958295285,
    1999385764809129, 2001184648101667, 2003143504227606, 2004630843859125, 2004960191756162,
    2003602651032264, 2000423011059361, 1995859125951880, 1990960901652827, 1987235591915924,
    1986303919500633, 1989437964414910, 1997102278766873, 2008634027461278, 2022168692980640,
    2034853690606363, 2043314270504152, 2044269378269447, 2035159192306045, 2014648581645272,
    1982906794464040, 1941619465992273, 1893747790574577, 1843097260152311, 1793786300221868,
    1749711340306052, 1714092306856174, 1689157195423337, 1675993259206311, 1674561951066796,
    1683850132901032, 1702114313553173, 1727168788206348, 1756671622369245]
private def pvn_m8_r512_5_10_p5 : List ℕ :=
  [1788372136380860, 1820296858439329, 1850864775811238, 1878934664613891, 1903795798339151,
    1925117914753218, 1942877296460912, 1957274072711171, 1968652472991405, 1977431790289518,
    1984052043575356, 1988935263487224, 1992461174634125, 1994954803401817, 1996683054114026,
    1997857359323051, 1998639908482913, 1999151511915874, 1999479730563329, 1999686412916545,
    1999814187565035, 1999891753089736, 1999937996493092, 1999965076971639, 1999980656426787,
    1999989462815482, 1999994354410360, 1999997024742242, 1999998457574451, 1999999213349256,
    1999999605277690, 1999999805120044, 1999999905323506, 1999999954736288, 1999999978702709,
    1999999990137268, 1999999995504268, 1999999997982730, 1999999999108920, 1999999999612491,
    1999999999834091, 1999999999930067, 1999999999970984, 1999999999988154, 1999999999995243,
    1999999999998126, 1999999999999280, 1999999999999732, 1999999999999906, 1999999999999971,
    1999999999999994]
private def pvn_m8_r512_5_10 : List ℕ :=
  pCat pvn_m8_r512_5_10_p0
    (pCat pvn_m8_r512_5_10_p1
    (pCat pvn_m8_r512_5_10_p2
    (pCat pvn_m8_r512_5_10_p3
    (pCat pvn_m8_r512_5_10_p4
      pvn_m8_r512_5_10_p5))))
private def phb_m8_r512_6_p0 : List ℕ :=
  [76623505322514, 108195698786136, 132308426762743, 152541371524070, 170283401206800,
    186247944099973, 200859469978081, 214394970814341, 227047140395967, 238956491485555,
    250229260644078, 260948107731926, 271178866711545, 280974995573338, 290380617254337,
    299432661475622, 308162412649939, 316596653648265, 324758527432642, 332668197271315,
    340343360294519, 347799652373850, 355050971198314, 362109736899946, 368987104390813,
    375693137925717, 382236955800603, 388626851209662, 394870393898360, 400974516219347,
    406945586423437, 412789471429048, 418511590861606, 424116963804483, 429610249429682,
    434995782461295, 440277604254036, 445459490132842, 450544973529866, 455537367366520,
    460439783056036, 465255147442921, 469986217947138, 474635596140607, 479205739950304,
    483698974654340, 488117502814102, 492463413265860, 496738689278698, 500945215971514,
    505084787069899, 509159111073457, 513169816895392, 517118459028639, 521006522286360,
    524835426158968, 528606528825052, 532321130849266, 535980478596634, 539585767389464,
    543138144430255, 546638711511513, 550088527531210, 553488610830707]
private def phb_m8_r512_6_p1 : List ℕ :=
  [556839941370244, 560143462755649, 563400084128517, 566610681930998, 569776101555216,
    572897158886450, 575974641748342, 579009311257644, 582001903095366, 584953128700548,
    587863676392364, 590734212425762, 593565381985405, 596357810122267, 599112102636914,
    601828846913118, 604508612705207, 607151952882245, 609759404131928, 612331487626819,
    614868709655378, 617371562220041, 619840523604423, 622276058911592, 624678620575193,
    627048648845091, 629386572249064, 631692808031992, 633967762573857, 636211831787812,
    638425401499460, 640608847808420, 642762537433192, 644886828040254, 646982068558259,
    649048599478164, 651086753140045, 653096854007324, 655079218929068, 657034157391005,
    658961971755831, 660862957493377, 662737403401141, 664585591815693, 666407798815391,
    668204294414864, 669975342751649, 671721202265378, 673442125869870, 675138361118477,
    676810150363000, 678457730906471, 680081335150110, 681681190734703, 683257520676673,
    684810543499085, 686340473357804, 687847520163039, 689331889696460, 690793783724106,
    692233400105242, 693650932897363, 695046572457502, 696420505539994]
private def phb_m8_r512_6_p2 : List ℕ :=
  [697772915390861, 699103981838939, 700413881383913, 701702787281349, 702970869624885,
    704218295425670, 705445228689174, 706651830489473, 707838259041102, 709004669768591,
    710151215373748, 711278045900805, 712385308799484, 713473148986082, 714541708902641,
    715591128574277, 716621545664738, 717633095530256, 718625911271758, 719600123785495,
    720555861812145, 721493251984446, 722412418873420, 723313485033223, 724196571044678,
    725061795557550, 725909275331573, 726739125276314, 727551458489884, 728346386296544,
    729124018283249, 729884462335162, 730627824670171, 731354209872440, 732063720925040,
    732756459241667, 733432524697502, 734092015659219, 734735029014185, 735361660198863,
    735972003226465, 736566150713850, 737144193907713, 737706222710083, 738252325703141,
    738782590173392, 739297102135200, 739795946353718, 740279206367214, 740746964508825,
    741199301927756, 741636298609928, 742058033398104, 742464584011503, 742856027064917,
    743232438087343, 743593891540149, 743940460834786, 744272218350052, 744589235448930,
    744891582495008, 745179328868491, 745452542981813, 745711292294872]
private def phb_m8_r512_6_p3 : List ℕ :=
  [745955643329885, 746185661685881, 746401412052835, 746602958225463, 746790363116676,
    746963688770703, 747122996375904, 747268346277264, 747399797988586, 747517410204387,
    747621240811509, 747711346900446, 747787784776395, 747850609970045, 747899877248097,
    747935640623534, 747957953365645, 747966868009793, 747962436366962, 747944709533058,
    747913737897991, 747869571154532, 747812258306955, 747741847679463, 747658386924409,
    747561923030315, 747452502329693, 747330170506662, 747194972604390, 747046953032334,
    746886155573305, 746712623390357, 746526399033486, 746327524446175, 746116040971755,
    745891989359606, 745655409771197, 745406341785960, 745144824407013, 744870896066723,
    744584594632121, 744285957410167, 743975021152868, 743651822062249, 743316395795186,
    742968777468096, 742609001661493, 742237102424400, 741853113278638, 741457067222973,
    741048996737142, 740628933785740, 740196909821991, 739752955791386, 739297102135200,
    738829378793886, 738349815210350, 737858440333102, 737355282619294, 736840370037637,
    736313730071200, 735775389720100, 735225375504074, 734663713464933]
private def phb_m8_r512_6_p4 : List ℕ :=
  [734090429168915, 733505547708915, 732909093706610, 732301091314475, 731681564217680,
    731050535635893, 730408028324959, 729754064578483, 729088666229294, 728411854650812,
    727723650758303, 727024075010024, 726313147408264, 725590887500281, 724857314379127,
    724112446684369, 723356302602703, 722588899868460, 721810255764002, 721020387120019,
    720219310315709, 719407041278853, 718583595485782, 717748987961235, 716903233278107,
    716046345557081, 715178338466161, 714299225220080, 713409018579605, 712507730850720,
    711595373883703, 710671959072081, 709737497351471, 708791999198302, 707835474628418,
    706867933195562, 705889383989734, 704899835635434, 703899296289768, 702887773640438,
    701865274903599, 700831806821585, 699787375660509, 698731987207718, 697665646769125,
    696588359166390, 695500128733974, 694400959316037, 693290854263199, 692169816429153,
    691037848167120, 689894951326160, 688741127247320, 687576376759628, 686400700175917,
    685214097288492, 684016567364620, 682808109141854, 681588720823174, 680358400071953,
    679117144006734, 677864949195823, 676601811651689, 675327726825158]
private def phb_m8_r512_6_p5 : List ℕ :=
  [674042689599420, 672746694283815, 671439734607416, 670121803712390, 668792894147143,
    667452997859226, 666102106188021, 664740209857174, 663367298966789, 661983362985368,
    660588390741490, 659182370415224, 657765289529271, 656337134939816, 654897892827098,
    653447548685683, 651986087314421, 650513492806101, 649029748536771, 647534837154728,
    646028740569162, 644511439938454, 642982915658094, 641443147348234, 639892113840853,
    638329793166512, 636756162540708, 635171198349795, 633574876136466, 631967170584786,
    630348055504750, 628717503816360, 627075487533204, 625421977745516, 623756944602698,
    622080357295300, 620392184036418, 618692392042506, 616980947513577, 615257815612769,
    613522960445256, 611776345036481, 610017931309687, 608247680062714, 606465550944046,
    604671502428074, 602865491789546, 601047475077171, 599217407086360, 597375241331044,
    595520930014563, 593654423999570, 591775672776919, 589884624433499, 587981225618972,
    586065421511359, 584137155781454, 582196370555988, 580243006379520, 578277002174979,
    576298295202818, 574306821018719, 572302513429773, 570285304449097]
private def phb_m8_r512_6_p6 : List ℕ :=
  [568255124248800, 566211901111230, 564155561378439, 562086029399773, 560003227477518,
    557907075810501, 555797492435565, 553674393166823, 551537691532581, 549387298709824,
    547223123456159, 545045072039093, 542853048162514, 540646952890250, 538426684566561,
    536192138733412, 533943208044383, 531679782175031, 529401747729542, 527108988143478,
    524801383582429, 522478810836348, 520141143209357, 517788250404788, 515419998405189,
    513036249347059, 510636861389999, 508221688579992, 505790580706487, 503343383152941,
    500879936740461, 498400077564142, 495903636821704, 493390440633963, 490860309856677,
    488313059883250, 485748500437752, 483166435357670, 480566662365776, 477948972830423,
    475313151513568, 472658976305744, 469986217947138, 467294639733909, 464583997208750,
    461854037834684, 459104500650963, 456335115909857, 453545604693046, 450735678506175,
    447905038850074, 445053376766959, 442180372359834, 439285694283130, 436368999202467,
    433429931221222, 430468121271393, 427483186466007, 424474729410076, 421442337466825,
    418385581975601, 415304017417528, 412197180524601, 409064589327453]
private def phb_m8_r512_6_p7 : List ℕ :=
  [405905742136593, 402720116451355, 399507167790191, 396266328435308, 392997006083851,
    389698582397028, 386370411437580, 383011817984964, 379622095716330, 376200505240061,
    372746271967010, 369258583802785, 365736588642399, 362179391646219, 358586052273477,
    354955581046464, 351286936014980, 347579018886434, 343830670782176, 340040667575055,
    336207714756604, 332330441774640, 328407395772989, 324437034654439, 320417719375401,
    316347705365787, 312225132949706, 308048016621146, 303814233002961, 299521507286253,
    295167397909179, 290749279187784, 286264321554311, 281709468987780, 277081413133751,
    272376563500070, 267591012976537, 262720497749988, 257760350460236, 252705445150386,
    247550132184401, 242288160803746, 236912586328367, 231415658110287, 225788683126112,
    220021858407559, 214104063144987, 208022597932900, 201762853747901, 195307886039257,
    188637858420127, 181729303585915, 174554122252361, 167078196837417, 159259421573647,
    151044817483360, 142366151991857, 133132990583976, 123221059579417, 112451354139431,
    100549005675267, 87051093020437, 71054588858110, 50227131475041]
private def phb_m8_r512_6 : List ℕ :=
  pCat phb_m8_r512_6_p0
    (pCat phb_m8_r512_6_p1
    (pCat phb_m8_r512_6_p2
    (pCat phb_m8_r512_6_p3
    (pCat phb_m8_r512_6_p4
    (pCat phb_m8_r512_6_p5
    (pCat phb_m8_r512_6_p6
      phb_m8_r512_6_p7))))))
private def pvn_m8_r512_6_0_p0 : List ℕ :=
  [1999887768645649, 1999933533978004, 2000210049481646, 2000203288708408, 2000049662994938,
    1999956217260388, 2000213010306394, 1999902328918879, 1999918798057673, 2000015690397032,
    2000038273100031, 2000026452091714, 1999885093355207, 2000164656595273, 2000152367865158,
    1999890648725497, 2000012120285368, 1999989605865810, 1999948377848625, 1999891599799172,
    2000002037358001, 2000041903708341, 1999967959443668, 2000012562261184, 1999963237674603,
    2000061549568194, 2000041173982465, 2000092741873585, 1999927596648840, 1999863159832440,
    1999990624836634, 1999984476798753, 1999949564570339, 2000043651834818, 1999968212691052,
    1999859648663185, 1999958498899781, 1999946688779235, 2000026150411205, 1999947759289330,
    1999981679634212, 1999865566809830, 1999837281216552, 1999995146316747, 1999983248488651,
    1999854734297354, 1999942564091895, 2000133712764021, 2000144766595401, 2000041633368797,
    2000018295717693, 2000023881276095, 1999988456953721, 2000005465492529, 1999978981378224,
    2000021698256530, 2000045395921466, 2000014214268728, 1999897947193066, 1999890976280337,
    1999990489500941, 1999974320405016, 1999898143632376, 1999987713696160]
private def pvn_m8_r512_6_0_p1 : List ℕ :=
  [2000165195425309, 2000181300612771, 2000053528355282, 1999969747395529, 1999926553156974,
    1999870226575520, 1999914924151426, 1999961600639153, 2000040088127791, 1999996726288467,
    2000100840151399, 1999843940469662, 2000045370909770, 2000213369366336, 2000066916300953,
    2000139470070251, 2000090007349906, 1999933913536719, 1999942140766217, 2000033619168437,
    2000014328481340, 1999957145049820, 1999980334292418, 1999982593819031, 2000085084673112,
    2000073160613886, 2000032898504254, 2000066808911770, 2000021404793968, 2000010823701878,
    2000002361158952, 1999943576690053, 1999932167478941, 2000004168273679, 2000031308397052,
    1999981681944752, 1999990626618513, 1999922981014737, 2000077680981280, 2000034983117563,
    1999944503697432, 1999915335686161, 2000146750277680, 1999998233300499, 1999870664100968,
    2000056193726265, 2000040613826226, 2000014393547433, 2000024612137957, 2000150885178286,
    2000171858053824, 1999989487944161, 1999849175874779, 2000088880620432, 1999994081773017,
    1999942711573202, 1999895661301669, 1999986889453920, 1999920006402064, 2000028747852145,
    1999964262026136, 2000054221449069, 2000160245730027, 2000056635521572]
private def pvn_m8_r512_6_0_p2 : List ℕ :=
  [1999857389994750, 1999852764161942, 2000007485461972, 2000032894703755, 2000090615423664,
    1999897319865591, 2000035506659015, 2000076809299655, 2000036740382467, 1999935096815292,
    2000077659504041, 2000151562520974, 2000014852035800, 1999878702464017, 1999948484150791,
    1999925004047243, 2000012487079128, 1999845120286629, 1999854125651982, 1999966360584967,
    2000077736273226, 1999896583972899, 2000199655668072, 2000002090041362, 2000222486394545,
    2000136114520727, 1999873745718056, 1999833047351101, 2000054100248279, 2000188456159166,
    2000066145524022, 1999928329873131, 1999995876514223, 1999840407189181, 1999851267310682,
    2000007568382862, 1999966365986673, 1999936428919331, 1999906930188024, 2000042630398276,
    1999852368638319, 1999971195908196, 1999823298972381, 1999826228329261, 1999951299721467,
    1999816915568485, 1999946631998134, 1999874760768759, 1999923821571757, 1999876767798759,
    1999828724209798, 1999996456942714, 2000120732082030, 2000020627166970, 2000138404320580,
    2000102314445223, 2000089436471863, 2000161298413789, 2000004995439292, 2000155884009249,
    2000075311478454, 2000162003703181, 1999762414129962, 1999971695437499]
private def pvn_m8_r512_6_0_p3 : List ℕ :=
  [1999788794137467, 1999824023392596, 2000076973218873, 2000192665286945, 1999991271365918,
    2000279878156238, 2000264494765230, 2000030572595073, 2000238552037389, 2000108342410868,
    2000172981514728, 2000224649604039, 1999958278701903, 2000311907624473, 2000257176752848,
    1999929786101008, 1999694442321710, 1999798250377490, 1999905686629605, 1999771756283835,
    1999946567331815, 1999791436267459, 1999762099492679, 1999993877666573, 2000240316554828,
    2000192806450175, 2000078565565632, 2000256809974511, 2000137057315602, 2000138343244879,
    2000248227482111, 2000059446133435, 2000228924315196, 1999686468311724, 1999882712018239,
    2000139214828811, 2000184107836598, 1999980876364345, 2000241253178493, 1999771094252034,
    2000036453327775, 2000318092859222, 2000354841243538, 2000114012949809, 2000177977799893,
    2000254317927420, 2000062731652620, 2000189230737753, 2000239002212374, 2000022401904235,
    2000267344020793, 1999636061298034, 1999826652240677, 1999852979661912, 1999666183161615,
    1999757461777953, 1999955340400805, 1999699018998716, 2000337554375108, 2000136101602976,
    2000154661020793, 2000334753767890, 1999711759015813, 2000050740558752]
private def pvn_m8_r512_6_0_p4 : List ℕ :=
  [1999776967810703, 1999638898229616, 1999721290966124, 1999975633360499, 2000253595605082,
    2000393710091939, 2000309579999622, 1999964764141765, 2000289613928431, 2000485007624497,
    2000420148851197, 1999910155193529, 2000361828493348, 2000695876793286, 2000698256304854,
    1999692487032913, 1999673249130019, 1999099034891811, 1998891364157630, 1999196881825603,
    1999919909540261, 1999236025092506, 1998631111149336, 1998532905361325, 1999014414333143,
    1999938561211823, 1998985807109280, 1998114142020642, 1997774281836932, 1998184958295285,
    1999385764809129, 1998815351898333, 1996856495772394, 1995369156140875, 1995039808243838,
    1996397348967736, 1999576988940639, 1995859125951880, 1990960901652827, 1987235591915924,
    1986303919500633, 1989437964414910, 1997102278766873, 1991365972538722, 1977831307019360,
    1965146309393637, 1956685729495848, 1955730621730553, 1964840807693955, 1985351418354728,
    1982906794464040, 1941619465992273, 1893747790574577, 1843097260152311, 1793786300221868,
    1749711340306052, 1714092306856174, 1689157195423337, 1675993259206311, 1674561951066796,
    1683850132901032, 1702114313553173, 1727168788206348, 1756671622369245]
private def pvn_m8_r512_6_0_p5 : List ℕ :=
  [1788372136380860, 1820296858439329, 1850864775811238, 1878934664613891, 1903795798339151,
    1925117914753218, 1942877296460912, 1957274072711171, 1968652472991405, 1977431790289518,
    1984052043575356, 1988935263487224, 1992461174634125, 1994954803401817, 1996683054114026,
    1997857359323051, 1998639908482913, 1999151511915874, 1999479730563329, 1999686412916545,
    2000185812434965, 2000108246910264, 2000062003506908, 2000034923028361, 1999980656426787,
    1999989462815482, 1999994354410360, 1999997024742242, 2000001542425549, 2000000786650744,
    1999999605277690, 1999999805120044, 2000000094676494, 2000000045263712, 2000000021297291,
    1999999990137268, 1999999995504268, 1999999997982730, 1999999999108920, 1999999999612491,
    2000000000165909, 2000000000069933, 2000000000029016, 2000000000011846, 2000000000004757,
    1999999999998126, 1999999999999280, 1999999999999732, 1999999999999906, 1999999999999971,
    2000000000000006]
private def pvn_m8_r512_6_0 : List ℕ :=
  pCat pvn_m8_r512_6_0_p0
    (pCat pvn_m8_r512_6_0_p1
    (pCat pvn_m8_r512_6_0_p2
    (pCat pvn_m8_r512_6_0_p3
    (pCat pvn_m8_r512_6_0_p4
      pvn_m8_r512_6_0_p5))))
private def pvn_m8_r512_6_1_p0 : List ℕ :=
  [1999996212095313, 1999857564073861, 1999907544414367, 1999884274711485, 2000253423039111,
    2000171864212168, 1999992087455165, 2000100264673455, 2000073490790660, 2000144477962431,
    2000053573494073, 1999816556393264, 2000043448854213, 2000091590805632, 1999958864025721,
    1999898325380640, 1999978229382998, 2000135487017081, 2000015466798266, 2000055712862081,
    2000028411654559, 2000066755733870, 1999994843361855, 1999925243480079, 1999964153123050,
    1999948319409561, 1999946002913630, 2000046964678711, 2000037441072406, 1999853449914300,
    2000009878410852, 2000032527006229, 2000074105507322, 2000044507280438, 2000034824788045,
    2000010982785860, 1999899219830422, 1999917445666086, 2000015438640401, 1999991182104334,
    1999973535524272, 2000024375060251, 1999958922166943, 1999857321772317, 1999896089629105,
    2000077820907458, 2000030032003325, 1999909688227427, 1999896930988796, 1999971223105308,
    1999983393055728, 1999916830753184, 1999866008409083, 1999860309445408, 1999924782074422,
    2000024539583810, 2000050040970741, 2000023792527978, 2000078147507779, 2000104218136058,
    2000056233772403, 1999892407385416, 2000015735692401, 2000036053834481]
private def pvn_m8_r512_6_1_p1 : List ℕ :=
  [2000119011909746, 1999917366599285, 1999990603926360, 2000071930130333, 1999928821656194,
    2000013804127910, 1999889814208507, 1999787608087489, 1999999222937588, 2000054894670983,
    2000021582679290, 2000129734870675, 2000204433248412, 2000004971755459, 1999911643501172,
    1999930006304719, 1999904424084067, 1999979198377944, 2000011126667053, 1999994789795226,
    1999963036291639, 1999899318623209, 1999966947580979, 2000087212951298, 2000171046142707,
    2000065576504996, 2000116447931142, 2000016929088613, 2000060492710948, 2000033103776416,
    2000020398239817, 1999947847357329, 1999963126082831, 2000005446387387, 1999950630099891,
    2000091742199650, 1999996606025847, 1999974715337635, 2000147585886484, 2000156948865356,
    1999896757550173, 1999999003528615, 2000005925141012, 2000075306248516, 1999896793829024,
    1999940374135385, 2000034417181001, 2000067695901726, 1999879111499940, 1999977731775447,
    2000107021701310, 1999957262754316, 1999934546840292, 2000012294164754, 2000102106536838,
    1999970124967697, 1999990177524768, 1999848603714000, 2000025614964366, 2000103216592932,
    2000066482409515, 2000034019521370, 2000093131639217, 2000082460772396]
private def pvn_m8_r512_6_1_p2 : List ℕ :=
  [2000059513038770, 1999945189141891, 2000008819182010, 1999999833280420, 2000097182748627,
    1999827866305093, 1999808524931862, 1999920635729657, 2000208897054025, 1999955944279890,
    2000114023382937, 1999945894988084, 2000027107831691, 2000037035469535, 1999823107427020,
    1999960035310407, 2000118485669664, 1999994348312905, 1999969746079727, 1999940061592923,
    2000010232505433, 2000072995153009, 2000077312040812, 2000078553422130, 1999908686435034,
    2000138971652620, 2000063772681544, 1999941611970747, 1999807943282784, 2000034335700389,
    2000047487084661, 1999747758608415, 1999900366971888, 1999845450588093, 2000034933960325,
    2000172172361421, 2000147544476853, 2000087617338079, 1999966704756862, 1999912364970582,
    2000059167848276, 2000068396772659, 2000099648647716, 2000090298871093, 1999887177423512,
    2000111473931728, 1999859856229914, 1999965724269320, 1999844103775537, 2000050671960242,
    1999869283738451, 1999990100374521, 1999984815923275, 1999948381318144, 1999947451425937,
    1999886524335003, 1999763237089381, 1999946473702978, 2000027236732146, 1999727658250243,
    1999955303472181, 1999954483109633, 1999657244986060, 2000011922438577]
private def pvn_m8_r512_6_1_p3 : List ℕ :=
  [1999862049524964, 1999913546404480, 2000099123516533, 2000047446381818, 2000120954348578,
    1999991630705172, 2000051579858033, 2000123789425882, 2000281291058996, 2000110620280888,
    2000020418895163, 2000163201632637, 1999894526367985, 1999714052490672, 1999871202883281,
    2000048979005456, 2000006765564577, 1999845029770122, 2000298290058626, 2000045030300851,
    2000312193510639, 2000157666925528, 2000052193019757, 1999982879860856, 2000276349277939,
    2000240473833282, 2000470348037643, 1999985544660047, 1999968970523103, 2000163615738059,
    1999891844739728, 1999841266662447, 1999967659533761, 1999768205560583, 1999638896293582,
    1999744283031343, 2000134391305609, 1999793396671378, 2000250035855945, 2000015884511407,
    1999933797105672, 2000245941365221, 2000406043162569, 2000219272889641, 2000266211845687,
    1999715877851009, 2000021661357355, 2000278317010671, 1999796448927925, 2000308375350601,
    1999884180778213, 1999960013975348, 2000058225657170, 1999929752435504, 2000246867468729,
    2000251843920374, 2000147052059722, 2000094298372313, 2000248678294650, 2000064520880334,
    2000368672165845, 2000221829136673, 2000225295038392, 1999974766302826]
private def pvn_m8_r512_6_1_p4 : List ℕ :=
  [2000219218518161, 1999835159104268, 1999966551813920, 1999587967166898, 1999735070408769,
    1999658596666165, 1999999613748465, 2000013814221906, 1999923001906822, 2000099116235422,
    2000552799069481, 2000405159101537, 1999315467406217, 1999803739262205, 1999994901596823,
    1999736285315208, 1999918801946032, 1999803396204492, 2000274062571554, 2000211061521429,
    2000288945598200, 2000247852064793, 2000457575832824, 1999213818486665, 2000807482774117,
    2000469802508564, 2001343912227637, 2000585539913741, 1999559594306660, 1998701193311543,
    2000995432294501, 1999421030006695, 1999170512431184, 2000116140338749, 1997028871705866,
    1999260579961827, 2001134544800477, 1999297722187000, 1998597880387727, 1996570030083526,
    1999899846364141, 1998012720346334, 2000427942311446, 2003258731990793, 1993724220477440,
    1990495327467320, 1999862675043960, 2002712869057435, 1998320559027569, 1997520793674140,
    1995098699666314, 1986045600523839, 1982397910015306, 1993413785519352, 2007497624858169,
    2006149001104411, 1986518628120043, 1963261241076352, 1952779520558567, 1959922733792725,
    1977237515973937, 1992362191481481, 1995302182014718, 1981568066604342]
private def pvn_m8_r512_6_1_p5 : List ℕ :=
  [1951756298796652, 1909689130125430, 1860643221744557, 1810098060605583, 1763072917030151,
    1723537806001947, 1694473368480194, 1677195936490628, 1672344781029261, 1678646759243164,
    1694942532723118, 1718671672127405, 1747512327926678, 1779337832467524, 1811634789828272,
    1842920793734350, 1872044562687961, 1897886394406461, 1920130838431994, 1938888752526565,
    1954188449440932, 1966224052174424, 1975518164268864, 1982646866748315, 1987995491586694,
    1991826579173546, 1994451210972428, 1996242055919867, 1997516380547213, 1998457482420647,
    1999137310827296, 1999585797946457, 1999841128604052, 1999959521426331, 1999999695800847,
    2000005998764481, 2000002986105017, 2000000057754668, 1999998924288321, 1999998913704535,
    1999999261891353, 1999999596094081, 1999999816255624, 1999999933207925, 1999999983750631,
    2000000000009717, 2000000002405971, 2000000001129671, 1999999999924040, 1999999999477959,
    1999999999513385, 1999999999694008, 1999999999849901, 1999999999941268, 1999999999982725,
    1999999999997330, 2000000000000845, 2000000000000956, 2000000000000496, 2000000000000181,
    2000000000000045, 2000000000000004, 1999999999999998, 1999999999999999]
private def pvn_m8_r512_6_1 : List ℕ :=
  pCat pvn_m8_r512_6_1_p0
    (pCat pvn_m8_r512_6_1_p1
    (pCat pvn_m8_r512_6_1_p2
    (pCat pvn_m8_r512_6_1_p3
    (pCat pvn_m8_r512_6_1_p4
      pvn_m8_r512_6_1_p5))))
private def pvn_m8_r512_6_2_p0 : List ℕ :=
  [2000075755234497, 1999917057527591, 2000033425671165, 1999939333438297, 1999731727529409,
    1999909855892643, 2000086366294112, 2000062660019057, 2000190310302415, 2000063014476046,
    1999946880036241, 2000120356798081, 2000171862137815, 2000169544895425, 1999929349605163,
    1999948612224280, 2000051501408657, 2000064021717399, 2000012140986046, 1999919145237517,
    1999943046543785, 2000005232098216, 2000048645379039, 1999938564596859, 2000098367654062,
    2000061306219415, 2000007972579609, 2000076031934362, 2000066324485398, 1999988264515902,
    1999904527766264, 1999923742160171, 2000023657788364, 2000023269812709, 1999943472513336,
    1999981433420959, 1999972648637269, 1999944001667026, 1999946328219798, 2000070996325023,
    2000105276350506, 2000019025524544, 2000011214675418, 2000037352517360, 1999966834965129,
    1999878433572061, 1999939588500176, 2000065206932572, 2000079908403375, 1999936417913788,
    1999914812311997, 1999888184397448, 2000021440615401, 1999959109085599, 2000032077894941,
    1999902500407265, 1999923823045145, 2000023957441233, 1999982960230883, 2000012054964308,
    1999841828438316, 1999853902637285, 2000016218497066, 1999847425365072]
private def pvn_m8_r512_6_2_p1 : List ℕ :=
  [1999837897376126, 2000006557593155, 2000056387129437, 2000055860562897, 2000105507623076,
    2000015787593071, 1999925068729759, 2000088097538811, 2000097907597952, 1999938169953789,
    1999983626276271, 2000035924558112, 2000069584995438, 2000001895578671, 2000049787218294,
    1999955034015721, 1999975217479245, 1999838679798408, 1999849704467860, 1999944105555297,
    2000005634067273, 2000102287676611, 2000128608512939, 2000167823289332, 1999972711963821,
    1999952170760276, 1999939383624684, 1999971592229144, 2000013294759352, 2000072679939732,
    1999827972552725, 1999963665034850, 1999927970622483, 1999943516727821, 2000035196975801,
    2000130009103034, 2000026986964181, 2000030110630432, 2000144945767638, 2000119989630768,
    2000071821250452, 1999899347998476, 2000059430951181, 2000081312894322, 1999992738718333,
    1999804745751889, 2000042127480339, 2000087684101809, 1999969254788503, 2000011206220031,
    2000119717025073, 2000055059653276, 2000061177227071, 1999945360445630, 2000054985161834,
    1999999217333678, 2000048657326479, 1999857241238200, 2000022392517612, 1999997678586502,
    2000107800142466, 1999859106946953, 1999990198295023, 1999956867816473]
private def pvn_m8_r512_6_2_p2 : List ℕ :=
  [2000025811475702, 2000150846244467, 1999910823688018, 1999935397265921, 2000088933806744,
    1999931754099613, 1999930054051861, 1999951166276155, 2000024180858110, 2000227252101934,
    2000026814941026, 1999973169889059, 1999953126648629, 2000216997681006, 2000097279312348,
    1999977447683762, 2000008149312339, 1999920765939493, 1999955119509953, 1999822825792797,
    2000013852110956, 1999970875263210, 2000065482952486, 2000183706778741, 1999909824788157,
    1999853242621804, 2000088228565882, 2000061276514900, 1999932990230293, 1999952278249028,
    1999927804552318, 2000160522049570, 1999843868693392, 2000047772735860, 1999919988040961,
    2000126891479253, 2000080904888357, 2000087484693234, 1999955129908302, 1999998308756359,
    2000056366010198, 2000033705369621, 2000058200672350, 1999934295208444, 1999739308411198,
    1999760063185923, 2000002780539405, 2000003029155321, 2000037729010485, 2000191844129164,
    1999858527025049, 2000114511581641, 2000061443962579, 1999823530723691, 2000226959534377,
    2000078551286474, 1999990782018496, 2000050924795209, 2000077924556877, 1999971571096181,
    1999929207233096, 1999943242299507, 1999871932176147, 1999991845237382]
private def pvn_m8_r512_6_2_p3 : List ℕ :=
  [2000002718978466, 1999936892489241, 2000071766821537, 1999784810775138, 1999999210339832,
    1999842096204996, 2000029542474385, 1999711675099916, 2000005268746546, 2000040159482241,
    1999799282072563, 1999643119540140, 2000036014729258, 1999791643611143, 1999885047335037,
    2000020034844831, 1999968377663467, 2000082172785635, 1999936393759318, 1999903483303552,
    2000259544580360, 2000081677744859, 2000319348145794, 2000112315729875, 2000124807291885,
    1999807335874837, 2000169548595857, 2000004542888995, 1999600709195646, 1999828277127742,
    2000167007506141, 1999937999694435, 2000247852678867, 2000213754045036, 1999785611172250,
    2000303766369676, 1999907526717763, 2000317359464472, 2000352545815793, 2000042310446058,
    2000375192334644, 2000037676750007, 2000082139588524, 2000239236920843, 2000143327505380,
    1999715513727543, 1999799290281120, 1999623134791774, 2000064792316958, 1999859709234847,
    1999857255213317, 1999675658242512, 2000101501490139, 1999925657434496, 2000325180918964,
    2000263712494512, 2000213860704109, 2000083990398190, 2000064925315952, 2000101069535194,
    2000057918897908, 2000237689141251, 1999966388463641, 2000029613657338]
private def pvn_m8_r512_6_2_p4 : List ℕ :=
  [1999806801554632, 2000057057809079, 2000190297456521, 1999850673150514, 2000449646464640,
    1999876788188889, 2000053309614578, 2000285423018798, 2000545907558866, 1999527760647992,
    2000665345901469, 2000007614418638, 2000838841239350, 1999589152726934, 2000030725880191,
    2000148427153305, 2000152203931074, 1999152866885814, 1999927969520645, 1999745095998899,
    1999312751689892, 2001143949593416, 1999460105812819, 2000121205533258, 2001240358853618,
    1998123182678330, 2001352764924895, 1999716194832294, 1999270720158417, 1999584464900162,
    1999729992849832, 2001358930620596, 1999427436031641, 2000359755795109, 2000658352895514,
    1997502385267034, 2001139126008123, 2003423728430271, 1998359270579374, 1999266707680693,
    2002817670389395, 1999208365649261, 1998612440284744, 2003238215670977, 2000330581648358,
    1994382504677355, 1998340415073586, 2004669377929578, 2001380434098733, 1995396354292294,
    1996481644663409, 1999931607679383, 1999686103974244, 1999564294686537, 2002101412010342,
    2001154811959100, 1994110825480934, 1989527079366969, 1995996133033473, 2007546977151052,
    2010388844905280, 1998775664657320, 1983277952629407, 1978560801742396]
private def pvn_m8_r512_6_2_p5 : List ℕ :=
  [1989128444784436, 2005786548915477, 2014029468439867, 2006800000704603, 1987914019400435,
    1968118951147392, 1957942002683416, 1961248375537437, 1974886975018016, 1991459555169638,
    2002302223976060, 2000892103308838, 1984409289242942, 1953189520294359, 1910208149147309,
    1860360364931199, 1809037151709375, 1761178366326160, 1721030618336826, 1691731311601199,
    1674840971238035, 1670469028671926, 1677727304797225, 1694940977839123, 1719760641137480,
    1749543885634044, 1781842130335670, 1814615657406536, 1846192072939154, 1875253402793500,
    1900939966878826, 1922905769775175, 1941205681857285, 1956095601728803, 1967896127799940,
    1976967836681364, 1983731645942042, 1988656197220320, 1992198955682942, 1994741863414350,
    1996562327867149, 1997846216568728, 1998721467788252, 1999287628741579, 1999630123017657,
    1999821918958187, 1999920637188439, 1999967099576757, 1999987042478815, 1999994882307952,
    1999997779858230, 1999998871078494, 1999999353503194, 1999999620959873, 1999999787520559,
    1999999889595039, 1999999947360416, 1999999976939218, 1999999990586000, 1999999996280685,
    1999999998469196, 1999999999287279, 1999999999620699, 1999999999785778]
private def pvn_m8_r512_6_2_p6 : List ℕ :=
  [1999999999881420, 1999999999938487, 1999999999970674, 1999999999987274, 1999999999995014,
    1999999999998261, 1999999999999475, 1999999999999873, 1999999999999980]
private def pvn_m8_r512_6_2 : List ℕ :=
  pCat pvn_m8_r512_6_2_p0
    (pCat pvn_m8_r512_6_2_p1
    (pCat pvn_m8_r512_6_2_p2
    (pCat pvn_m8_r512_6_2_p3
    (pCat pvn_m8_r512_6_2_p4
    (pCat pvn_m8_r512_6_2_p5
      pvn_m8_r512_6_2_p6)))))
private def pvn_m8_r512_6_3_p0 : List ℕ :=
  [2000111628793396, 2000004858410166, 1999918557434090, 2000043491422740, 2000114272111009,
    1999877054112081, 1999824614519519, 1999905299767457, 1999825464469758, 1999989180316512,
    2000079239595976, 2000167970987822, 2000093713243375, 1999943473405411, 2000006637018747,
    2000124593665407, 2000211067392351, 2000091814521719, 2000061931012752, 1999929953886046,
    2000022498363143, 2000124871915949, 2000004828844295, 1999966440854308, 2000003703947332,
    1999980228358378, 1999945972909249, 1999972805744709, 2000003635619441, 2000054946467162,
    1999988471994066, 1999993383914701, 2000079873327566, 2000129736460650, 2000059738170734,
    1999959124389429, 1999974865900275, 1999994875560366, 1999953348657485, 1999946017298518,
    2000043132670593, 2000013928568783, 1999972211225739, 1999858317217679, 2000008017377493,
    1999972388697823, 2000015526743090, 1999975985942828, 2000060046617916, 2000165941768644,
    2000001243462374, 1999970085612491, 1999911284499865, 1999909919252064, 2000079439369580,
    2000020064889301, 2000009883290266, 1999989263167807, 1999863739928102, 1999940581046024,
    2000083302046859, 1999980222363740, 1999844724058781, 1999965087641894]
private def pvn_m8_r512_6_3_p1 : List ℕ :=
  [2000046453589181, 1999928375062919, 2000014567798431, 1999968408098672, 1999949383211530,
    1999933657164904, 2000021184527950, 1999829189287941, 1999785298513159, 1999908569171876,
    1999985512824144, 2000055239042188, 1999964631213735, 2000026304607892, 2000028240418061,
    2000092373174076, 2000001632418566, 2000023354758862, 2000014301897921, 2000047290363433,
    1999909509852624, 2000095613742354, 2000029497597175, 2000040654098486, 2000092073951566,
    1999998143755775, 1999907699642041, 1999894145164637, 1999860232480996, 1999790040168466,
    2000064358673739, 2000096138630699, 2000136176861800, 2000039410665675, 2000062778878652,
    1999961068198444, 1999979175183277, 2000002406512323, 2000070285129284, 2000029008165828,
    1999887579968379, 1999805992620807, 2000103324623955, 1999944847385803, 1999898694627777,
    1999902651328253, 2000192286278733, 2000039365030656, 2000091919802445, 1999985990643302,
    2000157758960255, 2000078214941390, 2000045523934575, 2000026457461406, 1999957781012248,
    2000078323827432, 1999942452160487, 1999860547932211, 2000080105628731, 2000031165761843,
    2000007172134864, 2000109766377682, 1999918653125555, 2000125383639845]
private def pvn_m8_r512_6_3_p2 : List ℕ :=
  [2000097922912281, 2000040273688026, 1999903860201179, 1999959002593144, 2000084088878253,
    2000003460426691, 2000049035472092, 1999843216008711, 2000010972117334, 2000048394574315,
    1999972161363200, 1999920466778550, 1999975235212263, 2000196719085879, 2000046037793549,
    1999839801639989, 1999922825598147, 2000024145433259, 1999895584763566, 2000203832949060,
    1999890959768349, 2000048227018091, 1999975279462926, 2000160753179006, 2000020959137848,
    2000016246262521, 2000156136781137, 2000167524056264, 1999949760102464, 1999797861064048,
    1999923940912506, 1999992667509767, 2000013202441714, 1999989074646282, 1999966462614694,
    2000035559238218, 2000044251685415, 2000049590042500, 1999836082221635, 2000082568281047,
    2000031867913757, 1999881214349157, 2000181402897297, 1999807831453189, 1999898019274494,
    2000090615825715, 1999986692959899, 2000109849471619, 2000083954348328, 1999881787256728,
    1999954454177160, 2000188331995280, 2000159788653559, 1999952740032331, 2000139040681057,
    1999763195737966, 1999927055192702, 1999721272204197, 2000010598770135, 1999952969614154,
    2000074681244599, 1999959734601850, 2000028873307758, 2000007713930341]
private def pvn_m8_r512_6_3_p3 : List ℕ :=
  [2000062769679925, 1999918144870449, 2000147295846344, 2000053419600240, 1999921287122461,
    2000262631210300, 2000117464589925, 1999758891777108, 2000114910354978, 1999884594349440,
    2000049983031208, 1999799012594819, 2000041952344117, 2000027864859495, 2000024050059031,
    1999834212539870, 1999897758643802, 2000002548409199, 1999874645420293, 1999870635140071,
    2000080640904012, 1999919707872691, 1999640630724733, 2000189750407300, 1999508265511610,
    1999793996069712, 2000210524591705, 1999794887409416, 2000038299858256, 1999721565298604,
    1999967696751768, 2000136529982840, 2000071889835985, 2000010868381770, 2000307752652974,
    1999968117594851, 2000389038109551, 2000108976216124, 2000008507412907, 1999729016576935,
    1999957339722782, 1999763368128155, 2000082047672931, 2000043827601300, 2000085986194122,
    2000076695186624, 1999844117415463, 2000070896953605, 2000234094739869, 2000332471581460,
    1999967515308221, 2000156846580914, 2000226054108658, 2000278489290335, 2000453898694750,
    1999928666872546, 2000229498347920, 1999627307757693, 2000141550283225, 1999804026136710,
    2000025451944316, 1999460216232743, 2000286139217674, 1999072525851499]
private def pvn_m8_r512_6_3_p4 : List ℕ :=
  [2000404276639644, 1999921400238209, 2000189902169464, 2000109326459753, 2000287487559386,
    1999946863756873, 2000095579416056, 2000334575185799, 2000083130167656, 2000411318555028,
    1999282526287437, 2000270881622039, 2000945151805929, 1998312042390212, 2001452754649063,
    1999280587241313, 2000153191516315, 2000952187775084, 1998803593111627, 2000816639810935,
    2000260178512757, 1999992738346155, 2000398130003333, 1999917303183070, 2000924473435949,
    1999613143449780, 1999988034787026, 2001541103832034, 1998476024168270, 1998926794295254,
    2001650381419785, 1998747712883480, 1998938209364149, 2002163850159717, 1999139820924306,
    1998253707585703, 2002875543799535, 2001017424604621, 1996586770034619, 1999830911950456,
    2002244863692529, 1998635920082313, 1999004211995024, 2002559263768620, 1999925143875144,
    1996312469456045, 2000555595572974, 2004334962152888, 2000071305139600, 1996021256608937,
    2000028248896101, 2004351523699183, 2001941827037410, 1998236092985639, 1998736733838025,
    2000347610119009, 1999329621106417, 1999083066570647, 2001862853660059, 2002391226579376,
    1997311974622766, 1992525349293228, 1995929653388928, 2005299031770891]
private def pvn_m8_r512_6_3_p5 : List ℕ :=
  [2008989856724369, 2000900474629824, 1989013640494033, 1986327566135216, 1996561545981315,
    2010091448605410, 2013516310686825, 2002895128401267, 1986992985664893, 1978636503296251,
    1984110714020122, 1999122656254154, 2012663074419543, 2015050454297186, 2004087439725769,
    1985350991056688, 1967949899268081, 1959612718619265, 1963450727908365, 1977079045212954,
    1994100488214406, 2006917604534004, 2009188113998957, 1997114069871566, 1969881289512038,
    1929563553824556, 1880422780981683, 1827774876331986, 1776953232281691, 1732663547644003,
    1698568572281895, 1676933452194965, 1668452090678410, 1672416223681061, 1687133507462590,
    1710343332437916, 1739504444319634, 1772020837444723, 1805492598406834, 1837959413021849,
    1868033144568760, 1894873997439825, 1918068629753126, 1937506361948808, 1953303751203900,
    1965762858544710, 1975324711407428, 1982500791063252, 1987796886085888, 1991655248026594,
    1994429733368554, 1996390137002854, 1997741091034048, 1998641520922490, 1999217678970211,
    1999569591892468, 1999773985140527, 1999886634640159, 1999945524498100, 1999974768405643,
    1999988619032816, 1999994925262821, 1999997722461903, 1999998954882685]
private def pvn_m8_r512_6_3_p6 : List ℕ :=
  [1999999506544546, 1999999761807721, 1999999884216054, 1999999944227880, 1999999973678254,
    1999999987878993, 1999999994535509, 1999999997563831, 1999999998910687, 1999999999505072,
    1999999999770258, 1999999999891650, 1999999999948806, 1999999999976170, 1999999999989232,
    1999999999995327, 1999999999998070, 1999999999999245, 1999999999999723, 1999999999999906,
    1999999999999972, 1999999999999994, 1999999999999999]
private def pvn_m8_r512_6_3 : List ℕ :=
  pCat pvn_m8_r512_6_3_p0
    (pCat pvn_m8_r512_6_3_p1
    (pCat pvn_m8_r512_6_3_p2
    (pCat pvn_m8_r512_6_3_p3
    (pCat pvn_m8_r512_6_3_p4
    (pCat pvn_m8_r512_6_3_p5
      pvn_m8_r512_6_3_p6)))))
private def pvn_m8_r512_6_4_p0 : List ℕ :=
  [2000064194490833, 2000101175698340, 2000063933728975, 1999909022636960, 1999917241360449,
    2000133982656342, 2000046054009253, 2000002336783610, 1999962927495568, 1999891881105923,
    1999895442293379, 1999811765412389, 1999865057624686, 1999927283397703, 2000141169032858,
    2000135395308916, 2000029471393027, 2000017138493833, 1999959987502686, 2000014570920416,
    2000175278796482, 2000201870041634, 2000058229529288, 2000023257043049, 2000024189984711,
    2000060066940088, 2000052380121517, 2000013982691805, 2000030401520148, 2000038395588477,
    2000006666694321, 1999931680655867, 1999947779799381, 1999993094208659, 2000070260076704,
    1999929364647720, 1999973700063885, 1999969926366310, 2000113421943443, 2000064084781384,
    2000027523797031, 2000101701431855, 2000028109310863, 2000017707321978, 1999923539131732,
    1999913938846955, 2000089261829160, 2000001664433871, 1999959366122731, 1999989092501937,
    1999944333281952, 1999992576728465, 1999976758526118, 1999877132379591, 1999947383390768,
    2000064146814443, 2000102158764273, 2000034032160193, 2000142144876886, 1999941047237120,
    1999857096163127, 1999967691731790, 2000126855126297, 2000013426148738]
private def pvn_m8_r512_6_4_p1 : List ℕ :=
  [1999921842060656, 2000019851108347, 1999930599688091, 2000002657292810, 1999993137728303,
    1999996466273393, 1999878879791212, 1999960239758439, 1999982703399509, 2000040024398042,
    1999889818224620, 1999970777308001, 1999957896247544, 2000079291605860, 2000045403008253,
    1999843950237832, 1999885191768323, 1999894714007674, 1999882559290071, 1999862634950443,
    2000026603826569, 1999902066751972, 2000017188015802, 2000028127897518, 2000024968743518,
    2000011096280522, 2000095356426857, 2000021283507843, 1999980858796204, 1999985501094136,
    2000063596866735, 1999930005114129, 2000090347038940, 2000006209217502, 2000192344025928,
    2000040242605757, 1999978294854259, 1999803159314327, 1999952726432071, 1999791730442820,
    1999868965849454, 2000111368378774, 2000147792687613, 2000046793886344, 1999887633612768,
    2000057067881085, 2000145358332734, 1999982868309644, 1999993689970115, 2000011435741126,
    1999953300742593, 2000126899808655, 1999812100452438, 1999885262387818, 2000002567757993,
    1999941687045142, 1999978981242681, 1999965177447765, 2000099121474928, 2000009581148734,
    2000141401516549, 2000027329045008, 2000034803358074, 2000164909748067]
private def pvn_m8_r512_6_4_p2 : List ℕ :=
  [2000067262798222, 2000026232870579, 1999915740954533, 1999978564631067, 2000021028032834,
    2000058685076685, 1999880955604459, 2000043810268823, 1999880820857614, 2000312379200951,
    2000012763781931, 1999923180960466, 2000036777773394, 2000113386620974, 2000012670766826,
    1999929692397952, 2000014286300015, 2000034956108337, 2000038612504614, 1999988226028497,
    1999915167464906, 1999877991703790, 1999993886059018, 2000185742852874, 2000006132794482,
    1999954285903759, 1999941614757472, 2000070923743375, 1999960272055904, 1999831731209239,
    2000122543514411, 1999931667829841, 2000110678590979, 2000000675941298, 1999768300082662,
    2000166980946268, 2000189703602239, 2000043454955850, 2000167012584726, 1999999066607341,
    1999984490499360, 1999937592933753, 2000076852168484, 1999714306278057, 2000135347059798,
    1999924971813300, 2000037809293027, 2000022601454777, 2000036377509031, 1999862579705171,
    2000015843677084, 2000087418563777, 2000111879318628, 1999884128793010, 1999913724894659,
    1999937564298014, 1999988455174715, 2000087753998491, 2000015046421706, 1999911089895722,
    2000175143076880, 1999687224042136, 2000184001472264, 2000160665712016]
private def pvn_m8_r512_6_4_p3 : List ℕ :=
  [2000092657215161, 2000078512860713, 2000095137441867, 1999861949127837, 1999794512464415,
    1999957656720265, 1999949785562150, 1999910920438282, 1999871638121690, 2000114527242623,
    1999966538435550, 2000129997331299, 1999722382389397, 2000120685543345, 2000248156507743,
    1999653807991059, 2000384458496360, 2000041158775733, 1999973065305142, 2000141109096690,
    2000001750936929, 1999775389023991, 2000134206023474, 1999839064013665, 2000171965000670,
    1999814242841530, 2000035172352211, 2000010785909619, 1999931624828433, 1999692654659514,
    2000071199654702, 2000049076427621, 1999941188002537, 1999985222498829, 1999679517249605,
    1999860781450569, 1999873844159469, 1999983704310235, 1999832673467745, 1999828394703293,
    1999894449776363, 1999862053559634, 2000166062347338, 1999601404321084, 2000256829485884,
    1999821361118332, 2000356055964656, 1999980196719056, 2000610702010196, 1999871617248779,
    2000352104662861, 1999271989551735, 2000404895829916, 1999758964677694, 2000069353394274,
    2000079322226554, 1999723062361850, 1999972761662562, 2000224887765941, 2000153429044155,
    1999819961736389, 2000326033269425, 1999953895680661, 1999924832381785]
private def pvn_m8_r512_6_4_p4 : List ℕ :=
  [2001021566234457, 1999302303457452, 2001457993016068, 1999082621966017, 2000293744685325,
    2000970276940557, 1998525872842712, 2001156170889005, 1999726086470440, 1999081033819094,
    2000328826131827, 1999281752050658, 2000383672361952, 2000014513586241, 1999571022857481,
    2000436217941076, 1999886452410999, 2000555313760007, 2000007105835120, 1999412986101411,
    2001373983560368, 1999863929268048, 1998808383788006, 2001504940282708, 1999844131012370,
    1998431628612542, 2001754968273513, 2000384955251312, 1997906676334880, 2001276194209420,
    2001324343873215, 1998016114639945, 2000603684394538, 2002007032478394, 1998288569221994,
    1999328261218756, 2003245274980954, 2000128369283439, 1997347860187296, 2001109930734205,
    2002031740211497, 1998036641887081, 1998418554873999, 2001793556591275, 1999891149653808,
    1997658382687729, 2001274810367497, 2003229885076112, 1998709207209402, 1996207496401194,
    2000694980446486, 2003684832723095, 1999784133208841, 1996611776341822, 1999411680391519,
    2002362711388446, 2000827675787146, 1998615439511752, 1999465394919656, 2000693965154654,
    1999615601343387, 1999353763997183, 2002302258719127, 2003941013568678]
private def pvn_m8_r512_6_4_p5 : List ℕ :=
  [2000016348719919, 1994955626512094, 1996459027051470, 2003927607743503, 2007825261046860,
    2001754642864690, 1991669868512075, 1989518654995904, 1998720309641357, 2009673891018596,
    2010421869296060, 1999490995891105, 1987222735611250, 1985410182554501, 1996095640775700,
    2009935321453297, 2014902058694974, 2006637854281079, 1991384154428742, 1980301244298430,
    1981050443087962, 1992958977783266, 2008136063873789, 2016874635528217, 2013504068613974,
    1999153584316973, 1980382778042598, 1965370473404652, 1960180245859362, 1966602387189416,
    1981848820654957, 1999794568092413, 2013147096783277, 2015651571295710, 2003545198302402,
    1976033173962201, 1935063071213521, 1884727484961673, 1830427424759961, 1777875778031534,
    1732146588253133, 1697022522713997, 1674737118652344, 1666009279648853, 1670216589313031,
    1685642725029012, 1709812043584994, 1739901765981022, 1773150533602810, 1807159560248091,
    1840037307390003, 1870416567463132, 1897410114805202, 1920554081931818, 1939750036806570,
    1955194637427284, 1967290163733237, 1976545779540810, 1983489445272491, 1988606850035114,
    1992311788245473, 1994941307739646, 1996764266078948, 1997993522424559]
private def pvn_m8_r512_6_4_p6 : List ℕ :=
  [1998796489250277, 1999302846159872, 1999610335086029, 1999789867584450, 1999890591159495,
    1999944906851518, 1999973095360823, 1999987207172142, 1999994046428653, 1999997271303645,
    1999998760214885, 1999999438322601, 1999999745268437, 1999999884208101, 1999999947311191,
    1999999976066672, 1999999989177875, 1999999995136647, 1999999997827661, 1999999999033864,
    1999999999571113, 1999999999809592, 1999999999915444, 1999999999962525, 1999999999983500,
    1999999999992825, 1999999999996940, 1999999999998729, 1999999999999490, 1999999999999806,
    1999999999999931, 1999999999999977, 1999999999999995]
private def pvn_m8_r512_6_4 : List ℕ :=
  pCat pvn_m8_r512_6_4_p0
    (pCat pvn_m8_r512_6_4_p1
    (pCat pvn_m8_r512_6_4_p2
    (pCat pvn_m8_r512_6_4_p3
    (pCat pvn_m8_r512_6_4_p4
    (pCat pvn_m8_r512_6_4_p5
      pvn_m8_r512_6_4_p6)))))
private def pvn_m8_r512_6_5_p0 : List ℕ :=
  [2000017750734832, 2000028207976683, 2000066021320517, 2000173887096175, 2000008263331822,
    1999896329473308, 1999972419636571, 1999985746934835, 2000082175552226, 2000036753286167,
    2000051399429613, 1999997206059380, 1999952139270215, 1999996433842662, 1999895372709164,
    1999784239082173, 1999815058610886, 1999927962820153, 1999970417018282, 2000087265610299,
    2000142754818208, 2000047695697049, 1999953624425027, 1999935287536080, 2000040369587246,
    2000118854661867, 2000165590261246, 2000067800568719, 2000098430392956, 2000020027059143,
    2000106835772028, 2000023588925718, 2000003851165852, 2000051626807488, 2000050834889041,
    2000107710286656, 1999971448450998, 1999909438603487, 2000024579861505, 1999992790646931,
    2000024462806758, 1999973007720053, 1999899882414053, 2000022372648135, 2000030339549838,
    1999945510217132, 2000043795974531, 2000082888712094, 2000125165326879, 2000043767237026,
    2000049046323556, 1999904943082170, 1999996808097395, 2000069508204233, 1999971144901462,
    1999945386863470, 1999994249011338, 2000081758508448, 1999902639730766, 2000006873340769,
    1999992818421643, 1999897850998120, 1999806640642235, 2000041880934957]
private def pvn_m8_r512_6_5_p1 : List ℕ :=
  [2000089990952353, 2000140264519878, 2000008449867808, 2000008801404823, 1999961785322399,
    1999936160348413, 2000085335736270, 2000004733449101, 2000003325293979, 1999936123553040,
    2000001057242077, 1999975441875138, 2000103884587800, 1999910190851879, 1999883106296225,
    2000006404827254, 2000045190361101, 1999922902355462, 1999962818251954, 1999900807982996,
    1999982023710593, 1999944086268792, 2000141867948256, 1999922852174735, 2000029015192670,
    1999925105956548, 1999940531282297, 1999820777986907, 1999927424748085, 1999894079752834,
    1999916421742991, 1999964902707004, 1999882384266126, 2000046654148748, 2000057672653060,
    1999971462538548, 2000017020710196, 2000091129745841, 2000061197550928, 1999988639125872,
    1999841253136902, 2000139376144250, 1999985538007098, 1999947975744736, 2000199095664163,
    2000126121252209, 2000149188488704, 1999877190116222, 1999799304048117, 1999827595030035,
    2000023023378524, 1999985224911528, 1999859776571704, 2000072459432133, 2000038033275296,
    2000060262536968, 1999995887401487, 2000041329397533, 1999968335453588, 2000178970311396,
    1999918613228527, 2000106827883777, 1999868506434625, 2000032673465107]
private def pvn_m8_r512_6_5_p2 : List ℕ :=
  [1999977687003336, 1999826194718299, 1999956545588496, 1999961604876908, 1999989343154130,
    2000049473464369, 1999998394979223, 1999929265270130, 2000104343599933, 2000247478671797,
    2000047947964633, 1999968052848573, 2000013489340962, 2000182427332360, 2000005196469644,
    1999913853786440, 1999984059339612, 1999919832267968, 2000095517626714, 1999945950128863,
    2000075746436718, 1999992612760687, 1999990477422214, 2000268921611706, 1999943254956050,
    1999848339276295, 2000141429397593, 1999970088795749, 2000187017981904, 1999950203610118,
    1999948046555434, 1999838896597716, 2000213123372265, 1999791291701705, 1999991884583168,
    2000102489497035, 2000056524430521, 1999997071199179, 2000003204105638, 1999828597855410,
    2000023159536010, 2000083201320419, 2000017645855966, 1999913045541191, 1999962307020415,
    1999948073865587, 2000013358541758, 1999970286911350, 2000294551160377, 1999878338216880,
    2000241139906507, 2000067987126055, 2000012985019057, 2000038596432176, 1999814185334891,
    1999921010056976, 2000142154829032, 2000024644171335, 1999832611057251, 2000060979663146,
    1999914013044930, 2000034257334589, 1999992744257243, 2000223062312271]
private def pvn_m8_r512_6_5_p3 : List ℕ :=
  [1999886126879580, 1999855913891452, 2000128234340898, 1999731264550888, 2000271189821009,
    1999849853149853, 2000059217869503, 2000097465817160, 1999702452824059, 1999873021592839,
    2000456767125624, 1999797996045996, 2000222867958734, 2000102779842213, 2000083070460076,
    1999939174500961, 1999949217521044, 1999852594686357, 1999929041508401, 1999911679770599,
    1999954737378814, 2000072505512853, 1999787569820484, 2000132229498928, 2000007730004287,
    1999852114881036, 2000008285378711, 2000081634186652, 2000201964850367, 1999876039998015,
    2000320036591321, 1999774378636100, 2000370330429963, 1999631101757710, 2000178346536815,
    1999731429534721, 2000373132557946, 1999708336871770, 2000379062407895, 1999384659065226,
    2000197148806650, 1999865572666758, 2000074786439993, 2000086114996053, 1999652931477628,
    2000119147413928, 1999881560178329, 1999766327068692, 1999945983222254, 1999906806415667,
    1999868000788675, 1999502198815777, 2000671936515552, 1998926720087720, 2000890483665397,
    1999221521419383, 1999640453492241, 2000824954030413, 1999131133022755, 2001433816009632,
    1999585765296107, 1999668088577687, 2001146383900120, 1998908637750868]
private def pvn_m8_r512_6_5_p4 : List ℕ :=
  [2000498658742325, 2000366574921205, 1999125644159575, 2000357230022350, 1999866025188659,
    2000118964353095, 2000102270636697, 1999664454492155, 2000490147085249, 1999657239562659,
    1999937241247732, 2000810904252672, 1999704920586254, 2000574206440932, 2000532764737917,
    1998945430041387, 2001117128449415, 2001034938509247, 1998348865639732, 2000505776823185,
    2001181815560844, 1998003221813458, 1999978262152280, 2001422829696462, 1998298923647654,
    1999461363517043, 2002056890316077, 1998970805704420, 1998632554456866, 2002198312593514,
    2000269416095835, 1998154228448391, 2001387263593828, 2001411422493068, 1997869824965459,
    1999763008539518, 2002643656176454, 1999208870042185, 1997579367041405, 2001613196232168,
    2001881496356671, 1998161303888467, 1999047214475287, 2002057033943746, 2000205295744481,
    1998074134034348, 2001031935974756, 2002609311271625, 1998941227849919, 1997850769448703,
    2002000728957775, 2002912049641679, 1998224343885208, 1996358577266515, 2000437356657220,
    2003020773687177, 2000141927129798, 1997670457073434, 1999636526344617, 2001645612627847,
    2000300087404690, 1998954395760802, 2000097117583215, 2000748244602250]
private def pvn_m8_r512_6_5_p5 : List ℕ :=
  [1999030381906967, 1998324667101436, 2001016712412042, 2003160090951412, 2000232252064003,
    1995413665953202, 1996247807511881, 2003202273594892, 2007482235134021, 2002654090770274,
    1994032533883056, 1992509609093648, 2000801190837187, 2009646077829356, 2008436763787588,
    1997536158654443, 1988206677829248, 1990458097832656, 2002355282175299, 2012101719908768,
    2010019045924931, 1997741393349828, 1986178161104551, 1985403757318749, 1996170999375301,
    2009793672252006, 2015490286169319, 2008728980083660, 1994206500693477, 1981893822014928,
    1979866638515436, 1989281752986026, 2004319152352807, 2016133943757967, 2017839072134520,
    2007820045456098, 1990121683523409, 1972184850539489, 1961335329912496, 1961773300404107,
    1973239828012138, 1991483454916034, 2009870125981780, 2021340408182560, 2020167935876397,
    2003205036813394, 1970416080738914, 1924642178444809, 1870767762136144, 1814631790170861,
    1762010009795604, 1717834679623620, 1685672848195917, 1667445526805950, 1663394349725631,
    1672299027229148, 1691891097383756, 1719347208693530, 1751736202227386, 1786344338109475,
    1820870139798467, 1853520673921515, 1883043328984227, 1908710035691502]
private def pvn_m8_r512_6_5_p6 : List ℕ :=
  [1930258359802690, 1947795573957487, 1961681476256418, 1972412214117217, 1980524826440725,
    1986532594416115, 1990890536335136, 1993983405533890, 1996126781939487, 1997573799664838,
    1998523263755014, 1999127541110323, 1999499996291780, 1999722096641563, 1999850168278112,
    1999921585389868, 1999960118467327, 1999980255799329, 1999990464842669, 1999995496278379,
    1999997913208015, 1999999048373150, 1999999571494972, 1999999808904653, 1999999915391208,
    1999999962743133, 1999999983667159, 1999999992868585, 1999999996898224, 1999999998655998,
    1999999999419767, 1999999999750380, 1999999999892997, 1999999999954323, 1999999999980612,
    1999999999991834, 1999999999996600, 1999999999998608, 1999999999999443, 1999999999999786,
    1999999999999923, 1999999999999976, 1999999999999994]
private def pvn_m8_r512_6_5 : List ℕ :=
  pCat pvn_m8_r512_6_5_p0
    (pCat pvn_m8_r512_6_5_p1
    (pCat pvn_m8_r512_6_5_p2
    (pCat pvn_m8_r512_6_5_p3
    (pCat pvn_m8_r512_6_5_p4
    (pCat pvn_m8_r512_6_5_p5
      pvn_m8_r512_6_5_p6)))))
private def pvn_m8_r512_6_6_p0 : List ℕ :=
  [1999999235402051, 2000041018974831, 1999966357046543, 1999982041271892, 2000149011017709,
    2000109423847216, 2000088597658116, 1999988444891329, 1999929615199241, 1999975734606120,
    1999962926727771, 2000006225858506, 2000069201208957, 2000073580533155, 1999984296451940,
    2000001912616493, 2000070392784262, 2000007983607790, 1999946702795837, 1999875933966960,
    1999869170420540, 1999778482233658, 1999873074687101, 1999895446161677, 2000087314205307,
    2000112936553238, 2000059337230556, 2000022047108166, 1999907647193413, 1999980296719698,
    2000060190120661, 2000061182400774, 2000137516373754, 2000055394432006, 2000062950634443,
    2000156050778808, 2000067094055906, 2000001566468319, 2000041052985999, 1999990019473110,
    2000126312045713, 2000092971137311, 2000030821438353, 1999924136450186, 2000030271558270,
    2000049102228154, 1999954090915996, 2000016561192263, 1999953391515414, 2000004593747117,
    1999953949767486, 2000037299688721, 1999896161113568, 1999942499376018, 2000064855906917,
    2000186347800888, 1999990060758291, 2000038661506971, 2000081971288292, 2000007278054591,
    1999992110322434, 1999959630920026, 2000097765488168, 1999939430763023]
private def pvn_m8_r512_6_6_p1 : List ℕ :=
  [1999945832633583, 1999980032664768, 2000109425257507, 1999997217471406, 2000007990035781,
    1999888478387289, 1999838218699296, 1999910910828811, 2000050187040365, 1999995821906848,
    2000166895687854, 1999984617840300, 1999998447477613, 1999901449091336, 2000162702194037,
    1999994010636807, 1999964649939955, 1999952166852061, 2000021975303480, 2000010589946805,
    2000022779397371, 2000032140151899, 1999878199469270, 1999990091469298, 2000016544405185,
    1999984825475746, 1999995908562058, 1999950976223233, 1999874571486086, 2000020894812162,
    1999886870520458, 2000004932433083, 2000035492937617, 2000012412804227, 2000103913237582,
    1999805315455380, 1999999893126901, 2000006501737710, 1999841931998839, 1999825802881408,
    1999932856299082, 1999997343286331, 1999836178989291, 1999975579571366, 1999925454254003,
    2000074171135841, 2000016651431220, 2000053091567980, 1999905791267816, 2000253581558689,
    1999931732894823, 1999917211269868, 1999862608058642, 2000002731302181, 2000239335440158,
    2000105938187279, 2000108822188930, 2000038888529676, 1999942145653715, 1999979055436328,
    1999902214213285, 1999833581734529, 1999918154944426, 2000055996382862]
private def pvn_m8_r512_6_6_p2 : List ℕ :=
  [1999932906805072, 2000007738209229, 2000015006193502, 1999990418213445, 2000071728338902,
    2000020064533797, 2000100621780547, 1999896198520515, 2000127230549864, 2000137242019021,
    1999890970807336, 1999894189783330, 1999890206811213, 2000059879731419, 2000055818723877,
    1999687189126749, 2000105692685798, 1999879508798484, 2000089644205042, 2000051863584265,
    2000121027595032, 1999857361570240, 2000235561642824, 2000134025220739, 2000007968360338,
    2000050616735287, 1999986170514460, 1999958708887677, 2000163961566336, 1999874603478094,
    1999836576397064, 2000065464203759, 2000166083793450, 1999981803286456, 2000084364550301,
    1999876511306500, 2000159117130486, 1999922093974008, 2000168166790815, 1999940001706950,
    2000016199889285, 2000214107047752, 1999860300298981, 1999902826945999, 1999970989367249,
    1999979852201343, 2000026903594066, 2000163165691335, 1999853131481858, 2000067366307549,
    1999916160858294, 1999961421479387, 2000113034664001, 1999982467193832, 2000054610006765,
    1999682842264440, 2000299930099747, 1999808993022109, 1999881224764014, 2000091063918818,
    2000033314777061, 2000087777721555, 2000348813806430, 1999788056720206]
private def pvn_m8_r512_6_6_p3 : List ℕ :=
  [2000279719333545, 1999823146540564, 1999899042930721, 2000251888940042, 1999962729564627,
    1999794780031343, 2000064746835302, 2000003839413196, 1999801641175731, 2000146783594082,
    2000067444722964, 2000113439999067, 1999864169000494, 1999837471679347, 2000161238830388,
    1999855598530434, 2000201052222499, 1999844616859967, 2000198723207830, 1999555799860210,
    2000359050671282, 1999608948415228, 2000232458980151, 1999843051778013, 2000495808540582,
    1999753487477121, 2000388186964164, 1999714782350944, 2000251159331164, 1999843032581844,
    1999741703225682, 2000152554926685, 1999772320859032, 2000124168004255, 1999925478174200,
    1999814702108696, 2000178778197044, 1999707597292018, 2000324058117949, 1999522886942040,
    2000632249418295, 1999421672509236, 2000918401317277, 1999680093211991, 1999509225151374,
    2000961683980430, 1998925567579652, 2000948566996305, 1999772180655869, 1999477816130867,
    2000921637723046, 1998869841714877, 2000560460987046, 2000152732368989, 1999197246276981,
    2000925106218093, 1999356552571978, 1999754314213300, 2000683933715796, 1999374612953386,
    1999893014731104, 1999853257817575, 1999841721169320, 2000188281050863]
private def pvn_m8_r512_6_6_p4 : List ℕ :=
  [1999617636274194, 2000189151182490, 1999653691392527, 1999168375400460, 2000700266443243,
    1999863210823829, 1999626786761769, 2000917204461767, 1999623908117619, 1999833148631672,
    2001292493950214, 1999113737909614, 1999661321566436, 2001456441323499, 1998807627588406,
    1999111903635201, 2001997704448490, 1999520847310533, 1998378178526194, 2001560547596429,
    2000073474954901, 1998368978987146, 2001499860353978, 2000863878058510, 1998181877527660,
    2000797761650699, 2001884760663705, 1998591535044430, 1999639091264004, 2002357373763481,
    1999483570601861, 1998203142028251, 2001551404521520, 2000677562148740, 1997601361289497,
    2000018204579029, 2002101365740857, 1998766839021223, 1997917282817885, 2001731204569615,
    2001587488953241, 1998088784836948, 1999356829026031, 2002261836543014, 2000178667648987,
    1998150906763575, 2000780329700034, 2001850193355919, 1998677511354837, 1998210708772670,
    2001849006052679, 2002084672798711, 1998049955552499, 1997672138465277, 2001890382311607,
    2002680388576456, 1998650093695075, 1997410993591810, 2001021964281252, 2002930758451168,
    2000484728028683, 1998589494411989, 1999851877890709, 2000832163798562]
private def pvn_m8_r512_6_6_p5 : List ℕ :=
  [1999573401630034, 1998992496815060, 2000570183037578, 2001125355211550, 1999001603009250,
    1997978044470225, 2000795720978069, 2003343978580020, 2000704652969050, 1995898849464437,
    1996366207703462, 2002578254820035, 2006224843445406, 2001490362036236, 1993702514376994,
    1993036160432822, 2001243542594374, 2008747493762332, 2006164299456394, 1996001973653887,
    1990053682039741, 1995647528368800, 2007126386718341, 2012127761908543, 2005004451197507,
    1992623175374157, 1987132520806531, 1993904671457898, 2006614335934529, 2013470859582385,
    2008068218918629, 1994848320095116, 1984860621194718, 1986274006055290, 1997983335542393,
    2011036239587210, 2015779952679694, 2008731314328558, 1994486216141725, 1982178956942519,
    1979493775437576, 1988135791266249, 2003187107226683, 2016222117726178, 2019985911213099,
    2011939808071298, 1995082478482261, 1976175731298588, 1962675375835996, 1959832636339665,
    1968930697308294, 1986998769290386, 2007861411090273, 2024037715425686, 2028813450598561,
    2017849559055131, 1989965483234014, 1947090378938310, 1893613383571713, 1835414678936565,
    1778800216866101, 1729505363642194, 1691910842160597, 1668587926497411]
private def pvn_m8_r512_6_6_p6 : List ℕ :=
  [1660219957536173, 1665848815268260, 1683319770719642, 1709783111538505, 1742149359469519,
    1777450274781162, 1813097241513578, 1847043047917365, 1877853571030512, 1904696968087805,
    1927265308390049, 1945653088820420, 1960221777430323, 1971476019724297, 1979967348976759,
    1986229990604262, 1990744901548568, 1993924274643257, 1996108681824957, 1997571000157133,
    1998523562340587, 1999126665689610, 1999497480992201, 1999718762988285, 1999846892831347,
    1999918887133305, 1999958155775948, 1999978961017445, 1999989678104326, 1999995051786442,
    1999997678336609, 1999998931919020, 1999999517255050, 1999999785204156, 1999999905722355,
    1999999959102059, 1999999982434557, 1999999992519487, 1999999996837354, 1999999998671296,
    1999999999444916, 1999999999769320, 1999999999904626, 1999999999960782, 1999999999983976,
    1999999999993505, 1999999999997395, 1999999999998973, 1999999999999603, 1999999999999856,
    1999999999999951, 1999999999999986, 1999999999999998]
private def pvn_m8_r512_6_6 : List ℕ :=
  pCat pvn_m8_r512_6_6_p0
    (pCat pvn_m8_r512_6_6_p1
    (pCat pvn_m8_r512_6_6_p2
    (pCat pvn_m8_r512_6_6_p3
    (pCat pvn_m8_r512_6_6_p4
    (pCat pvn_m8_r512_6_6_p5
      pvn_m8_r512_6_6_p6)))))
private def pvn_m8_r512_6_7_p0 : List ℕ :=
  [1999975480405573, 2000017667842383, 2000070804703100, 1999945145464380, 1999958568893988,
    2000015546659223, 2000049483976207, 2000135699116595, 2000117271802109, 2000054115214141,
    2000000721755547, 1999995787915320, 1999965292152225, 1999904093043601, 2000000770743765,
    2000042144452362, 2000078153861522, 1999963764146939, 2000045654101747, 2000018503152511,
    2000051404042846, 2000056071496782, 1999972603027450, 2000000664579529, 1999926689156309,
    1999819128996665, 1999835097145326, 1999783118339396, 1999889126601914, 2000044214947917,
    2000059176572486, 2000076007602427, 2000076245851060, 1999892082816954, 1999985089804191,
    2000006124118273, 2000048607625557, 2000036283773401, 2000055828854719, 2000088375572674,
    2000058018476980, 2000204977630881, 2000051970750588, 2000008243440489, 1999967443206227,
    2000118851823833, 2000066903868557, 2000076796269254, 2000026660605607, 2000053923991719,
    1999971604492462, 2000017400056039, 2000108979289960, 1999904457396759, 1999970001404895,
    2000002993926271, 2000108134420558, 1999927153608603, 1999907465951430, 1999929607074672,
    2000042364440815, 1999957251976175, 2000024228164824, 2000100306434040]
private def pvn_m8_r512_6_7_p1 : List ℕ :=
  [2000125199492917, 1999940868656210, 2000105511547396, 1999959787697252, 2000104803563143,
    1999991200680928, 2000026268833402, 1999873918410832, 1999992534283977, 2000064061105586,
    2000028524019802, 2000063599027329, 2000022240562264, 1999932253034802, 1999759717025583,
    1999927335423119, 2000042679242323, 2000018123193676, 2000011580292978, 2000039937361903,
    1999921777692477, 2000106588515267, 2000046214114031, 1999979263878126, 2000047293390952,
    1999866374952366, 2000089370632012, 2000004554708887, 2000017505137588, 2000034717109194,
    1999885407208312, 2000022167514008, 2000007938532547, 2000005828581245, 1999887541500735,
    2000134662809351, 1999936073276971, 1999895204732510, 1999826082321236, 2000119668209014,
    1999885208193714, 2000043325583199, 1999984762263143, 1999976331259138, 2000135543165055,
    1999911797986707, 1999900476125368, 1999935728221872, 1999947200134737, 1999950204413660,
    1999793830082411, 1999880708128692, 2000005416609713, 1999982778406727, 1999849913315339,
    1999965399014753, 2000030501323007, 2000090428960991, 2000204241869529, 1999906413247385,
    1999920291109924, 1999886474807599, 2000033412299624, 2000029582952517]
private def pvn_m8_r512_6_7_p2 : List ℕ :=
  [2000018427213368, 2000208146811077, 2000101581032464, 2000015473705478, 2000169333218245,
    1999764595240610, 2000037412164586, 1999792771379207, 2000076560707098, 1999910136420888,
    1999880396764409, 1999915969051916, 2000224449421437, 1999940992035888, 1999870073379621,
    2000083866501151, 2000069722185244, 2000043019364874, 2000198543619556, 1999882565402900,
    1999945780426704, 2000065264071744, 2000042926783050, 1999852543206969, 2000055036617923,
    1999711468743022, 2000080858410250, 1999986995394317, 1999989081803580, 1999894536963976,
    1999969100741418, 2000278350917711, 1999982688793743, 2000050831368063, 2000065326264976,
    2000072706615215, 2000104443644979, 2000165708394906, 1999754371500662, 2000002083815995,
    2000068415268632, 1999901161789972, 2000143333547523, 1999854640966807, 2000221187710586,
    1999883669681460, 2000155392068754, 1999859473535698, 2000023656397499, 2000197147597467,
    2000041919775396, 1999926793221072, 2000313955620616, 1999589487805866, 2000048065838351,
    2000084998870540, 1999939223222332, 2000141611132798, 1999867202758899, 1999944712544204,
    2000147857474413, 1999956795198209, 1999843094016996, 2000234721486487]
private def pvn_m8_r512_6_7_p3 : List ℕ :=
  [1999907192847684, 1999905443869830, 2000206725422458, 1999776187408194, 1999977821094662,
    1999684186004477, 2000395405883248, 1999832696591312, 2000346279359961, 1999759183477695,
    2000489709914612, 1999610509802301, 2000273967283078, 1999875741950000, 2000330498094989,
    1999647455735538, 2000197281546952, 1999720864425269, 1999962085449071, 2000234289309732,
    1999872965723019, 2000191489488436, 1999799225245098, 1999973578683266, 2000204009512907,
    1999617109637739, 2000412632813634, 1999650212948781, 2000518117087988, 1999381093635729,
    2000398702023720, 1999543055253013, 2000102265927480, 2000305519317765, 1999256886245850,
    2001177046514516, 1999252804372929, 2000417319411376, 2000506232914071, 1998880363700091,
    2001022475571567, 1999408807959343, 1999867661284269, 2000526439189815, 1999013543493328,
    2000821028389659, 1999820086542957, 1999345950080616, 2000678291267966, 1999351077856493,
    2000178123211178, 2000563901684353, 1999526328666137, 2000303486317294, 2000038422621614,
    1999851379758895, 2000174775749356, 1999886217462513, 2000449833301830, 1999698973916443,
    1999625656656543, 2000684480655179, 1999599288252861, 1999649758240284]
private def pvn_m8_r512_6_7_p4 : List ℕ :=
  [2000771771096140, 1999205660700696, 1999891100007312, 2001005294433981, 1999104493461580,
    1999869934514002, 2000671531854511, 1998727784766453, 2000127994969453, 2001344756354847,
    1998499526289488, 1999508219774226, 2001547288239420, 1998554122844745, 1998939885054204,
    2001878835025230, 1999445860259063, 1998529922077267, 2001665540802240, 2000479458248577,
    1998552351808434, 2001196082666049, 2000883847813078, 1998025824445135, 2000340781352019,
    2001895719881024, 1998575014913623, 1998969255942122, 2001908324393765, 1999758187225513,
    1998075274240329, 2001216345887746, 2001381547247969, 1998190696925066, 1999625179718590,
    2002334801936139, 1999754310731987, 1998162661615712, 2001588436311495, 2002040946171207,
    1998399611107318, 1998876032663819, 2001974955077441, 2000480716830032, 1997883756835787,
    1999870081876121, 2001643860483119, 1999152781297399, 1998124029082464, 2001166718288145,
    2001769684537223, 1998428616767021, 1998282223001589, 2002081353382575, 2002229283279829,
    1998224800612785, 1997773748300853, 2001637781907378, 2002489820141566, 1998997975317088,
    1997675514283427, 2000499713832906, 2002098149918650, 2000065774296315]
private def pvn_m8_r512_6_7_p5 : List ℕ :=
  [1998515791813425, 1999811593424512, 2000866295776427, 1999878727891261, 1999652289688831,
    2001417797004112, 2001772867397978, 1999190690114935, 1997789318577822, 2000439120955763,
    2003027062835364, 2000683176499295, 1996280057968307, 1996826114217228, 2002544815225854,
    2005501729006623, 2000727850706120, 1994029255156350, 1994742076940586, 2002826864941384,
    2008101433140059, 2003258395722709, 1993675134737074, 1991077108602481, 1999051774577491,
    2008519141713027, 2008424429264879, 1998558484941934, 1989757967119671, 1991875063771713,
    2003165073321267, 2012215580049192, 2009766133314199, 1997960971245229, 1988025163639145,
    1989303147353018, 2000614896606706, 2011739443237194, 2012823362601482, 2002766877733952,
    1989660014208134, 1983827065516959, 1989759844521335, 2003095284230853, 2014218219131972,
    2015229452615794, 2005197321103502, 1990413684867075, 1980033329445941, 1980347834066751,
    1991305534371811, 2006955068412538, 2018957327526850, 2020861611864087, 2010988229188352,
    1992892214009152, 1973610364825584, 1960694429401827, 1959296051228873, 1970357177270817,
    1990405326001866, 2012790777996399, 2029723161466821, 2034347348655032]
private def pvn_m8_r512_6_7_p6 : List ℕ :=
  [2022296529912115, 1992472740388146, 1947053973340944, 1890864210714777, 1830314222596081,
    1772168751553375, 1722410129116099, 1685419395245117, 1663584878657444, 1657319405449164,
    1665375448288620, 1685318592827067, 1714041006170615, 1748236371739743, 1784791071654377,
    1821066759658791, 1855063242929771, 1885464988232759, 1911590416408916, 1933275809011611,
    1950730201673781, 1964392947243457, 1974814752214505, 1982570807774947, 1988205125686177,
    1992200001295390, 1994963185946253, 1996826326718158, 1998049996683201, 1998832239926282,
    1999318660834776, 1999612756041443, 1999785605731940, 1999884356944371, 1999939207806777,
    1999968838861654, 1999984415213098, 1999992388633572, 1999996366580283, 1999998302781174,
    1999999223281964, 1999999651282189, 1999999846188332, 1999999933249927, 1999999971456186,
    1999999987954909, 1999999994977073, 1999999997927399, 1999999999152810, 1999999999656628,
    1999999999861909, 1999999999944877, 1999999999978159, 1999999999991416, 1999999999996663,
    1999999999998722, 1999999999999521, 1999999999999828, 1999999999999943, 1999999999999984,
    1999999999999997]
private def pvn_m8_r512_6_7 : List ℕ :=
  pCat pvn_m8_r512_6_7_p0
    (pCat pvn_m8_r512_6_7_p1
    (pCat pvn_m8_r512_6_7_p2
    (pCat pvn_m8_r512_6_7_p3
    (pCat pvn_m8_r512_6_7_p4
    (pCat pvn_m8_r512_6_7_p5
      pvn_m8_r512_6_7_p6)))))
private def pvn_m8_r512_6_8_p0 : List ℕ :=
  [1999989495715898, 1999943405506408, 2000036200174888, 2000067440891667, 1999995899828190,
    1999986379298086, 1999963781216214, 1999959704253612, 1999999979594741, 2000054299692008,
    2000144780308019, 2000069873534291, 2000089250734842, 2000028347427377, 2000080798913256,
    1999965905254065, 1999903015208837, 1999973736676255, 1999975434244536, 2000032350925238,
    2000052122411088, 1999965416527653, 2000032192012175, 2000039965530271, 2000010362845595,
    2000050491509322, 2000065835550267, 1999972703266230, 2000085516465864, 1999962307675409,
    1999881036275191, 1999848052751104, 1999783902958310, 1999827420042105, 1999853090872658,
    2000087873351967, 2000024999692869, 2000068748361599, 1999996337323753, 1999998763102598,
    1999927168058590, 2000034149324193, 2000041675716772, 1999995958319944, 1999986522797585,
    2000016181416979, 2000219388495848, 2000060737953260, 2000103972979278, 2000047019066985,
    2000044681393399, 1999973857161130, 2000108981691267, 2000106001163756, 2000071841412785,
    1999947509190681, 2000078652835813, 2000064022464109, 2000128371533203, 1999833221124371,
    2000049033198234, 2000018326189724, 2000044857561149, 1999969309143357]
private def pvn_m8_r512_6_8_p1 : List ℕ :=
  [2000019681515905, 1999993353211264, 1999903490093547, 1999967177709049, 1999921264040561,
    2000002186498184, 2000051121590478, 2000106847052964, 1999996872097974, 1999994041509340,
    2000074124405100, 2000120899601046, 1999963210568127, 2000075762527788, 2000048866512379,
    1999831506658879, 2000022235149326, 1999936555691685, 2000131716273093, 2000142095139426,
    1999957965766993, 1999990364927298, 1999808898981844, 1999952391128712, 1999946845199488,
    2000038571392727, 1999886614832056, 2000072092064688, 1999911575653930, 2000092828288148,
    2000035184378967, 2000107814529734, 1999871608296010, 1999973572186191, 2000156576331567,
    1999896856311707, 2000015478069745, 2000055707489270, 1999992458107827, 2000019322201843,
    1999891836751127, 1999983922071231, 2000056921063724, 2000053284139466, 1999959780989174,
    1999933284931981, 1999956802799475, 1999977331895651, 1999983000863352, 1999776475333841,
    2000063784616365, 2000056222320199, 2000000884533380, 1999985035135085, 1999962940824790,
    2000040071896997, 2000018321934531, 1999870717723179, 1999985340698905, 1999671483342696,
    2000176871150444, 1999862257837672, 1999897368113098, 1999804722599021]
private def pvn_m8_r512_6_8_p2 : List ℕ :=
  [1999925208711624, 1999972907535661, 2000119360587165, 2000042637602230, 2000081101382036,
    1999992893170366, 1999885150039613, 1999971548853547, 2000055176394446, 1999765056088092,
    2000145002207587, 2000238807172634, 2000108585382413, 1999924775290274, 2000214720417886,
    1999863359999869, 2000110812182732, 1999919998022790, 1999773846215300, 1999996242943289,
    1999952125190723, 2000088114119347, 1999865546461512, 1999971048658081, 1999941914219768,
    2000024875213028, 2000121611949620, 2000137447935433, 1999829630366299, 2000057583781338,
    2000239177523477, 1999841970213194, 2000178857995178, 1999724737740720, 2000088527212046,
    1999936906896457, 2000031211198858, 1999793949328203, 1999899354368998, 2000046083812367,
    2000105929878531, 1999829301625812, 2000223940622839, 1999806165215384, 2000226334101686,
    2000266467028240, 1999795779644128, 2000226216475089, 2000055576622951, 1999870163620506,
    2000028246077531, 2000007109270796, 1999900632801844, 2000135086041463, 2000025399856606,
    1999921264244198, 2000280479856467, 1999548403572319, 2000279341921356, 1999970006887417,
    2000374032386269, 1999640980751625, 2000406158128151, 1999650766397992]
private def pvn_m8_r512_6_8_p3 : List ℕ :=
  [2000252184420932, 1999703410331581, 2000346540826629, 1999733914532203, 2000096676593332,
    1999914598088238, 2000206709199960, 1999862898343506, 1999780135049395, 2000329337837738,
    1999849761158267, 2000090639845186, 2000131030049004, 1999666918855307, 2000275094414530,
    1999391155115471, 2000487987130292, 1999568352260916, 2000511816787929, 1999780617585740,
    2000175853507983, 2000043631530954, 1999706389339921, 2000893562180182, 1999213861719778,
    2000635985546210, 1999688767747909, 1999586888886792, 2000897877019891, 1998872065085707,
    2000771223287062, 2000084600527052, 1999270044491468, 2000946634437148, 1999152124442329,
    2000210924569851, 2000454563343122, 1999290185228060, 2000741456552407, 1999618355804829,
    1999777502478056, 2000606286664632, 1999192928017279, 2000093308382516, 2000339845898401,
    1999645779958450, 2000435206315565, 1999943127728837, 2000026889097627, 2000238653098772,
    1999876092719459, 2000124492339051, 1999690084231810, 1999860334551358, 2000616156810282,
    1999397718197416, 1999915240042875, 2000638446915084, 1998992777554733, 2000034467355527,
    2000800844860865, 1999191481452247, 2000287943809289, 2000684415671150]
private def pvn_m8_r512_6_8_p4 : List ℕ :=
  [1998928086429710, 2000447388719318, 2000924704924549, 1998772662514951, 2000426667515182,
    2000981373620068, 1998519986670477, 2000403651107477, 2001431586040606, 1998286611123429,
    1999543702441493, 2001867433544623, 1999093474232079, 1998988306115214, 2001718038191056,
    1999557053552377, 1998271428039150, 2001332752353560, 2000478521500082, 1998277475322651,
    2000754516869290, 2000937673526757, 1998070570375604, 1999812232435180, 2001695242895249,
    1998712348610098, 1998443154857131, 2001730190619064, 2000579725640126, 1998246701140420,
    2000768080098460, 2001736815042799, 1998527224949865, 1999048474758596, 2002094558986658,
    2000196482978595, 1997876181691625, 2000644551085607, 2001836616851639, 1998604531530488,
    1998477840038497, 2001728994805503, 2000996460065506, 1998107673303847, 1999580728259198,
    2001991456413602, 2000069257571616, 1998470902016146, 2001007557534207, 2002000112729780,
    1999031655601290, 1998525346069677, 2001698889442827, 2001651853630857, 1998034734738375,
    1998043660455361, 2001697804754757, 2001776698434051, 1998126854781761, 1997750258385613,
    2001296327082956, 2002249184197684, 1999288823473413, 1998109944033252]
private def pvn_m8_r512_6_8_p5 : List ℕ :=
  [2000520437048444, 2001798020317892, 1999985955398738, 1998878716724013, 2000203244739628,
    2000822419608581, 1999534667323749, 1999390068855648, 2001167471199136, 2001252399873365,
    1998577062434438, 1997560010622651, 2000709723991175, 2003507955105386, 2001204925879937,
    1996971189850961, 1997647441118912, 2002921417389085, 2004898883394070, 1999704399259368,
    1994042203762919, 1996245201556692, 2004086939368781, 2007052240780712, 2000555165105058,
    1992616889919091, 1993676617478355, 2002959133865626, 2009162795116075, 2004431786198696,
    1994029862333969, 1990116765501721, 1997472918275412, 2007979817053808, 2009831816912865,
    2000684020700170, 1990178213271817, 1989540750047981, 1999804083189529, 2010915660569382,
    2012019165903059, 2002023171853335, 1990271648999984, 1987504494111226, 1996172225032579,
    2008681570510499, 2014299776408409, 2008165058350459, 1994955809771019, 1984840089256191,
    1985499925685661, 1996535144807039, 2010103525415048, 2016740205792537, 2011812912122325,
    1998254135234313, 1984291778119952, 1978230026290682, 1983714806829477, 1998005004664195,
    2013713026797759, 2022681072119417, 2019896994995694, 2005672782641822]
private def pvn_m8_r512_6_8_p6 : List ℕ :=
  [1985327251987341, 1966789616061092, 1957353406207758, 1960959176216353, 1976922692496074,
    2000299513934129, 2023478638843808, 2038328851579169, 2038247405317474, 2019637953043343,
    1982561235593275, 1930517694412057, 1869520858252294, 1806769463170554, 1749279658819064,
    1702781005709684, 1671046130781052, 1655678087948998, 1656275112191974, 1670847204091918,
    1696358774841315, 1729292046070340, 1766150597391719, 1803847186504729, 1839946344862076,
    1872760077508682, 1901319870766874, 1925264329717135, 1944685957870264, 1959974143645150,
    1971678940056653, 1980406998315693, 1986750767245456, 1991246150548960, 1994351680346552,
    1996442515662484, 1997813844775438, 1998689677870593, 1999234186716937, 1999563631546415,
    1999757585422582, 1999868695438992, 1999930640229724, 1999964257749882, 1999982024169856,
    1999991172042360, 1999995763858752, 1999998012368878, 1999999087333380, 1999999589519475,
    1999999818989493, 1999999921656654, 1999999966682870, 1999999986062133, 1999999994257625,
    1999999997667339, 1999999999064686, 1999999999629444, 1999999999854815, 1999999999943709,
    1999999999978396, 1999999999991796, 1999999999996923, 1999999999998865]
private def pvn_m8_r512_6_8_p7 : List ℕ :=
  [1999999999999592, 1999999999999861, 1999999999999957, 1999999999999989, 1999999999999999]
private def pvn_m8_r512_6_8 : List ℕ :=
  pCat pvn_m8_r512_6_8_p0
    (pCat pvn_m8_r512_6_8_p1
    (pCat pvn_m8_r512_6_8_p2
    (pCat pvn_m8_r512_6_8_p3
    (pCat pvn_m8_r512_6_8_p4
    (pCat pvn_m8_r512_6_8_p5
    (pCat pvn_m8_r512_6_8_p6
      pvn_m8_r512_6_8_p7))))))
private def pvn_m8_r512_6_9_p0 : List ℕ :=
  [2000022729308333, 1999966951784362, 1999935060426399, 2000006482574914, 2000041859516636,
    2000029456271760, 2000039459206372, 1999978273752165, 2000025564196677, 1999928321185176,
    1999965010753157, 1999961743280575, 2000033257110206, 2000119851804212, 2000053282720371,
    2000053413333466, 2000124416610159, 2000062683458641, 2000065369559269, 2000011711292766,
    1999927524926283, 1999917292931887, 2000039337771760, 1999947501343292, 2000022402415777,
    2000042803345781, 1999955813136018, 2000042485014726, 2000002731221421, 2000075587056975,
    1999956519787012, 2000075139622700, 2000048205406150, 2000054312177059, 2000015731110059,
    2000041307239229, 1999938988597707, 1999796100804904, 1999833779805042, 1999759522628487,
    1999925865156257, 1999897013997729, 2000075517978596, 2000060656600336, 1999994209135509,
    1999913520237631, 2000062615138188, 2000016263153749, 2000018754337068, 1999904790889488,
    2000066884368887, 1999925085582150, 2000111755415752, 2000042691897352, 2000187696003776,
    2000110872722101, 1999965450840814, 2000009259389004, 2000107164714198, 2000150528325597,
    1999963348472011, 2000027651510623, 2000078155239176, 2000097754784380]
private def pvn_m8_r512_6_9_p1 : List ℕ :=
  [2000038317372053, 2000054391787085, 1999997971181955, 2000009526008885, 1999991344370374,
    2000034241496854, 2000034988519494, 1999922042718498, 2000177399981596, 1999936231984380,
    1999852410299621, 2000006006937676, 1999890039136327, 2000068307520548, 1999944469912146,
    2000069847902732, 1999995125539127, 2000079462628752, 1999922374833136, 2000160692714752,
    2000033818383359, 2000133945418669, 2000003066570033, 1999925439756171, 1999903956829421,
    1999937643025405, 2000176536820548, 2000021566276851, 2000063919049878, 2000102724871261,
    1999811734121099, 1999943484308665, 2000027601262963, 1999955180137269, 1999889351690632,
    1999916159899439, 2000015230124053, 2000022685933852, 2000050625618581, 1999932625739155,
    2000115540474572, 1999986125352302, 1999995517028774, 1999992473059939, 1999946317763747,
    2000089468088655, 2000130623861081, 1999843040609558, 2000050669389991, 1999853241062235,
    2000227703093291, 1999832099279123, 2000026027948916, 2000038031568916, 2000009258061252,
    1999994879563784, 1999973707000735, 1999814168094749, 1999966499659259, 2000032248231861,
    1999978400683596, 1999896632559103, 2000021479147118, 1999966263957808]
private def pvn_m8_r512_6_9_p2 : List ℕ :=
  [2000215679302616, 1999900342025081, 1999930170861105, 1999919060720952, 2000035224573497,
    1999784527298012, 2000143351984894, 1999922599386797, 1999612114185553, 2000010124739215,
    1999877428663047, 1999995590132486, 1999949957512189, 2000082199217060, 2000082855303373,
    2000076807973058, 1999930698454812, 1999858107217411, 1999903753977324, 2000024675372506,
    2000183323476843, 1999774916714980, 2000353207721059, 1999918883193982, 2000196441328588,
    2000119479521655, 1999979130426543, 1999809214025433, 1999995046770441, 1999974887271855,
    2000101514446413, 1999751988309331, 2000039431371124, 1999816427174143, 2000042323892912,
    2000214583597676, 1999684256592804, 2000133483960395, 2000104734070648, 1999977455541617,
    2000188852998949, 1999949390442079, 1999882005278512, 2000160743974133, 2000158299403652,
    1999599387073583, 2000280206090588, 1999571182522190, 2000296305393203, 1999685389403171,
    2000181661775330, 1999671604563577, 2000384293135654, 1999589987940461, 2000370545827537,
    1999952915215403, 2000206772215694, 1999894439535525, 2000276685425022, 2000032914576039,
    1999824414970279, 2000027825987440, 1999940582534103, 2000220266451105]
private def pvn_m8_r512_6_9_p3 : List ℕ :=
  [1999927363930007, 1999911764744925, 2000348991261751, 1999331875969654, 2000586785221788,
    1999680878815895, 2000463040821091, 1999666387878158, 2000229409713498, 2000126305285812,
    1999737946983791, 2000410528063691, 1999363892353937, 2000685137228592, 1999510898054913,
    2000156787827523, 2000389174669487, 1999082981241924, 2000937079316426, 1999328709946307,
    2000074262692697, 2000708983641332, 1999083343814338, 2000906177881498, 1999488758709273,
    1999447565449692, 2000869934125893, 1999221189467403, 2000383730952013, 2000141734274993,
    1999425687190727, 2000735627221379, 1999670718804010, 2000043348181001, 2000610088723037,
    1999439751162824, 2000358991755443, 2000008197187027, 1999537269115500, 2000355565517398,
    1999986915047072, 1999927534449696, 2000079865232458, 1999792654924386, 2000265196355883,
    1999781671376978, 1999855148092378, 2000455553081488, 1999543007461973, 2000286073504137,
    2000456883585454, 1999025071001887, 2000287485251436, 2000521962783148, 1998958949264891,
    2000365910315493, 2000603840862497, 1999070803178890, 2000681615846212, 2000639624529866,
    1998882565221506, 2000647568609766, 2000440041503469, 1998677649115607]
private def pvn_m8_r512_6_9_p4 : List ℕ :=
  [2000862384646916, 2000746392715001, 1998405555334418, 2000446553533896, 2000943673843827,
    1998345656673929, 2000204546419694, 2001615225838533, 1998504079421016, 1999362743148137,
    2001979954193736, 1999365898875386, 1998760208180880, 2001590854509437, 2000002025308541,
    1998558347446321, 2001311649616441, 2000714905834775, 1998236764332989, 2000348434781732,
    2001307366160367, 1998616914127297, 1999602128382966, 2001910106827918, 1999349326583788,
    1998157785360354, 2001358250662383, 2000964322129577, 1998060989314535, 1999928781435888,
    2001770794267419, 1998968146126225, 1998547112270923, 2001500242564064, 2000373121684531,
    1997678731260935, 1999888653277636, 2001945767134166, 1999283429531578, 1998369628676482,
    2001415327773430, 2001395072816396, 1998388535084557, 1999265903291399, 2001960652264384,
    2000363072738555, 1998147270001813, 2000215083105022, 2001702634266807, 1999189556623542,
    1998381077367747, 2001221357598770, 2001447771453198, 1998341378491471, 1998517864990877,
    2001898989534122, 2001693274791112, 1998328594847072, 1998615962333541, 2002126817892966,
    2002110209484762, 1998648880095831, 1998223716197907, 2001261925399625]
private def pvn_m8_r512_6_9_p5 : List ℕ :=
  [2001827171639512, 1999054516485599, 1998157208505637, 2000284372439309, 2001098821871366,
    1999505486879946, 1999071331323980, 2000526449259512, 2000689808601141, 1999254082194227,
    1999485549429485, 2001459480579126, 2001293570941028, 1998503112705494, 1997821976041916,
    2001170110478989, 2003460969254740, 2000436422058915, 1996230859693028, 1997579086852867,
    2002973987846686, 2004198594755805, 1998846454934505, 1994714288006534, 1998576844119716,
    2005668642014135, 2005846884917871, 1998070767719829, 1992487926410581, 1996846508272864,
    2005816407062085, 2007705297141157, 1999644455592034, 1991465436479406, 1993466210264269,
    2003603765409077, 2009859771220240, 2004622228771899, 1993710209542406, 1989606017692714,
    1997145219723339, 2008131358446540, 2010525695792835, 2001529947517855, 1990380056092537,
    1988526070908554, 1998019523568679, 2009778568769731, 2012679135112800, 2004052870090951,
    1991817042498789, 1986983706466357, 1993879543432549, 2006658638675993, 2014563817704628,
    2010930025382253, 1998375330554749, 1986406683272752, 1983946458211345, 1992828389892952,
    2006847341203117, 2016408480572015, 2015019604266350, 2003250481803787]
private def pvn_m8_r512_6_9_p6 : List ℕ :=
  [1988043236649483, 1978338960719280, 1979914070186619, 1992318776846714, 2009305631377823,
    2022175980812741, 2024097432699216, 2013233495403461, 1993390451834433, 1972209173192487,
    1957977152937026, 1956484171451857, 1969033545747232, 1992086763440312, 2018409066228862,
    2039181067770891, 2046376286419105, 2034741825084041, 2002914883886312, 1953501733484337,
    1892249604546597, 1826659433197667, 1764460206970055, 1712301077406360, 1674874660095397,
    1654534304610203, 1651355432439496, 1663528028239961, 1687944121426428, 1720846715025584,
    1758426454140650, 1797284975987973, 1834724338772046, 1868862306945604, 1898604834860366,
    1923524025816892, 1943691555969075, 1959508097324707, 1971554782776272, 1980478684143315,
    1986913816152553, 1991433140078627, 1994524643584943, 1996584470110686, 1997921058563517,
    1998765559654889, 1999285049535360, 1999596143144232, 1999777501252183, 1999880432047213,
    1999937315165417, 1999967931575675, 1999983986015999, 1999992190957415, 1999996279747899,
    1999998267588388, 1999999210977742, 1999999648303149, 1999999846469237, 1999999934309869,
    1999999972430174, 1999999988640306, 1999999995400807, 1999999998168653]
private def pvn_m8_r512_6_9_p7 : List ℕ :=
  [1999999999282167, 1999999999722788, 1999999999894445, 1999999999960347, 1999999999985301,
    1999999999994628, 1999999999998068, 1999999999999320, 1999999999999770, 1999999999999927,
    1999999999999980, 1999999999999996]
private def pvn_m8_r512_6_9 : List ℕ :=
  pCat pvn_m8_r512_6_9_p0
    (pCat pvn_m8_r512_6_9_p1
    (pCat pvn_m8_r512_6_9_p2
    (pCat pvn_m8_r512_6_9_p3
    (pCat pvn_m8_r512_6_9_p4
    (pCat pvn_m8_r512_6_9_p5
    (pCat pvn_m8_r512_6_9_p6
      pvn_m8_r512_6_9_p7))))))
private def pvn_m8_r512_6_10_p0 : List ℕ :=
  [2000021714928914, 2000029336025912, 1999979861509579, 1999931829104323, 1999988782762624,
    1999956621183253, 2000056171491197, 2000012463054042, 2000024076306124, 2000042181607833,
    1999999516989787, 2000013970881956, 2000004603613477, 1999890861926842, 1999953249942611,
    2000012762491726, 2000037937674790, 2000014147738827, 2000108191986185, 2000027655027384,
    2000052162602544, 2000180772987624, 2000037080394633, 2000073630870410, 1999961638205428,
    2000008320055237, 1999911936320880, 1999982302532003, 2000012637240179, 1999998692755183,
    1999980963531175, 1999975741058840, 2000089627852898, 1999940089169717, 2000055153872703,
    1999990976327458, 2000056021803578, 2000002445731510, 2000039474135465, 2000041183583079,
    2000150324593828, 1999981685244415, 2000032292493782, 1999875086377216, 1999928535087085,
    1999671377378109, 1999837149623073, 1999924273843266, 1999976184318987, 2000010349879059,
    1999934613553828, 2000023063939722, 2000005686281892, 2000029730771305, 1999962850122871,
    2000046536323885, 2000016637152145, 1999912456618267, 1999888732452893, 2000090857598713,
    2000159311622041, 2000058780966017, 2000062272821732, 1999984847020466]
private def pvn_m8_r512_6_10_p1 : List ℕ :=
  [2000165607118927, 2000033011392666, 2000025238892752, 2000165910766542, 1999876103225021,
    2000138708921983, 2000072209325197, 2000093282780040, 1999968256638534, 2000140063290723,
    1999983211377356, 2000080289788191, 1999905323031563, 2000009976512154, 2000092027657553,
    2000017225177574, 2000063970368319, 1999952063933881, 2000007477775496, 1999921860467070,
    1999886958379632, 2000056836167666, 1999905241731945, 2000036326436722, 2000093741878537,
    1999890310282949, 1999970370914208, 2000086290138789, 2000135531267073, 2000038789919059,
    2000165984650496, 1999957599071566, 1999917918705082, 1999895787261604, 2000002079875633,
    2000142655037714, 2000099197485026, 1999888763979543, 2000170116632965, 1999849096409999,
    2000162512145659, 1999834699278258, 1999971038110541, 1999911060701888, 1999955927832492,
    2000001059361701, 1999909292329745, 1999937778639006, 2000184397839007, 2000013471771221,
    1999936940567410, 1999950658998660, 2000080531743051, 1999948916671783, 2000164033176451,
    1999888522133954, 2000040701409229, 1999990897090135, 2000073236331225, 1999901467296591,
    1999997659791228, 1999960999053466, 2000002302077461, 2000280844707648]
private def pvn_m8_r512_6_10_p2 : List ℕ :=
  [1999743144947251, 1999979028257877, 2000070273947964, 1999916661770383, 1999917306028364,
    2000002945434518, 1999900874729282, 1999863074044861, 2000118746357504, 2000020938088913,
    2000177972833256, 1999694706752524, 2000171712026452, 1999819632638206, 2000101388133325,
    2000025388040801, 1999829976351409, 1999888354854978, 2000062099285138, 1999681840904538,
    1999910169470313, 1999814170567602, 2000077832743986, 2000059885616605, 2000022305264455,
    2000180896622200, 1999700313741184, 2000071090078022, 2000054637807446, 1999789317422499,
    2000099009154056, 1999868922529728, 2000055329687064, 2000212286915680, 2000347373009554,
    1999591605151796, 2000471019608172, 1999587459334625, 2000368152185842, 1999798544457636,
    2000108308704182, 1999563506255304, 2000371093349644, 1999689997954342, 2000146783281319,
    1999752037459657, 2000009759230489, 2000086333179920, 2000064675535170, 1999966110822193,
    1999943322178017, 2000242215270573, 1999936843788508, 1999983062916200, 2000294457944146,
    1999607123654437, 2000403158295955, 1999369715145640, 2000596827895010, 1999540971784665,
    1999968934820089, 2000062225261971, 1999838941884841, 2000215359574917]
private def pvn_m8_r512_6_10_p3 : List ℕ :=
  [1999481877924118, 2000673571066180, 1999542898072346, 2000411631457141, 2000223457832163,
    1999631418333732, 2000639408699963, 1999113718254850, 2000695003882677, 2000055070414455,
    1999410030230466, 2000939733376874, 1999078971432488, 2000383484742779, 2000305361017524,
    1999164455688708, 2000962058276168, 1999511774090232, 2000003414032117, 2000720008393807,
    1999189534133399, 2000478753270409, 2000067982120604, 1999511625350840, 2000626076313673,
    1999599104969430, 2000161042442834, 2000227294321711, 1999352474611878, 2000313015102988,
    2000110783709431, 1999800028831077, 2000430373302241, 1999782371572185, 1999885649381075,
    2000112416226626, 1999765173923196, 2000186771373763, 1999749367373756, 2000001365313095,
    2000326160218272, 1999410875400136, 2000280875244613, 2000515502964481, 1999445584984530,
    2000504196518546, 2000300962301203, 1999094919068801, 2000661164808598, 2000332755292519,
    1998887978841712, 2000752393709307, 2000421052111382, 1998921754942605, 2000710392718013,
    2000155667381031, 1998897669195197, 2000967415206121, 2000285537235178, 1998804751353161,
    2000983138439791, 2000421199484251, 1998506952786936, 2000783072592095]
private def pvn_m8_r512_6_10_p4 : List ℕ :=
  [2000718411839667, 1998227433646809, 2000449318148431, 2001436460388401, 1998564368416923,
    2000004042926230, 2001759438761377, 1998742632100063, 1999113701977066, 2001886438492545,
    1999708138545796, 1998610143965415, 2001234199451658, 2000215764991593, 1998435923680857,
    2000799967476252, 2000862383412981, 1998319772368402, 2000018681761349, 2001676604693063,
    1998985166866536, 1998999935139483, 2001717074535789, 1999992755861381, 1998219707781270,
    2001162894490514, 2001539565764424, 1998316841420022, 1999303601787784, 2001790393391985,
    1999668457401037, 1998438723733247, 2001204288067663, 2001074869350696, 1998226812190197,
    1999526776996298, 2001918300159054, 1999666620179394, 1997988465904718, 2000806369043871,
    2001626404419770, 1998667580998180, 1998773806951971, 2001478380806085, 2000331704207828,
    1997874492558006, 1999691895748143, 2001698912076548, 1999562908503067, 1998353652120494,
    2000912835217742, 2001543807333119, 1998815899526691, 1998790266454729, 2001727226340452,
    2001330229079202, 1998163147325662, 1998702194901083, 2001956892640930, 2001369496204709,
    1998037102733393, 1998478450761689, 2001730288615528, 2001475670661246]
private def pvn_m8_r512_6_10_p5 : List ℕ :=
  [1998406234538863, 1998474738057346, 2001347950340667, 2001643983253079, 1999365225518591,
    1999112983052920, 2000977392493699, 2001111504241345, 1999554316958275, 1999574860153081,
    2000815029072554, 2000237410963449, 1998609105250423, 1999309081422909, 2001468813260219,
    2000918556736868, 1998029518912172, 1997959680510415, 2001691925999042, 2003351124020888,
    1999627055376422, 1996036734623369, 1998667158555923, 2003980702271272, 2003641140225744,
    1997628473961338, 1994950299453542, 2000078566763153, 2005677096626298, 2003110717820761,
    1995431248527083, 1993561132777174, 2000835752209328, 2007850952093862, 2005017116070520,
    1995661283527692, 1991922472727429, 1998900772514045, 2007885565420350, 2007353489071635,
    1997554411788807, 1990315946353153, 1994551787432410, 2005453167483223, 2010254242812614,
    2003246472230468, 1992270321979407, 1989644162196200, 1998409816077759, 2009205946850143,
    2010524907594830, 2000791146741400, 1989742022684029, 1988396273869275, 1998210330587204,
    2009933797038367, 2012629284324087, 2003835076556025, 1991536954048487, 1986727718320549,
    1993724692314588, 2006718342937792, 2014965805125032, 2011670346434322]
private def pvn_m8_r512_6_10_p6 : List ℕ :=
  [1999164130581734, 1986745897568370, 1983511145030973, 1991854700058364, 2006097597801788,
    2016629451584448, 2016315876487031, 2004921049636462, 1989037227771987, 1977973400591169,
    1978330768034056, 1990411324853362, 2008225066513994, 2022729515889478, 2026336011485094,
    2016394471106224, 1996214737637418, 1973507605620295, 1957201225702340, 1954029759971701,
    1966122582435549, 1990283752414885, 2019008324164420, 2042738672085371, 2052553651693472,
    2042464192154887, 2010728421637898, 1959980372731780, 1896335268405369, 1827871242088299,
    1762950618831212, 1708767211860975, 1670358970083230, 1650171132542041, 1648130424210636,
    1662107962295623, 1688607216540538, 1723509594619684, 1762737769302035, 1802745576170840,
    1840799295757370, 1875064206899394, 1904542528903423, 1928921240516908, 1948384125370895,
    1963428580116284, 1974711215065540, 1982931977316263, 1988756622519452, 1992771905365522,
    1995465788983305, 1997224994114930, 1998343274472966, 1999035246326380, 1999452056232344,
    1999696466681438, 1999835998129026, 1999913561181088, 1999955551633799, 1999977696035039,
    1999989075490779, 1999994775429015, 1999997559473872, 1999998886026211]
private def pvn_m8_r512_6_10_p7 : List ℕ :=
  [1999999502929113, 1999999783067453, 1999999907354830, 1999999961260149, 1999999984129475,
    1999999993626206, 1999999997488892, 1999999999028845, 1999999999631060, 1999999999862233,
    1999999999949407, 1999999999981725, 1999999999993509, 1999999999997738, 1999999999999230,
    1999999999999748, 1999999999999922, 1999999999999979, 1999999999999997]
private def pvn_m8_r512_6_10 : List ℕ :=
  pCat pvn_m8_r512_6_10_p0
    (pCat pvn_m8_r512_6_10_p1
    (pCat pvn_m8_r512_6_10_p2
    (pCat pvn_m8_r512_6_10_p3
    (pCat pvn_m8_r512_6_10_p4
    (pCat pvn_m8_r512_6_10_p5
    (pCat pvn_m8_r512_6_10_p6
      pvn_m8_r512_6_10_p7))))))
private def pvn_m8_r512_6_11_p0 : List ℕ :=
  [2000004051405994, 2000013965335714, 2000063651659684, 1999967960267045, 2000005606202833,
    1999956030034350, 1999936843545523, 1999992038213641, 2000003789859214, 1999981232516878,
    2000060151629631, 2000011177959197, 2000007145297946, 2000016741431405, 2000088767671233,
    1999991875477233, 1999909385056168, 2000027371711240, 1999878921667974, 1999999633781010,
    2000001543863231, 2000062615631905, 2000000742288793, 2000013765158605, 2000093272834805,
    2000064913725827, 2000134505533655, 2000033799729908, 2000156302357788, 1999975819871652,
    1999977533956265, 1999962102721024, 2000019556334338, 1999938209345253, 2000028215286965,
    1999913603893617, 2000084183327725, 1999943819347825, 2000042907833785, 1999952359338987,
    2000060779917624, 2000053936046778, 1999923971644248, 2000042168197990, 2000030732983191,
    2000069531660337, 2000021328092712, 2000098280662754, 2000097500819366, 2000062557825781,
    1999915712901479, 1999799166304236, 1999801357480703, 1999861937245079, 1999927293358825,
    1999816017979270, 2000014774382673, 2000007212521969, 1999926058891085, 2000021828322497,
    1999869597179231, 2000238212381344, 1999984680858677, 1999934914239234]
private def pvn_m8_r512_6_11_p1 : List ℕ :=
  [1999893361299593, 2000030937841412, 1999902923007021, 2000133586503428, 2000063591236643,
    2000001985126431, 2000074541043465, 2000036595815286, 2000161529734560, 2000035036820064,
    2000006419491786, 2000086098833592, 2000026613304175, 2000114222087844, 1999976539486295,
    2000043708316636, 2000183747404306, 1999994718887641, 2000073935813133, 2000026796378086,
    1999985045685923, 1999937854110835, 2000139385550625, 1999994659093279, 2000006922155527,
    2000094480817502, 2000053970201520, 1999851060634108, 2000034849157450, 1999791068174778,
    2000189369362291, 1999844402041235, 2000058770146281, 1999995955206616, 1999914600843192,
    1999950012493257, 2000020266491261, 2000150888864208, 2000216084878087, 1999980298522938,
    2000022751658978, 1999894445884538, 2000005427934577, 1999995180118290, 2000126591115472,
    1999835466391805, 2000163876191958, 2000078704266298, 2000014365925349, 1999941095700711,
    2000013957941979, 2000025895257229, 1999896604002849, 2000031123475995, 1999706523179873,
    2000075040910757, 2000032853392791, 1999935504577857, 2000105111274424, 1999920974610784,
    1999935612353666, 2000089005698562, 2000148993109187, 1999706541761062]
private def pvn_m8_r512_6_11_p2 : List ℕ :=
  [2000211655480426, 1999947099041447, 2000203606871991, 1999808776044037, 2000031268283464,
    2000004514142119, 1999913877869742, 2000050502715532, 2000175497234902, 1999794489983063,
    2000109642225855, 1999945651410596, 1999994393403694, 2000130505436915, 1999792727684407,
    1999931306462078, 1999807881475376, 2000125584140610, 2000099900315463, 1999754517590787,
    2000226946179125, 1999852865910443, 2000061559294539, 1999897736344994, 2000222460637088,
    1999527332009049, 2000579540540842, 1999528770465621, 2000183947614945, 1999639257054992,
    1999920555954733, 1999625066629171, 2000376677289400, 1999723028533618, 2000101088097000,
    1999987779824673, 1999970265876585, 2000144660592161, 1999936997285349, 1999848034826254,
    1999818295787326, 2000028800252051, 2000196706737988, 1999868293519335, 2000420823112151,
    1999463653903372, 2000753887019401, 1999661628956511, 2000226805547121, 1999863934047499,
    1999891804354512, 2000382414088977, 1999436023822162, 2000403421055959, 1999554075442284,
    2000234434628879, 1999732795362463, 1999965168283069, 2000490916507470, 1999159746249809,
    2000723034144253, 1999720141952796, 2000011814399717, 2000513923615276]
private def pvn_m8_r512_6_11_p3 : List ℕ :=
  [1999215903946296, 2000911391297587, 1999536407501773, 1999751325277907, 2000812301023620,
    1998945777248892, 2000547380851778, 2000010723799123, 1999380205555006, 2000730090444753,
    1999213638387411, 2000062883416845, 2000612816710769, 1999388867747811, 2000680756299369,
    1999883647480027, 1999689490687884, 2000567175638810, 1999654058633035, 2000136496051589,
    2000230337414524, 1999629444083625, 2000403729308201, 1999865499798968, 1999692611828398,
    2000400714835921, 1999758165226782, 2000039195049917, 2000189918501980, 1999919495716647,
    2000303620498970, 1999770927145839, 1999966875063825, 2000269325007488, 1999652667876818,
    2000395821829894, 2000237010042233, 1999233572103787, 2000400889571273, 2000203161178312,
    1999206202837015, 2000724884606145, 2000226330974560, 1999134113804772, 2000838194005389,
    1999983941273494, 1998965815428506, 2001012120222873, 2000042304339919, 1998864612679721,
    2000837433581612, 2000012316547488, 1999060475044429, 2001052598250877, 2000093341841989,
    1998992442114620, 2001203796943680, 2000235775706263, 1998553738884404, 2001013525953909,
    2000628025592465, 1998429768366430, 2000804974946007, 2001065296455502]
private def pvn_m8_r512_6_11_p4 : List ℕ :=
  [1998256336038219, 2000173947589698, 2001514454245040, 1998604130037512, 1999536214069967,
    2001752866176414, 1999261037920843, 1998949041477898, 2001596726140627, 1999945761568996,
    1998341167859245, 2000839310108221, 2000633133871522, 1998610779799736, 2000567853662880,
    2001261268763846, 1998581146037492, 1999622763981533, 2001851500076247, 1999447577348159,
    1998594562208953, 2001477173103256, 2000604447251204, 1998159146197943, 2000366087868451,
    2001563304538683, 1998605933378057, 1998825049001089, 2001732549437614, 2000326312005836,
    1998227056751710, 2000482887919156, 2001378277672692, 1998756891947706, 1999249307490705,
    2001910295180129, 2000297601371349, 1998030402242091, 2000374742383399, 2001824928036757,
    1999041893609669, 1998540486343376, 2001405598453817, 2000983409254772, 1998363174182627,
    1999570507307537, 2001661207736566, 1999750023992069, 1998206294236145, 2000591406287059,
    2001618483626519, 1999038759847381, 1998566892229919, 2001154222739478, 2000905565702901,
    1998074934435059, 1998738490527527, 2001749674278620, 2000898464022155, 1997894662715228,
    1998979600602709, 2002137452820501, 2001172713115044, 1998128377565896]
private def pvn_m8_r512_6_11_p5 : List ℕ :=
  [1998987379938268, 2001859258181714, 2001141941570226, 1998481990767594, 1998976134763530,
    2001268287762801, 2000886010267556, 1998949500393733, 1999245590797738, 2000739299829695,
    2000302470345423, 1999150698708303, 2000008204229648, 2001282259156431, 2000217849066610,
    1998772968262093, 2000188100571588, 2002311543676218, 2000892614833986, 1997722784888719,
    1998358483622527, 2002239406104945, 2002707300879291, 1998202459489227, 1995785983095105,
    1999912488331715, 2004507600759074, 2002122554815149, 1996083725799955, 1995853917956834,
    2002274024687461, 2005754436839052, 2000685905752936, 1994273679164874, 1996208878928045,
    2004250404672478, 2006953951526917, 1999893636140671, 1992326338223338, 1994739276608771,
    2004395740232534, 2008690517975703, 2001835875725611, 1992605008927516, 1993002610466561,
    2002789969479283, 2009753416130978, 2005046466584337, 1994127400645415, 1990029830388897,
    1997693974047485, 2008264527079886, 2009554525928138, 1999966069978415, 1990080920140186,
    1990793932201580, 2001524503283633, 2011036036961226, 2009356052565872, 1997980872475009,
    1988149250806140, 1989528988470405, 2000878768163733, 2011524147470449]
private def pvn_m8_r512_6_11_p6 : List ℕ :=
  [2011604772299947, 2001071732481916, 1989391369100931, 1986900286597457, 1995916655669798,
    2009095775919775, 2015755715675865, 2010449324042461, 1996971059572164, 1985203722054044,
    1983726856838639, 1993777393827868, 2008606767745136, 2018227950954113, 2016021508814161,
    2002850534900967, 1986344204004338, 1976192408462921, 1978538677266375, 1992685630562191,
    2011638002078643, 2025793511732341, 2027638789407858, 2015171131168759, 1992689235130861,
    1968905007330789, 1953396441030591, 1952906159564008, 1968848176010686, 1996785177273064,
    2027861694846801, 2051521832024551, 2058516683027122, 2043273579579767, 2005056165296534,
    1947802684448314, 1878912287938911, 1807457789848116, 1742331170422351, 1690726336953569,
    1657198843285844, 1643369475613949, 1648194116867249, 1668626665358811, 1700463118147507,
    1739169581672196, 1780550420624012, 1821183641976777, 1858617497645547, 1891370088118018,
    1918796853212454, 1940892145474421, 1958078330804844, 1971017518991945, 1980463500818703,
    1987158143995512, 1991768185364715, 1994854323183157, 1996863475740049, 1998135804321662,
    1998919677953187, 1999389583956020, 1999663709304050, 1999819349028680]
private def pvn_m8_r512_6_11_p7 : List ℕ :=
  [1999905367894177, 1999951653876283, 1999975907738269, 1999988286975526, 1999994443092170,
    1999997426757577, 1999998836583370, 1999999486272236, 1999999778373235, 1999999906553580,
    1999999961476509, 1999999984465648, 1999999993870042, 1999999997631795, 1999999999103842,
    1999999999667680, 1999999999879181, 1999999999956926, 1999999999984941, 1999999999994838,
    1999999999998272, 1999999999999438, 1999999999999826, 1999999999999951, 1999999999999989,
    1999999999999999]
private def pvn_m8_r512_6_11 : List ℕ :=
  pCat pvn_m8_r512_6_11_p0
    (pCat pvn_m8_r512_6_11_p1
    (pCat pvn_m8_r512_6_11_p2
    (pCat pvn_m8_r512_6_11_p3
    (pCat pvn_m8_r512_6_11_p4
    (pCat pvn_m8_r512_6_11_p5
    (pCat pvn_m8_r512_6_11_p6
      pvn_m8_r512_6_11_p7))))))
private def pvn_m8_r512_6_12_p0 : List ℕ :=
  [2000013071994317, 1999959451697521, 2000050794780301, 2000030780705818, 2000004924010834,
    2000019847080339, 2000025359694741, 1999932880262586, 1999978353973902, 1999967321334056,
    1999974480670532, 1999966132836364, 1999983969061875, 2000111819185371, 1999916100194360,
    2000027207480316, 2000038660010135, 2000047906057798, 2000032986175134, 1999999746720798,
    2000054019841812, 1999896571977665, 1999980580943425, 1999896878752839, 2000047533760500,
    1999987380908172, 2000000109989506, 1999973046994669, 2000106638466822, 1999950698412318,
    2000117514023249, 2000032276541018, 2000170856428377, 2000084472636601, 2000042486080577,
    2000048176010254, 1999952901934280, 2000062702461555, 1999950924843600, 1999950662651754,
    1999984588430233, 2000037004412604, 1999969216882667, 1999954723518512, 2000012542694762,
    2000023008245248, 2000042591514689, 1999953132820579, 2000036126224633, 1999992374849991,
    2000013054200153, 2000087221301703, 1999836888441115, 2000190632760991, 2000064271442302,
    2000193664287047, 2000020142370685, 1999966670242870, 1999889779266513, 1999971112799984,
    1999738685811095, 1999769479229953, 2000025440662634, 1999901438887852]
private def pvn_m8_r512_6_12_p1 : List ℕ :=
  [1999931535271033, 1999904083764138, 1999914944796635, 2000047875351608, 2000000092779669,
    2000114410291246, 2000010985994013, 1999878837332813, 1999990221543057, 1999905988336458,
    2000084044715815, 1999998131736780, 1999970162132269, 2000007239374562, 2000170552410123,
    2000002473014416, 2000052353509266, 2000079247957719, 2000128599024088, 1999898701457864,
    2000271092776321, 1999858090982880, 2000108183230284, 2000022637212377, 2000105025824190,
    2000136616668889, 1999987691496021, 2000049233458415, 2000109231432567, 1999918845534436,
    2000032092116480, 1999959428569797, 2000148459157933, 2000014572444521, 2000089652157551,
    1999938740282680, 2000099999061673, 1999820378726913, 1999958187203856, 2000052316919932,
    1999975737113041, 2000062364987971, 1999900343859514, 1999928414591799, 1999774561472584,
    2000216846298241, 2000111322503191, 2000002853887337, 2000164441293491, 1999933336717797,
    2000100133711533, 1999973201434666, 1999970896431840, 1999826420312735, 2000328354888387,
    1999798193704693, 2000166728308387, 1999989344878960, 1999999192982141, 2000045266938839,
    2000111033867124, 1999965739598491, 1999877550994903, 1999776417451398]
private def pvn_m8_r512_6_12_p2 : List ℕ :=
  [2000200493384758, 1999898828040284, 1999816989068117, 2000164515720386, 1999864773541505,
    2000098140756085, 2000000688639273, 1999913087343447, 2000084933613779, 1999820037510470,
    2000311502380689, 1999815076859308, 2000236872509765, 1999781148650899, 2000174935231499,
    1999574992252485, 2000651718261239, 1999521948230977, 2000188141898096, 1999871055140626,
    2000138008195923, 1999916711879763, 2000304738289791, 1999670966714388, 2000009253483489,
    2000035690640486, 1999763241627141, 2000091205854175, 1999961903654406, 1999889778617891,
    2000138639271013, 1999900202995278, 2000194302350350, 1999525101745932, 2000487195116692,
    1999516755624331, 2000584113368500, 1999772416089920, 1999805912434456, 2000099033342099,
    1999440676538220, 2000424984087496, 1999435522043228, 2000211780352438, 1999680329531528,
    2000091320348594, 2000424797351313, 1999538009936101, 2000400453094962, 1999356583937666,
    2000413170289794, 1999960200238908, 1999356865624767, 2000886176325176, 1999323130313747,
    2000381104511859, 2000323165300857, 1999447649737730, 2000892792466159, 1999265036331629,
    2000250672083122, 2000605529001566, 1999002806166162, 2000666887625791]
private def pvn_m8_r512_6_12_p3 : List ℕ :=
  [1999800069577815, 1999511405888007, 2000718981455541, 1999250083787813, 2000240885773380,
    2000196745034421, 1999386762726937, 2000626272806275, 1999829531865431, 1999772269299051,
    2000514001255341, 1999702420591411, 2000209954435889, 2000143066862106, 1999560919172583,
    2000352141230400, 1999878607464065, 1999902272347613, 2000253890817756, 1999497293371258,
    1999979079582226, 2000089058072470, 1999818177738577, 2000231049019132, 1999902389922935,
    2000128848764503, 2000253530506017, 1999613023458500, 2000312690088361, 2000254778646996,
    1999475406664832, 2000521736101426, 2000130741266678, 1999304080827516, 2000732782805936,
    1999940064247127, 1999085324018528, 2000913018109186, 2000038562088522, 1999274103213516,
    2001005115730591, 1999762882020015, 1999141317280355, 2001126745053170, 1999888824903467,
    1999171854523901, 2001122782071255, 1999857810304731, 1998960583650772, 2000961941916918,
    1999909259492074, 1999066050402095, 2001216712248704, 1999974247609342, 1998671553440788,
    2001241563933997, 2000403567023012, 1998397034471811, 2000916508928709, 2000795621562295,
    1998253462904993, 2000393415046028, 2001238116011501, 1998493767648819]
private def pvn_m8_r512_6_12_p4 : List ℕ :=
  [1999923789013461, 2001756014686427, 1999068054325645, 1999166710900509, 2001599159607960,
    1999697575803855, 1998713132263538, 2001318780910469, 2000442334133011, 1998473422448196,
    2000655005063834, 2000986829051662, 1998580218388259, 1999969428893158, 2001379782312385,
    1998924463630030, 1999272884277237, 2001871603075212, 1999938504230797, 1998171240648831,
    2000870777205904, 2001050886785367, 1998353348947156, 1999755945897084, 2001754357306458,
    1999321374420160, 1998580320597436, 2001444579534514, 2000878096309890, 1998307265369102,
    2000004887477971, 2001745215528454, 1999328458464623, 1998740729483870, 2001326281110483,
    2000549822355458, 1998094714104842, 1999960645041877, 2001918863994439, 1999376398047522,
    1998196665518307, 2000985226543089, 2001261254738712, 1998638962007443, 1999357313167119,
    2001697749180828, 2000234163174921, 1998370011056095, 2000349725783202, 2001582516633610,
    1999197742662673, 1998566848872064, 2001202287410150, 2001295492410114, 1998563120827164,
    1998945382135266, 2001608216972219, 2000673256050414, 1998000463762749, 1999392293403975,
    2002181396649685, 2000604713053368, 1997758142986034, 1999252423200542]
private def pvn_m8_r512_6_12_p5 : List ℕ :=
  [2001878730724358, 2000354322941311, 1997837813112119, 1999217244592501, 2001557186109429,
    2000455046939249, 1998528777148984, 1999591783934856, 2001290548603051, 2000399673087095,
    1999081449956602, 1999977145828535, 2000944776583706, 1999855057965047, 1999087741526002,
    2000491905262923, 2001219645869155, 1999308167618825, 1998171300297542, 2000416932180440,
    2002249659879662, 1999932559191107, 1997222255274796, 1999376904840300, 2003391474341998,
    2002341317470446, 1997455209761548, 1996871112644441, 2002067405378723, 2004684634935108,
    1999923084371297, 1994861766959273, 1997594561204728, 2004162142098073, 2004306196968823,
    1997439428084286, 1993968818912005, 1999583579164179, 2006295507114746, 2003986599746229,
    1995528410474691, 1993090668284000, 2000701919381040, 2008097964091545, 2004816595604818,
    1994855084578918, 1991488108392430, 1999365859642522, 2008216608283832, 2006424399006820,
    1996230928902077, 1990759956194590, 1997175868841095, 2007694241695596, 2009373964005419,
    1999993035190756, 1990601273189439, 1992253804390688, 2003108052389875, 2010736408919256,
    2006379803697883, 1994691830321999, 1988427721708794, 1994491709805654]
private def pvn_m8_r512_6_12_p6 : List ℕ :=
  [2006646537373917, 2012267095842549, 2005477243853894, 1992959477410456, 1987009935653593,
    1993398598422744, 2006056802692749, 2013157546330116, 2008175050972525, 1995569558390174,
    1986486776479573, 1988944054208120, 2001177566987256, 2013362303250386, 2015695948493850,
    2006064742333453, 1991477530257123, 1982640946232962, 1986101064611854, 1999701971385291,
    2014267820380383, 2019911622194664, 2012478678079569, 1996026033986771, 1980163294809090,
    1974292890432244, 1982307575411407, 2000580027680734, 2019968261936108, 2030454339086435,
    2025964114369754, 2007152071839534, 1981101230707793, 1958314842918190, 1948440048310930,
    1956501206254664, 1981013842622223, 2014477068142400, 2045821202863556, 2063779605755235,
    2060021740025917, 2031167672356511, 1979302079819802, 1911099761014590, 1836016392239670,
    1764136056248873, 1704223799466343, 1662367751505269, 1641380335592423, 1640923179208421,
    1658170380640905, 1688752780968282, 1727731120589252, 1770407969717788, 1812876380223716,
    1852287689675353, 1886881953488796, 1915855080063992, 1939140565716850, 1957170127384655,
    1970656588184306, 1980421717143808, 1987275538283657, 1991943139776149]
private def pvn_m8_r512_6_12_p7 : List ℕ :=
  [1995029645410866, 1997012410146175, 1998250252359161, 1999001477662482, 1999444763319291,
    1999699148128301, 1999841143207549, 1999918253193695, 1999958999355644, 1999979954455067,
    1999990445369063, 1999995559323881, 1999997987194122, 1999999110064559, 1999999616105013,
    1999999838391510, 1999999933591947, 1999999973356240, 1999999989559826, 1999999996003483,
    1999999998504990, 1999999999453334, 1999999999804552, 1999999999931664, 1999999999976633,
    1999999999992191, 1999999999997455, 1999999999999196, 1999999999999757, 1999999999999932,
    1999999999999985, 1999999999999998]
private def pvn_m8_r512_6_12 : List ℕ :=
  pCat pvn_m8_r512_6_12_p0
    (pCat pvn_m8_r512_6_12_p1
    (pCat pvn_m8_r512_6_12_p2
    (pCat pvn_m8_r512_6_12_p3
    (pCat pvn_m8_r512_6_12_p4
    (pCat pvn_m8_r512_6_12_p5
    (pCat pvn_m8_r512_6_12_p6
      pvn_m8_r512_6_12_p7))))))
private def pvn_m8_r512_6_13_p0 : List ℕ :=
  [2000040275876062, 1999965893233972, 1999976841074425, 2000011861185428, 2000053032566082,
    1999981917812900, 2000028253249332, 2000044467615435, 2000000631329149, 2000034838714193,
    1999895136163025, 2000052009938067, 1999971739437406, 1999904521463251, 1999986046163514,
    1999984104644602, 2000076100876192, 1999917784469566, 2000046928419518, 1999973855309241,
    2000052946083001, 1999993380297131, 2000071001490534, 1999987772055174, 2000142468814810,
    1999911524577685, 1999975077084377, 1999948832451323, 1999961231534246, 2000011235701056,
    1999914940828364, 2000046367957224, 1999986352845662, 2000010955314358, 2000008253783266,
    2000002495147608, 2000037899788011, 2000112060144594, 2000143888330669, 2000035673633853,
    2000083297761324, 2000059253665362, 2000056679032009, 2000024866838438, 1999869604279723,
    2000134546515472, 1999867477731372, 2000087583629078, 1999933957034960, 1999953452652352,
    1999990962279047, 2000072246591734, 1999961203916581, 1999983567610349, 2000029826071980,
    1999960944537232, 2000139373242062, 1999973907599811, 1999835289145226, 2000069231415038,
    2000066651691008, 2000091590029777, 2000079647427699, 2000073714530796]
private def pvn_m8_r512_6_13_p1 : List ℕ :=
  [2000209258639042, 1999936976645793, 1999947247338369, 1999835284330525, 1999852621202417,
    1999867062522707, 1999972229536295, 1999841318517406, 1999958003673716, 1999801962415733,
    1999976163261972, 1999874075933065, 2000297190488181, 1999860088611025, 1999992093362599,
    2000047512910710, 1999914500722271, 1999994949909189, 1999983547627447, 1999930037473102,
    2000065188711197, 1999912156956346, 2000149210904642, 1999996799585562, 2000061794241008,
    1999983864188192, 2000199299131824, 2000016695426512, 2000072134924415, 2000003195062960,
    2000011076456385, 2000163839979134, 1999916376918973, 2000129898539259, 2000072173810245,
    2000155004001751, 1999975794153433, 2000036733788915, 2000106559798701, 1999814664074415,
    2000170977232737, 1999966512872479, 2000099861305233, 2000016998496641, 2000259853252128,
    1999705923889868, 2000092454411803, 1999864859653429, 2000038479925543, 2000180017002081,
    1999933217918214, 1999792835507304, 2000029331561930, 1999882835479328, 2000016661352308,
    1999978018599076, 2000054233674661, 2000218550463495, 1999889013369751, 2000216891062492,
    2000026438456707, 1999702916823863, 2000264401399453, 1999889094305938]
private def pvn_m8_r512_6_13_p2 : List ℕ :=
  [2000222978603734, 1999648658119275, 2000303598403659, 1999815844355841, 2000402477232827,
    1999661076277328, 2000444169778527, 1999528387755369, 2000293840063166, 1999858431030389,
    1999898827742508, 1999900964281846, 2000138389090055, 1999728396528455, 2000125532838839,
    2000166591181623, 1999726234290023, 2000043302189469, 2000021835947168, 1999861368069656,
    2000411979357885, 1999683981882217, 2000256843630061, 1999600033456496, 2000533206228119,
    1999599988850652, 2000227245606709, 2000001383845927, 1999603062663975, 2000544685596273,
    1999525783931428, 2000509317010509, 1999712356363055, 2000070111555234, 2000103363156568,
    1999681270256699, 2000364790650676, 1999346318369884, 2000413129735044, 1999819792138211,
    1999958284593958, 2000421216083109, 1999190862983058, 2000580116256562, 1999634205264007,
    2000035026126224, 2000748518619468, 1998971936058012, 2000623626643796, 1999943913277448,
    1999536387638320, 2000518056180151, 1999001470606769, 2000306022864671, 2000195528723438,
    1999166959190874, 2000950274221440, 1999578405840470, 1999727428212781, 2000633089351399,
    1999345824496745, 2000227499767041, 1999970507413647, 1999503537136905]
private def pvn_m8_r512_6_13_p3 : List ℕ :=
  [2000603302978091, 1999766419224883, 1999892341059528, 2000495126752317, 1999635006809765,
    2000267728789811, 2000193157069096, 1999750896003953, 2000338055548649, 1999746831196167,
    1999960488763556, 2000256257529002, 1999622877654071, 2000073315002959, 1999989637422704,
    1999771574440371, 2000223223464208, 1999813859287715, 1999921254353240, 2000202199179623,
    1999802537631254, 2000365558683660, 2000122530799842, 1999430711660337, 2000520941416157,
    2000105175076916, 1999395622269963, 2000734344336685, 1999868402817111, 1999207065536210,
    2000771069972759, 1999641159275895, 1999229408543393, 2001033944719775, 1999719415765628,
    1999293955917714, 2001083540998193, 1999731051947618, 1999348802315369, 2001099955458428,
    1999651622533448, 1999298290893582, 2001274380813042, 1999772851694766, 1999058947889318,
    2001055103734093, 1999743602475185, 1999057988260257, 2001260433082302, 1999920559432956,
    1998867774794386, 2001265030376906, 2000077678535652, 1998502050637073, 2001243070563520,
    2000796923802668, 1998387302655051, 2000600188311109, 2001085864103774, 1998452485981172,
    2000056624217002, 2001489836389267, 1998821169021153, 1999402939519292]
private def pvn_m8_r512_6_13_p4 : List ℕ :=
  [2001640743877228, 1999452880032492, 1998840999663813, 2001425889294120, 2000176525371010,
    1998530820444696, 2000829174439700, 2000629414244951, 1998426186258627, 2000275645694441,
    2001317721468040, 1998882362309868, 1999626101542538, 2001578946417124, 1999406315660040,
    1998799291988190, 2001518445501610, 2000505508100332, 1998209333306218, 2000491539217549,
    2001636269418943, 1998795496428761, 1999036294187563, 2001509663442558, 1999905775223081,
    1998420066089516, 2001019905705322, 2001344848405209, 1998525707700165, 1999384909931362,
    2001657723580798, 1999714363395717, 1998364048313945, 2000893742686141, 2001069988309743,
    1998505996155213, 1999575052141946, 2001812607362232, 1999790481800323, 1998224167859548,
    2000866330804788, 2001675418452502, 1998905497636304, 1998904092357896, 2001355925292609,
    2000448076439540, 1998417814945028, 2000048441597271, 2001528198077717, 1999344692161034,
    1998425989916560, 2000922256874386, 2001259489000678, 1998679172158885, 1999024686981133,
    2001699383769926, 2000835034806608, 1998216177428481, 1999514164992558, 2001953975283847,
    2000235361977917, 1997953715952105, 2000006535249390, 2002210423793275]
private def pvn_m8_r512_6_13_p5 : List ℕ :=
  [2000006108869834, 1997816311111763, 1999870438609257, 2001863706311868, 2000015024989751,
    1998334709656937, 2000055336329071, 2001472596254263, 1999876645476254, 1998643813844335,
    1999963779221559, 2000766858973030, 1999447985680475, 1998959527954565, 2000368945070090,
    2000638080088886, 1999142773165821, 1999229357890897, 2001216152414204, 2001147178199955,
    1998656680902047, 1998486778634093, 2001544355691710, 2002328349392419, 1998831554646874,
    1997027037374278, 2000549266138991, 2003533313347187, 2000362805928689, 1995964351645975,
    1998025357894387, 2003658645823748, 2003581528713443, 1997584434814911, 1995444181808276,
    2001111788252503, 2005847105806196, 2001885164261652, 1995039814166847, 1995965424303523,
    2003461727650227, 2005933691242351, 1999107624281780, 1992946409246925, 1996955306439489,
    2005743422488613, 2006512043140823, 1997708115124214, 1991642822206166, 1997151383320246,
    2006992161448306, 2007731663426291, 1998198743045885, 1991087512569139, 1995862041220603,
    2006231735528521, 2008576343883302, 1999717564962375, 1990902258291945, 1993406556160896,
    2004408027641425, 2010571862617131, 2004372062887920, 1993074961806945]
private def pvn_m8_r512_6_13_p6 : List ℕ :=
  [1989975056882081, 1998776910721898, 2009431372289423, 2009757446287247, 1999162874403606,
    1989146639521109, 1990588794575986, 2002104603991691, 2011743181644837, 2009574139170941,
    1997704682739986, 1987843575835302, 1989580579236501, 2001265054254914, 2011909886357810,
    2011614889312390, 2000504601184410, 1988363336807319, 1985895628299742, 1995575647595848,
    2009728128753853, 2016961683018631, 2011311690919113, 1996787628792005, 1984142574457066,
    1982777429882351, 1993988793042246, 2010232071920952, 2020450835478821, 2017454928236516,
    2002445064987067, 1984122838854427, 1973377006389100, 1976971016616814, 1993803774527681,
    2015529145101357, 2030883023863306, 2031302662481686, 2015057528970377, 1988086667868201,
    1961403598578918, 1946438090344643, 1950397058921698, 1973466162520364, 2008718670810116,
    2044470082488049, 2067994800554408, 2069245434212190, 2043453670918328, 1992034380239877,
    1921810377007414, 1843032015966249, 1766889976251413, 1703208509446071, 1658819609133725,
    1636845814340084, 1636851780245943, 1655631355012004, 1688310452457542, 1729461390516424,
    1774009025845060, 1817820076844241, 1857967446223843, 1892729405316151]
private def pvn_m8_r512_6_13_p7 : List ℕ :=
  [1921414067928146, 1944099511398606, 1961361293176471, 1974033695123468, 1983027122870252,
    1989205963435830, 1993319911836757, 1995976447088041, 1997641111810853, 1998653815034724,
    1999252130835547, 1999595524807821, 1999787026192891, 1999890817316626, 1999945499137416,
    1999973508422486, 1999987459814000, 1999994218604794, 1999997403799156, 1999998864287184,
    1999999515968225, 1999999798994822, 1999999918656361, 1999999967916669, 1999999987665190,
    1999999995376823, 1999999998310495, 1999999999397938, 1999999999790771, 1999999999929091,
    1999999999976570, 1999999999992458, 1999999999997641, 1999999999999288, 1999999999999796,
    1999999999999948, 1999999999999990, 1999999999999999]
private def pvn_m8_r512_6_13 : List ℕ :=
  pCat pvn_m8_r512_6_13_p0
    (pCat pvn_m8_r512_6_13_p1
    (pCat pvn_m8_r512_6_13_p2
    (pCat pvn_m8_r512_6_13_p3
    (pCat pvn_m8_r512_6_13_p4
    (pCat pvn_m8_r512_6_13_p5
    (pCat pvn_m8_r512_6_13_p6
      pvn_m8_r512_6_13_p7))))))
private def pvn_m8_r512_6_14_p0 : List ℕ :=
  [2000046093591058, 2000011712529853, 2000002253968195, 1999942221385700, 1999992238279865,
    2000052824134995, 1999961164860101, 2000068917374749, 1999958074238318, 2000020307699122,
    2000108320770702, 1999957922395244, 2000025870570116, 1999934470570863, 2000087736302393,
    1999944377726035, 1999964318365640, 1999901615374759, 2000046558030697, 1999923049711497,
    2000072439529033, 1999948459040710, 1999972938240424, 2000065116968229, 1999957954410758,
    2000033383319733, 1999966727040227, 2000069539758099, 2000090228560001, 2000021653318344,
    2000003829937762, 1999983697980898, 1999989159823777, 1999935805068082, 1999991507943684,
    1999962897999704, 1999919860515701, 2000096597550602, 1999904261351759, 2000121040107676,
    1999835682085993, 2000046551814417, 2000074757916883, 2000049423607563, 2000056278604062,
    2000106874613339, 2000081621601806, 2000066188485211, 2000150621079594, 1999959388858706,
    1999981108384979, 2000086187219625, 1999936644553688, 2000042931429415, 2000009084405736,
    1999850101536130, 2000061220771675, 1999997789191830, 2000063948365870, 1999876062582530,
    1999966185859436, 2000067415078241, 2000122278393381, 1999896607224649]
private def pvn_m8_r512_6_14_p1 : List ℕ :=
  [2000066213127331, 1999884888053235, 2000097382086087, 1999862979364157, 2000135683153685,
    1999936344617132, 2000159282622041, 2000232823570441, 2000000127737894, 2000097020281643,
    2000050761983145, 1999728615533531, 1999973508091566, 1999878400263632, 2000027137573058,
    1999800985395692, 1999866804588128, 1999815123144390, 1999971161872307, 1999917131408904,
    2000000861787456, 2000097356874344, 1999875268259590, 2000096580742002, 1999931755785520,
    2000048965981008, 1999935476859412, 1999897218210482, 2000044348388069, 1999950594892054,
    2000141187433258, 1999777075938792, 2000183158879807, 2000004672062812, 2000118008405121,
    1999912814852153, 2000295499817025, 1999884060658189, 2000089511330447, 2000116641289969,
    1999909760761803, 2000054357454847, 2000176476538006, 1999950838347661, 2000176031399140,
    2000079268803658, 1999971104833902, 2000173739166028, 1999881743786375, 1999976354041922,
    2000035815017250, 2000007901919943, 2000468883568641, 1999617740208416, 2000245337770381,
    1999753389301883, 2000239634604964, 1999693633242630, 2000473281056853, 1999612099169466,
    2000266617564409, 1999638160232870, 2000249454888327, 1999738903984176]
private def pvn_m8_r512_6_14_p2 : List ℕ :=
  [1999861375221135, 2000092963118428, 2000171791891627, 1999956157901636, 2000150351535445,
    1999994899970714, 1999873076790496, 2000242289844054, 2000080828391735, 1999597859825285,
    2000473525963136, 1999551436297169, 2000371776914845, 1999765329088935, 2000358309338291,
    1999826851187543, 2000035503962843, 2000286146221450, 1999510957635263, 2000619251596052,
    1999360593282789, 2000133062758546, 1999994152750746, 1999853325091832, 2000365018067160,
    1999476122058419, 2000360612269030, 1999605285512994, 2000212212759793, 2000166201171814,
    1999588275864599, 2000578394235651, 1999386833529916, 2000400601663505, 2000159139591370,
    1999484082704753, 2000732162773083, 1999225486289132, 2000321278093304, 2000318446794807,
    1999220301959340, 2000846653083235, 1999594990365011, 1999883259587011, 2000758083588685,
    1999145957590892, 2000393732933645, 1999781659827240, 1999574586923692, 2000962127518132,
    1999292804718733, 1999837658905645, 2000509320091218, 1999386993560857, 2000337094104479,
    2000033101952698, 1999642656976955, 2000516793896675, 1999718659427573, 2000081595399516,
    2000321857428454, 1999365092427862, 2000083663564886, 1999930653108953]
private def pvn_m8_r512_6_14_p3 : List ℕ :=
  [1999642398527452, 2000194013497665, 1999727889499279, 2000054176442117, 2000223635314913,
    1999721911120074, 2000167430278669, 1999919969787599, 1999687392021553, 2000198677103188,
    1999849070826364, 1999953211055150, 2000192822613168, 1999715307026698, 2000276866032794,
    2000219917726698, 1999637315430938, 2000504915638215, 1999985778184844, 1999516162612960,
    2000791890358206, 1999766748601344, 1999285581988566, 2000851993024190, 1999708475301564,
    1999380397073512, 2000865519540306, 1999456889698251, 1999380242982590, 2001079710934015,
    1999585550153684, 1999443430451113, 2001108415840571, 1999540948982902, 1999370003553200,
    2001141327696434, 1999619900563526, 1999410644058089, 2001186065261509, 1999473405401581,
    1999101821500010, 2001157426401239, 1999576672230139, 1998978289625459, 2001174931941448,
    1999791994253842, 1999001155201655, 2001317202095328, 1999955685842198, 1998616526763778,
    2001268583478614, 2000569598102860, 1998484906880997, 2000881217527877, 2001039906337254,
    1998365797499018, 2000099385449844, 2001397896695560, 1998852130599168, 1999660976774646,
    2001549630751552, 1999173464929177, 1998977595821780, 2001536975422704]
private def pvn_m8_r512_6_14_p4 : List ℕ :=
  [2000001964095445, 1998703481698049, 2001139809238554, 2000579756885313, 1998541989966783,
    2000509125093695, 2001038640668524, 1998690858566212, 1999881623681492, 2001432897923354,
    1999117401047050, 1999101026189497, 2001531924875435, 2000032901563665, 1998535602326484,
    2001010232118300, 2000953996156240, 1998235511931411, 1999699832202338, 2001729417135356,
    1999325761688864, 1998630723408146, 2001361708123190, 2000670301143583, 1998445675081673,
    2000333023333220, 2001487380233207, 1998909044975574, 1999069881749409, 2001716032141400,
    2000379401337303, 1998288275425317, 2000364221050333, 2001309586308274, 1998830078015676,
    1999158838932364, 2001651120133439, 2000296709800543, 1998301846912366, 2000431899292469,
    2001629481801854, 1998991257138902, 1998565209085822, 2001226790629018, 2000861193057667,
    1998543478807450, 1999677571644348, 2001451950202711, 1999689623675315, 1998624980416129,
    2000956330695508, 2001413697828821, 1998797659740120, 1998919671123488, 2001529165891264,
    2000756237087590, 1998237206838800, 1999555968188678, 2001837140007270, 2000000478581130,
    1997935119105540, 2000113468623614, 2001931712262258, 1999583155868144]
private def pvn_m8_r512_6_14_p5 : List ℕ :=
  [1998106470388047, 2000649624617967, 2001957349083917, 1999409072303430, 1998206445921179,
    2000555293804880, 2001594822867462, 1999557261333351, 1998807795096909, 2000577847815624,
    2000961028168333, 1999297399941481, 1999153916966123, 2000668890489004, 2000548119527730,
    1999187014734275, 1999708201016601, 2001100703337232, 2000154226660570, 1998458924524773,
    1999601595591755, 2001566344154715, 2000143840171186, 1997583694695623, 1999028214229181,
    2002403667912485, 2001440374837868, 1997440894832958, 1997729629494142, 2002378508730191,
    2003290876415761, 1998409043985707, 1996018597154173, 2000641332924029, 2004688848190476,
    2000982382199588, 1995270986075582, 1997104913721874, 2003807751648387, 2004408185040370,
    1997584869467025, 1994267556290816, 2000201433486536, 2006380541300141, 2002994622403999,
    1995068949392027, 1994991149401725, 2003257889163446, 2007297284342745, 2000479321324262,
    1992477297974259, 1995172750181610, 2005007413349764, 2007878504075942, 1999424572504968,
    1991373353090472, 1995056962303440, 2005596012745365, 2008683335611048, 2000149928087010,
    1991480902272300, 1994292254069134, 2004947662927194, 2009468240757209]
private def pvn_m8_r512_6_14_p6 : List ℕ :=
  [2001770256134234, 1991454178745516, 1991561253098494, 2002212317277502, 2010520738064897,
    2006412467285746, 1994737540860177, 1989329074174444, 1996632411506712, 2008329206934695,
    2011066503439147, 2001581353359156, 1990148981311630, 1989130684378613, 1999693067121605,
    2010837706025572, 2011069035841467, 2000082757981142, 1988774733170853, 1988252641284995,
    1999105245768891, 2011086573728458, 2012912650754140, 2002642422157697, 1989281896590202,
    1984666682651721, 1993169061566632, 2008083396069696, 2017327634902178, 2013294241367869,
    1998780065307750, 1984649093021719, 1981536889434976, 1992091049903151, 2009232960890980,
    2021198479327588, 2019484360662502, 2004343391165020, 1984565487916872, 1972079705856118,
    1974893449081504, 1992486892709277, 2016043094945594, 2033096238459331, 2033931749310806,
    2016438758972116, 1987182923221681, 1958467173596921, 1942986330966553, 1948536980551190,
    1974909261229912, 2013933456189888, 2052323570975796, 2076012732544514, 2074377534515778,
    2043054045145052, 1984711439832037, 1907872460767419, 1824415586604106, 1746639041913655,
    1684708081965879, 1645031306012810, 1629749749939019, 1637199232391584]
private def pvn_m8_r512_6_14_p7 : List ℕ :=
  [1663004022451169, 1701402420377750, 1746466169989825, 1793002307090178, 1837062809260969,
    1876095049829732, 1908827756013893, 1935005058988159, 1955068188900665, 1969855900349901,
    1980363525055933, 1987574458410559, 1992360087647304, 1995434611802570, 1997348130928369,
    1998502518919900, 1999177866698392, 1999561143371218, 1999772215182562, 1999885034606035,
    1999943575716269, 1999973069997495, 1999987500522021, 1999994357843480, 1999997523105568,
    1999998942479750, 1999999560866701, 1999999822648192, 1999999930336003, 1999999973385837,
    1999999990111226, 1999999996426576, 1999999998744207, 1999999999570850, 1999999999857409,
    1999999999953950, 1999999999985554, 1999999999995606, 1999999999998710, 1999999999999640,
    1999999999999907, 1999999999999980, 1999999999999998]
private def pvn_m8_r512_6_14 : List ℕ :=
  pCat pvn_m8_r512_6_14_p0
    (pCat pvn_m8_r512_6_14_p1
    (pCat pvn_m8_r512_6_14_p2
    (pCat pvn_m8_r512_6_14_p3
    (pCat pvn_m8_r512_6_14_p4
    (pCat pvn_m8_r512_6_14_p5
    (pCat pvn_m8_r512_6_14_p6
      pvn_m8_r512_6_14_p7))))))
private def pvn_m8_r512_6_15_p0 : List ℕ :=
  [2000036611691831, 2000013503274204, 2000031736653700, 2000051886395757, 1999907056252340,
    2000016578635149, 1999994291929453, 1999938842796897, 2000107151635024, 1999949172229687,
    2000034645176849, 1999936097543629, 2000088019409452, 2000018975999023, 2000079766626155,
    1999903923753174, 2000050716671899, 2000034599894555, 1999966650711898, 2000059463161823,
    1999899608138272, 1999962070151943, 1999973790796601, 1999983244904572, 2000009848952469,
    1999952559144224, 1999990639128161, 2000014139916906, 2000027530342255, 1999986226534224,
    1999910692427290, 2000118322404697, 1999902314205159, 2000177305278180, 1999975349577770,
    2000064787245781, 2000029949842710, 1999955731865649, 2000020843692529, 2000001368096623,
    1999926184304647, 1999896362727778, 2000058026831948, 2000006333151820, 1999939184171075,
    2000052778141970, 1999918535275855, 1999932727352929, 2000139481281327, 1999919841841952,
    2000083709887442, 2000032149275285, 2000099200716707, 2000072142705063, 2000165508780220,
    2000007018259860, 2000110217016876, 1999864669345726, 2000211679806797, 1999973012843969,
    2000038751781704, 1999842307947903, 2000027311141252, 2000101971222045]
private def pvn_m8_r512_6_15_p1 : List ℕ :=
  [1999920507118375, 1999988124175229, 2000004407762640, 1999824709305938, 2000213323940649,
    1999930859090874, 2000012640306505, 2000009018045849, 2000077901322990, 1999923121254425,
    1999964080850777, 2000006502998615, 1999924236413098, 2000076558834779, 1999947351939779,
    2000293709590127, 2000157889013504, 2000034980518357, 2000051656904172, 1999867347619543,
    2000077221080235, 1999810896519009, 2000113942944628, 1999755367543243, 1999979765365544,
    1999719429619045, 1999951781823067, 1999837916687418, 2000080308385553, 1999838150549746,
    1999934335390523, 2000187724120457, 1999960715110438, 1999871098947712, 2000127014658523,
    1999890399294239, 1999929155535624, 2000126000080242, 1999833581964839, 2000009679816421,
    2000094996207062, 1999802262258470, 2000318928732486, 1999678558113349, 2000442783593066,
    1999728679963709, 2000375399578603, 1999796029898412, 2000297983821176, 1999631883919963,
    2000506275493139, 1999737709056043, 2000115693886795, 2000039728199528, 2000223661011550,
    2000122438053177, 1999957033135347, 1999965177856377, 2000047528873640, 1999895963233160,
    2000148346475507, 2000205582982954, 2000069613948452, 1999640169537726]
private def pvn_m8_r512_6_15_p2 : List ℕ :=
  [2000575712785834, 1999454776974287, 2000410753543864, 1999827910237170, 2000003678942366,
    2000148700309898, 1999916820321962, 2000238187772735, 1999280259729598, 2000504001100813,
    1999589318637065, 2000081749720500, 2000288030850246, 1999553333445630, 2000541962292108,
    1999644725959271, 2000323005584390, 1999961895756265, 1999923460006032, 2000301199853926,
    1999417472545588, 2000563925326444, 1999725746706909, 1999999997972809, 2000396029571231,
    1999337092213383, 2000814596283357, 1999730414744669, 1999890739538915, 2000515186670597,
    1999100042174926, 2000568445811242, 1999959692124961, 1999471126899443, 2000831820908817,
    1999156616804031, 2000135525533882, 2000442575032934, 1999266509885579, 2000651800884760,
    1999684808306183, 1999727231287078, 2000683675375806, 1999395414942111, 2000293239593896,
    2000337817414263, 1999266163725654, 2000530112187473, 2000066699985757, 1999580757824832,
    2000266586532705, 1999689413020609, 2000317332528009, 2000311609116004, 1999540712586147,
    2000258458285906, 1999895236347040, 1999768042238953, 2000318720749120, 1999793199681908,
    1999962314102716, 2000049964042425, 1999767531964632, 2000225680100783]
private def pvn_m8_r512_6_15_p3 : List ℕ :=
  [1999875390249963, 1999710635242723, 2000273254040583, 1999901389077824, 2000042932592854,
    2000303087779233, 1999714488316227, 2000135905129013, 2000034522569163, 1999475960023754,
    2000273290963993, 1999761795089713, 1999429703600012, 2000664107838191, 1999770305047009,
    1999530855728686, 2000819301133636, 1999511497424322, 1999463059412026, 2000941877431163,
    1999441742449158, 1999407750218084, 2000940874175276, 1999498880688988, 1999601066859525,
    2001054976221686, 1999419051763177, 1999590530750492, 2001241536005376, 1999505663806139,
    1999453427647897, 2001112923786492, 1999438743994445, 1999432782719025, 2001190195433407,
    1999399785673822, 1999223985783744, 2001151924086383, 1999430116704652, 1999112399527474,
    2001324747851042, 1999745030239437, 1998963081301730, 2001219666965212, 1999918149132567,
    1998812433022802, 2001301455418915, 2000366449398110, 1998480643099818, 2000952539606693,
    2000905218083433, 1998314211643234, 2000169361814689, 2001232430328223, 1998641927148621,
    1999677080718361, 2001526383963759, 1999158694577144, 1999141948159709, 2001437690583948,
    1999705865356207, 1998853523362395, 2001396078233157, 2000462077914106]
private def pvn_m8_r512_6_15_p4 : List ℕ :=
  [1998537289486269, 2000633787281163, 2000881968603597, 1998708196137556, 2000159384084163,
    2001307866109698, 1998958003885454, 1999378122673297, 2001456216734350, 1999625461288999,
    1998769327346590, 2001313849679250, 2000644422165222, 1998418104914871, 2000398272341164,
    2001461338352753, 1998775359359967, 1999193542932102, 2001708428470580, 1999921622254966,
    1998285759986098, 2000856463857887, 2001194170547910, 1998675762831623, 1999769349865364,
    2001582930066388, 1999377035938386, 1998627815546918, 2001212674587064, 2000650718209759,
    1998279762177310, 1999969162262289, 2001659487687374, 1999372891889473, 1998795164448000,
    2001237869330063, 2000622717899984, 1998450764573572, 2000135994295155, 2001802870709354,
    1999450412059205, 1998483111002117, 2001011727920494, 2001046500693763, 1998577301792988,
    1999389365350814, 2001535165882194, 2000104979267588, 1998635256869088, 2000596233210601,
    2001241825484860, 1998831517773473, 1998910877905921, 2001493024920737, 2000732384488448,
    1998190783102238, 1999515567229325, 2001804036151129, 2000036379908423, 1998214855390945,
    2000459959691671, 2001899086529456, 1999357514890751, 1998273646245972]
private def pvn_m8_r512_6_15_p5 : List ℕ :=
  [2000932059941177, 2001650356571242, 1998946971846477, 1998486800973679, 2001069342508354,
    2001248320072762, 1998775976618783, 1998738725784777, 2000981599126353, 2000945490441819,
    1999137803625341, 1999447413806594, 2000908318658540, 2000270865416987, 1999058682496082,
    2000027186428632, 2001085981234913, 1999846723846501, 1998952606729921, 2000500849244523,
    2001225085062352, 1999174679546350, 1998354512026219, 2000880515226320, 2002027455658470,
    1999157335956331, 1997556113093980, 2000696608217838, 2002941940642185, 1999620986260124,
    1996332882834188, 1999265260510197, 2003488956102689, 2001251370131467, 1996147654891083,
    1997344507498587, 2003277275154928, 2003757690338990, 1997605695663871, 1995242805272328,
    2001080708197414, 2005574181052503, 2000970206450205, 1994590640718777, 1997061493643128,
    2004612107337596, 2004842363574491, 1996945941878105, 1993448742205120, 2000260438082704,
    2006927413737205, 2002882444597798, 1994201634025390, 1994473331878606, 2003798981357097,
    2008286157313657, 2000888488926530, 1992133735739050, 1994762098145146, 2005099163182367,
    2008323131209834, 1999689015196998, 1991217327542144, 1994737349821671]
private def pvn_m8_r512_6_15_p6 : List ℕ :=
  [2005454390917936, 2008696436723652, 2000034142466783, 1991191095828663, 1994174793174909,
    2005268664075069, 2009972930118818, 2001949062732582, 1991185368425349, 1991236236160378,
    2002180939126950, 2010645652783857, 2006325162319779, 1994391296659395, 1989082577274191,
    1996785994420237, 2008742778214480, 2011322783636408, 2001465229843860, 1989882544836980,
    1989118786279382, 2000057453327142, 2011230398815690, 2010997894841215, 1999472462653887,
    1988177320065808, 1988385009929680, 2000082433987641, 2012146909414810, 2013036041062371,
    2001548394863075, 1987817222478808, 1984122587000295, 1994108185300948, 2009757894234953,
    2018243751173915, 2012457667361587, 1996583943885976, 1982683710515336, 1981454613360744,
    1994350726049992, 2012618735625128, 2023483955308424, 2018864183338338, 2000735635656330,
    1979912820111785, 1969356893172983, 1976335439402656, 1998082610448435, 2023238712034267,
    2037964162916023, 2033214886503501, 2009386652717931, 1976219106687035, 1948343589214398,
    1938816292257756, 1953580400326427, 1989033275827822, 2033337518974908, 2070595124688993,
    2086091798166356, 2070724064020396, 2023301972229097, 1950327528563385]
private def pvn_m8_r512_6_15_p7 : List ℕ :=
  [1863706696963943, 1777389441486158, 1704046191363406, 1652641768702829, 1627324031755191,
    1627591369340753, 1649381000262676, 1686587594626264, 1732560467616771, 1781271900317115,
    1828023504934742, 1869704288180836, 1904704805570241, 1932624760242449, 1953901150084472,
    1969450475649342, 1980378954411538, 1987780473107587, 1992618250292100, 1995673331768659,
    1997538942474336, 1998641300016902, 1999271885562275, 1999621229810552, 1999808721515334,
    1999906227558473, 1999955372805752, 1999979382860233, 1999990754210167, 1999995975408844,
    1999998299683195, 1999999302845992, 1999999722622965, 1999999892922551, 1999999959900051,
    1999999985434382, 1999999994869485, 1999999998248012, 1999999999420159, 1999999999814078,
    1999999999942276, 1999999999982662, 1999999999994973, 1999999999998601, 1999999999999630,
    1999999999999911, 1999999999999983, 1999999999999998]
private def pvn_m8_r512_6_15 : List ℕ :=
  pCat pvn_m8_r512_6_15_p0
    (pCat pvn_m8_r512_6_15_p1
    (pCat pvn_m8_r512_6_15_p2
    (pCat pvn_m8_r512_6_15_p3
    (pCat pvn_m8_r512_6_15_p4
    (pCat pvn_m8_r512_6_15_p5
    (pCat pvn_m8_r512_6_15_p6
      pvn_m8_r512_6_15_p7))))))
private def pvn_m8_r512_6_16_p0 : List ℕ :=
  [2000026799476888, 2000031502736141, 1999962642321913, 2000089493999441, 2000050367848028,
    1999912743958357, 2000081212722254, 1999912033367394, 2000014739550619, 1999936007748040,
    2000078308229899, 1999974058344404, 2000050477858757, 1999944242871305, 1999947849857554,
    2000128032836627, 1999989932981110, 2000038220094619, 2000015911673773, 1999968069824876,
    2000032617166230, 2000022270641525, 2000032624463361, 2000002404118134, 1999927023912093,
    2000005810439121, 1999875002941609, 2000137442347529, 1999844842243142, 2000020486794643,
    1999986383464481, 1999977434451609, 2000057005548909, 1999968946953618, 1999973167319827,
    1999985943111712, 2000007565745825, 1999979620645516, 2000059944549863, 2000120184743852,
    1999959188616208, 1999992352550268, 2000164850475392, 1999892763506055, 2000067720271143,
    1999936445946504, 1999932318918304, 1999937020430762, 2000098519934701, 1999894046652916,
    2000091810967556, 1999836689882529, 2000100121926752, 1999892488742251, 2000034328534986,
    2000020947659173, 1999987411785883, 2000022941176057, 2000029257895834, 2000126213407952,
    2000256789768845, 1999825387885922, 2000157951893456, 2000052615126688]
private def pvn_m8_r512_6_16_p1 : List ℕ :=
  [2000072355718003, 2000073029117723, 2000001029942553, 1999917704668188, 1999973128415696,
    2000163019487791, 1999883942677660, 2000032562503215, 1999922972152886, 1999989869490335,
    2000053333738697, 1999833915648983, 2000178140280375, 1999908376813153, 2000143210925714,
    1999834715003743, 2000183058119418, 1999907737041142, 2000012479140494, 1999821538837353,
    2000021039360107, 2000005739309453, 2000146845061151, 2000206671415230, 2000051002884170,
    2000091202488501, 2000088701780366, 1999831388761758, 2000064823492814, 2000155245082438,
    1999753403414934, 1999869822880231, 2000084309497155, 1999555539114726, 2000251414234228,
    1999473992546896, 2000267960967503, 1999617532922459, 2000307468672292, 1999720590971356,
    2000275484458621, 1999665657658965, 2000321961735635, 1999728869034620, 2000069328263351,
    2000033705930605, 1999860773457869, 1999996346500499, 2000070786991785, 1999921543415713,
    1999987652546930, 1999949036279944, 2000261211478836, 1999903209050033, 2000197890339937,
    1999693081644009, 2000663274470096, 1999516846426324, 2000239504527491, 2000116030798953,
    1999674274089055, 2000418363247893, 1999866249426081, 2000540031763371]
private def pvn_m8_r512_6_16_p2 : List ℕ :=
  [1999589611549528, 2000304183298173, 1999888273515858, 1999738714635297, 2000703432427225,
    1999446996579477, 2000395686195310, 1999963306707660, 1999987336294619, 2000262425990265,
    1999541141266884, 2000432718599047, 1999679632908869, 2000308269177098, 2000191505361129,
    1999458650758892, 2000610363097745, 1999335958225104, 2000115923403382, 2000238841407992,
    1999356547979144, 2000715077180033, 1999523718809473, 1999928957140202, 2000746019186407,
    1999241286911561, 2000642405766181, 1999899146607136, 1999457343503673, 2000896873954562,
    1999369420167522, 2000071749809403, 2000407938659438, 1999294136430971, 2000646425123474,
    2000051438152875, 1999693222964926, 2000617696601614, 1999411811376294, 2000027539032360,
    2000506361588436, 1999361192603906, 2000292774154252, 2000062966710849, 1999531400383362,
    2000343556444602, 1999841618407811, 1999995228753389, 2000087533113388, 1999578598245736,
    2000359577426375, 2000125394888285, 1999641042490272, 2000198703483939, 1999995398701742,
    2000067068000940, 2000186201948227, 1999683052670991, 2000025518281148, 2000027411487346,
    1999813625779280, 2000409326592736, 1999979128878136, 1999746006228984]
private def pvn_m8_r512_6_16_p3 : List ℕ :=
  [2000311162324048, 1999789912567899, 1999989912793669, 2000272572128317, 1999483588514768,
    2000208842721137, 2000291596500945, 1999354054458721, 2000394888094475, 2000103070062292,
    1999143801500154, 2000620177672198, 2000182712640480, 1999188751833902, 2000809889655301,
    2000189620585562, 1999127037702178, 2000798077555292, 2000032325964561, 1998864764075879,
    2000639890834374, 2000035296839845, 1999009220283620, 2000832366365804, 2000067034444162,
    1998937643220438, 2000926808477409, 2000181712482996, 1998801081607017, 2000760465640070,
    2000198362265600, 1998849146172182, 2000840382799361, 2000287327847734, 1998740789227580,
    2000868905801023, 2000632671232684, 1998767468188780, 2000717046483878, 2000810086315919,
    1998659948453372, 2000434638085263, 2001097773244249, 1998704870552530, 2000046413838409,
    2001281390058769, 1998671646207599, 1999425524055010, 2001629170301488, 1999293653225747,
    1998877745410113, 2001463117183539, 1999939293504152, 1998631674972674, 2001131162825929,
    2000510983018868, 1998615126380445, 2000765991137972, 2001017878255237, 1998634214292014,
    2000041214980712, 2001196692082590, 1998834809310731, 1999395699259848]
private def pvn_m8_r512_6_16_p4 : List ℕ :=
  [2001416906479893, 1999543828536195, 1998918182455169, 2001117722200801, 2000083468784170,
    1998681588420439, 2000953112953507, 2001007405806262, 1998610538794486, 2000009219306378,
    2001494725417638, 1999083678471288, 1999056825627473, 2001602263165947, 2000140354538119,
    1998334402916544, 2000772991481522, 2001201005638161, 1998532601818832, 1999607707596048,
    2001758301725590, 1999628444221618, 1998648307662742, 2001163844294509, 2000727037461372,
    1998544983110265, 2000201142748891, 2001431089327235, 1998973782864580, 1998900937410762,
    2001489679742101, 2000473360118410, 1998439223633961, 2000360006897303, 2001475064133626,
    1999065441388914, 1998983645200414, 2001305906246969, 2000251644710099, 1998306395953864,
    2000273451595026, 2001654445321224, 1999228661194709, 1998636313444241, 2001139777564940,
    2000879846863695, 1998684032360404, 1999840145924940, 2001568600432690, 1999728034368929,
    1998629482276989, 2000843396532351, 2001070892222208, 1998572930444408, 1999153297297582,
    2001771106583412, 2000605170936525, 1998189822579681, 1999839515045254, 2001828723092351,
    1999744509006807, 1998223660421528, 2000593343380392, 2001591369580433]
private def pvn_m8_r512_6_16_p5 : List ℕ :=
  [1998988658664810, 1998402120316395, 2001098660580066, 2001404869923322, 1998853648558193,
    1998891771746904, 2001293243572946, 2001007269614876, 1998829347086174, 1999293198878748,
    2001151218849843, 2000500196043621, 1998976008278628, 1999751021395228, 2000783592366245,
    1999692116964362, 1999047189480956, 2000533792492251, 2000977221063326, 1999219997240513,
    1999010674855906, 2001073197905108, 2001073860887422, 1998642531717303, 1998806486721238,
    2001769816615317, 2001683069802135, 1998159960126081, 1997875469158625, 2001799483308939,
    2002570077446183, 1998277479136309, 1996785870467850, 2001337550931102, 2003880821547076,
    1999437098379098, 1995680772639628, 1999523212394639, 2004336129949417, 2001300478707126,
    1995312363908910, 1996918679565812, 2003765458664038, 2004130130241130, 1997088168556136,
    1994576731007662, 2001230821764089, 2006137949037193, 2000919562060751, 1994015174935659,
    1996993386406100, 2005296434665928, 2005334401022686, 1996618023944028, 1992918401080189,
    2000350430135985, 2007406434771830, 2002876105710152, 1993500330427512, 1993799156075065,
    2003809955315448, 2008800130699530, 2001260181511181, 1992104763507105]
private def pvn_m8_r512_6_16_p6 : List ℕ :=
  [1994652178989068, 2005231226346767, 2008569675376739, 1999745351985921, 1991120079275045,
    1994797902296239, 2005695444116753, 2008709093976140, 1999578596381515, 1990666796204361,
    1994167810148377, 2005746263561947, 2010298828389157, 2001750151360874, 1990857242157231,
    1991365817018706, 2002687703983576, 2010834073466862, 2005795621298619, 1993615946492766,
    1988894278166639, 1997393211586956, 2009448676097953, 2011292643225213, 2000691063262774,
    1989260251635260, 1989496066220734, 2001235666308986, 2012033870681501, 2010456456554225,
    1997939883780331, 1987146535056387, 1989048486211769, 2002042748822368, 2013642520193216,
    2012567655253654, 1999365286993116, 1985809063382410, 1984166686133887, 1996358320542564,
    2012399487921852, 2018939302417923, 2010286802690966, 1992913723656084, 1980271415062493,
    1982426036350820, 1998518297652647, 2017376174624688, 2025435973697395, 2016153960198097,
    1994513150235028, 1973898107655863, 1967670272668381, 1980894477407390, 2007169907185231,
    2032149470109939, 2041418174995486, 2028225392411681, 1997064902329215, 1961595393206180,
    1938296535903511, 1939075832087169, 1966122699085049, 2010938126030406]
private def pvn_m8_r512_6_16_p7 : List ℕ :=
  [2057518245486459, 2088057520762065, 2088835381213094, 2054244520304007, 1987895720984466,
    1900895442859455, 1808286155043231, 1725014217203380, 1662639451424384, 1627504324764843,
    1620491545981806, 1638031289354256, 1673783996277828, 1720421880767173, 1771087290081540,
    1820320528084329, 1864442472576446, 1901503978213436, 1930966530059625, 1953272699637131,
    1969425696948240, 1980647899504056, 1988144460284618, 1992967452445608, 1995959537371082,
    1997751113732836, 1998787219623195, 1999366260977025, 1999679101987840, 1999842547716393,
    1999925142062718, 1999965517308836, 1999984611622002, 1999993347978681, 1999997215093367,
    1999998871044626, 1999999556953055, 1999999831728422, 1999999938166631, 1999999978024991,
    1999999992449958, 1999999997493447, 1999999999196337, 1999999999751313, 1999999999925793,
    1999999999978674, 1999999999994111, 1999999999998445, 1999999999999613, 1999999999999913,
    1999999999999984, 1999999999999999]
private def pvn_m8_r512_6_16 : List ℕ :=
  pCat pvn_m8_r512_6_16_p0
    (pCat pvn_m8_r512_6_16_p1
    (pCat pvn_m8_r512_6_16_p2
    (pCat pvn_m8_r512_6_16_p3
    (pCat pvn_m8_r512_6_16_p4
    (pCat pvn_m8_r512_6_16_p5
    (pCat pvn_m8_r512_6_16_p6
      pvn_m8_r512_6_16_p7))))))
private def pvn_m8_r512_6_17_p0 : List ℕ :=
  [1999998240462912, 2000068972812502, 1999990802345543, 1999922018142329, 2000151930156954,
    1999967396890833, 2000061269322679, 1999958630410548, 2000063923604489, 1999949221865535,
    1999965649119960, 2000015160692245, 1999905474620456, 2000085057632140, 2000048686045942,
    1999943496099033, 1999991701656144, 1999981179533678, 2000006431971074, 2000069142399796,
    1999986040259122, 2000110769408959, 1999876250126212, 2000120336208936, 1999922568959034,
    2000047517922671, 2000102338094880, 1999944144589057, 1999988745467935, 1999966635562538,
    1999976466501142, 1999988841286242, 1999984966074395, 1999948329447578, 1999944784080138,
    2000017535838039, 2000049379818838, 1999865295653845, 2000159891620375, 1999928325226152,
    1999932268517553, 1999968251221020, 2000104930868652, 1999892178434627, 2000180691696251,
    1999906460063660, 2000111149242274, 1999985821885656, 2000086747182405, 2000059611615280,
    1999935597333934, 1999955526133563, 2000007443408260, 1999893697263250, 2000126026615310,
    1999835178091151, 2000110087542797, 1999966389010857, 1999850623514394, 2000059756978091,
    2000050759990837, 1999971724918887, 1999853497621156, 2000107923094766]
private def pvn_m8_r512_6_17_p1 : List ℕ :=
  [1999962503252998, 2000127035240526, 2000176774739664, 1999897667031287, 2000169632260342,
    1999927611136883, 2000311269815086, 1999930223833728, 2000105954173221, 1999879367178247,
    2000147967704583, 1999951372565278, 2000015756572157, 1999989315979120, 2000038111663727,
    1999976444807762, 1999893370418598, 2000015718588592, 2000035035835818, 1999927253502683,
    2000059196011225, 1999976424898100, 1999980625126047, 2000124202950679, 2000162656569410,
    1999541531866509, 2000451763433167, 1999447279868015, 2000263873115302, 1999773628899422,
    2000465608864957, 1999842778301276, 2000337231268574, 1999781139525615, 2000307805898504,
    1999897085776245, 2000081407763431, 2000050846325051, 1999825886559799, 2000005687168956,
    1999985262442606, 1999710272722658, 1999997842354401, 1999746850004643, 2000039815774325,
    1999657826572547, 2000350225231338, 1999576670013756, 2000324570540657, 1999719254481043,
    2000097163402708, 2000264743045061, 1999356769712692, 2000540057352496, 1999708149597219,
    2000142461396586, 1999768156391875, 2000029042924943, 2000206470413517, 1999491306294677,
    2000689964656258, 1999545361959046, 2000107082349799, 2000344320515070]
private def pvn_m8_r512_6_17_p2 : List ℕ :=
  [1999664630441778, 2000538880071004, 1999670307337051, 2000147675478958, 1999891207748718,
    1999896371866250, 2000684000930388, 1999511688357402, 2000502103927638, 1999904948045016,
    1999709681132994, 2000708978167258, 1999329775599259, 2000312109400923, 2000297894848067,
    1999476003140811, 2000872918949436, 1999454990413717, 1999934845877247, 2000596774447345,
    1999172137848841, 2000685941929673, 2000072216313989, 1999519221580162, 2000737028867202,
    1999376836626277, 1999944925101178, 2000502672566419, 1999274174989985, 2000317860814791,
    1999984483966947, 1999539304254165, 2000695810369230, 1999697650412801, 1999908555967398,
    2000512377245218, 1999481000744394, 2000272380989129, 2000290229641389, 1999572481323524,
    2000176838897214, 1999876943312585, 1999993187983129, 2000312640119981, 1999808142034591,
    2000228296283192, 2000101906420025, 1999646585253855, 2000288028911008, 2000102030490507,
    1999774261902727, 2000050076633677, 1999818257120178, 2000125523029024, 2000150296794370,
    1999556363624671, 2000130195567915, 2000109164918809, 1999698839840026, 2000330660391496,
    1999839869760076, 1999676563026901, 2000479346714228, 1999822400371252]
private def pvn_m8_r512_6_17_p3 : List ℕ :=
  [2000013466728653, 2000478787489521, 1999313545573813, 2000002368633838, 2000622863720563,
    1999296506287567, 2000187210678987, 2000655068151959, 1999159762036329, 2000279637056636,
    2000716310080358, 1999014016701875, 2000187829497205, 2000715702652929, 1999024424814359,
    2000259524925877, 2000754213246762, 1998915536519142, 2000146172146443, 2000723534676182,
    1998912654909710, 2000210050236527, 2000818886418825, 1998948282244692, 2000336033784925,
    2001054951155022, 1998901566862249, 1999999160368314, 2000884956543260, 1998839915086835,
    1999898251785997, 2000965393336511, 1998847148361669, 1999802747905244, 2001293309047580,
    1999053562935277, 1999452229540356, 2001305146208312, 1999253910598961, 1999154083899150,
    2001362003766729, 1999547292981258, 1998755274493689, 2001330757678784, 2000140268540552,
    1998557533655322, 2001146998324180, 2000804290078734, 1998406707673081, 2000464076425291,
    2001293348732281, 1998799123461149, 1999906512287810, 2001321914228713, 1998996459224133,
    1999335261620643, 2001350199301374, 1999474179295972, 1998906787090666, 2001233718209662,
    2000118387699577, 1998632744939172, 2000802376611149, 2000726497036226]
private def pvn_m8_r512_6_17_p4 : List ℕ :=
  [1998676838283903, 2000291690769510, 2001299512359307, 1999048829767159, 1999605114742914,
    2001383107420534, 1999359020115801, 1998730014516428, 2001314091446166, 2000453958464115,
    1998329454092681, 2000402130389227, 2001237026226668, 1998648411644466, 1999440945512773,
    2001770193213724, 1999763173701013, 1998554818311390, 2001146203488883, 2000871808552134,
    1998478519611637, 2000061366771408, 2001552955532987, 1999210248830775, 1998987653108322,
    2001311849035058, 2000195267424848, 1998508898920193, 2000645042870782, 2001337534559008,
    1998797411443985, 1999252430206481, 2001610604624072, 2000176466311719, 1998523768033753,
    2000595516709145, 2001172920840232, 1998785859204755, 1999279926969180, 2001527907088249,
    2000112814236908, 1998433105677590, 2000592249084725, 2001545129799755, 1999029355858983,
    1998846098824185, 2001178734786586, 2000438939483196, 1998555718265551, 2000142143859336,
    2001413820141264, 1999231945721060, 1998707226765459, 2001221609575821, 2000990408177638,
    1998476325188390, 1999523916211138, 2001935630225890, 2000271093324062, 1998110615250212,
    2000093307160142, 2001699552149148, 1999440861065062, 1998456916244988]
private def pvn_m8_r512_6_17_p5 : List ℕ :=
  [2000956932661758, 2001430334713576, 1998846084117765, 1998803268443292, 2001332217957686,
    2001016220698078, 1998632104142332, 1999172608468118, 2001223143720694, 2000422945396475,
    1998728580000176, 1999763980121015, 2001132680908459, 2000011277886262, 1999122679267416,
    2000391638534145, 2000792116274501, 1999351997493488, 1999445105419716, 2001112435036383,
    2000553072167037, 1998540267406218, 1999348478241372, 2001556181441251, 2000446561007343,
    1998015356261993, 1999479095216761, 2002340651031669, 2000690604614297, 1997299395242600,
    1998951527357328, 2002964640845957, 2001602185821711, 1997051517135343, 1997966125964791,
    2003034137795492, 2002757538460605, 1997151064176863, 1996395490104411, 2002264726361077,
    2004294861891847, 1998540512159694, 1995174670544439, 2000510103270717, 2005297791317173,
    2000759222343780, 1994413011725907, 1997359894735563, 2004768595206329, 2003814111422128,
    1995826964519646, 1994413567204510, 2002332994227458, 2006462757350498, 1999708485298471,
    1993137406137967, 1997847884131413, 2006493586299623, 2004990527080680, 1995409475218349,
    1992929118684574, 2001694889414830, 2008059603681452, 2001854882017624]
private def pvn_m8_r512_6_17_p6 : List ℕ :=
  [1992329364942026, 1994086439650626, 2004800487131770, 2008639580672175, 1999949020416661,
    1991602805186047, 1995925247234685, 2006649219707541, 2008151146545561, 1998087006091066,
    1990697885432661, 1996467129990252, 2007333948658512, 2008054753131132, 1997394138953236,
    1989798671768227, 1995715478292546, 2007557920569559, 2009847257213161, 1999529919763871,
    1989790845896599, 1993010997519609, 2005160731206606, 2011083018289594, 2003364066251195,
    1991273542636179, 1989391837624509, 2000206326633778, 2011313653638948, 2009922203052074,
    1997451385003150, 1987771900288985, 1991650776247854, 2004984547256511, 2013417891639163,
    2007792275124696, 1993739828642547, 1985697166420119, 1992076917196294, 2006858680320656,
    2015631309335684, 2009604644901291, 1993922470946551, 1982804099690406, 1986562083610812,
    2002449716023813, 2017118635368456, 2018027774406193, 2003886140026976, 1985692721895798,
    1977979619010644, 1987482703651685, 2007934595966783, 2024586543824828, 2024810591700841,
    2007076224445225, 1982201182544762, 1966345273770991, 1970630369195564, 1994060084861597,
    2023894344317855, 2042888421928839, 2038930579442107, 2011689988930409]
private def pvn_m8_r512_6_17_p7 : List ℕ :=
  [1972979006760080, 1941058305604181, 1932042511540866, 1952568767359037, 1996837372046265,
    2048869107873253, 2088559145475997, 2098799243388698, 2070940702356366, 2006920439013372,
    1917847325712037, 1820094221580803, 1730551407171362, 1662601360633260, 1623786086856178,
    1615391972463214, 1633568581436603, 1671284107991618, 1720407500338378, 1773399539939776,
    1824363868985049, 1869448653528919, 1906743745325864, 1935877869225470, 1957507298815543,
    1972834705628195, 1983234137303317, 1990004904625654, 1994242003166365, 1996793724084448,
    1998273948474443, 1999101594723434, 1999547865189872, 1999779998759334, 1999896508690366,
    1999952941131738, 1999979319872220, 1999991219232339, 1999996398775731, 1999998573888508,
    1999999454915004, 1999999799009055, 1999999928541540, 1999999975519251, 1999999991924314,
    1999999997436920, 1999999999218083, 1999999999770973, 1999999999935682, 1999999999982716,
    1999999999995572, 1999999999998926, 1999999999999758, 1999999999999953, 1999999999999994]
private def pvn_m8_r512_6_17 : List ℕ :=
  pCat pvn_m8_r512_6_17_p0
    (pCat pvn_m8_r512_6_17_p1
    (pCat pvn_m8_r512_6_17_p2
    (pCat pvn_m8_r512_6_17_p3
    (pCat pvn_m8_r512_6_17_p4
    (pCat pvn_m8_r512_6_17_p5
    (pCat pvn_m8_r512_6_17_p6
      pvn_m8_r512_6_17_p7))))))
private def pvn_m8_r512_6_18_p0 : List ℕ :=
  [1999971421086065, 2000008635800870, 2000142162165121, 1999880120079980, 2000032549152223,
    1999980743203096, 2000084315478948, 2000024379705660, 1999969447689514, 2000096053992172,
    1999966313125887, 1999993767851133, 2000055562641341, 1999934483394206, 1999920005212932,
    2000037754990592, 1999962240480175, 2000129512886463, 1999884800807142, 2000089506091696,
    1999916610258264, 1999962064520919, 2000088853110020, 1999964672482057, 2000051273589974,
    2000060697748067, 1999985647716773, 1999969765471810, 2000015206187181, 2000030814561328,
    2000065958862845, 1999972316360864, 2000108132879070, 1999831878974151, 2000069587925372,
    2000004772771799, 1999976929636229, 1999853621437763, 2000166080779837, 1999807562161841,
    2000028945659045, 1999975847264607, 2000028238910883, 2000026176708035, 1999966864418356,
    1999961673181749, 2000023816520980, 1999857411436687, 2000168849399841, 1999912353935820,
    2000056019638399, 2000028859555128, 1999939939982880, 2000174596081561, 2000027004179875,
    2000015184416568, 1999972900278558, 2000095919112023, 1999881208466199, 1999871595696331,
    2000219069959829, 1999817276815463, 2000131804913637, 1999790122756967]
private def pvn_m8_r512_6_18_p1 : List ℕ :=
  [2000104201181143, 1999895129713505, 2000122598849855, 1999918279647506, 1999964960153104,
    1999888927953209, 2000016018529213, 2000128141559463, 2000051574662520, 1999998221245842,
    2000017831239576, 2000090783106764, 2000176874654026, 1999984584171779, 2000116569137177,
    2000032470542565, 2000150266961148, 1999691312805461, 2000513600927073, 1999460870599042,
    2000511865967147, 1999725834045005, 2000112704155210, 1999750931775028, 2000324927886046,
    1999712606824006, 2000112398323410, 1999899887633774, 2000022232105157, 2000055041052315,
    1999944027830593, 2000155575745643, 2000121238576449, 1999737071173454, 2000112726021803,
    1999659572697235, 2000193181088120, 1999816854039974, 2000430141095558, 1999682455058199,
    2000343471036682, 2000077072819458, 1999856704664341, 2000485766312377, 1999502307800525,
    2000551068086465, 1999674495057501, 1999975889590771, 2000201964995830, 1999603882024600,
    2000117840951635, 1999452378233718, 2000429211050826, 1999594392948559, 1999673744715634,
    2000544294382780, 1999402272607682, 2000357596305870, 1999882049527866, 1999821660623012,
    2000279303033978, 1999611358345719, 2000469684939523, 1999567388496074]
private def pvn_m8_r512_6_18_p2 : List ℕ :=
  [2000044613663955, 2000266451448724, 1999351664895498, 2000646796114759, 1999738650071333,
    1999704644193370, 2000613759738334, 1999324292956457, 2000647248780616, 2000209564278252,
    1999364554360338, 2000729382936857, 1999409546434210, 2000111363287839, 2000641539538800,
    1999256553481632, 2000643955796373, 2000147767099117, 1999521089893798, 2000722090028548,
    1999548352916393, 1999902806553176, 2000612109038878, 1999456241827629, 2000425323990991,
    2000248412061272, 1999474272953556, 2000483069230795, 1999746456671665, 1999864399717375,
    2000616520275445, 1999630404754961, 2000066193595790, 2000277161685187, 1999667971361157,
    2000196025516360, 1999960289092878, 1999761088187900, 2000074215358578, 1999745313301271,
    2000132414476551, 2000215293779088, 1999649816066782, 2000160565521100, 2000174271299579,
    1999828423223377, 2000268551388556, 1999989347373860, 1999884633960633, 2000096658542967,
    1999665629597094, 2000232468931774, 2000362429503752, 1999546687738123, 2000209996518127,
    2000244693011365, 1999698565653495, 2000417809862103, 1999882529041606, 1999572989038210,
    2000591078299298, 1999773322171937, 1999636014370469, 2000630356285486]
private def pvn_m8_r512_6_18_p3 : List ℕ :=
  [1999458949750151, 1999650310394080, 2000935104521142, 1999465965835077, 1999500336870482,
    2000833358693437, 1999419877018376, 1999683563025778, 2001120601383867, 1999433222335587,
    1999505679269730, 2001027755096535, 1999401138032501, 1999497917233123, 2001059967019997,
    1999403622507432, 1999521086963662, 2001179678356400, 1999469744623936, 1999450463313340,
    2001120845799987, 1999402673099894, 1999349853763357, 2001238199868256, 1999549368914464,
    1999169789633438, 2001151873953833, 1999671660831270, 1999035755088500, 2001054856753353,
    1999729069639946, 1998863865740258, 2001233692557880, 2000272167984113, 1998730747889100,
    2000987572578648, 2000571994265408, 1998535027310802, 2000545794993026, 2000778734333115,
    1998401717871330, 2000148928747598, 2001306882157771, 1998686957792407, 1999583640221909,
    2001529654278959, 1999157815977527, 1999024462830857, 2001429712722132, 1999761288739048,
    1998666815643273, 2000989961698202, 2000238636209006, 1998717736358291, 2000824768497753,
    2000768254681961, 1998655313364877, 2000270809621378, 2001250326216685, 1999012222532607,
    1999696052502455, 2001413083450394, 1999439431760939, 1999032743352119]
private def pvn_m8_r512_6_18_p4 : List ℕ :=
  [2001203271043913, 2000008792435051, 1998616184792047, 2000825660077214, 2000760657311702,
    1998527372435590, 2000105161413174, 2001403020500236, 1998884636831952, 1999094214634663,
    2001685045110066, 2000137418584866, 1998545321294890, 2000950897773144, 2000963740597213,
    1998423601255635, 1999841789933698, 2001614211713852, 1999258533171095, 1998756656793781,
    2001204901610533, 2000282303352195, 1998465144501151, 2000490758403437, 2001270998668829,
    1998920692729963, 1999457412765059, 2001499049942812, 1999825721681051, 1998613890945244,
    2000992365876093, 2001129105236879, 1998616267801977, 1999502045081971, 2001518118217734,
    1999773690716919, 1998652012877013, 2000906759561894, 2000958801566251, 1998645429398798,
    1999673245962778, 2001686470139149, 1999849385377083, 1998494362656729, 2000778964036313,
    2001210309471757, 1998785321772740, 1999242242266656, 2001368079460915, 2000110923456259,
    1998677087851021, 2000686086166313, 2001344227534718, 1998828512097484, 1998886568475201,
    2001475430988799, 2000644517212568, 1998222928485290, 1999734920440709, 2001810093059842,
    1999785515354275, 1998177842815230, 2000517649400441, 2001613610519712]
private def pvn_m8_r512_6_18_p5 : List ℕ :=
  [1999240029150981, 1998842822041496, 2001256000819600, 2001024897428321, 1998579557443548,
    1999184669839643, 2001437354018388, 2000540651813349, 1998623039292356, 1999762551723132,
    2001286806906077, 2000001956195832, 1998957825237882, 2000345610970293, 2000863390407031,
    1999372593922216, 1999311543967294, 2000758488831766, 2000262694068956, 1998850412740659,
    1999960024706077, 2001460316948487, 1999864502950083, 1998306907364359, 2000370657507344,
    2002048617517009, 1999621789393982, 1997847549846435, 2000615115112920, 2002465360969723,
    1999208008992936, 1996973797707322, 2000548585477835, 2003326265877775, 1999647940355844,
    1996278280882366, 1999919251185421, 2003970055091557, 2000565652761643, 1995813268425334,
    1998844045911319, 2004436476036060, 2002138142046933, 1995769974666206, 1996970229770305,
    2003843013271424, 2003903731384315, 1996698330332651, 1995121706725491, 2002385005270642,
    2005805534653509, 1999073183292636, 1993731881764163, 1999203002571824, 2006123205988471,
    2002322991591837, 1993986360392805, 1995364729931851, 2004442158663144, 2006027891524696,
    1997227327535002, 1992546717343815, 2000015095503206, 2007778055125671]
private def pvn_m8_r512_6_18_p6 : List ℕ :=
  [2003202308907740, 1993396027147120, 1994010656927395, 2004325869213723, 2008219238144685,
    1999360388710965, 1991145785647146, 1996131837835577, 2006854490006014, 2007213441068870,
    1996761755475463, 1991252390108823, 1999055455760465, 2008793033898784, 2006149536836609,
    1994776552159293, 1990959680927115, 2000224323589521, 2009518345989482, 2005645015125917,
    1993657824276318, 1989848900169073, 1999531916626134, 2009971536617451, 2007442186388424,
    1995234135814057, 1989160169266598, 1997082265307955, 2009016704993463, 2009899118576609,
    1998394333509002, 1988442280711005, 1992211612029065, 2005501454196188, 2012822002923730,
    2005586742299388, 1991961911256670, 1987401111978446, 1997180440848571, 2010632461796180,
    2012988919723374, 2001387114643901, 1987838589294058, 1986546384328687, 1999250228451689,
    2013511609839191, 2015117710224377, 2001939553260888, 1985952562495079, 1982022706633935,
    1994278413739958, 2012390109066036, 2020627914392524, 2011411182678557, 1991770600335452,
    1977648590680533, 1981058305624106, 2000480794108637, 2021809945786172, 2028792554656756,
    2014974770748243, 1988545876730025, 1966954962992353, 1965322669142687]
private def pvn_m8_r512_6_18_p7 : List ℕ :=
  [1986490294835893, 2018946813395020, 2043544471133077, 2044607604002733, 2018886447899962,
    1977576877846743, 1940756406077819, 1927524260307665, 1946900633397505, 1993623941795073,
    2050275780522138, 2094224303849034, 2106066009651547, 2076139515301931, 2006991761464509,
    1911564217473570, 1808448473575346, 1716290266222292, 1649232878266484, 1614496784438509,
    1612247105791924, 1637178282480459, 1680921302871964, 1734429185280778, 1789777312867099,
    1841157983973254, 1885127729732563, 1920324748910766, 1946914829108451, 1965983816780211,
    1979017630195036, 1987532690602430, 1992860781725912, 1996058776256454, 1997902026138013,
    1998923051034192, 1999466896851157, 1999745548407334, 1999882915855657, 1999948074930467,
    1999977813156386, 1999990869968083, 1999996383485594, 1999998621860208, 1999999495125856,
    1999999822329980, 1999999939995019, 1999999980571366, 1999999993976524, 1999999998214398,
    1999999999494724, 1999999999863791, 1999999999965111, 1999999999991539, 1999999999998071,
    1999999999999594, 1999999999999925, 1999999999999990]
private def pvn_m8_r512_6_18 : List ℕ :=
  pCat pvn_m8_r512_6_18_p0
    (pCat pvn_m8_r512_6_18_p1
    (pCat pvn_m8_r512_6_18_p2
    (pCat pvn_m8_r512_6_18_p3
    (pCat pvn_m8_r512_6_18_p4
    (pCat pvn_m8_r512_6_18_p5
    (pCat pvn_m8_r512_6_18_p6
      pvn_m8_r512_6_18_p7))))))
private def pvn_m8_r512_6_19_p0 : List ℕ :=
  [2000003371632787, 1999874691038170, 2000145413975330, 2000017239972480, 2000020681907290,
    1999982867873389, 1999919544274086, 2000084049831339, 2000026699509669, 1999973442434118,
    2000062253359769, 2000064479072894, 1999912433621970, 2000120838052455, 1999932908122927,
    2000112178249977, 1999911293016030, 1999918772540773, 2000049807239987, 1999927845274172,
    2000035104464017, 2000066879650969, 1999976940866764, 1999965134759747, 2000022517795882,
    1999940482246096, 2000039077901400, 1999917467685237, 2000173529167751, 1999941043687530,
    2000056900418490, 1999971297074467, 2000062163792404, 1999829507407901, 2000226838724482,
    1999995420099955, 1999955346184089, 2000044265035849, 2000023823718216, 1999954767953771,
    2000037099275441, 1999882869567192, 2000139245079576, 1999859639766597, 1999973837440961,
    2000020266031923, 1999864325312800, 2000099730756143, 1999968714444154, 2000023917086737,
    1999992094342170, 1999962122343695, 1999961452484676, 1999900219867867, 2000267897230282,
    1999709732360521, 2000150817472789, 1999948487409131, 2000106302234519, 1999922751100599,
    2000133350329369, 2000066138364211, 2000044963280969, 1999980720511545]
private def pvn_m8_r512_6_19_p1 : List ℕ :=
  [1999938766440261, 2000002130153949, 2000008628500036, 1999997718974334, 2000038215092771,
    1999862001079741, 2000021603106027, 1999882559770676, 2000249323879705, 1999759505692880,
    2000284891890840, 1999367700902262, 2000562309358087, 1999615125720122, 2000221413770803,
    1999905919894708, 2000164085902263, 1999807402833814, 2000314268147059, 1999950362919328,
    2000025609496691, 2000233749908076, 2000032720656632, 1999981296003928, 2000084746796295,
    1999887988957637, 2000360477027093, 1999670892575275, 2000272744093193, 1999789096175092,
    2000233231647149, 1999728563612677, 2000143510969745, 2000087336733861, 1999600857873297,
    2000485253824524, 1999401452213960, 2000385804848409, 2000008878880344, 1999954409873475,
    2000389430804857, 1999444980121458, 2000315606268308, 1999674541663062, 2000074860187252,
    2000009625698159, 1999777648786817, 2000624543314264, 1999416578734100, 2000387020202376,
    2000369678396698, 1999521119399891, 2000498800820937, 1999758198384068, 2000299001759986,
    1999947229914950, 1999738167282848, 2000418791683861, 1999366261202349, 2000227378953370,
    1999993999778286, 1999234570913377, 2000647715537462, 1999465119246383]
private def pvn_m8_r512_6_19_p2 : List ℕ :=
  [1999888853475920, 2000535259287077, 1999167160141665, 2000540656927212, 1999920344537186,
    1999516038999346, 2000817507696357, 1999366912250910, 1999948316705594, 2000468252544456,
    1999285696278397, 2000551894360862, 2000008118659775, 1999278907233279, 2000630138011373,
    1999746190032495, 1999960277862037, 2000641683783428, 1999436852525697, 2000247745732536,
    2000255776302350, 1999471757691288, 2000457298527093, 1999936584750877, 1999824149953071,
    2000568712546069, 1999793188610877, 2000043692087230, 2000321874520462, 1999668755475511,
    2000091030696620, 2000152653010887, 1999985112890059, 2000288768882851, 1999875460848715,
    1999965596453734, 2000204684569002, 1999740117535621, 2000179939488827, 2000261551819755,
    1999691983821223, 2000177918078110, 2000150938708502, 1999902379021108, 2000222514690385,
    1999705431961282, 1999881133479477, 2000289514823532, 1999539039932961, 2000073659105997,
    2000386091333585, 1999428249410313, 2000116794005263, 2000350542182608, 1999667162259663,
    2000470764294074, 2000035220319479, 1999320951901287, 2000612658612029, 2000081277570701,
    1999292010701534, 2000696278760450, 2000009980444378, 1999273859835544]
private def pvn_m8_r512_6_19_p3 : List ℕ :=
  [2000945803430590, 2000093985684757, 1999066137199098, 2000826152978385, 2000133136046712,
    1999139601195732, 2000871872280334, 1999996891430572, 1998907060203632, 2000875973416490,
    2000203233181107, 1998996185237363, 2000780402766980, 2000043908233553, 1998879588503368,
    2000871136818199, 2000273104770522, 1998930021548925, 2000858246393984, 2000362962107359,
    1998833385019340, 2000741010721711, 2000471438680619, 1998711553709790, 2000578552044705,
    2000756013334970, 1998833869409179, 2000445528432877, 2000893365068376, 1998726120041381,
    2000181008922799, 2001221816434217, 1998793774544468, 1999706936527226, 2001451651189545,
    1999155206840836, 1999288750296303, 2001378671903847, 1999346252267391, 1998801429133529,
    2001388882465652, 2000011526939632, 1998572517794580, 2001157522945221, 2000733144969814,
    1998565780923097, 2000501858896314, 2000962043367973, 1998622069927890, 1999859649446161,
    2001121436945962, 1999011392638448, 1999504691686758, 2001223757813765, 1999366424513434,
    1999073557587187, 2001281105183596, 2000009659578839, 1998612383295264, 2000737851003170,
    2000566820064139, 1998627964166548, 2000289892091297, 2001147540456425]
private def pvn_m8_r512_6_19_p4 : List ℕ :=
  [1998870593846979, 1999596485594394, 2001472784410047, 1999490737470323, 1998952246275900,
    2001444676397019, 2000404213574937, 1998428333249426, 2000654373425224, 2001253330887784,
    1998557090067292, 1999461116265058, 2001598596736222, 1999530928368359, 1998689268797453,
    2001165417761542, 2000443600871891, 1998356480490345, 2000326004592467, 2001456516628222,
    1999089989243262, 1999355234531587, 2001412984623578, 1999876791419331, 1998670643474297,
    2000908093623968, 2000902036018504, 1998587440462658, 1999721457953839, 2001397950565462,
    1999342099100748, 1998662623551934, 2001172359905533, 2000820983204888, 1998548231085881,
    1999901937099054, 2001479248507752, 1999456580747567, 1998936183414323, 2001257812288380,
    2000659812570528, 1998463495077698, 1999978822025905, 2001594967440660, 1999439249756586,
    1998659346604049, 2001035840541435, 2000857751890730, 1998692863148081, 1999833393201431,
    2001504040946521, 1999639092810781, 1998734819741391, 2001060859319896, 2001042057027841,
    1998436877698168, 1999223863478421, 2001758662122665, 2000376928040414, 1998290735268205,
    2000223524790335, 2001736254559570, 1999392630777062, 1998432726825285]
private def pvn_m8_r512_6_19_p5 : List ℕ :=
  [2000885856660453, 2001210812268888, 1998815702530798, 1999110250911383, 2001303811662213,
    2000421074696528, 1998469332215063, 1999811761160754, 2001542367317190, 2000075067543422,
    1998817203833661, 2000334899583049, 2000996354383079, 1999426231359703, 1999302553649971,
    2000786977067987, 2000352033614383, 1999030091041307, 2000026720724444, 2001159354066177,
    1999664112318711, 1998798373665415, 2000791617360190, 2001357198747038, 1998800034546868,
    1998382033447657, 2001361494231234, 2001634861941799, 1998311102520325, 1998223905168336,
    2001947666703530, 2001940005408574, 1997832813159888, 1997913427798945, 2002542647564005,
    2002630375141230, 1997487994907180, 1996944949687773, 2002362822965242, 2003360750242320,
    1997674802561137, 1996083272243049, 2001981870163267, 2004351415376298, 1998382977236280,
    1995077261794191, 2000929239575951, 2005355462604581, 1999998103889254, 1994518032896534,
    1999153762298588, 2005678128733326, 2002034356331888, 1994435981414832, 1996572000635300,
    2004947157524256, 2004745760593624, 1996118123418639, 1994202124502929, 2002583379092690,
    2006753290466160, 1999170990505972, 1992533395782661, 1998252205925518]
private def pvn_m8_r512_6_19_p6 : List ℕ :=
  [2006877513559214, 2003810423137310, 1993868738391061, 1993523122040633, 2003682459040634,
    2007978603063611, 1999339147414501, 1991555732697490, 1997226898105337, 2007598039611506,
    2006348445479992, 1995260600823655, 1991422003780765, 2000687343426580, 2008753180685269,
    2003238402963952, 1992546528521686, 1993002488144318, 2004216473214952, 2009688619296636,
    2001276322806579, 1991126618103372, 1993964381255056, 2005882506346384, 2009969656103910,
    2000216066398361, 1989866360852955, 1993065487180007, 2005576500070784, 2010657786890392,
    2001531991218884, 1990237023490512, 1991659578094589, 2004168624412077, 2011809972003260,
    2004684435240458, 1991399138857955, 1988315692969685, 1999429800910679, 2011581662229196,
    2010314816992837, 1996979737144508, 1987027111127137, 1992062089019312, 2006647219900462,
    2014523617736006, 2006689571888453, 1991207209857525, 1984508299601257, 1994028446229030,
    2010477581281626, 2017273818573139, 2007115520863019, 1989199144364163, 1980454786002404,
    1989592199371581, 2008953180229044, 2021330948152842, 2015242795420522, 1995075796570075,
    1977558178452896, 1977881263113031, 1997138411836316, 2021127061897335]
private def pvn_m8_r512_6_19_p7 : List ℕ :=
  [2031144299690524, 2018191032038411, 1989920555830436, 1965536812128261, 1962625134232551,
    1985157846092424, 2020522427349396, 2047095032936651, 2047251569074270, 2017862389338257,
    1972415647498750, 1934060619161612, 1923772120970625, 1949925744429032, 2004202467957588,
    2065160935056376, 2107144522718787, 2110178707657391, 2066769564564910, 1983464309024785,
    1877470198862744, 1770413686481077, 1681888436619805, 1624882308313253, 1604015278283086,
    1616368680279500, 1653953991600861, 1706676469027066, 1764877762162688, 1820968144426050,
    1870074935392592, 1909914627619969, 1940210936653963, 1961963330407305, 1976780759971997,
    1986389128969182, 1992334456964920, 1995850826330452, 1997841198079604, 1998920296781284,
    1999480975816941, 1999760248835939, 1999893617240106, 1999954677274892, 1999981471518288,
    1999992736724429, 1999997272126775, 1999999019429971, 1999999663035235, 1999999889453799,
    1999999965433385, 1999999989717417, 1999999997096580, 1999999999223892, 1999999999804235,
    1999999999953595, 1999999999989722, 1999999999997893, 1999999999999610, 1999999999999939,
    1999999999999994]
private def pvn_m8_r512_6_19 : List ℕ :=
  pCat pvn_m8_r512_6_19_p0
    (pCat pvn_m8_r512_6_19_p1
    (pCat pvn_m8_r512_6_19_p2
    (pCat pvn_m8_r512_6_19_p3
    (pCat pvn_m8_r512_6_19_p4
    (pCat pvn_m8_r512_6_19_p5
    (pCat pvn_m8_r512_6_19_p6
      pvn_m8_r512_6_19_p7))))))
private def pvn_m8_r512_6_20_p0 : List ℕ :=
  [2000086085365659, 1999845365622389, 1999983797045506, 2000056488566006, 2000006924212026,
    2000101924654814, 2000012478612580, 1999924655402546, 1999964494177402, 2000119265727519,
    1999873603070051, 2000111202989530, 1999981123410993, 2000040189759312, 2000072232873776,
    1999909996986752, 2000061509342319, 2000078858995830, 1999987814237299, 1999983457042539,
    2000040890965913, 1999868491769865, 2000037076262676, 1999899802363489, 2000138951002644,
    1999923512285348, 2000057329346703, 1999953279617967, 2000112558834670, 1999809603686942,
    2000060222963327, 2000033731741855, 1999921380965412, 2000046071052293, 2000166653804514,
    1999880687140778, 2000061762060839, 1999904931719668, 2000081810221077, 2000074284916499,
    1999887387677552, 2000155450976178, 1999975869829329, 1999998099696035, 2000033702574367,
    1999940627965013, 2000075239070413, 1999867471977187, 2000211214289486, 1999706333770792,
    2000156920376963, 1999884678666116, 1999938031499048, 1999977067004290, 2000129138021372,
    1999968092481647, 1999910032671668, 2000017708111350, 2000006113520764, 1999962798758027,
    1999999400501056, 1999936440936115, 2000123484712697, 1999842787707449]
private def pvn_m8_r512_6_20_p1 : List ℕ :=
  [2000159100461019, 1999757139624119, 2000408609051308, 1999640996842655, 2000579857363538,
    1999535185048215, 2000356681935713, 1999760557471243, 2000054972216946, 2000028275672871,
    2000176229277129, 1999696549724674, 2000004756720260, 2000090547070201, 1999905530176331,
    2000066060152320, 2000112137898488, 1999656314517993, 2000253279145153, 1999693435826891,
    2000284172618965, 1999690858473871, 2000190251501729, 1999981062277814, 1999987688540343,
    2000115516340810, 1999715726632602, 2000675077688713, 1999559407176640, 2000336220412989,
    2000118179025457, 1999711068165213, 2000532729935395, 1999572248861227, 2000382915936694,
    1999898882403470, 1999935325044751, 2000272346551215, 1999577160819819, 2000443138244227,
    1999698632839635, 2000115572022715, 2000203504504268, 1999238074116295, 2000616315855774,
    1999791270002759, 1999896538488559, 2000438210746322, 1999743137079657, 2000277957524105,
    1999600141686559, 2000021243517980, 2000356346011406, 1999231430499254, 2000536225728693,
    1999936026347988, 1999623310319224, 2000866353963383, 1999381119122304, 2000210519491916,
    2000527484044295, 1999354150940952, 2000709110458428, 1999858421238224]
private def pvn_m8_r512_6_20_p2 : List ℕ :=
  [1999622264979902, 2000758558353007, 1999365088521592, 1999989431684093, 2000384230460427,
    1999118719586807, 2000331241603033, 1999995598550602, 1999375658309786, 2000602655405957,
    1999587613175529, 1999677946371785, 2000558296550053, 1999559684137203, 2000172869976062,
    2000173657460463, 1999403779036470, 2000385503474382, 2000061549388224, 1999700881336666,
    2000301634536253, 1999684946518087, 1999837736889867, 2000294104445712, 1999786667365039,
    2000108376207495, 2000211897329768, 1999881436565938, 2000173201293348, 1999925068101859,
    1999924152721584, 2000238071928521, 1999754963978204, 2000092117381877, 2000424455617214,
    1999813459596811, 2000151903917140, 2000159622631476, 1999690041661519, 2000231704517845,
    2000062872519745, 1999959378006860, 2000436480166761, 1999686296047703, 1999883903063225,
    2000589668934087, 1999618732788126, 1999903288076409, 2000526340842966, 1999565457463788,
    2000104768360800, 2000530600117776, 1999514816666325, 2000255729882086, 2000322874059429,
    1999117888614768, 2000365797527833, 2000572453295663, 1999008132453512, 2000197432107919,
    2000527500356320, 1999052724930370, 2000457263230410, 2000769024791002]
private def pvn_m8_r512_6_20_p3 : List ℕ :=
  [1998958321130482, 2000296148575611, 2000800182366409, 1999009621194953, 2000251504479865,
    2000701625959721, 1998907999853995, 2000311591662435, 2000950959621083, 1999000284045955,
    2000149649118657, 2000871781096976, 1999045509608459, 2000228042500783, 2001004938509743,
    1998908988197365, 1999889110535866, 2001058316066664, 1999076154562725, 1999812824536707,
    2001161433406462, 1999078886554625, 1999454402160674, 2001206266725771, 1999313373851546,
    1999276875261470, 2001315113639727, 1999607430146799, 1999054838808224, 2001367893428445,
    1999918981730034, 1998587910320167, 2001090857143437, 2000464859325750, 1998550713764752,
    2000761889209761, 2000873212757518, 1998570445606378, 2000353578834935, 2001259558894651,
    1998673569344349, 1999677969333201, 2001507326289318, 1999273764984769, 1999219348513824,
    2001321528539264, 1999692337720007, 1998844065462190, 2000970036924000, 2000086746700517,
    1998725106059979, 2000777178242315, 2000694668351323, 1998815380111000, 2000422471571544,
    2001138957720865, 1998820915775077, 1999566877685672, 2001296053492661, 1999341292654445,
    1998983666198948, 2001146280742617, 1999932257344860, 1998636634925867]
private def pvn_m8_r512_6_20_p4 : List ℕ :=
  [2000930534845513, 2000774419625532, 1998472389762144, 2000079301298037, 2001324728081476,
    1998827727087498, 1999154484299703, 2001569241632089, 1999813757674105, 1998445644391614,
    2001010614370378, 2000905530411882, 1998533023954650, 2000086197638242, 2001529625252225,
    1999221292274240, 1999201161619065, 2001432634684513, 2000033215831886, 1998509309345189,
    2000699700499750, 2001012845432494, 1998769163738945, 1999718153944860, 2001271044525407,
    1999292752291406, 1998808602380660, 2001238204495623, 2000626408652656, 1998559731198251,
    2000227460449741, 2001458964856112, 1999149577702058, 1999015363068457, 2001398907799222,
    2000421303423242, 1998476396475542, 2000226359370982, 2001172542112793, 1998937773856940,
    1999143367629005, 2001429068508836, 2000213382487723, 1998398865410607, 2000400976607086,
    2001457400394809, 1999148135692125, 1999102382354691, 2001328300544917, 2000376528162862,
    1998598508866299, 2000349629935090, 2001367192214170, 1999046746015600, 1998882649756064,
    2001424586433071, 2000732160000182, 1998295407030732, 1999765632160029, 2001901695232615,
    1999937401157299, 1998366996730452, 2000590534961920, 2001372237846674]
private def pvn_m8_r512_6_20_p5 : List ℕ :=
  [1998956574663534, 1998885111472595, 2001292577623085, 2000796109267119, 1998694199477138,
    1999742373563189, 2001409089744265, 1999873667907749, 1998627206291836, 2000416781453001,
    2001191591859154, 1999351392226632, 1999046475215176, 2000665498445238, 2000385400949283,
    1999104642390113, 2000052868550116, 2001073100934412, 1999669213481913, 1999063240315658,
    2000850219603829, 2000936286228807, 1998765699004150, 1999166798133727, 2001622156152092,
    2000707840134881, 1998001707518696, 1999424368496776, 2002405602115631, 2000587635814299,
    1997398406132104, 1999546806608238, 2002840676335732, 2000260959561094, 1996728382443651,
    1999672932662924, 2003550428551274, 2000356222051483, 1996061582267079, 1999400192339881,
    2004240709440945, 2001026701466342, 1995754600293731, 1998797692942158, 2004499521625425,
    2001634239851960, 1995312237996719, 1997710997898883, 2004609110178747, 2002879624077982,
    1995459220766418, 1996293529164617, 2004110989008859, 2004379592054845, 1996362218887264,
    1994874408007775, 2002997318330051, 2006031665436257, 1998197405361664, 1993443710592950,
    2000443793288042, 2006805666876467, 2001045038382823, 1993182503827701]
private def pvn_m8_r512_6_20_p6 : List ℕ :=
  [1997246722888599, 2006461224592580, 2004768887067881, 1994738293093246, 1993441631717002,
    2003274504339319, 2007640956801436, 1998909494809158, 1991422980363318, 1997715423389656,
    2007637326839258, 2004949728994576, 1993927161987310, 1992454900839565, 2003099818358390,
    2008992946325273, 2000801415968403, 1991467723013000, 1995645513837951, 2006725143945825,
    2007310796700754, 1996284054184633, 1990500169986307, 1998992245192771, 2009267102593530,
    2006055428446998, 1994005583177220, 1990792407617607, 2001296339743302, 2010576720625377,
    2005297480167321, 1992610060100225, 1990049578246897, 2001158524982593, 2010726814346711,
    2005663507342956, 1992680458708718, 1989187881327218, 2000108937446220, 2011405917040967,
    2008364061535969, 1994534196839455, 1987202416199298, 1995653882976205, 2009694099476841,
    2012248872747769, 2000078817176978, 1987565658322451, 1989612604701129, 2004242092767162,
    2014903817720631, 2009265290689935, 1993016373991510, 1983680309067370, 1991704253469381,
    2009279227885725, 2018352121187711, 2009096928345614, 1989946514252750, 1979447848187998,
    1988299546697999, 2008978366945834, 2022535373550332, 2015927081352787]
private def pvn_m8_r512_6_20_p7 : List ℕ :=
  [1993975747227089, 1975457634281465, 1977049343268836, 1999039095541131, 2024634974359871,
    2033120729682385, 2016134311499604, 1984476187522721, 1960617399927727, 1962752712364415,
    1991870761042376, 2030545505144511, 2053831163832847, 2044866413071605, 2005411753256578,
    1955320607305296, 1921815204102790, 1925018871815838, 1967561129490211, 2033129216062430,
    2093834909545202, 2122104813096872, 2101384654478963, 2031408230614265, 1926829456774110,
    1810919026084125, 1707556326952251, 1634614608941251, 1600555834446677, 1604463358518986,
    1638547599804458, 1691675946545409, 1752636355056048, 1812362105760851, 1864915740985164,
    1907446371503834, 1939524883667634, 1962259391326483, 1977480343688273, 1987142367755751,
    1992972319748066, 1996321947970295, 1998156716738595, 1999115563391282, 1999593839840199,
    1999821571259646, 1999925066754893, 1999969942505185, 1999988496227488, 1999995804510091,
    1999998544148717, 1999999520207499, 1999999850152101, 1999999955763344, 1999999987694730,
    1999999996786899, 1999999999216144, 1999999999822404, 1999999999962924, 1999999999992949,
    1999999999998803, 1999999999999827, 1999999999999982]
private def pvn_m8_r512_6_20 : List ℕ :=
  pCat pvn_m8_r512_6_20_p0
    (pCat pvn_m8_r512_6_20_p1
    (pCat pvn_m8_r512_6_20_p2
    (pCat pvn_m8_r512_6_20_p3
    (pCat pvn_m8_r512_6_20_p4
    (pCat pvn_m8_r512_6_20_p5
    (pCat pvn_m8_r512_6_20_p6
      pvn_m8_r512_6_20_p7))))))
private def pvn_m8_r512_6_21_p0 : List ℕ :=
  [2000140243152315, 1999971347337120, 1999877518617832, 1999996947764989, 1999973739830475,
    2000004198700348, 2000010700284636, 2000208277443061, 1999882427529919, 2000013533039040,
    2000022776710967, 1999932755918798, 2000066936167609, 1999966688558123, 1999972518510603,
    2000064086739361, 2000102529266486, 1999883868989730, 2000108531774142, 1999927558056879,
    2000127341078082, 1999935484039492, 2000114556373261, 1999952764323758, 2000076534262112,
    1999837128061650, 1999997306030803, 2000054125229421, 1999938305189886, 1999925438582854,
    2000204374254218, 1999881582397560, 2000017155205953, 2000045764871047, 1999916819526190,
    2000061603686764, 1999843064415114, 2000046205483277, 2000152585898198, 1999914665181862,
    2000106472876387, 1999855747023413, 2000205707226347, 1999770677724859, 2000197389338000,
    1999936133882055, 2000006282586950, 2000086522078015, 2000039922281564, 1999934886223299,
    2000020887975946, 2000067954460609, 1999957286086770, 1999926960698201, 2000153313506190,
    1999879793584458, 2000079403013916, 1999673220172163, 2000303502203318, 1999643581657196,
    2000441732372076, 1999488498664371, 2000457122325538, 1999670283524611]
private def pvn_m8_r512_6_21_p1 : List ℕ :=
  [2000144627728382, 1999927647454211, 1999980025273671, 1999954771492417, 2000139815439305,
    1999855646784275, 1999970226685962, 2000086146467047, 1999947424847825, 1999846499121581,
    2000530159990460, 1999675321251878, 2000263528950862, 1999770757227312, 2000154164530384,
    2000014932855077, 1999968437659939, 2000225279881968, 1999546948058817, 2000359257695865,
    1999614014456011, 2000311511475955, 2000026505909832, 1999553744844923, 2000615150280768,
    1999477305003699, 2000151288129792, 1999969814406095, 1999789237207248, 2000385859017259,
    1999559765624982, 2000310589584617, 1999839106472361, 1999919507904911, 2000455239352813,
    1999515209585107, 2000587285651201, 1999870247388692, 1999825378168682, 2000618347105185,
    1999504937742702, 2000249347666054, 2000229337863705, 1999782685200931, 2000301909118367,
    1999530484629296, 2000424174082868, 2000132172971851, 1999377771303637, 2000828255908886,
    1999525621606260, 1999634557022946, 2000620250930373, 1999287629809974, 2000447966068990,
    2000297932547491, 1999347105228486, 2000709988714842, 1999753425749010, 1999661634506744,
    2000600781024952, 1999272289462011, 2000093978235850, 2000479435942207]
private def pvn_m8_r512_6_21_p2 : List ℕ :=
  [1999290368771982, 2000495470160315, 2000122911158848, 1999520203068573, 2000712592772319,
    1999800657237447, 1999854388757708, 2000610226894269, 1999597165146566, 2000144765219076,
    2000341311725519, 1999568999171355, 2000215186681841, 1999882419391380, 1999538991872949,
    2000290531009561, 1999843484903080, 1999707255200583, 2000092226937089, 1999704450527474,
    2000021204474570, 2000205799707775, 1999764010377843, 2000026197067566, 1999932039113612,
    1999873420814373, 2000282094326058, 1999824573857185, 1999911866376509, 2000265901170313,
    1999603587491378, 1999920291887913, 2000258789356249, 1999706336360705, 2000161419957776,
    2000165162163069, 1999788969204250, 2000383604787797, 1999911776772127, 1999665499153084,
    2000470884049088, 1999756213443919, 1999752908517931, 2000797128665201, 1999847125902824,
    1999682417914228, 2000570249110481, 1999670930116590, 1999888807140609, 2000712310772672,
    1999514747210444, 1999932158195767, 2000840952523473, 1999340980115248, 1999865119403003,
    2001028869041322, 1999266224746380, 1999616042460522, 2001057570606830, 1999467990821767,
    1999775628732261, 2001104714579988, 1999279370035211, 1999530984232598]
private def pvn_m8_r512_6_21_p3 : List ℕ :=
  [2001150424321505, 1999444977408869, 1999459720402536, 2000948517770108, 1999300064469072,
    1999425137465373, 2001150216111998, 1999500817692075, 1999333475541799, 2001143968298778,
    1999689377620117, 1999343615224086, 2001126102951761, 1999628565199745, 1999027213311169,
    2001163132170531, 2000019694166790, 1998945414633293, 2000995740421981, 2000174790477054,
    1998843468736483, 2001006498871027, 2000570473666067, 1998675449789313, 2000622507045814,
    2000772520105049, 1998623401461043, 2000379187490005, 2001179959264030, 1998659737281006,
    1999812288934664, 2001397784017317, 1998955211948080, 1999268126685147, 2001403034630652,
    1999458900815212, 1999040368052669, 2001427984292006, 1999964865516924, 1998621977989452,
    2001022807706661, 2000548814338679, 1998593003848621, 2000459359294067, 2000918943182383,
    1998892698238880, 2000106050587562, 2001110530138088, 1999042129446054, 1999603586761209,
    2001256517232613, 1999439547504217, 1999178010878064, 2001299688241914, 2000010725859029,
    1998697514453934, 2000854797990691, 2000572977109965, 1998495306141188, 2000168014172623,
    2001128761905256, 1998936684065257, 1999720589129925, 2001530161093898]
private def pvn_m8_r512_6_21_p4 : List ℕ :=
  [1999409460898249, 1998868030688282, 2001374979571875, 2000271136788787, 1998333864677723,
    2000564975630888, 2001055684372644, 1998510578220221, 1999636388229921, 2001589242964149,
    1999390849183315, 1998763257231121, 2001186870229533, 2000300263697527, 1998480445104982,
    2000448684216964, 2001053270088665, 1998761565847661, 1999546367341908, 2001395810999848,
    1999575918584455, 1998812510118303, 2001111561970212, 2000671521098484, 1998748410289668,
    2000329608558628, 2001302630750520, 1998977603287136, 1999136350135935, 2001484909907693,
    2000220039464308, 1998478817445064, 2000485384248352, 2001088086780602, 1998731277023405,
    1999321035508998, 2001466447146731, 1999954976183987, 1998654799164125, 2000802581494160,
    2001009806818504, 1998744617642709, 1999690968078038, 2001623821332727, 1999760224074872,
    1998486789357806, 2000733088633015, 2000977767787300, 1998721913533013, 1999512665299292,
    2001365974459278, 1999712843925449, 1998612276149325, 2000908997366606, 2001172751066727,
    1998661136025648, 1999319575812595, 2001748920926877, 2000302916783208, 1998245953117441,
    2000247851312292, 2001678854754886, 1999336172204451, 1998616526061448]
private def pvn_m8_r512_6_21_p5 : List ℕ :=
  [2000996759503860, 2000938037918033, 1998755049911472, 1999599623283294, 2001516822805713,
    2000135285884915, 1998655776469696, 2000311705587276, 2001124544535094, 1999272766425760,
    1999103174707739, 2000990261416581, 2000663027969089, 1999046954082034, 1999822416098438,
    2000926004736881, 1999710773820716, 1999223475776327, 2000804646679122, 2000614144487649,
    1998713076194992, 1999472343107493, 2001452436128346, 2000098379758111, 1998228406390868,
    2000302956604793, 2002126315489154, 1999463600803135, 1997774162213806, 2000964207475087,
    2002452064639639, 1998736552562698, 1997405877340196, 2001546344724378, 2002688635037432,
    1998167607461794, 1997267415061974, 2002260686751050, 2003024473147072, 1997514069898024,
    1996676734039343, 2002569011048886, 2003530829406663, 1997295793584054, 1996105659597565,
    2002599395247247, 2004079072432721, 1997402983281012, 1995651729085690, 2002636294069835,
    2004932032914957, 1997762448966726, 1994719289611618, 2001828242941104, 2005625029646632,
    1998653367449068, 1993955962167633, 2000584115180381, 2006251518859025, 2000160154991696,
    1993419705266384, 1998681411768954, 2006567385939881, 2002622423152970]
private def pvn_m8_r512_6_21_p6 : List ℕ :=
  [1993850953049435, 1996217087187800, 2005663405565041, 2005153507239461, 1995245347169706,
    1993437205227926, 2003243858658110, 2007694507429688, 1998863750778274, 1991858173975592,
    1998854471138171, 2008033025969414, 2003631108581224, 1992802718594639, 1993659075389720,
    2004848472633397, 2007788910374627, 1997544901135103, 1990941237244253, 1998866900981162,
    2008547942761206, 2004409870505398, 1993192956399652, 1992967244937245, 2004220655942461,
    2009134438174835, 1999698581350133, 1990282964347636, 1995433929685292, 2007548244375567,
    2008414009907198, 1996647675232373, 1989735946206469, 1998105467789826, 2009808896131598,
    2007926945795357, 1994964089401853, 1989211085631193, 1998781841166769, 2010269804581162,
    2007541526900132, 1994083682018869, 1988210084935254, 1998169140592638, 2011018319211232,
    2009796238260170, 1995804373834775, 1986897490081761, 1994541976094731, 2009309589606154,
    2012788239943448, 2000437398374681, 1987118942082880, 1989093207287905, 2004572227108567,
    2015735167462354, 2009339963412797, 1991948183131537, 1982748490456200, 1992397488477971,
    2011236089439027, 2019362651003598, 2007537071227819, 1987000977384522]
private def pvn_m8_r512_6_21_p7 : List ℕ :=
  [1978347053685620, 1990956635570339, 2013476925866266, 2024420056668470, 2012473603665783,
    1987376552987860, 1971537212382221, 1980221076151009, 2007880223983392, 2032232786823925,
    2032362738949324, 2005834386847229, 1971279411832455, 1954777700650443, 1970596556881155,
    2010407306588720, 2048328558268254, 2057882251598711, 2029304960230913, 1976218207009652,
    1928061700868326, 1913477384881277, 1944548311668845, 2010301685903052, 2081999090060460,
    2126414981413805, 2119967444143767, 2057331531261315, 1951784614616244, 1828621549977481,
    1715528408556573, 1634077570535592, 1595018585421295, 1597930101439871, 1634114693541165,
    1690880597875927, 1755517892891337, 1817958680894068, 1871874627193549, 1914514434070006,
    1945819614511238, 1967332286557915, 1981243480793772, 1989738655166715, 1994649499565319,
    1997341008677310, 1998740926561807, 1999432238792919, 1999756376398004, 1999900629981939,
    1999961523779659, 1999985880830219, 1999995099705914, 1999998395446240, 1999999505813556,
    1999999857367955, 1999999961600248, 1999999990412706, 1999999997796778, 1999999999538599,
    1999999999913162, 1999999999985616, 1999999999997978, 1999999999999779]
private def pvn_m8_r512_6_21_p8 : List ℕ := [1999999999999985]
private def pvn_m8_r512_6_21 : List ℕ :=
  pCat pvn_m8_r512_6_21_p0
    (pCat pvn_m8_r512_6_21_p1
    (pCat pvn_m8_r512_6_21_p2
    (pCat pvn_m8_r512_6_21_p3
    (pCat pvn_m8_r512_6_21_p4
    (pCat pvn_m8_r512_6_21_p5
    (pCat pvn_m8_r512_6_21_p6
    (pCat pvn_m8_r512_6_21_p7
      pvn_m8_r512_6_21_p8)))))))
private def pvn_m8_r512_6_22_p0 : List ℕ :=
  [2000112950844234, 2000118616074570, 1999947987705743, 1999959341071355, 1999895289754263,
    2000091031311985, 1999843953984558, 1999973811733206, 2000154543476388, 2000001826477222,
    2000055238696582, 2000016567746322, 1999990462513619, 1999911472547040, 2000164664522939,
    1999853978191737, 2000050962509019, 1999921014605994, 2000134226628504, 1999952582942946,
    2000081332396645, 1999943620280943, 2000039308580435, 2000039269722812, 1999996583704137,
    1999933619837028, 2000239171889186, 1999948966378371, 1999900120898169, 2000131226571165,
    1999882489266985, 1999989444192702, 1999981359086144, 1999900565507546, 2000204581885023,
    1999803066245472, 2000156999974232, 1999867064832034, 2000222804595722, 1999843664164829,
    1999927070623622, 2000041377220254, 1999966611119445, 2000002246854531, 2000093290041759,
    1999991130493075, 1999992295056326, 1999974159491965, 2000172762702517, 1999728593206825,
    2000255398647340, 1999758948018455, 2000416784865778, 1999525240096691, 2000503142292151,
    1999639067645981, 2000328810561520, 1999769463874223, 2000026748163544, 2000103274138208,
    2000036781249163, 1999894983949212, 2000060993224449, 1999874156330492]
private def pvn_m8_r512_6_22_p1 : List ℕ :=
  [1999985677174073, 1999959782718693, 2000138537920129, 1999609055811608, 2000495177465544,
    1999667135743462, 2000042393617145, 2000075824369515, 1999859379280953, 2000144036001286,
    1999685902232458, 2000464943739149, 1999617811824254, 2000111253263341, 1999987201404887,
    1999672237875266, 2000606504217101, 1999546004370180, 2000387209697856, 2000036628908803,
    1999574543037878, 2000534210779170, 1999742020063787, 2000241045618738, 1999911309490611,
    1999781808077038, 2000426217807277, 1999453173321776, 2000347935521737, 1999931474873025,
    1999754438719545, 2000550620799914, 1999434801607020, 2000134893628971, 2000207030501148,
    1999469095520730, 2000475245200248, 1999768681994642, 1999897441808277, 2000231744116194,
    1999549726737185, 2000575676139442, 1999681358359250, 1999764901789026, 2000962846316803,
    1999313085563328, 2000094394987453, 2000622841201883, 1999331619758347, 2000571797436200,
    2000101460603745, 1999506588546810, 2000718629659053, 1999569416867909, 1999820101242608,
    2000740799675274, 1999440723383202, 2000231831456396, 2000291479230280, 1999191081013132,
    2000471699645024, 2000022858474786, 1999474332445468, 2000612367530336]
private def pvn_m8_r512_6_22_p2 : List ℕ :=
  [1999795105835058, 1999880498757335, 2000546729101164, 1999560591815672, 2000000370007786,
    2000236741674399, 1999540779187401, 2000181978242904, 2000060483927684, 1999683751308198,
    2000307104452579, 1999962212400392, 1999864691613162, 2000368423480779, 1999940581618386,
    1999989093347882, 2000216306306226, 1999918655824142, 2000258838456737, 2000125426422393,
    1999745235044429, 2000121299130799, 1999842366019752, 1999852450767854, 2000271275160165,
    1999579830460429, 1999722306569506, 2000255949410892, 1999660738296319, 1999983186985941,
    2000217155598980, 1999610880935940, 2000112918013628, 2000047323732840, 1999610042587085,
    2000445053341479, 2000024832862113, 1999468926626956, 2000491368172558, 1999925256862409,
    1999349196465218, 2000527129722218, 1999957000614299, 1999440456264560, 2000651909560477,
    1999996604150291, 1999585473774810, 2000743260178684, 1999657572503822, 1999304108706543,
    2000994791842426, 1999900324092050, 1999275382115592, 2001078220561086, 1999960373446151,
    1999075791277478, 2000980871085442, 2000096021764267, 1999135664378990, 2000941162772423,
    2000061860983705, 1999085288599865, 2001036906162844, 2000246562366767]
private def pvn_m8_r512_6_22_p3 : List ℕ :=
  [1998944836088704, 2000737960105134, 2000220124887505, 1999053486162181, 2000915745897092,
    2000404181145446, 1998857156608514, 2000690388872667, 2000608629327788, 1998939987358180,
    2000552429520629, 2000609336647186, 1998707416298345, 2000321670984899, 2000908893325225,
    1998745461560488, 1999980301598202, 2001120077188224, 1999032474735293, 1999890231970555,
    2001330590832601, 1999058689756414, 1999373006824854, 2001436360709349, 1999467201239739,
    1999058394621241, 2001373177630123, 1999802054776922, 1998700504839817, 2001276140187028,
    2000491348770171, 1998597044179249, 2000765946638619, 2000825164581131, 1998625541049010,
    2000307376330240, 2001155313614873, 1998812922682304, 1999775751788715, 2001374233829448,
    1999214487292408, 1999152144181255, 2001131822426409, 1999708706224676, 1999033367703965,
    2001036260419183, 2000138252534410, 1998855457536961, 2000828555311008, 2000617037409137,
    1998656759615478, 2000267714253612, 2001098471372447, 1998888358411171, 1999694854935097,
    2001434342735357, 1999395248784185, 1999013939765883, 2001275868503937, 2000061117396562,
    1998664705570087, 2000927861816793, 2000800915686921, 1998582296111593]
private def pvn_m8_r512_6_22_p4 : List ℕ :=
  [2000256157244093, 2001396178722662, 1998769477165399, 1999082136968271, 2001461836914252,
    1999763296438355, 1998598327941178, 2001105270800094, 2000787867531805, 1998553013078511,
    2000218774156399, 2001387298422499, 1999035159563556, 1999217784304897, 2001240799901010,
    1999728544111783, 1998672543462440, 2000899785632306, 2000687076813741, 1998607065775268,
    2000028399400390, 2001263303530515, 1999104795794989, 1999081672693708, 2001241510040002,
    2000027208198538, 1998548270056593, 2000656918160033, 2001015829460879, 1998619115249666,
    1999509351034650, 2001609039781356, 1999857827065823, 1998761560030583, 2000985444775743,
    2000808972447532, 1998634295253438, 1999943962837760, 2001498450529509, 1999426440640551,
    1998859468144357, 2001098923472000, 2000427036339564, 1998418988501189, 2000099722744753,
    2001471359689623, 1999254211159999, 1998868916184119, 2001190027817988, 2000574616649985,
    1998693290162745, 2000273922409998, 2001422494628200, 1999142036745964, 1998831608079110,
    2001326785854958, 2000663689435520, 1998252796503458, 1999721883276776, 2001697447145657,
    1999651764968046, 1998381213254772, 2000777706333546, 2001299836123985]
private def pvn_m8_r512_6_22_p5 : List ℕ :=
  [1998941966017409, 1999255024213210, 2001348469371340, 2000311853002041, 1998698001693603,
    2000274022386074, 2001255984034675, 1999336858901233, 1998967937756199, 2000885439760484,
    2000626434314104, 1999013375059559, 1999935871699157, 2001167425291430, 1999799999763869,
    1999075481267537, 2000576980420330, 2000541065907668, 1999020338763599, 1999905292393210,
    2001383396364643, 1999744822451878, 1998451066918395, 2000718218302585, 2001671337062790,
    1998900527973210, 1998432760210421, 2001594176781343, 2001411476568937, 1997808694943611,
    1998553657626877, 2002472858240127, 2001216074959394, 1997174341826255, 1999060156144266,
    2003260280126271, 2000817335437835, 1996520621864535, 1999496725525076, 2003840257622441,
    2000280655057510, 1995781842501488, 1999836437967127, 2004578292487608, 2000215574371549,
    1995285525505117, 1999870412135308, 2004935473230697, 2000114922219204, 1994829000346770,
    1999792965521853, 2005320084441203, 2000220706916899, 1994298120624609, 1999408352663344,
    2005894147225048, 2001080828535856, 1994139699787369, 1998598067219876, 2006041458302606,
    2002034633658200, 1993951919971228, 1997221011913646, 2005901018538016]
private def pvn_m8_r512_6_22_p6 : List ℕ :=
  [2003579351028170, 1994309372151728, 1995348687733650, 2005006007592859, 2005489592862484,
    1995720657087411, 1993600205749479, 2003332496206382, 2007441855080409, 1998232211845097,
    1991925982352127, 1999874117416747, 2008203619343649, 2002180136813933, 1992220118886480,
    1995769523354226, 2006861635448136, 2006366777261827, 1994967431388764, 1991996405812394,
    2002460403135219, 2008624722483269, 2000029069677427, 1990984516828840, 1996561162201137,
    2007592886862190, 2005935191136253, 1994282894413254, 1991718657795818, 2002723542894437,
    2009878936341541, 2001611435588101, 1990581299814754, 1993924718614171, 2006616292281968,
    2009206836327874, 1997603525043680, 1989295960807844, 1996980002530022, 2009545545110119,
    2008548454794993, 1995345404589612, 1989068517508253, 1998865389614182, 2010761478725571,
    2007628824036248, 1993453082857445, 1987818410242834, 1998780856722550, 2011772503371478,
    2009307732971766, 1994410423242061, 1986581726675711, 1996211344843074, 2011116561572166,
    2012184951537444, 1997639710983112, 1985362021495459, 1990848742791470, 2008179736733867,
    2016878889283049, 2006109241208492, 1987590787191464, 1982450891576512]
private def pvn_m8_r512_6_22_p7 : List ℕ :=
  [1997289020870903, 2016441776304003, 2018841906455416, 2000875960239982, 1980677207296751,
    1979495756471182, 1999690451676240, 2021821318976465, 2023571280990198, 2001678818426758,
    1975707410776413, 1970278059851603, 1992407838617468, 2024473808015429, 2038829321845352,
    2021240824238018, 1983388942901791, 1954388927250472, 1958385623779153, 1995735841548319,
    2041776337002337, 2063654748650706, 2042924405090668, 1988423887129706, 1931437393086016,
    1907027081912625, 1933553423428463, 2002257325479106, 2081735935003394, 2133455594586163,
    2129292250384880, 2062567226146889, 1948695004963346, 1817059527690211, 1699185063851255,
    1618582407914535, 1585574401772543, 1597569930082009, 1643111742199903, 1707224905728538,
    1775987823250376, 1839246447863891, 1891388333223011, 1930723246123030, 1958208025258492,
    1976126920721269, 1987078254238724, 1993371371463087, 1996777933966137, 1998516771917188,
    1999353995167764, 1999734148347538, 1999896806123291, 1999962303439596, 1999987077345587,
    1999995857522009, 1999998763815967, 1999999658536316, 1999999913337373, 1999999979989304,
    1999999995853320, 1999999999244133, 1999999999882623, 1999999999985369]
private def pvn_m8_r512_6_22_p8 : List ℕ := [1999999999998740]
private def pvn_m8_r512_6_22 : List ℕ :=
  pCat pvn_m8_r512_6_22_p0
    (pCat pvn_m8_r512_6_22_p1
    (pCat pvn_m8_r512_6_22_p2
    (pCat pvn_m8_r512_6_22_p3
    (pCat pvn_m8_r512_6_22_p4
    (pCat pvn_m8_r512_6_22_p5
    (pCat pvn_m8_r512_6_22_p6
    (pCat pvn_m8_r512_6_22_p7
      pvn_m8_r512_6_22_p8)))))))
private def pvn_m8_r512_6_23_p0 : List ℕ :=
  [2000033815219130, 2000158216772394, 2000032417715529, 2000120070463475, 1999867795670871,
    1999937668111222, 2000102195185777, 1999886937738017, 1999916056678235, 1999947762943624,
    2000114005952138, 1999890380680580, 2000219364764009, 1999957639938766, 2000054810285762,
    1999905674130604, 2000102646222423, 1999977669856241, 2000000617743510, 1999952499761468,
    2000003029737856, 1999940367927887, 2000151545833794, 1999970073220130, 1999889458268014,
    2000217004649948, 1999958518417021, 1999873984911742, 2000159588974964, 1999870590226113,
    2000261915604304, 1999824374895504, 2000162582378356, 1999934419341924, 2000068328193944,
    1999957248892554, 1999862686578943, 2000055590335171, 2000057514294505, 1999863792386704,
    2000042799525447, 1999965231022366, 2000194708479483, 1999746781115610, 2000371375123448,
    1999566743256394, 2000329579629288, 1999550114435019, 2000487586313171, 1999624789576600,
    2000192476850748, 1999996351348658, 2000020406381691, 2000029007200539, 1999966714649883,
    1999924042029174, 2000187550572927, 1999867079843419, 2000064594235615, 1999893191644365,
    2000367467244485, 1999627601203577, 2000327452162345, 1999869835114815]
private def pvn_m8_r512_6_23_p1 : List ℕ :=
  [1999814743256464, 2000403869467069, 1999716365067483, 2000248192250224, 1999717964007535,
    2000259319409661, 1999879840736213, 1999681667034415, 2000489259212099, 1999464569175152,
    2000326592688224, 1999931084921645, 1999748254895667, 2000529236380902, 1999429452366847,
    2000195875160772, 2000091153981697, 1999714381072295, 2000431440187879, 1999608364652901,
    2000234730088490, 1999794924451799, 1999707229364421, 2000626274509700, 1999599365870210,
    2000157139366808, 2000214053404238, 1999508287297770, 2000596298298509, 1999820448550536,
    1999817594991985, 2000529253125067, 1999539306448180, 2000260454414789, 1999949085384365,
    1999654993837910, 2000575560243749, 1999439213166900, 2000184942092681, 2000530509339412,
    1999039979597072, 2000483108818936, 2000297099521873, 1999184767052833, 2000589123295004,
    1999877595092268, 1999617798764791, 2000606119974639, 1999395613806310, 2000005905126146,
    2000603227036995, 1999334865808491, 2000387424759964, 2000324534325566, 1999393754445683,
    2000591988898093, 1999996558262409, 1999660239012173, 2000714496346200, 1999769148490606,
    1999776799232216, 2000427074090059, 1999670604737040, 2000158618027829]
private def pvn_m8_r512_6_23_p2 : List ℕ :=
  [2000366971934400, 1999638515074961, 2000172605555394, 2000092831375077, 1999646559049967,
    2000177076373984, 1999908709901805, 1999786143631706, 2000311532772857, 1999946946620878,
    1999975503063627, 2000242607110260, 1999824509139827, 2000026600226269, 2000028573309646,
    1999740628831355, 2000195558289774, 1999916463210984, 1999711964003657, 2000308646847109,
    1999909183850170, 1999920957852366, 2000420652251377, 1999718146205174, 1999920138078090,
    2000522258222737, 1999880628991778, 2000104465590495, 2000264178702928, 1999603213914724,
    2000238887863326, 2000239445777086, 1999421465229744, 2000249274642320, 2000111884535186,
    1999171784740571, 2000285334667794, 2000282193848005, 1999240996539532, 2000309721284020,
    2000230979145742, 1999199339855466, 2000403519780350, 2000264793597856, 1999217100498355,
    2000609308695828, 2000288058345384, 1998951067269509, 2000621998851732, 2000461241005760,
    1998731959184675, 2000386925659135, 2000673171716891, 1998997556575803, 2000476840946140,
    2000768711237004, 1998936463327096, 2000243334294425, 2000704332702823, 1998980445616743,
    2000326014271612, 2000948636673746, 1999014605538732, 2000091385967892]
private def pvn_m8_r512_6_23_p3 : List ℕ :=
  [2000991288560082, 1999157729852570, 2000029054817364, 2001008359757363, 1999063542627782,
    1999831021657187, 2001312194760022, 1999367751227484, 1999551825423978, 2001149658514226,
    1999365096778154, 1999354216077749, 2001371517225915, 1999681054107597, 1998981954787739,
    2001237686802071, 2000086224088013, 1998907733910145, 2001111499910218, 2000310317177892,
    1998607021840242, 2000850797896099, 2000740008284655, 1998444015769954, 2000264112214986,
    2001054240701183, 1998706087001449, 1999977557806607, 2001445106722681, 1999022459214455,
    1999354963153115, 2001421965182938, 1999568211676095, 1999065098420608, 2001225996367227,
    1999926708763528, 1998743118153148, 2000985359379610, 2000566269617524, 1998766651368185,
    2000515125825967, 2000920467425868, 1998944720594507, 2000054406185002, 2001024750206430,
    1999081893625735, 1999708271049071, 2001334263974794, 1999406063915166, 1999037161060526,
    2001210179645430, 1999968482031850, 1998610645405003, 2000841629217968, 2000681686822047,
    1998617399933108, 2000312738122447, 2001248387229523, 1998866794280341, 1999525984882455,
    2001408920622185, 1999399219380032, 1998906850093924, 2001393528367672]
private def pvn_m8_r512_6_23_p4 : List ℕ :=
  [2000279792926584, 1998436792958389, 2000720179101833, 2001145146967451, 1998593388262221,
    1999690742271907, 2001509599114181, 1999424630570219, 1999067156968516, 2001347886214962,
    2000193791966052, 1998511636302398, 2000513450414638, 2000856696054597, 1998727185258086,
    1999795592419901, 2001310950899064, 1999358849890527, 1999113187200558, 2001336557491119,
    2000303869885410, 1998602147596337, 2000498599393555, 2000979985645267, 1998717831867131,
    1999534108598687, 2001400592924940, 1999543139552983, 1998695199266047, 2001081374511140,
    2000673987375896, 1998435400617537, 1999932342200956, 2001371483262260, 1999231119230755,
    1998983700041197, 2001151415356472, 2000133487539162, 1998495462416766, 2000501352764807,
    2001294189769310, 1998999910501996, 1999382229356540, 2001452148461387, 1999989762273624,
    1998592364060006, 2000773481131895, 2001231341052115, 1998854305414782, 1999374473714136,
    2001314630274508, 1999788753962658, 1998582726010243, 2000798669073888, 2001064187423517,
    1998571797025178, 1999307303375772, 2001716978902374, 2000209047910100, 1998360222829830,
    2000480391862687, 2001558267695238, 1999132748914287, 1998867427115386]
private def pvn_m8_r512_6_23_p5 : List ℕ :=
  [2001155418081645, 2000538033437119, 1998615119279193, 1999902326603589, 2001189054308256,
    1999462880472404, 1998964955570065, 2000906106318393, 2000697941303670, 1998926328567545,
    1999799545459191, 2001169311644427, 1999846479751754, 1999118933744975, 2000675050030256,
    2000608567778651, 1998982381385301, 1999758025966458, 2001135624170680, 1999724799236990,
    1998933534879345, 2001031439120390, 2001174666905344, 1998510673446421, 1998981358355462,
    2001898621786811, 2000723994404536, 1997792373806695, 1999752106208081, 2002545849893490,
    1999789729753298, 1997251023244172, 2000781616459813, 2003015215326064, 1998819078032522,
    1996946276488302, 2001620558638275, 2002919584691270, 1997722442223631, 1997000786770119,
    2002701834398322, 2002919187681303, 1996859356729106, 1997221827104294, 2003686535408186,
    2002857065270004, 1996037314706285, 1997193992117694, 2004203633219076, 2002709970144961,
    1995572107276069, 1997437451429685, 2004779013758621, 2002630701410806, 1995027155458630,
    1997314927539009, 2005187684406494, 2002864006585243, 1994638621346545, 1996754866518262,
    2005238188172108, 2003419804862155, 1994715359001323, 1996227909310573]
private def pvn_m8_r512_6_23_p6 : List ℕ :=
  [2005339092151304, 2004434699103763, 1994964068182245, 1995020790740906, 2004727754992828,
    2005671897194463, 1995798959916777, 1993604077484140, 2003405377796945, 2006954271786222,
    1997372746021035, 1992243565610396, 2001303141059306, 2008268757485942, 2000378101693618,
    1991740231515828, 1997955962050934, 2007964858144408, 2003818539188439, 1992758546515971,
    1994379913130449, 2005970321742711, 2007297056334579, 1996024011727683, 1991681542671834,
    2001750314314629, 2008855504307389, 2000692236593799, 1991009192420797, 1996201397574277,
    2007618390179946, 2006085175703390, 1993921778742238, 1991216167154088, 2002818371801305,
    2010255098390323, 2001483314947856, 1990274962045917, 1994367414757355, 2007419826780328,
    2008960467409326, 1996348679134084, 1988914313822549, 1998242331181220, 2010457370689490,
    2007225288222404, 1993316263617979, 1989462339267916, 2001613208595488, 2012141749005423,
    2005487768447317, 1990682192186690, 1988579359636427, 2002425498661603, 2013258524707873,
    2006082395824352, 1990395352002669, 1987352063916019, 2001387829298616, 2014225590795121,
    2008764237545058, 1991396926654296, 1984131652357670, 1996834757214712]
private def pvn_m8_r512_6_23_p7 : List ℕ :=
  [2014560776203900, 2015541916337815, 1997682569332271, 1981579271681354, 1986568739634186,
    2007986881035905, 2021922737204828, 2011961498520884, 1987836836165121, 1975418705938081,
    1989026444059345, 2015726670983309, 2028058946810962, 2011953569872317, 1981537686298522,
    1966195080591383, 1982546394264483, 2018025545309418, 2041258609366117, 2029718015712670,
    1990101135690434, 1953912701403951, 1952162464185286, 1990047523606527, 2041679194009059,
    2068544189133007, 2047430429263607, 1987499876905827, 1925116192270499, 1900903740273099,
    1934654739978235, 2013465512470805, 2098795081385546, 2146564805344204, 2128174575082743,
    2041891538806421, 1910875445484914, 1771268803439874, 1657524809589110, 1591547831752187,
    1578832390719329, 1611039564227883, 1672139931602985, 1744886191466971, 1815407277462304,
    1875191655281076, 1920889155639298, 1952890275796328, 1973611860786292, 1986088763773670,
    1993098385589050, 1996779773370770, 1998588595077510, 1999419947380606, 1999777019611723,
    1999920082471267, 1999973407221528, 1999991829434818, 1999997698681986, 1999999411529162,
    1999999865220317, 1999999972895733, 1999999995363821, 1999999999363790]
private def pvn_m8_r512_6_23_p8 : List ℕ := [1999999999939335]
private def pvn_m8_r512_6_23 : List ℕ :=
  pCat pvn_m8_r512_6_23_p0
    (pCat pvn_m8_r512_6_23_p1
    (pCat pvn_m8_r512_6_23_p2
    (pCat pvn_m8_r512_6_23_p3
    (pCat pvn_m8_r512_6_23_p4
    (pCat pvn_m8_r512_6_23_p5
    (pCat pvn_m8_r512_6_23_p6
    (pCat pvn_m8_r512_6_23_p7
      pvn_m8_r512_6_23_p8)))))))
private def pvn_m8_r512_6_24_p0 : List ℕ :=
  [1999953340331299, 2000138588942971, 2000007183932487, 2000114918929662, 2000185472616763,
    1999900226367819, 1999970304665173, 1999946663257845, 2000165570045842, 1999782426824057,
    2000038119562237, 1999893108336653, 2000008547135415, 1999912646078041, 2000087117831986,
    2000072119797436, 2000068966089712, 1999938135970204, 2000066590056539, 2000003829242917,
    1999944249675481, 2000160955599788, 1999941917256075, 1999768734779766, 2000283393634209,
    1999801510788051, 2000142318003608, 1999855360302838, 2000132899951390, 2000044143277249,
    1999968880836972, 2000010568341210, 1999965315478219, 1999997330264367, 2000173700468811,
    1999828260953032, 2000188351508229, 1999853525673287, 2000422524543067, 1999493659804870,
    2000421679480109, 1999596574408011, 2000360935373416, 1999654638747232, 2000159069801846,
    1999962332562731, 1999875570807113, 2000090128345639, 2000130001913852, 1999887191137310,
    2000129605706209, 1999780508642004, 2000184918766516, 1999783604030283, 2000215095962296,
    1999680523629107, 2000216161729351, 2000182183445374, 1999585387586972, 2000453514067371,
    1999691234004457, 2000172215319206, 1999979435282378, 1999905052971911]
private def pvn_m8_r512_6_24_p1 : List ℕ :=
  [2000203529634515, 1999581971049495, 2000606819703743, 1999753476459883, 1999826930553961,
    2000463931488116, 1999493916647281, 2000385998074728, 1999925691771142, 1999773875369416,
    2000549529418444, 1999506366936917, 2000214679407318, 2000001320171728, 1999773084874967,
    2000309410634064, 1999516095701404, 2000268131679680, 2000128898713550, 1999513568126794,
    2000578455399205, 1999694840302378, 1999728593073418, 2000468036758016, 1999524225041014,
    2000383995603591, 2000110261666723, 1999429854796918, 2000428529610544, 1999661218750595,
    2000036744948796, 2000393282215802, 1999355698788013, 2000537686101387, 2000100075044222,
    1999285237541621, 2000855823600452, 1999852378395470, 1999450501459253, 2000901165168563,
    1999652919422024, 1999706561635259, 2000535767402395, 1999427915262213, 2000255313304141,
    2000325058853587, 1999277498410179, 2000539382311553, 2000105366209692, 1999356044699018,
    2000540383898417, 1999830697440427, 1999661604583261, 2000551818792909, 1999627920228793,
    1999819117054222, 2000395811798888, 1999589959153680, 2000024917497997, 2000301323791905,
    1999724174476315, 2000220179525096, 2000108759840716, 1999696243910630]
private def pvn_m8_r512_6_24_p2 : List ℕ :=
  [2000318101678763, 2000149806855931, 1999910916742117, 2000284786007501, 1999879749265100,
    1999908001723899, 2000267059636800, 1999880645348089, 2000090144188216, 2000197044029436,
    1999836898771979, 2000208738650007, 1999986570928086, 1999672202795689, 2000243388451405,
    1999864021071753, 1999709362084385, 2000407602995868, 1999914151046940, 1999863335170431,
    2000431114220508, 1999740698721238, 1999854123014325, 2000413338336006, 1999675298985741,
    1999880922496157, 2000239965941415, 1999518506125861, 2000180485303861, 2000495756218034,
    1999350976046938, 2000069053457551, 2000601270343246, 1999422757772224, 2000191314753028,
    2000756038369141, 1999381846984572, 2000078481136160, 2000702512789608, 1999348403093403,
    2000147857932535, 2000685599220727, 1999040986645759, 1999966772469841, 2000764285584361,
    1998935540727089, 1999871920900409, 2001033673142878, 1999018231065238, 1999571590422465,
    2001030292612002, 1999274973465619, 1999573610700735, 2001004130028501, 1999367116083581,
    1999587632925789, 2001111833227608, 1999427207238039, 1999319575511327, 2000964943640617,
    1999472950349930, 1999228361608317, 2001149530820394, 1999873373550268]
private def pvn_m8_r512_6_24_p3 : List ℕ :=
  [1999182321246467, 2000999655909444, 1999865194741919, 1998957237280682, 2001059520351891,
    2000259521928003, 1998795905997130, 2000821360496341, 2000572253055073, 1998862285869907,
    2000711183295507, 2000778959118226, 1998616871454204, 2000315279324372, 2001242054442693,
    1998948399625622, 1999972884748497, 2001288380064596, 1998999234098078, 1999573343103514,
    2001526689565145, 1999352889162933, 1999020237562562, 2001423417442511, 1999950783246381,
    1998829329926264, 2001167909824143, 2000394086464190, 1998666432142036, 2000789052561868,
    2000878519709240, 1998678034225170, 2000089280739018, 2000953615209700, 1998881437751515,
    1999769638122506, 2001273894729930, 1999287791735896, 1999270429511753, 2001208533059865,
    1999829192162086, 1999090370301941, 2001007346989159, 2000117915028418, 1998808498693890,
    2000791866741469, 2000634310924631, 1998655631105215, 2000344046595434, 2001293159041376,
    1998942565516004, 1999585742007436, 2001408747705530, 1999434355871068, 1999028174725336,
    2001351566440987, 2000143935664024, 1998633700030757, 2000869171636511, 2000772563010337,
    1998485008739451, 2000084967342035, 2001303942620244, 1998873291933949]
private def pvn_m8_r512_6_24_p4 : List ℕ :=
  [1999296268639603, 2001592367471968, 1999790468958909, 1998600719396315, 2001019274563936,
    2000655213659171, 1998567747611095, 2000236134541543, 2001206601087418, 1999006089472912,
    1999515017931767, 2001376348018052, 1999648281476121, 1998807800742781, 2000993980282431,
    2000496486095467, 1998755456901958, 2000485833311875, 2001205311384597, 1998898051705171,
    1999407420564835, 2001341531246623, 1999636121352261, 1998653712215514, 2000931747182118,
    2000622639977514, 1998586065550896, 2000210594429204, 2001484511966352, 1999158984610794,
    1999075638778938, 2001348567486012, 2000141113604017, 1998476743182778, 2000481861464979,
    2001015384902280, 1998828542029096, 1999585034413972, 2001343560949193, 1999534146670926,
    1998663857931225, 2000994252006775, 2000762619306286, 1998556407834827, 1999816994768556,
    2001292686371171, 1999246098785345, 1998807061455483, 2001201245136559, 2000653473845897,
    1998615316822636, 2000122803052683, 2001384956089093, 1999225522750190, 1999028406533717,
    2001490547969590, 2000639404200484, 1998301496841145, 1999943738080155, 2001647298929372,
    1999419670560909, 1998540360869863, 2000921014812884, 2000852101209494]
private def pvn_m8_r512_6_24_p5 : List ℕ :=
  [1998696452741988, 1999656219864940, 2001330333181988, 1999821374716439, 1998971197167314,
    2000799328652409, 2000779690476201, 1998960002343366, 1999719747916632, 2001128908478165,
    1999738596793080, 1998897081358192, 2000550490044667, 2000630625166985, 1999036932850475,
    1999792916826943, 2001089312509295, 1999652163212649, 1998967933766010, 2000961510318021,
    2000912291100405, 1998672334682834, 1999610106476653, 2001823709341383, 1999877269301421,
    1997792529981649, 2000587446550158, 2002343852709317, 1998965740824626, 1997893255346885,
    2001769055285351, 2001954559131921, 1997639106706742, 1998362787893634, 2002943083582993,
    2001298349977189, 1996637269425960, 1999181673111112, 2003730358756252, 2000321857883511,
    1996092675519024, 2000398586614062, 2004226141048815, 1999030379467327, 1995556330147972,
    2001424661276274, 2004409183722405, 1997931575785592, 1995464505687483, 2002491574996465,
    2004530561725436, 1997186415048478, 1995692141998066, 2003326726686351, 2004248277544713,
    1996255102728609, 1995767480834569, 2004103447231290, 2004317149623773, 1995714942169151,
    1995676827418035, 2004516727100763, 2004494530965271, 1995437879411925]
private def pvn_m8_r512_6_24_p6 : List ℕ :=
  [1995392140751624, 2004604381200323, 2004726461499441, 1995209668247327, 1994773392911352,
    2004617551594919, 2005669491372886, 1995692710082621, 1993965573726590, 2004058608646965,
    2006639674133623, 1996506879553696, 1992853491061653, 2002837213970778, 2007705251555269,
    1998029512850236, 1991670438799067, 2000575230037680, 2008429813250451, 2000761932003789,
    1991644794503851, 1997846649994460, 2008144535306183, 2003793895811768, 1992529875960629,
    1994572356107682, 2006320011708692, 2006880337928938, 1995263279251844, 1992031023189328,
    2002978865130309, 2008976118641229, 1999377778310315, 1990570374439633, 1997767273375229,
    2008833733744978, 2004810472249692, 1992071796122395, 1991860118611576, 2004897042003613,
    2010002157088865, 1998808273525154, 1989462235597737, 1997196244451564, 2009721881988636,
    2006905758309620, 1992886264076784, 1989612892237760, 2002395640790791, 2011587690388180,
    2002975049056274, 1989643552147266, 1992061171943934, 2007061668645950, 2012427721089568,
    1999819765218200, 1987185212276691, 1992801601094758, 2008928180294092, 2012730644316023,
    1998521515629255, 1985861011026307, 1992563204293899, 2010079678449187]
private def pvn_m8_r512_6_24_p7 : List ℕ :=
  [2014752397071045, 1999548466429207, 1983873072159649, 1988560675328881, 2008665079867808,
    2019103529688364, 2006032217124342, 1984593190145030, 1980991543717031, 2000739140188468,
    2021349216550664, 2018227982862420, 1993482514737283, 1974389648883538, 1983204393782069,
    2012006444060849, 2030253235397647, 2016977143260265, 1983565283294556, 1963384961920062,
    1978688018170323, 2017734961381211, 2044527013981564, 2031976002824291, 1987654834134942,
    1948713113512765, 1950508843356489, 1996102088628357, 2052122795508983, 2073994829564893,
    2040138674362507, 1969021103839867, 1907273083283810, 1898561267453232, 1955174254622612,
    2050206517909116, 2133138248774699, 2157196591509126, 2101987238206466, 1980436947677434,
    1829479682905589, 1692153561387464, 1600995792775213, 1569391286973289, 1592126522741599,
    1652144922454698, 1728996740279727, 1805416855433907, 1870508182955765, 1919843802995562,
    1953750713209559, 1975101561843367, 1987492989894232, 1994142820673504, 1997447053269757,
    1998967065734322, 1999613482678771, 1999866914699555, 1999958123112426, 1999988070716920,
    1999996964131912, 1999999323242875, 1999999871961913, 1999999980604946]
private def pvn_m8_r512_6_24_p8 : List ℕ := [1999999997961749]
private def pvn_m8_r512_6_24 : List ℕ :=
  pCat pvn_m8_r512_6_24_p0
    (pCat pvn_m8_r512_6_24_p1
    (pCat pvn_m8_r512_6_24_p2
    (pCat pvn_m8_r512_6_24_p3
    (pCat pvn_m8_r512_6_24_p4
    (pCat pvn_m8_r512_6_24_p5
    (pCat pvn_m8_r512_6_24_p6
    (pCat pvn_m8_r512_6_24_p7
      pvn_m8_r512_6_24_p8)))))))
private def pvn_m8_r512_6_25_p0 : List ℕ :=
  [1999893246848351, 2000069835851241, 2000085138605263, 1999917139142640, 2000169899284793,
    2000068985652315, 2000244038566125, 1999808805240564, 2000039391796775, 1999991065597713,
    2000067392337711, 1999926288775701, 1999985104505405, 1999944122819672, 1999989009053123,
    1999891686416221, 1999905258188229, 2000108584217094, 2000053354173972, 1999871821693351,
    2000361432713924, 1999721222561080, 2000097972583988, 2000022069011788, 2000088052157548,
    2000001267265859, 1999902511765436, 2000002626797743, 2000098751001505, 1999832219230412,
    2000192053113950, 1999698895014104, 2000350968447341, 1999673609136764, 2000518366740320,
    1999467951726061, 2000355511276718, 1999820718922239, 2000160998055530, 1999911598449381,
    1999941395052505, 2000166760884387, 2000080886121495, 1999846724964407, 2000276461626073,
    1999772247402679, 2000167932233971, 1999793039039053, 2000222320333006, 1999844816070169,
    1999910987434950, 2000185483049581, 1999549834354073, 2000539998666740, 1999787192060884,
    1999906371250880, 2000269185334266, 1999735210829303, 2000298817470858, 1999591607008548,
    2000198593061330, 2000076377762656, 1999564391769192, 2000630833789191]
private def pvn_m8_r512_6_25_p1 : List ℕ :=
  [1999623636847837, 1999894192265479, 2000476006245482, 1999534112129958, 2000403863598030,
    1999788138641264, 1999802661759036, 2000450546866422, 1999621838408623, 2000239561569141,
    2000047725781708, 1999775640213285, 2000448582711132, 1999540571686900, 2000092932482601,
    2000465397716705, 1999383492184177, 2000421779604953, 2000092400207946, 1999557560754733,
    2000542445843868, 1999626578079289, 1999939009761794, 2000340853001511, 1999385971141982,
    2000381424600259, 2000110196028760, 1999559653302691, 2000574745749203, 1999499791481735,
    1999692671954753, 2000904194027792, 1999391689430302, 1999875944123304, 2000756992108955,
    1999202757457975, 2000030318279121, 2000507993300390, 1999348450110483, 2000339272471007,
    2000116846773121, 1999510585803399, 2000635499617502, 1999772079348459, 1999560665342597,
    2000764103485092, 1999799075827463, 1999768091452787, 2000524846253710, 1999648732877997,
    1999960854764725, 2000356664725976, 1999577993362476, 2000092467082399, 2000291700442544,
    1999671185009917, 2000137561484411, 2000073216830689, 1999704065768468, 2000224113764629,
    1999975165469880, 1999777192612596, 2000255641050438, 1999882080520878]
private def pvn_m8_r512_6_25_p2 : List ℕ :=
  [1999811347759216, 2000129864055574, 1999793398398011, 2000066199991218, 2000222323691927,
    1999759220377765, 2000097753193456, 2000067895535352, 1999803460772742, 2000394092813422,
    2000084080726322, 1999758848990044, 2000415991804779, 1999960059300874, 1999710297893225,
    2000423828254107, 1999922818769589, 1999819813442734, 2000499248740359, 1999855880263351,
    1999839822662378, 2000454711823944, 1999652558793590, 1999757943551068, 2000420191579085,
    1999557543218568, 1999926235929818, 2000713747984233, 1999468231378686, 1999746310314380,
    2000879068021658, 1999613169214242, 1999631259246337, 2000720865399874, 1999451500041681,
    1999575330362421, 2000873097516025, 1999531604970672, 1999551053190375, 2000919195325932,
    1999440948575264, 1999449501996157, 2001225752775272, 1999697159375806, 1999240341260455,
    2001190765155438, 1999927207725206, 1999121855634517, 2001070461561294, 2000146711462890,
    1999075763884874, 2000759357591037, 2000006502586763, 1998952952955543, 2000759980858209,
    2000178170878135, 1998802570730215, 2000598437909159, 2000403626580269, 1998798334599199,
    2000438481861584, 2000587964519142, 1998805520236364, 2000325881028960]
private def pvn_m8_r512_6_25_p3 : List ℕ :=
  [2000918829761627, 1998939904324878, 2000110052160127, 2001009121356616, 1998784397764150,
    1999615086244140, 2001251357931772, 1999251508331869, 1999484009386940, 2001316627635617,
    1999394146615121, 1999094970698241, 2001393291214742, 1999862496908789, 1998734214998349,
    2001090599925052, 2000319414805485, 1998768785211104, 2000987260418239, 2000732259035424,
    1998497364289233, 2000386235503152, 2001231333329829, 1998881520539257, 1999904932665122,
    2001340170332138, 1999194819425811, 1999485740660231, 2001387240795445, 1999595819130686,
    1999021055697439, 2001154278089694, 2000118603716421, 1998921563277140, 2000887020651299,
    2000483909748907, 1998813630006540, 2000576175762617, 2001005558758937, 1998964458525850,
    1999979778200451, 2000990647857709, 1999019189004031, 1999573717369001, 2001280961729184,
    1999372080403575, 1998970667454951, 2001309906226839, 2000145529185601, 1998627171298007,
    2000868965741928, 2000829653269907, 1998633887334174, 2000183857585508, 2001190666745311,
    1998862635005851, 1999536437617325, 2001530718152901, 1999545554465179, 1998904383300002,
    2001322218178666, 2000300600077760, 1998504702600885, 2000719480956398]
private def pvn_m8_r512_6_25_p4 : List ℕ :=
  [2001130194038815, 1998688066762589, 1999814007180194, 2001491801666847, 1999329217830209,
    1998975192265432, 2001143997145519, 2000027292787291, 1998695985385912, 2000754665301909,
    2000783450266616, 1998732495874370, 2000035384560620, 2001251289449768, 1999143131762081,
    1999222742063904, 2001274454773432, 1999921124285803, 1998763713180288, 2000950724757304,
    2000800827573045, 1998564640625717, 1999928727994468, 2001351691367399, 1999233920922695,
    1999187101226705, 2001435167944122, 2000172985274085, 1998572166115772, 2000683057315570,
    2001039599393800, 1998651083599109, 1999498361701538, 2001314035177238, 1999533768394346,
    1998879757793336, 2001114878669190, 2000567975327515, 1998691557383208, 2000318868987907,
    2001266830966956, 1998955284445682, 1999084467794705, 2001338530932668, 2000130982289779,
    1998538472401625, 2000517179676591, 2001036037067215, 1998756193425896, 1999413753564771,
    2001462412851596, 1999835016535910, 1998519663094375, 2000702448923797, 2000879633568548,
    1998515344479313, 1999521034129739, 2001698124969895, 1999853719369934, 1998358025138095,
    2000704841957459, 2001312780315980, 1998989462310505, 1999403765181852]
private def pvn_m8_r512_6_25_p5 : List ℕ :=
  [2001340762516490, 2000081531599880, 1998820725784872, 2000526674132819, 2000847762782955,
    1999011201717237, 1999543136013145, 2001039654961231, 1999773654433799, 1998910458647712,
    2000641012939560, 2000788610213234, 1999096028148415, 1999797852114082, 2001141528161638,
    1999737176931760, 1999050153041386, 2000876607261239, 2000616276363088, 1998570307342996,
    1999754479206595, 2001609797635627, 1999520338385606, 1998198228579331, 2001093786343567,
    2001662494263696, 1998221788568617, 1998645780527060, 2002453353155606, 2001064447467321,
    1997279415366047, 1999629190889193, 2002955067538470, 1999528131788635, 1996853752501349,
    2001312902438508, 2003262005665744, 1998048351604925, 1997010259033999, 2002723211509716,
    2002676252325113, 1996664018315689, 1997871901955673, 2003967604475372, 2001548876077690,
    1995515513497979, 1999095003321350, 2004952140890419, 2000390369998108, 1994919117318544,
    2000339688061722, 2005231500318074, 1998972921861824, 1994644231852315, 2001529351780784,
    2005172981542343, 1997744252436607, 1994864668640094, 2002906391822209, 2005214271017655,
    1996701341989083, 1994858381563005, 2003692486620884, 2005101155481759]
private def pvn_m8_r512_6_25_p6 : List ℕ :=
  [1996003496149521, 1994973491062629, 2004327267243890, 2005081316918843, 1995487296826877,
    1994925478464227, 2004807897253468, 2005323524158264, 1995080493582265, 1994311081627060,
    2004745498662383, 2005843531715368, 1995265450168708, 1993774609685509, 2004586857866488,
    2006766620094126, 1995856653878834, 1992801215122828, 2003670384502484, 2007796514322927,
    1997171679542669, 1991779209795166, 2001775117957283, 2008340552838865, 1999122829728627,
    1991354515434067, 1999617605935770, 2008730540092374, 2001876469975999, 1991569348366787,
    1996651007890232, 2007896281911662, 2004846057637691, 1992890182016792, 1993597594621715,
    2005991660602336, 2008111347024212, 1995917673010628, 1990640837545454, 2001705764231949,
    2010104055617620, 2001081612177063, 1989649632463148, 1995186464389958, 2008554905107477,
    2007401474490010, 1993615236037862, 1990202576331856, 2003110622860132, 2011325517003359,
    2001236608595660, 1988864686281475, 1994095332600607, 2008776682788071, 2009616283316133,
    1995010791562557, 1987720223929267, 1999537599940408, 2012891693754649, 2007432117654865,
    1990882493545249, 1987725317581198, 2002907985018245, 2014350316205450]
private def pvn_m8_r512_6_25_p7 : List ℕ :=
  [2005022100906462, 1987816466367530, 1987454433600915, 2005303663027653, 2016835283778346,
    2005376510985014, 1985548614495533, 1984179377809752, 2004259913155649, 2020125854735380,
    2010505832687891, 1986518102432219, 1978408407345088, 1997605956876626, 2021641862819168,
    2020829542595890, 1994399220133270, 1972591670857327, 1981920224983073, 2013870386269643,
    2033086590001532, 2016231087005769, 1978697106283179, 1959873535592076, 1982182946402007,
    2026502695195225, 2049407608835907, 2025402793599300, 1972971826234962, 1939404766379414,
    1958389959271000, 2018819669411091, 2072191558310891, 2071837202325278, 2011057732555184,
    1929946746889229, 1886934753538257, 1917651420923159, 2010591507286313, 2114272504416239,
    2168081578681745, 2135419787702499, 2020077773220379, 1860014164696638, 1706225007724100,
    1600255289824148, 1560983072663387, 1583838488566317, 1648976378879877, 1732181409295546,
    1813375440473870, 1880535272150583, 1929516202139740, 1961614545743370, 1980703416390956,
    1991057602149042, 1996190109284090, 1998514059542562, 1999472749745129, 1999831306897847,
    1999951953448017, 1999988051337545, 1999997485371747, 1999999577403714]
private def pvn_m8_r512_6_25_p8 : List ℕ := [1999999950847545]
private def pvn_m8_r512_6_25 : List ℕ :=
  pCat pvn_m8_r512_6_25_p0
    (pCat pvn_m8_r512_6_25_p1
    (pCat pvn_m8_r512_6_25_p2
    (pCat pvn_m8_r512_6_25_p3
    (pCat pvn_m8_r512_6_25_p4
    (pCat pvn_m8_r512_6_25_p5
    (pCat pvn_m8_r512_6_25_p6
    (pCat pvn_m8_r512_6_25_p7
      pvn_m8_r512_6_25_p8)))))))
private def pvn_m8_r512_6_26_p0 : List ℕ :=
  [1999897032027013, 1999905552629607, 2000167727875139, 1999914689703745, 2000123363435497,
    1999846312622676, 2000174584096890, 2000157414530834, 2000138562000855, 1999952744999128,
    1999996856632640, 1999999162193696, 2000036028785113, 2000022849417400, 1999970394737091,
    1999864689681108, 2000289451217398, 1999628618935911, 2000064667252223, 1999974555430529,
    1999884185266302, 1999987571830568, 2000092700046623, 2000031418421556, 2000166821827785,
    1999678002557294, 2000359527737155, 1999696534958700, 2000475268862005, 1999532910010901,
    2000426770104065, 1999647022854279, 2000180699396618, 2000018431856043, 1999917003613755,
    1999953827476076, 2000001429524244, 1999982215681980, 2000286442816889, 1999640792576683,
    2000247865543852, 1999915642880118, 2000106521549061, 1999930403688874, 1999892272793654,
    2000311789380881, 1999577300964162, 2000424627426192, 1999929102351156, 1999856408563846,
    2000441824161089, 1999543011002097, 2000254278315509, 1999978145591871, 1999961502087189,
    2000196103966669, 1999446454673619, 2000426134541590, 1999949036153812, 1999559614515284,
    2000656591421029, 1999561122278403, 2000065782788046, 2000348289524079]
private def pvn_m8_r512_6_26_p1 : List ℕ :=
  [1999570733790711, 2000314309024638, 1999774052730335, 1999856106827930, 2000426252647354,
    1999577229214062, 2000149665476021, 2000104291466226, 1999658376272072, 2000582415232867,
    1999679036231320, 1999772820008451, 2000634764534299, 1999418517605091, 2000074597438714,
    2000391333872333, 1999511787610151, 2000436285367516, 1999949635870875, 1999652314959140,
    2000571152292035, 1999603329935101, 1999937642485739, 2000578097333636, 1999383255700317,
    2000247363924364, 2000450846936921, 1999202707147766, 2000544896528016, 2000317794779368,
    1998992534838917, 2000503257769638, 2000237579202946, 1999381851004615, 2000571462895987,
    1999864669816492, 1999553684597717, 2000498582446228, 1999617650637906, 1999932303364748,
    2000628281433271, 1999451915860969, 1999925048332971, 2000527084328284, 1999509215241853,
    1999936363761633, 2000292554216650, 1999662579111383, 2000184707645559, 2000159367562317,
    1999601091294213, 2000205327343443, 2000138262154965, 1999770724857305, 2000267408967350,
    2000033589077816, 1999877432325727, 2000287633594192, 1999864610067935, 1999856693587889,
    2000234649304200, 1999845573775881, 2000009917490822, 2000173948215131]
private def pvn_m8_r512_6_26_p2 : List ℕ :=
  [1999769156027072, 2000126101650413, 2000081852298187, 1999664582416651, 2000212595942933,
    2000076679025382, 1999720659243115, 2000303909008384, 1999891640026946, 1999546669143785,
    2000362511209270, 2000005105980496, 1999661915395509, 2000373854850654, 1999889932667383,
    1999658002854517, 2000456362439480, 1999912713101209, 1999765292499961, 2000613337218622,
    1999874034946332, 1999691592872856, 2000652205799381, 1999766781471186, 1999572437498297,
    2000812853984150, 1999827776263420, 1999427857499158, 2000942170027809, 2000026768007574,
    1999247628703486, 2000672342794696, 1999909650322294, 1999225030663071, 2000812088888406,
    1999973779482257, 1999052913643557, 2000873931547357, 2000237644377199, 1999020376587358,
    2000870796014604, 2000396604573677, 1998722889526818, 2000522865487616, 2000672279115233,
    1998900101756490, 2000292995864412, 2000689010034954, 1998960755675430, 2000160328445159,
    2000798814972885, 1999102313247139, 2000166487923902, 2000992055433867, 1999076053561869,
    1999903464907748, 2001248501291839, 1999366294108961, 1999658210265246, 2001183602173334,
    1999391186774850, 1999312055911593, 2001161914416203, 1999554341631940]
private def pvn_m8_r512_6_26_p3 : List ℕ :=
  [1998975044691742, 2001097744884116, 1999866080133873, 1998738980580900, 2000967268702374,
    2000240592380430, 1998535847145778, 2000645839632175, 2000670444627132, 1998717808358798,
    2000538424975619, 2001063086901261, 1998587819778461, 1999800398762314, 2001235433013669,
    1999005831772274, 1999503588626892, 2001358805798237, 1999335077949163, 1999084171869380,
    2001425993255077, 1999967615650765, 1998680590395538, 2000891002995467, 2000424957334075,
    1998826526476279, 2000706509334510, 2000830347213798, 1998781800451204, 2000161600826602,
    2001129113839622, 1999094772514985, 1999742729230258, 2001217866840243, 1999422969212149,
    1999424897076012, 2001291422742192, 1999808010504793, 1998972891221035, 2001038446118635,
    2000291929546538, 1998845953521347, 2000778035012478, 2000695780503279, 1998621309006210,
    2000310066750930, 2001438985679081, 1999014620095745, 1999505543924989, 2001462592562400,
    1999522656893736, 1998891855895253, 2001188975225481, 2000115466666897, 1998566238468699,
    2000783759386187, 2000818261405517, 1998554428131202, 2000118972112951, 2001438862176418,
    1999044370000813, 1999288191125826, 2001445049202273, 1999723654760538]
private def pvn_m8_r512_6_26_p4 : List ℕ :=
  [1998658965580676, 2001061276658033, 2000660601378936, 1998658575441040, 2000328865310767,
    2001153691812207, 1999001370725584, 1999628117521333, 2001292936520117, 1999533791335467,
    1999093911269210, 2001246642491863, 2000297351307497, 1998654136615062, 2000550689732645,
    2000897843245159, 1998712964639579, 1999758472617815, 2001350347623732, 1999324287955328,
    1999005046354065, 2001310325132233, 2000251391849545, 1998505548823495, 2000523435519324,
    2001050421189801, 1998805562376188, 1999730457568632, 2001489226098646, 1999481016223413,
    1998761579377901, 2001085461485466, 2000505885444836, 1998647859621366, 2000347962863044,
    2001227401968826, 1999079932721314, 1999497628397503, 2001386281792159, 1999749572039444,
    1998597434140190, 2000816820420584, 2000766634890965, 1998549563953146, 1999804449133643,
    2001490346535496, 1999520682998279, 1998957170247108, 2001184430788987, 2000461910744484,
    1998473404597058, 2000202591510582, 2001386934943654, 1999052161263855, 1998955827213283,
    2001318318625366, 2000246759027369, 1998346073799511, 2000368436040679, 2001500016407796,
    1999030225178232, 1998804194690170, 2001067329787766, 2000329521301701]
private def pvn_m8_r512_6_26_p5 : List ℕ :=
  [1998723226530264, 2000219266569119, 2000947556756391, 1999173878034546, 1999456628896692,
    2001104438185031, 2000036566876533, 1999020544485961, 2000647999287306, 2000833251647298,
    1999071060696733, 1999734121944142, 2001134959438626, 1999695803512062, 1998939235534486,
    2000750246334136, 2000523067466225, 1998671342099733, 1999961155630526, 2001511865152363,
    1999358762653521, 1998578222037301, 2001441720487535, 2001250720208350, 1998060396567920,
    1999360927624749, 2002415970203573, 1999882720978533, 1997241355756968, 2000807389904758,
    2002651323082833, 1998290055732679, 1997538531973600, 2002378506025618, 2001849228949734,
    1996960566152429, 1999020624916572, 2003764638008880, 2000264723097167, 1995937952773794,
    2000596999938013, 2004070587989619, 1998441911311427, 1996162638254024, 2002610878202273,
    2003565131622608, 1996568620384183, 1997012274171789, 2004269168181046, 2002428624859617,
    1995181340203940, 1998309392447661, 2005220339871145, 2000879296796517, 1994567538137056,
    2000078862509198, 2005693170283379, 1999173229806103, 1994348643347662, 2001687475848859,
    2005577624467992, 1997420723159773, 1994332323341833, 2003113619289992]
private def pvn_m8_r512_6_26_p6 : List ℕ :=
  [2005487533893099, 1996348901946555, 1994787863381660, 2004253643762764, 2005045323572274,
    1995274206223985, 1995154449111355, 2005200593467761, 2004752625216166, 1994438896169099,
    1995328354545395, 2005929516495675, 2004801712929239, 1993985942763595, 1995213550721705,
    2006153038676817, 2004820918629825, 1993599945334384, 1994785248324505, 2006305953471517,
    2005556999366212, 1993881931172193, 1994078265721147, 2005881586745374, 2006451690000390,
    1994664106450649, 1993220489051888, 2004878185718636, 2007225532415941, 1995623871099090,
    1992057836175290, 2003395072338377, 2008381387980157, 1997630369107500, 1991234042402641,
    2001253871235632, 2009196408663714, 2000167509766846, 1990496827380554, 1998037890529801,
    2009461875938666, 2004095772664878, 1991249571201558, 1993850415269942, 2007603781856729,
    2008321442342175, 1994425881562713, 1989876112361328, 2002557871824937, 2010597643656425,
    2000033243013767, 1988814550593263, 1996270945836043, 2010253979320689, 2007391387995203,
    1992159633202889, 1989631807546175, 2004196063656999, 2012196111871780, 2000275486707571,
    1987171628623443, 1994045503566426, 2010764551632279, 2011403262353105]
private def pvn_m8_r512_6_26_p7 : List ℕ :=
  [1994583896778465, 1985962198883960, 1999074824767251, 2014408246994597, 2008464139361604,
    1989215384609228, 1985015116887263, 2003030148256584, 2017947663007334, 2007739873928319,
    1985580429218490, 1982372070050276, 2003821361899945, 2021527338158523, 2010837104026756,
    1984582863824226, 1977268072620006, 2000017841064254, 2024965317075561, 2019723720378493,
    1988688774754695, 1969252934858420, 1986842347895899, 2023015683018851, 2035312284485740,
    2006411429369028, 1965964809209422, 1959508805773656, 1998193240820926, 2044254136133541,
    2048612354331000, 2001905056854718, 1946604156363605, 1937589478293203, 1989349994097785,
    2059957690179562, 2086413879500480, 2039245189781372, 1949023158956316, 1883807031759236,
    1897582607482806, 1990413859502871, 2108038687045849, 2177265953787477, 2149898274891724,
    2027026447614125, 1853017589674482, 1688587421405170, 1581763612203704, 1551633533004680,
    1588857578988709, 1667438997580871, 1758844573650101, 1841808411502769, 1905677398257233,
    1948781901184342, 1974682027742226, 1988636516429436, 1995391884395634, 1998324923776343,
    1999460730790343, 1999849089748659, 1999964403852998, 1999993318975388]
private def pvn_m8_r512_6_26_p8 : List ℕ := [1999999134905103]
private def pvn_m8_r512_6_26 : List ℕ :=
  pCat pvn_m8_r512_6_26_p0
    (pCat pvn_m8_r512_6_26_p1
    (pCat pvn_m8_r512_6_26_p2
    (pCat pvn_m8_r512_6_26_p3
    (pCat pvn_m8_r512_6_26_p4
    (pCat pvn_m8_r512_6_26_p5
    (pCat pvn_m8_r512_6_26_p6
    (pCat pvn_m8_r512_6_26_p7
      pvn_m8_r512_6_26_p8)))))))
private def phb_m8_r512_7_p0 : List ℕ :=
  [58271889483809, 82282424639175, 100620064164956, 116007143052844, 129499890331096,
    141640865547707, 152752876380090, 163046574188859, 172668501879164, 181725518881914,
    190298417704763, 198450060862668, 206230514838071, 213680434232920, 220833374375958,
    227717420182073, 234356363330260, 240770572093818, 246977646608905, 252992920965679,
    258829853765553, 264500336030453, 270014936900936, 275383101841006, 280613314119609,
    285713227564913, 290689776606914, 295549268188806, 300297459073730, 304939621289971,
    309480597868480, 313924850578791, 318276501025788, 322539366203621, 326716989395189,
    330812667141967, 334829472879114, 338770277727137, 342637768847986, 346434465706015,
    350162734519361, 353824801142335, 357422762582515, 360958597325625, 364434174615947,
    367851262818795, 371211536973873, 374516585633360, 377767917065983, 380966964897621,
    384115093249883, 387213601430333, 390263728221376, 393266655809082, 396223513388310,
    399135380476218, 402003289962547, 404828230921855, 407611151210086, 410352959865390,
    413054529330980, 415716697515940, 418340269708222, 420926020352624]
private def phb_m8_r512_7_p1 : List ℕ :=
  [423474694705248, 425987010374799, 428463658760064, 430905306392024, 433312596188228,
    435686148626384, 438026562843427, 440334417665803, 442610272576172, 444854668621263,
    447068129265239, 449251161192498, 451404255063562, 453527886227365, 455622515392972,
    457688589263548, 459726541135129, 461736791462573, 463719748394867, 465675808281797,
    467605356153848, 469508766177031, 471386402084250, 473238617584648, 475065756752325,
    476868154395655, 478646136408413, 480400020103772, 482130114532188, 483836720784137,
    485520132278546, 487180635037771, 488818507949862, 490434023018837, 492027445603634,
    493599034646353, 495149042890380, 496677717088935, 498185298204550, 499672021599964,
    501138117220879, 502583809770995, 504009318879732, 505414859262996, 506800640877346,
    508166869067900, 509513744710267, 510841464346820, 512150220317575, 513440200885931,
    514711590359527, 515964569206432, 517199314166905, 518415998360914, 519614791391615,
    520795859444982, 521959365385751, 523105468849850, 524234326333472, 525346091278934,
    526440914157469, 527518942549076, 528580321219568, 529625192194919]
private def phb_m8_r512_7_p2 : List ℕ :=
  [530653694833043, 531665965893100, 532662139602437, 533642347721268, 534606719605168,
    535555382265492, 536488460427787, 537406076588286, 538308351068551, 539195402068356,
    540067345716858, 540924296122132, 541766365419141, 542593663816189, 543406299639915,
    544204379378898, 544988007725902, 545757287618837, 546512320280461, 547253205256883,
    547980040454907, 548692922178259, 549391945162734, 550077202610309, 550748786222253,
    551406786231264, 552051291432687, 552682389214818, 553300165588347, 553904705214958,
    554496091435121, 555074406295100, 555639730573201, 556192143805292, 556731724309611,
    557258549210897, 557772694463851, 558274234875961, 558763244129706, 559239794804163,
    559703958396026, 560155805340071, 560595405029068, 561022825833175, 561438135118809,
    561841399267030, 562232683691443, 562612052855628, 562979570290126, 563335298608980,
    563679299525858, 564011633869753, 564332361600293, 564641541822652, 564939232802095,
    565225491978139, 565500375978379, 565763940631948, 566016240982651, 566257331301771,
    566487265100554, 566706095142385, 566913873454665, 567110651340395]
private def phb_m8_r512_7_p3 : List ℕ :=
  [567296479389472, 567471407489712, 567635484837601, 567788759948781, 567931280668285,
    568063094180518, 568184247018999, 568294785075864, 568394753611137, 568484197261780,
    568563160050520, 568631685394463, 568689816113502, 568737594438518, 568775062019382,
    568802259932768, 568819228689769, 568826008243333, 568822637995519, 568809156804573,
    568785602991835, 568752014348470, 568708428142044, 568654881122935, 568591409530578,
    568518049099571, 568434835065612, 568341802171307, 568238984671814, 568126416340360,
    568004130473610, 567872159896904, 567730536969356, 567579293588827, 567418461196767,
    567248070782927, 567068152889953, 566878737617856, 566679854628361, 566471533149140,
    566253801977929, 566026689486531, 565790223624710, 565544431923971, 565289341501234,
    565024979062405, 564751370905834, 564468542925676, 564176520615150, 563875329069696,
    563564992990031, 563245536685112, 562916984074996, 562579358693615, 562232683691443,
    561876981838084, 561512275524758, 561138586766699, 560755937205464, 560364348111154,
    559963840384539, 559554434559108, 559136150803022, 558709008920981]
private def phb_m8_r512_7_p4 : List ℕ :=
  [558273028356012, 557828228191170, 557374627151147, 556912243603810, 556441095561644,
    555961200683117, 555472576273966, 554975239288394, 554469206330185, 553954493653747,
    553431117165060, 552899092422552, 552358434637889, 551809158676688, 551251279059145,
    550684809960579, 550109765211906, 549526158300017, 548934002368084, 548333310215785,
    547724094299438, 547106366732060, 546480139283345, 545845423379550, 545202230103306,
    544550570193341, 543890454044121, 543221891705401, 542544892881695, 541859466931660,
    541165622867387, 540463369353612, 539752714706829, 539033666894324, 538306233533109,
    537570421888769, 536826238874218, 536073691048352, 535312784614622, 534543525419496,
    533765918950832, 532979970336153, 532185684340811, 531383065366064, 530572117447037,
    529752844250586, 528925249073052, 528089334837904, 527245104093277, 526392559009392,
    525531701375867, 524662532598903, 523785053698364, 522899265304720, 522005167655880,
    521102760593893, 520192043561520, 519273015598672, 518345675338723, 517410021004676,
    516466050405196, 515513760930492, 514553149548060, 513584212798272]
private def phb_m8_r512_7_p5 : List ℕ :=
  [512606946789811, 511621347194953, 510627409244681, 509625127723639, 508614496964916,
    507595510844657, 506568162776493, 505532445705791, 504488352103718, 503435873961109,
    502375002782140, 501305729577798, 500228044859143, 499141938630352, 498047400381551,
    496944419081409, 495832983169510, 494713080548479, 493584698575862, 492447824055754,
    491302443230163, 490148541770106, 488986104766427, 487815116720329, 486635561533609,
    485447422498593, 484250682287750, 483045322942991, 481831325864625, 480608671799979,
    479377340831651, 478137312365405, 476888565117678, 475631077102702, 474364825619208,
    473089787236724, 471805937781429, 470513252321559, 469211705152349, 467901269780497,
    466581918908121, 465253624416210, 463916357347531, 462570087888988, 461214785353405,
    459850418160710, 458476953818509, 457094358902011, 455702599033292, 454301638859873,
    452891442032571, 451471971182618, 450043187897996, 448605052698981, 447157525012837,
    445700563147655, 444234124265284, 442758164353321, 441272638196123, 439777499344807,
    438272700086182, 436758191410583, 435233922978553, 433699843086320]
private def phb_m8_r512_7_p6 : List ℕ :=
  [432155898630033, 430602035068688, 429038196385688, 427464325048996, 425880361969789,
    424286246459572, 422681916185673, 421067307125040, 419442353516270, 417806987809793,
    416161140616110, 414504740652012, 412837714684663, 411159987473477, 409471481709640,
    407772117953209, 406061814567633, 404340487651584, 402608050967969, 400864415869970,
    399109491223965, 397343183329173, 395565395833855, 393776029647878, 391974982851473,
    390162150599962, 388337425024251, 386500695126857, 384651846673215, 382790762078024,
    380917320286330, 379031396649064, 377132862792724, 375221586482840, 373297431480886,
    371360257394235, 369409919518752, 367446268673581, 365469151027645, 363478407917356,
    361473875654986, 359455385327116, 357422762582515, 355375827408795, 353314393897090,
    351238269993971, 349147257239764, 347041150492329, 344919737635325, 342782799269874,
    340630108388473, 338461430029880, 336276520913627, 334075129052644, 331856993342421,
    329621843124904, 327369397725258, 325099365959369, 322811445609836, 320505322867931,
    318180671738830, 315837153407093, 313474415559133, 311092091659047]
private def phb_m8_r512_7_p7 : List ℕ :=
  [308689800173853, 306267143743745, 303823708292542, 301359062072983, 298872754640960,
    296364315752131, 293833254173626, 291279056402745, 288701185283598, 286099078511626,
    283472147014675, 280819773197995, 278141309038926, 275436074015273, 272703352849295,
    269942393046893, 267152402208831, 264332545087699, 261481940360615, 258599657083452,
    255684710787361, 252736059172525, 249752597347256, 246733152552383, 243676478301383,
    240581247855222, 237446046937336, 234269365577818, 231049588956287, 227784987089074,
    224473703177520, 221113740398790, 217702946877177, 214238998520145, 210719379336505,
    207141358770389, 203501965479092, 199797956848632, 196025783369029, 192181546769217,
    188260950522100, 184259240949171, 180171136647198, 175990743277354, 171711449827833,
    167325801177884, 162825339993331, 158200408423746, 153439896361424, 148530917538850,
    143458386457950, 138204456321270, 132747757728126, 127062344384855, 121116195012656,
    114869019296958, 108268926619663, 101247141869910, 93709155378198, 85518834633531,
    76467143101249, 66202030964005, 54036749321630, 38197545806382]
private def phb_m8_r512_7 : List ℕ :=
  pCat phb_m8_r512_7_p0
    (pCat phb_m8_r512_7_p1
    (pCat phb_m8_r512_7_p2
    (pCat phb_m8_r512_7_p3
    (pCat phb_m8_r512_7_p4
    (pCat phb_m8_r512_7_p5
    (pCat phb_m8_r512_7_p6
      phb_m8_r512_7_p7))))))
private def pvn_m8_r512_7_0_p0 : List ℕ :=
  [2000102967972987, 2000094447370393, 2000167727875139, 1999914689703745, 2000123363435497,
    1999846312622676, 2000174584096890, 2000157414530834, 2000138562000855, 1999952744999128,
    1999996856632640, 1999999162193696, 2000036028785113, 2000022849417400, 1999970394737091,
    1999864689681108, 2000289451217398, 1999628618935911, 2000064667252223, 1999974555430529,
    1999884185266302, 1999987571830568, 2000092700046623, 2000031418421556, 2000166821827785,
    1999678002557294, 2000359527737155, 1999696534958700, 2000475268862005, 1999532910010901,
    1999573229895935, 1999647022854279, 2000180699396618, 2000018431856043, 1999917003613755,
    1999953827476076, 2000001429524244, 1999982215681980, 2000286442816889, 1999640792576683,
    1999752134456148, 1999915642880118, 2000106521549061, 1999930403688874, 1999892272793654,
    2000311789380881, 1999577300964162, 2000424627426192, 1999929102351156, 1999856408563846,
    1999558175838911, 1999543011002097, 2000254278315509, 1999978145591871, 1999961502087189,
    2000196103966669, 1999446454673619, 2000426134541590, 1999949036153812, 1999559614515284,
    1999343408578971, 1999561122278403, 2000065782788046, 2000348289524079]
private def pvn_m8_r512_7_0_p1 : List ℕ :=
  [1999570733790711, 2000314309024638, 1999774052730335, 1999856106827930, 2000426252647354,
    1999577229214062, 1999850334523979, 2000104291466226, 1999658376272072, 2000582415232867,
    1999679036231320, 1999772820008451, 2000634764534299, 1999418517605091, 2000074597438714,
    2000391333872333, 2000488212389849, 2000436285367516, 1999949635870875, 1999652314959140,
    2000571152292035, 1999603329935101, 1999937642485739, 2000578097333636, 1999383255700317,
    2000247363924364, 1999549153063079, 1999202707147766, 2000544896528016, 2000317794779368,
    1998992534838917, 2000503257769638, 2000237579202946, 1999381851004615, 2000571462895987,
    1999864669816492, 2000446315402283, 2000498582446228, 1999617650637906, 1999932303364748,
    2000628281433271, 1999451915860969, 1999925048332971, 2000527084328284, 1999509215241853,
    1999936363761633, 1999707445783350, 1999662579111383, 2000184707645559, 2000159367562317,
    1999601091294213, 2000205327343443, 2000138262154965, 1999770724857305, 2000267408967350,
    2000033589077816, 2000122567674273, 2000287633594192, 1999864610067935, 1999856693587889,
    2000234649304200, 1999845573775881, 2000009917490822, 2000173948215131]
private def pvn_m8_r512_7_0_p2 : List ℕ :=
  [1999769156027072, 2000126101650413, 1999918147701813, 1999664582416651, 2000212595942933,
    2000076679025382, 1999720659243115, 2000303909008384, 1999891640026946, 1999546669143785,
    2000362511209270, 2000005105980496, 2000338084604491, 2000373854850654, 1999889932667383,
    1999658002854517, 2000456362439480, 1999912713101209, 1999765292499961, 2000613337218622,
    1999874034946332, 1999691592872856, 1999347794200619, 1999766781471186, 1999572437498297,
    2000812853984150, 1999827776263420, 1999427857499158, 2000942170027809, 2000026768007574,
    1999247628703486, 2000672342794696, 1999909650322294, 1999225030663071, 2000812088888406,
    1999973779482257, 1999052913643557, 2000873931547357, 2000237644377199, 1999020376587358,
    2000870796014604, 2000396604573677, 2001277110473182, 2000522865487616, 2000672279115233,
    1998900101756490, 2000292995864412, 2000689010034954, 1998960755675430, 2000160328445159,
    2000798814972885, 1999102313247139, 2000166487923902, 2000992055433867, 1999076053561869,
    1999903464907748, 2001248501291839, 1999366294108961, 1999658210265246, 2001183602173334,
    1999391186774850, 1999312055911593, 1998838085583797, 1999554341631940]
private def pvn_m8_r512_7_0_p3 : List ℕ :=
  [1998975044691742, 2001097744884116, 1999866080133873, 1998738980580900, 2000967268702374,
    2000240592380430, 1998535847145778, 2000645839632175, 1999329555372868, 1998717808358798,
    2000538424975619, 2001063086901261, 1998587819778461, 1999800398762314, 2001235433013669,
    1999005831772274, 1999503588626892, 2001358805798237, 2000664922050837, 1999084171869380,
    2001425993255077, 1999967615650765, 1998680590395538, 2000891002995467, 2000424957334075,
    1998826526476279, 2000706509334510, 2000830347213798, 2001218199548796, 2000161600826602,
    2001129113839622, 1999094772514985, 1999742729230258, 2001217866840243, 1999422969212149,
    1999424897076012, 2001291422742192, 1999808010504793, 2001027108778965, 2001038446118635,
    2000291929546538, 1998845953521347, 2000778035012478, 2000695780503279, 1998621309006210,
    2000310066750930, 2001438985679081, 1999014620095745, 2000494456075011, 2001462592562400,
    1999522656893736, 1998891855895253, 2001188975225481, 2000115466666897, 1998566238468699,
    2000783759386187, 2000818261405517, 1998554428131202, 1999881027887049, 2001438862176418,
    1999044370000813, 1999288191125826, 2001445049202273, 1999723654760538]
private def pvn_m8_r512_7_0_p4 : List ℕ :=
  [1998658965580676, 2001061276658033, 2000660601378936, 1998658575441040, 1999671134689233,
    2001153691812207, 1999001370725584, 1999628117521333, 2001292936520117, 1999533791335467,
    1999093911269210, 2001246642491863, 2000297351307497, 1998654136615062, 1999449310267355,
    2000897843245159, 1998712964639579, 1999758472617815, 2001350347623732, 1999324287955328,
    1999005046354065, 2001310325132233, 2000251391849545, 1998505548823495, 1999476564480676,
    2001050421189801, 1998805562376188, 1999730457568632, 2001489226098646, 1999481016223413,
    1998761579377901, 2001085461485466, 2000505885444836, 1998647859621366, 1999652037136956,
    2001227401968826, 1999079932721314, 1999497628397503, 2001386281792159, 1999749572039444,
    1998597434140190, 2000816820420584, 2000766634890965, 1998549563953146, 2000195550866357,
    2001490346535496, 1999520682998279, 1998957170247108, 2001184430788987, 2000461910744484,
    1998473404597058, 2000202591510582, 2001386934943654, 1999052161263855, 2001044172786717,
    2001318318625366, 2000246759027369, 1998346073799511, 2000368436040679, 2001500016407796,
    1999030225178232, 1998804194690170, 2001067329787766, 2000329521301701]
private def pvn_m8_r512_7_0_p5 : List ℕ :=
  [1998723226530264, 2000219266569119, 2000947556756391, 1999173878034546, 1999456628896692,
    2001104438185031, 2000036566876533, 1999020544485961, 2000647999287306, 2000833251647298,
    2000928939303267, 1999734121944142, 2001134959438626, 1999695803512062, 1998939235534486,
    2000750246334136, 2000523067466225, 1998671342099733, 1999961155630526, 2001511865152363,
    2000641237346479, 1998578222037301, 2001441720487535, 2001250720208350, 1998060396567920,
    1999360927624749, 2002415970203573, 1999882720978533, 1997241355756968, 2000807389904758,
    1997348676917167, 1998290055732679, 1997538531973600, 2002378506025618, 2001849228949734,
    1996960566152429, 1999020624916572, 2003764638008880, 2000264723097167, 1995937952773794,
    2000596999938013, 2004070587989619, 1998441911311427, 1996162638254024, 2002610878202273,
    2003565131622608, 1996568620384183, 1997012274171789, 2004269168181046, 2002428624859617,
    2004818659796060, 1998309392447661, 2005220339871145, 2000879296796517, 1994567538137056,
    2000078862509198, 2005693170283379, 1999173229806103, 1994348643347662, 2001687475848859,
    1994422375532008, 1997420723159773, 1994332323341833, 2003113619289992]
private def pvn_m8_r512_7_0_p6 : List ℕ :=
  [2005487533893099, 1996348901946555, 1994787863381660, 2004253643762764, 2005045323572274,
    1995274206223985, 2004845550888645, 2005200593467761, 2004752625216166, 1994438896169099,
    1995328354545395, 2005929516495675, 2004801712929239, 1993985942763595, 1995213550721705,
    2006153038676817, 2004820918629825, 1993599945334384, 1994785248324505, 2006305953471517,
    2005556999366212, 1993881931172193, 1994078265721147, 2005881586745374, 2006451690000390,
    1994664106450649, 2006779510948112, 2004878185718636, 2007225532415941, 1995623871099090,
    1992057836175290, 2003395072338377, 2008381387980157, 1997630369107500, 1991234042402641,
    2001253871235632, 2009196408663714, 2000167509766846, 1990496827380554, 1998037890529801,
    2009461875938666, 2004095772664878, 1991249571201558, 1993850415269942, 2007603781856729,
    2008321442342175, 1994425881562713, 1989876112361328, 2002557871824937, 2010597643656425,
    2000033243013767, 1988814550593263, 1996270945836043, 2010253979320689, 2007391387995203,
    1992159633202889, 1989631807546175, 2004196063656999, 2012196111871780, 2000275486707571,
    1987171628623443, 1994045503566426, 2010764551632279, 2011403262353105]
private def pvn_m8_r512_7_0_p7 : List ℕ :=
  [1994583896778465, 1985962198883960, 2000925175232749, 2014408246994597, 2008464139361604,
    1989215384609228, 1985015116887263, 2003030148256584, 2017947663007334, 2007739873928319,
    1985580429218490, 1982372070050276, 1996178638100055, 2021527338158523, 2010837104026756,
    1984582863824226, 1977268072620006, 2000017841064254, 2024965317075561, 2019723720378493,
    1988688774754695, 1969252934858420, 1986842347895899, 2023015683018851, 2035312284485740,
    2006411429369028, 1965964809209422, 1959508805773656, 1998193240820926, 2044254136133541,
    2048612354331000, 2001905056854718, 2053395843636395, 1937589478293203, 1989349994097785,
    2059957690179562, 2086413879500480, 2039245189781372, 1949023158956316, 1883807031759236,
    1897582607482806, 1990413859502871, 2108038687045849, 2177265953787477, 2149898274891724,
    2027026447614125, 1853017589674482, 1688587421405170, 1581763612203704, 1551633533004680,
    1588857578988709, 1667438997580871, 1758844573650101, 1841808411502769, 1905677398257233,
    1948781901184342, 1974682027742226, 1988636516429436, 1995391884395634, 1998324923776343,
    1999460730790343, 1999849089748659, 1999964403852998, 1999993318975388]
private def pvn_m8_r512_7_0_p8 : List ℕ := [1999999134905103]
private def pvn_m8_r512_7_0 : List ℕ :=
  pCat pvn_m8_r512_7_0_p0
    (pCat pvn_m8_r512_7_0_p1
    (pCat pvn_m8_r512_7_0_p2
    (pCat pvn_m8_r512_7_0_p3
    (pCat pvn_m8_r512_7_0_p4
    (pCat pvn_m8_r512_7_0_p5
    (pCat pvn_m8_r512_7_0_p6
    (pCat pvn_m8_r512_7_0_p7
      pvn_m8_r512_7_0_p8)))))))
private def pvn_m8_r512_7_1_p0 : List ℕ :=
  [2000092995128732, 2000075659861496, 2000198411083955, 1999920512783855, 2000144931625283,
    1999844609136683, 2000083201922687, 2000141581615944, 2000194969679892, 2000013722632996,
    1999993313883076, 1999984919253554, 2000020563753528, 2000027484134803, 2000074592218593,
    1999724617092523, 2000335585788828, 1999786986825150, 1999917604980141, 2000020707617068,
    1999919469688099, 1999892129955559, 2000065050351246, 1999926808856315, 2000362087122066,
    1999624661757076, 2000353082827104, 1999628933781394, 2000394128498354, 2000037956269050,
    1999761999725249, 1999405768399568, 1999825237863900, 2000059134351835, 2000001392520916,
    1999916773500790, 2000042476247030, 1999764966165718, 2000304045572028, 2000052431209599,
    1999791888815420, 1999694960834205, 1999938193169905, 2000142659432969, 1999627813122831,
    2000429136372588, 1999676196459844, 2000075671018640, 2000128881371903, 2000086774773995,
    2000025116804181, 1999351829183869, 1999727982252963, 2000106478525801, 1999712572339170,
    2000496734101871, 1999618710680450, 1999878826427627, 2000202489493887, 2000113888018003,
    1999710040878700, 1999419496237748, 1999213279343229, 2000350378819778]
private def pvn_m8_r512_7_1_p1 : List ℕ :=
  [1999773569428204, 2000015004944160, 2000240017615950, 1999520797891037, 2000217361531632,
    2000193681221202, 1999585444016063, 2000256582165004, 1999466525393236, 2000060506934205,
    2000511800716428, 1999332624604255, 2000366287007001, 2000124500655763, 1999735080402891,
    1999893932047499, 2000145295897593, 2000388948672602, 2000855951252611, 1999630464448863,
    2000143104961763, 2000412866034562, 1999325776637045, 2000520562044173, 1999921561955776,
    1999835212541120, 2000453173801814, 1999471232889874, 1998973630102226, 2000787477066276,
    1999883446405479, 1999265188208987, 2000639371860849, 1999632606285988, 2000055055917929,
    2000080261942766, 1999770124410150, 2000480138876005, 2000677575462102, 1999469481831200,
    2000248341800637, 2000483213549654, 1999395123062990, 2000237132808783, 2000103970146594,
    1999899395365433, 2000014566927542, 1999706002446104, 1999457086386545, 2000242651333309,
    1999999268103128, 1999679022231251, 2000249813518030, 1999918422768658, 1999964824040824,
    2000146573411821, 1999930819204380, 2000145897032253, 2000390301201734, 1999844167419594,
    2000008820935760, 2000146941605094, 1999774012620603, 2000177430033352]
private def pvn_m8_r512_7_1_p2 : List ℕ :=
  [2000007454996055, 1999844575249191, 2000240609316993, 1999889702653616, 1999625061547251,
    2000261015942883, 1999904785648155, 1999759743294428, 2000471540126611, 1999719495312737,
    1999856724934434, 1999975401635291, 1999936893322807, 2000131010574833, 2000705207216358,
    1999875033462937, 1999751992577163, 2000497994992339, 1999675721943872, 2000012620790396,
    2000162229872611, 2000477624163971, 1999621813465374, 2000045302678936, 1999133220553818,
    1999362901615939, 2000834080236910, 1999721689398996, 1999401556618414, 2000955301007187,
    1999977618052526, 1999405585285805, 2000807873012221, 1999766519933919, 1999204724995221,
    2000919800639891, 1999914294721195, 1998980417602458, 2001033466998117, 1999720762490282,
    1999990237543142, 1999529968301287, 2000710128945310, 2000193864299044, 2001512340787146,
    2001024649805944, 1999079490144258, 2000383192202904, 2000651392452893, 1998957720040360,
    2000197463871305, 2000738453437833, 1998998521495914, 2000163800203700, 2001061304319416,
    1999069762066206, 1999813740397131, 2001239200689035, 1999249963698186, 2000092136034319,
    2000325797373986, 2000708752045354, 1999118455718888, 1999956853401683]
private def pvn_m8_r512_7_1_p3 : List ℕ :=
  [1998681737817520, 1998516422793842, 2000974339826603, 1999933301033568, 1998594053737385,
    2001155976460345, 1999817275818680, 1999268888911633, 2000446278241522, 1999936119741510,
    1998060423800007, 2000167878372691, 2001192234116453, 1998740232666064, 1999746245361337,
    2000977510824396, 1999600917670037, 1998637386934905, 2001475521207857, 2000210791414212,
    1999434714389147, 2001518066327002, 2000290662234933, 1998736466570879, 2000884077797366,
    2000031239066508, 1999761365857502, 1999231548742991, 2001153642941687, 2000212741394188,
    2000990322296038, 2001571858308243, 1999329305676512, 1999634117015384, 2001341480467075,
    1999150169436067, 2000109328999643, 2000158579249781, 2000163237518878, 2000037939754711,
    2001787729510275, 2000772923202525, 1998875712540429, 2000702333280736, 2001015550763622,
    1998440581614208, 2000347424425225, 2000975507194796, 1999329109161961, 1999868354094880,
    2001857157769796, 1999962383645711, 1998845415345474, 2001104666199058, 2000352239451357,
    1998539875223611, 2000450394796162, 2001170306677866, 1998607923136466, 1999637081415020,
    2001403143294578, 1999271084838817, 1999057622130701, 2001384456734222]
private def pvn_m8_r512_7_1_p4 : List ℕ :=
  [2000027287471495, 1998668361298740, 2000497844969038, 2001215239254352, 1998695667178161,
    1999718774399087, 2000968011469341, 1999064377166121, 1999406008479017, 2001296774700679,
    1999675323136466, 1999075220167759, 2000667002900726, 2001203535739370, 1998570866997567,
    1999737696975568, 2000663035747651, 1998663666502328, 1999413745419866, 2001372544582604,
    1999520109780591, 1998943040491677, 2000730748141058, 2001164149070759, 1998419664597588,
    1999657844658219, 2000768117970112, 1998762117505302, 1999373177365679, 2001496046187136,
    1999809429763322, 1998765912937338, 2000578796418204, 2001096474075771, 1998592402193757,
    1999680410158453, 2001037323549316, 1999139146602567, 1999248560710823, 2001386228702627,
    2000123356931415, 1998465575551314, 2000718709631947, 2000788460636907, 1998736458508850,
    1999661502315879, 2001572077589096, 1999823918030962, 1998834893433722, 2001039857703400,
    2000870837126085, 1998222815267660, 2000645806104786, 2000304509096754, 1999709228080318,
    1999925147672248, 2001942875329422, 2000883996761623, 1998426781575493, 1999956052473989,
    2001583214738487, 1999452103602325, 1998728639363707, 2000815431816083]
private def pvn_m8_r512_7_1_p5 : List ℕ :=
  [2000444651553060, 1998797553472352, 2000061368255700, 2000968277161783, 1999273235334199,
    1999306319226336, 2001090822423697, 1999901654813173, 1999636505090106, 1999461417172506,
    2001346273270600, 2000220680114995, 2000284076072884, 2001411394129334, 1999896213459809,
    1998879361913225, 2000777500126622, 2000529437569365, 1999024638396544, 1998972625168178,
    2001983036807282, 2000297628315625, 1998694342538957, 2001414451312256, 2001697858436684,
    1998201807892255, 1998751065779742, 2003117408082034, 1998649767436351, 2000140357243892,
    1998845962934594, 1999881473554960, 1996986466376563, 1996500796659022, 2001869208274061,
    2002312347263607, 1997087991821643, 1998362302081276, 2003761453588967, 2001015931459804,
    1995867277317001, 1999897825454036, 2004285225524524, 1999051317685024, 1995767835409751,
    2002014095637273, 2004339506872515, 1996055606982710, 1999362857157804, 1998285570877920,
    2006349165205022, 2001084040072694, 2000549007483220, 2006006449794546, 2001812129666686,
    1994672754854800, 1999115850975962, 2006833216681888, 1996569337083798, 2000644257686190,
    1996975153860667, 1999435750258168, 1994791328631347, 1992924567971525]
private def pvn_m8_r512_7_1_p6 : List ℕ :=
  [2002248543696267, 2005790080779493, 1997063576898557, 1993530683350798, 2006519351113420,
    1999915476093135, 1999577566737618, 2000259593493101, 2007536979441902, 2006058769814361,
    1994940958582188, 1994850322985864, 2005609355138196, 2005268335584049, 1994290064866553,
    1994814707152552, 2005925830981597, 2005231337606298, 1993829053636756, 1994400469728263,
    2006056203489255, 2005825205772721, 1994295887961653, 1992901013327778, 2009030524550361,
    1998943187592838, 2001335928458512, 2000788551896844, 2008116771377953, 2008219798265485,
    1995858321789318, 1992027875418551, 2003383982111771, 2008386760270140, 1997538960800504,
    1991201560896689, 2001417344979975, 2009281794518352, 1999966889092960, 1990364248560391,
    1998267270872855, 2009636551778677, 2003814130843952, 1990980210625517, 1994149609237099,
    2007994078666781, 2008055300975406, 1993932840795297, 1990133777762039, 2003275186911266,
    2010534701580617, 1999172210840911, 1988575508475282, 1997124556151772, 2010767678320310,
    2006576600301153, 1991279921345328, 1990235180824004, 2005447600469256, 2012051005513291,
    1998828236123985, 1986703280521272, 1995435470481144, 2011802310531529]
private def pvn_m8_r512_7_1_p7 : List ℕ :=
  [2010642264074147, 1991876220503848, 1987506152461102, 2002181308651943, 2015519070793906,
    2006536783428417, 1987215353817537, 1986112676052791, 2005897942085193, 2018669602662594,
    2003689699386072, 1986785914929425, 1978692928699186, 2004133790684849, 2021181680965117,
    2006671620683689, 1980882842313646, 1979051499079362, 2005550504220193, 2027234420391315,
    2015212703713872, 1982397257853288, 1969156141285202, 1994016017659386, 2029473259796957,
    2032844715608212, 1996584905274838, 1959413705727832, 1964766341807845, 2009453553361591,
    2061455659995479, 1998566715033555, 2072602647518452, 1978997476840508, 1955139299618750,
    2011954945270274, 2076136650648763, 2081163369188447, 2013421425878464, 1921114132754764,
    1876447578872303, 1920353957522337, 2032066883216965, 2143227824447600, 2182164493666301,
    2115827751419248, 1964135595657519, 1783493124804587, 1635037264906649, 1557771289807699,
    1558525707005002, 1618433663567612, 1707605642708090, 1798790012697385, 1874796031329946,
    1929323844734134, 1963791343608348, 1983197368308352, 1992969130712501, 1997367193297624,
    1999128081047100, 1999749303852771, 1999939308138100, 1999988319427114]
private def pvn_m8_r512_7_1_p8 : List ℕ := [1999998450403708]
private def pvn_m8_r512_7_1 : List ℕ :=
  pCat pvn_m8_r512_7_1_p0
    (pCat pvn_m8_r512_7_1_p1
    (pCat pvn_m8_r512_7_1_p2
    (pCat pvn_m8_r512_7_1_p3
    (pCat pvn_m8_r512_7_1_p4
    (pCat pvn_m8_r512_7_1_p5
    (pCat pvn_m8_r512_7_1_p6
    (pCat pvn_m8_r512_7_1_p7
      pvn_m8_r512_7_1_p8)))))))
private def pwalks_m8_r512 : List RkmSegWalk := [
  ⟨uOfHb phb_m8_r512_0, bDec bZ (zPad bZ 1 pvn_m8_r192_0_0),
    bDec bZ (zPad bZ 17 pvn_m8_r512_0_1)⟩,
  ⟨uOfHb phb_m8_r512_1, bDec bZ (zPad bZ 17 pvn_m8_r512_1_0),
    bDec bZ (zPad bZ 33 pvn_m8_r512_1_1)⟩,
  ⟨uOfHb phb_m8_r512_2, bDec bZ (zPad bZ 33 pvn_m8_r512_2_0),
    bDec bZ (zPad bZ 65 pvn_m8_r512_2_1)⟩,
  ⟨uOfHb phb_m8_r512_3, bDec bZ (zPad bZ 65 pvn_m8_r512_3_0),
    bDec bZ (zPad bZ 129 pvn_m8_r512_3_2)⟩,
  ⟨uOfHb phb_m8_r512_4, bDec bZ (zPad bZ 129 pvn_m8_r512_4_0),
    bDec bZ (zPad bZ 257 pvn_m8_r512_4_4)⟩,
  ⟨uOfHb phb_m8_r512_5, bDec bZ (zPad bZ 257 pvn_m8_r512_5_0),
    bDec bZ (zPad bZ 513 pvn_m8_r512_5_10)⟩,
  ⟨uOfHb phb_m8_r512_6, bDec bZ (zPad bZ 513 pvn_m8_r512_6_0),
    bDec bZ (zPad bZ 513 pvn_m8_r512_6_26)⟩,
  ⟨uOfHb phb_m8_r512_7, bDec bZ (zPad bZ 513 pvn_m8_r512_7_0),
    bDec bZ (zPad bZ 513 pvn_m8_r512_7_1)⟩
  ]
private abbrev pdP_0 : Prop := rkmAllTrueF [
    bSlideChk 8 513 phb_m8_r512_6 513 pvn_m8_r512_6_14 513 pvn_m8_r512_6_15,
    bSlideChk 11 193 phb_m8_r192_7 193 pvn_m8_r192_7_1 193 pvn_m8_r192_7_2,
    bSlideChk 2 513 phb_m8_r512_7 513 pvn_m8_r512_7_0 513 pvn_m8_r512_7_1,
    rkmCheckRowFromWalks 8 112 512
      [2, 4, 8, 16, 32, 64, 112, 112]
      [7114907, 6934421, 6988083, 7791002, 8609126, 9977183, 11595698, 86034]
      [4, 7, 14, 29, 59, 119, 205, 2]
      rkmMasksPack_m8_r512 pwalks_m8_r512 rkmRowPack_m8_r512
  ] = true
private theorem pdk_0 : pdP_0 := by
  decide +kernel
private abbrev pdP_1 : Prop := rkmAllTrueF [
    bSlideChk 8 513 phb_m8_r512_6 513 pvn_m8_r512_6_13 513 pvn_m8_r512_6_14,
    bSlideChk 15 193 phb_m8_r192_7 193 pvn_m8_r192_7_0 193 pvn_m8_r192_7_1,
    bSlideChk 13 385 phb_m8_r384_6 377 pvn_m8_r384_6_0 385 pvn_m8_r384_6_1,
    rkmCheckRowFromWalks 8 24 192
      [1, 1, 1, 1, 24, 24, 24, 24]
      [8287726, 22981553, 35822718, 29572, 2581565, 2714, 4825924, 9229178]
      [2, 4, 6, 1, 8, 1, 14, 26]
      rkmMasksPack_m8_r192 pwalks_m8_r192 rkmRowPack_m8_r192,
    bSlideChk 1 9 phb_m8_r384_3 9 pvn_m8_r384_3_0 9 pvn_m8_r384_3_1
  ] = true
private theorem pdk_1 : pdP_1 := by
  decide +kernel
private abbrev pdP_2 : Prop := rkmAllTrueF [
    bSlideChk 10 513 phb_m8_r512_6 513 pvn_m8_r512_6_1 513 pvn_m8_r512_6_2,
    bSlideChk 16 129 phb_m8_r512_3 65 pvn_m8_r512_3_0 129 pvn_m8_r512_3_1,
    bSlideChk 10 385 phb_m8_r384_6 385 pvn_m8_r384_6_1 385 pvn_m8_r384_6_2,
    rkmCheckRowFromWalks 8 48 384
      [1, 1, 1, 1, 48, 48, 48, 48]
      [1952484, 16556247, 30301753, 404968, 1664085, 1216639, 2867248, 7217343]
      [1, 4, 8, 1, 13, 10, 23, 56]
      rkmMasksPack_m8_r384 pwalks_m8_r384 rkmRowPack_m8_r384
  ] = true
private theorem pdk_2 : pdP_2 := by
  decide +kernel
private abbrev pdP_3 : Prop := rkmAllTrueF [
    bSlideChk 9 513 phb_m8_r512_6 513 pvn_m8_r512_6_5 513 pvn_m8_r512_6_6,
    bSlideChk 13 129 phb_m8_r512_3 129 pvn_m8_r512_3_1 129 pvn_m8_r512_3_2,
    bSlideChk 14 193 phb_m8_r192_6 153 pvn_m8_r192_6_0 193 pvn_m8_r192_6_1,
    bSlideChk 7 33 phb_m8_r512_1 17 pvn_m8_r512_1_0 33 pvn_m8_r512_1_1
  ] = true
private theorem pdk_3 : pdP_3 := by
  decide +kernel
private abbrev pdP_4 : Prop := rkmAllTrueF [
    bSlideChk 8 513 phb_m8_r512_6 513 pvn_m8_r512_6_12 513 pvn_m8_r512_6_13,
    bSlideChk 14 385 phb_m8_r384_7 385 pvn_m8_r384_7_1 385 pvn_m8_r384_7_2,
    bSlideChk 10 385 phb_m8_r384_5 217 pvn_m8_r384_5_0 377 pvn_m8_r384_5_1
  ] = true
private theorem pdk_4 : pdP_4 := by
  decide +kernel
private abbrev pdP_5 : Prop := rkmAllTrueF [
    bSlideChk 8 513 phb_m8_r512_6 513 pvn_m8_r512_6_11 513 pvn_m8_r512_6_12,
    bSlideChk 11 385 phb_m8_r384_7 385 pvn_m8_r384_7_3 385 pvn_m8_r384_7_4,
    bSlideChk 14 65 phb_m8_r512_2 33 pvn_m8_r512_2_0 65 pvn_m8_r512_2_1
  ] = true
private theorem pdk_5 : pdP_5 := by
  decide +kernel
private abbrev pdP_6 : Prop := rkmAllTrueF [
    bSlideChk 9 513 phb_m8_r512_6 513 pvn_m8_r512_6_4 513 pvn_m8_r512_6_5,
    bSlideChk 18 385 phb_m8_r384_7 385 pvn_m8_r384_7_0 385 pvn_m8_r384_7_1,
    bSlideChk 13 385 phb_m8_r384_4 9 pvn_m8_r384_4_0 217 pvn_m8_r384_4_1
  ] = true
private theorem pdk_6 : pdP_6 := by
  decide +kernel
private abbrev pdP_7 : Prop := rkmAllTrueF [
    bSlideChk 10 513 phb_m8_r512_6 513 pvn_m8_r512_6_0 513 pvn_m8_r512_6_1,
    bSlideChk 13 385 phb_m8_r384_7 385 pvn_m8_r384_7_2 385 pvn_m8_r384_7_3,
    bSlideChk 8 193 phb_m8_r192_4 9 pvn_m8_r192_4_0 137 pvn_m8_r192_4_1,
    bSlideChk 8 9 phb_m8_r384_2 9 pvn_m8_r384_2_0 9 pvn_m8_r384_2_1,
    bSlideChk 1 9 phb_m8_r384_0 1 pvn_m8_r192_0_0 9 pvn_m8_r384_0_1
  ] = true
private theorem pdk_7 : pdP_7 := by
  decide +kernel
private abbrev pdP_8 : Prop := rkmAllTrueF [
    bSlideChk 8 513 phb_m8_r512_6 513 pvn_m8_r512_6_10 513 pvn_m8_r512_6_11,
    bSlideChk 13 257 phb_m8_r512_4 257 pvn_m8_r512_4_2 257 pvn_m8_r512_4_3,
    bSlideChk 1 193 phb_m8_r192_5 137 pvn_m8_r192_5_0 153 pvn_m8_r192_5_1,
    bSlideChk 1 9 phb_m8_r192_3 9 pvn_m8_r192_3_0 9 pvn_m8_r192_3_1
  ] = true
private theorem pdk_8 : pdP_8 := by
  decide +kernel
private abbrev pdP_9 : Prop := rkmAllTrueF [
    bSlideChk 8 513 phb_m8_r512_6 513 pvn_m8_r512_6_9 513 pvn_m8_r512_6_10,
    bSlideChk 12 257 phb_m8_r512_4 257 pvn_m8_r512_4_3 257 pvn_m8_r512_4_4,
    bSlideChk 4 17 phb_m8_r512_0 1 pvn_m8_r192_0_0 17 pvn_m8_r512_0_1,
    bSlideChk 4 9 phb_m8_r384_1 9 pvn_m8_r384_1_0 9 pvn_m8_r384_1_1
  ] = true
private theorem pdk_9 : pdP_9 := by
  decide +kernel
private abbrev pdP_10 : Prop := rkmAllTrueF [
    bSlideChk 9 513 phb_m8_r512_6 513 pvn_m8_r512_6_3 513 pvn_m8_r512_6_4,
    bSlideChk 15 257 phb_m8_r512_4 257 pvn_m8_r512_4_1 257 pvn_m8_r512_4_2,
    bSlideChk 6 9 phb_m8_r192_2 9 pvn_m8_r192_2_0 9 pvn_m8_r192_2_1,
    bSlideChk 2 9 phb_m8_r192_0 1 pvn_m8_r192_0_0 9 pvn_m8_r192_0_1
  ] = true
private theorem pdk_10 : pdP_10 := by
  decide +kernel
private abbrev pdP_11 : Prop := rkmAllTrueF [
    bSlideChk 8 513 phb_m8_r512_6 513 pvn_m8_r512_6_8 513 pvn_m8_r512_6_9,
    bSlideChk 19 257 phb_m8_r512_4 129 pvn_m8_r512_4_0 257 pvn_m8_r512_4_1,
    bSlideChk 4 9 phb_m8_r192_1 9 pvn_m8_r192_1_0 9 pvn_m8_r192_1_1
  ] = true
private theorem pdk_11 : pdP_11 := by
  decide +kernel
private abbrev pdP_12 : Prop := rkmAllTrueF [
    bSlideChk 11 513 phb_m8_r512_5 513 pvn_m8_r512_5_6 513 pvn_m8_r512_5_7,
    bSlideChk 9 513 phb_m8_r512_5 513 pvn_m8_r512_5_9 513 pvn_m8_r512_5_10
  ] = true
private theorem pdk_12 : pdP_12 := by
  decide +kernel
private abbrev pdP_13 : Prop := rkmAllTrueF [
    bSlideChk 15 513 phb_m8_r512_5 513 pvn_m8_r512_5_1 513 pvn_m8_r512_5_2,
    bSlideChk 12 513 phb_m8_r512_5 513 pvn_m8_r512_5_3 513 pvn_m8_r512_5_4
  ] = true
private theorem pdk_13 : pdP_13 := by
  decide +kernel
private abbrev pdP_14 : Prop := rkmAllTrueF [
    bSlideChk 9 513 phb_m8_r512_6 513 pvn_m8_r512_6_2 513 pvn_m8_r512_6_3,
    bSlideChk 13 513 phb_m8_r512_5 513 pvn_m8_r512_5_2 513 pvn_m8_r512_5_3
  ] = true
private theorem pdk_14 : pdP_14 := by
  decide +kernel
private abbrev pdP_15 : Prop := rkmAllTrueF [
    bSlideChk 8 513 phb_m8_r512_6 513 pvn_m8_r512_6_7 513 pvn_m8_r512_6_8,
    bSlideChk 10 513 phb_m8_r512_5 513 pvn_m8_r512_5_7 513 pvn_m8_r512_5_8
  ] = true
private theorem pdk_15 : pdP_15 := by
  decide +kernel
private abbrev pdP_16 : Prop := rkmAllTrueF [
    bSlideChk 12 513 phb_m8_r512_5 513 pvn_m8_r512_5_4 513 pvn_m8_r512_5_5,
    bSlideChk 11 513 phb_m8_r512_5 513 pvn_m8_r512_5_5 513 pvn_m8_r512_5_6
  ] = true
private theorem pdk_16 : pdP_16 := by
  decide +kernel
private abbrev pdP_17 : Prop := rkmAllTrueF [
    bSlideChk 7 513 phb_m8_r512_6 513 pvn_m8_r512_6_21 513 pvn_m8_r512_6_22,
    bSlideChk 7 513 phb_m8_r512_6 513 pvn_m8_r512_6_17 513 pvn_m8_r512_6_18
  ] = true
private theorem pdk_17 : pdP_17 := by
  decide +kernel
private abbrev pdP_18 : Prop := rkmAllTrueF [
    bSlideChk 7 513 phb_m8_r512_6 513 pvn_m8_r512_6_22 513 pvn_m8_r512_6_23,
    bSlideChk 8 513 phb_m8_r512_6 513 pvn_m8_r512_6_6 513 pvn_m8_r512_6_7
  ] = true
private theorem pdk_18 : pdP_18 := by
  decide +kernel
private abbrev pdP_19 : Prop := rkmAllTrueF [
    bSlideChk 7 513 phb_m8_r512_6 513 pvn_m8_r512_6_23 513 pvn_m8_r512_6_24,
    bSlideChk 7 513 phb_m8_r512_6 513 pvn_m8_r512_6_16 513 pvn_m8_r512_6_17
  ] = true
private theorem pdk_19 : pdP_19 := by
  decide +kernel
private abbrev pdP_20 : Prop := rkmAllTrueF [
    bSlideChk 7 513 phb_m8_r512_6 513 pvn_m8_r512_6_24 513 pvn_m8_r512_6_25,
    bSlideChk 16 513 phb_m8_r512_5 257 pvn_m8_r512_5_0 513 pvn_m8_r512_5_1
  ] = true
private theorem pdk_20 : pdP_20 := by
  decide +kernel
private abbrev pdP_21 : Prop := rkmAllTrueF [
    bSlideChk 7 513 phb_m8_r512_6 513 pvn_m8_r512_6_25 513 pvn_m8_r512_6_26,
    bSlideChk 7 513 phb_m8_r512_6 513 pvn_m8_r512_6_15 513 pvn_m8_r512_6_16
  ] = true
private theorem pdk_21 : pdP_21 := by
  decide +kernel
private abbrev pdP_22 : Prop := rkmAllTrueF [
    bSlideChk 7 513 phb_m8_r512_6 513 pvn_m8_r512_6_20 513 pvn_m8_r512_6_21,
    bSlideChk 7 513 phb_m8_r512_6 513 pvn_m8_r512_6_18 513 pvn_m8_r512_6_19
  ] = true
private theorem pdk_22 : pdP_22 := by
  decide +kernel
private abbrev pdP_23 : Prop := rkmAllTrueF [
    bSlideChk 7 513 phb_m8_r512_6 513 pvn_m8_r512_6_19 513 pvn_m8_r512_6_20,
    bSlideChk 10 513 phb_m8_r512_5 513 pvn_m8_r512_5_8 513 pvn_m8_r512_5_9
  ] = true
private theorem pdk_23 : pdP_23 := by
  decide +kernel
private theorem pdim_m8_r192_l1 :
    Nat.add (highdNatMin (Nat.mul 1 8) 192) 1 = 9 :=
  rfl
private theorem pdim_m8_r192_l24 :
    Nat.add (highdNatMin (Nat.mul 24 8) 192) 1 = 193 :=
  rfl
private theorem pdim_m8_r384_l1 :
    Nat.add (highdNatMin (Nat.mul 1 8) 384) 1 = 9 :=
  rfl
private theorem pdim_m8_r384_l48 :
    Nat.add (highdNatMin (Nat.mul 48 8) 384) 1 = 385 :=
  rfl
private theorem pdim_m8_r512_l2 :
    Nat.add (highdNatMin (Nat.mul 2 8) 512) 1 = 17 :=
  rfl
private theorem pdim_m8_r512_l4 :
    Nat.add (highdNatMin (Nat.mul 4 8) 512) 1 = 33 :=
  rfl
private theorem pdim_m8_r512_l8 :
    Nat.add (highdNatMin (Nat.mul 8 8) 512) 1 = 65 :=
  rfl
private theorem pdim_m8_r512_l16 :
    Nat.add (highdNatMin (Nat.mul 16 8) 512) 1 = 129 :=
  rfl
private theorem pdim_m8_r512_l32 :
    Nat.add (highdNatMin (Nat.mul 32 8) 512) 1 = 257 :=
  rfl
private theorem pdim_m8_r512_l64 :
    Nat.add (highdNatMin (Nat.mul 64 8) 512) 1 = 513 :=
  rfl
private theorem pdim_m8_r512_l112 :
    Nat.add (highdNatMin (Nat.mul 112 8) 512) 1 = 513 :=
  rfl
private theorem pwalk_m8_r192_0 :
    bWalkOk 2 9 phb_m8_r192_0 1 pvn_m8_r192_0_0 9 pvn_m8_r192_0_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl (rkmTl
      pdk_10))))
private theorem pwalk_m8_r192_1 :
    bWalkOk 4 9 phb_m8_r192_1 9 pvn_m8_r192_1_0 9 pvn_m8_r192_1_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl
      pdk_11)))
private theorem pwalk_m8_r192_2 :
    bWalkOk 6 9 phb_m8_r192_2 9 pvn_m8_r192_2_0 9 pvn_m8_r192_2_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl
      pdk_10)))
private theorem pwalk_m8_r192_3 :
    bWalkOk 1 9 phb_m8_r192_3 9 pvn_m8_r192_3_0 9 pvn_m8_r192_3_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl (rkmTl
      pdk_8))))
private theorem pwalk_m8_r192_4 :
    bWalkOk 8 193 phb_m8_r192_4 9 pvn_m8_r192_4_0 137 pvn_m8_r192_4_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl
      pdk_7)))
private theorem pwalk_m8_r192_5 :
    bWalkOk 1 193 phb_m8_r192_5 137 pvn_m8_r192_5_0 153 pvn_m8_r192_5_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl
      pdk_8)))
private theorem pwalk_m8_r192_6 :
    bWalkOk 14 193 phb_m8_r192_6 153 pvn_m8_r192_6_0 193 pvn_m8_r192_6_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl
      pdk_3)))
private theorem pw_m8_r192_7_0 :
    bWalkOk 15 193 phb_m8_r192_7 193 pvn_m8_r192_7_0 193 pvn_m8_r192_7_1 :=
  bWalk1
    (rkmHd
      (rkmTl
      pdk_1))
private theorem pwalk_m8_r192_7 :
    bWalkOk 26 193 phb_m8_r192_7 193 pvn_m8_r192_7_0 193 pvn_m8_r192_7_2 :=
  bChn (rfl : 15 + 11 = 26) pw_m8_r192_7_0
    (rkmHd
      (rkmTl
      pdk_0))
private theorem pwalks_snd_m8_r192 :
    RkmSegWalksSound 8 192 [1, 1, 1, 1, 24, 24, 24, 24]
      [2, 4, 6, 1, 8, 1, 14, 26] pwalks_m8_r192 := by
  dsimp only [RkmSegWalksSound, pwalks_m8_r192]
  exact ⟨bSeg_mk pdim_m8_r192_l1 pwalk_m8_r192_0,
    ⟨bSeg_mk pdim_m8_r192_l1 pwalk_m8_r192_1,
    ⟨bSeg_mk pdim_m8_r192_l1 pwalk_m8_r192_2,
    ⟨bSeg_mk pdim_m8_r192_l1 pwalk_m8_r192_3,
    ⟨bSeg_mk pdim_m8_r192_l24 pwalk_m8_r192_4,
    ⟨bSeg_mk pdim_m8_r192_l24 pwalk_m8_r192_5,
    ⟨bSeg_mk pdim_m8_r192_l24 pwalk_m8_r192_6,
    ⟨bSeg_mk pdim_m8_r192_l24 pwalk_m8_r192_7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Multi-segment trajectory soundness for `(m = 8, r = 192)`. -/
theorem rkmTrajPack_m8_r192 :
    rkmEvalT16Lo12 8 24 192 [1, 1, 1, 1, 24, 24, 24, 24]
      [8287726, 22981553, 35822718, 29572, 2581565, 2714, 4825924, 9229178]
      [2, 4, 6, 1, 8, 1, 14, 26]
      rkmMasksPack_m8_r192 = rkmRowPack_m8_r192 :=
  rkmCheckRowFromWalks_sound pwalks_snd_m8_r192
    (rkmHd
      (rkmTl (rkmTl (rkmTl
      pdk_1))))

private theorem pwalk_m8_r384_0 :
    bWalkOk 1 9 phb_m8_r384_0 1 pvn_m8_r192_0_0 9 pvn_m8_r384_0_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl (rkmTl (rkmTl
      pdk_7)))))
private theorem pwalk_m8_r384_1 :
    bWalkOk 4 9 phb_m8_r384_1 9 pvn_m8_r384_1_0 9 pvn_m8_r384_1_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl (rkmTl
      pdk_9))))
private theorem pwalk_m8_r384_2 :
    bWalkOk 8 9 phb_m8_r384_2 9 pvn_m8_r384_2_0 9 pvn_m8_r384_2_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl (rkmTl
      pdk_7))))
private theorem pwalk_m8_r384_3 :
    bWalkOk 1 9 phb_m8_r384_3 9 pvn_m8_r384_3_0 9 pvn_m8_r384_3_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl (rkmTl (rkmTl
      pdk_1)))))
private theorem pwalk_m8_r384_4 :
    bWalkOk 13 385 phb_m8_r384_4 9 pvn_m8_r384_4_0 217 pvn_m8_r384_4_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl
      pdk_6)))
private theorem pwalk_m8_r384_5 :
    bWalkOk 10 385 phb_m8_r384_5 217 pvn_m8_r384_5_0 377 pvn_m8_r384_5_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl
      pdk_4)))
private theorem pw_m8_r384_6_0 :
    bWalkOk 13 385 phb_m8_r384_6 377 pvn_m8_r384_6_0 385 pvn_m8_r384_6_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl
      pdk_1)))
private theorem pwalk_m8_r384_6 :
    bWalkOk 23 385 phb_m8_r384_6 377 pvn_m8_r384_6_0 385 pvn_m8_r384_6_2 :=
  bChn (rfl : 13 + 10 = 23) pw_m8_r384_6_0
    (rkmHd
      (rkmTl (rkmTl
      pdk_2)))
private theorem pw_m8_r384_7_0 :
    bWalkOk 18 385 phb_m8_r384_7 385 pvn_m8_r384_7_0 385 pvn_m8_r384_7_1 :=
  bWalk1
    (rkmHd
      (rkmTl
      pdk_6))
private theorem pw_m8_r384_7_1 :
    bWalkOk 32 385 phb_m8_r384_7 385 pvn_m8_r384_7_0 385 pvn_m8_r384_7_2 :=
  bChn (rfl : 18 + 14 = 32) pw_m8_r384_7_0
    (rkmHd
      (rkmTl
      pdk_4))
private theorem pw_m8_r384_7_2 :
    bWalkOk 45 385 phb_m8_r384_7 385 pvn_m8_r384_7_0 385 pvn_m8_r384_7_3 :=
  bChn (rfl : 32 + 13 = 45) pw_m8_r384_7_1
    (rkmHd
      (rkmTl
      pdk_7))
private theorem pwalk_m8_r384_7 :
    bWalkOk 56 385 phb_m8_r384_7 385 pvn_m8_r384_7_0 385 pvn_m8_r384_7_4 :=
  bChn (rfl : 45 + 11 = 56) pw_m8_r384_7_2
    (rkmHd
      (rkmTl
      pdk_5))
private theorem pwalks_snd_m8_r384 :
    RkmSegWalksSound 8 384 [1, 1, 1, 1, 48, 48, 48, 48]
      [1, 4, 8, 1, 13, 10, 23, 56] pwalks_m8_r384 := by
  dsimp only [RkmSegWalksSound, pwalks_m8_r384]
  exact ⟨bSeg_mk pdim_m8_r384_l1 pwalk_m8_r384_0,
    ⟨bSeg_mk pdim_m8_r384_l1 pwalk_m8_r384_1,
    ⟨bSeg_mk pdim_m8_r384_l1 pwalk_m8_r384_2,
    ⟨bSeg_mk pdim_m8_r384_l1 pwalk_m8_r384_3,
    ⟨bSeg_mk pdim_m8_r384_l48 pwalk_m8_r384_4,
    ⟨bSeg_mk pdim_m8_r384_l48 pwalk_m8_r384_5,
    ⟨bSeg_mk pdim_m8_r384_l48 pwalk_m8_r384_6,
    ⟨bSeg_mk pdim_m8_r384_l48 pwalk_m8_r384_7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Multi-segment trajectory soundness for `(m = 8, r = 384)`. -/
theorem rkmTrajPack_m8_r384 :
    rkmEvalT16Lo12 8 48 384 [1, 1, 1, 1, 48, 48, 48, 48]
      [1952484, 16556247, 30301753, 404968, 1664085, 1216639, 2867248, 7217343]
      [1, 4, 8, 1, 13, 10, 23, 56]
      rkmMasksPack_m8_r384 = rkmRowPack_m8_r384 :=
  rkmCheckRowFromWalks_sound pwalks_snd_m8_r384
    (rkmHd
      (rkmTl (rkmTl (rkmTl
      pdk_2))))

private theorem pwalk_m8_r512_0 :
    bWalkOk 4 17 phb_m8_r512_0 1 pvn_m8_r192_0_0 17 pvn_m8_r512_0_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl
      pdk_9)))
private theorem pwalk_m8_r512_1 :
    bWalkOk 7 33 phb_m8_r512_1 17 pvn_m8_r512_1_0 33 pvn_m8_r512_1_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl (rkmTl
      pdk_3))))
private theorem pwalk_m8_r512_2 :
    bWalkOk 14 65 phb_m8_r512_2 33 pvn_m8_r512_2_0 65 pvn_m8_r512_2_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl
      pdk_5)))
private theorem pw_m8_r512_3_0 :
    bWalkOk 16 129 phb_m8_r512_3 65 pvn_m8_r512_3_0 129 pvn_m8_r512_3_1 :=
  bWalk1
    (rkmHd
      (rkmTl
      pdk_2))
private theorem pwalk_m8_r512_3 :
    bWalkOk 29 129 phb_m8_r512_3 65 pvn_m8_r512_3_0 129 pvn_m8_r512_3_2 :=
  bChn (rfl : 16 + 13 = 29) pw_m8_r512_3_0
    (rkmHd
      (rkmTl
      pdk_3))
private theorem pw_m8_r512_4_0 :
    bWalkOk 19 257 phb_m8_r512_4 129 pvn_m8_r512_4_0 257 pvn_m8_r512_4_1 :=
  bWalk1
    (rkmHd
      (rkmTl
      pdk_11))
private theorem pw_m8_r512_4_1 :
    bWalkOk 34 257 phb_m8_r512_4 129 pvn_m8_r512_4_0 257 pvn_m8_r512_4_2 :=
  bChn (rfl : 19 + 15 = 34) pw_m8_r512_4_0
    (rkmHd
      (rkmTl
      pdk_10))
private theorem pw_m8_r512_4_2 :
    bWalkOk 47 257 phb_m8_r512_4 129 pvn_m8_r512_4_0 257 pvn_m8_r512_4_3 :=
  bChn (rfl : 34 + 13 = 47) pw_m8_r512_4_1
    (rkmHd
      (rkmTl
      pdk_8))
private theorem pwalk_m8_r512_4 :
    bWalkOk 59 257 phb_m8_r512_4 129 pvn_m8_r512_4_0 257 pvn_m8_r512_4_4 :=
  bChn (rfl : 47 + 12 = 59) pw_m8_r512_4_2
    (rkmHd
      (rkmTl
      pdk_9))
private theorem pw_m8_r512_5_0 :
    bWalkOk 16 513 phb_m8_r512_5 257 pvn_m8_r512_5_0 513 pvn_m8_r512_5_1 :=
  bWalk1
    (rkmHd
      (rkmTl
      pdk_20))
private theorem pw_m8_r512_5_1 :
    bWalkOk 31 513 phb_m8_r512_5 257 pvn_m8_r512_5_0 513 pvn_m8_r512_5_2 :=
  bChn (rfl : 16 + 15 = 31) pw_m8_r512_5_0
    (rkmHd
      pdk_13)
private theorem pw_m8_r512_5_2 :
    bWalkOk 44 513 phb_m8_r512_5 257 pvn_m8_r512_5_0 513 pvn_m8_r512_5_3 :=
  bChn (rfl : 31 + 13 = 44) pw_m8_r512_5_1
    (rkmHd
      (rkmTl
      pdk_14))
private theorem pw_m8_r512_5_3 :
    bWalkOk 56 513 phb_m8_r512_5 257 pvn_m8_r512_5_0 513 pvn_m8_r512_5_4 :=
  bChn (rfl : 44 + 12 = 56) pw_m8_r512_5_2
    (rkmHd
      (rkmTl
      pdk_13))
private theorem pw_m8_r512_5_4 :
    bWalkOk 68 513 phb_m8_r512_5 257 pvn_m8_r512_5_0 513 pvn_m8_r512_5_5 :=
  bChn (rfl : 56 + 12 = 68) pw_m8_r512_5_3
    (rkmHd
      pdk_16)
private theorem pw_m8_r512_5_5 :
    bWalkOk 79 513 phb_m8_r512_5 257 pvn_m8_r512_5_0 513 pvn_m8_r512_5_6 :=
  bChn (rfl : 68 + 11 = 79) pw_m8_r512_5_4
    (rkmHd
      (rkmTl
      pdk_16))
private theorem pw_m8_r512_5_6 :
    bWalkOk 90 513 phb_m8_r512_5 257 pvn_m8_r512_5_0 513 pvn_m8_r512_5_7 :=
  bChn (rfl : 79 + 11 = 90) pw_m8_r512_5_5
    (rkmHd
      pdk_12)
private theorem pw_m8_r512_5_7 :
    bWalkOk 100 513 phb_m8_r512_5 257 pvn_m8_r512_5_0 513 pvn_m8_r512_5_8 :=
  bChn (rfl : 90 + 10 = 100) pw_m8_r512_5_6
    (rkmHd
      (rkmTl
      pdk_15))
private theorem pw_m8_r512_5_8 :
    bWalkOk 110 513 phb_m8_r512_5 257 pvn_m8_r512_5_0 513 pvn_m8_r512_5_9 :=
  bChn (rfl : 100 + 10 = 110) pw_m8_r512_5_7
    (rkmHd
      (rkmTl
      pdk_23))
private theorem pwalk_m8_r512_5 :
    bWalkOk 119 513 phb_m8_r512_5 257 pvn_m8_r512_5_0 513 pvn_m8_r512_5_10 :=
  bChn (rfl : 110 + 9 = 119) pw_m8_r512_5_8
    (rkmHd
      (rkmTl
      pdk_12))
private theorem pw_m8_r512_6_0 :
    bWalkOk 10 513 phb_m8_r512_6 513 pvn_m8_r512_6_0 513 pvn_m8_r512_6_1 :=
  bWalk1
    (rkmHd
      pdk_7)
private theorem pw_m8_r512_6_1 :
    bWalkOk 20 513 phb_m8_r512_6 513 pvn_m8_r512_6_0 513 pvn_m8_r512_6_2 :=
  bChn (rfl : 10 + 10 = 20) pw_m8_r512_6_0
    (rkmHd
      pdk_2)
private theorem pw_m8_r512_6_2 :
    bWalkOk 29 513 phb_m8_r512_6 513 pvn_m8_r512_6_0 513 pvn_m8_r512_6_3 :=
  bChn (rfl : 20 + 9 = 29) pw_m8_r512_6_1
    (rkmHd
      pdk_14)
private theorem pw_m8_r512_6_3 :
    bWalkOk 38 513 phb_m8_r512_6 513 pvn_m8_r512_6_0 513 pvn_m8_r512_6_4 :=
  bChn (rfl : 29 + 9 = 38) pw_m8_r512_6_2
    (rkmHd
      pdk_10)
private theorem pw_m8_r512_6_4 :
    bWalkOk 47 513 phb_m8_r512_6 513 pvn_m8_r512_6_0 513 pvn_m8_r512_6_5 :=
  bChn (rfl : 38 + 9 = 47) pw_m8_r512_6_3
    (rkmHd
      pdk_6)
private theorem pw_m8_r512_6_5 :
    bWalkOk 56 513 phb_m8_r512_6 513 pvn_m8_r512_6_0 513 pvn_m8_r512_6_6 :=
  bChn (rfl : 47 + 9 = 56) pw_m8_r512_6_4
    (rkmHd
      pdk_3)
private theorem pw_m8_r512_6_6 :
    bWalkOk 64 513 phb_m8_r512_6 513 pvn_m8_r512_6_0 513 pvn_m8_r512_6_7 :=
  bChn (rfl : 56 + 8 = 64) pw_m8_r512_6_5
    (rkmHd
      (rkmTl
      pdk_18))
private theorem pw_m8_r512_6_7 :
    bWalkOk 72 513 phb_m8_r512_6 513 pvn_m8_r512_6_0 513 pvn_m8_r512_6_8 :=
  bChn (rfl : 64 + 8 = 72) pw_m8_r512_6_6
    (rkmHd
      pdk_15)
private theorem pw_m8_r512_6_8 :
    bWalkOk 80 513 phb_m8_r512_6 513 pvn_m8_r512_6_0 513 pvn_m8_r512_6_9 :=
  bChn (rfl : 72 + 8 = 80) pw_m8_r512_6_7
    (rkmHd
      pdk_11)
private theorem pw_m8_r512_6_9 :
    bWalkOk 88 513 phb_m8_r512_6 513 pvn_m8_r512_6_0 513 pvn_m8_r512_6_10 :=
  bChn (rfl : 80 + 8 = 88) pw_m8_r512_6_8
    (rkmHd
      pdk_9)
private theorem pw_m8_r512_6_10 :
    bWalkOk 96 513 phb_m8_r512_6 513 pvn_m8_r512_6_0 513 pvn_m8_r512_6_11 :=
  bChn (rfl : 88 + 8 = 96) pw_m8_r512_6_9
    (rkmHd
      pdk_8)
private theorem pw_m8_r512_6_11 :
    bWalkOk 104 513 phb_m8_r512_6 513 pvn_m8_r512_6_0 513 pvn_m8_r512_6_12 :=
  bChn (rfl : 96 + 8 = 104) pw_m8_r512_6_10
    (rkmHd
      pdk_5)
private theorem pw_m8_r512_6_12 :
    bWalkOk 112 513 phb_m8_r512_6 513 pvn_m8_r512_6_0 513 pvn_m8_r512_6_13 :=
  bChn (rfl : 104 + 8 = 112) pw_m8_r512_6_11
    (rkmHd
      pdk_4)
private theorem pw_m8_r512_6_13 :
    bWalkOk 120 513 phb_m8_r512_6 513 pvn_m8_r512_6_0 513 pvn_m8_r512_6_14 :=
  bChn (rfl : 112 + 8 = 120) pw_m8_r512_6_12
    (rkmHd
      pdk_1)
private theorem pw_m8_r512_6_14 :
    bWalkOk 128 513 phb_m8_r512_6 513 pvn_m8_r512_6_0 513 pvn_m8_r512_6_15 :=
  bChn (rfl : 120 + 8 = 128) pw_m8_r512_6_13
    (rkmHd
      pdk_0)
private theorem pw_m8_r512_6_15 :
    bWalkOk 135 513 phb_m8_r512_6 513 pvn_m8_r512_6_0 513 pvn_m8_r512_6_16 :=
  bChn (rfl : 128 + 7 = 135) pw_m8_r512_6_14
    (rkmHd
      (rkmTl
      pdk_21))
private theorem pw_m8_r512_6_16 :
    bWalkOk 142 513 phb_m8_r512_6 513 pvn_m8_r512_6_0 513 pvn_m8_r512_6_17 :=
  bChn (rfl : 135 + 7 = 142) pw_m8_r512_6_15
    (rkmHd
      (rkmTl
      pdk_19))
private theorem pw_m8_r512_6_17 :
    bWalkOk 149 513 phb_m8_r512_6 513 pvn_m8_r512_6_0 513 pvn_m8_r512_6_18 :=
  bChn (rfl : 142 + 7 = 149) pw_m8_r512_6_16
    (rkmHd
      (rkmTl
      pdk_17))
private theorem pw_m8_r512_6_18 :
    bWalkOk 156 513 phb_m8_r512_6 513 pvn_m8_r512_6_0 513 pvn_m8_r512_6_19 :=
  bChn (rfl : 149 + 7 = 156) pw_m8_r512_6_17
    (rkmHd
      (rkmTl
      pdk_22))
private theorem pw_m8_r512_6_19 :
    bWalkOk 163 513 phb_m8_r512_6 513 pvn_m8_r512_6_0 513 pvn_m8_r512_6_20 :=
  bChn (rfl : 156 + 7 = 163) pw_m8_r512_6_18
    (rkmHd
      pdk_23)
private theorem pw_m8_r512_6_20 :
    bWalkOk 170 513 phb_m8_r512_6 513 pvn_m8_r512_6_0 513 pvn_m8_r512_6_21 :=
  bChn (rfl : 163 + 7 = 170) pw_m8_r512_6_19
    (rkmHd
      pdk_22)
private theorem pw_m8_r512_6_21 :
    bWalkOk 177 513 phb_m8_r512_6 513 pvn_m8_r512_6_0 513 pvn_m8_r512_6_22 :=
  bChn (rfl : 170 + 7 = 177) pw_m8_r512_6_20
    (rkmHd
      pdk_17)
private theorem pw_m8_r512_6_22 :
    bWalkOk 184 513 phb_m8_r512_6 513 pvn_m8_r512_6_0 513 pvn_m8_r512_6_23 :=
  bChn (rfl : 177 + 7 = 184) pw_m8_r512_6_21
    (rkmHd
      pdk_18)
private theorem pw_m8_r512_6_23 :
    bWalkOk 191 513 phb_m8_r512_6 513 pvn_m8_r512_6_0 513 pvn_m8_r512_6_24 :=
  bChn (rfl : 184 + 7 = 191) pw_m8_r512_6_22
    (rkmHd
      pdk_19)
private theorem pw_m8_r512_6_24 :
    bWalkOk 198 513 phb_m8_r512_6 513 pvn_m8_r512_6_0 513 pvn_m8_r512_6_25 :=
  bChn (rfl : 191 + 7 = 198) pw_m8_r512_6_23
    (rkmHd
      pdk_20)
private theorem pwalk_m8_r512_6 :
    bWalkOk 205 513 phb_m8_r512_6 513 pvn_m8_r512_6_0 513 pvn_m8_r512_6_26 :=
  bChn (rfl : 198 + 7 = 205) pw_m8_r512_6_24
    (rkmHd
      pdk_21)
private theorem pwalk_m8_r512_7 :
    bWalkOk 2 513 phb_m8_r512_7 513 pvn_m8_r512_7_0 513 pvn_m8_r512_7_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl
      pdk_0)))
private theorem pwalks_snd_m8_r512 :
    RkmSegWalksSound 8 512 [2, 4, 8, 16, 32, 64, 112, 112]
      [4, 7, 14, 29, 59, 119, 205, 2] pwalks_m8_r512 := by
  dsimp only [RkmSegWalksSound, pwalks_m8_r512]
  exact ⟨bSeg_mk pdim_m8_r512_l2 pwalk_m8_r512_0,
    ⟨bSeg_mk pdim_m8_r512_l4 pwalk_m8_r512_1,
    ⟨bSeg_mk pdim_m8_r512_l8 pwalk_m8_r512_2,
    ⟨bSeg_mk pdim_m8_r512_l16 pwalk_m8_r512_3,
    ⟨bSeg_mk pdim_m8_r512_l32 pwalk_m8_r512_4,
    ⟨bSeg_mk pdim_m8_r512_l64 pwalk_m8_r512_5,
    ⟨bSeg_mk pdim_m8_r512_l112 pwalk_m8_r512_6,
    ⟨bSeg_mk pdim_m8_r512_l112 pwalk_m8_r512_7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Multi-segment trajectory soundness for `(m = 8, r = 512)`. -/
theorem rkmTrajPack_m8_r512 :
    rkmEvalT16Lo12 8 112 512 [2, 4, 8, 16, 32, 64, 112, 112]
      [7114907, 6934421, 6988083, 7791002, 8609126, 9977183, 11595698, 86034]
      [4, 7, 14, 29, 59, 119, 205, 2]
      rkmMasksPack_m8_r512 = rkmRowPack_m8_r512 :=
  rkmCheckRowFromWalks_sound pwalks_snd_m8_r512
    (rkmHd
      (rkmTl (rkmTl (rkmTl
      pdk_0))))

/-- Module export witness for `FindAllJohnsonRampKickMuxLowHiT3`. -/
theorem laneWitness_FindAllJohnsonRampKickMuxLowHiT3 : True := trivial

private theorem rkmOrd_T3 :
    rkmTrajPack_m8_r192 =
      rkmTrajPack_m8_r192 :=
  (And.intro
    (Eq.refl QuantumComputation.Specs.DickeSol.rkmTrajPack_m4_r512)
    rfl).right

end

end QuantumComputation.Specs.DickeSol
