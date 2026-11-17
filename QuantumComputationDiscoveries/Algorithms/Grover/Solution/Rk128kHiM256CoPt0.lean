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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kEngine
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM64K128KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM16K128KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kHiM128K128KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM32K512KrPt1
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kHiM256K512KrPt0
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM16K512KrPt1
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kLowM4K512L248KrPt1
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM16K256KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM32K512KrPt0
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kHiM256K512KrPt1
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM16K512KrPt0
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kHiM1024F256KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM64K256KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kLowM4K512L248KrPt2
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM16K512KrPt2
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM32K512KrPt2
/-
# 128-Segment 128k `m = 256` Mode-1 Part 0 (`Rk128kHiM256CoPt0`)

Certifies Part 0 (`439,918` F1272 / `449,871` Horner coord-ops: all `38` `r <= 128`
prefix anchors plus segment `0` of `r = 256` at `lTableMax = 2`).
-/
namespace QuantumComputation.Specs.GroverFindAll.Rk128kHiM256CoPt0
@[expose] public section
open QuantumComputation.Specs.DickeSol
/-- Active `RampKick128k` segments for `m = 256, r = 3` (`1` segments). -/
def hm256cs0SegsR3 : List Rkm128kSeg := [
  ⟨1, 44919386, 1, 28, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 3`. -/
def hm256cs0RowR3 : List ℕ := [805875282, 53487362015, 945703776144]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 3`. -/
def hm256cs0AncR3 : RampKick128kAnchor :=
  ⟨3, hm256cs0SegsR3, hm256cs0RowR3⟩
/-- Active `RampKick128k` segments for `m = 256, r = 4` (`1` segments). -/
def hm256cs0SegsR4 : List Rkm128kSeg := [
  ⟨1, 46063982, 1, 32, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 4`. -/
def hm256cs0RowR4 : List ℕ := [805355, 402591423, 39730236394, 959866366636]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 4`. -/
def hm256cs0AncR4 : RampKick128kAnchor :=
  ⟨4, hm256cs0SegsR4, hm256cs0RowR4⟩
/-- Active `RampKick128k` segments for `m = 256, r = 5` (`2` segments). -/
def hm256cs0SegsR5 : List Rkm128kSeg := [
  ⟨1, 37014165, 1, 32, []⟩,
  ⟨1, 9744260, 1, 16, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 5`. -/
def hm256cs0RowR5 : List ℕ := [1858, 34268, 201192169, 31670189693, 968128581726]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 5`. -/
def hm256cs0AncR5 : RampKick128kAnchor :=
  ⟨5, hm256cs0SegsR5, hm256cs0RowR5⟩
/-- Active `RampKick128k` segments for `m = 256, r = 6` (`8` segments). -/
def hm256cs0SegsR6 : List Rkm128kSeg := [
  ⟨1, 16831441, 1, 24, []⟩,
  ⟨1, 17069434, 1, 24, []⟩,
  ⟨1, 5713791, 1, 16, []⟩,
  ⟨1, 3094959, 1, 12, []⟩,
  ⟨1, 2264590, 1, 12, rkm128kMask56 1 [1]⟩,
  ⟨1, 1379868, 1, 8, rkm128kMask56 3 [6]⟩,
  ⟨1, 718544, 1, 8, rkm128kMask56 4 [12]⟩,
  ⟨1, 160275, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 6`. -/
def hm256cs0RowR6 : List ℕ := [41, 2, 463, 93639070, 26371249319, 973535110905]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 6`. -/
def hm256cs0AncR6 : RampKick128kAnchor :=
  ⟨6, hm256cs0SegsR6, hm256cs0RowR6⟩
/-- Active `RampKick128k` segments for `m = 256, r = 7` (`8` segments). -/
def hm256cs0SegsR7 : List Rkm128kSeg := [
  ⟨1, 20902411, 1, 28, []⟩,
  ⟨1, 20967411, 1, 28, []⟩,
  ⟨1, 1904582, 1, 10, []⟩,
  ⟨1, 1333212, 1, 8, rkm128kMask56 2 [2]⟩,
  ⟨1, 597294, 1, 6, rkm128kMask56 3 [4]⟩,
  ⟨1, 711306, 1, 6, rkm128kMask56 4 [8]⟩,
  ⟨1, 778246, 1, 8, rkm128kMask56 5 [18]⟩,
  ⟨1, 389118, 1, 6, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 7`. -/
def hm256cs0RowR7 : List ℕ := [0, 0, 0, 9548, 36217277, 22621493776, 977342275627]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 7`. -/
def hm256cs0AncR7 : RampKick128kAnchor :=
  ⟨7, hm256cs0SegsR7, hm256cs0RowR7⟩
/-- Active `RampKick128k` segments for `m = 256, r = 8` (`32` segments). -/
def hm256cs0SegsR8 : List Rkm128kSeg := [
  ⟨1, 12442238, 1, 25, []⟩,
  ⟨1, 6147882, 1, 20, []⟩,
  ⟨1, 5164432, 1, 19, []⟩,
  ⟨1, 4338552, 1, 17, []⟩,
  ⟨1, 3643884, 1, 16, []⟩,
  ⟨1, 2833990, 1, 15, []⟩,
  ⟨1, 2379539, 1, 14, []⟩,
  ⟨1, 2161854, 1, 14, []⟩,
  ⟨1, 1678626, 1, 13, []⟩,
  ⟨1, 1299916, 1, 12, []⟩,
  ⟨1, 1184400, 1, 12, []⟩,
  ⟨1, 1074248, 1, 12, []⟩,
  ⟨1, 835822, 1, 11, rkm128kMask56 3 [6]⟩,
  ⟨1, 414853, 1, 9, rkm128kMask56 4 [10]⟩,
  ⟨1, 51338, 1, 6, rkm128kMask56 4 [10]⟩,
  ⟨1, 182017, 1, 8, rkm128kMask56 4 [10]⟩,
  ⟨1, 590055, 1, 10, rkm128kMask56 5 [20]⟩,
  ⟨1, 391479, 1, 9, rkm128kMask56 5 [20]⟩,
  ⟨1, 316995, 1, 9, rkm128kMask56 6 [40]⟩,
  ⟨1, 113082, 1, 7, rkm128kMask56 6 [48]⟩,
  ⟨1, 23326, 1, 6, rkm128kMask56 6 [40]⟩,
  ⟨1, 69847, 1, 7, rkm128kMask56 6 [48]⟩,
  ⟨1, 121670, 1, 7, rkm128kMask56 6 [40]⟩,
  ⟨1, 67194, 1, 7, rkm128kMask56 6 [40]⟩,
  ⟨1, 66714, 1, 7, rkm128kMask56 6 [40]⟩,
  ⟨1, 64518, 1, 7, rkm128kMask56 5 [24]⟩,
  ⟨1, 12216, 1, 5, rkm128kMask56 6 [40]⟩,
  ⟨1, 58621, 1, 7, rkm128kMask56 6 [48]⟩,
  ⟨1, 59238, 1, 7, rkm128kMask56 6 [48]⟩,
  ⟨1, 36819, 1, 6, rkm128kMask56 6 [48]⟩,
  ⟨1, 24311, 1, 6, rkm128kMask56 6 [48]⟩,
  ⟨1, 8114, 1, 5, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 8`. -/
def hm256cs0RowR8 : List ℕ := [0, 0, 0, 2, 0, 8477930, 19827440389, 980164081607]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 8`. -/
def hm256cs0AncR8 : RampKick128kAnchor :=
  ⟨8, hm256cs0SegsR8, hm256cs0RowR8⟩
/-- Active `RampKick128k` segments for `m = 256, r = 9` (`8` segments). -/
def hm256cs0SegsR9 : List Rkm128kSeg := [
  ⟨1, 21465057, 1, 32, []⟩,
  ⟨1, 22402660, 1, 32, []⟩,
  ⟨1, 404592, 1, 6, []⟩,
  ⟨1, 901213, 1, 8, rkm128kMask56 4 [8]⟩,
  ⟨1, 602695, 1, 6, rkm128kMask56 5 [16]⟩,
  ⟨1, 700207, 1, 8, rkm128kMask56 6 [48]⟩,
  ⟨1, 864748, 1, 8, rkm128kMask56 7 [96]⟩,
  ⟨1, 740274, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 9`. -/
def hm256cs0RowR9 : List ℕ := [0, 0, 0, 1, 0, 17058, 35042, 17665992689, 982333951846]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 9`. -/
def hm256cs0AncR9 : RampKick128kAnchor :=
  ⟨9, hm256cs0SegsR9, hm256cs0RowR9⟩
/-- Active `RampKick128k` segments for `m = 256, r = 10` (`8` segments). -/
def hm256cs0SegsR10 : List Rkm128kSeg := [
  ⟨1, 21713584, 1, 36, []⟩,
  ⟨1, 22402788, 1, 36, rkm128kMask56 3 [4]⟩,
  ⟨1, 344612, 1, 6, []⟩,
  ⟨1, 721737, 1, 8, rkm128kMask56 5 [16]⟩,
  ⟨1, 636215, 1, 8, rkm128kMask56 6 [56]⟩,
  ⟨1, 698927, 1, 8, rkm128kMask56 7 [80]⟩,
  ⟨1, 887372, 1, 8, rkm128kMask56 8 [224]⟩,
  ⟨1, 864801, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 10`. -/
def hm256cs0RowR10 : List ℕ := [0, 0, 1, 0, 2, 1, 2272, 5116495, 15943532161, 984051348525]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 10`. -/
def hm256cs0AncR10 : RampKick128kAnchor :=
  ⟨10, hm256cs0SegsR10, hm256cs0RowR10⟩
/-- Active `RampKick128k` segments for `m = 256, r = 11` (`4` segments). -/
def hm256cs0SegsR11 : List Rkm128kSeg := [
  ⟨1, 38693356, 2, 32, rkm128kMask56 1 [1]⟩,
  ⟨1, 173840, 1, 6, rkm128kMask56 1 [1]⟩,
  ⟨1, 9418010, 1, 20, rkm128kMask56 10 [897]⟩,
  ⟨1, 149135, 1, 6, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 11`. -/
def hm256cs0RowR11 : List ℕ :=
  [0, 0, 0, 0, 0, 530, 144, 4351609, 265390, 14528993764, 985466379551]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 11`. -/
def hm256cs0AncR11 : RampKick128kAnchor :=
  ⟨11, hm256cs0SegsR11, hm256cs0RowR11⟩
/-- Active `RampKick128k` segments for `m = 256, r = 12` (`6` segments). -/
def hm256cs0SegsR12 : List Rkm128kSeg := [
  ⟨1, 20386171, 1, 36, []⟩,
  ⟨1, 21888871, 1, 40, []⟩,
  ⟨1, 2085265, 1, 10, []⟩,
  ⟨1, 2369681, 1, 12, rkm128kMask56 9 [464]⟩,
  ⟨1, 1629666, 1, 10, rkm128kMask56 11 [1744]⟩,
  ⟨1, 220064, 1, 6, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 12`. -/
def hm256cs0RowR12 : List ℕ :=
  [0, 0, 0, 0, 4, 128, 173, 158301, 5011080, 1427303, 13356910589, 986636488162]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 12`. -/
def hm256cs0AncR12 : RampKick128kAnchor :=
  ⟨12, hm256cs0SegsR12, hm256cs0RowR12⟩
/-- Active `RampKick128k` segments for `m = 256, r = 13` (`8` segments). -/
def hm256cs0SegsR13 : List Rkm128kSeg := [
  ⟨1, 21225168, 1, 40, []⟩,
  ⟨1, 21597189, 1, 40, []⟩,
  ⟨1, 2026620, 1, 10, rkm128kMask56 7 [96]⟩,
  ⟨1, 1815971, 1, 10, rkm128kMask56 10 [848]⟩,
  ⟨1, 834547, 1, 8, rkm128kMask56 11 [1728]⟩,
  ⟨1, 462559, 1, 6, rkm128kMask56 11 [1056]⟩,
  ⟨1, 481573, 1, 6, rkm128kMask56 12 [2160]⟩,
  ⟨1, 267305, 1, 6, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 13`. -/
def hm256cs0RowR13 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 8, 9963, 4, 2640, 2880954, 12368792756, 987628302595]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 13`. -/
def hm256cs0AncR13 : RampKick128kAnchor :=
  ⟨13, hm256cs0SegsR13, hm256cs0RowR13⟩
/-- Active `RampKick128k` segments for `m = 256, r = 14` (`8` segments). -/
def hm256cs0SegsR14 : List Rkm128kSeg := [
  ⟨1, 21225065, 1, 40, []⟩,
  ⟨1, 21717111, 1, 40, []⟩,
  ⟨1, 1949570, 1, 10, rkm128kMask56 8 [192]⟩,
  ⟨1, 1852722, 1, 10, rkm128kMask56 11 [1952]⟩,
  ⟨1, 793298, 1, 8, rkm128kMask56 12 [2560]⟩,
  ⟨1, 436170, 1, 6, rkm128kMask56 12 [2944]⟩,
  ⟨1, 540780, 1, 6, rkm128kMask56 13 [4384]⟩,
  ⟨1, 316199, 1, 6, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 14`. -/
def hm256cs0RowR14 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 31, 3, 11711, 831, 1238, 4442134, 11523504928, 988472018800]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 14`. -/
def hm256cs0AncR14 : RampKick128kAnchor :=
  ⟨14, hm256cs0SegsR14, hm256cs0RowR14⟩
/-- Active `RampKick128k` segments for `m = 256, r = 15` (`8` segments). -/
def hm256cs0SegsR15 : List Rkm128kSeg := [
  ⟨1, 20618603, 1, 40, []⟩,
  ⟨1, 22434745, 2, 28, []⟩,
  ⟨1, 1883612, 1, 10, rkm128kMask56 9 [384]⟩,
  ⟨1, 1853285, 1, 10, rkm128kMask56 12 [3904]⟩,
  ⟨1, 791561, 1, 8, rkm128kMask56 13 [4864]⟩,
  ⟨1, 431525, 1, 6, rkm128kMask56 13 [4288]⟩,
  ⟨1, 569827, 1, 6, rkm128kMask56 14 [8896]⟩,
  ⟨1, 358907, 1, 6, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 15`. -/
def hm256cs0RowR15 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 53, 19, 14318, 3307, 3448, 6078224, 10792672946, 989201197780]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 15`. -/
def hm256cs0AncR15 : RampKick128kAnchor :=
  ⟨15, hm256cs0SegsR15, hm256cs0RowR15⟩
/-- Active `RampKick128k` segments for `m = 256, r = 16` (`32` segments). -/
def hm256cs0SegsR16 : List Rkm128kSeg := [
  ⟨1, 12569786, 1, 34, []⟩,
  ⟨1, 5874095, 1, 24, []⟩,
  ⟨1, 4538071, 1, 16, []⟩,
  ⟨1, 4478551, 1, 16, []⟩,
  ⟨1, 3208540, 1, 16, []⟩,
  ⟨1, 3160598, 1, 16, []⟩,
  ⟨1, 2259465, 1, 12, []⟩,
  ⟨1, 2230377, 1, 12, []⟩,
  ⟨1, 1593772, 1, 12, []⟩,
  ⟨1, 1574053, 1, 12, []⟩,
  ⟨1, 1113187, 1, 12, []⟩,
  ⟨1, 1109326, 1, 12, []⟩,
  ⟨1, 873938, 1, 8, rkm128kMask56 9 [511]⟩,
  ⟨1, 670078, 1, 8, rkm128kMask56 10 [1023]⟩,
  ⟨1, 612118, 1, 8, rkm128kMask56 11 [1535]⟩,
  ⟨1, 556798, 1, 8, rkm128kMask56 11 [1024]⟩,
  ⟨1, 387598, 1, 8, rkm128kMask56 13 [6656]⟩,
  ⟨1, 446493, 1, 8, rkm128kMask56 12 [3072]⟩,
  ⟨1, 299297, 1, 8, rkm128kMask56 14 [12800]⟩,
  ⟨1, 257395, 1, 8, rkm128kMask56 14 [10496]⟩,
  ⟨1, 217519, 1, 8, rkm128kMask56 14 [14848]⟩,
  ⟨1, 160763, 1, 8, rkm128kMask56 14 [8704]⟩,
  ⟨1, 163148, 1, 8, rkm128kMask56 14 [10752]⟩,
  ⟨1, 138751, 1, 8, rkm128kMask56 15 [19456]⟩,
  ⟨1, 101355, 1, 8, rkm128kMask56 15 [31232]⟩,
  ⟨1, 96330, 1, 8, rkm128kMask56 15 [30463]⟩,
  ⟨1, 84518, 1, 8, rkm128kMask56 15 [27136]⟩,
  ⟨1, 71119, 1, 8, rkm128kMask56 15 [26624]⟩,
  ⟨1, 63630, 1, 8, rkm128kMask56 15 [27136]⟩,
  ⟨1, 51841, 1, 8, rkm128kMask56 15 [26624]⟩,
  ⟨1, 46496, 1, 8, rkm128kMask56 15 [27136]⟩,
  ⟨1, 37519, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 16`. -/
def hm256cs0RowR16 : List ℕ :=
  [0, 0, 0, 0, 0, 1, 1, 8, 20, 6068, 20902, 3466, 143, 35528, 10148666961, 989851259865]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 16`. -/
def hm256cs0AncR16 : RampKick128kAnchor :=
  ⟨16, hm256cs0SegsR16, hm256cs0RowR16⟩
/-- Active `RampKick128k` segments for `m = 256, r = 17` (`8` segments). -/
def hm256cs0SegsR17 : List Rkm128kSeg := [
  ⟨1, 21703388, 2, 34, []⟩,
  ⟨1, 21552900, 2, 34, []⟩,
  ⟨1, 1737454, 1, 12, rkm128kMask56 11 [1664]⟩,
  ⟨1, 1210405, 1, 12, rkm128kMask56 13 [7680]⟩,
  ⟨1, 1544403, 1, 12, rkm128kMask56 15 [27904]⟩,
  ⟨1, 809549, 1, 8, rkm128kMask56 10 [512]⟩,
  ⟨1, 156299, 1, 8, rkm128kMask56 16 [35328]⟩,
  ⟨1, 429975, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 17`. -/
def hm256cs0RowR17 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 1, 0, 618, 721, 209, 473646, 58974, 9438701, 9591676646, 990398349590]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 17`. -/
def hm256cs0AncR17 : RampKick128kAnchor :=
  ⟨17, hm256cs0SegsR17, hm256cs0RowR17⟩
/-- Active `RampKick128k` segments for `m = 256, r = 18` (`8` segments). -/
def hm256cs0SegsR18 : List Rkm128kSeg := [
  ⟨1, 21748829, 2, 34, []⟩,
  ⟨1, 21601024, 2, 34, []⟩,
  ⟨1, 1690378, 1, 12, rkm128kMask56 12 [3328]⟩,
  ⟨1, 1211429, 1, 12, rkm128kMask56 14 [12800]⟩,
  ⟨1, 1539007, 1, 12, rkm128kMask56 16 [51200]⟩,
  ⟨1, 717929, 1, 8, rkm128kMask56 16 [38144]⟩,
  ⟨1, 268974, 1, 8, rkm128kMask56 17 [66560]⟩,
  ⟨1, 460266, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 18`. -/
def hm256cs0RowR18 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 598, 813, 659713, 22061, 11120849, 9092860365, 990895335035]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 18`. -/
def hm256cs0AncR18 : RampKick128kAnchor :=
  ⟨18, hm256cs0SegsR18, hm256cs0RowR18⟩
/-- Active `RampKick128k` segments for `m = 256, r = 19` (`8` segments). -/
def hm256cs0SegsR19 : List Rkm128kSeg := [
  ⟨1, 20621136, 2, 34, []⟩,
  ⟨1, 22520696, 2, 34, []⟩,
  ⟨1, 1941262, 1, 12, rkm128kMask56 13 [6656]⟩,
  ⟨1, 1221529, 1, 12, rkm128kMask56 15 [25600]⟩,
  ⟨1, 1512627, 1, 12, rkm128kMask56 17 [103936]⟩,
  ⟨1, 576761, 1, 8, rkm128kMask56 17 [76416]⟩,
  ⟨1, 445438, 1, 8, rkm128kMask56 18 [135168]⟩,
  ⟨1, 487887, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 19`. -/
def hm256cs0RowR19 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 11, 391, 3648, 872996, 71845, 12731607, 8646872113,
   991339446728]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 19`. -/
def hm256cs0AncR19 : RampKick128kAnchor :=
  ⟨19, hm256cs0SegsR19, hm256cs0RowR19⟩
/-- Active `RampKick128k` segments for `m = 256, r = 20` (`8` segments). -/
def hm256cs0SegsR20 : List Rkm128kSeg := [
  ⟨1, 20623614, 2, 32, []⟩,
  ⟨1, 22604094, 2, 32, []⟩,
  ⟨1, 1899461, 1, 12, rkm128kMask56 14 [15360]⟩,
  ⟨1, 1215708, 1, 10, rkm128kMask56 16 [52224]⟩,
  ⟨1, 1557226, 1, 12, rkm128kMask56 18 [204800]⟩,
  ⟨1, 347964, 1, 6, rkm128kMask56 15 [17664]⟩,
  ⟨1, 653437, 1, 8, rkm128kMask56 19 [285696]⟩,
  ⟨1, 511991, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 20`. -/
def hm256cs0RowR20 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 5, 43, 1492, 861118, 195562, 14197440, 8246430920,
   991738309693]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 20`. -/
def hm256cs0AncR20 : RampKick128kAnchor :=
  ⟨20, hm256cs0SegsR20, hm256cs0RowR20⟩
/-- Active `RampKick128k` segments for `m = 256, r = 21` (`8` segments). -/
def hm256cs0SegsR21 : List Rkm128kSeg := [
  ⟨1, 20630196, 2, 34, []⟩,
  ⟨1, 22677376, 2, 34, []⟩,
  ⟨1, 1867062, 1, 12, rkm128kMask56 15 [18432]⟩,
  ⟨1, 1221114, 1, 12, rkm128kMask56 17 [104448]⟩,
  ⟨1, 1526854, 1, 12, rkm128kMask56 19 [413696]⟩,
  ⟨1, 479136, 1, 8, rkm128kMask56 19 [478720]⟩,
  ⟨1, 558382, 1, 8, rkm128kMask56 20 [1040384]⟩,
  ⟨1, 536792, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 21`. -/
def hm256cs0RowR21 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 103, 222, 322, 6313, 1144306, 118548, 15922688,
   7882536758, 992100269580]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 21`. -/
def hm256cs0AncR21 : RampKick128kAnchor :=
  ⟨21, hm256cs0SegsR21, hm256cs0RowR21⟩
/-- Active `RampKick128k` segments for `m = 256, r = 22` (`8` segments). -/
def hm256cs0SegsR22 : List Rkm128kSeg := [
  ⟨1, 20684017, 2, 34, []⟩,
  ⟨1, 22689293, 2, 34, rkm128kMask56 12 [3190]⟩,
  ⟨1, 1850083, 1, 12, rkm128kMask56 16 [54272]⟩,
  ⟨1, 1201710, 1, 12, rkm128kMask56 18 [204800]⟩,
  ⟨1, 1593138, 1, 12, rkm128kMask56 20 [839680]⟩,
  ⟨1, 883302, 1, 12, rkm128kMask56 20 [977920]⟩,
  ⟨1, 121282, 1, 8, rkm128kMask56 21 [2088960]⟩,
  ⟨1, 554935, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 22`. -/
def hm256cs0RowR22 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 34, 8, 10, 3106, 1916, 1109576, 180000, 17135380,
   7556870790, 992424697372]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 22`. -/
def hm256cs0AncR22 : RampKick128kAnchor :=
  ⟨22, hm256cs0SegsR22, hm256cs0RowR22⟩
/-- Active `RampKick128k` segments for `m = 256, r = 23` (`8` segments). -/
def hm256cs0SegsR23 : List Rkm128kSeg := [
  ⟨1, 20754069, 2, 34, []⟩,
  ⟨1, 22625245, 2, 34, rkm128kMask56 13 [6650]⟩,
  ⟨1, 1885356, 1, 12, rkm128kMask56 17 [114688]⟩,
  ⟨1, 1227086, 1, 12, rkm128kMask56 19 [413696]⟩,
  ⟨1, 1527405, 1, 12, rkm128kMask56 21 [1679360]⟩,
  ⟨1, 463322, 1, 8, rkm128kMask56 21 [1955840]⟩,
  ⟨1, 597309, 1, 8, rkm128kMask56 22 [4169728]⟩,
  ⟨1, 577065, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 23`. -/
def hm256cs0RowR23 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 177, 14661, 1597676, 217355, 18637143,
   7252498872, 992727029762]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 23`. -/
def hm256cs0AncR23 : RampKick128kAnchor :=
  ⟨23, hm256cs0SegsR23, hm256cs0RowR23⟩
/-- Active `RampKick128k` segments for `m = 256, r = 24` (`8` segments). -/
def hm256cs0SegsR24 : List Rkm128kSeg := [
  ⟨1, 22784895, 2, 36, []⟩,
  ⟨1, 22503395, 2, 36, rkm128kMask56 18 [237568]⟩,
  ⟨1, 612690, 1, 8, rkm128kMask56 19 [335872]⟩,
  ⟨1, 1345713, 1, 10, rkm128kMask56 21 [1798144]⟩,
  ⟨1, 921198, 1, 10, rkm128kMask56 22 [2127872]⟩,
  ⟨1, 974485, 1, 10, rkm128kMask56 23 [4472832]⟩,
  ⟨1, 590921, 1, 8, rkm128kMask56 21 [1064960]⟩,
  ⟨2, 8, 1, 6, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 24`. -/
def hm256cs0RowR24 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 97, 752, 90873, 1188, 944597, 19658378,
   6996182575, 992983116445]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 24`. -/
def hm256cs0AncR24 : RampKick128kAnchor :=
  ⟨24, hm256cs0SegsR24, hm256cs0RowR24⟩
/-- Active `RampKick128k` segments for `m = 256, r = 25` (`8` segments). -/
def hm256cs0SegsR25 : List Rkm128kSeg := [
  ⟨1, 22147508, 4, 24, []⟩,
  ⟨1, 23186207, 4, 24, rkm128kMask56 19 [442368]⟩,
  ⟨1, 615050, 1, 8, rkm128kMask56 20 [704512]⟩,
  ⟨1, 1334141, 1, 12, rkm128kMask56 22 [3588096]⟩,
  ⟨1, 880856, 1, 12, rkm128kMask56 23 [4317184]⟩,
  ⟨1, 983924, 1, 12, rkm128kMask56 24 [9011200]⟩,
  ⟨1, 457781, 1, 8, rkm128kMask56 24 [8617984]⟩,
  ⟨1, 204153, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 25`. -/
def hm256cs0RowR25 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 147, 1303, 106967, 145109, 31913, 36660,
   6742369616, 993257307072]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 25`. -/
def hm256cs0AncR25 : RampKick128kAnchor :=
  ⟨25, hm256cs0SegsR25, hm256cs0RowR25⟩
/-- Active `RampKick128k` segments for `m = 256, r = 26` (`8` segments). -/
def hm256cs0SegsR26 : List Rkm128kSeg := [
  ⟨1, 22322907, 4, 24, rkm128kMask56 27 [67108864]⟩,
  ⟨1, 23032308, 4, 24, rkm128kMask56 20 [709888]⟩,
  ⟨1, 644653, 1, 8, rkm128kMask56 21 [1933696]⟩,
  ⟨1, 1319547, 1, 12, rkm128kMask56 23 [6874176]⟩,
  ⟨1, 877909, 1, 12, rkm128kMask56 24 [11876352]⟩,
  ⟨1, 993931, 1, 12, rkm128kMask56 25 [30412800]⟩,
  ⟨1, 438185, 1, 8, rkm128kMask56 25 [33423360]⟩,
  ⟨1, 255307, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 26`. -/
def hm256cs0RowR26 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 0, 11, 0, 6, 35, 203, 6, 122, 659, 715, 300955, 13731, 47933,
   999380, 6488802226, 993509831948]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 26`. -/
def hm256cs0AncR26 : RampKick128kAnchor :=
  ⟨26, hm256cs0SegsR26, hm256cs0RowR26⟩
/-- Active `RampKick128k` segments for `m = 256, r = 27` (`8` segments). -/
def hm256cs0SegsR27 : List Rkm128kSeg := [
  ⟨1, 23056831, 4, 24, rkm128kMask56 28 [134217728]⟩,
  ⟨1, 22349832, 4, 24, rkm128kMask56 21 [1419776]⟩,
  ⟨1, 636978, 1, 8, rkm128kMask56 22 [3473152]⟩,
  ⟨1, 1329371, 1, 12, rkm128kMask56 24 [14416512]⟩,
  ⟨1, 883681, 1, 12, rkm128kMask56 25 [16827904]⟩,
  ⟨1, 978218, 1, 12, rkm128kMask56 26 [64905216]⟩,
  ⟨1, 421792, 1, 8, rkm128kMask56 26 [66584576]⟩,
  ⟨1, 300376, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 27`. -/
def hm256cs0RowR27 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 30, 88, 36, 163, 37, 22, 597, 1264, 185500, 186339,
   190, 3617407, 6293196914, 993702808351]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 27`. -/
def hm256cs0AncR27 : RampKick128kAnchor :=
  ⟨27, hm256cs0SegsR27, hm256cs0RowR27⟩
/-- Active `RampKick128k` segments for `m = 256, r = 28` (`8` segments). -/
def hm256cs0SegsR28 : List Rkm128kSeg := [
  ⟨1, 23819897, 2, 48, rkm128kMask56 29 [268435456]⟩,
  ⟨1, 21636798, 4, 24, rkm128kMask56 22 [2839808]⟩,
  ⟨1, 636343, 1, 8, rkm128kMask56 23 [7339520]⟩,
  ⟨1, 1334240, 1, 12, rkm128kMask56 25 [28572928]⟩,
  ⟨1, 885592, 1, 12, rkm128kMask56 26 [33580032]⟩,
  ⟨1, 970612, 1, 12, rkm128kMask56 27 [129966080]⟩,
  ⟨1, 423345, 1, 8, rkm128kMask56 27 [134139904]⟩,
  ⟨1, 322605, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 28`. -/
def hm256cs0RowR28 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 6, 6, 74, 0, 310, 61, 40, 150, 974, 854, 193408, 229425,
   2586, 4109416, 6091477479, 993903982802]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 28`. -/
def hm256cs0AncR28 : RampKick128kAnchor :=
  ⟨28, hm256cs0SegsR28, hm256cs0RowR28⟩
/-- Active `RampKick128k` segments for `m = 256, r = 29` (`8` segments). -/
def hm256cs0SegsR29 : List Rkm128kSeg := [
  ⟨1, 24104360, 2, 48, rkm128kMask56 30 [536870912]⟩,
  ⟨1, 21394361, 4, 24, rkm128kMask56 23 [5589504]⟩,
  ⟨1, 643605, 1, 8, rkm128kMask56 24 [13886464]⟩,
  ⟨1, 1333102, 1, 12, rkm128kMask56 26 [57149952]⟩,
  ⟨1, 883664, 1, 12, rkm128kMask56 27 [80676864]⟩,
  ⟨1, 972895, 1, 12, rkm128kMask56 28 [211402752]⟩,
  ⟨1, 421121, 1, 8, rkm128kMask56 28 [134717440]⟩,
  ⟨1, 347859, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 29`. -/
def hm256cs0RowR29 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 8, 0, 1, 23, 80, 50, 158, 167, 483, 3, 18007, 223605,
   291467, 16782, 5886107, 5901881293, 994091678630]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 29`. -/
def hm256cs0AncR29 : RampKick128kAnchor :=
  ⟨29, hm256cs0SegsR29, hm256cs0RowR29⟩
/-- Active `RampKick128k` segments for `m = 256, r = 30` (`24` segments). -/
def hm256cs0SegsR30 : List Rkm128kSeg := [
  ⟨1, 3182580, 2, 12, []⟩,
  ⟨1, 3865125, 1, 24, []⟩,
  ⟨1, 3876220, 1, 24, []⟩,
  ⟨1, 3641536, 1, 24, []⟩,
  ⟨1, 1672950, 1, 12, []⟩,
  ⟨1, 2597636, 1, 16, []⟩,
  ⟨1, 2174527, 1, 16, []⟩,
  ⟨1, 3006365, 1, 16, rkm128kMask56 31 [1073741824]⟩,
  ⟨1, 2681144, 1, 16, []⟩,
  ⟨1, 2163666, 1, 16, []⟩,
  ⟨1, 2360943, 1, 16, []⟩,
  ⟨1, 1912820, 1, 16, []⟩,
  ⟨1, 2097297, 1, 16, []⟩,
  ⟨1, 1779315, 1, 16, []⟩,
  ⟨1, 2314749, 1, 16, []⟩,
  ⟨1, 2182992, 1, 16, []⟩,
  ⟨1, 1593004, 1, 12, []⟩,
  ⟨1, 2346253, 1, 16, rkm128kMask56 24 [11192832]⟩,
  ⟨1, 673212, 1, 8, rkm128kMask56 25 [27780096]⟩,
  ⟨1, 1351116, 1, 12, rkm128kMask56 27 [114297344]⟩,
  ⟨1, 909170, 1, 12, rkm128kMask56 28 [161351680]⟩,
  ⟨1, 996202, 1, 12, rkm128kMask56 29 [422821888]⟩,
  ⟨1, 454895, 1, 8, rkm128kMask56 29 [269426688]⟩,
  ⟨1, 340630, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 30`. -/
def hm256cs0RowR30 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 3, 0, 2, 5, 20, 0, 8, 35, 448, 1423, 2021, 8565, 52, 937522,
   38058, 835017, 532366, 5670488145, 994327146006]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 30`. -/
def hm256cs0AncR30 : RampKick128kAnchor :=
  ⟨30, hm256cs0SegsR30, hm256cs0RowR30⟩
/-- Active `RampKick128k` segments for `m = 256, r = 32` (`32` segments). -/
def hm256cs0SegsR32 : List Rkm128kSeg := [
  ⟨1, 13367280, 1, 48, rkm128kMask56 33 [6438256640]⟩,
  ⟨1, 1943930, 1, 16, rkm128kMask56 31 [2147483647]⟩,
  ⟨1, 1945909, 1, 16, rkm128kMask56 26 [67108863]⟩,
  ⟨1, 1247674, 1, 12, rkm128kMask56 27 [134217727]⟩,
  ⟨1, 1248882, 1, 12, rkm128kMask56 29 [536870911]⟩,
  ⟨1, 1250459, 1, 12, rkm128kMask56 29 [536870911]⟩,
  ⟨1, 1252493, 1, 12, rkm128kMask56 31 [2147483647]⟩,
  ⟨1, 1611595, 1, 12, rkm128kMask56 31 [2147483647]⟩,
  ⟨1, 1616443, 1, 12, rkm128kMask56 1 [1]⟩,
  ⟨1, 1623747, 1, 12, rkm128kMask56 1 [1]⟩,
  ⟨1, 1626599, 1, 12, []⟩,
  ⟨1, 2096457, 1, 16, rkm128kMask56 1 [1]⟩,
  ⟨1, 2096448, 1, 16, rkm128kMask56 6 [43]⟩,
  ⟨1, 2096452, 1, 16, rkm128kMask56 10 [522]⟩,
  ⟨1, 2096334, 1, 16, rkm128kMask56 1 [1]⟩,
  ⟨1, 2230401, 1, 16, rkm128kMask56 5 [31]⟩,
  ⟨1, 2018677, 1, 16, rkm128kMask56 15 [32767]⟩,
  ⟨1, 1434871, 1, 12, rkm128kMask56 20 [1017159]⟩,
  ⟨1, 1414697, 1, 12, rkm128kMask56 23 [8388607]⟩,
  ⟨1, 1095828, 1, 12, rkm128kMask56 25 [25175042]⟩,
  ⟨1, 847246, 1, 12, rkm128kMask56 27 [103290880]⟩,
  ⟨1, 761079, 1, 12, rkm128kMask56 28 [201993490]⟩,
  ⟨1, 688426, 1, 12, rkm128kMask56 29 [277360720]⟩,
  ⟨1, 461045, 1, 8, rkm128kMask56 29 [360710768]⟩,
  ⟨1, 466657, 1, 8, rkm128kMask56 30 [620789778]⟩,
  ⟨1, 461259, 1, 8, rkm128kMask56 27 [83919468]⟩,
  ⟨1, 388863, 1, 8, rkm128kMask56 31 [1495302313]⟩,
  ⟨1, 204350, 1, 8, rkm128kMask56 31 [1881179138]⟩,
  ⟨1, 205219, 1, 8, rkm128kMask56 31 [1168113697]⟩,
  ⟨1, 195196, 1, 8, rkm128kMask56 31 [2132836352]⟩,
  ⟨1, 177906, 1, 8, rkm128kMask56 31 [2147483647]⟩,
  ⟨1, 139096, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 32`. -/
def hm256cs0RowR32 : List ℕ :=
  [17, 17, 43, 3, 0, 8, 14, 32, 101, 1, 31, 10, 40, 63, 16, 80, 8, 1, 113, 20, 500, 142, 795, 26,
   15413, 11850, 1105, 8798, 1245, 845970, 5410053243, 994589048747]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 32`. -/
def hm256cs0AncR32 : RampKick128kAnchor :=
  ⟨32, hm256cs0SegsR32, hm256cs0RowR32⟩
/-- Active `RampKick128k` segments for `m = 256, r = 33` (`16` segments). -/
def hm256cs0SegsR33 : List Rkm128kSeg := [
  ⟨1, 13147938, 1, 48, rkm128kMask56 32 [4286578688]⟩,
  ⟨1, 5995088, 1, 34, rkm128kMask56 29 [268435456]⟩,
  ⟨1, 5460658, 1, 24, rkm128kMask56 33 [4294967296]⟩,
  ⟨1, 4576454, 1, 24, []⟩,
  ⟨1, 3864421, 1, 24, rkm128kMask56 6 [39]⟩,
  ⟨1, 3230903, 1, 24, rkm128kMask56 11 [1918]⟩,
  ⟨1, 2938962, 2, 12, rkm128kMask56 16 [40965]⟩,
  ⟨1, 2292889, 1, 16, rkm128kMask56 19 [475138]⟩,
  ⟨1, 1764486, 1, 16, rkm128kMask56 21 [1311268]⟩,
  ⟨1, 1744366, 1, 16, rkm128kMask56 26 [41943050]⟩,
  ⟨1, 1252996, 1, 12, rkm128kMask56 28 [243567105]⟩,
  ⟨1, 1232372, 1, 12, rkm128kMask56 30 [805306370]⟩,
  ⟨1, 880057, 1, 12, rkm128kMask56 31 [1755578496]⟩,
  ⟨1, 719434, 1, 12, rkm128kMask56 31 [1252394272]⟩,
  ⟨1, 625579, 1, 8, rkm128kMask56 32 [2561182496]⟩,
  ⟨1, 649742, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 33`. -/
def hm256cs0RowR33 : List ℕ :=
  [2, 38, 91, 40, 2, 2, 121, 11, 0, 81, 24, 41, 68, 4, 2, 14, 7, 37, 213, 101, 71, 613, 8, 312,
   1781, 6213, 11462, 584871, 710809, 39793463, 202901, 5418325948, 994540351030]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 33`. -/
def hm256cs0AncR33 : RampKick128kAnchor :=
  ⟨33, hm256cs0SegsR33, hm256cs0RowR33⟩
/-- Active `RampKick128k` segments for `m = 256, r = 36` (`16` segments). -/
def hm256cs0SegsR36 : List Rkm128kSeg := [
  ⟨1, 12176316, 1, 48, rkm128kMask56 33 [8581545984]⟩,
  ⟨1, 7063276, 1, 34, rkm128kMask56 36 [66571993088]⟩,
  ⟨1, 5493865, 1, 34, rkm128kMask56 36 [34359738368]⟩,
  ⟨1, 4614995, 1, 24, []⟩,
  ⟨1, 3876744, 1, 24, []⟩,
  ⟨1, 3264753, 1, 24, rkm128kMask56 11 [1090]⟩,
  ⟨1, 2728867, 2, 12, rkm128kMask56 16 [40960]⟩,
  ⟨1, 2303883, 1, 16, rkm128kMask56 20 [542864]⟩,
  ⟨1, 1930586, 1, 16, rkm128kMask56 24 [14767108]⟩,
  ⟨1, 1617788, 1, 16, rkm128kMask56 28 [240430080]⟩,
  ⟨1, 1365900, 1, 12, rkm128kMask56 31 [1680713732]⟩,
  ⟨1, 1141697, 1, 12, rkm128kMask56 32 [3221239808]⟩,
  ⟨1, 961668, 1, 12, rkm128kMask56 34 [14044795904]⟩,
  ⟨1, 756459, 1, 12, rkm128kMask56 34 [9748784128]⟩,
  ⟨1, 659111, 1, 12, rkm128kMask56 35 [17519781888]⟩,
  ⟨1, 613099, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 36`. -/
def hm256cs0RowR36 : List ℕ :=
  [0, 2, 2, 0, 1, 0, 0, 5, 0, 0, 0, 0, 0, 0, 5, 2, 0, 4, 0, 94, 36, 14, 11, 59, 88, 418, 41630,
   12335, 156249, 163057, 646688, 3637116, 51710852, 32474498, 5394028112, 994517123680]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 36`. -/
def hm256cs0AncR36 : RampKick128kAnchor :=
  ⟨36, hm256cs0SegsR36, hm256cs0RowR36⟩
/-- Active `RampKick128k` segments for `m = 256, r = 40` (`16` segments). -/
def hm256cs0SegsR40 : List Rkm128kSeg := [
  ⟨1, 12285661, 1, 64, rkm128kMask56 35 [34342961152]⟩,
  ⟨1, 7127875, 1, 34, rkm128kMask56 40 [1090921693184]⟩,
  ⟨1, 5544728, 1, 34, rkm128kMask56 40 [824633720832]⟩,
  ⟨1, 4669803, 1, 24, rkm128kMask56 5 [22]⟩,
  ⟨1, 3591684, 1, 24, rkm128kMask56 8 [135]⟩,
  ⟨1, 3287897, 1, 24, rkm128kMask56 16 [40960]⟩,
  ⟨1, 2983126, 1, 24, rkm128kMask56 19 [262144]⟩,
  ⟨1, 2326829, 1, 16, rkm128kMask56 25 [16777225]⟩,
  ⟨1, 1790064, 1, 16, rkm128kMask56 28 [237324288]⟩,
  ⟨1, 1769626, 1, 16, rkm128kMask56 32 [3847659524]⟩,
  ⟨1, 1270485, 1, 12, rkm128kMask56 35 [26882123776]⟩,
  ⟨1, 1249573, 1, 12, rkm128kMask56 37 [108625418240]⟩,
  ⟨1, 892165, 1, 12, rkm128kMask56 38 [224725372928]⟩,
  ⟨1, 749902, 1, 12, rkm128kMask56 38 [155737276416]⟩,
  ⟨1, 649515, 1, 12, rkm128kMask56 39 [280607461440]⟩,
  ⟨1, 670457, 1, 12, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 40`. -/
def hm256cs0RowR40 : List ℕ :=
  [0, 3, 0, 0, 2, 0, 0, 5, 0, 2, 1, 0, 0, 14, 1, 9, 4, 8, 17, 32, 4, 71, 2, 0, 5, 49, 19, 39, 14,
   222, 7228, 5314, 2649, 12456, 131560, 935980, 50268531, 30893099, 4501147944, 995416589233]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 40`. -/
def hm256cs0AncR40 : RampKick128kAnchor :=
  ⟨40, hm256cs0SegsR40, hm256cs0RowR40⟩
/-- Active `RampKick128k` segments for `m = 256, r = 42` (`16` segments). -/
def hm256cs0SegsR42 : List Rkm128kSeg := [
  ⟨1, 13984122, 2, 34, rkm128kMask56 41 [2198889037824]⟩,
  ⟨1, 6399981, 1, 34, rkm128kMask56 42 [4363686772736]⟩,
  ⟨1, 4978588, 1, 34, rkm128kMask56 40 [549755813888]⟩,
  ⟨1, 4921636, 1, 34, rkm128kMask56 6 [47]⟩,
  ⟨1, 3482799, 1, 24, rkm128kMask56 11 [1033]⟩,
  ⟨1, 3465146, 1, 24, rkm128kMask56 18 [163841]⟩,
  ⟨1, 2464710, 1, 16, rkm128kMask56 24 [10489857]⟩,
  ⟨1, 2458328, 1, 16, rkm128kMask56 27 [100663425]⟩,
  ⟨1, 1735841, 1, 16, rkm128kMask56 31 [2041189376]⟩,
  ⟨1, 1727063, 1, 16, rkm128kMask56 35 [30944176132]⟩,
  ⟨1, 1302123, 1, 12, rkm128kMask56 37 [108138629632]⟩,
  ⟨1, 1250284, 1, 12, rkm128kMask56 39 [450339547140]⟩,
  ⟨1, 769832, 1, 12, rkm128kMask56 40 [859316486656]⟩,
  ⟨1, 657591, 1, 12, rkm128kMask56 40 [558384877568]⟩,
  ⟨1, 629573, 1, 12, rkm128kMask56 41 [1168773042176]⟩,
  ⟨1, 763451, 1, 12, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 42`. -/
def hm256cs0RowR42 : List ℕ :=
  [0, 2, 3, 2, 1, 6, 0, 0, 0, 1, 0, 7, 2, 9, 8, 49, 3, 162, 103, 426, 340, 7, 0, 264, 759, 319,
   51, 0, 316, 2746, 1654, 57, 64, 11202, 8032, 262293, 5613178, 3322851, 30437957, 9257779,
   4344662149, 995606408841]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 42`. -/
def hm256cs0AncR42 : RampKick128kAnchor :=
  ⟨42, hm256cs0SegsR42, hm256cs0RowR42⟩
/-- Active `RampKick128k` segments for `m = 256, r = 45` (`16` segments). -/
def hm256cs0SegsR45 : List Rkm128kSeg := [
  ⟨1, 17013757, 4, 24, rkm128kMask56 45 [33036888440832]⟩,
  ⟨1, 4811447, 1, 34, rkm128kMask56 45 [18141941858304]⟩,
  ⟨1, 4421327, 1, 24, rkm128kMask56 45 [30786325577728]⟩,
  ⟨1, 4750803, 1, 34, []⟩,
  ⟨1, 3629644, 1, 24, rkm128kMask56 1 [1]⟩,
  ⟨1, 3343700, 1, 24, rkm128kMask56 22 [2694156]⟩,
  ⟨1, 2383131, 2, 12, rkm128kMask56 27 [86151505]⟩,
  ⟨1, 2371021, 1, 16, rkm128kMask56 30 [1010212868]⟩,
  ⟨1, 1432603, 1, 16, rkm128kMask56 34 [15389508608]⟩,
  ⟨1, 1664552, 1, 16, rkm128kMask56 38 [245531494436]⟩,
  ⟨1, 1499332, 1, 16, rkm128kMask56 40 [938806161472]⟩,
  ⟨1, 1101508, 1, 12, rkm128kMask56 42 [3654298705920]⟩,
  ⟨1, 773727, 1, 12, rkm128kMask56 43 [4692587921408]⟩,
  ⟨1, 578326, 1, 12, rkm128kMask56 43 [4763454341248]⟩,
  ⟨1, 620975, 1, 12, rkm128kMask56 44 [8887700979720]⟩,
  ⟨1, 796501, 1, 12, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 45`. -/
def hm256cs0RowR45 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 1, 60, 0, 102, 46, 0, 29, 531, 585, 15,
   565, 284, 234, 578, 472, 4, 4170, 9472, 97099, 58410, 1152000, 22230, 4426112, 8155965,
   27825293, 4120721533, 995837515489]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 45`. -/
def hm256cs0AncR45 : RampKick128kAnchor :=
  ⟨45, hm256cs0SegsR45, hm256cs0RowR45⟩
/-- Active `RampKick128k` segments for `m = 256, r = 48` (`16` segments). -/
def hm256cs0SegsR48 : List Rkm128kSeg := [
  ⟨1, 16493944, 4, 24, []⟩,
  ⟨1, 5871365, 1, 34, []⟩,
  ⟨1, 4995376, 1, 34, []⟩,
  ⟨1, 4601723, 1, 34, rkm128kMask56 2 [2]⟩,
  ⟨1, 3493059, 1, 24, rkm128kMask56 8 [212]⟩,
  ⟨1, 3238573, 1, 24, rkm128kMask56 17 [123040]⟩,
  ⟨1, 2087773, 1, 16, rkm128kMask56 26 [65044480]⟩,
  ⟨1, 2296429, 1, 16, rkm128kMask56 34 [16161341442]⟩,
  ⟨1, 1667172, 1, 16, rkm128kMask56 38 [247640752256]⟩,
  ⟨1, 1612315, 1, 16, rkm128kMask56 42 [3926314524676]⟩,
  ⟨1, 1353119, 1, 16, rkm128kMask56 44 [13921441628672]⟩,
  ⟨1, 852377, 1, 12, rkm128kMask56 45 [19984828137480]⟩,
  ⟨1, 835056, 1, 12, rkm128kMask56 46 [37973158985728]⟩,
  ⟨1, 564886, 1, 8, rkm128kMask56 46 [39377687019520]⟩,
  ⟨1, 613022, 1, 12, rkm128kMask56 47 [74082098479616]⟩,
  ⟨1, 820076, 1, 12, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 48`. -/
def hm256cs0RowR48 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 2, 9, 26, 87, 1403, 2031, 184, 54885, 71744, 653190, 171110, 673476, 745243, 40047625,
   3883656817, 996073912311]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 48`. -/
def hm256cs0AncR48 : RampKick128kAnchor :=
  ⟨48, hm256cs0SegsR48, hm256cs0RowR48⟩
/-- Active `RampKick128k` segments for `m = 256, r = 64` (`72` segments). -/
def hm256cs0SegsR64 : List Rkm128kSeg := [
  ⟨1, 759020, 1, 12, rkm128kMask56 29 [429981696]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 57 [51209649373970432, 1]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 64 [25024145931370496, 155]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 65 [13912538983956480, 307]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 65 [2431733980987392, 393]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 64 [34427570141265920, 133]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 64 [5048250889404416, 182]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 65 [70133880434196480, 507]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 65 [19075075177185280, 324]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 64 [2371578130071552, 137]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 64 [12195230535122944, 188]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 65 [38970396497674240, 479]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 65 [14874171825717248, 262]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 65 [32997391921577984, 360]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 64 [66621436751511552, 212]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 65 [21506859756158975, 500]⟩,
  ⟨1, 761886, 1, 12, rkm128kMask56 65 [44260565698215936, 324]⟩,
  ⟨1, 761886, 1, 12, rkm128kMask56 64 [71702451782156288, 159]⟩,
  ⟨1, 761886, 1, 12, rkm128kMask56 65 [46150901064269824, 487]⟩,
  ⟨1, 761886, 1, 12, rkm128kMask56 65 [50639107528851456, 305]⟩,
  ⟨1, 761886, 1, 12, rkm128kMask56 63 [28622486694264832, 105]⟩,
  ⟨1, 761886, 1, 12, rkm128kMask56 65 [56646839063019520, 479]⟩,
  ⟨1, 761886, 1, 12, rkm128kMask56 65 [33073309763502080, 313]⟩,
  ⟨1, 761886, 1, 12, rkm128kMask56 64 [17451448556060672, 251]⟩,
  ⟨1, 691209, 1, 12, rkm128kMask56 62 [7881299347898368, 46]⟩,
  ⟨1, 691209, 1, 12, rkm128kMask56 61 [69805794224242688, 18]⟩,
  ⟨1, 691209, 1, 12, rkm128kMask56 60 [67553994410557440, 10]⟩,
  ⟨1, 691209, 1, 12, rkm128kMask56 65 [54043195528445952, 495]⟩,
  ⟨1, 691209, 1, 12, rkm128kMask56 65 [54043195528445952, 509]⟩,
  ⟨1, 691209, 1, 12, rkm128kMask56 65 [36028797018963968, 296]⟩,
  ⟨1, 691209, 1, 12, rkm128kMask56 65 [0, 448]⟩,
  ⟨1, 691209, 1, 12, rkm128kMask56 65 [0, 382]⟩,
  ⟨1, 787490, 1, 12, rkm128kMask56 65 [0, 308]⟩,
  ⟨1, 787491, 1, 12, rkm128kMask56 60 [2, 8]⟩,
  ⟨1, 787491, 1, 12, rkm128kMask56 64 [5, 144]⟩,
  ⟨1, 787491, 1, 12, rkm128kMask56 65 [0, 256]⟩,
  ⟨1, 787491, 1, 12, rkm128kMask56 65 [3, 288]⟩,
  ⟨1, 787490, 1, 12, rkm128kMask56 65 [178, 256]⟩,
  ⟨1, 678660, 1, 12, rkm128kMask56 65 [358, 320]⟩,
  ⟨1, 678660, 1, 12, rkm128kMask56 65 [84, 320]⟩,
  ⟨1, 678660, 1, 12, rkm128kMask56 12 [3159]⟩,
  ⟨1, 678661, 1, 12, rkm128kMask56 15 [18728]⟩,
  ⟨1, 678663, 1, 12, rkm128kMask56 64 [44235, 128]⟩,
  ⟨1, 678629, 1, 12, rkm128kMask56 65 [70783, 384]⟩,
  ⟨1, 807746, 1, 12, rkm128kMask56 18 [158061]⟩,
  ⟨1, 807746, 1, 12, rkm128kMask56 65 [271889, 256]⟩,
  ⟨1, 807734, 1, 12, rkm128kMask56 23 [6292494]⟩,
  ⟨1, 807734, 1, 12, rkm128kMask56 65 [393298, 256]⟩,
  ⟨1, 720339, 1, 12, rkm128kMask56 16 [34221]⟩,
  ⟨1, 720339, 1, 12, rkm128kMask56 29 [270680987]⟩,
  ⟨1, 720339, 1, 12, rkm128kMask56 22 [2109542]⟩,
  ⟨1, 720339, 1, 12, rkm128kMask56 33 [7449219226]⟩,
  ⟨1, 714615, 1, 12, rkm128kMask56 34 [8589942912]⟩,
  ⟨1, 714615, 1, 12, rkm128kMask56 37 [105226735637]⟩,
  ⟨1, 714615, 1, 12, rkm128kMask56 40 [756807672051]⟩,
  ⟨1, 1030994, 1, 12, rkm128kMask56 14 [8546]⟩,
  ⟨1, 1030994, 1, 12, rkm128kMask56 47 [106466423085699]⟩,
  ⟨1, 1686173, 1, 16, rkm128kMask56 52 [3986922218522278]⟩,
  ⟨1, 1245941, 1, 12, rkm128kMask56 55 [32673822683441061]⟩,
  ⟨1, 986073, 1, 12, rkm128kMask56 57 [41681570219753573, 1]⟩,
  ⟨1, 1167346, 1, 12, rkm128kMask56 59 [9615550049681419, 6]⟩,
  ⟨1, 732652, 1, 12, rkm128kMask56 60 [50118231698051893, 8]⟩,
  ⟨1, 771085, 1, 12, rkm128kMask56 61 [30005758758229236, 17]⟩,
  ⟨1, 770734, 1, 12, rkm128kMask56 62 [27182762821812264, 33]⟩,
  ⟨1, 379013, 1, 8, rkm128kMask56 62 [47850763929651298, 32]⟩,
  ⟨1, 130107, 1, 8, rkm128kMask56 58 [2993421112442990, 3]⟩,
  ⟨1, 572979, 1, 8, rkm128kMask56 63 [54650280734621795, 69]⟩,
  ⟨1, 241295, 1, 8, rkm128kMask56 63 [47475400427831880, 70]⟩,
  ⟨1, 240228, 1, 8, rkm128kMask56 63 [13520300457070848, 65]⟩,
  ⟨1, 238950, 1, 8, rkm128kMask56 63 [12009554409686055, 69]⟩,
  ⟨1, 237005, 1, 8, rkm128kMask56 63 [63238017376059395, 75]⟩,
  ⟨1, 219612, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 64`. -/
def hm256cs0RowR64 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 11, 0, 0, 39, 119, 886, 673, 3936, 1259, 0, 4814, 2914,
   14953, 169963, 290529, 261094, 92347, 2725984, 3147107407, 996849292519]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 64`. -/
def hm256cs0AncR64 : RampKick128kAnchor :=
  ⟨64, hm256cs0SegsR64, hm256cs0RowR64⟩
/-- Active `RampKick128k` segments for `m = 256, r = 92` (`8` segments). -/
def hm256cs0SegsR92 : List Rkm128kSeg := [
  ⟨1, 8613775, 2, 34, []⟩,
  ⟨1, 6910262, 1, 64, []⟩,
  ⟨1, 5605313, 2, 24, rkm128kMask56 93 [72057594037927916, 137438953471]⟩,
  ⟨1, 4278725, 1, 34, rkm128kMask56 93 [72057044428979838, 137438953471]⟩,
  ⟨1, 2545708, 1, 34, rkm128kMask56 93 [31650125789003904, 137438953408]⟩,
  ⟨1, 1250426, 1, 24, rkm128kMask56 93 [30680906293313536, 137438938847]⟩,
  ⟨1, 1504022, 1, 34, rkm128kMask56 93 [41109224279113728, 137437325088]⟩,
  ⟨1, 1161318, 1, 24, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 92`. -/
def hm256cs0RowR92 : List ℕ :=
  [0, 0, 0, 0, 0, 15, 214, 1981, 12559, 53505, 146962, 239642, 209394, 132320, 291151, 873497,
   106176, 1594587, 67160, 617622, 14691, 4203862, 946675, 11252583, 379001177, 610579823,
   181579736, 2474625316, 137086, 434219963, 123899875, 887987355, 283431190, 964519695,
   937784355, 179072055, 3301276996, 1596863438, 1114650264, 143741929, 3261833834, 1409573088,
   3890155759, 22000435556, 9279614131, 8976435847, 41783908090, 7310083168, 83596211847,
   1323939975, 125379992001, 208452151813, 6541837687, 46360390036, 8701729657, 2286957944,
   51998152645, 144488901799, 43410068076, 64088541886, 217991154, 33048027156, 23923340236,
   24159366, 2480443526, 12326903610, 15523018170, 6985175564, 3829477366, 2432229438, 70160505,
   738174375, 75967964, 63514592, 74268680, 371741, 9453106, 641244, 495611, 711492, 292991,
   75711, 15203, 2556, 367, 44, 4, 0, 0, 0, 0, 0]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 92`. -/
def hm256cs0AncR92 : RampKick128kAnchor :=
  ⟨92, hm256cs0SegsR92, hm256cs0RowR92⟩
/-- Active `RampKick128k` segments for `m = 256, r = 128` (`124` segments). -/
def hm256cs0SegsR128 : List Rkm128kSeg := [
  ⟨1, 470902, 1, 10, []⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 73 [41662694599688192, 107414]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 108 [37172289111851008, 3686149380764822]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 128 [36063981391052800, 8102251459480106, 35510]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 127 [36169534507319296, 26840275717960914, 28158]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 128 [36873221949095936, 53118714369396384, 61169]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 129 [1125899906842624, 5811608452707508, 106558]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 128 [4503599627370496, 23923809331025876, 52046]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 129 [27021597764222976, 49772076787550336, 117694]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 128 [36028797018963968, 62213788850547200, 53732]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 128 [0, 58295320905106050, 35247]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 129 [0, 21522524210778636, 102527]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 127 [0, 8892434556178448, 28854]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 129 [0, 27071029945028672, 109565]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 125 [0, 58617639738114432, 6608]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 128 [0, 48879036727722496, 33024]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 129 [0, 62617747837324288, 78689]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 127 [0, 33190365895069696, 17125]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 129 [0, 36170355751796736, 124839]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 129 [0, 38532301948289024, 103121]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 129 [0, 51399364916150272, 72661]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 128 [0, 35844380720627712, 42508]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 129 [0, 35250147702079488, 91459]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 128 [0, 26394141233512448, 63256]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 129 [0, 34238441537404928, 116820]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 129 [0, 1389674836787200, 87699]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 128 [0, 65420101179932672, 34453]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 129 [0, 10953034590846976, 81246]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 129 [0, 66228020431552512, 121343]⟩,
  ⟨1, 477041, 1, 10, rkm128kMask56 127 [0, 39184149503803392, 21512]⟩,
  ⟨1, 477041, 1, 10, rkm128kMask56 127 [0, 12864633937330176, 25675]⟩,
  ⟨1, 477041, 1, 10, rkm128kMask56 129 [0, 28892992324501504, 100955]⟩,
  ⟨1, 477041, 1, 10, rkm128kMask56 129 [0, 14406248023719936, 99607]⟩,
  ⟨1, 477041, 1, 10, rkm128kMask56 128 [0, 39696836528701440, 63776]⟩,
  ⟨1, 477041, 1, 10, rkm128kMask56 127 [0, 49279423962152960, 24761]⟩,
  ⟨1, 477041, 1, 10, rkm128kMask56 129 [0, 63101522073878528, 85977]⟩,
  ⟨1, 477041, 1, 10, rkm128kMask56 128 [0, 21270052439326720, 38987]⟩,
  ⟨1, 477041, 1, 10, rkm128kMask56 129 [0, 70410525619519488, 77106]⟩,
  ⟨1, 477041, 1, 10, rkm128kMask56 128 [0, 64682070038806528, 38388]⟩,
  ⟨1, 477041, 1, 10, rkm128kMask56 128 [1, 13950603533221888, 45817]⟩,
  ⟨1, 477041, 1, 10, rkm128kMask56 128 [1, 30434481856839680, 53642]⟩,
  ⟨1, 477041, 1, 10, rkm128kMask56 129 [4, 43980465111040000, 120924]⟩,
  ⟨1, 477041, 1, 10, rkm128kMask56 127 [9, 12807111440334848, 28255]⟩,
  ⟨1, 472944, 1, 10, rkm128kMask56 129 [15, 5348024557502464, 110712]⟩,
  ⟨1, 472944, 1, 10, rkm128kMask56 129 [59, 37717646879227904, 93594]⟩,
  ⟨1, 472944, 1, 10, rkm128kMask56 127 [143, 21392098230009856, 32429]⟩,
  ⟨1, 472944, 1, 10, rkm128kMask56 129 [892, 6755399441055744, 90393]⟩,
  ⟨1, 472944, 1, 10, rkm128kMask56 128 [1606, 9007199254740992, 32823]⟩,
  ⟨1, 472944, 1, 10, rkm128kMask56 128 [945, 18014398509481984, 56604]⟩,
  ⟨1, 472944, 1, 10, rkm128kMask56 127 [15333, 36028797018963968, 24172]⟩,
  ⟨1, 472944, 1, 10, rkm128kMask56 129 [49483, 36028797018963968, 106599]⟩,
  ⟨1, 472944, 1, 10, rkm128kMask56 128 [7050, 0, 40943]⟩,
  ⟨1, 472944, 1, 10, rkm128kMask56 129 [448397, 0, 125570]⟩,
  ⟨1, 472944, 1, 10, rkm128kMask56 128 [1281089, 0, 63236]⟩,
  ⟨1, 472944, 1, 10, rkm128kMask56 128 [7105154, 0, 46728]⟩,
  ⟨1, 471832, 1, 10, rkm128kMask56 128 [5573047, 0, 54544]⟩,
  ⟨1, 471832, 1, 10, rkm128kMask56 129 [72490406, 0, 75552]⟩,
  ⟨1, 471832, 1, 10, rkm128kMask56 127 [100999719, 0, 19488]⟩,
  ⟨1, 471832, 1, 10, rkm128kMask56 124 [1914277548, 0, 3136]⟩,
  ⟨1, 471832, 1, 10, rkm128kMask56 129 [3063550281, 0, 81024]⟩,
  ⟨1, 471832, 1, 10, rkm128kMask56 128 [4528154798, 0, 34816]⟩,
  ⟨1, 471832, 1, 10, rkm128kMask56 128 [31937471335, 0, 48384]⟩,
  ⟨1, 471832, 1, 10, rkm128kMask56 129 [626850192725, 0, 115200]⟩,
  ⟨1, 471832, 1, 10, rkm128kMask56 129 [669965047578, 0, 72192]⟩,
  ⟨1, 471832, 1, 10, rkm128kMask56 127 [9425263868736, 0, 23552]⟩,
  ⟨1, 471832, 1, 10, rkm128kMask56 128 [32657740233708, 0, 32768]⟩,
  ⟨1, 490659, 1, 10, rkm128kMask56 129 [403403280279911, 0, 126976]⟩,
  ⟨1, 490659, 1, 10, rkm128kMask56 129 [717107447441755, 0, 73728]⟩,
  ⟨1, 490659, 1, 10, rkm128kMask56 129 [3920814467817624, 0, 73728]⟩,
  ⟨1, 490659, 1, 10, rkm128kMask56 126 [9252045908651789, 0, 8192]⟩,
  ⟨1, 490659, 1, 10, rkm128kMask56 129 [68222068285630165, 0, 106496]⟩,
  ⟨1, 490659, 1, 10, rkm128kMask56 129 [19958792167151740, 2, 81920]⟩,
  ⟨1, 490659, 1, 10, rkm128kMask56 128 [34278525084460675, 31, 49152]⟩,
  ⟨1, 490659, 1, 10, rkm128kMask56 129 [52680803798884755, 107, 98304]⟩,
  ⟨1, 490659, 1, 10, rkm128kMask56 128 [46994380968313833, 494, 32768]⟩,
  ⟨1, 453178, 1, 10, rkm128kMask56 129 [56912568760929969, 819, 65536]⟩,
  ⟨1, 453178, 1, 10, rkm128kMask56 128 [50249594099227573, 10875, 32768]⟩,
  ⟨1, 453178, 1, 10, rkm128kMask56 128 [22335928310815609, 36896, 32768]⟩,
  ⟨1, 453178, 1, 10, rkm128kMask56 128 [64497846355428193, 115170, 32768]⟩,
  ⟨1, 453178, 1, 10, rkm128kMask56 129 [46735306740995481, 146122, 98304]⟩,
  ⟨1, 453178, 1, 10, rkm128kMask56 129 [71447193484957727, 1825659, 65536]⟩,
  ⟨1, 453178, 1, 10, rkm128kMask56 81 [44397919557108380, 25875617]⟩,
  ⟨1, 453178, 1, 10, rkm128kMask56 129 [18137230534607915, 60364090, 65536]⟩,
  ⟨1, 459005, 1, 10, rkm128kMask56 84 [45324302116986471, 261349891]⟩,
  ⟨1, 459005, 1, 10, rkm128kMask56 129 [10063142506695750, 400347416, 65536]⟩,
  ⟨1, 459004, 1, 10, rkm128kMask56 129 [42073561834165946, 1812913138, 65536]⟩,
  ⟨1, 459006, 1, 10, rkm128kMask56 129 [8401278621154954, 27699761638, 65536]⟩,
  ⟨1, 458998, 1, 10, rkm128kMask56 129 [5396308296039394, 15332018670, 65536]⟩,
  ⟨1, 459009, 1, 10, rkm128kMask56 129 [67462367076813995, 482489664578, 65536]⟩,
  ⟨1, 458974, 1, 10, rkm128kMask56 129 [33560346089587078, 1416093770792, 65536]⟩,
  ⟨1, 494119, 1, 10, rkm128kMask56 129 [15168843645420080, 5621910686709, 65536]⟩,
  ⟨1, 493817, 1, 10, rkm128kMask56 129 [26548348895323338, 33134272529936, 65536]⟩,
  ⟨1, 493798, 1, 10, rkm128kMask56 129 [59357141445525669, 76120368280876, 65536]⟩,
  ⟨1, 492887, 1, 10, rkm128kMask56 102 [47168225198111259, 43344754417745]⟩,
  ⟨1, 492878, 1, 10, rkm128kMask56 129 [33489703241601827, 1108102871613196, 65536]⟩,
  ⟨1, 511647, 1, 10, rkm128kMask56 108 [66785571926851077, 2459441452957050]⟩,
  ⟨1, 508815, 1, 10, rkm128kMask56 105 [12853169081935991, 296518156166500]⟩,
  ⟨1, 508965, 1, 10, rkm128kMask56 111 [25685843214309055, 18381587499664046]⟩,
  ⟨1, 499421, 1, 10, rkm128kMask56 112 [63115334631142077, 63165399772997543]⟩,
  ⟨1, 537467, 1, 10, rkm128kMask56 110 [45474603493890442, 10433607549331943]⟩,
  ⟨1, 537815, 1, 10, rkm128kMask56 110 [24184576580340193, 10142523770468228]⟩,
  ⟨1, 538205, 1, 10, rkm128kMask56 116 [57565652465418591, 20712392705554744, 12]⟩,
  ⟨1, 1443922, 1, 18, rkm128kMask56 119 [11980792198689391, 12598158141896428, 100]⟩,
  ⟨1, 1190162, 1, 16, rkm128kMask56 121 [26091554351325833, 4930114363109357, 442]⟩,
  ⟨1, 1352269, 1, 18, rkm128kMask56 123 [22793353603344760, 59857009521421032, 1770]⟩,
  ⟨1, 887684, 1, 14, rkm128kMask56 124 [39427782835046753, 36645965474674370, 2178]⟩,
  ⟨1, 916272, 1, 14, rkm128kMask56 125 [48538543638840583, 64564707676470613, 4138]⟩,
  ⟨1, 626864, 1, 12, rkm128kMask56 111 [66978700649250657, 35377601592155134]⟩,
  ⟨1, 482830, 1, 10, rkm128kMask56 126 [18402541894377481, 11759968751927841, 8291]⟩,
  ⟨1, 470169, 1, 10, rkm128kMask56 119 [40533548809806217, 38359801083797610, 64]⟩,
  ⟨1, 370259, 1, 8, rkm128kMask56 126 [4824658373520394, 11923243814328194, 8218]⟩,
  ⟨1, 218357, 1, 6, rkm128kMask56 127 [10282644638009652, 51832112042516650, 16578]⟩,
  ⟨1, 226848, 1, 8, rkm128kMask56 127 [36110720433259335, 12162019318917354, 16984]⟩,
  ⟨1, 202586, 1, 6, rkm128kMask56 127 [9032506041233686, 47997273916901600, 17753]⟩,
  ⟨1, 190825, 1, 6, rkm128kMask56 127 [45071631639874057, 66295148936441616, 16459]⟩,
  ⟨1, 172248, 1, 6, rkm128kMask56 127 [11540491376112761, 11686986159491682, 17890]⟩,
  ⟨1, 147956, 1, 6, rkm128kMask56 127 [45071592996213251, 45745189871954326, 17448]⟩,
  ⟨1, 118680, 1, 6, rkm128kMask56 127 [11295575044596227, 43775202460707490, 16816]⟩,
  ⟨1, 103576, 1, 6, rkm128kMask56 127 [598134327083266, 48278810440771744, 16650]⟩,
  ⟨1, 20874, 1, 6, rkm128kMask56 123 [9042383632597826, 2961331103992354, 1344]⟩,
  ⟨1, 86944, 1, 6, rkm128kMask56 127 [36028797019701256, 47887384805025920, 18217]⟩,
  ⟨1, 102310, 1, 6, rkm128kMask56 127 [45035996408184963, 48102889085995746, 17303]⟩,
  ⟨1, 85696, 1, 6, rkm128kMask56 127 [37888, 54889006189783682, 19898]⟩,
  ⟨1, 66033, 1, 6, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 256, r = 128`. -/
def hm256cs0RowR128 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 2, 0, 0, 1, 0, 3, 7, 46, 43, 37, 32,
   28, 3, 65, 60, 361, 192, 2156, 3097, 11729, 5, 27433, 7487, 24948, 2667, 21681, 48355, 69441,
   103694, 8836, 181883, 1420340, 530698, 111996, 895318, 2258, 670, 412588, 16248456, 7735832,
   2839399, 29687, 47955067, 32357019, 306157, 2354143048, 997534164630]
/-- Packaged `RampKick128kAnchor` for `m = 256, r = 128`. -/
def hm256cs0AncR128 : RampKick128kAnchor :=
  ⟨128, hm256cs0SegsR128, hm256cs0RowR128⟩
/-- All `38` `r <= 128` prefix `RampKick128k` anchors for `m = 256`. -/
def pfxAnchorsLt256 : List RampKick128kAnchor :=
  [hm256cs0AncR3, hm256cs0AncR4, hm256cs0AncR5, hm256cs0AncR6, hm256cs0AncR7, hm256cs0AncR8,
   hm256cs0AncR9, hm256cs0AncR10, hm256cs0AncR11, hm256cs0AncR12, hm256cs0AncR13,
   hm256cs0AncR14, hm256cs0AncR15, hm256cs0AncR16, hm256cs0AncR17, hm256cs0AncR18,
   hm256cs0AncR19, hm256cs0AncR20, hm256cs0AncR21, hm256cs0AncR22, hm256cs0AncR23,
   hm256cs0AncR24, hm256cs0AncR25, hm256cs0AncR26, hm256cs0AncR27, hm256cs0AncR28,
   hm256cs0AncR29, hm256cs0AncR30, hm256cs0AncR32, hm256cs0AncR33, hm256cs0AncR36,
   hm256cs0AncR40, hm256cs0AncR42, hm256cs0AncR45, hm256cs0AncR48, hm256cs0AncR64,
   hm256cs0AncR92, hm256cs0AncR128]
/-- Segment `0` (`1` segment) of `(256, 256)` `r = 256`. -/
def s0Segs : List Rkm128kSeg := [
  ⟨1, 452954, 1, 10, rkm128kMask56 55 [19083739182407680]⟩]
/-- Output multiplicity `lOut = 1` exiting `s0Segs` (`seg 0`). -/
def s0LOut : ℕ := 1
/-- Output truncated dimension `dCur = 256` exiting `s0Segs`. -/
def s0DCurOut : ℕ := 256
/-- Output `10 ^ 15`-scaled error pad `accPad = 5948126` exiting `s0Segs`. -/
def s0PadOut : ℕ := 5948126
/-- Slice `0` (`11` entries) of `s0Vec`. -/
def s0Vec0 : List ℤ :=
  [Int.ofNat 973464840338461, Int.ofNat 225790178669534, Int.ofNat 36887129735784,
   Int.ofNat 4901086851957, Int.ofNat 561729460140, Int.ofNat 57357227917, Int.ofNat 5325129204,
   Int.ofNat 455738665, Int.ofNat 36350917, Int.ofNat 2794312, Int.ofNat 197722]
/-- Checkpoint `11`-entry fixed-point amplitude vector exiting `s0Segs`. -/
def s0Vec : List ℤ := s0Vec0
/-- Segment count of `s0Segs` (`1` segment). -/
theorem s0Segs_len : rkm128kSegListLen s0Segs = 1 := rfl
end
public section
open QuantumComputation.Specs.DickeSol
private theorem s0AndL {a b : Bool} (h : Bool.and a b = true) : a = true := by
  cases a <;> cases h; rfl
private theorem s0AndR {a b : Bool} (h : Bool.and a b = true) : b = true := by
  cases a <;> cases b <;> cases h; rfl
private def s0NatEq (x y : ℕ) : Bool := Bool.and (Nat.ble x y) (Nat.ble y x)
private theorem s0NatEq_eq {x y : ℕ} (h : s0NatEq x y = true) : x = y := by
  unfold s0NatEq at h; rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at h; omega
private def s0NatListEq (xs ys : List ℕ) : Bool :=
  match xs, ys with
  | [], [] => true | x :: xr, y :: yr => cond (s0NatEq x y) (s0NatListEq xr yr) false
  | _, _ => false
private theorem s0NatListEq_eq {xs ys : List ℕ} (h : s0NatListEq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with | nil => rfl | cons _ _ => cases h
  | cons x xr ih =>
    cases ys with
    | nil => cases h
    | cons y yr =>
      dsimp only [s0NatListEq] at h; cases hxy : s0NatEq x y with
      | false => rw [hxy] at h; cases h
      | true => rw [hxy] at h; exact congrArg₂ List.cons (s0NatEq_eq hxy) (ih h)
private def s0IntEq (a b : ℤ) : Bool :=
  match a, b with
  | Int.ofNat x, Int.ofNat y => s0NatEq x y | Int.negSucc x, Int.negSucc y => s0NatEq x y
  | _, _ => false
private theorem s0IntEq_eq {a b : ℤ} (h : s0IntEq a b = true) : a = b := by
  cases a with
  | ofNat x =>
    cases b with | ofNat y => exact congrArg Int.ofNat (s0NatEq_eq h) | _ => cases h
  | negSucc x =>
    cases b with | ofNat _ => cases h | negSucc y => exact congrArg Int.negSucc (s0NatEq_eq h)
private def s0IntListEq (xs ys : List ℤ) : Bool :=
  match xs, ys with
  | [], [] => true | x :: xr, y :: yr => cond (s0IntEq x y) (s0IntListEq xr yr) false
  | _, _ => false
private theorem s0IntListEq_eq {xs ys : List ℤ} (h : s0IntListEq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with | nil => rfl | cons _ _ => cases h
  | cons x xr ih =>
    cases ys with
    | nil => cases h
    | cons y yr =>
      dsimp only [s0IntListEq] at h; cases hxy : s0IntEq x y with
      | false => rw [hxy] at h; cases h
      | true => rw [hxy] at h; exact congrArg₂ List.cons (s0IntEq_eq hxy) (ih h)
private def s0AtF (bs : List Bool) : Bool :=
  match bs with | [] => true | b :: rest => cond b (s0AtF rest) false
private theorem s0_hd {b : Bool} {bs : List Bool} (h : s0AtF (b :: bs) = true) : b = true := by
  unfold s0AtF at h; cases b <;> first | cases h | rfl
private theorem s0_tl1 {b : Bool} {s : List Bool}
    (h : s0AtF (b :: s) = true) : s0AtF s = true := by
  unfold s0AtF at h; cases b <;> first | cases h | exact h
private theorem s0_tl2 {b1 b2 : Bool} {bs : List Bool}
    (h : s0AtF (b1 :: b2 :: bs) = true) : s0AtF bs = true := s0_tl1 (s0_tl1 h)
private theorem s0_tl4 {b1 b2 b3 b4 : Bool} {bs : List Bool}
    (h : s0AtF (b1 :: b2 :: b3 :: b4 :: bs) = true) : s0AtF bs = true := s0_tl2 (s0_tl2 h)
private def s0ChkRow (r : ℕ) (segs : List Rkm128kSeg) (row : List ℕ) : Bool :=
  s0NatListEq (rkm128kEvalRowLo12 256 2 r segs) row
private theorem s0ChkRow_eq {r : ℕ} {segs : List Rkm128kSeg} {row : List ℕ}
    (h : s0ChkRow r segs row = true) : rkm128kEvalRowLo12 256 2 r segs = row :=
  s0NatListEq_eq h
private def s0StateAt (st : ℕ × ℕ × ℕ × List ℤ) (l d p : ℕ) (v : List ℤ) : Bool :=
  match st with
  | (ls, ds, ps, vs) =>
    Bool.and (s0NatEq ls l) (Bool.and (s0NatEq ds d) (Bool.and (s0NatEq ps p) (s0IntListEq vs v)))
private theorem s0StateAt_eq {st : ℕ × ℕ × ℕ × List ℤ} {l d p : ℕ} {v : List ℤ}
    (h : s0StateAt st l d p v = true) : st = (l, d, p, v) := by
  rcases st with ⟨ls, ds, ps, vs⟩; unfold s0StateAt at h; dsimp only at h
  simp only [Bool.and_eq_true] at h; rcases h with ⟨hl, ⟨hd, ⟨hp, hv⟩⟩⟩
  rw [s0NatEq_eq hl, s0NatEq_eq hd, s0NatEq_eq hp, s0IntListEq_eq hv]
private abbrev s0P : ℕ → ℤ := Int.ofNat
private abbrev s0N : ℕ → ℤ := Int.negSucc
private def s0RunAt (r : ℕ) (c : List Rkm128kSeg) (l0 d0 p0 : ℕ) (v0 : List ℤ)
    (l1 d1 p1 : ℕ) (v1 : List ℤ) : Bool :=
  s0StateAt (rkm128kRunSegs 256 2 r c l0 d0 p0 v0) l1 d1 p1 v1
private theorem s0RunLast {r : ℕ} {c : List Rkm128kSeg} {l0 d0 p0 l1 d1 p1 : ℕ} {v0 v1 : List ℤ}
    (h : s0RunAt r c l0 d0 p0 v0 l1 d1 p1 v1 = true) :
    rkm128kRunSegs 256 2 r c l0 d0 p0 v0 = (l1, d1, p1, v1) := s0StateAt_eq h
private theorem s0RunStep {r : ℕ} {c rest : List Rkm128kSeg}
    {l0 d0 p0 l1 d1 p1 l2 d2 p2 : ℕ} {v0 v1 v2 : List ℤ}
    (h1 : s0RunAt r c l0 d0 p0 v0 l1 d1 p1 v1 = true)
    (h2 : rkm128kRunSegs 256 2 r rest l1 d1 p1 v1 = (l2, d2, p2, v2)) :
    rkm128kRunSegs 256 2 r (c ++ rest) l0 d0 p0 v0 = (l2, d2, p2, v2) := by
  unfold s0RunAt at h1; rw [rkm128kRunSegs_append]; dsimp only
  rw [s0StateAt_eq h1]; exact h2
private theorem s0RowChk0 : s0AtF [
    s0ChkRow 3 hm256cs0SegsR3 hm256cs0RowR3,
    s0ChkRow 4 hm256cs0SegsR4 hm256cs0RowR4,
    s0ChkRow 5 hm256cs0SegsR5 hm256cs0RowR5,
    s0ChkRow 6 hm256cs0SegsR6 hm256cs0RowR6,
    s0ChkRow 7 hm256cs0SegsR7 hm256cs0RowR7,
    s0ChkRow 8 hm256cs0SegsR8 hm256cs0RowR8,
    s0ChkRow 9 hm256cs0SegsR9 hm256cs0RowR9,
    s0ChkRow 10 hm256cs0SegsR10 hm256cs0RowR10,
    s0ChkRow 11 hm256cs0SegsR11 hm256cs0RowR11,
    s0ChkRow 12 hm256cs0SegsR12 hm256cs0RowR12,
    s0ChkRow 13 hm256cs0SegsR13 hm256cs0RowR13,
    s0ChkRow 14 hm256cs0SegsR14 hm256cs0RowR14,
    s0ChkRow 15 hm256cs0SegsR15 hm256cs0RowR15,
    s0ChkRow 16 hm256cs0SegsR16 hm256cs0RowR16,
    s0ChkRow 17 hm256cs0SegsR17 hm256cs0RowR17,
    s0ChkRow 18 hm256cs0SegsR18 hm256cs0RowR18,
    s0ChkRow 19 hm256cs0SegsR19 hm256cs0RowR19,
    s0ChkRow 20 hm256cs0SegsR20 hm256cs0RowR20,
    s0ChkRow 21 hm256cs0SegsR21 hm256cs0RowR21
  ] = true := by
  decide +kernel
private theorem s0RowChk1 : s0AtF [
    s0ChkRow 22 hm256cs0SegsR22 hm256cs0RowR22,
    s0ChkRow 23 hm256cs0SegsR23 hm256cs0RowR23,
    s0ChkRow 24 hm256cs0SegsR24 hm256cs0RowR24,
    s0ChkRow 25 hm256cs0SegsR25 hm256cs0RowR25,
    s0ChkRow 26 hm256cs0SegsR26 hm256cs0RowR26,
    s0ChkRow 27 hm256cs0SegsR27 hm256cs0RowR27,
    s0ChkRow 28 hm256cs0SegsR28 hm256cs0RowR28
  ] = true := by
  decide +kernel
private theorem s0RowChk2 : s0AtF [
    s0ChkRow 29 hm256cs0SegsR29 hm256cs0RowR29,
    s0ChkRow 30 hm256cs0SegsR30 hm256cs0RowR30,
    s0ChkRow 32 hm256cs0SegsR32 hm256cs0RowR32,
    s0ChkRow 33 hm256cs0SegsR33 hm256cs0RowR33
  ] = true := by
  decide +kernel
private theorem s0RowChk3 : s0AtF [
    s0ChkRow 36 hm256cs0SegsR36 hm256cs0RowR36,
    s0ChkRow 40 hm256cs0SegsR40 hm256cs0RowR40,
    s0ChkRow 42 hm256cs0SegsR42 hm256cs0RowR42
  ] = true := by
  decide +kernel
private theorem s0RowChk4 : s0AtF [
    s0ChkRow 45 hm256cs0SegsR45 hm256cs0RowR45,
    s0ChkRow 48 hm256cs0SegsR48 hm256cs0RowR48
  ] = true := by
  decide +kernel
private theorem s0RowChk5 : s0AtF [
    s0ChkRow 92 hm256cs0SegsR92 hm256cs0RowR92,
    s0RunAt 256 s0Segs 1 0 1 [Int.ofNat wdScale] 1 256 5948126 s0Vec
  ] = true := by
  decide +kernel
private def r64Chk0 : List Rkm128kSeg := [
  ⟨1, 759020, 1, 12, rkm128kMask56 29 [429981696]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 57 [51209649373970432, 1]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 64 [25024145931370496, 155]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 65 [13912538983956480, 307]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 65 [2431733980987392, 393]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 64 [34427570141265920, 133]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 64 [5048250889404416, 182]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 65 [70133880434196480, 507]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 65 [19075075177185280, 324]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 64 [2371578130071552, 137]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 64 [12195230535122944, 188]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 65 [38970396497674240, 479]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 65 [14874171825717248, 262]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 65 [32997391921577984, 360]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 64 [66621436751511552, 212]⟩,
  ⟨1, 759020, 1, 12, rkm128kMask56 65 [21506859756158975, 500]⟩,
  ⟨1, 761886, 1, 12, rkm128kMask56 65 [44260565698215936, 324]⟩,
  ⟨1, 761886, 1, 12, rkm128kMask56 64 [71702451782156288, 159]⟩,
  ⟨1, 761886, 1, 12, rkm128kMask56 65 [46150901064269824, 487]⟩,
  ⟨1, 761886, 1, 12, rkm128kMask56 65 [50639107528851456, 305]⟩,
  ⟨1, 761886, 1, 12, rkm128kMask56 63 [28622486694264832, 105]⟩,
  ⟨1, 761886, 1, 12, rkm128kMask56 65 [56646839063019520, 479]⟩,
  ⟨1, 761886, 1, 12, rkm128kMask56 65 [33073309763502080, 313]⟩,
  ⟨1, 761886, 1, 12, rkm128kMask56 64 [17451448556060672, 251]⟩,
  ⟨1, 691209, 1, 12, rkm128kMask56 62 [7881299347898368, 46]⟩,
  ⟨1, 691209, 1, 12, rkm128kMask56 61 [69805794224242688, 18]⟩,
  ⟨1, 691209, 1, 12, rkm128kMask56 60 [67553994410557440, 10]⟩,
  ⟨1, 691209, 1, 12, rkm128kMask56 65 [54043195528445952, 495]⟩,
  ⟨1, 691209, 1, 12, rkm128kMask56 65 [54043195528445952, 509]⟩,
  ⟨1, 691209, 1, 12, rkm128kMask56 65 [36028797018963968, 296]⟩,
  ⟨1, 691209, 1, 12, rkm128kMask56 65 [0, 448]⟩,
  ⟨1, 691209, 1, 12, rkm128kMask56 65 [0, 382]⟩,
  ⟨1, 787490, 1, 12, rkm128kMask56 65 [0, 308]⟩,
  ⟨1, 787491, 1, 12, rkm128kMask56 60 [2, 8]⟩,
  ⟨1, 787491, 1, 12, rkm128kMask56 64 [5, 144]⟩,
  ⟨1, 787491, 1, 12, rkm128kMask56 65 [0, 256]⟩,
  ⟨1, 787491, 1, 12, rkm128kMask56 65 [3, 288]⟩,
  ⟨1, 787490, 1, 12, rkm128kMask56 65 [178, 256]⟩,
  ⟨1, 678660, 1, 12, rkm128kMask56 65 [358, 320]⟩,
  ⟨1, 678660, 1, 12, rkm128kMask56 65 [84, 320]⟩,
  ⟨1, 678660, 1, 12, rkm128kMask56 12 [3159]⟩,
  ⟨1, 678661, 1, 12, rkm128kMask56 15 [18728]⟩,
  ⟨1, 678663, 1, 12, rkm128kMask56 64 [44235, 128]⟩,
  ⟨1, 678629, 1, 12, rkm128kMask56 65 [70783, 384]⟩,
  ⟨1, 807746, 1, 12, rkm128kMask56 18 [158061]⟩,
  ⟨1, 807746, 1, 12, rkm128kMask56 65 [271889, 256]⟩,
  ⟨1, 807734, 1, 12, rkm128kMask56 23 [6292494]⟩,
  ⟨1, 807734, 1, 12, rkm128kMask56 65 [393298, 256]⟩,
  ⟨1, 720339, 1, 12, rkm128kMask56 16 [34221]⟩,
  ⟨1, 720339, 1, 12, rkm128kMask56 29 [270680987]⟩,
  ⟨1, 720339, 1, 12, rkm128kMask56 22 [2109542]⟩,
  ⟨1, 720339, 1, 12, rkm128kMask56 33 [7449219226]⟩,
  ⟨1, 714615, 1, 12, rkm128kMask56 34 [8589942912]⟩]
private def r64St0VecS0 : List ℤ :=
  [s0P 241166, s0N 597144, s0P 1441086, s0N 4312077, s0P 206960, s0P 1323982, s0P 4301624,
   s0N 4498266, s0N 3207846, s0P 8855417, s0N 6436354, s0N 521956, s0N 10781253, s0N 15748448,
   s0P 7091722, s0N 5312998, s0P 5911748, s0N 2407953, s0P 4375230, s0P 7956613, s0N 2851728,
   s0N 18548411, s0P 17903668, s0N 16130730, s0P 8300571, s0P 16919380, s0P 2558611,
   s0N 12342443, s0N 10774931, s0P 2393048, s0N 5022128, s0N 44288663, s0N 9799174, s0N 52971731,
   s0N 12016403, s0N 38285691, s0N 246124963, s0N 1132242771, s0N 4397975995, s0N 15622418099,
   s0N 50513913528, s0N 150108941768, s0N 412887775139, s0N 1054368487631, s0N 2508275284073,
   s0N 5569238137045, s0N 11559204902765, s0N 22445734913600, s0N 40795273143148,
   s0N 69398329513421, s0N 110447164788755, s0N 164307058907277, s0N 228170895515180,
   s0N 295232639973192, s0N 355045903839056, s0N 395560761317445, s0N 406583458925198,
   s0N 383439850347883, s0N 329467536168455, s0N 255401827310297, s0N 176250225002580,
   s0N 106223205682227, s0N 53927332127558, s0N 22193587918799]
private def r64St0VecS1 : List ℤ :=
  [s0N 5882916567532]
private def r64St0Vec : List ℤ :=
  r64St0VecS0 ++
  (r64St0VecS1)
private def r64Chk1 : List Rkm128kSeg := [
  ⟨1, 714615, 1, 12, rkm128kMask56 37 [105226735637]⟩,
  ⟨1, 714615, 1, 12, rkm128kMask56 40 [756807672051]⟩,
  ⟨1, 1030994, 1, 12, rkm128kMask56 14 [8546]⟩,
  ⟨1, 1030994, 1, 12, rkm128kMask56 47 [106466423085699]⟩,
  ⟨1, 1686173, 1, 16, rkm128kMask56 52 [3986922218522278]⟩,
  ⟨1, 1245941, 1, 12, rkm128kMask56 55 [32673822683441061]⟩,
  ⟨1, 986073, 1, 12, rkm128kMask56 57 [41681570219753573, 1]⟩,
  ⟨1, 1167346, 1, 12, rkm128kMask56 59 [9615550049681419, 6]⟩,
  ⟨1, 732652, 1, 12, rkm128kMask56 60 [50118231698051893, 8]⟩,
  ⟨1, 771085, 1, 12, rkm128kMask56 61 [30005758758229236, 17]⟩,
  ⟨1, 770734, 1, 12, rkm128kMask56 62 [27182762821812264, 33]⟩,
  ⟨1, 379013, 1, 8, rkm128kMask56 62 [47850763929651298, 32]⟩,
  ⟨1, 130107, 1, 8, rkm128kMask56 58 [2993421112442990, 3]⟩,
  ⟨1, 572979, 1, 8, rkm128kMask56 63 [54650280734621795, 69]⟩,
  ⟨1, 241295, 1, 8, rkm128kMask56 63 [47475400427831880, 70]⟩,
  ⟨1, 240228, 1, 8, rkm128kMask56 63 [13520300457070848, 65]⟩,
  ⟨1, 238950, 1, 8, rkm128kMask56 63 [12009554409686055, 69]⟩,
  ⟨1, 237005, 1, 8, rkm128kMask56 63 [63238017376059395, 75]⟩,
  ⟨1, 219612, 1, 8, []⟩]
private def r64St1VecS0 : List ℤ :=
  [s0P 461757, s0P 74749, s0N 1925995, s0P 35625, s0P 2815954, s0N 659968, s0N 2889931,
   s0P 5336806, s0N 2641749, s0P 4735357, s0P 13799573, s0N 3038190, s0N 12025796, s0N 13629464,
   s0N 12322301, s0P 15575197, s0N 1502727, s0N 3426862, s0P 16959936, s0N 14406836,
   s0P 12237381, s0P 4145252, s0P 732239, s0P 2305922, s0N 1338632, s0N 7300884, s0N 24701432,
   s0N 6274366, s0N 19506271, s0P 21665923, s0P 9415809, s0N 17590411, s0P 12844662,
   s0N 30744779, s0N 27764686, s0P 35914068, s0P 29183351, s0N 117643962, s0N 28889090,
   s0P 25315917, s0P 24399419, s0P 48408656, s0N 1227287446, s0P 585075192, s0N 1384019843,
   s0P 3449447989, s0P 490050695, s0N 362568603, s0P 6324721605, s0N 10937704723,
   s0P 29788608499, s0N 25969746020, s0N 62754539659, s0N 35502580590, s0P 185205885,
   s0N 69404112381, s0N 53999677826, s0P 122298707559, s0P 412280347102, s0P 539022488035,
   s0N 510988747290, s0N 303902048222, s0P 1651070063351, s0N 56099100043576]
private def r64St1VecS1 : List ℤ :=
  [s0N 998423417851645]
private def r64St1Vec : List ℤ :=
  r64St1VecS0 ++
  (r64St1VecS1)
private theorem r64Segs_split : hm256cs0SegsR64 =
  r64Chk0 ++
  (r64Chk1) := rfl
private theorem r64Chk0_ok :
    s0RunAt 64 r64Chk0 1 0 1 [Int.ofNat wdScale] 1 64 869907 r64St0Vec = true := by
  decide +kernel
private theorem r64Chk1_ok :
    Bool.and (s0RunAt 64 r64Chk1 1 64 869907 r64St0Vec 1 64 14420055 r64St1Vec)
      (s0NatListEq (rkm128kFinalizeState (1, 64, 14420055, r64St1Vec))
        hm256cs0RowR64) = true := by
  decide +kernel
private theorem s0R64_eq :
    rkm128kEvalRowLo12 256 2 64 hm256cs0SegsR64 = hm256cs0RowR64 := by
  have hrun : rkm128kRunSegs 256 2 64 hm256cs0SegsR64 1 0 1 [Int.ofNat wdScale] =
      (1, 64, 14420055, r64St1Vec) := by
    rw [r64Segs_split]
    exact s0RunStep r64Chk0_ok
      (s0RunLast (s0AndL r64Chk1_ok))
  exact rkm128kCertRow_of_runSegs rfl hrun (s0NatListEq_eq (s0AndR r64Chk1_ok))
private def r128Chk0 : List Rkm128kSeg := [
  ⟨1, 470902, 1, 10, []⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 73 [41662694599688192, 107414]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 108 [37172289111851008, 3686149380764822]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 128 [36063981391052800, 8102251459480106, 35510]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 127 [36169534507319296, 26840275717960914, 28158]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 128 [36873221949095936, 53118714369396384, 61169]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 129 [1125899906842624, 5811608452707508, 106558]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 128 [4503599627370496, 23923809331025876, 52046]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 129 [27021597764222976, 49772076787550336, 117694]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 128 [36028797018963968, 62213788850547200, 53732]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 128 [0, 58295320905106050, 35247]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 129 [0, 21522524210778636, 102527]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 127 [0, 8892434556178448, 28854]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 129 [0, 27071029945028672, 109565]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 125 [0, 58617639738114432, 6608]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 128 [0, 48879036727722496, 33024]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 129 [0, 62617747837324288, 78689]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 127 [0, 33190365895069696, 17125]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 129 [0, 36170355751796736, 124839]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 129 [0, 38532301948289024, 103121]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 129 [0, 51399364916150272, 72661]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 128 [0, 35844380720627712, 42508]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 129 [0, 35250147702079488, 91459]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 128 [0, 26394141233512448, 63256]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 129 [0, 34238441537404928, 116820]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 129 [0, 1389674836787200, 87699]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 128 [0, 65420101179932672, 34453]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 129 [0, 10953034590846976, 81246]⟩,
  ⟨1, 470902, 1, 10, rkm128kMask56 129 [0, 66228020431552512, 121343]⟩,
  ⟨1, 477041, 1, 10, rkm128kMask56 127 [0, 39184149503803392, 21512]⟩,
  ⟨1, 477041, 1, 10, rkm128kMask56 127 [0, 12864633937330176, 25675]⟩,
  ⟨1, 477041, 1, 10, rkm128kMask56 129 [0, 28892992324501504, 100955]⟩]
private def r128St0VecS0 : List ℤ :=
  [s0P 125121527, s0P 778730301, s0P 3404998470, s0P 12077428714, s0P 36856941950,
   s0P 99942168291, s0P 245759355997, s0P 555780025660, s0P 1167850029013, s0P 2298074957266,
   s0P 4261019376794, s0P 7481675489837, s0P 12491180010372, s0P 19898547609650,
   s0P 30333452959604, s0P 44360439152089, s0P 62372117975651, s0P 84476377494166,
   s0P 110398233404715, s0P 139418739714782, s0P 170370052118513, s0P 201697333106128,
   s0P 231586163099219, s0P 258141091475940, s0P 279590014086802, s0P 294482902777664,
   s0P 301853589599265, s0P 301319798823581, s0P 293107860484492, s0P 278001901303492,
   s0P 257229836766617, s0P 232307665081132, s0P 204867883692780, s0P 176497055857922,
   s0P 148602528625795, s0P 122320679519942, s0P 98470734887020, s0P 77550829522943,
   s0P 59767697494721, s0P 45088666745289, s0P 33304336616062, s0P 24091882664308,
   s0P 17071593771334, s0P 11852250383965, s0P 8063705434413, s0P 5377163289662,
   s0P 3515025468722, s0P 2252822365467, s0P 1415826515521, s0P 872638251019, s0P 527535103264,
   s0P 312830220169, s0P 181990717944, s0P 103875181310, s0P 58174299490, s0P 31969675922,
   s0P 17240907161, s0P 9124734038, s0P 4739563500, s0P 2416188345, s0P 1208955558,
   s0P 593726431, s0P 286196887, s0P 135409311]
private def r128St0VecS1 : List ℤ :=
  [s0P 62883460, s0P 28663180, s0P 12823427, s0P 5630707, s0P 2426519, s0P 1026218, s0P 425875,
   s0P 173399, s0P 69245, s0P 27101, s0P 10380, s0P 3878, s0P 1406, s0P 485, s0P 154, s0P 41,
   s0P 7, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def r128St0VecS2 : List ℤ :=
  [s0P 0]
private def r128St0Vec : List ℤ :=
  r128St0VecS0 ++
  (r128St0VecS1 ++
  (r128St0VecS2))
private def r128Chk1 : List Rkm128kSeg := [
  ⟨1, 477041, 1, 10, rkm128kMask56 129 [0, 14406248023719936, 99607]⟩,
  ⟨1, 477041, 1, 10, rkm128kMask56 128 [0, 39696836528701440, 63776]⟩,
  ⟨1, 477041, 1, 10, rkm128kMask56 127 [0, 49279423962152960, 24761]⟩,
  ⟨1, 477041, 1, 10, rkm128kMask56 129 [0, 63101522073878528, 85977]⟩,
  ⟨1, 477041, 1, 10, rkm128kMask56 128 [0, 21270052439326720, 38987]⟩,
  ⟨1, 477041, 1, 10, rkm128kMask56 129 [0, 70410525619519488, 77106]⟩,
  ⟨1, 477041, 1, 10, rkm128kMask56 128 [0, 64682070038806528, 38388]⟩,
  ⟨1, 477041, 1, 10, rkm128kMask56 128 [1, 13950603533221888, 45817]⟩,
  ⟨1, 477041, 1, 10, rkm128kMask56 128 [1, 30434481856839680, 53642]⟩,
  ⟨1, 477041, 1, 10, rkm128kMask56 129 [4, 43980465111040000, 120924]⟩,
  ⟨1, 477041, 1, 10, rkm128kMask56 127 [9, 12807111440334848, 28255]⟩,
  ⟨1, 472944, 1, 10, rkm128kMask56 129 [15, 5348024557502464, 110712]⟩,
  ⟨1, 472944, 1, 10, rkm128kMask56 129 [59, 37717646879227904, 93594]⟩,
  ⟨1, 472944, 1, 10, rkm128kMask56 127 [143, 21392098230009856, 32429]⟩,
  ⟨1, 472944, 1, 10, rkm128kMask56 129 [892, 6755399441055744, 90393]⟩,
  ⟨1, 472944, 1, 10, rkm128kMask56 128 [1606, 9007199254740992, 32823]⟩,
  ⟨1, 472944, 1, 10, rkm128kMask56 128 [945, 18014398509481984, 56604]⟩,
  ⟨1, 472944, 1, 10, rkm128kMask56 127 [15333, 36028797018963968, 24172]⟩,
  ⟨1, 472944, 1, 10, rkm128kMask56 129 [49483, 36028797018963968, 106599]⟩,
  ⟨1, 472944, 1, 10, rkm128kMask56 128 [7050, 0, 40943]⟩,
  ⟨1, 472944, 1, 10, rkm128kMask56 129 [448397, 0, 125570]⟩,
  ⟨1, 472944, 1, 10, rkm128kMask56 128 [1281089, 0, 63236]⟩,
  ⟨1, 472944, 1, 10, rkm128kMask56 128 [7105154, 0, 46728]⟩,
  ⟨1, 471832, 1, 10, rkm128kMask56 128 [5573047, 0, 54544]⟩,
  ⟨1, 471832, 1, 10, rkm128kMask56 129 [72490406, 0, 75552]⟩,
  ⟨1, 471832, 1, 10, rkm128kMask56 127 [100999719, 0, 19488]⟩,
  ⟨1, 471832, 1, 10, rkm128kMask56 124 [1914277548, 0, 3136]⟩,
  ⟨1, 471832, 1, 10, rkm128kMask56 129 [3063550281, 0, 81024]⟩,
  ⟨1, 471832, 1, 10, rkm128kMask56 128 [4528154798, 0, 34816]⟩,
  ⟨1, 471832, 1, 10, rkm128kMask56 128 [31937471335, 0, 48384]⟩,
  ⟨1, 471832, 1, 10, rkm128kMask56 129 [626850192725, 0, 115200]⟩,
  ⟨1, 471832, 1, 10, rkm128kMask56 129 [669965047578, 0, 72192]⟩]
private def r128St1VecS0 : List ℤ :=
  [s0P 9979, s0N 17615, s0P 24486, s0N 13311, s0P 12992, s0P 25708, s0P 26218, s0P 62802,
   s0N 133435, s0N 224057, s0N 36312, s0P 102415, s0N 65362, s0N 117483, s0N 233012, s0N 135492,
   s0P 176814, s0N 10441, s0N 240676, s0P 105686, s0N 652579, s0P 237006, s0N 381592, s0P 88688,
   s0N 456884, s0N 751472, s0N 717210, s0N 540734, s0P 1418780, s0N 371139, s0P 34748,
   s0N 298460, s0N 980887, s0N 525794, s0P 369798, s0N 139302, s0N 965143, s0N 3412941,
   s0P 7096388, s0P 4408301, s0N 4530091, s0P 3422927, s0P 16224969, s0P 42195597, s0P 101530476,
   s0P 236701525, s0P 537077881, s0P 1186786090, s0P 2554673215, s0P 5358441682, s0P 10954358753,
   s0P 21831277350, s0P 42423571372, s0P 80400239698, s0P 148631164643, s0P 268064732097,
   s0P 471754710778, s0P 810221810615, s0P 1358194903443, s0P 2222517901693, s0P 3550612324358,
   s0P 5538361241185, s0P 8435679294689, s0P 12547462769598]
private def r128St1VecS1 : List ℤ :=
  [s0P 18227236436101, s0P 25860832621075, s0P 35838054737371, s0P 48511633335037,
   s0P 64144886275936, s0P 82852159647137, s0P 104538942946633, s0P 128850917388856,
   s0P 155142412493752, s0P 182474185404449, s0P 209647735196305, s0P 235278592194017,
   s0P 257904776492151, s0P 276119979615165, s0P 288715360025158, s0P 294810512145908,
   s0P 293954155412516, s0P 286178713325970, s0P 271999718456161, s0P 252359644752967,
   s0P 228524612613835, s0P 201949647087747, s0P 174132376793522, s0P 146475528927885,
   s0P 120175444067412, s0P 96148012374702, s0P 74996323947605, s0P 57017451893878,
   s0P 42240420164143, s0P 30484315410559, s0P 21424847763337, s0P 14659081294398,
   s0P 9760826554432, s0P 6322486843995, s0P 3982244229177, s0P 2437860347548, s0P 1449829474302,
   s0P 837183445385, s0P 469103631469, s0P 254910992034, s0P 134240308007, s0P 68458587410,
   s0P 33780744605, s0P 16114550576, s0P 7424160190, s0P 3299776694, s0P 1413209406,
   s0P 582411934, s0P 230623618, s0P 87597259, s0P 31853846, s0P 11065207, s0P 3662302,
   s0P 1151816, s0P 342627, s0P 97456, s0P 23684, s0N 3582, s0P 357, s0N 25, s0N 0, s0P 0, s0P 0,
   s0P 0]
private def r128St1VecS2 : List ℤ :=
  [s0P 0]
private def r128St1Vec : List ℤ :=
  r128St1VecS0 ++
  (r128St1VecS1 ++
  (r128St1VecS2))
private def r128Chk2 : List Rkm128kSeg := [
  ⟨1, 471832, 1, 10, rkm128kMask56 127 [9425263868736, 0, 23552]⟩,
  ⟨1, 471832, 1, 10, rkm128kMask56 128 [32657740233708, 0, 32768]⟩,
  ⟨1, 490659, 1, 10, rkm128kMask56 129 [403403280279911, 0, 126976]⟩,
  ⟨1, 490659, 1, 10, rkm128kMask56 129 [717107447441755, 0, 73728]⟩,
  ⟨1, 490659, 1, 10, rkm128kMask56 129 [3920814467817624, 0, 73728]⟩,
  ⟨1, 490659, 1, 10, rkm128kMask56 126 [9252045908651789, 0, 8192]⟩,
  ⟨1, 490659, 1, 10, rkm128kMask56 129 [68222068285630165, 0, 106496]⟩,
  ⟨1, 490659, 1, 10, rkm128kMask56 129 [19958792167151740, 2, 81920]⟩,
  ⟨1, 490659, 1, 10, rkm128kMask56 128 [34278525084460675, 31, 49152]⟩,
  ⟨1, 490659, 1, 10, rkm128kMask56 129 [52680803798884755, 107, 98304]⟩,
  ⟨1, 490659, 1, 10, rkm128kMask56 128 [46994380968313833, 494, 32768]⟩,
  ⟨1, 453178, 1, 10, rkm128kMask56 129 [56912568760929969, 819, 65536]⟩,
  ⟨1, 453178, 1, 10, rkm128kMask56 128 [50249594099227573, 10875, 32768]⟩,
  ⟨1, 453178, 1, 10, rkm128kMask56 128 [22335928310815609, 36896, 32768]⟩,
  ⟨1, 453178, 1, 10, rkm128kMask56 128 [64497846355428193, 115170, 32768]⟩,
  ⟨1, 453178, 1, 10, rkm128kMask56 129 [46735306740995481, 146122, 98304]⟩,
  ⟨1, 453178, 1, 10, rkm128kMask56 129 [71447193484957727, 1825659, 65536]⟩,
  ⟨1, 453178, 1, 10, rkm128kMask56 81 [44397919557108380, 25875617]⟩,
  ⟨1, 453178, 1, 10, rkm128kMask56 129 [18137230534607915, 60364090, 65536]⟩,
  ⟨1, 459005, 1, 10, rkm128kMask56 84 [45324302116986471, 261349891]⟩,
  ⟨1, 459005, 1, 10, rkm128kMask56 129 [10063142506695750, 400347416, 65536]⟩,
  ⟨1, 459004, 1, 10, rkm128kMask56 129 [42073561834165946, 1812913138, 65536]⟩,
  ⟨1, 459006, 1, 10, rkm128kMask56 129 [8401278621154954, 27699761638, 65536]⟩,
  ⟨1, 458998, 1, 10, rkm128kMask56 129 [5396308296039394, 15332018670, 65536]⟩,
  ⟨1, 459009, 1, 10, rkm128kMask56 129 [67462367076813995, 482489664578, 65536]⟩,
  ⟨1, 458974, 1, 10, rkm128kMask56 129 [33560346089587078, 1416093770792, 65536]⟩,
  ⟨1, 494119, 1, 10, rkm128kMask56 129 [15168843645420080, 5621910686709, 65536]⟩,
  ⟨1, 493817, 1, 10, rkm128kMask56 129 [26548348895323338, 33134272529936, 65536]⟩,
  ⟨1, 493798, 1, 10, rkm128kMask56 129 [59357141445525669, 76120368280876, 65536]⟩,
  ⟨1, 492887, 1, 10, rkm128kMask56 102 [47168225198111259, 43344754417745]⟩,
  ⟨1, 492878, 1, 10, rkm128kMask56 129 [33489703241601827, 1108102871613196, 65536]⟩,
  ⟨1, 511647, 1, 10, rkm128kMask56 108 [66785571926851077, 2459441452957050]⟩]
private def r128St2VecS0 : List ℤ :=
  [s0P 8856, s0N 30380, s0N 22790, s0N 3911, s0N 9724, s0N 81047, s0P 49073, s0N 237563,
   s0N 94731, s0P 189346, s0P 26062, s0N 159475, s0P 201937, s0P 53336, s0N 460964, s0P 185605,
   s0P 188557, s0N 105945, s0P 154703, s0N 208371, s0P 776002, s0N 58627, s0N 186102, s0N 945462,
   s0N 28336, s0N 2210870, s0N 1801508, s0N 436718, s0N 1285001, s0P 782728, s0P 1805703,
   s0P 1470697, s0N 258235, s0P 1869371, s0P 1158453, s0N 1169577, s0N 1184713, s0N 1970289,
   s0P 3793736, s0N 1146093, s0N 4748610, s0P 10939396, s0P 7969914, s0P 5704089, s0P 8684374,
   s0P 11138187, s0N 7860391, s0N 8570574, s0N 8144780, s0P 7571591, s0P 13881001, s0N 12378152,
   s0P 4285537, s0P 2048482, s0N 4067237, s0P 2812687, s0N 13378940, s0N 13607869, s0N 2888956,
   s0N 8998384, s0N 4223412, s0N 7752101, s0P 11657031, s0N 8215267]
private def r128St2VecS1 : List ℤ :=
  [s0N 10108644, s0N 1433039, s0P 45722128, s0N 28275770, s0P 44856995, s0P 8947887, s0P 833144,
   s0P 37181282, s0N 23638185, s0P 122973556, s0P 31029118, s0P 39513291, s0N 54457200,
   s0P 81068434, s0P 66342181, s0N 159929230, s0P 24457064, s0N 298124723, s0N 8869214,
   s0N 97842378, s0N 19766792, s0P 544277009, s0P 517787574, s0N 414102480, s0P 334946216,
   s0N 664733752, s0P 1601758788, s0P 2970480991, s0N 2115784299, s0P 692064329, s0N 920261122,
   s0N 5275973305, s0N 2560275796, s0P 5818764057, s0P 13291444325, s0N 20837301415,
   s0N 23824939537, s0N 21270833280, s0N 5149289548, s0P 47447273381, s0P 4728276728,
   s0P 215030341181, s0N 93634272858, s0P 66136643537, s0P 1465908489692, s0P 6632794409993,
   s0P 18953067508947, s0P 42942015626216, s0P 82770993686858, s0P 140108454627916,
   s0P 211870570160406, s0P 289100371893415, s0P 358089157450509, s0P 403960839586809,
   s0P 415602908006239, s0P 389828633445289, s0P 332736208125772, s0P 257507245652482,
   s0P 179669891504511, s0P 112074570559775, s0P 61721771226565, s0P 29462207874563,
   s0P 11768083605494, s0P 3897518132735]
private def r128St2VecS2 : List ℤ :=
  [s0P 104427095311]
private def r128St2Vec : List ℤ :=
  r128St2VecS0 ++
  (r128St2VecS1 ++
  (r128St2VecS2))
private def r128Chk3 : List Rkm128kSeg := [
  ⟨1, 508815, 1, 10, rkm128kMask56 105 [12853169081935991, 296518156166500]⟩,
  ⟨1, 508965, 1, 10, rkm128kMask56 111 [25685843214309055, 18381587499664046]⟩,
  ⟨1, 499421, 1, 10, rkm128kMask56 112 [63115334631142077, 63165399772997543]⟩,
  ⟨1, 537467, 1, 10, rkm128kMask56 110 [45474603493890442, 10433607549331943]⟩,
  ⟨1, 537815, 1, 10, rkm128kMask56 110 [24184576580340193, 10142523770468228]⟩,
  ⟨1, 538205, 1, 10, rkm128kMask56 116 [57565652465418591, 20712392705554744, 12]⟩,
  ⟨1, 1443922, 1, 18, rkm128kMask56 119 [11980792198689391, 12598158141896428, 100]⟩,
  ⟨1, 1190162, 1, 16, rkm128kMask56 121 [26091554351325833, 4930114363109357, 442]⟩,
  ⟨1, 1352269, 1, 18, rkm128kMask56 123 [22793353603344760, 59857009521421032, 1770]⟩,
  ⟨1, 887684, 1, 14, rkm128kMask56 124 [39427782835046753, 36645965474674370, 2178]⟩,
  ⟨1, 916272, 1, 14, rkm128kMask56 125 [48538543638840583, 64564707676470613, 4138]⟩,
  ⟨1, 626864, 1, 12, rkm128kMask56 111 [66978700649250657, 35377601592155134]⟩,
  ⟨1, 482830, 1, 10, rkm128kMask56 126 [18402541894377481, 11759968751927841, 8291]⟩,
  ⟨1, 470169, 1, 10, rkm128kMask56 119 [40533548809806217, 38359801083797610, 64]⟩,
  ⟨1, 370259, 1, 8, rkm128kMask56 126 [4824658373520394, 11923243814328194, 8218]⟩,
  ⟨1, 218357, 1, 6, rkm128kMask56 127 [10282644638009652, 51832112042516650, 16578]⟩,
  ⟨1, 226848, 1, 8, rkm128kMask56 127 [36110720433259335, 12162019318917354, 16984]⟩,
  ⟨1, 202586, 1, 6, rkm128kMask56 127 [9032506041233686, 47997273916901600, 17753]⟩,
  ⟨1, 190825, 1, 6, rkm128kMask56 127 [45071631639874057, 66295148936441616, 16459]⟩,
  ⟨1, 172248, 1, 6, rkm128kMask56 127 [11540491376112761, 11686986159491682, 17890]⟩,
  ⟨1, 147956, 1, 6, rkm128kMask56 127 [45071592996213251, 45745189871954326, 17448]⟩,
  ⟨1, 118680, 1, 6, rkm128kMask56 127 [11295575044596227, 43775202460707490, 16816]⟩,
  ⟨1, 103576, 1, 6, rkm128kMask56 127 [598134327083266, 48278810440771744, 16650]⟩,
  ⟨1, 20874, 1, 6, rkm128kMask56 123 [9042383632597826, 2961331103992354, 1344]⟩,
  ⟨1, 86944, 1, 6, rkm128kMask56 127 [36028797019701256, 47887384805025920, 18217]⟩,
  ⟨1, 102310, 1, 6, rkm128kMask56 127 [45035996408184963, 48102889085995746, 17303]⟩,
  ⟨1, 85696, 1, 6, rkm128kMask56 127 [37888, 54889006189783682, 19898]⟩,
  ⟨1, 66033, 1, 6, []⟩]
private def r128St3VecS0 : List ℤ :=
  [s0P 32239, s0N 4308, s0P 35277, s0N 63294, s0P 90106, s0P 157111, s0N 96839, s0N 109719,
   s0N 159986, s0P 26186, s0P 127995, s0P 388983, s0P 187049, s0N 280391, s0P 160385, s0N 267904,
   s0N 396480, s0P 190169, s0N 333637, s0N 296410, s0P 1355537, s0N 153367, s0N 1570127,
   s0P 1499210, s0N 574149, s0P 3368639, s0N 3292445, s0N 1429191, s0N 1340891, s0P 3776840,
   s0P 547733, s0P 1186761, s0N 479650, s0P 7133472, s0N 6273870, s0P 8353207, s0P 6244760,
   s0P 3119159, s0P 2519400, s0N 8209173, s0N 235262, s0N 13047705, s0P 1267775, s0P 2250286,
   s0P 10839918, s0N 5966719, s0N 1212076, s0N 2172753, s0N 13687127, s0N 1590768, s0P 12735509,
   s0N 16310213, s0N 3252805, s0N 13858091, s0N 15680808, s0N 18237574, s0N 14405958,
   s0N 18148602, s0P 7389778, s0N 13534482, s0N 17524816, s0P 20710141, s0N 55464809,
   s0N 16260567]
private def r128St3VecS1 : List ℤ :=
  [s0N 7431284, s0P 96840378, s0P 13761670, s0P 53772148, s0P 8793858, s0P 47158827,
   s0N 105775029, s0N 202177068, s0N 265532128, s0N 289033780, s0N 189504229, s0P 20086641,
   s0N 133385125, s0N 3271256, s0P 142454718, s0N 807645364, s0P 1278076537, s0P 2118244699,
   s0N 1729614743, s0P 245598821, s0N 330073809, s0N 1497453779, s0N 129377665, s0N 2132507699,
   s0N 2966699715, s0N 7008745537, s0N 6760020012, s0P 6238513470, s0P 5851049428,
   s0N 5473502812, s0P 2139067190, s0N 8247279325, s0N 7949697997, s0N 19172727227,
   s0P 14032293224, s0P 46589379832, s0N 55807523431, s0P 108457475097, s0P 2470212435,
   s0P 165785504465, s0P 86682378633, s0N 158105294414, s0N 51797998992, s0N 147399946033,
   s0N 220052762585, s0P 263673004194, s0P 322170642983, s0N 94157837125, s0P 426633074125,
   s0P 1191934964658, s0P 728645168528, s0N 334814061099, s0N 946367266917, s0N 47675420642,
   s0N 26043632750, s0N 642485024786, s0P 4031092020846, s0N 2781491016963, s0P 1685206497588,
   s0P 172453918135, s0P 6925114400250, s0P 5688477688301, s0N 553469375141, s0P 48519666678820]
private def r128St3VecS2 : List ℤ :=
  [s0P 998766475976745]
private def r128St3Vec : List ℤ :=
  r128St3VecS0 ++
  (r128St3VecS1 ++
  (r128St3VecS2))
private theorem r128Segs_split : hm256cs0SegsR128 =
  r128Chk0 ++
  (r128Chk1 ++
  (r128Chk2 ++
  (r128Chk3))) := rfl
private theorem r128Chk0_ok :
    s0RunAt 128 r128Chk0 1 0 1 [Int.ofNat wdScale] 1 128 11831687 r128St0Vec = true := by
  decide +kernel
private theorem r128Chk1_ok :
    s0RunAt 128 r128Chk1 1 128 11831687 r128St0Vec 1 128 29049841 r128St1Vec = true := by
  decide +kernel
private theorem r128Chk2_ok :
    s0RunAt 128 r128Chk2 1 128 29049841 r128St1Vec 1 128 49293652 r128St2Vec = true := by
  decide +kernel
private theorem r128Chk3_ok :
    Bool.and (s0RunAt 128 r128Chk3 1 128 49293652 r128St2Vec 1 128 154643197 r128St3Vec)
      (s0NatListEq (rkm128kFinalizeState (1, 128, 154643197, r128St3Vec))
        hm256cs0RowR128) = true := by
  decide +kernel
private theorem s0R128_eq :
    rkm128kEvalRowLo12 256 2 128 hm256cs0SegsR128 = hm256cs0RowR128 := by
  have hrun : rkm128kRunSegs 256 2 128 hm256cs0SegsR128 1 0 1 [Int.ofNat wdScale] =
      (1, 128, 154643197, r128St3Vec) := by
    rw [r128Segs_split]
    exact s0RunStep r128Chk0_ok
      (s0RunStep r128Chk1_ok
      (s0RunStep r128Chk2_ok
      (s0RunLast (s0AndL r128Chk3_ok))))
  exact rkm128kCertRow_of_runSegs rfl hrun (s0NatListEq_eq (s0AndR r128Chk3_ok))
/-- `RampKick128kAnchorsSound 256 2` prefix combiner across all `38` `r <= 128` anchors. -/
theorem pfxAnchorsLt256_append_sound (rest : List RampKick128kAnchor)
    (hrest : RampKick128kAnchorsSound 256 2 rest) :
    RampKick128kAnchorsSound 256 2 (pfxAnchorsLt256 ++ rest) := by
  exact
    ⟨s0ChkRow_eq
      (s0_hd s0RowChk0),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl1 s0RowChk0)),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl2 s0RowChk0)),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl1 (s0_tl2 s0RowChk0))),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl4 s0RowChk0)),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl1 (s0_tl4 s0RowChk0))),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl2 (s0_tl4 s0RowChk0))),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl1 (s0_tl2 (s0_tl4 s0RowChk0)))),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl4 (s0_tl4 s0RowChk0))),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl1 (s0_tl4 (s0_tl4 s0RowChk0)))),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl2 (s0_tl4 (s0_tl4 s0RowChk0)))),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl1 (s0_tl2 (s0_tl4 (s0_tl4 s0RowChk0))))),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl4 (s0_tl4 (s0_tl4 s0RowChk0)))),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl1 (s0_tl4 (s0_tl4 (s0_tl4 s0RowChk0))))),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl2 (s0_tl4 (s0_tl4 (s0_tl4 s0RowChk0))))),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl1 (s0_tl2 (s0_tl4 (s0_tl4 (s0_tl4 s0RowChk0)))))),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl4 (s0_tl4 (s0_tl4 (s0_tl4 s0RowChk0))))),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl1 (s0_tl4 (s0_tl4 (s0_tl4 (s0_tl4 s0RowChk0)))))),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl2 (s0_tl4 (s0_tl4 (s0_tl4 (s0_tl4 s0RowChk0)))))),
    ⟨s0ChkRow_eq
      (s0_hd s0RowChk1),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl1 s0RowChk1)),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl2 s0RowChk1)),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl1 (s0_tl2 s0RowChk1))),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl4 s0RowChk1)),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl1 (s0_tl4 s0RowChk1))),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl2 (s0_tl4 s0RowChk1))),
    ⟨s0ChkRow_eq
      (s0_hd s0RowChk2),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl1 s0RowChk2)),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl2 s0RowChk2)),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl1 (s0_tl2 s0RowChk2))),
    ⟨s0ChkRow_eq
      (s0_hd s0RowChk3),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl1 s0RowChk3)),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl2 s0RowChk3)),
    ⟨s0ChkRow_eq
      (s0_hd s0RowChk4),
    ⟨s0ChkRow_eq
      (s0_hd (s0_tl1 s0RowChk4)),
    ⟨s0R64_eq,
    ⟨s0ChkRow_eq
      (s0_hd s0RowChk5),
    ⟨s0R128_eq,
    hrest⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
/-- `RampKick128kAnchorsSound 256 2` across all `38` `r <= 128` prefix anchors. -/
theorem pfxAnchorsLt256_sound :
    RampKick128kAnchorsSound 256 2 pfxAnchorsLt256 := by
  rw [← List.append_nil pfxAnchorsLt256]
  exact pfxAnchorsLt256_append_sound [] trivial
/-- Exact `rkm128kRunSegs 256 2 256` Markovian step across `s0Segs` (`seg 0`). -/
theorem s0Segs_step :
    rkm128kRunSegs 256 2 256 s0Segs 1 0 1 [Int.ofNat wdScale] =
      (1, 256, 5948126, s0Vec) := by
  exact s0RunLast (s0_hd (s0_tl1 s0RowChk5))

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_0 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM64K128KrCert.isMidM64K128KrotovCertCell)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_1 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM16K128KrCert.isMidM16K128KrotovCertCell)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_2 : True :=
  (And.intro
    (Eq.refl
      Rk128kHiM128K128KrCert.isHiTailM128K128KrotovCertCell)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_3 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM32K512KrPt1.mm32k512krS1Segs)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_4 : True :=
  (And.intro
    (Eq.refl
      Rk128kHiM256K512KrPt0.hm256k512krS0SegsR3)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_5 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM16K512KrPt1.mm16k512krS1Segs)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_6 : True :=
  (And.intro
    (Eq.refl
      Rk128kLowM4K512L248KrPt1.lm4k512l248krS1Segs)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_7 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM16K256KrCert.isMidM16K256KrotovCertCell)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_8 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM32K512KrPt0.mm32k512krS0SegsR3)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_9 : True :=
  (And.intro
    (Eq.refl
      Rk128kHiM256K512KrPt1.hm256k512krS1Segs)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_10 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM16K512KrPt0.mm16k512krS0SegsR3)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_11 : True :=
  (And.intro
    (Eq.refl
      Rk128kHiM1024F256KrCert.isHiTailM1024Full256KrotovCertCell)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_12 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM64K256KrCert.isMidM64K256KrotovCertCell)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_13 : True :=
  (And.intro
    (Eq.refl
      Rk128kLowM4K512L248KrPt2.lm4k512l248krS2Segs)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_14 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM16K512KrPt2.mm16k512krS2Segs)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_15 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM32K512KrPt2.mm32k512krS2Segs)
    trivial).right

end
end QuantumComputation.Specs.GroverFindAll.Rk128kHiM256CoPt0
