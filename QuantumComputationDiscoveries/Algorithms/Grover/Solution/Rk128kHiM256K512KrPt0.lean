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

/-
# `(256, 512)` `RampKick128k` Krotov Part 0 (`Rk128kHiM256K512KrPt0`)

Certifies Slice 0 (`440,663` F1272 / `443,423` Horner coord-ops: all `13` low anchors
`r <= 24` plus `r = 512` segments `0..58` at `lTableMax = 4`) for `(m, k) = (256, 512)`.
-/

namespace QuantumComputation.Specs.GroverFindAll
namespace Rk128kHiM256K512KrPt0

@[expose] public section

open QuantumComputation.Specs.DickeSol

/-- Active RampKick128k segments for m = 256, r = 3 (1 segments). -/
def hm256k512krS0SegsR3 : List Rkm128kSeg := [
  ⟨1, 44919386, 1, 25, []⟩]
/-- Certified 10 ^ 12-scaled hit-probability lower bounds for m = 256, r = 3. -/
def hm256k512krS0RowR3 : List ℕ :=
  [805875207, 53487361385, 945703773552]
/-- Packaged RampKick128kAnchor for m = 256, r = 3. -/
def hm256k512krS0AncR3 : RampKick128kAnchor :=
  ⟨3, hm256k512krS0SegsR3, hm256k512krS0RowR3⟩
/-- Active RampKick128k segments for m = 256, r = 5 (2 segments). -/
def hm256k512krS0SegsR5 : List Rkm128kSeg := [
  ⟨1, 37014165, 1, 29, []⟩,
  ⟨1, 9744260, 1, 15, []⟩]
/-- Certified 10 ^ 12-scaled hit-probability lower bounds for m = 256, r = 5. -/
def hm256k512krS0RowR5 : List ℕ :=
  [1858, 34265, 201191984, 31670187391, 968128569100]
/-- Packaged RampKick128kAnchor for m = 256, r = 5. -/
def hm256k512krS0AncR5 : RampKick128kAnchor :=
  ⟨5, hm256k512krS0SegsR5, hm256k512krS0RowR5⟩
/-- Active RampKick128k segments for m = 256, r = 6 (8 segments). -/
def hm256k512krS0SegsR6 : List Rkm128kSeg := [
  ⟨1, 16831441, 1, 21, []⟩,
  ⟨1, 17069434, 1, 21, []⟩,
  ⟨1, 5713791, 1, 12, []⟩,
  ⟨1, 3094959, 1, 10, []⟩,
  ⟨1, 2264590, 1, 8, rkm128kMask56 1 [1]⟩,
  ⟨1, 1379868, 1, 8, rkm128kMask56 3 [6]⟩,
  ⟨1, 718544, 1, 6, rkm128kMask56 4 [12]⟩,
  ⟨1, 160275, 1, 4, []⟩]
/-- Certified 10 ^ 12-scaled hit-probability lower bounds for m = 256, r = 6. -/
def hm256k512krS0RowR6 : List ℕ :=
  [41, 2, 462, 93638865, 26371245839, 973535089457]
/-- Packaged RampKick128kAnchor for m = 256, r = 6. -/
def hm256k512krS0AncR6 : RampKick128kAnchor :=
  ⟨6, hm256k512krS0SegsR6, hm256k512krS0RowR6⟩
/-- Active RampKick128k segments for m = 256, r = 7 (8 segments). -/
def hm256k512krS0SegsR7 : List Rkm128kSeg := [
  ⟨1, 20902411, 1, 25, []⟩,
  ⟨1, 20967411, 1, 25, []⟩,
  ⟨1, 1904582, 1, 8, []⟩,
  ⟨1, 1333212, 1, 8, rkm128kMask56 2 [2]⟩,
  ⟨1, 597294, 1, 6, rkm128kMask56 3 [4]⟩,
  ⟨1, 711306, 1, 6, rkm128kMask56 4 [8]⟩,
  ⟨1, 778246, 1, 6, rkm128kMask56 5 [18]⟩,
  ⟨1, 389118, 1, 6, []⟩]
/-- Certified 10 ^ 12-scaled hit-probability lower bounds for m = 256, r = 7. -/
def hm256k512krS0RowR7 : List ℕ :=
  [0, 0, 0, 9546, 36217132, 22621490151, 977342251898]
/-- Packaged RampKick128kAnchor for m = 256, r = 7. -/
def hm256k512krS0AncR7 : RampKick128kAnchor :=
  ⟨7, hm256k512krS0SegsR7, hm256k512krS0RowR7⟩
/-- Active RampKick128k segments for m = 256, r = 8 (32 segments). -/
def hm256k512krS0SegsR8 : List Rkm128kSeg := [
  ⟨1, 12441876, 1, 21, []⟩,
  ⟨1, 6147863, 1, 15, []⟩,
  ⟨1, 5164425, 1, 14, []⟩,
  ⟨1, 4338553, 1, 12, []⟩,
  ⟨1, 3643887, 1, 12, []⟩,
  ⟨1, 2833993, 1, 10, []⟩,
  ⟨1, 2379542, 1, 10, []⟩,
  ⟨1, 2161857, 1, 10, []⟩,
  ⟨1, 1678628, 1, 8, []⟩,
  ⟨1, 1299917, 1, 8, []⟩,
  ⟨1, 1184402, 1, 8, []⟩,
  ⟨1, 1074249, 1, 8, []⟩,
  ⟨1, 835822, 1, 6, rkm128kMask56 3 [6]⟩,
  ⟨1, 414945, 1, 6, rkm128kMask56 4 [10]⟩,
  ⟨1, 51339, 1, 4, rkm128kMask56 4 [10]⟩,
  ⟨1, 182034, 1, 4, rkm128kMask56 4 [10]⟩,
  ⟨1, 590078, 1, 6, rkm128kMask56 5 [20]⟩,
  ⟨1, 381777, 1, 6, rkm128kMask56 5 [20]⟩,
  ⟨1, 314517, 1, 6, rkm128kMask56 6 [40]⟩,
  ⟨1, 112985, 1, 4, rkm128kMask56 6 [48]⟩,
  ⟨1, 23813, 1, 4, rkm128kMask56 1 [1]⟩,
  ⟨1, 74200, 1, 4, rkm128kMask56 6 [48]⟩,
  ⟨1, 118418, 1, 4, rkm128kMask56 6 [40]⟩,
  ⟨1, 71207, 1, 4, rkm128kMask56 6 [40]⟩,
  ⟨1, 67113, 1, 4, rkm128kMask56 6 [40]⟩,
  ⟨1, 67158, 1, 4, rkm128kMask56 5 [24]⟩,
  ⟨1, 12268, 1, 4, rkm128kMask56 6 [40]⟩,
  ⟨1, 59701, 1, 4, rkm128kMask56 6 [48]⟩,
  ⟨1, 61117, 1, 4, rkm128kMask56 6 [48]⟩,
  ⟨1, 37357, 1, 4, rkm128kMask56 6 [48]⟩,
  ⟨1, 24606, 1, 4, rkm128kMask56 6 [48]⟩,
  ⟨1, 8135, 1, 4, []⟩]
/-- Certified 10 ^ 12-scaled hit-probability lower bounds for m = 256, r = 8. -/
def hm256k512krS0RowR8 : List ℕ :=
  [0, 0, 0, 0, 27, 8478421, 19827634012, 980163849909]
/-- Packaged RampKick128kAnchor for m = 256, r = 8. -/
def hm256k512krS0AncR8 : RampKick128kAnchor :=
  ⟨8, hm256k512krS0SegsR8, hm256k512krS0RowR8⟩
/-- Active RampKick128k segments for m = 256, r = 9 (8 segments). -/
def hm256k512krS0SegsR9 : List Rkm128kSeg := [
  ⟨1, 21465057, 1, 30, []⟩,
  ⟨1, 22402660, 1, 31, []⟩,
  ⟨1, 404592, 1, 6, []⟩,
  ⟨1, 901213, 1, 8, rkm128kMask56 4 [8]⟩,
  ⟨1, 602695, 1, 6, rkm128kMask56 5 [16]⟩,
  ⟨1, 700207, 1, 6, rkm128kMask56 6 [48]⟩,
  ⟨1, 864748, 1, 8, rkm128kMask56 7 [96]⟩,
  ⟨1, 740274, 1, 6, []⟩]
/-- Certified 10 ^ 12-scaled hit-probability lower bounds for m = 256, r = 9. -/
def hm256k512krS0RowR9 : List ℕ :=
  [0, 0, 0, 1, 0, 17056, 35038, 17665990014, 982333932309]
/-- Packaged RampKick128kAnchor for m = 256, r = 9. -/
def hm256k512krS0AncR9 : RampKick128kAnchor :=
  ⟨9, hm256k512krS0SegsR9, hm256k512krS0RowR9⟩
/-- Active RampKick128k segments for m = 256, r = 10 (8 segments). -/
def hm256k512krS0SegsR10 : List Rkm128kSeg := [
  ⟨1, 21713584, 1, 31, []⟩,
  ⟨1, 22402788, 1, 33, rkm128kMask56 3 [4]⟩,
  ⟨1, 344612, 1, 6, []⟩,
  ⟨1, 721737, 1, 6, rkm128kMask56 5 [16]⟩,
  ⟨1, 636215, 1, 6, rkm128kMask56 6 [56]⟩,
  ⟨1, 698927, 1, 6, rkm128kMask56 7 [80]⟩,
  ⟨1, 887372, 1, 8, rkm128kMask56 8 [224]⟩,
  ⟨1, 864801, 1, 8, []⟩]
/-- Certified 10 ^ 12-scaled hit-probability lower bounds for m = 256, r = 10. -/
def hm256k512krS0RowR10 : List ℕ :=
  [0, 0, 1, 0, 2, 1, 2270, 5116401, 15943526708, 984051306375]
/-- Packaged RampKick128kAnchor for m = 256, r = 10. -/
def hm256k512krS0AncR10 : RampKick128kAnchor :=
  ⟨10, hm256k512krS0SegsR10, hm256k512krS0RowR10⟩
/-- Active RampKick128k segments for m = 256, r = 11 (4 segments). -/
def hm256k512krS0SegsR11 : List Rkm128kSeg := [
  ⟨1, 38693356, 2, 31, rkm128kMask56 1 [1]⟩,
  ⟨1, 173840, 1, 4, rkm128kMask56 1 [1]⟩,
  ⟨1, 9418010, 1, 21, rkm128kMask56 10 [897]⟩,
  ⟨1, 149135, 1, 4, []⟩]
/-- Certified 10 ^ 12-scaled hit-probability lower bounds for m = 256, r = 11. -/
def hm256k512krS0RowR11 : List ℕ :=
  [0, 0, 0, 0, 0, 529, 144, 4351570, 265380, 14528991532, 985466360516]
/-- Packaged RampKick128kAnchor for m = 256, r = 11. -/
def hm256k512krS0AncR11 : RampKick128kAnchor :=
  ⟨11, hm256k512krS0SegsR11, hm256k512krS0RowR11⟩
/-- Active RampKick128k segments for m = 256, r = 12 (6 segments). -/
def hm256k512krS0SegsR12 : List Rkm128kSeg := [
  ⟨1, 20386171, 1, 34, []⟩,
  ⟨1, 21888871, 1, 35, []⟩,
  ⟨1, 2085265, 1, 10, []⟩,
  ⟨1, 2369681, 1, 10, rkm128kMask56 9 [464]⟩,
  ⟨1, 1629666, 1, 10, rkm128kMask56 11 [1744]⟩,
  ⟨1, 220064, 1, 6, []⟩]
/-- Certified 10 ^ 12-scaled hit-probability lower bounds for m = 256, r = 12. -/
def hm256k512krS0RowR12 : List ℕ :=
  [0, 0, 0, 0, 4, 127, 172, 158290, 5011015, 1427268, 13356907236, 986636459414]
/-- Packaged RampKick128kAnchor for m = 256, r = 12. -/
def hm256k512krS0AncR12 : RampKick128kAnchor :=
  ⟨12, hm256k512krS0SegsR12, hm256k512krS0RowR12⟩
/-- Active RampKick128k segments for m = 256, r = 14 (8 segments). -/
def hm256k512krS0SegsR14 : List Rkm128kSeg := [
  ⟨1, 21225065, 2, 24, []⟩,
  ⟨1, 21717111, 2, 24, []⟩,
  ⟨1, 1949570, 1, 10, rkm128kMask56 8 [192]⟩,
  ⟨1, 1852722, 1, 10, rkm128kMask56 11 [1952]⟩,
  ⟨1, 793298, 1, 8, rkm128kMask56 12 [2560]⟩,
  ⟨1, 436170, 1, 6, rkm128kMask56 12 [2944]⟩,
  ⟨1, 540780, 1, 6, rkm128kMask56 13 [4384]⟩,
  ⟨1, 316199, 1, 6, []⟩]
/-- Certified 10 ^ 12-scaled hit-probability lower bounds for m = 256, r = 14. -/
def hm256k512krS0RowR14 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 31, 3, 11708, 831, 1237, 4442076, 11523501991, 988471991592]
/-- Packaged RampKick128kAnchor for m = 256, r = 14. -/
def hm256k512krS0AncR14 : RampKick128kAnchor :=
  ⟨14, hm256k512krS0SegsR14, hm256k512krS0RowR14⟩
/-- Active RampKick128k segments for m = 256, r = 16 (24 segments). -/
def hm256k512krS0SegsR16 : List Rkm128kSeg := [
  ⟨1, 2011551, 1, 10, rkm128kMask56 16 [61632]⟩,
  ⟨1, 2011338, 1, 10, rkm128kMask56 17 [85376]⟩,
  ⟨1, 2015258, 1, 10, rkm128kMask56 17 [81408]⟩,
  ⟨1, 2016479, 1, 10, rkm128kMask56 16 [34816]⟩,
  ⟨1, 2018260, 1, 10, rkm128kMask56 16 [45056]⟩,
  ⟨1, 2020571, 1, 10, rkm128kMask56 17 [114688]⟩,
  ⟨1, 2023202, 1, 10, rkm128kMask56 16 [32768]⟩,
  ⟨1, 2026186, 1, 10, []⟩,
  ⟨1, 2029454, 1, 10, []⟩,
  ⟨1, 2032958, 1, 10, []⟩,
  ⟨1, 2036641, 1, 10, []⟩,
  ⟨1, 2040444, 1, 10, []⟩,
  ⟨1, 2044301, 1, 10, []⟩,
  ⟨1, 2048147, 1, 10, []⟩,
  ⟨1, 2051916, 1, 10, []⟩,
  ⟨1, 2055541, 1, 10, []⟩,
  ⟨1, 2058957, 1, 10, []⟩,
  ⟨1, 2062101, 1, 10, []⟩,
  ⟨1, 2064916, 1, 10, []⟩,
  ⟨1, 2067350, 1, 10, rkm128kMask56 1 [1]⟩,
  ⟨1, 2069355, 1, 10, rkm128kMask56 8 [147]⟩,
  ⟨1, 2070896, 1, 10, rkm128kMask56 10 [565]⟩,
  ⟨1, 2072071, 1, 10, rkm128kMask56 13 [7431]⟩,
  ⟨1, 2090283, 1, 10, []⟩]
/-- Certified 10 ^ 12-scaled hit-probability lower bounds for m = 256, r = 16. -/
def hm256k512krS0RowR16 : List ℕ :=
  [3, 650, 1, 1344, 508, 76, 674, 332, 266, 2377, 64257, 1724690, 5571994, 220851379, 10180369298,
   989590905236]
/-- Packaged RampKick128kAnchor for m = 256, r = 16. -/
def hm256k512krS0AncR16 : RampKick128kAnchor :=
  ⟨16, hm256k512krS0SegsR16, hm256k512krS0RowR16⟩
/-- Active RampKick128k segments for m = 256, r = 20 (8 segments). -/
def hm256k512krS0SegsR20 : List Rkm128kSeg := [
  ⟨1, 20623614, 2, 28, []⟩,
  ⟨1, 22604094, 2, 31, []⟩,
  ⟨1, 1899461, 1, 12, rkm128kMask56 14 [15360]⟩,
  ⟨1, 1215708, 1, 10, rkm128kMask56 16 [52224]⟩,
  ⟨1, 1557226, 1, 10, rkm128kMask56 18 [204800]⟩,
  ⟨1, 347964, 1, 6, rkm128kMask56 15 [17664]⟩,
  ⟨1, 653437, 1, 8, rkm128kMask56 19 [285696]⟩,
  ⟨1, 511991, 1, 6, []⟩]
/-- Certified 10 ^ 12-scaled hit-probability lower bounds for m = 256, r = 20. -/
def hm256k512krS0RowR20 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 5, 42, 1490, 861078, 195543, 14197277, 8246426929,
   991738266263]
/-- Packaged RampKick128kAnchor for m = 256, r = 20. -/
def hm256k512krS0AncR20 : RampKick128kAnchor :=
  ⟨20, hm256k512krS0SegsR20, hm256k512krS0RowR20⟩
/-- Active RampKick128k segments for m = 256, r = 24 (8 segments). -/
def hm256k512krS0SegsR24 : List Rkm128kSeg := [
  ⟨1, 22784895, 2, 35, []⟩,
  ⟨1, 22503395, 2, 33, rkm128kMask56 18 [237568]⟩,
  ⟨1, 612690, 1, 8, rkm128kMask56 19 [335872]⟩,
  ⟨1, 1345713, 1, 10, rkm128kMask56 21 [1798144]⟩,
  ⟨1, 921198, 1, 8, rkm128kMask56 22 [2127872]⟩,
  ⟨1, 974485, 1, 8, rkm128kMask56 23 [4472832]⟩,
  ⟨1, 590921, 1, 8, rkm128kMask56 21 [1064960]⟩,
  ⟨2, 8, 1, 4, []⟩]
/-- Certified 10 ^ 12-scaled hit-probability lower bounds for m = 256, r = 24. -/
def hm256k512krS0RowR24 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 96, 751, 90857, 1186, 944546, 19658152,
   6996178271, 992983065020]
/-- Packaged RampKick128kAnchor for m = 256, r = 24. -/
def hm256k512krS0AncR24 : RampKick128kAnchor :=
  ⟨24, hm256k512krS0SegsR24, hm256k512krS0RowR24⟩
/-- Ordered r < 512 RampKick128kAnchor prefix (13 anchors, r <= 24). -/
def hm256k512krS0PfxAnchors : List RampKick128kAnchor :=
  [hm256k512krS0AncR3, hm256k512krS0AncR5, hm256k512krS0AncR6, hm256k512krS0AncR7,
   hm256k512krS0AncR8, hm256k512krS0AncR9, hm256k512krS0AncR10, hm256k512krS0AncR11,
   hm256k512krS0AncR12, hm256k512krS0AncR14, hm256k512krS0AncR16, hm256k512krS0AncR20,
   hm256k512krS0AncR24]
/-- Alias for hm256k512krS0PfxAnchors matching RampKick128k part convention. -/
def pfxAnchorsLt512 : List RampKick128kAnchor := hm256k512krS0PfxAnchors
/-- Unmodified segments 0..58 (59 segs) of (256, 512) r = 512 (lTableMax = 4). -/
def hm256k512krS0Segs : List Rkm128kSeg := [
  ⟨1, 615136, 1, 14, rkm128kMask56 79 [27269261063487487, 8315678]⟩,
  ⟨1, 612797, 1, 14, rkm128kMask56 156 [8850151490715647, 21590267517167884, 14799047728124]⟩,
  ⟨1, 612277, 1, 14,
    rkm128kMask56 234 [64509790293852159, 22974075336531265, 41601248604556738, 3725131446344810,
     947]⟩,
  ⟨1, 612357, 1, 14,
    rkm128kMask56 257 [2183320049811455, 65458126859290690, 9112245016171746, 49590709384241712,
     6117467335]⟩,
  ⟨1, 612438, 1, 14,
    rkm128kMask56 257 [64104796369453055, 11295079078481711, 35280425834571282, 38832685606421976,
     4539666760]⟩,
  ⟨1, 612514, 1, 14,
    rkm128kMask56 257 [59147265943535616, 50223172945936445, 57856339433749859, 19704401791974368,
     5117770321]⟩,
  ⟨1, 612650, 1, 14,
    rkm128kMask56 256 [54038797481934847, 20272328763523551, 17445489817887688, 69639213348827158,
     2527314550]⟩,
  ⟨1, 612926, 1, 15,
    rkm128kMask56 256 [140737488355328, 40604626212235268, 49303256876477637, 55124000129366129,
     3897063081]⟩,
  ⟨1, 652927, 1, 16,
    rkm128kMask56 256 [58546795155816447, 33497450163600767, 13491832071049481, 27408690338327892,
     3906488473]⟩,
  ⟨1, 652979, 1, 17,
    rkm128kMask56 256 [0, 54710445000368132, 12142577397999952, 4259400953247180, 3957381214]⟩,
  ⟨1, 652989, 1, 18,
    rkm128kMask56 256 [72057594037927935, 63098999049027199, 12410353047703931, 18224852287408450,
     3212450210]⟩,
  ⟨1, 653055, 1, 20,
    rkm128kMask56 257 [72057594037927935, 70863526557630463, 14083823749354895, 64091917951973101,
     4698127935]⟩,
  ⟨1, 653481, 1, 19,
    rkm128kMask56 257 [12, 2808702454202368, 63235546222668624, 58348767054934662, 6248593985]⟩,
  ⟨1, 653547, 1, 20,
    rkm128kMask56 257 [53, 70334041043238912, 34172408606738223, 23950318986279262, 7147935536]⟩,
  ⟨1, 653656, 1, 21,
    rkm128kMask56 257 [72057594037927727, 29189821809295359, 71628707187984022, 69776662340005391,
     6185267893]⟩,
  ⟨1, 653738, 1, 21,
    rkm128kMask56 256 [72057594037921867, 17735397433933823, 55167141188291667, 53126212981606654,
     3308328699]⟩,
  ⟨1, 654142, 1, 22,
    rkm128kMask56 257 [72057594036977741, 54113564272623615, 848410605032137, 8247645752443027,
     7679955324]⟩,
  ⟨1, 654182, 1, 22,
    rkm128kMask56 257 [16100261, 9007199254740992, 5527997419323136, 14017124639183527,
     6540171488]⟩,
  ⟨1, 654621, 1, 22,
    rkm128kMask56 257 [7768433, 0, 31682156101074968, 49356207674688817, 6235944048]⟩,
  ⟨1, 654646, 1, 22,
    rkm128kMask56 257 [72057491462627482, 72057594037927935, 71960741220971007, 25852878895428833,
     8078090307]⟩,
  ⟨1, 654736, 1, 22,
    rkm128kMask56 256 [1981491870779, 0, 7262003450281984, 66223684418601074, 2677628164]⟩,
  ⟨1, 654728, 1, 22,
    rkm128kMask56 253 [414855519114, 0, 35467891495141376, 51318106446985008, 460948508]⟩,
  ⟨1, 654550, 1, 23,
    rkm128kMask56 257 [72029885281593258, 72057594037927935, 66407202172174335, 3633650687236923,
     6459373448]⟩,
  ⟨1, 656554, 1, 23,
    rkm128kMask56 257 [33404394450264658, 72057594037927935, 13545983254200319, 17476233272770329,
     6787896366]⟩,
  ⟨1, 656664, 1, 23,
    rkm128kMask56 257 [45922944487908171, 72057594037927815, 28143099624554495, 67055996265623724,
     5504052246]⟩,
  ⟨1, 657238, 1, 24,
    rkm128kMask56 257 [70703240307068594, 6172, 35888059530608640, 30867521684853184,
     7300540732]⟩,
  ⟨1, 657239, 1, 24,
    rkm128kMask56 255 [69852906169452550, 1737809, 54043195528445952, 1326451444467231,
     1449657375]⟩,
  ⟨1, 657281, 1, 24,
    rkm128kMask56 257 [45009051726628364, 149841828, 0, 20266578624498688, 6621192987]⟩,
  ⟨1, 331008, 1, 15,
    rkm128kMask56 256 [11215842796629111, 72057590692285496, 72057594037927935, 27948013476388863,
     2281647580]⟩,
  ⟨1, 331212, 1, 15,
    rkm128kMask56 257 [44980847273517863, 72057575108508163, 72057594037927935, 13829995828413439,
     7434053506]⟩,
  ⟨1, 331238, 1, 15,
    rkm128kMask56 257 [36673940904999641, 573054589510, 0, 54120531322986496, 6155242870]⟩,
  ⟨1, 331277, 1, 16,
    rkm128kMask56 251 [47513437036547084, 5302832238743, 0, 53296327282393088, 89917378]⟩,
  ⟨1, 331212, 1, 16,
    rkm128kMask56 257 [3567380800180512, 61796109692079, 0, 22144079055814656, 5302693867]⟩,
  ⟨1, 331265, 1, 16,
    rkm128kMask56 256 [4944675592405879, 181452339681250, 0, 64481590629105664, 2296704257]⟩,
  ⟨1, 331255, 1, 15,
    rkm128kMask56 257 [21913643610816257, 64433509635192691, 72057594037927935, 48233626269122559,
     7844674290]⟩,
  ⟨1, 331339, 1, 15,
    rkm128kMask56 256 [67153634394294731, 10921983475446894, 72057594037927935, 20676436419411967,
     3819678133]⟩,
  ⟨2, 283787, 1, 20,
    rkm128kMask56 332 [32500412542553735, 5405600526971709, 72057594037927926, 32643400717041663,
     32825333497271275, 3699838513805060]⟩,
  ⟨2, 284002, 1, 20,
    rkm128kMask56 407 [35641425303444265, 59553250658276567, 72057594037927503, 9570114848423935,
     71504703354859547, 42562819052388244, 45721802708835960, 29285]⟩,
  ⟨2, 284151, 1, 20,
    rkm128kMask56 466 [36592868082851616, 36173432257839500, 23061, 43911745634304000,
     17504214875776029, 65060082473947443, 51999727228719973, 3625172760324098, 254146]⟩,
  ⟨2, 284451, 1, 21,
    rkm128kMask56 479 [17983280301053243, 50590967848189659, 72057594037592823, 35184372088831,
     11265592960500099, 61622120272405084, 23213027690728159, 41345122583061703, 1867478503]⟩,
  ⟨2, 284473, 1, 21,
    rkm128kMask56 488 [49821147200565957, 11477844382225538, 15183123, 69805794224242688,
     60183280188400415, 5084468478451309, 43502929932558564, 44661782550799026, 962369307141]⟩,
  ⟨2, 284572, 1, 21,
    rkm128kMask56 498 [43681506898719724, 7583784058814642, 328143126, 0, 7061199569096704,
     56416995072033237, 12391769067046468, 71349066690528054, 1013546454823138]⟩,
  ⟨2, 284623, 1, 21,
    rkm128kMask56 504 [24868378330389429, 33848570346039056, 9007335432, 0, 49379023991865340,
     4899624086231611, 7146419994602191, 34490983546233988, 47235881379710166]⟩,
  ⟨2, 284575, 1, 21,
    rkm128kMask56 507 [47848391906918314, 34045860645060087, 72057270060907114, 72057594037927935,
     14562215600324415, 57125810402385526, 12011190966747336, 30400494292331079,
     47193299601779464, 5]⟩,
  ⟨2, 285307, 1, 21,
    rkm128kMask56 513 [58614408024170784, 58690346063561280, 152137339661189, 0,
     68402998983784448, 48917289009534861, 45714766290033838, 37441477177506232,
     35186481061844545, 291]⟩,
  ⟨2, 285136, 1, 21,
    rkm128kMask56 510 [2409440477906432, 1647619114808418, 3373714872367408, 0, 50427163777630208,
     61323725574209612, 12069174030794228, 25299311801802294, 67203583309331628, 38]⟩,
  ⟨2, 285261, 1, 21,
    rkm128kMask56 513 [70936427550469641, 8126996844363263, 47832247080475359, 72057594037927935,
     42926516641726463, 42328527046114989, 18731908965883406, 7092892216307807, 19807749661054860,
     328]⟩,
  ⟨2, 285691, 1, 21,
    rkm128kMask56 513 [14057271558554492, 652934418293120, 32411155261741619, 60,
     28820467238305792, 9739537303794481, 55586777399188242, 15551199323389820, 68990544201813900,
     460]⟩,
  ⟨2, 285613, 1, 22,
    rkm128kMask56 513 [64536443921597579, 690382658026467, 27971497781394157, 72057594037927360,
     1125898833100799, 54413859971022238, 64420833272638491, 43142326718535022, 62703467897131320,
     414]⟩,
  ⟨2, 286271, 1, 22,
    rkm128kMask56 513 [41765490273294527, 31416851905900526, 23285812877897378, 72057594037895213,
     17179869183, 3574741141061616, 45140112008458378, 315632621455282, 9283391796912128, 386]⟩,
  ⟨2, 286280, 1, 21,
    rkm128kMask56 509 [68388841801770568, 48202590865265792, 41388714491940289, 1991918,
     72057044282114048, 17405551566651391, 12267711346880595, 54771599115680864,
     10329072663194066, 16]⟩,
  ⟨2, 286005, 1, 21,
    rkm128kMask56 513 [68505884631715980, 2023138288210576, 46564544720002138, 72057593940353087,
     8796093022207, 65283425589788672, 23685878000317617, 71461156661775538, 46240968145384722,
     390]⟩,
  ⟨2, 290140, 1, 22,
    rkm128kMask56 513 [44335560063431360, 46724536409256298, 63994883400919989, 72057593707491343,
     562949953421311, 6465128371322880, 25150810969696855, 26872280537229461, 7045257338044881,
     321]⟩,
  ⟨2, 289616, 1, 22,
    rkm128kMask56 511 [47724294692235231, 72003124713160886, 52773581019228437, 72057552284975000,
     72057594037927935, 72057594037927935, 10422024760656385, 40920415289710971,
     16901185716192992, 108]⟩,
  ⟨2, 293060, 1, 22,
    rkm128kMask56 512 [61766301644941762, 62756734779318314, 20068223997175215, 72057024736811112,
     72057594037927935, 72057594037927935, 57237185312575487, 34631064414793736, 1693882894997204,
     195]⟩,
  ⟨2, 293110, 1, 22,
    rkm128kMask56 513 [155992427877570, 21399932270674895, 43096857152390272, 97480154438796, 0,
     0, 28806868683980800, 32297083874095704, 50997646637146824, 268]⟩,
  ⟨2, 295239, 1, 22,
    rkm128kMask56 511 [51696804311696668, 48270759077332082, 55178626366621662, 66093032055717070,
     72057594037927935, 72057594037927935, 4734497069203455, 22875154745677544, 33903684632236793,
     117]⟩,
  ⟨2, 294699, 1, 22,
    rkm128kMask56 513 [16026116600868024, 16834622078677948, 55742559387860254, 10692177576985055,
     72057594037927934, 72057594037927935, 63050394783186943, 69295798585991126,
     19882495311844729, 404]⟩,
  ⟨2, 294690, 1, 22,
    rkm128kMask56 513 [17728882211018288, 72057353285369141, 68648873605723679, 68716409738664496,
     72057594037927685, 72057594037927935, 36028797018963967, 37386987781938911,
     20400024720050956, 371]⟩]
/-- Initial multiplexing level entering r = 512 segment 0 (1). -/
def hm256k512krS0LIn : ℕ := 1
/-- Initial degree cursor entering r = 512 segment 0 (0). -/
def hm256k512krS0DCurIn : ℕ := 0
/-- Initial pad accumulator entering r = 512 segment 0 (1). -/
def hm256k512krS0PadIn : ℕ := 1
/-- Initial Chebyshev state vector entering r = 512 segment 0 ([Int.ofNat wdScale]). -/
def hm256k512krS0VecIn : List ℤ := [Int.ofNat wdScale]
/-- Exact lPrev exiting segment 58 (2). -/
def hm256k512krS0LOut : ℕ := 2
/-- Exact dCur exiting segment 58 (512). -/
def hm256k512krS0DCurOut : ℕ := 512
/-- Exact pad exiting segment 58 (571733853). -/
def hm256k512krS0PadOut : ℕ := 571733853
/-- Slice 0 (64 entries) of hm256k512krS0Vec. -/
def hm256k512krS0Vec0 : List ℤ :=
  [Int.ofNat 7175496, Int.ofNat 10846536, Int.ofNat 3203560, Int.negSucc 33763892,
   Int.negSucc 101034042, Int.negSucc 36084381, Int.negSucc 61192714, Int.negSucc 38242929,
   Int.ofNat 106480546, Int.negSucc 7759191, Int.ofNat 71672427, Int.ofNat 43544362,
   Int.ofNat 68453639, Int.ofNat 43420147, Int.ofNat 8946312, Int.negSucc 70742397,
   Int.ofNat 11189797, Int.negSucc 10466110, Int.ofNat 10466938, Int.ofNat 23590142,
   Int.ofNat 106516095, Int.ofNat 140601675, Int.ofNat 257648858, Int.ofNat 139220312,
   Int.negSucc 210215025, Int.ofNat 112272907, Int.ofNat 35049437, Int.negSucc 11112532,
   Int.negSucc 231737663, Int.negSucc 435356255, Int.negSucc 19915358, Int.ofNat 83410972,
   Int.ofNat 58115044, Int.ofNat 88039033, Int.ofNat 660510425, Int.ofNat 768841882,
   Int.ofNat 352756164, Int.negSucc 541900502, Int.negSucc 854523690, Int.negSucc 1093238701,
   Int.negSucc 562460158, Int.negSucc 53266983, Int.negSucc 208024215, Int.negSucc 2151624180,
   Int.negSucc 3442063558, Int.negSucc 4920103049, Int.negSucc 3182335263, Int.negSucc 1894432439,
   Int.negSucc 4120635930, Int.ofNat 835283539, Int.ofNat 2754165832, Int.ofNat 1128505368,
   Int.negSucc 1749014360, Int.negSucc 1287387073, Int.ofNat 2742587038, Int.negSucc 661742267,
   Int.ofNat 893678752, Int.ofNat 752234303, Int.ofNat 2291773352, Int.ofNat 638918527,
   Int.ofNat 2590369775, Int.ofNat 3337330922, Int.negSucc 666329411, Int.ofNat 37084707]
/-- Slice 1 (64 entries) of hm256k512krS0Vec. -/
def hm256k512krS0Vec1 : List ℤ :=
  [Int.negSucc 6094126600, Int.negSucc 6456905602, Int.ofNat 2355023907, Int.ofNat 8003760013,
   Int.ofNat 5072620464, Int.negSucc 6530112489, Int.negSucc 1706296787, Int.negSucc 2710800098,
   Int.negSucc 7096108593, Int.negSucc 3970492890, Int.ofNat 5848498557, Int.ofNat 933324044,
   Int.ofNat 4674546808, Int.ofNat 1210419343, Int.negSucc 4889288111, Int.negSucc 220976518,
   Int.ofNat 526443361, Int.negSucc 2522594348, Int.ofNat 3861748790, Int.negSucc 232457918,
   Int.ofNat 1796477656, Int.ofNat 1465373241, Int.ofNat 494084743, Int.negSucc 4079740218,
   Int.negSucc 4092672186, Int.negSucc 1681010512, Int.ofNat 2696424981, Int.negSucc 1284639265,
   Int.negSucc 2200271164, Int.negSucc 4918973601, Int.negSucc 15917727095,
   Int.negSucc 29809378060, Int.negSucc 43283823054, Int.negSucc 47865186036,
   Int.negSucc 40662002875, Int.negSucc 32206492565, Int.negSucc 8305263191,
   Int.ofNat 16215543980, Int.ofNat 16620038402, Int.ofNat 9412190286, Int.negSucc 1602734098,
   Int.negSucc 6054371113, Int.negSucc 6114491067, Int.negSucc 4028100486, Int.negSucc 2519571606,
   Int.negSucc 916786066, Int.ofNat 1837053243, Int.negSucc 11318996919, Int.negSucc 14983836872,
   Int.negSucc 14972059452, Int.negSucc 9392985439, Int.negSucc 4290822524, Int.ofNat 13781698208,
   Int.negSucc 5284805732, Int.negSucc 9001401185, Int.ofNat 2615958760, Int.negSucc 2507054852,
   Int.ofNat 4363426619, Int.negSucc 3071326163, Int.negSucc 6942584448, Int.negSucc 4394779577,
   Int.negSucc 7258775008, Int.ofNat 15162817287, Int.ofNat 24999427980]
/-- Slice 2 (64 entries) of hm256k512krS0Vec. -/
def hm256k512krS0Vec2 : List ℤ :=
  [Int.ofNat 25411976747, Int.ofNat 19999449066, Int.ofNat 11513784830, Int.ofNat 5427671031,
   Int.ofNat 244856997, Int.ofNat 4615496435, Int.negSucc 9267432206, Int.negSucc 6218612635,
   Int.negSucc 18111287241, Int.negSucc 15526183525, Int.ofNat 619532326, Int.negSucc 1515351621,
   Int.ofNat 9790656933, Int.ofNat 7928525762, Int.negSucc 14581712488, Int.negSucc 4578556870,
   Int.negSucc 11867506343, Int.ofNat 14025298300, Int.ofNat 19782958373, Int.negSucc 6490247451,
   Int.negSucc 8265117010, Int.negSucc 10395951444, Int.negSucc 12252393981,
   Int.negSucc 11435975092, Int.negSucc 3232455810, Int.negSucc 10218888377,
   Int.negSucc 26001195587, Int.negSucc 5445139611, Int.negSucc 5075085898,
   Int.negSucc 7981292831, Int.ofNat 11172273, Int.negSucc 3370768200, Int.negSucc 21082369381,
   Int.negSucc 21939476938, Int.ofNat 14505336989, Int.negSucc 9111387147, Int.negSucc 2548068531,
   Int.negSucc 1094156249, Int.negSucc 8650196937, Int.ofNat 11448238733, Int.negSucc 4910482988,
   Int.ofNat 840766150, Int.negSucc 10829623577, Int.negSucc 12793639023, Int.ofNat 5773903804,
   Int.ofNat 10038828292, Int.ofNat 10572932069, Int.ofNat 15059433391, Int.ofNat 13504654552,
   Int.negSucc 1196061694, Int.ofNat 3898425321, Int.ofNat 4373047237, Int.ofNat 6006614412,
   Int.ofNat 4377776159, Int.ofNat 7671731172, Int.negSucc 5486308615, Int.negSucc 4388264574,
   Int.ofNat 7263093485, Int.negSucc 2534669394, Int.ofNat 11039934710, Int.negSucc 5884617909,
   Int.negSucc 19598743063, Int.negSucc 1876436224, Int.negSucc 8207293627]
/-- Slice 3 (64 entries) of hm256k512krS0Vec. -/
def hm256k512krS0Vec3 : List ℤ :=
  [Int.negSucc 5085199505, Int.ofNat 15172281425, Int.ofNat 6925812659, Int.negSucc 1281556952,
   Int.ofNat 2412172021, Int.negSucc 5216940796, Int.negSucc 6880790168, Int.negSucc 2828318253,
   Int.negSucc 4556081733, Int.negSucc 1670277689, Int.ofNat 1019496821, Int.ofNat 2360700909,
   Int.ofNat 13842050426, Int.ofNat 273940537, Int.negSucc 2015644510, Int.ofNat 6955589130,
   Int.ofNat 1717458211, Int.ofNat 12241535572, Int.negSucc 3361087930, Int.ofNat 12176676393,
   Int.ofNat 15074295547, Int.ofNat 10280299596, Int.negSucc 10202352239, Int.negSucc 11129391594,
   Int.ofNat 6741583512, Int.negSucc 5402175574, Int.ofNat 9123404042, Int.ofNat 12363385003,
   Int.ofNat 23010294201, Int.negSucc 11863589707, Int.negSucc 8169419106,
   Int.negSucc 12748376263, Int.ofNat 26405066849, Int.negSucc 8217307521, Int.negSucc 7929776623,
   Int.negSucc 6375434744, Int.ofNat 11305479124, Int.ofNat 17496961506, Int.negSucc 23836729472,
   Int.negSucc 3102859326, Int.ofNat 18600067031, Int.ofNat 42626562968, Int.ofNat 95649568921,
   Int.ofNat 145916907892, Int.ofNat 276923769009, Int.ofNat 400829354886, Int.ofNat 693988559502,
   Int.ofNat 1091771985424, Int.ofNat 1645382127350, Int.ofNat 2495910606008,
   Int.ofNat 3659385706539, Int.ofNat 5322064245438, Int.ofNat 7560776490714,
   Int.ofNat 10499721861149, Int.ofNat 14385614028872, Int.ofNat 19353039318152,
   Int.ofNat 25565202819609, Int.ofNat 33211890513612, Int.ofNat 42410651208214,
   Int.ofNat 53290480746859, Int.ofNat 65887076147675, Int.ofNat 80127747832175,
   Int.ofNat 95939559279825, Int.ofNat 113106894572205]
/-- Slice 4 (64 entries) of hm256k512krS0Vec. -/
def hm256k512krS0Vec4 : List ℤ :=
  [Int.ofNat 131261841238729, Int.ofNat 150038905853487, Int.ofNat 168971390708172,
   Int.ofNat 187434953514079, Int.ofNat 204837876554822, Int.ofNat 220650164242041,
   Int.ofNat 234286246598223, Int.ofNat 245178203543228, Int.ofNat 252923919577413,
   Int.ofNat 257276388367386, Int.ofNat 258083217756521, Int.ofNat 255314249978982,
   Int.ofNat 249102457927263, Int.ofNat 239726213901780, Int.ofNat 227577737641052,
   Int.ofNat 213145180586837, Int.ofNat 196976574106341, Int.ofNat 179627881444471,
   Int.ofNat 161637585618945, Int.ofNat 143527116778977, Int.ofNat 125782637157060,
   Int.ofNat 108811206118893, Int.ofNat 92915879443487, Int.ofNat 78312562601023,
   Int.ofNat 65154967689707, Int.ofNat 53531223604492, Int.ofNat 43444826782853,
   Int.ofNat 34818837125881, Int.ofNat 27533418055147, Int.ofNat 21467073655041,
   Int.ofNat 16510114269622, Int.ofNat 12550066573403, Int.ofNat 9453855507410,
   Int.ofNat 7068123985882, Int.ofNat 5238150259921, Int.ofNat 3830522494474,
   Int.ofNat 2745384915229, Int.ofNat 1914561981789, Int.ofNat 1291120838891,
   Int.ofNat 838330698485, Int.ofNat 522925673711, Int.ofNat 313285806933, Int.ofNat 180571135836,
   Int.ofNat 100490749976, Int.ofNat 54303352751, Int.ofNat 28718146985, Int.ofNat 15011686493,
   Int.ofNat 7843842425, Int.ofNat 4141239053, Int.ofNat 2226395117, Int.ofNat 1222037255,
   Int.ofNat 682863158, Int.ofNat 385863934, Int.ofNat 218711769, Int.ofNat 123421751,
   Int.ofNat 68929266, Int.ofNat 37934820, Int.ofNat 20512629, Int.ofNat 10877070,
   Int.ofNat 5648799, Int.ofNat 2870658, Int.ofNat 1426691, Int.ofNat 693121, Int.ofNat 329059]
/-- Slice 5 (64 entries) of hm256k512krS0Vec. -/
def hm256k512krS0Vec5 : List ℤ :=
  [Int.ofNat 152612, Int.ofNat 69123, Int.ofNat 30564, Int.ofNat 13181, Int.ofNat 5539,
   Int.ofNat 2260, Int.ofNat 891, Int.ofNat 335, Int.ofNat 117, Int.ofNat 36, Int.ofNat 8,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
/-- Slice 6 (64 entries) of hm256k512krS0Vec. -/
def hm256k512krS0Vec6 : List ℤ :=
  [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0]
/-- Slice 7 (64 entries) of hm256k512krS0Vec. -/
def hm256k512krS0Vec7 : List ℤ :=
  [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0]
/-- Slice 8 (1 entries) of hm256k512krS0Vec. -/
def hm256k512krS0Vec8 : List ℤ :=
  [Int.ofNat 0]
/-- Exact 513-entry 10 ^ 15-scaled Chebyshev vector exiting segment 58. -/
def hm256k512krS0Vec : List ℤ :=
  hm256k512krS0Vec0 ++
  (hm256k512krS0Vec1 ++
  (hm256k512krS0Vec2 ++
  (hm256k512krS0Vec3 ++
  (hm256k512krS0Vec4 ++
  (hm256k512krS0Vec5 ++
  (hm256k512krS0Vec6 ++
  (hm256k512krS0Vec7 ++
  hm256k512krS0Vec8)))))))

end

public section

open QuantumComputation.Specs.DickeSol

private abbrev s0P : ℕ → ℤ := Int.ofNat
private abbrev s0N : ℕ → ℤ := Int.negSucc
private theorem s0AndLeft {a b : Bool} (h : Bool.and a b = true) : a = true := by
  cases a with
  | false => cases h
  | true => rfl
private theorem s0AndRight {a b : Bool} (h : Bool.and a b = true) : b = true := by
  cases a with
  | false => cases h
  | true =>
    cases b with
    | false => cases h
    | true => rfl
private def s0NatEq (x y : ℕ) : Bool := Bool.and (Nat.ble x y) (Nat.ble y x)
private theorem s0Ble_le {a b : ℕ} (h : Nat.ble a b = true) : a ≤ b := by
  induction a generalizing b with
  | zero => exact Nat.zero_le _
  | succ a ih =>
    cases b with
    | zero => cases h
    | succ b => exact Nat.succ_le_succ (ih h)
private theorem s0NatEq_eq {x y : ℕ} (h : s0NatEq x y = true) : x = y :=
  Nat.le_antisymm (s0Ble_le (s0AndLeft h)) (s0Ble_le (s0AndRight h))
private def s0NatListEq (xs ys : List ℕ) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xr, y :: yr => cond (s0NatEq x y) (s0NatListEq xr yr) false
  | _, _ => false
private theorem s0NatListEq_eq {xs ys : List ℕ} (h : s0NatListEq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x _ ih =>
    cases ys with
    | nil => cases h
    | cons y _ =>
      dsimp only [s0NatListEq] at h
      cases hxy : s0NatEq x y with
      | false => rw [hxy] at h; cases h
      | true => rw [hxy] at h; exact congrArg₂ List.cons (s0NatEq_eq hxy) (ih h)
private def s0IntEq (a b : ℤ) : Bool :=
  match a, b with
  | Int.ofNat x, Int.ofNat y => s0NatEq x y
  | Int.negSucc x, Int.negSucc y => s0NatEq x y
  | _, _ => false
private theorem s0IntEq_eq {a b : ℤ} (h : s0IntEq a b = true) : a = b := by
  cases a with
  | ofNat _ =>
    cases b with
    | ofNat _ => exact congrArg Int.ofNat (s0NatEq_eq h)
    | negSucc _ => cases h
  | negSucc _ =>
    cases b with
    | ofNat _ => cases h
    | negSucc _ => exact congrArg Int.negSucc (s0NatEq_eq h)
private def s0IntListEq (xs ys : List ℤ) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xr, y :: yr => cond (s0IntEq x y) (s0IntListEq xr yr) false
  | _, _ => false
private theorem s0IntListEq_eq {xs ys : List ℤ} (h : s0IntListEq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x _ ih =>
    cases ys with
    | nil => cases h
    | cons y _ =>
      dsimp only [s0IntListEq] at h
      cases hxy : s0IntEq x y with
      | false => rw [hxy] at h; cases h
      | true => rw [hxy] at h; exact congrArg₂ List.cons (s0IntEq_eq hxy) (ih h)
private def s0AtF (bs : List Bool) : Bool :=
  match bs with
  | [] => true
  | b :: rest => cond b (s0AtF rest) false
private theorem s0_hd {b : Bool} {bs : List Bool} (h : s0AtF (b :: bs) = true) : b = true := by
  cases b with
  | false => cases h
  | true => rfl
private theorem s0_tl1 {b : Bool} {s : List Bool} (h : s0AtF (b :: s) = true) :
    s0AtF s = true := by
  cases b with
  | false => cases h
  | true => exact h
private theorem s0_tl2 {b1 b2 : Bool} {bs : List Bool}
    (h : s0AtF (b1 :: b2 :: bs) = true) : s0AtF bs = true := s0_tl1 (s0_tl1 h)
private theorem s0_tl4 {b1 b2 b3 b4 : Bool} {bs : List Bool}
    (h : s0AtF (b1 :: b2 :: b3 :: b4 :: bs) = true) : s0AtF bs = true := s0_tl2 (s0_tl2 h)
private def s0ChkRow (r : ℕ) (segs : List Rkm128kSeg) (row : List ℕ) : Bool :=
  s0NatListEq (rkm128kEvalRowLo12 256 4 r segs) row
private theorem s0ChkRow_eq {r : ℕ} {segs : List Rkm128kSeg} {row : List ℕ}
    (h : s0ChkRow r segs row = true) : rkm128kEvalRowLo12 256 4 r segs = row := s0NatListEq_eq h
private def s0StateEq (st1 st2 : ℕ × ℕ × ℕ × List ℤ) : Bool :=
  match st1, st2 with
  | (l1, d1, p1, v1), (l2, d2, p2, v2) =>
    Bool.and (s0NatEq l1 l2)
      (Bool.and (s0NatEq d1 d2) (Bool.and (s0NatEq p1 p2) (s0IntListEq v1 v2)))
private theorem s0StateEq_eq {st1 st2 : ℕ × ℕ × ℕ × List ℤ} (h : s0StateEq st1 st2 = true) :
    st1 = st2 := by
  rcases st1 with ⟨_, _, _, _⟩; rcases st2 with ⟨_, _, _, _⟩; dsimp only [s0StateEq] at h
  have h1 := s0AndLeft h; have hr1 := s0AndRight h
  have h2 := s0AndLeft hr1; have hr2 := s0AndRight hr1
  rw [s0NatEq_eq h1, s0NatEq_eq h2, s0NatEq_eq (s0AndLeft hr2), s0IntListEq_eq (s0AndRight hr2)]
private def s0RunAtEq (c : List Rkm128kSeg)
    (lI dI pI : ℕ) (vI : List ℤ) (lO dO pO : ℕ) (vO : List ℤ) : Bool :=
  s0StateEq (rkm128kRunSegs 256 4 512 c lI dI pI vI) (lO, dO, pO, vO)
private theorem s0RunStep {c rest : List Rkm128kSeg}
    {lI dI pI l1 d1 p1 : ℕ} {vI v1 : List ℤ} {stOut : ℕ × ℕ × ℕ × List ℤ}
    (h1 : s0RunAtEq c lI dI pI vI l1 d1 p1 v1 = true)
    (h2 : rkm128kRunSegs 256 4 512 rest l1 d1 p1 v1 = stOut) :
    rkm128kRunSegs 256 4 512 (c ++ rest) lI dI pI vI = stOut := by
  unfold s0RunAtEq at h1; rw [rkm128kRunSegs_append]; dsimp only
  rw [s0StateEq_eq h1]; dsimp only; exact h2
private theorem s0RunLast {c : List Rkm128kSeg}
    {lI dI pI lO dO pO : ℕ} {vI vO : List ℤ} (h : s0RunAtEq c lI dI pI vI lO dO pO vO = true) :
    rkm128kRunSegs 256 4 512 c lI dI pI vI = (lO, dO, pO, vO) := s0StateEq_eq h
private def s0Take (n : ℕ) (xs : List Rkm128kSeg) : List Rkm128kSeg :=
  match n, xs with
  | 0, _ => []
  | _ + 1, [] => []
  | k + 1, x :: xr => x :: s0Take k xr
private def s0Drop (n : ℕ) (xs : List Rkm128kSeg) : List Rkm128kSeg :=
  match n, xs with
  | 0, _ => xs
  | _ + 1, [] => []
  | k + 1, _ :: xr => s0Drop k xr
private theorem s0Take_drop (n : ℕ) (xs : List Rkm128kSeg) :
    s0Take n xs ++ s0Drop n xs = xs := by
  induction n generalizing xs with
  | zero =>
    cases xs with
    | nil => rfl
    | cons _ _ => rfl
  | succ k ih =>
    cases xs with
    | nil => rfl
    | cons x xr => exact congrArg (List.cons x) (ih xr)
private theorem s0RunStepTd {xs : List Rkm128kSeg} {n : ℕ}
    {lI dI pI l1 d1 p1 : ℕ} {vI v1 : List ℤ} {stOut : ℕ × ℕ × ℕ × List ℤ}
    (h1 : s0RunAtEq (s0Take n xs) lI dI pI vI l1 d1 p1 v1 = true)
    (h2 : rkm128kRunSegs 256 4 512 (s0Drop n xs) l1 d1 p1 v1 = stOut) :
    rkm128kRunSegs 256 4 512 xs lI dI pI vI = stOut := by
  rw [← s0Take_drop n xs]; exact s0RunStep h1 h2
private theorem s0RowChk0 : s0AtF [
    s0ChkRow 3 hm256k512krS0SegsR3 hm256k512krS0RowR3,
    s0ChkRow 5 hm256k512krS0SegsR5 hm256k512krS0RowR5,
    s0ChkRow 6 hm256k512krS0SegsR6 hm256k512krS0RowR6,
    s0ChkRow 7 hm256k512krS0SegsR7 hm256k512krS0RowR7,
    s0ChkRow 8 hm256k512krS0SegsR8 hm256k512krS0RowR8,
    s0ChkRow 9 hm256k512krS0SegsR9 hm256k512krS0RowR9,
    s0ChkRow 10 hm256k512krS0SegsR10 hm256k512krS0RowR10,
    s0ChkRow 11 hm256k512krS0SegsR11 hm256k512krS0RowR11,
    s0ChkRow 12 hm256k512krS0SegsR12 hm256k512krS0RowR12,
    s0ChkRow 14 hm256k512krS0SegsR14 hm256k512krS0RowR14,
    s0ChkRow 16 hm256k512krS0SegsR16 hm256k512krS0RowR16,
    s0ChkRow 20 hm256k512krS0SegsR20 hm256k512krS0RowR20,
    s0ChkRow 24 hm256k512krS0SegsR24 hm256k512krS0RowR24
  ] = true := by decide +kernel
private def s0Rem0 : List Rkm128kSeg := hm256k512krS0Segs
private def s0Rem1 : List Rkm128kSeg := s0Drop 10 s0Rem0
private def s0V0S0 : List ℤ :=
  [s0N 33198660125, s0N 155485098893, s0N 513370571504, s0N 1379789300905, s0N 3201886775316,
   s0N 6625533975630, s0N 12477211064979, s0N 21687470863992, s0N 35153461331728,
   s0N 53556290139445, s0N 77166567739411, s0N 105682289090511, s0N 138142452280869,
   s0N 172946909734606, s0N 207990416592569, s0N 240893417179371, s0N 269290030940651,
   s0N 291121747453804, s0N 304885023456459, s0N 309792673626156, s0N 305828151533739,
   s0N 293693151886044, s0N 274668215937803, s0N 250417968081846, s0N 222777381015159,
   s0N 193551992454571, s0N 164356876831255, s0N 136508074421275, s0N 110969090202383,
   s0N 88346855089657, s0N 68925300161685, s0N 52723135918882, s0N 39562117951499,
   s0N 29135360039236, s0N 21067764066215, s0N 14964279952706, s0N 10444916485608,
   s0N 7166830724219, s0N 4835915072463, s0N 3209947446406, s0N 2096667631905, s0N 1348040116380,
   s0N 853357545672, s0N 532045004808, s0N 326782434632, s0N 197774471642, s0N 117947609197,
   s0N 69394078800, s0N 40201383925, s0N 22998367346, s0N 12991125399, s0N 7203592162,
   s0N 3958842594, s0N 2182955985, s0N 1177963096, s0N 588384152, s0N 259416643, s0N 98967838,
   s0P 33205087, s0N 10563442, s0N 3758857, s0N 1751817, s0N 982157, s0N 542114]
private def s0V0S1 : List ℤ :=
  [s0N 274127, s0N 131834, s0N 61169, s0N 26045, s0N 9961, s0P 3551, s0N 1194, s0N 370, s0N 107,
   s0N 28, s0N 6, s0N 0, s0P 1, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0]
private def s0V0S2 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V0 : List ℤ :=
  s0V0S0 ++
  (s0V0S1 ++
  s0V0S2)
private def s0Rem2 : List Rkm128kSeg := s0Drop 7 s0Rem1
private def s0V1S0 : List ℤ :=
  [s0P 229434242, s0N 184271774, s0N 522814913, s0N 2072360446, s0P 849600587, s0N 33476689,
   s0P 467470103, s0N 524485557, s0P 320897695, s0N 936128746, s0P 1201787203, s0N 840287598,
   s0N 883532694, s0P 651131829, s0P 1170689037, s0N 366462385, s0P 1097390148, s0N 3369645605,
   s0N 7172210081, s0N 14028400682, s0P 26367029484, s0P 48075433669, s0P 85306094702,
   s0P 147573994885, s0P 248951514386, s0P 410174016427, s0P 660268436989, s0P 1039368354069,
   s0P 1601123816383, s0P 2414917870998, s0P 3568634668061, s0P 5169291113199, s0P 7344021022317,
   s0P 10237562775196, s0P 14009648126080, s0P 18827953123054, s0P 24859752126334,
   s0P 32260565320131, s0P 41160399992160, s0P 51649640530616, s0P 63763322965320,
   s0P 77467674965506, s0P 92648997072001, s0P 109106071352680, s0P 126548167779390,
   s0P 144600359341036, s0P 162813517674161, s0P 180682323296643, s0P 197668697096579,
   s0P 213228619566644, s0P 226841599749809, s0P 238040413545027, s0P 246437417679291,
   s0P 251747517358674, s0P 253803038286536, s0P 252563471032490, s0P 248114061441085,
   s0P 240659154943961, s0P 230506948124650, s0P 218049130305775, s0P 203736848095742,
   s0P 188054182776310, s0P 171492884891857, s0P 154528993915169]
private def s0V1S1 : List ℤ :=
  [s0P 137600863615607, s0P 121095116392838, s0P 105334374230145, s0P 90572407671865,
   s0P 76991755312916, s0P 64707499316260, s0P 53773397884383, s0P 44189308786011,
   s0P 35912064421227, s0P 28865292403685, s0P 22948233165228, s0P 18046671704801,
   s0P 14039346768098, s0P 10805506811196, s0P 8227887388274, s0P 6199184027540,
   s0P 4621770204287, s0P 3409481306514, s0P 2489225760841, s0P 1798731565168, s0P 1286276055629,
   s0P 910510507662, s0P 637904325073, s0P 442505385633, s0P 303395424459, s0P 206650712308,
   s0P 138830994163, s0P 92406856487, s0P 61109155165, s0P 39819117637, s0P 25733822149,
   s0P 16820802164, s0P 10948852576, s0P 6689162781, s0P 3616782584, s0P 1669177444,
   s0P 643574952, s0P 200424885, s0N 44011644, s0N 376086, s0P 7925742, s0P 7755241, s0P 6027867,
   s0P 4071316, s0P 2336898, s0P 1115994, s0N 433278, s0N 126137, s0N 17311, s0N 8090, s0N 7475,
   s0P 3314, s0N 1043, s0N 313, s0P 131, s0P 69, s0N 30, s0P 10, s0N 1, s0P 1, s0N 1, s0P 1,
   s0P 0, s0P 0]
private def s0V1S2 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V1S3 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V1S4 : List ℤ :=
  [s0P 0]
private def s0V1 : List ℤ :=
  s0V1S0 ++
  (s0V1S1 ++
  (s0V1S2 ++
  (s0V1S3 ++
  s0V1S4)))
private def s0Rem3 : List Rkm128kSeg := s0Drop 6 s0Rem2
private def s0V2S0 : List ℤ :=
  [s0N 248867162, s0N 17044266, s0N 127484435, s0N 834740436, s0N 554216697, s0N 92089806,
   s0P 994716865, s0P 1589709148, s0P 2525714414, s0P 2360383113, s0P 265456194, s0N 1142310546,
   s0N 3180120151, s0P 1191767801, s0P 2392608475, s0N 314142296, s0N 1040592459, s0N 2327295676,
   s0N 3405905403, s0N 3352251745, s0N 537913171, s0N 7919651408, s0N 1133224377, s0N 560394790,
   s0N 10907122240, s0P 1666979273, s0N 3485536786, s0N 8721495436, s0P 1148591849, s0N 337813119,
   s0N 2432960025, s0P 9724762236, s0N 21217637167, s0N 7626560420, s0N 11104109131,
   s0P 1795311310, s0P 46662294849, s0P 24647617854, s0P 38651122831, s0P 44297930818,
   s0N 17320960430, s0P 4682371790, s0P 20485975, s0P 6979740341, s0P 7789141395, s0P 4133831761,
   s0P 19484884354, s0P 25744862969, s0P 20397956201, s0P 10198003688, s0P 3418665958,
   s0P 5780982931, s0P 17617328951, s0P 40016955965, s0P 72998596688, s0P 120759850611,
   s0P 188753079727, s0P 285949012624, s0P 425238762283, s0P 622314147198, s0P 898382973646,
   s0P 1280265336460, s0P 1801861498684, s0P 2504766001781]
private def s0V2S1 : List ℤ :=
  [s0P 3438809759040, s0P 4664597200482, s0P 6251547641533, s0P 8278299264992, s0P 10833163484757,
   s0P 14010862633793, s0P 17909654463499, s0P 22629650389681, s0P 28266748361980,
   s0P 34906209709382, s0P 42618540976445, s0P 51451550494097, s0P 61422924712049,
   s0P 72514415044475, s0P 84666706380863, s0P 97773282184389, s0P 111680091611454,
   s0P 126184363432283, s0P 141037770175833, s0P 155951245021597, s0P 170604115008727,
   s0P 184655051056932, s0P 197753981902916, s0P 209557094382474, s0P 219742495498894,
   s0P 228023151352800, s0P 234162286692259, s0P 237982545179854, s0P 239376930834519,
   s0P 238311328674187, s0P 234827264792910, s0P 229038966129686, s0P 221127203915778,
   s0P 211330488315494, s0P 199931859433139, s0P 187246856071916, s0P 173609945616662,
   s0P 159357108086633, s0P 144816700596072, s0P 130294239396737, s0P 116065996747562,
   s0P 102367803330496, s0P 89395179379144, s0P 77297188783637, s0P 66178508608959,
   s0P 56103571569808, s0P 47096435182211, s0P 39148197986565, s0P 32223600052219,
   s0P 26265065752640, s0P 21199426223904, s0P 16944744053915, s0P 13412234612903,
   s0P 10513161682210, s0P 8160396104501, s0P 6272911274475, s0P 4775276376401, s0P 3599854542490,
   s0P 2687995036711, s0P 1987835760546, s0P 1455331822070, s0P 1054931792412, s0P 757464358600,
   s0P 538660588276]
private def s0V2S2 : List ℤ :=
  [s0P 379534340999, s0P 264658023869, s0P 183070264105, s0P 125130261269, s0P 84918776681,
   s0P 57449055101, s0P 38307169904, s0P 25022967557, s0P 16001105098, s0P 9810984760,
   s0P 5545123876, s0P 2790681843, s0P 1228401394, s0N 472592118, s0N 161934839, s0P 52633937,
   s0P 18810627, s0P 8702494, s0P 5158244, s0P 3415956, s0P 2233731, s0P 1328751, s0P 686986,
   s0P 301605, s0N 110525, s0N 32935, s0P 7515, s0P 1088, s0P 2, s0N 45, s0N 6, s0P 6, s0P 3,
   s0P 2, s0N 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V2S3 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V2S4 : List ℤ :=
  [s0P 0]
private def s0V2 : List ℤ :=
  s0V2S0 ++
  (s0V2S1 ++
  (s0V2S2 ++
  (s0V2S3 ++
  s0V2S4)))
private def s0Rem4 : List Rkm128kSeg := s0Drop 7 s0Rem3
private def s0V3S0 : List ℤ :=
  [s0P 32480943, s0P 171405189, s0P 233412523, s0N 130998609, s0P 575364059, s0P 727622254,
   s0N 443577492, s0N 771190589, s0N 855992283, s0P 1222525924, s0N 251578527, s0N 807415495,
   s0N 946422532, s0N 1177860645, s0N 33900218, s0N 413889528, s0P 219359338, s0N 1054480017,
   s0N 588932134, s0N 2919355236, s0N 1965336982, s0N 5093880972, s0N 10614964109, s0N 3925177433,
   s0P 6423031664, s0P 4871086887, s0P 2373957116, s0P 25418263719, s0P 10377999498,
   s0P 3057343514, s0P 6687832631, s0N 10776248906, s0P 14147632835, s0P 21775952004,
   s0P 27498449591, s0P 10240072629, s0P 10335397639, s0P 4308496885, s0P 3234700332,
   s0N 1815439090, s0N 16230863583, s0P 18040927981, s0N 14903406438, s0P 7520951867,
   s0N 8919323543, s0P 17075134298, s0N 12696345600, s0N 6864738758, s0N 20369277684,
   s0N 18679156004, s0N 17455367690, s0P 44703409359, s0N 11433012460, s0N 3356686993,
   s0N 17575760178, s0P 23414882233, s0P 11591159893, s0P 16688769407, s0P 5582953406,
   s0N 6119081035, s0N 8971606180, s0N 5156823929, s0N 6707110985, s0N 5046762319]
private def s0V3S1 : List ℤ :=
  [s0N 1844423954, s0P 4953840825, s0N 5949803047, s0P 7681876651, s0P 6183407815, s0N 1363111245,
   s0P 1118273507, s0N 9847658728, s0N 1107628769, s0P 4061863480, s0N 6981581531, s0P 3225348285,
   s0P 5051960600, s0N 1617963018, s0P 5131884796, s0P 5150863103, s0N 2019375266, s0N 5340790700,
   s0N 1827598956, s0P 4657346455, s0P 14255470508, s0P 8985261275, s0P 918607711, s0N 1480397349,
   s0N 13273725591, s0N 13686080972, s0P 937816853, s0P 17056061220, s0P 38982106832,
   s0P 67290087090, s0P 106650142480, s0P 162391477148, s0P 242196506462, s0P 355708319652,
   s0P 515082080544, s0P 737247209730, s0P 1043411565491, s0P 1459560080265, s0P 2020408311926,
   s0P 2765760453188, s0P 3745408332411, s0P 5016816454253, s0P 6648475096182, s0P 8715995238193,
   s0P 11304026425055, s0P 14504491048281, s0P 18412571015933, s0P 23125418890248,
   s0P 28736171480222, s0P 35330159763322, s0P 42977881296546, s0P 51728544521273,
   s0P 61605052670340, s0P 72594398047188, s0P 84643531956281, s0P 97656405592722,
   s0P 111487328606124, s0P 125941690270191, s0P 140779581010268, s0P 155718014495441,
   s0P 170438886398749, s0P 184600815627903, s0P 197849174808058, s0P 209832413898238]
private def s0V3S2 : List ℤ :=
  [s0P 220215950324861, s0P 228699999594306, s0P 235028876126106, s0P 239011339901976,
   s0P 240521188846584, s0P 239512004019033, s0P 236013473721531, s0P 230134215097351,
   s0P 222054826211016, s0P 212015134228367, s0P 200309763851073, s0P 187265877616178,
   s0P 173234843301106, s0P 158570915990372, s0P 143624596603481, s0P 128715118839274,
   s0P 114139364635242, s0P 100144888159769, s0P 86936735884309, s0P 74673790109765,
   s0P 63459249536396, s0P 53355741250973, s0P 44384264614662, s0P 36526767235200,
   s0P 29739241054859, s0P 23954263120309, s0P 19086507321323, s0P 15044530833712,
   s0P 11731500361794, s0P 9048887132433, s0P 6902949267961, s0P 5209246956948, s0P 3889189099317,
   s0P 2871150500050, s0P 2095376271207, s0P 1512629468867, s0P 1080654809734, s0P 763679487361,
   s0P 533217748990, s0P 367745703519, s0P 251060024888, s0P 170282727704, s0P 114770854874,
   s0P 76262050470, s0P 49184415460, s0P 30279243861, s0P 17550203998, s0P 9530960491,
   s0P 4856784537, s0P 2336979766, s0N 1088014237, s0N 502979437, s0N 236058083, s0N 105363013,
   s0N 40661923, s0N 12924420, s0P 3346888, s0N 699748, s0N 108663, s0P 4877, s0N 5372, s0P 2999,
   s0P 1085, s0N 320]
private def s0V3S3 : List ℤ :=
  [s0P 85, s0P 19, s0N 3, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V3S4 : List ℤ :=
  [s0P 0]
private def s0V3 : List ℤ :=
  s0V3S0 ++
  (s0V3S1 ++
  (s0V3S2 ++
  (s0V3S3 ++
  s0V3S4)))
private def s0Rem5 : List Rkm128kSeg := s0Drop 7 s0Rem4
private def s0V4S0 : List ℤ :=
  [s0P 15657278, s0N 88278517, s0N 53752035, s0P 83412767, s0P 46473603, s0P 149124985,
   s0P 409608378, s0N 356114063, s0N 1437567104, s0P 412923651, s0P 417402737, s0P 168915770,
   s0N 72615111, s0P 2014219758, s0P 446758051, s0N 945338276, s0N 652574925, s0P 715213457,
   s0N 683022744, s0P 886328952, s0P 587449208, s0N 2078347723, s0P 624558238, s0N 366634504,
   s0P 831012348, s0N 623497427, s0N 476981214, s0P 1883664949, s0P 422403577, s0P 3435882030,
   s0P 7427602897, s0P 9393871308, s0P 3820334659, s0P 6014474243, s0N 4555151115, s0N 4218988752,
   s0P 10180464271, s0P 25327344803, s0P 23350094388, s0P 9637718972, s0N 18028160984,
   s0N 14617915953, s0N 22478165191, s0P 16248354529, s0P 24321787207, s0N 21556720290,
   s0N 26790279941, s0P 2594074731, s0N 21479529750, s0P 32811641580, s0P 555348483,
   s0P 15012843501, s0N 5593053739, s0N 13378197170, s0N 24141883992, s0P 19766289328,
   s0P 8360872010, s0N 7067199031, s0N 2631025934, s0P 5526667738, s0P 1945969505,
   s0P 17068899662, s0N 19649016779, s0N 14912567442]
private def s0V4S1 : List ℤ :=
  [s0P 18048563724, s0N 8992399989, s0N 3921515779, s0N 3590601528, s0N 2155700507,
   s0P 5718720153, s0P 4862938396, s0N 5898334596, s0P 6078831827, s0N 2188534591, s0N 8381850912,
   s0N 824239281, s0N 5145170889, s0N 705549110, s0P 5416692086, s0N 4223487663, s0N 6570189073,
   s0N 2905753269, s0P 12141744128, s0N 12178561060, s0N 843351834, s0P 3467020851,
   s0N 4132328662, s0N 15815257407, s0N 16069391396, s0N 16958168390, s0N 9134052248,
   s0N 7675858375, s0P 6069536911, s0N 5363098521, s0P 1574237343, s0P 4439326307, s0N 226552845,
   s0N 18285018380, s0P 8916459330, s0N 21184888355, s0N 5328738660, s0P 21534600220,
   s0N 6540698843, s0P 10430090022, s0P 9223449196, s0P 17236041109, s0P 11735278026,
   s0P 3074864230, s0N 3037044734, s0P 1753748492, s0N 9379746105, s0N 10771497937,
   s0N 3546636822, s0P 1825068036, s0P 2823314183, s0N 2483632665, s0N 5657367607,
   s0N 19562062138, s0N 42501219614, s0N 73601513905, s0N 119408090979, s0N 183329116457,
   s0N 276047328528, s0N 408243876956, s0N 594418560521, s0N 857197413138, s0N 1218556800060,
   s0N 1713902466448]
private def s0V4S2 : List ℤ :=
  [s0N 2384057092076, s0N 3276145423774, s0N 4453103876778, s0N 5984124061846, s0N 7949346005134,
   s0N 10443043434580, s0N 13563273827567, s0N 17417513033712, s0N 22116606930167,
   s0N 27766529689367, s0N 34468496769912, s0N 42308802508173, s0N 51348836487776,
   s0N 61621034411651, s0N 73119205871662, s0N 85788801233706, s0N 99524368005273,
   s0N 114164742715347, s0N 129488682780264, s0N 145219997592701, s0N 161033790636966,
   s0N 176563063943222, s0N 191413153286392, s0N 205178429497956, s0N 217456699501408,
   s0N 227871489784213, s0N 236091403044226, s0N 241847459814921, s0N 244941209254051,
   s0N 245266579416594, s0N 242807573519301, s0N 237646239233349, s0N 229948598513597,
   s0N 219965708071280, s0N 208016971994432, s0N 194468171847603, s0N 179719978278696,
   s0N 164183216685266, s0N 148264222739021, s0N 132346654636788, s0N 116772643759872,
   s0N 101836579801848, s0N 87779803113217, s0N 74782864144295, s0N 62965964601565,
   s0N 52395125535735, s0N 43086547909766, s0N 35013577759457, s0N 28116963910305,
   s0N 22311929117189, s0N 17494596645392, s0N 13552241742139, s0N 10371966864603,
   s0N 7843359561957, s0N 5860186576598, s0N 4324781368150, s0N 3151881325820, s0N 2268680796615,
   s0N 1613141878672, s0N 1133165510066, s0N 786382230559, s0N 539298173109, s0N 365661520523,
   s0N 245023650898]
private def s0V4S3 : List ℤ :=
  [s0N 161811201400, s0N 104773398711, s0N 66049510688, s0N 40260032162, s0N 23610978771,
   s0N 13280665716, s0N 7159754112, s0N 3710703467, s0N 1859654532, s0N 903040197, s0N 421579034,
   s0N 186356141, s0N 76745015, s0N 29036519, s0N 9979983, s0N 3089047, s0P 856191, s0P 212233,
   s0P 47343, s0N 9700, s0N 1912, s0N 387, s0N 83, s0N 17, s0N 2, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V4S4 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V4 : List ℤ :=
  s0V4S0 ++
  (s0V4S1 ++
  (s0V4S2 ++
  (s0V4S3 ++
  s0V4S4)))
private def s0Rem6 : List Rkm128kSeg := s0Drop 3 s0Rem5
private def s0V5S0 : List ℤ :=
  [s0P 27927379, s0N 10245156, s0N 47037570, s0P 98204046, s0P 55911458, s0N 106495795,
   s0N 533790515, s0P 77149760, s0P 24495694, s0P 534307199, s0P 1463321215, s0N 994239330,
   s0P 714678843, s0P 792895098, s0P 217870529, s0P 1513435169, s0N 161931222, s0P 2149527154,
   s0N 589437079, s0P 267566760, s0P 759391883, s0P 774704697, s0N 1584215585, s0N 152450550,
   s0P 941323987, s0P 3471097995, s0P 2145531871, s0P 865968559, s0P 2895029612, s0N 1585482450,
   s0P 88569078, s0P 2085206422, s0P 942274534, s0N 726314561, s0N 1491476229, s0N 1860695919,
   s0N 3938039753, s0N 3542034223, s0P 313988555, s0P 18030942097, s0P 10226272006,
   s0N 3861249256, s0N 4777669324, s0P 4472150061, s0P 6812016750, s0P 12685308182,
   s0P 33903281726, s0P 33778515908, s0P 19980584505, s0N 3426690659, s0N 45392809186,
   s0N 24043165515, s0N 15195857535, s0N 10556193947, s0N 11279145389, s0N 1737604378,
   s0N 20056193452, s0N 21679485689, s0P 861007583, s0P 18896818155, s0P 7013164386,
   s0N 16411395458, s0N 6284939581, s0P 2731621077]
private def s0V5S1 : List ℤ :=
  [s0P 5833731580, s0N 11442470232, s0N 11006750978, s0N 13651007728, s0P 3541878331,
   s0P 18781577704, s0N 12391811004, s0N 5497954892, s0P 7756741524, s0P 11458848908,
   s0N 2604734648, s0P 4159848908, s0P 1773792029, s0N 5101066983, s0P 13487444076,
   s0P 2701506384, s0P 4868318587, s0P 1528799059, s0N 3106347598, s0P 6077430239, s0P 4672983986,
   s0P 5191313666, s0N 2593766487, s0P 1363624120, s0N 9910981793, s0N 11024208279,
   s0N 7090847533, s0N 27402136141, s0N 13999719647, s0N 13058595222, s0P 1356745730,
   s0P 17479758119, s0P 2704455218, s0N 2426566659, s0P 7272136554, s0P 2002921789,
   s0P 1471352842, s0N 21936456456, s0N 8973040048, s0P 11410052252, s0P 2724528399,
   s0P 9054466477, s0N 11870438289, s0N 5710142087, s0P 11115029800, s0P 14203482110,
   s0N 458752212, s0P 10633037525, s0N 6168513866, s0P 4801209783, s0P 7204863863, s0N 81342279,
   s0N 4730110121, s0N 3282368715, s0P 2007409716, s0P 1939452864, s0P 1405596542, s0N 7482478772,
   s0N 310968206, s0P 9723471455, s0N 610179675, s0P 4592011558, s0N 4690376617, s0N 6526767831]
private def s0V5S2 : List ℤ :=
  [s0N 1877083980, s0P 8222169558, s0N 5622657813, s0N 3595794963, s0N 17791003090,
   s0N 38573486328, s0N 67296282136, s0N 108093953396, s0N 167777615621, s0N 253805501416,
   s0N 376018492198, s0N 551024851991, s0N 796273892924, s0N 1137328049036, s0N 1604535725588,
   s0N 2239270573553, s0N 3086698242065, s0N 4207987107022, s0N 5671120568042, s0N 7555073781463,
   s0N 9951106812028, s0N 12957292642458, s0N 16681127909279, s0N 21230931390984,
   s0N 26716715250071, s0N 33240660738428, s0N 40888088907317, s0N 49727523652081,
   s0N 59797581285405, s0N 71095741966826, s0N 83575471916282, s0N 97139408596753,
   s0N 111634153510513, s0N 126848859364422, s0N 142515266602663, s0N 158314764634543,
   s0N 173888803932720, s0N 188847468959414, s0N 202784873578366, s0N 215301018316477,
   s0N 226018986710983, s0N 234600176332526, s0N 240764334372397, s0N 244306795260723,
   s0N 245107655739366, s0N 243137789915050, s0N 238461829021721, s0N 231234214003710,
   s0N 221690296748349, s0N 210135047723346, s0N 196926669661097, s0N 182456285041173,
   s0N 167129128888368, s0N 151348459262327, s0N 135498350169817, s0N 119926513186306,
   s0N 104932491507411, s0N 90762304253179, s0N 77606025434464, s0N 65595966062446,
   s0N 54808099752796, s0N 45266637718337, s0N 36955272008138, s0N 29818682319632]
private def s0V5S3 : List ℤ :=
  [s0N 23785945889637, s0N 18746014100082, s0N 14614118190254, s0N 11244952933466,
   s0N 8565623306129, s0N 6440219853508, s0N 4782288324251, s0N 3518198454478, s0N 2552864467349,
   s0N 1822872549386, s0N 1301412621742, s0N 907877422762, s0N 632838228866, s0N 430109410592,
   s0N 283347594819, s0N 197953696501, s0N 139467076531, s0N 84084885025, s0N 39340764445,
   s0N 13952123551, s0N 4192876680, s0P 1853260629, s0P 1528424524, s0P 1324368766, s0P 974618161,
   s0P 620291605, s0P 358838422, s0P 193022911, s0P 94596161, s0P 40358913, s0P 14264238,
   s0P 3941207, s0N 752148, s0N 44875, s0N 34596, s0N 18674, s0N 6259, s0N 1788, s0N 503, s0P 155,
   s0P 49, s0N 11, s0N 3, s0P 2, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V5S4 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V5S5 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V5 : List ℤ :=
  s0V5S0 ++
  (s0V5S1 ++
  (s0V5S2 ++
  (s0V5S3 ++
  (s0V5S4 ++
  s0V5S5))))
private def s0Rem7 : List Rkm128kSeg := s0Drop 3 s0Rem6
private def s0V6S0 : List ℤ :=
  [s0P 25950241, s0N 4143418, s0P 19761325, s0N 61648125, s0P 61610833, s0P 82081805,
   s0P 108280344, s0P 291800545, s0P 292738612, s0P 381141765, s0N 467290717, s0N 1163635716,
   s0N 982711954, s0P 421946339, s0P 1670604746, s0P 1445413202, s0P 130167312, s0N 471294502,
   s0P 1292505914, s0P 1231963381, s0P 577328915, s0N 13854856, s0N 1917481854, s0P 285730353,
   s0N 1067537594, s0N 1362322184, s0P 2701410984, s0N 822830351, s0N 1533774578, s0P 3808979992,
   s0P 1864166679, s0P 114635620, s0P 1125719225, s0P 874338253, s0P 349397689, s0N 454333373,
   s0P 794195334, s0N 510113802, s0P 89632042, s0P 2420214505, s0P 7248242756, s0P 11809922684,
   s0P 15842506469, s0P 15108735389, s0P 8128149515, s0P 8582998149, s0P 6918928910,
   s0P 450311882, s0N 7921150392, s0N 4304584017, s0N 285899339, s0N 5838612584, s0N 10959863714,
   s0N 57285663100, s0P 28277576962, s0P 13612227840, s0P 12972338122, s0P 35841068957,
   s0N 1151585825, s0P 28615246642, s0P 11459504094, s0P 5661928757, s0P 15232217512,
   s0N 14393251818]
private def s0V6S1 : List ℤ :=
  [s0P 2743278393, s0P 10499491008, s0N 189763244, s0N 4611703008, s0P 18545215175,
   s0P 1491290722, s0P 7568046016, s0N 6857874169, s0N 1742695046, s0P 7905782282,
   s0P 14590956233, s0P 7483138015, s0N 2642221994, s0N 2683995690, s0N 18970674041,
   s0P 9292748175, s0P 2999503089, s0N 1557255757, s0N 2910858593, s0P 1365448071, s0N 9112329145,
   s0P 4739080518, s0N 1385406514, s0P 7610300428, s0P 4662921748, s0P 5835032581, s0P 6621488340,
   s0P 2883278631, s0P 8834414022, s0P 583895276, s0P 5762115549, s0P 15432026983, s0P 4009154228,
   s0P 12268004146, s0P 25063864549, s0P 23203743210, s0P 7642117210, s0N 9312890635,
   s0P 8125191021, s0N 7629997964, s0N 2549987276, s0N 14507218143, s0P 6129183662,
   s0N 1817657253, s0P 2431545535, s0P 4054659651, s0N 9107427561, s0N 4283575647, s0P 1379845976,
   s0N 10932300365, s0N 17810838196, s0P 9584710639, s0N 8783173509, s0N 9211459594,
   s0N 4696208317, s0P 2752615735, s0N 11798054319, s0P 95616796, s0N 2460036195, s0P 4943371259,
   s0P 2592865479, s0P 3886907906, s0P 2880055067, s0P 1241160844]
private def s0V6S2 : List ℤ :=
  [s0P 324684218, s0P 5748243677, s0P 1923503868, s0N 7723849073, s0N 3399666176, s0N 6200093223,
   s0N 5139565705, s0N 5412990333, s0P 1175536001, s0N 1802791565, s0N 582922798, s0N 976733634,
   s0N 1099913719, s0P 109551303, s0P 601450321, s0P 2195331006, s0P 2455424142, s0N 1131996967,
   s0N 3913326575, s0N 14497487868, s0N 29911308780, s0N 52662723327, s0N 87283438998,
   s0N 137318010407, s0N 209725464432, s0N 315558077366, s0N 467519523973, s0N 682273784718,
   s0N 982862476996, s0N 1399221492809, s0N 1969162894907, s0N 2738180936148, s0N 3760859015666,
   s0N 5104867731903, s0N 6849930497006, s0N 9083979188991, s0N 11904501727328,
   s0N 15419660414275, s0N 19742060270970, s0N 24982511691989, s0N 31247484356201,
   s0N 38632902058442, s0N 47213840243266, s0N 57035703713396, s0N 68108594350596,
   s0N 80397091911477, s0N 93816114546034, s0N 108219280125223, s0N 123409721493744,
   s0N 139117851732345, s0N 155043477597517, s0N 170809604875334, s0N 186050451739924,
   s0N 200327016219357, s0N 213258138738901, s0N 224431534923532, s0N 233509207260703,
   s0N 240197731614442, s0N 244264245515654, s0N 245579803737198, s0N 244107489483015,
   s0N 239873313863391, s0N 233056239217615, s0N 223851947954014]
private def s0V6S3 : List ℤ :=
  [s0N 212565310536855, s0N 199569899754420, s0N 185230626041748, s0N 169970483026861,
   s0N 154201510182283, s0N 138298185722395, s0N 122627392637543, s0N 107494628508010,
   s0N 93155988287590, s0N 79812072127261, s0N 67600202972082, s0N 56598231781287,
   s0N 46848707726027, s0N 38341461779988, s0N 31013475747062, s0N 24793476806543,
   s0N 19601479321600, s0N 15324833805093, s0N 11836774559610, s0N 9030399497449,
   s0N 6812566072255, s0N 5087093776869, s0N 3756820052890, s0N 2737244122762, s0N 1965970495944,
   s0N 1396034771301, s0N 984575218171, s0N 691027703315, s0N 481175395784, s0N 329428275248,
   s0N 218606219428, s0N 138289858563, s0N 82213773517, s0N 45576587906, s0P 23604666343,
   s0P 11603886658, s0P 5608350393, s0P 2806448335, s0P 1518530099, s0P 890914833, s0P 546497110,
   s0P 335308414, s0P 198350109, s0P 110470247, s0P 57129908, s0P 27130023, s0P 11706450,
   s0P 4550783, s0P 1584580, s0P 492257, s0N 135926, s0N 33185, s0N 7103, s0P 1325, s0P 221,
   s0N 35, s0N 9, s0N 3, s0N 1, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V6S4 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V6S5 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V6S6 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V6 : List ℤ :=
  s0V6S0 ++
  (s0V6S1 ++
  (s0V6S2 ++
  (s0V6S3 ++
  (s0V6S4 ++
  (s0V6S5 ++
  s0V6S6)))))
private def s0Rem8 : List Rkm128kSeg := s0Drop 3 s0Rem7
private def s0V7S0 : List ℤ :=
  [s0P 24315065, s0P 8469320, s0N 2194535, s0P 32989023, s0P 55041487, s0P 15612275,
   s0P 175140588, s0N 15439456, s0N 85174496, s0N 26959025, s0N 8145652, s0N 8780206,
   s0N 286524682, s0N 507632113, s0N 923279162, s0N 1634556476, s0N 1964940239, s0N 804692838,
   s0P 1154441056, s0P 26727177, s0N 1968723267, s0P 216864184, s0N 420149824, s0P 531538151,
   s0P 1939921466, s0P 889426178, s0P 2475854803, s0P 2703695241, s0N 571879398, s0P 1725586804,
   s0P 1176232882, s0P 1273751660, s0P 271829649, s0P 354456334, s0N 563009223, s0N 2550307492,
   s0N 1883368041, s0P 575227211, s0N 1577707007, s0N 204042251, s0N 664461896, s0P 1517838478,
   s0N 320534630, s0P 1459351309, s0P 2698234896, s0N 2374313339, s0N 1181191501, s0N 3890633803,
   s0N 3499652328, s0N 14021722509, s0N 17664270578, s0N 28361914302, s0N 39462739997,
   s0N 23457652552, s0N 9060989273, s0P 5707241965, s0P 19094379866, s0P 6723768017,
   s0N 26740619132, s0N 35853114236, s0N 18277596131, s0N 1490177961, s0P 14142316394,
   s0P 23419905903]
private def s0V7S1 : List ℤ :=
  [s0P 19085611540, s0N 4457575786, s0N 3563073686, s0P 3242402494, s0N 4875466976,
   s0P 10326184351, s0N 14353351367, s0N 16339625519, s0N 16375320853, s0N 26580357910,
   s0P 7080805963, s0P 3829888996, s0N 7447911035, s0P 607628357, s0P 4315721177, s0N 9112871107,
   s0N 11284602217, s0N 5853636484, s0N 15282084644, s0P 7462216507, s0P 2245508792,
   s0P 3070460693, s0N 790149989, s0P 2183979501, s0N 2414952305, s0P 4766894501, s0P 5742959911,
   s0P 5667739423, s0P 5112410874, s0N 9783664714, s0N 1213900499, s0N 9610328773, s0N 615586790,
   s0P 628671466, s0P 1312160916, s0P 5454410719, s0P 8996228560, s0P 2548994533, s0N 9127311439,
   s0N 11143531199, s0P 3263964198, s0P 1540776223, s0N 3781713653, s0P 3704005754,
   s0N 26449317622, s0N 21330014808, s0N 29559969568, s0N 2095294319, s0P 3488868979,
   s0P 698439580, s0N 12459907605, s0P 14992067756, s0N 7317515512, s0P 1044945329,
   s0N 3458148704, s0P 8193247633, s0N 898592663, s0P 8337159261, s0N 531297556, s0N 5765581777,
   s0N 1842358022, s0N 2100271873, s0N 112263673, s0P 3612290578]
private def s0V7S2 : List ℤ :=
  [s0N 3639504467, s0N 3949990150, s0P 7751388638, s0N 1605506496, s0P 2652722513, s0N 1749609389,
   s0N 218989456, s0P 7871791228, s0N 2877636026, s0P 2989704099, s0P 1562333173, s0P 1646677201,
   s0P 2368040643, s0P 4132877865, s0N 6854907738, s0N 159441452, s0P 1606777030, s0N 58290875,
   s0N 2309269428, s0N 1694779966, s0N 4138040337, s0P 60269187, s0P 2509981994, s0P 782933903,
   s0P 6252181576, s0N 11460034345, s0N 23045327825, s0P 33430214290, s0N 29372816228,
   s0P 1132462068, s0P 28796397107, s0N 9527860363, s0N 28296784325, s0P 145023206,
   s0N 18988598055, s0P 16455013777, s0P 17817639696, s0P 49015527454, s0P 101515826401,
   s0P 156952952011, s0P 248919433113, s0P 372281582619, s0P 551831257792, s0P 809524365688,
   s0P 1166878349466, s0P 1662170652739, s0P 2344427342828, s0P 3249970168045, s0P 4470795357957,
   s0P 6057610317176, s0P 8111743783298, s0P 10740363499642, s0P 14027880114792,
   s0P 18117522762346, s0P 23115341496691, s0P 29123621572910, s0P 36270589603874,
   s0P 44621319009340, s0P 54239092209292, s0P 65155034414795, s0P 77332384426312,
   s0P 90696746677025, s0P 105121385679243, s0P 120402935808942]
private def s0V7S3 : List ℤ :=
  [s0P 136281893854726, s0P 152447925359603, s0P 168532644661478, s0P 184137141582802,
   s0P 198841665968452, s0P 212215977281315, s0P 223855222720910, s0P 233394317346157,
   s0P 240514677234526, s0P 244979561865626, s0P 246647649540104, s0P 245458051484219,
   s0P 241447265248712, s0P 234766139453765, s0P 225647985707039, s0P 214386959866427,
   s0P 201336153715849, s0P 186914701600534, s0P 171531761447826, s0P 155623248141819,
   s0P 139541049887910, s0P 123714179323072, s0P 108402897023680, s0P 93924416519798,
   s0P 80437155833400, s0P 68080542723527, s0P 56980996585282, s0P 47148892792650,
   s0P 38544237986218, s0P 31191770476883, s0P 24906841448308, s0P 19682620416734,
   s0P 15367332848850, s0P 11871021422605, s0P 9077166146764, s0P 6831881606090,
   s0P 5085207357853, s0P 3762458247492, s0P 2757211432159, s0P 1953265683421, s0P 1396681322191,
   s0P 992904338235, s0P 707569553107, s0P 507911031936, s0P 340220877822, s0P 195242207430,
   s0P 92263027780, s0P 36029097878, s0N 12567528941, s0N 5095702174, s0N 3162710152,
   s0N 2474748314, s0N 1902123441, s0N 1350801284, s0N 894653535, s0N 560227103, s0N 338285010,
   s0N 196023876, s0N 109424545, s0N 59936297, s0N 31871342, s0N 15480070, s0N 6374316,
   s0N 2082306]
private def s0V7S4 : List ℤ :=
  [s0P 483933, s0P 43235, s0P 28572, s0P 21265, s0P 9460, s0P 3387, s0N 1054, s0N 293, s0P 75,
   s0P 17, s0P 4, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0]
private def s0V7S5 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V7S6 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V7S7 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0]
private def s0V7 : List ℤ :=
  s0V7S0 ++
  (s0V7S1 ++
  (s0V7S2 ++
  (s0V7S3 ++
  (s0V7S4 ++
  (s0V7S5 ++
  (s0V7S6 ++
  s0V7S7))))))
private def s0Rem9 : List Rkm128kSeg := s0Drop 3 s0Rem8
private def s0V8S0 : List ℤ :=
  [s0P 27640220, s0N 12092143, s0N 39202022, s0N 75707028, s0N 47437444, s0N 21572539,
   s0N 82916760, s0N 135115343, s0P 35956504, s0N 71420560, s0P 30798086, s0P 69273010,
   s0P 30924440, s0P 85946742, s0N 78828147, s0N 39523594, s0N 131948733, s0N 159206875,
   s0N 90824408, s0P 338793410, s0P 931389248, s0P 1681066314, s0P 2288428643, s0P 2530684241,
   s0P 206802618, s0N 1296051116, s0P 777232432, s0P 1827882411, s0P 2825056335, s0P 1622827150,
   s0P 738041702, s0P 916532511, s0N 2339427915, s0N 636074956, s0P 495313925, s0P 564944343,
   s0P 107093734, s0P 1223273677, s0P 1556941902, s0P 1320621062, s0N 671417496, s0P 3830782269,
   s0P 1247179643, s0N 1066511671, s0P 396529019, s0P 401803194, s0P 4606972706, s0P 3826730215,
   s0N 592607569, s0P 3731569476, s0P 2334171174, s0P 2312279801, s0N 980682007, s0P 9926105,
   s0P 1601672749, s0P 3343295287, s0P 9311479312, s0N 1157400081, s0N 2945569147, s0P 2507434618,
   s0N 4962993432, s0N 33361073472, s0N 47067632815, s0N 32533025421]
private def s0V8S1 : List ℤ :=
  [s0N 15893022437, s0P 1395885039, s0P 6993731146, s0P 14807953865, s0N 6522631947,
   s0N 19167798495, s0P 28652969705, s0P 20298590290, s0N 38606355341, s0N 5282315785,
   s0P 9577476603, s0P 5924548824, s0N 3443859815, s0P 9899957346, s0N 8265865885, s0N 3138207446,
   s0N 2922949687, s0P 994972516, s0N 13807204444, s0N 18649820546, s0N 15484488449,
   s0N 6188197681, s0P 9878573593, s0P 11252448432, s0P 2658682649, s0P 7714235979,
   s0P 2488874180, s0N 5793112355, s0N 8156811344, s0P 7227052942, s0N 12637654262,
   s0P 1875330417, s0N 546173664, s0N 8904692471, s0N 549343309, s0P 3117112445, s0N 7073154658,
   s0P 2056950651, s0P 4931553843, s0N 3312951472, s0N 1989239062, s0P 11214285675,
   s0P 4680877260, s0P 14820067826, s0N 4095090908, s0P 9392932352, s0N 13786680303,
   s0N 4355907161, s0P 11556703023, s0N 988392010, s0N 17955862513, s0P 14255151866,
   s0N 6359339600, s0N 17195256037, s0N 18652948588, s0P 8272548444, s0N 20723470579,
   s0P 3219962145, s0P 10704359588, s0N 8617549012, s0N 7171210085, s0N 8583804840,
   s0P 3727076608, s0N 5336428457]
private def s0V8S2 : List ℤ :=
  [s0N 1745279293, s0P 165549275, s0N 2875371015, s0N 2856384223, s0N 2362178980, s0N 3509435356,
   s0N 4249611545, s0N 3561369249, s0P 3569643504, s0N 5666342296, s0P 8012783685, s0N 1915666313,
   s0P 2647957716, s0N 8183702012, s0N 1181818483, s0N 1064857482, s0P 7025099164, s0P 472668067,
   s0N 18429718048, s0P 23572893827, s0P 18880630424, s0P 6652396984, s0N 2151356764,
   s0N 18210678979, s0P 1820402119, s0P 22758937946, s0N 25895723415, s0P 17046220019,
   s0P 8663278616, s0N 25954687016, s0P 14660849652, s0P 12554061203, s0P 12270874949,
   s0P 14946954191, s0N 2795939350, s0P 12451011119, s0N 391276502, s0P 1314474541,
   s0N 6800546017, s0N 757859962, s0N 15814636968, s0N 5492356158, s0N 3461963433, s0P 1230788049,
   s0P 1984628546, s0N 4134563450, s0P 2571704489, s0P 5594624023, s0P 5360192732, s0P 1960305783,
   s0P 2759147399, s0P 16880114711, s0P 34333383655, s0P 67495054031, s0P 116344404353,
   s0P 183188761040, s0P 286181383704, s0P 435841920868, s0P 647230370054, s0P 952523664739,
   s0P 1383278351928, s0P 1977880688577, s0P 2790940964424, s0P 3887374284479]
private def s0V8S3 : List ℤ :=
  [s0P 5339738131419, s0P 7248170966714, s0P 9700433197639, s0P 12823278810949,
   s0P 16720564480794, s0P 21551733324310, s0P 27388028217939, s0P 34400911193690,
   s0P 42637654665706, s0P 52207005721930, s0P 63108292137012, s0P 75343975084661,
   s0P 88850205044071, s0P 103473114225536, s0P 119007168498070, s0P 135242669201312,
   s0P 151763717620981, s0P 168282009989680, s0P 184297557634494, s0P 199402819367488,
   s0P 213179138688264, s0P 225128764722302, s0P 234914041051803, s0P 242191010218727,
   s0P 246727252478769, s0P 248343858434653, s0P 247014399400689, s0P 242763375103912,
   s0P 235790710857925, s0P 226306694130225, s0P 214636614786289, s0P 201203243559754,
   s0P 186368317030190, s0P 170607628616388, s0P 154378733585061, s0P 138069849227898,
   s0P 121997260023041, s0P 106565721943510, s0P 92016649274782, s0P 78523370624453,
   s0P 66234118047925, s0P 55207346856922, s0P 45490085221790, s0P 37061912748910,
   s0P 29848803025612, s0P 23734182737676, s0P 18671955841696, s0P 14522651728841,
   s0P 11171612551752, s0P 8498173103069, s0P 6372064310063, s0P 4711439674329, s0P 3449086800644,
   s0P 2507319337086, s0P 1815555049405, s0P 1310373440320, s0P 935067142896, s0P 643728346006,
   s0P 417791001472, s0P 251499746493, s0P 137784825841, s0P 67488623620, s0N 29563782333,
   s0P 12035086073]
private def s0V8S4 : List ℤ :=
  [s0P 5070959881, s0P 2609671343, s0P 1746682843, s0P 1339621492, s0P 980141436, s0P 616665001,
   s0P 329563922, s0P 159775723, s0P 79151454, s0P 43723334, s0P 25669491, s0P 14335733,
   s0P 7091121, s0P 3014196, s0P 1091259, s0P 339748, s0P 93975, s0P 24068, s0N 5730, s0N 1200,
   s0N 212, s0N 41, s0N 13, s0N 4, s0N 0, s0P 0, s0P 1, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V8S5 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V8S6 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V8S7 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V8S8 : List ℤ :=
  [s0P 0]
private def s0V8 : List ℤ :=
  s0V8S0 ++
  (s0V8S1 ++
  (s0V8S2 ++
  (s0V8S3 ++
  (s0V8S4 ++
  (s0V8S5 ++
  (s0V8S6 ++
  (s0V8S7 ++
  s0V8S8)))))))
private def s0Rem10 : List Rkm128kSeg := s0Drop 3 s0Rem9
private def s0V9S0 : List ℤ :=
  [s0N 21816633, s0N 14147185, s0P 7366082, s0P 23932231, s0N 21776542, s0P 72197299,
   s0P 45939567, s0N 39666787, s0P 157471810, s0P 52282765, s0P 21885848, s0P 62564284,
   s0P 60187218, s0N 49395159, s0P 45558022, s0N 2402595, s0P 52410976, s0P 78063054,
   s0P 79245531, s0P 30342070, s0P 55870031, s0N 89309384, s0N 12619421, s0N 494158948,
   s0N 824289550, s0N 1579750913, s0P 539670416, s0P 2263467296, s0N 1842951832, s0N 3236321841,
   s0N 27996089, s0P 3416533679, s0P 1888589724, s0P 259364989, s0N 286586095, s0N 984911074,
   s0N 163752858, s0N 225119584, s0N 145681132, s0N 1951964598, s0N 3098433952, s0N 1795501581,
   s0P 671095288, s0N 1459858144, s0N 216124257, s0P 2813400338, s0P 3112770564, s0N 2157550013,
   s0P 714241872, s0P 324704820, s0N 1208458966, s0N 7356433686, s0N 3427860875, s0N 1384444776,
   s0P 4712534104, s0P 1622957512, s0P 703246536, s0P 1123201100, s0N 460115619, s0P 1335664865,
   s0P 2299809654, s0P 4843888588, s0P 289544088, s0P 1599639128]
private def s0V9S1 : List ℤ :=
  [s0N 6376682880, s0N 14794128135, s0N 32252902259, s0N 30966221135, s0N 36729296416,
   s0N 39165741605, s0N 31134890004, s0P 2971557162, s0P 22635259157, s0P 25073673060,
   s0P 24157489092, s0P 13093368146, s0P 3862924610, s0N 5582896933, s0N 9844150349,
   s0N 14273426670, s0P 5859501091, s0P 407359616, s0P 438222994, s0P 2718925814, s0P 2696988442,
   s0P 8242211100, s0N 11904872162, s0P 11041871376, s0P 8154184739, s0N 1335517630,
   s0N 10993557157, s0P 3915256162, s0N 4739952247, s0P 9104149721, s0P 9222675269,
   s0P 9430967798, s0P 17080091414, s0P 14546086033, s0P 12283557395, s0P 12679743866,
   s0P 11954846863, s0P 857053829, s0P 8102289819, s0P 6242834664, s0P 6957536155, s0P 5816020481,
   s0N 1722005932, s0N 11506937086, s0P 10966605194, s0N 1273212418, s0N 6843490930,
   s0N 11339832415, s0N 16958844873, s0P 3036595494, s0N 20510950321, s0N 1893750148,
   s0N 15052145243, s0P 7686029696, s0N 168271583, s0P 16277685994, s0P 9019651776, s0N 993567523,
   s0N 11200728924, s0N 2633217561, s0N 12074340318, s0P 12836410368, s0P 14017182247,
   s0P 3532230973]
private def s0V9S2 : List ℤ :=
  [s0N 7165747588, s0P 5096258414, s0P 10478125238, s0N 6953778773, s0P 869418300, s0N 687296198,
   s0P 4415897258, s0P 2982175109, s0P 7439982048, s0N 4221662012, s0N 9962900216, s0N 3147458410,
   s0P 107759485, s0N 4537693558, s0N 8276285527, s0N 2274408288, s0P 11278352777,
   s0P 10688601467, s0P 12222106714, s0N 6574720948, s0N 3981063541, s0P 24486132943,
   s0P 10474659380, s0N 16797619726, s0P 7586137633, s0P 1142404073, s0P 32318636927,
   s0N 12266256488, s0P 19826851492, s0P 3719685426, s0P 1013288179, s0N 3637629963,
   s0N 7595679267, s0P 12100838890, s0N 29314095294, s0P 17536126564, s0P 8827323013,
   s0P 14099587756, s0N 7443005453, s0N 232444630, s0N 900396132, s0N 4892126709, s0P 664256901,
   s0P 5005089771, s0P 12565905381, s0P 4605510100, s0N 2542086111, s0P 657299307, s0N 2082031594,
   s0P 4962570434, s0N 2448460592, s0N 693185654, s0P 3661613222, s0N 2155428344, s0N 4220272094,
   s0P 4308266102, s0P 1180671100, s0P 8696050762, s0N 6742048544, s0P 1377583025, s0P 685633025,
   s0N 2756254177, s0P 943203440, s0N 5747575903]
private def s0V9S3 : List ℤ :=
  [s0P 6897275027, s0P 10846882015, s0P 2502143031, s0P 32694787969, s0P 44098331762,
   s0P 72207425029, s0P 148365158903, s0P 206981159015, s0P 343077893058, s0P 518875375825,
   s0P 780965898227, s0P 1157290965555, s0P 1690439352387, s0P 2421473031167, s0P 3444768811290,
   s0P 4802108182163, s0P 6598236540594, s0P 8974793547853, s0P 11997637855440,
   s0P 15837814412585, s0P 20604087700376, s0P 26454955558044, s0P 33509043553833,
   s0P 41865398826213, s0P 51591331359661, s0P 62767630956641, s0P 75350571111288,
   s0P 89235622081688, s0P 104347279510663, s0P 120419132565443, s0P 137161130790928,
   s0P 154245801328765, s0P 171256842132803, s0P 187688452114843, s0P 203116887316299,
   s0P 217063548277897, s0P 229047289958245, s0P 238672680250368, s0P 245598251455991,
   s0P 249607794118582, s0P 250573570834198, s0P 248430416134140, s0P 243271571875565,
   s0P 235324767997292, s0P 224875742010181, s0P 212284895297706, s0P 197955098277224,
   s0P 182381358124035, s0P 165986280924460, s0P 149306322213817, s0P 132635889144145,
   s0P 116461889864755, s0P 101007809849120, s0P 86580475206913, s0P 73360891640542,
   s0P 61394565200541, s0P 50754570582820, s0P 41519175697761, s0P 33487504145800,
   s0P 26761938362295, s0P 21127923965789, s0P 16475541699834, s0P 12702162130162,
   s0P 9639514108098]
private def s0V9S4 : List ℤ :=
  [s0P 7235232312216, s0P 5401722684893, s0P 3987843845677, s0P 2880417855849, s0P 2092566621283,
   s0P 1516585895612, s0P 1089232642132, s0P 749409086324, s0P 462240765191, s0P 244079048084,
   s0P 109912139119, s0N 44140903471, s0N 17745228337, s0N 8426503502, s0N 4990730279,
   s0N 3321114513, s0N 2246736341, s0N 1483852664, s0N 946591504, s0N 582601736, s0N 346778488,
   s0N 200437728, s0N 112967943, s0N 62235768, s0N 33502592, s0N 17568338, s0N 8931180,
   s0N 4378439, s0N 2060035, s0N 926611, s0N 397328, s0N 162102, s0N 62841, s0N 23132, s0N 8080,
   s0N 2674, s0N 833, s0N 242, s0N 62, s0N 12, s0N 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V9S5 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V9S6 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V9S7 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V9S8 : List ℤ :=
  [s0P 0]
private def s0V9 : List ℤ :=
  s0V9S0 ++
  (s0V9S1 ++
  (s0V9S2 ++
  (s0V9S3 ++
  (s0V9S4 ++
  (s0V9S5 ++
  (s0V9S6 ++
  (s0V9S7 ++
  s0V9S8)))))))
private def s0Rem11 : List Rkm128kSeg := s0Drop 3 s0Rem10
private def s0V10S0 : List ℤ :=
  [s0P 11796859, s0P 8264897, s0P 55904029, s0N 7723405, s0N 19231187, s0P 24325265, s0P 2141326,
   s0N 165281445, s0N 34607607, s0N 14628017, s0N 14899564, s0N 68968665, s0P 46802584,
   s0N 22978122, s0N 59757153, s0N 91414408, s0N 36462293, s0N 85763074, s0P 127224679,
   s0P 32517050, s0N 43581500, s0P 91904472, s0N 182017285, s0N 24569485, s0N 188603038,
   s0N 156243968, s0N 466940968, s0N 311049650, s0N 861409367, s0N 1414307519, s0N 1510570314,
   s0N 2853694228, s0N 3396347084, s0N 2682496548, s0N 59469471, s0P 1747152035, s0P 1244405336,
   s0N 1427423427, s0N 771912516, s0P 1349024872, s0N 1637735102, s0P 1568550560, s0N 425416425,
   s0P 766906084, s0P 3373353089, s0P 2047202331, s0P 2013506813, s0P 518339130, s0P 4586743105,
   s0N 1920622011, s0P 16323418, s0N 2071148479, s0P 1620584548, s0P 1572249102, s0P 5632049416,
   s0P 5941528302, s0P 158943596, s0N 792829332, s0P 340311622, s0N 3888987499, s0N 2602348689,
   s0N 4475754660, s0P 1118442717, s0P 2555160858]
private def s0V10S1 : List ℤ :=
  [s0N 2970782650, s0P 1120524084, s0P 3106902150, s0P 1439419404, s0N 3762809428, s0N 5296666901,
   s0N 3091446582, s0P 3681372231, s0P 2035362705, s0P 4774525048, s0P 11374302949,
   s0P 5454161527, s0P 7525194467, s0P 8633706842, s0P 30086601098, s0P 49691655854,
   s0P 46105875168, s0P 33752358367, s0P 6407649374, s0N 5723412367, s0N 25265200256,
   s0N 25222959949, s0N 22203837546, s0N 8849250751, s0P 5318972801, s0P 1210291169,
   s0P 680499010, s0P 1298998341, s0N 707284767, s0N 3811489557, s0N 5096920196, s0P 1593591131,
   s0P 4462168113, s0P 4274178594, s0P 2105588341, s0N 4642302406, s0N 9921467446, s0N 5495964238,
   s0P 8080072740, s0P 1179469592, s0N 4400454329, s0N 362679670, s0P 202811782, s0N 11320251831,
   s0N 10961741649, s0N 2409895051, s0N 25685661964, s0N 9446163430, s0N 25669617963,
   s0N 13308130074, s0N 608007306, s0P 15384188581, s0N 9116311781, s0N 12336266482,
   s0P 15642846054, s0P 15643837775, s0P 460860239, s0N 5699299339, s0N 7697802594,
   s0N 1512126861, s0N 950551341, s0P 2859199656, s0P 7692112937, s0P 18542190055]
private def s0V10S2 : List ℤ :=
  [s0P 6243814005, s0P 13064550560, s0P 7343492532, s0N 7947069633, s0N 19770370, s0N 7545361977,
   s0N 3035505398, s0P 2129700459, s0N 2291122617, s0P 7586790512, s0P 5508054666, s0P 3019702489,
   s0P 2418837966, s0N 10503794130, s0P 7997561888, s0P 3508945433, s0N 5191892459,
   s0N 22503198290, s0N 4855067010, s0P 8275565588, s0N 13080800893, s0N 29207769247,
   s0N 2936837079, s0P 12527238861, s0N 17640700957, s0P 5186561543, s0P 460286029,
   s0P 14287482048, s0P 25392785208, s0N 13541495322, s0N 14446200348, s0P 95685244,
   s0N 9498265528, s0N 26822307193, s0N 12411693536, s0N 1303755920, s0P 657840989,
   s0P 3498367029, s0N 418383690, s0N 3218186681, s0P 797489792, s0N 7001223716, s0N 9706686989,
   s0N 2946912090, s0P 3987664282, s0N 12439117373, s0N 5147397698, s0P 11434175575,
   s0P 4578853990, s0N 4027746971, s0N 11017304349, s0N 3062820550, s0N 5971910801,
   s0P 7469017023, s0N 6325450532, s0P 909425104, s0P 2076318116, s0P 11404885428, s0N 873903182,
   s0P 166138717, s0N 1702020111, s0P 8398491947, s0N 9153363121, s0P 11382246443]
private def s0V10S3 : List ℤ :=
  [s0P 9680821233, s0P 10783362777, s0P 12651255686, s0P 2448396806, s0N 1859319406,
   s0N 1349746705, s0P 6245909880, s0P 2437274091, s0N 821820263, s0P 6388973951, s0N 7788097055,
   s0N 1783701257, s0N 6492424300, s0P 3397200565, s0N 6789201767, s0N 3807788768, s0N 3962623273,
   s0N 6115819249, s0N 3726810923, s0N 25840175537, s0N 61962566188, s0N 81312134849,
   s0N 142060027548, s0N 257251206271, s0N 385045869594, s0N 595714704027, s0N 925946080846,
   s0N 1376021291754, s0N 2025249916810, s0N 2947603701873, s0N 4192488435565, s0N 5888323887096,
   s0N 8122790164605, s0N 11071212027191, s0N 14805536316706, s0N 19549497535601,
   s0N 25372391183863, s0N 32528817027738, s0N 41025704411045, s0N 51003888264017,
   s0N 62515564297759, s0N 75546015568478, s0N 90004748304644, s0N 105737843472530,
   s0N 122442787439774, s0N 139949440083713, s0N 157696959791851, s0N 175320591007913,
   s0N 192301426008598, s0N 208055583764933, s0N 222185745245496, s0N 234124044263334,
   s0N 243437765852340, s0N 249841240320797, s0N 253100923894441, s0N 253073684964446,
   s0N 249821078416478, s0N 243433071768385, s0N 234201822513213, s0N 222481468240126,
   s0N 208685931677331, s0N 193256017951457, s0N 176797317988412, s0N 159641295893645]
private def s0V10S4 : List ℤ :=
  [s0N 142412910485784, s0N 125469749673276, s0N 109194084545003, s0N 93878262270109,
   s0N 79657190104950, s0N 66779619125779, s0N 55356298458570, s0N 45313189096300,
   s0N 36625273455703, s0N 29270136829949, s0N 23108382435216, s0N 18006461565167,
   s0N 13864408091744, s0N 10549268201841, s0N 7919972056929, s0N 5870910335012,
   s0N 4321484981042, s0N 3180444676870, s0N 2334660209828, s0N 1678903064368, s0N 1151492249149,
   s0N 735793828289, s0N 432257843498, s0N 232988257273, s0N 116289974036, s0N 54978052749,
   s0N 25609613801, s0N 12397128225, s0N 6526547238, s0N 3765755398, s0N 2311544267,
   s0N 1453082536, s0N 910929894, s0N 561801202, s0N 338959219, s0N 199706966, s0N 114859708,
   s0N 64485995, s0N 35335923, s0N 18889291, s0N 9842933, s0N 4994713, s0N 2465462, s0N 1182555,
   s0N 550622, s0N 248679, s0N 108862, s0N 46168, s0N 18957, s0N 7527, s0N 2885, s0N 1063,
   s0N 371, s0N 120, s0N 34, s0N 6, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V10S5 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V10S6 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V10S7 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V10S8 : List ℤ :=
  [s0P 0]
private def s0V10 : List ℤ :=
  s0V10S0 ++
  (s0V10S1 ++
  (s0V10S2 ++
  (s0V10S3 ++
  (s0V10S4 ++
  (s0V10S5 ++
  (s0V10S6 ++
  (s0V10S7 ++
  s0V10S8)))))))
private def s0Rem12 : List Rkm128kSeg := s0Drop 3 s0Rem11
private def s0V11S0 : List ℤ :=
  [s0P 9988310, s0P 7314999, s0N 1605651, s0P 29483867, s0P 86839514, s0N 74770083, s0N 22317318,
   s0P 78161588, s0P 30123468, s0N 99131278, s0P 18952583, s0P 20038577, s0N 27845534,
   s0P 92155003, s0N 24347534, s0P 39078492, s0N 50126798, s0P 16166943, s0N 116531326,
   s0N 167147121, s0N 172747553, s0N 39057797, s0N 31922119, s0N 115355500, s0N 213530053,
   s0P 97231788, s0N 361675864, s0N 242104216, s0N 75005026, s0P 260667617, s0P 125597766,
   s0P 121924787, s0P 582314257, s0P 355366225, s0N 388240666, s0N 673794973, s0P 112862471,
   s0N 118329261, s0N 620585643, s0P 1215308402, s0P 3114395787, s0P 2987871421, s0P 4764163779,
   s0P 2633001552, s0N 203860018, s0N 2625837851, s0N 3573224631, s0N 1267804900, s0P 666344792,
   s0P 1677995408, s0P 897148788, s0P 3395428811, s0N 2259415967, s0N 272414900, s0N 1443134500,
   s0N 799914586, s0N 611784407, s0N 3372176526, s0N 711654750, s0N 1006226076, s0P 698101196,
   s0P 2185010387, s0N 5317073867, s0N 6202918388]
private def s0V11S1 : List ℤ :=
  [s0N 5615226134, s0P 1421905601, s0P 5143036932, s0P 1890883126, s0P 5235921635, s0N 5013316041,
   s0P 6132639069, s0P 441015641, s0N 5971397101, s0P 4287719080, s0P 4602172101, s0N 6904007176,
   s0N 1811662699, s0P 6143866245, s0P 2606203208, s0P 143882862, s0N 1606034466, s0N 701952520,
   s0N 1702082281, s0P 4668009843, s0P 3382615747, s0P 1535908361, s0N 740245261, s0N 3640751166,
   s0P 662654780, s0P 8622539940, s0P 18547287006, s0P 34843737872, s0P 48541702941,
   s0P 48946978529, s0P 31659500001, s0P 17717581433, s0P 900057790, s0N 19434212127,
   s0N 18211452888, s0N 12186677036, s0P 7978104292, s0P 13352595556, s0P 3818898267,
   s0P 3401909245, s0P 1906689284, s0P 796190307, s0P 6247995026, s0P 8790629065, s0P 15381799320,
   s0P 14571319956, s0P 5586153302, s0N 6888724417, s0N 9806687428, s0N 8711706126,
   s0N 8090398970, s0P 3527172006, s0P 1629890257, s0N 2855543313, s0N 3824846772, s0P 1628795974,
   s0N 4507438136, s0N 1567131691, s0N 20173363558, s0N 20849329538, s0N 33135701536,
   s0N 16427860886, s0P 4089376956, s0N 4856298277]
private def s0V11S2 : List ℤ :=
  [s0P 1521333199, s0P 4034415051, s0P 266256799, s0P 3947649063, s0P 1779550304, s0N 1713733760,
   s0N 4157352391, s0P 338292736, s0P 7542672291, s0P 7831839682, s0P 6042284314, s0N 5171935588,
   s0P 28154985443, s0P 1922126974, s0P 16580747739, s0P 1107556447, s0N 2612774948,
   s0N 16350094661, s0P 17060334514, s0P 6275694410, s0P 13546731487, s0N 16292545527,
   s0N 13084112331, s0N 7686510324, s0P 856018995, s0P 7449561546, s0P 19537837000,
   s0P 3300326954, s0P 11711648697, s0P 28128775435, s0N 92226705, s0P 1843998719,
   s0N 17726378953, s0P 7975781191, s0P 3141164250, s0N 3942997113, s0N 13010633539,
   s0N 9437990144, s0N 118329311, s0N 11530905554, s0N 5192163171, s0N 1278956383,
   s0P 21957409706, s0P 7457301511, s0P 12841904810, s0P 2697507323, s0N 10066329243,
   s0N 2889122471, s0P 4738975937, s0N 1556005280, s0P 8440647159, s0P 3494259703, s0N 783022735,
   s0N 9300471996, s0P 7692199633, s0P 12420272115, s0P 14521934482, s0P 8201587008,
   s0P 1174724689, s0P 3777323881, s0P 2499102300, s0P 5212540887, s0P 11683277345,
   s0P 4901311164]
private def s0V11S3 : List ℤ :=
  [s0N 4162453232, s0P 7728838281, s0P 1204811156, s0P 13392610861, s0N 10948507867,
   s0P 4947914095, s0N 6085435282, s0N 2276121937, s0N 4966794126, s0N 2656963873, s0P 1241825296,
   s0P 6143878328, s0P 10421794427, s0P 58726154, s0P 5463473463, s0P 9754746407, s0N 2567066216,
   s0P 355372863, s0N 15105639772, s0N 10176267713, s0N 4970470379, s0P 15885792677,
   s0N 12617250616, s0N 3718985421, s0P 1600083140, s0P 2820909607, s0P 5692131936,
   s0N 3057335890, s0P 3100017530, s0N 24451650175, s0N 6185945225, s0P 27861698605,
   s0N 3645357451, s0P 1145000105, s0N 23101941503, s0N 15915053333, s0N 71731012362,
   s0N 86738738974, s0N 160662286634, s0N 302337708407, s0N 458424681161, s0N 712605943110,
   s0N 1137435715846, s0N 1709117437885, s0N 2565217143267, s0N 3734500738282, s0N 5356003008853,
   s0N 7553104850295, s0N 10507732187806, s0N 14251092311897, s0N 19105927808157,
   s0N 25139019768240, s0N 32564388428710, s0N 41516022976278, s0N 52017334256996,
   s0N 64225556527723, s0N 78065624315003, s0N 93411567029755, s0N 110110548648746,
   s0N 127841656466037, s0N 146246796025870, s0N 164867662952301, s0N 183139296645256,
   s0N 200538704252475]
private def s0V11S4 : List ℤ :=
  [s0N 216481104283067, s0N 230356946921965, s0N 241717590285817, s0N 250159369251420,
   s0N 255288499637479, s0N 256930092684813, s0N 255115614869734, s0N 249927449305730,
   s0N 241539838839231, s0N 230304685004909, s0N 216692522869297, s0N 201211884046647,
   s0N 184397684229118, s0N 166796767731111, s0N 148924218333751, s0N 131242756987251,
   s0N 114167940621495, s0N 98052777952041, s0N 83153856303855, s0N 69626874884359,
   s0N 57558405792907, s0N 46987689211330, s0N 37895280523360, s0N 30191862279569,
   s0N 23742111909481, s0N 18409039101748, s0N 14077342785384, s0N 10640796451363,
   s0N 7977666547161, s0N 5944522476652, s0N 4394471026036, s0N 3202733951552, s0N 2280605396738,
   s0N 1572310271489, s0N 1041944648460, s0N 660721516072, s0N 400254225802, s0N 231861476218,
   s0N 128900539244, s0N 69210338807, s0N 36229623064, s0N 18722913271, s0N 9693840234,
   s0N 5100981757, s0N 2755331072, s0N 1531385682, s0N 871144860, s0N 502247652, s0N 290388268,
   s0N 166891043, s0N 94733868, s0N 52888848, s0N 28963915, s0N 15533393, s0N 8149472,
   s0N 4179534, s0N 2094223, s0N 1024754, s0N 489500, s0N 228178, s0N 103764, s0N 46016,
   s0N 19888, s0N 8370]
private def s0V11S5 : List ℤ :=
  [s0N 3422, s0N 1353, s0N 513, s0N 183, s0N 60, s0N 15, s0N 2, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V11S6 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V11S7 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V11S8 : List ℤ :=
  [s0P 0]
private def s0V11 : List ℤ :=
  s0V11S0 ++
  (s0V11S1 ++
  (s0V11S2 ++
  (s0V11S3 ++
  (s0V11S4 ++
  (s0V11S5 ++
  (s0V11S6 ++
  (s0V11S7 ++
  s0V11S8)))))))
private theorem s0B0_ok :
    s0RunAtEq (s0Take 10 s0Rem0)
      hm256k512krS0LIn hm256k512krS0DCurIn hm256k512krS0PadIn hm256k512krS0VecIn
      1 256 119904355 s0V0
      = true := by decide +kernel
private theorem s0B1_ok :
    s0RunAtEq (s0Take 7 s0Rem1)
      1 256 119904355 s0V0
      1 256 187151301 s0V1
      = true := by decide +kernel
private theorem s0B2_ok :
    s0RunAtEq (s0Take 6 s0Rem2)
      1 256 187151301 s0V1
      1 256 252502271 s0V2
      = true := by decide +kernel
private theorem s0B3_ok :
    s0RunAtEq (s0Take 7 s0Rem3)
      1 256 252502271 s0V2
      1 256 307660305 s0V3
      = true := by decide +kernel
private theorem s0B4_ok :
    s0RunAtEq (s0Take 7 s0Rem4)
      1 256 307660305 s0V3
      2 512 369025887 s0V4
      = true := by decide +kernel
private theorem s0B5_ok :
    s0RunAtEq (s0Take 3 s0Rem5)
      2 512 369025887 s0V4
      2 512 394183718 s0V5
      = true := by decide +kernel
private theorem s0B6_ok :
    s0RunAtEq (s0Take 3 s0Rem6)
      2 512 394183718 s0V5
      2 512 408086238 s0V6
      = true := by decide +kernel
private theorem s0B7_ok :
    s0RunAtEq (s0Take 3 s0Rem7)
      2 512 408086238 s0V6
      2 512 437855328 s0V7
      = true := by decide +kernel
private theorem s0B8_ok :
    s0RunAtEq (s0Take 3 s0Rem8)
      2 512 437855328 s0V7
      2 512 472987051 s0V8
      = true := by decide +kernel
private theorem s0B9_ok :
    s0RunAtEq (s0Take 3 s0Rem9)
      2 512 472987051 s0V8
      2 512 510844349 s0V9
      = true := by decide +kernel
private theorem s0B10_ok :
    s0RunAtEq (s0Take 3 s0Rem10)
      2 512 510844349 s0V9
      2 512 533123082 s0V10
      = true := by decide +kernel
private theorem s0B11_ok :
    s0RunAtEq (s0Take 3 s0Rem11)
      2 512 533123082 s0V10
      2 512 563824041 s0V11
      = true := by decide +kernel
private theorem s0B12_ok :
    s0RunAtEq s0Rem12
      2 512 563824041 s0V11
      hm256k512krS0LOut hm256k512krS0DCurOut hm256k512krS0PadOut hm256k512krS0Vec
      = true := by decide +kernel

/-- RampKick128kAnchorsSound 256 4 prefix combiner across all 13 r < 512 anchors. -/
theorem hm256k512krS0_pfxAnchors_append_sound (rest : List RampKick128kAnchor)
    (hrest : RampKick128kAnchorsSound 256 4 rest) :
    RampKick128kAnchorsSound 256 4 (hm256k512krS0PfxAnchors ++ rest) := by
  exact
    ⟨s0ChkRow_eq (s0_hd s0RowChk0),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 s0RowChk0)),
    ⟨s0ChkRow_eq (s0_hd (s0_tl2 s0RowChk0)),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl2 s0RowChk0))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl4 s0RowChk0)),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl4 s0RowChk0))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl2 (s0_tl4 s0RowChk0))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl2 (s0_tl4 s0RowChk0)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl4 (s0_tl4 s0RowChk0))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl4 (s0_tl4 s0RowChk0)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl2 (s0_tl4 (s0_tl4 s0RowChk0)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl2 (s0_tl4 (s0_tl4 s0RowChk0))))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl4 (s0_tl4 (s0_tl4 s0RowChk0)))),
    hrest⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- Standalone RampKick128kAnchorsSound 256 4 certificate for hm256k512krS0PfxAnchors. -/
theorem hm256k512krS0_pfxAnchors_sound :
    RampKick128kAnchorsSound 256 4 hm256k512krS0PfxAnchors := by
  rw [← List.append_nil hm256k512krS0PfxAnchors]
  exact hm256k512krS0_pfxAnchors_append_sound [] trivial

/-- Alias prefix combiner matching pfxAnchorsLt512 convention. -/
theorem pfxAnchorsLt512_append_sound (rest : List RampKick128kAnchor)
    (hrest : RampKick128kAnchorsSound 256 4 rest) :
    RampKick128kAnchorsSound 256 4 (pfxAnchorsLt512 ++ rest) :=
  hm256k512krS0_pfxAnchors_append_sound rest hrest

/-- Standalone alias certificate matching pfxAnchorsLt512 convention. -/
theorem pfxAnchorsLt512_sound : RampKick128kAnchorsSound 256 4 pfxAnchorsLt512 :=
  hm256k512krS0_pfxAnchors_sound

/-- Segment count of hm256k512krS0Segs (59 segments). -/
theorem hm256k512krS0_len : rkm128kSegListLen hm256k512krS0Segs = 59 := rfl

/-- Exact rkm128kRunSegs 256 4 512 step across hm256k512krS0Segs (segs 0..58). -/
theorem hm256k512krS0_step :
    rkm128kRunSegs 256 4 512 hm256k512krS0Segs 1 0 1 [Int.ofNat wdScale] =
      (hm256k512krS0LOut, hm256k512krS0DCurOut, hm256k512krS0PadOut, hm256k512krS0Vec) := by
  exact s0RunStepTd s0B0_ok
    (s0RunStepTd s0B1_ok
    (s0RunStepTd s0B2_ok
    (s0RunStepTd s0B3_ok
    (s0RunStepTd s0B4_ok
    (s0RunStepTd s0B5_ok
    (s0RunStepTd s0B6_ok
    (s0RunStepTd s0B7_ok
    (s0RunStepTd s0B8_ok
    (s0RunStepTd s0B9_ok
    (s0RunStepTd s0B10_ok
    (s0RunStepTd s0B11_ok
    (s0RunLast s0B12_ok))))))))))))

/-- Suffix chaining lemma advancing rkm128kRunSegs 256 4 512 past hm256k512krS0Segs. -/
theorem hm256k512krS0_run_after (rest : List Rkm128kSeg) :
    rkm128kRunSegs 256 4 512 (hm256k512krS0Segs ++ rest) 1 0 1 [Int.ofNat wdScale] =
      rkm128kRunSegs 256 4 512 rest hm256k512krS0LOut hm256k512krS0DCurOut
        hm256k512krS0PadOut hm256k512krS0Vec := by
  rw [rkm128kRunSegs_append]
  dsimp only
  rw [hm256k512krS0_step]

end

end Rk128kHiM256K512KrPt0
end QuantumComputation.Specs.GroverFindAll
