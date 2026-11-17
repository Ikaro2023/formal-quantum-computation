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
# `(4, 512)` `RampKick128k` Krotov `L <= 248` Part 0 (`Rk128kLowM4K512L248KrPt0`)

Certifies Slice 0 (`431,931` F1272 / `447,660 <= 450,000` Horner coord-ops: all `101`
low anchors `r < 512` plus `r = 512` segments `0..46` (`47` segments) at `lTableMax = 248`).
-/

namespace QuantumComputation.Specs.GroverFindAll.Rk128kLowM4K512L248KrPt0

@[expose] public section

open QuantumComputation.Specs.DickeSol

/-- Active `RampKick128k` segments for `m = 4, r = 3` (`6` segments). -/
def lm4k512l248krS0SegsR3 : List Rkm128kSeg := [
  ⟨1, 126263759, 1, 13, []⟩,
  ⟨1, 113792387, 1, 12, []⟩,
  ⟨1, 61478563, 1, 10, rkm128kMask56 1 [1]⟩,
  ⟨1, 63017453, 1, 10, rkm128kMask56 2 [3]⟩,
  ⟨1, 31096551, 1, 8, rkm128kMask56 2 [2]⟩,
  ⟨1, 22614910, 1, 6, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 3`. -/
def lm4k512l248krS0RowR3 : List ℕ :=
  [178663035, 115095579855, 884725540240]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 3`. -/
def lm4k512l248krS0AncR3 : RampKick128kAnchor :=
  ⟨3, lm4k512l248krS0SegsR3, lm4k512l248krS0RowR3⟩
/-- Active `RampKick128k` segments for `m = 4, r = 4` (`8` segments). -/
def lm4k512l248krS0SegsR4 : List Rkm128kSeg := [
  ⟨1, 125946636, 1, 15, []⟩,
  ⟨1, 139627773, 1, 15, rkm128kMask56 1 [1]⟩,
  ⟨2, 40320782, 1, 10, rkm128kMask56 2 [3]⟩,
  ⟨2, 42170397, 1, 10, rkm128kMask56 3 [5]⟩,
  ⟨2, 10717358, 1, 6, rkm128kMask56 3 [7]⟩,
  ⟨2, 7808907, 1, 6, rkm128kMask56 3 [4]⟩,
  ⟨2, 7387260, 1, 6, rkm128kMask56 3 [4]⟩,
  ⟨2, 4586449, 1, 6, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 4`. -/
def lm4k512l248krS0RowR4 : List ℕ :=
  [2418074, 11901478, 141128216160, 858839235012]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 4`. -/
def lm4k512l248krS0AncR4 : RampKick128kAnchor :=
  ⟨4, lm4k512l248krS0SegsR4, lm4k512l248krS0RowR4⟩
/-- Active `RampKick128k` segments for `m = 4, r = 5` (`16` segments). -/
def lm4k512l248krS0SegsR5 : List Rkm128kSeg := [
  ⟨1, 36317409, 1, 10, []⟩,
  ⟨1, 43260475, 1, 10, []⟩,
  ⟨1, 49378865, 1, 10, []⟩,
  ⟨1, 49378866, 1, 10, []⟩,
  ⟨2, 43388783, 1, 12, []⟩,
  ⟨2, 33392595, 1, 10, rkm128kMask56 2 [2]⟩,
  ⟨2, 18337802, 1, 8, []⟩,
  ⟨2, 21180611, 1, 10, rkm128kMask56 3 [7]⟩,
  ⟨2, 13986880, 1, 8, []⟩,
  ⟨2, 13943482, 1, 8, rkm128kMask56 3 [7]⟩,
  ⟨2, 9367338, 1, 6, rkm128kMask56 4 [8]⟩,
  ⟨2, 8416610, 1, 6, rkm128kMask56 4 [15]⟩,
  ⟨2, 4536878, 1, 6, []⟩,
  ⟨2, 5610220, 1, 6, rkm128kMask56 4 [8]⟩,
  ⟨2, 8447414, 1, 6, rkm128kMask56 4 [8]⟩,
  ⟨2, 5282111, 1, 6, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 5`. -/
def lm4k512l248krS0RowR5 : List ℕ :=
  [66274251, 73011515, 14721512, 141171875351, 858659951239]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 5`. -/
def lm4k512l248krS0AncR5 : RampKick128kAnchor :=
  ⟨5, lm4k512l248krS0SegsR5, lm4k512l248krS0RowR5⟩
/-- Active `RampKick128k` segments for `m = 4, r = 6` (`8` segments). -/
def lm4k512l248krS0SegsR6 : List Rkm128kSeg := [
  ⟨1, 66806850, 1, 12, []⟩,
  ⟨1, 78257937, 1, 14, []⟩,
  ⟨2, 71017885, 1, 15, rkm128kMask56 1 [1]⟩,
  ⟨2, 41791346, 1, 12, rkm128kMask56 3 [5]⟩,
  ⟨2, 40830951, 1, 12, rkm128kMask56 4 [14]⟩,
  ⟨3, 21574257, 1, 10, []⟩,
  ⟨3, 15278114, 1, 10, rkm128kMask56 5 [19]⟩,
  ⟨3, 13959895, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 6`. -/
def lm4k512l248krS0RowR6 : List ℕ :=
  [9949260, 147192173, 309008741, 643014068, 156562597797, 842310109453]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 6`. -/
def lm4k512l248krS0AncR6 : RampKick128kAnchor :=
  ⟨6, lm4k512l248krS0SegsR6, lm4k512l248krS0RowR6⟩
/-- Active `RampKick128k` segments for `m = 4, r = 7` (`38` segments). -/
def lm4k512l248krS0SegsR7 : List Rkm128kSeg := [
  ⟨1, 46353656, 1, 10, []⟩,
  ⟨1, 41648360, 1, 10, []⟩,
  ⟨1, 35634389, 1, 10, []⟩,
  ⟨2, 20293123, 1, 10, []⟩,
  ⟨2, 23561590, 1, 10, []⟩,
  ⟨2, 25600808, 1, 10, []⟩,
  ⟨2, 23803693, 1, 10, rkm128kMask56 2 [3]⟩,
  ⟨3, 22526008, 1, 12, []⟩,
  ⟨3, 162536, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨3, 6183494, 1, 8, rkm128kMask56 2 [3]⟩,
  ⟨3, 3481281, 1, 6, rkm128kMask56 2 [3]⟩,
  ⟨3, 2255065, 1, 6, rkm128kMask56 3 [7]⟩,
  ⟨3, 5795104, 1, 6, rkm128kMask56 4 [15]⟩,
  ⟨3, 7070759, 1, 8, rkm128kMask56 2 [2]⟩,
  ⟨3, 11157140, 1, 8, rkm128kMask56 3 [7]⟩,
  ⟨3, 3585, 1, 4, rkm128kMask56 4 [11]⟩,
  ⟨3, 1970616, 1, 6, rkm128kMask56 3 [5]⟩,
  ⟨3, 1326132, 1, 4, rkm128kMask56 4 [10]⟩,
  ⟨3, 7008637, 1, 8, rkm128kMask56 2 [3]⟩,
  ⟨3, 187874, 1, 4, rkm128kMask56 5 [17]⟩,
  ⟨3, 6471001, 1, 6, rkm128kMask56 2 [2]⟩,
  ⟨3, 5051827, 1, 6, []⟩,
  ⟨3, 1141983, 1, 4, rkm128kMask56 2 [3]⟩,
  ⟨3, 13355055, 1, 8, rkm128kMask56 6 [48]⟩,
  ⟨3, 1709429, 1, 4, rkm128kMask56 6 [32]⟩,
  ⟨3, 1825601, 1, 4, rkm128kMask56 6 [34]⟩,
  ⟨3, 2028897, 1, 6, rkm128kMask56 6 [34]⟩,
  ⟨3, 1642770, 1, 4, rkm128kMask56 6 [33]⟩,
  ⟨3, 1691732, 1, 4, rkm128kMask56 6 [34]⟩,
  ⟨3, 818616, 1, 4, rkm128kMask56 2 [2]⟩,
  ⟨3, 1238748, 1, 4, rkm128kMask56 6 [37]⟩,
  ⟨3, 2000835, 1, 4, rkm128kMask56 6 [39]⟩,
  ⟨3, 703871, 1, 4, rkm128kMask56 1 [1]⟩,
  ⟨3, 1072091, 1, 4, rkm128kMask56 6 [37]⟩,
  ⟨3, 2290698, 1, 6, rkm128kMask56 6 [56]⟩,
  ⟨3, 928354, 1, 4, []⟩,
  ⟨3, 1265776, 1, 4, rkm128kMask56 6 [32]⟩,
  ⟨4, 358433, 1, 4, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 7`. -/
def lm4k512l248krS0RowR7 : List ℕ :=
  [1348096, 1315850, 31686858, 18320006, 2870652, 153467275143, 846463467709]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 7`. -/
def lm4k512l248krS0AncR7 : RampKick128kAnchor :=
  ⟨7, lm4k512l248krS0SegsR7, lm4k512l248krS0RowR7⟩
/-- Active `RampKick128k` segments for `m = 4, r = 8` (`33` segments). -/
def lm4k512l248krS0SegsR8 : List Rkm128kSeg := [
  ⟨1, 23150929, 1, 8, []⟩,
  ⟨1, 30937626, 1, 10, []⟩,
  ⟨1, 30937625, 1, 10, []⟩,
  ⟨1, 30937626, 1, 10, []⟩,
  ⟨2, 24917727, 1, 10, []⟩,
  ⟨2, 22592187, 1, 10, []⟩,
  ⟨2, 21876205, 1, 10, []⟩,
  ⟨3, 16559334, 1, 10, rkm128kMask56 2 [3]⟩,
  ⟨3, 6422554, 1, 8, rkm128kMask56 1 [1]⟩,
  ⟨3, 11815738, 1, 10, rkm128kMask56 3 [7]⟩,
  ⟨3, 15485550, 1, 10, rkm128kMask56 4 [10]⟩,
  ⟨3, 23155225, 1, 12, rkm128kMask56 5 [16]⟩,
  ⟨3, 18470249, 1, 10, rkm128kMask56 6 [61]⟩,
  ⟨3, 2584648, 1, 6, rkm128kMask56 6 [46]⟩,
  ⟨3, 1913531, 1, 6, rkm128kMask56 3 [4]⟩,
  ⟨4, 1401453, 1, 6, rkm128kMask56 3 [7]⟩,
  ⟨4, 2627376, 1, 6, rkm128kMask56 6 [57]⟩,
  ⟨4, 2007329, 1, 6, rkm128kMask56 5 [20]⟩,
  ⟨4, 2777600, 1, 6, rkm128kMask56 6 [57]⟩,
  ⟨4, 2366695, 1, 6, rkm128kMask56 6 [59]⟩,
  ⟨4, 2650357, 1, 6, rkm128kMask56 6 [56]⟩,
  ⟨4, 4698212, 1, 6, rkm128kMask56 6 [56]⟩,
  ⟨4, 6093001, 1, 8, rkm128kMask56 7 [122]⟩,
  ⟨4, 1425237, 1, 4, rkm128kMask56 7 [118]⟩,
  ⟨4, 1171637, 1, 4, rkm128kMask56 7 [74]⟩,
  ⟨4, 1295990, 1, 4, rkm128kMask56 6 [61]⟩,
  ⟨4, 279112, 1, 4, rkm128kMask56 7 [89]⟩,
  ⟨4, 1989415, 1, 6, rkm128kMask56 7 [102]⟩,
  ⟨4, 2049642, 1, 6, rkm128kMask56 7 [69]⟩,
  ⟨4, 1105149, 1, 4, rkm128kMask56 1 [1]⟩,
  ⟨4, 1681077, 1, 6, rkm128kMask56 7 [71]⟩,
  ⟨4, 2590235, 1, 6, rkm128kMask56 7 [64]⟩,
  ⟨4, 1193404, 1, 4, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 8`. -/
def lm4k512l248krS0RowR8 : List ℕ :=
  [1008233, 22919207, 3325139, 31566889, 20266174, 197778, 160197710800, 839718936687]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 8`. -/
def lm4k512l248krS0AncR8 : RampKick128kAnchor :=
  ⟨8, lm4k512l248krS0SegsR8, lm4k512l248krS0RowR8⟩
/-- Active `RampKick128k` segments for `m = 4, r = 9` (`10` segments). -/
def lm4k512l248krS0SegsR9 : List Rkm128kSeg := [
  ⟨1, 112919610, 1, 18, []⟩,
  ⟨2, 80854728, 1, 19, rkm128kMask56 2 [3]⟩,
  ⟨3, 29954352, 1, 13, rkm128kMask56 4 [13]⟩,
  ⟨3, 20383171, 1, 12, rkm128kMask56 5 [28]⟩,
  ⟨4, 20316065, 1, 12, rkm128kMask56 6 [63]⟩,
  ⟨4, 23492111, 1, 14, rkm128kMask56 7 [66]⟩,
  ⟨4, 12799167, 1, 10, rkm128kMask56 7 [127]⟩,
  ⟨4, 11226787, 1, 10, rkm128kMask56 8 [223]⟩,
  ⟨4, 7089011, 1, 8, rkm128kMask56 8 [159]⟩,
  ⟨4, 5009266, 1, 6, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 9`. -/
def lm4k512l248krS0RowR9 : List ℕ :=
  [3744287, 8131032, 892, 40881467, 131529284, 79182, 126774483, 162220834308, 837467328730]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 9`. -/
def lm4k512l248krS0AncR9 : RampKick128kAnchor :=
  ⟨9, lm4k512l248krS0SegsR9, lm4k512l248krS0RowR9⟩
/-- Active `RampKick128k` segments for `m = 4, r = 10` (`23` segments). -/
def lm4k512l248krS0SegsR10 : List Rkm128kSeg := [
  ⟨1, 54000085, 1, 12, []⟩,
  ⟨1, 45091104, 1, 12, []⟩,
  ⟨2, 26435543, 1, 12, []⟩,
  ⟨2, 31736903, 1, 12, []⟩,
  ⟨3, 11146535, 1, 10, []⟩,
  ⟨3, 13597938, 1, 10, rkm128kMask56 2 [3]⟩,
  ⟨3, 24539267, 1, 14, rkm128kMask56 4 [13]⟩,
  ⟨4, 14316267, 1, 12, rkm128kMask56 5 [22]⟩,
  ⟨4, 16128122, 1, 12, rkm128kMask56 6 [43]⟩,
  ⟨4, 17810309, 1, 12, rkm128kMask56 7 [92]⟩,
  ⟨4, 10852686, 1, 10, rkm128kMask56 7 [80]⟩,
  ⟨4, 5795463, 1, 8, rkm128kMask56 8 [149]⟩,
  ⟨4, 4141603, 1, 6, rkm128kMask56 8 [130]⟩,
  ⟨4, 3464856, 1, 6, rkm128kMask56 8 [139]⟩,
  ⟨4, 4468609, 1, 8, rkm128kMask56 8 [146]⟩,
  ⟨4, 5525878, 1, 8, rkm128kMask56 7 [125]⟩,
  ⟨4, 5469033, 1, 8, rkm128kMask56 6 [35]⟩,
  ⟨4, 5829647, 1, 8, rkm128kMask56 9 [444]⟩,
  ⟨4, 4785893, 1, 6, rkm128kMask56 8 [143]⟩,
  ⟨4, 925265, 1, 4, rkm128kMask56 9 [336]⟩,
  ⟨4, 2253989, 1, 6, rkm128kMask56 7 [64]⟩,
  ⟨4, 2014624, 1, 6, rkm128kMask56 9 [496]⟩,
  ⟨4, 1945659, 1, 6, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 10`. -/
def lm4k512l248krS0RowR10 : List ℕ :=
  [4, 83070, 42605467, 71817550, 640736, 318691, 2174719, 796376, 166247415690, 833633512631]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 10`. -/
def lm4k512l248krS0AncR10 : RampKick128kAnchor :=
  ⟨10, lm4k512l248krS0SegsR10, lm4k512l248krS0RowR10⟩
/-- Active `RampKick128k` segments for `m = 4, r = 11` (`20` segments). -/
def lm4k512l248krS0SegsR11 : List Rkm128kSeg := [
  ⟨1, 22631550, 1, 10, []⟩,
  ⟨1, 23354538, 1, 10, []⟩,
  ⟨1, 23354537, 1, 10, []⟩,
  ⟨1, 23354538, 1, 10, []⟩,
  ⟨2, 22784012, 1, 12, []⟩,
  ⟨2, 22784013, 1, 12, []⟩,
  ⟨3, 17916542, 1, 12, []⟩,
  ⟨3, 18129709, 1, 12, rkm128kMask56 2 [3]⟩,
  ⟨3, 10948072, 1, 10, rkm128kMask56 3 [5]⟩,
  ⟨4, 10089369, 1, 10, rkm128kMask56 4 [11]⟩,
  ⟨4, 11302535, 1, 10, rkm128kMask56 1 [1]⟩,
  ⟨4, 11171187, 1, 10, rkm128kMask56 6 [55]⟩,
  ⟨4, 17745366, 1, 12, rkm128kMask56 7 [66]⟩,
  ⟨5, 14107591, 1, 12, rkm128kMask56 8 [247]⟩,
  ⟨5, 8711047, 1, 10, rkm128kMask56 2 [2]⟩,
  ⟨5, 9821924, 1, 10, rkm128kMask56 9 [486]⟩,
  ⟨5, 10181577, 1, 10, rkm128kMask56 6 [34]⟩,
  ⟨5, 10667225, 1, 10, rkm128kMask56 10 [566]⟩,
  ⟨5, 3120252, 1, 6, rkm128kMask56 4 [15]⟩,
  ⟨5, 3180044, 1, 6, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 11`. -/
def lm4k512l248krS0RowR11 : List ℕ :=
  [552459, 46511, 1069818, 371086, 13842608, 4856968, 157002835, 358467049, 302508947,
   167746679752, 831414224509]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 11`. -/
def lm4k512l248krS0AncR11 : RampKick128kAnchor :=
  ⟨11, lm4k512l248krS0SegsR11, lm4k512l248krS0RowR11⟩
/-- Active `RampKick128k` segments for `m = 4, r = 12` (`20` segments). -/
def lm4k512l248krS0SegsR12 : List Rkm128kSeg := [
  ⟨1, 20242769, 1, 8, []⟩,
  ⟨1, 23419980, 1, 10, []⟩,
  ⟨1, 23274683, 1, 10, []⟩,
  ⟨1, 22209185, 1, 10, []⟩,
  ⟨2, 23030855, 1, 12, []⟩,
  ⟨2, 23030855, 1, 12, []⟩,
  ⟨3, 18613916, 1, 12, []⟩,
  ⟨3, 18613917, 1, 12, rkm128kMask56 2 [2]⟩,
  ⟨4, 11729577, 1, 12, rkm128kMask56 4 [9]⟩,
  ⟨4, 11254432, 1, 10, rkm128kMask56 5 [30]⟩,
  ⟨4, 11814671, 1, 12, rkm128kMask56 5 [25]⟩,
  ⟨5, 12016583, 1, 12, rkm128kMask56 7 [110]⟩,
  ⟨5, 14917285, 1, 12, rkm128kMask56 8 [129]⟩,
  ⟨5, 13670482, 1, 12, rkm128kMask56 9 [471]⟩,
  ⟨5, 8461580, 1, 10, rkm128kMask56 6 [39]⟩,
  ⟨5, 9866078, 1, 10, rkm128kMask56 10 [986]⟩,
  ⟨5, 9050677, 1, 10, rkm128kMask56 7 [73]⟩,
  ⟨6, 9914037, 1, 10, rkm128kMask56 11 [1047]⟩,
  ⟨6, 2273147, 1, 6, []⟩,
  ⟨6, 2853330, 1, 6, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 12`. -/
def lm4k512l248krS0RowR12 : List ℕ :=
  [2, 442517, 25499166, 10125550, 39322895, 30971728, 34403660, 190483684, 671311639, 296694613,
   171030106303, 827669944894]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 12`. -/
def lm4k512l248krS0AncR12 : RampKick128kAnchor :=
  ⟨12, lm4k512l248krS0SegsR12, lm4k512l248krS0RowR12⟩
/-- Active `RampKick128k` segments for `m = 4, r = 13` (`20` segments). -/
def lm4k512l248krS0SegsR13 : List Rkm128kSeg := [
  ⟨1, 38359701, 1, 12, []⟩,
  ⟨1, 38118351, 1, 12, []⟩,
  ⟨2, 22968526, 1, 12, []⟩,
  ⟨2, 26496581, 1, 12, []⟩,
  ⟨3, 22405521, 1, 14, []⟩,
  ⟨4, 17761800, 1, 14, rkm128kMask56 3 [6]⟩,
  ⟨4, 19039832, 1, 13, rkm128kMask56 5 [21]⟩,
  ⟨5, 18028536, 1, 15, rkm128kMask56 7 [105]⟩,
  ⟨5, 22594381, 1, 17, rkm128kMask56 9 [381]⟩,
  ⟨6, 13787868, 1, 14, rkm128kMask56 10 [979]⟩,
  ⟨6, 16416612, 1, 15, rkm128kMask56 11 [1034]⟩,
  ⟨6, 11222316, 1, 12, rkm128kMask56 8 [239]⟩,
  ⟨6, 3822952, 1, 8, rkm128kMask56 12 [2296]⟩,
  ⟨6, 3611198, 1, 8, rkm128kMask56 12 [3287]⟩,
  ⟨6, 1222298, 1, 6, rkm128kMask56 12 [2104]⟩,
  ⟨6, 203798, 1, 4, rkm128kMask56 9 [264]⟩,
  ⟨6, 411808, 1, 4, rkm128kMask56 9 [297]⟩,
  ⟨6, 80385, 1, 4, rkm128kMask56 12 [2458]⟩,
  ⟨6, 224959, 1, 4, rkm128kMask56 9 [259]⟩,
  ⟨6, 75181, 1, 4, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 13`. -/
def lm4k512l248krS0RowR13 : List ℕ :=
  [292466, 28764, 233970, 9991461, 68126148, 392649131, 128625821, 67214260, 1757064353,
   670145764, 642256, 169253017066, 827651548866]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 13`. -/
def lm4k512l248krS0AncR13 : RampKick128kAnchor :=
  ⟨13, lm4k512l248krS0SegsR13, lm4k512l248krS0RowR13⟩
/-- Active `RampKick128k` segments for `m = 4, r = 14` (`25` segments). -/
def lm4k512l248krS0SegsR14 : List Rkm128kSeg := [
  ⟨1, 44180081, 1, 12, []⟩,
  ⟨1, 34959618, 1, 12, []⟩,
  ⟨2, 14970506, 1, 10, []⟩,
  ⟨2, 22282003, 1, 12, []⟩,
  ⟨3, 27869849, 1, 15, []⟩,
  ⟨4, 24430201, 1, 17, rkm128kMask56 4 [14]⟩,
  ⟨4, 8827330, 1, 10, rkm128kMask56 5 [22]⟩,
  ⟨5, 9163852, 1, 12, rkm128kMask56 6 [35]⟩,
  ⟨5, 9180083, 1, 12, rkm128kMask56 7 [93]⟩,
  ⟨5, 10335067, 1, 12, rkm128kMask56 8 [130]⟩,
  ⟨6, 10016132, 1, 12, rkm128kMask56 9 [284]⟩,
  ⟨6, 5726009, 1, 10, rkm128kMask56 9 [461]⟩,
  ⟨6, 5088523, 1, 8, rkm128kMask56 10 [842]⟩,
  ⟨6, 6494078, 1, 10, rkm128kMask56 9 [439]⟩,
  ⟨6, 5732332, 1, 10, rkm128kMask56 11 [1143]⟩,
  ⟨6, 6227657, 1, 10, rkm128kMask56 11 [1024]⟩,
  ⟨6, 6080894, 1, 10, rkm128kMask56 12 [2819]⟩,
  ⟨6, 5105225, 1, 8, rkm128kMask56 12 [3584]⟩,
  ⟨6, 3143708, 1, 8, rkm128kMask56 11 [1480]⟩,
  ⟨6, 3927566, 1, 8, rkm128kMask56 12 [4009]⟩,
  ⟨6, 4839381, 1, 8, rkm128kMask56 13 [4152]⟩,
  ⟨6, 2038687, 1, 6, rkm128kMask56 13 [8042]⟩,
  ⟨6, 2241326, 1, 6, rkm128kMask56 13 [7884]⟩,
  ⟨6, 2187942, 1, 6, rkm128kMask56 13 [5077]⟩,
  ⟨6, 1232636, 1, 6, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 14`. -/
def lm4k512l248krS0RowR14 : List ℕ :=
  [543492, 5041408, 1242754, 15797369, 2501037, 11302193, 6973575, 22500055, 10803139, 14633292,
   54012, 5086354, 170931688605, 828969336432]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 14`. -/
def lm4k512l248krS0AncR14 : RampKick128kAnchor :=
  ⟨14, lm4k512l248krS0SegsR14, lm4k512l248krS0RowR14⟩
/-- Active `RampKick128k` segments for `m = 4, r = 15` (`36` segments). -/
def lm4k512l248krS0SegsR15 : List Rkm128kSeg := [
  ⟨1, 16454406, 1, 8, []⟩,
  ⟨1, 17001821, 1, 8, []⟩,
  ⟨1, 16882778, 1, 8, []⟩,
  ⟨1, 16882778, 1, 8, []⟩,
  ⟨1, 16882776, 1, 8, []⟩,
  ⟨2, 13782232, 1, 10, []⟩,
  ⟨2, 12128701, 1, 10, []⟩,
  ⟨2, 11937927, 1, 10, []⟩,
  ⟨3, 9520277, 1, 10, []⟩,
  ⟨3, 9737224, 1, 10, []⟩,
  ⟨3, 10516200, 1, 10, rkm128kMask56 2 [2]⟩,
  ⟨4, 9107298, 1, 10, rkm128kMask56 2 [3]⟩,
  ⟨4, 13652755, 1, 12, rkm128kMask56 5 [27]⟩,
  ⟨5, 8982893, 1, 12, rkm128kMask56 6 [37]⟩,
  ⟨5, 9648708, 1, 12, rkm128kMask56 7 [68]⟩,
  ⟨6, 8688324, 1, 12, rkm128kMask56 8 [130]⟩,
  ⟨6, 9346809, 1, 12, rkm128kMask56 9 [266]⟩,
  ⟨6, 10159135, 1, 12, rkm128kMask56 10 [518]⟩,
  ⟨6, 5606071, 1, 10, rkm128kMask56 8 [211]⟩,
  ⟨6, 5555720, 1, 10, rkm128kMask56 11 [1062]⟩,
  ⟨7, 5628284, 1, 10, rkm128kMask56 10 [928]⟩,
  ⟨7, 4809057, 1, 10, rkm128kMask56 12 [2185]⟩,
  ⟨7, 5391348, 1, 10, rkm128kMask56 12 [2090]⟩,
  ⟨7, 5353873, 1, 10, rkm128kMask56 13 [5962]⟩,
  ⟨7, 2338879, 1, 6, rkm128kMask56 4 [8]⟩,
  ⟨7, 2030135, 1, 6, rkm128kMask56 13 [4331]⟩,
  ⟨7, 1547519, 1, 6, rkm128kMask56 12 [3088]⟩,
  ⟨7, 1542073, 1, 6, rkm128kMask56 10 [781]⟩,
  ⟨7, 3511744, 1, 8, rkm128kMask56 13 [5577]⟩,
  ⟨7, 3858057, 1, 8, rkm128kMask56 14 [14928]⟩,
  ⟨7, 1254115, 1, 6, rkm128kMask56 14 [8351]⟩,
  ⟨7, 880878, 1, 6, rkm128kMask56 14 [9009]⟩,
  ⟨7, 1089382, 1, 6, rkm128kMask56 14 [9094]⟩,
  ⟨7, 1947573, 1, 6, rkm128kMask56 14 [12401]⟩,
  ⟨7, 920314, 1, 6, rkm128kMask56 5 [31]⟩,
  ⟨8, 371918, 1, 4, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 15`. -/
def lm4k512l248krS0RowR15 : List ℕ :=
  [20354, 631996, 12415, 478098, 6187480, 1481578, 9780993, 9788671, 4748810, 1807069, 3057,
   1158131, 8516555, 170771635208, 829182875907]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 15`. -/
def lm4k512l248krS0AncR15 : RampKick128kAnchor :=
  ⟨15, lm4k512l248krS0SegsR15, lm4k512l248krS0RowR15⟩
/-- Active `RampKick128k` segments for `m = 4, r = 16` (`36` segments). -/
def lm4k512l248krS0SegsR16 : List Rkm128kSeg := [
  ⟨1, 20440386, 1, 10, []⟩,
  ⟨1, 17403009, 1, 10, []⟩,
  ⟨1, 17219889, 1, 8, []⟩,
  ⟨1, 17219889, 1, 8, []⟩,
  ⟨2, 10682325, 1, 10, []⟩,
  ⟨2, 11744679, 1, 10, []⟩,
  ⟨2, 11744678, 1, 10, []⟩,
  ⟨2, 11744679, 1, 10, []⟩,
  ⟨3, 11057307, 1, 10, []⟩,
  ⟨3, 8955456, 1, 10, []⟩,
  ⟨3, 9201717, 1, 10, rkm128kMask56 2 [2]⟩,
  ⟨4, 8185035, 1, 10, rkm128kMask56 3 [5]⟩,
  ⟨4, 9554498, 1, 10, rkm128kMask56 4 [8]⟩,
  ⟨5, 10032030, 1, 12, rkm128kMask56 6 [40]⟩,
  ⟨5, 8545803, 1, 12, rkm128kMask56 7 [71]⟩,
  ⟨5, 9288917, 1, 12, rkm128kMask56 8 [223]⟩,
  ⟨6, 9253418, 1, 12, rkm128kMask56 9 [340]⟩,
  ⟨6, 9413073, 1, 12, rkm128kMask56 10 [640]⟩,
  ⟨7, 8430568, 1, 12, rkm128kMask56 10 [777]⟩,
  ⟨7, 8331768, 1, 12, rkm128kMask56 12 [3309]⟩,
  ⟨7, 6265860, 1, 10, rkm128kMask56 10 [768]⟩,
  ⟨7, 6693410, 1, 10, rkm128kMask56 13 [4696]⟩,
  ⟨7, 6080173, 1, 10, rkm128kMask56 4 [8]⟩,
  ⟨7, 6297382, 1, 10, rkm128kMask56 14 [11080]⟩,
  ⟨7, 3821088, 1, 8, rkm128kMask56 11 [1303]⟩,
  ⟨7, 3968584, 1, 8, rkm128kMask56 14 [13847]⟩,
  ⟨8, 2211073, 1, 6, []⟩,
  ⟨8, 2128397, 1, 6, rkm128kMask56 15 [17639]⟩,
  ⟨8, 1081648, 1, 6, []⟩,
  ⟨8, 1117325, 1, 6, rkm128kMask56 15 [18395]⟩,
  ⟨8, 312920, 1, 4, rkm128kMask56 7 [67]⟩,
  ⟨8, 302175, 1, 4, rkm128kMask56 10 [1022]⟩,
  ⟨8, 666552, 1, 4, rkm128kMask56 7 [73]⟩,
  ⟨8, 655247, 1, 4, rkm128kMask56 15 [16421]⟩,
  ⟨8, 492846, 1, 4, rkm128kMask56 2 [2]⟩,
  ⟨8, 529408, 1, 4, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 16`. -/
def lm4k512l248krS0RowR16 : List ℕ :=
  [26316, 1277894, 620449, 11210559, 14139417, 740229, 6652430, 15750152, 463475649, 339391849,
   976266952, 858192250, 169154758, 7411936, 172677626844, 824456584905]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 16`. -/
def lm4k512l248krS0AncR16 : RampKick128kAnchor :=
  ⟨16, lm4k512l248krS0SegsR16, lm4k512l248krS0RowR16⟩
/-- Active `RampKick128k` segments for `m = 4, r = 17` (`39` segments). -/
def lm4k512l248krS0SegsR17 : List Rkm128kSeg := [
  ⟨1, 17849971, 1, 10, []⟩,
  ⟨1, 16523280, 1, 8, []⟩,
  ⟨1, 16557807, 1, 8, []⟩,
  ⟨1, 16320125, 1, 8, []⟩,
  ⟨2, 9158826, 1, 8, []⟩,
  ⟨2, 11373611, 1, 10, []⟩,
  ⟨2, 11540071, 1, 10, []⟩,
  ⟨3, 7742900, 1, 10, []⟩,
  ⟨3, 9051482, 1, 10, []⟩,
  ⟨3, 10051475, 1, 10, []⟩,
  ⟨4, 8333038, 1, 10, []⟩,
  ⟨4, 8128890, 1, 10, rkm128kMask56 2 [2]⟩,
  ⟨4, 13108561, 1, 12, rkm128kMask56 4 [10]⟩,
  ⟨5, 10045014, 1, 12, rkm128kMask56 6 [54]⟩,
  ⟨5, 7796782, 1, 10, rkm128kMask56 7 [80]⟩,
  ⟨6, 7198464, 1, 12, rkm128kMask56 8 [172]⟩,
  ⟨6, 7311565, 1, 12, rkm128kMask56 8 [167]⟩,
  ⟨6, 6990595, 1, 10, rkm128kMask56 10 [802]⟩,
  ⟨7, 8869830, 1, 12, rkm128kMask56 11 [1291]⟩,
  ⟨7, 7721699, 1, 12, rkm128kMask56 12 [3938]⟩,
  ⟨7, 3657196, 1, 8, rkm128kMask56 12 [3270]⟩,
  ⟨7, 4973208, 1, 10, rkm128kMask56 13 [4589]⟩,
  ⟨8, 3424973, 1, 8, rkm128kMask56 13 [5894]⟩,
  ⟨8, 5394881, 1, 10, rkm128kMask56 14 [11135]⟩,
  ⟨8, 1817728, 1, 6, rkm128kMask56 6 [35]⟩,
  ⟨8, 1751532, 1, 6, rkm128kMask56 14 [10436]⟩,
  ⟨8, 5408226, 1, 10, rkm128kMask56 13 [6171]⟩,
  ⟨8, 655391, 1, 6, rkm128kMask56 8 [183]⟩,
  ⟨8, 591202, 1, 4, rkm128kMask56 15 [22689]⟩,
  ⟨8, 1495684, 1, 6, rkm128kMask56 15 [28670]⟩,
  ⟨8, 4215729, 1, 8, rkm128kMask56 15 [25547]⟩,
  ⟨8, 3956514, 1, 8, rkm128kMask56 13 [7397]⟩,
  ⟨8, 4408476, 1, 8, rkm128kMask56 16 [51214]⟩,
  ⟨8, 1264815, 1, 6, rkm128kMask56 16 [38949]⟩,
  ⟨8, 429394, 1, 4, rkm128kMask56 9 [286]⟩,
  ⟨8, 478258, 1, 4, rkm128kMask56 16 [49367]⟩,
  ⟨8, 915322, 1, 6, rkm128kMask56 15 [16623]⟩,
  ⟨8, 694123, 1, 6, rkm128kMask56 16 [37316]⟩,
  ⟨8, 1361504, 1, 6, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 17`. -/
def lm4k512l248krS0RowR17 : List ℕ :=
  [1778, 564259, 284051, 414893, 1088840, 9233, 38589540, 14054, 99466848, 201572725, 811306080,
   143118337, 22725304, 6610983, 25039837, 172799679308, 825847313337]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 17`. -/
def lm4k512l248krS0AncR17 : RampKick128kAnchor :=
  ⟨17, lm4k512l248krS0SegsR17, lm4k512l248krS0RowR17⟩
/-- Active `RampKick128k` segments for `m = 4, r = 18` (`26` segments). -/
def lm4k512l248krS0SegsR18 : List Rkm128kSeg := [
  ⟨1, 36990421, 1, 12, []⟩,
  ⟨1, 34062896, 1, 12, []⟩,
  ⟨2, 24731932, 1, 14, []⟩,
  ⟨3, 18175901, 1, 14, []⟩,
  ⟨3, 18615837, 1, 13, []⟩,
  ⟨4, 17342716, 1, 15, rkm128kMask56 4 [13]⟩,
  ⟨5, 12906177, 1, 13, rkm128kMask56 6 [52]⟩,
  ⟨6, 11121187, 1, 14, rkm128kMask56 8 [225]⟩,
  ⟨6, 8191645, 1, 12, rkm128kMask56 9 [431]⟩,
  ⟨6, 8677695, 1, 12, rkm128kMask56 10 [530]⟩,
  ⟨7, 7564051, 1, 12, rkm128kMask56 11 [1086]⟩,
  ⟨7, 7547677, 1, 12, rkm128kMask56 12 [2138]⟩,
  ⟨8, 7304187, 1, 12, rkm128kMask56 13 [8093]⟩,
  ⟨8, 7726445, 1, 12, rkm128kMask56 14 [16261]⟩,
  ⟨8, 4701339, 1, 10, rkm128kMask56 13 [7838]⟩,
  ⟨8, 5653655, 1, 10, rkm128kMask56 15 [32550]⟩,
  ⟨8, 5921488, 1, 10, rkm128kMask56 11 [1842]⟩,
  ⟨8, 5959281, 1, 10, rkm128kMask56 16 [38802]⟩,
  ⟨8, 4288933, 1, 10, rkm128kMask56 13 [6575]⟩,
  ⟨9, 3935971, 1, 10, rkm128kMask56 16 [37336]⟩,
  ⟨9, 1426141, 1, 6, rkm128kMask56 17 [122504]⟩,
  ⟨9, 1264642, 1, 6, rkm128kMask56 17 [119792]⟩,
  ⟨9, 898791, 1, 6, rkm128kMask56 11 [1056]⟩,
  ⟨9, 840528, 1, 6, rkm128kMask56 17 [66159]⟩,
  ⟨9, 1402850, 1, 6, rkm128kMask56 17 [100944]⟩,
  ⟨10, 283344, 1, 4, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 18`. -/
def lm4k512l248krS0RowR18 : List ℕ :=
  [2890, 12132, 153645, 45645503, 91806, 96290959, 127843547, 99244528, 22323111, 11950789,
   27466635, 70925878, 866, 253800548, 28212516, 3535568, 174546730187, 824665011943]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 18`. -/
def lm4k512l248krS0AncR18 : RampKick128kAnchor :=
  ⟨18, lm4k512l248krS0SegsR18, lm4k512l248krS0RowR18⟩
/-- Active `RampKick128k` segments for `m = 4, r = 19` (`26` segments). -/
def lm4k512l248krS0SegsR19 : List Rkm128kSeg := [
  ⟨1, 31185028, 1, 12, []⟩,
  ⟨1, 32353568, 1, 12, []⟩,
  ⟨2, 25112947, 1, 13, []⟩,
  ⟨3, 17050119, 1, 14, []⟩,
  ⟨3, 17180634, 1, 14, []⟩,
  ⟨4, 18265978, 1, 15, rkm128kMask56 3 [6]⟩,
  ⟨5, 14208330, 1, 15, rkm128kMask56 6 [49]⟩,
  ⟨6, 12548758, 1, 15, rkm128kMask56 8 [206]⟩,
  ⟨6, 12725840, 1, 15, rkm128kMask56 10 [853]⟩,
  ⟨7, 7296063, 1, 12, rkm128kMask56 11 [1096]⟩,
  ⟨7, 7431939, 1, 12, rkm128kMask56 12 [3048]⟩,
  ⟨8, 6613957, 1, 12, rkm128kMask56 13 [5782]⟩,
  ⟨8, 7588578, 1, 12, rkm128kMask56 14 [11866]⟩,
  ⟨8, 8510239, 1, 12, rkm128kMask56 15 [25908]⟩,
  ⟨9, 3706610, 1, 10, rkm128kMask56 15 [18327]⟩,
  ⟨9, 4494628, 1, 10, rkm128kMask56 16 [62441]⟩,
  ⟨9, 5294534, 1, 10, rkm128kMask56 16 [35589]⟩,
  ⟨9, 4367855, 1, 10, rkm128kMask56 17 [67409]⟩,
  ⟨9, 5111114, 1, 10, rkm128kMask56 17 [71649]⟩,
  ⟨9, 2951453, 1, 8, rkm128kMask56 18 [258608]⟩,
  ⟨9, 282342, 1, 4, rkm128kMask56 18 [242316]⟩,
  ⟨9, 973225, 1, 6, rkm128kMask56 16 [43200]⟩,
  ⟨9, 1101627, 1, 6, rkm128kMask56 18 [261647]⟩,
  ⟨9, 1482694, 1, 6, rkm128kMask56 18 [188976]⟩,
  ⟨9, 2323158, 1, 8, rkm128kMask56 18 [238320]⟩,
  ⟨10, 573440, 1, 6, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 19`. -/
def lm4k512l248krS0RowR19 : List ℕ :=
  [969, 5903, 9843426, 2661760, 1078769, 8452724, 1275348, 179501, 13553175, 272281502,
   270208309, 124030136, 5824786, 121638600, 270854987, 12994668, 43605821, 174220017081,
   824620766305]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 19`. -/
def lm4k512l248krS0AncR19 : RampKick128kAnchor :=
  ⟨19, lm4k512l248krS0SegsR19, lm4k512l248krS0RowR19⟩
/-- Active `RampKick128k` segments for `m = 4, r = 20` (`30` segments). -/
def lm4k512l248krS0SegsR20 : List Rkm128kSeg := [
  ⟨1, 15843686, 1, 8, []⟩,
  ⟨1, 16914548, 1, 10, []⟩,
  ⟨1, 15802081, 1, 10, []⟩,
  ⟨1, 15802082, 1, 10, []⟩,
  ⟨2, 12500532, 1, 10, []⟩,
  ⟨2, 11112746, 1, 10, []⟩,
  ⟨2, 11173758, 1, 10, []⟩,
  ⟨3, 9496498, 1, 10, []⟩,
  ⟨4, 16494632, 1, 15, []⟩,
  ⟨4, 18552821, 1, 15, rkm128kMask56 4 [12]⟩,
  ⟨6, 13050584, 1, 15, rkm128kMask56 7 [102]⟩,
  ⟨6, 12746205, 1, 15, rkm128kMask56 9 [404]⟩,
  ⟨7, 12699582, 1, 17, rkm128kMask56 11 [1576]⟩,
  ⟨8, 6352898, 1, 12, rkm128kMask56 12 [2935]⟩,
  ⟨8, 5936890, 1, 12, rkm128kMask56 13 [5057]⟩,
  ⟨8, 6847580, 1, 12, rkm128kMask56 14 [15984]⟩,
  ⟨9, 6444851, 1, 12, rkm128kMask56 15 [16866]⟩,
  ⟨9, 7751529, 1, 12, rkm128kMask56 16 [63879]⟩,
  ⟨9, 4182072, 1, 10, rkm128kMask56 10 [1002]⟩,
  ⟨9, 4596622, 1, 10, rkm128kMask56 17 [78561]⟩,
  ⟨9, 4726334, 1, 10, rkm128kMask56 16 [61964]⟩,
  ⟨9, 4292544, 1, 10, rkm128kMask56 18 [204235]⟩,
  ⟨9, 4446679, 1, 10, rkm128kMask56 18 [222156]⟩,
  ⟨10, 3374008, 1, 10, rkm128kMask56 18 [218796]⟩,
  ⟨10, 1209154, 1, 6, rkm128kMask56 19 [340365]⟩,
  ⟨10, 665055, 1, 6, rkm128kMask56 19 [374815]⟩,
  ⟨10, 801448, 1, 6, rkm128kMask56 14 [9660]⟩,
  ⟨10, 856471, 1, 6, rkm128kMask56 19 [518740]⟩,
  ⟨10, 1571689, 1, 6, rkm128kMask56 19 [263613]⟩,
  ⟨10, 884755, 1, 6, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 20`. -/
def lm4k512l248krS0RowR20 : List ℕ :=
  [1944, 1195, 3326, 1206321, 981115, 1804217, 872001, 131217801, 6224628, 38480324, 37857878,
   148186102, 47241835, 808627500, 435789765, 35828376, 10366907, 3738558, 174949166086,
   823341447632]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 20`. -/
def lm4k512l248krS0AncR20 : RampKick128kAnchor :=
  ⟨20, lm4k512l248krS0SegsR20, lm4k512l248krS0RowR20⟩
/-- Active `RampKick128k` segments for `m = 4, r = 21` (`29` segments). -/
def lm4k512l248krS0SegsR21 : List Rkm128kSeg := [
  ⟨1, 33536851, 1, 12, []⟩,
  ⟨1, 30811800, 1, 12, []⟩,
  ⟨2, 22237858, 1, 14, []⟩,
  ⟨3, 15153428, 1, 14, []⟩,
  ⟨4, 16751692, 1, 15, []⟩,
  ⟨4, 19010067, 1, 17, rkm128kMask56 3 [6]⟩,
  ⟨5, 9804503, 1, 12, rkm128kMask56 6 [48]⟩,
  ⟨6, 7235534, 1, 12, rkm128kMask56 7 [65]⟩,
  ⟨6, 8933927, 1, 14, rkm128kMask56 9 [344]⟩,
  ⟨7, 7066397, 1, 12, rkm128kMask56 10 [980]⟩,
  ⟨7, 5798296, 1, 12, rkm128kMask56 11 [1217]⟩,
  ⟨8, 5374745, 1, 12, rkm128kMask56 12 [2451]⟩,
  ⟨8, 5630014, 1, 12, rkm128kMask56 13 [8191]⟩,
  ⟨8, 6130584, 1, 12, rkm128kMask56 14 [15970]⟩,
  ⟨9, 6263887, 1, 12, rkm128kMask56 15 [32532]⟩,
  ⟨9, 6781651, 1, 12, rkm128kMask56 16 [61808]⟩,
  ⟨9, 7480076, 1, 12, rkm128kMask56 17 [127112]⟩,
  ⟨10, 2654999, 1, 8, rkm128kMask56 13 [5369]⟩,
  ⟨10, 3510945, 1, 10, rkm128kMask56 18 [140810]⟩,
  ⟨10, 3170081, 1, 10, rkm128kMask56 18 [233547]⟩,
  ⟨10, 4241756, 1, 10, rkm128kMask56 18 [240984]⟩,
  ⟨10, 3372276, 1, 10, rkm128kMask56 19 [516805]⟩,
  ⟨10, 5751130, 1, 12, rkm128kMask56 17 [98173]⟩,
  ⟨10, 1524660, 1, 6, rkm128kMask56 20 [1048098]⟩,
  ⟨10, 487547, 1, 4, rkm128kMask56 20 [692014]⟩,
  ⟨10, 683379, 1, 6, rkm128kMask56 17 [98243]⟩,
  ⟨10, 805305, 1, 6, rkm128kMask56 20 [869853]⟩,
  ⟨10, 1405577, 1, 6, rkm128kMask56 20 [658396]⟩,
  ⟨10, 1847750, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 21`. -/
def lm4k512l248krS0RowR21 : List ℕ :=
  [22267, 909635, 7572604, 844953, 3118592, 721219, 92476, 8044062, 2004909, 62148655, 2774331,
   16336717, 60322966, 38030329, 26776, 79235024, 86509038, 984030, 180217403, 174041180967,
   825408023402]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 21`. -/
def lm4k512l248krS0AncR21 : RampKick128kAnchor :=
  ⟨21, lm4k512l248krS0SegsR21, lm4k512l248krS0RowR21⟩
/-- Active `RampKick128k` segments for `m = 4, r = 23` (`37` segments). -/
def lm4k512l248krS0SegsR23 : List Rkm128kSeg := [
  ⟨1, 11568258, 1, 8, []⟩,
  ⟨1, 14166691, 1, 8, []⟩,
  ⟨1, 14166691, 1, 10, []⟩,
  ⟨1, 14166691, 1, 8, []⟩,
  ⟨2, 7786760, 1, 8, []⟩,
  ⟨2, 7326398, 1, 8, []⟩,
  ⟨2, 7618500, 1, 8, []⟩,
  ⟨2, 7618500, 1, 8, []⟩,
  ⟨3, 14698607, 1, 14, []⟩,
  ⟨3, 14698607, 1, 14, []⟩,
  ⟨4, 11788174, 1, 14, rkm128kMask56 2 [2]⟩,
  ⟨5, 10888380, 1, 13, rkm128kMask56 5 [27]⟩,
  ⟨6, 9625005, 1, 13, rkm128kMask56 23 [4194329]⟩,
  ⟨6, 9028717, 1, 14, rkm128kMask56 9 [478]⟩,
  ⟨7, 7152518, 1, 12, rkm128kMask56 10 [579]⟩,
  ⟨8, 6352262, 1, 12, rkm128kMask56 5 [30]⟩,
  ⟨8, 6386520, 1, 12, rkm128kMask56 13 [4450]⟩,
  ⟨9, 6170865, 1, 14, rkm128kMask56 14 [12899]⟩,
  ⟨9, 6987111, 1, 14, rkm128kMask56 9 [430]⟩,
  ⟨10, 8997763, 1, 15, rkm128kMask56 17 [104099]⟩,
  ⟨10, 4138284, 1, 10, rkm128kMask56 12 [2282]⟩,
  ⟨10, 4523954, 1, 12, rkm128kMask56 14 [14977]⟩,
  ⟨10, 5114019, 1, 12, rkm128kMask56 10 [574]⟩,
  ⟨11, 4782264, 1, 12, rkm128kMask56 20 [728435]⟩,
  ⟨11, 4578819, 1, 12, rkm128kMask56 10 [593]⟩,
  ⟨11, 4769641, 1, 12, rkm128kMask56 21 [1999013]⟩,
  ⟨11, 2797083, 1, 10, rkm128kMask56 13 [5203]⟩,
  ⟨11, 2119786, 1, 8, rkm128kMask56 18 [204290]⟩,
  ⟨11, 2643337, 1, 8, rkm128kMask56 19 [262299]⟩,
  ⟨11, 1549966, 1, 8, rkm128kMask56 22 [2520726]⟩,
  ⟨11, 1000, 1, 4, rkm128kMask56 22 [2232770]⟩,
  ⟨11, 22747, 1, 4, rkm128kMask56 8 [130]⟩,
  ⟨11, 22408, 1, 4, rkm128kMask56 22 [2326390]⟩,
  ⟨11, 657968, 1, 6, rkm128kMask56 10 [512]⟩,
  ⟨11, 704192, 1, 6, rkm128kMask56 22 [2099976]⟩,
  ⟨11, 729240, 1, 6, []⟩,
  ⟨11, 633902, 1, 6, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 23`. -/
def lm4k512l248krS0RowR23 : List ℕ :=
  [200, 9516, 0, 509143, 6304562, 46145, 5590261, 91117056, 6122434, 56788548, 6259097,
   28568437, 5529738, 423878663, 2106977085, 9531659, 44489022, 61873784, 3159022342,
   10160750572, 11654027, 176637175917, 807175778264]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 23`. -/
def lm4k512l248krS0AncR23 : RampKick128kAnchor :=
  ⟨23, lm4k512l248krS0SegsR23, lm4k512l248krS0RowR23⟩
/-- Active `RampKick128k` segments for `m = 4, r = 25` (`32` segments). -/
def lm4k512l248krS0SegsR25 : List Rkm128kSeg := [
  ⟨1, 13378222, 1, 8, []⟩,
  ⟨1, 11182078, 1, 8, []⟩,
  ⟨1, 10951419, 1, 8, []⟩,
  ⟨1, 10712740, 1, 8, []⟩,
  ⟨2, 5697142, 1, 8, []⟩,
  ⟨2, 7715262, 1, 8, []⟩,
  ⟨2, 7819743, 1, 10, []⟩,
  ⟨2, 7819743, 1, 10, []⟩,
  ⟨3, 11507166, 1, 12, []⟩,
  ⟨3, 11507166, 1, 12, []⟩,
  ⟨4, 9608839, 1, 12, []⟩,
  ⟨5, 8594408, 1, 12, rkm128kMask56 1 [1]⟩,
  ⟨6, 10478382, 1, 15, rkm128kMask56 25 [16777232]⟩,
  ⟨6, 10478383, 1, 15, rkm128kMask56 25 [16777338]⟩,
  ⟨7, 9809205, 1, 15, rkm128kMask56 25 [16777754]⟩,
  ⟨8, 8682123, 1, 15, rkm128kMask56 26 [33557911]⟩,
  ⟨9, 6564032, 1, 14, rkm128kMask56 26 [33559565]⟩,
  ⟨9, 8928413, 1, 15, rkm128kMask56 7 [102]⟩,
  ⟨10, 6626038, 1, 15, rkm128kMask56 17 [65699]⟩,
  ⟨11, 5233710, 1, 14, rkm128kMask56 18 [215636]⟩,
  ⟨11, 5786725, 1, 14, rkm128kMask56 19 [262560]⟩,
  ⟨11, 5438494, 1, 12, rkm128kMask56 15 [25610]⟩,
  ⟨11, 5494491, 1, 12, rkm128kMask56 19 [262422]⟩,
  ⟨12, 5199442, 1, 12, rkm128kMask56 22 [3661846]⟩,
  ⟨12, 5261661, 1, 12, rkm128kMask56 20 [694880]⟩,
  ⟨12, 4554529, 1, 12, rkm128kMask56 24 [14218651]⟩,
  ⟨12, 122312, 1, 4, rkm128kMask56 8 [160]⟩,
  ⟨12, 111908, 1, 4, rkm128kMask56 24 [10245985]⟩,
  ⟨12, 2722530, 1, 10, rkm128kMask56 14 [8405]⟩,
  ⟨12, 2714066, 1, 10, rkm128kMask56 21 [2047848]⟩,
  ⟨12, 1910670, 1, 8, rkm128kMask56 21 [1050781]⟩,
  ⟨12, 1000558, 1, 6, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 25`. -/
def lm4k512l248krS0RowR25 : List ℕ :=
  [231582, 443329, 1241375, 77195, 38662, 620458, 472244, 44276663, 1057129, 31585885, 62581611,
   8788675, 157753797, 15344150, 273412833, 1131298, 155871327, 3615735602, 4287053736,
   77403278, 3811029726, 3754988970, 3951977623, 189993439322, 789751911546]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 25`. -/
def lm4k512l248krS0AncR25 : RampKick128kAnchor :=
  ⟨25, lm4k512l248krS0SegsR25, lm4k512l248krS0RowR25⟩
/-- Active `RampKick128k` segments for `m = 4, r = 27` (`30` segments). -/
def lm4k512l248krS0SegsR27 : List Rkm128kSeg := [
  ⟨1, 22218496, 1, 10, []⟩,
  ⟨1, 18716436, 1, 10, []⟩,
  ⟨1, 17606685, 1, 10, []⟩,
  ⟨2, 15221979, 1, 12, []⟩,
  ⟨3, 19208209, 1, 15, []⟩,
  ⟨4, 16021803, 1, 17, rkm128kMask56 2 [2]⟩,
  ⟨5, 14370388, 1, 16, rkm128kMask56 3 [6]⟩,
  ⟨6, 13437477, 1, 18, rkm128kMask56 8 [200]⟩,
  ⟨7, 4574185, 1, 12, rkm128kMask56 9 [458]⟩,
  ⟨7, 4016133, 1, 10, rkm128kMask56 10 [946]⟩,
  ⟨8, 4493306, 1, 12, rkm128kMask56 11 [1167]⟩,
  ⟨8, 4982058, 1, 12, rkm128kMask56 12 [2531]⟩,
  ⟨9, 7263936, 1, 15, rkm128kMask56 14 [8831]⟩,
  ⟨10, 7596606, 1, 15, rkm128kMask56 16 [54359]⟩,
  ⟨10, 5588879, 1, 14, rkm128kMask56 17 [123271]⟩,
  ⟨11, 7176540, 1, 15, rkm128kMask56 19 [484476]⟩,
  ⟨12, 4715893, 1, 12, rkm128kMask56 20 [937536]⟩,
  ⟨12, 4765684, 1, 12, rkm128kMask56 21 [2039176]⟩,
  ⟨12, 5403943, 1, 13, rkm128kMask56 22 [2114669]⟩,
  ⟨12, 5521762, 1, 13, rkm128kMask56 23 [5239776]⟩,
  ⟨13, 5707740, 1, 15, rkm128kMask56 24 [8586380]⟩,
  ⟨13, 3259094, 1, 10, rkm128kMask56 24 [14018405]⟩,
  ⟨13, 2545689, 1, 10, rkm128kMask56 25 [24309546]⟩,
  ⟨13, 2876964, 1, 10, rkm128kMask56 25 [28951737]⟩,
  ⟨13, 4537642, 1, 12, rkm128kMask56 26 [67101973]⟩,
  ⟨13, 965498, 1, 6, rkm128kMask56 26 [58931561]⟩,
  ⟨13, 526763, 1, 6, rkm128kMask56 23 [8225258]⟩,
  ⟨13, 615766, 1, 6, rkm128kMask56 26 [42263917]⟩,
  ⟨13, 634711, 1, 6, rkm128kMask56 26 [33975600]⟩,
  ⟨14, 165514, 1, 4, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 27`. -/
def lm4k512l248krS0RowR27 : List ℕ :=
  [604740, 273826, 1741986, 439431, 13500, 1848103, 352541, 3798871, 1656823, 17334091,
   32221802, 4200759, 159470406, 36758397, 116965624, 425507, 121198, 1775777, 4102490,
   153954776, 947826501, 1489243495, 107294677, 19891229, 35695, 177567077629, 819329317706]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 27`. -/
def lm4k512l248krS0AncR27 : RampKick128kAnchor :=
  ⟨27, lm4k512l248krS0SegsR27, lm4k512l248krS0RowR27⟩
/-- Active `RampKick128k` segments for `m = 4, r = 29` (`25` segments). -/
def lm4k512l248krS0SegsR29 : List Rkm128kSeg := [
  ⟨1, 20245145, 1, 10, []⟩,
  ⟨1, 20245145, 1, 10, []⟩,
  ⟨2, 12759697, 1, 12, []⟩,
  ⟨2, 12759697, 1, 12, []⟩,
  ⟨3, 19252034, 1, 17, []⟩,
  ⟨4, 8482562, 1, 12, []⟩,
  ⟨4, 8482563, 1, 12, rkm128kMask56 1 [1]⟩,
  ⟨6, 9874518, 1, 15, []⟩,
  ⟨6, 9874518, 1, 15, rkm128kMask56 6 [63]⟩,
  ⟨8, 9409495, 1, 17, rkm128kMask56 30 [553648150]⟩,
  ⟨8, 9409495, 1, 17, rkm128kMask56 30 [805310427]⟩,
  ⟨10, 8235299, 1, 17, rkm128kMask56 30 [536871298]⟩,
  ⟨10, 8235299, 1, 17, rkm128kMask56 7 [65]⟩,
  ⟨10, 8235299, 1, 17, rkm128kMask56 19 [462114]⟩,
  ⟨12, 5537817, 1, 15, []⟩,
  ⟨12, 5537817, 1, 15, []⟩,
  ⟨12, 5537817, 1, 15, rkm128kMask56 23 [6728484]⟩,
  ⟨13, 5071862, 1, 15, []⟩,
  ⟨13, 5071862, 1, 15, []⟩,
  ⟨13, 5071863, 1, 15, rkm128kMask56 28 [191528866]⟩,
  ⟨13, 2000, 1, 4, rkm128kMask56 28 [138799947]⟩,
  ⟨14, 4094191, 1, 12, []⟩,
  ⟨14, 4094192, 1, 12, rkm128kMask56 27 [71272971]⟩,
  ⟨14, 3560431, 1, 12, []⟩,
  ⟨14, 3560431, 1, 12, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 29`. -/
def lm4k512l248krS0RowR29 : List ℕ :=
  [542494, 1955179, 2513392, 39685, 861321, 218179, 1680775, 1568929, 99966791, 411318, 8016390,
   87561055, 1128961, 7034268, 361161222, 9021832, 94806482, 117480062, 1498073816, 905248774,
   196025846, 696061984, 3492072337, 52236510, 6913967640, 7834279000, 4421009266, 199295425751,
   773897073421]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 29`. -/
def lm4k512l248krS0AncR29 : RampKick128kAnchor :=
  ⟨29, lm4k512l248krS0SegsR29, lm4k512l248krS0RowR29⟩
/-- Active `RampKick128k` segments for `m = 4, r = 31` (`37` segments). -/
def lm4k512l248krS0SegsR31 : List Rkm128kSeg := [
  ⟨1, 22700635, 1, 12, []⟩,
  ⟨1, 18852437, 1, 10, []⟩,
  ⟨2, 10101098, 1, 10, []⟩,
  ⟨2, 12437045, 1, 12, []⟩,
  ⟨3, 19362717, 1, 17, []⟩,
  ⟨4, 16563907, 1, 18, []⟩,
  ⟨5, 7504377, 1, 12, rkm128kMask56 3 [6]⟩,
  ⟨6, 6166151, 1, 12, rkm128kMask56 4 [15]⟩,
  ⟨6, 6347031, 1, 12, rkm128kMask56 6 [52]⟩,
  ⟨7, 5954361, 1, 12, rkm128kMask56 29 [268435685]⟩,
  ⟨8, 5046680, 1, 12, rkm128kMask56 29 [268436385]⟩,
  ⟨8, 4519345, 1, 12, rkm128kMask56 29 [268436610]⟩,
  ⟨9, 5295974, 1, 14, rkm128kMask56 13 [4189]⟩,
  ⟨9, 4141995, 1, 12, rkm128kMask56 14 [15815]⟩,
  ⟨10, 4670032, 1, 14, rkm128kMask56 13 [4254]⟩,
  ⟨11, 4479836, 1, 14, rkm128kMask56 17 [122893]⟩,
  ⟨11, 3950904, 1, 12, rkm128kMask56 16 [35283]⟩,
  ⟨12, 3076482, 1, 12, rkm128kMask56 19 [475041]⟩,
  ⟨12, 3764171, 1, 12, rkm128kMask56 15 [21048]⟩,
  ⟨12, 2971326, 1, 12, rkm128kMask56 21 [1772084]⟩,
  ⟨13, 3517693, 1, 12, rkm128kMask56 17 [78468]⟩,
  ⟨13, 3180787, 1, 12, rkm128kMask56 23 [6213572]⟩,
  ⟨13, 4555219, 1, 13, rkm128kMask56 24 [16557248]⟩,
  ⟨14, 4191192, 1, 13, rkm128kMask56 25 [19233910]⟩,
  ⟨14, 4288593, 1, 13, rkm128kMask56 26 [38927365]⟩,
  ⟨14, 4825016, 1, 13, rkm128kMask56 27 [75454765]⟩,
  ⟨14, 2797765, 1, 10, rkm128kMask56 18 [204931]⟩,
  ⟨14, 2653613, 1, 10, rkm128kMask56 28 [166772967]⟩,
  ⟨14, 2114762, 1, 10, rkm128kMask56 26 [39189140]⟩,
  ⟨14, 2894591, 1, 12, rkm128kMask56 29 [482828793]⟩,
  ⟨14, 2254468, 1, 10, rkm128kMask56 29 [521077328]⟩,
  ⟨14, 3492540, 1, 12, rkm128kMask56 29 [429416403]⟩,
  ⟨14, 816292, 1, 6, rkm128kMask56 29 [467715920]⟩,
  ⟨14, 564107, 1, 6, rkm128kMask56 30 [566276167]⟩,
  ⟨14, 624823, 1, 6, rkm128kMask56 30 [633342628]⟩,
  ⟨14, 993813, 1, 8, rkm128kMask56 30 [669510315]⟩,
  ⟨14, 955538, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 31`. -/
def lm4k512l248krS0RowR31 : List ℕ :=
  [3184, 523, 4224, 139381, 1486476, 4855, 60851, 635505, 698590, 297853, 231141, 13320283,
   19989038, 75687998, 86128381, 1976492, 134694787, 4202433, 2514952, 103570766, 656796287,
   28731252, 81748778, 182832093, 682515268, 1087836240, 270565376, 228474887, 22271898,
   179787783686, 816523647785]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 31`. -/
def lm4k512l248krS0AncR31 : RampKick128kAnchor :=
  ⟨31, lm4k512l248krS0SegsR31, lm4k512l248krS0RowR31⟩
/-- Active `RampKick128k` segments for `m = 4, r = 34` (`40` segments). -/
def lm4k512l248krS0SegsR34 : List Rkm128kSeg := [
  ⟨1, 11078372, 1, 8, []⟩,
  ⟨1, 9606104, 1, 8, []⟩,
  ⟨1, 9566475, 1, 8, []⟩,
  ⟨1, 9566475, 1, 8, []⟩,
  ⟨2, 5553291, 1, 8, []⟩,
  ⟨2, 6598239, 1, 8, []⟩,
  ⟨2, 6694808, 1, 10, []⟩,
  ⟨2, 6694808, 1, 10, []⟩,
  ⟨3, 9641748, 1, 12, []⟩,
  ⟨3, 9641749, 1, 12, []⟩,
  ⟨4, 8896616, 1, 12, []⟩,
  ⟨5, 8305715, 1, 13, rkm128kMask56 2 [2]⟩,
  ⟨6, 6301781, 1, 12, rkm128kMask56 4 [8]⟩,
  ⟨7, 5894674, 1, 14, rkm128kMask56 6 [41]⟩,
  ⟨7, 5894674, 1, 14, rkm128kMask56 8 [140]⟩,
  ⟨8, 5513962, 1, 14, rkm128kMask56 10 [882]⟩,
  ⟨9, 5649571, 1, 15, rkm128kMask56 31 [1073744935]⟩,
  ⟨9, 5969750, 1, 15, rkm128kMask56 14 [12312]⟩,
  ⟨10, 3989872, 1, 12, rkm128kMask56 35 [17179880083]⟩,
  ⟨11, 4657918, 1, 13, rkm128kMask56 35 [17179968567]⟩,
  ⟨12, 3876383, 1, 14, rkm128kMask56 35 [19327503653]⟩,
  ⟨12, 3911521, 1, 14, rkm128kMask56 35 [17179886095]⟩,
  ⟨13, 3630677, 1, 12, rkm128kMask56 35 [17180969752]⟩,
  ⟨13, 3356649, 1, 12, rkm128kMask56 22 [3358188]⟩,
  ⟨14, 3355401, 1, 12, rkm128kMask56 35 [17184195594]⟩,
  ⟨14, 3399224, 1, 12, rkm128kMask56 35 [17184065697]⟩,
  ⟨14, 2430221, 1, 10, rkm128kMask56 35 [17184063886]⟩,
  ⟨15, 3025372, 1, 12, rkm128kMask56 26 [66241580]⟩,
  ⟨15, 5508399, 1, 17, rkm128kMask56 26 [34081309]⟩,
  ⟨16, 4958549, 1, 15, rkm128kMask56 29 [489478929]⟩,
  ⟨16, 4681738, 1, 15, rkm128kMask56 23 [4793609]⟩,
  ⟨16, 4656223, 1, 15, rkm128kMask56 31 [1618811080]⟩,
  ⟨16, 2422730, 1, 10, rkm128kMask56 22 [2381201]⟩,
  ⟨16, 3105938, 1, 12, rkm128kMask56 29 [460935401]⟩,
  ⟨16, 3245191, 1, 12, rkm128kMask56 30 [537068146]⟩,
  ⟨16, 1792198, 1, 10, rkm128kMask56 33 [7485273561]⟩,
  ⟨17, 1214948, 1, 8, rkm128kMask56 33 [4296018909]⟩,
  ⟨17, 324289, 1, 6, rkm128kMask56 33 [4582220567]⟩,
  ⟨17, 283980, 1, 6, rkm128kMask56 23 [4196377]⟩,
  ⟨17, 344437, 1, 6, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 34`. -/
def lm4k512l248krS0RowR34 : List ℕ :=
  [15345, 1040, 432, 54106, 12826, 5164, 538736, 44146, 2642550, 742922, 1119062, 3437400,
   26806100, 1369960, 11721810, 37927113, 9066629, 459, 96786635, 21255791, 453656508, 7389025,
   1224850525, 23078251, 154997, 695637270, 5615179399, 3707326038, 772724364, 1981186956,
   10124174150, 174032, 180294249013, 794884193700]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 34`. -/
def lm4k512l248krS0AncR34 : RampKick128kAnchor :=
  ⟨34, lm4k512l248krS0SegsR34, lm4k512l248krS0RowR34⟩
/-- Active `RampKick128k` segments for `m = 4, r = 37` (`44` segments). -/
def lm4k512l248krS0SegsR37 : List Rkm128kSeg := [
  ⟨1, 10712480, 1, 8, []⟩,
  ⟨1, 9101328, 1, 8, []⟩,
  ⟨1, 9276717, 1, 8, []⟩,
  ⟨1, 9276718, 1, 8, []⟩,
  ⟨2, 5236567, 1, 8, []⟩,
  ⟨2, 6197769, 1, 8, []⟩,
  ⟨2, 6227693, 1, 8, []⟩,
  ⟨2, 6227694, 1, 8, []⟩,
  ⟨3, 9303607, 1, 12, []⟩,
  ⟨3, 9303608, 1, 12, []⟩,
  ⟨4, 8852648, 1, 14, []⟩,
  ⟨5, 7913505, 1, 13, rkm128kMask56 2 [3]⟩,
  ⟨6, 5944132, 1, 12, rkm128kMask56 4 [10]⟩,
  ⟨7, 5915636, 1, 14, rkm128kMask56 26 [33554480]⟩,
  ⟨7, 5500010, 1, 12, rkm128kMask56 8 [192]⟩,
  ⟨8, 5226702, 1, 14, rkm128kMask56 10 [835]⟩,
  ⟨9, 5168131, 1, 13, rkm128kMask56 31 [1073745004]⟩,
  ⟨10, 5194924, 1, 15, rkm128kMask56 14 [12656]⟩,
  ⟨10, 3768220, 1, 12, rkm128kMask56 35 [17179870240]⟩,
  ⟨11, 4175363, 1, 14, rkm128kMask56 35 [17179999025]⟩,
  ⟨12, 3340266, 1, 12, rkm128kMask56 18 [133132]⟩,
  ⟨12, 3540203, 1, 14, rkm128kMask56 13 [7452]⟩,
  ⟨13, 3289980, 1, 12, rkm128kMask56 36 [34360789123]⟩,
  ⟨13, 2940502, 1, 12, rkm128kMask56 36 [34363657733]⟩,
  ⟨14, 3234744, 1, 12, rkm128kMask56 36 [34363949120]⟩,
  ⟨14, 3791779, 1, 13, rkm128kMask56 14 [8259]⟩,
  ⟨15, 3323755, 1, 14, rkm128kMask56 26 [35653629]⟩,
  ⟨15, 3363491, 1, 14, rkm128kMask56 27 [129172429]⟩,
  ⟨16, 4176878, 1, 15, rkm128kMask56 19 [363614]⟩,
  ⟨16, 4526399, 1, 15, rkm128kMask56 30 [829403085]⟩,
  ⟨17, 2795839, 1, 12, rkm128kMask56 14 [10762]⟩,
  ⟨17, 2740756, 1, 12, rkm128kMask56 23 [4231262]⟩,
  ⟨17, 2606404, 1, 12, rkm128kMask56 31 [1074406161]⟩,
  ⟨17, 2527300, 1, 12, rkm128kMask56 33 [7243546113]⟩,
  ⟨18, 2353866, 1, 12, rkm128kMask56 26 [35193035]⟩,
  ⟨18, 2524670, 1, 12, rkm128kMask56 28 [134223892]⟩,
  ⟨18, 2046589, 1, 10, rkm128kMask56 19 [427330]⟩,
  ⟨18, 2255871, 1, 12, rkm128kMask56 35 [31167284868]⟩,
  ⟨18, 2265407, 1, 12, rkm128kMask56 24 [8719440]⟩,
  ⟨18, 1983340, 1, 10, rkm128kMask56 36 [51712581306]⟩,
  ⟨18, 381208, 1, 6, rkm128kMask56 22 [2113735]⟩,
  ⟨18, 308728, 1, 6, rkm128kMask56 36 [51180186863]⟩,
  ⟨18, 820002, 1, 8, rkm128kMask56 25 [16777400]⟩,
  ⟨18, 917863, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 37`. -/
def lm4k512l248krS0RowR37 : List ℕ :=
  [6818, 4353, 196494, 59864, 49882, 10450, 612871, 1800908, 268514, 4059288, 2775456, 602153,
   45682, 315732, 8333740, 22001828, 1791978, 122934598, 8092395, 43401453, 255158742, 69118482,
   46449786, 26713440, 674120537, 442367158, 38714705, 2420108771, 6144067116, 42235583,
   1685741738, 1204562780, 4066727641, 688669190, 506895103, 185741158984, 795727149712]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 37`. -/
def lm4k512l248krS0AncR37 : RampKick128kAnchor :=
  ⟨37, lm4k512l248krS0SegsR37, lm4k512l248krS0RowR37⟩
/-- Active `RampKick128k` segments for `m = 4, r = 41` (`45` segments). -/
def lm4k512l248krS0SegsR41 : List Rkm128kSeg := [
  ⟨1, 10412787, 1, 8, []⟩,
  ⟨1, 9220842, 1, 8, []⟩,
  ⟨1, 8823817, 1, 8, []⟩,
  ⟨1, 8823817, 1, 8, []⟩,
  ⟨2, 4480886, 1, 8, []⟩,
  ⟨2, 5668175, 1, 8, []⟩,
  ⟨2, 5668174, 1, 8, []⟩,
  ⟨2, 5668175, 1, 8, []⟩,
  ⟨3, 8775691, 1, 12, []⟩,
  ⟨3, 8775692, 1, 12, []⟩,
  ⟨4, 8583976, 1, 14, []⟩,
  ⟨5, 7962989, 1, 15, rkm128kMask56 2 [3]⟩,
  ⟨6, 5577419, 1, 12, rkm128kMask56 25 [16777224]⟩,
  ⟨7, 5163687, 1, 12, rkm128kMask56 5 [18]⟩,
  ⟨7, 5163687, 1, 12, rkm128kMask56 8 [128]⟩,
  ⟨8, 4830186, 1, 14, rkm128kMask56 10 [1000]⟩,
  ⟨9, 4667086, 1, 13, rkm128kMask56 12 [2280]⟩,
  ⟨10, 4153704, 1, 14, rkm128kMask56 8 [152]⟩,
  ⟨10, 4351194, 1, 13, rkm128kMask56 13 [5136]⟩,
  ⟨11, 3892898, 1, 14, rkm128kMask56 17 [117799]⟩,
  ⟨12, 4077514, 1, 15, rkm128kMask56 42 [2199023274498]⟩,
  ⟨13, 4146656, 1, 15, rkm128kMask56 42 [2199023256157]⟩,
  ⟨14, 3995817, 1, 15, rkm128kMask56 21 [1181704]⟩,
  ⟨14, 3995817, 1, 15, rkm128kMask56 24 [12064167]⟩,
  ⟨15, 3543171, 1, 15, rkm128kMask56 15 [16658]⟩,
  ⟨16, 2961284, 1, 14, rkm128kMask56 27 [69469741]⟩,
  ⟨16, 2565513, 1, 12, rkm128kMask56 28 [136448045]⟩,
  ⟨16, 2545864, 1, 12, rkm128kMask56 29 [411457478]⟩,
  ⟨17, 1982146, 1, 12, rkm128kMask56 30 [537002148]⟩,
  ⟨17, 2970911, 1, 13, rkm128kMask56 31 [1616282765]⟩,
  ⟨18, 2110357, 1, 12, rkm128kMask56 30 [566495666]⟩,
  ⟨18, 2725611, 1, 14, rkm128kMask56 33 [7313536896]⟩,
  ⟨18, 3120595, 1, 13, rkm128kMask56 34 [8627718882]⟩,
  ⟨19, 1467179, 1, 10, rkm128kMask56 27 [100703022]⟩,
  ⟨19, 1907576, 1, 12, rkm128kMask56 23 [6304470]⟩,
  ⟨19, 2206304, 1, 12, rkm128kMask56 36 [51296202229]⟩,
  ⟨19, 3612773, 1, 15, rkm128kMask56 37 [68753226102]⟩,
  ⟨20, 2088519, 1, 12, rkm128kMask56 28 [202742155]⟩,
  ⟨20, 2864180, 1, 13, rkm128kMask56 31 [1074827371]⟩,
  ⟨20, 2994734, 1, 13, rkm128kMask56 39 [489583842492]⟩,
  ⟨20, 1408286, 1, 10, rkm128kMask56 24 [12616862]⟩,
  ⟨20, 1066976, 1, 8, rkm128kMask56 40 [571916085047]⟩,
  ⟨20, 64402, 1, 4, rkm128kMask56 40 [670817427783]⟩,
  ⟨20, 1609836, 1, 10, rkm128kMask56 26 [38496531]⟩,
  ⟨20, 2121710, 1, 12, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 41`. -/
def lm4k512l248krS0RowR41 : List ℕ :=
  [595, 13751, 34740, 287931, 326603, 14111, 19427, 188252, 1644322, 781571, 454042, 412909,
   90533, 2907085, 753716, 1800975, 10689, 2749473, 20128001, 5647591, 3454931, 1141286,
   120237752, 125395463, 71171955, 153488902, 53733642, 794759115, 799316666, 378925662,
   845486571, 47843577, 148286390, 1270487743, 178413416, 1164571877, 3821103249, 9354900769,
   1672895099, 189060444411, 789893060698]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 41`. -/
def lm4k512l248krS0AncR41 : RampKick128kAnchor :=
  ⟨41, lm4k512l248krS0SegsR41, lm4k512l248krS0RowR41⟩
/-- Active `RampKick128k` segments for `m = 4, r = 44` (`7` segments). -/
def lm4k512l248krS0SegsR44 : List Rkm128kSeg := [
  ⟨1, 30615663, 1, 15, rkm128kMask56 5 [16]⟩,
  ⟨1, 40732759, 1, 16, []⟩,
  ⟨1, 3028127, 1, 6, []⟩,
  ⟨1, 2966592, 1, 6, rkm128kMask56 4 [11]⟩,
  ⟨1, 1000, 1, 4, rkm128kMask56 4 [11]⟩,
  ⟨1, 3797099, 1, 6, []⟩,
  ⟨1, 4127280, 1, 6, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 44`. -/
def lm4k512l248krS0RowR44 : List ℕ :=
  [24077914300, 122375574764, 456632138325, 396527764270]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 44`. -/
def lm4k512l248krS0AncR44 : RampKick128kAnchor :=
  ⟨44, lm4k512l248krS0SegsR44, lm4k512l248krS0RowR44⟩
/-- Active `RampKick128k` segments for `m = 4, r = 47` (`12` segments). -/
def lm4k512l248krS0SegsR47 : List Rkm128kSeg := [
  ⟨1, 432605, 1, 4, []⟩,
  ⟨1, 473379, 1, 4, []⟩,
  ⟨1, 454203, 1, 4, []⟩,
  ⟨1, 467270, 1, 4, []⟩,
  ⟨1, 542802, 1, 4, []⟩,
  ⟨1, 578650, 1, 4, []⟩,
  ⟨1, 907148, 1, 4, []⟩,
  ⟨1, 907148, 1, 4, rkm128kMask56 4 [8]⟩,
  ⟨1, 5587357, 1, 8, []⟩,
  ⟨1, 5649389, 1, 8, rkm128kMask56 5 [16]⟩,
  ⟨1, 34524123, 1, 15, []⟩,
  ⟨1, 34387673, 1, 15, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 47`. -/
def lm4k512l248krS0RowR47 : List ℕ :=
  [12505160750, 110379355089, 404178219712, 472560115838]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 47`. -/
def lm4k512l248krS0AncR47 : RampKick128kAnchor :=
  ⟨47, lm4k512l248krS0SegsR47, lm4k512l248krS0RowR47⟩
/-- Active `RampKick128k` segments for `m = 4, r = 49` (`20` segments). -/
def lm4k512l248krS0SegsR49 : List Rkm128kSeg := [
  ⟨1, 35478816, 1, 15, []⟩,
  ⟨2, 23387812, 1, 18, []⟩,
  ⟨3, 7614353, 1, 12, []⟩,
  ⟨3, 8149418, 1, 12, []⟩,
  ⟨4, 7364787, 1, 14, rkm128kMask56 17 [98304]⟩,
  ⟨5, 5919146, 1, 12, rkm128kMask56 21 [1769468]⟩,
  ⟨6, 7481778, 1, 15, rkm128kMask56 5 [18]⟩,
  ⟨7, 6886315, 1, 15, rkm128kMask56 22 [2097400]⟩,
  ⟨8, 6569301, 1, 17, rkm128kMask56 33 [4840228424]⟩,
  ⟨9, 6464048, 1, 18, rkm128kMask56 37 [87140847175]⟩,
  ⟨10, 4446518, 1, 15, rkm128kMask56 41 [2176273400970]⟩,
  ⟨11, 4499262, 1, 15, rkm128kMask56 45 [17889612769613]⟩,
  ⟨12, 3908996, 1, 15, rkm128kMask56 49 [561047283763201]⟩,
  ⟨12, 2461404, 1, 12, rkm128kMask56 49 [398401168381811]⟩,
  ⟨13, 3677337, 1, 15, rkm128kMask56 50 [1118409489389585]⟩,
  ⟨14, 3927413, 1, 15, rkm128kMask56 50 [1078620932545190]⟩,
  ⟨14, 4317841, 1, 17, rkm128kMask56 50 [1112705666548616]⟩,
  ⟨14, 2614454, 1, 14, rkm128kMask56 50 [1125898836289134]⟩,
  ⟨14, 98348, 1, 4, rkm128kMask56 50 [1125898833634087]⟩,
  ⟨14, 37447, 1, 4, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 49`. -/
def lm4k512l248krS0RowR49 : List ℕ :=
  [128678, 190355, 2067741, 17178, 2791188, 2869318, 76236, 7577645, 59192133, 4026349,
   44269399, 67955922, 71317378, 47022944, 69701117, 5746378, 6963841, 174592540, 752460151,
   700734011, 36679781, 199719745, 310231120, 32488660, 208424683, 99631200, 295298370,
   1438932140, 46454283541, 139640972177, 256852261960, 263117660669, 175566265652, 80389935879,
   26055884493, 6099508891, 1039696589, 128577830, 11422343, 717652, 31934, 706, 4, 0, 0, 0, 0,
   0, 0]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 49`. -/
def lm4k512l248krS0AncR49 : RampKick128kAnchor :=
  ⟨49, lm4k512l248krS0SegsR49, lm4k512l248krS0RowR49⟩
/-- Active `RampKick128k` segments for `m = 4, r = 51` (`10` segments). -/
def lm4k512l248krS0SegsR51 : List Rkm128kSeg := [
  ⟨1, 593693, 1, 4, rkm128kMask56 4 [8]⟩,
  ⟨1, 642354, 1, 4, []⟩,
  ⟨1, 800871, 1, 4, rkm128kMask56 4 [8]⟩,
  ⟨1, 1004854, 1, 4, rkm128kMask56 4 [8]⟩,
  ⟨1, 2842371, 1, 6, rkm128kMask56 4 [8]⟩,
  ⟨1, 5749473, 1, 8, rkm128kMask56 4 [8]⟩,
  ⟨1, 7484044, 1, 8, []⟩,
  ⟨1, 7686058, 1, 8, rkm128kMask56 5 [16]⟩,
  ⟨1, 7277722, 1, 8, []⟩,
  ⟨1, 7490065, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 51`. -/
def lm4k512l248krS0RowR51 : List ℕ :=
  [403507883461, 285301552026, 84223266735, 3728166631]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 51`. -/
def lm4k512l248krS0AncR51 : RampKick128kAnchor :=
  ⟨51, lm4k512l248krS0SegsR51, lm4k512l248krS0RowR51⟩
/-- Active `RampKick128k` segments for `m = 4, r = 52` (`9` segments). -/
def lm4k512l248krS0SegsR52 : List Rkm128kSeg := [
  ⟨1, 2631789, 1, 6, []⟩,
  ⟨1, 2201335, 1, 6, rkm128kMask56 4 [8]⟩,
  ⟨1, 29567632, 1, 15, []⟩,
  ⟨1, 31272541, 1, 15, []⟩,
  ⟨1, 1182365, 1, 4, []⟩,
  ⟨1, 1340020, 1, 6, rkm128kMask56 4 [11]⟩,
  ⟨1, 1000, 1, 4, rkm128kMask56 4 [11]⟩,
  ⟨1, 3214686, 1, 6, []⟩,
  ⟨1, 3271006, 1, 6, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 52`. -/
def lm4k512l248krS0RowR52 : List ℕ :=
  [34594422118, 191786166368, 434651981367, 336757784613]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 52`. -/
def lm4k512l248krS0AncR52 : RampKick128kAnchor :=
  ⟨52, lm4k512l248krS0SegsR52, lm4k512l248krS0RowR52⟩
/-- Active `RampKick128k` segments for `m = 4, r = 54` (`10` segments). -/
def lm4k512l248krS0SegsR54 : List Rkm128kSeg := [
  ⟨1, 1242376, 1, 4, []⟩,
  ⟨1, 1278105, 1, 4, []⟩,
  ⟨1, 1499607, 1, 6, []⟩,
  ⟨1, 2261172, 1, 6, []⟩,
  ⟨1, 13167853, 1, 10, []⟩,
  ⟨1, 15064361, 1, 10, []⟩,
  ⟨1, 15064361, 1, 10, []⟩,
  ⟨1, 15064361, 1, 10, []⟩,
  ⟨1, 15064361, 1, 10, []⟩,
  ⟨1, 7225794, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 54`. -/
def lm4k512l248krS0RowR54 : List ℕ :=
  [1636137703, 37091920431, 286997673248, 674254480510]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 54`. -/
def lm4k512l248krS0AncR54 : RampKick128kAnchor :=
  ⟨54, lm4k512l248krS0SegsR54, lm4k512l248krS0RowR54⟩
/-- Active `RampKick128k` segments for `m = 4, r = 55` (`20` segments). -/
def lm4k512l248krS0SegsR55 : List Rkm128kSeg := [
  ⟨1, 1317030, 1, 5, rkm128kMask56 4 [8]⟩,
  ⟨1, 1356281, 1, 5, []⟩,
  ⟨1, 1345480, 1, 5, []⟩,
  ⟨1, 1501910, 1, 5, rkm128kMask56 5 [16]⟩,
  ⟨1, 7922406, 1, 9, []⟩,
  ⟨1, 9189443, 1, 9, []⟩,
  ⟨1, 3523322, 1, 7, []⟩,
  ⟨1, 3542892, 1, 7, rkm128kMask56 3 [4]⟩,
  ⟨1, 1000, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 2887266, 1, 6, []⟩,
  ⟨1, 2887267, 1, 6, rkm128kMask56 5 [16]⟩,
  ⟨1, 1000, 1, 4, rkm128kMask56 5 [16]⟩,
  ⟨1, 9699334, 1, 9, []⟩,
  ⟨1, 9699334, 1, 9, []⟩,
  ⟨2, 3303994, 1, 8, rkm128kMask56 7 [64]⟩,
  ⟨2, 3183409, 1, 8, []⟩,
  ⟨2, 8224453, 1, 11, []⟩,
  ⟨2, 6813780, 1, 11, rkm128kMask56 9 [256]⟩,
  ⟨2, 6015818, 1, 10, []⟩,
  ⟨2, 7466343, 1, 11, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 55`. -/
def lm4k512l248krS0RowR55 : List ℕ :=
  [323473018, 1404478578, 2762696148, 50643018614, 302549429325, 416390640293, 210740013726,
   15139227362]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 55`. -/
def lm4k512l248krS0AncR55 : RampKick128kAnchor :=
  ⟨55, lm4k512l248krS0SegsR55, lm4k512l248krS0RowR55⟩
/-- Active `RampKick128k` segments for `m = 4, r = 56` (`12` segments). -/
def lm4k512l248krS0SegsR56 : List Rkm128kSeg := [
  ⟨1, 25789586, 1, 13, []⟩,
  ⟨1, 20524016, 1, 12, []⟩,
  ⟨1, 2785424, 1, 6, []⟩,
  ⟨1, 2520957, 1, 6, rkm128kMask56 2 [3]⟩,
  ⟨1, 1000, 1, 4, []⟩,
  ⟨1, 1000, 1, 4, rkm128kMask56 2 [3]⟩,
  ⟨2, 13096619, 1, 14, []⟩,
  ⟨2, 12847989, 1, 14, []⟩,
  ⟨2, 3059021, 1, 8, []⟩,
  ⟨3, 2633398, 1, 8, rkm128kMask56 12 [2050]⟩,
  ⟨3, 4223900, 1, 10, rkm128kMask56 2 [2]⟩,
  ⟨3, 4685116, 1, 10, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 56`. -/
def lm4k512l248krS0RowR56 : List ℕ :=
  [3175302, 696142363, 264580672, 1356705004, 57371398412, 271017487867, 379978484177,
   227832850919, 55510271091, 5707582279, 237736011, 3222100]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 56`. -/
def lm4k512l248krS0AncR56 : RampKick128kAnchor :=
  ⟨56, lm4k512l248krS0SegsR56, lm4k512l248krS0RowR56⟩
/-- Active `RampKick128k` segments for `m = 4, r = 57` (`7` segments). -/
def lm4k512l248krS0SegsR57 : List Rkm128kSeg := [
  ⟨1, 44217679, 1, 18, []⟩,
  ⟨1, 4446079, 1, 7, rkm128kMask56 2 [3]⟩,
  ⟨1, 2000, 1, 4, []⟩,
  ⟨1, 2000, 1, 4, rkm128kMask56 2 [3]⟩,
  ⟨2, 25076406, 1, 20, []⟩,
  ⟨3, 8445550, 1, 14, rkm128kMask56 2 [2]⟩,
  ⟨3, 10163131, 1, 15, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 57`. -/
def lm4k512l248krS0RowR57 : List ℕ :=
  [47116510, 154720762, 341658857, 95602295, 12910743413, 132709297737, 328895993882,
   332939384685, 154633829211, 33798591984, 3322050908, 116803847]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 57`. -/
def lm4k512l248krS0AncR57 : RampKick128kAnchor :=
  ⟨57, lm4k512l248krS0SegsR57, lm4k512l248krS0RowR57⟩
/-- Active `RampKick128k` segments for `m = 4, r = 58` (`12` segments). -/
def lm4k512l248krS0SegsR58 : List Rkm128kSeg := [
  ⟨1, 20928208, 1, 12, []⟩,
  ⟨1, 21534226, 1, 12, []⟩,
  ⟨1, 2120836, 1, 6, []⟩,
  ⟨1, 2166620, 1, 6, rkm128kMask56 2 [3]⟩,
  ⟨1, 1000, 1, 4, []⟩,
  ⟨1, 1000, 1, 4, rkm128kMask56 2 [3]⟩,
  ⟨2, 7721387, 1, 10, rkm128kMask56 9 [384]⟩,
  ⟨2, 11803621, 1, 12, []⟩,
  ⟨2, 7413097, 1, 10, []⟩,
  ⟨3, 7187591, 1, 12, rkm128kMask56 2 [2]⟩,
  ⟨3, 7359971, 1, 12, rkm128kMask56 2 [2]⟩,
  ⟨4, 8805329, 1, 15, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 58`. -/
def lm4k512l248krS0RowR58 : List ℕ :=
  [1463454, 29624677, 292345523, 51591485, 458118120, 2092457887, 68858198952, 262262970974,
   356009489117, 223481299223, 72433664924, 12748739906, 1203374874, 58510349, 1344398, 11294]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 58`. -/
def lm4k512l248krS0AncR58 : RampKick128kAnchor :=
  ⟨58, lm4k512l248krS0SegsR58, lm4k512l248krS0RowR58⟩
/-- Active `RampKick128k` segments for `m = 4, r = 59` (`12` segments). -/
def lm4k512l248krS0SegsR59 : List Rkm128kSeg := [
  ⟨1, 21046170, 1, 12, []⟩,
  ⟨1, 21897035, 1, 12, []⟩,
  ⟨1, 1414924, 1, 6, []⟩,
  ⟨1, 1116131, 1, 4, rkm128kMask56 2 [3]⟩,
  ⟨1, 1000, 1, 4, []⟩,
  ⟨1, 1000, 1, 4, rkm128kMask56 2 [3]⟩,
  ⟨2, 13423476, 1, 13, []⟩,
  ⟨2, 12308905, 1, 14, []⟩,
  ⟨3, 8396452, 1, 14, rkm128kMask56 2 [2]⟩,
  ⟨3, 6442408, 1, 12, rkm128kMask56 2 [2]⟩,
  ⟨4, 8463280, 1, 15, rkm128kMask56 17 [65568]⟩,
  ⟨4, 5183209, 1, 12, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 59`. -/
def lm4k512l248krS0RowR59 : List ℕ :=
  [20734837, 11819751, 118934389, 120463928, 49369547, 565793640, 2860942923, 78411179537,
   267925057716, 345722388475, 216631780700, 72747007907, 13415907028, 1325590854, 65299794,
   832819]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 59`. -/
def lm4k512l248krS0AncR59 : RampKick128kAnchor :=
  ⟨59, lm4k512l248krS0SegsR59, lm4k512l248krS0RowR59⟩
/-- Active `RampKick128k` segments for `m = 4, r = 60` (`7` segments). -/
def lm4k512l248krS0SegsR60 : List Rkm128kSeg := [
  ⟨1, 39697464, 1, 18, []⟩,
  ⟨1, 3847702, 1, 6, rkm128kMask56 2 [3]⟩,
  ⟨2, 1020, 1, 4, []⟩,
  ⟨2, 1020, 1, 4, rkm128kMask56 2 [3]⟩,
  ⟨2, 22964897, 1, 18, []⟩,
  ⟨3, 14450620, 1, 18, rkm128kMask56 2 [2]⟩,
  ⟨4, 17766996, 1, 22, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 60`. -/
def lm4k512l248krS0RowR60 : List ℕ :=
  [20034512, 758680, 4044519, 320202076, 25962258, 791482199, 7877798, 28695524528,
   169867468232, 323794768331, 291552409286, 140871280759, 37989860296, 5625018984, 420318828,
   12203862]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 60`. -/
def lm4k512l248krS0AncR60 : RampKick128kAnchor :=
  ⟨60, lm4k512l248krS0SegsR60, lm4k512l248krS0RowR60⟩
/-- Active `RampKick128k` segments for `m = 4, r = 61` (`22` segments). -/
def lm4k512l248krS0SegsR61 : List Rkm128kSeg := [
  ⟨1, 10063655, 1, 10, []⟩,
  ⟨1, 11616893, 1, 10, []⟩,
  ⟨1, 9214078, 1, 10, []⟩,
  ⟨1, 9422862, 1, 10, []⟩,
  ⟨1, 662804, 1, 4, []⟩,
  ⟨1, 673959, 1, 4, []⟩,
  ⟨1, 671758, 1, 4, []⟩,
  ⟨1, 793420, 1, 4, rkm128kMask56 2 [3]⟩,
  ⟨1, 1000, 1, 4, []⟩,
  ⟨1, 1000, 1, 4, rkm128kMask56 2 [3]⟩,
  ⟨2, 6857666, 1, 10, []⟩,
  ⟨2, 6353455, 1, 10, []⟩,
  ⟨2, 4864821, 1, 10, []⟩,
  ⟨2, 5477750, 1, 10, []⟩,
  ⟨3, 5604949, 1, 12, []⟩,
  ⟨3, 4306154, 1, 10, rkm128kMask56 12 [2050]⟩,
  ⟨3, 3655950, 1, 10, rkm128kMask56 2 [2]⟩,
  ⟨4, 2737280, 1, 10, []⟩,
  ⟨4, 4918267, 1, 12, rkm128kMask56 3 [4]⟩,
  ⟨4, 4395903, 1, 12, rkm128kMask56 17 [65572]⟩,
  ⟨5, 5913490, 1, 15, rkm128kMask56 20 [524449]⟩,
  ⟨5, 4393862, 1, 12, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 61`. -/
def lm4k512l248krS0RowR61 : List ℕ :=
  [194547, 21692184, 3574028, 180335721, 6533945, 322112452, 50842634, 531482558, 5211616048,
   83148005709, 251383561833, 325586326530, 222439291226, 87188566606, 20698504025, 2967333147,
   247234829, 11425412, 212677, 1195]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 61`. -/
def lm4k512l248krS0AncR61 : RampKick128kAnchor :=
  ⟨61, lm4k512l248krS0SegsR61, lm4k512l248krS0RowR61⟩
/-- Active `RampKick128k` segments for `m = 4, r = 62` (`26` segments). -/
def lm4k512l248krS0SegsR62 : List Rkm128kSeg := [
  ⟨1, 8317595, 1, 8, []⟩,
  ⟨1, 10295137, 1, 10, []⟩,
  ⟨1, 9928629, 1, 10, []⟩,
  ⟨1, 9928630, 1, 10, []⟩,
  ⟨1, 810562, 1, 4, []⟩,
  ⟨1, 963447, 1, 4, []⟩,
  ⟨1, 884517, 1, 4, []⟩,
  ⟨1, 885062, 1, 4, rkm128kMask56 2 [3]⟩,
  ⟨1, 1000, 1, 4, []⟩,
  ⟨1, 1000, 1, 4, rkm128kMask56 2 [3]⟩,
  ⟨2, 86078, 1, 4, []⟩,
  ⟨2, 82799, 1, 4, []⟩,
  ⟨2, 79283, 1, 4, []⟩,
  ⟨2, 85859, 1, 4, []⟩,
  ⟨2, 5240237, 1, 10, []⟩,
  ⟨2, 5829774, 1, 10, []⟩,
  ⟨2, 5829774, 1, 10, []⟩,
  ⟨2, 5328794, 1, 10, []⟩,
  ⟨3, 4770076, 1, 10, rkm128kMask56 11 [1024]⟩,
  ⟨3, 4731930, 1, 10, rkm128kMask56 12 [2048]⟩,
  ⟨3, 4327946, 1, 10, rkm128kMask56 13 [4098]⟩,
  ⟨4, 3993359, 1, 10, []⟩,
  ⟨4, 5938380, 1, 12, []⟩,
  ⟨5, 5252478, 1, 14, rkm128kMask56 20 [655459]⟩,
  ⟨5, 6495165, 1, 15, rkm128kMask56 21 [1048943]⟩,
  ⟨5, 3888983, 1, 12, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 62`. -/
def lm4k512l248krS0RowR62 : List ℕ :=
  [3637909, 850205, 15369056, 81752293, 86707719, 8966432, 538186308, 92684563, 381051933,
   7240407306, 93562203083, 259882565482, 319548173441, 213016843840, 82598281126, 19913854640,
   2807678655, 210608119, 7571039, 67718]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 62`. -/
def lm4k512l248krS0AncR62 : RampKick128kAnchor :=
  ⟨62, lm4k512l248krS0SegsR62, lm4k512l248krS0RowR62⟩
/-- Active `RampKick128k` segments for `m = 4, r = 63` (`26` segments). -/
def lm4k512l248krS0SegsR63 : List Rkm128kSeg := [
  ⟨1, 8165955, 1, 8, []⟩,
  ⟨1, 10001989, 1, 10, []⟩,
  ⟨1, 9756047, 1, 10, []⟩,
  ⟨1, 9756048, 1, 10, []⟩,
  ⟨1, 852914, 1, 4, []⟩,
  ⟨1, 942406, 1, 4, []⟩,
  ⟨1, 974152, 1, 4, []⟩,
  ⟨1, 1063402, 1, 4, rkm128kMask56 2 [3]⟩,
  ⟨1, 1000, 1, 4, []⟩,
  ⟨1, 1000, 1, 4, rkm128kMask56 2 [3]⟩,
  ⟨2, 59650, 1, 4, []⟩,
  ⟨2, 61519, 1, 4, []⟩,
  ⟨2, 71887, 1, 4, []⟩,
  ⟨2, 75367, 1, 4, []⟩,
  ⟨2, 4765467, 1, 10, []⟩,
  ⟨2, 5917169, 1, 10, []⟩,
  ⟨2, 5647836, 1, 10, []⟩,
  ⟨2, 4878111, 1, 10, []⟩,
  ⟨3, 4608886, 1, 10, []⟩,
  ⟨3, 4389520, 1, 10, rkm128kMask56 12 [2048]⟩,
  ⟨3, 4191851, 1, 10, rkm128kMask56 12 [2050]⟩,
  ⟨4, 3824864, 1, 10, rkm128kMask56 13 [4098]⟩,
  ⟨4, 7822131, 1, 15, rkm128kMask56 3 [4]⟩,
  ⟨5, 7363846, 1, 15, rkm128kMask56 21 [1310948]⟩,
  ⟨5, 4236949, 1, 12, rkm128kMask56 21 [1311016]⟩,
  ⟨5, 6607797, 1, 15, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 63`. -/
def lm4k512l248krS0RowR63 : List ℕ :=
  [2181295, 15007147, 660166, 109382346, 98805828, 51696549, 4565904, 272993321, 236243799,
   234090493, 10132370352, 106224886831, 279434945245, 323697728811, 197239269289, 66648402074,
   14364967268, 1194343850, 35899058, 330780]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 63`. -/
def lm4k512l248krS0AncR63 : RampKick128kAnchor :=
  ⟨63, lm4k512l248krS0SegsR63, lm4k512l248krS0RowR63⟩
/-- Active `RampKick128k` segments for `m = 4, r = 67` (`20` segments). -/
def lm4k512l248krS0SegsR67 : List Rkm128kSeg := [
  ⟨1, 370353, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 338915, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 466718, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 445095, 1, 4, rkm128kMask56 5 [26]⟩,
  ⟨1, 281433, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 281433, 1, 4, rkm128kMask56 5 [30]⟩,
  ⟨1, 369280, 1, 4, []⟩,
  ⟨1, 424075, 1, 4, []⟩,
  ⟨1, 1663804, 1, 6, []⟩,
  ⟨1, 2032598, 1, 6, rkm128kMask56 4 [8]⟩,
  ⟨1, 4161401, 1, 8, []⟩,
  ⟨1, 3955433, 1, 8, rkm128kMask56 5 [24]⟩,
  ⟨1, 2544676, 1, 6, rkm128kMask56 5 [24]⟩,
  ⟨1, 8070909, 1, 8, rkm128kMask56 5 [16]⟩,
  ⟨1, 7268313, 1, 8, []⟩,
  ⟨1, 7931278, 1, 8, rkm128kMask56 5 [16]⟩,
  ⟨1, 7279853, 1, 8, rkm128kMask56 5 [16]⟩,
  ⟨1, 5970289, 1, 8, rkm128kMask56 5 [16]⟩,
  ⟨1, 8445141, 1, 10, rkm128kMask56 5 [16]⟩,
  ⟨1, 4003809, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 67`. -/
def lm4k512l248krS0RowR67 : List ℕ :=
  [47094229766, 119365446419, 829917931647, 33622367]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 67`. -/
def lm4k512l248krS0AncR67 : RampKick128kAnchor :=
  ⟨67, lm4k512l248krS0SegsR67, lm4k512l248krS0RowR67⟩
/-- Active `RampKick128k` segments for `m = 4, r = 68` (`3` segments). -/
def lm4k512l248krS0SegsR68 : List Rkm128kSeg := [
  ⟨1, 732580, 1, 4, []⟩,
  ⟨1, 732580, 1, 4, []⟩,
  ⟨1, 80513487, 1, 26, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 68`. -/
def lm4k512l248krS0RowR68 : List ℕ :=
  [225280792, 12032140016, 186083839850, 801657871765]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 68`. -/
def lm4k512l248krS0AncR68 : RampKick128kAnchor :=
  ⟨68, lm4k512l248krS0SegsR68, lm4k512l248krS0RowR68⟩
/-- Active `RampKick128k` segments for `m = 4, r = 70` (`15` segments). -/
def lm4k512l248krS0SegsR70 : List Rkm128kSeg := [
  ⟨1, 4642464, 1, 8, []⟩,
  ⟨1, 5832107, 1, 8, []⟩,
  ⟨1, 5048066, 1, 8, []⟩,
  ⟨1, 5537276, 1, 8, []⟩,
  ⟨1, 10907738, 1, 10, []⟩,
  ⟨1, 12887214, 1, 10, []⟩,
  ⟨1, 5442484, 1, 8, []⟩,
  ⟨1, 5494579, 1, 8, []⟩,
  ⟨1, 6544145, 1, 8, []⟩,
  ⟨1, 6544146, 1, 8, rkm128kMask56 5 [31]⟩,
  ⟨1, 149392, 1, 4, []⟩,
  ⟨1, 147111, 1, 4, rkm128kMask56 5 [26]⟩,
  ⟨1, 1000, 1, 4, rkm128kMask56 5 [26]⟩,
  ⟨2, 2418569, 1, 8, rkm128kMask56 8 [128]⟩,
  ⟨2, 2418569, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 70`. -/
def lm4k512l248krS0RowR70 : List ℕ :=
  [1804577877, 31417475851, 195803009131, 697415287187, 71658256878, 1857387221, 9631042, 12569]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 70`. -/
def lm4k512l248krS0AncR70 : RampKick128kAnchor :=
  ⟨70, lm4k512l248krS0SegsR70, lm4k512l248krS0RowR70⟩
/-- Active `RampKick128k` segments for `m = 4, r = 71` (`12` segments). -/
def lm4k512l248krS0SegsR71 : List Rkm128kSeg := [
  ⟨1, 226927, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 230388, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 242743, 1, 4, []⟩,
  ⟨1, 275859, 1, 4, []⟩,
  ⟨1, 292411, 1, 4, []⟩,
  ⟨1, 743764, 1, 4, []⟩,
  ⟨1, 1073859, 1, 4, []⟩,
  ⟨1, 715379, 1, 4, []⟩,
  ⟨1, 3612094, 1, 6, []⟩,
  ⟨1, 3612096, 1, 6, rkm128kMask56 5 [24]⟩,
  ⟨1, 29740801, 1, 15, []⟩,
  ⟨1, 30411280, 1, 15, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 71`. -/
def lm4k512l248krS0RowR71 : List ℕ :=
  [7108566497, 75393540693, 380917884209, 535723176361]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 71`. -/
def lm4k512l248krS0AncR71 : RampKick128kAnchor :=
  ⟨71, lm4k512l248krS0SegsR71, lm4k512l248krS0RowR71⟩
/-- Active `RampKick128k` segments for `m = 4, r = 72` (`15` segments). -/
def lm4k512l248krS0SegsR72 : List Rkm128kSeg := [
  ⟨1, 1839984, 1, 6, rkm128kMask56 4 [8]⟩,
  ⟨1, 2079073, 1, 6, []⟩,
  ⟨1, 3202556, 1, 6, rkm128kMask56 5 [16]⟩,
  ⟨1, 4704333, 1, 8, []⟩,
  ⟨1, 12069186, 1, 10, []⟩,
  ⟨1, 12069187, 1, 10, []⟩,
  ⟨1, 5040734, 1, 8, []⟩,
  ⟨1, 5266503, 1, 8, []⟩,
  ⟨1, 6451316, 1, 8, []⟩,
  ⟨1, 6451316, 1, 8, rkm128kMask56 5 [31]⟩,
  ⟨1, 72837, 1, 4, []⟩,
  ⟨1, 72837, 1, 4, rkm128kMask56 5 [26]⟩,
  ⟨1, 1000, 1, 4, rkm128kMask56 5 [26]⟩,
  ⟨2, 7617307, 1, 12, rkm128kMask56 8 [128]⟩,
  ⟨2, 7617316, 1, 12, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 72`. -/
def lm4k512l248krS0RowR72 : List ℕ :=
  [76960182, 10418495687, 32404644653, 417852448840, 413681366235, 118835781348, 6632930008,
   91858703]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 72`. -/
def lm4k512l248krS0AncR72 : RampKick128kAnchor :=
  ⟨72, lm4k512l248krS0SegsR72, lm4k512l248krS0RowR72⟩
/-- Active `RampKick128k` segments for `m = 4, r = 73` (`1` segments). -/
def lm4k512l248krS0SegsR73 : List Rkm128kSeg := [
  ⟨1, 40429611, 1, 18, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 73`. -/
def lm4k512l248krS0RowR73 : List ℕ :=
  [343950783193, 351461611115, 155927744910, 25339725891]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 73`. -/
def lm4k512l248krS0AncR73 : RampKick128kAnchor :=
  ⟨73, lm4k512l248krS0SegsR73, lm4k512l248krS0RowR73⟩
/-- Active `RampKick128k` segments for `m = 4, r = 74` (`3` segments). -/
def lm4k512l248krS0SegsR74 : List Rkm128kSeg := [
  ⟨1, 1313182, 1, 5, []⟩,
  ⟨1, 1291378, 1, 5, []⟩,
  ⟨1, 64312139, 1, 25, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 74`. -/
def lm4k512l248krS0RowR74 : List ℕ :=
  [14671739108, 120058412799, 400994515469, 463661703353]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 74`. -/
def lm4k512l248krS0AncR74 : RampKick128kAnchor :=
  ⟨74, lm4k512l248krS0SegsR74, lm4k512l248krS0RowR74⟩
/-- Active `RampKick128k` segments for `m = 4, r = 75` (`5` segments). -/
def lm4k512l248krS0SegsR75 : List Rkm128kSeg := [
  ⟨1, 489575, 1, 4, []⟩,
  ⟨1, 489575, 1, 4, []⟩,
  ⟨1, 637532, 1, 4, []⟩,
  ⟨1, 927101, 1, 4, rkm128kMask56 5 [20]⟩,
  ⟨1, 36511467, 1, 18, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 75`. -/
def lm4k512l248krS0RowR75 : List ℕ :=
  [360090577597, 346732091476, 140884120911, 20523639773]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 75`. -/
def lm4k512l248krS0AncR75 : RampKick128kAnchor :=
  ⟨75, lm4k512l248krS0SegsR75, lm4k512l248krS0RowR75⟩
/-- Active `RampKick128k` segments for `m = 4, r = 76` (`15` segments). -/
def lm4k512l248krS0SegsR76 : List Rkm128kSeg := [
  ⟨1, 4259863, 1, 7, rkm128kMask56 5 [20]⟩,
  ⟨1, 4678500, 1, 8, rkm128kMask56 4 [8]⟩,
  ⟨1, 5958821, 1, 8, rkm128kMask56 4 [8]⟩,
  ⟨1, 4807054, 1, 8, rkm128kMask56 4 [8]⟩,
  ⟨1, 7079527, 1, 9, rkm128kMask56 4 [8]⟩,
  ⟨1, 5443824, 1, 8, rkm128kMask56 4 [8]⟩,
  ⟨1, 3996032, 1, 7, rkm128kMask56 4 [8]⟩,
  ⟨1, 3063226, 1, 7, []⟩,
  ⟨1, 3905937, 1, 7, rkm128kMask56 4 [8]⟩,
  ⟨1, 2015173, 1, 6, rkm128kMask56 5 [31]⟩,
  ⟨1, 28741, 1, 4, []⟩,
  ⟨1, 28741, 1, 4, rkm128kMask56 5 [26]⟩,
  ⟨1, 1000, 1, 4, rkm128kMask56 5 [26]⟩,
  ⟨1, 1091690, 1, 5, []⟩,
  ⟨2, 681619, 1, 5, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 76`. -/
def lm4k512l248krS0RowR76 : List ℕ :=
  [118056533783, 830210153164, 39326945, 6334201, 20160, 12, 0, 0]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 76`. -/
def lm4k512l248krS0AncR76 : RampKick128kAnchor :=
  ⟨76, lm4k512l248krS0SegsR76, lm4k512l248krS0RowR76⟩
/-- Active `RampKick128k` segments for `m = 4, r = 77` (`4` segments). -/
def lm4k512l248krS0SegsR77 : List Rkm128kSeg := [
  ⟨1, 14397589, 1, 12, rkm128kMask56 5 [24]⟩,
  ⟨1, 18236386, 1, 12, []⟩,
  ⟨1, 17560744, 1, 12, rkm128kMask56 5 [16]⟩,
  ⟨1, 12211793, 1, 10, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 77`. -/
def lm4k512l248krS0RowR77 : List ℕ :=
  [25039351178, 115912190324, 853360018329, 730098281]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 77`. -/
def lm4k512l248krS0AncR77 : RampKick128kAnchor :=
  ⟨77, lm4k512l248krS0SegsR77, lm4k512l248krS0RowR77⟩
/-- Active `RampKick128k` segments for `m = 4, r = 78` (`4` segments). -/
def lm4k512l248krS0SegsR78 : List Rkm128kSeg := [
  ⟨1, 932233, 1, 4, []⟩,
  ⟨1, 993506, 1, 4, []⟩,
  ⟨1, 1293768, 1, 6, []⟩,
  ⟨1, 74274890, 1, 26, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 78`. -/
def lm4k512l248krS0RowR78 : List ℕ :=
  [133322176, 8717091413, 161736280006, 829412714563]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 78`. -/
def lm4k512l248krS0AncR78 : RampKick128kAnchor :=
  ⟨78, lm4k512l248krS0SegsR78, lm4k512l248krS0RowR78⟩
/-- Active `RampKick128k` segments for `m = 4, r = 79` (`5` segments). -/
def lm4k512l248krS0SegsR79 : List Rkm128kSeg := [
  ⟨1, 477022, 1, 4, []⟩,
  ⟨1, 477022, 1, 4, []⟩,
  ⟨1, 602940, 1, 4, []⟩,
  ⟨1, 1009039, 1, 4, rkm128kMask56 4 [8]⟩,
  ⟨1, 36108374, 1, 18, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 79`. -/
def lm4k512l248krS0RowR79 : List ℕ :=
  [346335849895, 349516902150, 153269800239, 24581769843]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 79`. -/
def lm4k512l248krS0AncR79 : RampKick128kAnchor :=
  ⟨79, lm4k512l248krS0SegsR79, lm4k512l248krS0RowR79⟩
/-- Active `RampKick128k` segments for `m = 4, r = 80` (`15` segments). -/
def lm4k512l248krS0SegsR80 : List Rkm128kSeg := [
  ⟨1, 3912783, 1, 7, []⟩,
  ⟨1, 4288523, 1, 8, []⟩,
  ⟨1, 4512617, 1, 8, []⟩,
  ⟨1, 4512617, 1, 8, []⟩,
  ⟨1, 8284188, 1, 10, []⟩,
  ⟨1, 8284188, 1, 10, []⟩,
  ⟨1, 3885509, 1, 7, []⟩,
  ⟨1, 4269942, 1, 8, []⟩,
  ⟨1, 5230557, 1, 8, []⟩,
  ⟨1, 5230557, 1, 8, rkm128kMask56 5 [31]⟩,
  ⟨1, 66440, 1, 4, []⟩,
  ⟨1, 68408, 1, 4, rkm128kMask56 5 [26]⟩,
  ⟨1, 1000, 1, 4, rkm128kMask56 5 [26]⟩,
  ⟨2, 7949857, 1, 12, rkm128kMask56 8 [128]⟩,
  ⟨2, 7949858, 1, 12, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 80`. -/
def lm4k512l248krS0RowR80 : List ℕ :=
  [303158130, 15542160277, 51544710112, 381430992809, 403603925520, 137978797285, 9416686449,
   160184961]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 80`. -/
def lm4k512l248krS0AncR80 : RampKick128kAnchor :=
  ⟨80, lm4k512l248krS0SegsR80, lm4k512l248krS0RowR80⟩
/-- Active `RampKick128k` segments for `m = 4, r = 81` (`1` segments). -/
def lm4k512l248krS0SegsR81 : List Rkm128kSeg := [
  ⟨1, 62983576, 1, 25, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 81`. -/
def lm4k512l248krS0RowR81 : List ℕ :=
  [18395092790, 134968914442, 409792589597, 435971681160]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 81`. -/
def lm4k512l248krS0AncR81 : RampKick128kAnchor :=
  ⟨81, lm4k512l248krS0SegsR81, lm4k512l248krS0RowR81⟩
/-- Active `RampKick128k` segments for `m = 4, r = 82` (`15` segments). -/
def lm4k512l248krS0SegsR82 : List Rkm128kSeg := [
  ⟨1, 2976530, 1, 6, rkm128kMask56 5 [20]⟩,
  ⟨1, 4310019, 1, 8, rkm128kMask56 4 [8]⟩,
  ⟨1, 3920332, 1, 8, []⟩,
  ⟨1, 4063524, 1, 8, rkm128kMask56 4 [8]⟩,
  ⟨1, 5857857, 1, 8, rkm128kMask56 4 [8]⟩,
  ⟨1, 5103041, 1, 8, rkm128kMask56 4 [8]⟩,
  ⟨1, 2782639, 1, 6, []⟩,
  ⟨1, 2932317, 1, 6, rkm128kMask56 4 [8]⟩,
  ⟨1, 5174169, 1, 8, rkm128kMask56 4 [8]⟩,
  ⟨1, 3849680, 1, 8, rkm128kMask56 5 [31]⟩,
  ⟨1, 38041, 1, 4, []⟩,
  ⟨1, 36480, 1, 4, rkm128kMask56 5 [26]⟩,
  ⟨1, 1685, 1, 4, rkm128kMask56 5 [18]⟩,
  ⟨1, 2902700, 1, 6, rkm128kMask56 4 [8]⟩,
  ⟨2, 722384, 1, 6, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 82`. -/
def lm4k512l248krS0RowR82 : List ℕ :=
  [124026208885, 815736403905, 151537, 3081139, 15964, 13, 0, 0]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 82`. -/
def lm4k512l248krS0AncR82 : RampKick128kAnchor :=
  ⟨82, lm4k512l248krS0SegsR82, lm4k512l248krS0RowR82⟩
/-- Active `RampKick128k` segments for `m = 4, r = 83` (`4` segments). -/
def lm4k512l248krS0SegsR83 : List Rkm128kSeg := [
  ⟨1, 13699448, 1, 12, rkm128kMask56 5 [24]⟩,
  ⟨1, 18507327, 1, 14, []⟩,
  ⟨1, 15798626, 1, 12, rkm128kMask56 5 [16]⟩,
  ⟨1, 12001002, 1, 10, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 83`. -/
def lm4k512l248krS0RowR83 : List ℕ :=
  [26048063601, 116085425932, 851473275492, 1459048592]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 83`. -/
def lm4k512l248krS0AncR83 : RampKick128kAnchor :=
  ⟨83, lm4k512l248krS0SegsR83, lm4k512l248krS0RowR83⟩
/-- Active `RampKick128k` segments for `m = 4, r = 84` (`15` segments). -/
def lm4k512l248krS0SegsR84 : List Rkm128kSeg := [
  ⟨1, 10767684, 1, 10, []⟩,
  ⟨1, 5796956, 1, 8, []⟩,
  ⟨1, 5975639, 1, 8, []⟩,
  ⟨1, 5964939, 1, 8, []⟩,
  ⟨1, 10074310, 1, 10, []⟩,
  ⟨1, 10074310, 1, 10, []⟩,
  ⟨1, 5142086, 1, 8, []⟩,
  ⟨1, 5441881, 1, 8, []⟩,
  ⟨1, 5966758, 1, 8, []⟩,
  ⟨1, 5966758, 1, 8, rkm128kMask56 5 [31]⟩,
  ⟨1, 65008, 1, 4, []⟩,
  ⟨1, 65008, 1, 4, rkm128kMask56 5 [26]⟩,
  ⟨2, 6489, 1, 4, rkm128kMask56 7 [90]⟩,
  ⟨2, 749081, 1, 6, rkm128kMask56 8 [128]⟩,
  ⟨2, 749081, 1, 6, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 84`. -/
def lm4k512l248krS0RowR84 : List ℕ :=
  [292981579, 11804998400, 157986932965, 818813844168, 11064734741, 34432556, 20995, 2]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 84`. -/
def lm4k512l248krS0AncR84 : RampKick128kAnchor :=
  ⟨84, lm4k512l248krS0SegsR84, lm4k512l248krS0RowR84⟩
/-- Active `RampKick128k` segments for `m = 4, r = 85` (`4` segments). -/
def lm4k512l248krS0SegsR85 : List Rkm128kSeg := [
  ⟨1, 459878, 1, 4, []⟩,
  ⟨1, 459878, 1, 4, []⟩,
  ⟨1, 598861, 1, 4, rkm128kMask56 4 [8]⟩,
  ⟨1, 35007545, 1, 18, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 85`. -/
def lm4k512l248krS0RowR85 : List ℕ :=
  [357952713911, 340765089793, 141362519010, 21546142349]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 85`. -/
def lm4k512l248krS0AncR85 : RampKick128kAnchor :=
  ⟨85, lm4k512l248krS0SegsR85, lm4k512l248krS0RowR85⟩
/-- Active `RampKick128k` segments for `m = 4, r = 86` (`15` segments). -/
def lm4k512l248krS0SegsR86 : List Rkm128kSeg := [
  ⟨1, 4371674, 1, 8, []⟩,
  ⟨1, 4067694, 1, 8, []⟩,
  ⟨1, 4350434, 1, 8, []⟩,
  ⟨1, 4350434, 1, 8, []⟩,
  ⟨1, 7832794, 1, 10, []⟩,
  ⟨1, 7832794, 1, 10, []⟩,
  ⟨1, 4170373, 1, 8, []⟩,
  ⟨1, 4116480, 1, 8, []⟩,
  ⟨1, 4790442, 1, 8, []⟩,
  ⟨1, 4790443, 1, 8, rkm128kMask56 5 [31]⟩,
  ⟨1, 75592, 1, 4, []⟩,
  ⟨1, 78356, 1, 4, rkm128kMask56 5 [26]⟩,
  ⟨1, 1000, 1, 4, rkm128kMask56 5 [26]⟩,
  ⟨2, 8441988, 1, 12, rkm128kMask56 8 [128]⟩,
  ⟨2, 8441988, 1, 12, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 86`. -/
def lm4k512l248krS0RowR86 : List ℕ :=
  [25867748, 10268979404, 25820203560, 311102871365, 438602217733, 196951275175, 16860657296,
   355572180]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 86`. -/
def lm4k512l248krS0AncR86 : RampKick128kAnchor :=
  ⟨86, lm4k512l248krS0SegsR86, lm4k512l248krS0RowR86⟩
/-- Active `RampKick128k` segments for `m = 4, r = 87` (`1` segments). -/
def lm4k512l248krS0SegsR87 : List Rkm128kSeg := [
  ⟨1, 64191099, 1, 25, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 87`. -/
def lm4k512l248krS0RowR87 : List ℕ :=
  [7692692806, 82923974567, 362651050967, 546489917129]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 87`. -/
def lm4k512l248krS0AncR87 : RampKick128kAnchor :=
  ⟨87, lm4k512l248krS0SegsR87, lm4k512l248krS0RowR87⟩
/-- Active `RampKick128k` segments for `m = 4, r = 88` (`1` segments). -/
def lm4k512l248krS0SegsR88 : List Rkm128kSeg := [
  ⟨1, 69510630, 1, 26, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 88`. -/
def lm4k512l248krS0RowR88 : List ℕ :=
  [1001444826, 25666403295, 242133220300, 731187282994]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 88`. -/
def lm4k512l248krS0AncR88 : RampKick128kAnchor :=
  ⟨88, lm4k512l248krS0SegsR88, lm4k512l248krS0RowR88⟩
/-- Active `RampKick128k` segments for `m = 4, r = 89` (`4` segments). -/
def lm4k512l248krS0SegsR89 : List Rkm128kSeg := [
  ⟨1, 695071, 1, 4, []⟩,
  ⟨1, 690891, 1, 4, []⟩,
  ⟨1, 899695, 1, 4, rkm128kMask56 4 [8]⟩,
  ⟨1, 52989227, 1, 22, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 89`. -/
def lm4k512l248krS0RowR89 : List ℕ :=
  [48632766815, 221400366248, 428748967059, 297367041464]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 89`. -/
def lm4k512l248krS0AncR89 : RampKick128kAnchor :=
  ⟨89, lm4k512l248krS0SegsR89, lm4k512l248krS0RowR89⟩
/-- Active `RampKick128k` segments for `m = 4, r = 90` (`4` segments). -/
def lm4k512l248krS0SegsR90 : List Rkm128kSeg := [
  ⟨1, 715891, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 906548, 1, 4, []⟩,
  ⟨1, 983111, 1, 4, rkm128kMask56 4 [8]⟩,
  ⟨1, 57173451, 1, 23, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 90`. -/
def lm4k512l248krS0RowR90 : List ℕ :=
  [18187142306, 133805355425, 409039419965, 438096882394]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 90`. -/
def lm4k512l248krS0AncR90 : RampKick128kAnchor :=
  ⟨90, lm4k512l248krS0SegsR90, lm4k512l248krS0RowR90⟩
/-- Active `RampKick128k` segments for `m = 4, r = 91` (`1` segments). -/
def lm4k512l248krS0SegsR91 : List Rkm128kSeg := [
  ⟨1, 36107531, 1, 18, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 91`. -/
def lm4k512l248krS0RowR91 : List ℕ :=
  [344937314900, 349866311365, 154804937398, 25210036553]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 91`. -/
def lm4k512l248krS0AncR91 : RampKick128kAnchor :=
  ⟨91, lm4k512l248krS0SegsR91, lm4k512l248krS0RowR91⟩
/-- Active `RampKick128k` segments for `m = 4, r = 92` (`1` segments). -/
def lm4k512l248krS0SegsR92 : List Rkm128kSeg := [
  ⟨1, 67982737, 1, 26, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 92`. -/
def lm4k512l248krS0RowR92 : List ℕ :=
  [1011785340, 25636002783, 241322020325, 732018118072]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 92`. -/
def lm4k512l248krS0AncR92 : RampKick128kAnchor :=
  ⟨92, lm4k512l248krS0SegsR92, lm4k512l248krS0RowR92⟩
/-- Active `RampKick128k` segments for `m = 4, r = 93` (`16` segments). -/
def lm4k512l248krS0SegsR93 : List Rkm128kSeg := [
  ⟨1, 328034, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 309380, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 309380, 1, 4, []⟩,
  ⟨1, 309380, 1, 4, rkm128kMask56 5 [28]⟩,
  ⟨1, 316467, 1, 4, rkm128kMask56 4 [8]⟩,
  ⟨1, 281909, 1, 4, rkm128kMask56 5 [20]⟩,
  ⟨1, 310730, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 288646, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 404647, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 390136, 1, 4, []⟩,
  ⟨1, 369968, 1, 4, []⟩,
  ⟨1, 369968, 1, 4, rkm128kMask56 4 [12]⟩,
  ⟨1, 12987990, 1, 12, rkm128kMask56 5 [16]⟩,
  ⟨1, 13242089, 1, 12, []⟩,
  ⟨1, 15096823, 1, 12, rkm128kMask56 5 [16]⟩,
  ⟨1, 11491530, 1, 12, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 93`. -/
def lm4k512l248krS0RowR93 : List ℕ :=
  [31801726093, 113535800523, 853397954928, 522703871]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 93`. -/
def lm4k512l248krS0AncR93 : RampKick128kAnchor :=
  ⟨93, lm4k512l248krS0SegsR93, lm4k512l248krS0RowR93⟩
/-- Active `RampKick128k` segments for `m = 4, r = 94` (`3` segments). -/
def lm4k512l248krS0SegsR94 : List Rkm128kSeg := [
  ⟨1, 938847, 1, 4, []⟩,
  ⟨1, 938847, 1, 4, []⟩,
  ⟨1, 68467391, 1, 26, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 94`. -/
def lm4k512l248krS0RowR94 : List ℕ :=
  [179727017, 9609734881, 164321766811, 825887645407]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 94`. -/
def lm4k512l248krS0AncR94 : RampKick128kAnchor :=
  ⟨94, lm4k512l248krS0SegsR94, lm4k512l248krS0RowR94⟩
/-- Active `RampKick128k` segments for `m = 4, r = 95` (`1` segments). -/
def lm4k512l248krS0SegsR95 : List Rkm128kSeg := [
  ⟨1, 35157722, 1, 18, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 95`. -/
def lm4k512l248krS0RowR95 : List ℕ :=
  [347841951898, 347758491603, 151804075894, 24411026323]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 95`. -/
def lm4k512l248krS0AncR95 : RampKick128kAnchor :=
  ⟨95, lm4k512l248krS0SegsR95, lm4k512l248krS0RowR95⟩
/-- Active `RampKick128k` segments for `m = 4, r = 96` (`4` segments). -/
def lm4k512l248krS0SegsR96 : List Rkm128kSeg := [
  ⟨1, 30366908, 1, 16, []⟩,
  ⟨2, 16810534, 1, 18, []⟩,
  ⟨4, 9056841, 1, 18, []⟩,
  ⟨8, 4872470, 1, 16, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 96`. -/
def lm4k512l248krS0RowR96 : List ℕ :=
  [19390940, 6136286, 567805162, 3569577061, 18486608977, 73039188008, 173991891054,
   253113686216, 236921489063, 149006618084, 65194442075, 20426401711, 4695273584, 807730006,
   105673043, 10646951, 833973, 51110, 2456, 91, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 96`. -/
def lm4k512l248krS0AncR96 : RampKick128kAnchor :=
  ⟨96, lm4k512l248krS0SegsR96, lm4k512l248krS0RowR96⟩
/-- Active `RampKick128k` segments for `m = 4, r = 102` (`1` segments). -/
def lm4k512l248krS0SegsR102 : List Rkm128kSeg := [
  ⟨1, 68383584, 1, 28, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 102`. -/
def lm4k512l248krS0RowR102 : List ℕ :=
  [98628198, 6766458108, 141678393681, 851456224050]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 102`. -/
def lm4k512l248krS0AncR102 : RampKick128kAnchor :=
  ⟨102, lm4k512l248krS0SegsR102, lm4k512l248krS0RowR102⟩
/-- Active `RampKick128k` segments for `m = 4, r = 104` (`16` segments). -/
def lm4k512l248krS0SegsR104 : List Rkm128kSeg := [
  ⟨1, 198607, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 197375, 1, 4, []⟩,
  ⟨1, 195200, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 184246, 1, 4, []⟩,
  ⟨1, 188591, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 208613, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 187872, 1, 4, []⟩,
  ⟨1, 196923, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 380656, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 404035, 1, 4, []⟩,
  ⟨1, 405232, 1, 4, []⟩,
  ⟨1, 396444, 1, 4, rkm128kMask56 4 [12]⟩,
  ⟨1, 14774286, 1, 12, rkm128kMask56 4 [8]⟩,
  ⟨1, 6340240, 1, 8, rkm128kMask56 4 [8]⟩,
  ⟨1, 9165722, 1, 10, rkm128kMask56 4 [8]⟩,
  ⟨1, 6675872, 1, 10, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 104`. -/
def lm4k512l248krS0RowR104 : List ℕ :=
  [130457100439, 812217960932, 1243547211, 120365323]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 104`. -/
def lm4k512l248krS0AncR104 : RampKick128kAnchor :=
  ⟨104, lm4k512l248krS0SegsR104, lm4k512l248krS0RowR104⟩
/-- Active `RampKick128k` segments for `m = 4, r = 105` (`4` segments). -/
def lm4k512l248krS0SegsR105 : List Rkm128kSeg := [
  ⟨1, 12352376, 1, 12, rkm128kMask56 5 [24]⟩,
  ⟨1, 15807168, 1, 12, []⟩,
  ⟨1, 14464928, 1, 12, rkm128kMask56 5 [16]⟩,
  ⟨1, 10686944, 1, 12, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 105`. -/
def lm4k512l248krS0RowR105 : List ℕ :=
  [26031727966, 115249146665, 851789226043, 1721680617]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 105`. -/
def lm4k512l248krS0AncR105 : RampKick128kAnchor :=
  ⟨105, lm4k512l248krS0SegsR105, lm4k512l248krS0RowR105⟩
/-- Active `RampKick128k` segments for `m = 4, r = 106` (`3` segments). -/
def lm4k512l248krS0SegsR106 : List Rkm128kSeg := [
  ⟨1, 1050159, 1, 6, []⟩,
  ⟨1, 1050159, 1, 6, []⟩,
  ⟨1, 64313995, 1, 26, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 106`. -/
def lm4k512l248krS0RowR106 : List ℕ :=
  [168948186, 8987665603, 158048941129, 832793556392]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 106`. -/
def lm4k512l248krS0AncR106 : RampKick128kAnchor :=
  ⟨106, lm4k512l248krS0SegsR106, lm4k512l248krS0RowR106⟩
/-- Active `RampKick128k` segments for `m = 4, r = 107` (`12` segments). -/
def lm4k512l248krS0SegsR107 : List Rkm128kSeg := [
  ⟨1, 132713, 1, 4, []⟩,
  ⟨1, 132713, 1, 4, []⟩,
  ⟨1, 132713, 1, 4, []⟩,
  ⟨1, 132713, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 185389, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 438334, 1, 4, []⟩,
  ⟨1, 605696, 1, 4, []⟩,
  ⟨1, 430387, 1, 4, rkm128kMask56 4 [8]⟩,
  ⟨1, 2165843, 1, 6, rkm128kMask56 4 [8]⟩,
  ⟨1, 2165843, 1, 6, rkm128kMask56 4 [8]⟩,
  ⟨1, 13961828, 1, 12, []⟩,
  ⟨1, 13961828, 1, 12, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 107`. -/
def lm4k512l248krS0RowR107 : List ℕ :=
  [319140688402, 365330515413, 177542913865, 30218920552]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 107`. -/
def lm4k512l248krS0AncR107 : RampKick128kAnchor :=
  ⟨107, lm4k512l248krS0SegsR107, lm4k512l248krS0RowR107⟩
/-- Active `RampKick128k` segments for `m = 4, r = 108` (`4` segments). -/
def lm4k512l248krS0SegsR108 : List Rkm128kSeg := [
  ⟨1, 35394938, 1, 19, []⟩,
  ⟨2, 17808869, 1, 18, rkm128kMask56 9 [256]⟩,
  ⟨3, 16108120, 1, 23, rkm128kMask56 5 [22]⟩,
  ⟨8, 2787892, 1, 13, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 108`. -/
def lm4k512l248krS0RowR108 : List ℕ :=
  [265362357, 10576234, 445067788, 346477423, 746934152, 701597, 6346902397, 123178852428,
   338562149695, 330739847432, 153775339725, 39280564430, 5636884149, 477262628, 25401038,
   900532, 22272, 395, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 108`. -/
def lm4k512l248krS0AncR108 : RampKick128kAnchor :=
  ⟨108, lm4k512l248krS0SegsR108, lm4k512l248krS0RowR108⟩
/-- Active `RampKick128k` segments for `m = 4, r = 110` (`8` segments). -/
def lm4k512l248krS0SegsR110 : List Rkm128kSeg := [
  ⟨1, 103190, 1, 4, []⟩,
  ⟨1, 103190, 1, 4, []⟩,
  ⟨1, 103190, 1, 4, []⟩,
  ⟨1, 103190, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 10065145, 1, 10, rkm128kMask56 4 [8]⟩,
  ⟨1, 8174311, 1, 10, rkm128kMask56 4 [8]⟩,
  ⟨1, 11911300, 1, 12, rkm128kMask56 4 [8]⟩,
  ⟨1, 8310358, 1, 10, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 110`. -/
def lm4k512l248krS0RowR110 : List ℕ :=
  [127644274103, 799114084424, 9468568551, 201708143]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 110`. -/
def lm4k512l248krS0AncR110 : RampKick128kAnchor :=
  ⟨110, lm4k512l248krS0SegsR110, lm4k512l248krS0RowR110⟩
/-- Active `RampKick128k` segments for `m = 4, r = 111` (`20` segments). -/
def lm4k512l248krS0SegsR111 : List Rkm128kSeg := [
  ⟨1, 157103, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 157104, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 155278, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 161358, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 132211, 1, 4, []⟩,
  ⟨1, 371092, 1, 4, []⟩,
  ⟨1, 330642, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 321820, 1, 4, []⟩,
  ⟨1, 357362, 1, 4, []⟩,
  ⟨1, 352429, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 353549, 1, 4, []⟩,
  ⟨1, 337109, 1, 4, []⟩,
  ⟨1, 303235, 1, 4, []⟩,
  ⟨1, 760543, 1, 4, []⟩,
  ⟨1, 468161, 1, 4, []⟩,
  ⟨1, 453343, 1, 4, rkm128kMask56 4 [12]⟩,
  ⟨1, 14444966, 1, 12, []⟩,
  ⟨1, 10960286, 1, 12, rkm128kMask56 5 [16]⟩,
  ⟨1, 14662768, 1, 12, rkm128kMask56 5 [16]⟩,
  ⟨1, 7510617, 1, 10, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 111`. -/
def lm4k512l248krS0RowR111 : List ℕ :=
  [28192287699, 86697925865, 883928859852, 1149559811]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 111`. -/
def lm4k512l248krS0AncR111 : RampKick128kAnchor :=
  ⟨111, lm4k512l248krS0SegsR111, lm4k512l248krS0RowR111⟩
/-- Active `RampKick128k` segments for `m = 4, r = 113` (`1` segments). -/
def lm4k512l248krS0SegsR113 : List Rkm128kSeg := [
  ⟨1, 62933632, 1, 26, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 113`. -/
def lm4k512l248krS0RowR113 : List ℕ :=
  [440067205, 15304466124, 194622724421, 789628897282]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 113`. -/
def lm4k512l248krS0AncR113 : RampKick128kAnchor :=
  ⟨113, lm4k512l248krS0SegsR113, lm4k512l248krS0RowR113⟩
/-- Active `RampKick128k` segments for `m = 4, r = 114` (`12` segments). -/
def lm4k512l248krS0SegsR114 : List Rkm128kSeg := [
  ⟨1, 454160, 1, 4, []⟩,
  ⟨1, 472547, 1, 4, []⟩,
  ⟨1, 472546, 1, 4, []⟩,
  ⟨1, 444979, 1, 4, []⟩,
  ⟨1, 621616, 1, 4, []⟩,
  ⟨1, 621616, 1, 4, []⟩,
  ⟨1, 876619, 1, 6, []⟩,
  ⟨1, 876619, 1, 6, rkm128kMask56 4 [8]⟩,
  ⟨1, 3992414, 1, 8, []⟩,
  ⟨1, 4379991, 1, 8, rkm128kMask56 5 [16]⟩,
  ⟨1, 23615916, 1, 15, []⟩,
  ⟨1, 21924323, 1, 15, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 114`. -/
def lm4k512l248krS0RowR114 : List ℕ :=
  [3756255378, 43887259737, 303574280036, 648737621840]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 114`. -/
def lm4k512l248krS0AncR114 : RampKick128kAnchor :=
  ⟨114, lm4k512l248krS0SegsR114, lm4k512l248krS0RowR114⟩
/-- Active `RampKick128k` segments for `m = 4, r = 115` (`1` segments). -/
def lm4k512l248krS0SegsR115 : List Rkm128kSeg := [
  ⟨1, 61812344, 1, 26, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 115`. -/
def lm4k512l248krS0RowR115 : List ℕ :=
  [618180397, 18606391841, 210117384750, 770651672049]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 115`. -/
def lm4k512l248krS0AncR115 : RampKick128kAnchor :=
  ⟨115, lm4k512l248krS0SegsR115, lm4k512l248krS0RowR115⟩
/-- Active `RampKick128k` segments for `m = 4, r = 116` (`8` segments). -/
def lm4k512l248krS0SegsR116 : List Rkm128kSeg := [
  ⟨1, 16877916, 1, 13, []⟩,
  ⟨1, 14533216, 1, 12, []⟩,
  ⟨2, 5969983, 1, 12, []⟩,
  ⟨2, 6506303, 1, 12, []⟩,
  ⟨2, 7739867, 1, 12, []⟩,
  ⟨2, 7172582, 1, 12, rkm128kMask56 2 [2]⟩,
  ⟨2, 7841272, 1, 12, rkm128kMask56 2 [2]⟩,
  ⟨2, 7891806, 1, 12, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 116`. -/
def lm4k512l248krS0RowR116 : List ℕ :=
  [25550077, 4386891, 248664798, 12056914, 1222790166, 16289116917, 335585884155, 646592695548]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 116`. -/
def lm4k512l248krS0AncR116 : RampKick128kAnchor :=
  ⟨116, lm4k512l248krS0SegsR116, lm4k512l248krS0RowR116⟩
/-- Active `RampKick128k` segments for `m = 4, r = 118` (`12` segments). -/
def lm4k512l248krS0SegsR118 : List Rkm128kSeg := [
  ⟨1, 98537, 1, 4, []⟩,
  ⟨1, 98537, 1, 4, []⟩,
  ⟨1, 98537, 1, 4, []⟩,
  ⟨1, 103503, 1, 4, []⟩,
  ⟨1, 103502, 1, 4, []⟩,
  ⟨1, 103502, 1, 4, []⟩,
  ⟨1, 103502, 1, 4, []⟩,
  ⟨1, 103503, 1, 4, rkm128kMask56 3 [4]⟩,
  ⟨1, 9858667, 1, 10, rkm128kMask56 4 [8]⟩,
  ⟨1, 9653890, 1, 10, rkm128kMask56 4 [8]⟩,
  ⟨1, 8230943, 1, 10, rkm128kMask56 4 [8]⟩,
  ⟨1, 7662775, 1, 10, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 118`. -/
def lm4k512l248krS0RowR118 : List ℕ :=
  [158298264549, 731843715257, 34035777409, 513407266]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 118`. -/
def lm4k512l248krS0AncR118 : RampKick128kAnchor :=
  ⟨118, lm4k512l248krS0SegsR118, lm4k512l248krS0RowR118⟩
/-- Active `RampKick128k` segments for `m = 4, r = 119` (`16` segments). -/
def lm4k512l248krS0SegsR119 : List Rkm128kSeg := [
  ⟨1, 133803, 1, 4, []⟩,
  ⟨1, 156744, 1, 4, []⟩,
  ⟨1, 156744, 1, 4, []⟩,
  ⟨1, 156744, 1, 4, rkm128kMask56 4 [8]⟩,
  ⟨1, 134220, 1, 4, rkm128kMask56 4 [8]⟩,
  ⟨1, 195427, 1, 4, []⟩,
  ⟨1, 168699, 1, 4, []⟩,
  ⟨1, 163653, 1, 4, []⟩,
  ⟨1, 222140, 1, 4, []⟩,
  ⟨1, 222140, 1, 4, []⟩,
  ⟨1, 222140, 1, 4, []⟩,
  ⟨1, 222140, 1, 4, rkm128kMask56 4 [12]⟩,
  ⟨1, 15724248, 1, 14, rkm128kMask56 5 [16]⟩,
  ⟨1, 14694159, 1, 12, rkm128kMask56 5 [16]⟩,
  ⟨1, 9503884, 1, 10, rkm128kMask56 5 [16]⟩,
  ⟨1, 7584817, 1, 10, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 119`. -/
def lm4k512l248krS0RowR119 : List ℕ :=
  [46603647280, 98322525573, 824756603986, 29381250302]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 119`. -/
def lm4k512l248krS0AncR119 : RampKick128kAnchor :=
  ⟨119, lm4k512l248krS0SegsR119, lm4k512l248krS0RowR119⟩
/-- Active `RampKick128k` segments for `m = 4, r = 120` (`8` segments). -/
def lm4k512l248krS0SegsR120 : List Rkm128kSeg := [
  ⟨1, 17133433, 1, 14, []⟩,
  ⟨1, 16917946, 1, 14, []⟩,
  ⟨2, 14010749, 1, 18, []⟩,
  ⟨3, 8540659, 1, 17, rkm128kMask56 2 [2]⟩,
  ⟨4, 4614372, 1, 14, rkm128kMask56 3 [6]⟩,
  ⟨4, 4308028, 1, 14, rkm128kMask56 16 [32828]⟩,
  ⟨5, 4778360, 1, 16, rkm128kMask56 20 [688302]⟩,
  ⟨8, 2668722, 1, 14, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 120`. -/
def lm4k512l248krS0RowR120 : List ℕ :=
  [45358133, 94877004, 520271810, 314452376, 54706938, 910942390, 169836, 789290957, 158240510,
   34510401300, 157720845920, 300917261574, 232676254133, 222363187549, 44683207235, 4013815787,
   207574038, 6777530, 149569, 2331, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 120`. -/
def lm4k512l248krS0AncR120 : RampKick128kAnchor :=
  ⟨120, lm4k512l248krS0SegsR120, lm4k512l248krS0RowR120⟩
/-- Active `RampKick128k` segments for `m = 4, r = 122` (`16` segments). -/
def lm4k512l248krS0SegsR122 : List Rkm128kSeg := [
  ⟨1, 251603, 1, 4, []⟩,
  ⟨1, 273483, 1, 4, []⟩,
  ⟨1, 273480, 1, 4, []⟩,
  ⟨1, 273483, 1, 4, []⟩,
  ⟨1, 273480, 1, 4, []⟩,
  ⟨1, 273483, 1, 4, []⟩,
  ⟨1, 273480, 1, 4, []⟩,
  ⟨1, 273483, 1, 4, rkm128kMask56 2 [2]⟩,
  ⟨1, 71862, 1, 4, rkm128kMask56 2 [2]⟩,
  ⟨1, 341513, 1, 4, rkm128kMask56 2 [2]⟩,
  ⟨1, 71862, 1, 4, rkm128kMask56 2 [2]⟩,
  ⟨1, 371218, 1, 4, rkm128kMask56 5 [20]⟩,
  ⟨1, 7597074, 1, 10, rkm128kMask56 5 [16]⟩,
  ⟨1, 9861659, 1, 11, rkm128kMask56 5 [16]⟩,
  ⟨1, 10498230, 1, 11, rkm128kMask56 4 [8]⟩,
  ⟨1, 9821552, 1, 11, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 122`. -/
def lm4k512l248krS0RowR122 : List ℕ :=
  [82327179298, 893982091176, 54389981, 891829]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 122`. -/
def lm4k512l248krS0AncR122 : RampKick128kAnchor :=
  ⟨122, lm4k512l248krS0SegsR122, lm4k512l248krS0RowR122⟩
/-- Active `RampKick128k` segments for `m = 4, r = 123` (`12` segments). -/
def lm4k512l248krS0SegsR123 : List Rkm128kSeg := [
  ⟨1, 192227, 1, 4, []⟩,
  ⟨1, 192227, 1, 4, []⟩,
  ⟨1, 200700, 1, 4, []⟩,
  ⟨1, 200700, 1, 4, []⟩,
  ⟨1, 200700, 1, 4, []⟩,
  ⟨1, 200700, 1, 4, []⟩,
  ⟨1, 200700, 1, 4, []⟩,
  ⟨1, 200700, 1, 4, rkm128kMask56 4 [12]⟩,
  ⟨1, 11460436, 1, 12, rkm128kMask56 5 [16]⟩,
  ⟨1, 12978230, 1, 12, []⟩,
  ⟨1, 13534507, 1, 12, rkm128kMask56 5 [16]⟩,
  ⟨1, 10026574, 1, 12, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 123`. -/
def lm4k512l248krS0RowR123 : List ℕ :=
  [33007301771, 105350423633, 860431840247, 90130430]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 123`. -/
def lm4k512l248krS0AncR123 : RampKick128kAnchor :=
  ⟨123, lm4k512l248krS0SegsR123, lm4k512l248krS0RowR123⟩
/-- Active `RampKick128k` segments for `m = 4, r = 124` (`1` segments). -/
def lm4k512l248krS0SegsR124 : List Rkm128kSeg := [
  ⟨1, 61242514, 1, 28, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 124`. -/
def lm4k512l248krS0RowR124 : List ℕ :=
  [204677848, 9660552815, 160453483994, 829680092069]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 124`. -/
def lm4k512l248krS0AncR124 : RampKick128kAnchor :=
  ⟨124, lm4k512l248krS0SegsR124, lm4k512l248krS0RowR124⟩
/-- Active `RampKick128k` segments for `m = 4, r = 125` (`3` segments). -/
def lm4k512l248krS0SegsR125 : List Rkm128kSeg := [
  ⟨1, 379226, 1, 4, []⟩,
  ⟨1, 379226, 1, 4, []⟩,
  ⟨1, 43307850, 1, 22, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 125`. -/
def lm4k512l248krS0RowR125 : List ℕ :=
  [79344152163, 274793645054, 411923080453, 225575087670]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 125`. -/
def lm4k512l248krS0AncR125 : RampKick128kAnchor :=
  ⟨125, lm4k512l248krS0SegsR125, lm4k512l248krS0RowR125⟩
/-- Active `RampKick128k` segments for `m = 4, r = 126` (`4` segments). -/
def lm4k512l248krS0SegsR126 : List Rkm128kSeg := [
  ⟨1, 518654, 1, 4, []⟩,
  ⟨1, 524076, 1, 4, []⟩,
  ⟨1, 711353, 1, 4, rkm128kMask56 4 [12]⟩,
  ⟨1, 43960617, 1, 22, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 126`. -/
def lm4k512l248krS0RowR126 : List ℕ :=
  [54961923735, 237873718734, 428854898971, 273897208822]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 126`. -/
def lm4k512l248krS0AncR126 : RampKick128kAnchor :=
  ⟨126, lm4k512l248krS0SegsR126, lm4k512l248krS0RowR126⟩
/-- Active `RampKick128k` segments for `m = 4, r = 127` (`1` segments). -/
def lm4k512l248krS0SegsR127 : List Rkm128kSeg := [
  ⟨1, 53267990, 1, 25, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 127`. -/
def lm4k512l248krS0RowR127 : List ℕ :=
  [7478028862, 79705655725, 354703665716, 557866353979]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 127`. -/
def lm4k512l248krS0AncR127 : RampKick128kAnchor :=
  ⟨127, lm4k512l248krS0SegsR127, lm4k512l248krS0RowR127⟩
/-- Active `RampKick128k` segments for `m = 4, r = 132` (`4` segments). -/
def lm4k512l248krS0SegsR132 : List Rkm128kSeg := [
  ⟨1, 29465011, 1, 18, []⟩,
  ⟨2, 16263272, 1, 18, []⟩,
  ⟨4, 7721799, 1, 18, rkm128kMask56 16 [40962]⟩,
  ⟨4, 7102594, 1, 18, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 132`. -/
def lm4k512l248krS0RowR132 : List ℕ :=
  [14117015, 823613, 149586087, 248003765, 137653370, 6063921925, 59552912521, 195958158260,
   304214923938, 259561172245, 126613322040, 39887125849, 6953560613, 605541319, 24149032,
   347130]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 132`. -/
def lm4k512l248krS0AncR132 : RampKick128kAnchor :=
  ⟨132, lm4k512l248krS0SegsR132, lm4k512l248krS0RowR132⟩
/-- Active `RampKick128k` segments for `m = 4, r = 144` (`8` segments). -/
def lm4k512l248krS0SegsR144 : List Rkm128kSeg := [
  ⟨1, 26039953, 1, 18, []⟩,
  ⟨2, 10628471, 1, 15, []⟩,
  ⟨3, 5675867, 1, 14, rkm128kMask56 12 [3072]⟩,
  ⟨3, 8105401, 1, 17, rkm128kMask56 13 [4098]⟩,
  ⟨4, 6881951, 1, 18, rkm128kMask56 3 [4]⟩,
  ⟨5, 5275298, 1, 17, rkm128kMask56 21 [1540307]⟩,
  ⟨6, 3672249, 1, 15, rkm128kMask56 25 [22283031]⟩,
  ⟨8, 3221924, 1, 17, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 144`. -/
def lm4k512l248krS0RowR144 : List ℕ :=
  [8653191, 4482129, 16870202, 74727, 141435506, 352479, 125404840, 13042487, 75263802,
   2395808658, 8011108819, 7488876826, 14879264408, 84836441051, 309974128374, 394563196418,
   142403614421, 30822990512, 3925718274, 298022931, 14509945, 481210, 11264, 189, 2, 0, 0, 0,
   0, 0, 0, 0]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 144`. -/
def lm4k512l248krS0AncR144 : RampKick128kAnchor :=
  ⟨144, lm4k512l248krS0SegsR144, lm4k512l248krS0RowR144⟩
/-- Active `RampKick128k` segments for `m = 4, r = 156` (`8` segments). -/
def lm4k512l248krS0SegsR156 : List Rkm128kSeg := [
  ⟨1, 12834376, 1, 12, []⟩,
  ⟨1, 15444809, 1, 13, []⟩,
  ⟨2, 12823145, 1, 18, rkm128kMask56 9 [256]⟩,
  ⟨3, 4408519, 1, 12, rkm128kMask56 13 [5632]⟩,
  ⟨4, 5608849, 1, 15, rkm128kMask56 16 [55298]⟩,
  ⟨4, 6742667, 1, 18, rkm128kMask56 15 [24612]⟩,
  ⟨5, 3743900, 1, 15, rkm128kMask56 21 [1155238]⟩,
  ⟨8, 1150263, 1, 12, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 156`. -/
def lm4k512l248krS0RowR156 : List ℕ :=
  [144990699, 39950720, 13645144, 649834543, 178554415, 419058783, 174346066, 418403742,
   742098607, 48922838431, 118266448791, 829871865766, 358910, 109184731, 35096168, 830386,
   134960, 85348, 9814, 406, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 156`. -/
def lm4k512l248krS0AncR156 : RampKick128kAnchor :=
  ⟨156, lm4k512l248krS0SegsR156, lm4k512l248krS0RowR156⟩
/-- Active `RampKick128k` segments for `m = 4, r = 168` (`8` segments). -/
def lm4k512l248krS0SegsR168 : List Rkm128kSeg := [
  ⟨1, 8168473, 1, 10, []⟩,
  ⟨1, 12603525, 1, 12, []⟩,
  ⟨1, 9038098, 1, 12, []⟩,
  ⟨2, 13657541, 1, 18, rkm128kMask56 9 [256]⟩,
  ⟨2, 4442258, 1, 10, rkm128kMask56 2 [2]⟩,
  ⟨3, 4048887, 1, 12, rkm128kMask56 13 [5122]⟩,
  ⟨3, 3192732, 1, 12, rkm128kMask56 12 [2576]⟩,
  ⟨8, 1192283, 1, 12, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 168`. -/
def lm4k512l248krS0RowR168 : List ℕ :=
  [63341055, 252940109, 1195298567, 7072943, 1454150443, 19037335495, 157513431461,
   820160693779, 133774652, 166108651, 935123, 37557, 927, 5, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 168`. -/
def lm4k512l248krS0AncR168 : RampKick128kAnchor :=
  ⟨168, lm4k512l248krS0SegsR168, lm4k512l248krS0RowR168⟩
/-- Active `RampKick128k` segments for `m = 4, r = 184` (`30` segments). -/
def lm4k512l248krS0SegsR184 : List Rkm128kSeg := [
  ⟨1, 18480006, 1, 15, []⟩,
  ⟨2, 9709194, 1, 15, []⟩,
  ⟨3, 6241382, 1, 15, rkm128kMask56 13 [6144]⟩,
  ⟨4, 5687068, 1, 17, rkm128kMask56 17 [65536]⟩,
  ⟨4, 2229078, 1, 10, []⟩,
  ⟨4, 1710457, 1, 10, []⟩,
  ⟨5, 1191234, 1, 8, rkm128kMask56 2 [3]⟩,
  ⟨5, 1585312, 1, 10, rkm128kMask56 3 [4]⟩,
  ⟨5, 1591127, 1, 10, rkm128kMask56 4 [8]⟩,
  ⟨6, 1469287, 1, 10, rkm128kMask56 20 [524308]⟩,
  ⟨6, 1583081, 1, 10, rkm128kMask56 6 [40]⟩,
  ⟨7, 1668289, 1, 12, rkm128kMask56 7 [111]⟩,
  ⟨7, 1152981, 1, 10, rkm128kMask56 9 [279]⟩,
  ⟨8, 1451508, 1, 12, rkm128kMask56 11 [1951]⟩,
  ⟨8, 1570170, 1, 12, rkm128kMask56 12 [2159]⟩,
  ⟨9, 1685177, 1, 12, rkm128kMask56 35 [17179883907]⟩,
  ⟨10, 1371028, 1, 12, rkm128kMask56 33 [4294997767]⟩,
  ⟨10, 1352604, 1, 12, rkm128kMask56 35 [17179899135]⟩,
  ⟨11, 1504269, 1, 14, rkm128kMask56 35 [18253912140]⟩,
  ⟨11, 978867, 1, 10, rkm128kMask56 45 [35114042097792]⟩,
  ⟨11, 14603, 1, 4, rkm128kMask56 45 [22059221458102]⟩,
  ⟨14, 1171479, 1, 14, rkm128kMask56 53 [5123797201816149]⟩,
  ⟨14, 1196685, 1, 14, rkm128kMask56 57 [67303274354458707, 1]⟩,
  ⟨14, 64671, 1, 6, rkm128kMask56 53 [4921831735692545]⟩,
  ⟨14, 64669, 1, 6, rkm128kMask56 57 [62768919802281969, 1]⟩,
  ⟨14, 11412, 1, 4, rkm128kMask56 57 [23659598036337633, 1]⟩,
  ⟨20, 1556169, 1, 18, rkm128kMask56 54 [12055079849171948]⟩,
  ⟨26, 1364856, 1, 20, rkm128kMask56 54 [11936298504539668]⟩,
  ⟨26, 1364851, 1, 20, rkm128kMask56 52 [3565719469990538]⟩,
  ⟨46, 705780, 1, 18, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 184`. -/
def lm4k512l248krS0RowR184 : List ℕ :=
  [187463, 11738, 858292, 755538, 1469473, 419200, 2666985, 343985, 5482031, 23666954, 1146197,
   12304084, 63481224, 29373613, 651094169, 289663203, 1139405196, 1126195108, 2278788422,
   491712791, 39615674, 1007081029, 1084488326, 7338993682, 3720654155, 117550381, 13623873,
   2682712515, 102309091, 3267907027, 16086577, 272130098, 626810197, 288310944, 9857962205,
   70192564667, 226697375577, 200396104593, 266733879410, 175418440954, 23317918338, 578714740,
   64511736, 37304574, 5190470, 399639, 16918, 368, 21, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 184`. -/
def lm4k512l248krS0AncR184 : RampKick128kAnchor :=
  ⟨184, lm4k512l248krS0SegsR184, lm4k512l248krS0RowR184⟩
/-- Active `RampKick128k` segments for `m = 4, r = 220` (`30` segments). -/
def lm4k512l248krS0SegsR220 : List Rkm128kSeg := [
  ⟨1, 6379601, 1, 10, rkm128kMask56 5 [24]⟩,
  ⟨1, 9068611, 1, 12, []⟩,
  ⟨1, 6128581, 1, 10, []⟩,
  ⟨1, 7805554, 1, 12, []⟩,
  ⟨2, 3190632, 1, 10, rkm128kMask56 7 [64]⟩,
  ⟨2, 4637348, 1, 12, []⟩,
  ⟨3, 2351980, 1, 10, rkm128kMask56 11 [1024]⟩,
  ⟨3, 2201849, 1, 10, []⟩,
  ⟨3, 1999390, 1, 10, rkm128kMask56 12 [2048]⟩,
  ⟨4, 2089663, 1, 12, rkm128kMask56 5 [16]⟩,
  ⟨4, 787913, 1, 8, rkm128kMask56 15 [16411]⟩,
  ⟨5, 1793883, 1, 12, rkm128kMask56 6 [62]⟩,
  ⟨5, 2258103, 1, 12, rkm128kMask56 16 [32836]⟩,
  ⟨6, 1984463, 1, 12, rkm128kMask56 24 [8388784]⟩,
  ⟨6, 1927752, 1, 12, rkm128kMask56 24 [8651131]⟩,
  ⟨7, 2170662, 1, 15, rkm128kMask56 29 [302514832]⟩,
  ⟨7, 1630428, 1, 12, rkm128kMask56 29 [336595516]⟩,
  ⟨8, 1548194, 1, 12, rkm128kMask56 33 [5440020204]⟩,
  ⟨9, 1651870, 1, 13, rkm128kMask56 37 [68996307823]⟩,
  ⟨9, 1338778, 1, 12, rkm128kMask56 37 [122146522368]⟩,
  ⟨10, 60095, 1, 4, rkm128kMask56 40 [922906326144]⟩,
  ⟨10, 1234276, 1, 12, rkm128kMask56 40 [955663851911]⟩,
  ⟨10, 1094161, 1, 12, rkm128kMask56 41 [1127965872187]⟩,
  ⟨10, 127447, 1, 6, rkm128kMask56 34 [11878472069]⟩,
  ⟨10, 173598, 1, 6, rkm128kMask56 41 [1918239768552]⟩,
  ⟨11, 29453, 1, 4, rkm128kMask56 45 [24155433157038]⟩,
  ⟨11, 1201938, 1, 14, rkm128kMask56 41 [2107085030144]⟩,
  ⟨12, 1673081, 1, 17, rkm128kMask56 42 [2290294548500]⟩,
  ⟨13, 1224407, 1, 15, rkm128kMask56 40 [732831387700]⟩,
  ⟨55, 213243, 1, 12, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 220`. -/
def lm4k512l248krS0RowR220 : List ℕ :=
  [2203243, 466730, 1047597, 20917, 388591, 3955450, 51944873, 1117901175, 754109864,
   1222416846, 231881096, 9716, 195273551, 331765254, 62177742, 57928, 106986289, 23250803,
   3289615, 715806744, 5084404, 78064160, 1335143564, 8624196574, 10480212322, 47786614024,
   178662938853, 743999651169, 1706589546, 2484828367, 6870660, 167771, 1600, 8, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 220`. -/
def lm4k512l248krS0AncR220 : RampKick128kAnchor :=
  ⟨220, lm4k512l248krS0SegsR220, lm4k512l248krS0RowR220⟩
/-- Active `RampKick128k` segments for `m = 4, r = 288` (`30` segments). -/
def lm4k512l248krS0SegsR288 : List Rkm128kSeg := [
  ⟨1, 8777810, 1, 12, []⟩,
  ⟨1, 10560377, 1, 13, []⟩,
  ⟨2, 5608220, 1, 14, rkm128kMask56 9 [384]⟩,
  ⟨2, 6810689, 1, 15, []⟩,
  ⟨3, 1664090, 1, 10, []⟩,
  ⟨3, 2025652, 1, 10, rkm128kMask56 13 [4096]⟩,
  ⟨4, 1647560, 1, 10, rkm128kMask56 13 [4098]⟩,
  ⟨4, 1605579, 1, 10, rkm128kMask56 2 [2]⟩,
  ⟨5, 1640403, 1, 12, rkm128kMask56 2 [2]⟩,
  ⟨5, 1492705, 1, 12, rkm128kMask56 17 [65536]⟩,
  ⟨6, 1402346, 1, 12, rkm128kMask56 18 [131124]⟩,
  ⟨6, 1671833, 1, 12, rkm128kMask56 18 [131563]⟩,
  ⟨7, 1293523, 1, 12, rkm128kMask56 28 [135004776]⟩,
  ⟨7, 1209579, 1, 12, rkm128kMask56 29 [400033404]⟩,
  ⟨8, 1265216, 1, 12, rkm128kMask56 33 [8453622243]⟩,
  ⟨8, 1572544, 1, 14, rkm128kMask56 32 [2151687857]⟩,
  ⟨9, 1143805, 1, 12, rkm128kMask56 36 [49383761785]⟩,
  ⟨10, 1138981, 1, 12, rkm128kMask56 39 [532005557060]⟩,
  ⟨10, 1163194, 1, 12, rkm128kMask56 39 [361381302913]⟩,
  ⟨11, 1786628, 1, 16, rkm128kMask56 42 [3590592665793]⟩,
  ⟨12, 39205, 1, 4, rkm128kMask56 46 [59901641220477]⟩,
  ⟨12, 786422, 1, 12, rkm128kMask56 47 [94922536474378]⟩,
  ⟨13, 1380339, 1, 17, rkm128kMask56 49 [282375848818921]⟩,
  ⟨13, 80914, 1, 6, rkm128kMask56 45 [31927721003265]⟩,
  ⟨13, 115136, 1, 6, rkm128kMask56 53 [9006370325984977]⟩,
  ⟨13, 19833, 1, 4, rkm128kMask56 53 [8615345771063340]⟩,
  ⟨14, 805279, 1, 14, rkm128kMask56 44 [10256411287556]⟩,
  ⟨15, 863108, 1, 14, rkm128kMask56 43 [5995780916489]⟩,
  ⟨15, 553293, 1, 12, rkm128kMask56 39 [455316899861]⟩,
  ⟨72, 157925, 1, 12, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 288`. -/
def lm4k512l248krS0RowR288 : List ℕ :=
  [91882, 22864, 15708, 1935715, 443830, 2168958, 220196115, 2618949, 1916011, 2700162,
   14314297, 109365990, 185666168, 126081618, 14088299, 11113035, 16681127, 191960136, 15877029,
   49820653, 119973799, 71782012, 559515857, 627725144, 221866796, 33641455, 626416099,
   2829051970, 7421526018, 53327304061, 178070710513, 755051677263, 69345744, 92607, 902350,
   66096, 6321, 13640, 673, 7, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 288`. -/
def lm4k512l248krS0AncR288 : RampKick128kAnchor :=
  ⟨288, lm4k512l248krS0SegsR288, lm4k512l248krS0RowR288⟩
/-- Active `RampKick128k` segments for `m = 4, r = 304` (`47` segments). -/
def lm4k512l248krS0SegsR304 : List Rkm128kSeg := [
  ⟨1, 1240735, 1, 6, rkm128kMask56 3 [4]⟩,
  ⟨1, 1298517, 1, 6, rkm128kMask56 5 [31]⟩,
  ⟨1, 5464662, 1, 10, []⟩,
  ⟨1, 6188012, 1, 10, []⟩,
  ⟨1, 6381546, 1, 10, []⟩,
  ⟨2, 5218628, 1, 14, []⟩,
  ⟨3, 3120360, 1, 12, []⟩,
  ⟨3, 1423316, 1, 10, []⟩,
  ⟨3, 2020058, 1, 10, []⟩,
  ⟨4, 1524053, 1, 10, rkm128kMask56 2 [2]⟩,
  ⟨4, 1565663, 1, 10, rkm128kMask56 15 [16387]⟩,
  ⟨4, 1337316, 1, 10, rkm128kMask56 15 [16387]⟩,
  ⟨5, 1040778, 1, 10, rkm128kMask56 17 [65537]⟩,
  ⟨5, 1115869, 1, 10, rkm128kMask56 5 [17]⟩,
  ⟨6, 1030192, 1, 10, rkm128kMask56 3 [4]⟩,
  ⟨6, 1029959, 1, 10, rkm128kMask56 25 [16777328]⟩,
  ⟨7, 1186643, 1, 12, rkm128kMask56 25 [17301748]⟩,
  ⟨7, 1217017, 1, 12, rkm128kMask56 9 [287]⟩,
  ⟨8, 1426464, 1, 12, rkm128kMask56 33 [4299162980]⟩,
  ⟨8, 1001083, 1, 12, rkm128kMask56 24 [8392257]⟩,
  ⟨9, 884069, 1, 10, rkm128kMask56 37 [120250701185]⟩,
  ⟨9, 945303, 1, 12, rkm128kMask56 37 [133093669880]⟩,
  ⟨10, 1092945, 1, 12, rkm128kMask56 39 [279508435609]⟩,
  ⟨11, 1222012, 1, 15, rkm128kMask56 31 [1073812810]⟩,
  ⟨11, 894086, 1, 12, rkm128kMask56 44 [16973174124840]⟩,
  ⟨12, 943670, 1, 12, rkm128kMask56 47 [140665548020769]⟩,
  ⟨13, 949134, 1, 14, rkm128kMask56 51 [1707563034787914]⟩,
  ⟨14, 1053677, 1, 15, rkm128kMask56 56 [40568388479382011]⟩,
  ⟨14, 671129, 1, 12, rkm128kMask56 57 [64165265224266546, 1]⟩,
  ⟨15, 821763, 1, 14, rkm128kMask56 60 [25860650942020082, 13]⟩,
  ⟨16, 836553, 1, 13, rkm128kMask56 64 [29345415678248197, 170]⟩,
  ⟨16, 871657, 1, 15, rkm128kMask56 64 [9081966552456513, 198]⟩,
  ⟨17, 643812, 1, 12, rkm128kMask56 68 [11276592222340406, 2793]⟩,
  ⟨18, 963629, 1, 15, rkm128kMask56 70 [25051276532082762, 11686]⟩,
  ⟨19, 1097773, 1, 18, rkm128kMask56 72 [30540061541720205, 43345]⟩,
  ⟨20, 838808, 1, 15, rkm128kMask56 79 [28429083255143805, 4295242]⟩,
  ⟨21, 744811, 1, 15, rkm128kMask56 84 [2815167999641222, 143010503]⟩,
  ⟨21, 395754, 1, 12, rkm128kMask56 84 [5628713640213653, 234356075]⟩,
  ⟨22, 143918, 1, 8, rkm128kMask56 88 [58547560678298378, 2419065052]⟩,
  ⟨22, 187569, 1, 8, rkm128kMask56 88 [38843902259495626, 2415919173]⟩,
  ⟨22, 125707, 1, 8, rkm128kMask56 88 [29274616318949891, 2688548893]⟩,
  ⟨22, 136768, 1, 8, rkm128kMask56 89 [72055386424720716, 8053063653]⟩,
  ⟨22, 4320, 1, 4, rkm128kMask56 89 [66428053654355578, 5897191412]⟩,
  ⟨23, 112233, 1, 8, rkm128kMask56 61 [41660955719649664, 26]⟩,
  ⟨23, 75166, 1, 6, rkm128kMask56 90 [53761757341679855, 11408506910]⟩,
  ⟨23, 196572, 1, 10, rkm128kMask56 57 [59960836249490007, 1]⟩,
  ⟨76, 130476, 1, 12, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 304`. -/
def lm4k512l248krS0RowR304 : List ℕ :=
  [4597621, 3657460, 16792046, 3182052, 822877, 3343706, 4281509, 1234730, 7956368, 23996193,
   1977681, 55124126, 5665461, 52370573, 46821425, 1943597581, 1545717, 138411, 15959, 1848251,
   312697, 981875, 595598, 1526477, 4399825, 443367, 3870122, 24730079, 26069, 132044060, 5361,
   22254869, 81659314, 50513620, 19696363, 2198384, 67381423, 122213115, 49165194, 10196599,
   8246175, 333796366, 423804453, 5637336987, 21535212697, 73275755017, 231957923045,
   664047661928, 3954174, 640962, 6035, 2904, 40226, 38253, 1460, 20671, 2615, 49, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 304`. -/
def lm4k512l248krS0AncR304 : RampKick128kAnchor :=
  ⟨304, lm4k512l248krS0SegsR304, lm4k512l248krS0RowR304⟩
/-- Active `RampKick128k` segments for `m = 4, r = 368` (`45` segments). -/
def lm4k512l248krS0SegsR368 : List Rkm128kSeg := [
  ⟨1, 552016, 1, 6, []⟩,
  ⟨1, 565324, 1, 6, rkm128kMask56 3 [4]⟩,
  ⟨1, 602965, 1, 6, []⟩,
  ⟨1, 778359, 1, 6, rkm128kMask56 5 [27]⟩,
  ⟨1, 5110501, 1, 10, []⟩,
  ⟨1, 5392856, 1, 10, []⟩,
  ⟨1, 5515821, 1, 10, []⟩,
  ⟨2, 5556586, 1, 15, rkm128kMask56 8 [128]⟩,
  ⟨3, 1770060, 1, 10, rkm128kMask56 10 [768]⟩,
  ⟨3, 2269156, 1, 12, rkm128kMask56 10 [512]⟩,
  ⟨4, 2035399, 1, 12, rkm128kMask56 2 [3]⟩,
  ⟨4, 1536449, 1, 10, rkm128kMask56 14 [8192]⟩,
  ⟨5, 1513244, 1, 12, rkm128kMask56 15 [16394]⟩,
  ⟨5, 1649142, 1, 12, rkm128kMask56 21 [2080769]⟩,
  ⟨6, 1716239, 1, 14, rkm128kMask56 25 [33292340]⟩,
  ⟨7, 1263151, 1, 12, rkm128kMask56 29 [268566639]⟩,
  ⟨7, 1529299, 1, 14, rkm128kMask56 27 [69731164]⟩,
  ⟨8, 769311, 1, 10, rkm128kMask56 27 [73401425]⟩,
  ⟨9, 1208269, 1, 14, rkm128kMask56 33 [4567600035]⟩,
  ⟨10, 1457108, 1, 15, rkm128kMask56 38 [142824450497]⟩,
  ⟨11, 1296411, 1, 15, rkm128kMask56 43 [8657647490879]⟩,
  ⟨11, 801337, 1, 12, rkm128kMask56 45 [32946962632208]⟩,
  ⟨12, 1193198, 1, 15, rkm128kMask56 31 [1074005411]⟩,
  ⟨13, 984583, 1, 15, rkm128kMask56 52 [3958929055927176]⟩,
  ⟨13, 1007811, 1, 15, rkm128kMask56 51 [1948368971745745]⟩,
  ⟨14, 1074260, 1, 15, rkm128kMask56 56 [64976739184356886]⟩,
  ⟨16, 1351961, 1, 18, rkm128kMask56 64 [9024791656563221, 137]⟩,
  ⟨17, 941744, 1, 15, rkm128kMask56 69 [29290990811350074, 5179]⟩,
  ⟨18, 834002, 1, 15, rkm128kMask56 73 [20301382960542017, 87345]⟩,
  ⟨19, 712775, 1, 15, rkm128kMask56 73 [20477311365218657, 83269]⟩,
  ⟨20, 1034913, 1, 18, rkm128kMask56 78 [28288323232530509, 2804053]⟩,
  ⟨21, 835912, 1, 17, rkm128kMask56 85 [59602443373675288, 536182231]⟩,
  ⟨21, 56079, 1, 6, rkm128kMask56 78 [49539708116534129, 2793989]⟩,
  ⟨21, 65814, 1, 6, rkm128kMask56 76 [42855168119768004, 688752]⟩,
  ⟨22, 72331, 1, 6, rkm128kMask56 78 [50665784656005176, 2794728]⟩,
  ⟨22, 72761, 1, 6, rkm128kMask56 76 [64176304370621537, 696386]⟩,
  ⟨22, 31021, 1, 6, rkm128kMask56 76 [36169534577778301, 696333]⟩,
  ⟨22, 99089, 1, 8, rkm128kMask56 74 [31526229910787381, 164010]⟩,
  ⟨22, 99088, 1, 8, rkm128kMask56 72 [50666915311457940, 32808]⟩,
  ⟨22, 97773, 1, 8, rkm128kMask56 89 [52915603261587318, 8589934571]⟩,
  ⟨22, 13228, 1, 4, rkm128kMask56 89 [21391413719529049, 8589891335]⟩,
  ⟨23, 314475, 1, 12, rkm128kMask56 70 [36030996143026190, 10582]⟩,
  ⟨23, 258390, 1, 10, rkm128kMask56 70 [1688852091636806, 10795]⟩,
  ⟨27, 213426, 1, 10, rkm128kMask56 51 [1689949642424852]⟩,
  ⟨92, 33196, 1, 8, []⟩]
/-- Certified `10 ^ 12`-scaled hit-probability lower bounds for `m = 4, r = 368`. -/
def lm4k512l248krS0RowR368 : List ℕ :=
  [860056, 2632727, 1015795, 317351, 10374477, 1175623, 4090931, 1462182, 1539611, 15095920,
   462096, 2277, 19085325, 6121812, 130733597, 485694594, 40036059, 11506, 243440, 9723475,
   11300989, 30862772, 228225517, 63487550, 763878, 14767202, 214655235, 7717395, 220102298,
   145555426, 92078085, 73305595, 273958144, 1067768114, 52666897, 363384916, 99822020,
   41579303, 839284736, 230844168, 247655187, 95527536, 1719998, 6014528719, 34159036012,
   49940756331, 98199761075, 805594264313, 19675982, 57015518, 326704802, 368510406, 138193708,
   27934446, 3524705, 224296, 5906, 102, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Packaged `RampKick128kAnchor` for `m = 4, r = 368`. -/
def lm4k512l248krS0AncR368 : RampKick128kAnchor :=
  ⟨368, lm4k512l248krS0SegsR368, lm4k512l248krS0RowR368⟩
/-- Ordered list of all `101` `r < 512` anchors for `m = 4` (`r in {3..368}`). -/
def pfxAnchorsLt512 : List RampKick128kAnchor :=
  [lm4k512l248krS0AncR3, lm4k512l248krS0AncR4, lm4k512l248krS0AncR5, lm4k512l248krS0AncR6,
   lm4k512l248krS0AncR7, lm4k512l248krS0AncR8, lm4k512l248krS0AncR9, lm4k512l248krS0AncR10,
   lm4k512l248krS0AncR11, lm4k512l248krS0AncR12, lm4k512l248krS0AncR13, lm4k512l248krS0AncR14,
   lm4k512l248krS0AncR15, lm4k512l248krS0AncR16, lm4k512l248krS0AncR17, lm4k512l248krS0AncR18,
   lm4k512l248krS0AncR19, lm4k512l248krS0AncR20, lm4k512l248krS0AncR21, lm4k512l248krS0AncR23,
   lm4k512l248krS0AncR25, lm4k512l248krS0AncR27, lm4k512l248krS0AncR29, lm4k512l248krS0AncR31,
   lm4k512l248krS0AncR34, lm4k512l248krS0AncR37, lm4k512l248krS0AncR41, lm4k512l248krS0AncR44,
   lm4k512l248krS0AncR47, lm4k512l248krS0AncR49, lm4k512l248krS0AncR51, lm4k512l248krS0AncR52,
   lm4k512l248krS0AncR54, lm4k512l248krS0AncR55, lm4k512l248krS0AncR56, lm4k512l248krS0AncR57,
   lm4k512l248krS0AncR58, lm4k512l248krS0AncR59, lm4k512l248krS0AncR60, lm4k512l248krS0AncR61,
   lm4k512l248krS0AncR62, lm4k512l248krS0AncR63, lm4k512l248krS0AncR67, lm4k512l248krS0AncR68,
   lm4k512l248krS0AncR70, lm4k512l248krS0AncR71, lm4k512l248krS0AncR72, lm4k512l248krS0AncR73,
   lm4k512l248krS0AncR74, lm4k512l248krS0AncR75, lm4k512l248krS0AncR76, lm4k512l248krS0AncR77,
   lm4k512l248krS0AncR78, lm4k512l248krS0AncR79, lm4k512l248krS0AncR80, lm4k512l248krS0AncR81,
   lm4k512l248krS0AncR82, lm4k512l248krS0AncR83, lm4k512l248krS0AncR84, lm4k512l248krS0AncR85,
   lm4k512l248krS0AncR86, lm4k512l248krS0AncR87, lm4k512l248krS0AncR88, lm4k512l248krS0AncR89,
   lm4k512l248krS0AncR90, lm4k512l248krS0AncR91, lm4k512l248krS0AncR92, lm4k512l248krS0AncR93,
   lm4k512l248krS0AncR94, lm4k512l248krS0AncR95, lm4k512l248krS0AncR96, lm4k512l248krS0AncR102,
   lm4k512l248krS0AncR104, lm4k512l248krS0AncR105, lm4k512l248krS0AncR106,
   lm4k512l248krS0AncR107, lm4k512l248krS0AncR108, lm4k512l248krS0AncR110,
   lm4k512l248krS0AncR111, lm4k512l248krS0AncR113, lm4k512l248krS0AncR114,
   lm4k512l248krS0AncR115, lm4k512l248krS0AncR116, lm4k512l248krS0AncR118,
   lm4k512l248krS0AncR119, lm4k512l248krS0AncR120, lm4k512l248krS0AncR122,
   lm4k512l248krS0AncR123, lm4k512l248krS0AncR124, lm4k512l248krS0AncR125,
   lm4k512l248krS0AncR126, lm4k512l248krS0AncR127, lm4k512l248krS0AncR132,
   lm4k512l248krS0AncR144, lm4k512l248krS0AncR156, lm4k512l248krS0AncR168,
   lm4k512l248krS0AncR184, lm4k512l248krS0AncR220, lm4k512l248krS0AncR288,
   lm4k512l248krS0AncR304, lm4k512l248krS0AncR368]
/-- Alias for `pfxAnchorsLt512` matching `lm4k512l248krS0*` convention. -/
abbrev lm4k512l248krS0AncsLt512 : List RampKick128kAnchor := pfxAnchorsLt512
/-- Alias for `pfxAnchorsLt512` matching `lm4k512l248krS0PfxAnchors` convention. -/
abbrev lm4k512l248krS0PfxAnchors : List RampKick128kAnchor := pfxAnchorsLt512
/-- Slice `0` (`64` entries) of `lm4k512l248krS0VPotPfx511` (`r <= 511`). -/
def lm4k512l248krS0VPotPfx0 : List ℕ :=
  [0, 321349540849363, 396444684681935, 455320463496120, 536923809472487, 595565681312294,
   655585726640013, 704039565212670, 753094710928759, 797655217938168, 839701976649737,
   879282940010803, 917888223463976, 955521329386686, 989169266444947, 1022063979156002,
   1056457533223612, 1087517245232886, 1118379835097367, 1148319897804219, 1178358259439155,
   1206052123002518, 1274564075312149, 1266045139720735, 1331640340067285, 1321435898609392,
   1384457728589199, 1363315993406900, 1424045348336344, 1423587076188479, 1482257206977521,
   1459087312647050, 1515894422513492, 1571834197326989, 1534308842753886, 1588626829094665,
   1642185085902893, 1597236838651344, 1649366617847646, 1700823726549967, 1751633550256633,
   1677570536285952, 1727155846947789, 1776161192504356, 1800696587452521, 1848600548644356,
   1895980953556664, 1880528976397669, 1926911787376005, 1859708996855691, 1905154684748845,
   1944222596691698, 1968903267750568, 2013044021906289, 2005842649681522, 2017677386784039,
   2038096217611644, 2053246797989239, 2074273018107093, 2091551179032211, 2106452862770827,
   2127050116619350, 2143669599507978, 2159486954272835]
/-- Slice `1` (`64` entries) of `lm4k512l248krS0VPotPfx511` (`r <= 511`). -/
def lm4k512l248krS0VPotPfx1 : List ℕ :=
  [2199655646879006, 2239514151888621, 2279069545997293, 2274741765171174, 2290023830556839,
   2328709769170710, 2354527353647294, 2356446585575355, 2373778151165400, 2408220001999980,
   2425356101441021, 2453497048014818, 2479180758075681, 2492693597968612, 2507880131330623,
   2539505094790178, 2546211863232581, 2569269826350735, 2597558114200996, 2610540051884612,
   2624714980185846, 2655659072788135, 2659240196376564, 2684005592764873, 2702664625379764,
   2721284012160440, 2736155049827615, 2764052814141654, 2776062188862692, 2797436323930523,
   2811478940482317, 2838709649199438, 2832923068487911, 2865551170884796, 2898012376522763,
   2930309220569743, 2962444174654680, 2994419649074882, 2971417237579740, 3003080748692093,
   3018298954978977, 3029942674410844, 3043267243801122, 3070088479864902, 3051462618649852,
   3082242322346779, 3097357663385697, 3108199208609503, 3138563886074225, 3148540039672551,
   3161405761402521, 3177175627231258, 3180294890690749, 3210003666251754, 3224424631308606,
   3234893696541851, 3228268003385280, 3257481598007950, 3272520301038920, 3282456022123664,
   3294636612364143, 3318060216701471, 3330515724584419, 3343256734605168]
/-- Slice `2` (`64` entries) of `lm4k512l248krS0VPotPfx511` (`r <= 511`). -/
def lm4k512l248krS0VPotPfx2 : List ℕ :=
  [3371660289538389, 3399953538987204, 3428137758167461, 3456214197912086, 3400326911683068,
   3428191450740317, 3455951822931801, 3483609187821157, 3511164683617088, 3538619427719930,
   3565974517250365, 3593231029560983, 3620390022731373, 3647452536047387, 3674419590465186,
   3701292189060659, 3572227162637908, 3598913789458523, 3625508866689183, 3652013330105375,
   3678428099648714, 3704754079799508, 3730992159938128, 3757143214695591, 3783208104293742,
   3809187674875422, 3835082758824965, 3860894175079381, 3722905104174519, 3748551589562676,
   3774116786361600, 3799601462655639, 3825006374508972, 3850332266227326, 3875579870612412,
   3900749909209322, 3925843092547133, 3950860120372935, 3975801681879508, 4000668455926850,
   3927532386229490, 3952251581679441, 3976897966380805, 4001472179961780, 4025974852740064,
   4050406605911490, 4074768051733779, 4099059793705557, 4123282426740792, 4147436537338788,
   4171522703749875, 4195541496136929, 4219493476732847, 4243379199994102, 4267199212750497,
   4290954054351231, 4045973450666338, 4069599538789897, 4093162030329395, 4116661436102301,
   4140098260124224, 4163472999735042, 4186786145722039, 4210038182440137]
/-- Slice `3` (`64` entries) of `lm4k512l248krS0VPotPfx511` (`r <= 511`). -/
def lm4k512l248krS0VPotPfx3 : List ℕ :=
  [4233229587929305, 4256360834029229, 4279432386491316, 4302444705088114, 4325398243720212,
   4348293450520699, 4371130767957243, 4393910632931861, 4416633476878438, 4439299725858066,
   4461909800652248, 4484464116854043, 4506963084957189, 4529407110443273, 4551796593866994,
   4574131930939566, 4596413512610320, 4618641725146543, 4640816950211606, 4662939564941422,
   4685009942019283, 4707028449749108, 4728995452127155, 4750911308912226, 4772776375694410,
   4794591003962398, 4816355541169408, 4838070330797751, 4516917726875855, 4538534036225113,
   4560101605243243, 4581620762148655, 4603091831492502, 4624515134215793, 4645890987705362,
   4667219705848729, 4688501599087878, 4709736974471975, 4730926135709053, 4752069383216692,
   4773167014171712, 4794219322558908, 4815226599218844, 4836189131894732, 4857107205278416,
   4877981101055482, 4898811097949516, 4919597471765524, 4940340495432541, 4961040439045440,
   4981697569905965, 5002312152563003, 5022884448852114, 5043414717934329, 5063903216334244,
   5084350197977416, 5104755914227077, 5125120613920192, 5145444543402859, 5165727946565076,
   5185971064874891, 5206174137411937, 5226337400900379, 5246461089741273]
/-- Slice `4` (`64` entries) of `lm4k512l248krS0VPotPfx511` (`r <= 511`). -/
def lm4k512l248krS0VPotPfx4 : List ℕ :=
  [5266545436044359, 5286590669659297, 5306597018206357, 5326564707106574, 5346493959611382,
   5366384996831737, 5386238037766737, 5406053299331756, 5425830996386092, 5445571341760152,
   5465274546282170, 5484940818804479, 5504570366229340, 5524163393534337, 5543720103797351,
   5563240698221118, 5582725376157378, 5602174335130630, 5621587770861491, 5640965877289679,
   5660308846596615, 5679616869227660, 5698890133913992, 5718128827694131, 5737333135935113,
   5756503242353330, 5775639329035035, 5794741576456519, 5813810163503971, 5832845267493023,
   5851847064187986, 5870815727820786, 5543729094425621, 5562632008593231, 5581502303385083,
   5600340147087072, 5619145706543052, 5637919147172077, 5656660632985377, 5675370326603075,
   5694048389270650, 5712694980875149, 5731310259961158, 5749894383746527, 5768447508137862,
   5786969787745785, 5805461375899968, 5823922424663938, 5664469782828731, 5682870204011019,
   5701240534541640, 5719580921563308, 5737891511023425, 5756172447687631, 5774423875153157,
   5792645935861985, 5810838771113818, 5829002521078863, 5847137324810431, 5865243320257358,
   5883320644276246, 5901369432643534, 5919389820067393, 5937381940199460]
/-- Slice `5` (`64` entries) of `lm4k512l248krS0VPotPfx511` (`r <= 511`). -/
def lm4k512l248krS0VPotPfx5 : List ℕ :=
  [5955345925646398, 5973281907981304, 5991190017754949, 6009070384506864, 6026923136776274,
   6044748402112877, 6062546307087479, 6080316977302477, 6098060537402201, 6115777111083113,
   6133466821103871, 6151129789295248, 6168766136569927, 6186375982932153, 6203959447487262,
   6221516648451080, 6239047703159194, 6256552728076101, 6274031838804237, 6291485150092882,
   6308912775846949, 6326314829135658, 6343691422201092, 6361042666466648, 6378368672545368,
   6395669550248168, 6412945408591959, 6430196355807660, 6447422499348109, 6464623945895872,
   6481800801370950, 6498953170938391, 6516081159015799, 6533184869280753, 6550264404678126,
   6567319867427316, 6584351359029384, 6601358980274098, 6618342831246896, 6635303011335755,
   6652239619237977, 6669152752966891, 6686042509858470, 6702908986577865, 6719752279125862,
   6736572482845256, 6753369692427147, 6770144001917161, 6313891689562081, 6330620478453955,
   6347326645579034, 6364010282461731, 6380671480010961, 6397310328525920, 6413926917701796,
   6430521336635410, 6447093673830788, 6463644017204669, 6480172454091948, 6496679071251051,
   6513163954869249, 6529627190567907, 6546068863407673, 6562489057893606]
/-- Slice `6` (`64` entries) of `lm4k512l248krS0VPotPfx511` (`r <= 511`). -/
def lm4k512l248krS0VPotPfx6 : List ℕ :=
  [6578887857980244, 6595265347076609, 6611621608051160, 6627956723236683, 6644270774435126,
   6660563842922380, 6676836009453001, 6693087354264881, 6709317957083865, 6725527897128311,
   6741717253113604, 6757886103256613, 6774034525280103, 6790162596417091, 6806270393415157,
   6822357992540705, 6838425469583174, 6854472899859206, 6870500358216764, 6886507919039204,
   6902495656249305, 6918463643313250, 6934411953244565, 6950340658608013, 6966249831523447,
   6982139543669621, 6998009866287955, 7013860870186263, 7029692625742440, 7045505202908105,
   7061298671212208, 7077073099764598, 7092828557259550, 7108565111979256, 7124282831797275,
   7139981784181953, 7155662036199797, 7171323654518821, 7186966705411852, 7202591254759801,
   7218197368054901, 7233785110403909, 7249354546531277, 7264905740782284, 7280438757126142,
   7295953659159063, 7311450510107300, 7326929372830149, 7342390309822928, 7357833383219918,
   7373258654797276, 7388666185975921, 7404056037824385, 7419428271061637, 7434782946059878,
   7450120122847308, 7465439861110864, 7480742220198929, 7496027259124015, 7511295036565419,
   7526545610871848, 7541779040064024, 7556995381837258, 7572194693564000]
/-- Slice `7` (`64` entries) of `lm4k512l248krS0VPotPfx511` (`r <= 511`). -/
def lm4k512l248krS0VPotPfx7 : List ℕ :=
  [7587377032296361, 7602542454768614, 7617691017399666, 7632822776295506, 7647937787251631,
   7663036105755445, 7678117786988637, 7693182885829532, 7708231456855423, 7723263554344875,
   7738279232280012, 7753278544348776, 7768261543947169, 7783228284181469, 7798178817870426,
   7813113197547438, 7828031475462704, 7842933703585357, 7857819933605574, 7872690216936671,
   7887544604717174, 7902383147812868, 7917205896818833, 7932012902061454, 7946804213600415,
   7961579881230674, 7976339954484419, 7991084482633004, 8005813514688870, 8020527099407444,
   8035225285289022, 8049908120580635, 8064575653277896, 8079227931126830, 8093865001625690,
   8108486912026749, 8123093709338084, 8137685440325336, 8152262151513459, 8166823889188448,
   8181370699399057, 8195902627958496, 8210419720446115, 8224922022209071, 8239409578363981,
   8253882433798560, 8268340633173244, 8282784220922796, 8297213241257900, 8311627738166742,
   8326027755416572, 8340413336555254, 8354784524912805, 8369141363602916, 8383483895524461,
   8397812163362992, 8412126209592224, 8426426076475500, 8440711806067249, 8454983440214430,
   8469241020557959, 8483484588534128, 8497714185376012, 8511929852114859]
/-- `512`-entry `10 ^ 15`-scaled Krotov `vPot` prefix (`r = 0..511`). -/
def lm4k512l248krS0VPotPfx511 : List ℕ :=
  lm4k512l248krS0VPotPfx0 ++ (lm4k512l248krS0VPotPfx1 ++ (lm4k512l248krS0VPotPfx2 ++
    (lm4k512l248krS0VPotPfx3 ++ (lm4k512l248krS0VPotPfx4 ++ (lm4k512l248krS0VPotPfx5 ++
      (lm4k512l248krS0VPotPfx6 ++ lm4k512l248krS0VPotPfx7))))))
/-- Full `513`-entry `10 ^ 15`-scaled Krotov `vPot` vector (`r = 0..512`). -/
def lm4k512l248krS0VPot : List ℕ := lm4k512l248krS0VPotPfx511 ++ [5787550928846840]
/-- Segments `0..46` (`47` segments) of `(4, 512)` `r = 512` (`lTableMax = 248`). -/
def lm4k512l248krS0Segs : List Rkm128kSeg := [
  ⟨1, 2807859, 1, 8, []⟩,
  ⟨1, 2873848, 1, 8, []⟩,
  ⟨2, 2071568, 1, 9, []⟩,
  ⟨2, 1933908, 1, 9, []⟩,
  ⟨3, 1577670, 1, 9, []⟩,
  ⟨4, 1353610, 1, 10, []⟩,
  ⟨4, 1090581, 1, 9, []⟩,
  ⟨5, 1214472, 1, 10, []⟩,
  ⟨5, 1215318, 1, 10, []⟩,
  ⟨6, 1112527, 1, 10, []⟩,
  ⟨7, 1030917, 1, 10, []⟩,
  ⟨7, 1031705, 1, 10, []⟩,
  ⟨8, 960373, 1, 10, []⟩,
  ⟨9, 927189, 1, 10, []⟩,
  ⟨10, 858776, 1, 10, []⟩,
  ⟨11, 818347, 1, 11, []⟩,
  ⟨13, 1762275, 1, 17, []⟩,
  ⟨15, 1656152, 1, 18, []⟩,
  ⟨17, 1553980, 1, 18, rkm128kMask56 3 [6]⟩,
  ⟨20, 1448374, 1, 19, rkm128kMask56 10 [773]⟩,
  ⟨22, 1379534, 1, 19, rkm128kMask56 11 [1963]⟩,
  ⟨25, 1306757, 1, 20, rkm128kMask56 25 [25357507]⟩,
  ⟨28, 1273641, 1, 21, rkm128kMask56 32 [3504830635]⟩,
  ⟨31, 1181574, 1, 23, rkm128kMask56 40 [1003790648535]⟩,
  ⟨33, 856920, 1, 20, rkm128kMask56 124 [31599759310486, 0, 2048]⟩,
  ⟨36, 787548, 1, 20, rkm128kMask56 137 [1079687175212155, 0, 16777216]⟩,
  ⟨38, 779326, 1, 21, rkm128kMask56 128 [28186155431098855, 0, 32768]⟩,
  ⟨41, 749386, 1, 22, rkm128kMask56 60 [56993002134044623, 13]⟩,
  ⟨45, 692196, 1, 23, rkm128kMask56 66 [42275853879499145, 966]⟩,
  ⟨48, 678717, 1, 23, rkm128kMask56 138 [71913954653806114, 30460, 33587200]⟩,
  ⟨52, 634860, 1, 24, rkm128kMask56 77 [27755742233605670, 1876707]⟩,
  ⟨53, 648700, 1, 24,
    rkm128kMask56 203 [45762583419341582, 52408674, 137438953472, 17179869184]⟩,
  ⟨56, 617981, 1, 25, rkm128kMask56 88 [70264766755491291, 3242587751]⟩,
  ⟨59, 612139, 1, 25, rkm128kMask56 235 [70399098282035544, 241300283897, 4194304, 0, 1032]⟩,
  ⟨61, 600089, 1, 25, rkm128kMask56 100 [48021404949379930, 15396174152952]⟩,
  ⟨65, 580812, 1, 26,
    rkm128kMask56 238 [58386776832006564, 992002473115082, 17179869184, 549755813888, 8192]⟩,
  ⟨67, 569646, 1, 26,
    rkm128kMask56 164 [31382959210149874, 65316414280674730, 2251799813685248]⟩,
  ⟨70, 551571, 1, 26,
    rkm128kMask56 280 [14611704363427635, 24092012076682372, 56, 4096, 36028797019492352]⟩,
  ⟨73, 543118, 1, 27,
    rkm128kMask56 293 [49486254752164785, 63251837283027529, 3232, 35184372088832, 0, 6144]⟩,
  ⟨76, 533029, 1, 27,
    rkm128kMask56 299 [3935499580101678, 14252984992759487, 212147, 17592186044416, 0, 393216]⟩,
  ⟨78, 404503, 1, 23,
    rkm128kMask56 313 [9589178556236233, 70083771487222009, 7738433, 0, 36028797023158272,
     6814564864]⟩,
  ⟨80, 376742, 1, 22,
    rkm128kMask56 319 [36390342973912612, 49105846792917586, 239651963, 68719476736,
     68720525312, 347074068480]⟩,
  ⟨84, 363248, 1, 23,
    rkm128kMask56 336 [36749536468326548, 24909849342289220, 3288083817, 4503599627370496, 0,
     70630222742953984]⟩,
  ⟨86, 361716, 1, 23,
    rkm128kMask56 345 [5096041392662769, 54441929167955027, 103773881647, 36028797018963968,
     9663676416, 42920972584484864, 273]⟩,
  ⟨88, 356734, 1, 23,
    rkm128kMask56 351 [69257979899580393, 52988051736198604, 3511414948626, 9007199254740992, 0,
     2238045474783232, 18340]⟩,
  ⟨91, 351093, 1, 23,
    rkm128kMask56 365 [14451427164924394, 13148026250564021, 53987580999527, 0, 0,
     26641166741012481, 323264294]⟩,
  ⟨94, 354393, 1, 24,
    rkm128kMask56 377 [33226306435026563, 32434211249567638, 1864832164706964, 0, 536870912,
     15763011014754304, 1612530761509]⟩]
/-- Entry `lPrev` (`1`) entering `lm4k512l248krS0Segs` at segment `0`. -/
def lm4k512l248krS0LIn : ℕ := 1
/-- Entry `dCur` (`0`) entering `lm4k512l248krS0Segs` at segment `0`. -/
def lm4k512l248krS0DCurIn : ℕ := 0
/-- Entry `accPad` (`1`) entering `lm4k512l248krS0Segs` at segment `0`. -/
def lm4k512l248krS0PadIn : ℕ := 1
/-- Entry initial vector `[Int.ofNat wdScale]` entering `lm4k512l248krS0Segs`. -/
def lm4k512l248krS0VecIn : List ℤ := [Int.ofNat wdScale]
/-- Exit `lPrev` (`94`) leaving `lm4k512l248krS0Segs` after segment `46`. -/
def lm4k512l248krS0LOut : ℕ := 94
/-- Exit `dCur` (`376`) leaving `lm4k512l248krS0Segs` after segment `46`. -/
def lm4k512l248krS0DCurOut : ℕ := 376
/-- Exit `accPad` leaving `lm4k512l248krS0Segs` after segment `46`. -/
def lm4k512l248krS0PadOut : ℕ := 1597588745
/-- Slice `0` (`64` entries) of `lm4k512l248krS0Vec`. -/
def lm4k512l248krS0Vec0 : List ℤ :=
  [Int.ofNat 952785362, Int.negSucc 542923009, Int.ofNat 405548032, Int.negSucc 1762858524,
   Int.ofNat 775721286, Int.ofNat 569661955, Int.ofNat 185084899, Int.ofNat 5346441652,
   Int.ofNat 2293334418, Int.ofNat 2106928857, Int.negSucc 1373314513, Int.negSucc 2252094153,
   Int.ofNat 1050462918, Int.ofNat 1577934383, Int.ofNat 1925889356, Int.ofNat 4222184758,
   Int.negSucc 6230526295, Int.negSucc 15295151410, Int.negSucc 28714223354,
   Int.negSucc 3394792696, Int.negSucc 973613815, Int.ofNat 2678874398, Int.ofNat 36955805983,
   Int.negSucc 3755382814, Int.ofNat 18018934929, Int.ofNat 17841430560, Int.ofNat 30077949278,
   Int.ofNat 82121521144, Int.ofNat 101162650883, Int.ofNat 10121618612, Int.ofNat 27388298565,
   Int.ofNat 43219969532, Int.ofNat 25454883085, Int.ofNat 27611758700, Int.ofNat 28665018842,
   Int.ofNat 2337991926, Int.negSucc 43396267859, Int.ofNat 74414606404, Int.ofNat 77590222184,
   Int.ofNat 275851918100, Int.negSucc 69225759028, Int.negSucc 55827674314,
   Int.ofNat 176190525886, Int.negSucc 43228351759, Int.negSucc 164395338740,
   Int.negSucc 241927571218, Int.negSucc 323365168006, Int.ofNat 121259931828,
   Int.ofNat 114911217582, Int.negSucc 862114991285, Int.negSucc 164770554543,
   Int.ofNat 370374240828, Int.negSucc 561674681518, Int.ofNat 193031960791,
   Int.ofNat 96744519343, Int.negSucc 182311676362, Int.negSucc 1104340859653,
   Int.negSucc 472079315053, Int.negSucc 758406219421, Int.ofNat 1636537239799,
   Int.ofNat 1266310259509, Int.ofNat 188413243033, Int.ofNat 1372904371391,
   Int.ofNat 631670696759]
/-- Slice `1` (`64` entries) of `lm4k512l248krS0Vec`. -/
def lm4k512l248krS0Vec1 : List ℤ :=
  [Int.ofNat 407806229249, Int.ofNat 136905691397, Int.ofNat 1249848603768,
   Int.negSucc 385827874116, Int.negSucc 857990186896, Int.negSucc 1824089048784,
   Int.negSucc 1303645303698, Int.ofNat 83187713973, Int.negSucc 864279446316,
   Int.negSucc 349377393713, Int.negSucc 385300970753, Int.ofNat 901459751182,
   Int.negSucc 42181427538, Int.negSucc 828332758959, Int.ofNat 681520194068,
   Int.ofNat 587982748730, Int.ofNat 49551459488, Int.ofNat 1189882485274,
   Int.ofNat 2237237357012, Int.ofNat 2004882398190, Int.ofNat 1841121743353,
   Int.ofNat 672095172667, Int.negSucc 958754072110, Int.negSucc 3186166657464,
   Int.negSucc 2381859816616, Int.negSucc 649935383541, Int.negSucc 1225301668758,
   Int.negSucc 1377852124470, Int.ofNat 3867752078764, Int.negSucc 824855606895,
   Int.negSucc 1326424118444, Int.ofNat 3542616218997, Int.ofNat 2369610085636,
   Int.negSucc 85208113241, Int.negSucc 958591059267, Int.negSucc 5317987856233,
   Int.negSucc 988295095145, Int.ofNat 1959918439088, Int.negSucc 753904064993,
   Int.ofNat 2450306998558, Int.ofNat 380975147964, Int.negSucc 3003190720285,
   Int.ofNat 2058248202629, Int.negSucc 3655414376640, Int.negSucc 402296506562,
   Int.ofNat 1343698732531, Int.ofNat 1317798891478, Int.ofNat 2863429033957,
   Int.negSucc 750162371766, Int.ofNat 1060696141693, Int.ofNat 4260376762485,
   Int.ofNat 1974450388586, Int.ofNat 1654048417744, Int.ofNat 4711780617014,
   Int.ofNat 1671123324461, Int.negSucc 1956149065481, Int.ofNat 2442721584860,
   Int.negSucc 2167688138923, Int.negSucc 268184262670, Int.ofNat 1019815091961,
   Int.negSucc 2733177931666, Int.ofNat 751019581368, Int.ofNat 3117205336567,
   Int.negSucc 1820635564261]
/-- Slice `2` (`64` entries) of `lm4k512l248krS0Vec`. -/
def lm4k512l248krS0Vec2 : List ℤ :=
  [Int.ofNat 2525457874560, Int.ofNat 1970954446636, Int.ofNat 7776393091415,
   Int.ofNat 2680546589514, Int.negSucc 3620471914218, Int.ofNat 1652859504957,
   Int.negSucc 659577496598, Int.ofNat 156428687595, Int.ofNat 382083407592,
   Int.negSucc 5907190334178, Int.ofNat 192816761995, Int.negSucc 850363626602,
   Int.negSucc 3455414594625, Int.negSucc 2205112454159, Int.ofNat 2397014258433,
   Int.ofNat 888347228358, Int.negSucc 2021503916885, Int.negSucc 2054358389931,
   Int.negSucc 4859551017536, Int.ofNat 4624956662429, Int.ofNat 1133855994179,
   Int.negSucc 1792250791803, Int.ofNat 4225491269368, Int.ofNat 3968857367523,
   Int.ofNat 252426249633, Int.ofNat 2226615289894, Int.negSucc 2664671103442,
   Int.ofNat 2452333852704, Int.ofNat 1749787579121, Int.ofNat 1788881702717,
   Int.ofNat 2015136388668, Int.negSucc 6442050915027, Int.ofNat 3743885740573,
   Int.ofNat 2850721151965, Int.ofNat 4770152577001, Int.ofNat 4414719990241,
   Int.ofNat 26902614366975, Int.ofNat 61608900506307, Int.ofNat 105440796051587,
   Int.ofNat 154204626044293, Int.ofNat 203287467524248, Int.ofNat 248251140179587,
   Int.ofNat 285341232231255, Int.ofNat 311860247080109, Int.ofNat 326363694427919,
   Int.ofNat 328670227131992, Int.ofNat 319709791448905, Int.ofNat 301257230855628,
   Int.ofNat 275609022982011, Int.ofNat 245258433705609, Int.ofNat 212612910720851,
   Int.ofNat 179781557655894, Int.ofNat 148443999292051, Int.ofNat 119797676617949,
   Int.ofNat 94570291203885, Int.ofNat 73078472820073, Int.ofNat 55312577975678,
   Int.ofNat 41029856393749, Int.ofNat 29842604403944, Int.ofNat 21292910715931,
   Int.ofNat 14910108246829, Int.ofNat 10250502025677, Int.ofNat 6921212164686,
   Int.ofNat 4591183343976]
/-- Slice `3` (`64` entries) of `lm4k512l248krS0Vec`. -/
def lm4k512l248krS0Vec3 : List ℤ :=
  [Int.ofNat 2992806657340, Int.ofNat 1917427081568, Int.ofNat 1207495331575,
   Int.ofNat 747454040638, Int.ofNat 454769743393, Int.ofNat 271931279285,
   Int.ofNat 159781616373, Int.ofNat 92242867854, Int.ofNat 52315020248, Int.ofNat 29146016381,
   Int.ofNat 15951247199, Int.ofNat 8576595811, Int.ofNat 4531323473, Int.ofNat 2353170704,
   Int.ofNat 1201626137, Int.ofNat 603639168, Int.ofNat 298475659, Int.ofNat 145348762,
   Int.ofNat 69748728, Int.ofNat 33001015, Int.ofNat 15403091, Int.ofNat 7095329,
   Int.ofNat 3226858, Int.ofNat 1449268, Int.ofNat 642916, Int.ofNat 281729, Int.ofNat 121942,
   Int.ofNat 52121, Int.ofNat 21990, Int.ofNat 9149, Int.ofNat 3743, Int.ofNat 1501,
   Int.ofNat 583, Int.ofNat 216, Int.ofNat 74, Int.ofNat 22, Int.ofNat 4, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
/-- Slice `4` (`64` entries) of `lm4k512l248krS0Vec`. -/
def lm4k512l248krS0Vec4 : List ℤ :=
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
/-- Slice `5` (`57` entries) of `lm4k512l248krS0Vec`. -/
def lm4k512l248krS0Vec5 : List ℤ :=
  [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0]
/-- Checkpoint `377`-entry fixed-point vector exiting `lm4k512l248krS0Segs` (`after seg
  46`). -/
def lm4k512l248krS0Vec : List ℤ :=
  lm4k512l248krS0Vec0 ++ (lm4k512l248krS0Vec1 ++ (lm4k512l248krS0Vec2 ++
    (lm4k512l248krS0Vec3 ++ (lm4k512l248krS0Vec4 ++ lm4k512l248krS0Vec5))))

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
  | true => cases b with
    | false => cases h
    | true => rfl
private def s0NatEq (x y : ℕ) : Bool := Bool.and (Nat.ble x y) (Nat.ble y x)
private theorem s0Ble_le {a b : ℕ} (h : Nat.ble a b = true) : a ≤ b := by
  induction a generalizing b with
  | zero => exact Nat.zero_le _
  | succ a ih => cases b with
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
  | nil => cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x _ ih => cases ys with
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
  | ofNat _ => cases b with
    | ofNat _ => exact congrArg Int.ofNat (s0NatEq_eq h)
    | negSucc _ => cases h
  | negSucc _ => cases b with
    | ofNat _ => cases h
    | negSucc _ => exact congrArg Int.negSucc (s0NatEq_eq h)
private def s0IntListEq (xs ys : List ℤ) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xr, y :: yr => cond (s0IntEq x y) (s0IntListEq xr yr) false
  | _, _ => false
private theorem s0IntListEq_eq {xs ys : List ℤ} (h : s0IntListEq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x _ ih => cases ys with
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
private theorem s0_tl1 {b : Bool} {s : List Bool} (h : s0AtF (b :: s) = true) : s0AtF s = true := by
  cases b with
  | false => cases h
  | true => exact h
private theorem s0_tl2 {b1 b2 : Bool} {bs : List Bool}
    (h : s0AtF (b1 :: b2 :: bs) = true) : s0AtF bs = true := s0_tl1 (s0_tl1 h)
private theorem s0_tl4 {b1 b2 b3 b4 : Bool} {bs : List Bool}
    (h : s0AtF (b1 :: b2 :: b3 :: b4 :: bs) = true) : s0AtF bs = true := s0_tl2 (s0_tl2 h)
private theorem s0_tl8 {b1 b2 b3 b4 b5 b6 b7 b8 : Bool} {bs : List Bool}
    (h : s0AtF (b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: bs) = true) :
    s0AtF bs = true := s0_tl4 (s0_tl4 h)
private def s0ChkRow (r : ℕ) (segs : List Rkm128kSeg) (row : List ℕ) : Bool :=
  s0NatListEq (rkm128kEvalRowLo12 4 248 r segs) row
private theorem s0ChkRow_eq {r : ℕ} {segs : List Rkm128kSeg} {row : List ℕ}
    (h : s0ChkRow r segs row = true) : rkm128kEvalRowLo12 4 248 r segs = row := s0NatListEq_eq h
private def s0StateEq (st1 st2 : ℕ × ℕ × ℕ × List ℤ) : Bool :=
  match st1, st2 with
  | (l1, d1, p1, v1), (l2, d2, p2, v2) =>
    Bool.and (s0NatEq l1 l2)
      (Bool.and (s0NatEq d1 d2) (Bool.and (s0NatEq p1 p2) (s0IntListEq v1 v2)))
private theorem s0StateEq_eq {st1 st2 : ℕ × ℕ × ℕ × List ℤ} (h : s0StateEq st1 st2 = true) :
    st1 = st2 := by
  rcases st1 with ⟨_, _, _, _⟩; rcases st2 with ⟨_, _, _, _⟩; dsimp only [s0StateEq] at h
  have hr1 := s0AndRight h; have hr2 := s0AndRight hr1
  rw [s0NatEq_eq (s0AndLeft h), s0NatEq_eq (s0AndLeft hr1),
      s0NatEq_eq (s0AndLeft hr2), s0IntListEq_eq (s0AndRight hr2)]
private def s0RunAtEq (c : List Rkm128kSeg)
    (lI dI pI : ℕ) (vI : List ℤ) (lO dO pO : ℕ) (vO : List ℤ) : Bool :=
  s0StateEq (rkm128kRunSegs 4 248 512 c lI dI pI vI) (lO, dO, pO, vO)
private theorem s0RunStep {c rest : List Rkm128kSeg}
    {lI dI pI l1 d1 p1 : ℕ} {vI v1 : List ℤ} {stOut : ℕ × ℕ × ℕ × List ℤ}
    (h1 : s0RunAtEq c lI dI pI vI l1 d1 p1 v1 = true)
    (h2 : rkm128kRunSegs 4 248 512 rest l1 d1 p1 v1 = stOut) :
    rkm128kRunSegs 4 248 512 (c ++ rest) lI dI pI vI = stOut := by
  unfold s0RunAtEq at h1; rw [rkm128kRunSegs_append]; dsimp only
  rw [s0StateEq_eq h1]; dsimp only; exact h2
private theorem s0RunLast {c : List Rkm128kSeg}
    {lI dI pI lO dO pO : ℕ} {vI vO : List ℤ} (h : s0RunAtEq c lI dI pI vI lO dO pO vO = true) :
    rkm128kRunSegs 4 248 512 c lI dI pI vI = (lO, dO, pO, vO) := s0StateEq_eq h
private def s0AncB0 : List RampKick128kAnchor :=
  [lm4k512l248krS0AncR3, lm4k512l248krS0AncR4, lm4k512l248krS0AncR5, lm4k512l248krS0AncR6,
   lm4k512l248krS0AncR7, lm4k512l248krS0AncR8, lm4k512l248krS0AncR9, lm4k512l248krS0AncR10,
   lm4k512l248krS0AncR11, lm4k512l248krS0AncR12, lm4k512l248krS0AncR13, lm4k512l248krS0AncR14,
   lm4k512l248krS0AncR15, lm4k512l248krS0AncR16, lm4k512l248krS0AncR17, lm4k512l248krS0AncR18,
   lm4k512l248krS0AncR19]
private theorem s0RowChk0 : s0AtF [
    s0ChkRow 3 lm4k512l248krS0SegsR3 lm4k512l248krS0RowR3,
    s0ChkRow 4 lm4k512l248krS0SegsR4 lm4k512l248krS0RowR4,
    s0ChkRow 5 lm4k512l248krS0SegsR5 lm4k512l248krS0RowR5,
    s0ChkRow 6 lm4k512l248krS0SegsR6 lm4k512l248krS0RowR6,
    s0ChkRow 7 lm4k512l248krS0SegsR7 lm4k512l248krS0RowR7,
    s0ChkRow 8 lm4k512l248krS0SegsR8 lm4k512l248krS0RowR8,
    s0ChkRow 9 lm4k512l248krS0SegsR9 lm4k512l248krS0RowR9,
    s0ChkRow 10 lm4k512l248krS0SegsR10 lm4k512l248krS0RowR10,
    s0ChkRow 11 lm4k512l248krS0SegsR11 lm4k512l248krS0RowR11,
    s0ChkRow 12 lm4k512l248krS0SegsR12 lm4k512l248krS0RowR12,
    s0ChkRow 13 lm4k512l248krS0SegsR13 lm4k512l248krS0RowR13,
    s0ChkRow 14 lm4k512l248krS0SegsR14 lm4k512l248krS0RowR14,
    s0ChkRow 15 lm4k512l248krS0SegsR15 lm4k512l248krS0RowR15,
    s0ChkRow 16 lm4k512l248krS0SegsR16 lm4k512l248krS0RowR16,
    s0ChkRow 17 lm4k512l248krS0SegsR17 lm4k512l248krS0RowR17,
    s0ChkRow 18 lm4k512l248krS0SegsR18 lm4k512l248krS0RowR18,
    s0ChkRow 19 lm4k512l248krS0SegsR19 lm4k512l248krS0RowR19
  ] = true := by decide +kernel
private theorem s0AncB0_ok (rest : List RampKick128kAnchor)
    (hrest : RampKick128kAnchorsSound 4 248 rest) :
    RampKick128kAnchorsSound 4 248 (s0AncB0 ++ rest) := by
  exact
    ⟨s0ChkRow_eq (s0_hd s0RowChk0),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 s0RowChk0)),
    ⟨s0ChkRow_eq (s0_hd (s0_tl2 s0RowChk0)),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl2 s0RowChk0))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl4 s0RowChk0)),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl4 s0RowChk0))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl2 (s0_tl4 s0RowChk0))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl2 (s0_tl4 s0RowChk0)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl8 s0RowChk0)),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl8 s0RowChk0))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl2 (s0_tl8 s0RowChk0))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl2 (s0_tl8 s0RowChk0)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl4 (s0_tl8 s0RowChk0))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl4 (s0_tl8 s0RowChk0)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl2 (s0_tl4 (s0_tl8 s0RowChk0)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl2 (s0_tl4 (s0_tl8 s0RowChk0))))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl8 (s0_tl8 s0RowChk0))),
    hrest⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
private def s0AncB1 : List RampKick128kAnchor :=
  [lm4k512l248krS0AncR20, lm4k512l248krS0AncR21, lm4k512l248krS0AncR23, lm4k512l248krS0AncR25,
   lm4k512l248krS0AncR27, lm4k512l248krS0AncR29]
private theorem s0RowChk1 : s0AtF [
    s0ChkRow 20 lm4k512l248krS0SegsR20 lm4k512l248krS0RowR20,
    s0ChkRow 21 lm4k512l248krS0SegsR21 lm4k512l248krS0RowR21,
    s0ChkRow 23 lm4k512l248krS0SegsR23 lm4k512l248krS0RowR23,
    s0ChkRow 25 lm4k512l248krS0SegsR25 lm4k512l248krS0RowR25,
    s0ChkRow 27 lm4k512l248krS0SegsR27 lm4k512l248krS0RowR27,
    s0ChkRow 29 lm4k512l248krS0SegsR29 lm4k512l248krS0RowR29
  ] = true := by decide +kernel
private theorem s0AncB1_ok (rest : List RampKick128kAnchor)
    (hrest : RampKick128kAnchorsSound 4 248 rest) :
    RampKick128kAnchorsSound 4 248 (s0AncB1 ++ rest) := by
  exact
    ⟨s0ChkRow_eq (s0_hd s0RowChk1),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 s0RowChk1)),
    ⟨s0ChkRow_eq (s0_hd (s0_tl2 s0RowChk1)),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl2 s0RowChk1))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl4 s0RowChk1)),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl4 s0RowChk1))),
    hrest⟩⟩⟩⟩⟩⟩
private def s0AncB2 : List RampKick128kAnchor :=
  [lm4k512l248krS0AncR31, lm4k512l248krS0AncR34, lm4k512l248krS0AncR37]
private theorem s0RowChk2 : s0AtF [
    s0ChkRow 31 lm4k512l248krS0SegsR31 lm4k512l248krS0RowR31,
    s0ChkRow 34 lm4k512l248krS0SegsR34 lm4k512l248krS0RowR34,
    s0ChkRow 37 lm4k512l248krS0SegsR37 lm4k512l248krS0RowR37
  ] = true := by decide +kernel
private theorem s0AncB2_ok (rest : List RampKick128kAnchor)
    (hrest : RampKick128kAnchorsSound 4 248 rest) :
    RampKick128kAnchorsSound 4 248 (s0AncB2 ++ rest) := by
  exact
    ⟨s0ChkRow_eq (s0_hd s0RowChk2),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 s0RowChk2)),
    ⟨s0ChkRow_eq (s0_hd (s0_tl2 s0RowChk2)),
    hrest⟩⟩⟩
private def s0AncB3 : List RampKick128kAnchor :=
  [lm4k512l248krS0AncR41, lm4k512l248krS0AncR44, lm4k512l248krS0AncR47, lm4k512l248krS0AncR49,
   lm4k512l248krS0AncR51, lm4k512l248krS0AncR52, lm4k512l248krS0AncR54, lm4k512l248krS0AncR55,
   lm4k512l248krS0AncR56, lm4k512l248krS0AncR57, lm4k512l248krS0AncR58, lm4k512l248krS0AncR59,
   lm4k512l248krS0AncR60, lm4k512l248krS0AncR61, lm4k512l248krS0AncR62, lm4k512l248krS0AncR63,
   lm4k512l248krS0AncR67, lm4k512l248krS0AncR68, lm4k512l248krS0AncR70, lm4k512l248krS0AncR71,
   lm4k512l248krS0AncR72, lm4k512l248krS0AncR73, lm4k512l248krS0AncR74, lm4k512l248krS0AncR75]
private theorem s0RowChk3 : s0AtF [
    s0ChkRow 41 lm4k512l248krS0SegsR41 lm4k512l248krS0RowR41,
    s0ChkRow 44 lm4k512l248krS0SegsR44 lm4k512l248krS0RowR44,
    s0ChkRow 47 lm4k512l248krS0SegsR47 lm4k512l248krS0RowR47,
    s0ChkRow 49 lm4k512l248krS0SegsR49 lm4k512l248krS0RowR49,
    s0ChkRow 51 lm4k512l248krS0SegsR51 lm4k512l248krS0RowR51,
    s0ChkRow 52 lm4k512l248krS0SegsR52 lm4k512l248krS0RowR52,
    s0ChkRow 54 lm4k512l248krS0SegsR54 lm4k512l248krS0RowR54,
    s0ChkRow 55 lm4k512l248krS0SegsR55 lm4k512l248krS0RowR55,
    s0ChkRow 56 lm4k512l248krS0SegsR56 lm4k512l248krS0RowR56,
    s0ChkRow 57 lm4k512l248krS0SegsR57 lm4k512l248krS0RowR57,
    s0ChkRow 58 lm4k512l248krS0SegsR58 lm4k512l248krS0RowR58,
    s0ChkRow 59 lm4k512l248krS0SegsR59 lm4k512l248krS0RowR59,
    s0ChkRow 60 lm4k512l248krS0SegsR60 lm4k512l248krS0RowR60,
    s0ChkRow 61 lm4k512l248krS0SegsR61 lm4k512l248krS0RowR61,
    s0ChkRow 62 lm4k512l248krS0SegsR62 lm4k512l248krS0RowR62,
    s0ChkRow 63 lm4k512l248krS0SegsR63 lm4k512l248krS0RowR63,
    s0ChkRow 67 lm4k512l248krS0SegsR67 lm4k512l248krS0RowR67,
    s0ChkRow 68 lm4k512l248krS0SegsR68 lm4k512l248krS0RowR68,
    s0ChkRow 70 lm4k512l248krS0SegsR70 lm4k512l248krS0RowR70,
    s0ChkRow 71 lm4k512l248krS0SegsR71 lm4k512l248krS0RowR71,
    s0ChkRow 72 lm4k512l248krS0SegsR72 lm4k512l248krS0RowR72,
    s0ChkRow 73 lm4k512l248krS0SegsR73 lm4k512l248krS0RowR73,
    s0ChkRow 74 lm4k512l248krS0SegsR74 lm4k512l248krS0RowR74,
    s0ChkRow 75 lm4k512l248krS0SegsR75 lm4k512l248krS0RowR75
  ] = true := by decide +kernel
private theorem s0AncB3_ok (rest : List RampKick128kAnchor)
    (hrest : RampKick128kAnchorsSound 4 248 rest) :
    RampKick128kAnchorsSound 4 248 (s0AncB3 ++ rest) := by
  exact
    ⟨s0ChkRow_eq (s0_hd s0RowChk3),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 s0RowChk3)),
    ⟨s0ChkRow_eq (s0_hd (s0_tl2 s0RowChk3)),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl2 s0RowChk3))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl4 s0RowChk3)),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl4 s0RowChk3))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl2 (s0_tl4 s0RowChk3))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl2 (s0_tl4 s0RowChk3)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl8 s0RowChk3)),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl8 s0RowChk3))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl2 (s0_tl8 s0RowChk3))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl2 (s0_tl8 s0RowChk3)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl4 (s0_tl8 s0RowChk3))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl4 (s0_tl8 s0RowChk3)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl2 (s0_tl4 (s0_tl8 s0RowChk3)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl2 (s0_tl4 (s0_tl8 s0RowChk3))))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl8 (s0_tl8 s0RowChk3))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl8 (s0_tl8 s0RowChk3)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl2 (s0_tl8 (s0_tl8 s0RowChk3)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl2 (s0_tl8 (s0_tl8 s0RowChk3))))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl4 (s0_tl8 (s0_tl8 s0RowChk3)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl4 (s0_tl8 (s0_tl8 s0RowChk3))))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl2 (s0_tl4 (s0_tl8 (s0_tl8 s0RowChk3))))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl2 (s0_tl4 (s0_tl8 (s0_tl8 s0RowChk3)))))),
    hrest⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
private def s0AncB4 : List RampKick128kAnchor :=
  [lm4k512l248krS0AncR76, lm4k512l248krS0AncR77, lm4k512l248krS0AncR78, lm4k512l248krS0AncR79,
   lm4k512l248krS0AncR80, lm4k512l248krS0AncR81, lm4k512l248krS0AncR82, lm4k512l248krS0AncR83,
   lm4k512l248krS0AncR84, lm4k512l248krS0AncR85, lm4k512l248krS0AncR86, lm4k512l248krS0AncR87,
   lm4k512l248krS0AncR88, lm4k512l248krS0AncR89, lm4k512l248krS0AncR90, lm4k512l248krS0AncR91,
   lm4k512l248krS0AncR92, lm4k512l248krS0AncR93, lm4k512l248krS0AncR94, lm4k512l248krS0AncR95,
   lm4k512l248krS0AncR96, lm4k512l248krS0AncR102, lm4k512l248krS0AncR104,
   lm4k512l248krS0AncR105]
private theorem s0RowChk4 : s0AtF [
    s0ChkRow 76 lm4k512l248krS0SegsR76 lm4k512l248krS0RowR76,
    s0ChkRow 77 lm4k512l248krS0SegsR77 lm4k512l248krS0RowR77,
    s0ChkRow 78 lm4k512l248krS0SegsR78 lm4k512l248krS0RowR78,
    s0ChkRow 79 lm4k512l248krS0SegsR79 lm4k512l248krS0RowR79,
    s0ChkRow 80 lm4k512l248krS0SegsR80 lm4k512l248krS0RowR80,
    s0ChkRow 81 lm4k512l248krS0SegsR81 lm4k512l248krS0RowR81,
    s0ChkRow 82 lm4k512l248krS0SegsR82 lm4k512l248krS0RowR82,
    s0ChkRow 83 lm4k512l248krS0SegsR83 lm4k512l248krS0RowR83,
    s0ChkRow 84 lm4k512l248krS0SegsR84 lm4k512l248krS0RowR84,
    s0ChkRow 85 lm4k512l248krS0SegsR85 lm4k512l248krS0RowR85,
    s0ChkRow 86 lm4k512l248krS0SegsR86 lm4k512l248krS0RowR86,
    s0ChkRow 87 lm4k512l248krS0SegsR87 lm4k512l248krS0RowR87,
    s0ChkRow 88 lm4k512l248krS0SegsR88 lm4k512l248krS0RowR88,
    s0ChkRow 89 lm4k512l248krS0SegsR89 lm4k512l248krS0RowR89,
    s0ChkRow 90 lm4k512l248krS0SegsR90 lm4k512l248krS0RowR90,
    s0ChkRow 91 lm4k512l248krS0SegsR91 lm4k512l248krS0RowR91,
    s0ChkRow 92 lm4k512l248krS0SegsR92 lm4k512l248krS0RowR92,
    s0ChkRow 93 lm4k512l248krS0SegsR93 lm4k512l248krS0RowR93,
    s0ChkRow 94 lm4k512l248krS0SegsR94 lm4k512l248krS0RowR94,
    s0ChkRow 95 lm4k512l248krS0SegsR95 lm4k512l248krS0RowR95,
    s0ChkRow 96 lm4k512l248krS0SegsR96 lm4k512l248krS0RowR96,
    s0ChkRow 102 lm4k512l248krS0SegsR102 lm4k512l248krS0RowR102,
    s0ChkRow 104 lm4k512l248krS0SegsR104 lm4k512l248krS0RowR104,
    s0ChkRow 105 lm4k512l248krS0SegsR105 lm4k512l248krS0RowR105
  ] = true := by decide +kernel
private theorem s0AncB4_ok (rest : List RampKick128kAnchor)
    (hrest : RampKick128kAnchorsSound 4 248 rest) :
    RampKick128kAnchorsSound 4 248 (s0AncB4 ++ rest) := by
  exact
    ⟨s0ChkRow_eq (s0_hd s0RowChk4),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 s0RowChk4)),
    ⟨s0ChkRow_eq (s0_hd (s0_tl2 s0RowChk4)),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl2 s0RowChk4))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl4 s0RowChk4)),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl4 s0RowChk4))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl2 (s0_tl4 s0RowChk4))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl2 (s0_tl4 s0RowChk4)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl8 s0RowChk4)),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl8 s0RowChk4))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl2 (s0_tl8 s0RowChk4))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl2 (s0_tl8 s0RowChk4)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl4 (s0_tl8 s0RowChk4))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl4 (s0_tl8 s0RowChk4)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl2 (s0_tl4 (s0_tl8 s0RowChk4)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl2 (s0_tl4 (s0_tl8 s0RowChk4))))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl8 (s0_tl8 s0RowChk4))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl8 (s0_tl8 s0RowChk4)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl2 (s0_tl8 (s0_tl8 s0RowChk4)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl2 (s0_tl8 (s0_tl8 s0RowChk4))))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl4 (s0_tl8 (s0_tl8 s0RowChk4)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl4 (s0_tl8 (s0_tl8 s0RowChk4))))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl2 (s0_tl4 (s0_tl8 (s0_tl8 s0RowChk4))))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl2 (s0_tl4 (s0_tl8 (s0_tl8 s0RowChk4)))))),
    hrest⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
private def s0AncB5 : List RampKick128kAnchor :=
  [lm4k512l248krS0AncR106, lm4k512l248krS0AncR107, lm4k512l248krS0AncR108,
   lm4k512l248krS0AncR110, lm4k512l248krS0AncR111, lm4k512l248krS0AncR113,
   lm4k512l248krS0AncR114, lm4k512l248krS0AncR115, lm4k512l248krS0AncR116,
   lm4k512l248krS0AncR118, lm4k512l248krS0AncR119, lm4k512l248krS0AncR120,
   lm4k512l248krS0AncR122, lm4k512l248krS0AncR123, lm4k512l248krS0AncR124,
   lm4k512l248krS0AncR125, lm4k512l248krS0AncR126, lm4k512l248krS0AncR127,
   lm4k512l248krS0AncR132, lm4k512l248krS0AncR144, lm4k512l248krS0AncR156,
   lm4k512l248krS0AncR168, lm4k512l248krS0AncR184, lm4k512l248krS0AncR220]
private theorem s0RowChk5 : s0AtF [
    s0ChkRow 106 lm4k512l248krS0SegsR106 lm4k512l248krS0RowR106,
    s0ChkRow 107 lm4k512l248krS0SegsR107 lm4k512l248krS0RowR107,
    s0ChkRow 108 lm4k512l248krS0SegsR108 lm4k512l248krS0RowR108,
    s0ChkRow 110 lm4k512l248krS0SegsR110 lm4k512l248krS0RowR110,
    s0ChkRow 111 lm4k512l248krS0SegsR111 lm4k512l248krS0RowR111,
    s0ChkRow 113 lm4k512l248krS0SegsR113 lm4k512l248krS0RowR113,
    s0ChkRow 114 lm4k512l248krS0SegsR114 lm4k512l248krS0RowR114,
    s0ChkRow 115 lm4k512l248krS0SegsR115 lm4k512l248krS0RowR115,
    s0ChkRow 116 lm4k512l248krS0SegsR116 lm4k512l248krS0RowR116,
    s0ChkRow 118 lm4k512l248krS0SegsR118 lm4k512l248krS0RowR118,
    s0ChkRow 119 lm4k512l248krS0SegsR119 lm4k512l248krS0RowR119,
    s0ChkRow 120 lm4k512l248krS0SegsR120 lm4k512l248krS0RowR120,
    s0ChkRow 122 lm4k512l248krS0SegsR122 lm4k512l248krS0RowR122,
    s0ChkRow 123 lm4k512l248krS0SegsR123 lm4k512l248krS0RowR123,
    s0ChkRow 124 lm4k512l248krS0SegsR124 lm4k512l248krS0RowR124,
    s0ChkRow 125 lm4k512l248krS0SegsR125 lm4k512l248krS0RowR125,
    s0ChkRow 126 lm4k512l248krS0SegsR126 lm4k512l248krS0RowR126,
    s0ChkRow 127 lm4k512l248krS0SegsR127 lm4k512l248krS0RowR127,
    s0ChkRow 132 lm4k512l248krS0SegsR132 lm4k512l248krS0RowR132,
    s0ChkRow 144 lm4k512l248krS0SegsR144 lm4k512l248krS0RowR144,
    s0ChkRow 156 lm4k512l248krS0SegsR156 lm4k512l248krS0RowR156,
    s0ChkRow 168 lm4k512l248krS0SegsR168 lm4k512l248krS0RowR168,
    s0ChkRow 184 lm4k512l248krS0SegsR184 lm4k512l248krS0RowR184,
    s0ChkRow 220 lm4k512l248krS0SegsR220 lm4k512l248krS0RowR220
  ] = true := by decide +kernel
private theorem s0AncB5_ok (rest : List RampKick128kAnchor)
    (hrest : RampKick128kAnchorsSound 4 248 rest) :
    RampKick128kAnchorsSound 4 248 (s0AncB5 ++ rest) := by
  exact
    ⟨s0ChkRow_eq (s0_hd s0RowChk5),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 s0RowChk5)),
    ⟨s0ChkRow_eq (s0_hd (s0_tl2 s0RowChk5)),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl2 s0RowChk5))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl4 s0RowChk5)),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl4 s0RowChk5))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl2 (s0_tl4 s0RowChk5))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl2 (s0_tl4 s0RowChk5)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl8 s0RowChk5)),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl8 s0RowChk5))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl2 (s0_tl8 s0RowChk5))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl2 (s0_tl8 s0RowChk5)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl4 (s0_tl8 s0RowChk5))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl4 (s0_tl8 s0RowChk5)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl2 (s0_tl4 (s0_tl8 s0RowChk5)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl2 (s0_tl4 (s0_tl8 s0RowChk5))))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl8 (s0_tl8 s0RowChk5))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl8 (s0_tl8 s0RowChk5)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl2 (s0_tl8 (s0_tl8 s0RowChk5)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl2 (s0_tl8 (s0_tl8 s0RowChk5))))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl4 (s0_tl8 (s0_tl8 s0RowChk5)))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl4 (s0_tl8 (s0_tl8 s0RowChk5))))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl2 (s0_tl4 (s0_tl8 (s0_tl8 s0RowChk5))))),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 (s0_tl2 (s0_tl4 (s0_tl8 (s0_tl8 s0RowChk5)))))),
    hrest⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
private def s0AncB6 : List RampKick128kAnchor :=
  [lm4k512l248krS0AncR288, lm4k512l248krS0AncR304]
private theorem s0RowChk6 : s0AtF [
    s0ChkRow 288 lm4k512l248krS0SegsR288 lm4k512l248krS0RowR288,
    s0ChkRow 304 lm4k512l248krS0SegsR304 lm4k512l248krS0RowR304
  ] = true := by decide +kernel
private theorem s0AncB6_ok (rest : List RampKick128kAnchor)
    (hrest : RampKick128kAnchorsSound 4 248 rest) :
    RampKick128kAnchorsSound 4 248 (s0AncB6 ++ rest) := by
  exact
    ⟨s0ChkRow_eq (s0_hd s0RowChk6),
    ⟨s0ChkRow_eq (s0_hd (s0_tl1 s0RowChk6)),
    hrest⟩⟩
private def s0AncB7 : List RampKick128kAnchor :=
  [lm4k512l248krS0AncR368]
private theorem s0RowChk7 : s0AtF [
    s0ChkRow 368 lm4k512l248krS0SegsR368 lm4k512l248krS0RowR368
  ] = true := by decide +kernel
private theorem s0AncB7_ok (rest : List RampKick128kAnchor)
    (hrest : RampKick128kAnchorsSound 4 248 rest) :
    RampKick128kAnchorsSound 4 248 (s0AncB7 ++ rest) := by
  exact
    ⟨s0ChkRow_eq (s0_hd s0RowChk7),
    hrest⟩
private theorem s0Ancs_append (rest : List RampKick128kAnchor) :
    pfxAnchorsLt512 ++ rest = s0AncB0 ++ (s0AncB1 ++ (s0AncB2 ++
      (s0AncB3 ++ (s0AncB4 ++ (s0AncB5 ++ (s0AncB6 ++ (s0AncB7 ++ rest))))))) := rfl
private def s0Ch0 : List Rkm128kSeg := [
  ⟨1, 2807859, 1, 8, []⟩,
  ⟨1, 2873848, 1, 8, []⟩,
  ⟨2, 2071568, 1, 9, []⟩,
  ⟨2, 1933908, 1, 9, []⟩,
  ⟨3, 1577670, 1, 9, []⟩,
  ⟨4, 1353610, 1, 10, []⟩,
  ⟨4, 1090581, 1, 9, []⟩,
  ⟨5, 1214472, 1, 10, []⟩,
  ⟨5, 1215318, 1, 10, []⟩,
  ⟨6, 1112527, 1, 10, []⟩,
  ⟨7, 1030917, 1, 10, []⟩,
  ⟨7, 1031705, 1, 10, []⟩,
  ⟨8, 960373, 1, 10, []⟩,
  ⟨9, 927189, 1, 10, []⟩,
  ⟨10, 858776, 1, 10, []⟩,
  ⟨11, 818347, 1, 11, []⟩,
  ⟨13, 1762275, 1, 17, []⟩,
  ⟨15, 1656152, 1, 18, []⟩,
  ⟨17, 1553980, 1, 18, rkm128kMask56 3 [6]⟩,
  ⟨20, 1448374, 1, 19, rkm128kMask56 10 [773]⟩,
  ⟨22, 1379534, 1, 19, rkm128kMask56 11 [1963]⟩,
  ⟨25, 1306757, 1, 20, rkm128kMask56 25 [25357507]⟩,
  ⟨28, 1273641, 1, 21, rkm128kMask56 32 [3504830635]⟩,
  ⟨31, 1181574, 1, 23, rkm128kMask56 40 [1003790648535]⟩,
  ⟨33, 856920, 1, 20, rkm128kMask56 124 [31599759310486, 0, 2048]⟩,
  ⟨36, 787548, 1, 20, rkm128kMask56 137 [1079687175212155, 0, 16777216]⟩,
  ⟨38, 779326, 1, 21, rkm128kMask56 128 [28186155431098855, 0, 32768]⟩,
  ⟨41, 749386, 1, 22, rkm128kMask56 60 [56993002134044623, 13]⟩,
  ⟨45, 692196, 1, 23, rkm128kMask56 66 [42275853879499145, 966]⟩,
  ⟨48, 678717, 1, 23, rkm128kMask56 138 [71913954653806114, 30460, 33587200]⟩,
  ⟨52, 634860, 1, 24, rkm128kMask56 77 [27755742233605670, 1876707]⟩]
private def s0V0S0 : List ℤ :=
  [s0N 1667443562, s0N 626318202, s0N 400258507, s0P 1524291203, s0P 2458663271, s0P 911204781,
   s0P 2603762413, s0P 5786942525, s0P 6906570069, s0N 2424458846, s0P 5087905427,
   s0P 18576015911, s0P 35414966327, s0P 19544539539, s0N 1770770003, s0N 28417921649,
   s0P 42527934103, s0P 32228619313, s0P 2759128311, s0P 52659003392, s0N 5773998410,
   s0N 46372024892, s0N 45644354981, s0P 1413411479, s0P 64945848458, s0N 50781915866,
   s0N 5861317373, s0P 151161284974, s0P 124329821831, s0P 16935997269, s0N 263125017353,
   s0N 135828410240, s0N 166926916478, s0N 109085499010, s0N 239723148365, s0P 142215005880,
   s0P 496840592005, s0N 111016052541, s0N 390437280245, s0N 380561651523, s0N 2260033050,
   s0N 482804684436, s0P 195316657688, s0N 263463381653, s0N 339783189933, s0P 105423570439,
   s0N 418817521630, s0P 531957867436, s0N 353208059424, s0N 1540415916491, s0N 182710182491,
   s0N 164711691674, s0P 316948854762, s0N 389656655077, s0P 1432479935948, s0N 105764362604,
   s0N 526515935980, s0N 1230680405933, s0N 372786203322, s0N 510408787444, s0P 674887989104,
   s0N 3026981780654, s0P 1501108255082, s0N 165790929979]
private def s0V0S1 : List ℤ :=
  [s0P 252662793884, s0N 1214991160018, s0P 1761051116302, s0N 1430804696803, s0P 986832584069,
   s0N 1548745952436, s0N 651352152381, s0P 78790304357, s0P 2126563897601, s0P 1951377586002,
   s0P 835987257481, s0P 3090832425994, s0P 1150850855830, s0P 7776993481311,
   s0P 25447087529384, s0P 52560822648152, s0P 88609287762454, s0P 131744711262274,
   s0P 178867812491317, s0P 225986412346741, s0P 268784698111909, s0P 303276710613322,
   s0P 326399971627980, s0P 336428040739087, s0P 333131905923407, s0P 317682567052933,
   s0P 292343368203847, s0P 260037258027958, s0P 223885380952512, s0P 186801231462453,
   s0P 151196744303816, s0P 118823158987084, s0P 90739331728818, s0P 67379272310140,
   s0P 48681113463640, s0P 34240257451442, s0P 23456889638135, s0P 15658644652107,
   s0P 10189743987128, s0P 6466310070016, s0P 4002933121959, s0P 2418022167513,
   s0P 1425681233728, s0P 820681229729, s0P 461335395952, s0P 253303384540, s0P 135872334675,
   s0P 71213707743, s0P 36476126022, s0P 18261238899, s0P 8936888237, s0P 4275921819,
   s0P 2000360587, s0P 915092431, s0P 409391063, s0P 179127714, s0P 76659975, s0P 32090869,
   s0P 13140976, s0P 5263916, s0P 2062943, s0P 790835, s0P 296514, s0P 108842]
private def s0V0S2 : List ℤ :=
  [s0P 39113, s0P 13678, s0P 4597, s0P 1465, s0P 437, s0P 121, s0P 30, s0P 5, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0]
private def s0V0S3 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V0 : List ℤ :=
  s0V0S0 ++
  (s0V0S1 ++
  (s0V0S2 ++
  s0V0S3))
private def s0Ch1 : List Rkm128kSeg := [
  ⟨53, 648700, 1, 24,
    rkm128kMask56 203 [45762583419341582, 52408674, 137438953472, 17179869184]⟩,
  ⟨56, 617981, 1, 25, rkm128kMask56 88 [70264766755491291, 3242587751]⟩,
  ⟨59, 612139, 1, 25, rkm128kMask56 235 [70399098282035544, 241300283897, 4194304, 0, 1032]⟩,
  ⟨61, 600089, 1, 25, rkm128kMask56 100 [48021404949379930, 15396174152952]⟩,
  ⟨65, 580812, 1, 26,
    rkm128kMask56 238 [58386776832006564, 992002473115082, 17179869184, 549755813888, 8192]⟩,
  ⟨67, 569646, 1, 26,
    rkm128kMask56 164 [31382959210149874, 65316414280674730, 2251799813685248]⟩,
  ⟨70, 551571, 1, 26,
    rkm128kMask56 280 [14611704363427635, 24092012076682372, 56, 4096, 36028797019492352]⟩]
private def s0V1S0 : List ℤ :=
  [s0N 1250988085, s0N 535600846, s0N 850971510, s0N 426848341, s0N 338891282, s0P 2480752378,
   s0P 169634631, s0P 634789844, s0P 5592514897, s0N 5538196643, s0N 5011509180, s0N 4134728605,
   s0N 5622482373, s0P 3385470, s0P 6695649414, s0P 13353554680, s0P 11108728408, s0P 916865964,
   s0N 34206713983, s0N 22053750956, s0N 109997717023, s0N 104804089466, s0N 45993943749,
   s0P 22823987181, s0N 23169621729, s0N 24610083047, s0N 73184566997, s0N 37919261779,
   s0N 34027543498, s0N 62507784313, s0N 82163137824, s0P 46592521771, s0N 34012171582,
   s0P 146474949964, s0P 161201508093, s0P 122388009584, s0N 14485304575, s0N 205447986399,
   s0P 78122676904, s0P 273917422935, s0P 186514208527, s0N 120480740793, s0N 544019685897,
   s0N 108692816497, s0N 255310417517, s0N 593659257341, s0N 55561047419, s0N 67668002796,
   s0N 61755813544, s0P 1216248884920, s0P 839039998028, s0P 687294508165, s0P 1208478027472,
   s0P 1002476255889, s0N 93401649079, s0N 918701762556, s0P 682527513810, s0P 357079983231,
   s0P 1164971876710, s0N 2251727322983, s0N 951047716237, s0N 970168630284, s0P 383795495969,
   s0P 528476919209]
private def s0V1S1 : List ℤ :=
  [s0P 868878930387, s0N 25340419399, s0P 1175261073198, s0N 874136570176, s0N 6370598228,
   s0P 92952108013, s0P 1293301788013, s0P 210964306986, s0P 1323025595231, s0N 452636783422,
   s0N 232676303945, s0P 2772883127336, s0P 930556311434, s0P 2728146569013, s0N 11298858818,
   s0P 392646374909, s0P 870548601331, s0N 2835152302540, s0N 559130298067, s0P 166861640792,
   s0P 649241951146, s0P 71495425990, s0P 53242211219, s0P 212584163632, s0N 126506541132,
   s0P 1163230896974, s0P 919748716056, s0N 2104112700363, s0N 2365316352044, s0N 2054342952622,
   s0N 1320790623627, s0P 1778241879447, s0P 4125558921206, s0P 2092338654517, s0N 47902609247,
   s0P 1194723716680, s0N 3089583179603, s0N 5510733642656, s0P 1792760600224,
   s0P 3611464537939, s0N 4500529055683, s0P 673024964737, s0P 3124804720326, s0N 2595798926151,
   s0P 1188302024166, s0P 1914571380968, s0N 770535474002, s0N 2398286254354, s0N 979003437069,
   s0P 3026093571352, s0P 3438335787436, s0P 738341623447, s0P 4777209544608, s0P 2737688189645,
   s0P 9368137258672, s0P 32920018093168, s0P 67157976724357, s0P 109721398326108,
   s0P 157116063410432, s0P 205204537878017, s0P 249732624100587, s0P 286875047353914,
   s0P 313705161509068, s0P 328490614783173]
private def s0V1S2 : List ℤ :=
  [s0P 330798453143157, s0P 321413494880854, s0P 302090495549071, s0P 275214189870429,
   s0P 243440496057203, s0P 209371770265353, s0P 175290119859009, s0P 143007973733554,
   s0P 113785896543964, s0P 88371409566912, s0P 67034328309928, s0P 49695892705888,
   s0P 36026687780229, s0P 25548832480176, s0P 17734396081820, s0P 12055367108454,
   s0P 8025586267792, s0P 5233780090886, s0P 3346142293864, s0P 2098003833814,
   s0P 1289447989256, s0P 777093354440, s0P 460107234683, s0P 267981506535, s0P 153053029541,
   s0P 85006199998, s0P 45453288531, s0P 23238951693, s0P 11360240656, s0P 5353163669,
   s0P 2471001131, s0P 1138775957, s0P 533853343, s0P 255993204, s0P 124561260, s0P 61247983,
   s0P 30211199, s0P 14527894, s0P 6566696, s0P 2743597, s0P 1077528, s0P 417413, s0P 168470,
   s0P 72231, s0P 32014, s0P 14087, s0P 5993, s0P 2437, s0P 943, s0P 345, s0P 118, s0P 35,
   s0N 7, s0P 1, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V1S3 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V1S4 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V1 : List ℤ :=
  s0V1S0 ++
  (s0V1S1 ++
  (s0V1S2 ++
  (s0V1S3 ++
  s0V1S4)))
private def s0Ch2 : List Rkm128kSeg := [
  ⟨73, 543118, 1, 27,
    rkm128kMask56 293 [49486254752164785, 63251837283027529, 3232, 35184372088832, 0, 6144]⟩,
  ⟨76, 533029, 1, 27,
    rkm128kMask56 299 [3935499580101678, 14252984992759487, 212147, 17592186044416, 0, 393216]⟩,
  ⟨78, 404503, 1, 23,
    rkm128kMask56 313 [9589178556236233, 70083771487222009, 7738433, 0, 36028797023158272,
     6814564864]⟩,
  ⟨80, 376742, 1, 22,
    rkm128kMask56 319 [36390342973912612, 49105846792917586, 239651963, 68719476736,
     68720525312, 347074068480]⟩,
  ⟨84, 363248, 1, 23,
    rkm128kMask56 336 [36749536468326548, 24909849342289220, 3288083817, 4503599627370496, 0,
     70630222742953984]⟩]
private def s0V2S0 : List ℤ :=
  [s0N 961184257, s0N 621755164, s0N 451160352, s0N 1204877608, s0P 141650955, s0N 85635893,
   s0N 3623539811, s0N 232418682, s0N 1628374661, s0P 4300050366, s0N 505930451, s0N 3692193302,
   s0P 948530443, s0N 570061453, s0P 6850015502, s0P 5240731312, s0N 6713529704,
   s0N 28305146694, s0N 12190342224, s0P 19481074623, s0P 21485274090, s0P 37739146087,
   s0P 25758099682, s0P 15416640259, s0P 12951023650, s0P 17919328846, s0N 27411357807,
   s0N 20935026773, s0P 16029062113, s0P 64701217626, s0P 72122792747, s0N 95547970337,
   s0N 159988883746, s0N 41757748519, s0N 96201213761, s0N 152992442603, s0N 126252544714,
   s0P 168453458566, s0P 6823194752, s0N 145920784533, s0P 8515903585, s0N 114390585775,
   s0N 68481944031, s0N 369262756809, s0N 313578908327, s0P 113337498254, s0P 141650964691,
   s0N 102449850814, s0N 290469501515, s0P 43950301431, s0P 551486514375, s0P 279910995786,
   s0P 1364383945421, s0N 685282323615, s0N 887845081756, s0N 406406299900, s0N 1470651231318,
   s0N 1122998228462, s0N 323161691626, s0N 330717649563, s0N 1642853277348, s0N 822496787032,
   s0N 939622561138, s0N 836492323091]
private def s0V2S1 : List ℤ :=
  [s0P 642936466091, s0N 202230710092, s0N 1818191609341, s0P 1004801572187, s0P 256571909480,
   s0P 62511143929, s0P 791965728996, s0N 229886247168, s0P 67520026046, s0P 1448428561978,
   s0P 441307314811, s0P 1064844169532, s0N 650390078135, s0N 381546970600, s0P 477378333020,
   s0P 1593467121379, s0P 708051373036, s0P 2140036756870, s0P 2326405964929, s0P 1557326400108,
   s0N 1889803715622, s0N 2075851874686, s0N 428691918130, s0P 1192364582809, s0P 1396267803445,
   s0N 622721480827, s0P 1412918096704, s0P 1524538810417, s0P 1671357772986, s0P 2126854480293,
   s0P 2223483268400, s0P 4213035078801, s0N 1564216074022, s0P 5562129478013,
   s0N 2339591555666, s0P 599417934447, s0P 1566892085660, s0P 63026246301, s0N 3360619982939,
   s0P 2322928567804, s0N 670898929633, s0N 2195520454999, s0N 1166258826720, s0P 4252834883544,
   s0N 508107307309, s0P 3786489986679, s0P 1368194993396, s0P 669810732770, s0P 477801406718,
   s0P 2163026810334, s0N 2205173830597, s0P 2476204538315, s0P 658645913236, s0P 1915384365552,
   s0P 3115821580556, s0P 2769492278322, s0N 3186676420601, s0N 386274676300, s0N 2250859256305,
   s0P 2694901499078, s0P 3637896496151, s0N 6398431223287, s0N 2400569068577,
   s0N 4605329360889]
private def s0V2S2 : List ℤ :=
  [s0P 511045442691, s0N 269057213452, s0P 2233023187048, s0P 3004105935631, s0P 952247684938,
   s0P 1634842996202, s0N 4175371751460, s0N 147550796373, s0N 2015680299141, s0N 2239101203404,
   s0N 385470977700, s0P 1854904221895, s0P 5105658496044, s0P 2866643766172, s0P 2842210445889,
   s0P 4686127698708, s0P 3463397930855, s0P 24138754216429, s0P 56799315341618,
   s0P 98877700033719, s0P 146579539632543, s0P 195512207361770, s0P 241263334583770,
   s0P 279929724607552, s0P 308541917715808, s0P 325330292634656, s0P 329803833854138,
   s0P 322649182081860, s0P 305491361846170, s0P 280575393765589, s0P 250428381125498,
   s0P 217551904596725, s0P 184180319364891, s0P 152123541249502, s0P 122695387837326,
   s0P 96714709944786, s0P 74559314693212, s0P 56251459089402, s0P 41555948597148,
   s0P 30075659868732, s0P 21333894310246, s0P 14837928960237, s0P 10122664121183,
   s0P 6776505195289, s0P 4453212942850, s0P 2873720336018, s0P 1821454440699,
   s0P 1134016225999, s0P 693390169386, s0P 416224868702, s0P 245147654327, s0P 141577418903,
   s0P 80121938703, s0P 44410206105, s0P 24103185548, s0P 12810095108, s0P 6669664437,
   s0P 3404737729, s0P 1706076132, s0P 840372889, s0P 407556484, s0P 194901243, s0P 92029743,
   s0P 42948116]
private def s0V2S3 : List ℤ :=
  [s0P 19818890, s0P 9043850, s0P 4079706, s0P 1818351, s0P 800302, s0P 347660, s0P 149020,
   s0P 63018, s0P 26285, s0P 10809, s0P 4373, s0P 1734, s0P 669, s0P 246, s0P 84, s0P 25, s0P 6,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V2S4 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V2S5 : List ℤ :=
  [s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0, s0P 0,
   s0P 0, s0P 0, s0P 0, s0P 0]
private def s0V2 : List ℤ :=
  s0V2S0 ++
  (s0V2S1 ++
  (s0V2S2 ++
  (s0V2S3 ++
  (s0V2S4 ++
  s0V2S5))))
private def s0Ch3 : List Rkm128kSeg := [
  ⟨86, 361716, 1, 23,
    rkm128kMask56 345 [5096041392662769, 54441929167955027, 103773881647, 36028797018963968,
     9663676416, 42920972584484864, 273]⟩,
  ⟨88, 356734, 1, 23,
    rkm128kMask56 351 [69257979899580393, 52988051736198604, 3511414948626, 9007199254740992, 0,
     2238045474783232, 18340]⟩,
  ⟨91, 351093, 1, 23,
    rkm128kMask56 365 [14451427164924394, 13148026250564021, 53987580999527, 0, 0,
     26641166741012481, 323264294]⟩,
  ⟨94, 354393, 1, 24,
    rkm128kMask56 377 [33226306435026563, 32434211249567638, 1864832164706964, 0, 536870912,
     15763011014754304, 1612530761509]⟩]
private theorem s0Segs_split : lm4k512l248krS0Segs =
    s0Ch0 ++ (s0Ch1 ++ (s0Ch2 ++ s0Ch3)) := rfl
private theorem s0B0_ok :
    s0RunAtEq s0Ch0 lm4k512l248krS0LIn lm4k512l248krS0DCurIn lm4k512l248krS0PadIn
      lm4k512l248krS0VecIn 52 208 1000822600 s0V0
      = true := by decide +kernel
private theorem s0B1_ok :
    s0RunAtEq s0Ch1 52 208 1000822600 s0V0
      70 280 1317849377 s0V1 = true := by decide +kernel
private theorem s0B2_ok :
    s0RunAtEq s0Ch2 70 280 1317849377 s0V1
      84 336 1504766184 s0V2 = true := by decide +kernel
private theorem s0B3_ok :
    s0RunAtEq s0Ch3 84 336 1504766184 s0V2
      lm4k512l248krS0LOut lm4k512l248krS0DCurOut lm4k512l248krS0PadOut lm4k512l248krS0Vec
      = true := by decide +kernel

/-- `RampKick128kAnchorsSound 4 248` prefix combiner across all `101` `r < 512` anchors. -/
theorem pfxAnchorsLt512_append_sound (rest : List RampKick128kAnchor)
    (hrest : RampKick128kAnchorsSound 4 248 rest) :
    RampKick128kAnchorsSound 4 248 (pfxAnchorsLt512 ++ rest) := by
  rw [s0Ancs_append]
  exact s0AncB0_ok _ (s0AncB1_ok _ (s0AncB2_ok _ (s0AncB3_ok _
    (s0AncB4_ok _ (s0AncB5_ok _ (s0AncB6_ok _ (s0AncB7_ok _ hrest)))))))

/-- Standalone `RampKick128kAnchorsSound 4 248` certificate for `pfxAnchorsLt512`. -/
theorem pfxAnchorsLt512_sound : RampKick128kAnchorsSound 4 248 pfxAnchorsLt512 := by
  rw [← List.append_nil pfxAnchorsLt512]
  exact pfxAnchorsLt512_append_sound [] trivial

/-- Alias prefix combiner matching `lm4k512l248krS0AncsLt512` convention. -/
theorem lm4k512l248krS0_ancsLt512_sound (rest : List RampKick128kAnchor)
    (hrest : RampKick128kAnchorsSound 4 248 rest) :
    RampKick128kAnchorsSound 4 248 (lm4k512l248krS0AncsLt512 ++ rest) :=
  pfxAnchorsLt512_append_sound rest hrest

/-- Alias prefix combiner matching `lm4k512l248krS0PfxAnchors` convention. -/
theorem lm4k512l248krS0_pfxAnchors_append_sound (rest : List RampKick128kAnchor)
    (hrest : RampKick128kAnchorsSound 4 248 rest) :
    RampKick128kAnchorsSound 4 248 (lm4k512l248krS0PfxAnchors ++ rest) :=
  pfxAnchorsLt512_append_sound rest hrest

/-- Standalone alias certificate matching `lm4k512l248krS0PfxAnchors` convention. -/
theorem lm4k512l248krS0_pfxAnchors_sound :
    RampKick128kAnchorsSound 4 248 lm4k512l248krS0PfxAnchors :=
  pfxAnchorsLt512_sound

/-- Segment count of `lm4k512l248krS0Segs` (`47` segments). -/
theorem lm4k512l248krS0_len : rkm128kSegListLen lm4k512l248krS0Segs = 47 := rfl

/-- Exact `rkm128kRunSegs 4 248 512` step across `lm4k512l248krS0Segs` (`segs 0..46`). -/
theorem lm4k512l248krS0_step :
    rkm128kRunSegs 4 248 512 lm4k512l248krS0Segs 1 0 1 [Int.ofNat wdScale] =
      (lm4k512l248krS0LOut, lm4k512l248krS0DCurOut,
        lm4k512l248krS0PadOut, lm4k512l248krS0Vec) := by
  rw [s0Segs_split]
  exact s0RunStep s0B0_ok (s0RunStep s0B1_ok (s0RunStep s0B2_ok (s0RunLast s0B3_ok)))

/-- Suffix chaining lemma advancing `rkm128kRunSegs 4 248 512` past `lm4k512l248krS0Segs`. -/
theorem lm4k512l248krS0_run_after (rest : List Rkm128kSeg) :
    rkm128kRunSegs 4 248 512 (lm4k512l248krS0Segs ++ rest) 1 0 1 [Int.ofNat wdScale] =
      rkm128kRunSegs 4 248 512 rest lm4k512l248krS0LOut lm4k512l248krS0DCurOut
        lm4k512l248krS0PadOut lm4k512l248krS0Vec := by
  rw [rkm128kRunSegs_append]; dsimp only; rw [lm4k512l248krS0_step]

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

end QuantumComputation.Specs.GroverFindAll.Rk128kLowM4K512L248KrPt0
