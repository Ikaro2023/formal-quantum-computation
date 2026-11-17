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
# High-`m` Coupled Walk & Trajectory Part `1` (`FindAllJohnsonRampKickMuxHi128T1`)

Certifies `(m = 128, r in {38,44,50,57,64,96})` coupled `T_16` walks (`19889` coords).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Unpacks `len` LSB-first bits of `< 2 ^ 50` word `w`
  (`FindAllJohnsonRampKickMuxHi128T1`). -/
def rkmWordBitsHi128T1 : ℕ → ℕ → List Bool
  | 0, _ => []
  | j + 1, w => Nat.ble 1 (Nat.mod w 2) :: rkmWordBitsHi128T1 j (Nat.div w 2)
/-- Unpacks `< 2 ^ 50` words of lengths `ns` (`FindAllJohnsonRampKickMuxHi128T1`). -/
def rkmUnpackMaskHi128T1 : List ℕ → List ℕ → List Bool
  | [], _ => []
  | _, [] => []
  | n :: ns, w :: ws => rkmWordBitsHi128T1 n w ++ rkmUnpackMaskHi128T1 ns ws
/-- Mask segment `0` for `(m = 128, r = 38)`. -/
def rkmMkHiHiB_m128_r38_s0 : List Bool := rkmUnpackMaskHi128T1 [38] [266287983904]
/-- Mask segment `1` for `(m = 128, r = 38)`. -/
def rkmMkHiHiB_m128_r38_s1 : List Bool := rkmUnpackMaskHi128T1 [23] [7689600]
/-- Mask segment `2` for `(m = 128, r = 38)`. -/
def rkmMkHiHiB_m128_r38_s2 : List Bool := rkmUnpackMaskHi128T1 [38] [274860076032]
/-- Mask segment `3` for `(m = 128, r = 38)`. -/
def rkmMkHiHiB_m128_r38_s3 : List Bool := rkmUnpackMaskHi128T1 [38] [274856583168]
/-- Mask segment `4` for `(m = 128, r = 38)`. -/
def rkmMkHiHiB_m128_r38_s4 : List Bool := rkmUnpackMaskHi128T1 [38] [274868903936]
/-- Mask segment `5` for `(m = 128, r = 38)`. -/
def rkmMkHiHiB_m128_r38_s5 : List Bool := rkmUnpackMaskHi128T1 [38] [274876235776]
/-- Mask segment `6` for `(m = 128, r = 38)`. -/
def rkmMkHiHiB_m128_r38_s6 : List Bool := rkmUnpackMaskHi128T1 [38] [272730947712]
/-- Prefix-kick masks for `(m = 128, r = 38)`. -/
def rkmMasksHiHiB_m128_r38 : List (List Bool) :=
  [rkmMkHiHiB_m128_r38_s0, rkmMkHiHiB_m128_r38_s1, rkmMkHiHiB_m128_r38_s2, rkmMkHiHiB_m128_r38_s3,
   rkmMkHiHiB_m128_r38_s4, rkmMkHiHiB_m128_r38_s5, rkmMkHiHiB_m128_r38_s6, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 38)`. -/
def rkmRowHiHiB_m128_r38 : List ℕ :=
  [118740048, 6245364958, 12293420803, 37367534423, 19119279520, 581454228212, 6922554792,
   2345580622, 42894151931, 108665680830, 95032284641, 58463158309, 22543403255, 5407957982,
   794206042, 73384928, 4473972, 187823, 5656, 128, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0]
/-- Mask segment `0` for `(m = 128, r = 44)`. -/
def rkmMkHiHiB_m128_r44_s0 : List Bool := rkmUnpackMaskHi128T1 [23] [8306048]
/-- Mask segment `1` for `(m = 128, r = 44)`. -/
def rkmMkHiHiB_m128_r44_s1 : List Bool := rkmUnpackMaskHi128T1 [28] [246337024]
/-- Mask segment `2` for `(m = 128, r = 44)`. -/
def rkmMkHiHiB_m128_r44_s2 : List Bool := rkmUnpackMaskHi128T1 [28] [218234881]
/-- Mask segment `3` for `(m = 128, r = 44)`. -/
def rkmMkHiHiB_m128_r44_s3 : List Bool := rkmUnpackMaskHi128T1 [33] [6048317441]
/-- Mask segment `4` for `(m = 128, r = 44)`. -/
def rkmMkHiHiB_m128_r44_s4 : List Bool := rkmUnpackMaskHi128T1 [33] [6352928769]
/-- Mask segment `5` for `(m = 128, r = 44)`. -/
def rkmMkHiHiB_m128_r44_s5 : List Bool := rkmUnpackMaskHi128T1 [30] [614465556]
/-- Mask segment `6` for `(m = 128, r = 44)`. -/
def rkmMkHiHiB_m128_r44_s6 : List Bool := rkmUnpackMaskHi128T1 [36] [39973814312]
/-- Prefix-kick masks for `(m = 128, r = 44)`. -/
def rkmMasksHiHiB_m128_r44 : List (List Bool) :=
  [rkmMkHiHiB_m128_r44_s0, rkmMkHiHiB_m128_r44_s1, rkmMkHiHiB_m128_r44_s2, rkmMkHiHiB_m128_r44_s3,
   rkmMkHiHiB_m128_r44_s4, rkmMkHiHiB_m128_r44_s5, rkmMkHiHiB_m128_r44_s6, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 44)`. -/
def rkmRowHiHiB_m128_r44 : List ℕ :=
  [4962286, 92540920, 118706872, 87578164, 4491960105, 4565459772, 134317388, 1786126004,
   6247768435, 23552135074, 32562860795, 100873511235, 69454034317, 132192658476, 134743796390,
   105779321574, 110070584557, 120793664384, 88752074389, 44991529271, 15018041983, 3190613928,
   440012622, 41000059, 2710830, 132829, 5170, 135, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Mask segment `0` for `(m = 128, r = 50)`. -/
def rkmMkHiHiB_m128_r50_s0 : List Bool := rkmUnpackMaskHi128T1 [34] [8657043456]
/-- Mask segment `2` for `(m = 128, r = 50)`. -/
def rkmMkHiHiB_m128_r50_s2 : List Bool := rkmUnpackMaskHi128T1 [49] [562949943213280]
/-- Mask segment `3` for `(m = 128, r = 50)`. -/
def rkmMkHiHiB_m128_r50_s3 : List Bool := rkmUnpackMaskHi128T1 [39] [305411061583]
/-- Mask segment `4` for `(m = 128, r = 50)`. -/
def rkmMkHiHiB_m128_r50_s4 : List Bool := rkmUnpackMaskHi128T1 [44] [16120892896876]
/-- Mask segment `5` for `(m = 128, r = 50)`. -/
def rkmMkHiHiB_m128_r50_s5 : List Bool := rkmUnpackMaskHi128T1 [47] [139248613386983]
/-- Mask segment `6` for `(m = 128, r = 50)`. -/
def rkmMkHiHiB_m128_r50_s6 : List Bool := rkmUnpackMaskHi128T1 [49] [480857648571279]
/-- Prefix-kick masks for `(m = 128, r = 50)`. -/
def rkmMasksHiHiB_m128_r50 : List (List Bool) :=
  [rkmMkHiHiB_m128_r50_s0, [], rkmMkHiHiB_m128_r50_s2, rkmMkHiHiB_m128_r50_s3,
   rkmMkHiHiB_m128_r50_s4, rkmMkHiHiB_m128_r50_s5, rkmMkHiHiB_m128_r50_s6, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 50)`. -/
def rkmRowHiHiB_m128_r50 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 100, 0, 0, 26, 307,
   1595, 16297, 3678, 43638, 35062, 9007, 263747, 19343, 18975, 1845095, 47940, 2886635, 94301448,
   1060245, 13520983, 163684953, 483225313, 18332327, 4940164468, 994280517154]
/-- Mask segment `0` for `(m = 128, r = 57)`. -/
def rkmMkHiHiB_m128_r57_s0 : List Bool := rkmUnpackMaskHi128T1 [50] [1117378691727360]
/-- Mask segment `1` for `(m = 128, r = 57)`. -/
def rkmMkHiHiB_m128_r57_s1 : List Bool := rkmUnpackMaskHi128T1 [50, 5] [1125899906780159, 31]
/-- Mask segment `2` for `(m = 128, r = 57)`. -/
def rkmMkHiHiB_m128_r57_s2 : List Bool := rkmUnpackMaskHi128T1 [41] [2105779216611]
/-- Mask segment `3` for `(m = 128, r = 57)`. -/
def rkmMkHiHiB_m128_r57_s3 : List Bool := rkmUnpackMaskHi128T1 [47] [121414775902208]
/-- Mask segment `4` for `(m = 128, r = 57)`. -/
def rkmMkHiHiB_m128_r57_s4 : List Bool := rkmUnpackMaskHi128T1 [50, 2] [678788084444449, 3]
/-- Mask segment `5` for `(m = 128, r = 57)`. -/
def rkmMkHiHiB_m128_r57_s5 : List Bool := rkmUnpackMaskHi128T1 [50, 5] [187849717208661, 25]
/-- Mask segment `6` for `(m = 128, r = 57)`. -/
def rkmMkHiHiB_m128_r57_s6 : List Bool := rkmUnpackMaskHi128T1 [50, 6] [565537311053073, 32]
/-- Prefix-kick masks for `(m = 128, r = 57)`. -/
def rkmMasksHiHiB_m128_r57 : List (List Bool) :=
  [rkmMkHiHiB_m128_r57_s0, rkmMkHiHiB_m128_r57_s1, rkmMkHiHiB_m128_r57_s2, rkmMkHiHiB_m128_r57_s3,
   rkmMkHiHiB_m128_r57_s4, rkmMkHiHiB_m128_r57_s5, rkmMkHiHiB_m128_r57_s6, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 57)`. -/
def rkmRowHiHiB_m128_r57 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 35, 83, 23,
   4, 327, 732, 799, 10006, 0, 262, 8603, 80, 1907, 200990, 40581, 90006, 3447293, 121884, 450652,
   14896569, 3641929, 328665, 103171284, 5316141, 118631205, 830071883, 20317365, 4752752029,
   994146496580]
/-- Mask segment `0` for `(m = 128, r = 64)`. -/
def rkmMkHiHiB_m128_r64_s0 : List Bool := rkmUnpackMaskHi128T1 [48] [140753594482688]
/-- Mask segment `1` for `(m = 128, r = 64)`. -/
def rkmMkHiHiB_m128_r64_s1 : List Bool := rkmUnpackMaskHi128T1 [50, 2] [43188, 3]
/-- Mask segment `2` for `(m = 128, r = 64)`. -/
def rkmMkHiHiB_m128_r64_s2 : List Bool := rkmUnpackMaskHi128T1 [50, 12] [1125188786415711, 4095]
/-- Mask segment `3` for `(m = 128, r = 64)`. -/
def rkmMkHiHiB_m128_r64_s3 : List Bool := rkmUnpackMaskHi128T1 [50, 3] [623494042122340, 7]
/-- Mask segment `4` for `(m = 128, r = 64)`. -/
def rkmMkHiHiB_m128_r64_s4 : List Bool := rkmUnpackMaskHi128T1 [50, 9] [353672723221667, 506]
/-- Mask segment `5` for `(m = 128, r = 64)`. -/
def rkmMkHiHiB_m128_r64_s5 : List Bool := rkmUnpackMaskHi128T1 [50, 11] [56304237890023, 1824]
/-- Mask segment `6` for `(m = 128, r = 64)`. -/
def rkmMkHiHiB_m128_r64_s6 : List Bool := rkmUnpackMaskHi128T1 [50, 13] [456029391279317, 6825]
/-- Prefix-kick masks for `(m = 128, r = 64)`. -/
def rkmMasksHiHiB_m128_r64 : List (List Bool) :=
  [rkmMkHiHiB_m128_r64_s0, rkmMkHiHiB_m128_r64_s1, rkmMkHiHiB_m128_r64_s2, rkmMkHiHiB_m128_r64_s3,
   rkmMkHiHiB_m128_r64_s4, rkmMkHiHiB_m128_r64_s5, rkmMkHiHiB_m128_r64_s6, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 64)`. -/
def rkmRowHiHiB_m128_r64 : List ℕ :=
  [31, 471, 34, 170, 81, 4539, 33628, 455, 5, 1417, 134, 3392, 10763, 30561, 20, 237, 201, 132, 234,
   129, 31, 0, 2, 225, 6, 109, 121, 0, 28, 717, 1038, 59096, 93099, 632, 22123, 6721, 185155, 34922,
   44355, 104608, 120787, 59401, 16995, 127390, 269470, 3887, 63398, 199049, 63586, 3285174,
   1816328, 556425, 62402, 8571700, 24913, 70027999, 11487026, 547125778, 120622962, 172460439,
   1299346947, 16404382, 4677741862, 993068899343]
/-- Mask segment `0` for `(m = 128, r = 96)`. -/
def rkmMkHiHiB_m128_r96_s0 : List Bool := rkmUnpackMaskHi128T1 [46] [70368744177663]
/-- Mask segment `1` for `(m = 128, r = 96)`. -/
def rkmMkHiHiB_m128_r96_s1 : List Bool := rkmUnpackMaskHi128T1 [50, 14] [1125899906842623, 16383]
/-- Mask segment `2` for `(m = 128, r = 96)`. -/
def rkmMkHiHiB_m128_r96_s2 : List Bool := rkmUnpackMaskHi128T1 [22] [4194303]
/-- Mask segment `3` for `(m = 128, r = 96)`. -/
def rkmMkHiHiB_m128_r96_s3 : List Bool :=
  rkmUnpackMaskHi128T1 [50, 36]
    [1125899906842623, 68719476735]
/-- Mask segment `4` for `(m = 128, r = 96)`. -/
def rkmMkHiHiB_m128_r96_s4 : List Bool := rkmUnpackMaskHi128T1 [32] [4294967295]
/-- Mask segment `5` for `(m = 128, r = 96)`. -/
def rkmMkHiHiB_m128_r96_s5 : List Bool := rkmUnpackMaskHi128T1 [38] [274877906943]
/-- Mask segment `6` for `(m = 128, r = 96)`. -/
def rkmMkHiHiB_m128_r96_s6 : List Bool := rkmUnpackMaskHi128T1 [38] [274877906943]
/-- Prefix-kick masks for `(m = 128, r = 96)`. -/
def rkmMasksHiHiB_m128_r96 : List (List Bool) :=
  [rkmMkHiHiB_m128_r96_s0, rkmMkHiHiB_m128_r96_s1, rkmMkHiHiB_m128_r96_s2, rkmMkHiHiB_m128_r96_s3,
   rkmMkHiHiB_m128_r96_s4, rkmMkHiHiB_m128_r96_s5, rkmMkHiHiB_m128_r96_s6, []]
/-- Part `0` of `rkmRowHiHiB_m128_r96`. -/
def rkmRowHiHiB_m128_r96_p0 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24,
   125, 294, 903, 1856, 1809, 344, 37954, 20439, 28883, 20450, 7448, 4, 7136, 19387, 17081, 2870,
   3307, 17930, 14713, 406, 19934, 16, 219240, 1582630, 7056949, 38064236, 156539619, 527769996,
   1604771190, 4255376308, 9795469695, 20026800485, 36492228627]
/-- Part `1` of `rkmRowHiHiB_m128_r96`. -/
def rkmRowHiHiB_m128_r96_p1 : List ℕ :=
  [58992834959, 84976591143, 109740488605, 127062217060, 131658640510, 122292264352, 102156982743,
   76751221608, 51693290697, 31141298513, 16813644085, 8171735485, 3578091492, 1400002053,
   480707695, 141290115, 34570781, 6834137, 1051694, 120710, 8374, 399, 31, 5, 0, 0, 0, 0, 0, 0, 0,
   0]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 96)`. -/
def rkmRowHiHiB_m128_r96 : List ℕ := rkmRowHiHiB_m128_r96_p0 ++ rkmRowHiHiB_m128_r96_p1
/-- Cumulative trajectory lane witness (`FindAllJohnsonRampKickMuxHi128T1`). -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi128T1 : (0 : ℕ) = 0 := rfl
end
public section
private abbrev fN {α : Type} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β := HighDForce.withForcedList xs k
private abbrev bZ : ℕ := 2000000000000000
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := by rw [Nat.add_eq]; exact Nat.add_comm 1 x
private theorem n0m (z : ℕ) : (0 : ℕ) = Nat.mul 0 z := by rw [Nat.mul_eq]; omega
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private theorem nmod (x y : ℕ) : Nat.mod x y = x % y := rfl
private def uConsNat (x : ℕ) (xs : List ℕ) : List ℕ :=
  match Nat.add 1 x with
  | 0 => xs
  | v + 1 =>
    match xs with
    | [] => [v]
    | h :: t => v :: h :: t
private theorem uConsNat_eq (x : ℕ) (xs : List ℕ) : uConsNat x xs = x :: xs := by
  unfold uConsNat; rw [n1a]; cases xs <;> rfl
private def uToNatHb : List ℤ → Option (List ℕ)
  | [] => some []
  | Int.negSucc _ :: _ => none
  | Int.ofNat n :: xs =>
    match uToNatHb xs with
    | some ns => some (uConsNat n ns)
    | none => none
private def uOfNatHb : List ℕ → List ℤ
  | [] => []
  | n :: ns => Int.ofNat n :: uOfNatHb ns
private theorem uToNatHb_sound : ∀ (hb : List ℤ) (ns : List ℕ), uToNatHb hb = some ns →
    hb = uOfNatHb ns
  | [], _, h => by injection h with h'; subst h'; rfl
  | Int.negSucc _ :: _, _, h => by dsimp only [uToNatHb] at h; cases h
  | Int.ofNat n :: xs, _, h => by
    dsimp only [uToNatHb] at h; revert h; cases hxs : uToNatHb xs with
    | none => intro h; dsimp only at h; cases h
    | some ms =>
      intro h; dsimp only at h; injection h with h'; subst h'
      rw [uConsNat_eq, uOfNatHb, uToNatHb_sound xs ms hxs]
private def bConsZ (x : ℤ) (xs : List ℤ) : List ℤ :=
  match x with
  | Int.ofNat v =>
    match xs with
    | [] => [Int.ofNat v]
    | h :: t => Int.ofNat v :: h :: t
  | Int.negSucc v =>
    match xs with
    | [] => [Int.negSucc v]
    | h :: t => Int.negSucc v :: h :: t
private theorem bConsZ_eq (x : ℤ) (xs : List ℤ) : bConsZ x xs = x :: xs := by
  cases x <;> cases xs <;> rfl
private theorem bOfNatF_eq (x : ℕ) : primOfNatForced x = Int.ofNat x := by
  simp [primOfNatForced, Nat.one_add]
private theorem bNegSuccF_eq (x : ℕ) : primNegSuccForced x = Int.negSucc x := by
  simp [primNegSuccForced, Nat.one_add]
private theorem bSub_eq (u z : ℕ) : rkmForcedSubNatNat u z = (u : ℤ) - (z : ℤ) := by
  unfold rkmForcedSubNatNat; rw [bOfNatF_eq, Nat.sub_eq]; cases h : z - u with
  | zero => dsimp only; rw [Nat.sub_eq, Int.ofNat_eq_natCast]; omega
  | succ k => dsimp only; rw [Int.negSucc_eq]; omega
private def bDec (z : ℕ) : List ℕ → List ℤ
  | [] => []
  | u :: us => bConsZ (rkmForcedSubNatNat u z) (bDec z us)
private theorem bDec_nil (z : ℕ) : bDec z [] = [] := rfl
private theorem bDec_cons (z u : ℕ) (us : List ℕ) :
    bDec z (u :: us) = ((u : ℤ) - (z : ℤ)) :: bDec z us := by rw [bDec, bConsZ_eq, bSub_eq]
private theorem bZero_eq (z : ℕ) : ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [Int.ofNat_eq_natCast]; omega
private theorem bMul0 (z : ℕ) : muxRawIntMul (Int.ofNat 0) ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [bZero_eq]; rfl
private def bEnc1 (z : ℕ) : ℤ → Option ℕ
  | Int.ofNat n => some (Nat.add z n)
  | Int.negSucc k =>
    match Nat.sub z (Nat.add k 1) with
    | 0 => none
    | w + 1 => some (Nat.add w 1)
private def bEnc (z : ℕ) : List ℤ → Option (List ℕ)
  | [] => some []
  | x :: xs =>
    match bEnc1 z x with
    | none => none
    | some u =>
      match bEnc z xs with
      | none => none
      | some us => some (uConsNat u us)
private theorem bEnc1_sound (z : ℕ) (x : ℤ) (u : ℕ) (h : bEnc1 z x = some u) :
    ((u : ℤ) - (z : ℤ)) = x := by
  cases x with
  | ofNat n =>
    unfold bEnc1 at h; injection h with h'; subst h'; rw [Nat.add_eq, Int.ofNat_eq_natCast]; omega
  | negSucc k =>
    unfold bEnc1 at h; simp only [Nat.sub_eq, Nat.add_eq] at h; revert h
    cases hz : z - (k + 1) with
    | zero => intro h; dsimp only at h; cases h
    | succ w => intro h; dsimp only at h; injection h with h'; subst h'; rw [Int.negSucc_eq]; omega
private theorem bEnc_sound (z : ℕ) : ∀ (xs : List ℤ) (us : List ℕ), bEnc z xs = some us →
    bDec z us = xs
  | [], _, h => by injection h with h'; subst h'; rfl
  | x :: xs, _, h => by
    dsimp only [bEnc] at h; revert h; cases hx : bEnc1 z x with
    | none => intro h; dsimp only at h; cases h
    | some u =>
      dsimp only; cases hxs : bEnc z xs with
      | none => intro h; dsimp only at h; cases h
      | some ws =>
        intro h; dsimp only at h; injection h with h'; subst h'
        rw [uConsNat_eq, bDec_cons, bEnc1_sound z x u hx, bEnc_sound z xs ws hxs]
private def zTdiv (x : ℤ) (d : ℕ) : ℤ :=
  match x with
  | Int.ofNat m => Int.ofNat (m / d)
  | Int.negSucc k => -(((k + 1) / d : ℕ) : ℤ)
private theorem bNeg_eq : ∀ (n : ℕ), muxRawNegOfNat n = -(n : ℤ)
  | 0 => by dsimp only [muxRawNegOfNat]; rw [Int.ofNat_eq_natCast]; omega
  | k + 1 => by dsimp only [muxRawNegOfNat]; rw [Int.negSucc_eq]; omega
private theorem bTdivNat_eq : ∀ (x : ℤ) (d : ℕ), muxRawIntTdivNat x d = zTdiv x d
  | Int.ofNat _, _ => rfl
  | Int.negSucc _, _ => by dsimp only [muxRawIntTdivNat, zTdiv]; rw [bNeg_eq, ndiv, Nat.add_eq]
private theorem bSubNatTdiv_eq (m n d : ℕ) :
    rkmUltraSubNatTdiv m n d = zTdiv ((m : ℤ) - (n : ℤ)) d := by
  unfold rkmUltraSubNatTdiv; simp only [Nat.sub_eq, ndiv, Nat.add_eq]; cases h : n - m with
  | zero =>
    have hm : (m : ℤ) - (n : ℤ) = Int.ofNat (m - n) := by rw [Int.ofNat_eq_natCast]; omega
    rw [hm]; rfl
  | succ k =>
    dsimp only; have hm : (m : ℤ) - (n : ℤ) = Int.negSucc k := by rw [Int.negSucc_eq]; omega
    rw [hm]; dsimp only [zTdiv]; rw [bNeg_eq]
private theorem bSubTdiv_eq (a b : ℤ) (d : ℕ) : rkmUltraSubTdiv a b d = zTdiv (a - b) d := by
  cases a with
  | ofNat m => cases b with
    | ofNat n => exact bSubNatTdiv_eq m n d
    | negSucc n =>
      have hm : Int.ofNat m - Int.negSucc n = Int.ofNat (m + (n + 1)) := by
        rw [Int.ofNat_eq_natCast, Int.negSucc_eq, Int.ofNat_eq_natCast]; omega
      rw [hm]; rfl
  | negSucc m => cases b with
    | ofNat n =>
      have hm : Int.negSucc m - Int.ofNat n = Int.negSucc (m + n) := by
        rw [Int.negSucc_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]; omega
      dsimp only [rkmUltraSubTdiv]; rw [hm]; dsimp only [zTdiv]; rw [bNeg_eq, ndiv, Nat.add_eq]
      rw [Nat.add_eq]; exact congrArg (fun t : ℕ => -(((t / d : ℕ) : ℤ))) (by omega)
    | negSucc n =>
      dsimp only [rkmUltraSubTdiv]; rw [bSubNatTdiv_eq, Nat.add_eq, Nat.add_eq]
      exact congrArg (fun t => zTdiv t d) (by simp only [Int.negSucc_eq]; omega)
private theorem bMul_eq (a b : ℤ) : muxRawIntMul a b = a * b := by
  cases a <;> cases b <;>
    simp only [muxRawIntMul, bNeg_eq, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast,
      Int.negSucc_eq] <;> push_cast <;> ring
private theorem bForcedAdd_eq (a b : ℤ) : rkmForcedIntAdd a b = a + b := by
  cases a <;> cases b <;>
    simp only [rkmForcedIntAdd, bOfNatF_eq, bNegSuccF_eq, bSub_eq, Nat.add_eq,
      Int.ofNat_eq_natCast, Int.negSucc_eq] <;> omega
private theorem bAddCons_eq (a b : ℤ) (xs : List ℤ) : rkmUltraAddCons a b xs = (a + b) :: xs := by
  unfold rkmUltraAddCons; rw [bForcedAdd_eq]; cases a + b <;> cases xs <;> rfl
private abbrev bStepVal (v P Q d : ℕ) : ℕ :=
  Nat.sub (Nat.add v (Nat.div (Nat.sub P Q) d)) (Nat.div (Nat.sub Q P) d)
private theorem bStepVal_eq (z v P Q d : ℕ) (hv : 0 < bStepVal v P Q d) :
    ((bStepVal v P Q d : ℤ) - (z : ℤ)) = ((v : ℤ) - (z : ℤ)) + zTdiv ((P : ℤ) - (Q : ℤ)) d := by
  rw [← bSubNatTdiv_eq]; unfold bStepVal at hv ⊢; unfold rkmUltraSubNatTdiv
  simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢; revert hv
  cases hd : Q - P with
  | zero =>
    intro _; dsimp only; rw [Nat.zero_div, Nat.sub_zero, Int.ofNat_eq_natCast]; push_cast; ring
  | succ k =>
    intro hv; dsimp only at hv ⊢
    have hpq : P - Q = 0 := by omega
    rw [hpq, Nat.zero_div, Nat.add_zero] at hv ⊢; rw [bNeg_eq]; omega
private abbrev bCV (z d b0 c0 b v c1 : ℕ) : ℕ :=
  bStepVal v (Nat.add (Nat.mul b0 c0) (Nat.mul b z)) (Nat.add (Nat.mul b c1) (Nat.mul b0 z)) d
private theorem bCell_hb (z d b0 c0 b v c1 : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bCV z d b0 c0 b v c1) (ht : bDec z rest = tailZ) :
    bDec z (uConsNat (bCV z d b0 c0 b v c1) rest) =
      rkmUltraAddCons ((v : ℤ) - (z : ℤ))
        (rkmUltraSubTdiv (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
          (muxRawIntMul (Int.ofNat b) ((c1 : ℤ) - (z : ℤ))) d) tailZ := by
  rw [uConsNat_eq, bDec_cons, ht, bAddCons_eq, bSubTdiv_eq, bMul_eq, bMul_eq]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.add (Nat.mul b0 c0) (Nat.mul b z) : ℕ) : ℤ) -
      ((Nat.add (Nat.mul b c1) (Nat.mul b0 z) : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) - (Int.ofNat b) * ((c1 : ℤ) - (z : ℤ)) := by
    simp only [Nat.add_eq, Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  unfold bCV at hv ⊢; rw [bStepVal_eq z v _ _ d hv, hpq]
private theorem bCell_nil (z d b0 c0 v : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bStepVal v (Nat.mul b0 c0) (Nat.mul b0 z) d) (ht : bDec z rest = tailZ) :
    bDec z (uConsNat (bStepVal v (Nat.mul b0 c0) (Nat.mul b0 z) d) rest) =
      rkmUltraAddCons ((v : ℤ) - (z : ℤ))
        (muxRawIntTdivNat (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ))) d) tailZ := by
  rw [uConsNat_eq, bDec_cons, ht, bAddCons_eq, bTdivNat_eq, bMul_eq]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.mul b0 c0 : ℕ) : ℤ) - ((Nat.mul b0 z : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) := by
    simp only [Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  rw [bStepVal_eq z v _ _ d hv, hpq]
private def bAllPos : List ℕ → Bool
  | [] => true
  | x :: xs => cond (Nat.ble x 0) false (bAllPos xs)
private theorem bAllPos_uCons {x : ℕ} {xs : List ℕ} (h : bAllPos (uConsNat x xs) = true) :
    0 < x ∧ bAllPos xs = true := by
  rw [uConsNat_eq] at h
  cases x with
  | zero => exact Bool.noConfusion h
  | succ k => exact ⟨Nat.succ_pos k, h⟩
private def bHeadOr (z : ℕ) : List ℕ → ℕ
  | [] => z
  | x :: _ => x
private def bTailN : List ℕ → List ℕ
  | [] => []
  | _ :: xs => xs
private theorem bHeadOr_eq (z : ℕ) : ∀ (cs : List ℕ),
    ((bHeadOr z cs : ℤ) - (z : ℤ)) = (match bDec z cs with | cn :: _ => cn | [] => Int.ofNat 0)
  | [] => by unfold bHeadOr; rw [bDec_nil, bZero_eq]
  | _ :: _ => by unfold bHeadOr; rw [bDec_cons]
private theorem bTailN_eq (z : ℕ) : ∀ (xs : List ℕ),
    bDec z (bTailN xs) = (match bDec z xs with | _ :: t => t | [] => [])
  | [] => rfl
  | _ :: _ => by unfold bTailN; rw [bDec_cons]
private def bSl (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, b0, c0, bns, vs, cs =>
    match bns with
    | [] => uConsNat (bStepVal (bHeadOr z vs) (Nat.mul b0 c0) (Nat.mul b0 z) d)
        (bSl z d rem 0 z [] (bTailN vs) (bTailN cs))
    | b :: bR =>
      match vs, cs with
      | v :: vT, c :: cT =>
        uConsNat (bCV z d b0 c0 b v (bHeadOr z cT)) (bSl z d rem b c bR vT cT)
      | v :: vT, [] => uConsNat (bCV z d b0 c0 b v z) (bSl z d rem b z bR vT [])
      | [], c :: cT => uConsNat (bCV z d b0 c0 b z (bHeadOr z cT)) (bSl z d rem b c bR [] cT)
      | [], [] => uConsNat (bCV z d b0 c0 b z z) (bSl z d rem b z bR [] [])
private theorem bSl_sound (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bAllPos (bSl z d rem b0 c0 bns vs cs) = true →
      bDec z (bSl z d rem b0 c0 bns vs cs) =
        rkmUltraSlideLoopAux d rem (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
          (uOfNatHb bns) (bDec z vs) (bDec z cs)
  | 0, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs, h => by
    cases bns with
    | nil =>
      dsimp only [bSl, uOfNatHb, rkmUltraSlideLoopAux] at h ⊢; have hp := bAllPos_uCons h
      have hi := bSl_sound z d rem 0 z [] (bTailN vs) (bTailN cs) hp.2
      rw [bMul0, uOfNatHb, bTailN_eq z vs, bTailN_eq z cs] at hi
      have hc := bCell_nil z d b0 c0 (bHeadOr z vs) hp.1 hi; rw [bHeadOr_eq z vs] at hc; exact hc
    | cons b bR =>
      cases vs with
      | nil => cases cs with
        | nil =>
          dsimp only [bSl, uOfNatHb] at h ⊢; rw [bDec_nil, rkmUltraSlideLoopAux]
          have hp := bAllPos_uCons h; have hi := bSl_sound z d rem b z bR [] [] hp.2
          rw [bZero_eq z, bDec_nil] at hi; have hc := bCell_hb z d b0 c0 b z z hp.1 hi
          rw [bZero_eq z] at hc; exact hc
        | cons c cT =>
          dsimp only [bSl, uOfNatHb] at h ⊢; rw [bDec_nil, bDec_cons z c cT]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uCons h
          have hi := bSl_sound z d rem b c bR [] cT hp.2; rw [bDec_nil] at hi
          have hc := bCell_hb z d b0 c0 b z (bHeadOr z cT) hp.1 hi
          rw [bHeadOr_eq z cT, bZero_eq z] at hc; exact hc
      | cons v vT => cases cs with
        | nil =>
          dsimp only [bSl, uOfNatHb] at h ⊢; rw [bDec_cons z v vT, bDec_nil]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uCons h
          have hi := bSl_sound z d rem b z bR vT [] hp.2
          rw [bZero_eq z, bDec_nil] at hi
          have hc := bCell_hb z d b0 c0 b v z hp.1 hi; rw [bZero_eq z] at hc; exact hc
        | cons c cT =>
          dsimp only [bSl, uOfNatHb] at h ⊢; rw [bDec_cons z v vT, bDec_cons z c cT]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uCons h
          have hi := bSl_sound z d rem b c bR vT cT hp.2
          have hc := bCell_hb z d b0 c0 b v (bHeadOr z cT) hp.1 hi
          rw [bHeadOr_eq z cT] at hc; exact hc
private def mkHbZ (z : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: bs => uConsNat b (uConsNat (Nat.mul b z) (mkHbZ z bs))
private def bSlZ (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, p0, q0, hbz, vs, cs =>
    match hbz with
    | [] =>
      uConsNat (bStepVal (bHeadOr z vs) p0 q0 d) (bSlZ z d rem 0 0 [] (bTailN vs) (bTailN cs))
    | [_] => []
    | b :: bz :: bR =>
      match vs, cs with
      | v :: vT, c :: cT =>
        uConsNat (bStepVal v (Nat.add p0 bz) (Nat.add (Nat.mul b (bHeadOr z cT)) q0) d)
          (bSlZ z d rem (Nat.mul b c) bz bR vT cT)
      | v :: vT, [] =>
        uConsNat (bStepVal v (Nat.add p0 bz) (Nat.add bz q0) d) (bSlZ z d rem bz bz bR vT [])
      | [], c :: cT =>
        uConsNat (bStepVal z (Nat.add p0 bz) (Nat.add (Nat.mul b (bHeadOr z cT)) q0) d)
          (bSlZ z d rem (Nat.mul b c) bz bR [] cT)
      | [], [] =>
        uConsNat (bStepVal z (Nat.add p0 bz) (Nat.add bz q0) d) (bSlZ z d rem bz bz bR [] [])
private theorem bSlZ_eq (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bSlZ z d rem (Nat.mul b0 c0) (Nat.mul b0 z) (mkHbZ z bns) vs cs = bSl z d rem b0 c0 bns vs cs
  | 0, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs => by
    cases bns with
    | nil =>
      have hrec := bSlZ_eq z d rem 0 z [] (bTailN vs) (bTailN cs)
      dsimp only [mkHbZ] at hrec; rw [← n0m z] at hrec; dsimp only [mkHbZ, bSlZ, bSl]; rw [hrec]
    | cons b bR =>
      dsimp only [mkHbZ]; rw [uConsNat_eq, uConsNat_eq]; cases vs with
      | nil => cases cs with
        | nil => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b z bR [] []]
        | cons c cT => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b c bR [] cT]
      | cons v vT => cases cs with
        | nil => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b z bR vT []]
        | cons c cT => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b c bR vT cT]
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
    | nil => cases cs with
      | nil => dsimp only [bSlZ]; rw [bSlZ_pfx z d rem l t bz bz [] [] hl]
      | cons c cT => dsimp only [bSlZ]; rw [bSlZ_pfx z d rem l t (Nat.mul b c) bz [] cT hl]
    | cons v vT => cases cs with
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
private theorem fH4_eq {α : Type} (h : HbZ4) (k : HbZ4 → α) : fH4 h k = k h := by
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
private def q4Hd (z : ℕ) : Q4 → ℕ
  | Q4.c4 x _ _ _ _ => x
  | Q4.tail xs => bHeadOr z xs
private theorem q4Hd_eq (z : ℕ) (w : Q4) : q4Hd z w = bHeadOr z (q4L w) := by
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
private def bSlQ4 (z d rT : ℕ) : ℕ → ℕ → ℕ → HbZ4 → Q4 → Q4 → Q4
  | 0, p0, q0, hbz, vs, cs => toQ4 (bSlZ z d rT p0 q0 (takeH4 1 hbz) (q4L vs) (q4L cs))
  | q + 1, p0, q0, hbz, vs, cs =>
    match hbz with
    | HbZ4.tail l =>
      toQ4 (bSlZ z d (Nat.add (Nat.mul 4 (Nat.add q 1)) rT) p0 q0 l (q4L vs) (q4L cs))
    | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR =>
      match vs with
      | Q4.tail vxs =>
        toQ4 (bSlZ z d (Nat.add (Nat.mul 4 (Nat.add q 1)) rT) p0 q0
          (takeH4 (Nat.add q 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR)) vxs (q4L cs))
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
    cases hbz with
    | tail l => dsimp only [bSlQ4, hbz4L]; rw [q4L_toQ4, hrem]
    | c4 b1 z1 b2 z2 b3 z3 b4 z4 bR =>
      cases vs with
      | tail vxs =>
        dsimp only [bSlQ4]; rw [q4L_toQ4, hrem, hq2]
        exact bSlZ_takeH4 z d (q + 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR)
          (4 * (q + 1) + rT) p0 q0 vxs (q4L cs) hle
      | c4 v1 v2 v3 v4 vR =>
        cases cs with
        | tail cxs =>
          dsimp only [bSlQ4]; rw [q4L_toQ4, hrem, hq2]
          exact bSlZ_takeH4 z d (q + 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR)
            (4 * (q + 1) + rT) p0 q0 (v1 :: v2 :: v3 :: v4 :: q4L vR) cxs hle
        | c4 c1 c2 c3 c4 cR =>
          dsimp only [bSlQ4]; rw [n1a (Nat.mul b4 c4)]; dsimp only; rw [q4S_eq, q4Hd_eq]
          have h4 : 4 * (q + 1) + rT = ((((4 * q + rT) + 1) + 1) + 1) + 1 := by omega
          rw [h4]; dsimp only [hbz4L, hbz4C, q4L, bSlZ, bHeadOr]
          rw [uConsNat_eq, uConsNat_eq, uConsNat_eq, uConsNat_eq]
          rw [bSlQ4_eq z d rT hr q (Nat.mul b4 c4) z4 bR vR cR]
private def bStg (z dg mL cL : ℕ) (h4 : HbZ4) (vs cs : Q4) : Option Q4 :=
  fN (rkmNextLen mL cL) fun nL => fN (Nat.div nL 4) fun q4 => fN (Nat.mod nL 4) fun rT =>
    fN (Nat.mul dg wdScale) fun d => bChkV (bSlQ4 z d rT q4 0 0 h4 vs cs)
private theorem bStg_sound (bns : List ℕ) {z dg mL cL : ℕ} {vs cs out : Q4}
    (h : bStg z dg mL cL (toH4 (mkHbZ z bns)) vs cs = some out) :
    bDec z (q4L out) =
      rkmUltraHornerStage dg mL cL (uOfNatHb bns) (bDec z (q4L vs)) (bDec z (q4L cs)) := by
  unfold bStg at h; dsimp only [fN] at h
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceNat_eq, bChkV_eq] at h
  have hr : Nat.mod (rkmNextLen mL cL) 4 ≤ 4 := by rw [nmod]; omega
  have hqr : 4 * Nat.div (rkmNextLen mL cL) 4 + Nat.mod (rkmNextLen mL cL) 4 =
      rkmNextLen mL cL := by rw [ndiv, nmod]; omega
  have hsl := bSlZ_eq z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z bns (q4L vs) (q4L cs)
  rw [← n0m z] at hsl
  have heq : q4L (bSlQ4 z (Nat.mul dg wdScale) (Nat.mod (rkmNextLen mL cL) 4)
      (Nat.div (rkmNextLen mL cL) 4) 0 0 (toH4 (mkHbZ z bns)) vs cs) =
      bSl z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z bns (q4L vs) (q4L cs) := by
    rw [bSlQ4_eq _ _ _ hr, hqr, hbz4L_toH4, hsl]
  revert h
  cases hv : q4AP (bSlQ4 z (Nat.mul dg wdScale) (Nat.mod (rkmNextLen mL cL) 4)
      (Nat.div (rkmNextLen mL cL) 4) 0 0 (toH4 (mkHbZ z bns)) vs cs) with
  | false => intro h; dsimp only [cond] at h; cases h
  | true =>
    intro h; dsimp only [cond] at h; injection h with h'
    have hp := q4AP_pos _ hv
    rw [heq] at hp; rw [← h', heq]
    unfold rkmUltraHornerStage; rw [rkmb_forceNat_eq, rkmb_forceNat_eq, ← bMul0 z]
    exact bSl_sound z _ _ 0 z bns (q4L vs) (q4L cs) hp
private def bBind (z dg mL cL : ℕ) (h4 : HbZ4) (vs cs : Q4)
    (k : ℕ → Q4 → Option Q4) : Option Q4 :=
  fN (rkmNextLen mL cL) fun nL =>
    match bStg z dg mL cL h4 vs cs with
    | none => none
    | some out => k nL out
private theorem bBind_sound (bns : List ℕ) {z dg mL cL : ℕ} {vs cs out : Q4}
    {kB : ℕ → Q4 → Option Q4} {kU : ℕ → List ℤ → List ℤ}
    (h : bBind z dg mL cL (toH4 (mkHbZ z bns)) vs cs kB = some out)
    (hk : ∀ (mid : Q4), kB (rkmNextLen mL cL) mid = some out →
      bDec z (q4L out) = kU (rkmNextLen mL cL) (bDec z (q4L mid))) :
    bDec z (q4L out) = (HighDForce.withForcedNat (rkmNextLen mL cL) fun nL =>
      HighDForce.withForcedList
        (rkmUltraHornerStage dg mL cL (uOfNatHb bns) (bDec z (q4L vs)) (bDec z (q4L cs)))
        (kU nL)) := by
  unfold bBind at h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h
  revert h; cases hs : bStg z dg mL cL (toH4 (mkHbZ z bns)) vs cs with
  | none => intro h; dsimp only at h; cases h
  | some mid =>
    intro h; rw [rkmb_forceNat_eq, rkmb_forceList_eq, ← bStg_sound bns hs]
    exact hk mid h
private def bStep (z mL c : ℕ) (h4 : HbZ4) (vs : Q4) : Option Q4 :=
  bBind z 16 mL c h4 vs vs fun l1 c1 => bBind z 15 mL l1 h4 vs c1 fun l2 c2 =>
  bBind z 14 mL l2 h4 vs c2 fun l3 c3 => bBind z 13 mL l3 h4 vs c3 fun l4 c4 =>
  bBind z 12 mL l4 h4 vs c4 fun l5 c5 => bBind z 11 mL l5 h4 vs c5 fun l6 c6 =>
  bBind z 10 mL l6 h4 vs c6 fun l7 c7 => bBind z 9 mL l7 h4 vs c7 fun l8 c8 =>
  bBind z 8 mL l8 h4 vs c8 fun l9 c9 => bBind z 7 mL l9 h4 vs c9 fun la ca =>
  bBind z 6 mL la h4 vs ca fun lb cb => bBind z 5 mL lb h4 vs cb fun lc cc =>
  bBind z 4 mL lc h4 vs cc fun ld cd => bBind z 3 mL ld h4 vs cd fun le ce =>
  bBind z 2 mL le h4 vs ce fun lf cf => bStg z 1 mL lf h4 vs cf
private theorem bStep_sound (bns : List ℕ) {z mL cL : ℕ} {vs out : Q4}
    (h : bStep z mL cL (toH4 (mkHbZ z bns)) vs = some out) :
    bDec z (q4L out) = rkmUltraHornerT16Step mL cL (uOfNatHb bns) (bDec z (q4L vs)) := by
  unfold bStep at h; unfold rkmUltraHornerT16Step
  refine bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => ?_
  refine bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => ?_
  refine bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => ?_
  refine bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => ?_
  refine bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => ?_
  exact bStg_sound bns h
private def bIter (z : ℕ) : ℕ → ℕ → ℕ → HbZ4 → Q4 → Option Q4
  | 0, _, _, _, vs => some vs
  | k + 1, mL, cL, h4, vs =>
    match bStep z mL cL h4 vs with
    | none => none
    | some vNext => fN (rkmNextLen16 mL cL) fun nL => bIter z k mL nL h4 vNext
private theorem bIter_sound (bns : List ℕ) (z : ℕ) : ∀ (k mL cL : ℕ) (vs out : Q4),
    bIter z k mL cL (toH4 (mkHbZ z bns)) vs = some out →
    bDec z (q4L out) = muxUltraIterFullT16Rkm k mL cL (uOfNatHb bns) (bDec z (q4L vs))
  | 0, _, _, _, _, h => by injection h with h'; rw [← h']; rfl
  | k + 1, mL, cL, vs, out, h => by
    unfold bIter at h; revert h; cases hs : bStep z mL cL (toH4 (mkHbZ z bns)) vs with
    | none => intro h; dsimp only at h; cases h
    | some vNext =>
      intro h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h; unfold muxUltraIterFullT16Rkm
      rw [rkmb_forceList_eq, rkmb_forceNat_eq, ← bStep_sound bns hs]
      exact bIter_sound bns z k mL (rkmNextLen16 mL cL) vNext out h
private def fQ4 {α : Type} (v : Q4) (k : Q4 → α) : α :=
  match v with
  | Q4.tail xs => k (Q4.tail xs)
  | Q4.c4 x1 x2 x3 x4 r => k (Q4.c4 x1 x2 x3 x4 r)
private theorem fQ4_eq {α : Type} (v : Q4) (k : Q4 → α) : fQ4 v k = k v := by
  cases v <;> rfl
private def fIter (k mL cL : ℕ) (hb v : List ℤ) : List ℤ :=
  match uToNatHb hb with
  | none => muxUltraIterFullT16Rkm k mL cL hb v
  | some bns =>
    match bEnc bZ v with
    | none => muxUltraIterFullT16Rkm k mL cL hb v
    | some vns =>
      fH4 (toH4 (mkHbZ bZ bns)) fun h4 =>
        fQ4 (toQ4 vns) fun vs0 =>
          match bIter bZ k mL cL h4 vs0 with
          | none => muxUltraIterFullT16Rkm k mL cL hb v
          | some out => bDec bZ (q4L out)
private theorem fIter_eq (k mL cL : ℕ) (hb v : List ℤ) :
    fIter k mL cL hb v = muxUltraIterFullT16Rkm k mL cL hb v := by
  unfold fIter; cases hh : uToNatHb hb with
  | none => rfl
  | some bns =>
    dsimp only; cases hv : bEnc bZ v with
    | none => rfl
    | some vns =>
      dsimp only; rw [fH4_eq, fQ4_eq]
      cases hi : bIter bZ k mL cL (toH4 (mkHbZ bZ bns)) (toQ4 vns) with
      | none => rfl
      | some out =>
        dsimp only; rw [bIter_sound bns bZ k mL cL (toQ4 vns) out hi,
          q4L_toQ4, ← uToNatHb_sound hb bns hh, bEnc_sound bZ v vns hv]
private def bSlideChk (steps maxLen : ℕ) (hb vecIn vecOut : List ℤ) : Bool :=
  fL hb fun hbF => fL vecIn fun inF => fL vecOut fun outF =>
    fN (altIntLen inF) fun len0 => muxIntListEq (fIter steps maxLen len0 hbF inF) outF
private theorem bSlideChk_sound {steps maxLen : ℕ} {hb vecIn vecOut : List ℤ}
    (h : bSlideChk steps maxLen hb vecIn vecOut = true) :
    muxFastIterFullT16 steps maxLen hb vecIn = vecOut := by
  unfold bSlideChk at h; dsimp only [fL, fN] at h
  rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceNat_eq, fIter_eq] at h
  have h2 : muxUltraIterFullT16HiChk steps 0 maxLen hb vecIn vecOut = true := by
    unfold muxUltraIterFullT16HiChk; dsimp only
    rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceNat_eq]; exact h
  exact muxUltraIterFullT16HiChk_sound h2
private theorem bCh (c : ℕ) {a b m : ℕ} {hb vi vm vo : List ℤ}
    (h1 : muxFastIterFullT16 a m hb vi = vm) (h2 : bSlideChk b m hb vm vo = true)
    (hc : a + b = c) : muxFastIterFullT16 c m hb vi = vo :=
  Eq.mp (congrArg (fun k => muxFastIterFullT16 k m hb vi = vo) hc)
    ((muxFastIterFullT16_add a b m hb vi).trans
      ((congrArg (muxFastIterFullT16 b m hb) h1).trans (bSlideChk_sound h2)))
private theorem rkmHd {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : b = true := (rkmAllTrueF_cons h).1
private theorem rkmTl {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : rkmAllTrueF bs = true := (rkmAllTrueF_cons h).2
private def pzeros : ℕ → List ℤ
  | 0 => []
  | k + 1 => Int.ofNat 0 :: pzeros k
private def pzig : List ℕ → List ℤ
  | [] => []
  | w :: ws =>
    (match Nat.mod w 2 with
      | 0 => primOfNatForced (Nat.div w 2)
      | _ => primNegSuccForced (Nat.div w 2)) :: pzig ws
private def pzigCatZ (z : ℕ) : List (List ℕ) → List ℤ
  | [] => pzeros z
  | ws :: wss => pzig ws ++ pzigCatZ z wss
private def pvi0 : List ℤ := [rkmP 1000000000000000]
private theorem bDm {a b : ℕ} (h : muxNatListEq [a] [b] = true) : a = b :=
  (List.cons.inj (muxNatListEq_eq_true.mp h)).1
private theorem rkmTl4 {a b c d : Bool} {bs : List Bool}
    (h : rkmAllTrueF (a :: b :: c :: d :: bs) = true) : rkmAllTrueF bs = true :=
  rkmTl (rkmTl (rkmTl (rkmTl h)))
private def phbv_g0 : List ℤ := pzigCatZ 0
 [
 [346593141884776,481771275016964,579722734613190,657418931524640,721536798554274,775547375850062,
  821536959500034,860878194238624,894531600000000,923199714477448,947413445276808,967583865396852,
  984034956901448,997025174462560,1006762099822086,1013412630925788,1017110164089920,
  1017959667423584,1016041209339424,1011412295929334,1004109230652812,994147607746956,
  981521967056852,966204557688650,948143066829136,927257050761190,903432631172092,876514746341666,
  846295790718350,812498674647418,774750847718604,732542891123736,685159042067718,631552480441696,
  570100112215656,498054116390532,410046354703312,292237319898972]]
private def pvo_r38_0 : List ℤ := pzigCatZ 20
 [
 [1746820774394898,910941264209548,330149925693762,95986037558460,23734272388656,5152736198064,
  1001973785500,176902779794,28636733212,4281555830,594579728,77029598,9342292,1063642,113928,
  11498,1092,96,6]]
private def phbv_g1 : List ℤ := pzigCatZ 0
 [
 [429109470127026,596470592062894,717742174924964,813936155297034,893319099221262,960188426405916,
  1017127134898778,1065834666447198,1107500220000000,1142993592275232,1172972088493042,
  1197944649239294,1218312389697630,1234395297005520,1246450373626400,1254684252295938,
  1259262088107142,1260313839804816,1257938638358306,1252207680815794,1243165913705028,
  1230832643913562,1215201111341732,1196236958208276,1173875417150990,1148016892544176,
  1118520394112708,1085193943295730,1047780508151582,1005937029973814,959202262159930,
  906945504305240,848280585979286,781911461854142,705828614328284,616630025674240,507669520052860,
  361812702961330]]
private def pvi_r38_1 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r38_s0 pvo_r38_0
private def pvo_r38_1 : List ℤ := pzigCatZ 12
 [
 [766057039023580,1077354959322926,1059395782054762,823946933101738,554444716604626,
  328417986943332,170129711421366,77120688875478,30927249900792,11154843690890,3684012594276,
  1132358891448,327884923078,90001594570,23421419090,5750731202,1321912854,281865908,55180826,
  9798492,1551996,213250,23978,1838,9,33,5]]
private def phbv_g2 : List ℤ := pzigCatZ 0
 [
 [433644933536922,602774975288410,725328335563990,822539036163882,902761016424064,970337117538924,
  1027877638499126,1077099983265392,1119205919999520,1155074438717456,1185369792012876,
  1210606299708334,1231189316565868,1247442211820188,1259624704316790,1267945610791648,
  1272571831941010,1273634700105862,1271234394018226,1265442863241966,1256305529366198,
  1243841903342212,1228045153619618,1208880559273316,1186282668383844,1160150832651658,
  1130342571607922,1096663877578466,1058855001927996,1016569259998366,969340530050932,
  916531445506508,857246469575128,790175858405368,713288854842190,623147483604170,513035322238108,
  365636874623238]]
private def pvi_r38_2 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r38_s1 pvo_r38_1
private def pvo_r38_2 : List ℤ := pzigCatZ 7
 [
 [245337264370666,512729628135032,771630253355394,896632261964238,950088278949940,752623713267662,
  659455257183044,531111047091342,285191153495210,99017417009106,18048685355008,2414650396785,
  3445883341655,1638375249449,556754093937,153905166939,36415352759,7575588853,1408307655,
  236802465,36185551,4897529,670073,260083,182701,98137,39041,12137,3065,643,111,15]]
private def phbv_g3 : List ℤ := pzigCatZ 0
 [
 [325057251923596,451835964962062,543701118741820,616569589582326,676703432804142,727358012219946,
  770489989953482,807386720171122,838949040000000,865835834294874,888545022219528,907462134366386,
  922891021869894,935074080078554,944205992448028,950443286563676,953911070036522,954707788683748,
  952908535792082,948567244258460,941717961792872,932375313669864,920534179006374,906168531236366,
  889229308052346,869641064183010,847296997251412,822051680442796,793710407971280,762013307407724,
  726610977111048,687025651488536,642586042337724,592310374699094,534676407012582,467107056714244,
  384567739847136,274078879920414]]
private def pvi_r38_3 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r38_s2 pvo_r38_2
private def pvo_r38_3 : List ℤ := pzigCatZ 6
 [
 [172483144772268,386689732311682,642153369663936,795370295710312,944446237208278,823592224558542,
  718283411137798,647551849067722,453051887790528,248803687105602,54322439557048,9612318203162,
  2241123802373,167738228727,743309854146,456690440072,169391597300,49042292756,12081262914,
  2666242826,460750420,62012018,7624894,1350324,67460,33892,55230,30746,11122,3104,710,136,18]]
private def phbv_g4 : List ℤ := pzigCatZ 0
 [
 [308429272945692,428722747575310,515888631190160,585029588203126,642087344750868,690150739762460,
  731076344265482,766085659110042,796033440000000,821544867193626,843092389297314,861041815471196,
  875681453648492,887241299685816,895906078201148,901824309767598,905114702241334,905870665542112,
  904163451634600,900044234532268,893545320268520,884680585976594,873445172727082,859814385316934,
  843741671171982,825155444348400,803954365838134,780000447989856,753108944997638,723033277946832,
  689441918488242,651881540650742,609715195309222,562011329221388,507325569573410,443212661885298,
  364895561312688,260058648633050]]
private def pvi_r38_4 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r38_s3 pvo_r38_3
private def pvo_r38_4 : List ℤ := pzigCatZ 4
 [
 [83891302975076,199390206257014,416920612142126,551088549956038,788945159634626,866423976333018,
  788694918065944,758995542327920,674532523018564,557877519904234,335494820010078,151439749207060,
  50762310488934,12108540253730,3089408668730,566456653006,106420353672,14166018614,1689708278,
  758130044,354603997,562216315,283178621,87833279,19814937,3511221,543253,112547,44425,19689,
  7251,2159,525,101,11]]
private def phbv_g5 : List ℤ := pzigCatZ 0
 [
 [342350015297176,475873245716528,572625545859548,649370556036382,712703467469796,766052826498860,
  811479387972236,850338992179416,883580400000000,911897548390542,935814845381718,955738331458494,
  971988022371668,984819208691676,994436930864866,1001006043608142,1004658310148728,
  1005497413535752,1003602441953544,999030197482302,991816539140602,981976870254890,
  969505797515572,954375909765916,936535534626294,915905213202522,892372461323994,865784115595768,
  835935112053320,802551753280080,765266049771236,723574819219654,676771061473750,623820771999184,
  563120727307514,491956746281508,405026409472058,288659638196418]]
private def pvi_r38_5 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r38_s4 pvo_r38_4
private def pvo_r38_5 : List ℤ := pzigCatZ 3
 [
 [56455282897324,124384971538796,316162097092498,422163085782670,644760680224442,817514526653262,
  799643429676696,782451391013350,728385984098494,675060286531124,513612420623552,303702517785268,
  154751432313766,34322234625118,6529232301858,877408213820,120113955536,18016208288,750816105,
  603520013,95037324,492601738,551902948,114603972,18142470,7883744,3076726,828734,195536,54784,
  18824,6382,1872,456,86,10]]
private def phbv_g6 : List ℤ := pzigCatZ 0
 [
 [173803598067500,241590415171436,290709437034388,329671196363892,361823927169710,388908227270580,
  411970296729094,431698465938680,448574400000000,462950395494014,475092682882278,485207400018148,
  493457011883194,499971123903770,504853830619770,508188825157162,510043000818012,510468995213510,
  509506959681140,507185731391852,503523515183306,498528130986682,492196840736926,484515728390646,
  475458561013428,464984999066516,453037936802280,439539616522618,424385931747978,407437932299720,
  388508797973000,367343074140808,343581832324426,316700131088320,285884049011874,249755655839784,
  205623029452760,146546170567132]]
private def pvi_r38_6 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r38_s5 pvo_r38_5
private def pvo_r38_6 : List ℤ := pzigCatZ 2
 [
 [47025952931052,93375963689342,272133961822198,365094567697122,565572580566632,772043454827542,
  792603902518352,787781159386008,742111103683192,711894398588342,592138070010356,389380392389076,
  225240043717190,77867441395248,20158589307540,2251127504958,224096984582,9445907916,673750831,
  743992141,35352382,328150697,609379579,250235849,59650717,15564537,5345021,1685675,446473,
  114659,33603,10827,3301,867,183,27,1]]
private def phbv_g7 : List ℤ := pzigCatZ 0
 [
 [278818191415282,387562762625928,466360192553686,528863198195666,580443063929280,623892081405550,
  660888579569066,692536787777134,719609400000000,742671575397994,762150404644818,778376577001762,
  791610721091212,802060751772098,809893658978298,815243704406784,818218199239300,818901585476560,
  817358274462318,813634527194266,807759548130588,799745882115538,789589136706408,777266987589476,
  762737351520140,745935515239516,726769868899176,705115672499526,680805916952914,653617696416564,
  623251311274276,589296957598610,551178837245018,508054831734464,458619236806660,400661557247748,
  329863373502106,235091440514910]]
private def pvi_r38_7 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r38_s6 pvo_r38_6
private def pvo_r38_7 : List ℤ := pzigCatZ 1
 [
 [31899860575606,21793581883380,158055243286700,221751399880376,386613680466056,276544966055630,
  1525062921242822,166403783823157,96862389763565,414218068140902,659289559838770,616546136905858,
  483583119564490,300289215925686,147077639435876,56363323256486,17133001115126,4230354007038,
  866774864744,150433894718,22751000254,3209822774,43752164,472798197,332580093,144179225,
  49062747,14972381,4366537,1213275,332511,72249,7519,1550,978,270,46,4]]
private abbrev pl_r38 : List ℕ := [1, 1, 1, 1, 1, 1, 1, 1]
private abbrev ptau_r38 : List ℕ :=
  [3727215, 6152779, 4663358, 1165207, 2211204, 1227195, 623020, 1998915]
private abbrev pnsub_r38 : List ℕ := [3, 4, 3, 1, 2, 1, 1, 2]
private def pwalks_r38 : List RkmSegWalk := [ ⟨phbv_g0, pvi0, pvo_r38_0⟩,
  ⟨phbv_g1, pvi_r38_1, pvo_r38_1⟩, ⟨phbv_g2, pvi_r38_2, pvo_r38_2⟩,
  ⟨phbv_g3, pvi_r38_3, pvo_r38_3⟩, ⟨phbv_g4, pvi_r38_4, pvo_r38_4⟩,
  ⟨phbv_g5, pvi_r38_5, pvo_r38_5⟩, ⟨phbv_g6, pvi_r38_6, pvo_r38_6⟩,
  ⟨phbv_g7, pvi_r38_7, pvo_r38_7⟩]
private def phbv_g8 : List ℤ := pzigCatZ 0
 [
 [451315376630852,628492201947382,757738497600000,861044779475606,947053793102266,
  1020256315646282,1083351879396462,1138118146997926,1185801336644554,1227315757882764,
  1263355607013888,1294462075626672,1321065853961732,1343515225126476,1362095286216856,
  1377041470267212,1388549272089614,1396781362224728,1401872848698636,1403935185744068,
  1403059062899070,1399316498554498,1392762286885490,1383434892751980,1371356847008034,
  1356534658752348,1338958226657842,1318599694152990,1295411647709996,1269324496774274,
  1240242787221680,1208040070123750,1172551743842580,1133564955666810,1090804086798766,
  1043909348430556,992404161204892,935643321279306,872726153351384,802340673288490,
  722457106707786,629642023987932,517186593600000,367777036104598]]
private def pvo_r44_0 : List ℤ := pzigCatZ 18
 [
 [1053881917298750,1204678432927442,958715422749230,613177391534868,334194929138908,
  160251514031746,68977508530184,27019419659008,9727922314318,3243291262370,1007136703334,
  292628925530,79849278066,20523315956,4980893876,1143716826,248880196,51392210,10080856,1879950,
  333506,56302,9044,1380,198,26,2]]
private def phbv_g9 : List ℤ := pzigCatZ 0
 [
 [373261034767182,519795384312524,626688720000000,712128329788388,783262208862600,843804460970922,
  895987738195872,941282258998294,980718709937254,1015053272045048,1044860081376386,
  1070586731217208,1092589424553720,1111156209433462,1126522875821844,1138884138950308,
  1148401683085834,1155210045134270,1159420966383934,1161126625219144,1160402026553464,
  1157306733301180,1151886063064060,1144171828260128,1134182663064816,1121923950837608,
  1107387337261340,1090549783518256,1071372076181640,1049796660282704,1025744590350066,
  999111286614616,969760615053742,937516535524760,902151097102564,863366735933384,820769296370732,
  773825161643836,721789426941614,663577013890264,597509194651754,520746346293606,427739920000000,
  304170529452830]]
private def pvi_r44_1 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r44_s0 pvo_r44_0
private def pvo_r44_1 : List ℤ := pzigCatZ 13
 [
 [470988226495140,818888724989844,991984816590484,961027904225318,809344104557262,562512812757442,
  395850748745448,244356708138026,105765484541662,30098992514072,4753058269188,482209120013,
  852841696175,566755283951,307553470925,140685814499,54064624777,17589660475,4913649431,
  1203148895,267644963,57578463,12973523,3189367,823511,207975,48741,10307,1937,319,45,3]]
private def phbv_g10 : List ℤ := pzigCatZ 0
 [
 [417072198201382,580805879417276,700245719999784,795713723752540,875196875082756,942845217178334,
  1001153457563344,1051764380209818,1095829647543794,1134194196636124,1167499552221780,
  1196245843428312,1220831082232930,1241577126052254,1258747440477458,1272559595257424,
  1283194252198132,1290801739348412,1295506913525366,1297412772464612,1296603124711004,
  1293144524319958,1287087608004194,1278467922134426,1267306288054928,1253608720991950,
  1237365886048198,1218552040246312,1197123367520444,1173015557441388,1146140398387202,
  1116381035636580,1083585356563848,1047556658479890,1008040234933828,964703595793996,
  917106321765038,864652163308822,806508783111592,741463742744394,667641275265668,581868459667860,
  477945491428424,339872259707200]]
private def pvi_r44_2 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r44_s1 pvo_r44_1
private def pvo_r44_2 : List ℤ := pzigCatZ 3
 [
 [20746330120948,20701629721292,104074458031958,176157191547682,315121947976174,426278882918940,
  572956713457328,725462001495688,785412906849764,759103637017480,712149717229904,660332553276270,
  576725158233260,452740152002378,313294556758530,190683576215842,102329211822872,48437876906448,
  20131712189948,7263164964172,2226599937772,559369104462,110839725518,21482790008,11032714914,
  9582893886,6897061988,4000283744,1955687440,830505824,311724480,104475760,31465248,8552876,
  2105608,471042,96066,17912,3054,472,64,6]]
private def phbv_g11 : List ℤ := pzigCatZ 0
 [
 [300186608628,418033491480,504000000000,572712842530,629920629920,678610344748,720577546138,
  757004623498,788720482806,816333265278,840304706638,860994773502,878689933934,893621843958,
  905980132232,915921394006,923575660138,929051128840,932437665476,933809402394,933226660570,
  930737342110,926377892654,920173896608,912140340078,902281552510,890590815132,877049599508,
  861626369140,844274836768,824931512308,803512289886,779907686844,753976126942,725534285888,
  694342854790,660084843030,622331101584,580482557876,533666562564,480533037364,418798280798,
  344000000000,244622157622]]
private def pvi_r44_3 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r44_s2 pvo_r44_2
private def pvo_r44_3 : List ℤ := pzigCatZ 3
 [
 [20749435430955,20676766485138,104034398873140,176093188070378,315038136608198,426183733256310,
  572839976498202,725371134427192,785388114648490,759122685390382,712182110919126,660383474415876,
  576810506616900,452853542722102,313410472040092,190778633914932,102438918438346,48399942875655,
  20105832197264,7271504373128,2229731851472,560357156612,111090304560,21539262496,11027188011,
  9580973622,6890957005,4004210767,1953574410,831216248,312032100,104591748,31503906,8564358,
  2108662,471772,96222,17942,3058,472,64,6]]
private def phbv_g12 : List ℤ := pzigCatZ 0
 [
 [397799789089536,553967532073658,667888200000000,758944741101088,834755070755488,899277463602406,
  954891349705022,1003163601946282,1045192665804348,1081784434815226,1113550789620608,
  1140968748977236,1164417933203296,1184205327067860,1200582221731188,1213756133303424,
  1223899375423844,1231155329661346,1235643083348342,1237460874817866,1236688639921818,
  1233389857332052,1227612823899146,1219391443438406,1208745575164600,1195680956347544,
  1180188683444422,1162244203030172,1141805723727114,1118811906814322,1093178616823746,
  1064794398751458,1033514168914892,999150314021718,961459897302534,920125792598316,
  874727931864348,824697617542902,769240973635310,707201587047144,636790367791222,554981011757500,
  455860200000000,324167167727700]]
private def pvi_r44_4 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r44_s3 pvo_r44_3
private def pvo_r44_4 : List ℤ := pzigCatZ 2
 [
 [18671892227458,2131904572106,60934921966284,103350150931718,214033261504976,312404383101376,
  424132392526034,583173348760464,715840673646246,759958954602576,742353852513392,709965157691554,
  665103968510690,585388723549050,467036834759308,332498207502186,210785627126000,119017808112356,
  59918874512914,26892696643902,10707912393056,3738942684308,1154791843400,280647491812,
  32861878546,10388270962,2885065203,566927851,2859610118,945532276,303944137,103578239,32382879,
  4634279,2588916,1738594,576994,140070,27988,4830,728,92,8]]
private def phbv_g13 : List ℤ := pzigCatZ 0
 [
 [328406851519274,457332401981904,551380536000000,626553004144554,689138838419182,742405824648220,
  788318320674206,828169871150338,862867306675682,893075939213892,919300911805648,941936031165572,
  961294695935108,977630339887322,991150418483534,1002026248336366,1010400084372302,
  1016390296411780,1020095197970710,1021595890503984,1020958365704324,1018235028905600,
  1013465751965650,1006678524454964,997889741309826,987104138979998,974314367073290,
  959500155309928,942627002478144,923644269897960,902482498849382,879049676747360,853226028577668,
  824856668660808,793741038570790,759617332227586,722138759040114,680835826113904,635053142661000,
  583836022445230,525707467675518,458169088378374,376339096000000,267618842038684]]
private def pvi_r44_5 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r44_s4 pvo_r44_4
private def pvo_r44_5 : List ℤ := pzigCatZ 0
 [
 [15001609210015,21262895373099,21015667259012,32297366376166,89337225810878,172503268185540,
  241786969452690,337029969768880,482829422085206,626036318447556,707368431142130,726946884977760,
  721514195724894,692020821529948,685687288119238,482831084737670,595981682984702,254501057228932,
  104396828004118,22714616641210,5748588482790,822390333588,122953722468,53859549118,7717064970,
  6830429083,10211801339,4037536313,1985023133,2590542477,1373469169,484941495,116894179,19319391,
  1506843,1816684,1783082,924994,330450,89080,18956,3242,440,42,2]]
private def phbv_g14 : List ℤ := pzigCatZ 0
 [
 [277270362925984,386120814741566,465524640000000,528991944132232,581832489032778,626805231030618,
  665568656266938,699214890541780,728509561149918,754014383806992,776155845334366,795266432494058,
  811610744379088,825402752390816,836817608937860,845999954788642,853069894243392,858127365664912,
  861255374094386,862522392615518,861984137302762,859684853414320,855658204329756,849927821341572,
  842507546517654,833401378791460,822603112306128,810095633083062,795849812121256,779822895729330,
  761956240659098,742172161677342,720369534031300,696417589412190,670146998503940,641336721256710,
  609693966114530,574822345290000,536168519409126,492926457178836,443849145293292,386827220042584,
  317739040000000,225947702109810]]
private def pvi_r44_6 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r44_s5 pvo_r44_5
private def pvo_r44_6 : List ℤ := pzigCatZ 0
 [
 [12256572770397,17832188301963,34761183544327,53510758142162,113872081626435,75627696328290,
  181880479169150,257771583552188,375982493627422,526016987521568,646832351247688,702631882556024,
  725830196148734,686650468101438,761836341881184,519080306661712,655629390528712,453111428523452,
  235267960133716,87583856590284,27187576697240,5263669642966,770307568066,47247216850,790407832,
  10129429553,7392477370,893927782,3497762991,1730241142,254331179,704624451,334874769,96131157,
  19672805,1595601,1628180,1340342,620864,206338,52534,10490,1636,188,12]]
private def phbv_g15 : List ℤ := pzigCatZ 0
 [
 [338347831250622,471175999085798,568071000000000,645518962637814,709999289999644,764878684824920,
  812180966692152,853238836262156,888986574184334,920109631626850,947128442470712,970448734084906,
  990393391787324,1007223520871856,1021152856542544,1032357901220308,1040985215933444,
  1047156753594464,1050973803700644,1052519922673674,1051863099795786,1049057326726952,
  1044143682258816,1037151003215056,1028096180811892,1016984094872922,1003807172507250,
  988544529847290,971160621318636,951603275392376,929800930810998,905658789739270,879053451535228,
  849825342080652,817767831982280,782611190206860,743998128701946,701444942873992,654276403047672,
  601508924331134,541620799740924,472038012245306,387731000000000,275719749410520]]
private def pvi_r44_7 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r44_s6 pvo_r44_6
private def pvo_r44_7 : List ℤ := pzigCatZ 0
 [
 [6896464672221,4455238806155,19239638873017,21790537290035,18716641763480,134044173876097,
  135136372663297,23179076351319,84525168429708,158085653651446,306934098111964,360903648524762,
  635211811549256,527082666914174,727166167102762,734149294247300,650474662766202,663537744852750,
  695107659418270,595825727970598,424224135899522,245096242651660,112971039742346,41952956197288,
  12806258404226,3292921229476,728917804930,143819990576,23342451318,28941955,877493093,345962963,
  180424569,41926013,18922651,24611485,15791241,5006075,68947,831788,517964,194702,51626,9688,
  1144]]
private abbrev pl_r44 : List ℕ := [1, 1, 1, 1, 1, 1, 1, 1]
private abbrev ptau_r44 : List ℕ :=
  [7517247, 3730290, 9725635, 1000, 1325175, 2188018, 923660, 3381375]
private abbrev pnsub_r44 : List ℕ := [5, 3, 7, 1, 1, 2, 1, 3]
private def pwalks_r44 : List RkmSegWalk := [ ⟨phbv_g8, pvi0, pvo_r44_0⟩,
  ⟨phbv_g9, pvi_r44_1, pvo_r44_1⟩, ⟨phbv_g10, pvi_r44_2, pvo_r44_2⟩,
  ⟨phbv_g11, pvi_r44_3, pvo_r44_3⟩, ⟨phbv_g12, pvi_r44_4, pvo_r44_4⟩,
  ⟨phbv_g13, pvi_r44_5, pvo_r44_5⟩, ⟨phbv_g14, pvi_r44_6, pvo_r44_6⟩,
  ⟨phbv_g15, pvi_r44_7, pvo_r44_7⟩]
private def phbv_g16 : List ℤ := pzigCatZ 0
 [
 [431159862856960,601261279137850,725963618582632,826194442389184,910171219787064,982161205575698,
  1044728907426764,1099563321644066,1147849266569428,1190457093532094,1228048955370378,
  1261142598856608,1290151783816566,1315413025950300,1337203928152094,1355756119408172,
  1371264612878306,1383894712496140,1393787195267196,1401062250555264,1405822502361504,
  1408155339615046,1408134711987038,1405822502361504,1401269554285120,1394516408693284,
  1385593785833998,1374522833421828,1361315149050352,1345972572454752,1328486730098588,
  1308838299381302,1286995940781864,1262914821032534,1236534615310828,1207776825731642,
  1176541177805426,1142700740309844,1106095229816894,1066521659310996,1023720977182096,
  977358432512802,926993705142464,872033480196094,811652000171248,744648471375326,669166496734864,
  582065814856896,477206520795838,338724714920812]]
private def pvo_r50_0 : List ℤ := pzigCatZ 20
 [
 [632755349005000,975511073082012,1048438286815816,906845513676826,669378656280172,
  435372205059240,254593594536928,135714992632784,66611994137766,30332537003086,12890093383632,
  5136086176306,1926141506046,681990476366,228572951592,72671384716,21957205320,6314243132,
  1730388500,452374568,112916456,26928984,6139302,1338522,279160,55698,10628,1936,332,54,8]]
private def phbv_g17 : List ℤ := pzigCatZ 0
 [
 [436368538947200,608524884863766,734733705198394,836175378948182,921166647420600,994026316475274,
  1057349874612434,1112846722249126,1161715991060810,1204838546755614,1242884541385034,
  1276377976420560,1305737610160924,1331304023622620,1353358173313480,1372134486440218,
  1387830332041410,1400613011023802,1410625001065644,1417987943492100,1422805702065324,
  1425166721426412,1425145844603984,1422805702065324,1418197751578400,1411363023838020,
  1402332610211658,1391127913891270,1377760672576490,1362232748227630,1344535666150786,
  1324649870316512,1302543642603104,1278171608129398,1251472713311986,1222367511963076,
  1190754518215666,1156505267440252,1119457539886530,1079405896331034,1036088155661078,
  989165522962482,938192358736480,882568180499802,821457255091950,753644282494630,677250439216980,
  589097527578720,482971468809566,342816717622758]]
private def pvi_r50_1 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r50_s0 pvo_r50_0
private def pvo_r50_1 : List ℤ := pzigCatZ 0
 [
 [7909342,68144450,406906058,1944381138,7884529062,28016897324,89020968770,256460514286,
  676684200276,1647806823510,3725373310186,7856747608264,15516854083642,28789486526804,
  50313198861828,83005895591926,129515823755972,191427138315066,268362708651190,357236752863106,
  451960311144630,543846054104508,622784406878660,679013591765932,705071645951116,697399817786728,
  657128260575190,589808210891962,504176557722400,410326124215524,317801573492052,234103197377076,
  163893001318234,108947941797176,68691756907344,41024639903394,23171728972294,12354826347286,
  6204648146286,2927188299804,1293167652542,532905974318,203878329678,71982559984,23275630122,
  6823570772,1788670238,410843352,80077906,12489190,1349990]]
private def phbv_g18 : List ℤ := pzigCatZ 0
 [
 [439543433846080,612952340971066,740079421226174,842259156095812,927868797160750,
  1001258572698748,1065042855255214,1120943482364392,1170168310246938,1213604613542412,
  1251927420140364,1285664543999784,1315237790187142,1340990217690724,1363204827178988,
  1382117751485142,1397927795649442,1410803477813028,1420888312281712,1428304825408766,
  1433157636639900,1435535834114570,1435514805398246,1433157636639900,1428516159999760,
  1421631704700444,1412535588321482,1401249369778440,1387784872171158,1372143971007048,
  1354318129932714,1334287650634534,1312020584218662,1287471225669044,1260578077193552,
  1231261114576252,1199418113567480,1164919674865182,1127602398453724,1087259350391564,
  1043626442009894,996362413417918,945018382769072,888989498638234,827433947305214,
  759127586570206,682177923150450,593383635692208,486485433533804,345310955751512]]
private def pvi_r50_2 : List ℤ := rkmApplyMaskBits [] pvo_r50_1
private def pvo_r50_2 : List ℤ := pzigCatZ 0
 [
 [2245,5335,6465,2771,3252,4566,633,4437,701,4020,1240,3711,1251,3584,752,4199,2294,38996,159812,
  156818,2783189,22421721,92055917,167560599,668884678,8003313518,45825533750,197138205282,
  704684433516,2181868984478,5981430495088,14712022649274,32747103857076,66350484481384,
  122864364625240,208489520603216,324741705429104,464656042740408,610758580376944,736929530213884,
  814944846199288,823978544470146,759043032077284,633976905581994,476925409121682,320186780020870,
  189345621700376,96726241072790,41364299519738,13972150529460,3230737410014]]
private def phbv_g19 : List ℤ := pzigCatZ 0
 [
 [402471222856960,561254381768446,677659240785008,771220876968120,849609983196508,916809878432162,
  975214432391542,1026400258452546,1071473339170548,1111246114185626,1146336677818502,
  1177228326856608,1204307290254442,1227887692532800,1248228665364082,1265546425537846,
  1280023010371682,1291812724758158,1301046978641568,1307837964190964,1312281476981948,
  1314459091233744,1314439836132832,1312281476981948,1308031474285120,1301727671453226,
  1293398744661494,1283064434491728,1270735566853462,1256413859069042,1240091494762826,
  1221750437027056,1201361431618840,1178882628399412,1154257716456818,1127413421021002,
  1098256139695480,1066667387044402,1032497544624984,995557131830554,955604333902226,
  912326673676228,865313129142464,814009863583170,757646063988088,695100835423590,624641302303080,
  543336150856896,445454014915424,316186551602280]]
private def pvi_r50_3 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r50_s2 pvo_r50_2
private def pvo_r50_3 : List ℤ := pzigCatZ 0
 [
 [1294,2329,155,4926,6581,6107,556,31919,148544,648245,2328650,7123779,18473648,40424985,73239738,
  105535913,110307290,60229187,32860797,93945510,46102867,63659277,72553132,46717944,72902695,
  59432713,50506430,86184004,1864188,72822039,133874200,642761424,630481955,9540585543,
  24449034667,15716827884,289153383404,928665121908,864249567492,4725036620245,28976797429789,
  93164740642905,224760055254505,426841015738685,683428230064161,893358791466221,1009959846466575,
  907515801279579,689505154982185,396572226025521,127638297958859]]
private def phbv_g20 : List ℤ := pzigCatZ 0
 [
 [385565600000000,537679143674054,649194468896666,738826090595850,813922497642956,878299691476962,
  934250988392628,983286776831396,1026466583048402,1064568720521728,1098185320797908,
  1127779380000000,1153720903708824,1176310821785846,1195797381194006,1212387716633780,
  1226256219027036,1237550711758672,1246397084957322,1252902818210390,1257159683243380,
  1259245827787084,1259227381488034,1257159683243380,1253088200000000,1247049185573308,
  1239070111608680,1229169889493650,1217358890400286,1203638759515582,1188002008787242,
  1170431358939712,1150898784541428,1129364193349894,1105773639767712,1080056926898612,
  1052124384072716,1021862502781658,989127949238108,953739201883136,915464603278134,
  874004801722176,828966040000000,779817745056292,725821481534910,665903437190212,598403525095914,
  520513560000000,426742919193296,302905277587490]]
private def pvi_r50_4 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r50_s3 pvo_r50_3
private def pvo_r50_4 : List ℤ := pzigCatZ 0
 [
 [1901,249,6313,48358,208783,777434,2509393,7256774,18731953,39834358,62180175,58175918,10969067,
  35809979,21712818,29572898,45552593,20380795,50126383,78285850,182218106,2831311,12894335,
  41823501,34388662,26750243,169832421,109315282,55194764,274603318,5121543153,31272244418,
  117474241735,313651719304,610158952451,830972954738,707445203891,296567387392,184868424345,
  1019444935248,3635386024101,6680500685428,4211077436200,15697384941142,63097872603307,
  230655101848275,578079093690713,956567457918917,1151570983216067,1030708360676585,
  552104939430441]]
private def phbv_g21 : List ℤ := pzigCatZ 0
 [
 [356225680000000,496764022975876,599793501118756,682604533506746,751986419924806,811464780157180,
  863158418777078,908462790020096,948356794651010,983559519766760,1014618038194416,
  1041960114000000,1065927596896328,1086798517248482,1104802231469960,1120130112181988,
  1132943279890984,1143378309244178,1151551510661064,1157562184984638,1161495120498192,
  1163422518218994,1163405475605692,1161495120498192,1157733460000000,1152153989163706,
  1144782089158052,1135635232293546,1124723000539694,1112046913891682,1097600054106490,
  1081366456788736,1063320229124288,1043424329721628,1021628918016358,997869138800684,
  972062144965434,944103065522178,913859473781766,881163661212198,845801598531308,807496713443178,
  765885212000000,720476895523730,670589520482066,615230987223500,552867534452476,480904668000000,
  394269578444800,279855460352772]]
private def pvi_r50_5 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r50_s4 pvo_r50_4
private def pvo_r50_5 : List ℤ := pzigCatZ 0
 [
 [7574,38661,64240,63660,313483,1929311,13614826,29122163,8050968,48938864,34922691,28567601,
  27989717,49150118,12976506,41351100,814601,98371006,4659447,30001131,61422178,13576548,
  168627831,72199980,547796675,1663513364,6671916265,21547049912,57603332891,124072881672,
  201025504099,196803826674,2859883594,251519002753,32586508642,397286962718,342528706498,
  587664431363,45981862790,2539059264417,1967821852172,208944676055,2021658452125,2697640212137,
  17223083628161,24165887624620,44104349095780,205176463924099,750068372877413,1350922381525657,
  1251982604877679]]
private def phbv_g22 : List ℤ := pzigCatZ 0
 [
 [363859280000000,507409234870170,612646543241210,697232142518474,768100821152528,828853749828900,
  881655137221344,927930340910580,968679238635532,1004636326891084,1036360401789206,
  1064288394000000,1088769478772074,1110087644414352,1128477162244600,1144133505829386,
  1157221248344510,1167879891110612,1176228236976198,1182367714713148,1186384929542376,
  1188353629684838,1188336221863468,1186384929542376,1182542660000000,1176843626058160,
  1169313752781508,1159970886896650,1148824815706192,1135877091777464,1121120648615642,
  1104539179722530,1086106237423980,1065783986564344,1043521518540188,1019252588354204,
  992892573557242,964334355868708,933442670813098,900046216013494,863926375730270,824800650968794,
  782297452000000,735916075623464,684959658433806,628414840964952,564714994778740,491210028000000,
  402718425406132,285852514361198]]
private def pvi_r50_6 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r50_s5 pvo_r50_5
private def pvo_r50_6 : List ℤ := pzigCatZ 0
 [
 [161113,846266,3269389,8657060,13517395,6682172,12781112,9442697,34229419,29298816,51226900,
  48285487,4206380,47620979,41408008,38127535,42681803,42784162,179192191,246274316,118752065,
  1241428879,4641251944,10849357135,15887785700,10273553133,8119730491,14557659710,11658808196,
  21200124595,13131993037,1498791943,166823093699,514666265026,81235486913,545984726850,
  727117779013,133304119509,1559589681978,2265790351707,3524907988482,5693190695997,
  14076756250052,12213506472029,1277642953292,27186220561302,37714587737889,47472677205938,
  132358894054054,664389707753619,1880491903061639]]
private def phbv_g23 : List ℤ := pzigCatZ 0
 [
 [353457920000000,492904324842290,595133296776788,677300913836040,746143725109512,805159957439380,
  856451952962614,901404323680146,940988364609798,975917575770948,1006734779409162,
  1033864416000000,1057645679192960,1078354439145804,1096218270245790,1111427058209874,
  1124140671689488,1134494624190382,1142604322437164,1148568295736920,1152470673595008,
  1154383096049806,1154366185852180,1152470673595008,1148738240000000,1143202119873858,
  1135887497181730,1126811708479842,1115984261288852,1103406663794068,1089072051505010,
  1072964584064564,1055058569837510,1035317255232136,1013691186929344,990116013625634,
  964509531907472,936767685600580,906759076928978,874317300402508,839229989678318,801222721339074,
  759934528000000,714879019670550,665379253633228,610450838534618,548571929915610,477168192000000,
  391206229478952,277681072619282]]
private def pvi_r50_7 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r50_s6 pvo_r50_6
private def pvo_r50_7 : List ℤ := pzigCatZ 0
 [
 [802438,2783253,3743816,3947210,12140457,14556663,14466998,24652801,60246602,29351511,31715024,
  25451370,30167381,3396019,10436197,64620114,61835288,42240801,15740242,38255761,191405998,
  357706346,582516586,12069542,2152658495,14092226095,20138718825,1479187817,810878768,
  10534005264,35103656450,79908510439,255330506678,121322873443,417800918127,374505555195,
  189822794388,1027130659226,278168851686,275510550385,2716687853723,437910225221,3398022024575,
  19421788088975,2059366972913,7354179685825,25587885572657,43964774314701,8563255010244,
  140572608540351,1994272316968725]]
private abbrev pl_r50 : List ℕ := [1, 1, 1, 1, 1, 1, 1, 1]
private abbrev ptau_r50 : List ℕ :=
  [9431622, 25909382, 17856452, 8804058, 4819570, 4452821, 4548241, 2209112]
private abbrev pnsub_r50 : List ℕ := [7, 19, 13, 7, 4, 4, 4, 2]
private def pwalks_r50 : List RkmSegWalk := [ ⟨phbv_g16, pvi0, pvo_r50_0⟩,
  ⟨phbv_g17, pvi_r50_1, pvo_r50_1⟩, ⟨phbv_g18, pvi_r50_2, pvo_r50_2⟩,
  ⟨phbv_g19, pvi_r50_3, pvo_r50_3⟩, ⟨phbv_g20, pvi_r50_4, pvo_r50_4⟩,
  ⟨phbv_g21, pvi_r50_5, pvo_r50_5⟩, ⟨phbv_g22, pvi_r50_6, pvo_r50_6⟩,
  ⟨phbv_g23, pvi_r50_7, pvo_r50_7⟩]
private def phbv_g24 : List ℤ := pzigCatZ 0
 [
 [421058652740012,587910282015498,710767282571612,809994492505112,893581077160878,965672883903076,
  1028760325655588,1084483290000000,1133992289507158,1178132897757164,1217549030082382,
  1252744929468712,1284124439359384,1312016993420176,1336695441047310,1358388643598512,
  1377290602546480,1393567217808420,1407361383986742,1418796893723862,1427981466993818,
  1435009127659612,1439962083814550,1442912224345798,1443922313530998,1443046943754556,
  1440333290694832,1435821703674708,1429546155000000,1421534565143224,1411809014925750,
  1400385850927744,1387275685822134,1372483290837040,1356007372751610,1337840222328564,
  1317967214392846,1296366131221004,1273006269577994,1247847276254450,1220837635235138,
  1191912698419988,1160992105923996,1127976372852236,1092742312604980,1055136796898074,
  1014968073864066,971993391006136,925900827180998,876281665804548,822586529387106,
  764051870820012,699567970082824,627419035998406,544700803398492,445728727201302,315793989555008]]
private def pvo_r57_0 : List ℤ := pzigCatZ 10
 [
 [5104349284616,19089464694344,49793107386856,104581373374172,187560219837548,296589143241644,
  421960392618650,547663065896526,655029294844312,727498908225762,754781310552994,735022672568178,
  674466082836626,585052478637360,481028713329978,375726292465702,279338289431924,197996819764918,
  133986728979450,86668214134794,53640744729968,31793788343732,18060041705590,9837563200082,
  5141189857432,2578799363870,1241875905822,574295211046,255058873826,108795055634,44567719594,
  17531419062,6620721030,2399680644,834431178,278229894,88906986,27207014,7966714,2230034,596054,
  151926,36866,8498,1854,380,70,10]]
private def phbv_g25 : List ℤ := pzigCatZ 0
 [
 [423490523874334,591305823313842,714872398156952,814672705890502,898742054173420,971250235172974,
  1034702045470194,1090746844000000,1140541788246702,1184937335494770,1224581120081270,
  1259980297303614,1291541043047808,1319594693660448,1344415674409830,1366234168467932,
  1385245297784562,1401615920450370,1415489756371452,1426991313168418,1436228932964008,
  1443297182666518,1448278745171246,1451245924567634,1452261847635398,1451381422063338,
  1448652095998198,1444114451804868,1437802658000000,1429744796313906,1419963075098198,
  1408473935344538,1395288051020526,1380410220911044,1363839144326096,1345567067502848,
  1325579280796910,1303853438163902,1280358659038822,1255054357147852,1227888718939274,
  1198796722930720,1167697545109720,1134491125995260,1099053567509688,1061230856959394,
  1020830134992664,977607247068602,931248470508626,881342728140490,827337469483646,
  768464737478088,703608402791828,631042764504728,547846783541652,448303083097718,317617892905750]]
private def pvi_r57_1 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r57_s0 pvo_r57_0
private def pvo_r57_1 : List ℤ := pzigCatZ 0
 [
 [71,534,2511,9514,30301,83790,204043,444938,851855,1572438,1925287,5407164,6751274,50728810,
  188319672,722153090,2527176228,8242496732,25155506500,71881410398,192870831834,486768555902,
  1157392903122,2596358750168,5501721058750,11024008712106,20906389727914,37553156168562,
  63931549728006,103206174415902,158047267776202,229656713201456,316704086315258,414508735072532,
  514865009042120,606815389597296,678413686345006,719155843506978,722432889477154,687239828088158,
  618547558682422,526172087928746,422488674779400,319719530149224,227612743212010,152107465909520,
  95169354583172,55573689643004,30171899101466,15158110892234,7005223127478,2955492039176,
  1126938158496,383014674078,113709879794,28556335876,5719999684,791450902]]
private def phbv_g26 : List ℤ := pzigCatZ 0
 [
 [425801795274382,594532975188704,718773935583170,819118920432208,903647091449882,976550998151820,
  1040349107471460,1096699780000000,1146766488605092,1191404332086154,1231264479354554,
  1266856853593800,1298589847463726,1326796605635268,1351753051099190,1373690623291196,
  1392805509072244,1409265477189332,1423215031924332,1434779360419322,1444067396092566,
  1451174221967302,1456182972194766,1459166345476238,1460187813116546,1459302582472518,
  1456558360647216,1451995951490666,1445649710000000,1437547871166342,1427712764547148,
  1416160920863586,1402903072338242,1387944043946180,1371282527898672,1352910728115404,
  1332813854671608,1310969439565570,1287346433696370,1261904029283710,1234590129994622,
  1205339359480962,1174070452619498,1140682803837618,1105051838862886,1067022704451280,
  1026401488688448,982942704518650,936330917068550,886152805642474,831852804121862,
  772658764190728,707448465051850,634486787479468,550836750331994,450749773250400,319351346455786]]
private def pvi_r57_2 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r57_s1 pvo_r57_1
private def pvo_r57_2 : List ℤ := pzigCatZ 0
 [
 [19525217,81187812,200808209,329792886,339576865,129750658,184677628,282115725,15016152,
  267007662,121708487,229899811,156184810,223178388,142466899,251147545,79460434,287694186,
  47291780,270036367,221707927,109905614,323161586,197673316,132598911,362512977,313337447,
  51156151,250450168,456429484,510676584,457898594,394520274,307104656,259973383,2167132731,
  4170859383,7463279304,70754699326,218302793026,250238168778,921460338227,6602001675987,
  23951370455389,64874610546135,143820993725937,271410066278633,444318344776171,637756476089275,
  806386847537397,899321205240813,882555101818895,757666547247049,563148403496641,356066368856045,
  185936329375421,75795952106177,20876740680027]]
private def phbv_g27 : List ℤ := pzigCatZ 0
 [
 [390450501681662,545173132206114,659099249601112,751113304286576,828623702660582,895474916681374,
  953976322891140,1005648600000000,1051558626001206,1092490506924672,1129041349759946,
  1161678742396584,1190777171557480,1216642123281778,1239526612637444,1259642864290460,
  1277170777102546,1292264191175258,1305055613628062,1315659838205298,1324176754358548,
  1330693551044120,1335286460376152,1338022145399990,1338958807849598,1338147071607758,
  1335630682996186,1331447058211552,1325627700000000,1318198499202226,1309179931511402,
  1298587155220524,1286430011532100,1272712924837838,1257434695925406,1240588175967570,
  1222159802941790,1202128974204682,1180467218441266,1157137115850904,1132090895288508,
  1105268608138980,1076595736144092,1045980026296144,1013307246838226,978435400889424,
  941186675662006,901335965143892,858594022775042,812581842936476,762789984211746,708510404265910,
  648714052310234,581809863723346,505104694011992,413327226544700,292837876261246]]
private def pvi_r57_3 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r57_s2 pvo_r57_2
private def pvo_r57_3 : List ℤ := pzigCatZ 0
 [
 [65494963,321095414,364783463,9678025,90882399,272431756,110567999,231908995,5393301,375665309,
  93539460,282678226,43855395,191354688,45271931,103193641,12631657,231585283,122032892,277785174,
  243269865,501277330,42888390,218373344,73612276,385426142,305884161,559032432,168215756,
  158308916,1197072811,2382254902,2211715467,518523826,1959636180,4144991530,36836997055,
  109738835030,163645506559,40818141320,233058086800,72146698725,510225366867,370888839107,
  847568602528,3275987888590,2987953263596,13292870128909,71759991533405,203316340026835,
  420036420050877,687660727586291,919595691110317,1013665691194701,915835361512937,
  663396914763905,366090948897251,134017512456245]]
private def phbv_g28 : List ℤ := pzigCatZ 0
 [
 [381074181977256,532081286863872,643271570408546,733075989838546,808725045295996,873970887182326,
  931067434426826,981498848000000,1026306385773964,1066255324173376,1101928431197290,
  1133782066030158,1162181722431040,1187425550464982,1209760489269306,1229393667124388,
  1246500662781624,1261231622010082,1273715869889220,1284065443494246,1292377833520868,
  1298738135160566,1303220749881412,1305890739875318,1306804909213650,1306012666091902,
  1303556706302986,1299473547527064,1293793936000000,1286543140817094,1277741145966056,
  1267402745727028,1255537544974838,1242149861853384,1227238525948346,1210796560105182,
  1192810727981200,1173260921687076,1152119353621002,1129349502585402,1104904744616518,
  1078726570711650,1050742252101916,1020861751153112,988973579281838,954939149535322,
  918584919140948,879691187806256,837975654968734,793068416490480,744472264735184,691496160371530,
  633135764345424,567838220029840,492975056388646,403401542746302,285805636482942]]
private def pvi_r57_4 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r57_s3 pvo_r57_3
private def pvo_r57_4 : List ℤ := pzigCatZ 0
 [
 [404561883,230310976,72328612,115654408,123693530,389359307,83047937,161402184,159863859,
  188462658,11595242,31163014,376643153,58405679,267726445,95810114,109478690,143677130,68419408,
  40100162,4922669,458363978,493588287,404170790,547204547,1196834874,122505105,428109615,
  2768797782,7590645959,18514117912,41386601411,80782066928,119554295981,133054464014,
  115138403201,118166644448,230564422147,444854654778,603405289311,745423198634,823850306937,
  18467697735,1698218714000,2570214855887,489052496916,4025834812230,1246636078011,6789050577115,
  1475085248980,24799426590774,24139548464760,92657504832927,406862142050935,856896568337221,
  1186340132765927,1120639580004921,653524805718959]]
private def phbv_g29 : List ℤ := pzigCatZ 0
 [
 [355636700749812,496563772463272,600331877114414,684141667830552,754740994077568,815631542541654,
  868916778452630,915981792000000,957798334962772,995080599998696,1028372454150698,
  1058099793694068,1084603714931748,1108162465801998,1129006501749552,1147329124818340,
  1163294193518910,1177041831083088,1188692729876710,1198351448271016,1206108969258334,
  1212044707752028,1216228098769974,1218719861469668,1219573008134510,1218833648861866,
  1216541629413128,1212731029838598,1207430544000000,1200663754228828,1192449310540730,
  1182801019667386,1171727845338574,1159233817453258,1145317843724666,1129973412737596,
  1113188171702310,1094943354972230,1075213029824818,1053963112927142,1031150092560416,
  1006719365317556,980603057223790,952717140841194,922957569677384,891195007742200,
  857267496598122,820970001396662,782039065715372,740129477274284,694777218063970,645337377042172,
  590872656841276,529933857190858,460067962873628,376473664511444,266727525562360]]
private def pvi_r57_5 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r57_s4 pvo_r57_4
private def pvo_r57_5 : List ℤ := pzigCatZ 0
 [
 [135479620,324325398,105307340,396626184,7978206,26230038,66584852,361890784,4246727,263748258,
  12811082,1776844,361313902,132181974,63202148,37540832,11102378,297496601,111872227,153023589,
  193915740,556194687,155356112,192903750,135950745,32455977,698616527,2132464656,7210286297,
  15171321866,29819518373,37914737116,33626856323,4691799428,40723858232,89706258035,151610521762,
  156978074473,412295878932,218541590188,760137139487,1901944033066,2711551255549,1708635506814,
  3303555006947,4019119208422,6838638537307,4365114561858,2102002732807,13778936717063,
  21759177149930,18244917846807,40658704733479,62768657031012,82567823664016,382432789867163,
  1240684235402209,1516881359519031]]
private def phbv_g30 : List ℤ := pzigCatZ 0
 [
 [338833974857240,473102681582352,571968066645866,651818105914676,719081833994720,777095493788056,
  827863168347108,872704506666080,912545348280546,948066142470710,979785060256494,
  1008107875641334,1033359569190770,1055805242495038,1075664462697246,1093121398922102,
  1108332167876146,1121430272405138,1132530702536726,1141733076584932,1149124078879210,
  1154779372225738,1158765111054166,1161139145731012,1161951983874472,1161247557023506,
  1159063828351440,1155433267732402,1150383213332560,1143936133291734,1136109796470446,
  1126917357275330,1116367355927866,1104463631926848,1091205144592648,1076585690154146,
  1060593499452422,1043210693459224,1024412564692344,1004166640150122,982431463906894,
  959155012396412,934272618477702,907704224747442,879350700585788,849088820725086,816764278759298,
  782181727097612,745090156812566,705160665828690,661951159541552,614847196945998,562955765054270,
  504896133792800,438331185269344,358686457012272,254125481142930]]
private def pvi_r57_6 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r57_s5 pvo_r57_5
private def pvo_r57_6 : List ℤ := pzigCatZ 0
 [
 [299273661,310015890,135221459,180429474,117583384,310770612,56069373,135990479,208597402,
  336986584,244288323,117140802,72631911,92412263,269460949,115526570,209116999,4666664,8802042,
  194685324,86560514,211471821,148573638,720075038,429846415,1958673878,4882385707,11086935822,
  17375409039,13927793298,10419157956,23741769027,63389629911,92519661588,89637169435,87423535726,
  35928100803,170313830876,21294657446,148270017379,571174075407,779385368034,1038941933253,
  1146112130531,2483280277835,1654521390189,989932025005,7711139606525,5851958062009,
  2982622878948,11458839453613,15013812401989,5629340665207,50383944447531,55249403759803,
  115247261911358,642298027100627,1888935141636739]]
private def phbv_g31 : List ℤ := pzigCatZ 0
 [
 [353924814897846,494173522821188,597442131357718,680848496908002,751107987622000,811705434535502,
  864734177679330,911572640000000,953187895671204,990290699526914,1023422300662316,
  1053006545266740,1079382887748648,1102828236677480,1123571938182156,1141806363831678,
  1157694583390480,1171376045595942,1182970861851498,1192583087228260,1200303266764606,
  1206210433103834,1210373687032772,1212853455432376,1213702495407154,1212966695099812,
  1210685708470968,1206893451523860,1201618480000000,1194884262715436,1186709359912466,
  1177107511862954,1166087639149048,1153653752271470,1139804764201254,1124534194866420,
  1107829750938378,1089672757100496,1070037405459482,1048889776745272,1026186568686228,
  1001873440713164,975882845568138,948131160286054,918514839210688,886905168921064,
  853140970579622,817018196289604,778274657797232,736566804529602,691432852065284,642230993693168,
  588028443801878,527382977963010,457853388745238,374661478259136,265443611173384]]
private def pvi_r57_7 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r57_s6 pvo_r57_6
private def pvo_r57_7 : List ℤ := pzigCatZ 0
 [
 [163376354,443780034,62617051,224700414,163636571,136090228,123584110,203688772,257280609,
  193209785,144070202,140211964,333808898,53065966,112096697,240375158,197694448,141818631,
  151557080,235241525,204446774,418569899,279637568,131861771,156903987,89593917,770328325,
  842315142,3617071207,12051696117,18398672763,9973338971,4583182992,36230790703,54163939311,
  56600607747,200073642425,601550459,32489640948,185524321678,18085270859,87372518915,
  896642728861,402902183683,600026359763,3713379984907,698244827376,1342616521113,7719217036637,
  3816770128809,1146591029517,20314655223939,4611353893250,21783592535803,57621938052329,
  9014959656034,137880414189233,1994137907341647]]
private abbrev pl_r57 : List ℕ := [1, 1, 1, 1, 1, 1, 1, 1]
private abbrev ptau_r57 : List ℕ :=
  [19717878, 24789701, 14954997, 4571130, 5576698, 5204442, 2975129, 2071756]
private abbrev pnsub_r57 : List ℕ := [16, 20, 12, 4, 5, 5, 3, 2]
private def pwalks_r57 : List RkmSegWalk := [ ⟨phbv_g24, pvi0, pvo_r57_0⟩,
  ⟨phbv_g25, pvi_r57_1, pvo_r57_1⟩, ⟨phbv_g26, pvi_r57_2, pvo_r57_2⟩,
  ⟨phbv_g27, pvi_r57_3, pvo_r57_3⟩, ⟨phbv_g28, pvi_r57_4, pvo_r57_4⟩,
  ⟨phbv_g29, pvi_r57_5, pvo_r57_5⟩, ⟨phbv_g30, pvi_r57_6, pvo_r57_6⟩,
  ⟨phbv_g31, pvi_r57_7, pvo_r57_7⟩]
private def phbv_g32 : List ℤ := pzigCatZ 0
 [
 [418480440587348,584880746874608,707818545077782,807476909424186,891767544588272,964793522865944,
  1029018362240080,1086063701536562,1137067073524238,1182864554184062,1224093011734126,
  1261251457565674,1294739909431802,1324885107846296,1351958155043484,1376186982603492,
  1397765391370752,1416859750890304,1433614059030318,1448153826431416,1460589101696096,
  1471016856881840,1479522888888198,1486183348903772,1491065982007356,1494231137806676,
  1495732597778768,1495618253875400,1493930664729002,1490707509593952,1485981955400726,
  1479782948574792,1472135440281562,1463060551283570,1452575680467308,1440694559178454,
  1427427251677284,1412780100179618,1396755610967382,1379352275806198,1360564320235146,
  1340381366988216,1318787998585566,1295763197599806,1271279635688474,1245302772350778,
  1217789710255342,1188687733964960,1157932429925942,1125445242832762,1091130258917612,
  1054869906780514,1016519107324702,975897143107628,932776072465496,886863723407694,
  837777827080434,785004928864840,727831493070174,665220103018838,595565541173900,516147782567778,
  421635755519836,298213196401470]]
private def pvo_r64_0 : List ℤ := pzigCatZ 12
 [
 [1073661501804,4572812476696,13595036571418,32573220072432,66700881414690,120541409820736,
  196185023682532,291582831882786,399782670600536,509554988811510,607403836254294,680424227888798,
  719135733204958,719435691367254,683150595141994,617157745589978,531491017972446,437078250537756,
  343738484297038,258856563173862,186868065275026,129441922299402,86107697646684,55049057183738,
  33842944117094,20018253219098,11397692142884,6248842483874,3299908818764,1678889900896,
  823058009596,388838763716,177033757576,77674888248,32840364298,13377558264,5249278672,
  1983633500,721637522,252638618,85074388,27540882,8565670,2557598,732534,201060,52824,13264,3174,
  718,152,28,4]]
private def phbv_g33 : List ℤ := pzigCatZ 0
 [
 [401066893353950,560543053821830,678365240999608,773876683611000,854659869407314,924647136197734,
  986199491590470,1040871095787432,1089752147252976,1133643931695502,1173156816369804,
  1208769048116174,1240863999398318,1269754814607438,1295701315040676,1318921947731326,
  1339602449203892,1357902266137610,1373959404451122,1387894152114508,1399811978456420,
  1409805820393530,1417957904698284,1424341213803498,1429020673821970,1432054123131172,
  1433493105286844,1433383519390706,1431766153151906,1428677117939178,1424148200561362,
  1418207142943308,1410877857998092,1402180587624240,1392132006716628,1380745275240734,
  1368030038669110,1353992375309242,1338634687153220,1321955528726372,1303949365851046,
  1284606253073556,1263911414456624,1241844707136944,1218379939942006,1193484009648808,
  1167115803942984,1139224800949242,1109749267450538,1078613916935750,1045726826740986,
  1010975317774080,974220347879204,935288719515376,893961975985230,849960102976900,
  802916738369854,752339793098750,697545422675240,637539378757828,570783239121120,494670162780954,
  404090911288338,285804134764394]]
private def pvi_r64_1 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r64_s0 pvo_r64_0
private def pvo_r64_1 : List ℤ := pzigCatZ 0
 [
 [15670839,114556536,569961303,2220180162,7147722205,19530528740,45867957737,93002322342,
  161946409737,239363845450,288521300359,267552655780,128607307281,41239774495,290930008620,
  83837353269,420013398502,1004728544258,1538385954860,3673247030038,7250888829208,12864276404466,
  23035659750160,39212350276130,62771085424772,96683743985960,143067017131596,201905494266954,
  272508077044332,352970353314856,438238162821840,520807368218042,592996382595786,647667041280282,
  678281586556998,680438539394500,653798768998560,602116580398456,531605239408912,449512021551232,
  363498280425548,280938067205272,207688136200848,147045705635164,99688044712702,64497337507358,
  39557305038368,22791419830540,12216316247808,6035611063922,2726268424842,1118035887968,
  413950515490,137914341172,41426702946,11380556732,2972102708,789292502,225533772,67922702,
  19804274,5139298,1112288,187116],
 [21144]]
private def phbv_g34 : List ℤ := pzigCatZ 0
 [
 [396938475867836,554773054394140,671382428482986,765910715624968,845862352564092,915129199243026,
  976047960029660,1030156797240614,1078534687286070,1121974667769226,1161080823075638,
  1196326477169508,1228091056236232,1256684481287566,1282363899127182,1305345508184552,
  1325813133088854,1343924579240856,1359816431983084,1373607741090780,1385402890234744,
  1395293859677288,1403362029782318,1409679631731528,1414310923315044,1417313147545890,
  1418737317411660,1418628859547622,1417028141811036,1413970903855072,1409488605288246,
  1403608702471456,1396354862168094,1387747117914916,1377801972962296,1366532451812444,
  1353948100651388,1340054935219022,1324855332782316,1308347862745720,1290527047898128,
  1271383045160258,1250901230692250,1229061668973140,1205838438431566,1181198776595470,
  1155101994343732,1127498089852442,1098325965360876,1067511109326264,1034962545298776,
  1000568754058426,964192124692100,925661242482998,884759899437064,841210963594478,
  794651844015550,744595516997190,690365177264682,630976810859642,564907831441712,489578231774618,
  399931365806556,282862184663008]]
private def pvi_r64_2 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r64_s1 pvo_r64_1
private def pvo_r64_2 : List ℤ := pzigCatZ 0
 [
 [154602737903,11261879028,155012835168,14511955130,203508103361,7366296756,191804966212,
  29268830263,122716760387,50594677236,11777943314,93547350573,108274484962,179608646898,
  173677512935,281427428249,124695588106,286631721884,26785264937,123853898529,76025468602,
  15975421349,248547823343,25916185001,261557060506,105312523656,289513820293,10025478410,
  170379761281,90260763210,830520358309,698080177102,698256320041,856392173554,1025265722541,
  692350177644,225209200398,770671211561,831057921830,523468143639,1203308353950,3304768228266,
  6811092329464,20944906534790,44824355927482,85854618756158,156275914536236,254719440966312,
  378219379579250,519782883238004,655408103827122,758055781756100,809419750524568,795922835615164,
  715651068121510,587853138897208,442658000343190,304495171496376,188171581486774,101825819065070,
  46943246001832,17943949329426,5509963156832,1290664274004],
 [202328513228]]
private def phbv_g35 : List ℤ := pzigCatZ 0
 [
 [378160817201292,528528838511480,639621863954174,729678375195860,805847802448730,871837896474746,
  929874820992072,981423973673150,1027513288633274,1068898287864712,1106154478804482,
  1139732794249442,1169994711166578,1197235489376238,1221700111038958,1243594547053844,
  1263093926001824,1280348588106736,1295488657374914,1308627551786798,1319864717016348,
  1329287782087396,1336974277566492,1342993017651194,1347405220338500,1350265420690900,
  1351622218464398,1351518891331882,1349993897499898,1347081285913736,1342811027946766,
  1337209281103254,1330298592561484,1322098048147330,1312623370404776,1301886967696074,
  1289897934613282,1276662002314378,1262181435606824,1246454871571132,1229477092102350,
  1211238719760068,1191725822502996,1170919407884306,1148794780584182,1125320727999258,
  1100458485856906,1074160417730480,1046368316163330,1017011194472086,986002379958822,
  953235628956250,918579840403320,881871708565448,842905253431402,801416453106682,757059869458180,
  709371518033010,657706610655330,601127683347064,538184177571478,466418136480920,381012124831638,
  269481044067700]]
private def pvi_r64_3 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r64_s2 pvo_r64_2
private def pvo_r64_3 : List ℤ := pzigCatZ 0
 [
 [6418552996,69036837242,39122017969,140490450848,296643536020,119186396327,142592137668,
  285538730781,61306842265,64875288860,35411993168,28665773312,98727824534,19128491170,
  47831137695,51812797821,148929347637,136135534305,184180065526,91944604497,189403868099,
  279581245226,13444642710,174367418936,94807392583,239721864139,279352831216,430682942741,
  471751279947,77113263546,564035632936,424569749507,224615531626,485092427641,525033779964,
  911149714732,1288785943797,16573545822,376589880182,391295479533,1567575814216,350050420430,
  1335743004451,445790622196,300097090687,1453781507957,192074721937,1055614583683,1525250744009,
  495571562388,1327217690242,3563596817354,4894829750316,16056395956417,82614093195721,
  220110804826439,430931836942099,691511727134239,896672162360311,986703466276439,899972983582571,
  685506374449585,427230754699257,194429233420095],
 [52152861684577]]
private def phbv_g36 : List ℤ := pzigCatZ 0
 [
 [404091756628006,564770692964154,683481500002532,779713293906426,861105749866710,931620863548694,
  993637449378656,1048721389099716,1097971103498614,1142193921614058,1182004814116192,
  1217885634802966,1250222647549232,1279331358494280,1305473548518334,1328869312191348,
  1349705786870454,1368143621788408,1384321863710260,1398361707822990,1410369418909330,
  1420438634820066,1428652202485402,1435083654774704,1439798407476236,1442854735186924,
  1444304570206162,1444194157808616,1442564593326038,1439452260480616,1434889185818628,
  1428903320495688,1421518757777054,1412755892226502,1402631524501658,1391158913821014,
  1378347778403676,1364204242399982,1348730725917944,1331925772581060,1313783806472682,
  1294294807130092,1273443887175278,1251210751826616,1227569012376680,1202485315936572,
  1175918240121138,1147816882016990,1118119042812576,1086748868182764,1053613742179090,
  1018600135878960,981567958464800,942342706132530,900704274575242,856370537601430,
  808972369972128,758013971265702,702806339410082,642347727401224,575088110169006,498400985825596,
  407138581832058,287959681495246]]
private def pvi_r64_4 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r64_s3 pvo_r64_3
private def pvo_r64_4 : List ℤ := pzigCatZ 0
 [
 [20075593283,47162172653,54965574758,34706272252,23122831512,27804816621,66317059541,
  107941539166,245917584726,328686023838,55038383356,98675067020,250393016717,197943533689,
  122533295102,117929627185,29400313866,59456989959,22992232587,23705311182,37994736509,
  54319288879,26748753025,80291801007,247197963870,325750594451,134670106674,350292897155,
  59376211788,432442261343,26334839664,89004883293,102648235150,110573816919,1167479336287,
  600355914759,770695045638,93452458092,492973480121,887584099802,705411061395,26033104409,
  1494739557920,1504653867180,7880231580,92152068733,721292876539,170783822042,2154954210653,
  2765344114210,2302884202602,4815524882193,5480343552296,461581246599,2467771293011,
  12462781248585,4180910428874,38315243668160,31595598695248,124170082326009,502836664327627,
  951688291775957,1199444959866609,1043668004507775],
 [543497289317921]]
private def phbv_g37 : List ℤ := pzigCatZ 0
 [
 [314860960075084,440059069981632,532556375512664,607538442138242,670957966061160,725902062369840,
  774224260075488,817144665802194,855519149084058,889976766050178,920996690681324,948954374708320,
  974150787929444,996831767000104,1017201286829276,1035430841109832,1051666243872780,
  1066032670083542,1078638462456908,1089578054082152,1098934244548642,1106779994769614,
  1113179857568918,1118191128423304,1121864778127292,1124246213188778,1125375898312566,
  1125289866977044,1124020139918590,1121595066672948,1118039601743508,1113375524163236,
  1107621606966988,1100793741228574,1092905017715384,1083965767769732,1073983563651502,
  1062963177187448,1050906494081790,1037812379552404,1023676488946270,1008491014500774,
  992244356241260,974920700842362,956499486702366,936954725855796,916254142732208,894358074705680,
  871218057591534,846774987076838,820956698496084,793674732174018,764819931889074,734256327445404,
  701812417563280,667268374636562,630336582980886,590630723909466,547613939517264,500505686726452,
  448098214144638,388344999187592,317234990955928,224372955625458]]
private def pvi_r64_5 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r64_s4 pvo_r64_4
private def pvo_r64_5 : List ℤ := pzigCatZ 0
 [
 [2107114122,11998157610,29048975366,52135293310,48757878522,19541326391,81047708136,155427066332,
  216296542179,117266809413,61819478642,255297703316,168024880472,129313065962,5742566473,
  241429619937,243385275229,104997416827,808167648,8212721621,3666143217,30536459627,37516826386,
  99280780047,87749870989,102866608434,128850870490,377463936997,540115515775,383367476082,
  203370370999,480219910212,432489009423,505585057565,757716010058,156821582471,261106801469,
  1290322301193,624573519836,549114680902,185960419389,72903093540,493801672499,1147523636751,
  1081706445258,983317442118,818008077570,1196327224308,478490172667,282480124113,2141596069026,
  589699881676,145174318846,8315124141136,5239978959808,10038409915013,18501700818208,
  20995725707358,47235669527891,21555142285848,56080931562606,252089436150199,890690704987595,
  1383917165502303],
 [1105014501889543]]
private def phbv_g38 : List ℤ := pzigCatZ 0
 [
 [350737272783374,490200874799272,593237633227588,676763407746110,747409164707022,808613775435066,
  862441966247088,910252866803798,952999867281542,991383700572368,1025938139345848,
  1057081415560940,1085148792523118,1110414118339958,1133104609504968,1153411300276964,
  1171496619226186,1187500004173004,1201542142764124,1213728228111406,1224150494266840,
  1232890215554572,1240019300163474,1245601572008884,1249693809668424,1252346593419632,
  1253604998651346,1253509164617214,1252094760603598,1249393366387326,1245432779871514,
  1240237261665114,1233827723865470,1226221868228586,1217434277127744,1207476459093018,
  1196356849192952,1184080762972228,1170650300998528,1156064199188844,1140317617845836,
  1123401859564260,1105304002629484,1086006431892866,1065486242894902,1043714486514264,
  1020655209593868,996264230215312,970487562022342,943259366158580,914499255274752,
  884108690303830,851966077398638,817919953463660,781779275788752,743299168873814,702159245139776,
  657929167454342,610010906524080,557534981577718,499156025982742,432594329514958,353381808696786,
  249938761933684]]
private def pvi_r64_6 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r64_s5 pvo_r64_5
private def pvo_r64_6 : List ℤ := pzigCatZ 0
 [
 [11426011829,24884121342,3191899244,78425624041,105904639636,226321472807,235153942256,
  18462259085,109150583284,140329107897,34650616773,139155812849,310934583216,90312515739,
  219480822027,3771013243,116000817868,24711780891,45329124594,19231630037,11664768368,3029586063,
  11654349268,6912819591,32365480339,15518136648,19707971710,17361670392,78244245596,232210415599,
  482285200027,503387476022,68748311778,283296124966,149260313888,595357809582,931462483914,
  234397755136,407366940503,881523919451,7256097760,222607409064,732524017542,875904349120,
  354110645200,603182454258,761735405888,1536994150741,2856364343089,2679790565454,2668336221861,
  324829451432,3488768896526,5671841809117,8764381926484,12875837573865,22498439268720,
  10052187410927,2455263568805,68119533989494,39156047540761,88574700073610,176077539917774,
  741966796545131],
 [1844866460662487]]
private def phbv_g39 : List ℤ := pzigCatZ 0
 [
 [308045310546292,430533314892002,521028374045118,594387338565746,656434049396058,710188796272448,
  757464985721168,799456313282714,837000121879360,870711850753218,901060301427590,928412798403388,
  953063796524920,975253810935246,995182401192862,1013017348746014,1028901311256844,
  1042956754086210,1055289674704280,1065992462050938,1075146123391144,1082822040287010,
  1089083368217264,1093986162409986,1097580290318486,1099910175556996,1101015406909570,
  1100931237854564,1099688995990292,1097316417183210,1093837915758122,1089274799307342,
  1083645434494526,1076965368406764,1069247408441658,1060501662303736,1050735538339674,
  1039953705082700,1028158007418072,1015347335127766,1001517437605454,986660676099548,
  970765701734680,953817043489218,935794584848930,916672900397804,896420413219734,874998319247316,
  852359203377652,828445240701526,803185828668560,776494422449160,748264228675986,718362220437114,
  686620608861670,652824324849998,616691978601386,577845613890924,535759993928262,489671471690450,
  438398439420712,379938674662346,310367951879030,219516058063696]]
private def pvi_r64_7 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r64_s6 pvo_r64_6
private def pvo_r64_7 : List ℤ := pzigCatZ 0
 [
 [1696881076,11440934230,43488770118,11984680425,26230400635,18133603145,134766219439,
  366768339265,42749173865,4976467833,75331034273,23297383886,116502272804,207506489327,
  349644960777,9357099463,30896160966,28491485602,23090454733,30711285111,22843216585,11375469121,
  1980043732,3618598987,30086769019,5509915042,21036945640,22111190094,2827279621,10877467729,
  53607953290,64474753480,486200443251,610249424141,50353214075,297490036933,163983995759,
  860598971902,373760376980,421220310468,646871068184,695094460584,487453781832,260746867502,
  713841209887,1038215477859,124716040109,503586147899,892303667758,504334585562,3625012860190,
  2695427265514,1491882503458,499614288598,5855496009034,315686493177,16736549078786,
  6778505708720,46781442150322,21965699447115,26264841104579,72092913094125,8100467326369,
  136788040660855],
 [1993056849744355]]
private abbrev pl_r64 : List ℕ := [1, 1, 1, 1, 1, 1, 1, 1]
private abbrev ptau_r64 : List ℕ :=
  [20806197, 17724820, 16445970, 9400784, 6696938, 3478755, 4843920, 2552589]
private abbrev pnsub_r64 : List ℕ := [18, 16, 15, 9, 6, 4, 5, 3]
private def pwalks_r64 : List RkmSegWalk := [ ⟨phbv_g32, pvi0, pvo_r64_0⟩,
  ⟨phbv_g33, pvi_r64_1, pvo_r64_1⟩, ⟨phbv_g34, pvi_r64_2, pvo_r64_2⟩,
  ⟨phbv_g35, pvi_r64_3, pvo_r64_3⟩, ⟨phbv_g36, pvi_r64_4, pvo_r64_4⟩,
  ⟨phbv_g37, pvi_r64_5, pvo_r64_5⟩, ⟨phbv_g38, pvi_r64_6, pvo_r64_6⟩,
  ⟨phbv_g39, pvi_r64_7, pvo_r64_7⟩]
private def phbv_g40 : List ℤ := pzigCatZ 0
 [
 [359116252218692,503237643100210,610666766260568,698587700645112,773720701935968,839543755672626,
  898141261542542,950883126115958,998729027398400,1042383589918938,1082383169475230,
  1119147877717590,1153014509614118,1184258315590278,1213107925590574,1239755892737474,
  1264366336282082,1287080605986928,1308021561928162,1327296863458236,1345001534972246,
  1361219994491210,1376027676923576,1389492347149708,1401675172686294,1412631607819646,
  1422412128317342,1431062846552652,1438626030053406,1445140541405774,1450642213615820,
  1455164172117664,1458737112376798,1461389540298720,1463147981292728,1464037162767262,
  1464080173979950,1463298606482080,1461712677846130,1459341340917556,1456202380466398,
  1452312498813442,1447687391756606,1442341815915588,1436289648438438,1429543939866146,
  1422116960825406,1414020243111104,1405264615625424,1395860235556816,1385816615106896,
  1375142644004782,1363846607984150,1351936203337034,1339418547598050,1326300186352092,
  1312587096095304,1298284683011924,1283397777455910,1267930623843778,1251886865570706,
  1235269524452164,1218080974063354,1200322906193070],
 [1181996289439606,1163101318744656,1143637354374296,1123602848497548,1102995257060988,
  1081810934082616,1060045004750072,1037691212751866,1014741736019592,991186963406600,
  967015222621984,942212446757718,916761762669854,890642978822900,863831942256662,836299722971062,
  808011567492058,778925538854766,748990723051954,718144824219218,686310878555666,653392664918774,
  619268130238464,583779685018916,546719357663194,507805075079430,466640660763580,422643541281258,
  374901500853058,321849645458842,260381855638708,182342139047098]]
private def pvo_r96_0 : List ℤ := pzigCatZ 45
 [
 [9044312535716,31263137878356,75680933975140,148138989289278,248667756653602,369668425028688,
  496675621219526,611614547036916,697370362597660,742006256350926,741249921044364,698672034772044,
  623865528985866,529523296899616,428447506789448,331277268201128,245293240238108,174252674914778,
  118952864628750,78143160402964,49462558417328,30200947909648,17805735572112,10145801587186,
  5591804924924,2983142114804,1541480777906,771973949212,374887214922,176621075396,80764072992,
  35859049630,15464576492,6479983008,2638939280,1044753830,402183322,150571924,54833586,19426470,
  6696332,2246040,733104,232858,71976,21646,6326,1794,492,128,28,4]]
private def pvm_r96_0_1 : List ℤ := pzigCatZ 53
 [
 [79725765549048,208519531098576,382016376634630,566025943809732,719362654595594,809826641676964,
  824125837351960,768827697116670,664254683113752,535658350748068,405642312679914,289893971793526,
  196305676895588,126383870604496,77581367539294,45519035758300,25580959833838,13795220129292,
  7150393723082,3567300485830,1715167843428,795645237930,356463470092,154377827644,64681653372,
  26237384114,10310720212,3927756004,1451175644,520266368,181072106,61202380,20096924,6413172,
  1989392,600038,176010,50216,13934,3756,980,244,54,10]]
private def phbv_g41 : List ℤ := pzigCatZ 0
 [
 [367507815139358,514996928067216,624936375505416,714911781243940,791800434928290,859161593091158,
  919128362129934,973102659578182,1022066588487128,1066741238530584,1107675498671708,
  1145299297419078,1179957299716460,1211931187837634,1241454934182522,1268725591312512,
  1293911113495954,1317156153452072,1338586442160380,1358312154677440,1376430535858116,
  1393027976341290,1408181673742550,1421960976421850,1434428481213164,1445640938217538,
  1455650002682950,1464502864502496,1472242778880326,1478909516514776,1484539747731088,
  1489167372014024,1492823802098000,1495538209993434,1497337740935758,1498247700145204,
  1498291716412092,1497491885823108,1495868898380006,1493442149804312,1490229840447422,
  1486249062917594,1481515879780538,1476045392477732,1469851802428150,1462948465128172,
  1455347937935418,1447062022111224,1438101799599556,1428477664934524,1418199352591836,
  1407275960029224,1395715966595260,1383527248423234,1370717089365050,1357292187957986,
  1343258660352524,1328622039060618,1313387267308364,1297558688692662,1281140031744858,
  1264134388891964,1246544189173134,1228371163909632],
 [1209616304333238,1190279809940904,1170361026049870,1149858368660598,1128769234272096,
  1107089891705760,1084815352238218,1061939213365122,1038453470237758,1014348287123314,
  989611718981420,964229370198952,938183973352816,911454865086656,884017328051770,855841756233242,
  826892584063556,797126894625856,766492584192056,734925901214074,702348083457854,668660661356396,
  633738729793770,597421016839398,559494691169912,519671088418106,477544774520464,432519562897554,
  383661921786458,329370389881228,266466266220218,186602975262250]]
private def pvi_r96_1 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r96_s0 pvo_r96_0
private def pvo_r96_1 : List ℤ := pzigCatZ 9
 [
 [11,3,7,19,63,411,2039,10891,49525,215893,863717,3254773,11501563,38378267,121138337,362785731,
  1033054275,2802660629,7256910979,17961411503,42553913405,96624894219,210511351521,440492476885,
  886086447789,1714943641161,3195866777973,5738417818473,9934215794725,16590606093911,
  26742725469177,41626641927045,62596284613527,90972343987201,127823369297153,173697215407141,
  228341598352047,290470257266861,357639374000723,426291720152607,492001159939933,549910573540201,
  595310433535433,624265320713933,634173885607325,624152368623201,595163718180781,549866344253497,
  492215142419853,426897132702479,358712296127553,292011103378885,230276054272343,175894211158777,
  130123384486517,93217684436455,64655984212303,43411498251125,28209419011361,17736732086089,
  10787692244213,6345011150545,3607829043099,1982516064699],
 [1052393111545,539446003803,266887746779,127380947881,58619370533,25994640521,11100825037,
  4561982939,1802809711,684516925,249495089,87206471,29198677,9353407,2862643,835749,232339,61369,
  15359,3625,797,159,25,1]]
private def pvm_r96_1_1 : List ℤ := pzigCatZ 22
 [
 [11115437,83399211,437422245,1851740623,6710315665,21496596153,62128380533,164280337635,
  401510867287,914129073573,1950632477915,3920525077905,7452048941779,13441316619259,
  23072198986677,37781968946823,59149539983971,88693869959323,127590150715999,176337717614291,
  234439533495331,300169795046611,370505474714051,441275202324479,507537021567579,564144346063011,
  606410753500087,630753470020407,635192545923463,619609895727095,585722772990129,536786338379293,
  477093879981525,411377736590247,344222269174797,279583332318035,220474162426137,168836391108739,
  125577748424707,90732531145217,63690122955597,43439510283449,28789688173271,18541904508345,
  11605240400195,7059023109739,4172778014559,2397105554487,1338174403349,725898627975,
  382597793381,195915672505,97455089291,47085602065,22092794343,10064994515,4451321089,1910643021,
  795753627,321490697,125955241,47837221,17604485,6273869],
 [2163545,721223,232097,71985,21471,6141,1677,431,101,19,1]]
private def phbv_g42 : List ℤ := pzigCatZ 0
 [
 [347812964541698,487398093052808,591445853558408,676599451159838,749367619552212,813118873676440,
  869872006138276,920953805303314,967293743034902,1009574265601708,1048314846847870,
  1083922375288268,1116723045172182,1146983443338502,1174925003538244,1200734218228782,
  1224570040960422,1246569372471132,1266851205780702,1285519811632402,1302667223501066,
  1318375202326136,1332716808680552,1345757674525508,1357557042112454,1368168620288032,
  1377641296080474,1386019730462792,1393344860580178,1399654325807690,1404982831297180,
  1409362459850174,1412822940783526,1415391882771134,1417094976327382,1417956170558394,
  1417997827980750,1417240860545430,1415704849470984,1413408151056586,1410367990291512,
  1406600543786174,1402121013308726,1396943691009998,1391082017250804,1384548631802590,
  1377355419070532,1369513547882942,1361033506299186,1351925131807276,1342197637209534,
  1331859632428290,1320919142401366,1309383621177774,1297259962265682,1284554505225808,
  1271273038442354,1257420797938348,1243002462030964,1228022141542486,1212483365191174,
  1196389059679986,1179741523875158,1162542396315944],
 [1144792615113726,1126492369074356,1107641038599714,1088237124577254,1068278163028366,
  1047760622729384,1026679782304074,1005029582360158,982802447031088,959989067683832,
  936578139416204,912556038080172,887906421618860,862609734031186,836642582578346,809976947840364,
  782579170218824,754408632726912,725416023890468,695541008625402,664709045588662,632826942225954,
  599776487122806,565405050958258,529511208101406,491821763792352,451953011296852,409340713847494,
  363101367919788,311719334984494,252186261588118,176602867597940]]
private def pvi_r96_2 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r96_s1 pvo_r96_1
private def pvo_r96_2 : List ℤ := pzigCatZ 0
 [
 [2399,2444,147,1893,1358,894,1775,206,1582,1075,899,1558,14,1521,826,1040,1367,235,1418,235,2395,
  5698,15355,52612,176741,559688,1698365,4971068,14024573,38090440,99515751,249910994,602638475,
  1393634974,3085903809,6530280902,13176138869,25276653398,45938377973,78740438964,126560623307,
  189185543464,260320816047,323952296466,353521741115,328257681776,187108234179,100456356914,
  399069742040,302597744682,1755143790992,3312777113772,7001878532390,14565386447866,
  26399686760818,46578904970768,77752170562678,121337163691806,180557673708600,255316702045876,
  341691297941916,435209926926444,528224645069004,609519257325168],
 [669384826393460,701168551367094,700091845138486,665415641496378,602541820962602,520584618311664,
  428871875237900,336098692650520,250321917493042,177569840541012,120338643374724,77859658392814,
  47736130947986,27361778150720,14421033175804,6865304443078,2892246598466,1046242214124,
  305256477170,58237023682,3439152611,10002753413,5981428159,2559490575,900036009,271695729,
  71560565,16503369,3314943,571555,82217,9319,713]]
private def pvm_r96_2_1 : List ℤ := pzigCatZ 0
 [
 [1083,2218,2427,1166,868,1915,1022,906,1725,570,1216,1487,47,1500,1021,729,1524,311,1269,1178,
  522,1473,424,1276,1371,414,2009,12618,46947,158622,521765,1645800,5187679,14875256,43416273,
  119566064,288517203,890224332,1346668319,6237790936,2528740939,40165461898,22774745450,
  228200603974,280446195734,1110028121776,1769176077936,4562231953872,7914714849166,
  15805608576716,27195901981008,46159286679420,74417021186264,113249993518086,166224076480328,
  231832034324572,308820777005634,394547080270774,481095227205094,561136616521934,627459972342518,
  671047574325460,686450706067924,673110456614982],
 [632178300115528,567630135140340,487741846221906,401788723615650,316882337949336,238480541638514,
  171209986321600,117756235700164,77898883681630,49387681870848,29601651262592,16437210938682,
  8267606947464,3674443457810,1393027842016,417715089550,74038545548,14669367249,22299984809,
  13576661729,6248091703,2427320391,828447365,252906489,69616247,17316337,3883163,779863,138623,
  21389,2767,279,13]]
private def phbv_g43 : List ℤ := pzigCatZ 0
 [
 [280355674255062,392868682133524,476736688864422,545374999406558,604029997907926,655416885852586,
  701162917023074,742337553126552,779689997722156,813770338653934,844997299358554,873698853533274,
  900137931022636,924529414940792,947051792621164,967855386863526,987068322649742,
  1004800949226710,1021149181271842,1036197066527792,1050018788850602,1062680251888618,
  1074240346333890,1084751975023896,1094262890351564,1102816384492432,1110451862980960,
  1117205324927244,1123109767838888,1128195531046072,1132490588739640,1136020801357158,
  1138810132302872,1140880835630470,1142253619255458,1142947787426038,1142981365515192,
  1142371209663188,1141133103369458,1139281842783536,1136831312159240,1133794550701498,
  1130183811840724,1126010615807598,1121285796244914,1116019541478028,1110221430967070,
  1103900467379312,1097065104646192,1089723272304168,1081882396359950,1073549416867030,
  1064730802350400,1055432561168434,1045660249853884,1035418978428518,1024713412636634,
  1013547772990160,1001925830460570,989850898588382,977325821707448,964352958895386,
  950934163160162,937070755251212],
 [922763491336010,908012523602066,892817352620482,877176770027128,861088789724716,844550565359918,
  827558291253378,810107083213932,792190834691824,773802042435722,754931594095602,735568507886436,
  715699611244686,695309140997532,674378241358304,652884327190220,630800267073892,608093321566328,
  584723743007162,560642898122456,535790702641008,510092038427328,483451620819292,455746422498914,
  426814083737482,396434395086468,364298068591818,329950299529460,292678937256472,251262296829768,
  203275486003122,142351266537858]]
private def pvi_r96_3 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r96_s2 pvo_r96_2
private def pvo_r96_3 : List ℤ := pzigCatZ 0
 [
 [2714,2023,775,2066,407,1673,1206,960,1631,119,1614,711,1219,1302,532,1547,290,1246,599,1605,324,
  17708,83537,256266,800417,2382710,6836009,18894678,50267103,128625646,316338065,747037030,
  1691886083,3669326648,7606592111,15038464072,28275926173,50386830758,84718206273,133624517090,
  196175495807,265114781340,324326746607,348893518904,312062987863,197153072866,14397269507,
  161636898381,347435843380,94365882551,573521577058,1438228608620,2716912809678,6798374643616,
  13492628129836,25232515165264,45787723289138,76647337063630,121062205614306,182074553913792,
  258354845403874,346968768358024,443317104479228,537971377658030],
 [619517462441424,678711986962024,708127008370796,702659677638260,662862167037358,595384800040242,
  509569019602294,414924096811382,320794214594518,235565953950538,164743153299382,109931418424776,
  69783047205810,41746396502538,23207702019462,11797812172828,5390442853546,2167763439286,
  742272942114,200939218864,32414814314,5246509011,7354940259,3926986285,1554405375,508437689,
  142343787,34493807,7224479,1291753,191943,22419,1777]]
private def phbv_g44 : List ℤ := pzigCatZ 0
 [
 [359847106837952,504261806038458,611909563333082,700009429806130,775295337852702,841252351226610,
  899969111676562,952818313735022,1000761588494016,1044504994497610,1084585979106742,
  1121425508960986,1155361064455952,1186668456192376,1215576779410474,1242278979106760,
  1266939508539252,1289700005138132,1310683579017948,1329998108633840,1347738811769586,
  1363990278249340,1378828096502738,1392320169321682,1404527788707792,1415506521805044,
  1425306947106658,1433975270831398,1441553846527752,1448081615872998,1453594484798658,
  1458125646154004,1461705857874332,1464363683878874,1466125703560048,1467016694650226,
  1467059793397086,1466276635293910,1464687479058924,1462311316109422,1459165967410084,
  1455268169273380,1450633649440496,1445277194563032,1439212710031086,1432453272945424,
  1425011178905278,1416897983174438,1408124536693510,1398701017322316,1388636956621212,
  1377941262411224,1366622237288724,1354687593208832,1342144462191404,1328999403142564,
  1315258404721508,1300926884114856,1286009681507052,1270511049952626,1254434640261604,
  1237783480399296,1220559948771478,1202765740609988],
 [1184401826484358,1165468401733020,1145964825320092,1125889546264538,1105240015335402,
  1084012579130578,1062202352916740,1039803067649882,1016806885342530,993204175287934,
  968983241440350,944129988263518,918627508274148,892455568843994,865589967858016,838001716439312,
  809655990385392,780510767383450,750515029808730,719606355015542,687707622570290,654722415506210,
  620528432357204,584967762909544,547832012313374,508838533416424,467590343436938,423503683317542,
  375664480784970,322504657028598,260911771176612,182713232234290]]
private def pvi_r96_4 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r96_s3 pvo_r96_3
private def pvo_r96_4 : List ℤ := pzigCatZ 0
 [
 [3005,1180,1762,1569,957,1786,214,1749,504,1476,1091,939,1484,274,1579,502,1186,955,648,9363,
  49452,178201,555494,1651615,4774346,13242109,35373442,90894997,224547920,532927541,1213965102,
  2650919217,5540926034,11065010225,21061968562,38103810719,65279008272,105407209789,159423524038,
  223921223289,288459315466,334192346905,336217449248,271908529711,135098545306,49446385278,
  219507069177,297212599280,226933870711,959943804,123301787146,562110366795,622635691129,
  1904688367155,5016604399177,9977671243077,20198605017013,38064824233099,65566294239833,
  107218531994807,165596964759161,239985324526581,328937930400109,427678246721313],
 [526172288644909,613115395901329,678556000342835,713414846852989,711658040831739,673838623662763,
  606584990137995,519220288954677,421856801554145,324867417062255,237348772231949,164936080649733,
  109105465046053,68418704021429,40276693466307,21958366016343,10920255418487,4873598018147,
  1912928764969,639326871543,170229244963,23187377931,7561412229,5399736687,2722442657,1031748725,
  319375747,83536911,18618379,3509311,546051,66481,5493]]
private def phbv_g45 : List ℤ := pzigCatZ 0
 [
 [185215148769382,259546134036836,314952986011312,360298438469588,399048480901814,432996893470080,
  463218710778984,490420465734344,515097114784010,537612069876546,558241957921046,577203452602786,
  594670256809726,610784331670564,625663593678706,639407352611980,652100253404504,663815197566956,
  674615550505778,684556837814304,693688068573484,702052781599018,709689882642750,716634321619422,
  722917645836162,728568455986546,733612785080068,738074415694154,741975147417120,745335023729692,
  748172525598706,750504737553674,752347490861416,753715487517440,754622408071146,755081005748280,
  755103188894010,754700093407530,753882146554858,752659123315740,751040196231962,749033979569262,
  746648568476576,743891573719208,740770152472656,737291035587658,733460551672104,729284648279446,
  724768910444384,719918576763496,714738553179706,709233424594118,703407464395604,697264641966960,
  690808628195330,684042798983288,676970236724390,669593729672332,661915769094838,653938544060852,
  645663933660994,637093496404514,628228456469048,619069686399104],
 [609617685751790,599872555068796,589833964405672,579501115464536,568872696143160,557946826016768,
  546720990888104,535191964048110,523355711244492,511207275503168,498740636809490,485948540118762,
  472822283062744,459351451804062,445523589390156,431323775097630,416734084731112,401732889190994,
  386293929444540,370385076236328,353966635284230,336988980281674,319389162037720,301085903356656,
  281971942342016,261901799057004,240671144430792,217979514686950,193356432145206,165994798611150,
  134292624828358,94043436357676]]
private def pvi_r96_5 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r96_s4 pvo_r96_4
private def pvo_r96_5 : List ℤ := pzigCatZ 0
 [
 [3090,645,2087,1040,1518,1407,963,1634,334,1691,310,1496,913,1105,1380,416,1559,1608,7623,39254,
  146645,468528,1400905,4044638,11266085,30150122,77613615,191542714,447220363,930887826,
  1318780539,994679195,11322235936,18073241199,33555850810,57846737795,94301563966,144338582767,
  205863116592,270614234663,322405881050,338271711975,294761997540,180063054393,8549420626,
  170803744630,283207422921,263787656378,98885798203,131654522307,257672483370,330034942151,
  335138690047,733580158737,2783201129833,5826051061617,12281946150237,25025358116977,
  45551631952041,77917548279093,126232704857343,191214468520493,272526855021015,367866866665361],
 [469409688959305,565946018537607,646667886030991,701259909222023,720941910529039,702476864581163,
  649716495956251,570933488734073,476123413009051,376135230545203,281476983927139,199954749909279,
  135080666948917,86613925865111,52324714497679,29430325563581,15195044925979,7092931832919,
  2942139756947,1058257060411,317462710655,63618890557,13581970953,6537785137,3438985857,
  1413797369,466060339,127763753,29544901,5740993,916921,114235,9645]]
private def phbv_g46 : List ℤ := pzigCatZ 0
 [
 [193533870100786,271203344454242,329098730247300,376480820557030,416971275729334,452444441459940,
  484023636272746,512447126170966,538232097991212,561758285903786,583314741191192,603127869183344,
  621379174429820,638216994077040,653764540699508,668125584457332,681388572012638,693629679162016,
  704915117294870,715302905871488,724844255158244,733584659465724,741564771952012,748821112266310,
  755386644626072,761291254291508,766562143514216,771224163038222,775300091554796,778810872774108,
  781775817713966,784212778235496,786138296648314,787567735270826,788515389098274,788994584152592,
  789017763628314,788596563580492,787741879603584,786463925709086,784772286412750,782675962879968,
  780183413843800,777302591898156,774040975674678,770405598332378,766403072721154,762039613521852,
  757321056614456,752252875880972,746840197608998,741087812625100,735000186252404,728581466153880,
  721835488090264,714765779588840,707375561485256,699667747264358,691644940086236,683309427339304,
  674663172511334,665707804110190,656444601296012,646874475802624],
 [636997949624154,626815127818006,616325665620662,605528728879624,594422946561132,583006353783336,
  571276323426752,559229483858472,546861619632488,534167551138032,521140987978560,507774349257540,
  494058541750066,479982683893462,465533759245748,450696176936716,435451207726772,419776251070648,
  403643868541928,387020487837338,369864631852592,352124445373724,333734151920652,314608823827686,
  294636381655988,273664811407908,251480606811878,227769809113100,202040809677700,173450260441802,
  140324220679090,98267287081038]]
private def pvi_r96_6 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r96_s5 pvo_r96_5
private def pvo_r96_6 : List ℤ := pzigCatZ 0
 [
 [3121,50,2250,357,1879,760,1554,1133,1127,1450,604,1593,4,1588,643,1397,2518,7159,32788,124619,
  406082,1225109,3541744,9874645,26466830,67978359,166001074,375259095,727045172,923137207,
  575547223,7081800964,18897590925,28879025338,52023120777,80914325206,95835937201,6159044571,
  347120371248,290609042933,338603491758,308659154687,213812907846,56985775649,123072501999,
  259437316528,282019821637,161295226626,56563992644,242579007325,268904371648,119004837545,
  277701249459,113323011803,1334797116709,3207071801535,6831112501443,15275849049115,
  29910115678569,53773493884163,91802778519319,146316831837149,217920951195953,306434275005329],
 [406967932553431,509498542201407,602837414540743,675898612631115,717824668040749,721546081252527,
  687200870954949,621047108870115,532417366294045,432219541242943,331971360192321,241559197107399,
  166887949362653,109457569665037,67815178317899,39298513782669,21026315587143,10239644619371,
  4469141096009,1713855993785,563335968701,139718567783,29567236723,9346012389,4412108577,
  1910446797,672184679,194416837,46911263,9437349,1552131,198375,17143]]
private def phbv_g47 : List ℤ := pzigCatZ 0
 [
 [76275416069020,106886447973082,129704131707420,148378323727206,164336389948294,178317046016288,
  190763013340856,201965256736244,212127609470124,221399732073858,229895545210670,237704279570412,
  244897469582852,251533577767006,257661164565448,263321127791746,268548325974536,273372781458622,
  277820589424518,281914616456096,285675045503106,289119806747312,292264922379278,295124785494316,
  297712387923774,300039508022814,302116866721352,303954258175006,305560659903588,306944326225616,
  308112867984180,309073320940694,309832204737156,310395573958370,310769062536574,310957922513006,
  310967057989676,310801054959410,310464207585292,309960541405470,309293833861722,308467632486248,
  307485271028240,306349883757730,305064418147118,303631646099480,302054173865994,300334450771770,
  298474776849218,296477309460392,294344068973714,292076943545966,289677693046772,287147952149788,
  284489232602006,281702924669694,278790297746056,275752500091436,272590557661234,269305371959168,
  265897716833484,262368234110420,258717427931556,254945657628710],
 [251053128929796,247039883239954,242905784681256,238650504498182,234273502339988,229774003808988,
  225150973506930,220403082608510,215528669725480,210525693473732,205391674687144,200123625588768,
  194717962363976,189170396379884,183475797606654,177628021382832,171619686155296,165441884614992,
  159083802750966,152532209073558,145770756659182,138779008371850,131531040437174,123993381230608,
  116121858092216,107856559385278,99113338186626,89768457319722,79628164377960,68360079688318,
  55304471053488,38729025592144]]
private def pvi_r96_7 : List ℤ := rkmApplyMaskBits rkmMkHiHiB_m128_r96_s6 pvo_r96_6
private def pvo_r96_7 : List ℤ := pzigCatZ 0
 [
 [3120,188,2259,70,1946,457,1701,852,1370,1231,929,1484,376,1619,234,1850,3595,12522,52947,188568,
  595865,1769080,5046861,13866630,36557565,91957222,217306989,461995468,783744545,613545300,
  2014016614,10078801533,22466988778,34384549565,60143777470,86189384415,85112724896,37194372193,
  389648649148,285941328431,339910772542,286017663191,172626744148,4789965931,168967153191,
  278490117048,261403624761,107181130554,115035788826,267822286429,242605315890,40353735999,
  282389285969,8269766516,936466538423,2516056565347,5312987057237,12339247008825,25023161583813,
  45946493181285,80119193669293,130466493542573,197944133141785,283032159761753],
 [382058786784111,485768815838717,583014894917097,662542042416715,712915753829367,725695918362153,
  699406220414269,639240122643973,554080219283019,454723174278123,352937949143477,259334875660137,
  180795306665175,119634303672629,74833205312073,43850097134595,23773106487925,11759387389061,
  5228439740017,2051046486173,694874922219,183035869181,40037614169,11329971851,4932108325,
  2142321623,770908547,227826243,55956427,11421593,1901501,245599,21425]]
private abbrev pl_r96 : List ℕ := [1, 1, 1, 1, 1, 1, 1, 1]
private abbrev ptau_r96 : List ℕ :=
  [14578303, 20720775, 13335033, 632279, 811554, 417711, 436472, 172022]
private abbrev pnsub_r96 : List ℕ := [18, 25, 17, 1, 1, 1, 1, 1]
private def pwalks_r96 : List RkmSegWalk := [ ⟨phbv_g40, pvi0, pvo_r96_0⟩,
  ⟨phbv_g41, pvi_r96_1, pvo_r96_1⟩, ⟨phbv_g42, pvi_r96_2, pvo_r96_2⟩,
  ⟨phbv_g43, pvi_r96_3, pvo_r96_3⟩, ⟨phbv_g44, pvi_r96_4, pvo_r96_4⟩,
  ⟨phbv_g45, pvi_r96_5, pvo_r96_5⟩, ⟨phbv_g46, pvi_r96_6, pvo_r96_6⟩,
  ⟨phbv_g47, pvi_r96_7, pvo_r96_7⟩]
private abbrev dP_0 : Prop := rkmAllTrueF [ bSlideChk 14 97 phbv_g40 pvi0 pvm_r96_0_1, bSlideChk 11
  97 phbv_g41 pvm_r96_1_1 pvo_r96_1, bSlideChk 12 58 phbv_g26 pvi_r57_2 pvo_r57_2, bSlideChk 13 51
  phbv_g18 pvi_r50_2 pvo_r50_2, rkmCheckRowFromWalks 128 64 44 pl_r44 ptau_r44 pnsub_r44
  rkmMasksHiHiB_m128_r44 pwalks_r44 rkmRowHiHiB_m128_r44, bSlideChk 7 51 phbv_g16 pvi0 pvo_r50_0,
  bSlideChk 5 58 phbv_g28 pvi_r57_4 pvo_r57_4, bSlideChk 4 58 phbv_g27 pvi_r57_3 pvo_r57_3,
  bSlideChk 3 65 phbv_g39 pvi_r64_7 pvo_r64_7, bSlideChk 3 45 phbv_g15 pvi_r44_7 pvo_r44_7,
  bSlideChk 2 51 phbv_g23 pvi_r50_7 pvo_r50_7, bSlideChk 1 97 phbv_g44 pvi_r96_4 pvo_r96_4,
  bSlideChk 2 45 phbv_g13 pvi_r44_5 pvo_r44_5, bSlideChk 1 39 phbv_g5 pvi_r38_5 pvo_r38_5,
  muxNatListEq [Nat.add (highdNatMin (Nat.mul 1 128) 50) 1] [51]] = true
private theorem bk_0 : dP_0 := by decide +kernel
private abbrev dP_1 : Prop := rkmAllTrueF [ bSlideChk 14 97 phbv_g41 pvi_r96_1 pvm_r96_1_1,
  bSlideChk 16 65 phbv_g33 pvi_r64_1 pvo_r64_1, rkmCheckRowFromWalks 128 64 96 pl_r96 ptau_r96
  pnsub_r96 rkmMasksHiHiB_m128_r96 pwalks_r96 rkmRowHiHiB_m128_r96, bSlideChk 9 65 phbv_g35
  pvi_r64_3 pvo_r64_3, rkmCheckRowFromWalks 128 64 50 pl_r50 ptau_r50 pnsub_r50
  rkmMasksHiHiB_m128_r50 pwalks_r50 rkmRowHiHiB_m128_r50, bSlideChk 5 65 phbv_g38 pvi_r64_6
  pvo_r64_6, bSlideChk 3 97 phbv_g42 pvm_r96_2_1 pvo_r96_2, bSlideChk 4 65 phbv_g37 pvi_r64_5
  pvo_r64_5, bSlideChk 3 58 phbv_g30 pvi_r57_6 pvo_r57_6, bSlideChk 3 45 phbv_g9 pvi_r44_1
  pvo_r44_1, bSlideChk 2 58 phbv_g31 pvi_r57_7 pvo_r57_7, bSlideChk 1 97 phbv_g47 pvi_r96_7
  pvo_r96_7, bSlideChk 1 45 phbv_g11 pvi_r44_3 pvo_r44_3, bSlideChk 1 45 phbv_g12 pvi_r44_4
  pvo_r44_4, bSlideChk 1 39 phbv_g6 pvi_r38_6 pvo_r38_6, muxNatListEq [Nat.add (highdNatMin
  (Nat.mul 1 128) 57) 1] [58]] = true
private theorem bk_1 : dP_1 := by decide +kernel
private abbrev dP_2 : Prop := rkmAllTrueF [ bSlideChk 14 97 phbv_g42 pvi_r96_2 pvm_r96_2_1,
  bSlideChk 15 65 phbv_g34 pvi_r64_2 pvo_r64_2, bSlideChk 16 58 phbv_g24 pvi0 pvo_r57_0,
  rkmCheckRowFromWalks 128 64 64 pl_r64 ptau_r64 pnsub_r64 rkmMasksHiHiB_m128_r64 pwalks_r64
  rkmRowHiHiB_m128_r64, bSlideChk 4 97 phbv_g40 pvm_r96_0_1 pvo_r96_0, bSlideChk 7 45 phbv_g10
  pvi_r44_2 pvo_r44_2, rkmCheckRowFromWalks 128 64 38 pl_r38 ptau_r38 pnsub_r38
  rkmMasksHiHiB_m128_r38 pwalks_r38 rkmRowHiHiB_m128_r38, bSlideChk 5 45 phbv_g8 pvi0 pvo_r44_0,
  bSlideChk 4 51 phbv_g22 pvi_r50_6 pvo_r50_6, bSlideChk 3 39 phbv_g0 pvi0 pvo_r38_0, bSlideChk 3
  39 phbv_g2 pvi_r38_2 pvo_r38_2, bSlideChk 1 97 phbv_g45 pvi_r96_5 pvo_r96_5, bSlideChk 2 39
  phbv_g4 pvi_r38_4 pvo_r38_4, bSlideChk 1 45 phbv_g14 pvi_r44_6 pvo_r44_6, muxNatListEq [Nat.add
  (highdNatMin (Nat.mul 1 128) 44) 1] [45], muxNatListEq [Nat.add (highdNatMin (Nat.mul 1 128) 96)
  1] [97]] = true
private theorem bk_2 : dP_2 := by decide +kernel
private abbrev dP_3 : Prop := rkmAllTrueF [ bSlideChk 18 65 phbv_g32 pvi0 pvo_r64_0, bSlideChk 20
  58 phbv_g25 pvi_r57_1 pvo_r57_1, bSlideChk 19 51 phbv_g17 pvi_r50_1 pvo_r50_1,
  rkmCheckRowFromWalks 128 64 57 pl_r57 ptau_r57 pnsub_r57 rkmMasksHiHiB_m128_r57 pwalks_r57
  rkmRowHiHiB_m128_r57, bSlideChk 6 65 phbv_g36 pvi_r64_4 pvo_r64_4, bSlideChk 7 51 phbv_g19
  pvi_r50_3 pvo_r50_3, bSlideChk 5 58 phbv_g29 pvi_r57_5 pvo_r57_5, bSlideChk 4 51 phbv_g20
  pvi_r50_4 pvo_r50_4, bSlideChk 4 51 phbv_g21 pvi_r50_5 pvo_r50_5, bSlideChk 4 39 phbv_g1
  pvi_r38_1 pvo_r38_1, bSlideChk 1 97 phbv_g43 pvi_r96_3 pvo_r96_3, bSlideChk 1 97 phbv_g46
  pvi_r96_6 pvo_r96_6, bSlideChk 2 39 phbv_g7 pvi_r38_7 pvo_r38_7, bSlideChk 1 39 phbv_g3 pvi_r38_3
  pvo_r38_3, muxNatListEq [Nat.add (highdNatMin (Nat.mul 1 128) 38) 1] [39], muxNatListEq [Nat.add
  (highdNatMin (Nat.mul 1 128) 64) 1] [65]] = true
private theorem bk_3 : dP_3 := by decide +kernel
private theorem pwalk_r38_0 : muxFastIterFullT16 3 39 phbv_g0 pvi0 = pvo_r38_0 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl4 (rkmTl4 bk_2)))))
private theorem pseg_r38_0 : muxFastIterFullT16 3
    (Nat.add (highdNatMin (Nat.mul 1 128) 38) 1)
    phbv_g0 pvi0 = pvo_r38_0 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_3))))))]; exact pwalk_r38_0
private theorem pwalk_r38_1 : muxFastIterFullT16 4 39 phbv_g1 pvi_r38_1 = pvo_r38_1 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl4 (rkmTl4 bk_3)))))
private theorem pseg_r38_1 : muxFastIterFullT16 4
    (Nat.add (highdNatMin (Nat.mul 1 128) 38) 1)
    phbv_g1 pvi_r38_1 = pvo_r38_1 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_3))))))]; exact pwalk_r38_1
private theorem pwalk_r38_2 : muxFastIterFullT16 3 39 phbv_g2 pvi_r38_2 = pvo_r38_2 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 bk_2))))))
private theorem pseg_r38_2 : muxFastIterFullT16 3
    (Nat.add (highdNatMin (Nat.mul 1 128) 38) 1)
    phbv_g2 pvi_r38_2 = pvo_r38_2 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_3))))))]; exact pwalk_r38_2
private theorem pwalk_r38_3 : muxFastIterFullT16 1 39 phbv_g3 pvi_r38_3 = pvo_r38_3 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_3))))))
private theorem pseg_r38_3 : muxFastIterFullT16 1
    (Nat.add (highdNatMin (Nat.mul 1 128) 38) 1)
    phbv_g3 pvi_r38_3 = pvo_r38_3 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_3))))))]; exact pwalk_r38_3
private theorem pwalk_r38_4 : muxFastIterFullT16 2 39 phbv_g4 pvi_r38_4 = pvo_r38_4 :=
    (bSlideChk_sound (rkmHd (rkmTl4 (rkmTl4 (rkmTl4 bk_2)))))
private theorem pseg_r38_4 : muxFastIterFullT16 2
    (Nat.add (highdNatMin (Nat.mul 1 128) 38) 1)
    phbv_g4 pvi_r38_4 = pvo_r38_4 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_3))))))]; exact pwalk_r38_4
private theorem pwalk_r38_5 : muxFastIterFullT16 1 39 phbv_g5 pvi_r38_5 = pvo_r38_5 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_0))))))
private theorem pseg_r38_5 : muxFastIterFullT16 1
    (Nat.add (highdNatMin (Nat.mul 1 128) 38) 1)
    phbv_g5 pvi_r38_5 = pvo_r38_5 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_3))))))]; exact pwalk_r38_5
private theorem pwalk_r38_6 : muxFastIterFullT16 1 39 phbv_g6 pvi_r38_6 = pvo_r38_6 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_1)))))))
private theorem pseg_r38_6 : muxFastIterFullT16 1
    (Nat.add (highdNatMin (Nat.mul 1 128) 38) 1)
    phbv_g6 pvi_r38_6 = pvo_r38_6 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_3))))))]; exact pwalk_r38_6
private theorem pwalk_r38_7 : muxFastIterFullT16 2 39 phbv_g7 pvi_r38_7 = pvo_r38_7 :=
    (bSlideChk_sound (rkmHd (rkmTl4 (rkmTl4 (rkmTl4 bk_3)))))
private theorem pseg_r38_7 : muxFastIterFullT16 2
    (Nat.add (highdNatMin (Nat.mul 1 128) 38) 1)
    phbv_g7 pvi_r38_7 = pvo_r38_7 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_3))))))]; exact pwalk_r38_7
private theorem pwalks_snd_r38 :
    RkmSegWalksSound 128 38 pl_r38 pnsub_r38 pwalks_r38 := by
  dsimp only [RkmSegWalksSound, pl_r38, pnsub_r38, pwalks_r38]
  exact ⟨pseg_r38_0, ⟨pseg_r38_1, ⟨pseg_r38_2, ⟨pseg_r38_3,
    ⟨pseg_r38_4, ⟨pseg_r38_5, ⟨pseg_r38_6, ⟨pseg_r38_7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Trajectory row certificate `(m = 128, r = 38)` (`FindAllJohnsonRampKickMuxHi128T1`). -/
theorem rkmTrajHiHiB_m128_r38 :
    rkmLo12EqHi 128 64 38 [1, 1, 1, 1, 1, 1, 1, 1]
      [3727215, 6152779, 4663358, 1165207, 2211204, 1227195, 623020, 1998915]
      [3, 4, 3, 1, 2, 1, 1, 2] rkmMasksHiHiB_m128_r38 rkmRowHiHiB_m128_r38 :=
  rkmCheckRowFromWalks_sound pwalks_snd_r38 (rkmHd (rkmTl (rkmTl (rkmTl4 bk_2))))
private theorem pwalk_r44_0 : muxFastIterFullT16 5 45 phbv_g8 pvi0 = pvo_r44_0 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 bk_2))))))
private theorem pseg_r44_0 : muxFastIterFullT16 5
    (Nat.add (highdNatMin (Nat.mul 1 128) 44) 1)
    phbv_g8 pvi0 = pvo_r44_0 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_2))))))]; exact pwalk_r44_0
private theorem pwalk_r44_1 : muxFastIterFullT16 3 45 phbv_g9 pvi_r44_1 = pvo_r44_1 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl4 (rkmTl4 bk_1)))))
private theorem pseg_r44_1 : muxFastIterFullT16 3
    (Nat.add (highdNatMin (Nat.mul 1 128) 44) 1)
    phbv_g9 pvi_r44_1 = pvo_r44_1 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_2))))))]; exact pwalk_r44_1
private theorem pwalk_r44_2 : muxFastIterFullT16 7 45 phbv_g10 pvi_r44_2 = pvo_r44_2 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl4 bk_2))))
private theorem pseg_r44_2 : muxFastIterFullT16 7
    (Nat.add (highdNatMin (Nat.mul 1 128) 44) 1)
    phbv_g10 pvi_r44_2 = pvo_r44_2 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_2))))))]; exact pwalk_r44_2
private theorem pwalk_r44_3 : muxFastIterFullT16 1 45 phbv_g11 pvi_r44_3 = pvo_r44_3 :=
    (bSlideChk_sound (rkmHd (rkmTl4 (rkmTl4 (rkmTl4 bk_1)))))
private theorem pseg_r44_3 : muxFastIterFullT16 1
    (Nat.add (highdNatMin (Nat.mul 1 128) 44) 1)
    phbv_g11 pvi_r44_3 = pvo_r44_3 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_2))))))]; exact pwalk_r44_3
private theorem pwalk_r44_4 : muxFastIterFullT16 1 45 phbv_g12 pvi_r44_4 = pvo_r44_4 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_1))))))
private theorem pseg_r44_4 : muxFastIterFullT16 1
    (Nat.add (highdNatMin (Nat.mul 1 128) 44) 1)
    phbv_g12 pvi_r44_4 = pvo_r44_4 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_2))))))]; exact pwalk_r44_4
private theorem pwalk_r44_5 : muxFastIterFullT16 2 45 phbv_g13 pvi_r44_5 = pvo_r44_5 :=
    (bSlideChk_sound (rkmHd (rkmTl4 (rkmTl4 (rkmTl4 bk_0)))))
private theorem pseg_r44_5 : muxFastIterFullT16 2
    (Nat.add (highdNatMin (Nat.mul 1 128) 44) 1)
    phbv_g13 pvi_r44_5 = pvo_r44_5 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_2))))))]; exact pwalk_r44_5
private theorem pwalk_r44_6 : muxFastIterFullT16 1 45 phbv_g14 pvi_r44_6 = pvo_r44_6 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_2))))))
private theorem pseg_r44_6 : muxFastIterFullT16 1
    (Nat.add (highdNatMin (Nat.mul 1 128) 44) 1)
    phbv_g14 pvi_r44_6 = pvo_r44_6 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_2))))))]; exact pwalk_r44_6
private theorem pwalk_r44_7 : muxFastIterFullT16 3 45 phbv_g15 pvi_r44_7 = pvo_r44_7 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl4 (rkmTl4 bk_0)))))
private theorem pseg_r44_7 : muxFastIterFullT16 3
    (Nat.add (highdNatMin (Nat.mul 1 128) 44) 1)
    phbv_g15 pvi_r44_7 = pvo_r44_7 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_2))))))]; exact pwalk_r44_7
private theorem pwalks_snd_r44 :
    RkmSegWalksSound 128 44 pl_r44 pnsub_r44 pwalks_r44 := by
  dsimp only [RkmSegWalksSound, pl_r44, pnsub_r44, pwalks_r44]
  exact ⟨pseg_r44_0, ⟨pseg_r44_1, ⟨pseg_r44_2, ⟨pseg_r44_3,
    ⟨pseg_r44_4, ⟨pseg_r44_5, ⟨pseg_r44_6, ⟨pseg_r44_7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Trajectory row certificate `(m = 128, r = 44)` (`FindAllJohnsonRampKickMuxHi128T1`). -/
theorem rkmTrajHiHiB_m128_r44 :
    rkmLo12EqHi 128 64 44 [1, 1, 1, 1, 1, 1, 1, 1]
      [7517247, 3730290, 9725635, 1000, 1325175, 2188018, 923660, 3381375] [5, 3, 7, 1, 1, 2, 1, 3]
      rkmMasksHiHiB_m128_r44 rkmRowHiHiB_m128_r44 :=
  rkmCheckRowFromWalks_sound pwalks_snd_r44 (rkmHd (rkmTl4 bk_0))
private theorem pwalk_r50_0 : muxFastIterFullT16 7 51 phbv_g16 pvi0 = pvo_r50_0 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl4 bk_0))))
private theorem pseg_r50_0 : muxFastIterFullT16 7
    (Nat.add (highdNatMin (Nat.mul 1 128) 50) 1)
    phbv_g16 pvi0 = pvo_r50_0 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_0))))))]; exact pwalk_r50_0
private theorem pwalk_r50_1 : muxFastIterFullT16 19 51 phbv_g17 pvi_r50_1 = pvo_r50_1 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl bk_3))))
private theorem pseg_r50_1 : muxFastIterFullT16 19
    (Nat.add (highdNatMin (Nat.mul 1 128) 50) 1)
    phbv_g17 pvi_r50_1 = pvo_r50_1 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_0))))))]; exact pwalk_r50_1
private theorem pwalk_r50_2 : muxFastIterFullT16 13 51 phbv_g18 pvi_r50_2 = pvo_r50_2 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl (rkmTl bk_0)))))
private theorem pseg_r50_2 : muxFastIterFullT16 13
    (Nat.add (highdNatMin (Nat.mul 1 128) 50) 1)
    phbv_g18 pvi_r50_2 = pvo_r50_2 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_0))))))]; exact pwalk_r50_2
private theorem pwalk_r50_3 : muxFastIterFullT16 7 51 phbv_g19 pvi_r50_3 = pvo_r50_3 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl4 bk_3))))
private theorem pseg_r50_3 : muxFastIterFullT16 7
    (Nat.add (highdNatMin (Nat.mul 1 128) 50) 1)
    phbv_g19 pvi_r50_3 = pvo_r50_3 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_0))))))]; exact pwalk_r50_3
private theorem pwalk_r50_4 : muxFastIterFullT16 4 51 phbv_g20 pvi_r50_4 = pvo_r50_4 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 bk_3))))))
private theorem pseg_r50_4 : muxFastIterFullT16 4
    (Nat.add (highdNatMin (Nat.mul 1 128) 50) 1)
    phbv_g20 pvi_r50_4 = pvo_r50_4 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_0))))))]; exact pwalk_r50_4
private theorem pwalk_r50_5 : muxFastIterFullT16 4 51 phbv_g21 pvi_r50_5 = pvo_r50_5 :=
    (bSlideChk_sound (rkmHd (rkmTl4 (rkmTl4 bk_3))))
private theorem pseg_r50_5 : muxFastIterFullT16 4
    (Nat.add (highdNatMin (Nat.mul 1 128) 50) 1)
    phbv_g21 pvi_r50_5 = pvo_r50_5 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_0))))))]; exact pwalk_r50_5
private theorem pwalk_r50_6 : muxFastIterFullT16 4 51 phbv_g22 pvi_r50_6 = pvo_r50_6 :=
    (bSlideChk_sound (rkmHd (rkmTl4 (rkmTl4 bk_2))))
private theorem pseg_r50_6 : muxFastIterFullT16 4
    (Nat.add (highdNatMin (Nat.mul 1 128) 50) 1)
    phbv_g22 pvi_r50_6 = pvo_r50_6 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_0))))))]; exact pwalk_r50_6
private theorem pwalk_r50_7 : muxFastIterFullT16 2 51 phbv_g23 pvi_r50_7 = pvo_r50_7 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 bk_0))))))
private theorem pseg_r50_7 : muxFastIterFullT16 2
    (Nat.add (highdNatMin (Nat.mul 1 128) 50) 1)
    phbv_g23 pvi_r50_7 = pvo_r50_7 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_0))))))]; exact pwalk_r50_7
private theorem pwalks_snd_r50 :
    RkmSegWalksSound 128 50 pl_r50 pnsub_r50 pwalks_r50 := by
  dsimp only [RkmSegWalksSound, pl_r50, pnsub_r50, pwalks_r50]
  exact ⟨pseg_r50_0, ⟨pseg_r50_1, ⟨pseg_r50_2, ⟨pseg_r50_3,
    ⟨pseg_r50_4, ⟨pseg_r50_5, ⟨pseg_r50_6, ⟨pseg_r50_7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Trajectory row certificate `(m = 128, r = 50)` (`FindAllJohnsonRampKickMuxHi128T1`). -/
theorem rkmTrajHiHiB_m128_r50 :
    rkmLo12EqHi 128 64 50 [1, 1, 1, 1, 1, 1, 1, 1]
      [9431622, 25909382, 17856452, 8804058, 4819570, 4452821, 4548241, 2209112]
      [7, 19, 13, 7, 4, 4, 4, 2] rkmMasksHiHiB_m128_r50 rkmRowHiHiB_m128_r50 :=
  rkmCheckRowFromWalks_sound pwalks_snd_r50 (rkmHd (rkmTl4 bk_1))
private theorem pwalk_r57_0 : muxFastIterFullT16 16 58 phbv_g24 pvi0 = pvo_r57_0 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl bk_2))))
private theorem pseg_r57_0 : muxFastIterFullT16 16
    (Nat.add (highdNatMin (Nat.mul 1 128) 57) 1)
    phbv_g24 pvi0 = pvo_r57_0 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_1)))))))]; exact pwalk_r57_0
private theorem pwalk_r57_1 : muxFastIterFullT16 20 58 phbv_g25 pvi_r57_1 = pvo_r57_1 :=
    (bSlideChk_sound (rkmHd (rkmTl bk_3)))
private theorem pseg_r57_1 : muxFastIterFullT16 20
    (Nat.add (highdNatMin (Nat.mul 1 128) 57) 1)
    phbv_g25 pvi_r57_1 = pvo_r57_1 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_1)))))))]; exact pwalk_r57_1
private theorem pwalk_r57_2 : muxFastIterFullT16 12 58 phbv_g26 pvi_r57_2 = pvo_r57_2 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl bk_0))))
private theorem pseg_r57_2 : muxFastIterFullT16 12
    (Nat.add (highdNatMin (Nat.mul 1 128) 57) 1)
    phbv_g26 pvi_r57_2 = pvo_r57_2 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_1)))))))]; exact pwalk_r57_2
private theorem pwalk_r57_3 : muxFastIterFullT16 4 58 phbv_g27 pvi_r57_3 = pvo_r57_3 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 bk_0))))))
private theorem pseg_r57_3 : muxFastIterFullT16 4
    (Nat.add (highdNatMin (Nat.mul 1 128) 57) 1)
    phbv_g27 pvi_r57_3 = pvo_r57_3 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_1)))))))]; exact pwalk_r57_3
private theorem pwalk_r57_4 : muxFastIterFullT16 5 58 phbv_g28 pvi_r57_4 = pvo_r57_4 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl (rkmTl4 bk_0)))))
private theorem pseg_r57_4 : muxFastIterFullT16 5
    (Nat.add (highdNatMin (Nat.mul 1 128) 57) 1)
    phbv_g28 pvi_r57_4 = pvo_r57_4 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_1)))))))]; exact pwalk_r57_4
private theorem pwalk_r57_5 : muxFastIterFullT16 5 58 phbv_g29 pvi_r57_5 = pvo_r57_5 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl (rkmTl4 bk_3)))))
private theorem pseg_r57_5 : muxFastIterFullT16 5
    (Nat.add (highdNatMin (Nat.mul 1 128) 57) 1)
    phbv_g29 pvi_r57_5 = pvo_r57_5 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_1)))))))]; exact pwalk_r57_5
private theorem pwalk_r57_6 : muxFastIterFullT16 3 58 phbv_g30 pvi_r57_6 = pvo_r57_6 :=
    (bSlideChk_sound (rkmHd (rkmTl4 (rkmTl4 bk_1))))
private theorem pseg_r57_6 : muxFastIterFullT16 3
    (Nat.add (highdNatMin (Nat.mul 1 128) 57) 1)
    phbv_g30 pvi_r57_6 = pvo_r57_6 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_1)))))))]; exact pwalk_r57_6
private theorem pwalk_r57_7 : muxFastIterFullT16 2 58 phbv_g31 pvi_r57_7 = pvo_r57_7 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 bk_1))))))
private theorem pseg_r57_7 : muxFastIterFullT16 2
    (Nat.add (highdNatMin (Nat.mul 1 128) 57) 1)
    phbv_g31 pvi_r57_7 = pvo_r57_7 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_1)))))))]; exact pwalk_r57_7
private theorem pwalks_snd_r57 :
    RkmSegWalksSound 128 57 pl_r57 pnsub_r57 pwalks_r57 := by
  dsimp only [RkmSegWalksSound, pl_r57, pnsub_r57, pwalks_r57]
  exact ⟨pseg_r57_0, ⟨pseg_r57_1, ⟨pseg_r57_2, ⟨pseg_r57_3,
    ⟨pseg_r57_4, ⟨pseg_r57_5, ⟨pseg_r57_6, ⟨pseg_r57_7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Trajectory row certificate `(m = 128, r = 57)` (`FindAllJohnsonRampKickMuxHi128T1`). -/
theorem rkmTrajHiHiB_m128_r57 :
    rkmLo12EqHi 128 64 57 [1, 1, 1, 1, 1, 1, 1, 1]
      [19717878, 24789701, 14954997, 4571130, 5576698, 5204442, 2975129, 2071756]
      [16, 20, 12, 4, 5, 5, 3, 2] rkmMasksHiHiB_m128_r57 rkmRowHiHiB_m128_r57 :=
  rkmCheckRowFromWalks_sound pwalks_snd_r57 (rkmHd (rkmTl (rkmTl (rkmTl bk_3))))
private theorem pwalk_r64_0 : muxFastIterFullT16 18 65 phbv_g32 pvi0 = pvo_r64_0 :=
    (bSlideChk_sound (rkmHd bk_3))
private theorem pseg_r64_0 : muxFastIterFullT16 18
    (Nat.add (highdNatMin (Nat.mul 1 128) 64) 1)
    phbv_g32 pvi0 = pvo_r64_0 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_3)))))))]; exact pwalk_r64_0
private theorem pwalk_r64_1 : muxFastIterFullT16 16 65 phbv_g33 pvi_r64_1 = pvo_r64_1 :=
    (bSlideChk_sound (rkmHd (rkmTl bk_1)))
private theorem pseg_r64_1 : muxFastIterFullT16 16
    (Nat.add (highdNatMin (Nat.mul 1 128) 64) 1)
    phbv_g33 pvi_r64_1 = pvo_r64_1 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_3)))))))]; exact pwalk_r64_1
private theorem pwalk_r64_2 : muxFastIterFullT16 15 65 phbv_g34 pvi_r64_2 = pvo_r64_2 :=
    (bSlideChk_sound (rkmHd (rkmTl bk_2)))
private theorem pseg_r64_2 : muxFastIterFullT16 15
    (Nat.add (highdNatMin (Nat.mul 1 128) 64) 1)
    phbv_g34 pvi_r64_2 = pvo_r64_2 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_3)))))))]; exact pwalk_r64_2
private theorem pwalk_r64_3 : muxFastIterFullT16 9 65 phbv_g35 pvi_r64_3 = pvo_r64_3 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl (rkmTl bk_1)))))
private theorem pseg_r64_3 : muxFastIterFullT16 9
    (Nat.add (highdNatMin (Nat.mul 1 128) 64) 1)
    phbv_g35 pvi_r64_3 = pvo_r64_3 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_3)))))))]; exact pwalk_r64_3
private theorem pwalk_r64_4 : muxFastIterFullT16 6 65 phbv_g36 pvi_r64_4 = pvo_r64_4 :=
    (bSlideChk_sound (rkmHd (rkmTl4 bk_3)))
private theorem pseg_r64_4 : muxFastIterFullT16 6
    (Nat.add (highdNatMin (Nat.mul 1 128) 64) 1)
    phbv_g36 pvi_r64_4 = pvo_r64_4 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_3)))))))]; exact pwalk_r64_4
private theorem pwalk_r64_5 : muxFastIterFullT16 4 65 phbv_g37 pvi_r64_5 = pvo_r64_5 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 bk_1))))))
private theorem pseg_r64_5 : muxFastIterFullT16 4
    (Nat.add (highdNatMin (Nat.mul 1 128) 64) 1)
    phbv_g37 pvi_r64_5 = pvo_r64_5 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_3)))))))]; exact pwalk_r64_5
private theorem pwalk_r64_6 : muxFastIterFullT16 5 65 phbv_g38 pvi_r64_6 = pvo_r64_6 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl4 bk_1))))
private theorem pseg_r64_6 : muxFastIterFullT16 5
    (Nat.add (highdNatMin (Nat.mul 1 128) 64) 1)
    phbv_g38 pvi_r64_6 = pvo_r64_6 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_3)))))))]; exact pwalk_r64_6
private theorem pwalk_r64_7 : muxFastIterFullT16 3 65 phbv_g39 pvi_r64_7 = pvo_r64_7 :=
    (bSlideChk_sound (rkmHd (rkmTl4 (rkmTl4 bk_0))))
private theorem pseg_r64_7 : muxFastIterFullT16 3
    (Nat.add (highdNatMin (Nat.mul 1 128) 64) 1)
    phbv_g39 pvi_r64_7 = pvo_r64_7 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_3)))))))]; exact pwalk_r64_7
private theorem pwalks_snd_r64 :
    RkmSegWalksSound 128 64 pl_r64 pnsub_r64 pwalks_r64 := by
  dsimp only [RkmSegWalksSound, pl_r64, pnsub_r64, pwalks_r64]
  exact ⟨pseg_r64_0, ⟨pseg_r64_1, ⟨pseg_r64_2, ⟨pseg_r64_3,
    ⟨pseg_r64_4, ⟨pseg_r64_5, ⟨pseg_r64_6, ⟨pseg_r64_7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Trajectory row certificate `(m = 128, r = 64)` (`FindAllJohnsonRampKickMuxHi128T1`). -/
theorem rkmTrajHiHiB_m128_r64 :
    rkmLo12EqHi 128 64 64 [1, 1, 1, 1, 1, 1, 1, 1]
      [20806197, 17724820, 16445970, 9400784, 6696938, 3478755, 4843920, 2552589]
      [18, 16, 15, 9, 6, 4, 5, 3] rkmMasksHiHiB_m128_r64 rkmRowHiHiB_m128_r64 :=
  rkmCheckRowFromWalks_sound pwalks_snd_r64 (rkmHd (rkmTl (rkmTl (rkmTl bk_2))))
private theorem pacc_r96_0_1 : muxFastIterFullT16 18 97 phbv_g40 pvi0 = pvo_r96_0 := bCh 18
    (bSlideChk_sound (rkmHd bk_0)) (rkmHd (rkmTl4 bk_2)) rfl
private theorem pwalk_r96_0 : muxFastIterFullT16 18 97 phbv_g40 pvi0 = pvo_r96_0 := pacc_r96_0_1
private theorem pseg_r96_0 : muxFastIterFullT16 18
    (Nat.add (highdNatMin (Nat.mul 1 128) 96) 1)
    phbv_g40 pvi0 = pvo_r96_0 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_2)))))))]; exact pwalk_r96_0
private theorem pacc_r96_1_1 : muxFastIterFullT16 25 97 phbv_g41 pvi_r96_1 = pvo_r96_1 := bCh 25
    (bSlideChk_sound (rkmHd bk_1)) (rkmHd (rkmTl bk_0)) rfl
private theorem pwalk_r96_1 : muxFastIterFullT16 25 97 phbv_g41 pvi_r96_1 = pvo_r96_1 :=
    pacc_r96_1_1
private theorem pseg_r96_1 : muxFastIterFullT16 25
    (Nat.add (highdNatMin (Nat.mul 1 128) 96) 1)
    phbv_g41 pvi_r96_1 = pvo_r96_1 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_2)))))))]; exact pwalk_r96_1
private theorem pacc_r96_2_1 : muxFastIterFullT16 17 97 phbv_g42 pvi_r96_2 = pvo_r96_2 := bCh 17
    (bSlideChk_sound (rkmHd bk_2)) (rkmHd (rkmTl (rkmTl (rkmTl4 bk_1)))) rfl
private theorem pwalk_r96_2 : muxFastIterFullT16 17 97 phbv_g42 pvi_r96_2 = pvo_r96_2 :=
    pacc_r96_2_1
private theorem pseg_r96_2 : muxFastIterFullT16 17
    (Nat.add (highdNatMin (Nat.mul 1 128) 96) 1)
    phbv_g42 pvi_r96_2 = pvo_r96_2 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_2)))))))]; exact pwalk_r96_2
private theorem pwalk_r96_3 : muxFastIterFullT16 1 97 phbv_g43 pvi_r96_3 = pvo_r96_3 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 bk_3))))))
private theorem pseg_r96_3 : muxFastIterFullT16 1
    (Nat.add (highdNatMin (Nat.mul 1 128) 96) 1)
    phbv_g43 pvi_r96_3 = pvo_r96_3 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_2)))))))]; exact pwalk_r96_3
private theorem pwalk_r96_4 : muxFastIterFullT16 1 97 phbv_g44 pvi_r96_4 = pvo_r96_4 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 bk_0)))))))
private theorem pseg_r96_4 : muxFastIterFullT16 1
    (Nat.add (highdNatMin (Nat.mul 1 128) 96) 1)
    phbv_g44 pvi_r96_4 = pvo_r96_4 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_2)))))))]; exact pwalk_r96_4
private theorem pwalk_r96_5 : muxFastIterFullT16 1 97 phbv_g45 pvi_r96_5 = pvo_r96_5 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 bk_2)))))))
private theorem pseg_r96_5 : muxFastIterFullT16 1
    (Nat.add (highdNatMin (Nat.mul 1 128) 96) 1)
    phbv_g45 pvi_r96_5 = pvo_r96_5 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_2)))))))]; exact pwalk_r96_5
private theorem pwalk_r96_6 : muxFastIterFullT16 1 97 phbv_g46 pvi_r96_6 = pvo_r96_6 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 bk_3)))))))
private theorem pseg_r96_6 : muxFastIterFullT16 1
    (Nat.add (highdNatMin (Nat.mul 1 128) 96) 1)
    phbv_g46 pvi_r96_6 = pvo_r96_6 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_2)))))))]; exact pwalk_r96_6
private theorem pwalk_r96_7 : muxFastIterFullT16 1 97 phbv_g47 pvi_r96_7 = pvo_r96_7 :=
    (bSlideChk_sound (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 bk_1)))))))
private theorem pseg_r96_7 : muxFastIterFullT16 1
    (Nat.add (highdNatMin (Nat.mul 1 128) 96) 1)
    phbv_g47 pvi_r96_7 = pvo_r96_7 := by
  rw [bDm (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 bk_2)))))))]; exact pwalk_r96_7
private theorem pwalks_snd_r96 :
    RkmSegWalksSound 128 96 pl_r96 pnsub_r96 pwalks_r96 := by
  dsimp only [RkmSegWalksSound, pl_r96, pnsub_r96, pwalks_r96]
  exact ⟨pseg_r96_0, ⟨pseg_r96_1, ⟨pseg_r96_2, ⟨pseg_r96_3,
    ⟨pseg_r96_4, ⟨pseg_r96_5, ⟨pseg_r96_6, ⟨pseg_r96_7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Trajectory row certificate `(m = 128, r = 96)` (`FindAllJohnsonRampKickMuxHi128T1`). -/
theorem rkmTrajHiHiB_m128_r96 :
    rkmLo12EqHi 128 64 96 [1, 1, 1, 1, 1, 1, 1, 1]
      [14578303, 20720775, 13335033, 632279, 811554, 417711, 436472, 172022]
      [18, 25, 17, 1, 1, 1, 1, 1] rkmMasksHiHiB_m128_r96 rkmRowHiHiB_m128_r96 :=
  rkmCheckRowFromWalks_sound pwalks_snd_r96 (rkmHd (rkmTl (rkmTl bk_1)))
end
end QuantumComputation.Specs.DickeSol
