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
# High-`m` Trajectory Part `0` (`FindAllJohnsonRampKickMuxHi1024T0`)

Certifies all `30` active `r = 3..32` Krotov rows for `m = 1024` (`15805` coords).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Prefix-kick masks for `(m = 1024, r = 3)`. -/
def rkmMasksHi_m1024_r3 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 3)`. -/
def rkmRowHi_m1024_r3 : List ℕ := [943656407, 53160483992, 945890589599]
/-- Prefix-kick masks for `(m = 1024, r = 4)`. -/
def rkmMasksHi_m1024_r4 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 4)`. -/
def rkmRowHi_m1024_r4 : List ℕ := [3029299, 548092332, 39357628342, 960091244462]
/-- Prefix-kick masks for `(m = 1024, r = 5)`. -/
def rkmMasksHi_m1024_r5 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 5)`. -/
def rkmRowHi_m1024_r5 : List ℕ := [2691, 1557044, 344651366, 31270630396, 968383158423]
/-- Prefix-kick masks for `(m = 1024, r = 6)`. -/
def rkmMasksHi_m1024_r6 : List (List Bool) := [[], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 6)`. -/
def rkmRowHi_m1024_r6 : List ℕ := [0, 828, 766779, 227914271, 25953380918, 973817937096]
/-- Prefix-kick masks for `(m = 1024, r = 7)`. -/
def rkmMasksHi_m1024_r7 : List (List Bool) := [[], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 7)`. -/
def rkmRowHi_m1024_r7 : List ℕ := [0, 0, 114, 351769, 155377593, 22190295980, 977653974414]
/-- Prefix-kick masks for `(m = 1024, r = 8)`. -/
def rkmMasksHi_m1024_r8 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 8)`. -/
def rkmRowHi_m1024_r8 : List ℕ := [0, 0, 0, 5, 138896, 107637539, 19385953674, 980506269725]
/-- Prefix-kick masks for `(m = 1024, r = 9)`. -/
def rkmMasksHi_m1024_r9 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 9)`. -/
def rkmRowHi_m1024_r9 : List ℕ := [0, 0, 0, 0, 149, 38361, 74908870, 17215509047, 982709543378]
/-- Prefix-kick masks for `(m = 1024, r = 10)`. -/
def rkmMasksHi_m1024_r10 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 10)`. -/
def rkmRowHi_m1024_r10 : List ℕ := [0, 0, 0, 0, 0, 363, 2533, 51824040, 15485639063,
  984462533774]
/-- Prefix-kick masks for `(m = 1024, r = 11)`. -/
def rkmMasksHi_m1024_r11 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 11)`. -/
def rkmRowHi_m1024_r11 : List ℕ := [0, 0, 0, 0, 0, 0, 563, 5196, 35251091, 14074614102,
  985890128774]
/-- Prefix-kick masks for `(m = 1024, r = 12)`. -/
def rkmMasksHi_m1024_r12 : List (List Bool) := [[], [], [], [], [], [false, false, false,
  false, false, false, false, true], [false, false, false, false, false, false, false, false,
  true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 12)`. -/
def rkmRowHi_m1024_r12 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 33, 30379, 23261042, 12901524286,
  987075183793]
/-- Prefix-kick masks for `(m = 1024, r = 13)`. -/
def rkmMasksHi_m1024_r13 : List (List Bool) := [[], [], [], [], [], [false, false, false,
  false, false, false, false, false, true], [false, false, false, false, false, false, false,
  false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 13)`. -/
def rkmRowHi_m1024_r13 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 171, 69834, 14614945, 11910993222,
  988074321328]
/-- Prefix-kick masks for `(m = 1024, r = 14)`. -/
def rkmMasksHi_m1024_r14 : List (List Bool) := [[], [], [], [], [], [false, false, false,
  false, false, false, false, false, false, true], [false, false, false, false, false, false,
  false, false, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 14)`. -/
def rkmRowHi_m1024_r14 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 429, 117883, 8486688,
  11063267027, 988928127440]
/-- Prefix-kick masks for `(m = 1024, r = 15)`. -/
def rkmMasksHi_m1024_r15 : List (List Bool) := [[], [], [], [], [], [false, false, false,
  false, false, false, false, false, false, false, true], [false, false, false, false, false,
  false, false, false, false, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 15)`. -/
def rkmRowHi_m1024_r15 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 909, 170995, 4311544,
  10330071183, 989665444800]
/-- Prefix-kick masks for `(m = 1024, r = 16)`. -/
def rkmMasksHi_m1024_r16 : List (List Bool) := [[], [], [], [false, false, false, false, false,
  false, false, false, true], [], [false, false, false, false, false, false, false, false,
  false, false, false, true], [false, false, false, false, false, false, false, false, false,
  false, true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 16)`. -/
def rkmRowHi_m1024_r16 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1733, 226869, 1686762,
  9689052266, 990309031761]
/-- Prefix-kick masks for `(m = 1024, r = 17)`. -/
def rkmMasksHi_m1024_r17 : List (List Bool) := [[], [], [], [], [false, false, false, false,
  false, false, false, false, false, false, false, true], [false, false, false, false, false,
  false, false, false, false, false, false, false, true], [false, false, false, false, false,
  false, false, false, false, false, false, true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 17)`. -/
def rkmRowHi_m1024_r17 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 3014, 283984, 325072,
  9124131838, 990875255440]
/-- Prefix-kick masks for `(m = 1024, r = 18)`. -/
def rkmMasksHi_m1024_r18 : List (List Bool) := [[], [], [], [], [false, false, false, false,
  false, false, false, false, false, false, false, true, true], [false, false, false, false,
  false, false, false, false, false, false, false, false, false, true], [false, false, false,
  false, false, false, false, false, false, false, false, false, true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 18)`. -/
def rkmRowHi_m1024_r18 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 4803, 341364,
  13809, 8622414333, 991377224960]
/-- Prefix-kick masks for `(m = 1024, r = 19)`. -/
def rkmMasksHi_m1024_r19 : List (List Bool) := [[], [], [], [], [false, false, false, false,
  false, false, false, false, false, false, false, false, false, true], [false, false, false,
  false, false, false, false, false, false, false, false, false, true, true, true], [false,
  false, false, false, false, false, false, false, false, false, false, false, false, true,
  true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 19)`. -/
def rkmRowHi_m1024_r19 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 7263, 398281,
  593630, 8174067453, 991824932556]
/-- Prefix-kick masks for `(m = 1024, r = 20)`. -/
def rkmMasksHi_m1024_r20 : List (List Bool) := [[], [false, false, false, false, false, false,
  false, false, true], [], [], [false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, true], [false, false, false, false, false, false, false,
  false, false, false, false, false, false, true, false, true, true], [false, false, false,
  false, false, false, false, false, false, false, false, false, false, true, false, false,
  false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 20)`. -/
def rkmRowHi_m1024_r20 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 96, 8, 82,
  1756464, 7770792641, 992227449747]
/-- Prefix-kick masks for `(m = 1024, r = 21)`. -/
def rkmMasksHi_m1024_r21 : List (List Bool) := [[], [false, false, false, false, false, false,
  false, false, false, true], [], [], [false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true, true], [false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, true, false, true, true],
  [false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, true, false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 21)`. -/
def rkmRowHi_m1024_r21 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 129, 4, 186,
  3649434, 7406187679, 992590161561]
/-- Prefix-kick masks for `(m = 1024, r = 22)`. -/
def rkmMasksHi_m1024_r22 : List (List Bool) := [[], [], [], [], [false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, true, true],
  [false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, false, true, true], [false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 22)`. -/
def rkmRowHi_m1024_r22 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 162, 3,
  1897, 6111478, 7075073290, 992918812117]
/-- Prefix-kick masks for `(m = 1024, r = 23)`. -/
def rkmMasksHi_m1024_r23 : List (List Bool) := [[], [], [], [], [false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, true,
  true], [false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, false, true, true], [false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 23)`. -/
def rkmRowHi_m1024_r23 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 203, 0,
  6116, 9083080, 6772825492, 993218084007]
/-- Prefix-kick masks for `(m = 1024, r = 24)`. -/
def rkmMasksHi_m1024_r24 : List (List Bool) := [[], [], [], [], [false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  true, true], [false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true, false, true, true], [false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 24)`. -/
def rkmRowHi_m1024_r24 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 237,
  0, 13609, 12515131, 6495978352, 993491491501]
/-- Prefix-kick masks for `(m = 1024, r = 25)`. -/
def rkmMasksHi_m1024_r25 : List (List Bool) := [[], [], [], [], [false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, true, true], [false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, false, true, true], [false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 25)`. -/
def rkmRowHi_m1024_r25 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3,
  300, 0, 25098, 16368591, 6241373440, 993742231348]
/-- Prefix-kick masks for `(m = 1024, r = 26)`. -/
def rkmMasksHi_m1024_r26 : List (List Bool) := [[], [], [], [], [false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, true], [false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, true,
  true], [false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 26)`. -/
def rkmRowHi_m1024_r26 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  17, 349, 4, 41964, 20608528, 6006575541, 993972772300]
/-- Prefix-kick masks for `(m = 1024, r = 27)`. -/
def rkmMasksHi_m1024_r27 : List (List Bool) := [[], [], [], [false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  true], [false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, true], [false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true, true], [false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 27)`. -/
def rkmRowHi_m1024_r27 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  27, 436, 34, 64422, 25210497, 5789157933, 994185565249]
/-- Prefix-kick masks for `(m = 1024, r = 28)`. -/
def rkmMasksHi_m1024_r28 : List (List Bool) := [[], [], [], [], [false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true], [false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, true, true, true],
  [false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true, false, false, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 28)`. -/
def rkmRowHi_m1024_r28 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 443, 79319, 838939, 32467545, 5587502009, 994379110286]
/-- Prefix-kick masks for `(m = 1024, r = 29)`. -/
def rkmMasksHi_m1024_r29 : List (List Bool) := [[], [false, false, false, false, false, false,
  false, false, false, false, false, true], [false, false, false, false, false, false, false,
  false, false, false, false, false, true], [], [false, false, false, false, false, false,
  false, false, false, false, false, false, true, false, false, false, false, true], [false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, true, true, false, false, true], [false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 29)`. -/
def rkmRowHi_m1024_r29 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  1, 35, 89, 370, 1682, 1054169, 38352238, 5399705182, 994560884700]
/-- Prefix-kick masks for `(m = 1024, r = 30)`. -/
def rkmMasksHi_m1024_r30 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 30)`. -/
def rkmRowHi_m1024_r30 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 174, 2204, 1115627, 44467575, 5224567619, 994729845103]
/-- Prefix-kick masks for `(m = 1024, r = 31)`. -/
def rkmMasksHi_m1024_r31 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 31)`. -/
def rkmRowHi_m1024_r31 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 201, 3060, 1175917, 50930744, 5060695548, 994887192859]
/-- Prefix-kick masks for `(m = 1024, r = 32)`. -/
def rkmMasksHi_m1024_r32 : List (List Bool) := [[], [false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, true, false, false, false, true], [false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, true, true, false, true, false, true, true], [false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, true, true, false, false,
  true, true], [false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  true, true, true, false, false, false, true], [false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, true, true, true], [false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, true,
  true, true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 32)`. -/
def rkmRowHi_m1024_r32 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 2, 0, 1, 16740, 1994231, 169462, 4900323291, 995097494295]

end

public section

private def pCat : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | x :: xs, ys => x :: pCat xs ys
private def atF : List Bool → Bool
  | [] => true
  | true :: bs => atF bs
  | false :: _ => false
private theorem tl1 : ∀ {b : Bool} {s : List Bool}, atF (b :: s) = true → atF s = true
  | false, _, h => Bool.noConfusion h
  | true, _, h => h
private theorem tl2 {a b : Bool} {s : List Bool} (h : atF (a :: b :: s) = true) :
    atF s = true := tl1 (tl1 h)
private abbrev fN {α : Type} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β :=
  HighDForce.withForcedList xs k
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := Nat.one_add x
private theorem n0m (z : ℕ) : (0 : ℕ) = Nat.mul 0 z := by
  rw [Nat.mul_eq]
  omega
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private theorem bFN {α : Type} (x : ℕ) (k : ℕ → α) :
    HighDForce.withForcedNat x k = k x := by
  unfold HighDForce.withForcedNat
  rw [n1a]
private theorem bFL {α β : Type} (xs : List α) (k : List α → β) :
    HighDForce.withForcedList xs k = k xs := by cases xs <;> rfl
private theorem bBle : ∀ {a b : ℕ}, Nat.ble a b = true → a ≤ b
  | 0, _, _ => Nat.zero_le _
  | _ + 1, 0, h => Bool.noConfusion h
  | _ + 1, _ + 1, h => Nat.succ_le_succ (bBle h)
private def bNatEq (a b : ℕ) : Bool := Bool.and (Nat.ble a b) (Nat.ble b a)
private theorem bNatEq_t {a b : ℕ} (h : bNatEq a b = true) : a = b := by
  unfold bNatEq at h
  revert h
  cases h1 : Nat.ble a b with
  | false => exact Bool.noConfusion
  | true =>
    cases h2 : Nat.ble b a with
    | false => exact Bool.noConfusion
    | true => exact fun _ => Nat.le_antisymm (bBle h1) (bBle h2)
private def bNLE : List ℕ → List ℕ → Bool
  | [], [] => true
  | x :: xs, y :: ys => cond (bNatEq x y) (bNLE xs ys) false
  | _, _ => false
private theorem bNLE_t : ∀ {xs ys : List ℕ}, bNLE xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | x :: xs, y :: ys, h => by
    unfold bNLE at h
    revert h
    cases hx : bNatEq x y with
    | false => exact Bool.noConfusion
    | true => exact fun h => congrArg₂ List.cons (bNatEq_t hx) (bNLE_t h)
private def bIntEq : ℤ → ℤ → Bool
  | Int.ofNat a, Int.ofNat b => bNatEq a b
  | Int.negSucc a, Int.negSucc b => bNatEq a b
  | _, _ => false
private theorem bIntEq_t : ∀ {a b : ℤ}, bIntEq a b = true → a = b
  | Int.ofNat _, Int.ofNat _, h => congrArg Int.ofNat (bNatEq_t h)
  | Int.negSucc _, Int.negSucc _, h => congrArg Int.negSucc (bNatEq_t h)
  | Int.ofNat _, Int.negSucc _, h => Bool.noConfusion h
  | Int.negSucc _, Int.ofNat _, h => Bool.noConfusion h
private def bILE : List ℤ → List ℤ → Bool
  | [], [] => true
  | x :: xs, y :: ys => cond (bIntEq x y) (bILE xs ys) false
  | _, _ => false
private theorem bILE_t : ∀ {xs ys : List ℤ}, bILE xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | x :: xs, y :: ys, h => by
    unfold bILE at h
    revert h
    cases hx : bIntEq x y with
    | false => exact Bool.noConfusion
    | true => exact fun h => congrArg₂ List.cons (bIntEq_t hx) (bILE_t h)
private theorem bhd_eq {x y : List ℕ} {s : List Bool} (h : atF (bNLE x y :: s) = true) : x = y := by
  revert h
  cases h0 : bNLE x y with
  | false => exact Bool.noConfusion
  | true => exact fun _ => bNLE_t h0
private theorem bIntHd_eq {x y : List ℤ} {s : List Bool}
    (h : atF (bILE x y :: s) = true) : x = y := by
  revert h
  cases h0 : bILE x y with
  | false => exact Bool.noConfusion
  | true => exact fun _ => bILE_t h0
private def uC (x : ℕ) (xs : List ℕ) : List ℕ := match Nat.add 1 x with
  | 0 => xs
  | v + 1 => match xs with | [] => [v] | h :: t => v :: h :: t
private theorem uC_eq (x : ℕ) (xs : List ℕ) : uC x xs = x :: xs := by
  unfold uC
  rw [n1a]
  cases xs <;> rfl
private def uMZ (z : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: bs => uC (Nat.mul b z) (uMZ z bs)
private def uHb : List ℤ → Option (List ℕ)
  | [] => some []
  | Int.ofNat n :: xs => match uHb xs with | some ns => some (uC n ns) | none => none
  | Int.negSucc _ :: _ => none
private def uOh : List ℕ → List ℤ
  | [] => []
  | n :: ns => Int.ofNat n :: uOh ns
private theorem uHb_s : ∀ (hb : List ℤ) (ns : List ℕ), uHb hb = some ns → hb = uOh ns
  | [], ns, h => by
    injection h with h'
    subst h'
    rfl
  | Int.negSucc _ :: _, _, h => by
    dsimp only [uHb] at h
    cases h
  | Int.ofNat n :: xs, ns, h => by
    dsimp only [uHb] at h
    revert h
    cases hxs : uHb xs with
    | none =>
      intro h
      dsimp only at h
      cases h
    | some ms =>
      intro h
      dsimp only at h
      injection h with h'
      subst h'
      rw [uC_eq, uOh, uHb_s xs ms hxs]
private theorem bPOf (x : ℕ) : primOfNatForced x = Int.ofNat x := by
  unfold primOfNatForced
  rw [n1a]
private theorem bPNS (x : ℕ) : primNegSuccForced x = Int.negSucc x := by
  unfold primNegSuccForced
  rw [n1a]
private theorem bPNeg : ∀ (x : ℕ), primNegOfNat x = -(x : ℤ)
  | 0 => by
    dsimp only [primNegOfNat]
    rw [Int.ofNat_eq_natCast]
    omega
  | k + 1 => by
    dsimp only [primNegOfNat]
    rw [bPNS, Int.negSucc_eq]
    omega
private theorem bPSub (m n : ℕ) : primSubNatNat m n = (m : ℤ) - (n : ℤ) := by
  unfold primSubNatNat
  simp only [Nat.sub_eq]
  cases h : n - m with
  | zero =>
    dsimp only
    rw [bPOf, Int.ofNat_eq_natCast]
    omega
  | succ k =>
    dsimp only
    rw [bPNS, Int.negSucc_eq]
    omega
private theorem bPMul (a b : ℤ) : primIntMul a b = a * b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      dsimp only [primIntMul]
      simp only [bPOf, Nat.mul_eq, Int.ofNat_eq_natCast]
      push_cast
      ring
    | negSucc n =>
      dsimp only [primIntMul]
      simp only [bPNeg, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
  | negSucc m =>
    cases b with
    | ofNat n =>
      dsimp only [primIntMul]
      simp only [bPNeg, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
    | negSucc n =>
      dsimp only [primIntMul]
      simp only [bPOf, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
private def bCZ (x : ℤ) (xs : List ℤ) : List ℤ := match x with
  | Int.ofNat v => match xs with | [] => [Int.ofNat v] | h :: t => Int.ofNat v :: h :: t
  | Int.negSucc v => match xs with | [] => [Int.negSucc v] | h :: t => Int.negSucc v :: h :: t
private theorem bCZ_eq (x : ℤ) (xs : List ℤ) : bCZ x xs = x :: xs := by
  cases x <;> cases xs <;> rfl
private theorem bSC_eq (x : ℤ) (xs : List ℤ) : highdStrictConsInt x xs = x :: xs := by
  cases x with
  | ofNat n =>
    unfold highdStrictConsInt
    dsimp only
    rw [n1a]
    cases xs <;> rfl
  | negSucc n =>
    unfold highdStrictConsInt
    dsimp only
    rw [n1a]
    cases xs <;> rfl
private def bDec (z : ℕ) : List ℕ → List ℤ
  | [] => []
  | u :: us => bCZ (primSubNatNat u z) (bDec z us)
private theorem bDec0 (z : ℕ) : bDec z [] = [] := rfl
private theorem bDecS (z u : ℕ) (us : List ℕ) :
    bDec z (u :: us) = ((u : ℤ) - (z : ℤ)) :: bDec z us := by
  rw [bDec, bCZ_eq, bPSub]
private theorem bDecL (z : ℕ) : ∀ (cs : List ℕ), altIntLen (bDec z cs) = altListLen cs
  | [] => rfl
  | _ :: cs => by rw [bDecS, altIntLen, altListLen, bDecL z cs]
private theorem bZ0 (z : ℕ) : ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [Int.ofNat_eq_natCast]
  omega
private theorem bPM0 (z : ℕ) : primIntMul (Int.ofNat 0) ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [bPMul, bZ0]
  rfl
private def bE1 (z : ℕ) : ℤ → Option ℕ
  | Int.ofNat n => some (Nat.add z n)
  | Int.negSucc k => match Nat.sub z (Nat.add k 1) with | 0 => none | w + 1 => some (Nat.add w 1)
private def bEnc (z : ℕ) : List ℤ → Option (List ℕ)
  | [] => some []
  | x :: xs => match bE1 z x with
    | none => none
    | some u => match bEnc z xs with | none => none | some us => some (uC u us)
private theorem bE1_s (z : ℕ) (x : ℤ) (u : ℕ) (h : bE1 z x = some u) : ((u : ℤ) - (z : ℤ)) = x := by
  cases x with
  | ofNat n =>
    unfold bE1 at h
    injection h with h'
    subst h'
    rw [Nat.add_eq, Int.ofNat_eq_natCast]
    omega
  | negSucc k =>
    unfold bE1 at h
    simp only [Nat.sub_eq, Nat.add_eq] at h
    revert h
    cases hz : z - (k + 1) with
    | zero =>
      intro h
      dsimp only at h
      cases h
    | succ w =>
      intro h
      dsimp only at h
      injection h with h'
      subst h'
      rw [Int.negSucc_eq]
      omega
private theorem bEnc_s (z : ℕ) : ∀ (xs : List ℤ) (us : List ℕ), bEnc z xs = some us → bDec z us = xs
  | [], us, h => by
    injection h with h'
    subst h'
    rfl
  | x :: xs, us, h => by
    dsimp only [bEnc] at h
    revert h
    cases hx : bE1 z x with
    | none =>
      intro h
      dsimp only at h
      cases h
    | some u =>
      dsimp only
      cases hxs : bEnc z xs with
      | none =>
        intro h
        dsimp only at h
        cases h
      | some ws =>
        intro h
        dsimp only at h
        injection h with h'
        subst h'
        rw [uC_eq, bDecS, bE1_s z x u hx, bEnc_s z xs ws hxs]
private def zTd (x : ℤ) (d : ℕ) : ℤ := match x with
  | Int.ofNat m => Int.ofNat (m / d)
  | Int.negSucc k => -(((k + 1) / d : ℕ) : ℤ)
private theorem bNeg : ∀ (n : ℕ), muxRawNegOfNat n = -(n : ℤ)
  | 0 => by
    dsimp only [muxRawNegOfNat]
    rw [Int.ofNat_eq_natCast]
    omega
  | k + 1 => by
    dsimp only [muxRawNegOfNat]
    rw [Int.negSucc_eq]
    omega
private theorem bTdN : ∀ (x : ℤ) (d : ℕ), muxRawIntTdivNat x d = zTd x d
  | Int.ofNat _, _ => rfl
  | Int.negSucc k, d => by
    dsimp only [muxRawIntTdivNat, zTd]
    rw [bNeg, ndiv, Nat.add_eq]
private theorem bRSubN (m n : ℕ) : muxRawSubNatNat m n = (m : ℤ) - (n : ℤ) := by
  unfold muxRawSubNatNat
  simp only [Nat.sub_eq]
  cases h : n - m with
  | zero =>
    dsimp only
    rw [Int.ofNat_eq_natCast]
    omega
  | succ k =>
    dsimp only
    rw [Int.negSucc_eq]
    omega
private theorem bRAdd (a b : ℤ) : muxRawIntAdd a b = a + b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      dsimp only [muxRawIntAdd]
      simp only [bPOf, Nat.add_eq, Int.ofNat_eq_natCast]
      omega
    | negSucc n =>
      dsimp only [muxRawIntAdd]
      simp only [bRSubN, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      omega
  | negSucc m =>
    cases b with
    | ofNat n =>
      dsimp only [muxRawIntAdd]
      simp only [bRSubN, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      omega
    | negSucc n =>
      dsimp only [muxRawIntAdd]
      simp only [bPNS, Nat.add_eq, Int.negSucc_eq]
      omega
private theorem bRNeg (a : ℤ) : muxRawIntNeg a = -a := by
  cases a with
  | ofNat n =>
    dsimp only [muxRawIntNeg]
    simp only [bNeg, Int.ofNat_eq_natCast]
  | negSucc n =>
    dsimp only [muxRawIntNeg]
    simp only [bPOf, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
    omega
private theorem bRSub (a b : ℤ) : muxRawIntSub a b = a - b := by
  unfold muxRawIntSub
  rw [bRAdd, bRNeg]
  omega
private theorem bRMul (a b : ℤ) : muxRawIntMul a b = a * b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      dsimp only [muxRawIntMul]
      simp only [Nat.mul_eq, Int.ofNat_eq_natCast]
      push_cast
      ring
    | negSucc n =>
      dsimp only [muxRawIntMul]
      simp only [bNeg, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
  | negSucc m =>
    cases b with
    | ofNat n =>
      dsimp only [muxRawIntMul]
      simp only [bNeg, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
    | negSucc n =>
      dsimp only [muxRawIntMul]
      simp only [Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
private def bSV (v P Q d : ℕ) : ℕ := match Nat.sub Q P with
  | 0 => Nat.add v (Nat.div (Nat.sub P Q) d)
  | k + 1 => Nat.sub v (Nat.div (Nat.add k 1) d)
private theorem bSV_eq (z v P Q d : ℕ) (hv : 0 < bSV v P Q d) :
    ((bSV v P Q d : ℤ) - (z : ℤ)) = ((v : ℤ) - (z : ℤ)) + zTd ((P : ℤ) - (Q : ℤ)) d := by
  unfold bSV at hv ⊢
  simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢
  revert hv
  cases h : Q - P with
  | zero =>
    intro _
    have hm : (P : ℤ) - (Q : ℤ) = Int.ofNat (P - Q) := by
      rw [Int.ofNat_eq_natCast]
      omega
    rw [hm]
    dsimp only [zTd]
    rw [Int.ofNat_eq_natCast]
    push_cast
    ring
  | succ k =>
    intro hv
    have hm : (P : ℤ) - (Q : ℤ) = Int.negSucc k := by
      rw [Int.negSucc_eq]
      omega
    rw [hm]
    dsimp only [zTd] at hv ⊢
    omega
private abbrev bCV (d b0 bz0 c0 b bz v c1 : ℕ) : ℕ :=
  bSV v (Nat.add (Nat.mul b0 c0) bz) (Nat.add (Nat.mul b c1) bz0) d
private theorem bChb (z d b0 c0 b v c1 : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bCV d b0 (Nat.mul b0 z) c0 b (Nat.mul b z) v c1) (ht : bDec z rest = tailZ) :
    bDec z (uC (bCV d b0 (Nat.mul b0 z) c0 b (Nat.mul b z) v c1) rest) =
      highdStrictConsInt (muxRawIntAdd ((v : ℤ) - (z : ℤ))
        (muxRawIntTdivNat (muxRawIntSub (primIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
          (muxRawIntMul (Int.ofNat b) ((c1 : ℤ) - (z : ℤ)))) d)) tailZ := by
  rw [uC_eq, bDecS, ht, bSC_eq, bRAdd, bTdN, bRSub, bPMul, bRMul]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.add (Nat.mul b0 c0) (Nat.mul b z) : ℕ) : ℤ) -
      ((Nat.add (Nat.mul b c1) (Nat.mul b0 z) : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) - (Int.ofNat b) * ((c1 : ℤ) - (z : ℤ)) := by
    simp only [Nat.add_eq, Nat.mul_eq, Int.ofNat_eq_natCast]
    push_cast
    ring
  unfold bCV at hv ⊢
  rw [bSV_eq z v _ _ d hv, hpq]
private theorem bC0 (z d b0 c0 v : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bSV v (Nat.mul b0 c0) (Nat.mul b0 z) d) (ht : bDec z rest = tailZ) :
    bDec z (uC (bSV v (Nat.mul b0 c0) (Nat.mul b0 z) d) rest) =
      highdStrictConsInt (muxRawIntAdd ((v : ℤ) - (z : ℤ))
        (muxRawIntTdivNat (primIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ))) d)) tailZ := by
  rw [uC_eq, bDecS, ht, bSC_eq, bRAdd, bTdN, bPMul]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.mul b0 c0 : ℕ) : ℤ) - ((Nat.mul b0 z : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) := by
    simp only [Nat.mul_eq, Int.ofNat_eq_natCast]
    push_cast
    ring
  rw [bSV_eq z v _ _ d hv, hpq]
private def bPos : List ℕ → Bool
  | [] => true
  | x :: xs => cond (Nat.ble x 0) false (bPos xs)
private theorem bPosC {x : ℕ} {xs : List ℕ} (h : bPos (uC x xs) = true) :
    0 < x ∧ bPos xs = true := by
  rw [uC_eq] at h
  cases x with
  | zero => exact Bool.noConfusion h
  | succ k => exact ⟨Nat.succ_pos k, h⟩
private def bHd (z : ℕ) : List ℕ → ℕ
  | [] => z
  | x :: _ => x
private def bTl : List ℕ → List ℕ
  | [] => []
  | _ :: xs => xs
private theorem bHd_eq (z : ℕ) : ∀ (cs : List ℕ),
    ((bHd z cs : ℤ) - (z : ℤ)) = (match bDec z cs with | cn :: _ => cn | [] => Int.ofNat 0)
  | [] => by
    unfold bHd
    rw [bDec0, bZ0]
  | c :: cs => by
    unfold bHd
    rw [bDecS]
private theorem bTl_eq (z : ℕ) : ∀ (xs : List ℕ),
    bDec z (bTl xs) = (match bDec z xs with | _ :: t => t | [] => [])
  | [] => rfl
  | x :: xs => by
    unfold bTl
    rw [bDecS]
private def bSlide (z d : ℕ) : ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _, _, _ => []
  | rem + 1, b0, bz0, c0, bns, bzs, vs, cs => match bns, bzs with
    | b :: bR, bz :: bzR => match vs, cs with
      | v :: vT, c :: cT =>
        uC (bCV d b0 bz0 c0 b bz v (bHd z cT)) (bSlide z d rem b bz c bR bzR vT cT)
      | v :: vT, [] => uC (bCV d b0 bz0 c0 b bz v z) (bSlide z d rem b bz z bR bzR vT [])
      | [], c :: cT => uC (bCV d b0 bz0 c0 b bz z (bHd z cT)) (bSlide z d rem b bz c bR bzR [] cT)
      | [], [] => uC (bCV d b0 bz0 c0 b bz z z) (bSlide z d rem b bz z bR bzR [] [])
    | _, _ =>
      uC (bSV (bHd z vs) (Nat.mul b0 c0) bz0 d) (bSlide z d rem 0 0 z [] [] (bTl vs) (bTl cs))
private theorem bSlide_s (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bPos (bSlide z d rem b0 (Nat.mul b0 z) c0 bns (uMZ z bns) vs cs) = true →
      bDec z (bSlide z d rem b0 (Nat.mul b0 z) c0 bns (uMZ z bns) vs cs) =
      muxFastSlideLoopAux d rem (primIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
        (uOh bns) (bDec z vs) (bDec z cs)
  | 0, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs, h => by
    cases bns with
    | nil =>
      dsimp only [bSlide, uMZ, uOh, muxFastSlideLoopAux] at h ⊢
      have hp := bPosC h
      have hp2 : bPos (bSlide z d rem 0 (Nat.mul 0 z) z [] (uMZ z []) (bTl vs) (bTl cs)) =
        true := by
        dsimp only [uMZ]
        rw [← n0m z]
        exact hp.2
      have hi := bSlide_s z d rem 0 z [] (bTl vs) (bTl cs) hp2
      dsimp only [uMZ] at hi
      rw [← n0m z, bPM0 z, uOh, bTl_eq z vs, bTl_eq z cs] at hi
      have hc := bC0 z d b0 c0 (bHd z vs) hp.1 hi
      rw [bHd_eq z vs] at hc
      exact hc
    | cons b bR =>
      rw [uMZ, uC_eq] at h ⊢
      cases vs with
      | nil =>
        cases cs with
        | nil =>
          dsimp only [bSlide, uOh] at h ⊢
          rw [bDec0]
          dsimp only [muxFastSlideLoopAux]
          have hp := bPosC h
          have hi := bSlide_s z d rem b z bR [] [] hp.2
          rw [bZ0 z, bDec0] at hi
          have hc := bChb z d b0 c0 b z z hp.1 hi
          rw [bZ0 z] at hc
          exact hc
        | cons c cT =>
          dsimp only [bSlide, uOh] at h ⊢
          rw [bDec0, bDecS z c cT]
          dsimp only [muxFastSlideLoopAux]
          have hp := bPosC h
          have hi := bSlide_s z d rem b c bR [] cT hp.2
          rw [bDec0] at hi
          have hc := bChb z d b0 c0 b z (bHd z cT) hp.1 hi
          rw [bHd_eq z cT, bZ0 z] at hc
          exact hc
      | cons v vT =>
        cases cs with
        | nil =>
          dsimp only [bSlide, uOh] at h ⊢
          rw [bDecS z v vT, bDec0]
          dsimp only [muxFastSlideLoopAux]
          have hp := bPosC h
          have hi := bSlide_s z d rem b z bR vT [] hp.2
          rw [bZ0 z, bDec0] at hi
          have hc := bChb z d b0 c0 b v z hp.1 hi
          rw [bZ0 z] at hc
          exact hc
        | cons c cT =>
          dsimp only [bSlide, uOh] at h ⊢
          rw [bDecS z v vT, bDecS z c cT]
          dsimp only [muxFastSlideLoopAux]
          have hp := bPosC h
          have hi := bSlide_s z d rem b c bR vT cT hp.2
          have hc := bChb z d b0 c0 b v (bHd z cT) hp.1 hi
          rw [bHd_eq z cT] at hc
          exact hc
private def bStg (z dg mL : ℕ) (bns bzs vns cns : List ℕ) : Option (List ℕ) :=
  fN (highdNatMin mL (Nat.add (altListLen cns) 1)) fun nL =>
    fN (Nat.mul dg wdScale) fun d =>
      fL (bSlide z d nL 0 0 z bns bzs vns cns) fun out => cond (bPos out) (some out) none
private theorem bStg_s (z dg mL : ℕ) (bns vns cns out : List ℕ)
    (h : bStg z dg mL bns (uMZ z bns) vns cns = some out) :
    bDec z out = muxFastHornerStage dg mL (uOh bns) (bDec z vns) (bDec z cns) := by
  unfold bStg at h
  dsimp only [fN, fL] at h
  rw [bFN, bFN, bFL] at h
  revert h
  set nL := highdNatMin mL (Nat.add (altListLen cns) 1)
  set d := Nat.mul dg wdScale
  cases hp : bPos (bSlide z d nL 0 0 z bns (uMZ z bns) vns cns) with
  | false =>
    intro h
    dsimp only [cond] at h
    cases h
  | true =>
    intro h
    dsimp only [cond] at h
    injection h with h'
    subst h'
    unfold muxFastHornerStage
    rw [bDecL z cns, bFN, bFN, ← bPM0 z]
    have hp0 : bPos (bSlide z d nL 0 (Nat.mul 0 z) z bns (uMZ z bns) vns cns) = true := by
      rw [← n0m z]
      exact hp
    have hs := bSlide_s z d nL 0 z bns vns cns hp0
    rw [← n0m z] at hs
    exact hs
private def bBd (x : Option (List ℕ)) (k : List ℕ → Option (List ℕ)) : Option (List ℕ) :=
  match x with | none => none | some out => k out
private theorem bBd_s {z dg mL : ℕ} {bns vns cns out : List ℕ}
    {kB : List ℕ → Option (List ℕ)} {kU : List ℤ → List ℤ}
    (h : bBd (bStg z dg mL bns (uMZ z bns) vns cns) kB = some out)
    (hk : ∀ (mid : List ℕ), kB mid = some out → bDec z out = kU (bDec z mid)) :
    bDec z out =
      HighDForce.withForcedList (muxFastHornerStage dg mL (uOh bns) (bDec z vns)
        (bDec z cns)) kU := by
  unfold bBd at h
  revert h
  cases hs : bStg z dg mL bns (uMZ z bns) vns cns with
  | none =>
    intro h
    dsimp only at h
    cases h
  | some mid =>
    intro h
    dsimp only at h
    rw [bFL, ← bStg_s z dg mL bns vns cns mid hs]
    exact hk mid h
private def bSp (z mL : ℕ) (bns bzs vns : List ℕ) : Option (List ℕ) :=
  bBd (bStg z 16 mL bns bzs vns vns) fun c1 => bBd (bStg z 15 mL bns bzs vns c1) fun c2 =>
  bBd (bStg z 14 mL bns bzs vns c2) fun c3 => bBd (bStg z 13 mL bns bzs vns c3) fun c4 =>
  bBd (bStg z 12 mL bns bzs vns c4) fun c5 => bBd (bStg z 11 mL bns bzs vns c5) fun c6 =>
  bBd (bStg z 10 mL bns bzs vns c6) fun c7 => bBd (bStg z 9 mL bns bzs vns c7) fun c8 =>
  bBd (bStg z 8 mL bns bzs vns c8) fun c9 => bBd (bStg z 7 mL bns bzs vns c9) fun ca =>
  bBd (bStg z 6 mL bns bzs vns ca) fun cb => bBd (bStg z 5 mL bns bzs vns cb) fun cc =>
  bBd (bStg z 4 mL bns bzs vns cc) fun cd => bBd (bStg z 3 mL bns bzs vns cd) fun ce =>
  bBd (bStg z 2 mL bns bzs vns ce) fun cf => bStg z 1 mL bns bzs vns cf
private theorem bSp_s (z mL : ℕ) (bns vns out : List ℕ)
    (h : bSp z mL bns (uMZ z bns) vns = some out) :
    bDec z out = muxFastHornerT16Step mL (uOh bns) (bDec z vns) := by
  unfold bSp at h
  unfold muxFastHornerT16Step
  refine bBd_s h fun _ h => bBd_s h fun _ h => bBd_s h fun _ h => ?_
  refine bBd_s h fun _ h => bBd_s h fun _ h => bBd_s h fun _ h => ?_
  refine bBd_s h fun _ h => bBd_s h fun _ h => bBd_s h fun _ h => ?_
  refine bBd_s h fun _ h => bBd_s h fun _ h => bBd_s h fun _ h => ?_
  refine bBd_s h fun _ h => bBd_s h fun _ h => bBd_s h fun _ h => ?_
  exact bStg_s _ _ _ _ _ _ _ h
private def bIt (z : ℕ) : ℕ → ℕ → List ℕ → List ℕ → List ℕ → Option (List ℕ)
  | 0, _, _, _, vns => some vns
  | k + 1, mL, bns, bzs, vns => match bSp z mL bns bzs vns with
    | none => none
    | some vNext => bIt z k mL bns bzs vNext
private theorem bIt_s (z : ℕ) : ∀ (k mL : ℕ) (bns vns out : List ℕ),
    bIt z k mL bns (uMZ z bns) vns = some out →
    bDec z out = muxFastIterFullT16 k mL (uOh bns) (bDec z vns)
  | 0, _, _, vns, out, h => by
    dsimp only [bIt] at h
    injection h with h'
    subst h'
    rfl
  | k + 1, mL, bns, vns, out, h => by
    dsimp only [bIt] at h
    revert h
    cases hs : bSp z mL bns (uMZ z bns) vns with
    | none =>
      intro h
      dsimp only at h
      cases h
    | some vNext =>
      intro h
      dsimp only at h
      unfold muxFastIterFullT16
      rw [bFL, ← bSp_s z mL bns vns vNext hs]
      exact bIt_s z k mL bns vNext out h
private abbrev zB : ℕ := 2000000000000000
private def fIter (k mL : ℕ) (hb v : List ℤ) : List ℤ := match uHb hb with
  | none => muxFastIterFullT16 k mL hb v
  | some bns => match bEnc zB v with
    | none => muxFastIterFullT16 k mL hb v
    | some vns => fL (uMZ zB bns) fun bzs => match bIt zB k mL bns bzs vns with
      | none => muxFastIterFullT16 k mL hb v
      | some out => bDec zB out
private theorem fIter_eq (k mL : ℕ) (hb v : List ℤ) :
    fIter k mL hb v = muxFastIterFullT16 k mL hb v := by
  unfold fIter
  dsimp only [fL]
  cases hh : uHb hb with
  | none => rfl
  | some bns =>
    dsimp only
    cases hv : bEnc zB v with
    | none => rfl
    | some vns =>
      dsimp only
      rw [bFL]
      cases hi : bIt zB k mL bns (uMZ zB bns) vns with
      | none => rfl
      | some out =>
        dsimp only
        rw [bIt_s zB k mL bns vns out hi, ← uHb_s hb bns hh, bEnc_s zB v vns hv]
private theorem mIter_add : ∀ (k1 k2 mL : ℕ) (hb v : List ℤ),
    muxFastIterFullT16 (k1 + k2) mL hb v =
      muxFastIterFullT16 k2 mL hb (muxFastIterFullT16 k1 mL hb v)
  | 0, k2, mL, hb, v => congrArg (fun n => muxFastIterFullT16 n mL hb v) (Nat.zero_add k2)
  | k1 + 1, k2, mL, hb, v => by
    have hk : k1 + 1 + k2 = (k1 + k2) + 1 := by omega
    rw [hk]
    dsimp only [muxFastIterFullT16]
    rw [bFL, bFL]
    exact mIter_add k1 k2 mL hb (muxFastHornerT16Step mL hb v)
private abbrev WalkCert : Type := Option (ℕ × ℕ × List ℕ × List ℕ × List ℕ)
private def WalkOk : WalkCert → Prop
  | none => True
  | some (kE, mE, bns, vns, out) => muxFastIterFullT16 kE mE (uOh bns) (bDec zB vns) = bDec zB out
private def WalksOk : List WalkCert → Prop
  | [] => True
  | wc :: wcs => WalkOk wc ∧ WalksOk wcs
private theorem wNil : WalksOk [] := trivial
private theorem wSkip {wcs : List WalkCert} (hw : WalksOk wcs) :
    WalksOk (none :: wcs) := And.intro trivial hw
private theorem wCons {wc : WalkCert} {wcs : List WalkCert} (h1 : WalkOk wc) (h2 : WalksOk wcs) :
    WalksOk (wc :: wcs) := And.intro h1 h2
private def bSlideChk (k mL : ℕ) (bns vns out : List ℕ) : Bool :=
  fL (uMZ zB bns) fun bzs =>
    match bIt zB k mL bns bzs vns with | none => false | some w => bNLE w out
private theorem bSlideChk_sound {k mL : ℕ} {bns vns out : List ℕ} {s : List Bool}
    (h : atF (bSlideChk k mL bns vns out :: s) = true) : WalkOk (some (k, mL, bns, vns, out)) := by
  unfold bSlideChk at h
  dsimp only [fL] at h
  rw [bFL] at h
  unfold WalkOk
  revert h
  cases hi : bIt zB k mL bns (uMZ zB bns) vns with
  | none =>
    intro h
    dsimp only [atF] at h
    cases h
  | some w =>
    intro h
    dsimp only at h
    rw [← bhd_eq h]
    exact (bIt_s zB k mL bns vns w hi).symm
private theorem mIter_split {k1 k2 kS mL : ℕ} {bns v0 v1 v2 : List ℕ}
    (hk : k1 + k2 = kS) (h1 : WalkOk (some (k1, mL, bns, v0, v1)))
    (h2 : WalkOk (some (k2, mL, bns, v1, v2))) : WalkOk (some (kS, mL, bns, v0, v2)) := by
  unfold WalkOk at h1 h2 ⊢
  dsimp only at h1 h2 ⊢
  rw [← hk, mIter_add, h1, h2]
private theorem bWalkEq {k mL : ℕ} {hb vi vo : List ℤ} {bns vns out : List ℕ} {s1 s2 s3 : List Bool}
    (hw : WalkOk (some (k, mL, bns, vns, out))) (hh : atF (bILE hb (uOh bns) :: s1) = true)
    (hi : atF (bILE vi (bDec zB vns) :: s2) = true)
    (ho : atF (bILE (bDec zB out) vo :: s3) = true) : muxFastIterFullT16 k mL hb vi = vo := by
  unfold WalkOk at hw
  dsimp only at hw
  rw [bIntHd_eq hh, bIntHd_eq hi, hw, bIntHd_eq ho]
private def wIter (k mL : ℕ) (hb v : List ℤ) : WalkCert → List ℤ
  | none => fIter k mL hb v
  | some (kE, mE, bns, vns, out) =>
    cond (Bool.and (bNatEq k kE) (Bool.and (bNatEq mL mE)
      (Bool.and (bILE hb (uOh bns)) (bILE v (bDec zB vns)))))
      (bDec zB out) (muxFastIterFullT16 k mL hb v)
private theorem wIter_eq (k mL : ℕ) (hb v : List ℤ) (wc : WalkCert) (hw : WalkOk wc) :
    wIter k mL hb v wc = muxFastIterFullT16 k mL hb v := by
  cases wc with
  | none => exact fIter_eq k mL hb v
  | some tup =>
    rcases tup with ⟨kE, mE, bns, vns, out⟩
    unfold WalkOk at hw
    dsimp only at hw
    unfold wIter
    dsimp only
    cases hk : bNatEq k kE with
    | false => rfl
    | true =>
      cases hm : bNatEq mL mE with
      | false => rfl
      | true =>
        cases hh : bILE hb (uOh bns) with
        | false => rfl
        | true =>
          cases hv : bILE v (bDec zB vns) with
          | false => rfl
          | true =>
            dsimp only [Bool.and, cond]
            rw [bNatEq_t hk, bNatEq_t hm, bILE_t hh, bILE_t hv]
            exact hw.symm
private def wHead : List WalkCert → WalkCert
  | [] => none
  | wc :: _ => wc
private def wTail : List WalkCert → List WalkCert
  | [] => []
  | _ :: wcs => wcs
private theorem wHead_ok : ∀ {wcs : List WalkCert}, WalksOk wcs → WalkOk (wHead wcs)
  | [], _ => trivial
  | _ :: _, h => h.1
private theorem wTail_ok : ∀ {wcs : List WalkCert}, WalksOk wcs → WalksOk (wTail wcs)
  | [], _ => trivial
  | _ :: _, h => h.2
private def bEvalSegsW (m lM r : ℕ) :
    List ℕ → List ℕ → List ℕ → List (List Bool) → List WalkCert →
    ℕ → ℕ → ℕ → List ℤ → (ℕ × ℕ × List ℤ)
  | [], tR, nR, mR, _, _, dE, aP, v =>
    match tR, nR, mR with | [], [], [] => (dE, aP, v) | _, _, _ => (0, 0, [])
  | lS :: lR, t9 :: tR, nS :: nR, mk :: mR, wcs, lP, _, aP, v =>
    let mE := Nat.mul lS m
    let d := highdNatMin mE r
    cond (Bool.or (primNatBlt lS 1) (Bool.or (primNatBlt lS lP) (Bool.or (primNatBlt lM lS)
      (Bool.or (primNatBlt mE 1) (Bool.or (primNatBlt 8192 mE) (Bool.or (primNatBlt d 1)
      (Bool.or (Nat.ble t9 0) (Bool.or (primNatBlt 4000000000 t9) (Bool.or (Nat.ble nS 0)
      (Bool.or (primNatBlt 16384 nS) (primNatBlt (Nat.add d 1)
        (rkmBoolListLen mk)))))))))))) (0, 0, [])
      (fN (Nat.div (Nat.mul t9 1000000) nS) fun hPt =>
        cond (primNatBlt hPt 1) (0, 0, [])
          (fN (altMaxBHiFrom mE r 0 d) fun bHi =>
            let bCap := Nat.mul 2 bHi
            fN (highdMulCeil15 (Nat.add 2 hPt) bCap) fun hgHi =>
              cond (Bool.or (primNatBlt 1500000000000000 hgHi)
                  (Bool.not (altCheckHbTight mE r 0 d))) (0, 0, [])
                (let hgP := altPow17Ceil15 hgHi
                let trP := Nat.div (Nat.add 299999999999999 (Nat.mul nS hgP)) 300000000000000
                let bCeil := Nat.div (Nat.add 999999999999999 bCap) wdScale
                let sPad := Nat.add (Nat.add trP 256) (Nat.mul nS (Nat.add 256 (Nat.mul 10 bCeil)))
                fN (Nat.add aP sPad) fun np =>
                  cond (Bool.or (Nat.ble np 0) (primNatBlt 100000000000000 np)) (0, 0, [])
                    (fL (altBuildHbFrom mE r hPt 0 d) fun hbP =>
                      fL (wIter nS (Nat.add d 1) hbP v (wHead wcs)) fun vW =>
                        fL (rkmApplyMaskBits mk vW) fun vN =>
                          bEvalSegsW m lM r lR tR nR mR (wTail wcs) lS d np vN))))
  | _, _, _, _, _, _, _, _, _ => (0, 0, [])
private theorem bEvalSegsW_eq (m lM r : ℕ) :
    ∀ (ls ts ns : List ℕ) (mks : List (List Bool)) (wcs : List WalkCert),
      WalksOk wcs → ∀ (lP dE aP : ℕ) (v : List ℤ),
        bEvalSegsW m lM r ls ts ns mks wcs lP dE aP v =
          rkmEvalSegsLoop m lM r ls ts ns mks lP dE aP v := by
  intro ls
  induction ls with
  | nil =>
    intros
    rfl
  | cons lS lR ih =>
    intro ts ns mks wcs hw lP dE aP v
    cases ts with
    | nil => rfl
    | cons t9 tR =>
      cases ns with
      | nil => rfl
      | cons nS nR =>
        cases mks with
        | nil => rfl
        | cons mk mR =>
          have hw0 : ∀ k mL hb u, wIter k mL hb u (wHead wcs) = muxFastIterFullT16 k mL hb u :=
            fun k mL hb u => wIter_eq k mL hb u (wHead wcs) (wHead_ok hw)
          have hi0 := ih tR nR mR (wTail wcs) (wTail_ok hw)
          unfold bEvalSegsW rkmEvalSegsLoop
          dsimp only [fN, fL]
          simp only [bFN, bFL, hw0, hi0]
          generalize Nat.add aP _ = np
          cases t9 <;> cases nS <;> cases np <;> rfl
private def bEvalLo12W (m lM r : ℕ) (ls ts ns : List ℕ)
    (mks : List (List Bool)) (wcs : List WalkCert) : List ℕ :=
  let nS := altListLen ls
  cond (Bool.or (Nat.ble nS 0) (Bool.or (primNatBlt 8 nS)
      (Bool.or (primNatBlt r 2) (primNatBlt 1024 r)))) []
    (match bEvalSegsW m lM r ls ts ns mks wcs 1 0 0 [Int.ofNat wdScale] with
    | (dE, aP, vF) => cond (Bool.or (Nat.ble dE 0) (Nat.ble aP 0)) []
        (match altPadRightInts (Nat.add dE 1) vF with
        | [] => []
        | _ :: tl => altVecTailToLo12 aP tl))
private theorem bEvalLo12W_eq (m lM r : ℕ) (ls ts ns : List ℕ)
    (mks : List (List Bool)) (wcs : List WalkCert) (hw : WalksOk wcs) :
    bEvalLo12W m lM r ls ts ns mks wcs = rkmEvalT16Lo12 m lM r ls ts ns mks := by
  unfold bEvalLo12W rkmEvalT16Lo12
  dsimp only
  rw [bEvalSegsW_eq m lM r ls ts ns mks wcs hw]
  generalize altListLen ls = nS
  cases rkmEvalSegsLoop m lM r ls ts ns mks 1 0 0 [Int.ofNat wdScale] with
  | mk dE rest =>
    cases rest with
    | mk aP vF => cases nS <;> cases dE <;> cases aP <;> rfl
private theorem bhW_eq {m lm r : ℕ} {ls ts ns : List ℕ} {mks : List (List Bool)}
    {wcs : List WalkCert} {y : List ℕ}
    {s : List Bool} (h : atF (bNLE (bEvalLo12W m lm r ls ts ns mks wcs) y :: s) = true)
    (hw : WalksOk wcs) : rkmLo12EqHi m lm r ls ts ns mks y :=
  (bEvalLo12W_eq m lm r ls ts ns mks wcs hw).symm.trans (bhd_eq h)
private theorem bh0_eq {m lm r : ℕ} {ls ts ns : List ℕ} {mks : List (List Bool)}
    {y : List ℕ} {s : List Bool}
    (h : atF (bNLE (bEvalLo12W m lm r ls ts ns mks []) y :: s) = true) :
    rkmLo12EqHi m lm r ls ts ns mks y := bhW_eq h wNil
private abbrev dP_0 : Prop := atF [ bNLE (bEvalLo12W 1024 8 32 [1,1,1,1,1,1,1,1]
  [11801948,11831604,372745,393642,31609,32423,38767,36954] [18,18,1,1,1,1,1,1]
  rkmMasksHi_m1024_r32 []) rkmRowHi_m1024_r32, bNLE (bEvalLo12W 1024 8 27 [1,1,1,1,1,1,1,1]
  [10804837,10717398,749165,747847,595897,341335,223736,292085] [13,13,1,1,1,1,1,1]
  rkmMasksHi_m1024_r27 []) rkmRowHi_m1024_r27] = true
private theorem bk_0 : dP_0 := by decide +kernel
private abbrev dP_1 : Prop := atF [ bNLE (bEvalLo12W 1024 8 30 [1] [24513504] [39]
  rkmMasksHi_m1024_r30 []) rkmRowHi_m1024_r30, bNLE (bEvalLo12W 1024 8 31 [1] [24526286] [36]
  rkmMasksHi_m1024_r31 []) rkmRowHi_m1024_r31, bNLE (bEvalLo12W 1024 8 3 [1] [22430263] [5]
  rkmMasksHi_m1024_r3 []) rkmRowHi_m1024_r3] = true
private theorem bk_1 : dP_1 := by decide +kernel
private abbrev dP_2 : Prop := atF [ bNLE (bEvalLo12W 1024 8 29 [1,1,1,1,1,1,1,1]
  [10135620,10211359,758633,738928,727504,658269,483431,786530] [13,13,1,1,1,1,1,1]
  rkmMasksHi_m1024_r29 []) rkmRowHi_m1024_r29, bNLE (bEvalLo12W 1024 8 28 [1,1,1,1,1,1,1,1]
  [10497110,10390676,791890,749411,700520,477494,379723,499722] [13,13,1,1,1,1,1,1]
  rkmMasksHi_m1024_r28 []) rkmRowHi_m1024_r28, bNLE (bEvalLo12W 1024 8 4 [1] [22985270] [5]
  rkmMasksHi_m1024_r4 []) rkmRowHi_m1024_r4, bNLE (bEvalLo12W 1024 8 5 [1] [23314714] [7]
  rkmMasksHi_m1024_r5 []) rkmRowHi_m1024_r5] = true
private theorem bk_2 : dP_2 := by decide +kernel
private abbrev dP_3 : Prop := atF [ bNLE (bEvalLo12W 1024 8 26 [1,1,1,1,1,1,1,1]
  [10851141,10730802,794569,747847,481497,345035,222136,284360] [13,13,1,1,1,1,1,1]
  rkmMasksHi_m1024_r26 []) rkmRowHi_m1024_r26, bNLE (bEvalLo12W 1024 8 25 [1,1,1,1,1,1,1,1]
  [10836038,10790702,794169,747847,446497,329335,221136,276056] [13,13,1,1,1,1,1,1]
  rkmMasksHi_m1024_r25 []) rkmRowHi_m1024_r25, bNLE (bEvalLo12W 1024 8 18 [1,1,1,1,1,1,1,1]
  [10553396,10399815,1085290,1026606,488146,148102,218772,382958] [9,9,1,1,1,1,1,1]
  rkmMasksHi_m1024_r18 []) rkmRowHi_m1024_r18] = true
private theorem bk_3 : dP_3 := by decide +kernel
private abbrev dP_4 : Prop := atF [ bNLE (bEvalLo12W 1024 8 24 [1,1,1,1,1,1,1,1]
  [10896763,10774107,793670,687848,457998,327736,220336,266928] [13,13,1,1,1,1,1,1]
  rkmMasksHi_m1024_r24 []) rkmRowHi_m1024_r24, bNLE (bEvalLo12W 1024 8 23 [1,1,1,1,1,1,1,1]
  [10882482,10776807,787970,687848,469998,326836,219132,257031] [13,13,1,1,1,1,1,1]
  rkmMasksHi_m1024_r23 []) rkmRowHi_m1024_r23, bNLE (bEvalLo12W 1024 8 19 [1,1,1,1,1,1,1,1]
  [10442517,10294835,1085290,966606,785646,126702,225672,399958] [9,9,1,1,1,1,1,1]
  rkmMasksHi_m1024_r19 []) rkmRowHi_m1024_r19] = true
private theorem bk_4 : dP_4 := by decide +kernel
private abbrev dP_5 : Prop := atF [ bNLE (bEvalLo12W 1024 8 22 [1,1,1,1,1,1,1,1]
  [10576087,11196907,655970,687848,481498,327436,217832,246231] [13,13,1,1,1,1,1,1]
  rkmMasksHi_m1024_r22 []) rkmRowHi_m1024_r22, bNLE (bEvalLo12W 1024 8 21 [1,1,1,1,1,1,1,1]
  [10566712,11186831,655970,687848,493498,328536,216632,234331] [13,13,1,1,1,1,1,1]
  rkmMasksHi_m1024_r21 []) rkmRowHi_m1024_r21, bNLE (bEvalLo12W 1024 8 20 [1,1,1,1,1,1,1,1]
  [10557928,11174827,655970,687848,505498,331736,214832,220931] [13,13,1,1,1,1,1,1]
  rkmMasksHi_m1024_r20 []) rkmRowHi_m1024_r20] = true
private theorem bk_5 : dP_5 := by decide +kernel
private abbrev dP_6 : Prop := atF [ bNLE (bEvalLo12W 1024 8 17 [1,1,1,1,1,1,1,1]
  [10599520,10387414,1085290,966606,476146,175202,222072,364558] [9,9,1,1,1,1,1,1]
  rkmMasksHi_m1024_r17 []) rkmRowHi_m1024_r17, bNLE (bEvalLo12W 1024 8 16 [1,1,1,1,1,1,1,1]
  [10897103,10481518,964790,666606,476146,203202,215172,343458] [9,9,1,1,1,1,1,1]
  rkmMasksHi_m1024_r16 []) rkmRowHi_m1024_r16, bNLE (bEvalLo12W 1024 8 15 [1,1,1,1,1,1,1,1]
  [10848717,10495539,967290,666606,476146,229702,212772,319358] [9,9,1,1,1,1,1,1]
  rkmMasksHi_m1024_r15 []) rkmRowHi_m1024_r15, bNLE (bEvalLo12W 1024 8 14 [1,1,1,1,1,1,1,1]
  [10801242,10510443,964290,666606,476146,259302,211572,290958] [9,9,1,1,1,1,1,1]
  rkmMasksHi_m1024_r14 []) rkmRowHi_m1024_r14, bNLE (bEvalLo12W 1024 8 13 [1,1,1,1,1,1,1,1]
  [10751662,10231863,1252290,666606,476146,285802,217972,258058] [9,9,1,1,1,1,1,1]
  rkmMasksHi_m1024_r13 []) rkmRowHi_m1024_r13] = true
private theorem bk_6 : dP_6 := by decide +kernel
private abbrev dP_7 : Prop := atF [ bNLE (bEvalLo12W 1024 8 12 [1,1,1,1,1,1,1,1]
  [10765766,10171863,1252289,666606,476146,345302,193972,222558] [9,9,1,1,1,1,1,1]
  rkmMasksHi_m1024_r12 []) rkmRowHi_m1024_r12, bNLE (bEvalLo12W 1024 8 6 [1,1] [16172786,7361113]
  [6,3] rkmMasksHi_m1024_r6 []) rkmRowHi_m1024_r6, bNLE (bEvalLo12W 1024 8 7 [1,1]
  [15801366,7889613] [6,3] rkmMasksHi_m1024_r7 []) rkmRowHi_m1024_r7, bNLE (bEvalLo12W 1024 8 8 [1]
  [23809654] [11] rkmMasksHi_m1024_r8 []) rkmRowHi_m1024_r8, bNLE (bEvalLo12W 1024 8 9 [1]
  [23902914] [11] rkmMasksHi_m1024_r9 []) rkmRowHi_m1024_r9, bNLE (bEvalLo12W 1024 8 10 [1]
  [23978494] [13] rkmMasksHi_m1024_r10 []) rkmRowHi_m1024_r10, bNLE (bEvalLo12W 1024 8 11 [1]
  [24041276] [13] rkmMasksHi_m1024_r11 []) rkmRowHi_m1024_r11] = true
private theorem bk_7 : dP_7 := by decide +kernel
/-- Trajectory row certificate `(m = 1024, r = 3)`. -/
theorem rkmTrajHi_m1024_r3 :
    rkmLo12EqHi 1024 8 3 [1]
      [22430263]
      [5] rkmMasksHi_m1024_r3 rkmRowHi_m1024_r3 := bh0_eq (tl2 bk_1)
/-- Trajectory row certificate `(m = 1024, r = 4)`. -/
theorem rkmTrajHi_m1024_r4 :
    rkmLo12EqHi 1024 8 4 [1]
      [22985270]
      [5] rkmMasksHi_m1024_r4 rkmRowHi_m1024_r4 := bh0_eq (tl2 bk_2)
/-- Trajectory row certificate `(m = 1024, r = 5)`. -/
theorem rkmTrajHi_m1024_r5 :
    rkmLo12EqHi 1024 8 5 [1]
      [23314714]
      [7] rkmMasksHi_m1024_r5 rkmRowHi_m1024_r5 := bh0_eq (tl1 (tl2 bk_2))
/-- Trajectory row certificate `(m = 1024, r = 6)`. -/
theorem rkmTrajHi_m1024_r6 :
    rkmLo12EqHi 1024 8 6 [1, 1]
      [16172786, 7361113]
      [6, 3] rkmMasksHi_m1024_r6 rkmRowHi_m1024_r6 := bh0_eq (tl1 bk_7)
/-- Trajectory row certificate `(m = 1024, r = 7)`. -/
theorem rkmTrajHi_m1024_r7 :
    rkmLo12EqHi 1024 8 7 [1, 1]
      [15801366, 7889613]
      [6, 3] rkmMasksHi_m1024_r7 rkmRowHi_m1024_r7 := bh0_eq (tl2 bk_7)
/-- Trajectory row certificate `(m = 1024, r = 8)`. -/
theorem rkmTrajHi_m1024_r8 :
    rkmLo12EqHi 1024 8 8 [1]
      [23809654]
      [11] rkmMasksHi_m1024_r8 rkmRowHi_m1024_r8 := bh0_eq (tl1 (tl2 bk_7))
/-- Trajectory row certificate `(m = 1024, r = 9)`. -/
theorem rkmTrajHi_m1024_r9 :
    rkmLo12EqHi 1024 8 9 [1]
      [23902914]
      [11] rkmMasksHi_m1024_r9 rkmRowHi_m1024_r9 := bh0_eq (tl2 (tl2 bk_7))
/-- Trajectory row certificate `(m = 1024, r = 10)`. -/
theorem rkmTrajHi_m1024_r10 :
    rkmLo12EqHi 1024 8 10 [1]
      [23978494]
      [13] rkmMasksHi_m1024_r10 rkmRowHi_m1024_r10 := bh0_eq (tl1 (tl2 (tl2 bk_7)))
/-- Trajectory row certificate `(m = 1024, r = 11)`. -/
theorem rkmTrajHi_m1024_r11 :
    rkmLo12EqHi 1024 8 11 [1]
      [24041276]
      [13] rkmMasksHi_m1024_r11 rkmRowHi_m1024_r11 := bh0_eq (tl2 (tl2 (tl2 bk_7)))
/-- Trajectory row certificate `(m = 1024, r = 12)`. -/
theorem rkmTrajHi_m1024_r12 :
    rkmLo12EqHi 1024 8 12 [1, 1, 1, 1, 1, 1, 1, 1]
      [10765766, 10171863, 1252289, 666606, 476146, 345302, 193972, 222558]
      [9, 9, 1, 1, 1, 1, 1, 1] rkmMasksHi_m1024_r12 rkmRowHi_m1024_r12 := bh0_eq bk_7
/-- Trajectory row certificate `(m = 1024, r = 13)`. -/
theorem rkmTrajHi_m1024_r13 :
    rkmLo12EqHi 1024 8 13 [1, 1, 1, 1, 1, 1, 1, 1]
      [10751662, 10231863, 1252290, 666606, 476146, 285802, 217972, 258058]
      [9, 9, 1, 1, 1, 1, 1, 1] rkmMasksHi_m1024_r13 rkmRowHi_m1024_r13 := bh0_eq (tl2 (tl2 bk_6))
/-- Trajectory row certificate `(m = 1024, r = 14)`. -/
theorem rkmTrajHi_m1024_r14 :
    rkmLo12EqHi 1024 8 14 [1, 1, 1, 1, 1, 1, 1, 1]
      [10801242, 10510443, 964290, 666606, 476146, 259302, 211572, 290958]
      [9, 9, 1, 1, 1, 1, 1, 1] rkmMasksHi_m1024_r14 rkmRowHi_m1024_r14 := bh0_eq (tl1 (tl2 bk_6))
/-- Trajectory row certificate `(m = 1024, r = 15)`. -/
theorem rkmTrajHi_m1024_r15 :
    rkmLo12EqHi 1024 8 15 [1, 1, 1, 1, 1, 1, 1, 1]
      [10848717, 10495539, 967290, 666606, 476146, 229702, 212772, 319358]
      [9, 9, 1, 1, 1, 1, 1, 1] rkmMasksHi_m1024_r15 rkmRowHi_m1024_r15 := bh0_eq (tl2 bk_6)
/-- Trajectory row certificate `(m = 1024, r = 16)`. -/
theorem rkmTrajHi_m1024_r16 :
    rkmLo12EqHi 1024 8 16 [1, 1, 1, 1, 1, 1, 1, 1]
      [10897103, 10481518, 964790, 666606, 476146, 203202, 215172, 343458]
      [9, 9, 1, 1, 1, 1, 1, 1] rkmMasksHi_m1024_r16 rkmRowHi_m1024_r16 := bh0_eq (tl1 bk_6)
/-- Trajectory row certificate `(m = 1024, r = 17)`. -/
theorem rkmTrajHi_m1024_r17 :
    rkmLo12EqHi 1024 8 17 [1, 1, 1, 1, 1, 1, 1, 1]
      [10599520, 10387414, 1085290, 966606, 476146, 175202, 222072, 364558]
      [9, 9, 1, 1, 1, 1, 1, 1] rkmMasksHi_m1024_r17 rkmRowHi_m1024_r17 := bh0_eq bk_6
/-- Trajectory row certificate `(m = 1024, r = 18)`. -/
theorem rkmTrajHi_m1024_r18 :
    rkmLo12EqHi 1024 8 18 [1, 1, 1, 1, 1, 1, 1, 1]
      [10553396, 10399815, 1085290, 1026606, 488146, 148102, 218772, 382958]
      [9, 9, 1, 1, 1, 1, 1, 1] rkmMasksHi_m1024_r18 rkmRowHi_m1024_r18 := bh0_eq (tl2 bk_3)
/-- Trajectory row certificate `(m = 1024, r = 19)`. -/
theorem rkmTrajHi_m1024_r19 :
    rkmLo12EqHi 1024 8 19 [1, 1, 1, 1, 1, 1, 1, 1]
      [10442517, 10294835, 1085290, 966606, 785646, 126702, 225672, 399958]
      [9, 9, 1, 1, 1, 1, 1, 1] rkmMasksHi_m1024_r19 rkmRowHi_m1024_r19 := bh0_eq (tl2 bk_4)
/-- Trajectory row certificate `(m = 1024, r = 20)`. -/
theorem rkmTrajHi_m1024_r20 :
    rkmLo12EqHi 1024 8 20 [1, 1, 1, 1, 1, 1, 1, 1]
      [10557928, 11174827, 655970, 687848, 505498, 331736, 214832, 220931]
      [13, 13, 1, 1, 1, 1, 1, 1] rkmMasksHi_m1024_r20 rkmRowHi_m1024_r20 := bh0_eq (tl2 bk_5)
/-- Trajectory row certificate `(m = 1024, r = 21)`. -/
theorem rkmTrajHi_m1024_r21 :
    rkmLo12EqHi 1024 8 21 [1, 1, 1, 1, 1, 1, 1, 1]
      [10566712, 11186831, 655970, 687848, 493498, 328536, 216632, 234331]
      [13, 13, 1, 1, 1, 1, 1, 1] rkmMasksHi_m1024_r21 rkmRowHi_m1024_r21 := bh0_eq (tl1 bk_5)
/-- Trajectory row certificate `(m = 1024, r = 22)`. -/
theorem rkmTrajHi_m1024_r22 :
    rkmLo12EqHi 1024 8 22 [1, 1, 1, 1, 1, 1, 1, 1]
      [10576087, 11196907, 655970, 687848, 481498, 327436, 217832, 246231]
      [13, 13, 1, 1, 1, 1, 1, 1] rkmMasksHi_m1024_r22 rkmRowHi_m1024_r22 := bh0_eq bk_5
/-- Trajectory row certificate `(m = 1024, r = 23)`. -/
theorem rkmTrajHi_m1024_r23 :
    rkmLo12EqHi 1024 8 23 [1, 1, 1, 1, 1, 1, 1, 1]
      [10882482, 10776807, 787970, 687848, 469998, 326836, 219132, 257031]
      [13, 13, 1, 1, 1, 1, 1, 1] rkmMasksHi_m1024_r23 rkmRowHi_m1024_r23 := bh0_eq (tl1 bk_4)
/-- Trajectory row certificate `(m = 1024, r = 24)`. -/
theorem rkmTrajHi_m1024_r24 :
    rkmLo12EqHi 1024 8 24 [1, 1, 1, 1, 1, 1, 1, 1]
      [10896763, 10774107, 793670, 687848, 457998, 327736, 220336, 266928]
      [13, 13, 1, 1, 1, 1, 1, 1] rkmMasksHi_m1024_r24 rkmRowHi_m1024_r24 := bh0_eq bk_4
/-- Trajectory row certificate `(m = 1024, r = 25)`. -/
theorem rkmTrajHi_m1024_r25 :
    rkmLo12EqHi 1024 8 25 [1, 1, 1, 1, 1, 1, 1, 1]
      [10836038, 10790702, 794169, 747847, 446497, 329335, 221136, 276056]
      [13, 13, 1, 1, 1, 1, 1, 1] rkmMasksHi_m1024_r25 rkmRowHi_m1024_r25 := bh0_eq (tl1 bk_3)
/-- Trajectory row certificate `(m = 1024, r = 26)`. -/
theorem rkmTrajHi_m1024_r26 :
    rkmLo12EqHi 1024 8 26 [1, 1, 1, 1, 1, 1, 1, 1]
      [10851141, 10730802, 794569, 747847, 481497, 345035, 222136, 284360]
      [13, 13, 1, 1, 1, 1, 1, 1] rkmMasksHi_m1024_r26 rkmRowHi_m1024_r26 := bh0_eq bk_3
/-- Trajectory row certificate `(m = 1024, r = 27)`. -/
theorem rkmTrajHi_m1024_r27 :
    rkmLo12EqHi 1024 8 27 [1, 1, 1, 1, 1, 1, 1, 1]
      [10804837, 10717398, 749165, 747847, 595897, 341335, 223736, 292085]
      [13, 13, 1, 1, 1, 1, 1, 1] rkmMasksHi_m1024_r27 rkmRowHi_m1024_r27 := bh0_eq (tl1 bk_0)
/-- Trajectory row certificate `(m = 1024, r = 28)`. -/
theorem rkmTrajHi_m1024_r28 :
    rkmLo12EqHi 1024 8 28 [1, 1, 1, 1, 1, 1, 1, 1]
      [10497110, 10390676, 791890, 749411, 700520, 477494, 379723, 499722]
      [13, 13, 1, 1, 1, 1, 1, 1] rkmMasksHi_m1024_r28 rkmRowHi_m1024_r28 := bh0_eq (tl1 bk_2)
/-- Trajectory row certificate `(m = 1024, r = 29)`. -/
theorem rkmTrajHi_m1024_r29 :
    rkmLo12EqHi 1024 8 29 [1, 1, 1, 1, 1, 1, 1, 1]
      [10135620, 10211359, 758633, 738928, 727504, 658269, 483431, 786530]
      [13, 13, 1, 1, 1, 1, 1, 1] rkmMasksHi_m1024_r29 rkmRowHi_m1024_r29 := bh0_eq bk_2
/-- Trajectory row certificate `(m = 1024, r = 30)`. -/
theorem rkmTrajHi_m1024_r30 :
    rkmLo12EqHi 1024 8 30 [1]
      [24513504]
      [39] rkmMasksHi_m1024_r30 rkmRowHi_m1024_r30 := bh0_eq bk_1
/-- Trajectory row certificate `(m = 1024, r = 31)`. -/
theorem rkmTrajHi_m1024_r31 :
    rkmLo12EqHi 1024 8 31 [1]
      [24526286]
      [36] rkmMasksHi_m1024_r31 rkmRowHi_m1024_r31 := bh0_eq (tl1 bk_1)
/-- Trajectory row certificate `(m = 1024, r = 32)`. -/
theorem rkmTrajHi_m1024_r32 :
    rkmLo12EqHi 1024 8 32 [1, 1, 1, 1, 1, 1, 1, 1]
      [11801948, 11831604, 372745, 393642, 31609, 32423, 38767, 36954]
      [18, 18, 1, 1, 1, 1, 1, 1] rkmMasksHi_m1024_r32 rkmRowHi_m1024_r32 := bh0_eq bk_0

/-- Self-contained `0bar` lane witness for `FindAllJohnsonRampKickMuxHi1024T0`. -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi1024T0 :
    rkmTrajHi_m1024_r3 = rkmTrajHi_m1024_r3 := rfl

end
end QuantumComputation.Specs.DickeSol
