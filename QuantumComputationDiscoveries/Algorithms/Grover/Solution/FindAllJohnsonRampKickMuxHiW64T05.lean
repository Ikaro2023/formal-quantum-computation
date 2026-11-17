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

public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHiWin
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHiW64T04

/-
# Caustic `r = 1024` Halo-16 Walk `w64_m16` Part `1` (`FindAllJohnsonRampKickMuxHiW64T05`)

Certifies part `1` of the `w64_m16` `r = 1024` halo-16 trajectory.
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Generator list for `w64_m16_s4b`. -/
def rkmHbWin_w64_m16_s4b : List ℤ := altBuildHbFrom 1024 1024 29638027559 0 1024
/-- Entry `rkmXsWin_w64_m16_s4b_in`. -/
def rkmXsWin_w64_m16_s4b_in : List ℤ := [rkmN 227779891, rkmN 350119899, rkmN 585590871,
  rkmN 736229225, rkmN 719823250, rkmN 178673275, rkmP 1526167786, rkmP 5310363490,
  rkmP 13007770460, rkmP 27169000145, rkmP 51970476872, rkmP 93393625363, rkmP 159890372817,
  rkmP 263347335031, rkmP 419596341709, rkmP 649886770596, rkmP 981343234364, rkmP 1448140175712,
  rkmP 2092323372021, rkmP 2964274634587, rkmP 4123428191598, rkmP 5637581868071,
  rkmP 7582591793984, rkmP 10040788478086, rkmP 13098905323821, rkmP 16845440588253,
  rkmP 21366561613411, rkmP 26742301592776, rkmP 33041283200734, rkmP 40315875334793,
  rkmP 48596833185728, rkmP 57888281766064, rkmP 68163443207304, rkmP 79361119536072,
  rkmP 91383414892886, rkmP 104095360729159, rkmP 117325599288470, rkmP 130869812275196,
  rkmP 144495166679067, rkmP 157946805000397, rkmP 170956145018365, rkmP 183249327380930,
  rkmP 194557757608575, rkmP 204627499701212, rkmP 213228979474793, rkmP 220166065036634,
  rkmP 225282805526066, rkmP 228469909399080, rkmP 229667995228958, rkmP 228869270106596,
  rkmP 226117051830338, rkmP 221502688005836, rkmP 215161332633283, rkmP 207265323459195,
  rkmP 198017171619902, rkmP 187641049278464, rkmP 176374183300819, rkmP 164458771950330,
  rkmP 152133443719682, rkmP 139626597998005, rkmP 127149993208400, rkmP 114893997179363,
  rkmP 103023971268565, rkmP 91677989114012, rkmP 80966061096229, rkmP 70970338099543,
  rkmP 61746071298797, rkmP 53324211314970, rkmP 45713423101766, rkmP 38903537987808,
  rkmP 32868679619241, rkmP 27570251703753, rkmP 22960837138032, rkmP 18986308839242,
  rkmP 15588966920625, rkmP 12709816228235, rkmP 10290135664548, rkmP 8273426509410,
  rkmP 6606089407627, rkmP 5238637799928, rkmP 4125905381729, rkmP 3227422054722,
  rkmP 2507630608589, rkmP 1935240059632, rkmP 1483502260256, rkmP 1129573371414,
  rkmP 854332521943, rkmP 641889725182, rkmP 479027550271, rkmP 355049154121, rkmP 261400848425,
  rkmP 191024349314, rkmP 138654378768, rkmP 99833196492, rkmP 71225331682, rkmP 50422954020,
  rkmP 35289968762, rkmP 24428559917, rkmP 16615186987, rkmP 11081885684, rkmP 7230833820,
  rkmP 4488191069, rkmP 2651424215, rkmP 1386709698, rkmP 618512629, rkmP 207830276]
/-- Exit `rkmXsWin_w64_m16_s4b_out`. -/
def rkmXsWin_w64_m16_s4b_out : List ℤ := [rkmP 208475749, rkmP 386014885, rkmP 525333499,
  rkmP 455252394, rkmP 35298947, rkmN 715660460, rkmN 1855818299, rkmN 3223716549, rkmN 4253275202,
  rkmN 4232268483, rkmN 2394487412, rkmP 2482418525, rkmP 10863091018, rkmP 22547258948,
  rkmP 36082717707, rkmP 47755387050, rkmP 51639115495, rkmP 39527302265, rkmP 1346751471,
  rkmN 72896147310, rkmN 190375855259, rkmN 351709745780, rkmN 545808339397, rkmN 743561960009,
  rkmN 892485334325, rkmN 910406485342, rkmN 681192365555, rkmN 53131098634, rkmP 1160199295956,
  rkmP 3174848092231, rkmP 6226956981310, rkmP 10559333073392, rkmP 16404700593234,
  rkmP 23965808988182, rkmP 33395075751257, rkmP 44775036613076, rkmP 58101146947046,
  rkmP 73269359079508, rkmP 90070447563239, rkmP 108190189748895, rkmP 127218429847025,
  rkmP 146665028896870, rkmP 165981868733857, rkmP 184590379525564, rkmP 201911715468875,
  rkmP 217397344078097, rkmP 230557880596850, rkmP 240988729520037, rkmP 248389733532730,
  rkmP 252577774748094, rkmP 253492496193230, rkmP 251194670802832, rkmP 245856745432672,
  rkmP 237748944731940, rkmP 227220131203274, rkmP 214675991337184, rkmP 200556385446120,
  rkmP 185313079971181, rkmP 169389094260290, rkmP 153200782215716, rkmP 137124129857374,
  rkmP 121484447607337, rkmP 106549700496227, rkmP 92528508621575, rkmP 79570979824947,
  rkmP 67771845276927, rkmP 57176159911061, rkmP 47786675916372, rkmP 39570828273556,
  rkmP 32468947922410, rkmP 26401691198462, rkmP 21277038518749, rkmP 16996080494740,
  rkmP 13458013419912, rkmP 10564505444230, rkmP 8222261558362, rkmP 6345008745819,
  rkmP 4855198198630, rkmP 3684313517836, rkmP 2772654459695, rkmP 2069360143248,
  rkmP 1531855710058, rkmP 1124780751493, rkmP 819115650123, rkmP 591652744755, rkmP 423832021960,
  rkmP 301160860410, rkmP 212087432296, rkmP 147969569060, rkmP 102337756620, rkmP 70029753905,
  rkmP 47269417547, rkmP 31471144421, rkmP 20639132786, rkmP 13200932185, rkmP 8115778866,
  rkmP 4744917810, rkmP 2590661298, rkmP 1223150569, rkmP 380758498]
/-- Generator list for `w64_m16_s5a`. -/
def rkmHbWin_w64_m16_s5a : List ℤ := altBuildHbFrom 1856 1024 19586394833 0 1024
/-- Entry `rkmXsWin_w64_m16_s5a_in`. -/
def rkmXsWin_w64_m16_s5a_in : List ℤ := [rkmP 208475749, rkmP 386014885, rkmP 525333499,
  rkmP 455252394, rkmP 35298947, rkmN 715660460, rkmN 1855818299, rkmN 3223716549, rkmN 4253275202,
  rkmN 4232268483, rkmN 2394487412, rkmP 2482418525, rkmP 10863091018, rkmP 22547258948,
  rkmP 36082717707, rkmP 47755387050, rkmP 51639115495, rkmP 39527302265, rkmP 1346751471,
  rkmN 72896147310, rkmN 190375855259, rkmN 351709745780, rkmN 545808339397, rkmN 743561960009,
  rkmN 892485334325, rkmN 910406485342, rkmN 681192365555, rkmN 53131098634, rkmP 1160199295956,
  rkmP 3174848092231, rkmP 6226956981310, rkmP 10559333073392, rkmP 16404700593234,
  rkmP 23965808988182, rkmP 33395075751257, rkmP 44775036613076, rkmP 58101146947046,
  rkmP 73269359079508, rkmP 90070447563239, rkmP 108190189748895, rkmP 127218429847025,
  rkmP 146665028896870, rkmP 165981868733857, rkmP 184590379525564, rkmP 201911715468875,
  rkmP 217397344078097, rkmP 230557880596850, rkmP 240988729520037, rkmP 248389733532730,
  rkmP 252577774748094, rkmP 253492496193230, rkmP 251194670802832, rkmP 245856745432672,
  rkmP 237748944731940, rkmP 227220131203274, rkmP 214675991337184, rkmP 200556385446120,
  rkmP 185313079971181, rkmP 169389094260290, rkmP 153200782215716, rkmP 137124129857374,
  rkmP 121484447607337, rkmP 106549700496227, rkmP 92528508621575, rkmP 79570979824947,
  rkmP 67771845276927, rkmP 57176159911061, rkmP 47786675916372, rkmP 39570828273556,
  rkmP 32468947922410, rkmP 26401691198462, rkmP 21277038518749, rkmP 16996080494740,
  rkmP 13458013419912, rkmP 10564505444230, rkmP 8222261558362, rkmP 6345008745819,
  rkmP 4855198198630, rkmP 3684313517836, rkmP 2772654459695, rkmP 2069360143248,
  rkmP 1531855710058, rkmP 1124780751493, rkmP 819115650123, rkmP 591652744755, rkmP 423832021960,
  rkmP 301160860410, rkmP 212087432296, rkmP 147969569060, rkmP 102337756620, rkmP 70029753905,
  rkmP 47269417547, rkmP 31471144421, rkmP 20639132786, rkmP 13200932185, rkmP 8115778866,
  rkmP 4744917810, rkmP 2590661298, rkmP 1223150569, rkmP 380758498]
/-- Exit `rkmXsWin_w64_m16_s5a_out`. -/
def rkmXsWin_w64_m16_s5a_out : List ℤ := [rkmP 316160027, rkmP 523820314, rkmP 348726432,
  rkmN 298875027, rkmN 1123835294, rkmN 1492070999, rkmN 847704563, rkmP 801379334,
  rkmP 2725632734, rkmP 3742482788, rkmP 2666576001, rkmN 785190203, rkmN 5395826123,
  rkmN 8526369778, rkmN 7567624299, rkmN 1241816682, rkmP 8792456669, rkmP 17967879854,
  rkmP 19993754174, rkmP 10541907085, rkmN 9680265962, rkmN 33399405325, rkmN 48395350989,
  rkmN 42315644445, rkmN 9215261681, rkmP 44211264128, rkmP 97599237426, rkmP 122421725596,
  rkmP 93409790748, rkmP 2526478089, rkmN 130791579503, rkmN 258394227949, rkmN 315757940102,
  rkmN 246194135543, rkmN 29099067629, rkmP 298277101788, rkmP 636180752345, rkmP 842564287217,
  rkmP 775939077807, rkmP 352478736162, rkmN 402436098763, rkmN 1327483609809, rkmN 2139810868019,
  rkmN 2495068993044, rkmN 2085128143232, rkmN 750708549908, rkmP 1423127023934,
  rkmP 4059657671061, rkmP 6516128834306, rkmP 7988112774943, rkmP 7679302148724,
  rkmP 5006048100407, rkmN 207028373395, rkmN 7587169307828, rkmN 16164606453454,
  rkmN 24436072656873, rkmN 30535585643848, rkmN 32488550620203, rkmN 28506145504220,
  rkmN 17269623391334, rkmP 1843617255546, rkmP 28630367159014, rkmP 62047590404831,
  rkmP 100313386132458, rkmP 141103784419597, rkmP 181811505463215, rkmP 219828509603600,
  rkmP 252810055327617, rkmP 278888828599667, rkmP 296816461683681, rkmP 306023686989419,
  rkmP 306601360586462, rkmP 299216394931058, rkmP 284982797441200, rkmP 265307718585737,
  rkmP 241735407401511, rkmP 215805636158626, rkmP 188939044969934, rkmP 162354963919653,
  rkmP 137024751308439, rkmP 113655365627297, rkmP 92698966578310, rkmP 74381632854090,
  rkmP 58742395183519, rkmP 45677581723580, rkmP 34984359911462, rkmP 26400050330199,
  rkmP 19634455453834, rkmP 14395723471815, rkmP 10407618428608, rkmP 7421018336935,
  rkmP 5219871361449, rkmP 3622580416385, rkmP 2480756175289, rkmP 1676612179874,
  rkmP 1118268608611, rkmP 736085787654, rkmP 478103183727, rkmP 306297544201, rkmP 193486693232,
  rkmP 120478453719, rkmP 73774850089, rkmP 44448858576, rkmP 26216380315, rkmP 15061474091,
  rkmP 8384790443, rkmP 4383003961, rkmP 2143600300, rkmP 816444386, rkmP 185080464]

end

public section

private abbrev fN {α : Type} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β :=
  HighDForce.withForcedList xs k
private abbrev bz0 : ℕ := 10000000000000000
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := by rw [Nat.add_eq]; exact Nat.add_comm 1 x
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private def uCN (x : ℕ) (xs : List ℕ) : List ℕ :=
  match Nat.add 1 x with
  | 0 => xs
  | v + 1 =>
    match xs with
    | [] => [v]
    | h :: t => v :: h :: t
private theorem uCN_eq (x : ℕ) (xs : List ℕ) : uCN x xs = x :: xs := by
  unfold uCN; rw [n1a]; cases xs <;> rfl
private def uHb : List ℕ → List ℤ
  | [] => []
  | n :: ns => Int.ofNat n :: uHb ns
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
private theorem czEq (x : ℤ) (xs : List ℤ) : bCZ x xs = x :: xs := by
  cases x <;> cases xs <;> rfl
private theorem onEq (x : ℕ) : primOfNatForced x = Int.ofNat x := by
  simp [primOfNatForced, Nat.one_add]
private theorem nsEq (x : ℕ) : primNegSuccForced x = Int.negSucc x := by
  simp [primNegSuccForced, Nat.one_add]
private theorem sbEq (u z : ℕ) : rkmForcedSubNatNat u z = (u : ℤ) - (z : ℤ) := by
  unfold rkmForcedSubNatNat; rw [onEq, Nat.sub_eq]; cases h : z - u with
  | zero => dsimp only; rw [Nat.sub_eq, Int.ofNat_eq_natCast]; omega
  | succ k => dsimp only; rw [Int.negSucc_eq]; omega
private def bD (z : ℕ) : List ℕ → List ℤ
  | [] => []
  | u :: us => bCZ (rkmForcedSubNatNat u z) (bD z us)
private theorem d0 (z : ℕ) : bD z [] = [] := rfl
private theorem dc (z u : ℕ) (us : List ℕ) :
    bD z (u :: us) = ((u : ℤ) - (z : ℤ)) :: bD z us := by rw [bD, czEq, sbEq]
private theorem bZ0 (z : ℕ) : ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [Int.ofNat_eq_natCast]; omega
private theorem bM0 (z : ℕ) : muxRawIntMul (Int.ofNat 0) ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [bZ0]; rfl
private def bE1 (z : ℕ) : ℤ → Option ℕ
  | Int.ofNat n => some (Nat.add z n)
  | Int.negSucc k =>
    match Nat.sub z (Nat.add k 1) with
    | 0 => none
    | w + 1 => some (Nat.add w 1)
private def bE (z : ℕ) : List ℤ → Option (List ℕ)
  | [] => some []
  | x :: xs =>
    match bE1 z x with
    | none => none
    | some u =>
      match bE z xs with
      | none => none
      | some us => some (uCN u us)
private theorem e1S (z : ℕ) (x : ℤ) (u : ℕ) (h : bE1 z x = some u) :
    ((u : ℤ) - (z : ℤ)) = x := by
  cases x with
  | ofNat n =>
    unfold bE1 at h; injection h with h'; subst h'; rw [Nat.add_eq, Int.ofNat_eq_natCast]; omega
  | negSucc k =>
    unfold bE1 at h; simp only [Nat.sub_eq, Nat.add_eq] at h; revert h
    cases hz : z - (k + 1) with
    | zero => intro h; dsimp only at h; cases h
    | succ w =>
      intro h; dsimp only at h; injection h with h'; subst h'; rw [Int.negSucc_eq]; omega
private theorem eS (z : ℕ) : ∀ (xs : List ℤ) (us : List ℕ), bE z xs = some us →
    bD z us = xs
  | [], us, h => by injection h with h'; subst h'; rfl
  | x :: xs, us, h => by
    dsimp only [bE] at h; revert h; cases hx : bE1 z x with
    | none => intro h; dsimp only at h; cases h
    | some u =>
      dsimp only; cases hxs : bE z xs with
      | none => intro h; dsimp only at h; cases h
      | some ws =>
        intro h; dsimp only at h; injection h with h'; subst h'
        rw [uCN_eq, dc, e1S z x u hx, eS z xs ws hxs]
private def zTdiv (x : ℤ) (d : ℕ) : ℤ :=
  match x with
  | Int.ofNat m => Int.ofNat (m / d)
  | Int.negSucc k => -(((k + 1) / d : ℕ) : ℤ)
private theorem ngEq : ∀ (n : ℕ), muxRawNegOfNat n = -(n : ℤ)
  | 0 => by dsimp only [muxRawNegOfNat]; rw [Int.ofNat_eq_natCast]; omega
  | k + 1 => by dsimp only [muxRawNegOfNat]; rw [Int.negSucc_eq]; omega
private theorem tdEq : ∀ (x : ℤ) (d : ℕ), muxRawIntTdivNat x d = zTdiv x d
  | Int.ofNat _, _ => rfl
  | Int.negSucc k, d => by dsimp only [muxRawIntTdivNat, zTdiv]; rw [ngEq, ndiv, Nat.add_eq]
private theorem sntEq (m n d : ℕ) :
    rkmUltraSubNatTdiv m n d = zTdiv ((m : ℤ) - (n : ℤ)) d := by
  unfold rkmUltraSubNatTdiv; simp only [Nat.sub_eq, ndiv, Nat.add_eq]; cases h : n - m with
  | zero =>
    have hm : (m : ℤ) - (n : ℤ) = Int.ofNat (m - n) := by rw [Int.ofNat_eq_natCast]; omega
    rw [hm]; rfl
  | succ k =>
    dsimp only; have hm : (m : ℤ) - (n : ℤ) = Int.negSucc k := by rw [Int.negSucc_eq]; omega
    rw [hm]; dsimp only [zTdiv]; rw [ngEq]
private theorem stEq (a b : ℤ) (d : ℕ) : rkmUltraSubTdiv a b d = zTdiv (a - b) d := by
  cases a with
  | ofNat m => cases b with
    | ofNat n => exact sntEq m n d
    | negSucc n =>
      have hm : Int.ofNat m - Int.negSucc n = Int.ofNat (m + (n + 1)) := by
        rw [Int.ofNat_eq_natCast, Int.negSucc_eq, Int.ofNat_eq_natCast]; omega
      rw [hm]; rfl
  | negSucc m => cases b with
    | ofNat n =>
      have hm : Int.negSucc m - Int.ofNat n = Int.negSucc (m + n) := by
        rw [Int.negSucc_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]; omega
      dsimp only [rkmUltraSubTdiv]; rw [hm]; dsimp only [zTdiv]; rw [ngEq, ndiv, Nat.add_eq]
      rw [Nat.add_eq]; exact congrArg (fun t : ℕ => -(((t / d : ℕ) : ℤ))) (by omega)
    | negSucc n =>
      dsimp only [rkmUltraSubTdiv]; rw [sntEq, Nat.add_eq, Nat.add_eq]
      exact congrArg (fun t => zTdiv t d) (by simp only [Int.negSucc_eq]; omega)
private theorem mlEq : ∀ (a b : ℤ), muxRawIntMul a b = a * b
  | Int.ofNat m, Int.ofNat n => by
    dsimp only [muxRawIntMul]; rw [Nat.mul_eq]; simp only [Int.ofNat_eq_natCast]; push_cast; ring
  | Int.ofNat m, Int.negSucc n => by
    dsimp only [muxRawIntMul]; rw [ngEq, Nat.mul_eq, Nat.add_eq]
    rw [Int.ofNat_eq_natCast, Int.negSucc_eq]; push_cast; ring
  | Int.negSucc m, Int.ofNat n => by
    dsimp only [muxRawIntMul]; rw [ngEq, Nat.mul_eq, Nat.add_eq]
    rw [Int.negSucc_eq, Int.ofNat_eq_natCast]; push_cast; ring
  | Int.negSucc m, Int.negSucc n => by
    dsimp only [muxRawIntMul]; rw [Nat.mul_eq, Nat.add_eq, Nat.add_eq, Int.ofNat_eq_natCast]
    simp only [Int.negSucc_eq]; push_cast; ring
private theorem faEq : ∀ (a b : ℤ), rkmForcedIntAdd a b = a + b
  | Int.ofNat m, Int.ofNat n => by
    dsimp only [rkmForcedIntAdd]; rw [onEq, Nat.add_eq]
    simp only [Int.ofNat_eq_natCast]; omega
  | Int.ofNat m, Int.negSucc n => by
    dsimp only [rkmForcedIntAdd]; rw [sbEq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
    omega
  | Int.negSucc m, Int.ofNat n => by
    dsimp only [rkmForcedIntAdd]; rw [sbEq, Nat.add_eq, Int.negSucc_eq, Int.ofNat_eq_natCast]
    omega
  | Int.negSucc m, Int.negSucc n => by
    dsimp only [rkmForcedIntAdd]; rw [nsEq, Nat.add_eq, Nat.add_eq]
    simp only [Int.negSucc_eq]; omega
private theorem acEq (a b : ℤ) (xs : List ℤ) : rkmUltraAddCons a b xs = (a + b) :: xs := by
  unfold rkmUltraAddCons; rw [faEq]; cases a + b <;> cases xs <;> rfl
private def bSV (v P Q d : ℕ) : ℕ :=
  match Nat.add 1 P with
  | 0 => 0
  | pF + 1 =>
    match Nat.add 1 Q with
    | 0 => 0
    | qF + 1 =>
      match Nat.sub qF pF with
      | 0 => Nat.add v (Nat.div (Nat.sub pF qF) d)
      | k + 1 => Nat.sub v (Nat.div (Nat.add k 1) d)
private theorem svEq (z v P Q d : ℕ) (hv : 0 < bSV v P Q d) :
    ((bSV v P Q d : ℤ) - (z : ℤ)) = ((v : ℤ) - (z : ℤ)) + zTdiv ((P : ℤ) - (Q : ℤ)) d := by
  unfold bSV at hv ⊢; rw [n1a P, n1a Q] at hv ⊢; dsimp only at hv ⊢
  rw [← sntEq]; unfold rkmUltraSubNatTdiv
  simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢; revert hv; cases h : Q - P with
  | zero => intro _; dsimp only; rw [Int.ofNat_eq_natCast]; push_cast; ring
  | succ k => intro hv; dsimp only at hv ⊢; rw [ngEq]; omega
private abbrev bCV (z d b0 c0 b v c1 : ℕ) : ℕ :=
  bSV v (Nat.add (Nat.mul b0 c0) (Nat.mul b z)) (Nat.add (Nat.mul b c1) (Nat.mul b0 z)) d
private theorem bCell_hb (z d b0 c0 b v c1 : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bCV z d b0 c0 b v c1) (ht : bD z rest = tailZ) :
    bD z (uCN (bCV z d b0 c0 b v c1) rest) =
      rkmUltraAddCons ((v : ℤ) - (z : ℤ))
        (rkmUltraSubTdiv (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
          (muxRawIntMul (Int.ofNat b) ((c1 : ℤ) - (z : ℤ))) d) tailZ := by
  rw [uCN_eq, dc, ht, acEq, stEq, mlEq, mlEq]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.add (Nat.mul b0 c0) (Nat.mul b z) : ℕ) : ℤ) -
      ((Nat.add (Nat.mul b c1) (Nat.mul b0 z) : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) - (Int.ofNat b) * ((c1 : ℤ) - (z : ℤ)) := by
    simp only [Nat.add_eq, Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  unfold bCV at hv ⊢; rw [svEq z v _ _ d hv, hpq]
private theorem bCell_nil (z d b0 c0 v : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bSV v (Nat.mul b0 c0) (Nat.mul b0 z) d) (ht : bD z rest = tailZ) :
    bD z (uCN (bSV v (Nat.mul b0 c0) (Nat.mul b0 z) d) rest) =
      rkmUltraAddCons ((v : ℤ) - (z : ℤ))
        (muxRawIntTdivNat (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ))) d) tailZ := by
  rw [uCN_eq, dc, ht, acEq, tdEq, mlEq]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.mul b0 c0 : ℕ) : ℤ) - ((Nat.mul b0 z : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) := by
    simp only [Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  rw [svEq z v _ _ d hv, hpq]
private def bAP : List ℕ → Bool
  | [] => true
  | x :: xs => cond (Nat.ble x 0) false (bAP xs)
private theorem apC {x : ℕ} {xs : List ℕ} (h : bAP (uCN x xs) = true) :
    0 < x ∧ bAP xs = true := by
  rw [uCN_eq] at h
  cases x with
  | zero => exact Bool.noConfusion h
  | succ k => exact ⟨Nat.succ_pos k, h⟩
private def bHO (z : ℕ) : List ℕ → ℕ
  | [] => z
  | x :: _ => x
private def bTN : List ℕ → List ℕ
  | [] => []
  | _ :: xs => xs
private theorem hoEq (z : ℕ) : ∀ (cs : List ℕ),
    ((bHO z cs : ℤ) - (z : ℤ)) = (match bD z cs with | cn :: _ => cn | [] => Int.ofNat 0)
  | [] => by unfold bHO; rw [d0, bZ0]
  | c :: cs => by unfold bHO; rw [dc]
private theorem tnEq (z : ℕ) : ∀ (xs : List ℕ),
    bD z (bTN xs) = (match bD z xs with | _ :: t => t | [] => [])
  | [] => rfl
  | x :: xs => by unfold bTN; rw [dc]
private def bSl (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, b0, c0, bns, vs, cs =>
    match bns with
    | [] => uCN (bSV (bHO z vs) (Nat.mul b0 c0) (Nat.mul b0 z) d)
        (bSl z d rem 0 z [] (bTN vs) (bTN cs))
    | b :: bR =>
      match vs, cs with
      | v :: vT, c :: cT =>
        uCN (bCV z d b0 c0 b v (bHO z cT)) (bSl z d rem b c bR vT cT)
      | v :: vT, [] => uCN (bCV z d b0 c0 b v z) (bSl z d rem b z bR vT [])
      | [], c :: cT => uCN (bCV z d b0 c0 b z (bHO z cT)) (bSl z d rem b c bR [] cT)
      | [], [] => uCN (bCV z d b0 c0 b z z) (bSl z d rem b z bR [] [])
private theorem bSl_sound (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bAP (bSl z d rem b0 c0 bns vs cs) = true →
      bD z (bSl z d rem b0 c0 bns vs cs) =
        rkmUltraSlideLoopAux d rem (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
          (uHb bns) (bD z vs) (bD z cs)
  | 0, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs, h => by
    cases bns with
    | nil =>
      dsimp only [bSl, uHb, rkmUltraSlideLoopAux] at h ⊢; have hp := apC h
      have hi := bSl_sound z d rem 0 z [] (bTN vs) (bTN cs) hp.2
      rw [bM0, uHb, tnEq z vs, tnEq z cs] at hi
      have hc := bCell_nil z d b0 c0 (bHO z vs) hp.1 hi; rw [hoEq z vs] at hc; exact hc
    | cons b bR =>
      cases vs with
      | nil => cases cs with
        | nil =>
          dsimp only [bSl, uHb] at h ⊢; rw [d0, rkmUltraSlideLoopAux]
          have hp := apC h; have hi := bSl_sound z d rem b z bR [] [] hp.2
          rw [bZ0 z, d0] at hi; have hc := bCell_hb z d b0 c0 b z z hp.1 hi
          rw [bZ0 z] at hc; exact hc
        | cons c cT =>
          dsimp only [bSl, uHb] at h ⊢; rw [d0, dc z c cT]
          dsimp only [rkmUltraSlideLoopAux]; have hp := apC h
          have hi := bSl_sound z d rem b c bR [] cT hp.2; rw [d0] at hi
          have hc := bCell_hb z d b0 c0 b z (bHO z cT) hp.1 hi
          rw [hoEq z cT, bZ0 z] at hc; exact hc
      | cons v vT => cases cs with
        | nil =>
          dsimp only [bSl, uHb] at h ⊢; rw [dc z v vT, d0]
          dsimp only [rkmUltraSlideLoopAux]; have hp := apC h
          have hi := bSl_sound z d rem b z bR vT [] hp.2; rw [bZ0 z, d0] at hi
          have hc := bCell_hb z d b0 c0 b v z hp.1 hi; rw [bZ0 z] at hc; exact hc
        | cons c cT =>
          dsimp only [bSl, uHb] at h ⊢; rw [dc z v vT, dc z c cT]
          dsimp only [rkmUltraSlideLoopAux]; have hp := apC h
          have hi := bSl_sound z d rem b c bR vT cT hp.2
          have hc := bCell_hb z d b0 c0 b v (bHO z cT) hp.1 hi; rw [hoEq z cT] at hc
          exact hc
private def mkHbZ (z : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: bs => uCN b (uCN (Nat.mul b z) (mkHbZ z bs))
private def bSlZ (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, p0, q0, hbz, vs, cs =>
    match hbz with
    | [] =>
      uCN (bSV (bHO z vs) p0 q0 d) (bSlZ z d rem 0 0 [] (bTN vs) (bTN cs))
    | [_] => []
    | b :: bz :: bR =>
      match vs, cs with
      | v :: vT, c :: cT =>
        fN (Nat.mul b c) fun bc =>
          uCN (bSV v (Nat.add p0 bz) (Nat.add (Nat.mul b (bHO z cT)) q0) d)
            (bSlZ z d rem bc bz bR vT cT)
      | v :: vT, [] =>
        uCN (bSV v (Nat.add p0 bz) (Nat.add bz q0) d) (bSlZ z d rem bz bz bR vT [])
      | [], c :: cT =>
        fN (Nat.mul b c) fun bc =>
          uCN (bSV z (Nat.add p0 bz) (Nat.add (Nat.mul b (bHO z cT)) q0) d)
            (bSlZ z d rem bc bz bR [] cT)
      | [], [] =>
        uCN (bSV z (Nat.add p0 bz) (Nat.add bz q0) d) (bSlZ z d rem bz bz bR [] [])
private theorem bSlZ_eq (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bSlZ z d rem (Nat.mul b0 c0) (Nat.mul b0 z) (mkHbZ z bns) vs cs = bSl z d rem b0 c0 bns vs cs
  | 0, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs => by
    cases bns with
    | nil =>
      have hrec := bSlZ_eq z d rem 0 z [] (bTN vs) (bTN cs)
      have hz0 : Nat.mul 0 z = 0 := by rw [Nat.mul_eq]; omega
      dsimp only [mkHbZ] at hrec; rw [hz0] at hrec; dsimp only [mkHbZ, bSlZ, bSl]; rw [hrec]
    | cons b bR =>
      dsimp only [mkHbZ]; rw [uCN_eq, uCN_eq]; cases vs with
      | nil => cases cs with
        | nil => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b z bR [] []]
        | cons c cT =>
          dsimp only [bSlZ, bSl, bCV, fN]; rw [rkmb_forceNat_eq, bSlZ_eq z d rem b c bR [] cT]
      | cons v vT => cases cs with
        | nil => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b z bR vT []]
        | cons c cT =>
          dsimp only [bSlZ, bSl, bCV, fN]; rw [rkmb_forceNat_eq, bSlZ_eq z d rem b c bR vT cT]
private def bStg (z dg mL cL : ℕ) (hbz v c : List ℕ) : Option (List ℕ) :=
  fN (rkmNextLen mL cL) fun nL => fN (Nat.mul dg wdScale) fun d =>
    fL (bSlZ z d nL 0 0 hbz v c) fun out => cond (bAP out) (some out) none
private theorem bStg_sound (z dg mL cL : ℕ) (b v c out : List ℕ)
    (h : bStg z dg mL cL (mkHbZ z b) v c = some out) :
    bD z out = rkmUltraHornerStage dg mL cL (uHb b) (bD z v) (bD z c) := by
  have hsl := bSlZ_eq z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b v c
  have hz0 : Nat.mul 0 z = 0 := by rw [Nat.mul_eq]; omega
  rw [hz0] at hsl; unfold bStg at h; dsimp only [fN, fL] at h
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceList_eq, hsl] at h; revert h
  cases hp : bAP (bSl z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b v c) with
  | false => intro h; dsimp only [cond] at h; cases h
  | true =>
    intro h; injection h with h'; subst h'; unfold rkmUltraHornerStage
    rw [rkmb_forceNat_eq, rkmb_forceNat_eq, ← bM0 z]; exact bSl_sound z _ _ 0 z b v c hp
private def bBind (z g m c : ℕ) (hbz v x : List ℕ)
    (k : ℕ → List ℕ → Option (List ℕ)) : Option (List ℕ) :=
  fN (rkmNextLen m c) fun n =>
    match bStg z g m c hbz v x with
    | none => none
    | some o => k n o
private theorem bBind_sound {z g m c : ℕ} {b v x out : List ℕ}
    {kB : ℕ → List ℕ → Option (List ℕ)} {kU : ℕ → List ℤ → List ℤ}
    (h : bBind z g m c (mkHbZ z b) v x kB = some out)
    (hk : ∀ m0, kB (rkmNextLen m c) m0 = some out → bD z out = kU (rkmNextLen m c) (bD z m0)) :
    bD z out = (HighDForce.withForcedNat (rkmNextLen m c) fun nL =>
      HighDForce.withForcedList
        (rkmUltraHornerStage g m c (uHb b) (bD z v) (bD z x)) (kU nL)) := by
  unfold bBind at h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h; revert h
  cases hs : bStg z g m c (mkHbZ z b) v x with
  | none => intro h; dsimp only at h; cases h
  | some mid =>
    intro h; rw [rkmb_forceNat_eq, rkmb_forceList_eq, ← bStg_sound z g m c b v x mid hs]
    exact hk mid h
private def bSp (z m c : ℕ) (hbz v : List ℕ) : Option (List ℕ) :=
  bBind z 16 m c hbz v v fun l x => bBind z 15 m l hbz v x fun l x =>
  bBind z 14 m l hbz v x fun l x => bBind z 13 m l hbz v x fun l x =>
  bBind z 12 m l hbz v x fun l x => bBind z 11 m l hbz v x fun l x =>
  bBind z 10 m l hbz v x fun l x => bBind z 9 m l hbz v x fun l x =>
  bBind z 8 m l hbz v x fun l x => bBind z 7 m l hbz v x fun l x =>
  bBind z 6 m l hbz v x fun l x => bBind z 5 m l hbz v x fun l x =>
  bBind z 4 m l hbz v x fun l x => bBind z 3 m l hbz v x fun l x =>
  bBind z 2 m l hbz v x fun l x => bStg z 1 m l hbz v x
private theorem bSp_sound (z mL cL : ℕ) (b v out : List ℕ)
    (h : bSp z mL cL (mkHbZ z b) v = some out) :
    bD z out = rkmUltraHornerT16Step mL cL (uHb b) (bD z v) := by
  unfold bSp at h; unfold rkmUltraHornerT16Step
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  exact bStg_sound z 1 mL _ b v _ out h
private def bIt (z : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → Option (List ℕ)
  | 0, _, _, _, v => some v
  | k + 1, m, c, hbz, v =>
    match bSp z m c hbz v with
    | none => none
    | some vN => fN (rkmNextLen16 m c) fun nL => bIt z k m nL hbz vN
private theorem bIt_sound (z : ℕ) : ∀ (k m c : ℕ) (b v out : List ℕ),
    bIt z k m c (mkHbZ z b) v = some out →
      bD z out = muxUltraIterFullT16Rkm k m c (uHb b) (bD z v)
  | 0, _, _, _, _, _, h => by injection h with h'; subst h'; rfl
  | k + 1, m, c, b, v, out, h => by
    unfold bIt at h; revert h; cases hs : bSp z m c (mkHbZ z b) v with
    | none => intro h; dsimp only at h; cases h
    | some vN =>
      intro h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h; unfold muxUltraIterFullT16Rkm
      rw [rkmb_forceList_eq, rkmb_forceNat_eq, ← bSp_sound z m c b v vN hs]
      exact bIt_sound z k m _ b vN out h
private def bDropB : ℕ → List Bool → List Bool
  | 0, bs => bs
  | _, [] => []
  | k + 1, _ :: bs => bDropB k bs
private def drN : ℕ → List ℕ → List ℕ
  | 0, xs => xs
  | _, [] => []
  | k + 1, _ :: xs => drN k xs
private theorem dnEq : ∀ (s : ℕ) (b : List ℕ),
    uHb (drN s b) = rkmDropInts s (uHb b)
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, _ :: bs => dnEq k bs
private def dr2 : ℕ → List ℕ → List ℕ
  | 0, xs => xs
  | k + 1, _ :: _ :: xs => dr2 k xs
  | _, _ => []
private theorem d2Eq (z : ℕ) : ∀ (s : ℕ) (b : List ℕ),
    dr2 s (mkHbZ z b) = mkHbZ z (drN s b)
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, _ :: bs => by
    dsimp only [mkHbZ, drN]; rw [uCN_eq, uCN_eq]
    dsimp only [dr2]; exact d2Eq z k bs
private theorem dr_hbS (m r hPt k rem w : ℕ) :
    rkmDropInts (k + 1) (altBuildHbFromAux m r hPt (rem + 1) w) =
      rkmDropInts k (altBuildHbFromAux m r hPt rem (w + 1)) := by
  dsimp only [altBuildHbFromAux]; rw [strictConsInt_eq, Nat.add_eq]; rfl
private theorem dr_hbA (m r hPt : ℕ) : ∀ (k rem w : ℕ),
    rkmDropInts k (altBuildHbFromAux m r hPt rem w) = altBuildHbFromAux m r hPt (rem - k) (w + k)
  | 0, _, _ => rfl
  | _ + 1, 0, _ => by rw [Nat.zero_sub]; rfl
  | k + 1, rem + 1, w => by
    rw [dr_hbS, dr_hbA m r hPt k rem (w + 1), Nat.succ_sub_succ_eq_sub,
      show w + 1 + k = w + (k + 1) by omega]
private theorem drHb (m r hPt w0 d : ℕ) :
    altBuildHbFrom m r hPt w0 (d - w0) = rkmDropInts w0 (altBuildHbFrom m r hPt 0 d) := by
  unfold altBuildHbFrom; rw [dr_hbA, Nat.zero_add]
private theorem dr_add : ∀ (a b : ℕ) (xs : List ℤ),
    rkmDropInts (a + b) xs = rkmDropInts b (rkmDropInts a xs)
  | 0, b, _ => by rw [Nat.zero_add b]; rfl
  | _ + 1, b, [] => by rw [Nat.succ_add]; cases b <;> rfl
  | a + 1, b, _ :: xs => by rw [Nat.succ_add]; exact dr_add a b xs
private def bAZ (z u : ℕ) : ℕ := Nat.add (Nat.sub u z) (Nat.sub z u)
private theorem azEq (z u : ℕ) : bAZ z u = rkmIntAbsNat ((u : ℤ) - (z : ℤ)) := by
  unfold bAZ; simp only [Nat.add_eq, Nat.sub_eq]; cases h : z - u with
  | zero =>
    have hm : (u : ℤ) - (z : ℤ) = Int.ofNat (u - z) := by rw [Int.ofNat_eq_natCast]; omega
    rw [hm]; dsimp only [rkmIntAbsNat]; omega
  | succ k =>
    have hm : (u : ℤ) - (z : ℤ) = Int.negSucc k := by rw [Int.negSucc_eq]; omega
    rw [hm]; dsimp only [rkmIntAbsNat]; rw [Nat.add_eq]; omega
private def bPZ (z : ℕ) : ℕ → List ℕ → List ℕ
  | 0, us => us
  | k + 1, us => uCN z (bPZ z k us)
private theorem pzEq (z : ℕ) : ∀ (k : ℕ) (us : List ℕ),
    bD z (bPZ z k us) = rkmPrependZeros k (bD z us)
  | 0, _ => rfl
  | k + 1, us => by
    dsimp only [bPZ, rkmPrependZeros]
    rw [uCN_eq, dc, bZ0 z, rkmw_strictConsInt_eq, pzEq z k us]
private def bNL : List ℕ → ℕ
  | [] => 0
  | _ :: us => Nat.add (bNL us) 1
private theorem nlEq (z : ℕ) : ∀ (us : List ℕ), bNL us = altIntLen (bD z us)
  | [] => by rw [d0, rkmw_altIntLen_eq]; rfl
  | u :: us => by
    dsimp only [bNL]; rw [Nat.add_eq, nlEq z us, dc]
    rw [rkmw_altIntLen_eq, rkmw_altIntLen_eq]; simp only [List.length_cons]
private def bTL (z thr : ℕ) : ℕ → List ℕ → ℕ → ℕ × List ℕ × ℕ
  | _, [], acc => (0, [], acc)
  | off, u :: us, acc =>
    fN (bAZ z u) fun ax =>
      match Nat.ble ax thr with
      | true =>
        fN (Nat.add off 1) fun off1 =>
          fN (Nat.add acc ax) fun acc1 => bTL z thr off1 us acc1
      | false => (off, u :: us, acc)
private theorem tlEq (z thr : ℕ) : ∀ (us : List ℕ) (off acc : ℕ),
    ((bTL z thr off us acc).1, bD z (bTL z thr off us acc).2.1,
      (bTL z thr off us acc).2.2) = rkmTrimLeft thr off (bD z us) acc
  | [], _, _ => by rw [d0]; rfl
  | u :: us, off, acc => by
    rw [dc]; dsimp only [bTL, rkmTrimLeft, fN]; simp only [rkmb_forceNat_eq]
    rw [azEq z u]; cases Nat.ble (rkmIntAbsNat ((u : ℤ) - (z : ℤ))) thr with
    | false => dsimp only; rw [dc]
    | true =>
      dsimp only
      exact tlEq z thr us (Nat.add off 1) (Nat.add acc (rkmIntAbsNat ((u : ℤ) - (z : ℤ))))
private def bTR (z thr : ℕ) : List ℕ → List ℕ × ℕ
  | [] => ([], 0)
  | u :: us =>
    match bTR z thr us with
    | ([], dTail) =>
      fN (bAZ z u) fun ax =>
        match Nat.ble ax thr with
        | true => fN (Nat.add ax dTail) fun dSum => ([], dSum)
        | false => (uCN u [], dTail)
    | (v :: vs, dTail) => (uCN u (v :: vs), dTail)
private theorem trEq (z thr : ℕ) : ∀ (us : List ℕ),
    (bD z (bTR z thr us).1, (bTR z thr us).2) = rkmTrimRight thr (bD z us)
  | [] => by rw [d0]; rfl
  | u :: us => by
    rw [dc z u us]; dsimp only [bTR, rkmTrimRight]; rw [← trEq z thr us]
    rcases bTR z thr us with ⟨ws, dTail⟩; cases ws with
    | nil =>
      dsimp only; rw [d0]; dsimp only [fN]; simp only [rkmb_forceNat_eq]; rw [azEq z u]
      cases Nat.ble (rkmIntAbsNat ((u : ℤ) - (z : ℤ))) thr with
      | true => rfl
      | false => dsimp only; rw [uCN_eq, dc, d0, rkmw_strictConsInt_eq]
    | cons v vs =>
      dsimp only; rw [dc z v vs]; dsimp only
      rw [uCN_eq, dc, dc z v vs, rkmw_strictConsInt_eq]
private def bTW (z thr off : ℕ) (us : List ℕ) (dropAcc : ℕ) : ℕ × List ℕ × ℕ :=
  match bTL z thr off us dropAcc with
  | (off1, us1, d1) =>
    match bTR z thr us1 with
    | ([], d2) => fN (Nat.add d1 d2) fun dOut => (0, [], dOut)
    | (v :: vs, d2) => fN (Nat.add d1 d2) fun dOut => (off1, v :: vs, dOut)
private theorem twEq (z thr off : ℕ) (us : List ℕ) (dropAcc : ℕ) :
    ((bTW z thr off us dropAcc).1, bD z (bTW z thr off us dropAcc).2.1,
      (bTW z thr off us dropAcc).2.2) = rkmTrimWin thr off (bD z us) dropAcc := by
  dsimp only [bTW, rkmTrimWin]; rw [← tlEq z thr us off dropAcc]
  rcases bTL z thr off us dropAcc with ⟨off1, us1, d1⟩; dsimp only; rw [← trEq z thr us1]
  rcases bTR z thr us1 with ⟨ws, d2⟩; cases ws with
  | nil => dsimp only [fN]; simp only [rkmb_forceNat_eq]; rfl
  | cons v vs => dsimp only [fN]; simp only [rkmb_forceNat_eq]; rw [dc z v vs]
private def bWS (z w0 thr d : ℕ) (hbz : List ℕ)
    (off : ℕ) (us : List ℕ) (dropAcc : ℕ) : Option (ℕ × List ℕ × ℕ) :=
  fN (Nat.sub off 16) fun sLo =>
    match Nat.ble w0 sLo with
    | false => none
    | true =>
      fN (Nat.sub sLo w0) fun kD => fN (Nat.sub off sLo) fun padL =>
        fN (Nat.sub (Nat.add d 1) sLo) fun remMax => fL (dr2 kD hbz) fun hbzSl =>
          fL (bPZ z padL us) fun vns => fN (bNL vns) fun curLen =>
            match bIt z 1 remMax curLen hbzSl vns with
            | none => none
            | some out => some (bTW z thr sLo out dropAcc)
private theorem wsS (z w0 thr d : ℕ) {hb : List ℤ} {b : List ℕ}
    (hhb : uHb b = rkmDropInts w0 hb)
    (off : ℕ) (us : List ℕ) (dropAcc o1 : ℕ) (u1 : List ℕ) (d1 : ℕ)
    (h : bWS z w0 thr d (mkHbZ z b) off us dropAcc = some (o1, u1, d1)) :
    (o1, bD z u1, d1) = muxWinStepT16 thr d hb off (bD z us) dropAcc := by
  unfold bWS at h; unfold muxWinStepT16; dsimp only [fN, fL] at h
  rw [rkmb_forceNat_eq] at h
  cases hb0 : Nat.ble w0 (Nat.sub off 16) with
  | false => rw [hb0] at h; cases h
  | true =>
    rw [hb0] at h; simp only [rkmb_forceNat_eq, rkmb_forceList_eq] at h ⊢
    set sLo := Nat.sub off 16; set kD := Nat.sub sLo w0
    set padL := Nat.sub off sLo; set remMax := Nat.sub (Nat.add d 1) sLo
    set vns := bPZ z padL us
    rw [d2Eq] at h; revert h
    cases hi : bIt z 1 remMax (bNL vns) (mkHbZ z (drN kD b)) vns with
    | none => intro h; cases h
    | some out =>
      intro h; injection h with h'
      have ho : o1 = (bTW z thr sLo out dropAcc).1 := (congrArg Prod.fst h').symm
      have hu : u1 = (bTW z thr sLo out dropAcc).2.1 := (congrArg (fun p => p.2.1) h').symm
      have hd : d1 = (bTW z thr sLo out dropAcc).2.2 := (congrArg (fun p => p.2.2) h').symm
      have hkd : uHb (drN kD b) = rkmDropInts sLo hb := by
        rw [dnEq kD b, hhb, ← dr_add w0 kD hb]
        have hw : w0 + kD = sLo := by
          have hle := rkmw_nat_ble_eq_true.mp hb0; dsimp only [kD]; rw [Nat.sub_eq]; omega
        rw [hw]
      rw [ho, hu, hd, twEq z thr sLo out dropAcc]
      rw [bIt_sound z 1 remMax (bNL vns) (drN kD b) vns out hi, hkd]
      dsimp only [vns]; rw [nlEq z (bPZ z padL us), pzEq z padL us]
private def bWI (z w0 : ℕ) : ℕ → ℕ → ℕ → List ℕ → ℕ → List ℕ → ℕ →
    Option (ℕ × List ℕ × ℕ)
  | 0, _, _, _, off, us, dropAcc => some (off, us, dropAcc)
  | k + 1, thr, d, hbz, off, us, dropAcc =>
    match bWS z w0 thr d hbz off us dropAcc with
    | none => none
    | some (off1, us1, drop1) => bWI z w0 k thr d hbz off1 us1 drop1
private theorem wiS (z w0 : ℕ) {hb : List ℤ} {b : List ℕ}
    (hhb : uHb b = rkmDropInts w0 hb) :
    ∀ (k thr d off : ℕ) (us : List ℕ) (dropAcc oR : ℕ) (uR : List ℕ) (dR : ℕ),
      bWI z w0 k thr d (mkHbZ z b) off us dropAcc = some (oR, uR, dR) →
        (oR, bD z uR, dR) = muxWinIterT16 k thr d hb off (bD z us) dropAcc
  | 0, _, _, off, us, dropAcc, oR, uR, dR, h => by
    dsimp only [bWI, muxWinIterT16] at h ⊢; injection h with h'
    rcases Prod.mk.inj h' with ⟨rfl, h2⟩; rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩; rfl
  | k + 1, thr, d, off, us, dropAcc, oR, uR, dR, h => by
    dsimp only [bWI, muxWinIterT16] at h ⊢; revert h
    cases hs : bWS z w0 thr d (mkHbZ z b) off us dropAcc with
    | none => intro h; cases h
    | some res1 =>
      rcases res1 with ⟨o1, u1, d1⟩; intro h
      rw [← wsS z w0 thr d hhb off us dropAcc o1 u1 d1 hs]
      exact wiS z w0 hhb k thr d o1 u1 d1 oR uR dR h
private def bNE (a b : ℕ) : Bool := Bool.and (Nat.ble a b) (Nat.ble b a)
private theorem neT {a b : ℕ} (h : bNE a b = true) : a = b := by
  unfold bNE at h; simp only [Bool.and_eq_true, rkmw_nat_ble_eq_true] at h
  exact Nat.le_antisymm h.1 h.2
private def bWinChk (w0 steps thr d : ℕ) (b : List ℕ)
    (offIn : ℕ) (xsIn : List ℤ) (offOut : ℕ) (xsOut : List ℤ) (dropExp : ℕ) : Bool :=
  fL b fun bF => fL (mkHbZ bz0 bF) fun hbz => fL xsIn fun inF => fL xsOut fun outF =>
    match bE bz0 inF with
    | none => false
    | some uIn =>
      match bWI bz0 w0 steps thr d hbz offIn uIn 0 with
      | none => false
      | some (oR, uR, dR) =>
        Bool.and (bNE oR offOut)
          (Bool.and (muxIntListEq (bD bz0 uR) outF) (bNE dR dropExp))
private theorem bWinChk_sound {w0 steps thr d : ℕ} {hb : List ℤ} {b : List ℕ}
    (hhb : uHb b = rkmDropInts w0 hb)
    {offIn : ℕ} {xsIn : List ℤ} {offOut : ℕ} {xsOut : List ℤ} {dropExp : ℕ}
    (h : bWinChk w0 steps thr d b offIn xsIn offOut xsOut dropExp = true) :
    RkmWinIterSound steps d hb offIn xsIn offOut xsOut dropExp := by
  unfold bWinChk at h; dsimp only [fL] at h; simp only [rkmb_forceList_eq] at h
  revert h; cases he : bE bz0 xsIn with
  | none => intro h; cases h
  | some uIn =>
    intro h
    change (match bWI bz0 w0 steps thr d (mkHbZ bz0 b) offIn uIn 0 with
      | none => false
      | some (oR, uR, dR) =>
        Bool.and (bNE oR offOut)
          (Bool.and (muxIntListEq (bD bz0 uR) xsOut) (bNE dR dropExp))) = true at h
    revert h
    cases hi : bWI bz0 w0 steps thr d (mkHbZ bz0 b) offIn uIn 0 with
    | none => intro h; cases h
    | some res =>
      rcases res with ⟨oR, uR, dR⟩; intro h
      change Bool.and (bNE oR offOut)
        (Bool.and (muxIntListEq (bD bz0 uR) xsOut) (bNE dR dropExp)) = true at h
      simp only [Bool.and_eq_true, muxIntListEq_eq_true] at h
      obtain ⟨ho, hx, hd⟩ := h; have ho' := neT ho; have hd' := neT hd
      rw [← ho', ← hx, ← hd']
      have hit := wiS bz0 w0 hhb steps thr d offIn uIn 0 oR uR dR hi
      rw [eS bz0 xsIn uIn he] at hit
      have h2 : muxWinIterT16HiChk steps thr 0 d hb offIn xsIn oR (bD bz0 uR) dR = true := by
        unfold muxWinIterT16HiChk; simp only [rkmb_forceList_eq]; rw [← hit]
        simp only [Bool.and_eq_true, rkmw_nat_beq_eq_true, muxIntListEq_eq_true]
        exact ⟨trivial, trivial, trivial⟩
      exact muxWinIterT16HiChk_sound h2
private theorem rkmChS (kT dT : ℕ) {w0 k1 k2 d o0 o1 o2 d1 d2 : ℕ}
    {hb x0 x1 x2 : List ℤ} {b : List ℕ} (h1 : RkmWinIterSound k1 d hb o0 x0 o1 x1 d1)
    (hhb : uHb b = rkmDropInts w0 hb)
    (h2 : bWinChk w0 k2 100000000 d b o1 x1 o2 x2 d2 = true)
    (hk : k1 + k2 = kT) (hd : d1 + d2 = dT) :
    RkmWinIterSound kT d hb o0 x0 o2 x2 dT :=
  rkmChainWinIterT16 hk hd (muxIntListEq_eq_true.mpr rfl) rfl
    (muxIntListEq_eq_true.mpr rfl) h1 (bWinChk_sound hhb h2)
private theorem rkmSegWalk_mk {nSub d offIn offOut dropSeg : ℕ}
    {hb xsIn xsOut : List ℤ} (hhb : hb.length = d)
    (hble : Nat.ble (Nat.add offIn (altIntLen xsIn)) (Nat.add d 1) = true)
    (hiter : RkmWinIterSound nSub d hb offIn xsIn offOut xsOut dropSeg) :
    RkmWinSegWalkSound nSub ⟨d, hb, offIn, xsIn, offOut, xsOut, dropSeg⟩ := by
  simp only [rkmw_nat_ble_eq_true, rkmw_altIntLen_eq, Nat.add_eq] at hble
  obtain ⟨hout, hbd⟩ := hiter hhb hble; exact ⟨hhb, hble, hout, hbd⟩
private def bAllT : List Bool → Bool
  | [] => true
  | false :: _ => false
  | true :: bs => bAllT bs
private theorem bAllT_hd {b : Bool} {bs : List Bool} (h : bAllT (b :: bs) = true) : b = true := by
  cases b with
  | false => exact Bool.noConfusion h
  | true => rfl
private theorem bAllT_tl {b : Bool} {bs : List Bool} (h : bAllT (b :: bs) = true) :
    bAllT bs = true := by
  cases b with
  | false => exact Bool.noConfusion h
  | true => exact h
private def uNatCatN : List (List ℕ) → List ℕ
  | [] => []
  | ns :: nss => ns ++ uNatCatN nss
private def pzig : List ℕ → List ℤ
  | [] => []
  | w :: ws =>
    (match Nat.mod w 2 with
      | 0 => primOfNatForced (Nat.div w 2)
      | _ => primNegSuccForced (Nat.div w 2)) :: pzig ws
private def pzigCat : List (List ℕ) → List ℤ
  | [] => []
  | ws :: wss => pzig ws ++ pzigCat wss
private abbrev tHd := @bAllT_hd
private abbrev tTl := @bAllT_tl
private def rkmPhb_w64_m16_s4b : List ℕ := uNatCatN
  [
   [744941120030274,744755481295136,744565544413493,744371320256024,744172819630534,
    743970053282493,743763031895569,743551766092156,743336266433896,743116543422197,
    742892607498741,742664469045988,742432138387681,742195625789331,741954941458711,
    741710095546338,741461098145948,741207959294972,740950688975000,740689297112243,
    740423793577994,740154188189074,739880490708285,739602710844847,739320858254841,
    739034942541637,738744973256325,738450959898139,738152911914875,737850838703304,
    737544749609588,737234653929679,736920560909725,736602479746469,736280419587637,
    735954389532332,735624398631416,735290455887894,734952570257288,734610750648015,
    734265005921749,733915344893796,733561776333448,733204308964344,732842951464827,
    732477712468291,732108600563528,731735624295078,731358792163561,730978112626021,
    730593594096253,730205244945138,729813073500970,729417088049774,729017296835633,
    728613708061000,728206329887016,727795170433817,727380237780845,726961539967152,
    726539084991697,726112880813654,725682935352701,725249256489311,724811852065052,
    724370729882862,723925897707343,723477363265039,723025134244712,722569218297624,
    722109623037809,721646356042339,721179424851600,720708836969553,720234599863998,
    719756720966837,719275207674328,718790067347345,718301307311631,717808934858047,
    717312957242822,716813381687799,716310215380678,715803465475262,715293139091691,
    714779243316683,714261785203766,713740771773517,713216210013784,712688106879923,
    712156469295017,711621304150108,711082618304413,710540418585549,709994711789747,
    709445504682074,708892803996640,708336616436818,707776948675449,707213807355055,
    706647199088041,706077130456905,705503608014436,704926638283918,704346227759332,
    703762382905547,703175110158522,702584415925498,701990306585190,701392788487978,
    700791867956095,700187551283818,699579844737650,698968754556506,698354286951894,
    697736448108098,697115244182358,696490681305042,695862765579829,695231503083882,
    694596899868019,693958961956886,693317695349128,692673106017557,692025199909319,
    691373982946060,690719461024094,690061640014559,689400525763586,688736124092453,
    688068440797750,687397481651532,686723252401478,686045758771045,685365006459620,
    684681001142677,683993748471924,683303254075453,682609523557892,681912562500549,
    681212376461560,680508970976034,679802351556194,679092523691523,678379492848906,
    677663264472765,676943843985204,676221236786144,675495448253459,674766483743115,
    674034348589302,673299048104567,672560587579950,671818972285111,671074207468462,
    670326298357300,669575250157927,668821068055786,668063757215580,667303322781405],
   [666539769876863,665773103605199,665003329049409,664230451272374,663454475316970,
    662675406206195,661893248943282,661108008511821,660319689875869,659528297980075,
    658733837749786,657936314091166,657135731891305,656332096018335,655525411321540,
    654715682631465,653902914760025,653087112500618,652268280628226,651446423899529,
    650621547053005,649793654809040,648962751870029,648128842920482,647291932627127,
    646452025639010,645609126587598,644763240086880,643914370733466,643062523106684,
    642207701768685,641349911264532,640489156122303,639625440853184,638758769951568,
    637889147895142,637016579144993,636141068145689,635262619325380,634381237095886,
    633496925852790,632609689975526,631719533827473,630826461756040,629930478092758,
    629031587153366,628129793237897,627225100630768,626317513600865,625407036401625,
    624493673271127,623577428432169,622658306092357,621736310444186,620811445665122,
    619883715917684,618953125349525,618019678093514,617083378267813,616144229975959,
    615202237306942,614257404335284,613309735121114,612359233710250,611405904134269,
    610449750410591,609490776542546,608528986519458,607564384316712,606596973895830,
    605626759204548,604653744176885,603677932733214,602699328780340,601717936211567,
    600733758906768,599746800732459,598757065541866,597764557174996,596769279458704,
    595771236206766,594770431219940,593766868286040,592760551180000,591751483663939,
    590739669487233,589725112386575,588707816086040,587687784297155,586665020718959,
    585639529038069,584611312928741,583580376052937,582546722060384,581510354588638,
    580471277263145,579429493697302,578385007492522,577337822238287,576287941512216,
    575235368880118,574180107896057,573122162102407,572061535029913,570998230197747,
    569932251113568,568863601273578,567792284162580,566718303254031,565641662010105,
    564562363881744,563480412308713,562395810719660,561308562532164,560218671152795,
    559126139977167,558030972389990,556933171765124,555832741465632,554729684843835,
    553624005241360,552515705989196,551404790407742,550291261806865,549175123485940,
    548056378733913,546935030829343,545811083040452,544684538625183,543555400831238,
    542423672896137,541289358047260,540152459501898,539012980467303,537870924140732,
    536726293709497,535579092351013,534429323232842,533276989512742,532122094338714,
    530964640849045,529804632172356,528642071427648,527476961724346,526309306162342,
    525139107832045,523966369814420,522791095181037,521613286994108,520432948306538,
    519250082161965,518064691594800,516876779630275,515686349284484,514493403564422,
    513297945468031,512099977984239,510899504093004,509696526765352,508491048963421],
   [507283073640500,506072603741068,504859642200840,503644191946799,502426255897241,
    501205836961814,499982938041555,498757562028933,497529711807880,496299390253841,
    495066600233801,493831344606330,492593626221619,491353447921517,490110812539569,
    488865722901054,487618181823019,486368192114319,485115756575652,483860877999596,
    482603559170644,481343802865240,480081611851817,478816988890828,477549936734785,
    476280458128293,475008555808085,473734232503056,472457490934296,471178333815128,
    469896763851139,468612783740215,467326396172574,466037603830800,464746409389876,
    463452815517216,462156824872701,460858440108707,459557663870142,458254498794475,
    456948947511771,455641012644718,454330696808665,453018002611650,451702932654432,
    450385489530520,449065675826208,447743494120605,446418946985662,445092036986206,
    443762766679970,442431138617622,441097155342795,439760819392119,438422133295247,
    437081099574888,435737720746832,434391999319985,433043937796392,431693538671271,
    430340804433038,428985737563335,427628340537064,426268615822408,424906565880863,
    423542193167265,422175500129819,420806489210122,419435162843198,418061523457518,
    416685573475031,415307315311189,413926751374977,412543884068935,411158715789188,
    409771248925472,408381485861158,406989428973280,405595080632560,404198443203437,
    402799519044087,401398310506451,399994819936264,398589049673073,397181002050270,
    395770679395110,394358084028741,392943218266225,391526084416564,390106684782727,
    388685021661669,387261097344360,385834914115805,384406474255072,382975780035312,
    381542833723786,380107637581885,378670193865157,377230504823328,375788572700324,
    374344399734299,372897988157651,371449340197052,369998458073464,368545344002167,
    367090000192776,365632428849270,364172632170008,362710612347755,361246371569701,
    359779912017485,358311235867218,356840345289499,355367242449445,353891929506702,
    352414408615477,350934681924551,349452751577304,347968619711736,346482288460485,
    344993759950851,343503036304816,342010119639061,340515012064992,339017715688756,
    337518232611263,336016564928206,334512714730081,333006684102207,331498475124744,
    329988089872715,328475530416026,326960798819482,325443897142811,323924827440678,
    322403591762711,320880192153513,319354630652685,317826909294846,316297030109648,
    314764995121796,313230806351070,311694465812338,310155975515581,308615337465903,
    307072553663557,305527626103958,303980556777706,302431347670599,300880000763652,
    299326518033118,297770901450502,296213152982581,294653274591420,293091268234390,
    291527135864186,289960879428843,288392500871754,286822002131689,285249385142806],
   [283674651834676,282097804132294,280518843956097,278937773221983,277354593841324,
    275769307720985,274181916763342,272592422866293,271000827923280,269407133823301,
    267811342450929,266213455686326,264613475405261,263011403479123,261407241774942,
    259800992155397,258192656478839,256582236599303,254969734366524,253355151625951,
    251738490218767,250119751981899,248498938748036,246876052345643,245251094598978,
    243624067328104,241994972348908,240363811473110,238730586508285,237095299257871,
    235457951521188,233818545093451,232177081765785,230533563325238,228887991554798,
    227240368233405,225590695135966,223938974033370,222285206692500,220629394876249,
    218971540343534,217311644849309,215649710144578,213985737976411,212319730087957,
    210651688218456,208981614103255,207309509473819,205635376057746,203959215578782,
    202281029756831,200600820307969,198918588944461,197234337374768,195548067303565,
    193859780431752,192169478456467,190477163071099,188782835965301,187086498825005,
    185388153332429,183687801166095,181985444000841,180281083507831,178574721354568,
    176866359204909,175155998719075,173443641553666,171729289361667,170012943792469,
    168294606491875,166574279102112,164851963261849,163127660606201,161401372766748,
    159673101371540,157942848045117,156210614408512,154476402079271,152740212671458,
    151002047795671,149261909059052,147519798065296,145775716414668,144029665704011,
    142281647526756,140531663472936,138779715129198,137025804078810,135269931901675,
    133512100174344,131752310470024,129990564358589,128226863406592,126461209177278,
    124693603230589,122924047123183,121152542408436,119379090636461,117603693354112,
    115826352104998,114047068429494,112265843864750,110482679944701,108697578200081,
    106910540158429,105121567344100,103330661278280,101537823478991,99743055461103,97946358736344,
    96147734813311,94347185197480,92544711391215,90740314893779,88933997201342,87125759806995,
    85315604200755,83503531869579,81689544297371,79873642964993,78055829350274,76236104928021,
    74414471170028,72590929545084,70765481518985,68938128554541,67108872111589,65277713646998,
    63444654614684,61609696465612,59772840647812,57934088606385,56093441783513,54250901618466,
    52406469547617,50560147004444,48711935419544,46861836220640,45009850832590,43155980677396,
    41300227174216,39442591739366,37583075786337,35721680725796,33858407965602,31993258910809,
    30126234963679,28257337523686,26386567987530,24513927749141,22639418199690,20763040727599,
    18884796718544,17004687555469,15122714618592,13238879285414,11353182930727,9465626926621,
    7576212642495],
   [5684941445065,3791814698368,1896833763776]]
private def rkmPhb_w64_m16_s5a : List ℕ := uNatCatN
  [
   [717825524980978,717401334415663,716974358826651,716544599659927,716112058332471,
    715676736232235,715238634718104,714797755119860,714354098738148,713907666844434,
    713458460680963,713006481460720,712551730367380,712094208555265,711633917149292,
    711170857244924,710705029908117,710236436175267,709765077053150,709290953518866,
    708814066519776,708334416973444,707852005767568,707366833759913,706878901778248,
    706388210620268,705894761053529,705398553815365,704899589612817,704397869122552,
    703893392990782,703386161833181,702876176234798,702363436749971,701847943902239,
    701329698184243,700808700057641,700284949953005,699758448269724,699229195375904,
    698697191608261,698162437272022,697624932640810,697084677956538,696541673429294,
    695995919237226,695447415526427,694896162410811,694342159971992,693785408259160,
    693225907288952,692663657045323,692098657479411,691530908509406,690960410020405,
    690387161864281,689811163859529,689232415791129,688650917410392,688066668434811,
    687479668547904,686889917399059,686297414603375,685702159741497,685104152359448,
    684503391968467,683899878044831,683293610029682,682684587328852,682072809312677,
    681458275315816,680840984637065,680220936539164,679598130248604,678972564955430,
    678344239813042,677713153937990,677079306409768,676442696270602,675803322525238,
    675161184140725,674516280046189,673868609132616,673218170252618,672564962220202,
    671908983810538,671250233759713,670588710764495,669924413482079,669257340529840,
    668587490485077,667914861884753,667239453225230,666561262962007,665880289509441,
    665196531240478,664509986486367,663820653536377,663128530637510,662433615994205,
    661735907768039,661035404077427,660332102997312,659626002558851,658917100749103,
    658205395510703,657490884741533,656773566294396,656053437976672,655330497549979,
    654604742729825,653876171185255,653144780538490,652410568364565,651673532190960,
    650933669497222,650190977714586,649445454225586,648697096363665,647945901412773,
    647191866606962,646434989129977,645675266114837,644912694643410,644147271745984,
    643378994400828,642607859533750,641833864017645,641057004672037,640277278262615,
    639494681500761,638709211043071,637920863490867,637129635389704,636335523228871,
    635538523440875,634738632400929,633935846426426,633130161776402,632321574650999,
    631510081190912,630695677476829,629878359528867,629058123305992,628234964705438,
    627408879562108,626579863647972,625747912671455,624913022276811,624075188043494,
    623234405485513,622390670050778,621543977120442,620694322008220,619841699959710,
    618986106151697,618127535691445,617265983615981,616401444891364,615533914411947],
   [614663386999622,613789857403058,612913320296920,612033770281084,611151201879831,
    610265609541033,609376987635327,608485330455267,607590632214473,606692887046762,
    605792089005257,604888232061498,603981310104521,603071316939932,602158246288964,
    601242091787516,600322846985180,599400505344245,598475060238692,597546504953168,
    596614832681941,595680036527845,594742109501196,593801044518700,592856834402337,
    591909471878224,590958949575467,590005260024984,589048395658311,588088348806392,
    587125111698341,586158676460185,585189035113589,584216179574554,583240101652091,
    582260793046879,581278245349893,580292450041007,579303398487578,578311081943002,
    577315491545239,576316618315324,575314453155836,574308986849352,573300210056867,
    572288113316184,571272687040283,570253921515647,569231806900571,568206333223430,
    567177490380919,566145268136262,565109656117384,564070643815051,563028220580974,
    561982375625882,560933098017549,559880376678795,558824200385440,557764557764226,
    556701437290690,555634827287011,554564715919796,553491091197843,552413940969845,
    551333252922058,550249014575921,549161213285626,548069836235649,546974870438218,
    545876302730747,544774119773204,543668308045436,542558853844437,541445743281559,
    540328962279669,539208496570247,538084331690425,536956452979963,535824845578168,
    534689494420742,533550384236569,532407499544437,531260824649681,530110343640769,
    528956040385805,527797898528964,526635901486844,525470032444748,524300274352883,
    523126609922470,521949021621779,520767491672072,519582002043459,518392534450660,
    517199070348677,516001590928366,514800077111912,513594509548201,512384868608091,
    511171134379569,509953286662803,508731304965082,507505168495632,506274856160321,
    505040346556236,503801617966130,502558648352749,501311415353014,500059896272072,
    498804068077203,497543907391579,496279390487879,495010493281742,493737191325064,
    492459459799133,491177273507590,489890606869225,488599433910581,487303728258387,
    486003463131788,484698611334393,483389145246106,482075036814759,480756257547529,
    479432778502126,478104570277763,476771603005881,475433846340638,474091269449139,
    472743841001415,471391529160127,470034301569998,468672125346958,467304967066994,
    465932792754694,464555567871480,463173257303510,461785825349244,460393235706668,
    458995451460151,457592435066931,456184148343218,454770552449897,453351607877814,
    451927274432641,450497511219296,449062276625900,447621528307261,446175223167874,
    444723317344393,443265766187590,441802524243758,440333545235543,438858782042187,
    437378186679162,435891710277157,434399303060419,432900914324390,431396492412650],
   [429885984693098,428369337533382,426846496275518,425317405209673,423782007547093,
    422240245392119,420692059713265,419137390313330,417576175798474,416008353546251,
    414433859672526,412852628997244,411264595008997,409669689828338,408067844169787,
    406458987302474,404843047009351,403219949544924,401589619591423,399951980213349,
    398306952810318,396654457068133,394994410907984,393326730433715,391651329877039,
    389968121540621,388277015738922,386577920736693,384870742685011,383155385554723,
    381431751067184,379699738622147,377959245222655,376210165396788,374452391116109,
    372685811710618,370910313780049,369125781101312,367332094531861,365529131908787,
    363716767943381,361894874110940,360063318535528,358221965869426,356370677166956,
    354509309752365,352637717081413,350755748596308,348863249573585,346960060964500,
    345046019227502,343120956152280,341184698674868,339237068683257,337277882812887,
    335306952231400,333324082411927,331329072894179,329321717032517,327301801730123,
    325269107158333,323223406460103,321164465436498,319092042214999,317005886898335,
    314905741192408,312791338011785,310662401061077,308518644390378,306359771922779,
    304185476951777,301995441606209,299789336280112,297566819024647,295327534898974,
    293071115276630,290797177103632,288505322104133,286195135929032,283866187242456,
    281518026740474,279150186095810,276762176821614,274353489046585,271923590192832,
    269471923546880,266997906713086,264500929937392,261980354287927,259435509677187,
    256865692708644,254270164328341,251648147259458,248998823194817,246321329718854,
    243614756926474,240878143701519,238110473612025,235310670372914,232477592819083,
    229610029322772,226706691578216,223766207663733,220787114275844,217767848011414,
    214706735551208,211601982570821,208451661171369,205253695581116,202005845828166,
    198705689020949,195350597793716,191937715374060,188463926602120,184925824068014,
    181319668323357,177641340848093,173886288092327,170049454431923,166125201229537,
    162107208311199,157988352951503,153760559755203,149414612395204,144939914648452,
    140324182971264,135553045000879,130609506211139,125473227601428,120119525523793,
    114517950653104,108630207037182,102406992908535,95782990012395,88668472556053,80934244623273,
    72381987847174,62677810015780,51170580129421,36179035075236]]
private theorem rkmStatOk_hi64t05 : bAllT [
  muxIntListEq (uHb rkmPhb_w64_m16_s4b) (altBuildHbFrom 1024 1024 29638027559 381 643),
  muxIntListEq (uHb rkmPhb_w64_m16_s5a) (altBuildHbFrom 1856 1024 19586394833 564 460)
  ] = true := by decide +kernel
private theorem rkmHhb_w64_m16_s4b :
    uHb rkmPhb_w64_m16_s4b = rkmDropInts 381 rkmHbWin_w64_m16_s4b :=
  (muxIntListEq_eq_true.mp (tHd rkmStatOk_hi64t05)).trans
    (drHb 1024 1024 29638027559 381 1024)
private theorem rkmHhb_w64_m16_s5a :
    uHb rkmPhb_w64_m16_s5a = rkmDropInts 564 rkmHbWin_w64_m16_s5a :=
  (muxIntListEq_eq_true.mp (tHd (tTl rkmStatOk_hi64t05))).trans
    (drHb 1856 1024 19586394833 564 1024)
private def rkmC_w64_m16_s4b_1 : List ℤ := pzigCat
  [
   [421722625,922991673,1838599729,3262006127,4679333219,5991863299,5906676411,2621886991,
    7353222292,29977872316,74189492752,153918114758,288877283498,507322211666,847238362458,
    1359252800404,2108646459552,3177205067992,4665323364112,6692872083998,9398992931174,
    12941816208766,17494931328380,23243793004910,30379519660180,39090996044588,49556350487928,
    61931086185806,76337980553912,92854462586366,111501417781996,132234394134982,154934197804372,
    179403048413162,205362176912154,232454067316914,260249404949220,288256569202348,
    315936849135364,342721109293334,368030131516090,391295572856626,411981876731308,
    429607147147724,443761458346182,454122717335958,460469136959562,462685636542656,
    460767614169004,454818283182328,445042104376998,431734684876994,415267664588416,
    396073791810364,374628027399264,351429474682622,326984119500544,301786747795318,
    276307299263046,250977848182984,226183224992056,202254066717230,179462873381550,
    158023011924184,138089778014160,119763307692738,103093954894952,88087104102596,74711094180490,
    62903606577922,52577984442904,43630913983446,35947157748544,29406043720722,23885397281166,
    19264961047040,15429886938588,12272625957322,9694059788574,7604878244968,5925039848464,
    4585004575788,3524128706754,2690289416040,2040106442450,1536610471162,1149594540574,
    854230417954,630372277692,461961738026,336067352934,242594735940,173905208222,123391673494,
    86766888316,60389115144,41355010344,27932694358,18368415296,11755535810,7116353524,3910717270,
    1935742872,698927444]]
private def rkmC_w64_m16_s4b_2 : List ℤ := pzigCat
  [
   [232321682,296264640,67546730,569784949,1764578715,3826317073,6758520701,10666416393,
    14850570855,17861045395,16797089113,5877648695,23728312436,86830669734,204991189812,
    408846380032,741514974518,1259958935050,2038888484896,3172010145926,4774397274278,
    6983277304662,9957244800786,13875038008288,18931742234588,25332449557772,33285358515716,
    42991442906338,54633649695518,68364133651582,84291115401056,102466623734070,122873594324072,
    145417707165752,169919430173192,196111239780912,223639247006494,252068158397512,
    280891966952444,309549023698536,337439656307970,363948743174758,388467864979422,
    410419250600258,429279178028024,444597951190324,456018935620320,463290678360630,
    466276333674598,464957032389372,459429624245668,449900320842688,436672998868260,
    420133909715998,400735403810042,378975207005636,355377179451844,330472052352126,
    304779064259308,278790942977678,252959256988474,227685610198824,203313921872196,
    180126030143526,158341399500280,138118207479746,119556576063864,102704721017200,
    87564363013728,74098751740110,62239387966438,51893543645324,42951850219648,35293103204884,
    28791264604588,23319427781454,18753366402124,14974947322522,11873975115902,9349465115130,
    7310766162352,5677067851680,4378349980408,3353698699034,2551239305952,1927697703316,
    1446681252554,1078147717918,798153133826,586625481252,428131390588,310212528836,222889495814,
    158964741870,112324651554,78588242572,54299173526,36923519870,24716026406,16095354216,
    9955213548,5934823256,3121167040,1379558312,451515660]]
private def rkmC_w64_m16_s4b_3 : List ℤ := pzigCat
  [
   [365337590,555329248,865302666,885591554,597410960,315679391,2507458795,6465981935,12792670425,
    21643597195,32210216117,42747974355,48457182015,40882124647,5750512571,79849214010,
    248852454076,548894839978,1044182747956,1819159862746,2981343546392,4662711011468,
    7020824441282,10237749593818,14516865079384,20078534622850,27151608770938,35964303954046,
    46731673981114,59641297910788,74840233648220,92418435011028,112395435043296,134708161228642,
    159201952079472,185625560788564,213630306575746,242775321326658,272538178384846,
    302328896667556,331511096151562,359424314328446,385409764664712,408837253064470,
    429130657920120,445791548783178,458419716947288,466728135028860,470554036368294,
    469862143033602,464743568120654,455409164196860,442175462028258,425450094877250,
    405711489090744,383487564478714,359334645451556,333815762522706,307481061146536,
    280851006863566,254401368431556,228553367470654,203665329216714,180029290320272,
    157870133320396,137347194966246,118558858303058,101548460266552,86310803138308,72801382002558,
    60942901443360,50633821791172,41756111039384,34181018593222,27775195518566,22405962994788,
    17944019420196,14267729006068,11263885651524,8829386898144,6872442172472,5311868011406,
    4076968994762,3107656767120,2352280093938,1768245433946,1320117709260,978602199558,
    720366233518,526563580456,381925746038,275108930088,196511243146,139123345584,97639619674,
    67684910492,46280622536,31249132630,20458014382,13070887488,7910390868,4320022722,2092273594,
    727490128]]
private def rkmC_w64_m16_s4b_4 : List ℤ := pzigCat
  [
   [643216532,1288398856,1938946720,2484542582,2404766278,884521168,2581854321,9475922483,
    21153193135,37918995269,59586859521,83172033851,102415687057,104479141709,67764407899,
    40963788496,271087454896,691216568608,1392908188772,2494951336578,4143839907250,6515762179034,
    9814997533230,14269759066364,20125974146830,27637914323008,37055902009876,48612166542650,
    62503755671890,78876485290872,97807003271490,119288008473330,143216015871808,169382312288048,
    197469913606228,227056240663364,257620442783076,288559537115916,319207258308990,
    348858990959580,376800258068380,402335297947360,424816609133078,443673312906270,
    458433741176910,468745941496846,474390006003202,475284886348534,471488836063374,
    463192045285466,450704443796524,434439416575946,414891303771948,392613728272820,
    368194985065510,342234340132812,315320784250858,288013106526092,260823761720140,
    234207687332544,208552193463842,184173599660780,161315776591690,140151765502758,
    120789052895028,103275594106200,87607099573794,73736939834248,61583382571768,51039110121292,
    41979095381724,34267150366870,27762812998754,22326388695528,17822127564700,14122687813780,
    11109910820646,8676720485810,6727966393760,5179732626110,3959413351676,3005381308092,
    2264999589182,1695033421564,1259604758178,929312177486,680775197630,495116505554,357251162992,
    255902512086,181710576022,127872538602,89171972516,61385347390,41626768496,27731704714,
    17895175742,11031128190,6605820008,3444291608,1481246250,464970934]]
private def rkmC_w64_m16_s4b_5 : List ℤ := pzigCat
  [
   [387635982,1469330628,2730076866,4396596852,5916198366,6304288460,4517402762,1478305137,
    14141425981,35471020471,67591131871,109926240915,158424380343,202713349849,222415070009,
    183788131369,34717090879,300392576458,923855260812,1970215888530,3607495105656,6037826721494,
    9496077457988,14243902842018,20561199834458,28734460291678,39040105180126,51728020115016,
    67000790834674,84993710897544,105756517851670,129236205946470,155264825084004,183553562062714,
    213691243629046,245152690965782,277312041456394,309463563918320,340849103082934,
    370688334841380,398211978047302,422696461314040,443494565994338,460064948275524,
    471994458645506,479013998305252,481008015321390,478015009636712,470220596210210,
    457945135571054,441623419497692,421782394539198,399015241234202,373953731720546,
    347242893164890,319515732724894,291372035524124,263360686483530,235966283474154,
    209599470463776,184593334695070,161201452293424,139601034828034,119898592142926,
    102136612226368,86302842407800,72340415813200,60156038148040,49630862935942,40628489832510,
    33002065773192,26601911508252,21280110090104,16894631749144,13312550714400,10412179817230,
    8083489585908,6229744035852,4766094488570,3619733490616,2729391194544,2043273973910,
    1518397998476,1120328206904,820527994356,596492716544,430442315476,308162949656,218846760152,
    154091803958,107359052570,73894725258,50340658608,33518456954,21794728310,13774859592,
    8195159324,4489860006,2202189522,752174830]]
private def rkmC_w64_m16_s4b_6 : List ℤ := pzigCat
  [
   [256498241,435302131,617291233,331896997,680518302,2332137278,5138185094,8578816908,
    12023151782,14006461230,11891652516,2563280506,18104353873,54701532483,110062745531,
    184475726829,271864888073,355871584099,405884086533,370198922925,171520719295,299541939366,
    1189237480652,2683598908874,5008940683766,8429782399756,13241442454250,19760083566308,
    28307324061692,39191226113034,52685128275464,69004085741380,88280901050550,110545793066548,
    135707560908876,163541869464620,193686795405968,225644315739724,258793340796690,
    292408939673258,325689499715712,357790269887626,387860600492204,415081577434670,
    438704973443424,458086703799798,472715287955790,482233987076098,486453267012054,
    485354437987320,479085944435342,467949111962066,452379152180212,432920192725728,
    410195688604360,384879613985032,357665819009212,329239986414366,300255389715070,
    271312579688646,242942584698332,215597456962968,189643969700870,165362097085470,
    142948447680504,122521223614496,104129113517248,87760949789712,73356056142306,60814829270322,
    50010228562442,40795853910470,33014912369998,26507954840588,21117421546810,16692818476006,
    13093995241770,10192864480394,7874336905066,6037664590986,4594773315982,3470558275020,
    2602096963366,1936500734340,1430426226596,1048822975604,763321240580,551161691228,
    395052779490,280838106608,197839733246,138156559670,95423085688,65003429016,43658866484,
    28754373644,18317201434,11193616136,6605782684,3331277784,1362959026,403762650]]
private def rkmC_w64_m16_s4b_7 : List ℤ := pzigCat
  [
   [254349764,12351916,430482253,1109439299,1765244399,1785589965,1084312279,986763968,4879399714,
    10580417692,17849078682,25219815118,29362611200,25894420144,8223073024,31522461399,
    100260189549,203172683067,338598457029,493901990665,639411738927,720812716177,651896562775,
    307809246579,481468716440,1934072608408,4316227336806,7938892891356,13146813387780,
    20304930071696,29778250624582,41907247013016,56981018136198,75209455736848,96695347042624,
    121411404436856,149182949286854,179677259067812,212404495844988,246726685253754,
    281878332988870,316996074205790,351155358260556,383412557330292,412850799471618,
    438623200845946,459993083233618,476369727732642,487332805129836,492648932372078,
    492277435588442,486365096040280,475231342551800,459346536951606,439302178417884,
    415778534850892,389510883133286,361254401654452,331753217864600,301713213683710,
    271778198687354,242514001317662,214396876433354,187808055494500,163032901328454,
    140265626536832,119615855840954,101118644340532,84746712164190,70421233898388,58024509897144,
    47411591850026,38420198643874,30879216966712,24617410879580,19467949901372,15272914291552,
    11887294189998,9179786388246,7033708691340,5347703472900,4034589126460,3020606444530,
    2244141844964,1654728966524,1210673814834,878966366554,633365400638,452686998086,320800485448,
    225456365108,156957312294,108039308076,73462203924,49318040366,32277161142,20640641536,
    12780028142,7373747148,3860808314,1775944258,566517460]]
private def rkmC_w64_m16_s4b_8 : List ℤ := pzigCat
  [
   [261348610,374214212,472505340,355861614,258259607,1136720347,2265139157,3539682865,4291520713,
    3589632957,584104687,6070348384,16543436464,30410053622,45410002778,56429549016,55749269814,
    32730230420,25776013573,132152489023,294704877351,512889481347,768911994285,1019209207689,
    1186034468349,1146298507917,724813577511,311589182464,2255428824414,5453781360280,
    10297981527150,17206309820292,26599956011608,38873258936148,54361965353460,73307983933760,
    95827463004282,121883507543416,151265848899478,183580775903846,218253898516968,
    254544039353160,291569852938028,328348298688684,363839580556868,396998131342376,
    426826525734556,452424287758002,473033544068388,488075138925030,497173228483822,
    500167741733452,497115262917114,488276825845072,474095191145394,455165234535398,
    432197117001622,405976521833928,377326395777566,347068514729748,315990601092636,
    284818551756692,254195308072340,224665941897212,196670598647568,170542807699768,
    146512198704718,124713393432188,105196792381828,87940460596512,72864531831742,59845271500024,
    48727004055120,39334681173524,31483626653440,24988252395114,19667958569252,15352813720446,
    11886687193020,9128412800660,6953671911524,5254848707116,3939519521866,2929948757216,
    2162015698812,1582857335382,1149688414358,828267438170,592082039874,419731886838,294838306630,
    205307385304,141554469522,96351193528,64695253158,42804790254,27673246782,17260120264,
    10308353528,5814050378,2863223140,927937182,205259544]]
private theorem rkmWC_w64_m16_s4b_0 : bWinChk 381 16 100000000 1024 rkmPhb_w64_m16_s4b
    397 rkmXsWin_w64_m16_s4b_in 421 rkmC_w64_m16_s4b_1 3402297123 = true := by decide +kernel
private theorem rkmWC_w64_m16_s4b_1 : bWinChk 381 15 100000000 1024 rkmPhb_w64_m16_s4b
    421 rkmC_w64_m16_s4b_1 441 rkmC_w64_m16_s4b_2 2950638732 = true := by decide +kernel
private theorem rkmWC_w64_m16_s4b_2 : bWinChk 381 16 100000000 1024 rkmPhb_w64_m16_s4b
    441 rkmC_w64_m16_s4b_2 463 rkmC_w64_m16_s4b_3 2930375118 = true := by decide +kernel
private theorem rkmWC_w64_m16_s4b_3 : bWinChk 381 15 100000000 1024 rkmPhb_w64_m16_s4b
    463 rkmC_w64_m16_s4b_3 485 rkmC_w64_m16_s4b_4 2876458246 = true := by decide +kernel
private theorem rkmWC_w64_m16_s4b_4 : bWinChk 381 16 100000000 1024 rkmPhb_w64_m16_s4b
    485 rkmC_w64_m16_s4b_4 507 rkmC_w64_m16_s4b_5 3247850169 = true := by decide +kernel
private theorem rkmWC_w64_m16_s4b_5 : bWinChk 381 15 100000000 1024 rkmPhb_w64_m16_s4b
    507 rkmC_w64_m16_s4b_5 524 rkmC_w64_m16_s4b_6 3067642032 = true := by decide +kernel
private theorem rkmWC_w64_m16_s4b_6 : bWinChk 381 16 100000000 1024 rkmPhb_w64_m16_s4b
    524 rkmC_w64_m16_s4b_6 543 rkmC_w64_m16_s4b_7 3051511419 = true := by decide +kernel
private theorem rkmWC_w64_m16_s4b_7 : bWinChk 381 16 100000000 1024 rkmPhb_w64_m16_s4b
    543 rkmC_w64_m16_s4b_7 561 rkmC_w64_m16_s4b_8 2948493618 = true := by decide +kernel
private theorem rkmWC_w64_m16_s4b_8 : bWinChk 381 15 100000000 1024 rkmPhb_w64_m16_s4b
    561 rkmC_w64_m16_s4b_8 580 rkmXsWin_w64_m16_s4b_out 2686029240 = true := by decide +kernel
/-- Certified `w64_m16_s4b` partial walk (`140` substeps). -/
theorem rkmWinIterSnd_w64_m16_s4b :
    RkmWinIterSound 140 1024 rkmHbWin_w64_m16_s4b 397 rkmXsWin_w64_m16_s4b_in
      580 rkmXsWin_w64_m16_s4b_out 27161295697 :=
  rkmChS 140 27161295697 (rkmChS 125 24475266457 (rkmChS 109 21526772839 (rkmChS 93 18475261420
    (rkmChS 78 15407619388 (rkmChS 62 12159769219 (rkmChS 47 9283310973 (rkmChS 31 6352935855
    (bWinChk_sound rkmHhb_w64_m16_s4b rkmWC_w64_m16_s4b_0) rkmHhb_w64_m16_s4b
    rkmWC_w64_m16_s4b_1 rfl rfl) rkmHhb_w64_m16_s4b rkmWC_w64_m16_s4b_2 rfl rfl)
    rkmHhb_w64_m16_s4b rkmWC_w64_m16_s4b_3 rfl rfl) rkmHhb_w64_m16_s4b rkmWC_w64_m16_s4b_4 rfl
    rfl) rkmHhb_w64_m16_s4b rkmWC_w64_m16_s4b_5 rfl rfl) rkmHhb_w64_m16_s4b rkmWC_w64_m16_s4b_6
    rfl rfl) rkmHhb_w64_m16_s4b rkmWC_w64_m16_s4b_7 rfl rfl) rkmHhb_w64_m16_s4b
    rkmWC_w64_m16_s4b_8 rfl rfl
private def rkmC_w64_m16_s5a_1 : List ℤ := pzigCat
  [
   [423750936,1266966934,2100724386,2543908596,2283803410,515238868,2968250773,8076263051,
    13906783647,18779307755,19574893965,12655205585,5307433656,37025479786,81677358840,
    133226923934,179388117062,199699779312,166247962844,46688323778,190215405529,566626792849,
    1082899985033,1703555028785,2342008505497,2846126541395,2985375771639,2445037910237,
    826936286885,2341408141786,7585152089020,15452207242250,26474923253788,41124208251186,
    59761963537896,82595890530164,109640281440940,140687420956452,175293488917768,212782319499244,
    252264846335782,292676335090470,332827976758650,371469301327496,407354766779898,
    439312903066632,466310146663406,487503763590190,502283590498722,510297503120146,
    511459521447404,505942216575936,494154355778898,476706556166254,454367812506996,
    428016889676714,398593519483962,367050253157456,334309257966226,301226332621288,
    268564015487106,236971105528278,206972218096692,178966039811894,153228278848786,
    129921675303674,109108422142774,90766667425464,74806965834374,61087929934184,49432639412982,
    39643076516090,31510716425198,24827296772904,19391772672016,15016253969206,11529315171370,
    8777429568242,6626376901070,4961185119010,3683759918626,2712845155592,1981523293060,
    1435444198286,1031386099478,734939765116,519075985860,363526587128,252183587818,173214830678,
    117727911874,78873989042,51953284604,33601989074,21013627626,12761553818,7333999444,
    3819455108,1770727218,595600228]]
private def rkmC_w64_m16_s5a_2 : List ℤ := pzigCat
  [
   [429083233,582998229,276748007,559728276,2094705462,3942084006,5437179132,5657727134,
    3657564164,1712609299,10862082207,22352640135,33566081203,40261993731,35770505697,13461197001,
    31842065666,101468715742,189558399612,279749009580,343866076504,342255746968,226370841850,
    53181394911,535788319283,1234554148185,2118855031657,3094251672899,3983946219113,
    4516172684387,4317531888851,2915790177779,242933479576,5766787845270,14277938422446,
    26363694433818,42521559724878,63103782665574,88267926919920,117937006696962,151773319683830,
    189173996752458,229284382543486,271031871298524,313178206737306,354385433017874,
    393290681892202,428583426308108,459078373299524,483781816375726,501941174507980,
    513078404872456,517005984372320,513822693756080,503892320279774,487809240448600,
    466351689876118,440430633387228,411034391134028,379175348951388,345842640369588,
    311960855845050,278357590606470,245742130072736,214691551192852,185647543919678,
    158919779280052,134694851096594,113051173173826,93975150261874,77379156502926,63119515686492,
    51013657328214,40854480776726,32424565662458,25505562057468,19886595241422,15370767305340,
    11778191411098,8948166979710,6740898097642,5035524053004,3730181477602,2740382705550,
    1996538558818,1442578557358,1033707141972,734485560136,517363307438,361385136984,249856152084,
    170951137244,115712643798,77173104030,50642080570,32704548490,20479448984,12465774030,
    7139856040,3672536292,1664343728,544330304]]
private def rkmC_w64_m16_s5a_3 : List ℤ := pzigCat
  [
   [414733739,1165938209,1789750295,1801923121,917579709,1148021482,4677534762,8433858602,
    11322014908,11689214938,7081473384,4109262897,21824715967,43880954833,64671083673,75768801409,
    65669426811,23131429667,59264080594,181804507036,331873794616,479517072306,577259199910,
    561147327972,357979541424,101994241947,867281443451,1941494079497,3260094710041,4665786792687,
    5889348991229,6539722010435,6106215646725,3973918481911,543640655326,8158701190432,
    19551424419906,35305399929070,55843113830154,81366792490846,111811195467010,146816919794526,
    185723417126822,227586872165312,271222451731712,315264582093826,358245047891360,
    398678537096810,435149852637096,466396141149646,491377722108068,509329907648094,
    519796936970548,522643130954712,518042787971066,506452549558698,488568005637898,
    465269172422638,437562357141342,406518529673350,373216537193480,338693187617358,
    303900480348188,269675543838794,236720376391792,205591525135024,176699358760078,
    150316083842780,126587546747012,105550937003274,87153665448058,71272614393994,57734217061892,
    46331162004026,36837768560588,29023041858036,22660782056040,17535824221858,13450624785596,
    10227488250120,7709534988094,5761808982168,4269664581056,3137212085428,2285745507796,
    1651640036648,1183256492566,840515891074,591957268216,413035321322,285488382946,195406428978,
    132198490202,88270421942,58257680186,37620239684,23773235648,14609152956,8448264790,
    4490769202,2129925220,705912150]]
private def rkmC_w64_m16_s5a_4 : List ℤ := pzigCat
  [
   [298439932,763505548,665338260,168040036,747652871,2346779501,3730059203,4365777725,3153884131,
    438652792,6340071648,13811451712,20659826762,23171397674,17864552044,1425833714,27381694653,
    65392713585,104347746067,130669849895,126204137337,72638600061,44036171688,226675947670,
    458568872936,699455615042,882051517152,915323640654,694855315916,120401940910,879241741603,
    2315701283107,4110121089187,6063975686319,7837476219263,8942874800023,8751634947819,
    6522395835459,1447381975947,7285479654912,20419135869000,38548722065166,62048149506726,
    91007950886822,125191856264818,164020256274842,206579485972762,251661208701806,
    297826544586826,343489583235416,387013791687944,426813793589246,461450360951036,
    489713968723916,510691031181634,523804482128088,528831700196498,525897388082132,
    515444126659092,498185331585238,475046743028132,447098951964062,415490144229470,
    381382413663440,345893548386728,310051450168026,274759231982188,240772305813080,
    208687588713872,178943866742970,151828679971644,127493725748908,105973938114122,
    87207736451238,71059712811614,57341520900442,45830091554610,36284834472240,28460728290334,
    22118951436118,17034184115316,13000755329450,9834348246130,7373604223412,5480560116026,
    4038385748292,2950021046598,2136596420486,1534283525290,1092212040796,770562032740,
    538974189760,373394569988,256111331370,173991571478,116792950954,77280197890,50433063528,
    32317236024,20073295914,11969283696,6851186298,3341563792,1320993184,378862804]]
private def rkmC_w64_m16_s5a_5 : List ℤ := pzigCat
  [
   [252811162,907801700,1600411748,1850747812,1178304992,529771039,3080943137,6230429065,
    8264696881,7775692617,3427491807,5631347412,18361146190,31641335680,40395426462,38053515390,
    18392942696,21455234187,79457569381,145056494435,199199677515,215867219991,165827380097,
    24747909383,216795331908,543815091302,907855800064,1222050707480,1366304727194,1198819513732,
    579230544042,598702891789,2368984377683,4653539046745,7226155127551,9689042643939,
    11465590192577,11814107774595,9866984081575,4691134302193,4634043869552,18925007917766,
    38803405817082,64612030184962,96349080453924,133629091912832,175675854999340,221348451687148,
    269200006449680,317563942467540,364658149809168,408699654921322,448019102387378,
    481162168935920,506974617088516,524660795022940,533814105067138,534418862356040,
    526826320612974,511707452671804,489989713864516,462785132483938,431313187085162,
    396826846919362,360547887465130,323610489348918,287019745784656,251623824095532,
    218099656431496,186949534331308,158509642381218,132965587265696,110371704641206,
    90675261664778,73740720185216,59371865400624,47333988727760,37371980026958,29225278401278,
    22639064159618,17374011982792,13210990994302,9954019006716,7432554888234,5500464908526,
    4034512268108,2933159333004,2113839438542,1509964951264,1069024658542,750031918828,
    521557520498,359059956744,244739789040,165225678572,110154808296,72356561290,46834789906,
    29693755882,18175623154,10621363138,5858762570,2846027220,920961802,204418952]]
private def rkmC_w64_m16_s5a_6 : List ℤ := pzigCat
  [
   [378655921,628371425,232938793,486748716,1899259938,3324469408,3920780014,3052720384,97154107,
    5245230519,11066278183,15549176111,15605106301,8390880157,7213979724,29376944620,53277190110,
    69728968928,67835432792,37526537398,26760558209,120803923645,227658514389,316921108265,
    347154819675,273781091365,61122731673,302791015680,791992453684,1330011091838,1787913088064,
    1991758887466,1743481038782,856742434988,797448454365,3239726647493,6332236105841,
    9739265219367,12907236396785,15069568779383,15279821145795,12477127970737,5573879312991,
    6438708462722,24378110003116,48765982380280,79743279940358,117014594532270,159830243618330,
    207010643100016,257008414199884,308004512675052,358029741846962,405097518039952,
    447335706294510,483108829898346,511115143148722,530455497767686,540669033873358,
    541734590512488,534041013454978,518332243787394,495634669970474,467172404804822,
    434280384113514,398322080058754,360615400997564,322372160035730,284654925740364,
    248347416803222,214141745428848,182538828816046,153859851248976,128264819854872,
    105776769226450,86309364941076,69692948269312,55699773618914,44067722849938,34518902219150,
    26774458239810,20566786474968,15647795410940,11793051054450,8805058310358,6513366849110,
    4774186393456,3467584750414,2495579406736,1779881522200,1258004761998,880862084232,
    611019494028,419928107932,285738320820,192279907790,127901380774,84030733732,54311874556,
    34299969598,21056807754,12505278272,7054526274,3307146538,1232459622,330033626]]
private def rkmC_w64_m16_s5a_7 : List ℤ := pzigCat
  [
   [302715756,31281730,431054625,1228575563,1775890529,1458819581,87226616,2562563914,5541818908,
    7495827516,6687426592,2358830442,5873912165,16435617637,25512029997,28324723903,20153727029,
    2177044976,37024239834,76924622688,108693616966,115121951912,78828753738,9830246919,
    147149475573,310753126907,456723912049,525074731379,450359477303,178530078371,311377178082,
    986255302414,1744506759310,2411882743160,2753792279124,2505946461732,1423198022884,
    660681722451,3765852765381,7705612441267,12043463545437,16075339501417,18847386345575,
    19211635091489,15916025978971,7721644598629,6464611175230,27457347079470,55677797519588,
    91068738288954,133052036521226,180535320505492,231967834372114,285437692376570,
    338805287462070,389855375296186,436452460834144,476687172786570,508998466438562,
    532262276608518,545841329538824,549595508691598,543855110323304,529361805820204,
    507187575159944,478640518734948,445164852892880,408245190720858,369322736550580,
    329725370456878,290616231186020,252961136490056,217514503892594,184818400533392,
    155216253553208,128875017074386,105812378678720,85927196753178,69029387183422,54868662812524,
    43159582177846,33601602212588,25896051317690,19758882141780,14928168163108,11168878397822,
    8275880919142,6073994865342,4415968952814,3180332319584,2268899156138,1603658275610,
    1122853739470,778840781492,534840396520,363623863482,244824956078,162899672258,106876588364,
    69182241218,44087976840,27352602120,16264645692,9152631500,4776302904,2146752194,640176516]]
private def rkmC_w64_m16_s5a_8 : List ℤ := pzigCat
  [
   [217390689,79628994,678978814,1026786630,808975430,64486549,1601269645,3223784857,3750707933,
    2603170557,735077716,5951217828,10998275414,13541656528,10971062984,1458622802,14381729793,
    32396871953,45891024597,46219426785,25912923185,17552586948,78265472400,140776660244,
    180909700536,170349556376,86457375814,78221389025,306402838871,549466540151,730433812959,
    755748869531,536062799173,15056233645,799942900722,1813752705622,2832028886158,3570179933588,
    3686283815924,2839907617898,767252682528,2634101728475,7225347216741,12566734932105,
    17892448585561,22128062395359,23954927260653,21920850360843,14582937193469,667906795359,
    20767665670428,50200458329640,87543826210890,132103758254476,182595084083412,237216459397910,
    293776253483608,349854946989988,402986423427202,450839694294158,491383500998996,
    523016487500686,544656643534958,555783010891822,556430817754370,547143645271242,
    528894166527200,502982755658100,470923286250516,434330330230908,394815472884414,
    353898423110884,312938593037778,273088384884990,235268139552320,200160476984244,
    168219579610420,139692829949774,114651316757566,93023494800068,74629001965410,59211854505342,
    46470447255140,36081949744918,27721574142934,21077687638406,15862323421490,11817054385772,
    8715626515244,6364594086364,4602166291514,3295459846008,2336995554890,1641241828930,
    1141345239926,785904417296,535800732446,361638666344,241354381470,159230231602,103501175270,
    66253717926,41833767026,25710731508,14949084968,8024770724,3903742584,1626083722,456661094]]
private def rkmC_w64_m16_s5a_9 : List ℤ := pzigCat
  [
   [451862805,582994411,453850569,440578726,1545067202,2236739836,1938043828,381742044,2472635009,
    5565092471,7133118963,5794349943,515880011,8205586522,17629437906,23288706310,20605428884,
    6447851476,18934180287,49293680349,73217649391,77090443027,48373517993,17669278284,
    112140783140,210671217582,275747459530,264207985872,141805029034,101455141707,436999350591,
    791242819963,1050070046191,1078234241065,752817082923,4280597947,1142017549572,2535276153514,
    3890181877910,4808658334570,4834977704586,3539751867038,625420309522,3964621927829,
    9954469354533,16677903599273,23070935799361,27725227134725,29000060016111,25182676759945,
    14679611166989,3785226217456,30991930489296,67090092818274,111526815122152,163046586093920,
    219764582133382,279305509823272,338990009811018,396046869390366,447829227685918,
    492011918790334,526749685921808,550784607317984,563497568698502,564903851862032,
    555597439619306,536657398149040,509528020453014,475888103357196,437519167773562,
    396186761594536,353541448329424,311043447277454,269913737892600,231109182083820,
    195320297715612,162987035183840,134326013709034,109366287270002,87989299074340,69967842008768,
    55002281143600,42752602897348,32864288819238,24988286023252,18795969291418,13988685402640,
    10302336181288,7509013977526,5416850100984,3867858699734,2734080817270,1913329585448,
    1325415644396,908683208116,616507067146,413945153408,274990372556,180548583172,116905553478,
    74422831386,46400609774,28177263196,16505144094,9150040508,4619241556,1949831806,537458808]]
private def rkmC_w64_m16_s5a_10 : List ℤ := pzigCat
  [
   [243653713,967268401,1554748347,1348454973,229834399,1610532012,3605678032,4442205800,
    3034042314,903095397,6479459873,11454761427,12832954969,7834440415,4088933550,20175226196,
    34754085976,39639134236,27102499616,5319174185,52237642391,99408131341,125183525387,
    107235873579,32040698003,96453722656,250769369052,380178772534,420444421760,312609173878,
    26529650304,416804119703,931932365161,1370694429839,1546062924593,1275504566173,438187094639,
    967199401884,2776007943216,4641465551000,6059881658518,6440142668682,5213938708856,
    1972064803890,3394762769817,10579221112645,18789170459503,26745439665053,32757959065439,
    34876544564859,31099008870453,19611458225189,971919834648,31402728216004,71655072328694,
    120866537771792,177370611106932,238815876030192,302358373995098,364902412895016,
    423359435199698,474896749176210,517150739812140,548383965018176,567575163403120,
    574440356203186,569389904317336,553433058622318,528046182506664,495021376657530,
    456311454403696,413886031022320,369609721128158,325148215738340,281904560757366,
    240985783527118,203196933585050,169056666753078,138827952817980,112558594408886,
    90126803820898,71287033595252,55712077485030,43029301353176,32850385362870,24794443027140,
    18504488308422,13657696400900,9970577156900,7200457000938,5144413930074,3636424550632,
    2543311515508,1760092872370,1205304537984,816689080250,547409420636,362789808234,237546711686,
    153490969958,97689960856,61053973348,37277397128,22050797118,12471124816,6601174912,
    3149444336,1250471122,326070492]]
private def rkmC_w64_m16_s5a_11 : List ℤ := pzigCat
  [
   [312943136,706279692,527572268,475214667,1962784289,2967034399,2810478507,863063573,2668857508,
    6348560456,8081801584,5890492970,726325019,10544470135,19718878349,22448330513,14174715981,
    5956332866,33340701646,57604437140,64800906922,42833478258,11342667249,87315090661,
    160320404029,195092691201,157556905403,30383333437,173758398318,405008905946,580562834586,
    603614135028,394495317930,73263925331,743242955833,1464000278561,2003119002577,2092566827065,
    1500781255811,115908355313,1979282347248,4461855107380,6773366664024,8186180759204,
    7928268310440,5351121338118,114263001664,7649087864459,17221104431505,27271358280755,
    35927586261823,40944524428981,39952012109221,30749409252519,11604956803953,18483941535108,
    59608317129870,110869191005088,170413588774256,235580063595130,303133675596070,
    369558169783986,431367706950354,485401855186522,529072584713686,560539747415294,
    578802514905580,583706550438752,575876618424102,556590540379764,527614124112622,
    491018502137620,449000249864142,403720524807128,357173979697620,311093199476700,
    266890256658504,225633225285082,188052293679796,154568219953982,125335580413760,
    100294014951730,79221725063790,61786561520540,47591280658078,36210982104242,27222103246004,
    20223326590376,14849281431898,10778148709812,7734388404626,5487856397964,3850528720246,
    2671859115430,1833587644568,1244416426410,835196869050,554085711916,363376936054,235175937756,
    150134414400,94372716814,58053378046,34813489716,20340303134,11462830192,6047635024,
    2840547736,1090649640,272012140]]
private def rkmC_w64_m16_s5a_12 : List ℤ := pzigCat
  [
   [210629199,381193271,191932350,1013571470,1724061142,1866003290,607150590,1951962633,
    4559715105,5694024161,3994522249,1037644454,8039822822,13586398906,13520400094,5369855392,
    9904170309,27259833595,37896777663,32387461247,6244846581,36022762074,80078385422,
    104151328748,86404935928,16286999574,95862833431,215760086045,290900949935,266317128603,
    107805570483,175287564560,517182132196,800432584918,882493236958,641234430742,28321120122,
    885945369759,1894052991165,2673140051107,2851552711903,2110962367775,303039642801,
    2448639515958,5693796784194,8674072990882,10426153438766,9961432332686,6496086770016,
    309763354031,10153528453199,21978816637377,33983385382553,43757744281409,48543027969949,
    45574483729641,32459415416831,7531022391809,29876131608772,79270181824218,138988274499986,
    206326281945214,277791400914088,349439955240288,417253496884198,477505423042274,
    527075646116862,563681549644476,586006657862432,593724771295100,587428771050238,
    568486031313264,538843115285266,500809870611118,456844228871698,409361559286342,
    360580269468606,312411351946714,266394106253664,223672116884904,185004490126086,
    150803344649576,121187016463306,96041985688786,75085889500290,57925346503442,44106367811622,
    33155648978924,24611051952830,18042767527702,13066113133840,9348441180042,6608987879894,
    4617380615038,3188189539618,2175676558106,1467620268262,978484464784,644492777924,
    419231270584,269164443294,170311250366,106011118412,64750595058,38835923106,22507125686,
    12617078936,6730943260,3193966690,1211398360,291532666]]
private def rkmC_w64_m16_s5a_13 : List ℤ := pzigCat
  [
   [292161804,56854014,473642571,1181765149,1249375877,353165,2037025170,3698931702,3841696416,
    1466654378,3309647831,8348943223,10365830127,6768383391,2753924052,15105670206,24009235838,
    22444379494,6502912986,21066079575,49555450659,63051267909,47209111057,2470185660,74395834822,
    140279482200,162909568224,111511183106,20727100721,204363862201,373335416825,440959817283,
    331415645363,17664019087,448937544388,931537834794,1232321877438,1149057395784,552490332762,
    538966490207,1914671124217,3181244516271,3835318929201,3394859215699,1560794155709,
    1630097668082,5711445640160,9788216808690,12653914531082,13015635876086,9792922042144,
    2434285262862,8818873676203,22782014614683,37335579608263,49605966130395,56299672768313,
    54143790148293,40361575611523,13105177935427,28223338672996,82813461206530,148473096528328,
    221831432985644,298686431398034,374440643520850,444564444860388,505023468634568,
    552623623389148,585237111235598,601897570493490,602769947603564,589012785882274,
    562565609458314,525895234982456,481734041831082,432838754024158,381789901197110,
    330843160844072,281838647541230,236160674833698,194744002552122,158112911152826,
    126443292250794,99634864928304,77385303817112,59261103410582,44757714952048,33347364568004,
    24516103065366,17788022167324,12740220085150,9008673725828,6290111863082,4337385489256,
    2953853266350,1986931851564,1320057925800,865988129082,560732169756,358349392112,225608766108,
    139929806518,85342679756,50958591676,29722008744,16809438294,9001961896,4376294576,1917063254,
    486421922]]
private theorem rkmWC_w64_m16_s5a_0 : bWinChk 564 17 100000000 1024 rkmPhb_w64_m16_s5a
    580 rkmXsWin_w64_m16_s5a_in 603 rkmC_w64_m16_s5a_1 3357379570 = true := by decide +kernel
private theorem rkmWC_w64_m16_s5a_1 : bWinChk 564 17 100000000 1024 rkmPhb_w64_m16_s5a
    603 rkmC_w64_m16_s5a_1 623 rkmC_w64_m16_s5a_2 3256751341 = true := by decide +kernel
private theorem rkmWC_w64_m16_s5a_2 : bWinChk 564 17 100000000 1024 rkmPhb_w64_m16_s5a
    623 rkmC_w64_m16_s5a_2 644 rkmC_w64_m16_s5a_3 2872227488 = true := by decide +kernel
private theorem rkmWC_w64_m16_s5a_3 : bWinChk 564 17 100000000 1024 rkmPhb_w64_m16_s5a
    644 rkmC_w64_m16_s5a_3 662 rkmC_w64_m16_s5a_4 3253572309 = true := by decide +kernel
private theorem rkmWC_w64_m16_s5a_4 : bWinChk 564 16 100000000 1024 rkmPhb_w64_m16_s5a
    662 rkmC_w64_m16_s5a_4 681 rkmC_w64_m16_s5a_5 2888231776 = true := by decide +kernel
private theorem rkmWC_w64_m16_s5a_5 : bWinChk 564 17 100000000 1024 rkmPhb_w64_m16_s5a
    681 rkmC_w64_m16_s5a_5 699 rkmC_w64_m16_s5a_6 3337132764 = true := by decide +kernel
private theorem rkmWC_w64_m16_s5a_6 : bWinChk 564 16 100000000 1024 rkmPhb_w64_m16_s5a
    699 rkmC_w64_m16_s5a_6 715 rkmC_w64_m16_s5a_7 2832568341 = true := by decide +kernel
private theorem rkmWC_w64_m16_s5a_7 : bWinChk 564 16 100000000 1024 rkmPhb_w64_m16_s5a
    715 rkmC_w64_m16_s5a_7 730 rkmC_w64_m16_s5a_8 2861890842 = true := by decide +kernel
private theorem rkmWC_w64_m16_s5a_8 : bWinChk 564 16 100000000 1024 rkmPhb_w64_m16_s5a
    730 rkmC_w64_m16_s5a_8 746 rkmC_w64_m16_s5a_9 3038263588 = true := by decide +kernel
private theorem rkmWC_w64_m16_s5a_9 : bWinChk 564 16 100000000 1024 rkmPhb_w64_m16_s5a
    746 rkmC_w64_m16_s5a_9 762 rkmC_w64_m16_s5a_10 2257125240 = true := by decide +kernel
private theorem rkmWC_w64_m16_s5a_10 : bWinChk 564 16 100000000 1024 rkmPhb_w64_m16_s5a
    762 rkmC_w64_m16_s5a_10 776 rkmC_w64_m16_s5a_11 2495759268 = true := by decide +kernel
private theorem rkmWC_w64_m16_s5a_11 : bWinChk 564 16 100000000 1024 rkmPhb_w64_m16_s5a
    776 rkmC_w64_m16_s5a_11 789 rkmC_w64_m16_s5a_12 2551215709 = true := by decide +kernel
private theorem rkmWC_w64_m16_s5a_12 : bWinChk 564 16 100000000 1024 rkmPhb_w64_m16_s5a
    789 rkmC_w64_m16_s5a_12 802 rkmC_w64_m16_s5a_13 2847596409 = true := by decide +kernel
private theorem rkmWC_w64_m16_s5a_13 : bWinChk 564 15 100000000 1024 rkmPhb_w64_m16_s5a
    802 rkmC_w64_m16_s5a_13 815 rkmXsWin_w64_m16_s5a_out 2467539875 = true := by decide +kernel
/-- Certified `w64_m16_s5a` partial walk (`228` substeps). -/
theorem rkmWinIterSnd_w64_m16_s5a :
    RkmWinIterSound 228 1024 rkmHbWin_w64_m16_s5a 580 rkmXsWin_w64_m16_s5a_in
      815 rkmXsWin_w64_m16_s5a_out 40317254520 :=
  rkmChS 228 40317254520 (rkmChS 213 37849714645 (rkmChS 197 35002118236 (rkmChS 181
    32450902527 (rkmChS 165 29955143259 (rkmChS 149 27698018019 (rkmChS 133 24659754431 (rkmChS
    117 21797863589 (rkmChS 101 18965295248 (rkmChS 84 15628162484 (rkmChS 68 12739930708
    (rkmChS 51 9486358399 (rkmChS 34 6614130911 (bWinChk_sound rkmHhb_w64_m16_s5a
    rkmWC_w64_m16_s5a_0) rkmHhb_w64_m16_s5a rkmWC_w64_m16_s5a_1 rfl rfl) rkmHhb_w64_m16_s5a
    rkmWC_w64_m16_s5a_2 rfl rfl) rkmHhb_w64_m16_s5a rkmWC_w64_m16_s5a_3 rfl rfl)
    rkmHhb_w64_m16_s5a rkmWC_w64_m16_s5a_4 rfl rfl) rkmHhb_w64_m16_s5a rkmWC_w64_m16_s5a_5 rfl
    rfl) rkmHhb_w64_m16_s5a rkmWC_w64_m16_s5a_6 rfl rfl) rkmHhb_w64_m16_s5a rkmWC_w64_m16_s5a_7
    rfl rfl) rkmHhb_w64_m16_s5a rkmWC_w64_m16_s5a_8 rfl rfl) rkmHhb_w64_m16_s5a
    rkmWC_w64_m16_s5a_9 rfl rfl) rkmHhb_w64_m16_s5a rkmWC_w64_m16_s5a_10 rfl rfl)
    rkmHhb_w64_m16_s5a rkmWC_w64_m16_s5a_11 rfl rfl) rkmHhb_w64_m16_s5a rkmWC_w64_m16_s5a_12
    rfl rfl) rkmHhb_w64_m16_s5a rkmWC_w64_m16_s5a_13 rfl rfl
/-- Cumulative `w64_m16` part `1` lane witness. -/
theorem rkmHiLane_w64_m16_wint1 : @rkmWinIterSnd_w64_m16_s5a = @rkmWinIterSnd_w64_m16_s5a :=
  (And.intro (Eq.refl rkmHiLane_w64_m16_wint0) rfl).right
/-- Module lane witness for `FindAllJohnsonRampKickMuxHiW64T05`. -/
theorem laneWitness_FindAllJohnsonRampKickMuxHiW64T05 :
    @rkmHiLane_w64_m16_wint1 = @rkmHiLane_w64_m16_wint1 := rfl

end
end QuantumComputation.Specs.DickeSol
