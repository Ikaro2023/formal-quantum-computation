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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi512T9

/-
# Caustic `r = 1024` Halo-16 Walk `w512` Parts `1..2` (`RkMuxHiW512WinT2`)
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Generator list for `w512_s0`. -/
def rkmHbWin_w512_s0 : List ℤ := altBuildHbFrom 512 1024 51941544502 0 512
/-- Entry `rkmXsWin_w512_s0_in`. -/
def rkmXsWin_w512_s0_in : List ℤ := [rkmP 1000000000000000]
/-- Exit `rkmXsWin_w512_s0_out`. -/
def rkmXsWin_w512_s0_out : List ℤ := let p := rkmP; [p 135703812, p 329016412, p 521216127,
  p 763028677, p 1159897861, p 1617284703, p 2377331821, p 3479365191, p 4999198682, p 7148685948,
  p 10076890257, p 14214495729, p 19865821780, p 27601632327, p 38168603989, p 52339651205,
  p 71392669419, p 96703353032, p 130160586569, p 174137079786, p 231457045577, p 305812207751,
  p 401456810320, p 523775545234, p 679196330017, p 875294601151, p 1121247144129, p 1427552302520,
  p 1806598665867, p 2272536073934, p 2841484597875, p 3531798836772, p 4363714053745,
  p 5359811643438, p 6544570307289, p 7944354162338, p 9587279454154, p 11502616909063,
  p 13720776267431, p 16272246417236, p 19187205088862, p 22494776853016, p 26221963270649,
  p 30393001824128, p 35027828313407, p 40141441145127, p 45742696917402, p 51833135845747,
  p 58406233195782, p 65446068161375, p 72927095950716, p 80813311790903, p 89057983544619,
  p 97603780995141, p 106382673261846, p 115317000876997, p 124319936449120, p 133296908917063,
  p 142147152518355, p 150765256358874, p 159043649835228, p 166874322391126, p 174151516774239,
  p 180773950968544, p 186647056707476, p 191685567618369, p 195815108085789, p 198974499883879,
  p 201116963513270, p 202211343494713, p 202243031370236, p 201213871255610, p 199142553707778,
  p 196063627067454, p 192026812651847, p 187095663582213, p 181345653551566, p 174862729212019,
  p 167740699810212, p 160079432219198, p 151982338067165, p 143554036382306, p 134898497992810,
  p 126116535943643, p 117304501861313, p 108552295150848, p 99942197462802, p 91547961581307,
  p 83433708712726, p 75654014004246, p 68253229499954, p 61265940625199, p 54717175072834,
  p 48622745955479, p 42990363328766, p 37819911300881, p 33104858386861, p 28832868695197,
  p 24986818957616, p 21545976287779, p 18486450789433, p 15782609053691, p 13407354783784,
  p 11333116912942, p 9532434042032, p 7978176501917, p 6644453120158, p 5506368458099,
  p 4540751769573, p 3726062036537, p 3042448117257, p 2472109613464, p 1998758875280,
  p 1608146534449, p 1287515660424, p 1025725571344, p 813218555459, p 641525462993, p 503684120094,
  p 393527317278, p 305999826672, p 236854511911, p 182414713979, p 139884851969, p 106690573850,
  p 80978103420, p 61124206551, p 45814261633, p 34160430534, p 25205326541, p 18470625609,
  p 13352614249, p 9485006715, p 6623028351, p 4405772549, p 2826287027, p 1616071354, p 791704403,
  p 290280028]
/-- Generator list for `w512_s1`. -/
def rkmHbWin_w512_s1 : List ℤ := altBuildHbFrom 1024 1024 29648891129 0 1024
/-- Entry `rkmXsWin_w512_s1_in`. -/
def rkmXsWin_w512_s1_in : List ℤ := let p := rkmP; [p 135703812, p 329016412, p 521216127,
  p 763028677, p 1159897861, p 1617284703, p 2377331821, p 3479365191, p 4999198682, p 7148685948,
  p 10076890257, p 14214495729, p 19865821780, p 27601632327, p 38168603989, p 52339651205,
  p 71392669419, p 96703353032, p 130160586569, p 174137079786, p 231457045577, p 305812207751,
  p 401456810320, p 523775545234, p 679196330017, p 875294601151, p 1121247144129, p 1427552302520,
  p 1806598665867, p 2272536073934, p 2841484597875, p 3531798836772, p 4363714053745,
  p 5359811643438, p 6544570307289, p 7944354162338, p 9587279454154, p 11502616909063,
  p 13720776267431, p 16272246417236, p 19187205088862, p 22494776853016, p 26221963270649,
  p 30393001824128, p 35027828313407, p 40141441145127, p 45742696917402, p 51833135845747,
  p 58406233195782, p 65446068161375, p 72927095950716, p 80813311790903, p 89057983544619,
  p 97603780995141, p 106382673261846, p 115317000876997, p 124319936449120, p 133296908917063,
  p 142147152518355, p 150765256358874, p 159043649835228, p 166874322391126, p 174151516774239,
  p 180773950968544, p 186647056707476, p 191685567618369, p 195815108085789, p 198974499883879,
  p 201116963513270, p 202211343494713, p 202243031370236, p 201213871255610, p 199142553707778,
  p 196063627067454, p 192026812651847, p 187095663582213, p 181345653551566, p 174862729212019,
  p 167740699810212, p 160079432219198, p 151982338067165, p 143554036382306, p 134898497992810,
  p 126116535943643, p 117304501861313, p 108552295150848, p 99942197462802, p 91547961581307,
  p 83433708712726, p 75654014004246, p 68253229499954, p 61265940625199, p 54717175072834,
  p 48622745955479, p 42990363328766, p 37819911300881, p 33104858386861, p 28832868695197,
  p 24986818957616, p 21545976287779, p 18486450789433, p 15782609053691, p 13407354783784,
  p 11333116912942, p 9532434042032, p 7978176501917, p 6644453120158, p 5506368458099,
  p 4540751769573, p 3726062036537, p 3042448117257, p 2472109613464, p 1998758875280,
  p 1608146534449, p 1287515660424, p 1025725571344, p 813218555459, p 641525462993, p 503684120094,
  p 393527317278, p 305999826672, p 236854511911, p 182414713979, p 139884851969, p 106690573850,
  p 80978103420, p 61124206551, p 45814261633, p 34160430534, p 25205326541, p 18470625609,
  p 13352614249, p 9485006715, p 6623028351, p 4405772549, p 2826287027, p 1616071354, p 791704403,
  p 290280028]
/-- Exit `rkmXsWin_w512_s1_out`. -/
def rkmXsWin_w512_s1_out : List ℤ := let p := rkmP; [p 202271878, p 354232405, p 590008408,
  p 889544348, p 1320559407, p 1967584281, p 2753240416, p 3996982235, p 5618966281, p 7859964366,
  p 10969130466, p 15148886678, p 20883235812, p 28587682205, p 38864623736, p 52694736290,
  p 70874750698, p 94812143837, p 126086711804, p 166761746108, p 219347898105, p 286787247708,
  p 372931867291, p 482379520313, p 620253365825, p 793197634986, p 1008778684200, p 1275845108404,
  p 1604724146595, p 2007306926847, p 2497147542691, p 3089571312761, p 3801690491006,
  p 4652665164177, p 5663168900966, p 6855996601760, p 8255399000900, p 9886924427833,
  p 11777448508984, p 13954433512957, p 16445498665903, p 19278249461757, p 22478812673954,
  p 26071880497295, p 30079476374999, p 34519972638281, p 39407530772369, p 44750816401923,
  p 50552082443992, p 56806819182921, p 63502127630221, p 70616729503573, p 78120143468616,
  p 85972309187337, p 94123752758704, p 102515377735220, p 111078902712464, p 119737993594585,
  p 128408369108794, p 136999810674140, p 145417284052575, p 153562421238366, p 161335784924843,
  p 168638621113751, p 175374838851800, p 181453585139516, p 186790521366176, p 191310501022185,
  p 194949015518323, p 197653528758909, p 199385181440857, p 200119457992967, p 199846564582819,
  p 198572215326900, p 196316730134003, p 193115137836529, p 189016038364716, p 184080123414474,
  p 178379124540486, p 171993911826792, p 165012331163676, p 157527811756664, p 149636590124126,
  p 141436236944198, p 133023619848671, p 124492759941660, p 115933558775945, p 107430279737857,
  p 99060006895700, p 90892339792815, p 82988003796394, p 75398814043410, p 68167549553189,
  p 61327662894571, p 54903839131181, p 48912471737425, p 43361832367469, p 38253434172583,
  p 33582245935986, p 29337716783958, p 25504894231650, p 22064844548796, p 18995919633149,
  p 16274366653575, p 13875022034886, p 11771964362863, p 9939344721663, p 8351315206091,
  p 6983080004393, p 5810828164734, p 4811918752432, p 3965480519085, p 3252212397097,
  p 2654253716949, p 2155892368927, p 1742702229444, p 1401894376911, p 1122405889484,
  p 894358026588, p 709255988294, p 559817784718, p 439776599372, p 343776346563, p 267497085735,
  p 206964270130, p 159249150321, p 121906149205, p 92685660306, p 69964752940, p 52469619618,
  p 38896838601, p 28533881399, p 20611099085, p 14578067144, p 10090897052, p 6724908667,
  p 4207744678, p 2462720844, p 1298428482, p 464251418, p 114518692]
/-- Generator list for `w512_s2a`. -/
def rkmHbWin_w512_s2a : List ℤ := altBuildHbFrom 2048 1024 18391866913 0 1024
/-- Entry `rkmXsWin_w512_s2a_in`. -/
def rkmXsWin_w512_s2a_in : List ℤ := let p := rkmP; [p 202271878, p 354232405, p 590008408,
  p 889544348, p 1320559407, p 1967584281, p 2753240416, p 3996982235, p 5618966281, p 7859964366,
  p 10969130466, p 15148886678, p 20883235812, p 28587682205, p 38864623736, p 52694736290,
  p 70874750698, p 94812143837, p 126086711804, p 166761746108, p 219347898105, p 286787247708,
  p 372931867291, p 482379520313, p 620253365825, p 793197634986, p 1008778684200, p 1275845108404,
  p 1604724146595, p 2007306926847, p 2497147542691, p 3089571312761, p 3801690491006,
  p 4652665164177, p 5663168900966, p 6855996601760, p 8255399000900, p 9886924427833,
  p 11777448508984, p 13954433512957, p 16445498665903, p 19278249461757, p 22478812673954,
  p 26071880497295, p 30079476374999, p 34519972638281, p 39407530772369, p 44750816401923,
  p 50552082443992, p 56806819182921, p 63502127630221, p 70616729503573, p 78120143468616,
  p 85972309187337, p 94123752758704, p 102515377735220, p 111078902712464, p 119737993594585,
  p 128408369108794, p 136999810674140, p 145417284052575, p 153562421238366, p 161335784924843,
  p 168638621113751, p 175374838851800, p 181453585139516, p 186790521366176, p 191310501022185,
  p 194949015518323, p 197653528758909, p 199385181440857, p 200119457992967, p 199846564582819,
  p 198572215326900, p 196316730134003, p 193115137836529, p 189016038364716, p 184080123414474,
  p 178379124540486, p 171993911826792, p 165012331163676, p 157527811756664, p 149636590124126,
  p 141436236944198, p 133023619848671, p 124492759941660, p 115933558775945, p 107430279737857,
  p 99060006895700, p 90892339792815, p 82988003796394, p 75398814043410, p 68167549553189,
  p 61327662894571, p 54903839131181, p 48912471737425, p 43361832367469, p 38253434172583,
  p 33582245935986, p 29337716783958, p 25504894231650, p 22064844548796, p 18995919633149,
  p 16274366653575, p 13875022034886, p 11771964362863, p 9939344721663, p 8351315206091,
  p 6983080004393, p 5810828164734, p 4811918752432, p 3965480519085, p 3252212397097,
  p 2654253716949, p 2155892368927, p 1742702229444, p 1401894376911, p 1122405889484,
  p 894358026588, p 709255988294, p 559817784718, p 439776599372, p 343776346563, p 267497085735,
  p 206964270130, p 159249150321, p 121906149205, p 92685660306, p 69964752940, p 52469619618,
  p 38896838601, p 28533881399, p 20611099085, p 14578067144, p 10090897052, p 6724908667,
  p 4207744678, p 2462720844, p 1298428482, p 464251418, p 114518692]
/-- Exit `rkmXsWin_w512_s2a_out`. -/
def rkmXsWin_w512_s2a_out : List ℤ := let p := rkmP; [p 117178024, p 191185493, p 449942720,
  p 761630059, p 1271688018, p 2188055122, p 3555594812, p 5700533352, p 9001504118, p 13893261220,
  p 21257293814, p 31994381497, p 47540541121, p 70007503225, p 101753837466, p 146351251435,
  p 208146596040, p 292884946838, p 407902312967, p 562287017590, p 767331914178, p 1037010271333,
  p 1387947376177, p 1840175828601, p 2417181129048, p 3146110385017, p 4058111443274,
  p 5188264277817, p 6575349769636, p 8261835658468, p 10292849285134, p 12715638837522,
  p 15578837252320, p 18930536777432, p 22817484813737, p 27282733005104, p 32363790313191,
  p 38090719279516, p 44483708627790, p 51550880103599, p 59286627627414, p 67669473701538,
  p 76660633882698, p 86203459120156, p 96222206502264, p 106622869259224, p 117293769461910,
  p 128106972591228, p 138920685316288, p 149582250677191, p 159931310331182, p 169804087874411,
  p 179037679498152, p 187474142265145, p 194965689083610, p 201378411857811, p 206596610256866,
  p 210526297363609, p 213097830142597, p 214267918884996, p 214021196043674, p 212369946355695,
  p 209353557892379, p 205037600633798, p 199510634448538, p 192881835674728, p 185277489795915,
  p 176836837820516, p 167707955458433, p 158043982249060, p 147998449932854, p 137721763777137,
  p 127357904768824, p 117040755887493, p 106892409256436, p 97020982509619, p 87519163598492,
  p 78463686533897, p 69915410609672, p 61919015812936, p 54504348125000, p 47687438841587,
  p 41471437756440, p 35848885765992, p 30802939294282, p 26309035943929, p 22336787968626,
  p 18851670195064, p 15815944411478, p 13190648946384, p 10936375792883, p 9013991530141,
  p 7386005298615, p 6016714237213, p 4872686668396, p 3923252015981, p 3140642878166,
  p 2499597939334, p 1978008412360, p 1556341763437, p 1217459822707, p 946883851493,
  p 732192737733, p 562804090357, p 430032837442, p 326595401912, p 246449131235, p 184649585357,
  p 137443146552, p 101443533207, p 74192740565, p 53826463867, p 38593619351, p 27233094358,
  p 18910560190, p 12846408438, p 8410291123, p 5257742083, p 3148738891, p 1592612959, p 648474906,
  p 190393943]
/-- Kick mask `w512` seg `2`. -/
def rkmMkHi_w512_s2 : List Bool := List.replicate 996 false ++ [
  true, false, false, false, false, true, true, true, false, false, false, false, false, false,
  true, true, true, true, false, false, false, false, false, false, false, false, true, true]
/-- Kick mask `w512` seg `3`. -/
def rkmMkHi_w512_s3 : List Bool := List.replicate 990 false ++ [
  true, false, false, true, false, true, true, false, true, false, true, false, true, false, true,
  false, false, true, false, false, true, true, false, true, true, false, false, false, true]
/-- Kick mask `w512` seg `4`. -/
def rkmMkHi_w512_s4 : List Bool := List.replicate 988 false ++ [
  true, false, false, false, false, true, false, false, true, false, false, true, false, true,
  false, true, false, false, true, false, true, false, true, false, true, true, true, true, true,
  true, true, true, true, true]
/-- Kick mask `w512` seg `5`. -/
def rkmMkHi_w512_s5 : List Bool := List.replicate 989 false ++ [
  true, true, false, false, false, true, false, true, false, true, true, false, false, true, true,
  false, false, false, false, true, false, false, false, true, true, false, true, true, true, true,
  true, true, true, true]
/-- Kick mask `w512` seg `6`. -/
def rkmMkHi_w512_s6 : List Bool := List.replicate 986 false ++ [
  true, false, true, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true, false, false, false, false, true, true, true,
  false, false, true, true]
/-- Kick-mask schedule for `w512` `r = 1024`. -/
def rkmMasksHi_w512_r1024 : List (List Bool) := [
  [], [], rkmMkHi_w512_s2, rkmMkHi_w512_s3, rkmMkHi_w512_s4, rkmMkHi_w512_s5, rkmMkHi_w512_s6, []]
/-- Certified `rowLo12` vector for `w512` `r = 1024`. -/
def rkmRowHi_w512_r1024 : List ℕ := List.replicate 958 0 ++ [
  158, 2207, 5421, 7220, 5526, 1440, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4052, 18790,
  3068, 0, 0, 0, 0, 0, 0, 44555, 3853, 0, 0, 31309, 0, 43911, 0, 1100458, 4631395, 12377231, 24556,
  40879, 47265, 953042, 275050, 0, 3227694, 306668153, 21669591, 3737104, 104523044, 368617162,
  2871570, 2972161, 2684311, 6494500, 1080145169, 552332, 146799673, 251564577, 1788374475,
  518878644, 1485463279, 993491717167]

end

public section

private abbrev fN {α : Type} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β :=
  HighDForce.withForcedList xs k
private abbrev bz0 : ℕ := 100000000000000000
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
private theorem n0m (z : ℕ) : (0 : ℕ) = Nat.mul 0 z := by rw [Nat.mul_eq]; omega
private theorem nmod (x y : ℕ) : Nat.mod x y = x % y := rfl
private abbrev bSV (v P Q d : ℕ) : ℕ :=
  Nat.sub (Nat.add v (Nat.div (Nat.sub P Q) d)) (Nat.div (Nat.sub Q P) d)
private theorem svEq (z v P Q d : ℕ) (hv : 0 < bSV v P Q d) :
    ((bSV v P Q d : ℤ) - (z : ℤ)) = ((v : ℤ) - (z : ℤ)) + zTdiv ((P : ℤ) - (Q : ℤ)) d := by
  rw [← sntEq]; unfold bSV at hv ⊢; unfold rkmUltraSubNatTdiv
  simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢; revert hv
  cases hd : Q - P with
  | zero =>
    intro _; dsimp only; rw [Nat.zero_div, Nat.sub_zero, Int.ofNat_eq_natCast]; push_cast; ring
  | succ k =>
    intro hv; dsimp only at hv ⊢; have hpq : P - Q = 0 := by omega
    rw [hpq, Nat.zero_div, Nat.add_zero] at hv ⊢; rw [ngEq]; omega
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
        uCN (bSV v (Nat.add p0 bz) (Nat.add (Nat.mul b (bHO z cT)) q0) d)
          (bSlZ z d rem (Nat.mul b c) bz bR vT cT)
      | v :: vT, [] =>
        uCN (bSV v (Nat.add p0 bz) (Nat.add bz q0) d) (bSlZ z d rem bz bz bR vT [])
      | [], c :: cT =>
        uCN (bSV z (Nat.add p0 bz) (Nat.add (Nat.mul b (bHO z cT)) q0) d)
          (bSlZ z d rem (Nat.mul b c) bz bR [] cT)
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
        | cons c cT => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b c bR [] cT]
      | cons v vT => cases cs with
        | nil => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b z bR vT []]
        | cons c cT => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b c bR vT cT]
private inductive HbZ4 : Type
  | tail : List ℕ → HbZ4
  | c4 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → HbZ4 → HbZ4
private abbrev hbz4C (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) (t : List ℕ) : List ℕ :=
  b1 :: z1 :: b2 :: z2 :: b3 :: z3 :: b4 :: z4 :: t
private def hbz4L : HbZ4 → List ℕ
  | HbZ4.tail l => l
  | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r => hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L r)
private def fH4 {α : Type} (h : HbZ4) (k : HbZ4 → α) : α :=
  match h with
  | HbZ4.tail l => fL l fun lF => k (HbZ4.tail lF)
  | HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 r => k (HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 r)
private theorem fH4e {α : Type} (h : HbZ4) (k : HbZ4 → α) : fH4 h k = k h := by
  cases h with
  | tail _ => dsimp only [fH4, fL]; rw [rkmb_forceList_eq]
  | c4 _ _ _ _ _ _ _ _ _ => rfl
private def tkZ : ℕ → List ℤ → List ℤ
  | 0, _ => []
  | n + 1, xs => match xs with | [] => [] | x :: r => x :: tkZ n r
private def tk4 : ℕ → List ℕ → List ℕ
  | 0, _ => []
  | q + 1, xs =>
    match xs with
    | x1 :: x2 :: x3 :: x4 :: r => x1 :: x2 :: x3 :: x4 :: tk4 q r
    | r => r
private theorem uHb_tk4 : ∀ (q : ℕ) (b : List ℕ), uHb (tk4 q b) = tkZ (4 * q) (uHb b)
  | 0, _ => by have h0 : 4 * 0 = 0 := rfl; rw [h0]; rfl
  | q + 1, [] => by
    have h4 : 4 * (q + 1) = (4 * q + 3) + 1 := by omega
    rw [h4]; rfl
  | q + 1, [x1] => by
    have h4 : 4 * (q + 1) = (((4 * q) + 1) + 1) + 1 + 1 := by omega
    rw [h4]; rfl
  | q + 1, [x1, x2] => by
    have h4 : 4 * (q + 1) = (((4 * q) + 1) + 1) + 1 + 1 := by omega
    rw [h4]; rfl
  | q + 1, [x1, x2, x3] => by
    have h4 : 4 * (q + 1) = (((4 * q) + 1) + 1) + 1 + 1 := by omega
    rw [h4]; rfl
  | q + 1, x1 :: x2 :: x3 :: x4 :: bs => by
    have h4 : 4 * (q + 1) = (((4 * q) + 1) + 1) + 1 + 1 := by omega
    rw [h4]; dsimp only [tk4, uHb, tkZ]; rw [uHb_tk4 q bs]
private def toH4K : ℕ → List ℕ → HbZ4
  | 0, _ => HbZ4.tail []
  | q + 1, xs =>
    match xs with
    | b1 :: z1 :: b2 :: z2 :: b3 :: z3 :: b4 :: z4 :: bs =>
      match toH4K q bs with
      | HbZ4.tail l => HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 (HbZ4.tail l)
      | HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 t =>
        HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 (HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 t)
    | bs => HbZ4.tail bs
private theorem hbz4L_toH4K (z : ℕ) : ∀ (q : ℕ) (b : List ℕ),
    hbz4L (toH4K q (mkHbZ z b)) = mkHbZ z (tk4 q b)
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | _ + 1, [x1] => by simp only [mkHbZ, tk4, uCN_eq]; rfl
  | _ + 1, [x1, x2] => by simp only [mkHbZ, tk4, uCN_eq]; rfl
  | _ + 1, [x1, x2, x3] => by simp only [mkHbZ, tk4, uCN_eq]; rfl
  | q + 1, x1 :: x2 :: x3 :: x4 :: bs => by
    have ih := hbz4L_toH4K z q bs; simp only [mkHbZ, tk4, uCN_eq]; dsimp only [toH4K]
    cases h : toH4K q (mkHbZ z bs) with
    | tail _ => rw [h] at ih; dsimp only [hbz4L, hbz4C] at ih ⊢; rw [ih]
    | c4 _ _ _ _ _ _ _ _ _ => rw [h] at ih; dsimp only [hbz4L, hbz4C] at ih ⊢; rw [ih]
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
private abbrev hbz4P (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) : List ℕ := [b1, z1, b2, z2, b3, z3, b4, z4]
private theorem hbz4C_app (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) (t : List ℕ) :
    hbz4C b1 z1 b2 z2 b3 z3 b4 z4 t = hbz4P b1 z1 b2 z2 b3 z3 b4 z4 ++ t := rfl
private theorem hbz4P_len (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) :
    (hbz4P b1 z1 b2 z2 b3 z3 b4 z4).length = 8 := rfl
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
  | Q4.tail xs => bHO z xs
private theorem q4Hd_eq (z : ℕ) (w : Q4) : q4Hd z w = bHO z (q4L w) := by
  cases w <;> rfl
private def q4AP : Q4 → Bool
  | Q4.tail xs => bAP xs
  | Q4.c4 x1 x2 x3 x4 r =>
    match Nat.add (Nat.add (Nat.sub 1 x1) (Nat.sub 1 x2))
        (Nat.add (Nat.sub 1 x3) (Nat.sub 1 x4)) with
    | 0 => q4AP r
    | _ + 1 => false
private theorem pos1_false {x : ℕ} (h : (1 - x) = 0) : Nat.ble x 0 = false := by
  cases x with
  | zero => cases h
  | succ _ => rfl
private theorem q4AP_pos : ∀ (w : Q4), q4AP w = true → bAP (q4L w) = true
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
      dsimp only [q4L, bAP]
      rw [pos1_false h1, pos1_false h2, pos1_false h3, pos1_false h4]
      exact q4AP_pos r h
private def bChkV (out : Q4) : Option Q4 :=
  match out with
  | Q4.tail xs => cond (bAP xs) (some (Q4.tail xs)) none
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
            q4S (bSV v1 (Nat.add p0 z1) (Nat.add (Nat.mul b1 c2) q0) d)
              (bSV v2 (Nat.add (Nat.mul b1 c1) z2) (Nat.add (Nat.mul b2 c3) z1) d)
              (bSV v3 (Nat.add (Nat.mul b2 c2) z3) (Nat.add (Nat.mul b3 c4) z2) d)
              (bSV v4 (Nat.add (Nat.mul b3 c3) z4) (Nat.add (Nat.mul b4 (q4Hd z cR)) z3) d)
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
          rw [h4]; dsimp only [hbz4L, hbz4C, q4L, bSlZ, bHO]
          rw [uCN_eq, uCN_eq, uCN_eq, uCN_eq]
          rw [bSlQ4_eq z d rT hr q (Nat.mul b4 c4) z4 bR vR cR]
private def fQ4 {α : Type} (v : Q4) (k : Q4 → α) : α :=
  match v with
  | Q4.tail xs => k (Q4.tail xs)
  | Q4.c4 x1 x2 x3 x4 r => k (Q4.c4 x1 x2 x3 x4 r)
private theorem fQ4_eq {α : Type} (v : Q4) (k : Q4 → α) : fQ4 v k = k v := by
  cases v <;> rfl
private def bStg (z dg mL cL : ℕ) (h4 : HbZ4) (vs cs : Q4) : Option Q4 :=
  fN (rkmNextLen mL cL) fun nL => fN (Nat.div nL 4) fun q4 => fN (Nat.mod nL 4) fun rT =>
    fN (Nat.mul dg wdScale) fun d => bChkV (bSlQ4 z d rT q4 0 0 h4 vs cs)
private theorem bStg_sound (z q dg mL cL : ℕ) (b : List ℕ) {vs cs out : Q4}
    (h : bStg z dg mL cL (toH4K q (mkHbZ z b)) vs cs = some out) :
    bD z (q4L out) =
      rkmUltraHornerStage dg mL cL (uHb (tk4 q b)) (bD z (q4L vs)) (bD z (q4L cs)) := by
  unfold bStg at h; dsimp only [fN] at h
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceNat_eq, bChkV_eq] at h
  have hr : Nat.mod (rkmNextLen mL cL) 4 ≤ 4 := by rw [nmod]; omega
  have hqr : 4 * Nat.div (rkmNextLen mL cL) 4 + Nat.mod (rkmNextLen mL cL) 4 =
      rkmNextLen mL cL := by rw [ndiv, nmod]; omega
  have hsl := bSlZ_eq z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z (tk4 q b) (q4L vs) (q4L cs)
  rw [← n0m z] at hsl
  have heq : q4L (bSlQ4 z (Nat.mul dg wdScale) (Nat.mod (rkmNextLen mL cL) 4)
      (Nat.div (rkmNextLen mL cL) 4) 0 0 (toH4K q (mkHbZ z b)) vs cs) =
      bSl z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z (tk4 q b) (q4L vs) (q4L cs) := by
    rw [bSlQ4_eq _ _ _ hr, hqr, hbz4L_toH4K, hsl]
  revert h
  cases hv : q4AP (bSlQ4 z (Nat.mul dg wdScale) (Nat.mod (rkmNextLen mL cL) 4)
      (Nat.div (rkmNextLen mL cL) 4) 0 0 (toH4K q (mkHbZ z b)) vs cs) with
  | false => intro h; dsimp only [cond] at h; cases h
  | true =>
    intro h; dsimp only [cond] at h; injection h with h'
    have hp := q4AP_pos _ hv; rw [heq] at hp; rw [← h', heq]
    unfold rkmUltraHornerStage; rw [rkmb_forceNat_eq, rkmb_forceNat_eq, ← bM0 z]
    exact bSl_sound z _ _ 0 z (tk4 q b) (q4L vs) (q4L cs) hp
private def bBind (z dg mL cL : ℕ) (h4 : HbZ4) (vs cs : Q4)
    (k : ℕ → Q4 → Option Q4) : Option Q4 :=
  fN (rkmNextLen mL cL) fun nL =>
    match bStg z dg mL cL h4 vs cs with | none => none | some out => k nL out
private theorem bBind_sound {z q dg mL cL : ℕ} {b : List ℕ} {vs cs out : Q4}
    {kB : ℕ → Q4 → Option Q4} {kU : ℕ → List ℤ → List ℤ}
    (h : bBind z dg mL cL (toH4K q (mkHbZ z b)) vs cs kB = some out)
    (hk : ∀ (mid : Q4), kB (rkmNextLen mL cL) mid = some out →
      bD z (q4L out) = kU (rkmNextLen mL cL) (bD z (q4L mid))) :
    bD z (q4L out) = (HighDForce.withForcedNat (rkmNextLen mL cL) fun nL =>
      HighDForce.withForcedList
        (rkmUltraHornerStage dg mL cL (uHb (tk4 q b)) (bD z (q4L vs)) (bD z (q4L cs)))
        (kU nL)) := by
  unfold bBind at h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h
  revert h; cases hs : bStg z dg mL cL (toH4K q (mkHbZ z b)) vs cs with
  | none => intro h; dsimp only at h; cases h
  | some mid =>
    intro h; rw [rkmb_forceNat_eq, rkmb_forceList_eq, ← bStg_sound z q dg mL cL b hs]
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
private theorem bStep_sound {z q mL cL : ℕ} {b : List ℕ} {vs out : Q4}
    (h : bStep z mL cL (toH4K q (mkHbZ z b)) vs = some out) :
    bD z (q4L out) = rkmUltraHornerT16Step mL cL (uHb (tk4 q b)) (bD z (q4L vs)) := by
  unfold bStep at h; unfold rkmUltraHornerT16Step
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  exact bStg_sound z q 1 mL _ b h
private def bSp (z q m c : ℕ) (hbz v : List ℕ) : Option (List ℕ) :=
  fH4 (toH4K q hbz) fun h4 =>
    fQ4 (toQ4 v) fun vs =>
      match bStep z m c h4 vs with | none => none | some outV => some (q4L outV)
private theorem bSp_sound (z q mL cL : ℕ) (b v out : List ℕ)
    (h : bSp z q mL cL (mkHbZ z b) v = some out) :
    bD z out = rkmUltraHornerT16Step mL cL (uHb (tk4 q b)) (bD z v) := by
  unfold bSp at h; rw [fH4e, fQ4_eq] at h; revert h
  cases hs : bStep z mL cL (toH4K q (mkHbZ z b)) (toQ4 v) with
  | none => intro h; dsimp only at h; cases h
  | some outV =>
    intro h; dsimp only at h; injection h with h'; rw [← h']
    have hstep := bStep_sound hs; rw [q4L_toQ4] at hstep; exact hstep
private theorem nxt_le (m c : ℕ) : rkmNextLen m c ≤ c + 1 := by
  unfold rkmNextLen; rw [rkmb_natMin_eq, Nat.add_eq]; exact Nat.min_le_right m (c + 1)
private theorem sl_tk : ∀ (d rem : ℕ) (p : ℤ) (n : ℕ) (hb v c : List ℤ),
    rem ≤ n → rkmUltraSlideLoopAux d rem p (tkZ n hb) v c =
      rkmUltraSlideLoopAux d rem p hb v c
  | _, 0, _, _, _, _, _, _ => rfl
  | _, rem + 1, _, 0, _, _, _, h => absurd h (Nat.not_succ_le_zero rem)
  | _, _ + 1, _, _ + 1, [], _, _, _ => rfl
  | d, rem + 1, p, n + 1, b :: hbR, v, c, h => by
    have hn : rem ≤ n := Nat.le_of_succ_le_succ h; dsimp only [tkZ]
    cases v with
    | nil => cases c with
      | nil => dsimp only [rkmUltraSlideLoopAux]; rw [sl_tk d rem _ n hbR [] [] hn]
      | cons _ cT => dsimp only [rkmUltraSlideLoopAux]; rw [sl_tk d rem _ n hbR [] cT hn]
    | cons _ vT => cases c with
      | nil => dsimp only [rkmUltraSlideLoopAux]; rw [sl_tk d rem _ n hbR vT [] hn]
      | cons _ cT => dsimp only [rkmUltraSlideLoopAux]; rw [sl_tk d rem _ n hbR vT cT hn]
private theorem stg_tk (dg mL cL n : ℕ) (hb v c : List ℤ) (hc : cL + 1 ≤ n) :
    rkmUltraHornerStage dg mL cL (tkZ n hb) v c = rkmUltraHornerStage dg mL cL hb v c := by
  unfold rkmUltraHornerStage; simp only [rkmb_forceNat_eq]
  exact sl_tk (Nat.mul dg wdScale) (rkmNextLen mL cL) (Int.ofNat 0) n hb v c
    ((nxt_le mL cL).trans hc)
private theorem bd_tk (dg mL cL k n : ℕ) (hb v c : List ℤ)
    {f1 f2 : ℕ → List ℤ → List ℤ} (hc : cL + (k + 1) ≤ n)
    (hf : ∀ l1 c1, l1 ≤ cL + 1 → f1 l1 c1 = f2 l1 c1) :
    (HighDForce.withForcedNat (rkmNextLen mL cL) fun l1 =>
      HighDForce.withForcedList (rkmUltraHornerStage dg mL cL (tkZ n hb) v c) (f1 l1)) =
    (HighDForce.withForcedNat (rkmNextLen mL cL) fun l1 =>
      HighDForce.withForcedList (rkmUltraHornerStage dg mL cL hb v c) (f2 l1)) := by
  simp only [rkmb_forceNat_eq, rkmb_forceList_eq]
  rw [stg_tk dg mL cL n hb v c (by omega)]
  exact hf (rkmNextLen mL cL) _ (nxt_le mL cL)
private theorem step_tk (mL cL n : ℕ) (hb v : List ℤ) (hc : cL + 16 ≤ n) :
    rkmUltraHornerT16Step mL cL (tkZ n hb) v = rkmUltraHornerT16Step mL cL hb v := by
  unfold rkmUltraHornerT16Step
  refine bd_tk 16 mL cL 15 n hb v v hc fun l1 c1 h1 => ?_
  refine bd_tk 15 mL l1 14 n hb v c1 (by omega) fun l2 c2 h2 => ?_
  refine bd_tk 14 mL l2 13 n hb v c2 (by omega) fun l3 c3 h3 => ?_
  refine bd_tk 13 mL l3 12 n hb v c3 (by omega) fun l4 c4 h4 => ?_
  refine bd_tk 12 mL l4 11 n hb v c4 (by omega) fun l5 c5 h5 => ?_
  refine bd_tk 11 mL l5 10 n hb v c5 (by omega) fun l6 c6 h6 => ?_
  refine bd_tk 10 mL l6 9 n hb v c6 (by omega) fun l7 c7 h7 => ?_
  refine bd_tk 9 mL l7 8 n hb v c7 (by omega) fun l8 c8 h8 => ?_
  refine bd_tk 8 mL l8 7 n hb v c8 (by omega) fun l9 c9 h9 => ?_
  refine bd_tk 7 mL l9 6 n hb v c9 (by omega) fun la ca ha => ?_
  refine bd_tk 6 mL la 5 n hb v ca (by omega) fun lb cb hb1 => ?_
  refine bd_tk 5 mL lb 4 n hb v cb (by omega) fun lc cc hc1 => ?_
  refine bd_tk 4 mL lc 3 n hb v cc (by omega) fun ld cd hd1 => ?_
  refine bd_tk 3 mL ld 2 n hb v cd (by omega) fun le ce he1 => ?_
  refine bd_tk 2 mL le 1 n hb v ce (by omega) fun lf cf hf1 => ?_
  exact stg_tk 1 mL lf n hb v cf (by omega)
private theorem it1_eq (mL cL : ℕ) (hb v : List ℤ) :
    muxUltraIterFullT16Rkm 1 mL cL hb v = rkmUltraHornerT16Step mL cL hb v := by
  unfold muxUltraIterFullT16Rkm; dsimp only; rw [rkmb_forceList_eq, rkmb_forceNat_eq]; rfl
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
        fN (Nat.sub (Nat.add d 1) sLo) fun remMax =>
          fL (bPZ z padL us) fun vns => fN (bNL vns) fun curLen =>
            fN (Nat.add (Nat.div curLen 4) 5) fun qH =>
              match bSp z qH remMax curLen (dr2 kD hbz) vns with
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
    set vns := bPZ z padL us; set qH := Nat.add (Nat.div (bNL vns) 4) 5
    rw [d2Eq] at h; revert h
    cases hi : bSp z qH remMax (bNL vns) (mkHbZ z (drN kD b)) vns with
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
      have hq : bNL vns + 16 ≤ 4 * qH := by
        have hdm := Nat.div_add_mod (bNL vns) 4
        have hml := Nat.mod_lt (bNL vns) (Nat.succ_pos 3)
        dsimp only [qH]; rw [Nat.add_eq, ndiv]; omega
      rw [ho, hu, hd, twEq z thr sLo out dropAcc]
      rw [bSp_sound z qH remMax (bNL vns) (drN kD b) vns out hi]
      rw [uHb_tk4 qH (drN kD b), step_tk remMax (bNL vns) (4 * qH) _ _ hq, ← it1_eq, hkd]
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
private def uNatApp : List ℕ → List ℕ → List ℕ
  | [], acc => acc
  | n :: ns, acc => n :: uNatApp ns acc
private def uNatCatN : List (List ℕ) → List ℕ
  | [] => []
  | ns :: nss => uNatApp ns (uNatCatN nss)
private def pzigApp : List ℕ → List ℤ → List ℤ
  | [], acc => acc
  | w :: ws, acc =>
    (match Nat.mod w 2 with
      | 0 => primOfNatForced (Nat.div w 2)
      | _ => primNegSuccForced (Nat.div w 2)) :: pzigApp ws acc
private def pzigCat : List (List ℕ) → List ℤ
  | [] => []
  | ws :: wss => pzigApp ws (pzigCat wss)
private theorem drHbSub {w0 k0 wc : ℕ} {hb : List ℤ} {b : List ℕ}
    (hhb : uHb b = rkmDropInts w0 hb) (hw : w0 + k0 = wc) :
    uHb (drN k0 b) = rkmDropInts wc hb := by
  rw [dnEq k0 b, hhb, ← dr_add w0 k0 hb, hw]
private def rkmPhb_w512_s0 : List ℕ := uNatCatN
  [
   [75219391165782,106220445806945,129902054065371,149777512285582,167209827659047,
    182899093049997,197261813980467,210569765790353,223011999719988,234726362531678,
    245817067674145,256365195077204,266435315749814,276079858383915,285342093244036,
    294258233773836,302858955383339,311170517664568,319215609764180,327013998120129,
    334583030295911,341938032183821,349092624946354,356058980685431,362848030735125,
    369469636894484,375932733361538,382245445277954,388415188434118,394448753673482,
    400352378774843,406131810013479,411792355158747,417338929322369,422776094803459,
    428108095865204,433338889210650,438472170791271,443511399474438,448459818008920,
    453320471656690,458096224801407,462789775796250,467403670274365,471940313112464,
    476401979210781,480790823229710,485108888404165,489358114540461,493540345286673,
    497657334755738,501710753570480,505702194391214,509633176979141,513505152842428,
    517319509506344,521077574444064,524780618700589,528429860238666,532026467032360,
    535571559931243,539066215315693,542511467561666,545908311331438,549257703705149,
    552560566166481,555817786454541,559030220292823,562198693005104,565324001027214,
    568406913322781,571448172710322,574448497108399,577408580704950,580329095056385,
    583210690121545,586053995235201,588859620025364,591628155278340,594360173755126,
    597056230962469,599716865881631,602342601657672,604933946251839,607491393059471,
    610015421495596,612506497550303,614965074315755,617391592486613,619786480835487,
    622150156664936,624483026237410,626785485184446,629057918896333,631300702893370,
    633514203179780,635698776581257,637854771067072,639982526057585,642082372717978,
    644154634238941,646199626105040,648217656351392,650209025809299,652174028341384,
    654112951066801,656026074577016,657913673142635,659776014911736,661613362100131,
    663425971173946,665214093024908,666977973138685,668717851756617,670433964031147,
    672126540175256,673795805606189,675441981083714,677065282843194,678665922723690,
    680244108291323,681800042958119,683333926096516,684845953149754,686336315738295,
    687805201762476,689252795501538,690679277709188],
   [692084825705854,693469613467749,694833811712905,696177587984277,697501106730053,
    698804529381280,700088014426909,701351717486373,702595791379788,703820386195869,
    705025649357667,706211725686186,707378757461983,708526884484826,709656244131469,
    710766971411631,711859199022243,712933057400021,713988674772433,715026177207120,
    716045688659820,717047331020859,718031224160251,718997485971465,719946232413900,
    720877577554118,721791633605874,722688510968989,723568318267104,724431162384354,
    725277148500994,726106380128026,726918959140837,727714985811909,728494558842613,
    729257775394113,730004731117434,730735520182693,731450235307535,732148967784798,
    732831807509432,733498843004684,734150161447597,734785848693810,735405989301719,
    736010666555981,736599962490414,737173957910287,737732732414028,738276364414378,
    738804931158979,739318508750444,739817172165908,740300995276070,740770050863759,
    741224410642018,741664145271732,742089324378810,742500016570931,742896289453871,
    743278209647415,743645842800872,743999253608205,744338505822776,744663662271732,
    744974784870024,745271934634084,745555171695161,745824555312325,746080143885151,
    746321994966085,746550165272512,746764710698515,746965686326353,747153146437651,
    747327144524311,747487733299156,747634964706314,747768889931333,747889559411060,
    747997022843261,748091329196009,748172526716838,748240662941661,748295784703471,
    748337938140823,748367168706094,748383521173545,748387039647167,748377767568333,
    748355747723250,748321022250222,748273632646718,748213619776262,748141023875138,
    748055884558914,747958240828800,747848131077826,747725593096861,747590664080452,
    747443380632523,747283778771891,747111893937646,746927760994361,746731414237164,
    746522887396648,746302213643646,746069425593857,745824555312325,745567634317789,
    745298693586883,745017763558210,744724874136272,744420054695277,744103334082811,
    743774740623377,743434302121810,743082045866571,742717998632902,742342186685875,
    741954635783303,741555371178540,741144417623158,740721799369502,740287540173134,
    739841663295151,739384191504396,738915147079546],
   [738434551811090,737942427003193,737438793475442,736923671564485,736397081125554,
    735859041533877,735309571685981,734748690000879,734176414421147,733592762413895,
    732997750971625,732391396612973,731773715383347,731144722855453,730504434129710,
    729852863834551,729190026126618,728515934690842,727830602740414,727134043016639,
    726426267788682,725707288853203,724977117533868,724235764680755,723483240669646,
    722719555401191,721944718299970,721158738313427,720361623910689,719553383081264,
    718734023333620,717903551693642,717061974702958,716209298417153,715345528403846,
    714470669740643,713584727012964,712687704311729,711779605230923,710860432865020,
    709930189806267,708988878141839,708036499450842,707073054801184,706098544746289,
    705112969321672,704116328041362,703108619894168,702089843339792,701059996304784,
    700019076178334,698967079807903,697904003494675,696829842988853,695744593484770,
    694648249615824,693540805449229,692422254480586,691292589628258,690151803227549,
    688999887024692,687836832170626,686662629214571,685477268097382,684280738144694,
    683073028059838,681854125916529,680624019151321,679382694555819,678130138268645,
    676866335767156,675591271858892,674304930672767,673007295649984,671698349534662,
    670378074364187,669046451459256,667703461413618,666349084083504,664983298576733,
    663606083241489,662217415654747,660817272610361,659405630106781,657982463334397,
    656547746662506,655101453625878,653643556910914,652174028341384,650692838863735,
    649199958531949,647695356491938,646179000965465,644650859233572,643110897619507,
    641559081471112,639995375142686,638419741976278,636832144282402,635232543320160,
    633620899276742,631997171246281,630361317208059,628713294004015,627053057315549,
    625380561639591,623695760263909,621998605241628,620289047364929,618567036137908,
    616832519748548,615085445039781,613325757479616,611553401130265,609768318616271,
    607970451091564,606159738205424,604336118067303,602499527210457,600649900554345,
    598787171365751,596911271218561,595022129952160,593119675628380,591203834486943,
    589274530899335,587331687321050,585375224242130],
   [583405060135927,581421111406018,579423292331192,577411515008408,575385689293668,
    573345722740675,571291520537208,569222985439091,567140017701655,565042515008576,
    562930372397972,560803482185621,558661733885175,556505014125221,554333206563040,
    552146191794905,549943847262748,547726047157014,545492662315523,543243560118131,
    540978604376970,538697655222069,536400568982080,534087198059891,531757390802826,
    529410991367169,527047839576695,524667770774881,522270615670470,519856200175994,
    517424345238892,514974866664779,512507574932442,510022275000074,507518766102238,
    504996841537026,502456288442814,499896887564011,497318413005109,494720631972338,
    492103304502145,489466183175672,486809012818350,484131530183643,481433463619921,
    478714532719354,475974447947618,473212910253135,470429610654443,467624229804195,
    464796437528134,461945892337297,459072240911510,456175117552091,453254143601493,
    450308926827428,447339060768766,444344124040294,441323679593118,438277273927224,
    435204436252346,432104677592960,428977489832785,425822344693727,422638692643694,
    419425961727141,416183556311563,412910855742442,409607212898359,406271952637066,
    402904370122305,399503729020005,396069259551188,392600156387436,389095576373086,
    385554636056421,381976409009903,378359922917037,374704156400530,371008035563136,
    367270430208746,363490149706851,359665938458412,355796470915154,351880346097376,
    347916081547175,343902106644391,339836755201250,335718257238284,331544729828141,
    327314166874894,323024427673605,318673224067467,314258105986569,309776445111909,
    305225416358875,300601976813650,295902841680890,291124456707573,286262966430891,
    281314177450416,276273515737265,271135976752744,265896066838696,260547733937329,
    255084285165920,249498288063584,243781451374395,237924479933081,231916896427359,
    225746820300082,219400690479545,212862913445689,206115410483622,199137026410993,
    191902744164086,184382621140635,176540316417929,168330998317714,159698280360046,
    150569569757876,140848690111636,130403527588053,119043855746454,106477683140946,
    92213431808111,75292525110103,53240057777205]]
private def rkmC_w512_s0_1 : List ℤ := pzigCat
  [
   [509772244,1942618118,5978072404,16803003540,42434951268,99155614102,216515845494,
    444914751266,866132245470,1605439619010,2844813009584,4835768287250,7908876697604,
    12477009817756,19029312918796,28112834881876,40300066578424,56142896610762,76115467970956,
    100550278620914,129574038831876,163051496653902,200545620892458,241301171183170,
    284256401006708,328084719614952,371264611081668,412172374281720,449189114278086,
    480811542039074,505755701449282,523043610195566,532064804687766,532607710669304,
    524859237834490,509374469521056,487021257396104,458906598406856,426292748452502,
    390511138873086,352881412622158,314641463465198,276892496027734,240561122450858,
    206378646357128,174876151928124,146392914719904,121095000929064,99000696234138,
    80009529067132,63932080096774,50518285424908,39482756208094,30525877134748,23350864477754,
    17675706022246,13242194643340,9819956342162,7209223528314,5240380468308,3772015112506,
    2688968688978,1898805638982,1328211954032,920378932560,632044423910,430181507424,
    290096773286,193566345970,128085669658,84103805368,54681560328,35308972704,22638386808,
    14176663538,8511557542,4861292226,2492905282,860602914,205148028]]
private def rkmC_w512_s0_2 : List ℤ := pzigCat
  [
   [411570068,985230574,1971177782,3720269932,6851151006,12221941814,21353743814,36393588846,
    60964553522,100169801698,161761946040,256622674908,399979246944,612948809384,923700183740,
    1369776656842,1999588470492,2874611676756,4071088169068,5681945867476,7817400483998,
    10605989731970,14193617087396,18741539832430,24423462068020,31420346243532,39913356077802,
    50076502577392,62066013067370,76010072465040,91997339263622,110065620917396,130191569205046,
    152281676890858,176165920531666,201594835607368,228239190390432,255695266211576,
    283492847185668,311108535844930,337981859079668,363534095325112,387190325854780,
    408400864362232,426663198236080,441541405287964,452684528036298,459839789541466,
    462861626827984,461715871107124,456480122464764,447337886977370,434568077495828,
    418531749005790,399656919861420,378418960535794,355321809603224,330880384279044,
    305601437125780,279968424648398,254428374500794,229381246919146,205171577930000,
    182085191596866,160346778540300,140120909342162,121515560677066,104586469124652,
    89342778653780,75755171444742,63761560613664,53274986143416,44190892201882,36392468348486,
    29756371633454,24158336527498,19475568700336,15590907419018,12394630738976,9785700509544,
    7673157935048,5976062371042,4622815838172,3552198555106,2711378771832,2055820899746,
    1548588010464,1158818761894,861349846218,636250035542,466801738562,340360268592,246699509994,
    177596909870,127207846164,90512441850,63999417964,44884230332,31116989950,21338048530,
    14288316470,9095581568,5614327500,3065182794,1410355804,480277584]]
private def rkmC_w512_s0_3 : List ℤ := pzigCat
  [
   [326680580,800729512,1483194410,2508418764,4007184816,6417510924,9963206934,15541607996,
    23840896658,36306099834,54755365956,81635445260,120310999956,175550662754,253341072964,
    361999577740,511988037766,716830557498,993699080144,1364435933914,1855354181004,
    2498659225004,3333621611226,4406939197764,5772105412762,7491590730718,9636726518176,
    12286570283974,15527693013148,19454136304192,24164505658404,29760893756412,36345993753286,
    44019150058626,52873259014066,62990837124136,74438406355550,87262379175742,101484877035408,
    117097703271108,134060055503834,152294421110510,171684179433914,192073182555832,
    213265453123748,235026835157942,257089582522498,279155749300726,300904376238960,
    321999051504082,342096287137310,360855120104334,377947010095046,393064934205930,
    405933505676418,416316635413202,424024809140722,428921704532766,430926705032636,
    430018356939624,426233876518372,419666519172644,410463576601604,398819616482566,
    384970391516774,369185120449984,351757848179986,332998695756334,313225072491730,
    292752961452300,271889592041642,250925614973456,230130160807252,209745673890936,
    189984032226670,171025431731942,153015930951434,136068710339486,120265058006974,
    105655503029394,92263503131484,80087484401300,69104921027244,59275501095864,50544618040832,
    42846902518782,36109335811014,30254162571914,25201824043450,20871979208628,17186753523946,
    14071364619514,11454987091816,9272440146492,7463224237106,5973215670764,4754007885318,
    3762450726750,2961177658632,2317469064506,1803735119204,1396112108970,1074557527790,
    822645142694,626294634936,474335901374,357276205102,267678347922,199613449702,148004955072,
    109234414982,80048917048,58268550394,42096389738,30007959920,21150866448,14475870000,
    9619190156,6073994496,3515789406,1869636870,729441274,204507032]]
private def rkmC_w512_s0_4 : List ℤ := pzigCat
  [
   [267806962,400785562,640797542,1280473806,1951602530,2840980958,4301440676,6240531660,
    9472938846,14003703404,20344790620,29527000260,42437819480,60565044480,85861688818,
    120480567602,167897327010,232318814282,318742406592,434295228444,587255789290,788032225190,
    1049764305418,1388016477878,1822235889566,2374891848700,3073053276774,3948278267128,
    5036789126100,6380482546814,8026608861868,10027383740874,12440951486940,15330187607356,
    18762236138476,22808133385638,27540727140444,33034205827308,39361379450488,46591897825302,
    54790313970086,64012333996702,74303447760290,85694866109474,98200813474834,111816740618586,
    126515421759298,142246013668378,158931949960044,176469811997820,194729521721322,
    213554261344942,232762733198324,252150635936780,271494368505382,290555108104742,
    309082823952520,326822744116556,343520251678464,358927420244886,372809184474852,
    384948904981634,395154850077296,403264395246118,409148987862952,412717111890552,
    413916475132048,412736098308188,409205398494606,403393734289458,395407760970880,
    385388430845084,373507287275822,359960678917840,344965374234880,328752379367212,
    311561483127044,293635597253130,275214645668742,256531468259058,237806502058438,
    219244448152368,201031006981776,183330214307884,166283629782518,150008589252730,
    134598834466656,120124624284468,106633779172234,94153690492696,82692346879894,72241368162136,
    62777660562500,54266099608744,46662064118888,39913056617700,33961718317110,28746948874138,
    24206254877790,20277072926306,16897672544980,14008897968196,11554081537084,9480481199936,
    7739173074226,6285301241732,5078593448908,4082530904950,3265159845702,2598117882478,
    2056791781352,1620088384910,1269567461116,989986574592,768066357130,592939007846,
    455546333918,348200777614,264979114338,200595781126,151152509680,113300165878,84350950674,
    62439679744,45707993466,33168187902,23697712474,16604873734],
   [11418779402,7487864992,4742460094,2689180110,1312090868,480901988]]
private def rkmPhb_w512_s1 : List ℕ := uNatCatN
  [
   [516360804661996,518801132815961,521217967045389,523611652819107,525982526230266,
    528330914354949,530657135593229,532961499993722,535244309562595,537505858557948,
    539746433770389,541966314790604,544165774264649,546345078137642,548504485886500,
    550644250742317,552764619902948,554865834736313,556948130974917,559011738902053,
    561056883530107,563083784771392,565092657601861,567083712218096,569057154187875,
    571013184594660,572952000176294,574873793458188,576778752881268,578667062924932,
    580538904225255,582394453688658,584233884601262,586057366734121,587865066444525,
    589657146773552,591433767540028,593195085431082,594941254089406,596672424197410,
    598388743558372,600090357174732,601777407323644,603450033629907,605108373136388,
    606752560372036,608382727417588,609999003969065,611601517399156,613190392816554,
    614765753123353,616327719070562,617876409311828,619411940455424,620934427114578,
    622443981956214,623940715748148,625424737404815,626896154031576,628355070967658,
    629801591827785,631235818542537,632657851397498,634067789071223,635465728672080,
    636851765774006,638225994451201,639588507311822,640939395530694,642278748881082,
    643606655765551,644923203245950,646228477072555,647522561712382,648805540376727,
    650077495047928,651338506505399,652588654350949,653828017033414,655056671872625,
    656274695082724,657482161794871,658679146079338,659865720967024,661041958470407,
    662207929603952,663363704403983,664509351948052,665644940373808,666770536897386,
    667886207831330,668992018602069,670088033766952,671174317030862,672250931262415,
    673317938509767,674375400016031,675423376234316,676461926842411,677491110757106,
    678510986148179,679521610452046,680523040385086,681515331956658,682498540481810,
    683472720593694,684437926255690,685394210773255,686341626805500,687280226376499,
    688210060886348,689131181121967,690043637267668,690947478915483,691842755075259,
    692729514184537,693607804118207,694477672197960,695339165201526,696192329371717,
    697037210425271,697873853561514,698702303470828,699522604342944,700334799875061,
    701138933279791,701935047292940,702723184181125],
   [703503385749234,704275693347737,705040147879835,705796789808476,706545659163219,
    707286795546965,708020238142551,708746025719205,709464196638883,710174788862476,
    710877839955886,711573387096000,712261467076524,712942116313728,713615370852056,
    714281266369648,714939838183737,715591121255959,716235150197550,716871959274451,
    717501582412312,718124053201404,718739404901440,719347670446303,719948882448689,
    720543073204660,721130274698120,721710518605200,722283836298571,722850258851672,
    723409817042868,723962541359524,724508462002016,725047608887661,725580011654585,
    726105699665514,726624702011508,727137047515618,727642764736488,728141881971888,
    728634427262192,729120428393787,729599912902432,730072908076552,730539440960483,
    730999538357652,731453226833715,731900532719629,732341482114683,732776100889471,
    733204414688821,733626448934670,734042228828893,734451779356089,734855125286313,
    735252291177773,735643301379475,736028180033828,736406951079208,736779638252477,
    737146265091469,737506854937422,737861430937389,738210016046595,738552633030766,
    738889304468418,739220052753112,739544900095668,739863868526351,740176979897021,
    740484255883245,740785717986387,741081387535651,741371285690108,741655433440678,
    741933851612096,742206560864832,742473581696998,742734934446216,742990639291458,
    743240716254865,743485185203534,743724065851279,743957377760365,744185140343220,
    744407372864117,744624094440839,744835324046306,745041080510195,745241382520523,
    745436248625213,745625697233641,745809746618151,745988414915555,746161720128614,
    746329680127490,746492312651184,746649635308949,746801665581689,746948420823333,
    747089918262190,747226175002289,747357208024696,747483034188818,747603670233681,
    747719132779199,747829438327421,747934603263758,748034643858203,748129576266523,
    748219416531444,748304180583812,748383884243747,748458543221773,748528173119940,
    748592789432926,748652407549125,748707042751726,748756710219769,748801425029194,
    748841202153874,748876056466632,748906002740251,748931055648462,748951229766926,
    748966539574205,748976999452711,748982623689650],
   [748983426477955,748979421917204,748970624014524,748957046685489,748938703755002,
    748915608958170,748887775941164,748855218262071,748817949391734,748775982714582,
    748729331529449,748678009050383,748622028407446,748561402647504,748496144735006,
    748426267552752,748351783902660,748272706506509,748189048006689,748100820966928,
    748008037873021,747910711133543,747808853080560,747702475970320,747591591983951,
    747476213228139,747356351735802,747232019466759,747103228308384,746969990076256,
    746832316514808,746690219297954,746543710029721,746392800244869,746237501409505,
    746077824921684,745913782112016,745745384244249,745572642515864,745395568058643,
    745214171939252,745028465159795,744838458658384,744644163309681,744445589925455,
    744242749255113,744035651986239,743824308745120,743608730097271,743388926547948,
    743164908542661,742936686467675,742704270650517,742467671360461,742226898809022,
    741981963150436,741732874482141,741479642845246,741222278225000,740960790551252,
    740695189698913,740425485488403,740151687686101,739873806004788,739591850104083,
    739305829590877,739015754019760,738721632893448,738423475663199,738121291729230,
    737815090441128,737504881098253,737190672950142,736872475196908,736550296989630,
    736224147430747,735894035574439,735559970427010,735221960947265,734880016046885,
    734534144590795,734184355397530,733830657239597,733473058843832,733111568891760,
    732746196019937,732376948820307,732003835840539,731626865584371,731246046511944,
    730861387040139,730472895542906,730080580351590,729684449755254,729284512001002,
    728880775294294,728473247799263,728061937639021,727646852895971,727228001612112,
    726805391789335,726379031389732,725948928335881,725515090511148,725077525759972,
    724636241888152,724191246663137,723742547814301,723290153033226,722834069973978,
    722374306253381,721910869451287,721443767110843,720973006738761,720498595805579,
    720020541745923,719538851958762,719053533807668,718564594621070,718072041692500,
    717575882280846,717076123610600,716572772872097,716065837221761,715555323782341,
    715041239643154,714523591860314,714002387456969],
   [713477633423530,712949336717902,712417504265706,711882142960509,711343259664044,
    710800861206428,710254954386385,709705545971460,709152642698233,708596251272534,
    708036378369649,707473030634535,706906214682022,706335937097018,705762204434716,
    705185023220791,704604399951603,704020341094392,703432853087476,702841942340444,
    702247615234348,701649878121897,701048737327642,700444199148166,699836269852269,
    699224955681153,698610262848603,697992197541170,697370765918349,696745974112758,
    696117828230312,695486334350400,694851498526060,694213326784145,693571825125500,
    692926999525124,692278855932345,691627400270981,690972638439503,690314576311204,
    689653219734356,688988574532372,688320646503967,687649441423311,686974965040190,
    686297223080158,685616221244693,684931965211348,684244460633902,683553713142511,
    682859728343857,682162511821295,681462069134996,680758405822098,680051527396846,
    679341439350736,678628147152653,677911656249018,677191972063922,676469099999264,
    675743045434890,675013813728729,674281410216926,673545840213977,672807109012858,
    672065221885163,671320184081228,670572000830264,669820677340484,669066218799229,
    668308630373098,667547917208069,666784084429626,666017137142880,665247080432695,
    664473919363803,663697658980932,662918304308920,662135860352834,661350332098089,
    660561724510565,659770042536721,658975291103709,658177475119491,657376599472951,
    656572669034004,655765688653710,654955663164386,654142597379712,653326496094841,
    652507364086506,651685206113129,650860026914928,650031831214016,649200623714513,
    648366409102647,647529192046855,646688977197888,645845769188910,644999572635602,
    644150392136258,643298232271886,642443097606307,641584992686251,640723922041456,
    639859890184762,638992901612208,638122960803124,637250072220230,636374240309725,
    635495469501381,634613764208636,633729128828683,632841567742562,631951085315252,
    631057685895754,630161373817188,629262153396873,628360028936421,627455004721818,
    626547085023514,625636274096506,624722576180426,623805995499620,622886536263236,
    621964202665306,621038998884828,620110929085845],
   [619179997417532,618246208014271,617309564995735,616370072466965,615427734518450,
    614482555226204,613534538651845,612583688842674,611630009831747,610673505637954,
    609714180266095,608752037706955,607787081937375,606819316920331,605848746605005,
    604875374926858,603899205807701,602920243155770,601938490865795,600953952819074,
    599966632883538,598976534913826,597983662751353,596988020224376,595989611148068,
    594988439324583,593984508543121,592977822580000,591968385198719,590956200150027,
    589941271171987,588923601990040,587903196317072,586880057853480,585854190287229,
    584825597293926,583794282536871,582760249667131,581723502323595,580684044133038,
    579641878710182,578597009657758,577549440566567,576499175015535,575446216571782,
    574390568790673,573332235215881,572271219379444,571207524801826,570141154991969,
    569072113447359,568000403654073,566926029086846,565848993209117,564769299473095,
    563686951319805,562601952179151,561514305469966,560424014600069,559331082966318,
    558235513954663,557137310940201,556036477287228,554933016349293,553826931469249,
    552718225979305,551606903201079,550492966445648,549376419013599,548257264195082,
    547135505269858,546011145507348,544884188166688,543754636496772,542622493736304,
    541487763113849,540350447847877,539210551146814,538068076209092,536923026223189,
    535775404367685,534625213811303,533472457712960,532317139221809,531159261477287,
    529998827609164,528835840737582,527670303973106,526502220416766,525331593160102,
    524158425285210,522982719864784,521804479962159,520623708631360,519440408917139,
    518254583855021,517066236471346,515875369783313,514681986799019,513486090517507,
    512287683928798,511086770013944,509883351745059,508677432085368,507469013989240,
    506258100402237,505044694261147,503828798494026,502610416020242,501389549750508,
    500166202586924,498940377423019,497712077143784,496481304625715,495248062736850,
    494012354336807,492774182276821,491533549399782,490290458540275,489044912524613,
    487796914170877,486546466288951,485293571680560,484038233139305,482780453450699,
    481520235392205,480257581733270,478992495235359],
   [477724978651993,476455034728784,475182666203466,473907875805936,472630666258280,
    471351040274817,470069000562125,468784549819078,467497690736882,466208425999103,
    464916758281704,463622690253078,462326224574081,461027363898060,459726110870893,
    458422468131016,457116438309457,455808024029868,454497227908554,453184052554510,
    451868500569447,450550574547826,449230277076890,447907610736690,446582578100123,
    445255181732954,443925424193855,442593308034429,441258835799240,439922010025849,
    438582833244835,437241307979831,435897436747553,434551222057822,433202666413604,
    431851772311029,430498542239425,429142978681347,427785084112600,426424861002273,
    425062311812765,423697438999812,422330245012514,420960732293367,419588903278284,
    418214760396628,416838306071234,415459542718442,414078472748118,412695098563683,
    411309422562141,409921447134102,408531174663813,407138607529177,405743748101788,
    404346598746949,402947161823701,401545439684848,400141434676984,398735149140514,
    397326585409684,395915745812604,394502632671270,393087248301596,391669595013429,
    390249675110581,388827490890850,387403044646046,385976338662010,384547375218647,
    383116156589941,381682685043983,380246962842994,378808992243348,377368775495596,
    375926314844487,374481612528994,373034670782335,371585491831996,370134077899756,
    368680431201703,367224553948267,365766448344230,364306116588760,362843560875424,
    361378783392214,359911786321570,358442571840399,356971142120097,355497499326572,
    354021645620265,352543583156171,351063314083858,349580840547493,348096164685858,
    346609288632374,345120214515121,343628944456857,342135480575041,340639824981852,
    339141979784208,337641947083791,336139728977062,334635327555281,333128744904533,
    331619983105740,330109044234687,328595930362037,327080643553352,325563185869115,
    324043559364746,322521766090621,320997808092095,319471687409516,317943406078248,
    316412966128688,314880369586282,313345618471552,311808714800103,310269660582653,
    308728457825041,307185108528254,305639614688439,304091978296923,302542201340232,
    300990285800111,299436233653533,297880046872728],
   [296321727425194,294761277273713,293198698376376,291633992686592,290067162153112,
    288498208720040,286927134326856,285353940908428,283778630395034,282201204712374,
    280621665781590,279040015519282,277456255837522,275870388643875,274282415841412,
    272692339328729,271100160999961,269505882744799,267909506448506,266311033991934,
    264710467251539,263107808099397,261503058403220,259896220026372,258287294827885,
    256676284662471,255063191380546,253448016828235,251830762847394,250211431275625,
    248590023946288,246966542688519,245340989327243,243713365683193,242083673572919,
    240451914808806,238818091199092,237182204547875,235544256655135,233904249316745,
    232262184324487,230618063466064,228971888525117,227323661281238,225673383509984,
    224021056982894,222366683467500,220710264727339,219051802521973,217391298607000,
    215728754734066,214064172650881,212397554101232,210728900824998,209058214558160,
    207385497032820,205710749977209,204033975115704,202355174168839,200674348853320,
    198991500882039,197306631964083,195619743804752,193930838105570,192239916564297,
    190546980874942,188852032727779,187155073809355,185456105802508,183755130386373,
    182052149236402,180347164024372,178640176418398,176931188082946,175220200678845,
    173507215863303,171792235289911,170075260608665,168356293465969,166635335504655,
    164912388363991,163187453679691,161460533083933,159731628205366,158000740669122,
    156267872096831,154533024106631,152796198313177,151057396327658,149316619757804,
    147573870207900,145829149278796,144082458567920,142333799669288,140583174173516,
    138830583667831,137076029736082,135319513958753,133561037912971,131800603172519,
    130038211307848,128273863886085,126507562471047,124739308623249,122969103899918,
    121196949855001,119422848039179,117646799999872,115868807281255,114088871424269,
    112306993966625,110523176442823,108737420384156,106949727318723,105160098771439,
    103368536264047,101575041315125,99779615440098,97982260151249,96182976957729,94381767365563,
    92578632877668,90773574993855,88966595210844,87157695022271,85346875918702,83534139387637,
    81719486913524],
   [79902919977769,78084440058742,76264048631791,74441747169248,72617537140441,70791420011704,
    68963397246384,67133470304851,65301640644510,63467909719807,61632278982242,59794749880375,
    57955323859835,56114002363333,54270786830669,52425678698740,50578679401551,48729790370222,
    46879013033000,45026348815265,43171799139542,41315365425506,39457049089994,37596851547015,
    35734774207753,33870818480583,32004985771074,30137277482001,28267695013353,26396239762341,
    24522913123405,22647716488228,20770651245738,18891718782122,17010920480829,15128257722583,
    13243731885391,11357344344547,9469096472646,7578989639588,5687025212590,3793204556189,
    1897529032256]]
private def rkmC_w512_s1_1 : List ℤ := pzigCat
  [
   [239391654,573160170,846608362,1339776048,1977260888,2817305046,4115338056,5726459048,
    8091990990,11327512976,15791251404,21988461648,30206975672,41456099330,56471295316,
    76503342182,103133218340,138124741192,184204234952,244098288888,321628772692,421444462470,
    549144439858,711913746970,917711513648,1176587520202,1500269155806,1902606210290,
    2400064422714,3011122522804,3757631134048,4664148241018,5758584722118,7072330174454,
    8639697058540,10498961968682,12691231947214,15260966589004,18255339629386,21723402506814,
    25716309043478,30285420317422,35482291998160,41356954268320,47956621898938,55324882476832,
    63499133838276,72510040094612,82378991066624,93116784564168,104722293410046,117180150549116,
    130460539191102,144517052279836,159286597142162,174688830318806,190625570923264,
    206982164993176,223627207965936,240414887610758,257186317266696,273771664090892,
    289993549023844,305668997807468,320613954491496,334646018281520,347588409796298,
    359274021492046,369548111656920,378272892004070,385329545475800,390621599259826,
    394077046657926,395649384202004,395319672659720,393095723334430,389012839400542,
    383132418435678,375540262808430,366345259021198,355675655170860,343677281088912,
    330509412053744,316341577103328,301350348225322,285714818942848,269614335392990,
    253224093831430,236712858435656,220240212057874,203953733419080,187988138199368,
    172462717178598,157481293535412,143131272980606,129483347039672,116592493087932,
    104497556637596,93223131261790,82780012252070,73166665341100,64371027446708,56371232423822,
    49138101482626,42635776439998,36823669528832,31657826597622,27091650226066,23077887024158,
    19568677313158,16517169444742,13877797743746,11606877044366,9663287028850,8008492582744,
    6606712036522,5425608701522,4435189718984,3609124092434,2923584279110,2357302955744,
    1892290262950,1512025208418,1202776462020,952564111512,751005206640,589566292082,
    460644868602],
   [358453222066,277617695308,213906653942,164070757018,125120263608,95059834890,71693405524,
    53663308868,39829359412,29138370256,21124268318,14887434442,10212570058,6657880304,
    3965812454,2164137834,859106144,243867550]]
private def rkmC_w512_s1_2 : List ℤ := pzigCat
  [
   [284672526,560979120,1025989726,1379808268,1994036052,2778721438,3943357398,5671283786,
    7787199368,10793326724,14734134566,20156741748,27550262452,37253402954,50307066468,
    67378194270,89909504522,119381064328,157535772578,207023899814,270473634930,351774046424,
    455199404418,585987010246,750756225838,956827678412,1213581458830,1531508093612,
    1923127084700,2403129747400,2987963249068,3697106018172,4552010250568,5577236429144,
    6800153483044,8250737611816,9962415941316,11970839174796,14314800117866,17035322336382,
    20175305422088,23779631387542,27893534705084,32562960817112,37832893198194,43746595265160,
    50344812660008,57663689025874,65734479503750,74581325271978,84220333417546,94658314028046,
    105890811454622,117901849639668,130661805510800,144127425284254,158240674783072,
    172928534415462,188103115890292,203661798162984,219487960638282,235452439253720,
    251414333441738,267223671345342,282722981720518,297749879996726,312140422819816,
    325730895404842,338362267790068,349882234853574,360148523996178,369032528465276,
    376420538362466,382217756109390,386349264869250,388761791789114,389425538112350,
    388333649119278,385503434315862,380975110315126,374811310054422,367095587976830,
    357930163140068,347434539852198,335741717991074,322996494601172,309352045013724,
    294966573434204,280001194688964,264616021123710,248968307835774,233209190942456,
    217481794098098,201919585105000,186643840865122,171763597579858,157373863396802,
    143555604098028,130375511032542,117885739975432,106125291139068,95119542502890,
    84882046250742,75415230045086,66711444759750,58754769865254,51521307956224,44981589281296,
    39101044880762,33841425362576,29162143098302,25020604751646,21374198853620,18180043724154,
    15396269443588,12982402913182,10899487896944,9111295920764,7583482174526,6284632454886,
    5185759245010,4260405692732,3485140561452,2838541319830,2302072235912,1859014774560,
    1494793705878,1196914385748],
   [954202376530,757590136918,598883928952,471422947850,369557698792,288334822408,224073207530,
    173234733984,133344753874,102128415810,77707059966,58828781400,44040884316,32690187712,
    23866304412,17056877640,11932207908,7925975480,5064804290,2884310908,1408669060,515748276]]
private def rkmC_w512_s1_3 : List ℤ := pzigCat
  [
   [414659830,777564460,1180343698,1709961594,2465683828,3398797590,4733882272,6507194188,
    8872423704,12201770760,16510779340,22421075682,30206426982,40421941590,54027948338,
    71569869020,94592888328,124340629426,162591491990,211871714866,274478353842,354135703910,
    454689737232,580940457178,739006874746,935453831480,1178766019482,1478421041352,
    1845625845124,2293473523416,2836691841858,3492527756050,4280012760402,5221063571932,
    6339875667588,7663090456956,9220433561112,11043492113470,13166848713710,15627135883896,
    18462879021964,21714560747982,25423346851278,29631408078432,34380296863852,39710815029006,
    45661957838730,52269316628356,59565057910428,67575630306058,76321319733668,85814792506732,
    96059698724356,107050139484584,118768618251298,131186234163120,144261196435408,
    157938393441480,172149654898766,186812922514812,201833504603210,217103779451074,
    232504763422574,247907440275494,263173695359192,278159235161012,292714796501146,
    306689308588514,319932061187968,332295201445380,343637260920078,353824782421508,
    362735880660282,370262033205972,376310485446674,380806501391754,383694011922610,
    384937872956382,384523691176360,382458618582376,378771103129628,373509721324396,
    366743100652898,358557362530304,349055111841550,338352884097324,326578696294722,
    313870208205492,300371019138498,286229009916866,271592947773076,256610301995776,
    241425149245860,226175164679934,210990740060466,195992353113610,181289973573750,
    166981861570488,153153398115660,139877554219096,127213738175724,115209011636450,
    103897908870580,93303070370378,83436551616954,74299816749480,65885929580296,58179734877704,
    51159485353994,44798028318086,39063265493434,33920264223122,29331163139662,25256981731448,
    21658012610738,18494319427012,15727084996362,13318056251518,11231096386210,9431691816742,
    7887492051574,6568756284264,5447593163852,4499106843458,3700271810710,3030632690196,
    2471996790614,2007896465012],
   [1624359350546,1308596971152,1049935916976,838976005982,667550563112,529089804856,
    417487754016,328152769184,256828728792,200103996260,155307431194,119819014648,92053037528,
    70186522872,53118509168,39874623638,29469482760,21567200192,15335196180,10638739922,
    7047274230,4282101196,2395722416,972730760,281688774]]
private def rkmC_w512_s1_4 : List ℤ := pzigCat
  [
   [371486354,681750420,1163662090,1587242572,2283384638,3122468996,4306958024,5958635636,
    8072611018,11102552062,14959144546,20159488996,27073675886,36058005522,47963184282,
    63335449796,83417878538,109290592440,142509768744,185168013486,239278538048,307937521408,
    394412007268,502937116800,638543087196,806943282472,1015435524912,1271918563608,
    1586093638762,1969087938946,2433611174436,2994576511270,3668367923390,4474082324462,
    5432694112728,6567557273086,7904691757774,9472107379026,11300719881600,13423178362106,
    15874514149988,18691644134140,21912598311428,25576901634918,29723985038550,34393534795150,
    39624062745948,45452115875616,51911929840406,59033468044978,66842402161166,75358050335634,
    84592773538414,94551013669770,105227519292098,116607397531570,128664195303516,
    141360071074756,154644926589470,168455785364240,182717579910936,197342323601268,
    212230709454188,227272145958746,242346032523298,257323647812814,272068949788914,
    286441643530434,300298266064316,313495149462186,325890884498790,337348267906478,
    347737786930738,356938857773888,364843138461966,371356194643734,376399285401230,
    379911609818420,381850415997260,382193037399262,380936465663322,378097787787032,
    373714013456212,367840438510518,360550629319020,351933778046240,342093744684928,
    331146691090242,319218411463666,306442835889472,292958393621096,278906719283032,
    264429483905518,249666226088442,234752664955816,219817752276608,204983218106996,
    190361039176440,176052957982886,162149550526372,148729035488146,135858061454946,
    123590446024240,111968483649368,101022790109104,90772840917810,81228429544178,72389410695622,
    64247957606866,56788587686542,49989732061414,43824965227078,38263223316412,33270979653484,
    28811891932114,24848623883596,21343204843752,18257418931818,15554269845284,13197203977746,
    11151757787332,9384942442956,7865772907948,6565800340116,5458212222460,4519144854534,
    3726407309544,3060267357044],
   [2503152108630,2039050317632,1654446456064,1336860628712,1075929872254,862482687940,
    688499732086,547561425412,433584406016,342048363728,268692983492,210116294192,163678780322,
    126730236482,97729394694,74810608590,56873782928,42920344168,31909616326,23512949912,
    16833208180,11754971668,7828602654,4773857704,2675471340,1086174624,314218926]]
private def rkmC_w512_s1_5 : List ℤ := pzigCat
  [
   [392596402,732397976,1014846828,1582607094,2163060502,3024933324,4189093114,5702327428,
    7903885908,10624062222,14376913228,19279211734,25718213062,34294229044,45352112808,
    59958583640,78736077612,102935425228,134012928430,173565120516,224042965848,287738845790,
    368069027198,468768140048,594310409948,750328104496,942929158530,1179998967692,1470166072404,
    1823711850852,2252583078138,2770098103008,3392038384520,4135541143670,5020323675870,
    6068176387740,7303038863088,8751622861284,10442311626102,12406347075372,14676678895574,
    17288217183912,20277649470402,23682311362342,27540916481652,31891757378986,36772932749812,
    42221187460382,48270785068298,54953494855008,62296358647096,70321822550804,79045814734126,
    88476949845380,98615955997404,109453681525400,120971439649094,133139061818488,
    145915080494876,159246236842048,173066700945122,187299169086796,201853863977980,
    216630290747574,231517499197238,246395233307512,261136038049714,275605774474502,
    289666873731288,303179399904806,316003876920574,328003776420242,339047101370956,
    349010012618542,357777861104976,365248424514374,371333447131408,375960092131976,
    379073263703412,380635434564108,380628716897630,379054267507740,375932574585026,
    371303364072434,365223764358454,357768450437916,349026860764772,339102311079746,
    328109731813548,316172973163834,303423551651436,289996922600532,276031388796814,
    261664983111230,247033396460462,232268503799796,217495356524040,202831943265440,
    188386606399592,174257701198546,160532763773178,147287289300408,134585664498236,
    122479748249200,111010275130290,100206634856394,90087408007564,80661900065768,71929740077292,
    63883222710872,56507162779922,49780473305406,43677362417954,38167459367280,33218078026464,
    28793710725932,24857924085970,21373628754708,18303446264192,15611221833938,13261138524572,
    11219473532340,9453873307158,7933927819350,6631694478414,5520743648114,4577572338676,
    3780236540622],
   [3109241719628,2547202995242,2078251812768,1689018469462,1367086788778,1102168058900,
    885100866954,707862242242,564026943260,447469586606,353669572940,278332392968,218050316684,
    170170070792,132011166936,102020847406,78283360148,59673631482,45152210012,33648016380,
    24823591454,17765251504,12372031860,8194947974,4960582184,2753495044,1107874008,317853448]]
private def rkmC_w512_s1_6 : List ℤ := pzigCat
  [
   [368959294,781407758,1102862366,1717098278,2398694030,3344569922,4662949996,6226735278,
    8534651024,11457520950,15489705690,20808942290,27687003252,36878806582,48656918278,
    64117046724,83979617386,109509133974,142349161696,184037140862,237141025906,304029720306,
    388184646078,493532038158,624576924772,787182748578,987569954644,1233817734770,1534817735190,
    1901011068064,2344631069988,2879112587668,3520493350688,4286166752370,5196068755964,
    6272274187744,7538867070078,9022849618164,10752780692746,12760016898566,15077554781714,
    17740234020248,20784787348172,24248438389084,28169732278676,32586618516612,37536742710128,
    43056417726314,49179298505890,55936489807594,63354154840038,71453799157496,80250379312262,
    89751426554102,99956572020824,110855421715202,122428098224076,134643254968266,
    147458285702476,160818859550290,174658060960872,188897664098802,203447073435056,
    218205195765536,233060669374758,247892999570806,262574750018064,276971974146064,
    290947573959070,304362264889758,317077449092952,328957702138654,339872305634774,
    349698920431504,358324475984282,365648457081756,371584359205112,376061151808884,
    379025592820520,380441942305986,380294061385354,378584683041174,375335759320434,
    370588319705202,364400617785528,356848290783090,348021465889544,338023960140152,
    326970947648054,314986351182690,302201591347768,288751824172476,274774913414804,
    260408219253752,245786650133386,231041163243672,216295834064936,201667669107370,
    187263967746284,173182081076856,159508484371542,146317659239074,133673011222680,
    121625468686298,110214962127700,99470112857746,89408874593186,80039970447616,71362547250350,
    63368515258132,56042350949304,49362761613854,43303761189444,37834889320348,32923400584308,
    28533772665272,24629643294280,21173990884742,18129607800890,15460489993572,13131015720038,
    11107657841912,9358220451106,7852492073842,6562659001584,5462474581258,4528584083308,
    3739201696552],
   [3075013413782,2518756555198,2054733461304,1669663406740,1351243757764,1089266832364,
    874623510404,699386235148,557158219686,441911639340,349167579884,274691019964,215133545328,
    167840520724,130185358898,100582338222,77142374166,58735970996,44322346230,32884142302,
    24071427800,17045497070,11700380080,7613720784,4521874466,2457687880,971591630,274526762]]
private def rkmC_w512_s1_7 : List ℤ := pzigCat
  [
   [333772552,773364968,1086879460,1658749370,2278174662,3131260754,4420521700,5955404478,
    8229699014,11066257876,14960878686,20147082096,26835807516,35782319006,47216118290,
    62277668192,81717970118,106750693948,138995566144,179934939116,232168508178,298044667552,
    380996174224,484917985824,614314279432,775129550184,973601720870,1217797586118,1516560212716,
    1880342322524,2321465570786,2853463045244,3492486947650,4256021952116,5164173290066,
    6239222290648,7505510117690,8990309739586,10722461521038,12733692185256,15057396065690,
    17728897616762,20785399531006,24264625918652,28205660300392,32646988901538,37626850857672,
    43182062260182,49346772321418,56152482096316,63625669409546,71788092203786,80654772727420,
    90233232416948,100522859407584,111512864236300,123182750586120,135500265878958,
    148421718223674,161891372067384,175840778366228,190189935433622,204846284772132,
    219706632188230,234657290207464,249575456975326,264331289003822,278788535637470,
    292807876040690,306247888384012,318968121111720,330831459684908,341705943720754,
    351468329704700,360005080658740,367215708845452,373014103422918,377330230758938,
    380112234808354,381326314916356,380958697792434,379014800053704,375519661158248,
    370517515095412,364070128040916,356256708870566,347171026688128,336920557111392,
    325623887403514,313408257976614,300407987267380,286760863409886,272606986710332,
    258085486438446,243332710937128,228480456676710,213653296455796,198968189280632,
    184531968542686,170441178222778,156781018036532,143624531001038,131033295260636,
    119056299635136,107731375105388,97084903594834,87132688370572,77881172311350,69327416022414,
    61461239362926,54265165183186,47716149254072,41786506063316,36444423484494,31655873650796,
    27384363935190,23592749612272,20243362659430,17298644607928,14722236420794,12478441685644,
    10533679319948,8855831509580,7414921313006,6183328768994,5135229629582,4247589857490,
    3499075378720],
   [2870810102766,2345905597970,1909155805620,1547591778486,1249363282706,1004597009258,
    804529100142,641623199678,509716862574,403156224506,317640083584,249178330400,194606948654,
    151358633520,117013691510,90007351202,68632717188,51835409098,38668273772,28272116728,
    20291721204,14042546544,9379008394,5920706886,3410707366,1795508886,691677554]]
private def rkmC_w512_s1_8 : List ℤ := pzigCat
  [
   [297459712,659849054,889448140,1403130082,1973575006,2776636402,3947017972,5342217798,
    7451976898,10086010160,13707477220,18468537280,24640813464,32968647884,43720530312,
    57990631742,76432756696,100259010112,131001577832,170182837470,220343312728,283804666868,
    364020237412,464824430818,590795446080,747809458230,942147501818,1181921313990,1476028279252,
    1835133400426,2271658148074,2799433049250,3434864445254,4195810185522,5102888355062,
    6178855955554,7448787701486,8940625205268,10684099402346,12711897749194,15058415687498,
    17760210727254,20855627045216,24383775696176,28385038139698,32899212618048,37965851026498,
    43622838052622,49905462528952,56846021525532,64471688045588,72804575915786,81859607177172,
    91643924084510,102155864980286,113383281920312,125303656341162,137882168175164,
    151072041827482,164813711802286,179034572558488,193649798023058,208561729284568,
    223661712135632,238830274081570,253938879894378,268851768004510,283427162241058,
    297520438033992,310985390181890,323677502495120,335456184636260,346187123753392,
    355745556741966,364017694021106,370903970576238,376320315905106,380200101829352,
    382495787273216,383179151401286,382242845353552,379699585761190,375582514871642,
    369944309585662,362855724624624,354404863602446,344694417640704,333840470492944,
    321969636982592,309216716084454,295722559808786,281630740251720,267086006045352,
    252230988276618,237204580965590,222139643821522,207161128109410,192384780600100,
    177915751123394,163847501871786,150261763104166,137227251255628,124800661315648,
    113026115254294,101935664605492,91550656842224,81881112802590,72928165116498,64684021300538,
    57133147964026,50254159548866,44019665920298,38398513725210,33356073264452,28855508142740,
    24858652540904,21326444535072,18220411424188,15502126363812,13134689773786,11082760472574,
    9312570357464,7792789440678,6493925375690,5389261367646,4454045989672,3665879465010,
    3004802934156],
   [2452829891356,1994020048382,1614458215042,1301577093232,1045173404266,835794759660,
    665533384570,527918022856,416843439336,327868868918,256833397318,200309933464,155462552342,
    119817457222,91837341416,69725619974,52378220106,38829292648,28257433962,20214497810,
    14065293258,9267186560,5958910538,3399170174,1633217798,576919034]]
private def rkmC_w512_s1_9 : List ℤ := pzigCat
  [
   [399341036,633463378,1144278724,1684894012,2470032646,3513439538,4793830218,6684206156,
    9058351446,12389456236,16774512046,22599817442,30453941944,40685227286,54296509918,
    71930371974,94881759316,124579459108,162704600298,211710911314,274030650922,353194537122,
    453056937230,578454077762,735301596542,930241148758,1171631662906,1468749417866,
    1832811119976,2276705633560,2815118041286,3465227965228,4245934633668,5179064851714,
    6288515257056,7601044288060,9145973216686,10955139974006,13062995050888,15506218521176,
    18323463737572,21555292287400,25243125879612,29429349302830,34156031407606,39464290589894,
    45393743013780,51980592478144,59257732651616,67252438516976,75985770766644,85471474929026,
    95713817833978,106707869376152,118437003331288,130872844041542,143974461753914,
    157687018866754,171942700191744,186659491344084,201742244446010,217083080871966,
    232562113242790,248049245033782,263405080622844,278483704602228,293133936617382,
    307202584528024,320536668113144,332986050074246,344406646467870,354662912182564,
    363630329507114,371198569754368,377272910434452,381776939462668,384653697137272,
    385866952426290,385402419881940,383266957477138,379489840485968,374120935854736,
    367229885024820,358905327657836,349251696803238,338388393549948,326446312965602,
    313565768350024,299893787516212,285580989946720,270779160874990,255638760068406,
    240306010647370,224921224091742,209616140524834,194513200633586,179723328860368,
    165345008114824,151464587289710,138154299347942,125473655004942,113468873559648,
    102173202356288,91608512180636,81784878099538,72702671414616,64352939067046,56718872340946,
    49777057457808,43498490066522,37849759238204,32794160353496,28292576962510,24305176756314,
    20790756961142,17708694897970,15019405277472,12684150315718,10666608551078,8931748879484,
    7447212511200,6183187620156,5111848003628,4208305301108,3449771668456,2816120947376,
    2289119176990,1852766933174],
   [1493310611222,1198524832638,957795462752,762326020332,604088796398,476855446034,374837931872,
    293209483074,228441093780,176959163346,136271165050,104170290834,78987011236,59387265552,
    44051993072,32155166822,23154723932,16051520310,10831837074,6956728788,4059037106,2125629398,
    796111616,211744340]]
private def rkmC_w512_s1_10 : List ℤ := pzigCat
  [
   [338006598,821759672,1238423130,1895482394,2679797316,3736334944,5204435048,7218842418,
    9975464282,13696690646,18695559406,25418132522,34319994894,46232613530,61852010630,
    82314848226,109104741930,143678078730,188550304390,246140553866,319758631310,413529988538,
    531941795786,681167486374,867815660476,1100432817042,1388671951688,1743917744180,
    2179709537608,2711256333142,3356295659448,4135158959710,5070288508600,6187438210504,
    7514851074738,9083654851068,10928100753020,13084781882114,15593319546908,18495059996244,
    21833563582768,25653624142460,30000324798604,34919302345652,40454308725206,46647681863458,
    53538089796402,61159615644642,69540905258004,78702955053182,88658229558764,99409614145708,
    110948197176102,123253025016492,136289547426792,150009082229106,164348257230980,
    179228416336256,194556651290744,210224995117096,226112298172498,242085026021896,
    257998526779082,273700100455908,289029705970368,303824057936212,317918749310806,
    331151064096900,343363666267728,354407313344558,364143828427134,372449392669738,
    379216582251420,384357292737230,387804029041448,389511910766486,389459550218068,
    387648863702124,384106180188814,378880338376634,372042645589872,363684606322274,
    353915725006362,342862029772492,330662731820436,317466968235566,303431799295224,
    288718190663274,273488778062130,257904346825288,242121027562926,226288801810528,
    210547988128164,195028593848754,179848044661064,165110405277058,150905900022884,
    137309896263088,124383376843296,112173521045118,100713045339598,90022293904698,
    80109595334646,70972514392826,62599258229126,54969271178990,48055885909466,41826219862256,
    36243127288580,31266648462738,26854381939610,22962874401280,19548736259332,16568688694028,
    13981081840742,11745491441206,9823966802508,8180748857848,6782338836060,5598316503396,
    4600884840096,3764362047402,3066556278758,2487091571324,2008181629484,1614551507500,
    1292311614020,1030045490030],
   [817482599218,645944117118,508204076060,398032010340,310287559366,240689763406,185517150544,
    142302315238,108318287882,81681775908,61067923808,45055537750,32707208232,23386464778,
    16098889716,10791648878,6852515366,3923289748,1995623024,723808814]]
private def rkmC_w512_s1_11 : List ℤ := pzigCat
  [
   [289780944,540028010,1041841462,1505674742,2268554160,3151340428,4480852848,6351146746,
    8808014428,12374593650,17136811436,23439867184,32110155440,43549302398,58826975070,
    79130479654,105748197040,140797590918,186238441666,245238101332,321185251920,418454715676,
    542339754394,699236778050,896983343924,1144657044092,1453239036356,1835808723282,
    2307037720584,2884536000596,3588352226332,4441024742946,5468781215548,6700151593130,
    8167565929510,9906325454482,11954815083312,14354742535920,17150221388462,20387793121580,
    24115907359488,28383760229908,33241144774406,38736735879756,44917534006084,51827462114820,
    59505206113418,67984285305764,77289855998036,87437993744974,98434013256790,110270770455044,
    122927706289140,136369165849912,150543544601946,165383403715980,180804006482244,
    196704350072652,212966950532656,229459451160532,246035909014872,262538023889824,
    278798109832356,294641975962266,309890905650482,324366033318850,337891254744836,
    350296670578698,361422666719772,371122396432042,379266429116396,385744079926278,
    390466659151142,393370020716836,394414908325972,393588465797692,390904775222352,
    386403400771920,380149735917400,372232501909350,362762065622296,351867765194284,
    339694954860120,326402033125426,312156851957574,297132935137848,281506913472242,
    265453889331740,249145394326838,232746019687098,216410655368920,200282994683214,
    184493242824294,169156431744250,154372925583150,140226232256934,126783995206450,
    114098237341794,102205366502920,91127677066442,80874376317142,71442268549282,62818478129494,
    54980288468136,47897705456264,41535001178316,35851311650676,30802601776300,26342998519696,
    22424999923544,19001952239384,16027325439642,13456098678204,11245605364338,9355121782156,
    7746670628328,6385538709916,5239210086678,4279032777084,3478868672632,2815301308566,
    2268018509450,1818867298094,1451948338786,1154054117850,913017327862,719081578490,
    563808794148],
   [439861683432,341521024128,263861360808,202522035312,154613235866,117073399988,87868070066,
    65402118166,48030839006,34736771058,24743805250,16963779936,11270657682,7020131324,
    3904105272,1910134218,666286790]]
private def rkmPhb_w512_s2a : List ℕ := uNatCatN
  [
   [748529915223942,748500228411687,748467385902154,748431392703426,748392253784714,
    748349974076558,748304558471021,748256011821889,748204338944856,748149544617719,
    748091633580559,748030610535930,747966480149036,747899247047912,747828915823601,
    747755491030325,747678977185657,747599378770694,747516700230216,747430945972855,
    747342120371258,747250227762240,747155272446947,747057258691007,746956190724684,
    746852072743025,746744908906013,746634703338707,746521460131387,746405183339697,
    746285876984780,746163545053418,746038191498164,745909820237474,745778435155839,
    745644040103911,745506638898629,745366235323346,745222833127943,745076436028957,
    744927047709692,744774671820340,744619311978088,744460971767234,744299654739294,
    744135364413112,743968104274962,743797877778653,743624688345630,743448539365072,
    743269434193994,743087376157337,742902368548065,742714414627255,742523517624188,
    742329680736435,742132907129946,741933199939130,741730562266942,741524997184959,
    741316507733461,741105096921505,740890767727005,740673523096799,740453365946724,
    740230299161683,740004325595714,739775448072055,739543669383209,739308992291004,
    739071419526654,738830953790819,738587597753659,738341354054892,738092225303845,
    737840214079505,737585322930570,737327554375496,737066910902546,736803394969827,
    736537009005342,736267755407023,735995636542774,735720654750507,735442812338180,
    735162111583825,734878554735588,734592144011753,734302881600773,734010769661297,
    733715810322194,733418005682579,733117357811831,732813868749615,732507540505901,
    732198375060978,731886374365471,731571540340352,731253874876953,730933379836974,
    730610057052491,730283908325963,729954935430235,729623140108540,729288524074504,
    728951089012137,728610836575837,728267768390385,727921886050933,727573191123001,
    727221685142468,726867369615555,726510246018817,726150315799123,725787580373642,
    725422041129826,725053699425382,724682556588259,724308613916615,723931872678797,
    723552334113311,723169999428790,722784869803966,722396946387635,722006230298621,
    721612722625737,721216424427753,720817336733345],
   [720415460541060,720010796819267,719603346506112,719193110509470,718780089706892,
    718364284945553,717945697042199,717524326783090,717100174923941,716673242189862,
    716243529275294,715811036843949,715375765528736,714937715931699,714496888623946,
    714053284145571,713606903005585,713157745681835,712705812620930,712251104238153,
    711793620917383,711333363011011,710870330839845,710404524693027,709935944827939,
    709464591470108,708990464813111,708513565018475,708033892215575,707551446501536,
    707066227941120,706578236566623,706087472377763,705593935341569,705097625392263,
    704598542431145,704096686326474,703592056913340,703084653993546,702574477335477,
    702061526673970,701545801710184,701027302111461,700506027511191,699981977508674,
    699455151668971,698925549522762,698393170566201,697858014260756,697320080033065,
    696779367274772,696235875342372,695689603557047,695140551204500,694588717534788,
    694034101762152,693476703064840,692916520584934,692353553428165,691787800663733,
    691219261324123,690647934404908,690073818864566,689496913624277,688917217567725,
    688334729540899,687749448351885,687161372770656,686570501528861,685976833319610,
    685380366797251,684781100577150,684179033235464,683574163308911,682966489294535,
    682356009649468,681742722790690,681126627094785,680507720897689,679886002494439,
    679261470138915,678634122043581,678003956379217,677370971274652,676735164816492,
    676096535048840,675455079973015,674810797547265,674163685686479,673513742261891,
    672860965100779,672205351986162,671546900656491,670885608805339,670221474081076,
    669554494086551,668884666378764,668211988468531,667536457820146,666858071851042,
    666176827931437,665492723383983,664805755483409,664115921456155,663423218480000,
    662727643683692,662029194146561,661327866898137,660623658917756,659916567134158,
    659206588425089,658493719616884,657777957484056,657059298748866,656337740080902,
    655613278096635,654885909358982,654155630376854,653422437604701,652686327442049,
    651947296233030,651205340265905,650460455772582,649712638928118,648961885850230,
    648208192598779,647451555175260,646691969522282],
   [645929431523034,645163937000748,644395481718156,643624061376931,642849671617125,
    642072308016601,641291966090447,640508641290390,639722329004199,638933024555073,
    638140723201028,637345420134269,636547110480553,635745789298546,634941451579164,
    634134092244908,633323706149187,632510288075633,631693832737400,630874334776459,
    630051788762874,629226189194076,628397530494115,627565807012911,626731013025484,
    625893142731177,625052190252866,624208149636157,623361014848569,622510779778705,
    621657438235411,620800983946921,619941410559984,619078711638985,618212880665043,
    617343911035104,616471796061008,615596528968554,614718102896535,613836510895771,
    612951745928117,612063800865459,611172668488691,610278341486680,609380812455205,
    608480073895888,607576118215100,606668937722854,605758524631676,604844871055458,
    603927969008291,603007810403285,602084387051352,601157690659993,600227712832039,
    599294445064391,598357878746725,597418005160183,596474815476036,595528300754325,
    594578451942482,593625259873926,592668715266625,591708808721652,590745530721696,
    589778871629558,588808821686619,587835371011278,586858509597364,585878227312519,
    584894513896556,583907358959778,582916751981277,581922682307197,580925139148966,
    579924111581496,578919588541351,577911558824880,576900011086318,575884933835848,
    574866315437628,573844144107789,572818407912382,571789094765297,570756192426141,
    569719688498070,568679570425588,567635825492302,566588440818626,565537403359454,
    564482699901779,563424317062269,562362241284797,561296458837920,560226955812308,
    559153718118133,558076731482388,556995981446171,555911453361905,554823132390503,
    553731003498481,552635051455007,551535260828898,550431615985545,549324101083787,
    548212700072714,547097396688406,545978174450607,544855016659324,543727906391361,
    542596826496782,541461759595291,540322688072545,539179594076382,538032459512977,
    536881266042905,535725995077125,534566627772885,533403145029522,532235527484184,
    531063755507453,529887809198871,528707668382373,527523312601611,526334721115177,
    525141872891724,523944746604968,522743320628585],
   [521537573030987,520327481569982,519113023687310,517894176503054,516670916809918,
    515443221067380,514211065395698,512974425569782,511733277012919,510487594790351,
    509237353602694,507982527779208,506723091270894,505459017643433,504190280069948,
    502916851323592,501638703769945,500355809359236,499068139618360,497775665642700,
    496478358087744,495176187160484,493869122610607,492557133721447,491240189300718,
    489918257670992,488591306659945,487259303590336,485922215269728,484580007979934,
    483232647466183,481880098925996,480522326997766,479159295749016,477790968664355,
    476417308633088,475038277936493,473653838234740,472263950553451,470868575269873,
    469467672098668,468061200077296,466649117550978,465231382157228,463807950809935,
    462378779682984,460943824193387,459503038983931,458056377905290,456603793997620,
    455145239471586,453680665688821,452210023141783,450733261432998,449250329253653,
    447761174361529,446265743558236,444763982665733,443255836502092,441741248856500,
    440220162463437,438692518976027,437158258938510,435617321757809,434069645674149,
    432515167730695,430953823742169,429385548262392,427810274550722,426227934537336,
    424638458787297,423041776463371,421437815287528,419826501501069,418207759823335,
    416581513408910,414947683803275,413306190896827,411656952877202,409999886179807,
    408334905436505,406661923422338,404980851000219,403291597063483,401594068476210,
    399888170011193,398173804285452,396450871693177,394719270335957,392978895950177,
    391229641831427,389471398755787,387704054897812,385927495745061,384141604008983,
    382346259531963,380541339190344,378726716793183,376902262976534,375067845092996,
    373223327096280,371368569420502,369503428853917,367627758406775,365741407172957,
    363844220185030,361936038262347,360016697851758,358086030860510,356143864480847,
    354190021005810,352224317635686,350246566274526,348256573316095,346254139418580,
    344239059267324,342211121324805,340170107566998,338115793205227,336047946392488,
    333966327913202,331870690855213,329760780262802,327636332769328,325497076208036,
    323342729199418,321173000713382,318987589604310],
   [316786184116946,314568461360830,312334086750805,310082713410876,307813981538455,
    305527517725705,303222934234426,300899828220499,298557780903567,296196356677125,
    293815102153729,291413545139429,288991193530934,286547534128241,284082031354701,
    281594125875533,279083233104770,276548741589415,273990011258251,271406371521180,
    268797119203194,266161516295058,263498787500431,260808117556437,258088648301601,
    255339475461399,252559645117456,249748149821503,246903924309410,244025840763808,
    241112703565803,238163243466805,235176111100159,232149869738855,229082987189370,
    225973826692312,222820636676926,219621539187974,216374516768446,213077397538592,
    209727838158590,206323304295969,202861048136085,199338082369441,195751149956854,
    192096688803435,188370790252691,184569150025750,180687009853824,176719087550682,
    172659492597354,168501623392373,164238041052222,159860312869246,155358816003693,
    150722488319355,145938507852581,140991874218010,135864852582425,130536220673450,
    124980226176608,119165105495894,113050914742167,106586237019581,99702960236726,
    92307532283207,84265264189936,75369430783164,65272028290907,53294489482033,37684930816726]]
private def rkmC_w512_s2a_1 : List ℤ := pzigCat
  [
   [515975130,936611570,1443632958,2325571868,3430355494,4917591238,7150710228,10024141076,
    14323061250,20183873364,28185289602,39308627590,54280224066,74483804780,101792182720,
    137870253476,185889094442,249100952758,331702978100,439147483198,577796882548,755783106406,
    982982944032,1270582803478,1632942272268,2086336997906,2649968705598,3346522889846,
    4201679003512,5244962522756,6510000343246,8033788333482,9858073528548,12027930518896,
    14592238263342,17603669083996,21117241656106,25190181389654,29881171063424,35248370444614,
    41349168096340,48237799921376,55963606786846,64570173211276,74091767063168,84552700049708,
    95964650219830,108324736366288,121613837151824,135795033564516,150811911188370,
    166588557899004,183028234662652,200013757682744,217408467244362,235057088942784,
    252787638668214,270414392508558,287739834236942,304559166688954,320664078167868,
    335846044784816,349902376556726,362639316415626,373877131281682,383454484170502,
    391231873634494,397094887354830,400957943690580,402765149050568,402492317918448,
    400147746210390,395771162250706,389433033809100,381233197076674,371296980337130,
    359773252269446,346830335842944,332651348071538,317431159680330,301370785871386,
    284673734227892,267541991474094,250171702342856,232749630491524,215450847968530,
    198435292954942,181845845659410,165808105579032,150427880274570,135792010508082,
    121968290478392,109005483572052,96935516320156,85773368830078,75519543215372,66161663408298,
    57676134394130,50029977306452,43182806293888,37088650840698,31697558651696,26956423377384,
    22811747590916,19209432833278,16096368133148,13421766055958,11136543336904,9195268453410,
    7555231191222,6177213364450,5025985045200,4069360333098,3278953516862,2629238545308,
    2098180451198,1666434043726,1317060289120,1035871283894,810802269068,631381889840,
    489320630670,377009266058,288856535864,220134843158,166490391898,125063445556,93046379848],
   [68515241136,49750640810,35410404318,24781557244,16782976868,10977299486,6755437570,
    3768905374,1900918856,700835456]]
private def rkmC_w512_s2a_2 : List ℤ := pzigCat
  [
   [235405438,704608826,1009307166,1699280590,2554872414,3782563768,5623737550,8102097380,
    11679871296,16853256732,23832193898,33649854484,47192642150,65593778286,90679091902,
    124473614442,169609808788,229797058950,309270414652,413388322244,549404255860,725150520334,
    951037474028,1239562538964,1605206547490,2065880515774,2642199015410,3358251448314,
    4242197219154,5326125145202,6646023979650,8242733059702,10161267832896,12450716267914,
    15164942506118,18360384327056,22097218762578,26437499990426,31443823901602,37178973630214,
    43703443186134,51073688992132,59341040836636,68548333387290,78728538599586,89902235406406,
    102075257866774,115236912297734,129357353591950,144387164834678,160254989962074,
    176867510584466,194109392596748,211842847113624,229910303815974,248134473371418,
    266322002591488,284266541338178,301751750650066,318556123168786,334457712246636,
    349238432051184,362689489791710,374615790778590,384841485493958,393213457760118,
    399605338115022,403921270662578,406097197615860,406103805721258,403945945980522,
    399662909646452,393327830652346,385044114105982,374944202622292,363185164114162,
    349944952129822,335418018999000,319810510832578,303335675548786,286209047276450,
    268643593981114,250846229523044,233013219383550,215327731251446,197956482073032,
    181047830661750,164731308271754,149114996678768,134286723619678,120313783667684,
    107243630516714,95105456961824,83911259409162,73657779155102,64328900686202,55896418078570,
    48323277445342,41564826038348,35570969330754,30288151402494,25659820590908,21629507466094,
    18140690026966,15138114641864,12569178761406,10383975749368,8535765601788,6981591357698,
    5681844400626,4601306249524,3707789358790,2973005310182,2372330189048,1883532967652,
    1488128722066,1169930775708,915165451838,712276017496,551469327026,424714431356,325327902480,
    247506912808,187214116716,140455412778,104345536174,76834127420,55778801732],
   [39944533988,28006539566,19169940542,12724728182,7950681128,4620607400,2476334864,936359150,
    248489292]]
private def rkmC_w512_s2a_3 : List ℤ := pzigCat
  [
   [410850908,761684750,1402974080,2141289358,3210292354,4948723022,7277622458,10797094426,
    15673296654,22617552178,32452955870,46016745724,64925391290,90684014412,126100257758,
    173882968538,237993043954,323683951542,436863279900,585390926070,779087675032,1029527962132,
    1351257609226,1761365036766,2280465993820,2932869607774,3746501590282,4754298990128,
    5993268445866,7505688631338,9338381528276,11543378442532,14177432057242,17301022230740,
    20978542718232,25277075038272,30264601384370,36009626843084,42578387469372,50033468767840,
    58431779311158,67820963135388,78238550284918,89707899238768,102236441332820,115813199135876,
    130406444705758,145962235755190,162402644756042,179625186134804,197503289018908,
    215885664735614,234598830266184,253448902463170,272224113937730,290699548517482,
    308639987237086,325806287952830,341959843785038,356867929512134,370309720190156,
    382081504177032,392001998339328,399916975451640,405702713461834,409270540613610,
    410567792062806,409579307706528,406328580324194,400875584085290,393316059865432,
    383777927168070,372418405729588,359419536633494,344982969053266,329325487616568,
    312673393675734,295256610890842,277304955664450,259042062323506,240681739317632,
    222424062165460,204452049357348,186929364480152,169998487516052,153779604299036,
    138370873422194,123847279031478,110262758625246,97651183689838,86026986198224,75388783311890,
    65719973445368,56991558914726,49164467706490,42191320660600,36018880992020,30589868320634,
    25844330370090,21722046367622,18162797020344,15108371491786,12502867847202,10293393866912,
    8430987651998,6870322145784,5569794435652,4492695134554,3605470733026,2878743827130,
    2286930432710,1807527602302,1421411142464,1112236875926,865631755842,670316519362,
    516242624906,395254373608,300876617832,227457520762,170626082782,127118549234,93627120552,
    68277297574,49129889070,34668205504,24048974648,16239373848],
   [10420651848,6445171634,3469566750,1548616586,506373490]]
private def rkmC_w512_s2a_4 : List ℤ := pzigCat
  [
   [332310204,778623404,1262434770,2054409910,3421492266,5178198712,7850541288,11760161680,
    17309671930,25421502562,36759194264,53047155610,75719351218,107212573072,150679867558,
    209843734602,289901429244,397291319394,540052910304,728712241660,975459031588,1295993574304,
    1709043071986,2236886613604,2906037689558,3747639716352,4797982794174,6098526042992,
    7696033358530,9643572604556,11999197906008,14825911045938,18192136403474,22169304496848,
    26832001737262,32255527606268,38514649826648,45681415546898,53822137333444,62995551690882,
    73249540223346,84617536911100,97117111485108,110745505885762,125477859474084,141265120405054,
    158031699207158,175674640450986,194063509476060,213040384928994,232421882870408,
    252000577604940,271549294111718,290824392234426,309570715109766,327527580405932,
    344434209139640,360035970003324,374091669675440,386378402863234,396698894514548,
    404886021707820,410806991481112,414367759026702,415514946323698,414236826013992,
    410564750447542,404570375467984,396364433900808,386093042278544,373933155007940,
    360088221609712,344782125971024,328252903979568,310748135401204,292517265491480,
    273807045149944,254856220846500,235890254295102,217117994404300,198728281100738,
    180886903935686,163736532673504,147394288910274,131952600743094,117480014212582,
    104021685970080,91601651714546,80224894166116,69878645546740,60536450648180,52159240333536,
    44698316908700,38098101881094,32297614544202,27232968062206,22839531351358,19052151075310,
    15807974691302,13046369079996,10709865254208,8745281912292,7103358312994,5739110599974,
    4612664192600,3687747944764,2932893378416,2320479573460,1826263445548,1429791572808,
    1113569856110,862473644996,664491280350,508985252004,387479984830,293165360762,220180017384,
    164046302626,121307850688,88688061388,64206531558,45840046570,32060072456,21944822446,
    14507958572,9048226404,5372743872,2765094360],
   [1179347590,370088530]]
private def rkmC_w512_s2a_5 : List ℤ := pzigCat
  [
   [289537452,734511956,1332389014,2320851192,3675292864,5634805198,8867961806,13345432472,
    20178500990,30305818516,44811637862,65705620116,95264346030,136532809120,194140524702,
    273184463598,381152706724,527108338082,722291232134,981262430672,1321632504974,1764767723652,
    2336997498192,3068882871088,3997228902956,5164402457210,6618987068560,8416551515482,
    10618742469992,13293439485060,16514975459536,20361701668792,24916310914218,30263304320912,
    36486967718972,43669514828868,51887594656538,61209402104390,71691941299496,83376010259566,
    96284333654060,110417281098370,125749467899294,142227752406156,159768614038212,
    178256991986050,197546746986830,217459818881240,237789395792888,258302049040770,
    278741415644780,298834034722992,318294756961128,336833227930298,354161986292462,
    370002476706010,384093815003966,396199532378142,406113751707750,413667759897572,
    418734419100274,421231392786456,421124383083420,418426426461826,413198152253172,
    405545462186322,395615494638508,383592630140670,369692678034490,354156057657698,
    337242194257592,319221331389114,300368146857522,280955357181914,261246654631930,
    241492223062066,221923380506028,202748954973206,184152559490810,166290985829090,
    149292607417574,133258443491494,118261988537280,104350925772666,91549539048190,
    79860401076122,69267201395028,59738383470380,51228587679564,43682789038766,37038708859060,
    31228494863198,26182048278170,21828338704338,18096982755702,14919838871434,12232306173764,
    9973223045526,8086551291776,6520716037812,5229091121626,4170519533916,3308094489892,
    2609610499816,2047459228508,1597801905226,1239816710992,956765724672,734067497202,
    559709432850,424238206868,319452052146,238775067158,177177967474,130428488564,94835559788,
    68300184406,48440699164,33646029130,22958231376,15183289972,9483121814,5549252012,2911203446,
    1030500562,251206530]]
private def rkmHbWin_w512_s2b : List ℤ := altBuildHbFrom 2048 1024 18391866913 0 1024
private def rkmXsWin_w512_s2b_in : List ℤ := pzigCat
  [
   [234356048,382370986,899885440,1523260118,2543376036,4376110244,7111189624,11401066704,
    18003008236,27786522440,42514587628,63988762994,95081082242,140015006450,203507674932,
    292702502870,416293192080,585769893676,815804625934,1124574035180,1534663828356,
    2074020542666,2775894752354,3680351657202,4834362258096,6292220770034,8116222886548,
    10376528555634,13150699539272,16523671316936,20585698570268,25431277675044,31157674504640,
    37861073554864,45634969627474,54565466010208,64727580626382,76181438559032,88967417255580,
    103101760207198,118573255254828,135338947403076,153321267765396,172406918240312,
    192444413004528,213245738518448,234587538923820,256213945182456,277841370632576,
    299164501354382,319862620662364,339608175748822,358075358996304,374948284530290,
    389931378167220,402756823715622,413193220513732,421052594727218,426195660285194,
    428535837769992,428042392087348,424739892711390,418707115784758,410075201267596,
    399021268897076,385763671349456,370554979591830,353673675641032,335415910916866,
    316087964498120,295996899865708,275443527554274,254715809537648,234081511774986,
    213784818512872,194041965019238,175038327196984,156927373067794,139830821219344,
    123838031625872,109008696250000,95374877683174,82942875512880,71697771531984,61605878588564,
    52618071887858,44673575937252,37703340390128,31631888822956,26381297892768,21872751585766,
    18027983060282,14772010597230,12033428474426,9745373336792,7846504031962,6281285756332,
    4999195878668,3956016824720,3112683526874,2434919645414,1893767702986,1464385475466,
    1125608180714,860065674884,653190803824,492898262470,369299170714,274886293104,202887066414,
    148385481130,107652927734,77187238702,54466188716,37821120380,25692816876,16820582246,
    10515484166,6297477782,3185225918,1296949812,380787886]]
private def rkmXsWin_w512_s2b_out : List ℤ := pzigCat
  [
   [592851335,784469965,634542368,2306880508,614674482,3978762735,3955167007,5016302284,
    11223907196,1252075745,22266211179,15141977871,28787586566,51614116822,8730126069,
    102010929067,76628375125,117364559738,254623070692,31437277512,441483729979,510948371781,
    283113397338,1252336178478,855717854430,1354454400231,3160382721963,1262280927353,
    4309101762414,7787509282020,2152157172252,11555331583957,20021534413417,7251291003205,
    26438118440478,54163069317176,37327806561942,38896777386625,137100502881465,175664193261719,
    76689918338389,176938910016508,518108405475234,825750674685770,989515571681048,
    965509179823160,789268504372094,544591245337984,315027995261230,149317103535612,
    55044950606524,13733180300158]]
private def rkmPhb_w512_s2b : List ℕ := uNatCatN
  [
   [690647934404908,690073818864566,689496913624277,688917217567725,688334729540899,
    687749448351885,687161372770656,686570501528861,685976833319610,685380366797251,
    684781100577150,684179033235464,683574163308911,682966489294535,682356009649468,
    681742722790690,681126627094785,680507720897689,679886002494439,679261470138915,
    678634122043581,678003956379217,677370971274652,676735164816492,676096535048840,
    675455079973015,674810797547265,674163685686479,673513742261891,672860965100779,
    672205351986162,671546900656491,670885608805339,670221474081076,669554494086551,
    668884666378764,668211988468531,667536457820146,666858071851042,666176827931437,
    665492723383983,664805755483409,664115921456155,663423218480000,662727643683692,
    662029194146561,661327866898137,660623658917756,659916567134158,659206588425089,
    658493719616884,657777957484056,657059298748866,656337740080902,655613278096635,
    654885909358982,654155630376854,653422437604701,652686327442049,651947296233030,
    651205340265905,650460455772582,649712638928118,648961885850230,648208192598779,
    647451555175260,646691969522282,645929431523034,645163937000748,644395481718156,
    643624061376931,642849671617125,642072308016601,641291966090447,640508641290390,
    639722329004199,638933024555073,638140723201028,637345420134269,636547110480553,
    635745789298546,634941451579164,634134092244908,633323706149187,632510288075633,
    631693832737400,630874334776459,630051788762874,629226189194076,628397530494115,
    627565807012911,626731013025484,625893142731177,625052190252866,624208149636157,
    623361014848569,622510779778705,621657438235411,620800983946921,619941410559984,
    619078711638985,618212880665043,617343911035104,616471796061008,615596528968554,
    614718102896535,613836510895771,612951745928117,612063800865459,611172668488691,
    610278341486680,609380812455205,608480073895888,607576118215100,606668937722854,
    605758524631676,604844871055458,603927969008291,603007810403285,602084387051352,
    601157690659993,600227712832039,599294445064391,598357878746725,597418005160183,
    596474815476036,595528300754325,594578451942482],
   [593625259873926,592668715266625,591708808721652,590745530721696,589778871629558,
    588808821686619,587835371011278,586858509597364,585878227312519,584894513896556,
    583907358959778,582916751981277,581922682307197,580925139148966,579924111581496,
    578919588541351,577911558824880,576900011086318,575884933835848,574866315437628,
    573844144107789,572818407912382,571789094765297,570756192426141,569719688498070,
    568679570425588,567635825492302,566588440818626,565537403359454,564482699901779,
    563424317062269,562362241284797,561296458837920,560226955812308,559153718118133,
    558076731482388,556995981446171,555911453361905,554823132390503,553731003498481,
    552635051455007,551535260828898,550431615985545,549324101083787,548212700072714,
    547097396688406,545978174450607,544855016659324,543727906391361,542596826496782,
    541461759595291,540322688072545,539179594076382,538032459512977,536881266042905,
    535725995077125,534566627772885,533403145029522,532235527484184,531063755507453,
    529887809198871,528707668382373,527523312601611,526334721115177,525141872891724,
    523944746604968,522743320628585,521537573030987,520327481569982,519113023687310,
    517894176503054,516670916809918,515443221067380,514211065395698,512974425569782,
    511733277012919,510487594790351,509237353602694,507982527779208,506723091270894,
    505459017643433,504190280069948,502916851323592,501638703769945,500355809359236,
    499068139618360,497775665642700,496478358087744,495176187160484,493869122610607,
    492557133721447,491240189300718,489918257670992,488591306659945,487259303590336,
    485922215269728,484580007979934,483232647466183,481880098925996,480522326997766,
    479159295749016,477790968664355,476417308633088,475038277936493,473653838234740,
    472263950553451,470868575269873,469467672098668,468061200077296,466649117550978,
    465231382157228,463807950809935,462378779682984,460943824193387,459503038983931,
    458056377905290,456603793997620,455145239471586,453680665688821,452210023141783,
    450733261432998,449250329253653,447761174361529,446265743558236,444763982665733,
    443255836502092,441741248856500,440220162463437],
   [438692518976027,437158258938510,435617321757809,434069645674149,432515167730695,
    430953823742169,429385548262392,427810274550722,426227934537336,424638458787297,
    423041776463371,421437815287528,419826501501069,418207759823335,416581513408910,
    414947683803275,413306190896827,411656952877202,409999886179807,408334905436505,
    406661923422338,404980851000219,403291597063483,401594068476210,399888170011193,
    398173804285452,396450871693177,394719270335957,392978895950177,391229641831427,
    389471398755787,387704054897812,385927495745061,384141604008983,382346259531963,
    380541339190344,378726716793183,376902262976534,375067845092996,373223327096280,
    371368569420502,369503428853917,367627758406775,365741407172957,363844220185030,
    361936038262347,360016697851758,358086030860510,356143864480847,354190021005810,
    352224317635686,350246566274526,348256573316095,346254139418580,344239059267324,
    342211121324805,340170107566998,338115793205227,336047946392488,333966327913202,
    331870690855213,329760780262802,327636332769328,325497076208036,323342729199418,
    321173000713382,318987589604310,316786184116946,314568461360830,312334086750805,
    310082713410876,307813981538455,305527517725705,303222934234426,300899828220499,
    298557780903567,296196356677125,293815102153729,291413545139429,288991193530934,
    286547534128241,284082031354701,281594125875533,279083233104770,276548741589415,
    273990011258251,271406371521180,268797119203194,266161516295058,263498787500431,
    260808117556437,258088648301601,255339475461399,252559645117456,249748149821503,
    246903924309410,244025840763808,241112703565803,238163243466805,235176111100159,
    232149869738855,229082987189370,225973826692312,222820636676926,219621539187974,
    216374516768446,213077397538592,209727838158590,206323304295969,202861048136085,
    199338082369441,195751149956854,192096688803435,188370790252691,184569150025750,
    180687009853824,176719087550682,172659492597354,168501623392373,164238041052222,
    159860312869246,155358816003693,150722488319355,145938507852581,140991874218010,
    135864852582425,130536220673450,124980226176608],
   [119165105495894,113050914742167,106586237019581,99702960236726,92307532283207,84265264189936,
    75369430783164,65272028290907,53294489482033,37684930816726]]
private def rkmC_w512_s2b_1 : List ℤ := pzigCat
  [
   [237413214,664167594,1373699148,2634799924,4620988858,7697262958,12915926048,20795955070,
    32988553886,51589683572,79323607944,120407008608,180131771118,265635339450,386703456766,
    556112161728,789850592996,1108914455206,1538703691836,2111053450072,2864791114274,
    3846009595380,5109636946110,6719516562456,8748231277516,11277644482674,14398580040376,
    18208574020768,22812245595492,28317877496448,34834469546708,42469229278956,51322888801972,
    61484811058096,73028807787524,86007627632038,100447201313726,116343149511652,133654815792404,
    152302532731520,172165270074542,193078642403712,214835590254730,237188884776458,
    259853793929774,282513692578644,304827967820264,326438750024124,346981637648028,
    366095625309716,383433355229850,398672206769004,411524513718052,421745701840446,
    429142933999258,433581120446226,434985989683470,433347001959596,428716883846712,
    421208325301260,410991067200180,398284550237448,383350681307732,366485214086804,
    348008262606968,328254017573080,307561652554202,286266184060448,264689437701654,
    243133594549068,221874941112284,201158296620126,181195135661606,162160703226698,
    144193703652870,127397019066954,111839713447648,97558734804426,84562664910272,72835798724480,
    62340854908444,53023673495116,44817590641596,37645707238136,31425206154716,26070255025894,
    21494533957416,17612760965224,14343570498098,11610049835852,9340190109258,7468613573254,
    5936144133408,4689570708554,3682424632560,2874332864574,2230029461378,1719663957806,
    1317955082466,1003930027660,759644795684,571046032830,426507247998,316093937700,232376005196,
    169517155178,122444812906,87327003338,61482709640,42639115892,28882634770,18857473082,
    12009674778,7064709568,3611231946,1567888462,478209580]]
private def rkmC_w512_s2b_2 : List ℤ := pzigCat
  [
   [210283008,723656932,1406875338,2857263774,5330496734,9442913738,16524181608,27753815110,
    45272179488,72625259672,114317256616,176589929778,268651699880,401695294292,591318596306,
    857683455314,1226191615588,1729499045886,2407742260382,3309616899814,4493925436650,
    6029670729184,7996596159282,10485543026796,13598188102754,17444968879292,22144692198506,
    27820858242232,34598514972946,42600587461082,51942050706488,62724647375704,75031143902200,
    88918441529864,104411365545500,121497010757248,140119678915132,160175982865840,
    181513711436466,203929743931770,227171421234578,250940473087540,274897591501136,
    298669990570352,321861263129062,344062094718424,364861721035374,383861673593226,
    400688282085218,415004440739174,426521542915994,435009438904668,440302428578924,
    442306251347906,441000048452356,436435897412086,428736740316634,418090999355904,
    404744953811938,388993409201900,371169790249040,351634228227936,330761837039154,
    308931957857552,286517059969796,263872233982190,241328518699398,219184864134680,
    197703264256216,177105782321756,157572865576968,139242910698210,122213599862680,
    106545229356002,92263250662604,79362218534922,67811210305776,57557831984990,48532100317764,
    40652436799778,33828899317026,27966854130032,22969969612738,18743561132980,15196125800184,
    12240605590310,9796656635074,7790756463162,6156044613388,4833364471832,3770946743952,
    2923410572742,2251814686686,1723395804520,1310522474590,989915180526,742715882848,
    553318458736,409371742896,300375468020,218444732126,157607735726,112532472370,79171049746,
    54869305814,37414088200,24833120382,15800735320,9540579878,5371136494,2605407830,827052370]]
private def rkmC_w512_s2b_3 : List ℤ := pzigCat
  [
   [227973801,17695626,681453710,1878213676,3922005382,7901397742,14890227764,26928655858,
    47436442672,80326120762,132140689746,212056187422,332128841310,509271310396,766194130480,
    1131781341276,1643521214174,2348317816216,3303909664214,4579824725030,6259146554870,
    8438073613952,11225927200208,14745363910746,19129315127214,24518944084372,31060280167662,
    38898676898894,48172977624280,59009258971102,71512556910778,85759278146312,101789152389888,
    119598144705482,139130720188624,160275643586730,182862652075218,206660116034866,
    231377554006740,256669620993270,282142307356382,307363033985348,331873050684630,
    355200886084284,376877373709074,396452161844696,413509259076180,427680860684976,
    438661849044626,446220223626740,450204727376662,450549757107928,447277843122864,
    440496148147298,430391679252718,417223850293840,401312707262020,383026832824726,
    362769850442566,340966017859100,318046286068292,294434970156704,270538115189352,
    246732870703054,223358790563728,200712430890624,179043475768920,158552004590024,
    139389420635290,121660206988162,105424958340220,90704042952544,77484147380318,65722790309154,
    55353770153202,46293379340304,38445307191310,31705480902654,25965874173640,21118180277920,
    17057378769102,13683248882576,10901580289180,8626205350104,6779623068982,5292414851108,
    4103428156554,3160018643674,2417150610844,1836352419528,1385376434814,1037789809592,
    771929408258,570013401188,417534366664,303343988494,218331207916,155771197580,109890052182,
    76244303678,52062507628,34997182200,22832057724,14121493680,8135386248,4285278508,1928847514,
    574716450]]
private def rkmC_w512_s2b_4 : List ℤ := pzigCat
  [
   [443173581,176360511,949290914,3789678110,10095692216,22132532530,43566854166,80485824080,
    141779073390,239625425966,391906002820,623001395412,964710635976,1459551643416,2161721778736,
    3138355403114,4472222984222,6262548487722,8624898543404,11691918093302,15611534611876,
    20544609245950,26660498378020,34132551918644,43130546775082,53812313314950,66314719395756,
    80743662550952,97163674742288,115587883563244,135969964906752,158196154522306,
    182080200686470,207362569240796,233711001554250,260725485894512,287948084271924,
    314874693196386,340970083903956,365686156561040,388481367606112,408840528206920,
    426294163232584,440436689872604,450942483957304,457577615413008,460208517450326,
    458806326266776,453446609148846,444303258986188,431641097072796,415803506534340,
    397197161447638,376275309197700,353520646863750,329428107754356,304487018767452,
    279166501521888,253903268644938,229090227798046,205068803666296,182124500322346,
    160484439672816,140317731133496,121737878754162,104806800321296,89540739560480,
    75916582494474,63878125523338,53343357396332,44211710847288,36369744091390,29696232015444,
    24067529674682,19361911883550,15462180966844,12257700436740,9646465996452,7536385301610,
    5845382180574,4501109715622,3440838770392,2611161811734,1967132316310,1471138272708,
    1091995265362,804283767608,587629738164,425816216614,305925689140,217721896912,153248752538,
    106474380014,72877276620,49025902746,32264030864,20547725908,12380114674,6752826890,
    3043114384,879665338]]
private def rkmC_w512_s2b_5 : List ℤ := pzigCat
  [
   [327757355,967219281,1821469761,2578696953,3218232867,2834881959,75523012,8042758640,
    25629558678,60192968570,123265972092,231412987196,408799074504,689460843950,1118837704984,
    1756917473680,2680887347204,3986946231108,5791993709342,8234952249334,11476743227254,
    15697638401804,21093791688242,27872376103316,36242881350526,46407254510972,58549558357584,
    72822527540298,89333345011704,108131026931108,129194114713164,152419651779026,
    177615775276720,204498321503300,232691818817244,261735339684706,291093253640158,
    320171122499992,348335821978918,374938265459748,399338478957198,420932154704234,
    439175818626420,453609037174606,463873767560748,469729358198866,471061142064746,
    467882995444482,460334826090442,448674272886264,433262517377134,414546298124268,
    393037888923030,369293208342686,343888826877286,317400032694536,290381437192242,
    263350133017632,236771580837112,211049226433308,186518349485496,163443500334104,
    142018787177398,122370909117174,104564795092898,88611031278358,74474062988422,62080672501834,
    51328612273230,42095069000904,34244367909482,27634521925692,22122663093288,17569547428976,
    13843141832368,10821159379826,8392541643698,6458123141450,4930774961948,3735181647854,
    2807258450688,2093222375196,1548442972716,1136263637968,826925215332,596603554228,
    426501626594,301959098896,211611008278,146666867214,100358579076,67545621684,44418895366,
    28240387144,17087605206,9610615806,4829967606,1999312782,536946986]]
private def rkmC_w512_s2b_6 : List ℤ := pzigCat
  [
   [218075773,888302189,2168809859,4363265571,7462471665,10956959667,13851818695,13827088247,
    5608102619,20211100568,78495231326,192339424048,396293213416,739173163678,1287665463118,
    2130663125088,3382507761796,5185060740384,7709422264904,11155926865502,15750871779432,
    21740706800106,29384145171022,38940883154352,50656695314348,64746582202486,81376892840172,
    100646456580290,122568267208262,147054280350416,173904506719446,202800693662556,
    233305945253792,264871927002884,296853639510098,328530560698892,359133373369088,
    387875555309596,413987893420324,436753183847808,455538936601652,469826504693288,
    479234810392672,483536740761392,482667174517606,476722699260694,465953452614256,
    450747576972270,431609316345248,409132583468824,383972089522692,356813787004630,
    328346082257066,299233325019820,270093057349292,241478025139748,213863269263698,
    187638195848588,163103429579114,140472139452050,119875202528554,101369241157540,
    84946512074200,70545827829202,58063897607818,47366522612014,38299061259122,30695671471992,
    24387074919090,19206832317370,14996230047890,11607860129440,8907944965220,6777506278456,
    5112583855518,3823782812554,2835406986642,2084343709506,1518776343218,1096770956976,
    784807521514,556360087108,390618220382,271433163854,186383185352,126224306280,83842695874,
    54562088688,34336453140,20768906928,12105510090,6650592552,3247159780,1279826202,322625872]]
private def rkmC_w512_s2b_7 : List ℤ := pzigCat
  [
   [284150048,707467982,834089380,371382832,1159346401,4768587881,11486218793,21658338175,
    34616888657,47789656655,54613752993,41930128585,12922372068,146211519520,413282969448,
    894237053494,1699033612558,2972213313178,4896897499402,7696647781674,11633976417856,
    17005141608786,24130844231004,33342113592030,44961304185090,59279246856550,76529990282722,
    96864477030464,120324939528558,146822581760580,176121192605670,207828632034450,
    241397511576146,276136118092476,311230034783230,345773694847942,378809885348224,
    409374642532546,436544719984070,459484546179256,477489079459920,490019488276302,
    496728836480590,497476988028222,492333004297316,481566684778544,465627884963180,
    445118501038416,420756210585254,393336298456938,363691176515656,332651805613792,
    301013303797508,269505050007716,238768793779572,209343443530278,181656568001514,
    156023409798406,132650912324538,111646316549462,93030026612006,76749630916618,62694933348566,
    50712809168618,40621963353350,32224273539638,25316740786494,19699519564676,15182717432304,
    11590790309888,8765010836300,6565655522790,4871960379794,3580917918064,2606879991700,
    1879567590384,1342336623734,949186336246,664523211482,460354842136,315078753752,212794475652,
    141544598636,92399280804,59026867142,36808665316,22325417204,12818529492,7025373380,
    3446519604,1329361474,317773580]]
private def rkmC_w512_s2b_8 : List ℤ := pzigCat
  [
   [430819082,1600645716,3219154550,4572225376,4869722216,2486395874,4626368771,18910499721,
    43063969251,78100494163,121164001245,161156882319,173863876753,115553847819,85549368438,
    537705340960,1394320315166,2861470920558,5201958740094,8736701814606,13838616612808,
    20920593927178,30415315933808,42748725882070,58305828187828,77393672364772,100201523234718,
    126763820165638,156930226237620,190343885592278,226433689376008,264422257825778,
    303348954555000,342110418629668,379512591168910,414334074546424,445392955855378,
    471614963452984,492095037975112,506148429005790,513347108664070,513539115299196,
    506850565697096,493668939154352,474611370560492,450481964560078,422217991298712,
    390834821206090,357370525670428,322834896196742,288164472191138,254188779588108,
    221606522513210,190971464464344,162690181277870,137026678746098,114114591159630,
    93974033784138,76532061198882,61642416037470,49107602747216,38697530154474,30165590804906,
    23262815581642,17748614442380,13397615006266,10006297758906,7394378113656,5406469774680,
    3911339522118,2799825883670,1982885204050,1389375167526,962563886304,659193786494,
    445839639404,297411073462,195481663502,126365856232,80037503050,49718389412,29942287502,
    17385965904,9580683582,4766911500,2090439194,511608708]]
private def rkmC_w512_s2b_9 : List ℤ := pzigCat
  [
   [382411067,680990689,672939481,193145644,2070129224,5558064864,10361401240,15622958940,
    18187938040,12761918172,7897760497,52470647087,127955778903,235467013599,362653941637,
    473570959401,494868522371,302768512783,292750015386,1560890821192,3857545307176,
    7624912536168,13382360714066,21702691632818,33176763498988,48366611537664,67748525691020,
    91651453891728,120199645607652,153260850721886,190412521523964,230927827975430,
    273786562667162,317714174427526,361245006878064,402804733338084,440808905252968,
    473763869911870,500365655124074,519584309663500,530727668762742,533479815874914,
    527910281998516,514454956146828,493873653081842,467185519088074,435593366787726,
    400401361325680,362933301668584,324461135794580,286142910004422,248978511780722,
    213780339019334,181160451853216,151533100483746,125127470620970,102011586527058,
    82119011611312,65279912409486,51250720633804,39741118514074,30439397315204,23030955887588,
    17214545875598,12711815872818,9273874131186,6684762046006,4760693004924,3349839622528,
    2328510933458,1598581399616,1083640301788,724765020820,478094345016,310584489466,
    198572474708,124654220606,76774124890,46000734552,26720976516,14887573274,7619481634,
    3518699706,1224747664,250970262]]
private def rkmC_w512_s2b_10 : List ℤ := pzigCat
  [
   [283003010,551504912,369747352,436225155,2027132239,3672153569,4615421241,3087822617,
    3124857914,15287335642,33266404580,52361997322,63272583164,49595131040,11454023751,
    143815335275,364716963447,668767100819,1008684066373,1268897439295,1238533019673,
    586392625615,1156452386836,4598775027598,10474307966800,19601235278174,32820546568416,
    50912130912016,74497266727208,103939036827690,139250317106378,180026896077596,
    225412518231282,274108310682632,324427523468784,374393630549530,421875018301902,
    464739004065236,501014419714590,529040342621614,547590212881422,555955054558228,
    553981521767014,542060490034512,521071907602458,492293505277314,457285698460094,
    417766185981524,375484033607758,332109177466678,289140003253036,247839431280160,
    209196919361718,173917521162636,142431868692354,114925225601798,91375277154894,
    71598419859054,55295263715994,42094810503596,31590873403422,23373589029062,17050902755998,
    12264770578350,8699011195576,6084064376366,4195597018372,2852551252302,1911508626950,
    1262212505116,820793803516,525413508124,330613583246,204347632218,123715372844,73266014744,
    42091634792,23302546672,12084678634,5734849990,2307578244,473961942]]
private def rkmC_w512_s2b_11 : List ℤ := pzigCat
  [
   [526984451,556343815,179392181,798665946,1878706914,2549537504,1912028150,973137263,
    6424523919,13323095967,18200307921,15647258067,1388813352,37737852234,92930763018,
    153934088484,191014880732,154848919052,17229778821,385580713241,979069575835,1754319486385,
    2543597851509,3003993618337,2573595309295,452827504803,4380758010772,13112721169562,
    26987804024534,47164045163484,74544288801502,109602679430146,152237494174740,201672769447472,
    256432248369978,314393406034160,372925944234698,429097586746762,479927098224978,
    522650006079400,554966983164104,575240784887938,582623409714574,577098259464154,
    559440161466058,531100569407878,494040140765134,450529992792110,402948663962366,
    353595951026472,304540053066758,257509834813042,213832080605876,174416548993518,
    139775705580100,110074945552804,85198355463094,64822298422514,48486891170590,35660037468788,
    25789404201550,18341270599458,12828504181620,8824290877750,5969307054216,3970685445712,
    2596611126476,1668891242868,1053817818892,653176242516,397309319308,236648118550,
    137699407524,78092796410,42830501942,22446263032,11084218750,4700496210,1593130398,279820260]]
private def rkmC_w512_s2b_12 : List ℤ := pzigCat
  [
   [304632896,398286180,25115140,973233651,1792333847,1899516659,570720377,2299504524,6420565284,
    9607948530,8610552316,560782519,19592403915,44607899441,63490112197,56259812039,87184375,
    120237239740,294200230400,468923491514,537397950370,347101942616,267102786877,1416076758765,
    3061857038563,4906709298019,6290107889129,6125863006657,2908829688157,5185979269830,
    20108332206750,43655107691620,77150279436188,121131198837452,175105533847070,237430188692576,
    305347562650006,375188647473368,442718886580084,503578888345028,553757300757956,
    590019946846436,610238380992550,613570762727724,600480602429678,572602740760868,
    532487813038820,483273944859728,428336153934350,370957936268866,314066977119312,
    260050844763520,210663102064780,167012078438066,129613982891218,98491599177622,
    73294956007012,53425128987120,38147838602998,26686382227960,18290517220414,12282257385164,
    8080298151616,5207411214988,3286696390642,2030937972638,1228127621960,726245404932,
    419441320832,236180649248,129363411110,68629111640,34882355856,16552907390,6935758332,
    2249173612,347894650]]
private def rkmC_w512_s2b_13 : List ℤ := pzigCat
  [
   [238828419,67153905,614062680,1539175358,1705726582,160470582,2844785563,6497440807,
    7764358985,3520605725,8505783958,25913346498,38491094924,30415865170,12565424063,90681497539,
    177158043689,214455495953,124633154865,155184798800,619920789836,1139630518696,1429289584304,
    1080588995090,325312186861,3018887246177,6788724919401,10737440721083,13127763882377,
    11401688791411,2423298894285,17057037657272,49780479823270,97319173696246,159523568990500,
    234216099275048,317226645915738,402791316479754,484255710814326,554956686768754,
    609117462433136,642593379220186,653344392636928,641570130415890,609512828046804,
    560995867420098,500804328615170,434026039674366,365460560886426,299172839878268,
    238227715014094,184603978048614,139258771731678,102296134214906,73188799502368,
    51008641797670,34633148081462,22908427891170,14761441563516,9264743210668,5662238149584,
    3368500472920,1949407511314,1096813442144,599368761526,317313267114,162241476990,79476154122,
    37013249564,15980144564,6164552678,1740934442,219775052]]
private def rkmC_w512_s2b_14 : List ℤ := pzigCat
  [
   [310396995,1523180917,2287687853,732938891,3681627226,8291779152,8038999014,1145920857,
    18235950057,33424512251,29363781909,8829921548,77136547976,138810072314,128785252294,
    12799767989,285373690087,577773146435,663527190217,277819192013,720967898118,2154166014132,
    3388720418346,3385016909826,1007875412186,4413785839255,12412509661249,20825510542689,
    25619592909223,21290186511739,1863002156033,37680450683036,99904534178350,183778331157088,
    284253107741024,392739838680130,498414892581734,590059887263828,657997903150758,
    695678626487016,700584600053818,674315043082586,621923527767686,550738312155228,
    468982992570206,384496778115814,303776914873590,231445133681606,170135620367674,
    120710960798090,82677654736812,54669330385488,34895549673826,21496354982810,12774680855618,
    7319583469872,4040517218046,2146325371940,1095399129280,535859175520,250315495292,
    110991297414,46184559504,17529669232,5634443462,1224320982]]
private def rkmC_w512_s2b_15 : List ℤ := pzigCat
  [
   [360383814,587325954,181082469,1229148173,1369471627,267361578,2936297174,4149648822,
    692080368,7457757173,14232190341,8435882497,14489225406,41046294964,41228025070,9579808277,
    97470961381,153944309515,84612209863,147455762430,436778065610,526296027052,142933581046,
    751924726289,1742418753017,1980028648971,582016902115,2667685925768,6659118644248,
    8827335118806,5936127367702,4245959834553,20926992817345,38856996174377,48393211599785,
    37481485601437,4813551120950,84346636794630,198939503307062,337628784433344,482543948985022,
    612892456923610,709797498565002,760492837554892,760695736358656,714672027812560,
    633275637170072,530806214603756,421713080456902,317997991432070,227777832204324,
    155035603748942,100266730896230,61586541423900,35895888197260,19827275193500,10359883452540,
    5108042847550,2368881817072,1028627736386,415437393946,154476056268,51853280782,15081527490,
    3148466796]]
private def rkmC_w512_s2b_16 : List ℤ := pzigCat
  [
   [365547930,127353321,1557187363,1426068807,1934743950,5173322332,2668768244,6682932123,
    13006173529,3613987763,20602560138,33911744710,5031008442,58830396629,90106010987,
    12504618567,153685481098,244533801846,65900974862,366116493803,681091191517,359015628433,
    727428553264,1851875730588,1653802753294,752933289697,4425292108065,6277397615577,
    2768308986715,6878020515514,18040446547434,21276659027802,7231752023646,25919145911753,
    66779496069807,91147934117935,70045324328523,17508346110656,173021460239656,374365281039534,
    581469208094226,749548971947490,843982930076304,850553522453534,777453464392014,
    649473701126440,497958273956796,351053074213786,227556394306498,135388304146404,
    73672030734638,36456451837244,16265493585564,6459823238364,2239004102808,655154703644,
    151459367604,22937872330]]
private def rkmHbWin_w512_s3 : List ℤ := altBuildHbFrom 2048 1024 18153035714 0 1024
private def rkmXsWin_w512_s3_in : List ℤ := pzigCat
  [
   [592851335,784469965,634542368,2306880508,614674482,3978762735,3955167007,5016302284,
    11223907196,1252075745,22266211179,15141977871,28787586566,51614116822,8730126069,
    102010929067,76628375125,117364559738,254623070692,31437277512,441483729979,510948371781,
    283113397338,1252336178477,855717854430,1354454400231,3160382721963,1262280927353,
    4309101762413,7787509282019,2152157172251,11555331583957,20021534413417,7251291003205,
    26438118440478,54163069317176,37327806561942,38896777386626,137100502881466,175664193261720,
    76689918338390,176938910016508,518108405475234,825750674685770,989515571681048,
    965509179823160,789268504372094,544591245337984,315027995261230,149317103535611,
    55044950606523,13733180300158]]
private def rkmXsWin_w512_s3_out : List ℤ := pzigCat
  [
   [656210552,2235947347,5096574402,9836148469,24106646556,58311660927,111676356512,194737965231,
    335966267932,520244501351,655495104412,660992008939,485348208780,44074524919,581351262505,
    837623186764,168903180871,1098999572319,2097170782744,2371071282349,1507947108754,
    826692434282,3013200950653,2529493648318,82225113901,1646997950701,1795435941980,
    296854909607,3859186718,3985640144851,1947831022010,17713145663962,37464512151407,
    6491404621356,54938840024936,64095341188193,33868860983521,56543162673238,30853032090985,
    76710357040207,96166397039996,132700275561012,76819567628770,153188345332119,273959948489220,
    608872676772326,1105411670684450,1312306331184310,712534293751766,161499826747178]]
private def rkmPhb_w512_s3 : List ℕ := uNatCatN
  [
   [303816802642612,301560030154645,299285373284791,296992434420145,294680800218502,
    292350040730013,289999708454784,287629337330634,285238441644574,282826514860862,
    280393028357683,277937430063610,275459142983930,272957563605789,270432060169742,
    267881970793768,265306601434078,262705223665001,260077072257956,257421342536827,
    254737187483962,252023714567470,249279982256271,246504996184514,243697704921267,
    240856995294651,237981687211719,235070527905956,232122185533174,229135242023262,
    226108185079299,223039399196352,219927155549033,216769600568659,213564742996305,
    210310439155592,207004376136598,203644052516922,200226756164208,196749538561253,
    193209184963796,189602179533230,185924664369688,182172391088358,178340663209883,
    174424267140902,170417388854933,166313512476900,162105295722372,157784415388274,
    153341373594127,148765251853266,144043394704167,139160996551918,134100552862462,
    128841116949405,123357270910008,117617663620680,111582869891493,105202140510798,
    98408247870123,91108854698369,83171021056505,74390706241113,64424425551521,52602423424612,
    37195565748255]]
private def rkmHbWin_w512_s4 : List ℤ := altBuildHbFrom 2048 1024 17553850000 0 1024
private def rkmXsWin_w512_s4_in : List ℤ := pzigCat
  [
   [656210552,2235947347,5096574402,9836148469,24106646556,58311660927,111676356512,194737965231,
    335966267932,520244501351,655495104412,660992008939,485348208780,44074524919,581351262505,
    837623186763,168903180871,1098999572319,2097170782743,2371071282349,1507947108753,
    826692434281,3013200950653,2529493648317,82225113901,1646997950702,1795435941980,
    296854909608,3859186718,3985640144852,1947831022010,17713145663962,37464512151408,
    6491404621356,54938840024936,64095341188194,33868860983522,56543162673238,30853032090986,
    76710357040208,96166397039996,132700275561012,76819567628770,153188345332120,273959948489220,
    608872676772326,1105411670684450,1312306331184310,712534293751766,161499826747178]]
private def rkmXsWin_w512_s4_out : List ℤ := pzigCat
  [
   [439363341,2211330774,5489235887,11299808662,21526107357,38862561442,67620422701,113282691250,
    179737796219,268149339986,372520049843,476684666142,552454174095,562425320830,472723123341,
    280412886464,44715440695,115581808301,92757142172,103612538818,303370702443,269895673932,
    72090597116,430199221163,362147595342,17237049328,51119756242,593921747591,331272331512,
    803103057060,741729081791,638055367457,1340989341812,638442284317,572226675965,2198812314233,
    2438352169879,5848538837548,16233982132639,12444861986940,10955844639081,8340588720101,
    26117952470032,23983331076201,7982954530674,2912977495253,12843324517634,5435877706611,
    30960220934730,21672515790148,81466775083940,30645571432060,27861857072390,67464368689444,
    94203180624282,122718860732008,95172221111900,92387085723695,680799993833680,
    1540766767474530,1050954953996552]]
private def rkmPhb_w512_s4 : List ℕ := uNatCatN
  [
   [310665952413769,308609767230606,306538901419932,304453067557690,302351968093608,
    300235294849581,298102728485670,295953937931125,293788579777595,291606297631400,
    289406721421450,287189466659034,284954133645327,282700306622035,280427552860100,
    278135421680874,275823443403523,273491128211766,271137964932256,268763419716043,
    266366934613549,263947926032350,261505783065779,259039865678864,256549502736443,
    254033989856330,251492587068202,248924516256261,246328958360763,243705050310032,
    241051881650545,238368490837947,235653861146377,232906916146940,230126514698567,
    227311445385391,224460420324026,221572068251264,218644926787272,215677433750841,
    212667917380730,209614585289862,206515511945722,203368624429259,200171686173846,
    196922278322697,193617778264075,190255334803858,186831839308347,183343891987860,
    179787762282031,176159342034464,172454089784688,168666964026848,164792342640745,
    160823924823830,156754610641877,152576351619657,148279963377660,143854887820801,
    139288887212275,134567644652345,129674233387272,124588398127707,119285559951477,
    113735402556145,107899802077412,101729684406518,95160040948011,88101582250155,80425756384469,
    71935257514172,62297938498264,50866150707785,35967834366483]]
private def rkmHbWin_w512_s5 : List ℤ := altBuildHbFrom 2048 1024 17335642857 0 1024
private def rkmXsWin_w512_s5_in : List ℤ := pzigCat
  [
   [439363341,2211330774,5489235887,11299808662,21526107357,38862561442,67620422701,113282691250,
    179737796219,268149339986,372520049843,476684666142,552454174095,562425320830,472723123341,
    280412886464,44715440695,115581808301,92757142172,103612538818,303370702443,269895673932,
    72090597116,430199221163,362147595341,17237049328,51119756242,593921747591,331272331512,
    803103057059,741729081791,638055367457,1340989341811,638442284317,572226675965,2198812314234,
    2438352169879,5848538837547,16233982132639,12444861986939,10955844639081,8340588720101,
    26117952470031,23983331076201,7982954530673,2912977495253,12843324517633,5435877706611,
    30960220934729,21672515790147,81466775083939,30645571432059,27861857072389,67464368689443,
    94203180624281,122718860732007,95172221111899,92387085723696,680799993833680,
    1540766767474530,1050954953996552]]
private def rkmXsWin_w512_s5_out : List ℤ := pzigCat
  [
   [786370421,2595168632,6120661503,11638434170,20809985445,35417930084,57790462989,91141260118,
    138537514933,201614208282,279481770779,365674201978,447869641351,506926112764,520215764609,
    468836421940,346652907683,173281599586,1537480408,109512276359,96535604570,33003319006,
    192683637225,252425171774,135550519839,89498226945,230673291492,147419418947,43539499029,
    5109307244,393693039486,694928621533,350649923398,247436768366,322370142535,380627144820,
    699592184013,369771681992,1072993006663,1411623868136,1911172187067,1517876955934,
    1982269037741,1459621586744,3961777068193,269254262177,1097248868947,6854418024732,
    237489382277,13884991211291,13084724986161,3703853167914,24113188236671,11842365654829,
    37330172959749,5941505814796,27597122945001,1374499282975,9488011129246,44929284853485,
    51917147468975,37859361835433,31503820978941,59150060295251,93644799723401,156195922792683,
    350479792497749,945044046719624,1713705436605120]]
private def rkmPhb_w512_s5 : List ℕ := uNatCatN
  [
   [324469800543733,322558324777081,320634524124384,318698186706321,316749093990601,
    314787020499522,312811733500816,310822992680580,308820549797020,306804148313609,
    304773523010148,302728399570069,300668494142208,298593512875058,296503151421393,
    294397094410902,292275014888285,290136573714008,287981418924623,285809185049294,
    283619492378784,281411946182817,279186135871275,276941634094240,274677995775327,
    272394757072177,270091434257281,267767522511550,265422494622167,263055799575270,
    260666861032917,258255075682455,255819811445013,253360405528127,250876162305597,
    248366351005468,245830203184488,243266909964424,240675619002210,238055431161920,
    235405396851900,232724511984930,230011713512910,227265874479987,224485798529074,
    221670213786117,218817766033704,215927011070452,212996406134201,210024300244921,
    207008923296212,203948373691330,200840604279118,197683406295102,194474390950648,
    191210968234992,187890322396434,184509383443855,181064793849436,177552869426394,
    173969553085709,170310359820573,166570310794720,162743853775002,158824766282436,
    154806036640149,150679716421322,146436735414974,142066666770834,137557424876079,
    132894870800465,128062288202133,123039673579736,117802753545009,112321588649240,
    106558528935532,100465110322050,93977132317538,87006415403190,79426005644644,71041049860402,
    61523529740385,50233847399887,35520727983723]]
private def rkmHbWin_w512_s6 : List ℤ := altBuildHbFrom 2048 1024 16750800000 0 1024
private def rkmXsWin_w512_s6_in : List ℤ := pzigCat
  [
   [786370421,2595168632,6120661503,11638434170,20809985445,35417930084,57790462989,91141260118,
    138537514933,201614208282,279481770779,365674201978,447869641351,506926112764,520215764609,
    468836421940,346652907683,173281599586,1537480408,109512276359,96535604570,33003319006,
    192683637225,252425171774,135550519839,89498226945,230673291492,147419418947,43539499029,
    5109307244,393693039486,694928621533,350649923398,247436768365,322370142536,380627144820,
    699592184013,369771681992,1072993006664,1411623868136,1911172187068,1517876955934,
    1982269037742,1459621586743,3961777068193,269254262177,1097248868948,6854418024731,
    237489382277,13884991211291,13084724986161,3703853167914,24113188236672,11842365654829,
    37330172959749,5941505814796,27597122945002,1374499282976,9488011129246,44929284853486,
    51917147468976,37859361835434,31503820978942,59150060295252,93644799723402,156195922792684,
    350479792497750,945044046719624,1713705436605120]]
private def rkmXsWin_w512_s6_out : List ℤ := pzigCat
  [
   [712752647,2342815664,5511865359,10416805978,18254886073,30152483662,47940845155,74070836506,
    110504829277,159403274928,220934368793,293061657236,369645200977,439242803618,487099940293,
    495988116040,452032090681,351252990046,206047997819,48619240026,73782141048,115765333705,
    57694716208,71012114572,193188831489,219684281968,109667126935,81697788361,225044907266,
    217676462479,96155828314,39823775719,204370215676,504438331115,621488280970,355170480473,
    51518851781,209648782136,238341571587,466333720940,378497704355,414309093615,535647205330,
    34830740404,142289457586,793607974111,402758009630,1003614153576,277702753688,1415417746238,
    6838365552520,5096539759927,2165255532952,2227462996903,2164119139215,470064198731,
    5819072632248,18998082196429,25140699288501,21917321396036,18229672543072,31065498300253,
    17160571710779,14898793330354,1768640795300,1332441378511,26328147762298,51896892152362,
    39012881405116,32577162821712,50362930588474,87382585508394,79645798031716,406052291058892,
    1951721218322830]]
private def rkmPhb_w512_s6 : List ℕ := uNatCatN
  [
   [324365909853829,322586403649457,320796095783049,318994814942054,317182384795307,
    315358623787838,313523344924777,311676355543642,309817457074227,307946444785266,
    306063107516969,304167227398448,302258579548993,300336931762037,298402044170580,
    296453668892725,294491549655855,292515421397869,290525009843729,288520031055432,
    286500190953344,284465184806624,282414696690281,280348398906139,278265951364746,
    276167000924949,274051180687550,271918109239064,269767389841224,267598609561376,
    265411338338426,263205127978406,260979511073049,258733999834067,256468084834922,
    254181233651002,251872889387951,249542469086739,247189361992584,244812927673280,
    242412493970577,239987354766165,237536767541330,235059950706510,232556080673658,
    230024288640495,227463657051205,224873215692895,222251937380925,219598733178918,
    216912447090616,214191850150463,211435633827523,208642402642624,205810665880908,
    202938828260531,200025179392180,197067881832213,194064957493065,191014272126106,
    187913517531928,184760191077505,181551572004572,178284693892580,174956312484740,
    171562867885612,168100439877913,164564694762992,160950821672791,157253455686734,
    153466584250122,149583432235091,145596319366438,141496481429800,137273843339704,
    132916727208867,128411471104202,123741922633697,118888753142906,113828508141245,
    108532258230387,102963623628908,97075775260510,90806678529892,84071128781201,76746455053732,
    68644377818450,59447944934970,48539136273579,34322385112444]]
private def rkmHbWin_w512_s7 : List ℤ := altBuildHbFrom 2048 1024 16900000000 0 1024
private def rkmXsWin_w512_s7_in : List ℤ := pzigCat
  [
   [712752647,2342815664,5511865359,10416805978,18254886073,30152483662,47940845155,74070836506,
    110504829277,159403274928,220934368793,293061657236,369645200977,439242803618,487099940293,
    495988116040,452032090681,351252990046,206047997819,48619240026,73782141048,115765333705,
    57694716208,71012114572,193188831489,219684281968,109667126935,81697788361,225044907266,
    217676462479,96155828314,39823775719,204370215676,504438331115,621488280970,355170480473,
    51518851782,209648782136,238341571588,466333720940,378497704355,414309093615,535647205330,
    34830740404,142289457586,793607974111,402758009630,1003614153576,277702753688,1415417746238,
    6838365552520,5096539759927,2165255532952,2227462996903,2164119139215,470064198731,
    5819072632247,18998082196429,25140699288501,21917321396036,18229672543072,31065498300254,
    17160571710780,14898793330353,1768640795300,1332441378511,26328147762297,51896892152361,
    39012881405116,32577162821712,50362930588474,87382585508394,79645798031716,406052291058892,
    1951721218322830]]
private def rkmXsWin_w512_s7_out : List ℤ := pzigCat
  [
   [777552876,2480681349,5677197988,10498775589,18115763852,29493021263,46215780578,70406929507,
    103815500870,148475243057,204636490408,270954337057,342902235272,411620984789,464904212924,
    487582519251,466314355974,393565617729,273316782400,126267431483,12444023803,100475344470,
    105431960213,25006234540,100904621108,199017108583,197820341382,77381770455,103843806387,
    234307533120,232315647909,130798496740,74087842307,193457823794,444951792531,591791458466,
    428431082079,57509362426,173124877034,128212177379,72984502342,180488946827,296176362158,
    739790313588,441796440573,45406119855,220357098263,671521660506,33093148961,736730753973,
    157442248331,2415679619464,4621759640845,7353882125904,631042820662,722004760144,
    752439384888,2270102465509,1366531106897,47756179134,3910781510858,35341510196589,
    9627745626357,4183942870540,20764926342532,38716434359468,3706766091406,3765615744289,
    3594398040668,5414486061326,66048747957103,1804006995827,24549806887504,32039198712870,
    84895977463244,45875439627946,77401040441612,1993798716936658]]
private def rkmPhb_w512_s7 : List ℕ := uNatCatN
  [
   [332577387361919,330813735357889,329039675535337,327255049103906,325459692771439,
    323653438566130,321836113649540,320007540119916,318167534805171,316315909044866,
    314452468460465,312577012713091,310689335247928,308789223024379,306876456230972,
    304950807983976,303012044008550,301059922301192,299094192772109,297114596866057,
    295120867160016,293112726935969,291089889726867,289052058833698,286998926811373,
    284930174920944,282845472545416,280744476566147,278626830696542,276492164769419,
    274340093974030,272170218038344,269982120351700,267775367022435,265549505864499,
    263304065306405,261038553215114,258752455626608,256445235373948,254116330602501,
    251765153160797,249391086854041,246993485545671,244571671090500,242124931080795,
    239652516384201,237153638449508,234627466352940,232073123553762,229489684323457,
    226876169807408,224231543671803,221554707281068,218844494342443,216099664943932,
    213318898899464,210500788300281,207643829153673,204746411968561,201806811121131,
    198823172801562,195793501303388,192715643368150,189587270237218,186405856986522,
    183168658623903,179872682306791,176514654881683,173090984745017,169597716761989,
    166030478633532,162384416641006,158654118078290,154833516836633,150915777441856,
    146893151210258,142756795864295,138496546579328,134100621452698,129555236863972,
    124844096551178,119947699698827,114842382906312,109498959100075,103880724462625,
    97940432809335,91615497000452,84819953459077,77430038589684,69255795850455,59977449996477,
    48971476169705,34628095876036]]
private def rkmWalksHi_w512_r1024 : List RkmWinSegWalk := [
  ⟨512, rkmHbWin_w512_s0, 0, rkmXsWin_w512_s0_in, 101, rkmXsWin_w512_s0_out, 21014282865⟩,
  ⟨1024, rkmHbWin_w512_s1, 101, rkmXsWin_w512_s1_in, 457, rkmXsWin_w512_s1_out, 46773028316⟩,
  ⟨1024, rkmHbWin_w512_s2a, 457, rkmXsWin_w512_s2a_in, 973, rkmXsWin_w512_s2b_out, 86249501680⟩,
  ⟨1024, rkmHbWin_w512_s3, 973, rkmXsWin_w512_s3_in, 975, rkmXsWin_w512_s3_out, 1681245957⟩,
  ⟨1024, rkmHbWin_w512_s4, 975, rkmXsWin_w512_s4_in, 964, rkmXsWin_w512_s4_out, 990071107⟩,
  ⟨1024, rkmHbWin_w512_s5, 964, rkmXsWin_w512_s5_in, 956, rkmXsWin_w512_s5_out, 674085209⟩,
  ⟨1024, rkmHbWin_w512_s6, 956, rkmXsWin_w512_s6_in, 950, rkmXsWin_w512_s6_out, 481111300⟩,
  ⟨1024, rkmHbWin_w512_s7, 950, rkmXsWin_w512_s7_in, 947, rkmXsWin_w512_s7_out, 261586222⟩
  ]
private theorem rkmHd {a : Bool} {s : List Bool} (h : rkmAllTrueF (a :: s) = true) :
    a = true := (rkmAllTrueF_cons h).1
private theorem rkmTl {a : Bool} {s : List Bool} (h : rkmAllTrueF (a :: s) = true) :
    rkmAllTrueF s = true := (rkmAllTrueF_cons h).2
private theorem rkmWP0 {a : Bool} {s : List Bool} (h : rkmAllTrueF (a :: s) = true) :
    a = true := rkmHd h
private theorem rkmWP1 {a b : Bool} {s : List Bool} (h : rkmAllTrueF (a :: b :: s) = true) :
    b = true := rkmHd (rkmTl h)
private theorem rkmWP2 {a b c : Bool} {s : List Bool}
    (h : rkmAllTrueF (a :: b :: c :: s) = true) : c = true := rkmHd (rkmTl (rkmTl h))
private theorem rkmWP3 {a b c d : Bool} {s : List Bool}
    (h : rkmAllTrueF (a :: b :: c :: d :: s) = true) :
    d = true := rkmHd (rkmTl (rkmTl (rkmTl h)))
private theorem rkmWP4 {a b c d e : Bool} {s : List Bool}
    (h : rkmAllTrueF (a :: b :: c :: d :: e :: s) = true) :
    e = true := rkmHd (rkmTl (rkmTl (rkmTl (rkmTl h))))
private theorem rkmWT5 {a b c d e : Bool} {s : List Bool}
    (h : rkmAllTrueF (a :: b :: c :: d :: e :: s) = true) :
    rkmAllTrueF s = true := rkmTl (rkmTl (rkmTl (rkmTl (rkmTl h))))
private abbrev rkmBP_00 : Prop := rkmAllTrueF [
  bWinChk 0 80 100000000 512 rkmPhb_w512_s0
  0 rkmXsWin_w512_s0_in 2 rkmC_w512_s0_1 3679265124,
  bWinChk 0 34 100000000 512 rkmPhb_w512_s0
  2 rkmC_w512_s0_1 20 rkmC_w512_s0_2 4853499170] = true
private theorem rkmBK_00 : rkmBP_00 := by decide +kernel
private abbrev rkmBP_01 : Prop := rkmAllTrueF [
  bWinChk 4 28 100000000 512 (drN 4 rkmPhb_w512_s0)
  20 rkmC_w512_s0_2 44 rkmC_w512_s0_3 4637552183,
  bWinChk 28 25 100000000 512 (drN 28 rkmPhb_w512_s0)
  44 rkmC_w512_s0_3 70 rkmC_w512_s0_4 3488313154] = true
private theorem rkmBK_01 : rkmBP_01 := by decide +kernel
private abbrev rkmBP_02 : Prop := rkmAllTrueF [
  bWinChk 54 24 100000000 512 (drN 54 rkmPhb_w512_s0)
  70 rkmC_w512_s0_4 101 rkmXsWin_w512_s0_out 4355653234,
  bWinChk 85 22 100000000 1024 rkmPhb_w512_s1
  101 rkmXsWin_w512_s1_in 127 rkmC_w512_s1_1 3558104943] = true
private theorem rkmBK_02 : rkmBP_02 := by decide +kernel
private abbrev rkmBP_03 : Prop := rkmAllTrueF [
  bWinChk 111 21 100000000 1024 (drN 26 rkmPhb_w512_s1)
  127 rkmC_w512_s1_1 154 rkmC_w512_s1_2 3460131920,
  bWinChk 138 21 100000000 1024 (drN 53 rkmPhb_w512_s1)
  154 rkmC_w512_s1_2 183 rkmC_w512_s1_3 4000903641] = true
private theorem rkmBK_03 : rkmBP_03 := by decide +kernel
private abbrev rkmBP_04 : Prop := rkmAllTrueF [
  bWinChk 167 20 100000000 1024 (drN 82 rkmPhb_w512_s1)
  183 rkmC_w512_s1_3 211 rkmC_w512_s1_4 3941200349,
  bWinChk 195 20 100000000 1024 (drN 110 rkmPhb_w512_s1)
  211 rkmC_w512_s1_4 240 rkmC_w512_s1_5 4099382594] = true
private theorem rkmBK_04 : rkmBP_04 := by decide +kernel
private abbrev rkmBP_05 : Prop := rkmAllTrueF [
  bWinChk 224 20 100000000 1024 (drN 139 rkmPhb_w512_s1)
  240 rkmC_w512_s1_5 270 rkmC_w512_s1_6 4253503254,
  bWinChk 254 20 100000000 1024 (drN 169 rkmPhb_w512_s1)
  270 rkmC_w512_s1_6 300 rkmC_w512_s1_7 3643799694] = true
private theorem rkmBK_05 : rkmBP_05 := by decide +kernel
private abbrev rkmBP_06 : Prop := rkmAllTrueF [
  bWinChk 284 20 100000000 1024 (drN 199 rkmPhb_w512_s1)
  300 rkmC_w512_s1_7 330 rkmC_w512_s1_8 3558061952,
  bWinChk 314 20 100000000 1024 (drN 229 rkmPhb_w512_s1)
  330 rkmC_w512_s1_8 361 rkmC_w512_s1_9 3856209037] = true
private theorem rkmBK_06 : rkmBP_06 := by decide +kernel
private abbrev rkmBP_07 : Prop := rkmAllTrueF [
  bWinChk 345 21 100000000 1024 (drN 260 rkmPhb_w512_s1)
  361 rkmC_w512_s1_9 393 rkmC_w512_s1_10 4137820146,
  bWinChk 377 21 100000000 1024 (drN 292 rkmPhb_w512_s1)
  393 rkmC_w512_s1_10 424 rkmC_w512_s1_11 4086195349] = true
private theorem rkmBK_07 : rkmBP_07 := by decide +kernel
private abbrev rkmBP_08 : Prop := rkmAllTrueF [
  bWinChk 408 22 100000000 1024 (drN 323 rkmPhb_w512_s1)
  424 rkmC_w512_s1_11 457 rkmXsWin_w512_s1_out 4177715437,
  bWinChk 441 20 100000000 1024 rkmPhb_w512_s2a
  457 rkmXsWin_w512_s2a_in 488 rkmC_w512_s2a_1 3864015609] = true
private theorem rkmBK_08 : rkmBP_08 := by decide +kernel
private abbrev rkmBP_09 : Prop := rkmAllTrueF [
  bWinChk 472 21 100000000 1024 (drN 31 rkmPhb_w512_s2a)
  488 rkmC_w512_s2a_1 519 rkmC_w512_s2a_2 3970263401,
  bWinChk 503 21 100000000 1024 (drN 62 rkmPhb_w512_s2a)
  519 rkmC_w512_s2a_2 551 rkmC_w512_s2a_3 4403330485] = true
private theorem rkmBK_09 : rkmBP_09 := by decide +kernel
private abbrev rkmBP_10 : Prop := rkmAllTrueF [
  bWinChk 535 21 100000000 1024 (drN 94 rkmPhb_w512_s2a)
  551 rkmC_w512_s2a_3 582 rkmC_w512_s2a_4 3966882462,
  bWinChk 566 22 100000000 1024 (drN 125 rkmPhb_w512_s2a)
  582 rkmC_w512_s2a_4 614 rkmC_w512_s2a_5 4313208933] = true
private theorem rkmBK_10 : rkmBP_10 := by decide +kernel
private abbrev rkmBP_11 : Prop := rkmAllTrueF [
  bWinChk 598 23 100000000 1024 (drN 157 rkmPhb_w512_s2a)
  614 rkmC_w512_s2a_5 646 rkmXsWin_w512_s2a_out 4532530346,
  bWinChk 630 18 100000000 1024 rkmPhb_w512_s2b
  646 rkmXsWin_w512_s2b_in 672 rkmC_w512_s2b_1 3240982485] = true
private theorem rkmBK_11 : rkmBP_11 := by decide +kernel
private abbrev rkmBP_12 : Prop := rkmAllTrueF [
  bWinChk 656 19 100000000 1024 (drN 26 rkmPhb_w512_s2b)
  672 rkmC_w512_s2b_1 698 rkmC_w512_s2b_2 3681923785,
  bWinChk 682 20 100000000 1024 (drN 52 rkmPhb_w512_s2b)
  698 rkmC_w512_s2b_2 724 rkmC_w512_s2b_3 4052247316] = true
private theorem rkmBK_12 : rkmBP_12 := by decide +kernel
private abbrev rkmBP_13 : Prop := rkmAllTrueF [
  bWinChk 708 20 100000000 1024 (drN 78 rkmPhb_w512_s2b)
  724 rkmC_w512_s2b_3 751 rkmC_w512_s2b_4 4769820658,
  bWinChk 735 21 100000000 1024 (drN 105 rkmPhb_w512_s2b)
  751 rkmC_w512_s2b_4 774 rkmC_w512_s2b_5 4230791683] = true
private theorem rkmBK_13 : rkmBP_13 := by decide +kernel
private abbrev rkmBP_14 : Prop := rkmAllTrueF [
  bWinChk 758 22 100000000 1024 (drN 128 rkmPhb_w512_s2b)
  774 rkmC_w512_s2b_5 799 rkmC_w512_s2b_6 2697342782,
  bWinChk 783 22 100000000 1024 (drN 153 rkmPhb_w512_s2b)
  799 rkmC_w512_s2b_6 821 rkmC_w512_s2b_7 3597818019] = true
private theorem rkmBK_14 : rkmBP_14 := by decide +kernel
private abbrev rkmBP_15 : Prop := rkmAllTrueF [
  bWinChk 805 23 100000000 1024 (drN 175 rkmPhb_w512_s2b)
  821 rkmC_w512_s2b_7 844 rkmC_w512_s2b_8 2713056952,
  bWinChk 828 24 100000000 1024 (drN 198 rkmPhb_w512_s2b)
  844 rkmC_w512_s2b_8 864 rkmC_w512_s2b_9 3704623783] = true
private theorem rkmBK_15 : rkmBP_15 := by decide +kernel
private abbrev rkmBP_16 : Prop := rkmAllTrueF [
  bWinChk 848 25 100000000 1024 (drN 218 rkmPhb_w512_s2b)
  864 rkmC_w512_s2b_9 883 rkmC_w512_s2b_10 4264140778,
  bWinChk 867 25 100000000 1024 (drN 237 rkmPhb_w512_s2b)
  883 rkmC_w512_s2b_10 900 rkmC_w512_s2b_11 3911428949] = true
private theorem rkmBK_16 : rkmBP_16 := by decide +kernel
private abbrev rkmBP_17 : Prop := rkmAllTrueF [
  bWinChk 884 26 100000000 1024 (drN 254 rkmPhb_w512_s2b)
  900 rkmC_w512_s2b_11 916 rkmC_w512_s2b_12 4147088601,
  bWinChk 900 27 100000000 1024 (drN 270 rkmPhb_w512_s2b)
  916 rkmC_w512_s2b_12 932 rkmC_w512_s2b_13 3724735974] = true
private theorem rkmBK_17 : rkmBP_17 := by decide +kernel
private abbrev rkmBP_18 : Prop := rkmAllTrueF [
  bWinChk 916 28 100000000 1024 (drN 286 rkmPhb_w512_s2b)
  932 rkmC_w512_s2b_13 948 rkmC_w512_s2b_14 3673865173,
  bWinChk 932 29 100000000 1024 (drN 302 rkmPhb_w512_s2b)
  948 rkmC_w512_s2b_14 956 rkmC_w512_s2b_15 3256253255] = true
private theorem rkmBK_18 : rkmBP_18 := by decide +kernel
private abbrev rkmBP_19 : Prop := rkmAllTrueF [
  bWinChk 940 31 100000000 1024 (drN 310 rkmPhb_w512_s2b)
  956 rkmC_w512_s2b_15 967 rkmC_w512_s2b_16 3267112991,
  bWinChk 951 33 100000000 1024 (drN 321 rkmPhb_w512_s2b)
  967 rkmC_w512_s2b_16 973 rkmXsWin_w512_s2b_out 2266037260] = true
private theorem rkmBK_19 : rkmBP_19 := by decide +kernel
private abbrev rkmBP_20 : Prop := rkmAllTrueF [
  muxIntListEq (uHb rkmPhb_w512_s0)
    (altBuildHbFrom 512 1024 51941544502 0 512),
  muxIntListEq (uHb rkmPhb_w512_s1)
    (altBuildHbFrom 1024 1024 29648891129 85 939),
  muxIntListEq (uHb rkmPhb_w512_s2a)
    (altBuildHbFrom 2048 1024 18391866913 441 583),
  muxIntListEq (uHb rkmPhb_w512_s2b)
    (altBuildHbFrom 2048 1024 18391866913 630 394),
  muxIntListEq (uHb rkmPhb_w512_s3)
    (altBuildHbFrom 2048 1024 18153035714 957 67),
  muxIntListEq (uHb rkmPhb_w512_s4)
    (altBuildHbFrom 2048 1024 17553850000 949 75),
  muxIntListEq (uHb rkmPhb_w512_s5)
    (altBuildHbFrom 2048 1024 17335642857 940 84),
  muxIntListEq (uHb rkmPhb_w512_s6)
    (altBuildHbFrom 2048 1024 16750800000 934 90),
  muxIntListEq (uHb rkmPhb_w512_s7)
    (altBuildHbFrom 2048 1024 16900000000 931 93)
  ] = true
private theorem rkmHbEq_w512_all : rkmBP_20 := by decide +kernel
private abbrev rkmBP_21 : Prop := rkmAllTrueF [
  Nat.ble (Nat.add 973 (altIntLen rkmXsWin_w512_s3_in)) (Nat.add 1024 1),
  Nat.ble (Nat.add 975 (altIntLen rkmXsWin_w512_s4_in)) (Nat.add 1024 1),
  Nat.ble (Nat.add 964 (altIntLen rkmXsWin_w512_s5_in)) (Nat.add 1024 1),
  Nat.ble (Nat.add 956 (altIntLen rkmXsWin_w512_s6_in)) (Nat.add 1024 1),
  Nat.ble (Nat.add 950 (altIntLen rkmXsWin_w512_s7_in)) (Nat.add 1024 1),
  muxIntListEq rkmHbWin_w512_s2a rkmHbWin_w512_s2b,
  muxIntListEq rkmXsWin_w512_s2a_out rkmXsWin_w512_s2b_in,
  Nat.ble (Nat.add 457 (altIntLen rkmXsWin_w512_s2a_in)) (Nat.add 1024 1),
  rkmCheckRowFromWinWalks 512 16 1024 [1, 2, 4, 4, 4, 4, 4, 4]
    [9920835, 7352925, 9950000, 508285, 351077, 242699, 167508, 84500]
    [191, 248, 541, 28, 20, 14, 10, 5]
    rkmMasksHi_w512_r1024 rkmWalksHi_w512_r1024 rkmRowHi_w512_r1024,
  bWinChk 957 28 100000000 1024 rkmPhb_w512_s3
  973 rkmXsWin_w512_s3_in 975 rkmXsWin_w512_s3_out 1681245957,
  bWinChk 949 20 100000000 1024 rkmPhb_w512_s4
  975 rkmXsWin_w512_s4_in 964 rkmXsWin_w512_s4_out 990071107,
  bWinChk 940 14 100000000 1024 rkmPhb_w512_s5
  964 rkmXsWin_w512_s5_in 956 rkmXsWin_w512_s5_out 674085209,
  bWinChk 934 10 100000000 1024 rkmPhb_w512_s6
  956 rkmXsWin_w512_s6_in 950 rkmXsWin_w512_s6_out 481111300,
  bWinChk 931 5 100000000 1024 rkmPhb_w512_s7
  950 rkmXsWin_w512_s7_in 947 rkmXsWin_w512_s7_out 261586222
  ] = true
private theorem rkmWinSt_w512_t2 : rkmBP_21 := by decide +kernel
private theorem rkmWC_w512_s0_0 :
    bWinChk 0 80 100000000 512 rkmPhb_w512_s0
      0 rkmXsWin_w512_s0_in 2 rkmC_w512_s0_1 3679265124 = true := rkmWP0 rkmBK_00
private theorem rkmWC_w512_s0_1 :
    bWinChk 0 34 100000000 512 rkmPhb_w512_s0
      2 rkmC_w512_s0_1 20 rkmC_w512_s0_2 4853499170 = true := rkmWP1 rkmBK_00
private theorem rkmWC_w512_s0_2 :
    bWinChk 4 28 100000000 512 (drN 4 rkmPhb_w512_s0)
      20 rkmC_w512_s0_2 44 rkmC_w512_s0_3 4637552183 = true := rkmWP0 rkmBK_01
private theorem rkmWC_w512_s0_3 :
    bWinChk 28 25 100000000 512 (drN 28 rkmPhb_w512_s0)
      44 rkmC_w512_s0_3 70 rkmC_w512_s0_4 3488313154 = true := rkmWP1 rkmBK_01
private theorem rkmWC_w512_s0_4 :
    bWinChk 54 24 100000000 512 (drN 54 rkmPhb_w512_s0)
      70 rkmC_w512_s0_4 101 rkmXsWin_w512_s0_out 4355653234 = true := rkmWP0 rkmBK_02
private theorem rkmWC_w512_s1_0 :
    bWinChk 85 22 100000000 1024 rkmPhb_w512_s1
      101 rkmXsWin_w512_s1_in 127 rkmC_w512_s1_1 3558104943 = true := rkmWP1 rkmBK_02
private theorem rkmWC_w512_s1_1 :
    bWinChk 111 21 100000000 1024 (drN 26 rkmPhb_w512_s1)
      127 rkmC_w512_s1_1 154 rkmC_w512_s1_2 3460131920 = true := rkmWP0 rkmBK_03
private theorem rkmWC_w512_s1_2 :
    bWinChk 138 21 100000000 1024 (drN 53 rkmPhb_w512_s1)
      154 rkmC_w512_s1_2 183 rkmC_w512_s1_3 4000903641 = true := rkmWP1 rkmBK_03
private theorem rkmWC_w512_s1_3 :
    bWinChk 167 20 100000000 1024 (drN 82 rkmPhb_w512_s1)
      183 rkmC_w512_s1_3 211 rkmC_w512_s1_4 3941200349 = true := rkmWP0 rkmBK_04
private theorem rkmWC_w512_s1_4 :
    bWinChk 195 20 100000000 1024 (drN 110 rkmPhb_w512_s1)
      211 rkmC_w512_s1_4 240 rkmC_w512_s1_5 4099382594 = true := rkmWP1 rkmBK_04
private theorem rkmWC_w512_s1_5 :
    bWinChk 224 20 100000000 1024 (drN 139 rkmPhb_w512_s1)
      240 rkmC_w512_s1_5 270 rkmC_w512_s1_6 4253503254 = true := rkmWP0 rkmBK_05
private theorem rkmWC_w512_s1_6 :
    bWinChk 254 20 100000000 1024 (drN 169 rkmPhb_w512_s1)
      270 rkmC_w512_s1_6 300 rkmC_w512_s1_7 3643799694 = true := rkmWP1 rkmBK_05
private theorem rkmWC_w512_s1_7 :
    bWinChk 284 20 100000000 1024 (drN 199 rkmPhb_w512_s1)
      300 rkmC_w512_s1_7 330 rkmC_w512_s1_8 3558061952 = true := rkmWP0 rkmBK_06
private theorem rkmWC_w512_s1_8 :
    bWinChk 314 20 100000000 1024 (drN 229 rkmPhb_w512_s1)
      330 rkmC_w512_s1_8 361 rkmC_w512_s1_9 3856209037 = true := rkmWP1 rkmBK_06
private theorem rkmWC_w512_s1_9 :
    bWinChk 345 21 100000000 1024 (drN 260 rkmPhb_w512_s1)
      361 rkmC_w512_s1_9 393 rkmC_w512_s1_10 4137820146 = true := rkmWP0 rkmBK_07
private theorem rkmWC_w512_s1_10 :
    bWinChk 377 21 100000000 1024 (drN 292 rkmPhb_w512_s1)
      393 rkmC_w512_s1_10 424 rkmC_w512_s1_11 4086195349 = true := rkmWP1 rkmBK_07
private theorem rkmWC_w512_s1_11 :
    bWinChk 408 22 100000000 1024 (drN 323 rkmPhb_w512_s1)
      424 rkmC_w512_s1_11 457 rkmXsWin_w512_s1_out 4177715437 = true := rkmWP0 rkmBK_08
private theorem rkmWC_w512_s2a_0 :
    bWinChk 441 20 100000000 1024 rkmPhb_w512_s2a
      457 rkmXsWin_w512_s2a_in 488 rkmC_w512_s2a_1 3864015609 = true := rkmWP1 rkmBK_08
private theorem rkmWC_w512_s2a_1 :
    bWinChk 472 21 100000000 1024 (drN 31 rkmPhb_w512_s2a)
      488 rkmC_w512_s2a_1 519 rkmC_w512_s2a_2 3970263401 = true := rkmWP0 rkmBK_09
private theorem rkmWC_w512_s2a_2 :
    bWinChk 503 21 100000000 1024 (drN 62 rkmPhb_w512_s2a)
      519 rkmC_w512_s2a_2 551 rkmC_w512_s2a_3 4403330485 = true := rkmWP1 rkmBK_09
private theorem rkmWC_w512_s2a_3 :
    bWinChk 535 21 100000000 1024 (drN 94 rkmPhb_w512_s2a)
      551 rkmC_w512_s2a_3 582 rkmC_w512_s2a_4 3966882462 = true := rkmWP0 rkmBK_10
private theorem rkmWC_w512_s2a_4 :
    bWinChk 566 22 100000000 1024 (drN 125 rkmPhb_w512_s2a)
      582 rkmC_w512_s2a_4 614 rkmC_w512_s2a_5 4313208933 = true := rkmWP1 rkmBK_10
private theorem rkmWC_w512_s2a_5 :
    bWinChk 598 23 100000000 1024 (drN 157 rkmPhb_w512_s2a)
      614 rkmC_w512_s2a_5 646 rkmXsWin_w512_s2a_out 4532530346 = true := rkmWP0 rkmBK_11
private theorem rkmWC_w512_s2b_0 :
    bWinChk 630 18 100000000 1024 rkmPhb_w512_s2b
      646 rkmXsWin_w512_s2b_in 672 rkmC_w512_s2b_1 3240982485 = true := rkmWP1 rkmBK_11
private theorem rkmWC_w512_s2b_1 :
    bWinChk 656 19 100000000 1024 (drN 26 rkmPhb_w512_s2b)
      672 rkmC_w512_s2b_1 698 rkmC_w512_s2b_2 3681923785 = true := rkmWP0 rkmBK_12
private theorem rkmWC_w512_s2b_2 :
    bWinChk 682 20 100000000 1024 (drN 52 rkmPhb_w512_s2b)
      698 rkmC_w512_s2b_2 724 rkmC_w512_s2b_3 4052247316 = true := rkmWP1 rkmBK_12
private theorem rkmWC_w512_s2b_3 :
    bWinChk 708 20 100000000 1024 (drN 78 rkmPhb_w512_s2b)
      724 rkmC_w512_s2b_3 751 rkmC_w512_s2b_4 4769820658 = true := rkmWP0 rkmBK_13
private theorem rkmWC_w512_s2b_4 :
    bWinChk 735 21 100000000 1024 (drN 105 rkmPhb_w512_s2b)
      751 rkmC_w512_s2b_4 774 rkmC_w512_s2b_5 4230791683 = true := rkmWP1 rkmBK_13
private theorem rkmWC_w512_s2b_5 :
    bWinChk 758 22 100000000 1024 (drN 128 rkmPhb_w512_s2b)
      774 rkmC_w512_s2b_5 799 rkmC_w512_s2b_6 2697342782 = true := rkmWP0 rkmBK_14
private theorem rkmWC_w512_s2b_6 :
    bWinChk 783 22 100000000 1024 (drN 153 rkmPhb_w512_s2b)
      799 rkmC_w512_s2b_6 821 rkmC_w512_s2b_7 3597818019 = true := rkmWP1 rkmBK_14
private theorem rkmWC_w512_s2b_7 :
    bWinChk 805 23 100000000 1024 (drN 175 rkmPhb_w512_s2b)
      821 rkmC_w512_s2b_7 844 rkmC_w512_s2b_8 2713056952 = true := rkmWP0 rkmBK_15
private theorem rkmWC_w512_s2b_8 :
    bWinChk 828 24 100000000 1024 (drN 198 rkmPhb_w512_s2b)
      844 rkmC_w512_s2b_8 864 rkmC_w512_s2b_9 3704623783 = true := rkmWP1 rkmBK_15
private theorem rkmWC_w512_s2b_9 :
    bWinChk 848 25 100000000 1024 (drN 218 rkmPhb_w512_s2b)
      864 rkmC_w512_s2b_9 883 rkmC_w512_s2b_10 4264140778 = true := rkmWP0 rkmBK_16
private theorem rkmWC_w512_s2b_10 :
    bWinChk 867 25 100000000 1024 (drN 237 rkmPhb_w512_s2b)
      883 rkmC_w512_s2b_10 900 rkmC_w512_s2b_11 3911428949 = true := rkmWP1 rkmBK_16
private theorem rkmWC_w512_s2b_11 :
    bWinChk 884 26 100000000 1024 (drN 254 rkmPhb_w512_s2b)
      900 rkmC_w512_s2b_11 916 rkmC_w512_s2b_12 4147088601 = true := rkmWP0 rkmBK_17
private theorem rkmWC_w512_s2b_12 :
    bWinChk 900 27 100000000 1024 (drN 270 rkmPhb_w512_s2b)
      916 rkmC_w512_s2b_12 932 rkmC_w512_s2b_13 3724735974 = true := rkmWP1 rkmBK_17
private theorem rkmWC_w512_s2b_13 :
    bWinChk 916 28 100000000 1024 (drN 286 rkmPhb_w512_s2b)
      932 rkmC_w512_s2b_13 948 rkmC_w512_s2b_14 3673865173 = true := rkmWP0 rkmBK_18
private theorem rkmWC_w512_s2b_14 :
    bWinChk 932 29 100000000 1024 (drN 302 rkmPhb_w512_s2b)
      948 rkmC_w512_s2b_14 956 rkmC_w512_s2b_15 3256253255 = true := rkmWP1 rkmBK_18
private theorem rkmWC_w512_s2b_15 :
    bWinChk 940 31 100000000 1024 (drN 310 rkmPhb_w512_s2b)
      956 rkmC_w512_s2b_15 967 rkmC_w512_s2b_16 3267112991 = true := rkmWP0 rkmBK_19
private theorem rkmWC_w512_s2b_16 :
    bWinChk 951 33 100000000 1024 (drN 321 rkmPhb_w512_s2b)
      967 rkmC_w512_s2b_16 973 rkmXsWin_w512_s2b_out 2266037260 = true := rkmWP1 rkmBK_19
private theorem rkmWC_w512_s3_0 :
    bWinChk 957 28 100000000 1024 rkmPhb_w512_s3
      973 rkmXsWin_w512_s3_in 975 rkmXsWin_w512_s3_out 1681245957 = true :=
  rkmWP0 (rkmWT5 (rkmTl (rkmTl (rkmTl (rkmTl rkmWinSt_w512_t2)))))
private theorem rkmWC_w512_s4_0 :
    bWinChk 949 20 100000000 1024 rkmPhb_w512_s4
      975 rkmXsWin_w512_s4_in 964 rkmXsWin_w512_s4_out 990071107 = true :=
  rkmWP1 (rkmWT5 (rkmTl (rkmTl (rkmTl (rkmTl rkmWinSt_w512_t2)))))
private theorem rkmWC_w512_s5_0 :
    bWinChk 940 14 100000000 1024 rkmPhb_w512_s5
      964 rkmXsWin_w512_s5_in 956 rkmXsWin_w512_s5_out 674085209 = true :=
  rkmWP2 (rkmWT5 (rkmTl (rkmTl (rkmTl (rkmTl rkmWinSt_w512_t2)))))
private theorem rkmWC_w512_s6_0 :
    bWinChk 934 10 100000000 1024 rkmPhb_w512_s6
      956 rkmXsWin_w512_s6_in 950 rkmXsWin_w512_s6_out 481111300 = true :=
  rkmWP3 (rkmWT5 (rkmTl (rkmTl (rkmTl (rkmTl rkmWinSt_w512_t2)))))
private theorem rkmWC_w512_s7_0 :
    bWinChk 931 5 100000000 1024 rkmPhb_w512_s7
      950 rkmXsWin_w512_s7_in 947 rkmXsWin_w512_s7_out 261586222 = true :=
  rkmWP4 (rkmWT5 (rkmTl (rkmTl (rkmTl (rkmTl rkmWinSt_w512_t2)))))
private theorem rkmHhb_w512_s0 : uHb rkmPhb_w512_s0 = rkmDropInts 0 rkmHbWin_w512_s0 :=
  (muxIntListEq_eq_true.mp (rkmWP0 rkmHbEq_w512_all)).trans
    (drHb 512 1024 51941544502 0 512)
private theorem rkmHhb_w512_s1 : uHb rkmPhb_w512_s1 = rkmDropInts 85 rkmHbWin_w512_s1 :=
  (muxIntListEq_eq_true.mp (rkmWP1 rkmHbEq_w512_all)).trans
    (drHb 1024 1024 29648891129 85 1024)
private theorem rkmHhb_w512_s2a : uHb rkmPhb_w512_s2a = rkmDropInts 441 rkmHbWin_w512_s2a :=
  (muxIntListEq_eq_true.mp (rkmWP2 rkmHbEq_w512_all)).trans
    (drHb 2048 1024 18391866913 441 1024)
private theorem rkmHhb_w512_s2b : uHb rkmPhb_w512_s2b = rkmDropInts 630 rkmHbWin_w512_s2b :=
  (muxIntListEq_eq_true.mp (rkmWP3 rkmHbEq_w512_all)).trans
    (drHb 2048 1024 18391866913 630 1024)
private theorem rkmHhb_w512_s3 : uHb rkmPhb_w512_s3 = rkmDropInts 957 rkmHbWin_w512_s3 :=
  (muxIntListEq_eq_true.mp (rkmWP4 rkmHbEq_w512_all)).trans
    (drHb 2048 1024 18153035714 957 1024)
private theorem rkmHhb_w512_s4 : uHb rkmPhb_w512_s4 = rkmDropInts 949 rkmHbWin_w512_s4 :=
  (muxIntListEq_eq_true.mp (rkmWP0 (rkmWT5 rkmHbEq_w512_all))).trans
    (drHb 2048 1024 17553850000 949 1024)
private theorem rkmHhb_w512_s5 : uHb rkmPhb_w512_s5 = rkmDropInts 940 rkmHbWin_w512_s5 :=
  (muxIntListEq_eq_true.mp (rkmWP1 (rkmWT5 rkmHbEq_w512_all))).trans
    (drHb 2048 1024 17335642857 940 1024)
private theorem rkmHhb_w512_s6 : uHb rkmPhb_w512_s6 = rkmDropInts 934 rkmHbWin_w512_s6 :=
  (muxIntListEq_eq_true.mp (rkmWP2 (rkmWT5 rkmHbEq_w512_all))).trans
    (drHb 2048 1024 16750800000 934 1024)
private theorem rkmHhb_w512_s7 : uHb rkmPhb_w512_s7 = rkmDropInts 931 rkmHbWin_w512_s7 :=
  (muxIntListEq_eq_true.mp (rkmWP3 (rkmWT5 rkmHbEq_w512_all))).trans
    (drHb 2048 1024 16900000000 931 1024)
private theorem rkmWinIter_w512_s0 :
    RkmWinIterSound 191 512 rkmHbWin_w512_s0 0 rkmXsWin_w512_s0_in
      101 rkmXsWin_w512_s0_out 21014282865 :=
  rkmChS 191 21014282865 (rkmChS 167 16658629631 (rkmChS 142 13170316477 (rkmChS 114 8532764294
    (bWinChk_sound rkmHhb_w512_s0 rkmWC_w512_s0_0) rkmHhb_w512_s0 rkmWC_w512_s0_1 rfl rfl)
    (drHbSub rkmHhb_w512_s0 rfl) rkmWC_w512_s0_2 rfl rfl) (drHbSub rkmHhb_w512_s0 rfl)
    rkmWC_w512_s0_3 rfl rfl) (drHbSub rkmHhb_w512_s0 rfl) rkmWC_w512_s0_4 rfl rfl
/-- Certified `w512` seg `0` (`191` steps). -/
theorem rkmWinSegWalkSnd_w512_s0 :
    RkmWinSegWalkSound 191 ⟨512, rkmHbWin_w512_s0, 0, rkmXsWin_w512_s0_in,
      101, rkmXsWin_w512_s0_out, 21014282865⟩ :=
  @rkmSegWalk_mk 191 512 0 101 21014282865 rkmHbWin_w512_s0 rkmXsWin_w512_s0_in
    rkmXsWin_w512_s0_out (rkmw_buildHbFrom_length 512 1024 51941544502 512 0)
    rfl rkmWinIter_w512_s0
private theorem rkmWinIter_w512_s1 :
    RkmWinIterSound 248 1024 rkmHbWin_w512_s1 101 rkmXsWin_w512_s1_in
      457 rkmXsWin_w512_s1_out 46773028316 :=
  rkmChS 248 46773028316 (rkmChS 226 42595312879 (rkmChS 205 38509117530 (rkmChS 184 34371297384
    (rkmChS 164 30515088347 (rkmChS 144 26957026395 (rkmChS 124 23313226701 (rkmChS 104
    19059723447 (rkmChS 84 14960340853 (rkmChS 64 11019140504 (rkmChS 43 7018236863
    (bWinChk_sound rkmHhb_w512_s1 rkmWC_w512_s1_0) (drHbSub rkmHhb_w512_s1 rfl) rkmWC_w512_s1_1
    rfl rfl) (drHbSub rkmHhb_w512_s1 rfl) rkmWC_w512_s1_2 rfl rfl) (drHbSub rkmHhb_w512_s1 rfl)
    rkmWC_w512_s1_3 rfl rfl) (drHbSub rkmHhb_w512_s1 rfl) rkmWC_w512_s1_4 rfl rfl) (drHbSub
    rkmHhb_w512_s1 rfl) rkmWC_w512_s1_5 rfl rfl) (drHbSub rkmHhb_w512_s1 rfl) rkmWC_w512_s1_6
    rfl rfl) (drHbSub rkmHhb_w512_s1 rfl) rkmWC_w512_s1_7 rfl rfl) (drHbSub rkmHhb_w512_s1 rfl)
    rkmWC_w512_s1_8 rfl rfl) (drHbSub rkmHhb_w512_s1 rfl) rkmWC_w512_s1_9 rfl rfl) (drHbSub
    rkmHhb_w512_s1 rfl) rkmWC_w512_s1_10 rfl rfl) (drHbSub rkmHhb_w512_s1 rfl) rkmWC_w512_s1_11
    rfl rfl
/-- Certified `w512` seg `1` (`248` steps). -/
theorem rkmWinSegWalkSnd_w512_s1 :
    RkmWinSegWalkSound 248 ⟨1024, rkmHbWin_w512_s1, 101, rkmXsWin_w512_s1_in,
      457, rkmXsWin_w512_s1_out, 46773028316⟩ :=
  @rkmSegWalk_mk 248 1024 101 457 46773028316 rkmHbWin_w512_s1 rkmXsWin_w512_s1_in
    rkmXsWin_w512_s1_out (rkmw_buildHbFrom_length 1024 1024 29648891129 1024 0)
    rfl rkmWinIter_w512_s1
/-- Certified `w512_s2a` partial walk (`128` substeps). -/
theorem rkmWinIterSnd_w512_s2a :
    RkmWinIterSound 128 1024 rkmHbWin_w512_s2a 457 rkmXsWin_w512_s2a_in
      646 rkmXsWin_w512_s2a_out 25050231236 :=
  rkmChS 128 25050231236 (rkmChS 105 20517700890 (rkmChS 83 16204491957 (rkmChS 62 12237609495
    (rkmChS 41 7834279010 (bWinChk_sound rkmHhb_w512_s2a rkmWC_w512_s2a_0) (drHbSub
    rkmHhb_w512_s2a rfl) rkmWC_w512_s2a_1 rfl rfl) (drHbSub rkmHhb_w512_s2a rfl)
    rkmWC_w512_s2a_2 rfl rfl) (drHbSub rkmHhb_w512_s2a rfl) rkmWC_w512_s2a_3 rfl rfl) (drHbSub
    rkmHhb_w512_s2a rfl) rkmWC_w512_s2a_4 rfl rfl) (drHbSub rkmHhb_w512_s2a rfl)
    rkmWC_w512_s2a_5 rfl rfl
/-- Cumulative `w512` part `1` lane witness. -/
theorem rkmHiLane_w512_wint1 : @rkmWinIterSnd_w512_s2a = @rkmWinIterSnd_w512_s2a :=
  (And.intro (Eq.refl laneWitness_FindAllJohnsonRampKickMuxHi512T9) rfl).right
private theorem rkmWinIterSnd_w512_s2b :
    RkmWinIterSound 413 1024 rkmHbWin_w512_s2b 646 rkmXsWin_w512_s2b_in
      973 rkmXsWin_w512_s2b_out 61199270444 :=
  rkmChS 413 61199270444 (rkmChS 380 58933233184 (rkmChS 349 55666120193 (rkmChS 320 52409866938
    (rkmChS 292 48736001765 (rkmChS 265 45011265791 (rkmChS 239 40864177190 (rkmChS 214
    36952748241 (rkmChS 189 32688607463 (rkmChS 165 28983983680 (rkmChS 142 26270926728 (rkmChS
    120 22673108709 (rkmChS 98 19975765927 (rkmChS 77 15744974244 (rkmChS 57 10975153586 (rkmChS
    37 6922906270 (bWinChk_sound rkmHhb_w512_s2b rkmWC_w512_s2b_0) (drHbSub rkmHhb_w512_s2b rfl)
    rkmWC_w512_s2b_1 rfl rfl) (drHbSub rkmHhb_w512_s2b rfl) rkmWC_w512_s2b_2 rfl rfl) (drHbSub
    rkmHhb_w512_s2b rfl) rkmWC_w512_s2b_3 rfl rfl) (drHbSub rkmHhb_w512_s2b rfl)
    rkmWC_w512_s2b_4 rfl rfl) (drHbSub rkmHhb_w512_s2b rfl) rkmWC_w512_s2b_5 rfl rfl) (drHbSub
    rkmHhb_w512_s2b rfl) rkmWC_w512_s2b_6 rfl rfl) (drHbSub rkmHhb_w512_s2b rfl)
    rkmWC_w512_s2b_7 rfl rfl) (drHbSub rkmHhb_w512_s2b rfl) rkmWC_w512_s2b_8 rfl rfl) (drHbSub
    rkmHhb_w512_s2b rfl) rkmWC_w512_s2b_9 rfl rfl) (drHbSub rkmHhb_w512_s2b rfl)
    rkmWC_w512_s2b_10 rfl rfl) (drHbSub rkmHhb_w512_s2b rfl) rkmWC_w512_s2b_11 rfl rfl) (drHbSub
    rkmHhb_w512_s2b rfl) rkmWC_w512_s2b_12 rfl rfl) (drHbSub rkmHhb_w512_s2b rfl)
    rkmWC_w512_s2b_13 rfl rfl) (drHbSub rkmHhb_w512_s2b rfl) rkmWC_w512_s2b_14 rfl rfl) (drHbSub
    rkmHhb_w512_s2b rfl) rkmWC_w512_s2b_15 rfl rfl) (drHbSub rkmHhb_w512_s2b rfl)
    rkmWC_w512_s2b_16 rfl rfl
private theorem rkmWinIter_w512_s3 :
    RkmWinIterSound 28 1024 rkmHbWin_w512_s3 973 rkmXsWin_w512_s3_in
      975 rkmXsWin_w512_s3_out 1681245957 :=
  bWinChk_sound rkmHhb_w512_s3 rkmWC_w512_s3_0
private theorem rkmWinIter_w512_s4 :
    RkmWinIterSound 20 1024 rkmHbWin_w512_s4 975 rkmXsWin_w512_s4_in
      964 rkmXsWin_w512_s4_out 990071107 :=
  bWinChk_sound rkmHhb_w512_s4 rkmWC_w512_s4_0
private theorem rkmWinIter_w512_s5 :
    RkmWinIterSound 14 1024 rkmHbWin_w512_s5 964 rkmXsWin_w512_s5_in
      956 rkmXsWin_w512_s5_out 674085209 :=
  bWinChk_sound rkmHhb_w512_s5 rkmWC_w512_s5_0
private theorem rkmWinIter_w512_s6 :
    RkmWinIterSound 10 1024 rkmHbWin_w512_s6 956 rkmXsWin_w512_s6_in
      950 rkmXsWin_w512_s6_out 481111300 :=
  bWinChk_sound rkmHhb_w512_s6 rkmWC_w512_s6_0
private theorem rkmWinIter_w512_s7 :
    RkmWinIterSound 5 1024 rkmHbWin_w512_s7 950 rkmXsWin_w512_s7_in
      947 rkmXsWin_w512_s7_out 261586222 :=
  bWinChk_sound rkmHhb_w512_s7 rkmWC_w512_s7_0
private theorem rkmWinSegWalkSnd_w512_s3 :
    RkmWinSegWalkSound 28 ⟨1024, rkmHbWin_w512_s3, 973, rkmXsWin_w512_s3_in,
      975, rkmXsWin_w512_s3_out, 1681245957⟩ :=
  @rkmSegWalk_mk 28 1024 973 975 1681245957
    rkmHbWin_w512_s3 rkmXsWin_w512_s3_in rkmXsWin_w512_s3_out
    (rkmw_buildHbFrom_length 2048 1024 18153035714 1024 0)
    (rkmWP0 rkmWinSt_w512_t2) rkmWinIter_w512_s3
private theorem rkmWinSegWalkSnd_w512_s4 :
    RkmWinSegWalkSound 20 ⟨1024, rkmHbWin_w512_s4, 975, rkmXsWin_w512_s4_in,
      964, rkmXsWin_w512_s4_out, 990071107⟩ :=
  @rkmSegWalk_mk 20 1024 975 964 990071107
    rkmHbWin_w512_s4 rkmXsWin_w512_s4_in rkmXsWin_w512_s4_out
    (rkmw_buildHbFrom_length 2048 1024 17553850000 1024 0)
    (rkmWP1 rkmWinSt_w512_t2) rkmWinIter_w512_s4
private theorem rkmWinSegWalkSnd_w512_s5 :
    RkmWinSegWalkSound 14 ⟨1024, rkmHbWin_w512_s5, 964, rkmXsWin_w512_s5_in,
      956, rkmXsWin_w512_s5_out, 674085209⟩ :=
  @rkmSegWalk_mk 14 1024 964 956 674085209
    rkmHbWin_w512_s5 rkmXsWin_w512_s5_in rkmXsWin_w512_s5_out
    (rkmw_buildHbFrom_length 2048 1024 17335642857 1024 0)
    (rkmWP2 rkmWinSt_w512_t2) rkmWinIter_w512_s5
private theorem rkmWinSegWalkSnd_w512_s6 :
    RkmWinSegWalkSound 10 ⟨1024, rkmHbWin_w512_s6, 956, rkmXsWin_w512_s6_in,
      950, rkmXsWin_w512_s6_out, 481111300⟩ :=
  @rkmSegWalk_mk 10 1024 956 950 481111300
    rkmHbWin_w512_s6 rkmXsWin_w512_s6_in rkmXsWin_w512_s6_out
    (rkmw_buildHbFrom_length 2048 1024 16750800000 1024 0)
    (rkmWP3 rkmWinSt_w512_t2) rkmWinIter_w512_s6
private theorem rkmWinSegWalkSnd_w512_s7 :
    RkmWinSegWalkSound 5 ⟨1024, rkmHbWin_w512_s7, 950, rkmXsWin_w512_s7_in,
      947, rkmXsWin_w512_s7_out, 261586222⟩ :=
  @rkmSegWalk_mk 5 1024 950 947 261586222
    rkmHbWin_w512_s7 rkmXsWin_w512_s7_in rkmXsWin_w512_s7_out
    (rkmw_buildHbFrom_length 2048 1024 16900000000 1024 0)
    (rkmWP4 rkmWinSt_w512_t2) rkmWinIter_w512_s7
private theorem rkmWinChain_w512_s2_full :
    RkmWinIterSound 541 1024 rkmHbWin_w512_s2a 457 rkmXsWin_w512_s2a_in
      973 rkmXsWin_w512_s2b_out 86249501680 :=
  rkmChainWinIterT16 (hb1 := rkmHbWin_w512_s2a) (hb2 := rkmHbWin_w512_s2b)
    (x1 := rkmXsWin_w512_s2a_out) (x1' := rkmXsWin_w512_s2b_in) rfl rfl
    (rkmWP0 (rkmWT5 rkmWinSt_w512_t2)) rfl (rkmWP1 (rkmWT5 rkmWinSt_w512_t2))
    rkmWinIterSnd_w512_s2a rkmWinIterSnd_w512_s2b
private theorem rkmWinSegWalkSnd_w512_s2 :
    RkmWinSegWalkSound 541 ⟨1024, rkmHbWin_w512_s2a, 457, rkmXsWin_w512_s2a_in,
      973, rkmXsWin_w512_s2b_out, 86249501680⟩ :=
  @rkmSegWalk_mk 541 1024 457 973 86249501680
    rkmHbWin_w512_s2a rkmXsWin_w512_s2a_in rkmXsWin_w512_s2b_out
    (rkmw_buildHbFrom_length 2048 1024 18391866913 1024 0)
    (rkmWP2 (rkmWT5 rkmWinSt_w512_t2)) rkmWinChain_w512_s2_full
private theorem rkmWalksSndHi_w512_r1024 :
    RkmWinSegWalksSound [191, 248, 541, 28, 20, 14, 10, 5] rkmWalksHi_w512_r1024 :=
  ⟨rkmWinSegWalkSnd_w512_s0,
  ⟨rkmWinSegWalkSnd_w512_s1,
  ⟨rkmWinSegWalkSnd_w512_s2,
  ⟨rkmWinSegWalkSnd_w512_s3,
  ⟨rkmWinSegWalkSnd_w512_s4,
  ⟨rkmWinSegWalkSnd_w512_s5,
  ⟨rkmWinSegWalkSnd_w512_s6,
  ⟨rkmWinSegWalkSnd_w512_s7,
    trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Caustic `w512` `r = 1024` hit certificate (`m = 512`). -/
theorem rkmTrajHitHi_w512_m512 :
    RkmAnchorHitSound 512 ⟨1024, [1, 2, 4, 4, 4, 4, 4, 4],
      [9920835, 7352925, 9950000, 508285, 351077, 242699, 167508, 84500],
      [191, 248, 541, 28, 20, 14, 10, 5], rkmMasksHi_w512_r1024, rkmRowHi_w512_r1024⟩ :=
  @rkmCheckRowFromWinWalks_sound 512 16 1024 [1, 2, 4, 4, 4, 4, 4, 4]
    [9920835, 7352925, 9950000, 508285, 351077, 242699, 167508, 84500]
    [191, 248, 541, 28, 20, 14, 10, 5] rkmMasksHi_w512_r1024
    rkmWalksHi_w512_r1024 rkmRowHi_w512_r1024
    rkmWalksSndHi_w512_r1024 (rkmWP3 (rkmWT5 rkmWinSt_w512_t2))
/-- Cumulative `w512` part `2` lane witness. -/
theorem rkmHiLane_w512_wint2 : @rkmTrajHitHi_w512_m512 = @rkmTrajHitHi_w512_m512 :=
  (And.intro (Eq.refl rkmHiLane_w512_wint1) rfl).right

end
end QuantumComputation.Specs.DickeSol
